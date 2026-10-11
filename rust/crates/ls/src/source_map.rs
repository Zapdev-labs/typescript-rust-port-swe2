// Ported from tsc/internal/ls/source_map.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::sync::Arc;

use tsc_ast::NodeId;
use tsc_core::text::{TextPos, TextRange};
use tsc_lsconv::converters::{
    Script, file_name_to_document_uri, source_file_script,
};
use tsc_lsproto::{self as lsproto};
use tsc_sourcemap::DocumentPosition;
use tsc_spanmap::{Fidelity, SpanMap};
use tsc_tspath::RootedFilePath;

use crate::languageservice::LanguageService;

impl<'h> LanguageService<'h> {
    /// `sourceFileRangeToLSPLocation` maps a range from an arbitrary program SourceFile to an LSP location,
    /// composing content-mapper span maps and declaration source maps as needed. LS features should use this
    /// for cross-file results instead of calling getMappedLocation or lsconv.ToLSPLocation directly.
    /// This unfiltered form is appropriate for diagnostics and text edits.
    pub(crate) fn source_file_range_to_lsp_location(
        &self,
        file: NodeId,
        file_range: TextRange,
    ) -> (lsproto::Location, Fidelity) {
        let nodes = self.program.nodes(file.file_index());
        if !nodes[file].as_source_file().content_mapper().is_empty() {
            let script = source_file_script(file, &nodes);
            return self.converters.to_lsp_location(&script, file_range);
        }
        let file_name = nodes[file].as_source_file().file_name().clone();
        drop(nodes);
        self.get_mapped_location(&file_name, file_range)
    }

    /// `sourceFileRangeToLSPLocationForFeature` is the preferred conversion for visible LS results that may
    /// come from another file. It applies content-mapper feature filtering and follows declaration source maps.
    /// Do not use it for diagnostics or text edits.
    pub(crate) fn source_file_range_to_lsp_location_for_feature(
        &self,
        file: NodeId,
        file_range: TextRange,
        feature: tsc_spanmap::Feature,
    ) -> (lsproto::Location, Fidelity) {
        let nodes = self.program.nodes(file.file_index());
        if !nodes[file].as_source_file().content_mapper().is_empty() {
            let script = source_file_script(file, &nodes);
            return self
                .converters
                .to_lsp_location_for_feature(&script, file_range, feature);
        }
        let file_name = nodes[file].as_source_file().file_name().clone();
        drop(nodes);
        self.get_mapped_location(&file_name, file_range)
    }

    /// `getMappedLocation` follows declaration source maps from a .d.ts range to its source location.
    /// It is an implementation detail of sourceFileRangeToLSPLocation; LS features should not call it directly,
    /// because it does not preserve a content-mapper projection or apply span-map feature filtering.
    fn get_mapped_location(
        &self,
        file_name: &RootedFilePath,
        file_range: TextRange,
    ) -> (lsproto::Location, Fidelity) {
        let start_pos = self.try_get_source_position(file_name, file_range.pos());
        let Some(start_pos) = start_pos else {
            let script = self.get_script(file_name);
            let (lsp_range, fidelity) = self.create_lsp_range_from_range(file_range, &script);
            return (
                lsproto::Location {
                    uri: file_name_to_document_uri(file_name),
                    range: lsp_range,
                },
                fidelity,
            );
        };
        let end_pos = match self.try_get_source_position(file_name, file_range.end()) {
            Some(end_pos)
                if end_pos.file_name == start_pos.file_name && end_pos.pos >= start_pos.pos =>
            {
                end_pos
            }
            // When end doesn't map, maps to a different source file (e.g. in a .d.ts with a
            // multi-source source map from --outFile compilation), or maps to a position before
            // start (non-monotonic source map mappings), approximate the end position.
            _ => DocumentPosition {
                file_name: start_pos.file_name.clone(),
                pos: start_pos.pos + file_range.len(),
            },
        };
        let new_range = TextRange::new(start_pos.pos, end_pos.pos);
        let script = self.get_script(&start_pos.file_name);
        let (lsp_range, fidelity) = self.create_lsp_range_from_range(new_range, &script);
        (
            lsproto::Location {
                uri: file_name_to_document_uri(&start_pos.file_name),
                range: lsp_range,
            },
            fidelity,
        )
    }

    /// `getScript`.
    fn get_script(&self, file_name: &RootedFilePath) -> PlainScript {
        let text = self
            .host
            .read_file(file_name)
            .expect("file should be readable");
        PlainScript {
            file_name: file_name.clone(),
            text,
        }
    }

    /// `tryGetSourcePosition`.
    pub(crate) fn try_get_source_position(
        &self,
        file_name: &RootedFilePath,
        position: TextPos,
    ) -> Option<DocumentPosition> {
        let new_pos = self.try_get_source_position_worker(file_name, position)?;
        if self.read_file(&new_pos.file_name).is_none() {
            // File doesn't exist
            return None;
        }
        Some(new_pos)
    }

    /// `tryGetSourcePositionWorker`.
    fn try_get_source_position_worker(
        &self,
        file_name: &RootedFilePath,
        position: TextPos,
    ) -> Option<DocumentPosition> {
        if !file_name.is_declaration_file() {
            return None;
        }

        let position_mapper = self.get_document_position_mapper(file_name);
        let document_pos = position_mapper.and_then(|position_mapper| {
            position_mapper.get_source_position(&DocumentPosition {
                file_name: file_name.clone(),
                pos: position,
            })
        })?;
        if let Some(new_pos) =
            self.try_get_source_position_worker(&document_pos.file_name, document_pos.pos)
        {
            return Some(new_pos);
        }
        Some(document_pos)
    }

    /// `tryGetGeneratedPosition`.
    pub(crate) fn try_get_generated_position(
        &self,
        file_name: &RootedFilePath,
        position: TextPos,
    ) -> Option<DocumentPosition> {
        let new_pos = self.try_get_generated_position_worker(file_name, position)?;
        if self.read_file(&new_pos.file_name).is_none() {
            // File doesn't exist
            return None;
        }
        Some(new_pos)
    }

    /// `tryGetGeneratedPositionWorker`.
    fn try_get_generated_position_worker(
        &self,
        file_name: &RootedFilePath,
        position: TextPos,
    ) -> Option<DocumentPosition> {
        if file_name.is_declaration_file() {
            return None;
        }

        let program = self.get_program();
        if program.get_source_file(file_name).is_none() {
            return None;
        }

        let path = program.path_key_for_file_name(file_name);
        // If this is source file of project reference source (instead of redirect) there is no generated position
        if program.is_source_from_project_reference(&path) {
            return None;
        }

        let declaration_file_name = tsc_outputpaths::get_output_declaration_file_name_worker(
            file_name,
            &program.options(),
            program.as_ref(),
        );
        let position_mapper = self.get_document_position_mapper(&declaration_file_name);
        let document_pos = position_mapper.and_then(|position_mapper| {
            position_mapper.get_generated_position(&DocumentPosition {
                file_name: file_name.clone(),
                pos: position,
            })
        })?;
        if let Some(new_pos) =
            self.try_get_generated_position_worker(&document_pos.file_name, document_pos.pos)
        {
            return Some(new_pos);
        }
        Some(document_pos)
    }
}

/// `type script struct` — a plain-text `lsconv.Script` for files that may not
/// be in the program (declaration source-map targets).
struct PlainScript {
    file_name: RootedFilePath,
    text: String,
}

impl Script for PlainScript {
    fn file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    fn original_file_name(&self) -> &RootedFilePath {
        &self.file_name
    }

    fn text(&self) -> &[u8] {
        self.text.as_bytes()
    }

    fn original_text(&self) -> &[u8] {
        self.text.as_bytes()
    }

    fn span_map(&self) -> Option<Arc<SpanMap>> {
        None
    }
}
