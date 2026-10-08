// Ported from tsc/internal/ls/lsconv/converters_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::io::Write;
use std::process::{Command, Stdio};
use std::sync::Arc;

use serde::Deserialize;
use tsc_ast::ast::ContentMapperSourceFileInfo;
use tsc_ast::parseoptions::SourceFileParseOptions;
use tsc_core::scriptkind::ScriptKind;
use tsc_lsproto::{DocumentUri, Position, PositionEncodingKind};
use tsc_parser::{parse_source_file, parse_source_file_into};
use tsc_spanmap::{Feature, Kind, Segment, SpanMap};
use tsc_tspath::{
    CaseSensitivity, PathKey, RootedDirectoryPath, RootedFilePath, rooted_file_path_from_absolute,
    rooted_file_path_from_normalized, to_rooted_file_path,
};

use crate::converters::{
    Converters, Script, file_name_to_document_uri, new_converters, source_file_script,
};
use crate::linemap::{LspLineMap, compute_lsp_line_starts};

#[test]
fn test_document_uri_to_file_name() {
    let tests: [(DocumentUri, &str); 20] = [
        (DocumentUri("file:///path/to/file.ts".to_string()), "/path/to/file.ts"),
        (
            DocumentUri("file://server/share/file.ts".to_string()),
            "//server/share/file.ts",
        ),
        (
            DocumentUri("file:///d%3A/work/tsgo932/lib/utils.ts".to_string()),
            "d:/work/tsgo932/lib/utils.ts",
        ),
        (
            DocumentUri("file:///D%3A/work/tsgo932/lib/utils.ts".to_string()),
            "D:/work/tsgo932/lib/utils.ts",
        ),
        (
            DocumentUri("file:///d%3A/work/tsgo932/app/%28test%29/comp/comp-test.tsx".to_string()),
            "d:/work/tsgo932/app/(test)/comp/comp-test.tsx",
        ),
        (
            DocumentUri("file:///path/to/file.ts#section".to_string()),
            "/path/to/file.ts",
        ),
        (DocumentUri("file:///c:/test/me".to_string()), "c:/test/me"),
        (
            DocumentUri("file://shares/files/c%23/p.cs".to_string()),
            "//shares/files/c#/p.cs",
        ),
        (
            DocumentUri(
                "file:///c:/Source/Z%C3%BCrich%20or%20Zurich%20(%CB%88zj%CA%8A%C9%99r%C9%AAk,/Code/resources/app/plugins/c%23/plugin.json"
                    .to_string(),
            ),
            "c:/Source/Zürich or Zurich (ˈzjʊərɪk,/Code/resources/app/plugins/c#/plugin.json",
        ),
        (
            DocumentUri("file:///c:/test %25/path".to_string()),
            "c:/test %/path",
        ),
        // {"file:?q", "/"},
        (DocumentUri("file:///_:/path".to_string()), "/_:/path"),
        (
            DocumentUri("file:///users/me/c%23-projects/".to_string()),
            "/users/me/c#-projects",
        ),
        (DocumentUri("file:///a/../b.ts".to_string()), "/b.ts"),
        (
            DocumentUri("file://localhost/c%24/GitDevelopment/express".to_string()),
            "//localhost/c$/GitDevelopment/express",
        ),
        (
            DocumentUri("file:///c%3A/test%20with%20%2525/c%23code".to_string()),
            "c:/test with %25/c#code",
        ),
        (
            DocumentUri("untitled:Untitled-1".to_string()),
            "^/~ts-uri~/untitled/ts-nul-authority/Untitled-1",
        ),
        (
            DocumentUri("untitled:Untitled-1#fragment".to_string()),
            "^/~ts-uri~/untitled/ts-nul-authority/~ts-uri-escape~556e7469746c65642d310023667261676d656e74~",
        ),
        (
            DocumentUri("untitled:c:/Users/jrieken/Code/abc.txt".to_string()),
            "^/~ts-uri~/untitled/ts-nul-authority/~ts-uri-escape~633a~/Users/jrieken/Code/abc.txt",
        ),
        (
            DocumentUri("untitled:C:/Users/jrieken/Code/abc.txt".to_string()),
            "^/~ts-uri~/untitled/ts-nul-authority/~ts-uri-escape~433a~/Users/jrieken/Code/abc.txt",
        ),
        (
            DocumentUri(
                "untitled://wsl%2Bubuntu/home/jabaile/work/TypeScript/newfile.ts".to_string(),
            ),
            "^/~ts-uri~/untitled/wsl%2Bubuntu/home/jabaile/work/TypeScript/newfile.ts",
        ),
    ];

    for (uri, file_name) in tests {
        assert_eq!(
            uri.file_name(),
            RootedFilePath::from(file_name),
            "uri {uri:?}"
        );
    }
}

#[test]
fn test_file_name_to_document_uri() {
    let tests: [(RootedFilePath, DocumentUri); 18] = [
        (
            RootedFilePath::from("/path/to/file.ts"),
            DocumentUri("file:///path/to/file.ts".to_string()),
        ),
        (
            RootedFilePath::from("//server/share/file.ts"),
            DocumentUri("file://server/share/file.ts".to_string()),
        ),
        (
            RootedFilePath::from("d:/work/tsgo932/lib/utils.ts"),
            DocumentUri("file:///d%3A/work/tsgo932/lib/utils.ts".to_string()),
        ),
        (
            RootedFilePath::from("D:/work/tsgo932/lib/utils.ts"),
            DocumentUri("file:///d%3A/work/tsgo932/lib/utils.ts".to_string()),
        ),
        (
            RootedFilePath::from("d:/work/tsgo932/app/(test)/comp/comp-test.tsx"),
            DocumentUri("file:///d%3A/work/tsgo932/app/%28test%29/comp/comp-test.tsx".to_string()),
        ),
        (
            RootedFilePath::from("/path/to/file.ts"),
            DocumentUri("file:///path/to/file.ts".to_string()),
        ),
        (
            RootedFilePath::from("c:/test/me"),
            DocumentUri("file:///c%3A/test/me".to_string()),
        ),
        (
            RootedFilePath::from("//shares/files/c#/p.cs"),
            DocumentUri("file://shares/files/c%23/p.cs".to_string()),
        ),
        (
            RootedFilePath::from(
                "c:/Source/Zürich or Zurich (ˈzjʊərɪk,/Code/resources/app/plugins/c#/plugin.json",
            ),
            DocumentUri("file:///c%3A/Source/Z%C3%BCrich%20or%20Zurich%20%28%CB%88zj%CA%8A%C9%99r%C9%AAk%2C/Code/resources/app/plugins/c%23/plugin.json".to_string()),
        ),
        (
            RootedFilePath::from("c:/test %/path"),
            DocumentUri("file:///c%3A/test%20%25/path".to_string()),
        ),
        (RootedFilePath::from("/"), DocumentUri("file:///".to_string())),
        (
            RootedFilePath::from("/_:/path"),
            DocumentUri("file:///_%3A/path".to_string()),
        ),
        (
            rooted_file_path_from_absolute("/users/me/c#-projects/"),
            DocumentUri("file:///users/me/c%23-projects".to_string()),
        ),
        (
            RootedFilePath::from("//localhost/c$/GitDevelopment/express"),
            DocumentUri("file://localhost/c%24/GitDevelopment/express".to_string()),
        ),
        (
            RootedFilePath::from("c:/test with %25/c#code"),
            DocumentUri("file:///c%3A/test%20with%20%2525/c%23code".to_string()),
        ),
        (
            RootedFilePath::from("^/untitled/ts-nul-authority/Untitled-1"),
            DocumentUri("untitled:Untitled-1".to_string()),
        ),
        (
            RootedFilePath::from("^/untitled/ts-nul-authority/c:/Users/jrieken/Code/abc.txt"),
            DocumentUri("untitled:c:/Users/jrieken/Code/abc.txt".to_string()),
        ),
        (
            RootedFilePath::from(
                "^/untitled/wsl%2Bubuntu/home/jabaile/work/TypeScript/newfile.ts",
            ),
            DocumentUri(
                "untitled://wsl%2Bubuntu/home/jabaile/work/TypeScript/newfile.ts".to_string(),
            ),
        ),
    ];

    for (file_name, uri) in tests {
        assert_eq!(
            file_name_to_document_uri(&file_name),
            uri,
            "fileName {:?}",
            file_name.as_string(),
        );
    }
}

#[test]
fn test_non_file_document_uri_round_trips_through_normalized_file_name() {
    assert_eq!(
        DocumentUri("custom:folder/../~ts-uri~/café\\file.ts".to_string()).file_name(),
        rooted_file_path_from_normalized(
            "^/~ts-uri~/custom/ts-nul-authority/folder/~ts-uri-escape~2e2e~/~ts-uri~/~ts-uri-escape~636166c3a95c66696c65~.ts",
        ),
    );
    assert_eq!(
        DocumentUri("custom:.git/file.ts".to_string()).file_name(),
        RootedFilePath::from("^/~ts-uri~/custom/ts-nul-authority/.git/file.ts"),
    );
    assert_eq!(
        DocumentUri("custom:~ts-uri-escape~dir.js/file.ts?x=1".to_string()).file_name(),
        rooted_file_path_from_normalized(
            "^/~ts-uri~/custom/ts-nul-authority/~ts-uri-escape~7e74732d7572692d6573636170657e6469722e6a73~/~ts-uri-escape~66696c65003f783d31~.ts",
        ),
    );
    assert_eq!(
        DocumentUri("custom:c:/dir/file.ts?x=1".to_string())
            .file_name()
            .directory(),
        DocumentUri("custom:c:/dir/other.ts".to_string())
            .file_name()
            .directory(),
    );

    for uri in [
        "untitled:folder/../file.ts",
        "vscode-vfs://github/path//file.ts",
        "custom:/path/./file.ts/",
        "custom:",
        "custom:///path",
        "custom://authority",
        "custom://authority/",
        "custom:path/file.ts?rev=a/b#frag/c",
        "custom://authority/path/file.ts#frag/a",
        "custom:path\\file.ts",
        "custom:.git/file.ts",
        "custom:..hidden/file.ts",
        "custom://~ts-uri~/path",
        "custom://ts-nul-authority/path",
        "custom:~ts-uri-escape~file.ts",
        "custom:~ts-uri-escape~no-path",
        "custom://authority/~ts-uri-no-path~~",
        "custom:~ts-uri-spec~666f6f~/file.ts?x=1",
        "custom:folder/../~ts-uri~/café\\file.ts",
        "custom:name.ts\\",
        "custom:name..ts",
    ]
    .map(|s| DocumentUri(s.to_string()))
    {
        let file_name = uri.file_name();
        assert_eq!(
            rooted_file_path_from_normalized(file_name.as_string()),
            file_name,
            "uri {uri:?}",
        );
        assert_eq!(file_name_to_document_uri(&file_name), uri, "uri {uri:?}");
    }

    for uri in [
        "custom:path\\file.ts",
        "custom:~ts-uri~file.ts",
        "custom:~ts-uri-escape~file.ts",
    ]
    .map(|s| DocumentUri(s.to_string()))
    {
        assert_eq!(uri.file_name().extension(), tsc_tspath::EXTENSION_TS);
    }
    for uri in [
        "custom:~ts-uri-escape~types.d.ts",
        "custom:~ts-uri-escape~types.d.mts",
        "custom:~ts-uri-escape~types.d.css.ts",
    ]
    .map(|s| DocumentUri(s.to_string()))
    {
        assert!(uri.file_name().is_declaration_file());
    }
    assert_eq!(
        DocumentUri("custom:~ts-uri-escape~types.d.ts".to_string())
            .file_name()
            .extension(),
        tsc_tspath::EXTENSION_DTS,
    );
    assert_eq!(
        DocumentUri("custom:~ts-uri-escape~types.d.mts".to_string())
            .file_name()
            .extension(),
        tsc_tspath::EXTENSION_DMTS,
    );
    assert!(
        DocumentUri("custom:~ts-uri-escape~types.d.css.ts".to_string())
            .file_name()
            .as_string()
            .ends_with(".d.css.ts"),
    );

    let exceptional_sibling = DocumentUri("custom:folder/main\\file.ts".to_string()).file_name();
    let ordinary_sibling = DocumentUri("custom:folder/dep.ts".to_string()).file_name();
    assert_eq!(
        exceptional_sibling.directory(),
        ordinary_sibling.directory()
    );

    let authority_file = DocumentUri("custom://a/main.ts".to_string()).file_name();
    let authority_sibling = DocumentUri("custom://a/b/dep.ts".to_string()).file_name();
    assert_eq!(
        authority_file.directory().resolve_file("../b/dep.ts"),
        authority_sibling,
    );
    let authority_only = DocumentUri("custom://a".to_string()).file_name();
    assert_eq!(
        authority_only.directory().resolve_file("dep.ts"),
        DocumentUri("custom://a/dep.ts".to_string()).file_name(),
    );
    let query_file = DocumentUri("custom:path/file.ts?rev=a/b".to_string()).file_name();
    assert_eq!(query_file.extension(), tsc_tspath::EXTENSION_TS);
    assert_eq!(
        query_file.directory(),
        DocumentUri("custom:path/other.ts".to_string())
            .file_name()
            .directory(),
    );
    assert_ne!(
        DocumentUri("custom:~ts-uri-escape~Foo.ts".to_string())
            .path_key(CaseSensitivity::CaseInsensitive),
        DocumentUri("custom:~ts-uri-escape~foo.ts".to_string())
            .path_key(CaseSensitivity::CaseInsensitive),
    );

    let literal_dynamic_file_name =
        rooted_file_path_from_normalized("^/custom/ts-nul-authority/~ts-uri-escape~666f6f~.ts");
    assert_eq!(
        file_name_to_document_uri(&literal_dynamic_file_name),
        DocumentUri("custom:~ts-uri-escape~666f6f~.ts".to_string()),
    );

    let invalid_utf8_file_name =
        rooted_file_path_from_normalized("^/~ts-uri~/custom/ts-nul-authority/~ts-uri-escape~ff~");
    assert_eq!(
        file_name_to_document_uri(&invalid_utf8_file_name),
        DocumentUri("custom:~ts-uri-escape~ff~".to_string()),
    );

    assert_ne!(
        DocumentUri("custom:name.ts\\".to_string()).file_name(),
        DocumentUri("custom:name..ts".to_string()).file_name(),
    );
}

/// `type testScript struct` — a `Script` implemented without an AST.
///
/// PORT: `text`/`original_text` are `Vec<u8>` — the invalid-UTF-8 test
/// (`TestConvertersInvalidUTF8`) needs Go's arbitrary-byte strings, which a
/// Rust `String` cannot hold.
struct TestScript {
    name: RootedFilePath,
    text: Vec<u8>,
    original_text: Vec<u8>,
    span_map: Option<Arc<SpanMap>>,
}

impl TestScript {
    /// `&testScript{name: name, text: text}` — `to_rooted_file_path` mirrors
    /// `tspath.ToRootedFilePath(s.name, "/")`.
    fn new(name: &str, text: &[u8]) -> Self {
        TestScript {
            name: to_rooted_file_path(name, &RootedDirectoryPath::from("/")),
            text: text.to_vec(),
            original_text: Vec::new(),
            span_map: None,
        }
    }
}

impl Script for TestScript {
    fn file_name(&self) -> &RootedFilePath {
        &self.name
    }
    fn original_file_name(&self) -> &RootedFilePath {
        &self.name
    }
    fn text(&self) -> &[u8] {
        &self.text
    }
    fn original_text(&self) -> &[u8] {
        if !self.original_text.is_empty() {
            return &self.original_text;
        }
        &self.text
    }
    fn span_map(&self) -> Option<Arc<SpanMap>> {
        self.span_map.clone()
    }
}

/// `newTestConverters` — PORT: Go returns `(*Converters, *testScript)` where
/// the converters hold only a line-map callback; ours borrows the caller's
/// `line_map`, so the caller constructs the `TestScript` and keeps the map
/// alive for the converters' lifetime.
fn new_test_converters<'a>(line_map: &'a LspLineMap) -> Converters<'a> {
    new_converters(PositionEncodingKind::UTF16, move |_| line_map)
}

#[test]
fn test_converters_source_file_projection_expansion() {
    let original = "x";
    let parse_options = SourceFileParseOptions {
        file_name: RootedFilePath::from("/component.vue"),
        path_key: PathKey::from("/component.vue"),
        ..Default::default()
    };
    let (canonical, nodes) = parse_source_file(parse_options.clone(), " x", ScriptKind::Ts);
    let mut supplemental_options = parse_options;
    supplemental_options.path_key = PathKey::from("/component.vue::supplemental");
    let (supplemental, mut nodes) =
        parse_source_file_into(supplemental_options, "  x", ScriptKind::Ts, nodes);
    nodes[canonical]
        .as_source_file_mut()
        .set_content_mapper_info(ContentMapperSourceFileInfo {
            original_text: original.to_string(),
            content_mapper: "mapper".to_string(),
            span_map: Some(Arc::new(SpanMap::new(&[Segment {
                virtual_start: 1,
                virtual_end: 2,
                original_end: 1,
                kind: Kind::Verbatim,
                features: Feature::All,
                ..Default::default()
            }]))),
            supplemental_source_files: vec![supplemental],
            ..Default::default()
        });
    nodes[supplemental]
        .as_source_file_mut()
        .set_content_mapper_info(ContentMapperSourceFileInfo {
            original_text: original.to_string(),
            content_mapper: "mapper".to_string(),
            span_map: Some(Arc::new(SpanMap::new(&[Segment {
                virtual_start: 2,
                virtual_end: 3,
                original_end: 1,
                kind: Kind::Verbatim,
                features: Feature::All,
                ..Default::default()
            }]))),
            canonical_source_file: Some(canonical),
            ..Default::default()
        });
    let line_map = compute_lsp_line_starts(original.as_bytes());
    let converters = new_test_converters(&line_map);

    let positions = converters.from_lsp_position_for_source_file(
        canonical,
        &nodes,
        Position::default(),
        Feature::Hover,
    );
    assert_eq!(positions.len(), 2);
    assert!(positions[0].script == source_file_script(canonical, &nodes));
    assert!(positions[0].script == source_file_script(canonical, &nodes));
    assert_eq!(positions[0].position, 1);
    assert!(positions[1].script == source_file_script(supplemental, &nodes));
    assert_eq!(positions[1].position, 2);
}

/// `TestConvertersInvalidUTF8` verifies behavior on text containing invalid
/// UTF-8 sequences (e.g. lone continuation bytes). Node's TextDecoder
/// substitutes such bytes with U+FFFD, so the JS-reference test cannot cover
/// this; we assert the expected Go-side behavior directly. Each invalid byte
/// advances the byte position by 1 and the UTF-16 character by 1
/// (RuneError = 1 code unit).
#[test]
fn test_converters_invalid_utf8() {
    // Text with invalid UTF-8 byte 0x80 (continuation byte without start byte).
    // Old code used utf8.RuneLen(RuneError)==3, overshooting the byte offset.
    let text: &[u8] = b"a\x80b\ncd";
    let line_map = compute_lsp_line_starts(text);
    let conv = new_test_converters(&line_map);
    let script = TestScript::new("test.ts", text);

    // (line, char) → byte position. Each row asserts both directions where the
    // position lies on a character boundary.
    let mappings: [(u32, u32, i32); 7] = [
        (0, 0, 0), // 'a'
        (0, 1, 1), // invalid byte 0x80
        (0, 2, 2), // 'b'
        (0, 3, 3), // newline (line end)
        (1, 0, 4), // 'c'
        (1, 1, 5), // 'd'
        (1, 2, 6), // EOF
    ];
    for (line, char_, byte_pos) in mappings {
        let lc = Position {
            line,
            character: char_,
        };
        let positions = conv.from_lsp_position(&script, lc, Feature::All);
        assert_eq!(positions.len(), 1);
        assert_eq!(
            positions[0].position, byte_pos,
            "LineAndCharacterToPosition({line},{char_})"
        );
        let (lsp_position, _) = conv.to_lsp_position(&script, byte_pos);
        assert_eq!(lsp_position, lc, "PositionToLineAndCharacter({byte_pos})");
    }

    // Byte-by-byte round-trip across the entire text.
    for byte_pos in 0..=(text.len() as i32) {
        let (lc, _) = conv.to_lsp_position(&script, byte_pos);
        let positions = conv.from_lsp_position(&script, lc, Feature::All);
        assert_eq!(positions.len(), 1);
        assert_eq!(
            positions[0].position, byte_pos,
            "round-trip byte {byte_pos}"
        );
    }
}

/// `jsReferenceScript` is a Node.js script that, given a list of UTF-8 byte
/// buffers, computes the authoritative mapping between (line, character in
/// UTF-16 code units) and UTF-8 byte offsets.
///
/// To avoid any string round-tripping at the protocol boundary, the inputs are
/// sent as raw bytes: the test writes a length-prefixed binary stream to stdin
/// ([uint32 little-endian count][uint32 LE len][bytes]...[uint32 LE
/// len][bytes]). Node reads the buffers and decodes each with
/// TextDecoder('utf-8') — which is essentially what tsserver / sys.ts does when
/// reading file contents from disk (read as Buffer, decode as UTF-8 to a JS
/// string with real UTF-16 semantics).
///
/// For each input buffer, Node walks the underlying UTF-8 bytes (NOT the
/// decoded string) to identify codepoint boundaries: every byte is the start
/// of a codepoint unless it's a UTF-8 continuation byte (0b10xxxxxx). At each
/// boundary it records the UTF-8 byte offset and the corresponding UTF-16 code
/// unit offset (in the decoded JS string) and (line, char) using the LSP
/// line-break rules (\n, \r, \r\n only).
///
/// Output is JSON on stdout: [ [ { bytePos, line, char }, ... ], ... ]
const JS_REFERENCE_SCRIPT: &str = r#"
const inChunks = [];
process.stdin.on('data', c => inChunks.push(c));
process.stdin.on('end', () => {
  const buf = Buffer.concat(inChunks);
  let off = 0;
  const readU32 = () => { const v = buf.readUInt32LE(off); off += 4; return v; };
  const n = readU32();
  const buffers = [];
  for (let i = 0; i < n; i++) {
    const len = readU32();
    buffers.push(buf.subarray(off, off + len));
    off += len;
  }

  const decoder = new TextDecoder('utf-8', { fatal: true });
  const out = buffers.map(bytes => {
    // Decode the raw UTF-8 bytes to a JS string (this is what sys.ts does with file contents).
    const text = decoder.decode(bytes);

    // LSP line starts in the *decoded* JS string: \n, \r, \r\n only.
    const lineStartsJs = [0];
    for (let i = 0; i < text.length; i++) {
      const c = text.charCodeAt(i);
      if (c === 13) {
        if (i + 1 < text.length && text.charCodeAt(i + 1) === 10) i++;
        lineStartsJs.push(i + 1);
      } else if (c === 10) {
        lineStartsJs.push(i + 1);
      }
    }

    // Walk the original UTF-8 byte buffer to find codepoint boundaries. Inputs are
    // valid UTF-8, so we advance bytePos by the sequence length of each lead byte
    // and jsIdx by the corresponding UTF-16 code unit count (1 for BMP, 2 for
    // surrogate pair) of the codepoint at jsIdx in the decoded string.
    const boundaries = [{ bytePos: 0, jsIdx: 0 }];
    let bytePos = 0, jsIdx = 0;
    while (bytePos < bytes.length) {
      const seq = utf8SeqLen(bytes[bytePos]);
      const cp = text.codePointAt(jsIdx);
      bytePos += seq;
      jsIdx += cp > 0xFFFF ? 2 : 1;
      boundaries.push({ bytePos, jsIdx });
    }

    return boundaries.map(({ bytePos, jsIdx }) => {
      let lo = 0, hi = lineStartsJs.length - 1;
      while (lo < hi) {
        const mid = (lo + hi + 1) >> 1;
        if (lineStartsJs[mid] <= jsIdx) lo = mid;
        else hi = mid - 1;
      }
      return { bytePos, line: lo, char: jsIdx - lineStartsJs[lo] };
    });
  });

  process.stdout.write(JSON.stringify(out));
});

function utf8SeqLen(b) {
  if (b < 0x80) return 1;
  if ((b & 0xE0) === 0xC0) return 2;
  if ((b & 0xF0) === 0xE0) return 3;
  if ((b & 0xF8) === 0xF0) return 4;
  throw new Error('invalid UTF-8 lead byte 0x' + b.toString(16));
}
"#;

/// `type jsTuple struct`
#[derive(Deserialize)]
struct JsTuple {
    #[serde(rename = "bytePos")]
    byte_pos: i64,
    line: i64,
    #[serde(rename = "char")]
    char_: i64,
}

/// `runJSReference` — PORT: returns `None` where Go does `t.Skipf` when node
/// is unavailable.
fn run_js_reference(texts: &[&[u8]]) -> Option<Vec<Vec<JsTuple>>> {
    // `exec.LookPath("node")`
    let node_available = Command::new("node")
        .arg("--version")
        .stdout(Stdio::null())
        .stderr(Stdio::null())
        .status()
        .map(|s| s.success())
        .unwrap_or(false);
    if !node_available {
        eprintln!("skipping: node not available"); // t.Skipf equivalent
        return None;
    }

    // Build a length-prefixed binary stream of the raw UTF-8 bytes:
    // [uint32 LE count] then for each: [uint32 LE length][bytes].
    let mut input = Vec::new();
    input.extend_from_slice(&(texts.len() as u32).to_le_bytes());
    for s in texts {
        input.extend_from_slice(&(s.len() as u32).to_le_bytes());
        input.extend_from_slice(s);
    }

    let mut cmd = Command::new("node")
        .arg("-e")
        .arg(JS_REFERENCE_SCRIPT)
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .stderr(Stdio::piped())
        .spawn()
        .expect("failed to spawn node");
    cmd.stdin
        .take()
        .unwrap()
        .write_all(&input)
        .expect("failed to write to node stdin");
    let output = cmd.wait_with_output().expect("node failed");
    assert!(
        output.status.success(),
        "node failed: {}\nstderr: {}",
        output.status,
        String::from_utf8_lossy(&output.stderr),
    );

    let out: Vec<Vec<JsTuple>> = tsc_json::unmarshal(&output.stdout, &[]).unwrap();
    Some(out)
}

/// `TestConvertersAgainstJSReference` cross-checks the UTF-16 conversions
/// against authoritative results computed by Node.js using real UTF-16 string
/// semantics.
#[test]
fn test_converters_against_js_reference() {
    let cases: [(&str, &[u8]); 14] = [
        ("empty", b""),
        ("ascii", b"hello\nworld"),
        ("ascii_crlf", b"hello\r\nworld\r\n!"),
        ("ascii_cr_only", b"a\rb\rc"),
        ("trailing_newline", b"abc\n"),
        ("bmp_em_dash", "ab\u{2014}cd\nef".as_bytes()),
        ("bmp_multi", "α\nβ\nγδε\nzz".as_bytes()),
        // 😀 is 4 UTF-8 bytes, 2 UTF-16 units
        ("supplementary_emoji", "x\u{1F600}y\nz".as_bytes()),
        (
            "supplementary_at_lineend",
            "ab\u{1F600}\ncd\u{1F60A}".as_bytes(),
        ),
        (
            "supplementary_only",
            "\u{1F600}\u{1F601}\u{1F602}".as_bytes(),
        ),
        ("mixed", "α — \u{1F600}\r\nβ\nγ\r".as_bytes()),
        ("long_mixed_ws", "  \tαβ\n\t\u{1F600}  end\n".as_bytes()),
        ("zwj_emoji", "\u{1F468}\u{200D}\u{1F4BB}\nnext".as_bytes()),
        ("only_newlines", b"\n\n\r\n\r"),
    ];

    let texts: Vec<&[u8]> = cases.iter().map(|(_, text)| *text).collect();
    let Some(refs) = run_js_reference(&texts) else {
        return; // t.Skip
    };
    assert_eq!(refs.len(), cases.len());

    for (i, (name, text)) in cases.iter().enumerate() {
        let ref_tuples = &refs[i];
        let line_map = compute_lsp_line_starts(text);
        let conv = new_test_converters(&line_map);
        let script = TestScript::new("test.ts", text);

        for tup in ref_tuples {
            let byte_pos = tup.byte_pos as i32;
            let expected_lc = Position {
                line: tup.line as u32,
                character: tup.char_ as u32,
            };

            let (got_lc, _) = conv.to_lsp_position(&script, byte_pos);
            assert_eq!(
                got_lc, expected_lc,
                "PositionToLineAndCharacter({byte_pos}) mismatch in {name:?}",
            );

            let positions = conv.from_lsp_position(&script, expected_lc, Feature::All);
            assert_eq!(positions.len(), 1);
            assert_eq!(
                positions[0].position, byte_pos,
                "LineAndCharacterToPosition({},{}) mismatch in {name:?}",
                tup.line, tup.char_,
            );
        }
    }
}
