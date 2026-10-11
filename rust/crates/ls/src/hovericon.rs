// Ported from tsc/internal/ls/hovericon.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_lsproto as lsproto;
use tsc_lsutil::symbol_display::{ScriptElementKind, ScriptElementKindModifier};

/// `vsImageCatalogGuid` is the GUID of the shared VS image catalog (see
/// `Microsoft.VisualStudio.Imaging.KnownImageIds`), mirroring the constant
/// duplicated in TypeScript-VS's `ImageIdMapping.cs` (which avoids taking an
/// assembly reference just for this GUID).
pub(crate) const VS_IMAGE_CATALOG_GUID: &str = "ae27a6b0-e345-4288-96df-5eaf394ee369";

// Known image IDs from `Microsoft.VisualStudio.Imaging.KnownImageIds`,
// restricted to the subset consumed by TypeScript-VS's `ImageIdMapping.cs`
// for hover tooltips. Corsa (this LSP server) has no TSServer/Roslyn
// dependency to reuse that mapping from, so the values are duplicated here.
const IMAGE_ID_WARNING: i32 = 0x00000637;
const IMAGE_ID_KEYWORD: i32 = 0x00000635;
const IMAGE_ID_MODULE_PRIVATE: i32 = 0x0000077D;
const IMAGE_ID_MODULE_PROTECTED: i32 = 0x0000077E;
const IMAGE_ID_MODULE_PUBLIC: i32 = 0x0000077F;
const IMAGE_ID_TYPE: i32 = 0x00000CA1;
const IMAGE_ID_NAMESPACE: i32 = 0x0000079F;
const IMAGE_ID_CLASS_PRIVATE: i32 = 0x000001D7;
const IMAGE_ID_CLASS_PROTECTED: i32 = 0x000001D8;
const IMAGE_ID_CLASS_PUBLIC: i32 = 0x000001D9;
const IMAGE_ID_INTERFACE_PRIVATE: i32 = 0x00000646;
const IMAGE_ID_INTERFACE_PROTECTED: i32 = 0x00000647;
const IMAGE_ID_INTERFACE_PUBLIC: i32 = 0x00000648;
const IMAGE_ID_ENUM_PRIVATE: i32 = 0x00000469;
const IMAGE_ID_ENUM_PROTECTED: i32 = 0x0000046A;
const IMAGE_ID_ENUM_PUBLIC: i32 = 0x0000046B;
const IMAGE_ID_ENUM_MEMBER: i32 = 0x00000465;
const IMAGE_ID_LOCAL_VARIABLE: i32 = 0x000006D3;
const IMAGE_ID_PROPERTY_PRIVATE: i32 = 0x00000982;
const IMAGE_ID_PROPERTY_PROTECTED: i32 = 0x00000983;
const IMAGE_ID_PROPERTY_PUBLIC: i32 = 0x00000984;
const IMAGE_ID_METHOD_PRIVATE: i32 = 0x00000756;
const IMAGE_ID_METHOD_PROTECTED: i32 = 0x00000757;
const IMAGE_ID_METHOD_PUBLIC: i32 = 0x00000758;
const IMAGE_ID_LABEL: i32 = 0x0000067D;
const IMAGE_ID_ASSEMBLY: i32 = 0x000000C4;
const IMAGE_ID_CONSTANT_PRIVATE: i32 = 0x0000026A;
const IMAGE_ID_CONSTANT_PROTECTED: i32 = 0x0000026B;
const IMAGE_ID_CONSTANT_PUBLIC: i32 = 0x0000026C;

/// `newVSImageId`.
pub(crate) fn new_vs_image_id(id: i32) -> lsproto::VSImageId {
    lsproto::VSImageId {
        guid: VS_IMAGE_CATALOG_GUID.to_string(),
        id,
        ..Default::default()
    }
}

/// `getVSHoverImageId` maps a symbol's `ScriptElementKind`/modifiers to the VS
/// image shown next to the symbol name in hover tooltips. This mirrors
/// TypeScript-VS's `ImageIdMapping.GetImageId`, which the legacy
/// (TSServer-backed) hover path uses; Corsa has no TSServer to source that
/// mapping from, so the LSP hover response must carry the equivalent icon
/// directly.
pub(crate) fn get_vs_hover_image_id(
    kind: ScriptElementKind,
    modifiers: ScriptElementKindModifier,
) -> lsproto::VSImageId {
    let is_private = modifiers.intersects(ScriptElementKindModifier::PRIVATE);
    let is_protected = modifiers.intersects(ScriptElementKindModifier::PROTECTED);

    // No internal/exported arm: the *Internal VS icons carry a chevron overlay
    // that conveys C# assembly-scoped visibility, a concept that doesn't
    // apply to TypeScript.
    let pick = |private: i32, protected: i32, public: i32| -> lsproto::VSImageId {
        if is_private {
            new_vs_image_id(private)
        } else if is_protected {
            new_vs_image_id(protected)
        } else {
            new_vs_image_id(public)
        }
    };

    use ScriptElementKind::*;
    match kind {
        Warning => new_vs_image_id(IMAGE_ID_WARNING),
        Keyword => new_vs_image_id(IMAGE_ID_KEYWORD),
        ScriptElement => pick(
            IMAGE_ID_MODULE_PRIVATE,
            IMAGE_ID_MODULE_PROTECTED,
            IMAGE_ID_MODULE_PUBLIC,
        ),
        PrimitiveType => new_vs_image_id(IMAGE_ID_TYPE),
        ModuleElement => new_vs_image_id(IMAGE_ID_NAMESPACE),
        ConstructorImplementationElement | ClassElement | LocalClassElement | TypeElement => pick(
            IMAGE_ID_CLASS_PRIVATE,
            IMAGE_ID_CLASS_PROTECTED,
            IMAGE_ID_CLASS_PUBLIC,
        ),
        InterfaceElement => pick(
            IMAGE_ID_INTERFACE_PRIVATE,
            IMAGE_ID_INTERFACE_PROTECTED,
            IMAGE_ID_INTERFACE_PUBLIC,
        ),
        EnumElement => pick(
            IMAGE_ID_ENUM_PRIVATE,
            IMAGE_ID_ENUM_PROTECTED,
            IMAGE_ID_ENUM_PUBLIC,
        ),
        EnumMemberElement => new_vs_image_id(IMAGE_ID_ENUM_MEMBER),
        ParameterElement
        | VariableElement
        | LocalVariableElement
        | VariableUsingElement
        | VariableAwaitUsingElement
        | LetElement
        | String => new_vs_image_id(IMAGE_ID_LOCAL_VARIABLE),
        ConstElement => pick(
            IMAGE_ID_CONSTANT_PRIVATE,
            IMAGE_ID_CONSTANT_PROTECTED,
            IMAGE_ID_CONSTANT_PUBLIC,
        ),
        MemberGetAccessorElement
        | MemberSetAccessorElement
        | MemberVariableElement
        | MemberAccessorVariableElement => pick(
            IMAGE_ID_PROPERTY_PRIVATE,
            IMAGE_ID_PROPERTY_PROTECTED,
            IMAGE_ID_PROPERTY_PUBLIC,
        ),
        FunctionElement
        | LocalFunctionElement
        | MemberFunctionElement
        | CallSignatureElement
        | IndexSignatureElement
        | ConstructSignatureElement => pick(
            IMAGE_ID_METHOD_PRIVATE,
            IMAGE_ID_METHOD_PROTECTED,
            IMAGE_ID_METHOD_PUBLIC,
        ),
        TypeParameterElement => new_vs_image_id(IMAGE_ID_TYPE),
        Label => new_vs_image_id(IMAGE_ID_LABEL),
        Alias => new_vs_image_id(IMAGE_ID_MODULE_PUBLIC),
        // PORT: `default:` in Go — `match` in Rust is exhaustive, so the
        // remaining kinds (`Unknown`, `Directory`, `ExternalModuleName`,
        // `Link`, `LinkName`, `LinkText`) all take the assembly icon.
        _ => new_vs_image_id(IMAGE_ID_ASSEMBLY),
    }
}

/// `buildVSHoverRawContent` assembles the VS-specific rich hover content
/// (symbol icon + colorized declaration line, plus an optional colorized
/// documentation block) matching the shape that TypeScript-VS's legacy
/// `HoverService.cs` builds from TSServer's quickinfo-full response
/// (`ImageElement` + `ClassifiedTextElement` wrapped in a `ContainerElement`).
pub(crate) fn build_vs_hover_raw_content(
    image_id: Option<lsproto::VSImageId>,
    quick_info_runs: &[lsproto::VSClassifiedTextRun],
    documentation_runs: &[lsproto::VSClassifiedTextRun],
) -> Option<lsproto::VSContainerElement> {
    if quick_info_runs.is_empty() {
        return None;
    }

    let display_line = lsproto::VSContainerElement {
        style: lsproto::VSContainerElementStyle::Wrapped,
        elements: Some(vec![
            lsproto::VSImageElementOrClassifiedTextElementOrContainerElement {
                image_element: Some(lsproto::VSImageElement {
                    image_id,
                    ..Default::default()
                }),
                ..Default::default()
            },
            lsproto::VSImageElementOrClassifiedTextElementOrContainerElement {
                classified_text_element: Some(lsproto::VSClassifiedTextElement {
                    runs: Some(quick_info_runs.to_vec()),
                    ..Default::default()
                }),
                ..Default::default()
            },
        ]),
        ..Default::default()
    };

    if documentation_runs.is_empty() {
        return Some(display_line);
    }

    Some(lsproto::VSContainerElement {
        style: lsproto::VSContainerElementStyle::Stacked,
        elements: Some(vec![
            lsproto::VSImageElementOrClassifiedTextElementOrContainerElement {
                container_element: Some(display_line),
                ..Default::default()
            },
            lsproto::VSImageElementOrClassifiedTextElementOrContainerElement {
                classified_text_element: Some(lsproto::VSClassifiedTextElement {
                    runs: Some(documentation_runs.to_vec()),
                    ..Default::default()
                }),
                ..Default::default()
            },
        ]),
        ..Default::default()
    })
}
