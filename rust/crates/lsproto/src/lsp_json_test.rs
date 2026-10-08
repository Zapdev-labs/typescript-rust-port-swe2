// Ported from tsc/internal/lsp/lsproto/lsp_json_test.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use tsc_json as json;

use crate::*;

#[test]
fn test_unmarshal_rejects_null_for_optional_non_nullable_fields() {
    fn check<T: serde::de::DeserializeOwned + std::fmt::Debug>(input: &str, err_text: &str) {
        let err = json::unmarshal::<T>(input.as_bytes(), &[]).unwrap_err();
        assert!(
            err.to_string().contains(err_text),
            "input {input:?}: error {err} does not contain {err_text:?}"
        );
    }

    check::<InlayHint>(
        r#"{"position": {"line": 0, "character": 0}, "label": "foo", "kind": null}"#,
        r#"null value is not allowed for field "kind""#,
    );
    check::<InlayHint>(
        r#"{"position": {"line": 0, "character": 0}, "label": "foo", "textEdits": null}"#,
        r#"null value is not allowed for field "textEdits""#,
    );
    check::<InlayHint>(
        r#"{"position": {"line": 0, "character": 0}, "label": "foo", "paddingLeft": null}"#,
        r#"null value is not allowed for field "paddingLeft""#,
    );
    check::<FoldingRange>(
        r#"{"startLine": 0, "endLine": 10, "kind": null}"#,
        r#"null value is not allowed for field "kind""#,
    );
    check::<FoldingRange>(
        r#"{"startLine": 0, "endLine": 10, "startCharacter": null}"#,
        r#"null value is not allowed for field "startCharacter""#,
    );
    check::<CompletionItem>(
        r#"{"label": "test", "insertTextFormat": null}"#,
        r#"null value is not allowed for field "insertTextFormat""#,
    );
    check::<Hover>(
        r#"{"contents": {"kind": "plaintext", "value": "hi"}, "range": null}"#,
        r#"null value is not allowed for field "range""#,
    );
    check::<WorkDoneProgressOptions>(
        r#"{"workDoneProgress": null}"#,
        r#"null value is not allowed for field "workDoneProgress""#,
    );
    check::<CallHierarchyIncomingCallsParams>(
        r#"{"item": null}"#,
        r#"null value is not allowed for field "item""#,
    );
    check::<CallHierarchyIncomingCall>(
        r#"{"from": null, "fromRanges": []}"#,
        r#"null value is not allowed for field "from""#,
    );
    check::<InitializeParams>(
        r#"{"processId": null, "rootUri": null, "capabilities": null}"#,
        r#"null value is not allowed for field "capabilities""#,
    );
    check::<InitializeResult>(
        r#"{"capabilities": null}"#,
        r#"null value is not allowed for field "capabilities""#,
    );
    check::<SemanticTokens>(
        r#"{"data": null}"#,
        r#"null value is not allowed for field "data""#,
    );
    check::<TextDocumentEdit>(
        r#"{"textDocument": {"uri": "file:///a.ts", "version": 1}, "edits": null}"#,
        r#"null value is not allowed for field "edits""#,
    );
}

#[test]
fn test_unmarshal_accepts_null_for_nullable_fields() {
    json::unmarshal::<InitializeParams>(
        br#"{"processId": null, "rootUri": null, "capabilities": {}}"#,
        &[],
    )
    .unwrap();
    json::unmarshal::<InitializeParams>(
        br#"{"processId": null, "rootUri": null, "capabilities": {}, "workspaceFolders": null}"#,
        &[],
    )
    .unwrap();
    json::unmarshal::<InitializationOptions>(br#"{"userPreferences": null}"#, &[]).unwrap();
    json::unmarshal::<InitializeParams>(
        br#"{"processId": null, "rootUri": null, "capabilities": {}, "initializationOptions": null}"#,
        &[],
    )
    .unwrap();
}

#[test]
fn test_unmarshal_accepts_omitted_optional_fields() {
    let hint = json::unmarshal::<InlayHint>(
        br#"{"position": {"line": 1, "character": 5}, "label": "test"}"#,
        &[],
    )
    .unwrap();
    assert!(hint.kind.is_none());
    assert!(hint.text_edits.is_none());
    assert!(hint.tooltip.is_none());
    assert!(hint.padding_left.is_none());
    assert!(hint.padding_right.is_none());
    assert!(hint.data.is_none());
    assert_eq!(hint.position.line, 1);
    assert_eq!(hint.position.character, 5);

    let fr = json::unmarshal::<FoldingRange>(br#"{"startLine": 5, "endLine": 10}"#, &[]).unwrap();
    assert!(fr.kind.is_none());
    assert!(fr.start_character.is_none());
    assert!(fr.end_character.is_none());
    assert!(fr.collapsed_text.is_none());
    assert_eq!(fr.start_line, 5);
    assert_eq!(fr.end_line, 10);
}

#[test]
fn test_unmarshal_rejects_incomplete_objects() {
    fn check<T: serde::de::DeserializeOwned + std::fmt::Debug>(input: &str, err_text: &str) {
        let err = json::unmarshal::<T>(input.as_bytes(), &[]).unwrap_err();
        assert!(
            err.to_string().contains(err_text),
            "input {input:?}: error {err} does not contain {err_text:?}"
        );
    }

    check::<InlayHint>(
        r#"{"label": "test"}"#,
        "missing required properties: position",
    );
    check::<InlayHint>(
        r#"{"position": {"line": 0, "character": 0}}"#,
        "missing required properties: label",
    );
    check::<Location>(
        r#"{"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}}}"#,
        "missing required properties: uri",
    );
    check::<Location>(r#"{}"#, "missing required properties: uri, range");
}

#[test]
fn test_marshal_unmarshal_round_trip() {
    // InlayHint with kind
    let v = InlayHint {
        position: Position {
            line: 1,
            character: 5,
        },
        label: StringOrInlayHintLabelParts {
            string: Some("param".to_string()),
            ..Default::default()
        },
        kind: Some(InlayHintKind::Parameter),
        ..Default::default()
    };
    let data = json::marshal(&v, &[]).unwrap();
    let result: InlayHint = json::unmarshal(&data, &[]).unwrap();
    assert_eq!(v, result);

    // InlayHint minimal
    let v = InlayHint {
        position: Position {
            line: 0,
            character: 0,
        },
        label: StringOrInlayHintLabelParts {
            string: Some("x".to_string()),
            ..Default::default()
        },
        ..Default::default()
    };
    let data = json::marshal(&v, &[]).unwrap();
    let result: InlayHint = json::unmarshal(&data, &[]).unwrap();
    assert_eq!(v, result);

    // FoldingRange with all fields
    let v = FoldingRange {
        start_line: 1,
        start_character: Some(0),
        end_line: 10,
        end_character: Some(5),
        kind: Some(FoldingRangeKind::Region),
        collapsed_text: Some("...".to_string()),
    };
    let data = json::marshal(&v, &[]).unwrap();
    let result: FoldingRange = json::unmarshal(&data, &[]).unwrap();
    assert_eq!(v, result);

    // Location
    let v = Location {
        uri: DocumentUri("file:///test.ts".to_string()),
        range: Range {
            start: Position {
                line: 1,
                character: 2,
            },
            end: Position {
                line: 3,
                character: 4,
            },
        },
    };
    let data = json::marshal(&v, &[]).unwrap();
    let result: Location = json::unmarshal(&data, &[]).unwrap();
    assert_eq!(v, result);

    // InitializeParams with null processId
    let v = InitializeParams {
        process_id: IntegerOrNull::default(),
        root_uri: DocumentUriOrNull {
            document_uri: Some(DocumentUri("file:///workspace".to_string())),
        },
        capabilities: Some(ClientCapabilities::default()),
        ..Default::default()
    };
    let data = json::marshal(&v, &[]).unwrap();
    let result: InitializeParams = json::unmarshal(&data, &[]).unwrap();
    assert_eq!(v, result);
}

#[test]
fn test_unmarshal_union_types() {
    let v = json::unmarshal::<IntegerOrString>(b"42", &[]).unwrap();
    assert_eq!(v.integer, Some(42));
    assert!(v.string.is_none());

    let v = json::unmarshal::<IntegerOrString>(b"\"hello\"", &[]).unwrap();
    assert_eq!(v.string.as_deref(), Some("hello"));
    assert!(v.integer.is_none());

    let v = json::unmarshal::<IntegerOrNull>(b"42", &[]).unwrap();
    assert_eq!(v.integer, Some(42));

    let v = json::unmarshal::<IntegerOrNull>(b"null", &[]).unwrap();
    assert!(v.integer.is_none());

    let v = json::unmarshal::<DocumentUriOrNull>(b"\"file:///test.ts\"", &[]).unwrap();
    assert_eq!(
        v.document_uri,
        Some(DocumentUri("file:///test.ts".to_string()))
    );

    let v = json::unmarshal::<DocumentUriOrNull>(b"null", &[]).unwrap();
    assert!(v.document_uri.is_none());
}

#[test]
fn test_marshal_union_types() {
    let v = IntegerOrNull { integer: Some(42) };
    let data = json::marshal(&v, &[]).unwrap();
    assert_eq!(data, b"42");

    let v = IntegerOrNull::default();
    let data = json::marshal(&v, &[]).unwrap();
    assert_eq!(data, b"null");

    let v = IntegerOrString {
        integer: Some(7),
        ..Default::default()
    };
    let data = json::marshal(&v, &[]).unwrap();
    assert_eq!(data, b"7");

    let v = IntegerOrString {
        string: Some("tok".to_string()),
        ..Default::default()
    };
    let data = json::marshal(&v, &[]).unwrap();
    assert_eq!(data, br#""tok""#);
}

#[test]
fn test_unmarshal_ignores_unknown_fields() {
    let loc = json::unmarshal::<Location>(
        br#"{
            "uri": "file:///test.ts",
            "range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 5}},
            "someUnknownField": 42,
            "anotherUnknown": {"nested": true}
        }"#,
        &[],
    )
    .unwrap();
    assert_eq!(loc.uri, DocumentUri("file:///test.ts".to_string()));

    json::unmarshal::<InlayHint>(
        br#"{
            "position": {"line": 0, "character": 0},
            "label": "x",
            "futureField": [1, 2, 3]
        }"#,
        &[],
    )
    .unwrap();
}

#[test]
fn test_unmarshal_rejects_wrong_types() {
    assert!(json::unmarshal::<Location>(b"[]", &[]).is_err());
    assert!(json::unmarshal::<Location>(b"\"not an object\"", &[]).is_err());
    assert!(json::unmarshal::<Location>(b"42", &[]).is_err());
    assert!(json::unmarshal::<Location>(b"null", &[]).is_err());
    assert!(json::unmarshal::<FoldingRange>(b"true", &[]).is_err());
}

#[test]
fn test_unmarshal_union_type_wrong_kind() {
    assert!(json::unmarshal::<IntegerOrString>(b"true", &[]).is_err());
    assert!(json::unmarshal::<IntegerOrString>(b"null", &[]).is_err());
    assert!(json::unmarshal::<IntegerOrString>(b"{}", &[]).is_err());
    assert!(json::unmarshal::<IntegerOrString>(b"[]", &[]).is_err());
    assert!(json::unmarshal::<StringOrInlayHintLabelParts>(b"42", &[]).is_err());
    assert!(json::unmarshal::<StringOrInlayHintLabelParts>(b"true", &[]).is_err());
}

#[test]
fn test_unmarshal_boolean_union_types() {
    let v = json::unmarshal::<BooleanOrHoverOptions>(b"true", &[]).unwrap();
    assert_eq!(v.boolean, Some(true));
    assert!(v.hover_options.is_none());

    let v = json::unmarshal::<BooleanOrHoverOptions>(b"false", &[]).unwrap();
    assert_eq!(v.boolean, Some(false));
    assert!(v.hover_options.is_none());

    let v = json::unmarshal::<BooleanOrHoverOptions>(b"{}", &[]).unwrap();
    assert!(v.boolean.is_none());
    assert!(v.hover_options.is_some());

    assert!(json::unmarshal::<BooleanOrHoverOptions>(b"\"nope\"", &[]).is_err());
}

#[test]
fn test_unmarshal_discriminator_union() {
    let v = json::unmarshal::<WorkDoneProgressBeginOrReportOrEnd>(
        br#"{"kind": "begin", "title": "Indexing"}"#,
        &[],
    )
    .unwrap();
    assert!(v.begin.is_some());
    assert!(v.report.is_none());
    assert!(v.end.is_none());
    assert_eq!(v.begin.as_ref().unwrap().title, "Indexing");

    let v = json::unmarshal::<WorkDoneProgressBeginOrReportOrEnd>(
        br#"{"kind": "report", "message": "50%"}"#,
        &[],
    )
    .unwrap();
    assert!(v.begin.is_none());
    assert!(v.report.is_some());
    assert!(v.end.is_none());
    assert_eq!(v.report.as_ref().unwrap().message.as_deref(), Some("50%"));

    let v =
        json::unmarshal::<WorkDoneProgressBeginOrReportOrEnd>(br#"{"kind": "end"}"#, &[]).unwrap();
    assert!(v.begin.is_none());
    assert!(v.report.is_none());
    assert!(v.end.is_some());

    // discriminator after variant fields
    let v = json::unmarshal::<WorkDoneProgressBeginOrReportOrEnd>(
        br#"{"title": "Indexing", "percentage": 25, "kind": "begin"}"#,
        &[],
    )
    .unwrap();
    assert!(v.begin.is_some());
    assert_eq!(v.begin.as_ref().unwrap().title, "Indexing");
    assert_eq!(v.begin.as_ref().unwrap().percentage, Some(25));

    // PORT: Go's "optional discriminator is preserved" subtest exercised
    // `unmarshalDiscriminatedArm` directly on a test-local struct; the
    // equivalent here asserts the discriminator literal survives in the arm.
    assert_eq!(v.begin.as_ref().unwrap().kind, StringLiteralBegin);

    assert!(
        json::unmarshal::<WorkDoneProgressBeginOrReportOrEnd>(br#"{"kind": "invalid"}"#, &[])
            .is_err()
    );
    assert!(
        json::unmarshal::<WorkDoneProgressBeginOrReportOrEnd>(br#"{"kind": null}"#, &[]).is_err()
    );
    let err = json::unmarshal::<WorkDoneProgressBeginOrReportOrEnd>(
        br#"{"message": "missing kind"}"#,
        &[],
    )
    .unwrap_err();
    assert!(err.to_string().contains(r#"missing discriminator "kind""#));
}

#[test]
fn test_unmarshal_presence_discriminator_union() {
    let v = json::unmarshal::<TextEditOrInsertReplaceEdit>(
        br#"{
            "range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}},
            "newText": "x"
        }"#,
        &[],
    )
    .unwrap();
    assert!(v.text_edit.is_some());
    assert!(v.insert_replace_edit.is_none());
    assert_eq!(v.text_edit.as_ref().unwrap().new_text, "x");

    let v = json::unmarshal::<TextEditOrInsertReplaceEdit>(
        br#"{
            "insert": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 1}},
            "replace": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 2}},
            "newText": "y"
        }"#,
        &[],
    )
    .unwrap();
    assert!(v.text_edit.is_none());
    assert!(v.insert_replace_edit.is_some());
    assert_eq!(v.insert_replace_edit.as_ref().unwrap().new_text, "y");
}

#[test]
fn test_unmarshal_string_or_array_union() {
    let v = json::unmarshal::<StringOrInlayHintLabelParts>(b"\"hello\"", &[]).unwrap();
    assert_eq!(v.string.as_deref(), Some("hello"));
    assert!(v.inlay_hint_label_parts.is_none());

    let v = json::unmarshal::<StringOrInlayHintLabelParts>(
        br#"[{"value": "param"}, {"value": ": "}, {"value": "string"}]"#,
        &[],
    )
    .unwrap();
    assert!(v.string.is_none());
    let parts = v.inlay_hint_label_parts.unwrap();
    assert_eq!(parts.len(), 3);
    assert_eq!(parts[0].value, "param");
}

#[test]
fn test_unmarshal_document_edit_union() {
    let v = json::unmarshal::<TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile>(
        br#"{
            "textDocument": {"uri": "file:///a.ts", "version": 1},
            "edits": [{"range": {"start": {"line": 0, "character": 0}, "end": {"line": 0, "character": 0}}, "newText": "x"}]
        }"#,
        &[],
    )
    .unwrap();
    assert!(v.text_document_edit.is_some());
    assert!(v.create_file.is_none());
    assert!(v.rename_file.is_none());
    assert!(v.delete_file.is_none());

    // TextDocumentEdit with non-string kind
    let v = json::unmarshal::<TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile>(
        br#"{
            "kind": null,
            "textDocument": {"uri": "file:///a.ts", "version": 1},
            "edits": []
        }"#,
        &[],
    )
    .unwrap();
    assert!(v.text_document_edit.is_some());
    assert!(v.create_file.is_none());
    assert!(v.rename_file.is_none());
    assert!(v.delete_file.is_none());

    let v = json::unmarshal::<TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile>(
        br#"{"kind": "create", "uri": "file:///new.ts"}"#,
        &[],
    )
    .unwrap();
    assert!(v.text_document_edit.is_none());
    assert_eq!(
        v.create_file.as_ref().unwrap().uri,
        DocumentUri("file:///new.ts".to_string())
    );

    // CreateFile with kind after fields
    let v = json::unmarshal::<TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile>(
        br#"{"uri": "file:///new.ts", "kind": "create"}"#,
        &[],
    )
    .unwrap();
    assert_eq!(
        v.create_file.as_ref().unwrap().uri,
        DocumentUri("file:///new.ts".to_string())
    );

    let v = json::unmarshal::<TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile>(
        br#"{"kind": "rename", "oldUri": "file:///old.ts", "newUri": "file:///new.ts"}"#,
        &[],
    )
    .unwrap();
    assert_eq!(
        v.rename_file.as_ref().unwrap().old_uri,
        DocumentUri("file:///old.ts".to_string())
    );

    let v = json::unmarshal::<TextDocumentEditOrCreateFileOrRenameFileOrDeleteFile>(
        br#"{"kind": "delete", "uri": "file:///gone.ts"}"#,
        &[],
    )
    .unwrap();
    assert_eq!(
        v.delete_file.as_ref().unwrap().uri,
        DocumentUri("file:///gone.ts".to_string())
    );
}

#[test]
fn test_unmarshal_field_ordering() {
    let loc = json::unmarshal::<Location>(
        br#"{
            "range": {"start": {"line": 1, "character": 2}, "end": {"line": 3, "character": 4}},
            "uri": "file:///test.ts"
        }"#,
        &[],
    )
    .unwrap();
    assert_eq!(loc.uri, DocumentUri("file:///test.ts".to_string()));
    assert_eq!(loc.range.start.line, 1);

    let hint = json::unmarshal::<InlayHint>(
        br#"{
            "kind": 1,
            "label": "x",
            "position": {"line": 0, "character": 0}
        }"#,
        &[],
    )
    .unwrap();
    assert_eq!(hint.kind, Some(InlayHintKind::Type));
}

#[test]
fn test_unmarshal_completion_item_data_file_name() {
    let data = json::unmarshal::<CompletionItemData>(
        br#"{"fileName":"/src/index.ts","position":1,"name":"value"}"#,
        &[],
    )
    .unwrap();
    assert_eq!(data.file_name, "/src/index.ts");
}

#[test]
fn test_unmarshal_empty_object() {
    let v = json::unmarshal::<WorkDoneProgressOptions>(b"{}", &[]).unwrap();
    assert!(v.work_done_progress.is_none());
    json::unmarshal::<InitializationOptions>(b"{}", &[]).unwrap();
    json::unmarshal::<ClientCapabilities>(b"{}", &[]).unwrap();
    json::unmarshal::<ServerCapabilities>(b"{}", &[]).unwrap();
}

#[test]
fn test_marshal_omits_zero_optional_fields() {
    let hint = InlayHint {
        position: Position {
            line: 0,
            character: 0,
        },
        label: StringOrInlayHintLabelParts {
            string: Some("x".to_string()),
            ..Default::default()
        },
        ..Default::default()
    };
    let data = json::marshal(&hint, &[]).unwrap();
    let s = String::from_utf8(data).unwrap();
    assert!(!s.contains("kind"), "should not contain 'kind', got: {s}");
    assert!(
        !s.contains("textEdits"),
        "should not contain 'textEdits', got: {s}"
    );
    assert!(
        !s.contains("paddingLeft"),
        "should not contain 'paddingLeft', got: {s}"
    );
    assert!(
        s.contains("position"),
        "should contain 'position', got: {s}"
    );
    assert!(s.contains("label"), "should contain 'label', got: {s}");

    let fr = FoldingRange {
        start_line: 1,
        end_line: 10,
        ..Default::default()
    };
    let data = json::marshal(&fr, &[]).unwrap();
    let s = String::from_utf8(data).unwrap();
    assert!(!s.contains("kind"), "should not contain 'kind', got: {s}");
    assert!(
        !s.contains("startCharacter"),
        "should not contain 'startCharacter', got: {s}"
    );
    assert!(
        s.contains("startLine"),
        "should contain 'startLine', got: {s}"
    );
    assert!(s.contains("endLine"), "should contain 'endLine', got: {s}");
}

#[test]
fn test_literal_types() {
    let v = StringLiteralCreate;
    let data = json::marshal(&v, &[]).unwrap();
    assert_eq!(data, br#""create""#);

    json::unmarshal::<StringLiteralCreate>(br#""create""#, &[]).unwrap();
    assert!(json::unmarshal::<StringLiteralCreate>(br#""delete""#, &[]).is_err());
    assert!(json::unmarshal::<StringLiteralCreate>(b"42", &[]).is_err());
}

#[test]
fn test_enum_string_values() {
    assert_eq!(InlayHintKind::Type.to_string(), "Type");
    assert_eq!(InlayHintKind::Parameter.to_string(), "Parameter");

    assert_eq!(SymbolKind::File.to_string(), "File");
    assert_eq!(SymbolKind::Function.to_string(), "Function");
    assert_eq!(SymbolKind::Variable.to_string(), "Variable");

    let v = InlayHintKind(999);
    let s = v.to_string();
    assert!(
        s.contains("999"),
        "should contain the numeric value, got: {s}"
    );
}

/// TestRoundTrip locks the generated codecs: every value must survive
/// marshal -> unmarshal unchanged.
#[test]
fn test_round_trip() {
    fn round_trip<T>(v: &T)
    where
        T: serde::Serialize + serde::de::DeserializeOwned + PartialEq + std::fmt::Debug,
    {
        let data = json::marshal(v, &[]).unwrap();
        let got: T = json::unmarshal(&data, &[]).unwrap();
        let again = json::marshal(&got, &[]).unwrap();
        assert_eq!(data, again, "re-marshal differs");
    }

    round_trip(&Range {
        start: Position {
            line: 1,
            character: 2,
        },
        end: Position {
            line: 3,
            character: 4,
        },
    });
    round_trip(&TextEdit {
        range: Range {
            start: Position {
                line: 1,
                character: 2,
            },
            end: Position {
                line: 3,
                character: 4,
            },
        },
        new_text: "hello".to_string(),
    });
    round_trip(&MarkupContent {
        kind: MarkupKind::Markdown,
        value: "**x**".to_string(),
    });
    round_trip(&DidChangeConfigurationParams {
        settings: serde_json::json!({"js/ts": {"x": 1}}),
    });
    round_trip(&DidChangeConfigurationParams {
        settings: serde_json::Value::Null,
    });
    round_trip(&CompletionItem {
        label: "pageXOffset".to_string(),
        kind: Some(CompletionItemKind::Field),
        sort_text: Some("15".to_string()),
        insert_text_format: Some(InsertTextFormat::PlainText),
        ..Default::default()
    });
    // StringOrTuple union (string arm and tuple arm).
    round_trip(&ParameterInformation {
        label: StringOrTuple {
            string: Some("p: number".to_string()),
            ..Default::default()
        },
        ..Default::default()
    });
    round_trip(&ParameterInformation {
        label: StringOrTuple {
            tuple: Some([0, 4]),
            ..Default::default()
        },
        ..Default::default()
    });
}

/// TestStrictnessMissingRequired confirms required fields are still enforced;
/// default reflective decoding would silently accept these.
#[test]
fn test_strictness_missing_required() {
    let err = json::unmarshal::<TextEdit>(
        br#"{"range":{"start":{"line":0,"character":0},"end":{"line":0,"character":1}}}"#,
        &[],
    )
    .unwrap_err();
    assert!(err.to_string().contains("missing required properties"));
    let err = json::unmarshal::<Range>(br#"{"start":{"line":0,"character":0}}"#, &[]).unwrap_err();
    assert!(err.to_string().contains("missing required properties"));
    let err = json::unmarshal::<Position>(br#"{"line":0}"#, &[]).unwrap_err();
    assert!(err.to_string().contains("missing required properties"));
}

/// TestStrictnessNotObject confirms a non-object where an object is required
/// is rejected rather than coerced.
#[test]
fn test_strictness_not_object() {
    let err = json::unmarshal::<TextEdit>(b"\"oops\"", &[]).unwrap_err();
    let s = err.to_string();
    assert!(
        s.contains("object") || s.contains("cannot unmarshal"),
        "unexpected error: {s}"
    );
}

/// TestUnmarshalParamsRequiresParams verifies that a NoParams method must be
/// given no params while every other method must be given params, and that a
/// mismatch (including a null value either way) is an InvalidParams error.
#[test]
fn test_unmarshal_params_requires_params() {
    fn raw(s: &str) -> json::Value {
        serde_json::value::RawValue::from_string(s.to_string()).unwrap()
    }

    // NoParams: only truly-absent/empty params are accepted; null and any
    // present value are rejected.
    //
    // PORT: Go's "empty" case (`json.Value("")`, a zero-length raw value)
    // cannot be constructed here — `RawValue::from_string` validates its
    // input, and the workspace forbids `unsafe` (no repr(transparent) cast).
    // `unmarshal_params` still implements the len==0 acceptance.
    for (name, params, want_err) in [
        ("absent", None, false),
        ("null", Some(raw("null")), true),
        ("object", Some(raw("{}")), true),
    ] {
        let r = RequestMessage {
            params,
            ..Default::default()
        };
        let result = r.unmarshal_params::<NoParams>();
        if want_err {
            let err = result.unwrap_err();
            assert_eq!(
                err.code(),
                ErrorCode::InvalidParams,
                "NoParams/{name}: wrong error code"
            );
        } else {
            result.unwrap_or_else(|e| panic!("NoParams/{name}: {e}"));
        }
    }

    // Required-params method: only an object or array is accepted; absent,
    // empty (see PORT note above), null, and other scalars are rejected.
    for (name, params, want_err) in [
        ("absent", None, true),
        ("null", Some(raw("null")), true),
        ("number", Some(raw("5")), true),
        ("string", Some(raw("\"x\"")), true),
        ("object", Some(raw(r#"{"settings":{"x":1}}"#)), false),
    ] {
        let r = RequestMessage {
            params,
            ..Default::default()
        };
        let result = r.unmarshal_params::<Option<DidChangeConfigurationParams>>();
        if want_err {
            let err = result.unwrap_err();
            assert_eq!(
                err.code(),
                ErrorCode::InvalidParams,
                "typed/{name}: wrong error code"
            );
        } else {
            let got = result.unwrap_or_else(|e| panic!("typed/{name}: {e}"));
            assert!(got.is_some() && !got.as_ref().unwrap().settings.is_null());
        }
    }
}
