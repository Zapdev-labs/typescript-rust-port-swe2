// Ported from tsc/internal/ast/functionflags.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// FunctionFlags

use crate::{Kind, Node};

flag_type! {
    pub struct FunctionFlags(pub u32);
}

impl FunctionFlags {
    pub const NORMAL: FunctionFlags = FunctionFlags(0);
    pub const GENERATOR: FunctionFlags = FunctionFlags(1 << 0);
    pub const ASYNC: FunctionFlags = FunctionFlags(1 << 1);
    pub const INVALID: FunctionFlags = FunctionFlags(1 << 2);
    pub const ASYNC_GENERATOR: FunctionFlags = FunctionFlags(Self::ASYNC.0 | Self::GENERATOR.0);
}

/// Ported from `GetFunctionFlags` in functionflags.go.
pub fn get_function_flags(node: Option<&Node>) -> FunctionFlags {
    let Some(node) = node else {
        return FunctionFlags::INVALID;
    };
    let Some(data) = node.body_data() else {
        return FunctionFlags::INVALID;
    };
    let mut flags = FunctionFlags::NORMAL;
    match node.kind {
        Kind::FunctionDeclaration | Kind::FunctionExpression | Kind::MethodDeclaration => {
            if data.asterisk_token.is_some() {
                flags |= FunctionFlags::GENERATOR;
            }
            // fallthrough
            if crate::utilities::has_syntactic_modifier(node, crate::ModifierFlags::ASYNC) {
                flags |= FunctionFlags::ASYNC;
            }
        }
        Kind::ArrowFunction
            if crate::utilities::has_syntactic_modifier(node, crate::ModifierFlags::ASYNC) =>
        {
            flags |= FunctionFlags::ASYNC;
        }
        _ => {}
    }
    if data.body.is_none() {
        flags |= FunctionFlags::INVALID;
    }
    flags
}
