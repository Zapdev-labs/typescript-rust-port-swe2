// Ported from tsc/internal/ast/precedence.go @ ec47d33c23e464a17cdf2475632cba629bee8763
//
// `type OperatorPrecedence int` and `type TypePrecedence int32` are ported as
// transparent `i32` newtypes with associated consts (matching this crate's
// flag-type convention) rather than Rust enums: Go code compares and could
// arithmetic on them, and `OperatorPrecedenceInvalid` is the out-of-band -1.

use crate::ast::Node;
use crate::ids::NodeId;
use crate::kind_generated::Kind;
use crate::utilities::is_optional_chain;

/// `type OperatorPrecedence int`
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct OperatorPrecedence(pub i32);

impl OperatorPrecedence {
    // Expression:
    //     AssignmentExpression
    //     Expression `,` AssignmentExpression
    pub const COMMA: OperatorPrecedence = OperatorPrecedence(0);
    // NOTE: `Spread` is higher than `Comma` due to how it is parsed in |ElementList|
    // SpreadElement:
    //     `...` AssignmentExpression
    pub const SPREAD: OperatorPrecedence = OperatorPrecedence(1);
    // AssignmentExpression:
    //     ConditionalExpression
    //     YieldExpression
    //     ArrowFunction
    //     AsyncArrowFunction
    //     LeftHandSideExpression `=` AssignmentExpression
    //     LeftHandSideExpression AssignmentOperator AssignmentExpression
    //
    // NOTE: AssignmentExpression is broken down into several precedences due to the requirements
    //       of the parenthesizer rules.
    // AssignmentExpression: YieldExpression
    // YieldExpression:
    //     `yield`
    //     `yield` AssignmentExpression
    //     `yield` `*` AssignmentExpression
    pub const YIELD: OperatorPrecedence = OperatorPrecedence(2);
    // AssignmentExpression: LeftHandSideExpression `=` AssignmentExpression
    // AssignmentExpression: LeftHandSideExpression AssignmentOperator AssignmentExpression
    // AssignmentOperator: one of
    //     `*=` `/=` `%=` `+=` `-=` `<<=` `>>=` `>>>=` `&=` `^=` `|=` `**=`
    pub const ASSIGNMENT: OperatorPrecedence = OperatorPrecedence(3);
    // NOTE: `Conditional` is considered higher than `Assignment` here, but in reality they have
    //       the same precedence.
    // AssignmentExpression: ConditionalExpression
    // ConditionalExpression:
    //     ShortCircuitExpression
    //     ShortCircuitExpression `?` AssignmentExpression `:` AssignmentExpression
    pub const CONDITIONAL: OperatorPrecedence = OperatorPrecedence(4);
    // LogicalORExpression:
    //     LogicalANDExpression
    //     LogicalORExpression `||` LogicalANDExpression
    pub const LOGICAL_OR: OperatorPrecedence = OperatorPrecedence(5);
    // LogicalANDExpression:
    //     BitwiseORExpression
    //     LogicalANDExprerssion `&&` BitwiseORExpression
    pub const LOGICAL_AND: OperatorPrecedence = OperatorPrecedence(6);
    // BitwiseORExpression:
    //     BitwiseXORExpression
    //     BitwiseORExpression `|` BitwiseXORExpression
    pub const BITWISE_OR: OperatorPrecedence = OperatorPrecedence(7);
    // BitwiseXORExpression:
    //     BitwiseANDExpression
    //     BitwiseXORExpression `^` BitwiseANDExpression
    pub const BITWISE_XOR: OperatorPrecedence = OperatorPrecedence(8);
    // BitwiseANDExpression:
    //     EqualityExpression
    //     BitwiseANDExpression `&` EqualityExpression
    pub const BITWISE_AND: OperatorPrecedence = OperatorPrecedence(9);
    // EqualityExpression:
    //     RelationalExpression
    //     EqualityExpression `==` RelationalExpression
    //     EqualityExpression `!=` RelationalExpression
    //     EqualityExpression `===` RelationalExpression
    //     EqualityExpression `!==` RelationalExpression
    pub const EQUALITY: OperatorPrecedence = OperatorPrecedence(10);
    // RelationalExpression:
    //     ShiftExpression
    //     RelationalExpression `<` ShiftExpression
    //     RelationalExpression `>` ShiftExpression
    //     RelationalExpression `<=` ShiftExpression
    //     RelationalExpression `>=` ShiftExpression
    //     RelationalExpression `instanceof` ShiftExpression
    //     RelationalExpression `in` ShiftExpression
    //     [+TypeScript] RelationalExpression `as` Type
    pub const RELATIONAL: OperatorPrecedence = OperatorPrecedence(11);
    // ShiftExpression:
    //     AdditiveExpression
    //     ShiftExpression `<<` AdditiveExpression
    //     ShiftExpression `>>` AdditiveExpression
    //     ShiftExpression `>>>` AdditiveExpression
    pub const SHIFT: OperatorPrecedence = OperatorPrecedence(12);
    // AdditiveExpression:
    //     MultiplicativeExpression
    //     AdditiveExpression `+` MultiplicativeExpression
    //     AdditiveExpression `-` MultiplicativeExpression
    pub const ADDITIVE: OperatorPrecedence = OperatorPrecedence(13);
    // MultiplicativeExpression:
    //     ExponentiationExpression
    //     MultiplicativeExpression MultiplicativeOperator ExponentiationExpression
    // MultiplicativeOperator: one of `*`, `/`, `%`
    pub const MULTIPLICATIVE: OperatorPrecedence = OperatorPrecedence(14);
    // ExponentiationExpression:
    //     UnaryExpression
    //     UpdateExpression `**` ExponentiationExpression
    pub const EXPONENTIATION: OperatorPrecedence = OperatorPrecedence(15);
    // UnaryExpression:
    //     UpdateExpression
    //     `delete` UnaryExpression
    //     `void` UnaryExpression
    //     `typeof` UnaryExpression
    //     `+` UnaryExpression
    //     `-` UnaryExpression
    //     `~` UnaryExpression
    //     `!` UnaryExpression
    //     AwaitExpression
    // UpdateExpression:            // TODO: Do we need to investigate the precedence here?
    //     `++` UnaryExpression
    //     `--` UnaryExpression
    pub const UNARY: OperatorPrecedence = OperatorPrecedence(16);
    // UpdateExpression:
    //     LeftHandSideExpression
    //     LeftHandSideExpression `++`
    //     LeftHandSideExpression `--`
    pub const UPDATE: OperatorPrecedence = OperatorPrecedence(17);
    // LeftHandSideExpression:
    //     NewExpression
    // NewExpression:
    //     MemberExpression
    //     `new` NewExpression
    pub const LEFT_HAND_SIDE: OperatorPrecedence = OperatorPrecedence(18);
    // LeftHandSideExpression:
    //     OptionalExpression
    // OptionalExpression:
    //     MemberExpression OptionalChain
    //     CallExpression OptionalChain
    //     OptionalExpression OptionalChain
    pub const OPTIONAL_CHAIN: OperatorPrecedence = OperatorPrecedence(19);
    // LeftHandSideExpression:
    //     CallExpression
    // CallExpression:
    //     CoverCallExpressionAndAsyncArrowHead
    //     SuperCall
    //     ImportCall
    //     CallExpression Arguments
    //     CallExpression `[` Expression `]`
    //     CallExpression `.` IdentifierName
    //     CallExpression TemplateLiteral
    // MemberExpression:
    //     PrimaryExpression
    //     MemberExpression `[` Expression `]`
    //     MemberExpression `.` IdentifierName
    //     MemberExpression TemplateLiteral
    //     SuperProperty
    //     MetaProperty
    //     `new` MemberExpression Arguments
    pub const MEMBER: OperatorPrecedence = OperatorPrecedence(20);
    // TODO: JSXElement?
    // PrimaryExpression:
    //     `this`
    //     IdentifierReference
    //     Literal
    //     ArrayLiteral
    //     ObjectLiteral
    //     FunctionExpression
    //     ClassExpression
    //     GeneratorExpression
    //     AsyncFunctionExpression
    //     AsyncGeneratorExpression
    //     RegularExpressionLiteral
    //     TemplateLiteral
    pub const PRIMARY: OperatorPrecedence = OperatorPrecedence(21);
    // PrimaryExpression:
    //     CoverParenthesizedExpressionAndArrowParameterList
    pub const PARENTHESES: OperatorPrecedence = OperatorPrecedence(22);
    pub const LOWEST: OperatorPrecedence = Self::COMMA;
    pub const HIGHEST: OperatorPrecedence = Self::PARENTHESES;
    pub const DISALLOW_COMMA: OperatorPrecedence = Self::YIELD;
    // ShortCircuitExpression:
    //     LogicalORExpression
    //     CoalesceExpression
    // CoalesceExpression:
    //     CoalesceExpressionHead `??` BitwiseORExpression
    // CoalesceExpressionHead:
    //     CoalesceExpression
    //     BitwiseORExpression
    pub const COALESCE: OperatorPrecedence = Self::LOGICAL_OR;
    // -1 is lower than all other precedences. Returning it will cause binary expression
    // parsing to stop.
    pub const INVALID: OperatorPrecedence = OperatorPrecedence(-1);
}

fn get_operator(expression: &Node, nodes: &[Node]) -> Kind {
    match expression.kind {
        Kind::BinaryExpression => nodes[expression
            .as_binary_expression()
            .operator_token
            .expect("BinaryExpression without OperatorToken in getOperator")]
        .kind,
        Kind::PrefixUnaryExpression => expression.as_prefix_unary_expression().operator,
        Kind::PostfixUnaryExpression => expression.as_postfix_unary_expression().operator,
        _ => expression.kind,
    }
}

/// `GetExpressionPrecedence` — gets the precedence of an expression.
pub fn get_expression_precedence(expression: &Node, nodes: &[Node]) -> OperatorPrecedence {
    let operator = get_operator(expression, nodes);
    let mut flags = OperatorPrecedenceFlags::NONE;
    if expression.kind == Kind::NewExpression && expression.argument_list().is_none() {
        flags = OperatorPrecedenceFlags::NEW_WITHOUT_ARGUMENTS;
    } else if is_optional_chain(expression) {
        flags = OperatorPrecedenceFlags::OPTIONAL_CHAIN;
    }
    get_operator_precedence(expression.kind, operator, flags)
}

flag_type! {
    /// `type OperatorPrecedenceFlags int`
    pub struct OperatorPrecedenceFlags(pub u32);
}

impl OperatorPrecedenceFlags {
    pub const NEW_WITHOUT_ARGUMENTS: OperatorPrecedenceFlags = OperatorPrecedenceFlags(1 << 0);
    pub const OPTIONAL_CHAIN: OperatorPrecedenceFlags = OperatorPrecedenceFlags(1 << 1);
}

/// `GetOperatorPrecedence` — gets the precedence of an operator.
pub fn get_operator_precedence(
    node_kind: Kind,
    operator_kind: Kind,
    flags: OperatorPrecedenceFlags,
) -> OperatorPrecedence {
    match node_kind {
        Kind::SpreadElement => OperatorPrecedence::SPREAD,
        Kind::YieldExpression => OperatorPrecedence::YIELD,
        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        Kind::ArrowFunction => OperatorPrecedence::ASSIGNMENT,
        Kind::ConditionalExpression => OperatorPrecedence::CONDITIONAL,
        Kind::BinaryExpression => match operator_kind {
            Kind::CommaToken => OperatorPrecedence::COMMA,
            Kind::EqualsToken
            | Kind::PlusEqualsToken
            | Kind::MinusEqualsToken
            | Kind::AsteriskAsteriskEqualsToken
            | Kind::AsteriskEqualsToken
            | Kind::SlashEqualsToken
            | Kind::PercentEqualsToken
            | Kind::LessThanLessThanEqualsToken
            | Kind::GreaterThanGreaterThanEqualsToken
            | Kind::GreaterThanGreaterThanGreaterThanEqualsToken
            | Kind::AmpersandEqualsToken
            | Kind::CaretEqualsToken
            | Kind::BarEqualsToken
            | Kind::BarBarEqualsToken
            | Kind::AmpersandAmpersandEqualsToken
            | Kind::QuestionQuestionEqualsToken => OperatorPrecedence::ASSIGNMENT,
            _ => get_binary_operator_precedence(operator_kind),
        },
        // TODO: Should prefix `++` and `--` be moved to the `Update` precedence?
        Kind::TypeAssertionExpression
        | Kind::NonNullExpression
        | Kind::PrefixUnaryExpression
        | Kind::TypeOfExpression
        | Kind::VoidExpression
        | Kind::DeleteExpression
        | Kind::AwaitExpression => OperatorPrecedence::UNARY,
        Kind::PostfixUnaryExpression => OperatorPrecedence::UPDATE,
        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        Kind::PropertyAccessExpression | Kind::ElementAccessExpression => {
            if flags.intersects(OperatorPrecedenceFlags::OPTIONAL_CHAIN) {
                return OperatorPrecedence::OPTIONAL_CHAIN;
            }
            OperatorPrecedence::MEMBER
        }
        Kind::CallExpression => {
            if flags.intersects(OperatorPrecedenceFlags::OPTIONAL_CHAIN) {
                return OperatorPrecedence::OPTIONAL_CHAIN;
            }
            OperatorPrecedence::MEMBER
        }
        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        Kind::NewExpression => {
            if flags.intersects(OperatorPrecedenceFlags::NEW_WITHOUT_ARGUMENTS) {
                return OperatorPrecedence::LEFT_HAND_SIDE;
            }
            OperatorPrecedence::MEMBER
        }
        // !!! By necessity, this differs from the old compiler to better align with ParenthesizerRules. consider backporting
        Kind::TaggedTemplateExpression | Kind::MetaProperty | Kind::ExpressionWithTypeArguments => {
            OperatorPrecedence::MEMBER
        }
        Kind::AsExpression | Kind::SatisfiesExpression => OperatorPrecedence::RELATIONAL,
        Kind::ThisKeyword
        | Kind::SuperKeyword
        | Kind::ImportKeyword
        | Kind::Identifier
        | Kind::PrivateIdentifier
        | Kind::NullKeyword
        | Kind::TrueKeyword
        | Kind::FalseKeyword
        | Kind::NumericLiteral
        | Kind::BigIntLiteral
        | Kind::StringLiteral
        | Kind::ArrayLiteralExpression
        | Kind::ObjectLiteralExpression
        | Kind::FunctionExpression
        | Kind::ClassExpression
        | Kind::RegularExpressionLiteral
        | Kind::NoSubstitutionTemplateLiteral
        | Kind::TemplateExpression
        | Kind::OmittedExpression
        | Kind::JsxElement
        | Kind::JsxSelfClosingElement
        | Kind::JsxFragment
        | Kind::MissingDeclaration => OperatorPrecedence::PRIMARY,
        // !!! By necessity, this differs from the old compiler to support emit. consider backporting
        Kind::ParenthesizedExpression => OperatorPrecedence::PARENTHESES,
        _ => OperatorPrecedence::INVALID,
    }
}

/// `GetBinaryOperatorPrecedence` — gets the precedence of a binary operator.
pub fn get_binary_operator_precedence(operator_kind: Kind) -> OperatorPrecedence {
    match operator_kind {
        Kind::QuestionQuestionToken => OperatorPrecedence::COALESCE,
        Kind::BarBarToken => OperatorPrecedence::LOGICAL_OR,
        Kind::AmpersandAmpersandToken => OperatorPrecedence::LOGICAL_AND,
        Kind::BarToken => OperatorPrecedence::BITWISE_OR,
        Kind::CaretToken => OperatorPrecedence::BITWISE_XOR,
        Kind::AmpersandToken => OperatorPrecedence::BITWISE_AND,
        Kind::EqualsEqualsToken
        | Kind::ExclamationEqualsToken
        | Kind::EqualsEqualsEqualsToken
        | Kind::ExclamationEqualsEqualsToken => OperatorPrecedence::EQUALITY,
        Kind::LessThanToken
        | Kind::GreaterThanToken
        | Kind::LessThanEqualsToken
        | Kind::GreaterThanEqualsToken
        | Kind::InstanceOfKeyword
        | Kind::InKeyword
        | Kind::AsKeyword
        | Kind::SatisfiesKeyword => OperatorPrecedence::RELATIONAL,
        Kind::LessThanLessThanToken
        | Kind::GreaterThanGreaterThanToken
        | Kind::GreaterThanGreaterThanGreaterThanToken => OperatorPrecedence::SHIFT,
        Kind::PlusToken | Kind::MinusToken => OperatorPrecedence::ADDITIVE,
        Kind::AsteriskToken | Kind::SlashToken | Kind::PercentToken => {
            OperatorPrecedence::MULTIPLICATIVE
        }
        Kind::AsteriskAsteriskToken => OperatorPrecedence::EXPONENTIATION,
        // -1 is lower than all other precedences.  Returning it will cause binary expression
        // parsing to stop.
        _ => OperatorPrecedence::INVALID,
    }
}

/// `GetLeftmostExpression` — gets the leftmost expression of an expression,
/// e.g. `a` in `a.b`, `a[b]`, `a++`, `a+b`, `a?b:c`, `a as B`, etc.
pub fn get_leftmost_expression(
    node: NodeId,
    stop_at_call_expressions: bool,
    nodes: &[Node],
) -> NodeId {
    let mut node = node;
    loop {
        match nodes[node].kind {
            Kind::PostfixUnaryExpression => {
                node = nodes[node]
                    .as_postfix_unary_expression()
                    .operand
                    .expect("PostfixUnaryExpression without Operand");
                continue;
            }
            Kind::BinaryExpression => {
                node = nodes[node]
                    .as_binary_expression()
                    .left
                    .expect("BinaryExpression without Left");
                continue;
            }
            Kind::ConditionalExpression => {
                node = nodes[node]
                    .as_conditional_expression()
                    .condition
                    .expect("ConditionalExpression without Condition");
                continue;
            }
            Kind::TaggedTemplateExpression => {
                node = nodes[node]
                    .as_tagged_template_expression()
                    .tag
                    .expect("TaggedTemplateExpression without Tag");
                continue;
            }
            Kind::CallExpression if stop_at_call_expressions => {
                return node;
            }
            Kind::CallExpression
            | Kind::AsExpression
            | Kind::ElementAccessExpression
            | Kind::PropertyAccessExpression
            | Kind::NonNullExpression
            | Kind::PartiallyEmittedExpression
            | Kind::SatisfiesExpression => {
                node = nodes[node]
                    .expression()
                    .expect("expression node without Expression");
                continue;
            }
            _ => {}
        }
        return node;
    }
}

/// `type TypePrecedence int32`
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash, Debug)]
#[repr(transparent)]
pub struct TypePrecedence(pub i32);

impl TypePrecedence {
    // Conditional precedence (lowest)
    //
    //   Type[Extends]:
    //       ConditionalTypeNode[?Extends]
    //
    //   ConditionalTypeNode[Extends]:
    //       [~Extends] UnionTypeNode `extends` Type[+Extends] `?` Type[~Extends] `:` Type[~Extends]
    //
    pub const CONDITIONAL: TypePrecedence = TypePrecedence(0);

    // JSDoc precedence (optional and variadic types)
    //
    //    JSDocType:
    //      `...`? Type `=`?
    pub const JSDOC: TypePrecedence = TypePrecedence(1);

    // Function precedence
    //
    //   Type[Extends]:
    //       ConditionalTypeNode[?Extends]
    //       FunctionTypeNode[?Extends]
    //       ConstructorTypeNode[?Extends]
    //
    //   ConditionalTypeNode[Extends]:
    //       UnionTypeNode
    //
    //   FunctionTypeNode[Extends]:
    //       TypeParameters? ArrowParameters `=>` Type[?Extends]
    //
    //   ConstructorTypeNode[Extends]:
    //       `abstract`? TypeParameters? ArrowParameters `=>` Type[?Extends]
    //
    pub const FUNCTION: TypePrecedence = TypePrecedence(2);

    // Union precedence
    //
    //   UnionTypeNode:
    //       `|`? UnionTypeNoBar
    //
    //   UnionTypeNoBar:
    //       IntersectionTypeNode
    //       UnionTypeNoBar `|` IntersectionTypeNode
    //
    pub const UNION: TypePrecedence = TypePrecedence(3);

    // Intersection precedence
    //
    //   IntersectionTypeNode:
    //       `&`? IntersectionTypeNoAmpersand
    //
    //   IntersectionTypeNoAmpersand:
    //       TypeOperatorNode
    //       IntersectionTypeNoAmpersand `&` TypeOperatorNode
    //
    pub const INTERSECTION: TypePrecedence = TypePrecedence(4);

    // TypeOperatorNode precedence
    //
    //   TypeOperatorNode:
    //     PostfixType
    //     InferTypeNode
    //     `keyof` TypeOperatorNode
    //     `unique` TypeOperatorNode
    //     `readonly` PostfixType
    //
    //   InferTypeNode:
    //     `infer` BindingIdentifier
    //     `infer` BindingIdentifier `extends` Type[+Extends]
    //
    pub const TYPE_OPERATOR: TypePrecedence = TypePrecedence(5);

    // Postfix precedence
    //
    //   PostfixType:
    //       NonArrayType
    //       OptionalTypeNode
    //       ArrayTypeNode
    //       IndexedAccessTypeNode
    //
    //   OptionalTypeNode:
    //       PostfixType `?`
    //
    //   ArrayTypeNode:
    //       PostfixType `[` `]`
    //
    //   IndexedAccessTypeNode:
    //       PostfixType `[` Type[~Extends] `]`
    //
    pub const POSTFIX: TypePrecedence = TypePrecedence(6);

    // NonArray precedence (highest)
    //
    //   NonArrayType:
    //       KeywordType
    //       LiteralTypeNode
    //       ThisTypeNode
    //       ImportType
    //       TypeQueryNode
    //       MappedTypeNode
    //       TypeLiteralNode
    //       TupleTypeNode
    //       ParenthesizedTypeNode
    //       TypePredicateNode
    //       TypeReferenceNode
    //       TemplateType
    //
    //   KeywordType: one of
    //       `any`       `unknown` `string`    `number` `bigint`
    //       `symbol`    `boolean` `undefined` `never`  `object`
    //       `intrinsic` `void`
    //
    //   LiteralTypeNode:
    //       StringLiteral
    //       NoSubstitutionTemplateLiteral
    //       NumericLiteral
    //       BigIntLiteral
    //       `-` NumericLiteral
    //       `-` BigIntLiteral
    //       `true`
    //       `false`
    //       `null`
    //
    //   ThisTypeNode:
    //       `this`
    //
    //   ImportType:
    //       `typeof`? `import` `(` Type[~Extends] `,`? `)` ImportTypeQualifier? TypeArguments?
    //       `typeof`? `import` `(` Type[~Extends] `,` ImportTypeAttributes `,`? `)` ImportTypeQualifier? TypeArguments?
    //
    //   ImportTypeQualifier:
    //       `.` EntityName
    //
    //   ImportTypeAttributes:
    //       `{` `with` `:` ImportAttributes `,`? `}`
    //
    //   TypeQueryNode:
    //
    //   MappedTypeNode:
    //       `{` MappedTypePrefix? MappedTypePropertyName MappedTypeSuffix? `:` Type[~Extends] `;` `}`
    //
    //   MappedTypePrefix:
    //       `readonly`
    //       `+` `readonly`
    //       `-` `readonly`
    //
    //   MappedTypePropertyName:
    //       `[` BindingIdentifier `in` Type[~Extends] `]`
    //       `[` BindingIdentifier `in` Type[~Extends] `as` Type[~Extends] `]`
    //
    //   MappedTypeSuffix:
    //       `?`
    //       `+` `?`
    //       `-` `?`
    //
    //   TypeLiteralNode:
    //       `{` TypeElementList `}`
    //
    //   TypeElementList:
    //       [empty]
    //       TypeElementList TypeElement
    //
    //   TypeElement:
    //       PropertySignatureDeclaration
    //       MethodSignatureDeclaration
    //       IndexSignatureDeclaration
    //       CallSignatureDeclaration
    //       ConstructSignatureDeclaration
    //
    //   PropertySignatureDeclaration:
    //       PropertyName `?`? TypeAnnotation? `;`
    //
    //   MethodSignatureDeclaration:
    //       PropertyName `?`? TypeParameters? `(` FormalParameterList `)` TypeAnnotation? `;`
    //       `get` PropertyName TypeParameters? `(` FormalParameterList `)` TypeAnnotation? `;` // GetAccessorDeclaration
    //       `set` PropertyName TypeParameters? `(` FormalParameterList `)` TypeAnnotation? `;` // SetAccessorDeclaration
    //
    //   IndexSignatureDeclaration:
    //       `[` IdentifierName`]` TypeAnnotation `;`
    //
    //   CallSignatureDeclaration:
    //       TypeParameters? `(` FormalParameterList `)` TypeAnnotation? `;`
    //
    //   ConstructSignatureDeclaration:
    //       `new` TypeParameters? `(` FormalParameterList `)` TypeAnnotation? `;`
    //
    //   TupleTypeNode:
    //       `[` `]`
    //       `[` NamedTupleElementTypes `,`? `]`
    //       `[` TupleElementTypes `,`? `]`
    //
    //   NamedTupleElementTypes:
    //       NamedTupleMember
    //       NamedTupleElementTypes `,` NamedTupleMember
    //
    //   NamedTupleMember:
    //       IdentifierName `?`? `:` Type[~Extends]
    //       `...` IdentifierName `:` Type[~Extends]
    //
    //   TupleElementTypes:
    //       TupleElementType
    //       TupleElementTypes `,` TupleElementType
    //
    //   TupleElementType:
    //       Type[~Extends]
    //       OptionalTypeNode
    //       RestTypeNode
    //
    //   RestTypeNode:
    //       `...` Type[~Extends]
    //
    //   ParenthesizedTypeNode:
    //       `(` Type[~Extends] `)`
    //
    //   TypePredicateNode:
    //       `asserts`? TypePredicateParameterName
    //       `asserts`? TypePredicateParameterName `is` Type[~Extends]
    //
    //   TypePredicateParameterName:
    //       `this`
    //       IdentifierReference
    //
    //   TypeReferenceNode:
    //       EntityName TypeArguments?
    //
    //   TemplateType:
    //       TemplateHead Type[~Extends] TemplateTypeSpans
    //
    //   TemplateTypeSpans:
    //       TemplateTail
    //       TemplateTypeMiddleList TemplateTail
    //
    //   TemplateTypeMiddleList:
    //       TemplateMiddle Type[~Extends]
    //       TemplateTypeMiddleList TemplateMiddle Type[~Extends]
    //
    //   TypeArguments:
    //       `<` TypeArgumentList `,`? `>`
    //
    //   TypeArgumentList:
    //       Type[~Extends]
    //       TypeArgumentList `,` Type[~Extends]
    //
    pub const NON_ARRAY: TypePrecedence = TypePrecedence(7);

    pub const LOWEST: TypePrecedence = Self::CONDITIONAL;
    pub const HIGHEST: TypePrecedence = Self::NON_ARRAY;
}

/// `GetTypeNodePrecedence` — gets the precedence of a TypeNode.
pub fn get_type_node_precedence(n: &Node, nodes: &[Node]) -> TypePrecedence {
    match n.kind {
        Kind::ConditionalType => TypePrecedence::CONDITIONAL,
        Kind::JSDocOptionalType | Kind::JSDocVariadicType => TypePrecedence::JSDOC,
        Kind::FunctionType | Kind::ConstructorType => TypePrecedence::FUNCTION,
        Kind::UnionType => TypePrecedence::UNION,
        Kind::IntersectionType => TypePrecedence::INTERSECTION,
        Kind::TypeOperator => TypePrecedence::TYPE_OPERATOR,
        Kind::InferType => {
            if nodes[n
                .as_infer_type_node()
                .type_parameter
                .expect("InferTypeNode without TypeParameter")]
            .as_type_parameter_declaration()
            .constraint
            .is_some()
            {
                // `infer T extends U` must be treated as FunctionTypeNode precedence as the `extends` clause eagerly consumes
                // TypeNode
                return TypePrecedence::FUNCTION;
            }
            TypePrecedence::TYPE_OPERATOR
        }
        Kind::IndexedAccessType | Kind::ArrayType | Kind::OptionalType => TypePrecedence::POSTFIX,
        Kind::TypeQuery => {
            // TypeQueryNode is actually a NonArrayType, but we treat it as TypeOperatorNode
            // precedence so that it is parenthesized when used in a PostfixType
            // context (e.g., `(typeof C)[]` instead of `typeof C[]`)
            TypePrecedence::TYPE_OPERATOR
        }
        Kind::AnyKeyword
        | Kind::UnknownKeyword
        | Kind::StringKeyword
        | Kind::NumberKeyword
        | Kind::BigIntKeyword
        | Kind::SymbolKeyword
        | Kind::BooleanKeyword
        | Kind::UndefinedKeyword
        | Kind::NeverKeyword
        | Kind::ObjectKeyword
        | Kind::IntrinsicKeyword
        | Kind::VoidKeyword
        | Kind::JSDocAllType
        | Kind::JSDocNullableType
        | Kind::JSDocNonNullableType
        | Kind::LiteralType
        | Kind::TypePredicate
        | Kind::TypeReference
        | Kind::TypeLiteral
        | Kind::TupleType
        | Kind::RestType
        | Kind::ParenthesizedType
        | Kind::ThisType
        | Kind::MappedType
        | Kind::NamedTupleMember
        | Kind::TemplateLiteralType
        | Kind::ImportType
        // These occur in pseudo-types like `f<T>.C`, where `f` is a generic function and `C` is a local type
        | Kind::PropertyAccessExpression
        | Kind::ExpressionWithTypeArguments => TypePrecedence::NON_ARRAY,
        _ => panic!("unhandled TypeNode: {}", n.kind.kind_string()),
    }
}
