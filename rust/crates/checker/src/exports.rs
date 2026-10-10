//! Ported from `tsc/internal/checker/exports.go` (Go baseline ec47d33).
//!
//! In Go this file holds the checker's public-facing API: thin wrappers that
//! delegate to unexported implementation methods, plus a few free functions.
//!
//! Rust has no overloading and no private/public method-name pairs, so the
//! port works as follows:
//!
//! * When the Go `GetX` wrapper and the internal `getX` have the same effective
//!   signature after the arena/ID adaptation, a single `pub fn` exists (the
//!   internal one, widened to `pub` where needed). Those are listed in the
//!   delegation table at the bottom of this file rather than re-declared.
//! * When the Go public signature differs (extra positional parameters that
//!   the wrapper fills in), a `pub fn ..._api` adapter is defined here, per the
//!   crate's existing convention (e.g. `get_symbol_at_location_api`).
//! * Field getters and genuinely distinct wrappers live in `impl Checker`
//!   blocks below; free functions are re-exported or defined at the top level.

use tsc_ast::{self as ast, NodeId, SymbolId};

use crate::checker_core::{CheckMode, Checker};
use crate::checker_types::UnionReduction;
use crate::types::{SignatureId, TypeArena, TypeFlags, TypeId};

// -- Free helper functions (exports.go:91-97, 179, 231-240, 410) -----------------

/// `func IsTypeUsableAsPropertyName` (exports.go:91).
pub use crate::types::is_type_usable_as_property_name;

/// `func GetPropertyNameFromType` (exports.go:95) — re-export of the
/// `utilities.go` helper.
pub use crate::utilities::get_property_name_from_type;

/// `func GetDeclarationModifierFlagsFromSymbol` (exports.go:179).
pub use crate::utilities::get_declaration_modifier_flags_from_symbol;

/// `func IsTupleType` (exports.go:231).
pub use crate::checker_core::is_tuple_type;

/// `func IsLiteralType` (exports.go:411-ish; `isLiteralType` lives in
/// checker_d.rs).
pub use crate::checker_d::is_literal_type;

/// `func IsTupleTypeTarget` (exports.go:235).
pub fn is_tuple_type_target(types: &TypeArena, t: TypeId) -> bool {
    crate::checker_core::is_tuple_type(types, t) && types.get(t).target() == Some(t)
}

/// `func IsDistributedTypeParameter` (exports.go:410).
pub fn is_distributed_type_parameter(types: &TypeArena, t: TypeId) -> bool {
    let ty = types.get(t);
    ty.flags
        .intersects(TypeFlags::TYPE_PARAMETER)
        && ty.as_type_parameter().is_distributed
}

// -- Simple "global" accessors (exports.go:8-87) ---------------------------------

impl Checker {
    /// `func (c *Checker) GetStringType` (exports.go:8).
    pub fn get_string_type(&self) -> TypeId {
        self.string_type
    }
    /// `func (c *Checker) GetNumberType` (exports.go:12).
    pub fn get_number_type(&self) -> TypeId {
        self.number_type
    }
    /// `func (c *Checker) GetBooleanType` (exports.go:16).
    pub fn get_boolean_type(&self) -> TypeId {
        self.boolean_type
    }
    /// `func (c *Checker) GetVoidType` (exports.go:20).
    pub fn get_void_type(&self) -> TypeId {
        self.void_type
    }
    /// `func (c *Checker) GetUndefinedType` (exports.go:24).
    pub fn get_undefined_type(&self) -> TypeId {
        self.undefined_type
    }
    /// `func (c *Checker) GetNullType` (exports.go:28).
    pub fn get_null_type(&self) -> TypeId {
        self.null_type
    }
    /// `func (c *Checker) GetAnyType` (exports.go:32).
    pub fn get_any_type(&self) -> TypeId {
        self.any_type
    }
    /// `func (c *Checker) GetErrorType` (exports.go:36).
    pub fn get_error_type(&self) -> TypeId {
        self.error_type
    }
    /// `func (c *Checker) GetNeverType` (exports.go:40).
    pub fn get_never_type(&self) -> TypeId {
        self.never_type
    }
    /// `func (c *Checker) GetUnknownType` (exports.go:44).
    pub fn get_unknown_type(&self) -> TypeId {
        self.unknown_type
    }
    /// `func (c *Checker) GetBigIntType` (exports.go:48).
    pub fn get_big_int_type(&self) -> TypeId {
        self.bigint_type
    }
    /// `func (c *Checker) GetESSymbolType` (exports.go:52).
    pub fn get_es_symbol_type(&self) -> TypeId {
        self.es_symbol_type
    }
    /// `func (c *Checker) GetNonPrimitiveType` (exports.go:56).
    pub fn get_non_primitive_type(&self) -> TypeId {
        self.non_primitive_type
    }
    /// `func (c *Checker) GetUnknownSymbol` (exports.go:64).
    pub fn get_unknown_symbol(&self) -> SymbolId {
        self.unknown_symbol
    }
    /// `func (c *Checker) GetUndefinedSymbol` (exports.go:68).
    pub fn get_undefined_symbol(&self) -> SymbolId {
        self.undefined_symbol
    }
    /// `func (c *Checker) GetArgumentsSymbol` (exports.go:72).
    pub fn get_arguments_symbol(&self) -> SymbolId {
        self.arguments_symbol
    }
    /// `func (c *Checker) GetUnknownSignature` (exports.go:76).
    pub fn get_unknown_signature(&self) -> SignatureId {
        self.unknown_signature
    }

    /// `func (c *Checker) GetNameTypeOfSymbol` (exports.go:84).
    pub fn get_name_type_of_symbol(&mut self, symbol: SymbolId) -> Option<TypeId> {
        self.value_symbol_links.get(symbol).name_type
    }
}

// -- Wrappers whose public signature differs from the internal one ---------------

impl Checker {
    /// `func (c *Checker) TryFindAmbientModule` (exports.go:119).
    pub fn try_find_ambient_module_api(&mut self, module_name: &str) -> Option<SymbolId> {
        self.try_find_ambient_module(module_name, true /* with_augmentations */)
    }

    /// `func (c *Checker) ResolveExternalModuleName` (exports.go:135).
    pub fn resolve_external_module_name_api(
        &mut self,
        module_specifier: NodeId,
        import_attributes_type: Option<TypeId>,
    ) -> Option<SymbolId> {
        self.resolve_external_module_name(
            module_specifier,
            Some(module_specifier),
            true, // ignore_errors
            import_attributes_type,
        )
    }

    /// `func (c *Checker) GetResolvedSignature` (exports.go:271).
    pub fn get_resolved_signature_api(&mut self, node: NodeId) -> Option<SignatureId> {
        self.get_resolved_signature(node, None, CheckMode::NORMAL)
    }

    /// `func (c *Checker) GetFullyQualifiedName` (exports.go:330).
    pub fn get_fully_qualified_name_api(&mut self, symbol: SymbolId) -> String {
        self.get_fully_qualified_name(symbol, None)
    }

    /// `func (c *Checker) GetUnionTypeEx` (exports.go:382).
    pub fn get_union_type_ex_api(&mut self, types: &[TypeId], union_reduction: UnionReduction) -> TypeId {
        self.get_union_type_ex(types, union_reduction, None, None)
    }

    /// `func (c *Checker) RequiresAddingImplicitUndefined` (exports.go:386).
    pub fn requires_adding_implicit_undefined_api(&mut self, node: NodeId) -> bool {
                let __program = self.program.clone().expect("program");
        let nodes = __program.nodes((node).file_index());;
        let mut enclosing_declaration =
            ast::find_ancestor(Some(node), &nodes, &mut |n, _| ast::is_declaration(n));
        if enclosing_declaration.is_none() {
            enclosing_declaration = ast::get_source_file_of_node(Some(node), &nodes);
        }
        let Some(enclosing_declaration) = enclosing_declaration else {
            return false;
        };
        let Some(symbol) = nodes[node].symbol() else {
            return false;
        };
        drop(nodes);
        self.requires_adding_implicit_undefined(node, Some(symbol), Some(enclosing_declaration))
    }

    /// `func (c *Checker) ResolveName` (exports.go:308).
    pub fn resolve_name_api(
        &mut self,
        name: &str,
        location: Option<NodeId>,
        meaning: ast::SymbolFlags,
        exclude_globals: bool,
    ) -> Option<SymbolId> {
        let resolve = self
            .resolve_name
            .clone()
            .expect("resolveName not initialized");
        resolve(self, location, name, meaning, None, true, exclude_globals)
    }

    /// `func (c *Checker) GetJsxFragmentFactory` (exports.go:300).
    pub fn get_jsx_fragment_factory(&mut self, location: NodeId) -> String {
        if let Some(entity) = self.get_jsx_fragment_factory_entity(location) {
                        let __program = self.program.clone().expect("program");
            let nodes = __program.nodes((location).file_index());;
            let first = ast::get_first_identifier(entity, &nodes);
            return nodes[first].as_identifier().text.clone();
        }
        String::new()
    }

    /// `func (c *Checker) WasCanceled` (exports.go:183).
    pub fn was_canceled(&self) -> bool {
        self.was_canceled
    }

    /// `func (c *Checker) CompareSymbols` (exports.go:406). Returns an
    /// ordering int like Go (`<0`, `0`, `>0`).
    pub fn compare_symbols(&self, s1: SymbolId, s2: SymbolId) -> i32 {
        self.compare_symbols_worker(Some(s1), Some(s2))
    }
}

// `func (c *Checker) IsGenericType` — collapses to `is_generic_type`
// (checker_d.rs), which is `pub`.

// -- Delegation table -------------------------------------------------------------
//
// The remaining Go public wrappers collapse onto existing `pub` methods whose
// signatures are identical after the arena/ID adaptation. They are not
// re-declared here; call the internals directly.
//
//   GetBaseTypeOfLiteralType     -> checker_d.rs::get_base_type_of_literal_type
//   GetUnionType                 -> checker_core.rs::get_union_type
//   GetGlobalSymbol              -> checker_core.rs::get_global_symbol
//   GetMergedSymbol              -> checker_core.rs::get_merged_symbol
//   GetSymbolOfNode              -> checker_b.rs::get_symbol_of_node
//   GetSymbolOfDeclaration       -> checker_core.rs::get_symbol_of_declaration
//   GetParentOfSymbol            -> checker_b.rs::get_parent_of_symbol
//   GetImmediateAliasedSymbol    -> checker_a.rs::get_immediate_aliased_symbol
//   GetTargetSymbol              -> checker_c.rs::get_target_symbol
//   GetTypeOnlyAliasDeclaration  -> checker_a.rs::get_type_only_alias_declaration
//   ResolveExternalModuleSymbol  -> checker_b.rs::resolve_external_module_symbol
//   GetTypeFromTypeNode          -> checker_core.rs::get_type_from_type_node
//   IsArrayLikeType              -> checker_c.rs::is_array_like_type
//   GetPropertiesOfType          -> checker_c.rs::get_properties_of_type
//   GetPropertyOfType            -> checker_c.rs::get_property_of_type
//   TypeHasCallOrConstructSignatures -> checker_d.rs::type_has_call_or_construct_signatures
//   IsPropertyAccessible         -> checker_b.rs::is_property_accessible
//   GetTypeOfPropertyOfContextualType -> checker_d.rs::get_type_of_property_of_contextual_type
//   GetSignaturesOfType          -> checker_c.rs::get_signatures_of_type
//   GetDeclaredTypeOfSymbol      -> checker_core.rs::get_declared_type_of_symbol
//   GetTypeOfSymbol              -> checker_c.rs::get_type_of_symbol
//   GetNonMissingTypeOfSymbol    -> checker_c.rs::get_non_missing_type_of_symbol
//   GetConstraintOfTypeParameter -> checker_c.rs::get_constraint_of_type_parameter
//   GetTrueTypeOfConditionalType -> checker_d.rs::get_true_type_from_conditional_type
//   GetFalseTypeOfConditionalType -> checker_d.rs::get_false_type_from_conditional_type
//   GetDefaultFromTypeParameter  -> checker_c.rs::get_default_from_type_parameter
//   GetEffectiveDeclarationFlags -> checker_a.rs::get_effective_declaration_flags
//   GetBaseConstraintOfType      -> checker_d.rs::get_base_constraint_of_type
//   GetTypePredicateOfSignature  -> relater.rs::get_type_predicate_of_signature
//   IsArrayType                  -> checker_core.rs::is_array_type
//   IsReadonlySymbol             -> checker_b.rs::is_readonly_symbol
//   GetReturnTypeOfSignature     -> checker_c.rs::get_return_type_of_signature
//   HasEffectiveRestParameter    -> relater.rs::has_effective_rest_parameter
//   GetLocalTypeParametersOfClassOrInterfaceOrTypeAlias
//                                -> checker_c.rs::get_local_type_parameters_of_class_or_interface_or_type_alias
//   GetContextualTypeForObjectLiteralElement
//                                -> checker_d.rs::get_contextual_type_for_object_literal_element
//   TypePredicateToString        -> printer_util.rs::type_predicate_to_string
//   GetExpandedParameters        -> checker_core.rs::get_expanded_parameters
//   GetTypeOfPropertyOfType      -> checker_c.rs::get_type_of_property_of_type
//   GetContextualTypeForArgumentAtIndex -> checker_d.rs::get_contextual_type_for_argument_at_index
//   GetAwaitedType               -> checker_d.rs::get_awaited_type
//   GetIndexSignaturesAtLocation -> checker_d.rs::get_index_signatures_at_location
//   GetResolvedSymbol            -> checker_b.rs::get_resolved_symbol
//   GetJsxNamespace              -> jsx.rs::get_jsx_namespace
//   GetSymbolFlags               -> checker_c.rs::get_symbol_flags
//   GetBaseTypes                 -> checker_c.rs::get_base_types
//   GetApparentType              -> checker_c.rs::get_apparent_type
//   GetReducedType               -> checker_c.rs::get_reduced_type
//   GetBaseConstructorTypeOfClass -> checker_c.rs::get_base_constructor_type_of_class
//   GetMemberOverrideModifierStatus -> checker_a.rs::get_member_override_modifier_status
//   GetRestTypeOfSignature       -> checker_b.rs::get_rest_type_of_signature
//   GetTypeArguments             -> checker_core.rs::get_type_arguments
//   GetIndexInfoOfType           -> checker_c.rs::get_index_info_of_type
//   GetIndexTypeOfType           -> checker_c.rs::get_index_type_of_type
//   GetIndexInfosOfType          -> checker_c.rs::get_index_infos_of_type
//   IsContextSensitive           -> checker_d.rs::is_context_sensitive
//   FillMissingTypeArguments     -> checker_c.rs::fill_missing_type_arguments
//   GetMinTypeArgumentCount      -> checker_c.rs::get_min_type_argument_count
//   GetWidenedLiteralType        -> checker_d.rs::get_widened_literal_type
//   IsTypeAssignableTo           -> relater.rs::is_type_assignable_to
//   RemoveMissingOrUndefinedType -> checker_d.rs::remove_missing_or_undefined_type
//   GetWidenedType               -> checker_c.rs::get_widened_type
