// Ported from tsc/internal/printer/helpers.go @ ec47d33c23e464a17cdf2475632cba629bee8763

use std::cmp::Ordering;
use std::sync::Arc;
use std::sync::LazyLock;

/// `type UniqueNameFn func(name string, isGeneratedName bool) bool` — used by
/// helper text callbacks to allocate unique names.
pub type UniqueNameFn<'a> = dyn FnMut(&str) -> String + 'a;

/// `type Priority struct`
#[derive(Clone, Copy, PartialEq, Eq, Debug)]
pub struct Priority {
    pub value: i32,
}

/// `TextCallback` — a function yielding an ES3-compatible raw script text.
pub type EmitHelperTextCallback =
    Box<dyn Fn(&mut UniqueNameFn<'_>) -> String + Send + Sync + 'static>;

/// `type EmitHelper struct`
pub struct EmitHelper {
    /// A unique name for this helper.
    pub name: &'static str,
    /// Indicates whether the helper MUST be emitted in the current scope.
    pub scoped: bool,
    /// ES3-compatible raw script text
    pub text: &'static str,
    /// A function yielding an ES3-compatible raw script text.
    pub text_callback: Option<EmitHelperTextCallback>,
    /// Helpers with a higher priority are emitted earlier than other helpers on the node.
    pub priority: Option<Priority>,
    /// Emit helpers this helper depends on
    pub dependencies: Vec<Arc<EmitHelper>>,
    /// The name of the helper to use when importing via `--importHelpers`.
    pub import_name: &'static str,
}

/// An `Arc<EmitHelper>` whose equality/hash is by pointer identity, matching
/// Go's `*EmitHelper` comparisons (`x == y`, map keys, `AppendIfUnique`).
#[derive(Clone)]
pub struct EmitHelperRef(pub Arc<EmitHelper>);

impl EmitHelperRef {
    /// `x == y` — pointer equality.
    pub fn ptr_eq(a: &Arc<EmitHelper>, b: &Arc<EmitHelper>) -> bool {
        Arc::ptr_eq(a, b)
    }
}

impl PartialEq for EmitHelperRef {
    fn eq(&self, other: &Self) -> bool {
        Arc::ptr_eq(&self.0, &other.0)
    }
}

impl Eq for EmitHelperRef {}

impl std::hash::Hash for EmitHelperRef {
    fn hash<H: std::hash::Hasher>(&self, state: &mut H) {
        state.write_usize(Arc::as_ptr(&self.0) as usize);
    }
}

/// `compareEmitHelpers` — helpers with a higher priority sort earlier;
/// otherwise insertion order is preserved (stable sort).
pub fn compare_emit_helpers(x: &Arc<EmitHelper>, y: &Arc<EmitHelper>) -> Ordering {
    if Arc::ptr_eq(x, y) {
        return Ordering::Equal;
    }
    if x.priority == y.priority {
        return Ordering::Equal;
    }
    match (x.priority, y.priority) {
        (None, _) => Ordering::Greater,
        (_, None) => Ordering::Less,
        (Some(a), Some(b)) => a.value.cmp(&b.value),
    }
}

macro_rules! emit_helper {
    ($name:ident, $body:expr) => {
        /// `var <helper>` — the shared `*EmitHelper` value; `Arc` preserves the
        /// pointer identity Go relies on for deduplication and sorting.
        pub fn $name() -> Arc<EmitHelper> {
            static HELPER: LazyLock<Arc<EmitHelper>> = LazyLock::new(|| Arc::new($body));
            HELPER.clone()
        }
    };
}

// TypeScript Helpers

emit_helper!(decorate_helper, EmitHelper {
    name: "typescript:decorate",
    import_name: "__decorate",
    scoped: false,
    priority: Some(Priority { value: 2 }),
    text: r#"var __decorate = (this && this.__decorate) || function (decorators, target, key, desc) {
    var c = arguments.length, r = c < 3 ? target : desc === null ? desc = Object.getOwnPropertyDescriptor(target, key) : desc, d;
    if (typeof Reflect === "object" && typeof Reflect.decorate === "function") r = Reflect.decorate(decorators, target, key, desc);
    else for (var i = decorators.length - 1; i >= 0; i--) if (d = decorators[i]) r = (c < 3 ? d(r) : c > 3 ? d(target, key, r) : d(target, key)) || r;
    return c > 3 && r && Object.defineProperty(target, key, r), r;
};"#,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(metadata_helper, EmitHelper {
    name: "typescript:metadata",
    import_name: "__metadata",
    scoped: false,
    priority: Some(Priority { value: 3 }),
    text: r#"var __metadata = (this && this.__metadata) || function (k, v) {
    if (typeof Reflect === "object" && typeof Reflect.metadata === "function") return Reflect.metadata(k, v);
};"#,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(param_helper, EmitHelper {
    name: "typescript:param",
    import_name: "__param",
    scoped: false,
    priority: Some(Priority { value: 4 }),
    text: r#"var __param = (this && this.__param) || function (paramIndex, decorator) {
    return function (target, key) { decorator(target, key, paramIndex); }
};"#,
    text_callback: None,
    dependencies: vec![],
});

// ESNext Helpers

emit_helper!(add_disposable_resource_helper, EmitHelper {
    name: "typescript:addDisposableResource",
    import_name: "__addDisposableResource",
    scoped: false,
    text: r#"var __addDisposableResource = (this && this.__addDisposableResource) || function (env, value, async) {
    if (value !== null && value !== void 0) {
        if (typeof value !== "object" && typeof value !== "function") throw new TypeError("Object expected.");
        var dispose, inner;
        if (async) {
            if (!Symbol.asyncDispose) throw new TypeError("Symbol.asyncDispose is not defined.");
            dispose = value[Symbol.asyncDispose];
        }
        if (dispose === void 0) {
            if (!Symbol.dispose) throw new TypeError("Symbol.dispose is not defined.");
            dispose = value[Symbol.dispose];
            if (async) inner = dispose;
        }
        if (typeof dispose !== "function") throw new TypeError("Object not disposable.");
        if (inner) dispose = function() { try { inner.call(this); } catch (e) { return Promise.reject(e); } };
        env.stack.push({ value: value, dispose: dispose, async: async });
    }
    else if (async) {
        env.stack.push({ async: true });
    }
    return value;
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(dispose_resources_helper, EmitHelper {
    name: "typescript:disposeResources",
    import_name: "__disposeResources",
    scoped: false,
    text: r#"var __disposeResources = (this && this.__disposeResources) || (function (SuppressedError) {
    return function (env) {
        function fail(e) {
            env.error = env.hasError ? new SuppressedError(e, env.error, "An error was suppressed during disposal.") : e;
            env.hasError = true;
        }
        var r, s = 0;
        function next() {
            while (r = env.stack.pop()) {
                try {
                    if (!r.async && s === 1) return s = 0, env.stack.push(r), Promise.resolve().then(next);
                    if (r.dispose) {
                        var result = r.dispose.call(r.value);
                        if (r.async) return s |= 2, Promise.resolve(result).then(next, function(e) { fail(e); return next(); });
                    }
                    else s |= 1;
                }
                catch (e) {
                    fail(e);
                }
            }
            if (s === 1) return env.hasError ? Promise.reject(env.error) : Promise.resolve();
            if (env.hasError) throw env.error;
        }
        return next();
    };
})(typeof SuppressedError === "function" ? SuppressedError : function (error, suppressed, message) {
    var e = new Error(message);
    return e.name = "SuppressedError", e.error = error, e.suppressed = suppressed, e;
});"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

// Class Fields Helpers

emit_helper!(class_private_field_get_helper, EmitHelper {
    name: "typescript:classPrivateFieldGet",
    import_name: "__classPrivateFieldGet",
    scoped: false,
    text: r#"var __classPrivateFieldGet = (this && this.__classPrivateFieldGet) || function (receiver, state, kind, f) {
    if (kind === "a" && !f) throw new TypeError("Private accessor was defined without a getter");
    if (typeof state === "function" ? receiver !== state || !f : !state.has(receiver)) throw new TypeError("Cannot read private member from an object whose class did not declare it");
    return kind === "m" ? f : kind === "a" ? f.call(receiver) : f ? f.value : state.get(receiver);
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(class_private_field_set_helper, EmitHelper {
    name: "typescript:classPrivateFieldSet",
    import_name: "__classPrivateFieldSet",
    scoped: false,
    text: r#"var __classPrivateFieldSet = (this && this.__classPrivateFieldSet) || function (receiver, state, value, kind, f) {
    if (kind === "m") throw new TypeError("Private method is not writable");
    if (kind === "a" && !f) throw new TypeError("Private accessor was defined without a setter");
    if (typeof state === "function" ? receiver !== state || !f : !state.has(receiver)) throw new TypeError("Cannot write private member to an object whose class did not declare it");
    return (kind === "a" ? f.call(receiver, value) : f ? f.value = value : state.set(receiver, value)), value;
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(class_private_field_in_helper, EmitHelper {
    name: "typescript:classPrivateFieldIn",
    import_name: "__classPrivateFieldIn",
    scoped: false,
    text: r#"var __classPrivateFieldIn = (this && this.__classPrivateFieldIn) || function(state, receiver) {
    if (receiver === null || (typeof receiver !== "object" && typeof receiver !== "function")) throw new TypeError("Cannot use 'in' operator on non-object");
    return typeof state === "function" ? receiver === state : state.has(receiver);
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

// ES2018 Helpers

emit_helper!(await_helper, EmitHelper {
    name: "typescript:await",
    import_name: "__await",
    scoped: false,
    text: r#"var __await = (this && this.__await) || function (v) { return this instanceof __await ? (this.v = v, this) : new __await(v); }"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(async_generator_helper, EmitHelper {
    name: "typescript:asyncGenerator",
    import_name: "__asyncGenerator",
    scoped: false,
    text: r#"var __asyncGenerator = (this && this.__asyncGenerator) || function (thisArg, _arguments, generator) {
    if (!Symbol.asyncIterator) throw new TypeError("Symbol.asyncIterator is not defined.");
    var g = generator.apply(thisArg, _arguments || []), i, q = [];
    return i = Object.create((typeof AsyncIterator === "function" ? AsyncIterator : Object).prototype), verb("next"), verb("throw"), verb("return", awaitReturn), i[Symbol.asyncIterator] = function () { return this; }, i;
    function awaitReturn(f) { return function (v) { return Promise.resolve(v).then(f, reject); }; }
    function verb(n, f) { if (g[n]) { i[n] = function (v) { return new Promise(function (a, b) { q.push([n, v, a, b]) > 1 || resume(n, v); }); }; if (f) i[n] = f(i[n]); } }
    function resume(n, v) { try { step(g[n](v)); } catch (e) { settle(q[0][3], e); } }
    function step(r) { r.value instanceof __await ? Promise.resolve(r.value.v).then(fulfill, reject) : settle(q[0][2], r); }
    function fulfill(value) { resume("next", value); }
    function reject(value) { resume("throw", value); }
    function settle(f, v) { if (f(v), q.shift(), q.length) resume(q[0][0], q[0][1]); }
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![await_helper()],
});

emit_helper!(async_delegator_helper, EmitHelper {
    name: "typescript:asyncDelegator",
    import_name: "__asyncDelegator",
    scoped: false,
    text: r#"var __asyncDelegator = (this && this.__asyncDelegator) || function (o) {
    var i, p;
    return i = {}, verb("next"), verb("throw", function (e) { throw e; }), verb("return"), i[Symbol.iterator] = function () { return this; }, i;
    function verb(n, f) { i[n] = o[n] ? function (v) { return (p = !p) ? { value: __await(o[n](v)), done: false } : f ? f(v) : v; } : f; }
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![await_helper()],
});

emit_helper!(async_values_helper, EmitHelper {
    name: "typescript:asyncValues",
    import_name: "__asyncValues",
    scoped: false,
    text: r#"var __asyncValues = (this && this.__asyncValues) || function (o) {
    if (!Symbol.asyncIterator) throw new TypeError("Symbol.asyncIterator is not defined.");
    var m = o[Symbol.asyncIterator], i;
    return m ? m.call(o) : (o = typeof __values === "function" ? __values(o) : o[Symbol.iterator](), i = {}, verb("next"), verb("throw"), verb("return"), i[Symbol.asyncIterator] = function () { return this; }, i);
    function verb(n) { i[n] = o[n] && function (v) { return new Promise(function (resolve, reject) { v = o[n](v), settle(resolve, reject, v.done, v.value); }); }; }
    function settle(resolve, reject, d, v) { Promise.resolve(v).then(function(v) { resolve({ value: v, done: d }); }, reject); }
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

// ES2018 Destructuring Helpers

emit_helper!(rest_helper, EmitHelper {
    name: "typescript:rest",
    import_name: "__rest",
    scoped: false,
    text: r#"var __rest = (this && this.__rest) || function (s, e) {
    var t = {};
    for (var p in s) if (Object.prototype.hasOwnProperty.call(s, p) && e.indexOf(p) < 0)
        t[p] = s[p];
    if (s != null && typeof Object.getOwnPropertySymbols === "function")
        for (var i = 0, p = Object.getOwnPropertySymbols(s); i < p.length; i++) {
            if (e.indexOf(p[i]) < 0 && Object.prototype.propertyIsEnumerable.call(s, p[i]))
                t[p[i]] = s[p[i]];
        }
    return t;
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(awaiter_helper, EmitHelper {
    name: "typescript:awaiter",
    import_name: "__awaiter",
    scoped: false,
    priority: Some(Priority { value: 5 }),
    text: r#"var __awaiter = (this && this.__awaiter) || function (thisArg, _arguments, P, generator) {
    function adopt(value) { return value instanceof P ? value : new P(function (resolve) { resolve(value); }); }
    return new (P || (P = Promise))(function (resolve, reject) {
        function fulfilled(value) { try { step(generator.next(value)); } catch (e) { reject(e); } }
        function rejected(value) { try { step(generator["throw"](value)); } catch (e) { reject(e); } }
        function step(result) { result.done ? resolve(result.value) : adopt(result.value).then(fulfilled, rejected); }
        step((generator = generator.apply(thisArg, _arguments || [])).next());
    });
};"#,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(async_super_helper, EmitHelper {
    name: "typescript:async-super",
    scoped: true,
    text: "",
    priority: None,
    import_name: "",
    dependencies: vec![],
    text_callback: Some(Box::new(|make_unique_name: &mut UniqueNameFn<'_>| {
        format!("\nconst {} = name => super[name];", make_unique_name("_superIndex"))
    })),
});

emit_helper!(advanced_async_super_helper, EmitHelper {
    name: "typescript:advanced-async-super",
    scoped: true,
    text: "",
    priority: None,
    import_name: "",
    dependencies: vec![],
    text_callback: Some(Box::new(|make_unique_name: &mut UniqueNameFn<'_>| {
        format!(
            "\nconst {} = (function (geti, seti) {{\n    const cache = Object.create(null);\n    return name => cache[name] || (cache[name] = {{ get value() {{ return geti(name); }}, set value(v) {{ seti(name, v); }} }});\n}})(name => super[name], (name, value) => super[name] = value);",
            make_unique_name("_superIndex")
        )
    })),
});

// ES Decorator Helpers

emit_helper!(es_decorate_helper, EmitHelper {
    name: "typescript:esDecorate",
    import_name: "__esDecorate",
    scoped: false,
    priority: Some(Priority { value: 2 }),
    text: r#"var __esDecorate = (this && this.__esDecorate) || function (ctor, descriptorIn, decorators, contextIn, initializers, extraInitializers) {
    function accept(f) { if (f !== void 0 && typeof f !== "function") throw new TypeError("Function expected"); return f; }
    var kind = contextIn.kind, key = kind === "getter" ? "get" : kind === "setter" ? "set" : "value";
    var target = !descriptorIn && ctor ? contextIn["static"] ? ctor : ctor.prototype : null;
    var descriptor = descriptorIn || (target ? Object.getOwnPropertyDescriptor(target, contextIn.name) : {});
    var _, done = false;
    for (var i = decorators.length - 1; i >= 0; i--) {
        var context = {};
        for (var p in contextIn) context[p] = p === "access" ? {} : contextIn[p];
        for (var p in contextIn.access) context.access[p] = contextIn.access[p];
        context.addInitializer = function (f) { if (done) throw new TypeError("Cannot add initializers after decoration has completed"); extraInitializers.push(accept(f || null)); };
        var result = (0, decorators[i])(kind === "accessor" ? { get: descriptor.get, set: descriptor.set } : descriptor[key], context);
        if (kind === "accessor") {
            if (result === void 0) continue;
            if (result === null || typeof result !== "object") throw new TypeError("Object expected");
            if (_ = accept(result.get)) descriptor.get = _;
            if (_ = accept(result.set)) descriptor.set = _;
            if (_ = accept(result.init)) initializers.unshift(_);
        }
        else if (_ = accept(result)) {
            if (kind === "field") initializers.unshift(_);
            else descriptor[key] = _;
        }
    }
    if (target) Object.defineProperty(target, contextIn.name, descriptor);
    done = true;
};"#,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(run_initializers_helper, EmitHelper {
    name: "typescript:runInitializers",
    import_name: "__runInitializers",
    scoped: false,
    priority: Some(Priority { value: 2 }),
    text: r#"var __runInitializers = (this && this.__runInitializers) || function (thisArg, initializers, value) {
    var useValue = arguments.length > 2;
    for (var i = 0; i < initializers.length; i++) {
        value = useValue ? initializers[i].call(thisArg, value) : initializers[i].call(thisArg);
    }
    return useValue ? value : void 0;
};"#,
    text_callback: None,
    dependencies: vec![],
});

// ES2015 Helpers

emit_helper!(make_template_object_helper, EmitHelper {
    name: "typescript:makeTemplateObject",
    import_name: "__makeTemplateObject",
    scoped: false,
    priority: Some(Priority { value: 0 }),
    text: r#"var __makeTemplateObject = (this && this.__makeTemplateObject) || function (cooked, raw) {
    if (Object.defineProperty) { Object.defineProperty(cooked, "raw", { value: raw }); } else { cooked.raw = raw; }
    return cooked;
};"#,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(prop_key_helper, EmitHelper {
    name: "typescript:propKey",
    import_name: "__propKey",
    scoped: false,
    text: r#"var __propKey = (this && this.__propKey) || function (x) {
    return typeof x === "symbol" ? x : "".concat(x);
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

// https://tc39.es/ecma262/#sec-setfunctionname
emit_helper!(set_function_name_helper, EmitHelper {
    name: "typescript:setFunctionName",
    import_name: "__setFunctionName",
    scoped: false,
    text: r#"var __setFunctionName = (this && this.__setFunctionName) || function (f, name, prefix) {
    if (typeof name === "symbol") name = name.description ? "[".concat(name.description, "]") : "";
    return Object.defineProperty(f, "name", { configurable: true, value: prefix ? "".concat(prefix, " ", name) : name });
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

// ES Module Helpers

emit_helper!(create_binding_helper, EmitHelper {
    name: "typescript:commonjscreatebinding",
    import_name: "__createBinding",
    scoped: false,
    priority: Some(Priority { value: 1 }),
    text: r#"var __createBinding = (this && this.__createBinding) || (Object.create ? (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    var desc = Object.getOwnPropertyDescriptor(m, k);
    if (!desc || ("get" in desc ? !m.__esModule : desc.writable || desc.configurable)) {
      desc = { enumerable: true, get: function() { return m[k]; } };
    }
    Object.defineProperty(o, k2, desc);
}) : (function(o, m, k, k2) {
    if (k2 === undefined) k2 = k;
    o[k2] = m[k];
}));"#,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(set_module_default_helper, EmitHelper {
    name: "typescript:commonjscreatevalue",
    import_name: "__setModuleDefault",
    scoped: false,
    priority: Some(Priority { value: 1 }),
    text: r#"var __setModuleDefault = (this && this.__setModuleDefault) || (Object.create ? (function(o, v) {
    Object.defineProperty(o, "default", { enumerable: true, value: v });
}) : function(o, v) {
    o["default"] = v;
});"#,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(import_star_helper, EmitHelper {
    name: "typescript:commonjsimportstar",
    import_name: "__importStar",
    scoped: false,
    priority: Some(Priority { value: 2 }),
    text: r#"var __importStar = (this && this.__importStar) || (function () {
    var ownKeys = function(o) {
        ownKeys = Object.getOwnPropertyNames || function (o) {
            var ar = [];
            for (var k in o) if (Object.prototype.hasOwnProperty.call(o, k)) ar[ar.length] = k;
            return ar;
        };
        return ownKeys(o);
    };
    return function (mod) {
        if (mod && mod.__esModule) return mod;
        var result = {};
        if (mod != null) for (var k = ownKeys(mod), i = 0; i < k.length; i++) if (k[i] !== "default") __createBinding(result, mod, k[i]);
        __setModuleDefault(result, mod);
        return result;
    };
})();"#,
    text_callback: None,
    dependencies: vec![create_binding_helper(), set_module_default_helper()],
});

emit_helper!(import_default_helper, EmitHelper {
    name: "typescript:commonjsimportdefault",
    import_name: "__importDefault",
    scoped: false,
    text: r#"var __importDefault = (this && this.__importDefault) || function (mod) {
    return (mod && mod.__esModule) ? mod : { "default": mod };
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});

emit_helper!(export_star_helper, EmitHelper {
    name: "typescript:export-star",
    import_name: "__exportStar",
    scoped: false,
    priority: Some(Priority { value: 2 }),
    text: r#"var __exportStar = (this && this.__exportStar) || function(m, exports) {
    for (var p in m) if (p !== "default" && !Object.prototype.hasOwnProperty.call(exports, p)) __createBinding(exports, m, p);
};"#,
    text_callback: None,
    dependencies: vec![create_binding_helper()],
});

emit_helper!(rewrite_relative_import_extensions_helper, EmitHelper {
    name: "typescript:rewriteRelativeImportExtensions",
    import_name: "__rewriteRelativeImportExtension",
    scoped: false,
    text: r#"var __rewriteRelativeImportExtension = (this && this.__rewriteRelativeImportExtension) || function (path, preserveJsx) {
    if (typeof path === "string" && /^\.\.?\//.test(path)) {
        return path.replace(/\.(tsx)$|((?:\.d)?)((?:\.[^./]+?)?)\.([cm]?)ts$/i, function (m, tsx, d, ext, cm) {
            return tsx ? preserveJsx ? ".jsx" : ".js" : d && (!ext || !cm) ? m : (d + ext + "." + cm.toLowerCase() + "js");
        });
    }
    return path;
};"#,
    priority: None,
    text_callback: None,
    dependencies: vec![],
});
