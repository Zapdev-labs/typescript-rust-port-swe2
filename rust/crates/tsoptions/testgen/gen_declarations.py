import re, sys

SRC = '/home/dih/TypeScript/tsc/internal/tsoptions/declarations_generated.go'
OUT = '/home/dih/TypeScript/rust/crates/tsoptions/testgen/declarations_options.rs'

src = open(SRC).read()

KIND_MAP = {
    'CommandLineOptionTypeString': 'CommandLineOptionKind::STRING',
    'CommandLineOptionTypeNumber': 'CommandLineOptionKind::NUMBER',
    'CommandLineOptionTypeBoolean': 'CommandLineOptionKind::BOOLEAN',
    'CommandLineOptionTypeObject': 'CommandLineOptionKind::OBJECT',
    'CommandLineOptionTypeList': 'CommandLineOptionKind::LIST',
    'CommandLineOptionTypeListOrElement': 'CommandLineOptionKind::LIST_OR_ELEMENT',
    'CommandLineOptionTypeEnum': 'CommandLineOptionKind::ENUM',
    'CommandLineOptionPathKindFile': 'CommandLineOptionPathKind::File',
    'CommandLineOptionPathKindDirectory': 'CommandLineOptionPathKind::Directory',
    'CommandLineOptionPathKindFileOrDirectory': 'CommandLineOptionPathKind::FileOrDirectory',
    'CommandLineOptionPathKindSourceMapLocation': 'CommandLineOptionPathKind::SourceMapLocation',
    'CommandLineOptionPathKindFileSpec': 'CommandLineOptionPathKind::FileSpec',
    'CommandLineOptionPathKindPathPattern': 'CommandLineOptionPathKind::PathPattern',
    'CommandLineOptionPathKindResolvedPathPattern': 'CommandLineOptionPathKind::ResolvedPathPattern',
    'CommandLineOptionPathKindConfigLocator': 'CommandLineOptionPathKind::ConfigLocator',
}

DEFAULT_VALUE_ENUM_MAP = {
    'core.ScriptTargetLatestStandard': 'DefaultValueDescription::ScriptTarget(ScriptTarget::LATEST_STANDARD)',
    'core.TSUnknown': 'DefaultValueDescription::Tristate(TS_UNKNOWN)',
}

def field_value(field, v):
    v = v.strip().rstrip(',')
    if field == 'Name':
        return 'name', v
    if field == 'ShortName':
        return 'short_name', v
    if field in ('Kind', 'PathKind'):
        return ('kind' if field == 'Kind' else 'path_kind'), KIND_MAP[v]
    if field in ('IsFilePath', 'IsTSConfigOnly', 'IsCommandLineOnly',
                 'ShowInSimplifiedHelpView', 'listPreserveFalsyValues'):
        return {'IsFilePath': 'is_file_path', 'IsTSConfigOnly': 'is_ts_config_only',
                'IsCommandLineOnly': 'is_command_line_only',
                'ShowInSimplifiedHelpView': 'show_in_simplified_help_view',
                'listPreserveFalsyValues': 'list_preserve_falsy_values'}[field], v
    v = v.removeprefix('diagnostics.')
    if field == 'Description':
        return 'description', 'Some(&diagnostics::%s)' % v
    if field == 'Category':
        return 'category', 'Some(&diagnostics::%s)' % v
    if field == 'DefaultValueDescription':
        if v in DEFAULT_VALUE_ENUM_MAP:
            return 'default_value_description', DEFAULT_VALUE_ENUM_MAP[v]
        if v in ('true', 'false'):
            return 'default_value_description', 'DefaultValueDescription::Bool(%s)' % v
        if v.startswith('"'):
            return 'default_value_description', 'DefaultValueDescription::Str(%s)' % v
        return 'default_value_description', 'DefaultValueDescription::Message(&diagnostics::%s)' % v.removeprefix('diagnostics.')
    if field == 'extraValidation':
        return 'extra_validation', 'Some(EXTRA_VALIDATION_LOCALE)'
    if field == 'minValue':
        return 'min_value', v
    raise ValueError('unknown field %r = %r' % (field, v))

def parse_literals(block):
    """Return list of `{...}` literal bodies at top level of block."""
    items = []
    i = 0
    while i < len(block):
        if block[i] == '{':
            depth = 0
            j = i
            while True:
                c = block[j]
                if c == '{':
                    depth += 1
                elif c == '}':
                    depth -= 1
                elif c == '"':
                    j += 1
                    while block[j] != '"':
                        if block[j] == '\\':
                            j += 1
                        j += 1
                if depth == 0:
                    break
                j += 1
            items.append(block[i + 1:j])
            i = j + 1
        else:
            i += 1
    return items

def parse_fields(lit):
    # Only capture `Field: value` pairs at brace depth 0 of the literal body,
    # so fields of nested option literals (e.g. inside ElementOptions) are
    # skipped.
    fields = []
    depth = 0
    for line in lit.split('\n'):
        stripped = line.strip()
        if depth == 0:
            m = re.match(r'(\w+)\s*:\s*(.*)', stripped)
            if m:
                v = m.group(2).rstrip(',').strip()
                fields.append((m.group(1), v))
        depth += stripped.count('{') - stripped.count('}')
        if depth < 0:
            depth = 0
    return fields

def block_body(src, brace_pos):
    depth = 0
    k = brace_pos
    while True:
        c = src[k]
        if c == '{':
            depth += 1
        elif c == '}':
            depth -= 1
        if depth == 0:
            break
        k += 1
    return src[brace_pos + 1:k], k

var_re = re.compile(r'^var (\w+) = (.*)$', re.M)
statics = []
out = []
counter = [0]

def emit_option(lit):
    fields = parse_fields(lit)
    parts = []
    extra = None
    for f, v in fields:
        if f == 'ElementOptions':
            extra = v
            continue
        parts.append(field_value(f, v))
    if extra is not None:
        parts.append(('element_options', 'Some(ElementOptions::%s)' % extra))
    counter[0] += 1
    name = 'OPTION_%d' % counter[0]
    body = 'CommandLineOption {\n'
    for rf, rv in parts:
        body += '        %s: %s,\n' % (rf, rv)
    body += '        ..DEFAULT_COMMAND_LINE_OPTION\n    }'
    statics.append('static %s: CommandLineOption = %s;\n' % (name, body))
    return '&%s' % name

SNAKE = {
    'commonOptionsWithBuild': 'COMMON_OPTIONS_WITH_BUILD',
    'optionsForCompiler': 'OPTIONS_DECLARATIONS',
    'typeAcquisitionDecls': 'TYPE_ACQUISITION_DECLS',
    'commandLineOptionElements': 'COMMAND_LINE_OPTION_ELEMENTS',
    'optionsForBuild': 'OPTIONS_FOR_BUILD',
}

for m in var_re.finditer(src):
    varname, rhs = m.group(1), m.group(2).strip()
    if rhs.startswith('[]*CommandLineOption{'):
        j = src.index('{', m.start())
        block, _ = block_body(src, j)
        lits = parse_literals(block)
        elems = ',\n    '.join(emit_option(l) for l in lits)
        rs_name = SNAKE.get(varname, re.sub(r'(?<!^)([A-Z])', r'_\1', varname).upper())
        out.append('pub static %s: &[&CommandLineOption] = &[\n    %s,\n];\n'
                   % (rs_name, elems))
    elif rhs.startswith('map[string]*CommandLineOption{'):
        j = src.index('{', m.start())
        block, _ = block_body(src, j)
        entries = re.findall(r'"([^"]+)":\s*\{', block)
        lits = parse_literals(block)
        assert len(entries) == len(lits), (varname, len(entries), len(lits))
        rows = ['("%s", %s)' % (n, emit_option(l)) for n, l in zip(entries, lits)]
        rs_name = SNAKE.get(varname, re.sub(r'(?<!^)([A-Z])', r'_\1', varname).upper())
        out.append('static %s: &[(&str, &CommandLineOption)] = &[\n    %s,\n];\n'
                   % (rs_name, ',\n    '.join(rows)))
    else:
        print('unhandled var %s: %s' % (varname, rhs[:80]), file=sys.stderr)

with open(OUT, 'w') as f:
    f.write(''.join(statics) + '\n' + '\n'.join(out))
print('wrote %d option statics, %d blocks' % (counter[0], len(out)), file=sys.stderr)

# ---------- second pass: single options, ordered maps, lookup tables ----------
extra = []

def emit_single_option(varname, lit):
    fields = parse_fields(lit)
    parts = []
    for f, v in fields:
        if f == 'ElementOptions':
            v = v.strip()
            if v == 'CommandLineCompilerOptionsMap':
                tag = 'CompilerOptions'
            elif v == 'commandLineOptionsToMap(typeAcquisitionDecls)':
                tag = 'TypeAcquisition'
            elif v.endswith('{{'):
                tag = 'Extends'
            else:
                tag = 'TsconfigRoot'
            parts.append(('element_options', 'Some(ElementOptions::%s)' % tag))
        else:
            parts.append(field_value(f, v))
    body = 'CommandLineOption {\n'
    for rf, rv in parts:
        body += '    %s: %s,\n' % (rf, rv)
    body += '    ..DEFAULT_COMMAND_LINE_OPTION\n}'
    return 'static %s: CommandLineOption = %s;\n' % (varname, body)

def ordered_map_entries(block):
    return re.findall(r'\{Key:\s*"([^"]+)",\s*Value:\s*([^}]+)\}', block)

ENUM_VALUE_MAP = {
    'core.ModuleResolutionKindNode16': 'Value::Int(ModuleResolutionKind::Node16 as i64)',
    'core.ModuleResolutionKindNodeNext': 'Value::Int(ModuleResolutionKind::NodeNext as i64)',
    'core.ModuleResolutionKindBundler': 'Value::Int(ModuleResolutionKind::Bundler as i64)',
    'core.ModuleResolutionKindClassic': 'Value::Int(ModuleResolutionKind::Classic as i64)',
    'core.ModuleResolutionKindNode10': 'Value::Int(ModuleResolutionKind::Node10 as i64)',
    'core.ModuleKindCommonJS': 'Value::Int(ModuleKind::CommonJS as i64)',
    'core.ModuleKindAMD': 'Value::Int(ModuleKind::AMD as i64)',
    'core.ModuleKindSystem': 'Value::Int(ModuleKind::System as i64)',
    'core.ModuleKindUMD': 'Value::Int(ModuleKind::UMD as i64)',
    'core.ModuleKindES2015': 'Value::Int(ModuleKind::ES2015 as i64)',
    'core.ModuleKindES2020': 'Value::Int(ModuleKind::ES2020 as i64)',
    'core.ModuleKindES2022': 'Value::Int(ModuleKind::ES2022 as i64)',
    'core.ModuleKindESNext': 'Value::Int(ModuleKind::ESNext as i64)',
    'core.ModuleKindNode16': 'Value::Int(ModuleKind::Node16 as i64)',
    'core.ModuleKindNode18': 'Value::Int(ModuleKind::Node18 as i64)',
    'core.ModuleKindNode20': 'Value::Int(ModuleKind::Node20 as i64)',
    'core.ModuleKindNodeNext': 'Value::Int(ModuleKind::NodeNext as i64)',
    'core.ModuleKindPreserve': 'Value::Int(ModuleKind::Preserve as i64)',
    'core.ScriptTargetES5': 'Value::Int(ScriptTarget::ES5 as i64)',
    'core.ScriptTargetES2015': 'Value::Int(ScriptTarget::ES2015 as i64)',
    'core.ScriptTargetES2016': 'Value::Int(ScriptTarget::ES2016 as i64)',
    'core.ScriptTargetES2017': 'Value::Int(ScriptTarget::ES2017 as i64)',
    'core.ScriptTargetES2018': 'Value::Int(ScriptTarget::ES2018 as i64)',
    'core.ScriptTargetES2019': 'Value::Int(ScriptTarget::ES2019 as i64)',
    'core.ScriptTargetES2020': 'Value::Int(ScriptTarget::ES2020 as i64)',
    'core.ScriptTargetES2021': 'Value::Int(ScriptTarget::ES2021 as i64)',
    'core.ScriptTargetES2022': 'Value::Int(ScriptTarget::ES2022 as i64)',
    'core.ScriptTargetES2023': 'Value::Int(ScriptTarget::ES2023 as i64)',
    'core.ScriptTargetES2024': 'Value::Int(ScriptTarget::ES2024 as i64)',
    'core.ScriptTargetES2025': 'Value::Int(ScriptTarget::ES2025 as i64)',
    'core.ScriptTargetES2026': 'Value::Int(ScriptTarget::ES2026 as i64)',
    'core.ScriptTargetESNext': 'Value::Int(ScriptTarget::ESNext as i64)',
    'core.ModuleDetectionKindAuto': 'Value::Int(ModuleDetectionKind::Auto as i64)',
    'core.ModuleDetectionKindLegacy': 'Value::Int(ModuleDetectionKind::Legacy as i64)',
    'core.ModuleDetectionKindForce': 'Value::Int(ModuleDetectionKind::Force as i64)',
    'core.JsxEmitPreserve': 'Value::Int(JsxEmit::Preserve as i64)',
    'core.JsxEmitReactNative': 'Value::Int(JsxEmit::ReactNative as i64)',
    'core.JsxEmitReactJSX': 'Value::Int(JsxEmit::ReactJSX as i64)',
    'core.JsxEmitReactJSXDev': 'Value::Int(JsxEmit::ReactJSXDev as i64)',
    'core.JsxEmitReact': 'Value::Int(JsxEmit::React as i64)',
    'core.NewLineKindCRLF': 'Value::Int(NewLineKind::CRLF as i64)',
    'core.NewLineKindLF': 'Value::Int(NewLineKind::LF as i64)',
}

def emit_ordered_map(varname, block):
    entries = ordered_map_entries(block)
    rows = []
    for k, v in entries:
        v = v.strip().rstrip(',')
        if v.startswith('"'):
            rv = 'Value::Str(%s.into())' % v
        else:
            rv = ENUM_VALUE_MAP[v]
        rows.append('        map.set(%s.to_string(), %s);' % ('%r' % k, rv))
    rs = re.sub(r'(?<!^)([A-Z])', r'_\1', varname).upper()
    body = ('pub static %s: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {\n'
            '    let mut map = OrderedMap::with_size_hint(%d);\n'
            '%s\n'
            '    map\n'
            '});\n' % (rs, len(entries), '\n'.join(rows)))
    return body.replace('%r' % '', '')  # noop

def emit_ordered_map2(varname, block):
    entries = ordered_map_entries(block)
    rows = []
    for k, v in entries:
        v = v.strip().rstrip(',')
        if v.startswith('"'):
            rv = 'Value::Str(%s.into())' % v
        else:
            rv = ENUM_VALUE_MAP[v]
        rows.append('    map.set("%s".to_string(), %s);' % (k, rv))
    rs = re.sub(r'(?<!^)([A-Z])', r'_\1', varname).upper()
    return ('pub static %s: LazyLock<OrderedMap<String, Value>> = LazyLock::new(|| {\n'
            '    let mut map = OrderedMap::with_size_hint(%d);\n'
            '%s\n'
            '    map\n'
            '});\n' % (rs, len(entries), '\n'.join(rows)))

single_re = re.compile(r'^var (\w+) = &?CommandLineOption\{', re.M)
pos_after_first = None
for m in single_re.finditer(src):
    varname = m.group(1)
    j = src.index('{', m.start())
    block, _ = block_body(src, j)
    lits = parse_literals(block)
    # for tsconfigRootOptionsMap, the literal contains nested { } items we don't need;
    # the member list is hand-written in `element_options`.
    extra.append('// var %s\n' % varname +
                 emit_single_option(re.sub(r'(?<!^)([A-Z])', r'_\1', varname).upper(), block))

omap_re = re.compile(r'^var (\w+) = collections\.NewOrderedMapFromList\(', re.M)
for m in omap_re.finditer(src):
    varname = m.group(1)
    j = src.index('{', m.start())
    # NewOrderedMapFromList([]MapEntry{...}) — find closing of the [] literal
    # first '{' opens the literal
    block, _ = block_body(src, j)
    extra.append(emit_ordered_map2(varname, block))

with open(OUT.replace('.rs', '_extra.rs'), 'w') as f:
    f.write('\n'.join(extra))
print('wrote extra', file=sys.stderr)
