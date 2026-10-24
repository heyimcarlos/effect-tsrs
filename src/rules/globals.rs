use super::RuleContext;
use crate::Rule;
use std::collections::{BTreeMap, HashMap, HashSet};
use std::path::{Component, Path, PathBuf};
use tsrs_ast::{self as ast, Kind, Node, SourceFile, Symbol, SymbolFlags};
use tsrs_core::{P, TextRange};

pub(crate) fn run(ctx: &mut RuleContext<'_>) {
    if ![
        Rule::AbortControllerInEffect,
        Rule::CryptoRandomUUID,
        Rule::CryptoRandomUUIDInEffect,
        Rule::GlobalFetch,
        Rule::GlobalFetchInEffect,
        Rule::ProcessEnv,
        Rule::ProcessEnvInEffect,
        Rule::GlobalConsole,
        Rule::GlobalConsoleInEffect,
        Rule::GlobalDate,
        Rule::GlobalDateInEffect,
        Rule::GlobalRandom,
        Rule::GlobalRandomInEffect,
        Rule::PreferEffectArray,
        Rule::PreferEffectRecord,
        Rule::PreferEffectString,
        Rule::GlobalTimers,
        Rule::GlobalTimersInEffect,
        Rule::PreferSchemaOverJson,
        Rule::NodeBuiltinImport,
        Rule::NewPromise,
        Rule::PreferNamespaceImport,
        Rule::PreferBarrelImport,
        Rule::DuplicatePackage,
        Rule::ObsoleteMatchImport,
        Rule::ObsoleteSchemaImport,
        Rule::OutdatedApi,
    ]
    .into_iter()
    .any(|rule| ctx.enabled(rule))
    {
        return;
    }
    let mut nodes = Vec::new();
    super::walk(ctx.file.as_node(), &mut |n| nodes.push(n));
    for node in nodes.iter().copied() {
        globals(ctx, node);
    }
    if [
        Rule::PreferEffectArray,
        Rule::PreferEffectRecord,
        Rule::PreferEffectString,
    ]
    .iter()
    .any(|&r| ctx.enabled(r))
    {
        let mut native = NativeRegistry::default();
        native.build(ctx);
        native_walk(ctx, ctx.file.as_node(), &native);
    }
    imports(ctx);
    if ctx.enabled(Rule::DuplicatePackage) {
        duplicate_packages(ctx);
    }
    if ctx.effect_version == 4 && ctx.enabled(Rule::OutdatedApi) {
        let before = ctx.diagnostics.len();
        for node in nodes {
            if node.kind() != Kind::PropertyAccessExpression {
                continue;
            }
            let access = node.as_property_access_expression();
            let name = access.name();
            let Some(hint) = migration(name.text()) else {
                continue;
            };
            let ty = ctx.ty(access.expression);
            if ctx.checker.get_property_of_type(ty, name.text()).is_none()
                && ctx.is_module(access.expression, "Effect")
            {
                ctx.emit(
                    Rule::OutdatedApi,
                    name,
                    377052,
                    &[name.text().into(), hint.into()],
                );
            }
        }
        if ctx.diagnostics.len() > before {
            ctx.emit_range(
                Rule::OutdatedApi,
                ctx.file,
                TextRange::new(0, 0),
                377053,
                &[],
            );
        }
    }
}

fn pair(
    ctx: &RuleContext<'_>,
    inside: bool,
    outer: Rule,
    inner: Rule,
    outer_code: i32,
    inner_code: i32,
) -> Option<(Rule, i32)> {
    let r = if inside { inner } else { outer };
    ctx.enabled(r)
        .then_some((r, if inside { inner_code } else { outer_code }))
}
fn globals(ctx: &mut RuleContext<'_>, node: P<Node>) {
    if node.kind() == Kind::NewExpression {
        let expr = node.as_new_expression().expression;
        if ctx.enabled(Rule::NewPromise) && ctx.is_global(expr, "Promise") {
            ctx.emit(Rule::NewPromise, node, 377080, &[]);
        }
        if ctx.enabled(Rule::AbortControllerInEffect)
            && ctx.effect_context(node) & 1 != 0
            && ctx.is_global(expr, "AbortController")
        {
            ctx.emit(Rule::AbortControllerInEffect, node, 377111, &[]);
        }
        if ctx.enabled(Rule::GlobalDate) || ctx.enabled(Rule::GlobalDateInEffect) {
            let inside = ctx.effect_context(node) & 3 != 0;
            if let Some((r, c)) = pair(
                ctx,
                inside,
                Rule::GlobalDate,
                Rule::GlobalDateInEffect,
                377068,
                377069,
            ) && ctx.is_global(expr, "Date")
            {
                ctx.emit(r, node, c, &[]);
            }
        }
    }
    if matches!(
        node.kind(),
        Kind::PropertyAccessExpression | Kind::ElementAccessExpression
    ) && (ctx.enabled(Rule::ProcessEnv) || ctx.enabled(Rule::ProcessEnvInEffect))
        && let Some(access) = node.expression()
        && access.kind() == Kind::PropertyAccessExpression
        && access.as_property_access_expression().name().text() == "env"
    {
        let inside = ctx.effect_context(node) & 3 != 0;
        if let Some((r, c)) = pair(
            ctx,
            inside,
            Rule::ProcessEnv,
            Rule::ProcessEnvInEffect,
            377076,
            377077,
        ) && ctx.is_global(access.as_property_access_expression().expression, "process")
        {
            ctx.emit(r, node, c, &[]);
        }
    }
    if node.kind() != Kind::CallExpression {
        return;
    }
    let call = node.as_call_expression();
    let callee = call.expression;
    let any_global = [
        Rule::GlobalFetch,
        Rule::GlobalFetchInEffect,
        Rule::GlobalConsole,
        Rule::GlobalConsoleInEffect,
        Rule::GlobalDate,
        Rule::GlobalDateInEffect,
        Rule::GlobalRandom,
        Rule::GlobalRandomInEffect,
        Rule::GlobalTimers,
        Rule::GlobalTimersInEffect,
        Rule::CryptoRandomUUID,
        Rule::CryptoRandomUUIDInEffect,
    ]
    .iter()
    .any(|&r| ctx.enabled(r));
    if any_global {
        let inside = ctx.effect_context(node) & 3 != 0;
        if let Some((r, c)) = pair(
            ctx,
            inside,
            Rule::GlobalFetch,
            Rule::GlobalFetchInEffect,
            377061,
            377063,
        ) && ctx.is_global(callee, "fetch")
        {
            ctx.emit(
                r,
                callee,
                c,
                &[if ctx.effect_version == 3 {
                    "@effect/platform"
                } else {
                    "effect/http"
                }
                .into()],
            );
        }
        for (outer, inner, global, member, co, ci) in [
            (
                Rule::GlobalDate,
                Rule::GlobalDateInEffect,
                "Date",
                "now",
                377066,
                377067,
            ),
            (
                Rule::GlobalRandom,
                Rule::GlobalRandomInEffect,
                "Math",
                "random",
                377070,
                377071,
            ),
            (
                Rule::CryptoRandomUUID,
                Rule::CryptoRandomUUIDInEffect,
                "crypto",
                "randomUUID",
                377078,
                377079,
            ),
        ] {
            if let Some((r, c)) = pair(ctx, inside, outer, inner, co, ci)
                && ctx.is_global_member(callee, global, member)
            {
                ctx.emit(r, node, c, &[]);
            }
        }
        if let Some((r, c)) = pair(
            ctx,
            inside,
            Rule::GlobalConsole,
            Rule::GlobalConsoleInEffect,
            377064,
            377065,
        ) {
            for (method, alt) in [
                ("log", "Effect.log or Logger"),
                ("warn", "Effect.logWarning or Logger"),
                ("error", "Effect.logError or Logger"),
                ("info", "Effect.logInfo or Logger"),
                ("debug", "Effect.logDebug or Logger"),
                ("trace", "Effect.logTrace or Logger"),
            ] {
                if ctx.is_global_member(callee, "console", method) {
                    ctx.emit(r, node, c, &[alt.into(), method.into()]);
                    break;
                }
            }
        }
        if let Some((r, c)) = pair(
            ctx,
            inside,
            Rule::GlobalTimers,
            Rule::GlobalTimersInEffect,
            377072,
            377073,
        ) {
            for (name, alt) in [
                ("setTimeout", "Effect.sleep or Schedule"),
                ("setInterval", "Schedule or Effect.repeat"),
            ] {
                if ctx.is_global(callee, name) {
                    ctx.emit(r, node, c, &[alt.into(), name.into()]);
                    break;
                }
            }
        }
    }
    if ctx.enabled(Rule::PreferSchemaOverJson) {
        let mut target = None;
        if ctx.is_api(callee, "Effect", "try")
            && let Some(arg) = call.arguments.nodes().first().copied()
        {
            if ctx.effect_version == 3
                && let Some(lazy) = ctx.parse_lazy_expression(arg, 0)
            {
                target = parse_json(lazy.expression);
            }
            if target.is_none() && arg.kind() == Kind::ObjectLiteralExpression {
                for &prop in arg.as_object_literal_expression().properties.nodes().iter() {
                    if prop.kind() == Kind::PropertyAssignment {
                        let p = prop.as_property_assignment();
                        if p.name().kind() == Kind::Identifier && p.name().text() == "try" {
                            if let Some(lazy) = ctx.parse_lazy_expression(p.initializer(), 0) {
                                target = parse_json(lazy.expression);
                            }
                            break;
                        }
                    }
                }
            }
        }
        if target.is_none() && parse_json(node).is_some() && ctx.effect_context(node) & 3 != 0 {
            target = Some(node);
        }
        if let Some(target) = target {
            let text = if ctx.effect_version == 4 {
                "Use `Schema.UnknownFromJsonString` for unknown shapes, `Schema.fromJsonString(schema)` for known ones, or `Schema.toCodecJson(schema)` when working with JSON values instead of strings."
            } else {
                "Use `Schema.parseJson(Schema.Unknown)` for unknown shapes or `Schema.parseJson(schema)` for known ones."
            };
            ctx.emit(Rule::PreferSchemaOverJson, target, 377026, &[text.into()]);
        }
    }
}
fn parse_json(node: P<Node>) -> Option<P<Node>> {
    if node.kind() != Kind::CallExpression {
        return None;
    }
    let callee = node.as_call_expression().expression;
    if callee.kind() != Kind::PropertyAccessExpression {
        return None;
    }
    let p = callee.as_property_access_expression();
    (p.expression.kind() == Kind::Identifier
        && p.expression.text() == "JSON"
        && matches!(p.name().text(), "parse" | "stringify"))
    .then_some(node)
}

#[derive(Default)]
struct NativeRegistry {
    entries: HashMap<(u8, String), Vec<P<Symbol>>>,
}
impl NativeRegistry {
    fn build(&mut self, ctx: &mut RuleContext<'_>) {
        for (name, meaning, id) in [
            ("Array", SymbolFlags::Type, 1),
            ("ReadonlyArray", SymbolFlags::Type, 1),
            ("Array", SymbolFlags::Value, 2),
            ("Object", SymbolFlags::Type, 3),
            ("Object", SymbolFlags::Value, 4),
            ("String", SymbolFlags::Type, 5),
        ] {
            let Some(s) = ctx
                .checker
                .resolve_name_exported(name, None, meaning, false)
            else {
                continue;
            };
            let ty = if meaning == SymbolFlags::Type {
                ctx.checker.get_declared_type_of_symbol(s)
            } else {
                ctx.checker.get_type_of_symbol(s)
            };
            let Some(owner) = ty.symbol() else {
                continue;
            };
            // Computing properties resolves lazy members before accessing the owning table.
            let _ = ctx.checker.get_properties_of_type(ty);
            let Some(members) = owner.members() else {
                continue;
            };
            for symbol in members.values() {
                if !symbol.flags().intersects(SymbolFlags::Value)
                    || symbol.declarations().is_empty()
                {
                    continue;
                }
                if !symbol.declarations().iter().all(|&d| {
                    ast::get_source_file_of_node(d)
                        .is_some_and(|f| ctx.program.is_source_file_default_library(f.path()))
                }) {
                    continue;
                }
                self.entries
                    .entry((id, symbol.name().into()))
                    .or_default()
                    .extend(ctx.checker.get_root_symbols(symbol));
            }
        }
    }
    fn matches(&self, ctx: &mut RuleContext<'_>, node: P<Node>, id: u8, name: &str) -> bool {
        let Some((receiver, key)) = member(node) else {
            return false;
        };
        let mut symbol = ctx.symbol(if node.kind() == Kind::ElementAccessExpression {
            key
        } else {
            node
        });
        if symbol.is_none() && node.kind() == Kind::ElementAccessExpression {
            let t = ctx.ty(receiver);
            let t = ctx.checker.get_non_nullable_type(t);
            symbol = ctx.checker.get_property_of_type(t, key.text());
        }
        let Some(symbol) = symbol else {
            return false;
        };
        let roots = ctx.checker.get_root_symbols(symbol);
        !roots.is_empty()
            && roots.into_iter().all(|root| {
                root.name() == name
                    && self
                        .entries
                        .get(&(id, name.into()))
                        .is_some_and(|canonical| {
                            canonical.iter().any(|&c| ctx.same_symbol(root, c))
                        })
            })
    }
}
fn member(node: P<Node>) -> Option<(P<Node>, P<Node>)> {
    match node.kind() {
        Kind::PropertyAccessExpression => {
            let p = node.as_property_access_expression();
            Some((p.expression, p.name()))
        }
        Kind::ElementAccessExpression => {
            let p = node.as_element_access_expression();
            let k = p.argument_expression;
            ast::is_string_literal_like(k).then_some((p.expression, k))
        }
        _ => None,
    }
}
fn native_walk(ctx: &mut RuleContext<'_>, node: P<Node>, native: &NativeRegistry) {
    if ast::is_type_node(node) {
        return;
    }
    if let Some((receiver, name)) = member(node) {
        let mut parent = node.parent();
        while parent.is_some_and(|p| p.kind() == Kind::ParenthesizedExpression) {
            parent = parent.unwrap().parent();
        }
        if ast::skip_parentheses(receiver).kind() != Kind::SuperKeyword {
            let writable = ast::is_assignment_target(node)
                || ast::is_declaration_name(node)
                || parent.is_some_and(|p| p.kind() == Kind::DeleteExpression);
            for &(r, code, preferences) in &[
                (Rule::PreferEffectArray, 377140, ARRAY),
                (Rule::PreferEffectRecord, 377143, RECORD),
                (Rule::PreferEffectString, 377150, STRING),
            ] {
                if !ctx.enabled(r) {
                    continue;
                }
                if r == Rule::PreferEffectString {
                    if !parent.is_some_and(|p| {
                        p.kind() == Kind::CallExpression
                            && ast::skip_parentheses(p.as_call_expression().expression) == node
                    }) {
                        continue;
                    }
                } else if writable {
                    continue;
                }
                if !preferences.iter().any(|(_, n, _, _)| name.text() == *n) {
                    continue;
                }
                for &(id, n, api, caveat) in preferences {
                    if native.matches(ctx, node, id, n) {
                        let label = if r == Rule::PreferEffectRecord {
                            format!(
                                "{}.{n}",
                                if id == 3 {
                                    "Object.prototype"
                                } else {
                                    "Object"
                                }
                            )
                        } else {
                            n.into()
                        };
                        ctx.emit(r, name, code, &[api.into(), label, caveat.into()]);
                        break;
                    }
                }
            }
        }
    }
    node.for_each_child(&mut |n| {
        native_walk(ctx, n, native);
        false
    });
}

fn package_name(spec: &str) -> &str {
    if spec.is_empty() || spec.starts_with('.') || spec.starts_with('/') {
        return "";
    }
    if spec.starts_with('@') {
        if let Some(first) = spec.find('/')
            && let Some(next) = spec[first + 1..].find('/')
        {
            return &spec[..first + 1 + next];
        }
        return spec;
    }
    spec.split('/').next().unwrap_or("")
}
fn configured(ctx: &RuleContext<'_>, option: &str, spec: &str) -> bool {
    let package = package_name(spec);
    !package.is_empty()
        && ctx
            .options
            .get(option)
            .and_then(|v| v.as_array())
            .is_some_and(|a| {
                a.iter()
                    .any(|v| v.as_str().is_some_and(|s| s.eq_ignore_ascii_case(package)))
            })
}
fn imports(ctx: &mut RuleContext<'_>) {
    let statements = ctx.file.statements.nodes().to_vec();
    for stmt in statements {
        let mut specs = Vec::new();
        match stmt.kind() {
            Kind::ImportDeclaration => {
                let d = stmt.as_import_declaration();
                specs.push(d.module_specifier);
            }
            Kind::ExportDeclaration => {
                if let Some(s) = stmt.as_export_declaration().module_specifier {
                    specs.push(s);
                }
            }
            Kind::VariableStatement => {
                let list = stmt
                    .as_variable_statement()
                    .declaration_list
                    .as_variable_declaration_list();
                for &d in list.declarations.nodes().iter() {
                    if let Some(init) = d.as_variable_declaration().initializer()
                        && init.kind() == Kind::CallExpression
                    {
                        let c = init.as_call_expression();
                        if c.expression.kind() == Kind::Identifier
                            && c.expression.text() == "require"
                            && c.arguments.nodes().len() == 1
                        {
                            specs.push(c.arguments.nodes()[0]);
                        }
                    }
                }
            }
            _ => {}
        }
        for s in specs {
            if s.kind() != Kind::StringLiteral {
                continue;
            }
            let spec = s.text();
            if stmt.kind() != Kind::ExportDeclaration
                && ctx.enabled(Rule::NodeBuiltinImport)
                && let Some((api, pkg, module)) = builtin(spec, ctx.effect_version)
            {
                ctx.emit(
                    Rule::NodeBuiltinImport,
                    s,
                    377057,
                    &[api.into(), pkg.into(), module.into()],
                );
            }
            for (r, prefix, code) in [
                (Rule::ObsoleteMatchImport, "@effect/match", 377129),
                (Rule::ObsoleteSchemaImport, "@effect/schema", 377128),
            ] {
                if ctx.effect_version == 4
                    && ctx.enabled(r)
                    && (spec == prefix || spec.starts_with(&format!("{prefix}/")))
                {
                    ctx.emit(r, s, code, &[spec.into()]);
                }
            }
        }
        if stmt.kind() != Kind::ImportDeclaration {
            continue;
        }
        let d = stmt.as_import_declaration();
        let spec = d.module_specifier;
        let Some(clause) = d.import_clause else {
            continue;
        };
        if spec.kind() != Kind::StringLiteral {
            continue;
        }
        let Some(bindings) = clause.as_import_clause().named_bindings else {
            continue;
        };
        if ctx.enabled(Rule::PreferNamespaceImport)
            && configured(ctx, "namespaceImportPackages", spec.text())
            && bindings.kind() == Kind::NamedImports
        {
            namespace_import(ctx, spec, clause, bindings);
        }
        if ctx.enabled(Rule::PreferBarrelImport)
            && !configured(ctx, "namespaceImportPackages", spec.text())
            && configured(ctx, "barrelImportPackages", spec.text())
            && let Some(resolved) = ctx
                .program
                .get_resolved_module_from_module_specifier(ctx.file, spec)
            && let Some((barrel, export)) =
                find_barrel(ctx, spec.text(), resolved.resolved_file_name)
        {
            let binding = if bindings.kind() == Kind::NamespaceImport
                && bindings.name().unwrap().text() != export
            {
                format!("{export} as {}", bindings.name().unwrap().text())
            } else {
                export
            };
            let keyword = if clause.is_type_only() {
                "import type"
            } else {
                "import"
            };
            let import = format!("{keyword} {{ {binding} }} from \"{barrel}\"");
            ctx.emit(
                Rule::PreferBarrelImport,
                spec,
                377148,
                &[spec.text().into(), barrel, import],
            );
        }
    }
}
fn builtin(spec: &str, v: u8) -> Option<(&'static str, &'static str, &'static str)> {
    let spec = spec.strip_prefix("node:").unwrap_or(spec);
    let old = if v == 3 { "@effect/platform" } else { "effect" };
    Some(match spec {
        "fs" | "fs/promises" => ("FileSystem", old, "fs"),
        "path" | "path/posix" | "path/win32" => ("Path", old, "path"),
        "child_process" => {
            if v == 3 {
                ("CommandExecutor", old, "child_process")
            } else {
                ("ChildProcess", "effect/process", "child_process")
            }
        }
        "http" => (
            "HttpClient",
            if v == 3 { old } else { "effect/http" },
            "http",
        ),
        "https" => (
            "HttpClient",
            if v == 3 { old } else { "effect/http" },
            "https",
        ),
        "console" => ("Console", "effect", "console"),
        "timers" | "timers/promises" => ("Effect", "effect", "timers"),
        "stream" | "stream/promises" | "stream/web" => ("Stream", "effect", "stream"),
        "crypto" if v == 4 => ("Crypto", "effect", "crypto"),
        _ => return None,
    })
}
fn symbol_file(s: P<Symbol>) -> Option<P<SourceFile>> {
    s.declarations()
        .iter()
        .find(|n| n.kind() == Kind::SourceFile)
        .map(|n| n.as_source_file_p())
        .or_else(|| s.value_declaration().and_then(ast::get_source_file_of_node))
}
fn namespace_import(ctx: &mut RuleContext<'_>, spec: P<Node>, clause: P<Node>, bindings: P<Node>) {
    let Some(mut module) = ctx.symbol(spec) else {
        return;
    };
    if module.flags().intersects(SymbolFlags::Alias) {
        module = ctx.checker.get_aliased_symbol(module);
    }
    let file = symbol_file(module);
    let follow = ctx
        .options
        .get("topLevelNamedReexports")
        .and_then(|v| v.as_str())
        .is_some_and(|s| s.eq_ignore_ascii_case("follow"));
    for &element in bindings.as_named_imports().elements.nodes().iter() {
        let imp = element.as_import_specifier();
        let imported = imp.property_name().unwrap_or(imp.name());
        if imported.kind() != Kind::Identifier {
            continue;
        }
        let Some(export) = ctx
            .checker
            .try_get_member_in_module_exports(imported.text(), module)
        else {
            continue;
        };
        let (target, reexport) =
            namespace_target(ctx, export, file, spec.text(), imp.name().text(), 0);
        if reexport && !follow {
            continue;
        }
        let mut args = vec![imported.text().into(), spec.text().into()];
        let code = if let Some((name, target)) = target {
            let keyword = if clause.is_type_only() || element.is_type_only() {
                "import type"
            } else {
                "import"
            };
            args.push(format!("{keyword} * as {name} from \"{target}\""));
            377146
        } else {
            377147
        };
        ctx.emit(Rule::PreferNamespaceImport, element, code, &args);
    }
}
fn namespace_target(
    ctx: &mut RuleContext<'_>,
    symbol: P<Symbol>,
    file: Option<P<SourceFile>>,
    spec: &str,
    local: &str,
    depth: usize,
) -> (Option<(String, String)>, bool) {
    if depth > 8 {
        return (None, true);
    }
    let declarations = symbol.declarations();
    if !symbol.flags().intersects(SymbolFlags::Alias) {
        if declarations
            .iter()
            .any(|&d| ast::get_source_file_of_node(d) == file)
        {
            return (
                Some((spec.rsplit('/').next().unwrap_or(spec).into(), spec.into())),
                false,
            );
        }
        return (None, true);
    }
    let Some(&d) = declarations.first() else {
        return (None, true);
    };
    if ast::get_source_file_of_node(d) != file {
        return (None, true);
    }
    if d.kind() == Kind::NamespaceExport {
        let target = d.parent().and_then(|p| reexport_target(p, spec));
        return (target.map(|s| (local.into(), s)), false);
    }
    if d.kind() == Kind::ExportSpecifier
        && let Some(export) = d.parent().and_then(|p| p.parent())
        && export.kind() == Kind::ExportDeclaration
        && export.as_export_declaration().module_specifier.is_some()
    {
        let target = reexport_target(export, spec);
        return (
            target.map(|s| (s.rsplit('/').next().unwrap_or(&s).into(), s)),
            true,
        );
    }
    if let Some(aliased) = ctx.checker.get_immediate_aliased_symbol(symbol)
        && !aliased.flags().intersects(SymbolFlags::Alias)
    {
        return namespace_target(ctx, aliased, file, spec, local, depth + 1);
    }
    (None, true)
}
const EXTENSIONS: &[&str] = &[
    ".d.ts", ".ts", ".tsx", ".d.mts", ".mts", ".d.cts", ".cts", ".js", ".mjs", ".cjs", ".jsx",
];
fn stem(s: &str) -> &str {
    for ext in EXTENSIONS {
        if let Some(s) = s.strip_suffix(ext) {
            return s;
        }
    }
    s
}
fn reexport_target(export: P<Node>, spec: &str) -> Option<String> {
    let file = ast::get_source_file_of_node(export)?;
    if stem(Path::new(file.file_name()).file_name()?.to_str()?) != "index" {
        return None;
    }
    let module = export.as_export_declaration().module_specifier?;
    if module.kind() != Kind::StringLiteral {
        return None;
    }
    let name = stem(module.text().strip_prefix("./")?);
    if name.is_empty() || name == "index" || name.contains(['/', '.']) {
        return None;
    }
    Some(format!("{spec}/{name}"))
}
fn normalize(path: PathBuf) -> PathBuf {
    let mut out = PathBuf::new();
    for component in path.components() {
        match component {
            Component::ParentDir => {
                out.pop();
            }
            Component::CurDir => {}
            _ => out.push(component.as_os_str()),
        }
    }
    out
}
fn find_barrel(
    ctx: &RuleContext<'_>,
    specifier: &str,
    file_name: &str,
) -> Option<(String, String)> {
    let package = package_name(specifier);
    if package.is_empty() || stem(Path::new(file_name).file_name()?.to_str()?) == "index" {
        return None;
    }
    let target = normalize(PathBuf::from(stem(file_name)));
    let mut dir = Path::new(file_name).parent()?;
    let mut spec = specifier;
    while spec.len() > package.len() {
        spec = spec.rsplit_once('/')?.0;
        for ext in EXTENSIONS {
            let path = dir.join(format!("index{ext}"));
            let path = path.to_str()?;
            let file = if let Some(f) = ctx.program.get_source_file(path) {
                Some(f)
            } else {
                ctx.program.host().fs().read_file(path).map(|text| {
                    tsrs_parser::parse_source_file(
                        ast::SourceFileParseOptions {
                            file_name: path.into(),
                            ..Default::default()
                        },
                        &text,
                        tsrs_core::ScriptKind::TS,
                    )
                })
            };
            let Some(file) = file else {
                continue;
            };
            for &statement in file.statements.nodes().iter() {
                if statement.kind() != Kind::ExportDeclaration {
                    continue;
                }
                let d = statement.as_export_declaration();
                let (Some(clause), Some(module)) = (d.export_clause, d.module_specifier) else {
                    continue;
                };
                if clause.kind() != Kind::NamespaceExport || module.kind() != Kind::StringLiteral {
                    continue;
                }
                let relative = module.text();
                if !(relative.starts_with("./") || relative.starts_with("../")) {
                    continue;
                }
                if normalize(dir.join(stem(relative))) == target {
                    let name = clause.name()?;
                    if name.kind() == Kind::Identifier {
                        return Some((spec.into(), name.text().into()));
                    }
                }
            }
            break;
        }
        dir = dir.parent()?;
    }
    None
}
fn duplicate_packages(ctx: &mut RuleContext<'_>) {
    let mut seen = HashSet::new();
    let mut packages: BTreeMap<String, Vec<(Option<String>, String)>> = BTreeMap::new();
    for &file in ctx.program.get_source_files() {
        let Some(json) = ctx.package_json(file) else {
            continue;
        };
        let Some(name) = json.get("name").and_then(|v| v.as_str()) else {
            continue;
        };
        let version = json
            .get("version")
            .and_then(|v| v.as_str())
            .map(str::to_string);
        if !seen.insert((name.to_string(), version.clone())) {
            continue;
        }
        if name != "effect"
            && !json
                .get("peerDependencies")
                .and_then(|v| v.as_object())
                .is_some_and(|o| o.contains_key("effect"))
        {
            continue;
        }
        let dir = Path::new(file.file_name())
            .parent()
            .and_then(|p| p.to_str())
            .map(|p| {
                ctx.program
                    .get_nearest_ancestor_directory_with_package_json(p)
            })
            .unwrap_or_default();
        packages
            .entry(name.into())
            .or_default()
            .push((version, dir));
    }
    let allowed: Vec<String> = ctx
        .options
        .get("allowedDuplicatedPackages")
        .and_then(|v| v.as_array())
        .map(|a| {
            a.iter()
                .filter_map(|v| v.as_str().map(str::to_string))
                .collect()
        })
        .unwrap_or_default();
    let target = ctx
        .file
        .statements
        .nodes()
        .first()
        .copied()
        .unwrap_or(ctx.file.as_node());
    for (name, entries) in packages {
        if entries.len() < 2 || allowed.contains(&name) {
            continue;
        }
        let details = entries
            .iter()
            .map(|(v, p)| {
                format!(
                    "{} @ {p}",
                    v.as_deref()
                        .filter(|v| !v.is_empty())
                        .unwrap_or("(unknown)")
                )
            })
            .collect::<Vec<_>>()
            .join(", ");
        let mut config = allowed.clone();
        config.push(name.clone());
        ctx.emit(
            Rule::DuplicatePackage,
            target,
            377051,
            &[name, details, serde_json::to_string(&config).unwrap()],
        );
    }
}

const ARRAY: &[(u8, &str, &str, &str)] = &[
    (
        1,
        "map",
        "map",
        "The callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "filter",
        "filter",
        "The callback type accepts (value, index), with no array parameter or thisArg; sparse-array holes are visited.",
    ),
    (
        1,
        "every",
        "every",
        "The callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "some",
        "some",
        "The callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "forEach",
        "forEach",
        "The callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "flatMap",
        "flatMap",
        "Callbacks must return arrays; the callback type accepts (value, index), with no array parameter or thisArg, and sparse-array holes are visited.",
    ),
    (
        1,
        "reduce",
        "reduce",
        "An initial value is required before the callback; the callback type omits the array parameter.",
    ),
    (
        1,
        "reduceRight",
        "reduceRight",
        "An initial value is required before the callback; the callback type omits the array parameter.",
    ),
    (
        1,
        "find",
        "findFirst",
        "Returns Option, with None replacing undefined; the callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "findLast",
        "findLast",
        "Returns Option, with None replacing undefined; the callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "findIndex",
        "findFirstIndex",
        "Returns Option<number>, with None replacing -1; the callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "findLastIndex",
        "findLastIndex",
        "Returns Option<number>, with None replacing -1; the callback type accepts (value, index), with no array parameter or thisArg.",
    ),
    (
        1,
        "join",
        "join",
        "Accepts strings and requires an explicit separator.",
    ),
    (
        1,
        "toReversed",
        "reverse",
        "Returns a new array, like native toReversed.",
    ),
    (
        1,
        "toSorted",
        "sort",
        "Requires an explicit Order instead of native default ordering or a numeric comparator.",
    ),
    (
        2,
        "isArray",
        "isArray",
        "Narrows elements to unknown rather than any.",
    ),
];

const RECORD: &[(u8, &str, &str, &str)] = &[
    (
        4,
        "keys",
        "keys",
        "Requires a record rather than arrays or primitives; types keys as the inferred key union, which does not guarantee exact runtime keys.",
    ),
    (
        4,
        "values",
        "values",
        "Requires a record rather than arrays or primitives; snapshots keys before reads, so getter or proxy mutations can change the result.",
    ),
    (
        4,
        "entries",
        "toEntries",
        "Requires a record rather than arrays or primitives; types entries with inferred keys and snapshots keys before reads, so getter or proxy mutations can change the result.",
    ),
    (
        4,
        "fromEntries",
        "fromEntries",
        "Requires typed string or symbol key tuples; native numeric keys and loose entry arrays need adaptation.",
    ),
    (
        4,
        "hasOwn",
        "has",
        "Requires a record rather than arrays or primitives and a string or symbol key of that record's key type; arbitrary strings may need narrowing.",
    ),
    (
        3,
        "hasOwnProperty",
        "has",
        "Pass the receiver explicitly; requires a record rather than arrays or primitives and a string or symbol key of that record's key type. Avoids instance binding and overrides.",
    ),
];

const STRING: &[(u8, &str, &str, &str)] = &[
    (
        5,
        "at",
        "at",
        "Returns Option, with None replacing undefined.",
    ),
    (
        5,
        "charAt",
        "charAt",
        "Returns Option, with None replacing the empty string for an out-of-range index.",
    ),
    (
        5,
        "charCodeAt",
        "charCodeAt",
        "Returns Option<number>, with None replacing NaN.",
    ),
    (
        5,
        "codePointAt",
        "codePointAt",
        "Returns Option<number>, with None replacing undefined.",
    ),
    (
        5,
        "concat",
        "concat",
        "Accepts exactly one string argument; native concat accepts any number of arguments and converts non-strings.",
    ),
    (5, "endsWith", "endsWith", "Same runtime behavior."),
    (5, "includes", "includes", "Same runtime behavior."),
    (
        5,
        "indexOf",
        "indexOf",
        "Returns Option<number>, with None replacing -1; there is no position parameter.",
    ),
    (
        5,
        "lastIndexOf",
        "lastIndexOf",
        "Returns Option<number>, with None replacing -1; there is no position parameter.",
    ),
    (
        5,
        "localeCompare",
        "localeCompare",
        "Returns an Ordering of -1, 0, or 1; Effect v4 types locales as Array<string>, so a single locale string needs an array.",
    ),
    (
        5,
        "match",
        "match",
        "Returns Option, with None replacing null.",
    ),
    (
        5,
        "matchAll",
        "matchAll",
        "Requires a RegExp; string patterns are not accepted.",
    ),
    (5, "normalize", "normalize", "Same runtime behavior."),
    (5, "padEnd", "padEnd", "Same runtime behavior."),
    (5, "padStart", "padStart", "Same runtime behavior."),
    (
        5,
        "repeat",
        "repeat",
        "In Effect v4, a negative count returns an empty string instead of throwing RangeError.",
    ),
    (
        5,
        "replace",
        "replace",
        "Requires a string replacement; replacer callbacks are not accepted.",
    ),
    (
        5,
        "replaceAll",
        "replaceAll",
        "Requires a string replacement; replacer callbacks are not accepted.",
    ),
    (
        5,
        "search",
        "search",
        "Returns Option<number>, with None replacing -1.",
    ),
    (5, "slice", "slice", "Same runtime behavior."),
    (
        5,
        "split",
        "split",
        "Returns a NonEmptyArray, so splitting an empty string by \"\" returns [\"\"] instead of []; there is no limit parameter.",
    ),
    (5, "startsWith", "startsWith", "Same runtime behavior."),
    (5, "substring", "substring", "Same runtime behavior."),
    (
        5,
        "toLocaleLowerCase",
        "toLocaleLowerCase",
        "Same runtime behavior; Effect v4 types the locale as string or Array<string>, without Intl.Locale.",
    ),
    (
        5,
        "toLocaleUpperCase",
        "toLocaleUpperCase",
        "Same runtime behavior; Effect v4 types the locale as string or Array<string>, without Intl.Locale.",
    ),
    (
        5,
        "toLowerCase",
        "toLowerCase",
        "Same runtime behavior; literal inputs keep a Lowercase<T> type.",
    ),
    (
        5,
        "toUpperCase",
        "toUpperCase",
        "Same runtime behavior; literal inputs keep an Uppercase<T> type.",
    ),
    (
        5,
        "trim",
        "trim",
        "Same runtime behavior; the literal result type only removes spaces, \\n, \\t, and \\r.",
    ),
    (
        5,
        "trimStart",
        "trimStart",
        "Same runtime behavior; the literal result type only removes spaces, \\n, \\t, and \\r.",
    ),
    (
        5,
        "trimEnd",
        "trimEnd",
        "Same runtime behavior; the literal result type only removes spaces, \\n, \\t, and \\r.",
    ),
    (
        5,
        "trimLeft",
        "trimStart",
        "Deprecated alias of trimStart; the literal result type only removes spaces, \\n, \\t, and \\r.",
    ),
    (
        5,
        "trimRight",
        "trimEnd",
        "Deprecated alias of trimEnd; the literal result type only removes spaces, \\n, \\t, and \\r.",
    ),
];

fn migration(name: &str) -> Option<&'static str> {
    Some(match name {
        "makeLatch" => "Use Latch.make instead of Effect.makeLatch.",
        "makeSemaphore" => "Use Semaphore.make instead of Effect.makeSemaphore.",
        "catchAll" => "Renamed to catch.",
        "catchAllCause" => "Renamed to catchCause.",
        "catchAllDefect" => "Renamed to catchDefect.",
        "catchSome" => {
            "Use Effect.catchIf instead. Note: the API shape changed from returning Option<Effect> to taking a predicate and handler separately."
        }
        "catchSomeCause" => {
            "Use Effect.catchCauseIf instead. Note: the API shape changed from returning Option<Effect> to taking a predicate and handler separately."
        }
        "ensureErrorType" => "Renamed to satisfiesErrorType.",
        "ensureRequirementsType" => "Renamed to satisfiesServicesType.",
        "ensureSuccessType" => "Renamed to satisfiesSuccessType.",
        "fork" => "Renamed to forkChild.",
        "forkDaemon" => "Renamed to forkDetach.",
        "scopeWith" => "Renamed to scopedWith.",
        "serviceOptional" => "Renamed to serviceOption.",
        "tapErrorCause" => "Renamed to tapCause.",
        "catchSomeDefect" => {
            "Use Effect.catchDefect or Effect.matchCause to handle specific defects."
        }
        "forkAll" => {
            "Fork effects individually with Effect.forEach and Effect.forkChild, or use Effect.all with concurrency options."
        }
        "forkWithErrorHandler" => {
            "Fork the effect with Effect.forkChild and observe the fiber result via Fiber.join or Fiber.await."
        }
        "Tag" => "Use Context.Service instead of Effect.Tag.",
        "Service" => "Use Context.Service instead of Effect.Service.",
        "runtime" => {
            "Runtime has been removed in Effect v4. Use Effect.context to grab services and then run using Effect.runPromiseWith."
        }
        "bindAll" => "Use Effect.gen instead of Effect.bindAll.",
        "EffectTypeId" => "EffectTypeId has been removed in Effect v4.",
        "acquireReleaseInterruptible" => "Use Effect.acquireRelease instead.",
        "allSuccesses" => "Use Effect.all with the { mode: 'either' } option and filter successes.",
        "allWith" => "Use Effect.all with options instead.",
        "allowInterrupt" => "Use Effect.yieldNow instead.",
        "ap" => "Use Effect.map and Effect.flatMap to apply functions instead.",
        "asSomeError" => "Use Effect.mapError(Option.some) instead.",
        "async" => {
            "Renamed to callback. Note: in v4 the callback receives a Scheduler as 'this' context."
        }
        "asyncEffect" => "Use Effect.suspend combined with Effect.promise instead.",
        "blocked" => "The request batching API has been reworked in Effect v4.",
        "cacheRequestResult" => "The request batching API has been reworked in Effect v4.",
        "cachedFunction" => "Use Effect.cached or implement caching with a Ref instead.",
        "cause" => "Use Effect.matchCause or Effect.sandbox to access the cause.",
        "checkInterruptible" => "Interruption checking has been removed in Effect v4.",
        "clock" => "Use Effect.clockWith instead.",
        "configProviderWith" => "ConfigProvider access has been reworked in Effect v4.",
        "console" => "Use Effect.consoleWith or the Console service directly.",
        "consoleWith" => "Console access has been reworked in Effect v4.",
        "contextWithEffect" => "Use Effect.flatMap with service access instead.",
        "custom" => "Use Effect.suspend or Effect.sync to create custom effects.",
        "daemonChildren" => "Use Effect.forkDetach to fork detached fibers instead.",
        "descriptor" => "Fiber descriptor access has been removed in Effect v4.",
        "descriptorWith" => "Fiber descriptor access has been removed in Effect v4.",
        "dieMessage" => "Use Effect.die(new Error(message)) instead.",
        "dieSync" => "Use Effect.die with a lazily evaluated value instead.",
        "diffFiberRefs" => "FiberRef has been replaced by Context.Reference in Effect v4.",
        "disconnect" => "Fiber disconnect has been removed in Effect v4.",
        "dropUntil" => "Use Array.dropUntil and Effect.forEach instead.",
        "dropWhile" => "Use Array.dropWhile and Effect.forEach instead.",
        "either" => {
            "Renamed to result. Note: returns Result.Result<A, E> instead of Either<E, A>. Use the Result module to work with the result."
        }
        "ensuringChild" => "Use Effect.onExit to manage child fiber cleanup instead.",
        "ensuringChildren" => "Use Effect.onExit to manage child fiber cleanup instead.",
        "every" => "Use Effect.forEach with a predicate check instead.",
        "exists" => "Use Effect.forEach with a predicate check instead.",
        "fiberIdWith" => "Use Effect.fiberId instead.",
        "filterEffectOrElse" => "Use Effect.filterOrElse with an effectful predicate instead.",
        "filterEffectOrFail" => "Use Effect.filterOrFail with an effectful predicate instead.",
        "filterOrDie" => "Use Effect.filterOrFail and Effect.orDie instead.",
        "filterOrDieMessage" => "Use Effect.filterOrFail and Effect.orDie instead.",
        "finalizersMask" => "Finalizer masking has been removed in Effect v4.",
        "flipWith" => "Use Effect.flip combined with the desired transformation instead.",
        "fromFiber" => "Use Fiber.join instead.",
        "fromFiberEffect" => "Use Effect.flatMap with Fiber.join instead.",
        "fromNullable" => "Use Effect.suspend with null checks instead.",
        "functionWithSpan" => "Use Effect.withSpan instead.",
        "getFiberRefs" => "FiberRef has been replaced by Context.Reference in Effect v4.",
        "getRuntimeFlags" => "Runtime flags have been removed in Effect v4.",
        "head" => "Use Array.head and Effect.flatMap instead.",
        "if" => "Use Effect.when instead of Effect.if.",
        "ignoreLogged" => "Logging configuration has been reworked in Effect v4.",
        "inheritFiberRefs" => "FiberRef has been replaced by Context.Reference in Effect v4.",
        "interruptWith" => "Use Effect.interrupt instead.",
        "intoDeferred" => "Use Deferred.complete instead.",
        "iterate" => "Use Effect.whileLoop or recursion with Effect.suspend instead.",
        "labelMetrics" => "Metric labeling has been reworked in Effect v4.",
        "labelMetricsScoped" => "Metric labeling has been reworked in Effect v4.",
        "liftPredicate" => "Use Effect.filterOrFail instead.",
        "linkSpanCurrent" => "Use Effect.linkSpans instead.",
        "locally" => {
            "FiberRef.locally has been removed. Use Effect.provideService with Context.Reference instead."
        }
        "locallyScoped" => {
            "FiberRef.locally has been removed. Use Effect.provideService with Context.Reference instead."
        }
        "locallyScopedWith" => {
            "FiberRef.locally has been removed. Use Effect.provideService with Context.Reference instead."
        }
        "locallyWith" => {
            "FiberRef.locally has been removed. Use Effect.provideService with Context.Reference instead."
        }
        "logAnnotations" => "Use Effect.annotateLogs instead.",
        "loop" => "Use Effect.whileLoop or recursion with Effect.suspend instead.",
        "mapAccum" => "Use Effect.gen with a mutable accumulator instead.",
        "mapErrorCause" => "Use Effect.sandbox and Effect.mapError instead.",
        "mapInputContext" => "Use Effect.provide with a layer instead.",
        "merge" => "Use Effect.match or Effect.exit instead.",
        "mergeAll" => "Use Effect.forEach with a mutable accumulator instead.",
        "metricLabels" => "Metric labeling has been reworked in Effect v4.",
        "negate" => "Use Effect.map with boolean negation instead.",
        "none" => "Use Effect.filterOrFail or Effect.option instead.",
        "once" => "Use Effect.cached instead.",
        "optionFromOptional" => "Use Effect.option instead.",
        "orDieWith" => "Use Effect.orDie or Effect.mapError combined with Effect.orDie instead.",
        "orElse" => "Use Effect.catch or Effect.matchEffect instead.",
        "orElseFail" => "Use Effect.mapError instead.",
        "parallelErrors" => "Use Effect.all with concurrency options instead.",
        "parallelFinalizers" => "Finalizer ordering configuration has been removed in Effect v4.",
        "patchFiberRefs" => "FiberRef has been replaced by Context.Reference in Effect v4.",
        "patchRuntimeFlags" => "Runtime flags have been removed in Effect v4.",
        "raceWith" => "Use Effect.race or Effect.raceFirst instead.",
        "random" => "Use Effect.randomWith instead.",
        "randomWith" => "Random access has been reworked in Effect v4.",
        "reduce" => "Use Effect.forEach with a mutable accumulator or Effect.gen instead.",
        "reduceEffect" => "Use Effect.forEach with a mutable accumulator or Effect.gen instead.",
        "reduceRight" => "Use Effect.forEach with a mutable accumulator or Effect.gen instead.",
        "reduceWhile" => "Use Effect.gen with early return instead.",
        "repeatN" => "Use Effect.repeat with a schedule instead.",
        "runRequestBlock" => "The request batching API has been reworked in Effect v4.",
        "scheduleForked" => "Use Effect.schedule combined with Effect.forkChild instead.",
        "sequentialFinalizers" => "Finalizer ordering configuration has been removed in Effect v4.",
        "serviceConstants" => {
            "Service helpers have been removed. Use Context.Service and yield* to access services."
        }
        "serviceFunction" => {
            "Service helpers have been removed. Use Context.Service and yield* to access services."
        }
        "serviceFunctionEffect" => {
            "Service helpers have been removed. Use Context.Service and yield* to access services."
        }
        "serviceFunctions" => {
            "Service helpers have been removed. Use Context.Service and yield* to access services."
        }
        "serviceMembers" => {
            "Service helpers have been removed. Use Context.Service and yield* to access services."
        }
        "setFiberRefs" => "FiberRef has been replaced by Context.Reference in Effect v4.",
        "step" => "The request batching API has been reworked in Effect v4.",
        "summarized" => "Use Effect.gen to capture before/after state instead.",
        "supervised" => "Supervision has been reworked in Effect v4.",
        "tagMetrics" => "Metric labeling has been reworked in Effect v4.",
        "tagMetricsScoped" => "Metric labeling has been reworked in Effect v4.",
        "takeUntil" => "Use Array.takeUntil and Effect.forEach instead.",
        "takeWhile" => "Use Array.takeWhile and Effect.forEach instead.",
        "tapBoth" => "Use Effect.tap and Effect.tapError instead.",
        "timedWith" => "Use Effect.timed instead.",
        "timeoutFail" => {
            "Use Effect.timeout combined with Effect.catchTag for TimeoutException instead."
        }
        "timeoutFailCause" => "Use Effect.timeout combined with Effect.sandbox instead.",
        "timeoutTo" => "Use Effect.timeoutOption and Effect.map instead.",
        "tracerWith" => "Use Effect.tracer instead.",
        "transplant" => "Fiber transplanting has been removed in Effect v4.",
        "transposeMapOption" => "Use Effect.map with Option operations instead.",
        "transposeOption" => "Use Effect.option instead.",
        "tryMap" => "Use Effect.map inside Effect.try instead.",
        "tryMapPromise" => "Use Effect.tryPromise instead.",
        "unless" => "Use Effect.when with a negated condition instead.",
        "unlessEffect" => "Use Effect.when with a negated effectful condition instead.",
        "unsafeMakeLatch" => "Use Effect.makeLatch instead.",
        "unsafeMakeSemaphore" => "Use Effect.makeSemaphore instead.",
        "unsandbox" => "Use Effect.catchCause instead.",
        "updateFiberRefs" => "FiberRef has been replaced by Context.Reference in Effect v4.",
        "using" => "Use Effect.scoped instead.",
        "validateAll" => "Use Effect.all with { mode: 'validate' } instead.",
        "validateFirst" => "Use Effect.all with { mode: 'validate' } instead.",
        "validateWith" => "Use Effect.all with { mode: 'validate' } instead.",
        "whenEffect" => "Use Effect.when with an effectful condition via Effect.flatMap instead.",
        "whenFiberRef" => "FiberRef has been replaced by Context.Reference in Effect v4.",
        "whenLogLevel" => "Log level checking has been reworked in Effect v4.",
        "whenRef" => "Use Ref.get and Effect.when instead.",
        "withClock" => "Clock configuration has been reworked in Effect v4.",
        "withClockScoped" => "Clock configuration has been reworked in Effect v4.",
        "withConfigProvider" => "ConfigProvider configuration has been reworked in Effect v4.",
        "withConfigProviderScoped" => {
            "ConfigProvider configuration has been reworked in Effect v4."
        }
        "withConsole" => "Console configuration has been reworked in Effect v4.",
        "withConsoleScoped" => "Console configuration has been reworked in Effect v4.",
        "withEarlyRelease" => "Use Effect.scoped with manual resource management instead.",
        "withFiberRuntime" => {
            "Renamed to withFiber. Note: in v4, only the Fiber is provided (not the full FiberRuntime with status). The callback receives (fiber: Fiber<unknown, unknown>) instead of (fiber: FiberRuntime<A, E>, status: FiberStatus)."
        }
        "withMaxOpsBeforeYield" => {
            "Use Context.Reference for MaxOpsBeforeYield configuration instead."
        }
        "withMetric" => "Metric configuration has been reworked in Effect v4.",
        "withRandom" => "Random configuration has been reworked in Effect v4.",
        "withRandomFixed" => "Random configuration has been reworked in Effect v4.",
        "withRandomScoped" => "Random configuration has been reworked in Effect v4.",
        "withRequestBatching" => "Request batching configuration has been reworked in Effect v4.",
        "withRequestCache" => "Request caching configuration has been reworked in Effect v4.",
        "withRequestCaching" => "Request caching configuration has been reworked in Effect v4.",
        "withRuntimeFlagsPatch" => "Runtime flags have been removed in Effect v4.",
        "withRuntimeFlagsPatchScoped" => "Runtime flags have been removed in Effect v4.",
        "withScheduler" => "Use Context.Reference for Scheduler configuration instead.",
        "withSchedulingPriority" => {
            "Scheduling priority configuration has been removed in Effect v4."
        }
        "withTracerScoped" => "Use Effect.withTracer instead.",
        "withUnhandledErrorLogLevel" => {
            "Use Context.Reference for UnhandledLogLevel configuration instead."
        }
        "zipLeft" => "Use Effect.tap instead of Effect.zipLeft.",
        "zipRight" => "Use Effect.andThen instead of Effect.zipRight.",
        _ => return None,
    })
}
