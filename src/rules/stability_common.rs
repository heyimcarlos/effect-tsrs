use std::collections::{HashMap, HashSet};
use std::path::Path;

use tsrs_ast::{self as ast, Kind, Node, SourceFile, Symbol, SymbolFlags};
use tsrs_checker::Signature;
use tsrs_core::P;

use super::RuleContext;

/// The ordering is significant: the larger value is the less stable API.
#[derive(Clone, Copy, Debug, Default)]
pub(crate) struct StabilityInfo {
    pub level: u8,
    pub declaration: Option<P<Node>>,
}

fn documentation_nodes(node: P<Node>) -> Vec<P<Node>> {
    let mut nodes = vec![node];
    if let Some(list) = node
        .parent()
        .filter(|p| p.kind() == Kind::VariableDeclarationList)
        && let Some(statement) = list
            .parent()
            .filter(|p| p.kind() == Kind::VariableStatement)
    {
        nodes.push(statement);
    }
    nodes
}

/// Read parsed JSDoc, including the enclosing statement of a variable. Prose
/// mentioning a tag and unrecognized stability values have no effect.
pub(crate) fn declaration_tag(node: P<Node>) -> Option<u8> {
    for node in documentation_nodes(node) {
        for doc in node.jsdoc(None) {
            let Some(tags) = doc.as_jsdoc().tags() else {
                continue;
            };
            for &tag in tags.nodes() {
                if tag.kind() != Kind::JSDocUnknownTag || tag.tag_name().text() != "stability" {
                    continue;
                }
                let Some(comment) = tag.as_jsdoc_unknown_tag().comment() else {
                    continue;
                };
                let Some(text) = comment
                    .nodes()
                    .first()
                    .filter(|t| t.kind() == Kind::JSDocText)
                else {
                    continue;
                };
                match text.text().trim() {
                    "stable" => return Some(0),
                    "unstable" => return Some(1),
                    "experimental" => return Some(2),
                    _ => {}
                }
            }
        }
    }
    None
}

pub(crate) fn is_internal(node: P<Node>) -> bool {
    documentation_nodes(node).into_iter().any(|node| {
        node.jsdoc(None).iter().any(|doc| {
            doc.as_jsdoc().tags().is_some_and(|tags| {
                tags.nodes().iter().any(|tag| {
                    tag.kind() == Kind::JSDocUnknownTag && tag.tag_name().text() == "internal"
                })
            })
        })
    })
}

pub(crate) fn declared_declaration(declaration: P<Node>) -> StabilityInfo {
    declaration_tag(declaration).map_or_else(StabilityInfo::default, |level| StabilityInfo {
        level,
        declaration: Some(declaration),
    })
}

fn has_alias_declaration(symbol: P<Symbol>) -> bool {
    symbol
        .declarations()
        .iter()
        .copied()
        .any(ast::is_alias_symbol_declaration)
}

pub(crate) fn resolve_alias(ctx: &mut RuleContext<'_>, mut symbol: P<Symbol>) -> Option<P<Symbol>> {
    let mut seen = HashSet::new();
    while symbol.flags().intersects(SymbolFlags::Alias) {
        if !seen.insert(symbol) || !has_alias_declaration(symbol) {
            return None;
        }
        let next = ctx.checker.effect_immediate_aliased_symbol(symbol)?;
        if next == symbol {
            break;
        }
        symbol = next;
    }
    Some(symbol)
}

pub(crate) fn declared_symbol(ctx: &mut RuleContext<'_>, mut symbol: P<Symbol>) -> StabilityInfo {
    let mut seen = HashSet::new();
    while seen.insert(symbol) {
        for &declaration in symbol.declarations() {
            let info = declared_declaration(declaration);
            if info.declaration.is_some() {
                return info;
            }
        }
        if !symbol.flags().intersects(SymbolFlags::Alias) || !has_alias_declaration(symbol) {
            break;
        }
        let Some(next) = ctx.checker.effect_immediate_aliased_symbol(symbol) else {
            break;
        };
        symbol = next;
    }
    StabilityInfo::default()
}

pub(crate) fn declared_signature(
    _ctx: &mut RuleContext<'_>,
    mut signature: P<Signature>,
) -> StabilityInfo {
    while let Some(target) = signature.target() {
        if target == signature {
            break;
        }
        signature = target;
    }
    signature
        .declaration()
        .map_or_else(StabilityInfo::default, declared_declaration)
}

#[derive(Default)]
pub(crate) struct DeclaredCache {
    symbols: HashMap<P<Symbol>, StabilityInfo>,
    signatures: HashMap<P<Signature>, StabilityInfo>,
}

impl DeclaredCache {
    pub fn symbol(
        &mut self,
        ctx: &mut RuleContext<'_>,
        symbol: Option<P<Symbol>>,
    ) -> StabilityInfo {
        let Some(symbol) = symbol else {
            return StabilityInfo::default();
        };
        *self
            .symbols
            .entry(symbol)
            .or_insert_with(|| declared_symbol(ctx, symbol))
    }

    pub fn signature(
        &mut self,
        ctx: &mut RuleContext<'_>,
        signature: P<Signature>,
    ) -> StabilityInfo {
        *self
            .signatures
            .entry(signature)
            .or_insert_with(|| declared_signature(ctx, signature))
    }
}

pub(crate) fn module_name(ctx: &mut RuleContext<'_>, file: P<SourceFile>) -> Option<String> {
    let package = ctx.package_json(file)?;
    let name = package.get("name")?.as_str().filter(|s| !s.is_empty())?;
    let parent = Path::new(file.file_name()).parent()?.to_str()?;
    let directory = ctx
        .program
        .get_nearest_ancestor_directory_with_package_json(parent);
    api_module_name(name, &directory, file.file_name())
}

fn normalize_path(path: &str) -> String {
    let path = path.replace('\\', "/");
    let mut parts: Vec<&str> = Vec::new();
    for part in path.split('/') {
        match part {
            "." => {}
            ".." if parts.last().is_some_and(|p| *p != ".." && !p.is_empty()) => {
                parts.pop();
            }
            _ => parts.push(part),
        }
    }
    parts.join("/")
}

pub(crate) fn api_module_name(package: &str, directory: &str, file_name: &str) -> Option<String> {
    if directory.is_empty() {
        return None;
    }
    let directory = format!("{}/", normalize_path(directory).trim_end_matches('/'));
    let file_name = normalize_path(file_name);
    let mut relative = file_name.strip_prefix(&directory)?;
    for prefix in ["dist/dts/", "dist/esm/", "dist/cjs/", "src/", "dist/"] {
        if let Some(rest) = relative.strip_prefix(prefix) {
            relative = rest;
            break;
        }
    }
    for extension in [
        ".d.ts", ".d.mts", ".d.cts", ".ts", ".mts", ".cts", ".tsx", ".js", ".mjs", ".cjs", ".jsx",
    ] {
        if let Some(rest) = relative.strip_suffix(extension) {
            relative = rest;
            break;
        }
    }
    if relative.rsplit('/').next() == Some("index") {
        relative = relative
            .strip_suffix("index")
            .unwrap()
            .trim_end_matches('/');
    }
    Some(if relative.is_empty() {
        package.to_owned()
    } else {
        format!("{package}/{relative}")
    })
}

fn is_module_export(ctx: &mut RuleContext<'_>, symbol: P<Symbol>, module: P<Symbol>) -> bool {
    ctx.checker
        .try_get_member_in_module_exports_and_properties(symbol.name(), module)
        == Some(symbol)
}

fn owning_export(
    ctx: &mut RuleContext<'_>,
    declaration: P<Node>,
    module: P<Symbol>,
) -> Option<P<Symbol>> {
    let mut current = declaration.parent();
    while let Some(node) = current {
        if let Some(symbol) = ctx.checker.get_symbol_of_declaration_exported(node) {
            let symbol = symbol.export_symbol().unwrap_or(symbol);
            if is_module_export(ctx, symbol, module) {
                return Some(symbol);
            }
        }
        current = node.parent();
    }
    None
}

pub(crate) struct Allowlist {
    entries: Vec<String>,
    decisions: HashMap<Option<P<Node>>, (bool, String)>,
    modules: HashMap<P<SourceFile>, Option<String>>,
}

impl Allowlist {
    pub fn new(ctx: &RuleContext<'_>, level: u8) -> Self {
        let key = if level == 2 {
            "allowedExperimentalApis"
        } else {
            "allowedUnstableApis"
        };
        Self {
            entries: ctx
                .options
                .get(key)
                .and_then(|v| v.as_array())
                .map(|v| {
                    v.iter()
                        .filter_map(|v| v.as_str().map(str::to_owned))
                        .collect()
                })
                .unwrap_or_default(),
            decisions: HashMap::new(),
            modules: HashMap::new(),
        }
    }

    pub fn decide(
        &mut self,
        ctx: &mut RuleContext<'_>,
        declaration: Option<P<Node>>,
    ) -> (bool, String) {
        if let Some(result) = self.decisions.get(&declaration) {
            return result.clone();
        }
        let result = self.compute(ctx, declaration);
        self.decisions.insert(declaration, result.clone());
        result
    }

    fn compute(
        &mut self,
        ctx: &mut RuleContext<'_>,
        declaration: Option<P<Node>>,
    ) -> (bool, String) {
        let Some(declaration) = declaration else {
            return (false, String::new());
        };
        let Some(file) = ast::get_source_file_of_node(declaration) else {
            return (false, String::new());
        };
        let module_name = self
            .modules
            .entry(file)
            .or_insert_with(|| module_name(ctx, file))
            .clone();
        let Some(module_name) = module_name else {
            return (false, String::new());
        };
        let module = ctx
            .checker
            .get_symbol_of_declaration_exported(file.as_node());
        let mut symbol = ctx
            .checker
            .get_symbol_of_declaration_exported(declaration)
            .map(|s| s.export_symbol().unwrap_or(s));
        if let Some(module) = module
            && symbol.is_none_or(|symbol| !is_module_export(ctx, symbol, module))
        {
            symbol = owning_export(ctx, declaration, module).or(symbol);
        }
        let mut name = module_name.clone();
        if let (Some(module), Some(symbol)) = (module, symbol)
            && is_module_export(ctx, symbol, module)
        {
            name = format!("{name}#{}", symbol.name());
        }
        for entry in &self.entries {
            if let Some((entry_module, member)) = entry.split_once('#') {
                if entry_module != module_name || member.is_empty() {
                    continue;
                }
                if let (Some(module), Some(symbol)) = (module, symbol)
                    && let Some(exported) = ctx
                        .checker
                        .try_get_member_in_module_exports_and_properties(member, module)
                {
                    if exported == symbol {
                        return (true, name);
                    }
                    if let (Some(left), Some(right)) =
                        (resolve_alias(ctx, exported), resolve_alias(ctx, symbol))
                        && ctx.checker.effect_same_symbol_reference(left, right)
                    {
                        return (true, name);
                    }
                }
            } else if !entry.is_empty()
                && (module_name == *entry
                    || module_name
                        .strip_prefix(entry)
                        .is_some_and(|s| s.starts_with('/')))
            {
                return (true, name);
            }
        }
        (false, name)
    }
}
