import fs from "node:fs";
import path from "node:path";
import { createHash } from "node:crypto";
import { spawnSync } from "node:child_process";
import { fileURLToPath } from "node:url";
import getExePath from "@effect/tsgo/lib/getExePath";

export const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), "..");
export const home = path.join(root, "fixtures/all");
export const sha256 = (content) => createHash("sha256").update(content).digest("hex");
export const readJson = (file) => JSON.parse(fs.readFileSync(file, "utf8"));
function writeText(file, data) {
  fs.mkdirSync(path.dirname(file), { recursive: true });
  if (fs.existsSync(file) && fs.readFileSync(file, "utf8") === data) return;
  const temporary = `${file}.${process.pid}.tmp`;
  fs.writeFileSync(temporary, data);
  fs.renameSync(temporary, file);
}
export function writeJson(file, data) {
  writeText(file, `${JSON.stringify(data, null, 2)}\n`);
}

export function jsonc(source) {
  let clean = "", string = false, escaped = false;
  for (let i = 0; i < source.length; i++) {
    const c = source[i], next = source[i + 1];
    if (string) {
      clean += c;
      if (escaped) escaped = false;
      else if (c === "\\") escaped = true;
      else if (c === '"') string = false;
    } else if (c === '"') { string = true; clean += c; }
    else if (c === "/" && next === "/") { while (i < source.length && source[i] !== "\n") i++; clean += "\n"; }
    else if (c === "/" && next === "*") { i += 2; while (i < source.length && !(source[i] === "*" && source[i + 1] === "/")) i++; i++; clean += " "; }
    else if (c === "," && /^\s*[}\]]/.test(source.slice(i + 1))) clean += " ";
    else clean += c;
  }
  return JSON.parse(clean);
}

// Matches internal/effecttest/runner.go parseTestUnits, including dropped text
// before the first @filename and the builder's handling of leading blank lines.
export function parseUnits(source, name) {
  const units = [];
  let currentName = "", content = "";
  for (const line of source.split(/\r?\n/)) {
    const directive = /^\/\/\s*@(\w+)\s*:\s*([^\r\n]*)/.exec(line);
    if (directive && directive[1].toLowerCase() === "filename") {
      if (currentName && content.length) units.push({ name: currentName, content });
      currentName = directive[2].trim(); content = ""; continue;
    }
    if (content.length) content += "\n";
    content += line;
  }
  if (currentName) units.push({ name: currentName, content });
  else if (content.length) units.push({ name, content });
  return units;
}

export const defaultPlugin = {
  name: "@effect/language-service", ignoreEffectErrorsInTscExitCode: true,
  skipDisabledOptimization: true,
  diagnosticSeverity: { experimentalApiUsage: "off", unstableApiUsage: "off", apiStabilityLeak: "off" },
};
export const defaultConfig = { compilerOptions: { skipLibCheck: true, plugins: [defaultPlugin] } };
export const compilerDefaults = { target: "ESNext", module: "NodeNext", moduleResolution: "NodeNext", skipDefaultLibCheck: true, skipLibCheck: true, noErrorTruncation: true, newLine: "lf", noEmit: true };

export function virtualPath(name) {
  return path.posix.normalize(name.startsWith("/") ? name : `/.src/${name}`);
}

export function setup(sourceRoot) {
  const liveInventory = path.join(root, "artifacts/all-rules/inventory.json");
  const inventory = readJson(fs.existsSync(liveInventory) ? liveInventory : path.join(home, "rules.json"));
  const revision = spawnSync("git", ["-C", sourceRoot, "rev-parse", "HEAD"], { encoding: "utf8" }).stdout?.trim();
  if (!revision) throw new Error(`Cannot determine source revision: ${sourceRoot}`);
  writeJson(path.join(home, "rules.json"), inventory);
  const fixtures = [];
  for (const version of ["v3", "v4"]) {
    const directory = path.join(sourceRoot, "testdata/tests", `effect-${version}`);
    const packageBytes = fs.readFileSync(path.join(directory, "package.json"));
    fs.mkdirSync(path.join(home, "deps", version), { recursive: true });
    fs.writeFileSync(path.join(home, "deps", version, "package.json"), packageBytes);
    for (const name of fs.readdirSync(directory).filter((f) => f.endsWith(".ts")).sort()) {
      const bytes = fs.readFileSync(path.join(directory, name));
      const source = bytes.toString("utf8");
      const rawPath = path.join("raw", version, name);
      fs.mkdirSync(path.join(home, "raw", version), { recursive: true });
      fs.writeFileSync(path.join(home, rawPath), bytes);
      const baselinePath = path.join(sourceRoot, "testdata/baselines/reference", `effect-${version}`, `${name.slice(0, -3)}.errors.txt`);
      const baseline = fs.existsSync(baselinePath) ? fs.readFileSync(baselinePath, "utf8") : null;
      const summary = baseline?.split(/\n==== /)[0] ?? "";
      const baselineRules = [...new Set([...summary.matchAll(/effect\((\w+)\)/g)].map((m) => m[1]))].sort();
      const baselineCounts = {};
      for (const match of summary.matchAll(/effect\((\w+)\)/g)) baselineCounts[match[1]] = (baselineCounts[match[1]] ?? 0) + 1;
      const references = new Set(baselineRules);
      const reasons = {};
      const add = (rule, why) => { references.add(rule); (reasons[rule] ??= []).push(why); };
      for (const rule of baselineRules) add(rule, "upstream error baseline");
      for (const rule of inventory) {
        if (name.startsWith(rule.name)) add(rule.name, "fixture filename prefix");
        if (new RegExp(`\\b${rule.name}\\s*:`).test(source)) add(rule.name, "source directive or plugin option");
      }
      // Negative plugin/directive fixtures should exercise every selected rule.
      const control = /^(pluginDisabled|unusedDirective|unknownRuleName|tsExpectErrorDoesNotSuppressEffectDiagnostics)/.test(name);
      const testConfig = /\/\/\s*@test-config\s+([^\r\n]+)/.exec(source);
      fixtures.push({ id: `${version}/${name.slice(0, -3)}`, version, name, raw: rawPath.split(path.sep).join("/"), sha256: sha256(bytes), baselineSha256: baseline === null ? null : sha256(baseline), baselineRules, baselineCounts, ruleRefs: [...references].sort(), reasons, control, testConfig: testConfig ? jsonc(testConfig[1]) : null, units: parseUnits(source, name).map((unit) => virtualPath(unit.name)) });
    }
  }
  const manifest = {
    schemaVersion: 1,
    source: { repository: "https://github.com/Effect-TS/tsgo", revision, license: "MIT", fixtureDirectories: ["testdata/tests/effect-v3", "testdata/tests/effect-v4"], preprocessing: ["internal/effecttest/runner.go:parseTestUnits and RunEffectTest", "internal/bundledeffect/effect.go:MountEffect and MountVitest", "internal/rules/rules_json_test.go:parseTestConfig (preview options only)"] },
    semantics: ["Raw fixture bytes preserved; materialized units normalize CRLF to LF like upstream.", "Virtual / is relocated to each case root; /.src is the compilation working directory.", "The pinned version package manifest is mounted at /.src/package.json unless explicitly replaced.", "Explicit tsconfig options are preserved, compiler harness defaults applied, and source units become explicit root files.", "Preview @test-config overrides are applied to plugin options; comments remain in the source.", "Original native output may include comment-enabled unrelated rules; comparisons filter the selected rule and retain all raw output.", "Related information is compared recursively; absent and empty related-information arrays are equivalent."],
    fixtures,
    controls: ["v3", "v4"].map((version) => {
      const source = "import { Effect } from \"effect\"\nexport const value = Effect.succeed(1)\n";
      return { id: `${version}/__clean_control`, version, name: "__clean_control.ts", synthetic: true,
        source, sha256: sha256(source), baselineRules: [], ruleRefs: [], control: true };
    }),
  };
  writeJson(path.join(home, "manifest.json"), manifest);
  return manifest;
}

export function prepare(fixture) {
  const source = fixture.synthetic ? fixture.source : fs.readFileSync(path.join(home, fixture.raw), "utf8");
  if (!fixture.synthetic && sha256(Buffer.from(source)) !== fixture.sha256) throw new Error(`Raw fixture hash changed: ${fixture.id}`);
  const units = parseUnits(source, fixture.name);
  const caseRoot = path.join(home, "cases", fixture.version, fixture.name.slice(0, -3));
  fs.mkdirSync(path.join(caseRoot, ".src"), { recursive: true });
  const real = (name) => path.join(caseRoot, virtualPath(name));
  const manifestPath = path.join(home, "deps", fixture.version, "package.json");
  const expectedEffectVersion = readJson(manifestPath).dependencies.effect;
  const effectManifest = path.join(home, "deps", fixture.version, "node_modules/effect/package.json");
  if (!fs.existsSync(effectManifest)) throw new Error(`Missing ${fixture.version} dependencies; run setup --install true`);
  if (readJson(effectManifest).version !== expectedEffectVersion) throw new Error(`Unexpected Effect version in ${effectManifest}`);
  const explicitPackage = units.some((u) => virtualPath(u.name) === "/.src/package.json");
  if (!explicitPackage) writeText(path.join(caseRoot, ".src/package.json"), fs.readFileSync(manifestPath, "utf8"));
  // Prevent an enclosing application's package identity leaking into absolute
  // /app fixtures. Their original fallback key root is the config directory.
  const addedPackageBoundaries = [];
  const dependencies = path.join(home, "deps", fixture.version, "node_modules");
  const nodeModules = path.join(caseRoot, "node_modules");
  fs.mkdirSync(nodeModules, { recursive: true });
  if (fs.existsSync(dependencies)) {
    for (const entry of fs.readdirSync(dependencies)) {
      if (entry.startsWith(".")) continue;
      const sourceEntry = path.join(dependencies, entry), target = path.join(nodeModules, entry);
      if (entry.startsWith("@")) {
        fs.mkdirSync(target, { recursive: true });
        for (const child of fs.readdirSync(sourceEntry)) {
          const childTarget = path.join(target, child);
          if (!fs.existsSync(childTarget)) fs.symlinkSync(path.join(sourceEntry, child), childTarget, "dir");
        }
      } else if (!fs.existsSync(target)) fs.symlinkSync(sourceEntry, target, "dir");
    }
  }
  let configUnit;
  const roots = [];
  for (const unit of units) {
    const file = real(unit.name);
    if (!file.startsWith(`${caseRoot}${path.sep}`)) throw new Error(`Unsafe virtual path in ${fixture.id}: ${unit.name}`);
    // Synthetic fixture packages must shadow mounted packages without changing
    // the shared dependency installation behind a symlink.
    let cursor = caseRoot;
    for (const segment of path.relative(caseRoot, path.dirname(file)).split(path.sep)) {
      cursor = path.join(cursor, segment);
      if (fs.existsSync(cursor) && fs.lstatSync(cursor).isSymbolicLink()) {
        // VFS writes overlay an installed package; retain its other files.
        const installed = fs.realpathSync(cursor);
        const overlay = `${cursor}.overlay-${process.pid}`;
        fs.cpSync(installed, overlay, { recursive: true });
        if (fs.lstatSync(cursor).isSymbolicLink()) {
          fs.unlinkSync(cursor);
          fs.renameSync(overlay, cursor);
        } else fs.rmSync(overlay, { recursive: true, force: true });
      }
      fs.mkdirSync(cursor, { recursive: true });
    }
    if (/\/(?:tsconfig|jsconfig)\.json$/i.test(virtualPath(unit.name))) configUnit = unit;
    else {
      writeText(file, unit.content);
      if (!virtualPath(unit.name).startsWith("/node_modules/") && /\.[cm]?[jt]sx?$/.test(unit.name)) roots.push(file);
    }
  }
  if (!configUnit) configUnit = { name: "tsconfig.json", content: JSON.stringify(defaultConfig) };
  const config = jsonc(configUnit.content);
  const configFile = real(configUnit.name);
  const options = { ...compilerDefaults, ...(config.compilerOptions ?? {}), skipDefaultLibCheck: true, skipLibCheck: true, noErrorTruncation: true, newLine: "lf", noEmit: true };
  if (!options.target || options.target.toLowerCase() === "es3") options.target = "ESNext";
  if (!options.module || options.module.toLowerCase() === "none") options.module = "NodeNext";
  if (!options.moduleResolution) options.moduleResolution = "NodeNext";
  const plugins = options.plugins ?? [];
  let plugin = plugins.find((p) => p.name === "@effect/language-service") ?? null;
  if (plugin) plugin = { ...plugin, ...(fixture.testConfig ?? {}) };
  if (fixture.testConfig && !plugin && !units.some((u) => /(?:tsconfig|jsconfig)\.json$/i.test(u.name))) plugin = { ...defaultPlugin, ...fixture.testConfig };
  if (plugin) options.plugins = [plugin];
  fs.mkdirSync(path.dirname(configFile), { recursive: true });
  writeJson(configFile, { ...config, compilerOptions: options, files: roots.map((file) => path.relative(path.dirname(configFile), file).split(path.sep).join("/")), include: [], exclude: [] });
  if (!virtualPath(configUnit.name).startsWith("/.src/")) {
    const boundary = path.join(path.dirname(configFile), "package.json");
    if (!fs.existsSync(boundary)) { writeJson(boundary, {}); addedPackageBoundaries.push(path.relative(caseRoot, boundary)); }
  }
  return { caseRoot, cwd: path.join(caseRoot, ".src"), configFile, plugin, roots, addedPackageBoundaries, dependencies };
}

const severityNames = { SeverityOff: "off", SeverityError: "error", SeverityWarning: "warning", SeveritySuggestion: "suggestion", SeverityMessage: "message" };
export function isolatedOptions(prepared, rule, inventory) {
  if (!prepared.plugin || prepared.plugin.diagnosticSeverity === null) return { diagnostics: false, diagnosticSeverity: null };
  const original = prepared.plugin.diagnosticSeverity ?? {};
  const severity = original[rule.name] ?? original["*"] ?? severityNames[rule.severity] ?? "warning";
  const diagnosticSeverity = Object.fromEntries(inventory.map((r) => [r.name, r.name === rule.name ? severity : "off"]));
  diagnosticSeverity.unusedDirective = "off"; diagnosticSeverity.unknownRuleName = "off";
  return { ...prepared.plugin, diagnosticSeverity };
}

export function commands(prepared, rule, inventory, binary) {
  const options = isolatedOptions(prepared, rule, inventory);
  return {
    reference: { command: getExePath(), args: ["--effect-cli-diagnostics", JSON.stringify({ cwd: prepared.cwd, project: prepared.configFile, format: "json", strict: false, progress: false, lspconfig: JSON.stringify(options) })] },
    candidate: { command: path.resolve(root, binary), args: ["diagnostics", "-p", prepared.configFile, "--format", "json", "--rules", rule.name, "--lspconfig", JSON.stringify(options)] },
    options,
  };
}

export function invoke(spec, prefix, timeout) {
  fs.mkdirSync(path.dirname(prefix), { recursive: true });
  const before = process.hrtime.bigint();
  const result = spawnSync(spec.command, spec.args, { cwd: root, env: { ...process.env, GOMAXPROCS: "1", RAYON_NUM_THREADS: "1" }, encoding: "utf8", timeout, maxBuffer: 64 * 1024 * 1024 });
  fs.writeFileSync(`${prefix}.stdout.json`, result.stdout ?? "");
  fs.writeFileSync(`${prefix}.stderr.txt`, result.stderr ?? "");
  const record = { ...spec, status: result.status, signal: result.signal, elapsedMs: Number(process.hrtime.bigint() - before) / 1e6, error: result.error?.message ?? null };
  writeJson(`${prefix}.process.json`, record);
  if (result.error || result.signal || ![0, 1].includes(result.status)) throw new Error(`Invocation failed (${record.status}, ${record.error ?? record.signal}): ${prefix}`);
  if (/panicked at|fatal error:|runtime error:|thread .*panicked/.test(result.stderr)) throw new Error(`Compiler panic: ${prefix}`);
  let data;
  try { data = JSON.parse(result.stdout); } catch { throw new Error(`Invalid JSON: ${prefix}`); }
  if (!Array.isArray(data.diagnostics)) throw new Error(`No diagnostic array: ${prefix}`);
  return { data, record };
}

export function normalize(data, prepared, rule) {
  const physicalToVirtual = (file) => {
    const absolute = path.isAbsolute(file) ? file : path.resolve(prepared.cwd, file);
    for (const [prefix, replacement] of [[prepared.caseRoot, ""], [prepared.dependencies, "/node_modules"]]) {
      if (absolute.startsWith(`${prefix}${path.sep}`)) return `${replacement}/${path.relative(prefix, absolute).split(path.sep).join("/")}`;
    }
    return absolute.split(path.sep).join("/");
  };
  const location = (d) => Object.fromEntries(["file", "start", "length", "line", "column", "endLine", "endColumn"].map((key) => {
    if (d[key] === undefined) throw new Error(`Missing diagnostic field ${key}`);
    return [key, key === "file" ? physicalToVirtual(d[key]) : d[key]];
  }));
  const related = (d) => ({ ...location(d), code: d.code, message: d.message });
  const diagnostics = data.diagnostics.filter((d) => d.name === rule.name).map((d) => {
    for (const field of ["severity", "code", "name", "message"]) if (d[field] === undefined) throw new Error(`Missing diagnostic field ${field}`);
    return { ...location(d), severity: d.severity, code: d.code, name: d.name, message: d.message, relatedInformation: (d.relatedInformation ?? d.related ?? []).map(related) };
  });
  return diagnostics.sort((a, b) => JSON.stringify(a).localeCompare(JSON.stringify(b)));
}

export function plan(manifest, rules, versions, selector, scope) {
  const entries = [], exclusions = [];
  const filter = selector === "all" ? null : new RegExp(selector);
  for (const fixture of [...manifest.fixtures, ...(manifest.controls ?? [])]) {
    if (!versions.includes(fixture.version) || (filter && !filter.test(fixture.id))) continue;
    for (const rule of rules) {
      if (scope !== "all" && !fixture.control && fixture.ruleRefs.length && !fixture.ruleRefs.includes(rule.name)) { exclusions.push({ fixture: fixture.id, rule: rule.name, reason: "associated with other rules; --scope all includes this pair" }); continue; }
      entries.push({ fixture, rule, supported: rule.versions.includes(fixture.version) });
    }
  }
  return { entries, exclusions };
}

export function findFiles(inputs, suffix) {
  const files = [];
  const visit = (directory) => {
    if (!fs.existsSync(directory)) return;
    if (fs.statSync(directory).isFile()) { if (directory.endsWith(suffix)) files.push(directory); return; }
    for (const entry of fs.readdirSync(directory, { withFileTypes: true })) {
      if (entry.isSymbolicLink()) continue;
      const target = path.join(directory, entry.name);
      if (entry.isDirectory()) visit(target);
      else if (entry.name.endsWith(suffix)) files.push(target);
    }
  };
  for (const input of inputs) visit(path.resolve(root, input));
  return [...new Set(files)].sort();
}

export function referenceKey(fixture, prepared, rule, options, nativeHash) {
  const lock = path.join(home, "deps", fixture.version, "package-lock.json");
  return sha256(JSON.stringify({
    source: fixture.sha256 ?? sha256(fixture.source), rule: rule.name, options,
    caseRoot: prepared.caseRoot, config: readJson(prepared.configFile),
    dependencyLock: fs.existsSync(lock) ? sha256(fs.readFileSync(lock)) : null,
    preprocessor: sha256(fs.readFileSync(fileURLToPath(import.meta.url))),
    nativeHash,
  }));
}

export function referenceCache(inputs) {
  const index = new Map();
  for (const file of findFiles(inputs, ".fixture.json")) {
    try {
      const metadata = readJson(file);
      const prefix = file.slice(0, -".fixture.json".length);
      if (metadata.referenceCacheKey && fs.existsSync(`${prefix}.reference.stdout.json`) && fs.existsSync(`${prefix}.reference.process.json`)) index.set(metadata.referenceCacheKey, `${prefix}.reference`);
    } catch { /* A partial file is not eligible for reuse. */ }
  }
  return index;
}

export function reuseReference(from, to) {
  const data = readJson(`${from}.stdout.json`);
  const record = readJson(`${from}.process.json`);
  if (!Array.isArray(data.diagnostics) || ![0, 1].includes(record.status) || record.signal || record.error) return null;
  fs.mkdirSync(path.dirname(to), { recursive: true });
  for (const suffix of [".stdout.json", ".stderr.txt"]) fs.copyFileSync(`${from}${suffix}`, `${to}${suffix}`);
  writeJson(`${to}.process.json`, { ...record, reusedFrom: from });
  return { data, record, reusedFrom: from };
}
