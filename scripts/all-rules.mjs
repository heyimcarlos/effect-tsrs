#!/usr/bin/env node
import fs from "node:fs";
import path from "node:path";
import os from "node:os";
import { spawnSync } from "node:child_process";
import { commands, findFiles, home, invoke, normalize, plan, prepare, readJson, referenceCache, referenceKey, reuseReference, root, setup, sha256, writeJson } from "./all-rules-lib.mjs";

const action = process.argv[2] ?? "list";
const args = {
  source: "../effect-tsgo", rules: "all", versions: "v3,v4", binary: "target/debug/effect-tsrs",
  fixtures: "all", scope: "relevant", output: `artifacts/all-rules/run-${new Date().toISOString().replace(/[:.]/g, "-")}`,
  timeout: "60000", install: "false", limit: "0", resume: "false", details: "false", "reuse-reference": "", inputs: "artifacts/all-rules",
};
for (let i = 3; i < process.argv.length; i += 2) {
  const key = process.argv[i].replace(/^--/, "");
  if (!(key in args) || !process.argv[i].startsWith("--") || process.argv[i + 1] === undefined) throw new Error(`Unknown or incomplete argument ${process.argv[i]}`);
  args[key] = process.argv[i + 1];
}
if (!["setup", "list", "run", "reference", "aggregate"].includes(action)) throw new Error("Usage: node scripts/all-rules.mjs setup|list|run|reference|aggregate [--rules name,name] [--versions v3,v4] [--fixtures REGEX] [--scope relevant|all] [--binary PATH] [--output DIR]");
if (!["relevant", "all"].includes(args.scope)) throw new Error("--scope must be relevant or all");
const versions = args.versions.split(",");
if (versions.some((v) => !["v3", "v4"].includes(v))) throw new Error("--versions must contain v3 and/or v4");
const timeout = Number(args.timeout), limit = Number(args.limit);
if (!Number.isSafeInteger(timeout) || timeout < 1 || !Number.isSafeInteger(limit) || limit < 0) throw new Error("Invalid --timeout or --limit");

if (action === "setup") {
  const manifest = setup(path.resolve(root, args.source));
  for (const version of versions) {
    if (args.install === "true") {
      const result = spawnSync("npm", ["install", "--ignore-scripts", "--no-audit", "--no-fund", "--legacy-peer-deps", "--cache", path.join(os.tmpdir(), "effect-tsrs-all-rules-npm-cache")], { cwd: path.join(home, "deps", version), stdio: "inherit" });
      if (result.status !== 0) throw new Error(`npm install failed for ${version}`);
    }
    const selectedFixtures = [...manifest.fixtures, ...(manifest.controls ?? [])].filter((f) => f.version === version);
    if (fs.existsSync(path.join(home, "deps", version, "node_modules/effect/package.json"))) {
      for (const fixture of selectedFixtures) prepare(fixture);
    }
    const count = manifest.fixtures.filter((f) => f.version === version).length;
    console.log(`${version}: copied ${count} original fixtures; dependencies ${fs.existsSync(path.join(home, "deps", version, "node_modules/effect/package.json")) ? "installed" : "missing (run setup --install true)"}`);
  }
  console.log(`Fixture manifest: ${path.relative(root, home)}/manifest.json`);
  process.exit(0);
}

const manifest = readJson(path.join(home, "manifest.json"));
const inventory = readJson(path.join(home, "rules.json"));
const names = args.rules === "all" ? inventory.map((r) => r.name) : args.rules.split(",");
for (const name of names) if (!inventory.some((r) => r.name === name)) throw new Error(`Unknown rule: ${name}`);
const rules = inventory.filter((r) => names.includes(r.name));
const planned = plan(manifest, rules, versions, args.fixtures, args.scope);
const selectedEntries = limit ? planned.entries.slice(0, limit) : planned.entries;
const gaps = [];
for (const rule of rules) {
  const supportedVersions = rule.versions.filter((v) => versions.includes(v));
  for (const version of supportedVersions) {
    if (!selectedEntries.some((p) => p.rule.name === rule.name && p.fixture.version === version)) gaps.push({ rule: rule.name, version, reason: "no selected fixture pairs" });
  }
}
if (action === "list") {
  const report = {
    fixtureCount: manifest.fixtures.length, selectedPairs: selectedEntries.length, allPlannedPairs: planned.entries.length,
    rules: rules.map((r) => ({ name: r.name, versions: r.versions, fixtureCount: selectedEntries.filter((p) => p.rule.name === r.name).length, fixtures: args.details === "true" ? selectedEntries.filter((p) => p.rule.name === r.name).map((p) => p.fixture.id) : undefined })),
    unmappedFixtures: manifest.fixtures.filter((f) => !f.ruleRefs.length && !f.control).map((f) => f.id), gaps,
    exclusionCount: planned.exclusions.length,
    exclusions: args.details === "true" ? planned.exclusions : undefined,
  };
  console.log(JSON.stringify(report, null, 2));
  process.exit(0);
}

const output = path.resolve(root, args.output);
fs.mkdirSync(output, { recursive: true });
const previous = args.resume === "true" && fs.existsSync(path.join(output, "report.json")) ? readJson(path.join(output, "report.json")) : null;
const hashFile = (file) => fs.existsSync(file) ? sha256(fs.readFileSync(file)) : null;
const binary = path.resolve(root, args.binary);
let executionBinary = binary;
let binaryHash = hashFile(binary);
if (action === "run") {
  if (previous) {
    if (!previous.binarySnapshot || !previous.binaryExecutionPath) throw new Error("Cannot resume a legacy run without an immutable binary snapshot; choose a new output directory");
    executionBinary = previous.binaryExecutionPath;
    binaryHash = hashFile(executionBinary);
    if (binaryHash !== previous.binarySha256) throw new Error("Candidate snapshot changed or is missing; cannot resume");
  } else {
    executionBinary = path.join(output, "candidate-binary");
    if (executionBinary === binary) throw new Error("Output snapshot would overwrite the source binary");
    const temporary = `${executionBinary}.${process.pid}.tmp`;
    fs.copyFileSync(binary, temporary, fs.constants.COPYFILE_FICLONE);
    fs.chmodSync(temporary, 0o555);
    fs.renameSync(temporary, executionBinary);
    binaryHash = hashFile(executionBinary);
  }
}
const harnessHash = hashFile(path.join(root, "scripts/all-rules-lib.mjs"));
const dependencyLockHashes = Object.fromEntries(versions.map((v) => [v, hashFile(path.join(home, "deps", v, "package-lock.json"))]));
if (previous && action !== "run" && previous.binarySha256 !== binaryHash) throw new Error("Refusing --resume with changed binary metadata; choose a new output directory");
if (previous && ["rules", "versions", "fixtures", "scope", "limit"].some((key) => previous.settings[key] !== args[key])) throw new Error("Refusing --resume with a changed selection; choose a new output directory");
if (previous && path.resolve(root, previous.settings.binary) !== binary) throw new Error("Refusing --resume with a different source binary path; keep the original path to reuse its snapshot");
if (previous && (previous.harnessSha256 !== harnessHash || JSON.stringify(previous.dependencyLockHashes) !== JSON.stringify(dependencyLockHashes))) throw new Error("Refusing --resume after preprocessing or dependencies changed; choose a new output directory and reuse compatible references");
if (action === "aggregate") {
  const selected = new Map(selectedEntries.map((p) => [`${p.fixture.id}:${p.rule.name}`, p]));
  const found = new Map(), stale = [], inputs = [];
  const reportFiles = findFiles(args.inputs.split(","), "report.json");
  for (const file of reportFiles) {
    let data;
    try { data = readJson(file); } catch { continue; }
    if (data.mode !== "run" || !Array.isArray(data.results)) continue;
    inputs.push(file);
    const eligible = data.binarySnapshot === true && data.binarySha256 === binaryHash && binaryHash !== null && data.harnessSha256 === harnessHash;
    for (const row of data.results) {
      const key = `${row.fixture}:${row.rule}`;
      const pair = selected.get(key);
      if (!pair) continue;
      const dependencyMatches = data.dependencyLockHashes?.[pair.fixture.version] === dependencyLockHashes[pair.fixture.version];
      if (!eligible || !dependencyMatches || (pair.fixture.sha256 && row.sourceSha256 !== pair.fixture.sha256)) { stale.push({ fixture: row.fixture, rule: row.rule, report: file, reason: !eligible ? "candidate binary or preprocessor hash differs" : !dependencyMatches ? "dependency lockfile hash differs" : "fixture source hash differs" }); continue; }
      const time = data.finishedAt ?? data.createdAt ?? "";
      if (!found.has(key) || time > found.get(key).time) found.set(key, { ...row, report: file, time });
    }
  }
  const missing = [...selected].filter(([key]) => !found.has(key)).map(([, p]) => ({ fixture: p.fixture.id, rule: p.rule.name }));
  const results = [...found.values()];
  const coverage = rules.map((rule) => {
    const rows = results.filter((r) => r.rule === rule.name);
    const expected = selectedEntries.filter((p) => p.rule.name === rule.name).length;
    return { rule: rule.name, expectedPairs: expected, observedPairs: rows.length, matchedPairs: rows.filter((r) => r.status === "matched").length, positiveReferenceFixtures: rows.filter((r) => r.referenceCount > 0).map((r) => r.fixture), byVersion: versions.map((version) => ({ version, observedPairs: rows.filter((r) => r.fixture.startsWith(`${version}/`)).length, positivePairs: rows.filter((r) => r.fixture.startsWith(`${version}/`) && r.referenceCount > 0).length })), failures: rows.filter((r) => r.status !== "matched" || r.referenceGap) };
  });
  const aggregate = { schemaVersion: 1, mode: "aggregate", createdAt: new Date().toISOString(), binary, binarySha256: binaryHash, source: manifest.source, settings: args, expectedPairs: selectedEntries.length, observedPairs: results.length, coverage, missing, stale, inputs, results, passed: missing.length === 0 && gaps.length === 0 && coverage.every((r) => r.failures.length === 0 && r.positiveReferenceFixtures.length > 0) };
  writeJson(path.join(output, "report.json"), aggregate);
  console.log(`aggregate: ${results.length}/${selectedEntries.length} current-binary pairs; ${coverage.filter((r) => r.positiveReferenceFixtures.length).length}/${rules.length} positive rules; ${stale.length} stale results. ${path.relative(root, output)}/report.json`);
  if (!aggregate.passed) process.exitCode = 1;
  process.exit();
}
const gitRevision = spawnSync("git", ["rev-parse", "HEAD"], { cwd: root, encoding: "utf8" }).stdout?.trim() ?? null;
const report = {
  schemaVersion: 1, mode: action, createdAt: new Date().toISOString(), gitRevision,
  source: manifest.source, binary, binaryExecutionPath: executionBinary, binarySnapshot: action === "run", binarySha256: binaryHash, harnessSha256: harnessHash, dependencyLockHashes,
  machine: { platform: process.platform, arch: process.arch, release: os.release(), cpu: os.cpus()[0]?.model },
  settings: { ...args, GOMAXPROCS: "1", RAYON_NUM_THREADS: "1" },
  fixtureCount: manifest.fixtures.length, plannedPairs: planned.entries.length, selectedPairs: selectedEntries.length,
  exclusionCount: planned.exclusions.length, planFile: "plan.json", gaps, results: previous?.results ?? [], completed: false, passed: false,
};
writeJson(path.join(output, "plan.json"), {
  pairs: selectedEntries.map((p) => ({ fixture: p.fixture.id, rule: p.rule.name })),
  exclusions: planned.exclusions,
  uncoveredOriginalFixtures: manifest.fixtures.filter((f) => !selectedEntries.some((p) => p.fixture.id === f.id)).map((f) => f.id),
});
writeJson(path.join(output, "report.json"), report);
const done = new Set(report.results.map((r) => `${r.fixture}:${r.rule}`));
const prepared = new Map();
const cachedReferences = args["reuse-reference"] ? referenceCache(args["reuse-reference"].split(",")) : new Map();
let count = 0;
for (const { fixture, rule } of selectedEntries) {
  const key = `${fixture.id}:${rule.name}`;
  if (done.has(key)) continue;
  const prefix = path.join(output, fixture.version, rule.name, fixture.name.slice(0, -3));
  const row = { fixture: fixture.id, rule: rule.name, sourceSha256: fixture.sha256, declaredSupportedVersion: rule.versions.includes(fixture.version), upstreamBaselineHadRule: fixture.baselineRules.includes(rule.name), upstreamBaselineCount: fixture.baselineCounts?.[rule.name] ?? 0, control: fixture.control, status: "failed" };
  try {
    if (!prepared.has(fixture.id)) prepared.set(fixture.id, prepare(fixture));
    const p = prepared.get(fixture.id);
    const specs = commands(p, rule, inventory, executionBinary);
    if (!report.referenceBinary) { report.referenceBinary = specs.reference.command; report.referenceBinarySha256 = hashFile(specs.reference.command); }
    row.options = specs.options;
    row.referenceCacheKey = referenceKey(fixture, p, rule, specs.options, report.referenceBinarySha256);
    row.syntheticPackageBoundaries = p.addedPackageBoundaries;
    writeJson(`${prefix}.fixture.json`, { ...row, cwd: p.cwd, configFile: p.configFile, roots: p.roots, commands: specs });
    let reference;
    const cached = cachedReferences.get(row.referenceCacheKey);
    if (cached && cached !== `${prefix}.reference`) {
      try { reference = reuseReference(cached, `${prefix}.reference`); } catch { /* Corrupt cache entries are rerun. */ }
    }
    if (!reference) reference = invoke(specs.reference, `${prefix}.reference`, timeout);
    row.reusedReference = reference.reusedFrom ?? null;
    const expected = normalize(reference.data, p, rule);
    row.referenceCount = expected.length;
    if (row.upstreamBaselineCount !== row.referenceCount) row.baselineCountDifference = row.referenceCount - row.upstreamBaselineCount;
    row.referenceOtherRules = [...new Set(reference.data.diagnostics.filter((d) => d.name !== rule.name).map((d) => d.name))];
    row.referenceFilesChecked = reference.data.summary?.filesChecked;
    if (action === "reference") {
      row.status = "reference-only";
      writeJson(`${prefix}.comparison.json`, { expected, actual: null });
    } else {
      const candidate = invoke(specs.candidate, `${prefix}.candidate`, timeout);
      const actual = normalize(candidate.data, p, rule);
      row.candidateCount = actual.length;
      row.candidateOtherRules = [...new Set(candidate.data.diagnostics.filter((d) => d.name !== rule.name).map((d) => d.name))];
      row.candidateTypeScriptCount = candidate.data.typescriptDiagnostics?.length ?? null;
      const equal = JSON.stringify(expected) === JSON.stringify(actual) && row.candidateOtherRules.length === 0;
      row.status = equal ? "matched" : "mismatch";
      writeJson(`${prefix}.comparison.json`, { equal, expected, actual });
    }
    if (row.upstreamBaselineHadRule && row.referenceCount === 0) row.referenceGap = "Upstream checked-in baseline contains this rule, but native oracle returned zero; inspect fixture/config/version fidelity";
  } catch (error) {
    row.error = error.message;
  }
  report.results.push(row);
  count++;
  writeJson(path.join(output, "report.json"), report);
  if (!["matched", "reference-only"].includes(row.status) || row.referenceGap) console.log(`${fixture.id} ${rule.name}: ${row.status}${row.error ? ` (${row.error})` : ""}${row.referenceGap ? " [reference coverage gap]" : ""}`);
  else if (count % 25 === 0) console.log(`${count}/${selectedEntries.length} pairs completed`);
}

report.coverage = rules.map((rule) => {
  const rows = report.results.filter((r) => r.rule === rule.name);
  const referencePositive = rows.filter((r) => (r.referenceCount ?? 0) > 0);
  return {
    rule: rule.name, versions, declaredSupportedVersions: rule.versions, pairs: rows.length,
    matched: rows.filter((r) => r.status === "matched").length,
    failed: rows.filter((r) => ["mismatch", "failed"].includes(r.status)).length,
    referencePositiveFixtures: referencePositive.map((r) => r.fixture),
    referenceDiagnostics: rows.reduce((sum, r) => sum + (r.referenceCount ?? 0), 0),
    zeroReferenceFixtures: rows.filter((r) => r.referenceCount === 0).map((r) => r.fixture),
    referenceGaps: rows.filter((r) => r.referenceGap).map((r) => r.fixture),
    positiveCoverage: referencePositive.length > 0,
    byVersion: versions.map((version) => ({ version, pairs: rows.filter((r) => r.fixture.startsWith(`${version}/`)).length, positivePairs: referencePositive.filter((r) => r.fixture.startsWith(`${version}/`)).length })),
  };
});
for (const coverage of report.coverage) {
  if (!coverage.positiveCoverage && coverage.versions.length) report.gaps.push({ rule: coverage.rule, reason: "no positive native-reference fixture in selected run; zero/zero is not positive coverage" });
}
report.completedSelection = report.results.length === selectedEntries.length;
report.completed = report.completedSelection && selectedEntries.length === planned.entries.length;
report.binaryIntegrityVerified = action !== "run" || hashFile(executionBinary) === binaryHash;
if (!report.binaryIntegrityVerified) report.gaps.push({ reason: "candidate snapshot changed during the run" });
report.passed = action === "run" && report.completed && report.gaps.length === 0 && report.results.every((r) => r.status === "matched" && !r.referenceGap);
report.referencePassed = report.completed && report.gaps.length === 0 && report.results.every((r) => r.referenceCount !== undefined && !r.referenceGap);
report.finishedAt = new Date().toISOString();
writeJson(path.join(output, "report.json"), report);
console.log(`${action}: ${report.results.length} pairs; ${report.coverage.filter((c) => c.positiveCoverage).length}/${rules.length} rules with positive native coverage; ${report.results.filter((r) => r.status === "mismatch" || r.status === "failed").length} failures. ${path.relative(root, output)}/report.json`);
if ((action === "run" && !report.passed) || (action === "reference" && !report.referencePassed)) process.exitCode = 1;
