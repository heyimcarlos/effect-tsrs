import fs from "node:fs";
import path from "node:path";
import { argumentsFor, assertEqual, candidateTypeScript, checkParity, commands, manifest, metadata, parseTypeScript, root, run, timestamp, writeJson } from "./harness.mjs";

const args = argumentsFor({ binary: "target/debug/effect-tsrs", output: `artifacts/verify-${timestamp()}`, fixture: "all" });
const output = path.resolve(root, args.output);
const projects = manifest.projects.filter((p) => args.fixture === "all" || p.name === args.fixture);
if (!projects.length) throw new Error(`Unknown fixture: ${args.fixture}`);
fs.mkdirSync(output, { recursive: true });
const report = { ...metadata(projects.map((p) => path.join(root, "fixtures", p.name)), args.binary), projects: [], passed: false };
writeJson(path.join(output, "report.json"), report);
try {
  for (const fixture of projects) {
    const project = path.join(root, "fixtures", fixture.name);
    const specs = commands(project, args.binary);
    const prefix = path.join(output, fixture.name);
    const reference = run(specs.reference, `${prefix}/reference`);
    const candidate = run(specs.candidate, `${prefix}/candidate`);
    const compilerOnly = run(specs.compilerOnly, `${prefix}/compiler-only`);
    const originalCompiler = run(specs.typescript, `${prefix}/typescript`, { json: false, allowedStatuses: [0, 1, 2] });
    const expectedTs = parseTypeScript(originalCompiler, project);
    const actualTs = candidateTypeScript(candidate.data, project);
    writeJson(`${prefix}/typescript-comparison.json`, { expected: expectedTs, actual: actualTs });
    assertEqual(actualTs, expectedTs, `TypeScript diagnostics differ for ${fixture.name}`);
    assertEqual(candidateTypeScript(compilerOnly.data, project), actualTs, "--rules none changed compiler diagnostics");
    assertEqual(compilerOnly.data.diagnostics, [], "--rules none emitted Effect diagnostics");
    if (fixture.typescript === "clean") assertEqual(actualTs, [], `${fixture.name} must be TypeScript-correct`);
    if (fixture.expectedTypeScriptCodes) assertEqual(actualTs.map((d) => d.code).sort(), fixture.expectedTypeScriptCodes.slice().sort(), "Expected ordinary TypeScript errors");
    const diagnostics = checkParity(reference, candidate, project, `${prefix}/effect`);
    if (fixture.expectedDiagnostics !== undefined) assertEqual(diagnostics.length, fixture.expectedDiagnostics, "Unexpected diagnostic count");
    const counts = Object.fromEntries(["floatingEffect", "asyncFunction", "unnecessaryPipe"].map((name) => [name, diagnostics.filter((d) => d.name === name).length]));
    for (const [rule, minimum] of Object.entries(fixture.minimumDiagnostics ?? {})) {
      if (counts[rule] < minimum) throw new Error(`${fixture.name} has ${counts[rule]} ${rule} diagnostics; expected at least ${minimum}`);
    }
    report.projects.push({ name: fixture.name, counts, typescriptDiagnostics: actualTs, filesChecked: candidate.data.summary.filesChecked });
    writeJson(path.join(output, "report.json"), report);
    console.log(`${fixture.name}: exact Effect parity (${diagnostics.length} diagnostics), TypeScript parity (${actualTs.length})`);
  }
  report.passed = true;
  console.log(`Verification passed. Evidence: ${path.relative(root, output)}/report.json`);
} catch (error) {
  report.error = error.message;
  console.error(error.message);
  process.exitCode = 1;
} finally {
  writeJson(path.join(output, "report.json"), report);
}
