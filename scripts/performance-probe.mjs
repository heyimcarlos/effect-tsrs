import fs from "node:fs";
import path from "node:path";
import { argumentsFor, assertEqual, normalizedDiagnostics, root, run, selectedRules, statistics, timestamp, writeJson } from "./harness.mjs";

const args = argumentsFor({ report: "artifacts/performance/release1-all-host/report.json", output: `artifacts/performance/probe-${timestamp()}`, samples: "3", groups: "none,floatingEffect,asyncFunction,unnecessaryPipe,three,apiStabilityLeak,allExceptApiStabilityLeak,all" });
const samples = Number(args.samples);
if (!Number.isSafeInteger(samples) || samples < 1) throw new Error("--samples must be a positive integer");
const sourceFile = path.resolve(root, args.report);
const source = JSON.parse(fs.readFileSync(sourceFile, "utf8"));
if (!source.gatePassed) throw new Error("Source benchmark must have passed its parity gate");
const project = path.join(path.dirname(sourceFile), "workload");
const all = source.selectedRules;
const selections = {
  none: [], floatingEffect: ["floatingEffect"], asyncFunction: ["asyncFunction"],
  unnecessaryPipe: ["unnecessaryPipe"], three: selectedRules,
  apiStabilityLeak: ["apiStabilityLeak"], allExceptApiStabilityLeak: all.filter((r) => r !== "apiStabilityLeak"), all,
  allExceptDuplicatePackage: all.filter((r) => r !== "duplicatePackage"),
};
const names = args.groups.split(",");
for (const name of names) {
  if (!selections[name] && all.includes(name)) selections[name] = [name];
  if (!selections[name]) throw new Error(`Unknown group: ${name}`);
}
const output = path.resolve(root, args.output);
const reference = JSON.parse(fs.readFileSync(path.join(path.dirname(sourceFile), "gate/reference.stdout.json"), "utf8"));
const report = { sourceReport: sourceFile, binary: source.binaries.candidate, groups: Object.fromEntries(names.map((name) => [name, selections[name]])), samples: [], passed: false };
writeJson(path.join(output, "report.json"), report);
try {
  for (let sample = 0; sample < samples; sample++) {
    const order = names.map((_, i) => names[(i + sample) % names.length]);
    for (const name of order) {
      const rules = selections[name];
      const spec = structuredClone(source.commands.candidate);
      const index = spec.args.indexOf("--rules");
      spec.args[index + 1] = rules.length ? rules.join(",") : "none";
      const result = run(spec, path.join(output, `${sample + 1}-${name}`));
      const expected = normalizedDiagnostics({ diagnostics: reference.diagnostics.filter((d) => rules.includes(d.name)) }, project, rules);
      const actual = normalizedDiagnostics(result.data, project, rules);
      assertEqual(actual, expected, `Probe changed selected output for ${name}`);
      report.samples.push({ group: name, sample: sample + 1, elapsedMs: result.elapsedMs, diagnostics: actual.length, timings: result.data.timings });
      writeJson(path.join(output, "report.json"), report);
    }
  }
  report.statistics = Object.fromEntries(names.map((name) => {
    const rows = report.samples.filter((r) => r.group === name);
    return [name, { wallMs: statistics(rows.map((r) => r.elapsedMs)), effectMs: statistics(rows.map((r) => r.timings.effectMs)) }];
  }));
  report.passed = true;
  console.log(JSON.stringify(report.statistics, null, 2));
} catch (error) {
  report.error = error.message;
  console.error(error.message);
  process.exitCode = 1;
} finally {
  writeJson(path.join(output, "report.json"), report);
}
