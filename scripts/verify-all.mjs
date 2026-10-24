import { spawn } from "node:child_process";
import fs from "node:fs";
import os from "node:os";
import path from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));
const options = {
  binary: "target/release/effect-tsrs", jobs: String(Math.min(8, os.availableParallelism())),
  output: `artifacts/all-rules/full-${new Date().toISOString().replace(/[:.]/g, "-")}`,
  "reuse-reference": "artifacts/all-rules", rules: "all", versions: "v3,v4", fixtures: "all", scope: "relevant",
};
for (let i = 2; i < process.argv.length; i += 2) {
  const key = process.argv[i].replace(/^--/, "");
  if (!(key in options) || !process.argv[i].startsWith("--") || process.argv[i + 1] === undefined) throw new Error(`Unknown or incomplete option: ${process.argv[i]}`);
  options[key] = process.argv[i + 1];
}
const jobs = Number(options.jobs);
if (!Number.isSafeInteger(jobs) || jobs < 1 || jobs > 32) throw new Error("--jobs must be between 1 and 32");
const catalog = JSON.parse(fs.readFileSync(path.join(root, "fixtures/all/rules.json"), "utf8"));
const names = options.rules === "all" ? catalog.map((rule) => rule.name) : [...new Set(options.rules.split(","))];
for (const name of names) if (!catalog.some((rule) => rule.name === name)) throw new Error(`Unknown rule: ${name}`);
const output = path.resolve(root, options.output);
fs.mkdirSync(output, { recursive: true });
const binary = path.join(output, "effect-tsrs");
if (fs.existsSync(binary)) throw new Error("Choose a new output directory to preserve the previous verification run");
fs.copyFileSync(path.resolve(root, options.binary), binary, fs.constants.COPYFILE_FICLONE);
fs.chmodSync(binary, 0o555);

function execute(args, log) {
  return new Promise((resolve, reject) => {
    const fd = log ? fs.openSync(log, "w") : null;
    const child = spawn(process.execPath, [path.join(root, "scripts/all-rules.mjs"), ...args], {
      cwd: root, stdio: fd === null ? "inherit" : ["ignore", fd, fd],
    });
    if (fd !== null) fs.closeSync(fd);
    child.once("error", reject);
    child.once("exit", (code, signal) => resolve(signal ? 1 : (code ?? 1)));
  });
}
const shared = ["--binary", binary, "--versions", options.versions, "--fixtures", options.fixtures, "--scope", options.scope];
const shards = Array.from({ length: Math.min(jobs, names.length) }, () => []);
names.forEach((name, i) => shards[i % shards.length].push(name));
console.log(`Checking ${names.length} rules in ${shards.length} processes; evidence: ${path.relative(root, output)}`);
const statuses = await Promise.all(shards.map(async (rules, i) => {
  const status = await execute(["run", ...shared, "--rules", rules.join(","), "--output", path.join(output, `shard-${i + 1}`),
    "--reuse-reference", options["reuse-reference"]], path.join(output, `shard-${i + 1}.log`));
  const file = path.join(output, `shard-${i + 1}/report.json`);
  const data = fs.existsSync(file) ? JSON.parse(fs.readFileSync(file, "utf8")) : null;
  const matched = data?.results?.filter((row) => row.status === "matched").length ?? 0;
  console.log(`Shard ${i + 1}: ${matched}/${data?.results?.length ?? 0} matched${status ? `; inspect shard-${i + 1}.log` : ""}`);
  return status;
}));
const status = await execute(["aggregate", ...shared, "--rules", options.rules, "--inputs", output, "--output", output]);
process.exitCode = status || (statuses.some((status) => status !== 0) ? 1 : 0);
