import { spawnSync } from "node:child_process";
import { existsSync, mkdirSync, readFileSync, readdirSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";

const root = fileURLToPath(new URL("../", import.meta.url));
const checkout = path.join(root, ".repos/tsrs");

function git(args, cwd = root, allowFailure = false) {
  const result = spawnSync("git", args, { cwd, encoding: "utf8" });
  if (result.error) throw result.error;
  if (result.status !== 0 && !allowFailure) {
    throw new Error(`git ${args.join(" ")} failed: ${result.stderr.trim()}`);
  }
  return result;
}

export function setupTsrs() {
  const upstream = JSON.parse(readFileSync(path.join(root, "upstream.json"), "utf8"));
  if (!existsSync(checkout)) {
    mkdirSync(path.dirname(checkout), { recursive: true });
    git(["clone", "--filter=blob:none", "--no-checkout", upstream.repository, checkout]);
    git(["checkout", "--detach", upstream.revision], checkout);
  }
  const revision = git(["rev-parse", "HEAD"], checkout).stdout.trim();
  if (revision !== upstream.revision) {
    throw new Error(`Expected tsrs ${upstream.revision}, found ${revision}. Preserve any local edits before replacing ${checkout}.`);
  }
  for (const name of readdirSync(path.join(root, "patches")).filter((name) => name.endsWith(".patch")).sort()) {
    const patch = path.join(root, "patches", name);
    if (git(["apply", "--reverse", "--check", patch], checkout, true).status === 0) continue;
    git(["apply", "--check", patch], checkout);
    git(["apply", patch], checkout);
  }
  console.log(`tsrs ${revision.slice(0, 12)} with Effect checker extensions ready`);
}

if (process.argv[1] && path.resolve(process.argv[1]) === fileURLToPath(import.meta.url)) setupTsrs();
