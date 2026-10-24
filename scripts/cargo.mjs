// Keep Cargo and rustc on the pinned toolchain even when Homebrew Rust is first
// on PATH. `rustup run cargo` alone still found that older rustc on this machine.
import { execFileSync, spawnSync } from "node:child_process";
import { readFileSync } from "node:fs";
import path from "node:path";
import { fileURLToPath } from "node:url";
import { setupTsrs } from "./setup-tsrs.mjs";

const root = fileURLToPath(new URL("../", import.meta.url));
setupTsrs();
const channel = /channel\s*=\s*"([^"]+)"/.exec(
  readFileSync(path.join(root, "rust-toolchain.toml"), "utf8"),
)[1];
const cargo = execFileSync("rustup", ["which", "--toolchain", channel, "cargo"], {
  encoding: "utf8",
}).trim();
// Preserve rustup's toolchain environment for compiler helpers such as
// rust-objcopy as well. PATH selects the matching compiler for Cargo itself.
const result = spawnSync("rustup", ["run", channel, cargo, ...process.argv.slice(2)], {
  cwd: root,
  env: { ...process.env, PATH: `${path.dirname(cargo)}${path.delimiter}${process.env.PATH}` },
  stdio: "inherit",
});
if (result.error) throw result.error;
process.exit(result.status ?? 1);
