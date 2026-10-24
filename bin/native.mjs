import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";

export function nativeExecutable() {
  if (process.env.EFFECT_TSRS_BINARY) {
    const binary = path.resolve(process.env.EFFECT_TSRS_BINARY);
    if (!fs.statSync(binary).isFile()) throw new Error(`Not an executable file: ${binary}`);
    return binary;
  }
  const target = `${process.platform}-${process.arch}`;
  const supported = ["darwin-arm64", "darwin-x64", "linux-arm64", "linux-x64", "win32-x64"];
  if (!supported.includes(target)) throw new Error(`Unsupported platform ${target}. Supported platforms: ${supported.join(", ")}.`);
  const packageName = `@yielded/effect-tsrs-${target}`;
  const binaryName = process.platform === "win32" ? "effect-tsrs.exe" : "effect-tsrs";
  try {
    return createRequire(import.meta.url).resolve(`${packageName}/bin/${binaryName}`);
  } catch (error) {
    throw new Error(`Cannot find the native executable in ${packageName}. Reinstall @yielded/effect-tsrs with optional dependencies enabled for ${target} (do not use --omit=optional). ${error.message}`);
  }
}
