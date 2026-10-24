#!/usr/bin/env node

import { spawn } from "node:child_process";
import { createRequire } from "node:module";
import { constants } from "node:os";

const targets = new Set([
  "darwin-arm64",
  "darwin-x64",
  "linux-x64",
  "linux-arm64",
  "win32-x64",
]);

function fail(message) {
  console.error(`effect-tsrs: ${message}`);
  process.exitCode = 1;
}

function main() {
  const target = `${process.platform}-${process.arch}`;
  if (!targets.has(target)) {
    fail(`Unsupported platform ${target}. Supported platforms: ${[...targets].join(", ")}.`);
    return;
  }

  const packageName = `@yielded/effect-tsrs-${target}`;
  const binaryName = process.platform === "win32" ? "effect-tsrs.exe" : "effect-tsrs";
  let executable;
  try {
    executable = createRequire(import.meta.url).resolve(`${packageName}/bin/${binaryName}`);
  } catch (error) {
    fail(`Cannot find the native executable in ${packageName}. Reinstall @yielded/effect-tsrs with optional dependencies enabled for ${target} (do not use --omit=optional). ${error.message}`);
    return;
  }

  const child = spawn(executable, process.argv.slice(2), {
    stdio: "inherit",
    cwd: process.cwd(),
  });
  const signals = ["SIGINT", "SIGTERM", "SIGHUP"];
  const forward = new Map(signals.map((signal) => [signal, () => child.kill(signal)]));
  for (const [signal, handler] of forward) process.on(signal, handler);
  const cleanup = () => {
    for (const [signal, handler] of forward) process.removeListener(signal, handler);
  };

  child.once("error", (error) => {
    cleanup();
    fail(`Could not start ${packageName}: ${error.message}`);
  });
  child.once("exit", (code, signal) => {
    cleanup();
    if (signal) {
      // Preserve signal termination for shells and process supervisors, rather
      // than turning it into an ordinary successful launcher exit.
      process.exitCode = 128 + (constants.signals[signal] ?? 1);
      try {
        process.kill(process.pid, signal);
      } catch {
        // Some signals cannot be raised on Windows; keep their failure code.
      }
    } else {
      process.exitCode = code ?? 1;
    }
  });
}

main();
