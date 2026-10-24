#!/usr/bin/env node

import { spawn } from "node:child_process";
import { constants } from "node:os";
import { pathToFileURL } from "node:url";
import { nativeExecutable } from "./native.mjs";
import { oxlintCommand, patchOxlint } from "./oxlint.mjs";

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

async function main() {
  const args = process.argv.slice(2);
  if (["patch", "unpatch"].includes(args[0])) {
    if (args.length !== 2 || args[1] !== "--oxlint") throw new Error("Usage: effect-tsrs patch|unpatch --oxlint");
    for (const file of patchOxlint(nativeExecutable(), args[0] === "unpatch")) console.log(`${args[0] === "unpatch" ? "Restored" : "Patched"} ${file}`);
    return;
  }
  const target = `${process.platform}-${process.arch}`;
  if (!targets.has(target)) {
    fail(`Unsupported platform ${target}. Supported platforms: ${[...targets].join(", ")}.`);
    return;
  }

  const packageName = `@yielded/effect-tsrs-${target}`;
  const executable = nativeExecutable();
  if (args[0] === "oxlint") {
    const command = oxlintCommand(executable, args.slice(1));
    Object.assign(process.env, command.env);
    process.argv = [process.execPath, ...command.args];
    await import(pathToFileURL(command.args[0]).href);
    return;
  }
  const command = { command: executable, args, env: process.env };

  const child = spawn(command.command, command.args, {
    stdio: "inherit",
    cwd: process.cwd(),
    env: command.env,
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

main().catch(error => fail(error.message));
