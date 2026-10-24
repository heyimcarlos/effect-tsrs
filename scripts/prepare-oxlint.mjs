import { fileURLToPath } from "node:url";
import path from "node:path";
import { copyOxlintArtifacts } from "./oxlint-artifacts.mjs";

const destination = process.argv[2] ? path.resolve(process.argv[2]) : fileURLToPath(new URL("../target/oxlint", import.meta.url));
copyOxlintArtifacts(destination);
console.log(`Pinned Oxlint frontend bindings copied to ${destination}.`);
