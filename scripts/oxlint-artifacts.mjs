import fs from "node:fs";
import path from "node:path";
import { createRequire } from "node:module";

export function copyOxlintArtifacts(destination, target = `${process.platform}-${process.arch}`) {
  const metadata = JSON.parse(fs.readFileSync(new URL("../bin/oxlint-metadata.json", import.meta.url)));
  const manifest = createRequire(import.meta.url).resolve(`@effect/tsgo-${target}/package.json`);
  if (JSON.parse(fs.readFileSync(manifest)).version !== metadata.sourceVersion) throw new Error("Oxlint frontend artifact version differs from the pinned source package");
  for (const version of metadata.oxlintVersions) {
    const source = path.join(path.dirname(manifest), "artifacts/oxlint", version);
    const files = fs.readdirSync(source).filter(file => file.endsWith(".node"));
    if (files.length !== 1) throw new Error(`Expected one native Oxlint binding in ${source}`);
    fs.mkdirSync(path.join(destination, version), { recursive: true });
    fs.copyFileSync(path.join(source, files[0]), path.join(destination, version, files[0]));
  }
}
