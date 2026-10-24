# effect-tsrs

A native Rust port of all **130 diagnostic rules** from
[effect-tsgo](https://github.com/Effect-TS/tsgo) to
[tsrs](https://github.com/oxc-project/tsrs). It checks a real TypeScript project,
then evaluates Effect diagnostics using the compiler's inferred types, symbols,
and AST. Both Effect v3 and v4 are supported.

The diagnostic runner is native Rust. The npm package uses a small Node launcher
to select the binary for your platform.

## Install and run

Requires Node 22.14 or newer. Prebuilt binaries are included for macOS (Apple
Silicon and Intel), Linux (x64 and ARM64), and Windows (x64). Linux builds are
statically linked with musl; no Rust toolchain or install scripts are required.

```sh
npm install --save-dev @yielded/effect-tsrs
npx effect-tsrs diagnostics -p tsconfig.json

# Or run without adding a dependency:
npx @yielded/effect-tsrs diagnostics -p tsconfig.json --format json
```

Keep optional dependencies enabled: npm uses them to install the native package
for your platform. The TypeScript standard libraries are embedded in the binary.

## Build from source

Requires rustup, a C compiler, CMake, and Node/npm. The build wrapper selects the
pinned Rust toolchain and verifies the pinned tsrs checkout and compiler patch.

```sh
rustup toolchain install 1.99.1 --profile minimal --component clippy --component rustfmt
npm ci --ignore-scripts
npm run setup
npm run build:release

./target/release/effect-tsrs diagnostics -p /path/to/tsconfig.json --format json
```

`npm run setup` creates `.repos/tsrs` at the revision in `upstream.json` and applies
`patches/checker-extensions.patch`. It preserves local changes and rejects an
unexpected revision or incompatible patch. Builds also perform this check.

## Configuration

The runner reads `@effect/language-service` options from `compilerOptions.plugins`,
including inherited settings, per-file overrides, rule severities, and source
suppression directives. Without a plugin entry, it uses upstream rule defaults.

```sh
# Select a subset; default-off rules become warnings unless explicitly disabled.
npx effect-tsrs diagnostics -p tsconfig.json \
  --rules floatingEffect,asyncFunction,unnecessaryPipe

# Select all 130 rules, subject to explicit configuration and directives.
npx effect-tsrs diagnostics -p tsconfig.json --rules all

# Replace the plugin options with an editor/CLI configuration.
npx effect-tsrs diagnostics -p tsconfig.json \
  --lspconfig '{"diagnosticSeverity":{"floatingEffect":"warning"}}'
```

`--rules none` disables the source-file Effect pass. Original version-specific
checks live in the individual rules; the registry's supported-version labels are
metadata, not a blanket runtime filter. The complete inventory is in
[fixtures/rule-catalog.json](fixtures/rule-catalog.json).

JSON contains Effect `diagnostics`, separate `typescriptDiagnostics`, a summary,
and phase `timings`. Diagnostic positions use UTF-16 code units; lines and columns
are one-based. Related information retains its own file and range. Text output
includes both kinds of diagnostics.

Exit codes: **0** for no errors, **1** for TypeScript or Effect errors, **2** for an
invocation/compiler failure. Warnings and suggestions do not fail the command.
Unused suppression directives and unknown configured rule names are diagnosed too.

## Verify

```sh
npm run check
npm test
npm run verify -- --binary target/release/effect-tsrs
npm run verify:config -- --binary target/release/effect-tsrs
npm run fixtures:install
npm run verify:all
```

The full suite retains **612 original fixtures**, their hashes, and separate pinned
Effect v3/v4 dependencies. It compares codes, messages, severities, UTF-16 ranges,
and related information against `@effect/tsgo@0.56.0`. The default matrix also
includes two clean controls and checks 4,263 rule/fixture pairs. Each run snapshots
the executable, records failures and coverage gaps, and reuses compatible reference
results. `verify:all` runs eight processes by default; use `--jobs N` to change it.

The verified release passes **4,263/4,263 comparisons**, with positive coverage for
all 130 rules, plus 10 configuration comparisons and 8 unit tests. See the
[retained coverage and source hashes](fixtures/all/verification.json).

See [the fixture guide](fixtures/all/HARNESS.md) for focused comparisons, fixture
regeneration, and the exhaustive `--scope all` matrix. The copied fixtures and
lockfiles allow verification without a sibling effect-tsgo checkout.

```sh
npm run bench
npm run bench -- --rules all
```

Benchmarks verify exact output before measuring fresh processes, retain individual
samples, and report wall time and peak RSS. Detailed results and integration notes
are in [PORTING.md](PORTING.md).

## Integration boundary

This is a one-project, one-process diagnostic CLI. Editor quick fixes, refactors,
hovers, completions, watch/build orchestration, and language-server integration
remain separate work. The process retains compiler arenas and ASTs until exit;
a long-lived host needs tsrs's project/snapshot lifetime management.

Pinned sources: effect-tsgo `8813161074039b67ddb8fe1847e8efa0d8ff1e24` (0.56.0)
and tsrs `8f135f106a637cf76f0395f146d0417f5287046e` (0.19.0,
TypeScript 7.1.0-beta). Fixtures use Effect 3.19.19 and 4.0.2.

## Releasing

Keep the version in `Cargo.toml`, `Cargo.lock`, `package.json`, and the native
`optionalDependencies` in sync, then update `package-lock.json`. Push a matching
`vX.Y.Z` tag to release. The `release-packages.yml` workflow builds and tests all
five platforms, runs the complete rule comparison on macOS ARM64, and publishes
the native packages before the launcher.

Publishing uses npm's trusted publisher for `yielded-dev/effect-tsrs` and
`release-packages.yml`, with GitHub OIDC and provenance. No npm token is needed.
Manually dispatching the workflow builds and verifies packages without publishing.

## License

Translated rules and copied fixtures retain effect-tsgo's [MIT license](LICENSE).
The tsrs/TypeScript compiler is an Apache-2.0 dependency. Binary packages include
its notices and dependency licenses in [THIRD-PARTY-NOTICES](THIRD-PARTY-NOTICES).
