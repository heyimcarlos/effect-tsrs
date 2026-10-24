# Porting notes

All 130 registered diagnostic rules have native Rust implementations. The port
shares semantic helpers across rule families, supports Effect v3/v4 recognition,
and retains the source diagnostic templates. Go is only a differential-testing
oracle; the built executable does not launch it.

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

## Structure

| Responsibility | Implementation |
| --- | --- |
| CLI, output formats, exit codes | `src/main.rs`, `src/lib.rs` |
| Config parsing, compiler program, checking, UTF-16 locations | `src/project.rs` |
| Effect options, inheritance, file overrides, directives | `src/config.rs` |
| Complete rule registry and defaults | `src/registry.rs` |
| Package/export identity, types, generator context, pipe/flow recognition | `src/semantic/` |
| Rule implementations and original messages | `src/rules/`, `src/messages.json` |
| Original fixtures, provenance, dependency locks | `fixtures/all/` |
| Exact comparison, snapshots, reference reuse, coverage | `scripts/all-rules*.mjs`, `scripts/verify-all.mjs` |

```text
tsconfig + source files
  → tsrs config parser / compiler host / Program
  → ordinary TypeScript diagnostics
  → retained checker and AST + per-file Effect configuration
  → shared semantic helpers and enabled rule families
  → directive processing, duplicate compaction, UTF-16 output
```

Checker handles are exclusive: collecting program diagnostics while holding one
can deadlock. All ordinary checking completes before the Effect pass. Type handles
and semantic caches stay within a file's checker acquisition. Immutable package
metadata is cached once per program, by source file and package directory, so
package discovery does not reread manifests for every rule and source file.

The runner preserves both raw detected Effect versions and the normalized version
used by upstream rules. An unknown/conflicting version is distinct from v3 where
the original recognizer makes that distinction. Supported-version labels in the
registry are documentation metadata; explicit rule guards control behavior.

## Compiler extensions

The initial three-rule spike used public APIs alone. The full rule set needs a
small source patch, checked in as `patches/checker-extensions.patch`. It provides:

- Recorded failed type relations and expression types from ordinary checking.
- The contextual type retained for object literals and resolved generic arguments.
- Narrow accessors for assignment checks, constant evaluation, contextual checking,
  signature construction, concrete generic base types, and alias identity.
- Contextual inference replay for stability diagnostics on generic object literals.

`scripts/setup-tsrs.mjs` checks the exact upstream revision and applies the patch
idempotently. The root Cargo dependencies all point at that one checkout, avoiding
mixed compiler/type identities. Cargo and npm lockfiles pin the other dependencies.

No checker is recycled or AST reclaimed before analysis. Like tsrs's CLI, checking
runs on a thread with a 512 MiB reserved stack. The process lifetime owns the arenas;
this API is not a repeated-rebuild language-server implementation.

## Verification

```sh
npm run check
npm test
npm run verify -- --binary target/release/effect-tsrs
npm run verify:config -- --binary target/release/effect-tsrs
npm run fixtures:install
npm run verify:all
```

The matrix covers every one of the 612 copied upstream fixtures, plus v3/v4 clean
controls. Every rule needs positive reference coverage; empty output alone does
not count as implementation evidence. Codes, messages, severity, paths, all UTF-16
positions, and related information are compared exactly. Ordinary TypeScript
findings are recorded separately, with a smaller smoke suite checking compiler
parity, aliases, Unicode, clean input, and a deliberate TS2322 error.

Fixture preprocessing follows the upstream virtual-file runner: preserve raw
bytes, normalize materialized unit newlines, expand `@filename` units, mount the
matching dependency package, and apply the original options. Native output is
retained before filtering to the selected rule. An immutable candidate snapshot
prevents concurrent rebuilds from mixing implementations in a report.

The default 4,263-pair matrix uses fixture names, original diagnostic associations,
configuration references, and broad negative controls. `--scope all` runs every
rule against every fixture. Configuration tests separately exercise inherited
option merging, override paths, suppression use tracking, and unknown rule names.

Run `npm run fixtures:install && npm run verify:all`. Detailed comparisons and
process metadata are written under `artifacts/all-rules/`; summaries reject stale
candidate hashes or changed fixture/dependency/preprocessing inputs.

The final release passed **4,263/4,263 pairs**, with positive findings for all 130
rules and no missing cases or reference gaps. Ten direct configuration comparisons,
eight Rust unit tests, the compiler smoke suite, formatting, and Clippy with warnings
denied also passed. [Retained verification](fixtures/all/verification.json) identifies
the source tree, executable, upstream revisions, and per-rule coverage.

## Performance

The benchmark generates 120 Effect modules and a shared re-export module. It
checks exact diagnostics and ordinary TypeScript correctness before collecting
interleaved fresh-process samples. The original three-rule mode is retained for
regression comparison; `--rules all` exercises the full port. Peak RSS uses macOS
`/usr/bin/time -l`; raw samples, environment details, source and binary hashes are
retained with each report.

The final run used an Apple M4 Max, one warmup and seven interleaved samples per
variant, with the eight-process fixture suite active. All-rule output matched
726 diagnostics; the three-rule comparison matched 720. The generated TypeScript
project was error-free. Four rules produced findings in the all-rule workload.

| Command | Selected rules | Median wall time | Range | Median peak RSS |
| --- | ---: | ---: | ---: | ---: |
| Preserved spike executable | 3 | 111.1 ms | 94.1–122.3 ms | 53.2 MiB |
| Current effect-tsrs | 3 | 75.3 ms | 71.7–92.3 ms | 54.4 MiB |
| Current effect-tsrs | 130 | 194.7 ms | 191.8–220.8 ms | 77.0 MiB |
| effect-tsgo | 130 | 264.7 ms | 257.4–273.8 ms | 134.2 MiB |

The current three-rule path has no measured latency regression against the preserved
spike. The full Effect pass took a median 120.5 ms. These are command measurements
on a generated project: the Rust command also performs and reports a complete
ordinary TypeScript diagnostic pass, so the Go comparison does not isolate compiler
or language speed. It does not measure a long-lived editor or every Effect workload.

[Final samples, settings, and hashes](benchmarks/full-port.json) retain both
comparisons. [benchmarks/spike.json](benchmarks/spike.json) archives the earlier
three-rule run under its original conditions.

## Remaining integration work

The diagnostic rules and their configuration are implemented here. Integrating
these results into tsrs's own command-line driver or language server, preserving
watch/snapshot lifetimes, and porting editor actions are separate changes. No quick
fixes, refactors, completions, or hover providers are supplied by this CLI.

## Releasing

Keep the version in `Cargo.toml`, `Cargo.lock`, `package.json`, and the native
`optionalDependencies` in sync, then update `package-lock.json`. Regenerate
`THIRD-PARTY-NOTICES` with `node scripts/third-party-notices.mjs` after changing
`Cargo.lock`. Push a matching
`vX.Y.Z` tag to release. The `release-packages.yml` workflow builds and tests all
five platforms, runs the complete rule comparison on macOS ARM64, and publishes
the native packages. It waits for all five to become publicly available before
publishing the launcher.

Publishing uses npm's trusted publisher for `yielded-dev/effect-tsrs` and
`release-packages.yml`, with GitHub OIDC and provenance. No npm token is needed.
Manually dispatching the workflow builds and verifies packages without publishing.
