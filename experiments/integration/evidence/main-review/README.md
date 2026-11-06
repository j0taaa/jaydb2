# Main-merge review evidence

This directory supersedes the parent directory's historical validation for merge
readiness. The reviewed source is `00d973e58217dbb589e4fdd0a48815a623faae9a`;
subsequent publication changes only review text, evidence and evidence whitespace
attributes. See `validation.json` for exact gate revisions and commands.

`host-repair-full-suite.txt` contains the completed aggregate proof run, native
regressions and recovery/demo checks before the last JavaScript loader guard.
`final-source-suite.txt` repeats the native/application/recovery/demo gates on
that last guard, including actual application proofs in both official modes.
Every `.bend` input and the proof drivers were unchanged between these runs.
`clean-export.txt` checks a source-only Git export with no ignored generated
modules. `.tools` still points to the immutable pinned distribution; toolchain
installation is an external prerequisite.

The benchmark's raw records, checked request journal, fresh build log and full
selected-root identity are `benchmark.json`, `benchmark-requests.jsonl`,
`benchmark-build.txt` and `benchmark.txt`. They describe the repaired executable,
not the earlier integration executable in the parent directory. The runner holds
the shared heavy-work lock. It measures complete requests at a fixed two-physical-
core/two-native-thread budget; one warmup and seven measured paired rounds per
workload. Its RSS samples are not a strict peak-memory bound.

`timing-before.txt`, `descendant-before.txt` and `cycle-before.json` retain actual
failing probes. The descendant Rust reproduction embeds the old transport and
its Node fixture retains the staging helper's inherited-pipe shape. These are
historical reproducers, not production code. Final Rust unit tests provide
causal, deterministic pre-exec sentinel controls for all startup failure points.
`cycle-after.txt` retains the standalone cycle/diamond guard tests; these also
passed in the final and clean-export suites.

To reproduce the extra library oracle, restore `library-oracles.py.txt` as
`build/review-main/library/review_oracles.py`, and the two `*.bend.txt` files as
`ArithmeticRuntime.bend` and `KeysRuntime.bend` beside it, under the repository
root. Then run that Python script under the shared heavy-work lock with unlimited
soft stack. It emits official C using the pinned toolchain, compiles that exact
unchanged C with clang-19, clears inherited BENDRTS, and compares native results
against independent Python arithmetic and key parsing. `library-oracles.json`
records actual case counts and emitted-source hashes. Those source files are
reproducer fixtures, not additions to the library's formal theorem claims.

The static proof graph summary and historical evidence recheck remain separate
from the new run. `publication-map.json` records exact-tree local/API commit
mapping for the three code-repair commits. `source-identity.json` records the
final source tree and normal/fault controller bytes. `preservation.json` confirms
all eight source heads and all 316 original root snapshot files were untouched.
`SHA256SUMS` covers every other file in this directory, including this README.
