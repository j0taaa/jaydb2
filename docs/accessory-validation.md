# Accessory workflow validation

This work sits on the reviewed engine at `6285060`. No existing `.bend` file,
server, contract, source proof, library, native runtime, wire protocol or existing
admission/checker/service tool was changed. Make targets, documentation, example
frontends, starter export/check tools and the optional TS client are accessories.

## Completed accessory checks

- TypeScript client: 24 codec, FIFO/fragmentation, process/failure and installed-
  tarball consumer tests; strict type checking and ESM/declaration build.
- The independent consumer installs only the built tarball into a separate TS
  application with a genuinely empty npm cache, then type-checks and executes it.
  Development compiler/Node types come from the controlled test installation;
  the SDK is loaded from the installed tarball, never a source symlink.
- Two owned-process lifecycle regressions verify pre-spawn option validation at
  the actual launch boundary and prevent signaling a reaped process group.
- 11 real ordinary/prepared SDK responses exercise fresh credentials, FIFO,
  refusal, invalidation and instance-local handles.
- Both starter profiles pass their actual universal certificate, termination and
  initial-validity targets in both official modes. All four law-breaking source
  mutations fail the intended proof obligations in both modes. Real prepared
  CRUD/conditional sessions check successful results and unchanged-state
  followups after denied admission.
- Seven cheap task workspace/parser/unknown-outcome checks and strict TS-app
  checking pass. The real cross-client persistent task test passed in 101.441s:
  TS saves; the seed is removed; Python reopens and exercises completion,
  refusal, Bob isolation and authentication; TS reopens to verify exact values.
  A second create is rejected without modifying the saved image.
- Bootstrap wrapper passes both with existing tools and with an isolated empty
  `.tools` directory: original pinned sources/executable are downloaded and
  verified, and the already-pinned supplied kernel is copied and hash-checked.
  No toolchain source or generated C is modified.

## GitHub smoke

The real hosted smoke job passed on source `b5d1156`:
https://github.com/j0taaa/jaydb2/actions/runs/42241149426

It includes a cold pinned-tool installation, the client/consumer/task/starter
checks, all 43 host tests, Clippy/formatting and benchmark-harness checks. The
first two hosted runs found genuine cold-environment assumptions: npm tarball
caching did not include registry metadata, and a host options test requires
installed tool paths. The consumer now uses an empty cache and the smoke job
installs the real pinned tools. No test was skipped and no fake tool paths were
created to obtain this result.

## Final local release and usage results

The complete release **test commands** passed locally: both official modes for
all selected proof aggregates and their negative controls, 21 admission/verifier,
10 native runtime, 43 host, 19 service, nine recovery and five demo tests, plus
library/index/receipt applications and all new native accessories.

The first long wrapper was edited while its shell was waiting for those tests.
After the final successful demo test, its stale input offset produced a stray
`brary: command not found` and exit 127. That wrapper invocation is **not**
recorded as a successful end-to-end script run. No database or test input was
changed. The now-frozen runner was checked separately: normal smoke exited 0,
and full-mode command-dispatch dry-run exited 0. The dry-run is evidence about
shell dispatch only; it is not substituted for the actual complete suites above.
Local raw outputs remain under `build/polish-checks/`.

The retained task workspace `.build/tasks/polish-workflow` contains the five
actual polish work items. Nineteen TS CLI invocations saved them, completed them,
reopened their exact titles/completion flags, checked Bob isolation, and verified
that refusal left the original task unchanged. The scripted session passed; no
long-term adoption claim is inferred. To open the result:

```sh
node applications/tasks/tasks.ts --workspace .build/tasks/polish-workflow --storage-mode open --command list
```

## Reproduction and limits

Use the commands in [verification.md](verification.md), the
[quickstart](../QUICKSTART.md) and the
[task-app notes](../applications/tasks/APPLICATION_NOTES.md).

The local full check uses the existing official proof/native/recovery/demo
commands. A first wrapper trial found an existing benchmark test module's
script-local import and absent `unittest.main`; the final wrapper uses unittest
discovery from that module's directory and the two oracle tests passed.
The final smoke rerun covers that corrected selection and the cold-cache repair.

Full GitHub release validation is available by manual dispatch/version tag;
local full validation is separate from a hosted full-workflow result. Neither
workflow publishes a release or package. The SDK is Node-only and does not add a
network listener, automatic retries, account provisioning or migrations.
Scripted use of real work items demonstrates the reference workflow; it is not
evidence of external adoption or long-term daily use. Existing engine proof and
trusted-boundary limitations remain unchanged.
