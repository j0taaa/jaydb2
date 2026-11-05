# Optional CUDA execution

Implementation and validation in progress; final evidence will replace this paragraph.

Base: `5925c57febd978d44fa24000233647a59e7898a6` (original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`). Accepted preprocessing prerequisite
`0f09c55dfff52fe10cd86b18a72a3241c5a92ad5` is merged; only initialize and
authenticate are compiled at startup, with fresh `Input.analyze` in execution.

`./jaydb2 --configuration examples/access/Configuration.bend --seed examples/access/Seed.bend --threads 8 --gpu 512`
opts into the official CUDA backend for explicit `!` calls with a 512 MiB corpus.
Default `--gpu off` retains CPU execution. MiB is an integer from 64 through
4096; there is no automatic CPU fallback for explicit bangs with GPU enabled.
Preprocessing always uses CPU. The serial controller allows one GPU worker at
a time per server, with no persistent workers or GPU database optimization.

Production compiles literal C from the checked Book, using pinned official
Bend 2.0.39 and `/usr/bin/clang-19` with `-DBEND_CUDA=1 -lcuda -lnvrtc`.
The executable itself builds its `.gpu` with official `--gpu-build` before a
registration is sealed. Both artifact hashes are retained by the controller
and checked as regular files before each execution and again before accepting
the result. All staged source, manifests, proof/dependency modules and both
artifacts belong to the prepared integrity snapshot. Missing/substituted files
refuse execution before entering CUDA. A device architecture change may make
the official runtime rebuild; any changed artifact or official rebuild
notification causes failure and rollback, requiring new preparation.

No emitted C, compiler, runtime or administrator proof target is patched.
The CUDA driver, NVRTC, compiler and physical GPU remain trusted implementation
boundaries. Existing `Bindings.certificate` / `Bindings.terminates`, prefix laws,
fresh `Input.analyze`, complete `checked_proposal` validation and cleanup before
publication remain in force. The serial theorem does not prove the CUDA
implementation or file/process bridge. The fixture's checked certificate proves
its original restricted-user access behavior and termination; numerical output
is independently tested, not supplied as an assumed validity proof.

The computation fixture uses the **runtime credential text length** as tree
depth, executes a balanced U32 tree with 64 mixing rounds per leaf via `tree!`,
then returns its checksum after a provisional credential write and read.
The Python oracle performs separate iterative arithmetic. Runtime arguments
change across calls without rebuilding a prepared program. The proof remains
bound to the exact client bytes, applicable administrator laws and dependencies.

A GPU-enabled program without reachable explicit bangs can perform CPU work;
no claim of a device launch is made for such work. Programs with bangs require
a usable CUDA device, managed memory and a compatible artifact. Failure never
publishes the provisional state. Existing protocol responses and all three
canonical limits are unchanged. The GPU corpus cap is additional runtime
capacity, not a change to the logical state/message/response limits.

Validation commands: `make test-gpu`, `make benchmark-gpu`. Both acquire
`flock /tmp/jaydb2-experiments-heavy.lock` and keep results and temporary state
under this worktree's `build/gpu`. General CPU regressions are separate.
The test-only `tests/service/gpu_faults.c` forwards successful calls to the real
CUDA driver, records launches and injects device/allocation/launch/synchronize
failures. It is never linked, frozen or loaded in production; unwrapped real
GPU and unavailable-device runs are separately required.
