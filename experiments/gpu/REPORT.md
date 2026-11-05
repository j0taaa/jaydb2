# Optional CUDA execution

Optional GPU execution is implemented. This report records the supported integration and its validation evidence.

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

## Hardware and exact proof boundary

Inventory before implementation: NVIDIA GeForce RTX 3080 Ti, compute capability
8.6, 12,288 MiB, NVIDIA driver 595.99.02 reporting CUDA 13.2; installed nvcc and
NVRTC are CUDA 12.0 (nvcc 12.0.140). Host compiler: Ubuntu clang 19.1.1.
GCC 13.3.0 builds only the test interposer. CPU: Intel i7-11700K at 3.60 GHz,
16 hardware threads; Linux 7.0.0-38-generic, about 16 GiB system RAM. The desktop
also uses this GPU. No official compiler source/binary or canonical contract
file differs from the pinned starting point.

The fixture proof's exact checked functions are `ClientProof.safe`,
`response_safe`, `read_safe`, `write_safe`, `program_safe`, `execution_trace`,
`finite`, and the `Bindings.certificate` / `Bindings.terminates` definitions.
They retain the example's administrator `Configuration.Allowed` and
`AllAllowed` restricted credential-access law, including failed operations
and refusal prefixes. Preparation requires the universal context/arguments
certificate, and ordinary calls use the original concrete access proof.
The emitted executable retains the fresh input analysis and prepared exact
source/proof substitution. Proof targets pass through primary checking and
BendTT before native/GPU compilation; no GPU permission or validity assumption
is added. Numerical equivalence is tested against an independent oracle;
there is no new formal proof of the compiler, CUDA driver or hardware.
The accepted preprocessing prerequisite additionally supplies
`proof/Preprocessing.bend`; the native differential regression is rerun here.

## Remaining limitations

Linux/NVIDIA CUDA is the supported GPU integration. Metal, multi-GPU selection,
CPU fallback on GPU failure, persistent workers and GPU query optimization are
not implemented. The cap of one GPU execution is per server process; separate
instances must be coordinated by their administrator. Read batching must keep
GPU services exclusive. All execution requests remain serial in this branch.

The 64–4096 MiB argument caps the requested official managed-memory corpus,
not driver overhead or all device memory. Some accepted small sizes/workloads
can still exhaust the runtime or physical device and return failure. Large
computations can run arbitrarily long; there is no deadline or hard resource
cancellation. The fixture intentionally leaves runtime input bounds to the
caller and is a benchmark/example, not a resource-admission policy.

Artifacts and generated code live in private instance directories. Hash checks
assume protected host files/tools; they do not remove the OS file-use race
against a hostile same-UID process, attest vendor libraries cryptographically,
or prove the GPU obeys its execution contract. An architecture-incompatible
artifact can cause the unmodified official runtime to attempt recompilation;
the host rejects its result, even if the rebuild succeeds. Ordinary and
prepared physical failures can terminate the worker without publication;
a host crash still loses RAM state. No persistence or stronger serial theorem
is claimed by this feature.

## Performance evidence

[Raw measurements](benchmark-results.json) were collected by `make benchmark-gpu`
under the shared heavy lock on clean revision
`1c9400ac2ccdd1209c27e4cb01329b60de5bbc6e`. The production code has no interposer;
no launch-tracing/fault library or inspector was loaded during these timings.
Both instances used eight CPU workers and the GPU instance used a 512 MiB
corpus. Each sample times the complete prepared frame exchange, including
fresh authentication, integrity hashes, child startup, execution, process exit,
proposal validation, publication and response delivery/decoding. Oracle work
is outside the timing. Three samples per size, successive runtime arguments,
successful credential state evolution and exact checksum checks are required.

| Runtime workload | CPU median (range), ms | CUDA median (range), ms |
| --- | ---: | ---: |
| Depth 2, 4 leaves × 64 rounds | 5.197 (5.185–5.998) | 175.659 (171.592–181.182) |
| Depth 16, 65,536 leaves × 64 rounds | 5.755 (5.682–5.946) | 166.517 (158.150–169.409) |

The first preparation is measured separately from handle execution: CPU
5,570.246 ms, CUDA 6,922.759 ms. This includes proof admission and native
compilation, plus CUDA prebuild where enabled; it is not a kernel-only compile
time. Startup plus an invalid-credential synchronization request is also
separate: CPU 5,706.573 ms, CUDA 5,472.017 ms. The small checksum is 689,817,445;
the larger checksum is 3,127,646,773, both independently reproduced.

CUDA is substantially slower for both tested sizes. Fresh process/device
setup and full host request overhead dominate these workloads. There is no
speedup claim, kernel-only timing, throughput claim or measured break-even
point. Three samples on a desktop GPU are observations rather than a broad
performance characterization. Larger workloads and other machines are
unmeasured, and can run out of the configured corpus.

## Focused heavier runtime-input workload

`HeavyClient.bend` retains the same credential access pattern and certificate
interface, but passes runtime `depth × 4096` rounds to each leaf of `tree!`.
The selected depth-16 case has 65,536 leaves and 65,536 rounds per leaf:
4,294,967,296 mixing rounds. The small control uses depth 2 and 8,192 rounds
per leaf, checked with an independent iterative Python oracle. Heavy output
and the complete canonical native state proposal are compared with real,
unwrapped CPU execution; no billion-step Python oracle is required.

`heavy_benchmark.py` separately records the first preparation (admission,
native compilation and optional device prebuild), fresh native-worker total,
and complete prepared frame exchanges. Native-worker timing includes that
worker's input analysis, GPU initialization/load where enabled, computation,
proposal encoding, binary pipes and process exit; it is not kernel-only time.
Each native trial consumes the same known seed bytes and must propose exactly
the expected full state, including Bob's untouched credential. Two complete
requests per size also check exact checksums and current credential evolution.
The heavier run is a focused pair of sizes, rather than a parameter sweep.

Run the direct script with an outer lock (the `make benchmark-gpu` target for
the earlier fixture already locks internally and must be invoked directly):

```sh
mkdir -p build/gpu/tmp
flock /tmp/jaydb2-experiments-heavy.lock env TMPDIR="$PWD/build/gpu/tmp" \
  PYTHONPATH=. python3 -B experiments/gpu/heavy_benchmark.py \
  --output build/gpu/heavy-benchmark.json
```
