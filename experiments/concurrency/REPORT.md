# Conservative read batches (implementation in progress)

Base: `5925c57febd978d44fa24000233647a59e7898a6` (original reference
`9b751fab3c7c349ff473a2d11a7133573b6c4df2`). Accepted preprocessing
prerequisite: `0f09c55dfff52fe10cd86b18a72a3241c5a92ad5` (integration pending).
Scheduling prerequisite and final validation results will be recorded here.

The additional source-bound `Bindings.read_only : ReadOnly.Program(Client.program())`
target is checked by the official primary checker and BendTT, together with the
ordinary universal administrator and termination certificates. The predicate's
exact flattened source is pinned in admission. All contexts, arguments and
`S.Return` continuations are covered by a finite depth witness. Permitted
operations are `ReadCell`, `ViewExistence`, `CountRows`, `EnumerateKeys`.
The witness may depend on context/arguments but not a database observation;
state-dependent traversals without such a witness use ordinary exclusive
execution. Ordinary admission is unchanged.

Opcode 3 requests checked read preparation; opcode 1 executes any prepared
handle. Example (against `examples/credentials`):

```
python3 tools/client.py --prepare-read --code experiments/concurrency/Read.bend \
  --proof experiments/concurrency/ReadProof.bend --credential alice-token
```

`src/ReadOnly.bend` defines `Operation`, finite `Action`, bounded `Prefix`, and
universal `Program`. `proof/ReadBatches.bend` derives absence of state changes
from the operation semantics, proves every execution prefix preserves state,
and equates frozen-snapshot batch traces with serial execution in FIFO order.
This supplements the existing administrator certificate; it does not grant
extra access privileges or prove physical processes and channels correct.
The host's successful-state equality check is defense in depth.

Remaining implementation work: accepted FIFO scheduler integration, bounded
parallel host execution and deterministic/native regressions. No performance
claim or completion claim is made by this checkpoint.

The implementation now integrates scheduler interface `d8ac16189df3869192581bffc5acad735226d512`
and its accepted boundary fix `23f7bcb7e8b718288a7cad869215b8acee91b005`,
including accepted preprocessing `0f09c55dfff52fe10cd86b18a72a3241c5a92ad5`.
`--read-workers N` opts into up to 16 workers, cannot exceed `--threads`, and
defaults to 1. `--threads` remains the exclusive native worker count; read
batches split that budget as floor(threads/read-workers) per native program.
Selection never waits to fill a batch and never refills an active batch. The
framing queue remains bounded by 8 items and max(message-limit, 1MiB) retained
body bytes (saturated at host representability). Active read bodies are bounded
by N times the message limit. One published state is borrowed immutably across
all reads. Active native inputs/outputs may each hold state/response copies;
there are at most N of them. Ready results discard returned state and retain
at most N response-limit-sized frames, plus the published last response.
There are no persistent workers, retries, row locks, merges or historical states.
