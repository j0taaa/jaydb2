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
