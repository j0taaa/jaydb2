# Current experimental integration

`experiment-integration` follows main and contains the accepted CPU experiments,
SQL/Drizzle frontend, reproducible database comparison and optional official
CUDA backend. `SOURCES.json` records the input revisions. The Bend controller
replacement and quota enforcement are excluded. GPU support remains outside
main.

The GPU merge retains mainline helper startup/cleanup, best-effort diagnostics,
seed-free durable recovery, read certificates and the extended prepared
contract. Initialization, recovery and authentication always compile for CPU.
CUDA workers retain prebuilt device artifacts and before/after integrity checks.
CUDA programs remain exclusive even when certified CPU read batching is enabled;
there is at most one device worker per service instance. CPU read batching keeps
its existing FIFO and total CPU budget rules.

The focused GPU composition test pipelines certified CUDA reads with
`--read-workers 2`, checks ordered results and non-batched timing records, then
reopens the durable database, rejects an old handle and prepares a fresh one.
The other GPU gates check actual device execution, CPU/GPU publication parity,
unavailable devices, sealed artifacts and injected driver failures.

Historical experiment reports and measurement digests remain tied to their
original sources. They are not relabeled as measurements of this combined tree.
Fresh validation results will be recorded after the frozen candidate finishes.
