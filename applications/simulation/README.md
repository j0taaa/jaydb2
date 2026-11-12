# Certified scenario simulation

Each of Alice and Bob owns one `scenarios` parameter row and one `results`
aggregate row. The installed access law permits reading only the caller's
scenario row and writing only the caller's result row. It permits no user-registry
access, scenario mutation, result reads, enumeration, or other operations.
The seed supplies two scenarios; a call simulates one authenticated user's row.

`Client.bend` accepts `[depth, steps]`, with integer `0 <= depth <= 18` and
`0 <= steps <= 65536`. It reads `seed`, `drift`, and `volatility` through three
ordinary access operations, runs `2^depth` independent paths in one balanced
`simulate!(...)` fork tree, and upserts its result in a fourth access operation.
The table remains small while runtime arguments scale numerical work. The
bounds constrain the inputs, not elapsed time or physical resource usage.

For path index `i`, all words and each arithmetic operation are modulo `2^32`:

```
r = seed + i * 747796405
v = 1000000
repeat steps times:
    r = r * 1664525 + 1013904223
    v = v + (drift % 65536) + ((r >> 16) % (2*(volatility % 32768)+1))
          - (volatility % 32768)
```

This is a deterministic integer random-walk Monte Carlo workload, using the
Numerical Recipes LCG constants. It is a reproducible compute demonstration,
not a calibrated asset-pricing model or a high-quality statistical PRNG.
The result contains `sum` modulo `2^32`, unsigned `max`, `above` (terminal
values strictly above 1,000,000), and `paths`. The sum is explicitly modular;
it must not be interpreted as an ordinary mean. An absent or malformed observed
integer maps to zero. Every valid schema integer with a nonzero high word also
maps to zero; ordinary seeded parameters are nonnegative U32 values.

`ClientProof.bend` is universal in context, arguments, valid state and execution
fuel. It proves the access law for every prefix and outcome, including failed
operations and refusal, using the standard trace/termination lemmas. Its `Safe`
induction bounds the Action chain by five constructors (three reads, one write,
one finish); the official structural termination checker additionally checks
all recursive numerical functions. The existing checked finalizer enforces
structure, canonical state and response size limits, and publication. Both
official checkers admit the complete sealed Book before compilation/CUDA.
The certificate proves access safety and termination, not a theorem of the
numerical formula's statistical properties or compiler/GPU correctness.

CPU-only validation (caller holds the shared heavy lock):

```
python3 -B applications/simulation/check.py
```

This check also runs in `make test`. `make test-gpu` compares CPU one worker,
CPU sixteen workers and CUDA against a scalar Python oracle and exact complete
published states, rejects a cross-user write before compilation/CUDA, and
observes successful real launches through the existing forwarding interposer.
The application uses the ordinary prepared protocol with its universal proof;
see `tests/service/test_simulation.py` for a complete session.

`make benchmark-simulation` acquires the common lock and fixes CPU policy using
`paper/bench/fixed-clock.sh`. It measures complete prepared requests separately
from preparation, plus in-database PostgreSQL PL/pgSQL and SQLite recursive SQL,
with a NumPy oracle at each size. No Python SQL UDF is used. PostgreSQL uses the
same extracted package and cluster helper as E3; provide `pg` and `python`
under `.build/paper-bench` as described by the paper benchmark setup. The raw
results and fairness limitations are in `paper/evidence/simulation.json` and
`paper/evidence/simulation.md`. The CUDA corpus is 512 MiB; GPU clock is not
fixed and the device also drives the desktop. No engine/toolchain code changed.
