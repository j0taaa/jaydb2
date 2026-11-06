# Verified performance improvements

The original ten-scenario benchmark is retained unchanged as a historical
report. This follow-up starts from engine revision `441f807` plus that saved
suite and uses separate frozen baseline/candidate checkouts. Final repeated
results and release-check evidence will be recorded here after completion.

## Implemented changes and preserved behavior

The original `Bytes.nat64` converts a natural through one predecessor step per
unit. `Input.parts` previously performed that conversion on the configured
state and message ceilings in every authentication and execution worker. The
8 MiB ceiling therefore caused millions of conversion steps even with tiny
stored data. The benchmark keeps that same ceiling.

`FastBytes.nat64_checked` uses the official U32 conversion and an exact natural
roundtrip guard. Values through `U32::MAX` use the short native path; larger
values try a two-word candidate checked against its exact fixed-width natural
measure. Values outside these guarded paths use a tail-recursive conversion.
The checked shortcuts and tail fallback are proved equal to the original for every natural,
including overflow. No arithmetic axiom, compiler change, truncated comparison,
cached answer or smaller logical limit is introduced.

`OptimizedInput` changes only the conversion used in input composition. Checked
theorems establish exact equality of parts, decode, analyze and private
authentication output to the original input machine for every packet, schema
and limits, without valid-input or credential assumptions. Native ordinary,
prepared and read-only entries use this equivalent input route. The original
contract and eight-law model functions remain unchanged. Rust, Node, C, the
official compiler/runtime, OS and storage assumptions retain their documented
trusted-boundary status.

Explicitly read-only-certified prepared requests now use the existing pinned
durable-root path with one reader as well as multiple readers. This remains
serial with one reader. It preserves fresh authentication, sealed artifacts,
native execution, changed-state rejection, response pairing and FIFO barriers.
Ordinary and write-capable requests retain their original publication path.

An additional `single-call-queries-v1` application profile executes generic SUM
and child-parent JOIN inside one certified transaction instead of nine or
seventeen requests. Actual key lists drive both traversal and termination;
there is no eight-row bound or cached data. Its Reader and validation program
have genuine read-only certificates; SUM/JOIN retain ordinary admission with
actual-state termination. All six program preparation costs remain measured.
This profile is reported separately from the engine-only comparison.

## Validation status

Focused proofs pass both official modes, including the complete existing
contract/implementation/library proof aggregate. Rust unit checks, exact-type
benchmark comparisons and application-wrapper unit checks pass. Full native,
durability/recovery, application and release validation are queued behind the
frozen baseline benchmark. No final performance or regression conclusion is
claimed until those checks and the candidate measurements complete.

The benchmark is now discoverable from the repository README, has Make targets,
and runs fixture/comparator checks in smoke and full CI. The comparison reports
every scenario/workload and setup result, with configurable noise and regression
thresholds; it does not invent an aggregate score or hide losses. Passing finite
tests and a sampled gate cannot establish absence of every possible regression.
