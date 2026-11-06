# Project review and verification status

Review started from merged `main` revision `1598ed4`. The earlier integration
and accessory records remain historical evidence; this review did not rewrite
their results or change any active/historical contract file or manifest.
The reviewed repairs and new proofs are recorded in commit `0552c76`.

## Validated repairs

| Finding | Repair and causal evidence |
| --- | --- |
| TypeScript calls could remain pending after silent request-pipe closure or attachment after response EOF | Observe terminal request-pipe events and already closed streams. Bounded before/after probes reproduce the hangs and their repair. |
| The demo watchdog began after a blocking request write | Nonblocking partial writes now share the existing adapter request/response deadline. A real nonreading subprocess and 4 KiB pipe reproduce the defect; a live-reader control receives exact bytes. This changes the demo adapter, not database deadlines. |
| Repeated workload arguments could overwrite paired benchmark records | Reject duplicate iteration counts before creating outputs or starting measurement. The regression requires this diagnostic specifically. Old measurements are unchanged. |
| Default library verification omitted receipt helpers and law templates | Import both `Receipts` and `ReceiptLaws` directly in `library/VERIFY.bend`. |
| Future core/library modules could miss the checked roots unnoticed | `make verify` now checks the transitive local import graph and rejects orphaned `src`, `proof` or `library` modules. Controls cover transitive inclusion, three orphan areas, missing imports, unsupported syntax and outside-root paths. |
| Key roundtrip theorem covered internal chosen fuel but not the public decoder | Constructively derive sufficient fuel from the actual encoded string length, then prove `decode(encode(parts)) == Some(parts)` for every finite list. An always-None decoder fails at its intended proof obligation in both official modes. |
| Structural comparison and signed-order properties lacked general helper theorems | Optional `ComparisonProofs` proves structural equality soundness/completeness and actual signed-comparison strict total order. Constant-true equality and constant-false order controls fail at the intended obligations. Runtime helper code/imports remain unchanged. |
| Prepared-wire mismatch was documented without a direct checked exclusion theorem | `PreparedPrograms` now proves tag-7 exclusion from ordinary request encodings, `RequestReceived`, and ordinary authentication justification for the same raw scenario. A forged encoding control fails in both modes. |

The import inventory reaches all **16 source, 132 proof and 22 library modules**,
209 transitive modules in total. It detects omitted checking; it does not
establish an unstated functional theorem about every imported function.
Application/generated roots, deliberately rejected fixtures, native effects and
historical experiment variants have their separately documented scopes.

Independent passes covered host framing/process ownership, persistence,
scheduling, prepared admission, native effects, source freezing, library
algorithms/application certificates, TypeScript and Python framing, the web
adapter, and benchmark provenance. No additional demonstrated defect in the
ordinary-core proof construction was found. Existing algorithms and archived evidence were retained where
removing or replacing them had no validated benefit.

## Completed checks and current gate

- Baseline `make verify-integration`: both official modes and all eight
  aggregate negative controls passed.
- Final amended library aggregate and public key theorem: both modes passed.
- Library false arithmetic, hidden-write, public-decoder and comparison
  controls: ten intended rejections across both modes passed.
- Smoke: exit zero, including all 43 Rust tests, formatting, strict Clippy,
  TypeScript/package/accessory/starter checks and benchmark oracles.
- Real demo: seven tests passed. Native TypeScript integration: eleven checked
  ordinary/prepared responses passed.
- Article numbers: reconstruct all displayed throughput, burst median, pooled
  nearest-rank p95 and maximum sampled RSS values from the retained raw bursts.
  Verify unique burst identities, eight responses per burst, elapsed-time
  throughput and paired ratios before compiling the documents.
- `bash tools/ci/check.sh full`: **exit zero**, about 47 minutes. Its 436
  recorded source/test/configuration inputs remained unchanged throughout.
  This included the complete native/application/recovery/demo gate.
- Subsequent additions are proof modules, verification fixtures and the
  both-mode negative runner. Promoted `PreparedPrograms` and amended library
  aggregates passed both official modes; final `make verify-integration`
  passed against their combined roots, including all nine core negative
  controls in both modes. The earlier full native result is
  not relabeled as having run after these proof-only additions.

Current raw logs and manifests stay ignored under `.build/review/`, including
`full.log`, `full-inputs.json`, `full-result.json`, `promoted-proofs.log` and
`final-proofs.log`. No
compiled binaries, repeated historical outputs or page-render caches are added
to Git. See [verification.md](verification.md) for reproduction commands.
The small [validation summary](review-validation.json) retains the successful
exit statuses, evidence digests and exact scope of the proof-only follow-up.

## What remains unproved

The checked `ContractService.contract_of_service` target is exactly the unchanged
eight-law `LAWS.Contract` for the **ordinary serial service model**, conditional
on the explicit source/tool/communication premises. The
[integration contract](../proof/SERVICE_CONTRACT.md) identifies those premises.
It is not an unconditional proof of the complete executable.

Prepared raw/control frames, read-batch scheduling and persistence have narrower
pure results and explicit operational bridges. Their Rust/Node/C implementation,
official translations, IO, filesystem and hardware assumptions remain trusted.
Full concrete refinement of these boundaries remains a substantial proof task;
neither module reachability nor passing fault tests discharges it.

There is also a structural protocol boundary, not just an unfinished proof:
prepared bodies begin with tag `7`, outside the canonical value tags `0..6`.
The host strips that prefix before authentication (`server/main.rs`,
`SerialService.propose`). The unchanged `Interface.RequestReceived` instead
requires an ordinary request's canonical encoding to equal the actual received
body. For example, an authentication response to an invalid credential in such
a prepared body cannot satisfy `Interface.ResponseJustified(Authentication)`
for that raw ordinary scenario. Successful `prepared`/`invalidated` control
statuses are also outside the original `Semantics.Status` type.

Consequently, silently normalizing the raw bytes is not a proof of the original
whole-wire contract. The existing ordinary theorem remains useful within its
declared scope. A single contract covering the extensions would require an
explicit, approved contract extension, or a separately identified ordinary-only
artifact. Removing the prepared workflow would break existing clients; neither
that removal nor a law change was made during this review. This unresolved
decision prevents claiming the user's strongest whole-project proof goal is
complete.

A code-only migration can retain compile-once reuse under the original wire
contract: transmit exact ordinary source/proof on every execution and cache
universally certified sealed artifacts internally. Client-local handles can
expand to those ordinary requests. This is not equivalent to all current
prepared behavior: ahead-of-time server authentication/admission would move to
first execution, invalidation would become local forgetting/cache eviction,
old raw clients would need migration, and combined source/proof plus arguments
can exceed a message ceiling even when the previous separate preparation and
handle calls each fit. A generic no-op wrapper also cannot inherit arbitrary
administrator laws that distinguish the actual source/program/arguments.
Thus compile reuse itself is compatible with the laws; preserving every
existing prepared wire, lifecycle and size behavior simultaneously is not.
The review has not silently made these compatibility changes.

Optional arithmetic currently has implementation-word and sign-predicate
contracts plus extensive finite oracles. A separate interpretation over
mathematical integers, especially general multiplication/division correctness,
remains open. Broader join/group/business functional specifications also require
additional theorems. These stronger algorithm contracts are distinct from the
transaction authorization/publication laws; their absence alone does not refute
the existing conditional eight-law result. No result here is labeled
"100% proved for the entire project."

## GPU decision and TCC

Optional GPU execution is plausible for large explicitly parallel pure work.
The existing `experiment-gpu` heavy trial measured 715.124 ms CPU versus
215.706 ms CUDA, while its small control measured 5.756 versus 174.945 ms.
Those are historical branch results, two complete samples per case, with eight
CPU workers, one GPU-worker cap and a 512 MiB corpus on an RTX 3080 Ti. They do
not establish general database acceleration or a mainline integration.

Retaining CPU-only mainline avoids importing the old branch's missing
combinations: current read batches require GPU exclusivity; artifact sealing,
persistence identity, timing and failure behavior need combined validation.
Compiler/CUDA semantic preservation would still remain an explicit assumption.
The laws were not changed to accommodate GPU behavior.

The English [TCC and editable slides](../paper/README.md) identify Gabriel Jota
Lizardo and PUC Minas, document the actual proof boundary, and derive quantitative
results from existing raw evidence. Their article and sixteen-slide
PDFs are generated under `.build/tcc/output/`; only the small editable source
set is tracked. Rendered pages and an independent factual review were checked.
The specific course template, advisor and defense metadata remain for local
confirmation before submission.
