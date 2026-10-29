# Retention V11: SIGCHLD inheritance at exec-root

V10-NEW-01 is a local launch regression: passive --stage-control installed an
observer SIGCHLD wake before forkroot. Exec then reset the inherited caught
action to DFL, losing an originally ignored disposition. This changes waitpid
semantics even without a stage arm or service-window. DB reachability was not
established by the review; its DFL requirement does not excuse the generic bug.

## Design and implementation

The installing sigaction now captures the entire previous action, including
handler, flags, action mask and libc restorer representation. Its real failure
still follows the existing setup error path. In the fork child, after the
bootstrap gate and ptrace attachment and immediately before execvp, a checked
sigaction restores the saved action. A real restore failure exits126 without
exec; no fallback substitutes DFL. The observer retains its wake handler and
timer/wait machinery. No process mask operation is added. No restore is done
in the new executable, where an old caught-handler address would be invalid.

Linux exec itself preserves IGN, resets caught handlers to DFL and clears
action flags/masks. The C launch controls compare direct exec with generic and
passive observation rather than assuming that pre-exec action flags should
survive exec. The upstream Linux v7.0 kernel/signal.c flush_signal_handlers and
fs/exec.c begin_new_exec are explanatory primary sources; the evidence retains
the exact bounded web read after direct download returned HTTP429. This is not
a claim of full provenance for the running distribution kernel. Real local
controls establish the observed boundary on this machine.

Production changes are limited to deadline.inc.c and trace.c. Counter120,
window280, deadline.h33acf, counter.c8dda, op6 and stage ABI1 are unchanged.
No service activation, public category, deadline, epoch or quota is introduced.
Generic mode without --stage-control takes no new sigaction path.

## Causal evidence and validation

The immutable V10 was extracted and rebuilt before editing production. Fourteen
own runs of the literal independent fixture reproduced the IGN-to-DFL defect,
with/without a report and service-window, and confirmed preserved process masks.
The official new V10 REPORT/COMMANDS/REVIEW_EVIDENCE, runners, fixtures and index
were read;348 indexed entries and307 retained texts were verified. The307 texts
plus their retained index are copied literally into tests/accounting/review_v10.
The official report is c90f7c2002db5687ec62d545a2b45cb5a6d88b4d8c7b944b5f18d1b68cc557b5.
Its review results are attributed to the reviewer, not counted as our executions.
The earlier partial review is not substituted for this official result.

Five additive test methods exercise53 process executions:8 literal fixture mask
controls,6 literal no-window/no-report repeat controls,36 C-launch executions
(12 direct,24 observed), one separate diagnostic restore failure and2 missing
exec controls. C-launch covers DFL/IGN/caught handlers, CHLD/USR1 independently
blocked, and action flags/masks across real exec. The failure diagnostic ELF
issues a real rt_sigaction with an invalid userspace pointer and observes
EFAULT; production has no injected path. It checks exit126 and no root payload.

The unchanged86 legacy methods and16 N1 methods remain separate suites; their
V10 result files and method ASTs are preserved in history. The V11 manifest and
validation sidecar record only actually completed canonical and extracted runs,
source/build equality, report provenance and checksums. Earlier V10 before-runs
and first V11 development runs remain distinctly labeled in evidence.

## Limits

This repair establishes the launch signal boundary, not complete accounting.
INCOMPLETE remains. N2, K, potentially unbounded recovery retry/report IO,
irretrievable metadata, adapted leases, external writers/path/open_how TOCTOU,
imported/special/hugetlb backing, genericfault/COW/invalidation, static bootstrap
and ordering, full init/FD profile, Field/SemCtx and host remain open. No scope
is closed by fictitious scan; no memory observation is inferred from a temporal
receipt. N1's pending states and conservative hold/vfork/in-flight behavior are
unchanged. No CLOSURE or service/native/proof snapshot is updated by V11.

Service V7 uses its own frozen V9 counter dependency. ROOT's seven isolated entry
scenarios are research, not a full profile or closure. V11 is delivered for a
NEW independent review task initiated by ROOT; the author starts no review.
