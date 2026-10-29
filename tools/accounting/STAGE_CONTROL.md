# Stage control ABI1 — N1 opt-in

`--stage-control` is additive and does not imply `--service-window`. Without
stage_arm, generic accounting keeps its existing protocol; without the option
no control page is acquired. Counter120/window280/deadline.h33acf/counter.c8dda
and op6 remain literally unchanged. This component does not activate the service
or confer memory coverage, K, MedicaoReal, Lei2 or Contrato. INCOMPLETE persists.

## Installation and identity

The observer creates and maps a separate4096-byte memfd before its first self
scan/baseline. The whole exposed mapping is counted, including bootstrap and
all aliases; there is no free supervisor. It exports only its descriptor as
JAYDB_ACCOUNTING_STAGE_FD. No Nat, fuel or budget is transported in environment.
The Python wrapper maps a read-only alias via the C runtime. Observer self-scan
and shared-object/offset union prevent charging it twice. Helpers may close
this FD; they remain observed by PID. The host's existing closefrom3 does so.

The page has an atomic u64 sequence followed by22 atomic u64 receipt words:
184 bytes of protocol inside the4096-byte mapping. Only the observer writes.
This is the trusted host API, not a sandbox against deliberate arbitrary memory
writes by the host/other privileged participants. External mutation/input and
full entry closure remain obligations in PROFILE_V5_PLAN.

The new header is native/accounting/stage_control.h. Request80 bytes:
abi/stage u64; scope_id/generation/start_ns/deadline_ns each {lo,hi}u64.
Receipt176 bytes: abi/error/state/stage u64; scope_id/generation/start_ns/
deadline_ns/observed_ns/arm_sequence/recovery_sequence u128; owner_pid/owner_mm/
pending_flags/cancellations u64. All fields use native Linux x86_64 layout.
Static asserts check80/176/184 and lock-free atomic words. Absolute instants use
the existing u128 CLOCK_MONOTONIC domain; this is not a public memory/fuel quota
or a restriction on arbitrary Nat budgets. There is no narrowing/rounding of a
request inside the protocol. Integrating public Nat→physical epoch remains the
host's existing domain/proof obligation, not discharged by this component.

## C and Python calls

C exports jaystage_arm(request,out), jaystage_retire(request,out),
jaystage_read(page,out), jaystage_map(fd,&page), jaystage_unmap(page).
Calls return positive errno; raw inline jaystage_raw_call is the matching
leaf handshake. It clears RDI after validation, on supported/unsupported/error
and null-argument paths, with a return dependency and caller-saved clobber.
This does not certify a separate caller's private raw syscall wrapper.

Python: from tools.accounting.stage import StageControl, Request. Construct
StageControl(Library(path)), read the real ACTIVE scope_id using the counter
API, and supply Request(scope_id,generation,stage,start_ns,deadline_ns).
arm()/retire() return immutable Receipt; read() reads only control state. close()
unmaps the alias and closes its duplicated FD. No method supplies CompleteMem.
The host must check both status and receipt state. An accepted arm with an
already expired original deadline can return EXPIRED_RECOVERED after real
reconciliation; accepting the request never means the deadline is future.

Handshake uses getpid with a DISTINCT token0x4a41595354414731, output pointer in
RSI, ARM1 or RETIRE2 in RDX and request pointer in R10. It is recognized only in
opt-in mode. The observer authenticates the actual root task/TGID (not a PID
claimed by input), checks recorded mm identity on retire, copies the complete
request with all tracees stopped, and checks ACTIVE scope and generation.
Only real syscall-exit after validated scans delivers the control reply.
There is no new operation on the old marker token or old page layout.

First generation must be positive. Later accepted generations strictly grow.
ARM requires IDLE or RETIRED; stale generation yields ESTALE, unresolved/current
stage EBUSY. For each (scope,stage), start and deadline are retained in an
unbounded-by-policy linked metadata ledger; a later generation cannot renew
that origin (EPERM). All metadata slabs are real counted backing. Retire must
match the accepted scope/generation/stage/start/deadline and owner mm; it does
not close a window. Window-close returns EBUSY while this opted-in stage is
unretired. Scope mismatch/closed scope yields ESTALE; no fake ACTIVE→CLOSED.

## Timer, cancellation and real recovery

States:0 IDLE,1 ARMED,2 EXPIRED_PENDING_RECOVERY,3 EXPIRED_RECOVERED,4 RETIRED.
observed_ns is a real expiry clock value only when cancellations is nonzero.
A retired receipt preserves that original value; it is never restamped on read.
arm_sequence is the last validated publication at arm, not a new memory fact.
recovery_sequence identifies the genuine subsequent validated recovery scan.

The timer uses the minimum of original stage and marker deadlines. deadline_tick
works in automatic stop_world/scans/waits without deadline_task. now>=deadline
expires; large u128 instants outside physical time_t do not install an earlier
timer or clamp the budget. A zero timer wake uses1ns only because POSIX zero
means disarm; comparison and receipt retain the original0. The opt-in wait loop
blocks SIGALRM/SIGCHLD around WNOHANG and atomically waits with sigsuspend, avoiding
a lost one-shot alarm between clock test and blocking. SIGCHLD wake setup is
observer-local. V11 captures the complete prior SIGCHLD action in the same
sigaction call that installs the observer wake. Only the fork child restores
that action, after the bootstrap gate and before execvp; failure exits126
without launching the root. The observer keeps its wake handler. Normal Linux
exec preserves SIG_IGN and resets caught handlers, flags and action masks;
no old handler pointer is installed after exec. The inherited process mask is
untouched by this restoration. See RETENTION_V11.md for the causal V10 repair,
including the passive opt-in case. No global setting is changed.

Signals only set a flag. Cancellation occurs at safepoints outside lifecycle
transactions and counter/receipt publication. collect stores the real result
and applies ownership before cancellation may escape. This matters because a
stage timer, unlike a marker-only timer, is armed while arbitrary helper exits
are collected. The final pre-publication safepoint forces a real clock check.
No bound is claimed for OS preemption between check/store or a critical syscall.

On expiry the receipt records the real original clock comparison and PENDING.
The partial region/retention scan bank is rolled back in O1, scan_fd is closed,
caches are dirty, and committed syscall results/ownership are preserved. No
partial snapshot/current/peak/time/sequence is published or fabricated. The
ACTIVE window remains ACTIVE. Existing published values are historical only.

**Chosen conservative return path:** cancellation retries real reconciliation
and a fresh validated scan through the normal serialized scheduler. It does not
immediately release Python or peers from a stale bank. The stage alarm is then
expired, not renewed; the original epoch/expiry receipt stays fixed. The recovery
scan has no demonstrated K bound. This limitation includes a costly repeat scan,
not only exceptional metadata cases; N1 is not a hard K solution.

PENDING bits:1 in-flight/queued non-owner memory operation,2 borrowed vfork mm,
4 essential metadata,8 hold,16 discarded/in-progress scan,32 task not stopped.
A receipt becomes EXPIRED_RECOVERED only after a real validated snapshot and
all these checks are clear. It means observer reconciliation, NOT that every
helper has been cleaned up, public timeout completed, or memory became complete.
Real helper cleanup remains the host's responsibility. Retire performs another
real handshake and cannot hide these pending transitions. op6 remains the old
scan-free release and can release a held owner; recovery still requires a scan.

If essential metadata becomes irrecoverable inside an opted-in armed/pending
lifecycle transaction, the observer preserves the transaction and cached real
return, emits unrecoverable_metadata and parks this instance. Its real timer
can still produce EXPIRED_PENDING_RECOVERY. It emits no later memory snapshot
or summary and does not internally kill the DB. This is intentionally an
unresolved/no-progress frontier, not a new public error, FalhaReal, Processavel
veto, or successful recovery. External teardown is needed if no real recovery
exists; the diagnostic test's explicit external harness cleanup is not a DB fact.
Generic mode keeps V9's negative boundary behavior. No arbitrary missing value
is replaced by0 or inferred death.

## Integration limits

This file implements N1 only. It does not produce Concluiu, delivery, cleanup,
window abandonment or a public limit response. Retire never resets retention,
forgets a committed return, discards a surviving owner or opens a new window.
The proof PreparacaoTemporal now integrated by ROOT can justify Preparou of the
original fixed temporal error without complete memory, given the real temporal
event and MedicaoReal. It does not satisfy an earlier AlocouCampo or prove this
control receipt is that event. Existing service commit gates remain untouched.

Full physical K, report-I/O blocking, bounded recovery/thaw/cleanup/delivery, adapted leases,
TOCTOU/external writers, imported/special/hugetlb backing, generic faults/COW/
invalidation, irreversible metadata loss/PID namespaces, bootstrap/kernel order,
full startup/dependency/FD/env closure, Campo/SemCtx/host remain INCOMPLETE.
Service V6's ROOT-owned deliver retry correction is a separate delta from the
V5 profile plan, with unchanged helper/process ABI; no CLOSURE was recaptured.
