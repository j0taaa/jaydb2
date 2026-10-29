# Accounting V10 — original-stage deadline control, N1

This adds opt-in --stage-control, versioned request80/receipt176/page4096,
read-only host aliases, authenticated all-stop handshake and timer coverage of
automatic stop_world/scan/waitpid without requiring marker_until. See
STAGE_CONTROL.md for API, states, conservative recovery and explicit N2/K limits.
No service/host/admission/native-outside-accounting/proof changes are included.

The V5 profile causal matrix and its JSON were written BEFORE production edits
as new PROFILE_V5_PLAN.md/JSON. Their references remain V9/V5, not a recaptured
closure of concurrent ROOT work. The later authorization was for N1 only.
ROOT's serviceV6 fixed partial-write retry in deliver separately; it still
uses accountingV9 frozen dependency and grants no runtime profile ratification.

Counter120/window280/deadline.h33acf/counter.c8dda/op6 stay literal. V3–V9,
original18, all prior history/CLOSURE/SOURCES remain unchanged. RESULTS_V9_86.json
and AST_V9_86.json preserve the old result/methods before the new build. All86
old methods remain identical. New tests are in separate test_stage.py.

Expiry rolls back only the partial scan bank. Real syscall results and lifecycle
ownership finish atomically before a cooperative jump. A subsequent REAL scan
and cleared pending flags qualify EXPIRED_RECOVERED; no memory complete flag is
introduced. A remaining hold/vfork/in-flight/essential-metadata condition stays
pending. Irrecoverable metadata parks the opted-in instance without internally
killing DB or publishing a partial snapshot; this is a negative, not recovered
progress. The default generic V9 negative boundary is unchanged.

Diagnostics are separate test_races/metadata ELFs. Tests use real monotonic time,
actual wait/scans, actual lease release and SIGKILL/EXIT/ptrace ESRCH. They never
mock clock/results/errno or alter global settings. Real leases in the in-flight
control are held/released by the test's own local broker, not an external service;
its backing is outside that diagnostic observed tree, and no complete memory is
claimed. Explicit harness kill of a deliberately pending negative is cleanup,
not external FalhaReal or a public timeout witness.

The stage tests distinguish real recovery, pending until actual release/EXIT,
and irrecoverable pending without progress. Page aliases do not add a second
charge; the page is included in baseline1 before fork. New effective inline
cleanup is tested O2/O3 and with immediate register capture/ordinary getpid after
success/error/outside/null paths. Existing token/op6/deadline tests remain intact.

All production observations/peaks/windows still INCOMPLETE. No MedicaoReal,
K, full Lei2/Contrato, selected-runtime closure or service activation is granted.
Physical K and the latency of an unguarded recovery retry remain open even in
otherwise qualified paths. PreparacaoTemporal is a separate mathematical
component from ROOT and proves Preparou only; no service completion patch here.

Final method/record/build/extraction counts and hashes are in the new V10
manifest, validation and evidence index; intermediate logs retain their actual
source-phase attribution. A NEW independent task from ROOT is required after
delivery. This front does not initiate a review.
