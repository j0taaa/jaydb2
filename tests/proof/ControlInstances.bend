import Base
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../contract/PreparedProtocol.bend as W
import ../../contract/PreparedRegistry.bend as G
import ../../contract/Theorems.bend as T
import ../../contract/Logic.bend as L
import ../../contract/Requirements.bend as R
import ../../contract/Semantics.bend as S
import ../../src/Control.bend as C
import ../../proof/ControlClauses.bend as Proof
import ../../proof/ControlHistory.bend as History
import ./Controls.bend as X
import ./Instances.bend as Instances
import ./WrongSteps.bend as Wrong
import ../../src/Dispatch.bend as Dispatch
import ../../src/Input.bend as Input

def handle() -> String: "0000000000000000000000000000000000000000000000000000000000000000"
def registry() -> C.Registry: C.ControlRegistry{Nil{}, Nil{}}
def admission() -> C.Admission: C.ControlUniversal{"controls", "refuse", "certificate"}
def entry() -> G.Entry: G.Entry{"controls", handle(), "refuse", "certificate", False{}, ""}
def request() -> P.Request: P.Request{"token", "refuse", D.VAbsent{}, "certificate"}
def invalidation() -> P.Request: P.Request{"token", handle(), D.VAbsent{}, ""}

# Same small no-law configuration as the transaction non-vacuity fixture.
def safe(+ctx: D.Context, +args: D.Value, +s: D.State, n: Nat) ->
  R.SafetyTrace(S.execute(n, X.program(), D.Schema{Nil{}}, s, ctx, args),
    X.configuration(), s, ctx, "refuse", args):
  match n:
    case 0n: L.Both{Unit{}, Unit{}}
    case 1n+0n: L.Both{L.Both{Unit{}, Unit{}}, L.Both{Unit{}, Unit{}}}
    case 1n+1n+k: L.Both{L.Both{Unit{}, Unit{}}, L.Both{Unit{}, Unit{}}}

def sound() -> T.ControlAdmissionSound(X.configuration(), admission()):
  (X.program(), L.Both{+ctx => +args => +s => valid => identity => n => safe(ctx, args, s, n),
    +s => ctx => args => (1n, s, Nil{}, S.Response{S.Refusal{}, D.VAbsent{}}, {==})})

def prepare_plan() -> C.Plan:
  C.routed(S.limits(X.configuration()), "controls",
    Dispatch.Routed{3, Input.InputReady{X.seed(), request()}}, registry(), admission(), handle())

def registered() -> C.Registry: C.apply(C.ControlAdd{entry()}, registry())

def invalidate_plan() -> C.Plan:
  C.routed(S.limits(X.configuration()), "controls",
    Dispatch.Routed{5, Input.InputReady{X.seed(), invalidation()}}, registered(), C.ControlUnaccepted{}, handle())

def bytes(receipt: W.Receipt) -> List<&2, U32>:
  Maybe.default(&2, List<&2, U32>, W.frame_receipt(receipt), Nil{})

law prepare_exact:
  {prepare_plan() == C.ControlReady{X.context(), C.ControlAdd{entry()}, W.PreparedReceipt{handle()},
    bytes(W.PreparedReceipt{handle()})} : C.Plan}
def prepare_exact(): {==}

law invalidate_exact:
  {invalidate_plan() == C.ControlReady{X.context(), C.ControlRemove{"controls", handle()},
    W.InvalidatedReceipt{}, bytes(W.InvalidatedReceipt{})} : C.Plan}
def invalidate_exact(): {==}

law reused_handle_denied:
  {C.admitted(S.limits(X.configuration()), "controls", True{}, X.context(), "controls", handle(),
    C.apply(C.ControlRemove{"controls", handle()}, registered()), request()) == C.ControlDenied{S.Failure{}} : C.Plan}
def reused_handle_denied(): {==}

law foreign_invalidation_denied:
  {C.invalidating(S.limits(X.configuration()), "other", True{}, X.context(), "other", registered(), handle()) ==
    C.ControlDenied{S.Failure{}} : C.Plan}
def foreign_invalidation_denied(): {==}

law denial_preserves_registry:
  {T.next_registry(C.finish(C.ControlDenied{S.Authentication{}}, X.seed(), [1, 2], registered())) ==
    registered() : C.Registry}
def denial_preserves_registry(): {==}

law receipt_before_mutation:
  {T.next_registry(C.finish(C.receipt(S.Limits{1024n, 1024n, 64n}, "controls", X.context(),
    C.ControlAdd{entry()}, W.PreparedReceipt{handle()}), X.seed(), [1, 2], registry())) == registry() : C.Registry}
def receipt_before_mutation(): {==}

def body(op: W.Operation, request: P.Request) -> List<&2, U32>:
  Maybe.default(&2, List<&2, U32>, W.encode_body(W.Extension{op, request}), Nil{})

law all_control_clauses:
  for k: T.ControlClause
  T.ControlAt(X.configuration(), k, X.seed(), [1, 2], registry(), body(W.Prepare{}, request()), admission(), handle())
def all_control_clauses(k):
  Proof.control_theorem()(k, X.configuration(), X.seed(), [1, 2], registry(), body(W.Prepare{}, request()), admission(), handle())

def mixed_run() -> T.ServiceRun<X.configuration(), X.seed(), registry()>:
  T.ServiceControl{body(W.Prepare{}, request()), admission(), handle(), sound(),
    T.ServiceTransaction{X.request(), Wrong.accept, X.seed(), Instances.controls_oracle_sound,
      T.StepRan{X.context(), X.program(), 1n, X.seed(), Nil{}, S.Response{S.Refusal{}, D.VAbsent{}},
        Instances.refused(), Instances.refused_bytes(), {==}, {==}, {==}, {==}},
      T.ServiceControl{body(W.Invalidate{}, invalidation()), C.ControlUnaccepted{}, handle(), Unit{},
        T.ServiceEnd{}}}}

law mixed_fold:
  for j: Nat
  T.ServiceAt(j, X.configuration(), X.seed(), registry(), mixed_run())
def mixed_fold(j):
  L.and_left(T.ServiceAt(j, X.configuration(), X.seed(), registry(), mixed_run()),
    L.E<T.RegistryLookupTheorem(), L.E<T.RegistryInvalidationTheorem(), L.E<T.ServiceLifetimeTheorem(), T.ServiceNoRevivalTheorem()>>>,
    History.service_fold_theorem()(X.configuration(), X.seed(), mixed_run(),
      Instances.controls_configured(), X.seed_valid(), j))

# A revoked handle stays absent through a repeated prepare attempt and another
# invalidation. The generic theorem also covers arbitrary interleaved calls.
def revoked_registry() -> C.Registry:
  C.apply(C.ControlRemove{"controls", handle()}, registered())

def retired_run() -> T.ServiceRun<X.configuration(), X.seed(), revoked_registry()>:
  T.ServiceControl{body(W.Prepare{}, request()), admission(), handle(), sound(),
    T.ServiceControl{body(W.Invalidate{}, invalidation()), C.ControlUnaccepted{}, handle(), Unit{},
      T.ServiceEnd{}}}

law revoked_handle_never_revives:
  for j: Nat
  T.RevokedAt(j, "controls", handle(), X.configuration(), X.seed(), revoked_registry(), retired_run())
def revoked_handle_never_revives(j):
  History.service_no_revival_theorem()(X.configuration(), X.seed(), revoked_registry(), "controls", handle(),
    retired_run(), {==}, {==}, j)
