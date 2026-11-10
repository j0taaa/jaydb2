# Transaction and metadata conclusions share one exact source-derived result.
# Both alternatives of ConclusionAt are inverted; no receipt-only shortcut
# hides a second transaction conclusion or a later full-source event.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ./EventObserver.bend as O
import ./PreparationCurrent.bend as PSource
import ./ObservationUniqueness.bend as U
import ./PreparationUniqueness.bend as A

def ConclusionMatches(-outcome: E.Outcome, -state: D.State, -closing: Bool, actual: U.View) -> Type:
  match actual:
    case U.ConclusionView{other, other_state, other_closing}:
      L.E<{other == outcome : E.Outcome}, L.E<{other_state == state : D.State}, {other_closing == closing : Bool}>>
    case _: Unit

def conclusion_payload(-outcome: E.Outcome, -state: D.State, -closing: Bool,
  -other: E.Outcome, -other_state: D.State, -other_closing: Bool,
  same: {U.ConclusionView{other, other_state, other_closing} == U.ConclusionView{outcome, state, closing} : U.View}) ->
  L.E<{other == outcome : E.Outcome}, L.E<{other_state == state : D.State}, {other_closing == closing : Bool}>>:
  %Equal.sym(U.View, U.ConclusionView{other, other_state, other_closing}, U.ConclusionView{outcome, state, closing}, same) : ConclusionMatches(outcome, state, closing, _)
  L.Both{{==}, L.Both{{==}, {==}}}

def conclusion_result(-at: Nat, -outcome: E.Outcome, -state: D.State, -closing: Bool,
  -other: E.Outcome, -other_state: D.State, -other_closing: Bool,
  result: L.E<{at == 11n : Nat}, {U.ConclusionView{other, other_state, other_closing} == U.ConclusionView{outcome, state, closing} : U.View}>) ->
  L.E<{at == 11n : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{other_state == state : D.State}, {other_closing == closing : Bool}>>>:
  match result:
    case L.Both{time, payload}: L.Both{time, conclusion_payload(outcome, state, closing, other, other_state, other_closing, payload)}

def conclusion_state_transport(-at: Nat, -outcome: E.Outcome, -state: D.State, -closing: Bool,
  -other: E.Outcome, -database: D.State, -other_state: D.State, -other_closing: Bool,
  same: {database == other_state : D.State},
  result: L.E<{at == 11n : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{database == state : D.State}, {other_closing == closing : Bool}>>>) ->
  L.E<{at == 11n : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{other_state == state : D.State}, {other_closing == closing : Bool}>>>:
  %same : L.E<{at == 11n : Nat}, L.E<{other == outcome : E.Outcome}, L.E<{_ == state : D.State}, {other_closing == closing : Bool}>>>
  result

def returned_conclusion_is_unique(~binding: Source.Source, ~public: List<&2, Source.FileSource>, ~c: S.Configuration,
  ~seed: Unit -> D.State, ~pi: String, ~artifacts: H.Artifacts, ~instance: String,
  ~world: Nat, ~input: X.Reception, ~mode: V.Mode, ~raw: P.Request, ~context: D.Context,
  ~handle: String, ~seal: String, ~bytes: List<&2, U32>, ~send: V.SendReturn,
  +at: Nat, other: E.Outcome, +state: D.State, +closing: Bool,
  authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>},
  fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool},
  frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>},
  concluded: E.ConclusionAt(O.environment(binding, public, c, seed, pi, artifacts,
    PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance), Source.artifact(binding),
    I.Serve{world, c, seed(Unit{}), input}, at, other, state, closing)) ->
  L.E<{at == 11n : Nat}, L.E<{other == E.Receipt{W.PreparedReceipt{handle}} : E.Outcome}, L.E<{state == seed(Unit{}) : D.State}, {closing == False{} : Bool}>>>:
  match other:
    case E.Transaction{+response}:
      conclusion_result(at, E.Receipt{W.PreparedReceipt{handle}}, seed(Unit{}), False{}, E.Transaction{response}, state, closing,
        U.actual_observation_inherits_only_the_derived_source_uniqueness(binding, public, c, seed, pi, artifacts,
          PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
            V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance, 3n, 8n,
          U.ConclusionView{E.Receipt{W.PreparedReceipt{handle}}, seed(Unit{}), False{}}, I.Serve{world, c, seed(Unit{}), input}, at,
          E.PreparedKernel{I.Concluded{response, state, closing}}, U.ConclusionView{E.Transaction{response}, state, closing},
          A.source_all_plain(world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.run(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
            V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})),
          A.actual_conclusion_tag(c, binding, public, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, context, handle, seal, bytes, send, authenticated, {==}, fits, frame),
          Unit{}, {==}, {==}, concluded))
    case E.Receipt{+receipt}:
      match concluded:
        case (result, (+snapshot, L.Both{observed, state_same})):
          conclusion_state_transport(at, E.Receipt{W.PreparedReceipt{handle}}, seed(Unit{}), False{}, E.Receipt{receipt}, E.database(snapshot), state, closing, state_same,
            conclusion_result(at, E.Receipt{W.PreparedReceipt{handle}}, seed(Unit{}), False{}, E.Receipt{receipt}, E.database(snapshot), closing,
              U.actual_observation_inherits_only_the_derived_source_uniqueness(binding, public, c, seed, pi, artifacts,
                PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
                  V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance, 3n, 8n,
                U.ConclusionView{E.Receipt{W.PreparedReceipt{handle}}, seed(Unit{}), False{}}, I.Serve{world, c, seed(Unit{}), input}, at,
                E.ReceiptConcluded{receipt, result, snapshot, closing}, U.ConclusionView{E.Receipt{receipt}, E.database(snapshot), closing},
                A.source_all_plain(world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, V.run(c, mode, raw, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}},
                  V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})),
                A.actual_conclusion_tag(c, binding, public, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw, context, handle, seal, bytes, send, authenticated, {==}, fits, frame),
                Unit{}, {==}, {==}, observed)))

law actual_successful_preparation_derives_unified_conclusion_uniqueness:
  for ~binding: Source.Source
  for ~public: List<&2, Source.FileSource>
  for ~c: S.Configuration
  for ~seed: Unit -> D.State
  for ~pi: String
  for ~artifacts: H.Artifacts
  for ~instance: String
  for ~world: Nat
  for ~input: X.Reception
  for ~mode: V.Mode
  for ~raw: P.Request
  for ~context: D.Context
  for ~handle: String
  for ~seal: String
  for ~bytes: List<&2, U32>
  for ~send: V.SendReturn
  for authenticated: {D.authenticate(seed(Unit{}), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  E.ConclusionUnique(O.environment(binding, public, c, seed, pi, artifacts,
    PSource.source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance), Source.artifact(binding),
    I.Serve{world, c, seed(Unit{}), input}, 11n, E.Receipt{W.PreparedReceipt{handle}}, seed(Unit{}), False{})
def actual_successful_preparation_derives_unified_conclusion_uniqueness(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, context, handle, seal, bytes, send, authenticated, fits, frame):
  at => other => state => closing => observed =>
    returned_conclusion_is_unique(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, context, handle, seal, bytes, send,
      at, other, state, closing, authenticated, fits, frame, observed)
