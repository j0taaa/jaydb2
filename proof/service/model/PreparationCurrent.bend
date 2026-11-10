# Concrete post-selection preparation source for the full Current theorem.
# Prefix selection is by take/drop of the ACTUAL phase renderer; the complete
# remaining phase suffix is still observed. This is a fresh-start/model branch,
# not a fabricated claim that a native checker accepted or an IO call succeeded.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedLaws.bend as H
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../../SourceService.bend as Source
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../phases/PrepareEvents.bend as A
import ./EventObserver.bend as O
import ./EventHistory.bend as T
import ./CurrentWitness.bend as C
import ./FrameBounds.bend as B

def phase_items(+world: Nat, +selected: D.State, +input: X.Reception, phases: List<&2, V.PreparationEvent>) -> List<&2, O.Item>:
  match phases:
    case Nil{}: Nil{}
    case Con{phase, rest}: Con{O.Item{world, selected, input, O.Preparation{phase}}, phase_items(world, selected, input, rest)}

def with_run(+world: Nat, +input: X.Reception, +before: E.Snapshot, run: V.PreparationRun) -> List<&2, O.Item>:
  Con{O.Item{world, E.database(before), input, O.Selection{before}}, phase_items(world, E.database(before), input, V.events(run))}

def source(~c: S.Configuration, world: Nat, input: X.Reception, +before: E.Snapshot,
  mode: V.Mode, raw: P.Request, returns: V.Returns) -> List<&2, O.Item>:
  with_run(world, input, before, V.run(c, mode, raw, before, returns))

def successful_prefix_coherent(+world: Nat, +input: X.Reception, mode: V.Mode, raw: P.Request, context: D.Context,
  +before: E.Snapshot, +entry: G.Entry, bytes: List<&2, U32>, send: V.SendReturn) ->
  T.Coherent(T.take(8n, with_run(world, input, before, A.success(mode, raw, context, before, entry, bytes, send))), before):
  match send:
    case V.SendPending{}:
      L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{L.Both{{==}, L.Both{{==}, {==}}}, Unit{}}}}}}}}}
    case V.SendComplete{}:
      L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{L.Both{{==}, L.Both{{==}, {==}}}, Unit{}}}}}}}}}
    case V.SendInterrupted{prefix}:
      L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{L.Both{{==}, L.Both{{==}, {==}}}, Unit{}}}}}}}}}

law the_actual_successful_preparation_prefix_derives_local_history_coherence:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +mode: V.Mode
  for +raw: P.Request
  for +before: E.Snapshot
  for +context: D.Context
  for +handle: String
  for +seal: String
  for +bytes: List<&2, U32>
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for fresh: {G.lookup(E.instance(before), handle, E.registry(before)) == None{} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.PreparedReceipt{handle})) == True{} : Bool}
  for frame: {W.frame_receipt(W.PreparedReceipt{handle}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  T.Coherent(T.take(8n, source(c, world, input, before, mode, raw,
    V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), before)
def the_actual_successful_preparation_prefix_derives_local_history_coherence(c, world, input, mode, raw, before, context, handle, seal, bytes, send, authenticated, fresh, fits, frame):
  %Equal.sym(V.PreparationRun,
    V.run(c, mode, raw, before, V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
    A.success(mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send),
    A.successful_preparation_has_the_exact_dispatcher_phases(c, mode, raw, before, context, handle, seal, bytes, send, authenticated, fresh, fits, frame)) :
      T.Coherent(T.take(8n, with_run(world, input, before, _)), before)
  successful_prefix_coherent(world, input, mode, raw, context, before, V.entry(mode, raw, E.instance(before), handle, seal), bytes, send)

law actual_preparation_mutation_has_full_current_history_before_its_conclusion:
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
  E.Current(O.environment(binding, public, c, seed, pi, artifacts,
    source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance), Source.artifact(binding),
    I.Serve{world, c, E.database(T.finish(T.take(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}})), input},
    O.time(B.count(O.Item, T.take(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})))),
    T.finish(T.take(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}))
def actual_preparation_mutation_has_full_current_history_before_its_conclusion(binding, public, c, seed, pi, artifacts, instance, world, input, mode, raw, context, handle, seal, bytes, send, authenticated, fits, frame):
  C.complete_current_is_derived_from_the_lossless_operational_event_prefix(binding, public, c, seed, pi, artifacts,
    source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}), instance,
    T.take(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})),
    T.drop(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
      V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})), world, input,
    the_actual_successful_preparation_prefix_derives_local_history_coherence(c, world, input, mode, raw,
      E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, context, handle, seal, bytes, send, authenticated, {==}, fits, frame),
    Equal.sym(List<&2, O.Item>,
      T.append(T.take(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
        V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send})),
        T.drop(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
          V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}))),
      source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
        V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}),
      T.taking_a_prefix_preserves_every_event_in_its_full_suffix(8n, source(c, world, input, E.Snapshot{instance, seed(Unit{}), Nil{}, Nil{}}, mode, raw,
        V.Returns{V.CheckerAccepted{}, V.AllocatorChosen{handle}, V.SealSucceeded{seal}, send}))))
