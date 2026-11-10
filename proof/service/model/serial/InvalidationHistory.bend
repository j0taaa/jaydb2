# Invalidation history includes the actual removal BEFORE all cleanup returns,
# including pending and fatal branches with NO completed-call result.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Interface.bend as I
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/PreparedRegistry.bend as G
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../specification/ServiceLaws.bend as E
import ../../phases/PreparePhases.bend as V
import ../../phases/InvalidationPhases.bend as N
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ./Common.bend as C
import ./LocalHistory.bend as J
import ./PrepareHistory.bend as Preparation


def Sound(+position: J.Position, +run: N.InvalidationRun, before: E.Snapshot) -> Type:
  J.Sound(position, C.invalidate_events(N.events(run)), before, N.snapshot(run))


def lifted_link(change: Maybe<&2, O.Change>, -world: Nat, -input: X.Reception, -selected: D.State,
  -event: V.PreparationEvent, -before: E.Snapshot,
  original: T.CoherentChange(change, O.Item{world, selected, input, O.Preparation{event}}, before)) ->
  T.CoherentChange(change, O.Item{world, selected, input, O.Invalidation{N.InvalidationBase{event}}}, before):
  match change:
    case None{}: Unit{}
    case Some{O.Change{mode, mutation, old, after}}: original


def lifted_coherence(+position: J.Position, +events: List<&2, V.PreparationEvent>, +before: E.Snapshot,
  original: T.Coherent(J.stamp(position, C.prepare_events(events)), before)) ->
  T.Coherent(J.stamp(position, C.invalidate_events(N.base_events(events))), before):
  J.Position{+world, +input, +selected} = position
  match events original:
    case Nil{} _: Unit{}
    case Con{+event, +rest} L.Both{head, later}:
      L.Both{lifted_link(O.phase_change(event), world, input, selected, event, before, head), lifted_coherence(J.Position{world, input, selected}, rest, T.next(O.phase_change(event), before), later)}


def lifted_finish(+position: J.Position, +events: List<&2, V.PreparationEvent>, +before: E.Snapshot) ->
  {T.finish(J.stamp(position, C.invalidate_events(N.base_events(events))), before) ==
    T.finish(J.stamp(position, C.prepare_events(events)), before) : E.Snapshot}:
  J.Position{+world, +input, +selected} = position
  match events:
    case Nil{}: {==}
    case Con{event, rest}: lifted_finish(J.Position{world, input, selected}, rest, T.next(O.phase_change(event), before))


def lifted_sound(+position: J.Position, +run: V.PreparationRun, +before: E.Snapshot,
  original: Preparation.Sound(position, run, before)) -> Sound(position, N.lift(run), before):
  V.PreparationRun{+events, result, +snapshot, waiting, closed} = run
  match original:
    case L.Both{coherent, final}:
      L.Both{lifted_coherence(position, events, before, coherent),
        Equal.trans(E.Snapshot, T.finish(J.stamp(position, C.invalidate_events(N.base_events(events))), before),
          T.finish(J.stamp(position, C.prepare_events(events)), before), snapshot,
          lifted_finish(position, events, before), final)}


def push(+position: J.Position, +event: N.InvalidationEvent, +run: N.InvalidationRun, +before: E.Snapshot,
  quiet: {O.invalidation_change(event) == None{} : Maybe<&2, O.Change>}, later: Sound(position, run, before)) ->
  Sound(position, N.push(event, run), before):
  N.InvalidationRun{events, result, snapshot, waiting, closed} = run
  J.quiet_push(position, O.Invalidation{event}, C.invalidate_events(events), before, snapshot, quiet, later)


def cleaned(+position: J.Position, +cleanup: N.CleanupReturn, +after: E.Snapshot, +bytes: List<&2, U32>, +send: V.SendReturn) ->
  Sound(position, N.cleaned(cleanup, after, bytes, send), after):
  match cleanup:
    case N.CleanupPending{}: lifted_sound(position, V.pending(after), after, J.no_events(position, after))
    case N.CleanupFailed{identifier, fatal}:
      lifted_sound(position, V.failed(X.Prepare{}, identifier, fatal, after, send), after, Preparation.failed(position, X.Prepare{}, identifier, fatal, after, send))
    case N.CleanupComplete{}:
      lifted_sound(position, V.push(V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(after), after, False{}}, V.delivery(send, bytes, N.metadata(after), after)), after,
        Preparation.push(position, V.ReceiptConcluded{W.InvalidatedReceipt{}, N.metadata(after), after, False{}}, V.delivery(send, bytes, N.metadata(after), after), after, {==},
          Preparation.delivery(position, send, bytes, N.metadata(after), after)))


def removed_tail(+position: J.Position, +before: E.Snapshot, +handle: String, +run: N.InvalidationRun,
  selection: {J.selected(position) == E.database(before) : D.State},
  later: Sound(position, run, N.removed(before, handle))) ->
  Sound(position, N.push(N.RegistryRemoved{handle, before, N.removed(before, handle)}, run), before):
  N.InvalidationRun{events, result, snapshot, waiting, closed} = run
  J.mutation_push(position, O.Invalidation{N.RegistryRemoved{handle, before, N.removed(before, handle)}}, C.invalidate_events(events), True{}, E.Invalidate{handle}, before, N.removed(before, handle), snapshot,
    {==}, {==}, selection, later)


def remove_and_cleanup(+position: J.Position, +before: E.Snapshot, +handle: String, +bytes: List<&2, U32>, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, N.remove_and_cleanup(before, handle, bytes, cleanup, send), before):
  removed_tail(position, before, handle, N.cleaned(cleanup, N.removed(before, handle), bytes, send), selection, cleaned(position, cleanup, N.removed(before, handle), bytes, send))


def framed(+position: J.Position, +frame: Maybe<&2, List<&2, U32>>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, N.framed(frame, before, handle, cleanup, send), before):
  match frame:
    case None{}: lifted_sound(position, V.inconsistent(before), before, J.no_events(position, before))
    case Some{+bytes}:
      push(position, N.InvalidationBase{V.ReceiptPrepared{W.InvalidatedReceipt{}, bytes}}, N.remove_and_cleanup(before, handle, bytes, cleanup, send), before, {==},
        remove_and_cleanup(position, before, handle, bytes, cleanup, send, selection))


def fitting(+position: J.Position, fits: Bool, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, N.fitting(fits, before, handle, cleanup, send), before):
  match fits:
    case False{}: lifted_sound(position, V.error(S.Limit{}, before, send), before, Preparation.error(position, S.Limit{}, before, send))
    case True{}: framed(position, W.frame_receipt(W.InvalidatedReceipt{}), before, handle, cleanup, send, selection)


def found(~c: S.Configuration, +position: J.Position, +entry: Maybe<&2, G.Entry>, +before: E.Snapshot, +handle: String, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, N.found(c, entry, before, handle, cleanup, send), before):
  match entry:
    case None{}: lifted_sound(position, V.error(S.Failure{}, before, send), before, Preparation.error(position, S.Failure{}, before, send))
    case Some{entry}: fitting(position, R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})), before, handle, cleanup, send, selection)


def proof_checked(~c: S.Configuration, +position: J.Position, empty: Bool, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, N.proof_checked(c, empty, before, raw, cleanup, send), before):
  match empty:
    case False{}: lifted_sound(position, V.error(S.Input{}, before, send), before, Preparation.error(position, S.Input{}, before, send))
    case True{}: found(c, position, G.lookup(E.instance(before), I.code(raw), E.registry(before)), before, I.code(raw), cleanup, send, selection)


def authenticated(~c: S.Configuration, +position: J.Position, +identity: Maybe<&2, D.Context>, +before: E.Snapshot, +raw: P.Request, +cleanup: N.CleanupReturn, +send: V.SendReturn,
  selection: {J.selected(position) == E.database(before) : D.State}) -> Sound(position, N.authenticated(c, identity, before, raw, cleanup, send), before):
  match identity:
    case None{}: lifted_sound(position, V.error(S.Authentication{}, before, send), before, Preparation.error(position, S.Authentication{}, before, send))
    case Some{context}: proof_checked(c, position, String.eq(I.proof(raw), ""), before, raw, cleanup, send, selection)


law every_actual_invalidation_prefix_derives_complete_history_even_without_a_result:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +raw: P.Request
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  Sound(J.Position{world, input, E.database(before)}, N.run(c, before, raw, cleanup, send), before)
def every_actual_invalidation_prefix_derives_complete_history_even_without_a_result(c, world, input, before, raw, cleanup, send):
  +position: J.Position = J.Position{world, input, E.database(before)}
  +identity = D.authenticate(E.database(before), I.credential(raw))
  push(position, N.InvalidationBase{V.WireReceived{W.Extension{W.Invalidate{}, raw}}},
    N.push(N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, identity}}, N.authenticated(c, identity, before, raw, cleanup, send)), before, {==},
    push(position, N.InvalidationBase{V.IdentityEstablished{W.Extension{W.Invalidate{}, raw}, identity}}, N.authenticated(c, identity, before, raw, cleanup, send), before, {==},
      authenticated(c, position, identity, before, raw, cleanup, send, {==})))
