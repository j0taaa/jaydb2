# Actual invalidation prefix coheres with the selected snapshot before ANY
# cleanup result. Pending/fatal cleanup retains the real removal in Current.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Interface.bend as I
import ../../../contract/Logic.bend as L
import ../../../contract/PreparedRegistry.bend as G
import ../../../contract/PreparedProtocol.bend as W
import ../../../contract/Protocol.bend as P
import ../../../contract/Requirements.bend as R
import ../../../contract/Resources.bend as X
import ../../../contract/Semantics.bend as S
import ../specification/ServiceLaws.bend as E
import ../phases/PreparePhases.bend as V
import ../phases/InvalidationPhases.bend as N
import ../phases/InvalidationEvents.bend as A
import ./EventObserver.bend as O
import ./EventHistory.bend as T
import ./FrameBounds.bend as B

def phase_items(+world: Nat, +selected: D.State, +input: X.Reception, phases: List<&2, N.InvalidationEvent>) -> List<&2, O.Item>:
  match phases:
    case Nil{}: Nil{}
    case Con{phase, rest}: Con{O.Item{world, selected, input, O.Invalidation{phase}}, phase_items(world, selected, input, rest)}

def with_run(+world: Nat, +input: X.Reception, +before: E.Snapshot, run: N.InvalidationRun) -> List<&2, O.Item>:
  Con{O.Item{world, E.database(before), input, O.Selection{before}}, phase_items(world, E.database(before), input, N.events(run))}

def source(~c: S.Configuration, world: Nat, input: X.Reception, +before: E.Snapshot,
  raw: P.Request, cleanup: N.CleanupReturn, send: V.SendReturn) -> List<&2, O.Item>:
  with_run(world, input, before, N.run(c, before, raw, cleanup, send))

def RemovalProperties(-items: List<&2, O.Item>, +before: E.Snapshot, -handle: String) -> Type:
  L.E<T.Coherent(T.take(5n, items), before),
    L.E<{T.finish(T.take(5n, items), before) == N.removed(before, handle) : E.Snapshot},
      {B.count(O.Item, T.take(5n, items)) == 5n : Nat}>>

def removal_prefix_properties(+world: Nat, +input: X.Reception, +before: E.Snapshot,
  +raw: P.Request, context: D.Context, bytes: List<&2, U32>, tail: N.InvalidationRun) ->
  RemovalProperties(with_run(world, input, before, A.removal_prefix(before, raw, context, bytes, tail)), before, I.code(raw)):
  match tail:
    case N.InvalidationRun{events, result, snapshot, waiting, closed}:
      L.Both{L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{Unit{}, L.Both{L.Both{{==}, L.Both{{==}, {==}}}, Unit{}}}}}},
        L.Both{{==}, {==}}}

law actual_removal_derives_local_history_before_every_cleanup_return:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for +raw: P.Request
  for +entry: G.Entry
  for +context: D.Context
  for +bytes: List<&2, U32>
  for +cleanup: N.CleanupReturn
  for +send: V.SendReturn
  for authenticated: {D.authenticate(E.database(before), I.credential(raw)) == Some{context} : Maybe<&2, D.Context>}
  for empty: {String.eq(I.proof(raw), "") == True{} : Bool}
  for present: {G.lookup(E.instance(before), I.code(raw), E.registry(before)) == Some{entry} : Maybe<&2, G.Entry>}
  for fits: {R.fits(R.limit_response(S.limits(c)), W.receipt_value(W.InvalidatedReceipt{})) == True{} : Bool}
  for frame: {W.frame_receipt(W.InvalidatedReceipt{}) == Some{bytes} : Maybe<&2, List<&2, U32>>}
  RemovalProperties(source(c, world, input, before, raw, cleanup, send), before, I.code(raw))
def actual_removal_derives_local_history_before_every_cleanup_return(c, world, input, before, raw, entry, context, bytes, cleanup, send,
  authenticated, empty, present, fits, frame):
  %Equal.sym(N.InvalidationRun, N.run(c, before, raw, cleanup, send),
    A.removal_prefix(before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send)),
    A.actual_authorized_framed_invalidation_has_its_exact_removal_phases(c, before, raw, entry, context, bytes, cleanup, send,
      authenticated, empty, present, fits, frame)) : RemovalProperties(with_run(world, input, before, _), before, I.code(raw))
  removal_prefix_properties(world, input, before, raw, context, bytes, N.cleaned(cleanup, N.removed(before, I.code(raw)), bytes, send))

law adjoining_actual_phase_prefixes_preserves_all_local_history_links:
  for +prefix: List<&2, O.Item>
  for +suffix: List<&2, O.Item>
  for +before: E.Snapshot
  for first: T.Coherent(prefix, before)
  for later: T.Coherent(suffix, T.finish(prefix, before))
  T.Coherent(T.append(prefix, suffix), before)
def adjoining_actual_phase_prefixes_preserves_all_local_history_links(prefix, suffix, before, first, later):
  match prefix first:
    case Nil{} _: later
    case Con{+item, +rest} L.Both{head, tail}:
      L.Both{head, adjoining_actual_phase_prefixes_preserves_all_local_history_links(rest, suffix, T.next(O.change(O.event(item)), before), tail, later)}

law adjoining_phase_prefixes_has_the_exact_sequential_snapshot:
  for +prefix: List<&2, O.Item>
  for +suffix: List<&2, O.Item>
  for +before: E.Snapshot
  {T.finish(T.append(prefix, suffix), before) == T.finish(suffix, T.finish(prefix, before)) : E.Snapshot}
def adjoining_phase_prefixes_has_the_exact_sequential_snapshot(prefix, suffix, before):
  match prefix:
    case Nil{}: {==}
    case Con{+item, rest}:
      adjoining_phase_prefixes_has_the_exact_sequential_snapshot(rest, suffix, T.next(O.change(O.event(item)), before))

law exact_suffix_query_survives_every_actual_prior_event:
  for +prefix: List<&2, O.Item>
  for +suffix: List<&2, O.Item>
  for +index: Nat
  {B.query(O.Item, T.append(prefix, suffix), Nat.add(B.count(O.Item, prefix), index)) == B.query(O.Item, suffix, index) : Maybe<&2, O.Item>}
def exact_suffix_query_survives_every_actual_prior_event(prefix, suffix, index):
  match prefix:
    case Nil{}: {==}
    case Con{item, rest}: exact_suffix_query_survives_every_actual_prior_event(rest, suffix, index)

def item_result(+world: Nat, +selected: D.State, +input: X.Reception, result: Maybe<&2, N.InvalidationEvent>) -> Maybe<&2, O.Item>:
  match result:
    case None{}: None{}
    case Some{phase}: Some{O.Item{world, selected, input, O.Invalidation{phase}}}

law exact_removal_phase_query_lifts_to_the_full_observer_item_query:
  for +world: Nat
  for +selected: D.State
  for +input: X.Reception
  for phases: List<&2, N.InvalidationEvent>
  for index: Nat
  {B.query(O.Item, phase_items(world, selected, input, phases), index) ==
    item_result(world, selected, input, B.query(N.InvalidationEvent, phases, index)) : Maybe<&2, O.Item>}
def exact_removal_phase_query_lifts_to_the_full_observer_item_query(world, selected, input, phases, index):
  match phases index:
    case Nil{} _: {==}
    case Con{phase, rest} 0n: {==}
    case Con{phase, rest} 1n+k: exact_removal_phase_query_lifts_to_the_full_observer_item_query(world, selected, input, rest, k)

law exact_invalidation_query_supplies_the_actual_observer_query:
  for ~c: S.Configuration
  for +world: Nat
  for +input: X.Reception
  for +before: E.Snapshot
  for raw: P.Request
  for cleanup: N.CleanupReturn
  for send: V.SendReturn
  for +index: Nat
  for -phase: N.InvalidationEvent
  for query: {B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index) == Some{phase} : Maybe<&2, N.InvalidationEvent>}
  {B.query(O.Item, source(c, world, input, before, raw, cleanup, send), Succ{index}) ==
    Some{O.Item{world, E.database(before), input, O.Invalidation{phase}}} : Maybe<&2, O.Item>}
def exact_invalidation_query_supplies_the_actual_observer_query(c, world, input, before, raw, cleanup, send, index, phase, query):
  Equal.trans(Maybe<&2, O.Item>, B.query(O.Item, phase_items(world, E.database(before), input, N.events(N.run(c, before, raw, cleanup, send))), index),
    item_result(world, E.database(before), input, B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index)),
    Some{O.Item{world, E.database(before), input, O.Invalidation{phase}}},
    exact_removal_phase_query_lifts_to_the_full_observer_item_query(world, E.database(before), input, N.events(N.run(c, before, raw, cleanup, send)), index),
    Equal.cong(Maybe<&2, N.InvalidationEvent>, Maybe<&2, O.Item>, result => item_result(world, E.database(before), input, result),
      B.query(N.InvalidationEvent, N.events(N.run(c, before, raw, cleanup, send)), index), Some{phase}, query))
