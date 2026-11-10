# Exact reverse V/N phase-item queries after one shared measured header bridge.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/PreparedProtocol.bend as W
import ../../../../../contract/Protocol.bend as P
import ../../../../../contract/Resources.bend as X
import ../../../../ProtocolService.bend as Q
import ../../../../Foundations.bend as F
import ../../../specification/ServiceLaws.bend as E
import ../../../phases/PreparePhases.bend as V
import ../../../phases/InvalidationPhases.bend as N
import ../../../model/EventObserver.bend as O
import ../../../model/FrameBounds.bend as B
import ../../../model/PreparationCurrent.bend as VP
import ../../../model/InvalidationPrefix.bend as NP
import ../../../model/serial/PreparationPrelude.bend as Prelude
import ../observed-invalidation/Prelude.bend as NPrelude
import ./Projection.bend as Projection
import ./Offset.bend as Offset

def phase_of(view: Projection.View) -> V.PreparationEvent:
  match view:
    case Projection.NoReceipt{}: V.Closed{}
    case Projection.Metadata{receipt, bytes}: V.ReceiptPrepared{receipt, bytes}

def reflect(phase: V.PreparationEvent, +wanted: W.Receipt, +prepared: List<&2, U32>,
  same: {Projection.phase(phase) == Projection.Metadata{wanted, prepared} : Projection.View}) -> {phase == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}:
  match phase:
    case V.WireReceived{wire}: L.ex_false({V.WireReceived{wire} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.IdentityEstablished{wire, context}: L.ex_false({V.IdentityEstablished{wire, context} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.Accepted{wire, context}: L.ex_false({V.Accepted{wire, context} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.Refuted{wire, context}: L.ex_false({V.Refuted{wire, context} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.PrimitiveFailed{stage, identifier, fatal}: L.ex_false({V.PrimitiveFailed{stage, identifier, fatal} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.HandleChosen{handle}: L.ex_false({V.HandleChosen{handle} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.ReceiptPrepared{receipt, bytes}: Equal.cong(Projection.View, V.PreparationEvent, phase_of, Projection.Metadata{receipt, bytes}, Projection.Metadata{wanted, prepared}, same)
    case V.ArtifactSealed{entry}: L.ex_false({V.ArtifactSealed{entry} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.RegistryChanged{entry, before, after}: L.ex_false({V.RegistryChanged{entry, before, after} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.ReceiptConcluded{receipt, result, snapshot, closes}: L.ex_false({V.ReceiptConcluded{receipt, result, snapshot, closes} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.ErrorPrepared{status, bytes}: L.ex_false({V.ErrorPrepared{status, bytes} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.ErrorConcluded{status, snapshot, closes}: L.ex_false({V.ErrorConcluded{status, snapshot, closes} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.Delivered{bytes}: L.ex_false({V.Delivered{bytes} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.Interrupted{prefix}: L.ex_false({V.Interrupted{prefix} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))
    case V.Closed{}: L.ex_false({V.Closed{} == V.ReceiptPrepared{wanted, prepared} : V.PreparationEvent}, (%same : Projection.Void(_) Unit{}))

def reflect_invalidation(event: N.InvalidationEvent, +receipt: W.Receipt, +bytes: List<&2, U32>,
  same: {Projection.event(O.Invalidation{event}) == Projection.Metadata{receipt, bytes} : Projection.View}) -> {event == N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}} : N.InvalidationEvent}:
  match event:
    case N.InvalidationBase{+phase}: Equal.cong(V.PreparationEvent, N.InvalidationEvent, p => N.InvalidationBase{p}, phase, V.ReceiptPrepared{receipt, bytes}, reflect(phase, receipt, bytes, same))
    case N.RegistryRemoved{handle, before, after}: L.ex_false({N.RegistryRemoved{handle, before, after} == N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}} : N.InvalidationEvent}, (%same : Projection.Void(_) Unit{}))

def PreparationHit(+world: Nat, +input: X.Reception, +selected: D.State, -events: List<&2, V.PreparationEvent>, -index: Nat, -item: O.Item) -> Type:
  &event: V.PreparationEvent -> L.E<{B.query(V.PreparationEvent, events, index) == Some{event} : Maybe<&2, V.PreparationEvent>}, {item == O.Item{world, selected, input, O.Preparation{event}} : O.Item}>

def preparation_phase(+world: Nat, +input: X.Reception, +selected: D.State, events: List<&2, V.PreparationEvent>, index: Nat, +item: O.Item,
  found: {B.query(O.Item, VP.phase_items(world, selected, input, events), index) == Some{item} : Maybe<&2, O.Item>}) -> PreparationHit(world, input, selected, events, index, item):
  match events index:
    case Nil{} index: L.ex_false(PreparationHit(world, input, selected, Nil{}, index, item), F.none_negative_some(O.Item, item, found))
    case Con{+head, rest} Zero{}: (head, L.Both{{==}, Equal.sym(O.Item, O.Item{world, selected, input, O.Preparation{head}}, item, F.some_injective(O.Item, O.Item{world, selected, input, O.Preparation{head}}, item, found))})
    case Con{head, +rest} Succ{prior}: preparation_phase(world, input, selected, rest, prior, item, found)

def preparation_from_hit(+world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, V.PreparationEvent>, +index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  hit: PreparationHit(world, input, selected, events, index, item)) ->
  {B.query(V.PreparationEvent, events, index) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}:
  match hit:
    case (+event, L.Both{found, exact}):
      Equal.trans(Maybe<&2, V.PreparationEvent>, B.query(V.PreparationEvent, events, index), Some{event}, Some{V.ReceiptPrepared{receipt, bytes}}, found,
        Equal.cong(V.PreparationEvent, Maybe<&2, V.PreparationEvent>, e => Some{e}, event, V.ReceiptPrepared{receipt, bytes},
          reflect(event, receipt, bytes, Equal.trans(Projection.View, Projection.phase(event), Projection.event(O.event(item)), Projection.Metadata{receipt, bytes},
            Equal.sym(Projection.View, Projection.event(O.event(item)), Projection.phase(event), Equal.cong(O.Item, Projection.View, i => Projection.event(O.event(i)), item, O.Item{world, selected, input, O.Preparation{event}}, exact)), actual))))

def preparation_shifted(+world: Nat, +input: X.Reception, +before: E.Snapshot, +frames: List<&2, Q.Frame>, +events: List<&2, V.PreparationEvent>, -index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  shifted: Offset.Hit(frames, VP.phase_items(world, E.database(before), input, events), index, item)) ->
  &local: Nat -> L.E<{index == Prelude.phase_index(frames, local) : Nat}, {B.query(V.PreparationEvent, events, local) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}>:
  match shifted:
    case (+local, L.Both{position, found}): (local, L.Both{position, preparation_from_hit(world, input, E.database(before), events, local, item, receipt, bytes, actual, preparation_phase(world, input, E.database(before), events, local, item, found))})

def preparation(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, run: V.PreparationRun, +index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, Prelude.with_run(world, input, before, raw, frames, run), index) == Some{item} : Maybe<&2, O.Item>}) ->
  &local: Nat -> L.E<{index == Prelude.phase_index(frames, local) : Nat}, {B.query(V.PreparationEvent, V.events(run), local) == Some{V.ReceiptPrepared{receipt, bytes}} : Maybe<&2, V.PreparationEvent>}>:
  match run:
    case V.PreparationRun{+events, result, snapshot, waiting, closed}:
      preparation_shifted(world, input, before, frames, events, index, item, receipt, bytes, actual, Offset.query(world, input, before, raw, frames, VP.phase_items(world, E.database(before), input, events), index, item, receipt, bytes, actual, found))

def InvalidationHit(+world: Nat, +input: X.Reception, +selected: D.State, -events: List<&2, N.InvalidationEvent>, -index: Nat, -item: O.Item) -> Type:
  &event: N.InvalidationEvent -> L.E<{B.query(N.InvalidationEvent, events, index) == Some{event} : Maybe<&2, N.InvalidationEvent>}, {item == O.Item{world, selected, input, O.Invalidation{event}} : O.Item}>

def invalidation_phase(+world: Nat, +input: X.Reception, +selected: D.State, events: List<&2, N.InvalidationEvent>, index: Nat, +item: O.Item,
  found: {B.query(O.Item, NP.phase_items(world, selected, input, events), index) == Some{item} : Maybe<&2, O.Item>}) -> InvalidationHit(world, input, selected, events, index, item):
  match events index:
    case Nil{} index: L.ex_false(InvalidationHit(world, input, selected, Nil{}, index, item), F.none_negative_some(O.Item, item, found))
    case Con{+head, rest} Zero{}: (head, L.Both{{==}, Equal.sym(O.Item, O.Item{world, selected, input, O.Invalidation{head}}, item, F.some_injective(O.Item, O.Item{world, selected, input, O.Invalidation{head}}, item, found))})
    case Con{head, +rest} Succ{prior}: invalidation_phase(world, input, selected, rest, prior, item, found)

def invalidation_from_hit(+world: Nat, +input: X.Reception, +selected: D.State, +events: List<&2, N.InvalidationEvent>, +index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  hit: InvalidationHit(world, input, selected, events, index, item)) ->
  {B.query(N.InvalidationEvent, events, index) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}:
  match hit:
    case (+event, L.Both{found, exact}):
      Equal.trans(Maybe<&2, N.InvalidationEvent>, B.query(N.InvalidationEvent, events, index), Some{event}, Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}}, found,
        Equal.cong(N.InvalidationEvent, Maybe<&2, N.InvalidationEvent>, e => Some{e}, event, N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}},
          reflect_invalidation(event, receipt, bytes, Equal.trans(Projection.View, Projection.event(O.Invalidation{event}), Projection.event(O.event(item)), Projection.Metadata{receipt, bytes},
            Equal.sym(Projection.View, Projection.event(O.event(item)), Projection.event(O.Invalidation{event}), Equal.cong(O.Item, Projection.View, i => Projection.event(O.event(i)), item, O.Item{world, selected, input, O.Invalidation{event}}, exact)), actual))))

def invalidation_shifted(+world: Nat, +input: X.Reception, +before: E.Snapshot, +frames: List<&2, Q.Frame>, +events: List<&2, N.InvalidationEvent>, -index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  shifted: Offset.Hit(frames, NP.phase_items(world, E.database(before), input, events), index, item)) ->
  &local: Nat -> L.E<{index == Prelude.phase_index(frames, local) : Nat}, {B.query(N.InvalidationEvent, events, local) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}>:
  match shifted:
    case (+local, L.Both{position, found}): (local, L.Both{position, invalidation_from_hit(world, input, E.database(before), events, local, item, receipt, bytes, actual, invalidation_phase(world, input, E.database(before), events, local, item, found))})

def invalidation(+world: Nat, +input: X.Reception, +before: E.Snapshot, +raw: P.Request, +frames: List<&2, Q.Frame>, run: N.InvalidationRun, +index: Nat, +item: O.Item, +receipt: W.Receipt, +bytes: List<&2, U32>,
  +actual: {Projection.event(O.event(item)) == Projection.Metadata{receipt, bytes} : Projection.View},
  found: {B.query(O.Item, NPrelude.with_run(world, input, before, raw, frames, run), index) == Some{item} : Maybe<&2, O.Item>}) ->
  &local: Nat -> L.E<{index == Prelude.phase_index(frames, local) : Nat}, {B.query(N.InvalidationEvent, N.events(run), local) == Some{N.InvalidationBase{V.ReceiptPrepared{receipt, bytes}}} : Maybe<&2, N.InvalidationEvent>}>:
  match run:
    case N.InvalidationRun{+events, result, snapshot, waiting, closed}:
      invalidation_shifted(world, input, before, frames, events, index, item, receipt, bytes, actual, Offset.query(world, input, before, raw, frames, NP.phase_items(world, E.database(before), input, events), index, item, receipt, bytes, actual, found))
