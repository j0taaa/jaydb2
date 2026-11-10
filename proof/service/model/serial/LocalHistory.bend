# Local replay induction over complete event lists. The only link facts are
# literal DATA before/after/selected equalities; no Current or validity premise.
import Base
import ../../../../contract/Data.bend as D
import ../../../../contract/Logic.bend as L
import ../../../../contract/Resources.bend as X
import ../../../ProtocolService.bend as Q
import ../../../SourceService.bend as Source
import ../../specification/ServiceLaws.bend as E
import ../EventObserver.bend as O
import ../EventHistory.bend as T
import ./Common.bend as C
import ./Engine.bend as Engine


type Position is Data:
  Position{world: Nat, input: X.Reception, selected: D.State}


def world(position: Position) -> Nat:
  Position{world, input, selected} = position
  world

def input(position: Position) -> X.Reception:
  Position{world, input, selected} = position
  input


def selected(position: Position) -> D.State:
  Position{world, input, selected} = position
  selected


def stamp(position: Position, events: List<&2, O.AuditEvent>) -> List<&2, O.Item>:
  Position{world, input, selected} = position
  Engine.stamp(world, input, selected, events)


def Sound(+position: Position, +events: List<&2, O.AuditEvent>, +before: E.Snapshot, -after: E.Snapshot) -> Type:
  L.E<T.Coherent(stamp(position, events), before), {T.finish(stamp(position, events), before) == after : E.Snapshot}>


def CallSound(+position: Position, +run: C.CallRun, before: E.Snapshot) -> Type:
  Sound(position, C.events(run), before, C.snapshot(run))


def Quiet(events: List<&2, O.AuditEvent>) -> Type:
  match events:
    case Nil{}: Unit
    case Con{event, rest}: L.E<{O.change(event) == None{} : Maybe<&2, O.Change>}, Quiet(rest)>


def no_events(position: Position, before: E.Snapshot) -> Sound(position, Nil{}, before, before):
  Position{world, input, selected} = position
  L.Both{Unit{}, {==}}


def quiet_push(+position: Position, +event: O.AuditEvent, +rest: List<&2, O.AuditEvent>,
  +before: E.Snapshot, -after: E.Snapshot,
  quiet: {O.change(event) == None{} : Maybe<&2, O.Change>},
  later: Sound(position, rest, before, after)) -> Sound(position, Con{event, rest}, before, after):
  Position{world, input, +selected} = position
  match later:
    case L.Both{coherent, final}:
      %Equal.sym(Maybe<&2, O.Change>, O.change(event), None{}, quiet) :
        L.E<L.E<T.CoherentChange(_, O.Item{world, selected, input, event}, before),
          T.Coherent(Engine.stamp(world, input, selected, rest), T.next(_, before))>,
          {T.finish(Engine.stamp(world, input, selected, rest), T.next(_, before)) == after : E.Snapshot}>
      L.Both{L.Both{Unit{}, coherent}, final}


def quiet_prefix(+position: Position, +prefix: List<&2, O.AuditEvent>, +rest: List<&2, O.AuditEvent>,
  +before: E.Snapshot, -after: E.Snapshot, silent: Quiet(prefix), later: Sound(position, rest, before, after)) ->
  Sound(position, C.append(prefix, rest), before, after):
  match prefix silent:
    case Nil{} _: later
    case Con{+event, +tail} L.Both{first, following}:
      quiet_push(position, event, C.append(tail, rest), before, after, first,
        quiet_prefix(position, tail, rest, before, after, following, later))


def quiet_all(+position: Position, +events: List<&2, O.AuditEvent>, +before: E.Snapshot,
  silent: Quiet(events)) -> Sound(position, events, before, before):
  match events silent:
    case Nil{} _: no_events(position, before)
    case Con{+event, +rest} L.Both{first, following}:
      quiet_push(position, event, rest, before, before, first, quiet_all(position, rest, before, following))


def prefix_call(+position: Position, +prefix: List<&2, O.AuditEvent>, +run: C.CallRun, +before: E.Snapshot,
  silent: Quiet(prefix), later: CallSound(position, run, before)) -> CallSound(position, C.prefix(prefix, run), before):
  C.CallRun{events, after, outcome, waiting, closed} = run
  quiet_prefix(position, prefix, events, before, after, silent, later)


def core_quiet(+mode: Bool, +code: String, frames: List<&2, Q.Frame>) -> Quiet(C.core(mode, code, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{{==}, core_quiet(mode, code, rest)}


def bound_core_quiet(+mode: Bool, +origin: Source.JudgmentSyntactic, frames: List<&2, Q.Frame>) -> Quiet(C.bound_core(mode, origin, frames)):
  match frames:
    case Nil{}: Unit{}
    case Con{frame, rest}: L.Both{{==}, bound_core_quiet(mode, origin, rest)}


def mutation_push(+position: Position, +event: O.AuditEvent, +rest: List<&2, O.AuditEvent>,
  +mode: Bool, +mutation: E.Mutation, +before: E.Snapshot, +after: E.Snapshot, -final: E.Snapshot,
  changed: {O.change(event) == Some{O.Change{mode, mutation, before, after}} : Maybe<&2, O.Change>},
  scope: {E.instance(before) == E.instance(after) : String},
  same_selection: {selected(position) == E.database(before) : D.State},
  later: Sound(position, rest, after, final)) -> Sound(position, Con{event, rest}, before, final):
  Position{world, input, +selected} = position
  match later:
    case L.Both{coherent, result}:
      %Equal.sym(Maybe<&2, O.Change>, O.change(event), Some{O.Change{mode, mutation, before, after}}, changed) :
        L.E<L.E<T.CoherentChange(_, O.Item{world, selected, input, event}, before),
          T.Coherent(Engine.stamp(world, input, selected, rest), T.next(_, before))>,
          {T.finish(Engine.stamp(world, input, selected, rest), T.next(_, before)) == final : E.Snapshot}>
      L.Both{L.Both{L.Both{{==}, L.Both{scope, same_selection}}, coherent}, result}


def linked_push(+position: Position, +event: O.AuditEvent, +rest: List<&2, O.AuditEvent>, +before: E.Snapshot, -after: E.Snapshot,
  link: T.CoherentChange(O.change(event), O.Item{world(position), selected(position), input(position), event}, before),
  later: Sound(position, rest, T.next(O.change(event), before), after)) -> Sound(position, Con{event, rest}, before, after):
  Position{world, input, selected} = position
  match later:
    case L.Both{coherent, final}: L.Both{L.Both{link, coherent}, final}


def append_sound(+position: Position, +prefix: List<&2, O.AuditEvent>, +suffix: List<&2, O.AuditEvent>,
  +before: E.Snapshot, +middle: E.Snapshot, -after: E.Snapshot,
  first: Sound(position, prefix, before, middle), later: Sound(position, suffix, middle, after)) -> Sound(position, C.append(prefix, suffix), before, after):
  Position{+world, +input, +selected} = position
  match prefix first:
    case Nil{} L.Both{empty, same}:
      %Equal.sym(E.Snapshot, before, middle, same) : Sound(Position{world, input, selected}, suffix, _, after)
      later
    case Con{+event, +rest} L.Both{L.Both{link, following}, final}:
      linked_push(Position{world, input, selected}, event, C.append(rest, suffix), before, after, link,
        append_sound(Position{world, input, selected}, rest, suffix, T.next(O.change(event), before), middle, after, L.Both{following, final}, later))


def full_prefix_call(+position: Position, +prefix: List<&2, O.AuditEvent>, +run: C.CallRun, +before: E.Snapshot, +middle: E.Snapshot,
  first: Sound(position, prefix, before, middle), later: CallSound(position, run, middle)) -> CallSound(position, C.prefix(prefix, run), before):
  C.CallRun{events, snapshot, outcome, waiting, closed} = run
  append_sound(position, prefix, events, before, middle, snapshot, first, later)
