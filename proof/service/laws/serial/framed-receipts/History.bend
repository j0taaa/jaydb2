# All retained items of the actual Engine, including arbitrary earlier calls,
# preserve the real metadata frame property. No query/output/history premise.
import Base
import ../../../../../contract/Data.bend as D
import ../../../../../contract/Logic.bend as L
import ../../../../../contract/Resources.bend as X
import ../../../../../contract/Semantics.bend as S
import ../../../../Foundations.bend as F
import ../../../../SourceService.bend as Binding
import ../../../specification/ServiceLaws.bend as E
import ../../../model/EventObserver.bend as O
import ../../../model/EventHistory.bend as T
import ../../../model/FrameBounds.bend as B
import ../../../model/serial/Common.bend as C
import ../../../model/serial/Dispatch.bend as Dispatch
import ../../../model/serial/Engine.bend as Engine
import ./Source.bend as Framed

def All(~c: S.Configuration, items: List<&2, O.Item>) -> Type:
  match items:
    case Nil{}: Unit
    case Con{item, rest}: L.E<Framed.Claim(c, O.event(item)), All(c, rest)>

def stamped(~c: S.Configuration, +world: Nat, +input: X.Reception, +selected: D.State, events: List<&2, O.AuditEvent>, properties: Framed.All(c, events)) -> All(c, Engine.stamp(world, input, selected, events)):
  match events properties:
    case Nil{} unit: Unit{}
    case Con{event, rest} L.Both{first, later}: L.Both{first, stamped(c, world, input, selected, rest, later)}

def selected(~c: S.Configuration, selection: Bool, +before: E.Snapshot, -events: List<&2, O.AuditEvent>, properties: Framed.All(c, events)) -> Framed.All(c, Engine.selected_events(selection, before, events)):
  match selection:
    case False{}: properties
    case True{}: L.Both{Unit{}, properties}

def block(~c: S.Configuration, ~binding: Binding.Source, ~public: List<&2, Binding.FileSource>, +ordinal: Nat, +before: E.Snapshot, job: Engine.Job) -> All(c, Engine.block_items(Engine.block(c, binding, public, ordinal, before, job))):
  match job:
    case Engine.Job{+input, +primitives}:
      stamped(c, Succ{ordinal}, input, E.database(before), Engine.selected_events(Engine.selection(X.decide_reception(c, input)), before, C.events(Dispatch.run(c, binding, public, before, input, primitives))),
        selected(c, Engine.selection(X.decide_reception(c, input)), before, C.events(Dispatch.run(c, binding, public, before, input, primitives)),
          Framed.every_actual_complete_dispatch_retains_encoding_and_limits_of_every_metadata_prepared_frame(c, binding, public, before, input, primitives)))

def appended(~c: S.Configuration, +prefix: List<&2, O.Item>, -tail: List<&2, O.Item>, first: All(c, prefix), later: All(c, tail)) -> All(c, T.append(prefix, tail)):
  match prefix first:
    case Nil{} unit: later
    case Con{item, +rest} L.Both{one, remaining}: L.Both{one, appended(c, rest, tail, remaining, later)}

def append_block(~c: S.Configuration, +block: Engine.Block, suffix: Engine.PrefixRun, first: All(c, Engine.block_items(block)), later: All(c, Engine.items(suffix))) -> All(c, Engine.items(Engine.append_block(block, suffix))):
  match suffix:
    case Engine.PrefixRun{blocks, items, snapshot, next, waiting, closed}: appended(c, Engine.block_items(block), items, first, later)

def stopped(~c: S.Configuration, block: Engine.Block, properties: All(c, Engine.block_items(block))) -> All(c, Engine.items(Engine.stopped_block(block))):
  match block:
    case Engine.Block{ordinal, selection, input, before, run}: properties

def branch(~c: S.Configuration, proceed: Bool, +block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  first: All(c, Engine.block_items(block)), rest: @next: Nat -> @before: E.Snapshot -> All(c, Engine.items(recur(next, before)))) -> All(c, Engine.items(Engine.branch(proceed, block, recur))):
  match proceed:
    case False{}: stopped(c, block, first)
    case True{}: append_block(c, block, recur(Engine.next_after(block), Engine.after(block)), first, rest(Engine.next_after(block), Engine.after(block)))

def execute_block(~c: S.Configuration, +block: Engine.Block, recur: Nat -> E.Snapshot -> Engine.PrefixRun,
  first: All(c, Engine.block_items(block)), rest: @next: Nat -> @before: E.Snapshot -> All(c, Engine.items(recur(next, before)))) -> All(c, Engine.items(Engine.execute_block(block, recur))):
  match block:
    case Engine.Block{+ordinal, +selection, +input, +before, +run}: branch(c, C.continues(run), Engine.Block{ordinal, selection, input, before, run}, recur, first, rest)

law every_actual_complete_serial_history_preserves_all_metadata_receipt_frame_encodings_and_bounds:
  for ~c: S.Configuration
  for ~binding: Binding.Source
  for ~public: List<&2, Binding.FileSource>
  for script: List<&2, Engine.Job>
  for +ordinal: Nat
  for +before: E.Snapshot
  All(c, Engine.items(Engine.run(c, binding, public, script, ordinal, before)))
def every_actual_complete_serial_history_preserves_all_metadata_receipt_frame_encodings_and_bounds(c, binding, public, script, ordinal, before):
  match script:
    case Nil{}: Unit{}
    case Con{+job, +rest}:
      execute_block(c, Engine.block(c, binding, public, ordinal, before, job), next => current => Engine.run(c, binding, public, rest, next, current),
        block(c, binding, public, ordinal, before, job),
        next => current => every_actual_complete_serial_history_preserves_all_metadata_receipt_frame_encodings_and_bounds(c, binding, public, rest, next, current))

def query(~c: S.Configuration, items: List<&2, O.Item>, index: Nat, +item: O.Item,
  properties: All(c, items), found: {B.query(O.Item, items, index) == Some{item} : Maybe<&2, O.Item>}) -> Framed.Claim(c, O.event(item)):
  match items index properties:
    case Nil{} _ unit: L.ex_false(Framed.Claim(c, O.event(item)), F.none_negative_some(O.Item, item, found))
    case Con{+head, rest} 0n L.Both{first, later}:
      %F.some_injective(O.Item, head, item, found) : Framed.Claim(c, O.event(_))
      first
    case Con{head, rest} 1n+previous L.Both{first, later}: query(c, rest, previous, item, later, found)
