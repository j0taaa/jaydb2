# Atomic queue/reservation transitions matching server/scheduling.rs.
# Counters include the sole reader's reservation before body allocation/read.
# This is an operational model; Rust/OS correspondence is a separate contract.
import Base
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./HandleCardinality.bend as N

type Frame is Data:
  Frame{identity: Nat, body: List<&2, U32>}

def frame_size(frame: Frame) -> Nat:
  Frame{id, body} = frame
  B.length(body)

def count(frames: List<&2, Frame>) -> Nat:
  match frames:
    case Nil{}: 0n
    case Con{frame, rest}: 1n+count(rest)

def byte_count(frames: List<&2, Frame>) -> Nat:
  match frames:
    case Nil{}: 0n
    case Con{frame, rest}: Nat.add(frame_size(frame), byte_count(rest))

def append(frames: List<&2, Frame>, last: Frame) -> List<&2, Frame>:
  match frames:
    case Nil{}: [last]
    case Con{frame, rest}: Con{frame, append(rest, last)}

def concatenate(left: List<&2, Frame>, right: List<&2, Frame>) -> List<&2, Frame>:
  match left:
    case Nil{}: right
    case Con{frame, rest}: Con{frame, concatenate(rest, right)}

type Phase is Data:
  Idle{}
  Header{}
  Body{declared: Nat}
  Ended{}

type End is Data:
  Eof{}
  Framing{status: String}
  Failed{identifier: String}

type Queue is Data:
  Queue{frames: List<&2, Frame>, phase: Phase, terminal: Maybe<&2, End>, stopped: Bool}

def frames(queue: Queue) -> List<&2, Frame>:
  Queue{frames, phase, terminal, stopped} = queue
  frames

def occupied_items(phase: Phase, frames: List<&2, Frame>) -> Nat:
  match phase:
    case Idle{}: count(frames)
    case Header{}: 1n+count(frames)
    case Body{declared}: 1n+count(frames)
    case Ended{}: count(frames)

def occupied_bytes(phase: Phase, frames: List<&2, Frame>) -> Nat:
  match phase:
    case Body{declared}: Nat.add(byte_count(frames), declared)
    case _: byte_count(frames)

def items(queue: Queue) -> Nat:
  Queue{frames, phase, terminal, stopped} = queue
  occupied_items(phase, frames)

def bytes(queue: Queue) -> Nat:
  Queue{frames, phase, terminal, stopped} = queue
  occupied_bytes(phase, frames)

type Bounds is Data:
  Bounds{items: Nat, bytes: Nat}

def item_bound(bounds: Bounds) -> Nat:
  Bounds{items, bytes} = bounds
  items

def byte_bound(bounds: Bounds) -> Nat:
  Bounds{items, bytes} = bounds
  bytes

def Within(-bounds: Bounds, +queue: Queue) -> Type:
  L.E<N.Le(items(queue), item_bound(bounds)), N.Le(bytes(queue), byte_bound(bounds))>

def reserve_item_allowed(allowed: Bool, frames: List<&2, Frame>) -> Maybe<&2, Queue>:
  match allowed:
    case False{}: None{}
    case True{}: Some{Queue{frames, Header{}, None{}, False{}}}

def reserve_item(bounds: Bounds, queue: Queue) -> Maybe<&2, Queue>:
  match queue:
    case Queue{+frames, Idle{}, None{}, False{}}:
      reserve_item_allowed(Nat.is_lt(count(frames), item_bound(bounds)), frames)
    case _: None{}

def reserve_body_allowed(allowed: Bool, frames: List<&2, Frame>, declared: Nat) -> Maybe<&2, Queue>:
  match allowed:
    case False{}: None{}
    case True{}: Some{Queue{frames, Body{declared}, None{}, False{}}}

def reserve_body(bounds: Bounds, queue: Queue, +declared: Nat) -> Maybe<&2, Queue>:
  match queue:
    case Queue{+frames, Header{}, None{}, False{}}:
      reserve_body_allowed(Nat.is_le(declared, Nat.sub(byte_bound(bounds), byte_count(frames))), frames, declared)
    case _: None{}

def commit_body_checked(exact: Bool, frames: List<&2, Frame>, frame: Frame) -> Maybe<&2, Queue>:
  match exact:
    case False{}: None{}
    case True{}: Some{Queue{append(frames, frame), Idle{}, None{}, False{}}}

def commit_body(queue: Queue, +frame: Frame) -> Maybe<&2, Queue>:
  match queue:
    case Queue{frames, Body{declared}, None{}, False{}}:
      commit_body_checked(Nat.is_eq(frame_size(frame), declared), frames, frame)
    case _: None{}

# Terminal publication drops only the unfinished reservation. Every complete
# frame remains queued, so the terminal event cannot overtake any one of them.
def finish_reader(queue: Queue, end: End) -> Queue:
  Queue{frames, phase, terminal, stopped} = queue
  Queue{frames, Ended{}, Some{end}, stopped}

def cancel(queue: Queue) -> Queue:
  Queue{frames, phase, terminal, stopped} = queue
  Queue{frames, phase, terminal, True{}}

# The producer can observe cancellation irrespective of capacity. The native
# bridge must account for wakeup/read return; no fairness is assumed here.
def stopped_return(queue: Queue) -> Maybe<&2, Queue>:
  match queue:
    case Queue{frames, Idle{}, terminal, True{}}:
      Some{Queue{frames, Ended{}, Some{Eof{}}, True{}}}
    case Queue{frames, Header{}, terminal, True{}}:
      Some{Queue{frames, Ended{}, Some{Eof{}}, True{}}}
    case Queue{frames, Body{declared}, terminal, True{}}:
      Some{Queue{frames, Ended{}, Some{Eof{}}, True{}}}
    case _: None{}

type Selection is Data:
  Selected{frame: Frame, rest: Queue}
  Terminal{end: End, rest: Queue}
  Blocked{}

def select(queue: Queue) -> Selection:
  match queue:
    case Queue{Con{frame, rest}, phase, terminal, stopped}:
      Selected{frame, Queue{rest, phase, terminal, stopped}}
    case Queue{Nil{}, phase, Some{end}, stopped}:
      Terminal{end, Queue{Nil{}, phase, None{}, stopped}}
    case Queue{Nil{}, phase, None{}, stopped}: Blocked{}

# Eligibility is a classification predicate only. It grants no certificate,
# authentication or access permission and cannot bypass an ineligible head.
def select_if_head(eligible: Bool, frame: Frame, rest: List<&2, Frame>, phase: Phase,
  terminal: Maybe<&2, End>, stopped: Bool) -> Maybe<&2, Selection>:
  match eligible:
    case False{}: None{}
    case True{}: Some{Selected{frame, Queue{rest, phase, terminal, stopped}}}

def select_if(~eligible: Frame -> Bool, queue: Queue) -> Maybe<&2, Selection>:
  match queue:
    case Queue{Nil{}, phase, terminal, stopped}: None{}
    case Queue{Con{+frame, rest}, phase, terminal, stopped}:
      select_if_head(eligible(frame), frame, rest, phase, terminal, stopped)

# Necessary arithmetic of actual source updates; no final counter equality is
# supplied by the caller as an invariant-preservation conclusion.
law add_zero_right:
  for n: Nat
  {Nat.add(n, 0n) == n : Nat}
def add_zero_right(n):
  match n:
    case 0n: {==}
    case 1n+p: Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, add_zero_right(p))

law add_associative:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}
def add_associative(a, b, c):
  match a:
    case 0n: {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), add_associative(p, b, c))

law subtract_zero_right:
  for n: Nat
  {Nat.sub(n, 0n) == n : Nat}
def subtract_zero_right(n):
  match n:
    case 0n: {==}
    case 1n+p: {==}

law subtract_added_prefix:
  for +prefix: Nat
  for +n: Nat
  {Nat.sub(Nat.add(prefix, n), prefix) == n : Nat}
def subtract_added_prefix(prefix, n):
  match prefix:
    case 0n: subtract_zero_right(n)
    case 1n+p: subtract_added_prefix(p, n)

law count_after_append:
  for +frames: List<&2, Frame>
  for frame: Frame
  {count(append(frames, frame)) == 1n+count(frames) : Nat}
def count_after_append(frames, frame):
  match frames:
    case Nil{}: {==}
    case Con{head, +rest}:
      Equal.cong(Nat, Nat, n => 1n+n, count(append(rest, frame)), 1n+count(rest), count_after_append(rest, frame))

law bytes_after_append:
  for +frames: List<&2, Frame>
  for +frame: Frame
  {byte_count(append(frames, frame)) == Nat.add(byte_count(frames), frame_size(frame)) : Nat}
def bytes_after_append(frames, frame):
  match frames:
    case Nil{}: add_zero_right(frame_size(frame))
    case Con{+head, +rest}:
      Equal.trans(Nat, Nat.add(frame_size(head), byte_count(append(rest, frame))),
        Nat.add(frame_size(head), Nat.add(byte_count(rest), frame_size(frame))),
        Nat.add(Nat.add(frame_size(head), byte_count(rest)), frame_size(frame)),
        Equal.cong(Nat, Nat, n => Nat.add(frame_size(head), n),
          byte_count(append(rest, frame)), Nat.add(byte_count(rest), frame_size(frame)), bytes_after_append(rest, frame)),
        Equal.sym(Nat, Nat.add(Nat.add(frame_size(head), byte_count(rest)), frame_size(frame)),
          Nat.add(frame_size(head), Nat.add(byte_count(rest), frame_size(frame))),
          add_associative(frame_size(head), byte_count(rest), frame_size(frame))))

law lt_entails_successor_bound:
  for n: Nat
  for limit: Nat
  for less: {Nat.is_lt(n, limit) == True{} : Bool}
  N.Le(1n+n, limit)
def lt_entails_successor_bound(n, limit, less):
  match n limit:
    case 0n 0n: F.absurd_boolean(Empty, less)
    case 0n 1n+k: Unit{}
    case 1n+n 0n: F.absurd_boolean(Empty, less)
    case 1n+n 1n+limit: lt_entails_successor_bound(n, limit, less)

law equality_test_is_literal:
  for +n: Nat
  for +m: Nat
  for equal: {Nat.is_eq(n, m) == True{} : Bool}
  {n == m : Nat}
def equality_test_is_literal(n, m, equal):
  match n m:
    case 0n 0n: {==}
    case 0n 1n+m: F.absurd_boolean({0n == 1n+m : Nat}, equal)
    case 1n+n 0n: F.absurd_boolean({1n+n == 0n : Nat}, equal)
    case 1n+n 1n+m: Equal.cong(Nat, Nat, n => 1n+n, n, m, equality_test_is_literal(n, m, equal))

law unused_capacity_entails_total_bound:
  for +used: Nat
  for +limit: Nat
  for +size: Nat
  for before: N.Le(used, limit)
  for unused: N.Le(size, Nat.sub(limit, used))
  N.Le(Nat.add(used, size), limit)
def unused_capacity_entails_total_bound(used, limit, size, before, unused):
  match used limit:
    case 0n 0n: unused
    case 0n 1n+limit: unused
    case 1n+used 0n: match before:
    case 1n+used 1n+limit: unused_capacity_entails_total_bound(used, limit, size, before, unused)

law drop_sum_prefix_bound:
  for prefix: Nat
  for +n: Nat
  for +limit: Nat
  for bounded: N.Le(Nat.add(prefix, n), limit)
  N.Le(n, limit)
def drop_sum_prefix_bound(prefix, n, limit, bounded):
  match prefix:
    case 0n: bounded
    case 1n+ +p:
      drop_sum_prefix_bound(p, n, limit, N.le_weaken_successor(Nat.add(p, n), limit, bounded))

law prefix_within_sum:
  for n: Nat
  for +suffix: Nat
  N.Le(n, Nat.add(n, suffix))
def prefix_within_sum(n, suffix):
  match n:
    case 0n: Unit{}
    case 1n+k: prefix_within_sum(k, suffix)

def OptionalWithin(result: Maybe<&2, Queue>, -bounds: Bounds) -> Type:
  match result:
    case None{}: Unit
    case Some{queue}: Within(bounds, queue)

def item_allowed_safe(allowed: Bool, +frames: List<&2, Frame>, +bounds: Bounds,
  checked: {Nat.is_lt(count(frames), item_bound(bounds)) == allowed : Bool},
  before: Within(bounds, Queue{frames, Idle{}, None{}, False{}})) ->
  OptionalWithin(reserve_item_allowed(allowed, frames), bounds):
  match allowed:
    case False{}: Unit{}
    case True{}:
      L.Both{old_items, old_bytes} = before
      L.Both{lt_entails_successor_bound(count(frames), item_bound(bounds), checked), old_bytes}

law item_reservation_preserves_bounds:
  for +bounds: Bounds
  for +queue: Queue
  for before: Within(bounds, queue)
  OptionalWithin(reserve_item(bounds, queue), bounds)
def item_reservation_preserves_bounds(bounds, queue, before):
  match queue:
    case Queue{+frames, Idle{}, None{}, False{}}:
      item_allowed_safe(Nat.is_lt(count(frames), item_bound(bounds)), frames, bounds, {==}, before)
    case Queue{frames, Idle{}, None{}, True{}}: Unit{}
    case Queue{frames, Idle{}, Some{end}, stopped}: Unit{}
    case Queue{frames, Header{}, terminal, stopped}: Unit{}
    case Queue{frames, Body{declared}, terminal, stopped}: Unit{}
    case Queue{frames, Ended{}, terminal, stopped}: Unit{}

def body_allowed_safe(allowed: Bool, +frames: List<&2, Frame>, +declared: Nat, +bounds: Bounds,
  checked: {Nat.is_le(declared, Nat.sub(byte_bound(bounds), byte_count(frames))) == allowed : Bool},
  before: Within(bounds, Queue{frames, Header{}, None{}, False{}})) ->
  OptionalWithin(reserve_body_allowed(allowed, frames, declared), bounds):
  match allowed:
    case False{}: Unit{}
    case True{}:
      L.Both{old_items, old_bytes} = before
      L.Both{old_items, unused_capacity_entails_total_bound(byte_count(frames), byte_bound(bounds), declared,
        old_bytes, N.actual_boolean_as_le(declared, Nat.sub(byte_bound(bounds), byte_count(frames)), checked))}

law byte_reservation_preserves_bounds:
  for +bounds: Bounds
  for +queue: Queue
  for +declared: Nat
  for before: Within(bounds, queue)
  OptionalWithin(reserve_body(bounds, queue, declared), bounds)
def byte_reservation_preserves_bounds(bounds, queue, declared, before):
  match queue:
    case Queue{+frames, Header{}, None{}, False{}}:
      body_allowed_safe(Nat.is_le(declared, Nat.sub(byte_bound(bounds), byte_count(frames))),
        frames, declared, bounds, {==}, before)
    case Queue{frames, Header{}, None{}, True{}}: Unit{}
    case Queue{frames, Header{}, Some{end}, stopped}: Unit{}
    case Queue{frames, Idle{}, terminal, stopped}: Unit{}
    case Queue{frames, Body{size}, terminal, stopped}: Unit{}
    case Queue{frames, Ended{}, terminal, stopped}: Unit{}

def committed_safe(exact: Bool, +frames: List<&2, Frame>, +declared: Nat,
  +frame: Frame, +bounds: Bounds, checked: {Nat.is_eq(frame_size(frame), declared) == exact : Bool},
  before: Within(bounds, Queue{frames, Body{declared}, None{}, False{}})) ->
  OptionalWithin(commit_body_checked(exact, frames, frame), bounds):
  match exact:
    case False{}: Unit{}
    case True{}:
      L.Both{old_items, old_bytes} = before
      L.Both{
        (%Equal.sym(Nat, count(append(frames, frame)), 1n+count(frames), count_after_append(frames, frame)) :
          N.Le(_, item_bound(bounds)) old_items),
        (%Equal.sym(Nat, byte_count(append(frames, frame)), Nat.add(byte_count(frames), frame_size(frame)),
            bytes_after_append(frames, frame)) : N.Le(_, byte_bound(bounds))
          %Equal.sym(Nat, frame_size(frame), declared, equality_test_is_literal(frame_size(frame), declared, checked)) :
            N.Le(Nat.add(byte_count(frames), _), byte_bound(bounds)) old_bytes)}

law completed_body_preserves_bounds:
  for +bounds: Bounds
  for +queue: Queue
  for +frame: Frame
  for before: Within(bounds, queue)
  OptionalWithin(commit_body(queue, frame), bounds)
def completed_body_preserves_bounds(bounds, queue, frame, before):
  match queue:
    case Queue{+frames, Body{+declared}, None{}, False{}}:
      committed_safe(Nat.is_eq(frame_size(frame), declared), frames, declared, frame, bounds, {==}, before)
    case Queue{frames, Body{declared}, None{}, True{}}: Unit{}
    case Queue{frames, Body{declared}, Some{end}, stopped}: Unit{}
    case Queue{frames, Idle{}, terminal, stopped}: Unit{}
    case Queue{frames, Header{}, terminal, stopped}: Unit{}
    case Queue{frames, Ended{}, terminal, stopped}: Unit{}

# These equations match the actual mutable-counter updates after pop_front.
law selected_item_counter_is_actual_subtraction:
  for phase: Phase
  for frame: Frame
  for +rest: List<&2, Frame>
  {occupied_items(phase, rest) == Nat.sub(occupied_items(phase, Con{frame, rest}), 1n) : Nat}
def selected_item_counter_is_actual_subtraction(phase, frame, rest):
  match phase:
    case Idle{}: Equal.sym(Nat, Nat.sub(count(rest), 0n), count(rest), subtract_zero_right(count(rest)))
    case Header{}: {==}
    case Body{declared}: {==}
    case Ended{}: Equal.sym(Nat, Nat.sub(count(rest), 0n), count(rest), subtract_zero_right(count(rest)))

law selected_byte_counter_is_actual_subtraction:
  for phase: Phase
  for +frame: Frame
  for +rest: List<&2, Frame>
  {Nat.sub(occupied_bytes(phase, Con{frame, rest}), frame_size(frame)) == occupied_bytes(phase, rest) : Nat}
def selected_byte_counter_is_actual_subtraction(phase, frame, rest):
  match phase:
    case Body{+declared}:
      Equal.trans(Nat, Nat.sub(Nat.add(Nat.add(frame_size(frame), byte_count(rest)), declared), frame_size(frame)),
        Nat.sub(Nat.add(frame_size(frame), Nat.add(byte_count(rest), declared)), frame_size(frame)),
        Nat.add(byte_count(rest), declared),
        Equal.cong(Nat, Nat, total => Nat.sub(total, frame_size(frame)),
          Nat.add(Nat.add(frame_size(frame), byte_count(rest)), declared),
          Nat.add(frame_size(frame), Nat.add(byte_count(rest), declared)),
          add_associative(frame_size(frame), byte_count(rest), declared)),
        subtract_added_prefix(frame_size(frame), Nat.add(byte_count(rest), declared)))
    case Idle{}: subtract_added_prefix(frame_size(frame), byte_count(rest))
    case Header{}: subtract_added_prefix(frame_size(frame), byte_count(rest))
    case Ended{}: subtract_added_prefix(frame_size(frame), byte_count(rest))

def selected_items_safe(phase: Phase, -frame: Frame, +rest: List<&2, Frame>, +limit: Nat,
  before: N.Le(occupied_items(phase, Con{frame, rest}), limit)) ->
  N.Le(occupied_items(phase, rest), limit):
  match phase:
    case Idle{}: N.le_weaken_successor(count(rest), limit, before)
    case Header{}: N.le_weaken_successor(1n+count(rest), limit, before)
    case Body{declared}: N.le_weaken_successor(1n+count(rest), limit, before)
    case Ended{}: N.le_weaken_successor(count(rest), limit, before)

def selected_bytes_safe(phase: Phase, +frame: Frame, +rest: List<&2, Frame>, +limit: Nat,
  before: N.Le(occupied_bytes(phase, Con{frame, rest}), limit)) ->
  N.Le(occupied_bytes(phase, rest), limit):
  match phase:
    case Body{+declared}:
      drop_sum_prefix_bound(frame_size(frame), Nat.add(byte_count(rest), declared), limit,
        (%add_associative(frame_size(frame), byte_count(rest), declared) : N.Le(_, limit) before))
    case Idle{}: drop_sum_prefix_bound(frame_size(frame), byte_count(rest), limit, before)
    case Header{}: drop_sum_prefix_bound(frame_size(frame), byte_count(rest), limit, before)
    case Ended{}: drop_sum_prefix_bound(frame_size(frame), byte_count(rest), limit, before)

def SelectionWithin(selection: Selection, -bounds: Bounds) -> Type:
  match selection:
    case Selected{frame, rest}: Within(bounds, rest)
    case Terminal{end, rest}: Within(bounds, rest)
    case Blocked{}: Unit

law fifo_selection_preserves_bounds:
  for +bounds: Bounds
  for +queue: Queue
  for before: Within(bounds, queue)
  SelectionWithin(select(queue), bounds)
def fifo_selection_preserves_bounds(bounds, queue, before):
  match queue:
    case Queue{Con{+frame, +rest}, +phase, terminal, stopped}:
      L.Both{old_items, old_bytes} = before
      L.Both{selected_items_safe(phase, frame, rest, item_bound(bounds), old_items),
        selected_bytes_safe(phase, frame, rest, byte_bound(bounds), old_bytes)}
    case Queue{Nil{}, phase, Some{end}, stopped}: before
    case Queue{Nil{}, phase, None{}, stopped}: Unit{}

law cancellation_preserves_bounds:
  for -bounds: Bounds
  for queue: Queue
  for before: Within(bounds, queue)
  Within(bounds, cancel(queue))
def cancellation_preserves_bounds(bounds, queue, before):
  match queue:
    case Queue{frames, phase, terminal, stopped}: before

law terminal_publication_preserves_bounds:
  for +bounds: Bounds
  for queue: Queue
  for -end: End
  for before: Within(bounds, queue)
  Within(bounds, finish_reader(queue, end))
def terminal_publication_preserves_bounds(bounds, queue, end, before):
  match queue:
    case Queue{frames, Idle{}, terminal, stopped}: before
    case Queue{frames, Ended{}, terminal, stopped}: before
    case Queue{+frames, Header{}, terminal, stopped}:
      L.Both{old_items, old_bytes} = before
      L.Both{N.le_weaken_successor(count(frames), item_bound(bounds), old_items), old_bytes}
    case Queue{+frames, Body{+declared}, terminal, stopped}:
      L.Both{old_items, old_bytes} = before
      L.Both{N.le_weaken_successor(count(frames), item_bound(bounds), old_items),
        N.le_transitive(byte_count(frames), Nat.add(byte_count(frames), declared), byte_bound(bounds),
          prefix_within_sum(byte_count(frames), declared), old_bytes)}
