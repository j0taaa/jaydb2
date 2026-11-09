# Constructive enabled-step progress for the real bounded queue operations.
# These finite paths do not postulate that an OS thread is eventually scheduled.
# Returning poll/read/wakeup/join operations remain explicit native boundaries.
import Base
import ../contract/Logic.bend as L
import ./HandleCardinality.bend as N
import ./FrameQueue.bend as Q

# Each edge is an equality about the actual select function, retaining every
# frame. The terminal is never selected by a queued-frame edge.
def SelectPath(frames: List<&2, Q.Frame>, -before: Q.Queue, -after: Q.Queue) -> Type:
  match frames:
    case Nil{}: {before == after : Q.Queue}
    case Con{frame, rest}:
      &next: Q.Queue -> L.E<{Q.select(before) == Q.Selected{frame, next} : Q.Selection},
        SelectPath(rest, next, after)>

def Emptying(-queue: Q.Queue) -> Type:
  &after: Q.Queue -> L.E<SelectPath(Q.frames(queue), queue, after),
    {Q.frames(after) == Nil{} : List<&2, Q.Frame>}>

# No assumption about final FIFO/emptiness/completeness is accepted. Induction
# constructs one actual head-pop for each member of the finite starting queue.
law any_finite_queued_backlog_has_an_actual_finite_head_pop_path:
  for +frames: List<&2, Q.Frame>
  for +phase: Q.Phase
  for +terminal: Maybe<&2, Q.End>
  for +stopped: Bool
  SelectPath(frames, Q.Queue{frames, phase, terminal, stopped}, Q.Queue{Nil{}, phase, terminal, stopped})
def any_finite_queued_backlog_has_an_actual_finite_head_pop_path(frames, phase, terminal, stopped):
  match frames:
    case Nil{}: {==}
    case Con{frame, +rest}:
      (Q.Queue{rest, phase, terminal, stopped}, L.Both{{==},
        any_finite_queued_backlog_has_an_actual_finite_head_pop_path(rest, phase, terminal, stopped)})

law every_queue_can_release_all_queued_capacity_in_exactly_its_finite_backlog:
  for queue: Q.Queue
  Emptying(queue)
def every_queue_can_release_all_queued_capacity_in_exactly_its_finite_backlog(queue):
  match queue:
    case Q.Queue{+frames, +phase, +terminal, +stopped}:
      (Q.Queue{Nil{}, phase, terminal, stopped},
        L.Both{any_finite_queued_backlog_has_an_actual_finite_head_pop_path(frames, phase, terminal, stopped), {==}})

# The native item reservation guard is independent of body length, so even an
# empty frame consumes one item. Draining a full item queue enables one header
# reservation under the positive bound checked by FrameQueue::start.
law draining_any_idle_queue_enables_the_next_item_reservation:
  for +frames: List<&2, Q.Frame>
  for +capacity_minus_one: Nat
  for +byte_limit: Nat
  L.E<SelectPath(frames, Q.Queue{frames, Q.Idle{}, None{}, False{}}, Q.Queue{Nil{}, Q.Idle{}, None{}, False{}}),
    {Q.reserve_item(Q.Bounds{1n+capacity_minus_one, byte_limit}, Q.Queue{Nil{}, Q.Idle{}, None{}, False{}}) ==
      Some{Q.Queue{Nil{}, Q.Header{}, None{}, False{}}} : Maybe<&2, Q.Queue>}>
def draining_any_idle_queue_enables_the_next_item_reservation(frames, capacity_minus_one, byte_limit):
  L.Both{any_finite_queued_backlog_has_an_actual_finite_head_pop_path(frames, Q.Idle{}, None{}, False{}), {==}}

# Admission facts give size<=byteLimit because start requires the byte bound to
# fit every host-allocatable accepted message. No current free-space/fairness
# proposition is supplied. The constructed pop path releases enough capacity.
law draining_any_header_queue_enables_every_legal_body_reservation:
  for +frames: List<&2, Q.Frame>
  for +item_limit: Nat
  for +byte_limit: Nat
  for +declared: Nat
  for fits: {Nat.is_le(declared, byte_limit) == True{} : Bool}
  L.E<SelectPath(frames, Q.Queue{frames, Q.Header{}, None{}, False{}}, Q.Queue{Nil{}, Q.Header{}, None{}, False{}}),
    {Q.reserve_body(Q.Bounds{item_limit, byte_limit}, Q.Queue{Nil{}, Q.Header{}, None{}, False{}}, declared) ==
      Some{Q.Queue{Nil{}, Q.Body{declared}, None{}, False{}}} : Maybe<&2, Q.Queue>}>
def draining_any_header_queue_enables_every_legal_body_reservation(frames, item_limit, byte_limit, declared, fits):
  L.Both{any_finite_queued_backlog_has_an_actual_finite_head_pop_path(frames, Q.Header{}, None{}, False{}),
    (%Equal.sym(Nat, Nat.sub(byte_limit, 0n), byte_limit, Q.subtract_zero_right(byte_limit)) :
      {Q.reserve_body_allowed(Nat.is_le(declared, _), Nil{}, declared) ==
        Some{Q.Queue{Nil{}, Q.Body{declared}, None{}, False{}}} : Maybe<&2, Q.Queue>}
      %Equal.sym(Bool, Nat.is_le(declared, byte_limit), True{}, fits) :
        {Q.reserve_body_allowed(_, Nil{}, declared) == Some{Q.Queue{Nil{}, Q.Body{declared}, None{}, False{}}} : Maybe<&2, Q.Queue>}
      {==})}

# A terminal already published by the reader cannot overtake even the last
# complete queued frame. After the exact pop path, it is immediately selectable.
law every_published_terminal_follows_all_preceding_complete_frames:
  for +frames: List<&2, Q.Frame>
  for +phase: Q.Phase
  for +end: Q.End
  for +stopped: Bool
  L.E<SelectPath(frames, Q.Queue{frames, phase, Some{end}, stopped}, Q.Queue{Nil{}, phase, Some{end}, stopped}),
    {Q.select(Q.Queue{Nil{}, phase, Some{end}, stopped}) ==
      Q.Terminal{end, Q.Queue{Nil{}, phase, None{}, stopped}} : Q.Selection}>
def every_published_terminal_follows_all_preceding_complete_frames(frames, phase, end, stopped):
  L.Both{any_finite_queued_backlog_has_an_actual_finite_head_pop_path(frames, phase, Some{end}, stopped), {==}}

# Cancellation cannot erase a live reservation before the reader actually
# returns. Native close first sets stopped and drops its cancellation endpoint;
# the reader's return then performs finish_reader and is always joined.
law cancellation_retains_every_occupied_counter_until_reader_return:
  for +queue: Q.Queue
  L.E<{Q.items(Q.cancel(queue)) == Q.items(queue) : Nat},
    {Q.bytes(Q.cancel(queue)) == Q.bytes(queue) : Nat}>
def cancellation_retains_every_occupied_counter_until_reader_return(queue):
  match queue:
    case Q.Queue{frames, phase, terminal, stopped}: L.Both{{==}, {==}}

def CancellationReady(+queue: Q.Queue) -> Type:
  match queue:
    case Q.Queue{frames, Q.Ended{}, terminal, stopped}: Unit
    case Q.Queue{frames, Q.Idle{}, terminal, stopped}:
      {Q.stopped_return(Q.cancel(queue)) == Some{Q.finish_reader(Q.cancel(queue), Q.Eof{})} : Maybe<&2, Q.Queue>}
    case Q.Queue{frames, Q.Header{}, terminal, stopped}:
      {Q.stopped_return(Q.cancel(queue)) == Some{Q.finish_reader(Q.cancel(queue), Q.Eof{})} : Maybe<&2, Q.Queue>}
    case Q.Queue{frames, Q.Body{declared}, terminal, stopped}:
      {Q.stopped_return(Q.cancel(queue)) == Some{Q.finish_reader(Q.cancel(queue), Q.Eof{})} : Maybe<&2, Q.Queue>}

law cancellation_is_observable_without_item_or_byte_capacity:
  for queue: Q.Queue
  CancellationReady(queue)
def cancellation_is_observable_without_item_or_byte_capacity(queue):
  match queue:
    case Q.Queue{frames, Q.Ended{}, terminal, stopped}: Unit{}
    case Q.Queue{frames, Q.Idle{}, terminal, stopped}: {==}
    case Q.Queue{frames, Q.Header{}, terminal, stopped}: {==}
    case Q.Queue{frames, Q.Body{declared}, terminal, stopped}: {==}

law actual_reader_return_releases_only_the_unfinished_reservation:
  for +queue: Q.Queue
  for +end: Q.End
  L.E<{Q.frames(Q.finish_reader(queue, end)) == Q.frames(queue) : List<&2, Q.Frame>},
    L.E<{Q.items(Q.finish_reader(queue, end)) == Q.count(Q.frames(queue)) : Nat},
      {Q.bytes(Q.finish_reader(queue, end)) == Q.byte_count(Q.frames(queue)) : Nat}>>
def actual_reader_return_releases_only_the_unfinished_reservation(queue, end):
  match queue:
    case Q.Queue{frames, phase, terminal, stopped}: L.Both{{==}, L.Both{{==}, {==}}}

law cancelled_body_cannot_be_committed_even_after_its_read_returns:
  for +frames: List<&2, Q.Frame>
  for +declared: Nat
  for +terminal: Maybe<&2, Q.End>
  for +stopped: Bool
  for +frame: Q.Frame
  {Q.commit_body(Q.cancel(Q.Queue{frames, Q.Body{declared}, terminal, stopped}), frame) == None{} : Maybe<&2, Q.Queue>}
def cancelled_body_cannot_be_committed_even_after_its_read_returns(frames, declared, terminal, stopped, frame):
  match terminal:
    case None{}: {==}
    case Some{end}: {==}
