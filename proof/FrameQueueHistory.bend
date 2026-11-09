# Conservation over the real bounded-queue operations. Accepted and selected
# are specification histories, not new runtime logs or assumed FIFO results.
import Base
import ../contract/Logic.bend as L
import ./FrameQueue.bend as Q

type History is Data:
  History{queue: Q.Queue, accepted: List<&2, Q.Frame>, selected: List<&2, Q.Frame>}

def queue(history: History) -> Q.Queue:
  History{queue, accepted, selected} = history
  queue

def accepted(history: History) -> List<&2, Q.Frame>:
  History{queue, accepted, selected} = history
  accepted

def selected(history: History) -> List<&2, Q.Frame>:
  History{queue, accepted, selected} = history
  selected

def Conserved(+history: History) -> Type:
  {accepted(history) == Q.concatenate(selected(history), Q.frames(queue(history))) : List<&2, Q.Frame>}

def initial() -> History:
  History{Q.Queue{Nil{}, Q.Idle{}, None{}, False{}}, Nil{}, Nil{}}

def reserved(result: Maybe<&2, Q.Queue>, original: History) -> History:
  match result original:
    case None{} original: original
    case Some{next} History{previous, accepted, selected}: History{next, accepted, selected}

def committed(result: Maybe<&2, Q.Queue>, frame: Q.Frame, original: History) -> History:
  match result original:
    case None{} original: original
    case Some{next} History{previous, accepted, selected}:
      History{next, Q.append(accepted, frame), selected}

def consumed(selection: Q.Selection, original: History) -> History:
  match selection original:
    case Q.Blocked{} original: original
    case Q.Terminal{end, next} History{previous, accepted, selected}: History{next, accepted, selected}
    case Q.Selected{frame, next} History{previous, accepted, selected}:
      History{next, accepted, Q.append(selected, frame)}

type Action is Data:
  ReserveItem{}
  ReserveBody{size: Nat}
  CommitBody{frame: Q.Frame}
  Finish{end: Q.End}
  Cancel{}
  Select{}

# Disabled attempts stutter. The fixed native correspondence must cover all
# actual atomic effects; an unknown effect cannot be dropped from that bridge.
def step(bounds: Q.Bounds, action: Action, +history: History) -> History:
  match action:
    case ReserveItem{}: reserved(Q.reserve_item(bounds, queue(history)), history)
    case ReserveBody{size}: reserved(Q.reserve_body(bounds, queue(history), size), history)
    case CommitBody{+frame}: committed(Q.commit_body(queue(history), frame), frame, history)
    case Finish{end}:
      match history:
        case History{queue, accepted, selected}: History{Q.finish_reader(queue, end), accepted, selected}
    case Cancel{}:
      match history:
        case History{queue, accepted, selected}: History{Q.cancel(queue), accepted, selected}
    case Select{}: consumed(Q.select(queue(history)), history)

law append_after_concatenation:
  for +left: List<&2, Q.Frame>
  for +right: List<&2, Q.Frame>
  for +frame: Q.Frame
  {Q.append(Q.concatenate(left, right), frame) == Q.concatenate(left, Q.append(right, frame)) : List<&2, Q.Frame>}
def append_after_concatenation(left, right, frame):
  match left:
    case Nil{}: {==}
    case Con{+head, +rest}:
      Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, xs => Con{head, xs},
        Q.append(Q.concatenate(rest, right), frame), Q.concatenate(rest, Q.append(right, frame)),
        append_after_concatenation(rest, right, frame))

law selected_head_moves_to_history:
  for +selected: List<&2, Q.Frame>
  for +frame: Q.Frame
  for +rest: List<&2, Q.Frame>
  {Q.concatenate(Q.append(selected, frame), rest) == Q.concatenate(selected, Con{frame, rest}) : List<&2, Q.Frame>}
def selected_head_moves_to_history(selected, frame, rest):
  match selected:
    case Nil{}: {==}
    case Con{+head, +tail}:
      Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, xs => Con{head, xs},
        Q.concatenate(Q.append(tail, frame), rest), Q.concatenate(tail, Con{frame, rest}),
        selected_head_moves_to_history(tail, frame, rest))

def FramesPreserved(result: Maybe<&2, Q.Queue>, -old: List<&2, Q.Frame>) -> Type:
  match result:
    case None{}: Unit
    case Some{next}: {Q.frames(next) == old : List<&2, Q.Frame>}

def reserved_frame_case(allowed: Bool, -frames: List<&2, Q.Frame>) ->
  FramesPreserved(Q.reserve_item_allowed(allowed, frames), frames):
  match allowed:
    case False{}: Unit{}
    case True{}: {==}

law item_reservation_preserves_frames:
  for +bounds: Q.Bounds
  for +queue: Q.Queue
  FramesPreserved(Q.reserve_item(bounds, queue), Q.frames(queue))
def item_reservation_preserves_frames(bounds, queue):
  match queue:
    case Q.Queue{+frames, Q.Idle{}, None{}, False{}}:
      reserved_frame_case(Nat.is_lt(Q.count(frames), Q.item_bound(bounds)), frames)
    case Q.Queue{frames, Q.Idle{}, None{}, True{}}: Unit{}
    case Q.Queue{frames, Q.Idle{}, Some{end}, stopped}: Unit{}
    case Q.Queue{frames, Q.Header{}, terminal, stopped}: Unit{}
    case Q.Queue{frames, Q.Body{size}, terminal, stopped}: Unit{}
    case Q.Queue{frames, Q.Ended{}, terminal, stopped}: Unit{}

def reserved_body_frame_case(allowed: Bool, -frames: List<&2, Q.Frame>, -size: Nat) ->
  FramesPreserved(Q.reserve_body_allowed(allowed, frames, size), frames):
  match allowed:
    case False{}: Unit{}
    case True{}: {==}

law body_reservation_preserves_frames:
  for +bounds: Q.Bounds
  for +queue: Q.Queue
  for +size: Nat
  FramesPreserved(Q.reserve_body(bounds, queue, size), Q.frames(queue))
def body_reservation_preserves_frames(bounds, queue, size):
  match queue:
    case Q.Queue{+frames, Q.Header{}, None{}, False{}}:
      reserved_body_frame_case(Nat.is_le(size, Nat.sub(Q.byte_bound(bounds), Q.byte_count(frames))), frames, size)
    case Q.Queue{frames, Q.Header{}, None{}, True{}}: Unit{}
    case Q.Queue{frames, Q.Header{}, Some{end}, stopped}: Unit{}
    case Q.Queue{frames, Q.Idle{}, terminal, stopped}: Unit{}
    case Q.Queue{frames, Q.Body{declared}, terminal, stopped}: Unit{}
    case Q.Queue{frames, Q.Ended{}, terminal, stopped}: Unit{}

def CommitFrames(result: Maybe<&2, Q.Queue>, -old: List<&2, Q.Frame>, -frame: Q.Frame) -> Type:
  match result:
    case None{}: Unit
    case Some{next}: {Q.frames(next) == Q.append(old, frame) : List<&2, Q.Frame>}

def committed_frame_case(exact: Bool, -frames: List<&2, Q.Frame>, -frame: Q.Frame) ->
  CommitFrames(Q.commit_body_checked(exact, frames, frame), frames, frame):
  match exact:
    case False{}: Unit{}
    case True{}: {==}

law complete_body_appends_exact_frame:
  for +queue: Q.Queue
  for +frame: Q.Frame
  CommitFrames(Q.commit_body(queue, frame), Q.frames(queue), frame)
def complete_body_appends_exact_frame(queue, frame):
  match queue:
    case Q.Queue{+frames, Q.Body{size}, None{}, False{}}:
      committed_frame_case(Nat.is_eq(Q.frame_size(frame), size), frames, frame)
    case Q.Queue{frames, Q.Body{size}, None{}, True{}}: Unit{}
    case Q.Queue{frames, Q.Body{size}, Some{end}, stopped}: Unit{}
    case Q.Queue{frames, Q.Idle{}, terminal, stopped}: Unit{}
    case Q.Queue{frames, Q.Header{}, terminal, stopped}: Unit{}
    case Q.Queue{frames, Q.Ended{}, terminal, stopped}: Unit{}

def reserved_preserves(result: Maybe<&2, Q.Queue>, +original: History,
  conserved: Conserved(original), frames_same: FramesPreserved(result, Q.frames(queue(original)))) ->
  Conserved(reserved(result, original)):
  match result original:
    case None{} original: conserved
    case Some{+next} History{+previous, accepted, +selected}:
      %Equal.sym(List<&2, Q.Frame>, Q.frames(next), Q.frames(previous), frames_same) :
        {accepted == Q.concatenate(selected, _) : List<&2, Q.Frame>}
      conserved

def committed_preserves(result: Maybe<&2, Q.Queue>, +frame: Q.Frame, +original: History,
  conserved: Conserved(original), frames_same: CommitFrames(result, Q.frames(queue(original)), frame)) ->
  Conserved(committed(result, frame, original)):
  match result original:
    case None{} original: conserved
    case Some{+next} History{+previous, +accepted, +selected}:
      %Equal.sym(List<&2, Q.Frame>, Q.frames(next), Q.append(Q.frames(previous), frame), frames_same) :
        {Q.append(accepted, frame) == Q.concatenate(selected, _) : List<&2, Q.Frame>}
      Equal.trans(List<&2, Q.Frame>, Q.append(accepted, frame),
        Q.append(Q.concatenate(selected, Q.frames(previous)), frame),
        Q.concatenate(selected, Q.append(Q.frames(previous), frame)),
        Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, accepted => Q.append(accepted, frame),
          accepted, Q.concatenate(selected, Q.frames(previous)), conserved),
        append_after_concatenation(selected, Q.frames(previous), frame))

law actual_selection_preserves_conservation:
  for +history: History
  for conserved: Conserved(history)
  Conserved(consumed(Q.select(queue(history)), history))
def actual_selection_preserves_conservation(history, conserved):
  match history:
    case History{Q.Queue{Con{+frame, +rest}, phase, terminal, stopped}, +accepted, +selected}:
      Equal.trans(List<&2, Q.Frame>, accepted, Q.concatenate(selected, Con{frame, rest}),
        Q.concatenate(Q.append(selected, frame), rest), conserved,
        Equal.sym(List<&2, Q.Frame>, Q.concatenate(Q.append(selected, frame), rest),
          Q.concatenate(selected, Con{frame, rest}), selected_head_moves_to_history(selected, frame, rest)))
    case History{Q.Queue{Nil{}, phase, Some{end}, stopped}, accepted, selected}: conserved
    case History{Q.Queue{Nil{}, phase, None{}, stopped}, accepted, selected}: conserved

law atomic_step_preserves_conservation:
  for +bounds: Q.Bounds
  for +action: Action
  for +history: History
  for conserved: Conserved(history)
  Conserved(step(bounds, action, history))
def atomic_step_preserves_conservation(bounds, action, history, conserved):
  match action:
    case ReserveItem{}:
      reserved_preserves(Q.reserve_item(bounds, queue(history)), history, conserved,
        item_reservation_preserves_frames(bounds, queue(history)))
    case ReserveBody{+size}:
      reserved_preserves(Q.reserve_body(bounds, queue(history), size), history, conserved,
        body_reservation_preserves_frames(bounds, queue(history), size))
    case CommitBody{+frame}:
      committed_preserves(Q.commit_body(queue(history), frame), frame, history, conserved,
        complete_body_appends_exact_frame(queue(history), frame))
    case Finish{end}:
      match history:
        case History{Q.Queue{frames, phase, terminal, stopped}, accepted, selected}: conserved
    case Cancel{}:
      match history:
        case History{Q.Queue{frames, phase, terminal, stopped}, accepted, selected}: conserved
    case Select{}: actual_selection_preserves_conservation(history, conserved)

def run(+bounds: Q.Bounds, actions: List<&2, Action>, history: History) -> History:
  match actions:
    case Nil{}: history
    case Con{action, rest}: run(bounds, rest, step(bounds, action, history))

law every_interleaving_preserves_conservation:
  for +bounds: Q.Bounds
  for +actions: List<&2, Action>
  for +history: History
  for conserved: Conserved(history)
  Conserved(run(bounds, actions, history))
def every_interleaving_preserves_conservation(bounds, actions, history, conserved):
  match actions:
    case Nil{}: conserved
    case Con{+action, +rest}:
      every_interleaving_preserves_conservation(bounds, rest, step(bounds, action, history),
        atomic_step_preserves_conservation(bounds, action, history, conserved))

law actual_finite_history_is_fifo:
  for +bounds: Q.Bounds
  for +actions: List<&2, Action>
  Conserved(run(bounds, actions, initial()))
def actual_finite_history_is_fifo(bounds, actions):
  every_interleaving_preserves_conservation(bounds, actions, initial(), {==})

def reserved_within(-bounds: Q.Bounds, result: Maybe<&2, Q.Queue>, original: History,
  before: Q.Within(bounds, queue(original)), after: Q.OptionalWithin(result, bounds)) ->
  Q.Within(bounds, queue(reserved(result, original))):
  match result original:
    case None{} original: before
    case Some{next} History{previous, accepted, selected}: after

def committed_within(-bounds: Q.Bounds, result: Maybe<&2, Q.Queue>, frame: Q.Frame, original: History,
  before: Q.Within(bounds, queue(original)), after: Q.OptionalWithin(result, bounds)) ->
  Q.Within(bounds, queue(committed(result, frame, original))):
  match result original:
    case None{} original: before
    case Some{next} History{previous, accepted, selected}: after

def consumed_within(-bounds: Q.Bounds, result: Q.Selection, original: History,
  before: Q.Within(bounds, queue(original)), after: Q.SelectionWithin(result, bounds)) ->
  Q.Within(bounds, queue(consumed(result, original))):
  match result original:
    case Q.Blocked{} original: before
    case Q.Selected{frame, next} History{previous, accepted, selected}: after
    case Q.Terminal{end, next} History{previous, accepted, selected}: after

def copy_within(-bounds: Q.Bounds, -queue: Q.Queue, before: Q.Within(bounds, queue)) ->
  L.E<Q.Within(bounds, queue), Q.Within(bounds, queue)>:
  L.Both{+items, +bytes} = before
  L.Both{L.Both{items, bytes}, L.Both{items, bytes}}

def finished_history_within(+bounds: Q.Bounds, history: History, end: Q.End,
  before: Q.Within(bounds, queue(history))) -> Q.Within(bounds, queue(step(bounds, Finish{end}, history))):
  match history:
    case History{queue, accepted, selected}: Q.terminal_publication_preserves_bounds(bounds, queue, end, before)

def canceled_history_within(+bounds: Q.Bounds, history: History,
  before: Q.Within(bounds, queue(history))) -> Q.Within(bounds, queue(step(bounds, Cancel{}, history))):
  match history:
    case History{queue, accepted, selected}: Q.cancellation_preserves_bounds(bounds, queue, before)

def atomic_step_accounted(+bounds: Q.Bounds, +action: Action, +history: History,
  before_pair: L.E<Q.Within(bounds, queue(history)), Q.Within(bounds, queue(history))>) ->
  Q.Within(bounds, queue(step(bounds, action, history))):
  match action:
    case ReserveItem{}:
      L.Both{before, duplicate} = before_pair
      reserved_within(bounds, Q.reserve_item(bounds, queue(history)), history, before,
        Q.item_reservation_preserves_bounds(bounds, queue(history), duplicate))
    case ReserveBody{+size}:
      L.Both{before, duplicate} = before_pair
      reserved_within(bounds, Q.reserve_body(bounds, queue(history), size), history, before,
        Q.byte_reservation_preserves_bounds(bounds, queue(history), size, duplicate))
    case CommitBody{+frame}:
      L.Both{before, duplicate} = before_pair
      committed_within(bounds, Q.commit_body(queue(history), frame), frame, history, before,
        Q.completed_body_preserves_bounds(bounds, queue(history), frame, duplicate))
    case Finish{end}:
      L.Both{before, duplicate} = before_pair
      finished_history_within(bounds, history, end, before)
    case Cancel{}:
      L.Both{before, duplicate} = before_pair
      canceled_history_within(bounds, history, before)
    case Select{}:
      L.Both{before, duplicate} = before_pair
      consumed_within(bounds, Q.select(queue(history)), history, before,
        Q.fifo_selection_preserves_bounds(bounds, queue(history), duplicate))

law atomic_step_preserves_actual_accounting_bounds:
  for +bounds: Q.Bounds
  for +action: Action
  for +history: History
  for before: Q.Within(bounds, queue(history))
  Q.Within(bounds, queue(step(bounds, action, history)))
def atomic_step_preserves_actual_accounting_bounds(bounds, action, history, before):
  atomic_step_accounted(bounds, action, history, copy_within(bounds, queue(history), before))

law every_interleaving_preserves_actual_accounting_bounds:
  for +bounds: Q.Bounds
  for +actions: List<&2, Action>
  for +history: History
  for before: Q.Within(bounds, queue(history))
  Q.Within(bounds, queue(run(bounds, actions, history)))
def every_interleaving_preserves_actual_accounting_bounds(bounds, actions, history, before):
  match actions:
    case Nil{}: before
    case Con{+action, +rest}:
      every_interleaving_preserves_actual_accounting_bounds(bounds, rest, step(bounds, action, history),
        atomic_step_preserves_actual_accounting_bounds(bounds, action, history, before))

law initial_history_and_every_finite_interleaving_are_bounded:
  for +bounds: Q.Bounds
  for +actions: List<&2, Action>
  Q.Within(bounds, queue(run(bounds, actions, initial())))
def initial_history_and_every_finite_interleaving_are_bounded(bounds, actions):
  every_interleaving_preserves_actual_accounting_bounds(bounds, actions, initial(), L.Both{Unit{}, Unit{}})

law prefix_of_concatenation:
  for left: List<&2, Q.Frame>
  for +right: List<&2, Q.Frame>
  L.Prefix(Q.Frame, left, Q.concatenate(left, right))
def prefix_of_concatenation(left, right):
  match left:
    case Nil{}: Unit{}
    case Con{head, tail}: L.Both{{==}, prefix_of_concatenation(tail, right)}

def conserved_implies_prefix(+history: History, conserved: Conserved(history)) ->
  L.Prefix(Q.Frame, selected(history), accepted(history)):
  %Equal.sym(List<&2, Q.Frame>, accepted(history), Q.concatenate(selected(history), Q.frames(queue(history))), conserved) :
    L.Prefix(Q.Frame, selected(history), _)
  prefix_of_concatenation(selected(history), Q.frames(queue(history)))

law selected_frames_are_an_actual_reception_prefix:
  for +bounds: Q.Bounds
  for +actions: List<&2, Action>
  L.Prefix(Q.Frame, selected(run(bounds, actions, initial())), accepted(run(bounds, actions, initial())))
def selected_frames_are_an_actual_reception_prefix(bounds, actions):
  conserved_implies_prefix(run(bounds, actions, initial()), actual_finite_history_is_fifo(bounds, actions))
