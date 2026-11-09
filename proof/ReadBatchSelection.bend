# Actual no-refill, bounded, already-enqueued head-prefix selection.
# Eligibility classifies a candidate; it is not authority to read any state.
import Base
import ../contract/Logic.bend as L
import ./Foundations.bend as F
import ./HandleCardinality.bend as N
import ./FrameQueue.bend as Q

type Batch is Data:
  Batch{frames: List<&2, Q.Frame>, after: Q.Queue}

def selected(batch: Batch) -> List<&2, Q.Frame>:
  Batch{frames, after} = batch
  frames

def after(batch: Batch) -> Q.Queue:
  Batch{frames, after} = batch
  after

def rebuild(queue: Q.Queue, frames: List<&2, Q.Frame>) -> Q.Queue:
  Q.Queue{previous, phase, terminal, stopped} = queue
  Q.Queue{frames, phase, terminal, stopped}

def prepend_frame(frame: Q.Frame, queue: Q.Queue) -> Q.Queue:
  Q.Queue{frames, phase, terminal, stopped} = queue
  Q.Queue{Con{frame, frames}, phase, terminal, stopped}

def prepend_batch(frame: Q.Frame, batch: Batch) -> Batch:
  Batch{frames, after} = batch
  Batch{Con{frame, frames}, after}

def collect_decision(qualifies: Bool, frame: Q.Frame, original: Q.Queue,
  rest: Q.Queue, recurse: Q.Queue -> Batch) -> Batch:
  match qualifies:
    case False{}: Batch{Nil{}, original}
    case True{}: prepend_batch(frame, recurse(rest))

def collect(~eligible: Q.Frame -> Bool, slots: Nat, queue: Q.Queue) -> Batch:
  match slots queue:
    case 0n queue: Batch{Nil{}, queue}
    case 1n+remaining Q.Queue{Nil{}, phase, terminal, stopped}:
      Batch{Nil{}, Q.Queue{Nil{}, phase, terminal, stopped}}
    case 1n+remaining Q.Queue{Con{+frame, +rest}, +phase, +terminal, +stopped}:
      collect_decision(eligible(frame), frame,
        Q.Queue{Con{frame, rest}, phase, terminal, stopped}, Q.Queue{rest, phase, terminal, stopped},
        next => collect(eligible, remaining, next))

def AllEligible(~eligible: Q.Frame -> Bool, frames: List<&2, Q.Frame>) -> Type:
  match frames:
    case Nil{}: Unit
    case Con{head, rest}: L.E<{eligible(head) == True{} : Bool}, AllEligible(eligible, rest)>

# The equality also fixes all metadata, so collection cannot consume the input
# terminal, change the reader reservation, or change the cancellation flag.
def Split(-before: Q.Queue, +batch: Batch) -> Type:
  {before == rebuild(after(batch), Q.concatenate(selected(batch), Q.frames(after(batch)))) : Q.Queue}

def Collected(~eligible: Q.Frame -> Bool, -slots: Nat, -before: Q.Queue) -> Type:
  &batch: Batch ->
    L.E<{collect(eligible, slots, before) == batch : Batch},
      L.E<Split(before, batch),
        L.E<AllEligible(eligible, selected(batch)), N.Le(Q.count(selected(batch)), slots)>>>

def lift_split(+frame: Q.Frame, -rest: Q.Queue, batch: Batch,
  split: Split(rest, batch)) -> Split(prepend_frame(frame, rest), prepend_batch(frame, batch)):
  match batch:
    case Batch{frames, Q.Queue{after, phase, terminal, stopped}}:
      Equal.cong(Q.Queue, Q.Queue, queue => prepend_frame(frame, queue),
        rest, Q.Queue{Q.concatenate(frames, after), phase, terminal, stopped}, split)

def collected_step(~eligible: Q.Frame -> Bool, -remaining: Nat, +frame: Q.Frame,
  -phase: Q.Phase, -terminal: Maybe<&2, Q.End>, -stopped: Bool, -rest: List<&2, Q.Frame>,
  +qualifies: {eligible(frame) == True{} : Bool},
  later: Collected(eligible, remaining, Q.Queue{rest, phase, terminal, stopped})) ->
  Collected(eligible, 1n+remaining, Q.Queue{Con{frame, rest}, phase, terminal, stopped}):
  match later:
    case (Batch{+frames, +after}, L.Both{actual, L.Both{split, L.Both{classified, bounded}}}):
      (Batch{Con{frame, frames}, after}, L.Both{(%Equal.sym(Bool, eligible(frame), True{}, qualifies) :
          {collect_decision(_, frame, Q.Queue{Con{frame, rest}, phase, terminal, stopped},
            Q.Queue{rest, phase, terminal, stopped}, next => collect(eligible, remaining, next)) ==
              Batch{Con{frame, frames}, after} : Batch}
          Equal.cong(Batch, Batch, batch => prepend_batch(frame, batch),
            collect(eligible, remaining, Q.Queue{rest, phase, terminal, stopped}), Batch{frames, after}, actual)), L.Both{lift_split(frame, Q.Queue{rest, phase, terminal, stopped}, Batch{frames, after}, split), L.Both{L.Both{qualifies, classified}, bounded}}})

def collected_decision(~eligible: Q.Frame -> Bool, qualifies: Bool, remaining: Nat,
  +frame: Q.Frame, +rest: List<&2, Q.Frame>, +phase: Q.Phase,
  +terminal: Maybe<&2, Q.End>, +stopped: Bool,
  checked: {eligible(frame) == qualifies : Bool},
  recurse: Unit -> Collected(eligible, remaining, Q.Queue{rest, phase, terminal, stopped})) ->
  Collected(eligible, 1n+remaining, Q.Queue{Con{frame, rest}, phase, terminal, stopped}):
  match qualifies:
    case False{}:
      (Batch{Nil{}, Q.Queue{Con{frame, rest}, phase, terminal, stopped}}, L.Both{(%Equal.sym(Bool, eligible(frame), False{}, checked) :
          {collect_decision(_, frame, Q.Queue{Con{frame, rest}, phase, terminal, stopped},
            Q.Queue{rest, phase, terminal, stopped}, next => collect(eligible, remaining, next)) ==
              Batch{Nil{}, Q.Queue{Con{frame, rest}, phase, terminal, stopped}} : Batch}
          {==}), L.Both{{==}, L.Both{Unit{}, Unit{}}}})
    case True{}: collected_step(eligible, remaining, frame, phase, terminal, stopped, rest, checked, recurse(Unit{}))

law actual_collection_is_bounded_classified_head_prefix:
  for ~eligible: Q.Frame -> Bool
  for slots: Nat
  for queue: Q.Queue
  Collected(eligible, slots, queue)
def actual_collection_is_bounded_classified_head_prefix(eligible, slots, queue):
  match slots queue:
    case 0n Q.Queue{frames, phase, terminal, stopped}:
      (Batch{Nil{}, Q.Queue{frames, phase, terminal, stopped}}, L.Both{{==}, L.Both{{==}, L.Both{Unit{}, Unit{}}}})
    case 1n+remaining Q.Queue{Nil{}, phase, terminal, stopped}:
      (Batch{Nil{}, Q.Queue{Nil{}, phase, terminal, stopped}}, L.Both{{==}, L.Both{{==}, L.Both{Unit{}, Unit{}}}})
    case 1n+ +remaining Q.Queue{Con{+frame, +rest}, +phase, +terminal, +stopped}:
      collected_decision(eligible, eligible(frame), remaining, frame, rest, phase, terminal, stopped, {==},
        unit => actual_collection_is_bounded_classified_head_prefix(eligible, remaining,
          Q.Queue{rest, phase, terminal, stopped}))
