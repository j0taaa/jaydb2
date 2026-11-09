# Unlike the fixed-snapshot collector lemma, this machine admits actual reader
# appends between select_if calls. Only the collector consumes queued frames.
# Its history records all completed receptions and every selected frame.
import Base
import ../contract/Logic.bend as L
import ./HandleCardinality.bend as N
import ./FrameQueue.bend as Q
import ./FrameQueueHistory.bend as H
import ./ReadBatchSelection.bend as S

type Producer is Data:
  ReserveItem{}
  ReserveBody{size: Nat}
  CommitBody{frame: Q.Frame}
  Finish{end: Q.End}
  Cancel{}

def producer_action(action: Producer) -> H.Action:
  match action:
    case ReserveItem{}: H.ReserveItem{}
    case ReserveBody{size}: H.ReserveBody{size}
    case CommitBody{frame}: H.CommitBody{frame}
    case Finish{end}: H.Finish{end}
    case Cancel{}: H.Cancel{}

type Collector is Data:
  Collector{history: H.History, remaining: Nat, open: Bool}

def history(collector: Collector) -> H.History:
  Collector{history, remaining, open} = collector
  history

def remaining(collector: Collector) -> Nat:
  Collector{history, remaining, open} = collector
  remaining

def batch(collector: Collector) -> List<&2, Q.Frame>:
  H.selected(history(collector))

def available(collector: Collector) -> Nat:
  Collector{history, remaining, open} = collector
  match open:
    case False{}: 0n
    case True{}: remaining

def collect_decision(eligible: Bool, +history: H.History, rest: Nat) -> Collector:
  match eligible:
    case False{}: Collector{history, 1n+rest, False{}}
    case True{}: Collector{H.consumed(Q.select(H.queue(history)), history), rest, True{}}

def attempt(~eligible: Q.Frame -> Bool, collector: Collector) -> Collector:
  match collector:
    case Collector{history, remaining, False{}}: Collector{history, remaining, False{}}
    case Collector{history, 0n, True{}}: Collector{history, 0n, True{}}
    case Collector{H.History{Q.Queue{Nil{}, phase, terminal, stopped}, accepted, selected}, 1n+rest, True{}}:
      Collector{H.History{Q.Queue{Nil{}, phase, terminal, stopped}, accepted, selected}, 1n+rest, False{}}
    case Collector{H.History{Q.Queue{Con{+head, tail}, phase, terminal, stopped}, accepted, selected}, 1n+rest, True{}}:
      collect_decision(eligible(head), H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, rest)

type Action is Data:
  Produce{action: Producer}
  TryCandidate{}

def advance(~eligible: Q.Frame -> Bool, bounds: Q.Bounds, action: Action, collector: Collector) -> Collector:
  match action collector:
    case Produce{action} Collector{history, remaining, open}:
      Collector{H.step(bounds, producer_action(action), history), remaining, open}
    case TryCandidate{} collector: attempt(eligible, collector)

def run(~eligible: Q.Frame -> Bool, +bounds: Q.Bounds, actions: List<&2, Action>, collector: Collector) -> Collector:
  match actions:
    case Nil{}: collector
    case Con{action, rest}: run(eligible, bounds, rest, advance(eligible, bounds, action, collector))

def Invariant(~eligible: Q.Frame -> Bool, -bounds: Q.Bounds, -limit: Nat, +collector: Collector) -> Type:
  L.E<H.Conserved(history(collector)),
    L.E<Q.Within(bounds, H.queue(history(collector))),
      L.E<S.AllEligible(eligible, batch(collector)),
        {Nat.add(Q.count(batch(collector)), remaining(collector)) == limit : Nat}>>>

def reserved_keeps_selected(result: Maybe<&2, Q.Queue>, +original: H.History) ->
  {H.selected(H.reserved(result, original)) == H.selected(original) : List<&2, Q.Frame>}:
  match result original:
    case None{} original: {==}
    case Some{next} H.History{previous, accepted, selected}: {==}

def committed_keeps_selected(result: Maybe<&2, Q.Queue>, frame: Q.Frame, +original: H.History) ->
  {H.selected(H.committed(result, frame, original)) == H.selected(original) : List<&2, Q.Frame>}:
  match result original:
    case None{} original: {==}
    case Some{next} H.History{previous, accepted, selected}: {==}

law producer_action_keeps_the_entire_selected_batch:
  for +bounds: Q.Bounds
  for +action: Producer
  for +previous: H.History
  {H.selected(H.step(bounds, producer_action(action), previous)) == H.selected(previous) : List<&2, Q.Frame>}
def producer_action_keeps_the_entire_selected_batch(bounds, action, previous):
  match action:
    case ReserveItem{}: reserved_keeps_selected(Q.reserve_item(bounds, H.queue(previous)), previous)
    case ReserveBody{+size}: reserved_keeps_selected(Q.reserve_body(bounds, H.queue(previous), size), previous)
    case CommitBody{+frame}: committed_keeps_selected(Q.commit_body(H.queue(previous), frame), frame, previous)
    case Finish{end}:
      match previous:
        case H.History{queue, accepted, selected}: {==}
    case Cancel{}:
      match previous:
        case H.History{queue, accepted, selected}: {==}

law add_successor_right:
  for n: Nat
  for +m: Nat
  {Nat.add(n, 1n+m) == 1n+Nat.add(n, m) : Nat}
def add_successor_right(n, m):
  match n:
    case 0n: {==}
    case 1n+p: Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 1n+m), 1n+Nat.add(p, m), add_successor_right(p, m))

law classified_append:
  for ~eligible: Q.Frame -> Bool
  for +frames: List<&2, Q.Frame>
  for +frame: Q.Frame
  for classified: S.AllEligible(eligible, frames)
  for checked: {eligible(frame) == True{} : Bool}
  S.AllEligible(eligible, Q.append(frames, frame))
def classified_append(eligible, frames, frame, classified, checked):
  match frames classified:
    case Nil{} unit: L.Both{checked, Unit{}}
    case Con{head, +rest} L.Both{head_checked, tail_checked}:
      L.Both{head_checked, classified_append(eligible, rest, frame, tail_checked, checked)}

law appended_budget_is_the_same:
  for +frames: List<&2, Q.Frame>
  for +frame: Q.Frame
  for +rest: Nat
  {Nat.add(Q.count(Q.append(frames, frame)), rest) == Nat.add(Q.count(frames), 1n+rest) : Nat}
def appended_budget_is_the_same(frames, frame, rest):
  Equal.trans(Nat, Nat.add(Q.count(Q.append(frames, frame)), rest), 1n+Nat.add(Q.count(frames), rest),
    Nat.add(Q.count(frames), 1n+rest),
    Equal.cong(Nat, Nat, count => Nat.add(count, rest), Q.count(Q.append(frames, frame)), 1n+Q.count(frames),
      Q.count_after_append(frames, frame)),
    Equal.sym(Nat, Nat.add(Q.count(frames), 1n+rest), 1n+Nat.add(Q.count(frames), rest), add_successor_right(Q.count(frames), rest)))

def producer_preserves(~eligible: Q.Frame -> Bool, +bounds: Q.Bounds, -limit: Nat,
  +action: Producer, +previous: H.History, +remaining: Nat, +open: Bool,
  invariant: Invariant(eligible, bounds, limit, Collector{previous, remaining, open})) ->
  Invariant(eligible, bounds, limit, Collector{H.step(bounds, producer_action(action), previous), remaining, open}):
  L.Both{conserved, L.Both{bounded, L.Both{classified, budget}}} = invariant
  L.Both{H.atomic_step_preserves_conservation(bounds, producer_action(action), previous, conserved),
    L.Both{H.atomic_step_preserves_actual_accounting_bounds(bounds, producer_action(action), previous, bounded),
      (%Equal.sym(List<&2, Q.Frame>, H.selected(H.step(bounds, producer_action(action), previous)), H.selected(previous),
          producer_action_keeps_the_entire_selected_batch(bounds, action, previous)) :
        L.E<S.AllEligible(eligible, _), {Nat.add(Q.count(_), remaining) == limit : Nat}>
        L.Both{classified, budget})}}

def successful_attempt_preserves(~eligible: Q.Frame -> Bool, +bounds: Q.Bounds, +limit: Nat,
  +head: Q.Frame, +tail: List<&2, Q.Frame>, +phase: Q.Phase, +terminal: Maybe<&2, Q.End>, +stopped: Bool,
  +accepted: List<&2, Q.Frame>, +selected: List<&2, Q.Frame>, +rest: Nat,
  checked: {eligible(head) == True{} : Bool},
  invariant: Invariant(eligible, bounds, limit,
    Collector{H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, 1n+rest, True{}})) ->
  Invariant(eligible, bounds, limit,
    Collector{H.History{Q.Queue{tail, phase, terminal, stopped}, accepted, Q.append(selected, head)}, rest, True{}}):
  L.Both{conserved, L.Both{bounded, L.Both{classified, budget}}} = invariant
  L.Both{H.actual_selection_preserves_conservation(
      H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, conserved),
    L.Both{Q.fifo_selection_preserves_bounds(bounds, Q.Queue{Con{head, tail}, phase, terminal, stopped}, bounded),
      L.Both{classified_append(eligible, selected, head, classified, checked),
        Equal.trans(Nat, Nat.add(Q.count(Q.append(selected, head)), rest), Nat.add(Q.count(selected), 1n+rest), limit,
          appended_budget_is_the_same(selected, head, rest), budget)}}}

def decided_attempt_preserves(~eligible: Q.Frame -> Bool, +bounds: Q.Bounds, +limit: Nat,
  qualifies: Bool, +head: Q.Frame, +tail: List<&2, Q.Frame>, +phase: Q.Phase,
  +terminal: Maybe<&2, Q.End>, +stopped: Bool, +accepted: List<&2, Q.Frame>, +selected: List<&2, Q.Frame>, +rest: Nat,
  checked: {eligible(head) == qualifies : Bool},
  invariant: Invariant(eligible, bounds, limit,
    Collector{H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, 1n+rest, True{}})) ->
  Invariant(eligible, bounds, limit,
    collect_decision(qualifies, H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, rest)):
  match qualifies:
    case False{}: invariant
    case True{}:
      successful_attempt_preserves(eligible, bounds, limit, head, tail, phase, terminal, stopped,
        accepted, selected, rest, checked, invariant)

law every_actual_conditional_head_attempt_preserves_the_collector_invariant:
  for ~eligible: Q.Frame -> Bool
  for +bounds: Q.Bounds
  for +limit: Nat
  for +collector: Collector
  for invariant: Invariant(eligible, bounds, limit, collector)
  Invariant(eligible, bounds, limit, attempt(eligible, collector))
def every_actual_conditional_head_attempt_preserves_the_collector_invariant(eligible, bounds, limit, collector, invariant):
  match collector:
    case Collector{history, remaining, False{}}: invariant
    case Collector{history, 0n, True{}}: invariant
    case Collector{H.History{Q.Queue{Nil{}, phase, terminal, stopped}, accepted, selected}, 1n+rest, True{}}: invariant
    case Collector{H.History{Q.Queue{Con{+head, +tail}, +phase, +terminal, +stopped}, +accepted, +selected}, 1n+ +rest, True{}}:
      decided_attempt_preserves(eligible, bounds, limit, eligible(head), head, tail, phase, terminal, stopped,
        accepted, selected, rest, {==}, invariant)

law every_collector_and_producer_interleaving_preserves_fifo_classification_and_both_budgets:
  for ~eligible: Q.Frame -> Bool
  for +bounds: Q.Bounds
  for +limit: Nat
  for +actions: List<&2, Action>
  for +collector: Collector
  for invariant: Invariant(eligible, bounds, limit, collector)
  Invariant(eligible, bounds, limit, run(eligible, bounds, actions, collector))
def every_collector_and_producer_interleaving_preserves_fifo_classification_and_both_budgets(eligible, bounds, limit, actions, collector, invariant):
  match actions:
    case Nil{}: invariant
    case Con{Produce{+action}, +rest}:
      match collector:
        case Collector{+previous, +remaining, +open}:
          every_collector_and_producer_interleaving_preserves_fifo_classification_and_both_budgets(eligible, bounds, limit, rest,
            Collector{H.step(bounds, producer_action(action), previous), remaining, open},
            producer_preserves(eligible, bounds, limit, action, previous, remaining, open, invariant))
    case Con{TryCandidate{}, +rest}:
      every_collector_and_producer_interleaving_preserves_fifo_classification_and_both_budgets(eligible, bounds, limit, rest,
        attempt(eligible, collector), every_actual_conditional_head_attempt_preserves_the_collector_invariant(eligible, bounds, limit, collector, invariant))

# Initial boundedness is a genuine pre-state fact, supplied by the preceding
# framing history; accepted and selected histories themselves are constructed.
def seed(+queue: Q.Queue, limit: Nat) -> Collector:
  Collector{H.History{queue, Q.frames(queue), Nil{}}, limit, True{}}

law seeded_collection_is_genuine:
  for ~eligible: Q.Frame -> Bool
  for +bounds: Q.Bounds
  for +queue: Q.Queue
  for +limit: Nat
  for bounded: Q.Within(bounds, queue)
  Invariant(eligible, bounds, limit, seed(queue, limit))
def seeded_collection_is_genuine(eligible, bounds, queue, limit, bounded):
  L.Both{{==}, L.Both{bounded, L.Both{Unit{}, {==}}}}

law actual_collected_batch_is_a_prefix_of_all_receptions_even_with_concurrent_appends:
  for ~eligible: Q.Frame -> Bool
  for +bounds: Q.Bounds
  for +queue: Q.Queue
  for +limit: Nat
  for +actions: List<&2, Action>
  for bounded: Q.Within(bounds, queue)
  Invariant(eligible, bounds, limit, run(eligible, bounds, actions, seed(queue, limit)))
def actual_collected_batch_is_a_prefix_of_all_receptions_even_with_concurrent_appends(eligible, bounds, queue, limit, actions, bounded):
  every_collector_and_producer_interleaving_preserves_fifo_classification_and_both_budgets(eligible, bounds, limit, actions,
    seed(queue, limit), seeded_collection_is_genuine(eligible, bounds, queue, limit, bounded))

law remaining_capacity_is_strictly_less_than_its_successor:
  for n: Nat
  {Nat.is_lt(n, 1n+n) == True{} : Bool}
def remaining_capacity_is_strictly_less_than_its_successor(n):
  match n:
    case 0n: {==}
    case 1n+p: remaining_capacity_is_strictly_less_than_its_successor(p)

def AttemptProgress(~eligible: Q.Frame -> Bool, +collector: Collector) -> Type:
  match collector:
    case Collector{history, remaining, False{}}: Unit
    case Collector{history, 0n, True{}}: Unit
    case Collector{history, 1n+rest, True{}}:
      {Nat.is_lt(available(attempt(eligible, collector)), 1n+rest) == True{} : Bool}

def decided_progress(qualifies: Bool, previous: H.History, rest: Nat) ->
  {Nat.is_lt(available(collect_decision(qualifies, previous, rest)), 1n+rest) == True{} : Bool}:
  match qualifies:
    case False{}: {==}
    case True{}: remaining_capacity_is_strictly_less_than_its_successor(rest)

law every_enabled_collector_attempt_strictly_decreases_its_finite_budget:
  for ~eligible: Q.Frame -> Bool
  for collector: Collector
  AttemptProgress(eligible, collector)
def every_enabled_collector_attempt_strictly_decreases_its_finite_budget(eligible, collector):
  match collector:
    case Collector{history, remaining, False{}}: Unit{}
    case Collector{history, 0n, True{}}: Unit{}
    case Collector{H.History{Q.Queue{Nil{}, phase, terminal, stopped}, accepted, selected}, 1n+rest, True{}}: {==}
    case Collector{H.History{Q.Queue{Con{+head, tail}, phase, terminal, stopped}, accepted, selected}, 1n+rest, True{}}:
      decided_progress(eligible(head), H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, rest)

# The relation is checked against Q.select_if itself, not a separately chosen
# FIFO result. Terminal/blocked constructors in Some would be impossible.
def CandidateAgreement(result: Maybe<&2, Q.Selection>, -previous: H.History, -rest: Nat, -after: Collector) -> Type:
  match result:
    case None{}: {after == Collector{previous, 1n+rest, False{}} : Collector}
    case Some{Q.Selected{frame, next}}:
      {after == Collector{H.consumed(Q.Selected{frame, next}, previous), rest, True{}} : Collector}
    case Some{Q.Terminal{end, next}}: Empty
    case Some{Q.Blocked{}}: Empty

def candidate_decision_agrees(qualifies: Bool, +head: Q.Frame, +tail: List<&2, Q.Frame>, +phase: Q.Phase,
  +terminal: Maybe<&2, Q.End>, +stopped: Bool, +accepted: List<&2, Q.Frame>, +selected: List<&2, Q.Frame>, +rest: Nat) ->
  CandidateAgreement(Q.select_if_head(qualifies, head, tail, phase, terminal, stopped),
    H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, rest,
    collect_decision(qualifies, H.History{Q.Queue{Con{head, tail}, phase, terminal, stopped}, accepted, selected}, rest)):
  match qualifies:
    case False{}: {==}
    case True{}: {==}

law collector_attempt_is_exactly_the_actual_conditional_head_selection:
  for ~eligible: Q.Frame -> Bool
  for +previous: H.History
  for +rest: Nat
  CandidateAgreement(Q.select_if(eligible, H.queue(previous)), previous, rest,
    attempt(eligible, Collector{previous, 1n+rest, True{}}))
def collector_attempt_is_exactly_the_actual_conditional_head_selection(eligible, previous, rest):
  match previous:
    case H.History{Q.Queue{Nil{}, phase, terminal, stopped}, accepted, selected}: {==}
    case H.History{Q.Queue{Con{+head, +tail}, +phase, +terminal, +stopped}, +accepted, +selected}:
      candidate_decision_agrees(eligible(head), head, tail, phase, terminal, stopped, accepted, selected, rest)

# A nonempty computed collection from an initially empty queue. This checks the
# newly added concurrent-arrival path rather than an always-empty collector.
law an_eligible_head_received_between_attempts_is_actually_collected:
  {batch(run(frame => True{}, Q.Bounds{2n, 0n},
    [Produce{ReserveBody{0n}}, Produce{CommitBody{Q.Frame{0n, []}}}, TryCandidate{}],
    seed(Q.Queue{[], Q.Header{}, None{}, False{}}, 1n))) == [Q.Frame{0n, []}] : List<&2, Q.Frame>}
def an_eligible_head_received_between_attempts_is_actually_collected():
  {==}

def CollectionSummary(~eligible: Q.Frame -> Bool, -limit: Nat, +collector: Collector) -> Type:
  L.E<L.Prefix(Q.Frame, batch(collector), H.accepted(history(collector))),
    L.E<S.AllEligible(eligible, batch(collector)), N.Le(Q.count(batch(collector)), limit)>>

law collection_summary_follows_from_the_constructed_invariant:
  for ~eligible: Q.Frame -> Bool
  for -bounds: Q.Bounds
  for +limit: Nat
  for +collector: Collector
  for invariant: Invariant(eligible, bounds, limit, collector)
  CollectionSummary(eligible, limit, collector)
def collection_summary_follows_from_the_constructed_invariant(eligible, bounds, limit, collector, invariant):
  L.Both{conserved, L.Both{bounded, L.Both{classified, budget}}} = invariant
  L.Both{H.conserved_implies_prefix(history(collector), conserved),
    L.Both{classified,
      (%budget :
        N.Le(Q.count(batch(collector)), _) Q.prefix_within_sum(Q.count(batch(collector)), remaining(collector)))}}

law every_seeded_interleaved_collection_is_a_classified_bounded_reception_prefix:
  for ~eligible: Q.Frame -> Bool
  for +bounds: Q.Bounds
  for +queue: Q.Queue
  for +limit: Nat
  for +actions: List<&2, Action>
  for bounded: Q.Within(bounds, queue)
  CollectionSummary(eligible, limit, run(eligible, bounds, actions, seed(queue, limit)))
def every_seeded_interleaved_collection_is_a_classified_bounded_reception_prefix(eligible, bounds, queue, limit, actions, bounded):
  collection_summary_follows_from_the_constructed_invariant(eligible, bounds, limit,
    run(eligible, bounds, actions, seed(queue, limit)),
    actual_collected_batch_is_a_prefix_of_all_receptions_even_with_concurrent_appends(eligible, bounds, queue, limit, actions, bounded))
