# Fixed-batch native algorithm: start a prefix, join every started handle,
# emit in start order, suppress all later emits after the first failure.
# Primitive returns below are data; actual OS/worker/IO correspondence remains
# a fixed technical source contract, not an assumed FIFO conclusion.
import Base
import ../contract/Logic.bend as L
import ./FrameQueue.bend as Q

type Failure is Data:
  SpawnFailure{job: Q.Frame, identifier: String}
  JoinFailure{job: Q.Frame, identifier: String}
  DeliveryFailure{job: Q.Frame, identifier: String}

type SpawnReturn is Data:
  Started{}
  SpawnError{identifier: String}

type JoinReturn is Data:
  Joined{response: List<&2, U32>}
  JoinError{identifier: String}

type SendReturn is Data:
  Sent{}
  SendError{prefix: List<&2, U32>, identifier: String}

type Start is Data:
  Start{handles: List<&2, Q.Frame>, failure: Maybe<&2, Failure>}

def prepend_start(job: Q.Frame, later: Start) -> Start:
  Start{handles, failure} = later
  Start{Con{job, handles}, failure}

def start_reply(reply: SpawnReturn, +job: Q.Frame, later: Unit -> Start) -> Start:
  match reply:
    case Started{}: prepend_start(job, later(Unit{}))
    case SpawnError{identifier}: Start{Nil{}, Some{SpawnFailure{job, identifier}}}

def start(~spawn: Q.Frame -> SpawnReturn, jobs: List<&2, Q.Frame>) -> Start:
  match jobs:
    case Nil{}: Start{Nil{}, None{}}
    case Con{+job, rest}: start_reply(spawn(job), job, unit => start(spawn, rest))

type JoinEvent is Data:
  JoinEvent{job: Q.Frame, returned: JoinReturn}

type Attempt is Data:
  Attempt{job: Q.Frame, response: List<&2, U32>, returned: SendReturn}

type Outcome is Data:
  Outcome{joins: List<&2, JoinEvent>, attempts: List<&2, Attempt>, failure: Maybe<&2, Failure>}

def record_join(job: Q.Frame, returned: JoinReturn, later: Outcome) -> Outcome:
  Outcome{joins, attempts, failure} = later
  Outcome{Con{JoinEvent{job, returned}, joins}, attempts, failure}

def record_attempt(job: Q.Frame, response: List<&2, U32>, returned: SendReturn, later: Outcome) -> Outcome:
  Outcome{joins, attempts, failure} = later
  Outcome{joins, Con{Attempt{job, response, returned}, attempts}, failure}

def after_send(returned: SendReturn, +job: Q.Frame, response: List<&2, U32>,
  later: Maybe<&2, Failure> -> Outcome) -> Outcome:
  match returned:
    case Sent{}: record_attempt(job, response, Sent{}, later(None{}))
    case SendError{prefix, +identifier}:
      record_attempt(job, response, SendError{prefix, identifier}, later(Some{DeliveryFailure{job, identifier}}))

def after_join(~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  initial_failure: Maybe<&2, Failure>, +job: Q.Frame, +returned: JoinReturn,
  later: Maybe<&2, Failure> -> Outcome) -> Outcome:
  match initial_failure returned:
    case Some{failure} returned: record_join(job, returned, later(Some{failure}))
    case None{} JoinError{+identifier}:
      record_join(job, JoinError{identifier}, later(Some{JoinFailure{job, identifier}}))
    case None{} Joined{+response}:
      record_join(job, Joined{response}, after_send(emit(job, response), job, response, later))

def drain(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  handles: List<&2, Q.Frame>, failure: Maybe<&2, Failure>) -> Outcome:
  match handles:
    case Nil{}: Outcome{Nil{}, Nil{}, failure}
    case Con{+job, rest}: after_join(emit, failure, job, join(job), next => drain(join, emit, rest, next))

def execute_started(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  started: Start) -> Outcome:
  Start{handles, failure} = started
  drain(join, emit, handles, failure)

def execute(~spawn: Q.Frame -> SpawnReturn, ~join: Q.Frame -> JoinReturn,
  ~emit: Q.Frame -> List<&2, U32> -> SendReturn, jobs: List<&2, Q.Frame>) -> Outcome:
  execute_started(join, emit, start(spawn, jobs))

def joined_jobs(joins: List<&2, JoinEvent>) -> List<&2, Q.Frame>:
  match joins:
    case Nil{}: Nil{}
    case Con{JoinEvent{job, returned}, rest}: Con{job, joined_jobs(rest)}

def attempted_jobs(attempts: List<&2, Attempt>) -> List<&2, Q.Frame>:
  match attempts:
    case Nil{}: Nil{}
    case Con{Attempt{job, response, returned}, rest}: Con{job, attempted_jobs(rest)}

def joins(outcome: Outcome) -> List<&2, JoinEvent>:
  Outcome{joins, attempts, failure} = outcome
  joins

def attempts(outcome: Outcome) -> List<&2, Attempt>:
  Outcome{joins, attempts, failure} = outcome
  attempts

def failure(outcome: Outcome) -> Maybe<&2, Failure>:
  Outcome{joins, attempts, failure} = outcome
  failure

# Every join-return record is retained even after failure. The source cannot
# justify a discarded/unjoined handle by merely returning a final error.
def joined_record(job: Q.Frame, returned: JoinReturn, later: Outcome) ->
  {joined_jobs(joins(record_join(job, returned, later))) == Con{job, joined_jobs(joins(later))} : List<&2, Q.Frame>}:
  match later:
    case Outcome{joins, attempts, failure}: {==}

def attempted_record(job: Q.Frame, response: List<&2, U32>, returned: SendReturn, later: Outcome) ->
  {attempted_jobs(attempts(record_attempt(job, response, returned, later))) ==
    Con{job, attempted_jobs(attempts(later))} : List<&2, Q.Frame>}:
  match later:
    case Outcome{joins, attempts, failure}: {==}

def attempted_join_record(job: Q.Frame, returned: JoinReturn, later: Outcome) ->
  {attempts(record_join(job, returned, later)) == attempts(later) : List<&2, Attempt>}:
  match later:
    case Outcome{joins, attempts, failure}: {==}

def joined_attempt_record(job: Q.Frame, response: List<&2, U32>, returned: SendReturn, later: Outcome) ->
  {joins(record_attempt(job, response, returned, later)) == joins(later) : List<&2, JoinEvent>}:
  match later:
    case Outcome{joins, attempts, failure}: {==}

def AlreadyFailed(initial: Maybe<&2, Failure>, +outcome: Outcome) -> Type:
  match initial:
    case None{}: Unit
    case Some{error}:
      L.E<{attempts(outcome) == Nil{} : List<&2, Attempt>},
        {failure(outcome) == Some{error} : Maybe<&2, Failure>}>

def Drained(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  -handles: List<&2, Q.Frame>, -initial: Maybe<&2, Failure>) -> Type:
  &outcome: Outcome -> L.E<{drain(join, emit, handles, initial) == outcome : Outcome},
    L.E<{joined_jobs(joins(outcome)) == handles : List<&2, Q.Frame>},
      L.E<L.Prefix(Q.Frame, attempted_jobs(attempts(outcome)), handles), AlreadyFailed(initial, outcome)>>>

def empty_already_failed(initial: Maybe<&2, Failure>) -> AlreadyFailed(initial, Outcome{Nil{}, Nil{}, initial}):
  match initial:
    case None{}: Unit{}
    case Some{error}: L.Both{{==}, {==}}

def drain_failed_head(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  +job: Q.Frame, +rest: List<&2, Q.Frame>, +error: Failure, +returned: JoinReturn,
  checked: {join(job) == returned : JoinReturn}, later: Drained(join, emit, rest, Some{error})) ->
  Drained(join, emit, Con{job, rest}, Some{error}):
  match later:
    case (Outcome{+joined, +attempted, +failed},
      L.Both{actual, L.Both{complete, L.Both{prefix, L.Both{+empty, retained}}}}):
      (Outcome{Con{JoinEvent{job, returned}, joined}, attempted, failed},
        L.Both{
          (%Equal.sym(JoinReturn, join(job), returned, checked) :
            {after_join(emit, Some{error}, job, _, next => drain(join, emit, rest, next)) ==
              Outcome{Con{JoinEvent{job, returned}, joined}, attempted, failed} : Outcome}
            Equal.cong(Outcome, Outcome, outcome => record_join(job, returned, outcome),
              drain(join, emit, rest, Some{error}), Outcome{joined, attempted, failed}, actual)),
          L.Both{Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, jobs => Con{job, jobs},
              joined_jobs(joined), rest, complete),
            L.Both{
              (%Equal.sym(List<&2, Attempt>, attempted, Nil{}, empty) :
                L.Prefix(Q.Frame, attempted_jobs(_), Con{job, rest}) Unit{}),
              L.Both{empty, retained}}}})

def drain_join_error_head(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  +job: Q.Frame, +rest: List<&2, Q.Frame>, +identifier: String,
  checked: {join(job) == JoinError{identifier} : JoinReturn},
  later: Drained(join, emit, rest, Some{JoinFailure{job, identifier}})) ->
  Drained(join, emit, Con{job, rest}, None{}):
  match later:
    case (Outcome{+joined, +attempted, +failed},
      L.Both{actual, L.Both{complete, L.Both{prefix, L.Both{empty, retained}}}}):
      (Outcome{Con{JoinEvent{job, JoinError{identifier}}, joined}, attempted, failed},
        L.Both{
          (%Equal.sym(JoinReturn, join(job), JoinError{identifier}, checked) :
            {after_join(emit, None{}, job, _, next => drain(join, emit, rest, next)) ==
              Outcome{Con{JoinEvent{job, JoinError{identifier}}, joined}, attempted, failed} : Outcome}
            Equal.cong(Outcome, Outcome, outcome => record_join(job, JoinError{identifier}, outcome),
              drain(join, emit, rest, Some{JoinFailure{job, identifier}}), Outcome{joined, attempted, failed}, actual)),
          L.Both{Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, jobs => Con{job, jobs},
              joined_jobs(joined), rest, complete),
            L.Both{
              (%Equal.sym(List<&2, Attempt>, attempted, Nil{}, empty) :
                L.Prefix(Q.Frame, attempted_jobs(_), Con{job, rest}) Unit{}), Unit{}}}})

def drain_sent_head(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  +job: Q.Frame, +rest: List<&2, Q.Frame>, +response: List<&2, U32>,
  joined_checked: {join(job) == Joined{response} : JoinReturn},
  sent_checked: {emit(job, response) == Sent{} : SendReturn}, later: Drained(join, emit, rest, None{})) ->
  Drained(join, emit, Con{job, rest}, None{}):
  match later:
    case (Outcome{+joined, +attempted, +failed},
      L.Both{actual, L.Both{complete, L.Both{prefix, retained}}}):
      (Outcome{Con{JoinEvent{job, Joined{response}}, joined}, Con{Attempt{job, response, Sent{}}, attempted}, failed},
        L.Both{
          (%Equal.sym(JoinReturn, join(job), Joined{response}, joined_checked) :
            {after_join(emit, None{}, job, _, next => drain(join, emit, rest, next)) ==
              Outcome{Con{JoinEvent{job, Joined{response}}, joined}, Con{Attempt{job, response, Sent{}}, attempted}, failed} : Outcome}
            %Equal.sym(SendReturn, emit(job, response), Sent{}, sent_checked) :
              {record_join(job, Joined{response}, after_send(_, job, response, next => drain(join, emit, rest, next))) ==
                Outcome{Con{JoinEvent{job, Joined{response}}, joined}, Con{Attempt{job, response, Sent{}}, attempted}, failed} : Outcome}
            Equal.cong(Outcome, Outcome, outcome =>
              record_join(job, Joined{response}, record_attempt(job, response, Sent{}, outcome)),
              drain(join, emit, rest, None{}), Outcome{joined, attempted, failed}, actual)),
          L.Both{Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, jobs => Con{job, jobs},
              joined_jobs(joined), rest, complete), L.Both{L.Both{{==}, prefix}, Unit{}}}})

def drain_delivery_error_head(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  +job: Q.Frame, +rest: List<&2, Q.Frame>, +response: List<&2, U32>,
  +written_prefix: List<&2, U32>, +identifier: String,
  joined_checked: {join(job) == Joined{response} : JoinReturn},
  sent_checked: {emit(job, response) == SendError{written_prefix, identifier} : SendReturn},
  later: Drained(join, emit, rest, Some{DeliveryFailure{job, identifier}})) ->
  Drained(join, emit, Con{job, rest}, None{}):
  match later:
    case (Outcome{+joined, +attempted, +failed},
      L.Both{actual, L.Both{complete, L.Both{prefix, L.Both{empty, retained}}}}):
      (Outcome{Con{JoinEvent{job, Joined{response}}, joined},
          Con{Attempt{job, response, SendError{written_prefix, identifier}}, attempted}, failed},
        L.Both{
          (%Equal.sym(JoinReturn, join(job), Joined{response}, joined_checked) :
            {after_join(emit, None{}, job, _, next => drain(join, emit, rest, next)) ==
              Outcome{Con{JoinEvent{job, Joined{response}}, joined},
                Con{Attempt{job, response, SendError{written_prefix, identifier}}, attempted}, failed} : Outcome}
            %Equal.sym(SendReturn, emit(job, response), SendError{written_prefix, identifier}, sent_checked) :
              {record_join(job, Joined{response}, after_send(_, job, response, next => drain(join, emit, rest, next))) ==
                Outcome{Con{JoinEvent{job, Joined{response}}, joined},
                  Con{Attempt{job, response, SendError{written_prefix, identifier}}, attempted}, failed} : Outcome}
            Equal.cong(Outcome, Outcome, outcome =>
              record_join(job, Joined{response}, record_attempt(job, response, SendError{written_prefix, identifier}, outcome)),
              drain(join, emit, rest, Some{DeliveryFailure{job, identifier}}), Outcome{joined, attempted, failed}, actual)),
          L.Both{Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, jobs => Con{job, jobs},
              joined_jobs(joined), rest, complete),
            L.Both{L.Both{{==},
                (%Equal.sym(List<&2, Attempt>, attempted, Nil{}, empty) :
                  L.Prefix(Q.Frame, attempted_jobs(_), rest) Unit{})}, Unit{}}}})

def certified_send(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  returned: SendReturn, +job: Q.Frame, +rest: List<&2, Q.Frame>, +response: List<&2, U32>,
  joined_checked: {join(job) == Joined{response} : JoinReturn},
  sent_checked: {emit(job, response) == returned : SendReturn},
  recurse: @next: Maybe<&2, Failure> -> Drained(join, emit, rest, next)) ->
  Drained(join, emit, Con{job, rest}, None{}):
  match returned:
    case Sent{}: drain_sent_head(join, emit, job, rest, response, joined_checked, sent_checked, recurse(None{}))
    case SendError{+prefix, +identifier}:
      drain_delivery_error_head(join, emit, job, rest, response, prefix, identifier,
        joined_checked, sent_checked, recurse(Some{DeliveryFailure{job, identifier}}))

def certified_join(~join: Q.Frame -> JoinReturn, ~emit: Q.Frame -> List<&2, U32> -> SendReturn,
  initial: Maybe<&2, Failure>, returned: JoinReturn, +job: Q.Frame, +rest: List<&2, Q.Frame>,
  checked: {join(job) == returned : JoinReturn},
  recurse: @next: Maybe<&2, Failure> -> Drained(join, emit, rest, next)) ->
  Drained(join, emit, Con{job, rest}, initial):
  match initial returned:
    case Some{+error} returned:
      drain_failed_head(join, emit, job, rest, error, returned, checked, recurse(Some{error}))
    case None{} JoinError{+identifier}:
      drain_join_error_head(join, emit, job, rest, identifier, checked,
        recurse(Some{JoinFailure{job, identifier}}))
    case None{} Joined{+response}:
      certified_send(join, emit, emit(job, response), job, rest, response, checked, {==}, recurse)

law every_started_handle_is_joined_and_attempts_are_fifo:
  for ~join: Q.Frame -> JoinReturn
  for ~emit: Q.Frame -> List<&2, U32> -> SendReturn
  for handles: List<&2, Q.Frame>
  for +failure: Maybe<&2, Failure>
  Drained(join, emit, handles, failure)
def every_started_handle_is_joined_and_attempts_are_fifo(join, emit, handles, failure):
  match handles:
    case Nil{}:
      (Outcome{Nil{}, Nil{}, failure}, L.Both{{==}, L.Both{{==}, L.Both{Unit{}, empty_already_failed(failure)}}})
    case Con{+job, +rest}:
      certified_join(join, emit, failure, join(job), job, rest, {==},
        next => every_started_handle_is_joined_and_attempts_are_fifo(join, emit, rest, next))

# Spawn decisions are checked against the same primitive-return function used
# by start. The stop witness identifies the actual first unstarted job.
def handles(started: Start) -> List<&2, Q.Frame>:
  Start{handles, failure} = started
  handles

def start_failure(started: Start) -> Maybe<&2, Failure>:
  Start{handles, failure} = started
  failure

def AllStarted(~spawn: Q.Frame -> SpawnReturn, jobs: List<&2, Q.Frame>) -> Type:
  match jobs:
    case Nil{}: Unit
    case Con{job, rest}: L.E<{spawn(job) == Started{} : SpawnReturn}, AllStarted(spawn, rest)>

def StopPosition(~spawn: Q.Frame -> SpawnReturn, -jobs: List<&2, Q.Frame>, +started: Start) -> Type:
  match started:
    case Start{handles, None{}}: {jobs == handles : List<&2, Q.Frame>}
    case Start{handles, Some{SpawnFailure{job, identifier}}}:
      &suffix: List<&2, Q.Frame> ->
        L.E<{jobs == Q.concatenate(handles, Con{job, suffix}) : List<&2, Q.Frame>},
          {spawn(job) == SpawnError{identifier} : SpawnReturn}>
    case Start{handles, Some{JoinFailure{job, identifier}}}: Empty
    case Start{handles, Some{DeliveryFailure{job, identifier}}}: Empty

def StartedCorrect(~spawn: Q.Frame -> SpawnReturn, -jobs: List<&2, Q.Frame>) -> Type:
  &started: Start -> L.E<{start(spawn, jobs) == started : Start},
    L.E<L.Prefix(Q.Frame, handles(started), jobs),
      L.E<AllStarted(spawn, handles(started)), StopPosition(spawn, jobs, started)>>>

def lift_stop_position(~spawn: Q.Frame -> SpawnReturn, +job: Q.Frame,
  +rest: List<&2, Q.Frame>, +started: Start,
  stopped: StopPosition(spawn, rest, started)) ->
  StopPosition(spawn, Con{job, rest}, prepend_start(job, started)):
  match started:
    case Start{+later, None{}}:
      Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, jobs => Con{job, jobs}, rest, later, stopped)
    case Start{+later, Some{SpawnFailure{+failed, +identifier}}}:
      match stopped:
        case (+suffix, L.Both{position, decision}):
          (suffix, L.Both{Equal.cong(List<&2, Q.Frame>, List<&2, Q.Frame>, jobs => Con{job, jobs},
            rest, Q.concatenate(later, Con{failed, suffix}), position), decision})
    case Start{later, Some{JoinFailure{failed, identifier}}}: Empty.absurd(Empty, stopped)
    case Start{later, Some{DeliveryFailure{failed, identifier}}}: Empty.absurd(Empty, stopped)

def start_success_step(~spawn: Q.Frame -> SpawnReturn, +job: Q.Frame, +rest: List<&2, Q.Frame>,
  +checked: {spawn(job) == Started{} : SpawnReturn}, later: StartedCorrect(spawn, rest)) ->
  StartedCorrect(spawn, Con{job, rest}):
  match later:
    case (Start{+later, +failure}, L.Both{actual, L.Both{prefix, L.Both{started, stopped}}}):
      (Start{Con{job, later}, failure}, L.Both{
        (%Equal.sym(SpawnReturn, spawn(job), Started{}, checked) :
          {start_reply(_, job, unit => start(spawn, rest)) == Start{Con{job, later}, failure} : Start}
          Equal.cong(Start, Start, result => prepend_start(job, result),
            start(spawn, rest), Start{later, failure}, actual)),
        L.Both{L.Both{{==}, prefix}, L.Both{L.Both{checked, started},
          lift_stop_position(spawn, job, rest, Start{later, failure}, stopped)}}})

def start_checked_reply(~spawn: Q.Frame -> SpawnReturn, returned: SpawnReturn,
  +job: Q.Frame, +rest: List<&2, Q.Frame>, +checked: {spawn(job) == returned : SpawnReturn},
  recurse: Unit -> StartedCorrect(spawn, rest)) -> StartedCorrect(spawn, Con{job, rest}):
  match returned:
    case Started{}: start_success_step(spawn, job, rest, checked, recurse(Unit{}))
    case SpawnError{+identifier}:
      (Start{Nil{}, Some{SpawnFailure{job, identifier}}}, L.Both{
        (%Equal.sym(SpawnReturn, spawn(job), SpawnError{identifier}, checked) :
          {start_reply(_, job, unit => start(spawn, rest)) == Start{Nil{}, Some{SpawnFailure{job, identifier}}} : Start} {==}),
        L.Both{Unit{}, L.Both{Unit{}, (rest, L.Both{{==}, checked})}}})

law actual_spawn_starts_exactly_the_successful_prefix:
  for ~spawn: Q.Frame -> SpawnReturn
  for jobs: List<&2, Q.Frame>
  StartedCorrect(spawn, jobs)
def actual_spawn_starts_exactly_the_successful_prefix(spawn, jobs):
  match jobs:
    case Nil{}: (Start{Nil{}, None{}}, L.Both{{==}, L.Both{Unit{}, L.Both{Unit{}, {==}}}})
    case Con{+job, +rest}:
      start_checked_reply(spawn, spawn(job), job, rest, {==},
        unit => actual_spawn_starts_exactly_the_successful_prefix(spawn, rest))

def Executed(~spawn: Q.Frame -> SpawnReturn, ~join: Q.Frame -> JoinReturn,
  ~emit: Q.Frame -> List<&2, U32> -> SendReturn, -jobs: List<&2, Q.Frame>) -> Type:
  &started: Start -> &outcome: Outcome ->
    L.E<{start(spawn, jobs) == started : Start},
      L.E<{execute(spawn, join, emit, jobs) == outcome : Outcome},
        L.E<AllStarted(spawn, handles(started)),
          L.E<StopPosition(spawn, jobs, started),
            L.E<{joined_jobs(joins(outcome)) == handles(started) : List<&2, Q.Frame>},
              L.E<L.Prefix(Q.Frame, joined_jobs(joins(outcome)), jobs),
                L.Prefix(Q.Frame, attempted_jobs(attempts(outcome)), joined_jobs(joins(outcome)))>>>>>>

def compose_started_execution(~spawn: Q.Frame -> SpawnReturn, ~join: Q.Frame -> JoinReturn,
  ~emit: Q.Frame -> List<&2, U32> -> SendReturn, +jobs: List<&2, Q.Frame>,
  +handles: List<&2, Q.Frame>, +failure: Maybe<&2, Failure>,
  +actual_start: {start(spawn, jobs) == Start{handles, failure} : Start},
  start_prefix: L.Prefix(Q.Frame, handles, jobs),
  all_started: AllStarted(spawn, handles), stop_position: StopPosition(spawn, jobs, Start{handles, failure}),
  drained: Drained(join, emit, handles, failure)) -> Executed(spawn, join, emit, jobs):
  match drained:
    case (+outcome, L.Both{actual_drain, L.Both{+complete, L.Both{attempt_prefix, already_failed}}}):
      (Start{handles, failure}, outcome, L.Both{actual_start, L.Both{
        (%Equal.sym(Start, start(spawn, jobs), Start{handles, failure}, actual_start) :
          {execute_started(join, emit, _) == outcome : Outcome} actual_drain),
        L.Both{all_started, L.Both{stop_position, L.Both{complete,
          L.Both{(%Equal.sym(List<&2, Q.Frame>, joined_jobs(joins(outcome)), handles, complete) : L.Prefix(Q.Frame, _, jobs) start_prefix),
            (%Equal.sym(List<&2, Q.Frame>, joined_jobs(joins(outcome)), handles, complete) : L.Prefix(Q.Frame, attempted_jobs(attempts(outcome)), _) attempt_prefix)}}}}}})

def compose_execution(~spawn: Q.Frame -> SpawnReturn, ~join: Q.Frame -> JoinReturn,
  ~emit: Q.Frame -> List<&2, U32> -> SendReturn, +jobs: List<&2, Q.Frame>,
  prepared: StartedCorrect(spawn, jobs),
  drained: @started: Start -> Drained(join, emit, handles(started), start_failure(started))) ->
  Executed(spawn, join, emit, jobs):
  match prepared:
    case (Start{+handles, +failure}, L.Both{actual_start, L.Both{start_prefix, L.Both{all_started, stop_position}}}):
      compose_started_execution(spawn, join, emit, jobs, handles, failure, actual_start,
        start_prefix, all_started, stop_position, drained(Start{handles, failure}))

law actual_fixed_batch_starts_a_prefix_joins_every_handle_and_attempts_fifo:
  for ~spawn: Q.Frame -> SpawnReturn
  for ~join: Q.Frame -> JoinReturn
  for ~emit: Q.Frame -> List<&2, U32> -> SendReturn
  for +jobs: List<&2, Q.Frame>
  Executed(spawn, join, emit, jobs)
def actual_fixed_batch_starts_a_prefix_joins_every_handle_and_attempts_fifo(spawn, join, emit, jobs):
  compose_execution(spawn, join, emit, jobs, actual_spawn_starts_exactly_the_successful_prefix(spawn, jobs),
    +started => every_started_handle_is_joined_and_attempts_are_fifo(join, emit, handles(started), start_failure(started)))
