# JayDB — semantics of programs and application laws.
# Submitted code produces Action; it never receives State.
# States and events below are specification objects, not a public log.
import Base
import ./Data.bend as D
import ./Logic.bend as L

type Return is Data:
  Datum{observation: D.Observation}
  UnitValue{}

type Action is Type:
  Finish{value: D.Value}
  Refuse{value: D.Value}
  Access{operation: D.Operation, resume: Return -> Action}

type Program is Type:
  Program{start: D.Context -> D.Value -> Action}

type Effect is Data:
  Reading{observation: D.Observation}
  Write{}
  ErrorOfData{}

type OperationEvent is Data:
  OperationEvent{operation: D.Operation, effect: Effect}

type Status is Data:
  Input{}
  Authentication{}
  Certificate{}
  DataError{}
  Limit{}
  Failure{}
  Refusal{}
  Success{}

type Response is Data:
  Response{status: Status, value: D.Value}

type Situation is Data:
  Stable{state: D.State}
  Executing{initial: D.State, context: D.Context, code: String,
    arguments: D.Value, working: D.State, events: List<&2, OperationEvent>}
  Closed{initial: D.State, context: D.Context, code: String,
    arguments: D.Value, working: D.State, events: List<&2, OperationEvent>, response: Response}

type Laws is Type:
  NoneLaw{}
  MoreOneLaw{rule: Situation -> Type, remaining: Laws}

def All(laws: Laws, +h: Situation) -> Type:
  match laws:
    case NoneLaw{}:
      Unit
    case MoreOneLaw{rule, rest}:
      L.E<rule(h), All(rest, h)>

# Sizes and memory in bytes; times in integer nanoseconds.
# Physical measurements belong to the environment, not the requester program.
type Limits is Data:
  Limits{message: Nat, state: Nat, response: Nat,
    memory: Nat, framing: Nat, authentication: Nat,
    verification: Nat, execution: Nat, preparation: Nat}

type Configuration is Type:
  Configuration{schema: D.Schema, laws: Laws, limits: Limits,
    environment: String}

def schema(c: Configuration) -> D.Schema:
  Configuration{e, ls, lim, amb} = c
  e

def limits(c: Configuration) -> Limits:
  Configuration{e, ls, lim, amb} = c
  lim

def environment(c: Configuration) -> String:
  Configuration{e, ls, lim, amb} = c
  amb

def Satisfies(c: Configuration, h: Situation) -> Type:
  Configuration{e, ls, lim, amb} = c
  All(ls, h)

def start(p: Program, c: D.Context, a: D.Value) -> Action:
  Program{f} = p
  f(c, a)

def append(xs: List<&2, OperationEvent>, e: OperationEvent) -> List<&2, OperationEvent>:
  match xs:
    case Nil{}:
      [e]
    case Con{h, t}:
      h <> append(t, e)

type Step is Type:
  Continue{state: D.State, action: Action, event: OperationEvent}
  Stopped{state: D.State, response: Response}
  OperationFailed{state: D.State, event: OperationEvent}

def apply(r: D.ResultOp, s: D.State, o: D.Operation,
  k: Return -> Action) -> Step:
  match r:
    case D.FailureData{}:
      OperationFailed{s, OperationEvent{o, ErrorOfData{}}}
    case D.Observed{+v}:
      Continue{s, k(Datum{v}), OperationEvent{o, Reading{v}}}
    case D.Changed{w}:
      Continue{w, k(UnitValue{}), OperationEvent{o, Write{}}}

def step(a: Action, e: D.Schema, +s: D.State) -> Step:
  match a:
    case Finish{v}:
      Stopped{s, Response{Success{}, v}}
    case Refuse{v}:
      Stopped{s, Response{Refusal{}, v}}
    case Access{+o, k}:
      apply(D.operate(e, s, o), s, o, k)

type Trace is Data:
  Prefix{working: D.State, events: List<&2, OperationEvent>}
  Final{working: D.State, events: List<&2, OperationEvent>, response: Response}

# n enumerates mathematical prefixes. It is NOT a new execution limit.
# Time and memory continue to be measured by the real environment.
def resume_execution_trace(n: Nat, p: Step, +e: D.Schema,
  ts: List<&2, OperationEvent>) -> Trace:
  match n p:
    case 0n Continue{s, a, ev}:
      Prefix{s, append(ts, ev)}
    case 0n Stopped{s, r}:
      Final{s, ts, r}
    case 0n OperationFailed{s, ev}:
      Final{s, append(ts, ev), Response{DataError{}, D.VAbsent{}}}
    case 1n+m Continue{s, a, ev}:
      resume_execution_trace(m, step(a, e, s), e, append(ts, ev))
    case 1n+m Stopped{s, r}:
      Final{s, ts, r}
    case 1n+m OperationFailed{s, ev}:
      Final{s, append(ts, ev), Response{DataError{}, D.VAbsent{}}}

def observe(n: Nat, a: Action, +e: D.Schema, +s: D.State) -> Trace:
  match n:
    case 0n:
      Prefix{s, Nil{}}
    case 1n+m:
      resume_execution_trace(m, step(a, e, s), e, Nil{})

def execute(n: Nat, p: Program, e: D.Schema, s: D.State,
  c: D.Context, a: D.Value) -> Trace:
  observe(n, start(p, c, a), e, s)

def state_execution_trace(p: Trace) -> D.State:
  match p:
    case Prefix{s, t}:
      s
    case Final{s, t, r}:
      s

def events_execution_trace(p: Trace) -> List<&2, OperationEvent>:
  match p:
    case Prefix{s, t}:
      t
    case Final{s, t, r}:
      t

def status_name(s: Status) -> String:
  match s:
    case Input{}:
      "input"
    case Authentication{}:
      "authentication"
    case Certificate{}:
      "certificate"
    case DataError{}:
      "data"
    case Limit{}:
      "limit"
    case Failure{}:
      "failure"
    case Refusal{}:
      "refusal"
    case Success{}:
      "success"

def response_value(r: Response) -> D.Value:
  Response{s, v} = r
  D.VRecord{"status", D.VText{status_name(s)},
    D.VRecord{"value", v, D.VRecordEmpty{}}}

def response_error(s: Status) -> Response:
  Response{s, D.VAbsent{}}

def is_success(s: Status) -> Bool:
  match s:
    case Success{}:
      True{}
    case _:
      False{}

def publish(r: Response, initial: D.State, working: D.State) -> D.State:
  match r:
    case Response{Success{}, v}:
      working
    case _:
      initial

# Model lemmas: complete proofs, independent of a native implementation.
law prefix_initial:
  for -p: Program
  for -e: D.Schema
  for -s: D.State
  for -c: D.Context
  for -a: D.Value
  {execute(0n, p, e, s, c, a) == Prefix{s, Nil{}} : Trace}

def prefix_initial(p, e, s, c, a):
  {==}

law refusal_preserves_published:
  for -v: D.Value
  for -s: D.State
  for -w: D.State
  {publish(Response{Refusal{}, v}, s, w) == s : D.State}

def refusal_preserves_published(v, s, w):
  {==}

law success_publish_working:
  for -v: D.Value
  for -s: D.State
  for -w: D.State
  {publish(Response{Success{}, v}, s, w) == w : D.State}

def success_publish_working(v, s, w):
  {==}

law write_negative_delivery_state:
  for -s: D.State
  for -w: D.State
  for -o: D.Operation
  for -k: Return -> Action
  {apply(D.Changed{w}, s, o, k) ==
    Continue{w, k(UnitValue{}), OperationEvent{o, Write{}}} : Step}

def write_negative_delivery_state(s, w, o, k):
  {==}

law error_of_operation_preserves_working:
  for -s: D.State
  for -o: D.Operation
  for -k: Return -> Action
  {apply(D.FailureData{}, s, o, k) ==
    OperationFailed{s, OperationEvent{o, ErrorOfData{}}} : Step}

def error_of_operation_preserves_working(s, o, k):
  {==}
