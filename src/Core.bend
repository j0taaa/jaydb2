# Incremental interpreter: each advance consumes exactly the current action.
# traverse fuel belongs only to the mathematical characterization;
# the server advances the machine without reexecuting prefixes.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Protocol.bend as P

type Machine is Type:
  Running{working: D.State, action: S.Action, events: List<&2, S.OperationEvent>}
  Stopped{working: D.State, events: List<&2, S.OperationEvent>, response: S.Response}

def start(p: S.Program, context: D.Context, arguments: D.Value,
  initial: D.State) -> Machine:
  Running{initial, S.start(p, context, arguments), Nil{}}

def step_machine(step: S.Step, events: List<&2, S.OperationEvent>) -> Machine:
  match step:
    case S.Continue{w, a, event}:
      Running{w, a, S.append(events, event)}
    case S.Stopped{w, response}:
      Stopped{w, events, response}
    case S.OperationFailed{w, event}:
      Stopped{w, S.append(events, event), S.response_error(S.DataError{})}

def advance(machine: Machine, schema: D.Schema) -> Machine:
  match machine:
    case Running{w, a, events}:
      step_machine(S.step(a, schema, w), events)
    case Stopped{w, events, response}:
      Stopped{w, events, response}

def snapshot(machine: Machine) -> S.Trace:
  match machine:
    case Running{w, a, events}:
      S.Prefix{w, events}
    case Stopped{w, events, response}:
      S.Final{w, events, response}

def traverse(n: Nat, machine: Machine, +schema: D.Schema) -> S.Trace:
  match n:
    case 0n:
      snapshot(machine)
    case 1n+m:
      traverse(m, advance(machine, schema), schema)

type Prepared is Data:
  Prepared{working: D.State, events: List<&2, S.OperationEvent>,
    response: S.Response, bytes: List<&2, U32>}

def prepare_bytes(result: Maybe<&2, List<&2, U32>>, working: D.State,
  events: List<&2, S.OperationEvent>, response: S.Response) -> Maybe<&2, Prepared>:
  match result:
    case None{}:
      None{}
    case Some{bytes}:
      Some{Prepared{working, events, response, bytes}}

def prepare_response(+response: S.Response, working: D.State,
  events: List<&2, S.OperationEvent>) -> Maybe<&2, Prepared>:
  prepare_bytes(P.frame(S.response_value(response)), working, events, response)

# Uses only technical contract conditions; never tests administrator
# laws at runtime. Those laws were required during admission.
def prepare(machine: Machine, configuration: S.Configuration) -> Maybe<&2, Prepared>:
  match machine:
    case Running{w, a, events}:
      None{}
    case Stopped{+w, events, proposal}:
      prepare_response(R.finalize(proposal, configuration, w), w, events)

type Conclusion is Data:
  Conclusion{published: D.State, response: S.Response, bytes: List<&2, U32>}

# The caller replaces the published root only after prepare returns Some.
def conclude(prepared: Prepared, initial: D.State) -> Conclusion:
  Prepared{w, events, +response, bytes} = prepared
  Conclusion{S.publish(response, initial, w), response, bytes}

law refusal_discards_state_of_working:
  for -w: D.State
  for -events: List<&2, S.OperationEvent>
  for -v: D.Value
  for -bytes: List<&2, U32>
  for -initial: D.State
  {conclude(Prepared{w, events, S.Response{S.Refusal{}, v}, bytes}, initial) ==
    Conclusion{initial, S.Response{S.Refusal{}, v}, bytes} : Conclusion}
def refusal_discards_state_of_working(w, events, v, bytes, initial):
  {==}

law success_publish_state_integer:
  for -w: D.State
  for -events: List<&2, S.OperationEvent>
  for -v: D.Value
  for -bytes: List<&2, U32>
  for -initial: D.State
  {conclude(Prepared{w, events, S.Response{S.Success{}, v}, bytes}, initial) ==
    Conclusion{w, S.Response{S.Success{}, v}, bytes} : Conclusion}
def success_publish_state_integer(w, events, v, bytes, initial):
  {==}

law start_uses_state_and_arguments_received:
  for -p: S.Program
  for -ctx: D.Context
  for -args: D.Value
  for -s: D.State
  {snapshot(start(p, ctx, args, s)) == S.Prefix{s, Nil{}} : S.Trace}
def start_uses_state_and_arguments_received(p, ctx, args, s):
  {==}

# The incremental machine's mathematical path matches the reference.
# The proof does not receive this correspondence as a premise.
law stopped_absorbs:
  for n: Nat
  for -w: D.State
  for -events: List<&2, S.OperationEvent>
  for -response: S.Response
  for -schema: D.Schema
  {traverse(n, Stopped{w, events, response}, schema) ==
    S.Final{w, events, response} : S.Trace}
def stopped_absorbs(n, w, events, response, schema):
  match n:
    case 0n:
      {==}
    case 1n+m:
      stopped_absorbs(m, w, events, response, schema)

law step_corresponds_to_reference:
  for n: Nat
  for step: S.Step
  for +schema: D.Schema
  for events: List<&2, S.OperationEvent>
  {traverse(n, step_machine(step, events), schema) ==
    S.resume_execution_trace(n, step, schema, events) : S.Trace}
def step_corresponds_to_reference(n, step, schema, events):
  match n step:
    case 0n S.Continue{w, a, event}:
      {==}
    case 0n S.Stopped{w, response}:
      {==}
    case 0n S.OperationFailed{w, event}:
      {==}
    case 1n+m S.Continue{w, a, event}:
      step_corresponds_to_reference(m, S.step(a, schema, w), schema,
        S.append(events, event))
    case 1n+m S.Stopped{w, response}:
      stopped_absorbs(1n+m, w, events, response, schema)
    case 1n+m S.OperationFailed{w, event}:
      stopped_absorbs(1n+m, w, S.append(events, event),
        S.response_error(S.DataError{}), schema)

law fidelity_of_all_os_prefixes:
  for n: Nat
  for program: S.Program
  for context: D.Context
  for arguments: D.Value
  for +schema: D.Schema
  for initial: D.State
  {traverse(n, start(program, context, arguments, initial), schema) ==
    S.execute(n, program, schema, initial, context, arguments) : S.Trace}
def fidelity_of_all_os_prefixes(n, program, context, arguments, schema, initial):
  match n:
    case 0n:
      {==}
    case 1n+m:
      step_corresponds_to_reference(m,
        S.step(S.start(program, context, arguments), schema, initial),
        schema, Nil{})

law certificate_covers_machine_incremental:
  for configuration: S.Configuration
  for -code: String
  for program: S.Program
  for +context: D.Context
  for +arguments: D.Value
  for certificate: R.Certifies(configuration, code, program, context, arguments)
  for +initial: D.State
  for valid: R.Valid(configuration, initial)
  for identity: {D.context_present(initial, context) == True{} : Bool}
  for +n: Nat
  R.SafetyTrace(
    traverse(n, start(program, context, arguments, initial), S.schema(configuration)),
    configuration, initial, context, code, arguments)
def certificate_covers_machine_incremental(configuration, code, program, context,
  arguments, certificate, initial, valid, identity, n):
  %Equal.sym(S.Trace,
    traverse(n, start(program, context, arguments, initial), S.schema(configuration)),
    S.execute(n, program, S.schema(configuration), initial, context, arguments),
    fidelity_of_all_os_prefixes(n, program, context, arguments,
      S.schema(configuration), initial)) :
        R.SafetyTrace(_, configuration, initial, context, code, arguments)
  certificate(initial, valid, identity, n)
