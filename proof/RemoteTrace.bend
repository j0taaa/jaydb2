# The trace reconstructs events from replies and follows the host state and worker action.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Core.bend as Core
import ./RemoteRefinement.bend as Step

def apply_step(step: Maybe<&1, S.Step>, events: List<&2, S.OperationEvent>) ->
  Maybe<&1, Core.Machine>:
  match step:
    case None{}: None{}
    case Some{p}: Some{Core.step_machine(p, events)}

def remote_advance(machine: Maybe<&1, Core.Machine>, e: D.Schema) -> Maybe<&1, Core.Machine>:
  match machine:
    case None{}: None{}
    case Some{Core.Stopped{w, events, r}}: Some{Core.Stopped{w, events, r}}
    case Some{Core.Running{w, a, events}}: apply_step(Step.remote_step(a, e, w), events)

def snapshot(machine: Maybe<&1, Core.Machine>) -> Maybe<&2, S.Trace>:
  match machine:
    case None{}: None{}
    case Some{m}: Some{Core.snapshot(m)}

def traverse(n: Nat, machine: Maybe<&1, Core.Machine>, +e: D.Schema) -> Maybe<&2, S.Trace>:
  match n:
    case 0n: snapshot(machine)
    case 1n+p: traverse(p, remote_advance(machine, e), e)

type AdvanceAvailable<-m: Core.Machine, -e: D.Schema> is Type:
  RunningAvailable{w: D.State, -a: S.Action, events: List<&2, S.OperationEvent>,
    machine: {m == Core.Running{w, a, events} : Core.Machine}, step: Step.StepAvailable<a, e, w>}
  StoppedAvailable{w: D.State, events: List<&2, S.OperationEvent>, r: S.Response,
    machine: {m == Core.Stopped{w, events, r} : Core.Machine}}

# Finite transport evidence: a request and reply can be encoded for each
# access taken by the reference at this fuel. Terminal steps need no bytes.
def TraceAvailable(n: Nat, -m: Core.Machine, -e: D.Schema) -> Type:
  match n:
    case 0n: Unit
    case 1n+p: L.E<AdvanceAvailable<m, e>, TraceAvailable(p, Core.advance(m, e), e)>

law remote_advance_refines_core:
  for -m: Core.Machine
  for +e: D.Schema
  for available: AdvanceAvailable<m, e>
  {remote_advance(Some{m}, e) == Some{Core.advance(m, e)} : Maybe<&1, Core.Machine>}
def remote_advance_refines_core(m, e, available):
  match available:
    case StoppedAvailable{w, events, r, same}:
      %Equal.sym(Core.Machine, m, Core.Stopped{w, events, r}, same) :
        {remote_advance(Some{_}, e) == Some{Core.advance(_, e)} : Maybe<&1, Core.Machine>}
      {==}
    case RunningAvailable{+w, a, events, same, step}:
      %Equal.sym(Core.Machine, m, Core.Running{w, a, events}, same) :
        {remote_advance(Some{_}, e) == Some{Core.advance(_, e)} : Maybe<&1, Core.Machine>}
      Equal.cong(Maybe<&1, S.Step>, Maybe<&1, Core.Machine>, out => apply_step(out, events),
        Step.remote_step(a, e, w), Some{S.step(a, e, w)}, Step.remote_step_refines_contract(a, e, w, step))

law all_remote_prefixes_refine_core:
  for n: Nat
  for -m: Core.Machine
  for +e: D.Schema
  for available: TraceAvailable(n, m, e)
  {traverse(n, Some{m}, e) == Some{Core.traverse(n, m, e)} : Maybe<&2, S.Trace>}
def all_remote_prefixes_refine_core(n, m, e, available):
  match n:
    case 0n: {==}
    case 1n+ +p:
      match available:
        case L.Both{first, rest}:
          %Equal.sym(Maybe<&1, Core.Machine>, remote_advance(Some{m}, e), Some{Core.advance(m, e)},
            remote_advance_refines_core(m, e, first)) :
            {traverse(p, _, e) == Some{Core.traverse(p, Core.advance(m, e), e)} : Maybe<&2, S.Trace>}
          all_remote_prefixes_refine_core(p, Core.advance(m, e), e, rest)

law all_remote_prefixes_refine_execute:
  for +n: Nat
  for program: S.Program
  for +context: D.Context
  for +arguments: D.Value
  for +e: D.Schema
  for +initial: D.State
  for available: TraceAvailable(n, Core.start(program, context, arguments, initial), e)
  {traverse(n, Some{Core.start(program, context, arguments, initial)}, e) ==
    Some{S.execute(n, program, e, initial, context, arguments)} : Maybe<&2, S.Trace>}
def all_remote_prefixes_refine_execute(n, program, context, arguments, e, initial, available):
  Equal.trans(Maybe<&2, S.Trace>,
    traverse(n, Some{Core.start(program, context, arguments, initial)}, e),
    Some{Core.traverse(n, Core.start(program, context, arguments, initial), e)},
    Some{S.execute(n, program, e, initial, context, arguments)},
    all_remote_prefixes_refine_core(n, Core.start(program, context, arguments, initial), e, available),
    Equal.cong(S.Trace, Maybe<&2, S.Trace>, t => Some{t},
      Core.traverse(n, Core.start(program, context, arguments, initial), e),
      S.execute(n, program, e, initial, context, arguments),
      Core.fidelity_of_all_os_prefixes(n, program, context, arguments, e, initial)))

def Safety(trace: Maybe<&2, S.Trace>, -configuration: S.Configuration, -initial: D.State,
  -context: D.Context, -code: String, -arguments: D.Value) -> Type:
  match trace:
    case None{}: Empty
    case Some{t}: R.SafetyTrace(t, configuration, initial, context, code, arguments)

law certificate_covers_remote_prefixes:
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
  for available: TraceAvailable(n, Core.start(program, context, arguments, initial), S.schema(configuration))
  Safety(traverse(n, Some{Core.start(program, context, arguments, initial)}, S.schema(configuration)),
    configuration, initial, context, code, arguments)
def certificate_covers_remote_prefixes(configuration, code, program, context, arguments, certificate,
  initial, valid, identity, n, available):
  %Equal.sym(Maybe<&2, S.Trace>,
    traverse(n, Some{Core.start(program, context, arguments, initial)}, S.schema(configuration)),
    Some{S.execute(n, program, S.schema(configuration), initial, context, arguments)},
    all_remote_prefixes_refine_execute(n, program, context, arguments, S.schema(configuration), initial, available)) :
    Safety(_, configuration, initial, context, code, arguments)
  certificate(initial, valid, identity, n)
