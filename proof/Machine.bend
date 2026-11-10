# Event order, actual operations and progress of the real interpreter.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/RequestFacts.bend as I
import ../contract/Links.bend as V
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ./Foundations.bend as F

law reference_stopped:
  for n: Nat
  for -w: D.State
  for -ts: List<&2, S.OperationEvent>
  for -r: S.Response
  for -e: D.Schema
  {S.resume_execution_trace(n, S.Stopped{w, r}, e, ts) == S.Final{w, ts, r} : S.Trace}
def reference_stopped(n, w, ts, r, e):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

law append_preserves_prefix:
  for ts: List<&2, S.OperationEvent>
  for -event: S.OperationEvent
  L.Prefix(S.OperationEvent, ts, S.append(ts, event))
def append_preserves_prefix(ts, event):
  match ts:
    case Nil{}:
      Unit{}
    case Con{h, t}:
      L.Both{{==}, append_preserves_prefix(t, event)}

def TraceWithPrefix(-n: Nat, -m: N.Machine, -e: D.Schema) -> Type:
  &execution_trace: S.Trace -> L.E<{N.traverse(n, m, e) == execution_trace : S.Trace},
    L.Prefix(S.OperationEvent, S.events_execution_trace(N.snapshot(m)), S.events_execution_trace(execution_trace))>

def receive_continuation(-n: Nat, -w: D.State, -a: S.Action, +ts: List<&2, S.OperationEvent>,
  +ev: S.OperationEvent, -e: D.Schema,
  result: TraceWithPrefix(n, N.Running{w, a, S.append(ts, ev)}, e)) ->
  &execution_trace: S.Trace -> L.E<{N.traverse(n, N.Running{w, a, S.append(ts, ev)}, e) == execution_trace : S.Trace},
    L.Prefix(S.OperationEvent, ts, S.events_execution_trace(execution_trace))>:
  match result:
    case (+execution_trace, L.Both{equality, prefix}):
      (execution_trace, L.Both{equality,
        F.prefix_transitive(S.OperationEvent, ts, S.append(ts, ev), S.events_execution_trace(execution_trace),
          append_preserves_prefix(ts, ev), prefix)})

def step_combined_prefix(step: S.Step, +n: Nat, +e: D.Schema, +ts: List<&2, S.OperationEvent>,
  rec: @m: N.Machine -> TraceWithPrefix(n, m, e)) ->
  &execution_trace: S.Trace -> L.E<{N.traverse(n, N.step_machine(step, ts), e) == execution_trace : S.Trace},
    L.Prefix(S.OperationEvent, ts, S.events_execution_trace(execution_trace))>:
  match step:
    case S.Continue{w, a, +ev}:
      receive_continuation(n, w, a, ts, ev, e, rec(N.Running{w, a, S.append(ts, ev)}))
    case S.Stopped{+w, +response}:
      (S.Final{w, ts, response}, L.Both{N.stopped_absorbs(n, w, ts, response, e), L.prefix_refl(S.OperationEvent, ts)})
    case S.OperationFailed{+w, +ev}:
      (S.Final{w, S.append(ts, ev), S.response_error(S.DataError{})},
        L.Both{N.stopped_absorbs(n, w, S.append(ts, ev), S.response_error(S.DataError{}), e),
          append_preserves_prefix(ts, ev)})

law execution_trace_combined_prefix:
  for +n: Nat
  for m: N.Machine
  for +e: D.Schema
  TraceWithPrefix(n, m, e)
def execution_trace_combined_prefix(n, m, e):
  match n m:
    case 0n N.Running{w, a, +ts}:
      (S.Prefix{w, ts}, L.Both{{==}, L.prefix_refl(S.OperationEvent, ts)})
    case 0n N.Stopped{w, +ts, response}:
      (S.Final{w, ts, response}, L.Both{{==}, L.prefix_refl(S.OperationEvent, ts)})
    case 1n+k N.Running{w, a, ts}:
      step_combined_prefix(S.step(a, e, w), k, e, ts,
        next => execution_trace_combined_prefix(k, next, e))
    case 1n+k N.Stopped{+w, +ts, +response}:
      (S.Final{w, ts, response}, L.Both{N.stopped_absorbs(1n+k, w, ts, response, e), L.prefix_refl(S.OperationEvent, ts)})

def extract_prefix(-n: Nat, -m: N.Machine, -e: D.Schema,
  result: TraceWithPrefix(n, m, e)) ->
  L.Prefix(S.OperationEvent, S.events_execution_trace(N.snapshot(m)), S.events_execution_trace(N.traverse(n, m, e))):
  match result:
    case (execution_trace, L.Both{equality, prefix}):
      %Equal.sym(S.Trace, N.traverse(n, m, e), execution_trace, equality) :
        L.Prefix(S.OperationEvent, S.events_execution_trace(N.snapshot(m)), S.events_execution_trace(_))
      prefix

law traverse_preserves_events_previous:
  for +n: Nat
  for m: N.Machine
  for +e: D.Schema
  L.Prefix(S.OperationEvent, S.events_execution_trace(N.snapshot(m)), S.events_execution_trace(N.traverse(n, m, e)))
def traverse_preserves_events_previous(n, m, e):
  extract_prefix(n, m, e, execution_trace_combined_prefix(n, m, e))

law prefixes_of_machine_in_order:
  for n: Nat
  for +additional: Nat
  for m: N.Machine
  for +e: D.Schema
  L.Prefix(S.OperationEvent, S.events_execution_trace(N.traverse(n, m, e)),
    S.events_execution_trace(N.traverse(Nat.add(n, additional), m, e)))
def prefixes_of_machine_in_order(n, additional, m, e):
  match n:
    case 0n:
      traverse_preserves_events_previous(additional, m, e)
    case 1n+k:
      prefixes_of_machine_in_order(k, additional, N.advance(m, e), e)

law result_binds_transition:
  for result: D.ResultOp
  for -s: D.State
  for -o: D.Operation
  for -k: S.Return -> S.Action
  for -ts: List<&2, S.OperationEvent>
  V.AfterOperation(result, s, o, ts,
    N.snapshot(N.step_machine(S.apply(result, s, o, k), ts)))
def result_binds_transition(result, s, o, k, ts):
  match result:
    case D.FailureData{}:
      {==}
    case D.Observed{observation}:
      L.Both{{==}, {==}}
    case D.Changed{w}:
      L.Both{{==}, {==}}

law operation_real_binds_transition:
  for +e: D.Schema
  for +s: D.State
  for +o: D.Operation
  for -k: S.Return -> S.Action
  for -ts: List<&2, S.OperationEvent>
  V.AfterOperation(D.operate(e, s, o), s, o, ts,
    N.snapshot(N.advance(N.Running{s, S.Access{o, k}, ts}, e)))
def operation_real_binds_transition(e, s, o, k, ts):
  result_binds_transition(D.operate(e, s, o), s, o, k, ts)

law start_uses_exactly_program_context_arguments_and_state:
  for -p: S.Program
  for -ctx: D.Context
  for -args: D.Value
  for -s: D.State
  {N.start(p, ctx, args, s) == N.Running{s, S.start(p, ctx, args), Nil{}} : N.Machine}
def start_uses_exactly_program_context_arguments_and_state(p, ctx, args, s):
  {==}

law termination_of_reference_implies_termination_incremental:
  for p: S.Program
  for +e: D.Schema
  for +s: D.State
  for +ctx: D.Context
  for +args: D.Value
  for terminates: I.Terminates(p, e, s, ctx, args)
  exs n: Nat
  exs w: D.State
  exs ts: List<&2, S.OperationEvent>
  exs r: S.Response
  {N.traverse(n, N.start(p, ctx, args, s), e) == S.Final{w, ts, r} : S.Trace}
def termination_of_reference_implies_termination_incremental(p, e, s, ctx, args, terminates):
  match terminates:
    case (+n, w, ts, r, reference):
      (n, w, ts, r, Equal.trans(S.Trace,
        N.traverse(n, N.start(p, ctx, args, s), e), S.execute(n, p, e, s, ctx, args),
        S.Final{w, ts, r}, N.fidelity_of_all_os_prefixes(n, p, ctx, args, e, s), reference))
