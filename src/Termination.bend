# Depth is a mathematical witness, never a runtime quota.
# The service executes Action incrementally, preserving the path already performed.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/RequestFacts.bend as I

def Finite(n: Nat, a: S.Action) -> Type:
  match n:
    case 0n:
      Empty
    case 1n+k:
      match a:
        case S.Finish{v}:
          Unit
        case S.Refuse{v}:
          Unit
        case S.Access{o, resume}:
          @r: S.Return -> Finite(k, resume(r))

def observe(n: Nat, a: S.Action, +e: D.Schema, +s: D.State,
  ts: List<&2, S.OperationEvent>) -> S.Trace:
  match n:
    case 0n:
      S.Prefix{s, ts}
    case 1n+k:
      S.resume_execution_trace(k, S.step(a, e, s), e, ts)

def End(-n: Nat, -a: S.Action, -e: D.Schema, -s: D.State,
  -ts: List<&2, S.OperationEvent>) -> Type:
  &w: D.State -> &events: List<&2, S.OperationEvent> -> &r: S.Response ->
    {observe(n, a, e, s, ts) == S.Final{w, events, r} : S.Trace}

law stopped:
  for n: Nat
  for -w: D.State
  for -r: S.Response
  for -e: D.Schema
  for -ts: List<&2, S.OperationEvent>
  {S.resume_execution_trace(n, S.Stopped{w, r}, e, ts) == S.Final{w, ts, r} : S.Trace}
def stopped(n, w, r, e, ts):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

law failure_of_operation:
  for n: Nat
  for -w: D.State
  for -ev: S.OperationEvent
  for -e: D.Schema
  for -ts: List<&2, S.OperationEvent>
  {S.resume_execution_trace(n, S.OperationFailed{w, ev}, e, ts) ==
    S.Final{w, S.append(ts, ev), S.response_error(S.DataError{})} : S.Trace}
def failure_of_operation(n, w, ev, e, ts):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

law continuation:
  for n: Nat
  for -w: D.State
  for -a: S.Action
  for -ev: S.OperationEvent
  for -e: D.Schema
  for -ts: List<&2, S.OperationEvent>
  {S.resume_execution_trace(n, S.Continue{w, a, ev}, e, ts) ==
    observe(n, a, e, w, S.append(ts, ev)) : S.Trace}
def continuation(n, w, a, ev, e, ts):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def convert_witness(-a: S.Trace, -b: S.Trace,
  eq: {a == b : S.Trace},
  result: &w: D.State -> &ts: List<&2, S.OperationEvent> -> &r: S.Response ->
    {b == S.Final{w, ts, r} : S.Trace}) ->
  &w: D.State -> &ts: List<&2, S.OperationEvent> -> &r: S.Response ->
    {a == S.Final{w, ts, r} : S.Trace}:
  match result:
    case (w, ts, r, h):
      (w, ts, r, Equal.trans(S.Trace, a, b, S.Final{w, ts, r}, eq, h))

def result_finite(result: D.ResultOp, +n: Nat,
  resume: S.Return -> S.Action, +e: D.Schema, +s: D.State,
  +o: D.Operation, +ts: List<&2, S.OperationEvent>,
  h: @r: S.Return -> Finite(n, resume(r)),
  rec: @a: S.Action -> @s2: D.State -> @ts2: List<&2, S.OperationEvent> ->
    Finite(n, a) -> End(n, a, e, s2, ts2)) ->
  &w: D.State -> &events: List<&2, S.OperationEvent> -> &r: S.Response ->
    {S.resume_execution_trace(n, S.apply(result, s, o, resume), e, ts) ==
      S.Final{w, events, r} : S.Trace}:
  match result:
    case D.FailureData{}:
      (s, S.append(ts, S.OperationEvent{o, S.ErrorOfData{}}), S.response_error(S.DataError{}),
        failure_of_operation(n, s, S.OperationEvent{o, S.ErrorOfData{}}, e, ts))
    case D.Observed{+obs}:
      convert_witness(S.resume_execution_trace(n,
        S.Continue{s, resume(S.Datum{obs}), S.OperationEvent{o, S.Reading{obs}}}, e, ts),
        observe(n, resume(S.Datum{obs}), e, s, S.append(ts, S.OperationEvent{o, S.Reading{obs}})),
        continuation(n, s, resume(S.Datum{obs}), S.OperationEvent{o, S.Reading{obs}}, e, ts),
        rec(resume(S.Datum{obs}), s, S.append(ts, S.OperationEvent{o, S.Reading{obs}}), h(S.Datum{obs})))
    case D.Changed{+w}:
      convert_witness(S.resume_execution_trace(n,
        S.Continue{w, resume(S.UnitValue{}), S.OperationEvent{o, S.Write{}}}, e, ts),
        observe(n, resume(S.UnitValue{}), e, w, S.append(ts, S.OperationEvent{o, S.Write{}})),
        continuation(n, w, resume(S.UnitValue{}), S.OperationEvent{o, S.Write{}}, e, ts),
        rec(resume(S.UnitValue{}), w, S.append(ts, S.OperationEvent{o, S.Write{}}), h(S.UnitValue{})))

law finite_terminates:
  for n: Nat
  for a: S.Action
  for +e: D.Schema
  for +s: D.State
  for +ts: List<&2, S.OperationEvent>
  for h: Finite(n, a)
  End(n, a, e, s, ts)
def finite_terminates(n, a, e, s, ts, h):
  match n:
    case 0n:
      Empty.absurd(End(0n, a, e, s, ts), h)
    case 1n+k:
      match a:
        case S.Finish{+v}:
          (s, ts, S.Response{S.Success{}, v}, stopped(k, s, S.Response{S.Success{}, v}, e, ts))
        case S.Refuse{+v}:
          (s, ts, S.Response{S.Refusal{}, v}, stopped(k, s, S.Response{S.Refusal{}, v}, e, ts))
        case S.Access{+o, resume}:
          +remaining = k
          result_finite(D.operate(e, s, o), remaining, resume, e, s, o, ts, h,
            next => state => events => proof => finite_terminates(remaining, next, e, state, events, proof))

law reference:
  for n: Nat
  for -a: S.Action
  for -e: D.Schema
  for -s: D.State
  {observe(n, a, e, s, Nil{}) == S.observe(n, a, e, s) : S.Trace}
def reference(n, a, e, s):
  match n:
    case 0n:
      {==}
    case 1n+k:
      {==}

def witness_program(+n: Nat, -p: S.Program, -e: D.Schema, -s: D.State,
  -ctx: D.Context, -args: D.Value,
  result: End(n, S.start(p, ctx, args), e, s, Nil{})) ->
  I.Terminates(p, e, s, ctx, args):
  match result:
    case (w, ts, r, h):
      (n, w, ts, r, Equal.trans(S.Trace, S.execute(n, p, e, s, ctx, args),
        observe(n, S.start(p, ctx, args), e, s, Nil{}), S.Final{w, ts, r},
        Equal.sym(S.Trace, observe(n, S.start(p, ctx, args), e, s, Nil{}),
          S.execute(n, p, e, s, ctx, args), reference(n, S.start(p, ctx, args), e, s)), h))

def program_finite(+n: Nat, p: S.Program, +e: D.Schema, +s: D.State,
  +ctx: D.Context, +args: D.Value, h: Finite(n, S.start(p, ctx, args))) ->
  I.Terminates(p, e, s, ctx, args):
  witness_program(n, p, e, s, ctx, args,
    finite_terminates(n, S.start(p, ctx, args), e, s, Nil{}, h))
