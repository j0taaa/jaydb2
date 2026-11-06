# Actual-state termination: enumeration supplies the finite list-dependent bound.
# This is an ordinary universal certificate, not a ReadOnly.Program witness.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as Free
import ./Logic.bend as L
import ./Termination.bend as T
import ./Interface.bend as F
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def B.certificate(ctx, args, s, valid, identity, n):
  Free.execution_trace_free_covers_prefixes_and_final(
    S.execute(n, Client.program(), C.schema(), s, ctx, args),
    C.schema(), C.limits(), S.environment(I.config()), s, ctx, B.code(), args)

# Unlike Finite, the bound may depend on the actual observed return/state.
def Complete(-a:S.Action,-e:D.Schema,-s:D.State,-ts:List<&2,S.OperationEvent>) -> Type:
  &n:Nat -> T.End(n,a,e,s,ts)

def finite(+n:Nat,a:S.Action,e:D.Schema,s:D.State,ts:List<&2,S.OperationEvent>,h:T.Finite(n,a)) -> Complete(a,e,s,ts):
  (n,T.finite_terminates(n,a,e,s,ts,h))

def Resumes(-step:S.Step,-e:D.Schema,-ts:List<&2,S.OperationEvent>) -> Type:
  &n:Nat -> &w:D.State -> &events:List<&2,S.OperationEvent> -> &r:S.Response ->
    {S.resume_execution_trace(n,step,e,ts) == S.Final{w,events,r} : S.Trace}

def continued(+s:D.State,-a:S.Action,+ev:S.OperationEvent,+e:D.Schema,+ts:List<&2,S.OperationEvent>,h:Complete(a,e,s,S.append(ts,ev))) ->
  Resumes(S.Continue{s,a,ev},e,ts):
  match h:
    case (+n,+w,+events,+r,eq):
      (n,w,events,r,Equal.trans(S.Trace,S.resume_execution_trace(n,S.Continue{s,a,ev},e,ts),T.observe(n,a,e,s,S.append(ts,ev)),S.Final{w,events,r},T.continuation(n,s,a,ev,e,ts),eq))

def result(res:D.ResultOp,+op:D.Operation,-k:S.Return -> S.Action,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,
  next:@r:S.Return -> @w:D.State -> @events:List<&2,S.OperationEvent> -> Complete(k(r),e,w,events)) -> Resumes(S.apply(res,s,op,k),e,ts):
  match res:
    case D.FailureData{}:
      (0n,s,S.append(ts,S.OperationEvent{op,S.ErrorOfData{}}),S.response_error(S.DataError{}),T.failure_of_operation(0n,s,S.OperationEvent{op,S.ErrorOfData{}},e,ts))
    case D.Observed{+obs}:
      continued(s,k(S.Datum{obs}),S.OperationEvent{op,S.Reading{obs}},e,ts,next(S.Datum{obs},s,S.append(ts,S.OperationEvent{op,S.Reading{obs}})))
    case D.Changed{+w}:
      continued(w,k(S.UnitValue{}),S.OperationEvent{op,S.Write{}},e,ts,next(S.UnitValue{},w,S.append(ts,S.OperationEvent{op,S.Write{}})))

def lift(+op:D.Operation,-k:S.Return -> S.Action,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,h:Resumes(S.step(S.Access{op,k},e,s),e,ts)) -> Complete(S.Access{op,k},e,s,ts):
  match h:
    case (n,w,events,r,eq): (Succ{n},w,events,r,eq)

def access(+op:D.Operation,-k:S.Return -> S.Action,+e:D.Schema,+s:D.State,+ts:List<&2,S.OperationEvent>,
  next:@r:S.Return -> @w:D.State -> @events:List<&2,S.OperationEvent> -> Complete(k(r),e,w,events)) -> Complete(S.Access{op,k},e,s,ts):
  lift(op,k,e,s,ts,result(D.operate(e,s,op),op,k,e,s,ts,next))


def steps(xs: List<&2, String>) -> Nat:
  match xs:
    case Nil{}: 0n
    case Con{k, rest}: Succ{Succ{steps(rest)}}

def parent_finite(+n: Nat, +key: String, +out: D.Value, -done: D.Value -> S.Action,
  h: @next: D.Value -> T.Finite(Succ{n}, done(next)), r: S.Return) ->
  T.Finite(Succ{n}, Client.parent_return(key, out, done, r)):
  match r:
    case S.Datum{D.Cell{v}}: h(D.VList{Client.pair(key, v), out})
    case S.Datum{D.RowAbsent{}}: h(out)
    case S.UnitValue{}: Unit{}
    case S.Datum{D.Existence{b}}: Unit{}
    case S.Datum{D.Count{n}}: Unit{}
    case S.Datum{D.Keys{keys}}: Unit{}

def foreign_finite(+n: Nat, +key: String, parent: String, column: String, out: D.Value,
  -done: D.Value -> S.Action, h: @next: D.Value -> T.Finite(Succ{n}, done(next)), r: S.Return) ->
  T.Finite(Succ{Succ{n}}, Client.foreign_return(key, parent, column, out, done, r)):
  match r:
    case S.Datum{D.Cell{D.VText{target}}}: next => parent_finite(n, key, out, done, h, next)
    case S.UnitValue{}: Unit{}
    case S.Datum{D.RowAbsent{}}: Unit{}
    case S.Datum{D.Existence{b}}: Unit{}
    case S.Datum{D.Count{n}}: Unit{}
    case S.Datum{D.Keys{keys}}: Unit{}
    case S.Datum{D.Cell{D.VAbsent{}}}: Unit{}
    case S.Datum{D.Cell{D.VBool{b}}}: Unit{}
    case S.Datum{D.Cell{D.VListEmpty{}}}: Unit{}
    case S.Datum{D.Cell{D.VList{head, tail}}}: Unit{}
    case S.Datum{D.Cell{D.VRecordEmpty{}}}: Unit{}
    case S.Datum{D.Cell{D.VRecord{name, value, rest}}}: Unit{}
    case S.Datum{D.Cell{D.VInt{hi, lo}}}: Unit{}

def walk_finite(xs: List<&2, String>, +child: String, +foreign: String,
  +parent: String, +column: String, +out: D.Value) ->
  T.Finite(Succ{steps(xs)}, Client.walk(xs, child, foreign, parent, column, out)):
  match xs:
    case Nil{}: Unit{}
    case Con{+key, +rest}:
      r => foreign_finite(steps(rest), key, parent, column, out,
        next => Client.walk(rest, child, foreign, parent, column, next),
        next => walk_finite(rest, child, foreign, parent, column, next), r)

def listed_complete(+child: String, +foreign: String, +parent: String, +column: String,
  r: S.Return, +e: D.Schema, +s: D.State, +ts: List<&2, S.OperationEvent>) ->
  Complete(Client.listed(child, foreign, parent, column, r), e, s, ts):
  match r:
    case S.Datum{D.Keys{+keys}}:
      finite(Succ{steps(keys)}, Client.walk(keys, child, foreign, parent, column, D.VListEmpty{}), e, s, ts,
        walk_finite(keys, child, foreign, parent, column, D.VListEmpty{}))
    case S.UnitValue{}: finite(1n, S.Refuse{D.VText{"unexpected keys return"}}, e, s, ts, Unit{})
    case S.Datum{D.RowAbsent{}}: finite(1n, S.Refuse{D.VText{"unexpected keys return"}}, e, s, ts, Unit{})
    case S.Datum{D.Cell{v}}: finite(1n, S.Refuse{D.VText{"unexpected keys return"}}, e, s, ts, Unit{})
    case S.Datum{D.Existence{b}}: finite(1n, S.Refuse{D.VText{"unexpected keys return"}}, e, s, ts, Unit{})
    case S.Datum{D.Count{n}}: finite(1n, S.Refuse{D.VText{"unexpected keys return"}}, e, s, ts, Unit{})

def command_complete(p: Client.Command, +e: D.Schema, +s: D.State,
  +ts: List<&2, S.OperationEvent>) -> Complete(Client.command(p), e, s, ts):
  match p:
    case Client.Join{+child, +foreign, +parent, +column}:
      access(D.EnumerateKeys{D.Application{child}}, Client.listed(child, foreign, parent, column), e, s, ts,
        r => w => events => listed_complete(child, foreign, parent, column, r, e, w, events))
    case Client.Invalid{}: finite(1n, S.Refuse{D.VText{"expected [join, child, foreign_key, parent, parent_column]"}}, e, s, ts, Unit{})

def start_complete(ctx: D.Context, args: D.Value, +e: D.Schema, +s: D.State,
  +ts: List<&2, S.OperationEvent>) -> Complete(S.start(Client.program(), ctx, args), e, s, ts):
  command_complete(Client.analyze(args), e, s, ts)

def witnessed(+s: D.State, +ctx: D.Context, +args: D.Value,
  h: Complete(S.start(Client.program(), ctx, args), C.schema(), s, Nil{})) ->
  F.Terminates(Client.program(), C.schema(), s, ctx, args):
  match h:
    case (+n, w, events, r, eq):
      T.witness_program(n, Client.program(), C.schema(), s, ctx, args, (w, events, r, eq))

def B.terminates(s, ctx, args):
  +s = s
  +ctx = ctx
  +args = args
  witnessed(s, ctx, args, start_complete(ctx, args, C.schema(), s, Nil{}))
