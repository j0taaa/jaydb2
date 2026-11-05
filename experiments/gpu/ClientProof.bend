import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Requirements.bend as R
import ./Logic.bend as L
import ./Termination.bend as T
import ./ValidationFinal.bend as V
import ./Client.bend as Client
import ./Configuration.bend as C
import ./Instance.bend as I
import ./Bindings.bend as B

def Safe(d: Nat, +ctx: D.Context, a: S.Action) -> Type:
  match d:
    case Zero{}: Empty
    case Succ{m}:
      match a:
        case S.Finish{v}: Unit
        case S.Refuse{v}: Unit
        case S.Access{op, k}: L.E<C.Allowed(ctx, op), @r: S.Return -> Safe(m, ctx, k(r))>

def append(+ctx: D.Context, ts: List<&2, S.OperationEvent>, +op: D.Operation,
  +ef: S.Effect, h: C.AllAllowed(ctx, ts), p: C.Allowed(ctx, op)) ->
  C.AllAllowed(ctx, S.append(ts, S.OperationEvent{op, ef})):
  match ts h:
    case Nil{} Unit{}: C.Both{p, Unit{}}
    case Con{S.OperationEvent{o, effect}, tail} C.Both{hp, ht}:
      C.Both{hp, append(ctx, tail, op, ef, ht, p)}

def rewind(-ctx: D.Context, -a: S.Trace, -b: S.Trace,
  eq: {a == b : S.Trace}, p: C.AllAllowed(ctx, S.events_execution_trace(b))) ->
  C.AllAllowed(ctx, S.events_execution_trace(a)):
  %Equal.sym(S.Trace, a, b, eq): C.AllAllowed(ctx, S.events_execution_trace(_))
  p

def result(res: D.ResultOp, +n: Nat, +ctx: D.Context, +e: D.Schema,
  +s: D.State, +ts: List<&2, S.OperationEvent>, +op: D.Operation, -k: S.Return -> S.Action,
  +hist: C.AllAllowed(ctx, ts), +p: C.Allowed(ctx, op),
  rec: @r: S.Return -> @w: D.State -> @ef: S.Effect ->
    C.AllAllowed(ctx, S.append(ts, S.OperationEvent{op, ef})) ->
    C.AllAllowed(ctx, S.events_execution_trace(T.observe(n, k(r), e, w, S.append(ts, S.OperationEvent{op, ef}))))) ->
  C.AllAllowed(ctx, S.events_execution_trace(S.resume_execution_trace(n, S.apply(res, s, op, k), e, ts))):
  match res:
    case D.FailureData{}:
      rewind(ctx, S.resume_execution_trace(n, S.OperationFailed{s, S.OperationEvent{op, S.ErrorOfData{}}}, e, ts),
        S.Final{s, S.append(ts, S.OperationEvent{op, S.ErrorOfData{}}), S.response_error(S.DataError{})},
        T.failure_of_operation(n, s, S.OperationEvent{op, S.ErrorOfData{}}, e, ts),
        append(ctx, ts, op, S.ErrorOfData{}, hist, p))
    case D.Observed{+obs}:
      rewind(ctx, S.resume_execution_trace(n, S.Continue{s, k(S.Datum{obs}), S.OperationEvent{op, S.Reading{obs}}}, e, ts),
        T.observe(n, k(S.Datum{obs}), e, s, S.append(ts, S.OperationEvent{op, S.Reading{obs}})),
        T.continuation(n, s, k(S.Datum{obs}), S.OperationEvent{op, S.Reading{obs}}, e, ts),
        rec(S.Datum{obs}, s, S.Reading{obs}, append(ctx, ts, op, S.Reading{obs}, hist, p)))
    case D.Changed{+w}:
      rewind(ctx, S.resume_execution_trace(n, S.Continue{w, k(S.UnitValue{}), S.OperationEvent{op, S.Write{}}}, e, ts),
        T.observe(n, k(S.UnitValue{}), e, w, S.append(ts, S.OperationEvent{op, S.Write{}})),
        T.continuation(n, w, k(S.UnitValue{}), S.OperationEvent{op, S.Write{}}, e, ts),
        rec(S.UnitValue{}, w, S.Write{}, append(ctx, ts, op, S.Write{}, hist, p)))

def safe(d: Nat, +n: Nat, a: S.Action, +ctx: D.Context, +e: D.Schema,
  +s: D.State, +ts: List<&2, S.OperationEvent>, h: Safe(d, ctx, a), +hist: C.AllAllowed(ctx, ts)) ->
  C.AllAllowed(ctx, S.events_execution_trace(T.observe(n, a, e, s, ts))):
  match d h:
    case Zero{} h:
      L.ex_false(C.AllAllowed(ctx, S.events_execution_trace(T.observe(n, a, e, s, ts))), h)
    case Succ{m} h:
      match n:
        case Zero{}: hist
        case Succ{rest}:
          match a h:
            case S.Finish{v} Unit{}:
              rewind(ctx, S.resume_execution_trace(rest, S.Stopped{s, S.Response{S.Success{}, v}}, e, ts),
                S.Final{s, ts, S.Response{S.Success{}, v}}, T.stopped(rest, s, S.Response{S.Success{}, v}, e, ts), hist)
            case S.Refuse{v} Unit{}:
              rewind(ctx, S.resume_execution_trace(rest, S.Stopped{s, S.Response{S.Refusal{}, v}}, e, ts),
                S.Final{s, ts, S.Response{S.Refusal{}, v}}, T.stopped(rest, s, S.Response{S.Refusal{}, v}, e, ts), hist)
            case S.Access{+op, k} L.Both{p, cont}:
              result(D.operate(e, s, op), rest, ctx, e, s, ts, op, k, hist, p,
                +r => w => ef => hp => safe(m, rest, k(r), ctx, e, w, S.append(ts, S.OperationEvent{op, ef}), cont(r), hp))

def response_safe(cancel: Bool, r: S.Return, ctx: D.Context) -> Safe(1n, ctx, Client.respond(cancel, r)):
  match cancel r:
    case True{} _: Unit{}
    case False{} S.UnitValue{}: Unit{}
    case False{} S.Datum{obs}:
      match obs:
        case D.Cell{v}: Unit{}
        case D.RowAbsent{}: Unit{}
        case D.Existence{b}: Unit{}
        case D.Count{n}: Unit{}
        case D.Keys{xs}: Unit{}

def read_safe(+id: String, kind: String, cancel: Bool) ->
  Safe(2n, D.Context{id, kind}, Client.read(id, cancel)):
  L.Both{C.Both{{==}, {==}}, r => response_safe(cancel, r, D.Context{id, kind})}

def write_safe(+id: String, kind: String, value: String, cancel: Bool) ->
  Safe(3n, D.Context{id, kind}, Client.write(id, value, cancel)):
  L.Both{C.Both{{==}, {==}}, r => read_safe(id, kind, cancel)}

def program_safe(ctx: D.Context, args: D.Value) -> Safe(3n, ctx, S.start(Client.program(), ctx, args)):
  match ctx args:
    case D.Context{id, kind} D.VText{value}: write_safe(id, kind, value, False{})
    case D.Context{id, kind} D.VAbsent{}: write_safe(id, kind, "discarded", True{})
    case D.Context{id, kind} D.VBool{b}: write_safe(id, kind, "discarded", True{})
    case D.Context{id, kind} D.VInt{hi, lo}: write_safe(id, kind, "discarded", True{})
    case D.Context{id, kind} D.VListEmpty{}: write_safe(id, kind, "discarded", True{})
    case D.Context{id, kind} D.VList{h, t}: write_safe(id, kind, "discarded", True{})
    case D.Context{id, kind} D.VRecordEmpty{}: write_safe(id, kind, "discarded", True{})
    case D.Context{id, kind} D.VRecord{k, v, t}: write_safe(id, kind, "discarded", True{})

def prefix(-s: D.State, -ctx: D.Context, -code: String, -args: D.Value,
  -w: D.State, -ts: List<&2, S.OperationEvent>, +h: C.AllAllowed(ctx, ts)) ->
  R.SafetyPrefix(C.config(), s, ctx, code, args, w, ts):
  L.Both{L.Both{h, Unit{}}, L.Both{h, Unit{}}}

def execution_trace(p: S.Trace, -s: D.State, -ctx: D.Context, -code: String, -args: D.Value,
  +h: C.AllAllowed(ctx, S.events_execution_trace(p))) -> R.SafetyTrace(p, C.config(), s, ctx, code, args):
  match p:
    case S.Prefix{w, ts}: prefix(s, ctx, code, args, w, ts, h)
    case S.Final{+w, ts, r}:
      L.Both{prefix(s, ctx, code, args, w, ts, h), L.Both{L.Both{h, Unit{}},
        V.finalize_preserves_laws_stable(r, C.config(), w, state => L.Both{Unit{}, Unit{}})}}

def B.certificate(ctx, args, s, valid, identity, n):
  +ctx = ctx
  +args = args
  +n = n
  +s = s
  execution_trace(S.execute(n, Client.program(), C.schema(), s, ctx, args),
    s, ctx, B.code(), args,
    rewind(ctx, S.execute(n, Client.program(), C.schema(), s, ctx, args),
      T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
      Equal.sym(S.Trace,
        T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
        S.execute(n, Client.program(), C.schema(), s, ctx, args),
        T.reference(n, S.start(Client.program(), ctx, args), C.schema(), s)),
      safe(3n, n, S.start(Client.program(), ctx, args), ctx, C.schema(), s, Nil{},
        program_safe(ctx, args), Unit{})))

def finite(d: Nat, a: S.Action, +ctx: D.Context, h: Safe(d, ctx, a)) -> T.Finite(d, a):
  match d a h:
    case Zero{} a h: L.ex_false(T.Finite(0n, a), h)
    case Succ{m} S.Finish{v} Unit{}: Unit{}
    case Succ{m} S.Refuse{v} Unit{}: Unit{}
    case Succ{m} S.Access{op, k} L.Both{p, cont}:
      +r => finite(m, k(r), ctx, cont(r))

def B.terminates(s, ctx, args):
  +context = ctx
  +arguments = args
  T.program_finite(3n, Client.program(), C.schema(), s, context, arguments, finite(3n, S.start(Client.program(), context, arguments), context, program_safe(context, arguments)))
