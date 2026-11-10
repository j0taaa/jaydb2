# Policy helpers: a local proof per operation covers every prefix.
import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../contract/Logic.bend as L
import ../../../src/Termination.bend as T
import ../../../src/ValidationFinal.bend as V
import ./Policy.bend as P
import ./Ownership.bend as O
import ../../../library/Laws.bend as G

def Safe(d: Nat, ctx: D.Context, a: S.Action) -> Type:
  G.Safe(~P.Allowed, d, ctx, a)

def Good(+ctx: D.Context, +s: D.State, ts: List<&2, S.OperationEvent>) -> Data:
  P.Both<P.Owners(s), P.Both<{D.context_present(s, ctx) == True{} : Bool}, P.AllAllowed(ctx, ts)>>

def Path(ctx: D.Context, +p: S.Trace) -> Data:
  Good(ctx, S.state_execution_trace(p), S.events_execution_trace(p))

def rewind(-ctx: D.Context, -a: S.Trace, -b: S.Trace,
  eq: {a == b : S.Trace}, h: Path(ctx, b)) -> Path(ctx, a):
  %Equal.sym(S.Trace, a, b, eq) : Path(ctx, _)
  h

def append(+ctx: D.Context, ts: List<&2, S.OperationEvent>, +op: D.Operation, +ef: S.Effect,
  h: P.AllAllowed(ctx, ts), p: P.Allowed(ctx, op)) -> P.AllAllowed(ctx, S.append(ts, S.OperationEvent{op, ef})):
  match ts h:
    case Nil{} Unit{}: P.Both{p, Unit{}}
    case Con{S.OperationEvent{o, effect}, tail} P.Both{hp, ht}:
      P.Both{hp, append(ctx, tail, op, ef, ht, p)}

def result(res: D.ResultOp, +n: Nat, +ctx: D.Context, +e: D.Schema,
  +s: D.State, +ts: List<&2, S.OperationEvent>, +op: D.Operation, -k: S.Return -> S.Action,
  +h: Good(ctx, s, ts), +p: P.Allowed(ctx, op), post: O.Preserves(ctx, res),
  rec: @r: S.Return -> @w: D.State -> @ef: S.Effect ->
    Good(ctx, w, S.append(ts, S.OperationEvent{op, ef})) ->
    Path(ctx, T.observe(n, k(r), e, w, S.append(ts, S.OperationEvent{op, ef})))) ->
  Path(ctx, S.resume_execution_trace(n, S.apply(res, s, op, k), e, ts)):
  match res:
    case D.FailureData{}:
      match h:
        case P.Both{owners, P.Both{present, hist}}:
          rewind(ctx, S.resume_execution_trace(n, S.OperationFailed{s, S.OperationEvent{op, S.ErrorOfData{}}}, e, ts),
            S.Final{s, S.append(ts, S.OperationEvent{op, S.ErrorOfData{}}), S.response_error(S.DataError{})},
            T.failure_of_operation(n, s, S.OperationEvent{op, S.ErrorOfData{}}, e, ts),
            P.Both{owners, P.Both{present, append(ctx, ts, op, S.ErrorOfData{}, hist, p)}})
    case D.Observed{+obs}:
      match h:
        case P.Both{owners, P.Both{present, hist}}:
          rewind(ctx, S.resume_execution_trace(n, S.Continue{s, k(S.Datum{obs}), S.OperationEvent{op, S.Reading{obs}}}, e, ts),
            T.observe(n, k(S.Datum{obs}), e, s, S.append(ts, S.OperationEvent{op, S.Reading{obs}})),
            T.continuation(n, s, k(S.Datum{obs}), S.OperationEvent{op, S.Reading{obs}}, e, ts),
            rec(S.Datum{obs}, s, S.Reading{obs}, P.Both{owners, P.Both{present, append(ctx, ts, op, S.Reading{obs}, hist, p)}}))
    case D.Changed{+w}:
      match h post:
        case P.Both{owners, P.Both{present, hist}} L.Both{new, authenticated}:
          rewind(ctx, S.resume_execution_trace(n, S.Continue{w, k(S.UnitValue{}), S.OperationEvent{op, S.Write{}}}, e, ts),
            T.observe(n, k(S.UnitValue{}), e, w, S.append(ts, S.OperationEvent{op, S.Write{}})),
            T.continuation(n, w, k(S.UnitValue{}), S.OperationEvent{op, S.Write{}}, e, ts),
            rec(S.UnitValue{}, w, S.Write{}, P.Both{new, P.Both{authenticated, append(ctx, ts, op, S.Write{}, hist, p)}}))

def safe(d: Nat, +n: Nat, a: S.Action, +ctx: D.Context, +e: D.Schema,
  +s: D.State, +ts: List<&2, S.OperationEvent>, h: Safe(d, ctx, a), +good: Good(ctx, s, ts)) ->
  Path(ctx, T.observe(n, a, e, s, ts)):
  match d h:
    case Zero{} h: L.ex_false(Path(ctx, T.observe(n, a, e, s, ts)), h)
    case Succ{m} h:
      match n:
        case Zero{}: good
        case Succ{rest}:
          match a h:
            case S.Finish{v} Unit{}:
              rewind(ctx, S.resume_execution_trace(rest, S.Stopped{s, S.Response{S.Success{}, v}}, e, ts),
                S.Final{s, ts, S.Response{S.Success{}, v}}, T.stopped(rest, s, S.Response{S.Success{}, v}, e, ts), good)
            case S.Refuse{v} Unit{}:
              rewind(ctx, S.resume_execution_trace(rest, S.Stopped{s, S.Response{S.Refusal{}, v}}, e, ts),
                S.Final{s, ts, S.Response{S.Refusal{}, v}}, T.stopped(rest, s, S.Response{S.Refusal{}, v}, e, ts), good)
            case S.Access{+op, k} L.Both{+p, cont}:
              match good:
                case P.Both{+owners, P.Both{+aut, +hist}}:
                  result(D.operate(e, s, op), rest, ctx, e, s, ts, op, k,
                    P.Both{owners, P.Both{aut, hist}}, p, O.operation_preserves(e, s, ctx, op, owners, aut, p),
                    +r => w => ef => hp => safe(m, rest, k(r), ctx, e, w, S.append(ts, S.OperationEvent{op, ef}), cont(r), hp))

def prefix(-e: D.Schema, -lim: S.Limits, -amb: String, -s: D.State, -ctx: D.Context,
  -code: String, -args: D.Value, -w: D.State, -ts: List<&2, S.OperationEvent>,
  +owners: P.Owners(w), +hist: P.AllAllowed(ctx, ts)) -> R.SafetyPrefix(P.config(e, lim, amb), s, ctx, code, args, w, ts):
  L.Both{L.Both{P.Both{owners, hist}, Unit{}}, L.Both{P.Both{owners, hist}, Unit{}}}

def finalize(r: S.Response, +e: D.Schema, +lim: S.Limits, +amb: String, +w: D.State, owners: P.Owners(w)) ->
  R.PublicationValid(R.finalize(r, P.config(e, lim, amb), w), P.config(e, lim, amb), w):
  match r:
    case S.Response{S.Success{}, +v}:
      V.state_validated(D.structure(e, w), R.fits(R.limit_state(lim), D.state_value(w)),
        e, S.MoreOneLaw{P.Rule, S.NoneLaw{}}, lim, amb, w, v, D.value_valid(v),
        R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})), {==}, {==}, L.Both{owners, Unit{}})
    case S.Response{S.Refusal{}, +v}:
      V.refusal_validated(D.value_valid(v), R.fits(R.limit_response(lim), S.response_value(S.Response{S.Refusal{}, v})), P.config(e, lim, amb), w, v)
    case S.Response{S.Input{}, v}: Unit{}
    case S.Response{S.Authentication{}, v}: Unit{}
    case S.Response{S.Certificate{}, v}: Unit{}
    case S.Response{S.DataError{}, v}: Unit{}
    case S.Response{S.Limit{}, v}: Unit{}
    case S.Response{S.Failure{}, v}: Unit{}

def execution_trace(p: S.Trace, +e: D.Schema, +lim: S.Limits, +amb: String, -s: D.State,
  -ctx: D.Context, -code: String, -args: D.Value, h: Path(ctx, p)) ->
  R.SafetyTrace(p, P.config(e, lim, amb), s, ctx, code, args):
  match p h:
    case S.Prefix{w, ts} P.Both{owners, P.Both{aut, hist}}: prefix(e, lim, amb, s, ctx, code, args, w, ts, owners, hist)
    case S.Final{+w, ts, r} P.Both{+owners, P.Both{aut, +hist}}:
      L.Both{prefix(e, lim, amb, s, ctx, code, args, w, ts, owners, hist),
        L.Both{L.Both{P.Both{owners, hist}, Unit{}}, finalize(r, e, lim, amb, w, owners)}}

def finite(d: Nat, a: S.Action, +ctx: D.Context, h: Safe(d, ctx, a)) -> T.Finite(d, a):
  match d a h:
    case Zero{} a h: L.ex_false(T.Finite(0n, a), h)
    case Succ{m} S.Finish{v} Unit{}: Unit{}
    case Succ{m} S.Refuse{v} Unit{}: Unit{}
    case Succ{m} S.Access{op, k} L.Both{p, cont}: +r => finite(m, k(r), ctx, cont(r))
