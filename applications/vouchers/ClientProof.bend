import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Logic.bend as L
import ./Requirements.bend as R
import ./Termination.bend as T
import ./ValidationFinal.bend as V
import ./Policy.bend as P
import ./Proofs.bend as H
import ./Configuration.bend as C
import ./Voucher.bend as F
import ./Initial.bend as Initial
import ./Receipts.bend as A
import ./ReceiptLaws.bend as RL
import ./Client.bend as Client
import ./Instance.bend as I
import ./Bindings.bend as B

def written_safe(+n: Nat, +ctx: D.Context, -a: S.Action,
  h: H.Safe(Succ{n}, ctx, a), r: S.Return) -> H.Safe(Succ{n}, ctx, A.written(a, r)):
  match r:
    case S.UnitValue{}: h
    case S.Datum{obs}: Unit{}

def finish_safe(n: Nat, ctx: D.Context, cancel: Bool, value: String) ->
  H.Safe(Succ{n}, ctx, F.finish(cancel, value)):
  match cancel:
    case True{}: Unit{}
    case False{}: Unit{}

def create_safe(+id: String, +kind: String, +request: String, input: String, +cancel: Bool) ->
  H.Safe(3n, D.Context{id, kind}, F.create(id, request, input, cancel)):
  L.Both{P.Both{{==}, {==}}, r => written_safe(1n, D.Context{id, kind},
    A.put(id, F.receipt(request), F.fields(id, F.receipt(request), F.canonical(input, cancel), F.operation(), F.voucher(request)),
      F.finish(cancel, F.voucher(request))),
    L.Both{P.Both{{==}, {==}}, r => written_safe(0n, D.Context{id, kind}, F.finish(cancel, F.voucher(request)),
      finish_safe(0n, D.Context{id, kind}, cancel, F.voucher(request)), r)}, r)}

def finish_result_safe(n: Nat, ctx: D.Context, value: A.Lookup) ->
  H.Safe(Succ{n}, ctx, F.finish_result(value)):
  match value:
    case A.StoredText{v}: Unit{}
    case A.Missing{}: Unit{}
    case A.Unexpected{}: Unit{}

def result_safe(n: Nat, ctx: D.Context, request: String, r: S.Return) ->
  H.Safe(Succ{n}, ctx, F.result(request, r)):
  finish_result_safe(n, ctx, A.observed(r))

def operation_match_safe(ok: Bool, +id: String, +kind: String, +request: String) ->
  H.Safe(2n, D.Context{id, kind}, A.operation_match(ok, id, F.receipt(request), F.result(request))):
  match ok:
    case True{}: L.Both{{==}, r => result_safe(0n, D.Context{id, kind}, request, r)}
    case False{}: Unit{}

def operation_value_safe(+id: String, +kind: String, +request: String, value: A.Lookup) ->
  H.Safe(2n, D.Context{id, kind}, A.operation_value(id, F.receipt(request), F.operation(), F.result(request), value)):
  match value:
    case A.StoredText{v}: operation_match_safe(String.eq(v, F.operation()), id, kind, request)
    case A.Missing{}: Unit{}
    case A.Unexpected{}: Unit{}

def operation_safe(+id: String, +kind: String, +request: String, input: String, op: S.Return) ->
  H.Safe(2n, D.Context{id, kind}, F.operation_seen(id, request, input, op)):
  operation_value_safe(id, kind, request, A.observed(op))

def input_match_safe(ok: Bool, +id: String, +kind: String, +request: String, +input: String) ->
  H.Safe(3n, D.Context{id, kind}, A.input_match(ok, id, F.receipt(request), F.operation(), F.result(request))):
  match ok:
    case True{}: L.Both{{==}, r => operation_safe(id, kind, request, input, r)}
    case False{}: Unit{}

def input_value_safe(+id: String, +kind: String, +request: String, +input: String, +cancel: Bool, value: A.Lookup) ->
  H.Safe(3n, D.Context{id, kind}, A.input_value(id, F.receipt(request), F.operation(), F.canonical(input, cancel),
    F.create(id, request, input, cancel), F.result(request), value)):
  match value:
    case A.Missing{}: create_safe(id, kind, request, input, cancel)
    case A.StoredText{v}: input_match_safe(String.eq(v, F.canonical(input, cancel)), id, kind, request, input)
    case A.Unexpected{}: Unit{}

def input_safe(+id: String, +kind: String, +request: String, +input: String, +cancel: Bool, r: S.Return) ->
  H.Safe(3n, D.Context{id, kind}, F.input_seen(id, request, input, cancel, r)):
  input_value_safe(id, kind, request, input, cancel, A.observed(r))

def command_safe(+id: String, +kind: String, p: F.Command) ->
  H.Safe(4n, D.Context{id, kind}, F.command(id, p)):
  match p:
    case F.Issue{+request, +input, cancel}:
      L.Both{{==}, r => input_safe(id, kind, request, input, cancel, r)}
    case F.Retire{+request}:
      L.Both{{==}, r => written_safe(2n, D.Context{id, kind},
        S.Access{D.RemoveRow{D.Application{id}, F.voucher(request)}, A.written(S.Finish{D.VText{"retired"}})},
        L.Both{{==}, r => written_safe(1n, D.Context{id, kind}, S.Finish{D.VText{"retired"}}, Unit{}, r)}, r)}
    case F.Inspect{request}: L.Both{{==}, r => Unit{}}
    case F.Permission{+enabled}:
      L.Both{P.Both{{==}, {==}}, r => written_safe(2n, D.Context{id, kind}, S.Finish{D.VText{"permission updated"}}, Unit{}, r)}
    case F.Invalid{}: Unit{}

def weaken(d: Nat, +ctx: D.Context, a: S.Action, h: H.Safe(d, ctx, a)) ->
  H.Safe(Succ{d}, ctx, a):
  match d a h:
    case Zero{} a h: L.ex_false(H.Safe(1n, ctx, a), h)
    case Succ{n} S.Finish{v} Unit{}: Unit{}
    case Succ{n} S.Refuse{v} Unit{}: Unit{}
    case Succ{n} S.Access{op, k} L.Both{p, cont}:
      L.Both{p, +r => weaken(n, ctx, k(r), cont(r))}

def permit_safe(ok: Bool, +id: String, +kind: String, p: F.Command) ->
  H.Safe(4n, D.Context{id, kind}, F.permit(ok, id, p)):
  match ok:
    case True{}: command_safe(id, kind, p)
    case False{}: Unit{}

def permitted_safe(+id: String, +kind: String, p: F.Command, r: S.Return) ->
  H.Safe(4n, D.Context{id, kind}, F.permitted(id, p, r)):
  permit_safe(F.enabled(r), id, kind, p)

def sized_safe(ok: Bool, +id: String, +kind: String, +request: String, +input: String, +cancel: Bool) ->
  H.Safe(5n, D.Context{id, kind}, F.sized(ok, id, request, input, cancel)):
  match ok:
    case False{}: Unit{}
    case True{}: L.Both{{==}, r => permitted_safe(id, kind, F.Issue{request, input, cancel}, r)}

def dispatch_safe(+id: String, +kind: String, p: F.Command) ->
  H.Safe(5n, D.Context{id, kind}, F.dispatch(id, p)):
  match p:
    case F.Permission{+enabled}:
      weaken(4n, D.Context{id, kind}, F.command(id, F.Permission{enabled}), command_safe(id, kind, F.Permission{enabled}))
    case F.Issue{+request, +input, +cancel}:
      sized_safe(Nat.is_le(String.length(request), 64n), id, kind, request, input, cancel)
    case F.Retire{+request}: L.Both{{==}, r => permitted_safe(id, kind, F.Retire{request}, r)}
    case F.Inspect{+request}: L.Both{{==}, r => permitted_safe(id, kind, F.Inspect{request}, r)}
    case F.Invalid{}: Unit{}

def program_safe(ctx: D.Context, args: D.Value) -> H.Safe(5n, ctx, S.start(Client.program(), ctx, args)):
  D.Context{id, kind} = ctx
  dispatch_safe(id, kind, F.analyze(args))

def owners_initial(-s: D.State, valid: R.Valid(C.config(), s)) -> P.Owners(s):
  match valid:
    case L.Both{structure, L.Both{owners, remaining}}: owners

def history_initial(-s: D.State, valid: R.Valid(C.config(), s)) ->
  RL.State(~F.program(), ~Initial.origin, C.schema(), C.limits(), s):
  match valid:
    case L.Both{structure, L.Both{owners, L.Both{history, rest}}}: history

def publication_cases(ok: Bool, fits: Bool, payload: Bool, size: Bool,
  +s: D.State, +w: D.State, +v: D.Value, owners: P.Owners(w),
  he: {D.structure(C.schema(), w) == ok : Bool},
  ht: {R.fits(R.limit_state(C.limits()), D.state_value(w)) == fits : Bool},
  h: RL.State(~F.program(), ~Initial.origin, C.schema(), C.limits(),
    S.publish(R.state_technical_cases(ok, fits, R.response_technique_cases(payload, size, S.Response{S.Success{}, v})), s, w))) ->
  R.PublicationValid(R.state_technical_cases(ok, fits, R.response_technique_cases(payload, size, S.Response{S.Success{}, v})), C.config(), w):
  match ok fits payload size:
    case True{} True{} True{} True{}:
      V.valid(C.schema(), C.laws(), C.limits(), C.environment(), w, he, ht,
        L.Both{owners, L.Both{h, Unit{}}})
    case True{} True{} False{} _: Unit{}
    case True{} True{} True{} False{}: Unit{}
    case False{} _ _ _: Unit{}
    case True{} False{} _ _: Unit{}

def finalize(r: S.Response, +s: D.State, +w: D.State, owners: P.Owners(w),
  h: RL.State(~F.program(), ~Initial.origin, C.schema(), C.limits(), S.publish(R.finalize(r, C.config(), w), s, w))) ->
  R.PublicationValid(R.finalize(r, C.config(), w), C.config(), w):
  match r:
    case S.Response{S.Success{}, +v}:
      publication_cases(D.structure(C.schema(), w), R.fits(R.limit_state(C.limits()), D.state_value(w)),
        D.value_valid(v), R.fits(R.limit_response(C.limits()), S.response_value(S.Response{S.Success{}, v})),
        s, w, v, owners, {==}, {==}, h)
    case S.Response{S.Refusal{}, +v}:
      V.refusal_validated(D.value_valid(v), R.fits(R.limit_response(C.limits()), S.response_value(S.Response{S.Refusal{}, v})), C.config(), w, v)
    case S.Response{S.Input{}, v}: Unit{}
    case S.Response{S.Authentication{}, v}: Unit{}
    case S.Response{S.Certificate{}, v}: Unit{}
    case S.Response{S.DataError{}, v}: Unit{}
    case S.Response{S.Limit{}, v}: Unit{}
    case S.Response{S.Failure{}, v}: Unit{}

def prefix(+n: Nat, +s: D.State, +ctx: D.Context, +args: D.Value, -code: String,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +owners: P.Owners(w), +hist: P.AllAllowed(ctx, ts),
  +initial: RL.State(~F.program(), ~Initial.origin, C.schema(), C.limits(), s),
  +at: RL.At(S.execute(n, F.program(), C.schema(), s, ctx, args), w, ts)) ->
  R.SafetyPrefix(C.config(), s, ctx, code, args, w, ts):
  L.Both{L.Both{P.Both{owners, hist}, L.Both{RL.Both{initial, (n, at)}, Unit{}}},
    L.Both{P.Both{owners, hist}, L.Both{RL.Both{initial, (n, RL.Both{at, Unit{}})}, Unit{}}}}

def trace(p: S.Trace, +n: Nat, +s: D.State, +ctx: D.Context, +args: D.Value, -code: String,
  +eq: {S.execute(n, F.program(), C.schema(), s, ctx, args) == p : S.Trace},
  +initial: RL.State(~F.program(), ~Initial.origin, C.schema(), C.limits(), s), h: H.Path(ctx, p)) ->
  R.SafetyTrace(p, C.config(), s, ctx, code, args):
  match p h:
    case S.Prefix{+w, +ts} P.Both{owners, P.Both{aut, hist}}:
      prefix(n, s, ctx, args, code, w, ts, owners, hist, initial,
        (%Equal.sym(S.Trace, S.execute(n, F.program(), C.schema(), s, ctx, args), S.Prefix{w, ts}, eq) : RL.At(_, w, ts) RL.Both{{==}, {==}}))
    case S.Final{+w, +ts, +r} P.Both{+owners, P.Both{aut, +hist}}:
      +at = {(%Equal.sym(S.Trace, S.execute(n, F.program(), C.schema(), s, ctx, args), S.Final{w, ts, r}, eq) : RL.At(_, w, ts) RL.Both{{==}, {==}}) : RL.At(S.execute(n, F.program(), C.schema(), s, ctx, args), w, ts)}
      L.Both{prefix(n, s, ctx, args, code, w, ts, owners, hist, initial, at),
        L.Both{L.Both{P.Both{owners, hist}, L.Both{RL.Both{initial, (n, RL.Both{at,
          (%Equal.sym(S.Trace, S.execute(n, F.program(), C.schema(), s, ctx, args), S.Final{w, ts, r}, eq) :
            RL.Success(_, C.schema(), C.limits(), R.finalize(r, C.config(), w))
              (%Equal.sym(S.Response, R.finalize(r, C.config(), w), R.finalize(r, RL.technical(C.schema(), C.limits()), w),
                RL.finalize_equivalent(~C.laws(), r, C.schema(), C.limits(), C.environment(), w)) :
                RL.Success(S.Final{w, ts, r}, C.schema(), C.limits(), _) RL.finalized(C.schema(), C.limits(), w, ts, r)))})}, Unit{}}}, finalize(r, s, w, owners,
          (%Equal.sym(S.Response, R.finalize(r, C.config(), w), R.finalize(r, RL.technical(C.schema(), C.limits()), w),
            RL.finalize_equivalent(~C.laws(), r, C.schema(), C.limits(), C.environment(), w)) :
            RL.State(~F.program(), ~Initial.origin, C.schema(), C.limits(), S.publish(_, s, w))
          (%eq : RL.State(~F.program(), ~Initial.origin, C.schema(), C.limits(), RL.advance(_, C.schema(), C.limits(), s))
            RL.extend(~F.program(), ~Initial.origin, C.schema(), C.limits(), s, ctx, args, n, initial))))}}

def certify(+ctx: D.Context, +args: D.Value, -code: String, +s: D.State,
  valid: R.Valid(C.config(), s), identity: {D.context_present(s, ctx) == True{} : Bool}, +n: Nat) ->
  R.SafetyTrace(S.execute(n, Client.program(), C.schema(), s, ctx, args), C.config(), s, ctx, code, args):
  match valid:
    case L.Both{structure, L.Both{+owners, L.Both{+initial, remaining}}}:
      trace(S.execute(n, Client.program(), C.schema(), s, ctx, args), n, s, ctx, args, code, {==}, initial,
        H.rewind(ctx, S.execute(n, Client.program(), C.schema(), s, ctx, args),
          T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
          Equal.sym(S.Trace, T.observe(n, S.start(Client.program(), ctx, args), C.schema(), s, Nil{}),
            S.execute(n, Client.program(), C.schema(), s, ctx, args), T.reference(n, S.start(Client.program(), ctx, args), C.schema(), s)),
          H.safe(5n, n, S.start(Client.program(), ctx, args), ctx, C.schema(), s, Nil{},
            program_safe(ctx, args), P.Both{owners, P.Both{identity, Unit{}}})))

def B.certificate(s, valid, identity, n):
  certify(I.context(), I.arguments(), B.code(), s, valid, identity, n)

def B.terminates(s, ctx, args):
  +ctx = ctx
  +args = args
  T.program_finite(5n, Client.program(), C.schema(), s, ctx, args,
    H.finite(5n, S.start(Client.program(), ctx, args), ctx, program_safe(ctx, args)))
