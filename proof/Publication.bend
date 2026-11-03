# Composition: faithful preparation, obtained from the certified machine, publishes
# only valid state. Faithfulness is proved in Preparation, not granted by the client.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ./Foundations.bend as F
import ./Preparation.bend as P
import ./Safety.bend as G

def published(c: N.Conclusion) -> D.State:
  N.Conclusion{s, r, bs} = c
  s

def working(p: N.Prepared) -> D.State:
  N.Prepared{w, ts, r, bs} = p
  w

def response(p: N.Prepared) -> S.Response:
  N.Prepared{w, ts, r, bs} = p
  r

law conclusion_of_preparation_certified_and_is_valid:
  for c: S.Configuration
  for -code: String
  for p: S.Program
  for +ctx: D.Context
  for +args: D.Value
  for certificate: R.Certifies(c, code, p, ctx, args)
  for +s: D.State
  for valid: R.Valid(c, s)
  for cred: String
  for aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}
  for +n: Nat
  for -w: D.State
  for -ts: List<&2, S.OperationEvent>
  for -proposal: S.Response
  for obtained: {N.traverse(n, N.start(p, ctx, args, s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace}
  for +prepared: N.Prepared
  for faithful: P.Faithful(w, ts, R.finalize(proposal, c, w), prepared)
  R.Valid(c, published(N.conclude(prepared, s)))
def conclusion_of_preparation_certified_and_is_valid(c, code, p, ctx, args,
  certificate, s, valid, cred, aut, n, w, ts, proposal, obtained, prepared, faithful):
  match prepared faithful:
    case N.Prepared{wp, events, rp, bs} L.Both{+equality, message}:
      %Equal.sym(D.State, wp, w,
        Equal.cong(N.Prepared, D.State, working,
          N.Prepared{wp, events, rp, bs}, N.Prepared{w, ts, R.finalize(proposal, c, w), bs}, equality)) :
          R.Valid(c, S.publish(rp, s, _))
      G.conclusion_certified_preserves_validity(rp, c, code, p, ctx, args, certificate,
        s, valid, cred, aut, n, w, ts, proposal, obtained,
        Equal.sym(S.Response, rp, R.finalize(proposal, c, w),
          Equal.cong(N.Prepared, S.Response, response,
            N.Prepared{wp, events, rp, bs}, N.Prepared{w, ts, R.finalize(proposal, c, w), bs}, equality)))

law all_status_without_success_preserves_published:
  for r: S.Response
  for -s: D.State
  for -w: D.State
  for without_success: {status_success(r) == False{} : Bool}
  {S.publish(r, s, w) == s : D.State}

def status_success(r: S.Response) -> Bool:
  S.Response{status, value} = r
  S.is_success(status)

def all_status_without_success_preserves_published(r, s, w, without_success):
  match r:
    case S.Response{S.Success{}, v}:
      F.absurd_boolean({S.publish(S.Response{S.Success{}, v}, s, w) == s : D.State},
        Equal.sym(Bool, True{}, False{}, without_success))
    case S.Response{S.Refusal{}, v}:
      {==}
    case S.Response{S.Input{}, v}:
      {==}
    case S.Response{S.Authentication{}, v}:
      {==}
    case S.Response{S.Certificate{}, v}:
      {==}
    case S.Response{S.DataError{}, v}:
      {==}
    case S.Response{S.Limit{}, v}:
      {==}
    case S.Response{S.Failure{}, v}:
      {==}
