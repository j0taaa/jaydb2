# Validity, limits, publication and the exact client certificate type.
import Base
import ./Data.bend as D
import ./Bytes.bend as B
import ./Protocol.bend as P
import ./Semantics.bend as S
import ./Logic.bend as L

def limit_message(l: S.Limits) -> Nat:
  S.Limits{a, b, c} = l
  a

def limit_state(l: S.Limits) -> Nat:
  S.Limits{a, b, c} = l
  b

def limit_response(l: S.Limits) -> Nat:
  S.Limits{a, b, c} = l
  c

def fits_result(r: Maybe<&2, List<&2, U32>>, limit: Nat) -> Bool:
  match r:
    case None{}:
      False{}
    case Some{bs}:
      Nat.is_le(B.length(bs), limit)

def fits(limit: Nat, value: D.Value) -> Bool:
  fits_result(P.encode(value), limit)

def fits_error(+limit: Nat, s: S.Status) -> Bool:
  fits(limit, S.response_value(S.response_error(s)))

def limits_all_valid(l: S.Limits) -> Bool:
  match l:
    case S.Limits{+msg, +est, +resp}:
      P.representable_result(B.length64(msg)) &&
      P.representable_result(B.length64(est)) &&
      P.representable_result(B.length64(resp)) &&
      fits_error(resp, S.Input{}) && fits_error(resp, S.Authentication{}) &&
      fits_error(resp, S.Certificate{}) && fits_error(resp, S.DataError{}) &&
      fits_error(resp, S.Limit{}) && fits_error(resp, S.Failure{})

# Laws are already terms of type Situation -> Type. Their source/dependency
# closure and environment version belong to BindingEnvironment.
def configuration_is_valid(c: S.Configuration) -> Bool:
  S.Configuration{e, ls, lim, amb} = c
  D.schema_valid(e) && limits_all_valid(lim) && D.unicode_valid(amb)

def structure(c: S.Configuration, +s: D.State) -> Bool:
  S.Configuration{e, ls, lim, amb} = c
  D.structure(e, s) && fits(limit_state(lim), D.state_value(s))

def Valid(-c: S.Configuration, -s: D.State) -> Type:
  L.E<{structure(c, s) == True{} : Bool}, S.Satisfies(c, S.Stable{s})>

def response_technique_cases(ok: Bool, fits: Bool, r: S.Response) -> S.Response:
  match ok fits:
    case False{} _:
      S.response_error(S.DataError{})
    case True{} False{}:
      S.response_error(S.Limit{})
    case True{} True{}:
      r

def state_technical_cases(ok: Bool, fits: Bool, r: S.Response) -> S.Response:
  match ok fits:
    case False{} _:
      S.response_error(S.DataError{})
    case True{} False{}:
      S.response_error(S.Limit{})
    case True{} True{}:
      r

# Final order: proposal structural validity; limits; response preparation.
# Internal data validation does not deliver data to the program.
def finalize(r: S.Response, c: S.Configuration, +w: D.State) -> S.Response:
  match r c:
    case S.Response{S.Success{}, +v} S.Configuration{e, ls, +lim, amb}:
      state_technical_cases(D.structure(e, w),
        fits(limit_state(lim), D.state_value(w)),
        response_technique_cases(D.value_valid(v),
          fits(limit_response(lim), S.response_value(S.Response{S.Success{}, v})),
          S.Response{S.Success{}, v}))
    case S.Response{S.Refusal{}, +v} S.Configuration{e, ls, lim, amb}:
      response_technique_cases(D.value_valid(v),
        fits(limit_response(lim), S.response_value(S.Response{S.Refusal{}, v})),
        S.Response{S.Refusal{}, v})
    case S.Response{s, v} S.Configuration{e, ls, lim, amb}:
      S.response_error(s)

def PublicationValid(r: S.Response, -c: S.Configuration, -w: D.State) -> Type:
  match r:
    case S.Response{S.Success{}, v}:
      Valid(c, w)
    case _:
      Unit

def SafetyFinal(-c: S.Configuration, -s: D.State, -ctx: D.Context,
  -code: String, -args: D.Value, -w: D.State,
  -ts: List<&2, S.OperationEvent>, -r: S.Response) -> Type:
  L.E<S.Satisfies(c, S.Closed{s, ctx, code, args, w, ts, r}),
    PublicationValid(r, c, w)>

# A prefix admits actual failure at any point, but not a fictitious limit.
# Logical state/response limits belong to the result of finalize.
def SafetyPrefix(-c: S.Configuration, -s: D.State, -ctx: D.Context,
  -code: String, -args: D.Value, -w: D.State,
  -ts: List<&2, S.OperationEvent>) -> Type:
  L.E<S.Satisfies(c, S.Executing{s, ctx, code, args, w, ts}),
    S.Satisfies(c, S.Closed{s, ctx, code, args, w, ts, S.response_error(S.Failure{})})>

def SafetyTrace(p: S.Trace, -c: S.Configuration, -s: D.State,
  -ctx: D.Context, -code: String, -args: D.Value) -> Type:
  match p:
    case S.Prefix{w, ts}:
      SafetyPrefix(c, s, ctx, code, args, w, ts)
    case S.Final{w, ts, r}:
      L.E<SafetyPrefix(c, s, ctx, code, args, w, ts),
        SafetyFinal(c, s, ctx, code, args, w, ts, finalize(r, c, w))>

# The proof is universal over valid states with the authenticated context.
# It receives no private claim from the requester as an axiom.
def Certifies(-c: S.Configuration, -code: String, -p: S.Program,
  -ctx: D.Context, -args: D.Value) -> Type:
  @s: D.State -> Valid(c, s) ->
    {D.context_present(s, ctx) == True{} : Bool} ->
    @n: Nat -> SafetyTrace(S.execute(n, p, S.schema(c), s, ctx, args),
      c, s, ctx, code, args)

# These lemmas only use a certificate actually supplied.
# They neither manufacture a certificate nor prove the server's eight laws.
law certificate_covers_prefix_zero:
  for -c: S.Configuration
  for -code: String
  for -p: S.Program
  for -ctx: D.Context
  for -args: D.Value
  for certificate: Certifies(c, code, p, ctx, args)
  for s: D.State
  for valid: Valid(c, s)
  for identity: {D.context_present(s, ctx) == True{} : Bool}
  SafetyPrefix(c, s, ctx, code, args, s, Nil{})

def certificate_covers_prefix_zero(c, code, p, ctx, args, certificate, s, valid, identity):
  certificate(s, valid, identity, 0n)

law list_empty_of_laws_and_true:
  for -h: S.Situation
  S.All(S.NoneLaw{}, h)

def list_empty_of_laws_and_true(h):
  Unit{}
