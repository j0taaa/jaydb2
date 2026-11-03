# Regression: no fictitious prefix limit, without dispensing with actual finalization.
import Base
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../contract/Logic.bend as L
import ../../proof/Machine.bend as M
import ./Certificate.bend as T

def without_limit(h: S.Situation) -> Type:
  match h:
    case S.Closed{s, ctx, code, args, w, ts, S.Response{S.Limit{}, v}}:
      Empty
    case _:
      Unit

def configuration() -> S.Configuration:
  S.Configuration{D.Schema{Nil{}}, S.MoreOneLaw{without_limit, S.NoneLaw{}},
    S.Limits{1024n, 1024n, 64n}, "Bend-2.0.39-tests"}

def program() -> S.Program:
  S.Program{ctx => args => S.Refuse{D.VAbsent{}}}

def prefix(-s: D.State, -ctx: D.Context, -args: D.Value) ->
  R.SafetyPrefix(configuration(), s, ctx, "refusal", args, s, Nil{}):
  L.Both{L.Both{Unit{}, Unit{}}, L.Both{Unit{}, Unit{}}}

law certificate_universal_of_refusal_without_limit:
  for -ctx: D.Context
  for -args: D.Value
  R.Certifies(configuration(), "refusal", program(), ctx, args)
def certificate_universal_of_refusal_without_limit(ctx, args, s, valid, identity, n):
  match n:
    case 0n:
      prefix(s, ctx, args)
    case 1n+k:
      %Equal.sym(S.Trace,
        S.resume_execution_trace(k, S.Stopped{s, S.Response{S.Refusal{}, D.VAbsent{}}},
          S.schema(configuration()), Nil{}),
        S.Final{s, Nil{}, S.Response{S.Refusal{}, D.VAbsent{}}},
        M.reference_stopped(k, s, Nil{}, S.Response{S.Refusal{}, D.VAbsent{}}, S.schema(configuration()))) :
          R.SafetyTrace(_, configuration(), s, ctx, "refusal", args)
      L.Both{prefix(s, ctx, args), L.Both{L.Both{Unit{}, Unit{}}, Unit{}}}

# Configuration and authenticated domain are not impossible premises.
law configuration_is_valid:
  {R.configuration_is_valid(configuration()) == True{} : Bool}
def configuration_is_valid():
  {==}

# The certificate domain includes a valid state and authenticated context.
law initial_valid:
  R.Valid(configuration(), T.initial())
def initial_valid():
  L.Both{{==}, L.Both{Unit{}, Unit{}}}

law identity_authenticated:
  {D.authenticate(T.initial(), "second") == Some{T.context()} : Maybe<&2, D.Context>}
def identity_authenticated():
  {==}

law refusal_large_still_produces_limit:
  for -s: D.State
  {R.finalize(S.Response{S.Refusal{}, D.VText{String.repeat("x", 80n)}}, configuration(), s) ==
    S.response_error(S.Limit{}) : S.Response}
def refusal_large_still_produces_limit(s):
  {==}

law safety_final_negative_waives_limit_real:
  for -s: D.State
  for -ctx: D.Context
  for -args: D.Value
  for safe: R.SafetyFinal(configuration(), s, ctx, "refusal", args, s, Nil{},
    R.finalize(S.Response{S.Refusal{}, D.VText{String.repeat("x", 80n)}}, configuration(), s))
  Empty
def safety_final_negative_waives_limit_real(s, ctx, args, safe):
  L.and_left(Empty, Unit,
    L.and_left(S.Satisfies(configuration(), S.Closed{s, ctx, "refusal", args, s, Nil{},
      S.response_error(S.Limit{})}), Unit, safe))
