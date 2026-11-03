# Technical publication conditions, independent of installed access laws.
# Proof of every law in the Stable phase is supplied, never assumed.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L

def conjunction(-a: Bool, -b: Bool, exists: {a == True{} : Bool},
  hb: {b == True{} : Bool}) -> {a && b == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, exists) : {_ && b == True{} : Bool}
  hb

def valid(-e: D.Schema, -laws: S.Laws, -l: S.Limits, -amb: String,
  -w: D.State, he: {D.structure(e, w) == True{} : Bool},
  ht: {R.fits(R.limit_state(l), D.state_value(w)) == True{} : Bool},
  stable: S.All(laws, S.Stable{w})) ->
  R.Valid(S.Configuration{e, laws, l, amb}, w):
  L.Both{conjunction(D.structure(e, w), R.fits(R.limit_state(l), D.state_value(w)), he, ht), stable}

def response_validated(ok: Bool, fits: Bool, -c: S.Configuration, -w: D.State,
  -v: D.Value, h: R.Valid(c, w)) ->
  R.PublicationValid(R.response_technique_cases(ok, fits, S.Response{S.Success{}, v}), c, w):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: h

def state_validated(ok: Bool, fits: Bool, -e: D.Schema, -laws: S.Laws,
  -l: S.Limits, -amb: String, -w: D.State, -v: D.Value,
  payload: Bool, size: Bool,
  he: {D.structure(e, w) == ok : Bool},
  ht: {R.fits(R.limit_state(l), D.state_value(w)) == fits : Bool},
  stable: S.All(laws, S.Stable{w})) ->
  R.PublicationValid(R.state_technical_cases(ok, fits,
    R.response_technique_cases(payload, size, S.Response{S.Success{}, v})),
    S.Configuration{e, laws, l, amb}, w):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}:
      response_validated(payload, size, S.Configuration{e, laws, l, amb}, w, v,
        valid(e, laws, l, amb, w, he, ht, stable))

def refusal_validated(ok: Bool, fits: Bool, -c: S.Configuration, -w: D.State,
  -v: D.Value) -> R.PublicationValid(R.response_technique_cases(ok, fits,
    S.Response{S.Refusal{}, v}), c, w):
  match ok fits:
    case False{} _: Unit{}
    case True{} False{}: Unit{}
    case True{} True{}: Unit{}

law finalize_preserves_laws_stable:
  for r: S.Response
  for c: S.Configuration
  for +w: D.State
  for stable: @s: D.State -> S.Satisfies(c, S.Stable{s})
  R.PublicationValid(R.finalize(r, c, w), c, w)
def finalize_preserves_laws_stable(r, c, w, stable):
  match r c:
    case S.Response{S.Success{}, +v} S.Configuration{e, laws, +l, amb}:
      state_validated(D.structure(e, w), R.fits(R.limit_state(l), D.state_value(w)),
        e, laws, l, amb, w, v, D.value_valid(v),
        R.fits(R.limit_response(l), S.response_value(S.Response{S.Success{}, v})),
        {==}, {==}, stable(w))
    case S.Response{S.Refusal{}, +v} S.Configuration{e, laws, l, amb}:
      refusal_validated(D.value_valid(v),
        R.fits(R.limit_response(l), S.response_value(S.Response{S.Refusal{}, v})), S.Configuration{e, laws, l, amb}, w, v)
    case S.Response{S.Input{}, v} S.Configuration{e, laws, l, amb}:
      Unit{}
    case S.Response{S.Authentication{}, v} S.Configuration{e, laws, l, amb}:
      Unit{}
    case S.Response{S.Certificate{}, v} S.Configuration{e, laws, l, amb}:
      Unit{}
    case S.Response{S.DataError{}, v} S.Configuration{e, laws, l, amb}:
      Unit{}
    case S.Response{S.Limit{}, v} S.Configuration{e, laws, l, amb}:
      Unit{}
    case S.Response{S.Failure{}, v} S.Configuration{e, laws, l, amb}:
      Unit{}
