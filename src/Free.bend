# General proof for configurations explicitly installing zero laws.
# Not an implicit policy: other configurations require their certificates.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ./ValidationFinal.bend as V

def configuration(e: D.Schema, l: S.Limits, environment: String) -> S.Configuration:
  S.Configuration{e, S.NoneLaw{}, l, environment}

# Existing interfaces delegate to shared technical validation.
def conjunction(-a: Bool, -b: Bool, exists: {a == True{} : Bool}, hb: {b == True{} : Bool}) ->
  {a && b == True{} : Bool}:
  V.conjunction(a, b, exists, hb)

def valid(-e: D.Schema, -l: S.Limits, -amb: String, -w: D.State,
  he: {D.structure(e, w) == True{} : Bool},
  ht: {R.fits(R.limit_state(l), D.state_value(w)) == True{} : Bool}) ->
  R.Valid(configuration(e, l, amb), w):
  V.valid(e, S.NoneLaw{}, l, amb, w, he, ht, Unit{})

def response_validated(ok: Bool, fits: Bool, -e: D.Schema, -l: S.Limits,
  -amb: String, -w: D.State, -v: D.Value, h: R.Valid(configuration(e, l, amb), w)) ->
  R.PublicationValid(R.response_technique_cases(ok, fits, S.Response{S.Success{}, v}), configuration(e, l, amb), w):
  V.response_validated(ok, fits, configuration(e, l, amb), w, v, h)

def state_validated(ok: Bool, fits: Bool, -e: D.Schema, -l: S.Limits,
  -amb: String, -w: D.State, -v: D.Value, payload: Bool, size: Bool,
  he: {D.structure(e, w) == ok : Bool},
  ht: {R.fits(R.limit_state(l), D.state_value(w)) == fits : Bool}) ->
  R.PublicationValid(R.state_technical_cases(ok, fits,
    R.response_technique_cases(payload, size, S.Response{S.Success{}, v})), configuration(e, l, amb), w):
  V.state_validated(ok, fits, e, S.NoneLaw{}, l, amb, w, v, payload, size, he, ht, Unit{})

def refusal_validated(ok: Bool, fits: Bool, -c: S.Configuration, -w: D.State, -v: D.Value) ->
  R.PublicationValid(R.response_technique_cases(ok, fits, S.Response{S.Refusal{}, v}), c, w):
  V.refusal_validated(ok, fits, c, w, v)

law final_technical_publish_only_state_valid:
  for r: S.Response
  for +e: D.Schema
  for +l: S.Limits
  for +amb: String
  for +w: D.State
  R.PublicationValid(R.finalize(r, configuration(e, l, amb), w), configuration(e, l, amb), w)
def final_technical_publish_only_state_valid(r, e, l, amb, w):
  V.finalize_preserves_laws_stable(r, configuration(e, l, amb), w, s => Unit{})

def prefix(-e: D.Schema, -l: S.Limits, -amb: String,
  -s: D.State, -ctx: D.Context, -code: String, -args: D.Value,
  -w: D.State, -ts: List<&2, S.OperationEvent>) ->
  R.SafetyPrefix(configuration(e, l, amb), s, ctx, code, args, w, ts):
  L.Both{Unit{}, Unit{}}

law execution_trace_free_covers_prefixes_and_final:
  for execution_trace: S.Trace
  for +e: D.Schema
  for +l: S.Limits
  for +amb: String
  for -s: D.State
  for -ctx: D.Context
  for -code: String
  for -args: D.Value
  R.SafetyTrace(execution_trace, configuration(e, l, amb), s, ctx, code, args)
def execution_trace_free_covers_prefixes_and_final(execution_trace, e, l, amb, s, ctx, code, args):
  match execution_trace:
    case S.Prefix{w, ts}:
      prefix(e, l, amb, s, ctx, code, args, w, ts)
    case S.Final{+w, ts, r}:
      L.Both{prefix(e, l, amb, s, ctx, code, args, w, ts),
        L.Both{Unit{}, final_technical_publish_only_state_valid(r, e, l, amb, w)}}
