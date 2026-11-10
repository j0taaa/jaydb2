# Actual complete preparation: payload, size and bytes, before publication.
import Base
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Protocol.bend as P
import ../contract/RequestFacts.bend as I
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../src/Core.bend as N
import ./Foundations.bend as F

def Preparable(-l: S.Limits, -r: S.Response) -> Type:
  L.E<I.ErrorFixed(r),
    {R.fits(R.limit_response(l), S.response_value(r)) == True{} : Bool}>

def Error(s: S.Status) -> Type:
  match s:
    case S.Success{}:
      Empty
    case S.Refusal{}:
      Empty
    case _:
      Unit

def prefix_limits(+msg: Nat, +est: Nat, resp: Nat) -> Bool:
  P.representable_result(B.length64(msg)) &&
    P.representable_result(B.length64(est)) &&
    P.representable_result(B.length64(resp))

# The three representable ceilings are the common prefix of limits_all_valid.
# Removes only the six additional fixed-error conditions.
def prefix_limits_all_valid(l: S.Limits, h: {R.limits_all_valid(l) == True{} : Bool}) ->
  {prefix_limits(R.limit_message(l), R.limit_state(l), R.limit_response(l)) == True{} : Bool}:
  match l:
    case S.Limits{+msg, +est, +resp}:
      +a = R.fits_error(resp, S.Input{})
      +b = R.fits_error(resp, S.Authentication{})
      +c = R.fits_error(resp, S.Certificate{})
      +d = R.fits_error(resp, S.DataError{})
      +e = R.fits_error(resp, S.Limit{})
      +f = R.fits_error(resp, S.Failure{})
      +prefix = prefix_limits(msg, est, resp)
      h5 = F.and_boolean_left(prefix && a && b && c && d && e, f, h)
      h4 = F.and_boolean_left(prefix && a && b && c && d, e, h5)
      h3 = F.and_boolean_left(prefix && a && b && c, d, h4)
      h2 = F.and_boolean_left(prefix && a && b, c, h3)
      h1 = F.and_boolean_left(prefix && a, b, h2)
      F.and_boolean_left(prefix, a, h1)

def Six(-a: Bool, -b: Bool, -c: Bool, -d: Bool, -e: Bool, -f: Bool) -> Type:
  L.E<{a == True{} : Bool}, L.E<{b == True{} : Bool}, L.E<{c == True{} : Bool},
    L.E<{d == True{} : Bool}, L.E<{e == True{} : Bool}, {f == True{} : Bool}>>>>>

def six_last(+rest: Bool, +a: Bool, +b: Bool, +c: Bool, +d: Bool,
  +e: Bool, -f: Bool, +h: {rest && a && b && c && d && e && f == True{} : Bool}) ->
  Six(a, b, c, d, e, f):
  +h5 = F.and_boolean_left(rest && a && b && c && d && e, f, h)
  +h4 = F.and_boolean_left(rest && a && b && c && d, e, h5)
  +h3 = F.and_boolean_left(rest && a && b && c, d, h4)
  +h2 = F.and_boolean_left(rest && a && b, c, h3)
  h1 = F.and_boolean_left(rest && a, b, h2)
  L.Both{F.and_boolean_right(rest, a, h1),
    L.Both{F.and_boolean_right(rest && a, b, h2),
      L.Both{F.and_boolean_right(rest && a && b, c, h3),
        L.Both{F.and_boolean_right(rest && a && b && c, d, h4),
          L.Both{F.and_boolean_right(rest && a && b && c && d, e, h5),
            F.and_boolean_right(rest && a && b && c && d && e, f, h)}}}}}

def six_errors(+l: S.Limits, h: {R.limits_all_valid(l) == True{} : Bool}) ->
  Six(R.fits_error(R.limit_response(l), S.Input{}),
    R.fits_error(R.limit_response(l), S.Authentication{}),
    R.fits_error(R.limit_response(l), S.Certificate{}),
    R.fits_error(R.limit_response(l), S.DataError{}),
    R.fits_error(R.limit_response(l), S.Limit{}),
    R.fits_error(R.limit_response(l), S.Failure{})):
  match l:
    case S.Limits{msg, est, +resp}:
      six_last(prefix_limits(msg, est, resp),
        R.fits_error(resp, S.Input{}), R.fits_error(resp, S.Authentication{}),
        R.fits_error(resp, S.Certificate{}), R.fits_error(resp, S.DataError{}),
        R.fits_error(resp, S.Limit{}), R.fits_error(resp, S.Failure{}), h)

def ErrorSelected(s: S.Status, -a: Bool, -b: Bool, -c: Bool,
  -d: Bool, -e: Bool, -f: Bool) -> Type:
  match s:
    case S.Input{}:
      {a == True{} : Bool}
    case S.Authentication{}:
      {b == True{} : Bool}
    case S.Certificate{}:
      {c == True{} : Bool}
    case S.DataError{}:
      {d == True{} : Bool}
    case S.Limit{}:
      {e == True{} : Bool}
    case S.Failure{}:
      {f == True{} : Bool}
    case _:
      Empty

def select_error_proofs(s: S.Status, -a: Bool, -b: Bool, -c: Bool,
  -d: Bool, -e: Bool, -f: Bool, pa: {a == True{} : Bool}, pb: {b == True{} : Bool},
  pc: {c == True{} : Bool}, pd: {d == True{} : Bool}, pe: {e == True{} : Bool},
  pf: {f == True{} : Bool}, error: Error(s)) -> ErrorSelected(s, a, b, c, d, e, f):
  match s:
    case S.Success{}:
      match error:
    case S.Refusal{}:
      match error:
    case S.Input{}:
      pa
    case S.Authentication{}:
      pb
    case S.Certificate{}:
      pc
    case S.DataError{}:
      pd
    case S.Limit{}:
      pe
    case S.Failure{}:
      pf

def select_error(s: S.Status, -a: Bool, -b: Bool, -c: Bool,
  -d: Bool, -e: Bool, -f: Bool, h: Six(a, b, c, d, e, f), error: Error(s)) ->
  ErrorSelected(s, a, b, c, d, e, f):
  match h:
    case L.Both{pa, L.Both{pb, L.Both{pc, L.Both{pd, L.Both{pe, pf}}}}}:
      select_error_proofs(s, a, b, c, d, e, f, pa, pb, pc, pd, pe, pf, error)

def errors_fit_selected(s: S.Status, -l: S.Limits,
  h: Six(R.fits_error(R.limit_response(l), S.Input{}),
    R.fits_error(R.limit_response(l), S.Authentication{}),
    R.fits_error(R.limit_response(l), S.Certificate{}),
    R.fits_error(R.limit_response(l), S.DataError{}),
    R.fits_error(R.limit_response(l), S.Limit{}),
    R.fits_error(R.limit_response(l), S.Failure{})), error: Error(s)) ->
  {R.fits_error(R.limit_response(l), s) == True{} : Bool}:
  match s h:
    case S.Input{} L.Both{input, rest}: input
    case S.Authentication{} L.Both{input, L.Both{authentication, rest}}: authentication
    case S.Certificate{} L.Both{input, L.Both{authentication, L.Both{certificate, rest}}}: certificate
    case S.DataError{} L.Both{input, L.Both{authentication, L.Both{certificate, L.Both{data, rest}}}}: data
    case S.Limit{} L.Both{input, L.Both{authentication, L.Both{certificate, L.Both{data, L.Both{limit, failure}}}}}: limit
    case S.Failure{} L.Both{input, L.Both{authentication, L.Both{certificate, L.Both{data, L.Both{limit, failure}}}}}: failure
    case S.Success{} _:
      match error:
    case S.Refusal{} _:
      match error:

law errors_fixed_fit:
  for s: S.Status
  for +l: S.Limits
  for h: {R.limits_all_valid(l) == True{} : Bool}
  for error: Error(s)
  {R.fits_error(R.limit_response(l), s) == True{} : Bool}
def errors_fixed_fit(s, l, h, error):
  errors_fit_selected(s, l, six_errors(l, h), error)

def error_payload(s: S.Status) -> I.ErrorFixed(S.response_error(s)):
  match s:
    case S.Success{}:
      {==}
    case S.Refusal{}:
      {==}
    case S.Input{}:
      {==}
    case S.Authentication{}:
      {==}
    case S.Certificate{}:
      {==}
    case S.DataError{}:
      {==}
    case S.Limit{}:
      {==}
    case S.Failure{}:
      {==}

def error_preparable(+s: S.Status, +l: S.Limits,
  h: {R.limits_all_valid(l) == True{} : Bool}, error: Error(s)) ->
  Preparable(l, S.response_error(s)):
  L.Both{error_payload(s), errors_fixed_fit(s, l, h, error)}

def response_technique_correct(ok: Bool, fits: Bool, -r: S.Response, -l: S.Limits,
  value: {ok == True{} : Bool} -> I.ErrorFixed(r),
  size: {R.fits(R.limit_response(l), S.response_value(r)) == fits : Bool},
  data: Preparable(l, S.response_error(S.DataError{})),
  limit: Preparable(l, S.response_error(S.Limit{}))) ->
  Preparable(l, R.response_technique_cases(ok, fits, r)):
  match ok fits:
    case False{} _:
      data
    case True{} False{}:
      limit
    case True{} True{}:
      L.Both{value({==}), size}

def state_technical_correct(ok: Bool, fits: Bool, -r: S.Response, -l: S.Limits,
  response: Preparable(l, r), data: Preparable(l, S.response_error(S.DataError{})),
  limit: Preparable(l, S.response_error(S.Limit{}))) ->
  Preparable(l, R.state_technical_cases(ok, fits, r)):
  match ok fits:
    case False{} _:
      data
    case True{} False{}:
      limit
    case True{} True{}:
      response

def limits_of_configuration(c: S.Configuration,
  h: {R.configuration_is_valid(c) == True{} : Bool}) ->
  {R.limits_all_valid(S.limits(c)) == True{} : Bool}:
  match c:
    case S.Configuration{+e, laws, +lim, amb}:
      F.and_boolean_right(D.schema_valid(e), R.limits_all_valid(lim),
        F.and_boolean_left(D.schema_valid(e) && R.limits_all_valid(lim),
          D.unicode_valid(amb), h))

law finalize_guarantees_payload_and_size:
  for proposal: S.Response
  for c: S.Configuration
  for +w: D.State
  for +h: {R.limits_all_valid(S.limits(c)) == True{} : Bool}
  Preparable(S.limits(c), R.finalize(proposal, c, w))
def finalize_guarantees_payload_and_size(proposal, c, w, h):
  match proposal c:
    case S.Response{S.Success{}, +v} S.Configuration{e, laws, +lim, amb}:
      state_technical_correct(D.structure(e, w), R.fits(R.limit_state(lim), D.state_value(w)),
        R.response_technique_cases(D.value_valid(v),
          R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})),
          S.Response{S.Success{}, v}), lim,
        response_technique_correct(D.value_valid(v),
          R.fits(R.limit_response(lim), S.response_value(S.Response{S.Success{}, v})),
          S.Response{S.Success{}, v}, lim, value => value, {==},
          error_preparable(S.DataError{}, lim, h, Unit{}), error_preparable(S.Limit{}, lim, h, Unit{})),
        error_preparable(S.DataError{}, lim, h, Unit{}), error_preparable(S.Limit{}, lim, h, Unit{}))
    case S.Response{S.Refusal{}, +v} S.Configuration{e, laws, +lim, amb}:
      response_technique_correct(D.value_valid(v),
        R.fits(R.limit_response(lim), S.response_value(S.Response{S.Refusal{}, v})),
        S.Response{S.Refusal{}, v}, lim, value => value, {==},
        error_preparable(S.DataError{}, lim, h, Unit{}), error_preparable(S.Limit{}, lim, h, Unit{}))
    case S.Response{S.Input{}, v} S.Configuration{e, laws, lim, amb}:
      error_preparable(S.Input{}, lim, h, Unit{})
    case S.Response{S.Authentication{}, v} S.Configuration{e, laws, lim, amb}:
      error_preparable(S.Authentication{}, lim, h, Unit{})
    case S.Response{S.Certificate{}, v} S.Configuration{e, laws, lim, amb}:
      error_preparable(S.Certificate{}, lim, h, Unit{})
    case S.Response{S.DataError{}, v} S.Configuration{e, laws, lim, amb}:
      error_preparable(S.DataError{}, lim, h, Unit{})
    case S.Response{S.Limit{}, v} S.Configuration{e, laws, lim, amb}:
      error_preparable(S.Limit{}, lim, h, Unit{})
    case S.Response{S.Failure{}, v} S.Configuration{e, laws, lim, amb}:
      error_preparable(S.Failure{}, lim, h, Unit{})

def bytes_prepared(p: N.Prepared) -> List<&2, U32>:
  N.Prepared{w, ts, r, bs} = p
  bs

def Faithful(-w: D.State, -ts: List<&2, S.OperationEvent>, -r: S.Response,
  -prepared: N.Prepared) -> Type:
  L.E<{prepared == N.Prepared{w, ts, r, bytes_prepared(prepared)} : N.Prepared},
    P.Message(S.response_value(r), bytes_prepared(prepared))>

def prepare_bytes_faithful(q: Maybe<&2, List<&2, U32>>, +w: D.State,
  +ts: List<&2, S.OperationEvent>, +r: S.Response, +prepared: N.Prepared,
  framed: {P.frame(S.response_value(r)) == q : Maybe<&2, List<&2, U32>>},
  obtained: {N.prepare_bytes(q, w, ts, r) == Some{prepared} : Maybe<&2, N.Prepared>}) ->
  Faithful(w, ts, r, prepared):
  match q:
    case None{}:
      L.ex_false(Faithful(w, ts, r, prepared), F.none_negative_some(N.Prepared, prepared, obtained))
    case Some{bs}:
      %F.some_injective(N.Prepared, N.Prepared{w, ts, r, bs}, prepared, obtained) : Faithful(w, ts, r, _)
      L.Both{{==}, framed}

def PreparationFaithful(m: N.Machine, -c: S.Configuration, -prepared: N.Prepared) -> Type:
  match m:
    case N.Running{w, a, ts}:
      Empty
    case N.Stopped{w, ts, proposal}:
      Faithful(w, ts, R.finalize(proposal, c, w), prepared)

law prepare_preserves_response_state_events_and_bytes:
  for m: N.Machine
  for c: S.Configuration
  for +prepared: N.Prepared
  for obtained: {N.prepare(m, c) == Some{prepared} : Maybe<&2, N.Prepared>}
  PreparationFaithful(m, c, prepared)
def prepare_preserves_response_state_events_and_bytes(m, c, prepared, obtained):
  match m:
    case N.Running{w, a, ts}:
      F.none_negative_some(N.Prepared, prepared, obtained)
    case N.Stopped{+w, ts, proposal}:
      +r = R.finalize(proposal, c, w)
      prepare_bytes_faithful(P.frame(S.response_value(r)), w, ts, r, prepared, {==}, obtained)

law machine_in_progress_negative_can_prepare:
  for -w: D.State
  for -a: S.Action
  for -ts: List<&2, S.OperationEvent>
  for -c: S.Configuration
  {N.prepare(N.Running{w, a, ts}, c) == None{} : Maybe<&2, N.Prepared>}
def machine_in_progress_negative_can_prepare(w, a, ts, c):
  {==}

law bytes_impossible_negative_create_preparation:
  for -w: D.State
  for -ts: List<&2, S.OperationEvent>
  for -r: S.Response
  {N.prepare_bytes(None{}, w, ts, r) == None{} : Maybe<&2, N.Prepared>}
def bytes_impossible_negative_create_preparation(w, ts, r):
  {==}

law conclude_preserves_entirely_bytes_and_response:
  for -w: D.State
  for -ts: List<&2, S.OperationEvent>
  for -r: S.Response
  for -bs: List<&2, U32>
  for -s: D.State
  {N.conclude(N.Prepared{w, ts, r, bs}, s) ==
    N.Conclusion{S.publish(r, s, w), r, bs} : N.Conclusion}
def conclude_preserves_entirely_bytes_and_response(w, ts, r, bs, s):
  {==}
