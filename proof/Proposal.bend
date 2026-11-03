# Actual binary proposal: success is frameable when published state is valid.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ../src/Execution.bend as E
import ../src/Transport.bend as T
import ./Foundations.bend as F
import ./Preparation.bend as Q
import ./Call.bend as C
import ./CodecSumsOrder.bend as O

def state_represented(l: S.Limits, h: {R.limits_all_valid(l) == True{} : Bool}) ->
  O.NumberRepresented<B.nat64(R.limit_state(l))>:
  match l:
    case S.Limits{+msg, +est, +resp}:
      C.represented(est, F.and_boolean_right(P.representable_result(B.length64(msg)),
        P.representable_result(B.length64(est)),
        F.and_boolean_left(
          P.representable_result(B.length64(msg)) && P.representable_result(B.length64(est)),
          P.representable_result(B.length64(resp)),
          Q.prefix_limits_all_valid(S.Limits{msg, est, resp}, h))))

def join_measured(+bs: List<&2, U32>, +resp: List<&2, U32>,
  measure: O.NumberRepresented<B.nat64(B.length(bs))>) ->
  &packet: List<&2, U32> -> {T.join(bs, resp) == Some{packet} : Maybe<&2, List<&2, U32>>}:
  match measure:
    case O.Represented{B.Number64{+high, +low}, measured}:
      (B.concatenate(B.be64(high, low), B.concatenate(bs, resp)),
        (%Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bs)), Some{B.Number64{high, low}}, measured) :
          {T.join_combined_header(B.number64_bytes(_), bs, resp) ==
            Some{B.concatenate(B.be64(high, low), B.concatenate(bs, resp))} : Maybe<&2, List<&2, U32>>}
          {==}))

def Assembled(-q: Maybe<&2, List<&2, U32>>, -resp: List<&2, U32>) -> Type:
  &bs: List<&2, U32> -> &packet: List<&2, U32> ->
    L.E<{q == Some{bs} : Maybe<&2, List<&2, U32>>},
      L.E<{T.join(bs, resp) == Some{packet} : Maybe<&2, List<&2, U32>>},
        {E.state_encoded(q, resp) == E.FinishOutput{Con{1, packet}} : E.Iteration}>>

def success_combined_packet(+resp: List<&2, U32>, +bs: List<&2, U32>,
  result: &packet: List<&2, U32> -> {T.join(bs, resp) == Some{packet} : Maybe<&2, List<&2, U32>>}) ->
  Assembled(Some{bs}, resp):
  match result:
    case (+packet, together):
      F.combined_pair(Assembled(Some{bs}, resp),
        {T.join(bs, resp) == Some{packet} : Maybe<&2, List<&2, U32>>},
        {T.join(bs, resp) == Some{packet} : Maybe<&2, List<&2, U32>>},
        C.duplicate_equality(Maybe<&2, List<&2, U32>>, T.join(bs, resp), Some{packet}, together),
        exact => close => (bs, packet, L.Both{{==}, L.Both{exact,
          Equal.cong(Maybe<&2, List<&2, U32>>, E.Iteration, E.packet_ready,
            T.join(bs, resp), Some{packet}, close)}}))

def success_encoded(q: Maybe<&2, List<&2, U32>>, +resp: List<&2, U32>, +limit: Nat,
  ceiling: O.NumberRepresented<B.nat64(limit)>,
  fits: {R.fits_result(q, limit) == True{} : Bool}) -> Assembled(q, resp):
  match q:
    case None{}:
      F.absurd_boolean(Assembled(None{}, resp), fits)
    case Some{+bs}:
      match ceiling:
        case O.Represented{number, measured}:
          success_combined_packet(resp, bs,
            join_measured(bs, resp, O.nat64_representability_closed_for_low(
              B.length(bs), limit, number, measured, fits)))

law success_valid_has_proposal_real:
  for c: S.Configuration
  for +state: D.State
  for -value: D.Value
  for +resp: List<&2, U32>
  for configured: {R.configuration_is_valid(c) == True{} : Bool}
  for valid: R.Valid(c, state)
  exs bs: List<&2, U32>
  exs packet: List<&2, U32>
  L.E<{P.encode(D.state_value(state)) == Some{bs} : Maybe<&2, List<&2, U32>>},
    L.E<{T.join(bs, resp) == Some{packet} : Maybe<&2, List<&2, U32>>},
      {E.conclude(N.Conclusion{state, S.Response{S.Success{}, value}, resp}) == E.FinishOutput{Con{1, packet}} : E.Iteration}>>
def success_valid_has_proposal_real(c, state, value, resp, configured, valid):
  match c:
    case S.Configuration{+e, laws, +lim, amb}:
      structure = L.and_left({R.structure(S.Configuration{e, laws, lim, amb}, state) == True{} : Bool},
        S.Satisfies(S.Configuration{e, laws, lim, amb}, S.Stable{state}), valid)
      success_encoded(P.encode(D.state_value(state)), resp, R.limit_state(lim),
        state_represented(lim, Q.limits_of_configuration(S.Configuration{e, S.NoneLaw{}, lim, amb}, configured)),
        F.and_boolean_right(D.structure(e, state), R.fits(R.limit_state(lim), D.state_value(state)), structure))

law without_success_negative_sends_state:
  for -state: D.State
  for r: S.Response
  for -resp: List<&2, U32>
  for without_success: {S.is_success(status(r)) == False{} : Bool}
  {E.conclude(N.Conclusion{state, r, resp}) == E.FinishOutput{Con{0, resp}} : E.Iteration}

def status(r: S.Response) -> S.Status:
  S.Response{s, v} = r
  s

def without_success_negative_sends_state(state, r, resp, without_success):
  match r:
    case S.Response{S.Success{}, v}:
      F.absurd_boolean({E.conclude(N.Conclusion{state, S.Response{S.Success{}, v}, resp}) ==
        E.FinishOutput{Con{0, resp}} : E.Iteration}, Equal.sym(Bool, True{}, False{}, without_success))
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}
