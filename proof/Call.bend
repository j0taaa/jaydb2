# Compose an authenticated call using actual Core functions.
# Assumes neither faithful preparation nor valid publication; does not assert host Contract.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/RequestFacts.bend as I
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Semantics.bend as S
import ../src/Core.bend as N
import ./Foundations.bend as F
import ./CodecSumsOrder.bend as O
import ./Machine.bend as M
import ./Preparation.bend as Q
import ./Publication.bend as U
import ./Safety.bend as G

def represented_cases(q: Maybe<&2, B.Number64>, -n: Nat,
  exact: {B.nat64(n) == q : Maybe<&2, B.Number64>},
  h: {P.representable_result(B.number64_bytes(q)) == True{} : Bool}) -> O.NumberRepresented<B.nat64(n)>:
  match q:
    case None{}:
      F.absurd_boolean(O.NumberRepresented<B.nat64(n)>, h)
    case Some{number}:
      O.Represented{number, exact}

def represented(+n: Nat, h: {P.representable_result(B.length64(n)) == True{} : Bool}) ->
  O.NumberRepresented<B.nat64(n)>:
  represented_cases(B.nat64(n), n, {==}, h)

def limit_represented(l: S.Limits, h: {R.limits_all_valid(l) == True{} : Bool}) ->
  O.NumberRepresented<B.nat64(R.limit_response(l))>:
  match l:
    case S.Limits{+msg, +est, +resp}:
      represented(resp, F.and_boolean_right(
        P.representable_result(B.length64(msg)) && P.representable_result(B.length64(est)),
        P.representable_result(B.length64(resp)),
        Q.prefix_limits_all_valid(S.Limits{msg, est, resp}, h)))

def frame_measured(+v: D.Value, +bs: List<&2, U32>,
  encoded: {P.encode(v) == Some{bs} : Maybe<&2, List<&2, U32>>},
  measure: O.NumberRepresented<B.nat64(B.length(bs))>) ->
  &bytes: List<&2, U32> -> P.Message(v, bytes):
  match measure:
    case O.Represented{B.Number64{+high, +low}, measured}:
      (B.concatenate(B.be64(high, low), bs),
        (%Equal.sym(Maybe<&2, List<&2, U32>>, P.encode(v), Some{bs}, encoded) : {P.frame_result(_) == Some{B.concatenate(B.be64(high, low), bs)} : Maybe<&2, List<&2, U32>>}
          %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bs)), Some{B.Number64{high, low}}, measured) : {P.concatenate_optional(B.number64_bytes(_), Some{bs}) ==
            Some{B.concatenate(B.be64(high, low), bs)} : Maybe<&2, List<&2, U32>>}
          {==}))

def frame_bounded(q: Maybe<&2, List<&2, U32>>, +v: D.Value, +limit: Nat,
  encoded: {P.encode(v) == q : Maybe<&2, List<&2, U32>>},
  ceiling: O.NumberRepresented<B.nat64(limit)>,
  fits: {R.fits_result(q, limit) == True{} : Bool}) ->
  &bytes: List<&2, U32> -> P.Message(v, bytes):
  match q:
    case None{}:
      F.absurd_boolean((&bytes: List<&2, U32> -> P.Message(v, bytes)), fits)
    case Some{+bs}:
      match ceiling:
        case O.Represented{number, measured}:
          frame_measured(v, bs, encoded,
            O.nat64_representability_closed_for_low(B.length(bs), limit, number, measured, fits))

law response_preparable_has_framing:
  for +v: D.Value
  for +l: S.Limits
  for valid: {R.limits_all_valid(l) == True{} : Bool}
  for fits: {R.fits(R.limit_response(l), v) == True{} : Bool}
  exs bytes: List<&2, U32>
  P.Message(v, bytes)
def response_preparable_has_framing(v, l, valid, fits):
  frame_bounded(P.encode(v), v, R.limit_response(l), {==}, limit_represented(l, valid), fits)

# Technical finalization does not inspect the law list. Equality preserves the actual target.
law finalize_independent_of_list_of_laws:
  for proposal: S.Response
  for -e: D.Schema
  for -laws: S.Laws
  for -lim: S.Limits
  for -amb: String
  for -w: D.State
  {R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w) ==
    R.finalize(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w) : S.Response}
def finalize_independent_of_list_of_laws(proposal, e, laws, lim, amb, w):
  match proposal:
    case S.Response{S.Success{}, v}: {==}
    case S.Response{S.Refusal{}, v}: {==}
    case S.Response{S.Input{}, v}: {==}
    case S.Response{S.Authentication{}, v}: {==}
    case S.Response{S.Certificate{}, v}: {==}
    case S.Response{S.DataError{}, v}: {==}
    case S.Response{S.Limit{}, v}: {==}
    case S.Response{S.Failure{}, v}: {==}

def prepare_framed(-c: S.Configuration, +w: D.State, +ts: List<&2, S.OperationEvent>, -proposal: S.Response,
  +r: S.Response, finalized: {R.finalize(proposal, c, w) == r : S.Response},
  message: &bytes: List<&2, U32> -> P.Message(S.response_value(r), bytes)) ->
  &prepared: N.Prepared -> {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{prepared} : Maybe<&2, N.Prepared>}:
  match message:
    case (bytes, framed):
      (N.Prepared{w, ts, r, bytes},
        Equal.trans(Maybe<&2, N.Prepared>, N.prepare(N.Stopped{w, ts, proposal}, c),
          N.prepare_response(r, w, ts), Some{N.Prepared{w, ts, r, bytes}},
          Equal.cong(S.Response, Maybe<&2, N.Prepared>, response => N.prepare_response(response, w, ts),
            R.finalize(proposal, c, w), r, finalized),
          Equal.cong(Maybe<&2, List<&2, U32>>, Maybe<&2, N.Prepared>,
            q => N.prepare_bytes(q, w, ts, r), P.frame(S.response_value(r)), Some{bytes}, framed)))

def prepare_configured(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  +is_valid: {R.configuration_is_valid(S.Configuration{e, laws, lim, amb}) == True{} : Bool}) ->
  &prepared: N.Prepared ->
    {N.prepare(N.Stopped{w, ts, proposal}, S.Configuration{e, laws, lim, amb}) == Some{prepared} : Maybe<&2, N.Prepared>}:
  +limits = Q.limits_of_configuration(S.Configuration{e, S.NoneLaw{}, lim, amb}, is_valid)
  +r = R.finalize(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w)
  F.combined_pair(
    (&prepared: N.Prepared -> {N.prepare(N.Stopped{w, ts, proposal}, S.Configuration{e, laws, lim, amb}) == Some{prepared} : Maybe<&2, N.Prepared>}),
    I.ErrorFixed(r), {R.fits(R.limit_response(lim), S.response_value(r)) == True{} : Bool},
    Q.finalize_guarantees_payload_and_size(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w, limits),
    payload => fits => prepare_framed(S.Configuration{e, laws, lim, amb}, w, ts, proposal, r,
      finalize_independent_of_list_of_laws(proposal, e, laws, lim, amb, w),
      response_preparable_has_framing(S.response_value(r), lim, limits, fits)))

law finalization_has_preparation_real:
  for c: S.Configuration
  for +w: D.State
  for +ts: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for +is_valid: {R.configuration_is_valid(c) == True{} : Bool}
  exs prepared: N.Prepared
  {N.prepare(N.Stopped{w, ts, proposal}, c) == Some{prepared} : Maybe<&2, N.Prepared>}
def finalization_has_preparation_real(c, w, ts, proposal, is_valid):
  match c:
    case S.Configuration{e, laws, lim, amb}:
      prepare_configured(e, laws, lim, amb, w, ts, proposal, is_valid)

# Uses copyable technical fields; the ACTUAL law list remains only in indices.
def preparation_configured_faithful(+e: D.Schema, -laws: S.Laws, +lim: S.Limits, +amb: String,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response, +prepared: N.Prepared,
  obtained: {N.prepare(N.Stopped{w, ts, proposal}, S.Configuration{e, laws, lim, amb}) == Some{prepared} : Maybe<&2, N.Prepared>}) ->
  Q.Faithful(w, ts, R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w), prepared):
  +r = R.finalize(proposal, S.Configuration{e, S.NoneLaw{}, lim, amb}, w)
  +equal = finalize_independent_of_list_of_laws(proposal, e, laws, lim, amb, w)
  %Equal.sym(S.Response, R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w), r, equal) :
    Q.Faithful(w, ts, _, prepared)
  Q.prepare_bytes_faithful(P.frame(S.response_value(r)), w, ts, r, prepared, {==},
    (%equal : {N.prepare_response(_, w, ts) == Some{prepared} : Maybe<&2, N.Prepared>} obtained))

def ConclusionIntegral(-c: S.Configuration, -s: D.State, -w: D.State,
  -ts: List<&2, S.OperationEvent>, -proposal: S.Response) -> Type:
  &prepared: N.Prepared ->
    L.E<{N.prepare(N.Stopped{w, ts, proposal}, c) == Some{prepared} : Maybe<&2, N.Prepared>},
      L.E<Q.Faithful(w, ts, R.finalize(proposal, c, w), prepared),
        R.Valid(c, U.published(N.conclude(prepared, s)))>>

def duplicate_equality(-A: Type, -x: A, -y: A, equality: {x == y : A}) ->
  L.E<{x == y : A}, {x == y : A}>:
  %equality : L.E<{x == _ : A}, {x == _ : A}>
  L.Both{{==}, {==}}

def conclude_configured(+e: D.Schema, laws: S.Laws, +lim: S.Limits, +amb: String,
  -code: String, p: S.Program, +ctx: D.Context, +args: D.Value,
  certificate: R.Certifies(S.Configuration{e, laws, lim, amb}, code, p, ctx, args),
  +s: D.State, valid: R.Valid(S.Configuration{e, laws, lim, amb}, s), cred: String,
  aut: {D.authenticate(s, cred) == Some{ctx} : Maybe<&2, D.Context>}, +n: Nat,
  +w: D.State, +ts: List<&2, S.OperationEvent>, +proposal: S.Response,
  obtained: {N.traverse(n, N.start(p, ctx, args, s), e) == S.Final{w, ts, proposal} : S.Trace},
  result: &prepared: N.Prepared ->
    {N.prepare(N.Stopped{w, ts, proposal}, S.Configuration{e, laws, lim, amb}) == Some{prepared} : Maybe<&2, N.Prepared>}) ->
  ConclusionIntegral(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal):
  match result:
    case (original, preparation_result):
      +prepared = (original : N.Prepared)
      F.combined_pair(ConclusionIntegral(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal),
        {N.prepare(N.Stopped{w, ts, proposal}, S.Configuration{e, laws, lim, amb}) == Some{prepared} : Maybe<&2, N.Prepared>},
        {N.prepare(N.Stopped{w, ts, proposal}, S.Configuration{e, laws, lim, amb}) == Some{prepared} : Maybe<&2, N.Prepared>},
        duplicate_equality(Maybe<&2, N.Prepared>,
          N.prepare(N.Stopped{w, ts, proposal}, S.Configuration{e, laws, lim, amb}), Some{prepared}, preparation_result),
        confirmed => stored =>
          F.combined_pair(ConclusionIntegral(S.Configuration{e, laws, lim, amb}, s, w, ts, proposal),
            {prepared == N.Prepared{w, ts, R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w), Q.bytes_prepared(prepared)} : N.Prepared},
            {P.frame(S.response_value(R.finalize(proposal, S.Configuration{e, laws, lim, amb}, w))) == Some{Q.bytes_prepared(prepared)} : Maybe<&2, List<&2, U32>>},
            preparation_configured_faithful(e, laws, lim, amb, w, ts, proposal, prepared, confirmed),
            +equal => +message =>
              (prepared, L.Both{stored, L.Both{L.Both{equal, message},
                U.conclusion_of_preparation_certified_and_is_valid(S.Configuration{e, laws, lim, amb}, code, p, ctx, args,
                  certificate, s, valid, cred, aut, n, w, ts, proposal, obtained, prepared, L.Both{equal, message})}})))

# Receives the actual function result, not faithfulness or validity of the conclusion.
# Machine.termination_of_reference_implies_termination_incremental supplies this path.
law call_authenticated_prepares_and_concludes:
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
  for +w: D.State
  for +ts: List<&2, S.OperationEvent>
  for +proposal: S.Response
  for obtained: {N.traverse(n, N.start(p, ctx, args, s), S.schema(c)) == S.Final{w, ts, proposal} : S.Trace}
  for is_valid: {R.configuration_is_valid(c) == True{} : Bool}
  ConclusionIntegral(c, s, w, ts, proposal)
def call_authenticated_prepares_and_concludes(c, code, p, ctx, args, certificate, s, valid, cred, aut,
  n, w, ts, proposal, obtained, is_valid):
  match c:
    case S.Configuration{+e, laws, +lim, +amb}:
      conclude_configured(e, laws, lim, amb, code, p, ctx, args, certificate, s, valid, cred, aut,
        n, w, ts, proposal, obtained, prepare_configured(e, laws, lim, amb, w, ts, proposal, is_valid))

law conclusion_without_success_preserves_state_initial:
  for prepared: N.Prepared
  for -s: D.State
  for without_success: {U.status_success(U.response(prepared)) == False{} : Bool}
  {U.published(N.conclude(prepared, s)) == s : D.State}
def conclusion_without_success_preserves_state_initial(prepared, s, without_success):
  match prepared:
    case N.Prepared{w, ts, r, bs}:
      U.all_status_without_success_preserves_published(r, s, w, without_success)
