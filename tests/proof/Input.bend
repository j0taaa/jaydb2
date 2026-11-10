# Universal reapplications and concrete samples of ACTUAL adapters.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../contract/Semantics.bend as S
import ../../contract/Requirements.bend as R
import ../../contract/RequestFacts.bend as I
import ../../contract/Logic.bend as L
import ../../src/Codec.bend as C
import ../../src/Input.bend as E
import ../../src/Transport.bend as T
import ../../proof/Input.bend as G
import ../../proof/CodecMinimum.bend as M

# Fallbacks are only fixture functions. Every use in the general theorem
# below separately proves encoding, measure and assembly by equality.
def list_or_empty(result: Maybe<&2, List<&2, U32>>) -> List<&2, U32>:
  match result:
    case None{}:
      Nil{}
    case Some{bs}:
      bs

def bytes(v: D.Value) -> List<&2, U32>:
  list_or_empty(P.encode(v))

def number_or_zero(result: Maybe<&2, B.Number64>) -> B.Number64:
  match result:
    case None{}:
      B.Number64{0, 0}
    case Some{n}:
      n

def number(bs: List<&2, U32>) -> B.Number64:
  number_or_zero(B.nat64(B.length(bs)))

def packet(be: List<&2, U32>, br: List<&2, U32>) -> List<&2, U32>:
  list_or_empty(T.join(be, br))

def user(+id: String, cred: String) -> D.Row:
  D.Row{id, [D.Field{"credential", D.VText{cred}}, D.Field{"id", D.VText{id}},
    D.Field{"kind", D.VText{"person"}}]}

def schema() -> D.Schema:
  D.Schema{Nil{}}

def published() -> D.State:
  D.State{Nil{}, [user("a", "first"), user("é", "second")]}

def arguments() -> D.Value:
  D.VList{D.VInt{2147483648, 0}, D.VList{D.VInt{2147483647, 4294967295},
    D.VList{D.VAbsent{}, D.VList{D.VText{"é\n𝄞"}, D.VListEmpty{}}}}}

def request() -> P.Request:
  P.Request{"second", "exact source\n𝄞", arguments(), "π\n\\proof"}

def state_bytes() -> List<&2, U32>:
  bytes(D.state_value(published()))

def message_bytes() -> List<&2, U32>:
  bytes(P.request_value(request()))

def assembled() -> List<&2, U32>:
  packet(state_bytes(), message_bytes())

def limits() -> S.Limits:
  S.Limits{B.length(message_bytes()), B.length(state_bytes()), 0n}

def limit_message_zero() -> S.Limits:
  S.Limits{0n, B.length(state_bytes()), 0n}

law ready_exact_in_two_limits_inclusive:
  {E.decode(assembled(), schema(), limits()) == E.InputReady{published(), request()} : E.PreAuthentication}
def ready_exact_in_two_limits_inclusive():
  G.bytes_canonical_assembled_produce_ready_exact(schema(), published(), request(), limits(),
    state_bytes(), message_bytes(), assembled(), number(state_bytes()), number(message_bytes()),
    number(state_bytes()), number(message_bytes()), {==}, {==}, {==}, {==}, {==}, {==}, {==},
    M.less_equal64_reflexive(number(state_bytes())), M.less_equal64_reflexive(number(message_bytes())), {==})

law authentication_in_end_of_registry_combined_unicode_and_bits_exact:
  {E.analyze(assembled(), schema(), limits()) ==
    E.Received{published(), request(), D.Context{"é", "person"}} : E.Analysis}
def authentication_in_end_of_registry_combined_unicode_and_bits_exact():
  G.analyze_accepts_exactly_context_authenticated(assembled(), schema(), limits(), published(),
    request(), D.Context{"é", "person"}, ready_exact_in_two_limits_inclusive(), {==})

law working_combined_empty_and_duplicates_negative_changes_semantics_original:
  {E.authenticate(Some{P.Request{"", "code", D.VAbsent{}, "proof"}},
    D.State{Nil{}, [user("a", ""), user("b", "")]}) ==
    E.Received{D.State{Nil{}, [user("a", ""), user("b", "")]},
      P.Request{"", "code", D.VAbsent{}, "proof"}, D.Context{"a", "person"}} : E.Analysis}
def working_combined_empty_and_duplicates_negative_changes_semantics_original():
  G.authenticate_preserves_exactly_state_request_and_context(
    D.State{Nil{}, [user("a", ""), user("b", "")]}, P.Request{"", "code", D.VAbsent{}, "proof"})

law state_published_combined_credential_empty_and_refused:
  {E.analyze(packet(state_bytes(), bytes(P.request_value(P.Request{"", "c", D.VAbsent{}, "p"}))),
    schema(), limits()) == E.Rejected{S.Authentication{}} : E.Analysis}
def state_published_combined_credential_empty_and_refused():
  {==}

law credential_unknown_and_refused_after_envelope:
  {E.analyze(packet(state_bytes(), bytes(P.request_value(P.Request{"other", "c", D.VAbsent{}, "p"}))),
    schema(), limits()) == E.Rejected{S.Authentication{}} : E.Analysis}
def credential_unknown_and_refused_after_envelope():
  {==}

law header_private_incomplete_negative_and_error_client:
  {E.analyze([0, 0, 0, 0, 0, 0, 0], schema(), limits()) == E.TransportInvalid{} : E.Analysis}
def header_private_incomplete_negative_and_error_client():
  {==}

law state_invalid_precedes_envelope_valid:
  {E.analyze(packet([0], message_bytes()), schema(), limits()) == E.TransportInvalid{} : E.Analysis}
def state_invalid_precedes_envelope_valid():
  {==}

law codec_of_state_invalid_negative_and_error_client:
  {E.analyze(packet([255], message_bytes()), schema(), limits()) == E.TransportInvalid{} : E.Analysis}
def codec_of_state_invalid_negative_and_error_client():
  {==}

law value_canonical_outside_of_envelope_produces_input:
  {E.analyze(packet(state_bytes(), [0]), schema(), limits()) == E.Rejected{S.Input{}} : E.Analysis}
def value_canonical_outside_of_envelope_produces_input():
  {==}

law suffix_extra_in_message_produces_input:
  {E.analyze(packet(state_bytes(), [0, 0]), schema(), limits()) == E.Rejected{S.Input{}} : E.Analysis}
def suffix_extra_in_message_produces_input():
  {==}

law message_above_of_ceiling_negative_becomes_authentication:
  {E.analyze(assembled(), schema(), limit_message_zero()) == E.Rejected{S.Limit{}} : E.Analysis}
def message_above_of_ceiling_negative_becomes_authentication():
  {==}

law state_above_of_ceiling_and_error_transport:
  {E.analyze(assembled(), schema(), S.Limits{1000n, 0n, 0n}) ==
    E.TransportInvalid{} : E.Analysis}
def state_above_of_ceiling_and_error_transport():
  {==}

law all_state_and_request_canonical_reapply_composition:
  for +e: D.Schema
  for +s: D.State
  for +r: P.Request
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for cod_and: P.Encoding(D.state_value(s), be)
  for cod_r: P.Encoding(P.request_value(r), br)
  for assembly: {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for structure: {D.structure(e, s) == True{} : Bool}
  {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
def all_state_and_request_canonical_reapply_composition(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure):
  G.bytes_canonical_assembled_produce_ready_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure)

law all_packet_canonical_reapplies_analysis_exact:
  for +e: D.Schema
  for +s: D.State
  for +r: P.Request
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for cod_and: P.Encoding(D.state_value(s), be)
  for cod_r: P.Encoding(P.request_value(r), br)
  for assembly: {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for structure: {D.structure(e, s) == True{} : Bool}
  L.E<{E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication},
    {E.analyze(bs, e, l) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}>
def all_packet_canonical_reapplies_analysis_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure):
  G.bytes_canonical_assembled_are_analyzed_combined_identity_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
  cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure)

law existence_of_packet_without_assume_assembly:
  for +e: D.Schema
  for +s: D.State
  for +r: P.Request
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for cod_and: P.Encoding(D.state_value(s), be)
  for cod_r: P.Encoding(P.request_value(r), br)
  for +measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for structure: {D.structure(e, s) == True{} : Bool}
  G.PacketReady(e, s, r, l, be, br)
def existence_of_packet_without_assume_assembly(e, s, r, l, be, br, ce, cr, te, tr,
  cod_and, cod_r, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure):
  G.all_input_canonical_admissible_has_packet_ready_and_analysis_exact(e, s, r, l, be, br, ce, cr, te, tr,
  cod_and, cod_r, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure)

law reapply_authenticate_preserves_exactly_state_request_and_context:
  for +s: D.State
  for r: P.Request
  {E.authenticate(Some{r}, s) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}
def reapply_authenticate_preserves_exactly_state_request_and_context(s, r):
  G.authenticate_preserves_exactly_state_request_and_context(s, r)

law reapply_analyze_ready_and_authentication_stable_exact:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  {E.analyze(bs, e, l) == E.identity(D.authenticate(s, I.credential(r)), s, r) : E.Analysis}
def reapply_analyze_ready_and_authentication_stable_exact(bs, e, l, s, r, ready):
  G.analyze_ready_and_authentication_stable_exact(bs, e, l, s, r, ready)

law reapply_analyze_accepts_exactly_context_authenticated:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for +ctx: D.Context
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  for aut: {D.authenticate(s, I.credential(r)) == Some{ctx} : Maybe<&2, D.Context>}
  {E.analyze(bs, e, l) == E.Received{s, r, ctx} : E.Analysis}
def reapply_analyze_accepts_exactly_context_authenticated(bs, e, l, s, r, ctx, ready, aut):
  G.analyze_accepts_exactly_context_authenticated(bs, e, l, s, r, ctx, ready, aut)

law reapply_analyze_refusal_exactly_authentication_absent:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  for aut: {D.authenticate(s, I.credential(r)) == None{} : Maybe<&2, D.Context>}
  {E.analyze(bs, e, l) == E.Rejected{S.Authentication{}} : E.Analysis}
def reapply_analyze_refusal_exactly_authentication_absent(bs, e, l, s, r, ready, aut):
  G.analyze_refusal_exactly_authentication_absent(bs, e, l, s, r, ready, aut)

law reapply_analyze_ready_publishable_refusal_credential_empty:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for +s: D.State
  for +r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  for structure: {D.structure(e, s) == True{} : Bool}
  for empty: {I.credential(r) == "" : String}
  {E.analyze(bs, e, l) == E.Rejected{S.Authentication{}} : E.Analysis}
def reapply_analyze_ready_publishable_refusal_credential_empty(bs, e, l, s, r, ready, structure, empty):
  G.analyze_ready_publishable_refusal_credential_empty(bs, e, l, s, r, ready, structure, empty)
