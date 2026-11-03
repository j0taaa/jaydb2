# The read contract preserves bytes and uint64 logical limits; the parser remains original.
import Base
import ./RoutesService.bend as Route
import ./Transport.bend as Transport
import ./InputMeasure.bend as M
import ../src/State.bend as State
import ../src/Transport.bend as T
import ./Input.bend as Input
import ../contract/Data.bend as D
import ../contract/Bytes.bend as B
import ../contract/Logic.bend as L
import ../contract/Interface.bend as I
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../contract/Resources.bend as X
import ../contract/Requirements.bend as R
import ../src/Codec.bend as C
import ../src/Input.bend as E
import ./Foundations.bend as F

# These are primitive Rust header/copy results, not decoder results.
def BodyCopied(-c: S.Configuration, -reception: X.Reception) -> Type:
  L.E<X.ReceptionValid(reception), @br: List<&2, U32> ->
    {X.decide_reception(c, reception) == X.ProcessBody{br} : X.Disposition} ->
      &body: B.Number64 -> &ceiling: B.Number64 ->
        L.E<{B.nat64(B.length(br)) == Some{body} : Maybe<&2, B.Number64>},
          L.E<{B.nat64(R.limit_message(S.limits(c))) == Some{ceiling} : Maybe<&2, B.Number64>},
            {C.less_equal64(body, ceiling) == True{} : Bool}>>>

# The snapshot is the same private encoding of published state.
def StateCopied(-c: S.Configuration, +s: D.State, +be: List<&2, U32>) -> Type:
  &ce: B.Number64 -> &te: B.Number64 ->
    L.E<P.Encoding(D.state_value(s), be),
      L.E<{B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>},
        L.E<{B.nat64(R.limit_state(S.limits(c))) == Some{te} : Maybe<&2, B.Number64>},
          {C.less_equal64(ce, te) == True{} : Bool}>>>

# If these bytes encoded a canonical request, ACTUAL transport/state/codec
# composition would return it. ErrorMessage therefore excludes it.
def request_ready(pre: E.PreAuthentication) -> Maybe<&2, P.Request>:
  match pre:
    case E.InputReady{s, r}: Some{r}
    case _: None{}

law error_of_packet_canonical_excludes_request:
  for +e: D.Schema
  for +s: D.State
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for +status: S.Status
  for cod_and: P.Encoding(D.state_value(s), be)
  for +assembly: {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for +measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for +measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for +ceiling_and: {B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>}
  for +ceiling_r: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for +fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for +fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for +structure: {D.structure(e, s) == True{} : Bool}
  for +error: {E.decode(bs, e, l) == E.ErrorMessage{status} : E.PreAuthentication}
  @r: P.Request -> P.Encoding(P.request_value(r), br) -> Empty
def error_of_packet_canonical_excludes_request(e, s, l, be, br, bs, ce, cr, te, tr, status,
  cod_and, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure, error):
  +r => cod_r => F.none_negative_some(P.Request, r,
    Equal.cong(E.PreAuthentication, Maybe<&2, P.Request>, request_ready, E.ErrorMessage{status}, E.InputReady{s, r},
      Equal.trans(E.PreAuthentication, E.ErrorMessage{status}, E.decode(bs, e, l), E.InputReady{s, r},
        Equal.sym(E.PreAuthentication, E.decode(bs, e, l), E.ErrorMessage{status}, error),
        Input.bytes_canonical_assembled_produce_ready_exact(e, s, r, l, be, br, bs, ce, cr, te, tr,
          cod_and, cod_r, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure))))

# Only actual body size produces Limit; below the ceiling this status never arises.
def message_admitted_without_limit(+br: List<&2, U32>, +cr: B.Number64, +tr: B.Number64, +s: D.State,
  measure: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(cr, tr) == True{} : Bool}) -> M.WithoutLimit(E.read_message(Some{tr}, br, s)):
  %Equal.sym(E.PreAuthentication, E.read_message(Some{tr}, br, s), E.message(C.decode(br, tr), s),
    M.body_admitted_preserves_result_of_codec(br, cr, tr, s, measure, fits)) : M.WithoutLimit(_)
  M.message_of_codec_never_creates_limit_of_resource(C.decode(br, tr), s)

def state_read_without_limit(q: Maybe<&2, D.State>, +br: List<&2, U32>, +cr: B.Number64, +tr: B.Number64,
  measure: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(cr, tr) == True{} : Bool}) -> M.WithoutLimit(E.state_read(q, br, Some{tr})):
  match q:
    case None{}: Unit{}
    case Some{s}: message_admitted_without_limit(br, cr, tr, s, measure, fits)

def state_decoded_without_limit(q: C.Outcome, +e: D.Schema, +br: List<&2, U32>, +cr: B.Number64, +tr: B.Number64,
  measure: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(cr, tr) == True{} : Bool}) -> M.WithoutLimit(E.state_decoded(q, e, br, Some{tr})):
  match q:
    case C.Decoded{v}: state_read_without_limit(State.decode(v, e), br, cr, tr, measure, fits)
    case C.Input{}: Unit{}
    case C.Limit{}: Unit{}

def read_state_without_limit(cap: Maybe<&2, B.Number64>, +e: D.Schema, +be: List<&2, U32>, +br: List<&2, U32>, +cr: B.Number64, +tr: B.Number64,
  measure: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(cr, tr) == True{} : Bool}) -> M.WithoutLimit(E.read_state(cap, e, be, br, Some{tr})):
  match cap:
    case None{}: Unit{}
    case Some{te}: state_decoded_without_limit(C.decode(be, te), e, br, cr, tr, measure, fits)

law packet_assembled_combined_body_admitted_negative_generates_limit:
  for +e: D.Schema
  for +l: S.Limits
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +cr: B.Number64
  for +tr: B.Number64
  for separation: {T.separate(bs) == Some{T.Parts{be, br}} : Maybe<&2, T.Parts>}
  for measure: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling: {B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(cr, tr) == True{} : Bool}
  M.WithoutLimit(E.decode(bs, e, l))
def packet_assembled_combined_body_admitted_negative_generates_limit(e, l, be, br, bs, cr, tr, separation, measure, ceiling, fits):
  %Equal.sym(Maybe<&2, T.Parts>, T.separate(bs), Some{T.Parts{be, br}}, separation) : M.WithoutLimit(E.parts(_, e, l))
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(R.limit_message(l)), Some{tr}, ceiling) :
    M.WithoutLimit(E.read_state(B.nat64(R.limit_state(l)), e, be, br, _))
  read_state_without_limit(B.nat64(R.limit_state(l)), e, be, br, cr, tr, measure, fits)


# The public error preserves the body's cause, not a physical parser limit.
def CauseInput(x: I.Scenario, error: Route.ErrorInput) -> Type:
  match error:
    case Route.Input{}: I.InputInvalid(x)
    case Route.Limit{}: I.LimitInInput(x)

def message_without_limit_classifies_input(-x: I.Scenario, status: S.Status,
  without_limit: M.WithoutLimit(E.ErrorMessage{status}), input: I.InputInvalid(x)) ->
  CauseInput(x, Route.error_of_message(status)):
  match status:
    case S.Success{}: input
    case S.Refusal{}: input
    case S.Input{}: input
    case S.Authentication{}: input
    case S.Certificate{}: input
    case S.DataError{}: input
    case S.Limit{}: match without_limit:
    case S.Failure{}: input

law error_of_body_processed_has_cause_original:
  for ~c: S.Configuration
  for +world: Nat
  for +s: D.State
  for +reception: X.Reception
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Number64
  for +cr: B.Number64
  for +te: B.Number64
  for +tr: B.Number64
  for +status: S.Status
  for cod_and: P.Encoding(D.state_value(s), be)
  for +assembly: {T.join(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for octets_and: {B.octets_all_valid(be) == True{} : Bool}
  for octets_r: {B.octets_all_valid(br) == True{} : Bool}
  for measure_and: {B.nat64(B.length(be)) == Some{ce} : Maybe<&2, B.Number64>}
  for +measure_r: {B.nat64(B.length(br)) == Some{cr} : Maybe<&2, B.Number64>}
  for ceiling_and: {B.nat64(R.limit_state(S.limits(c))) == Some{te} : Maybe<&2, B.Number64>}
  for +ceiling_r: {B.nat64(R.limit_message(S.limits(c))) == Some{tr} : Maybe<&2, B.Number64>}
  for fits_and: {C.less_equal64(ce, te) == True{} : Bool}
  for +fits_r: {C.less_equal64(cr, tr) == True{} : Bool}
  for structure: {D.structure(S.schema(c), s) == True{} : Bool}
  for received: {X.decide_reception(c, reception) == X.ProcessBody{br} : X.Disposition}
  for +error: {E.decode(bs, S.schema(c), S.limits(c)) == E.ErrorMessage{status} : E.PreAuthentication}
  CauseInput(I.Serve{world, c, s, reception}, Route.error_of_message(status))
def error_of_body_processed_has_cause_original(c, world, s, reception, be, br, bs, ce, cr, te, tr, status,
  cod_and, assembly, octets_and, octets_r, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure, received, error):
  message_without_limit_classifies_input(I.Serve{world, c, s, reception}, status,
    (%error : M.WithoutLimit(_)
      packet_assembled_combined_body_admitted_negative_generates_limit(S.schema(c), S.limits(c), be, br, bs, cr, tr,
        Transport.separate_inverts_all_assembly_is_valid(be, br, bs, assembly, octets_and, octets_r), measure_r, ceiling_r, fits_r)),
    L.Right{(br, L.Both{received,
      error_of_packet_canonical_excludes_request(S.schema(c), s, S.limits(c), be, br, bs, ce, cr, te, tr, status,
        cod_and, assembly, measure_and, measure_r, ceiling_and, ceiling_r, fits_and, fits_r, structure, error)})})
