# Inverts actual Input composition into exact blocks, ceilings and values.
# Envelope rejection excludes canonical requests for the same bytes.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../src/Input.bend as E
import ../src/State.bend as State
import ../src/Request.bend as Q
import ../src/Transport.bend as T
import ../src/Codec.bend as C
import ./CodecLaw2.bend as Codec
import ./CodecComplete.bend as Complete
import ./Representation.bend as V
import ./Transport.bend as Transport
import ./Foundations.bend as F

def ValueAccepted(-bs: List<&2, U32>, -ceiling: B.Number64, -v: D.Value) -> Type:
  L.E<{C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome},
    L.E<P.Encoding(v, bs), {D.value_valid(v) == True{} : Bool}>>

def RequestAccepts(-br: List<&2, U32>, -tr: B.Number64, -r: P.Request) -> Type:
  ValueAccepted(br, tr, P.request_value(r))

def StateAccepted(-be: List<&2, U32>, -te: B.Number64, -e: D.Schema, -s: D.State) -> Type:
  &ve: D.Value -> L.E<ValueAccepted(be, te, ve),
    L.E<{State.decode(ve, e) == Some{s} : Maybe<&2, D.State>},
      {D.structure(e, s) == True{} : Bool}>>

# All blocks, ceilings and values are witnesses extracted from execution.
# SeparationExact includes reassembly of the ORIGINAL packet and block bytes.
def InversionReady(-bs: List<&2, U32>, -e: D.Schema, -l: S.Limits,
  -s: D.State, -r: P.Request) -> Type:
  &be: List<&2, U32> -> &br: List<&2, U32> -> &te: B.Number64 -> &tr: B.Number64 ->
    L.E<{T.separate(bs) == Some{T.Parts{be, br}} : Maybe<&2, T.Parts>},
      L.E<Transport.SeparationExact(bs, T.Parts{be, br}),
        L.E<{B.nat64(R.limit_state(l)) == Some{te} : Maybe<&2, B.Number64>},
          L.E<{B.nat64(R.limit_message(l)) == Some{tr} : Maybe<&2, B.Number64>},
            L.E<StateAccepted(be, te, e, s), RequestAccepts(br, tr, r)>>>>>

def MessageFaithful(pre: E.PreAuthentication, -origin: D.State,
  -br: List<&2, U32>, -tr: B.Number64) -> Type:
  match pre:
    case E.InputReady{s, r}:
      L.E<{s == origin : D.State}, RequestAccepts(br, tr, r)>
    case _:
      Unit

def LimitMessageFaithful(pre: E.PreAuthentication, -origin: D.State,
  -br: List<&2, U32>, -limit: Maybe<&2, B.Number64>) -> Type:
  match pre:
    case E.InputReady{s, r}:
      &tr: B.Number64 -> L.E<{limit == Some{tr} : Maybe<&2, B.Number64>},
        MessageFaithful(E.InputReady{s, r}, origin, br, tr)>
    case _:
      Unit

def StateFaithful(pre: E.PreAuthentication, -be: List<&2, U32>, -te: B.Number64,
  -e: D.Schema, -br: List<&2, U32>, -limit: Maybe<&2, B.Number64>) -> Type:
  match pre:
    case E.InputReady{s, r}:
      &tr: B.Number64 -> L.E<{limit == Some{tr} : Maybe<&2, B.Number64>},
        L.E<StateAccepted(be, te, e, s), RequestAccepts(br, tr, r)>>
    case _:
      Unit

def LimitStateFaithful(pre: E.PreAuthentication, -limit_state: Maybe<&2, B.Number64>,
  -be: List<&2, U32>, -e: D.Schema, -br: List<&2, U32>,
  -limit_msg: Maybe<&2, B.Number64>) -> Type:
  match pre:
    case E.InputReady{s, r}:
      &te: B.Number64 -> L.E<{limit_state == Some{te} : Maybe<&2, B.Number64>},
        StateFaithful(E.InputReady{s, r}, be, te, e, br, limit_msg)>
    case _:
      Unit

def ReadyRelated(pre: E.PreAuthentication, -bs: List<&2, U32>,
  -e: D.Schema, -l: S.Limits) -> Type:
  match pre:
    case E.InputReady{s, r}:
      InversionReady(bs, e, l, s, r)
    case _:
      Unit

def value_accepted(+br: List<&2, U32>, +tr: B.Number64, +v: D.Value,
  +accepted: {C.decode(br, tr) == C.Decoded{v} : C.Outcome}) -> ValueAccepted(br, tr, v):
  L.Both{accepted, Codec.acceptance_reconstitutes_encoding_original_and_validity(br, tr, v, accepted)}

def request_of_value_accepted(+br: List<&2, U32>, +tr: B.Number64, +v: D.Value,
  +r: P.Request, accepted: {C.decode(br, tr) == C.Decoded{v} : C.Outcome},
  extracted: {Q.extract(v) == Some{r} : Maybe<&2, P.Request>}) -> RequestAccepts(br, tr, r):
  F.combined_pair(RequestAccepts(br, tr, r), {D.value_valid(v) == True{} : Bool},
    {v == P.request_value(r) : D.Value}, V.extract_preserves_value_and_is_valid(v, r, extracted),
    valid => exact =>
      %exact : ValueAccepted(br, tr, _)
      value_accepted(br, tr, v, accepted))

def envelope_faithful(q: Maybe<&2, P.Request>, +s: D.State,
  +br: List<&2, U32>, +tr: B.Number64, +v: D.Value,
  accepted: {C.decode(br, tr) == C.Decoded{v} : C.Outcome},
  extracted: {Q.extract(v) == q : Maybe<&2, P.Request>}) ->
  MessageFaithful(E.envelope(q, s), s, br, tr):
  match q:
    case None{}:
      Unit{}
    case Some{+r}:
      L.Both{{==}, request_of_value_accepted(br, tr, v, r, accepted, extracted)}

def message_faithful(result: C.Outcome, +s: D.State,
  +br: List<&2, U32>, +tr: B.Number64,
  accepted: {C.decode(br, tr) == result : C.Outcome}) ->
  MessageFaithful(E.message(result, s), s, br, tr):
  match result:
    case C.Input{}:
      Unit{}
    case C.Limit{}:
      Unit{}
    case C.Decoded{+v}:
      envelope_faithful(Q.extract(v), s, br, tr, v, accepted, {==})

def attach_limit_message(pre: E.PreAuthentication, -s: D.State,
  -br: List<&2, U32>, +tr: B.Number64, faithful: MessageFaithful(pre, s, br, tr)) ->
  LimitMessageFaithful(pre, s, br, Some{tr}):
  match pre:
    case E.InputReady{state, request}:
      (tr, L.Both{{==}, faithful})
    case E.ErrorMessage{status}:
      Unit{}
    case E.ErrorTransport{}:
      Unit{}

def message_fits_faithful(fits: Bool, +br: List<&2, U32>, +tr: B.Number64, +s: D.State) ->
  LimitMessageFaithful(E.message_fits(fits, br, tr, s), s, br, Some{tr}):
  match fits:
    case False{}:
      Unit{}
    case True{}:
      attach_limit_message(E.message(C.decode(br, tr), s), s, br, tr,
        message_faithful(C.decode(br, tr), s, br, tr, {==}))

def message_measure_faithful(measure: Maybe<&2, B.Number64>, +br: List<&2, U32>, +tr: B.Number64, +s: D.State) ->
  LimitMessageFaithful(E.message_measure(measure, br, tr, s), s, br, Some{tr}):
  match measure:
    case None{}:
      Unit{}
    case Some{body}:
      message_fits_faithful(C.less_equal64(body, tr), br, tr, s)

def read_message_faithful(limit: Maybe<&2, B.Number64>, +br: List<&2, U32>, +s: D.State) ->
  LimitMessageFaithful(E.read_message(limit, br, s), s, br, limit):
  match limit:
    case None{}:
      Unit{}
    case Some{+tr}:
      message_measure_faithful(B.nat64(B.length(br)), br, tr, s)

def link_state_to_body(pre: E.PreAuthentication, +origin: D.State,
  +ve: D.Value, +be: List<&2, U32>, +te: B.Number64, +e: D.Schema,
  -br: List<&2, U32>, -limit: Maybe<&2, B.Number64>,
  accepted: {C.decode(be, te) == C.Decoded{ve} : C.Outcome},
  +state: {State.decode(ve, e) == Some{origin} : Maybe<&2, D.State>},
  message: LimitMessageFaithful(pre, origin, br, limit)) -> StateFaithful(pre, be, te, e, br, limit):
  match pre:
    case E.InputReady{+s, r}:
      match message:
        case (tr, L.Both{ceiling, L.Both{+equal, request}}):
          (tr, L.Both{ceiling, L.Both{
            (ve, L.Both{value_accepted(be, te, ve, accepted), L.Both{
              (%Equal.sym(D.State, s, origin, equal) :
                {State.decode(ve, e) == Some{_} : Maybe<&2, D.State>}
                state),
              (%Equal.sym(D.State, s, origin, equal) : {D.structure(e, _) == True{} : Bool}
                V.transport_private_only_returns_state_structured(ve, e, origin, state))}}),
            request}})
    case E.ErrorMessage{status}:
      Unit{}
    case E.ErrorTransport{}:
      Unit{}

def state_read_faithful(q: Maybe<&2, D.State>, +ve: D.Value,
  +be: List<&2, U32>, +te: B.Number64, +e: D.Schema,
  +br: List<&2, U32>, +limit: Maybe<&2, B.Number64>,
  accepted: {C.decode(be, te) == C.Decoded{ve} : C.Outcome},
  state: {State.decode(ve, e) == q : Maybe<&2, D.State>}) ->
  StateFaithful(E.state_read(q, br, limit), be, te, e, br, limit):
  match q:
    case None{}:
      Unit{}
    case Some{+s}:
      link_state_to_body(E.read_message(limit, br, s), s, ve, be, te, e, br, limit,
        accepted, state, read_message_faithful(limit, br, s))

def state_decoded_faithful(result: C.Outcome, +be: List<&2, U32>, +te: B.Number64,
  +e: D.Schema, +br: List<&2, U32>, +limit: Maybe<&2, B.Number64>,
  accepted: {C.decode(be, te) == result : C.Outcome}) ->
  StateFaithful(E.state_decoded(result, e, br, limit), be, te, e, br, limit):
  match result:
    case C.Input{}:
      Unit{}
    case C.Limit{}:
      Unit{}
    case C.Decoded{+ve}:
      state_read_faithful(State.decode(ve, e), ve, be, te, e, br, limit, accepted, {==})

def attach_limit_state(pre: E.PreAuthentication, +te: B.Number64,
  -be: List<&2, U32>, -e: D.Schema, -br: List<&2, U32>, -limit: Maybe<&2, B.Number64>,
  faithful: StateFaithful(pre, be, te, e, br, limit)) ->
  LimitStateFaithful(pre, Some{te}, be, e, br, limit):
  match pre:
    case E.InputReady{state, request}:
      (te, L.Both{{==}, faithful})
    case E.ErrorMessage{status}:
      Unit{}
    case E.ErrorTransport{}:
      Unit{}

def read_state_faithful(limit_state: Maybe<&2, B.Number64>, +e: D.Schema,
  +be: List<&2, U32>, +br: List<&2, U32>, +limit: Maybe<&2, B.Number64>) ->
  LimitStateFaithful(E.read_state(limit_state, e, be, br, limit), limit_state, be, e, br, limit):
  match limit_state:
    case None{}:
      Unit{}
    case Some{+te}:
      attach_limit_state(E.state_decoded(C.decode(be, te), e, br, limit), te,
        be, e, br, limit, state_decoded_faithful(C.decode(be, te), be, te, e, br, limit, {==}))

def link_blocks(pre: E.PreAuthentication, +bs: List<&2, U32>, +be: List<&2, U32>,
  +br: List<&2, U32>, +e: D.Schema, +l: S.Limits,
  +separate: {T.separate(bs) == Some{T.Parts{be, br}} : Maybe<&2, T.Parts>},
  reading: LimitStateFaithful(pre, B.nat64(R.limit_state(l)), be, e, br,
    B.nat64(R.limit_message(l)))) -> ReadyRelated(pre, bs, e, l):
  match pre:
    case E.InputReady{s, r}:
      match reading:
        case (te, L.Both{ceiling_and, (tr, L.Both{ceiling_r, L.Both{state, request}})}):
          (be, br, te, tr, L.Both{separate, L.Both{
            Transport.all_separation_accepts_reconstructs_packet_original(bs, T.Parts{be, br}, separate),
            L.Both{ceiling_and, L.Both{ceiling_r, L.Both{state, request}}}}})
    case E.ErrorMessage{status}:
      Unit{}
    case E.ErrorTransport{}:
      Unit{}

def parts_faithful(parts: Maybe<&2, T.Parts>, +bs: List<&2, U32>, +e: D.Schema,
  +l: S.Limits, separate: {T.separate(bs) == parts : Maybe<&2, T.Parts>}) ->
  ReadyRelated(E.parts(parts, e, l), bs, e, l):
  match parts:
    case None{}:
      Unit{}
    case Some{T.Parts{+be, +br}}:
      link_blocks(E.read_state(B.nat64(R.limit_state(l)), e, be, br,
        B.nat64(R.limit_message(l))), bs, be, br, e, l, separate,
        read_state_faithful(B.nat64(R.limit_state(l)), e, be, br, B.nat64(R.limit_message(l))))

law decode_reconstructs_stages_real:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  ReadyRelated(E.decode(bs, e, l), bs, e, l)
def decode_reconstructs_stages_real(bs, e, l):
  parts_faithful(T.separate(bs), bs, e, l, {==})

# The only operational hypothesis is the result actually obtained.
law ready_reconstructs_blocks_ceilings_state_and_request:
  for +bs: List<&2, U32>
  for +e: D.Schema
  for +l: S.Limits
  for -s: D.State
  for -r: P.Request
  for ready: {E.decode(bs, e, l) == E.InputReady{s, r} : E.PreAuthentication}
  InversionReady(bs, e, l, s, r)
def ready_reconstructs_blocks_ceilings_state_and_request(bs, e, l, s, r, ready):
  %ready : ReadyRelated(_, bs, e, l)
  decode_reconstructs_stages_real(bs, e, l)

# Envelope rejection: completeness prevents the SAME bytes from encoding
# any request. Measure and ceiling are the actual body's.
def extraction_of_result(result: C.Outcome) -> Maybe<&2, P.Request>:
  match result:
    case C.Decoded{v}:
      Q.extract(v)
    case _:
      None{}

def WithoutRequestEncoded(-br: List<&2, U32>) -> Type:
  @r: P.Request -> P.Encoding(P.request_value(r), br) -> Empty

def exclude_request_alternative(+br: List<&2, U32>, +body: B.Number64,
  +tr: B.Number64, +v: D.Value,
  +measured: {B.nat64(B.length(br)) == Some{body} : Maybe<&2, B.Number64>},
  +fits: {C.less_equal64(body, tr) == True{} : Bool},
  +accepted: {C.decode(br, tr) == C.Decoded{v} : C.Outcome},
  +refused: {Q.extract(v) == None{} : Maybe<&2, P.Request>},
  +r: P.Request, encoded: P.Encoding(P.request_value(r), br)) -> Empty:
  +decoded = Complete.all_encoding_canonical_representable_and_decoded(
    P.request_value(r), br, body, tr, encoded, measured, fits)
  F.combined_pair(Empty, P.Encoding(P.request_value(r), br),
    {D.value_valid(P.request_value(r)) == True{} : Bool},
    Codec.acceptance_reconstitutes_encoding_original_and_validity(br, tr, P.request_value(r), decoded),
    canonical => valid =>
      F.none_negative_some(P.Request, r,
        Equal.trans(Maybe<&2, P.Request>, None{}, Q.extract(v), Some{r},
          Equal.sym(Maybe<&2, P.Request>, Q.extract(v), None{}, refused),
          Equal.trans(Maybe<&2, P.Request>, Q.extract(v), Q.extract(P.request_value(r)), Some{r},
            Equal.cong(C.Outcome, Maybe<&2, P.Request>, extraction_of_result,
              C.Decoded{v}, C.Decoded{P.request_value(r)},
              Equal.trans(C.Outcome, C.Decoded{v}, C.decode(br, tr),
                C.Decoded{P.request_value(r)},
                Equal.sym(C.Outcome, C.decode(br, tr), C.Decoded{v}, accepted), decoded)),
            V.request_is_valid_preserves_all_os_fields(r, valid)))))

law codec_accepted_combined_envelope_invalid_excludes_request_canonical:
  for +br: List<&2, U32>
  for +body: B.Number64
  for +tr: B.Number64
  for +v: D.Value
  for +measured: {B.nat64(B.length(br)) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, tr) == True{} : Bool}
  for +accepted: {C.decode(br, tr) == C.Decoded{v} : C.Outcome}
  for +refused: {Q.extract(v) == None{} : Maybe<&2, P.Request>}
  WithoutRequestEncoded(br)
def codec_accepted_combined_envelope_invalid_excludes_request_canonical(br, body, tr, v, measured, fits, accepted, refused):
  r => encoded => exclude_request_alternative(br, body, tr, v, measured, fits, accepted, refused, r, encoded)
