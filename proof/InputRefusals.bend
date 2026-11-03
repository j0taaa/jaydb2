# Envelope/codec rejections linked to ORIGINAL InputInvalid.
# Body reception is a specific external condition, never a fact
# chosen or an Environment created to satisfy the laws.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../contract/Resources.bend as X
import ../contract/Interface.bend as I
import ../contract/Logic.bend as L
import ../contract/Requirements.bend as R
import ../src/Codec.bend as C
import ../src/Input.bend as E
import ./CodecRefusals.bend as Refusals
import ./InputMeasure.bend as Measure

def WithoutRequest(-br: List<&2, U32>) -> Type:
  @r: P.Request -> P.Encoding(P.request_value(r), br) -> Empty

law absence_of_request_in_body_real_justifies_input_original:
  for -world: Nat
  for -c: S.Configuration
  for -s: D.State
  for -input: X.Reception
  for +br: List<&2, U32>
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  for none: WithoutRequest(br)
  I.InputInvalid(I.Serve{world, c, s, input})
def absence_of_request_in_body_real_justifies_input_original(world, c, s, input, br, received, none):
  L.Right{(br, L.Both{received, none})}

law codec_input_in_body_admissible_real_justifies_input_original:
  for -world: Nat
  for -c: S.Configuration
  for -s: D.State
  for +input: X.Reception
  for +br: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  for measured: {B.nat64(B.length(br)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for refused: {C.decode(br, ceiling) == C.Input{} : C.Outcome}
  I.InputInvalid(I.Serve{world, c, s, input})
def codec_input_in_body_admissible_real_justifies_input_original(world, c, s, input, br, body, ceiling,
  received, measured, fits, refused):
  none = Refusals.input_of_body_admissible_excludes_encoding(br, body, ceiling, measured, fits, refused)
  absence_of_request_in_body_real_justifies_input_original(world, c, s, input, br, received,
    r => encoded => none(P.request_value(r), encoded))

# This law requires body <= ceiling; excess size does not become input error.
law codec_limit_in_body_admissible_real_excludes_request_original:
  for -world: Nat
  for -c: S.Configuration
  for -s: D.State
  for +input: X.Reception
  for +br: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  for measured: {B.nat64(B.length(br)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for refused: {C.decode(br, ceiling) == C.Limit{} : C.Outcome}
  I.InputInvalid(I.Serve{world, c, s, input})
def codec_limit_in_body_admissible_real_excludes_request_original(world, c, s, input, br, body, ceiling,
  received, measured, fits, refused):
  none = Refusals.limit_of_body_admissible_excludes_encoding(br, body, ceiling, measured, fits, refused)
  absence_of_request_in_body_real_justifies_input_original(world, c, s, input, br, received,
    r => encoded => none(P.request_value(r), encoded))

# EXACT functional classification and ORIGINAL justification, with the same
# actual body measure. Neither conclusion is received as a hypothesis.
law limit_internal_admitted_and_input_justified_original:
  for -world: Nat
  for -c: S.Configuration
  for +s: D.State
  for +input: X.Reception
  for +br: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  for ceiling_actual: {B.nat64(R.limit_message(S.limits(c))) == Some{ceiling} : Maybe<&2, B.Number64>}
  for +measured: {B.nat64(B.length(br)) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for +internal: {C.decode(br, ceiling) == C.Limit{} : C.Outcome}
  L.E<{E.message(C.Limit{}, s) == E.ErrorMessage{S.Input{}} : E.PreAuthentication},
    L.E<{E.read_message(Some{ceiling}, br, s) == E.ErrorMessage{S.Input{}} : E.PreAuthentication},
      I.InputInvalid(I.Serve{world, c, s, input})>>
def limit_internal_admitted_and_input_justified_original(world, c, s, input, br, body, ceiling,
  received, ceiling_actual, measured, fits, internal):
  L.Both{{==}, L.Both{
    Measure.limit_internal_in_body_admitted_and_input(br, body, ceiling, s, measured, fits, internal),
    codec_limit_in_body_admissible_real_excludes_request_original(world, c, s, input,
      br, body, ceiling, received, measured, fits, internal)}}

law body_processed_preserves_closing_original:
  for -world: Nat
  for -c: S.Configuration
  for -s: D.State
  for -input: X.Reception
  for +br: List<&2, U32>
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  L.E<I.ClosingCorrect(I.Serve{world, c, s, input}, False{}),
    {X.body_invalid() == X.RefuseContinue{S.Input{}} : X.Disposition}>
def body_processed_preserves_closing_original(world, c, s, input, br, received):
  L.Both{
    (%Equal.sym(X.Disposition, X.decide_reception(c, input), X.ProcessBody{br}, received) :
      I.ClosingDisposition(_, False{})
      {==}), {==}}
