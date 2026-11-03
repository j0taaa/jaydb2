# Universal reapplications of actual quantities and original relations.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../contract/Semantics.bend as S
import ../../contract/Resources.bend as X
import ../../contract/Interface.bend as I
import ../../contract/Logic.bend as L
import ../../contract/Requirements.bend as R
import ../../src/Codec.bend as C
import ../../src/Input.bend as E
import ../../proof/InputRefusals.bend as G

law reapply_absence_of_request_in_body_real_justifies_input_original:
  for -world: Nat
  for -c: S.Configuration
  for -s: D.State
  for -input: X.Reception
  for +br: List<&2, U32>
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  for none: G.WithoutRequest(br)
  I.InputInvalid(I.Serve{world, c, s, input})
def reapply_absence_of_request_in_body_real_justifies_input_original(world, c, s, input, br, received, none):
  G.absence_of_request_in_body_real_justifies_input_original(world, c, s, input, br, received, none)

law reapply_codec_input_in_body_admissible_real_justifies_input_original:
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
def reapply_codec_input_in_body_admissible_real_justifies_input_original(world, c, s, input, br, body, ceiling,
  received, measured, fits, refused):
  G.codec_input_in_body_admissible_real_justifies_input_original(world, c, s, input, br, body, ceiling,
  received, measured, fits, refused)

law reapply_codec_limit_in_body_admissible_real_excludes_request_original:
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
def reapply_codec_limit_in_body_admissible_real_excludes_request_original(world, c, s, input, br, body, ceiling,
  received, measured, fits, refused):
  G.codec_limit_in_body_admissible_real_excludes_request_original(world, c, s, input, br, body, ceiling,
  received, measured, fits, refused)

law reapply_limit_internal_admitted_and_input_justified_original:
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
def reapply_limit_internal_admitted_and_input_justified_original(world, c, s, input, br, body, ceiling,
  received, ceiling_actual, measured, fits, internal):
  G.limit_internal_admitted_and_input_justified_original(world, c, s, input, br, body, ceiling,
  received, ceiling_actual, measured, fits, internal)

law reapply_body_processed_preserves_closing_original:
  for -world: Nat
  for -c: S.Configuration
  for -s: D.State
  for -input: X.Reception
  for +br: List<&2, U32>
  for received: {X.decide_reception(c, input) == X.ProcessBody{br} : X.Disposition}
  L.E<I.ClosingCorrect(I.Serve{world, c, s, input}, False{}),
    {X.body_invalid() == X.RefuseContinue{S.Input{}} : X.Disposition}>
def reapply_body_processed_preserves_closing_original(world, c, s, input, br, received):
  G.body_processed_preserves_closing_original(world, c, s, input, br, received)
