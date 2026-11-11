# Reapply the current executable body-measure/refusal laws. Complete small
# bodies with forged internal lengths are Input; excess physical bytes are Limit.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../src/Codec.bend as C
import ../../src/Input.bend as E
import ../../proof/InputMeasure.bend as G

law reapply_limit_internal_in_admitted_body_is_input:
  for +bytes: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +state: D.State
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for internal: {C.decode(bytes, ceiling) == C.Limit{} : C.Outcome}
  {E.read_message(Some{ceiling}, bytes, state) == E.ErrorMessage{S.Input{}} : E.PreAuthentication}
def reapply_limit_internal_in_admitted_body_is_input(bytes, body, ceiling, state, measured, fits, internal):
  G.limit_internal_in_body_admitted_and_input(bytes, body, ceiling, state, measured, fits, internal)

law reapply_body_above_ceiling_is_limit:
  for +bytes: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +state: D.State
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  for above: {C.less_equal64(body, ceiling) == False{} : Bool}
  {E.read_message(Some{ceiling}, bytes, state) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
def reapply_body_above_ceiling_is_limit(bytes, body, ceiling, state, measured, above):
  G.body_real_above_of_ceiling_produces_limit(bytes, body, ceiling, state, measured, above)
