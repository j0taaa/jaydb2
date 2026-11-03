# Universal reapplications of actual quantities and original relations.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Protocol.bend as P
import ../../contract/Logic.bend as L
import ../../src/Codec.bend as C
import ../../src/Input.bend as E
import ../../src/Request.bend as Q
import ../../proof/InputMeasure.bend as G

law reapply_body_admitted_preserves_result_of_codec:
  for +bs: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {E.read_message(Some{ceiling}, bs, s) == E.message(C.decode(bs, ceiling), s) : E.PreAuthentication}
def reapply_body_admitted_preserves_result_of_codec(bs, body, ceiling, s, measured, fits):
  G.body_admitted_preserves_result_of_codec(bs, body, ceiling, s, measured, fits)

law reapply_body_real_above_of_ceiling_produces_limit:
  for +bs: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for above: {C.less_equal64(body, ceiling) == False{} : Bool}
  {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
def reapply_body_real_above_of_ceiling_produces_limit(bs, body, ceiling, s, measured, above):
  G.body_real_above_of_ceiling_produces_limit(bs, body, ceiling, s, measured, above)

law reapply_body_real_negative_representable_produces_limit:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == None{} : Maybe<&2, B.Number64>}
  {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
def reapply_body_real_negative_representable_produces_limit(bs, ceiling, s, measured):
  G.body_real_negative_representable_produces_limit(bs, ceiling, s, measured)

law reapply_decoding_accepts_preserves_message:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +s: D.State
  for -v: D.Value
  for accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  {E.read_message(Some{ceiling}, bs, s) == E.message(C.decode(bs, ceiling), s) : E.PreAuthentication}
def reapply_decoding_accepts_preserves_message(bs, ceiling, s, v, accepted):
  G.decoding_accepts_preserves_message(bs, ceiling, s, v, accepted)

law reapply_limit_internal_in_body_admitted_and_input:
  for +bs: List<&2, U32>
  for body: B.Number64
  for +ceiling: B.Number64
  for +s: D.State
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for internal: {C.decode(bs, ceiling) == C.Limit{} : C.Outcome}
  {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Input{}} : E.PreAuthentication}
def reapply_limit_internal_in_body_admitted_and_input(bs, body, ceiling, s, measured, fits, internal):
  G.limit_internal_in_body_admitted_and_input(bs, body, ceiling, s, measured, fits, internal)

law reapply_message_of_codec_never_creates_limit_of_resource:
  for result: C.Outcome
  for -s: D.State
  G.WithoutLimit(E.message(result, s))
def reapply_message_of_codec_never_creates_limit_of_resource(result, s):
  G.message_of_codec_never_creates_limit_of_resource(result, s)

law reapply_message_limit_requires_excess_of_count_real:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +s: D.State
  for failure: {E.read_message(Some{ceiling}, bs, s) == E.ErrorMessage{S.Limit{}} : E.PreAuthentication}
  G.CountExceeded(B.nat64(B.length(bs)), ceiling)
def reapply_message_limit_requires_excess_of_count_real(bs, ceiling, s, failure):
  G.message_limit_requires_excess_of_count_real(bs, ceiling, s, failure)
