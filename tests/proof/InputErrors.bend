# Universal reapplications of ten error classes in the actual pipeline.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Semantics.bend as S
import ../../contract/Protocol.bend as P
import ../../contract/Requirements.bend as R
import ../../contract/Logic.bend as L
import ../../src/Codec.bend as C
import ../../src/Input.bend as A
import ../../src/State.bend as E
import ../../src/Request.bend as Q
import ../../src/Transport.bend as T
import ../../proof/InputErrors.bend as G

law reapply_pipeline_transport_invalid:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for separate: {T.separate(bytes) == None{} : Maybe<&2, T.Parts>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def reapply_pipeline_transport_invalid(bytes, schema, limits, separate):
  G.pipeline_transport_invalid(bytes, schema, limits, separate)

law reapply_pipeline_limit_state_negative_representable:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for absent: {B.nat64(R.limit_state(limits)) == None{} : Maybe<&2, B.Number64>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def reapply_pipeline_limit_state_negative_representable(bytes, schema, limits, absent):
  G.pipeline_limit_state_negative_representable(bytes, schema, limits, absent)

law reapply_pipeline_limit_message_negative_representable:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for absent: {B.nat64(R.limit_message(limits)) == None{} : Maybe<&2, B.Number64>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def reapply_pipeline_limit_message_negative_representable(bytes, schema, limits, absent):
  G.pipeline_limit_message_negative_representable(bytes, schema, limits, absent)

law reapply_pipeline_state_input:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling: B.Number64
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured: {B.nat64(R.limit_state(limits)) == Some{ceiling} : Maybe<&2, B.Number64>}
  for refused: {C.decode(state, ceiling) == C.Input{} : C.Outcome}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def reapply_pipeline_state_input(bytes, schema, limits, state, body, ceiling, separate, measured, refused):
  G.pipeline_state_input(bytes, schema, limits, state, body, ceiling, separate, measured, refused)

law reapply_pipeline_state_limit:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling: B.Number64
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured: {B.nat64(R.limit_state(limits)) == Some{ceiling} : Maybe<&2, B.Number64>}
  for refused: {C.decode(state, ceiling) == C.Limit{} : C.Outcome}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def reapply_pipeline_state_limit(bytes, schema, limits, state, body, ceiling, separate, measured, refused):
  G.pipeline_state_limit(bytes, schema, limits, state, body, ceiling, separate, measured, refused)

law reapply_pipeline_state_negative_extracted:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling: B.Number64
  for +value: D.Value
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured: {B.nat64(R.limit_state(limits)) == Some{ceiling} : Maybe<&2, B.Number64>}
  for read: {C.decode(state, ceiling) == C.Decoded{value} : C.Outcome}
  for invalid: {E.decode(value, schema) == None{} : Maybe<&2, D.State>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def reapply_pipeline_state_negative_extracted(bytes, schema, limits, state, body, ceiling, value,
  separate, measured, read, invalid):
  G.pipeline_state_negative_extracted(bytes, schema, limits, state, body, ceiling, value,
  separate, measured, read, invalid)

law reapply_pipeline_message_input:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling_state: B.Number64
  for +ceiling_msg: B.Number64
  for +value_state: D.Value
  for +s: D.State
  for count: B.Number64
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured_state: {B.nat64(R.limit_state(limits)) == Some{ceiling_state} : Maybe<&2, B.Number64>}
  for measured_msg: {B.nat64(R.limit_message(limits)) == Some{ceiling_msg} : Maybe<&2, B.Number64>}
  for read: {C.decode(state, ceiling_state) == C.Decoded{value_state} : C.Outcome}
  for extracted: {E.decode(value_state, schema) == Some{s} : Maybe<&2, D.State>}
  for measured_body: {B.nat64(B.length(body)) == Some{count} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(count, ceiling_msg) == True{} : Bool}
  for refused: {C.decode(body, ceiling_msg) == C.Input{} : C.Outcome}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorMessage{S.Input{}} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.Rejected{S.Input{}} : A.Analysis}>
def reapply_pipeline_message_input(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, fits, refused):
  G.pipeline_message_input(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, fits, refused)

law reapply_pipeline_message_limit_internal_admitted:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling_state: B.Number64
  for +ceiling_msg: B.Number64
  for +value_state: D.Value
  for +s: D.State
  for count: B.Number64
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured_state: {B.nat64(R.limit_state(limits)) == Some{ceiling_state} : Maybe<&2, B.Number64>}
  for measured_msg: {B.nat64(R.limit_message(limits)) == Some{ceiling_msg} : Maybe<&2, B.Number64>}
  for read: {C.decode(state, ceiling_state) == C.Decoded{value_state} : C.Outcome}
  for extracted: {E.decode(value_state, schema) == Some{s} : Maybe<&2, D.State>}
  for measured_body: {B.nat64(B.length(body)) == Some{count} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(count, ceiling_msg) == True{} : Bool}
  for refused: {C.decode(body, ceiling_msg) == C.Limit{} : C.Outcome}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorMessage{S.Input{}} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.Rejected{S.Input{}} : A.Analysis}>
def reapply_pipeline_message_limit_internal_admitted(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, fits, refused):
  G.pipeline_message_limit_internal_admitted(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, fits, refused)

law reapply_pipeline_message_body_above_of_ceiling:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling_state: B.Number64
  for +ceiling_msg: B.Number64
  for +value_state: D.Value
  for +s: D.State
  for count: B.Number64
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured_state: {B.nat64(R.limit_state(limits)) == Some{ceiling_state} : Maybe<&2, B.Number64>}
  for measured_msg: {B.nat64(R.limit_message(limits)) == Some{ceiling_msg} : Maybe<&2, B.Number64>}
  for read: {C.decode(state, ceiling_state) == C.Decoded{value_state} : C.Outcome}
  for extracted: {E.decode(value_state, schema) == Some{s} : Maybe<&2, D.State>}
  for measured_body: {B.nat64(B.length(body)) == Some{count} : Maybe<&2, B.Number64>}
  for above: {C.less_equal64(count, ceiling_msg) == False{} : Bool}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorMessage{S.Limit{}} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.Rejected{S.Limit{}} : A.Analysis}>
def reapply_pipeline_message_body_above_of_ceiling(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, above):
  G.pipeline_message_body_above_of_ceiling(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, above)

law reapply_pipeline_envelope_invalid:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling_state: B.Number64
  for +ceiling_msg: B.Number64
  for +value_state: D.Value
  for +s: D.State
  for +value_msg: D.Value
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured_state: {B.nat64(R.limit_state(limits)) == Some{ceiling_state} : Maybe<&2, B.Number64>}
  for measured_msg: {B.nat64(R.limit_message(limits)) == Some{ceiling_msg} : Maybe<&2, B.Number64>}
  for read_state: {C.decode(state, ceiling_state) == C.Decoded{value_state} : C.Outcome}
  for extracted: {E.decode(value_state, schema) == Some{s} : Maybe<&2, D.State>}
  for read_msg: {C.decode(body, ceiling_msg) == C.Decoded{value_msg} : C.Outcome}
  for absent: {Q.extract(value_msg) == None{} : Maybe<&2, P.Request>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorMessage{S.Input{}} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.Rejected{S.Input{}} : A.Analysis}>
def reapply_pipeline_envelope_invalid(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, value_msg, separate, measured_state, measured_msg, read_state,
  extracted, read_msg, absent):
  G.pipeline_envelope_invalid(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, value_msg, separate, measured_state, measured_msg, read_state,
  extracted, read_msg, absent)
