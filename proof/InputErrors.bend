# Error classification by actual Input functions, before and after
# authentication. Hypotheses describe only local results;
# no codec law, Contract or environment is assumed or rejected.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Semantics.bend as S
import ../contract/Protocol.bend as P
import ../contract/Requirements.bend as R
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ../src/Input.bend as A
import ../src/State.bend as E
import ../src/Request.bend as Q
import ../src/Transport.bend as T
import ./InputMeasure.bend as Measure

law authenticate_pre_preserves_error_message:
  for -status: S.Status
  {A.authenticate_pre(A.ErrorMessage{status}) == A.Rejected{status} : A.Analysis}
def authenticate_pre_preserves_error_message(status):
  {==}

law authenticate_pre_preserves_error_transport:
  {A.authenticate_pre(A.ErrorTransport{}) == A.TransportInvalid{} : A.Analysis}
def authenticate_pre_preserves_error_transport():
  {==}

law envelope_absent_and_input:
  for -state: D.State
  {A.envelope(None{}, state) == A.ErrorMessage{S.Input{}} : A.PreAuthentication}
def envelope_absent_and_input(state):
  {==}

law message_input_and_input:
  for -state: D.State
  {A.message(C.Input{}, state) == A.ErrorMessage{S.Input{}} : A.PreAuthentication}
def message_input_and_input(state):
  {==}

law message_limit_internal_and_input:
  for -state: D.State
  {A.message(C.Limit{}, state) == A.ErrorMessage{S.Input{}} : A.PreAuthentication}
def message_limit_internal_and_input(state):
  {==}

law message_without_envelope_and_input:
  for +value: D.Value
  for +state: D.State
  for absent: {Q.extract(value) == None{} : Maybe<&2, P.Request>}
  {A.message(C.Decoded{value}, state) == A.ErrorMessage{S.Input{}} : A.PreAuthentication}
def message_without_envelope_and_input(value, state, absent):
  Equal.cong(Maybe<&2, P.Request>, A.PreAuthentication,
    r => A.envelope(r, state), Q.extract(value), None{}, absent)

law message_bytes_input:
  for +bytes: List<&2, U32>
  for body: B.Number64
  for +limit: B.Number64
  for +state: D.State
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, limit) == True{} : Bool}
  for refused: {C.decode(bytes, limit) == C.Input{} : C.Outcome}
  {A.read_message(Some{limit}, bytes, state) == A.ErrorMessage{S.Input{}} : A.PreAuthentication}
def message_bytes_input(bytes, body, limit, state, measured, fits, refused):
  %refused : {A.read_message(Some{limit}, bytes, state) == A.message(_, state) : A.PreAuthentication}
  Measure.body_admitted_preserves_result_of_codec(bytes, body, limit, state, measured, fits)

law message_bytes_limit_internal_admitted:
  for +bytes: List<&2, U32>
  for body: B.Number64
  for +limit: B.Number64
  for +state: D.State
  for measured: {B.nat64(B.length(bytes)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, limit) == True{} : Bool}
  for refused: {C.decode(bytes, limit) == C.Limit{} : C.Outcome}
  {A.read_message(Some{limit}, bytes, state) == A.ErrorMessage{S.Input{}} : A.PreAuthentication}
def message_bytes_limit_internal_admitted(bytes, body, limit, state, measured, fits, refused):
  Measure.limit_internal_in_body_admitted_and_input(bytes, body, limit, state, measured, fits, refused)

law message_bytes_without_envelope:
  for +bytes: List<&2, U32>
  for +limit: B.Number64
  for +value: D.Value
  for +state: D.State
  for +read: {C.decode(bytes, limit) == C.Decoded{value} : C.Outcome}
  for absent: {Q.extract(value) == None{} : Maybe<&2, P.Request>}
  {A.read_message(Some{limit}, bytes, state) == A.ErrorMessage{S.Input{}} : A.PreAuthentication}
def message_bytes_without_envelope(bytes, limit, value, state, read, absent):
  %absent : {A.read_message(Some{limit}, bytes, state) == A.envelope(_, state) : A.PreAuthentication}
  %read : {A.read_message(Some{limit}, bytes, state) == A.message(_, state) : A.PreAuthentication}
  Measure.decoding_accepts_preserves_message(bytes, limit, state, value, read)

law state_input_and_error_transport:
  for -schema: D.Schema
  for -body: List<&2, U32>
  for -limit: Maybe<&2, B.Number64>
  {A.state_decoded(C.Input{}, schema, body, limit) == A.ErrorTransport{} : A.PreAuthentication}
def state_input_and_error_transport(schema, body, limit):
  {==}

law state_limit_and_error_transport:
  for -schema: D.Schema
  for -body: List<&2, U32>
  for -limit: Maybe<&2, B.Number64>
  {A.state_decoded(C.Limit{}, schema, body, limit) == A.ErrorTransport{} : A.PreAuthentication}
def state_limit_and_error_transport(schema, body, limit):
  {==}

law state_absent_and_error_transport:
  for -body: List<&2, U32>
  for -limit: Maybe<&2, B.Number64>
  {A.state_read(None{}, body, limit) == A.ErrorTransport{} : A.PreAuthentication}
def state_absent_and_error_transport(body, limit):
  {==}

law state_value_invalid_and_error_transport:
  for +value: D.Value
  for +schema: D.Schema
  for +body: List<&2, U32>
  for +limit: Maybe<&2, B.Number64>
  for invalid: {E.decode(value, schema) == None{} : Maybe<&2, D.State>}
  {A.state_decoded(C.Decoded{value}, schema, body, limit) == A.ErrorTransport{} : A.PreAuthentication}
def state_value_invalid_and_error_transport(value, schema, body, limit, invalid):
  Equal.cong(Maybe<&2, D.State>, A.PreAuthentication,
    s => A.state_read(s, body, limit), E.decode(value, schema), None{}, invalid)

law limit_state_absent_and_error_transport:
  for -schema: D.Schema
  for -state: List<&2, U32>
  for -body: List<&2, U32>
  for -limit_msg: Maybe<&2, B.Number64>
  {A.read_state(None{}, schema, state, body, limit_msg) == A.ErrorTransport{} : A.PreAuthentication}
def limit_state_absent_and_error_transport(schema, state, body, limit_msg):
  {==}

law limit_message_absent_and_error_transport:
  for -body: List<&2, U32>
  for -state: D.State
  {A.read_message(None{}, body, state) == A.ErrorTransport{} : A.PreAuthentication}
def limit_message_absent_and_error_transport(body, state):
  {==}

# Absence of the message limit yields invalid transport even when the
# state fails earlier. This classification is not replaced by S.Limit.
law state_read_without_limit_message:
  for state: Maybe<&2, D.State>
  for -body: List<&2, U32>
  {A.state_read(state, body, None{}) == A.ErrorTransport{} : A.PreAuthentication}
def state_read_without_limit_message(state, body):
  match state:
    case None{}:
      {==}
    case Some{s}:
      {==}

law state_decoded_without_limit_message:
  for result: C.Outcome
  for +schema: D.Schema
  for +body: List<&2, U32>
  {A.state_decoded(result, schema, body, None{}) == A.ErrorTransport{} : A.PreAuthentication}
def state_decoded_without_limit_message(result, schema, body):
  match result:
    case C.Input{}:
      {==}
    case C.Limit{}:
      {==}
    case C.Decoded{v}:
      state_read_without_limit_message(E.decode(v, schema), body)

law read_state_without_limit_message:
  for limit: Maybe<&2, B.Number64>
  for +schema: D.Schema
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  {A.read_state(limit, schema, state, body, None{}) == A.ErrorTransport{} : A.PreAuthentication}
def read_state_without_limit_message(limit, schema, state, body):
  match limit:
    case None{}:
      {==}
    case Some{n}:
      state_decoded_without_limit_message(C.decode(state, n), schema, body)

law parts_without_limit_state:
  for parts: Maybe<&2, T.Parts>
  for +schema: D.Schema
  for +limits: S.Limits
  for absent: {B.nat64(R.limit_state(limits)) == None{} : Maybe<&2, B.Number64>}
  {A.parts(parts, schema, limits) == A.ErrorTransport{} : A.PreAuthentication}
def parts_without_limit_state(parts, schema, limits, absent):
  match parts:
    case None{}:
      {==}
    case Some{T.Parts{state, body}}:
      Equal.cong(Maybe<&2, B.Number64>, A.PreAuthentication,
        n => A.read_state(n, schema, state, body, B.nat64(R.limit_message(limits))),
        B.nat64(R.limit_state(limits)), None{}, absent)

law parts_without_limit_message:
  for parts: Maybe<&2, T.Parts>
  for +schema: D.Schema
  for +limits: S.Limits
  for absent: {B.nat64(R.limit_message(limits)) == None{} : Maybe<&2, B.Number64>}
  {A.parts(parts, schema, limits) == A.ErrorTransport{} : A.PreAuthentication}
def parts_without_limit_message(parts, schema, limits, absent):
  match parts:
    case None{}:
      {==}
    case Some{T.Parts{+state, +body}}:
      Equal.trans(A.PreAuthentication, A.parts(Some{T.Parts{state, body}}, schema, limits),
        A.read_state(B.nat64(R.limit_state(limits)), schema, state, body, None{}), A.ErrorTransport{},
        Equal.cong(Maybe<&2, B.Number64>, A.PreAuthentication,
          n => A.read_state(B.nat64(R.limit_state(limits)), schema, state, body, n),
          B.nat64(R.limit_message(limits)), None{}, absent),
        read_state_without_limit_message(B.nat64(R.limit_state(limits)), schema, state, body))

# Pipeline factorizations: conclusions still call the actual next-stage
# functions rather than postulating the final classification.
law decode_state_separate:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling: B.Number64
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured: {B.nat64(R.limit_state(limits)) == Some{ceiling} : Maybe<&2, B.Number64>}
  {A.decode(bytes, schema, limits) ==
    A.state_decoded(C.decode(state, ceiling), schema, body,
      B.nat64(R.limit_message(limits))) : A.PreAuthentication}
def decode_state_separate(bytes, schema, limits, state, body, ceiling, separate, measured):
  %measured : {A.decode(bytes, schema, limits) ==
    A.read_state(_, schema, state, body, B.nat64(R.limit_message(limits))) : A.PreAuthentication}
  %separate : {A.decode(bytes, schema, limits) == A.parts(_, schema, limits) : A.PreAuthentication}
  {==}

law decode_state_read:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling: B.Number64
  for +value: D.Value
  for +s: D.State
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured: {B.nat64(R.limit_state(limits)) == Some{ceiling} : Maybe<&2, B.Number64>}
  for read: {C.decode(state, ceiling) == C.Decoded{value} : C.Outcome}
  for extracted: {E.decode(value, schema) == Some{s} : Maybe<&2, D.State>}
  {A.decode(bytes, schema, limits) ==
    A.read_message(B.nat64(R.limit_message(limits)), body, s) : A.PreAuthentication}
def decode_state_read(bytes, schema, limits, state, body, ceiling, value, s,
  separate, measured, read, extracted):
  %extracted : {A.decode(bytes, schema, limits) ==
    A.state_read(_, body, B.nat64(R.limit_message(limits))) : A.PreAuthentication}
  %read : {A.decode(bytes, schema, limits) ==
    A.state_decoded(_, schema, body, B.nat64(R.limit_message(limits))) : A.PreAuthentication}
  decode_state_separate(bytes, schema, limits, state, body, ceiling, separate, measured)

# Analysis authenticates exactly the decoding result.
# Combines both equalities without repeating transport for every error case.
def combined_authentication(+pre: A.PreAuthentication, +result: A.PreAuthentication,
  +equal: {pre == result : A.PreAuthentication}) ->
  L.E<{pre == result : A.PreAuthentication},
    {A.authenticate_pre(pre) == A.authenticate_pre(result) : A.Analysis}>:
  L.Both{equal, Equal.cong(A.PreAuthentication, A.Analysis, A.authenticate_pre,
    pre, result, equal)}

# Each pipeline law supplies both exact outputs: decode and analyze.
law pipeline_transport_invalid:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for separate: {T.separate(bytes) == None{} : Maybe<&2, T.Parts>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def pipeline_transport_invalid(bytes, schema, limits, separate):
  +pre = Equal.cong(Maybe<&2, T.Parts>, A.PreAuthentication,
    p => A.parts(p, schema, limits), T.separate(bytes), None{}, separate)
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorTransport{}, pre)

law pipeline_limit_state_negative_representable:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for absent: {B.nat64(R.limit_state(limits)) == None{} : Maybe<&2, B.Number64>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def pipeline_limit_state_negative_representable(bytes, schema, limits, absent):
  +pre = parts_without_limit_state(T.separate(bytes), schema, limits, absent)
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorTransport{}, pre)

law pipeline_limit_message_negative_representable:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for absent: {B.nat64(R.limit_message(limits)) == None{} : Maybe<&2, B.Number64>}
  L.E<{A.decode(bytes, schema, limits) == A.ErrorTransport{} : A.PreAuthentication},
    {A.analyze(bytes, schema, limits) == A.TransportInvalid{} : A.Analysis}>
def pipeline_limit_message_negative_representable(bytes, schema, limits, absent):
  +pre = parts_without_limit_message(T.separate(bytes), schema, limits, absent)
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorTransport{}, pre)

law pipeline_state_input:
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
def pipeline_state_input(bytes, schema, limits, state, body, ceiling, separate, measured, refused):
  +pre = Equal.trans(A.PreAuthentication, A.decode(bytes, schema, limits),
    A.state_decoded(C.decode(state, ceiling), schema, body, B.nat64(R.limit_message(limits))),
    A.ErrorTransport{},
    decode_state_separate(bytes, schema, limits, state, body, ceiling, separate, measured),
    Equal.cong(C.Outcome, A.PreAuthentication,
      r => A.state_decoded(r, schema, body, B.nat64(R.limit_message(limits))),
      C.decode(state, ceiling), C.Input{}, refused))
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorTransport{}, pre)

law pipeline_state_limit:
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
def pipeline_state_limit(bytes, schema, limits, state, body, ceiling, separate, measured, refused):
  +pre = Equal.trans(A.PreAuthentication, A.decode(bytes, schema, limits),
    A.state_decoded(C.decode(state, ceiling), schema, body, B.nat64(R.limit_message(limits))),
    A.ErrorTransport{},
    decode_state_separate(bytes, schema, limits, state, body, ceiling, separate, measured),
    Equal.cong(C.Outcome, A.PreAuthentication,
      r => A.state_decoded(r, schema, body, B.nat64(R.limit_message(limits))),
      C.decode(state, ceiling), C.Limit{}, refused))
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorTransport{}, pre)

law pipeline_state_negative_extracted:
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
def pipeline_state_negative_extracted(bytes, schema, limits, state, body, ceiling, value,
  separate, measured, read, invalid):
  +pre = Equal.trans(A.PreAuthentication, A.decode(bytes, schema, limits),
    A.state_decoded(C.decode(state, ceiling), schema, body, B.nat64(R.limit_message(limits))),
    A.ErrorTransport{},
    decode_state_separate(bytes, schema, limits, state, body, ceiling, separate, measured),
    Equal.trans(A.PreAuthentication,
      A.state_decoded(C.decode(state, ceiling), schema, body, B.nat64(R.limit_message(limits))),
      A.state_decoded(C.Decoded{value}, schema, body, B.nat64(R.limit_message(limits))),
      A.ErrorTransport{},
      Equal.cong(C.Outcome, A.PreAuthentication,
        r => A.state_decoded(r, schema, body, B.nat64(R.limit_message(limits))),
        C.decode(state, ceiling), C.Decoded{value}, read),
      state_value_invalid_and_error_transport(value, schema, body, B.nat64(R.limit_message(limits)), invalid)))
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorTransport{}, pre)

# Factorization up to the body, including both original nat64 limits.
law decode_message_separate:
  for +bytes: List<&2, U32>
  for +schema: D.Schema
  for +limits: S.Limits
  for +state: List<&2, U32>
  for +body: List<&2, U32>
  for +ceiling_state: B.Number64
  for +ceiling_msg: B.Number64
  for +value_state: D.Value
  for +s: D.State
  for separate: {T.separate(bytes) == Some{T.Parts{state, body}} : Maybe<&2, T.Parts>}
  for measured_state: {B.nat64(R.limit_state(limits)) == Some{ceiling_state} : Maybe<&2, B.Number64>}
  for measured_msg: {B.nat64(R.limit_message(limits)) == Some{ceiling_msg} : Maybe<&2, B.Number64>}
  for read: {C.decode(state, ceiling_state) == C.Decoded{value_state} : C.Outcome}
  for extracted: {E.decode(value_state, schema) == Some{s} : Maybe<&2, D.State>}
  {A.decode(bytes, schema, limits) == A.read_message(Some{ceiling_msg}, body, s) : A.PreAuthentication}
def decode_message_separate(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, separate, measured_state, measured_msg, read, extracted):
  %measured_msg : {A.decode(bytes, schema, limits) == A.read_message(_, body, s) : A.PreAuthentication}
  decode_state_read(bytes, schema, limits, state, body, ceiling_state, value_state, s,
    separate, measured_state, read, extracted)

law pipeline_message_input:
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
def pipeline_message_input(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, fits, refused):
  +pre = Equal.trans(A.PreAuthentication, A.decode(bytes, schema, limits),
    A.read_message(Some{ceiling_msg}, body, s), A.ErrorMessage{S.Input{}},
    decode_message_separate(bytes, schema, limits, state, body, ceiling_state,
      ceiling_msg, value_state, s, separate, measured_state, measured_msg, read, extracted),
    message_bytes_input(body, count, ceiling_msg, s, measured_body, fits, refused))
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorMessage{S.Input{}}, pre)

law pipeline_message_limit_internal_admitted:
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
def pipeline_message_limit_internal_admitted(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, fits, refused):
  +pre = Equal.trans(A.PreAuthentication, A.decode(bytes, schema, limits),
    A.read_message(Some{ceiling_msg}, body, s), A.ErrorMessage{S.Input{}},
    decode_message_separate(bytes, schema, limits, state, body, ceiling_state,
      ceiling_msg, value_state, s, separate, measured_state, measured_msg, read, extracted),
    message_bytes_limit_internal_admitted(body, count, ceiling_msg, s, measured_body, fits, refused))
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorMessage{S.Input{}}, pre)

# Excess is based on actual received quantity, regardless of codec.
law pipeline_message_body_above_of_ceiling:
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
def pipeline_message_body_above_of_ceiling(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, count, separate, measured_state, measured_msg, read, extracted,
  measured_body, above):
  +pre = Equal.trans(A.PreAuthentication, A.decode(bytes, schema, limits),
    A.read_message(Some{ceiling_msg}, body, s), A.ErrorMessage{S.Limit{}},
    decode_message_separate(bytes, schema, limits, state, body, ceiling_state,
      ceiling_msg, value_state, s, separate, measured_state, measured_msg, read, extracted),
    Measure.body_real_above_of_ceiling_produces_limit(body, count, ceiling_msg, s, measured_body, above))
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorMessage{S.Limit{}}, pre)

law pipeline_envelope_invalid:
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
def pipeline_envelope_invalid(bytes, schema, limits, state, body, ceiling_state,
  ceiling_msg, value_state, s, value_msg, separate, measured_state, measured_msg, read_state,
  extracted, read_msg, absent):
  +pre = Equal.trans(A.PreAuthentication, A.decode(bytes, schema, limits),
    A.read_message(Some{ceiling_msg}, body, s), A.ErrorMessage{S.Input{}},
    decode_message_separate(bytes, schema, limits, state, body, ceiling_state,
      ceiling_msg, value_state, s, separate, measured_state, measured_msg, read_state, extracted),
    message_bytes_without_envelope(body, ceiling_msg, value_msg, s, read_msg, absent))
  combined_authentication(A.decode(bytes, schema, limits), A.ErrorMessage{S.Input{}}, pre)
