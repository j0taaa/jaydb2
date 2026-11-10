# Actual byte decoder -> exact full physical ordinary/prepared reception.
# No Received, normalized raw request, codec output or final service outcome
# is a premise. Accepted canonical encoding is derived from InputRelations;
# unstripping proves the actual tag/opcode bytes, not a fabricated body.
import Base
import ../../../../contract/Bytes.bend as B
import ../../../../contract/Data.bend as D
import ../../../../contract/Logic.bend as L
import ../../../../contract/PreparedProtocol.bend as W
import ../../../../contract/Protocol.bend as P
import ../../../../contract/Requirements.bend as R
import ../../../../contract/Resources.bend as X
import ../../../../contract/Semantics.bend as S
import ../../../../src/Input.bend as Input
import ../../../InputRelations.bend as Relation
import ../../../../library/ComparisonProofs.bend as EqualWord
import ../../model/serial/Decode.bend as Decode

def MessageEncoding(pre: Input.PreAuthentication, +bytes: List<&2, U32>) -> Type:
  match pre:
    case Input.InputReady{state, request}: P.Encoding(P.request_value(request), bytes)
    case _: Unit

def message_encoding(pre: Input.PreAuthentication, -origin: D.State, +bytes: List<&2, U32>, -limit: Maybe<&2, B.Number64>,
  actual: Relation.LimitMessageFaithful(pre, origin, bytes, limit)) -> MessageEncoding(pre, bytes):
  match pre:
    case Input.InputReady{state, request}:
      match actual:
        case (ceiling, L.Both{limit_same, L.Both{state_same, L.Both{codec, L.Both{canonical, valid}}}}): canonical
    case Input.ErrorMessage{status}: Unit{}
    case Input.ErrorTransport{}: Unit{}

def wrapped(operation: Maybe<&2, W.Operation>, bytes: List<&2, U32>) -> List<&2, U32>:
  match operation:
    case None{}: bytes
    case Some{operation}: Con{7, Con{W.opcode(operation), bytes}}

def BodyFaithful(decision: Decode.Decision, +bytes: List<&2, U32>) -> Type:
  match decision:
    case Decode.Parsed{wire}: W.BodyEncoding(wire, bytes)
    case _: Unit

def message_body(operation: Maybe<&2, W.Operation>, pre: Input.PreAuthentication, +bytes: List<&2, U32>,
  encoded: MessageEncoding(pre, bytes)) -> BodyFaithful(Decode.message(operation, pre), wrapped(operation, bytes)):
  match operation pre:
    case None{} Input.InputReady{state, request}: encoded
    case Some{operation} Input.InputReady{state, request}: W.extension_body_encoding(operation, request, bytes, encoded)
    case None{} Input.ErrorMessage{status}: Unit{}
    case Some{operation} Input.ErrorMessage{status}: Unit{}
    case None{} Input.ErrorTransport{}: Unit{}
    case Some{operation} Input.ErrorTransport{}: Unit{}

def limited_body(limit: Maybe<&2, B.Number64>, +current: D.State, +operation: Maybe<&2, W.Operation>, +bytes: List<&2, U32>) ->
  BodyFaithful(Decode.decision(Decode.limited(limit, current, operation, bytes)), wrapped(operation, bytes)):
  match limit:
    case None{}: Unit{}
    case Some{+ceiling}:
      message_body(operation, Input.read_message(Some{ceiling}, bytes, current), bytes,
        message_encoding(Input.read_message(Some{ceiling}, bytes, current), current, bytes, Some{ceiling},
          Relation.read_message_faithful(Some{ceiling}, bytes, current)))

def Unstripped(route: W.Dispatch, +full: List<&2, U32>) -> Type:
  match route:
    case W.OrdinaryBody{bytes}: {bytes == full : List<&2, U32>}
    case W.ExtensionBody{operation, bytes}: {full == Con{7, Con{W.opcode(operation), bytes}} : List<&2, U32>}
    case W.InvalidExtension{}: Unit

def opcode_matches(+operation: U32, +bytes: List<&2, U32>, zero: Bool, one: Bool, two: Bool, three: Bool,
  ez: {U32.is_eq(operation, 0) == zero : Bool}, eo: {U32.is_eq(operation, 1) == one : Bool},
  et: {U32.is_eq(operation, 2) == two : Bool}, eh: {U32.is_eq(operation, 3) == three : Bool}) ->
  Unstripped(W.dispatch_opcode(zero, one, two, three, bytes), Con{7, Con{operation, bytes}}):
  match zero one two three:
    case True{} _ _ _:
      %Equal.sym(U32, operation, 0, EqualWord.u32_equal_sound(operation, 0, ez)) :
        Unstripped(W.ExtensionBody{W.Prepare{}, bytes}, Con{7, Con{_, bytes}})
      {==}
    case False{} True{} _ _:
      %Equal.sym(U32, operation, 1, EqualWord.u32_equal_sound(operation, 1, eo)) :
        Unstripped(W.ExtensionBody{W.Execute{}, bytes}, Con{7, Con{_, bytes}})
      {==}
    case False{} False{} True{} _:
      %Equal.sym(U32, operation, 2, EqualWord.u32_equal_sound(operation, 2, et)) :
        Unstripped(W.ExtensionBody{W.Invalidate{}, bytes}, Con{7, Con{_, bytes}})
      {==}
    case False{} False{} False{} True{}:
      %Equal.sym(U32, operation, 3, EqualWord.u32_equal_sound(operation, 3, eh)) :
        Unstripped(W.ExtensionBody{W.PrepareRead{}, bytes}, Con{7, Con{_, bytes}})
      {==}
    case False{} False{} False{} False{}: Unit{}

def strip_matches(+bytes: List<&2, U32>) -> Unstripped(W.strip_extension(bytes), Con{7, bytes}):
  match bytes:
    case Nil{}: Unit{}
    case Con{+operation, +body}:
      opcode_matches(operation, body, U32.is_eq(operation, 0), U32.is_eq(operation, 1), U32.is_eq(operation, 2), U32.is_eq(operation, 3), {==}, {==}, {==}, {==})

def tag_matches(extension: Bool, +tag: U32, +rest: List<&2, U32>, same: {U32.is_eq(tag, 7) == extension : Bool}) ->
  Unstripped(W.dispatch_tag(extension, tag, rest), Con{tag, rest}):
  match extension:
    case False{}: {==}
    case True{}:
      %Equal.sym(U32, tag, 7, EqualWord.u32_equal_sound(tag, 7, same)) : Unstripped(W.strip_extension(rest), Con{_, rest})
      strip_matches(rest)

law actual_routing_preserves_the_exact_full_body_and_recovers_each_extension_prefix:
  for +bytes: List<&2, U32>
  Unstripped(W.route_dispatch(bytes), bytes)
def actual_routing_preserves_the_exact_full_body_and_recovers_each_extension_prefix(bytes):
  match bytes:
    case Nil{}: {==}
    case Con{+tag, +rest}: tag_matches(U32.is_eq(tag, 7), tag, rest, {==})


def routed_body(~c: S.Configuration, +current: D.State, route: W.Dispatch, +full: List<&2, U32>, exact: Unstripped(route, full)) ->
  BodyFaithful(Decode.decision(Decode.routed(c, current, route)), full):
  match route:
    case W.OrdinaryBody{+bytes}:
      %exact : BodyFaithful(Decode.decision(Decode.limited(B.nat64(R.limit_message(S.limits(c))), current, None{}, bytes)), _)
      limited_body(B.nat64(R.limit_message(S.limits(c))), current, None{}, bytes)
    case W.ExtensionBody{+operation, +bytes}:
      %Equal.sym(List<&2, U32>, full, Con{7, Con{W.opcode(operation), bytes}}, exact) :
        BodyFaithful(Decode.decision(Decode.limited(B.nat64(R.limit_message(S.limits(c))), current, Some{operation}, bytes)), _)
      limited_body(B.nat64(R.limit_message(S.limits(c))), current, Some{operation}, bytes)
    case W.InvalidExtension{}: Unit{}

def ReceptionFaithful(~c: S.Configuration, -input: X.Reception, decision: Decode.Decision) -> Type:
  match decision:
    case Decode.Parsed{wire}: W.Received(c, input, wire)
    case _: Unit

def processed_body(~c: S.Configuration, +input: X.Reception, +full: List<&2, U32>, decision: Decode.Decision,
  valid: X.ReceptionValid(input), processing: {X.decide_reception(c, input) == X.ProcessBody{full} : X.Disposition},
  encoded: BodyFaithful(decision, full)) -> ReceptionFaithful(c, input, decision):
  match decision:
    case Decode.Parsed{wire}: L.Both{valid, (full, L.Both{processing, encoded})}
    case Decode.Shutdown{}: Unit{}
    case Decode.Reject{mode, status, closes}: Unit{}
    case Decode.TransportStopped{}: Unit{}

def disposed_reception(~c: S.Configuration, +current: D.State, +input: X.Reception, +disposition: X.Disposition,
  valid: X.ReceptionValid(input), actual: {X.decide_reception(c, input) == disposition : X.Disposition}) ->
  ReceptionFaithful(c, input, Decode.decision(Decode.disposed(c, current, disposition))):
  match disposition:
    case X.CloseWithoutResponse{}: Unit{}
    case X.RefuseClose{status}: Unit{}
    case X.RefuseContinue{status}: Unit{}
    case X.ProcessBody{+bytes}:
      processed_body(c, input, bytes, Decode.decision(Decode.routed(c, current, W.route_dispatch(bytes))), valid, actual,
        routed_body(c, current, W.route_dispatch(bytes), bytes, actual_routing_preserves_the_exact_full_body_and_recovers_each_extension_prefix(bytes)))

law every_actual_parsed_decision_has_its_exact_full_physical_reception:
  for ~c: S.Configuration
  for +current: D.State
  for +input: X.Reception
  for valid: X.ReceptionValid(input)
  ReceptionFaithful(c, input, Decode.decision(Decode.run(c, current, input)))
def every_actual_parsed_decision_has_its_exact_full_physical_reception(c, current, input, valid):
  disposed_reception(c, current, input, X.decide_reception(c, input), valid, {==})

law actual_decoding_of_either_wire_kind_derives_received_without_a_reception_encoding_premise:
  for ~c: S.Configuration
  for +current: D.State
  for +input: X.Reception
  for +wire: W.WireRequest
  for valid: X.ReceptionValid(input)
  for parsed: {Decode.decision(Decode.run(c, current, input)) == Decode.Parsed{wire} : Decode.Decision}
  W.Received(c, input, wire)
def actual_decoding_of_either_wire_kind_derives_received_without_a_reception_encoding_premise(c, current, input, wire, valid, parsed):
  %parsed : ReceptionFaithful(c, input, _)
  every_actual_parsed_decision_has_its_exact_full_physical_reception(c, current, input, valid)
