# REJECTION direction of the original Interface relation. For admissible
# bodies, Input/Limit exclude every canonical encoding,
# by general completeness for all values, without structural limits.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Interface.bend as I
import ../src/Codec.bend as C
import ./CodecComplete.bend as G
import ./CodecTrace.bend as R

def optional(r: C.Outcome) -> Maybe<&2, D.Value>:
  match r:
    case C.Decoded{v}:
      Some{v}
    case C.Input{}:
      None{}
    case C.Limit{}:
      None{}

law input_of_body_admissible_excludes_encoding:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for refused: {C.decode(bs, ceiling) == C.Input{} : C.Outcome}
  I.DecodingCorrect(bs, None{})
def input_of_body_admissible_excludes_encoding(bs, body, ceiling, measured, fits, refused):
  v => encoded =>
    R.input_negative_decoded(v, Equal.trans(C.Outcome,
      C.Input{}, C.decode(bs, ceiling), C.Decoded{v},
      Equal.sym(C.Outcome, C.decode(bs, ceiling), C.Input{}, refused),
      G.all_encoding_canonical_representable_and_decoded(v, bs, body, ceiling, encoded, measured, fits)))

law limit_of_body_admissible_excludes_encoding:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  for refused: {C.decode(bs, ceiling) == C.Limit{} : C.Outcome}
  I.DecodingCorrect(bs, None{})
def limit_of_body_admissible_excludes_encoding(bs, body, ceiling, measured, fits, refused):
  v => encoded =>
    R.limit_negative_decoded(v, Equal.trans(C.Outcome,
      C.Limit{}, C.decode(bs, ceiling), C.Decoded{v},
      Equal.sym(C.Outcome, C.decode(bs, ceiling), C.Limit{}, refused),
      G.all_encoding_canonical_representable_and_decoded(v, bs, body, ceiling, encoded, measured, fits)))
