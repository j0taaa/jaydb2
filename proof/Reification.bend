# Arguments inserted into source are exactly the received values,
# regardless of width/depth, without nested textual constructors.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../src/Codec.bend as C
import ../src/Reification.bend as R
import ./CodecComplete.bend as G
import ./CodecMinimum.bend as M

law text_of_octets_has_inverse_exact:
  for +bs: List<&2, U32>
  {R.octets(R.text(bs)) == bs : List<&2, U32>}
def text_of_octets_has_inverse_exact(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, +rest}:
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{b, xs}, R.octets(R.text(rest)), rest,
        text_of_octets_has_inverse_exact(rest))

law reification_canonical_decodes_exactly_o_argument:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +high: U32
  for +low: U32
  for encoded: P.Encoding(v, bs)
  for measured: {B.nat64(B.length(bs)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {R.decode(R.text(bs), high, low) == Some{v} : Maybe<&2, D.Value>}
def reification_canonical_decodes_exactly_o_argument(v, bs, high, low, encoded, measured):
  %Equal.sym(List<&2, U32>, R.octets(R.text(bs)), bs, text_of_octets_has_inverse_exact(bs)) :
    {R.extract(C.decode(_, B.Number64{high, low})) == Some{v} : Maybe<&2, D.Value>}
  Equal.cong(C.Outcome, Maybe<&2, D.Value>, R.extract,
    C.decode(bs, B.Number64{high, low}), C.Decoded{v},
    G.all_encoding_canonical_representable_and_decoded(v, bs, B.Number64{high, low}, B.Number64{high, low},
      encoded, measured, M.less_equal64_reflexive(B.Number64{high, low})))

law source_of_arguments_recovers_o_value_without_fallback:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +high: U32
  for +low: U32
  for encoded: P.Encoding(v, bs)
  for measured: {B.nat64(B.length(bs)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {R.arguments(R.text(bs), high, low) == v : D.Value}
def source_of_arguments_recovers_o_value_without_fallback(v, bs, high, low, encoded, measured):
  Equal.cong(Maybe<&2, D.Value>, D.Value, R.value,
    R.decode(R.text(bs), high, low), Some{v},
    reification_canonical_decodes_exactly_o_argument(v, bs, high, low, encoded, measured))
