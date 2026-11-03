import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../src/Reification.bend as R
import ../../proof/Reification.bend as G

law all_argument_canonical_reified_preserves_o_value:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +high: U32
  for +low: U32
  for encoded: P.Encoding(v, bs)
  for measured: {B.nat64(B.length(bs)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {R.arguments(R.text(bs), high, low) == v : D.Value}
def all_argument_canonical_reified_preserves_o_value(v, bs, high, low, encoded, measured):
  G.source_of_arguments_recovers_o_value_without_fallback(v, bs, high, low, encoded, measured)
