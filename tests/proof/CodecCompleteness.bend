# The including boundary is verified for EVERY canonical value,
# including arbitrarily nested lists/records, without fixed examples.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/Data.bend as D
import ../../contract/Protocol.bend as P
import ../../src/Codec.bend as C
import ../../proof/CodecComplete.bend as G
import ../../proof/CodecMinimum.bend as M

law any_encoding_representable_and_accepts_in_limit_exact:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +body: B.Number64
  for encoded: P.Encoding(v, bs)
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  {C.decode(bs, body) == C.Decoded{v} : C.Outcome}
def any_encoding_representable_and_accepts_in_limit_exact(v, bs, body, encoded, measured):
  G.all_encoding_canonical_representable_and_decoded(v, bs, body, body, encoded, measured, M.less_equal64_reflexive(body))
