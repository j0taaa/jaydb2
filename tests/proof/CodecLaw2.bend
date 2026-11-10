# Every representable body is arbitrary: includes malformed inputs,
# invalid Unicode, false counts, unordered names and extra suffixes.
import Base
import ../../contract/Bytes.bend as B
import ../../contract/RequestFacts.bend as I
import ../../src/Codec.bend as C
import ../../proof/CodecLaw2.bend as G
import ../../proof/CodecRefusals.bend as R
import ../../proof/CodecMinimum.bend as M

law any_body_in_limit_exact_satisfies_relation_original:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  I.DecodingCorrect(bs, R.optional(C.decode(bs, body)))
def any_body_in_limit_exact_satisfies_relation_original(bs, body, measured):
  G.decode_satisfies_relation_original(bs, body, body, measured, M.less_equal64_reflexive(body))
