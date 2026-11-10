# Links actual Codec to the ORIGINAL Interface/Protocol relation.
# No chosen Environment or Law2/Contract premise. This module handles
# the encoding part of Law2; observable host facts belong to the caller.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/RequestFacts.bend as I
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Codec.bend as V
import ./CodecAcceptance.bend as A
import ./CodecComplete.bend as G
import ./CodecRefusals.bend as R

law acceptance_reconstitutes_encoding_original_and_validity:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for +v: D.Value
  for +accepted: {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
  L.E<P.Encoding(v, bs), {D.value_valid(v) == True{} : Bool}>
def acceptance_reconstitutes_encoding_original_and_validity(bs, ceiling, v, accepted):
  L.Both{A.all_acceptance_publish_has_encoding_canonical(bs, ceiling, v, accepted),
    V.decode_only_returns_value_valid(bs, ceiling, v, accepted)}

def relation_of_result(r: C.Outcome, +bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64,
  measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>},
  fits: {C.less_equal64(body, ceiling) == True{} : Bool},
  result: {C.decode(bs, ceiling) == r : C.Outcome}) -> I.DecodingCorrect(bs, R.optional(r)):
  match r:
    case C.Decoded{+v}:
      A.all_acceptance_publish_has_encoding_canonical(bs, ceiling, v, result)
    case C.Input{}:
      R.input_of_body_admissible_excludes_encoding(bs, body, ceiling, measured, fits, result)
    case C.Limit{}:
      R.limit_of_body_admissible_excludes_encoding(bs, body, ceiling, measured, fits, result)

# Some returns the EXACT encoding; None excludes every possible encoding.
# Measure and ceiling are actual received-body bounds, without a new quota.
law decode_satisfies_relation_original:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  I.DecodingCorrect(bs, R.optional(C.decode(bs, ceiling)))
def decode_satisfies_relation_original(bs, body, ceiling, measured, fits):
  relation_of_result(C.decode(bs, ceiling), bs, body, ceiling, measured, fits, {==})

law encoding_and_acceptance_equivalent_in_body_admissible:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  L.E<
    ({C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome} -> P.Encoding(v, bs)),
    (P.Encoding(v, bs) -> {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome})>
def encoding_and_acceptance_equivalent_in_body_admissible(v, bs, body, ceiling, measured, fits):
  L.Both{
    accepted => A.all_acceptance_publish_has_encoding_canonical(bs, ceiling, v, accepted),
    encoded => G.all_encoding_canonical_representable_and_decoded(v, bs, body, ceiling, encoded, measured, fits)}
