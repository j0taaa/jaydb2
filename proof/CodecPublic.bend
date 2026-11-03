# Root specialization of the local property. This lemma is an induction
# combinator: by itself it does not assert the local property of every Value.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../src/Codec.bend as C
import ./CodecTrace.bend as R
import ./CodecComposition.bend as X
import ./CodecSequences.bend as S
import ./CodecOctets.bend as O
import ./CodecUTF8InverseText.bend as U

law completeness_local_canonical_implies_acceptance_publish:
  for +v: D.Value
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for complete: S.CompleteLocal(v, bs)
  for encoded: P.Encoding(v, bs)
  for +measured: {B.nat64(B.length(bs)) == Some{body} : Maybe<&2, B.Number64>}
  for +fits: {C.less_equal64(body, ceiling) == True{} : Bool}
  {C.decode(bs, ceiling) == C.Decoded{v} : C.Outcome}
def completeness_local_canonical_implies_acceptance_publish(v, bs, body, ceiling, complete, encoded, measured, fits):
  octets = O.any_encoding_only_emits_octets(v, bs, encoded)
  measure_suffix = {(%Equal.sym(List<&2, U32>, B.concatenate(bs, Nil{}), bs, U.concatenate_empty_right(bs)) :
    {B.nat64(B.length(_)) == Some{body} : Maybe<&2, B.Number64>}
    measured) : {B.nat64(B.length(B.concatenate(bs, Nil{}))) == Some{body} : Maybe<&2, B.Number64>}}
  execution = complete(body, ceiling, C.Root{}, Nil{}, 0n, {==}, {==}, measure_suffix, fits)
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bs)), Some{body}, measured) :
    {C.decode_measure(_, bs, ceiling) == C.Decoded{v} : C.Outcome}
  %Equal.sym(Bool, C.less_equal64(body, ceiling), True{}, fits) :
    {C.decode_size(_, bs, body, ceiling) == C.Decoded{v} : C.Outcome}
  %Equal.sym(Bool, B.octets_all_valid(bs), True{}, octets) :
    {C.decode_octets(_, bs, body, ceiling) == C.Decoded{v} : C.Outcome}
  Equal.trans(C.Outcome,
    C.traverse(bs, body, ceiling, C.Tag{C.Root{}}), R.finalize_frame(R.execute(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}})), C.Decoded{v},
    R.execution_trace_and_execution_integral(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}}),
    Equal.cong(R.Frame, C.Outcome, q => R.finalize_frame(q), R.execute(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}}), X.later(bs, body, ceiling, C.DecodedReady{v}), execution))
