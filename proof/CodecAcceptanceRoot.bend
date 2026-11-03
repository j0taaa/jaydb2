# Soundness interfaces for induction: the path may start with
# arbitrary counters. Validity and canonicity are not new hidden premises
# of the public API; the first is derived from the path itself.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./Codec.bend as V
import ./CodecTrace.bend as R
import ./CodecWordsBE64.bend as H
import ./CodecTextAccepted.bend as T
import ./CodecPrimitives.bend as A
import ./CodecUTF8InverseText.bend as U
import ./CodecAcceptanceWord.bend as W

law execution_ready_has_execution_trace_accepted:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +m: C.Machine
  for -v: D.Value
  for ready: {R.machine(R.execute(bs, R.Frame{body, ceiling, m})) == C.DecodedReady{v} : C.Machine}
  {C.traverse(bs, body, ceiling, m) == C.Decoded{v} : C.Outcome}
def execution_ready_has_execution_trace_accepted(bs, body, ceiling, m, v, ready):
  Equal.trans(C.Outcome, C.traverse(bs, body, ceiling, m), R.finalize_frame(R.execute(bs, R.Frame{body, ceiling, m})), C.Decoded{v},
    R.execution_trace_and_execution_integral(bs, R.Frame{body, ceiling, m}),
    Equal.cong(C.Machine, C.Outcome, x => C.finalize(x), R.machine(R.execute(bs, R.Frame{body, ceiling, m})), C.DecodedReady{v}, ready))

law execution_root_accepts_guarantees_value_valid:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for ready: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.Tag{C.Root{}}})) == C.DecodedReady{v} : C.Machine}
  {D.value_valid(v) == True{} : Bool}
def execution_root_accepts_guarantees_value_valid(bs, body, ceiling, v, ready):
  %execution_ready_has_execution_trace_accepted(bs, body, ceiling, C.Tag{C.Root{}}, v, ready) : V.ResultValid(_)
  V.traverse_preserves_validity(bs, body, ceiling, C.Tag{C.Root{}}, Unit{})

law check_accepts_and_fits:
  for c: C.Check
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for +f: C.Purpose
  for +n: B.Number64
  for +p: C.Stack
  for -v: D.Value
  for ready: {R.machine(R.execute(bs, R.Frame{body, ceiling, C.open_checked(c, f, n, p)})) == C.DecodedReady{v} : C.Machine}
  {c == C.Fits{} : C.Check}
def check_accepts_and_fits(c, bs, body, ceiling, f, n, p, v, ready):
  match c:
    case C.Fits{}:
      {==}
    case C.Short{}:
      L.ex_false({C.Short{} == C.Fits{} : C.Check}, R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{}, C.traverse(bs, body, ceiling, C.Invalid{}), C.Decoded{v},
          Equal.sym(C.Outcome, C.traverse(bs, body, ceiling, C.Invalid{}), C.Input{}, R.invalid_absorbs_all_suffix(bs, body, ceiling)),
          execution_ready_has_execution_trace_accepted(bs, body, ceiling, C.Invalid{}, v, ready))))
    case C.Large{}:
      L.ex_false({C.Large{} == C.Fits{} : C.Check}, R.limit_negative_decoded(v,
        Equal.trans(C.Outcome, C.Limit{}, C.traverse(bs, body, ceiling, C.Above{}), C.Decoded{v},
          Equal.sym(C.Outcome, C.traverse(bs, body, ceiling, C.Above{}), C.Limit{}, R.above_absorbs_all_suffix(bs, body, ceiling)),
          execution_ready_has_execution_trace_accepted(bs, body, ceiling, C.Above{}, v, ready))))

def integer_extracted_and_canonical(+bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  extracted: W.WordExtracted<bs, C.Integer{}, C.Root{}, body, ceiling, v>) -> P.Encoding(v, Con{3, bs}):
  match extracted:
    case W.Extracted{a, b, c, d, e, f0, g, h, +suf, +high, +low, factoring, octets, rest_valid, number, be64, +factoring_be64, frame, execution, ready}:
      F.combined_pair(P.Encoding(v, Con{3, bs}), {suf == Nil{} : List<&2, U32>}, {v == D.VInt{high, low} : D.Value},
        A.ready_accepted_requires_suffix_empty_and_value_exact(suf, H.decrease(8n, body), H.decrease(8n, ceiling), D.VInt{high, low}, v,
          execution_ready_has_execution_trace_accepted(suf, H.decrease(8n, body), H.decrease(8n, ceiling), C.DecodedReady{D.VInt{high, low}}, v, ready)),
        end => value =>
          (%Equal.sym(D.Value, v, D.VInt{high, low}, value) : P.Encoding(_, Con{3, bs})
           %Equal.sym(List<&2, U32>, bs, B.concatenate(B.be64(high, low), suf), factoring_be64) : P.Encoding(D.VInt{high, low}, Con{3, _})
           %Equal.sym(List<&2, U32>, suf, Nil{}, end) : P.Encoding(D.VInt{high, low}, Con{3, B.concatenate(B.be64(high, low), _)})
           %Equal.sym(List<&2, U32>, B.concatenate(B.be64(high, low), Nil{}), B.be64(high, low), U.concatenate_empty_right(B.be64(high, low))) :
             P.Encoding(D.VInt{high, low}, Con{3, _})
           {==}))

law integer_combined_execution_real_and_canonical:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for ready: {R.machine(R.execute(bs, W.start(C.Integer{}, C.Root{}, body, ceiling))) == C.DecodedReady{v} : C.Machine}
  P.Encoding(v, Con{3, bs})
def integer_combined_execution_real_and_canonical(bs, body, ceiling, v, all_valid, ready):
  integer_extracted_and_canonical(bs, body, ceiling, v,
    W.word_accepts_extracts_be64_and_execution_remaining(bs, C.Integer{}, C.Root{}, body, ceiling, v, all_valid, ready))

def text_extracted_and_canonical(+bs: List<&2, U32>, +body: B.Number64, +ceiling: B.Number64, -v: D.Value,
  valid: {D.value_valid(v) == True{} : Bool},
  extracted: W.WordExtracted<bs, C.TextValue{}, C.Root{}, body, ceiling, v>) -> P.Encoding(v, Con{4, bs}):
  match extracted:
    case W.Extracted{+a, +b, +c, +d, +e, +f0, +g, +h, +suf, high, low, +factoring, +octets, rest_valid, number, be64, factoring_be64, frame, execution, ready}:
      %Equal.sym(List<&2, U32>, bs, B.concatenate([a, b, c, d, e, f0, g, h], suf), factoring) : P.Encoding(v, Con{4, _})
      T.reencode_text_combined_header(a, b, c, d, e, f0, g, h, suf, v, valid, octets,
        T.analyze_header_textual(a, b, c, d, e, f0, g, h, suf, body, ceiling, v, octets,
          execution_ready_has_execution_trace_accepted(B.concatenate([a, b, c, d, e, f0, g, h], suf), body, ceiling, C.WordInput{C.TextValue{}, 7n, 0, 0, C.Root{}}, v,
            (%factoring : {R.machine(R.execute(_, W.start(C.TextValue{}, C.Root{}, body, ceiling))) == C.DecodedReady{v} : C.Machine}
              Equal.trans(C.Machine, R.machine(R.execute(bs, W.start(C.TextValue{}, C.Root{}, body, ceiling))),
                R.machine(R.execute(suf, W.after_word(C.TextValue{}, high, low, C.Root{}, body, ceiling))), C.DecodedReady{v},
                Equal.cong(R.Frame, C.Machine, q => R.machine(q), R.execute(bs, W.start(C.TextValue{}, C.Root{}, body, ceiling)),
                  R.execute(suf, W.after_word(C.TextValue{}, high, low, C.Root{}, body, ceiling)),
                  Equal.sym(R.Frame, R.execute(suf, W.after_word(C.TextValue{}, high, low, C.Root{}, body, ceiling)),
                    R.execute(bs, W.start(C.TextValue{}, C.Root{}, body, ceiling)), execution)), ready)))))

law text_combined_execution_real_and_canonical:
  for +bs: List<&2, U32>
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for valid: {D.value_valid(v) == True{} : Bool}
  for all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  for ready: {R.machine(R.execute(bs, W.start(C.TextValue{}, C.Root{}, body, ceiling))) == C.DecodedReady{v} : C.Machine}
  P.Encoding(v, Con{4, bs})
def text_combined_execution_real_and_canonical(bs, body, ceiling, v, valid, all_valid, ready):
  text_extracted_and_canonical(bs, body, ceiling, v, valid,
    W.word_accepts_extracts_be64_and_execution_remaining(bs, C.TextValue{}, C.Root{}, body, ceiling, v, all_valid, ready))
