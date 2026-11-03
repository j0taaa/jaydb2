# GENERAL integer roundtrip and canonicity: all 2^64 bit patterns.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Protocol.bend as P
import ../contract/Logic.bend as L
import ../src/Codec.bend as C
import ./Foundations.bend as F
import ./Orders.bend as O
import ./CodecWordsWord.bend as W
import ./CodecWordsBE64.bend as H
import ./CodecWordsInverse.bend as I
import ./CodecUTF8Bits.bend as A
import ./CodecTrace.bend as R

law cmp_bit_until_maximum:
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_le(c) == True{} : Bool}
  {Cmp.is_le(Word.cmp.fin(b, True{}, c)) == True{} : Bool}
def cmp_bit_until_maximum(b, c, e):
  match b c:
    case False{} EQ{}:
      {==}
    case False{} LT{}:
      {==}
    case True{} EQ{}:
      {==}
    case True{} LT{}:
      {==}
    case False{} GT{}:
      F.absurd_boolean({False{} == True{} : Bool}, e)
    case True{} GT{}:
      F.absurd_boolean({False{} == True{} : Bool}, e)

law word_until_maximum:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_le(Word.cmp(n, w, W.ones(n))) == True{} : Bool}
def word_until_maximum(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, +t}:
          cmp_bit_until_maximum(b, Word.cmp(p, t, W.ones(p)), word_until_maximum(p, t))

law all_octet_formed_fits_in_255:
  for +w: Word(8n)
  {U32.is_le(H.octet(w), 255) == True{} : Bool}
def all_octet_formed_fits_in_255(w):
  %Equal.sym(Cmp,
    Word.cmp(32n, W.join(8n, 24n, w, Word.zero(24n)), W.join(8n, 24n, W.ones(8n), Word.zero(24n))),
    O.priority(Word.cmp(24n, Word.zero(24n), Word.zero(24n)), Word.cmp(8n, w, W.ones(8n))),
    A.compare_blocks(8n, 24n, w, W.ones(8n), Word.zero(24n), Word.zero(24n))) :
    {Cmp.is_le(_) == True{} : Bool}
  word_until_maximum(8n, w)

law mask_of_octet_and_is_valid:
  for +x: U32
  {U32.is_le(U32.and(x, 255), 255) == True{} : Bool}
def mask_of_octet_and_is_valid(x):
  %Equal.sym(U32, U32.and(x, 255), H.octet(W.adjust(8n, 32n, H.bits(x))), H.mask_octet(x)) :
    {U32.is_le(_, 255) == True{} : Bool}
  all_octet_formed_fits_in_255(W.adjust(8n, 32n, H.bits(x)))

law be32_only_emits_octets:
  for +x: U32
  {B.octets_all_valid(B.be32(x)) == True{} : Bool}
def be32_only_emits_octets(x):
  F.and_boolean_intro(U32.is_le(U32.and(U32.shrn(x, 24n), 255), 255),
    U32.is_le(U32.and(U32.shrn(x, 16n), 255), 255) && (U32.is_le(U32.and(U32.shrn(x, 8n), 255), 255) && (U32.is_le(U32.and(x, 255), 255) && True{})),
    mask_of_octet_and_is_valid(U32.shrn(x, 24n)),
    F.and_boolean_intro(U32.is_le(U32.and(U32.shrn(x, 16n), 255), 255),
      U32.is_le(U32.and(U32.shrn(x, 8n), 255), 255) && (U32.is_le(U32.and(x, 255), 255) && True{}),
      mask_of_octet_and_is_valid(U32.shrn(x, 16n)),
      F.and_boolean_intro(U32.is_le(U32.and(U32.shrn(x, 8n), 255), 255), U32.is_le(U32.and(x, 255), 255) && True{},
        mask_of_octet_and_is_valid(U32.shrn(x, 8n)),
        F.and_boolean_intro(U32.is_le(U32.and(x, 255), 255), True{}, mask_of_octet_and_is_valid(x), {==}))))

law concatenate_preserves_octets:
  for +xs: List<&2, U32>
  for +ys: List<&2, U32>
  for +vx: {B.octets_all_valid(xs) == True{} : Bool}
  for vy: {B.octets_all_valid(ys) == True{} : Bool}
  {B.octets_all_valid(B.concatenate(xs, ys)) == True{} : Bool}
def concatenate_preserves_octets(xs, ys, vx, vy):
  match xs:
    case Nil{}:
      vy
    case Con{+h, +t}:
      F.and_boolean_intro(U32.is_le(h, 255), B.octets_all_valid(B.concatenate(t, ys)),
        F.and_boolean_left(U32.is_le(h, 255), B.octets_all_valid(t), vx),
        concatenate_preserves_octets(t, ys, F.and_boolean_right(U32.is_le(h, 255), B.octets_all_valid(t), vx), vy))

law be64_only_emits_octets:
  for +high: U32
  for +low: U32
  {B.octets_all_valid(B.be64(high, low)) == True{} : Bool}
def be64_only_emits_octets(high, low):
  concatenate_preserves_octets(B.be32(high), B.be32(low), be32_only_emits_octets(high), be32_only_emits_octets(low))

law execution_trace_of_integer_and_exact:
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  {C.traverse(B.be64(high, low), body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, C.Root{}}) ==
    C.Decoded{D.VInt{high, low}} : C.Outcome}
def execution_trace_of_integer_and_exact(high, low, body, ceiling):
  Equal.trans(C.Outcome,
    C.traverse(B.be64(high, low), body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, C.Root{}}),
    R.finalize_frame(R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, C.Root{}}})),
    C.Decoded{D.VInt{high, low}},
    R.execution_trace_and_execution_integral(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, C.Root{}}}),
    Equal.cong(R.Frame, C.Outcome, q => R.finalize_frame(q),
      R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, C.Root{}}}),
      R.Frame{H.decrease(8n, body), H.decrease(8n, ceiling), C.DecodedReady{D.VInt{high, low}}},
      H.be64_integer_emits(high, low, C.Root{}, body, ceiling)))

law all_integer_canonical_inside_of_limit_and_accepted:
  for +high: U32
  for +low: U32
  for +ceiling: B.Number64
  for fits: {C.less_equal64(B.Number64{0, 9}, ceiling) == True{} : Bool}
  {C.decode(Con{3, B.be64(high, low)}, ceiling) == C.Decoded{D.VInt{high, low}} : C.Outcome}
def all_integer_canonical_inside_of_limit_and_accepted(high, low, ceiling, fits):
  %Equal.sym(Bool, C.less_equal64(B.Number64{0, 9}, ceiling), True{}, fits) :
    {C.decode_size(_, Con{3, B.be64(high, low)}, B.Number64{0, 9}, ceiling) == C.Decoded{D.VInt{high, low}} : C.Outcome}
  %Equal.sym(Bool, B.octets_all_valid(Con{3, B.be64(high, low)}), True{}, be64_only_emits_octets(high, low)) :
    {C.decode_octets(_, Con{3, B.be64(high, low)}, B.Number64{0, 9}, ceiling) == C.Decoded{D.VInt{high, low}} : C.Outcome}
  execution_trace_of_integer_and_exact(high, low, B.Number64{0, 8}, C.decrease64(ceiling))

law integer_of_eight_octets_reconstitutes_to_encoding_original:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +all_valid: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {P.encode(D.VInt{I.assemble(a, b, c, d), I.assemble(e, f, g, h)}) == Some{[3, a, b, c, d, e, f, g, h]} : Maybe<&2, List<&2, U32>>}
def integer_of_eight_octets_reconstitutes_to_encoding_original(a, b, c, d, e, f, g, h, all_valid):
  Equal.cong(List<&2, U32>, Maybe<&2, List<&2, U32>>, bs => Some{Con{3, bs}},
    B.be64(I.assemble(a, b, c, d), I.assemble(e, f, g, h)), [a, b, c, d, e, f, g, h],
    I.be64_reencodes_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid))

law any_eight_octets_all_valid_are_integer_canonical:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +ceiling: B.Number64
  for +all_valid: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool}
  for fits: {C.less_equal64(B.Number64{0, 9}, ceiling) == True{} : Bool}
  {C.decode([3, a, b, c, d, e, f, g, h], ceiling) == C.Decoded{D.VInt{I.assemble(a, b, c, d), I.assemble(e, f, g, h)}} : C.Outcome}
def any_eight_octets_all_valid_are_integer_canonical(a, b, c, d, e, f, g, h, ceiling, all_valid, fits):
  %I.be64_reencodes_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid) :
    {C.decode(Con{3, _}, ceiling) == C.Decoded{D.VInt{I.assemble(a, b, c, d), I.assemble(e, f, g, h)}} : C.Outcome}
  all_integer_canonical_inside_of_limit_and_accepted(I.assemble(a, b, c, d), I.assemble(e, f, g, h), ceiling, fits)

def value_result(r: C.Outcome) -> D.Value:
  match r:
    case C.Decoded{v}:
      v
    case _:
      D.VAbsent{}

# The limit and bytes are also extracted from ACTUAL ACCEPTANCE,
# without requiring another canonicity or validity witness from the caller.
def conclude_integer_accepted(+a: U32, +b: U32, +c: U32, +d: U32,
  +e: U32, +f: U32, +g: U32, +h: U32, +ceiling: B.Number64, -v: D.Value,
  accepted: {C.decode([3, a, b, c, d, e, f, g, h], ceiling) == C.Decoded{v} : C.Outcome},
  input: R.InputChecked<Some{B.Number64{0, 9}}, [3, a, b, c, d, e, f, g, h], ceiling, v>) ->
  P.Encoding(v, [3, a, b, c, d, e, f, g, h]):
  match input:
    case R.Checked{+body, measure, fits, octets, execution_trace}:
      fits9 = {(%Equal.sym(B.Number64, B.Number64{0, 9}, body, F.some_injective(B.Number64, B.Number64{0, 9}, body, measure)) :
        {C.less_equal64(_, ceiling) == True{} : Bool}
        fits) : {C.less_equal64(B.Number64{0, 9}, ceiling) == True{} : Bool}}
      +all_valid = F.and_boolean_right(True{}, B.octets_all_valid([a, b, c, d, e, f, g, h]), octets)
      value = Equal.cong(C.Outcome, D.Value, r => value_result(r),
        C.Decoded{D.VInt{I.assemble(a, b, c, d), I.assemble(e, f, g, h)}}, C.Decoded{v},
        Equal.trans(C.Outcome,
          C.Decoded{D.VInt{I.assemble(a, b, c, d), I.assemble(e, f, g, h)}}, C.decode([3, a, b, c, d, e, f, g, h], ceiling), C.Decoded{v},
          Equal.sym(C.Outcome, C.decode([3, a, b, c, d, e, f, g, h], ceiling), C.Decoded{D.VInt{I.assemble(a, b, c, d), I.assemble(e, f, g, h)}},
            any_eight_octets_all_valid_are_integer_canonical(a, b, c, d, e, f, g, h, ceiling, all_valid, fits9)), accepted))
      %value : P.Encoding(_, [3, a, b, c, d, e, f, g, h])
      integer_of_eight_octets_reconstitutes_to_encoding_original(a, b, c, d, e, f, g, h, all_valid)

law acceptance_of_integer_reconstructs_exactly_os_bytes:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +ceiling: B.Number64
  for -v: D.Value
  for +accepted: {C.decode([3, a, b, c, d, e, f, g, h], ceiling) == C.Decoded{v} : C.Outcome}
  P.Encoding(v, [3, a, b, c, d, e, f, g, h])
def acceptance_of_integer_reconstructs_exactly_os_bytes(a, b, c, d, e, f, g, h, ceiling, v, accepted):
  conclude_integer_accepted(a, b, c, d, e, f, g, h, ceiling, v, accepted,
    R.acceptance_requires_body_representable_octets_and_limit([3, a, b, c, d, e, f, g, h], ceiling, v, accepted))

# Length required by the WordInput machine itself, including EOF and extras.
def WordWholeComplete(n: Nat, bs: List<&2, U32>) -> Type:
  match n bs:
    case 0n Con{b, Nil{}}:
      Unit
    case 0n Nil{}:
      Empty
    case 0n Con{b, Con{c, t}}:
      Empty
    case 1n+p Nil{}:
      Empty
    case 1n+p Con{b, t}:
      WordWholeComplete(p, t)

law word_whole_accepts_requires_size_exact:
  for n: Nat
  for +bs: List<&2, U32>
  for +high: U32
  for +low: U32
  for +body: B.Number64
  for +ceiling: B.Number64
  for -v: D.Value
  for accepted: {C.traverse(bs, body, ceiling, C.WordInput{C.Integer{}, n, high, low, C.Root{}}) == C.Decoded{v} : C.Outcome}
  WordWholeComplete(n, bs)
def word_whole_accepts_requires_size_exact(n, bs, high, low, body, ceiling, v, accepted):
  match n bs:
    case 0n Nil{}:
      R.input_negative_decoded(v, accepted)
    case 0n Con{b, Nil{}}:
      Unit{}
    case 0n Con{+b, Con{+c, +t}}:
      R.input_negative_decoded(v,
        Equal.trans(C.Outcome, C.Input{},
          C.traverse(Con{c, t}, C.decrease64(body), C.decrease64(ceiling), C.DecodedReady{D.VInt{(high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32)}}), C.Decoded{v},
          Equal.sym(C.Outcome,
            C.traverse(Con{c, t}, C.decrease64(body), C.decrease64(ceiling), C.DecodedReady{D.VInt{(high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32)}}), C.Input{},
            R.ready_refusal_any_octet_extra(c, t, C.decrease64(body), C.decrease64(ceiling), D.VInt{(high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32)})), accepted))
    case 1n+p Nil{}:
      R.input_negative_decoded(v, accepted)
    case 1n+p Con{+b, +t}:
      word_whole_accepts_requires_size_exact(p, t, (high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32), C.decrease64(body), C.decrease64(ceiling), v, accepted)

def integer_accepted_combined_format(+bs: List<&2, U32>, +ceiling: B.Number64, -v: D.Value,
  accepted: {C.decode(Con{3, bs}, ceiling) == C.Decoded{v} : C.Outcome},
  format: WordWholeComplete(7n, bs)) -> P.Encoding(v, Con{3, bs}):
  match bs:
    case Nil{}:
      L.ex_false(P.Encoding(v, Con{3, Nil{}}), format)
    case Con{a0, Nil{}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Nil{}}}), format)
    case Con{a0, Con{a1, Nil{}}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Con{a1, Nil{}}}}), format)
    case Con{a0, Con{a1, Con{a2, Nil{}}}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Con{a1, Con{a2, Nil{}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Nil{}}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Nil{}}}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Nil{}}}}}}}}), format)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Nil{}}}}}}}}}), format)
    case Con{+a0, Con{+a1, Con{+a2, Con{+a3, Con{+a4, Con{+a5, Con{+a6, Con{+a7, Nil{}}}}}}}}}:
      acceptance_of_integer_reconstructs_exactly_os_bytes(a0, a1, a2, a3, a4, a5, a6, a7, ceiling, v, accepted)
    case Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, rest}}}}}}}}}:
      L.ex_false(P.Encoding(v, Con{3, Con{a0, Con{a1, Con{a2, Con{a3, Con{a4, Con{a5, Con{a6, Con{a7, Con{a8, rest}}}}}}}}}}), format)

def body_integer_accepted_and_exact(+bs: List<&2, U32>, +ceiling: B.Number64, -v: D.Value,
  input: R.InputChecked<B.nat64(B.length(Con{3, bs})), Con{3, bs}, ceiling, v>) -> WordWholeComplete(7n, bs):
  match input:
    case R.Checked{body, measure, fits, octets, execution_trace}:
      word_whole_accepts_requires_size_exact(7n, bs, 0, 0, C.decrease64(body), C.decrease64(ceiling), v, execution_trace)

law all_acceptance_started_by_tag_integer_and_canonical:
  for +bs: List<&2, U32>
  for +ceiling: B.Number64
  for -v: D.Value
  for +accepted: {C.decode(Con{3, bs}, ceiling) == C.Decoded{v} : C.Outcome}
  P.Encoding(v, Con{3, bs})
def all_acceptance_started_by_tag_integer_and_canonical(bs, ceiling, v, accepted):
  integer_accepted_combined_format(bs, ceiling, v, accepted,
    body_integer_accepted_and_exact(bs, ceiling, v,
      R.acceptance_requires_body_representable_octets_and_limit(Con{3, bs}, ceiling, v, accepted)))
