# Reverse direction: eight valid bytes, accumulated words and exact bytes.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecTrace.bend as R
import ./CodecWordsWord.bend as W
import ./CodecWordsBE64.bend as E
import ./Foundations.bend as F

def byte_word(x: U32) -> Word(8n):
  W.adjust(8n, 32n, E.bits(x))

def assemble(a: U32, b: U32, c: U32, d: U32) -> U32:
  E.four(byte_word(a), byte_word(b), byte_word(c), byte_word(d))

law octet_valid_reconstituted:
  for +x: U32
  for valid: {U32.is_le(x, 255) == True{} : Bool}
  {x == E.octet(byte_word(x)) : U32}
def octet_valid_reconstituted(x, valid):
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.join(8n, 24n, W.adjust(8n, 32n, w), Word.zero(24n)), W.limit_bits_low(8n, 24n, w, valid))

def represent_octets(bs: List<&2, U32>) -> List<&2, U32>:
  match bs:
    case Nil{}:
      Nil{}
    case Con{b, t}:
      Con{E.octet(byte_word(b)), represent_octets(t)}

law octets_all_valid_representation:
  for +bs: List<&2, U32>
  for +all_valid: {B.octets_all_valid(bs) == True{} : Bool}
  {bs == represent_octets(bs) : List<&2, U32>}
def octets_all_valid_representation(bs, all_valid):
  match bs:
    case Nil{}:
      {==}
    case Con{+b, +t}:
      Equal.trans(List<&2, U32>, Con{b, t}, Con{E.octet(byte_word(b)), t}, Con{E.octet(byte_word(b)), represent_octets(t)},
        Equal.cong(U32, List<&2, U32>, x => Con{x, t}, b, E.octet(byte_word(b)),
          octet_valid_reconstituted(b, F.and_boolean_left(U32.is_le(b, 255), B.octets_all_valid(t), all_valid))),
        Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{E.octet(byte_word(b)), xs}, t, represent_octets(t),
          octets_all_valid_representation(t, F.and_boolean_right(U32.is_le(b, 255), B.octets_all_valid(t), all_valid))))

law reencode_blocks:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +f: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  {B.be64(E.four(a, b, c, d), E.four(e, f, g, h)) ==
    [E.octet(a), E.octet(b), E.octet(c), E.octet(d), E.octet(e), E.octet(f), E.octet(g), E.octet(h)] : List<&2, U32>}
def reencode_blocks(a, b, c, d, e, f, g, h):
  %Equal.sym(List<&2, U32>, B.be32(E.four(a, b, c, d)), [E.octet(a), E.octet(b), E.octet(c), E.octet(d)], E.be32_four(a, b, c, d)) :
    {B.concatenate(_, B.be32(E.four(e, f, g, h))) == [E.octet(a), E.octet(b), E.octet(c), E.octet(d), E.octet(e), E.octet(f), E.octet(g), E.octet(h)] : List<&2, U32>}
  %Equal.sym(List<&2, U32>, B.be32(E.four(e, f, g, h)), [E.octet(e), E.octet(f), E.octet(g), E.octet(h)], E.be32_four(e, f, g, h)) :
    {B.concatenate([E.octet(a), E.octet(b), E.octet(c), E.octet(d)], _) == [E.octet(a), E.octet(b), E.octet(c), E.octet(d), E.octet(e), E.octet(f), E.octet(g), E.octet(h)] : List<&2, U32>}
  {==}

law reencode_octets_separate:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for va: {U32.is_le(a, 255) == True{} : Bool}
  for vb: {U32.is_le(b, 255) == True{} : Bool}
  for vc: {U32.is_le(c, 255) == True{} : Bool}
  for vd: {U32.is_le(d, 255) == True{} : Bool}
  for ve: {U32.is_le(e, 255) == True{} : Bool}
  for vf: {U32.is_le(f, 255) == True{} : Bool}
  for vg: {U32.is_le(g, 255) == True{} : Bool}
  for vh: {U32.is_le(h, 255) == True{} : Bool}
  {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def reencode_octets_separate(a, b, c, d, e, f, g, h, va, vb, vc, vd, ve, vf, vg, vh):
  %Equal.sym(U32, a, E.octet(byte_word(a)), octet_valid_reconstituted(a, va)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [_, b, c, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, b, E.octet(byte_word(b)), octet_valid_reconstituted(b, vb)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [E.octet(byte_word(a)), _, c, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, c, E.octet(byte_word(c)), octet_valid_reconstituted(c, vc)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [E.octet(byte_word(a)), E.octet(byte_word(b)), _, d, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, d, E.octet(byte_word(d)), octet_valid_reconstituted(d, vd)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [E.octet(byte_word(a)), E.octet(byte_word(b)), E.octet(byte_word(c)), _, e, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, e, E.octet(byte_word(e)), octet_valid_reconstituted(e, ve)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [E.octet(byte_word(a)), E.octet(byte_word(b)), E.octet(byte_word(c)), E.octet(byte_word(d)), _, f, g, h] : List<&2, U32>}
  %Equal.sym(U32, f, E.octet(byte_word(f)), octet_valid_reconstituted(f, vf)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [E.octet(byte_word(a)), E.octet(byte_word(b)), E.octet(byte_word(c)), E.octet(byte_word(d)), E.octet(byte_word(e)), _, g, h] : List<&2, U32>}
  %Equal.sym(U32, g, E.octet(byte_word(g)), octet_valid_reconstituted(g, vg)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [E.octet(byte_word(a)), E.octet(byte_word(b)), E.octet(byte_word(c)), E.octet(byte_word(d)), E.octet(byte_word(e)), E.octet(byte_word(f)), _, h] : List<&2, U32>}
  %Equal.sym(U32, h, E.octet(byte_word(h)), octet_valid_reconstituted(h, vh)) :
    {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [E.octet(byte_word(a)), E.octet(byte_word(b)), E.octet(byte_word(c)), E.octet(byte_word(d)), E.octet(byte_word(e)), E.octet(byte_word(f)), E.octet(byte_word(g)), _] : List<&2, U32>}
  reencode_blocks(byte_word(a), byte_word(b), byte_word(c), byte_word(d), byte_word(e), byte_word(f), byte_word(g), byte_word(h))

law be64_reencodes_eight_octets_all_valid:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +all_valid: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {B.be64(assemble(a, b, c, d), assemble(e, f, g, h)) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def be64_reencodes_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid):
  Equal.trans(List<&2, U32>,
    B.be64(assemble(a, b, c, d), assemble(e, f, g, h)),
    represent_octets([a, b, c, d, e, f, g, h]), [a, b, c, d, e, f, g, h],
    reencode_blocks(byte_word(a), byte_word(b), byte_word(c), byte_word(d), byte_word(e), byte_word(f), byte_word(g), byte_word(h)),
    Equal.sym(List<&2, U32>, [a, b, c, d, e, f, g, h], represent_octets([a, b, c, d, e, f, g, h]),
      octets_all_valid_representation([a, b, c, d, e, f, g, h], all_valid)))

# Arithmetic IDENTICAL to src/Codec.read_word, before concluding the purpose.
def accumulate_octet(n: B.Number64, b: U32) -> B.Number64:
  B.Number64{high, +low} = n
  B.Number64{(high * 256 + U32.shrn(low, 24n) : U32), (low * 256 + b : U32)}

def accumulate(bs: List<&2, U32>, n: B.Number64) -> B.Number64:
  match bs:
    case Nil{}:
      n
    case Con{b, t}:
      accumulate(t, accumulate_octet(n, b))

def reencode(n: B.Number64) -> List<&2, U32>:
  B.Number64{high, low} = n
  B.be64(high, low)

def conclude_accumulation(n: Nat, f: C.Purpose, words: B.Number64, stack: C.Stack, body: B.Number64, ceiling: B.Number64) -> C.Machine:
  B.Number64{high, low} = words
  E.next(n, f, high, low, stack, body, ceiling)

law accumulator_and_transition_real:
  for n: Nat
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +b: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {C.read_word(n, f, high, low, b, stack, body, ceiling) ==
    conclude_accumulation(n, f, accumulate_octet(B.Number64{high, low}, b), stack, body, ceiling) : C.Machine}
def accumulator_and_transition_real(n, f, high, low, b, stack, body, ceiling):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law accumulate_blocks:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +i: Word(8n)
  for +j: Word(8n)
  {accumulate_octet(B.Number64{E.four(a, b, c, d), E.four(e, g, h, i)}, E.octet(j)) ==
    B.Number64{E.four(b, c, d, e), E.four(g, h, i, j)} : B.Number64}
def accumulate_blocks(a, b, c, d, e, g, h, i, j):
  %Equal.sym(U32, U32.shrn(E.four(e, g, h, i), 24n), E.octet(e), E.top_four(e, g, h, i)) :
    {B.Number64{(E.four(a, b, c, d) * 256 + _ : U32), (E.four(e, g, h, i) * 256 + E.octet(j) : U32)} ==
      B.Number64{E.four(b, c, d, e), E.four(g, h, i, j)} : B.Number64}
  %Equal.sym(U32, (E.four(a, b, c, d) * 256 + E.octet(e) : U32), E.four(b, c, d, e), E.append_four(a, b, c, d, e)) :
    {B.Number64{_, (E.four(e, g, h, i) * 256 + E.octet(j) : U32)} ==
      B.Number64{E.four(b, c, d, e), E.four(g, h, i, j)} : B.Number64}
  %Equal.sym(U32, (E.four(e, g, h, i) * 256 + E.octet(j) : U32), E.four(g, h, i, j), E.append_four(e, g, h, i, j)) :
    {B.Number64{E.four(b, c, d, e), _} == B.Number64{E.four(b, c, d, e), E.four(g, h, i, j)} : B.Number64}
  {==}

law accumulate_eight_blocks:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +f: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  {accumulate([E.octet(a), E.octet(b), E.octet(c), E.octet(d), E.octet(e), E.octet(f), E.octet(g), E.octet(h)], B.Number64{0, 0}) ==
    B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
def accumulate_eight_blocks(a, b, c, d, e, f, g, h):
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n))}, E.octet(a)), B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a)},
    accumulate_blocks(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a)) :
    {accumulate([E.octet(b), E.octet(c), E.octet(d), E.octet(e), E.octet(f), E.octet(g), E.octet(h)], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a)}, E.octet(b)), B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(Word.zero(8n), Word.zero(8n), a, b)},
    accumulate_blocks(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b)) :
    {accumulate([E.octet(c), E.octet(d), E.octet(e), E.octet(f), E.octet(g), E.octet(h)], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(Word.zero(8n), Word.zero(8n), a, b)}, E.octet(c)), B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(Word.zero(8n), a, b, c)},
    accumulate_blocks(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c)) :
    {accumulate([E.octet(d), E.octet(e), E.octet(f), E.octet(g), E.octet(h)], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(Word.zero(8n), a, b, c)}, E.octet(d)), B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(a, b, c, d)},
    accumulate_blocks(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d)) :
    {accumulate([E.octet(e), E.octet(f), E.octet(g), E.octet(h)], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), E.four(a, b, c, d)}, E.octet(e)), B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), E.four(b, c, d, e)},
    accumulate_blocks(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e)) :
    {accumulate([E.octet(f), E.octet(g), E.octet(h)], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), E.four(b, c, d, e)}, E.octet(f)), B.Number64{E.four(Word.zero(8n), Word.zero(8n), a, b), E.four(c, d, e, f)},
    accumulate_blocks(Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e, f)) :
    {accumulate([E.octet(g), E.octet(h)], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), Word.zero(8n), a, b), E.four(c, d, e, f)}, E.octet(g)), B.Number64{E.four(Word.zero(8n), a, b, c), E.four(d, e, f, g)},
    accumulate_blocks(Word.zero(8n), Word.zero(8n), a, b, c, d, e, f, g)) :
    {accumulate([E.octet(h)], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  %Equal.sym(B.Number64, accumulate_octet(B.Number64{E.four(Word.zero(8n), a, b, c), E.four(d, e, f, g)}, E.octet(h)), B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)},
    accumulate_blocks(Word.zero(8n), a, b, c, d, e, f, g, h)) :
    {accumulate([], _) == B.Number64{E.four(a, b, c, d), E.four(e, f, g, h)} : B.Number64}
  {==}

law accumulate_eight_octets_all_valid:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +all_valid: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {accumulate([a, b, c, d, e, f, g, h], B.Number64{0, 0}) == B.Number64{assemble(a, b, c, d), assemble(e, f, g, h)} : B.Number64}
def accumulate_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid):
  Equal.trans(B.Number64, accumulate([a, b, c, d, e, f, g, h], B.Number64{0, 0}), accumulate(represent_octets([a, b, c, d, e, f, g, h]), B.Number64{0, 0}), B.Number64{assemble(a, b, c, d), assemble(e, f, g, h)},
    Equal.cong(List<&2, U32>, B.Number64, ys => accumulate(ys, B.Number64{0, 0}), [a, b, c, d, e, f, g, h], represent_octets([a, b, c, d, e, f, g, h]), octets_all_valid_representation([a, b, c, d, e, f, g, h], all_valid)),
    accumulate_eight_blocks(byte_word(a), byte_word(b), byte_word(c), byte_word(d), byte_word(e), byte_word(f), byte_word(g), byte_word(h)))

# Words are computed here, not assumed by a canonicity premise.
law be64_inverts_accumulation_of_eight_octets_all_valid:
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +all_valid: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {reencode(accumulate([a, b, c, d, e, f, g, h], B.Number64{0, 0})) == [a, b, c, d, e, f, g, h] : List<&2, U32>}
def be64_inverts_accumulation_of_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid):
  Equal.trans(List<&2, U32>, reencode(accumulate([a, b, c, d, e, f, g, h], B.Number64{0, 0})), reencode(B.Number64{assemble(a, b, c, d), assemble(e, f, g, h)}), [a, b, c, d, e, f, g, h],
    Equal.cong(B.Number64, List<&2, U32>, n => reencode(n), accumulate([a, b, c, d, e, f, g, h], B.Number64{0, 0}), B.Number64{assemble(a, b, c, d), assemble(e, f, g, h)},
      accumulate_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid)),
    be64_reencodes_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid))

law eight_octets_all_valid_conclude_word:
  for +purpose: C.Purpose
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for +all_valid: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {R.execute([a, b, c, d, e, f, g, h], R.Frame{body, ceiling, C.WordInput{purpose, 7n, 0, 0, stack}}) == R.Frame{E.decrease(8n, body), E.decrease(8n, ceiling), C.conclude_word(purpose, assemble(a, b, c, d), assemble(e, f, g, h), stack, E.decrease(8n, body), E.decrease(8n, ceiling))} : R.Frame}
def eight_octets_all_valid_conclude_word(purpose, a, b, c, d, e, f, g, h, stack, body, ceiling, all_valid):
  Equal.trans(R.Frame, R.execute([a, b, c, d, e, f, g, h], R.Frame{body, ceiling, C.WordInput{purpose, 7n, 0, 0, stack}}), R.execute(represent_octets([a, b, c, d, e, f, g, h]), R.Frame{body, ceiling, C.WordInput{purpose, 7n, 0, 0, stack}}), R.Frame{E.decrease(8n, body), E.decrease(8n, ceiling), C.conclude_word(purpose, assemble(a, b, c, d), assemble(e, f, g, h), stack, E.decrease(8n, body), E.decrease(8n, ceiling))},
    Equal.cong(List<&2, U32>, R.Frame, ys => R.execute(ys, R.Frame{body, ceiling, C.WordInput{purpose, 7n, 0, 0, stack}}), [a, b, c, d, e, f, g, h], represent_octets([a, b, c, d, e, f, g, h]), octets_all_valid_representation([a, b, c, d, e, f, g, h], all_valid)),
    E.eight_octets_conclude_word(purpose, byte_word(a), byte_word(b), byte_word(c), byte_word(d), byte_word(e), byte_word(f), byte_word(g), byte_word(h), stack, body, ceiling))

law eight_octets_all_valid_conclude_accumulation_real:
  for +purpose: C.Purpose
  for +a: U32
  for +b: U32
  for +c: U32
  for +d: U32
  for +e: U32
  for +f: U32
  for +g: U32
  for +h: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for +all_valid: {B.octets_all_valid([a, b, c, d, e, f, g, h]) == True{} : Bool}
  {R.execute([a, b, c, d, e, f, g, h], R.Frame{body, ceiling, C.WordInput{purpose, 7n, 0, 0, stack}}) == R.Frame{E.decrease(8n, body), E.decrease(8n, ceiling), conclude_accumulation(0n, purpose, accumulate([a, b, c, d, e, f, g, h], B.Number64{0, 0}), stack, E.decrease(8n, body), E.decrease(8n, ceiling))} : R.Frame}
def eight_octets_all_valid_conclude_accumulation_real(purpose, a, b, c, d, e, f, g, h, stack, body, ceiling, all_valid):
  %Equal.sym(B.Number64, accumulate([a, b, c, d, e, f, g, h], B.Number64{0, 0}), B.Number64{assemble(a, b, c, d), assemble(e, f, g, h)},
    accumulate_eight_octets_all_valid(a, b, c, d, e, f, g, h, all_valid)) :
    {R.execute([a, b, c, d, e, f, g, h], R.Frame{body, ceiling, C.WordInput{purpose, 7n, 0, 0, stack}}) == R.Frame{E.decrease(8n, body), E.decrease(8n, ceiling), conclude_accumulation(0n, purpose, _, stack, E.decrease(8n, body), E.decrease(8n, ceiling))} : R.Frame}
  eight_octets_all_valid_conclude_word(purpose, a, b, c, d, e, f, g, h, stack, body, ceiling, all_valid)
