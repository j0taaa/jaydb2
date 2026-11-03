# General inversion of contract BE64 using actual Codec transitions.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../src/Codec.bend as C
import ./CodecWordsWord.bend as W
import ./CodecTrace.bend as R

def octet(w: Word(8n)) -> U32:
  U32{W.join(8n, 24n, w, Word.zero(24n))}

# Arguments follow big-endian order; Word stores the low bit first.
def four(a: Word(8n), b: Word(8n), c: Word(8n), d: Word(8n)) -> U32:
  U32{W.join(8n, 24n, d, W.join(8n, 16n, c, W.join(8n, 8n, b, a)))}

def bits(x: U32) -> Word(32n):
  U32{w} = x
  w

law append_octet:
  for +x: U32
  for +b: Word(8n)
  {(x * 256 + octet(b) : U32) ==
    U32{W.join(8n, 24n, b, W.adjust(24n, 32n, bits(x)))} : U32}
def append_octet(x, b):
  match x:
    case U32{w}:
      %Equal.sym(Word(32n), Word.mul(32n, w, bits(256)),
        W.zeros_low(8n, 24n, W.adjust(24n, 32n, w)),
        W.multiply_power_two(8n, 24n, 32n, w)) :
        {U32{Word.add(32n, _, W.join(8n, 24n, b, Word.zero(24n)))} ==
          U32{W.join(8n, 24n, b, W.adjust(24n, 32n, w))} : U32}
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.add(32n, W.zeros_low(8n, 24n, W.adjust(24n, 32n, w)), W.join(8n, 24n, b, Word.zero(24n))),
        W.join(8n, 24n, b, W.adjust(24n, 32n, w)), W.sum_blocks_separate(8n, 24n, b, W.adjust(24n, 32n, w)))


law mask_octet:
  for +x: U32
  {U32.and(x, 255) == octet(W.adjust(8n, 32n, bits(x))) : U32}
def mask_octet(x):
  match x:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z},
        Word.and(32n, w, W.join(8n, 24n, W.ones(8n), Word.zero(24n))),
        W.join(8n, 24n, W.adjust(8n, 32n, w), Word.zero(24n)), W.mask_low(8n, 24n, w))

law append_four:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  {(four(a, b, c, d) * 256 + octet(e) : U32) == four(b, c, d, e) : U32}
def append_four(a, b, c, d, e):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      %Equal.sym(U32, (four(a, b, c, d) * 256 + octet(e) : U32),
        U32{W.join(8n, 24n, e, W.adjust(24n, 32n, bits(four(a, b, c, d))))},
        append_octet(four(a, b, c, d), e)) : {_ == four(b, c, d, e) : U32}
      {==}

law top_four:
  for +a: Word(8n)
  for b: Word(8n)
  for c: Word(8n)
  for d: Word(8n)
  {U32.shrn(four(a, b, c, d), 24n) == octet(a) : U32}
def top_four(a, b, c, d):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      {==}

law be32_four:
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  {B.be32(four(a, b, c, d)) == [octet(a), octet(b), octet(c), octet(d)] : List<&2, U32>}
def be32_four(a, b, c, d):
  match a b c d:
    case WCon{a0, WCon{a1, WCon{a2, WCon{a3, WCon{a4, WCon{a5, WCon{a6, WCon{a7, WNil{}}}}}}}}} WCon{b0, WCon{b1, WCon{b2, WCon{b3, WCon{b4, WCon{b5, WCon{b6, WCon{b7, WNil{}}}}}}}}} WCon{c0, WCon{c1, WCon{c2, WCon{c3, WCon{c4, WCon{c5, WCon{c6, WCon{c7, WNil{}}}}}}}}} WCon{d0, WCon{d1, WCon{d2, WCon{d3, WCon{d4, WCon{d5, WCon{d6, WCon{d7, WNil{}}}}}}}}}:
      %Equal.sym(U32, U32.and(U32.shrn(four(a, b, c, d), 24n), 255), octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 24n)))), mask_octet(U32.shrn(four(a, b, c, d), 24n))) :
        {[_, U32.and(U32.shrn(four(a, b, c, d), 16n), 255), U32.and(U32.shrn(four(a, b, c, d), 8n), 255), U32.and(four(a, b, c, d), 255)] == [octet(a), octet(b), octet(c), octet(d)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.shrn(four(a, b, c, d), 16n), 255), octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 16n)))), mask_octet(U32.shrn(four(a, b, c, d), 16n))) :
        {[octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 24n)))), _, U32.and(U32.shrn(four(a, b, c, d), 8n), 255), U32.and(four(a, b, c, d), 255)] == [octet(a), octet(b), octet(c), octet(d)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(U32.shrn(four(a, b, c, d), 8n), 255), octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 8n)))), mask_octet(U32.shrn(four(a, b, c, d), 8n))) :
        {[octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 24n)))), octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 16n)))), _, U32.and(four(a, b, c, d), 255)] == [octet(a), octet(b), octet(c), octet(d)] : List<&2, U32>}
      %Equal.sym(U32, U32.and(four(a, b, c, d), 255), octet(W.adjust(8n, 32n, bits(four(a, b, c, d)))), mask_octet(four(a, b, c, d))) :
        {[octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 24n)))), octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 16n)))), octet(W.adjust(8n, 32n, bits(U32.shrn(four(a, b, c, d), 8n)))), _] == [octet(a), octet(b), octet(c), octet(d)] : List<&2, U32>}
      {==}

def next(n: Nat, f: C.Purpose, high: U32, low: U32, stack: C.Stack, body: B.Number64, ceiling: B.Number64) -> C.Machine:
  match n:
    case 0n:
      C.conclude_word(f, high, low, stack, body, ceiling)
    case 1n+p:
      C.WordInput{f, p, high, low, stack}

law read_word_blocks:
  for n: Nat
  for +f: C.Purpose
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +i: Word(8n)
  for +j: Word(8n)
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {C.read_word(n, f, four(a, b, c, d), four(e, g, h, i), octet(j), stack, body, ceiling) ==
    next(n, f, four(b, c, d, e), four(g, h, i, j), stack, body, ceiling) : C.Machine}
def read_word_blocks(n, f, a, b, c, d, e, g, h, i, j, stack, body, ceiling):
  match n:
    case 0n:
      %Equal.sym(U32, U32.shrn(four(e, g, h, i), 24n), octet(e), top_four(e, g, h, i)) :
        {C.conclude_word(f, (four(a, b, c, d) * 256 + _ : U32), (four(e, g, h, i) * 256 + octet(j) : U32), stack, body, ceiling) == C.conclude_word(f, four(b, c, d, e), four(g, h, i, j), stack, body, ceiling) : C.Machine}
      %Equal.sym(U32, (four(a, b, c, d) * 256 + octet(e) : U32), four(b, c, d, e), append_four(a, b, c, d, e)) :
        {C.conclude_word(f, _, (four(e, g, h, i) * 256 + octet(j) : U32), stack, body, ceiling) == C.conclude_word(f, four(b, c, d, e), four(g, h, i, j), stack, body, ceiling) : C.Machine}
      %Equal.sym(U32, (four(e, g, h, i) * 256 + octet(j) : U32), four(g, h, i, j), append_four(e, g, h, i, j)) :
        {C.conclude_word(f, four(b, c, d, e), _, stack, body, ceiling) == C.conclude_word(f, four(b, c, d, e), four(g, h, i, j), stack, body, ceiling) : C.Machine}
      {==}
    case 1n+p:
      %Equal.sym(U32, U32.shrn(four(e, g, h, i), 24n), octet(e), top_four(e, g, h, i)) :
        {C.WordInput{f, p, (four(a, b, c, d) * 256 + _ : U32), (four(e, g, h, i) * 256 + octet(j) : U32), stack} == C.WordInput{f, p, four(b, c, d, e), four(g, h, i, j), stack} : C.Machine}
      %Equal.sym(U32, (four(a, b, c, d) * 256 + octet(e) : U32), four(b, c, d, e), append_four(a, b, c, d, e)) :
        {C.WordInput{f, p, _, (four(e, g, h, i) * 256 + octet(j) : U32), stack} == C.WordInput{f, p, four(b, c, d, e), four(g, h, i, j), stack} : C.Machine}
      %Equal.sym(U32, (four(e, g, h, i) * 256 + octet(j) : U32), four(g, h, i, j), append_four(e, g, h, i, j)) :
        {C.WordInput{f, p, four(b, c, d, e), _, stack} == C.WordInput{f, p, four(b, c, d, e), four(g, h, i, j), stack} : C.Machine}
      {==}

law advance_word_blocks:
  for +n: Nat
  for +f: C.Purpose
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +i: Word(8n)
  for +j: Word(8n)
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.advance(R.Frame{body, ceiling, C.WordInput{f, n, four(a, b, c, d), four(e, g, h, i), stack}}, octet(j)) ==
    R.Frame{C.decrease64(body), C.decrease64(ceiling),
      next(n, f, four(b, c, d, e), four(g, h, i, j), stack, C.decrease64(body), C.decrease64(ceiling))} : R.Frame}
def advance_word_blocks(n, f, a, b, c, d, e, g, h, i, j, stack, body, ceiling):
  Equal.cong(C.Machine, R.Frame, m => R.Frame{C.decrease64(body), C.decrease64(ceiling), m},
    C.read_word(n, f, four(a, b, c, d), four(e, g, h, i), octet(j), stack, C.decrease64(body), C.decrease64(ceiling)),
    next(n, f, four(b, c, d, e), four(g, h, i, j), stack, C.decrease64(body), C.decrease64(ceiling)),
    read_word_blocks(n, f, a, b, c, d, e, g, h, i, j, stack, C.decrease64(body), C.decrease64(ceiling)))

def decrease(n: Nat, x: B.Number64) -> B.Number64:
  match n:
    case 0n:
      x
    case 1n+p:
      C.decrease64(decrease(p, x))

law eight_octets_conclude_word:
  for +f: C.Purpose
  for +a: Word(8n)
  for +b: Word(8n)
  for +c: Word(8n)
  for +d: Word(8n)
  for +e: Word(8n)
  for +fb: Word(8n)
  for +g: Word(8n)
  for +h: Word(8n)
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.execute([octet(a), octet(b), octet(c), octet(d), octet(e), octet(fb), octet(g), octet(h)],
    R.Frame{body, ceiling, C.WordInput{f, 7n, 0, 0, stack}}) ==
    R.Frame{decrease(8n, body), decrease(8n, ceiling),
      C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
def eight_octets_conclude_word(f, a, b, c, d, e, fb, g, h, stack, body, ceiling):
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(0n, body), decrease(0n, ceiling), C.WordInput{f, 7n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), stack}}, octet(a)), R.Frame{decrease(1n, body), decrease(1n, ceiling), C.WordInput{f, 6n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), stack}},
    advance_word_blocks(7n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, stack, decrease(0n, body), decrease(0n, ceiling))) :
    {R.execute([octet(b), octet(c), octet(d), octet(e), octet(fb), octet(g), octet(h)], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(1n, body), decrease(1n, ceiling), C.WordInput{f, 6n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), stack}}, octet(b)), R.Frame{decrease(2n, body), decrease(2n, ceiling), C.WordInput{f, 5n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(Word.zero(8n), Word.zero(8n), a, b), stack}},
    advance_word_blocks(6n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, stack, decrease(1n, body), decrease(1n, ceiling))) :
    {R.execute([octet(c), octet(d), octet(e), octet(fb), octet(g), octet(h)], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(2n, body), decrease(2n, ceiling), C.WordInput{f, 5n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(Word.zero(8n), Word.zero(8n), a, b), stack}}, octet(c)), R.Frame{decrease(3n, body), decrease(3n, ceiling), C.WordInput{f, 4n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(Word.zero(8n), a, b, c), stack}},
    advance_word_blocks(5n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, stack, decrease(2n, body), decrease(2n, ceiling))) :
    {R.execute([octet(d), octet(e), octet(fb), octet(g), octet(h)], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(3n, body), decrease(3n, ceiling), C.WordInput{f, 4n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(Word.zero(8n), a, b, c), stack}}, octet(d)), R.Frame{decrease(4n, body), decrease(4n, ceiling), C.WordInput{f, 3n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(a, b, c, d), stack}},
    advance_word_blocks(4n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, stack, decrease(3n, body), decrease(3n, ceiling))) :
    {R.execute([octet(e), octet(fb), octet(g), octet(h)], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(4n, body), decrease(4n, ceiling), C.WordInput{f, 3n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n)), four(a, b, c, d), stack}}, octet(e)), R.Frame{decrease(5n, body), decrease(5n, ceiling), C.WordInput{f, 2n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), four(b, c, d, e), stack}},
    advance_word_blocks(3n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e, stack, decrease(4n, body), decrease(4n, ceiling))) :
    {R.execute([octet(fb), octet(g), octet(h)], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(5n, body), decrease(5n, ceiling), C.WordInput{f, 2n, four(Word.zero(8n), Word.zero(8n), Word.zero(8n), a), four(b, c, d, e), stack}}, octet(fb)), R.Frame{decrease(6n, body), decrease(6n, ceiling), C.WordInput{f, 1n, four(Word.zero(8n), Word.zero(8n), a, b), four(c, d, e, fb), stack}},
    advance_word_blocks(2n, f, Word.zero(8n), Word.zero(8n), Word.zero(8n), a, b, c, d, e, fb, stack, decrease(5n, body), decrease(5n, ceiling))) :
    {R.execute([octet(g), octet(h)], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(6n, body), decrease(6n, ceiling), C.WordInput{f, 1n, four(Word.zero(8n), Word.zero(8n), a, b), four(c, d, e, fb), stack}}, octet(g)), R.Frame{decrease(7n, body), decrease(7n, ceiling), C.WordInput{f, 0n, four(Word.zero(8n), a, b, c), four(d, e, fb, g), stack}},
    advance_word_blocks(1n, f, Word.zero(8n), Word.zero(8n), a, b, c, d, e, fb, g, stack, decrease(6n, body), decrease(6n, ceiling))) :
    {R.execute([octet(h)], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  %Equal.sym(R.Frame, R.advance(R.Frame{decrease(7n, body), decrease(7n, ceiling), C.WordInput{f, 0n, four(Word.zero(8n), a, b, c), four(d, e, fb, g), stack}}, octet(h)), R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))},
    advance_word_blocks(0n, f, Word.zero(8n), a, b, c, d, e, fb, g, h, stack, decrease(7n, body), decrease(7n, ceiling))) :
    {R.execute([], _) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, four(a, b, c, d), four(e, fb, g, h), stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
  {==}

# Main theorem: every purpose, arbitrary words and every stack.
law be64_concludes_word:
  for +f: C.Purpose
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{f, 7n, 0, 0, stack}}) ==
    R.Frame{decrease(8n, body), decrease(8n, ceiling),
      C.conclude_word(f, high, low, stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
def be64_concludes_word(f, high, low, stack, body, ceiling):
  match high low:
    case U32{WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}} U32{WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}:
      %Equal.sym(List<&2, U32>, B.be32(high), [octet(WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}), octet(WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}), octet(WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}), octet(WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}})], be32_four(WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}})) :
        {R.execute(B.concatenate(_, B.be32(low)), R.Frame{body, ceiling, C.WordInput{f, 7n, 0, 0, stack}}) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, high, low, stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
      %Equal.sym(List<&2, U32>, B.be32(low), [octet(WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}), octet(WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WNil{}}}}}}}}}), octet(WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WNil{}}}}}}}}}), octet(WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WNil{}}}}}}}}})], be32_four(WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WNil{}}}}}}}}}, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WNil{}}}}}}}}}, WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WNil{}}}}}}}}})) :
        {R.execute(B.concatenate([octet(WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}), octet(WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}), octet(WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}), octet(WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}})], _), R.Frame{body, ceiling, C.WordInput{f, 7n, 0, 0, stack}}) == R.Frame{decrease(8n, body), decrease(8n, ceiling), C.conclude_word(f, high, low, stack, decrease(8n, body), decrease(8n, ceiling))} : R.Frame}
      eight_octets_conclude_word(f, WCon{h24, WCon{h25, WCon{h26, WCon{h27, WCon{h28, WCon{h29, WCon{h30, WCon{h31, WNil{}}}}}}}}}, WCon{h16, WCon{h17, WCon{h18, WCon{h19, WCon{h20, WCon{h21, WCon{h22, WCon{h23, WNil{}}}}}}}}}, WCon{h8, WCon{h9, WCon{h10, WCon{h11, WCon{h12, WCon{h13, WCon{h14, WCon{h15, WNil{}}}}}}}}}, WCon{h0, WCon{h1, WCon{h2, WCon{h3, WCon{h4, WCon{h5, WCon{h6, WCon{h7, WNil{}}}}}}}}}, WCon{l24, WCon{l25, WCon{l26, WCon{l27, WCon{l28, WCon{l29, WCon{l30, WCon{l31, WNil{}}}}}}}}}, WCon{l16, WCon{l17, WCon{l18, WCon{l19, WCon{l20, WCon{l21, WCon{l22, WCon{l23, WNil{}}}}}}}}}, WCon{l8, WCon{l9, WCon{l10, WCon{l11, WCon{l12, WCon{l13, WCon{l14, WCon{l15, WNil{}}}}}}}}}, WCon{l0, WCon{l1, WCon{l2, WCon{l3, WCon{l4, WCon{l5, WCon{l6, WCon{l7, WNil{}}}}}}}}}, stack, body, ceiling)

law be64_integer_emits:
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}}) ==
    R.Frame{decrease(8n, body), decrease(8n, ceiling), C.emit(stack, D.VInt{high, low})} : R.Frame}
def be64_integer_emits(high, low, stack, body, ceiling):
  be64_concludes_word(C.Integer{}, high, low, stack, body, ceiling)

law be64_integer_eight_steps:
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  {R.machine(R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}})) ==
    C.emit(stack, D.VInt{high, low}) : C.Machine}
def be64_integer_eight_steps(high, low, stack, body, ceiling):
  Equal.cong(R.Frame, C.Machine, q => R.machine(q),
    R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}}),
    R.Frame{decrease(8n, body), decrease(8n, ceiling), C.emit(stack, D.VInt{high, low})},
    be64_integer_emits(high, low, stack, body, ceiling))

law be64_integer_preserves_suffix:
  for +high: U32
  for +low: U32
  for +stack: C.Stack
  for +body: B.Number64
  for +ceiling: B.Number64
  for +suffix: List<&2, U32>
  {R.execute(B.concatenate(B.be64(high, low), suffix),
    R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}}) ==
    R.execute(suffix, R.Frame{decrease(8n, body), decrease(8n, ceiling), C.emit(stack, D.VInt{high, low})}) : R.Frame}
def be64_integer_preserves_suffix(high, low, stack, body, ceiling, suffix):
  Equal.trans(R.Frame,
    R.execute(B.concatenate(B.be64(high, low), suffix), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}}),
    R.execute(suffix, R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}})),
    R.execute(suffix, R.Frame{decrease(8n, body), decrease(8n, ceiling), C.emit(stack, D.VInt{high, low})}),
    R.execution_of_concatenation(B.be64(high, low), suffix, R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}}),
    Equal.cong(R.Frame, R.Frame, q => R.execute(suffix, q),
      R.execute(B.be64(high, low), R.Frame{body, ceiling, C.WordInput{C.Integer{}, 7n, 0, 0, stack}}),
      R.Frame{decrease(8n, body), decrease(8n, ceiling), C.emit(stack, D.VInt{high, low})},
      be64_integer_emits(high, low, stack, body, ceiling)))
