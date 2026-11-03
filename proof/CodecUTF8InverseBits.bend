# Block comparisons used in UTF-8 inversion. All payloads are
# arbitrary words; prefixes are bits fixed by the UTF-8 format.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecWordsWord.bend as W
import ./CodecUTF8Bits.bend as X
import ./Foundations.bend as F
import ./Orders.bend as O

def prefix2(hi: Word(5n)) -> U32:
  U32{W.join(5n, 27n, hi, W.adjust(27n, 32n, X.bits(6)))}

def prefix3(hi: Word(4n)) -> U32:
  U32{W.join(4n, 28n, hi, W.adjust(28n, 32n, X.bits(14)))}

def prefix4(hi: Word(3n)) -> U32:
  U32{W.join(3n, 29n, hi, W.adjust(29n, 32n, X.bits(30)))}

def bit_ge_zero(b: Bool, c: Cmp, e: {Cmp.is_ge(c) == True{} : Bool}) ->
  {Cmp.is_ge(Word.cmp.fin(b, False{}, c)) == True{} : Bool}:
  match b c:
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case _ GT{}:
      {==}
    case _ LT{}:
      e

def bit_reads_one(b: Bool, c: Cmp, e: {Cmp.is_le(c) == True{} : Bool}) ->
  {Cmp.is_le(Word.cmp.fin(b, True{}, c)) == True{} : Bool}:
  match b c:
    case False{} EQ{}:
      {==}
    case True{} EQ{}:
      {==}
    case _ LT{}:
      {==}
    case _ GT{}:
      e

law word_greater_equal_zero:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_ge(Word.cmp(n, w, Word.zero(n))) == True{} : Bool}
def word_greater_equal_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          bit_ge_zero(b, Word.cmp(p, t, Word.zero(p)), word_greater_equal_zero(p, t))

law word_less_equal_ones:
  for +n: Nat
  for +w: Word(n)
  {Cmp.is_le(Word.cmp(n, w, W.ones(n))) == True{} : Bool}
def word_less_equal_ones(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          bit_reads_one(b, Word.cmp(p, t, W.ones(p)), word_less_equal_ones(p, t))

law priority_ge_without_negative:
  for h: Cmp
  for l: Cmp
  for positive: {Cmp.is_ge(l) == True{} : Bool}
  {Cmp.is_ge(O.priority(h, l)) == Cmp.is_ge(h) : Bool}
def priority_ge_without_negative(h, l, positive):
  match h:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      positive

law priority_reads_without_excess:
  for h: Cmp
  for l: Cmp
  for fits: {Cmp.is_le(l) == True{} : Bool}
  {Cmp.is_le(O.priority(h, l)) == Cmp.is_le(h) : Bool}
def priority_reads_without_excess(h, l, fits):
  match h:
    case LT{}:
      {==}
    case GT{}:
      {==}
    case EQ{}:
      fits

law blocks_limit_lower:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +limit: Word(n)
  {Cmp.is_ge(Word.cmp(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, Word.zero(k), limit))) ==
    Cmp.is_ge(Word.cmp(n, hi, limit)) : Bool}
def blocks_limit_lower(k, n, lo, hi, limit):
  %Equal.sym(Cmp,
    Word.cmp(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, Word.zero(k), limit)),
    O.priority(Word.cmp(n, hi, limit), Word.cmp(k, lo, Word.zero(k))),
    X.compare_blocks(k, n, lo, Word.zero(k), hi, limit)) :
    {Cmp.is_ge(_) == Cmp.is_ge(Word.cmp(n, hi, limit)) : Bool}
  priority_ge_without_negative(Word.cmp(n, hi, limit), Word.cmp(k, lo, Word.zero(k)), word_greater_equal_zero(k, lo))

law blocks_limit_upper:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +limit: Word(n)
  {Cmp.is_le(Word.cmp(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, W.ones(k), limit))) ==
    Cmp.is_le(Word.cmp(n, hi, limit)) : Bool}
def blocks_limit_upper(k, n, lo, hi, limit):
  %Equal.sym(Cmp,
    Word.cmp(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, W.ones(k), limit)),
    O.priority(Word.cmp(n, hi, limit), Word.cmp(k, lo, W.ones(k))),
    X.compare_blocks(k, n, lo, W.ones(k), hi, limit)) :
    {Cmp.is_le(_) == Cmp.is_le(Word.cmp(n, hi, limit)) : Bool}
  priority_reads_without_excess(Word.cmp(n, hi, limit), Word.cmp(k, lo, W.ones(k)), word_less_equal_ones(k, lo))

law priority_reads_implies_hi:
  for h: Cmp
  for l: Cmp
  for fits: {Cmp.is_le(O.priority(h, l)) == True{} : Bool}
  {Cmp.is_le(h) == True{} : Bool}
def priority_reads_implies_hi(h, l, fits):
  match h:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      fits

law blocks_limit_hi:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  for +limlo: Word(k)
  for +limhi: Word(n)
  for fits: {Cmp.is_le(Word.cmp(Nat.add(k, n), W.join(k, n, lo, hi), W.join(k, n, limlo, limhi))) == True{} : Bool}
  {Cmp.is_le(Word.cmp(n, hi, limhi)) == True{} : Bool}
def blocks_limit_hi(k, n, lo, hi, limlo, limhi, fits):
  priority_reads_implies_hi(Word.cmp(n, hi, limhi), Word.cmp(k, lo, limlo),
    (%X.compare_blocks(k, n, lo, limlo, hi, limhi) :
      {Cmp.is_le(_) == True{} : Bool} fits))

law lt_false_and_ge:
  for c: Cmp
  for e: {Cmp.is_lt(c) == False{} : Bool}
  {Cmp.is_ge(c) == True{} : Bool}
def lt_false_and_ge(c, e):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      F.absurd_boolean({False{} == True{} : Bool}, Equal.sym(Bool, True{}, False{}, e))

law prefix2_lt_128:
  for +lo: Word(5n)
  {U32.is_lt(prefix2(lo), 128) == False{} : Bool}
def prefix2_lt_128(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c),
    U32.cmp(prefix2(lo), 128), GT{},
    X.compare_blocks(5n, 27n, lo, W.adjust(5n, 32n, X.bits(0)),
      W.adjust(27n, 32n, X.bits(6)), W.adjust(27n, 32n, X.bits(4))))

law prefix2_ge_194:
  for +lo: Word(5n)
  {U32.is_ge(prefix2(lo), 194) == Cmp.is_ge(Word.cmp(5n, lo, W.adjust(5n, 32n, X.bits(2)))) : Bool}
def prefix2_ge_194(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefix2(lo), 194), Word.cmp(5n, lo, W.adjust(5n, 32n, X.bits(2))),
    X.compare_blocks(5n, 27n, lo, W.adjust(5n, 32n, X.bits(2)),
      W.adjust(27n, 32n, X.bits(6)), W.adjust(27n, 32n, X.bits(6))))

law prefix2_reads_223:
  for +lo: Word(5n)
  {U32.is_le(prefix2(lo), 223) == True{} : Bool}
def prefix2_reads_223(lo):
  blocks_limit_upper(5n, 27n, lo, W.adjust(27n, 32n, X.bits(6)), W.adjust(27n, 32n, X.bits(6)))

law prefix2_subtract:
  for +lo: Word(5n)
  {(prefix2(lo) - 192 : U32) == U32{W.join(5n, 27n, lo, Word.zero(27n))} : U32}
def prefix2_subtract(lo):
  Equal.cong(Word(32n), U32, w => U32{w},
    X.bits((prefix2(lo) - 192 : U32)), W.join(5n, 27n, lo, Word.zero(27n)),
    X.subtract_blocks(5n, 27n, lo, W.adjust(27n, 32n, X.bits(6)), W.adjust(27n, 32n, X.bits(6))))

law prefix3_lt_128:
  for +lo: Word(4n)
  {U32.is_lt(prefix3(lo), 128) == False{} : Bool}
def prefix3_lt_128(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c),
    U32.cmp(prefix3(lo), 128), GT{},
    X.compare_blocks(4n, 28n, lo, W.adjust(4n, 32n, X.bits(0)),
      W.adjust(28n, 32n, X.bits(14)), W.adjust(28n, 32n, X.bits(8))))

law prefix3_ge_194:
  for +lo: Word(4n)
  {U32.is_ge(prefix3(lo), 194) == True{} : Bool}
def prefix3_ge_194(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefix3(lo), 194), GT{},
    X.compare_blocks(4n, 28n, lo, W.adjust(4n, 32n, X.bits(2)),
      W.adjust(28n, 32n, X.bits(14)), W.adjust(28n, 32n, X.bits(12))))

law prefix3_reads_223:
  for +lo: Word(4n)
  {U32.is_le(prefix3(lo), 223) == False{} : Bool}
def prefix3_reads_223(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefix3(lo), 223), GT{},
    X.compare_blocks(4n, 28n, lo, W.adjust(4n, 32n, X.bits(15)),
      W.adjust(28n, 32n, X.bits(14)), W.adjust(28n, 32n, X.bits(13))))

law prefix3_ge_224:
  for +lo: Word(4n)
  {U32.is_ge(prefix3(lo), 224) == True{} : Bool}
def prefix3_ge_224(lo):
  blocks_limit_lower(4n, 28n, lo, W.adjust(28n, 32n, X.bits(14)), W.adjust(28n, 32n, X.bits(14)))

law prefix3_reads_239:
  for +lo: Word(4n)
  {U32.is_le(prefix3(lo), 239) == True{} : Bool}
def prefix3_reads_239(lo):
  blocks_limit_upper(4n, 28n, lo, W.adjust(28n, 32n, X.bits(14)), W.adjust(28n, 32n, X.bits(14)))

law prefix3_subtract:
  for +lo: Word(4n)
  {(prefix3(lo) - 224 : U32) == U32{W.join(4n, 28n, lo, Word.zero(28n))} : U32}
def prefix3_subtract(lo):
  Equal.cong(Word(32n), U32, w => U32{w},
    X.bits((prefix3(lo) - 224 : U32)), W.join(4n, 28n, lo, Word.zero(28n)),
    X.subtract_blocks(4n, 28n, lo, W.adjust(28n, 32n, X.bits(14)), W.adjust(28n, 32n, X.bits(14))))

law prefix4_lt_128:
  for +lo: Word(3n)
  {U32.is_lt(prefix4(lo), 128) == False{} : Bool}
def prefix4_lt_128(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_lt(c),
    U32.cmp(prefix4(lo), 128), GT{},
    X.compare_blocks(3n, 29n, lo, W.adjust(3n, 32n, X.bits(0)),
      W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(16))))

law prefix4_ge_194:
  for +lo: Word(3n)
  {U32.is_ge(prefix4(lo), 194) == True{} : Bool}
def prefix4_ge_194(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefix4(lo), 194), GT{},
    X.compare_blocks(3n, 29n, lo, W.adjust(3n, 32n, X.bits(2)),
      W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(24))))

law prefix4_reads_223:
  for +lo: Word(3n)
  {U32.is_le(prefix4(lo), 223) == False{} : Bool}
def prefix4_reads_223(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefix4(lo), 223), GT{},
    X.compare_blocks(3n, 29n, lo, W.adjust(3n, 32n, X.bits(7)),
      W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(27))))

law prefix4_ge_224:
  for +lo: Word(3n)
  {U32.is_ge(prefix4(lo), 224) == True{} : Bool}
def prefix4_ge_224(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
    U32.cmp(prefix4(lo), 224), GT{},
    X.compare_blocks(3n, 29n, lo, W.adjust(3n, 32n, X.bits(0)),
      W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(28))))

law prefix4_reads_239:
  for +lo: Word(3n)
  {U32.is_le(prefix4(lo), 239) == False{} : Bool}
def prefix4_reads_239(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefix4(lo), 239), GT{},
    X.compare_blocks(3n, 29n, lo, W.adjust(3n, 32n, X.bits(7)),
      W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(29))))

law prefix4_ge_240:
  for +lo: Word(3n)
  {U32.is_ge(prefix4(lo), 240) == True{} : Bool}
def prefix4_ge_240(lo):
  blocks_limit_lower(3n, 29n, lo, W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(30)))

law prefix4_reads_244:
  for +lo: Word(3n)
  {U32.is_le(prefix4(lo), 244) == Cmp.is_le(Word.cmp(3n, lo, W.adjust(3n, 32n, X.bits(4)))) : Bool}
def prefix4_reads_244(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
    U32.cmp(prefix4(lo), 244), Word.cmp(3n, lo, W.adjust(3n, 32n, X.bits(4))),
    X.compare_blocks(3n, 29n, lo, W.adjust(3n, 32n, X.bits(4)),
      W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(30))))

law prefix4_subtract:
  for +lo: Word(3n)
  {(prefix4(lo) - 240 : U32) == U32{W.join(3n, 29n, lo, Word.zero(29n))} : U32}
def prefix4_subtract(lo):
  Equal.cong(Word(32n), U32, w => U32{w},
    X.bits((prefix4(lo) - 240 : U32)), W.join(3n, 29n, lo, Word.zero(29n)),
    X.subtract_blocks(3n, 29n, lo, W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(30))))

law continuation_ge_128:
  for +lo: Word(6n)
  {U32.is_ge(X.continuation(lo), 128) == True{} : Bool}
def continuation_ge_128(lo):
  blocks_limit_lower(6n, 26n, lo, W.adjust(26n, 32n, X.bits(2)), W.adjust(26n, 32n, X.bits(2)))

law continuation_reads_191:
  for +lo: Word(6n)
  {U32.is_le(X.continuation(lo), 191) == True{} : Bool}
def continuation_reads_191(lo):
  blocks_limit_upper(6n, 26n, lo, W.adjust(26n, 32n, X.bits(2)), W.adjust(26n, 32n, X.bits(2)))

law scalar2_minimum:
  for +hi: Word(5n)
  for +lo: Word(6n)
  {U32.is_ge(X.scalar2(hi, lo), 128) == U32.is_ge(prefix2(hi), 194) : Bool}
def scalar2_minimum(hi, lo):
  Equal.trans(Bool, U32.is_ge(X.scalar2(hi, lo), 128),
    Cmp.is_ge(Word.cmp(26n, W.join(5n, 21n, hi, Word.zero(21n)), W.adjust(26n, 32n, X.bits(2)))),
    U32.is_ge(prefix2(hi), 194),
    blocks_limit_lower(6n, 26n, lo, W.join(5n, 21n, hi, Word.zero(21n)), W.adjust(26n, 32n, X.bits(2))),
    Equal.trans(Bool,
      Cmp.is_ge(Word.cmp(26n, W.join(5n, 21n, hi, Word.zero(21n)), W.adjust(26n, 32n, X.bits(2)))),
      Cmp.is_ge(Word.cmp(5n, hi, W.adjust(5n, 32n, X.bits(2)))), U32.is_ge(prefix2(hi), 194),
      Equal.cong(Cmp, Bool, c => Cmp.is_ge(c),
        Word.cmp(26n, W.join(5n, 21n, hi, Word.zero(21n)), W.adjust(26n, 32n, X.bits(2))),
        Word.cmp(5n, hi, W.adjust(5n, 32n, X.bits(2))),
        X.compare_blocks(5n, 21n, hi, W.adjust(5n, 32n, X.bits(2)), Word.zero(21n), Word.zero(21n))),
      Equal.sym(Bool, U32.is_ge(prefix2(hi), 194), Cmp.is_ge(Word.cmp(5n, hi, W.adjust(5n, 32n, X.bits(2)))), prefix2_ge_194(hi))))

law start_two:
  for +hi: Word(5n)
  for +lo: Word(6n)
  for minimum: {U32.is_ge(X.scalar2(hi, lo), 128) == True{} : Bool}
  {C.step_utf8(C.Start{}, prefix2(hi)) ==
    C.Partial{C.Continue{1n, U32{W.join(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Scalar}
def start_two(hi, lo, minimum):
  %Equal.sym(Bool, U32.is_lt(prefix2(hi), 128), False{}, prefix2_lt_128(hi)) :
    {C.start_utf8(_, U32.is_ge(prefix2(hi), 194) && U32.is_le(prefix2(hi), 223), U32.is_ge(prefix2(hi), 224) && U32.is_le(prefix2(hi), 239), U32.is_ge(prefix2(hi), 240) && U32.is_le(prefix2(hi), 244), prefix2(hi)) == C.Partial{C.Continue{1n, U32{W.join(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Scalar}
  %Equal.sym(Bool, U32.is_ge(prefix2(hi), 194), True{},
    Equal.trans(Bool, U32.is_ge(prefix2(hi), 194), U32.is_ge(X.scalar2(hi, lo), 128), True{},
      Equal.sym(Bool, U32.is_ge(X.scalar2(hi, lo), 128), U32.is_ge(prefix2(hi), 194), scalar2_minimum(hi, lo)), minimum)) :
    {C.start_utf8(False{}, _ && U32.is_le(prefix2(hi), 223), U32.is_ge(prefix2(hi), 224) && U32.is_le(prefix2(hi), 239), U32.is_ge(prefix2(hi), 240) && U32.is_le(prefix2(hi), 244), prefix2(hi)) == C.Partial{C.Continue{1n, U32{W.join(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Scalar}
  %Equal.sym(Bool, U32.is_le(prefix2(hi), 223), True{}, prefix2_reads_223(hi)) :
    {C.start_utf8(False{}, True{} && _, U32.is_ge(prefix2(hi), 224) && U32.is_le(prefix2(hi), 239), U32.is_ge(prefix2(hi), 240) && U32.is_le(prefix2(hi), 244), prefix2(hi)) == C.Partial{C.Continue{1n, U32{W.join(5n, 27n, hi, Word.zero(27n))}, 128}} : C.Scalar}
  Equal.cong(U32, C.Scalar, cp => C.Partial{C.Continue{1n, cp, 128}},
    (prefix2(hi) - 192 : U32), U32{W.join(5n, 27n, hi, Word.zero(27n))}, prefix2_subtract(hi))

law start_three:
  for +hi: Word(4n)
  {C.step_utf8(C.Start{}, prefix3(hi)) == C.Partial{C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Scalar}
def start_three(hi):
  %Equal.sym(Bool, U32.is_lt(prefix3(hi), 128), False{}, prefix3_lt_128(hi)) :
    {C.start_utf8(_, U32.is_ge(prefix3(hi), 194) && U32.is_le(prefix3(hi), 223), U32.is_ge(prefix3(hi), 224) && U32.is_le(prefix3(hi), 239), U32.is_ge(prefix3(hi), 240) && U32.is_le(prefix3(hi), 244), prefix3(hi)) == C.Partial{C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Scalar}
  %Equal.sym(Bool, U32.is_ge(prefix3(hi), 194), True{}, prefix3_ge_194(hi)) :
    {C.start_utf8(False{}, _ && U32.is_le(prefix3(hi), 223), U32.is_ge(prefix3(hi), 224) && U32.is_le(prefix3(hi), 239), U32.is_ge(prefix3(hi), 240) && U32.is_le(prefix3(hi), 244), prefix3(hi)) == C.Partial{C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Scalar}
  %Equal.sym(Bool, U32.is_le(prefix3(hi), 223), False{}, prefix3_reads_223(hi)) :
    {C.start_utf8(False{}, True{} && _, U32.is_ge(prefix3(hi), 224) && U32.is_le(prefix3(hi), 239), U32.is_ge(prefix3(hi), 240) && U32.is_le(prefix3(hi), 244), prefix3(hi)) == C.Partial{C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Scalar}
  %Equal.sym(Bool, U32.is_ge(prefix3(hi), 224), True{}, prefix3_ge_224(hi)) :
    {C.start_utf8(False{}, True{} && False{}, _ && U32.is_le(prefix3(hi), 239), U32.is_ge(prefix3(hi), 240) && U32.is_le(prefix3(hi), 244), prefix3(hi)) == C.Partial{C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Scalar}
  %Equal.sym(Bool, U32.is_le(prefix3(hi), 239), True{}, prefix3_reads_239(hi)) :
    {C.start_utf8(False{}, True{} && False{}, True{} && _, U32.is_ge(prefix3(hi), 240) && U32.is_le(prefix3(hi), 244), prefix3(hi)) == C.Partial{C.Continue{2n, U32{W.join(4n, 28n, hi, Word.zero(28n))}, 2048}} : C.Scalar}
  Equal.cong(U32, C.Scalar, cp => C.Partial{C.Continue{2n, cp, 2048}},
    (prefix3(hi) - 224 : U32), U32{W.join(4n, 28n, hi, Word.zero(28n))}, prefix3_subtract(hi))

law start_four:
  for +hi: Word(3n)
  for fits: {U32.is_le(prefix4(hi), 244) == True{} : Bool}
  {C.step_utf8(C.Start{}, prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
def start_four(hi, fits):
  %Equal.sym(Bool, U32.is_lt(prefix4(hi), 128), False{}, prefix4_lt_128(hi)) :
    {C.start_utf8(_, U32.is_ge(prefix4(hi), 194) && U32.is_le(prefix4(hi), 223), U32.is_ge(prefix4(hi), 224) && U32.is_le(prefix4(hi), 239), U32.is_ge(prefix4(hi), 240) && U32.is_le(prefix4(hi), 244), prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
  %Equal.sym(Bool, U32.is_ge(prefix4(hi), 194), True{}, prefix4_ge_194(hi)) :
    {C.start_utf8(False{}, _ && U32.is_le(prefix4(hi), 223), U32.is_ge(prefix4(hi), 224) && U32.is_le(prefix4(hi), 239), U32.is_ge(prefix4(hi), 240) && U32.is_le(prefix4(hi), 244), prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
  %Equal.sym(Bool, U32.is_le(prefix4(hi), 223), False{}, prefix4_reads_223(hi)) :
    {C.start_utf8(False{}, True{} && _, U32.is_ge(prefix4(hi), 224) && U32.is_le(prefix4(hi), 239), U32.is_ge(prefix4(hi), 240) && U32.is_le(prefix4(hi), 244), prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
  %Equal.sym(Bool, U32.is_ge(prefix4(hi), 224), True{}, prefix4_ge_224(hi)) :
    {C.start_utf8(False{}, True{} && False{}, _ && U32.is_le(prefix4(hi), 239), U32.is_ge(prefix4(hi), 240) && U32.is_le(prefix4(hi), 244), prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
  %Equal.sym(Bool, U32.is_le(prefix4(hi), 239), False{}, prefix4_reads_239(hi)) :
    {C.start_utf8(False{}, True{} && False{}, True{} && _, U32.is_ge(prefix4(hi), 240) && U32.is_le(prefix4(hi), 244), prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
  %Equal.sym(Bool, U32.is_ge(prefix4(hi), 240), True{}, prefix4_ge_240(hi)) :
    {C.start_utf8(False{}, True{} && False{}, True{} && False{}, _ && U32.is_le(prefix4(hi), 244), prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
  %Equal.sym(Bool, U32.is_le(prefix4(hi), 244), True{}, fits) :
    {C.start_utf8(False{}, True{} && False{}, True{} && False{}, True{} && _, prefix4(hi)) == C.Partial{C.Continue{3n, U32{W.join(3n, 29n, hi, Word.zero(29n))}, 65536}} : C.Scalar}
  Equal.cong(U32, C.Scalar, cp => C.Partial{C.Continue{3n, cp, 65536}},
    (prefix4(hi) - 240 : U32), U32{W.join(3n, 29n, hi, Word.zero(29n))}, prefix4_subtract(hi))

law step_continuation:
  for +n: Nat
  for +cp: U32
  for +minimum: U32
  for +lo: Word(6n)
  {C.step_utf8(C.Continue{1n+n, cp, minimum}, X.continuation(lo)) ==
    C.complete_utf8(n, U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, X.bits(cp)))}, minimum) : C.Scalar}
def step_continuation(n, cp, minimum, lo):
  %Equal.sym(Bool, U32.is_ge(X.continuation(lo), 128), True{}, continuation_ge_128(lo)) :
    {C.resume_utf8(_ && U32.is_le(X.continuation(lo), 191), n, cp, minimum, X.continuation(lo)) == C.complete_utf8(n, U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, X.bits(cp)))}, minimum) : C.Scalar}
  %Equal.sym(Bool, U32.is_le(X.continuation(lo), 191), True{}, continuation_reads_191(lo)) :
    {C.resume_utf8(True{} && _, n, cp, minimum, X.continuation(lo)) == C.complete_utf8(n, U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, X.bits(cp)))}, minimum) : C.Scalar}
  Equal.cong(U32, C.Scalar, z => C.complete_utf8(n, z, minimum),
    (cp * 64 + X.continuation(lo) - 128 : U32), U32{W.join(6n, 26n, lo, W.adjust(26n, 32n, X.bits(cp)))}, X.resume_reconstructs_six_bits_exact(cp, lo))

law scalar4_prefix_bounded:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for valid: {B.code_valid(X.scalar4(hi, b0, b1, b2)) == True{} : Bool}
  {U32.is_le(prefix4(hi), 244) == True{} : Bool}
def scalar4_prefix_bounded(hi, b0, b1, b2, valid):
  match b0 b1 b2:
    case WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}} WCon{+b20, WCon{+b21, WCon{+b22, WCon{+b23, WCon{+b24, WCon{+b25, WNil{}}}}}}}:
      +limit = F.and_boolean_left(U32.is_le(X.scalar4(hi, b0, b1, b2), 1114111),
        U32.is_lt(X.scalar4(hi, b0, b1, b2), 55296) || U32.is_gt(X.scalar4(hi, b0, b1, b2), 57343), valid)
      +high = blocks_limit_hi(18n, 14n, W.join(6n, 12n, b2, W.join(6n, 6n, b1, b0)),
        W.join(3n, 11n, hi, Word.zero(11n)), W.adjust(18n, 32n, X.bits(65535)), W.adjust(14n, 32n, X.bits(4)), limit)
      %Equal.sym(Bool, U32.is_le(prefix4(hi), 244), Cmp.is_le(Word.cmp(3n, hi, W.adjust(3n, 32n, X.bits(4)))), prefix4_reads_244(hi)) :
        {_ == True{} : Bool}
      Equal.trans(Bool,
        Cmp.is_le(Word.cmp(3n, hi, W.adjust(3n, 32n, X.bits(4)))),
        Cmp.is_le(Word.cmp(14n, W.join(3n, 11n, hi, Word.zero(11n)), W.adjust(14n, 32n, X.bits(4)))), True{},
        Equal.cong(Cmp, Bool, c => Cmp.is_le(c),
          Word.cmp(3n, hi, W.adjust(3n, 32n, X.bits(4))),
          Word.cmp(14n, W.join(3n, 11n, hi, Word.zero(11n)), W.adjust(14n, 32n, X.bits(4))),
          Equal.sym(Cmp,
            Word.cmp(14n, W.join(3n, 11n, hi, Word.zero(11n)), W.adjust(14n, 32n, X.bits(4))),
            Word.cmp(3n, hi, W.adjust(3n, 32n, X.bits(4))),
            X.compare_blocks(3n, 11n, hi, W.adjust(3n, 32n, X.bits(4)), Word.zero(11n), Word.zero(11n)))), high)
