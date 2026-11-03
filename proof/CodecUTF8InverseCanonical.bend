# Canonicity of accepted sections: preserves bytes, including zeros.
import Base
import ../contract/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecWordsWord.bend as W
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InverseBits.bend as I
import ./CodecUTF8Inverse.bend as E
import ./CodecUnicode.bend as U
import ./Foundations.bend as F
import ./Orders.bend as O

law ge_true_lt_false:
  for c: Cmp
  for e: {Cmp.is_ge(c) == True{} : Bool}
  {Cmp.is_lt(c) == False{} : Bool}
def ge_true_lt_false(c, e):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      F.absurd_boolean({True{} == False{} : Bool}, e)

def ge_compose(ab: Cmp, bc: Cmp, ac: Cmp, h: O.Coherent(ab, bc, ac),
  a: {Cmp.is_ge(ab) == True{} : Bool}, b: {Cmp.is_ge(bc) == True{} : Bool}) ->
  {Cmp.is_ge(ac) == True{} : Bool}:
  match ab bc:
    case LT{} _:
      F.absurd_boolean({Cmp.is_ge(ac) == True{} : Bool}, a)
    case _ LT{}:
      F.absurd_boolean({Cmp.is_ge(ac) == True{} : Bool}, b)
    case EQ{} EQ{}:
      %Equal.sym(Cmp, ac, EQ{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}
    case EQ{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}
    case GT{} EQ{}:
      %Equal.sym(Cmp, ac, GT{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}
    case GT{} GT{}:
      %Equal.sym(Cmp, ac, GT{}, h) : {Cmp.is_ge(_) == True{} : Bool}
      {==}

law ge_transitive:
  for +a: U32
  for +b: U32
  for +c: U32
  for ab: {U32.is_ge(a, b) == True{} : Bool}
  for bc: {U32.is_ge(b, c) == True{} : Bool}
  {U32.is_ge(a, c) == True{} : Bool}
def ge_transitive(a, b, c, ab, bc):
  ge_compose(U32.cmp(a, b), U32.cmp(b, c), U32.cmp(a, c), O.u32_coherent(a, b, c), ab, bc)

law tail_ge:
  for a: Bool
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_ge(Word.cmp.fin(a, b, c)) == True{} : Bool}
  {Cmp.is_ge(c) == True{} : Bool}
def tail_ge(a, b, c, e):
  match c:
    case EQ{}:
      {==}
    case GT{}:
      {==}
    case LT{}:
      e

law reads_ge_equal:
  for c: Cmp
  for reads: {Cmp.is_le(c) == True{} : Bool}
  for ge: {Cmp.is_ge(c) == True{} : Bool}
  {c == EQ{} : Cmp}
def reads_ge_equal(c, reads, ge):
  match c:
    case EQ{}:
      {==}
    case LT{}:
      F.absurd_boolean({LT{} == EQ{} : Cmp}, ge)
    case GT{}:
      F.absurd_boolean({GT{} == EQ{} : Cmp}, reads)

law word_between_blocks:
  for +k: Nat
  for +n: Nat
  for +w: Word(Nat.add(k, n))
  for +prefix: Word(n)
  for ge: {Cmp.is_ge(Word.cmp(Nat.add(k, n), w, W.join(k, n, Word.zero(k), prefix))) == True{} : Bool}
  for reads: {Cmp.is_le(Word.cmp(Nat.add(k, n), w, W.join(k, n, W.ones(k), prefix))) == True{} : Bool}
  {w == W.join(k, n, W.adjust(k, Nat.add(k, n), w), prefix) : Word(Nat.add(k, n))}
def word_between_blocks(k, n, w, prefix, ge, reads):
  match k:
    case 0n:
      O.word_equal(n, w, prefix, reads_ge_equal(Word.cmp(n, w, prefix), reads, ge))
    case 1n+p:
      match w:
        case WCon{b, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{b, r},
            t, W.join(p, n, W.adjust(p, Nat.add(p, n), t), prefix),
            word_between_blocks(p, n, t, prefix,
              tail_ge(b, False{}, Word.cmp(Nat.add(p, n), t, W.join(p, n, Word.zero(p), prefix)), ge),
              W.limit_of_tail(b, True{}, Word.cmp(Nat.add(p, n), t, W.join(p, n, W.ones(p), prefix)), reads)))

law continuation_reconstituted:
  for +b: U32
  for ge: {U32.is_ge(b, 128) == True{} : Bool}
  for reads: {U32.is_le(b, 191) == True{} : Bool}
  {b == X.continuation(E.lo6(b)) : U32}
def continuation_reconstituted(b, ge, reads):
  match b:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.join(6n, 26n, E.lo6(b), W.adjust(26n, 32n, X.bits(2))),
        word_between_blocks(6n, 26n, w, W.adjust(26n, 32n, X.bits(2)), ge, reads))

law prefix2_reconstituted:
  for +b: U32
  for ge: {U32.is_ge(b, 194) == True{} : Bool}
  for reads: {U32.is_le(b, 223) == True{} : Bool}
  {b == I.prefix2(W.adjust(5n, 32n, X.bits(b))) : U32}
def prefix2_reconstituted(b, ge, reads):
  match b:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.join(5n, 27n, W.adjust(5n, 32n, w), W.adjust(27n, 32n, X.bits(6))),
        word_between_blocks(5n, 27n, w, W.adjust(27n, 32n, X.bits(6)), ge_transitive(b, 194, 192, ge, {==}), reads))

law prefix3_reconstituted:
  for +b: U32
  for ge: {U32.is_ge(b, 224) == True{} : Bool}
  for reads: {U32.is_le(b, 239) == True{} : Bool}
  {b == I.prefix3(W.adjust(4n, 32n, X.bits(b))) : U32}
def prefix3_reconstituted(b, ge, reads):
  match b:
    case U32{w}:
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.join(4n, 28n, W.adjust(4n, 32n, w), W.adjust(28n, 32n, X.bits(14))),
        word_between_blocks(4n, 28n, w, W.adjust(28n, 32n, X.bits(14)), ge, reads))

law prefix4_reconstituted:
  for +b: U32
  for ge: {U32.is_ge(b, 240) == True{} : Bool}
  for reads: {U32.is_le(b, 244) == True{} : Bool}
  {b == I.prefix4(W.adjust(3n, 32n, X.bits(b))) : U32}
def prefix4_reconstituted(b, ge, reads):
  match b:
    case U32{w}:
      lt = Equal.trans(Bool, U32.is_lt(b, 245), U32.is_le(b, 244), True{},
        Equal.sym(Bool, U32.is_le(b, 244), U32.is_lt(b, 245), U.limit_u32_successor(b, 244, {==})), reads)
      ceiling = Equal.trans(Bool, U32.is_le(b, 247), U32.is_lt(b, 248), True{},
        U.limit_u32_successor(b, 247, {==}), U.u32_lt_transitive(b, 245, 248, lt, {==}))
      Equal.cong(Word(32n), U32, z => U32{z}, w,
        W.join(3n, 29n, W.adjust(3n, 32n, w), W.adjust(29n, 32n, X.bits(30))),
        word_between_blocks(3n, 29n, w, W.adjust(29n, 32n, X.bits(30)), ge, ceiling))

law form2_limit_upper:
  for +hi: Word(5n)
  for +b0: Word(6n)
  {U32.is_lt(X.scalar2(hi, b0), 2048) == True{} : Bool}
def form2_limit_upper(hi, b0):
  match hi b0:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WCon{+hi4, WNil{}}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}}:
      Equal.trans(Bool, U32.is_lt(X.scalar2(hi, b0), 2048), U32.is_le(X.scalar2(hi, b0), 2047), True{},
        Equal.sym(Bool, U32.is_le(X.scalar2(hi, b0), 2047), U32.is_lt(X.scalar2(hi, b0), 2048), U.limit_u32_successor(X.scalar2(hi, b0), 2047, {==})),
        I.blocks_limit_upper(11n, 21n, W.join(6n, 5n, b0, hi), Word.zero(21n), Word.zero(21n)))

law form3_limit_upper:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  {U32.is_lt(X.scalar3(hi, b0, b1), 65536) == True{} : Bool}
def form3_limit_upper(hi, b0, b1):
  match hi b0 b1:
    case WCon{+hi0, WCon{+hi1, WCon{+hi2, WCon{+hi3, WNil{}}}}} WCon{+b00, WCon{+b01, WCon{+b02, WCon{+b03, WCon{+b04, WCon{+b05, WNil{}}}}}}} WCon{+b10, WCon{+b11, WCon{+b12, WCon{+b13, WCon{+b14, WCon{+b15, WNil{}}}}}}}:
      Equal.trans(Bool, U32.is_lt(X.scalar3(hi, b0, b1), 65536), U32.is_le(X.scalar3(hi, b0, b1), 65535), True{},
        Equal.sym(Bool, U32.is_le(X.scalar3(hi, b0, b1), 65535), U32.is_lt(X.scalar3(hi, b0, b1), 65536), U.limit_u32_successor(X.scalar3(hi, b0, b1), 65535, {==})),
        I.blocks_limit_upper(16n, 16n, W.join(6n, 10n, b1, W.join(6n, 4n, b0, hi)), Word.zero(16n), Word.zero(16n)))

law form2_reencodes:
  for +hi: Word(5n)
  for +b0: Word(6n)
  for +minimum: {U32.is_ge(X.scalar2(hi, b0), 128) == True{} : Bool}
  {B.utf8_code(X.scalar2(hi, b0)) == [I.prefix2(hi), X.continuation(b0)] : List<&2, U32>}
def form2_reencodes(hi, b0, minimum):
  %Equal.sym(Bool, U32.is_lt(X.scalar2(hi, b0), 128), False{}, ge_true_lt_false(U32.cmp(X.scalar2(hi, b0), 128), minimum)) :
    {B.utf8_code_emit(X.scalar2(hi, b0), _, U32.is_lt(X.scalar2(hi, b0), 2048), U32.is_lt(X.scalar2(hi, b0), 65536)) == [I.prefix2(hi), X.continuation(b0)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.scalar2(hi, b0), 2048), True{}, form2_limit_upper(hi, b0)) :
    {B.utf8_code_emit(X.scalar2(hi, b0), False{}, _, U32.is_lt(X.scalar2(hi, b0), 65536)) == [I.prefix2(hi), X.continuation(b0)] : List<&2, U32>}
  X.utf8_form_2_bytes(hi, b0)

law form3_reencodes:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +minimum: {U32.is_ge(X.scalar3(hi, b0, b1), 2048) == True{} : Bool}
  {B.utf8_code(X.scalar3(hi, b0, b1)) == [I.prefix3(hi), X.continuation(b0), X.continuation(b1)] : List<&2, U32>}
def form3_reencodes(hi, b0, b1, minimum):
  %Equal.sym(Bool, U32.is_lt(X.scalar3(hi, b0, b1), 128), False{}, ge_true_lt_false(U32.cmp(X.scalar3(hi, b0, b1), 128), ge_transitive(X.scalar3(hi, b0, b1), 2048, 128, minimum, {==}))) :
    {B.utf8_code_emit(X.scalar3(hi, b0, b1), _, U32.is_lt(X.scalar3(hi, b0, b1), 2048), U32.is_lt(X.scalar3(hi, b0, b1), 65536)) == [I.prefix3(hi), X.continuation(b0), X.continuation(b1)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.scalar3(hi, b0, b1), 2048), False{}, ge_true_lt_false(U32.cmp(X.scalar3(hi, b0, b1), 2048), minimum)) :
    {B.utf8_code_emit(X.scalar3(hi, b0, b1), False{}, _, U32.is_lt(X.scalar3(hi, b0, b1), 65536)) == [I.prefix3(hi), X.continuation(b0), X.continuation(b1)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.scalar3(hi, b0, b1), 65536), True{}, form3_limit_upper(hi, b0, b1)) :
    {B.utf8_code_emit(X.scalar3(hi, b0, b1), False{}, False{}, _) == [I.prefix3(hi), X.continuation(b0), X.continuation(b1)] : List<&2, U32>}
  X.utf8_form_3_bytes(hi, b0, b1)

law form4_reencodes:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  for +minimum: {U32.is_ge(X.scalar4(hi, b0, b1, b2), 65536) == True{} : Bool}
  {B.utf8_code(X.scalar4(hi, b0, b1, b2)) == [I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(b2)] : List<&2, U32>}
def form4_reencodes(hi, b0, b1, b2, minimum):
  %Equal.sym(Bool, U32.is_lt(X.scalar4(hi, b0, b1, b2), 128), False{}, ge_true_lt_false(U32.cmp(X.scalar4(hi, b0, b1, b2), 128), ge_transitive(X.scalar4(hi, b0, b1, b2), 65536, 128, minimum, {==}))) :
    {B.utf8_code_emit(X.scalar4(hi, b0, b1, b2), _, U32.is_lt(X.scalar4(hi, b0, b1, b2), 2048), U32.is_lt(X.scalar4(hi, b0, b1, b2), 65536)) == [I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(b2)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.scalar4(hi, b0, b1, b2), 2048), False{}, ge_true_lt_false(U32.cmp(X.scalar4(hi, b0, b1, b2), 2048), ge_transitive(X.scalar4(hi, b0, b1, b2), 65536, 2048, minimum, {==}))) :
    {B.utf8_code_emit(X.scalar4(hi, b0, b1, b2), False{}, _, U32.is_lt(X.scalar4(hi, b0, b1, b2), 65536)) == [I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(b2)] : List<&2, U32>}
  %Equal.sym(Bool, U32.is_lt(X.scalar4(hi, b0, b1, b2), 65536), False{}, ge_true_lt_false(U32.cmp(X.scalar4(hi, b0, b1, b2), 65536), minimum)) :
    {B.utf8_code_emit(X.scalar4(hi, b0, b1, b2), False{}, False{}, _) == [I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(b2)] : List<&2, U32>}
  X.utf8_form_4_bytes(hi, b0, b1, b2)

law ascii_reencodes:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {B.utf8_code(cp) == [cp] : List<&2, U32>}
def ascii_reencodes(cp, ascii):
  %Equal.sym(Bool, U32.is_lt(cp, 128), True{}, ascii) :
    {B.utf8_code_emit(cp, _, U32.is_lt(cp, 2048), U32.is_lt(cp, 65536)) == [cp] : List<&2, U32>}
  {==}
