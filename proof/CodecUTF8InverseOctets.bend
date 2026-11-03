# The byte precheck accepts UTF-8 for every valid contract text.
import Base
import ../contract/Bytes.bend as B
import ./CodecUTF8Bits.bend as X
import ./CodecUTF8InverseBits.bend as I
import ./CodecUTF8Inverse.bend as E
import ./CodecWordsWord.bend as W
import ./CodecUnicode.bend as U
import ./Foundations.bend as F

law ascii_and_octet:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {U32.is_le(cp, 255) == True{} : Bool}
def ascii_and_octet(cp, ascii):
  Equal.trans(Bool, U32.is_le(cp, 255), U32.is_lt(cp, 256), True{},
    U.limit_u32_successor(cp, 255, {==}), U.u32_lt_transitive(cp, 128, 256, ascii, {==}))

law prefix2_and_octet:
  for +lo: Word(5n)
  {U32.is_le(I.prefix2(lo), 255) == True{} : Bool}
def prefix2_and_octet(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(I.prefix2(lo), 255), LT{},
    X.compare_blocks(5n, 27n, lo, W.adjust(5n, 32n, X.bits(31)),
      W.adjust(27n, 32n, X.bits(6)), W.adjust(27n, 32n, X.bits(7))))

law prefix3_and_octet:
  for +lo: Word(4n)
  {U32.is_le(I.prefix3(lo), 255) == True{} : Bool}
def prefix3_and_octet(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(I.prefix3(lo), 255), LT{},
    X.compare_blocks(4n, 28n, lo, W.adjust(4n, 32n, X.bits(15)),
      W.adjust(28n, 32n, X.bits(14)), W.adjust(28n, 32n, X.bits(15))))

law prefix4_and_octet:
  for +lo: Word(3n)
  {U32.is_le(I.prefix4(lo), 255) == True{} : Bool}
def prefix4_and_octet(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(I.prefix4(lo), 255), LT{},
    X.compare_blocks(3n, 29n, lo, W.adjust(3n, 32n, X.bits(7)),
      W.adjust(29n, 32n, X.bits(30)), W.adjust(29n, 32n, X.bits(31))))

law continuation_and_octet:
  for +lo: Word(6n)
  {U32.is_le(X.continuation(lo), 255) == True{} : Bool}
def continuation_and_octet(lo):
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), U32.cmp(X.continuation(lo), 255), LT{},
    X.compare_blocks(6n, 26n, lo, W.adjust(6n, 32n, X.bits(63)),
      W.adjust(26n, 32n, X.bits(2)), W.adjust(26n, 32n, X.bits(3))))

law form2_emits_octets:
  for +hi: Word(5n)
  for +b0: Word(6n)
  {B.octets_all_valid(B.utf8_code_emit(X.scalar2(hi, b0), False{}, True{}, False{})) == True{} : Bool}
def form2_emits_octets(hi, b0):
  %Equal.sym(List<&2, U32>, B.utf8_code_emit(X.scalar2(hi, b0), False{}, True{}, False{}), [I.prefix2(hi), X.continuation(b0)], X.utf8_form_2_bytes(hi, b0)) :
    {B.octets_all_valid(_) == True{} : Bool}
  F.and_boolean_intro(U32.is_le(I.prefix2(hi), 255), B.octets_all_valid([X.continuation(b0)]), prefix2_and_octet(hi), F.and_boolean_intro(U32.is_le(X.continuation(b0), 255), B.octets_all_valid([]), continuation_and_octet(b0), {==}))

law form3_emits_octets:
  for +hi: Word(4n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  {B.octets_all_valid(B.utf8_code_emit(X.scalar3(hi, b0, b1), False{}, False{}, True{})) == True{} : Bool}
def form3_emits_octets(hi, b0, b1):
  %Equal.sym(List<&2, U32>, B.utf8_code_emit(X.scalar3(hi, b0, b1), False{}, False{}, True{}), [I.prefix3(hi), X.continuation(b0), X.continuation(b1)], X.utf8_form_3_bytes(hi, b0, b1)) :
    {B.octets_all_valid(_) == True{} : Bool}
  F.and_boolean_intro(U32.is_le(I.prefix3(hi), 255), B.octets_all_valid([X.continuation(b0), X.continuation(b1)]), prefix3_and_octet(hi), F.and_boolean_intro(U32.is_le(X.continuation(b0), 255), B.octets_all_valid([X.continuation(b1)]), continuation_and_octet(b0), F.and_boolean_intro(U32.is_le(X.continuation(b1), 255), B.octets_all_valid([]), continuation_and_octet(b1), {==})))

law form4_emits_octets:
  for +hi: Word(3n)
  for +b0: Word(6n)
  for +b1: Word(6n)
  for +b2: Word(6n)
  {B.octets_all_valid(B.utf8_code_emit(X.scalar4(hi, b0, b1, b2), False{}, False{}, False{})) == True{} : Bool}
def form4_emits_octets(hi, b0, b1, b2):
  %Equal.sym(List<&2, U32>, B.utf8_code_emit(X.scalar4(hi, b0, b1, b2), False{}, False{}, False{}), [I.prefix4(hi), X.continuation(b0), X.continuation(b1), X.continuation(b2)], X.utf8_form_4_bytes(hi, b0, b1, b2)) :
    {B.octets_all_valid(_) == True{} : Bool}
  F.and_boolean_intro(U32.is_le(I.prefix4(hi), 255), B.octets_all_valid([X.continuation(b0), X.continuation(b1), X.continuation(b2)]), prefix4_and_octet(hi), F.and_boolean_intro(U32.is_le(X.continuation(b0), 255), B.octets_all_valid([X.continuation(b1), X.continuation(b2)]), continuation_and_octet(b0), F.and_boolean_intro(U32.is_le(X.continuation(b1), 255), B.octets_all_valid([X.continuation(b2)]), continuation_and_octet(b1), F.and_boolean_intro(U32.is_le(X.continuation(b2), 255), B.octets_all_valid([]), continuation_and_octet(b2), {==}))))

law code2_emits_octets:
  for +cp: U32
  for limit: {U32.is_lt(cp, 2048) == True{} : Bool}
  {B.octets_all_valid(B.utf8_code_emit(cp, False{}, True{}, False{})) == True{} : Bool}
def code2_emits_octets(cp, limit):
  %Equal.sym(U32, cp, X.scalar2(E.hi2(cp), E.lo6(cp)), E.code_form2(cp, limit)) :
    {B.octets_all_valid(B.utf8_code_emit(_, False{}, True{}, False{})) == True{} : Bool}
  form2_emits_octets(E.hi2(cp), E.lo6(cp))

law code3_emits_octets:
  for +cp: U32
  for limit: {U32.is_lt(cp, 65536) == True{} : Bool}
  {B.octets_all_valid(B.utf8_code_emit(cp, False{}, False{}, True{})) == True{} : Bool}
def code3_emits_octets(cp, limit):
  %Equal.sym(U32, cp, X.scalar3(E.hi3(cp), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp)), E.code_form3(cp, limit)) :
    {B.octets_all_valid(B.utf8_code_emit(_, False{}, False{}, True{})) == True{} : Bool}
  form3_emits_octets(E.hi3(cp), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp))

law code4_emits_octets:
  for +cp: U32
  for limit: {U32.is_lt(cp, 2097152) == True{} : Bool}
  {B.octets_all_valid(B.utf8_code_emit(cp, False{}, False{}, False{})) == True{} : Bool}
def code4_emits_octets(cp, limit):
  %Equal.sym(U32, cp, X.scalar4(E.hi4(cp), E.lo6(U32.shrn(cp, 12n)), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp)), E.code_form4(cp, limit)) :
    {B.octets_all_valid(B.utf8_code_emit(_, False{}, False{}, False{})) == True{} : Bool}
  form4_emits_octets(E.hi4(cp), E.lo6(U32.shrn(cp, 12n)), E.lo6(U32.shrn(cp, 6n)), E.lo6(cp))

law code_emits_octets_cases:
  for +cp: U32
  for ascii: Bool
  for two: Bool
  for three: Bool
  for a: {U32.is_lt(cp, 128) == ascii : Bool}
  for d: {U32.is_lt(cp, 2048) == two : Bool}
  for t: {U32.is_lt(cp, 65536) == three : Bool}
  for valid: {B.code_valid(cp) == True{} : Bool}
  {B.octets_all_valid(B.utf8_code_emit(cp, ascii, two, three)) == True{} : Bool}
def code_emits_octets_cases(cp, ascii, two, three, a, d, t, valid):
  match ascii two three:
    case True{} _ _:
      F.and_boolean_intro(U32.is_le(cp, 255), True{}, ascii_and_octet(cp, a), {==})
    case False{} True{} _:
      code2_emits_octets(cp, d)
    case False{} False{} True{}:
      code3_emits_octets(cp, t)
    case False{} False{} False{}:
      code4_emits_octets(cp, E.code_valid_fits_21_bits(cp, valid))

law utf8_code_valid_emits_octets:
  for +cp: U32
  for valid: {B.code_valid(cp) == True{} : Bool}
  {B.octets_all_valid(B.utf8_code(cp)) == True{} : Bool}
def utf8_code_valid_emits_octets(cp, valid):
  code_emits_octets_cases(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536), {==}, {==}, {==}, valid)

law concatenate_preserves_octets:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +va: {B.octets_all_valid(a) == True{} : Bool}
  for vb: {B.octets_all_valid(b) == True{} : Bool}
  {B.octets_all_valid(B.concatenate(a, b)) == True{} : Bool}
def concatenate_preserves_octets(a, b, va, vb):
  match a:
    case Nil{}:
      vb
    case Con{+h, +tail}:
      F.and_boolean_intro(U32.is_le(h, 255), B.octets_all_valid(B.concatenate(tail, b)),
        F.and_boolean_left(U32.is_le(h, 255), B.octets_all_valid(tail), va),
        concatenate_preserves_octets(tail, b, F.and_boolean_right(U32.is_le(h, 255), B.octets_all_valid(tail), va), vb))

law utf8_text_valid_emits_octets:
  for +s: String
  for +valid: {B.text_valid(s) == True{} : Bool}
  {B.octets_all_valid(B.utf8(s)) == True{} : Bool}
def utf8_text_valid_emits_octets(s, valid):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +tail}:
      concatenate_preserves_octets(B.utf8_code(cp), B.utf8(tail),
        utf8_code_valid_emits_octets(cp, F.and_boolean_left(B.code_valid(cp), B.text_valid(tail), valid)),
        utf8_text_valid_emits_octets(tail, F.and_boolean_right(B.code_valid(cp), B.text_valid(tail), valid)))
