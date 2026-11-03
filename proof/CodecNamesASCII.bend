# Contract names are ASCII: UTF-8 measure equals character count.
# Actual Char ranges are proved in CodecNamesChar.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ./Foundations.bend as F
import ./CodecUnicode.bend as U
import ./CodecNamesChar.bend as H

def text_ascii(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{Chr{cp}, t}:
      U32.is_lt(cp, 128) && text_ascii(t)

law rest_name_and_ascii:
  for +s: String
  for +valid: {D.rest_name(s) == True{} : Bool}
  {text_ascii(s) == True{} : Bool}
def rest_name_and_ascii(s, valid):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      F.and_boolean_intro(U32.is_lt(cp, 128), text_ascii(t),
        H.rest_character_and_ascii(cp,
          F.and_boolean_left(D.start_name(Chr{cp}) || Char.is_digit(Chr{cp}), D.rest_name(t), valid)),
        rest_name_and_ascii(t,
          F.and_boolean_right(D.start_name(Chr{cp}) || Char.is_digit(Chr{cp}), D.rest_name(t), valid)))

law name_valid_and_ascii:
  for +s: String
  for valid: {D.name_valid(s) == True{} : Bool}
  {text_ascii(s) == True{} : Bool}
def name_valid_and_ascii(s, valid):
  match s:
    case SNil{}:
      F.absurd_boolean({True{} == True{} : Bool}, valid)
    case SCon{Chr{+cp}, +t}:
      +characters = F.and_boolean_left(D.start_name(Chr{cp}) && D.rest_name(t),
        Nat.is_le(String.length(SCon{Chr{cp}, t}), 64n), valid)
      F.and_boolean_intro(U32.is_lt(cp, 128), text_ascii(t),
        H.start_name_and_ascii(cp, F.and_boolean_left(D.start_name(Chr{cp}), D.rest_name(t), characters)),
        rest_name_and_ascii(t, F.and_boolean_right(D.start_name(Chr{cp}), D.rest_name(t), characters)))

law ascii_and_code_valid:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {B.code_valid(cp) == True{} : Bool}
def ascii_and_code_valid(cp, ascii):
  Equal.trans(Bool, B.code_valid(cp), D.scalar_valid(cp), True{},
    U.predicates_unicode_agree(cp), U.ascii_and_scalar(cp, ascii))

law text_ascii_and_valid:
  for +s: String
  for +ascii: {text_ascii(s) == True{} : Bool}
  {B.text_valid(s) == True{} : Bool}
def text_ascii_and_valid(s, ascii):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      F.and_boolean_intro(B.code_valid(cp), B.text_valid(t),
        ascii_and_code_valid(cp, F.and_boolean_left(U32.is_lt(cp, 128), text_ascii(t), ascii)),
        text_ascii_and_valid(t, F.and_boolean_right(U32.is_lt(cp, 128), text_ascii(t), ascii)))

law code_ascii_emits_one_octet:
  for +cp: U32
  for ascii: {U32.is_lt(cp, 128) == True{} : Bool}
  {B.utf8_code(cp) == Con{cp, Nil{}} : List<&2, U32>}
def code_ascii_emits_one_octet(cp, ascii):
  %Equal.sym(Bool, U32.is_lt(cp, 128), True{}, ascii) :
    {B.utf8_code_emit(cp, _, U32.is_lt(cp, 2048), U32.is_lt(cp, 65536)) == Con{cp, Nil{}} : List<&2, U32>}
  {==}

law text_ascii_has_one_octet_by_character:
  for +s: String
  for +ascii: {text_ascii(s) == True{} : Bool}
  {B.length(B.utf8(s)) == String.length(s) : Nat}
def text_ascii_has_one_octet_by_character(s, ascii):
  match s:
    case SNil{}:
      {==}
    case SCon{Chr{+cp}, +t}:
      %Equal.sym(List<&2, U32>, B.utf8_code(cp), Con{cp, Nil{}},
        code_ascii_emits_one_octet(cp, F.and_boolean_left(U32.is_lt(cp, 128), text_ascii(t), ascii))) :
        {B.length(B.concatenate(_, B.utf8(t))) == 1n+String.length(t) : Nat}
      Equal.cong(Nat, Nat, n => 1n+n, B.length(B.utf8(t)), String.length(t),
        text_ascii_has_one_octet_by_character(t,
          F.and_boolean_right(U32.is_lt(cp, 128), text_ascii(t), ascii)))

law name_valid_and_text_valid:
  for +s: String
  for valid: {D.name_valid(s) == True{} : Bool}
  {B.text_valid(s) == True{} : Bool}
def name_valid_and_text_valid(s, valid):
  text_ascii_and_valid(s, name_valid_and_ascii(s, valid))

law name_valid_utf8_has_length_exact:
  for +s: String
  for valid: {D.name_valid(s) == True{} : Bool}
  {B.length(B.utf8(s)) == String.length(s) : Nat}
def name_valid_utf8_has_length_exact(s, valid):
  text_ascii_has_one_octet_by_character(s, name_valid_and_ascii(s, valid))

law name_valid_has_until64_characters:
  for +s: String
  for valid: {D.name_valid(s) == True{} : Bool}
  {Nat.is_le(String.length(s), 64n) == True{} : Bool}
def name_valid_has_until64_characters(s, valid):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, +t}:
      F.and_boolean_right(D.start_name(h) && D.rest_name(t),
        Nat.is_le(String.length(SCon{h, t}), 64n), valid)

law name_valid_utf8_has_until64_octets:
  for +s: String
  for +valid: {D.name_valid(s) == True{} : Bool}
  {Nat.is_le(B.length(B.utf8(s)), 64n) == True{} : Bool}
def name_valid_utf8_has_until64_octets(s, valid):
  Equal.trans(Bool, Nat.is_le(B.length(B.utf8(s)), 64n), Nat.is_le(String.length(s), 64n), True{},
    Equal.cong(Nat, Bool, n => Nat.is_le(n, 64n), B.length(B.utf8(s)), String.length(s),
      name_valid_utf8_has_length_exact(s, valid)),
    name_valid_has_until64_characters(s, valid))
