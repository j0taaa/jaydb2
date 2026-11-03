# Characters accepted in contract names belong to ASCII.
# Uses actual Base ranges, without enumerating U32 values.
import Base
import ../contract/Data.bend as D
import ./Foundations.bend as F
import ./Orders.bend as O
import ./CodecUnicode.bend as U

# Constructive elimination of Boolean disjunction.
def or_boolean_eliminate(a: Bool, -b: Bool, -A: Type,
  accepted: {a || b == True{} : Bool},
  left: {a == True{} : Bool} -> A,
  right: {b == True{} : Bool} -> A) -> A:
  match a:
    case False{}:
      right(accepted)
    case True{}:
      left({==})

law uppercase_and_ascii:
  for +cp: U32
  for accepted: {Char.is_upper(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def uppercase_and_ascii(cp, accepted):
  reads = F.and_boolean_right(U32.is_ge(cp, 65), U32.is_le(cp, 90), accepted)
  lt = Equal.trans(Bool, U32.is_lt(cp, 91), U32.is_le(cp, 90), True{},
    Equal.sym(Bool, U32.is_le(cp, 90), U32.is_lt(cp, 91),
      U.limit_u32_successor(cp, 90, {==})), reads)
  U.u32_lt_transitive(cp, 91, 128, lt, {==})

law lowercase_and_ascii:
  for +cp: U32
  for accepted: {Char.is_lower(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def lowercase_and_ascii(cp, accepted):
  reads = F.and_boolean_right(U32.is_ge(cp, 97), U32.is_le(cp, 122), accepted)
  lt = Equal.trans(Bool, U32.is_lt(cp, 123), U32.is_le(cp, 122), True{},
    Equal.sym(Bool, U32.is_le(cp, 122), U32.is_lt(cp, 123),
      U.limit_u32_successor(cp, 122, {==})), reads)
  U.u32_lt_transitive(cp, 123, 128, lt, {==})

law alpha_and_ascii:
  for +cp: U32
  for accepted: {Char.is_alpha(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def alpha_and_ascii(cp, accepted):
  or_boolean_eliminate(Char.is_upper(Chr{cp}), Char.is_lower(Chr{cp}),
    {U32.is_lt(cp, 128) == True{} : Bool}, accepted,
    uppercase => uppercase_and_ascii(cp, uppercase),
    lowercase => lowercase_and_ascii(cp, lowercase))

law digit_and_ascii:
  for +cp: U32
  for accepted: {Char.is_digit(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def digit_and_ascii(cp, accepted):
  reads = F.and_boolean_right(U32.is_ge(cp, 48), U32.is_le(cp, 57), accepted)
  lt = Equal.trans(Bool, U32.is_lt(cp, 58), U32.is_le(cp, 57), True{},
    Equal.sym(Bool, U32.is_le(cp, 57), U32.is_lt(cp, 58),
      U.limit_u32_successor(cp, 57, {==})), reads)
  U.u32_lt_transitive(cp, 58, 128, lt, {==})

law underscore_and_ascii:
  for +cp: U32
  for accepted: {Char.is_eq(Chr{cp}, '_') == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def underscore_and_ascii(cp, accepted):
  %Equal.sym(U32, cp, 95,
    O.u32_equal(cp, 95, O.cmp_eq(U32.cmp(cp, 95), accepted))) :
    {U32.is_lt(_, 128) == True{} : Bool}
  {==}

law start_name_and_ascii:
  for +cp: U32
  for accepted: {D.start_name(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def start_name_and_ascii(cp, accepted):
  or_boolean_eliminate(Char.is_alpha(Chr{cp}), Char.is_eq(Chr{cp}, '_'),
    {U32.is_lt(cp, 128) == True{} : Bool}, accepted,
    alpha => alpha_and_ascii(cp, alpha),
    underscore => underscore_and_ascii(cp, underscore))

law rest_character_and_ascii:
  for +cp: U32
  for accepted: {D.start_name(Chr{cp}) || Char.is_digit(Chr{cp}) == True{} : Bool}
  {U32.is_lt(cp, 128) == True{} : Bool}
def rest_character_and_ascii(cp, accepted):
  or_boolean_eliminate(D.start_name(Chr{cp}), Char.is_digit(Chr{cp}),
    {U32.is_lt(cp, 128) == True{} : Bool}, accepted,
    start => start_name_and_ascii(cp, start),
    digit => digit_and_ascii(cp, digit))
