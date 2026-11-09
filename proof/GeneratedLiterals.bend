# Actual Generate.literal roundtrip through an independent restricted lexer.
# The lexer recognizes plain characters, escaped quote/backslash and exactly
# two hexadecimal digits in \\u{hh}, the subset the generator emits. Its grammar
# follows pinned Bend parse_char/quoted-string syntax; it is not the official
# frontend and no theorem here asserts frontend/compiler correctness.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Protocol.bend as P
import ../src/Generate.bend as G
import ../src/Reification.bend as R
import ./Foundations.bend as F
import ./Orders.bend as O
import ./CodecUnicode.bend as U
import ./CodecWordsWord.bend as W
import ./CodecCanonical.bend as K
import ./CodecLimitsSequences.bend as N
import ./Reification.bend as Reification

type Head is Data:
  Bad{}
  End{rest: String}
  Character{code: U32, rest: String}

type Parsed is Data:
  Invalid{}
  Literal{value: String, rest: String}

def hex_choice(decimal: Bool, lower: Bool, +n: U32) -> Maybe<&2, U32>:
  match decimal lower:
    case True{} _: Some{(n - 48 : U32)}
    case False{} True{}: Some{(n - 87 : U32)}
    case False{} False{}: None{}

def hex(+n: U32) -> Maybe<&2, U32>:
  hex_choice(U32.is_ge(n, 48) && U32.is_le(n, 57),
    U32.is_ge(n, 97) && U32.is_le(n, 102), n)

def hex_pair(valid: Bool, h: Maybe<&2, U32>, l: Maybe<&2, U32>, rest: String) -> Head:
  match valid h l:
    case True{} Some{high} Some{low}: Character{(high * 16 + low : U32), rest}
    case _ _ _: Bad{}

def unicode(raw: String) -> Head:
  match raw:
    case SCon{Chr{open}, SCon{Chr{h}, SCon{Chr{l}, SCon{Chr{close}, rest}}}}:
      hex_pair(U32.is_eq(open, 123) && U32.is_eq(close, 125), hex(h), hex(l), rest)
    case _: Bad{}

def escaped_choice(quote: Bool, slash: Bool, unicode_tag: Bool, rest: String) -> Head:
  match quote slash unicode_tag:
    case True{} _ _: Character{34, rest}
    case False{} True{} _: Character{92, rest}
    case False{} False{} True{}: unicode(rest)
    case False{} False{} False{}: Bad{}

def escaped(raw: String) -> Head:
  match raw:
    case SNil{}: Bad{}
    case SCon{Chr{+n}, rest}:
      escaped_choice(U32.is_eq(n, 34), U32.is_eq(n, 92), U32.is_eq(n, 117), rest)

def head_choice(quote: Bool, slash: Bool, n: U32, rest: String) -> Head:
  match quote slash:
    case True{} _: End{rest}
    case False{} True{}: escaped(rest)
    case False{} False{}: Character{n, rest}

def head(raw: String) -> Head:
  match raw:
    case SNil{}: Bad{}
    case SCon{Chr{+n}, rest}:
      head_choice(U32.is_eq(n, 34), U32.is_eq(n, 92), n, rest)

def prepend(n: U32, parsed: Parsed) -> Parsed:
  match parsed:
    case Invalid{}: Invalid{}
    case Literal{value, rest}: Literal{SCon{Chr{n}, value}, rest}

def consume(first: Head, resume: String -> Parsed) -> Parsed:
  match first:
    case Bad{}: Invalid{}
    case End{rest}: Literal{"", rest}
    case Character{n, rest}: prepend(n, resume(rest))

# Fuel counts decoded characters plus the closing delimiter. Exhaustion fails;
# it never supplies a fabricated string or scans past a closing quote.
def body(fuel: Nat, raw: String) -> Parsed:
  match fuel:
    case 0n: Invalid{}
    case 1n+k:
      consume(head(raw), rest => body(k, rest))

def opening(ok: Bool, fuel: Nat, rest: String) -> Parsed:
  match ok:
    case False{}: Invalid{}
    case True{}: body(fuel, rest)

def parse(fuel: Nat, raw: String) -> Parsed:
  match raw:
    case SNil{}: Invalid{}
    case SCon{Chr{n}, rest}: opening(U32.is_eq(n, 34), fuel, rest)

law append_associative:
  for a: String
  for +b: String
  for +c: String
  {(a ++ b) ++ c == a ++ (b ++ c) : String}
def append_associative(a, b, c):
  match a:
    case SNil{}: {==}
    case SCon{n, t}:
      Equal.cong(String, String, rest => SCon{n, rest},
        (t ++ b) ++ c, t ++ (b ++ c), append_associative(t, b, c))

def code_equal(+a: U32, +b: U32, equal: {U32.is_eq(a, b) == True{} : Bool}) -> {a == b : U32}:
  O.u32_equal(a, b, O.cmp_eq(U32.cmp(a, b), equal))

# This complete five-bit split covers exactly the fixed control-character
# alphabet. The next theorem reduces EVERY U32 below 32 to these five bits;
# the full string theorem is structural induction, not finite input testing.
def control(low: Word(5n)) -> U32:
  U32{W.join(5n, 27n, low, Word.zero(27n))}

law control_escape_decodes:
  for +low: Word(5n)
  for -rest: String
  {head(G.escape(control(low), False{}, False{}, True{}) ++ rest) == Character{control(low), rest} : Head}
def control_escape_decodes(low, rest):
  match low:
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{False{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}
    case WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WCon{True{}, WNil{}}}}}}: {==}

law small_code_escape_decodes:
  for +n: U32
  for +rest: String
  for small: {U32.is_lt(n, 32) == True{} : Bool}
  {head(G.escape(n, False{}, False{}, True{}) ++ rest) == Character{n, rest} : Head}
def small_code_escape_decodes(n, rest, small):
  match n:
    case U32{+word}:
      bounded = Equal.trans(Bool, U32.is_le(U32{word}, 31), U32.is_lt(U32{word}, 32), True{},
        U.limit_u32_successor(U32{word}, 31, {==}), small)
      %Equal.sym(U32, U32{word}, control(W.adjust(5n, 32n, word)),
        Equal.cong(Word(32n), U32, w => U32{w}, word,
          W.join(5n, 27n, W.adjust(5n, 32n, word), Word.zero(27n)),
          W.limit_bits_low(5n, 27n, word, bounded))) :
        {head(G.escape(_, False{}, False{}, True{}) ++ rest) == Character{_, rest} : Head}
      control_escape_decodes(W.adjust(5n, 32n, word), rest)

def escape_decodes(quote: Bool, slash: Bool, small: Bool, +n: U32, +rest: String,
  quoted: {U32.is_eq(n, 34) == quote : Bool},
  slashed: {U32.is_eq(n, 92) == slash : Bool},
  controlled: {U32.is_lt(n, 32) == small : Bool}) ->
  {head(G.escape(n, quote, slash, small) ++ rest) == Character{n, rest} : Head}:
  match quote slash small:
    case True{} _ _:
      %Equal.sym(U32, n, 34, code_equal(n, 34, quoted)) :
        {head("\\\"" ++ rest) == Character{_, rest} : Head}
      {==}
    case False{} True{} _:
      %Equal.sym(U32, n, 92, code_equal(n, 92, slashed)) :
        {head("\\\\" ++ rest) == Character{_, rest} : Head}
      {==}
    case False{} False{} True{}: small_code_escape_decodes(n, rest, controlled)
    case False{} False{} False{}:
      %Equal.sym(Bool, U32.is_eq(n, 34), False{}, quoted) :
        {head_choice(_, U32.is_eq(n, 92), n, rest) == Character{n, rest} : Head}
      %Equal.sym(Bool, U32.is_eq(n, 92), False{}, slashed) :
        {head_choice(False{}, _, n, rest) == Character{n, rest} : Head}
      {==}

law actual_escape_decodes_one_character_and_preserves_suffix:
  for +n: U32
  for +rest: String
  {head(G.escape(n, U32.is_eq(n, 34), U32.is_eq(n, 92), U32.is_lt(n, 32)) ++ rest) == Character{n, rest} : Head}
def actual_escape_decodes_one_character_and_preserves_suffix(n, rest):
  escape_decodes(U32.is_eq(n, 34), U32.is_eq(n, 92), U32.is_lt(n, 32), n, rest, {==}, {==}, {==})

law body_step_from_exact_head:
  for -fuel: Nat
  for -raw: String
  for -n: U32
  for -rest: String
  for read: {head(raw) == Character{n, rest} : Head}
  {body(1n+fuel, raw) == prepend(n, body(fuel, rest)) : Parsed}
def body_step_from_exact_head(fuel, raw, n, rest, read):
  %Equal.sym(Head, head(raw), Character{n, rest}, read) :
    {consume(_, later => body(fuel, later)) == prepend(n, body(fuel, rest)) : Parsed}
  {==}

law generated_body_recovers_exactly_before_closing_quote:
  for +value: String
  for +rest: String
  for +extra: Nat
  {body(Nat.add(String.length(value), 1n+extra), G.literal_body(value) ++ SCon{'"', rest}) == Literal{value, rest} : Parsed}
def generated_body_recovers_exactly_before_closing_quote(value, rest, extra):
  match value:
    case SNil{}: {==}
    case SCon{Chr{+n}, +tail}:
      +encoded = G.escape(n, U32.is_eq(n, 34), U32.is_eq(n, 92), U32.is_lt(n, 32))
      +later = G.literal_body(tail) ++ SCon{'"', rest}
      Equal.trans(Parsed,
        body(1n+Nat.add(String.length(tail), 1n+extra), (encoded ++ G.literal_body(tail)) ++ SCon{'"', rest}),
        body(1n+Nat.add(String.length(tail), 1n+extra), encoded ++ later),
        Literal{SCon{Chr{n}, tail}, rest},
        Equal.cong(String, Parsed, raw => body(1n+Nat.add(String.length(tail), 1n+extra), raw),
          (encoded ++ G.literal_body(tail)) ++ SCon{'"', rest}, encoded ++ later,
          append_associative(encoded, G.literal_body(tail), SCon{'"', rest})),
        Equal.trans(Parsed,
          body(1n+Nat.add(String.length(tail), 1n+extra), encoded ++ later),
          prepend(n, body(Nat.add(String.length(tail), 1n+extra), later)),
          Literal{SCon{Chr{n}, tail}, rest},
          body_step_from_exact_head(Nat.add(String.length(tail), 1n+extra), encoded ++ later, n, later,
            actual_escape_decodes_one_character_and_preserves_suffix(n, later)),
          Equal.cong(Parsed, Parsed, result => prepend(n, result),
            body(Nat.add(String.length(tail), 1n+extra), later), Literal{tail, rest},
            generated_body_recovers_exactly_before_closing_quote(tail, rest, extra))))

# The rest is arbitrary source text. Parsing consumes the one complete literal,
# returns exactly its original payload and leaves ALL following source intact.
law actual_generated_literal_roundtrip_with_arbitrary_source_suffix:
  for +value: String
  for +rest: String
  for +extra: Nat
  {parse(Nat.add(String.length(value), 1n+extra), G.literal(value) ++ rest) == Literal{value, rest} : Parsed}
def actual_generated_literal_roundtrip_with_arbitrary_source_suffix(value, rest, extra):
  %Equal.sym(String, (G.literal_body(value) ++ "\"") ++ rest,
    G.literal_body(value) ++ SCon{'"', rest}, append_associative(G.literal_body(value), "\"", rest)) :
    {body(Nat.add(String.length(value), 1n+extra), _) == Literal{value, rest} : Parsed}
  generated_body_recovers_exactly_before_closing_quote(value, rest, extra)

def payload(parsed: Parsed) -> String:
  match parsed:
    case Invalid{}: ""
    case Literal{value, rest}: value

def suffix(parsed: Parsed) -> String:
  match parsed:
    case Invalid{}: ""
    case Literal{value, rest}: rest

def equal_boundaries(-left: String, -right: String, -before: String, -after: String,
  same: {Literal{left, before} == Literal{right, after} : Parsed}) ->
  L.E<{left == right : String}, {before == after : String}>:
  %same : L.E<{left == payload(_) : String}, {before == suffix(_) : String}>
  L.Both{{==}, {==}}

def common_fuel(+a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == Nat.add(b, 1n+a) : Nat}:
  Equal.trans(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), Nat.add(b, 1n+a),
    K.sum_successor_right(a, b),
    Equal.trans(Nat, 1n+Nat.add(a, b), 1n+Nat.add(b, a), Nat.add(b, 1n+a),
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(a, b), Nat.add(b, a), N.sum_commutative(a, b)),
      Equal.sym(Nat, Nat.add(b, 1n+a), 1n+Nat.add(b, a), K.sum_successor_right(b, a))))

# Equal complete source prefixes cannot hide different payloads or move the
# closing boundary into following code. Both parses use one common fuel.
law generated_literal_boundary_is_unique:
  for +left: String
  for +right: String
  for +before: String
  for +after: String
  for same: {G.literal(left) ++ before == G.literal(right) ++ after : String}
  L.E<{left == right : String}, {before == after : String}>
def generated_literal_boundary_is_unique(left, right, before, after, same):
  equal_boundaries(left, right, before, after,
    Equal.trans(Parsed, Literal{left, before},
      parse(Nat.add(String.length(left), 1n+String.length(right)), G.literal(left) ++ before),
      Literal{right, after},
      Equal.sym(Parsed,
        parse(Nat.add(String.length(left), 1n+String.length(right)), G.literal(left) ++ before), Literal{left, before},
        actual_generated_literal_roundtrip_with_arbitrary_source_suffix(left, before, String.length(right))),
      Equal.trans(Parsed,
        parse(Nat.add(String.length(left), 1n+String.length(right)), G.literal(left) ++ before),
        parse(Nat.add(String.length(left), 1n+String.length(right)), G.literal(right) ++ after), Literal{right, after},
        Equal.cong(String, Parsed,
          raw => parse(Nat.add(String.length(left), 1n+String.length(right)), raw),
          G.literal(left) ++ before, G.literal(right) ++ after, same),
        (%Equal.sym(Nat, Nat.add(String.length(left), 1n+String.length(right)),
          Nat.add(String.length(right), 1n+String.length(left)), common_fuel(String.length(left), String.length(right))) :
          {parse(_, G.literal(right) ++ after) == Literal{right, after} : Parsed}
          actual_generated_literal_roundtrip_with_arbitrary_source_suffix(right, after, String.length(left))))))

type ArgumentsRead is Data:
  ArgumentsInvalid{}
  ArgumentsValue{value: D.Value, rest: String}

def reify_arguments(parsed: Parsed, high: U32, low: U32) -> ArgumentsRead:
  match parsed:
    case Invalid{}: ArgumentsInvalid{}
    case Literal{text, rest}: ArgumentsValue{R.arguments(text, high, low), rest}

# This is the actual literal emitted inside Generate.instance_content, followed
# there by decimal high/low length tokens. The following source is arbitrary;
# the numeric tokens and official frontend remain a separate parsing boundary.
# Reification.arguments cannot take its malformed-input fallback here: both
# lexical recovery and canonical byte decoding are proved from the encoding.
law actual_generated_argument_literal_recovers_exact_value_and_source_suffix:
  for +value: D.Value
  for +bytes: List<&2, U32>
  for +high: U32
  for +low: U32
  for +rest: String
  for +extra: Nat
  for encoded: P.Encoding(value, bytes)
  for measured: {B.nat64(B.length(bytes)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {reify_arguments(parse(Nat.add(String.length(R.text(bytes)), 1n+extra),
    G.literal(R.text(bytes)) ++ rest), high, low) == ArgumentsValue{value, rest} : ArgumentsRead}
def actual_generated_argument_literal_recovers_exact_value_and_source_suffix(value, bytes, high, low, rest, extra, encoded, measured):
  %Equal.sym(Parsed, parse(Nat.add(String.length(R.text(bytes)), 1n+extra), G.literal(R.text(bytes)) ++ rest),
    Literal{R.text(bytes), rest}, actual_generated_literal_roundtrip_with_arbitrary_source_suffix(R.text(bytes), rest, extra)) :
    {reify_arguments(_, high, low) == ArgumentsValue{value, rest} : ArgumentsRead}
  Equal.cong(D.Value, ArgumentsRead, v => ArgumentsValue{v, rest}, R.arguments(R.text(bytes), high, low), value,
    Reification.source_of_arguments_recovers_o_value_without_fallback(value, bytes, high, low, encoded, measured))
