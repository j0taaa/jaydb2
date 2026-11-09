# Independent numeric-argument tail grammar for Generate.instance_content.
import Base
import ./DecimalParser.bend as P
import ./DecimalShow.bend as S
import ../contract/Data.bend as Data
import ../contract/Bytes.bend as B
import ../contract/Protocol.bend as Protocol
import ../src/Generate.bend as G
import ../src/Reification.bend as R
import ./GeneratedLiterals.bend as Literal
import ./GeneratedContext.bend as Context
import ./Reification.bend as Reification

type WordsRead is Data:
  WordsInvalid{}
  WordsRead{high: U32, low: U32, rest: String}

def after_low(high: U32, parsed: P.WordParsed) -> WordsRead:
  match parsed:
    case P.WordParsed{low, SCon{')', rest}}: WordsRead{high, low, rest}
    case _: WordsInvalid{}

def after_separator(high: U32, raw: String) -> WordsRead:
  match raw:
    case SCon{',', SCon{' ', rest}}: after_low(high, P.parse_word(rest))
    case _: WordsInvalid{}

def after_high(parsed: P.WordParsed) -> WordsRead:
  match parsed:
    case P.WordInvalid{}: WordsInvalid{}
    case P.WordParsed{high, rest}: after_separator(high, rest)

def parse_words(raw: String) -> WordsRead:
  after_high(P.parse_word(raw))

law actual_high_low_tokens_roundtrip:
  for +high: U32
  for +low: U32
  for +rest: String
  {parse_words(U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest)))) == WordsRead{high, low, rest} : WordsRead}
def actual_high_low_tokens_roundtrip(high, low, rest):
  %Equal.sym(P.WordParsed, P.parse_word(U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest)))),
    P.WordParsed{high, ", " ++ (U32.show(low) ++ (")" ++ rest))},
    S.actual_u32_show_recovers_exact_word_and_source_boundary(high, ", " ++ (U32.show(low) ++ (")" ++ rest)),
      P.CommaBoundary{SCon{' ', U32.show(low) ++ (")" ++ rest)}, {==}})) :
    {after_high(_) == WordsRead{high, low, rest} : WordsRead}
  %Equal.sym(P.WordParsed, P.parse_word(U32.show(low) ++ (")" ++ rest)), P.WordParsed{low, ")" ++ rest},
    S.actual_u32_show_recovers_exact_word_and_source_boundary(low, ")" ++ rest, P.ParenBoundary{rest, {==}})) :
    {after_low(high, _) == WordsRead{high, low, rest} : WordsRead}
  {==}

type ArgumentRead is Data:
  ArgumentInvalid{}
  ArgumentRead{value: Data.Value, rest: String}

def from_words(text: String, parsed: WordsRead) -> ArgumentRead:
  match parsed:
    case WordsInvalid{}: ArgumentInvalid{}
    case WordsRead{high, low, rest}: ArgumentRead{R.arguments(text, high, low), rest}

def after_argument_separator(text: String, raw: Maybe<&2, String>) -> ArgumentRead:
  match raw:
    case None{}: ArgumentInvalid{}
    case Some{remaining}: from_words(text, parse_words(remaining))

def after_literal(parsed: Literal.Parsed) -> ArgumentRead:
  match parsed:
    case Literal.Invalid{}: ArgumentInvalid{}
    case Literal.Literal{text, rest}: after_argument_separator(text, Context.strip(", ", rest))

def after_open(fuel: Nat, raw: Maybe<&2, String>) -> ArgumentRead:
  match raw:
    case None{}: ArgumentInvalid{}
    case Some{remaining}: after_literal(Literal.parse(fuel, remaining))

def parse_argument(fuel: Nat, raw: String) -> ArgumentRead:
  after_open(fuel, Context.strip("Reification.arguments(", raw))

# A concrete source fragment specification; the final theorem below links it
# by equality to the actual instance generator, rather than presuming a prefix.
def argument_call(text: String, high: U32, low: U32, rest: String) -> String:
  "Reification.arguments(" ++ (G.literal(text) ++ (", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest))))))

law rendered_argument_call_reads_numeric_fields:
  for +text: String
  for +high: U32
  for +low: U32
  for +rest: String
  for +extra: Nat
  {parse_argument(Nat.add(String.length(text), 1n+extra), argument_call(text, high, low, rest)) ==
    ArgumentRead{R.arguments(text, high, low), rest} : ArgumentRead}
def rendered_argument_call_reads_numeric_fields(text, high, low, rest, extra):
  %Equal.sym(Maybe<&2, String>, Context.strip("Reification.arguments(",
    "Reification.arguments(" ++ (G.literal(text) ++ (", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest))))))),
    Some{G.literal(text) ++ (", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest)))))},
    Context.stripping_an_exact_prefix_preserves_the_entire_suffix("Reification.arguments(",
      G.literal(text) ++ (", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest))))))) :
    {after_open(Nat.add(String.length(text), 1n+extra), _) == ArgumentRead{R.arguments(text, high, low), rest} : ArgumentRead}
  %Equal.sym(Literal.Parsed, Literal.parse(Nat.add(String.length(text), 1n+extra),
    G.literal(text) ++ (", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest)))))),
    Literal.Literal{text, ", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest))))},
    Literal.actual_generated_literal_roundtrip_with_arbitrary_source_suffix(text,
      ", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest)))), extra)) :
    {after_literal(_) == ArgumentRead{R.arguments(text, high, low), rest} : ArgumentRead}
  %Equal.sym(Maybe<&2, String>, Context.strip(", ", ", " ++ (U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest))))),
    Some{U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest)))},
    Context.stripping_an_exact_prefix_preserves_the_entire_suffix(", ", U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest))))) :
    {after_argument_separator(text, _) == ArgumentRead{R.arguments(text, high, low), rest} : ArgumentRead}
  %Equal.sym(WordsRead, parse_words(U32.show(high) ++ (", " ++ (U32.show(low) ++ (")" ++ rest)))), WordsRead{high, low, rest},
    actual_high_low_tokens_roundtrip(high, low, rest)) :
    {from_words(text, _) == ArgumentRead{R.arguments(text, high, low), rest} : ArgumentRead}
  {==}

law actual_argument_call_recovers_value:
  for +value: Data.Value
  for +bytes: List<&2, U32>
  for +high: U32
  for +low: U32
  for +rest: String
  for +extra: Nat
  for encoded: Protocol.Encoding(value, bytes)
  for measured: {B.nat64(B.length(bytes)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {parse_argument(Nat.add(String.length(R.text(bytes)), 1n+extra), argument_call(R.text(bytes), high, low, rest)) ==
    ArgumentRead{value, rest} : ArgumentRead}
def actual_argument_call_recovers_value(value, bytes, high, low, rest, extra, encoded, measured):
  Equal.trans(ArgumentRead, parse_argument(Nat.add(String.length(R.text(bytes)), 1n+extra), argument_call(R.text(bytes), high, low, rest)),
    ArgumentRead{R.arguments(R.text(bytes), high, low), rest}, ArgumentRead{value, rest},
    rendered_argument_call_reads_numeric_fields(R.text(bytes), high, low, rest, extra),
    Equal.cong(Data.Value, ArgumentRead, v => ArgumentRead{v, rest}, R.arguments(R.text(bytes), high, low), value,
      Reification.source_of_arguments_recovers_o_value_without_fallback(value, bytes, high, low, encoded, measured)))
