# Actual generator source linked to the independently parsed numeric arguments.
# Context-prefix semantics are established separately by GeneratedContext.
import Base
import ./GeneratedArgumentCall.bend as A
import ./DecimalShow.bend as S
import ../contract/Data.bend as D
import ../contract/Bytes.bend as B
import ../contract/Protocol.bend as P
import ../src/Generate.bend as G
import ../src/Reification.bend as R
import ./GeneratedContext.bend as Context

def header() -> String:
  "import Base\n" ++
  "import ./Data.bend as D\n" ++
  "import ./Semantics.bend as S\n" ++
  "import ./Reification.bend as Reification\n" ++
  "import ./Configuration.bend as C\n\n" ++
  "def config() -> S.Configuration:\n  C.config()\n\n" ++
  "def context() -> D.Context:\n  "

def before_arguments() -> String:
  "\n\ndef arguments() -> D.Value:\n  "

def prefix(context: D.Context) -> String:
  header() ++ (G.context(context) ++ before_arguments())

law actual_generator_exposes_exact_numeric_call:
  for +context: D.Context
  for +bytes: List<&2, U32>
  for +high: U32
  for +low: U32
  {G.instance_content(context, bytes, high, low) == prefix(context) ++ A.argument_call(R.text(bytes), high, low, "\n") : String}
def actual_generator_exposes_exact_numeric_call(context, bytes, high, low):
  Equal.sym(String, prefix(context) ++ A.argument_call(R.text(bytes), high, low, "\n"), G.instance_content(context, bytes, high, low),
    Equal.trans(String, (header() ++ (G.context(context) ++ before_arguments())) ++ A.argument_call(R.text(bytes), high, low, "\n"),
      header() ++ ((G.context(context) ++ before_arguments()) ++ A.argument_call(R.text(bytes), high, low, "\n")),
      G.instance_content(context, bytes, high, low),
      S.string_append_associative(header(), G.context(context) ++ before_arguments(), A.argument_call(R.text(bytes), high, low, "\n")),
      Equal.cong(String, String, source => header() ++ source,
        (G.context(context) ++ before_arguments()) ++ A.argument_call(R.text(bytes), high, low, "\n"),
        G.context(context) ++ (before_arguments() ++ A.argument_call(R.text(bytes), high, low, "\n")),
        S.string_append_associative(G.context(context), before_arguments(), A.argument_call(R.text(bytes), high, low, "\n")))))

def after_prefix(fuel: Nat, source: Maybe<&2, String>) -> A.ArgumentRead:
  match source:
    case None{}: A.ArgumentInvalid{}
    case Some{call}: A.parse_argument(fuel, call)

def parse(context: D.Context, fuel: Nat, source: String) -> A.ArgumentRead:
  after_prefix(fuel, Context.strip(prefix(context), source))

law actual_instance_content_recovers_exact_argument_value:
  for +context: D.Context
  for +value: D.Value
  for +bytes: List<&2, U32>
  for +high: U32
  for +low: U32
  for +extra: Nat
  for encoded: P.Encoding(value, bytes)
  for measured: {B.nat64(B.length(bytes)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {parse(context, Nat.add(String.length(R.text(bytes)), 1n+extra), G.instance_content(context, bytes, high, low)) == A.ArgumentRead{value, "\n"} : A.ArgumentRead}
def actual_instance_content_recovers_exact_argument_value(context, value, bytes, high, low, extra, encoded, measured):
  %Equal.sym(String, G.instance_content(context, bytes, high, low), prefix(context) ++ A.argument_call(R.text(bytes), high, low, "\n"),
    actual_generator_exposes_exact_numeric_call(context, bytes, high, low)) :
    {parse(context, Nat.add(String.length(R.text(bytes)), 1n+extra), _) == A.ArgumentRead{value, "\n"} : A.ArgumentRead}
  %Equal.sym(Maybe<&2, String>, Context.strip(prefix(context), prefix(context) ++ A.argument_call(R.text(bytes), high, low, "\n")),
    Some{A.argument_call(R.text(bytes), high, low, "\n")},
    Context.stripping_an_exact_prefix_preserves_the_entire_suffix(prefix(context), A.argument_call(R.text(bytes), high, low, "\n"))) :
    {after_prefix(Nat.add(String.length(R.text(bytes)), 1n+extra), _) == A.ArgumentRead{value, "\n"} : A.ArgumentRead}
  A.actual_argument_call_recovers_value(value, bytes, high, low, "\n", extra, encoded, measured)

# None is a genuine generator failure branch. Every actual produced source
# has a constructively supplied parser fuel and recovers the original value.
def SourceCorrect(+context: D.Context, +value: D.Value, result: Maybe<&2, String>) -> Type:
  match result:
    case None{}: Unit
    case Some{source}: &fuel: Nat -> {parse(context, fuel, source) == A.ArgumentRead{value, "\n"} : A.ArgumentRead}

def measured_source(+context: D.Context, +value: D.Value, +bytes: List<&2, U32>, measure: Maybe<&2, B.Number64>,
  encoded: P.Encoding(value, bytes), measured: {B.nat64(B.length(bytes)) == measure : Maybe<&2, B.Number64>}) ->
  SourceCorrect(context, value, G.instance_measure(measure, context, bytes)):
  match measure:
    case None{}: Unit{}
    case Some{B.Number64{high, low}}:
      (Nat.add(String.length(R.text(bytes)), 1n), actual_instance_content_recovers_exact_argument_value(context, value, bytes, high, low, 0n, encoded, measured))

def encoded_source(+context: D.Context, +value: D.Value, encoded: Maybe<&2, List<&2, U32>>,
  exact: {P.encode(value) == encoded : Maybe<&2, List<&2, U32>>}) -> SourceCorrect(context, value, G.instance_encoded(encoded, context)):
  match encoded:
    case None{}: Unit{}
    case Some{+bytes}: measured_source(context, value, bytes, B.nat64(B.length(bytes)), exact, {==})

law actual_generated_instance_has_correct_numeric_arguments:
  for +context: D.Context
  for +value: D.Value
  SourceCorrect(context, value, G.instance(context, value))
def actual_generated_instance_has_correct_numeric_arguments(context, value):
  encoded_source(context, value, P.encode(value), {==})

# Non-vacuous success: representable, measured arguments actually produce the
# source whose numeric fields the independent parser just proved correct.
law representable_measured_value_is_actually_generated:
  for +context: D.Context
  for +value: D.Value
  for +bytes: List<&2, U32>
  for +high: U32
  for +low: U32
  for encoded: P.Encoding(value, bytes)
  for measured: {B.nat64(B.length(bytes)) == Some{B.Number64{high, low}} : Maybe<&2, B.Number64>}
  {G.instance(context, value) == Some{G.instance_content(context, bytes, high, low)} : Maybe<&2, String>}
def representable_measured_value_is_actually_generated(context, value, bytes, high, low, encoded, measured):
  %Equal.sym(Maybe<&2, List<&2, U32>>, P.encode(value), Some{bytes}, encoded) :
    {G.instance_encoded(_, context) == Some{G.instance_content(context, bytes, high, low)} : Maybe<&2, String>}
  %Equal.sym(Maybe<&2, B.Number64>, B.nat64(B.length(bytes)), Some{B.Number64{high, low}}, measured) :
    {G.instance_measure(_, context, bytes) == Some{G.instance_content(context, bytes, high, low)} : Maybe<&2, String>}
  {==}
