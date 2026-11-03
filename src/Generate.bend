# Reification of public values actually decoded/authenticated.
# Arguments use canonical bytes in escaped literals, without nested ASTs.
# No private state data is inserted in the certificate module.
import Base
import ../contract/Data.bend as D
import ../contract/Bytes.bend as B
import ../contract/Protocol.bend as P
import ./Reification.bend as R

def text(s: String) -> String:
  match s:
    case SNil{}:
      "SNil{}"
    case SCon{Chr{code}, rest}:
      "SCon{Chr{" ++ U32.show(code) ++ "}," ++ text(rest) ++ "}"

def boolean(b: Bool) -> String:
  match b:
    case True{}:
      "True{}"
    case False{}:
      "False{}"

def value(v: D.Value) -> String:
  match v:
    case D.VAbsent{}:
      "D.VAbsent{}"
    case D.VBool{b}:
      "D.VBool{" ++ boolean(b) ++ "}"
    case D.VInt{high, low}:
      "D.VInt{" ++ U32.show(high) ++ "," ++ U32.show(low) ++ "}"
    case D.VText{s}:
      "D.VText{" ++ text(s) ++ "}"
    case D.VListEmpty{}:
      "D.VListEmpty{}"
    case D.VList{h, t}:
      "D.VList{" ++ value(h) ++ "," ++ value(t) ++ "}"
    case D.VRecordEmpty{}:
      "D.VRecordEmpty{}"
    case D.VRecord{name, v, rest}:
      "D.VRecord{" ++ text(name) ++ "," ++ value(v) ++ "," ++ value(rest) ++ "}"

def hexadecimal(n: U32, small: Bool) -> Char:
  match small:
    case True{}:
      Chr{(48 + n : U32)}
    case False{}:
      Chr{(87 + n : U32)}

def escape(+n: U32, quotes: Bool, slash: Bool, control: Bool) -> String:
  match quotes slash control:
    case True{} _ _:
      "\\\""
    case False{} True{} _:
      "\\\\"
    case False{} False{} True{}:
      +high = U32.shrn(n, 4n)
      +low = U32.and(n, 15)
      "\\u{" ++ SCon{hexadecimal(high, U32.is_lt(high, 10)),
        SCon{hexadecimal(low, U32.is_lt(low, 10)), SNil{}}} ++ "}"
    case False{} False{} False{}:
      SCon{Chr{n}, SNil{}}

def literal_body(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{Chr{+n}, t}:
      escape(n, U32.is_eq(n, 34), U32.is_eq(n, 92), U32.is_lt(n, 32)) ++ literal_body(t)

def literal(s: String) -> String:
  "\"" ++ literal_body(s) ++ "\""

def context(c: D.Context) -> String:
  D.Context{id, kind} = c
  "D.Context{" ++ literal(id) ++ "," ++ literal(kind) ++ "}"

def instance_content(ctx: D.Context, bytes: List<&2, U32>, high: U32, low: U32) -> String:
  "import Base\n" ++
  "import ./Data.bend as D\n" ++
  "import ./Semantics.bend as S\n" ++
  "import ./Reification.bend as Reification\n" ++
  "import ./Configuration.bend as C\n\n" ++
  "def config() -> S.Configuration:\n  C.config()\n\n" ++
  "def context() -> D.Context:\n  " ++ context(ctx) ++ "\n\n" ++
  "def arguments() -> D.Value:\n  Reification.arguments(" ++ literal(R.text(bytes)) ++
    ", " ++ U32.show(high) ++ ", " ++ U32.show(low) ++ ")\n"

def instance_measure(measure: Maybe<&2, B.Number64>, ctx: D.Context, bytes: List<&2, U32>) -> Maybe<&2, String>:
  match measure:
    case None{}:
      None{}
    case Some{B.Number64{high, low}}:
      Some{instance_content(ctx, bytes, high, low)}

def instance_encoded(encoded: Maybe<&2, List<&2, U32>>, ctx: D.Context) -> Maybe<&2, String>:
  match encoded:
    case None{}:
      None{}
    case Some{+bytes}:
      instance_measure(B.nat64(B.length(bytes)), ctx, bytes)

def instance(ctx: D.Context, arguments: D.Value) -> Maybe<&2, String>:
  instance_encoded(P.encode(arguments), ctx)

def links(code: String) -> String:
  "import Base\n" ++
  "import ./Data.bend as D\n" ++
  "import ./Semantics.bend as S\n" ++
  "import ./Requirements.bend as R\n" ++
  "import ./Interface.bend as F\n" ++
  "import ./Instance.bend as I\n" ++
  "import ./Client.bend as Client\n\n" ++
  "def code() -> String:\n  " ++ literal(code) ++ "\n\n" ++
  "law certificate:\n  R.Certifies(I.config(), code(), Client.program(), I.context(), I.arguments())\n\n" ++
  "law terminates:\n  F.ProgramTerminates(I.config(), Client.program())\n"

law text_negative_interprets_sequence_of_escape:
  {text("\\n") == "SCon{Chr{92},SCon{Chr{110},SNil{}}}" : String}
def text_negative_interprets_sequence_of_escape():
  {==}

law integer_preserves_both_as_words:
  {value(D.VInt{4294967295, 2147483648}) == "D.VInt{4294967295,2147483648}" : String}
def integer_preserves_both_as_words():
  {==}

law literal_negative_allows_injection_of_source:
  {literal("\"\\\n") == "\"\\\"\\\\\\u{0a}\"" : String}
def literal_negative_allows_injection_of_source():
  {==}
