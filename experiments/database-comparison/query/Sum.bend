# One transaction; all actual table keys are scanned, with checked signed64 sum.
import Base
import ./Data.bend as D
import ./Semantics.bend as S

type SumWord is Data:
  SumWord{high: U32, low: U32}

def negative(x: SumWord) -> Bool:
  SumWord{h, l} = x
  U32.is_ge(h, 2147483648)

def wrapping_add(a: SumWord, b: SumWord) -> SumWord:
  SumWord{h, +l} = a
  SumWord{i, j} = b
  +low = U32.add(l, j)
  SumWord{U32.add(U32.add(h, i), Bool.to_u32(U32.is_lt(low, l))), low}

def checked(overflow: Bool, result: SumWord) -> Maybe<&2, SumWord>:
  match overflow:
    case True{}: None{}
    case False{}: Some{result}

def add(+a: SumWord, +b: SumWord) -> Maybe<&2, SumWord>:
  checked(Bool.not(Bool.xor(negative(a), negative(b))) &&
    Bool.xor(negative(a), negative(wrapping_add(a, b))), wrapping_add(a, b))

def value(x: SumWord) -> D.Value:
  SumWord{h, l} = x
  D.VInt{h, l}

def added(result: Maybe<&2, SumWord>, done: SumWord -> S.Action) -> S.Action:
  match result:
    case None{}: S.Refuse{D.VText{"integer sum overflow"}}
    case Some{x}: done(x)

def received(+acc: SumWord, done: SumWord -> S.Action, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{D.VInt{h, l}}}: added(add(acc, SumWord{h, l}), done)
    case _: S.Refuse{D.VText{"sum requires integer cells"}}

def walk(xs: List<&2, String>, +table: String, +column: String, +acc: SumWord) -> S.Action:
  match xs:
    case Nil{}: S.Finish{value(acc)}
    case Con{key, +rest}:
      S.Access{D.ReadCell{D.Application{table}, key, column},
        received(acc, next => walk(rest, table, column, next))}

def listed(+table: String, +column: String, r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Keys{keys}}: walk(keys, table, column, SumWord{0, 0})
    case _: S.Refuse{D.VText{"unexpected keys return"}}

type Command is Data:
  Sum{table: String, column: String}
  Invalid{}

def analyze(args: D.Value) -> Command:
  match args:
    case D.VList{D.VText{"sum"}, D.VList{D.VText{table}, D.VList{D.VText{column}, D.VListEmpty{}}}}: Sum{table, column}
    case _: Invalid{}

def command(p: Command) -> S.Action:
  match p:
    case Sum{+table, +column}:
      S.Access{D.EnumerateKeys{D.Application{table}}, listed(table, column)}
    case Invalid{}: S.Refuse{D.VText{"expected [sum, table, integer_column]"}}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  command(analyze(args))

def program() -> S.Program:
  S.Program{start}
