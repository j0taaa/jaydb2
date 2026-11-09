import Base
import ./Data.bend as D
import ./Semantics.bend as S

def arg(args: D.Value, n: Nat) -> D.Value:
  match args n:
    case D.VList{v, rest} Zero{}: v
    case D.VList{v, rest} Succ{p}: arg(rest, p)
    case _ _: D.VAbsent{}

def text(v: D.Value) -> String:
  match v:
    case D.VText{s}: s
    case _: ""

def fields(v: D.Value) -> List<&2, D.Field>:
  match v:
    case D.VRecord{n, v, rest}: D.Field{n, v} <> fields(rest)
    case _: []

def collection(args: D.Value) -> D.Collection:
  D.Application{text(arg(args, 1n))}

def operation(+args: D.Value) -> D.Operation:
  +command = text(arg(args, 0n))
  +collection = collection(args)
  +key = text(arg(args, 2n))
  Bool.pick(D.Operation, String.eq(command, "put"),
    D.DefineRow{collection, key, fields(arg(args, 3n))},
    Bool.pick(D.Operation, String.eq(command, "update"),
      D.DefineColumn{collection, key, text(arg(args, 3n)), arg(args, 4n)},
      Bool.pick(D.Operation, String.eq(command, "delete"),
        D.RemoveRow{collection, key},
        Bool.pick(D.Operation, String.eq(command, "keys"),
          D.EnumerateKeys{collection},
          D.ReadCell{collection, key, text(arg(args, 3n))}))))

def keys(xs: List<&2, String>) -> D.Value:
  match xs:
    case Nil{}: D.VListEmpty{}
    case Con{k, rest}: D.VList{D.VText{k}, keys(rest)}

def value(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{v}}: v
    case S.Datum{D.Keys{ks}}: keys(ks)
    case S.UnitValue{}: D.VBool{True{}}
    case _: D.VAbsent{}

def program() -> S.Program:
  S.Program{ctx => args => S.Access{operation(args), r => S.Finish{value(r)}}}
