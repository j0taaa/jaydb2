# Canonical records use the contract validator, including nested values.
import Base
import ../contract/Data.bend as D

def raw(fs: List<&2, D.Field>) -> D.Value:
  match fs:
    case Nil{}: D.VRecordEmpty{}
    case Con{D.Field{n, v}, rest}: D.VRecord{n, v, raw(rest)}

def checked(+v: D.Value) -> Maybe<&2, D.Value>:
  Bool.pick(Maybe<&2, D.Value>, D.value_valid(v), Some{v}, None{})

def make(fs: List<&2, D.Field>) -> Maybe<&2, D.Value>:
  checked(raw(fs))

def fields(v: D.Value) -> List<&2, D.Field>:
  match v:
    case D.VRecord{n, x, rest}: Con{D.Field{n, x}, fields(rest)}
    case _: Nil{}

law fields_roundtrip:
  for fs: List<&2, D.Field>
  {fields(raw(fs)) == fs : List<&2, D.Field>}
def fields_roundtrip(fs):
  match fs:
    case Nil{}: {==}
    case Con{D.Field{+n, +v}, rest}:
      Equal.cong(List<&2, D.Field>, List<&2, D.Field>, tail => Con{D.Field{n, v}, tail}, fields(raw(rest)), rest, fields_roundtrip(rest))
