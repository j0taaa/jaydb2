# Typed scalar decoders. None is a type mismatch; Some(VAbsent) is data.
import Base
import ../contract/Data.bend as D

type Int64 is Data:
  Int64{high: U32, low: U32}

def integer(v: D.Value) -> Maybe<&2, Int64>:
  match v:
    case D.VInt{h, l}: Some{Int64{h, l}}
    case _: None{}

def int_value(i: Int64) -> D.Value:
  Int64{h, l} = i
  D.VInt{h, l}

def text(v: D.Value) -> Maybe<&2, String>:
  match v:
    case D.VText{+s}: Bool.pick(Maybe<&2, String>, D.unicode_valid(s), Some{s}, None{})
    case _: None{}

def boolean(v: D.Value) -> Maybe<&2, Bool>:
  match v:
    case D.VBool{b}: Some{b}
    case _: None{}

law integer_roundtrip:
  for i: Int64
  {integer(int_value(i)) == Some{i} : Maybe<&2, Int64>}
def integer_roundtrip(i):
  match i:
    case Int64{h, l}: {==}

# Decode an actual list; malformed tails are rejected, never truncated.
def list_cons(x: D.Value, tail: Maybe<&2, List<&2, D.Value>>) -> Maybe<&2, List<&2, D.Value>>:
  match tail:
    case None{}: None{}
    case Some{xs}: Some{Con{x, xs}}

def list(v: D.Value) -> Maybe<&2, List<&2, D.Value>>:
  match v:
    case D.VListEmpty{}: Some{Nil{}}
    case D.VList{h, t}: list_cons(h, list(t))
    case _: None{}
