# Nested-loop joins on already obtained values, including duplicate matches.
import Base
import ../contract/Data.bend as D

def append(xs: List<&2, D.Value>, ys: List<&2, D.Value>) -> List<&2, D.Value>:
  match xs:
    case Nil{}: ys
    case Con{x, rest}: Con{x, append(rest, ys)}

def include(b: Bool, left: D.Value, right: D.Value, tail: List<&2, D.Value>) -> List<&2, D.Value>:
  match b:
    case True{}: Con{D.VList{left, D.VList{right, D.VListEmpty{}}}, tail}
    case False{}: tail

def matches(~left_key: D.Value -> String, ~right_key: D.Value -> String,
  +left: D.Value, right: List<&2, D.Value>) -> List<&2, D.Value>:
  match right:
    case Nil{}: Nil{}
    case Con{+r, rest}:
      include(String.eq(left_key(left), right_key(r)), left, r, matches(~left_key, ~right_key, left, rest))

def inner(~left_key: D.Value -> String, ~right_key: D.Value -> String,
  left: List<&2, D.Value>, +right: List<&2, D.Value>) -> List<&2, D.Value>:
  match left:
    case Nil{}: Nil{}
    case Con{l, rest}: append(matches(~left_key, ~right_key, l, right), inner(~left_key, ~right_key, rest, right))

def outer_matches(+left: D.Value, found: List<&2, D.Value>) -> List<&2, D.Value>:
  match found:
    case Nil{}: [D.VList{left, D.VList{D.VAbsent{}, D.VListEmpty{}}}]
    case Con{x, rest}: Con{x, rest}

def left_join(~left_key: D.Value -> String, ~right_key: D.Value -> String,
  left: List<&2, D.Value>, +right: List<&2, D.Value>) -> List<&2, D.Value>:
  match left:
    case Nil{}: Nil{}
    case Con{+l, rest}: append(outer_matches(l, matches(~left_key, ~right_key, l, right)), left_join(~left_key, ~right_key, rest, right))
