# Count is finite-list Nat; numeric sum/min/max retain full signed64 domain.
import Base
import ./Value.bend as V
import ./Int64.bend as I

def plus(x: V.Int64, tail: Maybe<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match tail:
    case None{}: None{}
    case Some{y}: I.add(x, y)

def sum(xs: List<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match xs:
    case Nil{}: Some{V.Int64{0, 0}}
    case Con{x, rest}: plus(x, sum(rest))

def minimum(xs: List<&2, V.Int64>, +best: V.Int64) -> V.Int64:
  match xs:
    case Nil{}: best
    case Con{+x, rest}: minimum(rest, Bool.pick(V.Int64, I.lt(x, best), x, best))

def maximum(xs: List<&2, V.Int64>, +best: V.Int64) -> V.Int64:
  match xs:
    case Nil{}: best
    case Con{+x, rest}: maximum(rest, Bool.pick(V.Int64, I.lt(best, x), x, best))
