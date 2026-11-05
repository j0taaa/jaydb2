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

def count(xs: List<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match xs:
    case Nil{}: Some{V.Int64{0, 0}}
    case Con{x, rest}: plus(V.Int64{0, 1}, count(rest))

def min_value(xs: List<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match xs:
    case Nil{}: None{}
    case Con{x, rest}: Some{minimum(rest, x)}

def max_value(xs: List<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match xs:
    case Nil{}: None{}
    case Con{x, rest}: Some{maximum(rest, x)}

def quotient(result: Maybe<&2, I.Division>) -> Maybe<&2, V.Int64>:
  match result:
    case None{}: None{}
    case Some{I.Division{q, r}}: Some{q}

def average_result(total: Maybe<&2, V.Int64>, count: Maybe<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  match total count:
    case Some{s} Some{n}: quotient(I.divmod(s, n))
    case _ _: None{}

# Empty/overflow -> None; integer mean truncates toward zero.
def average(+xs: List<&2, V.Int64>) -> Maybe<&2, V.Int64>:
  average_result(sum(xs), count(xs))
