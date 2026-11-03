# Constructive lemmas used by implementation proofs. No axioms.
import Base
import ../contract/Logic.bend as L

def combined_pair(-A: Type, -P: Type, -Q: Type, pair: L.E<P, Q>,
  resume: P -> Q -> A) -> A:
  match pair:
    case L.Both{p, q}:
      resume(p, q)

def false_negative_true(e: {False{} == True{} : Bool}) -> Empty:
  %e : Bool.pick(Type, _, Empty, Unit)
  Unit{}

def absurd_boolean(-A: Type, e: {False{} == True{} : Bool}) -> A:
  L.ex_false(A, false_negative_true(e))

law and_boolean_left:
  for a: Bool
  for -b: Bool
  for e: {a && b == True{} : Bool}
  {a == True{} : Bool}
def and_boolean_left(a, b, e):
  match a:
    case False{}:
      absurd_boolean({False{} == True{} : Bool}, e)
    case True{}:
      {==}

law and_boolean_right:
  for a: Bool
  for -b: Bool
  for e: {a && b == True{} : Bool}
  {b == True{} : Bool}
def and_boolean_right(a, b, e):
  match a:
    case False{}:
      absurd_boolean({b == True{} : Bool}, e)
    case True{}:
      e

law and_boolean_separate:
  for a: Bool
  for -b: Bool
  for e: {a && b == True{} : Bool}
  L.E<{a == True{} : Bool}, {b == True{} : Bool}>
def and_boolean_separate(a, b, e):
  match a:
    case False{}:
      absurd_boolean(L.E<{False{} == True{} : Bool}, {b == True{} : Bool}>, e)
    case True{}:
      L.Both{{==}, e}

law and_boolean_intro:
  for -a: Bool
  for -b: Bool
  for ea: {a == True{} : Bool}
  for eb: {b == True{} : Bool}
  {a && b == True{} : Bool}
def and_boolean_intro(a, b, ea, eb):
  %Equal.sym(Bool, a, True{}, ea) : {_ && b == True{} : Bool}
  eb

law negation_true:
  for b: Bool
  for e: {Bool.not(b) == True{} : Bool}
  {b == False{} : Bool}
def negation_true(b, e):
  match b:
    case False{}:
      {==}
    case True{}:
      absurd_boolean({True{} == False{} : Bool}, e)

def some(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

def none_negative_some(-A: Data, -x: A,
  e: {None{} == Some{x} : Maybe<&2, A>}) -> Empty:
  false_negative_true(Equal.cong(Maybe<&2, A>, Bool, m => some(A, m),
    None{}, Some{x}, e))

def extract_or(-A: Data, m: Maybe<&2, A>, default: A) -> A:
  match m:
    case None{}:
      default
    case Some{x}:
      x

law some_injective:
  for -A: Data
  for +a: A
  for -b: A
  for e: {Some{a} == Some{b} : Maybe<&2, A>}
  {a == b : A}
def some_injective(A, a, b, e):
  Equal.cong(Maybe<&2, A>, A,
    m => extract_or(A, m, a),
    Some{a}, Some{b}, e)

law prefix_transitive:
  for -A: Data
  for xs: List<&2, A>
  for ys: List<&2, A>
  for zs: List<&2, A>
  for xy: L.Prefix(A, xs, ys)
  for yz: L.Prefix(A, ys, zs)
  L.Prefix(A, xs, zs)
def prefix_transitive(A, xs, ys, zs, xy, yz):
  match xs ys zs:
    case Nil{} _ _:
      Unit{}
    case Con{x, xt} Nil{} _:
      match xy:
    case Con{x, xt} Con{y, yt} Nil{}:
      match yz:
    case Con{x, xt} Con{y, yt} Con{z, zt}:
      match xy yz:
        case L.Both{head1, tail1} L.Both{head2, tail2}:
          L.Both{Equal.trans(A, x, y, z, head1, head2),
            prefix_transitive(A, xt, yt, zt, tail1, tail2)}
