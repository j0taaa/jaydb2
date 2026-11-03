# Logical foundations of the JayDB contract.
# Each `law` in this file has a `def` proof with the same name.
# None of these lemmas asserts correctness of a database implementation.
import Base

type E<-P: Type, -Q: Type> is Type:
  Both{left: P, right: Q}

type Disjunction<-P: Type, -Q: Type> is Type:
  Left{proof: P}
  Right{proof: Q}

def Truth() -> Type:
  Unit

def Falsehood() -> Type:
  Empty

def Implies(-P: Type, -Q: Type) -> Type:
  P -> Q

def Not(-P: Type) -> Type:
  P -> Empty

def IsTrue(b: Bool) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      Empty

# Conjunction of ALL propositions P(x) in the list, without filtering.
def All(-A: Type, -P: @-x: A -> Type, xs: List<&1, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case h <> t:
      E<P(h), All(A, P, t)>

# Prefix uses propositional equality of elements, not a Boolean comparator
# whose correctness would have to be assumed.
def Prefix(-A: Data, xs: List<&2, A>, ys: List<&2, A>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case x <> xt:
      match ys:
        case Nil{}:
          Empty
        case y <> yt:
          E<{x == y : A}, Prefix(A, xt, yt)>

law truth:
  Truth()

def truth():
  Unit{}

law and_intro:
  for -P: Type
  for -Q: Type
  for p: P
  for q: Q
  E<P, Q>

def and_intro(P, Q, p, q):
  Both{p, q}

law and_left:
  for -P: Type
  for -Q: Type
  for pq: E<P, Q>
  P

def and_left(P, Q, pq):
  match pq:
    case Both{p, q}:
      p

law and_right:
  for -P: Type
  for -Q: Type
  for pq: E<P, Q>
  Q

def and_right(P, Q, pq):
  match pq:
    case Both{p, q}:
      q

law and_commutes:
  for -P: Type
  for -Q: Type
  for pq: E<P, Q>
  E<Q, P>

def and_commutes(P, Q, pq):
  match pq:
    case Both{p, q}:
      Both{q, p}

law and_associates:
  for -P: Type
  for -Q: Type
  for -R: Type
  for pqr: E<E<P, Q>, R>
  E<P, E<Q, R>>

def and_associates(P, Q, R, pqr):
  match pqr:
    case Both{pq, r}:
      match pq:
        case Both{p, q}:
          Both{p, Both{q, r}}

law or_left:
  for -P: Type
  for -Q: Type
  for p: P
  Disjunction<P, Q>

def or_left(P, Q, p):
  Left{p}

law or_right:
  for -P: Type
  for -Q: Type
  for q: Q
  Disjunction<P, Q>

def or_right(P, Q, q):
  Right{q}

law or_eliminates:
  for -P: Type
  for -Q: Type
  for -R: Type
  for alternative: Disjunction<P, Q>
  for of_p: P -> R
  for of_q: Q -> R
  R

def or_eliminates(P, Q, R, alternative, of_p, of_q):
  match alternative:
    case Left{p}:
      of_p(p)
    case Right{q}:
      of_q(q)

law modus_ponens:
  for -P: Type
  for -Q: Type
  for implication: Implies(P, Q)
  for p: P
  Q

def modus_ponens(P, Q, implication, p):
  implication(p)

law ex_false:
  for -P: Type
  for impossible: Falsehood()
  P

def ex_false(P, impossible):
  match impossible:

law all_empty:
  for -A: Type
  for -P: @-x: A -> Type
  All(A, P, Nil{})

def all_empty(A, P):
  Unit{}

law all_cons:
  for -A: Type
  for -P: @-x: A -> Type
  for -h: A
  for -t: List<&1, A>
  for ph: P(h)
  for pt: All(A, P, t)
  All(A, P, h <> t)

def all_cons(A, P, h, t, ph, pt):
  Both{ph, pt}

law all_head:
  for -A: Type
  for -P: @-x: A -> Type
  for -h: A
  for -t: List<&1, A>
  for all: All(A, P, h <> t)
  P(h)

def all_head(A, P, h, t, all):
  match all:
    case Both{ph, pt}:
      ph

law all_tail:
  for -A: Type
  for -P: @-x: A -> Type
  for -h: A
  for -t: List<&1, A>
  for all: All(A, P, h <> t)
  All(A, P, t)

def all_tail(A, P, h, t, all):
  match all:
    case Both{ph, pt}:
      pt

law prefix_empty:
  for -A: Data
  for -xs: List<&2, A>
  Prefix(A, Nil{}, xs)

def prefix_empty(A, xs):
  Unit{}

law prefix_refl:
  for -A: Data
  for xs: List<&2, A>
  Prefix(A, xs, xs)

def prefix_refl(A, xs):
  match xs:
    case Nil{}:
      Unit{}
    case h <> t:
      Both{{==}, prefix_refl(A, t)}
