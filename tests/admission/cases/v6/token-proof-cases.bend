import Base
type Token is Type:
  Token{f: @n: Nat -> Nat}
def f(~p: Nat, t: Token, n: Nat) -> Nat:
  match t:
    case Token{g}: g(Nat.add(p, n))
def invoke(t: Token, n: Nat) -> Nat:
  match t:
    case Token{g}: g(n)
def lemma(k: Nat, g: @n: Nat -> Nat, n: Nat) -> {Nat.is_ge(g(n),g(n)) == True{} : Bool}:
  match k:
    case Zero{}: Nat.ge_refl(g(n))
    case Succ{x}: lemma(x,g,n)
def take(k: Nat, t: Token, n: Nat) -> {Nat.is_ge(invoke(t,n),invoke(t,n)) == True{} : Bool}:
  match t:
    case Token{g}: lemma(k,g,n)
def innerProof(k: Nat, t: Token, n: Nat) -> {Nat.is_ge(f(3n,t,n),f(3n,t,n)) == True{} : Bool}:
  take(k,Token{z => f(3n,t,z)},n)

def main(k: Nat, t: Token, n: Nat) -> {Nat.is_ge(f(3n,t,n),f(3n,t,n)) == True{} : Bool}:
  match k:
    case Zero{}: innerProof(0n,t,n)
    case Succ{x}: main(x,t,n)
