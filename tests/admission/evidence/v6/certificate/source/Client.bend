import Base
import ./Dados.bend as D
import ./Semantica.bend as S

def contar(xs: List<U32>, acc: U32) -> U32:
  match xs:
    case Nil{}:
      acc
    case Con{h, t}:
      contar(t, (acc + h : U32))

def programa() -> S.Programa:
  S.Programa{c => a => S.Recusar{D.VInt{0, contar([1, 2, 3], 0)}}}

def f(~p: Nat, n: Nat) -> Nat:
  match n:
    case Zero{}:
      p
    case Succ{x}:
      f(p, x)
def reflexive(p: Nat, n: Nat) -> {f(p, n) == f(p, n) : Nat}:
  {==}
def theorem(n: Nat) -> {f(3n, n) == f(3n, n) : Nat}:
  reflexive(3n, n)
