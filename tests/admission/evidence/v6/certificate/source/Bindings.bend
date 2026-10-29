import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Requisitos.bend as R
import ./Instance.bend as I
import ./Client.bend as Client
import ./Interface.bend as F

def codigo() -> String:
  "import Base\nimport ./Dados.bend as D\nimport ./Semantica.bend as S\n\ndef contar(xs: List<U32>, acc: U32) -> U32:\n  match xs:\n    case Nil{}:\n      acc\n    case Con{h, t}:\n      contar(t, (acc + h : U32))\n\ndef programa() -> S.Programa:\n  S.Programa{c => a => S.Recusar{D.VInt{0, contar([1, 2, 3], 0)}}}\n\ndef f(~p: Nat, n: Nat) -> Nat:\n  match n:\n    case Zero{}:\n      p\n    case Succ{x}:\n      f(p, x)\ndef reflexive(p: Nat, n: Nat) -> {f(p, n) == f(p, n) : Nat}:\n  {==}\ndef theorem(n: Nat) -> {f(3n, n) == f(3n, n) : Nat}:\n  reflexive(3n, n)\n"

law certificado:
  R.Certifica(I.config(), codigo(), Client.programa(), I.contexto(), I.argumentos())

law termina:
  F.ProgramaTermina(I.config(), Client.programa())
