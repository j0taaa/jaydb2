# Injetividade da conversao real de Word/U32 para Nat, sem axiomas.
# Apoio a extracao das tags; nenhuma propriedade do codec e pressuposta.
import Base

def impossivel(-A: Type, e: Empty) -> A:
  match e:

def metade(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n:
      0n
    case 2n+p:
      1n+metade(p)

def paridade(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n:
      True{}
    case 2n+p:
      paridade(p)

law metade_dobro:
  for +n: Nat
  {metade(Nat.double(n)) == n : Nat}
def metade_dobro(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, metade(Nat.double(p)), p, metade_dobro(p))

law metade_sucessor_dobro:
  for +n: Nat
  {metade(1n+Nat.double(n)) == n : Nat}
def metade_sucessor_dobro(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, metade(1n+Nat.double(p)), p,
        metade_sucessor_dobro(p))

law paridade_dobro:
  for n: Nat
  {paridade(Nat.double(n)) == False{} : Bool}
def paridade_dobro(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      paridade_dobro(p)

law paridade_sucessor_dobro:
  for n: Nat
  {paridade(1n+Nat.double(n)) == True{} : Bool}
def paridade_sucessor_dobro(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      paridade_sucessor_dobro(p)

law dobro_injetivo:
  for +a: Nat
  for +b: Nat
  for e: {Nat.double(a) == Nat.double(b) : Nat}
  {a == b : Nat}
def dobro_injetivo(a, b, e):
  Equal.trans(Nat, a, metade(Nat.double(a)), b,
    Equal.sym(Nat, metade(Nat.double(a)), a, metade_dobro(a)),
    Equal.trans(Nat, metade(Nat.double(a)), metade(Nat.double(b)), b,
      Equal.cong(Nat, Nat, r => metade(r), Nat.double(a), Nat.double(b), e),
      metade_dobro(b)))

law sucessor_dobro_injetivo:
  for +a: Nat
  for +b: Nat
  for e: {1n+Nat.double(a) == 1n+Nat.double(b) : Nat}
  {a == b : Nat}
def sucessor_dobro_injetivo(a, b, e):
  Equal.trans(Nat, a, metade(1n+Nat.double(a)), b,
    Equal.sym(Nat, metade(1n+Nat.double(a)), a, metade_sucessor_dobro(a)),
    Equal.trans(Nat, metade(1n+Nat.double(a)), metade(1n+Nat.double(b)), b,
      Equal.cong(Nat, Nat, r => metade(r), 1n+Nat.double(a), 1n+Nat.double(b), e),
      metade_sucessor_dobro(b)))

def dobro_nao_sucessor_dobro(+a: Nat, +b: Nat,
  e: {Nat.double(a) == 1n+Nat.double(b) : Nat}) -> Empty:
  falso = Equal.trans(Bool, False{}, paridade(Nat.double(a)), True{},
    Equal.sym(Bool, paridade(Nat.double(a)), False{}, paridade_dobro(a)),
    Equal.trans(Bool, paridade(Nat.double(a)), paridade(1n+Nat.double(b)), True{},
      Equal.cong(Nat, Bool, r => paridade(r), Nat.double(a), 1n+Nat.double(b), e),
      paridade_sucessor_dobro(b)))
  %falso : Bool.pick(Type, _, Empty, Unit)
  Unit{}

# Inducao na largura, recuperando o bit baixo pela paridade e a cauda
# pelo cancelamento de double. Vale para qualquer largura, inclusive zero.
law word_to_nat_injetivo:
  for +n: Nat
  for +a: Word(n)
  for +b: Word(n)
  for e: {Word.to_nat(n, a) == Word.to_nat(n, b) : Nat}
  {a == b : Word(n)}
def word_to_nat_injetivo(n, a, b, e):
  match n:
    case 0n:
      match a b:
        case WNil{} WNil{}:
          {==}
    case 1n+p:
      match a b:
        case WCon{False{}, +at} WCon{False{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, at, bt,
            word_to_nat_injetivo(p, at, bt,
              dobro_injetivo(Word.to_nat(p, at), Word.to_nat(p, bt), e)))
        case WCon{False{}, at} WCon{True{}, bt}:
          impossivel({WCon{False{}, at} == WCon{True{}, bt} : Word(1n+p)},
            dobro_nao_sucessor_dobro(Word.to_nat(p, at), Word.to_nat(p, bt), e))
        case WCon{True{}, at} WCon{False{}, bt}:
          impossivel({WCon{True{}, at} == WCon{False{}, bt} : Word(1n+p)},
            dobro_nao_sucessor_dobro(Word.to_nat(p, bt), Word.to_nat(p, at),
              Equal.sym(Nat, 1n+Nat.double(Word.to_nat(p, at)), Nat.double(Word.to_nat(p, bt)), e)))
        case WCon{True{}, +at} WCon{True{}, +bt}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r}, at, bt,
            word_to_nat_injetivo(p, at, bt,
              sucessor_dobro_injetivo(Word.to_nat(p, at), Word.to_nat(p, bt), e)))

law u32_to_nat_injetivo:
  for +a: U32
  for +b: U32
  for e: {U32.to_nat(a) == U32.to_nat(b) : Nat}
  {a == b : U32}
def u32_to_nat_injetivo(a, b, e):
  match a b:
    case U32{+aw} U32{+bw}:
      Equal.cong(Word(32n), U32, r => U32{r}, aw, bw,
        word_to_nat_injetivo(32n, aw, bw, e))
