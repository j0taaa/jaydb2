# Algebra estrutural de Word para as inversoes do codec, sem axiomas.
import Base
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./Ordens.bend as O

def ajustar(n: Nat, m: Nat, w: Word(m)) -> Word(n):
  match n m:
    case 0n _:
      WNil{}
    case 1n+p 0n:
      Word.zero(1n+p)
    case 1n+p 1n+q:
      match w:
        case WCon{b, t}:
          WCon{b, ajustar(p, q, t)}

def um(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, Word.zero(p)}

law soma_zero_esquerda:
  for +n: Nat
  for +w: Word(n)
  {Word.add(n, Word.zero(n), w) == w : Word(n)}
def soma_zero_esquerda(n, w):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.add(p, Word.zero(p), t), t, soma_zero_esquerda(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
            Word.add(p, Word.zero(p), t), t, soma_zero_esquerda(p, t))

law soma_bit_zero:
  for n: Nat
  for b: Bool
  for x: Word(n)
  for y: Word(n)
  {Word.add(1n+n, WCon{b, x}, WCon{False{}, y}) ==
    WCon{b, Word.add(n, x, y)} : Word(1n+n)}
def soma_bit_zero(n, b, x, y):
  match b:
    case False{}:
      {==}
    case True{}:
      {==}

law deslocar_bit_zero:
  for n: Nat
  for w: Word(n)
  {Word.shl(1n+n, WCon{False{}, w}) == WCon{False{}, Word.shl(n, w)} : Word(1n+n)}
def deslocar_bit_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{b, t}:
          {==}

law multiplicar_preserva_bit_baixo:
  for +n: Nat
  for m: Nat
  for a: Word(m)
  for +b: Word(n)
  for +acc: Word(n)
  for +c: Bool
  {Word.mul.go(1n+n, m, a, WCon{False{}, b}, WCon{c, acc}) ==
    WCon{c, Word.mul.go(n, m, a, b, acc)} : Word(1n+n)}
def multiplicar_preserva_bit_baixo(n, m, a, b, acc, c):
  match m:
    case 0n:
      {==}
    case 1n+p:
      match a:
        case WCon{False{}, t}:
          %Equal.sym(Word(1n+n), Word.shl(1n+n, WCon{False{}, b}),
            WCon{False{}, Word.shl(n, b)}, deslocar_bit_zero(n, b)) :
            {Word.mul.go(1n+n, p, t, _, WCon{c, acc}) ==
              WCon{c, Word.mul.go(n, p, t, Word.shl(n, b), acc)} : Word(1n+n)}
          multiplicar_preserva_bit_baixo(n, p, t, Word.shl(n, b), acc, c)
        case WCon{True{}, t}:
          %Equal.sym(Word(1n+n), Word.shl(1n+n, WCon{False{}, b}),
            WCon{False{}, Word.shl(n, b)}, deslocar_bit_zero(n, b)) :
            {Word.mul.go(1n+n, p, t, _, Word.add(1n+n, WCon{c, acc}, WCon{False{}, b})) ==
              WCon{c, Word.mul.go(n, p, t, Word.shl(n, b), Word.add(n, acc, b))} : Word(1n+n)}
          %Equal.sym(Word(1n+n), Word.add(1n+n, WCon{c, acc}, WCon{False{}, b}),
            WCon{c, Word.add(n, acc, b)}, soma_bit_zero(n, c, acc, b)) :
            {Word.mul.go(1n+n, p, t, WCon{False{}, Word.shl(n, b)}, _) ==
              WCon{c, Word.mul.go(n, p, t, Word.shl(n, b), Word.add(n, acc, b))} : Word(1n+n)}
          multiplicar_preserva_bit_baixo(n, p, t, Word.shl(n, b), Word.add(n, acc, b), c)

law multiplicar_largura_zero:
  for m: Nat
  for w: Word(m)
  {Word.mul.go(0n, m, w, WNil{}, WNil{}) == WNil{} : Word(0n)}
def multiplicar_largura_zero(m, w):
  match m:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          multiplicar_largura_zero(p, t)
        case WCon{True{}, t}:
          multiplicar_largura_zero(p, t)

law deslocar_zero:
  for +n: Nat
  {Word.shl.put(n, False{}, Word.zero(n)) == Word.zero(n) : Word(n)}
def deslocar_zero(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), deslocar_zero(p))

law deslocar_um:
  for n: Nat
  {Word.shl(1n+n, um(1n+n)) == WCon{False{}, um(n)} : Word(1n+n)}
def deslocar_um(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Word(p), Word(2n+p), r => WCon{False{}, WCon{True{}, r}},
        Word.shl.put(p, False{}, Word.zero(p)), Word.zero(p), deslocar_zero(p))

law multiplicar_um_ajusta:
  for +n: Nat
  for +m: Nat
  for +w: Word(m)
  {Word.mul.go(n, m, w, um(n), Word.zero(n)) == ajustar(n, m, w) : Word(n)}
def multiplicar_um_ajusta(n, m, w):
  match n m:
    case 0n _:
      multiplicar_largura_zero(m, w)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      match w:
        case WCon{False{}, t}:
          %Equal.sym(Word(1n+p), Word.shl(1n+p, um(1n+p)),
            WCon{False{}, um(p)}, deslocar_um(p)) :
            {Word.mul.go(1n+p, q, t, _, Word.zero(1n+p)) == WCon{False{}, ajustar(p, q, t)} : Word(1n+p)}
          Equal.trans(Word(1n+p),
            Word.mul.go(1n+p, q, t, WCon{False{}, um(p)}, WCon{False{}, Word.zero(p)}),
            WCon{False{}, Word.mul.go(p, q, t, um(p), Word.zero(p))}, WCon{False{}, ajustar(p, q, t)},
            multiplicar_preserva_bit_baixo(p, q, t, um(p), Word.zero(p), False{}),
            Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
              Word.mul.go(p, q, t, um(p), Word.zero(p)), ajustar(p, q, t), multiplicar_um_ajusta(p, q, t)))

        case WCon{True{}, t}:
          %Equal.sym(Word(1n+p), Word.add(1n+p, Word.zero(1n+p), um(1n+p)),
            um(1n+p), soma_zero_esquerda(1n+p, um(1n+p))) :
            {Word.mul.go(1n+p, q, t, Word.shl(1n+p, um(1n+p)), _) == WCon{True{}, ajustar(p, q, t)} : Word(1n+p)}
          %Equal.sym(Word(1n+p), Word.shl(1n+p, um(1n+p)),
            WCon{False{}, um(p)}, deslocar_um(p)) :
            {Word.mul.go(1n+p, q, t, _, um(1n+p)) == WCon{True{}, ajustar(p, q, t)} : Word(1n+p)}
          Equal.trans(Word(1n+p),
            Word.mul.go(1n+p, q, t, WCon{False{}, um(p)}, WCon{True{}, Word.zero(p)}),
            WCon{True{}, Word.mul.go(p, q, t, um(p), Word.zero(p))}, WCon{True{}, ajustar(p, q, t)},
            multiplicar_preserva_bit_baixo(p, q, t, um(p), Word.zero(p), True{}),
            Equal.cong(Word(p), Word(1n+p), r => WCon{True{}, r},
              Word.mul.go(p, q, t, um(p), Word.zero(p)), ajustar(p, q, t), multiplicar_um_ajusta(p, q, t)))

# Os primeiros k bits sao os menos significativos.
def zeros_baixos(k: Nat, -n: Nat, w: Word(n)) -> Word(Nat.add(k, n)):
  match k:
    case 0n:
      w
    case 1n+p:
      WCon{False{}, zeros_baixos(p, n, w)}

law multiplicar_potencia_dois:
  for +k: Nat
  for +n: Nat
  for +m: Nat
  for +w: Word(m)
  {Word.mul.go(Nat.add(k, n), m, w, zeros_baixos(k, n, um(n)), Word.zero(Nat.add(k, n))) ==
    zeros_baixos(k, n, ajustar(n, m, w)) : Word(Nat.add(k, n))}
def multiplicar_potencia_dois(k, n, m, w):
  match k:
    case 0n:
      multiplicar_um_ajusta(n, m, w)
    case 1n+p:
      Equal.trans(Word(1n+Nat.add(p, n)),
        Word.mul.go(1n+Nat.add(p, n), m, w, WCon{False{}, zeros_baixos(p, n, um(n))}, WCon{False{}, Word.zero(Nat.add(p, n))}),
        WCon{False{}, Word.mul.go(Nat.add(p, n), m, w, zeros_baixos(p, n, um(n)), Word.zero(Nat.add(p, n)))},
        WCon{False{}, zeros_baixos(p, n, ajustar(n, m, w))},
        multiplicar_preserva_bit_baixo(Nat.add(p, n), m, w, zeros_baixos(p, n, um(n)), Word.zero(Nat.add(p, n)), False{}),
        Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
          Word.mul.go(Nat.add(p, n), m, w, zeros_baixos(p, n, um(n)), Word.zero(Nat.add(p, n))),
          zeros_baixos(p, n, ajustar(n, m, w)), multiplicar_potencia_dois(p, n, m, w)))

# Concatenacao binaria: lo ocupa os k bits menos significativos.
def juntar(k: Nat, -n: Nat, lo: Word(k), hi: Word(n)) -> Word(Nat.add(k, n)):
  match k:
    case 0n:
      hi
    case 1n+p:
      match lo:
        case WCon{b, t}:
          WCon{b, juntar(p, n, t, hi)}

def uns(n: Nat) -> Word(n):
  match n:
    case 0n:
      WNil{}
    case 1n+p:
      WCon{True{}, uns(p)}

law soma_zero_direita:
  for +n: Nat
  for +w: Word(n)
  {Word.add(n, w, Word.zero(n)) == w : Word(n)}
def soma_zero_direita(n, w):
  Equal.trans(Word(n), Word.add(n, w, Word.zero(n)), Word.add(n, Word.zero(n), w), w,
    Word.add_comm(n, w, Word.zero(n)), soma_zero_esquerda(n, w))

law soma_blocos_separados:
  for +k: Nat
  for +n: Nat
  for +lo: Word(k)
  for +hi: Word(n)
  {Word.add(Nat.add(k, n), zeros_baixos(k, n, hi), juntar(k, n, lo, Word.zero(n))) ==
    juntar(k, n, lo, hi) : Word(Nat.add(k, n))}
def soma_blocos_separados(k, n, lo, hi):
  match k:
    case 0n:
      soma_zero_direita(n, hi)
    case 1n+p:
      match lo:
        case WCon{False{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.add(Nat.add(p, n), zeros_baixos(p, n, hi), juntar(p, n, t, Word.zero(n))),
            juntar(p, n, t, hi), soma_blocos_separados(p, n, t, hi))
        case WCon{True{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.add(Nat.add(p, n), zeros_baixos(p, n, hi), juntar(p, n, t, Word.zero(n))),
            juntar(p, n, t, hi), soma_blocos_separados(p, n, t, hi))

law mascara_zero:
  for +n: Nat
  for +w: Word(n)
  {Word.and(n, w, Word.zero(n)) == Word.zero(n) : Word(n)}
def mascara_zero(n, w):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.and(p, t, Word.zero(p)), Word.zero(p), mascara_zero(p, t))
        case WCon{True{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r},
            Word.and(p, t, Word.zero(p)), Word.zero(p), mascara_zero(p, t))

law mascara_baixa:
  for +k: Nat
  for +n: Nat
  for +w: Word(Nat.add(k, n))
  {Word.and(Nat.add(k, n), w, juntar(k, n, uns(k), Word.zero(n))) ==
    juntar(k, n, ajustar(k, Nat.add(k, n), w), Word.zero(n)) : Word(Nat.add(k, n))}
def mascara_baixa(k, n, w):
  match k:
    case 0n:
      mascara_zero(n, w)
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{False{}, r},
            Word.and(Nat.add(p, n), t, juntar(p, n, uns(p), Word.zero(n))),
            juntar(p, n, ajustar(p, Nat.add(p, n), t), Word.zero(n)), mascara_baixa(p, n, t))
        case WCon{True{}, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{True{}, r},
            Word.and(Nat.add(p, n), t, juntar(p, n, uns(p), Word.zero(n))),
            juntar(p, n, ajustar(p, Nat.add(p, n), t), Word.zero(n)), mascara_baixa(p, n, t))

# Uma comparacao lexicografica nao pode esconder uma cauda maior.

law limite_da_cauda:
  for a: Bool
  for b: Bool
  for c: Cmp
  for e: {Cmp.is_le(Word.cmp.fin(a, b, c)) == True{} : Bool}
  {Cmp.is_le(c) == True{} : Bool}
def limite_da_cauda(a, b, c, e):
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      e

law palavra_ate_zero:
  for +n: Nat
  for +w: Word(n)
  for +e: {Cmp.is_le(Word.cmp(n, w, Word.zero(n))) == True{} : Bool}
  {w == Word.zero(n) : Word(n)}
def palavra_ate_zero(n, w, e):
  match n:
    case 0n:
      match w:
        case WNil{}:
          {==}
    case 1n+p:
      match w:
        case WCon{False{}, t}:
          Equal.cong(Word(p), Word(1n+p), r => WCon{False{}, r}, t, Word.zero(p),
            palavra_ate_zero(p, t, limite_da_cauda(False{}, False{}, Word.cmp(p, t, Word.zero(p)), e)))
        case WCon{True{}, t}:
          cauda = palavra_ate_zero(p, t, limite_da_cauda(True{}, False{}, Word.cmp(p, t, Word.zero(p)), e))
          ordem = Equal.trans(Cmp, Word.cmp(p, t, Word.zero(p)), Word.cmp(p, Word.zero(p), Word.zero(p)), EQ{},
            Equal.cong(Word(p), Cmp, r => Word.cmp(p, r, Word.zero(p)), t, Word.zero(p), cauda), O.word_refl(p, Word.zero(p)))
          F.absurdo_booleano({WCon{True{}, t} == Word.zero(1n+p) : Word(1n+p)},
            Equal.trans(Bool, False{}, Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.zero(p)))), True{},
              Equal.sym(Bool, Cmp.is_le(Word.cmp.fin(True{}, False{}, Word.cmp(p, t, Word.zero(p)))), False{},
                Equal.cong(Cmp, Bool, c => Cmp.is_le(Word.cmp.fin(True{}, False{}, c)), Word.cmp(p, t, Word.zero(p)), EQ{}, ordem)), e))

law limite_bits_baixos:
  for +k: Nat
  for +n: Nat
  for +w: Word(Nat.add(k, n))
  for e: {Cmp.is_le(Word.cmp(Nat.add(k, n), w, juntar(k, n, uns(k), Word.zero(n)))) == True{} : Bool}
  {w == juntar(k, n, ajustar(k, Nat.add(k, n), w), Word.zero(n)) : Word(Nat.add(k, n))}
def limite_bits_baixos(k, n, w, e):
  match k:
    case 0n:
      palavra_ate_zero(n, w, e)
    case 1n+p:
      match w:
        case WCon{b, t}:
          Equal.cong(Word(Nat.add(p, n)), Word(1n+Nat.add(p, n)), r => WCon{b, r},
            t, juntar(p, n, ajustar(p, Nat.add(p, n), t), Word.zero(n)),
            limite_bits_baixos(p, n, t, limite_da_cauda(b, True{}, Word.cmp(Nat.add(p, n), t, juntar(p, n, uns(p), Word.zero(n))), e)))
