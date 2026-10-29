# Aritmetica geral dos tamanhos reais do codec, inclusive None no overflow.
# Esta entrada nao afirma a Lei 2 completa do executavel.
import Base
import ../contrato/Bytes.bend as B
import ../src/Codec.bend as C
import ./CodecSomasBits.bend as S
import ./CodecSomas64.bend as P

# Resultado TOTAL: nenhuma premissa de representabilidade e necessaria.
# Se um operando ja transbordou, o resultado matematico tambem e None.
law somar_opcionais_nat64_exato:
  for +n: Nat
  for +m: Nat
  {C.somar_opcionais(B.nat64(n), B.nat64(m)) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Numero64>}
def somar_opcionais_nat64_exato(n, m):
  P.representar_injetiva(C.somar_opcionais(B.nat64(n), B.nat64(m)), B.nat64(Nat.add(n, m)),
    Equal.trans(Maybe<&2, Word(64n)>,
      P.representar(C.somar_opcionais(B.nat64(n), B.nat64(m))),
      S.somar_opcionais(64n, P.representar(B.nat64(n)), P.representar(B.nat64(m))),
      P.representar(B.nat64(Nat.add(n, m))),
      P.somar_opcionais_representa_soma_binaria(B.nat64(n), B.nat64(m)),
      Equal.trans(Maybe<&2, Word(64n)>,
        S.somar_opcionais(64n, P.representar(B.nat64(n)), P.representar(B.nat64(m))),
        S.natural(64n, Nat.add(n, m)), P.representar(B.nat64(Nat.add(n, m))),
        P.soma_naturais_representados(n, m),
        Equal.sym(Maybe<&2, Word(64n)>, P.representar(B.nat64(Nat.add(n, m))), S.natural(64n, Nat.add(n, m)), P.nat64_representa_natural_binario(Nat.add(n, m))))))

# Teorema pedido sobre a funcao real, para quaisquer contagens e palavras.
law somar64_nat64_exato:
  for +n: Nat
  for +m: Nat
  for +x: B.Numero64
  for +y: B.Numero64
  for nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Numero64>}
  for my: {B.nat64(m) == Some{y} : Maybe<&2, B.Numero64>}
  {C.somar64(x, y) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Numero64>}
def somar64_nat64_exato(n, m, x, y, nx, my):
  %nx :
    {C.somar_opcionais(_, Some{y}) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Numero64>}
  %my :
    {C.somar_opcionais(B.nat64(n), _) == B.nat64(Nat.add(n, m)) : Maybe<&2, B.Numero64>}
  somar_opcionais_nat64_exato(n, m)

law nat_somar_zero_direita:
  for +n: Nat
  {Nat.add(n, 0n) == n : Nat}
def nat_somar_zero_direita(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, Nat.add(p, 0n), p, nat_somar_zero_direita(p))

# Nao se exige que o produto caiba: o resultado pode ser None.
law multiplicar_pequeno_nat64_exato:
  for +k: Nat
  for +n: Nat
  for +x: B.Numero64
  for +nx: {B.nat64(n) == Some{x} : Maybe<&2, B.Numero64>}
  {C.multiplicar_pequeno(k, x) == B.nat64(Nat.mul(k, n)) : Maybe<&2, B.Numero64>}
def multiplicar_pequeno_nat64_exato(k, n, x, nx):
  match k:
    case 0n:
      {==}
    case 1n:
      %Equal.sym(Nat, Nat.add(n, 0n), n, nat_somar_zero_direita(n)) :
        {Some{x} == B.nat64(_) : Maybe<&2, B.Numero64>}
      Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{x}, nx)
    case 2n+p:
      %nx :
        {C.somar_opcionais(_, C.multiplicar_pequeno(1n+p, x)) == B.nat64(Nat.add(n, Nat.mul(1n+p, n))) : Maybe<&2, B.Numero64>}
      %Equal.sym(Maybe<&2, B.Numero64>, C.multiplicar_pequeno(1n+p, x), B.nat64(Nat.mul(1n+p, n)), multiplicar_pequeno_nat64_exato(1n+p, n, x, nx)) :
        {C.somar_opcionais(B.nat64(n), _) == B.nat64(Nat.add(n, Nat.mul(1n+p, n))) : Maybe<&2, B.Numero64>}
      somar_opcionais_nat64_exato(n, Nat.mul(1n+p, n))
