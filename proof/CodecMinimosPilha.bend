# Minimos matematicos EXATOS de toda pilha cujos contadores sao medidos.
# O resultado inclui None no overflow; nao presume que as somas cabem.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecContadores.bend as N
import ./CodecSomas.bend as S

law multiplicar_por_zero_direito:
  for k: Nat
  {Nat.mul(k, 0n) == 0n : Nat}
def multiplicar_por_zero_direito(k):
  match k:
    case 0n:
      {==}
    case 1n+p:
      multiplicar_por_zero_direito(p)

law somar_pendencia_nat64_exato:
  for +n: Nat
  for +q: B.Numero64
  for +fator: Nat
  for +resto: Nat
  for +medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  {C.somar_pendencia(q, fator, B.nat64(resto)) == B.nat64(Nat.add(Nat.mul(fator, n), resto)) : Maybe<&2, B.Numero64>}
def somar_pendencia_nat64_exato(n, q, fator, resto, medido):
  match n:
    case 0n:
      %F.algum_injetivo(B.Numero64, B.Numero64{0, 0}, q, medido) :
        {C.somar_pendencia(_, fator, B.nat64(resto)) == B.nat64(Nat.add(Nat.mul(fator, 0n), resto)) : Maybe<&2, B.Numero64>}
      %Equal.sym(Nat, Nat.mul(fator, 0n), 0n, multiplicar_por_zero_direito(fator)) :
        {B.nat64(resto) == B.nat64(Nat.add(_, resto)) : Maybe<&2, B.Numero64>}
      {==}
    case 1n+p:
      %Equal.sym(Bool, C.zero64(q), False{}, N.zero64_reflete_contagem_natural(1n+p, q, medido)) :
        {C.somar_pendencia_casos(_, q, fator, B.nat64(resto)) == B.nat64(Nat.add(Nat.mul(fator, 1n+p), resto)) : Maybe<&2, B.Numero64>}
      %Equal.sym(Maybe<&2, B.Numero64>, C.multiplicar_pequeno(fator, q), B.nat64(Nat.mul(fator, 1n+p)), S.multiplicar_pequeno_nat64_exato(fator, 1n+p, q, medido)) :
        {C.somar_opcionais(_, B.nat64(resto)) == B.nat64(Nat.add(Nat.mul(fator, 1n+p), resto)) : Maybe<&2, B.Numero64>}
      S.somar_opcionais_nat64_exato(Nat.mul(fator, 1n+p), resto)

type ContadorMedido<-q: B.Numero64> is Type:
  ContadorMedido{natural: Nat, medida: {B.nat64(natural) == Some{q} : Maybe<&2, B.Numero64>}}

# Apenas as contagens naturais de cada frame. Nao ha premissa de tamanho
# minimo, canonicidade do decoder ou correcao de conferir.
def MedidasPilha(pilha: C.Pilha) -> Type:
  match pilha:
    case C.Raiz{}:
      Unit
    case C.Lista{u, q, xs, pai}:
      L.E<ContadorMedido<q>, MedidasPilha(pai)>
    case C.Nome{u, q, anterior, xs, pai}:
      L.E<ContadorMedido<q>, MedidasPilha(pai)>
    case C.Campo{u, q, nome, xs, pai}:
      L.E<ContadorMedido<q>, MedidasPilha(pai)>

type MinimoExato<-pilha: C.Pilha> is Type:
  MinimoExato{natural: Nat, exato: {C.minimo_pilha(pilha) == B.nat64(natural) : Maybe<&2, B.Numero64>}}

def minimo_lista(+u: Bool, +q: B.Numero64, -xs: List<&2, D.Valor>, +pai: C.Pilha,
  +n: Nat, medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>},
  minimo_pai: MinimoExato<pai>) -> MinimoExato<C.Lista{u, q, xs, pai}>:
  match minimo_pai:
    case MinimoExato{+resto, exato}:
      MinimoExato{Nat.add(Nat.mul(1n, n), resto),
        (%Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(resto), exato) :
          {C.somar_pendencia(q, 1n, _) == B.nat64(Nat.add(Nat.mul(1n, n), resto)) : Maybe<&2, B.Numero64>}
          somar_pendencia_nat64_exato(n, q, 1n, resto, medido))}

def minimo_campo(+u: Bool, +q: B.Numero64, -nome: String, -xs: List<&2, D.Campo>, +pai: C.Pilha,
  +n: Nat, medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>},
  minimo_pai: MinimoExato<pai>) -> MinimoExato<C.Campo{u, q, nome, xs, pai}>:
  match minimo_pai:
    case MinimoExato{+resto, exato}:
      MinimoExato{Nat.add(Nat.mul(11n, n), resto),
        (%Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(resto), exato) :
          {C.somar_pendencia(q, 11n, _) == B.nat64(Nat.add(Nat.mul(11n, n), resto)) : Maybe<&2, B.Numero64>}
          somar_pendencia_nat64_exato(n, q, 11n, resto, medido))}

def minimo_nome(+u: Bool, +q: B.Numero64, -anterior: String, -xs: List<&2, D.Campo>, +pai: C.Pilha,
  +n: Nat, medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>},
  minimo_pai: MinimoExato<pai>) -> MinimoExato<C.Nome{u, q, anterior, xs, pai}>:
  match minimo_pai:
    case MinimoExato{+resto, exato}:
      MinimoExato{1n+Nat.add(Nat.mul(11n, n), resto),
        (%Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pai), B.nat64(resto), exato) :
          {C.somar_opcionais(Some{B.Numero64{0, 1}}, C.somar_pendencia(q, 11n, _)) == B.nat64(1n+Nat.add(Nat.mul(11n, n), resto)) : Maybe<&2, B.Numero64>}
          %Equal.sym(Maybe<&2, B.Numero64>, C.somar_pendencia(q, 11n, B.nat64(resto)), B.nat64(Nat.add(Nat.mul(11n, n), resto)), somar_pendencia_nat64_exato(n, q, 11n, resto, medido)) :
            {C.somar_opcionais(B.nat64(1n), _) == B.nat64(1n+Nat.add(Nat.mul(11n, n), resto)) : Maybe<&2, B.Numero64>}
          S.somar_opcionais_nat64_exato(1n, Nat.add(Nat.mul(11n, n), resto)))}

law todos_os_minimos_de_pilha_medida_sao_exatos:
  for +pilha: C.Pilha
  for medidas: MedidasPilha(pilha)
  MinimoExato<pilha>
def todos_os_minimos_de_pilha_medida_sao_exatos(pilha, medidas):
  match pilha:
    case C.Raiz{}:
      MinimoExato{0n, {==}}
    case C.Lista{+u, +q, xs, +pai}:
      match medidas:
        case L.Ambos{ContadorMedido{n, medido}, acima}:
          minimo_lista(u, q, xs, pai, n, medido, todos_os_minimos_de_pilha_medida_sao_exatos(pai, acima))
    case C.Campo{+u, +q, nome, xs, +pai}:
      match medidas:
        case L.Ambos{ContadorMedido{n, medido}, acima}:
          minimo_campo(u, q, nome, xs, pai, n, medido, todos_os_minimos_de_pilha_medida_sao_exatos(pai, acima))
    case C.Nome{+u, +q, anterior, xs, +pai}:
      match medidas:
        case L.Ambos{ContadorMedido{n, medido}, acima}:
          minimo_nome(u, q, anterior, xs, pai, n, medido, todos_os_minimos_de_pilha_medida_sao_exatos(pai, acima))

def fator_campo(f: C.Finalidade) -> Nat:
  match f:
    case C.ContaRegistro{}:
      11n
    case _:
      1n

def minimo_unitario(+n: Nat, -q: B.Numero64,
  medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}) ->
  {Some{q} == B.nat64(Nat.mul(1n, n)) : Maybe<&2, B.Numero64>}:
  %Equal.sym(Nat, Nat.add(n, 0n), n, S.nat_somar_zero_direita(n)) :
    {Some{q} == B.nat64(_) : Maybe<&2, B.Numero64>}
  Equal.sym(Maybe<&2, B.Numero64>, B.nat64(n), Some{q}, medido)

law todos_os_minimos_de_campo_medido_sao_exatos:
  for +f: C.Finalidade
  for +n: Nat
  for +q: B.Numero64
  for medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  {C.minimo_campo(f, q) == B.nat64(Nat.mul(fator_campo(f), n)) : Maybe<&2, B.Numero64>}
def todos_os_minimos_de_campo_medido_sao_exatos(f, n, q, medido):
  match f:
    case C.ContaRegistro{}:
      S.multiplicar_pequeno_nat64_exato(11n, n, q, medido)
    case C.Inteiro{}:
      minimo_unitario(n, q, medido)
    case C.Texto{}:
      minimo_unitario(n, q, medido)
    case C.NomeTexto{}:
      minimo_unitario(n, q, medido)
    case C.ContaLista{}:
      minimo_unitario(n, q, medido)

law minimo_de_campo_e_pilha_medido_e_exato:
  for +f: C.Finalidade
  for +n: Nat
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +m: Nat
  for medido: {B.nat64(n) == Some{q} : Maybe<&2, B.Numero64>}
  for minimo: {C.minimo_pilha(pilha) == B.nat64(m) : Maybe<&2, B.Numero64>}
  {C.somar_opcionais(C.minimo_campo(f, q), C.minimo_pilha(pilha)) == B.nat64(Nat.add(Nat.mul(fator_campo(f), n), m)) : Maybe<&2, B.Numero64>}
def minimo_de_campo_e_pilha_medido_e_exato(f, n, q, pilha, m, medido, minimo):
  %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_campo(f, q), B.nat64(Nat.mul(fator_campo(f), n)), todos_os_minimos_de_campo_medido_sao_exatos(f, n, q, medido)) :
    {C.somar_opcionais(_, C.minimo_pilha(pilha)) == B.nat64(Nat.add(Nat.mul(fator_campo(f), n), m)) : Maybe<&2, B.Numero64>}
  %Equal.sym(Maybe<&2, B.Numero64>, C.minimo_pilha(pilha), B.nat64(m), minimo) :
    {C.somar_opcionais(B.nat64(Nat.mul(fator_campo(f), n)), _) == B.nat64(Nat.add(Nat.mul(fator_campo(f), n), m)) : Maybe<&2, B.Numero64>}
  S.somar_opcionais_nat64_exato(Nat.mul(fator_campo(f), n), m)
