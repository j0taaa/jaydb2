# Segmentos reais, em ordem de leitura. As premissas sao codificacoes do
# contrato para CADA elemento, nunca desigualdades de tamanho.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecTamanhos.bend as T
import ./CodecLimitesNomes.bend as N
import ./CodecCanonico.bend as K
import ./CodecSomas.bend as A

law soma_associativa:
  for a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}
def soma_associativa(a, b, c):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), soma_associativa(p, b, c))

law soma_comutativa:
  for +a: Nat
  for +b: Nat
  {Nat.add(a, b) == Nat.add(b, a) : Nat}
def soma_comutativa(a, b):
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, A.nat_somar_zero_direita(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p),
        Equal.cong(Nat, Nat, r => 1n+r, Nat.add(p, b), Nat.add(b, p), soma_comutativa(p, b)),
        Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), K.soma_sucessor_direito(b, p)))

law trocar_parcelas_iniciais:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}
def trocar_parcelas_iniciais(a, b, c):
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), soma_associativa(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, r => Nat.add(r, c), Nat.add(a, b), Nat.add(b, a), soma_comutativa(a, b)),
      soma_associativa(b, a, c)))

law multiplicar_sucessor_direito:
  for +k: Nat
  for +n: Nat
  {Nat.mul(k, 1n+n) == Nat.add(k, Nat.mul(k, n)) : Nat}
def multiplicar_sucessor_direito(k, n):
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, r => 1n+r,
        Nat.add(n, Nat.mul(p, 1n+n)), Nat.add(p, Nat.add(n, Nat.mul(p, n))),
        Equal.trans(Nat, Nat.add(n, Nat.mul(p, 1n+n)), Nat.add(n, Nat.add(p, Nat.mul(p, n))), Nat.add(p, Nat.add(n, Nat.mul(p, n))),
          Equal.cong(Nat, Nat, r => Nat.add(n, r), Nat.mul(p, 1n+n), Nat.add(p, Nat.mul(p, n)), multiplicar_sucessor_direito(p, n)),
          trocar_parcelas_iniciais(n, p, Nat.mul(p, n))))

law limite_reflexivo:
  for +n: Nat
  {Nat.is_le(n, n) == True{} : Bool}
def limite_reflexivo(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      limite_reflexivo(p)

law limite_transitivo:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  for bc: {Nat.is_le(b, c) == True{} : Bool}
  {Nat.is_le(a, c) == True{} : Bool}
def limite_transitivo(a, b, c, ab, bc):
  match a b c:
    case 0n _ _:
      T.zero_natural_nao_maior(c)
    case 1n+p 0n _:
      F.absurdo_booleano({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      F.absurdo_booleano({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      limite_transitivo(p, q, r, ab, bc)

type ValorSegmentado is Data:
  ValorSegmentado{valor: D.Valor, bytes: List<&2, U32>}

type CampoSegmentado is Data:
  CampoSegmentado{nome: String, valor: D.Valor, nome_bytes: List<&2, U32>, valor_bytes: List<&2, U32>}

def ValoresCanonicos(xs: List<&2, ValorSegmentado>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{ValorSegmentado{v, bs}, t}:
      L.E<P.Codificacao(v, bs), ValoresCanonicos(t)>

def CamposCanonicos(xs: List<&2, CampoSegmentado>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{CampoSegmentado{n, v, nb, vb}, t}:
      L.E<{D.nome_valido(n) == True{} : Bool},
        L.E<{P.texto(n) == Some{nb} : Maybe<&2, List<&2, U32>>},
          L.E<P.Codificacao(v, vb), CamposCanonicos(t)>>>

def quantidade_valores(xs: List<&2, ValorSegmentado>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+quantidade_valores(t)

def quantidade_campos(xs: List<&2, CampoSegmentado>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{h, t}:
      1n+quantidade_campos(t)

def bytes_valores(xs: List<&2, ValorSegmentado>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{ValorSegmentado{v, bs}, t}:
      B.concatenar(bs, bytes_valores(t))

def bytes_campos(xs: List<&2, CampoSegmentado>) -> List<&2, U32>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{CampoSegmentado{n, v, nb, vb}, t}:
      B.concatenar(B.concatenar(nb, vb), bytes_campos(t))

def valores(xs: List<&2, ValorSegmentado>) -> List<&2, D.Valor>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{ValorSegmentado{v, bs}, t}:
      Con{v, valores(t)}

def campos(xs: List<&2, CampoSegmentado>) -> List<&2, D.Campo>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{CampoSegmentado{n, v, nb, vb}, t}:
      Con{D.Campo{n, v}, campos(t)}

law sequencia_de_valores_canonicos_exige_um_octeto_por_valor:
  for +xs: List<&2, ValorSegmentado>
  for canonicos: ValoresCanonicos(xs)
  {Nat.is_le(quantidade_valores(xs), B.comprimento(bytes_valores(xs))) == True{} : Bool}
def sequencia_de_valores_canonicos_exige_um_octeto_por_valor(xs, canonicos):
  match xs:
    case Nil{}:
      {==}
    case Con{ValorSegmentado{+v, +bs}, +t}:
      match canonicos:
        case L.Ambos{cabeca, cauda}:
          %Equal.sym(Nat, B.comprimento(B.concatenar(bs, bytes_valores(t))), Nat.add(B.comprimento(bs), B.comprimento(bytes_valores(t))), N.comprimento_concatenacao(bs, bytes_valores(t))) :
            {Nat.is_le(1n+quantidade_valores(t), _) == True{} : Bool}
          N.somar_preserva_limites(1n, quantidade_valores(t), B.comprimento(bs), B.comprimento(bytes_valores(t)),
            T.todo_valor_canonico_exige_pelo_menos_um_octeto(v, bs, cabeca),
            sequencia_de_valores_canonicos_exige_um_octeto_por_valor(t, cauda))

law sequencia_de_campos_canonicos_exige_onze_octetos_por_campo:
  for +xs: List<&2, CampoSegmentado>
  for canonicos: CamposCanonicos(xs)
  {Nat.is_le(Nat.mul(11n, quantidade_campos(xs)), B.comprimento(bytes_campos(xs))) == True{} : Bool}
def sequencia_de_campos_canonicos_exige_onze_octetos_por_campo(xs, canonicos):
  match xs:
    case Nil{}:
      {==}
    case Con{CampoSegmentado{+n, +v, +nb, +vb}, +t}:
      match canonicos:
        case L.Ambos{nome, L.Ambos{texto, L.Ambos{valor, cauda}}}:
          %Equal.sym(Nat, Nat.mul(11n, 1n+quantidade_campos(t)), Nat.add(11n, Nat.mul(11n, quantidade_campos(t))), multiplicar_sucessor_direito(11n, quantidade_campos(t))) :
            {Nat.is_le(_, B.comprimento(bytes_campos(xs))) == True{} : Bool}
          %Equal.sym(Nat, B.comprimento(B.concatenar(B.concatenar(nb, vb), bytes_campos(t))), Nat.add(B.comprimento(B.concatenar(nb, vb)), B.comprimento(bytes_campos(t))), N.comprimento_concatenacao(B.concatenar(nb, vb), bytes_campos(t))) :
            {Nat.is_le(Nat.add(11n, Nat.mul(11n, quantidade_campos(t))), _) == True{} : Bool}
          N.somar_preserva_limites(11n, Nat.mul(11n, quantidade_campos(t)), B.comprimento(B.concatenar(nb, vb)), B.comprimento(bytes_campos(t)),
            N.campo_canonico_exige_onze_octetos(n, v, nb, vb, nome, texto, valor),
            sequencia_de_campos_canonicos_exige_onze_octetos_por_campo(t, cauda))

law concatenar_segmentos_preserva_soma_dos_limites:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  for +m: Nat
  for +n: Nat
  for ma: {Nat.is_le(m, B.comprimento(a)) == True{} : Bool}
  for nb: {Nat.is_le(n, B.comprimento(b)) == True{} : Bool}
  {Nat.is_le(Nat.add(m, n), B.comprimento(B.concatenar(a, b))) == True{} : Bool}
def concatenar_segmentos_preserva_soma_dos_limites(a, b, m, n, ma, nb):
  %Equal.sym(Nat, B.comprimento(B.concatenar(a, b)), Nat.add(B.comprimento(a), B.comprimento(b)), N.comprimento_concatenacao(a, b)) :
    {Nat.is_le(Nat.add(m, n), _) == True{} : Bool}
  N.somar_preserva_limites(m, n, B.comprimento(a), B.comprimento(b), ma, nb)
