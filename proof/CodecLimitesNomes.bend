# Limites inferiores de nomes e campos, derivados do codificador real.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecConteudo.bend as G
import ./CodecTamanhos.bend as T

law comprimento_concatenacao:
  for +a: List<&2, U32>
  for +b: List<&2, U32>
  {B.comprimento(B.concatenar(a, b)) == Nat.add(B.comprimento(a), B.comprimento(b)) : Nat}
def comprimento_concatenacao(a, b):
  match a:
    case Nil{}:
      {==}
    case Con{h, t}:
      Equal.cong(Nat, Nat, n => 1n+n,
        B.comprimento(B.concatenar(t, b)), Nat.add(B.comprimento(t), B.comprimento(b)),
        comprimento_concatenacao(t, b))

law limite_reflexivo:
  for n: Nat
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

law aumentar_limite_direito:
  for +a: Nat
  for +b: Nat
  for ab: {Nat.is_le(a, b) == True{} : Bool}
  {Nat.is_le(a, 1n+b) == True{} : Bool}
def aumentar_limite_direito(a, b, ab):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      F.absurdo_booleano({Nat.is_le(p, 0n) == True{} : Bool}, ab)
    case 1n+p 1n+q:
      aumentar_limite_direito(p, q, ab)

law somar_preserva_limites:
  for +a: Nat
  for +b: Nat
  for +c: Nat
  for +d: Nat
  for ac: {Nat.is_le(a, c) == True{} : Bool}
  for bd: {Nat.is_le(b, d) == True{} : Bool}
  {Nat.is_le(Nat.add(a, b), Nat.add(c, d)) == True{} : Bool}
def somar_preserva_limites(a, b, c, d, ac, bd):
  match a c:
    case 0n 0n:
      bd
    case 0n 1n+r:
      aumentar_limite_direito(b, Nat.add(r, d),
        somar_preserva_limites(0n, b, r, d, T.zero_natural_nao_maior(r), bd))
    case 1n+p 0n:
      F.absurdo_booleano({Nat.is_le(Nat.add(1n+p, b), d) == True{} : Bool}, ac)
    case 1n+p 1n+r:
      somar_preserva_limites(p, b, r, d, ac, bd)

def TextoNaoVazio(s: String) -> Type:
  match s:
    case SNil{}:
      Empty
    case SCon{h, t}:
      Unit

law concatenar_preserva_nao_vazio:
  for +a: List<&2, U32>
  for b: List<&2, U32>
  for positivo: G.NaoVazio(a)
  G.NaoVazio(B.concatenar(a, b))
def concatenar_preserva_nao_vazio(a, b, positivo):
  match a:
    case Nil{}:
      L.ex_falso(G.NaoVazio(b), positivo)
    case Con{h, t}:
      Unit{}

law utf8_codigo_emitido_nao_e_vazio:
  for cp: U32
  for ascii: Bool
  for dois: Bool
  for tres: Bool
  G.NaoVazio(B.utf8_codigo_emitir(cp, ascii, dois, tres))
def utf8_codigo_emitido_nao_e_vazio(cp, ascii, dois, tres):
  match ascii dois tres:
    case True{} _ _:
      Unit{}
    case False{} True{} _:
      Unit{}
    case False{} False{} True{}:
      Unit{}
    case False{} False{} False{}:
      Unit{}

law texto_nao_vazio_utf8_nao_vazio:
  for +s: String
  for positivo: TextoNaoVazio(s)
  G.NaoVazio(B.utf8(s))
def texto_nao_vazio_utf8_nao_vazio(s, positivo):
  match s:
    case SNil{}:
      L.ex_falso(G.NaoVazio(Nil{}), positivo)
    case SCon{Chr{+cp}, t}:
      concatenar_preserva_nao_vazio(B.utf8_codigo(cp), B.utf8(t),
        utf8_codigo_emitido_nao_e_vazio(cp, U32.is_lt(cp, 128), U32.is_lt(cp, 2048), U32.is_lt(cp, 65536)))

law nome_valido_nao_e_vazio:
  for +nome: String
  for valido: {D.nome_valido(nome) == True{} : Bool}
  TextoNaoVazio(nome)
def nome_valido_nao_e_vazio(nome, valido):
  match nome:
    case SNil{}:
      F.absurdo_booleano(Empty, valido)
    case SCon{h, t}:
      Unit{}

law nome_valido_utf8_exige_um_octeto:
  for +nome: String
  for valido: {D.nome_valido(nome) == True{} : Bool}
  {Nat.is_le(1n, B.comprimento(B.utf8(nome))) == True{} : Bool}
def nome_valido_utf8_exige_um_octeto(nome, valido):
  T.bytes_nao_vazios_tem_pelo_menos_um_octeto(B.utf8(nome),
    texto_nao_vazio_utf8_nao_vazio(nome, nome_valido_nao_e_vazio(nome, valido)))

# Um prefixo aceito tem uma tag e os oito bytes reais do u64.
law prefixo_numero64_tem_nove_octetos_adicionais:
  for x: Maybe<&2, B.Numero64>
  for tag: U32
  for +conteudo: List<&2, U32>
  for -bs: List<&2, U32>
  for aceito: {P.prefixar_tamanho(tag, B.numero64_bytes(x), conteudo) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {B.comprimento(bs) == Nat.add(9n, B.comprimento(conteudo)) : Nat}
def prefixo_numero64_tem_nove_octetos_adicionais(x, tag, conteudo, bs, aceito):
  match x:
    case None{}:
      L.ex_falso({B.comprimento(bs) == Nat.add(9n, B.comprimento(conteudo)) : Nat},
        F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case Some{B.Numero64{+alto, +baixo}}:
      %F.algum_injetivo(List<&2, U32>, Con{tag, B.concatenar(B.be64(alto, baixo), conteudo)}, bs, aceito) :
        {B.comprimento(_) == Nat.add(9n, B.comprimento(conteudo)) : Nat}
      {==}

law texto_casos_aceito_tem_comprimento_exato:
  for valido: Bool
  for +conteudo: List<&2, U32>
  for -bs: List<&2, U32>
  for aceito: {P.texto_casos(valido, conteudo) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {B.comprimento(bs) == Nat.add(9n, B.comprimento(conteudo)) : Nat}
def texto_casos_aceito_tem_comprimento_exato(valido, conteudo, bs, aceito):
  match valido:
    case False{}:
      L.ex_falso({B.comprimento(bs) == Nat.add(9n, B.comprimento(conteudo)) : Nat},
        F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case True{}:
      prefixo_numero64_tem_nove_octetos_adicionais(B.nat64(B.comprimento(conteudo)), 4, conteudo, bs, aceito)

law texto_canonico_tem_comprimento_exato:
  for +s: String
  for -bs: List<&2, U32>
  for aceito: {P.texto(s) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {B.comprimento(bs) == Nat.add(9n, B.comprimento(B.utf8(s))) : Nat}
def texto_canonico_tem_comprimento_exato(s, bs, aceito):
  texto_casos_aceito_tem_comprimento_exato(B.texto_valido(s), B.utf8(s), bs, aceito)

law nome_canonico_exige_dez_octetos:
  for +nome: String
  for +bs: List<&2, U32>
  for valido: {D.nome_valido(nome) == True{} : Bool}
  for aceito: {P.texto(nome) == Some{bs} : Maybe<&2, List<&2, U32>>}
  {Nat.is_le(10n, B.comprimento(bs)) == True{} : Bool}
def nome_canonico_exige_dez_octetos(nome, bs, valido, aceito):
  %Equal.sym(Nat, B.comprimento(bs), Nat.add(9n, B.comprimento(B.utf8(nome))),
      texto_canonico_tem_comprimento_exato(nome, bs, aceito)) :
    {Nat.is_le(10n, _) == True{} : Bool}
  somar_preserva_limites(9n, 1n, 9n, B.comprimento(B.utf8(nome)), {==}, nome_valido_utf8_exige_um_octeto(nome, valido))

law campo_canonico_exige_onze_octetos:
  for +nome: String
  for +v: D.Valor
  for +nb: List<&2, U32>
  for +vb: List<&2, U32>
  for valido: {D.nome_valido(nome) == True{} : Bool}
  for aceito_nome: {P.texto(nome) == Some{nb} : Maybe<&2, List<&2, U32>>}
  for codificado: P.Codificacao(v, vb)
  {Nat.is_le(11n, B.comprimento(B.concatenar(nb, vb))) == True{} : Bool}
def campo_canonico_exige_onze_octetos(nome, v, nb, vb, valido, aceito_nome, codificado):
  %Equal.sym(Nat, B.comprimento(B.concatenar(nb, vb)), Nat.add(B.comprimento(nb), B.comprimento(vb)),
      comprimento_concatenacao(nb, vb)) :
    {Nat.is_le(11n, _) == True{} : Bool}
  somar_preserva_limites(10n, 1n, B.comprimento(nb), B.comprimento(vb),
    nome_canonico_exige_dez_octetos(nome, nb, valido, aceito_nome),
    T.todo_valor_canonico_exige_pelo_menos_um_octeto(v, vb, codificado))
