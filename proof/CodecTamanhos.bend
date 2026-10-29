# Limites inferiores dos segmentos canonicos usados pelos minimos.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecConteudo.bend as G

def ResultadoComTag(m: Maybe<&2, List<&2, U32>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{bs}:
      G.NaoVazio(bs)

def ParcialComTag(p: P.Parcial) -> Type:
  match p:
    case P.Atomo{bs}:
      G.NaoVazio(bs)
    case P.Impossivel{}:
      Unit
    case P.Lista{n, bs}:
      Unit
    case P.Registro{n, bs}:
      Unit

law prefixar_tamanho_sempre_insere_tag:
  for tag: U32
  for tamanho: Maybe<&2, List<&2, U32>>
  for conteudo: List<&2, U32>
  ResultadoComTag(P.prefixar_tamanho(tag, tamanho, conteudo))
def prefixar_tamanho_sempre_insere_tag(tag, tamanho, conteudo):
  match tamanho:
    case None{}:
      Unit{}
    case Some{cabecalho}:
      Unit{}

law texto_casos_sempre_insere_tag:
  for valido: Bool
  for +bs: List<&2, U32>
  ResultadoComTag(P.texto_casos(valido, bs))
def texto_casos_sempre_insere_tag(valido, bs):
  match valido:
    case False{}:
      Unit{}
    case True{}:
      prefixar_tamanho_sempre_insere_tag(4, B.comprimento64(B.comprimento(bs)), bs)

law atomo_opcional_preserva_tag:
  for +m: Maybe<&2, List<&2, U32>>
  for tag: ResultadoComTag(m)
  ParcialComTag(P.atomo_opcional(m))
def atomo_opcional_preserva_tag(m, tag):
  match m:
    case None{}:
      Unit{}
    case Some{bs}:
      tag

law lista_casos_tem_tag:
  for h: Maybe<&2, List<&2, U32>>
  for t: P.Parcial
  ParcialComTag(P.lista_casos(h, t))
def lista_casos_tem_tag(h, t):
  match h t:
    case None{} _:
      Unit{}
    case Some{bs} P.Impossivel{}:
      Unit{}
    case Some{bs} P.Atomo{xs}:
      Unit{}
    case Some{bs} P.Lista{n, xs}:
      Unit{}
    case Some{bs} P.Registro{n, xs}:
      Unit{}

law registro_casos_tem_tag:
  for nome: Maybe<&2, List<&2, U32>>
  for v: Maybe<&2, List<&2, U32>>
  for r: P.Parcial
  ParcialComTag(P.registro_casos(nome, v, r))
def registro_casos_tem_tag(nome, v, r):
  match nome v r:
    case None{} _ _:
      Unit{}
    case Some{bs} None{} _:
      Unit{}
    case Some{bs} Some{vs} P.Impossivel{}:
      Unit{}
    case Some{bs} Some{vs} P.Atomo{xs}:
      Unit{}
    case Some{bs} Some{vs} P.Lista{n, xs}:
      Unit{}
    case Some{bs} Some{vs} P.Registro{n, xs}:
      Unit{}

def booleano_tem_tag(b: Bool) -> ParcialComTag(P.booleano(b)):
  match b:
    case False{}:
      Unit{}
    case True{}:
      Unit{}

law codificacao_parcial_nunca_perde_tag:
  for v: D.Valor
  ParcialComTag(P.codificar_parcial(v))
def codificacao_parcial_nunca_perde_tag(v):
  match v:
    case D.VAusente{}:
      Unit{}
    case D.VBool{b}:
      booleano_tem_tag(b)
    case D.VInt{a, b}:
      Unit{}
    case D.VTexto{+s}:
      atomo_opcional_preserva_tag(P.texto(s), texto_casos_sempre_insere_tag(B.texto_valido(s), B.utf8(s)))
    case D.VListaVazia{}:
      Unit{}
    case D.VLista{h, t}:
      lista_casos_tem_tag(P.finalizar(P.codificar_parcial(h)), P.codificar_parcial(t))
    case D.VRegistroVazio{}:
      Unit{}
    case D.VRegistro{n, v, r}:
      registro_casos_tem_tag(P.texto(n), P.finalizar(P.codificar_parcial(v)), P.codificar_parcial(r))

def prefixo_aceito_tem_tag(tag: U32, tamanho: Maybe<&2, List<&2, U32>>, +conteudo: List<&2, U32>, -bs: List<&2, U32>,
  aceito: {P.prefixar_tamanho(tag, tamanho, conteudo) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> G.NaoVazio(bs):
  match tamanho:
    case None{}:
      L.ex_falso(G.NaoVazio(bs), F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case Some{+cabecalho}:
      %F.algum_injetivo(List<&2, U32>, Con{tag, B.concatenar(cabecalho, conteudo)}, bs, aceito) : G.NaoVazio(_)
      Unit{}

law finalizar_parcial_com_tag_nunca_e_vazio:
  for +p: P.Parcial
  for -bs: List<&2, U32>
  for tag: ParcialComTag(p)
  for aceito: {P.finalizar(p) == Some{bs} : Maybe<&2, List<&2, U32>>}
  G.NaoVazio(bs)
def finalizar_parcial_com_tag_nunca_e_vazio(p, bs, tag, aceito):
  match p:
    case P.Impossivel{}:
      L.ex_falso(G.NaoVazio(bs), F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case P.Atomo{+bytes}:
      %F.algum_injetivo(List<&2, U32>, bytes, bs, aceito) : G.NaoVazio(_)
      tag
    case P.Lista{n, +bytes}:
      prefixo_aceito_tem_tag(5, B.comprimento64(n), bytes, bs, aceito)
    case P.Registro{n, +bytes}:
      prefixo_aceito_tem_tag(6, B.comprimento64(n), bytes, bs, aceito)

def casos_aceitos_preservam_resultado(valido: Bool, -resultado: Maybe<&2, List<&2, U32>>, -bs: List<&2, U32>,
  aceito: {P.codificar_casos(valido, resultado) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> {resultado == Some{bs} : Maybe<&2, List<&2, U32>>}:
  match valido:
    case False{}:
      L.ex_falso({resultado == Some{bs} : Maybe<&2, List<&2, U32>>}, F.nenhum_nao_algum(List<&2, U32>, bs, aceito))
    case True{}:
      aceito

law nenhuma_codificacao_canonica_e_vazia:
  for +v: D.Valor
  for -bs: List<&2, U32>
  for codificado: P.Codificacao(v, bs)
  G.NaoVazio(bs)
def nenhuma_codificacao_canonica_e_vazia(v, bs, codificado):
  finalizar_parcial_com_tag_nunca_e_vazio(P.codificar_parcial(v), bs, codificacao_parcial_nunca_perde_tag(v),
    casos_aceitos_preservam_resultado(D.valor_valido(v), P.finalizar(P.codificar_parcial(v)), bs, codificado))

law zero_natural_nao_maior:
  for n: Nat
  {Nat.is_le(0n, n) == True{} : Bool}
def zero_natural_nao_maior(n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

law bytes_nao_vazios_tem_pelo_menos_um_octeto:
  for +bs: List<&2, U32>
  for positivo: G.NaoVazio(bs)
  {Nat.is_le(1n, B.comprimento(bs)) == True{} : Bool}
def bytes_nao_vazios_tem_pelo_menos_um_octeto(bs, positivo):
  match bs:
    case Nil{}:
      L.ex_falso({False{} == True{} : Bool}, positivo)
    case Con{b, t}:
      zero_natural_nao_maior(B.comprimento(t))

law todo_valor_canonico_exige_pelo_menos_um_octeto:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for codificado: P.Codificacao(v, bs)
  {Nat.is_le(1n, B.comprimento(bs)) == True{} : Bool}
def todo_valor_canonico_exige_pelo_menos_um_octeto(v, bs, codificado):
  bytes_nao_vazios_tem_pelo_menos_um_octeto(bs, nenhuma_codificacao_canonica_e_vazia(v, bs, codificado))
