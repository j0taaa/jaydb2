# Exposicao dos nomes canonicos: tag4, medida e UTF-8 exatos.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Protocolo.bend as P
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecLimitesSequencias.bend as S
import ./CodecMontagem.bend as M
import ./CodecMontagemExposicao.bend as X

type NomeExposto<-nome: String, -bs: List<&2, U32>> is Type:
  NomeExposto{numero: B.Numero64,
    valido: {B.texto_valido(nome) == True{} : Bool},
    medida: {B.nat64(B.comprimento(B.utf8(nome))) == Some{numero} : Maybe<&2, B.Numero64>},
    bytes: {bs == M.prefixo(4, numero, B.utf8(nome)) : List<&2, U32>}}

def nome_com_cabecalho(+nome: String, +bs: List<&2, U32>,
  valido: {B.texto_valido(nome) == True{} : Bool},
  cabecalho: X.Cabecalho<4, B.comprimento(B.utf8(nome)), B.utf8(nome), bs>) -> NomeExposto<nome, bs>:
  match cabecalho:
    case X.Cabecalho{numero, medida, bytes}:
      NomeExposto{numero, valido, medida, bytes}

def expor_nome_casos(valido: Bool, +nome: String, +bs: List<&2, U32>,
  teste: {B.texto_valido(nome) == valido : Bool},
  codificado: {P.texto_casos(valido, B.utf8(nome)) == Some{bs} : Maybe<&2, List<&2, U32>>}) -> NomeExposto<nome, bs>:
  match valido:
    case False{}:
      L.ex_falso(NomeExposto<nome, bs>, F.nenhum_nao_algum(List<&2, U32>, bs, codificado))
    case True{}:
      nome_com_cabecalho(nome, bs, teste,
        X.campo_variavel_expoe_medida_e_bytes(4, B.comprimento(B.utf8(nome)), B.utf8(nome), bs, codificado))

law nome_canonico_expoe_tag_medida_e_utf8:
  for +nome: String
  for +bs: List<&2, U32>
  for codificado: {P.texto(nome) == Some{bs} : Maybe<&2, List<&2, U32>>}
  NomeExposto<nome, bs>
def nome_canonico_expoe_tag_medida_e_utf8(nome, bs, codificado):
  expor_nome_casos(B.texto_valido(nome), nome, bs, {==}, codificado)

def NomesExpostos(xs: List<&2, S.CampoSegmentado>) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{S.CampoSegmentado{n, v, nb, vb}, t}:
      L.E<NomeExposto<n, nb>, NomesExpostos(t)>

law campos_canonicos_expoem_todos_os_nomes:
  for +xs: List<&2, S.CampoSegmentado>
  for canonicos: S.CamposCanonicos(xs)
  L.E<S.CamposCanonicos(xs), NomesExpostos(xs)>
def campos_canonicos_expoem_todos_os_nomes(xs, canonicos):
  match xs:
    case Nil{}:
      L.Ambos{Unit{}, Unit{}}
    case Con{S.CampoSegmentado{+n, +v, +nb, +vb}, +t}:
      match canonicos:
        case L.Ambos{nome, L.Ambos{+texto, L.Ambos{valor, cauda}}}:
          F.com_par(L.E<S.CamposCanonicos(xs), NomesExpostos(xs)>, S.CamposCanonicos(t), NomesExpostos(t),
            campos_canonicos_expoem_todos_os_nomes(t, cauda),
            campos => nomes => L.Ambos{
              L.Ambos{nome, L.Ambos{texto, L.Ambos{valor, campos}}},
              L.Ambos{nome_canonico_expoe_tag_medida_e_utf8(n, nb, texto), nomes}})
