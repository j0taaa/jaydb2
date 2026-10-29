# Capacidades de completude por subvalor e sua extracao para segmentos.
# A arvore nao presume a aceitacao de um container nem de seus bytes.
import Base
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ./Fundamentos.bend as F
import ./CodecLimitesSequencias.bend as S
import ./CodecSequencias.bend as V
import ./CodecRegistros.bend as G
import ./CodecAridades.bend as A
import ./CodecLimitesCopia.bend as K
import ./CodecTamanhos.bend as T
import ./CodecNomesLocais.bend as N

def Capacidade(+v: D.Valor) -> Type:
  @bs: List<&2, U32> -> P.Codificacao(v, bs) -> V.CompletoLocal(v, bs)

# Uma unica recursao define a arvore. O segundo componente coincide
# definicionalmente com Descendentes(v) em cada construtor de D.Valor.
def Estrutural(v: D.Valor) -> Type:
  match v:
    case D.VLista{h, t}:
      L.E<Capacidade(D.VLista{h, t}), L.E<Estrutural(h), Estrutural(t)>>
    case D.VRegistro{n, h, t}:
      L.E<Capacidade(D.VRegistro{n, h, t}), L.E<Estrutural(h), Estrutural(t)>>
    case _:
      L.E<Capacidade(v), Unit>

def Descendentes(v: D.Valor) -> Type:
  match v:
    case D.VLista{h, t}:
      L.E<Estrutural(h), Estrutural(t)>
    case D.VRegistro{n, h, t}:
      L.E<Estrutural(h), Estrutural(t)>
    case _:
      Unit

def capacidade_da_arvore(v: D.Valor, arvore: Estrutural(v)) -> Capacidade(v):
  match v arvore:
    case D.VAusente{} L.Ambos{capacidade, descendentes}:
      capacidade
    case D.VBool{b} L.Ambos{capacidade, descendentes}:
      capacidade
    case D.VInt{alto, baixo} L.Ambos{capacidade, descendentes}:
      capacidade
    case D.VTexto{s} L.Ambos{capacidade, descendentes}:
      capacidade
    case D.VListaVazia{} L.Ambos{capacidade, descendentes}:
      capacidade
    case D.VLista{h, t} L.Ambos{capacidade, descendentes}:
      capacidade
    case D.VRegistroVazio{} L.Ambos{capacidade, descendentes}:
      capacidade
    case D.VRegistro{n, h, t} L.Ambos{capacidade, descendentes}:
      capacidade

def descendentes_da_arvore(v: D.Valor, arvore: Estrutural(v)) -> Descendentes(v):
  match v arvore:
    case D.VAusente{} L.Ambos{capacidade, descendentes}:
      descendentes
    case D.VBool{b} L.Ambos{capacidade, descendentes}:
      descendentes
    case D.VInt{alto, baixo} L.Ambos{capacidade, descendentes}:
      descendentes
    case D.VTexto{s} L.Ambos{capacidade, descendentes}:
      descendentes
    case D.VListaVazia{} L.Ambos{capacidade, descendentes}:
      descendentes
    case D.VLista{h, t} L.Ambos{capacidade, descendentes}:
      descendentes
    case D.VRegistroVazio{} L.Ambos{capacidade, descendentes}:
      descendentes
    case D.VRegistro{n, h, t} L.Ambos{capacidade, descendentes}:
      descendentes

law anexar_valores_e_lista:
  for +xs: List<&2, S.ValorSegmentado>
  {A.anexar_lista(S.valores(xs), D.VListaVazia{}) == V.lista(xs) : D.Valor}
def anexar_valores_e_lista(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.ValorSegmentado{+v, bs}, +t}:
      Equal.cong(D.Valor, D.Valor, r => D.VLista{v, r},
        A.anexar_lista(S.valores(t), D.VListaVazia{}), V.lista(t), anexar_valores_e_lista(t))

law anexar_campos_e_registro:
  for +xs: List<&2, S.CampoSegmentado>
  {A.anexar_registro(S.campos(xs), D.VRegistroVazio{}) == G.registro(xs) : D.Valor}
def anexar_campos_e_registro(xs):
  match xs:
    case Nil{}:
      {==}
    case Con{S.CampoSegmentado{+n, +v, nb, vb}, +t}:
      Equal.cong(D.Valor, D.Valor, r => D.VRegistro{n, v, r},
        A.anexar_registro(S.campos(t), D.VRegistroVazio{}), G.registro(t), anexar_campos_e_registro(t))

law inducao_valores_dos_segmentos:
  for +xs: List<&2, S.ValorSegmentado>
  for descendentes: Descendentes(V.lista(xs))
  for canonicos: S.ValoresCanonicos(xs)
  V.InducaoValores(xs)
def inducao_valores_dos_segmentos(xs, descendentes, canonicos):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.ValorSegmentado{+v, +bs}, +t}:
      match descendentes:
        case L.Ambos{filho, cauda}:
          match canonicos:
            case L.Ambos{codificado, resto}:
              F.com_par(V.InducaoValores(xs), S.ValoresCanonicos(t), S.ValoresCanonicos(t),
                K.duplicar_valores_canonicos(t, resto),
                limite => recursao => L.Ambos{
                  capacidade_da_arvore(v, filho)(bs, codificado),
                  L.Ambos{
                    S.sequencia_de_valores_canonicos_exige_um_octeto_por_valor(t, limite),
                    inducao_valores_dos_segmentos(t, descendentes_da_arvore(V.lista(t), cauda), recursao)}})

law inducao_campos_dos_segmentos:
  for +xs: List<&2, S.CampoSegmentado>
  for descendentes: Descendentes(G.registro(xs))
  for canonicos: S.CamposCanonicos(xs)
  G.InducaoCampos(xs)
def inducao_campos_dos_segmentos(xs, descendentes, canonicos):
  match xs:
    case Nil{}:
      Unit{}
    case Con{S.CampoSegmentado{+n, +v, +nb, +vb}, +t}:
      match descendentes:
        case L.Ambos{filho, cauda}:
          match canonicos:
            case L.Ambos{nome_valido, L.Ambos{nome_codificado, L.Ambos{valor_codificado, resto}}}:
              +codificado = {valor_codificado : {P.codificar(v) == Some{vb} : Maybe<&2, List<&2, U32>>}}
              F.com_par(G.InducaoCampos(xs), S.CamposCanonicos(t), S.CamposCanonicos(t),
                K.duplicar_campos_canonicos(t, resto),
                limite => recursao => L.Ambos{
                  N.nome_canonico_completo(n, nb, nome_valido, nome_codificado),
                  L.Ambos{
                    capacidade_da_arvore(v, filho)(vb, codificado),
                    L.Ambos{
                      T.todo_valor_canonico_exige_pelo_menos_um_octeto(v, vb, codificado),
                      L.Ambos{
                        S.sequencia_de_campos_canonicos_exige_onze_octetos_por_campo(t, limite),
                        inducao_campos_dos_segmentos(t, descendentes_da_arvore(G.registro(t), cauda), recursao)}}}})
