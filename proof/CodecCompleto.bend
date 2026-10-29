# Completude do codec por inducao ESTRUTURAL em D.Valor.
# A arvore guarda capacidades dos subvalores: os segmentos arbitrarios
# expostos pelo encoder sao alinhados a ela por igualdade proposicional.
# Nenhuma premissa afirma aceitacao ou completude do container inteiro.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecSequencias.bend as V
import ./CodecRegistros.bend as G
import ./CodecLocais.bend as I
import ./CodecTextos.bend as T
import ./CodecAridades.bend as A
import ./CodecMontagem.bend as M
import ./CodecMontagemNomes.bend as N
import ./CodecMontagemExposicao.bend as E
import ./CodecMontagemExposicaoRegistro.bend as R
import ./CodecLimitesSequencias.bend as S
import ./CodecLimitesCopia.bend as Q
import ./CodecCompletoEstrutura.bend as Z
import ./CodecPublico.bend as U

law lista_segmentada_completa:
  for +xs: List<&2, S.ValorSegmentado>
  for +alto: U32
  for +baixo: U32
  for filhos: V.InducaoValores(xs)
  for canonicos: S.ValoresCanonicos(xs)
  for contado: {B.nat64(S.quantidade_valores(xs)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  V.CompletoLocal(V.lista(xs), V.bytes_lista(alto, baixo, xs))
def lista_segmentada_completa(xs, alto, baixo, filhos, canonicos, contado):
  corpo => teto => pai => sufixo => r => minimo => reserva => medido => cabe =>
    V.construtor_lista_compoe_completude_local(xs, alto, baixo, corpo, teto, pai, sufixo, r,
      filhos, canonicos, contado, minimo, reserva, medido, cabe)

law registro_segmentado_completo:
  for +xs: List<&2, S.CampoSegmentado>
  for +alto: U32
  for +baixo: U32
  for filhos: G.InducaoCampos(xs)
  for ordenados: A.CamposOrdenados(S.campos(xs), "")
  for canonicos: S.CamposCanonicos(xs)
  for contado: {B.nat64(S.quantidade_campos(xs)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  V.CompletoLocal(G.registro(xs), G.bytes_registro(alto, baixo, xs))
def registro_segmentado_completo(xs, alto, baixo, filhos, ordenados, canonicos, contado):
  corpo => teto => pai => sufixo => r => minimo => reserva => medido => cabe =>
    G.construtor_registro_compoe_completude_local(xs, alto, baixo, corpo, teto, pai, sufixo, r,
      filhos, ordenados, canonicos, contado, minimo, reserva, medido, cabe)

# O primeiro transporte consome apenas a igualdade do valor original;
# nao se faz chamada recursiva sobre segmentos produzidos pelo encoder.
def aplicar_lista_exposta(+v: D.Valor, +bs: List<&2, U32>,
  descendentes: Z.Descendentes(v), exposta: E.ListaExposta<v, bs>) -> V.CompletoLocal(v, bs):
  match exposta:
    case E.ListaExposta{+xs, B.Numero64{+alto, +baixo}, valor, canonicos, contado, bytes}:
      +igual = Equal.trans(D.Valor, v, A.anexar_lista(S.valores(xs), D.VListaVazia{}), V.lista(xs),
        valor, Z.anexar_valores_e_lista(xs))
      arvore = {(%igual : Z.Descendentes(_)
        descendentes) : Z.Descendentes(V.lista(xs))}
      %Equal.sym(D.Valor, v, V.lista(xs), igual) : V.CompletoLocal(_, bs)
      %Equal.sym(List<&2, U32>, bs, V.bytes_lista(alto, baixo, xs), bytes) : V.CompletoLocal(V.lista(xs), _)
      F.com_par(V.CompletoLocal(V.lista(xs), V.bytes_lista(alto, baixo, xs)),
        S.ValoresCanonicos(xs), S.ValoresCanonicos(xs), Q.duplicar_valores_canonicos(xs, canonicos),
        para_filhos => para_abertura => lista_segmentada_completa(xs, alto, baixo,
          Z.inducao_valores_dos_segmentos(xs, arvore, para_filhos), para_abertura, contado))

def aplicar_registro_exposto(+v: D.Valor, +bs: List<&2, U32>,
  descendentes: Z.Descendentes(v), exposto: R.RegistroExposto<v, bs>) -> V.CompletoLocal(v, bs):
  match exposto:
    case R.RegistroExposto{+xs, B.Numero64{+alto, +baixo}, valor, canonicos, ordenados, nomes, contado, bytes}:
      +igual = Equal.trans(D.Valor, v, A.anexar_registro(S.campos(xs), D.VRegistroVazio{}), G.registro(xs),
        valor, Z.anexar_campos_e_registro(xs))
      arvore = {(%igual : Z.Descendentes(_)
        descendentes) : Z.Descendentes(G.registro(xs))}
      %Equal.sym(D.Valor, v, G.registro(xs), igual) : V.CompletoLocal(_, bs)
      %Equal.sym(List<&2, U32>, bs, G.bytes_registro(alto, baixo, xs), bytes) : V.CompletoLocal(G.registro(xs), _)
      F.com_par(V.CompletoLocal(G.registro(xs), G.bytes_registro(alto, baixo, xs)),
        S.CamposCanonicos(xs), S.CamposCanonicos(xs), Q.duplicar_campos_canonicos(xs, canonicos),
        para_filhos => para_abertura => registro_segmentado_completo(xs, alto, baixo,
          Z.inducao_campos_dos_segmentos(xs, arvore, para_filhos), ordenados, para_abertura, contado))

law lista_codificada_com_descendentes_e_completa:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for descendentes: Z.Descendentes(v)
  for forma: {D.eh_lista(v) == True{} : Bool}
  for codificado: P.Codificacao(v, bs)
  V.CompletoLocal(v, bs)
def lista_codificada_com_descendentes_e_completa(v, bs, descendentes, forma, codificado):
  aplicar_lista_exposta(v, bs, descendentes,
    E.lista_codificada_expoe_segmentos_contagem_e_cabecalho(v, bs, forma, codificado))

law registro_codificado_com_descendentes_e_completo:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for descendentes: Z.Descendentes(v)
  for forma: {D.eh_registro(v) == True{} : Bool}
  for codificado: P.Codificacao(v, bs)
  V.CompletoLocal(v, bs)
def registro_codificado_com_descendentes_e_completo(v, bs, descendentes, forma, codificado):
  aplicar_registro_exposto(v, bs, descendentes,
    R.registro_codificado_expoe_segmentos_contagem_e_cabecalho(v, bs, forma, codificado))

law ausencia_codificada_e_completa:
  for +bs: List<&2, U32>
  for codificado: P.Codificacao(D.VAusente{}, bs)
  V.CompletoLocal(D.VAusente{}, bs)
def ausencia_codificada_e_completa(bs, codificado):
  %F.algum_injetivo(List<&2, U32>, [0], bs, codificado) : V.CompletoLocal(D.VAusente{}, _)
  I.ausencia_completa_em_qualquer_contexto()

law booleano_codificado_e_completo:
  for +b: Bool
  for +bs: List<&2, U32>
  for codificado: P.Codificacao(D.VBool{b}, bs)
  V.CompletoLocal(D.VBool{b}, bs)
def booleano_codificado_e_completo(b, bs, codificado):
  match b:
    case False{}:
      %F.algum_injetivo(List<&2, U32>, [1], bs, codificado) : V.CompletoLocal(D.VBool{False{}}, _)
      I.booleano_completo_em_qualquer_contexto(False{})
    case True{}:
      %F.algum_injetivo(List<&2, U32>, [2], bs, codificado) : V.CompletoLocal(D.VBool{True{}}, _)
      I.booleano_completo_em_qualquer_contexto(True{})

law inteiro_codificado_e_completo:
  for +alto: U32
  for +baixo: U32
  for +bs: List<&2, U32>
  for codificado: P.Codificacao(D.VInt{alto, baixo}, bs)
  V.CompletoLocal(D.VInt{alto, baixo}, bs)
def inteiro_codificado_e_completo(alto, baixo, bs, codificado):
  %F.algum_injetivo(List<&2, U32>, Con{3, B.be64(alto, baixo)}, bs, codificado) : V.CompletoLocal(D.VInt{alto, baixo}, _)
  I.inteiro_completo_em_qualquer_contexto(alto, baixo)

# O caso texto expoe somente o resultado do encoder original, e nao
# exige como hipotese uma medida ou validade textual adicional.
def aplicar_texto_exposto(+s: String, +bs: List<&2, U32>, exposto: N.NomeExposto<s, bs>) -> V.CompletoLocal(D.VTexto{s}, bs):
  match exposto:
    case N.NomeExposto{B.Numero64{+alto, +baixo}, valido, medida, bytes}:
      %Equal.sym(List<&2, U32>, bs, T.bytes_texto(alto, baixo, s), bytes) : V.CompletoLocal(D.VTexto{s}, _)
      I.texto_completo_em_qualquer_contexto(s, alto, baixo, valido, medida)

def finalizar_atomo_opcional_expoe_resultado(resultado: Maybe<&2, List<&2, U32>>, +bs: List<&2, U32>,
  codificado: {P.finalizar(P.atomo_opcional(resultado)) == Some{bs} : Maybe<&2, List<&2, U32>>}) ->
  {resultado == Some{bs} : Maybe<&2, List<&2, U32>>}:
  match resultado:
    case None{}:
      L.ex_falso({None{} == Some{bs} : Maybe<&2, List<&2, U32>>}, F.nenhum_nao_algum(List<&2, U32>, bs, codificado))
    case Some{payload}:
      codificado

law texto_codificado_expoe_bytes_de_texto:
  for +s: String
  for +bs: List<&2, U32>
  for codificado: P.Codificacao(D.VTexto{s}, bs)
  {P.texto(s) == Some{bs} : Maybe<&2, List<&2, U32>>}
def texto_codificado_expoe_bytes_de_texto(s, bs, codificado):
  F.com_par({P.texto(s) == Some{bs} : Maybe<&2, List<&2, U32>>},
    {D.valor_valido(D.VTexto{s}) == True{} : Bool},
    {P.finalizar(P.codificar_parcial(D.VTexto{s})) == Some{bs} : Maybe<&2, List<&2, U32>>},
    M.filho_canonico_expoe_validade_e_bytes(D.VTexto{s}, bs, codificado),
    valido => bytes => finalizar_atomo_opcional_expoe_resultado(P.texto(s), bs, bytes))

law texto_codificado_e_completo:
  for +s: String
  for +bs: List<&2, U32>
  for codificado: P.Codificacao(D.VTexto{s}, bs)
  V.CompletoLocal(D.VTexto{s}, bs)
def texto_codificado_e_completo(s, bs, codificado):
  aplicar_texto_exposto(s, bs,
    N.nome_canonico_expoe_tag_medida_e_utf8(s, bs, texto_codificado_expoe_bytes_de_texto(s, bs, codificado)))

# Cada chamada recursiva recebe h ou t DIRETAMENTE do match de v.
# A segunda construcao conserva as capacidades para os ancestrais; ela
# evita copiar callbacks, que sao afins em Bend.
law todo_valor_tem_arvore_de_completude:
  for +v: D.Valor
  Z.Estrutural(v)
def todo_valor_tem_arvore_de_completude(v):
  match v:
    case D.VAusente{}:
      L.Ambos{bs => codificado => ausencia_codificada_e_completa(bs, codificado), Unit{}}
    case D.VBool{+b}:
      L.Ambos{bs => codificado => booleano_codificado_e_completo(b, bs, codificado), Unit{}}
    case D.VInt{+alto, +baixo}:
      L.Ambos{bs => codificado => inteiro_codificado_e_completo(alto, baixo, bs, codificado), Unit{}}
    case D.VTexto{+s}:
      L.Ambos{bs => codificado => texto_codificado_e_completo(s, bs, codificado), Unit{}}
    case D.VListaVazia{}:
      L.Ambos{bs => codificado => lista_codificada_com_descendentes_e_completa(D.VListaVazia{}, bs, Unit{}, {==}, codificado), Unit{}}
    case D.VLista{+h, +t}:
      L.Ambos{
        bs => codificado => lista_codificada_com_descendentes_e_completa(D.VLista{h, t}, bs,
          L.Ambos{todo_valor_tem_arvore_de_completude(h), todo_valor_tem_arvore_de_completude(t)}, {==}, codificado),
        L.Ambos{todo_valor_tem_arvore_de_completude(h), todo_valor_tem_arvore_de_completude(t)}}
    case D.VRegistroVazio{}:
      L.Ambos{bs => codificado => registro_codificado_com_descendentes_e_completo(D.VRegistroVazio{}, bs, Unit{}, {==}, codificado), Unit{}}
    case D.VRegistro{+nome, +h, +t}:
      L.Ambos{
        bs => codificado => registro_codificado_com_descendentes_e_completo(D.VRegistro{nome, h, t}, bs,
          L.Ambos{todo_valor_tem_arvore_de_completude(h), todo_valor_tem_arvore_de_completude(t)}, {==}, codificado),
        L.Ambos{todo_valor_tem_arvore_de_completude(h), todo_valor_tem_arvore_de_completude(t)}}

law codificacao_canonica_implica_completude_local:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for codificado: P.Codificacao(v, bs)
  V.CompletoLocal(v, bs)
def codificacao_canonica_implica_completude_local(v, bs, codificado):
  Z.capacidade_da_arvore(v, todo_valor_tem_arvore_de_completude(v))(bs, codificado)

# API publica: as unicas premissas alem da codificacao canonica sao a
# medida exata do corpo e o limite u64 efetivamente recebido pelo decoder.
law toda_codificacao_canonica_representavel_e_decodificada:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for codificado: P.Codificacao(v, bs)
  for +medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
def toda_codificacao_canonica_representavel_e_decodificada(v, bs, corpo, teto, codificado, medido, cabe):
  +canonico = {codificado : {P.codificar(v) == Some{bs} : Maybe<&2, List<&2, U32>>}}
  U.completude_local_canonica_implica_aceitacao_publica(v, bs, corpo, teto,
    codificacao_canonica_implica_completude_local(v, bs, canonico), canonico, medido, cabe)
