# A entrega fechada REAL determina a medida; a medida nao e uma hipotese.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../contrato/Protocolo.bend as P
import ../src/Codec.bend as C
import ./CodecAridades.bend as A
import ./CodecContadores.bend as N
import ./CodecLimitesSequencias.bend as S
import ./CodecMontagem.bend as M
import ./Fundamentos.bend as F

# Projecao total: a injetividade de Pronto nao pressupoe uma forma de v.
def valor_pronto(m: C.Maquina) -> D.Valor:
  match m:
    case C.Pronto{v}:
      v
    case _:
      D.VAusente{}

law pronto_e_injetivo:
  for -a: D.Valor
  for -b: D.Valor
  for iguais: {C.Pronto{a} == C.Pronto{b} : C.Maquina}
  {a == b : D.Valor}
def pronto_e_injetivo(a, b, iguais):
  Equal.cong(C.Maquina, D.Valor, m => valor_pronto(m), C.Pronto{a}, C.Pronto{b}, iguais)

def medir_lista_aberta_fechada(vazio: Bool, +xs: List<&2, D.Valor>, +q: B.Numero64,
  -v: D.Valor, zero: {C.zero64(q) == vazio : Bool},
  entrega: {A.entregar_valores(xs, C.abrir_variavel(vazio, C.ContaLista{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}) ->
  {B.nat64(A.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}:
  match vazio:
    case False{}:
      A.lista_fechada_reconstroi_a_contagem_canonica_original(xs, q, Nil{}, v, entrega)
    case True{}:
      match xs:
        case Nil{}:
          %Equal.sym(B.Numero64, q, B.Numero64{0, 0}, N.zero64_so_reconhece_zero(q, zero)) :
            {Some{B.Numero64{0, 0}} == Some{_} : Maybe<&2, B.Numero64>}
          {==}
        case Con{+h, +t}:
          L.ex_falso({B.nat64(A.quantidade_valores(Con{h, t})) == Some{q} : Maybe<&2, B.Numero64>},
            A.invalido_nao_e_pronto(v,
              Equal.trans(C.Maquina, C.Invalido{}, A.entregar_valores(Con{h, t}, C.Pronto{D.VListaVazia{}}), C.Pronto{v},
                Equal.sym(C.Maquina, A.entregar_valores(Con{h, t}, C.Pronto{D.VListaVazia{}}), C.Invalido{},
                  A.pronto_recusa_valor_extra(h, t, D.VListaVazia{})), entrega)))

law abertura_de_lista_fechada_extrai_medida:
  for +xs: List<&2, S.ValorSegmentado>
  for +q: B.Numero64
  for -v: D.Valor
  for entrega: {A.entregar_valores(S.valores(xs), C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}
  {B.nat64(S.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>}
def abertura_de_lista_fechada_extrai_medida(xs, q, v, entrega):
  %M.quantidade_valores_projetados(xs) : {B.nat64(_) == Some{q} : Maybe<&2, B.Numero64>}
  medir_lista_aberta_fechada(C.zero64(q), S.valores(xs), q, v, {==}, entrega)

def medir_registro_aberto_fechado(vazio: Bool, +xs: List<&2, D.Campo>, +q: B.Numero64,
  -v: D.Valor, zero: {C.zero64(q) == vazio : Bool},
  entrega: {A.entregar_campos(xs, C.abrir_variavel(vazio, C.ContaRegistro{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}) ->
  {B.nat64(A.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}:
  match vazio:
    case False{}:
      A.registro_fechado_reconstroi_a_contagem_canonica_original(xs, q, "", Nil{}, v, entrega)
    case True{}:
      match xs:
        case Nil{}:
          %Equal.sym(B.Numero64, q, B.Numero64{0, 0}, N.zero64_so_reconhece_zero(q, zero)) :
            {Some{B.Numero64{0, 0}} == Some{_} : Maybe<&2, B.Numero64>}
          {==}
        case Con{+h, +t}:
          L.ex_falso({B.nat64(A.quantidade_campos(Con{h, t})) == Some{q} : Maybe<&2, B.Numero64>},
            A.invalido_nao_e_pronto(v,
              Equal.trans(C.Maquina, C.Invalido{}, A.entregar_campos(Con{h, t}, C.Pronto{D.VRegistroVazio{}}), C.Pronto{v},
                Equal.sym(C.Maquina, A.entregar_campos(Con{h, t}, C.Pronto{D.VRegistroVazio{}}), C.Invalido{},
                  A.pronto_recusa_campo_extra(h, t, D.VRegistroVazio{})), entrega)))

law abertura_de_registro_fechado_extrai_medida:
  for +xs: List<&2, S.CampoSegmentado>
  for +q: B.Numero64
  for -v: D.Valor
  for entrega: {A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}
  {B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}
def abertura_de_registro_fechado_extrai_medida(xs, q, v, entrega):
  %M.quantidade_campos_projetados(xs) : {B.nat64(_) == Some{q} : Maybe<&2, B.Numero64>}
  medir_registro_aberto_fechado(C.zero64(q), S.campos(xs), q, v, {==}, entrega)

# A medida extraida e reutilizada na abertura de A para reconstruir v.
# Os bytes dos segmentos so entram pela codificacao individual de S.
law lista_fechada_tem_medida_e_codificacao_canonica:
  for +xs: List<&2, S.ValorSegmentado>
  for +q: B.Numero64
  for -v: D.Valor
  for canonicos: S.ValoresCanonicos(xs)
  for +entrega: {A.entregar_valores(S.valores(xs), C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}
  L.E<{B.nat64(S.quantidade_valores(xs)) == Some{q} : Maybe<&2, B.Numero64>},
    P.Codificacao(v, M.prefixo(5, q, S.bytes_valores(xs)))>
def lista_fechada_tem_medida_e_codificacao_canonica(xs, q, v, canonicos, entrega):
  +medida = abertura_de_lista_fechada_extrai_medida(xs, q, v, entrega)
  medida_projetada = {(%Equal.sym(Nat, A.quantidade_valores(S.valores(xs)), S.quantidade_valores(xs), M.quantidade_valores_projetados(xs)) :
    {B.nat64(_) == Some{q} : Maybe<&2, B.Numero64>}
    medida) : {B.nat64(A.quantidade_valores(S.valores(xs))) == Some{q} : Maybe<&2, B.Numero64>}}
  valor = pronto_e_injetivo(A.anexar_lista(S.valores(xs), D.VListaVazia{}), v,
    Equal.trans(C.Maquina,
      C.Pronto{A.anexar_lista(S.valores(xs), D.VListaVazia{})},
      A.entregar_valores(S.valores(xs), C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, C.Raiz{})), C.Pronto{v},
      Equal.sym(C.Maquina,
        A.entregar_valores(S.valores(xs), C.abrir_variavel(C.zero64(q), C.ContaLista{}, q, C.Raiz{})),
        C.Pronto{A.anexar_lista(S.valores(xs), D.VListaVazia{})},
        A.abertura_de_lista_contada_preserva_aridade_e_ordem(S.valores(xs), q, C.Raiz{}, medida_projetada)), entrega))
  L.Ambos{medida,
    (%valor : P.Codificacao(_, M.prefixo(5, q, S.bytes_valores(xs)))
      M.lista_segmentada_tem_codificacao_canonica(xs, q, canonicos, medida))}

# CamposOrdenados e Type: suas conjuncoes sao reconstruidas por inducao.
law duplicar_campos_ordenados:
  for +xs: List<&2, D.Campo>
  for +anterior: String
  for ordenados: A.CamposOrdenados(xs, anterior)
  L.E<A.CamposOrdenados(xs, anterior), A.CamposOrdenados(xs, anterior)>
def duplicar_campos_ordenados(xs, anterior, ordenados):
  match xs:
    case Nil{}:
      L.Ambos{Unit{}, Unit{}}
    case Con{D.Campo{+nome, +v}, +t}:
      match ordenados:
        case L.Ambos{+valido, L.Ambos{+ordem, cauda}}:
          F.com_par(L.E<A.CamposOrdenados(xs, anterior), A.CamposOrdenados(xs, anterior)>,
            A.CamposOrdenados(t, nome), A.CamposOrdenados(t, nome), duplicar_campos_ordenados(t, nome, cauda),
            esquerda => direita => L.Ambos{
              L.Ambos{valido, L.Ambos{ordem, esquerda}},
              L.Ambos{valido, L.Ambos{ordem, direita}}})

def concluir_registro_fechado(+xs: List<&2, S.CampoSegmentado>, +q: B.Numero64, -v: D.Valor,
  canonicos: S.CamposCanonicos(xs),
  ordem_reconstrucao: A.CamposOrdenados(S.campos(xs), ""),
  ordem_codificacao: A.CamposOrdenados(S.campos(xs), ""),
  entrega: {A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina},
  +medida: {B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}) ->
  L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
    P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>:
  medida_projetada = {(%Equal.sym(Nat, A.quantidade_campos(S.campos(xs)), S.quantidade_campos(xs), M.quantidade_campos_projetados(xs)) :
    {B.nat64(_) == Some{q} : Maybe<&2, B.Numero64>}
    medida) : {B.nat64(A.quantidade_campos(S.campos(xs))) == Some{q} : Maybe<&2, B.Numero64>}}
  valor = pronto_e_injetivo(A.anexar_registro(S.campos(xs), D.VRegistroVazio{}), v,
    Equal.trans(C.Maquina,
      C.Pronto{A.anexar_registro(S.campos(xs), D.VRegistroVazio{})},
      A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})), C.Pronto{v},
      Equal.sym(C.Maquina,
        A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})),
        C.Pronto{A.anexar_registro(S.campos(xs), D.VRegistroVazio{})},
        A.abertura_de_registro_contado_preserva_aridade_e_ordem(S.campos(xs), q, C.Raiz{}, ordem_reconstrucao, medida_projetada)), entrega))
  L.Ambos{medida,
    (%valor : P.Codificacao(_, M.prefixo(6, q, S.bytes_campos(xs)))
      M.registro_segmentado_tem_codificacao_canonica(xs, q, canonicos, ordem_codificacao, medida))}

law registro_fechado_tem_medida_e_codificacao_canonica:
  for +xs: List<&2, S.CampoSegmentado>
  for +q: B.Numero64
  for -v: D.Valor
  for canonicos: S.CamposCanonicos(xs)
  for ordenados: A.CamposOrdenados(S.campos(xs), "")
  for +entrega: {A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}
  L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
    P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>
def registro_fechado_tem_medida_e_codificacao_canonica(xs, q, v, canonicos, ordenados, entrega):
  +medida = abertura_de_registro_fechado_extrai_medida(xs, q, v, entrega)
  F.com_par(L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
      P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>,
    A.CamposOrdenados(S.campos(xs), ""), A.CamposOrdenados(S.campos(xs), ""),
    duplicar_campos_ordenados(S.campos(xs), "", ordenados),
    ordem_reconstrucao => ordem_codificacao =>
      concluir_registro_fechado(xs, q, v, canonicos, ordem_reconstrucao, ordem_codificacao, entrega, medida))
