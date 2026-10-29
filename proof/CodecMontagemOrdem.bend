# A ordem estrita tambem e extraida da entrega REAL: um nome recusado
# torna a maquina invalida, e nenhum sufixo de campos a recupera.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecAridades.bend as A
import ./CodecLimitesSequencias.bend as S
import ./CodecMontagem.bend as M
import ./CodecMontagemFechada.bend as E

def campos_apos_pronto_tem_ordem(xs: List<&2, D.Campo>, +pronto: D.Valor, -v: D.Valor, +anterior: String,
  entrega: {A.entregar_campos(xs, C.Pronto{pronto}) == C.Pronto{v} : C.Maquina}) -> A.CamposOrdenados(xs, anterior):
  match xs:
    case Nil{}:
      Unit{}
    case Con{+h, +t}:
      L.ex_falso(A.CamposOrdenados(Con{h, t}, anterior), A.invalido_nao_e_pronto(v,
        Equal.trans(C.Maquina, C.Invalido{}, A.entregar_campos(Con{h, t}, C.Pronto{pronto}), C.Pronto{v},
          Equal.sym(C.Maquina, A.entregar_campos(Con{h, t}, C.Pronto{pronto}), C.Invalido{},
            A.pronto_recusa_campo_extra(h, t, pronto)), entrega)))

def conferir_nome_e_ordem_fechados(ok: Bool, ultimo: Bool, +q: B.Numero64,
  +anterior: String, +nome: String, +valor: D.Valor, +t: List<&2, D.Campo>,
  +invertidos: List<&2, D.Campo>, -v: D.Valor,
  +teste: {D.nome_valido(nome) && String.is_lt(anterior, nome) == ok : Bool},
  entrega: {A.entregar_campos(t, A.proximo_valor(C.nome_conferido(ok, ultimo, C.diminuir64(q), nome, invertidos, C.Raiz{}), valor)) == C.Pronto{v} : C.Maquina},
  continuar: {A.entregar_campos(t, C.TagNome{C.Nome{C.um64(C.diminuir64(q)), C.diminuir64(C.diminuir64(q)), nome, Con{D.Campo{nome, valor}, invertidos}, C.Raiz{}}}) == C.Pronto{v} : C.Maquina} ->
    A.CamposOrdenados(t, nome)) -> A.CamposOrdenados(Con{D.Campo{nome, valor}, t}, anterior):
  match ok ultimo:
    case False{} _:
      L.ex_falso(A.CamposOrdenados(Con{D.Campo{nome, valor}, t}, anterior), A.invalido_nao_e_pronto(v,
        Equal.trans(C.Maquina, C.Invalido{}, A.entregar_campos(t, C.Invalido{}), C.Pronto{v},
          Equal.sym(C.Maquina, A.entregar_campos(t, C.Invalido{}), C.Invalido{}, A.campos_nao_recuperam_maquina_invalida(t)), entrega)))
    case True{} False{}:
      L.Ambos{F.e_booleano_esquerda(D.nome_valido(nome), String.is_lt(anterior, nome), teste),
        L.Ambos{F.e_booleano_direita(D.nome_valido(nome), String.is_lt(anterior, nome), teste), continuar(entrega)}}
    case True{} True{}:
      L.Ambos{F.e_booleano_esquerda(D.nome_valido(nome), String.is_lt(anterior, nome), teste),
        L.Ambos{F.e_booleano_direita(D.nome_valido(nome), String.is_lt(anterior, nome), teste),
          campos_apos_pronto_tem_ordem(t, C.montar_registro(Con{D.Campo{nome, valor}, invertidos}, D.VRegistroVazio{}), v, nome, entrega)}}

law registro_fechado_conferiu_todos_os_nomes_e_ordem:
  for +xs: List<&2, D.Campo>
  for +q: B.Numero64
  for +anterior: String
  for +invertidos: List<&2, D.Campo>
  for -v: D.Valor
  for entrega: {A.entregar_campos(xs, C.TagNome{C.Nome{C.um64(q), C.diminuir64(q), anterior, invertidos, C.Raiz{}}}) == C.Pronto{v} : C.Maquina}
  A.CamposOrdenados(xs, anterior)
def registro_fechado_conferiu_todos_os_nomes_e_ordem(xs, q, anterior, invertidos, v, entrega):
  match xs:
    case Nil{}:
      Unit{}
    case Con{D.Campo{+nome, +valor}, +t}:
      conferir_nome_e_ordem_fechados(D.nome_valido(nome) && String.is_lt(anterior, nome), C.um64(q), q, anterior, nome, valor, t, invertidos, v,
        {==}, entrega, e => registro_fechado_conferiu_todos_os_nomes_e_ordem(t, C.diminuir64(q), nome, Con{D.Campo{nome, valor}, invertidos}, v, e))

def ordem_abertura_fechada(vazio: Bool, +xs: List<&2, D.Campo>, +q: B.Numero64, -v: D.Valor,
  entrega: {A.entregar_campos(xs, C.abrir_variavel(vazio, C.ContaRegistro{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}) -> A.CamposOrdenados(xs, ""):
  match vazio:
    case True{}:
      campos_apos_pronto_tem_ordem(xs, D.VRegistroVazio{}, v, "", entrega)
    case False{}:
      registro_fechado_conferiu_todos_os_nomes_e_ordem(xs, q, "", Nil{}, v, entrega)

law abertura_de_registro_fechado_extrai_ordem:
  for +xs: List<&2, S.CampoSegmentado>
  for +q: B.Numero64
  for -v: D.Valor
  for entrega: {A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}
  A.CamposOrdenados(S.campos(xs), "")
def abertura_de_registro_fechado_extrai_ordem(xs, q, v, entrega):
  ordem_abertura_fechada(C.zero64(q), S.campos(xs), q, v, entrega)

def reunir_fechamento_com_ordem(+xs: List<&2, S.CampoSegmentado>, +q: B.Numero64, -v: D.Valor,
  ordenados: A.CamposOrdenados(S.campos(xs), ""),
  fechado: L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>}, P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>) ->
  L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
    L.E<A.CamposOrdenados(S.campos(xs), ""), P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>>:
  match fechado:
    case L.Ambos{medida, bytes}:
      L.Ambos{medida, L.Ambos{ordenados, bytes}}

# Apenas os segmentos individuais e a entrega fechada sao premissas;
# contagem, ordem estrita e codificacao do registro sao conclusoes.
law registro_fechado_extrai_medida_ordem_e_codificacao_canonica:
  for +xs: List<&2, S.CampoSegmentado>
  for +q: B.Numero64
  for -v: D.Valor
  for canonicos: S.CamposCanonicos(xs)
  for +entrega: {A.entregar_campos(S.campos(xs), C.abrir_variavel(C.zero64(q), C.ContaRegistro{}, q, C.Raiz{})) == C.Pronto{v} : C.Maquina}
  L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
    L.E<A.CamposOrdenados(S.campos(xs), ""), P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>>
def registro_fechado_extrai_medida_ordem_e_codificacao_canonica(xs, q, v, canonicos, entrega):
  F.com_par(
    L.E<{B.nat64(S.quantidade_campos(xs)) == Some{q} : Maybe<&2, B.Numero64>},
      L.E<A.CamposOrdenados(S.campos(xs), ""), P.Codificacao(v, M.prefixo(6, q, S.bytes_campos(xs)))>>,
    A.CamposOrdenados(S.campos(xs), ""), A.CamposOrdenados(S.campos(xs), ""),
    E.duplicar_campos_ordenados(S.campos(xs), "", abertura_de_registro_fechado_extrai_ordem(xs, q, v, entrega)),
    ordem => ordem2 => reunir_fechamento_com_ordem(xs, q, v, ordem,
      E.registro_fechado_tem_medida_e_codificacao_canonica(xs, q, v, canonicos, ordem2, entrega)))
