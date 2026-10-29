# Reaplicacoes universais das relacoes originais, sem Ambiente instanciado.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../contrato/Requisitos.bend as R
import ../../contrato/Recursos.bend as X
import ../../contrato/Interface.bend as I
import ../../contrato/Logica.bend as L
import ../../src/Entrada.bend as E
import ../../src/Estado.bend as Estado
import ../../src/Requisicao.bend as Q
import ../../src/Transporte.bend as T
import ../../src/Codec.bend as C
import ../../proof/EntradaRelacoes.bend as G

law reaplicar_decodificar_reconstroi_etapas_reais:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  G.ProntaRelacionada(E.decodificar(bs, e, l), bs, e, l)
def reaplicar_decodificar_reconstroi_etapas_reais(bs, e, l):
  G.decodificar_reconstroi_etapas_reais(bs, e, l)

law reaplicar_pronta_reconstroi_blocos_tetos_estado_e_requisicao:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for -s: D.Estado
  for -r: P.Requisicao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  G.InversaoPronta(bs, e, l, s, r)
def reaplicar_pronta_reconstroi_blocos_tetos_estado_e_requisicao(bs, e, l, s, r, pronta):
  G.pronta_reconstroi_blocos_tetos_estado_e_requisicao(bs, e, l, s, r, pronta)

law reaplicar_pronta_fornece_corpo_e_ligacao_a_interface_original:
  for +bs: List<&2, U32>
  for +e: D.Esquema
  for +l: S.Limites
  for +s: D.Estado
  for +r: P.Requisicao
  for -mundo: Nat
  for -c: S.Configuracao
  for +entrada: X.Recepcao
  for pronta: {E.decodificar(bs, e, l) == E.Pronta{s, r} : E.PreAutenticacao}
  G.CorpoParaInterface(bs, r, mundo, c, s, entrada)
def reaplicar_pronta_fornece_corpo_e_ligacao_a_interface_original(bs, e, l, s, r, mundo, c, entrada, pronta):
  G.pronta_fornece_corpo_e_ligacao_a_interface_original(bs, e, l, s, r, mundo, c, entrada, pronta)

law reaplicar_codec_aceito_com_envelope_invalido_exclui_requisicao_canonica:
  for +br: List<&2, U32>
  for +corpo: B.Numero64
  for +tr: B.Numero64
  for +v: D.Valor
  for +medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, tr) == True{} : Bool}
  for +aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado}
  for +recusado: {Q.extrair(v) == None{} : Maybe<&2, P.Requisicao>}
  G.SemRequisicaoCodificada(br)
def reaplicar_codec_aceito_com_envelope_invalido_exclui_requisicao_canonica(br, corpo, tr, v, medido, cabe, aceito, recusado):
  G.codec_aceito_com_envelope_invalido_exclui_requisicao_canonica(br, corpo, tr, v, medido, cabe, aceito, recusado)

law reaplicar_envelope_invalido_do_corpo_real_implica_entrada_invalida_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for -entrada: X.Recepcao
  for +br: List<&2, U32>
  for +corpo: B.Numero64
  for +tr: B.Numero64
  for +v: D.Valor
  for recepcao: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for +teto: {B.nat64(R.limite_mensagem(S.limites(c))) == Some{tr} : Maybe<&2, B.Numero64>}
  for +medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, tr) == True{} : Bool}
  for +aceito: {C.decodificar(br, tr) == C.Decodificado{v} : C.Resultado}
  for +recusado: {Q.extrair(v) == None{} : Maybe<&2, P.Requisicao>}
  I.EntradaInvalida(I.Atender{mundo, c, s, entrada})
def reaplicar_envelope_invalido_do_corpo_real_implica_entrada_invalida_original(mundo, c, s, entrada,
  br, corpo, tr, v, recepcao, teto, medido, cabe, aceito, recusado):
  G.envelope_invalido_do_corpo_real_implica_entrada_invalida_original(mundo, c, s, entrada,
  br, corpo, tr, v, recepcao, teto, medido, cabe, aceito, recusado)
