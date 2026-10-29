# Reaplicacoes universais das quantidades reais e relacoes originais.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../contrato/Recursos.bend as X
import ../../contrato/Interface.bend as I
import ../../contrato/Logica.bend as L
import ../../contrato/Requisitos.bend as R
import ../../src/Codec.bend as C
import ../../src/Entrada.bend as E
import ../../proof/EntradaRecusas.bend as G

law reaplicar_ausencia_de_requisicao_no_corpo_real_justifica_entrada_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for -entrada: X.Recepcao
  for +br: List<&2, U32>
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for nenhuma: G.SemRequisicao(br)
  I.EntradaInvalida(I.Atender{mundo, c, s, entrada})
def reaplicar_ausencia_de_requisicao_no_corpo_real_justifica_entrada_original(mundo, c, s, entrada, br, recebido, nenhuma):
  G.ausencia_de_requisicao_no_corpo_real_justifica_entrada_original(mundo, c, s, entrada, br, recebido, nenhuma)

law reaplicar_codec_entrada_no_corpo_admissivel_real_justifica_entrada_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for +entrada: X.Recepcao
  for +br: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  for recusado: {C.decodificar(br, teto) == C.Entrada{} : C.Resultado}
  I.EntradaInvalida(I.Atender{mundo, c, s, entrada})
def reaplicar_codec_entrada_no_corpo_admissivel_real_justifica_entrada_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, medido, cabe, recusado):
  G.codec_entrada_no_corpo_admissivel_real_justifica_entrada_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, medido, cabe, recusado)

law reaplicar_codec_limite_no_corpo_admissivel_real_exclui_requisicao_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for +entrada: X.Recepcao
  for +br: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  for recusado: {C.decodificar(br, teto) == C.Limite{} : C.Resultado}
  I.EntradaInvalida(I.Atender{mundo, c, s, entrada})
def reaplicar_codec_limite_no_corpo_admissivel_real_exclui_requisicao_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, medido, cabe, recusado):
  G.codec_limite_no_corpo_admissivel_real_exclui_requisicao_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, medido, cabe, recusado)

law reaplicar_limite_interno_admitido_e_entrada_justificada_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for +s: D.Estado
  for +entrada: X.Recepcao
  for +br: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for teto_efetivo: {B.nat64(R.limite_mensagem(S.limites(c))) == Some{teto} : Maybe<&2, B.Numero64>}
  for +medido: {B.nat64(B.comprimento(br)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  for +interno: {C.decodificar(br, teto) == C.Limite{} : C.Resultado}
  L.E<{E.mensagem(C.Limite{}, s) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao},
    L.E<{E.ler_mensagem(Some{teto}, br, s) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao},
      I.EntradaInvalida(I.Atender{mundo, c, s, entrada})>>
def reaplicar_limite_interno_admitido_e_entrada_justificada_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, teto_efetivo, medido, cabe, interno):
  G.limite_interno_admitido_e_entrada_justificada_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, teto_efetivo, medido, cabe, interno)

law reaplicar_corpo_processado_preserva_fechamento_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for -entrada: X.Recepcao
  for +br: List<&2, U32>
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  L.E<I.FechamentoCorreto(I.Atender{mundo, c, s, entrada}, False{}),
    {X.corpo_invalido() == X.RecusarContinuar{S.Entrada{}} : X.Disposicao}>
def reaplicar_corpo_processado_preserva_fechamento_original(mundo, c, s, entrada, br, recebido):
  G.corpo_processado_preserva_fechamento_original(mundo, c, s, entrada, br, recebido)
