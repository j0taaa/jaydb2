# Recusas de envelope/codec ligadas a EntradaInvalida ORIGINAL.
# A recepcao do corpo e uma condicao externa especifica, nunca um fato
# escolhido ou um Ambiente criado para satisfazer as leis.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Semantica.bend as S
import ../contrato/Recursos.bend as X
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../contrato/Requisitos.bend as R
import ../src/Codec.bend as C
import ../src/Entrada.bend as E
import ./CodecRecusas.bend as Recusas
import ./EntradaMedida.bend as Medida

def SemRequisicao(-br: List<&2, U32>) -> Type:
  @r: P.Requisicao -> P.Codificacao(P.requisicao_valor(r), br) -> Empty

law ausencia_de_requisicao_no_corpo_real_justifica_entrada_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for -entrada: X.Recepcao
  for +br: List<&2, U32>
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  for nenhuma: SemRequisicao(br)
  I.EntradaInvalida(I.Atender{mundo, c, s, entrada})
def ausencia_de_requisicao_no_corpo_real_justifica_entrada_original(mundo, c, s, entrada, br, recebido, nenhuma):
  L.Direita{(br, L.Ambos{recebido, nenhuma})}

law codec_entrada_no_corpo_admissivel_real_justifica_entrada_original:
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
def codec_entrada_no_corpo_admissivel_real_justifica_entrada_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, medido, cabe, recusado):
  nenhuma = Recusas.entrada_de_corpo_admissivel_exclui_codificacao(br, corpo, teto, medido, cabe, recusado)
  ausencia_de_requisicao_no_corpo_real_justifica_entrada_original(mundo, c, s, entrada, br, recebido,
    r => codificado => nenhuma(P.requisicao_valor(r), codificado))

# Esta lei exige corpo <= teto; nao transforma excesso de tamanho em entrada.
law codec_limite_no_corpo_admissivel_real_exclui_requisicao_original:
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
def codec_limite_no_corpo_admissivel_real_exclui_requisicao_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, medido, cabe, recusado):
  nenhuma = Recusas.limite_de_corpo_admissivel_exclui_codificacao(br, corpo, teto, medido, cabe, recusado)
  ausencia_de_requisicao_no_corpo_real_justifica_entrada_original(mundo, c, s, entrada, br, recebido,
    r => codificado => nenhuma(P.requisicao_valor(r), codificado))

# Classificacao funcional EXATA e justificativa ORIGINAL, com a mesma
# medida real do corpo. Nenhuma das conclusoes e recebida como hipotese.
law limite_interno_admitido_e_entrada_justificada_original:
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
def limite_interno_admitido_e_entrada_justificada_original(mundo, c, s, entrada, br, corpo, teto,
  recebido, teto_efetivo, medido, cabe, interno):
  L.Ambos{{==}, L.Ambos{
    Medida.limite_interno_no_corpo_admitido_e_entrada(br, corpo, teto, s, medido, cabe, interno),
    codec_limite_no_corpo_admissivel_real_exclui_requisicao_original(mundo, c, s, entrada,
      br, corpo, teto, recebido, medido, cabe, interno)}}

law corpo_processado_preserva_fechamento_original:
  for -mundo: Nat
  for -c: S.Configuracao
  for -s: D.Estado
  for -entrada: X.Recepcao
  for +br: List<&2, U32>
  for recebido: {X.decidir_recepcao(c, entrada) == X.ProcessarCorpo{br} : X.Disposicao}
  L.E<I.FechamentoCorreto(I.Atender{mundo, c, s, entrada}, False{}),
    {X.corpo_invalido() == X.RecusarContinuar{S.Entrada{}} : X.Disposicao}>
def corpo_processado_preserva_fechamento_original(mundo, c, s, entrada, br, recebido):
  L.Ambos{
    (%Equal.sym(X.Disposicao, X.decidir_recepcao(c, entrada), X.ProcessarCorpo{br}, recebido) :
      I.FechamentoDisposicao(_, False{})
      {==}), {==}}
