# Ligacao do Codec real a relacao ORIGINAL de Interface/Protocolo.
# Sem Ambiente escolhido e sem premissa Lei2/Contrato. Este modulo trata
# a parte de codificacao da Lei2; fatos observaveis do host ficam no chamador.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Interface.bend as I
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Codec.bend as V
import ./CodecAceitacao.bend as A
import ./CodecCompleto.bend as G
import ./CodecRecusas.bend as R

law aceitacao_reconstitui_codificacao_original_e_validade:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +v: D.Valor
  for +aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  L.E<P.Codificacao(v, bs), {D.valor_valido(v) == True{} : Bool}>
def aceitacao_reconstitui_codificacao_original_e_validade(bs, teto, v, aceito):
  L.Ambos{A.toda_aceitacao_publica_tem_codificacao_canonica(bs, teto, v, aceito),
    V.decodificar_so_devolve_valor_valido(bs, teto, v, aceito)}

def relacao_do_resultado(r: C.Resultado, +bs: List<&2, U32>, +corpo: B.Numero64, +teto: B.Numero64,
  medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>},
  cabe: {C.menor_igual64(corpo, teto) == True{} : Bool},
  resultado: {C.decodificar(bs, teto) == r : C.Resultado}) -> I.DecodificacaoCorreta(bs, R.opcional(r)):
  match r:
    case C.Decodificado{+v}:
      A.toda_aceitacao_publica_tem_codificacao_canonica(bs, teto, v, resultado)
    case C.Entrada{}:
      R.entrada_de_corpo_admissivel_exclui_codificacao(bs, corpo, teto, medido, cabe, resultado)
    case C.Limite{}:
      R.limite_de_corpo_admissivel_exclui_codificacao(bs, corpo, teto, medido, cabe, resultado)

# Some devolve a codificacao EXATA; None exclui toda codificacao possivel.
# A medida e o teto sao os limites reais do corpo recebido, sem nova quota.
law decodificar_satisfaz_relacao_original:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  I.DecodificacaoCorreta(bs, R.opcional(C.decodificar(bs, teto)))
def decodificar_satisfaz_relacao_original(bs, corpo, teto, medido, cabe):
  relacao_do_resultado(C.decodificar(bs, teto), bs, corpo, teto, medido, cabe, {==})

law codificacao_e_aceitacao_equivalem_no_corpo_admissivel:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  L.E<
    ({C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado} -> P.Codificacao(v, bs)),
    (P.Codificacao(v, bs) -> {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado})>
def codificacao_e_aceitacao_equivalem_no_corpo_admissivel(v, bs, corpo, teto, medido, cabe):
  L.Ambos{
    aceito => A.toda_aceitacao_publica_tem_codificacao_canonica(bs, teto, v, aceito),
    codificado => G.toda_codificacao_canonica_representavel_e_decodificada(v, bs, corpo, teto, codificado, medido, cabe)}
