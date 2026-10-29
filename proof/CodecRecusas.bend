# O sentido de RECUSA da relacao original de Interface. Para corpos
# admissiveis, Entrada/Limite excluem qualquer codificacao canonica,
# pela completude geral de todos os valores, sem limitar estruturas.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Interface.bend as I
import ../src/Codec.bend as C
import ./CodecCompleto.bend as G
import ./CodecPercurso.bend as R

def opcional(r: C.Resultado) -> Maybe<&2, D.Valor>:
  match r:
    case C.Decodificado{v}:
      Some{v}
    case C.Entrada{}:
      None{}
    case C.Limite{}:
      None{}

law entrada_de_corpo_admissivel_exclui_codificacao:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  for recusado: {C.decodificar(bs, teto) == C.Entrada{} : C.Resultado}
  I.DecodificacaoCorreta(bs, None{})
def entrada_de_corpo_admissivel_exclui_codificacao(bs, corpo, teto, medido, cabe, recusado):
  v => codificado =>
    R.entrada_nao_decodificada(v, Equal.trans(C.Resultado,
      C.Entrada{}, C.decodificar(bs, teto), C.Decodificado{v},
      Equal.sym(C.Resultado, C.decodificar(bs, teto), C.Entrada{}, recusado),
      G.toda_codificacao_canonica_representavel_e_decodificada(v, bs, corpo, teto, codificado, medido, cabe)))

law limite_de_corpo_admissivel_exclui_codificacao:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  for recusado: {C.decodificar(bs, teto) == C.Limite{} : C.Resultado}
  I.DecodificacaoCorreta(bs, None{})
def limite_de_corpo_admissivel_exclui_codificacao(bs, corpo, teto, medido, cabe, recusado):
  v => codificado =>
    R.limite_nao_decodificado(v, Equal.trans(C.Resultado,
      C.Limite{}, C.decodificar(bs, teto), C.Decodificado{v},
      Equal.sym(C.Resultado, C.decodificar(bs, teto), C.Limite{}, recusado),
      G.toda_codificacao_canonica_representavel_e_decodificada(v, bs, corpo, teto, codificado, medido, cabe)))
