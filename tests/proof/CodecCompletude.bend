# A fronteira inclusiva e verificada para QUALQUER valor canonico,
# inclusive listas/registros arbitrariamente aninhados, sem exemplos fixos.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../src/Codec.bend as C
import ../../proof/CodecCompleto.bend as G
import ../../proof/CodecMinimos.bend as M

law qualquer_codificacao_representavel_e_aceita_no_limite_exato:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for codificado: P.Codificacao(v, bs)
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  {C.decodificar(bs, corpo) == C.Decodificado{v} : C.Resultado}
def qualquer_codificacao_representavel_e_aceita_no_limite_exato(v, bs, corpo, codificado, medido):
  G.toda_codificacao_canonica_representavel_e_decodificada(v, bs, corpo, corpo, codificado, medido, M.menor_igual64_reflexivo(corpo))
