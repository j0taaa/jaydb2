# Mutacao: aceitar um sufixo nao vazio depois de Pronto.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../src/Codec.bend as C
import ../../proof/CodecPercurso.bend as R

law falso:
  for b: U32
  for xs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +v: D.Valor
  {C.percorrer(Con{b, xs}, corpo, teto, C.Pronto{v}) == C.Decodificado{v} : C.Resultado}
def falso(b, xs, corpo, teto, v):
  R.pronto_recusa_qualquer_octeto_extra(b, xs, corpo, teto, v)
