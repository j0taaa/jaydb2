# Todo corpo representavel e arbitrario: inclui entradas malformadas,
# Unicode invalido, contagens falsas, nomes fora de ordem e sufixos extras.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Interface.bend as I
import ../../src/Codec.bend as C
import ../../proof/CodecLei2.bend as G
import ../../proof/CodecRecusas.bend as R
import ../../proof/CodecMinimos.bend as M

law qualquer_corpo_no_limite_exato_satisfaz_relacao_original:
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  I.DecodificacaoCorreta(bs, R.opcional(C.decodificar(bs, corpo)))
def qualquer_corpo_no_limite_exato_satisfaz_relacao_original(bs, corpo, medido):
  G.decodificar_satisfaz_relacao_original(bs, corpo, corpo, medido, M.menor_igual64_reflexivo(corpo))
