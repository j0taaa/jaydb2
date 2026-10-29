# Mutacao: substituir a aridade inteira original por zero.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../src/Codec.bend as C
import ../../proof/CodecEstruturas.bend as E
import ../../proof/CodecCanonico.bend as K

law falso:
  for +xs: List<&2, D.Valor>
  for validos: E.ValoresValidos(xs)
  {P.codificar(C.montar_lista(xs, D.VListaVazia{})) ==
    P.finalizar(K.lista_bytes(0n, P.concatenar_opcional(K.conteudo_valores(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def falso(xs, validos):
  K.lista_montada_tem_codificacao_exata(xs, validos)
