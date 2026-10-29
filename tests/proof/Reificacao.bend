import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../src/Reificacao.bend as R
import ../../proof/Reificacao.bend as G

law todo_argumento_canonico_reificado_preserva_o_valor:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +alto: U32
  for +baixo: U32
  for codificado: P.Codificacao(v, bs)
  for medido: {B.nat64(B.comprimento(bs)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  {R.argumentos(R.texto(bs), alto, baixo) == v : D.Valor}
def todo_argumento_canonico_reificado_preserva_o_valor(v, bs, alto, baixo, codificado, medido):
  G.fonte_de_argumentos_recupera_o_valor_sem_fallback(v, bs, alto, baixo, codificado, medido)
