# Os argumentos inseridos na fonte sao exatamente os valores recebidos,
# independentemente da largura/profundidade, sem construtores textuais aninhados.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../src/Codec.bend as C
import ../src/Reificacao.bend as R
import ./CodecCompleto.bend as G
import ./CodecMinimos.bend as M

law texto_de_octetos_tem_inversa_exata:
  for +bs: List<&2, U32>
  {R.octetos(R.texto(bs)) == bs : List<&2, U32>}
def texto_de_octetos_tem_inversa_exata(bs):
  match bs:
    case Nil{}:
      {==}
    case Con{b, +resto}:
      Equal.cong(List<&2, U32>, List<&2, U32>, xs => Con{b, xs}, R.octetos(R.texto(resto)), resto,
        texto_de_octetos_tem_inversa_exata(resto))

law reificacao_canonica_decodifica_exatamente_o_argumento:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +alto: U32
  for +baixo: U32
  for codificado: P.Codificacao(v, bs)
  for medido: {B.nat64(B.comprimento(bs)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  {R.decodificar(R.texto(bs), alto, baixo) == Some{v} : Maybe<&2, D.Valor>}
def reificacao_canonica_decodifica_exatamente_o_argumento(v, bs, alto, baixo, codificado, medido):
  %Equal.sym(List<&2, U32>, R.octetos(R.texto(bs)), bs, texto_de_octetos_tem_inversa_exata(bs)) :
    {R.extrair(C.decodificar(_, B.Numero64{alto, baixo})) == Some{v} : Maybe<&2, D.Valor>}
  Equal.cong(C.Resultado, Maybe<&2, D.Valor>, R.extrair,
    C.decodificar(bs, B.Numero64{alto, baixo}), C.Decodificado{v},
    G.toda_codificacao_canonica_representavel_e_decodificada(v, bs, B.Numero64{alto, baixo}, B.Numero64{alto, baixo},
      codificado, medido, M.menor_igual64_reflexivo(B.Numero64{alto, baixo})))

law fonte_de_argumentos_recupera_o_valor_sem_fallback:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +alto: U32
  for +baixo: U32
  for codificado: P.Codificacao(v, bs)
  for medido: {B.nat64(B.comprimento(bs)) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  {R.argumentos(R.texto(bs), alto, baixo) == v : D.Valor}
def fonte_de_argumentos_recupera_o_valor_sem_fallback(v, bs, alto, baixo, codificado, medido):
  Equal.cong(Maybe<&2, D.Valor>, D.Valor, R.valor,
    R.decodificar(R.texto(bs), alto, baixo), Some{v},
    reificacao_canonica_decodifica_exatamente_o_argumento(v, bs, alto, baixo, codificado, medido))
