# Especializacao na raiz da propriedade local. Este lema e um combinador
# da inducao: nao afirma, por si, a propriedade local de todo Valor.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../src/Codec.bend as C
import ./CodecPercurso.bend as R
import ./CodecComposicao.bend as X
import ./CodecSequencias.bend as S
import ./CodecOctetos.bend as O
import ./CodecUTF8InversaTexto.bend as U

law completude_local_canonica_implica_aceitacao_publica:
  for +v: D.Valor
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for completo: S.CompletoLocal(v, bs)
  for codificado: P.Codificacao(v, bs)
  for +medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
def completude_local_canonica_implica_aceitacao_publica(v, bs, corpo, teto, completo, codificado, medido, cabe):
  octetos = O.qualquer_codificacao_so_emite_octetos(v, bs, codificado)
  medida_sufixo = {(%Equal.sym(List<&2, U32>, B.concatenar(bs, Nil{}), bs, U.concatenar_vazio_direita(bs)) :
    {B.nat64(B.comprimento(_)) == Some{corpo} : Maybe<&2, B.Numero64>}
    medido) : {B.nat64(B.comprimento(B.concatenar(bs, Nil{}))) == Some{corpo} : Maybe<&2, B.Numero64>}}
  execucao = completo(corpo, teto, C.Raiz{}, Nil{}, 0n, {==}, {==}, medida_sufixo, cabe)
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(B.comprimento(bs)), Some{corpo}, medido) :
    {C.decodificar_medida(_, bs, teto) == C.Decodificado{v} : C.Resultado}
  %Equal.sym(Bool, C.menor_igual64(corpo, teto), True{}, cabe) :
    {C.decodificar_tamanho(_, bs, corpo, teto) == C.Decodificado{v} : C.Resultado}
  %Equal.sym(Bool, B.octetos_validos(bs), True{}, octetos) :
    {C.decodificar_octetos(_, bs, corpo, teto) == C.Decodificado{v} : C.Resultado}
  Equal.trans(C.Resultado,
    C.percorrer(bs, corpo, teto, C.Tag{C.Raiz{}}), R.finalizar_quadro(R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}})), C.Decodificado{v},
    R.percurso_e_execucao_integral(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}),
    Equal.cong(R.Quadro, C.Resultado, q => R.finalizar_quadro(q), R.executar(bs, R.Quadro{corpo, teto, C.Tag{C.Raiz{}}}), X.depois(bs, corpo, teto, C.Pronto{v}), execucao))
