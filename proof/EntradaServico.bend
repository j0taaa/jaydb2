# O mesmo snapshot publicado e transmitido; a autenticacao nao usa outro estado.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../contrato/Requisitos.bend as R
import ../contrato/Semantica.bend as S
import ../src/Codec.bend as C
import ../src/Entrada.bend as E
import ../src/Estado.bend as Estado
import ../src/Transporte.bend as T
import ./CodecCompleto.bend as Codec
import ./CodecOctetos.bend as Octetos
import ./Representacao.bend as Representacao
import ./Transporte.bend as Transporte

# Nem sucesso da mensagem nem identidade sao premissas. O corpo pode ser
# recusado; mesmo assim toda analise utiliza exatamente o snapshot recebido.
law pacote_privado_usa_estado_canonico:
  for +e: D.Esquema
  for +s: D.Estado
  for +l: S.Limites
  for +be: List<&2, U32>
  for +br: List<&2, U32>
  for +bs: List<&2, U32>
  for +ce: B.Numero64
  for +te: B.Numero64
  for canonico: P.Codificacao(D.estado_valor(s), be)
  for montagem: {T.juntar(be, br) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for octetos: {B.octetos_validos(br) == True{} : Bool}
  for medida: {B.nat64(B.comprimento(be)) == Some{ce} : Maybe<&2, B.Numero64>}
  for teto: {B.nat64(R.limite_estado(l)) == Some{te} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(ce, te) == True{} : Bool}
  for estrutura: {D.estrutura(e, s) == True{} : Bool}
  {E.decodificar(bs, e, l) == E.ler_mensagem(B.nat64(R.limite_mensagem(l)), br, s) : E.PreAutenticacao}
def pacote_privado_usa_estado_canonico(e, s, l, be, br, bs, ce, te, canonico,
  montagem, octetos, medida, teto, cabe, estrutura):
  +codificacao = {canonico : {P.codificar(D.estado_valor(s)) == Some{be} : Maybe<&2, List<&2, U32>>}}
  %Equal.sym(Maybe<&2, T.Partes>, T.separar(bs), Some{T.Partes{be, br}},
    Transporte.separar_inverte_toda_montagem_valida(be, br, bs, montagem,
      Octetos.qualquer_codificacao_so_emite_octetos(D.estado_valor(s), be, codificacao), octetos)) :
      {E.partes(_, e, l) == E.ler_mensagem(B.nat64(R.limite_mensagem(l)), br, s) : E.PreAutenticacao}
  %Equal.sym(Maybe<&2, B.Numero64>, B.nat64(R.limite_estado(l)), Some{te}, teto) :
    {E.ler_estado(_, e, be, br, B.nat64(R.limite_mensagem(l))) == E.ler_mensagem(B.nat64(R.limite_mensagem(l)), br, s) : E.PreAutenticacao}
  %Equal.sym(C.Resultado, C.decodificar(be, te), C.Decodificado{D.estado_valor(s)},
    Codec.toda_codificacao_canonica_representavel_e_decodificada(D.estado_valor(s), be, ce, te, codificacao, medida, cabe)) :
      {E.estado_decodificado(_, e, br, B.nat64(R.limite_mensagem(l))) == E.ler_mensagem(B.nat64(R.limite_mensagem(l)), br, s) : E.PreAutenticacao}
  %Equal.sym(Maybe<&2, D.Estado>, Estado.decodificar(D.estado_valor(s), e), Some{s},
    Representacao.transporte_privado_preserva_estado(e, s, estrutura)) :
      {E.estado_lido(_, br, B.nat64(R.limite_mensagem(l))) == E.ler_mensagem(B.nat64(R.limite_mensagem(l)), br, s) : E.PreAutenticacao}
  {==}
