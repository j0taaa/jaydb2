# Reaplicacoes universais das quantidades reais e relacoes originais.
import Base
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Semantica.bend as S
import ../../contrato/Protocolo.bend as P
import ../../contrato/Logica.bend as L
import ../../src/Codec.bend as C
import ../../src/Entrada.bend as E
import ../../src/Requisicao.bend as Q
import ../../proof/EntradaMedida.bend as G

law reaplicar_corpo_admitido_preserva_resultado_do_codec:
  for +bs: List<&2, U32>
  for corpo: B.Numero64
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {E.ler_mensagem(Some{teto}, bs, s) == E.mensagem(C.decodificar(bs, teto), s) : E.PreAutenticacao}
def reaplicar_corpo_admitido_preserva_resultado_do_codec(bs, corpo, teto, s, medido, cabe):
  G.corpo_admitido_preserva_resultado_do_codec(bs, corpo, teto, s, medido, cabe)

law reaplicar_corpo_real_acima_do_teto_produz_limite:
  for +bs: List<&2, U32>
  for corpo: B.Numero64
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for acima: {C.menor_igual64(corpo, teto) == False{} : Bool}
  {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
def reaplicar_corpo_real_acima_do_teto_produz_limite(bs, corpo, teto, s, medido, acima):
  G.corpo_real_acima_do_teto_produz_limite(bs, corpo, teto, s, medido, acima)

law reaplicar_corpo_real_nao_representavel_produz_limite:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == None{} : Maybe<&2, B.Numero64>}
  {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
def reaplicar_corpo_real_nao_representavel_produz_limite(bs, teto, s, medido):
  G.corpo_real_nao_representavel_produz_limite(bs, teto, s, medido)

law reaplicar_decodificacao_aceita_preserva_mensagem:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +s: D.Estado
  for -v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  {E.ler_mensagem(Some{teto}, bs, s) == E.mensagem(C.decodificar(bs, teto), s) : E.PreAutenticacao}
def reaplicar_decodificacao_aceita_preserva_mensagem(bs, teto, s, v, aceito):
  G.decodificacao_aceita_preserva_mensagem(bs, teto, s, v, aceito)

law reaplicar_limite_interno_no_corpo_admitido_e_entrada:
  for +bs: List<&2, U32>
  for corpo: B.Numero64
  for +teto: B.Numero64
  for +s: D.Estado
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  for interno: {C.decodificar(bs, teto) == C.Limite{} : C.Resultado}
  {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Entrada{}} : E.PreAutenticacao}
def reaplicar_limite_interno_no_corpo_admitido_e_entrada(bs, corpo, teto, s, medido, cabe, interno):
  G.limite_interno_no_corpo_admitido_e_entrada(bs, corpo, teto, s, medido, cabe, interno)

law reaplicar_mensagem_do_codec_nunca_cria_limite_de_recurso:
  for resultado: C.Resultado
  for -s: D.Estado
  G.SemLimite(E.mensagem(resultado, s))
def reaplicar_mensagem_do_codec_nunca_cria_limite_de_recurso(resultado, s):
  G.mensagem_do_codec_nunca_cria_limite_de_recurso(resultado, s)

law reaplicar_mensagem_limite_exige_excesso_da_quantidade_real:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for +s: D.Estado
  for falha: {E.ler_mensagem(Some{teto}, bs, s) == E.ErroMensagem{S.Limite{}} : E.PreAutenticacao}
  G.QuantidadeExcedida(B.nat64(B.comprimento(bs)), teto)
def reaplicar_mensagem_limite_exige_excesso_da_quantidade_real(bs, teto, s, falha):
  G.mensagem_limite_exige_excesso_da_quantidade_real(bs, teto, s, falha)
