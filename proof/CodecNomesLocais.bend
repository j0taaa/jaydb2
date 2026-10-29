# Caso nome completo para o passo indutivo de registros. Todas as
# conferencias sao derivadas do nome original e da reserva de sufixo.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Protocolo.bend as P
import ../src/Codec.bend as C
import ./CodecPercurso.bend as R
import ./CodecComposicao.bend as X
import ./CodecSequencias.bend as S
import ./CodecCampos.bend as G
import ./CodecPalavrasBE64.bend as H
import ./CodecTextos.bend as T
import ./CodecLimitesSequencias.bend as K
import ./CodecNomesAbertura.bend as N
import ./CodecMontagemNomes.bend as E

law nome_canonico_completo_com_reserva_real:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pilha: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for +valido: {D.nome_valido(s) == True{} : Bool}
  for +medida_texto: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for minimo: {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for medido: {B.nat64(B.comprimento(B.concatenar(T.bytes_texto(alto, baixo, s), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(T.bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.TagNome{pilha}}) ==
    X.depois(T.bytes_texto(alto, baixo, s), corpo, teto, C.emitir_nome(pilha, s)) : R.Quadro}
def nome_canonico_completo_com_reserva_real(s, alto, baixo, corpo, teto, pilha, sufixo, r, valido, medida_texto, minimo, reserva, medido, cabe):
  +medida_resto = T.remover_prefixo_da_medida(9n, B.comprimento(B.concatenar(B.utf8(s), sufixo)), corpo, medido)
  limite = K.concatenar_segmentos_preserva_soma_dos_limites(B.utf8(s), sufixo, B.comprimento(B.utf8(s)), r,
    K.limite_reflexivo(B.comprimento(B.utf8(s))), reserva)
  cabecalho = X.cabecalho_variavel_com_corpo_e_teto_u64_arbitrario(C.NomeTexto{}, B.comprimento(B.utf8(s)), r, B.comprimento(B.concatenar(B.utf8(s), sufixo)), alto, baixo, pilha, corpo, teto,
    Unit{}, medida_texto, minimo, medida_resto, limite, cabe)
  S.compor_dois_segmentos_reais(Con{4, B.be64(alto, baixo)}, B.utf8(s), corpo, teto, C.TagNome{pilha},
    C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.NomeTexto{}, B.Numero64{alto, baixo}, pilha), C.emitir_nome(pilha, s), cabecalho,
    N.nome_valido_aberto_emite_na_pilha_original(s, B.Numero64{alto, baixo}, H.diminuir(9n, corpo), H.diminuir(9n, teto), pilha, valido, medida_texto))

law nome_medido_completo_em_qualquer_contexto:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for valido: {D.nome_valido(s) == True{} : Bool}
  for medida: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  G.NomeCompleto(s, T.bytes_texto(alto, baixo, s))
def nome_medido_completo_em_qualquer_contexto(s, alto, baixo, valido, medida):
  corpo => teto => pilha => sufixo => r => minimo => reserva => medido => cabe =>
    nome_canonico_completo_com_reserva_real(s, alto, baixo, corpo, teto, pilha, sufixo, r, valido, medida, minimo, reserva, medido, cabe)

def aplicar_nome_exposto(+s: String, +bs: List<&2, U32>,
  valido: {D.nome_valido(s) == True{} : Bool}, exposto: E.NomeExposto<s, bs>) -> G.NomeCompleto(s, bs):
  match exposto:
    case E.NomeExposto{B.Numero64{+alto, +baixo}, texto_valido, medida, bytes}:
      %Equal.sym(List<&2, U32>, bs, T.bytes_texto(alto, baixo, s), bytes) : G.NomeCompleto(s, _)
      nome_medido_completo_em_qualquer_contexto(s, alto, baixo, valido, medida)

law nome_canonico_completo:
  for +s: String
  for +bs: List<&2, U32>
  for valido: {D.nome_valido(s) == True{} : Bool}
  for codificado: {P.texto(s) == Some{bs} : Maybe<&2, List<&2, U32>>}
  G.NomeCompleto(s, bs)
def nome_canonico_completo(s, bs, valido, codificado):
  aplicar_nome_exposto(s, bs, valido, E.nome_canonico_expoe_tag_medida_e_utf8(s, bs, codificado))
