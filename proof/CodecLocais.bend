# Casos base da inducao de completude, fortalecidos para QUALQUER pilha e
# sufixo com reserva suficiente, incluindo ancestrais que emitirao em cascata.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../src/Codec.bend as C
import ./CodecPercurso.bend as R
import ./CodecComposicao.bend as X
import ./CodecSequencias.bend as S
import ./CodecPalavrasBE64.bend as H
import ./CodecTextos.bend as T
import ./CodecMinimos.bend as M
import ./CodecLimitesSequencias.bend as K
import ./CodecUTF8Inversa.bend as V

law ausencia_completa_em_qualquer_contexto:
  S.CompletoLocal(D.VAusente{}, [0])
def ausencia_completa_em_qualquer_contexto():
  corpo => teto => pilha => sufixo => r => minimo => reserva => medido => cabe => {==}

def bytes_bool(b: Bool) -> List<&2, U32>:
  match b:
    case False{}:
      [1]
    case True{}:
      [2]

law booleano_completo_em_qualquer_contexto:
  for +b: Bool
  S.CompletoLocal(D.VBool{b}, bytes_bool(b))
def booleano_completo_em_qualquer_contexto(b):
  match b:
    case False{}:
      corpo => teto => pilha => sufixo => r => minimo => reserva => medido => cabe => {==}
    case True{}:
      corpo => teto => pilha => sufixo => r => minimo => reserva => medido => cabe => {==}

law inteiro_completo_em_qualquer_contexto:
  for +alto: U32
  for +baixo: U32
  S.CompletoLocal(D.VInt{alto, baixo}, Con{3, B.be64(alto, baixo)})
def inteiro_completo_em_qualquer_contexto(alto, baixo):
  corpo => teto => pilha => sufixo => r => minimo => reserva => medido => cabe =>
    X.cabecalho_canonico_composto_preserva_toda_a_pilha(C.Inteiro{}, alto, baixo, pilha, corpo, teto)

law texto_canonico_completo_com_reserva_real:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pilha: C.Pilha
  for +sufixo: List<&2, U32>
  for +r: Nat
  for valido: {B.texto_valido(s) == True{} : Bool}
  for +medida_texto: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  for minimo: {C.minimo_pilha(pilha) == B.nat64(r) : Maybe<&2, B.Numero64>}
  for reserva: {Nat.is_le(r, B.comprimento(sufixo)) == True{} : Bool}
  for medido: {B.nat64(B.comprimento(B.concatenar(T.bytes_texto(alto, baixo, s), sufixo))) == Some{corpo} : Maybe<&2, B.Numero64>}
  for +cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {R.executar(T.bytes_texto(alto, baixo, s), R.Quadro{corpo, teto, C.Tag{pilha}}) ==
    X.depois(T.bytes_texto(alto, baixo, s), corpo, teto, C.emitir(pilha, D.VTexto{s})) : R.Quadro}
def texto_canonico_completo_com_reserva_real(s, alto, baixo, corpo, teto, pilha, sufixo, r, valido, medida_texto, minimo, reserva, medido, cabe):
  +medida_resto = T.remover_prefixo_da_medida(9n, B.comprimento(B.concatenar(B.utf8(s), sufixo)), corpo, medido)
  limite = K.concatenar_segmentos_preserva_soma_dos_limites(B.utf8(s), sufixo, B.comprimento(B.utf8(s)), r,
    K.limite_reflexivo(B.comprimento(B.utf8(s))), reserva)
  cabecalho = X.cabecalho_variavel_com_corpo_e_teto_u64_arbitrario(C.Texto{}, B.comprimento(B.utf8(s)), r, B.comprimento(B.concatenar(B.utf8(s), sufixo)), alto, baixo, pilha, corpo, teto,
    Unit{}, medida_texto, minimo, medida_resto, limite, cabe)
  S.compor_dois_segmentos_reais(Con{4, B.be64(alto, baixo)}, B.utf8(s), corpo, teto, C.Tag{pilha},
    C.abrir_variavel(C.zero64(B.Numero64{alto, baixo}), C.Texto{}, B.Numero64{alto, baixo}, pilha), C.emitir(pilha, D.VTexto{s}), cabecalho,
    X.abertura_textual_canonica_emite_na_pilha_original(B.utf8(s), B.Numero64{alto, baixo}, H.diminuir(9n, corpo), H.diminuir(9n, teto), pilha, s, medida_texto, V.utf8_texto_valido_decodifica_exatamente(s, valido)))

law texto_completo_em_qualquer_contexto:
  for +s: String
  for +alto: U32
  for +baixo: U32
  for valido: {B.texto_valido(s) == True{} : Bool}
  for medida: {B.nat64(B.comprimento(B.utf8(s))) == Some{B.Numero64{alto, baixo}} : Maybe<&2, B.Numero64>}
  S.CompletoLocal(D.VTexto{s}, T.bytes_texto(alto, baixo, s))
def texto_completo_em_qualquer_contexto(s, alto, baixo, valido, medida):
  corpo => teto => pilha => sufixo => r => minimo => reserva => medido => cabe =>
    texto_canonico_completo_com_reserva_real(s, alto, baixo, corpo, teto, pilha, sufixo, r, valido, medida, minimo, reserva, medido, cabe)
