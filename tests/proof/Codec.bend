# Testes de aplicacao dos teoremas gerais; os 222 casos antigos continuam
# sendo regressao separada, sem serem confundidos com estes quantificadores.
import Base
import ./CodecCompletude.bend as Completude
import ./CodecLei2.bend as RelacaoOriginal
import ../../proof/Codec.bend as G
import ../../proof/CodecVerificar.bend as Todos
import ../../proof/CodecTextos.bend as Textos
import ../../proof/CodecTextoAceito.bend as TextoAceito
import ../../proof/CodecUnicode.bend as U
import ../../proof/CodecEstruturas.bend as E
import ../../proof/CodecCanonico.bend as K
import ../../proof/CodecPercurso.bend as R
import ../../proof/CodecInteiros.bend as J
import ../../contrato/Bytes.bend as B
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Logica.bend as L
import ../../src/Codec.bend as C

# Aplica a prova a entradas inteiramente arbitrarias, sem testemunha de
# canonicidade, validade, profundidade, quantidade ou tamanho declarados.
law qualquer_aceitacao_tem_garantias_gerais:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for aceito: {C.decodificar(bs, teto) == C.Decodificado{v} : C.Resultado}
  G.AceitacaoComprovada<bs, teto, v>
def qualquer_aceitacao_tem_garantias_gerais(bs, teto, v, aceito):
  G.aceitacao_garante_validade_limite_e_consumo_integral(bs, teto, v, aceito)

law unicode_de_qualquer_transicao_e_valido:
  for +u: C.Unicode
  for +b: U32
  U.EscalarValido(C.passo_utf8(u, b))
def unicode_de_qualquer_transicao_e_valido(u, b):
  U.passo_utf8_so_emite_escalares_validos(u, b)

law listas_de_largura_e_profundidade_arbitrarias:
  for +xs: List<&2, D.Valor>
  for validos: E.ValoresValidos(xs)
  {P.codificar(C.montar_lista(xs, D.VListaVazia{})) ==
    P.finalizar(K.lista_bytes(Nat.add(K.contar_valores(xs), 0n), P.concatenar_opcional(K.conteudo_valores(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def listas_de_largura_e_profundidade_arbitrarias(xs, validos):
  K.lista_montada_tem_codificacao_exata(xs, validos)

law registros_de_largura_e_profundidade_arbitrarias:
  for +xs: List<&2, D.Campo>
  for validos: E.CamposInvertidos(xs)
  {P.codificar(C.montar_registro(xs, D.VRegistroVazio{})) ==
    P.finalizar(K.registro_bytes(Nat.add(K.contar_campos(xs), 0n), P.concatenar_opcional(K.conteudo_campos(xs), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def registros_de_largura_e_profundidade_arbitrarias(xs, validos):
  K.registro_montado_tem_codificacao_exata(xs, validos)

law consumir_nao_ignora_o_primeiro_octeto_extra:
  for b: U32
  for xs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for v: D.Valor
  {C.percorrer(Con{b, xs}, corpo, teto, C.Pronto{v}) == C.Entrada{} : C.Resultado}
def consumir_nao_ignora_o_primeiro_octeto_extra(b, xs, corpo, teto, v):
  R.pronto_recusa_qualquer_octeto_extra(b, xs, corpo, teto, v)

# Instancias nao vazias exercitam a composicao dos invariantes.
def valores() -> List<&2, D.Valor>:
  [D.VTexto{"é𝄞"}, D.VLista{D.VInt{4294967295, 4294967295}, D.VListaVazia{}}]

def valores_validos() -> E.ValoresValidos(valores()):
  L.Ambos{{==}, L.Ambos{{==}, Unit{}}}

law lista_composta_nao_perde_unicode_nem_bits:
  {P.codificar(C.montar_lista(valores(), D.VListaVazia{})) ==
    P.finalizar(K.lista_bytes(Nat.add(K.contar_valores(valores()), 0n), P.concatenar_opcional(K.conteudo_valores(valores()), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def lista_composta_nao_perde_unicode_nem_bits():
  K.lista_montada_tem_codificacao_exata(valores(), valores_validos())

def campos() -> List<&2, D.Campo>:
  [D.Campo{"z", D.VTexto{"𝄞"}}, D.Campo{"a", D.VLista{D.VAusente{}, D.VListaVazia{}}}]

def campos_validos() -> E.CamposInvertidos(campos()):
  L.Ambos{{==}, L.Ambos{{==}, L.Ambos{{==}, L.Ambos{{==}, L.Ambos{{==}, Unit{}}}}}}

law registro_composto_tem_ordem_canonica:
  {P.codificar(C.montar_registro(campos(), D.VRegistroVazio{})) ==
    P.finalizar(K.registro_bytes(Nat.add(K.contar_campos(campos()), 0n), P.concatenar_opcional(K.conteudo_campos(campos()), Some{Nil{}}))) : Maybe<&2, List<&2, U32>>}
def registro_composto_tem_ordem_canonica():
  K.registro_montado_tem_codificacao_exata(campos(), campos_validos())

law qualquer_cauda_aceita_com_tag_inteiro_e_canonica:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for +aceito: {C.decodificar(Con{3, bs}, teto) == C.Decodificado{v} : C.Resultado}
  P.Codificacao(v, Con{3, bs})
def qualquer_cauda_aceita_com_tag_inteiro_e_canonica(bs, teto, v, aceito):
  J.toda_aceitacao_iniciada_por_tag_inteiro_e_canonica(bs, teto, v, aceito)

law qualquer_inteiro_canonico_dentro_do_limite_e_aceito:
  for +alto: U32
  for +baixo: U32
  for +teto: B.Numero64
  for cabe: {C.menor_igual64(B.Numero64{0, 9}, teto) == True{} : Bool}
  {C.decodificar(Con{3, B.be64(alto, baixo)}, teto) == C.Decodificado{D.VInt{alto, baixo}} : C.Resultado}
def qualquer_inteiro_canonico_dentro_do_limite_e_aceito(alto, baixo, teto, cabe):
  J.todo_inteiro_canonico_dentro_do_limite_e_aceito(alto, baixo, teto, cabe)

law qualquer_cauda_aceita_com_tag_texto_e_canonica:
  for +bs: List<&2, U32>
  for +teto: B.Numero64
  for -v: D.Valor
  for +aceito: {C.decodificar(Con{4, bs}, teto) == C.Decodificado{v} : C.Resultado}
  P.Codificacao(v, Con{4, bs})
def qualquer_cauda_aceita_com_tag_texto_e_canonica(bs, teto, v, aceito):
  TextoAceito.toda_aceitacao_iniciada_por_tag_texto_e_canonica(bs, teto, v, aceito)

law qualquer_texto_canonico_dentro_do_limite_e_aceito:
  for +s: String
  for +bs: List<&2, U32>
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +codificado: {P.codificar(D.VTexto{s}) == Some{bs} : Maybe<&2, List<&2, U32>>}
  for medido: {B.nat64(B.comprimento(bs)) == Some{corpo} : Maybe<&2, B.Numero64>}
  for cabe: {C.menor_igual64(corpo, teto) == True{} : Bool}
  {C.decodificar(bs, teto) == C.Decodificado{D.VTexto{s}} : C.Resultado}
def qualquer_texto_canonico_dentro_do_limite_e_aceito(s, bs, corpo, teto, codificado, medido, cabe):
  Textos.toda_codificacao_textual_dentro_do_limite_e_aceita(s, bs, corpo, teto, codificado, medido, cabe)
