# A validade do nome fornece os testes reais da abertura NomeTexto.
# Nao ha premissa de conferencia: positividade e limite64 sao derivados.
import Base
import ../contrato/Bytes.bend as B
import ../contrato/Dados.bend as D
import ../contrato/Logica.bend as L
import ../src/Codec.bend as C
import ./Fundamentos.bend as F
import ./CodecNomesASCII.bend as A
import ./CodecContadores.bend as N
import ./CodecSomasOrdem.bend as O
import ./CodecLimitesNomes.bend as Z
import ./CodecConteudo.bend as G
import ./CodecComposicao.bend as M
import ./CodecPercurso.bend as R

law sessenta_e_quatro_tem_medida_exata:
  {B.nat64(64n) == Some{B.Numero64{0, 64}} : Maybe<&2, B.Numero64>}
def sessenta_e_quatro_tem_medida_exata():
  {==}

law nome_valido_utf8_tem_medida_representavel:
  for +s: String
  for valido: {D.nome_valido(s) == True{} : Bool}
  O.NumeroRepresentado<B.nat64(B.comprimento(B.utf8(s)))>
def nome_valido_utf8_tem_medida_representavel(s, valido):
  O.nat64_representabilidade_fechada_para_baixo(B.comprimento(B.utf8(s)), 64n, B.Numero64{0, 64},
    sessenta_e_quatro_tem_medida_exata(), A.nome_valido_utf8_tem_ate64_octetos(s, valido))

law nome_valido_medido_respeita_limite64:
  for +s: String
  for +q: B.Numero64
  for valido: {D.nome_valido(s) == True{} : Bool}
  for medido: {B.nat64(B.comprimento(B.utf8(s))) == Some{q} : Maybe<&2, B.Numero64>}
  {C.menor_igual64(q, B.Numero64{0, 64}) == True{} : Bool}
def nome_valido_medido_respeita_limite64(s, q, valido, medido):
  O.menor_igual64_preserva_ordem_nat(B.comprimento(B.utf8(s)), 64n, q, B.Numero64{0, 64},
    medido, sessenta_e_quatro_tem_medida_exata(), A.nome_valido_utf8_tem_ate64_octetos(s, valido))

law medida_de_bytes_nao_vazios_e_positiva:
  for +bs: List<&2, U32>
  for -q: B.Numero64
  for positivo: G.NaoVazio(bs)
  for medido: {B.nat64(B.comprimento(bs)) == Some{q} : Maybe<&2, B.Numero64>}
  {C.zero64(q) == False{} : Bool}
def medida_de_bytes_nao_vazios_e_positiva(bs, q, positivo, medido):
  match bs:
    case Nil{}:
      L.ex_falso({C.zero64(q) == False{} : Bool}, positivo)
    case Con{h, t}:
      N.nat64_sucessor_nunca_zero(B.comprimento(t), q, medido)

law nome_valido_medido_nao_e_zero:
  for +s: String
  for -q: B.Numero64
  for valido: {D.nome_valido(s) == True{} : Bool}
  for medido: {B.nat64(B.comprimento(B.utf8(s))) == Some{q} : Maybe<&2, B.Numero64>}
  {C.zero64(q) == False{} : Bool}
def nome_valido_medido_nao_e_zero(s, q, valido, medido):
  medida_de_bytes_nao_vazios_e_positiva(B.utf8(s), q,
    Z.texto_nao_vazio_utf8_nao_vazio(s, Z.nome_valido_nao_e_vazio(s, valido)), medido)

law nome_valido_medido_abre_conteudo:
  for +s: String
  for +q: B.Numero64
  for +pilha: C.Pilha
  for +valido: {D.nome_valido(s) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.utf8(s))) == Some{q} : Maybe<&2, B.Numero64>}
  {C.abrir_variavel(C.zero64(q), C.NomeTexto{}, q, pilha) ==
    C.Conteudo{True{}, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha} : C.Maquina}
def nome_valido_medido_abre_conteudo(s, q, pilha, valido, medido):
  %Equal.sym(Bool, C.zero64(q), False{}, nome_valido_medido_nao_e_zero(s, q, valido, medido)) :
    {C.abrir_variavel(_, C.NomeTexto{}, q, pilha) ==
      C.Conteudo{True{}, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha} : C.Maquina}
  %Equal.sym(Bool, C.menor_igual64(q, B.Numero64{0, 64}), True{},
    nome_valido_medido_respeita_limite64(s, q, valido, medido)) :
    {C.abrir_nome(_, q, pilha) ==
      C.Conteudo{True{}, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha} : C.Maquina}
  {==}

# Executa os bytes reais do nome e preserva a pilha e os contadores finais.
law nome_valido_aberto_emite_na_pilha_original:
  for +s: String
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +pilha: C.Pilha
  for +valido: {D.nome_valido(s) == True{} : Bool}
  for +medido: {B.nat64(B.comprimento(B.utf8(s))) == Some{q} : Maybe<&2, B.Numero64>}
  {R.executar(B.utf8(s), R.Quadro{corpo, teto, C.abrir_variavel(C.zero64(q), C.NomeTexto{}, q, pilha)}) ==
    M.depois(B.utf8(s), corpo, teto, C.emitir_nome(pilha, s)) : R.Quadro}
def nome_valido_aberto_emite_na_pilha_original(s, q, corpo, teto, pilha, valido, medido):
  %Equal.sym(C.Maquina,
    C.abrir_variavel(C.zero64(q), C.NomeTexto{}, q, pilha),
    C.Conteudo{True{}, C.um64(q), C.diminuir64(q), C.Inicio{}, "", pilha},
    nome_valido_medido_abre_conteudo(s, q, pilha, valido, medido)) :
    {R.executar(B.utf8(s), R.Quadro{corpo, teto, _}) ==
      M.depois(B.utf8(s), corpo, teto, C.emitir_nome(pilha, s)) : R.Quadro}
  M.conteudo_canonico_emite_na_pilha_original(s, q, corpo, teto, True{}, pilha,
    Z.texto_nao_vazio_utf8_nao_vazio(s, Z.nome_valido_nao_e_vazio(s, valido)),
    A.nome_valido_e_texto_valido(s, valido), medido)

law nome_valido_ordenado_aberto_produz_campo:
  for +s: String
  for +q: B.Numero64
  for +corpo: B.Numero64
  for +teto: B.Numero64
  for +ultimo: Bool
  for +restantes: B.Numero64
  for +anterior: String
  for +campos: List<&2, D.Campo>
  for +pai: C.Pilha
  for +valido: {D.nome_valido(s) == True{} : Bool}
  for medido: {B.nat64(B.comprimento(B.utf8(s))) == Some{q} : Maybe<&2, B.Numero64>}
  for ordem: {String.is_lt(anterior, s) == True{} : Bool}
  {R.executar(B.utf8(s), R.Quadro{corpo, teto,
      C.abrir_variavel(C.zero64(q), C.NomeTexto{}, q, C.Nome{ultimo, restantes, anterior, campos, pai})}) ==
    M.depois(B.utf8(s), corpo, teto, C.Tag{C.Campo{ultimo, restantes, s, campos, pai}}) : R.Quadro}
def nome_valido_ordenado_aberto_produz_campo(s, q, corpo, teto, ultimo, restantes, anterior, campos, pai, valido, medido, ordem):
  Equal.trans(R.Quadro,
    R.executar(B.utf8(s), R.Quadro{corpo, teto,
      C.abrir_variavel(C.zero64(q), C.NomeTexto{}, q, C.Nome{ultimo, restantes, anterior, campos, pai})}),
    M.depois(B.utf8(s), corpo, teto, C.emitir_nome(C.Nome{ultimo, restantes, anterior, campos, pai}, s)),
    M.depois(B.utf8(s), corpo, teto, C.Tag{C.Campo{ultimo, restantes, s, campos, pai}}),
    nome_valido_aberto_emite_na_pilha_original(s, q, corpo, teto,
      C.Nome{ultimo, restantes, anterior, campos, pai}, valido, medido),
    (%Equal.sym(Bool, D.nome_valido(s) && String.is_lt(anterior, s), True{},
      F.e_booleano_intro(D.nome_valido(s), String.is_lt(anterior, s), valido, ordem)) :
      {M.depois(B.utf8(s), corpo, teto, C.nome_conferido(_, ultimo, restantes, s, campos, pai)) ==
        M.depois(B.utf8(s), corpo, teto, C.Tag{C.Campo{ultimo, restantes, s, campos, pai}}) : R.Quadro}
      {==}))
