import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Logica.bend as L
import ../../src/Estado.bend as E
import ../../src/Requisicao.bend as Q
import ../../proof/Representacao.bend as R
import ../../proof/Autenticacao.bend as A
import ./Certificado.bend as T

def esquema() -> D.Esquema:
  D.Esquema{[D.EsquemaTabela{"Coisas", "chave", [
    D.Coluna{"chave", D.Texto{}, False{}}, D.Coluna{"flag", D.Booleano{}, True{}},
    D.Coluna{"n", D.Inteiro{}, False{}}, D.Coluna{"texto", D.Texto{}, True{}}]}]}

def estado() -> D.Estado:
  D.Estado{[D.Tabela{"Coisas", [
    D.Linha{"a", [D.Campo{"chave", D.VTexto{"a"}}, D.Campo{"flag", D.VAusente{}},
      D.Campo{"n", D.VInt{2147483648, 0}}, D.Campo{"texto", D.VTexto{"é"}}]},
    D.Linha{"é", [D.Campo{"chave", D.VTexto{"é"}}, D.Campo{"flag", D.VBool{False{}}},
      D.Campo{"n", D.VInt{2147483647, 4294967295}}, D.Campo{"texto", D.VAusente{}}]}]}],
    [T.usuario("a", "c1"), T.usuario("aa", "c2"), T.usuario("é", "c3")]}

law estrutura_da_amostra:
  {D.estrutura(esquema(), estado()) == True{} : Bool}
def estrutura_da_amostra():
  {==}

law roundtrip_sem_perder_ausencia_unicode_nem_bits:
  {E.decodificar(D.estado_valor(estado()), esquema()) == Some{estado()} : Maybe<&2, D.Estado>}
def roundtrip_sem_perder_ausencia_unicode_nem_bits():
  R.transporte_privado_preserva_estado(esquema(), estado(), estrutura_da_amostra())

law saida_do_transporte_estruturada:
  {D.estrutura(esquema(), estado()) == True{} : Bool}
def saida_do_transporte_estruturada():
  R.transporte_privado_so_devolve_estado_estruturado(D.estado_valor(estado()), esquema(), estado(), roundtrip_sem_perder_ausencia_unicode_nem_bits())

law contexto_de_usuario_no_fim_do_cadastro:
  {D.contexto_presente(estado(), D.Contexto{"é", "pessoa"}) == True{} : Bool}
def contexto_de_usuario_no_fim_do_cadastro():
  A.autenticacao_implica_contexto_presente(esquema(), estado(), "c3", D.Contexto{"é", "pessoa"}, estrutura_da_amostra(), {==})

law credencial_vazia_nao_autentica:
  {D.autenticar(estado(), "") == None{} : Maybe<&2, D.Contexto>}
def credencial_vazia_nao_autentica():
  A.estado_publicavel_nao_autentica_vazio(esquema(), estado(), estrutura_da_amostra())

def requisicao() -> P.Requisicao:
  P.Requisicao{"c3", "\"\\n\n𝄞", D.VLista{D.VInt{4294967295, 4294967295}, D.VLista{D.VAusente{}, D.VListaVazia{}}}, "π\n\\"}

law envelope_preserva_fonte_prova_e_argumentos:
  {Q.extrair(P.requisicao_valor(requisicao())) == Some{requisicao()} : Maybe<&2, P.Requisicao>}
def envelope_preserva_fonte_prova_e_argumentos():
  R.requisicao_valida_preserva_todos_os_campos(requisicao(), {==})

law envelope_extraido_e_exatamente_o_original:
  {P.requisicao_valor(requisicao()) == P.requisicao_valor(requisicao()) : D.Valor}
def envelope_extraido_e_exatamente_o_original():
  R.envelope_aceito_reconstroi_exatamente(P.requisicao_valor(requisicao()), requisicao(), {==})

law envelope_aceito_tambem_e_valido:
  {D.valor_valido(P.requisicao_valor(requisicao())) == True{} : Bool}
def envelope_aceito_tambem_e_valido():
  L.e_esquerda(
    {D.valor_valido(P.requisicao_valor(requisicao())) == True{} : Bool},
    {P.requisicao_valor(requisicao()) == P.requisicao_valor(requisicao()) : D.Valor},
    R.extrair_preserva_valor_e_valida(P.requisicao_valor(requisicao()), requisicao(), envelope_preserva_fonte_prova_e_argumentos()))
