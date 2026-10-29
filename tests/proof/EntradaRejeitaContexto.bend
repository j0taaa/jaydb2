# Mutacao deliberada: deve falhar em falso, com corpo preenchido.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./Entrada.bend as F

law falso:
  {E.analisar(F.montado(), F.esquema(), F.limites()) ==
    E.Recebida{F.publicado(), F.requisicao(), D.Contexto{"a", "pessoa"}} : E.Analise}
def falso():
  F.autenticacao_no_fim_do_cadastro_com_unicode_e_bits_exatos()
