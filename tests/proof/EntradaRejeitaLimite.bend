# Mutacao deliberada: deve falhar em falso, com corpo preenchido.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./Entrada.bend as F

law falso:
  {E.analisar(F.montado(), F.esquema(), F.limite_mensagem_zero()) ==
    E.Rejeitada{S.Autenticacao{}} : E.Analise}
def falso():
  {==}
