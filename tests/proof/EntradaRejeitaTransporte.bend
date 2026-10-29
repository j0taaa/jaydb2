# Mutacao deliberada: deve falhar em falso, com corpo preenchido.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./Entrada.bend as F

law falso:
  {E.analisar(F.pacote([0], F.mensagem_bytes()), F.esquema(), F.limites()) ==
    E.Rejeitada{S.Entrada{}} : E.Analise}
def falso():
  {==}
