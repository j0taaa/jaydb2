# Mutacao deliberada: deve falhar em falso, com corpo preenchido.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./Entrada.bend as F

law falso:
  {E.analisar(F.pacote(F.estado_bytes(), [0]), F.esquema(), F.limites()) ==
    E.Rejeitada{S.Autenticacao{}} : E.Analise}
def falso():
  {==}
