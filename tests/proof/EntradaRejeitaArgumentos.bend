# Mutacao deliberada: deve falhar em falso, com corpo preenchido.
import Base
import ../../contrato/Dados.bend as D
import ../../contrato/Protocolo.bend as P
import ../../contrato/Semantica.bend as S
import ../../src/Entrada.bend as E
import ./Entrada.bend as F

law falso:
  {E.decodificar(F.montado(), F.esquema(), F.limites()) ==
    E.Pronta{F.publicado(), P.Requisicao{"segunda", "fonte exata\n𝄞", D.VAusente{}, "π\n\\prova"}} : E.PreAutenticacao}
def falso():
  F.pronta_exata_nos_dois_limites_inclusivos()
