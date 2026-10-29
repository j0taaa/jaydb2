import Base
import ./Dados.bend as D
import ./Semantica.bend as S
import ./Livre.bend as L
import ./Environment.bend as E

def esquema() -> D.Esquema:
  D.Esquema{Nil{}}

def limites() -> S.Limites:
  S.Limites{32768n, 65536n, 32768n}

def config() -> S.Configuracao:
  L.configuracao(esquema(), limites(), E.identidade())
