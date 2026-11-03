import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E

def schema() -> D.Schema:
  D.Schema{Nil{}}

def limits() -> S.Limits:
  S.Limits{32768n, 65536n, 32768n}

def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
