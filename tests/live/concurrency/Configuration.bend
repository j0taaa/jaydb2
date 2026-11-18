import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E
import ./Free.bend as F

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"counters", "id",
    [D.Column{"id", D.TextValue{}, False{}}, D.Column{"value", D.Integer{}, False{}}]}]}

def limits() -> S.Limits:
  S.Limits{65536n, 65536n, 32768n}

def config() -> S.Configuration:
  F.configuration(schema(), limits(), E.identity())
