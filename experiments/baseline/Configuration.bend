# Dedicated permissive benchmark instance; technical validation is unchanged.
import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"bench", "id", [
    D.Column{"id", D.TextValue{}, False{}},
    D.Column{"pad", D.TextValue{}, False{}},
    D.Column{"value", D.Integer{}, False{}}]}]}

def limits() -> S.Limits:
  S.Limits{32768n, 65536n, 32768n}

def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
