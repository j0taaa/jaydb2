import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Free.bend as L
import ./Environment.bend as E
def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"tasks", "id", [D.Column{"completed", D.Boolean{}, False{}}, D.Column{"due_on", D.TextValue{}, False{}}, D.Column{"estimated_minutes", D.Integer{}, False{}}, D.Column{"id", D.TextValue{}, False{}}, D.Column{"priority", D.Integer{}, False{}}, D.Column{"title", D.TextValue{}, False{}}]}]}
def limits() -> S.Limits:
  S.Limits{262144n, 8388608n, 262144n}
def config() -> S.Configuration:
  L.configuration(schema(), limits(), E.identity())
