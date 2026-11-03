import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E
import ./Policy.bend as Policy
import ./Proofs.bend as Proofs

# One table per person allows enumeration of only their own tasks.
def table(name: String) -> D.SchemaTable:
  D.SchemaTable{name, "id", [D.Column{"completed", D.Boolean{}, False{}},
    D.Column{"id", D.TextValue{}, False{}}, D.Column{"owner", D.TextValue{}, False{}},
    D.Column{"title", D.TextValue{}, False{}}]}

def schema() -> D.Schema:
  D.Schema{[table("alice"), table("bob")]}

def limits() -> S.Limits:
  S.Limits{32768n, 65536n, 32768n}

def environment() -> String:
  E.identity()

def config() -> S.Configuration:
  Policy.config(schema(), limits(), environment())
