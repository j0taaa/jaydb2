import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E
import ./Policy.bend as P
# Proof modules imported here are the administrator's published helpers that
# client certificates may import.
import ./Proofs.bend as Proofs
import ./Directory.bend as Directory
import ./Completion.bend as Completion

def directory(name: String) -> D.SchemaTable:
  D.SchemaTable{name, "id", [D.Column{"id", D.TextValue{}, False{}}, D.Column{"owner", D.TextValue{}, False{}}]}

# One shared notes table; each user's directory lists that user's note ids.
def schema() -> D.Schema:
  D.Schema{[directory("alice_dir"), directory("bob_dir"), D.SchemaTable{"notes", "id",
    [D.Column{"id", D.TextValue{}, False{}}, D.Column{"owner", D.TextValue{}, False{}},
      D.Column{"text", D.TextValue{}, False{}}]}]}

def limits() -> S.Limits:
  S.Limits{65536n, 65536n, 32768n}

def environment() -> String:
  E.identity()

def config() -> S.Configuration:
  P.config(schema(), limits(), environment())
