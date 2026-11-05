import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Environment.bend as E
import ./Policy.bend as P
import ./Proofs.bend as H
import ./ReceiptLaws.bend as RL
import ./Voucher.bend as Protocol
import ./Initial.bend as Initial

def table(name: String) -> D.SchemaTable:
  D.SchemaTable{name, "id", [D.Column{"enabled", D.Boolean{}, True{}},
    D.Column{"id", D.TextValue{}, False{}}, D.Column{"input", D.TextValue{}, True{}},
    D.Column{"operation", D.TextValue{}, True{}}, D.Column{"owner", D.TextValue{}, False{}},
    D.Column{"result", D.TextValue{}, True{}}]}

def schema() -> D.Schema:
  D.Schema{[table("alice"), table("bob")]}

def limits() -> S.Limits:
  S.Limits{32768n, 65536n, 32768n}

def environment() -> String:
  E.identity()

def laws() -> S.Laws:
  S.MoreOneLaw{P.Rule, S.MoreOneLaw{RL.Rule(~Protocol.program(), ~Initial.origin, schema(), limits()), S.NoneLaw{}}}

def config() -> S.Configuration:
  S.Configuration{schema(), laws(), limits(), environment()}
