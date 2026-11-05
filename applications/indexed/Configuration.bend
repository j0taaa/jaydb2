import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Policy.bend as P
import ./Environment.bend as E
import ./CheckedActions.bend as Checked
import ./Completion.bend as Completion
import ./Orders.bend as Orders

def business_table(name:String) -> D.SchemaTable:
  D.SchemaTable{name,"id",[D.Column{"available",D.Boolean{},False{}},D.Column{"id",D.TextValue{},False{}}]}

def index_table(name:String) -> D.SchemaTable:
  D.SchemaTable{name,"id",[D.Column{"id",D.TextValue{},False{}},D.Column{"target",D.TextValue{},False{}},D.Column{"value",D.TextValue{},False{}}]}

def schema() -> D.Schema:
  D.Schema{[business_table("alice"),index_table("alice_index"),business_table("bob"),index_table("bob_index")]}

def limits() -> S.Limits:
  S.Limits{65536n,65536n,32768n}

def config() -> S.Configuration:
  S.Configuration{schema(),P.laws(),limits(),E.identity()}
