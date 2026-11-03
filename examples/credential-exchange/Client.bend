import Base
import ./Data.bend as D
import ./Semantics.bend as S

type Credentials is Data:
  Credentials{alice: String, bob: String}

def arguments(v: D.Value) -> Credentials:
  match v:
    case D.VList{D.VText{a}, D.VList{D.VText{b}, D.VListEmpty{}}}:
      Credentials{a, b}
    case _:
      Credentials{"bob-token", "alice-token"}

def respond(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}:
      S.Finish{value}
    case _:
      S.Refuse{D.VAbsent{}}

def read(id: String) -> S.Action:
  S.Access{D.ReadCell{D.Users{}, id, "credential"}, respond}

def write_bob(bob: String, id: String) -> S.Action:
  S.Access{D.DefineColumn{D.Users{}, "bob", "credential", D.VText{bob}},
    unit => read(id)}

def swap(c: Credentials, ctx: D.Context) -> S.Action:
  Credentials{alice, bob} = c
  D.Context{id, kind} = ctx
  S.Access{D.DefineColumn{D.Users{}, "alice", "credential", D.VText{alice}},
    unit => write_bob(bob, id)}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  swap(arguments(args), ctx)

def program() -> S.Program:
  S.Program{start}
