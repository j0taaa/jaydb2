import Base
import ./Data.bend as D
import ./Semantics.bend as S

def token(args: D.Value) -> D.Value:
  match args:
    case D.VText{s}:
      D.VText{s}
    case _:
      D.VText{"new"}

def respond(r: S.Return) -> S.Action:
  match r:
    case S.Datum{D.Cell{value}}:
      S.Finish{value}
    case _:
      S.Refuse{D.VAbsent{}}

def read(id: String) -> S.Action:
  S.Access{D.ReadCell{D.Users{}, id, "credential"}, respond}

def write(+id: String, args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Users{}, id, "credential", token(args)},
    unit => read(id)}

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{+id, kind} = ctx
  S.Access{D.DefineColumn{D.Users{}, id, "credential", D.VText{""}},
    unit => write(id, args)}

def program() -> S.Program:
  S.Program{start}
