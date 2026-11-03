import Base
import ./Data.bend as D
import ./Semantics.bend as S

def respond(cancel: Bool, r: S.Return) -> S.Action:
  match cancel:
    case True{}: S.Refuse{D.VText{"cancelled"}}
    case False{}:
      match r:
        case S.Datum{D.Cell{value}}: S.Finish{value}
        case _: S.Refuse{D.VAbsent{}}

def read(id: String, cancel: Bool) -> S.Action:
  S.Access{D.ReadCell{D.Users{}, id, "credential"}, respond(cancel)}

def write(+id: String, value: String, cancel: Bool) -> S.Action:
  S.Access{D.DefineColumn{D.Users{}, id, "credential", D.VText{value}},
    unit => read(id, cancel)}

def arguments(id: String, args: D.Value) -> S.Action:
  match args:
    case D.VText{value}: write(id, value, False{})
    case _: write(id, "discarded", True{})

def start(ctx: D.Context, args: D.Value) -> S.Action:
  D.Context{id, kind} = ctx
  arguments(id, args)

def program() -> S.Program:
  S.Program{start}
