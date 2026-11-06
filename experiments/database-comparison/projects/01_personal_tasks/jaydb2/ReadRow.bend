import Base
import ./Data.bend as D
import ./Semantics.bend as S

def arg(args: D.Value, n: Nat) -> D.Value:
  match args n:
    case D.VList{v, rest} Zero{}: v
    case D.VList{v, rest} Succ{p}: arg(rest, p)
    case _ _: D.VAbsent{}

def text(v: D.Value) -> String:
  match v:
    case D.VText{s}: s
    case _: ""

def cell(r: S.Return) -> D.Value:
  match r:
    case S.Datum{D.Cell{v}}: v
    case _: D.VAbsent{}

def program() -> S.Program:
  S.Program{ctx => +args =>
    S.Access{D.ReadCell{D.Application{text(arg(args, 0n))}, text(arg(args, 1n)), text(arg(args, 2n))}, r0 =>
        S.Access{D.ReadCell{D.Application{text(arg(args, 0n))}, text(arg(args, 1n)), text(arg(args, 3n))}, r1 =>
            S.Access{D.ReadCell{D.Application{text(arg(args, 0n))}, text(arg(args, 1n)), text(arg(args, 4n))}, r2 =>
                S.Access{D.ReadCell{D.Application{text(arg(args, 0n))}, text(arg(args, 1n)), text(arg(args, 5n))}, r3 =>
                    S.Access{D.ReadCell{D.Application{text(arg(args, 0n))}, text(arg(args, 1n)), text(arg(args, 6n))}, r4 =>
                        S.Access{D.ReadCell{D.Application{text(arg(args, 0n))}, text(arg(args, 1n)), text(arg(args, 7n))}, r5 =>
                            S.Finish{D.VList{cell(r0), D.VList{cell(r1), D.VList{cell(r2), D.VList{cell(r3), D.VList{cell(r4), D.VList{cell(r5), D.VListEmpty{}}}}}}}}}}}}}}}
