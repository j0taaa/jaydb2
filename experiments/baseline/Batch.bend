import Base
import ./Data.bend as D
import ./Semantics.bend as S

# Scalar arguments set every row. A pair permits a late invalid write in
# validation: first seven take the first value, the last takes the second.
def first(args: D.Value) -> D.Value:
  match args:
    case D.VList{v, rest}: v
    case other: other

def last(args: D.Value) -> D.Value:
  match args:
    case D.VList{h, D.VList{v, rest}}: v
    case other: other

def write_7(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0007", "value", last(args)},
    r => S.Finish{args}}

def write_6(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0006", "value", first(args)},
    r => write_7(args)}

def write_5(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0005", "value", first(args)},
    r => write_6(args)}

def write_4(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0004", "value", first(args)},
    r => write_5(args)}

def write_3(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0003", "value", first(args)},
    r => write_4(args)}

def write_2(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0002", "value", first(args)},
    r => write_3(args)}

def write_1(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0001", "value", first(args)},
    r => write_2(args)}

def write_0(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0000", "value", first(args)},
    r => write_1(args)}

def program() -> S.Program:
  S.Program{ctx => args => write_0(args)}
