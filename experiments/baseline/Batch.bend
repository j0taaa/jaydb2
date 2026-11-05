import Base
import ./Data.bend as D
import ./Semantics.bend as S

def write_7(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0007", "value", args},
    r => S.Finish{args}}

def write_6(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0006", "value", args},
    r => write_7(args)}

def write_5(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0005", "value", args},
    r => write_6(args)}

def write_4(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0004", "value", args},
    r => write_5(args)}

def write_3(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0003", "value", args},
    r => write_4(args)}

def write_2(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0002", "value", args},
    r => write_3(args)}

def write_1(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0001", "value", args},
    r => write_2(args)}

def write_0(+args: D.Value) -> S.Action:
  S.Access{D.DefineColumn{D.Application{"bench"}, "k0000", "value", args},
    r => write_1(args)}

def program() -> S.Program:
  S.Program{ctx => args => write_0(args)}
