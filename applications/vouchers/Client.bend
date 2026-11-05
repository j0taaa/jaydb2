import Base
import ./Data.bend as D
import ./Semantics.bend as S
import ./Voucher.bend as P

def program() -> S.Program:
  S.Program{ctx => args => P.start(ctx, args)}
