# A cached ceiling cannot change the exact represented u64.
import Base
import ../../../contract/Bytes.bend as B
import ../../../src/LimitWords.bend as Limits

law false:
  {Limits.select(True{}, 0n) == Some{B.Number64{0, 65535}} : Maybe<&2, B.Number64>}
def false():
  {==}
