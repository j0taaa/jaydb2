# Transports public arguments to verified source. A text literal
# represents bytes as scalars 0..255; it does not apply UTF-8 again.
import Base
import ../contract/Bytes.bend as B
import ../contract/Data.bend as D
import ./Codec.bend as C

def text(bytes: List<&2, U32>) -> String:
  match bytes:
    case Nil{}:
      SNil{}
    case Con{b, rest}:
      SCon{Chr{b}, text(rest)}

def octets(s: String) -> List<&2, U32>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{Chr{b}, rest}:
      Con{b, octets(rest)}

def extract(result: C.Outcome) -> Maybe<&2, D.Value>:
  match result:
    case C.Decoded{value}:
      Some{value}
    case _:
      None{}

def decode(s: String, high: U32, low: U32) -> Maybe<&2, D.Value>:
  extract(C.decode(octets(s), B.Number64{high, low}))

# The generator supplies only admitted encodings, whose exact recovery
# is proved in proof/Reification.bend. None supplies no database data.
def value(result: Maybe<&2, D.Value>) -> D.Value:
  match result:
    case Some{v}:
      v
    case None{}:
      D.VAbsent{}

def arguments(s: String, high: U32, low: U32) -> D.Value:
  value(decode(s, high, low))

law octets_negative_reapply_utf8:
  {octets(text([0, 127, 128, 255])) == [0, 127, 128, 255] : List<&2, U32>}
def octets_negative_reapply_utf8():
  {==}
