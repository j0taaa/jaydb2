# Canonical prepared-handle wire shape.
import Base
import ./Logic.bend as L

def hex_digit(+code: U32) -> Bool:
  (U32.is_ge(code, 48) && U32.is_le(code, 57)) ||
    (U32.is_ge(code, 97) && U32.is_le(code, 102))

def hex_text(text: String) -> Bool:
  match text:
    case SNil{}: True{}
    case SCon{Chr{code}, rest}: hex_digit(code) && hex_text(rest)

def HandleValid(+handle: String) -> Type:
  L.E<{String.length(handle) == 64n : Nat}, {hex_text(handle) == True{} : Bool}>
