import Base
import ../../../src/Transport.bend as T

# A prefix-only parse cannot be treated as a fully validated packet.
law false:
  {T.separate([0,0,0,0,0,0,0,1,7,256]) == Some{T.Parts{[7],[256]}} : Maybe<&2, T.Parts>}
def false(): {==}
