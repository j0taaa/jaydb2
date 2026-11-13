import Base
import ../../../src/Transport.bend as T

# Fusing validation must still reject a non-octet in the cut prefix.
law false:
  {T.separate([0,0,0,0,0,0,0,1,256,7]) == Some{T.Parts{[256],[7]}} : Maybe<&2, T.Parts>}
def false(): {==}
