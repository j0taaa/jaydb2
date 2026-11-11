# The two recovered length words retain their positions.
import Base
import ../../../proof/GeneratedArgumentCall.bend as A

law false:
  {A.parse_words(U32.show(1) ++ ", " ++ U32.show(2) ++ ")") == A.WordsRead{2, 1, ""} : A.WordsRead}
def false():
  {==}
