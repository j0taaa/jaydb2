# A following digit extends the token; it cannot be a source boundary.
import Base
import ../../../proof/DecimalParser.bend as P

law false_following_digit_is_preserved_as_suffix:
  {P.parse_word(U32.show(1) ++ "0") == P.WordParsed{1, "0"} : P.WordParsed}
def false_following_digit_is_preserved_as_suffix():
  {==}
