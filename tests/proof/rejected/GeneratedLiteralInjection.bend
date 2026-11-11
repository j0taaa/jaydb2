# Removing quote escaping closes the literal inside the supplied payload.
import Base
import ../../../proof/GeneratedLiterals.bend as Lexer

def unescaped(value: String) -> String:
  "\"" ++ value ++ "\""

law false:
  for -rest: String
  {Lexer.parse(2n, unescaped("\"") ++ rest) == Lexer.Literal{"\"", rest} : Lexer.Parsed}
def false(rest):
  {==}
