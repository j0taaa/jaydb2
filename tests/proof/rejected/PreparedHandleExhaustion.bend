# Even zero registry entries cannot exhaust the fixed namespace.
import Base
import ../../../proof/HandleAllocation.bend as A

law false:
  {A.native_allocate(Word.zero(256n), Nil{}) == None{} : Maybe<&2, String>}
def false():
  {==}
