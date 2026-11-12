import Base
import ../Controls.bend as C
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../src/Input.bend as Input
import ../../../src/Messages.bend as M

def analysis() -> Input.Analysis:
  Input.Received{C.seed(), P.Request{"token", "handle",
    D.VList{D.VAbsent{}, D.VAbsent{}}, ""}, C.context()}

law correct_failure:
  {M.authentication_ready(analysis()) == False{} : Bool}
def correct_failure(): {==}

law false:
  {M.authentication_ready(analysis()) == True{} : Bool}
def false(): {==}
