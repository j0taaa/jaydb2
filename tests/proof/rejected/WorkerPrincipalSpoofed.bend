import Base
import ../Controls.bend as C
import ../../../contract/Data.bend as D
import ../../../src/Input.bend as Input
import ../../../src/Messages.bend as M

law correct_principal:
  {M.authenticated_principal(Input.Received{C.seed(), C.request(), D.Context{"alice", "user"}}) == Some{"alice"} : Maybe<&2, String>}
def correct_principal(): {==}

law false:
  {M.authenticated_principal(Input.Received{C.seed(), C.request(), D.Context{"alice", "user"}}) == Some{"bob"} : Maybe<&2, String>}
def false(): {==}
