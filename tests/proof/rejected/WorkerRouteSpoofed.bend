import Base
import ../Controls.bend as C
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P
import ../../../src/Resolve.bend as Resolve
import ../../../src/Worker.bend as W
import ../../../src/Messages.bend as M

law false:
  {M.worker_route(W.ready_metadata("controls", C.seed(), P.Request{"token", "actual-handle", D.VAbsent{}, ""},
    "program", "proof", Some{D.Context{"alice", "user"}}, Resolve.Selected{P.Request{"token", "program", D.VAbsent{}, "proof"}})) == Some{"wrong-handle"} : Maybe<&2, String>}
def false(): {==}
