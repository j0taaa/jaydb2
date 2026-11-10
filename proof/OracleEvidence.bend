# A generated worker constructs this checked package from its certificate law.
import Base
import ../contract/Theorems.bend as T
import ../contract/Protocol.bend as P
import ../contract/Semantics.bend as S
import ../src/Gate.bend as Gate

# Two equal oracle occurrences respect linear use by the Core and emission
# proofs. The generated package supplies the same closed admit twice.
type Checked<-c: S.Configuration> is Type:
  Checked{admit: Gate.Oracle(), bridge: Gate.Oracle(), same: {bridge == admit : Gate.Oracle()}, sound: @r: P.Request -> T.OracleSoundness(c, r, admit)}

def oracle(-c: S.Configuration, checked: Checked<c>) -> Gate.Oracle():
  match checked:
    case Checked{admit, bridge, same, sound}: admit
