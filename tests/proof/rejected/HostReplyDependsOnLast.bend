import Base
import ../../../contract/Data.bend as D
import ../../../src/Control.bend as C
import ../../../src/ControlBridge.bend as Wire

# Mutate the exact, root/last/registry-independent serialization clause:
# a host must not substitute its last response for the checked error bytes.
law false:
  for root: D.State
  for last: List<&2, U32>
  for reg: C.Registry
  {Wire.output(C.host_error("HANDLE", root, last, reg)) == last : List<&2, U32>}
def false(root, last, reg): {==}
