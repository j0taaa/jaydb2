import Base
import ../../../contract/Data.bend as D
import ../../../contract/Semantics.bend as S
import ../../../contract/Requirements.bend as R
import ../../../contract/Logic.bend as L
import ../Controls.bend as X
import ../GpuPrograms.bend as GPU

# The actual certificate's prefix obligation after this bang program reads
# Bob. Alice is present in the seed; failed reads must obey the installed law.
law false:
  R.SafetyPrefix(GPU.configuration(), X.seed(), X.context(), "gpu", D.VAbsent{}, X.seed(),
    S.events_execution_trace(S.execute(1n, GPU.program(), D.Schema{Nil{}}, X.seed(), X.context(), D.VAbsent{})))
def false():
  L.Both{L.Both{GPU.Pair{{==}, Unit{}}, Unit{}},
    L.Both{GPU.Pair{{==}, Unit{}}, Unit{}}}
