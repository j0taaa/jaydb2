import Base
import ../../../contract/Data.bend as D

def context() -> D.Context:
  D.Context{"alice", "user"}

def arguments() -> D.Value:
  D.VList{D.VText{"save"}, D.VList{D.VText{"t1"}, D.VList{D.VText{"Buy bread"}, D.VList{D.VBool{False{}}, D.VListEmpty{}}}}}
