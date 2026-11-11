# Causal negative: cached execution cannot obtain a handle after registration
# has been omitted. The actual current lookup is empty, despite the book being
# able to reopen an original checked declaration at some other index.
import Base
import ../../../contract/PreparedRegistry.bend as G

law false:
  for -instance: String
  for -handle: String
  for -entry: G.Entry
  {G.lookup(instance, handle, Nil{}) == Some{entry} : Maybe<&2, G.Entry>}
def false(instance, handle, entry):
  {==}
