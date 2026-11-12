# Metadata-preserving adapter around the unchanged checked Execution machine.
# The generated prepared driver uses these exact constructors and advance.
import Base
import ../contract/Semantics.bend as S
import ./Execution.bend as X
import ./Messages.bend as M

type StateExecution is Type:
  StateExecution{metadata: M.WorkerMetadata, execution: X.StateExecution}

type Iteration is Type:
  Continue{state: StateExecution}
  Prepare{state: StateExecution}
  FinishOutput{bytes: List<&2, U32>}
  Inconsistent{}

def attach(metadata: M.WorkerMetadata, iteration: X.Iteration) -> Iteration:
  match iteration:
    case X.Continue{state}: Continue{StateExecution{metadata, state}}
    case X.Prepare{state}: Prepare{StateExecution{metadata, state}}
    case X.FinishOutput{bytes}: FinishOutput{M.worker_result(M.WorkerResult{metadata, bytes})}
    case X.Inconsistent{}: Inconsistent{}

def advance(state: StateExecution, c: S.Configuration) -> Iteration:
  StateExecution{metadata, execution} = state
  attach(metadata, X.advance(execution, c))

law terminal_binds_metadata_and_exact_decision:
  for metadata: M.WorkerMetadata
  for bytes: List<&2, U32>
  {attach(metadata, X.FinishOutput{bytes}) == FinishOutput{M.worker_result(M.WorkerResult{metadata, bytes})} : Iteration}
def terminal_binds_metadata_and_exact_decision(metadata, bytes): {==}
