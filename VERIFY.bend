# Implemented pure components. The composition of the eight laws is checked
# in proof/VERIFY.bend, included in the make verify test aggregate.
import Base
import ./contract/VERIFY.bend as ContractOriginal
import ./src/Core.bend as Core
import ./src/Input.bend as Input
import ./src/Execution.bend as Execution
import ./src/Generate.bend as Generate
import ./src/Reification.bend as Reification
import ./src/ConfigurationCheck.bend as Configuration
import ./src/Messages.bend as Messages
import ./src/Free.bend as Free
import ./src/Termination.bend as Termination
