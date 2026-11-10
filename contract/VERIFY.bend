# Executable theorem statements, witnesses, definitions and wire examples.
import Base
import ./DataExamples.bend as ExamplesData
import ./ProtocolTests.bend as ExamplesProtocol
import ./PreparedProtocol.bend as PreparedProtocol
import ./PreparedRegistry.bend as PreparedRegistry
import ./ReadOnlyContract.bend as ReadOnlyContract
import ./PreparedHandles.bend as PreparedHandles
# Verified replacement milestones: Init, Core clauses, ingress, fold and wire theorems.
import ./Theorems.bend as ExecutableStatements
import ../proof/Init.bend as InitWitness
import ../proof/Gate.bend as GateWitness
import ../proof/WireTheorems.bend as WireWitness
import ../proof/CoreClauses.bend as CoreWitness
import ../proof/Ingress.bend as IngressWitness
import ../proof/Iteration.bend as FoldWitness
import ../proof/ControlClauses.bend as ControlWitness
