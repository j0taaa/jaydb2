# Single entry to check this package's types, lemmas and examples.
# Checker success does NOT mean Contract(a,k) was proved for
# any executable: this package does not yet contain that witness.
import Base
import ./LAWS.bend as Laws
import ./LEMMAS.bend as Lemmas
import ./DataExamples.bend as ExamplesData
import ./ProtocolTests.bend as ExamplesProtocol
import ./PreparedProtocol.bend as PreparedProtocol
import ./PreparedRegistry.bend as PreparedRegistry
import ./PreparedLaws.bend as PreparedLaws
import ./ReadOnlyContract.bend as ReadOnlyContract
# Verified replacement milestones: Init, Core clauses, ingress, fold and wire theorems.
import ./Theorems.bend as ExecutableStatements
import ../proof/Init.bend as InitWitness
import ../proof/Gate.bend as GateWitness
import ../proof/WireTheorems.bend as WireWitness
import ../proof/CoreClauses.bend as CoreWitness
import ../proof/Ingress.bend as IngressWitness
import ../proof/Iteration.bend as FoldWitness
