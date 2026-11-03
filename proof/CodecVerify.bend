# Aggregate of general Codec theorems, including canonical equivalence.
# Does not construct Environment or assert executable/host Contract.
import Base
import ./Codec.bend as Validity
import ./CodecIntegers.bend as Integers
import ./CodecTexts.bend as Texts
import ./CodecTextAccepted.bend as TextAccepted
import ./CodecArities.bend as Arities
import ./CodecMinimum.bend as Minimum
import ./CodecUTF8InverseText.bend as UTF8Inverse
import ./CodecUTF8InverseOctets.bend as Octets

import ./CodecMinimumStack.bend as MinimumStack
import ./CodecSumsMinimum.bend as SumsMinimum
import ./CodecLimitsPartial.bend as LimitsPartial
import ./CodecLimitsStack.bend as LimitsStack
import ./CodecLimitsCopy.bend as LimitsCopy
import ./CodecReservations.bend as Reservations
import ./CodecComposition.bend as Composition
import ./CodecSequences.bend as Sequences
import ./CodecLocals.bend as Locals
import ./CodecFields.bend as Fields
import ./CodecRecords.bend as Records
import ./CodecNamesLocals.bend as NamesLocals
import ./CodecAssemblyVerify.bend as Assembly
import ./CodecOctets.bend as OctetsOriginal
import ./CodecPublic.bend as Public
import ./CodecComplete.bend as Complete
import ./CodecPrimitives.bend as Primitives
import ./CodecRelax.bend as Relax
import ./CodecRefusals.bend as Refusals
import ./CodecAcceptance.bend as Acceptance
import ./CodecLaw2.bend as RelationOriginal
