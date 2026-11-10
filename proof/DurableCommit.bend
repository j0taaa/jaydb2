# Four-call image commit transition model, in the order of storage::commit.
# Each IO call can fail before OR after its effect. Atomic replacement and
# fsync crash semantics are the filesystem boundary, not proved Rust syscalls.
# No post-state invariant, final trace, fair IO, or checksum injectivity is a
# premise. Actual Rust/OS call-by-call refinement remains a separate obligation.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ./History.bend as History

type Phase is Data:
  Old{}
  TempWritten{}
  TempSynced{}
  Replaced{}
  DirectorySynced{}

type Return is Data:
  Succeeded{}
  FailedBefore{}
  FailedAfter{}

type Returns is Data:
  Returns{write: Return, file_sync: Return, replace: Return, directory_sync: Return}

type EffectResult is Data:
  IoApplied{phase: Phase}
  IoError{phase: Phase}

def effect(answer: Return, before: Phase, after: Phase) -> EffectResult:
  match answer:
    case Succeeded{}: IoApplied{after}
    case FailedBefore{}: IoError{before}
    case FailedAfter{}: IoError{after}

type CommitResult is Data:
  CommitReady{phase: Phase}
  CommitFailed{uncertain: Bool, phase: Phase}

def directory_result(result: EffectResult) -> CommitResult:
  match result:
    case IoApplied{phase}: CommitReady{phase}
    case IoError{phase}: CommitFailed{True{}, phase}

def replacement_result(result: EffectResult, directory_sync: Return) -> CommitResult:
  match result:
    case IoError{phase}: CommitFailed{True{}, phase}
    case IoApplied{phase}: directory_result(effect(directory_sync, phase, DirectorySynced{}))

def file_sync_result(result: EffectResult, replace: Return, directory_sync: Return) -> CommitResult:
  match result:
    case IoError{phase}: CommitFailed{False{}, phase}
    case IoApplied{phase}: replacement_result(effect(replace, phase, Replaced{}), directory_sync)

def write_result(result: EffectResult, file_sync: Return, replace: Return, directory_sync: Return) -> CommitResult:
  match result:
    case IoError{phase}: CommitFailed{False{}, phase}
    case IoApplied{phase}: file_sync_result(effect(file_sync, phase, TempSynced{}), replace, directory_sync)

def commit(answers: Returns) -> CommitResult:
  match answers:
    case Returns{write, file_sync, replace, directory_sync}:
      write_result(effect(write, Old{}, TempWritten{}), file_sync, replace, directory_sync)

def phase(result: CommitResult) -> Phase:
  match result:
    case CommitReady{phase}: phase
    case CommitFailed{uncertain, phase}: phase

# A synced temp never competes with the authoritative image. Before directory
# sync a replacement may recover old or new; after sync only new may recover.
type Origin is Data:
  Previous{}
  Candidate{}

def crash_origin(phase: Phase, replacement_survives: Bool) -> Origin:
  match phase:
    case Old{}: Previous{}
    case TempWritten{}: Previous{}
    case TempSynced{}: Previous{}
    case Replaced{}:
      match replacement_survives:
        case False{}: Previous{}
        case True{}: Candidate{}
    case DirectorySynced{}: Candidate{}

def restored(origin: Origin, previous: D.State, candidate: D.State) -> D.State:
  match origin:
    case Previous{}: previous
    case Candidate{}: candidate

def recover(result: CommitResult, previous: D.State, candidate: D.State, replacement_survives: Bool) -> D.State:
  restored(crash_origin(phase(result), replacement_survives), previous, candidate)

# Both the state and response may be acknowledged only when all four calls
# returned success. A failure at/after replacement requires fatal closure.
def OutcomeCorrect(result: CommitResult, +previous: D.State, +candidate: D.State, +survives: Bool) -> Type:
  match result:
    case CommitReady{phase}:
      L.E<{phase == DirectorySynced{} : Phase},
        {recover(CommitReady{phase}, previous, candidate, survives) == candidate : D.State}>
    case CommitFailed{False{}, phase}:
      {recover(CommitFailed{False{}, phase}, previous, candidate, survives) == previous : D.State}
    case CommitFailed{True{}, phase}: Unit

law four_call_commit_classifies_every_return:
  for answers: Returns
  for +previous: D.State
  for +candidate: D.State
  for +survives: Bool
  OutcomeCorrect(commit(answers), previous, candidate, survives)
def four_call_commit_classifies_every_return(answers, previous, candidate, survives):
  match answers:
    case Returns{write, file_sync, replace, directory_sync}:
      match write:
        case FailedBefore{}: {==}
        case FailedAfter{}: {==}
        case Succeeded{}:
          match file_sync:
            case FailedBefore{}: {==}
            case FailedAfter{}: {==}
            case Succeeded{}:
              match replace:
                case FailedBefore{}: Unit{}
                case FailedAfter{}: Unit{}
                case Succeeded{}:
                  match directory_sync:
                    case FailedBefore{}: Unit{}
                    case FailedAfter{}: Unit{}
                    case Succeeded{}: L.Both{{==}, {==}}

def ReplacementCorrect(answer: Return, directory_sync: Return, +before: Phase, +after: Phase) -> Type:
  match answer:
    case Succeeded{}: Unit
    case FailedBefore{}: {replacement_result(effect(answer, before, after), directory_sync) == CommitFailed{True{}, before} : CommitResult}
    case FailedAfter{}: {replacement_result(effect(answer, before, after), directory_sync) == CommitFailed{True{}, after} : CommitResult}

law replacement_errors_are_never_safe_rollback:
  for +answer: Return
  for directory_sync: Return
  for +before: Phase
  for +after: Phase
  ReplacementCorrect(answer, directory_sync, before, after)
def replacement_errors_are_never_safe_rollback(answer, directory_sync, before, after):
  match answer:
    case Succeeded{}: Unit{}
    case FailedBefore{}: {==}
    case FailedAfter{}: {==}

# Source certificates establish candidate validity via the real Core.conclude;
# recovery does not take an arbitrary valid-candidate premise or a disk checksum
# as a proof. This covers loss before RAM publication or client delivery.
def origin_preserves_validity(~c: S.Configuration, origin: Origin, +previous: D.State, +record: History.Record,
  valid: R.Valid(c, previous), source: History.Origin(c, previous, record)) ->
  R.Valid(c, restored(origin, previous, History.next(previous, record))):
  match origin:
    case Previous{}: valid
    case Candidate{}: History.step_preserves_validity(c, previous, record, valid, source)

law every_crash_cut_recovers_a_certified_state:
  for ~c: S.Configuration
  for answers: Returns
  for +previous: D.State
  for +record: History.Record
  for survives: Bool
  for valid: R.Valid(c, previous)
  for source: History.Origin(c, previous, record)
  R.Valid(c, recover(commit(answers), previous, History.next(previous, record), survives))
def every_crash_cut_recovers_a_certified_state(c, answers, previous, record, survives, valid, source):
  origin_preserves_validity(c, crash_origin(phase(commit(answers)), survives), previous, record, valid, source)
