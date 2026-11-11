# Executed controller denial: exact mapping, bounded canonical frame and
# unchanged published root/last response/registry, independent of admission.
import Base
import ../contract/Data.bend as D
import ../contract/Logic.bend as L
import ../contract/Semantics.bend as S
import ../contract/Requirements.bend as R
import ../contract/Protocol.bend as P
import ../contract/HostErrors.bend as Errors
import ../contract/Theorems.bend as T
import ../src/Control.bend as Control
import ../src/ControlBridge.bend as Wire
import ../src/Codec.bend as Codec
import ../src/Messages.bend as Messages
import ./DispatchBridge.bend as Dispatch

def classified_reply(flag: Bool, c: S.Configuration, +root: D.State,
  +last: List<&2, U32>, +reg: Control.Registry,
  limits: {R.limits_all_valid(S.limits(c)) == True{} : Bool}) ->
  L.E<{Control.finish(Control.ControlDenied{Errors.classified(flag)}, root, last, reg) ==
      Control.ControlResult{root, last, reg, Control.ControlTransaction{S.response_error(Errors.classified(flag))}} : Control.Transition},
    L.E<T.Early(c, root, S.response_error(Errors.classified(flag))),
      {Wire.output(Control.finish(Control.ControlDenied{Errors.classified(flag)}, root, Nil{}, reg)) ==
        Wire.output(Control.ControlResult{root, last, reg,
          Control.ControlTransaction{S.response_error(Errors.classified(flag))}}) : List<&2, U32>}>>:
  match flag:
    case True{}: L.Both{{==}, L.Both{Dispatch.early(c, root, S.Certificate{}, limits, Unit{}), {==}}}
    case False{}: L.Both{{==}, L.Both{Dispatch.early(c, root, S.Failure{}, limits, Unit{}), {==}}}

def host_error_reply_theorem() -> T.HostErrorReplyTheorem():
  code => c => root => last => reg => limits => classified_reply(Errors.certificate(code), c, root, last, reg, limits)

# Native serialization is exactly the canonical public frame with a private
# Keep tag. The Early clause above also proves framing succeeds and is bounded.
law emitted_frame:
  for code: String
  for root: D.State
  for last: List<&2, U32>
  for reg: Control.Registry
  {Wire.output(Control.host_error(code, root, last, reg)) == Messages.error(Errors.status(code)) : List<&2, U32>}
def emitted_frame(code, root, last, reg): {==}

law other_codes_fail:
  for +code: String
  for absent: {Errors.certificate(code) == False{} : Bool}
  {Errors.status(code) == S.Failure{} : S.Status}
def other_codes_fail(code, absent):
  Equal.cong(Bool, S.Status, Errors.classified, Errors.certificate(code), False{}, absent)

law row_import:
  {Errors.status("IMPORT") == S.Certificate{} : S.Status}
def row_import(): {==}

law row_import_cycle:
  {Errors.status("IMPORT_CYCLE") == S.Certificate{} : S.Status}
def row_import_cycle(): {==}

law row_dependency:
  {Errors.status("DEPENDENCY") == S.Certificate{} : S.Status}
def row_dependency(): {==}

law row_parse:
  {Errors.status("PARSE") == S.Certificate{} : S.Status}
def row_parse(): {==}

law row_meta:
  {Errors.status("META") == S.Certificate{} : S.Status}
def row_meta(): {==}

law row_unsafe:
  {Errors.status("UNSAFE") == S.Certificate{} : S.Status}
def row_unsafe(): {==}

law row_foreign:
  {Errors.status("FOREIGN") == S.Certificate{} : S.Status}
def row_foreign(): {==}

law row_io:
  {Errors.status("IO") == S.Certificate{} : S.Status}
def row_io(): {==}

law row_open_law:
  {Errors.status("OPEN_LAW") == S.Certificate{} : S.Status}
def row_open_law(): {==}

law row_shadow:
  {Errors.status("SHADOW") == S.Certificate{} : S.Status}
def row_shadow(): {==}

law row_redefinition:
  {Errors.status("REDEFINITION") == S.Certificate{} : S.Status}
def row_redefinition(): {==}

law row_primary_check:
  {Errors.status("PRIMARY_CHECK") == S.Certificate{} : S.Status}
def row_primary_check(): {==}

law row_bendtt_check:
  {Errors.status("BENDTT_CHECK") == S.Certificate{} : S.Status}
def row_bendtt_check(): {==}

law row_target:
  {Errors.status("TARGET") == S.Certificate{} : S.Status}
def row_target(): {==}

law row_source_binding:
  {Errors.status("SOURCE_BINDING") == S.Certificate{} : S.Status}
def row_source_binding(): {==}

law row_host_capture:
  {Errors.status("HOST_CAPTURE") == S.Certificate{} : S.Status}
def row_host_capture(): {==}

law row_kernel_capture:
  {Errors.status("KERNEL_CAPTURE") == S.Certificate{} : S.Status}
def row_kernel_capture(): {==}

law row_handle:
  {Errors.status("HANDLE") == S.Failure{} : S.Status}
def row_handle(): {==}

law row_prepared_integrity:
  {Errors.status("PREPARED_INTEGRITY") == S.Failure{} : S.Status}
def row_prepared_integrity(): {==}

law row_host_compile:
  {Errors.status("HOST_COMPILE") == S.Failure{} : S.Status}
def row_host_compile(): {==}

law row_native:
  {Errors.status("NATIVE") == S.Failure{} : S.Status}
def row_native(): {==}


def prepared_host_errors_theorem() -> T.PreparedHostErrorsTheorem():
  root => last => reg => L.Both{{==}, {==}}

# As with WorkerBridge, keep the native template-configuration correspondence
# separate from the contract type, within the official BendTT supported scope.
law native_error_branch:
  for ~c: S.Configuration
  for code: String
  for root: D.State
  for reg: Control.Registry
  {Wire.run(c, Some{root}, Some{reg}, Codec.Decoded{D.VText{code}}, Nil{}) ==
    Wire.output(Control.host_error(code, root, Nil{}, reg)) : List<&2, U32>}
def native_error_branch(c, code, root, reg): {==}
