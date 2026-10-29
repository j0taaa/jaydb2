"""Private adapter for a checked service Module; never an admission bypass.

install_accounted(Module, incomplete_type=IncompleteIntegration) adds only the
new run_accounted method. The legacy method/layouts remain unchanged. The C
descriptor, not an editable report flag, authorizes this lowering. Test recipe
artifacts are rejected here. A real INCOMPLETE observation stays an integration
error outside the service's NativeFailure mapper.
"""
from __future__ import annotations
import ctypes as C
from dataclasses import dataclass
import time

from tools.service.abi import (RequestV3, ResultV3, Ns128, NativeFailure,
                               NativeOwnershipPending, addressable_ceiling)
from tools.service.memory import MemoryExcess
from tools.service.lifecycle import READY, CANCELLED, RETURNED

U64=C.c_uint64

class IncompleteIntegration(Exception):
    pass

class Host(C.Structure):
    _fields_=[('abi',U64),('scope',Ns128),('ceiling',Ns128),('deadline_ns',Ns128*3)]

class Snapshot(C.Structure):
    _fields_=[('abi',U64),*[(n,Ns128) for n in
        ['sequence','current','peak','monotonic_ns','peak_monotonic_ns','peak_sequence']],
        ('peak_flags',U64),('flags',U64)]

class Window(C.Structure):
    _fields_=[('abi',U64),('state',U64),('error',U64),('snapshot',Snapshot),
        *[(n,Ns128) for n in ['scope_id','begin_sequence','begin_monotonic_ns','end_sequence',
            'end_monotonic_ns','peak','peak_monotonic_ns','peak_sequence']],('peak_flags',U64)]

class Field(C.Structure):
    _fields_=[*[(n,U64) for n in ['status','length_checked','construction_started','constructed',
        'instrument_error','release_error','clock_error','backing_error','position','quantity',
        'tag','acquired_bytes','stores_completed']],('window',Window),('checked_ns',Ns128)]

class Result(C.Structure):
    _fields_=[('native',ResultV3),*[(n,U64) for n in ['decoder_calls','decoder_completed',
        'field_calls','field_completed','decode_id','constructor_id','site_id','logical_claims']],
        ('field',Field),('timing_flags',U64),('stage_started_ns',Ns128),
        ('decision_deadline_ns',Ns128),('returned_ns',Ns128)]

assert C.sizeof(Result)==656 and Result.decision_deadline_ns.offset==624


class EpochAuthority:
    """Retained raw C result and invocation receipt, independent of diagnostics."""
    __slots__=('result','owner','incomplete')

    def __init__(self,result,incomplete):
        self.result=result
        self.owner=None
        self.incomplete=incomplete

    def deadline_ns(self):
        owner=self.owner
        if owner is None or owner.call_state in (READY,CANCELLED):
            return None  # no invocation entered; setup epoch remains authoritative
        out=self.result
        if (owner.call_state!=RETURNED or owner.call_status!=out.native.status
                or out.timing_flags!=3 or out.native.stage>2):
            raise self.incomplete('Native original stage epoch is unavailable')
        # This scalar conversion can also fail. Database rechecks OUTSIDE its
        # mapper; failure there refuses completion rather than choosing setup.
        return out.decision_deadline_ns.natural()

class Descriptor(C.Structure):
    _fields_=[*[(n,U64) for n in ['abi','host_bytes','result_bytes','lowering_version',
        'recipe_version','term_bytes','artifact_flags']],('generated_c_sha256',C.c_char_p)]

class Progress(C.Structure):
    _fields_=[*[(n,U64) for n in ['abi','phase','decode_id','stage','wire_size','wire_copied',
        'cursor','scalar_start','utf8_consumed','utf8_value','utf8_needed']],('sampled_ns',Ns128)]

@dataclass(frozen=True)
class ProgressReceipt:
    phase:int
    decode_id:int
    stage:int
    wire_size:int
    wire_copied:int
    cursor:int
    scalar_start:int
    utf8_consumed:int
    utf8_value:int
    utf8_needed:int
    sampled_ns:int

def read_progress(module):
    """Optional independent ABI. The frozen 656-byte result is unchanged."""
    try:read=module.library.jaydb_native_progress_accounted_v1
    except AttributeError:return None
    read.argtypes,read.restype=[C.POINTER(Progress)],C.c_uint32
    out=Progress()
    if read(C.byref(out)) or out.abi!=1:return None
    return ProgressReceipt(*(getattr(out,name) for name in ['phase','decode_id','stage','wire_size',
        'wire_copied','cursor','scalar_start','utf8_consumed','utf8_value','utf8_needed']),out.sampled_ns.natural())

@dataclass(frozen=True)
class Receipt:
    stage: int
    stage_started_ns: int
    decision_deadline_ns: int
    returned_ns: int
    timing_flags: int
    decoder_calls: int
    decoder_completed: int
    field_calls: int
    field_completed: int
    logical_claims: int
    decode_id: int
    constructor_id: int
    site_id: int
    field_status: int
    wire_position: int
    wire_quantity: int
    wire_tag: int
    construction_started: bool
    constructed: bool
    stores_completed: int
    # Exact private receipt bytes preserve the scoped snapshot and any partial
    # stores, without reinterpreting it as an independently certified witness.
    raw: bytes

    @classmethod
    def read(cls,r):
        f=r.field
        return cls(r.native.stage,r.stage_started_ns.natural(),r.decision_deadline_ns.natural(),
            r.returned_ns.natural(),r.timing_flags,r.decoder_calls,r.decoder_completed,
            r.field_calls,r.field_completed,r.logical_claims,r.decode_id,r.constructor_id,r.site_id,
            f.status,f.position,f.quantity,f.tag,bool(f.construction_started),bool(f.constructed),
            f.stores_completed,bytes(r))

def _nat(n,*,positive=False):
    if type(n) is not int or n<0 or (positive and not n):
        raise ValueError('Expected an exact '+('positive ' if positive else '')+'Nat')
    v=min(n,2**128-1)
    return Ns128(v&((1<<64)-1),v>>64)

def _bind(module,incomplete):
    lib=module.library
    if lib is None:raise RuntimeError('Module closed')
    try:
        describe=lib.jaydb_native_describe_accounted_v3
        run=lib.jaydb_native_run_accounted_v3
    except AttributeError as exc:
        raise incomplete('Native artifact has no private accounted ABI') from exc
    describe.argtypes,describe.restype=[],C.POINTER(Descriptor)
    d=describe().contents
    if (d.abi!=1 or d.host_bytes!=C.sizeof(Host) or d.result_bytes!=C.sizeof(Result)
            or d.lowering_version!=1 or d.recipe_version!=3 or d.term_bytes!=24 or d.artifact_flags):
        raise incomplete('Native artifact lacks the verified production decoder lowering')
    # Compare two descriptions compiled into this SAME loaded DSO. JSON cannot
    # enable lowering, replace an old artifact, or authorize a fixture.
    v3=lib.jaydb_native_describe_v3().contents
    if d.generated_c_sha256!=v3.generated_c_sha256:
        raise incomplete('Native accounted source binding mismatch')
    if not getattr(module,'automatic_terms',False) or not getattr(module,'automatic_native',False):
        raise incomplete('Accounted mode requires the automatic V3 stack interfaces')
    run.argtypes=[C.POINTER(RequestV3),C.POINTER(Host),C.POINTER(Result)]
    run.restype=C.c_uint32
    return run

def install_accounted(module_type,*,incomplete_type=IncompleteIntegration):
    """Attach the additional interface. Call before constructing service modules.

    Host integration supplies its own IncompleteIntegration class so coverage
    refusals cannot fall through its public failure mapper. No counter library
    is loaded here; the inherited observer owns the raw syscall protocol.
    """
    def run_accounted(self,data:bytes,*,accounting,capacity:int,memory:int,timeout_ns:int,
            execution_ns=None,preparation_ns=None,setup_deadline_ns=None,
            execution_deadline_ns=None,preparation_deadline_ns=None):
        self.last_accounted_epoch=None
        self.last_accounted_receipt=None
        self.last_accounted_progress=None
        self.preparation_deadline=None
        self.decision_deadline_ns=None
        self.stage_started_ns=None
        run=_bind(self,incomplete_type) # fail BEFORE invoking any decoder
        scope=accounting.scope
        if type(scope) is not int or not 0<scope<2**128:
            raise ValueError('An exact active accounting scope is required')
        _nat(accounting.ceiling)
        _nat(memory) # compatibility option, NOT the measured ceiling or a quota
        if setup_deadline_ns is None:
            raise incomplete_type('Accounted calls require the original absolute setup deadline')
        setup=_nat(setup_deadline_ns)
        deadlines=(Ns128*3)(setup,_nat(0 if execution_deadline_ns is None else execution_deadline_ns),
            _nat(0 if preparation_deadline_ns is None else preparation_deadline_ns))
        host=Host(1,_nat(scope),_nat(accounting.ceiling),deadlines)
        # The same raw counter/scope must already be owned by the host. poll is
        # a refusal check only; every field still obtains a FINAL held snapshot.
        try:accounting.poll()
        except MemoryExcess:raise
        except Exception as exc:
            raise incomplete_type('Accounted scope is not ACTIVE and complete') from exc
        inp=(C.c_uint8*max(1,len(data))).from_buffer_copy(data or b'\0')
        limit=addressable_ceiling(capacity)
        req=RequestV3(3,1,inp,len(data),limit,0,0,0,_nat(timeout_ns,positive=True),
            _nat(timeout_ns if execution_ns is None else execution_ns,positive=True),
            _nat(timeout_ns if preparation_ns is None else preparation_ns,positive=True))
        out=Result()
        self.last_accounted_epoch=EpochAuthority(out,incomplete_type)
        def error(exc):
            exc.accounted_receipt=self.last_accounted_receipt
            exc.accounted_progress=self.last_accounted_progress
            if self.last_accounted_receipt and self.last_accounted_receipt.timing_flags&1:
                exc.decision_deadline_ns=self.last_accounted_receipt.decision_deadline_ns
                exc.stage_started_ns=self.last_accounted_receipt.stage_started_ns
            return exc
        failure=None
        try:
            owner=self._prepare_output(out.native,result_owner=out)
            self.last_accounted_epoch.owner=owner
            status=owner.invoke(run,C.byref(req),C.byref(host),C.byref(out))
            self.last_accounted_progress=read_progress(self) if out.timing_flags&1 else None
            receipt=self.last_accounted_receipt=Receipt.read(out)
            if receipt.timing_flags&1:
                self.decision_deadline_ns=receipt.decision_deadline_ns
                self.stage_started_ns=receipt.stage_started_ns
                if out.native.stage==2:self.preparation_deadline=receipt.decision_deadline_ns
            r=out.native
            if (status!=r.status or r.stage>2 or r.reserved or r.output_len>limit
                    or r.output_len>r.output_capacity or (r.output_len and not r.output)):
                raise error(incomplete_type('Invalid private native result'))
            if receipt.timing_flags!=3:
                raise error(incomplete_type('Native call lacks observed original stage epochs'))
            if status:
                if r.lease or r.output_len or r.output_capacity or r.output:
                    raise error(incomplete_type('Failed native call retained output'))
                if r.runtime_code==0x4649454c and r.status!=3:
                    if receipt.field_status==1:
                        # Only MemoryWindow's complete, scoped, strict witness
                        # can enter the host's memory mapping. No local status
                        # or synthetic byte count becomes a public limit.
                        try:accounting.poll()
                        except MemoryExcess as exc:raise error(exc)
                        except Exception as exc:
                            raise error(incomplete_type('Accounted memory witness unavailable')) from exc
                    raise error(incomplete_type('Native field boundary refused coverage/instrumentation'))
                raise error(NativeFailure(status,r.runtime_code,r.stage))
            if not r.lease or receipt.timing_flags!=3:
                raise error(incomplete_type('Native success lacks lease/original stage epochs'))
            value=C.string_at(r.output,r.output_len) if r.output_len else b''
        except BaseException as exc:
            failure=exc
            raise
        finally:
            # ctypes may deliver an asynchronous Python exception after C has
            # committed its receipt. Preserve it and release the byte lease.
            try:
                self.last_accounted_receipt=Receipt.read(out)
                self.last_accounted_progress=read_progress(self) if out.timing_flags&1 else None
                if self.last_accounted_receipt.timing_flags&1:
                    self.decision_deadline_ns=self.last_accounted_receipt.decision_deadline_ns
                    self.stage_started_ns=self.last_accounted_receipt.stage_started_ns
                    if out.native.stage==2:self.preparation_deadline=self.decision_deadline_ns
                if failure is not None:error(failure)
            except BaseException as diagnostic:
                # An auxiliary wrapper failure must not replace an already
                # known native/host cause. Raw epoch authority is independent.
                if failure is None:
                    failure=diagnostic
                    raise
            finally:
                # Receipt/progress wrappers can themselves allocate or raise.
                # Output ownership is independent of diagnostic extraction.
                try:
                    self._release_outputs()
                except BaseException as cleanup:
                    if failure is not None and not isinstance(cleanup,NativeOwnershipPending):
                        raise failure from cleanup
                    raise
        if time.monotonic_ns()>=receipt.decision_deadline_ns:
            raise error(NativeFailure(3,0,receipt.stage))
        if execution_ns is not None and receipt.stage!=2:
            raise error(incomplete_type('Execution ended without preparation transition'))
        return value
    module_type.run_accounted=run_accounted
    return module_type
