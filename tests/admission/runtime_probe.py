"""Execute gate-emitted C through the actual private CPU1 native module."""
import ctypes as C
import importlib.util
import json
import os
from pathlib import Path
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).resolve().parents[2]
spec = importlib.util.spec_from_file_location('admission_native_build', ROOT / 'tools/native/build.py')
build = importlib.util.module_from_spec(spec)
spec.loader.exec_module(build)


class Request(C.Structure):
    _fields_ = [('abi_version', C.c_uint32), ('flags', C.c_uint32), ('input', C.c_void_p),
                ('input_len', C.c_uint64), ('output', C.c_void_p), ('output_capacity', C.c_uint64),
                ('memory_bytes', C.c_uint64), ('timeout_ns', C.c_uint64),
                ('term_stack_bytes', C.c_uint64), ('native_stack_bytes', C.c_uint64)]


class Result(C.Structure):
    _fields_ = [('status', C.c_uint32), ('runtime_code', C.c_uint32), ('output_len', C.c_uint64),
                ('elapsed_ns', C.c_uint64), ('charged_bytes', C.c_uint64)]


class RequestV2(C.Structure):
    _fields_ = [('base', Request), ('execution_timeout_ns', C.c_uint64), ('preparation_timeout_ns', C.c_uint64)]


class ResultV2(C.Structure):
    _fields_ = [('base', Result), ('stage', C.c_uint32), ('reserved', C.c_uint32),
                ('setup_ns', C.c_uint64), ('execution_ns', C.c_uint64), ('preparation_ns', C.c_uint64)]


c_file, module_file, mode = sys.argv[1:]
loop = mode == 'loop'
bindings = dict(input_cid='CID_Native_read', output_cid='CID_Native_write')
if loop:
    bindings = dict(input_cid=None, output_cid=None, loop_cid='CID_Native_loop',
                    continue_cid='CID_Native_Continuar', prepare_cid='CID_Native_Preparar',
                    finish_cid='CID_Native_Encerrar', inconsistent_cid='CID_Native_Inconsistente',
                    enter_cid='CID_Native_enter')
build.build_module(c_file, module_file, **bindings)
library = C.CDLL(str(module_file), mode=os.RTLD_LOCAL | os.RTLD_NOW)
input_ = C.create_string_buffer(bytes([0, 255, 128, 65]))
output = C.create_string_buffer(4096)
request = Request(2 if loop else 1, 1, C.addressof(input_), 4, C.addressof(output), 4096,
                  64 << 20, 3_000_000_000, 1 << 20, 1 << 20)
if loop:
    req2 = RequestV2(request, 3_000_000_000, 3_000_000_000)
    result = ResultV2()
    library.jaydb_native_run_v2.argtypes = [C.POINTER(RequestV2), C.POINTER(ResultV2)]
    library.jaydb_native_run_v2.restype = C.c_uint32
    status = library.jaydb_native_run_v2(C.byref(req2), C.byref(result))
    print(json.dumps(dict(status=status, output=list(output.raw[:result.base.output_len]), stage=result.stage)))
else:
    result = Result()
    library.jaydb_native_run_v1.argtypes = [C.POINTER(Request), C.POINTER(Result)]
    library.jaydb_native_run_v1.restype = C.c_uint32
    status = library.jaydb_native_run_v1(C.byref(request), C.byref(result))
    print(json.dumps(dict(status=status, output=list(output.raw[:result.output_len]))))
