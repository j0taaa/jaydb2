#!/usr/bin/env python3
"""Compile trusted, already emitted same-Book C to the native CPU1 ABI6.

This adapter is not admission. It does not parse Bend, replace the Codec, or
accept untrusted C. The caller supplies C emitted from its admitted Book.
No helper deadlines, physical quotas, coverage callbacks or observers exist.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[2]
NATIVE = ROOT / 'native'
CLANG = '/usr/bin/clang-19'

class BuildError(RuntimeError):
    def __init__(self, category, message):
        self.category = category
        super().__init__(message)

def between(source, start, end, replacement):
    if source.count(start) != 1 or source.count(end) != 1:
        raise BuildError('runtime_layout', f'Pinned runtime marker mismatch: {start!r}')
    a, b = source.index(start), source.index(end)
    if a >= b:
        raise BuildError('runtime_layout', 'Runtime sections out of order')
    return source[:a] + replacement + '\n\n' + source[b:]


def heap_accessors(source):
    """Rewrite pinned C heap lvalues, including nested indices, not the Book.

    Comments/string literals are skipped. Term-stack/local/static-image arrays
    remain ordinary C arrays. The only active heap bases are e.mem/H/CORPUS.
    Refcount atomics use the same accessor through their pinned a32_at macro.
    """
    pattern = re.compile(r'//[^\n]*|/\*.*?\*/|"(?:\\.|[^"\\])*"|\'(?:\\.|[^\'\\])*\'|\b(?:e\.mem|H|CORPUS)\s*\[', re.S)
    pieces, at = [], 0
    for match in pattern.finditer(source):
        if match.start() < at or not match[0].endswith('['):
            continue
        depth, end = 1, match.end()
        while end < len(source) and depth:
            if source[end] == '[': depth += 1
            elif source[end] == ']': depth -= 1
            end += 1
        if depth:
            raise BuildError('runtime_layout', 'Unclosed pinned heap index')
        base = match[0][:-1].strip()
        index = heap_accessors(source[match.end():end - 1])
        pieces.extend([source[at:match.start()], f'(*jaydb_heap_cell({base}, ({index})))'])
        at = end
    pieces.append(source[at:])
    return ''.join(pieces)


def prepare_source(emitted: str, input_cid: str | None, output_cid: str | None, *,
                   loop_cid=None, state_cid=None, continue_cid=None, finish_cid=None,
                   inconsistent_cid=None, prepare_cid=None, enter_cid=None):
    generic = bool(re.match(r'// JAYDB_NATIVE_GENERIC_V1 [0-9a-f]{64}\n', emitted))
    if not generic:
        raise BuildError('specialized_backend', 'Expected generic C emitted from the same checked Book')
    if 'JAYDB_NATIVE_ACCOUNTED_' in emitted or 'jaydb_codec_accounted(' in emitted:
        raise BuildError('runtime_layout', 'Accounted decoder lowering is outside the simple runtime')
    for marker in ('COMPACT_NAT', 'WIDE_IDS', 'WORD_ARITY', 'ADDRESS_WORD'):
        if f'// JAYDB_NATIVE_{marker}_V1\n' not in emitted:
            raise BuildError('runtime_layout', 'Expected current generic machine-word representation')
    loop_ids = (loop_cid, continue_cid, finish_cid, inconsistent_cid)
    if any(loop_ids) and not all(loop_ids):
        raise BuildError('effect_binding', 'Loop needs effect/continue/finish/inconsistent CIDs')
    if (prepare_cid or state_cid) and not loop_cid:
        raise BuildError('effect_binding', 'Prepare/state CID needs the loop bindings')
    ids = [x for x in (input_cid, output_cid, *loop_ids, state_cid, prepare_cid, enter_cid) if x is not None]
    for cid in ids:
        if not re.fullmatch(r'CID_[A-Za-z0-9_]+', cid) or not re.search(r'^#define ' + cid + r' \d+$', emitted, re.M):
            raise BuildError('effect_binding', f'Missing effect constructor {cid}')
    if len(ids) != len(set(ids)):
        raise BuildError('effect_binding', 'Distinct constructor bindings required')
    wide_ids = '// JAYDB_NATIVE_WIDE_IDS_V1\n' in emitted
    word_arity = '// JAYDB_NATIVE_WORD_ARITY_V1\n' in emitted
    address_word = '// JAYDB_NATIVE_ADDRESS_WORD_V1\n' in emitted
    if word_arity and not wide_ids:
        raise BuildError('runtime_layout', 'Word arities require the wide Term carrier')
    if address_word and not word_arity:
        raise BuildError('runtime_layout', 'Address-word Terms require word arities')
    for symbol, value in re.findall(r'^#define ([CF]ID_\w+) (\d+)$', emitted, re.M):
        if not wide_ids and int(value) > 65535:
            raise BuildError('id_representation', f'{symbol} exceeds the actual 16-bit runtime ID representation')
    # Retain the data representation, constructor primitives, and actual emitted
    # segments. Remove ALL scheduling, IO, signal, main and foreign effect code.
    # seq=1 selects the official sequential path of parallel lets.
    if emitted.count('// Monk\n// ====') != 1:
        raise BuildError('runtime_layout', 'Expected pinned Bend 2.0.39 runtime')
    source = emitted.split('// Monk\n// ====')[0]
    source = '#define _GNU_SOURCE\n#include "simple.h"\n' + source
    if wide_ids:
        source = source.replace('typedef u64 Term;', 'typedef __uint128_t Term;')
        source = source.replace('DEV u64* mem;', 'DEV Term* mem;')
        source = source.replace('static u64*    CORPUS;', 'static Term*   CORPUS;')
        source = source.replace('DEV u64* H', 'DEV Term* H')
        source = source.replace('CONSTV u64 STAT_IMG[]', 'CONSTV Term STAT_IMG[]')
        source = between(source, '#define term_make(tag, aux, loc)', 'INLINE bool term_triv(',
                         (NATIVE / 'terms.inc.c').read_text())
        # Cast BEFORE complementing, otherwise a u64 mask loses the metadata
        # word when it is promoted to Term for refcount wrapping/unwrapping.
        source = source.replace('~LOC_MASK', '~(Term)LOC_MASK')
        source = source.replace('~(RFC_BIT | LOC_MASK)', '~(Term)(RFC_BIT | LOC_MASK)')
        source = source.replace('(u32)term_aux(', '(u64)term_aux(')
        source = source.replace('(u32)STK(0)', '(u64)STK(0)')
        source = re.sub(r'\bu32(\s+)(aux|f|wf|fid)(\s*=.*?term_aux\()', r'u64\1\2\3', source)
        source = source.replace('Env e, u32 fid,', 'Env e, u64 fid,')
        # preserve_none cannot carry an arbitrary bank of scalar Term arguments
        # (128-bit returns also consume registers on x86_64). Pass one pointer
        # instead. The bank occupies its own stable allocation, once
        # per evaluator, and every emitted segment reads its input locals before
        # writing the next call's bank. musttail dispatch still has fixed arity.
        bank = re.search(r'^#define WL_BANK Term ([^;]+);$', source, re.M)
        if not bank:
            raise BuildError('runtime_layout', 'Expected scalar register bank from pinned emitter')
        bank_words = max(map(int, re.findall(r'\br(\d+)\b', bank[1]))) + 1
        source = source[:bank.start()] + '#define WL_BANK' + source[bank.end():]
        source = re.sub(r'^#define WL_SIG .*$',
                        '#define WL_SIG Env e, DEV Term* sp, u32 seq, u32 rn, Term* jaydb_regs', source, flags=re.M)
        source = re.sub(r'^#define WL_ALL .*$', '#define WL_ALL e, sp, seq, rn, jaydb_regs', source, flags=re.M)
        aliases = '\n'.join(f'#define r{i} jaydb_regs[{i}]' for i in range(bank_words))
        # spin_N uses independent scalar parameters also named r0, r1, ... .
        # Its definitions precede Work; aliases belong only to the evaluator.
        source = source.replace('// Work\n// ====',
            f'#define JAYDB_REGISTER_WORDS {bank_words}\n{aliases}\n\n// Work\n// ====')
        entry = 'static Term work_loop(Env e, DEV Term* sp, Term t, u32 seq) {\n  WL_BANK'
        if source.count(entry) != 1:
            raise BuildError('runtime_layout', 'Expected evaluator entry for register bank')
        source = source.replace(entry, '''static Term work_loop(Env e, DEV Term* sp, Term t, u32 seq) {
  Term *jaydb_regs = sp;
  sp = jaydb_stack_at(sp, JAYDB_REGISTER_WORDS, true);
  WL_BANK''')
    source = source.replace('typedef u64 Term;', 'typedef u64 Term;\nstatic Term *jaydb_stack_at(Term*, int64_t, bool);')
    if wide_ids:
        source = source.replace('typedef __uint128_t Term;',
            'typedef __uint128_t Term;\nstatic Term *jaydb_stack_at(Term*, int64_t, bool);')
    source = source.replace('#define TAG_ARR 6ull', '#define TAG_ARR 6ull\n#define TAG_NAT_SMALL 7ull\n#define TAG_NAT_BIG 8ull')
    source = source.replace('return term_tag(t) <= TAG_PAK || t == TERM_HOLE',
        'return term_tag(t) == TAG_NAT_SMALL || term_tag(t) <= TAG_PAK || t == TERM_HOLE')
    source = source.replace('if (term_tag(t) != TAG_CTR || term_rfc(t))',
        'if ((term_tag(t) != TAG_CTR && term_tag(t) != TAG_NAT_BIG) || term_rfc(t))')
    source = source.replace('FAR void term_drop(Env e, Term t) {',
        'static void jaydb_nat_free(Env, Term);\nFAR void term_drop(Env e, Term t) {')
    source = source.replace('if (tag == TAG_BUF) {\n        heap_free',
        'if (tag == TAG_NAT_BIG) {\n        jaydb_nat_free(e, t);\n      } else if (tag == TAG_BUF) {\n        heap_free')
    source = source.replace('#define STK(I)    sp[(long)(I) * LANE_STEP]', '#define STK(I) (*jaydb_stack_at(sp, (int64_t)(I), false))')
    source = source.replace('sp -= LANE_STEP;', 'sp = jaydb_stack_at(sp, -1, true);')
    source = source.replace('#define WL_POPN(N)  sp -= (N) * LANE_STEP', '#define WL_POPN(N) sp = jaydb_stack_at(sp, -(int64_t)(N), true)')
    source = source.replace('#define WL_PUSHN(N) sp += (N) * LANE_STEP', '#define WL_PUSHN(N) sp = jaydb_stack_at(sp, (int64_t)(N), true)')
    # Ring and device stacks are unreachable in CPU1. Only static constructors
    # and the root frame need a prefix. No 8-GiB reservation remains.
    source = re.sub(r'^#define STAT_OFF .*$', '#define STAT_OFF 1024ull', source, flags=re.M)
    source = between(source, 'static const char* ERR_TEXT[]', '#define err_seen(H)', '''
OUTLINE void err_fail(const char *message) { (void)message; jaydb_abort(JAYDB_RUNTIME, 0); }
static void err_post(Term *H, u32 code) {
  (void)H;
  uint32_t status = code == ERR_NATS ? JAYDB_NAT_REPRESENTATION
    : code == ERR_ARRS ? JAYDB_ARRAY_REPRESENTATION
    : code == ERR_CNTS ? JAYDB_REFCOUNT_REPRESENTATION : JAYDB_RUNTIME;
  jaydb_abort(status, code);
}
#endif
''')
    source = between(source, '// Bank\n// ====', '// Term\n// ====',
        (NATIVE / 'simple_arena.inc.c').read_text() + '\n' + (NATIVE / 'simple_stack.inc.c').read_text()
        + '\n' + (NATIVE / 'simple_heap.inc.c').read_text())
    # CPU1 saturating refcounts. RFC_CNT denotes immortal until arena unload.
    source = between(source, 'INLINE void rfc_bump(', 'INLINE Term term_keep(', '''
INLINE void rfc_bump(Env e, u64 r, u32 k) {
  u64 value = e.mem[r], count = value & RFC_CNT;
  u64 next = count + (u64)k;
  e.mem[r] = (value & ~(u64)RFC_CNT) | (next >= RFC_CNT ? RFC_CNT : next);
}
''')
    source = source.replace('if ((a32_sub_rel(p, 1) & RFC_CNT) != 1)',
                            'if ((a32_load(p) & RFC_CNT) == RFC_CNT || (a32_sub_rel(p, 1) & RFC_CNT) != 1)')
    if word_arity:
        source = source.replace('typedef struct { u8 ar, resw, bangs, nofk; } Fid;',
            'typedef struct { u64 ar, resw; u8 bangs, nofk; } Fid;')
        source = source.replace('typedef struct { u8 ar, hot; u16 spine; } Cid;',
            'typedef struct { u64 ar; u8 hot; u64 spine; } Cid;')
        source = between(source, 'FAR void term_drop(Env e, Term t) {', 'INLINE void term_sink(',
                         (NATIVE / 'drop.inc.c').read_text())
        source = source.replace('ctr_take(Env e, Term t, u32 n,', 'ctr_take(Env e, Term t, u64 n,')
        source = source.replace('span_fade(Env e, Term t, u64 src, u32 n)',
                                'span_fade(Env e, Term t, u64 src, u64 n)')
        source = source.replace('Env e, u64 fid, Term cont, u32 idx, u32 rem',
                                'Env e, u64 fid, Term cont, u64 idx, u64 rem')
        source = re.sub(r'\bu32(\s+)(ar|war|rw|wn)(\s*=.*fid_(?:arity|resw)\()', r'u64\1\2\3', source)
        source = source.replace('Term cont, u32 idx, THR Term* v, u32 n',
                                'Term cont, u64 idx, THR Term* v, u32 n')
        source = source.replace('for (u32 j = 0; j < n;', 'for (u64 j = 0; j < n;')
        source = source.replace('for (u32 i = 0; rem && i < ar;', 'for (u64 i = 0; rem && i < ar;')
        source = source.replace('for (u32 i = 0; i < ar;', 'for (u64 i = 0; i < ar;')
        source = source.replace('for (u32 wi = 0;', 'for (u64 wi = 0;')
        source = source.replace('((u64)idx << 32) | rem', '((Term)idx << 64) | rem')
        source = source.replace('(e.mem[wtl + 1] >> 32) & 0xFFFF', '(u64)(e.mem[wtl + 1] >> 64)')
        source = source.replace('u32  idx  = (u32)STK(1);', 'u64  idx  = (u64)STK(1);')
        source = between(source, '  DEV u32* c = a32_at(H, task_tail(cont) + 1);',
                         '\nINLINE void task_deal(', '''
  u64 tail = task_tail(cont) + 1, remaining = (u64)H[tail];
  H[tail] -= 1; /* CPU1: no other evaluator writes this continuation. */
  return remaining == 1 ? cont : 0;
}
''')
    if address_word:
        source = source.replace('typedef __uint128_t Term;', 'typedef unsigned _BitInt(192) Term;')
        source = source.replace('#define LOC_MASK  ((1ull << 40) - 1)', '#define LOC_MASK UINT64_MAX')
        source = source.replace('#define RFC_BIT   (1ull << 63)', '#define RFC_BIT ((Term)1 << 191)')
        source = between(source, '#define term_make(tag, aux, loc)', 'INLINE bool term_triv(',
                         (NATIVE / 'terms_address.inc.c').read_text())
        source = source.replace('(term_loc(t) << 24) | cnt', '((Term)term_loc(t) << 64) | cnt')
        source = source.replace('w64_load(&H[term_loc(t)]) >> 24', '(u64)(H[term_loc(t)] >> 64)')
        source = source.replace('u64 value = e.mem[r], count = value & RFC_CNT;',
                                'Term value = e.mem[r]; u64 count = (u64)value & RFC_CNT;')
        source = source.replace('value & ~(u64)RFC_CNT', 'value & ~(Term)RFC_CNT')
        source = source.replace('(H[r] >> 24)', '(H[r] >> 64)')
        source = source.replace('((Term)live << 80)', '((Term)live << 124)')
        source = source.replace('((Term)cls << 120)', '((Term)cls << 184)')
        source = source.replace('(cur >> 40)', '(cur >> 64)')
        source = source.replace('(cur >> 80)', '(cur >> 124)')
        source = source.replace('(cur >> 120)', '(cur >> 184)')
        source = source.replace('i = (u64)(cur >> 64) & LOC_MASK', 'i = (u64)(cur >> 64) & JAYDB_GC_COUNT_MASK')
        source = source.replace('n = (u64)(cur >> 124) & LOC_MASK', 'n = (u64)(cur >> 124) & JAYDB_GC_COUNT_MASK')
        source = source.replace('cur += (Term)1 << 40', 'cur += (Term)1 << 64')
        # Clang19 musttail with a wide scalar sret return fails to forward the
        # return buffer (a standalone differential probe reproduces it). Pass
        # an explicit result pointer instead. Segment calls remain musttail,
        # fixed-arity and preserve_none; their C return type is now void.
        source = source.replace('#define WL_FN      FAR PRESERVE(preserve_none) Term',
                                '#define WL_FN      FAR PRESERVE(preserve_none) void')
        source = source.replace('typedef Term (PRESERVE(preserve_none) *WlFn)',
                                'typedef void (PRESERVE(preserve_none) *WlFn)')
        source = source.replace('#define WL_SIG Env e, DEV Term* sp, u32 seq, u32 rn, Term* jaydb_regs',
                                '#define WL_SIG Env e, DEV Term* sp, u32 seq, u32 rn, Term* jaydb_regs, Term* jaydb_out')
        source = source.replace('#define WL_ALL e, sp, seq, rn, jaydb_regs',
                                '#define WL_ALL e, sp, seq, rn, jaydb_regs, jaydb_out')
        source = source.replace('return WL_FID_ENTER(WL_ALL);',
            'Term value; Term *jaydb_out = &value; WL_FID_ENTER(WL_ALL); return value;')
        source = source.replace('// Work\n// ====',
                                '#undef WL_ROOM\n#define WL_ROOM(N)\n\n// Work\n// ====')
        a, b = source.split('// Segments\n// ========')
        b = re.sub(r'\breturn ([^;\n]+);', r'{ *jaydb_out = \1; return; }', b)
        source = a + '// Segments\n// ========' + b
    if wide_ids:
        # Every segment carries a logical continuation-stack index. Its bank
        # pointer remains stable in a separate Book-sized allocation in auto
        # mode; continuation depth never requires a contiguous reservation.
        source = source.replace('Env e, DEV Term* sp, u32 seq, u32 rn, Term* jaydb_regs',
            'Env e, u64 sp, u32 seq, u32 rn, Term* jaydb_regs')
        source = source.replace('work_loop(Env e, DEV Term* sp, Term t, u32 seq)',
            'work_loop(Env e, Term* jaydb_regs, Term t, u32 seq)')
        source = source.replace('  Term *jaydb_regs = sp;\n  sp = jaydb_stack_at(sp, JAYDB_REGISTER_WORDS, true);',
            '  u64 sp = jaydb_stack_move(0, JAYDB_REGISTER_WORDS, true);')
        source = source.replace('(*jaydb_stack_at(sp, (int64_t)(I), false))',
            '(*jaydb_term_cell(&jaydb_term_stack, jaydb_stack_move(sp, (int64_t)(I), false)))')
        source = re.sub(r'jaydb_stack_at\(sp, ([^\n;]*?), true\)', r'jaydb_stack_move(sp, \1, true)', source)
    # F32.read consumes arbitrary Strings in the covered streaming parser.
    # Its final libc conversion receives a bounded, rounding-equivalent token.
    source += '\n' + (NATIVE / 'text.inc.c').read_text() + '\n' + (NATIVE / 'numeric.inc.c').read_text()
    image_decl = 'CONSTV Term STAT_IMG[]' if wide_ids else 'CONSTV u64 STAT_IMG[]'
    source = source.replace(image_decl, (NATIVE / 'nat.inc.c').read_text() + '\n' + image_decl)
    if generic and re.search(r'\b(nat_chk|nat_mul|blk_new|blk_half|blk_node)\(', source.split('// Segments\n')[1]):
        raise BuildError('generic_mismatch', 'A specialized Nat/Array operation survived generic emission')
    if '// JAYDB_NATIVE_COMPACT_NAT_V1\n' in emitted and re.search(r'\bterm_(?:pak|ctr)\(CID_(?:Zero|Succ)\b', source):
        raise BuildError('generic_mismatch', 'A unary Nat constructor survived compact emission')
    source += '\n' + (NATIVE / 'simple_module.inc.c').read_text()
    source = source.replace('static Term *jaydb_stack_at(Term*, int64_t, bool);',
        'static Term *jaydb_stack_at(Term*, int64_t, bool);\nstatic Term *jaydb_heap_cell(Term*, u64);\n'
        'struct jaydb_term_store;\nstatic Term *jaydb_term_cell(struct jaydb_term_store*, u64);')
    atomic_macro = '#define a32_at(H, word)     ((DEV u32*)&(H)[word])'
    if source.count(atomic_macro) != 1:
        raise BuildError('runtime_layout', 'Expected pinned heap atomic accessor')
    source = source.replace(atomic_macro, '#define a32_at(H, word) ((DEV u32*)jaydb_heap_cell((H), (word)))')
    source = source.replace('(DEV u32a*)(H + loc) + i', '(DEV u32a*)jaydb_heap_cell(H, loc) + i')
    source = source.replace('JAYDB_MEMORY', 'JAYDB_SYSTEM')
    return (heap_accessors(source), generic)


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def build_module(c_file, output, *, input_cid='CID_Native_read', output_cid='CID_Native_write',
                 loop_cid=None, state_cid=None, continue_cid=None, finish_cid=None,
                 inconsistent_cid=None, prepare_cid=None, enter_cid=None):
    if platform.system() != 'Linux' or platform.machine() != 'x86_64' or os.sysconf('SC_PAGE_SIZE') != 4096:
        raise BuildError('platform', 'ABI6 targets Linux x86_64 with 4096-byte pages')
    c_file, output = Path(c_file).resolve(), Path(output).resolve()
    emitted = c_file.read_text()
    source_hash = hashlib.sha256(emitted.encode()).hexdigest()
    bindings = dict(input_cid=input_cid, output_cid=output_cid, loop_cid=loop_cid,
        state_cid=state_cid, continue_cid=continue_cid, finish_cid=finish_cid,
        inconsistent_cid=inconsistent_cid, prepare_cid=prepare_cid, enter_cid=enter_cid)
    source, _ = prepare_source(emitted, **bindings)
    support_names = ['simple.h', 'simple_arena.inc.c', 'simple_stack.inc.c',
        'simple_heap.inc.c', 'simple_module.inc.c', 'terms.inc.c', 'terms_address.inc.c',
        'drop.inc.c', 'nat.inc.c', 'text.inc.c', 'numeric.inc.c', 'f32_parse.inc.c']
    support = [NATIVE/name for name in support_names] + [Path(__file__).resolve()]
    source_hashes = {str(path.relative_to(ROOT)): digest(path) for path in support}
    defines = [f'-DJAYDB_SOURCE_HASH="{source_hash}"',
        f'-DJAYDB_INPUT_CID={input_cid or "0"}', f'-DJAYDB_OUTPUT_CID={output_cid or "0"}',
        f'-DJAYDB_INPUT_ENABLED={int(input_cid is not None)}',
        f'-DJAYDB_OUTPUT_ENABLED={int(output_cid is not None)}']
    for key in ('loop', 'state', 'prepare', 'enter'):
        defines.append(f'-DJAYDB_{key.upper()}_ENABLED={int(bindings[key+"_cid"] is not None)}')
    for key in ('loop', 'state', 'continue', 'finish', 'inconsistent', 'prepare', 'enter'):
        if bindings[key+'_cid']:
            defines.append(f'-DJAYDB_{key.upper()}_CID={bindings[key+"_cid"]}')
    flags = ['--no-default-config', '-std=gnu11', '-O2', '-fPIC', '-fvisibility=hidden',
        '-fno-omit-frame-pointer', '-mno-red-zone', '-fstack-clash-protection',
        '-Werror=implicit-function-declaration', '-DBEND_CUDA=0', '-DBEND_METAL=0',
        '-shared', '-Wl,-z,now', '-Wl,-z,defs', '-Wl,-Bsymbolic-functions', *defines]
    compiler_hash = digest(CLANG)
    inputs = dict(abiVersion=6, sourceSha256=source_hash,
        preparedSourceSha256=hashlib.sha256(source.encode()).hexdigest(),
        sources=source_hashes, compilerSha256=compiler_hash, compiler=CLANG,
        arguments=[*flags, '-DJAYDB_BUILD_ID="<buildIdentitySha256>"',
                   '-I', '<native>', '<prepared.c>', '-lm', '-o', '<output.so>'], bindings=bindings)
    identity = hashlib.sha256(json.dumps(inputs, sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    output.parent.mkdir(parents=True, exist_ok=True)
    with tempfile.TemporaryDirectory(prefix='.jaydb-simple-', dir=output.parent) as temporary:
        work = Path(temporary)
        prepared, binary = work/'module.c', work/'module.so'
        prepared.write_text(source)
        try:
            result = subprocess.run([CLANG, *flags, f'-DJAYDB_BUILD_ID="{identity}"',
                '-I', str(NATIVE), str(prepared), '-lm', '-o', str(binary)],
                capture_output=True, text=True)
        except OSError as error:
            raise BuildError('infrastructure', str(error)) from error
        if result.returncode:
            raise BuildError('compile', result.stderr[-16000:])
        if digest(c_file) != source_hash or digest(CLANG) != compiler_hash or \
                any(digest(ROOT/name) != value for name, value in source_hashes.items()):
            raise BuildError('identity', 'Build inputs changed during compilation')
        symbols = subprocess.run(['/usr/bin/nm', '-D', str(binary)], check=True,
            capture_output=True, text=True).stdout
        forbidden = re.findall(r'\b(?:jaydb_poll|__sanitizer_cov_\w+|ptrace|clock_gettime|timer\w*|pthread_create)\b', symbols)
        if forbidden:
            raise BuildError('runtime_layout', 'Unexpected resource observer/check symbols: '+str(forbidden))
        report = dict(**inputs, buildIdentitySha256=identity, moduleSha256=digest(binary),
            simpleABI6=True, requestBytes=32, resultBytes=136, resultPrefixBytes=48,
            descriptorBytes=160, termBytes=24, flags=1, ownedOutput=True,
            nativeExecution='same-process-main-thread', nativeStack='linux-main-growdown',
            nativeStackClashProtection=True, semanticCorrespondenceProved=False,
            identityMeaning='Build input identity; hashes do not prove semantic equivalence',
            exportedSymbols=re.findall(r'\bT (jaydb_\w+)', symbols))
        manifest = work/'module.json'
        manifest.write_text(json.dumps(report, indent=2)+'\n')
        os.replace(binary, output)
        os.replace(manifest, output.with_suffix(output.suffix+'.json'))
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('emitted_c', type=Path)
    parser.add_argument('output_so', type=Path)
    for name in ('input', 'output', 'loop', 'state', 'continue', 'finish', 'inconsistent', 'prepare', 'enter'):
        parser.add_argument('--'+name+'-cid', default='CID_Native_'+('read' if name == 'input' else 'write')
                            if name in ('input', 'output') else None)
    args = parser.parse_args()
    try:
        bindings = {name+'_cid': None if getattr(args, name+'_cid') == 'none' else getattr(args, name+'_cid')
            for name in ('input', 'output', 'loop', 'state', 'continue', 'finish', 'inconsistent', 'prepare', 'enter')}
        print(json.dumps(build_module(args.emitted_c, args.output_so, **bindings)))
    except (BuildError, OSError) as error:
        print(json.dumps({'error': getattr(error, 'category', 'infrastructure'), 'message': str(error)}))
        raise SystemExit(1)

