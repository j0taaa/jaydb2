#!/usr/bin/env python3
"""Prepare already-emitted trusted Bend C as a Linux CPU1 buffer module.

This is not admission. Never point it at unproved client C/source. Compilation
uses a resource-limited helper; run_v1 executes in the server's address space.
"""
from __future__ import annotations
import argparse
import hashlib
import json
import os
import platform
from pathlib import Path
import re
import resource
import struct
import subprocess
import tempfile
import time
import importlib.util

ROOT = Path(__file__).resolve().parents[2]
NATIVE = ROOT / 'native'
CLANG = '/usr/bin/clang-19'
_BUDGET_SPEC = importlib.util.spec_from_file_location('jaydb_native_budget', Path(__file__).with_name('budget.py'))
_BUDGET = importlib.util.module_from_spec(_BUDGET_SPEC)
_BUDGET_SPEC.loader.exec_module(_BUDGET)
_STACK_SPEC = importlib.util.spec_from_file_location('jaydb_native_stack', Path(__file__).with_name('stack_audit.py'))
_STACK = importlib.util.module_from_spec(_STACK_SPEC)
_STACK_SPEC.loader.exec_module(_STACK)


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


def read_resources(path):
    try:
        values = json.loads(Path(path).read_text())
        if not isinstance(values, dict) or set(values) != {'timeout_ns', 'compiler_memory_bytes'}:
            raise ValueError('Expected timeout_ns and compiler_memory_bytes decimal strings')
        parsed = {key: _BUDGET.parse_nat(value) for key, value in values.items()}
        if not all(parsed.values()):
            raise ValueError('Positive compiler limits required')
        return parsed
    except (OSError, ValueError) as exc:
        raise BuildError('argument', f'Invalid compiler resources file: {exc}') from exc


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


def verify_accounted_lowering(emitted):
    """Verify the emitted control cut, not a JSON coverage assertion.

    Input remains trusted same-Book C, never hostile C. The staged compiler
    prevents folding/inlining this entry and identifies external helper entries.
    Every advertised decoder must have this exact dominating, returning arm;
    its legacy body is only in else. No field header/store precedes the arm.
    This is a structural audit, not a proof of the native machine's semantics.
    """
    markers=re.findall(r'^// JAYDB_NATIVE_ACCOUNTED_CODEC_V1 (.*)$',emitted,re.M)
    entries=re.findall(r'^// JAYDB_NATIVE_ACCOUNTED_ENTRY_V1 (FID_\w+)$',emitted,re.M)
    uncovered=re.findall(r'^// JAYDB_NATIVE_ACCOUNTED_UNCOVERED_V1 (.+)$',emitted,re.M)
    empty=emitted.splitlines().count('// JAYDB_NATIVE_ACCOUNTED_EMPTY_V1')
    if not markers and not entries and not empty:
        if 'jaydb_codec_accounted(' in emitted:
            raise BuildError('accounted_coverage','Unbound accounted decoder call')
        return None
    if (len(markers)!=1 or (not entries and not uncovered and not empty)
            or len(set(entries))!=len(entries) or empty>1
            or (empty and (entries or uncovered or markers[0]))):
        raise BuildError('accounted_coverage','Missing/duplicate compiled decoder entry bindings')
    for macro in [
        '#define WL_CASE(F) WL_FN WL_##F(WL_SIG) {',
        '#define WL_OPEN    { WL_BANK u32 rn;',
        '#define WL_DYN(F)  __attribute__((musttail)) return wl_tab[F](WL_ALL)',
        '#define WL_RETN(N)  { rn = (N); sp -= LANE_STEP; WL_DYN((u32)STK(0)); }']:
        if emitted.splitlines().count(macro)!=1:
            raise BuildError('accounted_coverage','Private return/entry macro changed')
    names=markers[0].split(',') if markers[0] else []
    if len(names)!=len(entries) or len(set(names))!=len(names):
        raise BuildError('accounted_coverage','Decoder entry binding mismatch')
    audited=[]
    for name,fid in zip(names,entries):
        # The fixed ABI of the pinned trusted Codec is bs:BOX, limit:2*w32,
        # result:(w32,BOX). This does not constrain arbitrary source arities.
        prefix=(r'WL_CASE\('+re.escape(fid)+r'\)\s*'
            r'Term (?P<bs>_\w+) = r0;\s*u32 (?P<hi>_\w+) = r1;\s*'
            r'u32 (?P<lo>_\w+) = r2;\s*WL_OPEN\s*'
            r'if \(jaydb_accounted_enabled\(\)\) \{\s*Term (?P<out>_\w+)\[2\];\s*'
            r'static const struct jaydb_decoder_ids (?P=out)_ids = \{(?P<ids>CID_\w+(?:, CID_\w+){8})\};\s*'
            r'jaydb_codec_accounted\(e, (?P=bs), (?P=hi), (?P=lo), (?P=out), &(?P=out)_ids\);\s*'
            r'r0 = \(u32\)(?P=out)\[0\];\s*r1 = (?P=out)\[1\];\s*WL_RETN\(2\);\s*'
            r'\} else \{')
        matches=list(re.finditer(prefix,emitted))
        if len(matches)!=1 or len(re.findall(r'WL_CASE\('+re.escape(fid)+r'\)',emitted))!=1:
            raise BuildError('accounted_coverage',f'Decoder lacks the dominating private return arm: {name}')
        ids=matches[0]['ids'].split(', ')
        suffixes=['VAusente','VBool','VInt','VTexto','VListaVazia','VLista','VRegistroVazio','VRegistro','Campo']
        namespaces=[]
        for cid,suffix in zip(ids,suffixes):
            if not cid.endswith('_'+suffix) or not re.search(r'^#define '+cid+r' \d+$',emitted,re.M):
                raise BuildError('accounted_coverage','Unbound trusted constructor layout')
            namespaces.append(cid[:-len(suffix)])
        if len(set(namespaces))!=1:
            raise BuildError('accounted_coverage','Mixed trusted constructor origins')
        audited.append({'name':name,'fid':fid,'constructors':ids})
    if len(re.findall(r'\bjaydb_codec_accounted\s*\(',emitted))!=len(entries):
        raise BuildError('accounted_coverage','Unexpected inline/unbound decoder entry')
    return {'version':1,'entries':audited,'dominatingPrivateReturn':True,
        'completeEntryCut':(bool(entries) or bool(empty)) and not uncovered,
        'decoderFree':bool(empty),'uncoveredEntries':uncovered,
        'semanticCorrespondenceProved':False,'measurementComplete':False}


def prepare_source(emitted: str, input_cid: str | None, output_cid: str | None, *, allow_specialized=False,
                   loop_cid=None, state_cid=None, continue_cid=None, finish_cid=None,
                   inconsistent_cid=None, prepare_cid=None, enter_cid=None):
    lowering=verify_accounted_lowering(emitted)
    accounted=lowering is not None
    accounted_coverage=accounted and lowering['completeEntryCut']
    generic = bool(re.match(r'// JAYDB_NATIVE_GENERIC_V1 [0-9a-f]{64}\n', emitted))
    if not generic and not allow_specialized:
        raise BuildError('specialized_backend', 'Use generic.mjs on the same admitted Book; optimized Nat/Array C is diagnostic only')
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
    source = (f'#define _GNU_SOURCE\n#define JAYDB_ACCOUNTED_CODEC {int(accounted and bool(lowering["entries"]))}\n'
        f'#define JAYDB_ACCOUNTED_ENTRY_COVERAGE {int(accounted_coverage)}\n'
        f'#define JAYDB_ACCOUNTED_NO_CODEC {int(accounted and lowering["decoderFree"])}\n'
        f'#define JAYDB_LOGICAL_TERMS {int(wide_ids)}\n#include "guard.h"\n') + source
    source = source.replace('// Dialect\n// =======', '#include "leaves_alias.h"\n\n// Dialect\n// =======')
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
        # instead. The bank occupies a prefix of the charged Term stack, once
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
        (NATIVE / 'arena.inc.c').read_text() + '\n' + (NATIVE / 'stack.inc.c').read_text()
        + '\n' + (NATIVE / 'heap.inc.c').read_text())
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
    source = source.replace('// Segments\n// ========', (NATIVE / 'decoder.inc.c').read_text()+'\n// Segments\n// ========')
    source += '\n' + (NATIVE / 'module_tail.c').read_text() + '\n' + (NATIVE / 'module_v3.c').read_text()
    source = source.replace('static Term *jaydb_stack_at(Term*, int64_t, bool);',
        'static Term *jaydb_stack_at(Term*, int64_t, bool);\nstatic Term *jaydb_heap_cell(Term*, u64);\n'
        'struct jaydb_term_store;\nstatic Term *jaydb_term_cell(struct jaydb_term_store*, u64);')
    atomic_macro = '#define a32_at(H, word)     ((DEV u32*)&(H)[word])'
    if source.count(atomic_macro) != 1:
        raise BuildError('runtime_layout', 'Expected pinned heap atomic accessor')
    source = source.replace(atomic_macro, '#define a32_at(H, word) ((DEV u32*)jaydb_heap_cell((H), (word)))')
    source = source.replace('(DEV u32a*)(H + loc) + i', '(DEV u32a*)jaydb_heap_cell(H, loc) + i')
    return (heap_accessors(source), generic)


def audit_ir(ir: str):
    """Fail if any optimized CFG cycle can avoid the cooperative callback.

    Also require coverage at every defined function's entry, so recursive and
    indirect function cycles cannot avoid polling. No program constructor runs
    at dlopen: only LLVM's guard initialization constructor is allowed.
    """
    functions = 0
    blocks = 0
    for match in re.finditer(r'^define [^\n]*@([^ (]+)\([^\n]*\)[^\n]*\{\n(.*?)^}', ir, re.M | re.S):
        name, body = match.groups()
        if name.startswith('sancov.module_ctor'):
            continue
        functions += 1
        pieces = re.split(r'^([A-Za-z0-9_.$-]+):[^\n]*\n', body, flags=re.M)
        graph = {'entry': pieces[0]}
        for i in range(1, len(pieces), 2):
            graph[pieces[i]] = pieces[i + 1]
        # Clang's implicit entry may be numeric and is not referred to by a
        # branch. Blocks starting with a label have an empty preamble instead.
        if not graph['entry'].strip():
            del graph['entry']
        safe = {k for k, v in graph.items() if 'call void @__sanitizer_cov_trace_pc_guard(' in v}
        first = next(iter(graph))
        if first not in safe:
            raise BuildError('coverage', f'Function entry without safe point: {name}')
        edges = {k: re.findall(r'label %([A-Za-z0-9_.$-]+)', v) for k, v in graph.items() if k not in safe}
        visiting, visited = set(), set()
        for node in edges:
            if node in visited:
                continue
            visiting.add(node)
            pending = [(node, iter(edges[node]))]
            while pending:
                current, targets = pending[-1]
                target = next(targets, None)
                if target is None:
                    pending.pop()
                    visiting.remove(current)
                    visited.add(current)
                elif target in visiting:
                    raise BuildError('coverage', f'Unpolled CFG cycle in {name}')
                elif target in edges and target not in visited:
                    visiting.add(target)
                    pending.append((target, iter(edges[target])))
        blocks += len(graph)
    if not functions:
        raise BuildError('coverage', 'No instrumented functions found')
    return {'instrumentedFunctions': functions, 'basicBlocks': blocks, 'unpolledCycles': 0}


def image_bytes(file):
    data = Path(file).read_bytes()
    if data[:6] != b'\x7fELF\x02\x01':
        raise BuildError('platform', 'Expected little-endian ELF64')
    phoff = struct.unpack_from('<Q', data, 32)[0]
    phsize, count = struct.unpack_from('<HH', data, 54)
    pages = set()
    for i in range(count):
        typ, _, _, vaddr, _, _, memsize, _ = struct.unpack_from('<IIQQQQQQ', data, phoff + i * phsize)
        if typ == 1:
            pages.update(range(vaddr // 4096, (vaddr + memsize + 4095) // 4096))
    return len(pages) * 4096


def build_module(c_file, output, *, input_cid='CID_Native_read', output_cid='CID_Native_write',
                 allow_specialized=False, timeout_seconds=60, timeout_ns=None, compiler_memory_bytes=2 * 1024**3,
                 diagnostic_vm_limit_bytes=None,
                 loop_cid=None, state_cid=None, continue_cid=None, finish_cid=None,
                 inconsistent_cid=None, prepare_cid=None, enter_cid=None, recipe_fixture=None):
    if platform.system() != 'Linux' or platform.machine() != 'x86_64' or os.sysconf('SC_PAGE_SIZE') != 4096:
        raise BuildError('platform', 'This audited backend currently targets Linux x86_64 with 4-KiB pages')
    try:
        budget_ns = _BUDGET.seconds_to_ns(timeout_seconds) if timeout_ns is None else timeout_ns
        deadline = _BUDGET.CompilerDeadline(budget_ns)
    except ValueError as exc:
        raise BuildError('argument', str(exc)) from exc
    if compiler_memory_bytes <= 0:
        raise BuildError('argument', 'Positive logical compiler memory limit required')
    if diagnostic_vm_limit_bytes is not None and diagnostic_vm_limit_bytes <= 0:
        raise BuildError('argument', 'Positive diagnostic VM limit required')
    source_text = Path(c_file).read_text()
    accounted_audit=verify_accounted_lowering(source_text)
    source_hash = hashlib.sha256(source_text.encode()).hexdigest()
    prepared, generic = prepare_source(source_text, input_cid, output_cid, allow_specialized=allow_specialized,
        loop_cid=loop_cid, state_cid=state_cid, continue_cid=continue_cid, finish_cid=finish_cid,
        inconsistent_cid=inconsistent_cid, prepare_cid=prepare_cid, enter_cid=enter_cid)
    compiler_hash = hashlib.sha256(Path(CLANG).read_bytes()).hexdigest()
    output = Path(output).resolve()
    output.parent.mkdir(parents=True, exist_ok=True)
    def run(args):
        def limits():
            # VM is not the selected user-space allocated-backing measure. Normal
            # compilation does not impose RLIMIT_AS from compiler_memory_bytes.
            # This separate option is for explicit diagnostic reproductions.
            if diagnostic_vm_limit_bytes is not None:
                finite_rlimit_max = (1 << (8 * struct.calcsize('l') - 1)) - 1
                address_limit = diagnostic_vm_limit_bytes if diagnostic_vm_limit_bytes <= finite_rlimit_max else resource.RLIM_INFINITY
                resource.setrlimit(resource.RLIMIT_AS, (address_limit, address_limit))
            resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
        try:
            deadline.remaining_ns()
            p = subprocess.Popen([CLANG, '--no-default-config', *args], stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                                 text=True, preexec_fn=limits)
            stdout, stderr = deadline.wait(p)
        except _BUDGET.CompilerTimeout as exc:
            raise BuildError('compile_time', 'Actual compiler helper deadline reached') from exc
        if p.returncode:
            # No arbitrary compiler failure is a physical memory measurement.
            raise BuildError('compile', stderr[-12000:])
        return stdout
    with tempfile.TemporaryDirectory(prefix='jaydb-native-', dir=output.parent) as temp:
        work = Path(temp)
        source = work / 'module.c'
        source.write_text(prepared)
        defines = [f'-DJAYDB_INPUT_CID={input_cid or "0"}', f'-DJAYDB_OUTPUT_CID={output_cid or "0"}',
                   f'-DJAYDB_INPUT_ENABLED={int(input_cid is not None)}',
                   f'-DJAYDB_OUTPUT_ENABLED={int(output_cid is not None)}',
                   f'-DJAYDB_GENERIC={int(generic)}', f'-DJAYDB_SOURCE_HASH="{source_hash}"',
                   f'-DJAYDB_ACCOUNTED_TEST_FIXTURE={int(recipe_fixture is not None)}',
                   f'-DJAYDB_LOOP_ENABLED={int(bool(loop_cid))}', f'-DJAYDB_PREPARE_ENABLED={int(bool(prepare_cid))}',
                   f'-DJAYDB_STATE_ENABLED={int(bool(state_cid))}',
                   f'-DJAYDB_ENTER_ENABLED={int(bool(enter_cid))}']
        for key, value in [('LOOP', loop_cid), ('STATE', state_cid), ('CONTINUE', continue_cid),
                           ('FINISH', finish_cid), ('INCONSISTENT', inconsistent_cid),
                           ('PREPARE', prepare_cid), ('ENTER', enter_cid)]:
            if value:
                defines.append(f'-DJAYDB_{key}_CID={value}')
        common = ['-std=gnu11', '-O2', '-fPIC', '-fvisibility=hidden', '-fno-omit-frame-pointer',
                  '-fno-optimize-sibling-calls', '-mno-red-zone', '-fstack-clash-protection',
                  '-Werror=implicit-function-declaration',
                  '-DBEND_CUDA=0', '-DBEND_METAL=0', '-DJAYDB_LOCAL_LEAVES=1', '-I', str(NATIVE), *defines]
        coverage = ['-fsanitize-coverage=trace-pc-guard,bb,no-prune']
        values = ['-DJAYDB_MAX_FRAME=0', '-DJAYDB_STACK_MARGIN=0', '-DJAYDB_IMAGE_BYTES=0']
        run([*common, *coverage, *values, '-S', '-emit-llvm', str(source), '-o', str(work / 'module.ll')])
        audit = audit_ir((work / 'module.ll').read_text())
        # Generated arrays have Book-derived constant sizes. Static C frames
        # have no arbitrary byte cap. Guard reserve follows the actual frames
        # and the uncovered internal guard callgraph, with external obligations
        # explicitly retained in the report rather than assumed away.
        run([*common, *coverage, *values, '-fstack-usage', '-c', str(source), '-o', str(work / 'module.o')])
        frames, dynamic = _STACK.read_frames((work / 'module.su').read_text())
        if dynamic:
            raise BuildError('stack_audit', f'Unexpected dynamic emitted C frames: {dynamic}')
        maximum = max(frames.values(), default=0)
        guard_frames, guard_irs, support_objects = {}, [], []
        memory_audit = None
        recipe_report = None
        accounted = accounted_audit is not None
        codec_present=accounted and bool(accounted_audit['entries'])
        if recipe_fixture is not None and not codec_present:
            raise BuildError('argument','Recipe fixtures require an accounted module')
        support_names = ['guard', 'leaves', 'owner', 'memory'] + (['decoder_memory'] if codec_present else [])
        for support in support_names:
            flags = [*common, *coverage, '-fno-builtin'] if support == 'memory' else common
            run([*flags, '-fstack-usage', '-c', str(NATIVE / (support + '.c')), '-o', str(work / (support + '.o'))])
            run([*flags, '-S', '-emit-llvm', str(NATIVE / (support + '.c')), '-o', str(work / (support + '.ll'))])
            support_frames, dynamic = _STACK.read_frames((work / (support + '.su')).read_text())
            if dynamic:
                raise BuildError('stack_audit', f'Unexpected dynamic {support} C frames: {dynamic}')
            support_ir = (work / (support + '.ll')).read_text()
            if support == 'memory':
                memory_audit = audit_ir(support_ir)
            guard_frames.update(support_frames)
            guard_irs.append(support_ir)
            support_objects.append(str(work / (support + '.o')))
        if codec_present:
            recipe_spec=importlib.util.spec_from_file_location('jaydb_native_recipe',Path(__file__).with_name('build_recipe.py'))
            recipe_build=importlib.util.module_from_spec(recipe_spec);recipe_spec.loader.exec_module(recipe_build)
            recipe_object=work/'recipe.o'
            recipe_report=recipe_build.build(recipe_object,test_fixture=recipe_fixture,object_only=True)
            support_objects.append(str(recipe_object))
        maximum = max(maximum, max(guard_frames.values(), default=0))
        guard_ir = '\n'.join(guard_irs)
        guard_stack = _STACK.analyze(guard_ir, guard_frames, roots=tuple(guard_frames))
        if not guard_stack['moduleBoundAvailable']:
            raise BuildError('stack_audit', 'Internal guard callgraph has unresolved stack growth')
        guard_bound = guard_stack['moduleBytesExcludingExternal']
        def margin(frame):
            # Reserve a complete next frame, all internal uncovered guard work,
            # and two x86_64 return addresses; align per the target C ABI.
            return (frame + guard_bound + 2 * _STACK.RETURN_ADDRESS_BYTES + 15) & ~15
        stack_margin = margin(maximum)
        def link():
            run(['-shared', '-Wl,-z,defs,-z,now,-Bsymbolic', str(work / 'module.o'), *support_objects, '-pthread', '-lm', '-o', str(work / 'module.so')])
        link()
        charged_image = image_bytes(work / 'module.so')
        # Embedding a nonzero allocation size can change optimized code size.
        # Find an exact fixed point, auditing the actual final compilation.
        while True:
            final_values = [f'-DJAYDB_MAX_FRAME={maximum}', f'-DJAYDB_STACK_MARGIN={stack_margin}', f'-DJAYDB_IMAGE_BYTES={charged_image}']
            run([*common, *coverage, *final_values, '-S', '-emit-llvm', str(source), '-o', str(work / 'module.ll')])
            audit = audit_ir((work / 'module.ll').read_text())
            run([*common, *coverage, *final_values, '-fstack-usage', '-c', str(source), '-o', str(work / 'module.o')])
            final_frames, dynamic = _STACK.read_frames((work / 'module.su').read_text())
            if dynamic:
                raise BuildError('stack_audit', f'Unexpected dynamic final C frames: {dynamic}')
            final_maximum = max(maximum, max(final_frames.values(), default=0))
            stack_audit = _STACK.analyze((work / 'module.ll').read_text() + '\n' + guard_ir,
                                         final_frames | guard_frames)
            link()
            actual_image = image_bytes(work / 'module.so')
            if actual_image == charged_image and final_maximum == maximum:
                break
            charged_image = actual_image
            maximum = final_maximum
            stack_margin = margin(maximum)
        if hashlib.sha256(Path(CLANG).read_bytes()).hexdigest() != compiler_hash:
            raise BuildError('compiler_changed', 'Selected compiler file changed during compilation')
        os.replace(work / 'module.so', output)
    report = {'abiVersion': 1, 'abiVersions': [1, 2, 3], 'flags': 'CPU1_GPU_OFF', 'genericNatArray': generic,
              'ownedOutputV3': True, 'demandStableHeapV3': True, 'durationBitsV3': 128,
              'accountedModeV3': accounted and accounted_audit['completeEntryCut'],
              'accountedCodecV3': codec_present and accounted_audit['completeEntryCut'],
              'accountedDecoderFreeV3':accounted and accounted_audit['decoderFree'],
              'accountedLoweringPresent':codec_present,'accountedRecipeAudit':recipe_report,
              'accountedLoweringAudit':accounted_audit,'privateAccountedAbi':1,
              'accountedTestFixture':recipe_fixture is not None,
              'accountedCoverageGrantedByJson':False,
              'absoluteSetupDeadlineV3': True, 'localSyscallAndMemoryLeafs': True,
              'memoryCoverage': memory_audit, 'dynamicTlsGuard': False,
              'coverageClockSampleEvery': 16, 'explicitDeadlineChecksAlwaysSample': True,
              'automaticTermStackV3': '// JAYDB_NATIVE_WIDE_IDS_V1\n' in source_text,
              'streamingF32Read': True,
              'compactNat': '// JAYDB_NATIVE_COMPACT_NAT_V1\n' in source_text,
              'wideIds': '// JAYDB_NATIVE_WIDE_IDS_V1\n' in source_text,
              'wordArity': '// JAYDB_NATIVE_WORD_ARITY_V1\n' in source_text,
              'addressWord': '// JAYDB_NATIVE_ADDRESS_WORD_V1\n' in source_text,
              'termBytes': 24 if '// JAYDB_NATIVE_ADDRESS_WORD_V1\n' in source_text else
                  16 if '// JAYDB_NATIVE_WIDE_IDS_V1\n' in source_text else 8,
              'segmentReturn': 'explicit-pointer' if '// JAYDB_NATIVE_ADDRESS_WORD_V1\n' in source_text else 'scalar',
              'registerBank': 'charged-term-stack' if '// JAYDB_NATIVE_WIDE_IDS_V1\n' in source_text else 'scalar-arguments',
              'registerWords': int(re.search(r'^#define JAYDB_REGISTER_WORDS (\d+)$', prepared, re.M)[1])
                  if '// JAYDB_NATIVE_WIDE_IDS_V1\n' in source_text else None,
              'preparationEpochGetter': True,
              'nativeLoop': bool(loop_cid), 'preparationTransition': bool(prepare_cid), 'stageEnter': bool(enter_cid),
              'immortalRefcounts': True, 'sourceSha256': source_hash, 'imageBytes': charged_image,
              'runtimeSha256': {name: hashlib.sha256((NATIVE / name).read_bytes()).hexdigest()
                  for name in ['abi.h', 'abi_v3.h', 'abi_deadline.h', 'abi_stack.h', 'guard.h', 'guard.c', 'leaves.h', 'leaves.c', 'leaves_alias.h', 'owner.h', 'owner.c', 'memory.c', 'arena.inc.c', 'stack.inc.c', 'heap.inc.c', 'terms.inc.c', 'terms_address.inc.c', 'drop.inc.c', 'text.inc.c',
                               'numeric.inc.c', 'f32_parse.inc.c', 'nat.inc.c', 'module_tail.c', 'module_v3.c',
                               'abi_accounted.h','decoder.inc.c','decoder_memory.h','decoder_memory.c',
                               'field_recipe.h','field_recipe.c','field_recipe.S','field.h']},
              'maximumCFrameBytes': maximum, 'coverage': audit,
              'stackGuardReserveBytes': stack_margin, 'nativeStackAudit': stack_audit,
              'minimumExplicitNativeStackBytes': (2 * stack_margin + os.sysconf('SC_THREAD_STACK_MIN') + 4095) & ~4095,
              'automaticNativeStackV3': True,
              'automaticNativeStackModeV3': 'linux-main-growdown',
              'nativeStackClashProtection': True,
              'automaticNativeStackRequiresV3': ['gettid==getpid', 'RLIMIT_STACK=RLIM_INFINITY',
                                                 'trusted host calls on ordinary Linux main stack'],
              'localChargedBytesIncludeOsMainStack': False,
              'compilerDriverFlags': ['--no-default-config'],
              'compilerDefaultConfiguration': False,
              'compilerSha256': compiler_hash,
              'compilerMemoryBytes': _BUDGET.format_nat(compiler_memory_bytes),
              'compilerVmLimitBytes': None if diagnostic_vm_limit_bytes is None else _BUDGET.format_nat(diagnostic_vm_limit_bytes),
              'compilerPhysicalMemoryEnforcedByBuilder': False,
              'compilerElapsedSeconds': (time.monotonic_ns() - deadline.started_ns) / 1_000_000_000,
              'compilerTimeoutNs': _BUDGET.format_nat(budget_ns),
              'compilerTimeoutSeconds': (_BUDGET.format_nat(timeout_seconds) if isinstance(timeout_seconds, int)
                  else str(timeout_seconds)) if timeout_ns is None else None,
              'moduleSha256': hashlib.sha256(output.read_bytes()).hexdigest(),
              'bindings': {'input': input_cid, 'output': output_cid, 'loop': loop_cid,
                  'state': state_cid, 'continue': continue_cid, 'finish': finish_cid,
                  'inconsistent': inconsistent_cid, 'prepare': prepare_cid, 'enter': enter_cid}}
    if accounted:
        identity={'loweringVersion':1,'privateAbi':1,'generatedC':source_hash,
            'compilerSource':re.search(r'^// JAYDB_NATIVE_GENERIC_V1 ([0-9a-f]{64})$',source_text,re.M)[1],
            'nativeSources':report['runtimeSha256'],'recipeSources':recipe_report['sources'] if recipe_report else {},
            'decoderFree':accounted_audit['decoderFree'],'entryCut':accounted_audit['entries'],
            'builder':hashlib.sha256(Path(__file__).read_bytes()).hexdigest(),
            'compilerSha256':compiler_hash,'compilerDriverFlags':['--no-default-config'],
            'semanticCorrespondenceProved':False}
        report['accountedLoweringIdentity']=identity
        report['accountedLoweringIdentitySha256']=hashlib.sha256(
            json.dumps(identity,sort_keys=True,separators=(',',':')).encode()).hexdigest()
        report['accountedProgressAbi']=1
        report['accountedProgressBytes']=104
    output.with_suffix(output.suffix + '.json').write_text(json.dumps(report, indent=2) + '\n')
    return report


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('emitted_c', type=Path)
    parser.add_argument('output_so', type=Path)
    parser.add_argument('--input-cid', default='CID_Native_read')
    parser.add_argument('--output-cid', default='CID_Native_write')
    for name in ('loop', 'state', 'continue', 'finish', 'inconsistent', 'prepare', 'enter'):
        parser.add_argument(f'--{name}-cid')
    parser.add_argument('--allow-specialized-diagnostic', action='store_true')
    timeout_group = parser.add_mutually_exclusive_group()
    timeout_group.add_argument('--timeout-seconds', help='Exact decimal seconds; no floating-point budget')
    timeout_group.add_argument('--timeout-ns', type=_BUDGET.parse_nat, help='Exact integer nanoseconds')
    parser.add_argument('--compiler-memory-bytes', type=_BUDGET.parse_nat)
    parser.add_argument('--diagnostic-vm-limit-bytes', type=_BUDGET.parse_nat,
                        help='Explicit diagnostic RLIMIT_AS, separate from all public resource limits')
    parser.add_argument('--resources-json', type=Path, help='Public limits as decimal strings, outside argv size limits')
    args = parser.parse_args()
    try:
        resources = {}
        if args.resources_json:
            if any(value is not None for value in (args.timeout_seconds, args.timeout_ns, args.compiler_memory_bytes)):
                raise BuildError('argument', '--resources-json cannot be combined with explicit CLI resource limits')
            resources = read_resources(args.resources_json)
        else:
            resources = {'timeout_seconds': args.timeout_seconds if args.timeout_seconds is not None else '60',
                'timeout_ns': args.timeout_ns,
                'compiler_memory_bytes': args.compiler_memory_bytes if args.compiler_memory_bytes is not None else 2 * 1024**3}
        print(json.dumps(build_module(args.emitted_c, args.output_so, input_cid=None if args.input_cid == 'none' else args.input_cid,
            output_cid=None if args.output_cid == 'none' else args.output_cid, allow_specialized=args.allow_specialized_diagnostic,
            diagnostic_vm_limit_bytes=args.diagnostic_vm_limit_bytes,
            **resources,
            **{name + '_cid': getattr(args, name + '_cid') for name in ('loop', 'state', 'continue', 'finish', 'inconsistent', 'prepare', 'enter')})))
    except BuildError as exc:
        print(json.dumps({'error': exc.category, 'message': str(exc)}))
        raise SystemExit(1)
