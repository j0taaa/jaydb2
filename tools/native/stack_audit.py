"""LLVM callgraph/stack evidence; external callees remain explicit obligations.

A musttail edge replaces its caller frame. Every other edge adds the callee
frame and x86_64 return address. This is a module bound, not a claim about
libc/pthread/loader stacks or physical memory. No recursion-depth quota is used.
"""
from collections import deque
import re

RETURN_ADDRESS_BYTES = 8


def read_frames(text):
    frames = {}
    dynamic = []
    for line in text.splitlines():
        location, size, kind = line.rsplit('\t', 2)
        name = location.rsplit(':', 1)[-1]
        frames[name] = int(size)
        if kind != 'static':
            dynamic.append({'function': name, 'kind': kind})
    return frames, dynamic


def functions(ir):
    return {m[1]: m[2] for m in re.finditer(
        r'^define [^\n]*@([^ (]+)\([^\n]*\)[^\n]*\{\n(.*?)^}', ir, re.M | re.S)}


def components(graph):
    """Iterative Kosaraju: Python's recursion limit must not bound a Book."""
    seen, order = set(), []
    for start in graph:
        if start in seen:
            continue
        seen.add(start)
        pending = [(start, iter(graph[start]))]
        while pending:
            node, edges = pending[-1]
            target = next(edges, None)
            if target is None:
                order.append(node)
                pending.pop()
            elif target not in seen:
                seen.add(target)
                pending.append((target, iter(graph[target])))
    reverse = {node: set() for node in graph}
    for node, targets in graph.items():
        for target in targets:
            reverse[target].add(node)
    groups, membership = [], {}
    for start in reversed(order):
        if start in membership:
            continue
        index, group, pending = len(groups), [], [start]
        membership[start] = index
        while pending:
            node = pending.pop()
            group.append(node)
            for target in reverse[node]:
                if target not in membership:
                    membership[target] = index
                    pending.append(target)
        groups.append(sorted(group))
    return groups, membership


def analyze(ir, frames, roots=('jaydb_worker',)):
    bodies = functions(ir)
    segments = {name for name in bodies if name.startswith('WL_')}
    graph = {name: set() for name in bodies}
    calls, external, indirect = [], [], []
    for name, body in bodies.items():
        for line in body.splitlines():
            # Inline asm and LLVM scalar/lifetime intrinsics do not call a C
            # function. Memory intrinsics can lower to libc and stay explicit.
            match = re.search(r'\b(call|invoke)\b.*?([@%])([A-Za-z0-9_.$-]+)\(', line)
            if not match:
                continue
            _, sigil, target = match.groups()
            tail = bool(re.search(r'\bmusttail\b', line))
            if sigil == '%':
                if tail and 'preserve_nonecc' in line:
                    targets = segments
                else:
                    indirect.append({'caller': name, 'instruction': line.strip()})
                    continue
            elif target.startswith('llvm.'):
                if re.match(r'llvm\.(memcpy|memmove|memset)\.', target):
                    memory_function = target.split('.')[1]
                    if memory_function in bodies:
                        # The linker binds compiler-generated memory calls to
                        # these hidden local implementations. Conservatively
                        # include their frame even if backend lowering inlines.
                        targets = {memory_function}
                        tail = False
                    else:
                        external.append({'caller': name, 'callee': target, 'reason': 'May lower to external memory routine'})
                        continue
                else:
                    continue
            else:
                targets = {target}
            for target in targets:
                if target in bodies:
                    graph[name].add(target)
                    calls.append((name, target, tail))
                else:
                    external.append({'caller': name, 'callee': target, 'reason': 'No implementation/stack metadata in audited module'})
    groups, member = components(graph)
    successors = {i: set() for i in range(len(groups))}
    growing, tail_edges = [], 0
    for caller, callee, tail in calls:
        a, b = member[caller], member[callee]
        tail_edges += tail
        if a == b:
            if not tail:
                growing.append({'caller': caller, 'callee': callee, 'component': a})
        else:
            successors[a].add(b)
    reachable = set()
    pending = [root for root in roots if root in graph]
    while pending:
        node = pending.pop()
        if node not in reachable:
            reachable.add(node)
            pending.extend(graph[node])
    missing = sorted(reachable - frames.keys())
    relevant_cycles = [edge for edge in growing if edge['caller'] in reachable]
    # Reverse Kahn over the condensation DAG.
    parents = {i: set() for i in successors}
    for a, targets in successors.items():
        for b in targets:
            parents[b].add(a)
    remaining = {i: len(targets) for i, targets in successors.items()}
    ready = deque(i for i, count in remaining.items() if not count)
    bounds, longest = {}, {}
    outgoing = {i: [] for i in successors}
    for caller, callee, tail in calls:
        if member[caller] != member[callee]:
            outgoing[member[caller]].append((caller, callee, tail))
    while ready:
        a = ready.popleft()
        bounds[a] = max((frames.get(name, 0) for name in groups[a]), default=0)
        longest[a] = [max(groups[a], key=lambda name: frames.get(name, 0))]
        for caller, callee, tail in outgoing[a]:
            candidate = bounds[member[callee]] + (0 if tail else frames.get(caller, 0) + RETURN_ADDRESS_BYTES)
            if candidate > bounds[a]:
                bounds[a] = candidate
                longest[a] = [caller] + longest[member[callee]]
        for parent in parents[a]:
            remaining[parent] -= 1
            if not remaining[parent]:
                ready.append(parent)
    module_bound = max((bounds[member[root]] for root in roots if root in member), default=0)
    external_reachable = sorted({edge['callee'] for edge in external if edge['caller'] in reachable})
    indirect_reachable = [edge for edge in indirect if edge['caller'] in reachable]
    valid_module = not (missing or relevant_cycles or indirect_reachable)
    return {
        'roots': list(roots), 'functions': len(bodies), 'reachableFunctions': len(reachable),
        'musttailEdges': tail_edges,
        'maximumFrameBytes': max(frames.values(), default=0),
        'moduleBytesExcludingExternal': module_bound if valid_module else None,
        'moduleBoundAvailable': valid_module,
        'wholeNativeBoundProved': valid_module and not external_reachable,
        'returnAddressBytes': RETURN_ADDRESS_BYTES,
        'missingFrameMetadata': missing,
        'stackGrowingCycles': relevant_cycles,
        'unknownIndirectCalls': indirect_reachable,
        'externalCallees': external_reachable,
        'maximumPath': max((longest[member[root]] for root in roots if root in member), key=lambda path: sum(frames.get(n, 0) for n in path), default=[]),
        'tailComponents': [group for group in groups if len(group) > 1 and any(n in reachable for n in group)],
    }
