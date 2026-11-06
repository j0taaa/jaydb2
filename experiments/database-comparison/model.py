"""Checked portable scenario definitions and independent expected-result model."""
from __future__ import annotations
import copy
import json
import re
from pathlib import Path

NAME = re.compile(r'[a-z][a-z0-9_]{0,62}\Z')


def validate(s):
    assert NAME.fullmatch('s' + s['id'])
    seen = {}
    for t in s['tables']:
        assert NAME.fullmatch(t['name']) and t['name'] not in seen
        columns = {c['name']: c for c in t['columns']}
        assert len(columns) == len(t['columns']) and columns['id']['type'] == 'text'
        assert all(NAME.fullmatch(n) for n in columns)
        assert t['rows'] and len({r['id'] for r in t['rows']}) == len(t['rows'])
        for r in t['rows']:
            assert r.keys() == columns.keys(), (t['name'], r)
            for n, c in columns.items():
                assert type(r[n]) is {'text': str, 'integer': int, 'boolean': bool}[c['type']]
                if c['type'] == 'integer':
                    assert -(2**63) <= r[n] < 2**63
                if 'references' in c:
                    parent, pk = c['references'].split('.')
                    assert pk == 'id' and parent in seen, (t['name'], parent)
                    assert r[n] in {x['id'] for x in seen[parent]['rows']}
        seen[t['name']] = t
    target = s['target']
    t = seen[target['table']]
    assert target['key'] in {r['id'] for r in t['rows']}
    assert next(c for c in t['columns'] if c['name'] == target['column'])['type'] == 'integer'
    a = s['aggregate']
    assert next(c for c in seen[a['table']]['columns'] if c['name'] == a['column'])['type'] == 'integer'
    if s['join']:
        j = s['join']
        col = next(c for c in seen[j['from_table']]['columns'] if c['name'] == j['fk'])
        assert col['references'] == j['to_table'] + '.id'
        assert j['column'] in {c['name'] for c in seen[j['to_table']]['columns']}
    return s


def load(path):
    return validate(json.loads(Path(path).read_text()))


def state(s):
    return {t['name']: sorted(copy.deepcopy(t['rows']), key=lambda r: r['id']) for t in s['tables']}


def joined(s, data):
    j = s['join']
    parent = {r['id']: r[j['column']] for r in data[j['to_table']]}
    return [[r['id'], parent[r[j['fk']]]] for r in data[j['from_table']]]
