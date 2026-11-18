#!/usr/bin/env python3
"""Compare randomized store operations and resulting canonical states with Bend."""
from __future__ import annotations

import json
import os
from pathlib import Path
import random
import re
import subprocess
import sys
import tempfile

ROOT = Path(__file__).resolve().parents[2]
sys.path.insert(0, str(ROOT / "tools"))
from bend import environment, executable
from client import encode

SCHEMA = """
import Base
import ../../../contract/Bytes.bend as B
import ../../../contract/Data.bend as D
import ../../../contract/Protocol.bend as P

def schema() -> D.Schema:
  D.Schema{[D.SchemaTable{"items", "id", [
    D.Column{"flag", D.Boolean{}, True{}},
    D.Column{"id", D.TextValue{}, False{}},
    D.Column{"number", D.Integer{}, False{}},
    D.Column{"text", D.TextValue{}, True{}}
  ]}]}

def strings(xs: List<&2, String>) -> D.Value:
  match xs:
    case Nil{}: D.VListEmpty{}
    case Con{h, t}: D.VList{D.VText{h}, strings(t)}

def label(result: String) -> D.Value:
  D.VRecord{"result", D.VText{result}, D.VRecordEmpty{}}

def count(n: Maybe<&2, B.Number64>) -> D.Value:
  match n:
    case Some{B.Number64{hi, lo}}: D.VRecord{"count", D.VInt{hi, lo}, label("count")}
    case None{}: D.VAbsent{}

def observation(o: D.Observation) -> D.Value:
  match o:
    case D.RowAbsent{}: label("row_absent")
    case D.Cell{v}: D.VRecord{"result", D.VText{"cell"}, D.VRecord{"value", v, D.VRecordEmpty{}}}
    case D.Existence{b}: D.VRecord{"exists", D.VBool{b}, label("existence")}
    case D.Count{n}: count(B.nat64(n))
    case D.Keys{ks}: D.VRecord{"keys", strings(ks), label("keys")}

def output(a: D.Value, s: D.State) -> Maybe<&2, List<&2, U32>>:
  P.encode(D.VRecord{"answer", a, D.VRecord{"state", D.state_value(s), D.VRecordEmpty{}}})

def run(result: D.ResultOp, before: D.State) -> Maybe<&2, List<&2, U32>>:
  match result:
    case D.Observed{o}: output(observation(o), before)
    case D.Changed{after}: output(label("changed"), after)
    case D.FailureData{}: output(label("data_error"), before)

def test(+s: D.State, operation: D.Operation) -> Maybe<&2, List<&2, U32>>:
  run(D.operate(schema(), s, operation), s)
"""

KEYS = ["", "Z", "a", "a0", "aa", "é", "é", "東京", "🌳", "🙂"]
OPERATIONS = {
    "read_cell": "ReadCell", "existence": "ViewExistence", "count": "CountRows",
    "keys": "EnumerateKeys", "define_row": "DefineRow", "define_column": "DefineColumn",
    "remove_row": "RemoveRow",
}


def string(s):
    return json.dumps(s, ensure_ascii=False)


def value(v):
    if v is None:
        return "D.VAbsent{}"
    if type(v) is bool:
        return "D.VBool{" + ("True{}" if v else "False{}") + "}"
    if type(v) is int:
        return f"D.VInt{{{(v >> 32) & 0xffffffff}, {v & 0xffffffff}}}"
    if type(v) is str:
        return f"D.VText{{{string(v)}}}"
    if type(v) is list:
        tail = "D.VListEmpty{}"
        for item in reversed(v):
            tail = f"D.VList{{{value(item)}, {tail}}}"
        return tail
    raise TypeError(v)


def fields(row):
    return "[" + ", ".join(f"D.Field{{{string(k)}, {value(v)}}}" for k, v in row.items()) + "]"


def rows(items):
    return "[" + ", ".join(f"D.Row{{{string(row['id'])}, {fields(row)}}}" for row in items) + "]"


def item(rng, key):
    return {
        "flag": rng.choice([None, False, True]), "id": key,
        "number": rng.choice([-(2**63), -1, 0, 2**63 - 1, rng.randrange(-10**12, 10**12)]),
        "text": rng.choice([None, *KEYS]),
    }


def user(rng, key):
    return {"credential": f"token-{key}", "id": key, "kind": rng.choice(KEYS)}


def case(rng, index):
    items = [item(rng, key) for key in sorted(rng.sample(KEYS, rng.randrange(0, 5)))]
    users = [user(rng, key) for key in sorted(rng.sample(KEYS, rng.randrange(0, 4)))]
    state = {"tables": [{"name": "items", "rows": items}], "users": users}
    bend_state = f'D.State{{[D.Table{{"items", {rows(items)}}}], {rows(users)}}}'

    op = list(OPERATIONS)[index % len(OPERATIONS)]
    collection = rng.choice(["items", "items", None, None, "unknown"])
    key = rng.choice(KEYS)
    current = users if collection is None else items
    if current and rng.randrange(2):
        key = rng.choice(current)["id"]
    columns = ["credential", "id", "kind"] if collection is None else ["flag", "id", "number", "text"]
    column = rng.choice([*columns, "unknown"])
    wire = {"op": op, "collection": collection}
    bend_args = ["D.Users{}" if collection is None else f"D.Application{{{string(collection)}}}"]
    if op not in ("count", "keys"):
        wire["key"] = key
        bend_args.append(string(key))
    if op in ("read_cell", "define_column"):
        wire["column"] = column
        bend_args.append(string(column))
    if op == "define_column":
        valid = (user(rng, key) if collection is None else item(rng, key)).get(column)
        wire["value"] = rng.choice([valid, valid, None, 42, "", "🌳", [True]])
        bend_args.append(value(wire["value"]))
    if op == "define_row":
        row = user(rng, key) if collection is None else item(rng, key)
        if rng.randrange(3) == 0:
            kind = rng.randrange(3)
            if kind == 0:
                row.pop(rng.choice(columns))
            elif kind == 1:
                row["id"] = key + "wrong"
            elif collection is None:
                row["credential"] = rng.choice(["", "token-a"])
            else:
                row["flag"] = "wrong"
        wire["fields"] = row
        bend_args.append(fields(row))

    bend_op = f"D.{OPERATIONS[op]}{{{', '.join(bend_args)}}}"
    wire_bytes = bytes([6]) + len(wire).to_bytes(8, "big")
    wire_bytes += b"".join(encode(k) + encode(v) for k, v in wire.items())
    return f"test({bend_state}, {bend_op})", encode(state).hex(), wire_bytes.hex()


def main():
    rng = random.Random(318528)
    cases = [case(rng, index) for index in range(336)]
    with tempfile.TemporaryDirectory(prefix="store-reference-", dir=ROOT / "tools/live") as tmp:
        generated = Path(tmp) / "StoreReference.bend"
        fixture = Path(tmp) / "cases"
        bend = executable()
        with fixture.open("w", encoding="ascii") as out:
            for start in range(0, len(cases), 42):
                batch = cases[start:start + 42]
                body = ",\n    ".join(expr for expr, _, _ in batch)
                generated.write_text(
                    SCHEMA + "\ndef main() -> List<&2, Maybe<&2, List<&2, U32>>>:\n"
                    f"  [\n    {body}\n  ]\n", encoding="utf-8",
                )
                result = subprocess.run(
                    [bend, generated], cwd=ROOT, env=environment(), capture_output=True,
                    text=True, timeout=120,
                )
                if result.returncode != 0:
                    raise RuntimeError(f"Bend failed for cases {start} onward:\n{result.stdout}{result.stderr}")
                outputs = re.findall(r"Some\{\[([0-9, ]*)\]\}", result.stdout)
                if len(outputs) != len(batch):
                    raise RuntimeError(f"Expected {len(batch)} Bend encodings, got {len(outputs)}:\n{result.stdout[:400]}")
                for (_, state, op), encoded in zip(batch, outputs, strict=True):
                    expected = bytes(map(int, encoded.split(", "))).hex()
                    out.write(f"{state} {op} {expected}\n")
        subprocess.run(
            ["cargo", "test", "--release", "store_reference", "--", "--ignored"],
            cwd=ROOT, env={**os.environ, "STORE_REFERENCE_CASES": str(fixture)}, check=True,
        )
    print(f"Compared {len(cases)} operations and resulting states with {bend.name}.")


if __name__ == "__main__":
    main()
