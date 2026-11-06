#!/usr/bin/env python3
"""Render reviewable per-engine projects from the canonical scenario definitions.

This creates source artifacts only: it never starts a database, compiles a
program, changes an engine, or copies the canonical row fixtures.
"""
from __future__ import annotations

import argparse
from pathlib import Path

from jay import SUITE, configuration, proof, seed
from model import load
from sql_engines import ddl


def readme(scenario: dict) -> str:
    scenario_id = scenario["id"]
    target, aggregate, join = (scenario[key] for key in ("target", "aggregate", "join"))
    rows = sum(len(table["rows"]) for table in scenario["tables"])
    lines = [
        f'# {scenario["title"]}',
        "",
        scenario["description"],
        "",
        f'This project has {len(scenario["tables"])} tables and {rows} deterministic seed rows. '
        f'The [canonical scenario](../../scenarios/{scenario_id}.json) contains the schema, '
        "literal rows, workload metadata, and domain limitations.",
        "",
        scenario["workflow"],
        "",
        "| Table | Rows | Columns | References |",
        "| --- | ---: | --- | --- |",
    ]
    for table in scenario["tables"]:
        columns = ", ".join(f'`{column["name"]}` ({column["type"]})' for column in table["columns"])
        references = ", ".join(
            f'`{column["name"]}` → `{column["references"]}`'
            for column in table["columns"] if "references" in column
        ) or "—"
        lines.append(f'| `{table["name"]}` | {len(table["rows"])} | {columns} | {references} |')
    lines += [
        "",
        f'The point-read and update target is `{target["table"]}.{target["column"]}` '
        f'where `id = {target["key"]!r}`. The aggregate sums '
        f'`{aggregate["table"]}.{aggregate["column"]}`. '
        "The transaction workload updates two existing rows atomically.",
    ]
    if join:
        lines += [
            "",
            f'The relationship workload joins `{join["from_table"]}.{join["fk"]}` '
            f'to `{join["to_table"]}.id` and returns '
            f'`[{join["from_table"]}.id, {join["to_table"]}.{join["column"]}]` '
            "in child-ID order. SQL runs a native join; JayDB2 composes key enumeration "
            "and cell reads in the client.",
        ]
    else:
        lines += ["", "This single-table project has no relationship-join workload."]
    lines += [
        "",
        "The `jaydb2/` directory contains the actual configuration, empty application-table "
        "seed with a benchmark user, generic access, two-write, and six-cell row-read "
        "programs, and their universal certificates and termination proofs. The row-read "
        "program batches untimed full-data validation into one certified transaction per "
        "row; it is separate from the timed point-read and relationship workloads. "
        "Each project has eleven generated files: eight Bend sources, two SQL schemas, "
        "and this README. The runner inserts the canonical "
        "rows through admitted prepared requests; the seed file does not embed those rows. "
        "Relative Bend dependencies are supplied by the existing service staging path.",
        "",
        "JayDB2 uses the permissive `Free` configuration: technical schema checks and "
        "authentication apply, but no administrator laws enforce foreign keys or domain "
        "invariants. The SQLite and PostgreSQL schemas declare real foreign-key constraints. "
        "SQLite additionally uses STRICT tables and Boolean checks; the runner enables "
        "`PRAGMA foreign_keys=ON`. These are explicit differences in integrity semantics.",
        "",
        "Run this scenario on all three engines from the repository root:",
        "",
        "```sh",
        "experiments/database-comparison/run.sh \\",
        f'  --scenarios {scenario_id} --output build/comparison-{scenario_id}',
        "```",
        "",
        "Use a new output directory for each run. The runner owns the live databases "
        "and records correctness checks, setup costs, timings, storage, and restart behavior "
        "there. The source artifacts in this directory are generated for review.",
        "",
        "Modeling limits:",
        "",
    ]
    lines += [f"- {limitation}" for limitation in scenario["limitations"]]
    lines += [
        "",
        "Regenerate all projects after changing scenario definitions or the common adapters:",
        "",
        "```sh",
        "python3 -B experiments/database-comparison/materialize.py",
        "python3 -B experiments/database-comparison/materialize.py --check",
        "```",
        "",
    ]
    return "\n".join(lines)


def artifacts(scenario: dict) -> dict[Path, str]:
    folder = SUITE / "projects" / scenario["id"]
    result = {
        folder / "README.md": readme(scenario),
        folder / "jaydb2" / "Configuration.bend": configuration(scenario),
        folder / "jaydb2" / "Seed.bend": seed(scenario),
    }
    for name, depth in (("Access", 2), ("Batch", 3), ("ReadRow", 7)):
        result[folder / "jaydb2" / f"{name}.bend"] = (SUITE / f"{name}.bend").read_text()
        result[folder / "jaydb2" / f"{name}Proof.bend"] = proof(depth)
    for engine in ("sqlite", "postgresql"):
        result[folder / engine / "schema.sql"] = ddl(scenario, engine)
    return result


def main() -> int:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--check", action="store_true", help="Check generated files without writing them")
    options = parser.parse_args()
    files: dict[Path, str] = {}
    scenarios = sorted((SUITE / "scenarios").glob("*.json"))
    for path in scenarios:
        files.update(artifacts(load(path)))
    changed = 0
    for path, expected in files.items():
        if path.is_file() and path.read_text() == expected:
            continue
        changed += 1
        if options.check:
            print(f"Out of date: {path.relative_to(SUITE)}")
        else:
            path.parent.mkdir(parents=True, exist_ok=True)
            path.write_text(expected)
    if options.check and changed:
        return 1
    action = "Checked" if options.check else "Materialized"
    print(f"{action} {len(scenarios)} projects, {len(files)} files; {changed} changed.")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
