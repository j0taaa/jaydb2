#!/usr/bin/env python3
"""Derive the manuscript's numbers from retained measurements, never timings here."""
import json
import hashlib
import math
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".build/tcc"

COMPARISON_DIGESTS = {
    "results.json": "355fd9b197d980dd590f0a2c5e2b6d6cd5f406616618d9da94a77f2db5d48ba6",
    "raw-result.json": "fbce76fdafe3ed56f40f1264a16e188209a10119e5cb9ba0ec0eac0fbd8079a4",
    "provenance-audit.json": "0d0906ee261582e6bd98d0056190f025c0613fb17a4f8a8b17b073c5f17d7498",
}


def canonical(value):
    # JSON type identity matters: true is not the integer 1.
    return json.dumps(value, sort_keys=True, separators=(",", ":"), allow_nan=False)


def comparison_statistics(data, raw, audit, raw_digest):
    """Recompute the narrowly scoped point-operation table, not an engine ranking."""
    if audit.get("status") != "passed" or audit.get("raw_result_sha256") != raw_digest:
        raise ValueError("Comparison provenance audit does not bind the raw result")
    if data.get("provenance_audit") != audit or raw.get("status") != "failed":
        raise ValueError("Comparison must retain its original inventory-guard failure")
    allowed_changes = {"error", "status", "provenance_audit", "analysis_input_path",
                       "original_inventory_guard_status"}
    if any(canonical(data.get(key)) != canonical(raw.get(key))
           for key in (set(data) | set(raw)) - allowed_changes):
        raise ValueError("Audited comparison changed captured measurements or configuration")
    if data.get("original_inventory_guard_status") != "failed" or audit.get("raw_result_status") != "failed":
        raise ValueError("Original comparison failure must remain explicit")
    if data.get("settings", {}).get("samples") != 7 or data["settings"].get("warmups") != 1:
        raise ValueError("Comparison design changed; revise the article")
    records = data["results"]
    engines = ("jaydb2", "postgresql", "sqlite")
    scenarios = {record["scenario"] for record in records}
    identities = [(record["scenario"], record["engine"]) for record in records]
    expected = {(scenario, engine) for scenario in scenarios for engine in engines}
    if len(scenarios) != 10 or len(identities) != 30 or set(identities) != expected:
        raise ValueError("Missing or duplicate comparison engine/scenario records")
    values = {(workload, engine): [] for workload in ("point_read", "point_update") for engine in engines}
    for record in records:
        if record.get("status") != "passed":
            raise ValueError("A comparison record failed")
        for sample in record["samples"]:
            if sample.get("checked") is not True or canonical(sample["actual"]) != canonical(sample["expected"]):
                raise ValueError("An independently checked comparison output disagrees")
        for workload in ("point_read", "point_update"):
            rows = [sample for sample in record["samples"] if sample["workload"] == workload]
            measured = [sample for sample in rows if sample["phase"] == "sample"]
            warmup = [sample for sample in rows if sample["phase"] == "warmup"]
            if (any(type(sample["iteration"]) is not int for sample in rows)
                    or len(rows) != 8 or len(measured) != 7 or len(warmup) != 1
                    or warmup[0]["iteration"] != 0
                    or {sample["iteration"] for sample in measured} != set(range(1, 8))):
                raise ValueError("Missing or duplicate comparison point-operation samples")
            if any(type(sample["elapsed_ns"]) is not int or sample["elapsed_ns"] <= 0 for sample in rows):
                raise ValueError("Invalid comparison latency")
            median = statistics.median(sample["elapsed_ns"] for sample in measured)
            summary = record["summary"][workload]
            if summary["n"] != 7 or not math.isclose(median, summary["median_ns"]):
                raise ValueError("Comparison summary disagrees with measured samples")
            values[workload, record["engine"]].append(median)
    for scenario in scenarios:
        hashes = {record["final_data_sha256"] for record in records if record["scenario"] == scenario}
        if len(hashes) != 1:
            raise ValueError("Comparison final models disagree across engines")
    return {key: statistics.median(samples) / 1e6 for key, samples in values.items()}


def write_comparison():
    directory = ROOT / "experiments/database-comparison/evidence"
    payloads = {name: (directory / name).read_bytes() for name in COMPARISON_DIGESTS}
    for name, payload in payloads.items():
        if hashlib.sha256(payload).hexdigest() != COMPARISON_DIGESTS[name]:
            raise ValueError(f"Retained comparison input changed: {name}")
    data, raw, audit = (json.loads(payloads[name]) for name in COMPARISON_DIGESTS)
    values = comparison_statistics(data, raw, audit, COMPARISON_DIGESTS["raw-result.json"])
    rows, macros = [], []
    for workload, label, suffix in (("point_read", "Point read", "Read"),
                                    ("point_update", "Point update", "Update")):
        numbers = []
        for engine, prefix in (("jaydb2", "Jay"), ("postgresql", "Postgres"), ("sqlite", "Sqlite")):
            value = f"{values[workload, engine]:.4g}"
            numbers.append(value)
            macros.append(f"\\newcommand{{\\Db{prefix}{suffix}}}{{{value}}}")
        rows.append(label + " & " + " & ".join(numbers) + r" \\")
    (OUT / "database-comparison-table.tex").write_text(
        "\\begin{tabular}{lrrr}\\toprule\n"
        "Operation & JayDB2 & PostgreSQL & SQLite \\\\\\midrule\n"
        + "\n".join(rows) + "\n\\bottomrule\\end{tabular}\n")
    (OUT / "database-comparison-numbers.tex").write_text("\n".join(macros) + "\n")
    print("Verified raw/audited comparison linkage and 30 records; derived point-operation table")


def main():
    source = ROOT / "experiments/integration/evidence/main-review/benchmark.json"
    data = json.loads(source.read_text())
    records = data["records"]
    if sum(r["checked_responses"] for r in records) != data["checked_responses"]:
        raise ValueError("Response counts disagree")
    if data["checked_responses"] != 256 or data["settings"]["samples"] != 7:
        raise ValueError("Manuscript experiment design changed; revise its narrative")
    if not data["controller"]["controller_build"]["chosen_executable_verified_against_fresh_build"]:
        raise ValueError("Measured executable was not matched to a fresh build")
    if data["settings"]["storage"] or data["settings"]["timing_log"]:
        raise ValueError("Manuscript's volatile/unobserved profile no longer holds")
    actual_keys = [(r["iterations_base"], r["read_workers"], r["phase"], r["round"])
                   for r in records]
    expected_keys = {(count, readers, "warmup" if round_ == 0 else "sample", round_)
                     for count in (0, 100_000_000) for readers in (1, 2)
                     for round_ in range(8)}
    if len(actual_keys) != len(expected_keys) or set(actual_keys) != expected_keys:
        raise ValueError("Missing or duplicate benchmark bursts")
    for r in records:
        if r["checked_responses"] != 8 or len(r["response_latency_ns"]) != 8:
            raise ValueError("A recorded burst does not contain eight checked responses")
        if r["elapsed_ns"] <= 0 or not math.isclose(r["requests_per_second"], 8e9 / r["elapsed_ns"]):
            raise ValueError("Burst throughput disagrees with elapsed time")
    summaries = {}
    for summary in data["summary"]:
        key = (summary["iterations_base"], summary["read_workers"])
        rows = [r for r in records if r["phase"] == "sample" and
                (r["iterations_base"], r["read_workers"]) == key]
        latencies = sorted(n for r in rows for n in r["response_latency_ns"])
        computed = {
            "median_requests_per_second": statistics.median(8e9 / r["elapsed_ns"] for r in rows),
            "median_burst_ns": statistics.median(r["elapsed_ns"] for r in rows),
            "response_latency_p95_ns": latencies[math.ceil(.95 * len(latencies)) - 1],
            "max_sampled_tree_rss_bytes": max(r["sampled_tree_peak_rss_bytes"] for r in rows),
        }
        if len(rows) != 7 or any(not math.isclose(value, summary[name]) for name, value in computed.items()):
            raise ValueError("Summary disagrees with raw measured bursts")
        summaries[key] = computed
    if set(summaries) != {(n, r) for n in (0, 100_000_000) for r in (1, 2)}:
        raise ValueError("Missing quantitative summaries")
    macros, table = [], []
    for label, count in [("Tiny", 0), ("Heavy", 100_000_000)]:
        paired = []
        for round_ in range(1, 8):
            rs = {r["read_workers"]: r["requests_per_second"] for r in records
                  if r["phase"] == "sample" and r["iterations_base"] == count and r["round"] == round_}
            paired.append(rs[2] / rs[1])
        median = statistics.median(paired)
        retained = next(p for p in data["paired_comparison"] if p["iterations_base"] == count)
        if not math.isclose(median, retained["median_throughput_ratio_parallel_over_serial"]):
            raise ValueError("Paired ratio disagrees with raw bursts")
        macros.append("\\newcommand{\\" + label + "Ratio}{" + f"{median:.2f}" + "}")
        for readers in (1, 2):
            s = summaries[count, readers]
            name = label + ("One" if readers == 1 else "Two") + "Rps"
            macros.append("\\newcommand{\\" + name + "}{" + f"{s['median_requests_per_second']:.1f}" + "}")
            table.append(f"{label.lower()} & {readers} & {s['median_requests_per_second']:.1f} & "
                         f"{s['median_burst_ns']/1e6:.2f} & {s['response_latency_p95_ns']/1e6:.2f} & "
                         f"{s['max_sampled_tree_rss_bytes']/2**20:.2f} " + r"\\")
    OUT.mkdir(parents=True, exist_ok=True)
    (OUT / "numbers.tex").write_text("\n".join(macros) + "\n")
    (OUT / "table.tex").write_text(
        "\\begin{tabular}{lrrrrr}\\toprule\n"
        "Workload & Readers & Requests/s & Burst ms & p95 ms & Peak MiB \\\\\\midrule\n"
        + "\n".join(table) + "\n\\bottomrule\\end{tabular}\n")
    print("Verified the count of 256 checked responses and all four seven-burst summaries; generated TCC data")
    write_comparison()


if __name__ == "__main__":
    main()
