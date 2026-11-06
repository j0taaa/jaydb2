#!/usr/bin/env python3
"""Derive the manuscript's numbers from retained measurements, never timings here."""
import json
import math
from pathlib import Path
import statistics

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / ".build/tcc"


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


if __name__ == "__main__":
    main()
