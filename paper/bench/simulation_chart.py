#!/usr/bin/env python3
"""Standalone figure from retained simulation medians and min/max samples."""
import json
from pathlib import Path


def main():
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    root = Path(__file__).resolve().parents[2]
    data = json.loads((root/'paper/evidence/simulation.json').read_text())
    fig, ax = plt.subplots(figsize=(8.5, 4.8), layout='constrained')
    for name in ('cpu-1', 'cpu-16', 'cuda', 'postgresql', 'sqlite'):
        rows = [r for r in data['records'] if r['backend'] == name and r['status'] == 'measured']
        x, y = [r['updates'] for r in rows], [r['median_ms'] for r in rows]
        bars = [[r['median_ms']-r['range_ms'][0] for r in rows],
                [r['range_ms'][1]-r['median_ms'] for r in rows]]
        ax.errorbar(x, y, yerr=bars, marker='o', capsize=3, label=name)
        cap = next((r for r in data['records'] if r['backend'] == name and r['status'] == 'timeout'), None)
        if cap:
            ax.scatter([(1 << cap['depth'])*cap['steps']], [cap['timeout_s']*1000], marker='x', color='gray')
    ax.set(xscale='log', yscale='log', xlabel='Path × step updates',
           ylabel='Complete request / SQL statement (ms)', title='Table-driven integer simulation')
    ax.grid(True, which='major', alpha=.2)
    ax.legend()
    fig.text(.01, -.035, f"Median and sample range; 1 warmup + {data['repeats']} samples. Gray ×: SQL timeout. GPU clock unfixed.", fontsize=9)
    fig.savefig(root/'paper/evidence/simulation.svg', bbox_inches='tight')
    plt.close(fig)


if __name__ == '__main__':
    main()
