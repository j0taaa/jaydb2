#!/usr/bin/env python3
"""Render the focused GPU measurements as a standalone research figure.
Optional dependency: matplotlib. Run after make benchmark-gpu.
"""
import argparse
import json
from pathlib import Path
import statistics


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--input', type=Path, default=Path('paper/evidence/gpu-programs.json'))
    parser.add_argument('--output', type=Path, default=Path('paper/evidence/gpu-programs.svg'))
    args = parser.parse_args()
    import matplotlib
    matplotlib.use('Agg')
    import matplotlib.pyplot as plt
    data = json.loads(args.input.read_text())
    assert len(data['runs']) == 3
    names = {'cpu-1': 'CPU, 1 worker', 'cpu-16': 'CPU, 16 workers', 'cuda': 'CUDA, 1 host worker'}
    colors = ['#4c78a8', '#f58518', '#54a24b']
    fig, axes = plt.subplots(2, 2, figsize=(10, 6))
    for size in range(2):
        sample = data['runs'][0]['records'][size]
        for column, metric in enumerate(['native_worker_ms', 'complete_request_ms']):
            ax = axes[size, column]
            rows = [run['records'][size][metric] for run in data['runs']]
            maximum = max(max(row) for row in rows)
            for index, (run, values, color) in enumerate(zip(data['runs'], rows, colors)):
                median = statistics.median(values)
                ax.barh(index, median, color=color, height=.55)
                ax.errorbar(median, index, xerr=[[median-min(values)], [max(values)-median]],
                            color='black', capsize=3, fmt='none', linewidth=1)
                ax.text(median+maximum*.025, index, f'{median:.2f}', va='center', fontsize=9)
            ax.set_yticks(range(3), [names[run['backend']] for run in data['runs']], fontsize=9)
            ax.invert_yaxis()
            ax.set_xlim(0, maximum*1.32)
            ax.set_xlabel('Wall time, ms (linear scale)', fontsize=9)
            label = 'Native worker' if column == 0 else 'Complete request'
            ax.set_title(f"{label}: depth {sample['depth']}, {sample['total_mixing_rounds']:,} rounds", fontsize=10)
            ax.spines[['top', 'right']].set_visible(False)
            ax.grid(axis='x', alpha=.2)
            ax.set_axisbelow(True)
    fig.suptitle('Same checked bang program: median and min–max of three samples', fontsize=12)
    fig.tight_layout(pad=1.6)
    args.output.parent.mkdir(parents=True, exist_ok=True)
    fig.savefig(args.output, metadata={'Date': None})
    plt.close(fig)


if __name__ == '__main__':
    main()
