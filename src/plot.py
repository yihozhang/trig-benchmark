#!/usr/bin/env python3
import argparse
import csv
import matplotlib.pyplot as plt
import matplotlib.path as mpath
import numpy as np


def _make_star_marker():
    """Create a custom marker: up + down triangles overlaid (star-like)."""
    up = mpath.Path(
        [(-1, -0.6), (1, -0.6), (0, 1), (-1, -0.6)],
        [mpath.Path.MOVETO, mpath.Path.LINETO, mpath.Path.LINETO, mpath.Path.CLOSEPOLY],
    )
    down = mpath.Path(
        [(-1, 0.6), (1, 0.6), (0, -1), (-1, 0.6)],
        [mpath.Path.MOVETO, mpath.Path.LINETO, mpath.Path.LINETO, mpath.Path.CLOSEPOLY],
    )
    verts = np.concatenate([up.vertices, down.vertices])
    codes = list(up.codes) + list(down.codes)
    return mpath.Path(verts, codes)


STAR = _make_star_marker()

# (marker, facecolor, edgecolor, label)
CATEGORIES = {
    (True, True): ("o", "none", "C0", "Both solved (23)"),
    (True, False): ("^", "none", "C1", "EqSat solved (3)"),
    (False, True): ("v", "none", "C2", "Stochastic solved (3)"),
    (False, False): ("x", "C0", "C0", "Neither solved (6)"),
}


def main():
    parser = argparse.ArgumentParser(description="Scatter plot of EqSat vs stochastic cost")
    parser.add_argument("csv", help="Path to CSV file (e.g. trig_results.csv)")
    parser.add_argument("-o", required=True, help="Output PNG filename")
    args = parser.parse_args()

    points = {k: ([], []) for k in CATEGORIES}
    with open(args.csv) as f:
        reader = csv.DictReader(f)
        for row in reader:
            eq_opt = row["eqsat_optimal"] == "true"
            st_opt = row["sto_optimal"] == "true"
            points[(eq_opt, st_opt)][0].append(int(row["sto_cost"]))
            points[(eq_opt, st_opt)][1].append(int(row["eqsat_cost"]))

    # plt.rcParams.update({"font.size": 12})

    fig, ax = plt.subplots(figsize=(4, 4))

    for key, (marker, fc, ec, label) in CATEGORIES.items():
        sx, sy = points[key]
        if sx:
            # kw = dict(marker=marker, s=50, linewidths=1.5, label=label, zorder=3)
            kw = dict(marker=marker, s=50, label=label, zorder=3)
            kw["alpha"] = 0.3
            # if marker == "x":
            kw["color"] = ec
            # else:
            #     kw["facecolors"] = fc
            #     kw["edgecolors"] = ec
            ax.scatter(sx, sy, **kw)

    all_x = [v for xs, _ in points.values() for v in xs]
    all_y = [v for _, ys in points.values() for v in ys]
    hi = max(max(all_x), max(all_y)) + 1
    ax.plot([0, hi], [0, hi], "k--", linewidth=0.8, label="y = x")

    ax.set_xlim(left=0)
    ax.set_ylim(bottom=0)
    ax.set_xlabel("Stochastic search cost")
    ax.set_ylabel("EqSat cost")
    ax.legend()
    fig.tight_layout()
    fig.savefig(args.o, dpi=300, bbox_inches="tight")
    print(f"Saved to {args.o}")


if __name__ == "__main__":
    main()
