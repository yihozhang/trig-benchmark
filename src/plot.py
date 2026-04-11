#!/usr/bin/env python3
import argparse
import csv
import matplotlib.pyplot as plt


def main():
    parser = argparse.ArgumentParser(description="Scatter plot of EqSat vs stochastic cost")
    parser.add_argument("csv", help="Path to CSV file (e.g. trig_results.csv)")
    parser.add_argument("-o", required=True, help="Output PNG filename")
    args = parser.parse_args()

    eqsat_costs = []
    sto_costs = []
    with open(args.csv) as f:
        reader = csv.DictReader(f)
        for row in reader:
            eqsat_costs.append(int(row["eqsat_cost"]))
            sto_costs.append(int(row["sto_cost"]))

    fig, ax = plt.subplots()
    ax.scatter(sto_costs, eqsat_costs, s=30, alpha=0.7)

    lo = 0
    hi = max(max(eqsat_costs), max(sto_costs)) + 1
    ax.plot([lo, hi], [lo, hi], "k--", linewidth=0.8, label="y = x")

    ax.set_xlabel("Stochastic cost")
    ax.set_ylabel("EqSat cost")
    ax.set_title("EqSat vs Stochastic Optimization Cost")
    ax.legend()
    fig.tight_layout()
    fig.savefig(args.o, dpi=150)
    print(f"Saved to {args.o}")


if __name__ == "__main__":
    main()
