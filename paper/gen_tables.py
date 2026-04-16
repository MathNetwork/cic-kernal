#!/usr/bin/env python3
"""Generate LaTeX table fragments from JSON data files."""
import json, os

root = os.path.dirname(os.path.abspath(__file__))
data = os.path.join(root, "..", "Examples", "Examples", "Data")

# === Growth table ===
with open(os.path.join(data, "cahypergraph.json")) as f:
    hyper = json.load(f)

from collections import OrderedDict
groups = OrderedDict()
for n in hyper["nerves"]:
    d = n["decl"]
    groups.setdefault(d, []).append(n)

lines = []
lines.append(r"\begin{tabular}{@{}lrr@{}}")
lines.append(r"\toprule")
lines.append(r"Declaration & New nerves & Total \\")
lines.append(r"\midrule")
total = 0
for decl, nerves in groups.items():
    count = len(nerves)
    total += count
    name = decl.replace("_", r"\_")
    lines.append(rf"\texttt{{{name}}} & $+{count}$ & {total} \\")
lines.append(r"\bottomrule")
lines.append(r"\end{tabular}")

with open(os.path.join(root, "tables", "growth.tex"), "w") as f:
    f.write("\n".join(lines) + "\n")
print(f"wrote tables/growth.tex ({len(groups)} declarations, {total} nerves)")

# === Dedup stats ===
with open(os.path.join(data, "treeenv.json")) as f:
    tree = json.load(f)

def count_const(obj, name):
    c = 0
    if isinstance(obj, dict):
        if obj.get("const") == name: c += 1
        for v in obj.values(): c += count_const(v, name)
    elif isinstance(obj, list):
        for v in obj: c += count_const(v, name)
    return c

def count_nodes(obj):
    if isinstance(obj, dict): return 1 + sum(count_nodes(v) for v in obj.values())
    elif isinstance(obj, list): return sum(count_nodes(v) for v in obj)
    return 0

nat_total = sum(count_const(d["decl"], "Nat") for d in tree["declarations"])
node_total = sum(count_nodes(d["decl"]) for d in tree["declarations"])

# Find Const(Nat) ref count in hypergraph
nat_nerve = [n for n in hyper["nerves"] if n["record"] == "Sort(Ls(L0))"]
nat_hash = nat_nerve[0]["hash"] if nat_nerve else 0
nat_const = [n for n in hyper["nerves"] if f"Const({nat_hash}" in n["record"] and n["record"].startswith("Const(")]
nc_hash = nat_const[0]["hash"] if nat_const else 0
nc_refs = sum(1 for n in hyper["nerves"] if nc_hash in n["ref"] and n["hash"] != nc_hash)

dlines = []
dlines.append(r"\begin{tabular}{@{}lrr@{}}")
dlines.append(r"\toprule")
dlines.append(r"& Tree kernel & Hypergraph kernel \\")
dlines.append(r"\midrule")
dlines.append(rf"\texttt{{Const(Nat)}} occurrences & {nat_total} & 1 (referenced by {nc_refs}) \\")
dlines.append(rf"Total nodes/nerves & {node_total} & {total} \\")
dlines.append(r"\bottomrule")
dlines.append(r"\end{tabular}")

with open(os.path.join(root, "tables", "dedup.tex"), "w") as f:
    f.write("\n".join(dlines) + "\n")
print(f"wrote tables/dedup.tex (Nat: {nat_total} vs 1, {node_total} vs {total})")
