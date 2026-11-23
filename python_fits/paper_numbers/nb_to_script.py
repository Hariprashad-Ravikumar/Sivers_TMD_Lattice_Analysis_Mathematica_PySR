#!/opt/homebrew/anaconda3/bin/python
"""Extract chosen code cells of a saved analysis notebook verbatim into a plain script (so the paper numbers come from a script run,
not from stale notebook outputs). Magics and plt.show() are removed and the Agg backend is forced.
Usage: nb_to_script.py NOTEBOOK.ipynb OUT.py CELL [CELL ...]   (cell indices, in the order they should run)"""
import json, sys, re
nb, out, *cells = sys.argv[1:]
cells = [int(c) for c in cells]
nbj = json.load(open(nb))
parts = ["import matplotlib\nmatplotlib.use('Agg')\nimport matplotlib.pyplot as _plt\n_plt.show = lambda *a, **k: None\n"]
for i in cells:
    c = nbj["cells"][i]
    assert c["cell_type"] == "code", (i, c["cell_type"])
    src = "".join(c["source"])
    src = "\n".join(l for l in src.splitlines() if not l.strip().startswith(("%", "!")))
    parts.append(f"# ===== notebook cell {i} =====\n{src}\n")
open(out, "w").write("\n".join(parts))
print("wrote", out, "from cells", cells)
