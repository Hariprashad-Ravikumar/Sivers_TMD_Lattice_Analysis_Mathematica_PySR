import nbformat
import sys

with open("Factorization_RatioTest_CrossPL.py") as f:
    code = f.read()

nb = nbformat.v4.new_notebook()
# Split by standard comments or just put it all in one cell
nb.cells.append(nbformat.v4.new_code_cell(code))

with open("Factorization_RatioTest_CrossPL.ipynb", "w") as f:
    nbformat.write(nb, f)
