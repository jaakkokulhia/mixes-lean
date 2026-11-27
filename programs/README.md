# Programs

The programs behind the numbers, tables and figures of the paper. They are written in Python
(some need NumPy and SciPy; see the paper's section *Programs*). Each part folder `parts/<part>/`
contains a program that writes its output to `data/`, and a script `make_nums.py` that computes the
numbers quoted from it and writes them to `nums.tex`. `make_nums.py` in this folder runs all of
these scripts on the stored data and collects their macros in `nums.tex`.

```bash
cd programs
python3 make_nums.py
```

The stored data in `parts/*/data/` are the outputs used for the paper; rerunning a program
regenerates them.
