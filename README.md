
# Implementation of CDCL solver with two watched literals




## Run Locally (Windows)


Install python

```bash
  https://www.python.org/downloads/
```

Go to the project directory

```bash
  cd CDCL-Solver
```

Run the python script

```bash
  python CDCL_Solver.py 
  
  Example: python .\CDCL_Solver.py .\project1-revised-tests\sat\block0.cnf
```

Performance Analysis (optional)  
To get analysis details uncomment *cProfile.run* command and execute *Performance_Analysis*.py  
***Note: 'stats' is the generated file name***

```bash
  python Performance_Analysis.py stats
```
## Optimizations

- Implemented arithmetic restart policy
- Implemented Variable State Independent Decaying Sum (VSIDS) heuristic
- Bug fixes for edge case scenarios
- Analyzing performance of testcases


## Documentation

[CDCL_Solver_Documentation](https://github.com/AbhishekMShastryK/CDCL-Solver/blob/main/CDCL_Solver_Documentation.pdf)


## Acknowledgements

[CDCL SAT Solver from Scratch](https://kienyew.github.io/CDCL-SAT-Solver-from-Scratch/CDCL-SAT-Solver-from-Scratch.html)

