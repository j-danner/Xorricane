# Xorricane

> Conflict-Driven SAT Solver for propositional logic formulas in XNF.

This repository contains the source code of our implementation of `CDXCL` called `xorricane`.

## Usage

Run `xorricane -h` to get the following help:

```text
Positional arguments:
  fname                                 path to XNF instance   ve

Optional arguments:
  -h, --help                            shows help message and exits 
  -v, --version                         shows version and compilation information 
  -vb, --verb                           verbosity level (choose in 0-200) [default: 1]
  -t, --time-out                        timeout in seconds [default: - : 1]
  -t, --time-out                        timeout in seconds [default: -1]
  -dh, --decision-heuristic             decision heuristic; 'vsids', 'lwl' (longest watch list), 'swl' (shortest watch list), or 'lex' (lexicographical) [default: "vsids"]
  -po, --phase-options                  phase saving options; 'save', 'save_inv', 'rand' [default: "save"]
  -ca, --conflict-analysis              conflict analysis; 'no' (DPLL) or '1uip' (1UIP/TRLearning) [default: "1uip"]
  -rh, --restart-heuristic              restart schedule; 'no' (never), 'fixed' (fixed num confl), 'luby' (theoretical optimal), 'lbd' (dynamic lbd) [default: "lbd"]
  -delh, --deletion-heuristic           deletion heuristic for move/delete in each tier; 'avg_util' (average util), 'util' (median utility), 'lbd' (median LBD) [default: "avg_util"]
  -il, --impl-lits                      computation implied literals after every s-th decision [default: 0]
  -no-lgj, --no-lazy-gauss-jordan-elim  deactivate lazy gauss-jordan-elim of unit clauses 
  -ip, --initial-propagation            initial propagation of linerals; 'no' (no), 'nbu' (reduce if each linerals size does not blow up), or 'full' (full reduction) [default: "no"]
  -pp, --preprocess                     preprocessing via implication graphs (see 2-Xornado); 'no' (no), 'scc' (SCC), or 'fls_scc' (FLS+SCC) [default: "fls_scc"]
  -no-eq, --no-equiv-sub                deactivate substitution of equivalence linerals 
  -ms, --maxsol                         number of solutions to compute; -1 to compute all solutions [default: 1]
  -g, --gcp-out                         propagates once and outputs result [default: "out.xnf"]
  -gp, --guessing-path                  path to guessing path file; each line contains one literal dictating the initial decisions 
  -cm, --clause-minimization            activate (experimental!) clause minimization
```

### Input Format

##### XNF

Informally, a XNF-formula is a CNF-formula, where literals are replaced by XORs of literals, called *linerals*.
The solver reads XNF-formulas in a DIMACS-like format with header `p xnf n_vars n_cls`, where linerals, a XOR of literals, are encoded as literals connected by `+`; and clauses are terminated by `0`.
For example, the XNF clause $(\neg X_1 \oplus X_2 \oplus X_3) \vee (X_4\oplus X_5)$ is encoded as `-1+2+3 4+5 0`.

##### CNF-XOR

A CNF-XOR formula consists of a CNF formula and XOR constraints on the variables. `xorricane` supports these constraints in the usual encoding as a line starting with `x` followed by the involved literals. For example the constraint $\neg X_1 \oplus X_2$ can be encoded as `x -1 2 0`. It coincides with the XNF unit clause `-1+2 0`.

##### ANF

To solve systems in algebraic normal form (ANF), use our [`anf_to_2xnf`](https://github.com/Wrazlmumfp/anf_to_2xnf.git) tool to encode the system of polynomials in XNF first.

## Build

On Ubuntu/Debian ensure that the packages `build-essential`, `cmake`, and `libgmp-dev` (optionally `libjemalloc-dev`, `libbenchmark-dev`, `catch2`/`libcatch2-dev`) are installed. On Arch-based systems the packages `base-devel`, `cmake`, `gcc-libs`, `git`, and `gmp` (optionally `jemalloc`, `benchmark`, `catch2`) are required.
Then run `cmake .` and `make xorricane`.

__SOON__
Alternatively, use the docker image `jdanner/xorricane` (download via `docker pull jdanner/xorricane:latest`) or build it yourself using the provided [`Dockerfile`](Dockerfile) by `docker build -t jdanner/xorricane:latest .`. Then access Xorricane through [`docker_xorricane`](docker_xorricane).

### License

All code written by J. Danner is licensed under __MIT__, as are most of the included libraries. Only [`parallel-hashmap`](src/xornado/parallel-hashmap/) is licensed under __Apache 2.0__ and `m4ri` (downloaded and built during configuration) under __GPLv2__. therefore, the whole solver is licensed under __GPLv3__, which is compatible with all three licenses.
