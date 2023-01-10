### C++20 implementation

## Benefits
Improves upon python3-implementation as:
(1) graph data structure that allows O(m) backtracking (and linear update times)
(2) xlit<->V translation data structure that allows O(log(m)) containment checks, O(log(n)) insertions, and O(1) backtracking
(3) low-level implementation of xor-literals (dense and sparse) to allow efficient addition, comparison, and gaussian eliminations
(4) 

## Graph data structure

## xlit <-> V
xlit -> vector<int> as unordered_map
int -> xlit as unordered_map



## USAGE
To compile the solver gcc version >=10 is req (we use C++20); for the unit tests we use the framework Catch2.
If you have docker installed on your system you can also test the program using the provided docker executable as
´´´docker run 2xnf_solver_docker [args]´´´
((work in progress!))



## Implementation

update_graph: bfs implementation doesn't work well!


## TODO
 - compile with '-fno-exceptions', to avoid any exception handling?
 - use custom allocator for vecs?
 - revise update func when using trie, i.e., update trie instead of entries?
 - treat long XORs seperatiley:
 (1) store them in a separate list (e.g. in a triangular form); BEFORE graph update sort out too long XORs, AFTER graph update check for contraditions with newly derived xlits --> req decisions for solving will probably increase significantly!
 (2) store them in a separate list (e.g. in a triangular form); DURING graph update only keep new vals if xlit does not increase by too much; in that case store the xlit in list of XORS; AFTER graph update check for contraditions with newly derived xlits --> req decisions for solving will probably increase significantly!
 (3) combine search heuristics with GD-attack ideas, i.e., build 'deduction graph' and use it as a 'pre-selection' strategy for decision heuristic (or as advanced update func for activity-score!)
 (4) in update_graph instead of updating all vertex labels also keep track of their pairwise differences; then it is only necessary to check if each such xlit evals to 0 or 1, and omit the expensive equality/collision checks; this might allow lazy data structures!
