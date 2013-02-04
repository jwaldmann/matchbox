This program proves termination of rewriting systems.

This is derived from 
http://dfa.imn.htwk-leipzig.de/matchbox/ . 
The intention is to keep the main program small, 
by moving re-usable components to libraries
(haskell-tpdb, satchmo-smt).

Input is in TPDB syntax (plain or XTC),
output is proof trace (textual, CPF).

Methods used: Matrix interpretations over natural
and arctic numbers, dependency pairs transformation,
compression of rewriting systems.

Constraint solvers used: 
glpk linear programming solver, minisat SAT solver.

