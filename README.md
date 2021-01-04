# Minimal models

Uses a SAT solver to find minimal partial assignments that are model of a CNF
formula. Supports incremental clause additions. Quick and dirty implementation
to illustrate the technique.

This works by maintaining two SAT solver instances, one for the CNF formula
(the positive solver) and one for its negation (the negative solver). As the
negation of a CNF formula is in DNF, we use the Tseytin transformation to
convert the resulting DNF back into an equisatisfiable CNF with auxiliary
variables.

To find a model we first query the positive solver and obtain a complete
assignment that is a model of our formula (if it exists). If we query the
negative solver using a model (complete or partial) of our formula as
assumptions, the result will be UNSAT. The negative solver will then report a
(not necessarily strict) subset of assumptions that are sufficient for
falsifying the formula of the negative solver (called failed literals).

We can minimize the model by iteratively removing a literal from the assignment
and querying the negative solver. If the result becomes SAT, we know the
removed literal is essential and add it back to the assignment. If the result
remains UNSAT, we can permanently remove that candidate and continue with
another literal not known to be essential until none are left. Each time the
result is UNSAT we can also remove all literals not among the failed literals.

I don't have anything to cite right now, but I'm pretty sure this is a known
technique, very similar ideas are used all over the place as part of algorithms
for MaxSAT, QBF, interpolant generation etc.

## Usage

`cat example.cnf - | cargo run --release`

Then press return to find a minimal model and add a clause blocking the found
model.
