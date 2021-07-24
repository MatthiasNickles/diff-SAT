0.5.2

- Minor bug fixes and improvements. Renamed to diff-SAT

0.5.1

- Bug fix: in rare cases, conflict nogood generation messed up the memory layout

0.5.0 

- Optimized SAT solver core (and thus improved sampling performance)
- User API for solving problems with probabilistic or non-probabilistic CNF clauses and ASP ground rules
- Direct User API support for probabilistic non-ground normal rules
- aspif and User API support for weight and choice rules, double default negation in rule bodies and for double and single negation in rule heads 
- Probabilistic ASP Intermediate Format (PASPIF) (ASPIF plus a new probabilistic rule type) 
- CDNL interleaved with Stochastic Local Search (WalkSAT or Simulated Annealing (SASAT-style)) for regular SAT solving
- Bug fixes and several minor improvements
- Some code cleanup and refactoring

0.4.1

- Support for weighted clauses annotated with probabilities in DIMACS CNF (Probabilistic CNF). See [Usage](README.md#usage) for details.
- `_eval_("term", "?")` meta-predicate for ad hoc querying of probabilities and other statistics (e.g., remaining loss) over sampled models. 
An example can be found under [Performing ad hoc queries](README.md#Performing-ad-hoc-queries). 
- Argument `-s` k (k>1) for sampling k models _uniformly_ from the multimodel cost solution.
- Argument `-n` -k (k>1) for sampling k models such that k-m of these models are sampled _uniformly_ from the sample (with size m) for which the cost threshold was initially reached.
- Improved finite differences approach to the case where not all parameter atoms are measured (i.e., occur in costs), automatically activated when needed. Switch `useNumFiniteDiff` is
not required anymore, however, purely numerical differentiation approach can still be enforced with `--solverarg mixedScenario false` (in rare cases this is more efficient). 
- Typically higher solution entropy for the same sample size (`-n`), compared to previous versions. For how to increase the entropy further see [README.md](README.md).
- Support for non-quoted `_cost_` and `_eval_` terms using plain logic programming term notation (e.g., `_cost_(pow(subtr(div(77,100),f(coin(1,heads))),2))` instead of `_cost_("(0.77-f(coin(1,heads)))^2")`).
- Several minor improvements and bug fixes
- Enhanced documentation (this file)

0.4.0  

- Simplified usage; support for parameter atom and cost function specification using special logical predicates
- Support for distinct sets of parameter atoms and measured atoms, enabling preliminary support for inductive/abductive inference.
