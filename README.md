**DelSAT**

DelSAT is an Answer Set and SAT solver for sampling-based multimodel optimization (but it can be
used for plain SAT or ASP solving too). 

DelSAT is written in Scala and runs on the JVM. A JRE 8 or higher is required.

Input is currently accepted in DIMACS-CNF or a subset of the ASP Intermediate Format (aspif),
with an optional list of user-defined _cost functions_. Each cost function ranges over a multiset of models (satisfying
assignments or answer sets).

DelSAT generates samples (multisets of sampled models) which minimize the cost functions (up to a user-specified accuracy). 
Such a sample is called a _solution_. 

For optimization, DelSAT makes use of an approach called _Differentiable Satisfiability_ / _Differentiable Answer Set Programming_.
Details on this approach can be found in the following publications:

- Matthias Nickles: Differentiable SAT/ASP. In Proceedings of the 5th International Workshop on Probabilistic Logic 
  Programming (PLP'18). CEUR proceedings, 2018.
- Matthias Nickles: Sampling-Based SAT/ASP Multi-Model Optimization as a Framework for Probabilistic Inference. 
  Proceedings of the 28th International Conference on Inductive Logic Programming (ILP'18). Lecture Notes 
  in Artificial Intelligence (LNAI), Springer, 2018.
- Matthias Nickles: Distribution-Aware Sampling of Answer Sets. Proceedings of the 12th International Conference on 
  Scalable Uncertainty Management (SUM'18). Lecture Notes in Artificial Intelligence (LNAI), Springer, 2018.

In the input, cost functions are defined in lines starting with "cost ". Cost functions need to be 
differentiable with respect to their respective parameter atom terms (see below).

In addition to the cost functions, DelSAT input requires a list of _parameter atoms_ (parameter variables); these are 
the random variables which can occur in cost functions. They need to be listed in a single line starting with "pats " 
(before the cost function declarations). 
In SAT-mode only, parameter atoms within cost function expressions need to be prefixed by character 'v'. 

The DelSAT input can state any number of arbitrary such cost functions and can specify arbitrary 
logical dependencies between parameter atoms (but of course not all such constraint systems have 
a solution).

A terms of form f(p) in a cost function, where p is a parameter atom, evaluates during sampling to 
the frequency of p in the sample (count of p in all models in the sample, normalized with the total number of models in the sample). 

Example for SAT (use without initial whitespace in lines):

       p cnf 2 3
       1 -1 0
       2 -2 0
       -1 -2 0
    
       pats 1 2
    
       cost (0.2-f(v1))^2
       cost (0.5-f(v2))^2
           
Example for ASP:

        asp 1 0 0
        1 0 1 1 0 0
        1 0 1 2 0 0
        1 0 0 0 2 3 4
        1 0 1 4 0 1 -5
        1 0 1 5 0 1 -4
        1 0 1 3 0 1 -6
        1 0 1 6 0 1 -3
        4 1 b 1 3
        4 1 a 1 4
        0
        
        pats a b
        
        cost ((0.4-f(a))^2+(0.3-f(b))^2)/2
           
To generate aspif format (the lines above before "pats") from an Answer Set program, use, e.g., Clingo (https://potassco.org/clingo/).
Example: clingo myLogicProgram.lp --trans-ext=all --pre=aspif
(Note that DelSAT itself doesn't require Clingo or any other external ASP or SAT solver.)
 
DelSAT is configured using command line arguments (call with --help to see the most important ones,
e.g., desired accuracy). 
Some problems require a specific solver configuration to be solvable or to be efficiently solable. E.g.,
the ASP example above requires argument --solverarg "partDerivComplete" "true"  

The list of internal solver parameters accessible via meta-argument --solverarg can currently be
found in source code file sharedDefs.scala
