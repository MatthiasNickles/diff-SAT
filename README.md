**DelSAT**

**Current version:** 0.2

**Purpose**

DelSAT is an Answer Set Programming (ASP) and SAT solver for sampling-based multimodel optimization (but it can be
used for plain parallelized Answer Set or SAT solving too). 

DelSAT is written in Scala and runs on the Java Virtual Machine (JVM). A JRE or JDK 8 or higher (with support for Unsafe) is required. For performance reasons Java 11 or higher is recommended, e.g., OpenJDK 11.

Input is currently accepted as DIMACS CNF or a subset of the ASP Intermediate Format (aspif),
with an optional list of user-defined differentiable _cost functions_.

DelSAT generates a sample (a multiset of sampled answer sets or sampled satisfying assignments) which
minimizes the given cost functions up to a user-specified accuracy. Such a sample is called a _solution_. 

DelSAT makes use of an approach called _Differentiable Satisfiability_ / _Differentiable Answer Set Programming_ where
a form of Gradient Descent is embedded in CDCL/CDNL-style solving to iteratively generate models until the cost functions' minima are reached.
Details on this approach can be found in the following publications:

- Matthias Nickles: Differentiable SAT/ASP. In Proceedings of the 5th International Workshop on Probabilistic Logic Programming (PLP'18). CEUR Vol. 2219, 2018.
- Matthias Nickles: Sampling-Based SAT/ASP Multi-Model Optimization as a Framework for Probabilistic Inference. 
  In Proceedings of the 28th International Conference on Inductive Logic Programming (ILP'18). Lecture Notes in Artificial Intelligence (LNAI), Springer, 2018.
- Matthias Nickles: Distribution-Aware Sampling of Answer Sets. In Proceedings of the 12th International Conference on 
  Scalable Uncertainty Management (SUM'18). Lecture Notes in Artificial Intelligence (LNAI), Springer 2018.

**Use**

In the input, cost functions are defined in lines starting with "cost ". Cost functions need to be 
differentiable with respect to their respective parameter atom terms (see below). If multiple cost functions
are given, their normalized sum is minimized.

In addition to the cost functions, DelSAT input requires a list of _parameter atoms_ (parameter variables); these are the random variables which 
can occur in cost functions. They need to be listed in a single line starting with "pats " (preceding the cost function declarations). 
In SAT-mode only, parameter atoms within cost function expressions need to be prefixed by character 'v'. 

The DelSAT input can state any number of arbitrary such cost functions and can specify arbitrary 
logical dependencies between parameter atoms (but of course not all such constraint systems have 
a solution).

A term of form f(p) in a cost function, where p is a parameter atom, evaluates during sampling to 
the frequency of p in the sample (count of p in all models in the sample, normalized with the total number of models in the sample). 
(Parameter atoms are listed in addition to the cost functions because a future version of DelSAT is planned to allow for
atoms to occur in cost functions which are not parameter atoms, as proposed in the ILP'18 paper.)

Example input for SAT (recommended to use with switch -mse - activates optimized handling of costs which have the form of inner MSE (Mean Squared Error) terms):

       p cnf 2 3
       1 -1 0
       2 -2 0
       -1 -2 0
    
       pats 1 2
    
       cost (0.2-f(v1))^2
       cost (0.5-f(v2))^2
           
Example input for ASP (recommended to use with switch -mse):

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
        
        cost (0.4-f(a))^2
        cost (0.3-f(b))^2
           
To generate aspif format (the lines above before "pats") from a non-ground Answer Set program, preprocess
using, e.g., Clingo (https://potassco.org/clingo/). 

Example preprocessor call: clingo myLogicProg.lp --trans-ext=all --pre=aspif

(Note that DelSAT itself doesn't require Clingo or any other external ASP or SAT solver.)
 
DelSAT is configured using command line arguments (call with --help to see the most important ones,
e.g., desired accuracy). 

More complex cost functions might require argument --solverarg partDerivComplete true  
(DelSAT shows a message in this case).

Harder SAT or ASP problems might also require a specific solver configuration to be (efficiently) solvable 
(such as a certain restart configuration, number of parallel solver threads, non-default portfolio of concurrent solver configurations...). 

The list of solver parameters (accessible via argument --solverarg) can currently be
found in source code file sharedDefs.scala (more accessible documentation is planned for a forthcoming version).

**Tips & Tricks & Miscellanea**

- DelSAT can be used with most types of logic programs supported by modern answer set solvers (including Disjunctive Logic Programs) but such programs might require preprocessing and grounding as explained above

- For using First-Order Logic (FOL) syntax (under stable model semantics), consider preprocessing using a tool such as fol2asp or f2lp.

- While in principle usable with any kind of differentiable cost function(s), MSE-style costs receive optimized treatment with 
command line switch -mse. With that switch, list the instantiated inner MSE terms (of form (wi-f(vari))^2) 
individually instead of providing a single long MSE formula. DelSAT minimizes then the expression (innerCost1+...+innerCostN)/n.

- For arbitrary cost functions, you might need to provide switch --solverarg "partDerivComplete" "true" which activates a 
differentiation approach which is more general than the (faster) default approach. DelSAT shows a message in case 
the default approach isn't usable.

- There is no API documentation yet, but it is planned for the near future

- For performance reasons, DelSAT is largely programmed in imperative style. 

More tbw. 

**Author & contact details**

Author: Matthias Nickles 

matthiasDOTnicklesATgmxDOTnet

Web: https://www.researchgate.net/profile/Matthias_Nickles

Feedback and bug reports on this software are welcome!

**DelSAT Copyright & License**

 Copyright (c) 2018 by Matthias Nickles

License: [MIT license](https://github.com/MatthiasNickles/DelSAT/blob/master/LICENSE)
