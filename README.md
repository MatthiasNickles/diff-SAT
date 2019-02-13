### delSAT ###

- [Synopsis](#synopsis)

- [Introduction](#introduction)

- [Build and Run](#build-and-run)

- [Use](#use)

- [Miscellanea](#miscellanea)

- [Author & Contact details](#author--contact-details)

- [delSAT Copyright & License](#delsat-copyright--license)

- [Dependencies](#dependencies)

#### Synopsis ####

delSAT ("&#8711;SAT") is an Answer Set and SAT solver for the Java Virtual Machine (JVM), mainly targeted at model sampling and model multiset optimization. 

Example use cases: 

- Finding an optimal multiset of models, given a user-defined cost function which assigns costs to entire multisets of models

- Distribution-aware sampling of satisfying propositional models or answer sets

- As a probabilistic inference engine which can use logical, graph or other relational background knowledge, as in Statistical Relational Learning (SRL)
or probabilistic logic programming

- Parallelized plain SAT or Answer Set solving for the JVM

The sampling/optimization feature uses a new algorithm called _Differentiable SAT_ respectively _Differentiable Answer Set Programming_.

The non-probabilistic part of the solver algorithm is, like the ASP and SAT solver clasp (https://github.com/potassco/clasp), 
a complete solver, based on CDNL (Conflict-Driven Nogood Learning) - as opposed to related and more common older approaches such as CDCL and DPLL. 

#### Introduction ####

As an optimization and sampling tool, delSAT generates a _sample_ (a multiset (bag) of sampled models, i.e., answer sets (stable models) or satisfying assignments (witnesses, instances)) which
minimizes a user-defined arbitrary differentiable cost function down to a user-specified threshold. The threshold allows to trade-off accuracy against speed. 

Such a sample is called a _multi-solution_ (or just _solution_ if there is no ambiguity) of the given cost function and the logical rules/clauses. In 
contrast to traditional optimization in SAT or ASP, a cost function refers to the entire multiset of models, and the sampled <ins>multiset</ins> of 
models as a whole minimizes the cost function. If multiple cost functions are provided, they are combined into a single overall cost function (see below). 

Cost functions can be used, for example, to specify desired probability distributions over satisfying Boolean assignments or answer sets
from which delSAT then samples. They can also be used to create expressive probabilistic logic programming frameworks. See literature below for details.

To solve the described optimization problem efficiently and approximately, delSAT makes use of a new approach called Differentiable Satisfiability 
(respectively Differentiable Answer Set Programming) where a form of Gradient Descent is directly embedded in the core ASP or SAT solver algorithm, in order to 
iteratively generate models until the cost function's minimum is (approximately) reached (as opposed to, e.g., converting the problem where possible into a linear programming 
form or a regular (reified) SAT or ASP problem).

Details about this approach can be found in the following publications:

- Matthias Nickles: Differentiable Satisfiability and Differentiable Answer Set Programming for Sampling-Based Multi-Model Optimization
http://arxiv.org/abs/1812.11948
- Matthias Nickles: Differentiable SAT/ASP. In Proceedings of the 5th International Workshop on Probabilistic Logic Programming (PLP'18). CEUR Vol. 2219, 2018.
- Matthias Nickles: Sampling-Based SAT/ASP Multi-Model Optimization as a Framework for Probabilistic Inference. 
  In Proceedings of the 28th International Conference on Inductive Logic Programming (ILP'18). Lecture Notes in Artificial Intelligence (LNAI), Springer, 2018.
- Matthias Nickles: Distribution-Aware Sampling of Answer Sets. In Proceedings of the 12th International Conference on 
  Scalable Uncertainty Management (SUM'18). Lecture Notes in Artificial Intelligence (LNAI), Springer 2018.

#### Build and Run ####

delSAT is currently provided only in the form of source code. To build delSAT from sources, including all dependencies:

- Install sbt (https://www.scala-sbt.org/)
- Make sure file project/assembly.sbt exists with content addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.9")
- Run "sbt assembly" in console (from the directory with file build.sbt)

This creates a self-contained jar file which you can run, for example, like this:

java -Xms2g -Xmx6g -Xss10m -jar delSAT-assembly-0.3.jar myDIMACSFile.cnf 

or like this: 

java -Xms2g -Xmx6g -Xss10m -jar delSAT-assembly-0.3.jar myProbabilisticTask.pcnf -t 0.005 -mse 

#### Use ####

delSAT is written in Scala and runs on the Java Virtual Machine (JVM). A JRE or JDK 8 or higher (64-bit, with support for Unsafe) is required, e.g., OpenJDK.

Input is currently accepted as DIMACS CNF or a subset of the ASP Intermediate Format (aspif), with optional cost function (loss function). 
Most Answer Set programs, including disjunctive programs and programs with variables or typical ASP constructs such as integrity constraints or choice rules, 
can be automatically translated into the supported aspif format using a grounding/preprocessing step, see further below in this guide.

A delSAT cost function is a user-specified differentiable function over properties of multiple models, in particular statistics over variables/atoms.

In the input, multiple cost functions can be defined in lines starting with "cost ". Cost functions need to be 
differentiable with respect to their respective parameter atom terms (see below). If multiple cost functions
are given, their normalized sum is minimized.

In addition to the cost functions, delSAT input requires a list of _parameter atoms_ (parameter variables); these are the random variables which 
can occur in cost functions. They need to be listed in a single line starting with "pats " (preceding the cost function declarations). 
In SAT-mode only, parameter atoms (the random variables) within cost function expressions need to be prefixed by character 'v'. 

The delSAT input can state any number of arbitrary such cost functions and can specify arbitrary 
logical dependencies between parameter atoms, but of course not all such problems have a solution.

A term of form f(p) in a cost function, where p is a parameter atom, evaluates during sampling to 
the frequency of positive occurrences of p in the sample (count of p in all models in the sample, normalized with the total number of models in the sample). 
(Remark: Parameter atoms are listed in addition to the cost functions because a future version of delSAT might allow for
atoms to occur in cost functions which are not parameter atoms, as proposed in the ILP'18 paper.)

Example input file for SAT (recommended to use with switch -mse which activates optimized handling of costs which have the form of inner MSE (Mean Squared Error) terms):

       p cnf 2 3
       1 -1 0
       2 -2 0
       -1 -2 0
    
       pats 1 2
    
       cost (0.2-f(v1))^2
       cost (0.5-f(v2))^2
       
The costs in the above example specify that literal 1 has probability 0.2 and that literal 2 has probability 0.5.
If, like above, multiple costs terms are provided, they add up to the overall cost.

The part before "pats" is in plain DIMACS-CNF syntax.
           
An example input file for ASP (recommended to use with switch -mse):

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

In the above example, the two cost function terms contain atoms a and b and specify that their frequencies in the sample
(resulting bag of answer sets) shall be 0.4 and 0.3, respectively. 

The part above "pats" is in aspif syntax and typically generated automatically from an Answer Set (AnsProlog) program using a preprocessing/grounding tool - see further below for details.
        
Costs can in principle be arbitrary differentiable functions, e.g., you could rephrase the above as follows. Then, call 
delSAT with --solverarg "partDerivComplete" "true" and without -mse. This activates a more general but somewhat less 
efficient differentiation approach:

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

           
To generate aspif format (the lines above before "pats") from a non-ground Answer Set program, preprocess
using, e.g., Clingo's (https://potassco.org/clingo/) preprocessing and grounding capability. 

Example preprocessor call for a non-ground or non-normal Answer Set program: 
    
    clingo myLogicProg.lp --trans-ext=all --pre=aspif > myDelSATInputFile.aspif

(Note that delSAT itself doesn't require Clingo or any other external ASP, SAT or SMT solver.)
 
The final input file can then be created simply by appending the "pats" and "cost" lines (if any) to the aspif or DIMACS file, starting in a new line. 
 
delSAT can  be configured using command line arguments (call with --help to see the list of available options). Within the delSAT source code, settings are mainly 
specified in files sharedDefs.scala and delSAT.scala.  

Less common settings are specified using command line parameters of the form --solverarg "name" "value1 [value2 ...]"
The list of solver parameters accessible via argument --solverarg can currently be found in source code file sharedDefs.scala (more accessible documentation is planned for a forthcoming version).

Example delSAT call: 
    
    java -jar delSAT.jar myInputFile.pasp -t 0.1 -mse --solverarg "partDerivComplete" "true" --solverarg "maxCompetingSolverThreadsR" "6"

Parameter -t specifies the accuracy threshold (lower = more accurate). Default is is 0.01.

In principle, arbitrary differentiable cost functions can be specified. Certain more complex cost functions may require argument --solverarg partDerivComplete true  
(delSAT shows a message in this case). For the common MSE form of cost functions (see earlier in this text), argument -mse should be used.

Harder SAT or ASP problems might also require a specific solver configuration to be (efficiently) solvable 
(such as a certain restart configuration, number of parallel solver threads, non-default portfolio of concurrent solver configurations...). 

#### Miscellanea ####

- delSAT can be used with most types of logic programs supported by modern answer set solvers (including Disjunctive Logic Programs) but such programs 
might require a preceeding preprocessing and grounding step as explained above.

- For using First-Order Logic (FOL) syntax (under stable model semantics), consider preprocessing using a tool such as fol2asp or f2lp.

- Most of the configuration options in sharedDefs.scala can also be set when calling delSAT from the command line (see sharedDefs.scala) 

- delSAT is not a solver for (weighted) Max-SAT or Min-SAT, nor for finding individually optimal models

- The input format of delSAT is similar to the input format typically used with PSAT (Probabilistic Satisifiability), so consistent PSAT problems 
might in principle be feedable into delSAT in order to sample satisfying models. However, PSAT is a different problem and delSAT doesn't check the probabilistic coherence of the input (except for the 
Boolean satisfiability of the "hard" clauses). delSAT's semantics is different from SSAT (Stochastic Boolean Satisfiability).

- While in principle usable with any kind of differentiable cost function(s), MSE-style costs receive optimized treatment with 
command line switch -mse. With that switch, list the instantiated inner MSE terms (of form (wi-f(vari))^2) 
individually instead of providing a single long MSE formula. delSAT minimizes then the expression (innerCost1+...+innerCostN)/n.

- For certain cost functions, you might need to provide switch --solverarg "partDerivComplete" "true" which activates a 
differentiation approach which is more general than the (faster) default approach. delSAT shows a message in case 
the default approach isn't usable.

- If delSAT doesn't seem to terminate, the most likely reason is that no solution exists because of a probabilistic inconsistency (impossible weights) in the provided input.
There is currently no way to let delSAT check for probabilistic (weight) inconsistencies and termination with #models >= 1 doesn't guarantee weight consistency (since delSAT doesn't look for exact solutions). 

- Another possible reason for nontermination could be a convergence threshold which is too low (it's in principle not possible to reach arbitrary accurary) - in that 
case an increase of the threshold (specified with command line argument -t) should solve the problem.

- delSAT doesn't require any assumptions about random event independence, but it can to some degree profit from
probabilistic independence among random variables using option maxBurstR (see sharedDefs.scala) 

- delSAT is not designed as a tool for sampling from the _uniform_ (or a near-uniform) distribution over models, but it supports model set diversification 
with --solverarg "diversify" "true", and one can in principle associate arbitary probabiltities with individual models using cost functions.

- delSAT never guarantees that the models it prints are different from each other, as sampling is with replacement. --solverarg "diversify" "true" just increases the amount of randomness during decision making when generating a model.

- More detailed API documentation is planned for the near future.

#### Author & Contact details ####

Author: Matthias Nickles 

matthiasDOTnicklesATgmxDOTnet

Web: https://www.researchgate.net/profile/Matthias_Nickles

Feedback and bug reports are welcome.

#### delSAT Copyright & License ####

Copyright (c) 2018-2019 by Matthias Nickles

License: [MIT license](https://github.com/MatthiasNickles/delSAT/blob/master/LICENSE)

#### Dependencies ####

delSAT uses the following third-party libraries:

- JAutoDiff (https://github.com/uniker9/JAutoDiff, https://github.com/accelad-com/nilgiri-math/tree/master/src/main/java/com/accelad/math/nilgiri)  
  Copyright (c) 2012 uniker9 (JAutoDiff)  
  License: https://github.com/uniker9/JAutoDiff/blob/master/LICENSE.txt  
  Copyright (c) 2017 AccelaD (https://github.com/accelad-com/nilgiri-math/tree/master/src/main/java/com/accelad/math/nilgiri)  
  License: https://github.com/accelad-com/nilgiri-math/blob/master/src/main/java/com/accelad/math/nilgiri/LICENSE

- Parsington (https://github.com/scijava/parsington)  
  Copyright (c) 2015-2016, Board of Regents of the University of Wisconsin-Madison  
  License: https://github.com/scijava/parsington/blob/master/LICENSE.txt

- fastutil (http://fastutil.di.unimi.it)  
  Copyright (c) 2002-2017 Sebastiano Vigna  
  License: https://github.com/vigna/fastutil/blob/master/LICENSE-2.0
