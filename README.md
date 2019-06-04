### Latest version ###

0.4.0  

Major changes compared to previous version:
- Simplified usage; support for parameter atom and cost function specification using special logical predicates
- Support for distinct sets of parameter atoms and measured atoms, enabling preliminary support for inductive/abductive inference.

### delSAT ###

- [Synopsis](#synopsis)

- [Introduction](#introduction)

- [References](#references)

- [Build and Run](#build-and-run)

- [Usage](#usage)

- [Miscellanea](#miscellanea)

- [Author contact details](#author-contact-details)

- [delSAT Copyright & License](#delsat-copyright--license)

- [Dependencies](#dependencies)

#### Synopsis ####

delSAT is a probabilistic Answer Set and SAT solver targeted at _multimodel_ optimization, probabilistic inference and sampling. It is named after the del (aka nabla) operator &#8711;. 

It uses automatic differentiation and a form of gradient descent to find an optimal multiset of models, given a 
user-defined cost function (loss function, multimodel objective function) over weighted variables - using an approach called _Differentiable Satisfiability_ respectively 
_Differentiable Answer Set Programming_ (&#8706;SAT/ASP) - see [References](#references) for details. 

delSAT can be used for plain SAT and Answer Set solving too, but has a wider range of use cases. For example: 

- Associating differentiable cost functions (representing, e.g., smooth probabilistic weights) with rules, formulas or individual Boolean variables.
  This way, delSAT can be used as a "hybrid" inference engine which makes use of symbolic/logical, graph or other relational 
  knowledge as well as probabilistic/subsymbolic constraints (in form of cost functions). In contrast to most existing probabilistic logic 
  approaches, delSAT doesn't require any independence assumptions or other restrictions for random variables.

- Distribution-aware sampling of models (answer sets or satisfying truth assignments) 
   
- Efficient search for models of _satisfiable_ CPA and PSAT (Probabilistic Satisfiability) instances given in PSAT normal form 

- Parallelized regular (non-probabilistic) SAT or Answer Set solving on the JVM, using DIMACS-CNF or AnsProlog/Clingo-compatible 
  syntax (by using Clingo as grounder)

The non-probabilistic part of the solver algorithm is, like the ASP and SAT solver clasp (https://github.com/potassco/clasp), 
a complete solver, based on CDNL (Conflict-Driven Nogood Learning, which is itself based on CDCL (Conflict-Driven Clause Learning)). 

#### Introduction ####

delSAT's output is a _sample_ (or UNSAT). A sample is here a multiset (bag) of sampled models, i.e., answer sets 
(aka stable models) or satisfying truth assignments (aka witnesses) of the input propositional formula or answer set program.  

The generated sample minimizes a user-defined arbitrary differentiable cost function down to a user-specified threshold or until the cost doesn't change anymore. The threshold allows 
to trade-off accuracy against speed. 

Such a sample is called a _multi-solution_ (or just _solution_ if there is no ambiguity) of the given cost function and the 
logical rules/clauses. In contrast to traditional optimization in SAT or ASP, a cost function refers to the entire multiset of models, 
and the sampled multiset of models as a whole minimizes the cost function. If multiple cost functions are provided, they are combined 
into a single overall cost function (see below).  

E.g., cost functions can be used for (but are not limited to) the specifcation of the probabilities of Boolean variables (atoms),
or, by extension, entire rules and other formulas. This way, delSAT can be used as the "inference engine" for expressive probabilistic 
logic programming frameworks.  
Using the resulting sample, the probabilities of arbitrary queries (logical formulas whose unknown probabilities should be deductively computed) 
can be approximately answered with the usual method, that is, by summing up the frequencies of those models (possible worlds) within the resulting 
sample where the query formula holds. There are no independency assumptions required for the random variables.

To solve the described optimization problem efficiently and approximately, delSAT makes use of a new approach called _Differentiable SAT_ 
(respectively _Differentiable Answer Set Programming_) where a variant of Gradient Descent is directly embedded in the core ASP or SAT 
solving algorithm. Essentially, Differentiable Satisfiability chooses the truth values of nondeterministic Boolean variables in dependance
from the values of partial derivatives of the user-defined cost function. This is then used to iteratively generate models until the cost function's 
minimum is approximately reached. This approach is typically much faster and economic than converting the problem (in those instances where 
such a conversion would be possible) to linear programming form or to a regular SAT, CSP (Constraint Satisfaction Problem) or a standard 
ASP optimization problem using reification).

Details about our approach can be found in the publications under [References](#references).

#### References ####

- Matthias Nickles: Differentiable SAT/ASP. In Elena Bellodi, Tom Schrijvers (Eds.): Proceedings of the 5th International Workshop on Probabilistic Logic Programming (PLP'18). CEUR Vol. 2219, 2018.
- Matthias Nickles: Differentiable Satisfiability and Differentiable Answer Set Programming for Sampling-Based Multi-Model Optimization
http://arxiv.org/abs/1812.11948
- Matthias Nickles: Sampling-Based SAT/ASP Multi-Model Optimization as a Framework for Probabilistic Inference. 
  In Fabrizio Riguzzi, Elena Bellodi, Riccardo Zese (Eds.): Proceedings of the 28th International Conference on Inductive Logic Programming (ILP'18). Lecture Notes in Artificial Intelligence (LNAI), Springer, 2018.
- Matthias Nickles: Distribution-Aware Sampling of Answer Sets. In Davide Ciucci, Gabriella Pasi, Barbara Vantaggi (Eds.): Proceedings of the 12th International Conference on 
  Scalable Uncertainty Management (SUM'18). Lecture Notes in Artificial Intelligence (LNAI), Springer 2018.

#### Build and Run ####

delSAT is written in Scala and runs on the Java Virtual Machine (JVM). A JRE or JDK 8 or higher (64-bit, with support for Unsafe) is required, e.g., OpenJDK.  

A ready-to-run JAR file can be found under [Releases](https://github.com/MatthiasNickles/delSAT/releases).  

To build delSAT from sources, including all dependencies:

- Install sbt (https://www.scala-sbt.org/)
- Make sure file `project/assembly.sbt` exists with content `addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.9")`
- Run `sbt assembly` in console (from the directory which contains file `build.sbt`)

Run delSAT, e.g., like this:

    java -jar delSAT.jar myDIMACSFile.cnf 

or like this: 

    java -jar delSAT.jar myProbabilisticTask.pcnf -t 0.005 -mse 

delSAT can be configured using command line arguments (use `--help` to see the list of available options). Within the source code, settings are mainly 
specified in files sharedDefs.scala and delSAT.scala.  To increase memory available to delSAT, use java with arguments, e.g., `-Xms2g -Xmx6g -Xss10m` 

Less common settings are specified using command line arguments of the form `--solverarg "name" "value1 [value2 ...]"`
The list of supported such argument names and values can be found in source code file `sharedDefs.scala` (more accessible documentation is planned for a forthcoming version).

Another example delSAT call: 
    
    java -jar delSAT-assembly-0.4.0.jar myInputFile.pASPIF -t 0.1 -mse --solverarg "maxCompetingSolverThreadsR" "6" --solverarg "partDerivComplete" "true" 

Parameter `-t` specifies the accuracy threshold (lower = more accurate). Default is is 0.01. For the meaning of `-mse` see the next section.

The format of the input files and how to create them is described in the following section. 

#### Usage ####

##### Cost functions, parameter atoms and measured atoms #####

Input is accepted in various alternative forms:

- as DIMACS CNF (for plain SAT solving) 

- as DIMACS CNF with a list of _parameter atoms_ and cost function (loss function) terms appended 

- in ASP Intermediate Format (ASPIF), optionally with parameter atoms and cost function terms defined using special predicates

- in ASPIF format with a list of parameter atoms and cost function terms appended 

A delSAT cost function is a user-specified differentiable function over so-called _measured variables_. Measured variables
represent the frequencies of _measured atoms_ in the sample. 

Another important concept are _parameter atoms_ (the random variables in our approach). These are those atoms whose truth values 
are varied by differentiable satisfiability. During solving, the cost function is partially differentiated wrt. variables 
which represent individual parameter atoms.  

Parameter and measured atoms are (possibly empty) subsets of the set of all atoms respectively Boolean variables occuring in the input.  

It is up to the user to declare parameter and measured atoms. The set of parameter atoms needs to be explicitly
declared in the input. The set of measured atoms is implicitly given as the set of all variables in the given cost function term.
See examples further below.  

For deductive probabilistic inference, the set of measured atoms and the set of parameter atoms are _identical_. This is
the most efficient situtation. If the two sets aren't identical (as in weight learning, a form of inductive inference), delSAT currently uses a 
finite difference method to approximate the partial derivatives wrt. to the parameter atoms (this
might change in future versions). The latter approach needs to be activated by the user with command line switch `--solverarg useNumericalFiniteDifferences true`  
Of course, if there are parameter atoms which aren't measured atoms, the cost function still needs to depend indirectly from the parameter atoms, as
otherwise searching the parameter space (numerical values of parameter variables) wouldn't have any effect on the loss.  

It is possible to provide multiple cost functions in the input. These are combined into a single cost function 
as a normalized sum.  

The clauses or rules in the input can state can specify arbitrary logical constraints and dependencies among parameter 
or measured atoms, but of course not all such problems have a solution.  
 
The ASPIF input supported by delSAT is a subset of the full ASPIF specification, however, most Answer Set programs (AnsProlog programs), 
including disjunctive programs and programs with variables and typical ASP constructs such as integrity constraints or choice rules, 
can be automatically translated into the supported ASPIF format using a grounding/preprocessing step, see further below in this guide.    

Cost function terms are mathematical expressions which can, besides the usual operators, parentheses and built-in functions such 
as sqrt, log, abs and exp, contain subterms of the form `f(a)` where `a` is an atom, or (in SAT mode) `f(vi)` (where `i` is a Boolean variable).
Some examples are provided in the next sections.  

By default, delSAT stops when the specified cost threshold has been reached. The threshold is set with command line argument `-t` (default: 0.01).  
With switch `--solverarg stopSamplingWhenCostStagnates true` sampling stops when the cost function value doesn't improve significantly anymore.
This is useful in cases where the theoretical cost minimum isn't known or not zero, but with this switch delSAT also becomes more easily stuck in a local minimum.

##### Declaring cost functions and parameter atoms in a logic program #####

Since version 0.4.0, cost functions (including measured atoms) and parameter atoms can optionally be declared in logic programming 
syntax using special predicates, without the need to append them to the DIMACS or ASPIF file.  

These special predicates are otherwise ordinary predicates which can even be part of rules. However, delSAT recognizes them
as cost/parameter atom definitions only if they appear as facts (at least after grounding).  

- Fact `_pat_(a).` declares that atom `a` is a parameter atom. Multiple such facts can be stated.

- Fact `_cost_("L").` declares that `L` is a term which defines a cost function (or a summand of the overall cost function in case multiple such
cost facts are provided). The term needs to be provided as a string literal. 

- Fact `_pr_(a, p).` declares that the probability of atom `a` is `p`/10000 (/10000 is required since standard ASP cannot directly deal with 
fractions or real numbers). `_pr_(a, p)` is syntactic sugar for `_cost_((p/10000-f(a))^2)` and `_pat_(a)`.  The divisor can be changed (see sharedDefs.scala). 
Multiple `_pr_` facts can be provided.

If of these only `_pr_` facts are provided (i.e., the problem is purely deductive-probabilistic), it is recommended to use delSAT
with command line switch `-mse` which activates optimized handling of costs which have the form of inner MSE (Mean Squared Error) terms.  

Note that parameter atoms (the random variables in our framework) need to be defined (i.e., occur in some rule head) but without completely fixing their 
truth values (as otherwise they couldn't be varied during sampling). A simple way to ensure this is by using a so-called _spanning rule_ of
the form `{a}.` However, apart from this, parameter atoms and measured atoms can be freely used in any rules and be interdependent 
with other atoms (even other parameter or measured atoms).  

Example (1):  

    coin(1).
    coin(2).
    
    _pr_(heads(C), 5000) :- coin(C). 
    
    win :- heads(1), heads(2).
    1{heads(C);tails(C)}1 :- coin(C).

The line `_pr_(heads(C), 5000) :- coin(C)` defines that the probability of heads is 0.5 for both coins. This rule works despite not being a fact because it is grounded to 
two facts `_pr_(heads(1), 5000).` and `_pr_(heads(2), 5000)`.  

Remark: If the sets of parameter and measured atoms are identical (as above) but the overall cost function 
isn't provided in form of multiple part cost-terms differentiable against one parameter variable each, 
delSAT needs to be called with `--solverarg partDerivComplete true` and without switch `-mse`.

Any input logic program needs to be normalized and grounded into ASPIF format before sending it to delSAT. For this, 
[Clingo](https://potassco.org/clingo/) can be used as a grounder (observe the required `--trans-ext=all` argument): 
    
    clingo myProbLogicProg.lp --trans-ext=all --pre=aspif > myDelSATInputFile.aspif

Observe that Clingo is used here only to generate the proper ASPIF ground form from the input program; delSAT itself doesn't require Clingo 
or any other external Answer set, SAT or SMT solver.

Probabilities (or more generally: parameter or measured variables) can also be associated with entire rules; how this can be done is explained in more detail in the second document linked under [References](#references). 
The basic syntax pattern for probabilistic rules is  

    aux:- l1, l2, ..., not h.
    h :- l1, l2, ..., not aux.
    _pr_(aux, 10000-pr).
    
where `pr` is the desired probability (multiplied with 10000) of rule `h :- l1, l2, ...` and the `l1` etc are literals.
     
Measured and parameter atoms don't need to overlap, as shown in the following logic program.  
Example (2):  

    _pat_(h).
    
    0{h}1.
    
    e1 :- h.
    e2 :- h.
    e3 :- h.
    
    _cost_("1 - (f(e1) * f(e2) * f(e3))").

With the code above, delSAT shall search for a probability of atom `h` (a _hypothesis_) such that the probabilities of example atoms `e`i 
are maximized.  

Here, the set of parameter atoms {`h`} is different from the set of measured atoms {`e1`, `e2`, `e3`}, so switch 
`--solverarg useNumericalFiniteDifferences true` is required (this might change in a future version of delSAT).  

[More tbw.]

##### Declaring cost functions and parameter atoms on DIMACS or ASPIF level #####

Alternatively or in addition to the approach described in the previous section, cost functions and parameter atoms can
also be declared directly as an appendix to a DIMACS-CNF or ASPIF file.  

In the input, multiple cost functions can be defined in lines starting with keyword `cost ` (followed by a space).  
If multiple cost functions are given, their normalized sum is minimized.  

If any cost function is provided, also a (single) list of all parameter atoms needs to be specified in the input. These 
have to be listed in a single line starting with `pats `, with no preceding whitespace and with the `pats ` line preceding 
the cost function declarations.  
 
In SAT-mode only, the names of measured atoms (the atoms referred to in cost function terms) need to be prefixed by character `v`.  

A term of form `f(a)` in a cost function (loss function), where `a` is an atom (a propositional variable whose 
truth value delSAT should determine st. the cost is minimized), evaluates during sampling to the frequency of positive 
occurrences of `a` in the sample (count of `a` in all models in the sample, normalized with the total number of models 
in the sample).  

Example (3), for SAT (recommended to use with switch `-mse` which activates optimized handling of costs which have the form of inner MSE (Mean Squared Error) terms):

       p cnf 2 3
       1 -1 0
       2 -2 0
       -1 -2 0
    
       pats 1 2
    
       cost (0.2-f(v1))^2
       cost (0.5-f(v2))^2
       
The costs in the above example specify that literal 1 has probability 0.2 (and its negation -1 has probability 0.8) and that literal 2 has probability 0.5.
If, like above, multiple costs terms are provided, they add up to the overall cost (after normalization with the number of part costs). Such part costs are sometimes called _inner costs_.

Note that in input for SAT, propositional variables _within cost terms_ need to be prefixed by letter `v` (but not in the `pats` line).

The part before line `pats`... is in plain DIMACS-CNF syntax.  
           
Example (4), based on ASPIF (for Answer Set solving instead of SAT). It is recommended to use it with switch `-mse`, since
the cost is provided as multiple inner MSE terms, which can be handled more efficiently with this switch.

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

In the above example, the two cost function terms contain measured atoms a and b and specify that their frequencies in the sample
(resulting bag of answer sets) shall be 0.4 and 0.3, respectively. 

The part above `pats`... is in ASPIF syntax and typically generated automatically from an Answer Set (AnsProlog) program using a preprocessing/grounding tool - see further below for details.
        
Costs can in principle be arbitrary differentiable functions, e.g., you could rephrase the above as follows. Then, call 
delSAT with `--solverarg partDerivComplete true` and without `-mse`. This activates a more general but somewhat less 
efficient but more general differentiation approach:

Example (5):

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

In case the set of parameter atoms is different from the set of measured atoms, currently switch 
`--solverarg useNumericalFiniteDifferences true` is required (this might change in a future version of delSAT).  

To generate the ASPIF part (the part above `pats`) from a non-ground Answer Set program, preprocess
using, e.g., Clingo's (https://potassco.org/clingo/) preprocessing and grounding capability. 

Example grounder call using [Clingo](https://potassco.org/clingo/) (observe the required `--trans-ext=all` argument): 
    
    clingo myLogicProg.lp --trans-ext=all --pre=aspif > myDelSATInputFile.aspif

(Observe that Clingo is only used to generate the proper ground form of the input program; delSAT itself doesn't require Clingo or any other external Answer set, SAT or SMT solver.)
 
The final input file can then be created by appending the `pats` and `cost` lines (if any) to the ASPIF or DIMACS file, each starting in a new line. 

#### Miscellanea ####

- delSAT can be used with most types of logic programs supported by modern answer set solvers (including Disjunctive Logic Programs) but such programs 
might require a preceeding preprocessing and grounding step as explained above.

- For using First-Order Logic (FOL) syntax (under stable model semantics) with delSAT, preprocess your first-order formulas using a tool such as [fol2asp](https://github.com/MatthiasNickles/fol2asp) or [F2LP](http://reasoning.eas.asu.edu/f2lp/).

- delSAT is not a solver for (weighted) Max-SAT or Min-SAT, nor for finding individually optimal models or an optimality ranking of 
individual models (these problem categories might be supported in a future version).

- In the case where the costs express probabilities of propositional variables (or, by straightforward extension, formulas, as in PSAT), 
the input to delSAT is similar to the normal representation format used for PSAT (probabilistic satisfiability problem) instances, 
so consistent PSAT problem instances are in principle feedable into delSAT in order to sample satisfying probabilistic models. However, note that 
PSAT is a different problem and delSAT doesn't check the satisfiability of probability assignments (except for the Boolean 
satisfiability of "hard" clauses), at least not directly (see remarks about termination and non-termination further below).  
Also note that delSAT's semantics is different from SSAT (Stochastic Boolean Satisfiability).

- While in principle usable with any kind of differentiable cost function(s), MSE-style costs receive optimized treatment with 
command line switch -mse. With that switch, list the instantiated inner MSE terms (of form (wi-f(vari))^2) 
individually instead of providing a single long MSE formula. delSAT minimizes then the expression (innerCost1+...+innerCostN)/n.

- delSAT is not (or only remotely) related to SGDB (Stochastic Gradient Descent Branching Heuristic, in Jia Hui Liang: 
Machine Learning for SAT Solvers, 2018). Whereas SGDB provides a branching heuristics for finding decision variables which maximize 
the probability of creating partial assignments leading to _conflicts_ (and thus improve regular SAT solving performance), 
delSAT's gradient descent-style branching heuristics aims at minimizing a user-defined loss function.

- For certain cost functions, you might need to provide switch --solverarg "partDerivComplete" "true" which activates a 
differentiation approach which is more general than the (faster) default approach. delSAT shows a message in case 
the default approach isn't usable.

- If delSAT doesn't seem to terminate, the most likely reason is that no solution exists because of a probabilistic inconsistency (impossible or conflicting weights) in the provided input.
There is currently no way to let delSAT check for probabilistic (weight) inconsistencies and termination with #models >= 1 doesn't guarantee weight consistency (since delSAT doesn't look for exact solutions). 

- Another possible reason for nontermination could be a convergence threshold which is too low (it's in principle not possible to reach arbitrary accurary) - in that 
case an increase of the threshold (specified with command line argument -t) should solve the problem.

- delSAT doesn't require any assumptions about random event independence, but it can to some degree profit from
probabilistic independence among random variables using option maxBurstR (see sharedDefs.scala) 

- delSAT is not designed as a tool for sampling from the _uniform_ (or a near-uniform) distribution over models, but it supports model set diversification 
with `--solverarg diversify true`, and delSAT can also be used with arbitary discrete probabiltities (including uniform ones) associated with individual models 
using suitable cost functions.

- To increase the entropy of the sample, try 1) increasing the number of models in the sample and/or 2) switch `--solverarg diversify true` 

- delSAT never guarantees that the models it prints are different from each other, as sampling is with replacement (so the resulting lists of
answer sets or propositional models are not duplicate free enumerations as those returned by, e.g., MiniSat, clingo/clasp or smodels). 
--solverarg "diversify" "true" just increases the amount of randomness during decision making when generating a model.

- More detailed API documentation is planned for the near future.

#### Author contact details ####

Matthias Nickles 

matthiasDOTnicklesATgmxDOTnet

Web: https://www.researchgate.net/profile/Matthias_Nickles

Feedback and bug reports are welcome.

#### delSAT Copyright & License ####

Copyright (c) 2018-2019 by Matthias Nickles

License: [MIT license](https://github.com/MatthiasNickles/delSAT/blob/master/LICENSE)

#### Dependencies ####

delSAT uses the following third-party libraries:

- JAutoDiff   
  Copyright (c) 2012 uniker9 (https://github.com/uniker9/JAutoDiff)  
  License: https://github.com/uniker9/JAutoDiff/blob/master/LICENSE.txt  
  Copyright (c) 2017 AccelaD (https://github.com/accelad-com/nilgiri-math/tree/master/src/main/java/com/accelad/math/nilgiri)  
  License: https://github.com/accelad-com/nilgiri-math/blob/master/src/main/java/com/accelad/math/nilgiri/LICENSE

- Parsington (https://github.com/scijava/parsington)  
  Copyright (c) 2015-2016, Board of Regents of the University of Wisconsin-Madison  
  License: https://github.com/scijava/parsington/blob/master/LICENSE.txt

- fastutil (http://fastutil.di.unimi.it)  
  Copyright (c) 2002-2017 Sebastiano Vigna  
  License: https://github.com/vigna/fastutil/blob/master/LICENSE-2.0
