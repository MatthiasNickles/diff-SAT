
![#f03c15](https://via.placeholder.com/15/f03c15/000000?text=+) 
Workaround for 'Error [-100]: Invalid input data:"' (without qualifier): This message likely indicates an unsupported character encoding. 
Open the input file with some text editor which supports switching between different character encodings (such as Notepad++ or vim) and 
change the encoding to ***UTF-8*** (without BOM). The next version of diff-SAT will support a wider range of character encodings. ![#f03c15](https://via.placeholder.com/15/f03c15/000000?text=+) 

### Latest versions ###

See [CHANGELOG.md](CHANGELOG.md) 

### User guide ###

- [Synopsis](#synopsis)

- [Introduction](#introduction)

- [References](#references)

- [Installation](#installation)

- [Usage](#usage)

- [Miscellanea](#miscellanea)

- [Author contact details, Feedback](#author-contact-details)

- [diff-SAT Copyright & License](#diff-SAT-copyright--license)

- [Dependencies](#dependencies)

#### Synopsis ####

diff-SAT is an Answer Set and SAT solver targeted at _multi-models_ (worldview) optimization, probabilistic reasoning and model sampling.

diff-SAT uses an approach called _Differentiable Satisfiability_ respectively _Differentiable Answer Set Programming_ (&#8706;SAT/ASP). Basically, this
means SAT or ASP solving using automatic differentiation and a form of gradient descent to find an optimal multiset of models (interpretations), given a 
user-defined cost function (loss function, multimodel objective function) over weighted Boolean variables (see [References](#references) for details). 

[Answer set programming](https://www.cs.utexas.edu/users/vl/papers/wiasp.pdf) is a form of logic programming, with a syntax very similar to Prolog and Datalog. It is mainly oriented towards difficult (primarily NP-hard) combinatorial 
search problems and relational knowledge representation. ASP is closely related to SAT, Constraint Satisfaction Problems (CSP) and Satisfiability Modulo Theories (SMT).  

diff-SAT can be used for plain SAT and Answer Set solving too, but has a wider range of use cases. For example: 

- Associating differentiable cost functions and weights with rules, clauses and other formulas or individual Boolean variables.
  This way, diff-SAT can be used as a "hybrid" inference engine which makes use of symbolic/logical, graph or other relational 
  knowledge as well as probabilistic/subsymbolic constraints (in form of cost functions). In contrast to most existing probabilistic logic 
  approaches, diff-SAT doesn't require any independence assumptions or other restrictions for random variables.

- As an instance of the previous: _probabilistic logic programming_ (_probabilistic answer set programming_) and _probabilistic satisfiability solving_ (weighting of Boolean variables, clauses, facts and rules with probabilities)

- Distribution-aware sampling of models (answer sets or satisfying truth assignments) 
   
- Efficient search for models of _satisfiable_ CPA and PSAT (Probabilistic Satisfiability) instances given in PSAT normal form 

- Highly configurable multithreaded regular SAT and Answer Set solving on the Java VM 

The non-probabilistic part of the solver algorithm is, like the ASP and SAT solver [clasp](https://github.com/potassco/clasp) and the JVM SAT solver [SAT4j](http://www.sat4j.org/), 
a complete solver based on CDNL (Conflict-Driven Nogood Learning), which is itself based on CDCL (Conflict-Driven Clause Learning). However, diff-SAT's CDNL variant differs from clasp in that for non-tight ASP programs, loop handling follows the older ASSAT approach (Lin, Zhao 2004) whereas clasp integrates loop handling in the propagation core. 

#### Introduction ####

diff-SAT's output is a _sample_ (or UNSAT). A sample is here a multiset (bag) of models sampled under probabilistic and logical constraints. Each model is an answer sets 
(aka _stable model_) or a satisfying truth assignment (aka _witness_ or _interpretation_) of the input answer set program respectively propositional formula. From 
a probability theoretical point of view, the individual models in the sample are the _possible worlds_ and their frequencies in the sample are the possible worlds' probabilities.  

The generated sample minimizes a user-defined arbitrary differentiable cost function down to a user-specified threshold or until the cost didn't change anymore. The threshold allows 
to trade-off accuracy against speed. The cost function is given as an arithmetic expression defined over certain statistics of the entire sample.  

Such a sample - respectively the  probability distribution over models it represents - is called an (exact or approximate) _multisolution_ of the given cost function and the 
logical rules/clauses.      

In contrast to traditional optimization in SAT or ASP, a cost function refers to the entire multiset of models, 
and the sampled multiset of models as a whole minimizes the cost function. If multiple cost functions are provided, they are combined 
into a single overall cost function (see below). The number of sampled models and the precise sampling semantics can be influenced with command line
options `-n` and `-s` (use `--help` for details). Observe that for the same input problem, multiple multisolutions may exist.   

Cost functions can, for example, be used for the specification of the probabilities of Boolean variables (atoms),
or, by extension, entire clauses, rules and other formulas. This way, diff-SAT can be used as the "inference engine" for expressive probabilistic 
logic programming frameworks.  

In the resulting sample, marginal possible world probabilities are simply the frequencies of the respective models. Therefore probabilities of arbitrary query formulas 
can be (approximately) computed with the usual method, that is, by summing up the frequencies of those models where the query formula holds. There are no independency assumptions required for the random variables.

To solve the described optimization problem efficiently and approximately, diff-SAT makes use of a new approach called _Differentiable SAT_ 
(respectively _Differentiable Answer Set Programming_) where a variant of Gradient Descent is directly embedded in the core ASP or SAT 
solving algorithm. Essentially, Differentiable Satisfiability chooses (during the search for a satisfying model) the truth values of 
nondeterministic Boolean variables depending on the values of partial derivatives of the user-defined cost function. This is used to 
iteratively generate models until the cost function's minimum is approximately reached. This approach works typically much faster than via converting the problem (in those instances where 
such a conversion would be possible) to Linear Program form or to a regular SAT, CSP (Constraint Satisfaction Problem) or a standard 
ASP optimization problem using model reification.

Details about our approach can be found in the publications under [References](#references).

#### References ####

- Matthias Nickles: Differentiable SAT/ASP. In Elena Bellodi, Tom Schrijvers (Eds.): Proceedings of the 5th International Workshop on Probabilistic Logic Programming (PLP'18). CEUR Vol. 2219, 2018.
- Matthias Nickles: Differentiable Satisfiability and Differentiable Answer Set Programming for Sampling-Based Multi-Model Optimization
http://arxiv.org/abs/1812.11948
- Matthias Nickles: Sampling-Based SAT/ASP Multi-Model Optimization as a Framework for Probabilistic Inference. 
  In Fabrizio Riguzzi, Elena Bellodi, Riccardo Zese (Eds.): Proceedings of the 28th International Conference on Inductive Logic Programming (ILP'18). Lecture Notes in Artificial Intelligence (LNAI), Springer, 2018.
- Matthias Nickles: Distribution-Aware Sampling of Answer Sets. In Davide Ciucci, Gabriella Pasi, Barbara Vantaggi (Eds.): Proceedings of the 12th International Conference on 
  Scalable Uncertainty Management (SUM'18). Lecture Notes in Artificial Intelligence (LNAI), Springer 2018.

To cite diff-SAT, please use 
```
    @inproceedings{DBLP:conf/ilp/Nickles18a,
      author    = {Matthias Nickles},
      editor    = {Elena Bellodi and Tom Schrijvers},
      title     = {Differentiable {SAT/ASP}},
      booktitle = {Proceedings of the 5th International Workshop on Probabilistic Logic Programming, {PLP} 2018},
      publisher = {CEUR-WS.org},
      year      = {2018},
    }
```

diff-SAT furthers ideas from earlier publications where Probabilistic Answer Set Programming was implemented via sampling and counting operations 
over multiple answer sets, see, e.g.,  

- Matthias Nickles, Alessandra Mileo: A Hybrid Approach to Inference in Probabilistic Non-Monotonic Logic Programming, PLP@ICLP, 2015.

#### Installation ####

diff-SAT is written in Scala and runs on the Java Virtual Machine (JVM). A JRE or JDK 8 or higher (64-bit, with support for Unsafe) is required, e.g., OpenJDK.  

A ready-to-run JAR file can be found under [Releases](https://github.com/MatthiasNickles/diff-SAT/releases).  

To build diff-SAT from sources, including all dependencies:

- Install sbt (https://www.scala-sbt.org/)
- Make sure file `project/assembly.sbt` exists with content `addSbtPlugin("com.eed3si9n" % "sbt-assembly" % "0.14.9")`
- Run `sbt assembly` in console (from the directory which contains file `build.sbt`)

Run diff-SAT, e.g., like this:

    java -jar diffSAT.jar myDIMACSFile.cnf 

or like this: 

    java -jar diffSAT.jar myProbabilisticTask.opt -t 0.005 -mse 
    
##### Command line arguments #####

diff-SAT can be configured using command line arguments. Use `--help` to see the list of the most important arguments. Less frequently required settings are 
specified using command line arguments of 
the form `--solverarg "name" "value1 [value2 ...]"` The full list of these settings can be found in source code file 
[sharedDefs.scala](https://github.com/MatthiasNickles/diff-SAT/blob/master/src/main/scala/sharedDefs.scala).  

Example call: 
    
    java -jar diffSAT.jar myInputFile.paspif -t 0.1 -n 100 -mse --solverarg maxSolverThreadsR 2

Parameter `-t` specifies the accuracy threshold (lower = more accurate) for the loss. diff-SAT generates models until the value of 
the cost function reaches this threshold and, if `-n` is present, the minimum number of models specified with `-n` has been reached.  
For the meaning of `-mse` see the next section. 

`--solverarg` is used for setting an advanced parameter (here the number of parallel solver threads). Parameters
such as `maxSolverThreadsR` can have a massive influence on solver performance.

The possible formats of input files is described in the following section. To increase memory available to diff-SAT, use, e.g., `-Xms3g -Xmx8g -Xss10m`   

#### Usage ####

##### User API #####

diff-SAT can be used from the commandline or as a library, i.e., using its User API. The User API allows to build enhanced boolean formulas and answer set programs (consisting of various types of rules, including probabilistic and non-ground rules) 
programmatically, to call the solver, and to print and examine the resulting sample. 

(For complex non-ground ASP rules, firstly an aspif file needs to be generated from the answer set program using, e.g., clingo, as preprocessor, then one of the textual input formats described in section [File input formats](#File-input-formats) can be used.)

Entry points for documentation of the User API (/doc/index.html) are classes [input.ProbabilisticAnswerSetProgram](doc/input/ProbabilisticAnswerSetProgram.html)
and [input.BooleanFormulaWithCosts](doc/input/BooleanFormulaWithCosts.html) in package 'input'.

User API example code can also be found in source code file userAPItests.APITests.scala 

##### File input formats #####

Textual file or stdin input is accepted in various forms:

- DIMACS CNF (for plain SAT solving) 

- Enhanced DIMACS CNF with a list of _parameter atoms_ and cost function (loss function) terms appended to the DIMACS part

- Probabilistic DIMACS CNF (PCNF) where each clause can optionally be annotated with a probability

- ASP Intermediate Format (ASPIF), optionally extended with parameter atoms and cost function terms defined using special predicates

- Enhanced ASPIF format with a list of parameter atoms and cost function terms appended to the ASPIF part

- Probabilistic ASP Intermediate Format (PASPIF) with a new probabilistic rule type 

Logic programs need to be grounded into ASPIF format before sending them to diff-SAT. For this, 
[Clingo](https://potassco.org/clingo/) or Gringo can be used as a grounder: 
    
    clingo myProbLogicProg.lp --trans-ext=all --pre=aspif > myDiffSATInputFile.aspif

Observe that Clingo is used here only to generate the ASPIF form of the input program, not for solving; diff-SAT itself doesn't require Clingo 
or any other external Answer set, SAT or SMT solver.  

It is also possible to translate various other constraint and logic languages into ASPIF format and thus 
into a form diff-SAT can in principle work with (e.g., MiniZinc/flatzinc constraint satisfaction problem (CSP) or various action languages) - however, we 
haven't tested this yet. 

##### Cost functions, parameter atoms and measured atoms #####

A diff-SAT cost function is a user-specified differentiable function over so-called _measured variables_. Measured variables
represent the frequencies of _measured atoms_ in the sample. 

Another important concept are _parameter atoms_ (the random variables in our approach). These are those atoms whose truth values 
are varied by differentiable satisfiability. During solving, the cost function is partially differentiated wrt. variables 
which represent individual parameter atoms.  

Parameter and measured atoms are (possibly empty) subsets of the set of all atoms respectively Boolean variables occuring in the input.  

It is up to the user to declare parameter and measured atoms. The set of parameter atoms needs to be explicitly
declared in the input. The set of measured atoms is implicitly given as the set of all variables in the given cost function term.
See examples further below.  

For deductive probabilistic inference, the set of measured atoms and the set of parameter atoms are _identical_. This is
the most efficient situation. If the two sets aren't identical (as in some forms of abductive or inductive reasoning), diff-SAT currently uses a 
finite difference method to approximate the partial derivatives wrt. to the parameter atoms (this
might change in future versions).   
Of course, if there are parameter atoms which aren't measured atoms (i.e., don't appear in the cost function term), the cost function result still needs to depend indirectly from the parameter atoms, as
otherwise searching the parameter space (numerical values of parameter variables) wouldn't have any effect on the loss.  

It is possible to provide multiple cost functions in the input. These are combined into a single cost function 
as a normalized sum (the combination function can be changed using setting `innerCostReductFun` in `sharedDefs.scala`).  

The clauses or rules in the input can state can specify arbitrary logical constraints and dependencies among parameter 
or measured atoms, but of course not all such problems have a solution.  
 
The ASPIF input supported by diff-SAT is a subset of the full ASPIF specification, however, most Answer Set programs (AnsProlog programs), 
including disjunctive programs and programs with variables and typical ASP constructs such as integrity constraints or choice rules, 
can be automatically translated into the supported ASPIF format using a grounding/preprocessing step, see further below in this guide.    

Cost function terms are mathematical expressions which can, besides the usual operators, parentheses and built-in functions such 
as sqrt, log, abs and exp, contain subterms of the form `f(a)` where `a` is an atom, or (in SAT mode) `f(vi)` (where `i` is a Boolean variable).
Some examples are provided in the next sections. The arguments of `f(...)` are the measured atoms.  

By default, diff-SAT stops when the specified cost threshold has been reached. The threshold is set with command line argument `-t` (default: 0.01).  
With switch `--solverarg stopSamplingOnStagnation true` sampling stops when the cost function value doesn't improve significantly anymore.
This is useful in cases where the theoretical cost minimum isn't known or not zero, but with this switch diff-SAT also becomes more easily stuck in a local minimum.  

Cost terms can in principle be arbitrary expressions. A few examples:  

`((0.123-f(a))^2+(0.45-f(b))^2)/2` (mean squared error, MSE)

`(0.12 - f(heads(coin(1))))^2` (MSE inner term; one way to define the prior probability (here: 0.12) of an individual atom (here: `heads(coin(1))`)  

`(0.4 - (f(c) / f(q)))^2` (with `c :- p, q.`, this defines conditional probability Pr(p|q)=0.4)

`sqrt(abs(f(x)-f(y)))+0.5` 

The atoms occurring as arguments of `f()` within these cost terms are measured atoms (because their frequencies `f()` in the sample need to be measured during sampling).

##### Declaring cost functions and parameter atoms in a logic program #####

Since version 0.4.0, cost functions (including measured atoms) and parameter atoms can optionally be declared in logic programming 
syntax using special predicates, without the need to append them to the DIMACS or ASPIF file.  

These special predicates are otherwise ordinary predicates which can even be part of rules. However, diff-SAT recognizes them
as cost/parameter atom definitions only if they appear as facts (at least after grounding).  

- Fact `_pat_(a).` declares that atom `a` is a parameter atom. Multiple such facts can be stated.

- Fact `_cost_("L").` declares that `L` is a term which defines a cost function (or a summand of the overall cost function in case multiple such
cost facts are provided). The term needs to be provided as a string literal. 

- Fact `_pr_(a, p).` declares that the probability of atom `a` is `p`/10000 (/10000 is required since standard ASP cannot directly deal with 
fractions or real numbers). `_pr_(a, p)` is syntactic sugar for `_cost_((p/10000-f(a))^2)` and `_pat_(a)`.  The divisor can be changed (see file `sharedDefs.scala`). 
Multiple `_pr_` facts can be provided.

If of these only `_pr_` facts are provided (i.e., the problem is purely deductive-probabilistic), it is recommended to use diff-SAT
with command line switch `-mse` which activates optimized handling of costs which have the form of inner MSE (Mean Squared Error) terms.  

Note that parameter atoms (the random variables in our framework) need to be logically defined (i.e., occur in some rule head or choice fact) but 
without completely fixing their truth values, as otherwise they couldn't be varied during sampling. A simple way to ensure this is by using a so-called _spanning rule_ of
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

Note that probabilistic programs typically have multiple solutions (probabilities which aren't directly specified falling into intervals) and that the default solution is not necessarily the one with the maximum entropy. Informally, this means that diff-SAT takes a 
time-saving approach and allows itself to make any kinds of assumptions as long as all user-defined constraints (rules and cost terms) 
are satisfied, including random variable dependence assumptions. E.g., with the above code and default settings, the resulting sample encodes Pr(win)=0.5, since diff-SAT manages
to fulfill all given constraints with only two different answer sets (models). A simple way to increase the entropy is to increase the size of the sample using `-n n` where `n` is the number of models that should be sampled. 
 For an even higher entropy, additionally to `-n`, switch `--solverarg diversify true` can be used (however, this switch might slow down sampling).
 `--solverarg diversify true` increases the randomness with which nondeterministic branching literal decisions are made.  
E.g., with the following options, diff-SAT samples 100 models and Pr(win) converges to 0.25:  

    -n 100 --solverarg diversify true --solverarg suppressAnswers true --solverarg showProbsOfSymbols true 

Remark: If the sets of parameter and measured atoms are identical (as above) but the overall cost function 
isn't provided in form of multiple part cost-terms differentiable against one parameter variable each, 
diff-SAT needs to be called with `--solverarg partDerivComplete true` and without switch `-mse`.  

Probabilities (or more generally: parameter or measured variables) can also be associated with entire rules. The basic syntax pattern for probabilistic ground rules is  

    aux:- l1, l2, ..., not h.
    h :- l1, l2, ..., not aux.
    _pr_(aux, 10000-pr).
    
where `aux` is a fresh symbol, `pr` is the desired probability (multiplied with 10000) of rule `h :- l1, l2, ...` and the `l1` etc are literals.
     
More details on this can be found in the second document linked under [References](#references).  

How to associate probabilities with entire clauses in SAT mode can be found further below in README.md under "Probabilistic clauses for DIMACS CNF (PCNF)".  
     
Measured and parameter atoms don't need to overlap, as shown in the following logic program.  
Example (2):  

    _pat_(h).
    
    0{h}1.
    
    e1 :- h.
    e2 :- h.
    e3 :- h.
    
    _cost_("1 - (f(e1) * f(e2) * f(e3))").

With the code above, diff-SAT shall search for a probability of atom `h` (a _hypothesis_) such that the probabilities of example atoms `e`i 
are maximized.  

Here, the set of parameter atoms {`h`} is different from the set of measured atoms {`e1`, `e2`, `e3`}, which the current version of diff-SAT approaches 
using a numerical finite differences approach (diff-SAT automatically selects the most appropriate approach to differentiation and also supports mixed scenarious where some but not all of the parameter variables are measured).  


##### Declaring cost functions and parameter atoms explicitly on DIMACS or ASPIF level #####

Alternatively or in addition to the approach described in the previous section, cost functions and parameter atoms can
also be declared directly as an appendix to a DIMACS-CNF or ASPIF file.  

In the input, multiple cost functions can be defined in lines starting with keyword `cost ` (followed by a space).  
If multiple cost functions are given, their normalized sum is minimized.  

If any cost function is provided, also a (single) list of all parameter atoms needs to be specified in the input. These 
have to be listed in a single line starting with `pats `, with no preceding whitespace and with the `pats ` line preceding 
the cost function declarations.  
 
In SAT-mode only, the names of measured atoms (the atoms referred to in cost function terms) need to be prefixed by character `v`.  

A term of form `f(a)` in a cost function (loss function), where `a` is an atom (a propositional variable whose 
truth value diff-SAT should determine st. the cost is minimized), evaluates during sampling to the frequency of positive 
occurrences of `a` in the sample (count of `a` in all models in the sample, normalized with the total number of models 
in the sample).  

Example (4), for SAT (recommended to use with switch `-mse` which activates optimized handling of costs which have the form of inner MSE (Mean Squared Error) terms):

       p cnf 2 3
       1 -1 0
       2 -2 0
       -1 -2 0
    
       pats 1 2
    
       cost (0.2-f(v1))^2
       cost (0.5-f(v2))^2
       
The costs in the above example specify that literal 1 has probability 0.2 (and its negation -1 has probability 0.8) and that literal 2 has probability 0.5.
If, like above, multiple costs terms are provided, they add up to the overall cost (after normalization with the number of part costs). Such part costs are sometimes called _inner costs_.
The function used for combining the inner costs to the total cost can be changed using setting `innerCostReductFun` in `sharedDefs.scala`.  

Note that in input for SAT, propositional variables _within cost terms_ need to be prefixed by letter `v` (but not in the `pats` line).

The part before line `pats`... is in plain DIMACS-CNF syntax.  
           
Example (5), based on an extended form of ASPIF (for Answer Set Programming). It is recommended to use it with switch `-mse`, since
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
diff-SAT with `--solverarg partDerivComplete true` and without `-mse`. This activates a more general but somewhat less 
efficient differentiation approach:

Example (6):

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

To generate the ASPIF part (the part above `pats`) from a non-ground Answer Set program, preprocess
using, e.g., Clingo's (https://potassco.org/clingo/) preprocessing and grounding capability. 

Example grounder call using [Clingo](https://potassco.org/clingo/) (observe the required `--trans-ext=all` argument): 
    
    clingo myLogicProg.lp --trans-ext=all --pre=aspif > myDiffSATInputFile.aspif

(Observe that Clingo is only used to generate the proper ground form of the input program; diff-SAT itself doesn't require Clingo or any other external Answer set, SAT or SMT solver.)
 
The final input file can then be created by appending the `pats` and `cost` lines (if any) to the ASPIF or DIMACS file, each starting in a new line. 

##### Probabilistic rules in PASPIF (Probabilistic ASPIF) #####

Alternatively to the previous extension of ASPIF files with "pats" and "cost" lines, since version 0.5, diff-SAT also
understands ASPIF format enhanced with a new rule type - _probabilistic rules_.  

Probabilistic rules are defined using aspif statements of the form
    
    1000[space]p[space][rule]

where `[space]` is a single space character and `[rule]` is the aspif format of a normal rule (i.e., there must
be only a single head atom (a positive literal). Choice heads or weight bodies are also not allowed).
`p` is either a double number `0<=p<=1` or -1, the latter denoting that the probability is unknown (informally
meaning 'rule v not rule', i.e., a so-called _spanning rule_ [Nickles,Mileo 2015]).  

**Important**: it is the user's responsibility (or the responsibility of some higher-level tool which generates the paspif file) to ensure that the probabilistic weight is possible (compatible with
other probabilities defined or implied by the probabilistic logic program and with the axioms of probability) and that all literals in the probabilistic rule are properly defined. E.g., if 
rule `p :- u,v` (using symbols instead of numeric aspif literals for clarity) is assigned probability 0.5 but `u` or `v` are undefined, the rule has actually probability 1 and thus
the probabilistic logic program represented by the paspif file is inconsistent (in which case sampling doesn't terminate unless a meaningless error threshold or an upper bound for the number of models is specified). 
 
Examples: the following paspif rule statement declares are normal probabilistic rule with probability 0.5,
head atom 63 and body literals 67 and -62: 
    
    1000 .5 1 0 1 63 0 2 67 -62
    
The next paspif statement is a spanning rule which specifies that rule `63 :- 67,62` is uncertain but without
quantifying the uncertainty:   
 
    1000 -1 1 0 1 63 0 2 67 -62
    
Remark: a statement of the form
    
    1000 -1 1 0 1 h 0 0
    
has the same semantics as an aspif statement representing choice rule `{ hs }` where `hs` is a symbol representing aspif literal `h`.

##### Probabilistic clauses for DIMACS CNF (PCNF) #####

Alternatively to the previous formats, input is also accepted in an extension of the DIMACS CNF format (called _Probabilistic CNF_ or PCNF) where each
clause can optionally be prefixed by a real number p which specifies the probability of the clause, 0 < p < 1, followed by whitespace. The number **must** contain a decimal point ('.').  

In the DIMACS CNF "problem" line `p cnf nvar nclauses`, `cnf` needs to be replaced with `pcnf`.  

The annotated clause syntax is treated in diff-SAT as syntactic sugar for a set of clauses which define a fresh Boolean variable which is logically equivalent to 
the annotated clause and which is declared a parameter atom. Also, a cost function line of the form `cost (p-f(vp))^2` is generated for each weighted clause
where `p` is the clause probability and `vp` is the fresh Boolean variable.  

Remark: the clause weights are interpreted as probabilities and implemented using cost functions. This means that a weight of 1.0 
represents "almost surely" (if the accuracy threshold is set to 0), i.e., it does _not_ guarantee that the respective clause holds in literally _every_ model, and conversely, a weight of 0.0 does not guarantee that the respective clause holds in no models.  

Example (7):

    c An example for probabilistic conjunctive normal form (omit preceding whitespace in lines)
    p pcnf 6 4
    0.65 1 -2 3 0
    4 5 0
    0.7 6 0
	0.92 -1 3 0
    
This example defines that clause v1 v -v2 v v3 has probability 0.65, that the probability of -v1 v v3 is 0.92 and Boolean variable v6 has probability 0.7 (and that -v6 has probability 0.3). Cost functions and
auxiliary Boolean variables and their declaration as parameter atoms are automatically generated for these weighted clauses. Clause v4 v v5 is a regular ("hard") clause which must always hold.   
    
Remark: diff-SAT doesn't solve the PSAT problem (as it doesn't check whether or not the PCNF input has a solution). But
it can be used to generate PSAT solutions _if they exist_. The formula which diff-SAT actually checks for SAT/UNSAT is the plain Boolean formula where all weighted clauses
are subsituted by unweighted clauses which define the parameter variables which are equivalent to the respective weighted clauses without their weights.

##### Performing ad hoc queries #####

diff-SAT is just a solver and sampler, and as such it doesn't contain a real query tool (a tool which computes from the sample the probabilities of user-specified query formulas). However, there are several ways built into diff-SAT for 
performing simple types of queries.   

Most simply, with switch `--solverarg showProbsOfSymbols true` diff-SAT prints the probabilities of all symbols (ground atoms) in the program,
by summing up the probabilities (frequencies) of those models in the sample which contain the respective atom.  

Secondly, Scala variables `adHocConjunctiveQueries`, `adHocDisjunctiveQueries` and `adHocRuleQueries` can be used to specify 
queries consisting of conjunctions, disjunctions or normal rules consisting of ground literals. See file `sharedDefs.scala` for details and `APITests.scala` for a few examples for how to use them with the User API.   

Thirdly, `_eval_("term","?")` is a pseudo-predicate which, if stated as a fact in the input program, makes diff-SAT instantiate `"?"` with
the numerial value of the given term. The term has the same syntax as the terms in cost functions.   

A simple example: The following probabilistic logic program specifies a conditional probability Pr(p|q) = 0.4 and uses `_eval_` to let diff-SAT 
(after grounding the program to ASPIF format) print the actual conditional probability (multiplied with 1000) achieved by sampling (ideally `_eval_("f(num)/f(q)",4000)`, with accuracy depending on threshold, e.g., `-t 0.001`).  

Example (8):

    0{p}1.
    0{q}1.    
    num :- 2{p;q}2.  % num is true iff both p and q are true
    
    _cost_("(0.4 - (f(num) / f(q)))^2").   % we specify the conditional prior probability Pr(p|q) = 0.4
    
    _pat_(num).
    _pat_(q).
    
    _eval_("f(num) / f(q)", "?").  % queries Pr(p|q)
    _eval_("f(p)", "?").           % queries marginal probability Pr(p)

Observe that `_eval_`, like `_cost_`, `_pr_` and `_pat_`, isn't a proper predicate, it cannot be used in the body of a rule (more precisely, it syntactically can, but then the `"?"` as second argument isn't resolved).

##### Probabilistic inference without cost functions #####

Perhaps notably, diff-SAT can also be used for probabilistic inference even if no cost function or parameter atoms are present, provided the 
random variables (nondeterministic atoms) are mutually independent.  

Example (9):

    0{heads(1)}1.  % nondeterministic atom. 0{x}1 means that x is part of the answer set or not.
    0{heads(2)}1.
    win :- heads(1), heads(2).

After grounding the program to ASPIF format and with diff-SAT arguments `-n 100 --solverarg showProbsOfSymbols true --solverarg diversify true` , diff-SAT returns values
roughly around Pr(heads(1)) ≈ 0.5, Pr(heads(2)) ≈ 0.5, Pr(win) ≈ 0.25. `--solverarg diversify true` isn't strictly necessary,
but helps achieving a more uniform mix of `heads(1)`, `heads(2)` in the sample.  

How this approach can be used to specify _arbitrary_(!) probabilities (in form of fractions) of mutuably independent probabilistic facts using a _plain_ answer set program is described in  
[Matthias Nickles, Alessandra Mileo (2014): Probabilistic Inductive Logic Programming Based on Answer Set Programming. In Proceedings of the 15th International Workshop on Non-Monotonic Reasoning (NMR'14)](https://arxiv.org/pdf/1405.0720.pdf) (end of Section 4). However,
this approach is suitable only for small problems, due to the very large number of models that need to be generated to obtain reasonably accurate results.

#### Miscellanea ####

- diff-SAT can be used with most types of logic programs supported by modern answer set solvers (including Disjunctive Logic Programs) but such programs 
might require a preceeding preprocessing and grounding step as explained above.

- For using First-Order Logic (FOL) syntax (under stable model semantics) with diff-SAT, preprocess your first-order formulas using a tool such as [fol2asp](https://github.com/MatthiasNickles/fol2asp) or [F2LP](http://reasoning.eas.asu.edu/f2lp/).

- diff-SAT is not a solver for (weighted) Max-SAT or Min-SAT, nor for finding individually optimal models or an optimality ranking of 
individual models (these problem categories might be supported in a future version).

- diff-SAT is also not a Stochastic Local Search (SLS) solver (such as WalkSAT), although it includes a simple WalkSAT implementation for
speeding up regular CDCL/CDNL-style SAT solving during so-called rephasing.

- In the case where the costs express probabilities of propositional variables (or, by straightforward extension, formulas, as in PSAT), 
the input to diff-SAT is similar to the normal representation format used for PSAT (probabilistic satisfiability problem) instances, 
so consistent PSAT problem instances are in principle feedable into diff-SAT in order to sample satisfying probabilistic models. However, note that 
PSAT is a different problem and diff-SAT doesn't check the satisfiability of probability assignments (except for the Boolean 
satisfiability of "hard" clauses), at least not directly (see remarks about termination and non-termination further below).  
Also note that diff-SAT's semantics and purpose are different from SSAT (Stochastic Boolean Satisfiability).

- While in principle usable with any kind of differentiable cost function(s), MSE-style costs receive optimized treatment with 
command line switch -mse. With that switch, list the instantiated inner MSE terms (of form (wi-f(vari))^2) 
individually instead of providing a single long MSE formula. diff-SAT minimizes then the expression (innerCost1+...+innerCostN)/n.

- diff-SAT is not (or only very remotely) related to SGDB (Stochastic Gradient Descent Branching Heuristic, in Jia Hui Liang: 
Machine Learning for SAT Solvers, 2018). Whereas SGDB provides a branching heuristics for finding decision variables which increase 
the likeliness of _conflicts_ (and thus the CDCL conflict clause learning rate) and thus improves regular SAT solving performance, 
diff-SAT's gradient descent-style branching heuristics aims at minimizing a user-defined loss function.

- For certain cost functions, you might need to provide switch --solverarg "partDerivComplete" "true" which activates a 
differentiation approach which is more general than the (faster) default approach. diff-SAT shows a message in case 
the default approach isn't usable.

- If diff-SAT doesn't seem to terminate, the most likely reasons are that no solution exists because of a probabilistic inconsistency (impossible or conflicting weights) in the provided input,
or, in case of a non-convex cost function, the solver got stuck in a local minimum. There is currently no way to let diff-SAT check for probabilistic (weight) inconsistencies and termination with #models >= 1 doesn't guarantee weight consistency since diff-SAT 
only samples until convergence to a certain threshold or until cost stagnation (however, each individual model in the sample is an exact model of the input SAT/ASP formula/logic program).  
Another possible reason for nontermination could be a convergence threshold which is too low (it's in principle not possible to reach arbitrary accurary) - in that 
case an increase of the threshold (specified with command line argument -t) should solve the problem.  
Other common reasons are forgotten parameter atom declarations (e.g., using `_pat_(atom).` facts if the input is a logic program) or typos in the cost term.  

- diff-SAT doesn't require any assumptions about independence of variables (random events).

- diff-SAT is not designed as a tool for sampling from the _uniform_ (or a near-uniform) distribution over models, but it supports model set diversification 
with `--solverarg diversify true`, and diff-SAT can also be used with arbitary discrete probabiltities (including uniform ones) associated with individual models 
using suitable cost functions.

- To increase the entropy of the sample, increase the number of models in the sample using parameter `-n`. To further increase the sample entropy, switch `--solverarg diversify true` can be used, but it slows down sampling.
To *de*crease models entropy, use switch `--solverarg diversifyLight false` with `-n -1`.

- every individual model returned by diff-SAT is a precise model of the input clauses or rules (except in PCNF, where the weighted clauses are 
syntactic sugar and are replaced with other clauses), that is, not different from a model returned 
by a conventional SAT or ASP solver. Uncertainty is modelled only on the level of multiple models by identifying models with possible worlds 
and their frequencies in the sample with possible world probabilities.  

- diff-SAT never guarantees that the models it prints are different from each other, as sampling is with replacement (so the resulting lists of
answer sets or propositional models are not duplicate free enumerations as those returned by, e.g., MiniSat, clingo/clasp or smodels). 
`--solverarg diversify true` just increases the amount of randomness in the selection of decision literals.

- The mixture of multiple samples obtained from multiple diff-SAT calls doesn't have a (known) meaningful semantics,
unless the input problem has only a single distribution as its multisolution (in which case repeated calls with 
`-s` all sample from this distribution). To sample `n` models, use a single diff-SAT call with switch `-n n`.

- If with older versions of Windows diff-SAT's status updates in the console scroll instead of being updated in place, try with flipped value of diffSAT.changeConsoleWidthUnderWin

#### Author contact details ####

Matthias Nickles 

matthiasDOTnicklesATgmxDOTnet

https://www.researchgate.net/profile/Matthias_Nickles

Feedback and bug reports are welcome!

#### diff-SAT Copyright & License ####

Copyright (c) 2018-2021 by Matthias Nickles

License: [MIT license](https://github.com/MatthiasNickles/diff-SAT/blob/master/LICENSE)

#### Dependencies ####

diff-SAT uses the following third-party libraries, besides the Java and Scala standard libraries:

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

- Apache Commons Math (https://commons.apache.org/proper/commons-math/)  
  License: https://github.com/apache/commons-math/blob/master/LICENSE.txt 
  
- jsoniter (https://jsoniter.com/)  
  Copyright (c) 2016 Tao Wen
  License: https://github.com/json-iterator/java/blob/master/LICENSE

   
