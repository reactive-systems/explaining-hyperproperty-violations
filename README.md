# Explaining Hyperproperty Violations

## Introduction

This python library computes explanations for counterexamples to hyperproperties described in the specification logic HyperLTL.
Hyperproperties relate multiple computation traces to each other. Model checkers for hyperproperties thus return, in case a system model violates the specification, a set of traces as a counterexample. Fixing the erroneous relations between traces in the system that led to the counterexample is a difficult manual effort that highly benefits from additional explanations.

## Requirements
- [Python](https://www.python.org) (tested with v3.7)
- [PyAiger](https://github.com/mvcisback/py-aiger) (tested with v6.1.23)
- [Graphviz](https://graphviz.org/) (tested with v2.42.2-5)
- [PyGraphviz](https://pygraphviz.github.io/) (tested with v1.9)
- [SATisPy](https://github.com/netom/satispy) (tested with v1.1b1)
- [PySAT](https://pysathq.github.io/) (tested with v0.1.7.dev16)
- [spot](https://spot.lrde.epita.fr/) (tested with v2.10.4)

## Installation

To install the python package as well as the python requirements above, run:

```
git clone https://github.com/reactive-systems/explaining-hyperproperty-violations.git
cd explaining-hyperproperty-violations
pip install .
```

In addition to the python requirements above, the LTL, automata manipulation and model checking library [Spot](https://spot.lrde.epita.fr) is required. Please follow the [download and installation instructions](https://spot.lrde.epita.fr/install.html) on their website.

## Usage

The input is
- a HyperLTL specification as a string in the MCHyper (<https://github.com/reactive-systems/MCHyper>) format provided with `-f`
- system given as DOT (.dot) and Aiger (.aag) provided with `-stateMachine` and `-aag` respectively
- and a MCHyper counterexample (.cex) provided with `-cex`

The output is
- a cause explaining the hyperproperty violation
- and a set of all minimal causes.

Example data is provided in `/examples`. The examples are taking from the CAV'22 paper of the same name. In general, any MCHyper counter example file and every Aiger file and its .dot representation work (see [aiger2dot](https://github.com/arminbiere/aiger)).
```
cd examples
python ../explainhyper/explain_hyper.py -aag asymmetric_arbiter.aag -cex asymmetric_arbiter.cex -f "Forall (Forall (Implies (G (And (Eq (AP \"req_0\" 0) (AP \"req_0\" 1)) (Eq (AP \"req_1\" 0) (AP \"req_1\" 1)))) (G (And (Eq (AP \"grant_0\" 0) (AP \"grant_0\" 1)) (Eq (AP \"grant_1\" 0) (AP \"grant_1\" 1))))))" -outName "tmp" -stateMachine "asymmetric_arbiter.dot"
```

The command line output is structured as follows:
```
Size of the counter example:
Size of the formula:
Causes:
Time (in s) to compute this set of causes:
All minimal causes:
Number of minimal causes:
Time (in s) to compute all causes:
```
Where a cause is given as a tuple (name of AP, time step, truth value, trace belonging). For more information about notation and algorithmic details, please see the corresponding paper.

## Further Usage

The library can be used on top of the existing Hyperproperty model checking tool MCHyper to provide meaningful explanations. The library is flexible enough to incorporate further development progress and support hyperproperty model checking tools developed in the future.

## How to cite
```
@inproceedings{explaining-hyperproperty-violations,
    title     = {Explaining Hyperproperty violations},
    author    = {Norine Coenen, Raimund Dachselt, Bernd Finkbeiner, Hadar Frenkel, Christopher Hahn, Tom Horak, Niklas Metzger, and Julian Siber},
    booktitle = {34th International Conference on Computer Aided Verification (CAV 2022), to appear},
    year      = {2022}
}
```
