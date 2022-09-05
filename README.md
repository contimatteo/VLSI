# Very Large Scale Integration Project

This project describes a Combinatorial Optimization approach to the VLSI problem. In particular, four different technologies have been implemented to address the problem at hand, namely Constraint Programming (CP), propositional Satisfiability (SAT), Satisfiability Modulo Theories (SMT) and Linear Programming (LP).


<!-- -------- --------------------------------------------------------------------------------- -->


## Introduction
*VLSI (Very Large Scale Integration) refers to the trend of integrating circuits into silicon chips. A typical example are systems on a chip for smartphones. The modern trend of shrinking transistor sizes, allowing engineers to fit more and more transistors into the same area of silicon, has pushed the integration of more and more functions of cellphone circuitry into a single silicon die (i.e. plate). This enabled the modern cellphone to mature into a powerful tool that shrank from the size of a large brick-sized unit to a device small enough to comfortably carry in a pocket or purse, with a video camera, touchscreen, and other advanced features.*


### Documentation
You can find the report of the project [here](./report.pdf).

You can find the notebook with all the results [here](./notebooks/plots.ipynb).


<!-- -------- --------------------------------------------------------------------------------- -->


## Installation
Below you can find all the scripts for installing based on your OS/processor
```
$ make
    > "+------------------------------------------------------+"
    > "|         OS         |  Hardware  |    Setup Command   |"
    > "+------------------------------------------------------+"
    > "|   Windows/Linux    |   + CPU    |  'make setup.CPU'  |"
    > "|    Apple macOS     |    + M1    |  'make setup.M1'   |"
    > "|    Apple macOS     |    - M1    |  'make setup.CPU'  |"
    > "+------------------------------------------------------+"
```
for instance, if you have MacOS with Intel chip you have to run:
```
$ make setup.CPU
```
or alternatively you can find all the different version of the `requirements` inside the `/tools/requirements` folder.


<!-- -------- --------------------------------------------------------------------------------- -->


## Running the Tests

### CP
```
$ python src/CP.py -h
   usage: CP.py [-h] --data DATA
                [--model {base,rotation,rotation.search,rotation.symmetry,rotation.search.symmetry,search,symmetry,search.symmetry}]
                [--solver {Chuffed,Gecode}] [--sol SOL] [--verbose {0,1,2}] 
                [--plot] [--time TIME] [--stats] [--debug]

    CP solver of VLSI problem.

    optional arguments:
        -h, --help                  show this help message and exit
        --data DATA                 name of txt data file
        --model {...}               name of the model to use
        --solver {Chuffed,Gecode}   name of the solver to use
        --sol SOL                   max no. of solutions
        --verbose {0,1,2}           print execution verbose infos
        --plot                      show final solutions plot
        --time TIME                 computation (seconds) time limit
        --stats                     prints execution statistics infos
        --debug                     prints development debug infos
```

In order to easily run the solver on all the instances, you have to run:
```
$ sh scripts/CP.sh
```

### SAT

```
$ python src/SAT.py -h
    usage: SAT.py [-h] --data DATA 
                  [--model {base,rotation}] [--sol SOL] [--plot] [--time TIME]
                  [--debug] [--search {linear,binary}] [--symmetry] [--cumulative]

    SAT solver of VLSI problem.

    optional arguments:
        -h, --help                show this help message and exit
        --data DATA               name of txt data file
        --model {base,rotation}   name of the model to use
        --sol SOL                 max no. of solutions
        --plot                    show final solutions plot
        --time TIME               computation (seconds) time limit
        --debug                   prints development debug infos
        --search {linear,binary}  makespan search strategy
        --symmetry                add symmetry constraints
        --cumulative              add cumulative constraint on both x and y
```

In order to easily run the solver on all the instances, you have to run:
```
$ sh scripts/SAT.sh
```

### SMT

```
$ python src/SMT.py -h
```

In order to easily run the solver on all the instances, you have to run:
```
$ sh scripts/SMT.sh
    usage: SMT.py [-h] --data DATA 
                  [--model {base,rotation}] [--sol SOL] [--plot] [--time TIME] 
                  [--debug] [--search {linear}] [--symmetry] [--cumulative]

    SMT solver of VLSI problem.

    optional arguments:
        -h, --help                show this help message and exit
        --data DATA               name of txt data file
        --model {base,rotation}   name of the model to use
        --sol SOL                 max no. of solutions
        --plot                    show final solutions plot
        --time TIME               computation (seconds) time limit
        --debug                   prints development debug infos
        --search {linear}         makespan search strategy
        --symmetry                add symmetry constraints
        --cumulative              add cumulative constraint on both x and y
```

### ILP

```
$ python src/ILP.py -h
```

In order to easily run the solver on all the instances, you have to run:
```
$ sh scripts/ILP.sh
    usage: ILP.py [-h] --data DATA 
                  [--model {base,rotation}] [--sol SOL] [--plot]
                  [--time TIME] [--stats] [--debug] [--search {simplex}]

    ILP solver of VLSI problem.

    optional arguments:
        -h, --help                show this help message and exit
        --data DATA               name of txt data file
        --model {base,rotation}   name of the model to use
        --sol SOL                 max no. of solutions
        --plot                    show final solutions plot
        --time TIME               computation (seconds) time limit
        --debug                   prints development debug infos
```


<!-- -------- --------------------------------------------------------------------------------- -->


## References
Libraries:
 - [*minizinc*](https://github.com/MiniZinc/libminizinc)
 - [*z3*](https://github.com/Z3Prover/z3)
 - [*docplex*](https://github.com/IBMDecisionOptimization/docplex-examples)


<!-- -------- --------------------------------------------------------------------------------- -->


## Authors
- **Matteo Conti** - [GitHub](https://github.com/contimatteo)
- **Davide Sangiorgi** - [GitHub](https://github.com/DavideSangiorgi)
- **Riccardo Falco** - [GitHub](https://github.com/falric05)
- **Leonardo Monti** - [GitHub](https://github.com/LeonardoM999)


<!-- -------- --------------------------------------------------------------------------------- -->


## License

This project is licensed under the MIT License - see the [LICENSE.md](LICENSE.md) file for details
