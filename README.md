# smtx

My first SMT solver! *yay*

It can solve pure SAT problems in DIMACS or SMT-LIB format and also supports the theory QF_UF of quantifier-free uninterpreted functions and equalities.

Only QF_UF theory is supported at the moment. The decision procedure is still very inefficient, compared to state-of-the-art solvers. SMT-LIB support is rather quick'n'dirty.

Caution! This is experimental software. Do not use in production. There are plenty of really good solvers such as [z3](https://github.com/Z3Prover/z3) and [CVC-4](https://cvc4.github.io/) and [Yices](https://github.com/SRI-CSL/yices2) for that.

Nevertheless, technically it's already a true SMT solver.

### Building and testing

This project uses the so-called Haskell Tool Stack, which is a relatively new build and dependency management system for GHC.
To get started, just install stack and it will download its own copy of GHC initially, and install project specific dependencies
to a work folder inside the project folder. There is no need to install any other Haskell dependencies through your distro.

#### Run unit test suite:

Run test suite with coverage (using a different work-dir so you can run it concurrently with other stack processes):

```
stack --work-dir .stack-work-test build --test --coverage
```

```
stack --work-dir .stack-work-test test --coverage && stack --work-dir .stack-work-test hpc report smtx
```

#### Validate further:

Run against z3 on all files in resources/ (put any number of SMT-LIB2 and DIMACS files there*):

```
stack build
```

```
python3 compare.py
```

*There are a lot of sample problems on the web. Instances from past SMT competitions can be obtained [here](https://www.starexec.org/starexec/secure/explore/spaces.jsp?id=295650), Boolean SAT instances [here](http://www.satcompetition.org/).

#### Run benchmarks:

```
stack bench --benchmark-arguments "--output bench.html"
```

#### Run it on a specific problem!

There's a built-in help message:

```
stack exec smtx -- -h
```

### Hacking

Sometimes it's necessary to explicitly re-run `stack build` or even `stack clean` after changes (with the correct work-dir
parameter), as it doesn't always reliably pick up on changes.
