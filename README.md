# `RInGen:` Regular Invariant Generator
RInGen is a [SMTLIB2](http://smtlib.cs.uiowa.edu/language.shtml) converter.
It takes arbitrary SMTLIB2 files as input and
generates [Horn clauses](https://chc-comp.github.io/format.html) over
pure [algebraic datatypes](https://en.wikipedia.org/wiki/Algebraic_data_type) in SMTLIB2 and Prolog.
It can optionally run a number of CHC and other solvers over output clauses, currently:
[Z3](https://github.com/Z3Prover/z3),
[Eldarica](https://github.com/uuverifiers/eldarica),
[CVC4 in finite model find mode](https://cvc4.github.io/papers/cav2013-fmf),
[CVC4 in inductive mode](http://lara.epfl.ch/~reynolds/VMCAI2015-ind/),
[VeriMAP (for inductively defined data types)](https://fmlab.unich.it/iclp2018/),
[Vampire](https://vprover.github.io/).

## Features
- [x] Supports extra `(lemma P *args* *lemma-expr*)` syntax (see, e.g., `samples/lemmas_with_new_syntax.smt2`).
- [x] Supports `define-fun`, `define-fun-rec` and `define-funs-rec` translation to
predicates
  - [x] Functions are translated to predicates with a supplementary return-argument
  - [x] `let` and `match` expressions are eliminated
- [x] Supports instantiation of the free sorts (declared with `declare-sort`)
  to Peano `Nat` algebraic datatype
- [x] Supports `Int` sort substitution with Peano `Nat` algebraic datatype
  - [x] Supports `Int` operations translation to predicates over `Nat`:
    `-`, `+`, `*`, `mod`, `div`, `<`, `<=`, `>`, `>=`
- [x] Supports ADT selectors and testers translation to clauses

## Requirements
- [`.NET core >= 3.1`](https://dotnet.microsoft.com/download/dotnet/3.1)
- (optionally, to run solvers) `z3`, `eldarica`, `cvc4`, `VeriMAP-iddt`, `vampire` executables accessible
in the environment

## Build
`~/RInGen$ dotnet build -c Release RInGen.sln`
### Build standalone version (for specific platform from the [list](https://raw.githubusercontent.com/dotnet/runtime/main/src/libraries/Microsoft.NETCore.Platforms/pkg/runtime.json))
`dotnet publish -c Release -r <RID> -p:PublishReadyToRun=true RInGen.sln`

Executable then can be found in the `~/RInGen/bin/Release/net5.0/<RID>/publish` folder.

## Run
### Standalone version
```bash
~$ unzip /path/to/standalone-<RID>.zip -d RInGen
~$ cd RInGen
~/RInGen$ ./RInGen ..arguments..
```
### .NET crossplatform version
```bash
~$ unzip /path/to/dotnet-build.zip -d RInGen
~$ cd RInGen
~/RInGen$ dotnet RInGen.dll ..arguments..
```
### Built from sources
```bash
~/RInGen$ dotnet bin/Release/net5.0/RInGen.dll ..arguments..
```

## Modes and Options
### General
#### `-q`, `--quiet`
Quiet mode. Only outputs are `sat`, `unsat`, `unknown` when in `solve` mode or nothing when in `transform` mode.
#### `--timelimit`
Time limit for transformation and/or solving, in seconds (default `300`).
#### `-o`, `--output-directory` `PATH`
A **full** path `PATH` to an output path where to put auxiliary files (default: same as input).
Treated as a directory if ends with a directory separator (e.g., /).
Otherwise, treated as a file.
#### `--help`
#### Common for both transformation and solving: `/FULL/PATH`
Specifies **full** path to either a single SMTLIB2 file or a directory.
If `/FULL/PATH.smt2` leads to a file and the `--output-directory` flag is not specified,
the tool will generate Horn clauses in SMTLIB2 format and save them at `/FULL/PATH.*.0.smt2`.
Otherwise if `/FULL/PATH.smt2` leads to a directory,
the tool will recursively traverse the directory and process all `.smt2` files.

### `transform (--mode MODE) /FULL/PATH --transform-options <transform-options>`
Only transform input files, do not run any solvers.
#### `-m`, `--mode` `<original|freesorts|prolog>`
If `original` is specified, saves as `smt2` with ADTs.

If `freesorts` is specified, saves as `smt2` with all algebraic datatypes transformed into sorts.
Specifically, each ADT sort declaration with `declare-datatypes` is substituted with
`declare-sort` for ADT sort and a number of `declare-fun` declarations for constructors.

If `prolog` is specified, saves as `pl` Prolog problem.

Default: `original`.

### `solve (--table) --solver SOLVER_NAME (--in) (--path /FULL/PATH) (--transform-options <transform-options>)`
Process input files and run one (or many) solvers.
#### `--table`
Generate a solver run statistics table. Useful after running several solvers.
#### `--solver`, `-s` `SOLVER_NAME`
Run a specific solver after processing. Available options:
- [Z3](https://github.com/Z3Prover/z3) (`z3`)
- [Eldarica](https://github.com/uuverifiers/eldarica) (`eldarica`)
- [CVC4 in finite model find mode](https://cvc4.github.io/papers/cav2013-fmf) (`cvc_fmf`)
- [CVC4 in inductive mode](http://lara.epfl.ch/~reynolds/VMCAI2015-ind/) (`cvc_ind`)
- [VeriMAP (for inductively defined data types)](https://fmlab.unich.it/iclp2018/) (`verimap`)
- [Vampire in SMTLIB2 mode](https://vprover.github.io/) (`vampire`)
- all the above solvers (`all`)
> Note that in order to run `Z3`, `Eldarica`, `CVC4`, `Vampire` and `VeriMAP` one should have
> `z3`, `eld`, `cvc4`, `vampire` and `VeriMAP-iddt` executables accessible in the environment.
> The easiest way to do that is to prefix tool running with:
>
> `env 'VeriMAP-iddt=/FULL/PATH/TO/VeriMAP-iddt-linux_x86_64/VeriMAP-iddt'`
#### `--in`
Interactive mode: reads `smt2` commands from stdin.
Runs solver on `(check-sat)` SMTLIB2 command.
#### `--path /FULL/PATH`
Noninteractive mode: read `smt2` commands from specified path (file or directory)
#### `--transform-options <transform-options>`
Transformation options to be performed before solving

### A list of `<transform-options>`
#### `--tip`
Convert [TIP-like](https://tip-org.github.io/) systems to Horn clauses.
This flag makes the tool treat all `assert`ions as **queries**, meaning that
they are transformed to the following form:
```(assert (forall ... (=> .. false)))```
#### `--sync-terms`
Synchronize ADT terms of a CHC system by making all user predicates unary and introducing new predicates and combined ADT declarations.
User predicate with signature `S1 * ... * Sn` will become a unary predicate over fresh ADT sort `S1...Sn`.
Term synchronization is hardcoded (like in TATA): left subterm is synchronized with left subterm, right with right, etc.

## Examples
### Convert benchmarks from `DIRECTORY` into SMTLIB2 Horn clauses
`$ ringen transform /FULL/PATH/TO/DIRECTORY`

Obtained clauses are in the `/FULL/PATH/TO/DIRECTORY.Original` folder.

### Convert benchmark into Horn clauses and run Z3 over the result with timelimit 5 sec
`$ ringen --timelimit 5 solve --solver z3 --path .../samples/one-zeroary-constr.smt2 -t`

Obtained clauses are in the `.../samples/one-zeroary-constr.Original.smt2` file.

Result of the `z3` run will be output to `.../samples/one-zeroary-constr.Original.Z3.smt2` file.
For `one-zeroary-constr` example it will contain four lines:

| Result file line | description                   |                 |
|------------------|-------------------------------|-----------------|
| 0                | rounded transformed file size | in kilobytes    |
| 13176            | solver run memory             | in kilobytes    |
| 0                | solver run time               | in milliseconds |
| SAT ElemFormula  | solver result                 | `<solver result>` |

#### `<solver result>` type
Has SMTLIB2 status (`sat`, `unsat`,..) and *invariant representation type* if status is `sat`.

### Use the finite-model finder in CVC4 as an ADT Horn-solver on a TIP benchmark
`$ ringen --quiet solve --solver cvc_fmf --path .../samples/prop_20.smt2 -t --tip`

The output is `sat`.

### Use the finite-model finder in CVC4 as an ADT Horn-solver in *interactive mode*
`$ ringen --quiet solve --solver cvc_fmf --in -t`

For example, one can copy-paste `samples/lemmas_with_new_syntax.smt2` line-by-line obtaining:
```
smt2> (set-logic HORN)
smt2> (declare-datatypes ((Nat 0)) (((Z) (S (unS Nat)))))
smt2> (declare-fun P (Nat) Bool)
smt2> (lemma P ((x Nat)) (= x Z))
smt2> (lemma P ((y Nat)) (= y (S (S Z))))
smt2> (assert (forall ((x Nat)) (=> (= x Z) (P x))))
smt2> (assert (forall ((x Nat)) (=> (P x) (P (S (S x))))))
smt2> (assert (forall ((x Nat)) (=> (and (P x) (= x (S Z))) false)))
smt2> (check-sat)
sat
smt2> 
```

One could also omit the `--quiet` flag to obtain more verbose output (with locations of auxiliary files).
