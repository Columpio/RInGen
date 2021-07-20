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
### `transform (--tip) (--sorts) (--quiet) (--output-directory PATH) /FULL/PATH`
Only process input files, do not run any solvers.

### `solve (--tip) (--keep-exist-quantifiers) (--timelimit SECONDS) (--quiet) (--output-directory PATH) SOLVER_NAME /FULL/PATH`
Process input files and run one (or many) solvers.

## Shared options for both modes
### `/FULL/PATH`
Specifies **full** path to either a single SMTLIB2 file or a directory.
If `/FULL/PATH.smt2` leads to a file and the `--output-directory` flag is not specified,
the tool will generate Horn clauses in SMTLIB2 format and save them at `/FULL/PATH.*.0.smt2`.
Otherwise if `/FULL/PATH.smt2` leads to a directory,
the tool will recursively traverse the directory and process all `.smt2` files.

### `-o`, `--output-directory` `PATH`
A **full** path `PATH` to an output **directory** where to put a transformed file (default: same as input).

### `--tip`
Convert [TIP-like](https://tip-org.github.io/) systems to Horn clauses.
This flag makes the tool treat all `assert`ions as **queries**, meaning that
they are transformed to the following form:
```(assert (forall ... (=> .. false)))```

### `-q`, `--quiet`
Quiet mode. Only outputs are `sat`, `unsat`, `unknown` when in `solve` mode or nothing when in `transform` mode.

### `--help`, `--version`

## `transform` options
### `--sorts`
After all other translation the following will be performed:
all algebraic datatypes are transformed into sorts.
Specifically, each ADT sort declaration with `declare-datatypes` is substituted with
`declare-sort` for ADT sort and a number of `declare-fun` declarations for constructors.
This preprocessing step is required to run the finite-model finder.

## `solve` options
### `-e`, `--keep-exist-quantifiers`
Proceed to solving even if there are existential quantifiers after transformation. By default this option is disabled and `RInGen` will return `unknown` if existentials appeared after transformation.
### `SOLVER_NAME`
Run a specific solver after processing. Available options:
- [Z3](https://github.com/Z3Prover/z3) (`z3`)
- [Eldarica](https://github.com/uuverifiers/eldarica) (`eldarica`)
- [CVC4 in finite model find mode](https://cvc4.github.io/papers/cav2013-fmf) (`cvc4f`)
- [CVC4 in inductive mode](http://lara.epfl.ch/~reynolds/VMCAI2015-ind/) (`cvc4ind`)
- [VeriMAP (for inductively defined data types)](https://fmlab.unich.it/iclp2018/) (`verimap`)
- [Vampire in SMTLIB2 mode](https://vprover.github.io/)
- all the above solvers (`--solver all`)
> Note that in order to run `Z3`, `Eldarica`, `CVC4`, `Vampire` and `VeriMAP` one should have
> `z3`, `eld`, `cvc4`, `vampire` and `VeriMAP-iddt` executables accessible in the environment.
> The easiest way to do that is to prefix tool running with:
> 
> `env 'VeriMAP-iddt=/FULL/PATH/TO/VeriMAP-iddt-linux_x86_64/VeriMAP-iddt'`

### `-t`, `--timelimit`
Time limit for the specified `--solver`, in seconds (default `300`).
 
### `-f`, `--force`
Force transformed file generation. If omitted, no transformation will be performed if other transformed file already exist in the output directory.

## Examples
### Convert benchmarks from `DIRECTORY` into Horn clauses
`~/RInGen$ dotnet bin/Release/net5.0/RInGen.dll transform /FULL/PATH/TO/DIRECTORY`

Obtained clauses are in the `/FULL/PATH/TO/DIRECTORY.Transformed` folder.

### Convert benchmark into Horn clauses and run Z3 over the result with timelimit 5 sec
`~/RInGen$ dotnet bin/Release/net5.0/RInGen.dll solve --timelimit 5 z3 ~/RInGen/samples/one-zeroary-constr.smt2`

Obtained clauses are in the `~/RInGen/samples/one-zeroary-constr.Z3.0.smt2` file.

Result of the `z3` run will be output to `stdout`. For `one-zeroary-constr.Z3.0.smt2` example it is `SAT`.

### Use the finite-model finder in CVC4 as an ADT Horn-solver on a TIP benchmark
`~/RInGen$ dotnet bin/Release/net5.0/RInGen.dll solve --tip --quiet cvc4f ~/RInGen/samples/prop_20.smt2`

The output is `sat`.
