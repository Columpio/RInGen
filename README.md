# `RInGen:` Regular Invariant Generator
RInGen is a [SMTLIB2](http://smtlib.cs.uiowa.edu/language.shtml) converter.
It takes arbitrary SMTLIB2 files as input and
generates [Horn clauses](https://chc-comp.github.io/format.html) over
pure [algebraic datatypes](https://en.wikipedia.org/wiki/Algebraic_data_type) again in SMTLIB2.
It can optionally run a number of CHC and other solvers over output clauses, currently:
[z3](https://github.com/Z3Prover/z3),
[Eldarica](https://github.com/uuverifiers/eldarica),
[cvc4 in finite model find mode](https://cvc4.github.io/papers/cav2013-fmf),
[cvc4 in inductive mode](http://lara.epfl.ch/~reynolds/VMCAI2015-ind/).

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
- (optionally, to run solvers) `z3`, `eldarica`, `cvc4` executables accessible
in the environment

## Build
`~/RInGen$ dotnet build -c Release RInGen.sln`
### Build standalone version (for specific platform from the [list](https://raw.githubusercontent.com/dotnet/runtime/main/src/libraries/Microsoft.NETCore.Platforms/pkg/runtime.json))
`dotnet publish -c Release -r <RID> -p:PublishReadyToRun=true RInGen.sln`

Executable then can be found in the `~/RInGen/bin/Release/netcoreapp3.1/<RID>/publish` folder.

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
~/RInGen$ dotnet bin/Release/netcoreapp3.1/RInGen.dll ..arguments..
```

## Options
### `-f`, `--file` `/FULL/PATH.smt2`
Specifies **full** path `/FULL/PATH.smt2` to a single SMTLIB2 file. If `--output-directory` flag is not specified,
the tool will generate Horn clauses in SMTLIB2 format and save them at `/FULL/PATH.*.0.smt2`.
### `-d`, `--directory`
Run on a directory. The tool will recursively traverse the directory and process all
`.smt2` files.
> Either `--file` or `--directory` should be specified to run the tool.
### `-o`, `--output-directory`
Output directory where to put a transformed file (default: same as `--file`)

### `--tipToHorn` `/FULL/PATH`
Convert [TIP-like](https://tip-org.github.io/) systems to Horn clauses.
This flag enables translation of functions defined with `define-*` SMTLIB2 command
into Horn clauses. Each function is transformed into a predicate with one supplementary
argument (for return). All `assert`ions are then **treated as queries**, meaning that
they are transformed to the following form:
```(assert (forall ... (=> .. false)))```

### `--sorts`
After all other translation the following will be performed:
all algebraic datatypes are transformed into sorts.
Specifically, each ADT sort declaration with `declare-datatypes` is substituted with
`declare-sort` for ADT sort and a number of `declare-fun` declarations for constructors.
This preprocessing step is required to run the finite-model finder.

### `-s`, `--solver`
Run a specific solver (one of: z3 | eldarica | cvc4f | cvc4ind | all) after processing.
- [z3](https://github.com/Z3Prover/z3) (`--solver z3`)
- [Eldarica](https://github.com/uuverifiers/eldarica) (`--solver eldarica`)
- [cvc4 in finite model find mode](https://cvc4.github.io/papers/cav2013-fmf) (`--solver cvc4f`)
- [cvc4 in inductive mode](http://lara.epfl.ch/~reynolds/VMCAI2015-ind/) (`--solver cvc4ind`)
- all the above solvers (`--solver all`)
> Note that in order to run `Z3`, `Eldarica` and `CVC4` one should have
> `z3`, `eld` and `cvc4` executables accessible in the environment.

### `-t`, `--timelimit`
Time limit for the specified `--solver`, in seconds (default `300`).

### `-q`, `--quiet`
Quiet mode, to be run as solver. Only outputs are `sat`, `unsat` and `unknown` -
satisfiability result for translated Horn clauses, obtained from `--solver`.

### `--help`, `--version`
   
## Examples
### Convert benchmarks without `define`s from `DIRECTORY` into Horn clauses
`~/RInGen$ dotnet bin/Release/netcoreapp3.1/RInGen.dll --directory /FULL/PATH/TO/DIRECTORY`

Obtained clauses are in the `/FULL/PATH/TO/DIRECTORY.Z3` folder.
### Convert benchmarks with `define`s from `DIRECTORY` into Horn clauses
`~/RInGen$ dotnet bin/Release/netcoreapp3.1/RInGen.dll --tipToHorn --directory /FULL/PATH/TO/DIRECTORY`

Obtained clauses are in the `/FULL/PATH/TO/DIRECTORY.Z3` folder.

### Convert benchmark into Horn clauses and run z3 over the result with timelimit 5 sec
`~/RInGen$ dotnet bin/Release/netcoreapp3.1/RInGen.dll --solver z3 --timelimit 5 --file ~/RInGen/samples/one-zeroary-constr.smt2`

Obtained clauses are in the `~/RInGen/samples/one-zeroary-constr.Z3.0.smt2` file.

Result of the `z3` run will be output to `stdout`. For `one-zeroary-constr.Z3.0.smt2` example it is `SAT`.

### Use the finite-model finder in cvc4 as an ADT Horn-solver
`~/RInGen$ dotnet bin/Release/netcoreapp3.1/RInGen.dll --sorts --solver cvc4f --tipToHorn --quiet  --file ~/RInGen/samples/prop_20.smt2`

The output is `sat`.
