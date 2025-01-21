# How to build the project

## Mata lib

- Clone the main repository: `git clone https://github.com/VeriFIT/mata`
- Follow the instructions in their README on how to build it

## cvc5 fork

- Clone the main git repository: `git clone https://github.com/lframosferreira/cvc5`
- Change to the correct branch: `git checkout automata_based_lia_solver`
- Run the configure script with the following flags: `./configure.sh --mata --auto-download`
- Change to the build directory and run: `make && sudo make install`
- The binary `cvc5` is installed in the directory `cvc5/build/bin/`

# How to use

- Run `./cvc5/build/bin/cvc5 [inputfile] --automata`. The `--automata` flag applies the automata preprocessing.

# IMPORTANT

This implementation only works with LIA formulae following the grammar presented in the report. It will crash if anything else is passed as an input.
Inside the `cvc5` folder there are two other folders, called `lia_tests` and `qflia_tests`, each of which contains benchmarks for testing the implementation that are already following
the specified format. If you want to use another set of tests but don't want the trouble of rewriting it to respect the accepted grammar yourself, you can use the Amaya tool `convert` step
to do it for you. Instructions on how to build and use Amaya are described below:

## How to build and use Amaya

- Clone the repository `https://github.com/MichalHe/amaya` and follow the build instructions described in the README file
- Run `python3 run-amaya.py convert [inputfile]`. This will print to *stdout* the converted formula
