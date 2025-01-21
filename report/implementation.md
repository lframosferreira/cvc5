# Implementation details, such as data structures and functions created

As described in the main report, the implementation works as a preprocessing step in the cvc5 environment.  All the code
can be found at the files `cvc5/src/preprocessing/passes/automata.{h or cpp}`.
From now on, I will describe the main data structures created as well as the functions implemented.

## AtomicFormulaStructure

This data structure contains information about a atomic formula, such as:

- Kind (<=, =, mod)
- Vector of coefficients
- Vector of variables
- Variable free contant
- Value of the mod

It helps a lot when solving the problems, because it allowd to store the relevant information from the formula in a simple manner.

## get_atomic_formula_structure()

This functions is repsonsible for iterating through a node of an atomic formula and filling a structure of type AtomicFormulaStructure
with it's information. This was actually a really confusing part of the implementation, since I didn't fully comprehend yet the SMT-LIB AST inside
the cvc5 environment. The implementation is quite messy but it works, if and only if the input formula is in the format of the grammar
described in the main report.

## project_variable()

This function performs projection of a variable, needed to apply the exitential quantifier operation over the automaton.

## perform_pad_closure()

This function is responsible for applying the pad closure algorithm responsible for augmenting the automaton after we project a variable tape out of it.

## build_nfa_for_formula()

This function receives a node and recursively constructs the automaton for the input node. If the kind of the input node is AND, for example, it calls itself
recursively for each of it's children and then merges them with automaton itersection. If the formula is atomic, instead of a recursive call, the function calls
`build_nfa_for_atomic_formula()`;

## build_nfa_for_atomic_formula()

Function that created an NFA for an atomic formulae, acording to the algorithm described in the main report.
