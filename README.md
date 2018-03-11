
# Mutation plugin for Frama-C

Generation of *mutant* programs.

Mutant programs (*mutants* for short) are the result of a *mutation* : a
syntactically modification on the source program (on its instructions or its
specification). A given mutant may or may not be semantically equivalent to the
source program.

Here are the corresponding versions of Frama-C for each version of Mutation:

| Frama-C        |  Mutation  |
| -------------- | ---------- |
| v16 Sulfur     |  v0.2.x    |


## Building

    autoconf
    ./configure
    make
    make install


# Using Mutation

    frama-c FILE -mut [-mut-code] [-mut-spec] [-mut-summary-file SUMMARY]

where 'FILE' is the file the plugin is applied to, 'SUMMARY' is the file where
the list of the produced mutants will be written. Use the options '-mut-code'
and '-mut-spec' to apply code-only mutations or spec-only mutations.

Here are some of the mutations applied by the Mutation plugin:
* Replacement of a binary operator
* Condition reversal
* Loop invariant deletion
* Postcondition deletion
* Conjunction pruning
* Replacement of numerical values
