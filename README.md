# Bandwidth-Timeout Mechanization

This directory contains the Rocq mechanization of the core calculus and its
bandwidth-safety theorem.

## Toolchain

The development is checked locally with Rocq 9.1.0 and in CI with the pinned
Rocq 9.1.1 bug-fix image. It uses only the Rocq standard library. Pinning the CI
release keeps the artifact reproducible; additional packages will be added only
when they remove substantial binding or proof-engineering boilerplate.

Build the current development with:

```sh
make
```

## Continuous integration

GitHub Actions runs a clean build on every push and pull request using the
official `rocq/rocq-prover:9.1.1` image. The job executes `make clean` followed
by `make -j2`, so every listed `.v` file must compile from scratch for the
`Proofs (Rocq 9.1.1)` check to pass. The workflow can also be started manually
from GitHub's Actions page.

## Representation choices

- Rates are rational numbers (`Q`). This keeps comparison, normalization, and
  the eventual checker executable. Well-formed obligations will require rates
  to be nonnegative.
- Effects initially use lists. Their meaning is given entirely by `covers`, so
  order and duplicates are semantically irrelevant.
- Pareto normalization will be introduced as an executable optimization and
  proved equivalent with respect to coverage.
- Source and runtime syntax will be distinguished explicitly so the main
  safety theorem can require a closed source program.

## Proof milestones

1. Effect preorder and monotonicity of sequential and parallel composition.
2. Pareto normalization preserves and reflects coverage.
3. Source/runtime syntax, substitution, typing, and reduction.
4. Preservation, active well-formedness, and counter agreement.
5. Bandwidth safety.
6. Scenario-projection exactness and size-inference metatheory.

## Current checked results

The initial milestone establishes:

- reflexivity and transitivity of obligation and effect coverage;
- monotonicity of sequential and parallel effect composition;
- monotonicity of maximum concurrency under effect coverage;
- executable Pareto normalization;
- exact preservation of coverage by normalization;
- duplicate-freedom and the antichain property of normalized effects;
- monotonicity of per-obligation bandwidth under coverage;
- preservation and reflection of the pointwise bandwidth check by
  normalization; and
- exact preservation of the computed maximum required bandwidth by
  normalization.

The syntax layer uses a unified runtime AST with de Bruijn indices. A runtime
well-formedness predicate enforces that tuple nodes contain values, matching the
paper's grammar. Source expressions are identified by an inductive predicate
that additionally excludes the runtime-only running-download form at every
depth, and a separate scoping predicate identifies closed programs.

The substitution layer now provides binder-aware renaming, shifting, and
simultaneous substitution over the de Bruijn representation. The checked
structural results show that these operations preserve values, source syntax,
runtime well-formedness, and scoping under the corresponding assumptions. In
particular, every binder-aware renaming is exactly the identity on a closed
expression, and single-variable substitution removes one binder without
breaking scope.

The operational-semantics layer defines configurations containing a runtime
expression and the global active-download counter, together with the terminal
bandwidth-error configuration. Its small-step relation covers call-by-value
computation, arbitrary interleavings of parallel children, download start and
finish, the fair-share bandwidth error, and error propagation. Successful
steps are proved to preserve runtime well-formedness and scoping; in
particular, evaluation cannot introduce a free variable into a closed program.

The next module will define the source and runtime typing judgments. It will
then use the substitution and operational-semantics results to prove the
typing substitution lemma and preservation with decreasing effects.
