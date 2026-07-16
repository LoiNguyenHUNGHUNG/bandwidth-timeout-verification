# Bandwidth-Timeout Mechanization

This directory contains the Rocq mechanization of the core calculus and its
bandwidth-safety theorem.

## Toolchain

The initial development is checked with Rocq 9.1.0 and uses only the Rocq
standard library. Pinning an exact Rocq release keeps the artifact reproducible;
additional packages will be added only when they remove substantial binding or
proof-engineering boilerplate.

Build the current development with:

```sh
make
```

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

The next module will define source/runtime syntax and make source-ness an
explicit premise of the top-level safety theorem.
