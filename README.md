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

## Authorship and proof provenance

All Rocq definitions and mechanized proof scripts in this repository are
written solely by OpenAI Codex. The human collaborator guides selected steps
and design decisions and provides pen-and-paper proofs for the principal
theorems and lemmas; Codex translates those arguments into Rocq, supplies the
supporting proof engineering, and checks the resulting development with the
compiler and CI.

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
- Pareto normalization is an executable optimization proved equivalent with
  respect to coverage.
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
A reflexive-transitive successful-step relation records execution prefixes that
have not entered the terminal error state.

The typing layer now formalizes the paper's declarative type-and-effect system.
It includes normalized sequential and parallel effect composition, structural
subtyping for products and latent-effect arrows, the ordinary source rules, and
the runtime-only rule for an active download. Its checked metatheory establishes
type-preserving de Bruijn renaming, simultaneous substitution, the single-binder
substitution theorem used by beta and let reduction, scoping and runtime-grammar
well-formedness of typed terms, and the fact that values have empty immediate
effect. The parallel-effect algebra additionally proves that binary composition
adds operand maxima, the list fold sums the maximum concurrency of every branch,
and different binary groupings are coverage-equivalent.

The active-runtime layer follows the paper's running-download appendix. It
defines the multiset of evaluation-active running rates, the induced active
effect, the stronger whole-syntax `no_run` predicate, and `active_wf`, which
requires dormant call-by-value positions to contain no hidden running download.
The checked lemmas show that source expressions satisfy `no_run`, substitution
preserves it, `no_run` implies `active_wf`, actively well-formed values satisfy
`no_run`, and every successful state reachable from a source expression remains
actively well formed.

The safety layer completes the main metatheory from the paper. The checked
active-effect algebra proves that the maximum concurrency of an active effect
is exactly the number of running downloads and that active effects of finite
multiset unions are covered by iterated parallel composition. Generation modulo
subsumption is represented by explicit subtype chains, which support a full
proof of preservation with decreasing effects for every successful reduction
rule, including beta reduction and arbitrary parallel-child interleavings.

The remaining checked invariants establish local and reachable active-effect
coverage, one-step counter balance, counter agreement for executions from source
syntax, and error exposure through every evaluation context. The final theorem
`bandwidth_safety` states that if a closed source program has effect `Phi` and
`required_bandwidth Phi <= B`, then no successful execution prefix from counter
zero can be followed by a transition to the bandwidth-error configuration.

The next milestones concern the paper's later scenario-projection exactness and
size-inference metatheory; they are independent of the completed core
bandwidth-safety theorem.
