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

## File guide

The files in `_RocqProject` are ordered by dependency. Each file has one main
responsibility:

- `theories/Effects.v` defines bandwidth obligations, effect coverage, the
  effect preorder, and raw sequential and parallel composition.
- `theories/Normalization.v` implements Pareto normalization and proves that
  it preserves effect coverage, maximum concurrency, and the Pareto-frontier
  invariants.
- `theories/Bandwidth.v` connects effects to numeric bandwidth requirements
  and proves that normalization preserves the computed requirement.
- `theories/Syntax.v` defines types, the unified source/runtime expression
  syntax, values, source expressions, scoping, and runtime grammar
  well-formedness.
- `theories/Substitution.v` implements binder-aware de Bruijn renaming,
  shifting, and substitution and proves their structural preservation lemmas.
- `theories/Typing.v` defines subtyping and declarative type-and-effect typing,
  together with renaming, substitution, scoping, and value-effect results.
- `theories/Semantics.v` defines runtime configurations, successful and error
  reduction rules, multi-step execution, and preservation of syntax-level
  well-formedness and scope.
- `theories/ActiveWF.v` defines the focused running-rate collector, whole-term
  `no_run`, the `active_wf` invariant, and preservation of that invariant from
  source programs.
- `theories/ActiveEffects.v` proves the algebraic facts connecting focused
  running-rate multisets to pair-set effects.
- `theories/Preservation.v` proves generation modulo subtyping, preservation
  with decreasing effects, and active-effect coverage.
- `theories/Safety.v` proves counter balance, counter agreement, error
  exposure, and the final bandwidth-safety theorem.
- `theories/SizeInference.v` defines the separable size-constraint language
  and executable minimum-upper-bound solver and proves solver soundness and
  pointwise maximality.

## Proof milestones

1. Effect preorder and monotonicity of sequential and parallel composition.
2. Pareto normalization preserves and reflects coverage.
3. Source/runtime syntax, substitution, typing, and reduction.
4. Preservation, active well-formedness, and counter agreement.
5. Bandwidth safety.
6. Separable size-constraint solving and maximal inferred bounds.
7. Symbolic constraint generation and size-inference soundness and
   completeness.

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
defines a focused multiset of running rates that follows the current
call-by-value evaluation positions directly: let and conditional bodies are
dormant, applications switch from the function to the argument when the
function becomes a value, and all parallel branches remain active. The layer
also defines the induced active effect, the stronger whole-syntax `no_run`
predicate, and `active_wf`, which ensures that dormant positions contain no
hidden running download that could later be exposed without a counter update.
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

Because the running-rate multiset is focused, local active-effect coverage now
holds for every typed runtime expression without an `active_wf` or reachability
premise. The remaining checked invariants establish one-step counter balance
under `active_wf`, counter agreement for executions from source syntax, and
error exposure through every evaluation context. The final theorem
`bandwidth_safety` states that if a closed source program has effect `Phi` and
`required_bandwidth Phi <= B`, then no successful execution prefix from counter
zero can be followed by a transition to the bandwidth-error configuration.

The first size-inference layer is also checked. It represents the paper's
solver-facing constraints as finite conjunction trees containing failure,
concrete comparisons, nonnegativity requirements, and single-variable upper
bounds. The executable solver rejects failed concrete checks and unbounded
variables, assigns each remaining variable the minimum of its upper bounds,
and is proved both sound and pointwise greatest among satisfying assignments.

The next milestones concern symbolic rates and effects, instantiation, root
bandwidth constraints, and the soundness and completeness of constraint
generation. They build on the completed core bandwidth-safety theorem and the
checked separable solver.
