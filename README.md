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
- `theories/Symbolic.v` defines symbolic rates, effects, types, and source
  expressions; instantiates them with a size assignment; and proves that
  instantiation commutes with sequential and parallel effect composition.
- `theories/Compatibility.v` implements symbolic-rate, symbolic-effect, and
  structural symbolic-type compatibility against concrete latent-effect
  contracts and proves exactness and separability of the generated constraints.
- `theories/Merging.v` defines the concrete effect meet and mutually recursive
  symbolic branch-type joins and meets, then proves their correctness,
  separability, forward and reverse instantiation commutation, and concrete
  optimality. Its polarity-aware readiness judgments state exactly when a
  symbolic join or meet can reconstruct a concrete merge.
- `theories/AlgorithmicTyping.v` defines the paper's syntax-directed concrete
  checker and proves that every accepted term is a well-scoped source term
  accepted by the declarative type-and-effect system.
- `theories/RootConstraints.v` generates the whole-program bandwidth
  constraints and proves their exactness and separability.
- `theories/Inference.v` defines expression- and list-level size-constraint
  generation and proves source-grammar preservation, separability, and
  constraint-generation soundness. It also proves that programmer-written
  annotation types satisfy both symbolic-merge readiness judgments.
- `theories/Completeness.v` lifts semantic effect equality through types and
  contexts, reconstructs subtype and branch-merge constraints, and proves
  expression-level and end-to-end size-inference completeness relative to the
  syntax-directed concrete checker.
- `theories/InferenceSafety.v` combines local and root soundness and applies
  the runtime bandwidth theorem to inferred closed programs.

## Proof milestones

1. Effect preorder and monotonicity of sequential and parallel composition.
2. Pareto normalization preserves and reflects coverage.
3. Source/runtime syntax, substitution, typing, and reduction.
4. Preservation, active well-formedness, and counter agreement.
5. Bandwidth safety.
6. Separable size-constraint solving and maximal inferred bounds.
7. Symbolic syntax, effects, instantiation, and effect-operation commutation.
8. Symbolic rate/effect and structural type compatibility constraints and
   exactness.
9. Branch joins and meets, including correctness, instantiation commutation,
   and concrete least/greatest-bound optimality.
10. Constraint generation and size-inference soundness and completeness.

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

The symbolic inference layer is now checked as well. It represents inferred
rates as either a concrete rate or a size variable divided by a known timeout,
uses the paper's unnormalized symbolic sequential and parallel operations, and
defines assignment instantiation for symbolic effects, types, and source
expressions. The checked commutation lemmas follow the paper's proof strategy:
instantiation preserves concurrency shifts exactly, while final Pareto
normalization makes the symbolic and concrete operations semantically
equivalent. Instantiation also preserves symbolic values, source grammar, and
effect well-formedness.

The first compatibility layer is now checked. It computes the greatest rate in
a concrete latent-effect contract whose concurrency can cover a symbolic
obligation, proves that this maximum exists exactly when such a covering
obligation exists, and proves that comparison with it is exactly concrete
effect coverage after instantiation. The resulting `RateC` and `EffC`
constraints contain only variable-free comparisons and upper bounds on one
inferred size variable; no compatibility constraint can relate two inferred
variables. This formalizes the key concrete-contract restriction used by the
paper's separability lemma.

Structural symbolic type compatibility is checked as well. A dedicated
relation records when a symbolic latent effect is actually a programmer-written
concrete contract, so the concrete-contract restriction is a formal premise
rather than an English assumption. `SubTyC` follows declarative subtyping:
products are checked pointwise, arrows are contravariant in their domains and
covariant in their latent effects and codomains, and incompatible shapes or
product arities generate failure. Its exactness theorem proves that a
well-formed assignment models the generated constraint exactly when the
instantiated source type is a concrete subtype of the instantiated target.
Every generated `SubTyC` constraint remains in the separable compatibility
fragment.

Symbolic branch joins and meets are checked next. The concrete effect meet is
implemented exactly as the paper's normalized Cartesian product of
coordinatewise minima and is proved to be the greatest lower bound under
effect coverage. Symbolic type joins and meets follow subtyping variance for
products and arrows; function meets formally require both latent effects to be
concrete contracts. Modeled join constraints produce a common supertype, and
modeled meet constraints produce a common subtype. The merge constraints remain
separable. Instantiation also commutes with symbolic merging: the instantiated
result corresponds to the concrete structural join or meet, using structural
type equivalence with semantic effect equivalence because effects are
list-backed in Rocq rather than mathematical sets.

Concrete structural merge optimality is checked as well. Whenever two types
share a common supertype, their concrete join exists and is still below that
supertype; dually, whenever they share a common subtype, their concrete meet
exists and remains above it. The proof follows the paper's mutual argument:
products recurse pointwise, while arrows use meet optimality in contravariant
domains, join optimality in covariant codomains, the sequential-effect least
upper bound, and the concrete-effect-meet greatest lower bound.

Root bandwidth constraints are now checked. Each symbolic root obligation
produces one concrete upper bound on its size variable, while each concrete
obligation produces a variable-free bandwidth comparison. Modeling their
conjunction is proved equivalent to the normalized instantiated effect's
required bandwidth being within the nonnegative budget. The generated root
constraint remains in the separable fragment and never relates two inferred
size variables. The Rocq definition also totalizes the otherwise harmless
zero-concurrency edge case as the exact concrete check `0 <= B`; the paper's
generated obligations use positive concurrency.

Expression-level constraint generation and its soundness lemma are now
checked. The mutually defined judgments cover every symbolic source form and
aligned tuple/parallel lists. `SI-Down` makes the positive-timeout convention
explicit and emits the paper's nonnegativity and global-maximum constraints;
`SI-Abs` enforces concrete programmer-written latent-effect annotations,
application invokes `SubTyC`, and conditionals invoke symbolic type joining.
Every generated constraint remains in the independent single-variable
fragment. If an assignment models an expression's generated constraint, the
instantiated expression has exactly the instantiated inferred type in the
declarative system. Its concrete typing effect is coverage-equivalent to the
normalized instantiated symbolic effect, which is the list-backed Rocq form of
the paper's set equality. Inference also preserves symbolic type/effect
well-formedness from its context; for a closed program, this discharges the
root theorem's well-formedness premise automatically.

End-to-end size-inference soundness is now checked. A model of the conjunction
of local and root constraints yields a declaratively typed concrete source
program whose exact typing effect fits within the requested nonnegative budget.
The final corollary feeds that typing and bound to `bandwidth_safety`, ruling
out every successful execution prefix followed by a bandwidth-error step.

The syntax-directed concrete checker from the completeness section is now
checked. It contains no global subsumption rule: applications perform the
argument subtype check locally, and conditionals compute the concrete
least-common-supertype join of their branch types. Every algorithmically typed
term is proved to be source syntax, well scoped by its context, and accepted
with the same type and effect by the declarative system.

Size-inference completeness is now checked relative to the syntax-directed
concrete checker. Because effects are represented by lists rather than the
paper's sets, the theorem uses mutual-coverage equality for effects, lifts it
structurally through types and pointwise through contexts, and proves that
subtyping and concrete joins respect that equality. Under the paper's global
size bound and concrete-annotation discipline, every accepted instantiated
program reconstructs a symbolic inference derivation whose local constraints
are modeled by the same assignment. If the concrete effect also fits the
bandwidth budget, the generated root constraints are modeled as well.
