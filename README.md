# Bandwidth-Timeout Mechanization

This directory contains Rocq mechanizations of the original monomorphic
calculus and the explicit effect-polymorphic calculus, including their
bandwidth-safety theorems and size-constraint infrastructure.

## Toolchain

The development is checked locally with Rocq 9.1.0 and in CI with the pinned
Rocq 9.1.1 bug-fix image. It uses only the Rocq standard library. Pinning the CI
release keeps the artifact reproducible; additional packages will be added only
when they remove substantial binding or proof-engineering boilerplate.

Build the current development with:

```sh
make
make check
```

`make check` independently kernel-checks every module listed in
`_RocqProject`, including its dependencies. The development introduces no
axioms or admitted proofs.

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
`Proofs (Rocq 9.1.1)` check to pass. Run `make check` locally for the additional
independent kernel check. The workflow can also be started manually from
GitHub's Actions page.

## Explicit effect polymorphism

The `Polymorphic*.v` modules implement the extension in
`bandwidth-timeout-polymorphic-effects-updated.tex`. The original modules are
retained as a checked monomorphic development and supply the concrete
pair-set algebra, normalization, bandwidth arithmetic, and numeric solver.
The polymorphic safety theorem is proved for its own syntax, typing, and
reduction rules.

Finite effect literals include the empty effect. The core syntax represents
it as `EffLit []`, and the symbolic syntax as `PSELiteral []`; `ps_empty` is an
abbreviation for the latter. Neither grammar needs a separate empty
constructor or production.

Normalization collects numerical literal factors from each parallel tree,
combines them with concrete parallel composition, and puts the resulting
literal before the remaining factors. For example,
`({(4,3)} parallel A) parallel {(2,1)}` becomes
`{(4,4)} parallel A`. Remaining factors keep their order and multiplicity;
unknown-size singletons also remain factors. Collection stops at joins, so
`{(4,3)} parallel ({(2,1)} join A)` is not distributed. Join normalization
continues to fold only adjacent numerical children and eliminate empty
operands. The implementation preserves semantic equivalence under every
closing effect and size assignment; it does not claim a canonical form for
all equivalent symbolic expressions.

- `PolymorphicEffects.v` adds whole-effect variables, composition trees,
  scope, capture-avoiding substitution, normalization with parallel regrouping,
  and entailment quantified over every well-formed closing effect assignment.
- `PolymorphicSyntax.v` uses separate de Bruijn namespaces for term and effect
  variables. `PTForall T E` binds an effect variable in both the result type
  and suspended effect. Substituting a term beneath an effect abstraction
  also shifts its free effect variables.
- `PolymorphicTypeSubstitution.v` proves well-formedness, structural
  subtyping, transitivity, and substitution through polymorphic binders.
- `PolymorphicTyping.v` defines declarative typing and proves term and effect
  substitution. An effect abstraction has an empty immediate effect;
  application charges its substituted suspended effect.
- `PolymorphicSemantics.v`, `PolymorphicActiveWF.v`, and
  `PolymorphicCounter.v` define reduction and prove preservation of active
  runtime well-formedness, counter agreement, and error exposure. Effect
  beta reduction neither starts a suspended download nor changes the counter.
- `PolymorphicPreservation.v` proves typing preservation and coverage of
  evaluation-active downloads. Declarative subsumption permits retaining
  the original effect upper bound, which also establishes preservation with
  decreasing effects.
- `PolymorphicSafety.v` proves `poly_bandwidth_safety` for closed source
  programs, plus `poly_bandwidth_safety_open` for a specified closing effect
  assignment.
- `PolymorphicSymbolic.v` adds size singletons to open effect trees and proves
  that closing expansion, size assignment, normalization, and root bandwidth
  checking agree.
- `PolymorphicNormalizationSize.v` proves `eff_norm_size_le` and
  `ps_norm_size_le`: normalization never increases the number of syntax nodes
  plus literal pair entries. Numeric payloads are counted as atomic values;
  this is not a bound on runtime or numeric bit size.
- `PolymorphicConstraints.v` retains each local comparison's generating
  effect scope. Its finite proof search and numeric fallback are proved exact
  when compilation succeeds. The fallback handles a source effect with no
  effect variables and a size-free target, even when the target contains
  effect variables. The solver distinguishes `Solved`, `Unsatisfiable`, and
  `Unresolved`, with soundness, conditional completeness, and maximality proofs.
- `PolymorphicInferenceTypes.v` supplies inferred polymorphic types, exact
  structural compatibility constraints, normalization, and conservative
  joins and meets.
- `PolymorphicInference.v` uses size-free core types for written annotations
  and size-free core effects for explicit arguments. Download sites introduce
  inferred sizes; effect binders never bind size variables. It proves
  constraint-generation soundness, generated well-formedness, and retention
  of caps for every source download variable, including suspended bodies.
- `PolymorphicInferenceSafety.v` connects inferred constraints to the runtime
  safety theorem. Successful solving produces a safe program and a pointwise
  greatest assignment on all source size variables. Its completeness theorem
  explicitly requires successful constraint compilation.
- `PolymorphicInputFree.v` proves the manuscript's proposed size-free
  expected-contract invariant: inference preserves size-free arrow domains,
  and every generated comparison has a size-free expected effect, including
  comparisons beneath binders and contravariant compatibility subderivations.
- `PolymorphicExamples.v` checks the paper's polymorphic `invoke`, forwarding
  across nested binders, suspended nonvalue bodies, and reuse of one bound
  polymorphic value at different effects. It applies the full safety theorem
  to callback programs and parallel reuse, and includes negative checks.
  Inference examples derive and solve the paper's callback bound of 10,
  exercise a tighter cap of 8, reject an insufficient root budget, and retain
  universally quantified local guards beneath effect abstractions. Open
  expected-effect examples check numeric bounds, impossible bare-parameter
  contracts, and comparisons that remain unresolved.

The principal entry points are:

| Result | Theorem |
| --- | --- |
| Core runtime bandwidth safety | `poly_bandwidth_safety` |
| Size-inference typing soundness | `pi_inference_sound` |
| Successful solver implies runtime safety and source caps | `pi_solved_program_safe` |
| Solver assignment is greatest on every source size variable | `pi_solved_program_maximal` |
| Solver completeness after successful compilation | `pi_compiled_inference_complete` |
| Scoped local-constraint compilation exactness | `ps_compile_exact` |
| Compiler coverage for effect-closed sources and size-free targets | `ps_compile_guard_closed_sizefree` |
| Size-free expected contracts for closed programs | `pi_closed_expected_contracts_sizefree` |

### Compiling open expected effects

An expected effect containing a universal effect parameter need not be
rejected. For example, the scoped guard
`{(a/2, 1)} <= epsilon join {(3, 2)}` is equivalent to `a <= 6`:
the concrete pair provides coverage for every value of `epsilon`, and
choosing the empty effect for `epsilon` establishes the necessary bound.

More generally, if the source effect has no effect variables and the target
has no size variables, the compiler replaces every effect variable in the
target by the empty effect and compiles the resulting numeric comparison.
This is exact because join and parallel composition are monotone and the
empty effect is least. The source may still contain inferred sizes.
This also recognizes a nonempty download effect below a bare universal
parameter as unsatisfiable.

The argument does not permit replacing effect variables on both sides by
empty effects. Comparisons with effect variables in the source that are not
discharged by the finite proof search still return `Unresolved`. Local
guards retain their universal scope after an effect application; a supplied
effect argument cannot repair an invalid polymorphic body.

Parallel comparison tries both direct and commuted binary pairings.
The finite search is still sensitive to grouping: regrouping can make a
previously recognized open-source guard return `Unresolved`. Regression
proofs exhibit a guard that remains universally valid but is missed after
regrouping. Successful compilation remains exact, and the complete fragment
with no source effect variables and a size-free target is unaffected.

### Scope of the results

As in the original artifact, quantities are exact rationals, with
nonnegative sizes/rates and positive timeouts. This is not a formalization of
arbitrary real-valued endpoints.

The updated manuscript marks **size-free expected contracts** and
**separable final size constraints** as proposed results. The former is proved
here for the mechanized grammar by `pi_size_free_expected_contracts`. The
latter, a semantic representation theorem over arbitrary real sizes, remains
unproved and is not assumed. Solver completeness retains the successful
constraint-compilation premise; `Unresolved` does not imply unsatisfiability.
Structural polymorphic meets are conservative common lower bounds, not
greatest lower bounds, and no size-substitution commutation or declarative
checker completeness claim is inherited from the monomorphic modules.

## Representation choices

- Download sizes and inferred size bounds inhabit a refined nonnegative-rational
  type; download timeouts inhabit a refined positive-rational type. The original
  annotation grammar also refines rates. Polymorphic effect literals reuse the
  concrete list carrier, with their nonnegative rates checked by `eff_scoped`
  and `ps_scoped` and preserved by typing.
- Effects initially use lists. Their meaning is given entirely by `covers`, so
  order and duplicates are semantically irrelevant.
- Pareto normalization is an executable optimization proved equivalent with
  respect to coverage.
- Source predicates exclude running downloads at every depth, including
  suspended function and effect-abstraction bodies. Empty-context typing
  implies closedness in both variable namespaces.

## File guide

The files in `_RocqProject` are ordered by dependency. Each file has one main
responsibility:

- `theories/Quantities.v` defines the shared nonnegative- and positive-rational
  domains used by concrete syntax and size inference.
- `theories/Effects.v` defines bandwidth obligations, effect coverage, the
  effect preorder, and raw sequential and parallel composition.
- `theories/Normalization.v` implements Pareto normalization and proves that
  it preserves effect coverage, maximum concurrency, and the Pareto-frontier
  invariants.
- `theories/Bandwidth.v` connects effects to numeric bandwidth requirements
  and proves that normalization preserves the computed requirement.
- `theories/Syntax.v` defines types, the unified source/runtime expression
  syntax, values, source expressions, scoping, and runtime grammar
  well-formedness. Concrete and running downloads contain only checked sizes
  and timeouts by construction.
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
- `theories/SizeInference.v` uses the shared nonnegative domain for size
  assignments, defines the separable size-constraint language and executable
  minimum-upper-bound solver, and proves solver soundness, completeness for
  satisfiable constraints, and pointwise maximality.
- `theories/Symbolic.v` defines symbolic rates, effects, types, and source
  expressions. Symbolic downloads contain positive timeouts by construction.
  Lambda syntax uses a separate annotation-type grammar whose effect
  obligations contain concrete nonnegative rates, making symbolic or
  negative-rate programmer contracts unrepresentable. The file also
  instantiates symbolic syntax with a size assignment and proves that
  instantiation commutes with sequential and parallel effect composition.
- `theories/Compatibility.v` implements symbolic-rate, symbolic-effect, and
  structural symbolic-type compatibility against concrete latent-effect
  contracts and proves exactness and separability of the generated constraints.
- `theories/Merging.v` defines the concrete effect meet and mutually recursive
  symbolic branch-type joins and meets, then proves their correctness,
  separability, forward and reverse instantiation commutation, and concrete
  optimality. Its polarity-aware readiness judgments state exactly when a
  symbolic join or meet can reconstruct a concrete merge.
- `theories/Subtyping.v` proves structural transitivity of concrete subtyping
  in a dependency-neutral module shared by checker comparison and inference
  completeness.
- `theories/AlgorithmicTyping.v` defines the paper's syntax-directed concrete
  checker and proves that every accepted term is a well-scoped source term
  accepted by the declarative type-and-effect system.
- `theories/CheckerComparison.v` proves completeness of syntax-directed
  concrete checking relative to declarative typing with subsumption. Every
  declaratively typed source expression has an algorithmic type and effect at
  least as precise, and therefore the two systems accept exactly the same
  source expressions.
- `theories/RootConstraints.v` generates the whole-program bandwidth
  constraints and proves their exactness and separability.
- `theories/Inference.v` defines expression- and list-level size-constraint
  generation and proves source-grammar preservation, separability, and
  constraint-generation soundness. It also proves once that the checked
  annotation grammar satisfies both symbolic-merge readiness judgments; the
  inference rules need no separate annotation-validity premise.
- `theories/Completeness.v` lifts semantic effect equality through types and
  contexts, reconstructs subtype and branch-merge constraints, and proves
  expression-level and end-to-end size-inference completeness. Its public
  closed-program results cover both the syntax-directed checker and the
  paper's declarative checker; the latter also proves that the generated local
  and root constraints are accepted by the executable solver.
- `theories/InferenceSafety.v` combines local and root soundness and applies
  the runtime bandwidth theorem to inferred closed programs.
- `theories/PaperExamples.v` encodes the two motivating programs from the
  paper directly with `EDownload`, `ELet`, and `EParallel`. Its compile-time
  checks establish that both are closed source programs, derive their stated
  types and normalized effects, and reproduce the required-bandwidth results
  10 and 9. Additional cases exercise deeper nested parallelism and the latent
  effect of an applied higher-order function. A negative application case
  proves that applying a [Nat]-identity function to [Unit] has no algorithmic
  typing derivation, exercising [AlgTyApp]'s local subtype rejection. The file
  also checks the paper's standalone parallel-effect calculation.
