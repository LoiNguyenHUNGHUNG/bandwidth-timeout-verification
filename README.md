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

- Download sizes, inferred size bounds, and programmer-written annotation
  rates inhabit a refined nonnegative-rational type. Download timeouts inhabit
  a refined positive-rational type in both concrete/runtime and symbolic
  syntax. These invariants are grammatical rather than later typing or
  theorem hypotheses.
- Effects initially use lists. Their meaning is given entirely by `covers`, so
  order and duplicates are semantically irrelevant.
- Pareto normalization is an executable optimization proved equivalent with
  respect to coverage.
- Source and runtime syntax will be distinguished explicitly so the main
  safety theorem can require a closed source program.

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
  effect of an applied higher-order function. The file also checks the paper's
  standalone parallel-effect calculation.
