(** End-to-end soundness of size inference.

    Constraint-generation soundness supplies a declarative typing derivation,
    while root-constraint exactness supplies the bandwidth bound for the
    normalized instantiated symbolic effect.  Because effects are list-backed,
    the concrete typing derivation may use an effect that is semantically
    equivalent rather than literally equal.  The bandwidth-transfer lemma in
    [Bandwidth] connects that representation-level gap before the existing
    runtime bandwidth-safety theorem is applied. *)

From Stdlib Require Import List QArith.

From BandwidthTimeout Require Import Normalization Bandwidth Typing Semantics
  SizeInference Symbolic RootConstraints Inference Safety.

Import ListNotations.
Open Scope Q_scope.

(** The paper's size-inference soundness theorem, with list-backed effect
    equality represented by [effect_equiv].  A model of the local and root
    constraints yields a concrete source typing whose exact typing effect fits
    within the requested bandwidth budget. *)
Theorem size_inference_sound :
  forall M e T Phi C sigma B,
    size_infers M [] e T Phi C ->
    0 <= B ->
    models sigma (CAnd C (root_constraint Phi B)) ->
    exists concrete_effect,
      source_has_type []
        (instantiate_expr sigma e)
        (instantiate_ty sigma T)
        concrete_effect /\
      required_bandwidth concrete_effect <= B /\
      instantiate_effect sigma Phi ≈ concrete_effect.
Proof.
  intros M e T Phi C sigma B Hinfer HB Hmodels.
  assert (Hempty_context : symbolic_context_wf []) by constructor.
  pose proof (size_infers_effect_wf
    M [] e T Phi C Hinfer Hempty_context) as Hphi_wf.
  destruct Hmodels as [Hlocal Hroot].
  destruct (constraint_generation_sound
    M [] e T Phi C sigma Hinfer Hlocal)
    as [concrete_effect [Htyping Hequiv]].
  simpl in Htyping.
  pose proof (proj1 (root_constraint_exact sigma Phi B
    Hphi_wf HB) Hroot) as Hsymbolic_budget.
  pose proof (proj2 (required_bandwidth_spec
    (instantiate_effect sigma Phi) B HB) Hsymbolic_budget)
    as Hsymbolic_safe.
  assert (Hconcrete_safe : bandwidth_safe B concrete_effect).
  { eapply bandwidth_safe_antitone_nonnegative_budget.
    - exact HB.
    - exact (proj2 Hequiv).
    - exact Hsymbolic_safe. }
  exists concrete_effect. split.
  - exact Htyping.
  - split.
    + apply required_bandwidth_least; assumption.
    + exact Hequiv.
Qed.

(** Successful size inference for a closed symbolic program rules out every
    execution prefix followed by a bandwidth-error transition. *)
Theorem inferred_program_bandwidth_safe :
  forall M e T Phi C sigma B,
    size_infers M [] e T Phi C ->
    0 <= B ->
    models sigma (CAnd C (root_constraint Phi B)) ->
    ~ exists target active,
        successful_steps B (instantiate_expr sigma e) 0 target active /\
        step B (Config target active) Error.
Proof.
  intros M e T Phi C sigma B Hinfer HB Hmodels.
  destruct (size_inference_sound
    M e T Phi C sigma B Hinfer HB Hmodels)
    as [concrete_effect [Htyping [Hbudget Hequiv]]].
  eapply bandwidth_safety; eauto.
Qed.
