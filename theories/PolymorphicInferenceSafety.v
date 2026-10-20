(** The complete checked path from successful polymorphic size inference to
    runtime bandwidth safety, and greatest bounds for every source download.
    Completeness concerns successfully compiled constraints only. *)
From Stdlib Require Import Arith List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Bandwidth
  SizeInference Symbolic Compatibility RootConstraints PolymorphicEffects
  PolymorphicSyntax PolymorphicTypeSubstitution PolymorphicTyping
  PolymorphicSemantics PolymorphicSafety PolymorphicSymbolic
  PolymorphicConstraints PolymorphicInferenceTypes PolymorphicInference.
Import ListNotations.
Open Scope Q_scope.

Lemma pi_effect_equiv_budget : forall Phi Psi B,
  Phi ≈ Psi -> 0 <= B ->
  (required_bandwidth Phi <= B <-> required_bandwidth Psi <= B).
Proof.
  intros Phi Psi B [H1 H2] HB. split; intro H;
    apply (proj1 (required_bandwidth_spec _ B HB));
    eapply bandwidth_safe_antitone_nonnegative_budget; eauto;
    apply (proj2 (required_bandwidth_spec _ B HB)); exact H.
Qed.

Theorem pi_root_core_exact : forall d E eta sigma B,
  ps_scoped d E -> ps_environment d eta -> 0 <= B ->
  (models sigma (ps_root eta E B) <->
   required_bandwidth (eff_eval eta (ps_instantiate sigma E)) <= B).
Proof.
  intros d E eta sigma B HE Heta HB.
  rewrite (ps_root_exact d E eta sigma B HE Heta HB).
  apply pi_effect_equiv_budget; [apply ps_eval_instantiate|exact HB].
Qed.

Theorem pi_size_inference_safety_open : forall M d Gamma e T E C eta sigma B,
  pi_context_wf d Gamma -> ps_environment d eta -> 0 <= B ->
  pi_infers M d Gamma e T E C -> ps_models sigma C ->
  models sigma (ps_root eta E B) ->
  ~ exists target active,
      poly_successful_steps B (pi_instantiate sigma e) 0 target active /\
      poly_step B (PolyConfig target active) PolyError.
Proof.
  intros M d Gamma e T E C eta sigma B HG Heta HB Hinfer HC Hroot.
  destruct (pi_inference_sound _ _ _ _ _ _ _ _ Hinfer HC) as [Hsource Htyping].
  destruct (pi_generated_wf _ _ _ _ _ _ _ Hinfer) as [HT [HE Hwf]].
  eapply poly_bandwidth_safety_open.
  - apply pi_instantiate_context_wf. exact HG.
  - exact Heta.
  - exact Hsource.
  - exact Htyping.
  - apply (proj1 (pi_root_core_exact d E eta sigma B HE Heta HB)). exact Hroot.
Qed.

Corollary pi_size_inference_safety : forall M e T E C sigma B,
  0 <= B -> pi_infers M 0 [] e T E C -> ps_models sigma C ->
  models sigma (ps_root ps_empty_environment E B) ->
  ~ exists target active,
      poly_successful_steps B (pi_instantiate sigma e) 0 target active /\
      poly_step B (PolyConfig target active) PolyError.
Proof.
  intros. eapply pi_size_inference_safety_open; eauto using ps_empty_environment_wf.
  constructor.
Qed.

Theorem pi_solved_program_safe : forall M e T E C B sigma,
  0 <= B -> pi_infers M 0 [] e T E C ->
  ps_solve ps_empty_environment E B C = Solved sigma ->
  poly_source (pi_instantiate sigma e) /\
  poly_has_type 0 [] (pi_instantiate sigma e)
    (pst_instantiate sigma T) (ps_instantiate sigma E) /\
  (forall a, In a (pi_size_variables e) -> sigma a <= M) /\
  ~ exists target active,
      poly_successful_steps B (pi_instantiate sigma e) 0 target active /\
      poly_step B (PolyConfig target active) PolyError.
Proof.
  intros M e T E C B sigma HB Hinfer Hsolve.
  destruct (pi_generated_wf _ _ _ _ _ _ _ Hinfer) as [HT [HE HC]].
  destruct (ps_solve_sound 0 E ps_empty_environment B C sigma HE
    (ps_empty_environment_wf 0) HB HC Hsolve) as [Hlocal Hbudget].
  destruct (pi_inference_sound _ _ _ _ _ _ _ _ Hinfer Hlocal) as [Hsource Htyping].
  split; [exact Hsource|]. split; [exact Htyping|]. split.
  - eapply (proj1 (pi_inference_caps_mut M)); eauto.
  - eapply poly_bandwidth_safety; [exact Hsource|exact Htyping|].
    apply (proj1 (pi_effect_equiv_budget _ _ B (ps_eval_instantiate E sigma ps_empty_environment) HB)).
    exact Hbudget.
Qed.

(** This statement covers suspended download sites as well as those currently
    visible in the root effect. The generation theorem locates each source
    variable's cap in the compiled numeric constraint. *)
Theorem pi_solved_program_maximal : forall M e T E C B sigma_star,
  0 <= B -> pi_infers M 0 [] e T E C ->
  ps_solve ps_empty_environment E B C = Solved sigma_star ->
  forall sigma,
    ps_models sigma C ->
    required_bandwidth (eff_eval ps_empty_environment (ps_instantiate sigma E)) <= B ->
    forall a, In a (pi_size_variables e) -> sigma a <= sigma_star a.
Proof.
  intros M e T E C B sigma_star HB Hinfer Hsolve sigma Hlocal Hbudget a Hin.
  destruct (pi_generated_wf _ _ _ _ _ _ _ Hinfer) as [HT [HE HC]].
  destruct (ps_compile C) as [D|] eqn:Hcompile.
  - eapply (ps_solve_maximal 0 E ps_empty_environment B C D sigma_star);
      eauto using ps_empty_environment_wf.
    + apply (proj2 (pi_effect_equiv_budget _ _ B
        (ps_eval_instantiate E sigma ps_empty_environment) HB)). exact Hbudget.
    + unfold ps_final_constraint. simpl. apply in_or_app. left.
      eapply pi_compilation_bounds_every_source_variable; eauto.
  - unfold ps_solve in Hsolve. rewrite Hcompile in Hsolve. discriminate.
Qed.

Theorem pi_compiled_inference_complete : forall M e T E C D B,
  0 <= B -> pi_infers M 0 [] e T E C -> ps_compile C = Some D ->
  ((exists sigma_star, ps_solve ps_empty_environment E B C = Solved sigma_star) <->
   exists sigma, ps_models sigma C /\
     required_bandwidth (eff_eval ps_empty_environment (ps_instantiate sigma E)) <= B).
Proof.
  intros M e T E C D B HB Hinfer Hcompile.
  destruct (pi_generated_wf _ _ _ _ _ _ _ Hinfer) as [HT [HE HC]].
  rewrite (ps_solve_complete 0 E ps_empty_environment B C D HE
    (ps_empty_environment_wf 0) HB HC Hcompile).
  split; intros [sigma [Hlocal Hbudget]]; exists sigma; split; [exact Hlocal| |exact Hlocal|].
  - apply (proj1 (pi_effect_equiv_budget _ _ B
      (ps_eval_instantiate E sigma ps_empty_environment) HB)). exact Hbudget.
  - apply (proj2 (pi_effect_equiv_budget _ _ B
      (ps_eval_instantiate E sigma ps_empty_environment) HB)). exact Hbudget.
Qed.
