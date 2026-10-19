(** End-to-end bandwidth safety for explicit effect polymorphism. *)
From Stdlib Require Import Arith Lia Lra List QArith Qfield ZArith.
From BandwidthTimeout Require Import Effects Normalization Bandwidth Syntax
  Safety PolymorphicEffects PolymorphicSyntax PolymorphicTypeSubstitution
  PolymorphicTyping PolymorphicSemantics PolymorphicActiveWF
  PolymorphicCounter PolymorphicPreservation.
Import ListNotations.
Open Scope Q_scope.

Theorem poly_bandwidth_safety_open : forall d Gamma eta B source T E,
  poly_context_wf d Gamma -> eff_environment d eta ->
  poly_source source -> poly_has_type d Gamma source T E ->
  required_bandwidth (eff_eval eta E) <= B ->
  ~ exists target active,
      poly_successful_steps B source 0 target active /\
      poly_step B (PolyConfig target active) PolyError.
Proof.
  intros d Gamma eta B source T E HG Heta Hsource Htyping Hbudget
    [target [active [Hsteps Herror]]].
  pose proof (poly_preservation_steps _ _ _ _ _ _ _ _ _ Hsteps HG Htyping)
    as Htyping_current.
  pose proof (poly_active_coverage _ _ _ _ _ eta Htyping_current Heta) as Hactive_le.
  pose proof (poly_counter_agreement _ _ _ _ Hsource Hsteps) as Hcounter.
  destruct (poly_error_exposure _ _ _ Herror)
    as [required_rate [Hrate_in [Hpositive Hunder]]].
  assert (Hactive_covers :
    covers (poly_active_effect (poly_running_rates target))
      (Obligation required_rate active)).
  { unfold poly_active_effect.
    apply (le_normalize
      (map (fun current_rate =>
        Obligation current_rate (length (poly_running_rates target)))
        (poly_running_rates target))).
    apply in_map_iff. exists required_rate. split.
    - f_equal. symmetry. exact Hcounter.
    - exact Hrate_in. }
  assert (Htop_covers : covers (eff_eval eta E) (Obligation required_rate active)).
  { eapply covers_effect_le; eauto. }
  destruct Htop_covers as [top_obligation [Htop_in Hcoordinates]].
  assert (Hbandwidth_nonnegative : 0 <= B).
  { eapply Qle_trans.
    - apply required_bandwidth_nonnegative.
    - exact Hbudget. }
  assert (Hactive_positive : 0 < qnat active).
  { apply qnat_positive. exact Hpositive. }
  assert (Hshare_nonnegative : 0 <= B / qnat active).
  { unfold Qdiv. apply Qmult_le_0_compat.
    - exact Hbandwidth_nonnegative.
    - apply Qinv_le_0_compat. apply Qlt_le_weak. exact Hactive_positive. }
  assert (Hrate_nonnegative : 0 <= required_rate).
  { eapply Qle_trans.
    - exact Hshare_nonnegative.
    - apply Qlt_le_weak. exact Hunder. }
  assert (Herror_bandwidth :
    B < obligation_bandwidth (Obligation required_rate active)).
  { unfold obligation_bandwidth. simpl.
    assert (Hmultiplied :
      (B / qnat active) * qnat active <
      required_rate * qnat active).
    { apply (proj2 (Qmult_lt_r
        (B / qnat active) required_rate (qnat active)
        Hactive_positive)).
      exact Hunder. }
    assert (Hcancel :
      B / qnat active * qnat active == B).
    { field. intro Hzero. apply (Qlt_not_eq _ _ Hactive_positive).
      symmetry. exact Hzero. }
    rewrite Hcancel in Hmultiplied. exact Hmultiplied. }
  assert (Hcovered_bandwidth :
    obligation_bandwidth (Obligation required_rate active) <=
    obligation_bandwidth top_obligation).
  { eapply obligation_bandwidth_mono.
    - exact Hrate_nonnegative.
    - exact Hcoordinates. }
  assert (Htop_bandwidth :
    obligation_bandwidth top_obligation <= required_bandwidth (eff_eval eta E)).
  { apply obligation_bandwidth_le_required. exact Htop_in. }
  assert (Htoo_much : B < required_bandwidth (eff_eval eta E)).
  { eapply Qlt_le_trans.
    - exact Herror_bandwidth.
    - eapply Qle_trans; eauto. }
  exact (Qlt_not_le _ _ Htoo_much Hbudget).
Qed.

(** Closed programs require neither an effect assignment nor a term
    environment from the caller. *)
Corollary poly_bandwidth_safety : forall B source T E,
  poly_source source -> poly_has_type 0 [] source T E ->
  required_bandwidth (eff_eval (fun _ => []) E) <= B ->
  ~ exists target active,
      poly_successful_steps B source 0 target active /\
      poly_step B (PolyConfig target active) PolyError.
Proof.
  intros. eapply poly_bandwidth_safety_open; eauto.
  - constructor.
  - intros i Hi. lia.
Qed.
