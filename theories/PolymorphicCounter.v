(** Counter agreement, error exposure, and the final bandwidth-safety theorem.

    This file assembles the static and dynamic invariants proved earlier. The
    key operational balance lemma states that one successful step changes the
    number of exposed running forms by exactly the same amount as it changes
    the global counter. *)

From Stdlib Require Import Arith Lia Lra List QArith Qfield ZArith.
From BandwidthTimeout Require Import
  Effects Normalization Bandwidth Syntax Semantics ActiveWF ActiveEffects
  PolymorphicEffects PolymorphicSyntax PolymorphicSemantics PolymorphicActiveWF.

Import ListNotations.
Open Scope Q_scope.

(** If every expression in a list contains no running form, concatenating all
    of their active rate multisets gives the empty multiset. *)
Lemma poly_Forall_no_run_running_rates_empty :
  forall expressions,
    Forall poly_no_run expressions ->
    concat (map poly_running_rates expressions) = [].
Proof.
  intros expressions Hno. induction Hno; simpl.
  - reflexivity.
  - rewrite (poly_no_run_running_rates_empty _ H), IHHno. reflexivity.
Qed.

(** Extend the running-count/counter balance equation to arbitrary transition
    endpoints. PolyError targets do not participate in counter agreement. *)
Definition poly_counter_balance_transition
    (source target : poly_configuration) : Prop :=
  match source, target with
  | PolyConfig e active, PolyConfig e' active' =>
      poly_active_wf e ->
      (length (poly_running_rates e') + active =
       length (poly_running_rates e) + active')%nat
  | _, _ => True
  end.

(** One successful step changes the explicit running-form count and the global
    active-download counter in lockstep. [poly_active_wf] is essential for the pure
    redexes: it rules out hidden running forms in discarded dormant syntax. *)
Lemma poly_step_counter_balance_general :
  forall B source target,
    poly_step B source target ->
    poly_counter_balance_transition source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl in *.
  - intros Hactive. inversion Hactive; subst.
    match goal with
    | Hbound_active : poly_active_wf bound,
      Hbody_no_run : poly_no_run body |- _ =>
        pose proof
          (poly_active_wf_value_no_run _ H Hbound_active) as Hbound_no_run;
        pose proof
          (poly_subst0_preserves_no_run _ _ Hbound_no_run Hbody_no_run)
          as Hresult_no_run;
        rewrite (poly_no_run_running_rates_empty _ Hbound_no_run),
          (poly_no_run_running_rates_empty _ Hresult_no_run)
    end.
    reflexivity.
  - intros Hactive. inversion Hactive; subst.
    + exfalso. match goal with
      | Hnot_value : ~ poly_value (PELambda _ _) |- _ =>
          apply Hnot_value; constructor
      end.
    + match goal with
      | Hlambda_no_run : poly_no_run (PELambda _ _) |- _ =>
          inversion Hlambda_no_run; subst
      end.
      match goal with
      | Hbody_no_run : poly_no_run body,
        Hargument_active : poly_active_wf argument,
        Hargument_value : poly_value argument |- _ =>
          pose proof
            (poly_active_wf_value_no_run _ Hargument_value Hargument_active)
            as Hargument_no_run;
          pose proof
            (poly_subst0_preserves_no_run _ _ Hargument_no_run Hbody_no_run)
            as Hresult_no_run;
          rewrite (poly_no_run_running_rates_empty _ Hargument_no_run),
            (poly_no_run_running_rates_empty _ Hresult_no_run)
      end.
      destruct (poly_value_dec (PELambda parameter_ty body))
        as [Hlambda_value | Hlambda_not_value].
      * reflexivity.
      * exfalso. apply Hlambda_not_value. constructor.
  - intros Hactive. inversion Hactive; subst.
    match goal with Hzero_no_run : poly_no_run zero_branch |- _ =>
      rewrite (poly_no_run_running_rates_empty _ Hzero_no_run)
    end.
    reflexivity.
  - intros Hactive. inversion Hactive; subst.
    match goal with Hnonzero_no_run : poly_no_run nonzero_branch |- _ =>
      rewrite (poly_no_run_running_rates_empty _ Hnonzero_no_run)
    end.
    reflexivity.
  - intros Hactive. inversion Hactive; subst.
    match goal with Hbranches_active : Forall poly_active_wf branches |- _ =>
      pose proof
        (poly_Forall_values_active_wf_no_run _ H Hbranches_active)
        as Hbranches_no_run;
      rewrite (poly_Forall_no_run_running_rates_empty _ Hbranches_no_run)
    end.
    reflexivity.
  - intros Hactive. simpl. lia.
  - intros Hactive. simpl. lia.
  - exact I.
  - intros Hactive. inversion Hactive; subst.
    match goal with
    | Hbound_active : poly_active_wf bound |- _ =>
        exact (IHHstep Hbound_active)
    end.
  - intros Hactive.
    assert (~ poly_value function) as Hfunction_not_value.
    { intro Hvalue. eapply poly_value_no_successful_step; eauto. }
    inversion Hactive; subst.
    + match goal with
      | Hfunction_active : poly_active_wf function,
        Hargument_no_run : poly_no_run argument |- _ =>
          pose proof (IHHstep Hfunction_active) as Hbalance;
          pose proof
            (poly_no_run_running_rates_empty _ Hargument_no_run)
            as Hargument_rates;
          destruct (poly_value_dec function) as [Hvalue | Hnot_value]
      end.
      * contradiction.
      * destruct (poly_value_dec function') as [Hvalue' | Hnot_value'].
        -- assert (poly_active_wf function') as Hfunction'_active.
           { eapply poly_step_preserves_active_wf; eauto. }
           pose proof
             (poly_active_wf_value_no_run _ Hvalue' Hfunction'_active)
             as Hfunction'_no_run.
           rewrite Hargument_rates.
           rewrite (poly_no_run_running_rates_empty _ Hfunction'_no_run)
             in Hbalance.
           exact Hbalance.
        -- exact Hbalance.
    + contradiction.
  - intros Hactive. inversion Hactive; subst.
    + contradiction.
    + match goal with
      | Hfunction_value : poly_value function,
        Hargument_active : poly_active_wf argument |- _ =>
          pose proof (IHHstep Hargument_active) as Hbalance;
          destruct (poly_value_dec function) as [Hvalue | Hnot_value]
      end.
      * exact Hbalance.
      * contradiction.
  - intros Hactive. inversion Hactive; subst.
    match goal with Hguard_active : poly_active_wf guard |- _ =>
      exact (IHHstep Hguard_active)
    end.
  - intros Hactive. inversion Hactive; subst.
    match goal with Hbranches_active :
      Forall poly_active_wf (prefix ++ branch :: suffix) |- _ =>
        pose proof
          (IHHstep
            (Forall_middle _ poly_active_wf _ _ _ Hbranches_active))
          as Hbalance
    end.
    simpl. rewrite !map_app, !concat_app. simpl. rewrite !length_app.
    lia.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - intros Hactive. inversion Hactive; subst.
    match goal with Habs : poly_active_wf (PEAbsEff _) |- _ =>
      inversion Habs; subst
    end.
    unfold poly_effect_subst0.
    rewrite (poly_no_run_running_rates_empty _
      (poly_effect_subst_preserves_no_run _ _ ltac:(eassumption))).
    reflexivity.
  - intros Hactive. inversion Hactive; subst. apply IHHstep. assumption.
  - exact I.
Qed.

(** Direct successful-step form of the running-count/counter balance law. *)
Lemma poly_step_counter_balance :
  forall B e active e' active',
    poly_step B (PolyConfig e active) (PolyConfig e' active') ->
    poly_active_wf e ->
    (length (poly_running_rates e') + active =
     length (poly_running_rates e) + active')%nat.
Proof.
  intros B e active e' active' Hstep Hactive.
  pose proof (poly_step_counter_balance_general B _ _ Hstep) as Hbalance.
  simpl in Hbalance. apply Hbalance. exact Hactive.
Qed.

(** Iterated balance law, generalized to an arbitrary initial counter. The
    source-rate term makes the invariant stable even before specializing to a
    source expression with no running forms. *)
Lemma poly_successful_steps_counter_balance :
  forall B source initial_active target target_active,
    poly_source source ->
    poly_successful_steps B source initial_active target target_active ->
    (initial_active + length (poly_running_rates target) =
     target_active + length (poly_running_rates source))%nat.
Proof.
  intros B source initial_active target target_active Hsource Hsteps.
  induction Hsteps.
  - lia.
  - pose proof (IHHsteps Hsource) as Hprefix_balance.
    pose proof
      (poly_reachable_source_active_wf _ _ _ _ _ Hsource Hsteps)
      as Hactive.
    pose proof (poly_step_counter_balance _ _ _ _ _ H Hactive) as Hbalance.
    lia.
Qed.

(** The operational counter agrees with the number of evaluation-active
    running forms at every successful state reached from source syntax. *)
Theorem poly_counter_agreement :
  forall B source target target_active,
    poly_source source ->
    poly_successful_steps B source 0 target target_active ->
    target_active = length (poly_running_rates target).
Proof.
  intros B source target target_active Hsource Hsteps.
  pose proof
    (poly_successful_steps_counter_balance
      _ _ _ _ _ Hsource Hsteps) as Hbalance.
  rewrite (poly_no_run_running_rates_empty _ (poly_source_no_run _ Hsource))
    in Hbalance.
  simpl in Hbalance. lia.
Qed.

(** A rate exposed by one distinguished parallel child is exposed by the whole
    parallel expression. *)
Lemma poly_running_rate_in_parallel_middle :
  forall prefix branch suffix required_rate,
    In required_rate (poly_running_rates branch) ->
    In required_rate
      (poly_running_rates (PEParallel (prefix ++ branch :: suffix))).
Proof.
  intros prefix branch suffix required_rate Hin. simpl.
  apply in_concat. exists (poly_running_rates branch). split.
  - apply in_map_iff. exists branch. split; [reflexivity |].
    apply in_or_app. right. simpl. auto.
  - exact Hin.
Qed.

(** Extend error exposure to arbitrary transition endpoints. Only transitions
    to [PolyError] expose an under-provisioned running rate. *)
Definition poly_error_exposure_transition
    (B : Q) (source target : poly_configuration) : Prop :=
  match source, target with
  | PolyConfig e active, PolyError =>
      exists required_rate,
        In required_rate (poly_running_rates e) /\
        (0 < active)%nat /\
        B / qnat active < required_rate
  | _, _ => True
  end.

(** Every error-producing transition is rooted at a concrete running download
    whose fair bandwidth share is below its required rate. Contextual error
    rules preserve membership in [poly_running_rates]. *)
Lemma poly_step_error_exposure_general :
  forall B source target,
    poly_step B source target ->
    poly_error_exposure_transition B source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl in *.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct H as [Hpositive Hrate].
    exists (download_rate size timeout). simpl. auto.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    exists required_rate. repeat split; assumption.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    destruct (poly_value_dec function) as [Hvalue | Hnot_value].
    + exfalso. eapply poly_value_no_step; eauto.
    + exists required_rate. repeat split; assumption.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    destruct (poly_value_dec function) as [Hvalue | Hnot_value].
    + exists required_rate. repeat split; assumption.
    + contradiction.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    exists required_rate. repeat split; assumption.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    exists required_rate. repeat split; try assumption.
    eapply poly_running_rate_in_parallel_middle. exact Hin.
  - exact I.
  - exact I.
  - exact IHHstep.
Qed.

(** Direct error-step form used by bandwidth safety. *)
Theorem poly_error_exposure :
  forall B e active,
    poly_step B (PolyConfig e active) PolyError ->
    exists required_rate,
      In required_rate (poly_running_rates e) /\
      (0 < active)%nat /\
      B / qnat active < required_rate.
Proof.
  intros B e active Hstep.
  pose proof (poly_step_error_exposure_general B _ _ Hstep) as Hexposed.
  exact Hexposed.
Qed.
