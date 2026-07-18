(** Counter agreement, error exposure, and the final bandwidth-safety theorem.

    This file assembles the static and dynamic invariants proved earlier. The
    key operational balance lemma states that one successful step changes the
    number of exposed running forms by exactly the same amount as it changes
    the global counter. *)

From Stdlib Require Import Arith Lia Lra List QArith Qfield ZArith.
From BandwidthTimeout Require Import
  Effects Normalization Bandwidth Syntax Substitution Typing Semantics
  ActiveWF ActiveEffects Preservation.

Import ListNotations.
Open Scope Q_scope.

(** If every expression in a list contains no running form, concatenating all
    of their active rate multisets gives the empty multiset. *)
Lemma Forall_no_run_running_rates_empty :
  forall expressions,
    Forall no_run expressions ->
    concat (map running_rates expressions) = [].
Proof.
  intros expressions Hno. induction Hno; simpl.
  - reflexivity.
  - rewrite (no_run_running_rates_empty _ H), IHHno. reflexivity.
Qed.

(** Extend the running-count/counter balance equation to arbitrary transition
    endpoints. Error targets do not participate in counter agreement. *)
Definition counter_balance_transition
    (source target : configuration) : Prop :=
  match source, target with
  | Config e active, Config e' active' =>
      active_wf e ->
      (length (running_rates e') + active =
       length (running_rates e) + active')%nat
  | _, _ => True
  end.

(** One successful step changes the explicit running-form count and the global
    active-download counter in lockstep. [active_wf] is essential for the pure
    redexes: it rules out hidden running forms in discarded dormant syntax. *)
Lemma step_counter_balance_general :
  forall B source target,
    step B source target ->
    counter_balance_transition source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl in *.
  - intros Hactive. inversion Hactive; subst.
    match goal with
    | Hbound_active : active_wf bound,
      Hbody_no_run : no_run body |- _ =>
        pose proof
          (active_wf_value_no_run _ H Hbound_active) as Hbound_no_run;
        pose proof
          (subst0_preserves_no_run _ _ Hbound_no_run Hbody_no_run)
          as Hresult_no_run;
        rewrite (no_run_running_rates_empty _ Hbound_no_run),
          (no_run_running_rates_empty _ Hbody_no_run),
          (no_run_running_rates_empty _ Hresult_no_run)
    end.
    reflexivity.
  - intros Hactive. inversion Hactive; subst.
    + exfalso. match goal with
      | Hnot_value : ~ value (ELambda _ _) |- _ =>
          apply Hnot_value; constructor
      end.
    + match goal with
      | Hlambda_no_run : no_run (ELambda _ _) |- _ =>
          inversion Hlambda_no_run; subst
      end.
      match goal with
      | Hbody_no_run : no_run body,
        Hargument_active : active_wf argument,
        Hargument_value : value argument |- _ =>
          pose proof
            (active_wf_value_no_run _ Hargument_value Hargument_active)
            as Hargument_no_run;
          pose proof
            (subst0_preserves_no_run _ _ Hargument_no_run Hbody_no_run)
            as Hresult_no_run;
          rewrite (no_run_running_rates_empty _ Hargument_no_run),
            (no_run_running_rates_empty _ Hresult_no_run)
      end.
      reflexivity.
  - intros Hactive. inversion Hactive; subst.
    match goal with
    | Hzero_no_run : no_run zero_branch,
      Hnonzero_no_run : no_run nonzero_branch |- _ =>
        rewrite (no_run_running_rates_empty _ Hzero_no_run),
          (no_run_running_rates_empty _ Hnonzero_no_run)
    end.
    reflexivity.
  - intros Hactive. inversion Hactive; subst.
    match goal with
    | Hzero_no_run : no_run zero_branch,
      Hnonzero_no_run : no_run nonzero_branch |- _ =>
        rewrite (no_run_running_rates_empty _ Hzero_no_run),
          (no_run_running_rates_empty _ Hnonzero_no_run)
    end.
    reflexivity.
  - intros Hactive. inversion Hactive; subst.
    match goal with Hbranches_active : Forall active_wf branches |- _ =>
      pose proof
        (Forall_values_active_wf_no_run _ H Hbranches_active)
        as Hbranches_no_run;
      rewrite (Forall_no_run_running_rates_empty _ Hbranches_no_run)
    end.
    reflexivity.
  - intros Hactive. simpl. lia.
  - intros Hactive. simpl. lia.
  - exact I.
  - intros Hactive. inversion Hactive; subst.
    match goal with
    | Hbound_active : active_wf bound,
      Hbody_no_run : no_run body |- _ =>
        pose proof (IHHstep Hbound_active) as Hbalance;
        rewrite (no_run_running_rates_empty _ Hbody_no_run), !app_nil_r;
        exact Hbalance
    end.
  - intros Hactive.
    assert (~ value function) as Hfunction_not_value.
    { intro Hvalue. eapply value_no_successful_step; eauto. }
    inversion Hactive; subst.
    + match goal with
      | Hfunction_active : active_wf function,
        Hargument_no_run : no_run argument |- _ =>
          pose proof (IHHstep Hfunction_active) as Hbalance;
          rewrite (no_run_running_rates_empty _ Hargument_no_run),
            !app_nil_r;
          exact Hbalance
      end.
    + contradiction.
  - intros Hactive. inversion Hactive; subst.
    + contradiction.
    + match goal with
      | Hfunction_no_run : no_run function,
        Hargument_active : active_wf argument |- _ =>
          pose proof (IHHstep Hargument_active) as Hbalance;
          rewrite (no_run_running_rates_empty _ Hfunction_no_run);
          simpl;
          exact Hbalance
      end.
  - intros Hactive. inversion Hactive; subst.
    match goal with
    | Hguard_active : active_wf guard,
      Hzero_no_run : no_run zero_branch,
      Hnonzero_no_run : no_run nonzero_branch |- _ =>
        pose proof (IHHstep Hguard_active) as Hbalance;
        rewrite (no_run_running_rates_empty _ Hzero_no_run),
          (no_run_running_rates_empty _ Hnonzero_no_run), !app_nil_r;
        exact Hbalance
    end.
  - intros Hactive. inversion Hactive; subst.
    match goal with Hbranches_active :
      Forall active_wf (prefix ++ branch :: suffix) |- _ =>
        pose proof
          (IHHstep
            (Forall_middle _ active_wf _ _ _ Hbranches_active))
          as Hbalance
    end.
    simpl. rewrite !map_app, !concat_app. simpl. rewrite !length_app.
    lia.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** Direct successful-step form of the running-count/counter balance law. *)
Lemma step_counter_balance :
  forall B e active e' active',
    step B (Config e active) (Config e' active') ->
    active_wf e ->
    (length (running_rates e') + active =
     length (running_rates e) + active')%nat.
Proof.
  intros B e active e' active' Hstep Hactive.
  pose proof (step_counter_balance_general B _ _ Hstep) as Hbalance.
  simpl in Hbalance. apply Hbalance. exact Hactive.
Qed.

(** Iterated balance law, generalized to an arbitrary initial counter. The
    source-rate term makes the invariant stable even before specializing to a
    source expression with no running forms. *)
Lemma successful_steps_counter_balance :
  forall B source initial_active target target_active,
    source_expr source ->
    successful_steps B source initial_active target target_active ->
    (initial_active + length (running_rates target) =
     target_active + length (running_rates source))%nat.
Proof.
  intros B source initial_active target target_active Hsource Hsteps.
  induction Hsteps.
  - lia.
  - pose proof (IHHsteps Hsource) as Hprefix_balance.
    pose proof
      (reachable_source_active_wf _ _ _ _ _ Hsource Hsteps)
      as Hactive.
    pose proof (step_counter_balance _ _ _ _ _ H Hactive) as Hbalance.
    lia.
Qed.

(** The operational counter agrees with the number of evaluation-active
    running forms at every successful state reached from source syntax. *)
Theorem counter_agreement :
  forall B source target target_active,
    source_expr source ->
    successful_steps B source 0 target target_active ->
    target_active = length (running_rates target).
Proof.
  intros B source target target_active Hsource Hsteps.
  pose proof
    (successful_steps_counter_balance
      _ _ _ _ _ Hsource Hsteps) as Hbalance.
  rewrite (no_run_running_rates_empty _ (source_no_run _ Hsource))
    in Hbalance.
  simpl in Hbalance. lia.
Qed.

(** A rate exposed by one distinguished parallel child is exposed by the whole
    parallel expression. *)
Lemma running_rate_in_parallel_middle :
  forall prefix branch suffix required_rate,
    In required_rate (running_rates branch) ->
    In required_rate
      (running_rates (EParallel (prefix ++ branch :: suffix))).
Proof.
  intros prefix branch suffix required_rate Hin. simpl.
  apply in_concat. exists (running_rates branch). split.
  - apply in_map_iff. exists branch. split; [reflexivity |].
    apply in_or_app. right. simpl. auto.
  - exact Hin.
Qed.

(** Extend error exposure to arbitrary transition endpoints. Only transitions
    to [Error] expose an under-provisioned running rate. *)
Definition error_exposure_transition
    (B : Q) (source target : configuration) : Prop :=
  match source, target with
  | Config e active, Error =>
      exists required_rate,
        In required_rate (running_rates e) /\
        (0 < active)%nat /\
        B / qnat active < required_rate
  | _, _ => True
  end.

(** Every error-producing transition is rooted at a concrete running download
    whose fair bandwidth share is below its required rate. Contextual error
    rules preserve membership in [running_rates]. *)
Lemma step_error_exposure_general :
  forall B source target,
    step B source target ->
    error_exposure_transition B source target.
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
    exists required_rate. simpl. repeat split; try assumption.
    apply in_or_app. left. exact Hin.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    exists required_rate. simpl. repeat split; try assumption.
    apply in_or_app. left. exact Hin.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    exists required_rate. simpl. repeat split; try assumption.
    apply in_or_app. right. exact Hin.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    exists required_rate. simpl. repeat split; try assumption.
    apply in_or_app. left. exact Hin.
  - destruct IHHstep as [required_rate [Hin [Hpositive Hrate]]].
    exists required_rate. repeat split; try assumption.
    eapply running_rate_in_parallel_middle. exact Hin.
Qed.

(** Direct error-step form used by bandwidth safety. *)
Theorem error_exposure :
  forall B e active,
    step B (Config e active) Error ->
    exists required_rate,
      In required_rate (running_rates e) /\
      (0 < active)%nat /\
      B / qnat active < required_rate.
Proof.
  intros B e active Hstep.
  pose proof (step_error_exposure_general B _ _ Hstep) as Hexposed.
  exact Hexposed.
Qed.

(** Coverage of an obligation transports through effect overapproximation. *)
Lemma covers_effect_le :
  forall Phi Psi p,
    covers Phi p ->
    Phi ≼ Psi ->
    covers Psi p.
Proof.
  intros Phi Psi p [q [Hq Hpq]] Hle.
  eapply covers_weaken_obligation; [exact Hpq |].
  apply Hle. exact Hq.
Qed.

(** Positive natural numbers embed as strictly positive rationals. *)
Lemma qnat_positive :
  forall n,
    (0 < n)%nat ->
    0 < qnat n.
Proof.
  intros n Hpositive. unfold qnat.
  change (inject_Z 0 < inject_Z (Z.of_nat n)).
  rewrite <- Zlt_Qlt. lia.
Qed.

(** The paper's final safety theorem. A closed source typing whose computed
    bandwidth requirement fits within [B] cannot have a successful execution
    prefix followed by a bandwidth-error step. *)
Theorem bandwidth_safety :
  forall B source T Phi,
    source_has_type [] source T Phi ->
    required_bandwidth Phi <= B ->
    ~ exists target active,
        successful_steps B source 0 target active /\
        step B (Config target active) Error.
Proof.
  intros B source T Phi [Hsource Htyping] Hbudget
    [target [active [Hsteps Herror]]].
  destruct (preservation_successful_steps
    _ _ _ _ _ _ _ _ Hsteps Htyping)
    as [Phi_current [Htyping_current Hcurrent_le]].
  pose proof
    (reachable_active_effect_coverage
      _ _ _ _ _ _ _ Hsource Hsteps Htyping_current)
    as Hactive_le.
  pose proof (counter_agreement _ _ _ _ Hsource Hsteps) as Hcounter.
  destruct (error_exposure _ _ _ Herror)
    as [required_rate [Hrate_in [Hpositive Hunder]]].
  assert (Hactive_covers :
    covers (active_effect (running_rates target))
      (Obligation required_rate active)).
  { unfold active_effect.
    apply (le_normalize
      (map (fun current_rate =>
        Obligation current_rate (length (running_rates target)))
        (running_rates target))).
    apply in_map_iff. exists required_rate. split.
    - f_equal. symmetry. exact Hcounter.
    - exact Hrate_in. }
  assert (Htop_covers : covers Phi (Obligation required_rate active)).
  { eapply covers_effect_le.
    - eapply covers_effect_le; eauto.
    - exact Hcurrent_le. }
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
    obligation_bandwidth top_obligation <= required_bandwidth Phi).
  { apply obligation_bandwidth_le_required. exact Htop_in. }
  assert (Htoo_much : B < required_bandwidth Phi).
  { eapply Qlt_le_trans.
    - exact Herror_bandwidth.
    - eapply Qle_trans; eauto. }
  exact (Qlt_not_le _ _ Htoo_much Hbudget).
Qed.
