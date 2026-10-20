(** Evaluation-active running downloads and runtime well-formedness.

    This file follows the paper's running-download appendix. [poly_running_rates]
    observes only evaluation-active positions, while [poly_no_run] inspects every
    syntactic position, including dormant function bodies and tuple contents.
    [poly_active_wf] connects the two views by requiring every dormant position to
    contain no runtime-only running download. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import
  Effects Normalization Syntax Substitution Semantics PolymorphicEffects
  PolymorphicSyntax PolymorphicSemantics.

Import ListNotations.
Open Scope Q_scope.

(** Runtime values are syntactically decidable. Besides selecting the
    appropriate application clause of [poly_active_wf], this decision lets
    [poly_running_rates] follow the call-by-value evaluation focus. *)
Definition poly_value_dec : forall e, {poly_value e} + {~ poly_value e}.
Proof.
  fix IH 1. intro e. destruct e.
  - right. intro Hvalue. inversion Hvalue.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - destruct (Forall_dec poly_value IH l) as [Hvalues | Hnot_values].
    + left. constructor. exact Hvalues.
    + right. intro Hvalue. inversion Hvalue; subst. contradiction.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - left. constructor.
  - right. intro Hvalue. inversion Hvalue.
Defined.

(** Multiset of required rates exposed in evaluation-active positions. Lists
    represent multisets, so append and [concat] implement multiset union.

    The definition follows the current call-by-value focus directly: let and
    conditional bodies are dormant, and an application evaluates its argument
    only after its function has become a value. All parallel branches remain
    active and therefore contribute by multiset union. *)
Fixpoint poly_running_rates (e : poly_expr) : list Q :=
  match e with
  | PEVar _ => []
  | PEUnit => []
  | PENat _ => []
  | PELambda _ _ => []
  | PETuple _ => []
  | PEApp function argument =>
      if poly_value_dec function
      then poly_running_rates argument
      else poly_running_rates function
  | PELet bound _ => poly_running_rates bound
  | PEIfZero guard _ _ => poly_running_rates guard
  | PEDownload _ _ => []
  | PERunning size timeout => [download_rate size timeout]
  | PEParallel branches => concat (map poly_running_rates branches)
  | PEAbsEff _ => []
  | PEAppEff e _ => poly_running_rates e
  end.

(** Convert the currently running rate multiset into obligations at the total
    active concurrency, then Pareto-normalize it. *)
Definition poly_active_effect (rates : list Q) : effect :=
  normalize
    (map (fun required_rate =>
      Obligation required_rate (length rates)) rates).

(** With no running rates there are no active obligations. *)
Lemma poly_active_effect_empty : poly_active_effect [] = [].
Proof. reflexivity. Qed.

(** No running download occurs anywhere in [e]. Unlike [poly_running_rates], this
    predicate descends into dormant lambda bodies and tuple components. There
    is deliberately no constructor for [PERunning]. *)
Inductive poly_no_run : poly_expr -> Prop :=
| poly_NoRunVar : forall index,
    poly_no_run (PEVar index)
| poly_NoRunUnit : poly_no_run PEUnit
| poly_NoRunNat : forall n,
    poly_no_run (PENat n)
| poly_NoRunLambda : forall parameter_ty body,
    poly_no_run body ->
    poly_no_run (PELambda parameter_ty body)
| poly_NoRunTuple : forall components,
    Forall poly_no_run components ->
    poly_no_run (PETuple components)
| poly_NoRunApp : forall function argument,
    poly_no_run function ->
    poly_no_run argument ->
    poly_no_run (PEApp function argument)
| poly_NoRunLet : forall bound body,
    poly_no_run bound ->
    poly_no_run body ->
    poly_no_run (PELet bound body)
| poly_NoRunIfZero : forall guard zero_branch nonzero_branch,
    poly_no_run guard ->
    poly_no_run zero_branch ->
    poly_no_run nonzero_branch ->
    poly_no_run (PEIfZero guard zero_branch nonzero_branch)
| poly_NoRunDownload : forall size timeout,
    poly_no_run (PEDownload size timeout)
| poly_NoRunParallel : forall branches,
    Forall poly_no_run branches ->
    poly_no_run (PEParallel branches)
| poly_NoRunAbsEff : forall body, poly_no_run body ->
    poly_no_run (PEAbsEff body)
| poly_NoRunAppEff : forall e F, poly_no_run e ->
    poly_no_run (PEAppEff e F).

(** Every source expression contains no runtime-only running download. *)
Lemma poly_source_no_run :
  forall e,
    poly_source e ->
    poly_no_run e.
Proof.
  fix IH 2. intros e Hsource. destruct Hsource.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IH. assumption.
  - apply poly_NoRunTuple. clear H. induction H0.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - apply poly_NoRunParallel. induction H.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor. apply IH. assumption.
  - constructor. apply IH. assumption.
Qed.

(** If no running form occurs anywhere, the active running-rate multiset is
    empty. The converse is false for dormant occurrences inside lambdas. *)
Lemma poly_no_run_running_rates_empty :
  forall e,
    poly_no_run e ->
    poly_running_rates e = [].
Proof.
  fix IH 2. intros e Hno. destruct Hno; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - destruct (poly_value_dec function).
    + match goal with Hargument : poly_no_run argument |- _ =>
        rewrite (IH argument Hargument); reflexivity
      end.
    + match goal with Hfunction : poly_no_run function |- _ =>
        rewrite (IH function Hfunction); reflexivity
      end.
  - match goal with
    | Hbound : poly_no_run ?bound |- _ =>
        rewrite (IH bound Hbound); reflexivity
    end.
  - match goal with
    | Hguard : poly_no_run ?guard |- _ =>
        rewrite (IH guard Hguard); reflexivity
    end.
  - reflexivity.
  - match goal with Hbranches : Forall poly_no_run ?branches |- _ =>
      induction Hbranches
    end.
    + reflexivity.
    + simpl. rewrite (IH _ H), IHForall. reflexivity.
  - reflexivity.
  - apply IH. assumption.
Qed.

(** Renaming variable indices cannot introduce or remove a running-download
    constructor, so it preserves [poly_no_run]. *)
Lemma poly_rename_preserves_no_run :
  forall xi e,
    poly_no_run e ->
    poly_no_run (poly_rename xi e).
Proof.
  fix IH 3. intros xi e Hno. destruct Hno; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eapply IH. eassumption.
  - apply poly_NoRunTuple.
    match goal with Hcomponents : Forall poly_no_run ?components |- _ =>
      induction Hcomponents
    end; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - apply poly_NoRunParallel.
    match goal with Hbranches : Forall poly_no_run ?branches |- _ =>
      induction Hbranches
    end; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor. apply IH. assumption.
  - constructor. apply IH. assumption.
Qed.

Lemma poly_effect_rename_preserves_no_run :
  forall xi e,
    poly_no_run e ->
    poly_no_run (poly_effect_rename xi e).
Proof.
  fix IH 3. intros xi e Hno. destruct Hno; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eapply IH. eassumption.
  - apply poly_NoRunTuple.
    match goal with Hcomponents : Forall poly_no_run ?components |- _ =>
      induction Hcomponents
    end; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - apply poly_NoRunParallel.
    match goal with Hbranches : Forall poly_no_run ?branches |- _ =>
      induction Hbranches
    end; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor. apply IH. assumption.
  - constructor. apply IH. assumption.
Qed.

Lemma poly_effect_subst_preserves_no_run :
  forall xi e,
    poly_no_run e ->
    poly_no_run (poly_effect_subst xi e).
Proof.
  fix IH 3. intros xi e Hno. destruct Hno; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eapply IH. eassumption.
  - apply poly_NoRunTuple.
    match goal with Hcomponents : Forall poly_no_run ?components |- _ =>
      induction Hcomponents
    end; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - apply poly_NoRunParallel.
    match goal with Hbranches : Forall poly_no_run ?branches |- _ =>
      induction Hbranches
    end; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor. apply IH. assumption.
  - constructor. apply IH. assumption.
Qed.

(** A substitution whose every replacement has no running form remains safe
    when lifted through a binder. Older replacements are renamed, which is
    harmless by [poly_rename_preserves_no_run]. *)
Lemma poly_up_subst_preserves_no_run :
  forall sigma,
    (forall index, poly_no_run (sigma index)) ->
    forall index, poly_no_run (poly_up_subst sigma index).
Proof.
  intros sigma Hsigma [|index]; simpl.
  - constructor.
  - apply poly_rename_preserves_no_run. apply Hsigma.
Qed.

(** Simultaneous substitution preserves absence of running forms when both the
    original term and every replacement satisfy [poly_no_run]. *)
Lemma poly_subst_preserves_no_run :
  forall sigma e,
    (forall index, poly_no_run (sigma index)) ->
    poly_no_run e ->
    poly_no_run (poly_subst sigma e).
Proof.
  fix IH 4. intros sigma e Hsigma Hno. destruct Hno; simpl.
  - apply Hsigma.
  - constructor.
  - constructor.
  - constructor. eapply IH.
    + apply poly_up_subst_preserves_no_run. exact Hsigma.
    + eassumption.
  - apply poly_NoRunTuple.
    match goal with Hcomponents : Forall poly_no_run ?components |- _ =>
      induction Hcomponents
    end; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
  - constructor; eapply IH; eauto.
  - constructor.
    + eapply IH; eauto.
    + eapply IH.
      * apply poly_up_subst_preserves_no_run. exact Hsigma.
      * eassumption.
  - constructor; eapply IH; eauto.
  - constructor.
  - apply poly_NoRunParallel.
    match goal with Hbranches : Forall poly_no_run ?branches |- _ =>
      induction Hbranches
    end; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
  - constructor. eapply IH.
    + intros i. apply poly_effect_rename_preserves_no_run. apply Hsigma.
    + eassumption.
  - constructor. eapply IH; eauto.
Qed.

(** The single-binder substitution used by beta and let reduction preserves
    [poly_no_run] when both the replacement value and body satisfy it. *)
Lemma poly_subst0_preserves_no_run :
  forall replacement body,
    poly_no_run replacement ->
    poly_no_run body ->
    poly_no_run (poly_subst0 replacement body).
Proof.
  intros replacement body Hreplacement Hbody. unfold poly_subst0.
  eapply poly_subst_preserves_no_run.
  - intros [|index]; simpl; [exact Hreplacement | constructor].
  - exact Hbody.
Qed.

(** Every running download in an actively well-formed term occurs in a position
    currently evaluated by call-by-value reduction. The two application
    constructors switch from callee to argument precisely when the callee is a
    value. *)
Inductive poly_active_wf : poly_expr -> Prop :=
| poly_ActiveVar : forall index,
    poly_active_wf (PEVar index)
| poly_ActiveUnit : poly_active_wf PEUnit
| poly_ActiveNat : forall n,
    poly_active_wf (PENat n)
| poly_ActiveLambda : forall parameter_ty body,
    poly_no_run body ->
    poly_active_wf (PELambda parameter_ty body)
| poly_ActiveTuple : forall components,
    Forall poly_no_run components ->
    poly_active_wf (PETuple components)
| poly_ActiveAppFunction : forall function argument,
    ~ poly_value function ->
    poly_active_wf function ->
    poly_no_run argument ->
    poly_active_wf (PEApp function argument)
| poly_ActiveAppArgument : forall function argument,
    poly_value function ->
    poly_no_run function ->
    poly_active_wf argument ->
    poly_active_wf (PEApp function argument)
| poly_ActiveLet : forall bound body,
    poly_active_wf bound ->
    poly_no_run body ->
    poly_active_wf (PELet bound body)
| poly_ActiveIfZero : forall guard zero_branch nonzero_branch,
    poly_active_wf guard ->
    poly_no_run zero_branch ->
    poly_no_run nonzero_branch ->
    poly_active_wf (PEIfZero guard zero_branch nonzero_branch)
| poly_ActiveDownload : forall size timeout,
    poly_active_wf (PEDownload size timeout)
| poly_ActiveRunning : forall size timeout,
    poly_active_wf (PERunning size timeout)
| poly_ActiveParallel : forall branches,
    Forall poly_active_wf branches ->
    poly_active_wf (PEParallel branches)
| poly_ActiveAbsEff : forall body, poly_no_run body ->
    poly_active_wf (PEAbsEff body)
| poly_ActiveAppEff : forall e F, poly_active_wf e ->
    poly_active_wf (PEAppEff e F).

(** A term containing no running form is actively well formed, because all
    potentially dormant positions are safe. *)
Lemma poly_no_run_implies_active_wf :
  forall e,
    poly_no_run e ->
    poly_active_wf e.
Proof.
  fix IH 2. intros e Hno. destruct Hno.
  - constructor.
  - constructor.
  - constructor.
  - constructor. assumption.
  - constructor. assumption.
  - destruct (poly_value_dec function) as [Hvalue | Hnot_value].
    + eapply poly_ActiveAppArgument; eauto.
    + eapply poly_ActiveAppFunction; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - apply poly_ActiveParallel.
    match goal with Hbranches : Forall poly_no_run ?branches |- _ =>
      induction Hbranches
    end.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor. assumption.
  - constructor. apply IH. assumption.
Qed.

(** An actively well-formed runtime value cannot hide a running download in a
    dormant function body or tuple component. *)
Lemma poly_active_wf_value_no_run :
  forall v,
    poly_value v ->
    poly_active_wf v ->
    poly_no_run v.
Proof.
  intros v Hvalue Hactive. destruct Hvalue; inversion Hactive; subst.
  - constructor.
  - constructor.
  - constructor. assumption.
  - constructor. assumption.
  - constructor. assumption.
Qed.

(** A runtime value cannot take a successful expression-to-expression step. *)
Lemma poly_value_no_successful_step :
  forall B v active e' active',
    poly_value v ->
    ~ poly_step B (PolyConfig v active) (PolyConfig e' active').
Proof.
  intros B v active e' active' Hvalue Hstep.
  inversion Hstep; subst; inversion Hvalue.
Qed.

(** If a list consists of actively well-formed values, every member contains
    no hidden running download. *)
Lemma poly_Forall_values_active_wf_no_run :
  forall values,
    Forall poly_value values ->
    Forall poly_active_wf values ->
    Forall poly_no_run values.
Proof.
  intros values Hvalues. induction Hvalues; intros Hactive.
  - constructor.
  - inversion Hactive; subst. constructor.
    + eapply poly_active_wf_value_no_run; eauto.
    + apply IHHvalues. exact H3.
Qed.

(** Extend [poly_active_wf] to arbitrary transition endpoints. Only a successful
    expression target has an invariant to preserve; an error target is ignored
    by this one-step lemma and handled separately by bandwidth safety. *)
Definition poly_active_wf_transition
    (source target : poly_configuration) : Prop :=
  match source, target with
  | PolyConfig e _, PolyConfig e' _ => poly_active_wf e -> poly_active_wf e'
  | _, _ => True
  end.

(** Every successful reduction preserves active runtime well-formedness. This
    proof follows the operational rules and the corresponding appendix proof. *)
Lemma poly_step_preserves_active_wf_general :
  forall B source target,
    poly_step B source target ->
    poly_active_wf_transition source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl in *.
  - intros Hactive. inversion Hactive; subst.
    apply poly_no_run_implies_active_wf.
    apply poly_subst0_preserves_no_run.
    + eapply poly_active_wf_value_no_run; eauto.
    + assumption.
  - intros Hactive.
    inversion Hactive; subst.
    + exfalso. match goal with
      | Hnot : ~ poly_value (PELambda _ _) |- _ => apply Hnot; constructor
      end.
    + apply poly_no_run_implies_active_wf. apply poly_subst0_preserves_no_run.
      * eapply poly_active_wf_value_no_run; eauto.
      * match goal with Hlambda : poly_no_run (PELambda _ _) |- _ =>
          inversion Hlambda; subst; assumption
        end.
  - intros Hactive. inversion Hactive; subst.
    apply poly_no_run_implies_active_wf. assumption.
  - intros Hactive. inversion Hactive; subst.
    apply poly_no_run_implies_active_wf. assumption.
  - intros Hactive. inversion Hactive; subst.
    apply poly_ActiveTuple. eapply poly_Forall_values_active_wf_no_run; eauto.
  - intros Hactive. constructor.
  - intros Hactive. constructor.
  - exact I.
  - intros Hactive. inversion Hactive; subst. constructor.
    + apply IHHstep. assumption.
    + assumption.
  - intros Hactive.
    assert (~ poly_value function) as Hfunction_not_value.
    { intro Hvalue. eapply poly_value_no_successful_step; eauto. }
    inversion Hactive; subst.
    + match goal with
      | Hfunction_active : poly_active_wf function,
        Hargument_no_run : poly_no_run argument |- _ =>
          pose proof (IHHstep Hfunction_active) as Hfunction'
      end.
      destruct (poly_value_dec function') as [Hvalue' | Hnot_value'].
      * apply poly_ActiveAppArgument.
        -- exact Hvalue'.
        -- eapply poly_active_wf_value_no_run; eauto.
        -- apply poly_no_run_implies_active_wf. assumption.
      * apply poly_ActiveAppFunction; assumption.
    + contradiction.
  - intros Hactive.
    inversion Hactive; subst.
    + contradiction.
    + apply poly_ActiveAppArgument.
      * assumption.
      * assumption.
      * apply IHHstep. assumption.
  - intros Hactive. inversion Hactive; subst. constructor.
    + apply IHHstep. assumption.
    + assumption.
    + assumption.
  - intros Hactive. inversion Hactive; subst. apply poly_ActiveParallel.
    eapply Forall_replace_middle.
    + eassumption.
    + apply IHHstep. eapply Forall_middle. eassumption.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - intros Hactive. inversion Hactive; subst.
    match goal with Habs : poly_active_wf (PEAbsEff _) |- _ =>
      inversion Habs; subst
    end.
    apply poly_no_run_implies_active_wf.
    apply poly_effect_subst_preserves_no_run. assumption.
  - intros Hactive. inversion Hactive; subst. constructor.
    apply IHHstep. assumption.
  - exact I.
Qed.

(** Direct successful-step form of [poly_active_wf] preservation. *)
Theorem poly_step_preserves_active_wf :
  forall B e active e' active',
    poly_step B (PolyConfig e active) (PolyConfig e' active') ->
    poly_active_wf e ->
    poly_active_wf e'.
Proof.
  intros B e active e' active' Hstep Hactive.
  pose proof
    (poly_step_preserves_active_wf_general B _ _ Hstep) as Hpreserves.
  simpl in Hpreserves. apply Hpreserves. exact Hactive.
Qed.

(** Every successful state reachable from a source expression is actively well
    formed. The initial counter is arbitrary here; the later counter-agreement
    theorem specializes it to [0]. *)
Theorem poly_reachable_source_active_wf :
  forall B source initial_active target target_active,
    poly_source source ->
    poly_successful_steps B
      source initial_active target target_active ->
    poly_active_wf target.
Proof.
  intros B source initial_active target target_active Hsource Hsteps.
  induction Hsteps.
  - apply poly_no_run_implies_active_wf. apply poly_source_no_run. exact Hsource.
  - eapply poly_step_preserves_active_wf; eauto.
Qed.
