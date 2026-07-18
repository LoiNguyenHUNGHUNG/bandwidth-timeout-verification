(** Evaluation-active running downloads and runtime well-formedness.

    This file follows the paper's running-download appendix. [running_rates]
    observes only evaluation-active positions, while [no_run] inspects every
    syntactic position, including dormant function bodies and tuple contents.
    [active_wf] connects the two views by requiring every dormant position to
    contain no runtime-only running download. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import
  Effects Normalization Syntax Substitution Semantics.

Import ListNotations.
Open Scope Q_scope.

(** Multiset of required rates exposed in evaluation-active positions. Lists
    represent multisets, so append and [concat] implement multiset union.

    Lambda bodies and tuple components are dormant and therefore contribute
    nothing. Sequentially dormant positions are included structurally here;
    [active_wf] will prove that their contribution is empty in reachable
    states. *)
Fixpoint running_rates (e : expr) : list Q :=
  match e with
  | EVar _ => []
  | EUnit => []
  | ENat _ => []
  | ELambda _ _ => []
  | ETuple _ => []
  | EApp function argument =>
      running_rates function ++ running_rates argument
  | ELet bound body =>
      running_rates bound ++ running_rates body
  | EIfZero guard zero_branch nonzero_branch =>
      running_rates guard ++
      running_rates zero_branch ++
      running_rates nonzero_branch
  | EDownload _ _ => []
  | ERunning size timeout => [download_rate size timeout]
  | EParallel branches => concat (map running_rates branches)
  end.

(** Convert the currently running rate multiset into obligations at the total
    active concurrency, then Pareto-normalize it. *)
Definition active_effect (rates : list Q) : effect :=
  normalize
    (map (fun required_rate =>
      Obligation required_rate (length rates)) rates).

(** With no running rates there are no active obligations. *)
Lemma active_effect_empty : active_effect [] = [].
Proof. reflexivity. Qed.

(** No running download occurs anywhere in [e]. Unlike [running_rates], this
    predicate descends into dormant lambda bodies and tuple components. There
    is deliberately no constructor for [ERunning]. *)
Inductive no_run : expr -> Prop :=
| NoRunVar : forall index,
    no_run (EVar index)
| NoRunUnit : no_run EUnit
| NoRunNat : forall n,
    no_run (ENat n)
| NoRunLambda : forall parameter_ty body,
    no_run body ->
    no_run (ELambda parameter_ty body)
| NoRunTuple : forall components,
    Forall no_run components ->
    no_run (ETuple components)
| NoRunApp : forall function argument,
    no_run function ->
    no_run argument ->
    no_run (EApp function argument)
| NoRunLet : forall bound body,
    no_run bound ->
    no_run body ->
    no_run (ELet bound body)
| NoRunIfZero : forall guard zero_branch nonzero_branch,
    no_run guard ->
    no_run zero_branch ->
    no_run nonzero_branch ->
    no_run (EIfZero guard zero_branch nonzero_branch)
| NoRunDownload : forall size timeout,
    no_run (EDownload size timeout)
| NoRunParallel : forall branches,
    Forall no_run branches ->
    no_run (EParallel branches).

(** Every source expression contains no runtime-only running download. *)
Lemma source_no_run :
  forall e,
    source_expr e ->
    no_run e.
Proof.
  fix IH 2. intros e Hsource. destruct Hsource.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IH. assumption.
  - apply NoRunTuple. clear H. induction H0.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - apply NoRunParallel. induction H.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** If no running form occurs anywhere, the active running-rate multiset is
    empty. The converse is false for dormant occurrences inside lambdas. *)
Lemma no_run_running_rates_empty :
  forall e,
    no_run e ->
    running_rates e = [].
Proof.
  fix IH 2. intros e Hno. destruct Hno; simpl.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - match goal with
    | Hfunction : no_run ?function,
      Hargument : no_run ?argument |- _ =>
        rewrite (IH function Hfunction), (IH argument Hargument);
        reflexivity
    end.
  - match goal with
    | Hbound : no_run ?bound,
      Hbody : no_run ?body |- _ =>
        rewrite (IH bound Hbound), (IH body Hbody); reflexivity
    end.
  - match goal with
    | Hguard : no_run ?guard,
      Hzero : no_run ?zero_branch,
      Hnonzero : no_run ?nonzero_branch |- _ =>
        rewrite (IH guard Hguard),
          (IH zero_branch Hzero),
          (IH nonzero_branch Hnonzero);
        reflexivity
    end.
  - reflexivity.
  - match goal with Hbranches : Forall no_run ?branches |- _ =>
      induction Hbranches
    end.
    + reflexivity.
    + simpl. rewrite (IH _ H), IHForall. reflexivity.
Qed.

(** Renaming variable indices cannot introduce or remove a running-download
    constructor, so it preserves [no_run]. *)
Lemma rename_preserves_no_run :
  forall xi e,
    no_run e ->
    no_run (rename xi e).
Proof.
  fix IH 3. intros xi e Hno. destruct Hno; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. eapply IH. eassumption.
  - apply NoRunTuple.
    match goal with Hcomponents : Forall no_run ?components |- _ =>
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
  - apply NoRunParallel.
    match goal with Hbranches : Forall no_run ?branches |- _ =>
      induction Hbranches
    end; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** A substitution whose every replacement has no running form remains safe
    when lifted through a binder. Older replacements are renamed, which is
    harmless by [rename_preserves_no_run]. *)
Lemma up_subst_preserves_no_run :
  forall sigma,
    (forall index, no_run (sigma index)) ->
    forall index, no_run (up_subst sigma index).
Proof.
  intros sigma Hsigma [|index]; simpl.
  - constructor.
  - apply rename_preserves_no_run. apply Hsigma.
Qed.

(** Simultaneous substitution preserves absence of running forms when both the
    original term and every replacement satisfy [no_run]. *)
Lemma subst_preserves_no_run :
  forall sigma e,
    (forall index, no_run (sigma index)) ->
    no_run e ->
    no_run (subst sigma e).
Proof.
  fix IH 4. intros sigma e Hsigma Hno. destruct Hno; simpl.
  - apply Hsigma.
  - constructor.
  - constructor.
  - constructor. eapply IH.
    + apply up_subst_preserves_no_run. exact Hsigma.
    + eassumption.
  - apply NoRunTuple.
    match goal with Hcomponents : Forall no_run ?components |- _ =>
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
      * apply up_subst_preserves_no_run. exact Hsigma.
      * eassumption.
  - constructor; eapply IH; eauto.
  - constructor.
  - apply NoRunParallel.
    match goal with Hbranches : Forall no_run ?branches |- _ =>
      induction Hbranches
    end; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
Qed.

(** The single-binder substitution used by beta and let reduction preserves
    [no_run] when both the replacement value and body satisfy it. *)
Lemma subst0_preserves_no_run :
  forall replacement body,
    no_run replacement ->
    no_run body ->
    no_run (subst0 replacement body).
Proof.
  intros replacement body Hreplacement Hbody. unfold subst0.
  eapply subst_preserves_no_run.
  - intros [|index]; simpl; [exact Hreplacement | constructor].
  - exact Hbody.
Qed.

(** Every running download in an actively well-formed term occurs in a position
    currently evaluated by call-by-value reduction. The two application
    constructors switch from callee to argument precisely when the callee is a
    value. *)
Inductive active_wf : expr -> Prop :=
| ActiveVar : forall index,
    active_wf (EVar index)
| ActiveUnit : active_wf EUnit
| ActiveNat : forall n,
    active_wf (ENat n)
| ActiveLambda : forall parameter_ty body,
    no_run body ->
    active_wf (ELambda parameter_ty body)
| ActiveTuple : forall components,
    Forall no_run components ->
    active_wf (ETuple components)
| ActiveAppFunction : forall function argument,
    ~ value function ->
    active_wf function ->
    no_run argument ->
    active_wf (EApp function argument)
| ActiveAppArgument : forall function argument,
    value function ->
    no_run function ->
    active_wf argument ->
    active_wf (EApp function argument)
| ActiveLet : forall bound body,
    active_wf bound ->
    no_run body ->
    active_wf (ELet bound body)
| ActiveIfZero : forall guard zero_branch nonzero_branch,
    active_wf guard ->
    no_run zero_branch ->
    no_run nonzero_branch ->
    active_wf (EIfZero guard zero_branch nonzero_branch)
| ActiveDownload : forall size timeout,
    active_wf (EDownload size timeout)
| ActiveRunning : forall size timeout,
    active_wf (ERunning size timeout)
| ActiveParallel : forall branches,
    Forall active_wf branches ->
    active_wf (EParallel branches).

(** Runtime values are syntactically decidable. This constructive decision is
    used only to select the appropriate application clause of [active_wf]. *)
Lemma value_dec : forall e, {value e} + {~ value e}.
Proof.
  fix IH 1. intro e. destruct e.
  - right. intro Hvalue. inversion Hvalue.
  - left. constructor.
  - left. constructor.
  - left. constructor.
  - destruct (Forall_dec value IH l) as [Hvalues | Hnot_values].
    + left. constructor. exact Hvalues.
    + right. intro Hvalue. inversion Hvalue; subst. contradiction.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
  - right. intro Hvalue. inversion Hvalue.
Qed.

(** A term containing no running form is actively well formed, because all
    potentially dormant positions are safe. *)
Lemma no_run_implies_active_wf :
  forall e,
    no_run e ->
    active_wf e.
Proof.
  fix IH 2. intros e Hno. destruct Hno.
  - constructor.
  - constructor.
  - constructor.
  - constructor. assumption.
  - constructor. assumption.
  - destruct (value_dec function) as [Hvalue | Hnot_value].
    + eapply ActiveAppArgument; eauto.
    + eapply ActiveAppFunction; eauto.
  - constructor; eauto.
  - constructor; eauto.
  - constructor.
  - apply ActiveParallel.
    match goal with Hbranches : Forall no_run ?branches |- _ =>
      induction Hbranches
    end.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** An actively well-formed runtime value cannot hide a running download in a
    dormant function body or tuple component. *)
Lemma active_wf_value_no_run :
  forall v,
    value v ->
    active_wf v ->
    no_run v.
Proof.
  intros v Hvalue Hactive. destruct Hvalue; inversion Hactive; subst.
  - constructor.
  - constructor.
  - constructor. assumption.
  - constructor. assumption.
Qed.

(** A runtime value cannot take a successful expression-to-expression step. *)
Lemma value_no_successful_step :
  forall B v active e' active',
    value v ->
    ~ step B (Config v active) (Config e' active').
Proof.
  intros B v active e' active' Hvalue Hstep.
  inversion Hstep; subst; inversion Hvalue.
Qed.

(** If a list consists of actively well-formed values, every member contains
    no hidden running download. *)
Lemma Forall_values_active_wf_no_run :
  forall values,
    Forall value values ->
    Forall active_wf values ->
    Forall no_run values.
Proof.
  intros values Hvalues. induction Hvalues; intros Hactive.
  - constructor.
  - inversion Hactive; subst. constructor.
    + eapply active_wf_value_no_run; eauto.
    + apply IHHvalues. exact H3.
Qed.

(** Extend [active_wf] to arbitrary transition endpoints. Only a successful
    expression target has an invariant to preserve; an error target is ignored
    by this one-step lemma and handled separately by bandwidth safety. *)
Definition active_wf_transition
    (source target : configuration) : Prop :=
  match source, target with
  | Config e _, Config e' _ => active_wf e -> active_wf e'
  | _, _ => True
  end.

(** Every successful reduction preserves active runtime well-formedness. This
    proof follows the operational rules and the corresponding appendix proof. *)
Lemma step_preserves_active_wf_general :
  forall B source target,
    step B source target ->
    active_wf_transition source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl in *.
  - intros Hactive. inversion Hactive; subst.
    apply no_run_implies_active_wf.
    apply subst0_preserves_no_run.
    + eapply active_wf_value_no_run; eauto.
    + assumption.
  - intros Hactive.
    inversion Hactive; subst.
    + exfalso. match goal with
      | Hnot : ~ value (ELambda _ _) |- _ => apply Hnot; constructor
      end.
    + apply no_run_implies_active_wf. apply subst0_preserves_no_run.
      * eapply active_wf_value_no_run; eauto.
      * match goal with Hlambda : no_run (ELambda _ _) |- _ =>
          inversion Hlambda; subst; assumption
        end.
  - intros Hactive. inversion Hactive; subst.
    apply no_run_implies_active_wf. assumption.
  - intros Hactive. inversion Hactive; subst.
    apply no_run_implies_active_wf. assumption.
  - intros Hactive. inversion Hactive; subst.
    apply ActiveTuple. eapply Forall_values_active_wf_no_run; eauto.
  - intros Hactive. constructor.
  - intros Hactive. constructor.
  - exact I.
  - intros Hactive. inversion Hactive; subst. constructor.
    + apply IHHstep. assumption.
    + assumption.
  - intros Hactive.
    assert (~ value function) as Hfunction_not_value.
    { intro Hvalue. eapply value_no_successful_step; eauto. }
    inversion Hactive; subst.
    + match goal with
      | Hfunction_active : active_wf function,
        Hargument_no_run : no_run argument |- _ =>
          pose proof (IHHstep Hfunction_active) as Hfunction'
      end.
      destruct (value_dec function') as [Hvalue' | Hnot_value'].
      * apply ActiveAppArgument.
        -- exact Hvalue'.
        -- eapply active_wf_value_no_run; eauto.
        -- apply no_run_implies_active_wf. assumption.
      * apply ActiveAppFunction; assumption.
    + contradiction.
  - intros Hactive.
    inversion Hactive; subst.
    + contradiction.
    + apply ActiveAppArgument.
      * assumption.
      * assumption.
      * apply IHHstep. assumption.
  - intros Hactive. inversion Hactive; subst. constructor.
    + apply IHHstep. assumption.
    + assumption.
    + assumption.
  - intros Hactive. inversion Hactive; subst. apply ActiveParallel.
    eapply Forall_replace_middle.
    + eassumption.
    + apply IHHstep. eapply Forall_middle. eassumption.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** Direct successful-step form of [active_wf] preservation. *)
Theorem step_preserves_active_wf :
  forall B e active e' active',
    step B (Config e active) (Config e' active') ->
    active_wf e ->
    active_wf e'.
Proof.
  intros B e active e' active' Hstep Hactive.
  pose proof
    (step_preserves_active_wf_general B _ _ Hstep) as Hpreserves.
  simpl in Hpreserves. apply Hpreserves. exact Hactive.
Qed.

(** Every successful state reachable from a source expression is actively well
    formed. The initial counter is arbitrary here; the later counter-agreement
    theorem specializes it to [0]. *)
Theorem reachable_source_active_wf :
  forall B source initial_active target target_active,
    source_expr source ->
    successful_steps B
      source initial_active target target_active ->
    active_wf target.
Proof.
  intros B source initial_active target target_active Hsource Hsteps.
  induction Hsteps.
  - apply no_run_implies_active_wf. apply source_no_run. exact Hsource.
  - eapply step_preserves_active_wf; eauto.
Qed.
