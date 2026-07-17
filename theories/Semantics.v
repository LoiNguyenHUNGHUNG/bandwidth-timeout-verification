(** Small-step operational semantics for the bandwidth-timeout calculus.

    A successful configuration pairs a runtime expression with the global
    number of active downloads. The distinguished error configuration records
    bandwidth under-provisioning. The transition relation is parameterized by
    the fixed global bandwidth budget [B]. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Bandwidth Syntax Substitution.

Import ListNotations.
Open Scope Q_scope.

(** Runtime configurations are either a current expression and active-download
    counter, or the terminal bandwidth-error state. *)
Inductive configuration : Type :=
| Config : expr -> nat -> configuration
| Error : configuration.

(** A running download is under-provisioned when at least one download is
    active and its fair share of [B] is below its required average rate. *)
Definition underprovisioned
    (B : Q) (active : nat) (size timeout : Q) : Prop :=
  (0 < active)%nat /\
  B / qnat active < download_rate size timeout.

(** [step B c c'] means that configuration [c] can take one small step to
    configuration [c'] under the fixed bandwidth budget [B]. Parallel children
    may step in any order, so this relation is intentionally nondeterministic. *)
Inductive step (B : Q) : configuration -> configuration -> Prop :=
| StepLetDone : forall bound body active,
    value bound ->
    step B
      (Config (ELet bound body) active)
      (Config (subst0 bound body) active)
| StepBeta : forall parameter_ty body argument active,
    value argument ->
    step B
      (Config (EApp (ELambda parameter_ty body) argument) active)
      (Config (subst0 argument body) active)
| StepIfZero : forall zero_branch nonzero_branch active,
    step B
      (Config (EIfZero (ENat 0) zero_branch nonzero_branch) active)
      (Config zero_branch active)
| StepIfNonzero : forall n zero_branch nonzero_branch active,
    (n <> 0)%nat ->
    step B
      (Config (EIfZero (ENat n) zero_branch nonzero_branch) active)
      (Config nonzero_branch active)
| StepParallelDone : forall branches active,
    Forall value branches ->
    step B
      (Config (EParallel branches) active)
      (Config (ETuple branches) active)
| StepDownloadStart : forall size timeout active,
    step B
      (Config (EDownload size timeout) active)
      (Config (ERunning size timeout) (S active))
| StepDownloadFinish : forall size timeout active,
    (0 < active)%nat ->
    step B
      (Config (ERunning size timeout) active)
      (Config EUnit (Nat.pred active))
| StepBandwidthError : forall size timeout active,
    underprovisioned B active size timeout ->
    step B
      (Config (ERunning size timeout) active)
      Error
| StepLet : forall bound bound' body active active',
    step B (Config bound active) (Config bound' active') ->
    step B
      (Config (ELet bound body) active)
      (Config (ELet bound' body) active')
| StepAppFunction : forall function function' argument active active',
    step B (Config function active) (Config function' active') ->
    step B
      (Config (EApp function argument) active)
      (Config (EApp function' argument) active')
| StepAppArgument : forall function argument argument' active active',
    value function ->
    step B (Config argument active) (Config argument' active') ->
    step B
      (Config (EApp function argument) active)
      (Config (EApp function argument') active')
| StepIfGuard : forall guard guard' zero_branch nonzero_branch active active',
    step B (Config guard active) (Config guard' active') ->
    step B
      (Config (EIfZero guard zero_branch nonzero_branch) active)
      (Config (EIfZero guard' zero_branch nonzero_branch) active')
| StepParallel : forall prefix branch branch' suffix active active',
    step B (Config branch active) (Config branch' active') ->
    step B
      (Config (EParallel (prefix ++ (branch :: suffix))) active)
      (Config (EParallel (prefix ++ (branch' :: suffix))) active')
| StepLetError : forall bound body active,
    step B (Config bound active) Error ->
    step B (Config (ELet bound body) active) Error
| StepAppFunctionError : forall function argument active,
    step B (Config function active) Error ->
    step B (Config (EApp function argument) active) Error
| StepAppArgumentError : forall function argument active,
    value function ->
    step B (Config argument active) Error ->
    step B (Config (EApp function argument) active) Error
| StepIfGuardError : forall guard zero_branch nonzero_branch active,
    step B (Config guard active) Error ->
    step B (Config (EIfZero guard zero_branch nonzero_branch) active) Error
| StepParallelError : forall prefix branch suffix active,
    step B (Config branch active) Error ->
    step B
      (Config (EParallel (prefix ++ (branch :: suffix))) active)
      Error.

(** Beta-reduction uses [subst0] to replace the lambda's nearest variable. *)
Example beta_identity_step :
  forall B active,
    step B
      (Config (EApp (ELambda TyNat (EVar 0)) (ENat 5)) active)
      (Config (ENat 5) active).
Proof.
  intros B active. apply StepBeta. constructor.
Qed.

(** Starting a download exposes the runtime-only form and increments the global
    active-download counter. *)
Example download_start_step :
  forall B size timeout active,
    step B
      (Config (EDownload size timeout) active)
      (Config (ERunning size timeout) (S active)).
Proof.
  intros B size timeout active. constructor.
Qed.

(** If every member of a list satisfies [P], the distinguished member between
    [prefix] and [suffix] satisfies [P]. This list lemma supports the arbitrary
    parallel-child rule. *)
Lemma Forall_middle :
  forall (A : Type) (P : A -> Prop) prefix element suffix,
    Forall P (prefix ++ (element :: suffix)) ->
    P element.
Proof.
  intros A P prefix. induction prefix as [|head prefix IH];
    intros element suffix Hforall; simpl in Hforall.
  - inversion Hforall. assumption.
  - inversion Hforall. eapply IH. eassumption.
Qed.

(** Replacing one distinguished list member by another member satisfying [P]
    preserves [Forall P]. *)
Lemma Forall_replace_middle :
  forall (A : Type) (P : A -> Prop) prefix old new suffix,
    Forall P (prefix ++ (old :: suffix)) ->
    P new ->
    Forall P (prefix ++ (new :: suffix)).
Proof.
  intros A P prefix. induction prefix as [|head prefix IH];
    intros old new suffix Hforall Hnew; simpl in *.
  - inversion Hforall. constructor; assumption.
  - inversion Hforall. constructor.
    + assumption.
    + eapply IH; eassumption.
Qed.

(** Extend runtime well-formedness to arbitrary transition endpoints. Only a
    successful expression-to-expression step has a proof obligation; an error
    target carries no expression whose grammar must be checked. *)
Definition runtime_wf_transition
    (source target : configuration) : Prop :=
  match source, target with
  | Config e _, Config e' _ => runtime_wf e -> runtime_wf e'
  | _, _ => True
  end.

(** Every transition preserves runtime grammar whenever it has a successful
    expression target. Error-producing rules satisfy the property trivially. *)
Lemma step_preserves_runtime_wf_general :
  forall B source target,
    step B source target ->
    runtime_wf_transition source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl in *.
  - intros Hwf. inversion Hwf; subst.
    eapply subst0_preserves_runtime_wf; eauto.
  - intros Hwf. inversion Hwf; subst.
    match goal with
    | Hlambda : runtime_wf (ELambda _ _) |- _ =>
        inversion Hlambda; subst
    end.
    eapply subst0_preserves_runtime_wf; eauto.
  - intros Hwf. inversion Hwf; subst. assumption.
  - intros Hwf. inversion Hwf; subst. assumption.
  - intros Hwf. inversion Hwf; subst. apply RtTuple; assumption.
  - intros Hwf. constructor.
  - intros Hwf. constructor.
  - exact I.
  - intros Hwf. inversion Hwf; subst. constructor.
    + apply IHHstep. assumption.
    + assumption.
  - intros Hwf. inversion Hwf; subst. constructor.
    + apply IHHstep. assumption.
    + assumption.
  - intros Hwf. inversion Hwf; subst. constructor.
    + assumption.
    + apply IHHstep. assumption.
  - intros Hwf. inversion Hwf; subst. constructor.
    + apply IHHstep. assumption.
    + assumption.
    + assumption.
  - intros Hwf. inversion Hwf; subst. constructor.
    eapply Forall_replace_middle.
    + eassumption.
    + apply IHHstep. eapply Forall_middle. eassumption.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** Direct successful-step form of runtime well-formedness preservation. *)
Theorem step_preserves_runtime_wf :
  forall B e active e' active',
    step B (Config e active) (Config e' active') ->
    runtime_wf e ->
    runtime_wf e'.
Proof.
  intros B e active e' active' Hstep Hwf.
  pose proof (step_preserves_runtime_wf_general B _ _ Hstep) as Hpreserves.
  simpl in Hpreserves. apply Hpreserves. exact Hwf.
Qed.

(** Extend the scoping invariant at a fixed context depth to arbitrary
    transition endpoints. As above, an error target has no expression. *)
Definition scoped_transition
    (depth : nat) (source target : configuration) : Prop :=
  match source, target with
  | Config e _, Config e' _ => scoped depth e -> scoped depth e'
  | _, _ => True
  end.

(** Every successful step preserves scoping at every surrounding context
    depth. Beta and let reduction use [subst0_preserves_scoped] to remove their
    binder without exposing a free variable. *)
Lemma step_preserves_scoped_general :
  forall B source target,
    step B source target ->
    forall depth, scoped_transition depth source target.
Proof.
  intros B source target Hstep. induction Hstep; intros depth; simpl in *.
  - intros Hscoped. inversion Hscoped; subst.
    eapply subst0_preserves_scoped; eauto.
  - intros Hscoped. inversion Hscoped; subst.
    match goal with
    | Hlambda : scoped _ (ELambda _ _) |- _ =>
        inversion Hlambda; subst
    end.
    eapply subst0_preserves_scoped; eauto.
  - intros Hscoped. inversion Hscoped; subst. assumption.
  - intros Hscoped. inversion Hscoped; subst. assumption.
  - intros Hscoped. inversion Hscoped; subst. constructor. assumption.
  - intros Hscoped. constructor.
  - intros Hscoped. constructor.
  - exact I.
  - intros Hscoped. inversion Hscoped; subst. constructor.
    + apply (IHHstep depth). assumption.
    + assumption.
  - intros Hscoped. inversion Hscoped; subst. constructor.
    + apply (IHHstep depth). assumption.
    + assumption.
  - intros Hscoped. inversion Hscoped; subst. constructor.
    + assumption.
    + apply (IHHstep depth). assumption.
  - intros Hscoped. inversion Hscoped; subst. constructor.
    + apply (IHHstep depth). assumption.
    + assumption.
    + assumption.
  - intros Hscoped. inversion Hscoped; subst. constructor.
    eapply Forall_replace_middle.
    + eassumption.
    + apply (IHHstep depth). eapply Forall_middle. eassumption.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** Direct successful-step form of scoping preservation. *)
Theorem step_preserves_scoped :
  forall B e active e' active' depth,
    step B (Config e active) (Config e' active') ->
    scoped depth e ->
    scoped depth e'.
Proof.
  intros B e active e' active' depth Hstep Hscoped.
  pose proof
    (step_preserves_scoped_general B _ _ Hstep depth) as Hpreserves.
  simpl in Hpreserves. apply Hpreserves. exact Hscoped.
Qed.

(** In particular, a successful step cannot introduce a free variable into a
    closed expression. *)
Corollary step_preserves_closed :
  forall B e active e' active',
    step B (Config e active) (Config e' active') ->
    closed e ->
    closed e'.
Proof.
  intros B e active e' active' Hstep Hclosed.
  unfold closed in *. eapply step_preserves_scoped; eauto.
Qed.
