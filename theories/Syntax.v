(** Source and runtime syntax for the bandwidth-timeout calculus.

    We use one runtime expression datatype and identify source expressions with
    an inductive predicate. The runtime-only [ERunning] constructor has no
    [source_expr] constructor, so it cannot occur anywhere in a source program.

    Term binders use de Bruijn indices. Index [0] denotes the variable bound by
    the nearest enclosing lambda or let. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Effects.

Import ListNotations.
Open Scope Q_scope.

(** Types carry latent effects on function arrows. Products are n-ary to match
    the result of structured parallel composition. *)
Inductive ty : Type :=
| TyUnit : ty
| TyNat : ty
| TyArrow : ty -> effect -> ty -> ty
| TyProduct : list ty -> ty.

(** Raw runtime expressions. [ERunning] is introduced only by reduction;
    [ETuple] represents both source tuple values and the result of a completed
    parallel composition. The [runtime_wf] predicate below enforces the paper's
    restriction that tuple components are values. *)
Inductive expr : Type :=
| EVar : nat -> expr
| EUnit : expr
| ENat : nat -> expr
| ELambda : ty -> expr -> expr
| ETuple : list expr -> expr
| EApp : expr -> expr -> expr
| ELet : expr -> expr -> expr
| EIfZero : expr -> expr -> expr -> expr
| EDownload : Q -> Q -> expr
| ERunning : Q -> Q -> expr
| EParallel : list expr -> expr.

Definition runtime_expr : Type := expr.

(** Download declarations store size and timeout. Positivity is a static
    well-formedness condition rather than a proof field in the syntax. *)
Definition download_rate (size timeout : Q) : Q := size / timeout.

Definition download_parameters_wf (size timeout : Q) : Prop :=
  0 <= size /\ 0 < timeout.

(** Runtime values are a predicate over expressions. Lambda bodies may contain
    arbitrary runtime syntax; the later [ActiveWF] invariant will show that
    reachable values never hide a running download. *)
Inductive value : expr -> Prop :=
| VUnit : value EUnit
| VNat : forall n, value (ENat n)
| VLambda : forall parameter_ty body, value (ELambda parameter_ty body)
| VTuple : forall components,
    Forall value components ->
    value (ETuple components).

(** Well-formed runtime expressions follow the runtime grammar in the paper.
    In particular, tuple nodes contain values, while their lambda bodies and
    nested tuples must still be recursively well formed. *)
Inductive runtime_wf : expr -> Prop :=
| RtVar : forall index, runtime_wf (EVar index)
| RtUnit : runtime_wf EUnit
| RtNat : forall n, runtime_wf (ENat n)
| RtLambda : forall parameter_ty body,
    runtime_wf body ->
    runtime_wf (ELambda parameter_ty body)
| RtTuple : forall components,
    Forall value components ->
    Forall runtime_wf components ->
    runtime_wf (ETuple components)
| RtApp : forall function argument,
    runtime_wf function ->
    runtime_wf argument ->
    runtime_wf (EApp function argument)
| RtLet : forall bound body,
    runtime_wf bound ->
    runtime_wf body ->
    runtime_wf (ELet bound body)
| RtIfZero : forall guard zero_branch nonzero_branch,
    runtime_wf guard ->
    runtime_wf zero_branch ->
    runtime_wf nonzero_branch ->
    runtime_wf (EIfZero guard zero_branch nonzero_branch)
| RtDownload : forall size timeout,
    runtime_wf (EDownload size timeout)
| RtRunning : forall size timeout,
    runtime_wf (ERunning size timeout)
| RtParallel : forall branches,
    Forall runtime_wf branches ->
    runtime_wf (EParallel branches).

(** Source expressions are exactly runtime expressions with no [ERunning]
    constructor at any depth. In particular, lambda bodies and tuple
    components must themselves be source expressions. *)
Inductive source_expr : expr -> Prop :=
| SrcVar : forall index, source_expr (EVar index)
| SrcUnit : source_expr EUnit
| SrcNat : forall n, source_expr (ENat n)
| SrcLambda : forall parameter_ty body,
    source_expr body ->
    source_expr (ELambda parameter_ty body)
| SrcTuple : forall components,
    Forall value components ->
    Forall source_expr components ->
    source_expr (ETuple components)
| SrcApp : forall function argument,
    source_expr function ->
    source_expr argument ->
    source_expr (EApp function argument)
| SrcLet : forall bound body,
    source_expr bound ->
    source_expr body ->
    source_expr (ELet bound body)
| SrcIfZero : forall guard zero_branch nonzero_branch,
    source_expr guard ->
    source_expr zero_branch ->
    source_expr nonzero_branch ->
    source_expr (EIfZero guard zero_branch nonzero_branch)
| SrcDownload : forall size timeout,
    source_expr (EDownload size timeout)
| SrcParallel : forall branches,
    Forall source_expr branches ->
    source_expr (EParallel branches).

(** [scoped depth e] means that every free de Bruijn index in [e] is strictly
    below [depth]. Lambda and let bodies introduce one additional variable. *)
Inductive scoped : nat -> expr -> Prop :=
| ScVar : forall depth index,
    (index < depth)%nat ->
    scoped depth (EVar index)
| ScUnit : forall depth,
    scoped depth EUnit
| ScNat : forall depth n,
    scoped depth (ENat n)
| ScLambda : forall depth parameter_ty body,
    scoped (S depth) body ->
    scoped depth (ELambda parameter_ty body)
| ScTuple : forall depth components,
    Forall (scoped depth) components ->
    scoped depth (ETuple components)
| ScApp : forall depth function argument,
    scoped depth function ->
    scoped depth argument ->
    scoped depth (EApp function argument)
| ScLet : forall depth bound body,
    scoped depth bound ->
    scoped (S depth) body ->
    scoped depth (ELet bound body)
| ScIfZero : forall depth guard zero_branch nonzero_branch,
    scoped depth guard ->
    scoped depth zero_branch ->
    scoped depth nonzero_branch ->
    scoped depth (EIfZero guard zero_branch nonzero_branch)
| ScDownload : forall depth size timeout,
    scoped depth (EDownload size timeout)
| ScRunning : forall depth size timeout,
    scoped depth (ERunning size timeout)
| ScParallel : forall depth branches,
    Forall (scoped depth) branches ->
    scoped depth (EParallel branches).

Definition closed (e : expr) : Prop := scoped 0 e.

Definition closed_source (e : expr) : Prop :=
  source_expr e /\ closed e.

(** Type annotations and latent effects are well formed when all rates are
    nonnegative and all component types are recursively well formed. *)
Inductive ty_wf : ty -> Prop :=
| WfTyUnit : ty_wf TyUnit
| WfTyNat : ty_wf TyNat
| WfTyArrow : forall domain latent codomain,
    ty_wf domain ->
    effect_wf latent ->
    ty_wf codomain ->
    ty_wf (TyArrow domain latent codomain)
| WfTyProduct : forall components,
    Forall ty_wf components ->
    ty_wf (TyProduct components).

Lemma running_not_source :
  forall size timeout,
    ~ source_expr (ERunning size timeout).
Proof.
  intros size timeout Hsource. inversion Hsource.
Qed.

Lemma source_is_runtime :
  forall e,
    source_expr e -> runtime_wf e.
Proof.
  fix IH 2.
  intros e Hsource. destruct Hsource.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IH. assumption.
  - apply RtTuple.
    + assumption.
    + induction H0.
      * constructor.
      * constructor.
        -- apply IH. assumption.
        -- apply IHForall. inversion H. assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - constructor.
    induction H.
    + constructor.
    + constructor.
      * apply IH. assumption.
      * assumption.
Qed.

Lemma source_lambda_body :
  forall parameter_ty body,
    source_expr (ELambda parameter_ty body) ->
    source_expr body.
Proof.
  intros parameter_ty body Hsource. inversion Hsource. assumption.
Qed.

Lemma source_tuple_components :
  forall components,
    source_expr (ETuple components) ->
    Forall source_expr components.
Proof.
  intros components Hsource. inversion Hsource. assumption.
Qed.

Lemma source_tuple_values :
  forall components,
    source_expr (ETuple components) ->
    Forall value components.
Proof.
  intros components Hsource. inversion Hsource. assumption.
Qed.

Lemma source_parallel_branches :
  forall branches,
    source_expr (EParallel branches) ->
    Forall source_expr branches.
Proof.
  intros branches Hsource. inversion Hsource. assumption.
Qed.

Lemma closed_variable_impossible :
  forall index,
    ~ closed (EVar index).
Proof.
  intros index Hclosed. unfold closed in Hclosed.
  inversion Hclosed. lia.
Qed.

Lemma closed_source_is_source :
  forall e,
    closed_source e -> source_expr e.
Proof.
  intros e [Hsource _]. exact Hsource.
Qed.

Lemma closed_source_is_closed :
  forall e,
    closed_source e -> closed e.
Proof.
  intros e [_ Hclosed]. exact Hclosed.
Qed.
