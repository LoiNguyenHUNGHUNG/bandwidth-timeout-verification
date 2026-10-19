(** Explicit effect polymorphism.  Term and effect binders use independent
    de Bruijn indices.  In particular, crossing an effect abstraction shifts
    the free effect variables of a substituted term, preventing capture. *)
From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Syntax Substitution
  PolymorphicEffects.
Import ListNotations.
Open Scope nat_scope.

Inductive poly_ty : Type :=
| PTUnit | PTNat
| PTArrow : poly_ty -> open_effect -> poly_ty -> poly_ty
| PTProduct : list poly_ty -> poly_ty
| PTForall : poly_ty -> open_effect -> poly_ty.

Definition eff_up_ren (xi : nat -> nat) : nat -> nat :=
  fun i => match i with 0 => 0 | S j => S (xi j) end.
Definition eff_up_subst (sigma : nat -> open_effect) : nat -> open_effect :=
  fun i => match i with 0 => EffVar 0
               | S j => eff_rename S (sigma j) end.

Fixpoint poly_ty_rename (xi : nat -> nat) (T : poly_ty) : poly_ty :=
  match T with
  | PTUnit => PTUnit | PTNat => PTNat
  | PTArrow A E B => PTArrow (poly_ty_rename xi A) (eff_rename xi E)
                             (poly_ty_rename xi B)
  | PTProduct Ts => PTProduct (map (poly_ty_rename xi) Ts)
  | PTForall T E => PTForall (poly_ty_rename (eff_up_ren xi) T)
                              (eff_rename (eff_up_ren xi) E)
  end.
Fixpoint poly_ty_subst (sigma : nat -> open_effect) (T : poly_ty) : poly_ty :=
  match T with
  | PTUnit => PTUnit | PTNat => PTNat
  | PTArrow A E B => PTArrow (poly_ty_subst sigma A) (eff_subst sigma E)
                             (poly_ty_subst sigma B)
  | PTProduct Ts => PTProduct (map (poly_ty_subst sigma) Ts)
  | PTForall T E => PTForall (poly_ty_subst (eff_up_subst sigma) T)
                              (eff_subst (eff_up_subst sigma) E)
  end.
Definition eff_single (F : open_effect) : nat -> open_effect :=
  fun i => match i with 0 => F | S j => EffVar j end.
Definition poly_ty_subst0 F T := poly_ty_subst (eff_single F) T.

Inductive poly_expr : Type :=
| PEVar : nat -> poly_expr
| PEUnit : poly_expr
| PENat : nat -> poly_expr
| PELambda : poly_ty -> poly_expr -> poly_expr
| PETuple : list poly_expr -> poly_expr
| PEApp : poly_expr -> poly_expr -> poly_expr
| PELet : poly_expr -> poly_expr -> poly_expr
| PEIfZero : poly_expr -> poly_expr -> poly_expr -> poly_expr
| PEDownload : nonnegative_rational -> positive_rational -> poly_expr
| PERunning : nonnegative_rational -> positive_rational -> poly_expr
| PEParallel : list poly_expr -> poly_expr
| PEAbsEff : poly_expr -> poly_expr
| PEAppEff : poly_expr -> open_effect -> poly_expr.

Fixpoint poly_effect_rename (xi : nat -> nat) (e : poly_expr) : poly_expr :=
  match e with
  | PEVar i => PEVar i | PEUnit => PEUnit | PENat n => PENat n
  | PELambda T e => PELambda (poly_ty_rename xi T) (poly_effect_rename xi e)
  | PETuple es => PETuple (map (poly_effect_rename xi) es)
  | PEApp e f => PEApp (poly_effect_rename xi e) (poly_effect_rename xi f)
  | PELet e f => PELet (poly_effect_rename xi e) (poly_effect_rename xi f)
  | PEIfZero e f g => PEIfZero (poly_effect_rename xi e)
      (poly_effect_rename xi f) (poly_effect_rename xi g)
  | PEDownload s t => PEDownload s t | PERunning s t => PERunning s t
  | PEParallel es => PEParallel (map (poly_effect_rename xi) es)
  | PEAbsEff e => PEAbsEff (poly_effect_rename (eff_up_ren xi) e)
  | PEAppEff e F => PEAppEff (poly_effect_rename xi e) (eff_rename xi F)
  end.
Fixpoint poly_effect_subst (sigma : nat -> open_effect) (e : poly_expr)
    : poly_expr :=
  match e with
  | PEVar i => PEVar i | PEUnit => PEUnit | PENat n => PENat n
  | PELambda T e => PELambda (poly_ty_subst sigma T) (poly_effect_subst sigma e)
  | PETuple es => PETuple (map (poly_effect_subst sigma) es)
  | PEApp e f => PEApp (poly_effect_subst sigma e) (poly_effect_subst sigma f)
  | PELet e f => PELet (poly_effect_subst sigma e) (poly_effect_subst sigma f)
  | PEIfZero e f g => PEIfZero (poly_effect_subst sigma e)
      (poly_effect_subst sigma f) (poly_effect_subst sigma g)
  | PEDownload s t => PEDownload s t | PERunning s t => PERunning s t
  | PEParallel es => PEParallel (map (poly_effect_subst sigma) es)
  | PEAbsEff e => PEAbsEff (poly_effect_subst (eff_up_subst sigma) e)
  | PEAppEff e F => PEAppEff (poly_effect_subst sigma e) (eff_subst sigma F)
  end.
Definition poly_effect_subst0 F e := poly_effect_subst (eff_single F) e.

Fixpoint poly_rename (xi : nat -> nat) (e : poly_expr) : poly_expr :=
  match e with
  | PEVar i => PEVar (xi i) | PEUnit => PEUnit | PENat n => PENat n
  | PELambda T e => PELambda T (poly_rename (up_ren xi) e)
  | PETuple es => PETuple (map (poly_rename xi) es)
  | PEApp e f => PEApp (poly_rename xi e) (poly_rename xi f)
  | PELet e f => PELet (poly_rename xi e) (poly_rename (up_ren xi) f)
  | PEIfZero e f g => PEIfZero (poly_rename xi e)
      (poly_rename xi f) (poly_rename xi g)
  | PEDownload s t => PEDownload s t | PERunning s t => PERunning s t
  | PEParallel es => PEParallel (map (poly_rename xi) es)
  | PEAbsEff e => PEAbsEff (poly_rename xi e)
  | PEAppEff e F => PEAppEff (poly_rename xi e) F
  end.
Definition poly_up_subst (sigma : nat -> poly_expr) : nat -> poly_expr :=
  fun i => match i with 0 => PEVar 0 | S j => poly_rename S (sigma j) end.
Fixpoint poly_subst (sigma : nat -> poly_expr) (e : poly_expr) : poly_expr :=
  match e with
  | PEVar i => sigma i | PEUnit => PEUnit | PENat n => PENat n
  | PELambda T e => PELambda T (poly_subst (poly_up_subst sigma) e)
  | PETuple es => PETuple (map (poly_subst sigma) es)
  | PEApp e f => PEApp (poly_subst sigma e) (poly_subst sigma f)
  | PELet e f => PELet (poly_subst sigma e) (poly_subst (poly_up_subst sigma) f)
  | PEIfZero e f g => PEIfZero (poly_subst sigma e)
      (poly_subst sigma f) (poly_subst sigma g)
  | PEDownload s t => PEDownload s t | PERunning s t => PERunning s t
  | PEParallel es => PEParallel (map (poly_subst sigma) es)
  | PEAbsEff e => PEAbsEff
      (poly_subst (fun i => poly_effect_rename S (sigma i)) e)
  | PEAppEff e F => PEAppEff (poly_subst sigma e) F
  end.
Definition poly_subst0 v e :=
  poly_subst (fun i => match i with 0 => v | S j => PEVar j end) e.

Inductive poly_value : poly_expr -> Prop :=
| PVUnit : poly_value PEUnit
| PVNat : forall n, poly_value (PENat n)
| PVLambda : forall T e, poly_value (PELambda T e)
| PVTuple : forall es, Forall poly_value es -> poly_value (PETuple es)
| PVAbsEff : forall e, poly_value (PEAbsEff e).

Inductive poly_ty_wf : nat -> poly_ty -> Prop :=
| PTWUnit : forall d, poly_ty_wf d PTUnit
| PTWNat : forall d, poly_ty_wf d PTNat
| PTWArrow : forall d A E B, poly_ty_wf d A -> eff_scoped d E ->
    poly_ty_wf d B -> poly_ty_wf d (PTArrow A E B)
| PTWProduct : forall d Ts, Forall (poly_ty_wf d) Ts ->
    poly_ty_wf d (PTProduct Ts)
| PTWForall : forall d T E, poly_ty_wf (S d) T -> eff_scoped (S d) E ->
    poly_ty_wf d (PTForall T E).

Inductive poly_source : poly_expr -> Prop :=
| PSVar : forall i, poly_source (PEVar i)
| PSUnit : poly_source PEUnit
| PSNat : forall n, poly_source (PENat n)
| PSLambda : forall T e, poly_source e -> poly_source (PELambda T e)
| PSTuple : forall es, Forall poly_value es -> Forall poly_source es ->
    poly_source (PETuple es)
| PSApp : forall e f, poly_source e -> poly_source f -> poly_source (PEApp e f)
| PSLet : forall e f, poly_source e -> poly_source f -> poly_source (PELet e f)
| PSIfZero : forall e f g, poly_source e -> poly_source f -> poly_source g ->
    poly_source (PEIfZero e f g)
| PSDownload : forall s t, poly_source (PEDownload s t)
| PSParallel : forall es, Forall poly_source es -> poly_source (PEParallel es)
| PSAbsEff : forall e, poly_source e -> poly_source (PEAbsEff e)
| PSAppEff : forall e F, poly_source e -> poly_source (PEAppEff e F).

(** Both variable namespaces are checked.  The depth of the term context
    remains unchanged under an effect abstraction. *)
Inductive poly_scoped : nat -> nat -> poly_expr -> Prop :=
| PCVar : forall d g i, i < g -> poly_scoped d g (PEVar i)
| PCUnit : forall d g, poly_scoped d g PEUnit
| PCNat : forall d g n, poly_scoped d g (PENat n)
| PCLambda : forall d g T e, poly_ty_wf d T -> poly_scoped d (S g) e ->
    poly_scoped d g (PELambda T e)
| PCTuple : forall d g es, Forall (poly_scoped d g) es ->
    poly_scoped d g (PETuple es)
| PCApp : forall d g e f, poly_scoped d g e -> poly_scoped d g f ->
    poly_scoped d g (PEApp e f)
| PCLet : forall d g e f, poly_scoped d g e -> poly_scoped d (S g) f ->
    poly_scoped d g (PELet e f)
| PCIfZero : forall d g e f h, poly_scoped d g e -> poly_scoped d g f ->
    poly_scoped d g h -> poly_scoped d g (PEIfZero e f h)
| PCDownload : forall d g s t, poly_scoped d g (PEDownload s t)
| PCRunning : forall d g s t, poly_scoped d g (PERunning s t)
| PCParallel : forall d g es, Forall (poly_scoped d g) es ->
    poly_scoped d g (PEParallel es)
| PCAbsEff : forall d g e, poly_scoped (S d) g e ->
    poly_scoped d g (PEAbsEff e)
| PCAppEff : forall d g e F, poly_scoped d g e -> eff_scoped d F ->
    poly_scoped d g (PEAppEff e F).
Definition poly_closed_source e := poly_source e /\ poly_scoped 0 0 e.

Example effect_substitution_avoids_capture :
  poly_effect_subst0 (EffVar 0)
    (PEAbsEff (PEAppEff (PEVar 0) (EffVar 1))) =
  PEAbsEff (PEAppEff (PEVar 0) (EffVar 1)).
Proof. reflexivity. Qed.
Example term_substitution_avoids_effect_capture :
  poly_subst0 (PEAppEff (PEVar 0) (EffVar 0)) (PEAbsEff (PEVar 0)) =
  PEAbsEff (PEAppEff (PEVar 0) (EffVar 1)).
Proof. reflexivity. Qed.

(** Algebra of capture-avoiding effect substitution.  All equalities are
    constructive; no functional-extensionality axiom is used. *)
Lemma poly_eff_rename_ext : forall E xi zeta,
  (forall i, xi i = zeta i) -> eff_rename xi E = eff_rename zeta E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.
Lemma poly_eff_subst_ext : forall E sigma tau,
  (forall i, sigma i = tau i) -> eff_subst sigma E = eff_subst tau E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.
Lemma poly_eff_rename_comp : forall E xi zeta,
  eff_rename xi (eff_rename zeta E) = eff_rename (fun i => xi (zeta i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.
Lemma poly_eff_subst_rename : forall E sigma xi,
  eff_subst sigma (eff_rename xi E) = eff_subst (fun i => sigma (xi i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.
Lemma poly_eff_rename_subst : forall E xi sigma,
  eff_rename xi (eff_subst sigma E) =
  eff_subst (fun i => eff_rename xi (sigma i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.
Lemma poly_eff_subst_comp : forall E sigma tau,
  eff_subst sigma (eff_subst tau E) =
  eff_subst (fun i => eff_subst sigma (tau i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.
Lemma poly_eff_subst_vars : forall E xi,
  eff_subst (fun i => EffVar (xi i)) E = eff_rename xi E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.
Lemma poly_eff_rename_id : forall E,
  eff_rename (fun i => i) E = E.
Proof. induction E; simpl; f_equal; auto. Qed.
Lemma poly_eff_subst_id : forall E,
  eff_subst EffVar E = E.
Proof. induction E; simpl; f_equal; auto. Qed.

Lemma poly_ty_rename_ext : forall T xi zeta,
  (forall i, xi i = zeta i) -> poly_ty_rename xi T = poly_ty_rename zeta T.
Proof.
  fix IH 1. intros T xi zeta H. destruct T; simpl; try reflexivity; f_equal.
  - apply IH; assumption.
  - apply poly_eff_rename_ext; assumption.
  - apply IH; assumption.
  - induction l; simpl; f_equal; auto.
  - apply IH. intros [|i]; simpl; auto.
  - apply poly_eff_rename_ext. intros [|i]; simpl; auto.
Qed.
Lemma poly_ty_subst_ext : forall T sigma tau,
  (forall i, sigma i = tau i) -> poly_ty_subst sigma T = poly_ty_subst tau T.
Proof.
  fix IH 1. intros T sigma tau H. destruct T; simpl; try reflexivity; f_equal.
  - apply IH; assumption.
  - apply poly_eff_subst_ext; assumption.
  - apply IH; assumption.
  - induction l; simpl; f_equal; auto.
  - apply IH. intros [|i]; simpl; auto. unfold eff_up_subst. rewrite H. reflexivity.
  - apply poly_eff_subst_ext. intros [|i]; simpl; auto. unfold eff_up_subst. rewrite H. reflexivity.
Qed.
Lemma poly_ty_rename_comp : forall T xi zeta,
  poly_ty_rename xi (poly_ty_rename zeta T) =
  poly_ty_rename (fun i => xi (zeta i)) T.
Proof.
  fix IH 1. intros T xi zeta. destruct T; simpl; try reflexivity; f_equal.
  - apply IH.
  - apply poly_eff_rename_comp.
  - apply IH.
  - induction l; simpl; f_equal; auto.
  - rewrite IH. apply poly_ty_rename_ext. intros [|i]; reflexivity.
  - rewrite poly_eff_rename_comp. apply poly_eff_rename_ext. intros [|i]; reflexivity.
Qed.
Lemma poly_ty_subst_rename : forall T sigma xi,
  poly_ty_subst sigma (poly_ty_rename xi T) =
  poly_ty_subst (fun i => sigma (xi i)) T.
Proof.
  fix IH 1. intros T sigma xi. destruct T; simpl; try reflexivity; f_equal.
  - apply IH.
  - apply poly_eff_subst_rename.
  - apply IH.
  - induction l; simpl; f_equal; auto.
  - rewrite IH. apply poly_ty_subst_ext. intros [|i]; reflexivity.
  - rewrite poly_eff_subst_rename. apply poly_eff_subst_ext. intros [|i]; reflexivity.
Qed.
Lemma poly_ty_rename_subst : forall T xi sigma,
  poly_ty_rename xi (poly_ty_subst sigma T) =
  poly_ty_subst (fun i => eff_rename xi (sigma i)) T.
Proof.
  fix IH 1. intros T xi sigma. destruct T; simpl; try reflexivity; f_equal.
  - apply IH.
  - apply poly_eff_rename_subst.
  - apply IH.
  - induction l; simpl; f_equal; auto.
  - rewrite IH. apply poly_ty_subst_ext. intros [|i]; simpl; auto.
    unfold eff_up_subst. rewrite !poly_eff_rename_comp.
    apply poly_eff_rename_ext. reflexivity.
  - rewrite poly_eff_rename_subst. apply poly_eff_subst_ext.
    intros [|i]; simpl; auto. unfold eff_up_subst.
    rewrite !poly_eff_rename_comp. apply poly_eff_rename_ext. reflexivity.
Qed.
Lemma poly_ty_subst_comp : forall T sigma tau,
  poly_ty_subst sigma (poly_ty_subst tau T) =
  poly_ty_subst (fun i => eff_subst sigma (tau i)) T.
Proof.
  fix IH 1. intros T sigma tau. destruct T; simpl; try reflexivity; f_equal.
  - apply IH.
  - apply poly_eff_subst_comp.
  - apply IH.
  - induction l; simpl; f_equal; auto.
  - rewrite IH. apply poly_ty_subst_ext. intros [|i]; simpl; auto.
    unfold eff_up_subst. rewrite poly_eff_subst_rename, poly_eff_rename_subst.
    apply poly_eff_subst_ext. reflexivity.
  - rewrite poly_eff_subst_comp. apply poly_eff_subst_ext.
    intros [|i]; simpl; auto. unfold eff_up_subst.
    rewrite poly_eff_subst_rename, poly_eff_rename_subst.
    apply poly_eff_subst_ext. reflexivity.
Qed.
Lemma poly_ty_subst_vars : forall T xi,
  poly_ty_subst (fun i => EffVar (xi i)) T = poly_ty_rename xi T.
Proof.
  fix IH 1. intros T xi. destruct T; simpl; try reflexivity; f_equal.
  - apply IH.
  - apply poly_eff_subst_vars.
  - apply IH.
  - induction l; simpl; f_equal; auto.
  - transitivity (poly_ty_subst (fun i => EffVar (eff_up_ren xi i)) T).
    + apply poly_ty_subst_ext. intros [|i]; reflexivity.
    + apply IH.
  - transitivity (eff_subst (fun i => EffVar (eff_up_ren xi i)) o).
    + apply poly_eff_subst_ext. intros [|i]; reflexivity.
    + apply poly_eff_subst_vars.
Qed.
Lemma poly_ty_rename_id : forall T, poly_ty_rename (fun i => i) T = T.
Proof.
  fix IH 1. intro T. destruct T; simpl; try reflexivity; f_equal.
  - apply IH.
  - apply poly_eff_rename_id.
  - apply IH.
  - induction l; simpl; f_equal; auto.
  - transitivity (poly_ty_rename (fun i => i) T).
    + apply poly_ty_rename_ext. intros [|i]; reflexivity.
    + apply IH.
  - transitivity (eff_rename (fun i => i) o).
    + apply poly_eff_rename_ext. intros [|i]; reflexivity.
    + apply poly_eff_rename_id.
Qed.
Lemma poly_ty_subst_id : forall T, poly_ty_subst EffVar T = T.
Proof.
  intro T. transitivity (poly_ty_subst (fun i => EffVar ((fun j => j) i)) T).
  - reflexivity.
  - rewrite poly_ty_subst_vars. apply poly_ty_rename_id.
Qed.
Lemma poly_ty_subst_shift : forall T sigma,
  poly_ty_subst (eff_up_subst sigma) (poly_ty_rename S T) =
  poly_ty_rename S (poly_ty_subst sigma T).
Proof.
  intros. rewrite poly_ty_subst_rename, poly_ty_rename_subst.
  apply poly_ty_subst_ext. reflexivity.
Qed.
Lemma poly_ty_subst_instantiate : forall T F sigma,
  poly_ty_subst sigma (poly_ty_subst0 F T) =
  poly_ty_subst0 (eff_subst sigma F) (poly_ty_subst (eff_up_subst sigma) T).
Proof.
  intros. unfold poly_ty_subst0. rewrite !poly_ty_subst_comp.
  apply poly_ty_subst_ext. intros [|i]; simpl; auto.
  unfold eff_single, eff_up_subst. rewrite poly_eff_subst_rename.
  apply eq_sym. apply poly_eff_subst_id.
Qed.
Lemma poly_effect_instantiate : forall E F sigma,
  eff_subst sigma (eff_subst (eff_single F) E) =
  eff_subst (eff_single (eff_subst sigma F)) (eff_subst (eff_up_subst sigma) E).
Proof.
  intros. rewrite !poly_eff_subst_comp. apply poly_eff_subst_ext.
  intros [|i]; simpl; auto. unfold eff_single, eff_up_subst.
  rewrite poly_eff_subst_rename. apply eq_sym. apply poly_eff_subst_id.
Qed.

Lemma poly_effect_subst_ext : forall e sigma tau,
  (forall i, sigma i = tau i) -> poly_effect_subst sigma e = poly_effect_subst tau e.
Proof.
  fix IH 1. intros e sigma tau H. destruct e; simpl; try reflexivity; f_equal;
    try (apply IH; assumption); try (apply poly_ty_subst_ext; assumption);
    try (apply poly_eff_subst_ext; assumption).
  - induction l; simpl; f_equal; auto.
  - induction l; simpl; f_equal; auto.
  - apply IH. intros [|i]; simpl; auto. unfold eff_up_subst. rewrite H. reflexivity.
Qed.
Lemma poly_effect_subst_vars : forall e xi,
  poly_effect_subst (fun i => EffVar (xi i)) e = poly_effect_rename xi e.
Proof.
  fix IH 1. intros e xi. destruct e; simpl; try reflexivity; f_equal;
    try apply IH; try apply poly_ty_subst_vars; try apply poly_eff_subst_vars.
  - induction l; simpl; f_equal; auto.
  - induction l; simpl; f_equal; auto.
  - transitivity (poly_effect_subst (fun i => EffVar (eff_up_ren xi i)) e).
    + apply poly_effect_subst_ext. intros [|i]; reflexivity.
    + apply IH.
Qed.
