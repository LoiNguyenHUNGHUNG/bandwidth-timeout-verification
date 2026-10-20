(** Open quantitative effects for explicit effect polymorphism.

    Effect indices use a separate de Bruijn namespace.  Semantic entailment
    quantifies over every well-formed closing environment, including the empty
    literal.  It must never be checked at just one chosen instantiation. *)
From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Effects Normalization Bandwidth Typing.

Import ListNotations.
Local Open Scope nat_scope.

(** Finite literals include the empty effect, represented by [EffLit []]. *)
Inductive open_effect : Type :=
| EffLit : effect -> open_effect
| EffVar : nat -> open_effect
| EffJoin : open_effect -> open_effect -> open_effect
| EffPar : open_effect -> open_effect -> open_effect.

Inductive eff_scoped : nat -> open_effect -> Prop :=
| EffScopedLit : forall d Phi, effect_wf Phi -> eff_scoped d (EffLit Phi)
| EffScopedVar : forall d i, i < d -> eff_scoped d (EffVar i)
| EffScopedJoin : forall d E F,
    eff_scoped d E -> eff_scoped d F -> eff_scoped d (EffJoin E F)
| EffScopedPar : forall d E F,
    eff_scoped d E -> eff_scoped d F -> eff_scoped d (EffPar E F).

Fixpoint eff_rename (rho : nat -> nat) (E : open_effect) : open_effect :=
  match E with
  | EffLit Phi => EffLit Phi
  | EffVar i => EffVar (rho i)
  | EffJoin E F => EffJoin (eff_rename rho E) (eff_rename rho F)
  | EffPar E F => EffPar (eff_rename rho E) (eff_rename rho F)
  end.

Fixpoint eff_subst (sigma : nat -> open_effect) (E : open_effect) : open_effect :=
  match E with
  | EffLit Phi => EffLit Phi
  | EffVar i => sigma i
  | EffJoin E F => EffJoin (eff_subst sigma E) (eff_subst sigma F)
  | EffPar E F => EffPar (eff_subst sigma E) (eff_subst sigma F)
  end.

Definition eff_up (sigma : nat -> open_effect) : nat -> open_effect :=
  fun i => match i with 0 => EffVar 0 | S j => eff_rename S (sigma j) end.

Definition eff_subst0 (F E : open_effect) : open_effect :=
  eff_subst (fun i => match i with 0 => F | S j => EffVar j end) E.

Fixpoint eff_eval (eta : nat -> effect) (E : open_effect) : effect :=
  match E with
  | EffLit Phi => Phi
  | EffVar i => eta i
  | EffJoin E F => sequential_effect (eff_eval eta E) (eff_eval eta F)
  | EffPar E F => parallel_effect (eff_eval eta E) (eff_eval eta F)
  end.

Definition eff_environment (d : nat) (eta : nat -> effect) : Prop :=
  forall i, i < d -> effect_wf (eta i).

Definition eff_le (d : nat) (E F : open_effect) : Prop :=
  forall eta, eff_environment d eta ->
    effect_le (eff_eval eta E) (eff_eval eta F).

Definition eff_equiv (d : nat) (E F : open_effect) : Prop :=
  eff_le d E F /\ eff_le d F E.

Lemma eff_scoped_rename : forall d E, eff_scoped d E ->
  forall d' rho, (forall i, i < d -> rho i < d') ->
  eff_scoped d' (eff_rename rho E).
Proof.
  intros d E H; induction H; intros d' rho Hr; simpl;
    constructor; eauto.
Qed.

Lemma eff_scoped_subst : forall d E, eff_scoped d E ->
  forall d' sigma, (forall i, i < d -> eff_scoped d' (sigma i)) ->
  eff_scoped d' (eff_subst sigma E).
Proof.
  intros d E H; induction H; intros d' sigma Hs; simpl;
    eauto using eff_scoped.
Qed.

Lemma eff_up_scoped : forall d d' sigma,
  (forall i, i < d -> eff_scoped d' (sigma i)) ->
  forall i, i < S d -> eff_scoped (S d') (eff_up sigma i).
Proof.
  intros d d' sigma Hs [|i] Hi; simpl; unfold eff_up.
  - constructor; lia.
  - apply eff_scoped_rename with d'.
    + apply Hs; lia.
    + intros; lia.
Qed.

Lemma eff_subst0_scoped : forall d E F,
  eff_scoped (S d) E -> eff_scoped d F -> eff_scoped d (eff_subst0 F E).
Proof.
  intros d E F HE HF. apply eff_scoped_subst with (S d); auto.
  intros [|i] Hi; simpl; auto. constructor; lia.
Qed.

Lemma eff_eval_wf : forall d E, eff_scoped d E ->
  forall eta, eff_environment d eta -> effect_wf (eff_eval eta E).
Proof.
  intros d E H; induction H; intros eta Heta; simpl; auto.
  - unfold sequential_effect. apply normalize_wf, effect_wf_join; auto.
  - unfold parallel_effect. apply normalize_wf, effect_wf_parallel; auto.
Qed.

Lemma eff_rename_id : forall E, eff_rename (fun i => i) E = E.
Proof. induction E; simpl; f_equal; auto. Qed.

Lemma eff_subst_id : forall E, eff_subst EffVar E = E.
Proof. induction E; simpl; f_equal; auto. Qed.

Lemma eff_rename_comp : forall E rho rho',
  eff_rename rho' (eff_rename rho E) = eff_rename (fun i => rho' (rho i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_subst_comp : forall E sigma sigma',
  eff_subst sigma' (eff_subst sigma E) =
  eff_subst (fun i => eff_subst sigma' (sigma i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_subst_ext : forall E sigma sigma',
  (forall i, sigma i = sigma' i) -> eff_subst sigma E = eff_subst sigma' E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_eval_ext : forall E eta eta',
  (forall i, eta i = eta' i) -> eff_eval eta E = eff_eval eta' E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_eval_subst : forall E sigma eta,
  eff_eval eta (eff_subst sigma E) =
  eff_eval (fun i => eff_eval eta (sigma i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_eval_rename : forall E rho eta,
  eff_eval eta (eff_rename rho E) = eff_eval (fun i => eta (rho i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_subst_rename : forall E rho sigma,
  eff_subst sigma (eff_rename rho E) = eff_subst (fun i => sigma (rho i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_rename_subst : forall E rho sigma,
  eff_rename rho (eff_subst sigma E) =
  eff_subst (fun i => eff_rename rho (sigma i)) E.
Proof. induction E; intros; simpl; f_equal; auto. Qed.

Lemma eff_le_refl : forall d E, eff_le d E E.
Proof. intros d E eta Heta; apply effect_le_refl. Qed.

Lemma eff_le_trans : forall d E F G,
  eff_le d E F -> eff_le d F G -> eff_le d E G.
Proof. intros d E F G H1 H2 eta Heta; eapply effect_le_trans; eauto. Qed.

Lemma eff_le_empty : forall d E, eff_le d (EffLit []) E.
Proof. intros d E eta Heta; apply empty_effect_le. Qed.

Lemma eff_le_subst : forall d d' E F sigma,
  eff_le d E F ->
  (forall i, i < d -> eff_scoped d' (sigma i)) ->
  eff_le d' (eff_subst sigma E) (eff_subst sigma F).
Proof.
  intros d d' E F sigma H Hs eta Heta. rewrite !eff_eval_subst.
  apply H. intros i Hi. eapply eff_eval_wf; eauto.
Qed.

Lemma eff_join_mono : forall d E E' F F',
  eff_le d E E' -> eff_le d F F' ->
  eff_le d (EffJoin E F) (EffJoin E' F').
Proof. intros d E E' F F' H1 H2 eta Heta; simpl;
  apply sequential_effect_mono; auto. Qed.

Lemma eff_par_mono : forall d E E' F F',
  eff_le d E E' -> eff_le d F F' ->
  eff_le d (EffPar E F) (EffPar E' F').
Proof. intros d E E' F F' H1 H2 eta Heta; simpl;
  apply parallel_effect_mono; auto. Qed.

Lemma eff_le_join_l : forall d E F, eff_le d E (EffJoin E F).
Proof. intros d E F eta Heta; simpl; unfold sequential_effect.
  eapply effect_le_trans; [apply effect_le_join_l | apply le_normalize]. Qed.

Lemma eff_le_join_r : forall d E F, eff_le d F (EffJoin E F).
Proof. intros d E F eta Heta; simpl; unfold sequential_effect.
  eapply effect_le_trans; [apply effect_le_join_r | apply le_normalize]. Qed.

(** Local normalization never reassociates a symbolic tree. *)
Definition eff_join_node (E F : open_effect) : open_effect :=
  match E, F with
  | EffLit [], _ => F
  | _, EffLit [] => E
  | EffLit Phi, EffLit Psi => EffLit (sequential_effect Phi Psi)
  | _, _ => EffJoin E F
  end.

Definition eff_par_node (E F : open_effect) : open_effect :=
  match E, F with
  | EffLit [], _ => F
  | _, EffLit [] => E
  | EffLit Phi, EffLit Psi => EffLit (parallel_effect Phi Psi)
  | _, _ => EffPar E F
  end.

Fixpoint eff_norm (E : open_effect) : open_effect :=
  match E with
  | EffLit Phi => EffLit (normalize Phi)
  | EffVar i => EffVar i
  | EffJoin E F => eff_join_node (eff_norm E) (eff_norm F)
  | EffPar E F => eff_par_node (eff_norm E) (eff_norm F)
  end.

Lemma eff_join_node_scoped : forall d E F,
  eff_scoped d E -> eff_scoped d F -> eff_scoped d (eff_join_node E F).
Proof.
  intros d E F HE HF. destruct E, F; simpl; try (constructor; assumption).
  all: try destruct e; try destruct e0; simpl; try assumption;
    try (constructor; assumption).
  constructor. inversion HE; inversion HF; subst.
  unfold sequential_effect. apply normalize_wf, effect_wf_join; assumption.
Qed.

Lemma eff_par_node_scoped : forall d E F,
  eff_scoped d E -> eff_scoped d F -> eff_scoped d (eff_par_node E F).
Proof.
  intros d E F HE HF. destruct E, F; simpl; try (constructor; assumption).
  all: try destruct e; try destruct e0; simpl; try assumption;
    try (constructor; assumption).
  constructor. inversion HE; inversion HF; subst.
  unfold parallel_effect. apply normalize_wf, effect_wf_parallel; assumption.
Qed.

Lemma eff_norm_scoped : forall d E, eff_scoped d E -> eff_scoped d (eff_norm E).
Proof.
  intros d E H; induction H; simpl; eauto using eff_join_node_scoped,
    eff_par_node_scoped, eff_scoped.
  constructor. apply normalize_wf; assumption.
Qed.

Lemma sequential_empty_l : forall Phi, sequential_effect [] Phi ≈ Phi.
Proof. intros; apply normalize_coverage_equiv. Qed.

Lemma sequential_empty_r : forall Phi, sequential_effect Phi [] ≈ Phi.
Proof. intros; unfold sequential_effect, join; rewrite app_nil_r;
  apply normalize_coverage_equiv. Qed.

Lemma parallel_empty_l : forall Phi, parallel_effect [] Phi ≈ Phi.
Proof.
  intro Phi. unfold parallel_effect, parallel, shift_effect; simpl.
  replace (map (shift 0) Phi) with Phi.
  - apply normalize_coverage_equiv.
  - symmetry. induction Phi as [|[r n] Phi IH]; simpl; auto.
    rewrite IH. unfold shift; simpl. rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma parallel_empty_r : forall Phi, parallel_effect Phi [] ≈ Phi.
Proof.
  intro Phi. unfold parallel_effect, parallel, shift_effect; simpl.
  unfold join. rewrite app_nil_r. replace (map (shift 0) Phi) with Phi.
  - apply normalize_coverage_equiv.
  - symmetry. induction Phi as [|[r n] Phi IH]; simpl; auto.
    rewrite IH. unfold shift; simpl. rewrite Nat.add_0_r; reflexivity.
Qed.

Lemma eff_join_node_eval : forall E F eta,
  eff_eval eta (eff_join_node E F) ≈
    sequential_effect (eff_eval eta E) (eff_eval eta F).
Proof.
  intros E F eta. destruct E, F; simpl; try apply effect_equiv_refl;
    try destruct e; try destruct e0; simpl; try apply effect_equiv_refl;
    apply effect_equiv_sym; auto using sequential_empty_l, sequential_empty_r.
Qed.

Lemma eff_par_node_eval : forall E F eta,
  eff_eval eta (eff_par_node E F) ≈
    parallel_effect (eff_eval eta E) (eff_eval eta F).
Proof.
  intros E F eta. destruct E, F; simpl; try apply effect_equiv_refl;
    try destruct e; try destruct e0; simpl; try apply effect_equiv_refl;
    apply effect_equiv_sym; auto using parallel_empty_l, parallel_empty_r.
Qed.

Theorem eff_norm_eval : forall E eta,
  eff_eval eta (eff_norm E) ≈ eff_eval eta E.
Proof.
  induction E; intro eta; simpl.
  - apply normalize_coverage_equiv.
  - apply effect_equiv_refl.
  - eapply effect_equiv_trans; [apply eff_join_node_eval |].
    apply sequential_effect_respects_equiv; auto.
  - eapply effect_equiv_trans; [apply eff_par_node_eval |].
    apply parallel_effect_respects_equiv; auto.
Qed.

Theorem eff_norm_equiv : forall d E, eff_equiv d (eff_norm E) E.
Proof. intros d E; split; intros eta Heta; apply eff_norm_eval. Qed.
