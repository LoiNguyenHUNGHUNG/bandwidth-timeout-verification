(** Scope and structural subtyping for polymorphic result and suspended types. *)
From Stdlib Require Import Arith Lia List.
From BandwidthTimeout Require Import Effects PolymorphicEffects PolymorphicSyntax.
Import ListNotations.
Local Open Scope nat_scope.

Lemma poly_ty_wf_rename : forall d T, poly_ty_wf d T ->
  forall d' rho, (forall i, i < d -> rho i < d') ->
  poly_ty_wf d' (poly_ty_rename rho T).
Proof.
  fix IH 2. intros d T HT d' rho Hr. destruct T; inversion HT; subst; simpl.
  - constructor.
  - constructor.
  - constructor; eauto using eff_scoped_rename.
  - constructor. clear HT.
    match goal with H : Forall _ l |- _ => revert H end.
    induction l; intros H; inversion H; subst; simpl; constructor; eauto.
  - constructor.
    + eapply IH; eauto. intros [|i] Hi; unfold eff_up_ren; try lia.
      specialize (Hr i ltac:(lia)); lia.
    + eapply eff_scoped_rename; eauto.
      intros [|i] Hi; unfold eff_up_ren; try lia.
      specialize (Hr i ltac:(lia)); lia.
Qed.

Lemma poly_ty_wf_subst : forall d T, poly_ty_wf d T ->
  forall d' sigma, (forall i, i < d -> eff_scoped d' (sigma i)) ->
  poly_ty_wf d' (poly_ty_subst sigma T).
Proof.
  fix IH 2. intros d T HT d' sigma Hs. destruct T; inversion HT; subst; simpl.
  - constructor.
  - constructor.
  - constructor; eauto using eff_scoped_subst.
  - constructor. clear HT.
    match goal with H : Forall _ l |- _ => revert H end.
    induction l; intros H; inversion H; subst; simpl; constructor; eauto.
  - constructor.
    + eapply IH; eauto. apply eff_up_scoped; assumption.
    + eapply eff_scoped_subst; eauto. apply eff_up_scoped; assumption.
Qed.

Inductive poly_subtype : nat -> poly_ty -> poly_ty -> Prop :=
| PSTUnit : forall d, poly_subtype d PTUnit PTUnit
| PSTNat : forall d, poly_subtype d PTNat PTNat
| PSTArrow : forall d A E B A' E' B',
    poly_subtype d A' A -> eff_le d E E' -> poly_subtype d B B' ->
    poly_subtype d (PTArrow A E B) (PTArrow A' E' B')
| PSTProduct : forall d Ts Us, Forall2 (poly_subtype d) Ts Us ->
    poly_subtype d (PTProduct Ts) (PTProduct Us)
| PSTForall : forall d T E U F,
    poly_subtype (S d) T U -> eff_le (S d) E F ->
    poly_subtype d (PTForall T E) (PTForall U F).

Lemma poly_subtype_refl : forall T d, poly_subtype d T T.
Proof.
  fix IH 1. intros T d. destruct T; constructor; auto using eff_le_refl.
  induction l; constructor; auto.
Qed.

Lemma poly_subtype_arrow_inv : forall d A E B A' E' B',
  poly_subtype d (PTArrow A E B) (PTArrow A' E' B') ->
  poly_subtype d A' A /\ eff_le d E E' /\ poly_subtype d B B'.
Proof. intros; inversion H; subst; auto. Qed.

Lemma poly_subtype_forall_inv : forall d T E U F,
  poly_subtype d (PTForall T E) (PTForall U F) ->
  poly_subtype (S d) T U /\ eff_le (S d) E F.
Proof. intros; inversion H; subst; auto. Qed.

Lemma poly_subtype_product_inv : forall d Ts Us,
  poly_subtype d (PTProduct Ts) (PTProduct Us) ->
  Forall2 (poly_subtype d) Ts Us.
Proof. intros; inversion H; subst; auto. Qed.

Lemma poly_subtype_subst : forall d T U, poly_subtype d T U ->
  forall d' sigma, (forall i, i < d -> eff_scoped d' (sigma i)) ->
  poly_subtype d' (poly_ty_subst sigma T) (poly_ty_subst sigma U).
Proof.
  fix IH 4. intros d T U H d' sigma Hs. destruct H; simpl.
  - constructor.
  - constructor.
  - constructor; eauto using eff_le_subst.
  - constructor. induction H; simpl; constructor; eauto.
  - constructor.
    + eapply IH; eauto. apply eff_up_scoped; assumption.
    + eapply eff_le_subst; eauto. apply eff_up_scoped; assumption.
Qed.

Lemma poly_subtype_rename : forall d T U, poly_subtype d T U ->
  forall d' rho, (forall i, i < d -> rho i < d') ->
  poly_subtype d' (poly_ty_rename rho T) (poly_ty_rename rho U).
Proof.
  intros d T U H d' rho Hr. rewrite <- !poly_ty_subst_vars.
  eapply poly_subtype_subst; eauto. intros; constructor; auto.
Qed.

Fixpoint poly_type_measure (T : poly_ty) : nat :=
  match T with
  | PTUnit | PTNat => 1
  | PTArrow A _ B => S (poly_type_measure A + poly_type_measure B)
  | PTProduct Ts => S (fold_right (fun T n => poly_type_measure T + n) 0 Ts)
  | PTForall T _ => S (poly_type_measure T)
  end.

Lemma poly_type_measure_member : forall Ts T,
  In T Ts -> poly_type_measure T < poly_type_measure (PTProduct Ts).
Proof.
  intros Ts; induction Ts as [|A Ts IH]; intros T Hin; simpl in *.
  - contradiction.
  - destruct Hin; subst; [lia | specialize (IH T H); simpl in IH; lia].
Qed.

Theorem poly_subtype_trans : forall middle d left right,
  poly_subtype d left middle -> poly_subtype d middle right ->
  poly_subtype d left right.
Proof.
  intro middle. pattern middle.
  apply (well_founded_induction_type
    (well_founded_ltof poly_ty poly_type_measure)).
  clear middle. intros middle IH d left right Hleft Hright.
  destruct middle; inversion Hleft; subst; inversion Hright; subst.
  - constructor.
  - constructor.
  - constructor.
    + eapply (IH middle1); try eassumption. unfold ltof; simpl; lia.
    + eapply eff_le_trans; eassumption.
    + eapply (IH middle2); try eassumption. unfold ltof; simpl; lia.
  - constructor.
    assert (HC : forall ms ls rs,
      Forall2 (poly_subtype d) ls ms -> Forall2 (poly_subtype d) ms rs ->
      (forall T, In T ms -> poly_type_measure T < poly_type_measure (PTProduct l)) ->
      Forall2 (poly_subtype d) ls rs).
    { intros ms ls rs HL. revert rs. induction HL; intros rs HR Hsmall;
        inversion HR; subst; constructor.
      - eapply (IH y); try eassumption. apply Hsmall; left; reflexivity.
      - eapply IHHL; eauto. intros; apply Hsmall; right; assumption. }
    eapply HC; try eassumption. intros; apply poly_type_measure_member; assumption.
  - constructor.
    + eapply (IH middle); try eassumption. unfold ltof; simpl; lia.
    + eapply eff_le_trans; eassumption.
Qed.

Corollary poly_subtype_subst0 : forall d T U F,
  poly_subtype (S d) T U -> eff_scoped d F ->
  poly_subtype d (poly_ty_subst0 F T) (poly_ty_subst0 F U).
Proof.
  intros d T U F H HF. apply poly_subtype_subst with (S d); auto.
  intros [|i] Hi; simpl; unfold eff_single; auto. constructor; lia.
Qed.

Corollary poly_ty_wf_subst0 : forall d T F,
  poly_ty_wf (S d) T -> eff_scoped d F -> poly_ty_wf d (poly_ty_subst0 F T).
Proof.
  intros d T F H HF. apply poly_ty_wf_subst with (S d); auto.
  intros [|i] Hi; simpl; unfold eff_single; auto. constructor; lia.
Qed.
