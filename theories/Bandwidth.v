(** Bandwidth obligations and their interaction with effect coverage. *)

From Stdlib Require Import Arith Lia Lra List QArith ZArith.
From BandwidthTimeout Require Import Effects Normalization.

Import ListNotations.
Open Scope Q_scope.

Definition qnat (n : nat) : Q := inject_Z (Z.of_nat n).

Definition obligation_bandwidth (p : obligation) : Q :=
  rate p * qnat (concurrency p).

(** This pointwise form is the semantic bandwidth check. For a finite effect it
    is equivalent, under a nonnegative bandwidth assumption, to comparing [B]
    against the maximum [obligation_bandwidth] in the effect. *)
Definition bandwidth_safe (B : Q) (Phi : effect) : Prop :=
  forall p, In p Phi -> obligation_bandwidth p <= B.

Lemma qnat_nonnegative : forall n, 0 <= qnat n.
Proof.
  intro n. unfold qnat.
  change (inject_Z 0 <= inject_Z (Z.of_nat n)).
  rewrite <- Zle_Qle. apply Nat2Z.is_nonneg.
Qed.

Lemma qnat_mono :
  forall n m,
    (n <= m)%nat ->
    qnat n <= qnat m.
Proof.
  intros n m Hnm. unfold qnat.
  rewrite <- Zle_Qle. apply Nat2Z.inj_le. exact Hnm.
Qed.

Lemma obligation_bandwidth_mono :
  forall p q,
    obligation_wf p ->
    obligation_le p q ->
    obligation_bandwidth p <= obligation_bandwidth q.
Proof.
  intros p q Hp_wf [Hrate Hconc].
  unfold obligation_wf in Hp_wf.
  unfold obligation_bandwidth.
  assert (Hq_wf : 0 <= rate q).
  { eapply Qle_trans; eauto. }
  eapply Qle_trans.
  - apply Qmult_le_compat_r.
    + exact Hrate.
    + apply qnat_nonnegative.
  - rewrite (Qmult_comm (rate q) (qnat (concurrency p))).
    rewrite (Qmult_comm (rate q) (qnat (concurrency q))).
    apply Qmult_le_compat_r.
    + apply qnat_mono. exact Hconc.
    + exact Hq_wf.
Qed.

Lemma bandwidth_safe_antitone :
  forall B Phi Psi,
    effect_wf Phi ->
    Phi ≼ Psi ->
    bandwidth_safe B Psi ->
    bandwidth_safe B Phi.
Proof.
  intros B Phi Psi Hwf Hle Hsafe p Hp_in.
  unfold effect_wf in Hwf.
  apply Forall_forall with (x := p) in Hwf; [|exact Hp_in].
  destruct (Hle p Hp_in) as [q [Hq_in Hpq]].
  eapply Qle_trans.
  - eapply obligation_bandwidth_mono; eauto.
  - apply Hsafe. exact Hq_in.
Qed.

Lemma Forall_filter_preserve :
  forall (A : Type) (P : A -> Prop) (f : A -> bool) xs,
    Forall P xs ->
    Forall P (filter f xs).
Proof.
  intros A P f xs Hforall. induction Hforall; simpl.
  - constructor.
  - destruct (f x).
    + constructor; assumption.
    + assumption.
Qed.

Lemma insert_frontier_wf :
  forall p Phi,
    obligation_wf p ->
    effect_wf Phi ->
    effect_wf (insert_frontier p Phi).
Proof.
  intros p Phi Hp Hwf. unfold insert_frontier.
  destruct (existsb (obligation_leb p) Phi).
  - exact Hwf.
  - constructor.
    + exact Hp.
    + eapply Forall_filter_preserve. exact Hwf.
Qed.

Lemma normalize_wf :
  forall Phi,
    effect_wf Phi ->
    effect_wf (normalize Phi).
Proof.
  intros Phi Hwf. induction Hwf; simpl.
  - constructor.
  - apply insert_frontier_wf; assumption.
Qed.

Theorem normalize_bandwidth_safe_iff :
  forall B Phi,
    effect_wf Phi ->
    (bandwidth_safe B (normalize Phi) <-> bandwidth_safe B Phi).
Proof.
  intros B Phi Hwf. split; intro Hsafe.
  - eapply bandwidth_safe_antitone.
    + exact Hwf.
    + apply le_normalize.
    + exact Hsafe.
  - eapply bandwidth_safe_antitone.
    + apply normalize_wf. exact Hwf.
    + apply normalize_le.
    + exact Hsafe.
Qed.
