(** Pair-set effects before Pareto normalization.

    Lists are used as the concrete carrier, but [covers] is the semantic
    interface. Consequently, list order and duplicate obligations are
    intentionally unobservable to the metatheory. *)

From Stdlib Require Import Arith Lia List QArith.

Import ListNotations.
Open Scope Q_scope.

Record obligation : Type := Obligation {
  rate : Q;
  concurrency : nat
}.

Definition effect : Type := list obligation.

(** Coordinatewise ordering on obligations. *)
Definition obligation_le (p q : obligation) : Prop :=
  rate p <= rate q /\ (concurrency p <= concurrency q)%nat.

(** [Phi] covers [p] when some member of [Phi] is at least as demanding as
    [p] in both coordinates. *)
Definition covers (Phi : effect) (p : obligation) : Prop :=
  exists q, In q Phi /\ obligation_le p q.

(** Effect ordering is pointwise coverage. *)
Definition effect_le (Phi Psi : effect) : Prop :=
  forall p, In p Phi -> covers Psi p.

Notation "Phi ≼ Psi" := (effect_le Phi Psi) (at level 70).

Lemma obligation_le_refl : forall p, obligation_le p p.
Proof.
  intros p. split; [apply Qle_refl | apply Nat.le_refl].
Qed.

Lemma obligation_le_trans :
  forall p q r,
    obligation_le p q -> obligation_le q r -> obligation_le p r.
Proof.
  intros p q r [Hrate_pq Hconc_pq] [Hrate_qr Hconc_qr].
  split.
  - eapply Qle_trans; eauto.
  - eapply Nat.le_trans; eauto.
Qed.

Lemma covers_member :
  forall Phi p, In p Phi -> covers Phi p.
Proof.
  intros Phi p Hin. exists p. split; [assumption | apply obligation_le_refl].
Qed.

Lemma covers_weaken_obligation :
  forall Phi p q,
    obligation_le p q -> covers Phi q -> covers Phi p.
Proof.
  intros Phi p q Hpq [r [Hin Hqr]].
  exists r. split; [assumption | eapply obligation_le_trans; eauto].
Qed.

Lemma effect_le_refl : forall Phi, Phi ≼ Phi.
Proof.
  intros Phi p Hin. apply covers_member. assumption.
Qed.

Lemma effect_le_trans :
  forall Phi Psi Xi,
    Phi ≼ Psi -> Psi ≼ Xi -> Phi ≼ Xi.
Proof.
  intros Phi Psi Xi HPhiPsi HPsiXi p Hin.
  destruct (HPhiPsi p Hin) as [q [Hq_in Hpq]].
  eapply covers_weaken_obligation; [exact Hpq |].
  apply HPsiXi. exact Hq_in.
Qed.

Lemma empty_effect_le : forall Phi, [] ≼ Phi.
Proof.
  intros Phi p Hin. inversion Hin.
Qed.

(** Sequential composition is raw union. Pareto normalization will later be
    wrapped around this operation and proved coverage-equivalent. *)
Definition join (Phi Psi : effect) : effect := Phi ++ Psi.

Lemma effect_le_join_l : forall Phi Psi, Phi ≼ join Phi Psi.
Proof.
  intros Phi Psi p Hin. apply covers_member. apply in_or_app. left. exact Hin.
Qed.

Lemma effect_le_join_r : forall Phi Psi, Psi ≼ join Phi Psi.
Proof.
  intros Phi Psi p Hin. apply covers_member. apply in_or_app. right. exact Hin.
Qed.

Lemma join_mono :
  forall Phi1 Phi2 Psi1 Psi2,
    Phi1 ≼ Psi1 ->
    Phi2 ≼ Psi2 ->
    join Phi1 Phi2 ≼ join Psi1 Psi2.
Proof.
  intros Phi1 Phi2 Psi1 Psi2 H1 H2 p Hin.
  apply in_app_or in Hin. destruct Hin as [Hin | Hin].
  - destruct (H1 p Hin) as [q [Hqin Hle]].
    exists q. split; [apply in_or_app; left; exact Hqin | exact Hle].
  - destruct (H2 p Hin) as [q [Hqin Hle]].
    exists q. split; [apply in_or_app; right; exact Hqin | exact Hle].
Qed.

(** Maximum possible concurrency recorded in an effect. *)
Fixpoint max_concurrency (Phi : effect) : nat :=
  match Phi with
  | [] => 0
  | p :: Phi' => Nat.max (concurrency p) (max_concurrency Phi')
  end.

Lemma concurrency_le_max :
  forall Phi p,
    In p Phi ->
    (concurrency p <= max_concurrency Phi)%nat.
Proof.
  induction Phi as [|q Phi IH]; intros p Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Nat.le_max_l.
    + eapply Nat.le_trans; [apply IH; exact Hin | apply Nat.le_max_r].
Qed.

Lemma max_concurrency_least :
  forall Phi n,
    (forall p, In p Phi -> (concurrency p <= n)%nat) ->
    (max_concurrency Phi <= n)%nat.
Proof.
  induction Phi as [|p Phi IH]; intros n Hbound; simpl.
  - lia.
  - apply Nat.max_lub.
    + apply Hbound. left. reflexivity.
    + apply IH. intros q Hq. apply Hbound. right. exact Hq.
Qed.

Lemma max_concurrency_mono :
  forall Phi Psi,
    Phi ≼ Psi ->
    (max_concurrency Phi <= max_concurrency Psi)%nat.
Proof.
  intros Phi Psi Hle.
  apply max_concurrency_least. intros p Hin.
  destruct (Hle p Hin) as [q [Hqin [_ Hconc]]].
  eapply Nat.le_trans; [exact Hconc |].
  apply concurrency_le_max. exact Hqin.
Qed.

Definition shift (k : nat) (p : obligation) : obligation :=
  Obligation (rate p) (concurrency p + k).

Definition shift_effect (k : nat) (Phi : effect) : effect :=
  map (shift k) Phi.

Lemma shift_effect_mono :
  forall Phi Psi k l,
    Phi ≼ Psi ->
    (k <= l)%nat ->
    shift_effect k Phi ≼ shift_effect l Psi.
Proof.
  intros Phi Psi k l HPhiPsi Hkl shifted_p Hin.
  apply in_map_iff in Hin.
  destruct Hin as [p [Hp_eq Hp_in]].
  subst shifted_p.
  destruct (HPhiPsi p Hp_in) as [q [Hq_in [Hrate Hconc]]].
  exists (shift l q). split.
  - apply in_map. exact Hq_in.
  - split; simpl.
    + exact Hrate.
    + lia.
Qed.

(** Raw parallel composition. Each side is shifted by the largest concurrency
    of the other side. *)
Definition parallel (Phi Psi : effect) : effect :=
  join
    (shift_effect (max_concurrency Psi) Phi)
    (shift_effect (max_concurrency Phi) Psi).

Lemma parallel_mono :
  forall Phi1 Phi2 Psi1 Psi2,
    Phi1 ≼ Psi1 ->
    Phi2 ≼ Psi2 ->
    parallel Phi1 Phi2 ≼ parallel Psi1 Psi2.
Proof.
  intros Phi1 Phi2 Psi1 Psi2 H1 H2.
  unfold parallel.
  apply join_mono.
  - apply shift_effect_mono.
    + exact H1.
    + apply max_concurrency_mono. exact H2.
  - apply shift_effect_mono.
    + exact H2.
    + apply max_concurrency_mono. exact H1.
Qed.

(** Nonnegativity will be an invariant of all effects produced by typing. *)
Definition obligation_wf (p : obligation) : Prop := 0 <= rate p.

Definition effect_wf (Phi : effect) : Prop := Forall obligation_wf Phi.

Lemma effect_wf_join :
  forall Phi Psi,
    effect_wf Phi -> effect_wf Psi -> effect_wf (join Phi Psi).
Proof.
  intros Phi Psi HPhi HPsi. unfold effect_wf, join in *.
  apply Forall_app. split; assumption.
Qed.

Lemma effect_wf_shift :
  forall k Phi,
    effect_wf Phi -> effect_wf (shift_effect k Phi).
Proof.
  intros k Phi Hwf. unfold effect_wf, shift_effect in *.
  apply Forall_map. exact Hwf.
Qed.

Lemma effect_wf_parallel :
  forall Phi Psi,
    effect_wf Phi -> effect_wf Psi -> effect_wf (parallel Phi Psi).
Proof.
  intros Phi Psi HPhi HPsi. unfold parallel.
  apply effect_wf_join.
  - apply effect_wf_shift. exact HPhi.
  - apply effect_wf_shift. exact HPsi.
Qed.
