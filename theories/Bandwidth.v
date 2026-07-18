(** Bandwidth obligations and their interaction with effect coverage. *)

From Stdlib Require Import Arith Lia Lra List QArith Qminmax ZArith.
From BandwidthTimeout Require Import Effects Normalization.

Import ListNotations.
Open Scope Q_scope.

(** Embed a natural-number concurrency count into the rationals. *)
Definition qnat (n : nat) : Q := inject_Z (Z.of_nat n).

(** The bandwidth required by [(r,n)] is the product [r * n]. *)
Definition obligation_bandwidth (p : obligation) : Q :=
  rate p * qnat (concurrency p).

(** This pointwise form is the semantic bandwidth check. For a finite effect it
    is equivalent, under a nonnegative bandwidth assumption, to comparing [B]
    against the maximum [obligation_bandwidth] in the effect. *)
Definition bandwidth_safe (B : Q) (Phi : effect) : Prop :=
  forall p, In p Phi -> obligation_bandwidth p <= B.

(** The executable maximum-bandwidth summary from the paper. The empty effect
    requires zero bandwidth. *)
Fixpoint required_bandwidth (Phi : effect) : Q :=
  match Phi with
  | [] => 0
  | p :: Phi' => Qmax (obligation_bandwidth p) (required_bandwidth Phi')
  end.

(** Every natural number remains nonnegative after embedding into [Q]. *)
Lemma qnat_nonnegative : forall n, 0 <= qnat n.
Proof.
  intro n. unfold qnat.
  change (inject_Z 0 <= inject_Z (Z.of_nat n)).
  rewrite <- Zle_Qle. apply Nat2Z.is_nonneg.
Qed.

(** The embedding [qnat] preserves the natural-number ordering. *)
Lemma qnat_mono :
  forall n m,
    (n <= m)%nat ->
    qnat n <= qnat m.
Proof.
  intros n m Hnm. unfold qnat.
  rewrite <- Zle_Qle. apply Nat2Z.inj_le. exact Hnm.
Qed.

(** For nonnegative rates, making either coordinate of an obligation larger
    cannot decrease its required bandwidth. *)
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

(** The computed required bandwidth is always nonnegative, including for an
    empty or ill-formed input list. *)
Lemma required_bandwidth_nonnegative :
  forall Phi,
    0 <= required_bandwidth Phi.
Proof.
  induction Phi as [|p Phi IH]; simpl.
  - apply Qle_refl.
  - eapply Qle_trans.
    + exact IH.
    + apply Q.le_max_r.
Qed.

(** Every member's bandwidth demand is bounded by the maximum demand computed
    for the whole effect. *)
Lemma obligation_bandwidth_le_required :
  forall Phi p,
    In p Phi ->
    obligation_bandwidth p <= required_bandwidth Phi.
Proof.
  induction Phi as [|q Phi IH]; intros p Hin; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + apply Q.le_max_l.
    + eapply Qle_trans.
      * apply IH. exact Hin.
      * apply Q.le_max_r.
Qed.

(** If a nonnegative budget [B] satisfies every obligation, the computed
    maximum required bandwidth is at most [B]. *)
Lemma required_bandwidth_least :
  forall Phi B,
    0 <= B ->
    bandwidth_safe B Phi ->
    required_bandwidth Phi <= B.
Proof.
  induction Phi as [|p Phi IH]; intros B HB Hsafe; simpl.
  - exact HB.
  - apply Q.max_lub.
    + apply Hsafe. simpl. auto.
    + apply IH.
      * exact HB.
      * intros q Hq. apply Hsafe. simpl. auto.
Qed.

(** For a nonnegative budget, the pointwise safety predicate is equivalent to
    one comparison with [required_bandwidth]. *)
Theorem required_bandwidth_spec :
  forall Phi B,
    0 <= B ->
    (bandwidth_safe B Phi <-> required_bandwidth Phi <= B).
Proof.
  intros Phi B HB. split.
  - apply required_bandwidth_least. exact HB.
  - intros Hrequired p Hp.
    eapply Qle_trans.
    + apply obligation_bandwidth_le_required. exact Hp.
    + exact Hrequired.
Qed.

(** An effect is pointwise safe under its own computed bandwidth requirement. *)
Lemma required_bandwidth_is_safe :
  forall Phi,
    bandwidth_safe (required_bandwidth Phi) Phi.
Proof.
  intros Phi p Hp.
  apply obligation_bandwidth_le_required. exact Hp.
Qed.

(** Safety flows backward through effect overapproximation: if [Psi] safely
    overapproximates well-formed [Phi], safety of [Psi] implies safety of
    [Phi]. *)
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

(** With a nonnegative budget, safety also flows backward through effect
    overapproximation without a well-formedness premise on the smaller effect.
    A negative-rate obligation is automatically below the budget; all other
    obligations use ordinary bandwidth monotonicity. *)
Lemma bandwidth_safe_antitone_nonnegative_budget :
  forall B Phi Psi,
    0 <= B ->
    Phi ≼ Psi ->
    bandwidth_safe B Psi ->
    bandwidth_safe B Phi.
Proof.
  intros B Phi Psi HB Hle Hsafe p Hp_in.
  destruct (Hle p Hp_in) as [q [Hq_in Hpq]].
  destruct (Qlt_le_dec (rate p) 0) as [Hnegative | Hnonnegative].
  - unfold obligation_bandwidth.
    pose proof
      (Qmult_le_compat_r
        (rate p) 0 (qnat (concurrency p))
        (Qlt_le_weak _ _ Hnegative)
        (qnat_nonnegative (concurrency p))) as Hzero.
    setoid_replace (0 * qnat (concurrency p)) with 0 in Hzero by ring.
    eapply Qle_trans; eauto.
  - eapply Qle_trans.
    + apply obligation_bandwidth_mono.
      * exact Hnonnegative.
      * exact Hpq.
    + apply Hsafe. exact Hq_in.
Qed.

(** Filtering a list cannot invalidate a property that held for every original
    element. *)
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

(** Inserting a well-formed obligation into a well-formed frontier candidate
    preserves rate nonnegativity. *)
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

(** Pareto normalization preserves effect well-formedness. *)
Lemma normalize_wf :
  forall Phi,
    effect_wf Phi ->
    effect_wf (normalize Phi).
Proof.
  intros Phi Hwf. induction Hwf; simpl.
  - constructor.
  - apply insert_frontier_wf; assumption.
Qed.

(** For well-formed effects, normalization preserves the pointwise bandwidth
    safety judgment in both directions. *)
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

(** [Q] uses setoid equality [Qeq], written [==], because rational values can
    have distinct concrete representations for the same number. This theorem
    is the exact numeric [ReqBW] preservation result from the paper. *)
Theorem normalize_required_bandwidth :
  forall Phi,
    effect_wf Phi ->
    required_bandwidth (normalize Phi) == required_bandwidth Phi.
Proof.
  intros Phi Hwf. apply Qle_antisym.
  - apply required_bandwidth_least.
    + apply required_bandwidth_nonnegative.
    + eapply bandwidth_safe_antitone.
      * apply normalize_wf. exact Hwf.
      * apply normalize_le.
      * apply required_bandwidth_is_safe.
  - apply required_bandwidth_least.
    + apply required_bandwidth_nonnegative.
    + eapply bandwidth_safe_antitone.
      * exact Hwf.
      * apply le_normalize.
      * apply required_bandwidth_is_safe.
Qed.
