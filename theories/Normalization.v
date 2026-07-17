(** Executable Pareto normalization and its semantic correctness. *)

From Stdlib Require Import Arith Bool Lia List QArith.
From BandwidthTimeout Require Import Effects.

Import ListNotations.
Open Scope Q_scope.

(** Boolean reflection of coordinatewise obligation ordering. *)
Definition obligation_leb (p q : obligation) : bool :=
  Qle_bool (rate p) (rate q) &&
  Nat.leb (concurrency p) (concurrency q).

(** The executable Boolean test returns [true] exactly when the propositional
    ordering [obligation_le] holds. *)
Lemma obligation_leb_spec :
  forall p q,
    obligation_leb p q = true <-> obligation_le p q.
Proof.
  intros p q. unfold obligation_leb, obligation_le.
  rewrite andb_true_iff, Qle_bool_iff, Nat.leb_le.
  reflexivity.
Qed.

(** Insert [p] into a frontier candidate.

    If an existing obligation covers [p], [p] is redundant. Otherwise [p] is
    retained and obligations that it covers are removed. *)
Definition insert_frontier (p : obligation) (Phi : effect) : effect :=
  if existsb (obligation_leb p) Phi then
    Phi
  else
    p :: filter (fun q => negb (obligation_leb q p)) Phi.

(** Adding the same head obligation to both effects preserves [≼]. *)
Lemma effect_le_cons_mono :
  forall p Phi Psi,
    Phi ≼ Psi ->
    p :: Phi ≼ p :: Psi.
Proof.
  intros p Phi Psi Hle q Hin.
  simpl in Hin. destruct Hin as [-> | Hin].
  - apply covers_member. simpl. auto.
  - destruct (Hle q Hin) as [r [Hr_in Hqr]].
    exists r. split; [simpl; auto | exact Hqr].
Qed.

(** Frontier insertion never introduces an obligation that is not covered by
    the original list [p :: Phi]. *)
Lemma insert_frontier_le_cons :
  forall p Phi,
    insert_frontier p Phi ≼ p :: Phi.
Proof.
  intros p Phi. unfold insert_frontier.
  destruct (existsb (obligation_leb p) Phi) eqn:Hexists;
    intros q Hq.
  - apply covers_member. simpl. auto.
  - simpl in Hq. destruct Hq as [-> | Hq].
    + apply covers_member. simpl. auto.
    + apply filter_In in Hq. destruct Hq as [Hq_in _].
      apply covers_member. simpl. auto.
Qed.

(** Frontier insertion still covers every obligation from [p :: Phi], even
    when it deletes dominated entries. *)
Lemma cons_le_insert_frontier :
  forall p Phi,
    p :: Phi ≼ insert_frontier p Phi.
Proof.
  intros p Phi. unfold insert_frontier.
  destruct (existsb (obligation_leb p) Phi) eqn:Hexists.
  - apply existsb_exists in Hexists.
    destruct Hexists as [r [Hr_in Hpr_bool]].
    apply obligation_leb_spec in Hpr_bool.
    intros q Hq. simpl in Hq. destruct Hq as [-> | Hq].
    + exists r. split; assumption.
    + apply covers_member. exact Hq.
  - intros q Hq. simpl in Hq. destruct Hq as [-> | Hq].
    + apply covers_member. simpl. auto.
    + destruct (obligation_leb q p) eqn:Hqp_bool.
      * exists p. split.
        -- simpl. auto.
        -- apply obligation_leb_spec. exact Hqp_bool.
      * apply covers_member. simpl. right.
        apply filter_In. split; [exact Hq |].
        rewrite Hqp_bool. reflexivity.
Qed.

(** Compute a Pareto frontier by inserting each obligation into the normalized
    remainder of the list. *)
Fixpoint normalize (Phi : effect) : effect :=
  match Phi with
  | [] => []
  | p :: Phi' => insert_frontier p (normalize Phi')
  end.

(** Every normalized obligation is covered by the original effect. *)
Lemma normalize_le : forall Phi, normalize Phi ≼ Phi.
Proof.
  induction Phi as [|p Phi IH]; simpl.
  - apply effect_le_refl.
  - eapply effect_le_trans.
    + apply insert_frontier_le_cons.
    + apply effect_le_cons_mono. exact IH.
Qed.

(** Every original obligation remains covered after normalization. *)
Lemma le_normalize : forall Phi, Phi ≼ normalize Phi.
Proof.
  induction Phi as [|p Phi IH]; simpl.
  - apply effect_le_refl.
  - eapply effect_le_trans.
    + apply effect_le_cons_mono. exact IH.
    + apply cons_le_insert_frontier.
Qed.

(** Two effects are coverage-equivalent when each safely overapproximates the
    other. They may still differ as concrete lists. *)
Definition effect_equiv (Phi Psi : effect) : Prop :=
  Phi ≼ Psi /\ Psi ≼ Phi.

(** The notation [Phi ≈ Psi] denotes mutual coverage, not list equality. *)
Notation "Phi ≈ Psi" := (effect_equiv Phi Psi) (at level 70).

(** Normalization preserves the exact coverage semantics of an effect. *)
Theorem normalize_coverage_equiv : forall Phi, normalize Phi ≈ Phi.
Proof.
  intro Phi. split.
  - apply normalize_le.
  - apply le_normalize.
Qed.

(** An individual obligation is covered after normalization exactly when it
    was covered before normalization. *)
Corollary normalize_covers_iff :
  forall Phi p,
    covers (normalize Phi) p <-> covers Phi p.
Proof.
  intros Phi p. split; intros Hcovers.
  - destruct Hcovers as [q [Hq_in Hpq]].
    eapply covers_weaken_obligation; [exact Hpq |].
    apply normalize_le. exact Hq_in.
  - destruct Hcovers as [q [Hq_in Hpq]].
    eapply covers_weaken_obligation; [exact Hpq |].
    apply le_normalize. exact Hq_in.
Qed.

(** An antichain has no two distinct entries for which the first is
    coordinatewise below the second. *)
Definition antichain (Phi : effect) : Prop :=
  forall p q,
    In p Phi ->
    In q Phi ->
    obligation_le p q ->
    p = q.

(** A Pareto frontier is an antichain with no duplicate list entries. *)
Definition pareto_frontier (Phi : effect) : Prop :=
  NoDup Phi /\ antichain Phi.

(** Inserting into a duplicate-free candidate frontier preserves [NoDup]. *)
Lemma insert_frontier_nodup :
  forall p Phi,
    NoDup Phi ->
    NoDup (insert_frontier p Phi).
Proof.
  intros p Phi Hnodup. unfold insert_frontier.
  destruct (existsb (obligation_leb p) Phi) eqn:Hexists.
  - exact Hnodup.
  - constructor.
    + intro Hp_filter.
      apply filter_In in Hp_filter.
      destruct Hp_filter as [Hp_in _].
      assert (existsb (obligation_leb p) Phi = true) as Htrue.
      { apply existsb_exists. exists p. split; [exact Hp_in |].
        apply obligation_leb_spec. apply obligation_le_refl. }
      rewrite Hexists in Htrue. discriminate.
    + apply NoDup_filter. exact Hnodup.
Qed.

(** Inserting into an antichain and removing dominated entries produces another
    antichain. *)
Lemma insert_frontier_antichain :
  forall p Phi,
    antichain Phi ->
    antichain (insert_frontier p Phi).
Proof.
  intros p Phi Hanti. unfold insert_frontier.
  destruct (existsb (obligation_leb p) Phi) eqn:Hexists.
  - exact Hanti.
  - intros x y Hx Hy Hxy.
    simpl in Hx, Hy.
    destruct Hx as [Hx | Hx]; destruct Hy as [Hy | Hy].
    + subst. reflexivity.
    + subst x. exfalso.
      apply filter_In in Hy. destruct Hy as [Hy_in _].
      assert (existsb (obligation_leb p) Phi = true) as Htrue.
      { apply existsb_exists. exists y. split; [exact Hy_in |].
        apply obligation_leb_spec. exact Hxy. }
      rewrite Hexists in Htrue. discriminate.
    + subst y. exfalso.
      apply filter_In in Hx. destruct Hx as [_ Hx_not_covered].
      assert (obligation_leb x p = true) as Htrue.
      { apply obligation_leb_spec. exact Hxy. }
      rewrite Htrue in Hx_not_covered. discriminate.
    + apply filter_In in Hx. destruct Hx as [Hx_in _].
      apply filter_In in Hy. destruct Hy as [Hy_in _].
      eapply Hanti; eauto.
Qed.

(** The executable normalization function always returns a Pareto frontier. *)
Theorem normalize_is_pareto :
  forall Phi,
    pareto_frontier (normalize Phi).
Proof.
  induction Phi as [|p Phi [Hnodup Hanti]]; simpl.
  - split.
    + constructor.
    + intros x y Hx. inversion Hx.
  - split.
    + apply insert_frontier_nodup. exact Hnodup.
    + apply insert_frontier_antichain. exact Hanti.
Qed.
