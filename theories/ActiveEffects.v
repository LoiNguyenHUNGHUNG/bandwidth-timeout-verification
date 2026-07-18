(** Algebra of effects induced by the currently running downloads.

    [ActiveWF] defined the active rate multiset and its normalized effect. This
    file proves the two numerical and compositional facts used by the safety
    argument: its maximum concurrency is the multiset cardinality, and active
    effects distribute safely over finite multiset union. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import
  Effects Normalization Typing ActiveWF.

Import ListNotations.
Open Scope Q_scope.

(** A nonempty list of obligations whose concurrency coordinate is constantly
    [n] has maximum concurrency exactly [n]. *)
Lemma max_concurrency_constant_nonempty :
  forall n required_rate rates,
    max_concurrency
      (map (fun rate => Obligation rate n) (required_rate :: rates)) = n.
Proof.
  intros n required_rate rates. revert required_rate.
  induction rates as [|rate rates IH]; intros required_rate.
  - simpl. lia.
  - change (Nat.max n
      (max_concurrency
        (map (fun current_rate => Obligation current_rate n)
          (rate :: rates))) = n).
    rewrite (IH rate). lia.
Qed.

(** The maximum concurrency recorded by an active effect is precisely the
    number of currently running downloads. Normalization does not change the
    maximum. *)
Theorem active_effect_concurrency :
  forall rates,
    max_concurrency (active_effect rates) = length rates.
Proof.
  intros [|required_rate rates].
  - reflexivity.
  - unfold active_effect. rewrite max_concurrency_normalize.
    apply max_concurrency_constant_nonempty.
Qed.

(** The raw obligations for a multiset union are covered by parallel
    composition of the two normalized active effects. An occurrence from the
    left receives the right cardinality as its shift, and conversely. *)
Lemma raw_active_union_le_parallel :
  forall left right,
    map (fun required_rate =>
      Obligation required_rate (length (left ++ right))) (left ++ right)
    ≼ parallel_effect (active_effect left) (active_effect right).
Proof.
  intros left right p Hp.
  rewrite map_app in Hp. apply in_app_or in Hp. destruct Hp as [Hp | Hp].
  - apply in_map_iff in Hp.
    destruct Hp as [required_rate [Hp Hin]]. subst p.
    assert (Hcovered :
      covers (active_effect left)
        (Obligation required_rate (length left))).
    { unfold active_effect.
      apply (le_normalize
        (map (fun current_rate => Obligation current_rate (length left))
          left)).
      apply in_map_iff. exists required_rate. split; [reflexivity | exact Hin]. }
    destruct Hcovered as [q [Hq [Hrate Hconcurrency]]].
    unfold parallel_effect.
    eapply covers_weaken_obligation with (q := shift (length right) q).
    + split.
      * exact Hrate.
      * unfold shift. simpl. rewrite length_app.
        apply Nat.add_le_mono_r. exact Hconcurrency.
    + apply le_normalize. unfold parallel, join.
      apply in_or_app. left. unfold shift_effect.
      rewrite active_effect_concurrency. apply in_map_iff.
      exists q. split; [reflexivity | exact Hq].
  - apply in_map_iff in Hp.
    destruct Hp as [required_rate [Hp Hin]]. subst p.
    assert (Hcovered :
      covers (active_effect right)
        (Obligation required_rate (length right))).
    { unfold active_effect.
      apply (le_normalize
        (map (fun current_rate => Obligation current_rate (length right))
          right)).
      apply in_map_iff. exists required_rate. split; [reflexivity | exact Hin]. }
    destruct Hcovered as [q [Hq [Hrate Hconcurrency]]].
    unfold parallel_effect.
    eapply covers_weaken_obligation with (q := shift (length left) q).
    + split.
      * exact Hrate.
      * unfold shift. simpl. rewrite length_app.
        rewrite Nat.add_comm. apply Nat.add_le_mono_r. exact Hconcurrency.
    + apply le_normalize. unfold parallel, join.
      apply in_or_app. right. unfold shift_effect.
      rewrite active_effect_concurrency. apply in_map_iff.
      exists q. split; [reflexivity | exact Hq].
Qed.

(** Active effects of binary multiset union are safely overapproximated by
    normalized parallel effect composition. List append represents multiset
    union, so duplicate occurrences are retained. *)
Theorem active_effect_union :
  forall left right,
    active_effect (left ++ right)
    ≼ parallel_effect (active_effect left) (active_effect right).
Proof.
  intros left right. unfold active_effect at 1.
  eapply effect_le_trans.
  - apply normalize_le.
  - apply raw_active_union_le_parallel.
Qed.

(** The binary union result iterates over any finite list of rate multisets.
    The right-associated fold exactly matches [parallel_effects]. *)
Theorem active_effect_concat :
  forall rate_lists,
    active_effect (concat rate_lists)
    ≼ parallel_effects (map active_effect rate_lists).
Proof.
  intros rate_lists. induction rate_lists as [|rates rate_lists IH]; simpl.
  - apply effect_le_refl.
  - eapply effect_le_trans.
    + apply active_effect_union.
    + apply parallel_effect_mono.
      * apply effect_le_refl.
      * exact IH.
Qed.
