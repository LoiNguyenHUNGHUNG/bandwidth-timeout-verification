(** Constraints for comparing inferred symbolic effects with concrete contracts.

    This file mechanizes [RateC] and [EffC] from the paper.  The direction of
    comparison is important: the left effect may contain inferred size
    variables, while the right effect is a programmer-written concrete
    contract.  Consequently every generated arithmetic constraint is either a
    concrete comparison or one upper bound on one inferred variable.

    Concrete effects are list-backed in this development.  [best_cover_rate]
    computes the paper's maximum concrete rate among obligations whose
    concurrency coordinate is large enough.  Its specification proves that
    choosing this one rate is exactly equivalent to existential effect
    coverage, independently of list order and duplicates. *)

From Stdlib Require Import Arith Lia List QArith Qminmax.

From BandwidthTimeout Require Import Effects Normalization SizeInference
  Symbolic.

Import ListNotations.
Open Scope Q_scope.

(** [rate_constraint symbolic upper] is the paper's [RateC].  A symbolic
    download rate [a/t] yields [a <= t * upper]; a concrete rate yields a
    variable-free comparison. *)
Definition rate_constraint
    (symbolic : symbolic_rate) (upper : Q) : constraint :=
  match symbolic with
  | SRateVariable variable timeout => CUpper variable (timeout * upper)
  | SRateConcrete concrete_rate => CConcreteLe concrete_rate upper
  end.

(** The fragment emitted by compatibility checking contains only conjunction,
    failure/success, single-variable upper bounds, and concrete comparisons.
    Nonnegativity constraints are introduced separately by [SI-Down]. *)
Inductive compatibility_fragment : constraint -> Prop :=
| CompatTop : compatibility_fragment CTop
| CompatBottom : compatibility_fragment CBottom
| CompatAnd : forall C1 C2,
    compatibility_fragment C1 ->
    compatibility_fragment C2 ->
    compatibility_fragment (CAnd C1 C2)
| CompatUpper : forall variable bound,
    compatibility_fragment (CUpper variable bound)
| CompatConcreteLe : forall lhs rhs,
    compatibility_fragment (CConcreteLe lhs rhs).

(** One rate comparison always belongs to the separable compatibility
    fragment.  In particular it can never relate two inferred variables. *)
Lemma rate_constraint_fragment :
  forall symbolic upper,
    compatibility_fragment (rate_constraint symbolic upper).
Proof.
  intros symbolic upper. destruct symbolic; simpl; constructor.
Qed.

(** Under the required positive-timeout invariant, satisfying [RateC] is
    exactly comparison of the instantiated concrete rate with its bound. *)
Lemma rate_constraint_exact :
  forall sigma symbolic upper,
    symbolic_rate_wf symbolic ->
    (satisfies_constraint sigma (rate_constraint symbolic upper) <->
     instantiate_rate sigma symbolic <= upper).
Proof.
  intros sigma symbolic upper Hwf. inversion Hwf; subst; simpl.
  - split.
    + intro Hupper. apply Qle_shift_div_r; [exact H |].
      setoid_replace (upper * timeout) with (timeout * upper) by ring.
      exact Hupper.
    + intro Hrate.
      pose proof
        (Qmult_le_compat_r
           (sigma variable / timeout) upper timeout Hrate
           (Qlt_le_weak _ _ H)) as Hmult.
      setoid_replace (sigma variable / timeout * timeout)
        with (sigma variable) in Hmult.
      * setoid_replace (upper * timeout) with (timeout * upper) in Hmult
          by ring.
        exact Hmult.
      * field. intro Hzero. apply (Qlt_not_eq 0 timeout H).
        symmetry. exact Hzero.
  - tauto.
Qed.

(** The best concrete rate capable of covering concurrency [needed].  [None]
    means that the concrete effect has no obligation with sufficiently large
    concurrency. *)
Fixpoint best_cover_rate (needed : nat) (Phi : effect) : option Q :=
  match Phi with
  | [] => None
  | p :: Phi' =>
      if Nat.leb needed (concurrency p)
      then
        match best_cover_rate needed Phi' with
        | None => Some (rate p)
        | Some tail_rate => Some (Qmax (rate p) tail_rate)
        end
      else best_cover_rate needed Phi'
  end.

(** Returning [None] is equivalent to absence of any concrete obligation with
    enough concurrency. *)
Lemma best_cover_rate_none_iff :
  forall needed Phi,
    best_cover_rate needed Phi = None <->
    forall p, In p Phi -> ~ (needed <= concurrency p)%nat.
Proof.
  intros needed Phi. induction Phi as [|head tail IH]; simpl.
  - split.
    + intros _ p Hin. inversion Hin.
    + intros _. reflexivity.
  - destruct (Nat.leb needed (concurrency head)) eqn:Hhead.
    + destruct (best_cover_rate needed tail); split; intro H.
      * discriminate.
      * exfalso. specialize (H head (or_introl eq_refl)).
        apply H. apply Nat.leb_le. exact Hhead.
      * discriminate.
      * exfalso. specialize (H head (or_introl eq_refl)).
        apply H. apply Nat.leb_le. exact Hhead.
    + rewrite IH. split.
      * intros Hnone p [-> | Hin].
        -- apply Nat.leb_gt in Hhead. lia.
        -- apply Hnone. exact Hin.
      * intros Hnone p Hin. apply Hnone. right. exact Hin.
Qed.

(** Every eligible concrete rate is below the computed best rate. *)
Lemma best_cover_rate_upper :
  forall needed Phi best p,
    best_cover_rate needed Phi = Some best ->
    In p Phi ->
    (needed <= concurrency p)%nat ->
    rate p <= best.
Proof.
  intros needed Phi. induction Phi as [|head tail IH];
    intros best p Hbest Hin Heligible; simpl in Hbest.
  - inversion Hin.
  - destruct (Nat.leb needed (concurrency head)) eqn:Hhead.
    + destruct (best_cover_rate needed tail) as [tail_rate|] eqn:Htail.
      * inversion Hbest; subst best. destruct Hin as [-> | Hin].
        -- apply Q.le_max_l.
        -- eapply Qle_trans.
           ++ eapply IH; eauto.
           ++ apply Q.le_max_r.
      * inversion Hbest; subst best. destruct Hin as [-> | Hin].
        -- apply Qle_refl.
        -- exfalso.
           apply (proj1 (best_cover_rate_none_iff needed tail) Htail p Hin).
           exact Heligible.
    + destruct Hin as [-> | Hin].
      * apply Nat.leb_gt in Hhead. lia.
      * eapply IH; eauto.
Qed.

(** A returned best rate is attained, up to rational equality, by an eligible
    obligation in the concrete effect.  The order statement is all later
    coverage proofs need. *)
Lemma best_cover_rate_witness :
  forall needed Phi best,
    best_cover_rate needed Phi = Some best ->
    exists p,
      In p Phi /\
      (needed <= concurrency p)%nat /\
      best <= rate p.
Proof.
  intros needed Phi. induction Phi as [|head tail IH];
    intros best Hbest; simpl in Hbest.
  - discriminate.
  - destruct (Nat.leb needed (concurrency head)) eqn:Hhead.
    + destruct (best_cover_rate needed tail) as [tail_rate|] eqn:Htail.
      * inversion Hbest; subst best.
        destruct (Q.max_spec (rate head) tail_rate)
          as [[_ Hmax] | [_ Hmax]].
        -- destruct (IH tail_rate eq_refl) as [p [Hin [Hconc Hrate]]].
           exists p. split; [right; exact Hin |]. split; [exact Hconc |].
           setoid_rewrite Hmax. exact Hrate.
        -- exists head. split; [left; reflexivity |]. split.
           ++ apply Nat.leb_le. exact Hhead.
           ++ setoid_rewrite Hmax. apply Qle_refl.
      * inversion Hbest; subst best. exists head.
        split; [left; reflexivity |]. split.
        -- apply Nat.leb_le. exact Hhead.
        -- apply Qle_refl.
    + destruct (IH best Hbest) as [p [Hin [Hconc Hrate]]].
      exists p. split; [right; exact Hin |]. split; assumption.
Qed.

(** If there is no eligible concrete obligation, no obligation at concurrency
    [needed] can be covered, regardless of its rate. *)
Lemma best_cover_rate_none_no_cover :
  forall needed Phi concrete_rate,
    best_cover_rate needed Phi = None ->
    ~ covers Phi (Obligation concrete_rate needed).
Proof.
  intros needed Phi concrete_rate Hnone [p [Hin [_ Hconc]]].
  apply (proj1 (best_cover_rate_none_iff needed Phi) Hnone p Hin).
  exact Hconc.
Qed.

(** With a defined best covering rate, [RateC] holds exactly when the concrete
    effect covers the instantiated symbolic obligation. *)
Lemma rate_constraint_covers_exact :
  forall sigma symbolic needed Phi best,
    symbolic_rate_wf symbolic ->
    best_cover_rate needed Phi = Some best ->
    (satisfies_constraint sigma (rate_constraint symbolic best) <->
     covers Phi (Obligation (instantiate_rate sigma symbolic) needed)).
Proof.
  intros sigma symbolic needed Phi best Hwf Hbest.
  rewrite rate_constraint_exact by exact Hwf. split.
  - intro Hrate.
    destruct (best_cover_rate_witness needed Phi best Hbest)
      as [p [Hin [Hconc Hbest_rate]]].
    exists p. split; [exact Hin |]. split.
    + eapply Qle_trans; eauto.
    + exact Hconc.
  - intros [p [Hin [Hrate Hconc]]].
    eapply Qle_trans.
    + exact Hrate.
    + eapply best_cover_rate_upper; eauto.
Qed.

(** [effect_constraint symbolic concrete] is the paper's [EffC].  It compares
    every symbolic obligation against the best eligible rate in the concrete
    contract, and fails if the contract has no eligible obligation. *)
Fixpoint effect_constraint
    (symbolic : symbolic_effect) (concrete : effect) : constraint :=
  match symbolic with
  | [] => CTop
  | p :: symbolic' =>
      match best_cover_rate (symbolic_concurrency p) concrete with
      | None => CBottom
      | Some upper =>
          CAnd
            (rate_constraint (symbolic_obligation_rate p) upper)
            (effect_constraint symbolic' concrete)
      end
  end.

(** Effect compatibility generates only the separable compatibility fragment.
    This is the mechanized no-variable-to-variable fact for [EffC]. *)
Theorem effect_constraint_fragment :
  forall symbolic concrete,
    compatibility_fragment (effect_constraint symbolic concrete).
Proof.
  intros symbolic concrete. induction symbolic as [|p symbolic IH]; simpl.
  - constructor.
  - destruct (best_cover_rate (symbolic_concurrency p) concrete).
    + constructor.
      * apply rate_constraint_fragment.
      * exact IH.
    + constructor.
Qed.

(** Satisfaction of [EffC] is exactly pointwise concrete coverage of every
    symbolic obligation before normalization. *)
Lemma effect_constraint_pointwise_exact :
  forall sigma symbolic concrete,
    symbolic_effect_wf symbolic ->
    (satisfies_constraint sigma (effect_constraint symbolic concrete) <->
     forall p,
       In p symbolic ->
       covers concrete (instantiate_obligation sigma p)).
Proof.
  intros sigma symbolic. induction symbolic as [|head tail IH];
    intros concrete Hwf; simpl.
  - split.
    + intros _ p Hin. inversion Hin.
    + intros _. exact I.
  - inversion Hwf as [|head' tail' Hhead Htail]; subst.
    destruct (best_cover_rate (symbolic_concurrency head) concrete)
      as [upper|] eqn:Hbest; simpl.
    + rewrite (rate_constraint_covers_exact
        sigma (symbolic_obligation_rate head)
        (symbolic_concurrency head) concrete upper Hhead Hbest).
      rewrite IH by exact Htail. split.
      * intros [Hcovers_head Hcovers_tail] p [-> | Hin].
        -- exact Hcovers_head.
        -- apply Hcovers_tail. exact Hin.
      * intro Hall. split.
        -- apply Hall. left. reflexivity.
        -- intros p Hin. apply Hall. right. exact Hin.
    + split.
      * contradiction.
      * intro Hall. exfalso.
        apply (best_cover_rate_none_no_cover
          (symbolic_concurrency head) concrete
          (instantiate_rate sigma (symbolic_obligation_rate head)) Hbest).
        apply Hall. left. reflexivity.
Qed.

(** Pointwise coverage of symbolic obligations is the same as effect ordering
    from their raw instantiated list. *)
Lemma instantiate_effect_raw_le_iff :
  forall sigma symbolic concrete,
    (forall p,
       In p symbolic ->
       covers concrete (instantiate_obligation sigma p)) <->
    instantiate_effect_raw sigma symbolic ≼ concrete.
Proof.
  intros sigma symbolic concrete. unfold instantiate_effect_raw, effect_le.
  split.
  - intros Hall p Hin.
    apply in_map_iff in Hin as [symbolic_p [Hp Hin]]. subst p.
    apply Hall. exact Hin.
  - intros Hle symbolic_p Hin. apply Hle.
    apply in_map. exact Hin.
Qed.

(** Main [EffC] exactness theorem.  For a well-formed assignment and symbolic
    effect, the generated constraint is modeled exactly when the normalized
    instantiated effect is covered by the programmer-written concrete
    contract. *)
Theorem effect_constraint_exact :
  forall sigma symbolic concrete,
    assignment_wf sigma ->
    symbolic_effect_wf symbolic ->
    (models sigma (effect_constraint symbolic concrete) <->
     instantiate_effect sigma symbolic ≼ concrete).
Proof.
  intros sigma symbolic concrete Hsigma Hwf.
  unfold models. rewrite effect_constraint_pointwise_exact by exact Hwf.
  rewrite instantiate_effect_raw_le_iff. unfold instantiate_effect. split.
  - intros [_ Hraw].
    eapply effect_le_trans.
    + apply normalize_le.
    + exact Hraw.
  - intro Hnormalized. split; [exact Hsigma |].
    eapply effect_le_trans.
    + apply le_normalize.
    + exact Hnormalized.
Qed.
