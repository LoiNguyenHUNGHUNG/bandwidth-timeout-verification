(** Root bandwidth constraints for size inference.

    Local inference produces a symbolic effect.  At the root of a closed
    program, the paper turns every symbolic obligation into either one upper
    bound on one inferred size variable or one variable-free bandwidth check.
    This file proves that those constraints are exact for the normalized
    instantiated effect and remain in the separable solver fragment. *)

From Stdlib Require Import Arith Lia List QArith ZArith.

From BandwidthTimeout Require Import Effects Normalization Bandwidth
  SizeInference Symbolic Compatibility.

Import ListNotations.
Open Scope Q_scope.

(** A positive natural concurrency remains strictly positive after embedding
    into the rationals. *)
Lemma qnat_positive :
  forall n,
    (0 < n)%nat ->
    0 < qnat n.
Proof.
  intros n Hn. unfold qnat.
  change (inject_Z 0 < inject_Z (Z.of_nat n)).
  rewrite <- Zlt_Qlt.
  change (Z.of_nat 0 < Z.of_nat n)%Z.
  apply Nat2Z.inj_lt. exact Hn.
Qed.

(** The paper's [RootC] operation for one symbolic obligation.

    For positive concurrency, a symbolic rate [a/t] produces [a <= B*t/n].
    The general effect datatype also admits the harmless edge case [n = 0];
    its exact bandwidth condition is the variable-free check [0 <= B]. *)
Definition root_obligation_constraint
    (p : symbolic_obligation) (B : Q) : constraint :=
  match symbolic_obligation_rate p with
  | SRateVariable variable timeout =>
      match symbolic_concurrency p with
      | O => CConcreteLe 0 B
      | S _ as concurrency_value =>
          CUpper variable (B * timeout / qnat concurrency_value)
      end
  | SRateConcrete concrete_rate =>
      CConcreteLe
        (qnat (symbolic_concurrency p) * concrete_rate)
        B
  end.

(** Root checking conjoins [RootC] for every obligation in the symbolic
    whole-program effect. *)
Fixpoint root_constraint
    (Phi : symbolic_effect) (B : Q) : constraint :=
  match Phi with
  | [] => CTop
  | p :: Phi' =>
      CAnd (root_obligation_constraint p B) (root_constraint Phi' B)
  end.

(** One root constraint is exactly the bandwidth check for its instantiated
    obligation. *)
Lemma root_obligation_constraint_exact :
  forall sigma p B,
    symbolic_obligation_wf p ->
    (satisfies_constraint sigma (root_obligation_constraint p B) <->
     obligation_bandwidth (instantiate_obligation sigma p) <= B).
Proof.
  intros sigma [symbolic concurrency_value] B Hwf.
  unfold symbolic_obligation_wf in Hwf. simpl in Hwf.
  destruct symbolic as [variable timeout | concrete_rate].
  - inversion Hwf; subst. destruct concurrency_value as [|concurrency_tail].
    + unfold obligation_bandwidth. simpl.
      setoid_replace (sigma variable / timeout * 0) with 0 by ring.
      tauto.
    + unfold obligation_bandwidth. simpl. split; intro Hbound.
      * assert (Hconcurrency : 0 < qnat (S concurrency_tail)).
        { apply qnat_positive. lia. }
        pose proof
          (Qmult_le_compat_r
             (sigma variable)
             (B * timeout / qnat (S concurrency_tail))
             (qnat (S concurrency_tail))
             Hbound
             (Qlt_le_weak _ _ Hconcurrency)) as Hscaled.
        setoid_replace
          ((B * timeout / qnat (S concurrency_tail)) *
             qnat (S concurrency_tail))
          with (B * timeout) in Hscaled.
        2: { field. intro Hzero.
             apply (Qlt_not_eq 0 (qnat (S concurrency_tail)) Hconcurrency).
             symmetry. exact Hzero. }
        setoid_replace
          ((sigma variable / timeout) * qnat (S concurrency_tail))
          with ((sigma variable * qnat (S concurrency_tail)) / timeout).
        2: { field. intro Hzero. apply (Qlt_not_eq 0 timeout H0).
             symmetry. exact Hzero. }
        apply Qle_shift_div_r; [exact H0 |].
        exact Hscaled.
      * assert (Hconcurrency : 0 < qnat (S concurrency_tail)).
        { apply qnat_positive. lia. }
        apply Qle_shift_div_l; [exact Hconcurrency |].
        pose proof
          (Qmult_le_compat_r
             ((sigma variable / timeout) * qnat (S concurrency_tail))
             B timeout Hbound (Qlt_le_weak _ _ H0)) as Hscaled.
        setoid_replace
          ((sigma variable / timeout) * qnat (S concurrency_tail) * timeout)
          with (sigma variable * qnat (S concurrency_tail)) in Hscaled.
        2: { field. intro Hzero. apply (Qlt_not_eq 0 timeout H0).
             symmetry. exact Hzero. }
        exact Hscaled.
  - unfold obligation_bandwidth. simpl.
    setoid_replace (concrete_rate * qnat concurrency_value)
      with (qnat concurrency_value * concrete_rate) by ring.
    tauto.
Qed.

(** Satisfaction of all root constraints is exactly pointwise safety of the
    unnormalized instantiated effect. *)
Lemma root_constraint_raw_exact :
  forall sigma Phi B,
    symbolic_effect_wf Phi ->
    (satisfies_constraint sigma (root_constraint Phi B) <->
     bandwidth_safe B (instantiate_effect_raw sigma Phi)).
Proof.
  intros sigma Phi. induction Phi as [|head tail IH]; intros B Hwf; simpl.
  - split.
    + intros _ p Hin. inversion Hin.
    + intros _. exact I.
  - inversion Hwf as [|head' tail' Hhead Htail]; subst.
    rewrite (root_obligation_constraint_exact sigma head B Hhead).
    rewrite (IH B Htail). split.
    + intros [Hhead_safe Htail_safe] p Hin.
      destruct Hin as [Heq | Hin].
      * subst p. exact Hhead_safe.
      * apply Htail_safe. exact Hin.
    + intro Hsafe. split.
      * apply Hsafe. left. reflexivity.
      * intros p Hin. apply Hsafe. right. exact Hin.
Qed.

(** Root constraints use only conjunction, single-variable upper bounds, and
    concrete comparisons, so no constraint relates two inferred variables. *)
Theorem root_constraint_fragment :
  forall Phi B,
    compatibility_fragment (root_constraint Phi B).
Proof.
  intros Phi B. induction Phi as [|p Phi IH]; simpl.
  - constructor.
  - constructor.
    + destruct p as [[variable timeout | concrete_rate] concurrency_value];
        simpl.
      * destruct concurrency_value; constructor.
      * constructor.
    + exact IH.
Qed.

(** Main root-constraint exactness theorem from the paper.  A well-formed
    assignment models the generated root constraint exactly when the required
    bandwidth of the normalized instantiated effect is within budget. *)
Theorem root_constraint_exact :
  forall sigma Phi B,
    assignment_wf sigma ->
    symbolic_effect_wf Phi ->
    0 <= B ->
    (models sigma (root_constraint Phi B) <->
     required_bandwidth (instantiate_effect sigma Phi) <= B).
Proof.
  intros sigma Phi B Hsigma Hwf HB.
  pose proof (instantiate_effect_raw_wf sigma Phi Hsigma Hwf) as Hraw_wf.
  unfold models, instantiate_effect. split.
  - intros [_ Hroot].
    apply (proj1 (required_bandwidth_spec (normalize
      (instantiate_effect_raw sigma Phi)) B HB)).
    apply (proj2 (normalize_bandwidth_safe_iff
      B (instantiate_effect_raw sigma Phi) Hraw_wf)).
    apply (proj1 (root_constraint_raw_exact sigma Phi B Hwf)).
    exact Hroot.
  - intro Hrequired. split.
    + exact Hsigma.
    + apply (proj2 (root_constraint_raw_exact sigma Phi B Hwf)).
      apply (proj1 (normalize_bandwidth_safe_iff
        B (instantiate_effect_raw sigma Phi) Hraw_wf)).
      apply (proj2 (required_bandwidth_spec (normalize
        (instantiate_effect_raw sigma Phi)) B HB)).
      exact Hrequired.
Qed.
