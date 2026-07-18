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
  Symbolic Typing.

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

(** A symbolic effect is a concrete contract when every rate is a concrete
    rate.  The relation also records the corresponding ordinary effect.
    Nonnegativity is included because programmer-written rates denote physical
    bandwidth requirements. *)
Inductive concrete_symbolic_effect : symbolic_effect -> effect -> Prop :=
| ConcreteSymbolicEffectNil :
    concrete_symbolic_effect [] []
| ConcreteSymbolicEffectCons : forall concrete_rate concurrency_value
                                      symbolic_tail concrete_tail,
    0 <= concrete_rate ->
    concrete_symbolic_effect symbolic_tail concrete_tail ->
    concrete_symbolic_effect
      (SymbolicObligation
         (SRateConcrete concrete_rate) concurrency_value :: symbolic_tail)
      (Obligation concrete_rate concurrency_value :: concrete_tail).

(** Reifying a concrete symbolic contract preserves its raw list exactly. *)
Lemma concrete_symbolic_effect_instantiates_raw :
  forall sigma symbolic concrete,
    concrete_symbolic_effect symbolic concrete ->
    instantiate_effect_raw sigma symbolic = concrete.
Proof.
  intros sigma symbolic concrete Hconcrete. induction Hconcrete; simpl.
  - reflexivity.
  - rewrite IHHconcrete. reflexivity.
Qed.

(** Normalized instantiation of a concrete symbolic contract is ordinary
    normalization of the reified concrete effect. *)
Lemma concrete_symbolic_effect_instantiates :
  forall sigma symbolic concrete,
    concrete_symbolic_effect symbolic concrete ->
    instantiate_effect sigma symbolic = normalize concrete.
Proof.
  intros sigma symbolic concrete Hconcrete. unfold instantiate_effect.
  rewrite (concrete_symbolic_effect_instantiates_raw
    sigma symbolic concrete Hconcrete). reflexivity.
Qed.

(** Concrete symbolic contracts are symbolically well formed. *)
Lemma concrete_symbolic_effect_wf :
  forall symbolic concrete,
    concrete_symbolic_effect symbolic concrete ->
    symbolic_effect_wf symbolic.
Proof.
  intros symbolic concrete Hconcrete. induction Hconcrete.
  - constructor.
  - constructor.
    + constructor. exact H.
    + exact IHHconcrete.
Qed.

(** Normalizing the right side of effect coverage does not change whether it
    covers a source effect. *)
Lemma effect_le_normalize_right_iff :
  forall Phi Psi,
    Phi ≼ normalize Psi <-> Phi ≼ Psi.
Proof.
  intros Phi Psi. split; intro Hle.
  - eapply effect_le_trans.
    + exact Hle.
    + apply normalize_le.
  - eapply effect_le_trans.
    + exact Hle.
    + apply le_normalize.
Qed.

(** Under a fixed well-formed assignment, modeling a conjunction is exactly
    modeling both conjuncts. *)
Lemma models_and_iff :
  forall sigma C1 C2,
    assignment_wf sigma ->
    (models sigma (CAnd C1 C2) <->
     models sigma C1 /\ models sigma C2).
Proof.
  intros sigma C1 C2 Hsigma. unfold models. simpl. tauto.
Qed.

(** Outer-shape compatibility for symbolic types.  Product arity is handled
    by the mutually defined list judgment below. *)
Definition same_symbolic_type_shape
    (source target : symbolic_ty) : bool :=
  match source, target with
  | STyUnit, STyUnit => true
  | STyNat, STyNat => true
  | STyArrow _ _ _, STyArrow _ _ _ => true
  | STyProduct _, STyProduct _ => true
  | _, _ => false
  end.

(** Different outer symbolic shapes can never instantiate to related concrete
    types. *)
Lemma different_symbolic_shapes_not_subtype :
  forall sigma source target,
    same_symbolic_type_shape source target = false ->
    ~ subtype (instantiate_ty sigma source) (instantiate_ty sigma target).
Proof.
  intros sigma source target Hshape Hsubtype.
  destruct source; destruct target; simpl in Hshape; try discriminate;
    simpl in Hsubtype; inversion Hsubtype.
Qed.

(** Structural symbolic type compatibility from the paper.

    [subtype_constraint source target C] represents
    [SubTyC(source,target)=C].  In the arrow rule, the target latent effect is
    reified as a concrete contract, the domain check is contravariant, and the
    result check is covariant.  The mutually defined list judgment handles
    product components and generates [CBottom] for arity mismatch. *)
Inductive subtype_constraint : symbolic_ty -> symbolic_ty -> constraint -> Prop :=
| SubtypeConstraintUnit :
    subtype_constraint STyUnit STyUnit CTop
| SubtypeConstraintNat :
    subtype_constraint STyNat STyNat CTop
| SubtypeConstraintArrow :
    forall source_domain source_latent source_codomain
           target_domain target_latent target_codomain
           concrete_target_latent domain_constraint codomain_constraint,
      symbolic_effect_wf source_latent ->
      concrete_symbolic_effect target_latent concrete_target_latent ->
      subtype_constraint
        target_domain source_domain domain_constraint ->
      subtype_constraint
        source_codomain target_codomain codomain_constraint ->
      subtype_constraint
        (STyArrow source_domain source_latent source_codomain)
        (STyArrow target_domain target_latent target_codomain)
        (CAnd
          domain_constraint
          (CAnd
            (effect_constraint source_latent concrete_target_latent)
            codomain_constraint))
| SubtypeConstraintProduct :
    forall source_components target_components components_constraint,
      subtype_constraint_list
        source_components target_components components_constraint ->
      subtype_constraint
        (STyProduct source_components)
        (STyProduct target_components)
        components_constraint
| SubtypeConstraintShapeMismatch :
    forall source target,
      same_symbolic_type_shape source target = false ->
      subtype_constraint source target CBottom
with subtype_constraint_list :
    list symbolic_ty -> list symbolic_ty -> constraint -> Prop :=
| SubtypeConstraintListNil :
    subtype_constraint_list [] [] CTop
| SubtypeConstraintListCons :
    forall source source_tail target target_tail
           head_constraint tail_constraint,
      subtype_constraint source target head_constraint ->
      subtype_constraint_list source_tail target_tail tail_constraint ->
      subtype_constraint_list
        (source :: source_tail)
        (target :: target_tail)
        (CAnd head_constraint tail_constraint)
| SubtypeConstraintListLeftShort :
    forall target target_tail,
      subtype_constraint_list [] (target :: target_tail) CBottom
| SubtypeConstraintListRightShort :
    forall source source_tail,
      subtype_constraint_list (source :: source_tail) [] CBottom.

Scheme subtype_constraint_ind_mut :=
  Induction for subtype_constraint Sort Prop
with subtype_constraint_list_ind_mut :=
  Induction for subtype_constraint_list Sort Prop.

Combined Scheme subtype_constraint_mutind
  from subtype_constraint_ind_mut, subtype_constraint_list_ind_mut.

(** Every structural type-compatibility constraint remains in the same
    separable fragment as [RateC] and [EffC]. *)
Lemma subtype_constraint_fragment_mut :
  (forall source target C,
      subtype_constraint source target C ->
      compatibility_fragment C) /\
  (forall sources targets C,
      subtype_constraint_list sources targets C ->
      compatibility_fragment C).
Proof.
  apply subtype_constraint_mutind.
  - constructor.
  - constructor.
  - intros source_domain source_latent source_codomain
      target_domain target_latent target_codomain concrete_target_latent
      domain_constraint codomain_constraint Hsource_wf Htarget_concrete
      Hdomain IHdomain Hcodomain IHcodomain.
    constructor.
    + exact IHdomain.
    + constructor.
      * apply effect_constraint_fragment.
      * exact IHcodomain.
  - intros source_components target_components components_constraint
      Hcomponents IHcomponents. exact IHcomponents.
  - intros source target Hshape. constructor.
  - constructor.
  - intros source source_tail target target_tail head_constraint
      tail_constraint Hhead IHhead Htail IHtail.
    constructor; assumption.
  - intros target target_tail. constructor.
  - intros source source_tail. constructor.
Qed.

(** Public separability result for one [SubTyC] derivation. *)
Theorem subtype_constraint_fragment :
  forall source target C,
    subtype_constraint source target C ->
    compatibility_fragment C.
Proof.
  intros source target C Hconstraint.
  apply (proj1 subtype_constraint_fragment_mut source target C Hconstraint).
Qed.

(** Mutual exactness of structural type compatibility and its product-list
    helper.  A satisfying assignment makes [SubTyC(source,target)] hold exactly
    when the instantiated source is a concrete subtype of the instantiated
    target. *)
Lemma subtype_constraint_exact_mut :
  (forall source target C,
      subtype_constraint source target C ->
      forall sigma,
        assignment_wf sigma ->
        (models sigma C <->
         subtype (instantiate_ty sigma source) (instantiate_ty sigma target))) /\
  (forall sources targets C,
      subtype_constraint_list sources targets C ->
      forall sigma,
        assignment_wf sigma ->
        (models sigma C <->
         Forall2
           subtype
           (map (instantiate_ty sigma) sources)
           (map (instantiate_ty sigma) targets))).
Proof.
  apply subtype_constraint_mutind.
  - intros sigma Hsigma. unfold models. simpl. split.
    + intros _. constructor.
    + intros _. split; [exact Hsigma | exact I].
  - intros sigma Hsigma. unfold models. simpl. split.
    + intros _. constructor.
    + intros _. split; [exact Hsigma | exact I].
  - intros source_domain source_latent source_codomain
      target_domain target_latent target_codomain concrete_target_latent
      domain_constraint codomain_constraint Hsource_wf Htarget_concrete
      Hdomain IHdomain Hcodomain IHcodomain sigma Hsigma.
    simpl.
    rewrite (concrete_symbolic_effect_instantiates
      sigma target_latent concrete_target_latent Htarget_concrete).
    split.
    + intro Hmodels.
      apply (proj1 (models_and_iff sigma domain_constraint
        (CAnd (effect_constraint source_latent concrete_target_latent)
          codomain_constraint) Hsigma)) in Hmodels.
      destruct Hmodels as [Hmodels_domain Hmodels_rest].
      apply (proj1 (models_and_iff sigma
        (effect_constraint source_latent concrete_target_latent)
        codomain_constraint Hsigma)) in Hmodels_rest.
      destruct Hmodels_rest as [Hmodels_effect Hmodels_codomain].
      apply SubArrow.
      * apply (proj1 (IHdomain sigma Hsigma)). exact Hmodels_domain.
      * eapply effect_le_trans.
        -- apply (proj1 (effect_constraint_exact
             sigma source_latent concrete_target_latent
             Hsigma Hsource_wf)).
           exact Hmodels_effect.
        -- apply le_normalize.
      * apply (proj1 (IHcodomain sigma Hsigma)). exact Hmodels_codomain.
    + intro Hsubtype. inversion Hsubtype; subst.
      apply (proj2 (models_and_iff sigma domain_constraint
        (CAnd (effect_constraint source_latent concrete_target_latent)
          codomain_constraint) Hsigma)).
      split.
      * apply (proj2 (IHdomain sigma Hsigma)). assumption.
      * apply (proj2 (models_and_iff sigma
          (effect_constraint source_latent concrete_target_latent)
          codomain_constraint Hsigma)).
        split.
        -- apply (proj2 (effect_constraint_exact
             sigma source_latent concrete_target_latent
             Hsigma Hsource_wf)).
           eapply effect_le_trans.
           ++ eassumption.
           ++ apply normalize_le.
        -- apply (proj2 (IHcodomain sigma Hsigma)). assumption.
  - intros source_components target_components components_constraint
      Hcomponents IHcomponents sigma Hsigma. simpl. split.
    + intro Hmodels. apply SubProduct.
      apply (proj1 (IHcomponents sigma Hsigma)). exact Hmodels.
    + intro Hsubtype. inversion Hsubtype; subst.
      apply (proj2 (IHcomponents sigma Hsigma)). assumption.
  - intros source target Hshape sigma Hsigma. unfold models. simpl. split.
    + intros [_ Hfalse]. contradiction.
    + intro Hsubtype. exfalso.
      eapply different_symbolic_shapes_not_subtype; eauto.
  - intros sigma Hsigma. unfold models. simpl. split.
    + intros _. constructor.
    + intros _. split; [exact Hsigma | exact I].
  - intros source source_tail target target_tail head_constraint
      tail_constraint Hhead IHhead Htail IHtail sigma Hsigma. simpl.
    rewrite (models_and_iff sigma head_constraint tail_constraint Hsigma).
    rewrite (IHhead sigma Hsigma).
    rewrite (IHtail sigma Hsigma). split.
    + intros [Hhead_subtype Htail_subtypes]. constructor; assumption.
    + intro Hsubtypes. inversion Hsubtypes; subst. split; assumption.
  - intros target target_tail sigma Hsigma. unfold models. simpl. split.
    + intros [_ Hfalse]. contradiction.
    + intro Hsubtypes. inversion Hsubtypes.
  - intros source source_tail sigma Hsigma. unfold models. simpl. split.
    + intros [_ Hfalse]. contradiction.
    + intro Hsubtypes. inversion Hsubtypes.
Qed.

(** Exactness theorem corresponding to the paper's symbolic type
    compatibility lemma. *)
Theorem subtype_constraint_exact :
  forall sigma source target C,
    assignment_wf sigma ->
    subtype_constraint source target C ->
    (models sigma C <->
     subtype (instantiate_ty sigma source) (instantiate_ty sigma target)).
Proof.
  intros sigma source target C Hsigma Hconstraint.
  apply (proj1 subtype_constraint_exact_mut
    source target C Hconstraint sigma Hsigma).
Qed.
