(** Completeness of symbolic size inference relative to algorithmic checking.

    The paper treats effects as sets.  The executable development represents
    them as lists, so the completeness result is stated modulo
    [type_effect_equiv] and [effect_equiv].  This file lifts that semantic
    equality to contexts and makes every representation-independence step
    explicit. *)

From Stdlib Require Import Arith Lia List QArith.

From BandwidthTimeout Require Import Effects Normalization Bandwidth Syntax
  Typing SizeInference Symbolic Compatibility Merging AlgorithmicTyping
  RootConstraints Inference.

Import ListNotations.
Open Scope Q_scope.

(** Semantic type equivalence is reflexive. *)
Lemma type_effect_equiv_refl :
  forall T,
    type_effect_equiv T T.
Proof.
  fix IH 1. intro T. destruct T as [| |domain latent codomain|components].
  - constructor.
  - constructor.
  - constructor.
    + apply IH.
    + apply effect_equiv_refl.
    + apply IH.
  - constructor. induction components as [|head tail IHtail].
    + constructor.
    + constructor.
      * apply IH.
      * exact IHtail.
Qed.

(** Semantic type equivalence is symmetric. *)
Lemma type_effect_equiv_sym :
  forall left right,
    type_effect_equiv left right ->
    type_effect_equiv right left.
Proof.
  intro left. pattern left.
  apply (well_founded_induction_type
    (well_founded_ltof ty type_measure)).
  clear left. intros left IH right Hequiv.
  destruct left as [| |left_domain left_latent left_codomain|left_components];
    inversion Hequiv; subst.
  - constructor.
  - constructor.
  - constructor.
    + apply (IH left_domain); [unfold ltof; simpl; lia | assumption].
    + apply effect_equiv_sym. assumption.
    + apply (IH left_codomain); [unfold ltof; simpl; lia | assumption].
  - constructor.
    match goal with
    | Hcomponents : Forall2 type_effect_equiv left_components _ |- _ =>
        assert (Hreverse :
          forall sources targets,
            Forall2 type_effect_equiv sources targets ->
            (forall source, In source sources ->
              ltof ty type_measure source (Syntax.TyProduct left_components)) ->
            Forall2 type_effect_equiv targets sources) by
          (intros sources targets Hrelations;
           induction Hrelations; intro Hsmall; constructor;
           [apply (IH x); [apply Hsmall; left; reflexivity | assumption]
           | apply IHHrelations; intros source Hin; apply Hsmall; right;
             assumption]);
        apply Hreverse; [exact Hcomponents |];
        intros source Hin; apply type_measure_product_member; exact Hin
    end.
Qed.

(** Semantic type equivalence is transitive.  Structural recursion on the
    middle type supplies the corresponding component in product types. *)
Lemma type_effect_equiv_trans :
  forall middle left right,
    type_effect_equiv left middle ->
    type_effect_equiv middle right ->
    type_effect_equiv left right.
Proof.
  intro middle. pattern middle.
  apply (well_founded_induction_type
    (well_founded_ltof ty type_measure)).
  clear middle. intros middle IH left right Hleft Hright.
  destruct middle as
    [| |middle_domain middle_latent middle_codomain|middle_components];
    inversion Hleft; subst; inversion Hright; subst.
  - constructor.
  - constructor.
  - constructor.
    + apply (IH middle_domain).
      * unfold ltof; simpl; lia.
      * eassumption.
      * eassumption.
    + eapply effect_equiv_trans; eauto.
    + apply (IH middle_codomain).
      * unfold ltof; simpl; lia.
      * eassumption.
      * eassumption.
  - constructor.
    assert (Hcompose :
      forall middles lefts rights,
        Forall2 type_effect_equiv lefts middles ->
        Forall2 type_effect_equiv middles rights ->
        (forall component, In component middles ->
          ltof ty type_measure component
            (Syntax.TyProduct middle_components)) ->
        Forall2 type_effect_equiv lefts rights).
    { intros middles lefts rights Hlefts.
      revert rights. induction Hlefts;
        intros rights Hrights Hsmall; inversion Hrights; subst; constructor.
      - apply (IH y).
        + apply Hsmall. left. reflexivity.
        + assumption.
        + assumption.
      - eapply IHHlefts.
        + eassumption.
        + intros component Hin. apply Hsmall. right. assumption. }
    eapply Hcompose.
    + exact H1.
    + exact H0.
    + intros component Hin. apply type_measure_product_member. exact Hin.
Qed.

(** A concrete context represents a symbolic context under [sigma] when
    corresponding types are semantically equivalent. *)
Definition instantiated_context_equiv
    (sigma : size_assignment)
    (symbolic : symbolic_context)
    (concrete : context) : Prop :=
  Forall2
    (fun symbolic_ty concrete_ty =>
      type_effect_equiv (instantiate_ty sigma symbolic_ty) concrete_ty)
    symbolic concrete.

(** Literal context instantiation is a special case of context equivalence. *)
Lemma instantiate_context_equiv_refl :
  forall sigma Gamma,
    instantiated_context_equiv sigma Gamma (instantiate_context sigma Gamma).
Proof.
  intros sigma Gamma. induction Gamma as [|head tail IH]; simpl; constructor.
  - apply type_effect_equiv_refl.
  - exact IH.
Qed.

(** Equivalent contexts preserve de Bruijn lookup, returning the symbolic type
    stored at the same index. *)
Lemma instantiated_context_lookup_reverse :
  forall sigma symbolic concrete index concrete_ty,
    instantiated_context_equiv sigma symbolic concrete ->
    lookup concrete index concrete_ty ->
    exists symbolic_ty,
      symbolic_lookup symbolic index symbolic_ty /\
      type_effect_equiv
        (instantiate_ty sigma symbolic_ty) concrete_ty.
Proof.
  intros sigma symbolic concrete index concrete_ty Hequiv.
  revert index concrete_ty. induction Hequiv;
    intros index concrete_ty Hlookup.
  - destruct index; inversion Hlookup.
  - destruct index as [|index']; simpl in Hlookup.
    + inversion Hlookup; subst. exists x. split; [reflexivity | assumption].
    + destruct (IHHequiv _ _ Hlookup) as [symbolic_ty [Hsymbolic Htype]].
      exists symbolic_ty. split; assumption.
Qed.

(** Context types must remain admissible as results of symbolic inference.
    Programmer annotations and previously inferred let-bound types establish
    this invariant. *)
Definition symbolic_context_join_ready (Gamma : symbolic_context) : Prop :=
  Forall symbolic_join_ready Gamma.

Lemma symbolic_lookup_join_ready :
  forall Gamma index T,
    symbolic_context_join_ready Gamma ->
    symbolic_lookup Gamma index T ->
    symbolic_join_ready T.
Proof.
  intros Gamma. induction Gamma as [|head tail IH];
    intros index T Hready Hlookup.
  - destruct index; inversion Hlookup.
  - inversion Hready; subst. destruct index as [|index']; simpl in Hlookup.
    + inversion Hlookup; subst. assumption.
    + eapply IH; eauto.
Qed.

(** The global representable-size premise from the paper. *)
Definition assignment_within_bound
    (M : Q) (sigma : size_assignment) : Prop :=
  forall variable, sigma variable <= M.

(** A structural measure for induction through tuple component lists. *)
Fixpoint symbolic_expr_measure (e : symbolic_expr) : nat :=
  match e with
  | SEVar _ | SEUnit | SENat _ | SEDownload _ _ => 1
  | SELambda _ body => S (symbolic_expr_measure body)
  | SETuple components | SEParallel components =>
      S (fold_right
        (fun component total =>
          (symbolic_expr_measure component + total)%nat)
        O components)
  | SEApp function argument | SELet function argument =>
      S ((symbolic_expr_measure function + symbolic_expr_measure argument)%nat)
  | SEIfZero guard zero_branch nonzero_branch =>
      S ((symbolic_expr_measure guard +
        symbolic_expr_measure zero_branch +
        symbolic_expr_measure nonzero_branch)%nat)
  end.

Lemma symbolic_expr_measure_member :
  forall component components,
    In component components ->
    (symbolic_expr_measure component <
      symbolic_expr_measure (SETuple components))%nat.
Proof.
  intros component components Hin. simpl.
  induction components as [|head tail IH]; simpl in *.
  - contradiction.
  - destruct Hin as [-> | Hin].
    + lia.
    + specialize (IH Hin). lia.
Qed.

(** Instantiation cannot turn a non-value symbolic expression into a concrete
    value. *)
Lemma instantiate_value_reverse :
  forall sigma e,
    value (instantiate_expr sigma e) ->
    symbolic_value e.
Proof.
  intros sigma e. pattern e.
  apply (well_founded_induction_type
    (well_founded_ltof symbolic_expr symbolic_expr_measure)).
  clear e. intros e IH Hvalue. destruct e; simpl in Hvalue;
    inversion Hvalue; subst; try constructor.
  assert (Hreflect :
    forall expressions,
      Forall value (map (instantiate_expr sigma) expressions) ->
      (forall child, In child expressions ->
        ltof symbolic_expr symbolic_expr_measure child (SETuple l)) ->
      Forall symbolic_value expressions).
  { intros expressions Hvalues Hsmall.
    induction expressions as [|head tail IHtail]; inversion Hvalues; subst;
      constructor.
    - apply (IH head); [apply Hsmall; left; reflexivity | assumption].
    - apply IHtail.
      + assumption.
      + intros child Hin. apply Hsmall. right. assumption. }
  apply Hreflect.
  - assumption.
  - intros child Hin. unfold ltof. eapply symbolic_expr_measure_member. exact Hin.
Qed.

(** Pointwise form of value reflection for tuple components. *)
Lemma instantiate_values_reverse :
  forall sigma expressions,
    Forall value (map (instantiate_expr sigma) expressions) ->
    Forall symbolic_value expressions.
Proof.
  intros sigma expressions Hvalues. induction expressions as [|head tail IH];
    inversion Hvalues; subst; constructor.
  - eapply instantiate_value_reverse. eassumption.
  - apply IH. assumption.
Qed.

(** Concrete joins and meets are insensitive to the list representation of
    latent effects.  This transports an algorithmic merge to the semantically
    equivalent instantiated branch types reconstructed by induction. *)
Lemma concrete_type_merge_respects_equiv_mut :
  (forall left right result,
      concrete_type_join left right result ->
      forall left' right',
        type_effect_equiv left' left ->
        type_effect_equiv right' right ->
        exists result',
          concrete_type_join left' right' result' /\
          type_effect_equiv result' result) /\
  (forall left right result,
      concrete_type_meet left right result ->
      forall left' right',
        type_effect_equiv left' left ->
        type_effect_equiv right' right ->
        exists result',
          concrete_type_meet left' right' result' /\
          type_effect_equiv result' result) /\
  (forall left right result,
      concrete_type_join_list left right result ->
      forall left' right',
        Forall2 type_effect_equiv left' left ->
        Forall2 type_effect_equiv right' right ->
        exists result',
          concrete_type_join_list left' right' result' /\
          Forall2 type_effect_equiv result' result) /\
  (forall left right result,
      concrete_type_meet_list left right result ->
      forall left' right',
        Forall2 type_effect_equiv left' left ->
        Forall2 type_effect_equiv right' right ->
        exists result',
          concrete_type_meet_list left' right' result' /\
          Forall2 type_effect_equiv result' result).
Proof.
  apply concrete_type_merge_mutind.
  - intros left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    exists Syntax.TyUnit. split; constructor.
  - intros left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    exists Syntax.TyNat. split; constructor.
  - intros left_domain left_latent left_codomain
      right_domain right_latent right_codomain result_domain result_codomain
      Hdomain IHdomain Hcodomain IHcodomain left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    destruct (IHdomain _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_domain' [Hdomain' Hequiv_domain]].
    destruct (IHcodomain _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_codomain' [Hcodomain' Hequiv_codomain]].
    eexists (Syntax.TyArrow result_domain'
      (sequential_effect left_latent0 left_latent1) result_codomain').
    split.
    + constructor; assumption.
    + constructor.
      * exact Hequiv_domain.
      * apply sequential_effect_respects_equiv; assumption.
      * exact Hequiv_codomain.
  - intros left_components right_components result_components Hcomponents
      IHcomponents left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    destruct (IHcomponents _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_components' [Hcomponents' Hequiv_components]].
    exists (Syntax.TyProduct result_components'). split; constructor; assumption.
  - intros left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    exists Syntax.TyUnit. split; constructor.
  - intros left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    exists Syntax.TyNat. split; constructor.
  - intros left_domain left_latent left_codomain
      right_domain right_latent right_codomain result_domain result_codomain
      Hdomain IHdomain Hcodomain IHcodomain left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    destruct (IHdomain _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_domain' [Hdomain' Hequiv_domain]].
    destruct (IHcodomain _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_codomain' [Hcodomain' Hequiv_codomain]].
    eexists (Syntax.TyArrow result_domain'
      (effect_meet left_latent0 left_latent1) result_codomain').
    split.
    + constructor; assumption.
    + constructor.
      * exact Hequiv_domain.
      * apply effect_meet_respects_equiv; assumption.
      * exact Hequiv_codomain.
  - intros left_components right_components result_components Hcomponents
      IHcomponents left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    destruct (IHcomponents _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_components' [Hcomponents' Hequiv_components]].
    exists (Syntax.TyProduct result_components'). split; constructor; assumption.
  - intros left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    exists []. split; constructor.
  - intros left left_tail right right_tail result result_tail Hhead IHhead
      Htail IHtail left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    destruct (IHhead _ _ ltac:(eassumption) ltac:(eassumption))
      as [result' [Hresult' Hequiv_result]].
    destruct (IHtail _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_tail' [Hresult_tail' Hequiv_tail]].
    exists (result' :: result_tail'). split; constructor; assumption.
  - intros left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    exists []. split; constructor.
  - intros left left_tail right right_tail result result_tail Hhead IHhead
      Htail IHtail left' right' Hleft Hright.
    inversion Hleft; subst. inversion Hright; subst.
    destruct (IHhead _ _ ltac:(eassumption) ltac:(eassumption))
      as [result' [Hresult' Hequiv_result]].
    destruct (IHtail _ _ ltac:(eassumption) ltac:(eassumption))
      as [result_tail' [Hresult_tail' Hequiv_tail]].
    exists (result' :: result_tail'). split; constructor; assumption.
Qed.

(** Public congruence theorem for concrete joins. *)
Lemma concrete_type_join_respects_equiv :
  forall left right result left' right',
    concrete_type_join left right result ->
    type_effect_equiv left' left ->
    type_effect_equiv right' right ->
    exists result',
      concrete_type_join left' right' result' /\
      type_effect_equiv result' result.
Proof.
  intros. eapply (proj1 concrete_type_merge_respects_equiv_mut); eauto.
Qed.

(** Equivalent types have the same structural measure; latent effects do not
    contribute to [type_measure]. *)
Lemma type_effect_equiv_measure :
  forall left right,
    type_effect_equiv left right ->
    type_measure left = type_measure right.
Proof.
  intro left. pattern left.
  apply (well_founded_induction_type
    (well_founded_ltof ty type_measure)).
  clear left. intros left IH right Hequiv.
  destruct left as [| |left_domain left_latent left_codomain|left_components];
    inversion Hequiv; subst; simpl.
  - reflexivity.
  - reflexivity.
  - assert (Hdomain_measure :
      ltof ty type_measure left_domain
        (Syntax.TyArrow left_domain left_latent left_codomain))
      by (unfold ltof; simpl; lia).
    assert (Hcodomain_measure :
      ltof ty type_measure left_codomain
        (Syntax.TyArrow left_domain left_latent left_codomain))
      by (unfold ltof; simpl; lia).
    rewrite (IH left_domain Hdomain_measure right_domain H2).
    rewrite (IH left_codomain Hcodomain_measure right_codomain H5).
    reflexivity.
  - f_equal.
    assert (Hsum :
      forall sources targets,
        Forall2 type_effect_equiv sources targets ->
        (forall source, In source sources ->
          ltof ty type_measure source (Syntax.TyProduct left_components)) ->
        fold_right
          (fun component total => (type_measure component + total)%nat)
          O sources =
        fold_right
          (fun component total => (type_measure component + total)%nat)
          O targets).
    { intros sources targets Hrelations Hsmall.
      induction Hrelations; simpl.
      - reflexivity.
      - rewrite (IH x ltac:(apply Hsmall; left; reflexivity) y H).
        rewrite (IHHrelations
          (fun source Hin => Hsmall source (or_intror Hin))).
        reflexivity. }
    eapply Hsum.
    + eassumption.
    + intros source Hin. apply type_measure_product_member. exact Hin.
Qed.

(** Semantically equivalent types are interchangeable by subtyping. *)
Lemma type_effect_equiv_implies_subtype :
  forall left right,
    type_effect_equiv left right ->
    subtype left right.
Proof.
  intro left. pattern left.
  apply (well_founded_induction_type
    (well_founded_ltof ty type_measure)).
  clear left. intros left IH right Hequiv.
  destruct left as [| |left_domain left_latent left_codomain|left_components];
    inversion Hequiv; subst.
  - constructor.
  - constructor.
  - apply SubArrow.
    + apply (IH right_domain).
      * unfold ltof.
        pose proof (type_effect_equiv_measure _ _ H2). simpl in *. lia.
      * apply type_effect_equiv_sym. exact H2.
    + exact (proj1 H4).
    + apply (IH left_codomain).
      * unfold ltof. simpl. lia.
      * exact H5.
  - apply SubProduct.
    assert (Hsubtypes :
      forall sources targets,
        Forall2 type_effect_equiv sources targets ->
        (forall source, In source sources ->
          ltof ty type_measure source (Syntax.TyProduct left_components)) ->
        Forall2 subtype sources targets).
    { intros sources targets Hrelations Hsmall.
      induction Hrelations; constructor.
      - apply (IH x).
        + apply Hsmall. left. reflexivity.
        + assumption.
      - apply IHHrelations. intros source Hin. apply Hsmall. right. assumption. }
    eapply Hsubtypes.
    + eassumption.
    + intros source Hin. apply type_measure_product_member. exact Hin.
Qed.

(** Structural subtyping is transitive. *)
Lemma subtype_trans :
  forall middle left right,
    subtype left middle ->
    subtype middle right ->
    subtype left right.
Proof.
  intro middle. pattern middle.
  apply (well_founded_induction_type
    (well_founded_ltof ty type_measure)).
  clear middle. intros middle IH left right Hleft Hright.
  destruct middle as
    [| |middle_domain middle_latent middle_codomain|middle_components];
    inversion Hleft; subst; inversion Hright; subst.
  - constructor.
  - constructor.
  - apply SubArrow.
    + apply (IH middle_domain); try assumption. unfold ltof. simpl. lia.
    + eapply effect_le_trans; eassumption.
    + apply (IH middle_codomain); try assumption. unfold ltof. simpl. lia.
  - apply SubProduct.
    assert (Hcompose :
      forall middles lefts rights,
        Forall2 subtype lefts middles ->
        Forall2 subtype middles rights ->
        (forall component, In component middles ->
          ltof ty type_measure component
            (Syntax.TyProduct middle_components)) ->
        Forall2 subtype lefts rights).
    { intros middles lefts rights Hlefts.
      revert rights. induction Hlefts;
        intros rights Hrights Hsmall; inversion Hrights; subst; constructor.
      - apply (IH y).
        + apply Hsmall. left. reflexivity.
        + assumption.
        + assumption.
      - eapply IHHlefts.
        + eassumption.
        + intros component Hin. apply Hsmall. right. assumption. }
    eapply Hcompose.
    + eassumption.
    + eassumption.
    + intros component Hin. apply type_measure_product_member. exact Hin.
Qed.

(** Subtyping is preserved when either endpoint is replaced by a semantically
    equivalent type. *)
Lemma subtype_respects_type_effect_equiv :
  forall source target source' target',
    type_effect_equiv source' source ->
    type_effect_equiv target' target ->
    subtype source target ->
    subtype source' target'.
Proof.
  intros source target source' target' Hsource Htarget Hsubtype.
  eapply subtype_trans.
  - apply type_effect_equiv_implies_subtype. exact Hsource.
  - eapply subtype_trans.
    + exact Hsubtype.
    + apply type_effect_equiv_implies_subtype.
      apply type_effect_equiv_sym. exact Htarget.
Qed.

(** Readiness plus ordinary well-formedness ensures that the structural
    subtype-constraint generator is defined.  The four statements follow the
    same positive/negative polarity switch as arrow subtyping. *)
Lemma subtype_constraint_exists_mut :
  (forall source (Hsource_ready : symbolic_join_ready source),
      symbolic_ty_wf source ->
      forall target,
        symbolic_meet_ready target ->
        symbolic_ty_wf target ->
        exists C, subtype_constraint source target C) /\
  (forall target (Htarget_ready : symbolic_meet_ready target),
      symbolic_ty_wf target ->
      forall source,
        symbolic_join_ready source ->
        symbolic_ty_wf source ->
        exists C, subtype_constraint source target C) /\
  (forall sources (Hsources_ready : symbolic_join_list_ready sources),
      Forall symbolic_ty_wf sources ->
      forall targets,
        symbolic_meet_list_ready targets ->
        Forall symbolic_ty_wf targets ->
        exists C, subtype_constraint_list sources targets C) /\
  (forall targets (Htargets_ready : symbolic_meet_list_ready targets),
      Forall symbolic_ty_wf targets ->
      forall sources,
        symbolic_join_list_ready sources ->
        Forall symbolic_ty_wf sources ->
        exists C, subtype_constraint_list sources targets C).
Proof.
  apply symbolic_merge_ready_mutind.
  - intros Hsource_wf target Htarget_ready Htarget_wf.
    destruct target; inversion Htarget_ready; subst.
    + exists CTop. constructor.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
  - intros Hsource_wf target Htarget_ready Htarget_wf.
    destruct target; inversion Htarget_ready; subst.
    + exists CBottom. constructor. reflexivity.
    + exists CTop. constructor.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
  - intros source_domain source_latent source_codomain Hdomain IHdomain
      Hcodomain IHcodomain Hsource_wf target Htarget_ready Htarget_wf.
    destruct target as
      [| |target_domain target_latent target_codomain|target_components].
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + inversion Htarget_ready; subst. inversion Hsource_wf; subst.
      inversion Htarget_wf; subst.
      destruct (IHdomain ltac:(assumption) target_domain
        ltac:(assumption) ltac:(assumption)) as [Cdomain Hconstraint_domain].
      destruct (IHcodomain ltac:(assumption) target_codomain
        ltac:(assumption) ltac:(assumption)) as [Ccodomain Hconstraint_codomain].
      eexists. econstructor; eauto.
    + exists CBottom. constructor. reflexivity.
  - intros source_components Hcomponents IHcomponents Hsource_wf target
      Htarget_ready Htarget_wf.
    destruct target as
      [| |target_domain target_latent target_codomain|target_components].
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + inversion Htarget_ready; subst. inversion Hsource_wf; subst.
      inversion Htarget_wf; subst.
      destruct (IHcomponents ltac:(assumption) target_components
        ltac:(assumption) ltac:(assumption)) as [C Hconstraint].
      exists C. constructor. exact Hconstraint.
  - intros Htarget_wf source Hsource_ready Hsource_wf.
    destruct source; inversion Hsource_ready; subst.
    + exists CTop. constructor.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
  - intros Htarget_wf source Hsource_ready Hsource_wf.
    destruct source; inversion Hsource_ready; subst.
    + exists CBottom. constructor. reflexivity.
    + exists CTop. constructor.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
  - intros target_domain target_latent target_codomain concrete_target_latent
      Hdomain IHdomain Htarget_latent Hcodomain IHcodomain Htarget_wf source
      Hsource_ready Hsource_wf.
    destruct source as
      [| |source_domain source_latent source_codomain|source_components].
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + inversion Hsource_ready; subst. inversion Hsource_wf; subst.
      inversion Htarget_wf; subst.
      destruct (IHdomain ltac:(assumption) source_domain
        ltac:(assumption) ltac:(assumption)) as [Cdomain Hconstraint_domain].
      destruct (IHcodomain ltac:(assumption) source_codomain
        ltac:(assumption) ltac:(assumption)) as [Ccodomain Hconstraint_codomain].
      eexists. econstructor; eauto.
    + exists CBottom. constructor. reflexivity.
  - intros target_components Hcomponents IHcomponents Htarget_wf source
      Hsource_ready Hsource_wf.
    destruct source as
      [| |source_domain source_latent source_codomain|source_components].
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + exists CBottom. constructor. reflexivity.
    + inversion Hsource_ready; subst. inversion Hsource_wf; subst.
      inversion Htarget_wf; subst.
      destruct (IHcomponents ltac:(assumption) source_components
        ltac:(assumption) ltac:(assumption)) as [C Hconstraint].
      exists C. constructor. exact Hconstraint.
  - intros Hsources_wf targets Htargets_ready Htargets_wf.
    destruct targets.
    + exists CTop. constructor.
    + exists CBottom. constructor.
  - intros source source_tail Hsource IHsource Htail IHtail Hsources_wf
      targets Htargets_ready Htargets_wf.
    destruct targets as [|target target_tail].
    + exists CBottom. constructor.
    + inversion Htargets_ready; subst. inversion Hsources_wf; subst.
      inversion Htargets_wf; subst.
      destruct (IHsource ltac:(assumption) target ltac:(assumption)
        ltac:(assumption)) as [Chead Hhead].
      destruct (IHtail ltac:(assumption) target_tail ltac:(assumption)
        ltac:(assumption)) as [Ctail Htail_constraint].
      exists (CAnd Chead Ctail). constructor; assumption.
  - intros Htargets_wf sources Hsources_ready Hsources_wf.
    destruct sources.
    + exists CTop. constructor.
    + exists CBottom. constructor.
  - intros target target_tail Htarget IHtarget Htail IHtail Htargets_wf
      sources Hsources_ready Hsources_wf.
    destruct sources as [|source source_tail].
    + exists CBottom. constructor.
    + inversion Hsources_ready; subst. inversion Hsources_wf; subst.
      inversion Htargets_wf; subst.
      destruct (IHtarget ltac:(assumption) source ltac:(assumption)
        ltac:(assumption)) as [Chead Hhead].
      destruct (IHtail ltac:(assumption) source_tail ltac:(assumption)
        ltac:(assumption)) as [Ctail Htail_constraint].
      exists (CAnd Chead Ctail). constructor; assumption.
Qed.

(** A concrete subtype check between semantically corresponding instances can
    always be reconstructed as a modeled symbolic subtype constraint. *)
Theorem subtype_constraint_reverse_complete :
  forall sigma source target concrete_source concrete_target,
    symbolic_join_ready source ->
    symbolic_meet_ready target ->
    symbolic_ty_wf source ->
    symbolic_ty_wf target ->
    type_effect_equiv (instantiate_ty sigma source) concrete_source ->
    type_effect_equiv (instantiate_ty sigma target) concrete_target ->
    subtype concrete_source concrete_target ->
    exists C,
      subtype_constraint source target C /\
      models sigma C.
Proof.
  intros sigma source target concrete_source concrete_target Hsource_ready
    Htarget_ready Hsource_wf Htarget_wf Hsource_equiv Htarget_equiv
    Hsubtype.
  destruct (proj1 subtype_constraint_exists_mut source Hsource_ready Hsource_wf
    target Htarget_ready Htarget_wf) as [C Hconstraint].
  exists C. split; [exact Hconstraint |].
  apply (proj2 (subtype_constraint_exact sigma source target C Hconstraint)).
  eapply subtype_respects_type_effect_equiv; eauto.
Qed.

(** A convenient constructor for modeled conjunctions. *)
Lemma models_and_intro :
  forall sigma C1 C2,
    models sigma C1 ->
    models sigma C2 ->
    models sigma (CAnd C1 C2).
Proof.
  intros sigma C1 C2 H1 H2.
  apply (proj2 (models_and_iff sigma C1 C2)). split; assumption.
Qed.

(** Symbolic values inferred by the syntax-directed judgment have no
    immediate effect. *)
Lemma inferred_symbolic_value_effect_empty :
  forall M Gamma e T Phi C,
    size_infers M Gamma e T Phi C ->
    symbolic_value e ->
    Phi = [].
Proof.
  intros M Gamma e T Phi C Hinfer Hvalue.
  inversion Hinfer; subst; inversion Hvalue; reflexivity.
Qed.

(** Pointwise version used by the tuple rule. *)
Lemma inferred_symbolic_values_effects_empty :
  forall M Gamma expressions types effects C,
    size_infers_list M Gamma expressions types effects C ->
    Forall symbolic_value expressions ->
    effects = repeat [] (length expressions).
Proof.
  intros M Gamma expressions types effects C Hinfer.
  induction Hinfer; intro Hvalues; inversion Hvalues; subst; simpl.
  - reflexivity.
  - rewrite (inferred_symbolic_value_effect_empty _ _ _ _ _ _ H H2).
    rewrite IHHinfer by assumption. reflexivity.
Qed.

(** Exact completeness of expression/list constraint generation relative to
    the concrete syntax-directed checker.  "Exact" here means semantic
    equality of list-backed effects and of latent effects inside types. *)
Lemma constraint_generation_complete_mut :
  forall M sigma,
    assignment_within_bound M sigma ->
  (forall concrete_context concrete_expr concrete_ty concrete_effect,
      algorithmic_has_type
        concrete_context concrete_expr concrete_ty concrete_effect ->
      forall Gamma e,
        instantiated_context_equiv sigma Gamma concrete_context ->
        symbolic_context_wf Gamma ->
        symbolic_context_join_ready Gamma ->
        concrete_expr = instantiate_expr sigma e ->
        exists T Phi C,
          size_infers M Gamma e T Phi C /\
          models sigma C /\
          type_effect_equiv (instantiate_ty sigma T) concrete_ty /\
          instantiate_effect sigma Phi ≈ concrete_effect /\
          symbolic_join_ready T) /\
  (forall concrete_context concrete_expressions concrete_types
          concrete_effects,
      algorithmic_expressions_have_types concrete_context
        concrete_expressions concrete_types concrete_effects ->
      forall Gamma expressions,
        instantiated_context_equiv sigma Gamma concrete_context ->
        symbolic_context_wf Gamma ->
        symbolic_context_join_ready Gamma ->
        concrete_expressions = map (instantiate_expr sigma) expressions ->
        exists types effects C,
          size_infers_list M Gamma expressions types effects C /\
          models sigma C /\
          Forall2 type_effect_equiv
            (map (instantiate_ty sigma) types) concrete_types /\
          Forall2 effect_equiv
            (map (instantiate_effect sigma) effects) concrete_effects /\
          symbolic_join_list_ready types).
Proof.
  intros M sigma Hbound.
  apply algorithmic_typing_mutind.
  - intros concrete_context index concrete_ty Hlookup Gamma e Hcontext
      Hcontext_wf Hcontext_ready Heq.
    destruct e; inversion Heq; subst.
    destruct (instantiated_context_lookup_reverse sigma Gamma concrete_context
      n concrete_ty Hcontext Hlookup) as [T [Hlookup_symbolic Hequiv]].
    exists T, [], CTop. split.
    + constructor. exact Hlookup_symbolic.
    + split.
      * exact I.
      * split.
        -- exact Hequiv.
        -- split.
           ++ simpl. apply effect_equiv_refl.
           ++ eapply symbolic_lookup_join_ready; eauto.
  - intros concrete_context Gamma e Hcontext Hcontext_wf Hcontext_ready Heq.
    destruct e; inversion Heq; subst.
    exists STyUnit, [], CTop. split.
    + constructor.
    + split.
      * exact I.
      * split; [constructor |]. split; [apply effect_equiv_refl | constructor].
  - intros concrete_context n Gamma e Hcontext Hcontext_wf Hcontext_ready Heq.
    destruct e; inversion Heq; subst.
    exists STyNat, [], CTop. split.
    + constructor.
    + split.
      * exact I.
      * split; [constructor |]. split; [apply effect_equiv_refl | constructor].
  - intros concrete_context concrete_components concrete_component_types
      Hvalues Hcomponents IHcomponents Gamma e Hcontext Hcontext_wf
      Hcontext_ready Heq.
    destruct e as
      [| | | |symbolic_components| | | | |]; inversion Heq; subst.
    destruct (IHcomponents Gamma symbolic_components Hcontext Hcontext_wf
      Hcontext_ready eq_refl)
      as [component_types [component_effects [C
        [Hinfer [Hmodels [Htypes [Heffects Hready]]]]]]].
    pose proof (instantiate_values_reverse sigma symbolic_components Hvalues)
      as Hsymbolic_values.
    pose proof (inferred_symbolic_values_effects_empty M Gamma
      symbolic_components component_types component_effects C Hinfer
      Hsymbolic_values) as Hempty.
    subst component_effects.
    exists (STyProduct component_types), [], C. split.
    + apply SIInferTuple.
      * exact Hsymbolic_values.
      * exact Hinfer.
    + split.
      * exact Hmodels.
      * split.
        -- simpl. constructor. exact Htypes.
        -- split.
           ++ simpl. apply effect_equiv_refl.
           ++ constructor. exact Hready.
  - intros concrete_context size timeout Hparameters Gamma e Hcontext
      Hcontext_wf Hcontext_ready Heq.
    destruct e as [index| |n|annotation body|components|function argument|
      bound body|guard zero_branch nonzero_branch|variable symbolic_timeout|
      branches]; inversion Heq; subst.
    exists STyUnit,
      [SymbolicObligation (SRateVariable variable symbolic_timeout) 1],
      (CUpper variable M).
    split.
    + constructor.
    + split.
      * simpl. apply Hbound.
      * split; [constructor |]. split.
        -- simpl. apply effect_equiv_refl.
        -- constructor.
  - intros concrete_context concrete_bound concrete_body concrete_bound_ty
      concrete_body_ty concrete_bound_effect concrete_body_effect Hbound_typing
      IHbound Hbody_typing IHbody Gamma e Hcontext Hcontext_wf Hcontext_ready
      Heq.
    destruct e as [| | | | | |symbolic_bound symbolic_body| | |];
      inversion Heq; subst.
    destruct (IHbound Gamma symbolic_bound Hcontext Hcontext_wf Hcontext_ready
      eq_refl)
      as [bound_ty [bound_effect [bound_constraint
        [Hinfer_bound [Hmodels_bound [Hequiv_bound_ty
          [Hequiv_bound_effect Hready_bound]]]]]]].
    pose proof (proj1 (proj1 (size_inference_wf_mut M)
      Gamma symbolic_bound bound_ty bound_effect bound_constraint Hinfer_bound
      Hcontext_wf)) as Hbound_ty_wf.
    destruct (IHbody (bound_ty :: Gamma) symbolic_body
      ltac:(constructor; assumption) ltac:(constructor; assumption)
      ltac:(constructor; assumption) eq_refl)
      as [body_ty [body_effect [body_constraint
        [Hinfer_body [Hmodels_body [Hequiv_body_ty
          [Hequiv_body_effect Hready_body]]]]]]].
    exists body_ty, (symbolic_join bound_effect body_effect),
      (CAnd bound_constraint body_constraint). split.
    + econstructor; eauto.
    + split.
      * apply models_and_intro; assumption.
      * split.
        -- exact Hequiv_body_ty.
        -- split.
           ++ eapply effect_equiv_trans.
              ** apply instantiate_symbolic_join.
              ** apply sequential_effect_respects_equiv; assumption.
           ++ exact Hready_body.
  - intros concrete_context concrete_guard concrete_zero concrete_nonzero
      concrete_zero_ty concrete_nonzero_ty concrete_result_ty
      concrete_guard_effect concrete_zero_effect concrete_nonzero_effect
      Hguard IHguard Hzero IHzero Hnonzero IHnonzero Hjoin Gamma e Hcontext
      Hcontext_wf Hcontext_ready Heq.
    destruct e as
      [| | | | | | |symbolic_guard symbolic_zero symbolic_nonzero| |];
      inversion Heq; subst.
    destruct (IHguard Gamma symbolic_guard Hcontext Hcontext_wf Hcontext_ready
      eq_refl)
      as [guard_ty [guard_effect [guard_constraint
        [Hinfer_guard [Hmodels_guard [Hequiv_guard_ty
          [Hequiv_guard_effect Hready_guard]]]]]]].
    destruct guard_ty; inversion Hequiv_guard_ty; subst.
    destruct (IHzero Gamma symbolic_zero Hcontext Hcontext_wf Hcontext_ready
      eq_refl)
      as [zero_ty [zero_effect [zero_constraint
        [Hinfer_zero [Hmodels_zero [Hequiv_zero_ty
          [Hequiv_zero_effect Hready_zero]]]]]]].
    destruct (IHnonzero Gamma symbolic_nonzero Hcontext Hcontext_wf
      Hcontext_ready eq_refl)
      as [nonzero_ty [nonzero_effect [nonzero_constraint
        [Hinfer_nonzero [Hmodels_nonzero [Hequiv_nonzero_ty
          [Hequiv_nonzero_effect Hready_nonzero]]]]]]].
    destruct (concrete_type_join_respects_equiv _ _ _ _ _ Hjoin
      Hequiv_zero_ty Hequiv_nonzero_ty)
      as [transported_result [Htransported_join Hequiv_transport]].
    destruct (proj1 symbolic_type_merge_reverse_mut zero_ty Hready_zero
      nonzero_ty sigma transported_result Hready_nonzero
      Htransported_join) as [result_ty [join_constraint
        [Hsymbolic_join [Hmodels_join [Hequiv_result Hready_result]]]]].
    exists result_ty,
      (symbolic_join guard_effect (symbolic_join zero_effect nonzero_effect)),
      (CAnd guard_constraint
        (CAnd zero_constraint (CAnd nonzero_constraint join_constraint))).
    split.
    + econstructor; eauto.
    + split.
      * apply models_and_intro; [exact Hmodels_guard |].
        apply models_and_intro; [exact Hmodels_zero |].
        apply models_and_intro; assumption.
      * split.
        -- eapply type_effect_equiv_trans; eauto.
        -- split.
           ++ eapply effect_equiv_trans.
              ** apply instantiate_symbolic_join.
              ** apply sequential_effect_respects_equiv.
                 --- exact Hequiv_guard_effect.
                 --- eapply effect_equiv_trans.
                     +++ apply instantiate_symbolic_join.
                     +++ apply sequential_effect_respects_equiv; assumption.
           ++ exact Hready_result.
  - intros concrete_context concrete_branches concrete_branch_types
      concrete_branch_effects Hbranches IHbranches Gamma e Hcontext Hcontext_wf
      Hcontext_ready Heq.
    destruct e as [| | | | | | | | |symbolic_branches]; inversion Heq; subst.
    destruct (IHbranches Gamma symbolic_branches Hcontext Hcontext_wf
      Hcontext_ready eq_refl)
      as [branch_types [branch_effects [C
        [Hinfer [Hmodels [Hequiv_types [Hequiv_effects Hready_types]]]]]]].
    exists (STyProduct branch_types),
      (symbolic_parallel_effects branch_effects), C. split.
    + constructor. exact Hinfer.
    + split.
      * exact Hmodels.
      * split.
        -- simpl. constructor. exact Hequiv_types.
        -- split.
           ++ eapply effect_equiv_trans.
              ** apply instantiate_symbolic_parallel_effects.
              ** apply parallel_effects_respects_equiv. exact Hequiv_effects.
           ++ constructor. exact Hready_types.
  - intros concrete_context concrete_parameter_ty concrete_body concrete_result_ty
      concrete_body_effect Hbody IHbody Gamma e Hcontext Hcontext_wf
      Hcontext_ready Heq.
    destruct e as
      [| | |parameter_annotation symbolic_body| | | | | |];
      inversion Heq; subst.
    pose proof (annotation_symbolic_ty_wf parameter_annotation)
      as Hparameter_wf.
    pose proof (annotation_symbolic_ty_join_ready parameter_annotation)
      as Hparameter_ready.
    destruct (IHbody
      (annotation_symbolic_ty parameter_annotation :: Gamma) symbolic_body
      ltac:(constructor; [apply type_effect_equiv_refl | assumption])
      ltac:(constructor; assumption) ltac:(constructor; assumption)
      eq_refl)
      as [result_ty [body_effect [C
        [Hinfer [Hmodels [Hequiv_result [Hequiv_body Hready_result]]]]]]].
    exists (STyArrow (annotation_symbolic_ty parameter_annotation)
      body_effect result_ty), [], C. split.
    + apply SIInferAbs. exact Hinfer.
    + split.
      * exact Hmodels.
      * split.
        -- simpl. constructor.
           ++ apply type_effect_equiv_refl.
           ++ exact Hequiv_body.
           ++ exact Hequiv_result.
        -- split.
           ++ simpl. apply effect_equiv_refl.
           ++ constructor.
              ** apply annotation_symbolic_ty_meet_ready.
              ** exact Hready_result.
  - intros concrete_context concrete_function concrete_argument concrete_domain
      concrete_latent concrete_codomain concrete_argument_ty
      concrete_function_effect concrete_argument_effect Hfunction IHfunction
      Hargument IHargument Hsubtype Gamma e Hcontext Hcontext_wf Hcontext_ready
      Heq.
    destruct e as
      [| | | | |symbolic_function symbolic_argument| | | |];
      inversion Heq; subst.
    destruct (IHfunction Gamma symbolic_function Hcontext Hcontext_wf
      Hcontext_ready eq_refl)
      as [function_ty [function_effect [function_constraint
        [Hinfer_function [Hmodels_function [Hequiv_function_ty
          [Hequiv_function_effect Hready_function]]]]]]].
    destruct function_ty as
      [| |domain latent codomain|components]; inversion Hequiv_function_ty;
      subst. inversion Hready_function; subst.
    pose proof (proj1 (proj1 (size_inference_wf_mut M)
      Gamma symbolic_function (STyArrow domain latent codomain)
      function_effect function_constraint Hinfer_function Hcontext_wf))
      as Hfunction_ty_wf.
    inversion Hfunction_ty_wf; subst.
    destruct (IHargument Gamma symbolic_argument Hcontext Hcontext_wf
      Hcontext_ready eq_refl)
      as [argument_ty [argument_effect [argument_constraint
        [Hinfer_argument [Hmodels_argument [Hequiv_argument_ty
          [Hequiv_argument_effect Hready_argument]]]]]]].
    pose proof (proj1 (proj1 (size_inference_wf_mut M)
      Gamma symbolic_argument argument_ty argument_effect argument_constraint
      Hinfer_argument Hcontext_wf)) as Hargument_ty_wf.
    destruct (subtype_constraint_reverse_complete sigma argument_ty domain
      concrete_argument_ty concrete_domain Hready_argument ltac:(assumption)
      Hargument_ty_wf ltac:(assumption) Hequiv_argument_ty
      ltac:(assumption) Hsubtype)
      as [subtype_result [Hsubtype_constraint Hmodels_subtype]].
    exists codomain,
      (symbolic_join function_effect (symbolic_join argument_effect latent)),
      (CAnd function_constraint
        (CAnd argument_constraint subtype_result)). split.
    + econstructor; eauto.
    + split.
      * apply models_and_intro; [exact Hmodels_function |].
        apply models_and_intro; assumption.
      * split.
        -- assumption.
        -- split.
           ++ eapply effect_equiv_trans.
              ** apply instantiate_symbolic_join.
              ** apply sequential_effect_respects_equiv.
                 --- exact Hequiv_function_effect.
                 --- eapply effect_equiv_trans.
                     +++ apply instantiate_symbolic_join.
                     +++ apply sequential_effect_respects_equiv; assumption.
           ++ assumption.
  - intros concrete_context Gamma expressions Hcontext Hcontext_wf
      Hcontext_ready Heq.
    destruct expressions; inversion Heq; subst.
    exists [], [], CTop. split.
    + constructor.
    + split.
      * exact I.
      * split; [constructor |]. split; constructor.
  - intros concrete_context concrete_head concrete_tail concrete_head_ty
      concrete_tail_types concrete_head_effect concrete_tail_effects Hhead
      IHhead Htail IHtail Gamma expressions Hcontext Hcontext_wf Hcontext_ready
      Heq.
    destruct expressions as [|symbolic_head symbolic_tail]; inversion Heq; subst.
    destruct (IHhead Gamma symbolic_head Hcontext Hcontext_wf Hcontext_ready
      eq_refl)
      as [head_ty [head_effect [head_constraint
        [Hinfer_head [Hmodels_head [Hequiv_head_ty
          [Hequiv_head_effect Hready_head]]]]]]].
    destruct (IHtail Gamma symbolic_tail Hcontext Hcontext_wf Hcontext_ready
      eq_refl)
      as [tail_types [tail_effects [tail_constraint
        [Hinfer_tail [Hmodels_tail [Hequiv_tail_types
          [Hequiv_tail_effects Hready_tail]]]]]]].
    exists (head_ty :: tail_types), (head_effect :: tail_effects),
      (CAnd head_constraint tail_constraint). split.
    + constructor; assumption.
    + split.
      * apply models_and_intro; assumption.
      * split.
        -- constructor; assumption.
        -- split; constructor; assumption.
Qed.

(** Public expression-level completeness theorem. *)
Theorem constraint_generation_complete :
  forall M sigma Gamma e concrete_ty concrete_effect,
    assignment_within_bound M sigma ->
    symbolic_context_wf Gamma ->
    symbolic_context_join_ready Gamma ->
    algorithmic_has_type
      (instantiate_context sigma Gamma)
      (instantiate_expr sigma e)
      concrete_ty concrete_effect ->
    exists T Phi C,
      size_infers M Gamma e T Phi C /\
      models sigma C /\
      type_effect_equiv (instantiate_ty sigma T) concrete_ty /\
      instantiate_effect sigma Phi ≈ concrete_effect /\
      symbolic_join_ready T.
Proof.
  intros M sigma Gamma e concrete_ty concrete_effect Hbound Hcontext_wf
    Hcontext_ready Htyping.
  apply (proj1 (constraint_generation_complete_mut M sigma Hbound)
    (instantiate_context sigma Gamma) (instantiate_expr sigma e)
    concrete_ty concrete_effect Htyping Gamma e).
  - apply instantiate_context_equiv_refl.
  - exact Hcontext_wf.
  - exact Hcontext_ready.
  - reflexivity.
Qed.

(** End-to-end completeness from algorithmic checking and a concrete
    bandwidth bound to modeled local and root constraints. *)
Theorem size_inference_complete :
  forall M sigma Gamma e concrete_ty concrete_effect B,
    assignment_within_bound M sigma ->
    symbolic_context_wf Gamma ->
    symbolic_context_join_ready Gamma ->
    0 <= B ->
    algorithmic_has_type
      (instantiate_context sigma Gamma)
      (instantiate_expr sigma e)
      concrete_ty concrete_effect ->
    required_bandwidth concrete_effect <= B ->
    exists T Phi C,
      size_infers M Gamma e T Phi C /\
      models sigma (CAnd C (root_constraint Phi B)) /\
      type_effect_equiv (instantiate_ty sigma T) concrete_ty /\
      instantiate_effect sigma Phi ≈ concrete_effect.
Proof.
  intros M sigma Gamma e concrete_ty concrete_effect B Hbound Hcontext_wf
    Hcontext_ready HB Htyping Hbudget.
  destruct (constraint_generation_complete M sigma Gamma e concrete_ty
    concrete_effect Hbound Hcontext_wf Hcontext_ready Htyping)
    as [T [Phi [C [Hinfer [Hmodels [Hequiv_type
      [Hequiv_effect Hready]]]]]]].
  pose proof (size_infers_effect_wf M Gamma e T Phi C Hinfer Hcontext_wf)
    as Heffect_wf.
  assert (Hconcrete_safe : bandwidth_safe B concrete_effect).
  { apply (proj2 (required_bandwidth_spec concrete_effect B HB)).
    exact Hbudget. }
  assert (Hsymbolic_safe :
    bandwidth_safe B (instantiate_effect sigma Phi)).
  { eapply bandwidth_safe_antitone_nonnegative_budget.
    - exact HB.
    - exact (proj1 Hequiv_effect).
    - exact Hconcrete_safe. }
  assert (Hsymbolic_budget :
    required_bandwidth (instantiate_effect sigma Phi) <= B).
  { apply required_bandwidth_least; assumption. }
  pose proof (proj2 (root_constraint_exact sigma Phi B Heffect_wf HB)
    Hsymbolic_budget) as Hroot.
  exists T, Phi, C. split.
  - exact Hinfer.
  - split.
    + apply models_and_intro; assumption.
    + split; assumption.
Qed.

(** Closed-source form of end-to-end completeness.

    This is the public source-program theorem: typing under the empty context
    rules out free variables, and the empty symbolic context is automatically
    well formed and join-ready.  Programmer-written annotations are concrete
    and nonnegative by construction of [annotation_ty], so this theorem needs
    no additional annotation-validity premise. *)
Corollary size_inference_complete_closed_source :
  forall M sigma e concrete_ty concrete_effect B,
    assignment_within_bound M sigma ->
    0 <= B ->
    algorithmic_has_type
      [] (instantiate_expr sigma e) concrete_ty concrete_effect ->
    required_bandwidth concrete_effect <= B ->
    exists T Phi C,
      size_infers M [] e T Phi C /\
      models sigma (CAnd C (root_constraint Phi B)) /\
      type_effect_equiv (instantiate_ty sigma T) concrete_ty /\
      instantiate_effect sigma Phi ≈ concrete_effect.
Proof.
  intros M sigma e concrete_ty concrete_effect B Hbound HB Htyping Hbudget.
  apply (size_inference_complete M sigma [] e concrete_ty concrete_effect B).
  - exact Hbound.
  - constructor.
  - constructor.
  - exact HB.
  - exact Htyping.
  - exact Hbudget.
Qed.
