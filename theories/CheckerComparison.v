(** Comparison of declarative and algorithmic concrete typing.

    Declarative typing admits [TySub] at any point in a derivation, whereas
    algorithmic typing keeps subsumption at the application and conditional
    rules where it is needed.  Consequently the two judgments need not return
    identical results: declarative typing may widen both result types and
    latent effects.  This file proves the appropriate completeness property:
    every declaratively typed source expression has an algorithmic typing whose
    type and effect are at least as precise.

    The proof follows the standard subsumption-elimination argument, strengthened
    to permit pointwise-more-precise contexts.  That strengthening is essential
    for let bindings: the algorithmic type inferred for the bound expression
    may be a strict subtype of the type chosen by the declarative derivation.

    Proof map:

    - [context_subtype] and [context_subtype_lookup] implement the narrowing
      argument needed when a let-bound variable receives a more precise type.
    - [effect_le_empty_inv], [effects_below_repeat_empty], and
      [parallel_effects_mono_list] bridge the aligned list judgments used by
      tuples and parallel expressions.
    - [subtype_nat_inv] and [subtype_arrow_inv] expose exactly the shapes needed
      by algorithmic conditionals and applications.
    - [declarative_algorithmic_refinement_mut] performs one mutual induction
      over declarative expression and list typing, deleting [TySub] steps and
      reconstructing a syntax-directed derivation.
    - The two public results specialize the strengthened theorem to one context
      and then combine it with the already-proved soundness direction. *)

From Stdlib Require Import List.
From BandwidthTimeout Require Import Effects Normalization Syntax Typing
  Merging AlgorithmicTyping Completeness.

Import ListNotations.

(** [context_subtype algorithmic declarative] is pointwise context precision.

    The [Forall2] representation simultaneously records equal context lengths
    and, at every de Bruijn position [i], a relation

      [algorithmic[i] <: declarative[i]].

    The orientation matters: algorithmic reconstruction is allowed to know a
    more precise type for a variable than the original declarative derivation.
    This relation appears only in the strengthened induction theorem; the public
    same-context theorem later instantiates both arguments with [Gamma]. *)
Definition context_subtype
    (algorithmic declarative : context) : Prop :=
  Forall2 subtype algorithmic declarative.

(** Every context pointwise refines itself.

    This is the bridge from the strengthened theorem, which permits two related
    contexts, to the user-facing comparison theorem over a single context. *)
Lemma context_subtype_refl :
  forall Gamma,
    context_subtype Gamma Gamma.
Proof.
  intro Gamma. unfold context_subtype.
  induction Gamma as [|T Gamma IH]; constructor.
  - apply subtype_refl.
  - exact IH.
Qed.

(** Looking up a declarative binding in two related contexts recovers a
    corresponding, possibly more precise, algorithmic binding.

    This is the variable case of the main induction. Because contexts are
    aligned by [Forall2], walking to the same de Bruijn index on both sides
    finds an algorithmic type that is a subtype of the declarative one. *)
Lemma context_subtype_lookup :
  forall algorithmic declarative index declarative_ty,
    context_subtype algorithmic declarative ->
    lookup declarative index declarative_ty ->
    exists algorithmic_ty,
      lookup algorithmic index algorithmic_ty /\
      algorithmic_ty <: declarative_ty.
Proof.
  intros algorithmic declarative index declarative_ty Hcontexts.
  unfold context_subtype in Hcontexts.
  revert index declarative_ty.
  induction Hcontexts; intros index declarative_ty Hlookup.
  - destruct index; inversion Hlookup.
  - destruct index as [|index']; simpl in Hlookup.
    + inversion Hlookup; subst. exists x. split.
      * reflexivity.
      * exact H.
    + apply IHHcontexts. exact Hlookup.
Qed.

(** The only effect below the empty effect is the empty effect itself.

    This is stronger than merely saying that empty is the least effect. If a
    nonempty [Phi] were below [[]], its head obligation would have to be covered
    by a member of the empty list, which is impossible. The tuple case uses the
    resulting list equality because [AlgTyTuple] requires literal empty effects
    for all value components. *)
Lemma effect_le_empty_inv :
  forall Phi,
    Phi ≼ [] ->
    Phi = [].
Proof.
  intros [|p Phi] Hle.
  - reflexivity.
  - exfalso.
    destruct (Hle p (or_introl eq_refl)) as [q [Hq _]].
    inversion Hq.
Qed.

(** Pointwise effect refinement is preserved by the n-ary parallel fold.

    The binary fact [parallel_effect_mono] already handles one pair of effects.
    Induction over [Forall2] lifts it to [parallel_effects], which is the fold
    used by both declarative and algorithmic parallel typing rules. *)
Lemma parallel_effects_mono_list :
  forall algorithmic_effects declarative_effects,
    Forall2 effect_le algorithmic_effects declarative_effects ->
    parallel_effects algorithmic_effects ≼
    parallel_effects declarative_effects.
Proof.
  intros algorithmic_effects declarative_effects Hrelations.
  induction Hrelations; simpl.
  - apply effect_le_refl.
  - apply parallel_effect_mono; assumption.
Qed.

(** If a list of effects is pointwise below an equally long list of empty
    effects, every effect in the first list is literally empty.

    The proof combines alignment information from [Forall2] with
    [effect_le_empty_inv] at every head. Tuple typing needs this syntactic list
    equality because its aligned judgment stores [repeat [] n], rather than a
    list whose members are only semantically equivalent to empty. *)
Lemma effects_below_repeat_empty :
  forall effects count,
    Forall2 effect_le effects (repeat [] count) ->
    effects = repeat [] count.
Proof.
  intros effects count Hrelations.
  remember (repeat [] count) as empty_effects eqn:Hempty.
  revert count Hempty.
  induction Hrelations; intros count Hempty.
  - destruct count; simpl in Hempty; [reflexivity | discriminate].
  - destruct count; simpl in Hempty; [discriminate |].
    inversion Hempty; subst.
    rewrite (effect_le_empty_inv x H).
    f_equal. apply IHHrelations with (count := count). reflexivity.
Qed.

(** A subtype of [Nat] has exactly the [Nat] shape required by the
    algorithmic conditional rule.

    The declarative guard may end in subsumption, so induction initially gives
    an algorithmic guard type merely known to be below [Nat]. Structural
    inversion rules out units, arrows, and products and recovers literal
    [Nat], which is what [AlgTyIfZero] requires. *)
Lemma subtype_nat_inv :
  forall T,
    T <: Syntax.TyNat ->
    T = Syntax.TyNat.
Proof.
  intros T Hsub. destruct T; inversion Hsub. reflexivity.
Qed.

(** A subtype of an arrow is itself an arrow.

    If an algorithmic function type is below the arrow selected by a
    declarative application, structural inversion recovers an algorithmic
    domain, latent effect, and codomain. The three returned relations are the
    arrow-variance facts needed to rebuild [AlgTyApp]: the declarative domain
    is below the algorithmic domain, the algorithmic latent effect is covered
    by the declarative latent effect, and the algorithmic codomain is below the
    declarative codomain. *)
Lemma subtype_arrow_inv :
  forall T declarative_domain declarative_latent declarative_codomain,
    T <:
      Syntax.TyArrow declarative_domain declarative_latent
        declarative_codomain ->
    exists algorithmic_domain algorithmic_latent algorithmic_codomain,
      T = Syntax.TyArrow algorithmic_domain algorithmic_latent
        algorithmic_codomain /\
      declarative_domain <: algorithmic_domain /\
      algorithmic_latent ≼ declarative_latent /\
      algorithmic_codomain <: declarative_codomain.
Proof.
  intros T declarative_domain declarative_latent declarative_codomain Hsub.
  destruct T as
    [| |algorithmic_domain algorithmic_latent algorithmic_codomain|];
    inversion Hsub; subst.
  exists algorithmic_domain, algorithmic_latent, algorithmic_codomain.
  repeat split; assumption.
Qed.

(** Strengthened declarative-to-algorithmic completeness, mutually for
    expressions and aligned expression lists.

    The expression statement returns an algorithmic type below the declarative
    type and an algorithmic effect covered by the declarative effect.  The list
    statement records those relations pointwise.

    Induction is over the declarative derivation, not over bare expression
    syntax. Consequently the [TySub] case is explicit: it discards that final
    declarative subsumption step and composes its subtype premise with the
    precision result from the induction hypothesis. Recursive [TySub] uses are
    removed in the same way inside every premise. *)
Lemma declarative_algorithmic_refinement_mut :
  (forall declarative_context e declarative_ty declarative_effect,
      has_type declarative_context e declarative_ty declarative_effect ->
      forall algorithmic_context,
        context_subtype algorithmic_context declarative_context ->
        source_expr e ->
        exists algorithmic_ty algorithmic_effect,
          algorithmic_has_type
            algorithmic_context e algorithmic_ty algorithmic_effect /\
          algorithmic_ty <: declarative_ty /\
          algorithmic_effect ≼ declarative_effect) /\
  (forall declarative_context expressions declarative_types
          declarative_effects,
      expressions_have_types declarative_context expressions
        declarative_types declarative_effects ->
      forall algorithmic_context,
        context_subtype algorithmic_context declarative_context ->
        Forall source_expr expressions ->
        exists algorithmic_types algorithmic_effects,
          algorithmic_expressions_have_types algorithmic_context expressions
            algorithmic_types algorithmic_effects /\
          Forall2 subtype algorithmic_types declarative_types /\
          Forall2 effect_le algorithmic_effects declarative_effects).
Proof.
  apply typing_mutind.
  (** [TyVar]. Transfer lookup through the pointwise-related contexts. *)
  - intros declarative_context index declarative_ty Hlookup
      algorithmic_context Hcontexts Hsource.
    destruct (context_subtype_lookup _ _ _ _ Hcontexts Hlookup)
      as [algorithmic_ty [Halgorithmic_lookup Hsubtype]].
    exists algorithmic_ty, []. split.
    + constructor. exact Halgorithmic_lookup.
    + split; [exact Hsubtype | apply effect_le_refl].
  (** [TyUnit]. Both systems produce exactly [Unit] and the empty effect. *)
  - intros declarative_context algorithmic_context Hcontexts Hsource.
    exists Syntax.TyUnit, []. split.
    + constructor.
    + split; [constructor | apply effect_le_refl].
  (** [TyNat]. Both systems produce exactly [Nat] and the empty effect. *)
  - intros declarative_context n algorithmic_context Hcontexts Hsource.
    exists Syntax.TyNat, []. split.
    + constructor.
    + split; [constructor | apply effect_le_refl].
  (** [TyTuple]. Reconstruct all components mutually. Their effects are only
      initially known to lie below empty; [effects_below_repeat_empty] turns
      that semantic fact into the literal empty-effect list required by the
      algorithmic tuple rule. Product covariance relates the result types. *)
  - intros declarative_context components component_types Hvalues Hcomponents
      IHcomponents algorithmic_context Hcontexts Hsource.
    pose proof (source_tuple_components _ Hsource) as Hsource_components.
    destruct (IHcomponents algorithmic_context Hcontexts Hsource_components)
      as [algorithmic_types [algorithmic_effects
        [Halgorithmic [Htypes Heffects]]]].
    pose proof (effects_below_repeat_empty _ _ Heffects) as Hempty.
    subst algorithmic_effects.
    exists (Syntax.TyProduct algorithmic_types), []. split.
    + apply AlgTyTuple; assumption.
    + split.
      * apply SubProduct. exact Htypes.
      * apply effect_le_refl.
  (** [TyDownload]. Download typing is already syntax directed, so its type and
      singleton obligation are unchanged. *)
  - intros declarative_context size timeout algorithmic_context Hcontexts
      Hsource.
    exists Syntax.TyUnit, (download_effect size timeout). split.
    + constructor.
    + split; [constructor | apply effect_le_refl].
  (** [TyRunning]. No reconstruction is required: [ERunning] is runtime-only
      syntax and contradicts the theorem's [source_expr] premise. *)
  - intros declarative_context size timeout algorithmic_context Hcontexts
      Hsource. inversion Hsource.
  (** [TyLet]. First infer a potentially smaller type for the bound expression.
      Extend the algorithmic context with that smaller type and the declarative
      context with the original type; [context_subtype] relates the extensions,
      allowing the strengthened induction hypothesis to reconstruct the body.
      Sequential-effect monotonicity then relates the two whole-let effects. *)
  - intros declarative_context bound body bound_ty body_ty bound_effect
      body_effect Hbound IHbound Hbody IHbody algorithmic_context Hcontexts
      Hsource.
    inversion Hsource; subst.
    destruct (IHbound algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_bound_ty [algorithmic_bound_effect
        [Halgorithmic_bound [Hbound_sub Hbound_effect_le]]]].
    destruct (IHbody (algorithmic_bound_ty :: algorithmic_context)
      ltac:(unfold context_subtype; constructor; assumption)
      ltac:(assumption))
      as [algorithmic_body_ty [algorithmic_body_effect
        [Halgorithmic_body [Hbody_sub Hbody_effect_le]]]].
    exists algorithmic_body_ty,
      (sequential_effect algorithmic_bound_effect algorithmic_body_effect).
    split.
    + eapply AlgTyLet; eauto.
    + split.
      * exact Hbody_sub.
      * apply sequential_effect_mono; assumption.
  (** [TyIfZero]. Guard inversion recovers literal [Nat]. Each reconstructed
      branch type is below the common declarative branch type, so concrete join
      optimality supplies an algorithmic join that also remains below it. *)
  - intros declarative_context guard zero_branch nonzero_branch branch_ty
      guard_effect zero_effect nonzero_effect Hguard IHguard Hzero IHzero
      Hnonzero IHnonzero algorithmic_context Hcontexts Hsource.
    inversion Hsource; subst.
    destruct (IHguard algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_guard_ty [algorithmic_guard_effect
        [Halgorithmic_guard [Hguard_sub Hguard_effect_le]]]].
    apply subtype_nat_inv in Hguard_sub. subst algorithmic_guard_ty.
    destruct (IHzero algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_zero_ty [algorithmic_zero_effect
        [Halgorithmic_zero [Hzero_sub Hzero_effect_le]]]].
    destruct (IHnonzero algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_nonzero_ty [algorithmic_nonzero_effect
        [Halgorithmic_nonzero [Hnonzero_sub Hnonzero_effect_le]]]].
    destruct (concrete_type_join_optimal algorithmic_zero_ty
      algorithmic_nonzero_ty branch_ty Hzero_sub Hnonzero_sub)
      as [algorithmic_result_ty [Hjoin Hresult_sub]].
    exists algorithmic_result_ty,
      (sequential_effect algorithmic_guard_effect
        (sequential_effect algorithmic_zero_effect
          algorithmic_nonzero_effect)).
    split.
    + econstructor; eauto.
    + split.
      * exact Hresult_sub.
      * apply sequential_effect_mono.
        -- exact Hguard_effect_le.
        -- apply sequential_effect_mono; assumption.
  (** [TyParallel]. The mutual list hypothesis reconstructs all branches.
      Product covariance relates their result types, and
      [parallel_effects_mono_list] relates the folded parallel effects. *)
  - intros declarative_context branches branch_types branch_effects Hbranches
      IHbranches algorithmic_context Hcontexts Hsource.
    pose proof (source_parallel_branches _ Hsource) as Hsource_branches.
    destruct (IHbranches algorithmic_context Hcontexts Hsource_branches)
      as [algorithmic_types [algorithmic_effects
        [Halgorithmic [Htypes Heffects]]]].
    exists (Syntax.TyProduct algorithmic_types),
      (parallel_effects algorithmic_effects). split.
    + apply AlgTyParallel. exact Halgorithmic.
    + split.
      * apply SubProduct. exact Htypes.
      * apply parallel_effects_mono_list. exact Heffects.
  (** [TyAbs]. The parameter annotation is identical in both judgments, so the
      contexts extend by a reflexive subtype. Body type/effect precision lifts
      directly through the covariant codomain and latent-effect positions of
      arrow subtyping; the immediate lambda effect remains empty. *)
  - intros declarative_context parameter_ty body result_ty body_effect Hbody
      IHbody algorithmic_context Hcontexts Hsource.
    pose proof (source_lambda_body _ _ Hsource) as Hsource_body.
    destruct (IHbody (parameter_ty :: algorithmic_context)
      ltac:(unfold context_subtype; constructor;
        [apply subtype_refl | exact Hcontexts]) Hsource_body)
      as [algorithmic_result_ty [algorithmic_body_effect
        [Halgorithmic_body [Hresult_sub Hbody_effect_le]]]].
    exists
      (Syntax.TyArrow parameter_ty algorithmic_body_effect
        algorithmic_result_ty), [].
    split.
    + apply AlgTyAbs. exact Halgorithmic_body.
    + split.
      * apply SubArrow.
        -- apply subtype_refl.
        -- exact Hbody_effect_le.
        -- exact Hresult_sub.
      * apply effect_le_refl.
  (** [TyApp]. Arrow inversion turns the reconstructed function's subtype fact
      into its domain/latent/codomain variance premises. Transitivity shows the
      reconstructed argument is accepted by that more precise domain. The
      latent-effect premise and effect monotonicity relate application effects. *)
  - intros declarative_context function argument domain codomain latent
      function_effect argument_effect Hfunction IHfunction Hargument
      IHargument algorithmic_context Hcontexts Hsource.
    inversion Hsource; subst.
    destruct (IHfunction algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_function_ty [algorithmic_function_effect
        [Halgorithmic_function [Hfunction_sub Hfunction_effect_le]]]].
    destruct (subtype_arrow_inv _ _ _ _ Hfunction_sub)
      as [algorithmic_domain [algorithmic_latent [algorithmic_codomain
        [Hfunction_shape [Hdomain_sub
          [Hlatent_le Hcodomain_sub]]]]]].
    subst algorithmic_function_ty.
    destruct (IHargument algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_argument_ty [algorithmic_argument_effect
        [Halgorithmic_argument [Hargument_sub Hargument_effect_le]]]].
    assert (Happlication_sub : algorithmic_argument_ty <: algorithmic_domain).
    { eapply subtype_trans; eassumption. }
    exists algorithmic_codomain,
      (sequential_effect algorithmic_function_effect
        (sequential_effect algorithmic_argument_effect algorithmic_latent)).
    split.
    + eapply AlgTyApp with
        (domain := algorithmic_domain)
        (latent := algorithmic_latent)
        (argument_ty := algorithmic_argument_ty); eauto.
    + split.
      * exact Hcodomain_sub.
      * apply sequential_effect_mono.
        -- exact Hfunction_effect_le.
        -- apply sequential_effect_mono; assumption.
  (** [TySub]. Algorithmic typing has no corresponding global rule. Keep the
      derivation produced by the induction hypothesis, compose its result type
      with the declarative subtype premise, and leave its smaller effect intact. *)
  - intros declarative_context e source_ty target_ty Phi Htyping IHtyping
      Hsubtype algorithmic_context Hcontexts Hsource.
    destruct (IHtyping algorithmic_context Hcontexts Hsource)
      as [algorithmic_ty [algorithmic_effect
        [Halgorithmic [Halgorithmic_sub Heffect_le]]]].
    exists algorithmic_ty, algorithmic_effect. split.
    + exact Halgorithmic.
    + split.
      * eapply subtype_trans; eassumption.
      * exact Heffect_le.
  (** [TypesNil]. Empty expression lists agree exactly. *)
  - intros declarative_context algorithmic_context Hcontexts Hsources.
    inversion Hsources. exists [], []. repeat split; constructor.
  (** [TypesCons]. Reconstruct the head expression and tail list separately,
      then preserve their pointwise type/effect precision with [Forall2]. *)
  - intros declarative_context e expressions T types Phi effects Hhead IHhead
      Htail IHtail algorithmic_context Hcontexts Hsources.
    inversion Hsources; subst.
    destruct (IHhead algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_ty [algorithmic_effect
        [Halgorithmic_head [Htype_relation Heffect_relation]]]].
    destruct (IHtail algorithmic_context Hcontexts ltac:(assumption))
      as [algorithmic_types [algorithmic_effects
        [Halgorithmic_tail [Htype_relations Heffect_relations]]]].
    exists (algorithmic_ty :: algorithmic_types),
      (algorithmic_effect :: algorithmic_effects).
    split.
    + constructor; assumption.
    + split; constructor; assumption.
Qed.

(** Public comparison theorem.

    For the same context, algorithmic typing is complete for declaratively
    typed source expressions and returns a result at least as precise in both
    its type and effect. The proof uses [context_subtype_refl] to specialize the
    stronger two-context induction theorem. Thus context refinement is proof
    infrastructure, not an additional premise exposed to clients. *)
Theorem declarative_typing_algorithmic_refinement :
  forall Gamma e declarative_ty declarative_effect,
    source_has_type Gamma e declarative_ty declarative_effect ->
    exists algorithmic_ty algorithmic_effect,
      algorithmic_has_type Gamma e algorithmic_ty algorithmic_effect /\
      algorithmic_ty <: declarative_ty /\
      algorithmic_effect ≼ declarative_effect.
Proof.
  intros Gamma e declarative_ty declarative_effect [Hsource Htyping].
  apply (proj1 declarative_algorithmic_refinement_mut Gamma e declarative_ty
    declarative_effect Htyping Gamma).
  - apply context_subtype_refl.
  - exact Hsource.
Qed.

(** On source expressions, the algorithmic and declarative systems accept
    exactly the same terms.

    Left-to-right is the previously proved soundness theorem and preserves the
    reported type/effect exactly. Right-to-left forgets the precision witnesses
    from [declarative_typing_algorithmic_refinement] and retains only existence
    of an algorithmic derivation. The systems therefore agree on acceptance
    even though declarative subsumption lets them report different results. *)
Corollary algorithmic_declarative_acceptance_equiv :
  forall Gamma e,
    source_expr e ->
    ((exists T Phi, algorithmic_has_type Gamma e T Phi) <->
     (exists T Phi, has_type Gamma e T Phi)).
Proof.
  intros Gamma e Hsource. split.
  - intros [T [Phi Halgorithmic]].
    exists T, Phi. apply algorithmic_typing_sound. exact Halgorithmic.
  - intros [T [Phi Hdeclarative]].
    destruct (declarative_typing_algorithmic_refinement Gamma e T Phi
      (conj Hsource Hdeclarative))
      as [algorithmic_ty [algorithmic_effect [Halgorithmic _]]].
    exists algorithmic_ty, algorithmic_effect. exact Halgorithmic.
Qed.
