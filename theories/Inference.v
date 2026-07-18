(** Expression-level constraint generation and its soundness proof.

    This file formalizes the paper's judgment
    [Gamma |-sz e : theta ; Phi | C].  The global representable-size bound [M]
    is an explicit parameter of the Rocq judgment.  Constraint generation is
    mutually defined with an aligned list judgment for tuples and structured
    parallel expressions.

    Since concrete effects are represented as lists rather than mathematical
    sets, soundness returns a concretely typable effect semantically equivalent
    to the normalized instantiated symbolic effect. *)

From Stdlib Require Import Arith List QArith.

From BandwidthTimeout Require Import Effects Normalization Bandwidth Syntax
  Typing SizeInference Symbolic Compatibility Merging RootConstraints.

Import ListNotations.
Open Scope Q_scope.

(** Symbolic typing contexts use the same de Bruijn layout as concrete
    contexts, but store symbolic types. *)
Definition symbolic_context : Type := list symbolic_ty.

(** Instantiate every type in a symbolic context. *)
Definition instantiate_context
    (sigma : size_assignment) (Gamma : symbolic_context) : context :=
  map (instantiate_ty sigma) Gamma.

(** Context lookup before instantiation. *)
Definition symbolic_lookup
    (Gamma : symbolic_context) (index : nat) (T : symbolic_ty) : Prop :=
  nth_error Gamma index = Some T.

(** Symbolic lookup commutes with context instantiation. *)
Lemma instantiate_context_lookup :
  forall sigma Gamma index T,
    symbolic_lookup Gamma index T ->
    lookup (instantiate_context sigma Gamma) index (instantiate_ty sigma T).
Proof.
  intros sigma Gamma index T Hlookup.
  unfold symbolic_lookup in Hlookup.
  unfold lookup, instantiate_context. rewrite nth_error_map, Hlookup.
  reflexivity.
Qed.

(** Programmer-written type annotations contain only concrete latent-effect
    contracts, recursively through arrows and products.  Inferred types remain
    free to contain symbolic effects. *)
Inductive symbolic_annotation_ty : symbolic_ty -> Prop :=
| AnnotationTyUnit : symbolic_annotation_ty STyUnit
| AnnotationTyNat : symbolic_annotation_ty STyNat
| AnnotationTyArrow : forall domain latent codomain concrete_latent,
    symbolic_annotation_ty domain ->
    concrete_symbolic_effect latent concrete_latent ->
    symbolic_annotation_ty codomain ->
    symbolic_annotation_ty (STyArrow domain latent codomain)
| AnnotationTyProduct : forall components,
    Forall symbolic_annotation_ty components ->
    symbolic_annotation_ty (STyProduct components).

(** Expression-level size inference and its aligned list helper.

    Positive timeout is recorded directly in [SIInferDownload], making the
    paper's positive-timeout metavariable convention explicit.  Tuple
    components are symbolic values and must have empty immediate effects, just
    as in the concrete source grammar and typing rule. *)
Inductive size_infers (M : Q) :
    symbolic_context -> symbolic_expr -> symbolic_ty ->
    symbolic_effect -> constraint -> Prop :=
| SIInferVar : forall Gamma index T,
    symbolic_lookup Gamma index T ->
    size_infers M Gamma (SEVar index) T [] CTop
| SIInferUnit : forall Gamma,
    size_infers M Gamma SEUnit STyUnit [] CTop
| SIInferNat : forall Gamma n,
    size_infers M Gamma (SENat n) STyNat [] CTop
| SIInferTuple : forall Gamma components component_types C,
    Forall symbolic_value components ->
    size_infers_list M Gamma components component_types
      (repeat [] (length components)) C ->
    size_infers M Gamma (SETuple components)
      (STyProduct component_types) [] C
| SIInferDownload : forall Gamma variable timeout,
    0 < timeout ->
    size_infers M Gamma (SEDownload variable timeout) STyUnit
      [SymbolicObligation (SRateVariable variable timeout) 1]
      (CAnd (CNonnegative variable) (CUpper variable M))
| SIInferLet : forall Gamma bound body bound_ty body_ty
                      bound_effect body_effect bound_constraint body_constraint,
    size_infers M Gamma bound bound_ty bound_effect bound_constraint ->
    size_infers M (bound_ty :: Gamma) body body_ty body_effect body_constraint ->
    size_infers M Gamma (SELet bound body) body_ty
      (symbolic_join bound_effect body_effect)
      (CAnd bound_constraint body_constraint)
| SIInferIfZero : forall Gamma guard zero_branch nonzero_branch
                         zero_ty nonzero_ty result_ty
                         guard_effect zero_effect nonzero_effect
                         guard_constraint zero_constraint nonzero_constraint
                         join_constraint,
    size_infers M Gamma guard STyNat guard_effect guard_constraint ->
    size_infers M Gamma zero_branch zero_ty zero_effect zero_constraint ->
    size_infers M Gamma nonzero_branch nonzero_ty nonzero_effect
      nonzero_constraint ->
    symbolic_type_join zero_ty nonzero_ty result_ty join_constraint ->
    size_infers M Gamma (SEIfZero guard zero_branch nonzero_branch) result_ty
      (symbolic_join guard_effect
        (symbolic_join zero_effect nonzero_effect))
      (CAnd guard_constraint
        (CAnd zero_constraint (CAnd nonzero_constraint join_constraint)))
| SIInferParallel : forall Gamma branches branch_types branch_effects C,
    size_infers_list M Gamma branches branch_types branch_effects C ->
    size_infers M Gamma (SEParallel branches)
      (STyProduct branch_types)
      (symbolic_parallel_effects branch_effects) C
| SIInferAbs : forall Gamma parameter_ty body result_ty body_effect C,
    symbolic_annotation_ty parameter_ty ->
    size_infers M (parameter_ty :: Gamma) body result_ty body_effect C ->
    size_infers M Gamma (SELambda parameter_ty body)
      (STyArrow parameter_ty body_effect result_ty) [] C
| SIInferApp : forall Gamma function argument domain latent codomain argument_ty
                      function_effect argument_effect
                      function_constraint argument_constraint
                      subtype_result,
    size_infers M Gamma function (STyArrow domain latent codomain)
      function_effect function_constraint ->
    size_infers M Gamma argument argument_ty
      argument_effect argument_constraint ->
    subtype_constraint argument_ty domain subtype_result ->
    size_infers M Gamma (SEApp function argument) codomain
      (symbolic_join function_effect
        (symbolic_join argument_effect latent))
      (CAnd function_constraint
        (CAnd argument_constraint subtype_result))
with size_infers_list (M : Q) :
    symbolic_context -> list symbolic_expr -> list symbolic_ty ->
    list symbolic_effect -> constraint -> Prop :=
| SIInferListNil : forall Gamma,
    size_infers_list M Gamma [] [] [] CTop
| SIInferListCons : forall Gamma e expressions T types Phi effects
                           head_constraint tail_constraint,
    size_infers M Gamma e T Phi head_constraint ->
    size_infers_list M Gamma expressions types effects tail_constraint ->
    size_infers_list M Gamma
      (e :: expressions) (T :: types) (Phi :: effects)
      (CAnd head_constraint tail_constraint).

Scheme size_infers_ind_mut := Induction for size_infers Sort Prop
with size_infers_list_ind_mut := Induction for size_infers_list Sort Prop.

Combined Scheme size_inference_mutind
  from size_infers_ind_mut, size_infers_list_ind_mut.

(** The whole inference language remains separable: every arithmetic leaf is
    a nonnegativity check, a single-variable upper bound, or a variable-free
    concrete comparison. *)
Inductive inference_fragment : constraint -> Prop :=
| InferFragTop : inference_fragment CTop
| InferFragBottom : inference_fragment CBottom
| InferFragAnd : forall C1 C2,
    inference_fragment C1 ->
    inference_fragment C2 ->
    inference_fragment (CAnd C1 C2)
| InferFragNonnegative : forall variable,
    inference_fragment (CNonnegative variable)
| InferFragUpper : forall variable bound,
    inference_fragment (CUpper variable bound)
| InferFragConcreteLe : forall lhs rhs,
    inference_fragment (CConcreteLe lhs rhs).

(** The compatibility fragment is contained in the full inference fragment. *)
Lemma compatibility_is_inference_fragment :
  forall C,
    compatibility_fragment C ->
    inference_fragment C.
Proof.
  intros C Hfragment. induction Hfragment; constructor; assumption.
Qed.

(** Constraint generation preserves separability for expressions and lists. *)
Lemma size_inference_fragment_mut :
  forall M,
  (forall Gamma e T Phi C,
      size_infers M Gamma e T Phi C ->
      inference_fragment C) /\
  (forall Gamma expressions types effects C,
      size_infers_list M Gamma expressions types effects C ->
      inference_fragment C).
Proof.
  intro M.
  apply size_inference_mutind.
  - intros. constructor.
  - intros. constructor.
  - intros. constructor.
  - intros. assumption.
  - intros. constructor; constructor.
  - intros. constructor; assumption.
  - intros. repeat constructor; try assumption.
    apply compatibility_is_inference_fragment.
    eapply symbolic_type_join_fragment; eauto.
  - intros. assumption.
  - intros. assumption.
  - intros. repeat constructor; try assumption.
    apply compatibility_is_inference_fragment.
    eapply subtype_constraint_fragment; eauto.
  - intros. constructor.
  - intros. constructor; assumption.
Qed.

(** Public separability theorem for one expression-level inference result. *)
Theorem size_infers_fragment :
  forall M Gamma e T Phi C,
    size_infers M Gamma e T Phi C ->
    inference_fragment C.
Proof.
  intros M Gamma e T Phi C Hinfer.
  apply (proj1 (size_inference_fragment_mut M)
    Gamma e T Phi C Hinfer).
Qed.

(** Every inference derivation describes grammatical symbolic source syntax. *)
Lemma size_inference_source_mut :
  forall M,
  (forall Gamma e T Phi C,
      size_infers M Gamma e T Phi C ->
      symbolic_source_expr e) /\
  (forall Gamma expressions types effects C,
      size_infers_list M Gamma expressions types effects C ->
      Forall symbolic_source_expr expressions).
Proof.
  intro M.
  apply size_inference_mutind.
  - intros. constructor.
  - intros. constructor.
  - intros. constructor.
  - intros. constructor; assumption.
  - intros. constructor.
  - intros. constructor; assumption.
  - intros. constructor; assumption.
  - intros. constructor. assumption.
  - intros. constructor. assumption.
  - intros. constructor; assumption.
  - intros. constructor.
  - intros. constructor; assumption.
Qed.

(** Instantiation maps a list of symbolic values to concrete values. *)
Lemma instantiate_symbolic_values :
  forall sigma expressions,
    Forall symbolic_value expressions ->
    Forall value (map (instantiate_expr sigma) expressions).
Proof.
  intros sigma expressions Hvalues. induction Hvalues; simpl.
  - constructor.
  - constructor.
    + apply instantiate_symbolic_value. exact H.
    + exact IHHvalues.
Qed.

(** A list of concretely typed values has an all-empty immediate-effect list. *)
Lemma inferred_values_effects_empty :
  forall Gamma expressions types effects,
    expressions_have_types Gamma expressions types effects ->
    Forall value expressions ->
    effects = repeat [] (length expressions).
Proof.
  intros Gamma expressions types effects Htypes Hvalues.
  induction Htypes; inversion Hvalues; subst; simpl.
  - reflexivity.
  - rewrite (value_typing_empty_effect _ _ _ _ H2 H).
    f_equal. apply IHHtypes. assumption.
Qed.

(** Pointwise semantic equivalence is preserved by the structured parallel
    effect fold. *)
Lemma parallel_effects_respects_equiv :
  forall effects effects',
    Forall2 effect_equiv effects effects' ->
    parallel_effects effects ≈ parallel_effects effects'.
Proof.
  intros effects effects' Hequiv. induction Hequiv; simpl.
  - apply effect_equiv_refl.
  - apply parallel_effect_respects_equiv; assumption.
Qed.

(** Mutual soundness of expression and aligned-list constraint generation.

    The inferred type instantiates literally.  The immediate effect is stated
    modulo semantic equivalence because list order is not observable in the
    paper's set semantics. *)
Lemma constraint_generation_sound_mut :
  forall M,
  (forall Gamma e T Phi C,
      size_infers M Gamma e T Phi C ->
      forall sigma,
        models sigma C ->
        exists concrete_effect,
          has_type
            (instantiate_context sigma Gamma)
            (instantiate_expr sigma e)
            (instantiate_ty sigma T)
            concrete_effect /\
          instantiate_effect sigma Phi ≈ concrete_effect) /\
  (forall Gamma expressions types effects C,
      size_infers_list M Gamma expressions types effects C ->
      forall sigma,
        models sigma C ->
        exists concrete_effects,
          expressions_have_types
            (instantiate_context sigma Gamma)
            (map (instantiate_expr sigma) expressions)
            (map (instantiate_ty sigma) types)
            concrete_effects /\
          Forall2 effect_equiv
            (map (instantiate_effect sigma) effects)
            concrete_effects).
Proof.
  intro M.
  apply size_inference_mutind.
  - intros Gamma index T Hlookup sigma Hmodels.
    exists []. split.
    + constructor. apply instantiate_context_lookup. exact Hlookup.
    + simpl. apply effect_equiv_refl.
  - intros Gamma sigma Hmodels. exists []. split.
    + constructor.
    + simpl. apply effect_equiv_refl.
  - intros Gamma n sigma Hmodels. exists []. split.
    + constructor.
    + simpl. apply effect_equiv_refl.
  - intros Gamma components component_types C Hvalues Hlist IHlist
      sigma Hmodels.
    destruct (IHlist sigma Hmodels)
      as [concrete_effects [Htypes Heffects]].
    pose proof (instantiate_symbolic_values sigma components Hvalues)
      as Hconcrete_values.
    pose proof (inferred_values_effects_empty _ _ _ _
      Htypes Hconcrete_values) as Hempty.
    rewrite Hempty in Htypes. exists []. split.
    + simpl. apply TyTuple.
      * exact Hconcrete_values.
      * exact Htypes.
    + simpl. apply effect_equiv_refl.
  - intros Gamma variable timeout Htimeout sigma Hmodels.
    exists (download_effect (sigma variable) timeout). split.
    + simpl. apply TyDownload.
      apply instantiate_download_parameters_wf.
      * exact (proj1 Hmodels).
      * exact Htimeout.
    + simpl. apply effect_equiv_refl.
  - intros Gamma bound body bound_ty body_ty bound_effect body_effect
      bound_constraint body_constraint Hbound IHbound Hbody IHbody
      sigma Hmodels.
    destruct Hmodels as [Hsigma [Hmodels_bound Hmodels_body]].
    destruct (IHbound sigma (conj Hsigma Hmodels_bound))
      as [concrete_bound [Htyping_bound Hequiv_bound]].
    destruct (IHbody sigma (conj Hsigma Hmodels_body))
      as [concrete_body [Htyping_body Hequiv_body]].
    exists (sequential_effect concrete_bound concrete_body). split.
    + simpl. apply TyLet with
        (bound_ty := instantiate_ty sigma bound_ty); assumption.
    + eapply effect_equiv_trans.
      * apply instantiate_symbolic_join.
      * apply sequential_effect_respects_equiv; assumption.
  - intros Gamma guard zero_branch nonzero_branch zero_ty nonzero_ty
      result_ty guard_effect zero_effect nonzero_effect guard_constraint
      zero_constraint nonzero_constraint join_constraint Hguard IHguard
      Hzero IHzero Hnonzero IHnonzero Hjoin sigma Hmodels.
    destruct Hmodels as
      [Hsigma [Hmodels_guard [Hmodels_zero [Hmodels_nonzero Hmodels_join]]]].
    destruct (IHguard sigma (conj Hsigma Hmodels_guard))
      as [concrete_guard [Htyping_guard Hequiv_guard]].
    destruct (IHzero sigma (conj Hsigma Hmodels_zero))
      as [concrete_zero [Htyping_zero Hequiv_zero]].
    destruct (IHnonzero sigma (conj Hsigma Hmodels_nonzero))
      as [concrete_nonzero [Htyping_nonzero Hequiv_nonzero]].
    pose proof (symbolic_type_join_correct sigma zero_ty nonzero_ty result_ty
      join_constraint Hjoin (conj Hsigma Hmodels_join))
      as [Hzero_sub Hnonzero_sub].
    exists (sequential_effect concrete_guard
      (sequential_effect concrete_zero concrete_nonzero)). split.
    + simpl. apply TyIfZero.
      * exact Htyping_guard.
      * eapply TySub; eauto.
      * eapply TySub; eauto.
    + eapply effect_equiv_trans.
      * apply instantiate_symbolic_join.
      * apply sequential_effect_respects_equiv.
        -- exact Hequiv_guard.
        -- eapply effect_equiv_trans.
           ++ apply instantiate_symbolic_join.
           ++ apply sequential_effect_respects_equiv; assumption.
  - intros Gamma branches branch_types branch_effects C Hbranches IHbranches
      sigma Hmodels.
    destruct (IHbranches sigma Hmodels)
      as [concrete_effects [Htypes Heffects]].
    exists (parallel_effects concrete_effects). split.
    + simpl. apply TyParallel. exact Htypes.
    + eapply effect_equiv_trans.
      * apply instantiate_symbolic_parallel_effects.
      * apply parallel_effects_respects_equiv. exact Heffects.
  - intros Gamma parameter_ty body result_ty body_effect C Hparameter
      Hbody IHbody sigma Hmodels.
    destruct (IHbody sigma Hmodels)
      as [concrete_body [Htyping_body Hequiv_body]].
    exists []. split.
    + simpl. eapply TySub.
      * apply TyAbs with (Phi_body := concrete_body). exact Htyping_body.
      * apply SubArrow.
        -- apply subtype_refl.
        -- exact (proj2 Hequiv_body).
        -- apply subtype_refl.
    + simpl. apply effect_equiv_refl.
  - intros Gamma function argument domain latent codomain argument_ty
      function_effect argument_effect function_constraint argument_constraint
      subtype_result Hfunction IHfunction Hargument IHargument Hsubtype
      sigma Hmodels.
    destruct Hmodels as
      [Hsigma [Hmodels_function [Hmodels_argument Hmodels_subtype]]].
    destruct (IHfunction sigma (conj Hsigma Hmodels_function))
      as [concrete_function [Htyping_function Hequiv_function]].
    destruct (IHargument sigma (conj Hsigma Hmodels_argument))
      as [concrete_argument [Htyping_argument Hequiv_argument]].
    pose proof (proj1 (subtype_constraint_exact sigma argument_ty domain
      subtype_result Hsigma Hsubtype) (conj Hsigma Hmodels_subtype))
      as Hargument_subtype.
    exists (sequential_effect concrete_function
      (sequential_effect concrete_argument (instantiate_effect sigma latent))).
    split.
    + simpl. apply TyApp with (domain := instantiate_ty sigma domain).
      * exact Htyping_function.
      * eapply TySub; eauto.
    + eapply effect_equiv_trans.
      * apply instantiate_symbolic_join.
      * apply sequential_effect_respects_equiv.
        -- exact Hequiv_function.
        -- eapply effect_equiv_trans.
           ++ apply instantiate_symbolic_join.
           ++ apply sequential_effect_respects_equiv.
              ** exact Hequiv_argument.
              ** apply effect_equiv_refl.
  - intros Gamma sigma Hmodels. exists []. split; constructor.
  - intros Gamma e expressions T types Phi effects head_constraint
      tail_constraint Hhead IHhead Htail IHtail sigma Hmodels.
    destruct Hmodels as [Hsigma [Hmodels_head Hmodels_tail]].
    destruct (IHhead sigma (conj Hsigma Hmodels_head))
      as [concrete_head [Htyping_head Hequiv_head]].
    destruct (IHtail sigma (conj Hsigma Hmodels_tail))
      as [concrete_tail [Htyping_tail Hequiv_tail]].
    exists (concrete_head :: concrete_tail). split.
    + simpl. constructor; assumption.
    + simpl. constructor; assumption.
Qed.

(** Public constraint-generation soundness theorem.  The instantiated source
    expression has exactly the instantiated inferred type and a semantically
    equivalent concrete effect in the declarative system. *)
Theorem constraint_generation_sound :
  forall M Gamma e T Phi C sigma,
    size_infers M Gamma e T Phi C ->
    models sigma C ->
    exists concrete_effect,
      source_has_type
        (instantiate_context sigma Gamma)
        (instantiate_expr sigma e)
        (instantiate_ty sigma T)
        concrete_effect /\
      instantiate_effect sigma Phi ≈ concrete_effect.
Proof.
  intros M Gamma e T Phi C sigma Hinfer Hmodels.
  destruct (proj1 (constraint_generation_sound_mut M)
    Gamma e T Phi C Hinfer sigma Hmodels)
    as [concrete_effect [Htyping Hequiv]].
  exists concrete_effect. split.
  - split.
    + apply instantiate_symbolic_source.
      apply (proj1 (size_inference_source_mut M)
        Gamma e T Phi C Hinfer).
    + exact Htyping.
  - exact Hequiv.
Qed.
