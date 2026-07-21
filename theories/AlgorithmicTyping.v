(** Syntax-directed concrete type-and-effect checking.

    This file formalizes the paper's judgment
    [Gamma |-alg e : T ; Phi].  Unlike the declarative judgment in [Typing],
    the algorithmic judgment has no global subsumption rule.  Applications
    perform their subtype check locally, and conditionals compute a concrete
    structural join of their branch types.

    The judgment is mutually defined with an aligned list judgment for tuple
    components and parallel branches.  There is deliberately no rule for the
    runtime-only [ERunning] form: this checker accepts source programs only. *)

From Stdlib Require Import List QArith.

From BandwidthTimeout Require Import Effects Normalization Syntax Typing
  Merging.

Import ListNotations.
Open Scope Q_scope.

(** Algorithmic typing and its aligned list helper.  Every immediate effect is
    computed by the syntax-directed rule rather than chosen by subsumption. *)
Inductive algorithmic_has_type : context -> expr -> ty -> effect -> Prop :=
| AlgTyVar : forall Gamma index T,
    lookup Gamma index T ->
    algorithmic_has_type Gamma (EVar index) T []
| AlgTyUnit : forall Gamma,
    algorithmic_has_type Gamma EUnit Syntax.TyUnit []
| AlgTyNat : forall Gamma n,
    algorithmic_has_type Gamma (ENat n) Syntax.TyNat []
| AlgTyTuple : forall Gamma components component_types,
    Forall value components ->
    algorithmic_expressions_have_types
      Gamma components component_types (repeat [] (length components)) ->
    algorithmic_has_type
      Gamma (ETuple components) (Syntax.TyProduct component_types) []
| AlgTyDownload : forall Gamma size timeout,
    algorithmic_has_type Gamma (EDownload size timeout) Syntax.TyUnit
      (download_effect size timeout)
| AlgTyLet : forall Gamma bound body bound_ty body_ty
                    bound_effect body_effect,
    algorithmic_has_type Gamma bound bound_ty bound_effect ->
    algorithmic_has_type
      (bound_ty :: Gamma) body body_ty body_effect ->
    algorithmic_has_type Gamma (ELet bound body) body_ty
      (sequential_effect bound_effect body_effect)
| AlgTyIfZero : forall Gamma guard zero_branch nonzero_branch
                       zero_ty nonzero_ty result_ty
                       guard_effect zero_effect nonzero_effect,
    algorithmic_has_type Gamma guard Syntax.TyNat guard_effect ->
    algorithmic_has_type Gamma zero_branch zero_ty zero_effect ->
    algorithmic_has_type
      Gamma nonzero_branch nonzero_ty nonzero_effect ->
    concrete_type_join zero_ty nonzero_ty result_ty ->
    algorithmic_has_type
      Gamma (EIfZero guard zero_branch nonzero_branch) result_ty
      (sequential_effect guard_effect
        (sequential_effect zero_effect nonzero_effect))
| AlgTyParallel : forall Gamma branches branch_types branch_effects,
    algorithmic_expressions_have_types
      Gamma branches branch_types branch_effects ->
    algorithmic_has_type Gamma (EParallel branches)
      (Syntax.TyProduct branch_types) (parallel_effects branch_effects)
| AlgTyAbs : forall Gamma parameter_ty body result_ty body_effect,
    algorithmic_has_type
      (parameter_ty :: Gamma) body result_ty body_effect ->
    algorithmic_has_type Gamma (ELambda parameter_ty body)
      (Syntax.TyArrow parameter_ty body_effect result_ty) []
| AlgTyApp : forall Gamma function argument domain latent codomain argument_ty
                    function_effect argument_effect,
    algorithmic_has_type Gamma function
      (Syntax.TyArrow domain latent codomain) function_effect ->
    algorithmic_has_type Gamma argument argument_ty argument_effect ->
    subtype argument_ty domain ->
    algorithmic_has_type Gamma (EApp function argument) codomain
      (sequential_effect function_effect
        (sequential_effect argument_effect latent))
with algorithmic_expressions_have_types
    : context -> list expr -> list ty -> list effect -> Prop :=
| AlgTypesNil : forall Gamma,
    algorithmic_expressions_have_types Gamma [] [] []
| AlgTypesCons : forall Gamma e expressions T types Phi effects,
    algorithmic_has_type Gamma e T Phi ->
    algorithmic_expressions_have_types Gamma expressions types effects ->
    algorithmic_expressions_have_types
      Gamma (e :: expressions) (T :: types) (Phi :: effects).

Scheme algorithmic_has_type_ind_mut :=
  Induction for algorithmic_has_type Sort Prop
with algorithmic_expressions_have_types_ind_mut :=
  Induction for algorithmic_expressions_have_types Sort Prop.

Combined Scheme algorithmic_typing_mutind
  from algorithmic_has_type_ind_mut,
       algorithmic_expressions_have_types_ind_mut.

(** Every algorithmic derivation is accepted by the declarative system.  The
    conditional case widens each branch to the computed join, while the
    application case widens its argument at the local subtype premise. *)
Lemma algorithmic_typing_sound_mut :
  (forall Gamma e T Phi,
      algorithmic_has_type Gamma e T Phi ->
      has_type Gamma e T Phi) /\
  (forall Gamma expressions types effects,
      algorithmic_expressions_have_types Gamma expressions types effects ->
      expressions_have_types Gamma expressions types effects).
Proof.
  apply algorithmic_typing_mutind.
  - intros Gamma index T Hlookup. constructor. exact Hlookup.
  - intros. constructor.
  - intros. constructor.
  - intros Gamma components component_types Hvalues Hcomponents IHcomponents.
    apply TyTuple; assumption.
  - intros Gamma size timeout. constructor.
  - intros Gamma bound body bound_ty body_ty bound_effect body_effect
      Hbound IHbound Hbody IHbody.
    eapply TyLet; eauto.
  - intros Gamma guard zero_branch nonzero_branch zero_ty nonzero_ty result_ty
      guard_effect zero_effect nonzero_effect Hguard IHguard Hzero IHzero
      Hnonzero IHnonzero Hjoin.
    destruct (concrete_type_join_correct _ _ _ Hjoin)
      as [Hzero_sub Hnonzero_sub].
    apply TyIfZero.
    + exact IHguard.
    + eapply TySub; eauto.
    + eapply TySub; eauto.
  - intros Gamma branches branch_types branch_effects Hbranches IHbranches.
    apply TyParallel. exact IHbranches.
  - intros Gamma parameter_ty body result_ty body_effect Hbody IHbody.
    apply TyAbs. exact IHbody.
  - intros Gamma function argument domain latent codomain argument_ty
      function_effect argument_effect Hfunction IHfunction Hargument
      IHargument Hsubtype.
    apply TyApp with (domain := domain) (latent := latent).
    + exact IHfunction.
    + eapply TySub; eauto.
  - intros Gamma. constructor.
  - intros Gamma e expressions T types Phi effects Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

(** Main-judgment form of algorithmic soundness. *)
Theorem algorithmic_typing_sound :
  forall Gamma e T Phi,
    algorithmic_has_type Gamma e T Phi ->
    has_type Gamma e T Phi.
Proof.
  intros Gamma e T Phi Htyping.
  apply (proj1 algorithmic_typing_sound_mut Gamma e T Phi Htyping).
Qed.

(** The algorithmic checker accepts only source syntax; in particular, no
    derivation can contain a runtime-only running-download node. *)
Lemma algorithmic_typing_source_mut :
  (forall Gamma e T Phi,
      algorithmic_has_type Gamma e T Phi ->
      source_expr e) /\
  (forall Gamma expressions types effects,
      algorithmic_expressions_have_types Gamma expressions types effects ->
      Forall source_expr expressions).
Proof.
  apply algorithmic_typing_mutind.
  - intros. constructor.
  - intros. constructor.
  - intros. constructor.
  - intros Gamma components component_types Hvalues Hcomponents IHcomponents.
    apply SrcTuple; assumption.
  - intros. constructor.
  - intros Gamma bound body bound_ty body_ty bound_effect body_effect
      Hbound IHbound Hbody IHbody. constructor; assumption.
  - intros Gamma guard zero_branch nonzero_branch zero_ty nonzero_ty result_ty
      guard_effect zero_effect nonzero_effect Hguard IHguard Hzero IHzero
      Hnonzero IHnonzero Hjoin. constructor; assumption.
  - intros Gamma branches branch_types branch_effects Hbranches IHbranches.
    constructor. exact IHbranches.
  - intros Gamma parameter_ty body result_ty body_effect Hbody IHbody.
    constructor. exact IHbody.
  - intros Gamma function argument domain latent codomain argument_ty
      function_effect argument_effect Hfunction IHfunction Hargument
      IHargument Hsubtype. constructor; assumption.
  - intros. constructor.
  - intros Gamma e expressions T types Phi effects Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

(** Main-judgment form of source-grammar preservation. *)
Theorem algorithmic_typing_source :
  forall Gamma e T Phi,
    algorithmic_has_type Gamma e T Phi ->
    source_expr e.
Proof.
  intros Gamma e T Phi Htyping.
  apply (proj1 algorithmic_typing_source_mut Gamma e T Phi Htyping).
Qed.

(** A successful algorithmic check therefore supplies the source-typing
    package used by the runtime safety theorem. *)
Theorem algorithmic_source_typing_sound :
  forall Gamma e T Phi,
    algorithmic_has_type Gamma e T Phi ->
    source_has_type Gamma e T Phi.
Proof.
  intros Gamma e T Phi Htyping. split.
  - apply algorithmic_typing_source with (Gamma := Gamma) (T := T)
      (Phi := Phi). exact Htyping.
  - apply algorithmic_typing_sound. exact Htyping.
Qed.

(** Algorithmic typing bounds every free de Bruijn index by the context
    length, inherited from declarative typing soundness. *)
Corollary algorithmic_typing_scoped :
  forall Gamma e T Phi,
    algorithmic_has_type Gamma e T Phi ->
    scoped (length Gamma) e.
Proof.
  intros Gamma e T Phi Htyping.
  apply typing_implies_scoped with (T := T) (Phi := Phi).
  apply algorithmic_typing_sound. exact Htyping.
Qed.

(** A program algorithmically checked in the empty context is a closed source
    expression. *)
Corollary closed_algorithmic_typing_is_closed_source :
  forall e T Phi,
    algorithmic_has_type [] e T Phi ->
    closed_source e.
Proof.
  intros e T Phi Htyping. split.
  - eapply algorithmic_typing_source; eauto.
  - change (scoped (length ([] : context)) e).
    eapply algorithmic_typing_scoped; eauto.
Qed.
