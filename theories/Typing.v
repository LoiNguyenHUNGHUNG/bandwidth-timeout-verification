(** Declarative source and runtime typing for the bandwidth-timeout calculus.

    The judgment in this file is the paper's type-and-effect judgment. It is
    defined over the shared runtime AST from [Syntax]: source programs use the
    same rules, while [TyRunning] is the single runtime-only extension.

    Contexts follow the de Bruijn representation. The head of a context is the
    type of index [0], namely the variable bound by the nearest lambda or let. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Effects Normalization Syntax Substitution.

Import ListNotations.
Open Scope Q_scope.

(** The paper's sequential effect operator normalizes raw list union. *)
Definition sequential_effect (Phi Psi : effect) : effect :=
  normalize (join Phi Psi).

(** The paper's binary parallel effect operator normalizes raw parallel
    composition. *)
Definition parallel_effect (Phi Psi : effect) : effect :=
  normalize (parallel Phi Psi).

(** Fold binary parallel composition over the effects of a list of branches.
    The empty parallel expression has no bandwidth obligations. *)
Fixpoint parallel_effects (effects : list effect) : effect :=
  match effects with
  | [] => []
  | Phi :: effects' => parallel_effect Phi (parallel_effects effects')
  end.

(** Normalization is monotone for semantic effect coverage. *)
Lemma normalize_mono :
  forall Phi Psi,
    Phi ≼ Psi ->
    normalize Phi ≼ normalize Psi.
Proof.
  intros Phi Psi Hle.
  eapply effect_le_trans.
  - apply normalize_le.
  - eapply effect_le_trans.
    + exact Hle.
    + apply le_normalize.
Qed.

(** Normalized sequential composition is monotone in both operands. *)
Lemma sequential_effect_mono :
  forall Phi1 Phi2 Psi1 Psi2,
    Phi1 ≼ Psi1 ->
    Phi2 ≼ Psi2 ->
    sequential_effect Phi1 Phi2 ≼ sequential_effect Psi1 Psi2.
Proof.
  intros Phi1 Phi2 Psi1 Psi2 H1 H2.
  apply normalize_mono. apply join_mono; assumption.
Qed.

(** Normalized parallel composition is monotone in both operands. *)
Lemma parallel_effect_mono :
  forall Phi1 Phi2 Psi1 Psi2,
    Phi1 ≼ Psi1 ->
    Phi2 ≼ Psi2 ->
    parallel_effect Phi1 Phi2 ≼ parallel_effect Psi1 Psi2.
Proof.
  intros Phi1 Phi2 Psi1 Psi2 H1 H2.
  apply normalize_mono. apply parallel_mono; assumption.
Qed.

(** Type subtyping follows the paper: products are pointwise covariant, while
    arrows are contravariant in their domain, covariant in their codomain, and
    covariant in their latent effect. The paper presents a general reflexivity
    rule; [subtype_refl] below proves that rule admissible for this structural
    Rocq presentation. *)
Inductive subtype : ty -> ty -> Prop :=
| SubUnit : subtype TyUnit TyUnit
| SubNat : subtype TyNat TyNat
| SubProduct : forall components components',
    Forall2 subtype components components' ->
    subtype (TyProduct components) (TyProduct components')
| SubArrow : forall domain latent codomain
                    domain' latent' codomain',
    subtype domain' domain ->
    latent ≼ latent' ->
    subtype codomain codomain' ->
    subtype
      (TyArrow domain latent codomain)
      (TyArrow domain' latent' codomain').

(** Notation matching the direction of the paper's subtype symbol. *)
Notation "T '<:' U" := (subtype T U) (at level 70).

(** Every type is a subtype of itself. *)
Lemma subtype_refl : forall T, T <: T.
Proof.
  fix IH 1. intro T. destruct T.
  - constructor.
  - constructor.
  - apply SubArrow.
    + apply IH.
    + apply effect_le_refl.
    + apply IH.
  - apply SubProduct. induction l as [|T types IHtypes].
    + constructor.
    + constructor.
      * apply IH.
      * exact IHtypes.
Qed.

(** A typing context lists the types of the expression's free de Bruijn
    variables, beginning with index [0]. *)
Definition context : Type := list ty.

(** Context lookup is ordinary list lookup at a de Bruijn index. *)
Definition lookup (Gamma : context) (index : nat) (T : ty) : Prop :=
  nth_error Gamma index = Some T.

(** A singleton effect for a source or running download. *)
Definition download_effect (size timeout : Q) : effect :=
  [Obligation (download_rate size timeout) 1].

(** Runtime type-and-effect typing and aligned list typing are mutually
    inductive. The auxiliary list judgment records one type and one effect for
    each parallel branch. For tuples, the effect list is pointwise empty. *)
Inductive has_type : context -> expr -> ty -> effect -> Prop :=
| TyVar : forall Gamma index T,
    lookup Gamma index T ->
    has_type Gamma (EVar index) T []
| TyUnit : forall Gamma,
    has_type Gamma EUnit TyUnit []
| TyNat : forall Gamma n,
    has_type Gamma (ENat n) TyNat []
| TyTuple : forall Gamma components component_types,
    Forall value components ->
    expressions_have_types
      Gamma components component_types (repeat [] (length components)) ->
    has_type Gamma (ETuple components) (TyProduct component_types) []
| TyDownload : forall Gamma size timeout,
    download_parameters_wf size timeout ->
    has_type Gamma (EDownload size timeout) TyUnit
      (download_effect size timeout)
| TyRunning : forall Gamma size timeout,
    download_parameters_wf size timeout ->
    has_type Gamma (ERunning size timeout) TyUnit
      (download_effect size timeout)
| TyLet : forall Gamma bound body bound_ty body_ty Phi_bound Phi_body,
    has_type Gamma bound bound_ty Phi_bound ->
    has_type (bound_ty :: Gamma) body body_ty Phi_body ->
    has_type Gamma (ELet bound body) body_ty
      (sequential_effect Phi_bound Phi_body)
| TyIfZero : forall Gamma guard zero_branch nonzero_branch
                    branch_ty Phi_guard Phi_zero Phi_nonzero,
    has_type Gamma guard TyNat Phi_guard ->
    has_type Gamma zero_branch branch_ty Phi_zero ->
    has_type Gamma nonzero_branch branch_ty Phi_nonzero ->
    has_type Gamma (EIfZero guard zero_branch nonzero_branch) branch_ty
      (sequential_effect Phi_guard
        (sequential_effect Phi_zero Phi_nonzero))
| TyParallel : forall Gamma branches branch_types branch_effects,
    expressions_have_types Gamma branches branch_types branch_effects ->
    has_type Gamma (EParallel branches) (TyProduct branch_types)
      (parallel_effects branch_effects)
| TyAbs : forall Gamma parameter_ty body result_ty Phi_body,
    has_type (parameter_ty :: Gamma) body result_ty Phi_body ->
    has_type Gamma (ELambda parameter_ty body)
      (TyArrow parameter_ty Phi_body result_ty) []
| TyApp : forall Gamma function argument domain codomain
                 latent Phi_function Phi_argument,
    has_type Gamma function (TyArrow domain latent codomain) Phi_function ->
    has_type Gamma argument domain Phi_argument ->
    has_type Gamma (EApp function argument) codomain
      (sequential_effect Phi_function
        (sequential_effect Phi_argument latent))
| TySub : forall Gamma e T U Phi,
    has_type Gamma e T Phi ->
    T <: U ->
    has_type Gamma e U Phi
with expressions_have_types
    : context -> list expr -> list ty -> list effect -> Prop :=
| TypesNil : forall Gamma,
    expressions_have_types Gamma [] [] []
| TypesCons : forall Gamma e expressions T types Phi effects,
    has_type Gamma e T Phi ->
    expressions_have_types Gamma expressions types effects ->
    expressions_have_types
      Gamma (e :: expressions) (T :: types) (Phi :: effects).

Scheme has_type_mut := Induction for has_type Sort Prop
with expressions_have_types_mut :=
  Induction for expressions_have_types Sort Prop.

Combined Scheme typing_mutind
  from has_type_mut, expressions_have_types_mut.

(** Source typing is runtime typing paired with the fact that no runtime-only
    [ERunning] node occurs in the expression. *)
Definition source_has_type
    (Gamma : context) (e : expr) (T : ty) (Phi : effect) : Prop :=
  source_expr e /\ has_type Gamma e T Phi.

(** A context renaming says that every old variable keeps its type at the
    index selected by [xi] in the new context. *)
Definition context_renaming
    (xi : renaming) (Gamma Delta : context) : Prop :=
  forall index T,
    lookup Gamma index T ->
    lookup Delta (xi index) T.

(** Lifting a type-preserving renaming under one binder keeps the new index
    [0] at the head and renames all older variables outside it. *)
Lemma up_ren_preserves_context :
  forall xi Gamma Delta parameter_ty,
    context_renaming xi Gamma Delta ->
    context_renaming
      (up_ren xi) (parameter_ty :: Gamma) (parameter_ty :: Delta).
Proof.
  intros xi Gamma Delta parameter_ty Hren index T Hlookup.
  destruct index as [|index']; simpl in *.
  - inversion Hlookup. reflexivity.
  - apply Hren. exact Hlookup.
Qed.

(** Shifting all variables embeds a context below one fresh binder. *)
Lemma shift_preserves_context :
  forall Gamma parameter_ty,
    context_renaming shift Gamma (parameter_ty :: Gamma).
Proof.
  intros Gamma parameter_ty index T Hlookup.
  exact Hlookup.
Qed.

(** Renaming simultaneously preserves the main typing judgment and its aligned
    list judgment whenever the context lookup relation is preserved. *)
Lemma typing_renaming_mut :
  (forall Gamma e T Phi,
      has_type Gamma e T Phi ->
      forall Delta xi,
        context_renaming xi Gamma Delta ->
        has_type Delta (rename xi e) T Phi) /\
  (forall Gamma expressions types effects,
      expressions_have_types Gamma expressions types effects ->
      forall Delta xi,
        context_renaming xi Gamma Delta ->
        expressions_have_types
          Delta (map (rename xi) expressions) types effects).
Proof.
  apply typing_mutind.
  - intros Gamma index T Hlookup Delta xi Hren. simpl.
    apply TyVar. apply Hren. exact Hlookup.
  - intros Gamma Delta xi Hren. simpl. constructor.
  - intros Gamma n Delta xi Hren. simpl. constructor.
  - intros Gamma components component_types Hvalues Htypes IHtypes
        Delta xi Hren. simpl.
    apply TyTuple.
    + apply Forall_forall. intros renamed_component Hin.
      apply in_map_iff in Hin.
      destruct Hin as [component [Heq Hin]]. subst renamed_component.
      apply rename_preserves_value.
      apply Forall_forall with (x := component) in Hvalues; assumption.
    + rewrite length_map. apply IHtypes. exact Hren.
  - intros Gamma size timeout Hparameters Delta xi Hren. simpl.
    constructor. exact Hparameters.
  - intros Gamma size timeout Hparameters Delta xi Hren. simpl.
    constructor. exact Hparameters.
  - intros Gamma bound body bound_ty body_ty Phi_bound Phi_body
        Hbound IHbound Hbody IHbody Delta xi Hren. simpl.
    apply TyLet with (bound_ty := bound_ty).
    + apply IHbound. exact Hren.
    + apply IHbody. apply up_ren_preserves_context. exact Hren.
  - intros Gamma guard zero_branch nonzero_branch branch_ty
        Phi_guard Phi_zero Phi_nonzero
        Hguard IHguard Hzero IHzero Hnonzero IHnonzero Delta xi Hren.
    simpl. apply TyIfZero.
    + apply IHguard. exact Hren.
    + apply IHzero. exact Hren.
    + apply IHnonzero. exact Hren.
  - intros Gamma branches branch_types branch_effects
        Hbranches IHbranches Delta xi Hren. simpl.
    apply TyParallel. apply IHbranches. exact Hren.
  - intros Gamma parameter_ty body result_ty Phi_body
        Hbody IHbody Delta xi Hren. simpl.
    apply TyAbs. apply IHbody.
    apply up_ren_preserves_context. exact Hren.
  - intros Gamma function argument domain codomain latent
        Phi_function Phi_argument
        Hfunction IHfunction Hargument IHargument Delta xi Hren. simpl.
    apply TyApp with (domain := domain) (latent := latent).
    + apply IHfunction. exact Hren.
    + apply IHargument. exact Hren.
  - intros Gamma e T U Phi Htyping IHtyping Hsub Delta xi Hren.
    apply TySub with (T := T).
    + apply IHtyping. exact Hren.
    + exact Hsub.
  - intros Gamma Delta xi Hren. simpl. constructor.
  - intros Gamma e expressions T types Phi effects
        Hhead IHhead Htail IHtail Delta xi Hren. simpl.
    constructor.
    + apply IHhead. exact Hren.
    + apply IHtail. exact Hren.
Qed.

(** Convenient main-judgment form of type-preserving renaming. *)
Theorem typing_renaming :
  forall Gamma Delta xi e T Phi,
    context_renaming xi Gamma Delta ->
    has_type Gamma e T Phi ->
    has_type Delta (rename xi e) T Phi.
Proof.
  intros Gamma Delta xi e T Phi Hren Htyping.
  destruct typing_renaming_mut as [Hmain _].
  eapply Hmain; eauto.
Qed.

(** A type-preserving simultaneous substitution maps every variable in the old
    context to a term of the same type and empty immediate effect in the new
    context. Empty effect is essential: arbitrary effectful replacements could
    add obligations each time a variable occurs. *)
Definition context_substitution
    (sigma : substitution) (Gamma Delta : context) : Prop :=
  forall index T,
    lookup Gamma index T ->
    has_type Delta (sigma index) T [].

(** Lifting a type-preserving substitution under a binder maps the new index
    [0] to itself and shifts every older replacement below the new binder. *)
Lemma up_subst_preserves_context :
  forall sigma Gamma Delta parameter_ty,
    context_substitution sigma Gamma Delta ->
    context_substitution
      (up_subst sigma) (parameter_ty :: Gamma) (parameter_ty :: Delta).
Proof.
  intros sigma Gamma Delta parameter_ty Hsubst index T Hlookup.
  destruct index as [|index']; simpl in *.
  - inversion Hlookup; subst. apply TyVar. reflexivity.
  - apply typing_renaming with
      (Gamma := Delta) (xi := shift).
    + apply shift_preserves_context.
    + apply Hsubst. exact Hlookup.
Qed.

(** Simultaneous substitution preserves both the main typing judgment and the
    aligned list judgment when every replacement is typed with empty immediate
    effect. *)
Lemma typing_substitution_mut :
  (forall Gamma e T Phi,
      has_type Gamma e T Phi ->
      forall Delta sigma,
        context_substitution sigma Gamma Delta ->
        has_type Delta (subst sigma e) T Phi) /\
  (forall Gamma expressions types effects,
      expressions_have_types Gamma expressions types effects ->
      forall Delta sigma,
        context_substitution sigma Gamma Delta ->
        expressions_have_types
          Delta (map (subst sigma) expressions) types effects).
Proof.
  apply typing_mutind.
  - intros Gamma index T Hlookup Delta sigma Hsubst. simpl.
    apply Hsubst. exact Hlookup.
  - intros Gamma Delta sigma Hsubst. simpl. constructor.
  - intros Gamma n Delta sigma Hsubst. simpl. constructor.
  - intros Gamma components component_types Hvalues Htypes IHtypes
        Delta sigma Hsubst. simpl.
    apply TyTuple.
    + apply Forall_forall. intros substituted_component Hin.
      apply in_map_iff in Hin.
      destruct Hin as [component [Heq Hin]]. subst substituted_component.
      apply subst_preserves_value.
      apply Forall_forall with (x := component) in Hvalues; assumption.
    + rewrite length_map. apply IHtypes. exact Hsubst.
  - intros Gamma size timeout Hparameters Delta sigma Hsubst. simpl.
    constructor. exact Hparameters.
  - intros Gamma size timeout Hparameters Delta sigma Hsubst. simpl.
    constructor. exact Hparameters.
  - intros Gamma bound body bound_ty body_ty Phi_bound Phi_body
        Hbound IHbound Hbody IHbody Delta sigma Hsubst. simpl.
    apply TyLet with (bound_ty := bound_ty).
    + apply IHbound. exact Hsubst.
    + apply IHbody. apply up_subst_preserves_context. exact Hsubst.
  - intros Gamma guard zero_branch nonzero_branch branch_ty
        Phi_guard Phi_zero Phi_nonzero
        Hguard IHguard Hzero IHzero Hnonzero IHnonzero Delta sigma Hsubst.
    simpl. apply TyIfZero.
    + apply IHguard. exact Hsubst.
    + apply IHzero. exact Hsubst.
    + apply IHnonzero. exact Hsubst.
  - intros Gamma branches branch_types branch_effects
        Hbranches IHbranches Delta sigma Hsubst. simpl.
    apply TyParallel. apply IHbranches. exact Hsubst.
  - intros Gamma parameter_ty body result_ty Phi_body
        Hbody IHbody Delta sigma Hsubst. simpl.
    apply TyAbs. apply IHbody.
    apply up_subst_preserves_context. exact Hsubst.
  - intros Gamma function argument domain codomain latent
        Phi_function Phi_argument
        Hfunction IHfunction Hargument IHargument Delta sigma Hsubst. simpl.
    apply TyApp with (domain := domain) (latent := latent).
    + apply IHfunction. exact Hsubst.
    + apply IHargument. exact Hsubst.
  - intros Gamma e T U Phi Htyping IHtyping Hsub Delta sigma Hsubst.
    apply TySub with (T := T).
    + apply IHtyping. exact Hsubst.
    + exact Hsub.
  - intros Gamma Delta sigma Hsubst. simpl. constructor.
  - intros Gamma e expressions T types Phi effects
        Hhead IHhead Htail IHtail Delta sigma Hsubst. simpl.
    constructor.
    + apply IHhead. exact Hsubst.
    + apply IHtail. exact Hsubst.
Qed.

(** Convenient main-judgment form of simultaneous substitution. *)
Theorem typing_substitution :
  forall Gamma Delta sigma e T Phi,
    context_substitution sigma Gamma Delta ->
    has_type Gamma e T Phi ->
    has_type Delta (subst sigma e) T Phi.
Proof.
  intros Gamma Delta sigma e T Phi Hsubst Htyping.
  destruct typing_substitution_mut as [Hmain _].
  eapply Hmain; eauto.
Qed.

(** Substituting for the nearest binder preserves the body's type and effect.
    The replacement may have a more precise type than the binder annotation;
    subsumption first widens it to the annotated type. *)
Theorem typing_subst0 :
  forall Gamma replacement body replacement_ty parameter_ty result_ty Phi,
    has_type Gamma replacement replacement_ty [] ->
    replacement_ty <: parameter_ty ->
    has_type (parameter_ty :: Gamma) body result_ty Phi ->
    has_type Gamma (subst0 replacement body) result_ty Phi.
Proof.
  intros Gamma replacement body replacement_ty parameter_ty result_ty Phi
    Hreplacement Hsub Hbody.
  assert (has_type Gamma replacement parameter_ty []) as Hreplacement'.
  { eapply TySub; eauto. }
  unfold subst0.
  eapply typing_substitution; [|exact Hbody].
  intros index T Hlookup. destruct index as [|index']; simpl in *.
  - inversion Hlookup; subst. exact Hreplacement'.
  - apply TyVar. exact Hlookup.
Qed.

(** The source-language form of the substitution theorem additionally records
    that replacing a source term in a source body cannot introduce [ERunning]. *)
Corollary source_typing_subst0 :
  forall Gamma replacement body replacement_ty parameter_ty result_ty Phi,
    source_has_type Gamma replacement replacement_ty [] ->
    replacement_ty <: parameter_ty ->
    source_has_type (parameter_ty :: Gamma) body result_ty Phi ->
    source_has_type Gamma (subst0 replacement body) result_ty Phi.
Proof.
  intros Gamma replacement body replacement_ty parameter_ty result_ty Phi
    [Hreplacement_source Hreplacement_type] Hsub
    [Hbody_source Hbody_type].
  split.
  - apply subst0_preserves_source; assumption.
  - eapply typing_subst0; eauto.
Qed.

(** Typing a term in [Gamma] guarantees that every free de Bruijn index is
    bounded by the length of [Gamma]. The list half is the corresponding fact
    for parallel branches and tuple components. *)
Lemma typing_implies_scoped_mut :
  (forall Gamma e T Phi,
      has_type Gamma e T Phi ->
      scoped (length Gamma) e) /\
  (forall Gamma expressions types effects,
      expressions_have_types Gamma expressions types effects ->
      Forall (scoped (length Gamma)) expressions).
Proof.
  apply typing_mutind.
  - intros Gamma index T Hlookup. apply ScVar.
    apply nth_error_Some. rewrite Hlookup. discriminate.
  - intros Gamma. constructor.
  - intros Gamma n. constructor.
  - intros Gamma components component_types Hvalues Htypes IHtypes.
    apply ScTuple. exact IHtypes.
  - intros Gamma size timeout Hparameters. constructor.
  - intros Gamma size timeout Hparameters. constructor.
  - intros Gamma bound body bound_ty body_ty Phi_bound Phi_body
        Hbound IHbound Hbody IHbody.
    apply ScLet.
    + exact IHbound.
    + simpl in IHbody. exact IHbody.
  - intros Gamma guard zero_branch nonzero_branch branch_ty
        Phi_guard Phi_zero Phi_nonzero
        Hguard IHguard Hzero IHzero Hnonzero IHnonzero.
    constructor; assumption.
  - intros Gamma branches branch_types branch_effects Hbranches IHbranches.
    constructor. exact IHbranches.
  - intros Gamma parameter_ty body result_ty Phi_body Hbody IHbody.
    apply ScLambda. simpl in IHbody. exact IHbody.
  - intros Gamma function argument domain codomain latent
        Phi_function Phi_argument
        Hfunction IHfunction Hargument IHargument.
    constructor; assumption.
  - intros Gamma e T U Phi Htyping IHtyping Hsub. exact IHtyping.
  - intros Gamma. constructor.
  - intros Gamma e expressions T types Phi effects
        Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

(** Main-judgment form: typing determines the ambient scoping bound. *)
Theorem typing_implies_scoped :
  forall Gamma e T Phi,
    has_type Gamma e T Phi ->
    scoped (length Gamma) e.
Proof.
  intros Gamma e T Phi Htyping.
  destruct typing_implies_scoped_mut as [Hmain _].
  apply Hmain with (T := T) (Phi := Phi). exact Htyping.
Qed.

(** A closed typing derivation therefore contains no free variables. *)
Corollary closed_typing_is_closed :
  forall e T Phi,
    has_type [] e T Phi ->
    closed e.
Proof.
  intros e T Phi Htyping.
  apply typing_implies_scoped in Htyping. exact Htyping.
Qed.

(** Every typed expression belongs to the runtime grammar. The tuple case uses
    its explicit value premise in addition to recursively typed components. *)
Lemma typing_implies_runtime_wf_mut :
  (forall Gamma e T Phi,
      has_type Gamma e T Phi ->
      runtime_wf e) /\
  (forall Gamma expressions types effects,
      expressions_have_types Gamma expressions types effects ->
      Forall runtime_wf expressions).
Proof.
  apply typing_mutind.
  - intros Gamma index T Hlookup. constructor.
  - intros Gamma. constructor.
  - intros Gamma n. constructor.
  - intros Gamma components component_types Hvalues Htypes IHtypes.
    apply RtTuple; assumption.
  - intros Gamma size timeout Hparameters. constructor.
  - intros Gamma size timeout Hparameters. constructor.
  - intros Gamma bound body bound_ty body_ty Phi_bound Phi_body
        Hbound IHbound Hbody IHbody.
    constructor; assumption.
  - intros Gamma guard zero_branch nonzero_branch branch_ty
        Phi_guard Phi_zero Phi_nonzero
        Hguard IHguard Hzero IHzero Hnonzero IHnonzero.
    constructor; assumption.
  - intros Gamma branches branch_types branch_effects Hbranches IHbranches.
    constructor. exact IHbranches.
  - intros Gamma parameter_ty body result_ty Phi_body Hbody IHbody.
    constructor. exact IHbody.
  - intros Gamma function argument domain codomain latent
        Phi_function Phi_argument
        Hfunction IHfunction Hargument IHargument.
    constructor; assumption.
  - intros Gamma e T U Phi Htyping IHtyping Hsub. exact IHtyping.
  - intros Gamma. constructor.
  - intros Gamma e expressions T types Phi effects
        Hhead IHhead Htail IHtail.
    constructor; assumption.
Qed.

(** Main-judgment form of runtime grammatical well-formedness. *)
Theorem typing_implies_runtime_wf :
  forall Gamma e T Phi,
    has_type Gamma e T Phi ->
    runtime_wf e.
Proof.
  intros Gamma e T Phi Htyping.
  destruct typing_implies_runtime_wf_mut as [Hmain _].
  eapply Hmain; eauto.
Qed.

(** Values never have an immediate effect. Lambda-body effects are latent in
    their arrow types, and tuple components are required to have empty effects. *)
Lemma value_typing_empty_effect_mut :
  (forall Gamma e T Phi,
      has_type Gamma e T Phi ->
      value e ->
      Phi = []) /\
  (forall Gamma expressions types effects,
      expressions_have_types Gamma expressions types effects -> True).
Proof.
  apply typing_mutind.
  - intros Gamma index T Hlookup Hvalue. inversion Hvalue.
  - intros Gamma Hvalue. reflexivity.
  - intros Gamma n Hvalue. reflexivity.
  - intros Gamma components component_types Hvalues Htypes IHtypes Hvalue.
    reflexivity.
  - intros Gamma size timeout Hparameters Hvalue. inversion Hvalue.
  - intros Gamma size timeout Hparameters Hvalue. inversion Hvalue.
  - intros Gamma bound body bound_ty body_ty Phi_bound Phi_body
        Hbound IHbound Hbody IHbody Hvalue.
    inversion Hvalue.
  - intros Gamma guard zero_branch nonzero_branch branch_ty
        Phi_guard Phi_zero Phi_nonzero
        Hguard IHguard Hzero IHzero Hnonzero IHnonzero Hvalue.
    inversion Hvalue.
  - intros Gamma branches branch_types branch_effects
        Hbranches IHbranches Hvalue.
    inversion Hvalue.
  - intros Gamma parameter_ty body result_ty Phi_body Hbody IHbody Hvalue.
    reflexivity.
  - intros Gamma function argument domain codomain latent
        Phi_function Phi_argument
        Hfunction IHfunction Hargument IHargument Hvalue.
    inversion Hvalue.
  - intros Gamma e T U Phi Htyping IHtyping Hsub Hvalue.
    apply IHtyping. exact Hvalue.
  - intros Gamma. exact I.
  - intros Gamma e expressions T types Phi effects
        Hhead IHhead Htail IHtail. exact I.
Qed.

(** Main-judgment form of the value-effect inversion lemma used by beta and let
    preservation. *)
Theorem value_typing_empty_effect :
  forall Gamma value_expression T Phi,
    value value_expression ->
    has_type Gamma value_expression T Phi ->
    Phi = [].
Proof.
  intros Gamma value_expression T Phi Hvalue Htyping.
  destruct value_typing_empty_effect_mut as [Hmain _].
  eapply Hmain; eauto.
Qed.
