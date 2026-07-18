(** Type preservation with decreasing effects and active-effect coverage.

    Subsumption may appear any number of times at the root of a typing
    derivation. We therefore expose a syntax-directed root rule together with
    an explicit chain of subtype steps. This is the mechanized counterpart of
    the paper's "generation modulo subtyping" argument. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import
  Effects Normalization Syntax Substitution Typing Semantics ActiveWF
  ActiveEffects.

Import ListNotations.
Open Scope Q_scope.

(** Reflexive-transitive subtype chains record repeated uses of [TySub]
    without adding a transitivity constructor to the declarative subtype
    relation itself. *)
Inductive subtype_chain : ty -> ty -> Prop :=
| SubChainRefl : forall T,
    subtype_chain T T
| SubChainStep : forall T U V,
    T <: U ->
    subtype_chain U V ->
    subtype_chain T V.

(** A single structural subtype step is also a subtype chain. *)
Lemma subtype_chain_single :
  forall T U,
    T <: U ->
    subtype_chain T U.
Proof.
  intros T U Hsub. eapply SubChainStep.
  - exact Hsub.
  - constructor.
Qed.

(** Subtype chains compose transitively. *)
Lemma subtype_chain_trans :
  forall T U V,
    subtype_chain T U ->
    subtype_chain U V ->
    subtype_chain T V.
Proof.
  intros T U V HTU. revert V.
  induction HTU; intros V' HUV.
  - exact HUV.
  - eapply SubChainStep.
    + exact H.
    + apply IHHTU. exact HUV.
Qed.

(** A typing derivation may be widened along any subtype chain by replaying
    [TySub] at each link. *)
Lemma typing_subtype_chain :
  forall Gamma e T U Phi,
    has_type Gamma e T Phi ->
    subtype_chain T U ->
    has_type Gamma e U Phi.
Proof.
  intros Gamma e T U Phi Htyping Hchain.
  induction Hchain.
  - exact Htyping.
  - apply IHHchain. eapply TySub; eauto.
Qed.

(** Arrow subtyping chains invert pointwise: domains run contravariantly,
    latent effects grow by coverage, and codomains run covariantly. *)
Lemma subtype_chain_arrow_inv :
  forall domain latent codomain domain' latent' codomain',
    subtype_chain
      (TyArrow domain latent codomain)
      (TyArrow domain' latent' codomain') ->
    subtype_chain domain' domain /\
    latent ≼ latent' /\
    subtype_chain codomain codomain'.
Proof.
  fix IH 7.
  intros domain latent codomain domain' latent' codomain' Hchain.
  inversion Hchain as [T|T U V Hsub Htail]; subst.
  - repeat split; try constructor.
    apply effect_le_refl.
  - inversion Hsub; subst.
    destruct (IH _ _ _ _ _ _ Htail)
      as [Hdomain [Heffect Hcodomain]].
    split.
    + eapply subtype_chain_trans.
      * exact Hdomain.
      * apply subtype_chain_single. eassumption.
    + split.
      * eapply effect_le_trans; eauto.
      * eapply subtype_chain_trans.
        -- apply subtype_chain_single. eassumption.
        -- exact Hcodomain.
Qed.

(** A syntax-directed root typing rule is one whose last rule is not [TySub].
    Its premises remain ordinary declarative typings, so subsumption is still
    available recursively inside the expression. *)
Inductive root_has_type : context -> expr -> ty -> effect -> Prop :=
| RootVar : forall Gamma index T,
    lookup Gamma index T ->
    root_has_type Gamma (EVar index) T []
| RootUnit : forall Gamma,
    root_has_type Gamma EUnit Syntax.TyUnit []
| RootNat : forall Gamma n,
    root_has_type Gamma (ENat n) Syntax.TyNat []
| RootTuple : forall Gamma components component_types,
    Forall value components ->
    expressions_have_types
      Gamma components component_types (repeat [] (length components)) ->
    root_has_type Gamma (ETuple components) (TyProduct component_types) []
| RootDownload : forall Gamma size timeout,
    download_parameters_wf size timeout ->
    root_has_type Gamma (EDownload size timeout) Syntax.TyUnit
      (download_effect size timeout)
| RootRunning : forall Gamma size timeout,
    download_parameters_wf size timeout ->
    root_has_type Gamma (ERunning size timeout) Syntax.TyUnit
      (download_effect size timeout)
| RootLet : forall Gamma bound body bound_ty body_ty Phi_bound Phi_body,
    has_type Gamma bound bound_ty Phi_bound ->
    has_type (bound_ty :: Gamma) body body_ty Phi_body ->
    root_has_type Gamma (ELet bound body) body_ty
      (sequential_effect Phi_bound Phi_body)
| RootIfZero : forall Gamma guard zero_branch nonzero_branch
                     branch_ty Phi_guard Phi_zero Phi_nonzero,
    has_type Gamma guard Syntax.TyNat Phi_guard ->
    has_type Gamma zero_branch branch_ty Phi_zero ->
    has_type Gamma nonzero_branch branch_ty Phi_nonzero ->
    root_has_type Gamma (EIfZero guard zero_branch nonzero_branch) branch_ty
      (sequential_effect Phi_guard
        (sequential_effect Phi_zero Phi_nonzero))
| RootParallel : forall Gamma branches branch_types branch_effects,
    expressions_have_types Gamma branches branch_types branch_effects ->
    root_has_type Gamma (EParallel branches) (TyProduct branch_types)
      (parallel_effects branch_effects)
| RootAbs : forall Gamma parameter_ty body result_ty Phi_body,
    has_type (parameter_ty :: Gamma) body result_ty Phi_body ->
    root_has_type Gamma (ELambda parameter_ty body)
      (TyArrow parameter_ty Phi_body result_ty) []
| RootApp : forall Gamma function argument domain codomain
                   latent Phi_function Phi_argument,
    has_type Gamma function (TyArrow domain latent codomain) Phi_function ->
    has_type Gamma argument domain Phi_argument ->
    root_has_type Gamma (EApp function argument) codomain
      (sequential_effect Phi_function
        (sequential_effect Phi_argument latent)).

(** Every root judgment is an ordinary declarative typing judgment. *)
Lemma root_has_type_is_typing :
  forall Gamma e T Phi,
    root_has_type Gamma e T Phi ->
    has_type Gamma e T Phi.
Proof.
  intros Gamma e T Phi Hroot. destruct Hroot.
  - eapply TyVar; eauto.
  - apply Typing.TyUnit.
  - apply Typing.TyNat.
  - eapply TyTuple; eauto.
  - eapply TyDownload; eauto.
  - eapply TyRunning; eauto.
  - eapply TyLet; eauto.
  - eapply TyIfZero; eauto.
  - eapply TyParallel; eauto.
  - eapply TyAbs; eauto.
  - eapply TyApp; eauto.
Qed.

(** Generation modulo subsumption: every typing has a syntax-directed root
    result that reaches the assigned type through a subtype chain. *)
Theorem typing_generation :
  forall Gamma e T Phi,
    has_type Gamma e T Phi ->
    exists root_type,
      root_has_type Gamma e root_type Phi /\
      subtype_chain root_type T.
Proof.
  intros Gamma e T Phi Htyping. induction Htyping.
  - exists T. split; [eapply RootVar; eauto | constructor].
  - exists Syntax.TyUnit. split; [constructor | constructor].
  - exists Syntax.TyNat. split; [constructor | constructor].
  - exists (TyProduct component_types). split.
    + eapply RootTuple; eauto.
    + constructor.
  - exists Syntax.TyUnit. split; [eapply RootDownload; eauto | constructor].
  - exists Syntax.TyUnit. split; [eapply RootRunning; eauto | constructor].
  - exists body_ty. split; [eapply RootLet; eauto | constructor].
  - exists branch_ty. split; [eapply RootIfZero; eauto | constructor].
  - exists (TyProduct branch_types). split.
    + eapply RootParallel; eauto.
    + constructor.
  - exists (TyArrow parameter_ty Phi_body result_ty).
    split; [eapply RootAbs; eauto | constructor].
  - exists codomain. split; [eapply RootApp; eauto | constructor].
  - destruct IHHtyping as [root_type [Hroot Hchain]].
    exists root_type. split.
    + exact Hroot.
    + eapply subtype_chain_trans.
      * exact Hchain.
      * apply subtype_chain_single. exact H.
Qed.

(** Generation for let expressions. *)
Lemma typing_let_generation :
  forall Gamma bound body T Phi,
    has_type Gamma (ELet bound body) T Phi ->
    exists bound_ty body_ty Phi_bound Phi_body,
      has_type Gamma bound bound_ty Phi_bound /\
      has_type (bound_ty :: Gamma) body body_ty Phi_body /\
      subtype_chain body_ty T /\
      Phi = sequential_effect Phi_bound Phi_body.
Proof.
  intros Gamma bound body T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. eauto 12.
Qed.

(** Generation for applications. *)
Lemma typing_app_generation :
  forall Gamma function argument T Phi,
    has_type Gamma (EApp function argument) T Phi ->
    exists domain codomain latent Phi_function Phi_argument,
      has_type Gamma function (TyArrow domain latent codomain) Phi_function /\
      has_type Gamma argument domain Phi_argument /\
      subtype_chain codomain T /\
      Phi = sequential_effect Phi_function
        (sequential_effect Phi_argument latent).
Proof.
  intros Gamma function argument T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. eauto 12.
Qed.

(** Generation for lambda abstractions. *)
Lemma typing_abs_generation :
  forall Gamma parameter_ty body T Phi,
    has_type Gamma (ELambda parameter_ty body) T Phi ->
    exists result_ty Phi_body,
      has_type (parameter_ty :: Gamma) body result_ty Phi_body /\
      subtype_chain
        (TyArrow parameter_ty Phi_body result_ty) T /\
      Phi = [].
Proof.
  intros Gamma parameter_ty body T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. eauto 8.
Qed.

(** Generation for conditionals. *)
Lemma typing_if_generation :
  forall Gamma guard zero_branch nonzero_branch T Phi,
    has_type Gamma (EIfZero guard zero_branch nonzero_branch) T Phi ->
    exists branch_ty Phi_guard Phi_zero Phi_nonzero,
      has_type Gamma guard Syntax.TyNat Phi_guard /\
      has_type Gamma zero_branch branch_ty Phi_zero /\
      has_type Gamma nonzero_branch branch_ty Phi_nonzero /\
      subtype_chain branch_ty T /\
      Phi = sequential_effect Phi_guard
        (sequential_effect Phi_zero Phi_nonzero).
Proof.
  intros Gamma guard zero_branch nonzero_branch T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. eauto 12.
Qed.

(** Generation for parallel expressions. *)
Lemma typing_parallel_generation :
  forall Gamma branches T Phi,
    has_type Gamma (EParallel branches) T Phi ->
    exists branch_types branch_effects,
      expressions_have_types Gamma branches branch_types branch_effects /\
      subtype_chain (TyProduct branch_types) T /\
      Phi = parallel_effects branch_effects.
Proof.
  intros Gamma branches T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. eauto 8.
Qed.

(** Generation for a source download. *)
Lemma typing_download_generation :
  forall Gamma size timeout T Phi,
    has_type Gamma (EDownload size timeout) T Phi ->
    download_parameters_wf size timeout /\
    subtype_chain Syntax.TyUnit T /\
    Phi = download_effect size timeout.
Proof.
  intros Gamma size timeout T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. eauto.
Qed.

(** Generation for a runtime running download. *)
Lemma typing_running_generation :
  forall Gamma size timeout T Phi,
    has_type Gamma (ERunning size timeout) T Phi ->
    download_parameters_wf size timeout /\
    subtype_chain Syntax.TyUnit T /\
    Phi = download_effect size timeout.
Proof.
  intros Gamma size timeout T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. eauto.
Qed.

(** Each operand is covered by its normalized sequential composition. *)
Lemma sequential_effect_le_left :
  forall Phi Psi,
    Phi ≼ sequential_effect Phi Psi.
Proof.
  intros Phi Psi. unfold sequential_effect.
  eapply effect_le_trans; [apply effect_le_join_l | apply le_normalize].
Qed.

Lemma sequential_effect_le_right :
  forall Phi Psi,
    Psi ≼ sequential_effect Phi Psi.
Proof.
  intros Phi Psi. unfold sequential_effect.
  eapply effect_le_trans; [apply effect_le_join_r | apply le_normalize].
Qed.

(** Aligned typing of a list of values forces every immediate branch effect to
    be empty. *)
Lemma typed_values_effects_empty :
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

(** Split aligned list typing around a distinguished middle expression. *)
Lemma expressions_have_types_split :
  forall Gamma prefix branch suffix types effects,
    expressions_have_types
      Gamma (prefix ++ branch :: suffix) types effects ->
    exists prefix_types branch_type suffix_types
           prefix_effects branch_effect suffix_effects,
      types = prefix_types ++ branch_type :: suffix_types /\
      effects = prefix_effects ++ branch_effect :: suffix_effects /\
      expressions_have_types Gamma prefix prefix_types prefix_effects /\
      has_type Gamma branch branch_type branch_effect /\
      expressions_have_types Gamma suffix suffix_types suffix_effects.
Proof.
  intros Gamma prefix. induction prefix as [|head prefix IH];
    intros branch suffix types effects Htypes; simpl in Htypes.
  - inversion Htypes as
      [|Gamma' e expressions T0 types0 Phi0 effects0 Hbranch Hsuffix];
      subst.
    exists [], T0, types0, [], Phi0, effects0.
    repeat split; try reflexivity.
    + constructor.
    + exact Hbranch.
    + exact Hsuffix.
  - inversion Htypes as
      [|Gamma' e expressions T0 types0 Phi0 effects0 Hhead Htail];
      subst.
    destruct (IH _ _ _ _ Htail)
      as (prefix_types & branch_type & suffix_types &
          prefix_effects & branch_effect & suffix_effects &
          Htypes_eq & Heffects_eq & Hprefix & Hbranch & Hsuffix).
    subst types0 effects0.
    exists (T0 :: prefix_types), branch_type, suffix_types,
      (Phi0 :: prefix_effects), branch_effect, suffix_effects.
    repeat split; try assumption.
    constructor; assumption.
Qed.

(** Reassemble aligned list typing from a prefix, one middle expression, and a
    suffix. *)
Lemma expressions_have_types_middle :
  forall Gamma prefix branch suffix prefix_types branch_type suffix_types
         prefix_effects branch_effect suffix_effects,
    expressions_have_types Gamma prefix prefix_types prefix_effects ->
    has_type Gamma branch branch_type branch_effect ->
    expressions_have_types Gamma suffix suffix_types suffix_effects ->
    expressions_have_types Gamma
      (prefix ++ branch :: suffix)
      (prefix_types ++ branch_type :: suffix_types)
      (prefix_effects ++ branch_effect :: suffix_effects).
Proof.
  intros Gamma prefix branch suffix prefix_types branch_type suffix_types
    prefix_effects branch_effect suffix_effects Hprefix Hbranch Hsuffix.
  induction Hprefix; simpl.
  - constructor; assumption.
  - constructor.
    + assumption.
    + exact (IHHprefix Hbranch Hsuffix).
Qed.

(** Decreasing one branch effect decreases the right-associated parallel fold
    while every other branch effect remains unchanged. *)
Lemma parallel_effects_replace_middle_mono :
  forall prefix Phi Phi' suffix,
    Phi' ≼ Phi ->
    parallel_effects (prefix ++ Phi' :: suffix)
    ≼ parallel_effects (prefix ++ Phi :: suffix).
Proof.
  intros prefix. induction prefix as [|head prefix IH];
    intros Phi Phi' suffix Hle; simpl.
  - apply parallel_effect_mono.
    + exact Hle.
    + apply effect_le_refl.
  - apply parallel_effect_mono.
    + apply effect_le_refl.
    + apply IH. exact Hle.
Qed.

(** Extend preservation to arbitrary transition endpoints. Error targets carry
    no expression to type, so only successful expression-to-expression steps
    produce a proof obligation. *)
Definition typing_preservation_transition
    (source target : configuration) : Prop :=
  match source, target with
  | Config e _, Config e' _ =>
      forall Gamma T Phi,
        has_type Gamma e T Phi ->
        exists Phi',
          has_type Gamma e' T Phi' /\
          Phi' ≼ Phi
  | _, _ => True
  end.

(** General transition form of preservation with decreasing effects. *)
Lemma preservation_decreasing_effects_general :
  forall B source target,
    step B source target ->
    typing_preservation_transition source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl.
  all: try (intros Gamma T Phi Htyping).
  - destruct (typing_let_generation _ _ _ _ _ Htyping)
      as [bound_ty [body_ty [Phi_bound [Phi_body
        [Hbound [Hbody [Hsub Hphi]]]]]]].
    subst Phi.
    pose proof (value_typing_empty_effect _ _ _ _ H Hbound) as Heffect.
    subst Phi_bound. exists Phi_body. split.
    + apply typing_subtype_chain with (T := body_ty); [|exact Hsub].
      eapply typing_subst0.
      * exact Hbound.
      * apply subtype_refl.
      * exact Hbody.
    + apply sequential_effect_le_right.
  - destruct (typing_app_generation _ _ _ _ _ Htyping)
      as [domain [codomain [latent [Phi_function [Phi_argument
        [Hfunction [Hargument [Hresult Hphi]]]]]]]].
    subst Phi.
    pose proof
      (value_typing_empty_effect _ _ _ _ (VLambda parameter_ty body)
        Hfunction) as Hfunction_effect.
    pose proof
      (value_typing_empty_effect _ _ _ _ H Hargument) as Hargument_effect.
    subst Phi_function Phi_argument.
    destruct (typing_abs_generation _ _ _ _ _ Hfunction)
      as [body_ty [Phi_body [Hbody [Harrow _]]]].
    destruct (subtype_chain_arrow_inv _ _ _ _ _ _ Harrow)
      as [Hdomain [Hlatent Hcodomain]].
    assert (Hargument_parameter :
      has_type Gamma argument parameter_ty []).
    { eapply typing_subtype_chain; eauto. }
    exists Phi_body. split.
    + apply typing_subtype_chain with (T := body_ty).
      * eapply typing_subst0.
        -- exact Hargument_parameter.
        -- apply subtype_refl.
        -- exact Hbody.
      * eapply subtype_chain_trans; eauto.
    + eapply effect_le_trans.
      * exact Hlatent.
      * eapply effect_le_trans.
        -- apply sequential_effect_le_right.
        -- apply sequential_effect_le_right.
  - destruct (typing_if_generation _ _ _ _ _ _ Htyping)
      as [branch_ty [Phi_guard [Phi_zero [Phi_nonzero
        [Hguard [Hzero [Hnonzero [Hsub Hphi]]]]]]]].
    subst Phi. exists Phi_zero. split.
    + eapply typing_subtype_chain; eauto.
    + eapply effect_le_trans.
      * apply sequential_effect_le_left.
      * apply sequential_effect_le_right.
  - destruct (typing_if_generation _ _ _ _ _ _ Htyping)
      as [branch_ty [Phi_guard [Phi_zero [Phi_nonzero
        [Hguard [Hzero [Hnonzero [Hsub Hphi]]]]]]]].
    subst Phi. exists Phi_nonzero. split.
    + eapply typing_subtype_chain; eauto.
    + eapply effect_le_trans.
      * apply sequential_effect_le_right.
      * apply sequential_effect_le_right.
  - destruct (typing_parallel_generation _ _ _ _ Htyping)
      as [branch_types [branch_effects [Hbranches [Hsub Hphi]]]].
    subst Phi.
    pose proof
      (typed_values_effects_empty _ _ _ _ Hbranches H) as Heffects.
    subst branch_effects. exists []. split.
    + apply typing_subtype_chain with (T := TyProduct branch_types).
      * apply TyTuple; assumption.
      * exact Hsub.
    + apply empty_effect_le.
  - destruct (typing_download_generation _ _ _ _ _ Htyping)
      as [Hparameters [Hsub Hphi]].
    subst Phi. exists (download_effect size timeout). split.
    + apply typing_subtype_chain with (T := Syntax.TyUnit).
      * constructor. exact Hparameters.
      * exact Hsub.
    + apply effect_le_refl.
  - destruct (typing_running_generation _ _ _ _ _ Htyping)
      as [Hparameters [Hsub Hphi]].
    subst Phi. exists []. split.
    + apply typing_subtype_chain with (T := Syntax.TyUnit).
      * constructor.
      * exact Hsub.
    + apply empty_effect_le.
  - exact I.
  - destruct (typing_let_generation _ _ _ _ _ Htyping)
      as [bound_ty [body_ty [Phi_bound [Phi_body
        [Hbound [Hbody [Hsub Hphi]]]]]]].
    subst Phi.
    destruct (IHHstep _ _ _ Hbound) as [Phi_bound' [Hbound' Hle]].
    exists (sequential_effect Phi_bound' Phi_body). split.
    + apply typing_subtype_chain with (T := body_ty).
      * eapply TyLet; eauto.
      * exact Hsub.
    + apply sequential_effect_mono; [exact Hle | apply effect_le_refl].
  - destruct (typing_app_generation _ _ _ _ _ Htyping)
      as [domain [codomain [latent [Phi_function [Phi_argument
        [Hfunction [Hargument [Hsub Hphi]]]]]]]].
    subst Phi.
    destruct (IHHstep _ _ _ Hfunction)
      as [Phi_function' [Hfunction' Hle]].
    exists (sequential_effect Phi_function'
      (sequential_effect Phi_argument latent)). split.
    + apply typing_subtype_chain with (T := codomain).
      * eapply TyApp; eauto.
      * exact Hsub.
    + apply sequential_effect_mono.
      * exact Hle.
      * apply effect_le_refl.
  - destruct (typing_app_generation _ _ _ _ _ Htyping)
      as [domain [codomain [latent [Phi_function [Phi_argument
        [Hfunction [Hargument [Hsub Hphi]]]]]]]].
    subst Phi.
    destruct (IHHstep _ _ _ Hargument)
      as [Phi_argument' [Hargument' Hle]].
    exists (sequential_effect Phi_function
      (sequential_effect Phi_argument' latent)). split.
    + apply typing_subtype_chain with (T := codomain).
      * eapply TyApp; eauto.
      * exact Hsub.
    + apply sequential_effect_mono.
      * apply effect_le_refl.
      * apply sequential_effect_mono; [exact Hle | apply effect_le_refl].
  - destruct (typing_if_generation _ _ _ _ _ _ Htyping)
      as [branch_ty [Phi_guard [Phi_zero [Phi_nonzero
        [Hguard [Hzero [Hnonzero [Hsub Hphi]]]]]]]].
    subst Phi.
    destruct (IHHstep _ _ _ Hguard) as [Phi_guard' [Hguard' Hle]].
    exists (sequential_effect Phi_guard'
      (sequential_effect Phi_zero Phi_nonzero)). split.
    + apply typing_subtype_chain with (T := branch_ty).
      * eapply TyIfZero; eauto.
      * exact Hsub.
    + apply sequential_effect_mono; [exact Hle | apply effect_le_refl].
  - destruct (typing_parallel_generation _ _ _ _ Htyping)
      as [branch_types [branch_effects [Hbranches [Hsub Hphi]]]].
    subst Phi.
    destruct (expressions_have_types_split _ _ _ _ _ _ Hbranches)
      as (prefix_types & branch_type & suffix_types &
          prefix_effects & branch_effect & suffix_effects &
          Htypes_eq & Heffects_eq & Hprefix & Hbranch & Hsuffix).
    subst branch_types branch_effects.
    destruct (IHHstep _ _ _ Hbranch) as [branch_effect' [Hbranch' Hle]].
    exists (parallel_effects
      (prefix_effects ++ branch_effect' :: suffix_effects)). split.
    + apply typing_subtype_chain with
        (T := TyProduct
          (prefix_types ++ branch_type :: suffix_types)).
      * apply TyParallel. eapply expressions_have_types_middle; eauto.
      * exact Hsub.
    + apply parallel_effects_replace_middle_mono. exact Hle.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
Qed.

(** Direct successful-step statement from the paper: the assigned type is
    preserved and the new immediate effect is covered by the old one. *)
Theorem preservation_decreasing_effects :
  forall B e active e' active' Gamma T Phi,
    step B (Config e active) (Config e' active') ->
    has_type Gamma e T Phi ->
    exists Phi',
      has_type Gamma e' T Phi' /\
      Phi' ≼ Phi.
Proof.
  intros B e active e' active' Gamma T Phi Hstep Htyping.
  pose proof
    (preservation_decreasing_effects_general B _ _ Hstep) as Hpreserves.
  simpl in Hpreserves. eapply Hpreserves. exact Htyping.
Qed.

(** Preservation iterated over a successful execution prefix. The final
    effect remains covered by the initial effect. *)
Theorem preservation_successful_steps :
  forall B source source_active target target_active Gamma T Phi,
    successful_steps B source source_active target target_active ->
    has_type Gamma source T Phi ->
    exists Phi',
      has_type Gamma target T Phi' /\
      Phi' ≼ Phi.
Proof.
  intros B source source_active target target_active Gamma T Phi Hsteps.
  induction Hsteps; intros Htyping.
  - exists Phi. split; [exact Htyping | apply effect_le_refl].
  - destruct (IHHsteps Htyping) as [Phi_middle [Hmiddle Hmiddle_le]].
    destruct (preservation_decreasing_effects
      _ _ _ _ _ _ _ _ H Hmiddle) as [Phi_target [Htarget Htarget_le]].
    exists Phi_target. split.
    + exact Htarget.
    + eapply effect_le_trans; eauto.
Qed.

(** Local active-effect coverage and its aligned-list companion are proved
    together. The list statement is exactly the finite-parallel case needed by
    [TyParallel]. *)
Lemma local_active_effect_coverage_mut :
  (forall Gamma e T Phi,
      has_type Gamma e T Phi ->
      active_wf e ->
      active_effect (running_rates e) ≼ Phi) /\
  (forall Gamma expressions types effects,
      expressions_have_types Gamma expressions types effects ->
      Forall active_wf expressions ->
      active_effect (concat (map running_rates expressions))
      ≼ parallel_effects effects).
Proof.
  apply typing_mutind.
  - intros Gamma index T Hlookup Hactive. simpl. apply empty_effect_le.
  - intros Gamma Hactive. simpl. apply empty_effect_le.
  - intros Gamma n Hactive. simpl. apply empty_effect_le.
  - intros Gamma components component_types Hvalues Htypes IHtypes Hactive.
    simpl. apply empty_effect_le.
  - intros Gamma size timeout Hparameters Hactive.
    simpl. apply empty_effect_le.
  - intros Gamma size timeout Hparameters Hactive.
    simpl. apply effect_le_refl.
  - intros Gamma bound body bound_ty body_ty Phi_bound Phi_body
      Hbound IHbound Hbody IHbody Hactive.
    inversion Hactive; subst. simpl.
    match goal with Hbody_no_run : no_run body |- _ =>
      rewrite (no_run_running_rates_empty _ Hbody_no_run), app_nil_r
    end.
    eapply effect_le_trans.
    + apply IHbound. assumption.
    + apply sequential_effect_le_left.
  - intros Gamma guard zero_branch nonzero_branch branch_ty
      Phi_guard Phi_zero Phi_nonzero
      Hguard IHguard Hzero IHzero Hnonzero IHnonzero Hactive.
    inversion Hactive; subst. simpl.
    match goal with
    | Hzero_no_run : no_run zero_branch,
      Hnonzero_no_run : no_run nonzero_branch |- _ =>
        rewrite (no_run_running_rates_empty _ Hzero_no_run),
          (no_run_running_rates_empty _ Hnonzero_no_run), !app_nil_r
    end.
    eapply effect_le_trans.
    + apply IHguard. assumption.
    + apply sequential_effect_le_left.
  - intros Gamma branches branch_types branch_effects
      Hbranches IHbranches Hactive.
    inversion Hactive; subst. simpl. apply IHbranches. assumption.
  - intros Gamma parameter_ty body result_ty Phi_body Hbody IHbody Hactive.
    simpl. apply empty_effect_le.
  - intros Gamma function argument domain codomain latent
      Phi_function Phi_argument
      Hfunction IHfunction Hargument IHargument Hactive.
    inversion Hactive; subst; simpl.
    + match goal with Hargument_no_run : no_run argument |- _ =>
        rewrite (no_run_running_rates_empty _ Hargument_no_run), app_nil_r
      end.
      eapply effect_le_trans.
      * apply IHfunction. assumption.
      * apply sequential_effect_le_left.
    + match goal with Hfunction_no_run : no_run function |- _ =>
        rewrite (no_run_running_rates_empty _ Hfunction_no_run)
      end.
      eapply effect_le_trans.
      * apply IHargument. assumption.
      * eapply effect_le_trans.
        -- apply sequential_effect_le_left.
        -- apply sequential_effect_le_right.
  - intros Gamma e T U Phi Htyping IHtyping Hsub Hactive.
    apply IHtyping. exact Hactive.
  - intros Gamma Hactive. inversion Hactive. simpl. apply effect_le_refl.
  - intros Gamma e expressions T types Phi effects
      Hhead IHhead Htail IHtail Hactive.
    inversion Hactive; subst. simpl.
    eapply effect_le_trans.
    + apply active_effect_union.
    + apply parallel_effect_mono.
      * apply IHhead. assumption.
      * apply IHtail. assumption.
Qed.

(** Structural active-effect coverage: every actively well-formed typed runtime
    expression covers the obligations of all downloads currently exposed by
    the evaluation order. *)
Theorem local_active_effect_coverage :
  forall Gamma e T Phi,
    active_wf e ->
    has_type Gamma e T Phi ->
    active_effect (running_rates e) ≼ Phi.
Proof.
  intros Gamma e T Phi Hactive Htyping.
  destruct local_active_effect_coverage_mut as [Hmain _].
  eapply Hmain; eauto.
Qed.

(** Reachability from source syntax supplies [active_wf], so the local
    structural theorem applies to every successfully reachable typed state. *)
Theorem reachable_active_effect_coverage :
  forall B source target target_active Gamma T Phi,
    source_expr source ->
    successful_steps B source 0 target target_active ->
    has_type Gamma target T Phi ->
    active_effect (running_rates target) ≼ Phi.
Proof.
  intros B source target target_active Gamma T Phi
    Hsource Hsteps Htyping.
  eapply local_active_effect_coverage.
  - eapply reachable_source_active_wf; eauto.
  - exact Htyping.
Qed.
