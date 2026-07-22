(** Executable checks for the sample programs in the paper.

    These examples are deliberately stated against the public syntax, typing,
    effect, and bandwidth definitions.  They therefore act as regression tests:
    if the mechanization drifts away from the programs or calculations printed
    in the paper, this file will stop compiling.

    The paper uses [dl_r] as notation for an arbitrary download whose required
    rate is [r].  Here the terms use [EDownload] directly, choosing size [r]
    and timeout [1], so [download_rate r 1 = r].

    Numeric-carrier caveat: the paper presents sizes, timeouts, and rates over
    the reals, whereas the executable Rocq development uses rational numbers.
    The examples below all lie in that rational fragment. *)

From Stdlib Require Import List QArith.
From BandwidthTimeout Require Import
  Quantities Effects Normalization Bandwidth Syntax Typing Preservation.

Import ListNotations.
Open Scope Q_scope.

(** Checked quantities used by the concrete paper examples. *)
Definition paper_size_1 : nonnegative_rational.
Proof. refine (NonnegativeRational 1 _). vm_compute. discriminate. Defined.

Definition paper_size_2 : nonnegative_rational.
Proof. refine (NonnegativeRational 2 _). vm_compute. discriminate. Defined.

Definition paper_size_3 : nonnegative_rational.
Proof. refine (NonnegativeRational 3 _). vm_compute. discriminate. Defined.

Definition paper_size_10 : nonnegative_rational.
Proof. refine (NonnegativeRational 10 _). vm_compute. discriminate. Defined.

Definition paper_timeout_1 : positive_rational.
Proof. refine (PositiveRational 1 _). vm_compute. reflexivity. Defined.

(** The chosen size/timeout pairs really have the rates advertised by the
    paper's informal [dl_r] notation. *)
Example paper_rate_1 :
  download_rate paper_size_1 paper_timeout_1 = 1.
Proof. vm_compute. reflexivity. Qed.

Example paper_rate_2 :
  download_rate paper_size_2 paper_timeout_1 = 2.
Proof. vm_compute. reflexivity. Qed.

Example paper_rate_3 :
  download_rate paper_size_3 paper_timeout_1 = 3.
Proof. vm_compute. reflexivity. Qed.

Example paper_rate_10 :
  download_rate paper_size_10 paper_timeout_1 = 10.
Proof. vm_compute. reflexivity. Qed.

(** Paper example [e1]: one rate-10 download, followed sequentially by three
    parallel rate-1 downloads.  The let-bound variable is unused, so its body
    contains no de Bruijn variable. *)
Definition paper_e1 : expr :=
  ELet
    (EDownload paper_size_10 paper_timeout_1)
    (EParallel
      [EDownload paper_size_1 paper_timeout_1;
       EDownload paper_size_1 paper_timeout_1;
       EDownload paper_size_1 paper_timeout_1]).

Definition paper_e1_ty : ty :=
  TyProduct [Syntax.TyUnit; Syntax.TyUnit; Syntax.TyUnit].

Definition paper_e1_effect : effect :=
  [Obligation 10 1; Obligation 1 3].

(** The concrete Rocq AST for [e1] is a closed source program. *)
Example paper_e1_closed_source : closed_source paper_e1.
Proof.
  unfold closed_source, closed, paper_e1.
  split; repeat constructor.
Qed.

(** The effect operations compute exactly the pair set printed for [e1]. *)
Example paper_e1_effect_calculation :
  sequential_effect
    (download_effect paper_size_10 paper_timeout_1)
    (parallel_effects
      [download_effect paper_size_1 paper_timeout_1;
       download_effect paper_size_1 paper_timeout_1;
       download_effect paper_size_1 paper_timeout_1]) =
  paper_e1_effect.
Proof. vm_compute. reflexivity. Qed.

(** The paper's source typing judgment is derivable with that exact type and
    normalized effect. *)
Example paper_e1_typing :
  source_has_type [] paper_e1 paper_e1_ty paper_e1_effect.
Proof.
  split.
  - exact (proj1 paper_e1_closed_source).
  - rewrite <- paper_e1_effect_calculation.
    unfold paper_e1, paper_e1_ty.
    eapply TyLet with (bound_ty := Syntax.TyUnit).
    + apply TyDownload.
    + apply TyParallel.
      repeat constructor.
Qed.

(** Consequently, [e1] requires bandwidth 10 rather than the imprecise 30. *)
Example paper_e1_required_bandwidth :
  required_bandwidth paper_e1_effect = 10.
Proof. vm_compute. reflexivity. Qed.

(** Paper example [e2]: a rate-2 download in parallel with a nested parallel
    expression containing rate-3 and rate-2 downloads. *)
Definition paper_e2 : expr :=
  EParallel
    [EDownload paper_size_2 paper_timeout_1;
     EParallel
       [EDownload paper_size_3 paper_timeout_1;
        EDownload paper_size_2 paper_timeout_1]].

Definition paper_e2_ty : ty :=
  TyProduct
    [Syntax.TyUnit; TyProduct [Syntax.TyUnit; Syntax.TyUnit]].

Definition paper_e2_effect : effect :=
  [Obligation 3 3].

(** The concrete Rocq AST for [e2] is also a closed source program. *)
Example paper_e2_closed_source : closed_source paper_e2.
Proof.
  unfold closed_source, closed, paper_e2.
  split; repeat constructor.
Qed.

(** Nested parallel composition computes and normalizes to the singleton
    effect [(3,3)] stated in the paper. *)
Example paper_e2_effect_calculation :
  parallel_effects
    [download_effect paper_size_2 paper_timeout_1;
     parallel_effects
       [download_effect paper_size_3 paper_timeout_1;
        download_effect paper_size_2 paper_timeout_1]] =
  paper_e2_effect.
Proof. vm_compute. reflexivity. Qed.

(** The source typing judgment derives the nested product type and the exact
    normalized effect claimed for [e2]. *)
Example paper_e2_typing :
  source_has_type [] paper_e2 paper_e2_ty paper_e2_effect.
Proof.
  split.
  - exact (proj1 paper_e2_closed_source).
  - rewrite <- paper_e2_effect_calculation.
    unfold paper_e2, paper_e2_ty.
    apply TyParallel.
    repeat constructor.
Qed.

(** Hence the required bandwidth for [e2] is 9, not the bandwidth-only
    approximation 12 discussed in the paper. *)
Example paper_e2_required_bandwidth :
  required_bandwidth paper_e2_effect = 9.
Proof. vm_compute. reflexivity. Qed.

(** A deeper nested-parallel regression case.  The left child is [paper_e1],
    whose rate-10 download occurs in a sequential phase with local concurrency
    one.  The right child contains two parallel downloads.  In the outer
    parallel composition, the rate-10 obligation therefore rises to
    concurrency three, while the lower-rate obligations can reach five. *)
Definition nested_parallel_case : expr :=
  EParallel
    [paper_e1;
     EParallel
       [EDownload paper_size_3 paper_timeout_1;
        EDownload paper_size_2 paper_timeout_1]].

Definition nested_parallel_case_ty : ty :=
  TyProduct
    [paper_e1_ty;
     TyProduct [Syntax.TyUnit; Syntax.TyUnit]].

Definition nested_parallel_case_effect : effect :=
  [Obligation 10 3; Obligation 3 5].

Example nested_parallel_case_closed_source :
  closed_source nested_parallel_case.
Proof.
  unfold closed_source, closed, nested_parallel_case, paper_e1.
  split; repeat constructor.
Qed.

Example nested_parallel_case_effect_calculation :
  parallel_effects
    [paper_e1_effect;
     parallel_effects
       [download_effect paper_size_3 paper_timeout_1;
        download_effect paper_size_2 paper_timeout_1]] =
  nested_parallel_case_effect.
Proof. vm_compute. reflexivity. Qed.

Example nested_parallel_case_typing :
  source_has_type [] nested_parallel_case
    nested_parallel_case_ty nested_parallel_case_effect.
Proof.
  split.
  - exact (proj1 nested_parallel_case_closed_source).
  - rewrite <- nested_parallel_case_effect_calculation.
    unfold nested_parallel_case, nested_parallel_case_ty.
    apply TyParallel.
    constructor.
    + exact (proj2 paper_e1_typing).
    + constructor.
      * apply TyParallel. repeat constructor.
      * constructor.
Qed.

Example nested_parallel_case_required_bandwidth :
  required_bandwidth nested_parallel_case_effect = 30.
Proof. vm_compute. reflexivity. Qed.

(** A higher-order regression case:

      let f = (lambda (_ : unit). par(download 3 1, download 2 1)) in
      par(f unit, download 1 1)

    Merely creating [f] has empty effect.  Its two downloads are recorded in
    the arrow's latent effect; applying [f] exposes that effect, after which
    the outer parallel composition raises its concurrency from two to three. *)
Definition higher_order_latent_effect : effect :=
  [Obligation 3 2].

Definition higher_order_function_ty : ty :=
  TyArrow Syntax.TyUnit higher_order_latent_effect
    (TyProduct [Syntax.TyUnit; Syntax.TyUnit]).

Definition higher_order_case : expr :=
  ELet
    (ELambda Syntax.TyUnit
      (EParallel
        [EDownload paper_size_3 paper_timeout_1;
         EDownload paper_size_2 paper_timeout_1]))
    (EParallel
      [EApp (EVar 0) EUnit;
       EDownload paper_size_1 paper_timeout_1]).

Definition higher_order_case_ty : ty :=
  TyProduct
    [TyProduct [Syntax.TyUnit; Syntax.TyUnit]; Syntax.TyUnit].

Definition higher_order_case_effect : effect :=
  [Obligation 3 3].

Example higher_order_case_closed_source : closed_source higher_order_case.
Proof.
  unfold closed_source, closed, higher_order_case.
  split; repeat constructor.
Qed.

Example higher_order_latent_effect_calculation :
  parallel_effects
    [download_effect paper_size_3 paper_timeout_1;
     download_effect paper_size_2 paper_timeout_1] =
  higher_order_latent_effect.
Proof. vm_compute. reflexivity. Qed.

Example higher_order_case_effect_calculation :
  sequential_effect []
    (parallel_effects
      [sequential_effect [] (sequential_effect [] higher_order_latent_effect);
       download_effect paper_size_1 paper_timeout_1]) =
  higher_order_case_effect.
Proof. vm_compute. reflexivity. Qed.

Example higher_order_case_typing :
  source_has_type [] higher_order_case
    higher_order_case_ty higher_order_case_effect.
Proof.
  split.
  - exact (proj1 higher_order_case_closed_source).
  - rewrite <- higher_order_case_effect_calculation.
    unfold higher_order_case, higher_order_case_ty.
    eapply TyLet with (bound_ty := higher_order_function_ty).
    + unfold higher_order_function_ty.
      apply TyAbs.
      rewrite <- higher_order_latent_effect_calculation.
      apply TyParallel. repeat constructor.
    + apply TyParallel.
      constructor.
      * eapply TyApp with
          (domain := Syntax.TyUnit)
          (latent := higher_order_latent_effect).
        -- apply TyVar. reflexivity.
        -- apply TyUnit.
      * constructor.
        -- apply TyDownload.
        -- constructor.
Qed.

Example higher_order_case_required_bandwidth :
  required_bandwidth higher_order_case_effect = 9.
Proof. vm_compute. reflexivity. Qed.

(** A negative application regression case:

      (lambda (x : Nat). x) unit

    Both subexpressions are individually well typed, but the function domain
    is [Nat] while the argument has type [Unit].  The declarative application
    rule therefore cannot combine their derivations: subsumption cannot turn
    [Unit] into [Nat].  This example checks that the declarative system rejects
    a closed, grammatically valid source program for precisely that reason. *)
Definition ill_typed_application : expr :=
  EApp (ELambda Syntax.TyNat (EVar 0)) EUnit.

(** Rejection is a typing property rather than a syntax property: the example
    is a closed source expression with no runtime-only forms or free variables. *)
Example ill_typed_application_closed_source :
  closed_source ill_typed_application.
Proof.
  unfold closed_source, closed, ill_typed_application.
  split; repeat constructor.
Qed.

(** The function subexpression itself is accepted and has the expected
    identity-function type and empty immediate effect. *)
Example ill_typed_application_function_typing :
  source_has_type []
    (ELambda Syntax.TyNat (EVar 0))
    (TyArrow Syntax.TyNat [] Syntax.TyNat) [].
Proof.
  split.
  - repeat constructor.
  - apply TyAbs. apply TyVar. reflexivity.
Qed.

(** The argument subexpression is also accepted, but its type is [Unit]. *)
Example ill_typed_application_argument_typing :
  source_has_type [] EUnit Syntax.TyUnit [].
Proof. split; constructor. Qed.

(** A subtype chain beginning at [Unit] cannot change its outer type
    constructor.  This small inversion fact lets the negative example account
    for any number of declarative [TySub] steps around the argument. *)
Lemma subtype_chain_from_unit_inv :
  forall T,
    subtype_chain Syntax.TyUnit T ->
    T = Syntax.TyUnit.
Proof.
  fix IH 2. intros T Hchain.
  inversion Hchain as [T'|T' U V Hsub Htail]; subst.
  - reflexivity.
  - inversion Hsub; subst. apply IH. exact Htail.
Qed.

(** Likewise, a subtype chain ending at [Nat] must have begun at [Nat].
    We use this for the contravariant domain chain obtained by inverting the
    type assigned to the annotated lambda. *)
Lemma subtype_chain_to_nat_inv :
  forall T,
    subtype_chain T Syntax.TyNat ->
    T = Syntax.TyNat.
Proof.
  fix IH 2. intros T Hchain.
  inversion Hchain as [T'|T' U V Hsub Htail]; subst.
  - reflexivity.
  - pose proof (IH U Htail) as HU. subst U.
    inversion Hsub. reflexivity.
Qed.

(** Declarative typing of [unit], including any trailing [TySub] rules, keeps
    the empty effect and starts its subtype chain at [Unit]. *)
Lemma typing_unit_generation :
  forall Gamma T Phi,
    has_type Gamma EUnit T Phi ->
    subtype_chain Syntax.TyUnit T /\ Phi = [].
Proof.
  intros Gamma T Phi Htyping.
  destruct (typing_generation _ _ _ _ Htyping)
    as [root_type [Hroot Hchain]].
  inversion Hroot; subst. auto.
Qed.

(** No declarative result type or effect exists for the whole application.
    Application generation produces one common domain for the function and
    argument.  Lambda generation says that domain is below the annotation
    [Nat], while unit generation says it is above [Unit].  The two inversion
    lemmas force that domain to be both distinct base types, a contradiction. *)
Example ill_typed_application_rejected :
  ~ exists T Phi,
      source_has_type [] ill_typed_application T Phi.
Proof.
  intros [T [Phi [_ Htyping]]].
  unfold ill_typed_application in Htyping.
  destruct (typing_app_generation _ _ _ _ _ Htyping)
    as [domain [codomain [latent [Phi_function [Phi_argument
      [Hfunction [Hargument _]]]]]]].
  destruct (typing_abs_generation _ _ _ _ _ Hfunction)
    as [result_ty [Phi_body [_ [Harrow _]]]].
  destruct (subtype_chain_arrow_inv _ _ _ _ _ _ Harrow)
    as [Hdomain _].
  destruct (typing_generation _ _ _ _ Hargument)
    as [root_type [Hroot Hunit]].
  inversion Hroot; subst.
  pose proof (subtype_chain_from_unit_inv _ Hunit) as Hdomain_unit.
  pose proof (subtype_chain_to_nat_inv _ Hdomain) as Hdomain_nat.
  congruence.
Qed.

(** A negative higher-order effect regression case:

      (lambda (f : unit -[{(1,1)}]-> unit). unit)
        (lambda (_ : unit). download 10 1)

    The outer function requires a callback whose latent effect is covered by
    [(1,1)].  The supplied callback instead has latent effect [(10,1)].  This
    is an effect mismatch in arrow subtyping, even though both callbacks have
    the same domain and codomain.  Notice that this tests a *latent* effect:
    ordinary immediate argument effects are accumulated by [TyApp], not
    rejected by it. *)
Definition effect_rejected_expected_latent : effect :=
  [Obligation 1 1].

Definition effect_rejected_actual_latent : effect :=
  download_effect paper_size_10 paper_timeout_1.

Definition effect_rejected_callback_ty : ty :=
  TyArrow Syntax.TyUnit effect_rejected_expected_latent Syntax.TyUnit.

Definition effect_rejected_application : expr :=
  EApp
    (ELambda effect_rejected_callback_ty EUnit)
    (ELambda Syntax.TyUnit
      (EDownload paper_size_10 paper_timeout_1)).

(** The supplied callback really carries the singleton rate-10 latent effect. *)
Example effect_rejected_actual_latent_calculation :
  effect_rejected_actual_latent = [Obligation 10 1].
Proof. vm_compute. reflexivity. Qed.

(** The higher-order mismatch is a closed, grammatically valid source term. *)
Example effect_rejected_application_closed_source :
  closed_source effect_rejected_application.
Proof.
  unfold closed_source, closed, effect_rejected_application,
    effect_rejected_callback_ty.
  split; repeat constructor.
Qed.

(** The outer function is declaratively well typed on its own. *)
Example effect_rejected_application_function_typing :
  source_has_type []
    (ELambda effect_rejected_callback_ty EUnit)
    (TyArrow effect_rejected_callback_ty [] Syntax.TyUnit) [].
Proof.
  split.
  - unfold effect_rejected_callback_ty. repeat constructor.
  - apply TyAbs. apply TyUnit.
Qed.

(** The supplied callback is also declaratively well typed on its own, with
    the larger rate-10 latent effect. *)
Example effect_rejected_application_argument_typing :
  source_has_type []
    (ELambda Syntax.TyUnit
      (EDownload paper_size_10 paper_timeout_1))
    (TyArrow Syntax.TyUnit effect_rejected_actual_latent Syntax.TyUnit) [].
Proof.
  split.
  - repeat constructor.
  - unfold effect_rejected_actual_latent. apply TyAbs. apply TyDownload.
Qed.

(** The complete application has no declarative typing.  Generation exposes
    a common callback type selected by [TyApp].  The supplied callback must be
    below that type, and that type must be below the annotation on the outer
    lambda.  Composing and inverting those subtype chains would require the
    rate-10 latent effect to be covered by the rate-1 latent effect, which is
    arithmetically impossible. *)
Example effect_rejected_application_rejected :
  ~ exists T Phi,
      source_has_type [] effect_rejected_application T Phi.
Proof.
  intros [T [Phi [_ Htyping]]].
  unfold effect_rejected_application in Htyping.
  destruct (typing_app_generation _ _ _ _ _ Htyping)
    as [domain [codomain [latent [Phi_function [Phi_argument
      [Hfunction [Hargument _]]]]]]].

  destruct (typing_abs_generation _ _ _ _ _ Hfunction)
    as [outer_result [outer_effect
      [Houter_body [Houter_arrow _]]]].
  destruct (typing_unit_generation _ _ _ Houter_body)
    as [_ Houter_effect].
  subst outer_effect.
  destruct (subtype_chain_arrow_inv _ _ _ _ _ _ Houter_arrow)
    as [Hdomain_expected _].

  destruct (typing_abs_generation _ _ _ _ _ Hargument)
    as [argument_result [argument_effect
      [Hargument_body [Hargument_arrow _]]]].
  destruct (typing_download_generation _ _ _ _ _ Hargument_body)
    as [_ Hargument_effect].
  subst argument_effect.

  pose proof
    (subtype_chain_trans _ _ _ Hargument_arrow Hdomain_expected)
    as Hcallback_subtype.
  unfold effect_rejected_callback_ty in Hcallback_subtype.
  destruct (subtype_chain_arrow_inv _ _ _ _ _ _ Hcallback_subtype)
    as [_ [Heffect _]].
  unfold effect_rejected_actual_latent, effect_rejected_expected_latent,
    download_effect in Heffect.
  specialize (Heffect (Obligation 10 1)).
  assert (Hin : In (Obligation 10 1)
    [Obligation (download_rate paper_size_10 paper_timeout_1) 1]).
  { vm_compute. auto. }
  specialize (Heffect Hin).
  destruct Heffect as [covered [[Heq | []] [Hrate _]]].
  inversion Heq; subst covered.
  vm_compute in Hrate.
  apply Hrate. reflexivity.
Qed.

(** The paper also calculates parallel composition directly on two effects:
    [(10,1),(6,5)] in parallel with [(1,10)].  This checks the effect algebra
    independently of expression typing. *)
Example paper_parallel_effect_calculation :
  parallel_effect
    [Obligation 10 1; Obligation 6 5]
    [Obligation 1 10] =
  [Obligation 10 11; Obligation 6 15].
Proof. vm_compute. reflexivity. Qed.
