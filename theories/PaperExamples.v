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
  Quantities Effects Normalization Bandwidth Syntax Typing AlgorithmicTyping.

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
    is [Nat] while the argument has type [Unit].  [AlgTyApp] therefore requires
    the impossible premise [Unit <: Nat].  This example checks that the local
    application subtype test rejects a closed, grammatically valid source
    program for precisely that reason. *)
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
  algorithmic_has_type []
    (ELambda Syntax.TyNat (EVar 0))
    (TyArrow Syntax.TyNat [] Syntax.TyNat) [].
Proof.
  apply AlgTyAbs. apply AlgTyVar. reflexivity.
Qed.

(** The argument subexpression is also accepted, but its type is [Unit]. *)
Example ill_typed_application_argument_typing :
  algorithmic_has_type [] EUnit Syntax.TyUnit [].
Proof. apply AlgTyUnit. Qed.

(** No algorithmic result type or effect exists for the whole application.
    Inverting a hypothetical [AlgTyApp] derivation fixes the function domain
    to [Nat] and the argument type to [Unit]; structural subtyping has no rule
    relating those two different base types. *)
Example ill_typed_application_rejected :
  ~ exists T Phi,
      algorithmic_has_type [] ill_typed_application T Phi.
Proof.
  intros [T [Phi Htyping]]. unfold ill_typed_application in Htyping.
  inversion Htyping; subst.
  match goal with
  | Hfunction : algorithmic_has_type _ (ELambda _ _) _ _ |- _ =>
      inversion Hfunction; subst
  end.
  match goal with
  | Hargument : algorithmic_has_type _ EUnit _ _ |- _ =>
      inversion Hargument; subst
  end.
  match goal with
  | Hsubtype : Syntax.TyUnit <: Syntax.TyNat |- _ => inversion Hsubtype
  end.
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
