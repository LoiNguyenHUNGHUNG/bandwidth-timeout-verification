(** Symbolic syntax and effects for size-bound inference.

    This file follows the first part of the paper's size-inference appendix.
    Symbolic effect operations deliberately retain every obligation and do not
    normalize. A size assignment replaces symbolic rates by concrete rational
    rates; only then do we Pareto-normalize the resulting concrete effect.

    The symbolic source language mirrors [Syntax.expr], but a download carries
    a size-variable identifier rather than a concrete transfer size. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import
  Effects Normalization Bandwidth Syntax Typing SizeInference.

Import ListNotations.
Open Scope Q_scope.

(** A symbolic rate is either an inferred size divided by a known timeout or
    an already-concrete rate from a programmer-written contract. *)
Inductive symbolic_rate : Type :=
| SRateVariable (variable : size_variable) (timeout : Q)
| SRateConcrete (concrete_rate : Q).

(** A symbolic obligation has the same concrete concurrency coordinate as an
    ordinary obligation; only its rate may contain a size variable. *)
Record symbolic_obligation : Type := SymbolicObligation {
  symbolic_obligation_rate : symbolic_rate;
  symbolic_concurrency : nat
}.

(** Symbolic effects are finite lists. As with concrete effects, list order is
    representation detail rather than semantic information. *)
Definition symbolic_effect : Type := list symbolic_obligation.

(** Maximum concurrency is computed without inspecting symbolic rates. *)
Fixpoint symbolic_max_concurrency (Phi : symbolic_effect) : nat :=
  match Phi with
  | [] => 0
  | p :: Phi' =>
      Nat.max (symbolic_concurrency p) (symbolic_max_concurrency Phi')
  end.

(** The paper's symbolic sequential join is raw finite union. *)
Definition symbolic_join
    (Phi Psi : symbolic_effect) : symbolic_effect :=
  Phi ++ Psi.

(** Add [k] possible concurrent downloads to one symbolic obligation. *)
Definition symbolic_shift
    (k : nat) (p : symbolic_obligation) : symbolic_obligation :=
  SymbolicObligation
    (symbolic_obligation_rate p)
    (symbolic_concurrency p + k).

(** Apply the same concurrency shift to every symbolic obligation. *)
Definition symbolic_shift_effect
    (k : nat) (Phi : symbolic_effect) : symbolic_effect :=
  map (symbolic_shift k) Phi.

(** Raw symbolic parallel composition uses exactly the concurrency shifts from
    the paper and intentionally performs no Pareto normalization. *)
Definition symbolic_parallel
    (Phi Psi : symbolic_effect) : symbolic_effect :=
  symbolic_join
    (symbolic_shift_effect (symbolic_max_concurrency Psi) Phi)
    (symbolic_shift_effect (symbolic_max_concurrency Phi) Psi).

(** Fold symbolic parallel composition over the branch effects of a structured
    parallel expression. *)
Fixpoint symbolic_parallel_effects
    (effects : list symbolic_effect) : symbolic_effect :=
  match effects with
  | [] => []
  | Phi :: effects' =>
      symbolic_parallel Phi (symbolic_parallel_effects effects')
  end.

(** Symbolic types have the concrete type structure but may store symbolic
    latent effects on arrows. *)
Inductive symbolic_ty : Type :=
| STyUnit
| STyNat
| STyArrow : symbolic_ty -> symbolic_effect -> symbolic_ty -> symbolic_ty
| STyProduct : list symbolic_ty -> symbolic_ty.

(** [concrete_symbolic_effect symbolic concrete] relates two representations
    of the same effect.  The left side remains a [symbolic_effect], but every
    rate in it must have the form [SRateConcrete r], so it contains no unknown
    size variables.  The right side is the corresponding ordinary [effect],
    obtained by removing the [SRateConcrete] wrappers.  The relation also
    requires every represented rate to be nonnegative. *)
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

(** One programmer-written effect obligation.  Its rate is concrete and
    nonnegative by construction; concurrency remains an ordinary natural
    number, as in the paper's effect grammar. *)
Record annotation_obligation : Type := AnnotationObligation {
  annotation_rate : Q;
  annotation_concurrency : nat;
  annotation_rate_nonnegative : 0 <= annotation_rate
}.

(** Programmer-written effects contain only checked concrete obligations. *)
Definition annotation_effect : Type := list annotation_obligation.

(** Dedicated grammar for programmer-written type annotations.  It is
    intentionally separate from [symbolic_ty]: inferred types may mention size
    variables in latent effects, whereas source annotations cannot. *)
Inductive annotation_ty : Type :=
| ATyUnit
| ATyNat
| ATyArrow : annotation_ty -> annotation_effect ->
    annotation_ty -> annotation_ty
| ATyProduct : list annotation_ty -> annotation_ty.

(** Embed one checked annotation obligation into symbolic effect syntax. *)
Definition annotation_obligation_symbolic
    (p : annotation_obligation) : symbolic_obligation :=
  SymbolicObligation
    (SRateConcrete (annotation_rate p))
    (annotation_concurrency p).

(** Embed a checked annotation effect into all-concrete symbolic syntax. *)
Definition annotation_effect_symbolic
    (Phi : annotation_effect) : symbolic_effect :=
  map annotation_obligation_symbolic Phi.

(** Embed the dedicated annotation grammar into the larger inferred-type
    grammar used internally by constraint generation. *)
Fixpoint annotation_symbolic_ty (T : annotation_ty) : symbolic_ty :=
  match T with
  | ATyUnit => STyUnit
  | ATyNat => STyNat
  | ATyArrow domain latent codomain =>
      STyArrow
        (annotation_symbolic_ty domain)
        (annotation_effect_symbolic latent)
        (annotation_symbolic_ty codomain)
  | ATyProduct components =>
      STyProduct (map annotation_symbolic_ty components)
  end.

(** The concrete effect represented by a checked annotation effect. *)
Definition annotation_effect_concrete
    (Phi : annotation_effect) : effect :=
  map (fun p =>
    Obligation (annotation_rate p) (annotation_concurrency p)) Phi.

(** Embedding an annotation effect produces a concrete symbolic contract. *)
Lemma annotation_effect_symbolic_concrete :
  forall Phi,
    concrete_symbolic_effect
      (annotation_effect_symbolic Phi)
      (annotation_effect_concrete Phi).
Proof.
  intros Phi. induction Phi as [|p Phi IH]; simpl.
  - constructor.
  - destruct p as [rate concurrency Hrate]. simpl. constructor; assumption.
Qed.

(** Symbolic source syntax. Term variables remain de Bruijn indices. Unlike
    [Syntax.expr], this datatype has no runtime-only running-download form. *)
Inductive symbolic_expr : Type :=
| SEVar : nat -> symbolic_expr
| SEUnit : symbolic_expr
| SENat : nat -> symbolic_expr
| SELambda : annotation_ty -> symbolic_expr -> symbolic_expr
| SETuple : list symbolic_expr -> symbolic_expr
| SEApp : symbolic_expr -> symbolic_expr -> symbolic_expr
| SELet : symbolic_expr -> symbolic_expr -> symbolic_expr
| SEIfZero : symbolic_expr -> symbolic_expr -> symbolic_expr -> symbolic_expr
| SEDownload : size_variable -> Q -> symbolic_expr
| SEParallel : list symbolic_expr -> symbolic_expr.

(** Symbolic values mirror concrete values. Lambda bodies are not evaluated
    when the lambda is created. *)
Inductive symbolic_value : symbolic_expr -> Prop :=
| SVUnit : symbolic_value SEUnit
| SVNat : forall n, symbolic_value (SENat n)
| SVLambda : forall parameter_ty body,
    symbolic_value (SELambda parameter_ty body)
| SVTuple : forall components,
    Forall symbolic_value components ->
    symbolic_value (SETuple components).

(** Grammatical symbolic source expressions. The separate predicate retains
    the concrete source grammar's requirement that tuple components be values. *)
Inductive symbolic_source_expr : symbolic_expr -> Prop :=
| SSrcVar : forall index, symbolic_source_expr (SEVar index)
| SSrcUnit : symbolic_source_expr SEUnit
| SSrcNat : forall n, symbolic_source_expr (SENat n)
| SSrcLambda : forall parameter_ty body,
    symbolic_source_expr body ->
    symbolic_source_expr (SELambda parameter_ty body)
| SSrcTuple : forall components,
    Forall symbolic_value components ->
    Forall symbolic_source_expr components ->
    symbolic_source_expr (SETuple components)
| SSrcApp : forall function argument,
    symbolic_source_expr function ->
    symbolic_source_expr argument ->
    symbolic_source_expr (SEApp function argument)
| SSrcLet : forall bound body,
    symbolic_source_expr bound ->
    symbolic_source_expr body ->
    symbolic_source_expr (SELet bound body)
| SSrcIfZero : forall guard zero_branch nonzero_branch,
    symbolic_source_expr guard ->
    symbolic_source_expr zero_branch ->
    symbolic_source_expr nonzero_branch ->
    symbolic_source_expr (SEIfZero guard zero_branch nonzero_branch)
| SSrcDownload : forall variable timeout,
    symbolic_source_expr (SEDownload variable timeout)
| SSrcParallel : forall branches,
    Forall symbolic_source_expr branches ->
    symbolic_source_expr (SEParallel branches).

(** Substitute a size assignment into one symbolic rate. *)
Definition instantiate_rate
    (sigma : size_assignment) (symbolic : symbolic_rate) : Q :=
  match symbolic with
  | SRateVariable variable timeout => sigma variable / timeout
  | SRateConcrete concrete_rate => concrete_rate
  end.

(** Substitute a size assignment into one symbolic obligation. *)
Definition instantiate_obligation
    (sigma : size_assignment) (p : symbolic_obligation) : obligation :=
  Obligation
    (instantiate_rate sigma (symbolic_obligation_rate p))
    (symbolic_concurrency p).

(** Raw instantiation changes rates but retains every symbolic obligation. *)
Definition instantiate_effect_raw
    (sigma : size_assignment) (Phi : symbolic_effect) : effect :=
  map (instantiate_obligation sigma) Phi.

(** The paper's [sigma_Norm] operation: instantiate and then compute the
    concrete Pareto frontier. *)
Definition instantiate_effect
    (sigma : size_assignment) (Phi : symbolic_effect) : effect :=
  normalize (instantiate_effect_raw sigma Phi).

(** Instantiate every symbolic latent effect in a symbolic type. *)
Fixpoint instantiate_ty
    (sigma : size_assignment) (T : symbolic_ty) : ty :=
  match T with
  | STyUnit => Syntax.TyUnit
  | STyNat => Syntax.TyNat
  | STyArrow domain latent codomain =>
      Syntax.TyArrow
        (instantiate_ty sigma domain)
        (instantiate_effect sigma latent)
        (instantiate_ty sigma codomain)
  | STyProduct components =>
      Syntax.TyProduct (map (instantiate_ty sigma) components)
  end.

(** Replace symbolic downloads by concrete downloads and instantiate every
    lambda annotation. *)
Fixpoint instantiate_expr
    (sigma : size_assignment) (e : symbolic_expr) : expr :=
  match e with
  | SEVar index => EVar index
  | SEUnit => EUnit
  | SENat n => ENat n
  | SELambda parameter_annotation body =>
      ELambda
        (instantiate_ty sigma
          (annotation_symbolic_ty parameter_annotation))
        (instantiate_expr sigma body)
  | SETuple components => ETuple (map (instantiate_expr sigma) components)
  | SEApp function argument =>
      EApp (instantiate_expr sigma function) (instantiate_expr sigma argument)
  | SELet bound body =>
      ELet (instantiate_expr sigma bound) (instantiate_expr sigma body)
  | SEIfZero guard zero_branch nonzero_branch =>
      EIfZero
        (instantiate_expr sigma guard)
        (instantiate_expr sigma zero_branch)
        (instantiate_expr sigma nonzero_branch)
  | SEDownload variable timeout => EDownload (sigma variable) timeout
  | SEParallel branches => EParallel (map (instantiate_expr sigma) branches)
  end.

(** A symbolic rate is well formed when a concrete rate is nonnegative or a
    symbolic download timeout is strictly positive. *)
Inductive symbolic_rate_wf : symbolic_rate -> Prop :=
| WfSRateVariable : forall variable timeout,
    0 < timeout ->
    symbolic_rate_wf (SRateVariable variable timeout)
| WfSRateConcrete : forall concrete_rate,
    0 <= concrete_rate ->
    symbolic_rate_wf (SRateConcrete concrete_rate).

(** A symbolic obligation is well formed when its rate is well formed. *)
Definition symbolic_obligation_wf (p : symbolic_obligation) : Prop :=
  symbolic_rate_wf (symbolic_obligation_rate p).

(** A symbolic effect is well formed when every obligation is well formed. *)
Definition symbolic_effect_wf (Phi : symbolic_effect) : Prop :=
  Forall symbolic_obligation_wf Phi.

(** A well-formed assignment turns a well-formed symbolic rate into a
    nonnegative concrete rate. *)
Lemma instantiate_rate_nonnegative :
  forall sigma symbolic,
    assignment_wf sigma ->
    symbolic_rate_wf symbolic ->
    0 <= instantiate_rate sigma symbolic.
Proof.
  intros sigma symbolic Hsigma Hsymbolic. destruct Hsymbolic; simpl.
  - unfold Qdiv. apply Qmult_le_0_compat.
    + apply Hsigma.
    + apply Qinv_le_0_compat. apply Qlt_le_weak. exact H.
  - exact H.
Qed.

(** Raw instantiation preserves rate well-formedness. *)
Lemma instantiate_effect_raw_wf :
  forall sigma Phi,
    assignment_wf sigma ->
    symbolic_effect_wf Phi ->
    effect_wf (instantiate_effect_raw sigma Phi).
Proof.
  intros sigma Phi Hsigma Hwf. induction Hwf; simpl.
  - constructor.
  - constructor.
    + unfold obligation_wf, symbolic_obligation_wf in *. simpl.
      apply instantiate_rate_nonnegative; assumption.
    + exact IHHwf.
Qed.

(** Normalized instantiation also preserves rate well-formedness. *)
Lemma instantiate_effect_wf :
  forall sigma Phi,
    assignment_wf sigma ->
    symbolic_effect_wf Phi ->
    effect_wf (instantiate_effect sigma Phi).
Proof.
  intros sigma Phi Hsigma Hwf. unfold instantiate_effect.
  apply normalize_wf. apply instantiate_effect_raw_wf; assumption.
Qed.

(** Instantiation changes no concurrency coordinate, so it preserves the
    computed maximum concurrency exactly. *)
Lemma max_concurrency_instantiate_effect_raw :
  forall sigma Phi,
    max_concurrency (instantiate_effect_raw sigma Phi) =
    symbolic_max_concurrency Phi.
Proof.
  intros sigma Phi. induction Phi as [|p Phi IH]; simpl.
  - reflexivity.
  - rewrite IH. reflexivity.
Qed.

(** Pareto normalization also preserves maximum concurrency. *)
Lemma max_concurrency_instantiate_effect :
  forall sigma Phi,
    max_concurrency (instantiate_effect sigma Phi) =
    symbolic_max_concurrency Phi.
Proof.
  intros sigma Phi. unfold instantiate_effect.
  rewrite max_concurrency_normalize.
  apply max_concurrency_instantiate_effect_raw.
Qed.

(** Instantiation of one symbolic shift is the corresponding concrete shift. *)
Lemma instantiate_symbolic_shift :
  forall sigma k p,
    instantiate_obligation sigma (symbolic_shift k p) =
    shift k (instantiate_obligation sigma p).
Proof.
  intros sigma k [symbolic_rate concurrency]. reflexivity.
Qed.

(** Instantiation commutes literally with shifting an unnormalized symbolic
    effect. *)
Lemma instantiate_symbolic_shift_effect_raw :
  forall sigma k Phi,
    instantiate_effect_raw sigma (symbolic_shift_effect k Phi) =
    shift_effect k (instantiate_effect_raw sigma Phi).
Proof.
  intros sigma k Phi. induction Phi as [|p Phi IH]; simpl.
  - reflexivity.
  - rewrite instantiate_symbolic_shift, IH. reflexivity.
Qed.

(** Instantiation commutes literally with unnormalized symbolic union. *)
Lemma instantiate_symbolic_join_raw :
  forall sigma Phi Psi,
    instantiate_effect_raw sigma (symbolic_join Phi Psi) =
    join (instantiate_effect_raw sigma Phi)
      (instantiate_effect_raw sigma Psi).
Proof.
  intros sigma Phi Psi. unfold instantiate_effect_raw, symbolic_join, join.
  apply map_app.
Qed.

(** Because instantiation leaves concurrency unchanged, raw symbolic and raw
    concrete parallel composition commute literally. *)
Lemma instantiate_symbolic_parallel_raw :
  forall sigma Phi Psi,
    instantiate_effect_raw sigma (symbolic_parallel Phi Psi) =
    parallel (instantiate_effect_raw sigma Phi)
      (instantiate_effect_raw sigma Psi).
Proof.
  intros sigma Phi Psi. unfold symbolic_parallel, parallel.
  rewrite instantiate_symbolic_join_raw.
  rewrite !instantiate_symbolic_shift_effect_raw.
  rewrite !max_concurrency_instantiate_effect_raw.
  reflexivity.
Qed.

(** Instantiation commutes with the paper's symbolic sequential operation up
    to semantic effect equivalence. The paper writes set equality;
    [effect_equiv] is its list-representation counterpart. *)
Theorem instantiate_symbolic_join :
  forall sigma Phi Psi,
    instantiate_effect sigma (symbolic_join Phi Psi) ≈
    sequential_effect
      (instantiate_effect sigma Phi)
      (instantiate_effect sigma Psi).
Proof.
  intros sigma Phi Psi. unfold instantiate_effect, sequential_effect.
  rewrite instantiate_symbolic_join_raw. split; apply normalize_mono.
  - apply join_mono; apply le_normalize.
  - apply join_mono; apply normalize_le.
Qed.

(** Instantiation commutes with the paper's symbolic parallel operation up to
    semantic effect equivalence. The proof follows the paper: instantiation
    preserves concurrency shifts, and normalization removes only obligations
    already dominated in the child effects. *)
Theorem instantiate_symbolic_parallel :
  forall sigma Phi Psi,
    instantiate_effect sigma (symbolic_parallel Phi Psi) ≈
    parallel_effect
      (instantiate_effect sigma Phi)
      (instantiate_effect sigma Psi).
Proof.
  intros sigma Phi Psi. unfold instantiate_effect, parallel_effect.
  rewrite instantiate_symbolic_parallel_raw. split; apply normalize_mono.
  - apply parallel_mono; apply le_normalize.
  - apply parallel_mono; apply normalize_le.
Qed.

(** The binary parallel commutation theorem extends to the structured list
    fold used by parallel expressions. *)
Theorem instantiate_symbolic_parallel_effects :
  forall sigma effects,
    instantiate_effect sigma (symbolic_parallel_effects effects) ≈
    parallel_effects (map (instantiate_effect sigma) effects).
Proof.
  intros sigma effects. induction effects as [|Phi effects IH]; simpl.
  - apply effect_equiv_refl.
  - eapply effect_equiv_trans.
    + apply instantiate_symbolic_parallel.
    + apply parallel_effect_respects_equiv.
      * apply effect_equiv_refl.
      * exact IH.
Qed.

(** Instantiating a symbolic value always produces a concrete value. *)
Lemma instantiate_symbolic_value :
  forall sigma e,
    symbolic_value e ->
    value (instantiate_expr sigma e).
Proof.
  fix IH 3. intros sigma e Hvalue. destruct Hvalue; simpl.
  - constructor.
  - constructor.
  - constructor.
  - apply VTuple. induction H.
    + constructor.
    + simpl. constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** Instantiation maps every grammatical symbolic source expression to a
    grammatical concrete source expression. *)
Theorem instantiate_symbolic_source :
  forall sigma e,
    symbolic_source_expr e ->
    source_expr (instantiate_expr sigma e).
Proof.
  fix IH 3. intros sigma e Hsource. destruct Hsource; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IH. exact Hsource.
  - apply SrcTuple.
    + induction H.
      * constructor.
      * simpl. constructor.
        -- apply instantiate_symbolic_value. exact H.
        -- apply IHForall. inversion H0. assumption.
    + induction H0.
      * constructor.
      * simpl. constructor.
        -- apply IH. exact H0.
        -- apply IHForall. inversion H. assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - constructor. induction H.
    + constructor.
    + simpl. constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** A well-formed symbolic download becomes a concrete download whose size is
    nonnegative and whose timeout is positive. *)
Lemma instantiate_download_parameters_wf :
  forall sigma variable timeout,
    assignment_wf sigma ->
    0 < timeout ->
    download_parameters_wf (sigma variable) timeout.
Proof.
  intros sigma variable timeout Hsigma Htimeout. split.
  - apply Hsigma.
  - exact Htimeout.
Qed.
