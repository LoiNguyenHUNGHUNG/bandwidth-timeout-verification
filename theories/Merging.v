(** Symbolic branch-type joins and meets for size inference.

    This file follows the mutually recursive [join_theta]/[meet_theta] section
    of the paper.  It begins with the concrete effect meet required in the
    negative (function-domain) case.  Symbolic joins may retain inferred rates,
    but a symbolic function meet is permitted only when both latent effects are
    programmer-written concrete contracts. *)

From Stdlib Require Import Arith Lia List QArith Qminmax.

From BandwidthTimeout Require Import Effects Normalization Bandwidth Syntax
  Typing SizeInference Symbolic Compatibility.

Import ListNotations.
Open Scope Q_scope.

(** Coordinatewise meet of two concrete obligations. *)
Definition meet_obligation (p q : obligation) : obligation :=
  Obligation
    (Qmin (rate p) (rate q))
    (Nat.min (concurrency p) (concurrency q)).

(** The unnormalized Cartesian-product effect meet from the paper. *)
Definition raw_effect_meet (Phi Psi : effect) : effect :=
  flat_map (fun p => map (meet_obligation p) Psi) Phi.

(** The concrete effect meet is the Pareto normalization of every
    coordinatewise pairwise minimum. *)
Definition effect_meet (Phi Psi : effect) : effect :=
  normalize (raw_effect_meet Phi Psi).

(** Every selected pair contributes its coordinatewise minimum to the raw
    effect meet. *)
Lemma in_raw_effect_meet :
  forall Phi Psi p q,
    In p Phi ->
    In q Psi ->
    In (meet_obligation p q) (raw_effect_meet Phi Psi).
Proof.
  intros Phi Psi p q Hp Hq. unfold raw_effect_meet.
  apply in_flat_map. exists p. split; [exact Hp |].
  apply in_map. exact Hq.
Qed.

(** Every raw meet member arises from one member of each operand. *)
Lemma raw_effect_meet_inv :
  forall Phi Psi m,
    In m (raw_effect_meet Phi Psi) ->
    exists p q,
      In p Phi /\
      In q Psi /\
      m = meet_obligation p q.
Proof.
  intros Phi Psi m Hin. unfold raw_effect_meet in Hin.
  apply in_flat_map in Hin as [p [Hp Hin]].
  apply in_map_iff in Hin as [q [Hq_eq Hq]].
  exists p, q. split; [exact Hp |]. split; [exact Hq |].
  symmetry. exact Hq_eq.
Qed.

(** A coordinatewise pairwise minimum is below its left input. *)
Lemma meet_obligation_le_left :
  forall p q,
    obligation_le (meet_obligation p q) p.
Proof.
  intros p q. split.
  - apply Q.le_min_l.
  - apply Nat.le_min_l.
Qed.

(** A coordinatewise pairwise minimum is below its right input. *)
Lemma meet_obligation_le_right :
  forall p q,
    obligation_le (meet_obligation p q) q.
Proof.
  intros p q. split.
  - apply Q.le_min_r.
  - apply Nat.le_min_r.
Qed.

(** Anything below both inputs is below their coordinatewise minimum. *)
Lemma obligation_le_meet :
  forall x p q,
    obligation_le x p ->
    obligation_le x q ->
    obligation_le x (meet_obligation p q).
Proof.
  intros x p q [Hrate_p Hconc_p] [Hrate_q Hconc_q]. split.
  - apply Q.min_glb; assumption.
  - apply Nat.min_glb; assumption.
Qed.

(** The raw meet is covered by its left operand. *)
Lemma raw_effect_meet_le_left :
  forall Phi Psi,
    raw_effect_meet Phi Psi ≼ Phi.
Proof.
  intros Phi Psi m Hin.
  destruct (raw_effect_meet_inv Phi Psi m Hin)
    as [p [q [Hp [Hq ->]]]].
  exists p. split; [exact Hp |]. apply meet_obligation_le_left.
Qed.

(** The raw meet is covered by its right operand. *)
Lemma raw_effect_meet_le_right :
  forall Phi Psi,
    raw_effect_meet Phi Psi ≼ Psi.
Proof.
  intros Phi Psi m Hin.
  destruct (raw_effect_meet_inv Phi Psi m Hin)
    as [p [q [Hp [Hq ->]]]].
  exists q. split; [exact Hq |]. apply meet_obligation_le_right.
Qed.

(** Any effect covered by both inputs is covered by their raw meet. *)
Lemma raw_effect_meet_greatest :
  forall Xi Phi Psi,
    Xi ≼ Phi ->
    Xi ≼ Psi ->
    Xi ≼ raw_effect_meet Phi Psi.
Proof.
  intros Xi Phi Psi Hleft Hright x Hx.
  destruct (Hleft x Hx) as [p [Hp Hxp]].
  destruct (Hright x Hx) as [q [Hq Hxq]].
  exists (meet_obligation p q). split.
  - apply in_raw_effect_meet; assumption.
  - apply obligation_le_meet; assumption.
Qed.

(** The normalized concrete meet is below its left operand. *)
Lemma effect_meet_le_left :
  forall Phi Psi,
    effect_meet Phi Psi ≼ Phi.
Proof.
  intros Phi Psi. unfold effect_meet. eapply effect_le_trans.
  - apply normalize_le.
  - apply raw_effect_meet_le_left.
Qed.

(** The normalized concrete meet is below its right operand. *)
Lemma effect_meet_le_right :
  forall Phi Psi,
    effect_meet Phi Psi ≼ Psi.
Proof.
  intros Phi Psi. unfold effect_meet. eapply effect_le_trans.
  - apply normalize_le.
  - apply raw_effect_meet_le_right.
Qed.

(** The concrete meet is the greatest lower bound under effect coverage. *)
Theorem effect_meet_greatest :
  forall Xi Phi Psi,
    Xi ≼ Phi ->
    Xi ≼ Psi ->
    Xi ≼ effect_meet Phi Psi.
Proof.
  intros Xi Phi Psi Hleft Hright. unfold effect_meet.
  eapply effect_le_trans.
  - eapply raw_effect_meet_greatest.
    + exact Hleft.
    + exact Hright.
  - apply le_normalize.
Qed.

(** The raw meet of well-formed effects has nonnegative rates. *)
Lemma raw_effect_meet_wf :
  forall Phi Psi,
    effect_wf Phi ->
    effect_wf Psi ->
    effect_wf (raw_effect_meet Phi Psi).
Proof.
  intros Phi Psi HPhi HPsi. unfold effect_wf in *.
  apply Forall_forall. intros m Hin.
  destruct (raw_effect_meet_inv Phi Psi m Hin)
    as [p [q [Hp [Hq ->]]]].
  unfold obligation_wf, meet_obligation. simpl.
  apply Q.min_glb.
  - apply Forall_forall with (x := p) in HPhi; assumption.
  - apply Forall_forall with (x := q) in HPsi; assumption.
Qed.

(** Normalized concrete effect meet preserves well-formedness. *)
Lemma effect_meet_wf :
  forall Phi Psi,
    effect_wf Phi ->
    effect_wf Psi ->
    effect_wf (effect_meet Phi Psi).
Proof.
  intros Phi Psi HPhi HPsi. unfold effect_meet.
  apply normalize_wf. apply raw_effect_meet_wf; assumption.
Qed.

(** Reflect one concrete obligation into symbolic syntax without introducing a
    size variable. *)
Definition symbolize_obligation (p : obligation) : symbolic_obligation :=
  SymbolicObligation (SRateConcrete (rate p)) (concurrency p).

(** Reflect a concrete effect into an all-concrete symbolic effect. *)
Definition symbolize_effect (Phi : effect) : symbolic_effect :=
  map symbolize_obligation Phi.

(** A well-formed concrete effect reifies to a concrete symbolic contract. *)
Lemma symbolize_effect_concrete :
  forall Phi,
    effect_wf Phi ->
    concrete_symbolic_effect (symbolize_effect Phi) Phi.
Proof.
  intros Phi Hwf. unfold effect_wf in Hwf.
  induction Hwf as [|p Phi Hp HPhi IH]; simpl.
  - constructor.
  - destruct p as [concrete_rate concurrency_value]. simpl in *.
    constructor; assumption.
Qed.

(** The concrete effect produced by [effect_meet] can therefore be stored in a
    symbolic function type without introducing inferred variables. *)
Lemma symbolize_effect_meet_concrete :
  forall Phi Psi,
    effect_wf Phi ->
    effect_wf Psi ->
    concrete_symbolic_effect
      (symbolize_effect (effect_meet Phi Psi))
      (effect_meet Phi Psi).
Proof.
  intros Phi Psi HPhi HPsi. apply symbolize_effect_concrete.
  apply effect_meet_wf; assumption.
Qed.

(** Reification also records that the resulting ordinary concrete contract is
    well formed. *)
Lemma concrete_symbolic_effect_reified_wf :
  forall symbolic concrete,
    concrete_symbolic_effect symbolic concrete ->
    effect_wf concrete.
Proof.
  intros symbolic concrete Hconcrete. induction Hconcrete.
  - constructor.
  - constructor; assumption.
Qed.

(** Join/meet compatibility of the outer type shapes.  Product arity is part
    of the shape check because products of different lengths have no
    structural common merge in the core calculus. *)
Definition merge_shapes_compatible (left right : symbolic_ty) : bool :=
  match left, right with
  | STyUnit, STyUnit => true
  | STyNat, STyNat => true
  | STyArrow _ _ _, STyArrow _ _ _ => true
  | STyProduct left_components, STyProduct right_components =>
      Nat.eqb (length left_components) (length right_components)
  | _, _ => false
  end.

(** Mutually defined symbolic type joins and meets.

    [symbolic_type_join left right result C] corresponds to
    [(result,C)=join_theta(left,right)], and [symbolic_type_meet] corresponds to
    [meet_theta].  The list judgments implement pointwise product merging.
    Incompatible shapes return the paper's dummy [Unit] result together with
    [CBottom], which can never be modeled. *)
Inductive symbolic_type_join :
    symbolic_ty -> symbolic_ty -> symbolic_ty -> constraint -> Prop :=
| SymbolicJoinUnit :
    symbolic_type_join STyUnit STyUnit STyUnit CTop
| SymbolicJoinNat :
    symbolic_type_join STyNat STyNat STyNat CTop
| SymbolicJoinArrow :
    forall left_domain left_latent left_codomain
           right_domain right_latent right_codomain
           result_domain result_codomain
           domain_constraint codomain_constraint,
      symbolic_type_meet
        left_domain right_domain result_domain domain_constraint ->
      symbolic_type_join
        left_codomain right_codomain result_codomain codomain_constraint ->
      symbolic_type_join
        (STyArrow left_domain left_latent left_codomain)
        (STyArrow right_domain right_latent right_codomain)
        (STyArrow
          result_domain
          (symbolic_join left_latent right_latent)
          result_codomain)
        (CAnd domain_constraint codomain_constraint)
| SymbolicJoinProduct :
    forall left_components right_components result_components C,
      symbolic_type_join_list
        left_components right_components result_components C ->
      symbolic_type_join
        (STyProduct left_components)
        (STyProduct right_components)
        (STyProduct result_components)
        C
| SymbolicJoinMismatch :
    forall left right,
      merge_shapes_compatible left right = false ->
      symbolic_type_join left right STyUnit CBottom
with symbolic_type_meet :
    symbolic_ty -> symbolic_ty -> symbolic_ty -> constraint -> Prop :=
| SymbolicMeetUnit :
    symbolic_type_meet STyUnit STyUnit STyUnit CTop
| SymbolicMeetNat :
    symbolic_type_meet STyNat STyNat STyNat CTop
| SymbolicMeetArrow :
    forall left_domain left_latent left_codomain
           right_domain right_latent right_codomain
           left_concrete right_concrete
           result_domain result_codomain
           domain_constraint codomain_constraint,
      concrete_symbolic_effect left_latent left_concrete ->
      concrete_symbolic_effect right_latent right_concrete ->
      symbolic_type_join
        left_domain right_domain result_domain domain_constraint ->
      symbolic_type_meet
        left_codomain right_codomain result_codomain codomain_constraint ->
      symbolic_type_meet
        (STyArrow left_domain left_latent left_codomain)
        (STyArrow right_domain right_latent right_codomain)
        (STyArrow
          result_domain
          (symbolize_effect (effect_meet left_concrete right_concrete))
          result_codomain)
        (CAnd domain_constraint codomain_constraint)
| SymbolicMeetProduct :
    forall left_components right_components result_components C,
      symbolic_type_meet_list
        left_components right_components result_components C ->
      symbolic_type_meet
        (STyProduct left_components)
        (STyProduct right_components)
        (STyProduct result_components)
        C
| SymbolicMeetMismatch :
    forall left right,
      merge_shapes_compatible left right = false ->
      symbolic_type_meet left right STyUnit CBottom
with symbolic_type_join_list :
    list symbolic_ty -> list symbolic_ty -> list symbolic_ty ->
    constraint -> Prop :=
| SymbolicJoinListNil :
    symbolic_type_join_list [] [] [] CTop
| SymbolicJoinListCons :
    forall left left_tail right right_tail result result_tail
           head_constraint tail_constraint,
      symbolic_type_join left right result head_constraint ->
      symbolic_type_join_list
        left_tail right_tail result_tail tail_constraint ->
      symbolic_type_join_list
        (left :: left_tail)
        (right :: right_tail)
        (result :: result_tail)
        (CAnd head_constraint tail_constraint)
with symbolic_type_meet_list :
    list symbolic_ty -> list symbolic_ty -> list symbolic_ty ->
    constraint -> Prop :=
| SymbolicMeetListNil :
    symbolic_type_meet_list [] [] [] CTop
| SymbolicMeetListCons :
    forall left left_tail right right_tail result result_tail
           head_constraint tail_constraint,
      symbolic_type_meet left right result head_constraint ->
      symbolic_type_meet_list
        left_tail right_tail result_tail tail_constraint ->
      symbolic_type_meet_list
        (left :: left_tail)
        (right :: right_tail)
        (result :: result_tail)
        (CAnd head_constraint tail_constraint).

Scheme symbolic_type_join_ind_mut :=
  Induction for symbolic_type_join Sort Prop
with symbolic_type_meet_ind_mut :=
  Induction for symbolic_type_meet Sort Prop
with symbolic_type_join_list_ind_mut :=
  Induction for symbolic_type_join_list Sort Prop
with symbolic_type_meet_list_ind_mut :=
  Induction for symbolic_type_meet_list Sort Prop.

Combined Scheme symbolic_type_merge_mutind
  from symbolic_type_join_ind_mut, symbolic_type_meet_ind_mut,
       symbolic_type_join_list_ind_mut, symbolic_type_meet_list_ind_mut.

(** Joins and meets only conjoin recursively generated compatibility
    constraints or return [CTop]/[CBottom], so they preserve separability. *)
Lemma symbolic_type_merge_fragment_mut :
  (forall left right result C,
      symbolic_type_join left right result C ->
      compatibility_fragment C) /\
  (forall left right result C,
      symbolic_type_meet left right result C ->
      compatibility_fragment C) /\
  (forall left right result C,
      symbolic_type_join_list left right result C ->
      compatibility_fragment C) /\
  (forall left right result C,
      symbolic_type_meet_list left right result C ->
      compatibility_fragment C).
Proof.
  apply symbolic_type_merge_mutind.
  - constructor.
  - constructor.
  - intros. constructor; assumption.
  - intros. assumption.
  - intros. constructor.
  - constructor.
  - constructor.
  - intros. constructor; assumption.
  - intros. assumption.
  - intros. constructor.
  - constructor.
  - intros. constructor; assumption.
  - constructor.
  - intros. constructor; assumption.
Qed.

Theorem symbolic_type_join_fragment :
  forall left right result C,
    symbolic_type_join left right result C ->
    compatibility_fragment C.
Proof.
  intros left right result C Hjoin.
  apply (proj1 symbolic_type_merge_fragment_mut left right result C Hjoin).
Qed.

Theorem symbolic_type_meet_fragment :
  forall left right result C,
    symbolic_type_meet left right result C ->
    compatibility_fragment C.
Proof.
  intros left right result C Hmeet.
  apply (proj1 (proj2 symbolic_type_merge_fragment_mut)
    left right result C Hmeet).
Qed.

(** After instantiation, the symbolic sequential join covers its left
    operand. *)
Lemma instantiate_symbolic_join_le_left :
  forall sigma Phi Psi,
    instantiate_effect sigma Phi ≼
    instantiate_effect sigma (symbolic_join Phi Psi).
Proof.
  intros sigma Phi Psi. unfold instantiate_effect.
  rewrite instantiate_symbolic_join_raw. eapply effect_le_trans.
  - apply normalize_le.
  - eapply effect_le_trans.
    + apply effect_le_join_l.
    + apply le_normalize.
Qed.

(** After instantiation, the symbolic sequential join covers its right
    operand. *)
Lemma instantiate_symbolic_join_le_right :
  forall sigma Phi Psi,
    instantiate_effect sigma Psi ≼
    instantiate_effect sigma (symbolic_join Phi Psi).
Proof.
  intros sigma Phi Psi. unfold instantiate_effect.
  rewrite instantiate_symbolic_join_raw. eapply effect_le_trans.
  - apply normalize_le.
  - eapply effect_le_trans.
    + apply effect_le_join_r.
    + apply le_normalize.
Qed.

(** Normalization on both sides preserves the left lower-bound property of
    concrete effect meet. *)
Lemma normalize_effect_meet_le_left :
  forall Phi Psi,
    normalize (effect_meet Phi Psi) ≼ normalize Phi.
Proof.
  intros Phi Psi. eapply effect_le_trans.
  - apply normalize_le.
  - eapply effect_le_trans.
    + apply effect_meet_le_left.
    + apply le_normalize.
Qed.

(** Normalization on both sides preserves the right lower-bound property of
    concrete effect meet. *)
Lemma normalize_effect_meet_le_right :
  forall Phi Psi,
    normalize (effect_meet Phi Psi) ≼ normalize Psi.
Proof.
  intros Phi Psi. eapply effect_le_trans.
  - apply normalize_le.
  - eapply effect_le_trans.
    + apply effect_meet_le_right.
    + apply le_normalize.
Qed.

(** Mutual correctness theorem for symbolic joins, meets, and their product
    helpers.  Modeled join constraints produce a common supertype; modeled
    meet constraints produce a common subtype. *)
Lemma symbolic_type_merge_correct_mut :
  (forall left right result C,
      symbolic_type_join left right result C ->
      forall sigma,
        models sigma C ->
        subtype (instantiate_ty sigma left) (instantiate_ty sigma result) /\
        subtype (instantiate_ty sigma right) (instantiate_ty sigma result)) /\
  (forall left right result C,
      symbolic_type_meet left right result C ->
      forall sigma,
        models sigma C ->
        subtype (instantiate_ty sigma result) (instantiate_ty sigma left) /\
        subtype (instantiate_ty sigma result) (instantiate_ty sigma right)) /\
  (forall left right result C,
      symbolic_type_join_list left right result C ->
      forall sigma,
        models sigma C ->
        Forall2
          subtype
          (map (instantiate_ty sigma) left)
          (map (instantiate_ty sigma) result) /\
        Forall2
          subtype
          (map (instantiate_ty sigma) right)
          (map (instantiate_ty sigma) result)) /\
  (forall left right result C,
      symbolic_type_meet_list left right result C ->
      forall sigma,
        models sigma C ->
        Forall2
          subtype
          (map (instantiate_ty sigma) result)
          (map (instantiate_ty sigma) left) /\
        Forall2
          subtype
          (map (instantiate_ty sigma) result)
          (map (instantiate_ty sigma) right)).
Proof.
  apply symbolic_type_merge_mutind.
  - intros sigma Hmodels. split; constructor.
  - intros sigma Hmodels. split; constructor.
  - intros left_domain left_latent left_codomain
      right_domain right_latent right_codomain
      result_domain result_codomain domain_constraint codomain_constraint
      Hdomain IHdomain Hcodomain IHcodomain sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma domain_constraint codomain_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_domain Hmodels_codomain].
    destruct (IHdomain sigma Hmodels_domain)
      as [Hresult_left_domain Hresult_right_domain].
    destruct (IHcodomain sigma Hmodels_codomain)
      as [Hleft_result_codomain Hright_result_codomain].
    simpl. split; apply SubArrow.
    + exact Hresult_left_domain.
    + apply instantiate_symbolic_join_le_left.
    + exact Hleft_result_codomain.
    + exact Hresult_right_domain.
    + apply instantiate_symbolic_join_le_right.
    + exact Hright_result_codomain.
  - intros left_components right_components result_components C
      Hcomponents IHcomponents sigma Hmodels.
    destruct (IHcomponents sigma Hmodels) as [Hleft Hright].
    simpl. split; constructor; assumption.
  - intros left right Hshapes sigma Hmodels.
    destruct Hmodels as [_ Hfalse]. simpl in Hfalse. contradiction.
  - intros sigma Hmodels. split; constructor.
  - intros sigma Hmodels. split; constructor.
  - intros left_domain left_latent left_codomain
      right_domain right_latent right_codomain left_concrete right_concrete
      result_domain result_codomain domain_constraint codomain_constraint
      Hleft_concrete Hright_concrete Hdomain IHdomain Hcodomain IHcodomain
      sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma domain_constraint codomain_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_domain Hmodels_codomain].
    destruct (IHdomain sigma Hmodels_domain)
      as [Hleft_result_domain Hright_result_domain].
    destruct (IHcodomain sigma Hmodels_codomain)
      as [Hresult_left_codomain Hresult_right_codomain].
    pose proof
      (concrete_symbolic_effect_reified_wf
        left_latent left_concrete Hleft_concrete) as Hleft_wf.
    pose proof
      (concrete_symbolic_effect_reified_wf
        right_latent right_concrete Hright_concrete) as Hright_wf.
    pose proof
      (symbolize_effect_meet_concrete
        left_concrete right_concrete Hleft_wf Hright_wf) as Hresult_concrete.
    simpl. split; apply SubArrow.
    + exact Hleft_result_domain.
    + rewrite (concrete_symbolic_effect_instantiates
        sigma (symbolize_effect (effect_meet left_concrete right_concrete))
        (effect_meet left_concrete right_concrete) Hresult_concrete).
      rewrite (concrete_symbolic_effect_instantiates
        sigma left_latent left_concrete Hleft_concrete).
      apply normalize_effect_meet_le_left.
    + exact Hresult_left_codomain.
    + exact Hright_result_domain.
    + rewrite (concrete_symbolic_effect_instantiates
        sigma (symbolize_effect (effect_meet left_concrete right_concrete))
        (effect_meet left_concrete right_concrete) Hresult_concrete).
      rewrite (concrete_symbolic_effect_instantiates
        sigma right_latent right_concrete Hright_concrete).
      apply normalize_effect_meet_le_right.
    + exact Hresult_right_codomain.
  - intros left_components right_components result_components C
      Hcomponents IHcomponents sigma Hmodels.
    destruct (IHcomponents sigma Hmodels) as [Hleft Hright].
    simpl. split; constructor; assumption.
  - intros left right Hshapes sigma Hmodels.
    destruct Hmodels as [_ Hfalse]. simpl in Hfalse. contradiction.
  - intros sigma Hmodels. split; constructor.
  - intros left left_tail right right_tail result result_tail
      head_constraint tail_constraint Hhead IHhead Htail IHtail
      sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma head_constraint tail_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_head Hmodels_tail].
    destruct (IHhead sigma Hmodels_head) as [Hleft_head Hright_head].
    destruct (IHtail sigma Hmodels_tail) as [Hleft_tail Hright_tail].
    simpl. split; constructor; assumption.
  - intros sigma Hmodels. split; constructor.
  - intros left left_tail right right_tail result result_tail
      head_constraint tail_constraint Hhead IHhead Htail IHtail
      sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma head_constraint tail_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_head Hmodels_tail].
    destruct (IHhead sigma Hmodels_head) as [Hleft_head Hright_head].
    destruct (IHtail sigma Hmodels_tail) as [Hleft_tail Hright_tail].
    simpl. split; constructor; assumption.
Qed.

(** Public common-supertype correctness theorem for symbolic joins. *)
Theorem symbolic_type_join_correct :
  forall sigma left right result C,
    symbolic_type_join left right result C ->
    models sigma C ->
    subtype (instantiate_ty sigma left) (instantiate_ty sigma result) /\
    subtype (instantiate_ty sigma right) (instantiate_ty sigma result).
Proof.
  intros sigma left right result C Hjoin Hmodels.
  apply (proj1 symbolic_type_merge_correct_mut
    left right result C Hjoin sigma Hmodels).
Qed.

(** Public common-subtype correctness theorem for symbolic meets. *)
Theorem symbolic_type_meet_correct :
  forall sigma left right result C,
    symbolic_type_meet left right result C ->
    models sigma C ->
    subtype (instantiate_ty sigma result) (instantiate_ty sigma left) /\
    subtype (instantiate_ty sigma result) (instantiate_ty sigma right).
Proof.
  intros sigma left right result C Hmeet Hmodels.
  apply (proj1 (proj2 symbolic_type_merge_correct_mut)
    left right result C Hmeet sigma Hmodels).
Qed.

(** Concrete effect meet respects semantic equivalence of both operands. *)
Lemma effect_meet_respects_equiv :
  forall Phi Phi' Psi Psi',
    Phi ≈ Phi' ->
    Psi ≈ Psi' ->
    effect_meet Phi Psi ≈ effect_meet Phi' Psi'.
Proof.
  intros Phi Phi' Psi Psi' [HPhi HPhi'] [HPsi HPsi']. split.
  - apply effect_meet_greatest.
    + eapply effect_le_trans.
      * apply effect_meet_le_left.
      * exact HPhi.
    + eapply effect_le_trans.
      * apply effect_meet_le_right.
      * exact HPsi.
  - apply effect_meet_greatest.
    + eapply effect_le_trans.
      * apply effect_meet_le_left.
      * exact HPhi'.
    + eapply effect_le_trans.
      * apply effect_meet_le_right.
      * exact HPsi'.
Qed.

(** Reifying the concrete meet in symbolic syntax commutes with instantiation
    up to semantic effect equivalence. *)
Lemma instantiate_symbolized_effect_meet :
  forall sigma left_symbolic right_symbolic left_concrete right_concrete,
    concrete_symbolic_effect left_symbolic left_concrete ->
    concrete_symbolic_effect right_symbolic right_concrete ->
    instantiate_effect sigma
      (symbolize_effect (effect_meet left_concrete right_concrete)) ≈
    effect_meet
      (instantiate_effect sigma left_symbolic)
      (instantiate_effect sigma right_symbolic).
Proof.
  intros sigma left_symbolic right_symbolic left_concrete right_concrete
    Hleft Hright.
  pose proof
    (concrete_symbolic_effect_reified_wf
      left_symbolic left_concrete Hleft) as Hleft_wf.
  pose proof
    (concrete_symbolic_effect_reified_wf
      right_symbolic right_concrete Hright) as Hright_wf.
  pose proof
    (symbolize_effect_meet_concrete
      left_concrete right_concrete Hleft_wf Hright_wf) as Hresult.
  rewrite (concrete_symbolic_effect_instantiates
    sigma (symbolize_effect (effect_meet left_concrete right_concrete))
    (effect_meet left_concrete right_concrete) Hresult).
  rewrite (concrete_symbolic_effect_instantiates
    sigma left_symbolic left_concrete Hleft).
  rewrite (concrete_symbolic_effect_instantiates
    sigma right_symbolic right_concrete Hright).
  eapply effect_equiv_trans.
  - apply normalize_coverage_equiv.
  - apply effect_meet_respects_equiv.
    + apply effect_equiv_sym. apply normalize_coverage_equiv.
    + apply effect_equiv_sym. apply normalize_coverage_equiv.
Qed.

(** Structural equivalence of concrete types modulo semantic equivalence of
    latent effects.  This replaces literal equality in the paper because the
    Rocq development represents effects as lists. *)
Inductive type_effect_equiv : ty -> ty -> Prop :=
| TypeEffectEquivUnit :
    type_effect_equiv Syntax.TyUnit Syntax.TyUnit
| TypeEffectEquivNat :
    type_effect_equiv Syntax.TyNat Syntax.TyNat
| TypeEffectEquivArrow :
    forall left_domain left_latent left_codomain
           right_domain right_latent right_codomain,
      type_effect_equiv left_domain right_domain ->
      left_latent ≈ right_latent ->
      type_effect_equiv left_codomain right_codomain ->
      type_effect_equiv
        (Syntax.TyArrow left_domain left_latent left_codomain)
        (Syntax.TyArrow right_domain right_latent right_codomain)
| TypeEffectEquivProduct :
    forall left_components right_components,
      Forall2 type_effect_equiv left_components right_components ->
      type_effect_equiv
        (Syntax.TyProduct left_components)
        (Syntax.TyProduct right_components).

(** Concrete structural joins and meets used to state the commutation theorem.
    These are the paper's concrete versions of [join_theta]/[meet_theta]. *)
Inductive concrete_type_join : ty -> ty -> ty -> Prop :=
| ConcreteJoinUnit :
    concrete_type_join Syntax.TyUnit Syntax.TyUnit Syntax.TyUnit
| ConcreteJoinNat :
    concrete_type_join Syntax.TyNat Syntax.TyNat Syntax.TyNat
| ConcreteJoinArrow :
    forall left_domain left_latent left_codomain
           right_domain right_latent right_codomain
           result_domain result_codomain,
      concrete_type_meet left_domain right_domain result_domain ->
      concrete_type_join left_codomain right_codomain result_codomain ->
      concrete_type_join
        (Syntax.TyArrow left_domain left_latent left_codomain)
        (Syntax.TyArrow right_domain right_latent right_codomain)
        (Syntax.TyArrow
          result_domain
          (sequential_effect left_latent right_latent)
          result_codomain)
| ConcreteJoinProduct :
    forall left_components right_components result_components,
      concrete_type_join_list
        left_components right_components result_components ->
      concrete_type_join
        (Syntax.TyProduct left_components)
        (Syntax.TyProduct right_components)
        (Syntax.TyProduct result_components)
with concrete_type_meet : ty -> ty -> ty -> Prop :=
| ConcreteMeetUnit :
    concrete_type_meet Syntax.TyUnit Syntax.TyUnit Syntax.TyUnit
| ConcreteMeetNat :
    concrete_type_meet Syntax.TyNat Syntax.TyNat Syntax.TyNat
| ConcreteMeetArrow :
    forall left_domain left_latent left_codomain
           right_domain right_latent right_codomain
           result_domain result_codomain,
      concrete_type_join left_domain right_domain result_domain ->
      concrete_type_meet left_codomain right_codomain result_codomain ->
      concrete_type_meet
        (Syntax.TyArrow left_domain left_latent left_codomain)
        (Syntax.TyArrow right_domain right_latent right_codomain)
        (Syntax.TyArrow
          result_domain
          (effect_meet left_latent right_latent)
          result_codomain)
| ConcreteMeetProduct :
    forall left_components right_components result_components,
      concrete_type_meet_list
        left_components right_components result_components ->
      concrete_type_meet
        (Syntax.TyProduct left_components)
        (Syntax.TyProduct right_components)
        (Syntax.TyProduct result_components)
with concrete_type_join_list : list ty -> list ty -> list ty -> Prop :=
| ConcreteJoinListNil :
    concrete_type_join_list [] [] []
| ConcreteJoinListCons :
    forall left left_tail right right_tail result result_tail,
      concrete_type_join left right result ->
      concrete_type_join_list left_tail right_tail result_tail ->
      concrete_type_join_list
        (left :: left_tail)
        (right :: right_tail)
        (result :: result_tail)
with concrete_type_meet_list : list ty -> list ty -> list ty -> Prop :=
| ConcreteMeetListNil :
    concrete_type_meet_list [] [] []
| ConcreteMeetListCons :
    forall left left_tail right right_tail result result_tail,
      concrete_type_meet left right result ->
      concrete_type_meet_list left_tail right_tail result_tail ->
      concrete_type_meet_list
        (left :: left_tail)
        (right :: right_tail)
        (result :: result_tail).

(** Mutual instantiation-commutation theorem.  Successful symbolic merging
    instantiates to a corresponding concrete merge result, modulo structural
    type equivalence and semantic effect equivalence. *)
Lemma symbolic_type_merge_commutes_mut :
  (forall left right result C,
      symbolic_type_join left right result C ->
      forall sigma,
        models sigma C ->
        exists concrete_result,
          concrete_type_join
            (instantiate_ty sigma left)
            (instantiate_ty sigma right)
            concrete_result /\
          type_effect_equiv
            (instantiate_ty sigma result) concrete_result) /\
  (forall left right result C,
      symbolic_type_meet left right result C ->
      forall sigma,
        models sigma C ->
        exists concrete_result,
          concrete_type_meet
            (instantiate_ty sigma left)
            (instantiate_ty sigma right)
            concrete_result /\
          type_effect_equiv
            (instantiate_ty sigma result) concrete_result) /\
  (forall left right result C,
      symbolic_type_join_list left right result C ->
      forall sigma,
        models sigma C ->
        exists concrete_result,
          concrete_type_join_list
            (map (instantiate_ty sigma) left)
            (map (instantiate_ty sigma) right)
            concrete_result /\
          Forall2
            type_effect_equiv
            (map (instantiate_ty sigma) result)
            concrete_result) /\
  (forall left right result C,
      symbolic_type_meet_list left right result C ->
      forall sigma,
        models sigma C ->
        exists concrete_result,
          concrete_type_meet_list
            (map (instantiate_ty sigma) left)
            (map (instantiate_ty sigma) right)
            concrete_result /\
          Forall2
            type_effect_equiv
            (map (instantiate_ty sigma) result)
            concrete_result).
Proof.
  apply symbolic_type_merge_mutind.
  - intros sigma Hmodels. exists Syntax.TyUnit. split; constructor.
  - intros sigma Hmodels. exists Syntax.TyNat. split; constructor.
  - intros left_domain left_latent left_codomain
      right_domain right_latent right_codomain
      result_domain result_codomain domain_constraint codomain_constraint
      Hdomain IHdomain Hcodomain IHcodomain sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma domain_constraint codomain_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_domain Hmodels_codomain].
    destruct (IHdomain sigma Hmodels_domain)
      as [concrete_domain [Hconcrete_domain Hequiv_domain]].
    destruct (IHcodomain sigma Hmodels_codomain)
      as [concrete_codomain [Hconcrete_codomain Hequiv_codomain]].
    exists (Syntax.TyArrow
      concrete_domain
      (sequential_effect
        (instantiate_effect sigma left_latent)
        (instantiate_effect sigma right_latent))
      concrete_codomain).
    split.
    + simpl. constructor; assumption.
    + simpl. constructor.
      * exact Hequiv_domain.
      * apply instantiate_symbolic_join.
      * exact Hequiv_codomain.
  - intros left_components right_components result_components C
      Hcomponents IHcomponents sigma Hmodels.
    destruct (IHcomponents sigma Hmodels)
      as [concrete_components [Hconcrete Hequiv]].
    exists (Syntax.TyProduct concrete_components). split.
    + simpl. constructor. exact Hconcrete.
    + simpl. constructor. exact Hequiv.
  - intros left right Hshapes sigma Hmodels.
    destruct Hmodels as [_ Hfalse]. simpl in Hfalse. contradiction.
  - intros sigma Hmodels. exists Syntax.TyUnit. split; constructor.
  - intros sigma Hmodels. exists Syntax.TyNat. split; constructor.
  - intros left_domain left_latent left_codomain
      right_domain right_latent right_codomain left_concrete right_concrete
      result_domain result_codomain domain_constraint codomain_constraint
      Hleft_concrete Hright_concrete Hdomain IHdomain Hcodomain IHcodomain
      sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma domain_constraint codomain_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_domain Hmodels_codomain].
    destruct (IHdomain sigma Hmodels_domain)
      as [concrete_domain [Hconcrete_domain Hequiv_domain]].
    destruct (IHcodomain sigma Hmodels_codomain)
      as [concrete_codomain [Hconcrete_codomain Hequiv_codomain]].
    exists (Syntax.TyArrow
      concrete_domain
      (effect_meet
        (instantiate_effect sigma left_latent)
        (instantiate_effect sigma right_latent))
      concrete_codomain).
    split.
    + simpl. constructor; assumption.
    + simpl. constructor.
      * exact Hequiv_domain.
      * apply instantiate_symbolized_effect_meet; assumption.
      * exact Hequiv_codomain.
  - intros left_components right_components result_components C
      Hcomponents IHcomponents sigma Hmodels.
    destruct (IHcomponents sigma Hmodels)
      as [concrete_components [Hconcrete Hequiv]].
    exists (Syntax.TyProduct concrete_components). split.
    + simpl. constructor. exact Hconcrete.
    + simpl. constructor. exact Hequiv.
  - intros left right Hshapes sigma Hmodels.
    destruct Hmodels as [_ Hfalse]. simpl in Hfalse. contradiction.
  - intros sigma Hmodels. exists []. split; constructor.
  - intros left left_tail right right_tail result result_tail
      head_constraint tail_constraint Hhead IHhead Htail IHtail
      sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma head_constraint tail_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_head Hmodels_tail].
    destruct (IHhead sigma Hmodels_head)
      as [concrete_head [Hconcrete_head Hequiv_head]].
    destruct (IHtail sigma Hmodels_tail)
      as [concrete_tail [Hconcrete_tail Hequiv_tail]].
    exists (concrete_head :: concrete_tail). simpl. split; constructor; assumption.
  - intros sigma Hmodels. exists []. split; constructor.
  - intros left left_tail right right_tail result result_tail
      head_constraint tail_constraint Hhead IHhead Htail IHtail
      sigma Hmodels.
    pose proof (proj1 Hmodels) as Hsigma.
    apply (proj1 (models_and_iff sigma head_constraint tail_constraint
      Hsigma)) in Hmodels.
    destruct Hmodels as [Hmodels_head Hmodels_tail].
    destruct (IHhead sigma Hmodels_head)
      as [concrete_head [Hconcrete_head Hequiv_head]].
    destruct (IHtail sigma Hmodels_tail)
      as [concrete_tail [Hconcrete_tail Hequiv_tail]].
    exists (concrete_head :: concrete_tail). simpl. split; constructor; assumption.
Qed.

(** Public instantiation-commutation theorem for symbolic joins. *)
Theorem symbolic_type_join_commutes :
  forall sigma left right result C,
    symbolic_type_join left right result C ->
    models sigma C ->
    exists concrete_result,
      concrete_type_join
        (instantiate_ty sigma left)
        (instantiate_ty sigma right)
        concrete_result /\
      type_effect_equiv (instantiate_ty sigma result) concrete_result.
Proof.
  intros sigma left right result C Hjoin Hmodels.
  apply (proj1 symbolic_type_merge_commutes_mut
    left right result C Hjoin sigma Hmodels).
Qed.

(** Public instantiation-commutation theorem for symbolic meets. *)
Theorem symbolic_type_meet_commutes :
  forall sigma left right result C,
    symbolic_type_meet left right result C ->
    models sigma C ->
    exists concrete_result,
      concrete_type_meet
        (instantiate_ty sigma left)
        (instantiate_ty sigma right)
        concrete_result /\
      type_effect_equiv (instantiate_ty sigma result) concrete_result.
Proof.
  intros sigma left right result C Hmeet Hmodels.
  apply (proj1 (proj2 symbolic_type_merge_commutes_mut)
    left right result C Hmeet sigma Hmodels).
Qed.
