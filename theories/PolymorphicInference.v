(** Size inference for the explicitly effect-polymorphic source language.
    Programmer-written annotations and explicit effect arguments use the core
    size-free grammar. Constraints from suspended bodies remain universally
    quantified at their generating effect scope. *)
From Stdlib Require Import Arith Bool Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Bandwidth
  Typing SizeInference Symbolic Compatibility RootConstraints PolymorphicEffects
  PolymorphicSyntax PolymorphicTyping PolymorphicTypeSubstitution
  PolymorphicSymbolic PolymorphicConstraints PolymorphicInferenceTypes.
Import ListNotations.
Open Scope nat_scope.

Inductive pi_expr : Type :=
| PIEVar : nat -> pi_expr
| PIEUnit : pi_expr
| PIENat : nat -> pi_expr
| PIELambda : poly_ty -> pi_expr -> pi_expr
| PIETuple : list pi_expr -> pi_expr
| PIEApp : pi_expr -> pi_expr -> pi_expr
| PIELet : pi_expr -> pi_expr -> pi_expr
| PIEIfZero : pi_expr -> pi_expr -> pi_expr -> pi_expr
| PIEDownload : size_variable -> positive_rational -> pi_expr
| PIEKnownDownload : nonnegative_rational -> positive_rational -> pi_expr
| PIEParallel : list pi_expr -> pi_expr
| PIEAbsEff : pi_expr -> pi_expr
| PIEAppEff : pi_expr -> open_effect -> pi_expr.

Inductive pi_value : pi_expr -> Prop :=
| PIVUnit : pi_value PIEUnit
| PIVNat : forall n, pi_value (PIENat n)
| PIVLambda : forall T e, pi_value (PIELambda T e)
| PIVTuple : forall es, Forall pi_value es -> pi_value (PIETuple es)
| PIVAbsEff : forall e, pi_value (PIEAbsEff e).

Fixpoint pi_instantiate (sigma : size_assignment) (e : pi_expr) : poly_expr :=
  match e with
  | PIEVar i => PEVar i
  | PIEUnit => PEUnit
  | PIENat n => PENat n
  | PIELambda A e => PELambda A (pi_instantiate sigma e)
  | PIETuple es => PETuple (map (pi_instantiate sigma) es)
  | PIEApp e f => PEApp (pi_instantiate sigma e) (pi_instantiate sigma f)
  | PIELet e f => PELet (pi_instantiate sigma e) (pi_instantiate sigma f)
  | PIEIfZero e f g => PEIfZero (pi_instantiate sigma e)
      (pi_instantiate sigma f) (pi_instantiate sigma g)
  | PIEDownload a t => PEDownload (sigma a) t
  | PIEKnownDownload s t => PEDownload s t
  | PIEParallel es => PEParallel (map (pi_instantiate sigma) es)
  | PIEAbsEff e => PEAbsEff (pi_instantiate sigma e)
  | PIEAppEff e F => PEAppEff (pi_instantiate sigma e) F
  end.

Lemma pi_instantiate_value : forall e,
  pi_value e -> forall sigma, poly_value (pi_instantiate sigma e).
Proof.
  fix IH 2. intros e H sigma. destruct H; simpl; constructor.
  induction H; simpl; constructor; auto.
Qed.

Fixpoint pi_parallel_effects (Es : list ps_effect) : ps_effect :=
  match Es with [] => ps_empty | E :: Es => PSEPar E (pi_parallel_effects Es) end.
Fixpoint pi_conjoin (Cs : list local_constraint) : local_constraint :=
  match Cs with [] => LNumeric CTop | C :: Cs => LAnd C (pi_conjoin Cs) end.

Lemma pi_parallel_instantiate : forall sigma Es,
  ps_instantiate sigma (pi_parallel_effects Es) =
  poly_parallel_effects (map (ps_instantiate sigma) Es).
Proof. intros sigma Es. induction Es; simpl; congruence. Qed.

Lemma pi_scope_reflect : forall d E sigma,
  eff_scoped d (ps_instantiate sigma E) -> ps_scoped d E.
Proof.
  intros d E. induction E; intros sigma H; inversion H; subst; simpl; eauto.
Qed.

(** A normalization step is admissible in the declarative core judgment. *)
Lemma pi_typing_normalize_effect : forall d Gamma e T E sigma,
  poly_has_type d Gamma e T (ps_instantiate sigma E) ->
  poly_has_type d Gamma e T (ps_instantiate sigma (ps_norm E)).
Proof.
  intros d Gamma e T E sigma H.
  destruct (poly_typing_wf _ _ _ _ _ H) as [HT HE].
  eapply PHTSub; [exact H|apply poly_subtype_refl| |exact HT|].
  - apply (proj2 (ps_norm_core_equiv d E sigma)).
  - apply ps_instantiate_scoped, ps_norm_scoped. eapply pi_scope_reflect; eauto.
Qed.

Fixpoint pi_effect_subst (s : nat -> open_effect) (e : pi_expr) : pi_expr :=
  match e with
  | PIEVar i => PIEVar i
  | PIEUnit => PIEUnit
  | PIENat n => PIENat n
  | PIELambda A e => PIELambda (poly_ty_subst s A) (pi_effect_subst s e)
  | PIETuple es => PIETuple (map (pi_effect_subst s) es)
  | PIEApp e f => PIEApp (pi_effect_subst s e) (pi_effect_subst s f)
  | PIELet e f => PIELet (pi_effect_subst s e) (pi_effect_subst s f)
  | PIEIfZero e f g => PIEIfZero (pi_effect_subst s e)
      (pi_effect_subst s f) (pi_effect_subst s g)
  | PIEDownload a t => PIEDownload a t
  | PIEKnownDownload a t => PIEKnownDownload a t
  | PIEParallel es => PIEParallel (map (pi_effect_subst s) es)
  | PIEAbsEff e => PIEAbsEff (pi_effect_subst (eff_up_subst s) e)
  | PIEAppEff e F => PIEAppEff (pi_effect_subst s e) (eff_subst s F)
  end.

Theorem pi_instantiate_effect_subst : forall e sigma s,
  pi_instantiate sigma (pi_effect_subst s e) =
  poly_effect_subst s (pi_instantiate sigma e).
Proof.
  fix IH 1. intros e sigma s. destruct e; simpl; try reflexivity;
    f_equal; try apply IH; rewrite !map_map; induction l; simpl; f_equal; auto.
Qed.

Fixpoint pi_size_variables (e : pi_expr) : list size_variable :=
  match e with
  | PIEVar _ | PIEUnit | PIENat _ | PIEKnownDownload _ _ => []
  | PIEDownload a _ => [a]
  | PIELambda _ e | PIEAbsEff e | PIEAppEff e _ => pi_size_variables e
  | PIEApp e f | PIELet e f => pi_size_variables e ++ pi_size_variables f
  | PIEIfZero e f g => pi_size_variables e ++ pi_size_variables f ++ pi_size_variables g
  | PIETuple es | PIEParallel es => flat_map pi_size_variables es
  end.

Definition pi_context := list pst_type.
Definition pi_context_wf d (Gamma : pi_context) := Forall (pst_scoped d) Gamma.
Definition pi_context_shift (Gamma : pi_context) :=
  map (pst_subst (fun i => EffVar (S i))) Gamma.
Definition pi_instantiate_context sigma (Gamma : pi_context) :=
  map (pst_instantiate sigma) Gamma.

Lemma pi_instantiate_context_shift : forall sigma Gamma,
  pi_instantiate_context sigma (pi_context_shift Gamma) =
  poly_context_shift (pi_instantiate_context sigma Gamma).
Proof.
  intros sigma Gamma. unfold pi_instantiate_context, pi_context_shift, poly_context_shift.
  rewrite !map_map. apply map_ext. intro T.
  rewrite pst_instantiate_subst. apply poly_ty_subst_vars.
Qed.

Lemma pi_instantiate_context_wf : forall sigma d Gamma,
  pi_context_wf d Gamma -> poly_context_wf d (pi_instantiate_context sigma Gamma).
Proof.
  intros sigma d Gamma H. induction H; simpl; constructor; auto using pst_instantiate_scoped.
Qed.

Lemma pi_typing_normalize_type : forall sigma d Gamma e T E,
  pst_scoped d T -> poly_has_type d Gamma e (pst_instantiate sigma T) E ->
  poly_has_type d Gamma e (pst_instantiate sigma (pst_norm T)) E.
Proof.
  intros sigma d Gamma e T E HT H.
  eapply PHTSub; [exact H| |apply eff_le_refl| |].
  - apply (proj2 (pst_norm_instantiate T d sigma)).
  - apply pst_instantiate_scoped, pst_norm_scoped. exact HT.
  - exact (proj2 (poly_typing_wf _ _ _ _ _ H)).
Qed.

Inductive pi_infers (M : Q) : nat -> pi_context -> pi_expr -> pst_type ->
    ps_effect -> local_constraint -> Prop :=
| PIIVar : forall d Gamma i T,
    nth_error Gamma i = Some T -> pst_scoped d T ->
    pi_infers M d Gamma (PIEVar i) T ps_empty (LNumeric CTop)
| PIIUnit : forall d Gamma,
    pi_infers M d Gamma PIEUnit PSTyUnit ps_empty (LNumeric CTop)
| PIINat : forall d Gamma n,
    pi_infers M d Gamma (PIENat n) PSTyNat ps_empty (LNumeric CTop)
| PIITuple : forall d Gamma es Ts Cs,
    Forall pi_value es ->
    pi_infers_list M d Gamma es Ts (repeat ps_empty (length es)) Cs ->
    pi_infers M d Gamma (PIETuple es) (PSTyProduct Ts) ps_empty (pi_conjoin Cs)
| PIIDownload : forall d Gamma a t,
    pi_infers M d Gamma (PIEDownload a t) PSTyUnit (PSESize a t) (LNumeric (CUpper a M))
| PIIKnownDownload : forall d Gamma s t,
    pi_infers M d Gamma (PIEKnownDownload s t) PSTyUnit
      (PSELiteral (download_effect s t)) (LNumeric CTop)
| PIILet : forall d Gamma e f A B E F C D,
    pi_infers M d Gamma e A E C -> pi_infers M d (A :: Gamma) f B F D ->
    pi_infers M d Gamma (PIELet e f) B (ps_norm (PSEJoin E F)) (LAnd C D)
| PIIIfZero : forall d Gamma e f g T U V E F G C D H,
    pi_infers M d Gamma e PSTyNat E C ->
    pi_infers M d Gamma f T F D -> pi_infers M d Gamma g U G H ->
    pst_join T U = Some V -> pst_scoped d V ->
    pi_infers M d Gamma (PIEIfZero e f g) (pst_norm V)
      (ps_norm (PSEJoin E (PSEJoin F G))) (LAnd C (LAnd D H))
| PIIParallel : forall d Gamma es Ts Es Cs,
    pi_infers_list M d Gamma es Ts Es Cs ->
    pi_infers M d Gamma (PIEParallel es) (PSTyProduct Ts)
      (ps_norm (pi_parallel_effects Es)) (pi_conjoin Cs)
| PIIAbs : forall d Gamma A e B E C,
    poly_ty_wf d A -> pi_infers M d (pst_embed A :: Gamma) e B E C ->
    pi_infers M d Gamma (PIELambda A e) (PSTyArrow (pst_embed A) E B)
      ps_empty C
| PIIApp : forall d Gamma e f A B U E F G C D,
    pi_infers M d Gamma e (PSTyArrow A G B) E C ->
    pi_infers M d Gamma f U F D ->
    pi_infers M d Gamma (PIEApp e f) B (ps_norm (PSEJoin E (PSEJoin F G)))
      (LAnd C (LAnd D (ps_constraint_norm (pst_subtype_constraint d U A))))
| PIIAbsEff : forall d Gamma e T E C,
    pi_context_wf d Gamma ->
    pi_infers M (S d) (pi_context_shift Gamma) e T E C ->
    pi_infers M d Gamma (PIEAbsEff e) (PSTyForall T E) ps_empty C
| PIIAppEff : forall d Gamma e T E F G C,
    pi_infers M d Gamma e (PSTyForall T G) E C -> eff_scoped d F ->
    pi_infers M d Gamma (PIEAppEff e F) (pst_norm (pst_subst (eff_single F) T))
      (ps_norm (PSEJoin E (ps_subst (eff_single F) G))) C
with pi_infers_list (M : Q) : nat -> pi_context -> list pi_expr -> list pst_type ->
    list ps_effect -> list local_constraint -> Prop :=
| PIINil : forall d Gamma, pi_infers_list M d Gamma [] [] [] []
| PIICons : forall d Gamma e es T Ts E Es C Cs,
    pi_infers M d Gamma e T E C -> pi_infers_list M d Gamma es Ts Es Cs ->
    pi_infers_list M d Gamma (e :: es) (T :: Ts) (E :: Es) (C :: Cs).

Scheme pi_infers_mutind := Induction for pi_infers Sort Prop
with pi_infers_list_mutind := Induction for pi_infers_list Sort Prop.
Combined Scheme pi_inference_mutind from pi_infers_mutind, pi_infers_list_mutind.

Theorem pi_inference_source_mut : forall M,
  (forall d Gamma e T E C, pi_infers M d Gamma e T E C ->
     forall sigma, poly_source (pi_instantiate sigma e)) /\
  (forall d Gamma es Ts Es Cs, pi_infers_list M d Gamma es Ts Es Cs ->
     forall sigma, Forall poly_source (map (pi_instantiate sigma) es)).
Proof.
  intro M. apply pi_inference_mutind; intros; simpl; try (constructor; auto).
  - apply Forall_map. eapply Forall_impl; [|eassumption].
    intros. apply pi_instantiate_value. assumption.
Qed.

Lemma pi_product_scoped : forall d Ts,
  Forall (pst_scoped d) Ts -> pst_scoped d (PSTyProduct Ts).
Proof. intros d Ts H. induction H; simpl; auto. Qed.

Lemma pi_parallel_scoped : forall d Es,
  Forall (ps_scoped d) Es -> ps_scoped d (pi_parallel_effects Es).
Proof. intros d Es H. induction H; simpl; auto. constructor. Qed.

Lemma pi_single_scoped : forall d F,
  eff_scoped d F -> forall i, i < S d -> eff_scoped d (eff_single F i).
Proof. intros d F H [|i] Hi; simpl; auto. constructor. lia. Qed.

Lemma pi_type_subst_scoped : forall d d' T s,
  pst_scoped d T -> (forall i, i < d -> eff_scoped d' (s i)) ->
  pst_scoped d' (pst_subst s T).
Proof.
  intros d d' T s HT Hs. apply (pst_scope_reflect _ _ ps_zero_assignment).
  rewrite pst_instantiate_subst. eapply poly_ty_wf_subst; eauto using pst_instantiate_scoped.
Qed.

Theorem pi_generated_wf_mut : forall M,
  (forall d Gamma e T E C, pi_infers M d Gamma e T E C ->
    pst_scoped d T /\ ps_scoped d E /\ ps_constraint_wf C) /\
  (forall d Gamma es Ts Es Cs, pi_infers_list M d Gamma es Ts Es Cs ->
    Forall (pst_scoped d) Ts /\ Forall (ps_scoped d) Es /\ ps_constraint_wf (pi_conjoin Cs)).
Proof.
  intro M. apply pi_inference_mutind.
  - intros. repeat split; auto. constructor.
  - intros. repeat split; auto. constructor.
  - intros. repeat split; auto. constructor.
  - intros d Gamma es Ts Cs Hv Ht [HT [HE HC]].
    split; [apply pi_product_scoped; exact HT|]. split; [constructor|exact HC].
  - intros. repeat split; auto.
  - intros. repeat split; auto. apply poly_download_effect_wf.
  - intros d Gamma e f A B E F C D He [HA [HE HC]] Hf [HB [HF HD]].
    split; [exact HB|]. split; [apply ps_norm_scoped; split; assumption|split; assumption].
  - intros d Gamma e f g T U V E F G C D H He [HT0 [HE HC]]
      Hf [HT [HF HD]] Hg [HU [HG HH]] Hjoin HV.
    split; [apply pst_norm_scoped; exact HV|]. split.
    + apply ps_norm_scoped. simpl. tauto.
    + simpl. tauto.
  - intros d Gamma es Ts Es Cs Ht [HT [HE HC]].
    split; [apply pi_product_scoped; exact HT|]. split; auto.
    apply ps_norm_scoped, pi_parallel_scoped. exact HE.
  - intros d Gamma A e B E C HA He [HB [HE HC]].
    split; [simpl; repeat split; auto using pst_embed_scoped|].
    split; [constructor|exact HC].
  - intros d Gamma e f A B U E F G C D He [HT [HE HC]] Hf [HU [HF HD]].
    simpl in HT. destruct HT as [HA [HG HB]].
    split; [exact HB|]. split.
    + apply ps_norm_scoped. simpl. tauto.
    + simpl. split; [exact HC|]. split; [exact HD|].
      apply ps_constraint_norm_wf, pst_subtype_constraint_wf; assumption.
  - intros d Gamma e T E C HG He [HT [HE HC]].
    split; [simpl; split; assumption|]. split; [constructor|exact HC].
  - intros d Gamma e T E F G C He [HT [HE HC]] HF.
    simpl in HT. destruct HT as [HT HG]. split.
    + apply pst_norm_scoped. eapply pi_type_subst_scoped; eauto using pi_single_scoped.
    + split; [|exact HC]. apply ps_norm_scoped. split; [exact HE|].
      eapply ps_subst_scoped; eauto using pi_single_scoped.
  - intros. split; [constructor|]. split; [constructor|exact I].
  - intros d Gamma e es T Ts E Es C Cs He [HT [HE HC]] Hes [HTs [HEs HCs]].
    split; [constructor; assumption|]. split; [constructor; assumption|split; assumption].
Qed.

Theorem pi_generated_wf : forall M d Gamma e T E C,
  pi_infers M d Gamma e T E C ->
  pst_scoped d T /\ ps_scoped d E /\ ps_constraint_wf C.
Proof. intros M. exact (proj1 (pi_generated_wf_mut M)). Qed.

Theorem pi_inference_numeric_variables_mut : forall M,
  (forall d Gamma e T E C, pi_infers M d Gamma e T E C ->
    forall a, In a (pi_size_variables e) -> In a (ps_numeric_variables C)) /\
  (forall d Gamma es Ts Es Cs, pi_infers_list M d Gamma es Ts Es Cs ->
    forall a, In a (flat_map pi_size_variables es) ->
      In a (ps_numeric_variables (pi_conjoin Cs))).
Proof.
  intro M. apply pi_inference_mutind; intros;
    cbn [pi_size_variables ps_numeric_variables pi_conjoin constraint_variables flat_map] in *;
    repeat rewrite in_app_iff in *; firstorder.
Qed.

Theorem pi_inference_caps_mut : forall M,
  (forall d Gamma e T E C, pi_infers M d Gamma e T E C ->
    forall sigma, ps_models sigma C -> forall a, In a (pi_size_variables e) -> (sigma a <= M)%Q) /\
  (forall d Gamma es Ts Es Cs, pi_infers_list M d Gamma es Ts Es Cs ->
    forall sigma, ps_models sigma (pi_conjoin Cs) -> forall a,
      In a (flat_map pi_size_variables es) -> (sigma a <= M)%Q).
Proof.
  intro M. apply pi_inference_mutind; intros;
    cbn [pi_size_variables ps_models pi_conjoin models satisfies_constraint flat_map] in *;
    repeat rewrite in_app_iff in *; firstorder; subst; assumption.
Qed.

Theorem pi_compilation_bounds_every_source_variable : forall M d Gamma e T E C D a,
  pi_infers M d Gamma e T E C -> ps_compile C = Some D ->
  In a (pi_size_variables e) -> In a (constraint_variables D).
Proof.
  intros M d Gamma e T E C D a H Hcompile Hin.
  eapply ps_compile_retains_numeric_variables; [exact Hcompile|].
  eapply (proj1 (pi_inference_numeric_variables_mut M)); eauto.
Qed.

Theorem pi_inference_sound_mut : forall M,
  (forall d Gamma e T E C, pi_infers M d Gamma e T E C ->
    forall sigma, ps_models sigma C ->
    poly_has_type d (pi_instantiate_context sigma Gamma) (pi_instantiate sigma e)
      (pst_instantiate sigma T) (ps_instantiate sigma E)) /\
  (forall d Gamma es Ts Es Cs, pi_infers_list M d Gamma es Ts Es Cs ->
    forall sigma, ps_models sigma (pi_conjoin Cs) ->
    poly_types d (pi_instantiate_context sigma Gamma) (map (pi_instantiate sigma) es)
      (map (pst_instantiate sigma) Ts) (map (ps_instantiate sigma) Es)).
Proof.
  intro M. apply pi_inference_mutind.
  - intros d Gamma i T Hi HT sigma HC. simpl. constructor.
    + unfold pi_instantiate_context. rewrite nth_error_map, Hi. reflexivity.
    + apply pst_instantiate_scoped. exact HT.
  - intros. constructor.
  - intros. constructor.
  - intros d Gamma es Ts Cs Hv Ht IH sigma HC. simpl. apply PHTTuple.
    + apply Forall_map. eapply Forall_impl; [|exact Hv].
      intros. apply pi_instantiate_value. assumption.
    + specialize (IH sigma HC). rewrite map_repeat in IH. rewrite length_map. exact IH.
  - intros. constructor.
  - intros. constructor.
  - intros d Gamma e f A B E F C D He IHe Hf IHf sigma [HC HD].
    apply pi_typing_normalize_effect. simpl. eapply PHTLet; eauto.
  - intros d Gamma e f g T U V E F G C D H He IHe Hf IHf Hg IHg Hjoin HV
      sigma [HC [HD HH]].
    apply pi_typing_normalize_effect. apply pi_typing_normalize_type; [exact HV|].
    destruct (pst_join_sound T U V d sigma Hjoin) as [HT HU].
    specialize (IHf sigma HD). specialize (IHg sigma HH).
    eapply PHTIfZero.
    + exact (IHe sigma HC).
    + eapply PHTSub; [exact IHf|exact HT|apply eff_le_refl| |].
      * apply pst_instantiate_scoped. exact HV.
      * exact (proj2 (poly_typing_wf _ _ _ _ _ IHf)).
    + eapply PHTSub; [exact IHg|exact HU|apply eff_le_refl| |].
      * apply pst_instantiate_scoped. exact HV.
      * exact (proj2 (poly_typing_wf _ _ _ _ _ IHg)).
  - intros d Gamma es Ts Es Cs Ht IH sigma HC.
    apply pi_typing_normalize_effect. rewrite pi_parallel_instantiate.
    apply PHTParallel. exact (IH sigma HC).
  - intros d Gamma A e B E C HA He IH sigma HC. simpl.
    rewrite pst_instantiate_embed. apply PHTAbs; [exact HA|].
    specialize (IH sigma HC). unfold pi_instantiate_context in IH. simpl in IH.
    rewrite pst_instantiate_embed in IH. exact IH.
  - intros d Gamma e f A B U E F G C D He IHe Hf IHf sigma [HC [HD Hcompat]].
    apply pi_typing_normalize_effect. simpl.
    specialize (IHe sigma HC). specialize (IHf sigma HD).
    eapply PHTApp; [exact IHe|].
    eapply PHTSub; [exact IHf| |apply eff_le_refl| |].
    + apply (proj1 (pst_subtype_constraint_exact d U A sigma)).
      apply (proj1 (ps_constraint_norm_models _ sigma)). exact Hcompat.
    + pose proof (proj1 (poly_typing_wf _ _ _ _ _ IHe)) as HT.
      inversion HT; subst. assumption.
    + exact (proj2 (poly_typing_wf _ _ _ _ _ IHf)).
  - intros d Gamma e T E C HG He IH sigma HC. simpl.
    apply PHTAbsEff; [apply pi_instantiate_context_wf; exact HG|].
    specialize (IH sigma HC). rewrite pi_instantiate_context_shift in IH. exact IH.
  - intros d Gamma e T E F G C He IH HF sigma HC.
    apply pi_typing_normalize_effect.
    assert (HT : pst_scoped d (pst_subst (eff_single F) T)).
    { destruct (pi_generated_wf _ _ _ _ _ _ _ He) as [[HT HG] _].
      eapply pi_type_subst_scoped; eauto using pi_single_scoped. }
    apply pi_typing_normalize_type; [exact HT|].
    simpl. rewrite pst_instantiate_subst, ps_instantiate_subst.
    eapply PHTAppEff; [exact (IH sigma HC)|exact HF].
  - intros. constructor.
  - intros d Gamma e es T Ts E Es C Cs He IHe Hes IHes sigma [HC HCs].
    simpl. constructor; auto.
Qed.

Theorem pi_inference_sound : forall M d Gamma e T E C sigma,
  pi_infers M d Gamma e T E C -> ps_models sigma C ->
  poly_source (pi_instantiate sigma e) /\
  poly_has_type d (pi_instantiate_context sigma Gamma) (pi_instantiate sigma e)
    (pst_instantiate sigma T) (ps_instantiate sigma E).
Proof.
  intros M d Gamma e T E C sigma H HC. split.
  - eapply (proj1 (pi_inference_source_mut M)); eauto.
  - eapply (proj1 (pi_inference_sound_mut M)); eauto.
Qed.
