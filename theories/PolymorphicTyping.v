(** Declarative typing for explicit effect abstraction and application.
    Composition builds the manuscript's raw effect expressions; semantic
    subsumption admits the equivalent locally normalized result. *)
From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Syntax
  Substitution Typing PolymorphicEffects PolymorphicSyntax
  PolymorphicTypeSubstitution.
Import ListNotations.
Local Open Scope nat_scope.
Definition poly_context := list poly_ty.
Definition poly_context_wf d (Gamma : poly_context) := Forall (poly_ty_wf d) Gamma.
Definition poly_context_shift (Gamma : poly_context) := map (poly_ty_rename S) Gamma.
Fixpoint poly_parallel_effects (Es : list open_effect) : open_effect :=
  match Es with [] => EffLit [] | E :: Es => EffPar E (poly_parallel_effects Es) end.

Inductive poly_has_type : nat -> poly_context -> poly_expr -> poly_ty -> open_effect -> Prop :=
| PHTVar : forall d Gamma i T,
    nth_error Gamma i = Some T -> poly_ty_wf d T ->
    poly_has_type d Gamma (PEVar i) T (EffLit [])
| PHTUnit : forall d Gamma, poly_has_type d Gamma PEUnit PTUnit (EffLit [])
| PHTNat : forall d Gamma n, poly_has_type d Gamma (PENat n) PTNat (EffLit [])
| PHTTuple : forall d Gamma es Ts,
    Forall poly_value es ->
    poly_types d Gamma es Ts (repeat (EffLit []) (length es)) ->
    poly_has_type d Gamma (PETuple es) (PTProduct Ts) (EffLit [])
| PHTDownload : forall d Gamma s t,
    poly_has_type d Gamma (PEDownload s t) PTUnit (EffLit (download_effect s t))
| PHTRunning : forall d Gamma s t,
    poly_has_type d Gamma (PERunning s t) PTUnit (EffLit (download_effect s t))
| PHTLet : forall d Gamma e f A B E F,
    poly_has_type d Gamma e A E -> poly_has_type d (A :: Gamma) f B F ->
    poly_has_type d Gamma (PELet e f) B (EffJoin E F)
| PHTIfZero : forall d Gamma e f g T E F G,
    poly_has_type d Gamma e PTNat E -> poly_has_type d Gamma f T F ->
    poly_has_type d Gamma g T G ->
    poly_has_type d Gamma (PEIfZero e f g) T (EffJoin E (EffJoin F G))
| PHTParallel : forall d Gamma es Ts Es,
    poly_types d Gamma es Ts Es ->
    poly_has_type d Gamma (PEParallel es) (PTProduct Ts) (poly_parallel_effects Es)
| PHTAbs : forall d Gamma A e B E,
    poly_ty_wf d A -> poly_has_type d (A :: Gamma) e B E ->
    poly_has_type d Gamma (PELambda A e) (PTArrow A E B) (EffLit [])
| PHTApp : forall d Gamma e f A B E F G,
    poly_has_type d Gamma e (PTArrow A G B) E ->
    poly_has_type d Gamma f A F ->
    poly_has_type d Gamma (PEApp e f) B (EffJoin E (EffJoin F G))
| PHTAbsEff : forall d Gamma e T E,
    poly_context_wf d Gamma ->
    poly_has_type (S d) (poly_context_shift Gamma) e T E ->
    poly_has_type d Gamma (PEAbsEff e) (PTForall T E) (EffLit [])
| PHTAppEff : forall d Gamma e T E F G,
    poly_has_type d Gamma e (PTForall T G) E -> eff_scoped d F ->
    poly_has_type d Gamma (PEAppEff e F) (poly_ty_subst0 F T)
      (EffJoin E (eff_subst (eff_single F) G))
| PHTSub : forall d Gamma e T U E F,
    poly_has_type d Gamma e T E -> poly_subtype d T U -> eff_le d E F ->
    poly_ty_wf d U -> eff_scoped d F ->
    poly_has_type d Gamma e U F
with poly_types : nat -> poly_context -> list poly_expr -> list poly_ty -> list open_effect -> Prop :=
| PHTNil : forall d Gamma, poly_types d Gamma [] [] []
| PHTCons : forall d Gamma e es T Ts E Es,
    poly_has_type d Gamma e T E -> poly_types d Gamma es Ts Es ->
    poly_types d Gamma (e :: es) (T :: Ts) (E :: Es).

Scheme poly_has_type_mutind := Induction for poly_has_type Sort Prop
with poly_types_mutind := Induction for poly_types Sort Prop.
Combined Scheme poly_typing_mutind from poly_has_type_mutind, poly_types_mutind.

Lemma poly_effect_subst_value : forall v sigma,
  poly_value v -> poly_value (poly_effect_subst sigma v).
Proof.
  fix IH 3. intros v sigma Hv. destruct Hv; simpl; try constructor.
  induction H; simpl; constructor; auto.
Qed.
Lemma poly_effect_rename_value : forall v xi,
  poly_value v -> poly_value (poly_effect_rename xi v).
Proof.
  fix IH 3. intros v xi Hv. destruct Hv; simpl; try constructor.
  induction H; simpl; constructor; auto.
Qed.
Lemma poly_rename_value : forall v xi,
  poly_value v -> poly_value (poly_rename xi v).
Proof.
  fix IH 3. intros v xi Hv. destruct Hv; simpl; try constructor.
  induction H; simpl; constructor; auto.
Qed.
Lemma poly_subst_value : forall v sigma,
  poly_value v -> poly_value (poly_subst sigma v).
Proof.
  fix IH 3. intros v sigma Hv. destruct Hv; simpl; try constructor.
  induction H; simpl; constructor; auto.
Qed.
Lemma poly_parallel_subst : forall Es sigma,
  eff_subst sigma (poly_parallel_effects Es) =
  poly_parallel_effects (map (eff_subst sigma) Es).
Proof. induction Es; intros; simpl; f_equal; auto. Qed.
Lemma poly_context_subst_shift : forall Gamma sigma,
  map (poly_ty_subst (eff_up_subst sigma)) (poly_context_shift Gamma) =
  poly_context_shift (map (poly_ty_subst sigma) Gamma).
Proof.
  intros. unfold poly_context_shift. rewrite !map_map.
  apply map_ext. intro T. apply poly_ty_subst_shift.
Qed.

Lemma poly_typing_effect_subst_mut :
  (forall d Gamma e T E, poly_has_type d Gamma e T E ->
    forall d' sigma, (forall i, i < d -> eff_scoped d' (sigma i)) ->
    poly_has_type d' (map (poly_ty_subst sigma) Gamma)
      (poly_effect_subst sigma e) (poly_ty_subst sigma T) (eff_subst sigma E)) /\
  (forall d Gamma es Ts Es, poly_types d Gamma es Ts Es ->
    forall d' sigma, (forall i, i < d -> eff_scoped d' (sigma i)) ->
    poly_types d' (map (poly_ty_subst sigma) Gamma)
      (map (poly_effect_subst sigma) es) (map (poly_ty_subst sigma) Ts)
      (map (eff_subst sigma) Es)).
Proof.
  apply poly_typing_mutind.
  - intros d Gamma i T Hlookup Hwf d' sigma Hsigma. simpl. constructor.
    + rewrite nth_error_map, Hlookup. reflexivity.
    + eapply poly_ty_wf_subst; eauto.
  - intros; constructor.
  - intros; constructor.
  - intros d Gamma es Ts Hvalues Htypes IH d' sigma Hsigma. simpl.
    apply PHTTuple.
    + apply Forall_map. eapply Forall_impl; [|exact Hvalues].
      intros. apply poly_effect_subst_value; assumption.
    + specialize (IH d' sigma Hsigma). rewrite map_repeat in IH.
      rewrite length_map. exact IH.
  - intros; constructor.
  - intros; constructor.
  - intros d Gamma e f A B E F He IHe Hf IHf d' sigma Hsigma.
    simpl. eapply PHTLet; eauto.
  - intros d Gamma e f g T E F G He IHe Hf IHf Hg IHg d' sigma Hsigma.
    simpl. eapply PHTIfZero; eauto.
  - intros d Gamma es Ts Es Htypes IH d' sigma Hsigma.
    simpl. rewrite poly_parallel_subst. apply PHTParallel. auto.
  - intros d Gamma A e B E Hwf He IH d' sigma Hsigma. simpl.
    apply PHTAbs.
    + eapply poly_ty_wf_subst; eauto.
    + apply IH; auto.
  - intros d Gamma e f A B E F G He IHe Hf IHf d' sigma Hsigma.
    simpl. eapply PHTApp; eauto.
  - intros d Gamma e T E Hwf He IH d' sigma Hsigma. simpl.
    apply PHTAbsEff.
    + unfold poly_context_wf in *. apply Forall_map.
      eapply Forall_impl; [|exact Hwf]. intros.
      eapply poly_ty_wf_subst; eauto.
    + specialize (IH (S d') (eff_up_subst sigma)).
      rewrite poly_context_subst_shift in IH.
      apply IH. apply eff_up_scoped. exact Hsigma.
  - intros d Gamma e T E F G He IH HF d' sigma Hsigma. simpl.
    rewrite poly_ty_subst_instantiate, poly_effect_instantiate.
    eapply PHTAppEff.
    + exact (IH d' sigma Hsigma).
    + eapply eff_scoped_subst; eauto.
  - intros d Gamma e T U E F He IH Hsub Hle Hwf HF d' sigma Hsigma.
    eapply PHTSub.
    + apply IH; auto.
    + eapply poly_subtype_subst; eauto.
    + eapply eff_le_subst; eauto.
    + eapply poly_ty_wf_subst; eauto.
    + eapply eff_scoped_subst; eauto.
  - intros; constructor.
  - intros; simpl. constructor; eauto.
Qed.
Theorem poly_typing_effect_subst : forall d Gamma e T E d' sigma,
  poly_has_type d Gamma e T E ->
  (forall i, i < d -> eff_scoped d' (sigma i)) ->
  poly_has_type d' (map (poly_ty_subst sigma) Gamma)
    (poly_effect_subst sigma e) (poly_ty_subst sigma T) (eff_subst sigma E).
Proof. intros. eapply (proj1 poly_typing_effect_subst_mut); eauto. Qed.

Theorem poly_typing_effect_rename : forall d Gamma e T E d' xi,
  poly_has_type d Gamma e T E ->
  (forall i, i < d -> xi i < d') ->
  poly_has_type d' (map (poly_ty_rename xi) Gamma)
    (poly_effect_rename xi e) (poly_ty_rename xi T) (eff_rename xi E).
Proof.
  intros d Gamma e T E d' xi Htyping Hxi.
  pose proof (poly_typing_effect_subst d Gamma e T E d'
    (fun i => EffVar (xi i)) Htyping) as H.
  assert (forall i, i < d -> eff_scoped d' (EffVar (xi i))) as Hscope.
  { intros. constructor. auto. }
  specialize (H Hscope).
  rewrite poly_effect_subst_vars, poly_ty_subst_vars, poly_eff_subst_vars in H.
  replace (map (poly_ty_subst (fun i => EffVar (xi i))) Gamma)
    with (map (poly_ty_rename xi) Gamma) in H.
  - exact H.
  - apply map_ext. intro U. symmetry. apply poly_ty_subst_vars.
Qed.

Lemma poly_download_effect_wf : forall s t, effect_wf (download_effect s t).
Proof.
  intros. constructor; [|constructor]. unfold obligation_wf; simpl.
  unfold download_rate, Qdiv. apply Qmult_le_0_compat.
  - apply nonnegative_value_spec.
  - apply Qinv_le_0_compat, Qlt_le_weak, positive_value_spec.
Qed.
Lemma poly_parallel_scoped : forall d Es,
  Forall (eff_scoped d) Es -> eff_scoped d (poly_parallel_effects Es).
Proof. intros d Es H; induction H; simpl; constructor; auto. constructor. Qed.
Lemma poly_typing_wf_mut :
  (forall d Gamma e T E, poly_has_type d Gamma e T E ->
     poly_ty_wf d T /\ eff_scoped d E) /\
  (forall d Gamma es Ts Es, poly_types d Gamma es Ts Es ->
     Forall (poly_ty_wf d) Ts /\ Forall (eff_scoped d) Es).
Proof.
  apply poly_typing_mutind.
  - intros. split; auto. constructor. constructor.
  - intros. split; constructor. constructor.
  - intros. split; constructor. constructor.
  - intros d Gamma es Ts Hv Ht [HT HE]. split; constructor; auto. constructor.
  - intros. split; constructor. apply poly_download_effect_wf.
  - intros. split; constructor. apply poly_download_effect_wf.
  - intros d Gamma e f A B E F He [HA HE] Hf [HB HF]. split; auto. constructor; auto.
  - intros d Gamma e f g T E F G He [HA HE] Hf [HB HF] Hg [HC HG].
    split; auto. constructor; auto. constructor; auto.
  - intros d Gamma es Ts Es Ht [HT HE]. split; [constructor; auto|apply poly_parallel_scoped; auto].
  - intros d Gamma A e B E HA He [HB HE]. split; constructor; auto. constructor.
  - intros d Gamma e f A B E F G He [HT HE] Hf [HA HF].
    inversion HT; subst. split; auto. constructor; auto. constructor; auto.
  - intros d Gamma e T E HG He [HT HE]. split; constructor; auto. constructor.
  - intros d Gamma e T E F G He [HT HE] HF. inversion HT; subst.
    split.
    + eapply poly_ty_wf_subst0; eauto.
    + constructor; auto. apply eff_subst0_scoped; auto.
  - intros. split; auto.
  - intros. split; constructor.
  - intros d Gamma e es T Ts E Es He [HT HE] Hes [HTs HEs].
    split; constructor; auto.
Qed.
Theorem poly_typing_wf : forall d Gamma e T E,
  poly_has_type d Gamma e T E -> poly_ty_wf d T /\ eff_scoped d E.
Proof. exact (proj1 poly_typing_wf_mut). Qed.
Lemma poly_context_shift_wf : forall d Gamma,
  poly_context_wf d Gamma -> poly_context_wf (S d) (poly_context_shift Gamma).
Proof.
  intros d Gamma H. unfold poly_context_wf, poly_context_shift in *.
  apply Forall_map. eapply Forall_impl; [|exact H]. intros.
  eapply poly_ty_wf_rename; eauto. intros; lia.
Qed.
Definition poly_renaming_typed (Gamma Delta : poly_context) (xi : nat -> nat) :=
  forall i T, nth_error Gamma i = Some T -> nth_error Delta (xi i) = Some T.
Lemma poly_renaming_up : forall Gamma Delta xi T,
  poly_renaming_typed Gamma Delta xi ->
  poly_renaming_typed (T :: Gamma) (T :: Delta) (up_ren xi).
Proof.
  intros Gamma Delta xi T H [|i] U Hu; simpl in *.
  - exact Hu.
  - apply H; auto.
Qed.
Lemma poly_renaming_effect_shift : forall Gamma Delta xi,
  poly_renaming_typed Gamma Delta xi ->
  poly_renaming_typed (poly_context_shift Gamma) (poly_context_shift Delta) xi.
Proof.
  intros Gamma Delta xi H i T Hi. unfold poly_context_shift in *.
  rewrite nth_error_map in Hi. destruct (nth_error Gamma i) eqn:HGi;
    simpl in Hi; inversion Hi; subst.
  rewrite nth_error_map, (H _ _ HGi). reflexivity.
Qed.
Lemma poly_typing_rename_mut :
  (forall d Gamma e T E, poly_has_type d Gamma e T E ->
    forall Delta xi, poly_context_wf d Delta ->
    poly_renaming_typed Gamma Delta xi ->
    poly_has_type d Delta (poly_rename xi e) T E) /\
  (forall d Gamma es Ts Es, poly_types d Gamma es Ts Es ->
    forall Delta xi, poly_context_wf d Delta ->
    poly_renaming_typed Gamma Delta xi ->
    poly_types d Delta (map (poly_rename xi) es) Ts Es).
Proof.
  apply poly_typing_mutind.
  - intros. simpl. constructor; auto.
  - intros. constructor.
  - intros. constructor.
  - intros d Gamma es Ts Hv Ht IH Delta xi HD Hxi. simpl. apply PHTTuple.
    + apply Forall_map. eapply Forall_impl; [|exact Hv].
      intros. apply poly_rename_value; auto.
    + rewrite length_map. apply IH; auto.
  - intros; constructor.
  - intros; constructor.
  - intros d Gamma e f A B E F He IHe Hf IHf Delta xi HD Hxi. simpl.
    eapply PHTLet.
    + apply IHe; auto.
    + apply IHf; [|apply poly_renaming_up; auto].
      constructor; auto. apply (proj1 (poly_typing_wf _ _ _ _ _ He)).
  - intros. simpl. eapply PHTIfZero; eauto.
  - intros. simpl. apply PHTParallel; eauto.
  - intros d Gamma A e B E HA He IH Delta xi HD Hxi. simpl.
    apply PHTAbs; auto. apply IH; [constructor; auto|apply poly_renaming_up; auto].
  - intros. simpl. eapply PHTApp; eauto.
  - intros d Gamma e T E HG He IH Delta xi HD Hxi. simpl.
    apply PHTAbsEff; auto. apply IH.
    + apply poly_context_shift_wf; auto.
    + apply poly_renaming_effect_shift; auto.
  - intros. simpl. eapply PHTAppEff; eauto.
  - intros. eapply PHTSub; eauto.
  - intros. constructor.
  - intros. simpl. constructor; eauto.
Qed.
Theorem poly_typing_rename : forall d Gamma e T E Delta xi,
  poly_has_type d Gamma e T E -> poly_context_wf d Delta ->
  poly_renaming_typed Gamma Delta xi -> poly_has_type d Delta (poly_rename xi e) T E.
Proof. intros. eapply (proj1 poly_typing_rename_mut); eauto. Qed.

Definition poly_substitution_typed d (Gamma Delta : poly_context)
    (sigma : nat -> poly_expr) :=
  forall i T, nth_error Gamma i = Some T ->
    poly_has_type d Delta (sigma i) T (EffLit []).
Lemma poly_substitution_up : forall d Gamma Delta sigma T,
  poly_context_wf d Delta -> poly_ty_wf d T ->
  poly_substitution_typed d Gamma Delta sigma ->
  poly_substitution_typed d (T :: Gamma) (T :: Delta) (poly_up_subst sigma).
Proof.
  intros d Gamma Delta sigma T HD HT Hsigma [|i] U Hu; simpl in *.
  - inversion Hu; subst. constructor; auto.
  - unfold poly_up_subst. eapply poly_typing_rename.
    + apply Hsigma; auto.
    + constructor; auto.
    + intros j V Hj. exact Hj.
Qed.
Lemma poly_substitution_effect_shift : forall d Gamma Delta sigma,
  poly_substitution_typed d Gamma Delta sigma ->
  poly_substitution_typed (S d) (poly_context_shift Gamma)
    (poly_context_shift Delta) (fun i => poly_effect_rename S (sigma i)).
Proof.
  intros d Gamma Delta sigma H i T Hi. unfold poly_context_shift in *.
  rewrite nth_error_map in Hi. destruct (nth_error Gamma i) eqn:HGi;
    simpl in Hi; inversion Hi; subst.
  change (poly_has_type (S d) (map (poly_ty_rename S) Delta)
    (poly_effect_rename S (sigma i)) (poly_ty_rename S p) (eff_rename S (EffLit []))).
  eapply poly_typing_effect_rename; eauto. intros; lia.
Qed.
Lemma poly_typing_subst_mut :
  (forall d Gamma e T E, poly_has_type d Gamma e T E ->
    forall Delta sigma, poly_context_wf d Delta ->
    poly_substitution_typed d Gamma Delta sigma ->
    poly_has_type d Delta (poly_subst sigma e) T E) /\
  (forall d Gamma es Ts Es, poly_types d Gamma es Ts Es ->
    forall Delta sigma, poly_context_wf d Delta ->
    poly_substitution_typed d Gamma Delta sigma ->
    poly_types d Delta (map (poly_subst sigma) es) Ts Es).
Proof.
  apply poly_typing_mutind.
  - intros; simpl; auto.
  - intros; constructor.
  - intros; constructor.
  - intros d Gamma es Ts Hv Ht IH Delta sigma HD Hsigma. simpl. apply PHTTuple.
    + apply Forall_map. eapply Forall_impl; [|exact Hv].
      intros. apply poly_subst_value; auto.
    + rewrite length_map. apply IH; auto.
  - intros; constructor.
  - intros; constructor.
  - intros d Gamma e f A B E F He IHe Hf IHf Delta sigma HD Hsigma. simpl.
    assert (poly_ty_wf d A) as HA by (apply (proj1 (poly_typing_wf _ _ _ _ _ He))).
    eapply PHTLet.
    + apply IHe; auto.
    + apply IHf; [constructor; auto|apply poly_substitution_up; auto].
  - intros. simpl. eapply PHTIfZero; eauto.
  - intros. simpl. apply PHTParallel; eauto.
  - intros d Gamma A e B E HA He IH Delta sigma HD Hsigma. simpl.
    apply PHTAbs; auto. apply IH; [constructor; auto|apply poly_substitution_up; auto].
  - intros. simpl. eapply PHTApp; eauto.
  - intros d Gamma e T E HG He IH Delta sigma HD Hsigma. simpl.
    apply PHTAbsEff; auto. apply IH.
    + apply poly_context_shift_wf; auto.
    + apply poly_substitution_effect_shift; auto.
  - intros. simpl. eapply PHTAppEff; eauto.
  - intros. eapply PHTSub; eauto.
  - intros. constructor.
  - intros. simpl. constructor; eauto.
Qed.
Theorem poly_typing_subst : forall d Gamma e T E Delta sigma,
  poly_has_type d Gamma e T E -> poly_context_wf d Delta ->
  poly_substitution_typed d Gamma Delta sigma ->
  poly_has_type d Delta (poly_subst sigma e) T E.
Proof. intros. eapply (proj1 poly_typing_subst_mut); eauto. Qed.
Theorem poly_typing_subst0 : forall d Gamma v body A T E,
  poly_context_wf d Gamma ->
  poly_has_type d Gamma v A (EffLit []) ->
  poly_has_type d (A :: Gamma) body T E ->
  poly_has_type d Gamma (poly_subst0 v body) T E.
Proof.
  intros d Gamma v body A T E HG Hv Hb. eapply poly_typing_subst; eauto.
  intros [|i] U Hu; simpl in *.
  - inversion Hu; subst. exact Hv.
  - constructor; auto. unfold poly_context_wf in HG.
    apply Forall_forall with (x := U) in HG; auto.
    eapply nth_error_In; eauto.
Qed.
Lemma poly_context_instantiate_shift : forall Gamma F,
  map (poly_ty_subst (eff_single F)) (poly_context_shift Gamma) = Gamma.
Proof.
  intros. unfold poly_context_shift. rewrite map_map.
  induction Gamma; simpl; f_equal; auto.
  rewrite poly_ty_subst_rename. apply poly_ty_subst_id.
Qed.
Theorem poly_typing_effect_subst0 : forall d Gamma body T E F,
  poly_has_type (S d) (poly_context_shift Gamma) body T E ->
  eff_scoped d F ->
  poly_has_type d Gamma (poly_effect_subst0 F body)
    (poly_ty_subst0 F T) (eff_subst (eff_single F) E).
Proof.
  intros d Gamma body T E F Hb HF.
  pose proof (poly_typing_effect_subst (S d) (poly_context_shift Gamma)
    body T E d (eff_single F) Hb) as H.
  rewrite poly_context_instantiate_shift in H. apply H.
  intros [|i] Hi; simpl; auto. constructor; lia.
Qed.
