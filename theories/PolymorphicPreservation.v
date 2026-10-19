(** Generation, preservation, and active-effect coverage for the
    polymorphic calculus. All effect comparisons quantify over closing
    substitutions, including locally bound effect variables. *)
From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Syntax Typing
  Semantics ActiveWF ActiveEffects PolymorphicEffects PolymorphicSyntax
  PolymorphicTypeSubstitution PolymorphicTyping PolymorphicSemantics
  PolymorphicActiveWF.
Import ListNotations.

Inductive poly_root_type : nat -> poly_context -> poly_expr -> poly_ty -> open_effect -> Prop :=
| PRootVar : forall d Gamma i T,
    nth_error Gamma i = Some T -> poly_ty_wf d T ->
    poly_root_type d Gamma (PEVar i) T (EffLit [])
| PRootUnit : forall d Gamma, poly_root_type d Gamma PEUnit PTUnit (EffLit [])
| PRootNat : forall d Gamma n, poly_root_type d Gamma (PENat n) PTNat (EffLit [])
| PRootTuple : forall d Gamma es Ts,
    Forall poly_value es ->
    poly_types d Gamma es Ts (repeat (EffLit []) (length es)) ->
    poly_root_type d Gamma (PETuple es) (PTProduct Ts) (EffLit [])
| PRootDownload : forall d Gamma s t,
    poly_root_type d Gamma (PEDownload s t) PTUnit (EffLit (download_effect s t))
| PRootRunning : forall d Gamma s t,
    poly_root_type d Gamma (PERunning s t) PTUnit (EffLit (download_effect s t))
| PRootLet : forall d Gamma e f A B E F,
    poly_has_type d Gamma e A E -> poly_has_type d (A :: Gamma) f B F ->
    poly_root_type d Gamma (PELet e f) B (EffJoin E F)
| PRootIfZero : forall d Gamma e f g T E F G,
    poly_has_type d Gamma e PTNat E -> poly_has_type d Gamma f T F ->
    poly_has_type d Gamma g T G ->
    poly_root_type d Gamma (PEIfZero e f g) T (EffJoin E (EffJoin F G))
| PRootParallel : forall d Gamma es Ts Es,
    poly_types d Gamma es Ts Es ->
    poly_root_type d Gamma (PEParallel es) (PTProduct Ts) (poly_parallel_effects Es)
| PRootAbs : forall d Gamma A e B E,
    poly_ty_wf d A -> poly_has_type d (A :: Gamma) e B E ->
    poly_root_type d Gamma (PELambda A e) (PTArrow A E B) (EffLit [])
| PRootApp : forall d Gamma e f A B E F G,
    poly_has_type d Gamma e (PTArrow A G B) E ->
    poly_has_type d Gamma f A F ->
    poly_root_type d Gamma (PEApp e f) B (EffJoin E (EffJoin F G))
| PRootAbsEff : forall d Gamma e T E,
    poly_context_wf d Gamma ->
    poly_has_type (S d) (poly_context_shift Gamma) e T E ->
    poly_root_type d Gamma (PEAbsEff e) (PTForall T E) (EffLit [])
| PRootAppEff : forall d Gamma e T E F G,
    poly_has_type d Gamma e (PTForall T G) E -> eff_scoped d F ->
    poly_root_type d Gamma (PEAppEff e F) (poly_ty_subst0 F T)
      (EffJoin E (eff_subst (eff_single F) G)).

Lemma poly_root_is_typing : forall d Gamma e T E,
  poly_root_type d Gamma e T E -> poly_has_type d Gamma e T E.
Proof. intros d Gamma e T E H; destruct H; econstructor; eauto. Qed.

Lemma poly_typing_generation : forall d Gamma e T E,
  poly_has_type d Gamma e T E -> exists T0 E0,
    poly_root_type d Gamma e T0 E0 /\
    poly_subtype d T0 T /\ eff_le d E0 E.
Proof.
  intros d Gamma e T E H. induction H.
  all: try (eexists; eexists; split;
    [econstructor; eauto | split; [apply poly_subtype_refl | apply eff_le_refl]]).
  destruct IHpoly_has_type as (T0 & E0 & Hr & Ht & He).
  exists T0, E0. split; [exact Hr | split].
  - eapply poly_subtype_trans; eauto.
  - eapply eff_le_trans; eauto.
Qed.

Lemma poly_value_typing_pure : forall d Gamma v T E,
  poly_value v -> poly_has_type d Gamma v T E ->
  poly_has_type d Gamma v T (EffLit []).
Proof.
  intros d Gamma v T E Hv Ht. induction Ht;
    try solve [inversion Hv; subst; econstructor; eauto].
  eapply PHTSub.
  - apply IHHt. exact Hv.
  - exact H.
  - apply eff_le_refl.
  - exact H1.
  - constructor. constructor.
Qed.

Lemma poly_let_generation : forall d Gamma bound body T E,
  poly_has_type d Gamma (PELet bound body) T E ->
  exists A U E1 E2,
    poly_has_type d Gamma bound A E1 /\
    poly_has_type d (A :: Gamma) body U E2 /\
    poly_subtype d U T /\ eff_le d (EffJoin E1 E2) E.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_app_generation : forall d Gamma f a T E,
  poly_has_type d Gamma (PEApp f a) T E ->
  exists A U G E1 E2,
    poly_has_type d Gamma f (PTArrow A G U) E1 /\
    poly_has_type d Gamma a A E2 /\
    poly_subtype d U T /\ eff_le d (EffJoin E1 (EffJoin E2 G)) E.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_abs_generation : forall d Gamma A body T E,
  poly_has_type d Gamma (PELambda A body) T E ->
  exists U G,
    poly_has_type d (A :: Gamma) body U G /\
    poly_subtype d (PTArrow A G U) T.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_if_generation : forall d Gamma guard e1 e2 T E,
  poly_has_type d Gamma (PEIfZero guard e1 e2) T E ->
  exists U E0 E1 E2,
    poly_has_type d Gamma guard PTNat E0 /\
    poly_has_type d Gamma e1 U E1 /\
    poly_has_type d Gamma e2 U E2 /\
    poly_subtype d U T /\ eff_le d (EffJoin E0 (EffJoin E1 E2)) E.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_parallel_generation : forall d Gamma es T E,
  poly_has_type d Gamma (PEParallel es) T E ->
  exists Ts Es, poly_types d Gamma es Ts Es /\
    poly_subtype d (PTProduct Ts) T /\
    eff_le d (poly_parallel_effects Es) E.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_download_generation : forall d Gamma s t T E,
  poly_has_type d Gamma (PEDownload s t) T E ->
  poly_subtype d PTUnit T /\ eff_le d (EffLit (download_effect s t)) E.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_running_generation : forall d Gamma s t T E,
  poly_has_type d Gamma (PERunning s t) T E ->
  poly_subtype d PTUnit T /\ eff_le d (EffLit (download_effect s t)) E.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_abs_eff_generation : forall d Gamma body T E,
  poly_has_type d Gamma (PEAbsEff body) T E ->
  exists U G, poly_context_wf d Gamma /\
    poly_has_type (S d) (poly_context_shift Gamma) body U G /\
    poly_subtype d (PTForall U G) T.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

Lemma poly_app_eff_generation : forall d Gamma e F T E,
  poly_has_type d Gamma (PEAppEff e F) T E ->
  exists U G E0, poly_has_type d Gamma e (PTForall U G) E0 /\
    eff_scoped d F /\ poly_subtype d (poly_ty_subst0 F U) T /\
    eff_le d (EffJoin E0 (eff_subst (eff_single F) G)) E.
Proof.
  intros. match goal with H : poly_has_type _ _ _ _ _ |- _ =>
    destruct (poly_typing_generation _ _ _ _ _ H) as (U0 & G0 & Hr & Hsub & Hle)
  end. inversion Hr; subst; eauto 18.
Qed.

(** Coverage follows evaluation-active positions, so dormant effect
    abstractions contribute no running obligations. *)
Lemma poly_active_coverage_mut :
  (forall d Gamma e T E, poly_has_type d Gamma e T E ->
    forall eta, eff_environment d eta ->
    poly_active_effect (poly_running_rates e) ≼ eff_eval eta E) /\
  (forall d Gamma es Ts Es, poly_types d Gamma es Ts Es ->
    forall eta, eff_environment d eta ->
    poly_active_effect (concat (map poly_running_rates es)) ≼
    eff_eval eta (poly_parallel_effects Es)).
Proof.
  apply poly_typing_mutind.
  - intros; simpl; apply empty_effect_le.
  - intros; simpl; apply empty_effect_le.
  - intros; simpl; apply empty_effect_le.
  - intros; simpl; apply empty_effect_le.
  - intros; simpl; apply empty_effect_le.
  - intros; simpl; apply effect_le_refl.
  - intros d Gamma e f A B E F He IHe Hf IHf eta Heta. simpl.
    eapply effect_le_trans; [apply IHe; exact Heta |].
    unfold sequential_effect. eapply effect_le_trans;
      [apply effect_le_join_l | apply le_normalize].
  - intros d Gamma e f g T E F G He IHe Hf IHf Hg IHg eta Heta. simpl.
    eapply effect_le_trans; [apply IHe; exact Heta |].
    unfold sequential_effect. eapply effect_le_trans;
      [apply effect_le_join_l | apply le_normalize].
  - intros; simpl; auto.
  - intros; simpl; apply empty_effect_le.
  - intros d Gamma e f A B E F G He IHe Hf IHf eta Heta. simpl.
    destruct (poly_value_dec e).
    + eapply effect_le_trans; [apply IHf; exact Heta |].
      eapply effect_le_trans.
      * unfold sequential_effect. eapply effect_le_trans;
          [apply effect_le_join_l | apply le_normalize].
      * unfold sequential_effect. eapply effect_le_trans;
          [apply effect_le_join_r | apply le_normalize].
    + eapply effect_le_trans; [apply IHe; exact Heta |].
      unfold sequential_effect. eapply effect_le_trans;
        [apply effect_le_join_l | apply le_normalize].
  - intros; simpl; apply empty_effect_le.
  - intros d Gamma e T E F G He IHe HF eta Heta. simpl.
    eapply effect_le_trans; [apply IHe; exact Heta |].
    unfold sequential_effect. eapply effect_le_trans;
      [apply effect_le_join_l | apply le_normalize].
  - intros d Gamma e T U E F He IHe Hsub Hle HU HF eta Heta.
    eapply effect_le_trans; [apply IHe; exact Heta | apply Hle; exact Heta].
  - intros; simpl; apply effect_le_refl.
  - intros d Gamma e es T Ts E Es He IHe Hes IHes eta Heta. simpl.
    eapply effect_le_trans.
    + apply active_effect_union.
    + apply parallel_effect_mono; auto.
Qed.

Theorem poly_active_coverage : forall d Gamma e T E eta,
  poly_has_type d Gamma e T E -> eff_environment d eta ->
  poly_active_effect (poly_running_rates e) ≼ eff_eval eta E.
Proof. intros; eapply (proj1 poly_active_coverage_mut); eauto. Qed.
(** Split aligned list typing around a distinguished middle expression. *)
Lemma poly_types_split :
  forall d Gamma prefix branch suffix types effects,
    poly_types
      d Gamma (prefix ++ branch :: suffix) types effects ->
    exists prefix_types branch_type suffix_types
           prefix_effects branch_effect suffix_effects,
      types = prefix_types ++ branch_type :: suffix_types /\
      effects = prefix_effects ++ branch_effect :: suffix_effects /\
      poly_types d Gamma prefix prefix_types prefix_effects /\
      poly_has_type d Gamma branch branch_type branch_effect /\
      poly_types d Gamma suffix suffix_types suffix_effects.
Proof.
  intros d Gamma prefix. induction prefix as [|head prefix IH];
    intros branch suffix types effects Htypes; simpl in Htypes.
  - inversion Htypes as
      [|d' Gamma' e expressions T0 types0 Phi0 effects0 Hbranch Hsuffix];
      subst.
    exists [], T0, types0, [], Phi0, effects0.
    repeat split; try reflexivity.
    + constructor.
    + exact Hbranch.
    + exact Hsuffix.
  - inversion Htypes as
      [|d' Gamma' e expressions T0 types0 Phi0 effects0 Hhead Htail];
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
Lemma poly_types_middle :
  forall d Gamma prefix branch suffix prefix_types branch_type suffix_types
         prefix_effects branch_effect suffix_effects,
    poly_types d Gamma prefix prefix_types prefix_effects ->
    poly_has_type d Gamma branch branch_type branch_effect ->
    poly_types d Gamma suffix suffix_types suffix_effects ->
    poly_types d Gamma
      (prefix ++ branch :: suffix)
      (prefix_types ++ branch_type :: suffix_types)
      (prefix_effects ++ branch_effect :: suffix_effects).
Proof.
  intros d Gamma prefix branch suffix prefix_types branch_type suffix_types
    prefix_effects branch_effect suffix_effects Hprefix Hbranch Hsuffix.
  induction Hprefix; simpl.
  - constructor; assumption.
  - constructor.
    + assumption.
    + exact (IHHprefix Hbranch Hsuffix).
Qed.


Lemma poly_typed_values_pure : forall d Gamma es Ts Es,
  poly_types d Gamma es Ts Es -> Forall poly_value es ->
  poly_types d Gamma es Ts (repeat (EffLit []) (length es)).
Proof.
  intros d Gamma es Ts Es H; induction H; intros Hv; inversion Hv; subst; simpl.
  - constructor.
  - constructor; [eapply poly_value_typing_pure; eauto | auto].
Qed.

Lemma poly_typing_widen : forall d Gamma e T U E F,
  poly_has_type d Gamma e T E -> poly_subtype d T U -> eff_le d E F ->
  poly_ty_wf d U -> eff_scoped d F -> poly_has_type d Gamma e U F.
Proof. intros; eapply PHTSub; eauto. Qed.

Lemma poly_effect_single_scoped : forall d F,
  eff_scoped d F -> forall i, (i < S d)%nat -> eff_scoped d (eff_single F i).
Proof. intros d F HF [|i] Hi; simpl; [exact HF | constructor; lia]. Qed.

Definition poly_preservation_transition source target : Prop :=
  match source, target with
  | PolyConfig e _, PolyConfig e' _ =>
      forall d Gamma T E, poly_context_wf d Gamma ->
      poly_has_type d Gamma e T E -> poly_has_type d Gamma e' T E
  | _, _ => True
  end.

Lemma poly_lambda_annotation_wf : forall d Gamma A body T E,
  poly_has_type d Gamma (PELambda A body) T E -> poly_ty_wf d A.
Proof.
  intros. destruct (poly_typing_generation _ _ _ _ _ H) as (U & F & Hr & _).
  inversion Hr; subst; assumption.
Qed.

(** Declarative subsumption lets each reduct retain the original upper
    bound. The decreasing-effect statement below follows from reflexivity. *)
Theorem poly_preservation_general : forall B source target,
  poly_step B source target -> poly_preservation_transition source target.
Proof.
  intros B source target Hstep. induction Hstep; simpl.
  all: try (intros d Gamma T E HG Htyping;
    destruct (poly_typing_wf _ _ _ _ _ Htyping) as [HT HE]).
  - destruct (poly_let_generation _ _ _ _ _ _ Htyping)
      as (A & U & E1 & E2 & Hbound & Hbody & Hsub & Hle).
    eapply poly_typing_widen; [|exact Hsub| |exact HT|exact HE].
    + eapply poly_typing_subst0; eauto using poly_value_typing_pure.
    + eapply eff_le_trans; [apply eff_le_join_r | exact Hle].
  - destruct (poly_app_generation _ _ _ _ _ _ Htyping)
      as (A & U & G & E1 & E2 & Hfun & Harg & Hresult & Hle).
    destruct (poly_abs_generation _ _ _ _ _ _ Hfun)
      as (U0 & G0 & Hbody & Harrow).
    destruct (poly_subtype_arrow_inv _ _ _ _ _ _ _ Harrow)
      as (Hdomain & Hlatent & Hcodomain).
    assert (HA : poly_ty_wf d parameter_ty).
    { eapply poly_lambda_annotation_wf; eauto. }
    assert (Ha : poly_has_type d Gamma argument parameter_ty (EffLit [])).
    { eapply PHTSub; [eapply poly_value_typing_pure; eauto |exact Hdomain|
        apply eff_le_refl|exact HA|constructor; constructor]. }
    eapply poly_typing_widen.
    + eapply poly_typing_subst0; eauto.
    + eapply poly_subtype_trans; eauto.
    + eapply eff_le_trans; [exact Hlatent |].
      eapply eff_le_trans; [apply eff_le_join_r |].
      eapply eff_le_trans; [apply eff_le_join_r | exact Hle].
    + exact HT.
    + exact HE.
  - destruct (poly_if_generation _ _ _ _ _ _ _ Htyping)
      as (U & E0 & E1 & E2 & Hguard & Hzero & Hnonzero & Hsub & Hle).
    eapply poly_typing_widen; [exact Hzero|exact Hsub| |exact HT|exact HE].
    eapply eff_le_trans; [apply eff_le_join_l |].
    eapply eff_le_trans; [apply eff_le_join_r | exact Hle].
  - destruct (poly_if_generation _ _ _ _ _ _ _ Htyping)
      as (U & E0 & E1 & E2 & Hguard & Hzero & Hnonzero & Hsub & Hle).
    eapply poly_typing_widen; [exact Hnonzero|exact Hsub| |exact HT|exact HE].
    eapply eff_le_trans; [apply eff_le_join_r |].
    eapply eff_le_trans; [apply eff_le_join_r | exact Hle].
  - destruct (poly_parallel_generation _ _ _ _ _ Htyping)
      as (Ts & Es & Hbranches & Hsub & Hle).
    eapply poly_typing_widen; [|exact Hsub|apply eff_le_empty|exact HT|exact HE].
    apply PHTTuple; [exact H|]. eapply poly_typed_values_pure; eauto.
  - destruct (poly_download_generation _ _ _ _ _ _ Htyping) as [Hsub Hle].
    eapply poly_typing_widen; [constructor|exact Hsub|exact Hle|exact HT|exact HE].
  - destruct (poly_running_generation _ _ _ _ _ _ Htyping) as [Hsub Hle].
    eapply poly_typing_widen; [constructor|exact Hsub|apply eff_le_empty|exact HT|exact HE].
  - exact I.
  - destruct (poly_let_generation _ _ _ _ _ _ Htyping)
      as (A & U & E1 & E2 & Hbound & Hbody & Hsub & Hle).
    eapply poly_typing_widen; [|exact Hsub|exact Hle|exact HT|exact HE].
    eapply PHTLet; [eapply IHHstep; eauto|exact Hbody].
  - destruct (poly_app_generation _ _ _ _ _ _ Htyping)
      as (A & U & G & E1 & E2 & Hfun & Harg & Hsub & Hle).
    eapply poly_typing_widen; [|exact Hsub|exact Hle|exact HT|exact HE].
    eapply PHTApp; [eapply IHHstep; eauto|exact Harg].
  - destruct (poly_app_generation _ _ _ _ _ _ Htyping)
      as (A & U & G & E1 & E2 & Hfun & Harg & Hsub & Hle).
    eapply poly_typing_widen; [|exact Hsub|exact Hle|exact HT|exact HE].
    eapply PHTApp; [exact Hfun|eapply IHHstep; eauto].
  - destruct (poly_if_generation _ _ _ _ _ _ _ Htyping)
      as (U & E0 & E1 & E2 & Hguard & Hzero & Hnonzero & Hsub & Hle).
    eapply poly_typing_widen; [|exact Hsub|exact Hle|exact HT|exact HE].
    eapply PHTIfZero; [eapply IHHstep; eauto|exact Hzero|exact Hnonzero].
  - destruct (poly_parallel_generation _ _ _ _ _ Htyping)
      as (Ts & Es & Hbranches & Hsub & Hle).
    destruct (poly_types_split _ _ _ _ _ _ _ Hbranches)
      as (preT & branchT & postT & preE & branchE & postE &
        HTs & HEs & Hpre & Hbranch & Hpost).
    subst Ts Es.
    eapply poly_typing_widen; [|exact Hsub|exact Hle|exact HT|exact HE].
    apply PHTParallel. eapply poly_types_middle; eauto.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - exact I.
  - destruct (poly_app_eff_generation _ _ _ _ _ _ Htyping)
      as (U & G & E0 & Hfun & HF & Hresult & Hle).
    destruct (poly_abs_eff_generation _ _ _ _ _ Hfun)
      as (U0 & G0 & Hcontext & Hbody & Hall).
    destruct (poly_subtype_forall_inv _ _ _ _ _ Hall) as [Hbodytype Hbodyeffect].
    eapply poly_typing_widen.
    + eapply poly_typing_effect_subst0; eauto.
    + eapply poly_subtype_trans; [|exact Hresult].
      eapply poly_subtype_subst; [exact Hbodytype|].
      apply poly_effect_single_scoped. exact HF.
    + eapply eff_le_trans.
      * eapply eff_le_subst; [exact Hbodyeffect|].
        apply poly_effect_single_scoped. exact HF.
      * eapply eff_le_trans; [apply eff_le_join_r|exact Hle].
    + exact HT.
    + exact HE.
  - destruct (poly_app_eff_generation _ _ _ _ _ _ Htyping)
      as (U & G & E0 & Hfun & HF & Hresult & Hle).
    eapply poly_typing_widen; [|exact Hresult|exact Hle|exact HT|exact HE].
    eapply PHTAppEff; [eapply IHHstep; eauto|exact HF].
  - exact I.
Qed.

Theorem poly_preservation : forall B e n e' n' d Gamma T E,
  poly_step B (PolyConfig e n) (PolyConfig e' n') ->
  poly_context_wf d Gamma -> poly_has_type d Gamma e T E ->
  poly_has_type d Gamma e' T E.
Proof. intros; eapply (poly_preservation_general _ _ _ H); eauto. Qed.

Corollary poly_preservation_decreasing_effects : forall B e n e' n' d Gamma T E,
  poly_step B (PolyConfig e n) (PolyConfig e' n') ->
  poly_context_wf d Gamma -> poly_has_type d Gamma e T E ->
  exists F, poly_has_type d Gamma e' T F /\ eff_le d F E.
Proof. intros; exists E; split; [eapply poly_preservation; eauto|apply eff_le_refl]. Qed.

Theorem poly_preservation_steps : forall B source n target n' d Gamma T E,
  poly_successful_steps B source n target n' ->
  poly_context_wf d Gamma -> poly_has_type d Gamma source T E ->
  poly_has_type d Gamma target T E.
Proof. intros B source n target n' d Gamma T E H; induction H; eauto using poly_preservation. Qed.

(** Typing checks both namespaces, including effect variables in annotations
    and explicit effect arguments. *)
Lemma poly_typing_scoped_mut :
  (forall d Gamma e T E, poly_has_type d Gamma e T E ->
    poly_scoped d (length Gamma) e) /\
  (forall d Gamma es Ts Es, poly_types d Gamma es Ts Es ->
    Forall (poly_scoped d (length Gamma)) es).
Proof.
  apply poly_typing_mutind; intros; try solve [econstructor; eauto].
  - constructor. apply (proj1 (nth_error_Some Gamma i)). rewrite e. discriminate.
  - constructor. match goal with Hs : poly_scoped _ (length (poly_context_shift _)) _ |- _ =>
      unfold poly_context_shift in Hs; rewrite length_map in Hs; exact Hs end.
  - assumption.
Qed.

Theorem poly_typing_scoped : forall d Gamma e T E,
  poly_has_type d Gamma e T E -> poly_scoped d (length Gamma) e.
Proof. exact (proj1 poly_typing_scoped_mut). Qed.

Corollary poly_typed_source_closed : forall e T E,
  poly_source e -> poly_has_type 0 [] e T E -> poly_closed_source e.
Proof. intros e T E Hs Ht; split; [exact Hs|exact (poly_typing_scoped 0 [] e T E Ht)]. Qed.
