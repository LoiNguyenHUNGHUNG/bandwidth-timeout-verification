(** The manuscript's size-free expected-contract invariant.
    This is proved from the restricted source-generation rules, rather than
    assumed as an extra premise about their output constraints. *)
From Stdlib Require Import Arith Bool Lia List.
From BandwidthTimeout Require Import PolymorphicEffects PolymorphicSyntax
  PolymorphicSymbolic PolymorphicConstraints PolymorphicInferenceTypes
  PolymorphicInference.
Import ListNotations.

Fixpoint pst_sizefree (T : pst_type) : Prop :=
  match T with
  | PSTyUnit | PSTyNat => True
  | PSTyArrow A E B => pst_sizefree A /\ ps_size_free E = true /\ pst_sizefree B
  | PSTyProduct Ts =>
      let fix go Ts := match Ts with [] => True | T::Ts => pst_sizefree T /\ go Ts end
      in go Ts
  | PSTyForall T E => pst_sizefree T /\ ps_size_free E = true
  end.

Fixpoint pst_inputfree (T : pst_type) : Prop :=
  match T with
  | PSTyUnit | PSTyNat => True
  | PSTyArrow A _ B => pst_sizefree A /\ pst_inputfree B
  | PSTyProduct Ts =>
      let fix go Ts := match Ts with [] => True | T::Ts => pst_inputfree T /\ go Ts end
      in go Ts
  | PSTyForall T _ => pst_inputfree T
  end.

Fixpoint ps_rhs_free (C : local_constraint) : Prop :=
  match C with
  | LNumeric _ => True
  | LAnd C D => ps_rhs_free C /\ ps_rhs_free D
  | LGuard _ _ F => ps_size_free F = true
  end.

Lemma ps_embed_sizefree : forall E, ps_size_free (ps_embed E) = true.
Proof. induction E; simpl; auto; rewrite IHE1, IHE2; reflexivity. Qed.

Lemma ps_subst_sizefree : forall E s,
  ps_size_free E = true -> ps_size_free (ps_subst s E) = true.
Proof.
  induction E; intros s H; simpl in *; auto using ps_embed_sizefree;
    try discriminate; apply andb_true_iff in H as [H1 H2];
    rewrite IHE1, IHE2; auto.
Qed.

Lemma ps_norm_join_sizefree : forall E F,
  ps_size_free E = true -> ps_size_free F = true ->
  ps_size_free (ps_norm_join E F) = true.
Proof.
  intros E F HE HF. destruct E; destruct F; simpl in *; try discriminate;
    try destruct Phi; try destruct Phi0; simpl in *; auto.
  all: try (apply andb_true_iff; auto).
Qed.

Lemma ps_norm_par_sizefree : forall E F,
  ps_size_free E = true -> ps_size_free F = true ->
  ps_size_free (ps_norm_par E F) = true.
Proof.
  intros E F HE HF. destruct E; destruct F; simpl in *; try discriminate;
    try destruct Phi; try destruct Phi0; simpl in *; auto.
  all: apply andb_true_iff; auto.
Qed.

Lemma ps_norm_sizefree : forall E,
  ps_size_free E = true -> ps_size_free (ps_norm E) = true.
Proof.
  induction E; intro H; simpl in *; auto; apply andb_true_iff in H as [H1 H2].
  - apply ps_norm_join_sizefree; auto.
  - apply ps_par_regroup_sizefree; auto.
Qed.

Lemma ps_rhs_free_norm : forall C,
  ps_rhs_free C -> ps_rhs_free (ps_constraint_norm C).
Proof. induction C; simpl; intros; auto using ps_norm_sizefree; tauto. Qed.

Lemma pst_sizefree_inputfree : forall T, pst_sizefree T -> pst_inputfree T.
Proof.
  fix IH 1. intro T. destruct T; simpl; auto.
  - intros [HA [HE HB]]; split; auto.
  - induction l; simpl; auto. intros [H1 H2]. split; [apply IH; exact H1 | apply IHl; exact H2].
  - intros [HT HE]. auto.
Qed.

Lemma pst_embed_sizefree : forall T, pst_sizefree (pst_embed T).
Proof.
  fix IH 1. intro T. destruct T; simpl; auto.
  - repeat split; auto using ps_embed_sizefree.
  - induction l; simpl; auto.
  - split; auto using ps_embed_sizefree.
Qed.

Lemma pst_norm_sizefree : forall T, pst_sizefree T -> pst_sizefree (pst_norm T).
Proof.
  fix IH 1. intro T. destruct T; simpl; auto.
  - intros [HA [HE HB]]; repeat split; auto using ps_norm_sizefree.
  - induction l; simpl; auto. intros [H1 H2]. split; [apply IH; exact H1 | apply IHl; exact H2].
  - intros [HT HE]; split; auto using ps_norm_sizefree.
Qed.

Lemma pst_norm_inputfree : forall T, pst_inputfree T -> pst_inputfree (pst_norm T).
Proof.
  fix IH 1. intro T. destruct T; simpl; auto.
  - intros [HA HB]; split; auto using pst_norm_sizefree.
  - induction l; simpl; auto. intros [H1 H2]. split; [apply IH; exact H1 | apply IHl; exact H2].
Qed.

Lemma pst_subst_sizefree : forall T s,
  pst_sizefree T -> pst_sizefree (pst_subst s T).
Proof.
  fix IH 1. intros T s. destruct T; simpl; auto.
  - intros [HA [HE HB]]; repeat split; auto using ps_subst_sizefree.
  - induction l; simpl; auto. intros [H1 H2]. split; [apply IH; exact H1 | apply IHl; exact H2].
  - intros [HT HE]; split; auto using ps_subst_sizefree.
Qed.

Lemma pst_subst_inputfree : forall T s,
  pst_inputfree T -> pst_inputfree (pst_subst s T).
Proof.
  fix IH 1. intros T s. destruct T; simpl; auto.
  - intros [HA HB]; split; auto using pst_subst_sizefree.
  - induction l; simpl; auto. intros [H1 H2]. split; [apply IH; exact H1 | apply IHl; exact H2].
Qed.

Lemma ps_meet_sizefree : forall E F,
  ps_size_free E = true -> ps_size_free F = true ->
  ps_size_free (ps_meet E F) = true.
Proof.
  induction E; intros F HE HF; destruct F; simpl in *; auto; try discriminate.
  - destruct (Nat.eqb index index0); reflexivity.
  - apply andb_true_iff in HE as [H1 H2]. apply andb_true_iff in HF as [H3 H4].
    rewrite IHE1, IHE2; auto.
  - apply andb_true_iff in HE as [H1 H2]. apply andb_true_iff in HF as [H3 H4].
    rewrite IHE1, IHE2; auto.
Qed.

Lemma pst_merge_sizefree : forall T U joining V,
  pst_merge joining T U = Some V -> pst_sizefree T -> pst_sizefree U -> pst_sizefree V.
Proof.
  fix IH 1. intros T U joining V Hmerge HT HU.
  destruct T as [| |A E B|Ts|T E]; destruct U as [| |A' F B'|Us|U F];
    simpl in Hmerge; try discriminate; simpl in HT, HU.
  - inversion Hmerge; subst; exact I.
  - inversion Hmerge; subst; exact I.
  - destruct (pst_merge (negb joining) A A') as [D|] eqn:HD; try discriminate.
    destruct (pst_merge joining B B') as [R|] eqn:HR; try discriminate.
    inversion Hmerge; subst; simpl.
    destruct HT as [HA [HE HB]], HU as [HA' [HF HB']].
    split; [eapply IH; eauto|]. split; [|eapply IH; eauto].
    destruct joining; simpl; [apply andb_true_iff; auto|apply ps_meet_sizefree; assumption].
  - change (match pst_merge_list joining Ts Us with
      Some Vs => Some (PSTyProduct Vs) | None => None end = Some V) in Hmerge.
    destruct (pst_merge_list joining Ts Us) as [Vs|] eqn:Hlist; try discriminate.
    inversion Hmerge; subst.
    clear Hmerge. revert Us Vs HT HU Hlist.
    induction Ts as [|T Ts IHTs]; intros [|U Us] Vs HT HU Hlist;
      simpl in Hlist; try discriminate.
    + inversion Hlist; subst; exact I.
    + destruct (pst_merge joining T U) as [V|] eqn:HV; try discriminate.
      destruct (pst_merge_list joining Ts Us) as [Vs'|] eqn:HVs; try discriminate.
      inversion Hlist; subst. simpl in HT, HU |- *.
      destruct HT as [HT HTs], HU as [HU HUs].
      split; [eapply IH; eauto | eapply IHTs; eauto].
  - destruct (pst_merge joining T U) as [R|] eqn:HR; try discriminate.
    inversion Hmerge; subst; simpl. destruct HT, HU.
    split; [eapply IH; eauto|].
    destruct joining; simpl; [apply andb_true_iff; auto|apply ps_meet_sizefree; assumption].
Qed.

Lemma pst_merge_inputfree : forall T U joining V,
  pst_merge joining T U = Some V -> pst_inputfree T -> pst_inputfree U -> pst_inputfree V.
Proof.
  fix IH 1. intros T U joining V Hmerge HT HU.
  destruct T as [| |A E B|Ts|T E]; destruct U as [| |A' F B'|Us|U F];
    simpl in Hmerge; try discriminate; simpl in HT, HU.
  - inversion Hmerge; subst; exact I.
  - inversion Hmerge; subst; exact I.
  - destruct (pst_merge (negb joining) A A') as [D|] eqn:HD; try discriminate.
    destruct (pst_merge joining B B') as [R|] eqn:HR; try discriminate.
    inversion Hmerge; subst; simpl. destruct HT, HU.
    split; [eapply pst_merge_sizefree; eauto | eapply IH; eauto].
  - change (match pst_merge_list joining Ts Us with
      Some Vs => Some (PSTyProduct Vs) | None => None end = Some V) in Hmerge.
    destruct (pst_merge_list joining Ts Us) as [Vs|] eqn:Hlist; try discriminate.
    inversion Hmerge; subst.
    clear Hmerge. revert Us Vs HT HU Hlist.
    induction Ts as [|T Ts IHTs]; intros [|U Us] Vs HT HU Hlist;
      simpl in Hlist; try discriminate.
    + inversion Hlist; subst; exact I.
    + destruct (pst_merge joining T U) as [V|] eqn:HV; try discriminate.
      destruct (pst_merge_list joining Ts Us) as [Vs'|] eqn:HVs; try discriminate.
      inversion Hlist; subst. simpl in HT, HU |- *.
      destruct HT as [HT HTs], HU as [HU HUs].
      split; [eapply IH; eauto | eapply IHTs; eauto].
  - destruct (pst_merge joining T U) as [R|] eqn:HR; try discriminate.
    inversion Hmerge; subst; simpl. eapply IH; eauto.
Qed.

(** The polarity parameter is essential: contravariant domain checks reverse
    their operands. Both domains are entirely size-free in that case. *)
Lemma pst_compatibility_rhs_free_go : forall T U d (forward : bool),
  (if forward then pst_inputfree T /\ pst_sizefree U
   else pst_sizefree T /\ pst_inputfree U) ->
  ps_rhs_free (pst_subtype_constraint_go d forward T U).
Proof.
  fix IH 1. intros T U d forward H.
  destruct T as [| |A E B|Ts|T E]; destruct U as [| |A' F B'|Us|U F];
    simpl; auto.
  - destruct forward; simpl in *.
    + destruct H as [[HA HB] [HA' [HF HB']]].
      split; [apply IH; simpl; split; auto using pst_sizefree_inputfree|].
      split; [exact HF|apply IH; simpl; auto].
    + destruct H as [[HA [HE HB]] [HA' HB']].
      split; [apply IH; simpl; split; auto using pst_sizefree_inputfree|].
      split; [exact HE|apply IH; simpl; auto].
  - revert Us H. induction Ts as [|T Ts IHTs]; intros [|U Us] H; simpl; auto.
    destruct forward; simpl in *.
    + destruct H as [[HT HTs] [HU HUs]]. split.
      * apply IH; simpl; auto.
      * apply IHTs; simpl; auto.
    + destruct H as [[HT HTs] [HU HUs]]. split.
      * apply IH; simpl; auto.
      * apply IHTs; simpl; auto.
  - destruct forward; simpl in *.
    + destruct H as [HT [HU HF]]. split; [apply IH; simpl; auto|exact HF].
    + destruct H as [[HT HE] HU]. split; [apply IH; simpl; auto|exact HE].
Qed.

Theorem pst_compatibility_rhs_free : forall d T U,
  pst_inputfree T -> pst_sizefree U -> ps_rhs_free (pst_subtype_constraint d T U).
Proof. intros. apply pst_compatibility_rhs_free_go; simpl; auto. Qed.

Definition pi_context_inputfree (Gamma : pi_context) := Forall pst_inputfree Gamma.

Lemma pi_context_inputfree_lookup : forall Gamma i T,
  pi_context_inputfree Gamma -> nth_error Gamma i = Some T -> pst_inputfree T.
Proof.
  intros Gamma i T H. revert i T. induction H; intros [|i] T Hlookup;
    simpl in Hlookup; try discriminate.
  - inversion Hlookup; subst; assumption.
  - eauto.
Qed.

Lemma pi_context_shift_inputfree : forall Gamma,
  pi_context_inputfree Gamma -> pi_context_inputfree (pi_context_shift Gamma).
Proof.
  intros Gamma H; induction H; simpl; constructor; auto using pst_subst_inputfree.
Qed.

Lemma pi_product_inputfree : forall Ts,
  Forall pst_inputfree Ts -> pst_inputfree (PSTyProduct Ts).
Proof. intros Ts H; induction H; simpl; auto. Qed.

Theorem pi_inference_inputfree_mut : forall M,
  (forall d Gamma e T E C, pi_infers M d Gamma e T E C ->
    pi_context_inputfree Gamma -> pst_inputfree T /\ ps_rhs_free C) /\
  (forall d Gamma es Ts Es Cs, pi_infers_list M d Gamma es Ts Es Cs ->
    pi_context_inputfree Gamma -> Forall pst_inputfree Ts /\ ps_rhs_free (pi_conjoin Cs)).
Proof.
  intro M. apply pi_inference_mutind.
  - intros d Gamma i T Hlookup HT HG. split; [eapply pi_context_inputfree_lookup; eauto|exact I].
  - intros; split; exact I.
  - intros; split; exact I.
  - intros d Gamma es Ts Cs Hv Hlist IH HG. destruct (IH HG).
    split; auto using pi_product_inputfree.
  - intros; split; exact I.
  - intros; split; exact I.
  - intros d Gamma e f A B E F C D He IHe Hf IHf HG.
    destruct (IHe HG) as [HA HC].
    assert (HAG : pi_context_inputfree (A :: Gamma)) by (constructor; assumption).
    destruct (IHf HAG) as [HB HD]. split; [exact HB|split; assumption].
  - intros d Gamma e f g T U V E F G C D H He IHe Hf IHf Hg IHg Hjoin HV Hctx.
    destruct (IHe Hctx) as [_ HC], (IHf Hctx) as [HT HD], (IHg Hctx) as [HU HH].
    split.
    + apply pst_norm_inputfree. eapply pst_merge_inputfree; eauto.
    + simpl; auto.
  - intros d Gamma es Ts Es Cs Hlist IH HG. destruct (IH HG).
    split; auto using pi_product_inputfree.
  - intros d Gamma A e B E C HA He IH HG.
    assert (HAG : pi_context_inputfree (pst_embed A :: Gamma)).
    { constructor; auto. apply pst_sizefree_inputfree, pst_embed_sizefree. }
    destruct (IH HAG) as [HB HC]. split; [simpl; split; auto using pst_embed_sizefree|exact HC].
  - intros d Gamma e f A B U E F G C D He IHe Hf IHf HG.
    destruct (IHe HG) as [[HA HB] HC], (IHf HG) as [HU HD].
    split; [exact HB|]. simpl; split; [exact HC|]. split; [exact HD|].
    apply ps_rhs_free_norm, pst_compatibility_rhs_free; assumption.
  - intros d Gamma e T E C HG He IH Hctx.
    destruct (IH (pi_context_shift_inputfree Gamma Hctx)). simpl; auto.
  - intros d Gamma e T E F G C He IH HF HG.
    destruct (IH HG) as [HT HC]. split; [|exact HC].
    apply pst_norm_inputfree, pst_subst_inputfree. exact HT.
  - intros; split; [constructor|exact I].
  - intros d Gamma e es T Ts E Es C Cs He IHe Hes IHes HG.
    destruct (IHe HG), (IHes HG). split; [constructor; assumption|split; assumption].
Qed.

(** The first proposed theorem in the revised manuscript, now derived from
    generation. It applies even to open contexts whose stored types can have
    symbolic results and suspended effects, provided all arrow inputs are
    entirely size-free. *)
Theorem pi_size_free_expected_contracts : forall M d Gamma e T E C,
  pi_infers M d Gamma e T E C -> pi_context_inputfree Gamma ->
  pst_inputfree T /\ ps_rhs_free C.
Proof. intros M. exact (proj1 (pi_inference_inputfree_mut M)). Qed.

Inductive ps_guard_occurs (scope : nat) (E F : ps_effect) : local_constraint -> Prop :=
| PSGuardHere : ps_guard_occurs scope E F (LGuard scope E F)
| PSGuardLeft : forall C D, ps_guard_occurs scope E F C ->
    ps_guard_occurs scope E F (LAnd C D)
| PSGuardRight : forall C D, ps_guard_occurs scope E F D ->
    ps_guard_occurs scope E F (LAnd C D).

Lemma ps_rhs_free_guard : forall scope E F C,
  ps_guard_occurs scope E F C -> ps_rhs_free C -> ps_size_free F = true.
Proof. intros scope E F C H; induction H; simpl; tauto. Qed.

Corollary pi_generated_guard_sizefree : forall M d Gamma e T E C scope G H,
  pi_infers M d Gamma e T E C -> pi_context_inputfree Gamma ->
  ps_guard_occurs scope G H C -> ps_size_free H = true.
Proof.
  intros M d Gamma e T E C scope G H Hgen Hctx Hoccurs.
  eapply ps_rhs_free_guard; [exact Hoccurs|].
  exact (proj2 (pi_size_free_expected_contracts _ _ _ _ _ _ _ Hgen Hctx)).
Qed.

Corollary pi_closed_expected_contracts_sizefree : forall M e T E C,
  pi_infers M 0 [] e T E C -> pst_inputfree T /\ ps_rhs_free C.
Proof. intros; eapply pi_size_free_expected_contracts; [eassumption|constructor]. Qed.
