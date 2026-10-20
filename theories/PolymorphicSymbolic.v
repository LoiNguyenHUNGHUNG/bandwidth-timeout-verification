(** Open symbolic effects for the effect-polymorphic size inference system.
    Whole-effect variables and download-size variables have distinct syntax.
    Closing expansion substitutes only whole effects and preserves unknown
    sizes; the existing numeric root compiler can therefore be reused. *)
From Stdlib Require Import Arith Bool Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Bandwidth
  Typing SizeInference Symbolic Compatibility RootConstraints PolymorphicEffects.
Import ListNotations.
Open Scope Q_scope.

Inductive ps_effect : Type :=
| PSELiteral (Phi : effect)
| PSESize (a : size_variable) (timeout : positive_rational)
| PSEVar (index : nat)
| PSEJoin (left right : ps_effect)
| PSEPar (left right : ps_effect).

(** The empty effect is the empty finite literal; [ps_empty] abbreviates it. *)
Definition ps_empty : ps_effect := PSELiteral [].
Definition ps_environment (d : nat) (eta : nat -> effect) : Prop :=
  forall i, (i < d)%nat -> effect_wf (eta i).

Fixpoint ps_scoped (d : nat) (E : ps_effect) : Prop :=
  match E with
  | PSELiteral Phi => effect_wf Phi
  | PSESize _ _ => True
  | PSEVar i => (i < d)%nat
  | PSEJoin E F | PSEPar E F => ps_scoped d E /\ ps_scoped d F
  end.

Definition ps_literal (Phi : effect) : symbolic_effect :=
  map (fun p => SymbolicObligation (SRateConcrete (rate p)) (concurrency p)) Phi.

Fixpoint ps_expand (eta : nat -> effect) (E : ps_effect) : symbolic_effect :=
  match E with
  | PSELiteral Phi => ps_literal Phi
  | PSESize a t => [SymbolicObligation (SRateVariable a t) 1]
  | PSEVar i => ps_literal (eta i)
  | PSEJoin E F => symbolic_join (ps_expand eta E) (ps_expand eta F)
  | PSEPar E F => symbolic_parallel (ps_expand eta E) (ps_expand eta F)
  end.

(** Raw denotation makes the concurrency-preserving expansion lemma literal
    equality. Observational denotation normalizes its result. *)
Fixpoint ps_eval_raw (sigma : size_assignment) (eta : nat -> effect)
    (E : ps_effect) : effect :=
  match E with
  | PSELiteral Phi => Phi
  | PSESize a t => [Obligation (sigma a / t) 1]
  | PSEVar i => eta i
  | PSEJoin E F => join (ps_eval_raw sigma eta E) (ps_eval_raw sigma eta F)
  | PSEPar E F => parallel (ps_eval_raw sigma eta E) (ps_eval_raw sigma eta F)
  end.

Definition ps_eval sigma eta E := normalize (ps_eval_raw sigma eta E).

Lemma ps_literal_instantiates : forall sigma Phi,
  instantiate_effect_raw sigma (ps_literal Phi) = Phi.
Proof.
  intros sigma Phi. unfold instantiate_effect_raw, ps_literal. rewrite map_map.
  induction Phi as [|[r n] tail IH]; simpl; auto. rewrite IH. reflexivity.
Qed.

Theorem ps_expand_assignment_commutes : forall sigma eta E,
  instantiate_effect_raw sigma (ps_expand eta E) = ps_eval_raw sigma eta E.
Proof.
  intros sigma eta E. induction E; simpl.
  - apply ps_literal_instantiates.
  - reflexivity.
  - apply ps_literal_instantiates.
  - rewrite instantiate_symbolic_join_raw, IHE1, IHE2. reflexivity.
  - rewrite instantiate_symbolic_parallel_raw, IHE1, IHE2. reflexivity.
Qed.

Lemma ps_literal_wf : forall Phi,
  effect_wf Phi -> symbolic_effect_wf (ps_literal Phi).
Proof.
  intros Phi H. induction H; simpl; constructor; auto.
  unfold symbolic_obligation_wf. simpl. constructor. exact H.
Qed.

Lemma ps_symbolic_shift_wf : forall k Phi,
  symbolic_effect_wf Phi -> symbolic_effect_wf (symbolic_shift_effect k Phi).
Proof.
  intros k Phi H. induction H; simpl; constructor; auto.
Qed.

Lemma ps_symbolic_parallel_wf : forall Phi Psi,
  symbolic_effect_wf Phi -> symbolic_effect_wf Psi ->
  symbolic_effect_wf (symbolic_parallel Phi Psi).
Proof.
  intros Phi Psi H1 H2. unfold symbolic_parallel, symbolic_join.
  apply Forall_app. split; apply ps_symbolic_shift_wf; assumption.
Qed.

Theorem ps_expand_wf : forall d E eta,
  ps_scoped d E -> ps_environment d eta -> symbolic_effect_wf (ps_expand eta E).
Proof.
  intros d E. induction E; intros eta Hsc Henv; simpl in *.
  - apply ps_literal_wf. exact Hsc.
  - constructor; [constructor|constructor].
  - apply ps_literal_wf. apply Henv. exact Hsc.
  - destruct Hsc as [H1 H2]. unfold symbolic_join.
    apply Forall_app. split; [exact (IHE1 eta H1 Henv)|exact (IHE2 eta H2 Henv)].
  - destruct Hsc as [H1 H2]. apply ps_symbolic_parallel_wf;
      [exact (IHE1 eta H1 Henv)|exact (IHE2 eta H2 Henv)].
Qed.

Lemma ps_eval_raw_wf : forall d E sigma eta,
  ps_scoped d E -> ps_environment d eta -> effect_wf (ps_eval_raw sigma eta E).
Proof.
  intros d E sigma eta HE Heta. rewrite <- ps_expand_assignment_commutes.
  apply instantiate_effect_raw_wf. eapply ps_expand_wf; eauto.
Qed.

Definition ps_root eta E B := root_constraint (ps_expand eta E) B.

Theorem ps_root_exact : forall d E eta sigma B,
  ps_scoped d E -> ps_environment d eta -> 0 <= B ->
  (models sigma (ps_root eta E B) <-> required_bandwidth (ps_eval sigma eta E) <= B).
Proof.
  intros d E eta sigma B HE Heta HB. unfold ps_root.
  rewrite root_constraint_exact by (eauto using ps_expand_wf).
  unfold instantiate_effect, ps_eval. rewrite ps_expand_assignment_commutes.
  reflexivity.
Qed.

(** Closedness and size-free contracts are deliberately independent tests. *)
Fixpoint ps_closed (E : ps_effect) : bool :=
  match E with
  | PSELiteral _ | PSESize _ _ => true
  | PSEVar _ => false
  | PSEJoin E F | PSEPar E F => ps_closed E && ps_closed F
  end.

Fixpoint ps_size_free (E : ps_effect) : bool :=
  match E with
  | PSELiteral _ | PSEVar _ => true
  | PSESize _ _ => false
  | PSEJoin E F | PSEPar E F => ps_size_free E && ps_size_free F
  end.

Definition ps_empty_environment : nat -> effect := fun _ => [].
Definition ps_zero_assignment : size_assignment := fun _ => checked_size_bound 0.

Lemma ps_empty_environment_wf : forall d, ps_environment d ps_empty_environment.
Proof. intros d i Hi. constructor. Qed.

(** Whole-effect parameters occur only positively. Increasing their denotations
    therefore increases every symbolic effect, including its parallel counts. *)
Lemma ps_eval_raw_environment_mono : forall E sigma eta eta',
  (forall i, eta i ≼ eta' i) ->
  ps_eval_raw sigma eta E ≼ ps_eval_raw sigma eta' E.
Proof.
  induction E; intros sigma eta eta' Heta; simpl.
  - apply effect_le_refl.
  - apply effect_le_refl.
  - apply Heta.
  - apply join_mono; [apply IHE1|apply IHE2]; exact Heta.
  - apply parallel_mono; [apply IHE1|apply IHE2]; exact Heta.
Qed.

Lemma ps_eval_raw_empty_environment_le : forall E sigma eta,
  ps_eval_raw sigma ps_empty_environment E ≼ ps_eval_raw sigma eta E.
Proof.
  intros E sigma eta. apply ps_eval_raw_environment_mono.
  intro i. apply empty_effect_le.
Qed.

Lemma ps_closed_environment_independent : forall E sigma eta eta',
  ps_closed E = true -> ps_eval_raw sigma eta E = ps_eval_raw sigma eta' E.
Proof.
  induction E; intros sigma eta eta' H; simpl in *; try reflexivity;
    try discriminate; apply andb_true_iff in H as [H1 H2];
    rewrite (IHE1 sigma eta eta' H1), (IHE2 sigma eta eta' H2); reflexivity.
Qed.

Lemma ps_size_free_assignment_independent : forall E sigma sigma' eta,
  ps_size_free E = true -> ps_eval_raw sigma eta E = ps_eval_raw sigma' eta E.
Proof.
  induction E; intros sigma sigma' eta H; simpl in *; try reflexivity;
    try discriminate; apply andb_true_iff in H as [H1 H2];
    rewrite (IHE1 sigma sigma' eta H1), (IHE2 sigma sigma' eta H2); reflexivity.
Qed.

Lemma ps_shift_zero : forall Phi, shift_effect 0 Phi = Phi.
Proof.
  induction Phi as [|[r n] Phi IH]; simpl; auto.
  unfold shift. simpl. rewrite Nat.add_0_r, IH. reflexivity.
Qed.

Lemma ps_parallel_empty_l : forall Phi, parallel [] Phi = Phi.
Proof. intros Phi. unfold parallel, join. simpl. apply ps_shift_zero. Qed.
Lemma ps_parallel_empty_r : forall Phi, parallel Phi [] = Phi.
Proof. intros Phi. unfold parallel, join. simpl. rewrite app_nil_r, ps_shift_zero. reflexivity. Qed.

(** Empty-only normalization used by the finite proof search. It never
    reassociates effects and does not prune symbolic obligations. *)
Definition ps_simpl_join E F :=
  match E, F with
  | PSELiteral [], _ => F
  | _, PSELiteral [] => E
  | _, _ => PSEJoin E F
  end.
Definition ps_simpl_par E F :=
  match E, F with
  | PSELiteral [], _ => F
  | _, PSELiteral [] => E
  | _, _ => PSEPar E F
  end.
Fixpoint ps_simpl_empty E :=
  match E with
  | PSEJoin E F => ps_simpl_join (ps_simpl_empty E) (ps_simpl_empty F)
  | PSEPar E F => ps_simpl_par (ps_simpl_empty E) (ps_simpl_empty F)
  | _ => E
  end.

Lemma ps_simpl_join_exact : forall E F sigma eta,
  ps_eval_raw sigma eta (ps_simpl_join E F) =
  join (ps_eval_raw sigma eta E) (ps_eval_raw sigma eta F).
Proof.
  intros E F sigma eta. destruct E; destruct F; simpl;
    try (destruct Phi); try (destruct Phi0); simpl; unfold join;
    try rewrite app_nil_r; reflexivity.
Qed.

Lemma ps_simpl_par_exact : forall E F sigma eta,
  ps_eval_raw sigma eta (ps_simpl_par E F) =
  parallel (ps_eval_raw sigma eta E) (ps_eval_raw sigma eta F).
Proof.
  intros E F sigma eta. destruct E; destruct F; simpl;
    try (destruct Phi); try (destruct Phi0); simpl;
    try rewrite ps_parallel_empty_l; try rewrite ps_parallel_empty_r; reflexivity.
Qed.

Theorem ps_simpl_empty_exact : forall E sigma eta,
  ps_eval_raw sigma eta (ps_simpl_empty E) = ps_eval_raw sigma eta E.
Proof.
  induction E; intros sigma eta; simpl; try reflexivity.
  - rewrite ps_simpl_join_exact, IHE1, IHE2. reflexivity.
  - rewrite ps_simpl_par_exact, IHE1, IHE2. reflexivity.
Qed.

(** Embedding the size-free source grammar excludes unknown sizes by
    construction. Instantiation changes sizes, never whole-effect binders. *)
Fixpoint ps_embed (E : open_effect) : ps_effect :=
  match E with
  | EffLit Phi => PSELiteral Phi
  | EffVar i => PSEVar i
  | EffJoin E F => PSEJoin (ps_embed E) (ps_embed F)
  | EffPar E F => PSEPar (ps_embed E) (ps_embed F)
  end.
Fixpoint ps_instantiate (sigma : size_assignment) (E : ps_effect) : open_effect :=
  match E with
  | PSELiteral Phi => EffLit Phi
  | PSESize a t => EffLit [Obligation (sigma a / t) 1]
  | PSEVar i => EffVar i
  | PSEJoin E F => EffJoin (ps_instantiate sigma E) (ps_instantiate sigma F)
  | PSEPar E F => EffPar (ps_instantiate sigma E) (ps_instantiate sigma F)
  end.
Fixpoint ps_subst (s : nat -> open_effect) (E : ps_effect) : ps_effect :=
  match E with
  | PSELiteral Phi => PSELiteral Phi
  | PSESize a t => PSESize a t
  | PSEVar i => ps_embed (s i)
  | PSEJoin E F => PSEJoin (ps_subst s E) (ps_subst s F)
  | PSEPar E F => PSEPar (ps_subst s E) (ps_subst s F)
  end.

Theorem ps_instantiate_embed : forall sigma E, ps_instantiate sigma (ps_embed E) = E.
Proof. intros sigma E. induction E; simpl; congruence. Qed.

Theorem ps_instantiate_subst : forall sigma s E,
  ps_instantiate sigma (ps_subst s E) = eff_subst s (ps_instantiate sigma E).
Proof.
  intros sigma s E. induction E; simpl; try congruence.
  apply ps_instantiate_embed.
Qed.

Theorem ps_instantiate_scoped : forall d E sigma,
  ps_scoped d E -> eff_scoped d (ps_instantiate sigma E).
Proof.
  intros d E. induction E; intros sigma H; simpl in *.
  - constructor. exact H.
  - constructor. constructor; [|constructor]. unfold obligation_wf. simpl.
    exact (instantiate_rate_nonnegative sigma (SRateVariable a timeout)
      (WfSRateVariable a timeout)).
  - constructor. exact H.
  - destruct H. constructor; auto.
  - destruct H. constructor; auto.
Qed.

Theorem ps_eval_instantiate : forall E sigma eta,
  ps_eval sigma eta E ≈ eff_eval eta (ps_instantiate sigma E).
Proof.
  induction E; intros sigma eta; simpl.
  - apply normalize_coverage_equiv.
  - apply normalize_coverage_equiv.
  - apply normalize_coverage_equiv.
  - destruct (IHE1 sigma eta) as [H1 H1']; destruct (IHE2 sigma eta) as [H2 H2'].
    unfold ps_eval in *. simpl. unfold sequential_effect. split; apply normalize_mono;
      apply join_mono; eapply effect_le_trans; eauto using le_normalize, normalize_le.
  - destruct (IHE1 sigma eta) as [H1 H1']; destruct (IHE2 sigma eta) as [H2 H2'].
    unfold ps_eval in *. simpl. unfold parallel_effect. split; apply normalize_mono;
      apply parallel_mono; eapply effect_le_trans; eauto using le_normalize, normalize_le.
Qed.

(** Incremental normalization folds only numerical children. Unknown size
    singletons survive unchanged; normalization never reassociates the tree. *)
Definition ps_norm_join E F :=
  match E, F with
  | PSELiteral Phi, PSELiteral Psi => PSELiteral (sequential_effect Phi Psi)
  | _, _ => ps_simpl_join E F
  end.
Definition ps_norm_par E F :=
  match E, F with
  | PSELiteral Phi, PSELiteral Psi => PSELiteral (parallel_effect Phi Psi)
  | _, _ => ps_simpl_par E F
  end.
Fixpoint ps_norm E :=
  match E with
  | PSELiteral Phi => PSELiteral (normalize Phi)
  | PSEJoin E F => ps_norm_join (ps_norm E) (ps_norm F)
  | PSEPar E F => ps_norm_par (ps_norm E) (ps_norm F)
  | _ => E
  end.

Lemma ps_norm_join_eval : forall E F sigma eta,
  ps_eval_raw sigma eta (ps_norm_join E F) ≈
  join (ps_eval_raw sigma eta E) (ps_eval_raw sigma eta F).
Proof.
  intros E F sigma eta. destruct E; destruct F; cbn [ps_norm_join];
    try rewrite ps_simpl_join_exact; try apply effect_equiv_refl.
  apply normalize_coverage_equiv.
Qed.
Lemma ps_norm_par_eval : forall E F sigma eta,
  ps_eval_raw sigma eta (ps_norm_par E F) ≈
  parallel (ps_eval_raw sigma eta E) (ps_eval_raw sigma eta F).
Proof.
  intros E F sigma eta. destruct E; destruct F; cbn [ps_norm_par];
    try rewrite ps_simpl_par_exact; try apply effect_equiv_refl.
  apply normalize_coverage_equiv.
Qed.
Theorem ps_norm_eval : forall E sigma eta,
  ps_eval_raw sigma eta (ps_norm E) ≈ ps_eval_raw sigma eta E.
Proof.
  induction E; intros sigma eta; simpl.
  - apply normalize_coverage_equiv.
  - apply effect_equiv_refl.
  - apply effect_equiv_refl.
  - eapply effect_equiv_trans; [apply ps_norm_join_eval|].
    destruct (IHE1 sigma eta), (IHE2 sigma eta). split; apply join_mono; assumption.
  - eapply effect_equiv_trans; [apply ps_norm_par_eval|].
    destruct (IHE1 sigma eta), (IHE2 sigma eta). split; apply parallel_mono; assumption.
Qed.

Theorem ps_norm_core_equiv : forall d E sigma,
  eff_equiv d (ps_instantiate sigma (ps_norm E)) (ps_instantiate sigma E).
Proof.
  intros d E sigma. split; intros eta Heta;
    destruct (ps_eval_instantiate (ps_norm E) sigma eta) as [HN HN'];
    destruct (ps_eval_instantiate E sigma eta) as [HE HE'];
    destruct (ps_norm_eval E sigma eta) as [Hraw Hraw']; unfold ps_eval in *.
  - eapply effect_le_trans; [exact HN'|].
    eapply effect_le_trans; [apply normalize_mono; exact Hraw|exact HE].
  - eapply effect_le_trans; [exact HE'|].
    eapply effect_le_trans; [apply normalize_mono; exact Hraw'|exact HN].
Qed.

Lemma ps_simpl_join_scoped : forall d E F,
  ps_scoped d E -> ps_scoped d F -> ps_scoped d (ps_simpl_join E F).
Proof.
  intros d E F HE HF. destruct E; destruct F; simpl in *;
    try destruct Phi; try destruct Phi0; simpl in *; auto.
Qed.
Lemma ps_simpl_par_scoped : forall d E F,
  ps_scoped d E -> ps_scoped d F -> ps_scoped d (ps_simpl_par E F).
Proof.
  intros d E F HE HF. destruct E; destruct F; simpl in *;
    try destruct Phi; try destruct Phi0; simpl in *; auto.
Qed.
Theorem ps_norm_scoped : forall d E, ps_scoped d E -> ps_scoped d (ps_norm E).
Proof.
  intros d E. induction E; intro H; simpl in *; auto using normalize_wf.
  - destruct H as [H1 H2]. specialize (IHE1 H1). specialize (IHE2 H2).
    unfold ps_norm_join. destruct (ps_norm E1); destruct (ps_norm E2);
      try apply ps_simpl_join_scoped; auto.
    apply normalize_wf, effect_wf_join; assumption.
  - destruct H as [H1 H2]. specialize (IHE1 H1). specialize (IHE2 H2).
    unfold ps_norm_par. destruct (ps_norm E1); destruct (ps_norm E2);
      try apply ps_simpl_par_scoped; auto.
    apply normalize_wf, effect_wf_parallel; assumption.
Qed.

Lemma ps_embed_scoped : forall d E,
  eff_scoped d E -> ps_scoped d (ps_embed E).
Proof. intros d E H. induction H; simpl; auto. Qed.

Lemma ps_subst_scoped : forall d E,
  ps_scoped d E -> forall d' s,
  (forall i, (i < d)%nat -> eff_scoped d' (s i)) -> ps_scoped d' (ps_subst s E).
Proof.
  intros d E. induction E; intros H d' s Hs; simpl in *; auto.
  - apply ps_embed_scoped. auto.
  - destruct H. split; eauto.
  - destruct H. split; eauto.
Qed.
