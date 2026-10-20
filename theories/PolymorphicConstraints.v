(** Scoped local constraints, partial elimination, and the three-way solver.

    A local guard universally quantifies over its recorded effect scope. A
    root closing environment is used only by root bandwidth checking, never
    to discharge a local guard. Unsupported elimination returns unresolved,
    rather than a claim of inconsistency. *)
From Stdlib Require Import Arith Bool Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Bandwidth
  Typing SizeInference Symbolic Compatibility RootConstraints
  PolymorphicEffects PolymorphicSymbolic.
Import ListNotations.
Open Scope Q_scope.

Definition ps_guard_models sigma d E F : Prop :=
  forall eta, ps_environment d eta ->
    ps_eval_raw sigma eta E ≼ ps_eval_raw sigma eta F.

Inductive local_constraint : Type :=
| LNumeric (D : constraint)
| LAnd (C1 C2 : local_constraint)
| LGuard (scope : nat) (source target : ps_effect).

Fixpoint ps_models (sigma : size_assignment) (C : local_constraint) : Prop :=
  match C with
  | LNumeric D => models sigma D
  | LAnd C1 C2 => ps_models sigma C1 /\ ps_models sigma C2
  | LGuard d E F => ps_guard_models sigma d E F
  end.

Fixpoint ps_constraint_wf (C : local_constraint) : Prop :=
  match C with
  | LNumeric _ => True
  | LAnd C1 C2 => ps_constraint_wf C1 /\ ps_constraint_wf C2
  | LGuard d E F => ps_scoped d E /\ ps_scoped d F
  end.

Lemma ps_guard_core_exact : forall sigma d E F,
  ps_guard_models sigma d E F <->
  eff_le d (ps_instantiate sigma E) (ps_instantiate sigma F).
Proof.
  intros sigma d E F. split; intros H eta Heta;
    destruct (ps_eval_instantiate E sigma eta) as [HE HE'];
    destruct (ps_eval_instantiate F sigma eta) as [HF HF'];
    specialize (H eta Heta); unfold ps_eval in *.
  - eapply effect_le_trans; [exact HE'|].
    eapply effect_le_trans; [apply normalize_mono; exact H|exact HF].
  - eapply effect_le_trans; [apply le_normalize|].
    eapply effect_le_trans; [exact HE|].
    eapply effect_le_trans; [exact H|].
    eapply effect_le_trans; [exact HF'|apply normalize_le].
Qed.

Definition ps_literal_leb (Phi Psi : effect) : bool :=
  forallb (fun p => existsb (fun q => obligation_leb p q) Psi) Phi.

Lemma ps_literal_leb_sound : forall Phi Psi,
  ps_literal_leb Phi Psi = true -> Phi ≼ Psi.
Proof.
  intros Phi Psi H p Hin. unfold ps_literal_leb in H.
  apply forallb_forall with (x:=p) in H; auto.
  apply existsb_exists in H as [q [Hq Hle]].
  exists q. split; auto. apply obligation_leb_spec. exact Hle.
Qed.

Definition ps_atom (E F : ps_effect) : bool :=
  match E, F with
  | PSELiteral Phi, PSELiteral Psi => ps_literal_leb Phi Psi
  | PSEVar i, PSEVar j => Nat.eqb i j
  | PSESize a t, PSESize b u => Nat.eqb a b && Qeq_bool t u
  | _, _ => false
  end.

Lemma ps_atom_sound : forall E F sigma eta,
  ps_atom E F = true -> ps_eval_raw sigma eta E ≼ ps_eval_raw sigma eta F.
Proof.
  intros E F sigma eta. destruct E; destruct F; simpl; intro H; try discriminate.
  - apply ps_literal_leb_sound. exact H.
  - apply andb_true_iff in H as [Ha Ht]. apply Nat.eqb_eq in Ha.
    apply Qeq_bool_eq in Ht. subst a0.
    intros p [Hp|[]]. subst p. exists (Obligation (sigma a / timeout0) 1).
    split; [left; reflexivity|]. split; simpl; [|lia]. rewrite Ht. apply Qle_refl.
  - apply Nat.eqb_eq in H. subst index0. apply effect_le_refl.
Qed.

Lemma ps_join_le : forall Phi Psi Xi,
  Phi ≼ Xi -> Psi ≼ Xi -> join Phi Psi ≼ Xi.
Proof.
  intros Phi Psi Xi H1 H2 p Hin. apply in_app_or in Hin.
  destruct Hin; auto.
Qed.

Lemma ps_effect_le_shift : forall Phi k, Phi ≼ shift_effect k Phi.
Proof.
  intros Phi k p Hin. exists (shift k p). split.
  - apply in_map. exact Hin.
  - split; simpl; [apply Qle_refl|lia].
Qed.
Lemma ps_effect_le_parallel_l : forall Phi Psi, Phi ≼ parallel Phi Psi.
Proof.
  intros Phi Psi. unfold parallel. eapply effect_le_trans.
  - apply ps_effect_le_shift.
  - apply effect_le_join_l.
Qed.
Lemma ps_effect_le_parallel_r : forall Phi Psi, Psi ≼ parallel Phi Psi.
Proof.
  intros Phi Psi. unfold parallel. eapply effect_le_trans.
  - apply ps_effect_le_shift.
  - apply effect_le_join_r.
Qed.

(** The ordered clauses extend the appendix's G search with commuted binary
    parallel matching. Fuel controls termination only: every successful
    derivation is universally sound. This is not general AC matching. *)
Fixpoint ps_search (fuel : nat) (E F : ps_effect) : bool :=
  match fuel with
  | O => false
  | S k =>
      match E with
      | PSELiteral [] => true
      | PSEJoin E1 E2 => ps_search k E1 F && ps_search k E2 F
      | _ =>
          match F with
          | PSEJoin F1 F2 => ps_search k E F1 || ps_search k E F2
          | PSEPar F1 F2 =>
              ps_search k E F1 || ps_search k E F2 ||
              match E with
              | PSEPar E1 E2 =>
                  (ps_search k E1 F1 && ps_search k E2 F2) ||
                  (ps_search k E1 F2 && ps_search k E2 F1)
              | _ => false
              end
          | _ => ps_atom E F
          end
      end
  end.

Lemma ps_search_sound : forall fuel E F sigma eta,
  ps_search fuel E F = true -> ps_eval_raw sigma eta E ≼ ps_eval_raw sigma eta F.
Proof.
  induction fuel as [|fuel IH]; intros E F sigma eta H; [discriminate|].
  destruct E as [Phi|a t|i|E1 E2|E1 E2].
  - destruct Phi as [|p Phi].
    + apply empty_effect_le.
    + destruct F; cbn [ps_search] in H; try solve [apply ps_atom_sound; exact H].
      * apply orb_true_iff in H as [H|H]; eapply effect_le_trans;
          [eapply IH; exact H|apply effect_le_join_l|eapply IH; exact H|apply effect_le_join_r].
      * rewrite orb_false_r in H. apply orb_true_iff in H as [H|H];
          eapply effect_le_trans;
          [eapply IH; exact H|apply ps_effect_le_parallel_l|eapply IH; exact H|apply ps_effect_le_parallel_r].
  - destruct F; cbn [ps_search] in H; try solve [apply ps_atom_sound; exact H].
    + apply orb_true_iff in H as [H|H]; eapply effect_le_trans;
        [eapply IH; exact H|apply effect_le_join_l|eapply IH; exact H|apply effect_le_join_r].
    + rewrite orb_false_r in H. apply orb_true_iff in H as [H|H];
        eapply effect_le_trans;
        [eapply IH; exact H|apply ps_effect_le_parallel_l|eapply IH; exact H|apply ps_effect_le_parallel_r].
  - destruct F; cbn [ps_search] in H; try solve [apply ps_atom_sound; exact H].
    + apply orb_true_iff in H as [H|H]; eapply effect_le_trans;
        [eapply IH; exact H|apply effect_le_join_l|eapply IH; exact H|apply effect_le_join_r].
    + rewrite orb_false_r in H. apply orb_true_iff in H as [H|H];
        eapply effect_le_trans;
        [eapply IH; exact H|apply ps_effect_le_parallel_l|eapply IH; exact H|apply ps_effect_le_parallel_r].
  - simpl in H |- *. apply andb_true_iff in H as [H1 H2].
    apply ps_join_le; eapply IH; eauto.
  - destruct F; cbn [ps_search] in H; try solve [apply ps_atom_sound; exact H].
    + apply orb_true_iff in H as [H|H]; eapply effect_le_trans;
        [eapply IH; exact H|apply effect_le_join_l|eapply IH; exact H|apply effect_le_join_r].
    + apply orb_true_iff in H as [H|H].
      * apply orb_true_iff in H as [H|H]; eapply effect_le_trans;
          [eapply IH; exact H|apply ps_effect_le_parallel_l|eapply IH; exact H|apply ps_effect_le_parallel_r].
      * apply orb_true_iff in H as [H|H].
        -- apply andb_true_iff in H as [H1 H2].
           apply parallel_mono; eapply IH; eauto.
        -- apply andb_true_iff in H as [H1 H2].
           eapply effect_le_trans.
           ++ apply parallel_mono; [eapply IH; exact H1|eapply IH; exact H2].
           ++ apply (proj1 (parallel_comm _ _)).
Qed.

Fixpoint ps_nodes E : nat :=
  match E with
  | PSEJoin E F | PSEPar E F => S (ps_nodes E + ps_nodes F)
  | _ => 1%nat
  end.

Definition ps_trivial E F :=
  ps_search (S (ps_nodes E + ps_nodes F)) (ps_simpl_empty E) (ps_simpl_empty F).

Theorem ps_trivial_sound : forall E F sigma d,
  ps_trivial E F = true -> ps_guard_models sigma d E F.
Proof.
  intros E F sigma d H eta Heta. unfold ps_trivial in H.
  pose proof (ps_search_sound _ _ _ sigma eta H) as Hle.
  rewrite !ps_simpl_empty_exact in Hle. exact Hle.
Qed.

(** Empty is the least possible target environment. For a closed source and
    size-free target it therefore suffices to compile that universal worst
    case, even when the target still contains whole-effect parameters. *)
Definition ps_compile_guard E F : option constraint :=
  if ps_trivial E F then Some CTop
  else if ps_closed E && ps_size_free F then
    Some (effect_constraint (ps_expand ps_empty_environment E)
      (ps_eval ps_zero_assignment ps_empty_environment F))
  else None.

Theorem ps_compile_guard_closed_sizefree : forall E F,
  ps_closed E = true -> ps_size_free F = true ->
  exists D, ps_compile_guard E F = Some D.
Proof.
  intros E F HE HF. unfold ps_compile_guard.
  destruct (ps_trivial E F); [eexists; reflexivity|].
  rewrite HE, HF. eexists. reflexivity.
Qed.

Fixpoint ps_compile C : option constraint :=
  match C with
  | LNumeric D => Some D
  | LAnd C1 C2 =>
      match ps_compile C1, ps_compile C2 with
      | Some D1, Some D2 => Some (CAnd D1 D2)
      | _, _ => None
      end
  | LGuard _ E F => ps_compile_guard E F
  end.

Lemma ps_normalized_le_iff : forall Phi Psi,
  normalize Phi ≼ normalize Psi <-> Phi ≼ Psi.
Proof.
  intros Phi Psi. split; intro H.
  - eapply effect_le_trans; [apply le_normalize|].
    eapply effect_le_trans; [exact H|apply normalize_le].
  - apply normalize_mono. exact H.
Qed.

(** The all-empty environment is an exact universal test when the source is
    closed. The target may contain any positive combination of parameters:
    it is least at empty, while the source is unchanged by that choice. *)
Lemma ps_closed_source_guard_at_empty : forall d E F sigma,
  ps_closed E = true ->
  (ps_eval_raw sigma ps_empty_environment E ≼
     ps_eval_raw sigma ps_empty_environment F <->
   ps_guard_models sigma d E F).
Proof.
  intros d E F sigma HE. split.
  - intros H eta Heta.
    rewrite (ps_closed_environment_independent E sigma eta
      ps_empty_environment HE).
    eapply effect_le_trans; [exact H|apply ps_eval_raw_empty_environment_le].
  - intro H. apply H. apply ps_empty_environment_wf.
Qed.

Lemma ps_closed_guard_exact : forall d E F sigma,
  ps_scoped d E -> ps_closed E = true ->
  ps_size_free F = true ->
  (models sigma (effect_constraint (ps_expand ps_empty_environment E)
      (ps_eval ps_zero_assignment ps_empty_environment F)) <->
   ps_guard_models sigma d E F).
Proof.
  intros d E F sigma HE HCE HSF.
  rewrite effect_constraint_exact by
    (eapply ps_expand_wf; eauto using ps_empty_environment_wf).
  unfold instantiate_effect, ps_eval. rewrite ps_expand_assignment_commutes.
  rewrite ps_normalized_le_iff.
  rewrite <- (ps_size_free_assignment_independent F sigma ps_zero_assignment
    ps_empty_environment HSF).
  apply ps_closed_source_guard_at_empty. exact HCE.
Qed.

Theorem ps_compile_guard_exact : forall d E F D,
  ps_scoped d E -> ps_compile_guard E F = Some D ->
  forall sigma, models sigma D <-> ps_guard_models sigma d E F.
Proof.
  intros d E F D HE Hcompile sigma. unfold ps_compile_guard in Hcompile.
  destruct (ps_trivial E F) eqn:Ht.
  - inversion Hcompile; subst. split.
    + intros _. apply ps_trivial_sound. exact Ht.
    + intros _. exact I.
  - destruct (ps_closed E && ps_size_free F) eqn:Hclosed;
      try discriminate.
    apply andb_true_iff in Hclosed as [HCE HSF].
    inversion Hcompile; subst. apply (ps_closed_guard_exact d); assumption.
Qed.

(** Exactness is conditional on successful compilation. The compiler is
    intentionally incomplete for general open symbolic comparisons. *)
Theorem ps_compile_exact : forall C D,
  ps_constraint_wf C -> ps_compile C = Some D ->
  forall sigma, models sigma D <-> ps_models sigma C.
Proof.
  induction C as [D0|C1 IH1 C2 IH2|d E F]; intros D Hwf Hcompile sigma; simpl in *.
  - inversion Hcompile; subst. reflexivity.
  - destruct Hwf as [H1 H2].
    destruct (ps_compile C1) as [D1|] eqn:HC1; try discriminate.
    destruct (ps_compile C2) as [D2|] eqn:HC2; try discriminate.
    inversion Hcompile; subst. rewrite models_and_iff.
    rewrite (IH1 D1 H1 eq_refl sigma), (IH2 D2 H2 eq_refl sigma). reflexivity.
  - destruct Hwf as [HE HF]. eapply ps_compile_guard_exact; eauto.
Qed.

Theorem ps_compile_separable : forall C D,
  ps_compile C = Some D -> compatibility_fragment D.
Proof.
  intros C D _. induction D; constructor; assumption.
Qed.

Inductive ps_solver_result : Type :=
| Solved (sigma : size_assignment)
| Unsatisfiable
| Unresolved.

Definition ps_final_constraint eta E B D := CAnd D (ps_root eta E B).

Definition ps_solve eta E B C : ps_solver_result :=
  match ps_compile C with
  | None => Unresolved
  | Some D =>
      let final := ps_final_constraint eta E B D in
      if solver_succeeds final then Solved (solved_assignment final)
      else Unsatisfiable
  end.

Lemma ps_final_exact : forall d E eta B C D sigma,
  ps_scoped d E -> ps_environment d eta -> 0 <= B ->
  ps_constraint_wf C -> ps_compile C = Some D ->
  (models sigma (ps_final_constraint eta E B D) <->
   ps_models sigma C /\ required_bandwidth (ps_eval sigma eta E) <= B).
Proof.
  intros d E eta B C D sigma HE Heta HB HC Hcompile.
  unfold ps_final_constraint. rewrite models_and_iff.
  rewrite (ps_compile_exact C D HC Hcompile sigma).
  rewrite (ps_root_exact d E eta sigma B HE Heta HB). reflexivity.
Qed.

Theorem ps_solve_sound : forall d E eta B C sigma,
  ps_scoped d E -> ps_environment d eta -> 0 <= B -> ps_constraint_wf C ->
  ps_solve eta E B C = Solved sigma ->
  ps_models sigma C /\ required_bandwidth (ps_eval sigma eta E) <= B.
Proof.
  intros d E eta B C sigma HE Heta HB HC Hsolve.
  unfold ps_solve in Hsolve. destruct (ps_compile C) as [D|] eqn:Hcompile;
    try discriminate.
  destruct (solver_succeeds (ps_final_constraint eta E B D)) eqn:Hs;
    try discriminate. inversion Hsolve; subst.
  apply (proj1 (ps_final_exact d E eta B C D _ HE Heta HB HC Hcompile)).
  apply solver_succeeds_sound. exact Hs.
Qed.

Theorem ps_solve_complete : forall d E eta B C D,
  ps_scoped d E -> ps_environment d eta -> 0 <= B ->
  ps_constraint_wf C -> ps_compile C = Some D ->
  ((exists sigma, ps_solve eta E B C = Solved sigma) <->
   exists sigma, ps_models sigma C /\ required_bandwidth (ps_eval sigma eta E) <= B).
Proof.
  intros d E eta B C D HE Heta HB HC Hcompile. split.
  - intros [sigma Hsolve]. exists sigma. eapply ps_solve_sound; eauto.
  - intros [sigma Hmodel].
    pose proof (proj2 (ps_final_exact d E eta B C D sigma HE Heta HB HC Hcompile)
      Hmodel) as Hnumeric.
    pose proof (solver_complete _ sigma Hnumeric) as Hsuccess.
    exists (solved_assignment (ps_final_constraint eta E B D)).
    unfold ps_solve. rewrite Hcompile, Hsuccess. reflexivity.
Qed.

Theorem ps_solve_unsatisfiable : forall d E eta B C,
  ps_scoped d E -> ps_environment d eta -> 0 <= B -> ps_constraint_wf C ->
  ps_solve eta E B C = Unsatisfiable ->
  ~ exists sigma, ps_models sigma C /\ required_bandwidth (ps_eval sigma eta E) <= B.
Proof.
  intros d E eta B C HE Heta HB HC Hsolve [sigma Hmodel].
  unfold ps_solve in Hsolve. destruct (ps_compile C) as [D|] eqn:Hcompile;
    try discriminate.
  destruct (solver_succeeds (ps_final_constraint eta E B D)) eqn:Hsuccess;
    try discriminate.
  pose proof (proj2 (ps_final_exact d E eta B C D sigma HE Heta HB HC Hcompile)
    Hmodel) as Hnumeric.
  pose proof (solver_complete _ sigma Hnumeric) as Htrue. congruence.
Qed.

Theorem ps_solve_unresolved : forall eta E B C,
  ps_solve eta E B C = Unresolved <-> ps_compile C = None.
Proof.
  intros eta E B C. unfold ps_solve. destruct (ps_compile C) as [D|];
    [destruct (solver_succeeds _)|]; split; intro H; try discriminate; reflexivity.
Qed.

(** Maximality is on variables mentioned by the final numeric constraints.
    Download caps ensure that generated source variables belong to that set. *)
Theorem ps_solve_maximal : forall d E eta B C D sigma_star,
  ps_scoped d E -> ps_environment d eta -> 0 <= B -> ps_constraint_wf C ->
  ps_compile C = Some D -> ps_solve eta E B C = Solved sigma_star ->
  forall sigma a,
    ps_models sigma C -> required_bandwidth (ps_eval sigma eta E) <= B ->
    In a (constraint_variables (ps_final_constraint eta E B D)) ->
    sigma a <= sigma_star a.
Proof.
  intros d E eta B C D sigma_star HE Heta HB HC Hcompile Hsolve sigma a Hlocal Hroot Hin.
  unfold ps_solve in Hsolve. rewrite Hcompile in Hsolve.
  destruct (solver_succeeds (ps_final_constraint eta E B D)) eqn:Hsuccess;
    try discriminate. inversion Hsolve; subst.
  eapply solver_succeeds_greatest; [exact Hsuccess| |exact Hin].
  apply (proj2 (ps_final_exact d E eta B C D sigma HE Heta HB HC Hcompile)).
  split; assumption.
Qed.

(** A one-sided open join retains precisely its guaranteed concrete bound.
    The general empty-environment compiler now covers this case. *)
Theorem ps_unknown_join_contract : forall sigma a t Phi,
  ps_guard_models sigma 1 (PSESize a t) (PSEJoin (PSEVar 0) (PSELiteral Phi)) <->
  [Obligation (sigma a / t) 1] ≼ Phi.
Proof.
  intros sigma a t Phi. split.
  - intro H. exact (H ps_empty_environment (ps_empty_environment_wf 1)).
  - intros H eta Heta. simpl. eapply effect_le_trans; [exact H|apply effect_le_join_r].
Qed.

Theorem ps_bare_effect_parameter_cannot_cover_download : forall sigma a t,
  ~ ps_guard_models sigma 1 (PSESize a t) (PSEVar 0).
Proof.
  intros sigma a t H.
  specialize (H ps_empty_environment (ps_empty_environment_wf 1)).
  destruct (H (Obligation (sigma a / t) 1) (or_introl eq_refl)) as [q [Hin _]].
  inversion Hin.
Qed.

Example ps_open_reflexivity_compiles :
  ps_compile (LGuard 1 (PSEVar 0) (PSEVar 0)) = Some CTop.
Proof. reflexivity. Qed.

Example ps_parallel_forwarding_compiles :
  ps_compile (LGuard 1 (PSEVar 0) (PSEPar (PSEVar 0) (PSEVar 0))) = Some CTop.
Proof. reflexivity. Qed.

Example ps_empty_simplification_compiles :
  ps_compile (LGuard 1 (PSEPar (PSEVar 0) ps_empty) (PSEVar 0)) = Some CTop.
Proof. reflexivity. Qed.

Definition ps_timeout_two : positive_rational.
Proof. refine (PositiveRational 2 _). reflexivity. Defined.

Example ps_numerical_contract_bound :
  ps_compile (LGuard 0 (PSESize 0%nat ps_timeout_two) (PSELiteral [Obligation 5 1])) =
  Some (CAnd (CUpper 0%nat (2 * 5)) CTop).
Proof. reflexivity. Qed.

Example ps_open_join_compiles :
  ps_compile (LGuard 1 (PSESize 0%nat ps_timeout_two)
    (PSEJoin (PSEVar 0) (PSELiteral [Obligation 5 1]))) =
  Some (CAnd (CUpper 0%nat (2 * 5)) CTop).
Proof. reflexivity. Qed.

Example ps_empty_contract_unsatisfiable :
  ps_solve ps_empty_environment ps_empty 10
    (LGuard 0 (PSESize 0%nat ps_timeout_two) ps_empty) = Unsatisfiable.
Proof. reflexivity. Qed.

Example ps_bare_parameter_unsatisfiable :
  ps_solve (fun _ => [Obligation 100 1]) ps_empty 10
    (LGuard 1 (PSESize 0%nat ps_timeout_two) (PSEVar 0)) = Unsatisfiable.
Proof. reflexivity. Qed.

Example ps_open_source_remains_unresolved :
  ps_solve ps_empty_environment ps_empty 10
    (LGuard 2 (PSEVar 0) (PSEVar 1)) = Unresolved.
Proof. reflexivity. Qed.

(** Explicit download caps survive successful compilation, so maximality can
    later be stated for all source download variables, including suspended
    bodies whose downloads are absent from the root effect. *)
Fixpoint ps_numeric_variables C : list size_variable :=
  match C with
  | LNumeric D => constraint_variables D
  | LAnd C1 C2 => ps_numeric_variables C1 ++ ps_numeric_variables C2
  | LGuard _ _ _ => []
  end.

Theorem ps_compile_retains_numeric_variables : forall C D,
  ps_compile C = Some D -> forall a,
  In a (ps_numeric_variables C) -> In a (constraint_variables D).
Proof.
  induction C as [D0|C1 IH1 C2 IH2|d E F]; intros D Hcompile a Hin; simpl in *.
  - inversion Hcompile; subst. exact Hin.
  - destruct (ps_compile C1) as [D1|] eqn:H1; try discriminate.
    destruct (ps_compile C2) as [D2|] eqn:H2; try discriminate.
    inversion Hcompile; subst. simpl. apply in_app_or in Hin. apply in_or_app.
    destruct Hin; [left; eapply IH1|right; eapply IH2]; eauto.
  - contradiction.
Qed.

(** Constraint generation normalizes both operands before invoking the partial
    compiler. This can expose numerical subtrees without changing the scope
    or weakening universal satisfaction. *)
Fixpoint ps_constraint_norm C : local_constraint :=
  match C with
  | LNumeric D => LNumeric D
  | LAnd C D => LAnd (ps_constraint_norm C) (ps_constraint_norm D)
  | LGuard d E F => LGuard d (ps_norm E) (ps_norm F)
  end.

Theorem ps_constraint_norm_models : forall C sigma,
  ps_models sigma (ps_constraint_norm C) <-> ps_models sigma C.
Proof.
  induction C as [D|C IHC D IHD|d E F]; intros sigma; simpl; try tauto.
  - rewrite IHC, IHD. reflexivity.
  - split; intros H eta Heta;
      destruct (ps_norm_eval E sigma eta) as [HE HE'];
      destruct (ps_norm_eval F sigma eta) as [HF HF'];
      specialize (H eta Heta).
    + eapply effect_le_trans; [exact HE'|].
      eapply effect_le_trans; [exact H|exact HF].
    + eapply effect_le_trans; [exact HE|].
      eapply effect_le_trans; [exact H|exact HF'].
Qed.

Theorem ps_constraint_norm_wf : forall C,
  ps_constraint_wf C -> ps_constraint_wf (ps_constraint_norm C).
Proof.
  induction C; simpl.
  - auto.
  - intros [H1 H2]. split; auto.
  - intros [HE HF]. split; apply ps_norm_scoped; assumption.
Qed.

Lemma ps_constraint_norm_variables : forall C,
  ps_numeric_variables (ps_constraint_norm C) = ps_numeric_variables C.
Proof. induction C; simpl; congruence. Qed.
