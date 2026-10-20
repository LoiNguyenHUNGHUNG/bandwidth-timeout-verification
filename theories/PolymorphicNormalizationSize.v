(** Parallel regrouping does not grow effect syntax. The cost counts every
    AST node and every concrete literal pair; numeric payloads are atomic.
    Adding one to this cost makes binary composition additive. *)
From Stdlib Require Import Arith Lia List.
From BandwidthTimeout Require Import Effects Normalization Typing
  PolymorphicEffects PolymorphicSymbolic.
Import ListNotations.
Local Open Scope nat_scope.

Definition literal_mass (Phi : effect) : nat :=
  match Phi with [] => 0 | _ => 2 + length Phi end.

Lemma literal_mass_parallel : forall Phi Psi,
  literal_mass (parallel_effect Phi Psi) <= literal_mass Phi + literal_mass Psi.
Proof.
  intros [|p Phi] [|q Psi]; [reflexivity| | |];
    pose proof parallel_effect_length_le as Hlen.
  - specialize (Hlen [] (q :: Psi)).
    destruct (parallel_effect [] (q :: Psi)); cbn [literal_mass] in *; simpl in *; lia.
  - specialize (Hlen (p :: Phi) []).
    destruct (parallel_effect (p :: Phi) []); cbn [literal_mass] in *; simpl in *; lia.
  - specialize (Hlen (p :: Phi) (q :: Psi)).
    destruct (parallel_effect (p :: Phi) (q :: Psi)); cbn [literal_mass] in *; simpl in *; lia.
Qed.

Fixpoint eff_mass E : nat :=
  match E with
  | EffLit Phi => 2 + length Phi
  | EffVar _ => 2
  | EffJoin E F | EffPar E F => eff_mass E + eff_mass F
  end.

Fixpoint eff_syntax_size E : nat :=
  match E with
  | EffLit Phi => 1 + length Phi
  | EffVar _ => 1
  | EffJoin E F | EffPar E F => 1 + eff_syntax_size E + eff_syntax_size F
  end.

Lemma eff_mass_size : forall E, eff_mass E = S (eff_syntax_size E).
Proof. induction E; cbn [eff_mass eff_syntax_size]; lia. Qed.
Lemma eff_mass_positive : forall E, 2 <= eff_mass E.
Proof. induction E; cbn [eff_mass]; lia. Qed.

Definition eff_list_mass Es := fold_right (fun E n => eff_mass E + n) 0 Es.
Lemma eff_list_mass_app : forall Es Fs,
  eff_list_mass (Es ++ Fs) = eff_list_mass Es + eff_list_mass Fs.
Proof.
  intros Es Fs. unfold eff_list_mass. rewrite fold_right_app.
  induction Es; simpl; lia.
Qed.
Lemma eff_list_mass_cons : forall E Es, 2 <= eff_list_mass (E :: Es).
Proof. intros. pose proof (eff_mass_positive E). cbn [eff_list_mass fold_right]. lia. Qed.

Lemma eff_join_node_mass : forall E F,
  eff_mass (eff_join_node E F) <= eff_mass E + eff_mass F.
Proof.
  intros E F. destruct E as [Phi|i|E1 E2|E1 E2], F as [Psi|j|F1 F2|F1 F2];
    cbn [eff_join_node]; try destruct Phi; try destruct Psi;
    cbn [eff_mass]; try lia.
  all: match goal with
       | |- context [sequential_effect ?A ?B] =>
           pose proof (sequential_effect_length_le A B)
       end; simpl in *; lia.
Qed.

Lemma eff_par_node_mass : forall E F,
  eff_mass (eff_par_node E F) <= eff_mass E + eff_mass F.
Proof.
  intros E F. destruct E as [Phi|i|E1 E2|E1 E2], F as [Psi|j|F1 F2|F1 F2];
    cbn [eff_par_node]; try destruct Phi; try destruct Psi;
    cbn [eff_mass]; try lia.
  all: match goal with
       | |- context [parallel_effect ?A ?B] =>
           pose proof (parallel_effect_length_le A B)
       end; simpl in *; lia.
Qed.

Lemma eff_par_node_empty_r : forall E, eff_par_node E (EffLit []) = E.
Proof. destruct E; cbn [eff_par_node]; try destruct e; reflexivity. Qed.

Lemma eff_par_list_mass : forall Es,
  eff_mass (eff_par_list Es) <= Nat.max 2 (eff_list_mass Es).
Proof.
  induction Es as [|E Es IH].
  - reflexivity.
  - destruct Es as [|F Fs].
    + cbn [eff_par_list fold_right]. rewrite eff_par_node_empty_r.
      pose proof (eff_mass_positive E). cbn [eff_list_mass fold_right]. lia.
    + change (eff_mass (eff_par_node E (eff_par_list (F :: Fs))) <=
        Nat.max 2 (eff_mass E + eff_list_mass (F :: Fs))).
      pose proof (eff_par_node_mass E (eff_par_list (F :: Fs))).
      pose proof (eff_list_mass_cons F Fs). lia.
Qed.

Lemma eff_par_collect_mass : forall E,
  let '(Phi, Es) := eff_par_collect E in
  literal_mass Phi + eff_list_mass Es <= eff_mass E.
Proof.
  induction E; cbn [eff_par_collect].
  - destruct e; cbn [literal_mass eff_list_mass eff_mass]; simpl; lia.
  - cbn [literal_mass eff_list_mass eff_mass]. simpl. lia.
  - cbn [literal_mass eff_list_mass eff_mass]. simpl. lia.
  - destruct (eff_par_collect E1) as [Phi Es].
    destruct (eff_par_collect E2) as [Psi Fs].
    rewrite eff_list_mass_app. pose proof (literal_mass_parallel Phi Psi).
    cbn [eff_mass]. lia.
Qed.

Lemma eff_par_rebuild_mass : forall Phi Es,
  eff_mass (eff_par_rebuild Phi Es) <=
    Nat.max 2 (literal_mass Phi + eff_list_mass Es).
Proof.
  intros [|p Phi] Es.
  - unfold eff_par_rebuild. cbn [eff_par_node literal_mass].
    apply eff_par_list_mass.
  - destruct Es as [|E Es].
    + unfold eff_par_rebuild. cbn [eff_par_list fold_right].
      rewrite eff_par_node_empty_r. cbn [eff_mass literal_mass eff_list_mass]. lia.
    + unfold eff_par_rebuild.
      pose proof (eff_par_node_mass (EffLit (p :: Phi)) (eff_par_list (E :: Es))).
      pose proof (eff_par_list_mass (E :: Es)).
      pose proof (eff_list_mass_cons E Es).
      cbn [eff_mass literal_mass] in *. lia.
Qed.

Lemma eff_par_regroup_mass : forall E F,
  eff_mass (eff_par_regroup E F) <= eff_mass E + eff_mass F.
Proof.
  intros E F.
  pose proof (eff_par_collect_mass (EffPar E F)) as Hcollect.
  unfold eff_par_regroup.
  destruct (eff_par_collect (EffPar E F)) as [Phi Es].
  pose proof (eff_par_rebuild_mass Phi Es).
  pose proof (eff_mass_positive E). pose proof (eff_mass_positive F).
  cbn [eff_mass] in Hcollect. lia.
Qed.

Theorem eff_norm_mass_le : forall E, eff_mass (eff_norm E) <= eff_mass E.
Proof.
  induction E; cbn [eff_norm].
  - pose proof (normalize_length_le e). cbn [eff_mass]. lia.
  - reflexivity.
  - pose proof (eff_join_node_mass (eff_norm E1) (eff_norm E2)).
    cbn [eff_mass]. lia.
  - pose proof (eff_par_regroup_mass (eff_norm E1) (eff_norm E2)).
    cbn [eff_mass]. lia.
Qed.

Theorem eff_norm_size_le : forall E,
  eff_syntax_size (eff_norm E) <= eff_syntax_size E.
Proof. intro E. pose proof (eff_norm_mass_le E). rewrite !eff_mass_size in H. lia. Qed.

(** Unknown size singletons are single syntax nodes, just like parameters.
    Their identifiers and rational timeouts are atomic numeric payloads. *)
Fixpoint ps_mass E : nat :=
  match E with
  | PSELiteral Phi => 2 + length Phi
  | PSESize _ _ | PSEVar _ => 2
  | PSEJoin E F | PSEPar E F => ps_mass E + ps_mass F
  end.

Fixpoint ps_syntax_size E : nat :=
  match E with
  | PSELiteral Phi => 1 + length Phi
  | PSESize _ _ | PSEVar _ => 1
  | PSEJoin E F | PSEPar E F => 1 + ps_syntax_size E + ps_syntax_size F
  end.

Lemma ps_mass_size : forall E, ps_mass E = S (ps_syntax_size E).
Proof. induction E; cbn [ps_mass ps_syntax_size]; lia. Qed.
Lemma ps_mass_positive : forall E, 2 <= ps_mass E.
Proof. induction E; cbn [ps_mass]; lia. Qed.

Definition ps_list_mass Es := fold_right (fun E n => ps_mass E + n) 0 Es.
Lemma ps_list_mass_app : forall Es Fs,
  ps_list_mass (Es ++ Fs) = ps_list_mass Es + ps_list_mass Fs.
Proof.
  intros Es Fs. unfold ps_list_mass. rewrite fold_right_app.
  induction Es; simpl; lia.
Qed.
Lemma ps_list_mass_cons : forall E Es, 2 <= ps_list_mass (E :: Es).
Proof. intros. pose proof (ps_mass_positive E). cbn [ps_list_mass fold_right]. lia. Qed.

Lemma ps_norm_join_mass : forall E F,
  ps_mass (ps_norm_join E F) <= ps_mass E + ps_mass F.
Proof.
  intros E F.
  destruct E as [Phi|a t|i|E1 E2|E1 E2], F as [Psi|b u|j|F1 F2|F1 F2];
    cbn [ps_norm_join ps_simpl_join]; try destruct Phi; try destruct Psi;
    cbn [ps_mass]; try lia.
  all: match goal with
       | |- context [sequential_effect ?A ?B] =>
           pose proof (sequential_effect_length_le A B)
       end; simpl in *; lia.
Qed.

Lemma ps_simpl_par_mass : forall E F,
  ps_mass (ps_simpl_par E F) <= ps_mass E + ps_mass F.
Proof.
  intros E F.
  destruct E as [Phi|a t|i|E1 E2|E1 E2], F as [Psi|b u|j|F1 F2|F1 F2];
    cbn [ps_simpl_par]; try destruct Phi; try destruct Psi;
    cbn [ps_mass]; lia.
Qed.

Lemma ps_simpl_par_empty_r : forall E, ps_simpl_par E ps_empty = E.
Proof. destruct E; cbn [ps_simpl_par ps_empty]; try destruct Phi; reflexivity. Qed.

Lemma ps_par_list_mass : forall Es,
  ps_mass (ps_par_list Es) <= Nat.max 2 (ps_list_mass Es).
Proof.
  induction Es as [|E Es IH].
  - reflexivity.
  - destruct Es as [|F Fs].
    + cbn [ps_par_list fold_right]. rewrite ps_simpl_par_empty_r.
      pose proof (ps_mass_positive E). cbn [ps_list_mass fold_right]. lia.
    + change (ps_mass (ps_simpl_par E (ps_par_list (F :: Fs))) <=
        Nat.max 2 (ps_mass E + ps_list_mass (F :: Fs))).
      pose proof (ps_simpl_par_mass E (ps_par_list (F :: Fs))).
      pose proof (ps_list_mass_cons F Fs). lia.
Qed.

Lemma ps_par_collect_mass : forall E,
  let '(Phi, Es) := ps_par_collect E in
  literal_mass Phi + ps_list_mass Es <= ps_mass E.
Proof.
  induction E; cbn [ps_par_collect].
  - destruct Phi; cbn [literal_mass ps_list_mass ps_mass]; simpl; lia.
  - cbn [literal_mass ps_list_mass ps_mass]. simpl. lia.
  - cbn [literal_mass ps_list_mass ps_mass]. simpl. lia.
  - cbn [literal_mass ps_list_mass ps_mass]. simpl. lia.
  - destruct (ps_par_collect E1) as [Phi Es].
    destruct (ps_par_collect E2) as [Psi Fs].
    rewrite ps_list_mass_app. pose proof (literal_mass_parallel Phi Psi).
    cbn [ps_mass]. lia.
Qed.

Lemma ps_par_rebuild_mass : forall Phi Es,
  ps_mass (ps_par_rebuild Phi Es) <=
    Nat.max 2 (literal_mass Phi + ps_list_mass Es).
Proof.
  intros [|p Phi] Es.
  - unfold ps_par_rebuild. cbn [ps_simpl_par literal_mass].
    apply ps_par_list_mass.
  - destruct Es as [|E Es].
    + unfold ps_par_rebuild. cbn [ps_par_list fold_right].
      rewrite ps_simpl_par_empty_r. cbn [ps_mass literal_mass ps_list_mass]. lia.
    + unfold ps_par_rebuild.
      pose proof (ps_simpl_par_mass (PSELiteral (p :: Phi)) (ps_par_list (E :: Es))).
      pose proof (ps_par_list_mass (E :: Es)).
      pose proof (ps_list_mass_cons E Es).
      cbn [ps_mass literal_mass] in *. lia.
Qed.

Lemma ps_par_regroup_mass : forall E F,
  ps_mass (ps_par_regroup E F) <= ps_mass E + ps_mass F.
Proof.
  intros E F.
  pose proof (ps_par_collect_mass (PSEPar E F)) as Hcollect.
  unfold ps_par_regroup.
  destruct (ps_par_collect (PSEPar E F)) as [Phi Es].
  pose proof (ps_par_rebuild_mass Phi Es).
  pose proof (ps_mass_positive E). pose proof (ps_mass_positive F).
  cbn [ps_mass] in Hcollect. lia.
Qed.

Theorem ps_norm_mass_le : forall E, ps_mass (ps_norm E) <= ps_mass E.
Proof.
  induction E; cbn [ps_norm].
  - pose proof (normalize_length_le Phi). cbn [ps_mass]. lia.
  - reflexivity.
  - reflexivity.
  - pose proof (ps_norm_join_mass (ps_norm E1) (ps_norm E2)).
    cbn [ps_mass]. lia.
  - pose proof (ps_par_regroup_mass (ps_norm E1) (ps_norm E2)).
    cbn [ps_mass]. lia.
Qed.

Theorem ps_norm_size_le : forall E,
  ps_syntax_size (ps_norm E) <= ps_syntax_size E.
Proof. intro E. pose proof (ps_norm_mass_le E). rewrite !ps_mass_size in H. lia. Qed.
