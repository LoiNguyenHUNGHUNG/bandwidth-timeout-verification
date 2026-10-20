(** Inferred polymorphic types, exact compatibility, and conservative merges.
    Size variables occur in inferred effects, while source annotations and
    explicit effect arguments are embedded from the size-free core grammar. *)
From Stdlib Require Import Arith Bool Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Bandwidth
  Typing Merging SizeInference PolymorphicEffects PolymorphicSyntax
  PolymorphicTypeSubstitution PolymorphicSymbolic PolymorphicConstraints.
Import ListNotations.
Local Open Scope nat_scope.

Inductive pst_type : Type :=
| PSTyUnit | PSTyNat
| PSTyArrow : pst_type -> ps_effect -> pst_type -> pst_type
| PSTyProduct : list pst_type -> pst_type
| PSTyForall : pst_type -> ps_effect -> pst_type.

Fixpoint pst_instantiate (sigma : size_assignment) (T : pst_type) : poly_ty :=
  match T with
  | PSTyUnit => PTUnit | PSTyNat => PTNat
  | PSTyArrow A E B => PTArrow (pst_instantiate sigma A)
      (ps_instantiate sigma E) (pst_instantiate sigma B)
  | PSTyProduct Ts => PTProduct (map (pst_instantiate sigma) Ts)
  | PSTyForall T E => PTForall (pst_instantiate sigma T) (ps_instantiate sigma E)
  end.

Fixpoint pst_embed (T : poly_ty) : pst_type :=
  match T with
  | PTUnit => PSTyUnit | PTNat => PSTyNat
  | PTArrow A E B => PSTyArrow (pst_embed A) (ps_embed E) (pst_embed B)
  | PTProduct Ts => PSTyProduct (map pst_embed Ts)
  | PTForall T E => PSTyForall (pst_embed T) (ps_embed E)
  end.

Fixpoint pst_subst (s : nat -> open_effect) (T : pst_type) : pst_type :=
  match T with
  | PSTyUnit => PSTyUnit | PSTyNat => PSTyNat
  | PSTyArrow A E B => PSTyArrow (pst_subst s A) (ps_subst s E) (pst_subst s B)
  | PSTyProduct Ts => PSTyProduct (map (pst_subst s) Ts)
  | PSTyForall T E => PSTyForall (pst_subst (eff_up_subst s) T)
      (ps_subst (eff_up_subst s) E)
  end.

Fixpoint pst_scoped (d : nat) (T : pst_type) {struct T} : Prop :=
  match T with
  | PSTyUnit | PSTyNat => True
  | PSTyArrow A E B => pst_scoped d A /\ ps_scoped d E /\ pst_scoped d B
  | PSTyProduct Ts =>
      let fix go Ts := match Ts with [] => True | T :: Ts => pst_scoped d T /\ go Ts end
      in go Ts
  | PSTyForall T E => pst_scoped (S d) T /\ ps_scoped (S d) E
  end.

Lemma pst_instantiate_embed : forall T sigma,
  pst_instantiate sigma (pst_embed T) = T.
Proof.
  fix IH 1. intros T sigma. destruct T; simpl; try reflexivity; f_equal;
    auto using ps_instantiate_embed.
  rewrite map_map. induction l; simpl; f_equal; auto.
Qed.

Lemma pst_instantiate_subst : forall T sigma s,
  pst_instantiate sigma (pst_subst s T) = poly_ty_subst s (pst_instantiate sigma T).
Proof.
  fix IH 1. intros T sigma s. destruct T; simpl; try reflexivity; f_equal;
    auto using ps_instantiate_subst.
  rewrite !map_map. induction l; simpl; f_equal; auto.
Qed.

Lemma pst_instantiate_scoped : forall T d sigma,
  pst_scoped d T -> poly_ty_wf d (pst_instantiate sigma T).
Proof.
  fix IH 1. intros T d sigma H. destruct T; simpl in *.
  - constructor.
  - constructor.
  - destruct H as [HA [HE HB]]. constructor; auto using ps_instantiate_scoped.
  - constructor. induction l; simpl in *; [constructor|].
    destruct H. constructor; auto.
  - destruct H. constructor; auto using ps_instantiate_scoped.
Qed.

Lemma pst_embed_scoped : forall T d,
  poly_ty_wf d T -> pst_scoped d (pst_embed T).
Proof.
  fix IH 1. intros T d H. destruct T; inversion H; subst; simpl; auto.
  - repeat split; eauto using ps_embed_scoped.
  - clear H. match goal with HT : Forall _ l |- _ => revert HT end.
    induction l; intro HT; inversion HT; subst; simpl; auto.
    split; [apply IH; assumption | apply IHl; assumption].
  - split; eauto using ps_embed_scoped.
Qed.

Fixpoint pst_subtype_constraint_go (d : nat) (forward : bool)
    (T U : pst_type) {struct T} : local_constraint :=
  match T, U with
  | PSTyUnit, PSTyUnit | PSTyNat, PSTyNat => LNumeric CTop
  | PSTyArrow A E B, PSTyArrow A' F B' =>
      LAnd (pst_subtype_constraint_go d (negb forward) A A')
        (LAnd (if forward then LGuard d E F else LGuard d F E)
          (pst_subtype_constraint_go d forward B B'))
  | PSTyProduct Ts, PSTyProduct Us =>
      let fix go Ts Us {struct Ts} :=
        match Ts, Us with
        | [], [] => LNumeric CTop
        | T :: Ts, U :: Us => LAnd (pst_subtype_constraint_go d forward T U) (go Ts Us)
        | _, _ => LNumeric CBottom
        end in go Ts Us
  | PSTyForall T E, PSTyForall U F =>
      LAnd (pst_subtype_constraint_go (S d) forward T U)
        (if forward then LGuard (S d) E F else LGuard (S d) F E)
  | _, _ => LNumeric CBottom
  end.

Definition pst_subtype_constraint d T U := pst_subtype_constraint_go d true T U.

Lemma poly_subtype_product_iff : forall d Ts Us,
  poly_subtype d (PTProduct Ts) (PTProduct Us) <-> Forall2 (poly_subtype d) Ts Us.
Proof. split; [apply poly_subtype_product_inv | constructor; assumption]. Qed.

Lemma pst_subtype_constraint_go_exact : forall T d U forward sigma,
  ps_models sigma (pst_subtype_constraint_go d forward T U) <->
  if forward then poly_subtype d (pst_instantiate sigma T) (pst_instantiate sigma U)
  else poly_subtype d (pst_instantiate sigma U) (pst_instantiate sigma T).
Proof.
  fix IH 1. intros T d U forward sigma.
  destruct T as [| |A E B|Ts|T E]; destruct U as [| |A' F B'|Us|U F];
    destruct forward; simpl;
    try (split; [contradiction | intro H; inversion H]);
    try (split; [intro H; constructor | intro H; exact I]).
  - rewrite (IH A d A' false sigma), (IH B d B' true sigma), ps_guard_core_exact.
    split; [intros [HA [HE HB]]; constructor; assumption |].
    intro H; inversion H; subst; auto.
  - rewrite (IH A d A' true sigma), (IH B d B' false sigma), ps_guard_core_exact.
    split; [intros [HA [HE HB]]; constructor; assumption |].
    intro H; inversion H; subst; auto.
  - rewrite poly_subtype_product_iff.
    revert Us. induction Ts as [|T Ts IHTs]; intros [|U Us]; simpl.
    + split; [intro; constructor|intro; exact I].
    + split; [contradiction|intro H; inversion H].
    + split; [contradiction|intro H; inversion H].
    + rewrite (IH T d U true sigma), IHTs.
      split; [intros [H1 H2]; constructor; assumption | intro H; inversion H; auto].
  - rewrite poly_subtype_product_iff.
    revert Us. induction Ts as [|T Ts IHTs]; intros [|U Us]; simpl.
    + split; [intro; constructor|intro; exact I].
    + split; [contradiction|intro H; inversion H].
    + split; [contradiction|intro H; inversion H].
    + rewrite (IH T d U false sigma), IHTs.
      split; [intros [H1 H2]; constructor; assumption | intro H; inversion H; auto].
  - rewrite (IH T (S d) U true sigma), ps_guard_core_exact.
    split; [intros [H1 H2]; constructor; assumption | intro H; inversion H; auto].
  - rewrite (IH T (S d) U false sigma), ps_guard_core_exact.
    split; [intros [H1 H2]; constructor; assumption | intro H; inversion H; auto].
Qed.

Theorem pst_subtype_constraint_exact : forall d T U sigma,
  ps_models sigma (pst_subtype_constraint d T U) <->
  poly_subtype d (pst_instantiate sigma T) (pst_instantiate sigma U).
Proof. intros. apply (pst_subtype_constraint_go_exact T d U true sigma). Qed.

Lemma pst_subtype_constraint_go_wf : forall T d U forward,
  pst_scoped d T -> pst_scoped d U ->
  ps_constraint_wf (pst_subtype_constraint_go d forward T U).
Proof.
  fix IH 1. intros T d U forward HT HU.
  destruct T as [| |A E B|Ts|T E]; destruct U as [| |A' F B'|Us|U F];
    simpl in *; auto.
  - destruct HT as [HA [HE HB]], HU as [HA' [HF HB']].
    repeat split; try (eapply IH; eauto). destruct forward; simpl; auto.
  - revert Us HU. induction Ts; intros [|U Us] HU; simpl in *; auto.
    destruct HT as [HT HTs], HU as [HU HUs]. split; eauto.
  - destruct HT as [HT HE], HU as [HU HF].
    split; [eapply IH; eauto|destruct forward; simpl; auto].
Qed.

Theorem pst_subtype_constraint_wf : forall d T U,
  pst_scoped d T -> pst_scoped d U -> ps_constraint_wf (pst_subtype_constraint d T U).
Proof. intros. apply pst_subtype_constraint_go_wf; assumption. Qed.

Fixpoint pst_norm (T : pst_type) : pst_type :=
  match T with
  | PSTyUnit => PSTyUnit | PSTyNat => PSTyNat
  | PSTyArrow A E B => PSTyArrow (pst_norm A) (ps_norm E) (pst_norm B)
  | PSTyProduct Ts => PSTyProduct (map pst_norm Ts)
  | PSTyForall T E => PSTyForall (pst_norm T) (ps_norm E)
  end.

Lemma pst_norm_scoped : forall T d, pst_scoped d T -> pst_scoped d (pst_norm T).
Proof.
  fix IH 1. intros T d H. destruct T; simpl in *; auto.
  - destruct H as [H1 [H2 H3]]. repeat split; auto using ps_norm_scoped.
  - induction l; simpl in *; auto. destruct H. split;
      [apply IH; assumption | apply IHl; assumption].
  - destruct H. split; auto using ps_norm_scoped.
Qed.

Theorem pst_norm_instantiate : forall T d sigma,
  poly_subtype d (pst_instantiate sigma (pst_norm T)) (pst_instantiate sigma T) /\
  poly_subtype d (pst_instantiate sigma T) (pst_instantiate sigma (pst_norm T)).
Proof.
  fix IH 1. intros T d sigma. destruct T; simpl.
  - split; constructor.
  - split; constructor.
  - destruct (IH T1 d sigma), (IH T2 d sigma).
    destruct (ps_norm_core_equiv d p sigma). split; constructor; assumption.
  - rewrite map_map. assert (H :
      Forall2 (poly_subtype d) (map (fun T => pst_instantiate sigma (pst_norm T)) l)
        (map (pst_instantiate sigma) l) /\
      Forall2 (poly_subtype d) (map (pst_instantiate sigma) l)
        (map (fun T => pst_instantiate sigma (pst_norm T)) l)).
    { induction l; simpl; [split; constructor|].
      destruct IHl, (IH a d sigma). split; constructor; assumption. }
    destruct H. split; constructor; assumption.
  - destruct (IH T (S d) sigma), (ps_norm_core_equiv (S d) p sigma).
    split; constructor; assumption.
Qed.

Lemma pst_effect_scope_reflect : forall E d sigma,
  eff_scoped d (ps_instantiate sigma E) -> ps_scoped d E.
Proof.
  induction E; intros d sigma H; inversion H; subst; simpl; eauto.
Qed.

Lemma pst_scope_reflect : forall T d sigma,
  poly_ty_wf d (pst_instantiate sigma T) -> pst_scoped d T.
Proof.
  fix IH 1. intros T d sigma H. destruct T; inversion H; subst; simpl; auto.
  - repeat split; eauto using pst_effect_scope_reflect.
  - clear H. match goal with HT : Forall _ (map _ l) |- _ => revert HT end.
    induction l; intros HT; inversion HT; subst; simpl; auto.
    split; [eapply IH; eassumption | apply IHl; assumption].
  - split; eauto using pst_effect_scope_reflect.
Qed.

(** Conservative structural meet: no greatest-lower-bound claim for open
    effects or different size variables. *)
Fixpoint ps_meet (E F : ps_effect) : ps_effect :=
  match E, F with
  | PSELiteral Phi, PSELiteral Psi => PSELiteral (effect_meet Phi Psi)
  | PSESize a t, PSESize b u =>
      if Nat.eqb a b && Qeq_bool t u then E else ps_empty
  | PSEVar i, PSEVar j => if Nat.eqb i j then E else ps_empty
  | PSEJoin E1 E2, PSEJoin F1 F2 => PSEJoin (ps_meet E1 F1) (ps_meet E2 F2)
  | PSEPar E1 E2, PSEPar F1 F2 => PSEPar (ps_meet E1 F1) (ps_meet E2 F2)
  | _, _ => ps_empty
  end.

Lemma ps_meet_raw_bounds : forall E F sigma eta,
  ps_eval_raw sigma eta (ps_meet E F) ≼ ps_eval_raw sigma eta E /\
  ps_eval_raw sigma eta (ps_meet E F) ≼ ps_eval_raw sigma eta F.
Proof.
  induction E; intros F sigma eta; destruct F; simpl;
    try (split; apply empty_effect_le).
  - split; auto using effect_meet_le_left, effect_meet_le_right.
  - destruct (Nat.eqb a a0 && Qeq_bool timeout timeout0) eqn:H; simpl;
      [split|split; apply empty_effect_le].
    + apply effect_le_refl.
    + apply (ps_atom_sound (PSESize a timeout) (PSESize a0 timeout0) sigma eta); exact H.
  - destruct (Nat.eqb index index0) eqn:H; simpl;
      [split|split; apply empty_effect_le].
    + apply effect_le_refl.
    + apply (ps_atom_sound (PSEVar index) (PSEVar index0) sigma eta); exact H.
  - destruct (IHE1 F1 sigma eta), (IHE2 F2 sigma eta).
    split; apply join_mono; assumption.
  - destruct (IHE1 F1 sigma eta), (IHE2 F2 sigma eta).
    split; apply parallel_mono; assumption.
Qed.

Lemma ps_meet_bounds : forall E F sigma d,
  eff_le d (ps_instantiate sigma (ps_meet E F)) (ps_instantiate sigma E) /\
  eff_le d (ps_instantiate sigma (ps_meet E F)) (ps_instantiate sigma F).
Proof.
  intros E F sigma d; split; apply ps_guard_core_exact;
    intros eta Heta; apply ps_meet_raw_bounds.
Qed.

Lemma ps_meet_scoped : forall E F d,
  ps_scoped d E -> ps_scoped d F -> ps_scoped d (ps_meet E F).
Proof.
  induction E; intros F d HE HF; destruct F; simpl in *;
    try (constructor; fail).
  - apply effect_meet_wf; assumption.
  - destruct (Nat.eqb a a0 && Qeq_bool timeout timeout0); simpl; auto; constructor.
  - destruct (Nat.eqb index index0); simpl; auto; constructor.
  - destruct HE, HF. split; eauto.
  - destruct HE, HF. split; eauto.
Qed.

Fixpoint pst_merge (joining : bool) (T U : pst_type) {struct T} : option pst_type :=
  match T, U with
  | PSTyUnit, PSTyUnit => Some PSTyUnit
  | PSTyNat, PSTyNat => Some PSTyNat
  | PSTyArrow A E B, PSTyArrow A' F B' =>
      match pst_merge (negb joining) A A', pst_merge joining B B' with
      | Some D, Some R => Some (PSTyArrow D
          (if joining then PSEJoin E F else ps_meet E F) R)
      | _, _ => None
      end
  | PSTyProduct Ts, PSTyProduct Us =>
      let fix go Ts Us {struct Ts} :=
        match Ts, Us with
        | [], [] => Some []
        | T :: Ts, U :: Us =>
            match pst_merge joining T U, go Ts Us with
            | Some V, Some Vs => Some (V :: Vs)
            | _, _ => None
            end
        | _, _ => None
        end in
      match go Ts Us with Some Vs => Some (PSTyProduct Vs) | None => None end
  | PSTyForall T E, PSTyForall U F =>
      match pst_merge joining T U with
      | Some V => Some (PSTyForall V
          (if joining then PSEJoin E F else ps_meet E F))
      | None => None
      end
  | _, _ => None
  end.

Definition pst_join T U := pst_merge true T U.
Definition pst_meet T U := pst_merge false T U.

Definition pst_merge_list (joining : bool) :=
  fix go (Ts Us : list pst_type) {struct Ts} : option (list pst_type) :=
  match Ts, Us with
  | [], [] => Some []
  | T :: Ts, U :: Us =>
      match pst_merge joining T U, go Ts Us with
      | Some V, Some Vs => Some (V :: Vs)
      | _, _ => None
      end
  | _, _ => None
  end.

Definition pst_bound (joining : bool) sigma d T V : Prop :=
  if joining then poly_subtype d (pst_instantiate sigma T) (pst_instantiate sigma V)
  else poly_subtype d (pst_instantiate sigma V) (pst_instantiate sigma T).

Lemma pst_product_bound : forall joining sigma d Ts Vs,
  Forall2 (pst_bound joining sigma d) Ts Vs ->
  pst_bound joining sigma d (PSTyProduct Ts) (PSTyProduct Vs).
Proof.
  intros joining sigma d Ts Vs H. destruct joining; simpl; constructor;
    induction H; simpl; constructor; auto.
Qed.

Theorem pst_merge_sound : forall T U joining V d sigma,
  pst_merge joining T U = Some V ->
  pst_bound joining sigma d T V /\ pst_bound joining sigma d U V.
Proof.
  fix IH 1. intros T U joining V d sigma Hmerge.
  destruct T as [| |A E B|Ts|T E]; destruct U as [| |A' F B'|Us|U F];
    simpl in Hmerge; try discriminate.
  - inversion Hmerge; subst. destruct joining; split; constructor.
  - inversion Hmerge; subst. destruct joining; split; constructor.
  - destruct (pst_merge (negb joining) A A') as [D|] eqn:HD; try discriminate.
    destruct (pst_merge joining B B') as [R|] eqn:HR; try discriminate.
    inversion Hmerge; subst.
    destruct (IH A A' (negb joining) D d sigma HD) as [HA HA'].
    destruct (IH B B' joining R d sigma HR) as [HB HB'].
    destruct joining; simpl in *.
    + split; constructor; auto using eff_le_join_l, eff_le_join_r.
    + destruct (ps_meet_bounds E F sigma d). split; constructor; assumption.
  - change (match pst_merge_list joining Ts Us with
      Some Vs => Some (PSTyProduct Vs) | None => None end = Some V) in Hmerge.
    destruct (pst_merge_list joining Ts Us) as [Vs|] eqn:Hlist; try discriminate.
    inversion Hmerge; subst.
    assert (HC : forall Us Vs, pst_merge_list joining Ts Us = Some Vs ->
      Forall2 (pst_bound joining sigma d) Ts Vs /\
      Forall2 (pst_bound joining sigma d) Us Vs).
    { clear Hlist Hmerge Us Vs. induction Ts as [|T Ts IHTs];
        intros [|U Us] Vs Hgo; simpl in Hgo; try discriminate.
      - inversion Hgo; subst; split; constructor.
      - destruct (pst_merge joining T U) as [V|] eqn:HV; try discriminate.
        destruct (pst_merge_list joining Ts Us) as [Vs'|] eqn:HVs; try discriminate.
        inversion Hgo; subst.
        destruct (IH T U joining V d sigma HV).
        destruct (IHTs Us Vs' HVs). split; constructor; assumption. }
    destruct (HC Us Vs Hlist). split; apply pst_product_bound; assumption.
  - destruct (pst_merge joining T U) as [R|] eqn:HR; try discriminate.
    inversion Hmerge; subst.
    destruct (IH T U joining R (S d) sigma HR).
    destruct joining; simpl in *.
    + split; constructor; auto using eff_le_join_l, eff_le_join_r.
    + destruct (ps_meet_bounds E F sigma (S d)); split; constructor; assumption.
Qed.

Corollary pst_join_sound : forall T U V d sigma,
  pst_join T U = Some V ->
  poly_subtype d (pst_instantiate sigma T) (pst_instantiate sigma V) /\
  poly_subtype d (pst_instantiate sigma U) (pst_instantiate sigma V).
Proof. intros; apply (pst_merge_sound T U true V d sigma); assumption. Qed.

Corollary pst_meet_sound : forall T U V d sigma,
  pst_meet T U = Some V ->
  poly_subtype d (pst_instantiate sigma V) (pst_instantiate sigma T) /\
  poly_subtype d (pst_instantiate sigma V) (pst_instantiate sigma U).
Proof. intros; apply (pst_merge_sound T U false V d sigma); assumption. Qed.

Theorem pst_merge_scoped : forall T U joining V d,
  pst_merge joining T U = Some V -> pst_scoped d T -> pst_scoped d U ->
  pst_scoped d V.
Proof.
  fix IH 1. intros T U joining V d Hmerge HT HU.
  destruct T as [| |A E B|Ts|T E]; destruct U as [| |A' F B'|Us|U F];
    simpl in Hmerge; try discriminate; simpl in HT, HU.
  - inversion Hmerge; subst; exact I.
  - inversion Hmerge; subst; exact I.
  - destruct (pst_merge (negb joining) A A') as [D|] eqn:HD; try discriminate.
    destruct (pst_merge joining B B') as [R|] eqn:HR; try discriminate.
    inversion Hmerge; subst; simpl.
    destruct HT as [HA [HE HB]], HU as [HA' [HF HB']].
    split; [eapply IH; eauto|]. split; [|eapply IH; eauto].
    destruct joining; simpl; auto using ps_meet_scoped.
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
    split; [eapply IH; eauto|]. destruct joining; simpl; auto using ps_meet_scoped.
Qed.

(** Regression witnesses for the manuscript's explicit limitations. *)
Example ps_permuted_join_meet_empty :
  ps_norm (ps_meet (PSEJoin (PSEVar 0) (PSEVar 1))
    (PSEJoin (PSEVar 1) (PSEVar 0))) = ps_empty.
Proof. reflexivity. Qed.

Lemma ps_join_commutative : forall sigma d E F,
  ps_guard_models sigma d (PSEJoin E F) (PSEJoin F E).
Proof.
  intros sigma d E F eta Heta p Hin. simpl in *. unfold join in *.
  exists p. split; [apply in_app_iff in Hin; apply in_app_iff; tauto|].
  apply obligation_le_refl.
Qed.

Definition pst_nonempty_environment (i : nat) : effect :=
  match i with 0 => [Obligation 1%Q 1] | _ => [] end.

Lemma pst_nonempty_environment_wf : ps_environment 2 pst_nonempty_environment.
Proof.
  intros [|i] Hi; simpl; constructor; [|constructor].
  unfold obligation_wf; simpl; discriminate.
Qed.

Theorem ps_structural_meet_not_greatest : forall sigma,
  ps_guard_models sigma 2 (PSEJoin (PSEVar 0) (PSEVar 1))
    (PSEJoin (PSEVar 1) (PSEVar 0)) /\
  ~ ps_guard_models sigma 2 (PSEJoin (PSEVar 0) (PSEVar 1))
    (ps_meet (PSEJoin (PSEVar 0) (PSEVar 1))
      (PSEJoin (PSEVar 1) (PSEVar 0))).
Proof.
  intro sigma; split; [apply ps_join_commutative|].
  intro H. specialize (H pst_nonempty_environment pst_nonempty_environment_wf).
  destruct (H (Obligation 1%Q 1) (or_introl eq_refl)) as [p [Hp _]].
  inversion Hp.
Qed.

Definition pst_timeout_one : positive_rational.
Proof. refine (PositiveRational 1%Q _); reflexivity. Defined.
Definition pst_one_assignment : size_assignment := fun _ => checked_size_bound 1%Q.

Example ps_meet_before_size_assignment :
  ps_instantiate pst_one_assignment
    (ps_meet (PSESize 0 pst_timeout_one) (PSESize 1 pst_timeout_one)) = EffLit [].
Proof. reflexivity. Qed.

Example ps_meet_after_size_assignment :
  ps_meet
    (ps_embed (ps_instantiate pst_one_assignment (PSESize 0 pst_timeout_one)))
    (ps_embed (ps_instantiate pst_one_assignment (PSESize 1 pst_timeout_one))) =
  PSELiteral [Obligation 1%Q 1].
Proof. reflexivity. Qed.
