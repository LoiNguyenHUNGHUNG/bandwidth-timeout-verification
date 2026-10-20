(** Regression examples for explicit polymorphism, delayed effects, and
    independent term/effect binders.  These are proofs about the language
    judgments and reduction relation, not evaluations of unverified code. *)
From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Quantities Effects Normalization Bandwidth
  Syntax Typing PolymorphicEffects PolymorphicSyntax PolymorphicTypeSubstitution
  PolymorphicTyping PolymorphicSemantics PolymorphicActiveWF PolymorphicPreservation PolymorphicSafety
  SizeInference PolymorphicSymbolic PolymorphicConstraints
  PolymorphicInferenceTypes PolymorphicInference PolymorphicInferenceSafety.
Import ListNotations.
Open Scope Q_scope.

Definition poly_size_10 : nonnegative_rational.
Proof. refine (NonnegativeRational 10 _). vm_compute. discriminate. Defined.
Definition poly_size_6 : nonnegative_rational.
Proof. refine (NonnegativeRational 6 _). vm_compute. discriminate. Defined.
Definition poly_timeout_2 : positive_rational.
Proof. refine (PositiveRational 2 _). vm_compute. reflexivity. Defined.
Definition poly_rate5 := EffLit [Obligation 5 1].
Definition poly_rate3 := EffLit [Obligation 3 1].
Definition poly_empty := EffLit [].

Lemma poly_le_drop_empty : forall d E, eff_le d (EffJoin poly_empty E) E.
Proof. intros d E eta Heta. simpl. apply sequential_empty_l. Qed.
Lemma poly_rate5_scoped : forall d, eff_scoped d poly_rate5.
Proof. intros. repeat constructor. vm_compute. discriminate. Qed.
Lemma poly_rate3_scoped : forall d, eff_scoped d poly_rate3.
Proof. intros. repeat constructor. vm_compute. discriminate. Qed.

(** The paper's effect-polymorphic callback invoker. *)
Definition poly_invoke : poly_expr :=
  PEAbsEff (PELambda (PTArrow PTUnit (EffVar 0) PTUnit)
    (PEApp (PEVar 0) PEUnit)).
Definition poly_invoke_type : poly_ty :=
  PTForall
    (PTArrow (PTArrow PTUnit (EffVar 0) PTUnit) (EffVar 0) PTUnit)
    poly_empty.
Lemma poly_invoke_type_wf : forall d, poly_ty_wf d poly_invoke_type.
Proof. intros; unfold poly_invoke_type, poly_empty. repeat (first [solve [lia] | constructor]). Qed.
Example poly_invoke_typed : forall d Gamma,
  poly_context_wf d Gamma ->
  poly_has_type d Gamma poly_invoke poly_invoke_type poly_empty.
Proof.
  intros d Gamma HG. unfold poly_invoke, poly_invoke_type, poly_empty.
  apply PHTAbsEff; auto. apply PHTAbs.
  - repeat (first [solve [lia] | constructor]).
  - eapply PHTSub with (E := EffJoin (EffLit []) (EffJoin (EffLit []) (EffVar 0)))
      (T := PTUnit).
    + eapply PHTApp.
      * apply PHTVar; [reflexivity|repeat (first [solve [lia] | constructor])].
      * constructor.
    + constructor.
    + eapply eff_le_trans; apply poly_le_drop_empty.
    + constructor.
    + constructor. lia.
Qed.
Example poly_invoke_closed : poly_closed_source poly_invoke.
Proof.
  unfold poly_closed_source, poly_invoke. split; repeat (first [solve [lia] | constructor]).
Qed.
Definition poly_download5 := PEDownload poly_size_10 poly_timeout_2.
Definition poly_callback5 := PELambda PTUnit poly_download5.
Lemma poly_download5_typed : forall d Gamma,
  poly_has_type d Gamma poly_download5 PTUnit poly_rate5.
Proof.
  intros. eapply PHTSub with (E := EffLit (download_effect poly_size_10 poly_timeout_2))
    (T := PTUnit).
  - constructor.
  - constructor.
  - intros eta Heta. simpl. intros p Hp. destruct Hp as [Hp|Hp]; [subst p|contradiction].
    exists (Obligation 5 1). split; [left; reflexivity|].
    split; simpl; vm_compute; (reflexivity || discriminate).
  - constructor.
  - apply poly_rate5_scoped.
Qed.
Lemma poly_callback5_typed : forall d Gamma,
  poly_has_type d Gamma poly_callback5 (PTArrow PTUnit poly_rate5 PTUnit) poly_empty.
Proof. intros. apply PHTAbs; [constructor|apply poly_download5_typed]. Qed.
Definition poly_invoke5 := PEApp (PEAppEff poly_invoke poly_rate5) poly_callback5.
Definition poly_invoke_effect F :=
  EffJoin (EffJoin poly_empty poly_empty) (EffJoin poly_empty F).
Example poly_invoke5_typed :
  poly_has_type 0 [] poly_invoke5 PTUnit (poly_invoke_effect poly_rate5).
Proof.
  unfold poly_invoke5, poly_invoke_effect. eapply PHTApp with
    (A := PTArrow PTUnit poly_rate5 PTUnit) (G := poly_rate5).
  - change (poly_has_type 0 [] (PEAppEff poly_invoke poly_rate5)
      (poly_ty_subst0 poly_rate5
        (PTArrow (PTArrow PTUnit (EffVar 0) PTUnit) (EffVar 0) PTUnit))
      (EffJoin poly_empty (eff_subst (eff_single poly_rate5) poly_empty))).
    apply PHTAppEff; [apply poly_invoke_typed; constructor|apply poly_rate5_scoped].
  - apply poly_callback5_typed.
Qed.
Example poly_invoke5_requires5 :
  required_bandwidth (eff_eval (fun _ => []) (poly_invoke_effect poly_rate5)) == 5.
Proof. vm_compute. reflexivity. Qed.
Example poly_invoke5_closed : poly_closed_source poly_invoke5.
Proof.
  unfold poly_closed_source, poly_invoke5, poly_invoke, poly_callback5,
    poly_download5, poly_rate5. split; repeat (first [solve [lia] | constructor]);
    vm_compute; discriminate.
Qed.

(** Abstraction delays downloads even if its body is not a value. *)
Definition poly_suspended := PEAbsEff poly_download5.
Example poly_suspended_empty_effect :
  poly_has_type 0 [] poly_suspended (PTForall PTUnit poly_rate5) poly_empty.
Proof. apply PHTAbsEff; [constructor|apply poly_download5_typed]. Qed.
Example poly_suspended_no_step : forall B k target,
  ~ poly_step B (PolyConfig poly_suspended k) target.
Proof. intros. apply poly_value_no_step. constructor. Qed.
Example poly_suspended_application_charges5 :
  poly_has_type 0 [] (PEAppEff poly_suspended poly_empty) PTUnit
    (EffJoin poly_empty poly_rate5).
Proof.
  change (poly_has_type 0 [] (PEAppEff poly_suspended poly_empty)
    (poly_ty_subst0 poly_empty PTUnit)
    (EffJoin poly_empty (eff_subst (eff_single poly_empty) poly_rate5))).
  apply PHTAppEff; [apply poly_suspended_empty_effect|repeat constructor].
Qed.
Example poly_suspended_beta_counter : forall B k,
  poly_step B (PolyConfig (PEAppEff poly_suspended poly_empty) k)
    (PolyConfig poly_download5 k).
Proof. intros. apply PolyStepEffectBeta. Qed.
Example poly_suspended_download_starts : forall B k,
  poly_step B (PolyConfig poly_download5 k)
    (PolyConfig (PERunning poly_size_10 poly_timeout_2) (S k)).
Proof. intros; constructor. Qed.

(** The inner binder is forwarded to an effect application; closing the
    outer binder never captures that inner variable. *)
Definition poly_forward := PEAbsEff (PEAppEff poly_invoke (EffVar 0)).
Example poly_forward_typed :
  poly_has_type 0 [] poly_forward
    (PTForall
      (PTArrow (PTArrow PTUnit (EffVar 0) PTUnit) (EffVar 0) PTUnit)
      (EffJoin poly_empty poly_empty)) poly_empty.
Proof.
  apply PHTAbsEff; [constructor|].
  change (poly_has_type 1 [] (PEAppEff poly_invoke (EffVar 0))
    (poly_ty_subst0 (EffVar 0)
      (PTArrow (PTArrow PTUnit (EffVar 0) PTUnit) (EffVar 0) PTUnit))
    (EffJoin poly_empty (eff_subst (eff_single (EffVar 0)) poly_empty))).
  apply PHTAppEff; [apply poly_invoke_typed; constructor|constructor; lia].
Qed.
Example poly_forward_beta : forall B k,
  poly_step B (PolyConfig (PEAppEff poly_forward poly_rate5) k)
    (PolyConfig (PEAppEff poly_invoke poly_rate5) k).
Proof. intros. apply PolyStepEffectBeta. Qed.

(** A single let-bound polymorphic value supports distinct effect arguments. *)
Definition poly_two_instantiations :=
  PELet poly_invoke
    (PEParallel [PEAppEff (PEVar 0) poly_rate5; PEAppEff (PEVar 0) poly_rate3]).
Definition poly_instantiated_type F := PTArrow (PTArrow PTUnit F PTUnit) F PTUnit.
Example poly_two_instantiations_typed :
  poly_has_type 0 [] poly_two_instantiations
    (PTProduct [poly_instantiated_type poly_rate5; poly_instantiated_type poly_rate3])
    (EffJoin poly_empty
      (poly_parallel_effects [EffJoin poly_empty poly_empty; EffJoin poly_empty poly_empty])).
Proof.
  unfold poly_two_instantiations. eapply PHTLet.
  - apply poly_invoke_typed. constructor.
  - apply PHTParallel. apply PHTCons.
    + change (poly_has_type 0 [poly_invoke_type] (PEAppEff (PEVar 0) poly_rate5)
        (poly_ty_subst0 poly_rate5
          (PTArrow (PTArrow PTUnit (EffVar 0) PTUnit) (EffVar 0) PTUnit))
        (EffJoin poly_empty (eff_subst (eff_single poly_rate5) poly_empty))).
      apply PHTAppEff; [apply PHTVar; [reflexivity|apply poly_invoke_type_wf]|apply poly_rate5_scoped].
    + apply PHTCons.
      * change (poly_has_type 0 [poly_invoke_type] (PEAppEff (PEVar 0) poly_rate3)
          (poly_ty_subst0 poly_rate3
            (PTArrow (PTArrow PTUnit (EffVar 0) PTUnit) (EffVar 0) PTUnit))
          (EffJoin poly_empty (eff_subst (eff_single poly_rate3) poly_empty))).
        apply PHTAppEff; [apply PHTVar; [reflexivity|apply poly_invoke_type_wf]|apply poly_rate3_scoped].
      * constructor.
Qed.
Example poly_two_instantiations_cost_zero :
  required_bandwidth (eff_eval (fun _ => [])
    (EffJoin poly_empty
      (poly_parallel_effects [EffJoin poly_empty poly_empty; EffJoin poly_empty poly_empty]))) == 0.
Proof. reflexivity. Qed.

(** Universal effect entailment may not replace a variable by empty, even
    though the empty instantiation would make that one comparison pass. *)
Example poly_variable_not_below_empty : ~ eff_le 1 (EffVar 0) poly_empty.
Proof.
  intro H. specialize (H (fun _ => [Obligation 5 1])).
  assert (eff_environment 1 (fun _ => [Obligation 5 1])) as Henv.
  { intros i Hi. repeat constructor. vm_compute. discriminate. }
  specialize (H Henv (Obligation 5 1) (or_introl eq_refl)).
  destruct H as [p [Hp _]]. contradiction.
Qed.
Example poly_rate5_not_below3 : ~ eff_le 0 poly_rate5 poly_rate3.
Proof.
  intro H. specialize (H (fun _ => [])).
  assert (eff_environment 0 (fun _ => [])) as Henv by (intros i Hi; lia).
  specialize (H Henv (Obligation 5 1) (or_introl eq_refl)).
  destruct H as [p [Hp [Hr Hn]]]. destruct Hp as [Hp|Hp]; [subst p|contradiction].
  vm_compute in Hr. apply Hr. reflexivity.
Qed.

Example poly_bad_effect_application_shape : forall F T E,
  ~ poly_has_type 0 [] (PEAppEff PEUnit F) T E.
Proof.
  intros F T E H.
  destruct (poly_app_eff_generation _ _ _ _ _ _ H)
    as (U & G & E0 & Hu & _).
  destruct (poly_typing_generation _ _ _ _ _ Hu)
    as (U0 & G0 & Hr & Hsub & He).
  inversion Hr; subst. inversion Hsub.
Qed.
Example poly_unbound_effect_argument_rejected : forall T E,
  ~ poly_has_type 0 [] (PEAppEff poly_invoke (EffVar 0)) T E.
Proof.
  intros T E H.
  destruct (poly_app_eff_generation _ _ _ _ _ _ H)
    as (U & G & E0 & Hu & HF & _).
  inversion HF. lia.
Qed.

Definition poly_download3 := PEDownload poly_size_6 poly_timeout_2.
Definition poly_callback3 := PELambda PTUnit poly_download3.
Lemma poly_callback3_typed : forall d Gamma,
  poly_has_type d Gamma poly_callback3 (PTArrow PTUnit poly_rate3 PTUnit) poly_empty.
Proof.
  intros. apply PHTAbs; [constructor|].
  eapply PHTSub with (E := EffLit (download_effect poly_size_6 poly_timeout_2))
    (T := PTUnit).
  - constructor.
  - constructor.
  - intros eta Heta. simpl. intros p Hp. destruct Hp as [Hp|Hp]; [subst p|contradiction].
    exists (Obligation 3 1). split; [left; reflexivity|].
    split; simpl; vm_compute; (reflexivity || discriminate).
  - constructor.
  - apply poly_rate3_scoped.
Qed.
Lemma poly_bound_invoke_typed : forall F,
  eff_scoped 0 F ->
  poly_has_type 0 [poly_invoke_type] (PEAppEff (PEVar 0) F)
    (poly_instantiated_type F) (EffJoin poly_empty poly_empty).
Proof.
  intros F HF.
  change (poly_has_type 0 [poly_invoke_type] (PEAppEff (PEVar 0) F)
    (poly_ty_subst0 F
      (PTArrow (PTArrow PTUnit (EffVar 0) PTUnit) (EffVar 0) PTUnit))
    (EffJoin poly_empty (eff_subst (eff_single F) poly_empty))).
  apply PHTAppEff; [apply PHTVar; [reflexivity|apply poly_invoke_type_wf]|auto].
Qed.
Definition poly_parallel_reuse :=
  PELet poly_invoke (PEParallel
    [PEApp (PEAppEff (PEVar 0) poly_rate5) poly_callback5;
     PEApp (PEAppEff (PEVar 0) poly_rate3) poly_callback3]).
Definition poly_parallel_reuse_effect :=
  EffJoin poly_empty (poly_parallel_effects
    [poly_invoke_effect poly_rate5; poly_invoke_effect poly_rate3]).
Example poly_parallel_reuse_typed :
  poly_has_type 0 [] poly_parallel_reuse (PTProduct [PTUnit; PTUnit])
    poly_parallel_reuse_effect.
Proof.
  unfold poly_parallel_reuse, poly_parallel_reuse_effect. eapply PHTLet.
  - apply poly_invoke_typed. constructor.
  - apply PHTParallel. apply PHTCons.
    + eapply PHTApp with (A := PTArrow PTUnit poly_rate5 PTUnit).
      * apply poly_bound_invoke_typed. apply poly_rate5_scoped.
      * apply poly_callback5_typed.
    + apply PHTCons.
      * eapply PHTApp with (A := PTArrow PTUnit poly_rate3 PTUnit).
        -- apply poly_bound_invoke_typed. apply poly_rate3_scoped.
        -- apply poly_callback3_typed.
      * constructor.
Qed.
Example poly_parallel_reuse_requires10 :
  required_bandwidth (eff_eval (fun _ => []) poly_parallel_reuse_effect) == 10.
Proof. vm_compute. reflexivity. Qed.
Example poly_parallel_reuse_closed : poly_closed_source poly_parallel_reuse.
Proof.
  unfold poly_closed_source, poly_parallel_reuse, poly_invoke, poly_callback5,
    poly_download5, poly_callback3, poly_download3, poly_rate5, poly_rate3.
  split; repeat (first [solve [lia] | constructor]); vm_compute; discriminate.
Qed.

(** End-to-end safety checks use the new polymorphic runtime theorem. *)
Example poly_invoke5_safe :
  ~ exists target active,
    poly_successful_steps 5 poly_invoke5 0 target active /\
    poly_step 5 (PolyConfig target active) PolyError.
Proof.
  eapply poly_bandwidth_safety.
  - exact (proj1 poly_invoke5_closed).
  - apply poly_invoke5_typed.
  - rewrite poly_invoke5_requires5. apply Qle_refl.
Qed.
Example poly_parallel_reuse_safe :
  ~ exists target active,
    poly_successful_steps 10 poly_parallel_reuse 0 target active /\
    poly_step 10 (PolyConfig target active) PolyError.
Proof.
  eapply poly_bandwidth_safety.
  - exact (proj1 poly_parallel_reuse_closed).
  - apply poly_parallel_reuse_typed.
  - rewrite poly_parallel_reuse_requires10. apply Qle_refl.
Qed.
Example poly_suspended_application_safe :
  ~ exists target active,
    poly_successful_steps 5 (PEAppEff poly_suspended poly_empty) 0 target active /\
    poly_step 5 (PolyConfig target active) PolyError.
Proof.
  eapply poly_bandwidth_safety.
  - unfold poly_suspended, poly_download5. repeat constructor.
  - apply poly_suspended_application_charges5.
  - vm_compute. discriminate.
Qed.

(** Executable symbolic regression: a callback contract a/2 <= 5 produces
    a <= 10, combines it with the download cap and root budget, and feeds
    exactly those generated constraints to the verified solver. *)
Definition pi_example_invoke :=
  PIEAbsEff (PIELambda (PTArrow PTUnit (EffVar 0) PTUnit)
    (PIEApp (PIEVar 0) PIEUnit)).
Definition pi_example_invoke_type :=
  PSTyForall
    (PSTyArrow (PSTyArrow PSTyUnit (PSEVar 0) PSTyUnit) (PSEVar 0) PSTyUnit)
    ps_empty.
Definition pi_example_invoke_constraint :=
  LAnd (LNumeric CTop) (LAnd (LNumeric CTop) (LNumeric CTop)).
Lemma pi_example_invoke_infers : forall M d Gamma,
  pi_context_wf d Gamma ->
  pi_infers M d Gamma pi_example_invoke pi_example_invoke_type ps_empty
    pi_example_invoke_constraint.
Proof.
  intros M d Gamma HG. apply PIIAbsEff; auto. apply PIIAbs.
  - repeat (first [solve [lia] | constructor]).
  - change (pi_infers M (S d)
      (pst_embed (PTArrow PTUnit (EffVar 0) PTUnit) :: pi_context_shift Gamma)
      (PIEApp (PIEVar 0) PIEUnit) PSTyUnit
      (ps_norm (PSEJoin ps_empty (PSEJoin ps_empty (PSEVar 0))))
      (LAnd (LNumeric CTop) (LAnd (LNumeric CTop)
        (ps_constraint_norm (pst_subtype_constraint (S d) PSTyUnit PSTyUnit))))).
    eapply PIIApp.
    + apply PIIVar; [reflexivity|]. simpl. repeat split; lia.
    + constructor.
Qed.
Definition pi_example_callback := PIELambda PTUnit (PIEDownload 0%nat poly_timeout_2).
Definition pi_example := PIEApp (PIEAppEff pi_example_invoke poly_rate5) pi_example_callback.
Definition pi_example_effect := PSELiteral [Obligation 5 1].
Definition pi_example_comparison := pst_subtype_constraint 0
  (PSTyArrow PSTyUnit (PSESize 0%nat poly_timeout_2) PSTyUnit)
  (PSTyArrow PSTyUnit pi_example_effect PSTyUnit).
Definition pi_example_constraint M :=
  LAnd pi_example_invoke_constraint
    (LAnd (LNumeric (CUpper 0%nat M)) (ps_constraint_norm pi_example_comparison)).
Example pi_example_generated : forall M,
  pi_infers M 0 [] pi_example PSTyUnit pi_example_effect (pi_example_constraint M).
Proof.
  intro M. unfold pi_example, pi_example_constraint, pi_example_comparison.
  change (pi_infers M 0 []
    (PIEApp (PIEAppEff pi_example_invoke poly_rate5) pi_example_callback)
    PSTyUnit (ps_norm (PSEJoin ps_empty (PSEJoin ps_empty pi_example_effect)))
    (LAnd pi_example_invoke_constraint (LAnd (LNumeric (CUpper 0%nat M))
      (ps_constraint_norm (pst_subtype_constraint 0
        (PSTyArrow PSTyUnit (PSESize 0%nat poly_timeout_2) PSTyUnit)
        (PSTyArrow PSTyUnit pi_example_effect PSTyUnit)))))).
  eapply PIIApp with (A := PSTyArrow PSTyUnit pi_example_effect PSTyUnit).
  - change (pi_infers M 0 [] (PIEAppEff pi_example_invoke poly_rate5)
      (pst_norm (pst_subst (eff_single poly_rate5)
        (PSTyArrow (PSTyArrow PSTyUnit (PSEVar 0) PSTyUnit) (PSEVar 0) PSTyUnit)))
      (ps_norm (PSEJoin ps_empty (ps_subst (eff_single poly_rate5) ps_empty)))
      pi_example_invoke_constraint).
    apply PIIAppEff; [apply pi_example_invoke_infers; constructor|apply poly_rate5_scoped].
  - apply PIIAbs; [constructor|constructor].
Qed.
Example pi_example_local_bound :
  ps_compile_guard (PSESize 0%nat poly_timeout_2) pi_example_effect =
    Some (CAnd (CUpper 0%nat 10) CTop).
Proof. vm_compute. reflexivity. Qed.
Definition pi_example_numeric M : constraint :=
  match ps_compile (pi_example_constraint M) with Some D => D | None => CBottom end.
Definition pi_example_final M B :=
  ps_final_constraint ps_empty_environment pi_example_effect B (pi_example_numeric M).
Definition pi_example_assignment M B := solved_assignment (pi_example_final M B).
Example pi_example_compilation_succeeds : forall M,
  ps_compile (pi_example_constraint M) = Some (pi_example_numeric M).
Proof. intro M. reflexivity. Qed.
Example pi_example_solver_returns_assignment :
  ps_solve ps_empty_environment pi_example_effect 5 (pi_example_constraint 100) =
    Solved (pi_example_assignment 100 5).
Proof. reflexivity. Qed.
Example pi_example_inferred_maximum_is10 : pi_example_assignment 100 5 0%nat == 10.
Proof. vm_compute. reflexivity. Qed.
Example pi_example_cap_can_bind : pi_example_assignment 8 5 0%nat == 8.
Proof. vm_compute. reflexivity. Qed.
Example pi_example_root_rejects_insufficient_bandwidth :
  ps_solve ps_empty_environment pi_example_effect 4 (pi_example_constraint 100) =
    Unsatisfiable.
Proof. reflexivity. Qed.

(** Equal rational timeout values are accepted even when their rational
    representations differ. *)
Definition poly_timeout_4_over_2 : positive_rational.
Proof. refine (PositiveRational (4#2) _). vm_compute. reflexivity. Defined.
Example ps_atom_timeout_equality_is_numeric :
  ps_atom (PSESize 0%nat poly_timeout_2) (PSESize 0%nat poly_timeout_4_over_2) = true.
Proof. reflexivity. Qed.

(** Normalizing compatibility guards matters to the partial compiler. *)
Definition ps_nested_concrete :=
  PSEPar (PSEVar 0)
    (PSEPar (PSELiteral [Obligation 1 1]) (PSELiteral [Obligation 1 1])).
Definition ps_folded_concrete := PSEPar (PSEVar 0) (PSELiteral [Obligation 1 2]).
Example ps_raw_guard_is_unresolved :
  ps_compile (LGuard 1 ps_nested_concrete ps_folded_concrete) = None.
Proof. reflexivity. Qed.
Example ps_normalized_guard_compiles :
  ps_compile (ps_constraint_norm (LGuard 1 ps_nested_concrete ps_folded_concrete)) = Some CTop.
Proof. reflexivity. Qed.

(** A local callback comparison is generated under the new effect binder.
    Its scope survives both abstraction and explicit instantiation; a root
    closing assignment cannot specialize away this universal obligation. *)
Definition pi_scoped_body :=
  PIEApp (PIELambda (PTArrow PTUnit (EffVar 0) PTUnit) PIEUnit)
    pi_example_callback.
Definition pi_scoped_suspension := PIEAbsEff pi_scoped_body.
Definition pi_scoped_constraint :=
  LAnd (LNumeric CTop) (LAnd (LNumeric (CUpper 0%nat 100))
    (ps_constraint_norm (pst_subtype_constraint 1
      (PSTyArrow PSTyUnit (PSESize 0%nat poly_timeout_2) PSTyUnit)
      (PSTyArrow PSTyUnit (PSEVar 0) PSTyUnit)))).
Example pi_scoped_suspension_generated :
  pi_infers 100 0 [] pi_scoped_suspension (PSTyForall PSTyUnit ps_empty)
    ps_empty pi_scoped_constraint.
Proof.
  apply PIIAbsEff; [constructor|].
  change (pi_infers 100 1 [] pi_scoped_body PSTyUnit
    (ps_norm (PSEJoin ps_empty (PSEJoin ps_empty ps_empty))) pi_scoped_constraint).
  eapply PIIApp with (A := PSTyArrow PSTyUnit (PSEVar 0) PSTyUnit).
  - apply PIIAbs; [repeat (first [solve [lia] | constructor])|constructor].
  - apply PIIAbs; [constructor|constructor].
Qed.
Example pi_scoped_application_retains_constraint :
  pi_infers 100 0 [] (PIEAppEff pi_scoped_suspension poly_rate5)
    PSTyUnit ps_empty pi_scoped_constraint.
Proof.
  change (pi_infers 100 0 [] (PIEAppEff pi_scoped_suspension poly_rate5)
    (pst_norm (pst_subst (eff_single poly_rate5) PSTyUnit))
    (ps_norm (PSEJoin ps_empty (ps_subst (eff_single poly_rate5) ps_empty)))
    pi_scoped_constraint).
  apply PIIAppEff; [apply pi_scoped_suspension_generated|apply poly_rate5_scoped].
Qed.
Example pi_scoped_guard_is_retained :
  ps_compile pi_scoped_constraint =
    Some (CAnd CTop (CAnd (CUpper 0%nat 100)
      (CAnd CTop (CAnd CBottom CTop)))).
Proof. reflexivity. Qed.
Example pi_root_assignment_cannot_discharge_local_binder : forall eta B,
  ps_solve eta ps_empty B pi_scoped_constraint = Unsatisfiable.
Proof. reflexivity. Qed.

Example pi_example_inferred_program_safe :
  ~ exists target active,
    poly_successful_steps 5
      (pi_instantiate (pi_example_assignment 100 5) pi_example) 0 target active /\
    poly_step 5 (PolyConfig target active) PolyError.
Proof.
  destruct (pi_solved_program_safe 100 pi_example PSTyUnit pi_example_effect
    (pi_example_constraint 100) 5 (pi_example_assignment 100 5))
    as [_ [_ [_ Hsafe]]].
  - vm_compute. discriminate.
  - apply pi_example_generated.
  - apply pi_example_solver_returns_assignment.
  - exact Hsafe.
Qed.

(** A concrete guarantee remains available for every value of the rigid
    parameter.  At timeout two, {(3,2)} permits precisely sizes a <= 6. *)
Definition ps_open_contract :=
  PSEJoin (PSEVar 0) (PSELiteral [Obligation 3 2]).
Definition ps_open_download := PSESize 0%nat poly_timeout_2.
Definition ps_open_guard := LGuard 1 ps_open_download ps_open_contract.
Definition ps_open_numeric := CAnd (CUpper 0%nat 6) CTop.

Example ps_open_join_three_two_compiles :
  ps_compile_guard ps_open_download ps_open_contract = Some ps_open_numeric.
Proof. vm_compute. reflexivity. Qed.
Example ps_open_join_reversed_compiles :
  ps_compile_guard ps_open_download
    (PSEJoin (PSELiteral [Obligation 3 2]) (PSEVar 0)) = Some ps_open_numeric.
Proof. vm_compute. reflexivity. Qed.
Example ps_open_nested_join_compiles :
  ps_compile_guard ps_open_download
    (PSEJoin (PSEPar (PSEVar 0) (PSEVar 1))
      (PSEJoin (PSELiteral [Obligation 1 1]) (PSELiteral [Obligation 3 2]))) =
    Some ps_open_numeric.
Proof. vm_compute. reflexivity. Qed.
Example ps_open_parallel_compiles :
  ps_compile_guard ps_open_download
    (PSEPar (PSEVar 0) (PSELiteral [Obligation 3 2])) = Some ps_open_numeric.
Proof. vm_compute. reflexivity. Qed.
Example ps_open_parallel_guarantees_combine :
  ps_compile_guard ps_open_download
    (PSEPar (PSEJoin (PSEVar 0) (PSELiteral [Obligation 1 1]))
      (PSEJoin (PSEVar 1) (PSELiteral [Obligation 3 1]))) =
    Some ps_open_numeric.
Proof. vm_compute. reflexivity. Qed.

Example ps_open_join_exact_size : forall sigma,
  ps_guard_models sigma 1 ps_open_download ps_open_contract <->
    sigma 0%nat <= 6.
Proof.
  intro sigma.
  pose proof (ps_compile_guard_exact 1 ps_open_download ps_open_contract
    ps_open_numeric I ps_open_join_three_two_compiles sigma) as H.
  change (sigma 0%nat <= 6 /\ True <->
    ps_guard_models sigma 1 ps_open_download ps_open_contract) in H.
  tauto.
Qed.
Example ps_open_join_accepts6 :
  ps_guard_models (fun _ => poly_size_6) 1 ps_open_download ps_open_contract.
Proof. apply ps_open_join_exact_size. vm_compute. discriminate. Qed.
Example ps_open_join_rejects_larger_sizes : forall sigma : size_assignment,
  6 < sigma 0%nat ->
  ~ ps_guard_models sigma 1 ps_open_download ps_open_contract.
Proof.
  intros sigma Hlarge Hguard. apply ps_open_join_exact_size in Hguard.
  exact (Qlt_not_le _ _ Hlarge Hguard).
Qed.
Example ps_open_join_numeric_rejects10 :
  ~ models (fun _ => poly_size_10) ps_open_numeric.
Proof. vm_compute. intuition discriminate. Qed.

Definition ps_open_capped := LAnd (LNumeric (CUpper 0%nat 100)) ps_open_guard.
Definition ps_open_assignment :=
  solved_assignment (ps_final_constraint ps_empty_environment ps_empty 0
    (CAnd (CUpper 0%nat 100) ps_open_numeric)).
Example ps_open_join_solver_accepts :
  ps_solve ps_empty_environment ps_empty 0 ps_open_capped =
    Solved ps_open_assignment.
Proof. reflexivity. Qed.
Example ps_open_join_solver_maximum_is6 : ps_open_assignment 0%nat == 6.
Proof. vm_compute. reflexivity. Qed.

(** Even a zero-size download contributes a singleton obligation. Neither an
    empty target nor an unconstrained rigid parameter can cover it universally. *)
Example ps_empty_target_is_unsatisfiable : forall eta B,
  ps_solve eta ps_empty B (LGuard 1 ps_open_download ps_empty) = Unsatisfiable.
Proof. reflexivity. Qed.
Example ps_bare_parameter_is_unsatisfiable : forall eta B,
  ps_solve eta ps_empty B (LGuard 1 ps_open_download (PSEVar 0)) = Unsatisfiable.
Proof. reflexivity. Qed.
Example ps_zero_rate_singleton_is_not_empty : forall eta B,
  ps_solve eta ps_empty B
    (LGuard 1 (PSELiteral [Obligation 0 1]) (PSEVar 0)) = Unsatisfiable.
Proof. reflexivity. Qed.

(** Empty instantiation is sufficient only for the supported direction with
    a closed source. Evaluating both sides at empty would wrongly accept this
    open-source guard. The compiler continues to return Unresolved. *)
Example ps_open_source_empty_instance_passes : forall sigma,
  ps_eval_raw sigma ps_empty_environment (PSEVar 0) ≼
    ps_eval_raw sigma ps_empty_environment ps_empty.
Proof. intros. apply effect_le_refl. Qed.
Example ps_open_source_universal_guard_fails : forall sigma,
  ~ ps_guard_models sigma 1 (PSEVar 0) ps_empty.
Proof.
  intros sigma H.
  assert (ps_environment 1 (fun _ => [Obligation 5 1])) as Henv.
  { intros i Hi. repeat constructor. vm_compute. discriminate. }
  specialize (H (fun _ => [Obligation 5 1]) Henv).
  destruct (H (Obligation 5 1) (or_introl eq_refl)) as [p [Hp _]].
  contradiction.
Qed.
Example ps_open_source_guard_remains_unresolved : forall eta B,
  ps_solve eta ps_empty B (LGuard 1 (PSEVar 0) ps_empty) = Unresolved.
Proof. reflexivity. Qed.

(** The supported comparison is also produced by the actual inference
    judgment under a binder. Explicit instantiation retains its universal
    obligation and cannot enlarge the inferred maximum size. *)
Definition pi_supported_annotation :=
  PTArrow PTUnit (EffJoin (EffVar 0) (EffLit [Obligation 3 2])) PTUnit.
Definition pi_supported_suspension :=
  PIEAbsEff (PIEApp (PIELambda pi_supported_annotation PIEUnit) pi_example_callback).
Definition pi_supported_constraint :=
  LAnd (LNumeric CTop) (LAnd (LNumeric (CUpper 0%nat 100))
    (ps_constraint_norm (pst_subtype_constraint 1
      (PSTyArrow PSTyUnit ps_open_download PSTyUnit)
      (PSTyArrow PSTyUnit ps_open_contract PSTyUnit)))).
Example pi_supported_suspension_generated :
  pi_infers 100 0 [] pi_supported_suspension (PSTyForall PSTyUnit ps_empty)
    ps_empty pi_supported_constraint.
Proof.
  apply PIIAbsEff; [constructor|].
  change (pi_infers 100 1 []
    (PIEApp (PIELambda pi_supported_annotation PIEUnit) pi_example_callback)
    PSTyUnit (ps_norm (PSEJoin ps_empty (PSEJoin ps_empty ps_empty)))
    pi_supported_constraint).
  eapply PIIApp with (A := PSTyArrow PSTyUnit ps_open_contract PSTyUnit).
  - apply PIIAbs.
    + unfold pi_supported_annotation. repeat (first [solve [lia] | constructor]).
      vm_compute. discriminate.
    + constructor.
  - apply PIIAbs; [constructor|constructor].
Qed.
Example pi_supported_application_retains_constraint :
  pi_infers 100 0 [] (PIEAppEff pi_supported_suspension poly_rate5)
    PSTyUnit ps_empty pi_supported_constraint.
Proof.
  change (pi_infers 100 0 [] (PIEAppEff pi_supported_suspension poly_rate5)
    (pst_norm (pst_subst (eff_single poly_rate5) PSTyUnit))
    (ps_norm (PSEJoin ps_empty (ps_subst (eff_single poly_rate5) ps_empty)))
    pi_supported_constraint).
  apply PIIAppEff; [apply pi_supported_suspension_generated|apply poly_rate5_scoped].
Qed.
Definition pi_supported_numeric :=
  CAnd CTop (CAnd (CUpper 0%nat 100) (CAnd CTop (CAnd ps_open_numeric CTop))).
Definition pi_supported_assignment :=
  solved_assignment (ps_final_constraint ps_empty_environment ps_empty 0
    pi_supported_numeric).
Example pi_supported_compilation :
  ps_compile pi_supported_constraint = Some pi_supported_numeric.
Proof. reflexivity. Qed.
Example pi_supported_solver :
  ps_solve ps_empty_environment ps_empty 0 pi_supported_constraint =
    Solved pi_supported_assignment.
Proof. reflexivity. Qed.
Example pi_supported_inferred_maximum_is6 : pi_supported_assignment 0%nat == 6.
Proof. vm_compute. reflexivity. Qed.
Example pi_supported_inferred_application_safe :
  ~ exists target active,
    poly_successful_steps 0
      (pi_instantiate pi_supported_assignment
        (PIEAppEff pi_supported_suspension poly_rate5)) 0 target active /\
    poly_step 0 (PolyConfig target active) PolyError.
Proof.
  destruct (pi_solved_program_safe 100
    (PIEAppEff pi_supported_suspension poly_rate5) PSTyUnit ps_empty
    pi_supported_constraint 0 pi_supported_assignment) as [_ [_ [_ Hsafe]]].
  - apply Qle_refl.
  - apply pi_supported_application_retains_constraint.
  - apply pi_supported_solver.
  - exact Hsafe.
Qed.

(** Parallel regrouping collects numerical factors across effect variables,
    but never distributes through a join or removes repeated parallel factors. *)
Definition poly_parallel_mixed :=
  EffPar (EffPar (EffLit [Obligation 4 3]) (EffVar 0))
    (EffLit [Obligation 2 1]).

Example poly_parallel_collects_separated_literals :
  eff_norm poly_parallel_mixed =
    EffPar (EffLit [Obligation 4 4]) (EffVar 0).
Proof. vm_compute. reflexivity. Qed.

Example poly_parallel_collects_from_right_subtree :
  eff_norm (EffPar (EffVar 0)
    (EffPar (EffLit [Obligation 4 3]) (EffLit [Obligation 2 1]))) =
    EffPar (EffLit [Obligation 4 4]) (EffVar 0).
Proof. vm_compute. reflexivity. Qed.

Example poly_parallel_preserves_repeated_variables :
  eff_norm (EffPar
    (EffPar (EffLit [Obligation 4 3]) (EffVar 0))
    (EffPar (EffLit [Obligation 2 1]) (EffVar 0))) =
    EffPar (EffLit [Obligation 4 4]) (EffPar (EffVar 0) (EffVar 0)).
Proof. vm_compute. reflexivity. Qed.

Example poly_parallel_preserves_residual_order :
  eff_norm (EffPar (EffPar (EffVar 1) (EffVar 0)) (EffVar 1)) =
    EffPar (EffVar 1) (EffPar (EffVar 0) (EffVar 1)).
Proof. vm_compute. reflexivity. Qed.

Example poly_parallel_stops_at_union :
  eff_norm (EffPar (EffLit [Obligation 4 3])
    (EffPar (EffJoin (EffLit [Obligation 2 1]) (EffVar 0)) (EffVar 1))) =
    EffPar (EffLit [Obligation 4 3])
      (EffPar (EffJoin (EffLit [Obligation 2 1]) (EffVar 0)) (EffVar 1)).
Proof. vm_compute. reflexivity. Qed.

Example poly_union_still_preserves_association :
  eff_norm (EffJoin
    (EffJoin (EffLit [Obligation 4 3]) (EffVar 0))
    (EffJoin (EffLit [Obligation 2 1]) (EffVar 1))) =
    EffJoin (EffJoin (EffLit [Obligation 4 3]) (EffVar 0))
      (EffJoin (EffLit [Obligation 2 1]) (EffVar 1)).
Proof. vm_compute. reflexivity. Qed.

Example poly_parallel_empty_factors_are_units :
  eff_norm (EffPar (EffPar (EffLit []) (EffVar 0)) (EffLit [])) = EffVar 0.
Proof. reflexivity. Qed.

Example poly_parallel_zero_pair_is_not_empty :
  eff_norm (EffPar (EffLit [Obligation 0 0]) (EffVar 0)) =
    EffPar (EffLit [Obligation 0 0]) (EffVar 0).
Proof. vm_compute. reflexivity. Qed.

(** The remaining symbolic factor still contributes its full concurrency.
    An empty instantiation is also legal, with a different bandwidth bound. *)
Example poly_parallel_regrouped_nonempty_bandwidth :
  required_bandwidth
    (eff_eval (fun _ => [Obligation 1 2]) (eff_norm poly_parallel_mixed)) == 24.
Proof. vm_compute. reflexivity. Qed.

Example poly_parallel_regrouped_empty_bandwidth :
  required_bandwidth
    (eff_eval (fun _ => []) (eff_norm poly_parallel_mixed)) == 16.
Proof. vm_compute. reflexivity. Qed.

Example ps_parallel_collects_separated_literals :
  ps_norm (PSEPar (PSEPar (PSELiteral [Obligation 4 3]) (PSEVar 0))
    (PSELiteral [Obligation 2 1])) =
    PSEPar (PSELiteral [Obligation 4 4]) (PSEVar 0).
Proof. vm_compute. reflexivity. Qed.

Example ps_parallel_preserves_unknown_size :
  ps_norm (PSEPar
    (PSEPar (PSELiteral [Obligation 4 3]) (PSESize 0%nat poly_timeout_2))
    (PSELiteral [Obligation 2 1])) =
    PSEPar (PSELiteral [Obligation 4 4]) (PSESize 0%nat poly_timeout_2).
Proof. vm_compute. reflexivity. Qed.

Example ps_parallel_preserves_repeated_variables :
  ps_norm (PSEPar
    (PSEPar (PSELiteral [Obligation 4 3]) (PSEVar 0))
    (PSEPar (PSELiteral [Obligation 2 1]) (PSEVar 0))) =
    PSEPar (PSELiteral [Obligation 4 4]) (PSEPar (PSEVar 0) (PSEVar 0)).
Proof. vm_compute. reflexivity. Qed.

Example ps_parallel_stops_at_union :
  ps_norm (PSEPar (PSELiteral [Obligation 4 3])
    (PSEPar (PSEJoin (PSELiteral [Obligation 2 1]) (PSEVar 0)) (PSEVar 1))) =
    PSEPar (PSELiteral [Obligation 4 3])
      (PSEPar (PSEJoin (PSELiteral [Obligation 2 1]) (PSEVar 0)) (PSEVar 1)).
Proof. vm_compute. reflexivity. Qed.

Example ps_parallel_empty_factors_are_units :
  ps_norm (PSEPar (PSEPar ps_empty (PSEVar 0)) ps_empty) = PSEVar 0.
Proof. reflexivity. Qed.

Example ps_parallel_zero_pair_is_not_empty :
  ps_norm (PSEPar (PSELiteral [Obligation 0 0]) (PSEVar 0)) =
    PSEPar (PSELiteral [Obligation 0 0]) (PSEVar 0).
Proof. vm_compute. reflexivity. Qed.

Example poly_parallel_zero_rate_still_adds_concurrency :
  required_bandwidth (eff_eval (fun _ => [Obligation 4 1])
    (eff_norm (EffPar (EffLit [Obligation 0 1]) (EffVar 0)))) == 8.
Proof. vm_compute. reflexivity. Qed.

(** The normalized form is consumed by actual guard compilation, retaining
    universal quantification over the remaining effect variable. *)
Example ps_parallel_regrouped_guard_compiles :
  ps_compile (ps_constraint_norm (LGuard 1
    (PSEPar (PSEPar (PSELiteral [Obligation 4 3]) (PSEVar 0))
      (PSELiteral [Obligation 2 1]))
    (PSEPar (PSELiteral [Obligation 4 4]) (PSEVar 0)))) = Some CTop.
Proof. vm_compute. reflexivity. Qed.

Example ps_parallel_repeated_factor_not_discarded_by_solver : forall eta B,
  ps_solve eta ps_empty B (ps_constraint_norm
    (LGuard 1 (PSEPar (PSEVar 0) (PSEVar 0)) (PSEVar 0))) = Unresolved.
Proof. reflexivity. Qed.

(** Literal collection may change the relative position of matching parallel
    operands. Guard search must also try the commuted pairing. *)
Example ps_parallel_regrouped_guard_matches_commuted_operands :
  ps_compile (ps_constraint_norm (LGuard 2
    (PSEPar (PSEVar 0) (PSELiteral [Obligation 2 1]))
    (PSEPar (PSEJoin (PSEVar 0) (PSEVar 1))
      (PSEJoin (PSELiteral [Obligation 2 1]) (PSEVar 1))))) = Some CTop.
Proof. vm_compute. reflexivity. Qed.

(** Finite structural search is still incomplete and sensitive to grouping.
    Regrouping can change acceptance even though universal meaning is proved
    equivalent: the following valid guard becomes unresolved, never false. *)
Definition ps_regroup_precision_source :=
  PSEPar (PSEVar 0) (PSEPar (PSELiteral [Obligation 2 1]) (PSEVar 1)).
Definition ps_regroup_precision_target :=
  PSEPar (PSEJoin (PSEVar 0) (PSEVar 2))
    (PSEPar (PSEJoin (PSELiteral [Obligation 2 1]) (PSEVar 2))
      (PSEJoin (PSEVar 1) (PSEVar 2))).

Example ps_parallel_original_grouping_compiles :
  ps_compile (LGuard 3 ps_regroup_precision_source ps_regroup_precision_target) =
    Some CTop.
Proof. vm_compute. reflexivity. Qed.

Example ps_parallel_regrouped_guard_remains_valid : forall sigma,
  ps_guard_models sigma 3
    (ps_norm ps_regroup_precision_source) (ps_norm ps_regroup_precision_target).
Proof.
  intros sigma eta Heta.
  assert (Hguard : ps_guard_models sigma 3
    ps_regroup_precision_source ps_regroup_precision_target).
  { apply ps_trivial_sound. vm_compute. reflexivity. }
  destruct (ps_norm_eval ps_regroup_precision_source sigma eta) as [HS _].
  destruct (ps_norm_eval ps_regroup_precision_target sigma eta) as [_ HT].
  eapply effect_le_trans; [exact HS|].
  eapply effect_le_trans; [apply Hguard; exact Heta|exact HT].
Qed.

Example ps_parallel_regrouped_search_can_be_unresolved : forall eta B,
  ps_solve eta ps_empty B (ps_constraint_norm
    (LGuard 3 ps_regroup_precision_source ps_regroup_precision_target)) = Unresolved.
Proof. reflexivity. Qed.
