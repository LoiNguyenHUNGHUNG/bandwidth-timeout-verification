(** Executable solving for the separable constraints produced by size inference.

    The paper's constraint generator eventually emits only conjunctions of
    failure, concrete comparisons, and upper bounds on one size variable at a
    time. Nonnegativity belongs to the semantic domain of size assignments,
    not to the generated constraint language. This file mechanizes that
    solver-facing language independently of symbolic typing. The later
    generator proof shows that every generated constraint belongs to this
    fragment. *)

From Stdlib Require Import Arith Bool Lia List QArith Qminmax.

Import ListNotations.
Open Scope Q_scope.

(** Size variables are represented by natural-number identifiers. *)
Definition size_variable : Type := nat.

(** A transfer-size bound is a rational together with the physical invariant
    that it is nonnegative. *)
Record nonnegative_rational : Type := NonnegativeRational {
  nonnegative_value : Q;
  nonnegative_value_spec : 0 <= nonnegative_value
}.

(** Use checked size bounds transparently in rational arithmetic. *)
Coercion nonnegative_value : nonnegative_rational >-> Q.

(** A timeout is a rational together with the language invariant that it is
    strictly positive. *)
Record positive_rational : Type := PositiveRational {
  positive_value : Q;
  positive_value_spec : 0 < positive_value
}.

(** Use checked timeouts transparently in rational arithmetic. *)
Coercion positive_value : positive_rational >-> Q.

(** A size assignment can therefore assign only nonnegative transfer sizes.
    The invariant is part of the semantic domain instead of a later premise. *)
Definition size_assignment : Type := size_variable -> nonnegative_rational.

(** Solver-facing constraints. [CUpper a c] represents [a <= c], while
    [CConcreteLe c c'] represents a variable-free check [c <= c']. *)
Inductive constraint : Type :=
| CTop
| CBottom
| CAnd (lhs rhs : constraint)
| CUpper (variable : size_variable) (bound : Q)
| CConcreteLe (lhs rhs : Q).

(** Semantic satisfaction of one constraint tree by an assignment. *)
Fixpoint satisfies_constraint
    (sigma : size_assignment) (C : constraint) : Prop :=
  match C with
  | CTop => True
  | CBottom => False
  | CAnd C1 C2 =>
      satisfies_constraint sigma C1 /\ satisfies_constraint sigma C2
  | CUpper variable bound => sigma variable <= bound
  | CConcreteLe lhs rhs => lhs <= rhs
  end.

(** Modeling now means constraint satisfaction directly: nonnegativity is
    already guaranteed by the type of [sigma]. *)
Definition models (sigma : size_assignment) (C : constraint) : Prop :=
  satisfies_constraint sigma C.

(** Collect every size variable mentioned by a constraint. Duplicates are
    harmless: the list is used only to check that each variable is bounded. *)
Fixpoint constraint_variables (C : constraint) : list size_variable :=
  match C with
  | CTop | CBottom | CConcreteLe _ _ => []
  | CAnd C1 C2 => constraint_variables C1 ++ constraint_variables C2
  | CUpper variable _ => [variable]
  end.

(** Collect all concrete upper bounds generated for [variable]. *)
Fixpoint upper_bounds
    (variable : size_variable) (C : constraint) : list Q :=
  match C with
  | CTop | CBottom | CConcreteLe _ _ => []
  | CAnd C1 C2 => upper_bounds variable C1 ++ upper_bounds variable C2
  | CUpper bounded_variable bound =>
      if Nat.eqb variable bounded_variable then [bound] else []
  end.

(** Check the solver's variable-free failure conditions and reject negative
    upper bounds. Generated constraints satisfy the latter condition under the
    paper's well-formedness assumptions. *)
Fixpoint solver_checks (C : constraint) : bool :=
  match C with
  | CTop => true
  | CBottom => false
  | CAnd C1 C2 => solver_checks C1 && solver_checks C2
  | CUpper _ bound => Qle_bool 0 bound
  | CConcreteLe lhs rhs => Qle_bool lhs rhs
  end.

(** Minimum of one distinguished bound and a possibly empty suffix. *)
Fixpoint minimum_from (head : Q) (tail : list Q) : Q :=
  match tail with
  | [] => head
  | bound :: tail' => Qmin head (minimum_from bound tail')
  end.

(** The computed minimum is no larger than the distinguished head. *)
Lemma minimum_from_le_head :
  forall head tail,
    minimum_from head tail <= head.
Proof.
  intros head tail. destruct tail as [|bound tail']; simpl.
  - apply Qle_refl.
  - apply Q.le_min_l.
Qed.

(** The computed minimum is no larger than every member of the input list. *)
Lemma minimum_from_le_member :
  forall head tail bound,
    In bound (head :: tail) ->
    minimum_from head tail <= bound.
Proof.
  intros head tail. revert head.
  induction tail as [|next tail IH]; intros head bound Hin; simpl in *.
  - destruct Hin as [-> | []]. apply Qle_refl.
  - destruct Hin as [-> | Hin].
    + apply Q.le_min_l.
    + eapply Qle_trans.
      * apply Q.le_min_r.
      * apply IH. exact Hin.
Qed.

(** Any common lower bound on the inputs is a lower bound on their minimum. *)
Lemma lower_bound_minimum_from :
  forall lower head tail,
    lower <= head ->
    (forall bound, In bound tail -> lower <= bound) ->
    lower <= minimum_from head tail.
Proof.
  intros lower head tail. revert head.
  induction tail as [|next tail IH]; intros head Hhead Htail; simpl.
  - exact Hhead.
  - apply Q.min_glb.
    + exact Hhead.
    + apply IH.
      * apply Htail. left. reflexivity.
      * intros bound Hin. apply Htail. right. exact Hin.
Qed.

(** The minimum of nonnegative bounds remains nonnegative. *)
Lemma minimum_from_nonnegative :
  forall head tail,
    0 <= head ->
    Forall (fun bound => 0 <= bound) tail ->
    0 <= minimum_from head tail.
Proof.
  intros head tail Hhead Htail.
  apply lower_bound_minimum_from.
  - exact Hhead.
  - intros bound Hin.
    apply Forall_forall with (x := bound) in Htail; assumption.
Qed.

(** Solve one variable by taking the minimum of all its generated upper
    bounds. [None] records that the variable has no finite upper bound. *)
Definition solve_variable
    (C : constraint) (variable : size_variable) : option Q :=
  match upper_bounds variable C with
  | [] => None
  | head :: tail => Some (minimum_from head tail)
  end.

(** Clamp an arbitrary rational into the semantic domain used by size
    assignments. Successful solver runs prove that the clamp is inactive. *)
Definition checked_size_bound (bound : Q) : nonnegative_rational :=
  NonnegativeRational (Qmax 0 bound) (Q.le_max_l 0 bound).

(** Turn the finite solver result into a total assignment. The default [0] is
    used only for identifiers absent from the constraint or for an unsuccessful
    unbounded variable. *)
Definition solved_assignment (C : constraint) : size_assignment :=
  fun variable =>
    match solve_variable C variable with
    | Some bound => checked_size_bound bound
    | None => checked_size_bound 0
    end.

(** Test whether a variable has at least one finite generated upper bound. *)
Definition variable_has_upper_bound
    (C : constraint) (variable : size_variable) : bool :=
  match upper_bounds variable C with
  | [] => false
  | _ :: _ => true
  end.

(** Every mentioned size variable must have a finite upper bound for a greatest
    satisfying assignment to exist. [SI-Down]'s global [M] bound will establish
    this premise for constraints produced by the later generator. *)
Definition all_variables_bounded (C : constraint) : bool :=
  forallb (variable_has_upper_bound C) (constraint_variables C).

(** The executable solver succeeds exactly when all concrete checks pass, all
    upper bounds can inhabit the nonnegative assignment domain, and every
    mentioned variable is bounded. *)
Definition solver_succeeds (C : constraint) : bool :=
  solver_checks C && all_variables_bounded C.

(** Passing the solver checks guarantees that every collected upper bound is
    nonnegative. *)
Lemma upper_bounds_nonnegative :
  forall C variable,
    solver_checks C = true ->
    Forall (fun bound => 0 <= bound) (upper_bounds variable C).
Proof.
  induction C; intros variable_to_solve Hchecks; simpl in *.
  - constructor.
  - constructor.
  - apply andb_true_iff in Hchecks as [Hleft Hright].
    apply Forall_app. split.
    + apply IHC1. exact Hleft.
    + apply IHC2. exact Hright.
  - destruct (Nat.eqb variable_to_solve variable) eqn:Heq.
    + constructor.
      * apply Qle_bool_iff. exact Hchecks.
      * constructor.
    + constructor.
  - constructor.
Qed.

(** The solved value is below every upper bound collected for its variable. *)
Lemma solved_assignment_respects_upper_bound :
  forall C variable bound,
    solver_checks C = true ->
    In bound (upper_bounds variable C) ->
    solved_assignment C variable <= bound.
Proof.
  intros C variable bound Hchecks Hin.
  unfold solved_assignment, solve_variable.
  destruct (upper_bounds variable C) as [|head tail] eqn:Hbounds.
  - contradiction.
  - simpl.
    pose proof (upper_bounds_nonnegative C variable Hchecks) as Hnonnegative.
    rewrite Hbounds in Hnonnegative. inversion Hnonnegative; subst.
    assert (Hminimum : 0 <= minimum_from head tail).
    { apply minimum_from_nonnegative; assumption. }
    rewrite Q.max_r by exact Hminimum.
    apply minimum_from_le_member. exact Hin.
Qed.

(** Any assignment respecting all collected upper bounds satisfies the
    original constraint tree once the concrete checks have passed. *)
Lemma satisfies_constraint_from_upper_bounds :
  forall C (sigma : size_assignment),
    solver_checks C = true ->
    (forall variable bound,
      In bound (upper_bounds variable C) -> sigma variable <= bound) ->
    satisfies_constraint sigma C.
Proof.
  induction C; intros sigma Hchecks Hbounds; simpl in *.
  - exact I.
  - discriminate.
  - apply andb_true_iff in Hchecks as [Hleft Hright]. split.
    + apply IHC1.
      * exact Hleft.
      * intros variable bound Hin. apply Hbounds.
        apply in_or_app. left. exact Hin.
    + apply IHC2.
      * exact Hright.
      * intros variable bound Hin. apply Hbounds.
        apply in_or_app. right. exact Hin.
  - apply Hbounds with (variable := variable) (bound := bound).
    rewrite Nat.eqb_refl. left. reflexivity.
  - apply Qle_bool_iff. exact Hchecks.
Qed.

(** Passing the concrete solver checks is enough for the computed assignment to
    satisfy the constraint. The boundedness check is needed only for greatest
    solutions, not for basic satisfiability. *)
Theorem solver_checks_sound :
  forall C,
    solver_checks C = true ->
    models (solved_assignment C) C.
Proof.
  intros C Hchecks. apply satisfies_constraint_from_upper_bounds.
  - exact Hchecks.
  - intros variable bound Hin.
    apply solved_assignment_respects_upper_bound; assumption.
Qed.

(** Solver success exposes the concrete checks used by the soundness proof. *)
Lemma solver_succeeds_checks :
  forall C,
    solver_succeeds C = true ->
    solver_checks C = true.
Proof.
  intros C Hsuccess. unfold solver_succeeds in Hsuccess.
  apply andb_true_iff in Hsuccess as [Hchecks _]. exact Hchecks.
Qed.

(** Every variable mentioned by a successfully solved constraint has a
    nonempty list of upper bounds. *)
Lemma solver_succeeds_has_upper_bound :
  forall C variable,
    solver_succeeds C = true ->
    In variable (constraint_variables C) ->
    exists head tail, upper_bounds variable C = head :: tail.
Proof.
  intros C variable Hsuccess Hin.
  unfold solver_succeeds in Hsuccess.
  apply andb_true_iff in Hsuccess as [_ Hbounded].
  unfold all_variables_bounded in Hbounded.
  rewrite forallb_forall in Hbounded.
  specialize (Hbounded variable Hin).
  unfold variable_has_upper_bound in Hbounded.
  destruct (upper_bounds variable C) as [|head tail] eqn:Hbounds.
  - discriminate.
  - exists head, tail. reflexivity.
Qed.

(** Satisfaction of a constraint implies every upper bound collected from that
    constraint. *)
Lemma satisfies_constraint_upper_bound :
  forall C sigma variable bound,
    satisfies_constraint sigma C ->
    In bound (upper_bounds variable C) ->
    sigma variable <= bound.
Proof.
  induction C; intros sigma variable_to_solve requested_bound Hsatisfies Hin;
    simpl in *.
  - contradiction.
  - contradiction.
  - destruct Hsatisfies as [Hleft Hright].
    apply in_app_or in Hin. destruct Hin as [Hin | Hin].
    + eapply IHC1; eauto.
    + eapply IHC2; eauto.
  - destruct (Nat.eqb variable_to_solve variable) eqn:Heq.
    + apply Nat.eqb_eq in Heq. subst variable_to_solve.
      destruct Hin as [-> | []]. exact Hsatisfies.
    + contradiction.
  - contradiction.
Qed.

(** Every satisfying assignment lies below the solver's assignment at each
    mentioned variable. This is the pointwise greatest-solution direction. *)
Theorem solver_succeeds_greatest :
  forall C sigma variable,
    solver_succeeds C = true ->
    models sigma C ->
    In variable (constraint_variables C) ->
    sigma variable <= solved_assignment C variable.
Proof.
  intros C sigma variable Hsuccess Hsatisfies Hin.
  destruct (solver_succeeds_has_upper_bound C variable Hsuccess Hin)
    as [head [tail Hbounds]].
  unfold solved_assignment, solve_variable. rewrite Hbounds. simpl.
  pose proof (solver_succeeds_checks C Hsuccess) as Hchecks.
  pose proof (upper_bounds_nonnegative C variable Hchecks) as Hnonnegative.
  rewrite Hbounds in Hnonnegative. inversion Hnonnegative; subst.
  assert (Hminimum : 0 <= minimum_from head tail).
  { apply minimum_from_nonnegative; assumption. }
  rewrite Q.max_r by exact Hminimum.
  apply lower_bound_minimum_from.
  - eapply satisfies_constraint_upper_bound.
    + exact Hsatisfies.
    + rewrite Hbounds. left. reflexivity.
  - intros bound Hbound_in.
    eapply satisfies_constraint_upper_bound.
    + exact Hsatisfies.
    + rewrite Hbounds. right. exact Hbound_in.
Qed.

(** Successful solving produces a satisfying assignment. *)
Theorem solver_succeeds_sound :
  forall C,
    solver_succeeds C = true ->
    models (solved_assignment C) C.
Proof.
  intros C Hsuccess. apply solver_checks_sound.
  apply solver_succeeds_checks. exact Hsuccess.
Qed.

(** The paper's maximality theorem for the separable solver fragment: on
    success, the computed assignment is itself a model and is pointwise at
    least as large as every other model on every inferred size variable. *)
Theorem solver_maximal :
  forall C,
    solver_succeeds C = true ->
    models (solved_assignment C) C /\
    forall sigma variable,
      models sigma C ->
      In variable (constraint_variables C) ->
      sigma variable <= solved_assignment C variable.
Proof.
  intros C Hsuccess. split.
  - apply solver_succeeds_sound. exact Hsuccess.
  - intros sigma variable Hmodels Hin.
    eapply solver_succeeds_greatest; eauto.
Qed.
