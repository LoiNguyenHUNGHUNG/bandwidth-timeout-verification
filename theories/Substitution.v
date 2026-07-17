(** Capture-avoiding renaming and substitution for de Bruijn expressions.

    A [renaming] maps old variable indices to new variable indices. A
    [substitution] maps old variable indices to replacement expressions.
    Both operations must be lifted when they pass underneath a lambda or the
    body of a let, because index [0] is bound by that construct. *)

From Stdlib Require Import Arith Lia List.
From BandwidthTimeout Require Import Syntax.

Import ListNotations.

(** A renaming tells us the new index of every free variable. *)
Definition renaming : Type := nat -> nat.

(** Lift a renaming through one binder. The newly bound variable remains
    index [0]; every older variable is renamed and remains outside it. *)
Definition up_ren (xi : renaming) : renaming :=
  fun index =>
    match index with
    | 0 => 0
    | S index' => S (xi index')
    end.

(** Rename all free variables in an expression. Only lambda bodies and let
    bodies introduce a binder, so only those recursive calls use [up_ren]. *)
Fixpoint rename (xi : renaming) (e : expr) : expr :=
  match e with
  | EVar index => EVar (xi index)
  | EUnit => EUnit
  | ENat n => ENat n
  | ELambda parameter_ty body =>
      ELambda parameter_ty (rename (up_ren xi) body)
  | ETuple components => ETuple (map (rename xi) components)
  | EApp function argument =>
      EApp (rename xi function) (rename xi argument)
  | ELet bound body =>
      ELet (rename xi bound) (rename (up_ren xi) body)
  | EIfZero guard zero_branch nonzero_branch =>
      EIfZero
        (rename xi guard)
        (rename xi zero_branch)
        (rename xi nonzero_branch)
  | EDownload size timeout => EDownload size timeout
  | ERunning size timeout => ERunning size timeout
  | EParallel branches => EParallel (map (rename xi) branches)
  end.

(** [shift] makes room for one new binder by increasing every free index. *)
Definition shift : renaming := S.

(** A simultaneous substitution supplies one replacement expression for every
    free variable index. *)
Definition substitution : Type := nat -> expr.

(** Lift a substitution through one binder. Index [0] now refers to the new
    binder. Older replacement expressions are shifted so that their free
    variables are not captured by that binder. *)
Definition up_subst (sigma : substitution) : substitution :=
  fun index =>
    match index with
    | 0 => EVar 0
    | S index' => rename shift (sigma index')
    end.

(** Simultaneously replace every free variable according to [sigma]. *)
Fixpoint subst (sigma : substitution) (e : expr) : expr :=
  match e with
  | EVar index => sigma index
  | EUnit => EUnit
  | ENat n => ENat n
  | ELambda parameter_ty body =>
      ELambda parameter_ty (subst (up_subst sigma) body)
  | ETuple components => ETuple (map (subst sigma) components)
  | EApp function argument =>
      EApp (subst sigma function) (subst sigma argument)
  | ELet bound body =>
      ELet (subst sigma bound) (subst (up_subst sigma) body)
  | EIfZero guard zero_branch nonzero_branch =>
      EIfZero
        (subst sigma guard)
        (subst sigma zero_branch)
        (subst sigma nonzero_branch)
  | EDownload size timeout => EDownload size timeout
  | ERunning size timeout => ERunning size timeout
  | EParallel branches => EParallel (map (subst sigma) branches)
  end.

(** The substitution used by beta-reduction. Index [0] is replaced by
    [replacement], while every higher index is decremented because one binder
    disappears. *)
Definition subst0 (replacement body : expr) : expr :=
  subst
    (fun index =>
       match index with
       | 0 => replacement
       | S index' => EVar index'
       end)
    body.

(** Substituting for the nearest variable returns the replacement. *)
Example subst0_var_zero :
  subst0 (ENat 5) (EVar 0) = ENat 5.
Proof. reflexivity. Qed.

(** Substitution crosses a binder without replacing the variable introduced
    by that binder. The closed replacement needs no visible index shift. *)
Example subst0_under_lambda :
  subst0 (ENat 5) (ELambda TyNat (EVar 1)) =
  ELambda TyNat (ENat 5).
Proof. reflexivity. Qed.

(** An open replacement is shifted when it crosses the lambda. Its free index
    [0] therefore becomes [1], rather than being captured by the lambda as the
    lambda's own index [0]. *)
Example subst0_avoids_capture :
  subst0 (EVar 0) (ELambda TyNat (EVar 1)) =
  ELambda TyNat (EVar 1).
Proof. reflexivity. Qed.

(** Renaming preserves values. Lambda bodies may be renamed, but a lambda is
    still a value; tuple components remain values recursively. *)
Lemma rename_preserves_value :
  forall xi v,
    value v -> value (rename xi v).
Proof.
  fix IH 3.
  intros xi v Hvalue. destruct Hvalue; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. induction H.
    + constructor.
    + simpl. constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** Renaming variable indices cannot introduce runtime-only syntax, so source
    expressions remain source expressions. *)
Lemma rename_preserves_source :
  forall xi e,
    source_expr e -> source_expr (rename xi e).
Proof.
  fix IH 3.
  intros xi e Hsource. destruct Hsource; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IH. assumption.
  - apply SrcTuple.
    + clear H0. induction H; simpl.
      * constructor.
      * constructor.
        -- apply rename_preserves_value. exact H.
        -- exact IHForall.
    + clear H. induction H0; simpl.
      * constructor.
      * constructor.
        -- apply IH. exact H.
        -- exact IHForall.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** Renaming preserves the runtime grammar, including the requirement that
    tuple components remain values. *)
Lemma rename_preserves_runtime_wf :
  forall xi e,
    runtime_wf e -> runtime_wf (rename xi e).
Proof.
  fix IH 3.
  intros xi e Hwf. destruct Hwf; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. apply IH. assumption.
  - apply RtTuple.
    + clear H0. induction H; simpl.
      * constructor.
      * constructor.
        -- apply rename_preserves_value. exact H.
        -- exact IHForall.
    + clear H. induction H0; simpl.
      * constructor.
      * constructor.
        -- apply IH. exact H.
        -- exact IHForall.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor; apply IH; assumption.
  - constructor.
  - constructor.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** [renaming_scoped source_depth target_depth xi] says that [xi] maps every
    variable admitted at [source_depth] to one admitted at [target_depth]. *)
Definition renaming_scoped
    (source_depth target_depth : nat) (xi : renaming) : Prop :=
  forall index,
    (index < source_depth)%nat ->
    (xi index < target_depth)%nat.

(** A scope-respecting renaming remains scope-respecting underneath a binder. *)
Lemma up_ren_scoped :
  forall source_depth target_depth xi,
    renaming_scoped source_depth target_depth xi ->
    renaming_scoped (S source_depth) (S target_depth) (up_ren xi).
Proof.
  intros source_depth target_depth xi Hxi index Hindex.
  destruct index as [|index']; simpl.
  - lia.
  - specialize (Hxi index' ltac:(lia)). lia.
Qed.

(** Renaming preserves scoping when the index map respects the source and
    target context depths. This is the structural core of the later weakening
    lemma for typing. *)
Lemma rename_preserves_scoped :
  forall source_depth target_depth xi e,
    renaming_scoped source_depth target_depth xi ->
    scoped source_depth e ->
    scoped target_depth (rename xi e).
Proof.
  fix IH 6.
  intros source_depth target_depth xi e Hxi Hscoped.
  destruct Hscoped; simpl.
  - constructor. apply Hxi. assumption.
  - constructor.
  - constructor.
  - constructor. eapply IH.
    + apply up_ren_scoped. exact Hxi.
    + assumption.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
  - constructor; eapply IH; eauto.
  - constructor.
    + eapply IH; eauto.
    + eapply IH.
      * apply up_ren_scoped. exact Hxi.
      * assumption.
  - constructor; eapply IH; eauto.
  - constructor.
  - constructor.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
Qed.

(** In particular, renaming a closed expression leaves it closed. *)
Lemma rename_preserves_closed :
  forall xi e,
    closed e -> closed (rename xi e).
Proof.
  intros xi e Hclosed. unfold closed in *.
  eapply rename_preserves_scoped with (source_depth := 0).
  - intros index Hindex. lia.
  - exact Hclosed.
Qed.

(** If [xi] is the identity on all variables admitted at [depth], lifting it
    through one binder is the identity on all variables admitted at the larger
    depth. *)
Lemma up_ren_identity_on_scope :
  forall depth xi,
    (forall index, (index < depth)%nat -> xi index = index) ->
    forall index,
      (index < S depth)%nat -> up_ren xi index = index.
Proof.
  intros depth xi Hxi [|index] Hindex; simpl.
  - reflexivity.
  - f_equal. apply Hxi. lia.
Qed.

(** A renaming that is the identity on every variable in scope leaves the
    entire expression syntactically unchanged. *)
Lemma rename_identity_on_scoped :
  forall depth e xi,
    scoped depth e ->
    (forall index, (index < depth)%nat -> xi index = index) ->
    rename xi e = e.
Proof.
  fix IH 4.
  intros depth e xi Hscoped Hxi. destruct Hscoped; simpl.
  - f_equal. apply Hxi. assumption.
  - reflexivity.
  - reflexivity.
  - f_equal. eapply IH; eauto using up_ren_identity_on_scope.
  - f_equal. induction H; simpl.
    + reflexivity.
    + f_equal.
      * eapply IH; eauto.
      * exact IHForall.
  - f_equal; eapply IH; eauto.
  - f_equal.
    + eapply IH; eauto.
    + eapply IH; eauto using up_ren_identity_on_scope.
  - f_equal; eapply IH; eauto.
  - reflexivity.
  - reflexivity.
  - f_equal. induction H; simpl.
    + reflexivity.
    + f_equal.
      * eapply IH; eauto.
      * exact IHForall.
Qed.

(** A closed expression has no free variable on which [xi] can act. Therefore
    every binder-aware renaming returns exactly the original expression. *)
Lemma rename_closed_identity :
  forall xi e,
    closed e -> rename xi e = e.
Proof.
  intros xi e Hclosed. apply rename_identity_on_scoped with (depth := 0).
  - exact Hclosed.
  - intros index Hindex. lia.
Qed.

(** Substitution preserves values for every replacement map. A variable is
    never itself a value, and substitution does not change the outer form of
    lambdas or tuples. *)
Lemma subst_preserves_value :
  forall sigma v,
    value v -> value (subst sigma v).
Proof.
  fix IH 3.
  intros sigma v Hvalue. destruct Hvalue; simpl.
  - constructor.
  - constructor.
  - constructor.
  - constructor. induction H.
    + constructor.
    + simpl. constructor.
      * apply IH. exact H.
      * exact IHForall.
Qed.

(** If every replacement is source syntax, lifting the substitution through a
    binder preserves that property. *)
Lemma up_subst_preserves_source :
  forall sigma,
    (forall index, source_expr (sigma index)) ->
    forall index, source_expr (up_subst sigma index).
Proof.
  intros sigma Hsigma [|index]; simpl.
  - constructor.
  - apply rename_preserves_source. apply Hsigma.
Qed.

(** Substitution cannot introduce runtime-only syntax when all replacement
    expressions are themselves source expressions. *)
Lemma subst_preserves_source :
  forall sigma e,
    (forall index, source_expr (sigma index)) ->
    source_expr e ->
    source_expr (subst sigma e).
Proof.
  fix IH 4.
  intros sigma e Hsigma Hsource. destruct Hsource; simpl.
  - apply Hsigma.
  - constructor.
  - constructor.
  - constructor. eapply IH.
    + apply up_subst_preserves_source. exact Hsigma.
    + assumption.
  - apply SrcTuple.
    + clear H0. induction H; simpl.
      * constructor.
      * constructor.
        -- apply subst_preserves_value. exact H.
        -- exact IHForall.
    + clear H. induction H0; simpl.
      * constructor.
      * constructor.
        -- eapply IH; eauto.
        -- exact IHForall.
  - constructor; eapply IH; eauto.
  - constructor.
    + eapply IH; eauto.
    + eapply IH.
      * apply up_subst_preserves_source. exact Hsigma.
      * assumption.
  - constructor; eapply IH; eauto.
  - constructor.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
Qed.

(** If every replacement follows the runtime grammar, lifting through a binder
    preserves that property. *)
Lemma up_subst_preserves_runtime_wf :
  forall sigma,
    (forall index, runtime_wf (sigma index)) ->
    forall index, runtime_wf (up_subst sigma index).
Proof.
  intros sigma Hsigma [|index]; simpl.
  - constructor.
  - apply rename_preserves_runtime_wf. apply Hsigma.
Qed.

(** Substitution preserves the runtime grammar when every replacement follows
    that grammar. *)
Lemma subst_preserves_runtime_wf :
  forall sigma e,
    (forall index, runtime_wf (sigma index)) ->
    runtime_wf e ->
    runtime_wf (subst sigma e).
Proof.
  fix IH 4.
  intros sigma e Hsigma Hwf. destruct Hwf; simpl.
  - apply Hsigma.
  - constructor.
  - constructor.
  - constructor. eapply IH.
    + apply up_subst_preserves_runtime_wf. exact Hsigma.
    + assumption.
  - apply RtTuple.
    + clear H0. induction H; simpl.
      * constructor.
      * constructor.
        -- apply subst_preserves_value. exact H.
        -- exact IHForall.
    + clear H. induction H0; simpl.
      * constructor.
      * constructor.
        -- eapply IH; eauto.
        -- exact IHForall.
  - constructor; eapply IH; eauto.
  - constructor.
    + eapply IH; eauto.
    + eapply IH.
      * apply up_subst_preserves_runtime_wf. exact Hsigma.
      * assumption.
  - constructor; eapply IH; eauto.
  - constructor.
  - constructor.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
Qed.

(** [substitution_scoped source_depth target_depth sigma] says that every
    variable admitted at [source_depth] is replaced by an expression scoped at
    [target_depth]. *)
Definition substitution_scoped
    (source_depth target_depth : nat) (sigma : substitution) : Prop :=
  forall index,
    (index < source_depth)%nat ->
    scoped target_depth (sigma index).

(** A scope-respecting substitution remains scope-respecting underneath one
    binder. Older replacements are shifted into the larger target context. *)
Lemma up_subst_scoped :
  forall source_depth target_depth sigma,
    substitution_scoped source_depth target_depth sigma ->
    substitution_scoped
      (S source_depth) (S target_depth) (up_subst sigma).
Proof.
  intros source_depth target_depth sigma Hsigma index Hindex.
  destruct index as [|index']; simpl.
  - constructor. lia.
  - eapply rename_preserves_scoped with
        (source_depth := target_depth) (target_depth := S target_depth).
    + intros old_index Hold_index. unfold shift. lia.
    + apply Hsigma. lia.
Qed.

(** Substitution preserves scoping whenever the replacement map relates the
    source and target context depths. *)
Lemma subst_preserves_scoped :
  forall source_depth target_depth sigma e,
    substitution_scoped source_depth target_depth sigma ->
    scoped source_depth e ->
    scoped target_depth (subst sigma e).
Proof.
  fix IH 6.
  intros source_depth target_depth sigma e Hsigma Hscoped.
  destruct Hscoped; simpl.
  - apply Hsigma. assumption.
  - constructor.
  - constructor.
  - constructor. eapply IH.
    + apply up_subst_scoped. exact Hsigma.
    + assumption.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
  - constructor; eapply IH; eauto.
  - constructor.
    + eapply IH; eauto.
    + eapply IH.
      * apply up_subst_scoped. exact Hsigma.
      * assumption.
  - constructor; eapply IH; eauto.
  - constructor.
  - constructor.
  - constructor. induction H; simpl.
    + constructor.
    + constructor.
      * eapply IH; eauto.
      * exact IHForall.
Qed.

(** The beta-reduction substitution preserves source syntax when both its
    replacement and body are source expressions. *)
Lemma subst0_preserves_source :
  forall replacement body,
    source_expr replacement ->
    source_expr body ->
    source_expr (subst0 replacement body).
Proof.
  intros replacement body Hreplacement Hbody.
  apply subst_preserves_source.
  - intros [|index]; simpl; [exact Hreplacement | constructor].
  - exact Hbody.
Qed.

(** The beta-reduction substitution preserves the runtime grammar when both
    its replacement and body follow that grammar. *)
Lemma subst0_preserves_runtime_wf :
  forall replacement body,
    runtime_wf replacement ->
    runtime_wf body ->
    runtime_wf (subst0 replacement body).
Proof.
  intros replacement body Hreplacement Hbody.
  apply subst_preserves_runtime_wf.
  - intros [|index]; simpl; [exact Hreplacement | constructor].
  - exact Hbody.
Qed.

(** Removing one binder by [subst0] preserves scoping: the body may use the
    removed index [0], and the replacement must fit the surrounding context. *)
Lemma subst0_preserves_scoped :
  forall depth replacement body,
    scoped depth replacement ->
    scoped (S depth) body ->
    scoped depth (subst0 replacement body).
Proof.
  intros depth replacement body Hreplacement Hbody.
  apply subst_preserves_scoped with (source_depth := S depth).
  - intros [|index] Hindex; simpl.
    + exact Hreplacement.
    + constructor. lia.
  - exact Hbody.
Qed.
