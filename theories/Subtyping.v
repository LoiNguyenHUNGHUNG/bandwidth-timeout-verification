(** General structural properties of concrete subtyping.

    This module is intentionally independent of both constraint-generation
    completeness and checker comparison.  Those two developments both need
    transitivity: completeness uses it to transport subtype facts across
    semantic type equivalence, while checker comparison uses it to collapse
    chains of declarative [TySub] steps.  Keeping the lemma here avoids an
    artificial dependency in either direction. *)

From Stdlib Require Import Arith Lia List.

From BandwidthTimeout Require Import Effects Syntax Typing Merging.

Import ListNotations.

(** Structural subtyping is transitive.

    The middle type determines the shape of both input derivations.  Arrow
    domains and codomains are structurally smaller middle types, so the proof
    recursively composes their subtype derivations; latent-effect coverage is
    composed by [effect_le_trans].  Product subtyping is pointwise, requiring
    a subsidiary induction that aligns the two [Forall2] derivations.

    A well-founded induction on [type_measure] is used because product
    components are stored in lists rather than appearing as direct recursive
    premises of the outer [ty] induction principle. *)
Lemma subtype_trans :
  forall middle left right,
    subtype left middle ->
    subtype middle right ->
    subtype left right.
Proof.
  intro middle. pattern middle.
  apply (well_founded_induction_type
    (well_founded_ltof ty type_measure)).
  clear middle. intros middle IH left right Hleft Hright.
  destruct middle as
    [| |middle_domain middle_latent middle_codomain|middle_components];
    inversion Hleft; subst; inversion Hright; subst.
  - constructor.
  - constructor.
  - apply SubArrow.
    + apply (IH middle_domain); try assumption. unfold ltof. simpl. lia.
    + eapply effect_le_trans; eassumption.
    + apply (IH middle_codomain); try assumption. unfold ltof. simpl. lia.
  - apply SubProduct.
    assert (Hcompose :
      forall middles lefts rights,
        Forall2 subtype lefts middles ->
        Forall2 subtype middles rights ->
        (forall component, In component middles ->
          ltof ty type_measure component
            (Syntax.TyProduct middle_components)) ->
        Forall2 subtype lefts rights).
    { intros middles lefts rights Hlefts.
      revert rights. induction Hlefts;
        intros rights Hrights Hsmall; inversion Hrights; subst; constructor.
      - apply (IH y).
        + apply Hsmall. left. reflexivity.
        + assumption.
        + assumption.
      - eapply IHHlefts.
        + eassumption.
        + intros component Hin. apply Hsmall. right. assumption. }
    eapply Hcompose.
    + eassumption.
    + eassumption.
    + intros component Hin. apply type_measure_product_member. exact Hin.
Qed.
