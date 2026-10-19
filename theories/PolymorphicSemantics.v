(** Small-step operational semantics for the bandwidth-timeout calculus.

    A successful configuration pairs a runtime expression with the global
    number of active downloads. The distinguished error configuration records
    bandwidth under-provisioning. The transition relation is parameterized by
    the fixed global bandwidth budget [B]. *)

From Stdlib Require Import Arith Lia List QArith.
From BandwidthTimeout Require Import Quantities Bandwidth Syntax PolymorphicEffects PolymorphicSyntax.

Import ListNotations.
Open Scope Q_scope.

(** Runtime configurations are either a current expression and active-download
    counter, or the terminal bandwidth-error state. *)
Inductive poly_configuration : Type :=
| PolyConfig : poly_expr -> nat -> poly_configuration
| PolyError : poly_configuration.

(** A running download is under-provisioned when at least one download is
    active and its fair share of [B] is below its required average rate. *)
Definition poly_underprovisioned
    (B : Q) (active : nat)
    (size : nonnegative_rational) (timeout : positive_rational) : Prop :=
  (0 < active)%nat /\
  B / qnat active < download_rate size timeout.

(** [poly_step B c c'] means that configuration [c] can take one small step to
    configuration [c'] under the fixed bandwidth budget [B]. Parallel children
    may step in any order, so this relation is intentionally nondeterministic. *)
Inductive poly_step (B : Q) : poly_configuration -> poly_configuration -> Prop :=
| PolyStepLetDone : forall bound body active,
    poly_value bound ->
    poly_step B
      (PolyConfig (PELet bound body) active)
      (PolyConfig (poly_subst0 bound body) active)
| PolyStepBeta : forall parameter_ty body argument active,
    poly_value argument ->
    poly_step B
      (PolyConfig (PEApp (PELambda parameter_ty body) argument) active)
      (PolyConfig (poly_subst0 argument body) active)
| PolyStepIfZero : forall zero_branch nonzero_branch active,
    poly_step B
      (PolyConfig (PEIfZero (PENat 0) zero_branch nonzero_branch) active)
      (PolyConfig zero_branch active)
| PolyStepIfNonzero : forall n zero_branch nonzero_branch active,
    (n <> 0)%nat ->
    poly_step B
      (PolyConfig (PEIfZero (PENat n) zero_branch nonzero_branch) active)
      (PolyConfig nonzero_branch active)
| PolyStepParallelDone : forall branches active,
    Forall poly_value branches ->
    poly_step B
      (PolyConfig (PEParallel branches) active)
      (PolyConfig (PETuple branches) active)
| PolyStepDownloadStart : forall size timeout active,
    poly_step B
      (PolyConfig (PEDownload size timeout) active)
      (PolyConfig (PERunning size timeout) (S active))
| PolyStepDownloadFinish : forall size timeout active,
    (0 < active)%nat ->
    poly_step B
      (PolyConfig (PERunning size timeout) active)
      (PolyConfig PEUnit (Nat.pred active))
| PolyStepBandwidthError : forall size timeout active,
    poly_underprovisioned B active size timeout ->
    poly_step B
      (PolyConfig (PERunning size timeout) active)
      PolyError
| PolyStepLet : forall bound bound' body active active',
    poly_step B (PolyConfig bound active) (PolyConfig bound' active') ->
    poly_step B
      (PolyConfig (PELet bound body) active)
      (PolyConfig (PELet bound' body) active')
| PolyStepAppFunction : forall function function' argument active active',
    poly_step B (PolyConfig function active) (PolyConfig function' active') ->
    poly_step B
      (PolyConfig (PEApp function argument) active)
      (PolyConfig (PEApp function' argument) active')
| PolyStepAppArgument : forall function argument argument' active active',
    poly_value function ->
    poly_step B (PolyConfig argument active) (PolyConfig argument' active') ->
    poly_step B
      (PolyConfig (PEApp function argument) active)
      (PolyConfig (PEApp function argument') active')
| PolyStepIfGuard : forall guard guard' zero_branch nonzero_branch active active',
    poly_step B (PolyConfig guard active) (PolyConfig guard' active') ->
    poly_step B
      (PolyConfig (PEIfZero guard zero_branch nonzero_branch) active)
      (PolyConfig (PEIfZero guard' zero_branch nonzero_branch) active')
| PolyStepParallel : forall prefix branch branch' suffix active active',
    poly_step B (PolyConfig branch active) (PolyConfig branch' active') ->
    poly_step B
      (PolyConfig (PEParallel (prefix ++ (branch :: suffix))) active)
      (PolyConfig (PEParallel (prefix ++ (branch' :: suffix))) active')
| PolyStepLetError : forall bound body active,
    poly_step B (PolyConfig bound active) PolyError ->
    poly_step B (PolyConfig (PELet bound body) active) PolyError
| PolyStepAppFunctionError : forall function argument active,
    poly_step B (PolyConfig function active) PolyError ->
    poly_step B (PolyConfig (PEApp function argument) active) PolyError
| PolyStepAppArgumentError : forall function argument active,
    poly_value function ->
    poly_step B (PolyConfig argument active) PolyError ->
    poly_step B (PolyConfig (PEApp function argument) active) PolyError
| PolyStepIfGuardError : forall guard zero_branch nonzero_branch active,
    poly_step B (PolyConfig guard active) PolyError ->
    poly_step B (PolyConfig (PEIfZero guard zero_branch nonzero_branch) active) PolyError
| PolyStepParallelError : forall prefix branch suffix active,
    poly_step B (PolyConfig branch active) PolyError ->
    poly_step B
      (PolyConfig (PEParallel (prefix ++ (branch :: suffix))) active)
      PolyError
| PolyStepEffectBeta : forall body F active,
    poly_step B
      (PolyConfig (PEAppEff (PEAbsEff body) F) active)
      (PolyConfig (poly_effect_subst0 F body) active)
| PolyStepEffectApp : forall e e' F active active',
    poly_step B (PolyConfig e active) (PolyConfig e' active') ->
    poly_step B (PolyConfig (PEAppEff e F) active)
                (PolyConfig (PEAppEff e' F) active')
| PolyStepEffectAppError : forall e F active,
    poly_step B (PolyConfig e active) PolyError ->
    poly_step B (PolyConfig (PEAppEff e F) active) PolyError.

(** Reflexive-transitive successful execution. This relation records only
    expression-to-expression transitions; an execution that ends in [PolyError]
    is represented later by a successful prefix followed by one error step.
    The snoc presentation makes invariants easy to extend over the final
    successful transition. *)
Inductive poly_successful_steps (B : Q) : poly_expr -> nat -> poly_expr -> nat -> Prop :=
| PolyStepsRefl : forall e active,
    poly_successful_steps B e active e active
| PolyStepsSnoc : forall e active middle middle_active target target_active,
    poly_successful_steps B e active middle middle_active ->
    poly_step B
      (PolyConfig middle middle_active)
      (PolyConfig target target_active) ->
    poly_successful_steps B e active target target_active.

(** Effect abstraction suspends its body.  Only explicit application
    performs capture-avoiding effect substitution; it does not change the
    global download counter. *)
Example poly_effect_beta_step : forall B body F active,
  poly_step B (PolyConfig (PEAppEff (PEAbsEff body) F) active)
              (PolyConfig (poly_effect_subst0 F body) active).
Proof. intros. constructor. Qed.

Lemma poly_value_no_step : forall B v n target,
  poly_value v -> ~ poly_step B (PolyConfig v n) target.
Proof. intros B v n target Hv Hs. inversion Hv; subst; inversion Hs. Qed.
