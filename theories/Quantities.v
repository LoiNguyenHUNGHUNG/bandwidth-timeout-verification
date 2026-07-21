(** Refined rational quantities shared by concrete and symbolic syntax.

    Transfer sizes and rates may be zero but cannot be negative. Timeouts must
    be strictly positive. Packaging those invariants in their types makes
    invalid download parameters unrepresentable throughout the development. *)

From Stdlib Require Import QArith.

Open Scope Q_scope.

(** A rational quantity known to be nonnegative. *)
Record nonnegative_rational : Type := NonnegativeRational {
  nonnegative_value : Q;
  nonnegative_value_spec : 0 <= nonnegative_value
}.

(** Use checked nonnegative quantities transparently in rational arithmetic. *)
Coercion nonnegative_value : nonnegative_rational >-> Q.

(** A rational quantity known to be strictly positive. *)
Record positive_rational : Type := PositiveRational {
  positive_value : Q;
  positive_value_spec : 0 < positive_value
}.

(** Use checked positive quantities transparently in rational arithmetic. *)
Coercion positive_value : positive_rational >-> Q.
