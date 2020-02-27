Require Import Coq.micromega.Lia.

Definition LPO := forall f : nat -> bool, (exists x, f x = true) \/ (forall x, f x = false).

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Definition infvalley(f : nat -> nat)(x : nat) := forall y, x <= y -> f y = f x.

(**
Infinite valley -> LPO:
Proof:

We need to show for a general boolean function f, either f is always false or there exists an x such that f(x) = true.
To do that, we must use the implication of the infinite valley statement. Specifically, we must construct a decreasing function.

Consider a function f' that calls f. It starts at 1 and upon the first true result, goes to 0 and stays there. Clearly this is decreasing so there exists an x such that there is an infinite valley at x.
f'(x) is either 0 or 1.
Case 0: f'(x) = 1 implies f(x) = true.
Case 1: We know that all x' > x satisfies f'(x') = 1 due to the infinite valley result. All x' < x also satisfy f'(x') = 1 since f' is decreasing. This shows that f is always false.

Qed.
*)

Fixpoint bool_f_to_decr (f : nat -> bool)(x : nat) : nat :=
  match f(x) with
  | true => 0
  | false =>
    match x with
    | 0 => 1
    | S x' => bool_f_to_decr f x'
    end
  end.

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
  intros.
  unfold LPO. intros bool_f.
Admitted.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Admitted.
