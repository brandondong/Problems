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
Case 0: f'(x) = 0 implies f(x) = true or there exists some x' where f(x') = true.
Case 1: We know that all x' > x satisfies f'(x') = 1 due to the infinite valley result. All x' < x also satisfy f'(x') = 1 since f' is decreasing. This shows that f is always false.

Qed.
*)

Fixpoint bool_f_to_nat (f : nat -> bool)(x : nat) : nat :=
  match f(x) with
  | true => 0
  | false =>
    match x with
    | 0 => 1
    | S x' => bool_f_to_nat f x'
    end
  end.

Theorem bool_f_to_nat_decr: forall f, decr (bool_f_to_nat f).
Proof.
  intros. unfold decr.
  intros x.
  simpl.
  case (f (S x)).
  lia. lia.
Qed.

Theorem bool_f_to_0_implies_true : forall f x, bool_f_to_nat f x = 0 -> exists x', f x' = true.
Proof.
  intros f x eq_0.
  induction x.
  exists 0. unfold bool_f_to_nat in eq_0.
  destruct (f 0). trivial. lia.
  assert (bool_f_to_nat f x = 0 \/ bool_f_to_nat f x <> 0). lia.
  destruct H.
  specialize (IHx H). trivial.
  clear IHx.
  simpl in eq_0.
  assert (f(S x) = true \/ f(S x) = false) as cases. destruct (f (S x)). left. trivial. right. trivial.
  destruct cases.
  exists (S x). trivial.
  destruct (f (S x)).
  discriminate.
  contradiction.
Qed.

Theorem infvalley_LPO : (forall f, decr f -> exists x, infvalley f x) -> LPO.
Proof.
  intros.
  unfold LPO. intros bool_f.
  specialize (bool_f_to_nat_decr bool_f). intros convert_decr.
  specialize (H (bool_f_to_nat bool_f) convert_decr).
  destruct H as [x inf_valley].
  assert ((bool_f_to_nat bool_f x) = 0 \/ (bool_f_to_nat bool_f x) <> 0) as cases. lia.
  destruct cases.
  specialize (bool_f_to_0_implies_true bool_f x H). intros goal. left. trivial.
Admitted.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Admitted.
