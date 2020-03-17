Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

(* feel free to change this if you prefer other formalizations of Fin *)
Fixpoint Fin(n : nat) : Set :=
  match n with
  |0   => Empty_set
  |S m => unit + Fin m
  end.

(**
Proof:

Assume we have an injective function f. We must show for an element y that there exists an x such that f(x) = y.
We can prove this with induction.
Base case:
For the empty set or set with just y, this is trivial.
IH:
Assume this holds for a set of size k where k >= 1.
For k+1, let x' be an element in this set where x' != y.
If f(x') = x', then this is trivial.
Otherwise, construct a new function using f on Fin k (doesn't include x') such that f'(x) = f(x') if f(x) = x', otherwise f'(x) = f(x).
f' is injective and therefore surjective.
Therefore, there exists a y' such that f'(y') = y.
Since y != x', f(y') != x' and therefore f(y') = f'(y') = y.
Qed.
*)

Theorem inj_to_surj(n : nat) : forall f : Fin n -> Fin n, inj f -> surj f.
Proof.
  intros.
  unfold surj.
  intros.
  induction n.
  { simpl in y. contradiction. }
  destruct n.
  {
    exists y.
    simpl in y.
    simpl in f.
    admit.
  }
  {
    admit.
  }
  
Admitted.

Theorem surj_to_inj(n : nat) : forall f : Fin n -> Fin n, surj f -> inj f.
Admitted.
