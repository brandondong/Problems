Require Import Coq.micromega.Lia.

Definition decr(f : nat -> nat) := forall n, f (S n) <= f n.

Definition valley(f : nat -> nat)(n x : nat) := forall y, x <= y -> y <= n+x -> f y = f x.

(**
Proof:

For any x, there either is a n-valley at x or there exists an x' such that f(x') < f(x).
This can be shown constructively by considering x+n and using the fact that f is decreasing.

From this, we can prove that for any k, there exists an x such that f(x) < f(0)-k or there exists a n-valley somewhere using induction.

Base case (k = 0):
We can apply the claim above, specifically, there is either a n-valley at 0 or there exists an x' such that f(x') < f(0).

Inductive hypothesis (Assume k, prove k+1):
The case where there exists a n-valley is trivial.
In the case where there exists an x such that f(x) < f(0)-k, we need to prove there exists a y such that f(y) < f(0)-(k+1). We can use the above claim to show such a y.
Namely, f(y) < f(x), f(x) < f(0)-k, and f(0)-k-1 <= f(0)-(k+1) should be sufficient to show that f(y) < f(0)-(k+1).

With this new result, we show that there either exists a n-valley or for any n, there exists an x such that f(x) < f(0)-n. In the latter case, we can use n = f(0) to show a contradiction.

Qed
*)

Lemma n_valley_or_decr : forall n f x, decr f -> valley f n x \/ exists x', f x' < f x.
Admitted.

Lemma n_valley_or_k_down_f0 : forall n f k, decr f -> (exists y, valley f n y \/ exists x, f x < (f 0)-k).
Admitted.

Theorem decr_valleys : forall n f, decr f -> exists x, valley f n x.
intros n f decr_f.
Admitted.
