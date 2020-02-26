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

Lemma decr_applies_all_after : forall f x k, decr f -> f (x+k) <= f x.
Proof.
  intros f x k decr_f.
  induction k.
  assert (x + 0 = x). lia. rewrite H. lia.
  unfold decr in decr_f.
  specialize (decr_f (x+k)).
  assert ((S (x + k)) = (x + S k)). lia.
  rewrite <- H.
  lia.
Qed.

Lemma n_valley_or_decr : forall n f x, decr f -> valley f n x \/ exists x', f x' < f x.
Proof.
  intros n f x decr_f.
  assert (f (x+n) <> f x \/ f (x+n) = f x) as excl_middle. lia.
  destruct excl_middle.
  {
  right.
  exists (x+n).
  specialize (decr_applies_all_after f x n decr_f).
  intros lt.
  lia.
  }
  {
  left.
  unfold valley.
  intros y gt lt.
  specialize (decr_applies_all_after f x (y-x) decr_f).
  intros f_lt.
  specialize (decr_applies_all_after f y (n+x-y) decr_f).
  intros f_gt.
  assert (y + (n + x - y) = n+x) as eq_y. lia.
  assert (x + (y - x) = y) as eq_n_x. lia.
  assert (f y <= f x).
  {
  rewrite <- eq_n_x.
  trivial.
  }
  clear eq_n_x f_lt. rename H0 into f_lt.
  assert (f (n+x) <= f y). rewrite <- eq_y. trivial.
  clear eq_y f_gt. rename H0 into f_gt.
  assert (n+x = x+n) as commut. lia.
  assert (f (x+n) <= f y). rewrite <- commut. trivial.
  lia.
  }
Qed.

Lemma n_valley_or_k_down_f0 : forall n f k, decr f -> ((exists y, valley f n y) \/ exists x, f x < (f 0)-k).
Proof.
  intros n f k decr_f.
  induction k.
  {
  specialize (n_valley_or_decr n f 0 decr_f).
  intros claim_at_0.
  destruct claim_at_0.
  left. exists 0. trivial.
  right. destruct H. exists x. lia.
  }
  destruct IHk.
  left. trivial.
  destruct H.
  specialize (n_valley_or_decr n f x decr_f).
  intros claim_at_x.
  destruct claim_at_x as [valley|lower].
  left. exists x. trivial.
  right.
  destruct lower.
  exists x0.
  lia.
Qed.

Theorem decr_valleys : forall n f, decr f -> exists x, valley f n x.
Proof.
  intros n f decr_f.
  specialize (n_valley_or_k_down_f0 n f (f 0) decr_f).
  intros induct_result.
  destruct induct_result as [found|below_0].
  trivial.
  destruct below_0 as [x below_0].
  lia.
Qed.
