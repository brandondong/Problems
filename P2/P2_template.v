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

Lemma bool_f_cases : forall (f : nat -> bool) x, f x = true \/ f x = false.
Proof.
  intros.
  destruct (f x).
  left. trivial. right. trivial.
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
  specialize (bool_f_cases f (S x)).
  intros cases.
  destruct cases.
  exists (S x). trivial.
  destruct (f (S x)).
  discriminate.
  contradiction.
Qed.

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

Theorem bool_f_all_0_implies_constant_0 : forall f, (forall x', bool_f_to_nat f x' <> 0) -> (forall x : nat, f x = false).
Proof.
  intros f no_decr x.
  destruct x.
  specialize (bool_f_cases f 0).
  intros.
  destruct H.
  assert (bool_f_to_nat f 0 = 0).
  simpl. rewrite H. trivial.
  specialize (no_decr 0). contradiction.
  trivial.
  specialize (bool_f_cases f (S x)).
  intros.
  destruct H.
  assert (bool_f_to_nat f (S x) = 0).
  simpl.
  rewrite H. trivial.
  specialize (no_decr (S x)).
  contradiction.
  trivial.
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
  assert (forall x', bool_f_to_nat bool_f x' <> 0) as all_ne.
  {
  intros.
  assert (x' >= x \/ x' < x) as cases. lia.
  destruct cases as [gt|lt].
  unfold infvalley in inf_valley.
  specialize (inf_valley x' gt).
  lia.
  specialize (decr_applies_all_after (bool_f_to_nat bool_f) x' (x-x') convert_decr).
  assert (x' + (x - x') = x). lia.
  rewrite H0. clear H0.
  intros compare.
  lia.
  }
  specialize (bool_f_all_0_implies_constant_0 bool_f all_ne).
  intros constant. right. trivial.
Qed.

(**
LPO -> Infinite valley
Proof:

This will be basically the same proof as P1.
The difference is we will need to prove for any x, there is either an infinite valley at x or there exists an x' such that f(x') < f(x) instead of an n-valley.

We will need to use LPO and for that, construct a nat -> bool function from our original nat -> nat function f.
Since we need to show this property for a particular x, the function conversion should offset by x such that the modified function, when taking in 0 calls f(x).
Consider the function that given y, returns false if f(y+x) = f(y+x+1) and true otherwise.
This function is either all false or there exists an x such that x is true.
The false case implies an infinite valley starting at 0 (x).
The true case implies an x' such that f(x') < f(x), namely at f(y+x+1).

Qed.
*)

Definition f_to_bool (f : nat -> nat)(offset x : nat) : bool :=
  match f (x+offset) - f (x+offset+1) with
  | 0 => false
  | _ => true
  end.

Lemma infvalley_or_decr : LPO -> forall f x, decr f -> (infvalley f x \/ exists x', f x' < f x).
Proof.
  intros.
  unfold LPO in H.
  specialize (H (f_to_bool f x)).
  destruct H.
  {
    right.
    destruct H as [y H].
    exists (y+x+1).
    assert (f (y+x+1) < f (y+x)).
    {
      assert (f (y + x) - f (y + x + 1) = 0 \/ f (y + x) - f (y + x + 1) > 0). lia.
      destruct H1.
      {
        assert (f_to_bool f x y = false).
        {
          unfold f_to_bool.
          rewrite H1.
          trivial.
        }
        assert (true = false). rewrite <- H. trivial.
        discriminate.
      }
      { lia. }
    }
    assert (f (y + x) <= f x).
    {
      specialize (decr_applies_all_after f x y H0).
      intros.
      assert (y+x = x+y). lia.
      rewrite H3.
      trivial.
    }
    lia.
  }
  {
    left.
    unfold infvalley.
    intros.
    induction y.
    {
      assert (x = 0). lia.
      rewrite H2. trivial.
    }
    {
      assert (x = S y \/ x <= y). lia.
      destruct H2.
      { rewrite H2. trivial. }
      {
        specialize (IHy H2).
        assert (f (S y) = f y).
        {
          specialize (H (y-x)).
          assert (f (S y) = f y \/ f (S y) <> f y). lia.
          destruct H3.
          { trivial. }
          assert (f_to_bool f x (y - x) = true).
          {
            unfold f_to_bool.
            assert (f (y - x + x) - f (y - x + x + 1) > 0).
            {
              assert (f (S y) < f y).
              {
                unfold decr in H0.
                specialize (H0 y).
                lia.
              }
              assert (y - x + x = y). lia. rewrite H5.
              assert (y+1 = S y). lia. rewrite H6. lia.
            }
            destruct (f (y - x + x) - f (y - x + x + 1)). 
            { lia. }
            { trivial. }
          }
          assert (true = false). rewrite <- H4. trivial.
          discriminate.
        }
        rewrite H3. trivial.
      }
    }
  }
Qed.

Lemma infvalley_or_down : LPO -> forall f n, decr f -> ((exists x, infvalley f x) \/ exists x', f x' < f 0-n).
Proof.
  intros.
  induction n.
  {
    specialize (infvalley_or_decr H f 0 H0).
    intros.
    destruct H1.
    { left. exists 0. trivial. }
    { right. assert (f 0 - 0 = f 0). lia. rewrite H2. trivial. }
  }
  {
    destruct IHn.
    { left. trivial. }
    {
      destruct H1.
      specialize (infvalley_or_decr H f x H0).
      intros.
      destruct H2.
      { left. exists x. trivial. }
      {
        right. destruct H2.
        exists x0.
        lia.
      }
    }
  }
Qed.

Theorem LPO_infvalley : LPO -> forall f, decr f -> exists x, infvalley f x.
Admitted.
