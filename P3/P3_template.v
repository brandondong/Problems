Definition inj{X Y}(f : X -> Y) := forall x x', f x = f x' -> x = x'.

Definition surj{X Y}(f : X -> Y) := forall y, {x : X & f x = y}.

Definition ded_fin(X : Set) := forall f : X -> X, inj f -> surj f.

Section df_inh_cancel_sgroups.

Variable X : Set.
Variable x0 : X.
Variable m : X -> X -> X.

Infix "*" := m.

Hypothesis X_df : ded_fin X.
Hypothesis assoc : forall x y z, x * (y * z) = (x * y) * z.
Hypothesis l_cancel : forall x y z, x * y = x * z -> y = z.
Hypothesis r_cancel : forall x y z, y * x = z * x -> y = z.

Lemma l_eq_solve : forall a b, {x : X & x * a = b}.
Proof.
Admitted.

(* the identity *)
Definition e : X := projT1 (l_eq_solve x0 x0).

Theorem l_id : forall x, e * x = x.
Proof.
  intros.
  assert (e * x0 = x0).
  {
    unfold e.
    destruct (l_eq_solve x0 x0).
    simpl.
    trivial.
  }
  assert (x * (e * x0) = x * x0).
  {
    rewrite H. trivial.
  }
  assert ((x * e) * x0 = x * x0).
  {
    pose (assoc x e x0). rewrite <- e0. trivial.
  }
  pose (r_cancel x0 (x * e) x H1).
  pose (assoc x e x).
  assert (x * (e * x) = x * x).
  {
    assert (forall a b, a * e = b -> x * (e * x) = a * e * x -> x * (e * x) = b * x).
    {
      intros. rewrite <- H2. trivial.
    }
    specialize (H2 x x e0 e1).
    trivial.
  }
  pose (l_cancel x (e*x) x H2).
  trivial.
Qed.

Theorem r_id : forall x, x * e = x.
Proof.
  intros.
  pose (assoc x e x).
  specialize (l_id (x)).
  intros.
  assert (x * x = x * e * x).
  {
    assert (x*x = x*(e*x)).
    {
      rewrite H.
      trivial.
    }
    rewrite H0.
    trivial.
  }
  pose (r_cancel x x (x*e) H0).
  symmetry.
  trivial.
Qed.

(* the inverse operation *)
Definition inv : X -> X := fun x => projT1 (l_eq_solve x e).

Theorem l_inv : forall x, (inv x) * x = e.
Proof.
  intros.
  unfold inv.
  destruct (l_eq_solve x e).
  simpl.
  trivial.
Qed.

Theorem r_inv : forall x, x * (inv x) = e.
Proof.
  intros.
  pose (assoc x (inv x) x).
  assert (x * inv x * x = e * x).
  {
    assert (x * inv x * x = x * e).
    {
      symmetry.
      specialize (l_inv x).
      intros.
      rewrite <- H.
      trivial.
    }
    assert (x * e = e * x).
    {
      specialize (r_id x).
      intros. rewrite H0.
      specialize (l_id x).
      intros. symmetry. trivial.
    }
    rewrite <- H0.
    trivial.
  }
  pose (r_cancel x (x * inv x) e H).
  trivial.
Qed.

End df_inh_cancel_sgroups.
