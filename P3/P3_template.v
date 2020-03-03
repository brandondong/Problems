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

(* the identity *)
Definition e : X.
Admitted.

Theorem l_id : forall x, e * x = x.
Proof.
  intros.
Admitted.

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
Definition inv : X -> X.
Admitted.

Theorem l_inv : forall x, (inv x) * x = e.
Admitted.

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
