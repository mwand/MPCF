(* lightweight definition of weights *)
Parameter Weight : Type.
Parameter zero_weight : Weight.
Parameter one_weight : Weight.
Parameter prod_weights : Weight -> Weight -> Weight.

Axiom prod_weights_zeroL : forall y, (prod_weights zero_weight y) = zero_weight.

Hint Rewrite prod_weights_zeroL.

Axiom prod_weights_oneL : forall y, (prod_weights one_weight y) = y.

Hint Rewrite prod_weights_oneL.

Axiom prod_weights_comm : forall x y, prod_weights x y = prod_weights y x.

Hint Resolve prod_weights_oneL.

Lemma prod_weights_zeroR : forall y, (prod_weights y zero_weight) = zero_weight.
Proof.
  intros.
  rewrite prod_weights_comm.
  apply prod_weights_zeroL.
Qed.

Hint Rewrite prod_weights_zeroR.

Lemma prod_weights_oneR : forall y, (prod_weights y one_weight) = y.
Proof.
  intros.
  rewrite prod_weights_comm.
  apply prod_weights_oneL.
Qed.

Hint Rewrite prod_weights_oneR.