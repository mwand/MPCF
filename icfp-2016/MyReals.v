(* The types Unit and real *)

Require Import LiftedTypes.
Require Import Weights.

Parameter Unit : Type.
Parameter left_half : Unit -> Unit.
Parameter right_half : Unit -> Unit.

(* These will be axiomatized in Measures.v *)

Parameter real : Type.
Parameter zero : real.
Parameter unit_real : Unit -> real.
Parameter times : Weight -> real -> real.

Axiom times_one_weight : forall r, times one_weight r = r.
Hint Rewrite times_one_weight.

Axiom times_weight_zero : forall w, times w zero = zero.
Hint Rewrite times_weight_zero.

Axiom times_zero_weight : forall r, times zero_weight r = zero.
Hint Rewrite times_zero_weight.

Axiom times_assoc : forall x y z,
    times x (times y z) = times (prod_weights x y) z.

Definition strict0  {X: Type} (v :lifted X)  (f : X -> real) : real :=
  match v with
    | bottom  => zero
    | lift x => (f x)
  end.
Local Hint Unfold strict0.

Definition strict20  {X Y} (v : lifted (X * Y))
           (f : X -> Y -> real) : real :=
  strict0 v (prod_curry f).
Local Hint Unfold strict20.

Notation "'doW' x , w <- m ; y" :=
  (strict20 m (fun x w => y))
    (at level 200, x ident, right associativity, m at level 100, y at level 200).
     (* format "'doW' '[' '[' x ',' '/  ' w ']' <- '[hv    ' m ']' ; '//' y ']'"). *)

Notation "'do' x , w <- m ; y" :=
  (strict2 m (fun x w => y))
    (at level 200, x ident, right associativity, m at level 100, y at level 200).
     (* format "'do' '[' '[' x ',' '/  ' w ']' <- '[hv    ' m ']' ; '//' y ']'"). *)

Notation "'doW' x <- m ; y" :=
  (strict0 m (fun x => y))
    (at level 200, x ident, right associativity, m at level 100, y at level 200).
     (* format "'doW' '[' '[' x ']' <- '[hv    ' m ']' ; '//' y ']'"). *)

Notation "'do' x <- m ; y" :=
  (strict m (fun x => y))
    (at level 200, x ident, right associativity, m at level 100, y at level 200).
     (* format "'do' '[' '[' x ']' <- '[hv    ' m ']' ; '//' y ']'"). *)

Lemma strict0_linear :
  forall (X : Type) (w : Weight) (d : lifted X) f,
    times w (doW a <- d; f a) = doW a <- d; times w (f a).
Proof.
  destruct d; auto using times_weight_zero.
Qed.

Lemma strict20_linear :
  forall (X Y : Type) (w : Weight) (d : lifted (X * Y)) f,
    times w (doW a, w' <- d; f a w') = doW a, w' <- d; times w (f a w').
Proof.
  destruct d as [|p]; [|destruct p];
  auto using times_weight_zero.
Qed.

Lemma strict0_bind_assoc : forall (A B : Type)
                                 (f : B -> real)
                                 (g : A -> lifted B)
                                 (m : lifted A),
    (doW x <- (do x <- m; g x); f x) =
    (doW x <- m; doW x <- g x; f x).
Proof.
  destruct m; auto.
Qed.

Lemma strict0_strict20_bind_assoc : forall (A B C : Type)
                                 (f : B -> C -> real)
                                 (g : A -> lifted (B * C))
                                 (m : lifted A),
    (doW y, w <- (do x <- m; g x); f y w) =
    (doW x <- m; doW y, w <- g x; f y w).
Proof.
  destruct m; auto.
Qed.

Lemma strict20_bind_assoc : forall (A B C : Type)
                                 (f : B -> C -> real)
                                 (g : A -> C -> lifted (B * C))
                                 (m : lifted (A * C)),
    (doW x, w <- (do x, w <- m; g x w); f x w) =
    (doW x, w <- m; doW x, w <- g x w; f x w).
Proof.
  destruct m as [|p]; auto.
  destruct p as [a w]; auto.
Qed.