(* Lifted Domains *)

Inductive lifted (X : Type) : Type :=
  | bottom : lifted X
  | lift : X -> lifted X.

Arguments bottom {_}.
Arguments lift {_} _.

Hint Constructors lifted.

Definition strict  {X: Type} {Y : Type} (v :lifted X)  (f : X -> (lifted Y)) : (lifted Y) :=
  match v with
    | bottom => @bottom Y
    | lift x => (f x)
  end.

Definition strict2  {X Y Z} (v : lifted (X * Y))
           (f : X -> Y -> lifted Z) : (lifted Z) :=
  strict v (prod_curry f).
