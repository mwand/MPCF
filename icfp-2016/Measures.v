(* Measures as integrators, a la diFinetti/Shan *)

Require Import LiftedTypes.
Require Import Weights.
Require Import MyReals.

Definition Measure (A : Type) : Type
  := ((A -> real) -> real).

(* Not every such function is a legitimate measure, but this *)
(* characterization, along with the Lebesgue axioms below, is good *)
(* enough for us *)

(* A better version would insist that the expectation function (A -> *)
(* Real) be measurable. *)

Parameter uniform_dist : Measure real.
(* currently not used.  We should redefine uniformopM to use this, with suitable axioms TK. *)

(* The Lebesgue integral *)
Parameter mu_L : Measure Unit.


(* Axioms about the integral *)

Axiom mu_L_const : forall (c : real) (f : Unit -> real),
    (forall u, f u = c) -> mu_L f = c.

Axiom mu_L_linear : forall c f,
    mu_L (fun u => (times c (f u))) = (times c (mu_L f)).
    
Axiom split_entropy : forall f,
    mu_L (fun u1 => mu_L (fun u2 => f u1 u2))
    = mu_L (fun u => f (left_half u) (right_half u)).

Axiom mu_L_extensional : forall f g,
    (forall u, f u = g u) -> mu_L f = mu_L g.

Lemma strict0_mu_L : forall {X : Type} (m : lifted X) h,
    (mu_L (fun u => doW x <- m ; h x u))
    =
    (doW x <- m;
        mu_L (fun u => (h x u))).
Proof.
  destruct m; simpl; auto.
  rewrite (mu_L_const zero); auto.
Qed.

Lemma strict20_mu_L : forall {A W : Type} (m : lifted (A * W)) h,
    (mu_L (fun u => doW x, w <- m ; h x w u))
    =
    (doW x, w <- m;
        mu_L (fun u => (h x w u))).
Proof.
  destruct m; simpl; auto.
  rewrite (mu_L_const zero); auto.
  destruct p; auto.
Qed.

(* An arbitrary measure, drawn from by 'distval' *)

Parameter mu_1 : Measure real.
Parameter density_1 : real -> Weight.

Axiom mu_1_density_1 :
  forall k : real -> real,
    mu_1 k = mu_L (fun u =>
                     (times (density_1 (unit_real u)) (k (unit_real u)))).

