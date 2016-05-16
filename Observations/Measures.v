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
    mu_L (fun u => strict0 m (fun x => h x u))
    =
    strict0 m (fun x => mu_L (fun u => h x u)).
Proof.
  destruct m; simpl; auto.
  rewrite (mu_L_const zero); auto.
Qed.

(* An arbitrary family of real-valued measure, indexed by the reals
   and drawn from by 'distval'.  The first argument p is the index.
   Think of (mu_1 p) as (normal p 1.0) *)


Parameter mu_1 : real -> Measure real.
Parameter density_1 : real -> real -> Weight.

Axiom mu_1_density_1 :
  forall (p: real)(k : real -> real),
    mu_1 p k = mu_L (fun u =>
                     (times (density_1 p (unit_real u)) (k (unit_real u)))).

Lemma strict20_mu_L : forall {A W : Type} (m : lifted (A * W)) h,
    mu_L (fun u => strict20 m (fun x w => h x w u))
    =
    strict20 m (fun x w => mu_L (fun u => (h x w u))).
Proof.
  destruct m; simpl; auto.
  rewrite (mu_L_const zero); auto.
  destruct p; auto.
Qed.


