(* The Operational Semantics *)

Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.

Require Import EqNat. 

Require Import LiftedTypes.
Require Import MyReals.
Require Import Weights.
Require Import Measures.
Require Import Types.
Require Import Syntax.
Require Import Substitutions.

Inductive ev : forall {o: Otype}, Exp nil o -> Val nil o -> Prop :=
| ev_val : forall o (val: Val nil o), ev (valexp val) val
| ev_prod : forall {m m'} (e1 : Exp nil (Stype m)) (e2 : Exp nil (Stype m'))
                   v1 v2,
    ev e1 v1
    -> ev e2 v2
    -> ev (prodexp e1 e2) (prodval v1 v2)
| ev_proj1 : forall {m m'}
                    (e : Exp nil (Stype (Prod_type m m')))
                    v w,
    ev e (prodval v w) -> ev (proj1exp e) v
                                                           
| ev_proj2 : forall {m m'}
                    (e : Exp nil (Stype (Prod_type m m')))
                    v w,
    ev e (prodval v w) -> ev (proj2exp e) w

  | ev_app : forall o o' (e1 : Exp nil (Funtype o o'))
                    (e2 : Exp nil o)
                    e' v w,
               ev e1 (absexp e')
               -> ev e2 v
               -> ev (ap_Se (subst1 v) e') w
               -> ev (appexp e1 e2) w
  | ev_bind : forall (o o': Mtype) 
                     (e1 : Exp nil (Meastype o))
                     (c1 : Val nil (Meastype o))

                     (e2 : Exp nil (Funtype (Stype o)
                                            (Meastype o')))

                     (c2 : Val nil (Funtype (Stype o)
                                            (Meastype o'))),

                ev e1 c1 ->
                ev e2 c2 ->
                ev (bindexp e1 e2) (bindval c1 c2)
  | ev_return : forall o
                       (e : Exp nil (Stype o))
                       (c : Val nil (Stype o)),
                  ev e c ->
                  ev (returnexp e) (returnval c).

(* these could be replaced by saying
   ev_val : forall {o} (e : /etc/) ...
 *)

Arguments ev_val {_} _.
Arguments ev_app {_ _ _ _ _ _ _} _ _ _.
Arguments ev_bind {_ _ _ _ _} _ _ _.
Arguments ev_return {_ _ _} _.



Inductive evs : forall {o: Mtype},
    Unit
    -> Val nil (Meastype o)
    -> Val nil (Stype o)
    -> Weight
    -> Prop :=
| evs_unif : forall {u},
               evs u (uniformval) (constexp (unit_real u)) one_weight
| evs_return : forall {o u} {c: Val nil (Stype o)},
                 evs u (returnval c) c one_weight
| evs_bind : forall {u a b}
                    {c1 : Val nil (Meastype a)} 
                    {c2 : Val nil (Funtype (Stype a)(Meastype b))}
                    {c3 c4 c5 w1 w2},
               evs (left_half u) c1 c3 w1 ->
               ev (appexp (valexp c2) (valexp c3)) c4 ->
               evs (right_half u) c4 c5 w2 ->
               evs u (bindval c1 c2) c5 (prod_weights w1 w2)
| evs_dist : forall {p u},
    evs u (distval (constexp p))
        (constexp (unit_real u))
        (density_1 p (unit_real u)).
                    



