(* Expressions and Values *)

Require Import MyReals.
Require Import Types.

(* We distinguish syntactically between Values (canonical forms) 
   and general expressions.  These are mutually recursive, 
   because of abstractions. *)

(* Expressions and Values of type o, with free variables drawn from G *)

Inductive Exp G : Otype -> Type :=
| valexp : forall o, Val G o -> Exp G o
| prodexp : forall m m', Exp G (Stype m) -> Exp G (Stype m') ->
                         Exp G (Stype (Prod_type m m'))
| proj1exp : forall m m', Exp G (Stype (Prod_type m m'))
                          -> Exp G (Stype m)
| proj2exp : forall m m', Exp G (Stype (Prod_type m m'))
                          -> Exp G (Stype m')                                 
| appexp : forall (a b : Otype),
             (Exp G (Funtype a b)) -> (Exp G a) -> (Exp G b)
| bindexp : forall (o o' : Mtype),  Exp G (Meastype o) ->
                        Exp G (Funtype (Stype o) (Meastype o')) ->
                        Exp G (Meastype o')
| returnexp : forall (o : Mtype), Exp G (Stype o)
                                  -> Exp G (Meastype o)
with
Val G : Otype -> Type :=
| constexp : real -> Val G (Stype Real_type)
| prodval : forall m m', Val G (Stype m) -> Val G (Stype m')
                         -> Val G (Stype (Prod_type m m'))
| varexp : forall o, Var G o -> Val G o 
| absexp : forall (o o': Otype),
             (Exp (cons o G) o') -> (Val G (Funtype o o'))
| uniformval : Val G (Meastype Real_type)
| distval : Val G (Stype Real_type) -> Val G (Meastype Real_type)  (* some non-uniform distribution: *) 
 
| bindval : forall o o', Val G (Meastype o) ->
                         Val G (Funtype
                                  (Stype o)
                                  (Meastype o')) ->
                        Val G (Meastype o')
| returnval : forall a, Val G (Stype a) -> Val G (Meastype a).

Arguments valexp {G o} _.
Arguments prodexp {G m m'} _ _.
Arguments proj1exp {G m m'} _.
Arguments proj2exp {G m m'} _.
Arguments appexp {G a b} _ _.
Arguments bindexp {G o o'} _ _.
Arguments returnexp {G o} _.
Arguments constexp {G} _.
Arguments varexp {G o} _.
Arguments prodval {G m m'} _ _.
Arguments absexp {G o o'} _.
Arguments uniformval {G}.
Arguments distval {G} _.
Arguments bindval {G o o'} _ _.
Arguments returnval {G a} _.

(* Coq doesn't generate the correct mutual induction hypotheses
   for these, so we have to help it along. *)

Scheme exp_val_rec := Induction for Exp Sort Prop
with
val_exp_rec := Induction for Val Sort Prop.
