(* Measure Semantics *)

Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.


Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import LiftedTypes.
Require Import Weights.
Require Import MyReals. (* including times: Weight -> real -> real *)
Require Import Measures.
Require Import Types.   (* including variables and environments *)
Require Import Syntax.


Function den_typeM (t : Otype) : Type :=
  match t with
    | Stype m => (den_Mtype m)
    | Funtype t u => (den_typeM t) -> (lifted (den_typeM u))
    | Meastype m => Measure (den_Mtype m)
  end.  

Function strict2 {A B C : Type}
         (d1 : lifted A)
         (d2 : lifted B)
         (f  : A -> B -> lifted C)
         : lifted C
  :=
    (strict d1 (fun a => (strict d2 (fun b => (f a b))))).



(* turn fn u => u into an integrator *)
Definition uniformopM : (den_typeM (Meastype Real_type))
  := fun k => mu_L (fun u => k (unit_real u)).
Hint Unfold uniformopM.

(* Definition distvalM : (den_typeM (Meastype Real_Mtype)) *)
(*   := mu_1. *)
(* Hint Unfold distvalM. *)

Definition returnopM {m : Mtype}
           (v : (den_Mtype m)) : (den_typeM (Meastype m))
  :=
    fun k => k v.
Hint Unfold returnopM.

Definition bindopM
           {o o' : Mtype}
           (mu : (den_typeM (Meastype o)))
           (f :  (den_typeM (Stype o)) -> 
                 (lifted (den_typeM (Meastype o'))))
           : (den_typeM (Meastype o'))
  := fun (k : (den_typeM (Stype o')) -> real)
     => mu (fun a => strict0 (f a) (fun mu' => (mu' k))).
Hint Unfold bindopM.

(* Coercion, needed to make den_val typecheck *)
Function coerce_realM (w : real) : (den_typeM (Stype Real_type)) := w.
Hint Unfold coerce_realM.


(* The denotations of values and expressions in the measure semantics *)

Function den_valM {G o} (val : Val G o) (r : (@den_env den_typeM G))
         : (den_typeM o)
  :=
    match val with
    | constexp w => (coerce_realM w)
    | prodval v1 v2 => (den_valM v1 r, den_valM v2 r)
      | varexp var => (apply_env r var)
      | absexp e => (fun val => den_expM e (cons_env val r))
      | uniformval => uniformopM
      | distval v => mu_1 (den_valM v r)
      | bindval s f => bindopM (den_valM s r) (den_valM f r)
      | returnval v => returnopM (den_valM v r)
    end
with
den_expM {G o} (exp : (Exp  G o)) (r : (den_env G)) : (lifted (den_typeM o))
:=
  match exp with
  | valexp val => lift (den_valM val r)
  | prodexp e1 e2 => strict2 (den_expM e1 r) (den_expM e2 r)
                             (fun v1 v2 => (lift (v1, v2)))
  | proj1exp e => strict (den_expM e r) (fun p => (lift (fst p)))
  | proj2exp e => strict (den_expM e r) (fun p => (lift (snd p)))
  | appexp e1 e2 => strict2 (den_expM e1 r) (den_expM e2 r) (fun f a => (f a))
  | returnexp e1 => strict (den_expM e1 r)
                           (fun a => (lift (returnopM a)))
  | bindexp e1 e2 =>  strict2 (den_expM e1 r) (den_expM e2 r)
                              (fun s f => (lift (bindopM s f)))
  end.
