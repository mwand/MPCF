(* Sampling Semantics *)

(* For Importance Sampling, a sample consists of a value and a weight *)

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

Function den_typeS (t : Otype) : Type :=
  match t with
    | Stype m => (den_Mtype m)
    | Funtype t u => (den_typeS t) -> (lifted (den_typeS u))
    | Meastype m => Unit -> lifted ((den_Mtype m) * Weight)
  end. 

Function seq2 {A B C : Type}
         (d1 : lifted A)
         (d2 : lifted B)
         (f : (A -> B -> lifted C))
         : lifted C
  :=
    (strict d1 (fun a => (strict d2 (fun b => (f a b))))).

Function bindopS {a b : Mtype}
         (s : den_typeS (Meastype a))
         (f : den_typeS (Funtype (Stype a) (Meastype b)))
         : (den_typeS (Meastype b)) :=
  (fun (u:Unit) =>
     (strict2
        (s (left_half u))
        (fun a w1 =>
           (strict
              (f a)
              (fun s2 => (strict2
                            (s2 (right_half u))
                            (fun b w2 => (lift
                                            (b, (prod_weights w1 w2)))))))))).

Hint Unfold bindopS.

Function returnopS {m} (v : den_typeS (Stype m)) : (den_typeS (Meastype m))
  := fun u => (lift (v, one_weight)).
Hint Unfold returnopS.

Definition uniformopS : (den_typeS (Meastype Real_type))
  := fun u => (lift ((unit_real u), one_weight)).
Hint Unfold uniformopS.

Definition distvalS : real -> (den_typeS (Meastype Real_type))
  := fun p u => (lift ((unit_real u), (density_1 p (unit_real u)))).
Hint Unfold distvalS.


Definition obsvalS : (den_typeS (Stype Real_type)) ->
                     (den_typeS (Stype Real_type)) ->
                     (den_typeS (Meastype Empty_type)) :=
  fun r x => fun u => lift (tt, (density_1 r x)).



(* Coercion, needed to make den_val typecheck *)
Function coerce_realS (w : real) : (den_typeS (Stype Real_type)) := w.
Hint Unfold coerce_realS.

(* Denotations of Values and Expressions in the Sampling Semantics*)

Function den_valS {G o} (val : Val G o) (r : (@den_env den_typeS G))
         : (den_typeS o)
  :=
    match val with
    | constexp w => (coerce_realS w)
    | varexp var => (apply_env r var)
    | absexp e => (fun val => den_expS e (cons_env val r))
    | uniformval => uniformopS
    | distval v => distvalS (den_valS v r)
    | bindval s f => bindopS (den_valS s r) (den_valS f r)
    | returnval v => returnopS (den_valS v r)
    | prodval v1 v2 => ((den_valS v1 r), (den_valS v2 r))
    | obsval v1 v2 => obsvalS (den_valS v1 r) (den_valS v2 r)
    | unitval => tt
    end
with
den_expS {G o} (exp : (Exp  G o)) (r : (den_env G)) : (lifted (den_typeS o))
  :=
  match exp with
  | valexp val => lift (den_valS val r)
  | prodexp e1 e2 => seq2 (den_expS e1 r) (den_expS e2 r)
                          (fun v1 v2 => (lift (v1, v2)))
  | proj1exp e => strict (den_expS e r) (fun p => (lift (fst p)))
  | proj2exp e => strict (den_expS e r) (fun p => (lift (snd p)))
  | appexp e1 e2 => seq2 (den_expS e1 r) (den_expS e2 r) (fun f a => (f a))
  | returnexp e1 => strict (den_expS e1 r)
                           (fun a => (lift (returnopS a)))
  | bindexp e1 e2 => seq2 (den_expS e1 r) (den_expS e2 r)
                          (fun s f => (lift (bindopS s f)))
  end.

