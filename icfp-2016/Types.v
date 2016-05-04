(* types of the object language *)
(* and environments *)

Require Import Coq.Lists.List.

Require Import LiftedTypes.
Require Import Weights.
Require Import MyReals.                   (* including times: Weight -> real -> real *)
Require Import Measures.


(* Measurable types *)

Inductive Mtype : Type :=
| Real_Mtype : Mtype
| Prod_Mtype : Mtype -> Mtype -> Mtype.


(* denotations of measurable types: same for both *)

Function den_Mtype (m : Mtype) : Type :=
  match m with
  | Real_Mtype => real
  | Prod_Mtype m1 m2 => (den_Mtype m1) * (den_Mtype m2)
  end.
    
Inductive Otype : Type :=
| M_Otype : Mtype -> Otype (* injection *)
| Funtype : Otype -> Otype -> Otype
(* | Prod_Otype : Otype -> Otype -> Otype *)
| Meastype : Mtype -> Otype.    (* Meas A *)
                          

(* Environments *)

Definition Tyenv := list Otype.

(* den_env G is the type of value environments compatible with G *)

Fixpoint den_env {den_type : Otype -> Type}(G : Tyenv) : Type :=
  match G with
    | nil => unit
    | (cons o G') =>  (den_type o) * (@den_env den_type G')
  end.

Function cons_env {o}{G : Tyenv} {den_type : Otype -> Type} (d : den_type o) (r : den_env G) 
: (den_env (o::G)) := (d, r).

(* Represent variables following Benton, Kennedy, and Varming*)

(* v : Var G o iff v is a variable of type o in G *)
(* the n-th variable in (Var G o) is, roughly speaking, a proof that the
   the n-th position in G is of type o. *)

Inductive Var : Tyenv -> Otype -> Type :=
| var_0 : forall (G : Tyenv) (o : Otype), Var (cons o G) o
| var_S : forall G o o', Var G o -> Var (cons o' G) o.

Fixpoint env_lookup
         {G : Tyenv}
         {o : Otype}
         {den_type : Otype -> Type}
         (v : Var G o) : (den_env G) -> (den_type o) 
:=  match v 
  with
    | var_0 _ _ => fun venv => fst venv
    | var_S _ _ _ v'  => fun venv => env_lookup v' (snd venv)
    end.

(* Simply reversing the arguments to env_lookup doesn't work, so
   apply_env has to call env_lookup *)

Definition apply_env
         {G : Tyenv}
         {o : Otype}
         {den_type : Otype -> Type}
         (r : den_env G)
         (v : Var G o) : (den_type o) 
  :=  env_lookup v r.
