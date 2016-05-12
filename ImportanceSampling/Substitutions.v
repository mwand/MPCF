(* Substitutions and Renamings, following Benton-Hur-Kennedy-Varming *)

Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.

Require Import EqNat. 

Require Import LiftedTypes.
Require Import MyReals.
Require Import Types.
Require Import Syntax.



(* **************** Substitutions **************** *)

(* Substitutions: following Benton-Hur-Kennedy *)

(* A Subst G G' is a function that takes an o, a o-valued variable in *)
(*    G and returns an o-valued value that is  well-typed in G'  *)

(* It would be nice to represent a substitution as a heterogenous list,
   like we did for value environments, but I couldn't make this work. 
   We will, however, use subst_lookup as an interface in most 
   (if not all) places. *)

Definition Subst G G': Type := forall o, Var G o -> Val G' o.

Function subst_lookup {G G' o}
         (var: Var G o)
         (s : Subst G G')
: (Val G' o)
  :=
    (s o var).

Definition id_subst {G} : Subst G G := fun o var => varexp var.

(* (cons_subst val s)(var0) = val, *)
(* (cons_subst val s)(var_n) = s(var(n-1)) *)

Program Definition cons_subst {G G' o}  (* fixpoint doesn't work here, I *)
                                        (* don't know why *)
         (val : Val G' o)
         (s : Subst G G')
: (Subst (o::G) G') :=
  fun o' (var : Var (o::G) o') =>
    match var with
      | var_0 => val
      | var_S v' => s _ v'
    end.

(*  singleton substitution [val/*1*] *)
Function subst1 {G o} (val : Val G o) : (Subst (o::G) G) :=
  (cons_subst val id_subst).


Definition hd_subst {G G':Tyenv}{o}
           (s : Subst (o::G) G')
: Val G' o := subst_lookup var_0 s.


Definition tl_subst {G G' o}
           (s : Subst (o::G) G')
: Subst G G'
  :=
    fun o' v => s o' (var_S v).

(* **************** Renamings **************** *)

(* We want to substitute inside abstractions, but we don't have enough *)
(* operations on substitutions yet. *)

(* We eventually need to deal with grotty details of deBruijn
   shifting.  To do this, we follow BKV and introduce Renamings 
   as a way of operating on the results of substitutions.
*)

(* A Renaming G G' is a function from variables defined over G to *)
(* variables defined over G' *)

Definition Renaming G G' := forall o, Var G o -> Var G' o.

Definition id_renaming G : Renaming G G := fun o v => v.

(* rename var_0 to var, others as per renaming r *)

Program Definition cons_renaming {G G' o}
        (var : Var G' o)
        (r : Renaming G G')
: (Renaming (o::G) G')
   := fun o' (in_var : Var (o::G) o') =>
        match in_var with
          | var_0 => var
          | var_S v' => r o' v'
        end.

(* pad_renaming: Given that we have a renaming r from G to G', 
   renames (var_0 (o::G)) to (var_0 (o::G')), renames other variables 
   according to r *)

Program Definition pad_renaming {G G' o} (ren : Renaming G G')
: (Renaming (o::G) (o::G'))
  :=
    fun o' v =>
      match v with
        | var_0  => var_0 
        | var_S  v' => var_S (ren _ v')
      end.

(* apply renaming.  Our naming convention calls these ap and ap_Re *)

Fixpoint ap_Rv {G G' o} (ren : Renaming G G')
         (val : Val G o) : (Val G' o) :=
  match val with
  | varexp var => varexp (ren _ var)
  | prodval v1 v2 => prodval (ap_Rv ren v1) (ap_Rv ren v2)
  | absexp e => absexp (ap_Re (pad_renaming ren) e)
  | constexp n => constexp n 
  | uniformval => uniformval
  | bindval v1 v2 => bindval (ap_Rv ren v1) (ap_Rv ren v2)
  | returnval v => returnval (ap_Rv ren v)
  | distval v => distval (ap_Rv ren v)
  end
with
ap_Re {G G' o} (ren : Renaming G G') (exp : Exp G o)
: (Exp G' o) :=
  match exp with
  | valexp val => valexp (ap_Rv ren val)
  | prodexp e1 e2 => prodexp (ap_Re ren e1) (ap_Re ren e2)
  | proj1exp e1 => proj1exp (ap_Re ren e1)
  | proj2exp e1 => proj2exp (ap_Re ren e1)
  | appexp e1 e2 => appexp (ap_Re ren e1) (ap_Re ren e2)
  | bindexp e1 e2 => bindexp (ap_Re ren e1) (ap_Re ren e2)
  | returnexp e1 => returnexp (ap_Re ren e1)
  end.

Hint Resolve ap_Rv ap_Re.

(* GIVEN: subst : Subst G G',  *)
(* RETURNS: a new substitution, with var0 bound to var0:o, and 
   var(n+1) bound to (subst var(n)), with all the variables incremented by 1 *)

Program Definition shift_subst {G G' o}
        (subst : Subst G G') : (Subst (o::G) (o::G')) 
   :=
     fun _ var =>
       match var with
         | var_0 => varexp var_0
         | var_S var' => ap_Rv  (* increment variables in the range of subst *)
                                 (fun _ var'' => var_S var'')
                                 (subst _ var')
       end.

(* applying a substitution to a value or exp *)

Fixpoint ap_Sv {G G' o} (s : Subst G G') (val : Val G o) : (Val G' o)
  :=
    match val with
    | constexp n => constexp n
    | prodval v1 v2 => prodval (ap_Sv s v1) (ap_Sv s v2)
      | varexp var => subst_lookup var s
      | absexp e => absexp (ap_Se (shift_subst s) e)
      | uniformval => @uniformval _
      | bindval e1 e2 => bindval (ap_Sv s e1) (ap_Sv s e2)
      | returnval v => returnval (ap_Sv s v)
      | distval v => distval (ap_Sv s v)
    end
with
ap_Se {G G' o} (s : Subst G G') (e : Exp G o) : (Exp G' o)
:=
  match e with
  | valexp val => valexp (ap_Sv s val)
  | prodexp e1 e2 => prodexp (ap_Se s e1) (ap_Se s e2)
  | proj1exp e1 => proj1exp (ap_Se s e1)
  | proj2exp e1 => proj2exp (ap_Se s e1)
  | appexp e1 e2 => appexp (ap_Se s e1) (ap_Se s e2)
  | bindexp  e1 e2 => bindexp (ap_Se s e1) (ap_Se s e2)
  | returnexp e1 => returnexp (ap_Se s e1)
  end.

Hint Resolve ap_Sv ap_Se.

(* compositions of renamings and substitutions.  All are right-to-left *)

Definition c_RR {E E' E''} (r : Renaming E' E'') (r' : Renaming E E') := 
  (fun t v => r t (r' t v)) : Renaming E E''.

Definition c_SR {E E' E''} (s : Subst E' E'') (r : Renaming E E')  := 
  (fun t v => s t (r  t v)) : Subst E E''.

Definition c_RS {E E' E''} (r : Renaming E' E'') (s : Subst E E')  := 
  (fun t v => ap_Rv r (s t v)) : Subst E E''.

Definition c_SS {E E' E''} (s : Subst E' E'') (s' : Subst E E') := 
  (fun t v => ap_Sv s (s' t v)) : Subst E E''.



(* Tactic From BKV: applies functional_extensionality twice
   -- useful for substitutions, which take two arguments *)
Ltac ExtVar :=
 match goal with
    [ |- ?X = ?Y ] => 
    (apply (@functional_extensionality_dep _ _ X Y) ; 
     let t := fresh "t" in intro t;
     apply functional_extensionality; 
     let v := fresh "v" in intro v; 
     dependent destruction v; auto) 
 end.

Ltac Rewrites E := 
  (intros; simpl; try rewrite E; 
   repeat (match goal with | [H:context[_=_] |- _] => rewrite H end); 
   auto).


(* **************************************************************** *)

(* ***** Algebraic Properties of substitutions and renamings  ***** *)

(* The object of this part of the development is to get to ap_cSS_e, which 
   describes how application distributes over composition of substitutions. 
   *)

Lemma shift_id_subst : forall E t,
                         shift_subst (@id_subst E) = @id_subst (t::E). 
Proof. intros. ExtVar. Qed.

Lemma ap_Sv_id :
  forall G o (e : Val G o), ap_Sv id_subst e = e. 
Proof.
  apply (val_exp_rec
           (fun E t (e : Exp E t) => ap_Se id_subst e = e)
           (fun E t (v : Val E t) => ap_Sv id_subst v = v));
  intros; simpl; eauto; try rewrite H; try rewrite H0; auto.
  rewrite shift_id_subst.
  rewrite H.
  auto.
Qed.

(* pad distributes over composition of renamings *)
Lemma pad_cRR : forall G G' G'' o
                            (r : Renaming G' G'')
                            (r' : Renaming G G'),
                       (pad_renaming (o:=o)
                          (c_RR r r')) =
                       (c_RR (pad_renaming r)
                             (pad_renaming r')).
Proof.  intros.  ExtVar. Qed.

Lemma ap_cRR_v :
  forall G t (e: Val G t) G' G''
         (r : Renaming G' G'')
         (r' : Renaming G G'),
    (ap_Rv (c_RR r r') e) =
    (ap_Rv r (ap_Rv r' e)).
Proof.
  apply (val_exp_rec
           (fun G t (e : Exp G t) =>
              forall G' G''
                     (r : Renaming G' G'')
                     (r' : Renaming G G'),
                (ap_Re (c_RR r r') e) = (ap_Re r (ap_Re r' e)))
           (fun G t (v : Val G t) =>
              forall G' G''
                     (r : Renaming G' G'')
                     (r' : Renaming G G'),
                (ap_Rv (c_RR r r') v) = (ap_Rv r (ap_Rv r' v))));
  Rewrites pad_cRR.
Qed.

Lemma shift_cSR :
  forall G G' G'' o
         (s : Subst G' G'') (r: Renaming G G'),
    shift_subst (o:=o) (c_SR s r)
    = c_SR (shift_subst s) (pad_renaming r).
Proof. intros. ExtVar. Qed.

Lemma ap_cSR_v : forall E t (e:Val E t) E' E''
                        (s:Subst E' E'')
                        (r:Renaming E E'), 
                   ap_Sv (c_SR s r) e = ap_Sv s (ap_Rv r e).
Proof.
  apply (val_exp_rec
           (fun E t (e : Exp E t) =>
              forall  E' E''
                      (s:Subst E' E'') (r:Renaming E E'), 
                ap_Se (c_SR s r) e = ap_Se s (ap_Re r e))
           (fun E t (v : Val E t) =>
              forall  E' E''
                      (s:Subst E' E'') (r:Renaming E E'), 
                ap_Sv (c_SR s r) v = ap_Sv s (ap_Rv r v)));
  (intros; Rewrites H; Rewrites shift_cSR).
Qed.

Lemma shift_cRS : forall G0 G1 G2 o
                         (r : Renaming G1 G2)
                         (s : Subst G0 G1),
                    shift_subst (o:=o) (c_RS r s)
                    = c_RS (pad_renaming r) (shift_subst s).
Proof.
  intros.
  ExtVar.
  unfold c_RS. 
  simpl.       
  unfold shift_subst.
  simpl.
  rewrite <-  2 ap_cRR_v.
  unfold c_RR.
  simpl.
  reflexivity.
Qed.

Lemma ap_cRS_v : forall
                   G o (e : Val G o) G' G''
                   (r : Renaming G' G'')
                   (s : Subst G G'),
                 (ap_Sv (c_RS r s) e) = (ap_Rv r (ap_Sv s e)).
Proof.
  apply (val_exp_rec
           (fun G o (e : Exp G o) =>
              forall G' G''
                     (r : Renaming G' G'')
                     (s : Subst G G'),
                (ap_Se (c_RS r s) e)
                = (ap_Re r (ap_Se s e)))
           (fun G o (e : Val G o) =>
              forall G' G''
                     (r : Renaming G' G'')
                     (s : Subst G G'),
                (ap_Sv (c_RS r s) e)
                = (ap_Rv r (ap_Sv s e)))); Rewrites shift_cRS.
Qed.



Lemma shift_cSS :
  forall G G' G'' o
         (s: Subst G' G'')
         (s' : Subst G G'),
    (shift_subst (o:=o) (c_SS s s'))
    = (c_SS (shift_subst s) (shift_subst s')).
Proof.
  intros.
  ExtVar.
  simpl.
  unfold c_SS.
  simpl.
  rewrite <- ap_cRS_v.
  rewrite <- ap_cSR_v.
  auto.   (* not sure what this is doing here, 
             but I'm too tired to investigate. *) 
Qed.

Lemma ap_cSS_e: forall G o (e : Exp G o) G' G''
                       (s : Subst G' G'')
                       (s': Subst G G'),
                  (ap_Se (c_SS s s') e)
                    = (ap_Se s (ap_Se s' e)).
Proof.
  apply (exp_val_rec
            (fun G o (exp: Exp G o) =>
                 forall G' G'' (s : Subst G' G'')
                        (s': Subst G G'),
                   (ap_Se (c_SS s s') exp)
                   = (ap_Se s (ap_Se s' exp)))
            (fun G o (val: Val G o) =>
                 forall G' G'' (s : Subst G' G'')
                        (s': Subst G G'), 
                   (ap_Sv (c_SS s s') val)
                   = (ap_Sv s (ap_Sv s' val))));
  Rewrites shift_cSS.
Qed.


Lemma cSS_subst1 : forall G o (val : Val G o) G',
                   forall (s : Subst G' G),
                     (c_SS (subst1 val) (shift_subst s))
                     = (cons_subst val s).
Proof.
  intros.
  unfold c_SS.
  ExtVar.
  simpl.
  rewrite <- ap_cSR_v.
  unfold c_SR.
  simpl.
  assert (H0 : (fun t var => @id_subst G t var) = id_subst) by ExtVar.
  rewrite H0.
  rewrite ap_Sv_id.
  reflexivity.
Qed.

