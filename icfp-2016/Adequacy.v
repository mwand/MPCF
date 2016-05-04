(* now let's do the termination proof *)

Require Import List.
Require Import Program.
Require Import FunctionalExtensionality.
Require Import EqNat. 

(* BKH sets these.  I don't knowhow to get it to work without them *)
Set Implicit Arguments.         
Set Asymmetric Patterns.

(* This doesn't seem to do anything:    *)
(* Set Elimination Schemes. *)

(* **************************************************************** *)

Inductive lifted (X : Type): Type :=
  | bottom : lifted X
  | lift : X -> lifted X.

Definition strict  {X: Type} {Y : Type} (v :lifted X)  (f : X -> (lifted Y)) : (lifted Y) :=
  match v with
    | bottom  => bottom Y
    | lift x => (f x)
  end.

(* Object Types *)

Inductive Otype : Type :=
| Inttype : Otype              
| Arrtype : Otype -> Otype -> Otype.

(* Denotations of object types *)

Function den_type (t : Otype) : Type :=
  match t with
    | Inttype => nat
    | Arrtype t u => (den_type t) -> (lifted (den_type u))
  end.

(* **************** Environments **************** *)

Definition Tyenv := list Otype.

(* den_env G is the type of value environments compatible with G *)

Fixpoint den_env (G : Tyenv) : Type :=
  match G with
    | nil => unit
    | (cons o G') =>  (den_type o) * (den_env G')
  end.

Function cons_env {o}{G : Tyenv} (d : den_type o) (r : den_env G) 
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
         (r : den_env G)
         (v : Var G o) : (den_type o) 
:=  env_lookup v r.

(* **************************************************************** *)

(* Expressions and Values *)

(* We distinguish syntactically between Values (canonical forms) 
   and general expressions.  These are mutually recursive, 
   because of abstractions. *)

(* Expressions and Values of type o, with free variables drawn from G *)

Inductive Exp G : Otype -> Type :=
| valexp : forall o, Val G o -> Exp G o
| appexp : forall (a b : Otype),
             (Exp G (Arrtype a b)) -> (Exp G a) -> (Exp G b) 
with
Val G : Otype -> Type :=
| constexp : nat -> Val G Inttype
| varexp : forall o, Var G o -> Val G o 
| absexp : forall (o o': Otype),
             (Exp (cons o G) o') -> (Val G (Arrtype o o')).

(* Coq doesn't generate the correct mutual induction hypotheses
   for these, so we have to help it along. *)

Scheme exp_val_rec := Induction for Exp Sort Prop
with
val_exp_rec := Induction for Val Sort Prop.

(* Denotational Semantics *)

Function cbv  {A : Type}{B : Type} 
                 (d: lifted (A -> (lifted B)))
                 (d': lifted A) : lifted B :=
  strict d (fun f => strict d' (fun a => (f a))).

(* Coercion, needed to make den_val typecheck *)
Function coerce_int (n : nat) : (den_type Inttype) := n.

(* Denotations of Values and Expressions *)

Function den_val {G o} (val : Val G o) r : (den_type o)
  :=
    match val with
      | constexp n => (coerce_int n)
      | varexp  _ var => (apply_env r var)
   (* | absexp o' o e => (fun val => den_exp e (val, r)) *)
      | absexp o' o e => (fun val => den_exp e (cons_env val r))                    
    end
with
den_exp {G o} (exp : (Exp  G o)) (r : (den_env G)) : (lifted (den_type o))
  :=
  match exp with
    | valexp _ val => lift (den_val val r)
    | appexp _ _ e1 e2 => cbv (den_exp e1 r) (den_exp e2 r)
  end.

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
      | var_0 _ _ => val
      | var_S _ _ _ v' => s _ v'
    end.

(*  singleton substitution [val/*1*] *)
Function subst1 {G o} (val : Val G o) : (Subst (o::G) G) :=
  (cons_subst val id_subst).


Definition hd_subst {G G':Tyenv}{o}
           (s : Subst (o::G) G')
: Val G' o := subst_lookup (var_0 _ _) s.


Definition tl_subst {G G' o}
           (s : Subst (o::G) G')
: Subst G G'
  :=
    fun o' v => s o' (var_S o v).

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
          | var_0 _ _ => var
          | var_S _ _ _ v' => r o' v'
        end.

(* pad_renaming: Given that we have a renaming r from G to G', 
   renames (var_0 (o::G)) to (var_0 (o::G')), renames other variables 
   according to r *)

Program Definition pad_renaming {G G' o} (ren : Renaming G G')
: (Renaming (o::G) (o::G'))
  :=
    fun o' v =>
      match v with
        | var_0 _ _  => var_0 _ _
        | var_S _ _ _ v' => var_S _ (ren _ v')
      end.

(* apply renaming.  Our naming convention calls these ap and ap_Re *)

Fixpoint ap_Rv {G G' o} (ren : Renaming G G')
         (val : Val G o) : (Val G' o) :=
  match val with
    | varexp _ var => varexp (ren _ var)
    | absexp _ _ e => absexp (ap_Re (pad_renaming ren) e)
    | constexp n => @constexp _ n 
  end
with
ap_Re {G G' o} (ren : Renaming G G') (exp : Exp G o)
: (Exp G' o) :=
  match exp with
    | valexp _ val => valexp (ap_Rv ren val)
    | appexp _ _ e1 e2 => appexp (ap_Re ren e1) (ap_Re ren e2)
  end.

(* GIVEN: subst : Subst G G',  *)
(* RETURNS: a new substitution, with var0 bound to var0:o, and 
   var(n+1) bound to (subst var(n)), with all the variables incremented by 1 *)

Program Definition shift_subst {G G' o}
        (subst : Subst G G') : (Subst (o::G) (o::G')) 
   :=
     fun _ var =>
       match var with
         | var_0 _ _ => varexp (var_0 _ _)
         | var_S _ _ _ var' => ap_Rv  (* increment variables in the range of subst *)
                                 (fun _ var'' => var_S _ var'')
                                 (subst _ var')
       end.

(* applying a substitution to a value or exp *)

Fixpoint ap_Sv G G' o (s : Subst G G') (val : Val G o) : (Val G' o)
  :=
    match val with
      | constexp n => constexp G' n
      | varexp _ var => subst_lookup var s
      | absexp o o' e => absexp (ap_Se (shift_subst s) e)
    end
with
ap_Se G G' o (s : Subst G G') (e : Exp G o) : (Exp G' o)
:=
  match e with
    | valexp _ val => valexp (ap_Sv s val)
    | appexp _ _ e1 e2 => appexp (ap_Se s e1) (ap_Se s e2)
  end.

(* compose renamings and compositions.  All are right-to-left *)

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
           (fun E t (v : Val E t) => ap_Sv id_subst v = v)).
  intros.
  simpl.
  rewrite H.
  reflexivity.

  intros. simpl.
  rewrite H.
  rewrite H0.
  reflexivity.

  intros.
  auto.                         (* does simpl; reflexivity *)

  intros.
  auto.  (* does simpl; unfold*; reflexivity *)

  intros.
  simpl.
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



(* **************************************************************** *)

(* And, at last, the operational semantics!!!! *)


Inductive ev : forall (o: Otype), Exp nil o -> Val nil o -> Prop :=
  | ev_val : forall o (val: Val nil o), ev (valexp val) val
  | ev_app : forall o o' (e1 : Exp nil (Arrtype o o'))
                    (e2 : Exp nil o)
                    e' v w,
               ev e1 (absexp e')
               -> ev e2 v
               -> ev (ap_Se (subst1 v) e') w
               -> ev (appexp e1 e2) w.



(* **************************************************************** *)

(* The Logical Relation *)

(* Defined as a fixed point over Otypes and lifted Otypes *)

Definition EqInt : (den_type Inttype) -> nat -> Prop :=
  fun n1 n2 => (n1 = n2).

(* General recipe for lifting a relation *)
(* (liftRel o R d e) iff d is bottom or d = lift(a) and e evaluates to *)
(* a value v such (Rel a v) holds*) 

Function lift_Rel (o : Otype) (R : (den_type o) -> (Val nil o) -> Prop)
: (lifted (den_type o)) -> (Exp nil o) -> Prop :=
  fun d e =>
    match d with
      | bottom => True
      | lift a => exists v, ev e v /\ R a v
    end.

Definition  FunRel {o1 o2}
            (Rel1 : (den_type o1) -> (Val [] o1) -> Prop)
            (Rel2 : (lifted (den_type o2)) -> (Exp [] o2) -> Prop)
            (f1 : (den_type o1) -> (lifted (den_type o2)))
            (val1 : Val nil (Arrtype o1 o2))
: Prop :=
  exists e, val1 = absexp e /\
  forall (a1 : den_type o1) (val2: Val [] o1),
    (Rel1 a1 val2) ->
    (Rel2 (f1 a1) (ap_Se (subst1 val2) e)).

(* for some reason, Coq thinks this makes the first argument to Rel implicit  *)
Fixpoint Rel (o : Otype) : (den_type o) -> (Val nil o) -> Prop :=
 match o with
    | Inttype => fun d val => match val with
                       | constexp n => EqInt d n
                       | _ => False
                     end
    | Arrtype o1 o2 =>
      fun (f1 : den_type (Arrtype o1 o2))
           (val1 : Val nil (Arrtype o1 o2)) =>
         FunRel (@Rel o1)  (lift_Rel (@Rel o2)) f1 val1
 end.


Fixpoint Rel_Env G : (den_env G) -> (Subst G nil) -> Prop :=
  match G with
    | nil => fun r s => True
    | (o :: G') => fun (r : den_env (o::G')) s =>
                     @Rel o (fst r) (hd_subst s)
                     /\ @Rel_Env G' (snd r) (tl_subst s)
  end.

Lemma lookup_preserves_Rel : forall G (o : Otype)
                       (var : Var G o)
                       (r : den_env G)
                       (s : Subst G nil),
                                Rel_Env r s
                                -> Rel (apply_env r var) (s _ var).
Proof.
  intros.
  induction G as [| o' G'].
  (* G = [] *)
  inversion var.
  (* G = o' :: G' *)
  induction var as [| G''].
  (* var = var_0 *)
  simpl.
  inversion H.
  apply H0.
  (* var = var_S v' *)
  apply (IHvar (snd r) (tl_subst s)).
  apply H.
  intros.
  apply IHG'.
  apply H0.
Qed.

Lemma extend_env_preserves_Rel :
  forall (o: Otype) G r (s : Subst G nil) (d : den_type o) (val: Val nil o),
    Rel_Env r s -> Rel d val
    -> Rel_Env (cons_env d r) (cons_subst val s).
Proof.
  intros.
  simpl.
  split.
  apply H0.
  apply H.
Qed.

(* **************************************************************** *)

(* The Fundamental Theorem *)


Definition Fun_Thm_Exp G o  (exp: Exp G o) :=
  forall         
         (r : den_env G)
         (s : Subst G nil),
    Rel_Env r s
    -> lift_Rel (@Rel o) (den_exp exp r) (ap_Se s exp).

Definition Fun_Thm_Val G o   (val: Val G o):= 
  forall 
        
         (r : den_env G)
         (s : Subst G nil),
    Rel_Env r s
    -> @Rel o (den_val val r) (ap_Sv s val).

Theorem Fund_Thm: forall G o exp, @Fun_Thm_Exp G o exp.
Proof.
  apply (exp_val_rec Fun_Thm_Exp Fun_Thm_Val).

  (*valexp*)
  intros.
  unfold Fun_Thm_Exp.
  intros.
  simpl.
  exists (ap_Sv s v).
  split.
  apply ev_val.
  { destruct v.
    (* constexp *)
    simpl.
    unfold EqInt.
    reflexivity.
    (* varexp *)
    simpl.
    apply lookup_preserves_Rel.
    apply H0.
    (* absexp *)
    apply H.
    apply H0.
    }
  { (* appexp e1 e2 *)
    intros.
    unfold Fun_Thm_Exp.
    intros.
    unfold Fun_Thm_Exp in H.
    unfold Fun_Thm_Exp in H0.
    specialize (H _ _ H1).
    specialize (H0 _ _ H1).
    simpl.
    destruct (den_exp e r) eqn: eqe.
    simpl in H.
    destruct (den_exp e0 r) eqn: eqe0.
    simpl.
    apply I.
    simpl.
    apply I.
    simpl.
    destruct (den_exp e0 r) eqn: eqe0.
    simpl.
    apply I.
    simpl.
    destruct (d d0) eqn: eqb.
    simpl.
    apply I.
    simpl.
    simpl in H0.
    simpl in H.
    inversion H. clear H.
    inversion H2. clear H2.
    inversion H3. clear H3.
    inversion H2. clear H2.
    inversion H0. clear H0.
    inversion H2.
    specialize (H4 d0 x1 H5).
    rewrite eqb in *.
    simpl in H4.
    inversion H4.
    exists x2.
    rewrite H3 in *.
    split.
    apply (ev_app H H0).
    apply H6.
    apply H6.
  }
  (* constexp *)
  unfold Fun_Thm_Val.
  intros.
  simpl.
  unfold EqInt.
  unfold coerce_int.
  reflexivity.

  (* varexp *)
  unfold Fun_Thm_Val.
  intros.
  simpl.
  apply lookup_preserves_Rel.
  apply H.

  (* absexp *)
  intros.
  unfold Fun_Thm_Val.
  intros.
  simpl.
  unfold FunRel.
  exists (ap_Se (shift_subst s) e).
  split.
  reflexivity.

  intros.

  assert (Rel_Env (cons_env a1 r) (cons_subst val2 s)).
  apply extend_env_preserves_Rel.
  apply H0.
  apply H1.
  unfold lift_Rel.
  destruct (den_exp e (cons_env a1 r)) eqn: eq_e.
  apply I.

  unfold Fun_Thm_Exp in H.
  specialize (H _ _ H2).
  rewrite eq_e in *.
  simpl in H.
  inversion H; clear H.
  exists x.
  inversion H3; clear H3.
  rewrite <- ap_cSS_e.
  rewrite cSS_subst1.
  split.
  apply H.
  apply H4.
  Qed.

  
