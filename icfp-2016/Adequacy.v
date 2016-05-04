(* now let's do the termination proof *)

Require Import List.
Require Import Program.
Require Import FunctionalExtensionality.
Require Import EqNat.

Require Import LiftedTypes.
Require Import MyReals.


(* BKH sets these.  I don't knowhow to get it to work without them *)
(* Set Implicit Arguments.          *)
(* Set Asymmetric Patterns. *)

(* This doesn't seem to do anything:    *)
(* Set Elimination Schemes. *)

(* **************************************************************** *)

(* Inductive Unit : Type := *)
(* | unitval : Unit. *)

(* (* Fake functions *) *)
(* Definition left_half (u : Unit) := u. *)
(* Definition right_half (u : Unit) := u. *)
(* Definition uniform_dist (u : Unit) := u. *)

(* Inductive real : Type := *)
(* | unit_real : Unit -> real. *)

(* Object Types *)

Inductive Otype : Type :=
| Funtype : Otype -> Otype -> Otype
| Realtype : Otype
| Meastype : Otype -> Otype.

(* Denotations of object types *)

Function den_type (t : Otype) : Type :=
  match t with
    | Funtype t u => (den_type t) -> (lifted (den_type u))
    | Realtype => real
    | Meastype t => Unit -> lifted (den_type t)
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

Arguments var_0 {_ _}.
Arguments var_S {_ _ _} _.

Fixpoint env_lookup
         {G : Tyenv}
         {o : Otype}
         (v : Var G o) : (den_env G) -> (den_type o) 
:=  match v 
  with
    | var_0 => fun venv => fst venv
    | var_S v'  => fun venv => env_lookup v' (snd venv)
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
             (Exp G (Funtype a b)) -> (Exp G a) -> (Exp G b)
| bindexp : forall o o', Exp G (Meastype o) ->
                        Exp G (Funtype o (Meastype o')) ->
                        Exp G (Meastype o')
| returnexp : forall o, Exp G o -> Exp G (Meastype o)
with
Val G : Otype -> Type :=
| constexp : real -> Val G Realtype
| varexp : forall o, Var G o -> Val G o 
| absexp : forall (o o': Otype),
             (Exp (cons o G) o') -> (Val G (Funtype o o'))
| uniformval : Val G (Meastype Realtype)
| bindval : forall o o', Val G (Meastype o) ->
                        Val G (Funtype o (Meastype o')) ->
                        Val G (Meastype o')
| returnval : forall a, Val G a -> Val G (Meastype a).

Arguments valexp {G o} _.
Arguments appexp {G a b} _ _.
Arguments bindexp {G o o'} _ _.
Arguments returnexp {G o} _.
Arguments constexp {G} _.
Arguments varexp {G o} _.
Arguments absexp {G o o'} _.
Arguments uniformval {G}.
(* Arguments distval {G}. *)
Arguments bindval {G o o'} _ _.
Arguments returnval {G a} _.




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

Function bindop {a b}
         (s : den_type (Meastype a))
         (f : den_type (Funtype a (Meastype b)))
         : (den_type (Meastype b)) :=
  (fun (u:Unit) =>
     (strict
        (s (left_half u))
        (fun a =>
           (strict
              (f a)
              (fun s2 => (s2 (right_half u))))))).

Function returnop {a} (v : den_type a) : (den_type (Meastype a))
  := fun u => (lift v).

Definition uniformop : (den_type (Meastype Realtype))
  := fun u => (lift (unit_real u)).


(* Coercion, needed to make den_val typecheck *)
Function coerce_real (w : real) : (den_type Realtype) := w.

(* Denotations of Values and Expressions *)

Function den_val {G o} (val : Val G o) r : (den_type o)
  :=
    match val with
      | constexp w => (coerce_real w)
      | varexp var => (apply_env r var)
      | absexp  e => (fun val => den_exp e (cons_env val r))
      | uniformval => uniformop
      | bindval s f => bindop (den_val s r) (den_val f r)
      | returnval v => returnop (den_val v r)
    end
with
den_exp {G o} (exp : (Exp  G o)) (r : (den_env G)) : (lifted (den_type o))
  :=
  match exp with
    | valexp val => lift (den_val val r)
    | appexp e1 e2 => cbv (den_exp e1 r) (den_exp e2 r)
    | returnexp e1 => strict (den_exp e1 r)
                               (fun a => (lift (returnop a)))
    | bindexp e1 e2
      => strict (den_exp e1 r)
                (fun s => strict (den_exp e2 r)
                                 (fun f => (lift (bindop s f))))
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
          | var_0  => var
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
        | var_0 => @var_0 _ _
        | var_S v' => var_S (ren o v')
      end.




(* apply renaming.  Our naming convention calls these ap and ap_Re *)

Fixpoint ap_Rv {G G' o} (ren : Renaming G G')
         (val : Val G o) : (Val G' o) :=
  match val with
    | varexp var => varexp (ren _ var)
    | absexp e => absexp (ap_Re (pad_renaming ren) e)
    | constexp n => @constexp _ n 
    | uniformval => @uniformval _
    | bindval e1 e2 => bindval (ap_Rv ren e1) (ap_Rv ren e2)
    | returnval v => returnval (ap_Rv ren v)
  end
with
ap_Re {G G' o} (ren : Renaming G G') (exp : Exp G o)
: (Exp G' o) :=
  match exp with
    | valexp val => valexp (ap_Rv ren val)
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
      | uniformval => @uniformval _
      | bindval _ _ e1 e2 => bindval (ap_Sv s e1) (ap_Sv s e2)
      | returnval _ v => returnval (ap_Sv s v)
    end
with
ap_Se G G' o (s : Subst G G') (e : Exp G o) : (Exp G' o)
:=
  match e with
    | valexp _ val => valexp (ap_Sv s val)
    | appexp _ _ e1 e2 => appexp (ap_Se s e1) (ap_Se s e2)
    | bindexp _ _ e1 e2 => bindexp (ap_Se s e1) (ap_Se s e2)
    | returnexp _ e1 => returnexp (ap_Se s e1)
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
  intros; auto.

  simpl. rewrite H.  auto.
  simpl. rewrite H. rewrite H0.  auto.
  simpl. rewrite H. rewrite H0. auto.
  simpl. rewrite H. auto.
  simpl. rewrite shift_id_subst. rewrite H. auto.
  simpl. rewrite H. rewrite H0. auto.
  simpl. rewrite H. auto.
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
  | ev_app : forall o o' (e1 : Exp nil (Funtype o o'))
                    (e2 : Exp nil o)
                    e' v w,
               ev e1 (absexp e')
               -> ev e2 v
               -> ev (ap_Se (subst1 v) e') w
               -> ev (appexp e1 e2) w
  | ev_bind : forall a b (e1 : Exp nil (Meastype a))
                     (e2 : Exp nil (Funtype a (Meastype b)))
                     (c1 : Val nil (Meastype a))
                     (c2 : Val nil (Funtype a (Meastype b))),
                ev e1 c1 ->
                ev e2 c2 ->
                ev (bindexp e1 e2) (bindval c1 c2)
  | ev_return : forall a (e : Exp nil a) (c : Val nil a),
                  ev e c ->
                  ev (returnexp e) (returnval c).

Inductive evs : forall (o: Otype),
                  Unit -> Val nil (Meastype o) -> Val nil o -> Prop :=
| evs_unif : forall u,
               evs u (uniformval nil) (constexp _ (unit_real u))
| evs_return : forall o u (c: Val nil o),
                 evs u (returnval c) c
| evs_bind : forall u a b (c1 : Val nil (Meastype a))
                    (c2 : Val nil (Funtype a (Meastype b)))
                    c3 c4 c5,
               evs (left_half u) c1 c3 ->
               ev (appexp (valexp c2) (valexp c3)) c4 ->
               evs (right_half u) c4 c5 ->
               evs u (bindval c1 c2) c5.
               
(* **************************************************************** *)

(* The Logical Relation *)

(* Defined as a fixed point over Otypes and lifted Otypes *)

Definition EqReal : (den_type Realtype) -> real -> Prop :=
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
            (val1 : Val nil (Funtype o1 o2))
: Prop :=
  exists e, val1 = absexp e /\
  forall (a1 : den_type o1) (val2: Val [] o1),
    (Rel1 a1 val2) ->
    (Rel2 (f1 a1) (ap_Se (subst1 val2) e)).

Definition MeasRel {o}
           (Rel : (den_type o) -> (Val [] o) -> Prop)
           (s : den_type (Meastype o))
           (c : Val nil (Meastype o)) : Prop :=
  forall (u:Unit),
    match (s u) with
      | bottom => True
      | lift a => exists c', evs u c c' /\ Rel a c'
    end.

Fixpoint Rel (o : Otype) : (den_type o) -> (Val nil o) -> Prop :=
 match o with
     | Realtype => fun d val => match val with
                                  | constexp n => EqReal d n
                                  | _ => False
                                end
     | Funtype o1 o2 =>
       fun (f1 : den_type (Funtype o1 o2))
           (val1 : Val nil (Funtype o1 o2)) =>
         FunRel (@Rel o1)  (lift_Rel (@Rel o2)) f1 val1
    | Meastype o => MeasRel (@Rel o)
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

Lemma bind_preserves_Rel :
  forall o o' (s1 : Unit -> lifted (den_type o))
         (f : den_type o -> lifted (Unit -> lifted (den_type o')))
         c1 c2,
    MeasRel (Rel (o:=o)) s1 c1 ->
    FunRel (Rel (o:=o)) (lift_Rel (MeasRel (Rel (o:=o')))) f c2 ->
    MeasRel (Rel (o:=o')) (bindop s1 f) (bindval c1 c2).
Proof.    
  intros.
  unfold MeasRel.
  intros u.
  destruct (bindop s1 f u) as [| b] eqn: f_u; auto.
  unfold bindop in f_u.
  destruct (s1 (left_half u)) as [| a] eqn: s1_uL; auto.

  (* (s1 u_L) = bottom *)
  simpl in f_u; inversion f_u.

  (* (s1 u_L) = lift a *)
  destruct (f a) as [| s'] eqn: f_a; auto.
  simpl in f_u.
  rewrite f_a in f_u.
  simpl in f_u.
  inversion f_u.

  (* (f a) = lift s' *)
  destruct (s' (right_half u)) as [| b'] eqn: s'_uR; auto.

  (* (s' u_R) = bottom *)
  simpl in f_u.
  rewrite f_a in f_u.
  simpl in f_u.
  rewrite s'_uR in f_u.
  inversion f_u.

  (* (s' u_R) = lift b *)
  simpl in f_u.
  rewrite f_a in *.
  simpl in f_u.

  assert (Hc3: exists c3, (evs (left_half u) c1 c3) /\ Rel a c3).
  { rewrite s'_uR in *.
    inversion f_u.
    rewrite H2 in *.
    clear f_u.
    unfold FunRel in H0.
    inversion H0 as [e2]. clear H0. inversion H1. clear H1.
    unfold MeasRel in H.
    specialize (H (left_half u)).
    rewrite s1_uL in H.
    inversion H as [c3]; clear H.
    exists c3.
    apply H1. }
    
  inversion Hc3 as [c3]; clear Hc3.
  inversion H1; clear H1.
  unfold FunRel in H0.
  inversion H0 as [e2']; simpl; clear H0.
  inversion H1; clear H1.
  specialize (H4 a c3 H3).
  unfold lift_Rel in H4.
  rewrite f_a in H4.
  inversion H4 as [c4]; clear H4.
  inversion H1; clear H1.
  unfold MeasRel in H5.
  specialize (H5 (right_half u)).
  rewrite s'_uR in *.
  inversion H5 as [c5]; clear H5.
  exists c5.
  inversion H1; clear H1.
  inversion f_u as [eq_b] ; clear f_u.
  rewrite eq_b in *.
  split.
  assert (H10: ev (appexp (valexp c2) (valexp c3)) c4).
  { rewrite H0 in *.
    assert (H12: ev (valexp (absexp e2')) (absexp e2')) by apply ev_val.
    assert (H13: ev (valexp c3) c3) by apply ev_val.
    apply (ev_app H12 H13 H4).
  }
  apply (evs_bind H2 H10 H5).
  (* woo-hoo! *)
  apply H6.
Qed.

Hint Resolve bind_preserves_Rel.

Lemma return_preserves_Rel :
  forall o (v : den_type o) (c : Val nil o),
         Rel v c ->
         MeasRel (Rel (o:=o)) (returnop v) (returnval c).
Proof.
  intros.
  unfold returnop.
  unfold MeasRel.
  intros.
  exists c.
  split.
  apply evs_return.
  apply H.
Qed.

Hint Resolve return_preserves_Rel.

Lemma unif_preserves_Rel :
  MeasRel (Rel (o:=Realtype)) uniformop (uniformval nil).
Proof.
  unfold MeasRel.
  intros.
  unfold uniformop.
  exists (constexp _ (unit_real u)).
  split.
  apply evs_unif.
  unfold Rel.
  unfold EqReal.
  auto.
Qed.

Hint Resolve unif_preserves_Rel.

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
  apply (exp_val_rec Fun_Thm_Exp Fun_Thm_Val);
  unfold Fun_Thm_Exp;
  unfold Fun_Thm_Val;
  intros;
  simpl.

  (* valexp *)
  specialize (H _ _ H0).
  exists (ap_Sv s v).
  split.
  apply ev_val.
  apply H.

  { (* appexp e1 e2 *)
    intros.
    specialize (H _ _ H1).
    specialize (H0 _ _ H1).
    destruct (den_exp e r) eqn: eqe; simpl; auto.
    destruct (den_exp e0 r) eqn: eqe0; simpl; auto.
    destruct (d d0) eqn: eqb; simpl; auto.
    simpl in *.
    inversion H. clear H.
    inversion H2. clear H2.
    inversion H3. clear H3.
    inversion H2. clear H2.
    inversion H0. clear H0.
    inversion H2.
    specialize (H4 d0 x1 H5).
    rewrite eqb in *.
    simpl in H4.
    inversion H4 as [v].
    exists v.
    rewrite H3 in *.
    split.
    apply (ev_app H H0).
    apply H6.
    apply H6.
  }

  (* bindexp e e0 *)
  { specialize (H _ _ H1).
    specialize (H0 _ _ H1).
    destruct (den_exp e r) as [| s1] eqn: eq_e; auto.
    destruct (den_exp e0 r) as [| f] eqn: eq_e0; auto.

    (* e, e0 non-bottom *)
    simpl.
    simpl in *.  
    inversion H as [c1]; clear H; inversion H2; clear H2.
    inversion H0 as [c2]; clear H0; inversion H2; clear H2.
    exists (bindval c1 c2). 
    split.
    apply ev_bind.
    apply H.
    apply H0.
    apply bind_preserves_Rel.
    apply H3.
    apply H4.
  }

  (* returnexp e *)
  specialize (H _ _ H0).
  unfold lift_Rel.
  destruct (den_exp e r) as [|v1] eqn: eq_e; auto.
  simpl.
  unfold lift_Rel in H.
  inversion H as [v]; clear H.
  inversion H1; clear H1.
  exists (returnval v).
  split.
  apply ev_return.
  apply H.
  apply return_preserves_Rel.
  apply H2.

  (* constexp *)
  unfold coerce_real.
  unfold EqReal.
  auto.

  (* varexp *)
  apply lookup_preserves_Rel. apply H.

  { (* absexp *)
  (* copied straight from adequacy-cbv.v! *)
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


    specialize (H _ _ H2).
    rewrite eq_e in *.
    simpl in H.
    inversion H as [v]; clear H.
    exists v.
    inversion H3; clear H3.
    rewrite <- ap_cSS_e.
    rewrite cSS_subst1.
    split.
    apply H.
    apply H4.
  }

  (* uniformval *)
  unfold MeasRel.
  intros.
  unfold uniformop.
  exists (constexp _ (unit_real u)).
  split.
  apply evs_unif.
  unfold EqReal.
  auto.

  (* bindval *)
  apply bind_preserves_Rel.
  specialize (H _ _ H1).
  specialize (H0 _ _ H1).
  apply H.
  specialize (H0 _ _ H1).
  apply H0.

  (* returnval *)
  apply return_preserves_Rel.
  specialize (H _ _ H0).
  apply H.
Qed.


  
