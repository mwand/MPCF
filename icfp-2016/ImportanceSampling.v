(* The First Logical Relations Proof: Measure Semantics vs. Sampler Semantics *)


Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import LiftedTypes.
Require Import Weights.
Require Import MyReals.                   (* including times: Weight -> real -> real *)
Require Import Measures.
Require Import Types.                     (* including variables and environments *)
                            
(* false_invert: tactic from SF *)
(* false_invert proves any goal provided there is at least one *)
(* hypothesis H in the context that can be proved absurd by calling *)
(* inversion H. *)

Ltac false_invert :=
  intros;
  match goal with
    [ H:_ |- _ ] => solve [ inversion H ]
  end.

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
| bindexp : forall (o o' : Mtype),  Exp G (Meastype o) ->
                        Exp G (Funtype (M_Otype o) (Meastype o')) ->
                        Exp G (Meastype o')
| returnexp : forall (o : Mtype), Exp G (M_Otype o)
                                  -> Exp G (Meastype o)
with
Val G : Otype -> Type :=
| constexp : real -> Val G (M_Otype Real_Mtype)
| varexp : forall o, Var G o -> Val G o 
| absexp : forall (o o': Otype),
             (Exp (cons o G) o') -> (Val G (Funtype o o'))
| uniformval : Val G (Meastype Real_Mtype)
| distval : Val G (Meastype Real_Mtype)  (* some non-uniform distribution: *)
 
| bindval : forall o o', Val G (Meastype o) ->
                         Val G (Funtype
                                  (M_Otype o)
                                  (Meastype o')) ->
                        Val G (Meastype o')
| returnval : forall a, Val G (M_Otype a) -> Val G (Meastype a).

Arguments valexp {G o} _.
Arguments appexp {G a b} _ _.
Arguments bindexp {G o o'} _ _.
Arguments returnexp {G o} _.
Arguments constexp {G} _.
Arguments varexp {G o} _.
Arguments absexp {G o o'} _.
Arguments uniformval {G}.
Arguments distval {G}.
Arguments bindval {G o o'} _ _.
Arguments returnval {G a} _.



(* Coq doesn't generate the correct mutual induction hypotheses
   for these, so we have to help it along. *)

Scheme exp_val_rec := Induction for Exp Sort Prop
with
val_exp_rec := Induction for Val Sort Prop.

(* ******************************************************** *)

(* The Sampling Semantics *)

(* all that changes is the interpretation of Meastype m *)

Function den_typeS (t : Otype) : Type :=
  match t with
    | M_Otype m => (den_Mtype m)
    | Funtype t u => (den_typeS t) -> (lifted (den_typeS u))
    | Meastype m => Unit -> lifted ((den_Mtype m) * Weight)
  end. 

Function cbv  {A : Type}{B : Type} 
                 (d: lifted (A -> (lifted B)))
                 (d': lifted A) : lifted B :=
  strict d (fun f => strict d' (fun a => (f a))).

Function bindopS {a b : Mtype}
         (s : den_typeS (Meastype a))
         (f : den_typeS (Funtype (M_Otype a) (Meastype b)))
         : (den_typeS (Meastype b)) :=
  (fun (u:Unit) =>
     (strict2
        (s (left_half u))
        (fun a w =>
           (strict
              (f a)
              (fun s2 => (strict2
                            (s2 (right_half u))
                            (fun b w' => (lift (b, (prod_weights w w')))))))))).
Hint Unfold bindopS.

Function returnopS {m} (v : den_typeS (M_Otype m)) : (den_typeS (Meastype m))
  := fun u => (lift (v, one_weight)).
Hint Unfold returnopS.

Definition uniformopS : (den_typeS (Meastype Real_Mtype))
  := fun u => (lift ((unit_real u), one_weight)).
Hint Unfold uniformopS.

Definition distvalS : (den_typeS (Meastype Real_Mtype))
  := fun u => (lift ((unit_real u), (density_1 (unit_real u)))).
Hint Unfold distvalS.


(* Coercion, needed to make den_val typecheck *)
Function coerce_real (w : real) : (den_typeS (M_Otype Real_Mtype)) := w.
Hint Unfold coerce_real.

(* Denotations of Values and Expressions in the Sampling Semantics*)

Function den_valS {G o} (val : Val G o) (r : (@den_env den_typeS G))
         : (den_typeS o)
  :=
    match val with
      | constexp w => (coerce_real w)
      | varexp var => (apply_env r var)
      | absexp e => (fun val => den_expS e (cons_env val r))
      | uniformval => uniformopS
      | distval => distvalS
      | bindval s f => bindopS (den_valS s r) (den_valS f r)
      | returnval v => returnopS (den_valS v r)
    end
with
den_expS {G o} (exp : (Exp  G o)) (r : (den_env G)) : (lifted (den_typeS o))
  :=
  match exp with
    | valexp val => lift (den_valS val r)
    | appexp e1 e2 => cbv (den_expS e1 r) (den_expS e2 r)
    | returnexp e1 => strict (den_expS e1 r)
                               (fun a => (lift (returnopS a)))
    | bindexp e1 e2
      => strict (den_expS e1 r)
                (fun s => strict (den_expS e2 r)
                                 (fun f => (lift (bindopS s f))))
  end.

(* **************************************************************** *)

(* The Measure Semantics *)

(* measure semantics is unchanged! *)


(* We will use a deFinetti/Shan formulation of measures.  This is not *)
(* what's in the paper, but we'll see if this works anyway. *)

Function den_typeM (t : Otype) : Type :=
  match t with
    | M_Otype m => (den_Mtype m)
    | Funtype t u => (den_typeM t) -> (lifted (den_typeM u))
    | Meastype m => Measure (den_Mtype m)
  end.  

(* turn fn u => u into an integrator *)
Definition uniformopM : (den_typeM (Meastype Real_Mtype))
  := fun k => mu_L (fun u => k (unit_real u)).
Hint Unfold uniformopM.

Definition distvalM : (den_typeM (Meastype Real_Mtype))
  := mu_1.
Hint Unfold distvalM.

Definition returnopM {m : Mtype}
           (v : (den_Mtype m)) : (den_typeM (Meastype m))
  :=
    fun k => k v.
Hint Unfold returnopM.

Definition bindopM
           {o o' : Mtype}
           (mu : (den_typeM (Meastype o)))
           (f :  (den_typeM (M_Otype o)) -> 
                 (lifted (den_typeM (Meastype o'))))
           : (den_typeM (Meastype o'))
  := fun (k : (den_typeM (M_Otype o')) -> real)
     => mu (fun a => strict0 (f a) (fun mu' => (mu' k))).
Hint Unfold bindopM.

(* The denotations of values and expressions in the measure semantics *)

Function den_valM {G o} (val : Val G o) (r : (@den_env den_typeM G))
         : (den_typeM o)
  :=
    match val with
      | constexp w => (coerce_real w)
      | varexp var => (apply_env r var)
      | absexp e => (fun val => den_expM e (cons_env val r))
      | uniformval => uniformopM
      | distval => distvalM
      | bindval s f => bindopM (den_valM s r) (den_valM f r)
      | returnval v => returnopM (den_valM v r)
    end
with
den_expM {G o} (exp : (Exp  G o)) (r : (den_env G)) : (lifted (den_typeM o))
  :=
  match exp with
    | valexp val => lift (den_valM val r)
    | appexp e1 e2 => cbv (den_expM e1 r) (den_expM e2 r)
    | returnexp e1 => strict (den_expM e1 r)
                               (fun a => (lift (returnopM a)))
    | bindexp e1 e2
      => strict (den_expM e1 r)
                (fun s => strict (den_expM e2 r)
                                 (fun f => (lift (bindopM s f))))
  end.

(* **************************************************************** *)

Definition EqReal : (den_Mtype Real_Mtype) ->
                    (den_Mtype Real_Mtype) -> Prop :=
  fun v1 v2 => (v1 = v2).

Hint Unfold EqReal.

Function EqMtype (m : Mtype) : (den_typeM (M_Otype m))
                               -> (den_typeS (M_Otype m)) -> Prop 
         := 
  match m with
  | Real_Mtype => EqReal
  | Prod_Mtype m1 m2 => fun v1 v2 => (EqMtype m1 (fst v1) (fst v2))
                        /\ (EqMtype m2 (snd v1) (snd v2))
  end.

Hint Unfold EqMtype.

Function coerceMS {m} (v: den_typeM (M_Otype m)) : (den_typeS (M_Otype m))
  := v.

Hint Unfold coerceMS.

Theorem EqMtype_coerce : forall (m : Mtype) (v: den_typeM (M_Otype m)),
    EqMtype m (@coerceMS m v) v.
Proof.
  induction m; auto.
  constructor.
  - apply IHm1.
  - apply IHm2.
Qed.


Theorem EqMtype_injective :
  forall (m : Mtype)  (v v': den_typeM (M_Otype m)),
    EqMtype m (@coerceMS m v) v' -> v = v'.
Proof.
  induction m; auto.
  destruct v, v'.
  inversion 1.
  f_equal; auto.
Qed.

Function lift_Rel {A B : Type} (R : (A -> B -> Prop)) : 
  ((lifted A) -> (lifted B) -> Prop) :=
  fun d d' =>
    match (d, d') with
      | (bottom, bottom) => True
      | (lift u, lift u') => R u u'
      | _ => False
    end. 
Hint Unfold lift_Rel.

(* We'll use an extensional version of Rel_Meas  *)

Fixpoint Rel (t : Otype) : (den_typeM t) -> (den_typeS t) -> Prop :=
  match t with
  | M_Otype m => EqMtype m

(* fun (v1 : @den_typeM m) *)
(*                      (v2 : @den_typeS m) => EqMtype m (coerceMS v1) v2 *)

    | Funtype t u => (fun f1 f2 =>
                        forall a1 a2,
                               (Rel t a1 a2)
                               -> (lift_Rel (Rel u) (f1 a1) (f2 a2)))
    | Meastype t => (fun mu s =>
                       forall k,
                         mu k =
                         mu_L (fun u => (strict20 (s u) (fun a w => (times w (k a))))))
  end.
Hint Unfold Rel.


Definition den_envM := @den_env den_typeM.
Definition den_envS := @den_env den_typeS.

Fixpoint Rel_Env G : (den_envM G) -> (den_envS G)
                     -> Prop :=
  match G with
    | nil => fun r1 r2 => True
    | (o :: G') => fun r1 r2 =>
                     Rel o (fst r1) (fst r2)
                     /\ Rel_Env G' (snd r1) (snd r2)
  end.
Hint Unfold Rel_Env.

Lemma Fund_Env : forall G (o : Otype)
                        (var : Var G o)
                        (r1 : den_envM G)
                        (r2 : den_envS G),
                   Rel_Env G r1 r2 ->
                   Rel o (env_lookup var r1) (env_lookup var r2). 
Proof.  
  induction G as [| o' G'];
    try false_invert.
  (* G = o':: G' *)
  induction var as [| G'' ? ? ? IHvar ];
    inversion 1; auto.
  apply IHvar.
  auto.
Qed.

Lemma lookup_preserves_Rel : forall G (o : Otype)
                       (var : Var G o)
                       (r : den_envM G)
                       (s : den_envS G),
    Rel_Env G r s -> Rel o (apply_env r var) (apply_env s var).
Proof.
  induction G; try false_invert.
  (* G = o' :: G' *)
  induction var.
  - (* var = var_0 *)
    inversion 1.
    auto.
  - (* var = var_S v' *)
    intros.
    apply IHvar.
    apply H.
Qed.

Lemma extend_env_preserves_Rel :
  forall G o r1 r2 val1 val2,
    Rel_Env G r1 r2 -> Rel o val1 val2 -> Rel_Env (o::G) (val1,r1) (val2,r2).
Proof.
  auto.
Qed.

Theorem Rel_cbv : forall o o' f f' a a',
    lift_Rel (Rel (Funtype o o')) f f' ->
    lift_Rel (Rel o)              a a' ->
    lift_Rel (Rel o') (cbv f a) (cbv f' a').
Proof.                                
  destruct f, f', a, a';
    try false_invert;
    eauto.
Qed.

Theorem Rel_Return : forall m (v : den_typeS (M_Otype m)),
    Rel _ (returnopM v) (returnopS v).
Proof.
  autounfold; simpl.
  symmetry.
  auto using mu_L_const, times_one_weight.
Qed.

Theorem Rel_Uniform : Rel _ uniformopM uniformopS.
Proof.
  autounfold; simpl.
  auto using times_one_weight, mu_L_extensional.
Qed.

Lemma RelMeas_Lemma1 :
  forall (m : Mtype)
         (mu : (lifted (den_typeM (Meastype m))))
         (s  : (lifted (den_typeS (Meastype m))))
         k,
    lift_Rel (Rel (Meastype m)) mu s ->
    strict0 mu (fun mu' => (mu' k))
    = strict0 s (fun s' =>
                   (mu_L (fun u =>
                            strict20 (s' u) (fun b w =>
                                               (times w (k b)))))).
Proof.
  destruct mu, s;
    try false_invert;
    eauto.
Qed.

Ltac push_bind_right :=
  progress
    repeat
    (try rewrite strict0_bind_assoc;
     try rewrite strict20_bind_assoc;
     try rewrite strict0_strict20_bind_assoc;
     match goal with
     | [ |- (doW x <- ?m ; _) = (doW x' <- ?m ; _) ] =>
       f_equal; extensionality x
     | [ |- (doW x, w <- ?m ; _) = (doW x', w' <- ?m ; _) ] =>
       f_equal; extensionality x; extensionality w
     end).

Lemma split_entropy_sampler : forall
    (o o' : Mtype)
    (mu : den_typeM (Meastype o))
    (s : den_typeS (Meastype o))
    (f : den_typeM (M_Otype o) -> lifted (den_typeM (Meastype o')))
    (f' : den_typeM (M_Otype o) -> lifted (den_typeS (Meastype o')))
    (k : den_Mtype o' -> real)
    (H0 : forall a : den_typeM (M_Otype o), lift_Rel (Rel (Meastype o')) (f a) (f' a)),

    mu_L (fun u =>
            (doW a, w <- s (left_half u);
               doW s2 <- f' a;
               doW b, w' <- s2 (right_half u);
               times (prod_weights w w') (k b)))
    =
    mu_L (fun u => (doW a, w <- s u;
                      times w (doW mu' <- f a; mu' k))).
Proof.
  intros.
  rewrite <- split_entropy with (f:=(fun lu ru =>
                                       doW a, w <- s lu;
                                       doW s2 <- f' a;
                                       doW b, w' <- s2 ru; _)).
  apply mu_L_extensional; intro u.
  rewrite strict20_mu_L.
  f_equal; extensionality a; extensionality w.
  rewrite strict0_mu_L.
  erewrite RelMeas_Lemma1 by auto.
  rewrite strict0_linear.
  f_equal; extensionality b.
  rewrite <- mu_L_linear.
  apply mu_L_extensional; intro u'.
  rewrite strict20_linear.
  f_equal; extensionality c; extensionality w'.
  auto using times_assoc.
Qed.

Theorem Rel_bindop : forall (o o': Mtype) mu s
                            f f',
    Rel _ mu s ->
    (forall a, lift_Rel (Rel (Meastype o')) (f a) (f' a)) ->
    Rel _ (@bindopM o o' mu f) (@bindopS o o' s f').
Proof.
  intros.
  autounfold.
  intros.
  rewrite H; clear H.

  erewrite <- split_entropy_sampler; auto.
  apply mu_L_extensional; intro u.
  push_bind_right.
Qed.

Definition Fun_Thm_Exp G o  (exp: Exp G o) :=
  forall         
         (r : den_envM G)
         (s : den_envS G),
    Rel_Env G r s
    -> lift_Rel (@Rel o) (den_expM exp r) (den_expS exp s).
Hint Unfold Fun_Thm_Exp.

Definition Fun_Thm_Val G o  (val: Val G o) :=
  forall         
         (r : den_envM G)
         (s : den_envS G),
    Rel_Env G r s
    -> Rel o (den_valM val r) (den_valS val s).
Hint Unfold Fun_Thm_Val.

Theorem Fund_Thm: forall G o exp, @Fun_Thm_Exp G o exp.
Proof.
  apply (exp_val_rec Fun_Thm_Exp Fun_Thm_Val);
    unfold Fun_Thm_Exp, Fun_Thm_Val;
    intros; simpl;
    eauto using lookup_preserves_Rel, extend_env_preserves_Rel,
    times_one_weight, mu_L_extensional, mu_1_density_1.

  (* appexp *)
  - specialize (H r s H1).
    specialize (H0 r s H1).
    destruct (den_expM e r), (den_expS e s), (den_expM e0 r), (den_expS e0 s);
      try false_invert;
      eauto using H, H0.

  (* appexp *)
  - specialize (H r s H1).
    specialize (H0 r s H1).
    destruct (den_expM e r), (den_expS e s), (den_expM e0 r), (den_expS e0 s);
      try false_invert;
      auto.
    apply Rel_bindop; auto.
    intros.
    apply H0.
    apply EqMtype_coerce.

  (* returnexp *)
  - specialize (H r s H0).
    destruct (den_expM e r), (den_expS e s);
      try false_invert;
      auto.
    apply EqMtype_injective in H; subst.
    apply Rel_Return.

  (* bindval *)
  - apply Rel_bindop; auto.
    intros.
    apply H0; auto.
    apply EqMtype_coerce.

  (* returnval *)
  - eapply EqMtype_injective in H; eauto.
    rewrite H.
    apply Rel_Return.
Qed.
