(* The First Logical Relations Proof: Measure Semantics vs. Sampler Semantics *)


Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.

Require Import LiftedTypes.
Require Import Weights.
Require Import MyReals.                   (* including times: Weight -> real -> real *)
Require Import Measures.
Require Import Types.                     (* including variables and environments *)

Require Import Syntax.

Require Import MeasureSemantics.
Require Import SamplingSemantics.

                            
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

Definition EqReal : (den_Mtype Real_type) ->
                    (den_Mtype Real_type) -> Prop :=
  fun v1 v2 => (v1 = v2).

Hint Unfold EqReal.

Function EqMtype (m : Mtype) : (den_typeM (Stype m))
                               -> (den_typeS (Stype m)) -> Prop 
         := 
  match m with
  | Real_type => EqReal
  |Prod_type m1 m2 => fun v1 v2 => (EqMtype m1 (fst v1) (fst v2))
                        /\ (EqMtype m2 (snd v1) (snd v2))
  end.

Hint Unfold EqMtype.

Function coerceMS {m} (v: den_typeM (Stype m)) : (den_typeS (Stype m))
  := v.

Hint Unfold coerceMS.

Theorem EqMtype_coerce : forall (m : Mtype) (v: den_typeM (Stype m)),
    EqMtype m (@coerceMS m v) v.
Proof.
  induction m; auto.
  constructor.
  - apply IHm1.
  - apply IHm2.
Qed.


Theorem EqMtype_injective :
  forall (m : Mtype)  (v v': den_typeM (Stype m)),
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
  | Stype m => EqMtype m
  | Funtype t u => (fun f1 f2 =>
                      forall a1 a2,
                        (Rel t a1 a2)
                        -> (lift_Rel (Rel u) (f1 a1) (f2 a2)))
  | Meastype t => (fun mu s =>
                     forall k,
                       mu k =
                       mu_L (fun u => (strict0 (s u) k)))
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

Theorem Rel_strict2 : forall o1 o2 o3 d1 d1' d2 d2' f f',
    lift_Rel (Rel o1) d1 d1' ->
    lift_Rel (Rel o2) d2 d2' ->
    (forall v1 v1' v2 v2',
        Rel o1 v1 v1' -> Rel o2 v2 v2' -> lift_Rel (Rel o3) (f v1 v2) (f' v1' v2'))
    -> lift_Rel (Rel o3) (strict2 d1 d2 f) (strict2 d1' d2' f').
Proof.
  destruct d1, d1', d2, d2'; try false_invert; eauto.
Qed.

Theorem Rel_Return : forall m (v : den_typeS (Stype m)),
    Rel _ (returnopM v) (returnopS v).
Proof.
  autounfold; simpl.
  symmetry.
  auto using mu_L_const.
Qed.

Theorem Rel_Uniform : Rel _ uniformopM uniformopS.
Proof.
  autounfold; simpl.
  auto using mu_L_extensional.
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
                            strict0 (s' u) k))).
Proof.
  destruct mu, s;
    try false_invert;
    eauto.
Qed.

Lemma split_entropy_sampler : forall
    (o o' : Mtype)
    (mu : den_typeM (Meastype o))
    (s : den_typeS (Meastype o))
    (f : den_typeM (Stype o) -> lifted (den_typeM (Meastype o')))
    (f' : den_typeM (Stype o) -> lifted (den_typeS (Meastype o')))
    (k : den_Mtype o' -> real)
    (H0 : forall a : den_typeM (Stype o), lift_Rel (Rel (Meastype o')) (f a) (f' a)),

    mu_L (fun u =>
            (strict0 (s (left_half u))
                     (fun a =>
                        (strict0 (f' a)
                                 (fun s2 =>
                                    (strict0 (s2 (right_half u)) k))))))
    =
    mu_L (fun u => (strict0 (s u)
                            (fun a =>
                               (strict0 (f a)
                                        (fun mu' => (mu' k)))))).
Proof.
  intros.
  rewrite <- (split_entropy
                (fun lu ru =>
                   strict0 (s lu)
                           (fun a => (strict0 (f' a)
                                              (fun s2 =>
                                                 (strict0 (s2 ru) _)))))). 
  apply mu_L_extensional; intro u.
  rewrite strict0_mu_L.
  f_equal.
  extensionality x.
  erewrite RelMeas_Lemma1.
  rewrite strict0_mu_L.
  f_equal.
  apply H0.
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
  rewrite strict0_strict.
  f_equal. extensionality a.
  rewrite strict0_strict.
  f_equal. extensionality x.
  rewrite strict0_strict.
  f_equal.
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
      Rel_strict2, Rel_Return, Rel_Uniform, Rel_bindop,
    times_one_weight, mu_L_extensional, mu_1_density_1.

  (* prodexp *)
  - specialize (H r s H1).
    specialize (H0 r s H1).
     destruct (den_expM e r), (den_expS e s), (den_expM e0 r), (den_expS e0 s);
      try false_invert;
      eauto using H, H0.
     simpl.
     unfold lift_Rel.
     auto.

  (* proj1exp *)
  - specialize (H r s H0).
    destruct (den_expM e r), (den_expS e s); try false_invert; auto.
    simpl.
    unfold lift_Rel.
    unfold lift_Rel in H.
    unfold Rel in H.
    apply H.

      (* proj2exp *)
  - specialize (H r s H0).
    destruct (den_expM e r), (den_expS e s); try false_invert; auto.
    simpl.
    unfold lift_Rel.
    unfold lift_Rel in H.
    unfold Rel in H.
    apply H.

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

  (* prodval *)
  - specialize (H r s H1).
    specialize (H0 r s H1).
    auto.


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
