(* Adequacy of Operational Semantics vs. Sampling Semantics *)

(* We don't bother with soundness, which is (or should be) dull *)

Require Import Coq.Lists.List.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Program.
Require Import EqNat. 

Require Import LiftedTypes.
Require Import MyReals.

Require Import Types.
Require Import Syntax.
Require Import SamplingSemantics.
Require Import Substitutions.
Require Import OperationalSemantics.

(* false_invert: a tactic from SF *)
(* false_invert proves any goal provided there is at least one *)
(* hypothesis H in the context that can be proved absurd by calling *)
(* inversion H. *)

Ltac false_invert :=
  intros;
  match goal with
    [ H:_ |- _ ] => solve [ inversion H ]
  end.

(* Ltac helpers *)
Ltac invert_ex :=
  repeat
    match goal with
    | [ H : exists _, _ |- _ ] => inversion H; clear H; intuition
    end.

Ltac solve_ex := invert_ex; try (eexists; intuition).


(* **************************************************************** *)

(* The Logical Relation *)

(* The relation will be defined compositionally in Otype. *)

(* First we build some combinators for the different cases. *)

Definition EqReal : (den_Mtype Real_type) ->
                    (den_Mtype Real_type) -> Prop :=
  fun v1 v2 => (v1 = v2).


(* Combinators for Mtypes:  *)

Function Real_Rel
         (d : (den_Mtype Real_type))
         (val : (Val nil (Stype Real_type)))
  :=
    exists n, val = constexp n /\ d = n.

Hint Unfold Real_Rel.

Function Prod_Rel {ma mb : Mtype}
         (RA : (den_Mtype ma) -> (Val nil (Stype ma)) -> Prop)
         (RB : (den_Mtype mb) -> (Val nil (Stype mb)) -> Prop)
         (d  : (den_Mtype (Prod_type ma mb)))
         (val : (Val nil (Stype (Prod_type ma mb))))
  := 
    exists e1 e2, val = prodval e1 e2 /\
                  (RA (fst d) e1) /\ (RB (snd d) e2).

Hint Unfold Prod_Rel.

Fixpoint Mtype_Rel (m : Mtype)
  : (den_typeS (Stype m)) -> (Val nil (Stype m)) -> Prop :=
  match m with
  | Real_type => Real_Rel
  | Prod_type m1 m2 => Prod_Rel (Mtype_Rel m1) (Mtype_Rel m2) 
  end.

(* General recipe for lifting a relation *)
(* (liftRel o R d e) iff d is bottom or d = lift(a) and e evaluates to *)
(* a value v such (Rel a v) holds*) 

Function lift_Rel {o : Otype} (R : (den_typeS o) -> (Val nil o) -> Prop)
: (lifted (den_typeS o)) -> (Exp nil o) -> Prop :=
  fun d e =>
    match d with
      | bottom => True
      | lift a => exists v, ev e v /\ R a v
    end.

Hint Unfold lift_Rel.

Definition Fun_Rel {o1 o2}
           (Rel1 : (den_typeS o1) -> (Val [] o1) -> Prop)
           (Rel2 : (lifted (den_typeS o2)) -> (Exp [] o2) -> Prop)
           (f1 : (den_typeS o1) -> (lifted (den_typeS o2)))
           (val1 : Val nil (Funtype o1 o2))
: Prop :=
  exists e, val1 = absexp e /\
  forall (a1 : den_typeS o1) (val2: Val [] o1),
    (Rel1 a1 val2) ->
    (Rel2 (f1 a1) (ap_Se (subst1 val2) e)).

Hint Unfold Fun_Rel.

Definition Meas_Rel
           (m : Mtype)
           (s : den_typeS (Meastype m))
           (c : Val nil (Meastype m)) : Prop :=
  forall (u:Unit),
    match (s u) with
      | bottom => True
      | lift (a,w) => exists c', evs u c c' w /\ Mtype_Rel m a c'
    end.

Hint Unfold Meas_Rel.

(* Now the main relation simply branches depending on its Otype argument: *)

Fixpoint Rel {o : Otype} : (den_typeS o) -> (Val nil o) -> Prop :=
  match o with
  | Stype m => Mtype_Rel m
  | Funtype o1 o2 => Fun_Rel (@Rel o1)  (lift_Rel (@Rel o2)) 
  | Meastype m => Meas_Rel m
  end.


(* Extend the relation to environments based on a type environment G *)

Fixpoint Rel_Env {G} : (den_env G) -> (Subst G nil) -> Prop :=
  match G with
    | nil => fun r s => True
    | (o :: G') => fun (r : den_env (o::G')) s =>
                     Rel (fst r) (hd_subst s)
                     /\ Rel_Env (snd r) (tl_subst s)
  end.

Lemma lookup_preserves_Rel : forall G (o : Otype)
                       (var : Var G o)
                       (r : den_env G)
                       (s : Subst G nil),
    Rel_Env r s -> Rel (apply_env r var) (s _ var).
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

Hint Resolve lookup_preserves_Rel. 

Lemma extend_env_preserves_Rel :
  forall (o: Otype) G r (s : Subst G nil) (d : den_typeS o) (val: Val nil o),
    Rel_Env r s -> Rel d val
    -> Rel_Env (cons_env d r) (cons_subst val s).
Proof.
  intros.
  simpl.
  split.
  apply H0.
  apply H.
Qed.

Hint Resolve extend_env_preserves_Rel.

    
Lemma bind_preserves_Rel :
  forall m m'
         (s1 : den_typeS (Meastype m))
         (f : (den_typeS (Stype m))
              -> lifted (den_typeS (Meastype m')))
         c1 c2,
    Meas_Rel m s1 c1 ->
    Fun_Rel (Rel ) (lift_Rel (Meas_Rel m')) f c2 ->
    Meas_Rel m' (bindopS s1 f) (bindval c1 c2).
Proof.    
  intros.
  unfold Meas_Rel.
  intros.
  destruct (bindopS s1 f u) as [|b]  eqn: f_u; try false_invert; auto.
  unfold bindopS in f_u.
  destruct (s1 (left_half u)) eqn: s1_uL; try false_invert; simpl in *; auto.

  destruct b.
  unfold prod_curry in f_u.
  destruct p.
  destruct (f d0) as [| s2] eqn: f_d; try false_invert; auto.
  simpl in f_u.
  destruct (s2 (right_half u)) as [| b'] eqn: s2_uR; try false_invert; simpl in *; auto.
  unfold prod_curry in f_u.
  destruct b'.
  inversion f_u; clear f_u.
  (* rewrite H2 in *. *)
  subst.

  (* now we have all the denotations, next let's work on the 
     reductions *)

  (* First reduction: evs (left_half u) c1 c3 *)
  unfold Meas_Rel in H.
  specialize (H (left_half u)).
  rewrite s1_uL in H; simpl in H.
  inversion H as [c3]; clear H.
  inversion H1 as [Red1a Red1b]; clear H1.

  (* second reduction: ev (appexp (valexp c2) (valexp c3)) c4 *)
  (* c2: is a function, so it has to be an abstraction *)

  unfold Fun_Rel in H0.
  inversion H0 as [e]; clear H0.
  inversion H; clear H.
  specialize (H1 _ _ Red1b).
  unfold lift_Rel in H1.
  rewrite f_d in *; simpl in *.
  inversion H1 as [c4]; clear H1.
  inversion H; clear H.


  assert (Red2: ev (appexp (valexp c2) (valexp c3)) c4).
  assert (Red2a: ev (valexp c2) c2) by apply ev_val.
  assert (Red2b: ev (valexp c3) c3) by apply ev_val.
  rewrite H0 in *.
  apply (ev_app Red2a Red2b H1).

  (* now for the last step *)
  unfold Meas_Rel in H2.
  specialize (H2 (right_half u)).
  rewrite s2_uR in *.
  inversion H2 as [c5]; clear H2.
  inversion H as [Red3a Red3b]; clear H.
  exists c5.
  split.
  apply (evs_bind Red1a Red2 Red3a).
  apply Red3b.
Qed.

Hint Resolve bind_preserves_Rel. 

Lemma bind_preserves_Rel' :
  forall m m'
         (s1 : den_typeS (Meastype m))
         (f : (den_typeS (Stype m))
              -> lifted (den_typeS (Meastype m')))
         c1 c2,
    Meas_Rel m s1 c1 ->
    Fun_Rel (Rel ) (lift_Rel (Meas_Rel m')) f c2 ->
    Meas_Rel m' (bindopS s1 f) (bindval c1 c2).
Proof.    
  intros.
  unfold Meas_Rel.
  intros.
  destruct (bindopS s1 f u) as [|b]  eqn: f_u; try false_invert; auto.
  unfold bindopS in f_u.
  destruct (s1 (left_half u)) eqn: s1_uL; try false_invert; simpl in *; auto.

  destruct b.
  unfold prod_curry in f_u.
  destruct p.
  destruct (f d0) as [| s2] eqn: f_d; try false_invert; auto.
  simpl in f_u.
  destruct (s2 (right_half u)) as [| b'] eqn: s2_uR; try false_invert; simpl in *; auto.
  unfold prod_curry in f_u.
  destruct b'.
  inversion f_u; clear f_u.
  subst.
 

  (* now we have all the denotations, next let's work on the 
     reductions *)

  (* First reduction: evs (left_half u) c1 c3 *)
  unfold Meas_Rel in H.
  specialize (H (left_half u)).
  rewrite s1_uL in H; simpl in H.
  inversion H; clear H.
  inversion H1 as [Red1a Red1b]; clear H1.

  (* second reduction: ev (appexp (valexp c2) (valexp c3)) c4 *)
  (* c2: is a function, so it has to be an abstraction *)

  unfold Fun_Rel in H0.
  inversion H0 as [e]; clear H0.
  inversion H; clear H.

  specialize (H1 _ _ Red1b).
  unfold lift_Rel in H1.
  rewrite f_d in *; simpl in *.
  inversion H1; clear H1.
  inversion H; clear H.

  (* finish unfolding *)
  unfold Meas_Rel in H2.
  specialize (H2 (right_half u)).
  rewrite s2_uR in *.
  inversion H2; clear H2.
  inversion H.

  (* Now patch the pieces together.  Coq is actually good at this! *)

  subst.
  eauto using evs_bind, ev_app, ev_val.
Qed.

Hint Resolve bind_preserves_Rel'.

Lemma return_preserves_Rel :
  forall m (v : den_typeS (Stype m)) (c : Val nil (Stype m)),
         Rel v c ->
         Meas_Rel m (returnopS v) (returnval c).
Proof.
  intros.
  unfold returnopS.
  unfold Meas_Rel.
  intros.
  exists c.
  split.
  apply evs_return.
  apply H.
Qed.

Hint Resolve return_preserves_Rel.

Lemma unif_preserves_Rel :
  Meas_Rel _ uniformopS uniformval.
Proof.
  unfold Meas_Rel.
  intros.
  unfold uniformopS.
  exists (constexp (unit_real u)).
  split.
  apply evs_unif.
  unfold Mtype_Rel.
  unfold Real_Rel.
  eauto.
Qed.

Hint Resolve unif_preserves_Rel.

Lemma dist_preserves_Rel :
  forall r,
    Meas_Rel _ (distvalS r) (distval (constexp r)).
Proof.
  intros.
  unfold Meas_Rel.
  intros.
  simpl.
  eexists.
  split.
  apply evs_dist.
  unfold Real_Rel.
  eauto.
Qed.

Lemma dist_preserves_Rel':
  forall d v,
    Real_Rel d v -> Meas_Rel Real_type (distvalS d) (distval v).
Proof.
  intros.
  autounfold in *.
  invert_ex.
  subst.
  eexists.
  split.
  eapply evs_dist.
  unfold Mtype_Rel.
  unfold Real_Rel.
  eauto.
Qed.

(* This should really be of the form
  forall d v, Rel d v -> Meas_Rel _ (distvalS d) (distval v)

 *)

(* **************************************************************** *)

(* The Fundamental Theorem *)


Definition Fun_Thm_Exp G o  (exp: Exp G o) :=
  forall         
         (r : den_env G)
         (s : Subst G nil),
    Rel_Env r s
    -> lift_Rel (@Rel o) (den_expS exp r) (ap_Se s exp).

Definition Fun_Thm_Val G o   (val: Val G o):= 
  forall 
        
         (r : den_env G)
         (s : Subst G nil),
    Rel_Env r s
    -> @Rel o (den_valS val r) (ap_Sv s val).

(* Tactics for proving the fundamental theorem *)



Ltac auto_specialize :=
  repeat
    match goal with
    | [ H : forall x : ?a, _, v : ?a |- _ ] => specialize H with (x:=v)
    | [ H : ?a -> _, v : ?a |- _ ] =>
      let Hv := fresh H in
      apply H in v as Hv; clear H
    end.

Ltac destruct_lift :=
  match goal with
  | [ H : lift_Rel _ ?x _ |- _ ] =>
    match x with
    | bottom => fail 1
    | lift _ => fail 1
    | _ => destruct x
    end
  end.

Theorem Fund_Thm_Proof3 : forall G o exp, @Fun_Thm_Exp G o exp.
Proof.
  apply (exp_val_rec Fun_Thm_Exp Fun_Thm_Val);
  unfold Fun_Thm_Exp;
  unfold Fun_Thm_Val;
  simpl; intros;
    try (auto_specialize;
         repeat (destruct_lift; simpl in *; auto);
         repeat invert_ex;
         unfold Prod_Rel, Fun_Rel in *).
           

  { (* valexp *)
    eauto using ev_val.
    }

  { (* prodexp *)
    solve_ex.
    eauto using ev_prod.
    eexists.
    eexists.
    eauto.
    }

  { (* proj1exp *)
    invert_ex.
    subst.
    eauto using ev_proj1.
  }
  
  { (* proj2exp *)
    invert_ex.
    subst.
    eauto using ev_proj2.
  } 

  { (* appexp e e0 *)
    invert_ex.
    destruct (d0 d) eqn: d0_d; unfold lift_Rel; auto.
    invert_ex.
    subst.
    auto_specialize.
    rewrite d0_d in *.
    apply H5 in H3; clear H5.
    unfold lift_Rel in H3.
    invert_ex.
    eexists.
    eauto using ev_app.
    }

  { (* bindexp e e0 *)
    invert_ex.
    subst.
    eexists.
    split.
    eauto using ev_bind.
    eauto using bind_preserves_Rel'.
  }

  { (* returnexp e *)
    eauto using ev_return, return_preserves_Rel.
  }

  (* Now on to values: *)

  { (* valexp *)   (* this is one that the header got *)
    unfold Real_Rel.
    eauto.
  }

  { (* prodval *)
    unfold Prod_Rel.
    eauto.
  }

  { (* varexp *)
    (* eauto using lookup_preserves_Rel doesn't work here. *)
    apply lookup_preserves_Rel.
    eauto.
  }

  { (* absexp *)
    unfold Fun_Rel.
    eexists.
    intuition.
    replace (ap_Se (subst1 val2) (ap_Se (shift_subst s) e))
    with (ap_Se (cons_subst val2 s) e)
      by (rewrite <- cSS_subst1, <- ap_cSS_e; auto).
    auto.
  }

  { (* uniformval *)
    auto using unif_preserves_Rel.
  }

  { (* distval *)
    auto using dist_preserves_Rel'.
  }

  { (* bindval *)
    auto using bind_preserves_Rel'.
  }

  { (* returnval *)
    auto using return_preserves_Rel.
  }
Qed.

Theorem Fund_Thm_NewProof : forall G o exp, @Fun_Thm_Exp G o exp.
Proof.
  apply (exp_val_rec Fun_Thm_Exp Fun_Thm_Val);
  unfold Fun_Thm_Exp;
  unfold Fun_Thm_Val;
  simpl; intros;
    (* this script knocks off 5 cases *)
  try solve [auto_specialize; eauto;
                  repeat destruct_lift;
                  unfold Prod_Rel, lift_Rel in *;
                  solve_ex; subst; eauto].

  { (* appexp e e0 *)
    auto_specialize.
    repeat destruct_lift; eauto.
    simpl in *.
    invert_ex.
    destruct (d0 d) eqn: d0_d; unfold lift_Rel; auto.
    unfold Fun_Rel in *.
    invert_ex.
    subst.
    auto_specialize.
    rewrite d0_d in *.
    simpl in H4.
    invert_ex.
    eauto using ev_app.
    }

  (* Now on to values: *)

  { (* varexp *)
    apply lookup_preserves_Rel.
    assumption.
  }

  { (* absexp *)
    unfold Fun_Rel.
    solve_ex.
    replace (ap_Se (subst1 val2) (ap_Se (shift_subst s) e))
    with (ap_Se (cons_subst val2 s) e)
      by (rewrite <- cSS_subst1, <- ap_cSS_e; auto).
    auto.
    }

  { (* distval *)
    auto_specialize.
    unfold Real_Rel in H1.
    invert_ex.
    subst.
    rewrite H1.
    apply dist_preserves_Rel.
    }
Qed.




Theorem Fund_Thm: forall G o exp, @Fun_Thm_Exp G o exp.
Proof.
  apply (exp_val_rec Fun_Thm_Exp Fun_Thm_Val);
  unfold Fun_Thm_Exp;
  unfold Fun_Thm_Val;
  intros;
  simpl.

  (* valexp *)
  { specialize (H _ _ H0).
    exists (ap_Sv s v).
    split.
    apply ev_val.
    apply H.
    }

  { (* prodexp e1 e2 *)
    intros.
    specialize (H _ _ H1).
    specialize (H0 _ _ H1).
    destruct (den_expS e r), (den_expS e0 r); simpl; auto.
    simpl in *.
    inversion H.
    inversion H0.
    exists (prodval x x0).
    inversion H2; clear H2.
    inversion H3; clear H3.
    split.
    apply ev_prod; auto.
    unfold Prod_Rel.
    eauto.
  }

  { (* proj1exp e *)
    specialize (H r s H0); clear H0.
    destruct (den_expS e r); simpl; auto.
    inversion H. clear H. inversion H0. clear H0.
    unfold Rel in H1.
    simpl in H1.
    unfold Prod_Rel in H1.
    inversion H1; clear H1.
    inversion H0; clear H0.
    inversion H1; clear H1.
    inversion H2; clear H2.
    exists x0.
    split.
    apply (ev_proj1 _ x0 x1).
    rewrite H0 in H.
    apply H.
    auto.
  }
    
 { (* proj2exp e *)
    specialize (H r s H0); clear H0.
    destruct (den_expS e r); simpl; auto.
    inversion H. clear H. inversion H0. clear H0.
    unfold Rel in H1.
    simpl in H1.
    unfold Prod_Rel in H1.
    inversion H1; clear H1.
    inversion H0; clear H0.
    inversion H1; clear H1.
    inversion H2; clear H2.
    exists x1.
    split.
    apply (ev_proj2 _ x0 x1).
    rewrite H0 in H.
    apply H.
    auto.
  }


 { (* appexp e e0 *)
    specialize (H _ _ H1).
    specialize (H0 _ _ H1).
    destruct (den_expS e r), (den_expS e0 r); simpl in *; auto.

    (* work out the first reduction *)
    inversion H; clear H; intuition.
    inversion H0; clear H0; intuition.
    inversion H3 as [e']; clear H3; intuition.
    subst.
    (* H: ev (ap_Se s e) (absexp e') *)
    (* H0: ev (ap_Se s e0) x *)

    (* now the third reduction *)
    specialize (H5 _ _ H4).
    destruct (d d0); simpl in *; auto.
    inversion H5; clear H5; intuition.
    eauto using ev_app.

  }

  (* bindexp e e0 *)
  { specialize (H _ _ H1).
    specialize (H0 _ _ H1).
    destruct (den_expS e r), (den_expS e0 r); simpl in *; auto.
    inversion H0; inversion H; intuition.
    eauto using ev_bind, bind_preserves_Rel.
  }

  (* returnexp e *)
  { specialize (H _ _ H0).
    destruct (den_expS e r); simpl in *; auto.
    inversion H; intuition.
    eauto using ev_return, return_preserves_Rel.
    }

  (* constexp *)
  { unfold coerce_realS.
    unfold Real_Rel.
    eauto. }

  { (* prodval *)
    specialize (H r s H1).
    specialize (H0 r s H1).
    unfold Prod_Rel.
    eauto.
    }

  (* varexp  (which is a Val!) *)
    apply lookup_preserves_Rel. assumption.

  { (* absexp *)
    unfold Fun_Rel.
    exists (ap_Se (shift_subst s) e).
    split; auto.
    intros.

    assert (H2: (Rel_Env (cons_env a1 r) (cons_subst val2 s))).
    apply extend_env_preserves_Rel; auto.
    specialize (H _ _ H2).

    assert (H3: (ap_Se (cons_subst val2 s) e)
                =
                (ap_Se (subst1 val2) (ap_Se (shift_subst s) e))).
    rewrite <- cSS_subst1.
    rewrite <- ap_cSS_e.
    auto.
    rewrite <- H3 in *.
    apply H.
    }

  { (* uniformval *)
    unfold Meas_Rel.
    intros.
    unfold uniformopS.
    exists (constexp (unit_real u)). (* this could be an eexists *)
    split.
    apply evs_unif.
    simpl.
    unfold Real_Rel.
    eauto.
  }

  { (* distval *)
    (* this should be turned into a lemma distval_preserves_Rel *)
    specialize (H _ _ H0).
    unfold Rel in H.
    unfold Mtype_Rel in H.
    unfold Real_Rel in H.
    inversion H; clear H; intuition.
    subst.
    rewrite H.
    apply dist_preserves_Rel.
  }


  { (* bindval *)
    apply bind_preserves_Rel.
    specialize (H _ _ H1).
    specialize (H0 _ _ H1).
    apply H.
    specialize (H0 _ _ H1).
    apply H0.
  }

  { (* returnval *)
    apply return_preserves_Rel.
    specialize (H _ _ H0).
    apply H. }
Qed.