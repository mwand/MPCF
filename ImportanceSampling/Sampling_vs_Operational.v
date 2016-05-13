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

Ltac auto_specialize :=
  repeat
    match goal with
    | [ H : forall x : ?a, _, v : ?a |- _ ] => specialize H with (x:=v)
    | [ H : ?a -> _, v : ?a |- _ ] =>
      let Hv := fresh H in
      apply H in v as Hv; clear H
    end.



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

Function Prod_Rel {ma mb : Mtype}
         (RA : (den_Mtype ma) -> (Val nil (Stype ma)) -> Prop)
         (RB : (den_Mtype mb) -> (Val nil (Stype mb)) -> Prop)
         (d  : (den_Mtype (Prod_type ma mb)))
         (val : (Val nil (Stype (Prod_type ma mb))))
  := 
    exists e1 e2, val = prodval e1 e2 /\
                  (RA (fst d) e1) /\ (RB (snd d) e2).

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

Ltac destruct_lift :=
  match goal with
  | [ H : lift_Rel _ ?x _ |- _ ] =>
    match x with
    | bottom => fail 1
    | lift _ => fail 1
    | _ => destruct x
    end
  end.

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

Definition Meas_Rel
           (m : Mtype)
           (s : den_typeS (Meastype m))
           (c : Val nil (Meastype m)) : Prop :=
  forall (u:Unit),
    match (s u) with
      | bottom => True
      | lift (a,w) => exists c', evs u c c' w /\ Mtype_Rel m a c'
    end.

Ltac destruct_lift_match :=
  match goal with
  | [ |- context[match ?x with
                 | bottom => _
                 | lift _ => _
                 end]] =>
    destruct x eqn:?; try false_invert; auto
  | [ |- context[strict2 ?x _] ] =>
    destruct x eqn:?; try false_invert; auto
  | [ |- context[strict ?x _] ] =>
    destruct x eqn:?; try false_invert; auto
  | [ H : context[match ?x with
                 | bottom => _
                 | lift _ => _
                 end] |- _] =>
    destruct x eqn:?; try false_invert; auto; simpl in H
  | [ H : context[strict2 ?x _] |- _ ] =>
    destruct x eqn:?; try false_invert; auto; simpl in H
  | [ H : context[strict ?x _] |- _ ] =>
    destruct x eqn:?; try false_invert; auto; simpl in H
  end.

(* Unpack a goal that has type Meas_Rel *)
Ltac destruct_Meas_Rel :=
  intros;
  lazymatch goal with
  | [ |- Meas_Rel ?m ?s ?c ] =>
    let Hsu := fresh "Hsu" in
    unfold Meas_Rel;
    intro u;
    destruct (s u) as [|p] eqn:Hsu;
    [trivial|]; (* takes care of bottom case *)
    simpl in Hsu;
    destruct p;
    autounfold in Hsu;
    unfold strict2, prod_curry, strict in Hsu;
    repeat (destruct_lift_match;
            try destruct p);
    inversion Hsu;
    subst; clear Hsu
  | _ => fail "Not Meas_Rel."
  end.

(* Unpack a hypothesis that has type Meas_Rel.
   H is the hypothesis to invert.
   u is the entropy to use. *)
Ltac invert_Meas_Rel H u :=
  lazymatch type of H with
  | Meas_Rel _ ?s1 _ =>
    unfold Meas_Rel in H;
    specialize (H u);
    match goal with
    | [ Hueq : s1 u = _ |- _ ] => rewrite Hueq in H
    | [ Hueq : _ = s1 u |- _ ] => rewrite <- Hueq in H
    end;
    let c := fresh "c" in
    let H1 := fresh H in
    inversion H as [c H1]; clear H;
    inversion H1; clear H1
  | _ => fail "Not Meas_Rel."
  end.

(* Unpack a hypothesis that has type Fun_Rel *)
Ltac invert_Fun_Rel H HRel :=
  lazymatch type of H with
  | Fun_Rel _ _ ?f _ => 
    unfold Fun_Rel in H;
    let H0 := fresh H in
    let e := fresh "e" in
    inversion H as [e H0]; clear H;
    let H1 := fresh H in
    let H2 := fresh H in
    inversion H0 as [H1 H2]; clear H0;
    specialize (H2 _ _ HRel);
    unfold lift_Rel in H2;
    match goal with
    | [ Heq : f _ = _ |- _ ] => rewrite Heq in H2
    | [ Heq : _ = f _ |- _ ] => rewrite <- Heq in H2
    end;
    simpl in H2;
    let H3 := fresh H in
    let v := fresh "v" in
    inversion H2 as [v H3]; clear H2;
    inversion H3; clear H3
  | _ => fail "Not Fun_Rel"
  end.

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
  induction G as [| o' G'];
    try false_invert.
  (* G = o' :: G' *)
  induction var as [| G'']; simpl.
  (* var = var_0 *)
  - inversion H.
    assumption.
  (* var = var_S v' *)
  - apply (IHvar _ (tl_subst s)); auto.
    apply H.
Qed.

Lemma extend_env_preserves_Rel :
  forall (o: Otype) G r (s : Subst G nil) (d : den_typeS o) (val: Val nil o),
    Rel_Env r s -> Rel d val
    -> Rel_Env (cons_env d r) (cons_subst val s).
Proof.
  simpl; auto.
Qed.

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
  destruct_Meas_Rel.

  invert_Meas_Rel H (left_half u).
  invert_Fun_Rel H0 H2.
  invert_Meas_Rel H3 (right_half u).

  subst; eauto.
Qed.

Hint Resolve bind_preserves_Rel.

Lemma return_preserves_Rel :
  forall m (v : den_typeS (Stype m)) (c : Val nil (Stype m)),
         Rel v c ->
         Meas_Rel m (returnopS v) (returnval c).
Proof.
  destruct_Meas_Rel.
  eauto.
Qed.

Hint Resolve return_preserves_Rel.

Lemma unif_preserves_Rel :
  Meas_Rel _ uniformopS uniformval.
Proof.
  destruct_Meas_Rel.
  unfold Mtype_Rel, Real_Rel.
  eauto.
Qed.

Hint Resolve unif_preserves_Rel.

Lemma dist_preserves_Rel :
  forall r,
    Meas_Rel _ (distvalS r) (distval (constexp r)).
Proof.
  destruct_Meas_Rel.
  unfold Mtype_Rel, Real_Rel.
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

Theorem Fund_Thm: forall G o exp, @Fun_Thm_Exp G o exp.
Proof.
  apply (exp_val_rec Fun_Thm_Exp Fun_Thm_Val);
    unfold Fun_Thm_Exp; unfold Fun_Thm_Val;
      simpl;
      intros;
      try solve [ auto_specialize; eauto;
                  repeat destruct_lift;
                  unfold Prod_Rel, lift_Rel in *;
                  solve_ex; subst; eauto ].

  { (* appexp e e0 *)
    auto_specialize.
    repeat destruct_lift; eauto.
    simpl in *.
    invert_ex.
    inversion H4; clear H4.
    intuition; subst.
    auto_specialize.
    destruct (d0 d); unfold lift_Rel; eauto.
    unfold lift_Rel in *.
    apply H5 in H3.
    solve_ex; eauto.
  }

  (* varexp *)
  apply lookup_preserves_Rel; auto.

  { (* absexp *)
    unfold Fun_Rel.
    solve_ex.

    replace (ap_Se (subst1 val2) (ap_Se (shift_subst s) e))
    with (ap_Se (cons_subst val2 s) e)
      by (rewrite <- cSS_subst1, <- ap_cSS_e; auto).

    auto.
  }

  { (* distval *)
    (* this should be turned into a lemma *)
    destruct_Meas_Rel.
    unfold Mtype_Rel, Real_Rel.
    auto_specialize.
    inversion H1.
    intuition; subst.
    rewrite H2.
    eauto.
  }
Qed.
