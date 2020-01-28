(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import tacs rel_utils list_utils.

Require Import formula sequent_rules.
Require Import relevant_LR1 mini_LI1.

Set Implicit Arguments.

Section Relational_phase_semantics.

  Variable M : Type.

  Implicit Types A B C : M -> Prop.

  Variable cl : (M -> Prop) -> (M -> Prop).

  Hypothesis cl_increase   : forall A, A inc1 cl A.
  Hypothesis cl_monotone   : forall A B, A inc1 B -> cl A inc1 cl B.
  Hypothesis cl_idempotent : forall A, cl (cl A) inc1 cl A.
  
  Proposition cl_prop A B : A inc1 cl B <-> cl A inc1 cl B.
  Proof.
    split; intros H x Hx.
    apply cl_idempotent; revert Hx; apply cl_monotone; auto.
    apply H, cl_increase; auto.
  Qed.
  
  Definition cl_inc A B := proj1 (cl_prop A B).
  Definition inc_cl A B := proj2 (cl_prop A B). 
  
  Fact cl_eq1 A B : A ~eq1 B -> cl A ~eq1 cl B.
  Proof.
    intros []; split; apply cl_monotone; auto.
  Qed.

  Hint Resolve cl_inc cl_eq1 : core. (* inc_cl. *)

  Notation closed := (fun x : M -> Prop => cl x inc1 x).
  
  Fact cl_closed A B : closed B -> A inc1 B -> cl A inc1 B.
  Proof.
    intros H1 H2.
    apply inc1_trans with (2 := H1), cl_inc, 
          inc1_trans with (1 := H2), cl_increase.
  Qed.

  (* this is a relational/non-deterministic monoid *)

  Variable Compose : M -> M -> M -> Prop.

  (* Composition lifted to predicates *)

  Inductive Composes (A B : M -> Prop) : M -> Prop :=
    In_composes : forall a b c, A a -> B b -> Compose a b c -> Composes A B c.

  Infix "ø" := Composes (at level 50, no associativity).

  Proposition composes_monotone A A' B B' : A inc1 A' -> B inc1 B' ->  A ø B inc1 A' ø B'.
  Proof. intros ? ? _ [ ? ? ? ? ? H ]; apply In_composes with (3 := H); auto. Qed.

  Hint Resolve composes_monotone : core.

  Variable e : M.

  (* Stability is the important axiom in phase semantics *)

  Definition cl_stability   := forall A B, cl A ø cl B inc1 cl (A ø B).
  Definition cl_stability_l := forall A B, cl A ø    B inc1 cl (A ø B).
  Definition cl_stability_r := forall A B,    A ø cl B inc1 cl (A ø B).

  Proposition cl_stable_imp_stable_l : cl_stability -> cl_stability_l.
  Proof. 
    intros H ? ? x Hx.
    apply H; revert x Hx. 
    apply composes_monotone; auto.
  Qed.

  Proposition cl_stable_imp_stable_r : cl_stability -> cl_stability_r.
  Proof. 
    intros H ? ? x Hx.
    apply H; revert x Hx. 
    apply composes_monotone; auto.
  Qed.

  Proposition cl_stable_lr_imp_stable : cl_stability_l -> cl_stability_r -> cl_stability.
  Proof. 
    intros H1 H2 A B x Hx.
    apply cl_idempotent.
    generalize (H1 _ _ _ Hx).
    apply cl_monotone, H2.
  Qed.

  Hint Resolve cl_stable_imp_stable_l cl_stable_imp_stable_r cl_stable_lr_imp_stable : core.
  
  Notation sg := (@eq _).

  Definition cl_neutrality_1 := forall a, cl (sg e ø sg a) a.
  Definition cl_neutrality_2 := forall a, sg e ø sg a inc1 cl (sg a).
  Definition cl_commutativity := forall a b, sg a ø sg b inc1 cl (sg b ø sg a).
  Definition cl_associativity := forall a b c, sg a ø (sg b ø sg c) inc1 cl ((sg a ø sg b) ø sg c).

  Hypothesis cl_commute : cl_commutativity.
  
  Fact sg_inc1 (A : M -> Prop) : forall x, A x -> sg x inc1 A.
  Proof. intros ? ? ? []; trivial. Qed.

  Proposition composes_commute_1 A B : A ø B inc1 cl (B ø A).
  Proof.
    intros _ [ a b c Ha Hb Hc ].
    apply cl_monotone with (sg b ø sg a).
    apply composes_monotone; apply sg_inc1; auto.
    apply cl_commute.
    constructor 1 with (3 := Hc); auto.
  Qed.

  Hint Resolve composes_commute_1 : core.

  Proposition composes_commute A B : cl (A ø B) ~eq1 cl (B ø A).
  Proof. 
    split; intros x Hx; apply cl_idempotent; revert Hx; apply cl_monotone; auto. 
  Qed. 

  Proposition cl_stable_l_imp_r : cl_stability_l -> cl_stability_r.
  Proof.
    intros Hl A B x Hx.
    apply cl_idempotent.
    apply cl_monotone with (cl B ø A).
    apply inc1_trans with (cl ((cl B) ø A)); auto.
    rewrite <- cl_prop; auto.
    generalize (@composes_commute_1 B A); intros H.
    rewrite cl_prop in H; auto.
    apply composes_commute_1; auto.
  Qed.
  
  Proposition cl_stable_r_imp_l : cl_stability_r -> cl_stability_l.
  Proof.
    intros Hl A B.
    generalize (@composes_commute_1 B A); intros H.
    rewrite cl_prop in H; auto.
    apply inc1_trans with (B := cl (B ø cl A)),
          inc1_trans with (2 := H); auto.
    rewrite <- cl_prop; apply Hl.
  Qed.

  Hint Resolve cl_stable_l_imp_r cl_stable_r_imp_l : core.
  
  Proposition cl_stable_l_imp_stable : cl_stability_l -> cl_stability.    Proof. auto. Qed. 
  Proposition cl_stable_r_imp_stable : cl_stability_r -> cl_stability.    Proof. auto. Qed.

  Hypothesis cl_stable_l : cl_stability_l.
  
  Proposition cl_stable_r : cl_stability_r.                               Proof. auto. Qed.
  Proposition cl_stable : cl_stability.                                   Proof. auto. Qed.

  Hint Resolve cl_stable_r cl_stable : core.

  Hypothesis cl_neutral_1 : cl_neutrality_1.
  Hypothesis cl_neutral_2 : cl_neutrality_2.
  Hypothesis cl_associative : cl_associativity.

  Definition Magicwand A B k := sg k ø A inc1 B.
  Infix "-ø" := Magicwand (at level 51, right associativity).

  Proposition magicwand_spec A B C : A ø B inc1 C <-> A inc1 B -ø C.
  Proof.
    split; intros H x Hx.
    intros y Hy; apply H; revert Hy; apply composes_monotone; auto.
    apply sg_inc1; auto.
    destruct Hx as [ a b x Ha Hb Hx ].
    apply (H _ Ha).
    constructor 1 with a b; auto.
  Qed.

  Definition magicwand_adj_1 A B C := proj1 (magicwand_spec A B C).
  Definition magicwand_adj_2 A B C := proj2 (magicwand_spec A B C).

(*  Hint Resolve magicwand_adj_1 magicwand_adj_2. *)

  Proposition magicwand_monotone A A' B B' : A inc1 A' -> B inc1 B' -> A' -ø B inc1 A -ø B'.
  Proof.
    intros ? HB; apply magicwand_adj_1, inc1_trans with (2 := HB).
    intros _ [? ? ? Ha ? Hc]; apply Ha, In_composes with (3 := Hc); auto.
  Qed.

  Hint Resolve magicwand_monotone : core.

  Proposition cl_magicwand_1 X Y : cl (X -ø cl Y) inc1 X -ø cl Y.
  Proof. 
    apply magicwand_adj_1, 
          inc1_trans with (B := cl ((X -ø cl Y) ø X)); auto.
    rewrite <- cl_prop; apply magicwand_spec; auto. 
  Qed.

  Proposition cl_magicwand_2 X Y : cl X -ø Y inc1 X -ø Y.
  Proof.
    apply magicwand_monotone; auto.
  Qed.
 
  Hint Immediate cl_magicwand_1 cl_magicwand_2 : core.

  Proposition cl_magicwand_3 X Y : X -ø cl Y inc1 cl X -ø cl Y.
  Proof.
    intros c Hc y.
    apply inc1_trans with (B := cl (sg c ø X)); auto.
    rewrite <- cl_prop.
    intros ? [ a b d [] Hb ].
    intros; apply Hc. 
    constructor 1 with c b; auto.
  Qed.

  Hint Immediate cl_magicwand_3 : core.

  Proposition closed_magicwand X Y : closed Y -> closed (X -ø Y).
  Proof. 
    simpl; intros ?.
    apply inc1_trans with (B := cl (X -ø cl Y)); auto.
    apply cl_monotone, magicwand_monotone; auto.
    apply inc1_trans with (B := X -ø cl Y); auto.
    apply magicwand_monotone; auto.
  Qed.

  Hint Resolve closed_magicwand : core.

  Proposition magicwand_eq_1 X Y : X -ø cl Y ~eq1 cl X -ø cl Y.
  Proof. split; auto. Qed.

  Proposition magicwand_eq_2 X Y : cl (X -ø cl Y) ~eq1 X -ø cl Y.
  Proof. split; auto. Qed.

  Proposition magicwand_eq_3 X Y : cl (X -ø cl Y) ~eq1 cl X -ø cl Y.
  Proof.
    split; auto.
    apply inc1_trans with (B := X -ø cl Y); auto.
  Qed.

  Hint Resolve magicwand_eq_1 magicwand_eq_2 magicwand_eq_3 : core.

  Proposition cl_equiv_2 X Y : cl (cl X ø Y) ~eq1 cl (X ø Y).
  Proof. 
    split.
    rewrite <- cl_prop; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_3 X Y : cl (X ø cl Y) ~eq1 cl (X ø Y).
  Proof.
    split.
    rewrite <- cl_prop; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Proposition cl_equiv_4 X Y : cl (cl X ø cl Y) ~eq1 cl (X ø Y).
  Proof. 
    split.
    rewrite <- cl_prop; auto.
    apply cl_monotone, composes_monotone; auto.
  Qed.

  Hint Immediate cl_equiv_2 cl_equiv_3 cl_equiv_4 : core.

  Proposition composes_associative_1 A B C : A ø (B ø C) inc1 cl ((A ø B) ø C).
  Proof.
    intros _ [a _ k Ha [b c y Hb Hc Hy] Hk].
    generalize (@cl_associative a b c k); intros H.
    spec_all H.
    apply In_composes with (3 := Hk); auto.
    apply In_composes with (3 := Hy); auto.
    revert H.
    apply cl_monotone.
    repeat apply composes_monotone; apply sg_inc1; auto.
  Qed.

  Hint Immediate composes_associative_1 : core.

  Proposition composes_associative A B C : cl (A ø (B ø C)) ~eq1 cl ((A ø B) ø C).
  Proof.
    split; auto.
    rewrite <- cl_prop; auto.
    rewrite <- cl_prop; auto.
    apply inc1_trans with (1 := @composes_commute_1 _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (B := C ø cl (A ø B)); auto.
    apply composes_monotone; auto.
    apply inc1_trans with (B := C ø cl (B ø A)); auto.
    apply composes_monotone; auto.
    apply composes_commute.
    apply inc1_trans with (1 := @cl_stable_r _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @composes_associative_1 _ _ _).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @composes_commute_1 _ _). 
    rewrite <- cl_prop.
    apply inc1_trans with (B := A ø cl (C ø B)); auto.
    apply composes_monotone; auto.
    apply inc1_trans with (B := A ø cl (B ø C)); auto.
    apply composes_monotone; auto.
    apply composes_commute.
  Qed.

  Hint Immediate composes_associative : core.

  Proposition composes_congruent_1 A B C : A inc1 cl B -> C ø A inc1 cl (C ø B).
  Proof.
    intros ?.
    apply inc1_trans with (B := cl (C ø cl B)); auto.
    apply cl_prop, cl_monotone, composes_monotone; auto.
    apply cl_equiv_3.
  Qed.

  Hint Resolve composes_congruent_1 : core.

  Proposition composes_congruent A B C : cl A ~eq1 cl B -> cl (C ø A) ~eq1 cl (C ø B).
  Proof. 
    intros [H1 H2].
    rewrite <- cl_prop in H1.
    rewrite <- cl_prop in H2.
    split; rewrite <- cl_prop;
    apply inc1_trans with (2 := @cl_stable_r _ _), composes_monotone; auto.
  Qed.

  Proposition composes_assoc_special A A' B B' : cl((A ø A') ø (B ø B')) ~eq1 cl ((A ø B) ø (A' ø B')).
  Proof.
    do 2 apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent.
    apply eq1_sym, eq1_trans with (1 := composes_commute _ _).
    apply eq1_sym, eq1_trans with (2 := composes_associative _ _ _).
    apply composes_congruent, composes_commute.
  Qed.

  Definition composes_assoc_special_1 A A' B B' := proj1 (composes_assoc_special A A' B B').
  
  Proposition composes_neutral_1 A : A inc1 cl (sg e ø A).
  Proof.
    intros a Ha.
    generalize (cl_neutral_1 a).
    apply cl_monotone, composes_monotone; auto.
    apply sg_inc1; auto.
  Qed.

  Proposition composes_neutral_2 A : sg e ø A inc1 cl A.
  Proof.
    intros _ [y a x [] Ha Hx].
    generalize (@cl_neutral_2 a x); intros H.
    spec_all H.
    constructor 1 with e a; auto.
    revert H; apply cl_monotone, sg_inc1; auto.
  Qed.
  
  Hint Resolve composes_neutral_1 composes_neutral_2 : core.

  Proposition composes_neutral A : cl (sg e ø A) ~eq1 cl A.
  Proof. split; rewrite <- cl_prop; auto. Qed.

  Notation "x 'glb' y " := (x cap1 y) (at level 60, no associativity).
  Notation "x 'lub' y" := (cl (x cup1 y)) (at level 60, no associativity).

  Proposition closed_glb A B : closed A -> closed B -> closed (A glb B).
  Proof. 
    simpl; intros HA HB x Hx; split; 
      [ apply HA | apply HB ]; revert x Hx; 
      apply cl_monotone; tauto. 
  Qed.

  Proposition lub_out A B C : closed C -> A inc1 C -> B inc1 C -> A lub B inc1 C.
  Proof. 
    simpl.
    intros H1 H2 H3.
    apply inc1_trans with (2 := H1), cl_monotone.
    intros ? [ ]; auto.
  Qed.

  Proposition glb_in A B C : C inc1 A -> C inc1 B -> C inc1 A glb B.
  Proof. simpl; split; auto. Qed. 

  Proposition closed_lub A B : closed (cl (A cup1 B)).     Proof. simpl; apply cl_idempotent. Qed.
  Proposition glb_out_l A B  : A glb B inc1 A .            Proof. simpl; tauto. Qed.
  Proposition glb_out_r A B  : A glb B inc1 B.             Proof. simpl; tauto. Qed.
  Proposition lub_in_l A B   : A inc1 A lub B.             Proof. apply inc1_trans with (2 := cl_increase _); tauto. Qed.
  Proposition lub_in_r A B   : B inc1 A lub B.             Proof. apply inc1_trans with (2 := cl_increase _); tauto. Qed.

  Notation "x '**' y " := (cl (x ø y)) (at level 59).

  Proposition closed_times A B : closed (A ** B).
  Proof. simpl; apply cl_idempotent. Qed.

  Proposition times_monotone A A' B B' : A inc1 A' -> B inc1 B' -> A ** B inc1 A' ** B'.
  Proof. simpl; intros ? ?; apply cl_monotone, composes_monotone; auto. Qed.

  Notation top := (fun _ : M => True).
  Notation bot := (cl (fun _ => False)).
  Notation unit := (cl (sg e)). 

  Proposition closed_top     : closed top.         Proof. simpl; intros; auto. Qed. 
  Proposition closed_bot     : closed bot.         Proof. simpl; apply cl_idempotent. Qed.
  Proposition closed_unit    : closed unit.        Proof. simpl; apply cl_idempotent. Qed.
  Proposition top_greatest A : A inc1 top.         Proof. simpl; tauto. Qed. 

  Proposition bot_least A : closed A -> bot inc1 A.
  Proof. intro H; apply inc1_trans with (2 := H), cl_monotone; tauto. Qed.

  Proposition unit_neutral_1 A : closed A -> unit ** A inc1 A.
  Proof. 
    intros H; apply inc1_trans with (2 := H).
    rewrite <- cl_prop.
    apply inc1_trans with (1 := @cl_stable_l _ _).
    rewrite <- cl_prop.
    apply composes_neutral_2.
  Qed.

  Proposition unit_neutral_2 A : A inc1 unit ** A.
  Proof. 
    intros a Ha; simpl.
    generalize (composes_neutral_1 _ _ Ha).
    apply cl_monotone, composes_monotone; auto.
  Qed.
  
(*  Hint Resolve unit_neutral_1 unit_neutral_2. *)

  Proposition unit_neutral A : closed A -> unit ** A ~eq1 A.
  Proof. 
    intros H; split. 
    revert H; apply unit_neutral_1.
    apply unit_neutral_2.
  Qed.

  Proposition times_commute_1 A B : A ** B inc1 B ** A.
  Proof. simpl; apply cl_inc, composes_commute_1. Qed.

  Hint Resolve unit_neutral times_commute_1 : core.
 
  Proposition times_commute A B : A ** B ~eq1 B ** A.
  Proof. split; auto. Qed.

  Proposition unit_neutral' A : closed A -> A ** unit ~eq1 A.
  Proof. intros ?; apply eq1_trans with (1 := times_commute _ _); auto. Qed.

  Proposition times_associative A B C : ((A ** B) ** C) ~eq1 (A ** (B ** C)).
  Proof.
    apply eq1_sym, eq1_trans with (1 := cl_equiv_3 _ _ ).
    apply eq1_sym, eq1_trans with (1 := cl_equiv_2 _ _ ).
    apply eq1_sym, composes_associative.
  Qed.

  Proposition times_associative_1 A B C : (A ** B) ** C inc1 A ** (B ** C).
  Proof. apply times_associative. Qed.

  Proposition times_associative_2 A B C : A ** (B ** C) inc1 (A ** B) ** C.
  Proof. apply times_associative. Qed.

  Hint Resolve times_associative_1 times_associative_2 : core.

  Proposition times_congruence A A' B B' : A ~eq1 A' -> B ~eq1 B' -> A ** B ~eq1 A' ** B'.
  Proof. 
    intros H1 H2.
    apply eq1_trans with (A ** B').
    apply composes_congruent; auto.
    do 2 apply eq1_sym, eq1_trans with (1 := times_commute _ _).
    apply composes_congruent; auto.
  Qed.
 
  Proposition adjunction_1 A B C : closed C -> A ** B inc1 C -> A inc1 B -ø C.
  Proof. intros ? H; apply magicwand_adj_1, inc1_trans with (2 := H); auto. Qed.

  Proposition adjunction_2 A B C : closed C -> A inc1 B -ø C -> A ** B inc1 C.
  Proof. intros H ?; apply inc1_trans with (2 := H), cl_monotone, magicwand_adj_2; auto. Qed.

  Hint Resolve times_congruence adjunction_1 (* adjunction_2 *) : core.
 
  Proposition adjunction A B C : closed C -> (A ** B inc1 C <-> A inc1 B -ø C).
  Proof.
    split; [ apply adjunction_1 | apply  adjunction_2 ]; auto.
  Qed.

  Proposition times_bot_distrib_l A : bot ** A inc1 bot.
  Proof.
    apply adjunction_2; auto.
    apply bot_least; auto.
  Qed.

  Proposition times_bot_distrib_r A : A ** bot inc1 bot.
  Proof. apply inc1_trans with (1 := @times_commute_1 _ _), times_bot_distrib_l. Qed.
 
  Hint Immediate times_bot_distrib_l times_bot_distrib_r : core.

  Proposition times_lub_distrib_l A B C : (A lub B) ** C inc1 (A ** C) lub (B ** C).
  Proof. 
    apply adjunction, lub_out; auto;
    apply adjunction; auto. 
  Qed.

  Proposition times_lub_distrib_r A B C : C ** (A lub B) inc1 (C ** A) lub (C ** B).
  Proof. 
    apply inc1_trans with (1 := @times_commute_1 _ _),
          inc1_trans with (1 := @times_lub_distrib_l _ _ _); auto.
    apply lub_out; auto.
  Qed.

  Reserved Notation "'[[' x ']]'" (at level 50).
  Reserved Notation "'[|' x '|]'" (at level 50).
  
  Variable (v : Var -> M -> Prop) (Hv : forall x, cl (v x) inc1 v x).
  
  Fixpoint Form_sem f :=
    match f with
      | £ x    => v x
      | a %> b => [[a]] -ø [[b]]
    end
  where "[[ a ]]" := (Form_sem a).
  
  Fact cl_Form_sem f : cl ([[f]]) inc1 [[f]].
  Proof.
    induction f; simpl; auto.
  Qed.
  
  Fixpoint FList_sem ll :=
    match ll with
      | nil   => unit
      | x::ll => [[x]] ** [|ll|]
    end
  where "[| ll |]" := (FList_sem ll).
  
  Fact cl_FList_sem ll : cl ([|ll|]) inc1 [|ll|].
  Proof.
    induction ll; simpl; auto.
  Qed.
  
  Hint Resolve cl_Form_sem cl_FList_sem : core.
  
  Fact FList_sem_app l m : [|l++m|] ~eq1 [|l|] ** [|m|].
  Proof.
    induction l; simpl.
    apply eq1_sym, unit_neutral; auto.
    apply eq1_sym, eq1_trans with (1 := @times_associative _ _ _), eq1_sym.
    apply times_congruence; auto.
  Qed.
  
  Fact FList_sem_perm l m : l ~p m -> [|l|] ~eq1 [|m|].
  Proof.
    induction 1 as [ | x l m _ IHl | x y l | l m k ]; auto.
    apply composes_congruent, cl_eq1; auto.
    simpl; do 2 apply eq1_sym, eq1_trans with (2 := @times_associative _ _ _).
    apply times_congruence; auto.
    apply eq1_trans with ([|m|]); auto.
  Qed.
  
  Definition cl_weak_hyp := forall x, cl (sg e) x.
  Definition cl_cntr_hyp := forall x, cl (sg x ø sg x) x.

  Hypothesis cl_weak : cl_weak_hyp.
  Hypothesis cl_cntr : cl_cntr_hyp.
  
  Proposition cl_weakening A : A inc1 unit.
  Proof.
    intros x Hx.
    apply cl_weak.
  Qed.
  
  Proposition cl_contract A : A inc1 A ** A.
  Proof.
    intros x Hx.
    generalize (cl_cntr x).
    apply times_monotone;
    intros ? []; auto.
  Qed.
  
  Theorem sem_LR1_sound : forall s, LR1_provable s -> [|fst s|] inc1 [[snd s]].
  Proof.
    induction 1 as [ A 
                   | ga A B IH 
                   | ga de th A B C H1 IH1 IH2 
                   | ga de A B H1 IH 
                   | ga de th A B H1 IH1 IH2 ] using LR1_provable_ind; simpl in * |- *.
 
    apply inc1_trans with (1 := @times_commute_1 _ _), unit_neutral_1; auto.
    
    apply adjunction_1; auto.
    
    apply inc1_trans with (1 := proj1 (FList_sem_perm H1)),
          inc1_trans with (2 := IH2).
    simpl.
    apply inc1_trans with ([[A]] -ø[[B]] ** ([|ga|] ** [|de|])).
    apply times_congruence; auto.
    apply eq1_sym, FList_sem_app.
    apply inc1_trans with (1 := @times_associative_2 _ _ _).
    apply times_monotone; auto.
    apply inc1_trans with ([[A]] -ø[[B]] ** [[A]]).
    apply times_monotone; auto.
    apply adjunction_2; auto.
    
    apply inc1_trans with (2 := IH),
          inc1_trans with (1 := proj1 (FList_sem_perm H1)).
    apply inc1_trans with (2 := @times_associative_1 _ _ _).
    simpl; apply times_monotone; auto.
    apply cl_contract.
    
    apply inc1_trans with (2 := IH2),
          inc1_trans with (1 := proj1 (FList_sem_perm H1)),
          inc1_trans with (1 := proj1 (FList_sem_app _ _)).
    apply times_monotone; auto.
  Qed.
  
  Theorem sem_LI1_sound : forall s, LI1_provable s -> [|fst s|] inc1 [[snd s]].
  Proof.
    induction 1 as [ A 
                   | ga A B IH 
                   | ga de th A B C H1 IH1 IH2 
                   | ga de A B H1 IH 
                   | ga de A B H1 IH
                   | ga de th A B H1 IH1 IH2 ] using LI1_provable_ind; simpl in * |- *.
 
    apply inc1_trans with (1 := @times_commute_1 _ _), unit_neutral_1; auto.
    
    apply adjunction_1; auto.
    
    apply inc1_trans with (1 := proj1 (FList_sem_perm H1)),
          inc1_trans with (2 := IH2).
    simpl.
    apply inc1_trans with ([[A]] -ø[[B]] ** ([|ga|] ** [|de|])).
    apply times_congruence; auto.
    apply eq1_sym, FList_sem_app.
    apply inc1_trans with (1 := @times_associative_2 _ _ _).
    apply times_monotone; auto.
    apply inc1_trans with ([[A]] -ø[[B]] ** [[A]]).
    apply times_monotone; auto.
    apply adjunction_2; auto.
    
    apply inc1_trans with (2 := IH),
          inc1_trans with (1 := proj1 (FList_sem_perm H1)).
    apply inc1_trans with (2 := @times_associative_1 _ _ _).
    simpl; apply times_monotone; auto.
    apply cl_contract.
    
    apply inc1_trans with (2 := IH),
          inc1_trans with (1 := proj1 (FList_sem_perm H1)).
    apply inc1_trans with (2 := unit_neutral_1 (cl_FList_sem _)).
    simpl; apply times_monotone; auto.
    
    apply inc1_trans with (2 := IH2),
          inc1_trans with (1 := proj1 (FList_sem_perm H1)),
          inc1_trans with (1 := proj1 (FList_sem_app _ _)).
    apply times_monotone; auto.
  Qed.
  
End Relational_phase_semantics.

Section Cut_Adm.

  Local Notation " l '≻c' m " := (list_contract Form_eq_dec l m) (at level 70, no associativity).

  Variable (P : list Form -> Form -> Prop).

  Notation " g '|--' a " := (P g a) (at level 70, no associativity).

  Implicit Types (X Y : list Form -> Prop).

  Local Definition cl X de := forall ga x, (forall th, X th -> ga++th |-- x) -> ga++de |-- x.
  
  Local Fact cl_increase X : X inc1 cl X.
  Proof.
    intros ? ? ? ?; auto.
  Qed.
  
  Local Fact cl_mono X Y : X inc1 Y -> cl X inc1 cl Y.
  Proof.
    intros H1 de Hde ga x HY.
    apply Hde.
    intros; apply HY, H1; auto.
  Qed.
  
  Local Fact cl_idem X : cl (cl X) inc1 cl X.
  Proof.
    intros de Hde ga x HX.
    apply Hde.
    intros th Hth.
    apply Hth, HX.
  Qed.
  
  Local Definition comp (ga de th : list Form) := ga ++ de ~p th.
  Local Definition e : list Form := nil.
  
  Local Fact cl_comm : cl_commutativity cl comp.
  Proof.
    intros ga de _ [ ga' de' th ]. 
    intros; subst ga' de'.
    intros rho x H; apply H.
    constructor 1 with de ga; auto.
    revert H1; unfold comp.
    apply perm_trans, Permutation_app_comm.
  Qed.
  
  Local Fact cl_neutral_1 : cl_neutrality_1 cl comp e.
  Proof.
    intros l th x H.
    apply H.
    constructor 1 with nil l; auto.
    red; simpl; auto.
  Qed.
  
  Hypothesis HP_perm : forall ga de x, ga ~p de -> ga |-- x -> de |-- x.
  
  Local Fact cl_neutral_2 : cl_neutrality_2 cl comp e.
  Proof.
    intros ga ? [ de th ka ? ? H1 ] rho x G; subst th de.
    cbv in H1.
    generalize (G _ eq_refl).
    apply HP_perm, Permutation_app; auto.
  Qed.

  Local Fact cl_stable_l : cl_stability_l cl comp.
  Proof.
    intros X Y _ [ ga de th H1 H2 H3 ] rho x HXY.
    red in H1.
    apply HP_perm with ((rho++de)++ga).
    rewrite app_ass.
    apply Permutation_app; auto.
    apply perm_trans with (2 := H3), Permutation_app_comm.
    apply H1.
    intros ka Hka.
    rewrite app_ass.
    apply HXY.
    constructor 1 with ka de; auto.
    apply Permutation_app_comm.
  Qed.
  
  Local Fact cl_assoc : cl_associativity cl comp.
  Proof.
    intros ga de th _ [ ga' rho ka H2 H3 H4 ].
    destruct H3 as [ de' th' to ]; subst ga' de' th'.
    intros u x Hu.
    specialize (Hu ((ga++de)++th)).
    spec_all Hu.
    constructor 1 with (ga++de) th; auto.
    constructor 1 with ga de; auto.
    red; auto.
    red; auto.
    revert Hu.
    apply HP_perm, Permutation_app; auto.
    rewrite app_ass.
    apply Permutation_trans with (2 := H4).
    apply Permutation_app; auto.
  Qed.
  
  Hypothesis HP_contract : forall ga de x, ga ≻c de -> ga |-- x -> de |-- x.
  
  Local Fact cl_cntr : cl_cntr_hyp cl comp.
  Proof.
    intros ga rho x H.
    specialize (H (ga++ga)).
    spec_all H.
    constructor 1 with ga ga; cbv; auto.
    revert H; apply HP_contract.
    intros d; repeat rewrite occ_app.
    unfold nat_contract; omega.
  Qed.
  
  Hypothesis HP_weak : forall ga de x, ga |-- x -> ga++de |-- x.
  
  Local Fact cl_weak : cl_weak_hyp cl nil.
  Proof.
    intros ga rho x H.
    generalize (H _ eq_refl).
    rewrite <- app_nil_end.
    apply HP_weak.
  Qed.
  
  Local Definition dc a ga := ga |-- a.
  
  Local Definition v x := dc (£ x).
  
  Local Fact Hv x : cl (v x) inc1 v x.
  Proof.
    intros ga Hga.
    apply (Hga nil).
    simpl; auto.
  Qed.
  
  Local Definition cl_LR1_sound := @sem_LR1_sound _ _ cl_increase cl_mono cl_idem comp 
                                    _ cl_comm cl_stable_l cl_neutral_1 cl_neutral_2 cl_assoc 
                                    _ Hv cl_cntr.
  
  Local Definition cl_LI1_sound := @sem_LI1_sound _ _ cl_increase cl_mono cl_idem comp 
                                      _ cl_comm cl_stable_l cl_neutral_1 cl_neutral_2 cl_assoc 
                                      _ Hv cl_weak cl_cntr.
                                    
  Hypothesis HP_id : forall x, x :: nil |-- x.
  
  Local Fact rule_id x : Form_sem comp v (£ x) (£ x::nil).
  Proof. simpl; apply HP_id. Qed.
  
  Notation sg := (@eq _).
  Infix "-ø" := (Magicwand comp) (at level 51, right associativity).
  
  Hypothesis HP_r : forall ga a b, a::ga |-- b -> ga |-- a %> b.
  
  Local Fact rule_r A B : sg (A :: nil) -ø dc B inc1 dc (A %> B).
  Proof.
    intros th Hth.
    apply HP_r, Hth.
    constructor 1 with th (A :: nil); auto.
    apply Permutation_app_comm.
  Qed.
  
  Hypothesis HP_l : forall ga de a b c, ga |-- a -> b::de |-- c -> a%>b::ga++de |-- c.
  
  Local Fact rule_l A B : (dc A -ø cl (sg (B:: nil))) (A %> B :: nil).
  Proof.
    intros th Hth de C H.
    destruct Hth as [ rho ga th H1 H2 H3 ].
    subst rho; red in H3; simpl in H3.
    apply HP_perm with (A%>B::ga++de).
    apply perm_trans with (2 := Permutation_app_comm _ _). 
    apply Permutation_app with (1 := H3); auto.
    apply HP_l; auto.
    generalize (H _ eq_refl).
    apply HP_perm, Permutation_app_comm.
  Qed.
  
  Hint Resolve cl_increase cl_mono cl_idem cl_stable_l Hv : core.
  
  Local Fact mw_mono (X Y X' Y' : _ -> Prop) : X inc1 X' -> Y inc1 Y' -> X' -ø Y inc1 X -ø Y'.
  Proof.
    apply magicwand_monotone; auto.
  Qed.
  
  Local Fact cl_sem A : cl (Form_sem comp v A) inc1 Form_sem comp v A.
  Proof.
    apply cl_Form_sem; eauto.
  Qed.
  
  Local Fact cl_clos (A B : _ -> Prop) : cl B inc1 B -> A inc1 B -> cl A inc1 B.
  Proof.
    apply cl_closed; eauto.
  Qed.
   
  Local Lemma cl_Okada A : Form_sem comp v A (A::nil) 
                        /\ Form_sem comp v A inc1 fun ga => ga |-- A.
  Proof.
    induction A as [ x | A [ HA1 HA2 ] B [ HB1 HB2 ] ]; simpl; split.
    
    apply rule_id.
    intros ga; auto.
    
    generalize (@rule_l A B).
    apply mw_mono; auto.
    apply cl_clos; auto.
    apply cl_sem; auto.
    intros ? []; auto.
    
    intros th Hth.
    apply (@rule_r A B).
    revert Hth.
    revert th; apply mw_mono; auto.
    intros ? []; auto.
  Qed.
  
  Local Lemma cl_Okada_ctx ga : FList_sem cl comp e v ga ga.
  Proof.
    induction ga as [ | A ga Hga ]; simpl; 
      apply cl_increase; auto.
    constructor 1 with (A :: nil) ga; auto.
    apply cl_Okada.
    apply Permutation_refl.
  Qed.

End Cut_Adm.

Local Hint Resolve LR1_cf_provable_perm 
                   LR1_cf_provable_contract
                   LR1_cf_provable_id LR1_cf_provable_r : core.

Theorem LR1_cut_admissibility : LR1_provable inc1 LR1_cf_provable.
Proof.
  intros (ga,A) H.
  apply cl_Okada with (P := fun ga a => LR1_cf_provable (ga,a)); auto.
  apply LR1_cf_provable_perm.
  intros ? ? ? ? ?; apply LR1_cf_provable_l; auto.
  
  apply cl_LR1_sound with (3 := H); simpl; auto.
  apply LR1_cf_provable_perm.
  apply LR1_cf_provable_contract.
  apply cl_Okada_ctx; auto.
  apply LR1_cf_provable_perm.
  intros ? ? ? ? ?; apply LR1_cf_provable_l; auto.
Qed.

Local Hint Resolve LI1_cf_provable_perm 
                   LI1_cf_provable_contract LI1_cf_provable_weakening
                   LI1_cf_provable_id LI1_cf_provable_r : core.

Theorem LI1_cut_admissibility : LI1_provable inc1 LI1_cf_provable.
Proof.
  intros (ga,A) H.
  apply cl_Okada with (P := fun ga a => LI1_cf_provable (ga,a)); auto.
  apply LI1_cf_provable_perm.
  intros ? ? ? ? ?; apply LI1_cf_provable_l; auto.
  
  apply cl_LI1_sound with (4 := H); simpl; auto.
  apply LI1_cf_provable_perm.
  apply LI1_cf_provable_contract.
  apply cl_Okada_ctx; auto.
  apply LI1_cf_provable_perm.
  intros ? ? ? ? ?; apply LI1_cf_provable_l; auto.
Qed.


