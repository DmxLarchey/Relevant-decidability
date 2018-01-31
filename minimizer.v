(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega.
Require Import List.

Require Import list_utils.
Require Import finite.

Set Implicit Arguments.

Section minimizer.

  Variable (X : Type) (f : X -> nat).
  
  Let minimizer_rec n ll : 1 <= length ll < n -> { a | In a ll /\ forall b, In b ll -> f a <= f b }.
  Proof.
    revert ll.
    induction n as [ | n IHn ]; intros ll (H1 & H2).
    omega.
    destruct ll as [ | a ll ].
    contradict H1; simpl; omega.
    destruct (list_dec_rec (fun b => f b < f a) ll) as [ (a' & Ha1 & Ha2) | Ha ].
    intros; apply lt_dec.
    
    destruct (IHn ll) as (m & H3 & H4).
    split.
    destruct ll; simpl in H2 |- *; try omega.
    destruct Ha1.
    simpl in H2; omega.
    exists m; split.
    right; auto.
    intros b [ Hb | Hb ]; auto.
    subst b; apply le_trans with (1 := H4 _ Ha1); auto; omega.
    
    exists a; split.
    left; auto.
    intros b [ Hb | Hb ]; auto.
    subst; auto.
    specialize (Ha _ Hb); omega.
  Qed.
  
  Let minimizer_list ll : ll <> nil -> { a | In a ll /\ forall b, In b ll -> f a <= f b }.
  Proof.
    intros Hll.
    apply minimizer_rec with (n := S (length ll)).
    destruct ll.
    contradict Hll; auto.
    simpl; omega.
  Qed.
  
  Fact minimizer_finite (P : X -> Prop) : finite P
                                       -> (exists a, P a)
                                       -> exists a, P a /\ forall b, P b -> f a <= f b.
  Proof.
    intros (ll & Hll) (a & Ha).
    destruct (@minimizer_list ll) as (m & H1 & H2).
    apply Hll in Ha.
    destruct ll.
    destruct Ha.
    discriminate.
    exists m; split.
    apply Hll; auto.
    intros b Hb; apply H2, Hll; auto.
  Qed.
  
  Fact minimizer_finite_t (P : X -> Prop) : finite_t P
                                         -> (exists a, P a) 
                                         -> { a | P a /\ forall b, P b -> f a <= f b }.
  Proof.
    intros (ll & Hll) Ha.
    destruct (@minimizer_list ll) as (m & H1 & H2).
    destruct Ha as (a & Ha).
    apply Hll in Ha.
    destruct ll.
    destruct Ha.
    discriminate.
    exists m; split.
    apply Hll; auto.
    intros b Hb; apply H2, Hll; auto.
  Qed.

End minimizer.
