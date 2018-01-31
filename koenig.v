(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Require Import tacs rel_utils list_utils almost_full.

Set Implicit Arguments.

Section Constructive_Koenigs_lemma.

  Variable (X : Type) (R : X -> X -> Prop) (HR : af_t R) (f : nat -> list X).

  (** This is an infinitist version of the Constructive FAN theorem 
  
      From f, one can compute a (uniform) bound n such that 
      if c : nat -> X is a choice sequence for f (ie forall i, c(i) belongs to f(i)) 
      then the sequence g(0),...,g(n-1) is good 
    *)

  Theorem Constructive_FAN_theorem : 
      { n | forall g, (forall k, In (g k) (f k)) -> exists i j, i < j < n /\ R (g i) (g j) }. 
  Proof.
    apply af_t_bar_t in HR.
    generalize (@fan_t_on_list _ _ (@good_mono _ R) HR); intros FAN.
    destruct (bar_t_inv FAN f) as (n & Hn).
    exists n.
    
    intros g Hg.
    apply good_pfx_rev_eq.
    rewrite Forall_forall in Hn.
    apply Hn, list_fan_spec.
    do 2 rewrite pfx_pfx_rev_eq.
    rewrite <- Forall2_rev.
    apply Forall2_pfx.
    intros; auto.
  Qed.
  
  (** This is a finitist version of the Constructive FAN theorem 
  
      The set of choice sequences [x(m-1);...;x1;x0] st x(i) in f(i) eventually
      becomes uniformly good after some natural number n 
    *) 
  
  Theorem Constructive_Koenigs_lemma : { n | forall m, n <= m -> Forall (good R) (list_fan (pfx_rev f m)) }.
  Proof.
    apply af_t_bar_t in HR.
    generalize (@fan_t_on_list _ _ (@good_mono _ R) HR); intros FAN.
    destruct (bar_t_inv FAN f) as (n & Hn).
    exists n.
    
    rewrite Forall_forall in Hn.
    intros m Hm.
    apply Forall_forall.
    induction Hm as [ | m Hnm IH ]; auto.
    
    simpl pfx_rev.
    intros u Hu.
    rewrite list_fan_cons_In in Hu.
    destruct Hu as (c & v & H1 & H2 & H3).
    apply IH in H2.
    subst u; constructor 2; auto.
  Qed.
  
End Constructive_Koenigs_lemma.
