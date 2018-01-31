(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Relations Permutation.

Require Import rel_utils.

Require Import list_aux.
Require Import list_perm.
Require Import list_prod.
Require Import list_forall.

(*
Require Import finite.
*)

Set Implicit Arguments.

Section list_fan.

  Variable (X : Type).

  Fixpoint list_fan (lw : list (list X)) := 
    match lw with
      | nil => nil::nil
      | w::lw => list_prod (@cons _) w (list_fan lw)
    end.

  (* list_fan [l1;...;lk] contains all the list of the form [x1;...;xk] 
     with x1 in l1, x2 in l2 ... xk in lk 
  *)

  Fact list_fan_eq_nil lw : list_fan lw = nil -> exists w, In w lw /\ w = nil.
  Proof.
    induction lw as [ | w lw IH ]; simpl.
    discriminate 1.
    intros H.
    apply list_prod_nil in H.
    destruct H as [ H | H ].
    exists w; auto.
    destruct (IH H) as (w' & ? & ?).
    exists w'; auto.
  Qed.

  Fact list_fan_spec lw : forall w, In w (list_fan lw) <-> Forall2 (@In _) w lw.
  Proof.
    induction lw as [ | w lw ]; intros x; simpl.
    destruct x as [ | ].
    split; auto.
    split.
    intros [ H | [] ]; discriminate H.
    intros H; inversion H.
    rewrite list_prod_spec.
    split.
    intros (a & u & H1 & H2 & ?); subst.
    constructor; auto.
    revert H2; apply IHlw.
    intros H; destruct x as [ | a x ]; inversion_clear H.
    exists a, x; repeat split; auto.
    apply IHlw; auto.
  Qed.

  Fact list_fan_cons_In w lw l : In l (list_fan (w::lw)) <-> exists x l', In x w /\ In l' (list_fan lw) /\ l = x::l'.
  Proof.
    simpl.
    rewrite list_prod_spec.
    split; auto.
  Qed.
 
  Fact list_fan_app w1 w2 lw : list_fan ((w1++w2)::lw) ~p list_fan (w1::lw) ++ list_fan (w2::lw).
  Proof.
    apply list_prod_app_left.
  Qed.

  Fact list_fan_cons a w lw : list_fan ((a::w)::lw) ~p list_fan ((a::nil)::lw) ++ list_fan (w::lw).
  Proof.
    apply (list_fan_app (a::nil)).
  Qed.

  Fact list_fan_nil lw rw : list_fan (lw++nil::rw) = nil.
  Proof.
    induction lw as [ | w lw IH ]; simpl.
    apply list_prod_nil_left.    
    rewrite IH, list_prod_nil_right; auto.
  Qed.

  Fact list_fan_sg_left lw a : list_fan ((a::nil)::lw) = map (cons a) (list_fan lw).
  Proof.
    simpl list_fan at 1.
    unfold list_prod.
    generalize (list_fan lw); clear lw.
    induction l; simpl; f_equal; auto.
  Qed.

  Fact list_fan_sg_right lw a : list_fan (lw++(a::nil)::nil) = map (fun w => w++a::nil) (list_fan lw).
  Proof.
    induction lw as [ | w lw IH ]; simpl; auto.
    rewrite IH.
    unfold list_prod.
    rewrite map_flat_map, flat_map_map.
    apply flat_map_ext.
    intros x _.
    rewrite map_map.
    apply map_ext.
    intros ?; auto.
  Qed.

  Fact list_fan_middle_app lw w1 w2 rw : list_fan (lw++(w1++w2)::rw) ~p list_fan (lw++w1::rw) ++ list_fan (lw++w2::rw).
  Proof.
    induction lw as [ | w lw IHlw ].
    simpl app at 1 3.
    rewrite list_fan_app; auto; simpl.
    apply list_prod_perm with (f := @cons X) (1 := Permutation_refl w) in IHlw.
    apply Permutation_trans with (1 := IHlw),
          Permutation_trans with (1 := list_prod_app_right _ _ _ _); auto.
  Qed.
  
  Fact list_fan_middle_cons lw a w rw : list_fan (lw++(a::w)::rw) ~p list_fan (lw++(a::nil)::rw) ++ list_fan (lw++w::rw).
  Proof.
    apply list_fan_middle_app with (w1 := a::nil).
  Qed.

  Fact list_fan_mono lw mw : Forall2 (@incl _) lw mw -> incl (list_fan lw) (list_fan mw).
  Proof.
    induction 1 as [ | l m lw mw H1 H2 IH2 ].
    apply incl_refl.
    intros x Hx.
    rewrite list_fan_spec in Hx.
    rewrite list_fan_spec.
    destruct x as [ | a x ].
    inversion Hx.
    apply Forall2_cons_inv in Hx.
    destruct Hx as [ Ha Hx ].
    constructor 2.
    revert Ha; auto.
    revert Hx; do 2 rewrite <- list_fan_spec; auto.
  Qed.

  Let list_fan_rev_alt x lw : In x (list_fan lw) -> In (rev x)  (list_fan (rev lw)).
  Proof.
    do 2 rewrite list_fan_spec.
    induction 1; simpl.
    constructor.
    apply Forall2_app; auto.
  Qed.

  Fact list_fan_rev x lw : In (rev x)  (list_fan (rev lw)) <-> In x (list_fan lw).
  Proof.
    split; auto.
    rewrite <- (rev_involutive lw) at 2.
    rewrite <- (rev_involutive x) at 2.
    auto.
  Qed.

  Fact list_fan_length lw w : In w (list_fan lw) -> length w = length lw.
  Proof.
    rewrite list_fan_spec.
    apply Forall2_length.
  Qed.    

  Section list_fan_Forall.

    Variable P : list X -> Prop.
  
    Fact list_fan_Forall_cons a lw : Forall (fun l => P (a::l)) (list_fan lw) 
                                  -> Forall P (list_fan ((a::nil)::lw)).
    Proof.
      do 2 rewrite Forall_forall.
      intros H x Hx.
      rewrite list_fan_sg_left, in_map_iff in Hx.
      destruct Hx as (y & H1 & Hx); subst; auto.
    Qed.
    
    Fact list_fan_Forall w lw : Forall (fun a => Forall (fun l => P (a::l)) (list_fan lw)) w 
                             -> Forall P (list_fan (w::lw)).
    Proof.
      induction w as [ | a w IH ].
      generalize (list_fan_nil nil lw); simpl; intros H; rewrite H; constructor.
      intros H; rewrite (Forall_perm _ (list_fan_cons _ _ _)), Forall_app; split.
      apply list_fan_Forall_cons.
      apply Forall_inv in H; auto.
      apply IH.
      inversion_clear H; auto.
    Qed.

  End list_fan_Forall.

  Fact list_fan_Forall_Forall P ll : Forall (Forall P) ll -> Forall (Forall P) (list_fan ll).
  Proof.
    induction 1 as [ | x ll Hx Hll IHll ].
    constructor; constructor.
    apply list_fan_Forall.
    revert Hx; do 2 rewrite Forall_forall; intros Hx u Hu.
    revert IHll; apply Forall_impl; constructor; auto.
  Qed.

End list_fan.

Fact list_fan_map_map U V (f : U -> V) (ll : list (list U)) : list_fan (map (map f) ll) = map (map f) (list_fan ll).
Proof.
  induction ll as [ | ? ? IH ]; simpl; f_equal.
  rewrite IH.
  rewrite <- list_prod_map, map_list_prod.
  auto.
Qed.
  


