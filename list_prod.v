(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.
Require Import Permutation.
Require Import Arith.

Require Import list_aux.
Require Import list_perm.

Set Implicit Arguments.

(* list product *)

Section list_prod.

  Variables (A B C : Type) (f : A -> B -> C).

  (* list_prod [a1;...;an] [b1;...;bm] = [f a1 b1; f a2 b1;...;f an b1;f a1 b2;...;f an b2;...;f a1 bm;...;f an bm] *)

  Definition list_prod ll mm := flat_map (fun y => map (fun x => f x y) ll) mm.

  Fact list_prod_spec ll mm : forall c, In c (list_prod ll mm) <-> exists a b, In a ll /\ In b mm /\ c = f a b.
  Proof.
    intros c; split; unfold list_prod;
    rewrite in_flat_map.
    intros (b & H1 & H2).
    rewrite in_map_iff in H2.
    destruct H2 as (a & H2 & H3).
    exists a, b; auto.
    intros (a & b & H1 & H2 & H3).
    exists b; split; auto.
    rewrite in_map_iff.
    exists a; auto.
  Qed.

  Fact list_prod_length ll mm : length (list_prod ll mm) = length ll * length mm.
  Proof.
    rewrite mult_comm; induction mm; simpl; auto.
    rewrite app_length, map_length; f_equal; auto.
  Qed.

  Fact list_prod_nil ll mm : list_prod ll mm = nil -> ll = nil \/ mm = nil.
  Proof.
    intros H.
    apply f_equal with (f := @length _) in H.
    rewrite list_prod_length in H; simpl in H.
    destruct ll; auto.
    destruct mm; auto.
    simpl in H; discriminate H.
  Qed.

  Fact list_prod_nil_left mm : list_prod nil mm = nil.
  Proof.
    induction mm; simpl; f_equal; auto.
  Qed.

  Fact list_prod_nil_right ll : list_prod ll nil = nil.
  Proof.
    reflexivity.
  Qed.

  Fact list_prod_sg_right ll x : list_prod ll (x::nil) = map (fun a => f a x) ll.
  Proof.
    symmetry; apply app_nil_end.
  Qed.

  Fact list_prod_app_left ll mm nn : list_prod (ll++mm) nn ~p list_prod ll nn ++ list_prod mm nn.
  Proof.
    induction nn as [ | x nn IH ]; simpl.
    apply perm_nil.
    rewrite map_app, app_ass, app_ass.
    apply Permutation_app; auto.
    apply Permutation_trans with (1 := Permutation_app_head _ IH).
    do 2 rewrite <- app_ass.
    apply Permutation_app; auto.
    apply Permutation_app_comm.
  Qed.

  Fact list_prod_app_right ll mm nn : list_prod ll (mm++nn) ~p list_prod ll mm ++ list_prod ll nn.
  Proof.
    unfold list_prod; rewrite flat_map_app; apply Permutation_refl.
  Qed.

  Fact list_prod_cons_left a ll mm : list_prod (a::ll) mm ~p list_prod (a::nil) mm ++ list_prod ll mm.
  Proof.
    apply (list_prod_app_left (a::nil)).
  Qed.

  Fact list_prod_cons_right ll a mm : list_prod ll (a::mm) ~p list_prod ll (a::nil) ++ list_prod ll mm.
  Proof.
    apply (list_prod_app_right _ (a::nil)).
  Qed.

  Let list_prod_perm_left ll mm nn : ll ~p mm -> list_prod ll nn ~p list_prod mm nn.
  Proof.
    intros; apply flat_map_perm.
    intros; apply Permutation_map; assumption.
  Qed.

  Let list_prod_perm_right nn ll mm : ll ~p mm -> list_prod nn ll ~p list_prod nn mm.
  Proof.
    induction 1 as [ | | | l1 l2 l3 _ IH1 ]; simpl.
    apply perm_nil.
    apply Permutation_app; auto.
    do 2 rewrite app_assoc.
    apply Permutation_app.
    apply Permutation_app_comm.
    apply Permutation_refl.
    apply Permutation_trans with (1 := IH1); auto.
  Qed.

  (* list_prod is congruent under permutations *)

  Fact list_prod_perm l1 l2 m1 m2 : l1 ~p l2 -> m1 ~p m2 -> list_prod l1 m1 ~p list_prod l2 m2.
  Proof.
    intros H1 H2.
    apply Permutation_trans with (1 := list_prod_perm_left _ H1).
    apply list_prod_perm_right; auto.
  Qed.

End list_prod.

Fact list_prod_map A A' B B' C (p : A' -> B' -> C) (f : A -> A') (g : B -> B') l m :
     list_prod (fun a b => p (f a) (g b)) l m = list_prod p (map f l) (map g m).
Proof.
  induction m; simpl; f_equal; auto.
  rewrite map_map; auto.
Qed.

Fact map_list_prod A B C C' (p : A -> B -> C) (f : C -> C') l m : map f (list_prod p l m) = list_prod (fun a b => f (p a b)) l m.
Proof.
  induction m; simpl; f_equal; auto.
  rewrite map_app.
  f_equal; auto.
  rewrite map_map; auto.
Qed.
