(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Permutation.

Require Import list_in.

Set Implicit Arguments.

Fact In_map_nat_find X (f : X -> nat) x l : In x (map f l) -> { u | x = f u /\ In u l }.
Proof.
  induction l as [ | y l IH ].
  intros [].
  destruct (eq_nat_dec x (f y)) as [ | C ].
  exists y; split; auto; left; auto.
  intros H.
  destruct IH as (u & H1 & H2).
  destruct H; auto; contradict C; auto.
  exists u; split; auto; right; auto.
Qed.

Notation lsum := (fold_right plus 0).
 
Fact lsum_prop x ll : In x ll -> x <= lsum ll.
Proof.
  induction ll as [ | y ll IH ]; simpl.
  intros [].
  intros [ | H ]; subst.
  omega.
  specialize (IH H); omega.
Qed.

Fact lsum_perm l m : Permutation l m -> lsum l = lsum m.
Proof.
  induction 1; simpl; auto; omega.
Qed.

Fact lsum_app l r : lsum (l++r) = lsum l + lsum r.
Proof.
  induction l; simpl; auto; omega.
Qed.

Section lmax.

  Definition lmax := fold_right max 0.
  
  Fact lmax_fix x l : lmax (x::l) = max x (lmax l).
  Proof. auto. Qed.

  Fact Forall2_lmax ll mm : Forall2 le ll mm -> lmax ll <= lmax mm.
  Proof.
    induction 1; auto.
    do 2 rewrite lmax_fix.
    apply max_lub.
    apply le_trans with (2 := le_max_l _ _); auto.
    apply le_trans with (2 := le_max_r _ _); auto.
  Qed.

  Fact lmax_In x ll : In x ll -> x <= lmax ll.
  Proof.
    induction ll as [ | y ll IH ].
    simpl; omega.
    rewrite lmax_fix.
    intros [ H | H ]; subst.
    apply le_max_l.
    apply le_trans with (1 := IH H), le_max_r.
  Qed.
  
  Fact lmax_inv l : { l = nil } + { In (lmax l) l }.
  Proof.
    induction l as [ | x l IHl ].
    left; auto.
    right.
    simpl.
    destruct IHl.
    subst; left; simpl.
    rewrite max_0_r; auto.
    destruct (le_lt_dec x (lmax l)).
    right; rewrite max_r; auto.
    left; rewrite max_l; auto.
    apply lt_le_weak; assumption.
  Qed.

  Fact lmax_inv' l : 0 < lmax l -> { x | In x l /\ x = lmax l }.
  Proof.
    intros H0; destruct (lmax_inv l) as [ H | H ].
    exfalso; subst; simpl in H0; omega.
    exists (lmax l); auto.
  Qed.
  
  Fact lmax_map_inv X (f : X -> nat) l : l <> nil -> { x | In x l /\ f x = lmax (map f l) }.
  Proof.
    intros H0.
    destruct (lmax_inv (map f l)) as [ H | H ].
    contradict H0.
    destruct l; auto; discriminate H.
    apply In_map_nat_find in H.
    destruct H as (u & ? & ?); exists u; auto.
  Qed.

  Fact lmax_inv_t l : 0 < lmax l -> { x : _ & { _ : In_t x l | x = lmax l } }.
  Proof.
    induction l as [ | x l IH ].
    simpl; omega.
    intros H0.
    destruct (eq_nat_dec (lmax l) 0) as [ H1 | H1 ].

    rewrite lmax_fix, H1, max_0_r in H0.
    exists x; split; simpl; auto.
    rewrite H1, max_0_r; auto.
    
    destruct IH as (z & H2 & H3).
    omega.
    destruct (le_lt_dec x z) as [ H4 | H4 ].
    exists z; split; simpl; auto.
    rewrite max_r; omega.
    exists x; split; simpl; auto.
    rewrite max_l; omega.
  Qed.

  Fact lmax_0_inv l : lmax l = 0 -> (In_t 0 l + { l = nil })%type.
  Proof.
    destruct l as [ | x l ].
    right; auto.
    rewrite lmax_fix.
    intros H.
    destruct (max_dec x (lmax l)) as [ E | E ];
    rewrite H in E.
    subst x; left; left; auto.
    rewrite <- E, max_0_r in H.
    subst x; left; left; auto.
  Qed.
  
  Fact lmax_app l m : lmax (l++m) = max (lmax l) (lmax m).
  Proof.
    induction l as [ | x l IH ]; simpl; auto.
    rewrite IH; apply max_assoc.
  Qed.
  
  Variable (f : nat -> nat) (Hf : forall m n, m <= n -> f m <= f n).
  
  Fact max_monotone n m : f (max n m) = max (f n) (f m).
  Proof.
    symmetry; destruct (max_dec n m) as [ H | H ]; rewrite H.
    apply max_l, Hf; rewrite <- H; apply le_max_r.
    apply max_r, Hf; rewrite <- H; apply le_max_l.
  Qed.
  
  Fact lmax_mono l : l <> nil -> lmax (map f l) = f (lmax l).
  Proof.
    induction l as [ | x [ | y l ] IH ]; simpl.
    intros H; contradict H; auto.
    do 2 rewrite max_0_r; auto.
    intros _; rewrite max_monotone; f_equal.
    apply IH; discriminate.
  Qed.
  
End lmax.

Fixpoint list_n n := match n with 0 => nil | S n => n::list_n n end.
  
Fact list_n_prop n x : x < n <-> In x (list_n n).
Proof.
  revert x; induction n as [ | ? IH ]; intros ?.
  split. 
  omega.
  intros [].
  simpl; rewrite <- IH.
  split; omega.
Qed.

Fact list_n_length x : length (list_n x) = x.
Proof. induction x; simpl; f_equal; auto. Qed.

Fact largest_nat_prefix n (P : nat -> Prop) : (forall i, i <= n -> { P i } + { ~ P i })
                                           -> P 0
                                           -> { i | i <= n 
                                                 /\ P i 
                                                 /\ (P (S i) -> n <= i) 
                                                 /\ forall j, j <= i -> P j }.
Proof.
  revert P.
  induction n as [ | n IHn ]; intros P HP H.

  exists 0.
  repeat split; auto.
  intros j Hj.
  cutrewrite (j = 0); auto; omega.
  
  destruct (HP 1) as [ H1 | H1 ]; try omega.

  destruct (IHn (fun x => P (S x))) as (i & H3 & H4 & H5 & H6); auto.
  intros; apply  HP; omega.
  exists (S i); repeat split; auto. 
  omega.
  intros H'; apply H5 in H'; omega.
  intros [ | j ]; auto.
  intros H7; apply H6; omega.
  
  exists 0; repeat split; auto.
  omega.
  tauto.
  intros j Hj; cutrewrite (j=0); auto; omega.
Qed.

