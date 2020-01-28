(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import tacs list_utils good_base.

Set Implicit Arguments.

Section pigeon.

  Variable (X : Type).

  Implicit Types (l m : list X).
  
  Definition list_has_dup := good (@eq X).
  
  Fact list_hd_cons_inv x l : list_has_dup (x::l) -> In x l \/ list_has_dup l.
  Proof.
    intros H.
    apply good_cons_inv in H.
    destruct H as [ (y & ? & []) | H ]; auto.
  Qed.
  
  Fact in_list_hd0 x l : In x l -> list_has_dup (x::l).
  Proof. constructor 1 with x; auto. Qed.
  
  Fact in_list_hd1 x l : list_has_dup l -> list_has_dup (x::l).
  Proof. constructor 2; auto. Qed.
  
  Fact list_has_dup_app_left l m : list_has_dup m -> list_has_dup (l++m).
  Proof. apply good_app_left. Qed.
  
  Fact list_has_dup_app_right l m : list_has_dup l -> list_has_dup (l++m).
  Proof. apply good_app_right. Qed.
  
  Fact list_hd_eq_perm l m : l ~p m -> list_has_dup l -> list_has_dup m.
  Proof.
    induction 1 as [ | x l m H1 IH1 | x y l | ]; auto.
    intros H.
    apply list_hd_cons_inv in H.
    destruct H as [ H | H ].
    apply Permutation_in with (1 := H1) in H.
    
    apply in_list_hd0; auto.
    apply in_list_hd1; auto.
    intros H.
    apply list_hd_cons_inv in H.
    destruct H as [ [ H | H ] | H ]; subst.
    apply in_list_hd0; left; auto.
    apply in_list_hd1, in_list_hd0; auto.
    apply list_hd_cons_inv in H.
    destruct H as [ H | H ].
    apply in_list_hd0; right; auto.
    do 2 apply in_list_hd1; auto.
  Qed.
  
  Fact incl_right_cons_choose x l m : incl m (x::l) -> In x m \/ incl m l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as ( m1 & m2 & H1 & H2 & H3 ); simpl in H1.
    destruct m1 as [ | y m1 ].
    right.
    intros u H; apply H3; revert H.
    apply Permutation_in; auto.
    left.
    apply Permutation_in with (1 := Permutation_sym H1).
    rewrite (H2 y); left; auto.
  Qed.
  
  Fact repeat_choice_two (x : X) m : (forall a, In a m -> a = x) -> (exists m', m = x::x::m') \/ m = nil \/ m = x::nil.
  Proof.
    intros H.
    destruct m as [ | a [ | b m ] ].
    right; left; auto.
    right; right; rewrite (H a); auto; left; auto.
    left; rewrite (H a), (H b).
    exists m; auto.
    right; left; auto.
    left; auto.
  Qed.

  Fact incl_right_cons_incl_or_lhd_or_perm m x l : incl m (x::l) -> incl m l 
                                                                 \/ list_has_dup m 
                                                                 \/ exists m', m ~p x::m' /\ incl m' l.
  Proof.
    intros H.
    apply incl_cons_rinv in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    destruct (repeat_choice_two _ H2) as [ (m3 & H4) | [ H4 | H4 ] ]; 
      subst m1; simpl in H1; clear H2.
    
    apply Permutation_sym in H1.
    right; left.
    apply list_hd_eq_perm with (1 := H1).
    apply in_list_hd0; left; auto.
    
    left.
    intros ? H; apply H3; revert H.
    apply Permutation_in; auto.
    
    right; right.
    exists m2; auto.
  Qed.
 
  Fact length_le_and_incl_implies_dup_or_perm l :  
               forall m, length l <= length m 
                      -> incl m l 
                      -> list_has_dup m \/ m ~p l.
  Proof.
  
    induction l as [ [ | x l ] IHl ] using list_length_rect.
      
    intros [ | x ] _ H.
    right; auto.
    specialize (H x); simpl in H; contradict H; left; auto.
    
    intros [ | y m ] H1 H2.
    apply le_Sn_0 in H1; destruct H1.
    simpl in H1; apply le_S_n in H1.
    apply incl_cons_linv in H2. 
    destruct H2 as [ [ H3 | H3 ] H4 ].
    subst y.
    apply incl_right_cons_choose in H4.
    destruct H4 as [ H4 | H4 ].
    left; apply in_list_hd0; auto.
    destruct IHl with (3 := H4); auto.
    left; apply in_list_hd1; auto.
    apply incl_right_cons_incl_or_lhd_or_perm in H4.
    destruct H4 as [ H4 | [ H4 | (m' & H4 & H5) ] ].
    destruct IHl with (3 := H4) as [ H5 | H5 ]; auto.
    left; apply in_list_hd1; auto.
    left; apply in_list_hd0; revert H3.
    apply Permutation_in, Permutation_sym; auto.
    left; apply in_list_hd1; auto.
    apply Permutation_sym in H4.
    apply perm_in_head in H3.
    destruct H3 as (l' & Hl').
    assert (incl m' (y::l')) as H6.
      intros ? ?; apply Permutation_in with (1 := Hl'), H5; auto.
    clear H5.
    apply incl_right_cons_choose in H6.
    destruct H6 as [ H6 | H6 ].
    left; apply in_list_hd0, Permutation_in with (1 := H4); right; auto.
    apply IHl in H6.
    destruct H6 as [ H6 | H6 ].
    left; apply list_hd_eq_perm in H4; apply in_list_hd1; auto.
    right.
    apply Permutation_trans with (y::x::m').
    apply perm_skip, Permutation_sym; auto.
    apply Permutation_trans with (1 := perm_swap _ _ _),
          perm_skip, Permutation_sym,
          Permutation_trans with (1 := Hl'),
          perm_skip, Permutation_sym; auto.
    apply Permutation_length in Hl'; simpl in Hl' |- *; omega.
    apply Permutation_length in Hl'.
    apply Permutation_length in H4.
    simpl in Hl', H4; omega.
  Qed.
  
  Theorem finite_pigeon_hole l m : 
       length l < length m 
    -> incl m l 
    -> exists x aa bb cc, m = aa++x::bb++x::cc.
  Proof.
    intros H1 H2.
    assert (list_has_dup m) as Hm.
 
    destruct (@list_prefix _ m (length l)) 
      as (m1 & m2 & H3 & H4); try omega; subst m.
    symmetry in H4.
    destruct (@length_le_and_incl_implies_dup_or_perm l m1) as [ H5 | H5 ].
    rewrite H4; auto.
    intros ? ?; apply H2, in_or_app; auto. 
    apply list_has_dup_app_right; auto.
    destruct m2 as [ | x m2 ].
    rewrite <- app_nil_end in H1; omega.
    assert (In x m1) as Hm1.
      apply Permutation_in with (1 := Permutation_sym H5).
      apply H2, in_or_app; right; simpl; auto.
    apply in_split in Hm1.
    destruct Hm1 as (l1 & l2 & ?); subst.
    rewrite app_ass; simpl.
    apply list_has_dup_app_left, in_list_hd0, in_or_app; simpl; auto.
    
    apply good_inv in Hm.
    destruct Hm as (aa & x & bb & y & cc & ? & ?); subst m y.
    exists x, aa, bb, cc; auto.
  Qed.

End pigeon.

Section pigeon_rel.

  Variable (X Y : Type) (R : X -> Y -> Prop).
  
  Implicit Types (lx : list X) (ly : list Y).
  
  Fact list_rel_choice lx ly : 
       (forall x, In x lx -> exists y, R x y /\ In y ly)
     -> exists ly', Forall2 R lx ly' /\ incl ly' ly.
  Proof.
    intros HR; apply sig_invert in HR.
    destruct HR as (mm & Hmm); exists mm; split.
    revert Hmm; apply Forall2_impl; tauto.
    apply Forall2_conj, proj2, Forall2_right_Forall, proj1 in Hmm.
    red; apply Forall_forall; auto.
  Qed.
  
  Theorem pigeon_hole_rel lx ly :
            (forall x, In x lx -> exists y, R x y /\ In y ly)
         -> length ly < length lx 
         -> exists a x1 b x2 c y, lx = a++x1::b++x2::c /\ In y ly /\ R x1 y /\ R x2 y.
  Proof.
    intros HR.
    destruct (list_rel_choice _ _ HR) as (ly' & H1 & H2); intros H3.
    destruct finite_pigeon_hole with (2 := H2) as (y & a & b & c & H4).
    apply Forall2_length in H1; rewrite <- H1; auto.
    subst ly'.
    apply Forall2_app_inv_r in H1.
    destruct H1 as (u & v1 & H1 & H4 & H5); subst lx.
    apply Forall2_cons_inv_r in H4.
    destruct H4 as (x1 & v2 & H4 & H5 & H6); subst v1.
    apply Forall2_app_inv_r in H6.
    destruct H6 as (v & w1 & H7 & H5 & H6); subst v2.
    apply Forall2_cons_inv_r in H5.
    destruct H5 as (x2 & w & H5 & H6 & H8); subst w1.
    exists u, x1, v, x2, w, y; repeat split; auto.
    apply H2, in_or_app; right; left; auto.
  Qed.

End pigeon_rel.
