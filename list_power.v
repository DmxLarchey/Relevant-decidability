(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation.

Require Import list_perm list_in.
Require Import sublist.

Set Implicit Arguments.

Section list_power.

  Variable (X : Type).

  Implicit Type ll : list X.  

  Fixpoint list_power ll :=
    match ll with
      | nil  => nil::nil
      | x::ll => map (cons x) (list_power ll) ++ list_power ll
    end.
    
  Fact list_power_spec ll m : In m (list_power ll) <-> m <sl ll.
  Proof.
    revert m; induction ll as [ | x l IHl ]; intros m; simpl; split.
    intros [ ? | [] ]; subst; apply sl_refl.
    intros H; apply sublist_nil_inv in H; subst; auto.

    intros H.
    apply in_app_or in H.
    rewrite in_map_iff in H.
    destruct H as [ (p & H1 & H2)  | H2 ];
       apply IHl in H2.
    subst; constructor 2; auto.
    constructor 3; auto.
    
    intros H.
    apply sublist_cons_inv_rt in H.
    destruct H as [ H2 | (p & H1 & H2) ];
      apply IHl in H2.
    apply in_or_app; right; auto.
    subst; apply in_or_app; left.
    apply in_map_iff; exists p; auto.
  Qed.
  
  Fact list_power_equiv ll l : incl l ll <-> exists m, In m (list_power ll) /\ eql l m.
  Proof.
    split.
    
    revert l; induction ll as [ | x ll ].
    
    intros [ | y l ] Hl.
    exists nil; simpl; repeat split; auto.
    exfalso; apply (Hl y); left; auto.
    
    intros l Hl.
    apply incl_cons_rinv in Hl.
    destruct Hl as (m1 & m2 & H1 & H2 & H3).
    apply IHll in H3.
    destruct H3 as (m3 & H3 & H4).
    
    destruct m1 as [ | a m1 ].
    
    exists m3; split.
    simpl; apply in_or_app; right; auto.
    simpl in H1.
    split; intros y Hy.
    apply H4, Permutation_in with (1 := H1); trivial.
    apply Permutation_in with (1 := Permutation_sym H1), H4; trivial.
    
    rewrite (H2 a) in H1.
    2: left; auto.
    exists (x::m3); split.
    simpl; apply in_or_app; left.
    apply in_map_iff.
    exists m3; auto.
    split.
    intros y Hy.
    apply Permutation_in with (1 := H1), in_app_or in Hy.
    destruct Hy as [ [ Hy | Hy ] | Hy ].
    subst; left; auto.
    left; symmetry; apply H2; right; auto.
    right; apply H4; auto.
    intros y [ Hy | Hy ].
    subst; apply Permutation_in with (1 := Permutation_sym H1).
    left; auto.
    apply Permutation_in with (1 := Permutation_sym H1).
    right; apply in_or_app; right; apply H4; auto.
    
    intros (m & H1 & H2 & H3).
    apply list_power_spec in H1.
    intros x Hx; apply H2 in Hx; revert Hx.
    apply sl_In; trivial.
  Qed.

End list_power.

    
    
