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

Require Import tree proof.

Require Import formula relevant_contract sequent_rules.
Require Import mini_HI mini_LI1 mini_LI2 sem_cut_adm.

Set Implicit Arguments.

Theorem LI1_cf_LI1 : LI1_cf_proof inc1 LI1_proof.
Proof.
  induction 1 as [ | | ? ? ? ? ? ? H | ? ? ? ? H | ? ? ? ? H ] using LI1_cf_proof_rect.
  apply LI1_rule_id.
  apply LI1_rule_r; trivial.
  apply LI1_rule_l with (1 := H); trivial.
  apply LI1_rule_cntr with (1 := H); trivial.
  apply LI1_rule_weak with (1 := H); trivial.
Qed.

Local Hint Resolve LI1_rule_id perm_skip perm_swap.

Local Notation "HI--" := HI_proof.
Local Notation "x 'LI1-' y" := (LI1_proof (x,y)) (at level 70, no associativity).  
Local Notation "x 'LI1cf-' y" := (LI1_cf_proof (x,y)) (at level 70, no associativity).
Local Notation "x 'LI2-' y" := (LI2_proof (x,y)) (at level 70, no associativity).

Theorem HI_LI1 A : HI-- A -> nil LI1- A.
Proof.
  induction 1 as [ A | A B C | A B _ IH1 _ IH2 ].
    
  do 2 apply LI1_rule_r.
  apply LI1_rule_weak with (A::nil) B; auto.
    
  do 3 apply LI1_rule_r.
  apply LI1_rule_cntr with (A %> B :: A %> B %> C :: nil) A; auto.
  apply LI1_rule_l with (A :: nil) (A :: A %> B %> C :: nil) A B; simpl; auto.
  apply perm_trans with (2 := perm_swap _ _ _); auto.
  apply LI1_rule_l with (A :: nil) (B :: nil) A (B %> C); simpl; auto.
  apply perm_trans with (1 := perm_swap _ _ _); auto.
  apply perm_trans with (2 := perm_swap _ _ _); auto.
  apply LI1_rule_l with (B :: nil) (nil) B C; simpl; auto.
    
  apply LI1_rule_cut with (2 := IH2) (de := nil); auto.
  apply LI1_rule_cut with (2 := IH1) (de := A :: nil); auto.
  apply LI1_rule_l with (A :: nil) nil A B; simpl; auto.
Qed.

Section LI1_HI.

  Let LI1_HR_rec : forall s, LI1_proof s -> HI_proof (fst s %%> snd s).
  Proof.
    induction 1 as [ 
                   | 
                   | ga de th A B C H1 H3 H4 
                   | de th A B H1 H3 
                   | de th A B H1 H3 
                   | ga de th A B H1 H2 H3 ] using LI1_proof_rect; simpl in * |- *.
                   
    (* rule_id *)

    apply HI_I.
    
    (* rule_r *)
    
    auto.
    
    (* rule_l *)
 
    apply Permutation_sym in H1.
    apply HI_proof_perm with (1 := H1).
    simpl; rewrite list_Form_to_Form_app.
    revert H4; apply HI_list_Form_to_Form_HI_proof.
    assert (B %> C :: A %> B :: ga ~p A %> B :: ga ++ B %> C :: nil) as H4.
      apply perm_trans with (1 := perm_swap _ _ _), perm_skip,
            Permutation_app_comm with (l := _ :: nil).
    apply HI_proof_perm with (a := C) in H4.
    simpl in H4; rewrite list_Form_to_Form_app in H4; auto.
    simpl; revert H3; apply HI_list_Form_to_Form_HI_proof.
    clear H1 H4.
    generalize (HI_B A B C).
    apply HI_proof_perm with (l := _ :: _ :: _ :: nil) 
                             (m := _ :: _ :: _ :: nil).
    apply perm_trans with (1 := perm_swap _ _ _),
          perm_trans with (2 := perm_swap _ _ _); auto.
          
    (* rule_cntr *)
          
    apply HI_proof_perm with (1 := Permutation_sym H1).
    revert H3; apply HI_proof_contract.
    
    (* rule_weak *)
          
    apply HI_proof_perm with (1 := Permutation_sym H1).
    revert H3; apply HI_proof_weak.
    
    (* rule_cut *)
    
    apply Permutation_sym in H1.
    apply HI_proof_perm with (1 := H1).
    simpl; rewrite list_Form_to_Form_app.
    revert H3; apply HI_list_Form_to_Form_HI_proof.
    assert (A %> B :: ga ~p ga ++ A %> B :: nil) as E.
      apply Permutation_sym, Permutation_app_comm.
    apply HI_proof_perm with (a := B) in E.
    simpl in E; rewrite list_Form_to_Form_app in E; auto.
    simpl; revert H2; apply HI_list_Form_to_Form_HI_proof.
    apply in_HI_MP with (1 := HI_C _ _ _), HI_I.
  Qed.
  
  Theorem LI1_HI A : nil LI1- A -> HI-- A.
  Proof. apply LI1_HR_rec. Qed.

  Theorem LI1_cf_HI A : nil LI1cf- A -> HI-- A.
  Proof. 
    intro; apply LI1_HI, LI1_cf_LI1; auto.
  Qed.

End LI1_HI.

Section LI2_HI.
  
  Let LI2_imp_HI_rec : forall s, LI2_proof s -> HI_proof (fst s %%> snd s).
  Proof.
    induction 1 as [ | | ga th A B C H1 H2 H3 ] using LI2_proof_rect.
    
    simpl.
    apply HI_proof_perm with (A::ga++de).
    apply Permutation_cons_app; auto.
    simpl; apply HI_proof_weakening, HI_I.
    
    auto.
    
    simpl in *.
    apply HI_proof_perm with (1 := Permutation_sym H1).
    simpl; clear th H1.
    apply HI_list_Form_to_Form_HI_proof with (1 := HI_SI _ _) in H2.
    apply HI_list_Form_to_Form_HI_proof with (1 := HI_C _ _ _) in H3.
    revert H2; apply HI_list_MP.
    revert H3; apply HI_list_Form_to_Form_HI_proof.
    apply in_HI_S.
  Qed.
 
  Theorem LI2_HI A : nil LI2- A -> HI-- A.
  Proof. apply LI2_imp_HI_rec. Qed.
  
End LI2_HI.
  
Theorem LI1_cf_LI2 : LI1_cf_bprovable inc2 LI2_bprovable.
Proof.
  intros n c.
  induction 1 as [ n A 
                 | n ga A B H1 
                 | n ga de th A B C H1 H2 H3
                 | n ga th A B H1 H2
                 | n ga th A B H1 H2 ] using LI1_cf_bprovable_ind.
    
  apply LI2_b_ax with (l := nil).
    
  apply LI2_b_imp_r; auto.
    
  apply LI2_b_imp_l with (ga++de) A B; auto.
  revert H3; apply LI2_incl.
  intros ? [ ? | ? ]; right; [ left | right]; auto; apply in_or_app; auto.
  revert H2; apply LI2_incl.
  intros ? ?; right; apply in_or_app; auto.
  
  apply LI2_bprovable_mono with n; auto.
  revert H2; apply LI2_incl.
  intros d Hd; apply Permutation_in with (1 := Permutation_sym H1).
  destruct Hd as [ ? | [ ? | ? ] ]; [ left | left | right ]; auto.
  
  apply LI2_bprovable_mono with n; auto.
  revert H2; apply LI2_incl.
  intros d Hd; apply Permutation_in with (1 := Permutation_sym H1).
  right; auto.
Qed.

Theorem HI_LI2 A : HI-- A -> exists t, proof LI2_rules (nil,A) t.
Proof.
  intros H.
  apply HI_LI1, inhabits, LI1_cut_admissibility in H. 
  destruct H as (n & t & Ht).
  destruct (@LI1_cf_LI2 n (nil,A)) as (t' & Ht').
  exists t; auto.
  exists t'; apply Ht'.
Qed.

