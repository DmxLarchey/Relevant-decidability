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
Require Import relevant_HR relevant_LR1 relevant_LR2 sem_cut_adm.

Set Implicit Arguments.

(** These are high level equivalence results between 

    a) HR Hilbert style proofs for Relevant Logic
    b) LR1 and LR1_cf sequent calculi for Relevant Logic
       where _cf means cut-free
    c) LR2 sequent calculus with customized contraction
       absorbed into the rules
       
 *)

(** LR1 cut-free proofs are LR1 proofs **)

Theorem LR1_cf_LR1 : LR1_cf_proof inc1 LR1_proof.
Proof.
  induction 1 as [ | | ? ? ? ? ? ? H | ? ? ? ? H ] using LR1_cf_proof_rect.
  apply LR1_rule_id.
  apply LR1_rule_r; trivial.
  apply LR1_rule_l with (1 := H); trivial.
  apply LR1_rule_cntr with (1 := H); trivial.
Qed.

Local Hint Resolve LR1_rule_id perm_skip perm_swap.

Local Notation "HR--" := HR_proof.
Local Notation "x 'LR1-' y" := (LR1_proof (x,y)) (at level 70, no associativity).  
Local Notation "x 'LR1cf-' y" := (LR1_cf_proof (x,y)) (at level 70, no associativity).
Local Notation "x 'LR2-' y" := (LR2_proof (x,y)) (at level 70, no associativity).

(** Any HR proof of A can be transformed into a LR1 proof of ø |- A **)

Theorem HR_LR1 A : HR-- A -> nil LR1- A.
Proof.
  induction 1 as [ A | A B C | A B C | A B | A B _ IH1 _ IH2 ].
    
  apply LR1_rule_r; auto.
    
  do 3 apply LR1_rule_r.
  apply LR1_rule_l with (C :: nil) (A %> B :: nil) C A; simpl; auto.
  apply LR1_rule_l with (A :: nil) nil A B; simpl; auto.
    
  do 3 apply LR1_rule_r.
  apply LR1_rule_l with (A :: nil) (B :: nil) A (B %> C); simpl; auto.
  apply perm_trans with (2 := perm_swap _ _ _); auto.
  apply LR1_rule_l with (B :: nil) nil B C; simpl; auto.
  
  do 2 apply LR1_rule_r.
  apply LR1_rule_cntr with (A %> A %> B :: nil) A; auto.
  apply LR1_rule_l with (A :: nil) (A :: nil) A (A %> B); simpl; auto.
  apply perm_trans with (2 := perm_swap _ _ _); auto.
  apply LR1_rule_l with (A :: nil) nil A B; simpl; auto.
    
  apply LR1_rule_cut with (2 := IH2) (de := nil); auto.
  apply LR1_rule_cut with (2 := IH1) (de := A :: nil); auto.
  apply LR1_rule_l with (A :: nil) nil A B; simpl; auto.
Qed.

Section LR1_HR.

  Let LR1_HR_rec : forall s, LR1_proof s -> HR_proof (fst s %%> snd s).
  Proof.
    induction 1 as [ 
                   | 
                   | ga de th A B C H1 H3 H4 
                   | de th A B H1 H3 
                   | ga de th A B H1 H2 H3 ] using LR1_proof_rect; simpl in * |- *.
                   
    (* LR1_rule_id *)

    intros; constructor.
    
    (* LR1_rule_r *)
    
    auto.
    
    (* LR1_rule_l *)
 
    apply Permutation_sym in H1.
    apply HR_proof_perm with (1 := H1).
    simpl; rewrite list_Form_to_Form_app.
    revert H4; apply HR_list_Form_to_Form_HR_proof.
    assert (B %> C :: A %> B :: ga ~p A %> B :: ga ++ B %> C :: nil) as H4.
      apply perm_trans with (1 := perm_swap _ _ _), perm_skip,
            Permutation_app_comm with (l := _ :: nil).
    apply HR_proof_perm with (a := C) in H4.
    simpl in H4; rewrite list_Form_to_Form_app in H4; auto.
    simpl; revert H3; apply HR_list_Form_to_Form_HR_proof.
    clear H1 H4.
    generalize (in_HR_pfx B C A).
    apply HR_proof_perm with (l := _ :: _ :: _ :: nil) 
                             (m := _ :: _ :: _ :: nil).
    apply perm_trans with (1 := perm_swap _ _ _),
          perm_trans with (2 := perm_swap _ _ _); auto.
          
    (* LR1_rule_c *)
          
    apply HR_proof_perm with (1 := Permutation_sym H1).
    revert H3; apply HR_proof_contract.
    
    (* LR1_rule_cut *)
    
    apply Permutation_sym in H1.
    apply HR_proof_perm with (1 := H1).
    simpl; rewrite list_Form_to_Form_app.
    revert H3; apply HR_list_Form_to_Form_HR_proof.
    assert (A %> B :: ga ~p ga ++ A %> B :: nil) as E.
      apply Permutation_sym, Permutation_app_comm.
    apply HR_proof_perm with (a := B) in E.
    simpl in E; rewrite list_Form_to_Form_app in E; auto.
    simpl; revert H2; apply HR_list_Form_to_Form_HR_proof.
    apply in_HR_MP with (1 := in_HR_comm _ _ _), in_HR_ax.
  Qed.
  
  (** Any LR1 proof of ø |- A can be transformed into an HR proof of A *)
  
  Theorem LR1_HR A : nil LR1- A -> HR-- A.
  Proof. apply LR1_HR_rec. Qed.

  (** Any cut-free LR1 proof of ø |- A can be transformed into an HR proof of A *)

  Theorem LR1_cf_HR A : nil LR1cf- A -> HR-- A.
  Proof. 
    intro; apply LR1_HR, LR1_cf_LR1; auto.
  Qed.

End LR1_HR.

Section LR2_HR.
  
  Let LR2_imp_HR_rec : forall s, LR2_proof s -> HR_proof (fst s %%> snd s).
  Proof.
    induction 1 as [ | | ga de th th' A B C H1 H2 H3 H4 ] using LR2_proof_rect.
    
    intros; simpl; constructor.
    
    auto.
 
    simpl in H3, H4 |- *.
    apply HR_proof_perm with (1 := Permutation_sym H1).
    apply HR_proof_list_contract with (1 := LR2_condition_contract H2).
    simpl; rewrite list_Form_to_Form_app.
    revert H4; apply HR_list_Form_to_Form_HR_proof.
    assert (B %> C :: A %> B :: ga ~p A %> B :: ga ++ B %> C :: nil) as H4.
      apply perm_trans with (1 := perm_swap _ _ _).
      apply perm_skip.
      apply Permutation_app_comm with (l := _ :: nil).
    apply HR_proof_perm with (a := C) in H4.
    simpl in H4; rewrite list_Form_to_Form_app in H4; auto.
    simpl; revert H3; apply HR_list_Form_to_Form_HR_proof.
    
    clear H1 H2 H4.
    apply HR_proof_perm with (l := A :: A %> B :: B %> C :: nil)
                             (m := B %> C :: A %> B :: A :: nil); simpl.
    apply perm_trans with (1 := perm_swap _ _ _).
    apply perm_trans with (2 := perm_swap _ _ _).
    apply perm_skip, perm_swap.
    apply in_HR_pfx. 
  Qed.
  
  (** Any LR2 proof of A can be transformed into a HR proof of A *)

  Theorem LR2_HR A : nil LR2- A -> HR-- A.
  Proof. apply LR2_imp_HR_rec. Qed.
  
End LR2_HR.

(** If   ga |- A has a cut-free LR1 proof of size bounded by n
    then ga |- A has a LR2 proof of size bounded by n *)
  
Theorem LR1_cf_LR2 : LR1_cf_bprovable inc2 LR2_bprovable.
Proof.
  intros n c.
  induction 1 as [ n A 
                 | n ga A B H1 
                 | n ga de th A B C H1 H2 H3
                 | n ga th A B H1 H2 ] using LR1_cf_bprovable_ind.
    
  apply LR2_b_id.
    
  apply LR2_b_imp_r; auto.
    
  apply LR2_b_imp_l with ga de (ga++de) A B; auto.
  split.
  intros d Hd; repeat rewrite occ_neq; auto.
  repeat rewrite occ_app; red; omega.
  repeat rewrite occ_eq.
  repeat rewrite occ_app; red; omega.
    
  apply LR2_Curry with (A::A::th).
  2: revert H2; apply LR2_bprovable_mono; omega.
  apply Permutation_sym in H1.
  apply list_contract_perm with (1 := Permutation_refl _) (2 := H1).
  intros x; simpl; destruct (Form_eq_dec x A); red; omega.
Qed.
  
(** For any HR proof of A there exists a LR2 proof of ø |- A *)

Theorem HR_LR2 A : HR-- A -> exists t, proof LR2_rules (nil,A) t.
Proof.
  intros H.
  apply HR_LR1, inhabits, LR1_cut_admissibility in H. 
  destruct H as (n & t & Ht).
  destruct (@LR1_cf_LR2 n (nil,A)) as (t' & Ht').
  exists t; auto.
  exists t'; apply Ht'.
Qed.

