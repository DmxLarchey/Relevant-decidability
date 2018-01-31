(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import tree proof.
Require Import formula sequent_rules.

Require Import relevant_HR relevant_LR2 relevant_LR2_dec relevant_equiv.

Require Import mini_HI mini_LI2 mini_LI2_dec mini_equiv.

Set Implicit Arguments.

(* Then we convert it to HR using proof transformation algorithms *)
  
Corollary HR_decider f : HR_proof f + (HR_proof f -> False).
Proof.
  destruct (LR2_decider (nil,f)) as [ (t & Ht) | H ]; 
    [ left | right ].
    
  apply LR2_HR.
  exists (tree_ht t), t; split; auto; red; auto.
    
  intros H1; apply HR_LR2 in H1; revert H1.
  intros (t & Ht); apply (H t), Ht.
Qed.

Print HR_proof.
Check HR_decider.
Print Assumptions HR_decider.

(* Extraction "hr_decider.ml" HR_decider. *)
  
Corollary HI_decider f : HI_proof f + (HI_proof f -> False).
Proof.
  destruct (LI2_decider (nil,f)) as [ (t & Ht) | H ]; 
    [ left | right ].
    
  apply LI2_HI.
  exists (tree_ht t), t; split; auto; red; auto.
    
  intros H1; apply HI_LI2 in H1; revert H1.
  intros (t & Ht); apply (H t), Ht.
Qed.

Print HI_proof.
Check HI_decider.
Print Assumptions HI_decider.
