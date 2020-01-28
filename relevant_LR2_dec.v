(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation.

Require Import tacs rel_utils list_utils finite.

Require Import almost_full list_contract_af.

Require Import tree proof.

Require Import formula relevant_contract.
Require Import sequent_rules relevant_LR2.

Set Implicit Arguments.

(* LR2 is used to decide relevant logic *)

Local Notation " g '|--' a " := ((g,a):Seq) (at level 70, no associativity).

Section LR2_decider.

  (* Redundancy for LR2 is the reflexivce and transitive closure of the contraction rule *)

  Definition redund (y x : Seq) := list_contract Form_eq_dec (fst x) (fst y) /\ snd x = snd y.

  Infix "≺r" := redund (at level 70, no associativity).
  
  (* We transport the af_t property from a product (Ramsey theorem) 
     using the very useful af_t_relmap ...
     
     It works like a charm on Sigma types, try with af_t_comap 
     instead and you will feel the difference ...
  *)

  Theorem Kripke_LR2 ga A : af_t (redund restr LR_sf (ga |-- A)).
  Proof.
    generalize (ga |-- A); clear ga A; intro s.
    generalize (af_t_prod (af_t_list_contract Form_eq_dec (sf_Seq_finite_t s))
                          (af_t_eq_finite (sf_Seq_finite_t s))).
    apply af_t_relmap with (f := fun x y => proj1_sig (fst x) = fst (proj1_sig y)
                                         /\ proj1_sig (snd x) = snd (proj1_sig y)).
                                         
    intros ((ga,a) & H); simpl.
    red in H.
    assert (Forall (sf_Seq s) ga) as H1.
      apply Forall_forall; intros u Hu.
      apply H; left; exists u; split; auto.
      apply sf_Form_refl.
    assert (sf_Seq s a) as H2.
      apply H; right; apply sf_Form_refl.
    exists (exist _ ga H1, exist _ a H2); auto.
    
    intros ((? & ?) & (? & ?)) ((? & ?) & (? & ?)) ((?,?) & ?) ((?,?) & ?); simpl.
    intros (? & ?) (? & ?); subst; unfold rel_prod; simpl. 
    intros []; split; auto.
  Qed.

  Theorem LR2_decider : forall s, { t | proof LR2_rules s t } + { forall t, ~ proof LR2_rules s t }.
  Proof.
    apply proof_decider with (1 := LR2_rules_finite_t) (sf := LR_sf) (redund := redund).
 
    apply LR_sf_refl.
    apply LR_sf_trans.
    apply sf_LR2_rules.
    2: intros []; apply Kripke_LR2.
    
    (* contraction is height preserving (Curry's lemma) *)

    unfold redund; intros (ga,a) (de,b) t; simpl.
    intros H1 (H2 & ?); subst b.
    destruct (@LR2_Curry (tree_ht t) de ga a a) as (t' & Ht'); try tauto.
    exists t; split; auto; red; auto.
    exists t'; apply Ht'.
  Qed.

End LR2_decider.

Check LR2_decider.
Print Assumptions LR2_decider.
