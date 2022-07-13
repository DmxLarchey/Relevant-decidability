(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Permutation.

Require Import tacs rel_utils list_utils finite.

Require Import almost_full.

Require Import tree proof.

Require Import formula sequent_rules mini_LI2.

Set Implicit Arguments.

Section LI2_decider.

  (* Redundancy for LI2 is sequent are identical when considered as sets *)

  Let redund (y x : Seq) := eql (fst x) (fst y) /\ snd x = snd y.

  Let LI2_redund_af_t s : af_t (redund <# LR_sf s #>).
  Proof.
    generalize (af_t_prod (af_t_eql_finite (sf_Seq_finite_t s))
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
    intros []; split; simpl; auto; apply eql_sym; auto.
  Qed.

  Theorem LI2_decider : forall s, { t | proof LI2_rules s t } + { forall t, ~ proof LI2_rules s t }.
  Proof.
    apply proof_decider with (1 := LI2_rules_finite_t) (sf := LR_sf) (redund := redund).

    apply LR_sf_refl.
    apply LR_sf_trans.
    apply sf_LI2_rules.
    2: apply LI2_redund_af_t.

    unfold redund; intros (ga,a) (de,b) t; simpl.
    intros H1 (H2 & ?); subst b.
    destruct (@LI2_incl (tree_ht t) _ _ a (proj1 H2))
      as (t' & Ht').
    exists t; split; auto; red; auto.
    exists t'; apply Ht'.
  Qed.

End LI2_decider.

Check LI2_decider.
Print Assumptions LI2_decider.
