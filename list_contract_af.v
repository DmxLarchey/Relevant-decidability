(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Lia List Relations Permutation.

Require Import tacs rel_utils list_utils.
Require Import finite almost_full.

Set Implicit Arguments.

Fact af_t_nat_contract : af_t (fun x y => nat_contract y x).
Proof.
  assert (af_t (fun x y => x = 0 <-> y = 0)) as H1.
    apply in_af_t1; intros [ | x ];
    apply in_af_t1; intros [ | y ];
    apply in_af_t0; intros a b; cbv; lia.
  generalize (af_t_inter H1 (le_af_t)).
  apply af_t_inc.
  unfold nat_contract; intros; lia.
Qed.

Section af_contract.

  Variables (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).

  Notation occ := (@occ _ eqX_dec).
  Notation list_contract := (@list_contract _ eqX_dec).
  Notation list_redund := (fun x y => list_contract y x).

  Fact af_t_nat_contract_list (ll : list X) : af_t (fun l m => forall d, In d ll -> nat_contract (occ d m) (occ d l)).
  Proof.
    induction ll as [ | x ll IHll ].

    apply in_af_t0.
    intros _ _ ? [].

    generalize (af_t_prod af_t_nat_contract IHll).
    apply af_t_relmap with (f := fun c d => fst c = occ x d /\ forall y, In y ll -> occ y (snd c) = occ y d).

    intros d; exists (occ x d, d); simpl; auto.

    intros (x1,c1) (x2,c2) d1 d2; simpl.
    intros (? & H1) (? & H2); subst x1 x2.
    intros [ H3 H4 ]; simpl in H3, H4.
    intros d [ [] | Hd ]; auto.
    rewrite <- H1, <- H2; auto.
  Qed.

  Theorem af_t_list_contract P : finite_t P -> af_t (list_redund restr Forall P).
  Proof.
    intros (ll & Hll).
    generalize (af_t_nat_contract_list ll).
    apply af_t_relmap with (f := fun l m => l = proj1_sig m).
    intros (l & Hl); exists l; auto.
    intros x1 x2 (y1 & H1) (y2 & H2); simpl.
    intros ? ? H3; subst y1 y2.
    intros d.
    destruct (in_dec eqX_dec d ll) as [ H | H ].
    apply H3; auto.
    rewrite Forall_forall in H1.
    rewrite Forall_forall in H2.
    right; split; apply not_in_occ_0; contradict H; apply Hll;
      [ apply H2 | apply H1 ]; auto.
  Qed.

End af_contract.