(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Lia.

Require Import tacs.

Require Import list_nat.
Require Import list_decide.

Set Implicit Arguments.

Section list_find_dup.

  Variable X : Type.

  Implicit Type (f : nat -> X).

  Let find_dup n l f : length l = S n -> (forall i, i <= S n -> In (f i) l) -> exists i j, i < j <= S n /\ f i = f j.
  Proof.
    revert l f.
    induction n as [ | n IHn ]; intros m f Hn Hf.

    destruct m as [ | x [ | ] ]; try discriminate Hn.
    exists 0, 1.
    split.
    lia.
    destruct (Hf 0) as [ H | [] ]; try lia.
    destruct (Hf 1) as [ | [] ]; try lia.
    rewrite <- H; auto.

    generalize (Hf 0).
    intros H0; spec_all H0.
    lia.
    apply in_split in H0.
    destruct H0 as (l & r & H0).
    assert (length (l++r) = S n) as L0.
      revert Hn; subst m; do 2 rewrite app_length; simpl.
      intro; lia.

    assert (forall i, In i (list_n (S (S n))) -> f (S i) = f 0 \/ In (f (S i)) (l++r)) as H1.
      intros i Hi.
      specialize (Hf (S i)).
      spec_all Hf.
      rewrite <- list_n_prop in Hi.
      lia.

    subst m.
    apply in_app_or in Hf; destruct Hf as [ Hf | [ Hf | Hf ] ].
    right; apply in_or_app; left; auto.
    left; auto.
    right; apply in_or_app; right; auto.

    apply list_choose in H1.
    destruct H1 as [ (j & H1 & H2) | H1 ].

    exists 0, (S j).
    split; auto.
    rewrite <- list_n_prop in H1.
    lia.

    destruct (IHn (l++r) (fun i => f (S i))) as (i & j & H2 & H3); auto.

    intros i Hi.
    apply H1.
    rewrite <- list_n_prop.
    lia.
    exists (S i), (S j).
    split; auto; lia.
  Qed.

  Fact list_find_dup f l : (forall i, i <= length l -> In (f i) l) -> exists i j, i < j <= length l /\ f i = f j.
  Proof.
    intros H2.
    destruct l as [ | x l ].
    exfalso; apply (H2 0); auto.
    simpl; apply find_dup with (n := length l) (l := x::l); auto.
  Qed.

End list_find_dup.