(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Relations.

Set Implicit Arguments.

Section list_splits.

  Variables (X : Type).

  Implicit Types (l : list X).

  Fixpoint list_splits l :=
    match l with
      | nil =>  ((nil,nil)::nil)
      | x::l => (nil,x::l)::map (fun (c : list X * list X) => let (u,v) := c in (x::u,v)) (list_splits l)
    end.

  Fact list_splits_spec l x y : In (x,y) (list_splits l) <-> x++y = l.
  Proof.
    revert x y.
    induction l as [ | a l IH ]; intros x y; simpl; split.
    intros [ H | [] ]; injection H; intros; subst; auto.
    destruct x; destruct y; try discriminate 1; tauto.
    intros [ H | H ].
    injection H; intros; subst; auto.
    apply in_map_iff in H.
    destruct H as ((u,v) & H1 & H2).
    injection H1; clear H1; intros ? ?; subst x y.
    rewrite IH in H2.
    rewrite <- H2; auto.
    intros H.
    destruct x as [ | a' x ].
    simpl in H; subst y; left; auto.
    injection H; clear H; intros ? ?; subst a' l; right.
    apply in_map_iff.
    exists (x,y).
    rewrite IH; auto.
  Qed.

  Definition lmr l := flat_map (fun c => match c with (_,nil) => nil | (l,x::r) => (l,(x,r))::nil end) (list_splits l).

  Fact lmr_spec ll w : In w (lmr ll) <-> exists l x r, ll = l++x::r /\ w = (l,(x,r)).
  Proof.
    unfold lmr; rewrite in_flat_map.
    split.

    intros ((l,[ | x r ]) & H1 & H2).
    destruct H2.
    destruct H2 as [ H2 | [] ]; subst.
    apply list_splits_spec in H1; subst.
    exists l, x, r; auto.

    intros (l & x & r & H1 & H2); subst.
    exists (l,x::r); split; simpl; auto.
    rewrite list_splits_spec; auto.
  Qed.

  Let list_msplits k l : { ll | forall m, In m ll <-> flat_map (fun x => x) m = l /\ length m = S k }.
  Proof.
    revert l; induction k as [ | k IH ]; intros l.

    exists ((l::nil)::nil); split.
    intros [ ? | [] ]; subst; simpl; rewrite <- app_nil_end; auto.
    intros (H1 & H2).
    destruct m as [ | a [ | ] ]; try discriminate H2; simpl in H1.
    rewrite <- app_nil_end in H1; subst a; left; auto.

    set (h l := proj1_sig (IH l)).
    assert (Hh : forall l m, In m (h l) <-> flat_map (fun x => x) m = l /\ length m = S k).
      intros u; apply (proj2_sig (IH u)).
    generalize h Hh; clear h Hh IH; intros h Hh.

    set (g (c : list X * list X) := let (w1,w2) := c in map (fun d => w1::d) (h w2)).

    exists (flat_map g (list_splits l)).
    intros m; split.

    rewrite in_flat_map.
    intros ((u,v) & H1 & H2).
    unfold g in H2.
    rewrite list_splits_spec in H1.
    rewrite in_map_iff in H2.
    destruct H2 as (ll & H2 & H3).
    rewrite Hh in H3.
    destruct H3 as (H3 & H4).
    subst m l v; split; simpl; auto.

    intros (H1 & H2).
    rewrite in_flat_map.
    destruct m as [ | a m ]; try discriminate H2.
    simpl in H2; injection H2; clear H2; intros H2.
    simpl in H1; subst l.
    exists (a, flat_map (fun x => x) m); split.
    rewrite list_splits_spec; auto.
    unfold g.
    rewrite in_map_iff.
    exists m; split; auto.
    rewrite Hh; split; auto.
  Qed.

  Definition list_multi_splits k l := proj1_sig (list_msplits k l).

  Fact list_multi_splits_spec k l mm : In mm (list_multi_splits k l) <-> flat_map (fun x => x) mm = l /\ length mm = S k.
  Proof.
    apply (proj2_sig (list_msplits k l)).
  Qed.

End list_splits.

