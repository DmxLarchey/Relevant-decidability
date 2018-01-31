(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith.
Require Import List.
Require Import Permutation.

Require Omega.

Require Import list_in.
Require Import list_perm.
Require Import list_nat.

Set Implicit Arguments.

Section aux.

  Variable (X Y : Type).
  
  Implicit Type (f : X -> Y) (g : X -> list Y).

  Fact map_eq_nil f ll : map f ll = nil <-> ll = nil.
  Proof.
    destruct ll; split; simpl; auto; discriminate 1.
  Qed.

  Fact map_inj f l m :
                (forall x y, f x = f y -> x = y) 
              -> map f l = map f m -> l = m.
  Proof.
    intros Hf; revert m.
    induction l as [ | x l IH ]; intros [ | y m ] H; try discriminate H; auto.
    simpl in H; injection H; clear H; intros; f_equal; auto.
  Qed.

  Fact flat_map_eq_nil g l : 
                 flat_map g l = nil 
              -> forall x, In x l -> g x = nil.
  Proof.
    induction l as [ | x l IH ];simpl.
    intros _ ? [].
    intros H; apply app_eq_nil in H; destruct H.
    intros ? [ ? | ? ]; subst; auto.
  Qed.

  Fact flat_map_length g l : length (flat_map g l) 
                           = lsum (map (fun x => length (g x)) l).
  Proof.
    induction l; simpl; auto.
    rewrite app_length; f_equal; auto.
  Qed.

  Fact flat_map_app g l m : flat_map g (l++m) = flat_map g l ++ flat_map g m.
  Proof.
    induction l; simpl; auto.
    rewrite app_ass; f_equal; auto.
  Qed.
  
  Fact flat_map_ext g h ll : (forall x, In x ll -> g x = h x)
                           -> flat_map g ll = flat_map h ll.
  Proof.
    induction ll; simpl; auto; intro; f_equal; auto.
  Qed.

  Definition concat := flat_map (fun x : list X => x).

  Fact flat_map_concat_eq ll : concat ll = flat_map (fun x : list X => x) ll.
  Proof.
    induction ll; simpl; f_equal; auto.
  Qed.

  Section flat_map_map.
 
    Variable (A B : Type) (f : X -> list Y) (g : A -> X) (h : Y -> B).
  
    Fact flat_map_map ll : flat_map f (map g ll) = flat_map (fun x => f (g x)) ll.
    Proof.
      induction ll; simpl; f_equal; auto.
    Qed.

    Fact map_flat_map ll : map h (flat_map f ll) = flat_map (fun x => map h (f x)) ll.
    Proof.
      induction ll; simpl; f_equal; auto.
      rewrite map_app; f_equal; auto.
    Qed.
  
  End flat_map_map.

  Fact flat_map_perm g h ll : (forall x, In x ll -> g x ~p h x) -> flat_map g ll ~p flat_map h ll.
  Proof.
    induction ll as [ | x ll IH ]; intros H.
    apply Permutation_refl.
    simpl.
    apply Permutation_app.
    apply H; left; auto.
    apply IH; intros; apply H; right; auto.
  Qed.    

  Definition list_flatten := fold_right (@app X) nil.

  Fact list_flatten_spec ll x : In x (list_flatten ll) <-> exists l, In x l /\ In l ll.
  Proof.
    split.
    
    revert x; induction ll as [ | y ll IH ]; simpl.
    intros _ [].
    intros x Hx. 
    apply in_app_or in Hx; destruct Hx as [ Hx | Hx ].
    exists y; tauto.
    destruct (IH _ Hx) as (z & H1 & H2).
    exists z; tauto.
    
    intros (l & H1 & H2); revert x l H1 H2.
    induction ll as [ | y ll IH ]; simpl; intros x l H1 H2; auto.
    destruct H2 as [ H2 | H2 ]; subst; apply in_or_app.
    tauto.
    right; apply IH with (2 := H2); auto.
  Qed.

End aux.

Section fold_right_map.

  Variables (A B C : Type) (f : C -> A -> A) (g : B -> C).

  Fact fold_right_map a ll : fold_right f a (map g ll) = fold_right (fun x y => f (g x) y) a ll.
  Proof.
    induction ll; simpl; f_equal; auto.
  Qed.

End fold_right_map.

Fact fold_right_conj_prop ll : fold_right and True ll <-> forall x, In x ll -> x.
Proof.
  induction ll as [ | x ll IH ]; simpl; split; auto.
  intros ? ? [].
  intros ( H1 & H2 ) a [ H3 | H3 ]; subst; auto; apply (proj1 IH); auto.
  intros H; split.
  apply H; tauto.
  apply IH; intros; apply H; tauto.
Qed.

Fact fold_right_disj_prop ll : fold_right or False ll <-> exists x, In x ll /\ x.
Proof.
  induction ll as [ | x ll IH ]; simpl; split; auto.
  intros [].
  intros ( ? & [] & _).
  
  intros [ H | H ].
  exists x; tauto.
  destruct (proj1 IH H) as (y & ? & ?); exists y; auto.
  
  intros (y & [ H1 | H1 ] & H2); subst; try tauto.
  right; rewrite IH; exists y; auto.
Qed.

(* tails for Schwichtenberg & Seisenberger algorithmic proof of Higman *)

Section tails.

  Variable X : Type.

  (* tails [x1;...;xn] = [[x2;...;xn];[x3;...;xn];...;[xn];[]] *)

  Fixpoint tails (ll : list X) :=
    match ll with
      | nil   => nil
      | x::ll => ll::tails ll
    end.

  Fact tails_length ll : forall x, In x (tails ll) -> length x < length ll.
  Proof.
    induction ll as [ | a ll IH ]; simpl; intros x.
    intros [].
    intros [ H | H ]; subst; auto.
    apply lt_le_trans with (1 := IH _ H).
    auto.
  Qed.

  Fact tails_spec ll r : In r (tails ll) <-> exists l, ll = l++r /\ l <> nil.
  Proof.
    revert r; induction ll as [ | x ll IH ]; intros r; simpl.

    split; try tauto.
    intros ( [ | ] & H1 & H2).
    apply H2; auto.
    discriminate H1.
    
    split.
    intros [ H | H ].
    subst; exists (x::nil); simpl; split; auto; discriminate.
    rewrite IH in H.
    destruct H as (l & H1 & H2).
    exists (x::l); simpl; split.
    f_equal; auto.
    discriminate.
    intros (l & H1 & H2).
    rewrite IH.
    destruct l as [ | y l ].
    contradict H2; auto.
    injection H1; clear H1; intros ? ?; subst.
    destruct l as [ | z l ].
    left; auto.
    right; exists (z::l); split; auto; discriminate.
  Qed.
    
  Fact tail_In_t ll l x : In_t x l -> In_t l (tails ll) -> In_t x ll.
  Proof.
    induction ll as [ | y ll ]; simpl.
    intros _ [].
    intros H1 [ H2 | H2 ]; subst; tauto.
  Defined.
  
  Fact tail_In ll l x : In x l -> In l (tails ll) -> In x ll.
  Proof.
    induction ll as [ | y ll ]; simpl.
    intros _ [].
    intros H1 [ H2 | H2 ]; subst; tauto.
  Defined.    

End tails.

