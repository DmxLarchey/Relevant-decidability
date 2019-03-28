(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Relations Permutation.

Require Import tacs rel_utils list_perm list_induction.

Set Implicit Arguments.

(** Notice that this file implements occurences comparison
    by computing them using decidable equality (a very low
    requirement in the context of proof-search)
   
    It could perhaps be done w/o decidable equality but this
    may require a much bigger effort to implement 
 *)

Section occ_list_repeat.

  Variable (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).
  
  Fixpoint occ x l :=
    match l with
      | nil  => 0
      | y::l => if eqX_dec x y then S (occ x l) else occ x l
    end.
    
  Fact occ_app f l m : occ f (l++m) = occ f l + occ f m.
  Proof.
    induction l as [ | x l IHl ]; simpl; auto.
    destruct (eqX_dec f x); simpl; f_equal; auto.
  Qed.
  
  Fact occ_perm l m : l ~p m -> forall f, occ f l = occ f m.
  Proof.
    intros H f; revert H.
    induction 1 as [ | a l m H IH | | l m k _ H1 _ H2 ]. 
    simpl; auto.
    simpl; rewrite IH; auto.
    simpl.
    destruct (eqX_dec f x); destruct (eqX_dec f y); auto.
    rewrite H1; auto.
  Qed.

  Fact occ_eq f l : occ f (f::l) = S (occ f l).
  Proof.
    simpl.
    destruct (eqX_dec f f) as [ _ | [] ]; auto.
  Qed.
  
  Fact occ_neq f g l : f <> g -> occ f (g::l) = occ f l.
  Proof.
    simpl; intros D.
    destruct (eqX_dec f g) as [ ? | ]; auto.
    contradict D; auto.
  Qed.
  
  Fact not_in_occ_0 f l : ~ In f l -> occ f l = 0.
  Proof.
    induction l as [ | x l IHl ]; simpl; auto.
    destruct (eqX_dec f x).
    intros []; auto.
    intros H; apply IHl; tauto.
  Qed.
  
  Fact in_occ_neq0 f l : In f l <-> 0 < occ f l.
  Proof.
    induction l as [ | x l IHl ]; simpl.
    omega.
    destruct (eqX_dec f x) as [ | C ].
    split; auto; omega.
    rewrite IHl.
    split.
    intros [ ? | ? ]; auto.
    contradict C; auto.
    tauto.
  Qed.
  
  Fixpoint list_repeat (x : X) n :=
    match n with 
      | 0   => nil
      | S n => x :: list_repeat x n
    end.

  Fact list_repeat_plus x n m : list_repeat x (n+m) = list_repeat x n ++ list_repeat x m.
  Proof.
   induction n; simpl; f_equal; auto.
  Qed.

  Fact list_repeat_In x n y : In y (list_repeat x n) -> y = x.
  Proof.
    induction n.
    intros [].
    intros [ ? | ? ]; subst; auto.
  Qed.
  
  Definition In_list_repeat := list_repeat_In.
  
  Fact list_repeat_length x n : length (list_repeat x n) = n.
  Proof.
    induction n; simpl; auto.
  Qed.
    
  Fact list_repeat_prop x l : (forall y, In y l -> y = x) -> l = list_repeat x (length l).
  Proof.
    induction l as [ | y l IHl ]; simpl; intros H; f_equal; auto.
  Qed.
  
  Fact list_repeat_perm_app_l x n l m : list_repeat x n ~p l ++ m -> l = list_repeat x (length l).
  Proof.
    intros H.
    apply list_repeat_prop.
    intros y Hy; apply list_repeat_In with n.
    apply Permutation_in with (1 := Permutation_sym H), in_or_app; left; auto.
  Qed.
  
  Fact list_repeat_perm_app_r x n l m : list_repeat x n ~p l ++ m -> m = list_repeat x (length m).
  Proof.
    intros H.
    apply list_repeat_prop.
    intros y Hy; apply list_repeat_In with n.
    apply Permutation_in with (1 := Permutation_sym H), in_or_app; right; auto.
  Qed.
  
  Fact list_repeat_perm_eq x n l : l ~p list_repeat x n -> l = list_repeat x n.
  Proof.
    revert n; induction l as [ | y l IHl ]; intros n Hn.
    apply Permutation_nil in Hn; auto.
    destruct n as [ | n ].
    apply Permutation_sym, Permutation_nil in Hn; discriminate.
    assert (y = x) as E.
      generalize (Permutation_in _ Hn (or_introl eq_refl)).
      apply In_list_repeat.
    subst y.
    simpl; f_equal.
    apply IHl.
    revert Hn; apply Permutation_cons_inv.
  Qed.

  Fact occ_destruct f l : { m | l ~p list_repeat f (occ f l) ++ m /\ occ f m = 0 }.
  Proof.
    induction l as [ | x l IHl ].
    exists nil; simpl; auto.
    destruct IHl as (m & H1 & H2).
    simpl occ.
    destruct (eqX_dec f x) as [ E | D ].
    exists m; split; auto; simpl; subst; constructor; auto.
    exists (x::m).
    rewrite occ_neq; auto; split; auto.
    apply Permutation_cons_app; auto.
  Qed.
  
  Fact occ_destruct_any l : { x : _ & 
                             { n : _ & 
                              { m | l ~p list_repeat x (S n) ++ m /\ occ x m = 0 } } } + { l = nil }.
  Proof.
    destruct l as [ | x l ].
    right; auto.
    destruct (occ_destruct x l) as (m & H1 & H2).
    left; exists x, (occ x l), m; split; auto.
    simpl; constructor; auto.
  Qed.

  Fact occ_repeat_eq f n : occ f (list_repeat f n) = n.
  Proof.
    induction n; auto.
    simpl list_repeat.
    rewrite occ_eq; f_equal; auto.
  Qed.
  
  Fact occ_repeat_neq f x n : x <> f -> occ x (list_repeat f n) = 0.
  Proof.
    intros H.
    induction n; auto.
    simpl list_repeat.
    rewrite occ_neq; f_equal; auto.
  Qed.
  
  Fact occ_gt_0 f l : 0 < occ f l -> { m | l ~p f::m }.
  Proof.
    intros H.
    destruct (occ_destruct f l) as (m & Hm).
    revert H Hm.
    generalize (occ f l); intros [ | n ] ?.
    exfalso; omega.
    intros (H1 & _).
    exists (list_repeat f n ++ m); auto.
  Qed.
  
  Fact length_occ l m : (forall d, occ d l <= occ d m) -> length l <= length m.
  Proof.
    revert m.
    induction l as [ | x l IHl ].
    intros; simpl; omega.
    intros m Hm.
    assert (In x m) as Hx.
      apply in_occ_neq0.
      specialize (Hm x).
      rewrite occ_eq in Hm; omega.
    apply in_split in Hx.
    destruct Hx as (m1 & m2 & Hx).
    subst m; rewrite app_length; simpl.
    specialize (IHl (m1++m2)).
    spec_all IHl.
    intros d.
    generalize (Hm d).
    repeat rewrite occ_app.
    simpl.
    destruct (eqX_dec d x); omega.
    rewrite app_length in IHl; omega.
  Qed.
    
  Fact occ_construct f l : (forall x, x <> f -> occ x l = 0) -> l = list_repeat f (occ f l).
  Proof.
    intros H.
    destruct (occ_destruct f l) as (m & H1 & H2).
    destruct m as [ | x m ].
    rewrite <- app_nil_end in H1.
    apply list_repeat_perm_eq in H1; auto.
    destruct (eqX_dec x f) as [ H3 | H3 ].
    subst.
    rewrite occ_eq in H2; discriminate.
    apply H in H3.
    rewrite occ_perm with (1 := H1), occ_app, occ_eq in H3.
    omega.
  Qed.
  
  Fact occ_subset l m : (forall d, occ d l <= occ d m) -> exists k, m ~p l ++ k.
  Proof.
    revert l; induction m as [ | x m IHm ]; intros l Hl.
    exists nil.
    destruct l as [ | x ]; auto.
    exfalso; generalize (Hl x).
    rewrite occ_eq; simpl; omega.
    destruct (occ_destruct x l) as (l' & H1 & H2).
    revert H1; generalize (occ x l); intros [ | n ] Hn.
    simpl in Hn.

    destruct (IHm l) as (k & Hk).
    intros d.
    destruct (eqX_dec d x).
    subst; rewrite occ_perm with (1 := Hn); omega.
    generalize (Hl d).
    rewrite occ_neq; auto.
    exists (x::k).
    apply Permutation_cons_app; auto.

    destruct (IHm (list_repeat x n ++ l')) as (k & Hk).
    intros d.
    generalize (Hl d).
    rewrite occ_perm with (1 := Hn).
    simpl list_repeat; simpl app; simpl occ.
    destruct (eqX_dec d x); omega.
    exists k.
    apply Permutation_trans with (1 := perm_skip _ Hk).
    change  (x :: (list_repeat x n ++ l') ++ k)
    with     ((x :: list_repeat x n ++ l') ++ k).
    apply Permutation_app; auto.
    apply Permutation_sym; auto.
  Qed.

  Definition nat_contract a b := 1 <= b <= a \/ a = 0 /\ b = 0.
  
  Definition list_contract l1 l2 := forall d, nat_contract (occ d l1) (occ d l2).
  
  Infix "cc>" := list_contract (at level 70, no associativity).
  
  Fact list_contract_refl l : l cc> l.
  Proof. intros d; red; omega. Qed.
  
  Fact list_contract_trans l m k : l cc> m -> m cc> k -> l cc> k.
  Proof. intros H1 H2 d; generalize (H1 d) (H2 d); unfold nat_contract; omega. Qed.
  
  Fact list_contract_incl l m : l cc> m -> incl l m.
  Proof.
    intros H d; generalize (H d).
    unfold nat_contract.
    do 2 rewrite in_occ_neq0.
    omega.
  Qed.

  Fact perm_list_contract l m : l ~p m -> l cc> m.
  Proof.
    intros H d; rewrite occ_perm with (1 := H); red; omega.
  Qed.
  
  Fact list_contract_perm l1 m1 l2 m2 : l1 ~p m1 -> l2 ~p m2 -> l1 cc> l2 -> m1 cc> m2.
  Proof.
    intros H1 H2 H d.
    rewrite <- occ_perm with (1 := H1),
            <- occ_perm with (1 := H2).
    apply H.
  Qed.
  
  Fact list_contract_app l1 m1 l2 m2 : l1 cc> m1 -> l2 cc> m2 -> (l1++l2) cc> (m1++m2).
  Proof.
    intros H1 H2 d.
    do 2 rewrite occ_app.
    generalize (H1 d) (H2 d).
    unfold nat_contract; omega.
  Qed.
  
  Fact list_contract_cons a l m : l cc> m -> a::l cc> a::m.
  Proof.
    apply list_contract_app with (1 := list_contract_refl (a::nil)).
  Qed.
  
  Fact list_contract_length l1 l2 : l1 cc> l2 -> length l2 <= length l1.
  Proof.
    intros H.
    apply length_occ.
    intros d; generalize (H d). 
    unfold nat_contract; omega.
  Qed.
  
  Fact list_repeat_contract x m n : nat_contract m n <-> list_repeat x m cc> list_repeat x n.
  Proof.
    split.
    intros H d.
    destruct (eqX_dec d x).
    subst; repeat rewrite occ_repeat_eq; auto.
    repeat rewrite occ_repeat_neq; auto; red; auto.
    intros H; generalize (H x).
    repeat rewrite occ_repeat_eq; auto.
  Qed.

  Fact list_repeat_contract_app x n m l : 
       nat_contract m n 
    -> list_repeat x m ++ l cc> list_repeat x n ++ l.
  Proof.
    intros H; apply list_contract_app.
    apply list_repeat_contract; trivial.
    apply list_contract_refl.
  Qed.
  
  Fact list_contract_repeat_app a n l m : 
       l cc> m 
    -> list_repeat a n ++ l cc> list_repeat a n ++ m.
  Proof.
    apply list_contract_app, list_contract_refl.
  Qed.

  Fact list_contract_nil l : nil cc> l -> l = nil.
  Proof.
    intros H.
    apply list_contract_length in H.
    destruct l; simpl in H; auto; omega. 
  Qed.
  
  Fact list_contract_nil_inv l : l cc> nil -> l = nil.
  Proof.
    intros H. 
    destruct l as [ | x l ]; auto.
    exfalso; generalize (H x).
    unfold nat_contract; rewrite occ_eq; simpl; omega.
  Qed.
  
  Fact list_contract_repeat a n l : 
     list_repeat a n cc> l -> { p | l = list_repeat a p /\ p <= n }.
  Proof.
    intros H.
    destruct (occ_destruct a l) as (m & H1 & H2).
    revert H1; generalize (occ a l); intros p H1.
    destruct m as [ | d m ].
    rewrite <- app_nil_end in H1.
    exists p.
    apply list_repeat_perm_eq in H1.
    split; auto.
    subst.
    generalize (H a).
    repeat rewrite occ_repeat_eq; auto.
    unfold nat_contract; omega.
    simpl in H2.
    destruct (eqX_dec a d) as [ | C ].
    discriminate H2.
    specialize (H d).
    rewrite occ_repeat_neq in H; auto.
    red in H.
    rewrite occ_perm with (1 := H1), occ_app, occ_eq in H.
    omega.
  Qed.
  
  Fact list_contract_repeat_S a n l : 
     list_repeat a (S n) cc> l -> { p | l = list_repeat a (S p) /\ p <= n }.
  Proof.
    intros H.
    destruct list_contract_repeat with (1 := H)
      as ( [ | p ] & H1 & H2).
    subst l; apply list_contract_nil_inv in H; discriminate.
    exists p; split; auto; omega.
  Qed.

  Fact list_contract_1 a l : a::nil cc> l -> l = a::nil.
  Proof.
    intros H.
    destruct list_contract_repeat_S with (n := 0) (1 := H) as (p & H1 & H2).
    cutrewrite (p = 0) in H1; auto; omega.
  Qed.
  
  Local Fact eq_1_plus_inv a b : 1 = a + b -> a = 0 /\ b = 1 \/ a = 1 /\ b = 0.
  Proof. omega. Qed.
  
  Local Fact leq_1_inv a : a <= 1 -> a = 0 \/ a = 1.
  Proof. omega. Qed.
  
  Local Fact leq_1_2_inv a : 1 <= a <= 2 -> a = 1 \/ a = 2.
  Proof. omega. Qed.
  
  Fact list_contract_2 a l : a::a::nil cc> l -> l = a::nil \/ l = a::a::nil.
  Proof.
    intros H.
    destruct list_contract_repeat_S with (n := 1) (1 := H) as (p & H1 & H2).
    apply leq_1_inv in H2; destruct H2; subst; tauto.
  Qed.
  
  Fact list_contract_app_inv l m k :
        (forall d, occ d l = 0 \/ occ d m = 0)
     -> l ++ m cc> k
     -> { p : _ & { q | k ~p p ++ q /\ l cc> p /\ m cc> q } }.
  Proof.
    revert k; induction l as [ l IHl ] using list_length_rect; intros k Hlm Hk.
    destruct (occ_destruct_any l) as [ (x & n & l' & H1 & H2) | Hl ].
    destruct (occ_destruct x k) as (k' & H3 & H4).
    revert H3; generalize (occ x k); intros p H3.
    assert (occ x m = 0) as H5.
      generalize (Hlm x).
      rewrite occ_perm with (1 := H1), occ_app, occ_repeat_eq; omega.
    destruct p.
    simpl in H3.
    exfalso.
    generalize (Hk x).
    rewrite occ_app, 
            occ_perm with (1 := H3),
            occ_perm with (1 := H1),
            occ_app, occ_repeat_eq.
    unfold nat_contract; omega.
    
    destruct (IHl l') with (k := k') as (l1 & l2 & G1 & G2 & G3).
    
    apply Permutation_length in H1.
    rewrite app_length in H1; simpl in H1; omega.
    
    intros d.
    destruct (eqX_dec d x) as [ | C ].
    subst d; auto.
    generalize (Hlm d) (occ_perm H1 d) (occ_perm H3 d).
    repeat rewrite occ_app.
    repeat rewrite occ_repeat_neq; auto.
    omega.
    
    intros d; red.
    rewrite occ_app.
    destruct (eqX_dec d x) as [ | C ].
    subst d; omega.
    generalize (Hk d) (occ_perm H1 d) (occ_perm H3 d).
    unfold nat_contract.
    repeat rewrite occ_app.
    repeat rewrite occ_repeat_neq; auto.
    omega.
    
    exists (list_repeat x (S p) ++ l1), l2; split.
    rewrite app_ass.
    apply perm_trans with (1 := H3), Permutation_app; auto.
    split; auto.
    intros d.
    generalize (Hk d) (G2 d) (G3 d).
    rewrite occ_app.
    rewrite occ_perm with (1 := H1),
            occ_perm with (1 := H3).
    repeat rewrite occ_app.
    rewrite occ_perm with (1 := G1).
    repeat rewrite occ_app.
    unfold nat_contract.
    destruct (eqX_dec d x) as [ | C ].
    subst d; repeat rewrite occ_repeat_eq; omega.
    repeat rewrite occ_repeat_neq; auto.
    
    exists nil, k; subst; repeat split; auto.
    apply list_contract_refl.
  Qed.
  
  Fact list_contract_repeat_inv a n l m :
        occ a l = 0
     -> list_repeat a (S n) ++ l cc> m
     -> { p : _ & { k | p <= n 
                     /\ occ a k = 0 
                     /\ m ~p list_repeat a (S p) ++ k 
                     /\ l cc> k } }.
  Proof.
    intros H1 H2.
    apply list_contract_app_inv in H2.
    destruct H2 as (p' & q & H2 & H3 & H4).
    apply list_contract_repeat_S in H3.
    destruct H3 as (p & H3 & H5); subst p'.
    exists p, q; repeat split; auto.
    generalize (H4 a); unfold nat_contract; omega.
    intros d.
    destruct (eqX_dec d a) as [ | C ].
    subst d; auto.
    rewrite occ_repeat_neq; auto.
  Qed.

  Fact list_contract_one_perm x l m : x::l cc> m -> { m' | m ~p x::m' }.
  Proof.
    intros H.
    destruct (occ_destruct x m) as (k & H6 & H7).
    case_eq (occ x m).
    + intros E.
      specialize (H x).
      rewrite occ_eq, E in H.
      exfalso; red in H; omega.
    + intros n Hn.
      exists (list_repeat x n ++ k).
      rewrite Hn in H6; auto.
  Qed.

  Section list_contract_isolate.
   
    (* I do not particularily like those proofs 
       However the results are crucial to the list_contract
       recursion principle list_contract_one_rect
       and list_contract_rect *)
  
    Let list_contract_isolate_rec n l m : 
         length l < n 
      -> l cc> m 
      -> ( l ~p m ) + { x : _ & { n : _ & { p : _ & { l' : _ & { m' | 
                                     1 <= p < n 
                                  /\ l ~p list_repeat x n ++ l'
                                  /\ m ~p list_repeat x p ++ m'
                                  /\ occ x l' = 0
                                  /\ occ x m' = 0
                                  /\ list_contract l' m' } } } } }.
    Proof.
      revert l m; induction n as [ | n IHn ]; intros l m Hn Hlm.
      omega.
      destruct (occ_destruct_any l) as [ (x & p & l' & H1 & H2) | ? ].
      destruct (occ_destruct x m) as (m' & H3 & H4).
      destruct (lt_eq_lt_dec (S p) (occ x m)) as [ [ H5 | H5 ] | H5 ].
    
      exfalso.
      specialize (Hlm x).
      rewrite occ_perm with (1 := H1) in Hlm.
      rewrite occ_perm with (1 := H3) in Hlm.
      repeat rewrite occ_app in Hlm.
      repeat rewrite occ_repeat_eq in Hlm.
      red in Hlm; omega.
    
      rewrite <- H5 in H3.
      destruct (IHn l' m') as [ E | (y & q & r & l'' & m'' & G1 & G2 & G3 & G4 & G5 & G6) ].
      apply Permutation_length in H1.
      rewrite app_length in H1; simpl in H1; omega.
      intros d.
      specialize (Hlm d).
      rewrite occ_perm with (1 := H1) in Hlm.
      rewrite occ_perm with (1 := H3) in Hlm.
      repeat rewrite occ_app in Hlm.
      destruct (eqX_dec d x).
      red in Hlm |- *; subst; omega.
      rewrite occ_repeat_neq in Hlm; auto.
      left.
      apply Permutation_trans with (1 := H1), Permutation_sym,
            Permutation_trans with (1 := H3), Permutation_sym.
      apply Permutation_app; auto.
      right.
      exists y, q, r, (list_repeat x (S p) ++ l''), (list_repeat x (S p) ++ m'').
      split; auto.
      split.
      apply Permutation_trans with (list_repeat x (S p) ++ list_repeat y q ++ l'').
      apply Permutation_trans with (1 := H1), Permutation_app; auto.
      do 2 rewrite <- app_ass.
      apply Permutation_app; auto.
      apply Permutation_app_comm.
      split.
      apply Permutation_trans with (list_repeat x (S p) ++ list_repeat y r ++ m'').
      apply Permutation_trans with (1 := H3), Permutation_app; auto.
      do 2 rewrite <- app_ass.
      apply Permutation_app; auto.
      apply Permutation_app_comm.
      split.
      rewrite occ_app, occ_repeat_neq; auto.
      intro; subst y.
      rewrite occ_perm with (1 := G2) in H2.
      rewrite occ_app, occ_repeat_eq in H2; omega.
      split.
      rewrite occ_app, occ_repeat_neq; auto.
      intro; subst y.
      rewrite occ_perm with (1 := G2) in H2.
      rewrite occ_app, occ_repeat_eq in H2; omega.
      apply list_contract_repeat_app; auto.
    
      right.
      exists x, (S p), (occ x m), l', m'.
      split; auto.
      split; auto.
      specialize (Hlm x).
      rewrite occ_perm with (1 := H1), occ_app, occ_repeat_eq in Hlm.
      red in Hlm; omega.
      split; auto.
      split; auto.
      split; auto.
      split; auto.
      intros d.
      specialize (Hlm d).
      rewrite occ_perm with (1 := H1) in Hlm.
      rewrite occ_perm with (1 := H3) in Hlm.
      repeat rewrite occ_app in Hlm.
      destruct (eqX_dec d x).
      subst; repeat rewrite occ_repeat_eq in Hlm; red in Hlm |- *; omega.
      repeat (rewrite occ_repeat_neq in Hlm; auto); omega.
    
      left.
      subst l.
      apply list_contract_nil in Hlm.
      subst; auto.
    Qed.
 
    Lemma list_contract_isolate l m : 
       l cc> m 
    -> ( l ~p m ) + { x : _ & { n : _ & { p : _ & { l' : _ & { m' | 
                                     1 <= p < n 
                                  /\ l ~p list_repeat x n ++ l'
                                  /\ m ~p list_repeat x p ++ m'
                                  /\ occ x l' = 0
                                  /\ occ x m' = 0
                                  /\ l' cc> m' } } } } }.
    Proof.
      apply list_contract_isolate_rec with (n := S (length l)); auto.
    Qed.

    Lemma list_contract_isolate_one l m :
       l cc> m -> (l ~p m) + { a : _ & { k | l ~p a::a::k /\ a::k cc> m } }.
    Proof.
      intros H.
      apply list_contract_isolate in H.
      destruct H as [ H | (x & n & p & l' & m' & H1 & H2 & H3 & H4 & H5 & H6) ].
      left; auto.
      right; exists x, (list_repeat x (n-2) ++ l'); split.
      cutrewrite (n = 2+(n-2)) in H2; try omega.
      apply perm_trans with (1 := H2); simpl; auto.
      apply Permutation_sym, perm_list_contract in H3.
      apply list_contract_trans with (2 := H3).
      apply list_contract_app with (l1 := list_repeat x (1+(n-2))); auto.
      apply list_repeat_contract.
      red; omega.
    Qed.

  End list_contract_isolate.
  
  Section list_contract_one_rect.
  
    (* A nice induction principle in sort Type which holds when 
       @eq X is decidable *)
  
    Variables (P : list X -> list X -> Type)
              (HP0 : forall l m, l ~p m -> P l m)
              (HP1 : forall a l, P (a::a::l) (a::l))
              (HP2 : forall l m k, P l m -> P m k -> P l k).
    
    Theorem list_contract_one_rect l m : l cc> m -> P l m.
    Proof.
      revert m.
      induction l as [ l IHl ] using list_length_rect; intros m H.
      apply list_contract_isolate_one in H.
      
      destruct H as [ H | (a & k & H1 & H2) ].
      apply HP0; trivial.
      apply HP2 with (a::k).
      apply HP2 with (1 := HP0 H1), HP1.
      apply IHl; auto.
      apply Permutation_length in H1.
      rewrite H1; simpl; omega.
    Qed.
 
  End list_contract_one_rect.
  
  Section list_contract_rect.
  
    (* A "more expressive"  induction principle in sort Type which holds when 
       @eq X is decidable *)
  
    Variable P : list X -> list X -> Type.
    
    Hypothesis HP0 : forall l m, l ~p m -> P l m.
    
    Hypothesis HP1 : forall l m y n p ll, l ~p list_repeat y n ++ ll
                                       -> m ~p list_repeat y p ++ ll 
                                       -> 1 <= p <= n 
                                       -> occ y ll = 0
                                       -> P l m.
                                       
    Hypothesis HP2 : forall l m k, P l m -> P m k -> P l k.
    
    Theorem list_contract_rect l m : l cc> m -> P l m.
    Proof.
      revert m.
      induction l as [ l IHl ] using list_length_rect; intros m H.
      apply list_contract_isolate in H.
      destruct H as [ H | (x & n & p & l' & m' & H1 & H2 & H3 & H4 & H5 & H6) ].
      apply HP0; trivial.
      apply HP2 with (list_repeat x p ++ l').
      apply HP2 with (1 := HP0 H2).
      apply HP1 with x n p l'; auto.
      omega.
      apply IHl.
      apply Permutation_length in H2.
      rewrite H2.
      repeat rewrite app_length.
      repeat rewrite list_repeat_length; omega.
      apply Permutation_sym in H3.
      apply perm_list_contract in H3.
      apply list_contract_trans with (2 := H3).
      apply list_contract_app; auto.
      apply list_contract_refl.
    Qed.
 
  End list_contract_rect.
  
  Inductive list_contract_one (l m : list X) : Prop :=
    | in_list_contract_one : forall y n p ll, l ~p list_repeat y n ++ ll
                                           -> m ~p list_repeat y p ++ ll 
                                           -> 1 <= p <= n 
                                           -> occ y ll = 0
                                           -> list_contract_one l m.
  
  Fact list_contract_trans_one : list_contract inc2 clos_refl_trans _ list_contract_one.
  Proof.
    apply list_contract_rect.
    
    intros l m Hlm.
    destruct (occ_destruct_any l) as [ (x & p & k & H2 & H3) | E ].
    2: subst; apply Permutation_nil in Hlm; subst; constructor 2.
    constructor 1; constructor 1 with x (S p) (S p) k; auto.
    apply perm_trans with (2 := H2), Permutation_sym; auto.
    omega.
    
    intros; constructor 1; constructor 1 with y n p ll; auto.
    
    intros ? m ? ? ?; constructor 3 with m; auto.
  Qed.
  
  Fact list_contract_one_trans : clos_refl_trans _ list_contract_one inc2 list_contract.
  Proof.
    induction 1 as [ l m H | l | l m k H1 IH1 H2 IH2 ].
    induction H as [ y n p ll H1 H2 H3 H4 ].
    apply list_contract_perm with (1 := Permutation_sym H1) (2 := Permutation_sym H2).
    intros d.
    repeat rewrite occ_app.
    unfold nat_contract.
    destruct (eqX_dec d y).
    subst; repeat rewrite occ_repeat_eq; auto; omega.
    repeat rewrite occ_repeat_neq; auto; omega.
    apply list_contract_refl.
    apply list_contract_trans with m; auto.
  Qed.
  
End occ_list_repeat.
