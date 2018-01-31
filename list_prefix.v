(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Omega.

Require Import tacs.

Set Implicit Arguments.

Definition app_split X (l1 : list X) : forall l2 r1 r2, l1++r1 = l2++r2
                                      -> { m | l2 = l1++m /\ r1 = m++r2 }
                                       + { m | l1 = l2++m /\ r2 = m++r1 }.
Proof.
  induction l1 as [ | x l1 Hl1 ].
  left; exists l2; auto.
  intros [ | y l2 ] r1 r2 H.
  right; exists (x::l1); auto.
  simpl in H; injection H; clear H; intros H ?; subst.
  apply Hl1 in H.
  destruct H as [ (m & H1 & H2) | (m & H1 & H2) ].
  left; exists m; subst; auto.
  right; exists m; subst; auto.
Qed.

Fact list_split_first_half U (ll : list U) x : x <= length ll -> { l : _ & { r | ll = l++r /\ length l = x } }.
Proof.
  revert ll; induction x as [ | x IHx ]; intros [ | u ll ] Hx.
  exists nil, nil; simpl; auto.
  exists nil, (u::ll); auto.
  simpl in Hx; omega.
  destruct (IHx ll) as (l & r & H1 & H2).
  simpl in Hx; omega.
  exists (u::l), r; simpl; split; f_equal; auto.
Qed.
    
Fact list_split_second_half U (ll : list U) x : x <= length ll -> { l : _ & { r | ll = l++r /\ length r = x } }.
Proof.
  intros Hx.
  destruct list_split_first_half with (ll := ll) (x := length ll - x)
    as (l & r & H1 & H2).
  omega.
  exists l, r; split; auto.
  apply f_equal with (f := @length _) in H1.
  rewrite app_length in H1.
  omega.
Qed.  

Section list_prefix. 

  Variables (X : Type).

  Fixpoint pfx (f : nat -> X) n :=
      match n with
        | 0   => nil
      | S n => f 0 :: pfx (fun n => f (S n)) n
    end.

  Fact pfx_length f n : length (pfx f n) = n.
  Proof.
    revert f; induction n; intros f; simpl; auto.
  Qed.
    
  Fact pfx_plus f a b : pfx f (a+b) = pfx f a ++ pfx (fun n => f (a+n)) b.
  Proof.
    revert f;
    induction a; intros f; simpl; auto.
    f_equal; apply IHa.
  Qed.

  Fact pfx_In f n x : In x (pfx f n) <-> exists i, i < n /\ x = f i.
  Proof.
    split.

    revert f; induction n as [ | n IHn ]; intros f; simpl.
    intros [].
    intros [ H | H ].
    subst; exists 0; split; auto; omega.
    destruct (IHn _ H) as (i & H1 & H2).
    exists (S i); split; auto; omega.
    
    intros (i & H1 & H2); subst x.
    revert f i H1.
    induction n as [ | n IH ]; intros f i Hi; try omega; simpl.
    destruct i.
    left; auto.
    right. 
    apply (IH (fun x => f (S x))); omega.
  Qed.

  Fact pfx_eq f n l x r : pfx f n = l++x::r -> f (length l) = x.
  Proof.
    revert f l x r; induction n as [ | n IH ]; intros f l x r; simpl.
    destruct l; discriminate 1.
    destruct l as [ | y l ]; simpl;
    intros H; injection H; clear H; intros H1 H2; auto.
    apply IH in H1; auto.
  Qed.

  Fixpoint list_fun_concat l f n : X :=
    match l with 
      | nil  => f n
      | x::l => 
      match n with 
        | 0   => x
        | S n => list_fun_concat l f n
      end
    end.

  Fact lf_concat_pfx_lt ll f n : n < length ll -> exists l r, l ++ r = ll /\ l = pfx (list_fun_concat ll f) n.
  Proof.
    revert n; induction ll as [ | x ll IH ]; intros [ | n ] Hn; simpl in Hn; try (exfalso; omega); simpl.
    exists nil, (x::ll); auto.
    destruct (IH n) as (l & r & H1 & H2).
    omega.
    exists (x::l), r; simpl; split; f_equal; auto.
  Qed.
  
  Fact lf_concat_pfx_ge ll f n : length ll <= n -> pfx (list_fun_concat ll f) n = ll ++ pfx f (n - length ll).
  Proof.
    revert n; induction ll as [ | x ll IH ]; intros n Hn.
    simpl; f_equal; omega.
    destruct n.
    simpl in Hn; omega.
    simpl.
    f_equal.
    apply IH.
    simpl in Hn; omega.
  Qed.

End list_prefix.

Fact pfx_map X Y (h : X -> Y) f n : pfx (fun n => h (f n)) n = map h (pfx f n).
Proof.
  revert f; induction n; intros f; simpl; f_equal; auto.
Qed.

(* prefix of an infinite sequence, in reverse order *)
   
Section list_prefix_rev.
 
  Variable X : Type.

  Fixpoint pfx_rev f n : list X := 
    match n with 
      | 0   => nil
      | S n => (f n)::(pfx_rev f n)
    end.

  Fact pfx_rev_plus f a b : pfx_rev f (a+b) = pfx_rev (fun n => f (b+n)) a ++ pfx_rev f b.
  Proof.
    induction a; simpl; auto.
    f_equal; auto.
    f_equal; apply plus_comm.
  Qed.
  
  Fact pfx_rev_S f a : pfx_rev f (S a) = pfx_rev (fun n => f (S n)) a ++ f 0 :: nil.
  Proof.
    generalize (pfx_rev_plus f a 1); intros H.
    replace_with H; f_equal; rewrite plus_comm; auto.
  Qed.

  Fact pfx_pfx_rev_eq f n : pfx_rev f n = rev (pfx f n).
  Proof.
    revert f.
    induction n as [ | n IHn ]; intros f.
    simpl; auto.
    simpl pfx.
    cutrewrite (S n = n+1); try omega.
    rewrite pfx_rev_plus; simpl.
    f_equal; auto.
  Qed.  

  Fact pfx_rev_ext f g n : (forall x, x < n -> f x = g x) -> pfx_rev f n = pfx_rev g n.
  Proof.
    induction n; simpl; auto; 
    intros H.
    rewrite H; try omega.
    f_equal; auto.
  Qed.
  
  Fact pfx_rev_minus f n : pfx_rev f n = pfx (fun x => f (n - S x)) n.
  Proof.
    revert f; induction n as [ | n IHn ]; intros f; simpl; auto.
    do 2 f_equal. omega.
    apply IHn.
  Qed.    

  Fact pfx_rev_In f n x : In x (pfx_rev f n) <-> exists i, i < n /\ x = f i.
  Proof.
    split.

    induction n as [ | n IHn ]; simpl.
    intros [].
    intros [ H | H ].
    subst; exists n; auto.
    destruct (IHn H) as (i & H1 & H2).
    exists i; split; auto.
    
    intros (i & H1 & H2); subst x.
    revert i H1.
    induction n as [ | n IH ]; intros i Hi; try omega; simpl.
    destruct (le_lt_dec n i).
    left; f_equal; omega.
    right; apply IH; auto.
  Qed.

  Fact pfx_rev_length f n : length (pfx_rev f n) = n.
  Proof.
    induction n; simpl; auto.
  Qed.

  Fact pfx_rev_eq f n l x r : pfx_rev f n = l++x::r -> f (length r) = x.
  Proof.
    revert l x r; induction n as [ | n IH ]; intros l x r; simpl.
    destruct l; discriminate 1.
    destruct l as [ | y l ]; simpl;
    intros H; injection H; clear H; intros H1 H2.
    replace_with H2; f_equal.
    subst r; apply pfx_rev_length.
    apply IH with (1 := H1).
  Qed.

End list_prefix_rev.

Fact pfx_rev_map X Y (h : X -> Y) f n : pfx_rev (fun n => h (f n)) n = map h (pfx_rev f n).
Proof.
  induction n; simpl; f_equal; auto.
Qed.
 
Definition list_prefix X (ll : list X) n : n <= length ll -> { l : _ & { r | ll = l++r /\ length l = n } }.
Proof.
  revert n; induction ll as [ | x ll IH ].
  intros [ | n ] Hn; exists nil, nil; split; auto.
  exfalso; simpl in Hn; omega.
  intros [ | n ] Hn.
  exists nil, (x::ll); auto.
  simpl in Hn.
  destruct (IH n) as (l & r & H1 & H2).
  omega.
  subst.
  exists (x::l), r; auto.
Qed.

Definition list_suffix X (ll : list X) n : n <= length ll -> { l : _ & { r | ll = l++r /\ length r = n } }.
Proof.
  intros H.
  destruct (@list_prefix _ ll (length ll - n)) as (l & r & H1 & H2).
  omega.
  exists l, r; repeat split; auto.
  apply f_equal with (f := @length _) in H1.
  rewrite app_length in H1.
  omega.
Qed.

Fact list_prefix_eq X (l r l' r' : list X) : l++r = l'++r' -> length l = length l' -> l = l' /\ r = r'.
Proof.
  revert l'; induction l as [ | x l IHl ]; intros [ | y l' ] H1 H2; auto; simpl in H2; try discriminate H2.
  simpl in H1; injection H1; clear H1; intros H1 H3; subst.
  destruct IHl with (1 := H1).
  omega.
  subst; auto.
Qed.

Fact list_suffix_eq X (l r l' r' : list X) : l++r = l'++r' -> length r = length r' -> l = l' /\ r = r'.
Proof.
  intros H1 H2; apply list_prefix_eq; auto.
  apply f_equal with (f := @length _) in H1.
  do 2 rewrite app_length in H1.
  omega.
Qed.

Fact list_suffix_split X (l r l' r' : list X) : l++r = l'++r' -> length r <= length r' -> { m | l = l'++m /\ r' = m++r }.
Proof.
  revert r l' r'; induction l as [ | x l IHl ]; intros r [ | y l' ] r' H1 H2; simpl in H1.
  exists nil; auto.
  apply f_equal with (f := @length _) in H1.
  simpl in H1.
  rewrite app_length in H1.
  exfalso; omega.
  exists (x::l); auto.
  injection H1; clear H1; intros H1 ?; subst y.
  destruct IHl with (1 := H1) as (m & H3 & H4); auto.
  exists m; subst; auto.
Qed.
