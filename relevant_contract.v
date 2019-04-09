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

Set Implicit Arguments.

Section Relevant.

  Variables (X : Type) (eqX_dec : forall x y : X, { x = y } + { x <> y }).
  
  Notation occ := (@occ _ eqX_dec).
  Infix "c>>" := (@list_contract _ eqX_dec) (at level 70, no associativity).

  Local Fact part_eq p a b : p <= a + b -> { a' : _ & { b' | a' <= a /\ b' <= b /\ p = a' + b' } }.
  Proof.
    intros H.
    destruct (le_lt_dec p a).
    exists p, 0; omega.
    exists a, (p-a); omega.
  Qed.
  
  Local Fact part_eq_SS p a b : 
     2 <= p <= a + b -> { a' : _ & { b' | a' <= a /\ b' <= b /\ p = a' + b' /\ (a' = 0 -> a = 0) /\ (b' = 0 -> b = 0) } }.
  Proof.
    intros H.
    destruct a.
    exists 0, p; omega.
    destruct b.
    exists p, 0; omega.
    destruct (@part_eq (p-2) a b) as (a' & b' & ? & ? & ?).
    omega.
    exists (S a'), (S b'); omega.
  Qed.

  Definition LR2_condition_1 a e h := 
     (h = 0  -> a = 0 /\ e = 0)
  /\ (h = 1  -> a = 0 /\ e = 1
             \/ a = 1 /\ e = 0
             \/ a = 1 /\ e = 1)
  /\ (2 <= h -> h = a + e).

  Definition LR2c_1 a b c := (c <= 1 /\ c <= a+b /\ a <= c /\ b <= c) \/ (2 <= c /\ c = a + b).
  Definition LR2c_2 a b c := (c <= 1 /\ c <= a+b /\ a <= 1 /\ b <= 1) \/ (2 <= c /\ c = a + b).

  Fact LR2_condition_1_eq a b c : LR2_condition_1 a b c <-> LR2c_1 a b c.
  Proof. unfold LR2_condition_1, LR2c_1; omega. Qed.

  Definition LR2_condition_2 a e h :=
     (h = 0  -> a = 0 /\ e = 0)
  /\ (h = 1  -> a = 0 /\ e = 0
             \/ a = 0 /\ e = 1
             \/ a = 1 /\ e = 0
             \/ a = 1 /\ e = 1)
  /\ (h = 2  -> a = 0 /\ e = 1
             \/ a = 1 /\ e = 0
             \/ a = 1 /\ e = 1)
  /\ (3 <= h -> h = 1 + a + e).

  Fact LR2_condition_2_eq a b c : LR2_condition_2 a b c 
                              <-> (a <= c /\ b <= c <= 1)
                               \/ (a <= 1 /\ b <= 1 /\ 1 <= a+b <= c /\ c = 2)
                               \/ (3 <= c /\ c = 1+a+b).
  Proof. unfold LR2_condition_2; omega. Qed. 

  Fact LR2_condition_2_eq' a b c : LR2_condition_2 a b (1+c) <-> LR2c_2 a b c.
  Proof. unfold LR2_condition_2, LR2c_2; omega. Qed. 

  (* Proofs for the lazy mathematician ... thank you omega *)

  Fact LR2_c1_contract a e h h' :
       LR2_condition_1 a e h 
    -> 1 <= h' <= h 
    -> exists a' e', LR2_condition_1 a' e' h'
                  /\ nat_contract a a'
                  /\ nat_contract e e'.
  Proof.
    unfold LR2_condition_1, nat_contract.
    intros H1 H2.
    destruct (le_lt_dec h' 1).
    
    apply proj2 in H1.
    destruct a; destruct e; try (exfalso; omega); clear H1.
    exists 0, 1; omega.
    exists 1, 0; omega.
    exists 1, 1; omega.
    
    do 2 apply proj2 in H1.
    destruct (@part_eq_SS h' a e) as (a' & e' & ? & ? & ? & ? & ?).
    omega.
    exists a', e'; omega.
  Qed.

  Fact LR2_c2_contract a e h h' :
       LR2_condition_2 a e h 
    -> 1 <= h' <= h 
    -> exists a' e', LR2_condition_2 a' e' h'
                  /\ nat_contract a a'
                  /\ nat_contract e e'.
  Proof.
    unfold LR2_condition_2, nat_contract.
    intros [ _ H1 ] H2.
    destruct (le_lt_dec h' 2).
    
    assert (h' = 1 \/ h' = 2) as H3 by omega.
    destruct a; destruct e.
    destruct H3.
    clear H1; exists 0, 0; omega.
    exfalso; omega.
    clear H1; exists 0, 1; omega.
    clear H1; exists 1, 0; omega.
    clear H1; exists 1, 1; omega.
    
    do 2 apply proj2 in H1.
    destruct (@part_eq_SS (h'-1) a e) as (a' & e' & ? & ? & ? & ? & ?).
    omega.
    exists a', e'; omega.
  Qed.

  Definition LR2_condition x (ga de th : list X) :=
       (forall d, d <> x -> LR2_condition_1 (occ d ga) (occ d de) (occ d th))
    /\                      LR2_condition_2 (occ x ga) (occ x de) (occ x th).

  Definition LR2c x ga de th :=
       (forall d, d <> x -> LR2c_1 (occ d ga) (occ d de) (occ d th))
    /\                      LR2c_2 (occ x ga) (occ x de) (occ x th).

  Fact LR2_condition_LR2c x ga de th : LR2_condition x ga de (x::th) <-> LR2c x ga de th.
  Proof.
    split; intros [ H1 H2 ]; split.
    2,4: revert H2; rewrite occ_eq; apply LR2_condition_2_eq'.
    1,2: intros d Hd; generalize (H1 _ Hd); rewrite occ_neq; auto; apply LR2_condition_1_eq.
  Qed.
   
  Fact LR2_condition_prop1 x ga de th : LR2_condition x ga de th -> incl ga (x::th).
  Proof.
    intros H1 y.
    do 2 rewrite in_occ_neq0 with (eqX_dec := eqX_dec).
    destruct (eqX_dec y x) as [ | D ].
    subst y; generalize (proj2 H1); rewrite occ_eq; omega.
    generalize (proj1 H1 _ D); rewrite occ_neq; auto. 
    intros (H & _); omega.
  Qed.

  Fact LR2c_prop1 x ga de th : LR2c x ga de th -> incl ga (x::th).
  Proof.
    intros H.
    apply LR2_condition_LR2c, LR2_condition_prop1 in H.
    intros y Hy; apply H in Hy; revert Hy; simpl; tauto.
  Qed.
  
  Fact LR2_condition_prop2 x ga de th : LR2_condition x ga de th -> incl de (x::th).
  Proof.
    intros H1 y.
    do 2 rewrite in_occ_neq0 with (eqX_dec := eqX_dec).
    destruct (eqX_dec y x) as [ | D ].
    subst y; generalize (proj2 H1); rewrite occ_eq; omega.
    generalize (proj1 H1 _ D); rewrite occ_neq; auto. 
    intros (H & _); omega.
  Qed.

  Fact LR2c_prop2 x ga de th : LR2c x ga de th -> incl de (x::th).
  Proof.
    intros H.
    apply LR2_condition_LR2c, LR2_condition_prop2 in H.
    intros y Hy; apply H in Hy; revert Hy; simpl; tauto.
  Qed.
  
  (* Rule LR2_imp_l is a composition of LR1_imp_l with contracttion *)

  Fact LR2_condition_contract x ga de th : 
       LR2_condition x ga de (x::th) -> x::ga++de c>> x::th.
  Proof.
    intros H1 y.
    destruct (eqX_dec y x) as [ | D ].
    subst y; generalize (proj2 H1).
    repeat rewrite occ_eq. 
    rewrite occ_app.
    generalize (occ x ga) (occ x de) (occ x th).
    intros a b c; unfold LR2_condition_2, nat_contract; omega.
    generalize (proj1 H1 _ D).
    repeat rewrite occ_neq; auto.
    rewrite occ_app.
    generalize (occ y ga) (occ y de) (occ y th).
    intros a b c; unfold LR2_condition_1, nat_contract; omega.
  Qed.

  Fact LR2c_contract x ga de th : 
       LR2c x ga de th -> x::ga++de c>> x::th.
  Proof.
    intro; apply LR2_condition_contract,  LR2_condition_LR2c; auto.
  Qed.

  Fact LR2_condition_2contract_1 x ga de th : 
       LR2_condition x ga de th -> forall y, occ y ga <= 2 * occ y th.
  Proof.
    intros [ H1 H2 ] y.
    destruct (eqX_dec y x) as [ | Hy ].
    subst y; clear H1; red in H2; omega.
    clear H2; specialize (H1 _ Hy); red in H1; omega.
  Qed.

  Fact LR2_condition_2contract_2 x ga de th : 
       LR2_condition x ga de th -> forall y, occ y de <= 2 * occ y th.
  Proof.
    intros [ H1 H2 ] y.
    destruct (eqX_dec y x) as [ | Hy ].
    subst y; clear H1; red in H2; omega.
    clear H2; specialize (H1 _ Hy); red in H1; omega.
  Qed.
 
  Fact LR2_condition_perm_1 x ga ga' de th : 
       ga ~p ga' 
    -> LR2_condition x ga de th 
    -> LR2_condition x ga' de th.
  Proof.
    intros H1 [ H2 H3 ]; split; [ intros d Hd; specialize (H2 _ Hd) | ];
    rewrite <- occ_perm with (1 := H1); auto.
  Qed.
  
  Fact LR2_condition_perm_2 x ga de de' th : 
       de ~p de' 
    -> LR2_condition x ga de th 
    -> LR2_condition x ga de' th.
  Proof.
    intros H1 [ H2 H3 ]; split; [ intros d Hd; specialize (H2 _ Hd) | ];
    rewrite <- occ_perm with (1 := H1); auto.
  Qed.
  
  Fact LR2_condition_perm_3 x ga de th th' : 
       th ~p th' 
    -> LR2_condition x ga de th 
    -> LR2_condition x ga de th'.
  Proof.
    intros H1 [ H2 H3 ]; split; [ intros d Hd; specialize (H2 _ Hd) | ];
    rewrite <- occ_perm with (1 := H1); auto.
  Qed.

  Fact LR2c_perm_1 x ga ga' de th : 
       ga ~p ga' 
    -> LR2c x ga de th 
    -> LR2c x ga' de th.
  Proof.
    intro; do 2 rewrite <- LR2_condition_LR2c.
    apply LR2_condition_perm_1; auto.
  Qed.

  Fact LR2c_perm_2 x ga de de' th : 
       de ~p de' 
    -> LR2c x ga de th 
    -> LR2c x ga de' th.
  Proof.
    intro; do 2 rewrite <- LR2_condition_LR2c.
    apply LR2_condition_perm_2; auto.
  Qed.

  Fact LR2c_perm_3 x ga de th th' : 
       th ~p th' 
    -> LR2c x ga de th 
    -> LR2c x ga de th'.
  Proof.
    intro; do 2 rewrite <- LR2_condition_LR2c.
    apply LR2_condition_perm_3; constructor; auto.
  Qed.

  Hint Resolve list_contract_refl.

  Theorem LR2_condition_cntr x y ga de th :
                              LR2_condition x ga de   (y::y::th)
           -> exists ga' de', LR2_condition x ga' de' (y::th) 
                           /\ ga c>> ga' /\ de c>> de'.
  Proof.
    intros H.
    destruct (occ_destruct eqX_dec y ga) as (la & Hla1 & Hla).
    destruct (occ_destruct eqX_dec y de) as (le & Hle1 & Hle).
    destruct (occ_destruct eqX_dec y th) as (lh & Hlh1 & Hlh).
    apply LR2_condition_perm_1 with (1 := Hla1) in H.
    apply LR2_condition_perm_2 with (1 := Hle1) in H.
    apply LR2_condition_perm_3 with (1 := perm_skip y (perm_skip y Hlh1)) in H.
    revert H Hla1 Hle1 Hlh1.
    generalize (occ y ga) (occ y de) (occ y th). 
    intros na ne nh H Hla1 Hle1 Hlh1.
    destruct (eqX_dec y x) as [ | D ]; [ subst | ].
    + destruct H as (H1 & H2).
      repeat rewrite occ_eq in H2.
      repeat rewrite occ_app in H2.
      repeat rewrite occ_repeat_eq in H2.
      rewrite Hlh, Hle, Hla in H2.
      repeat rewrite Nat.add_0_r in H2.
      destruct LR2_c2_contract with (h' := S nh) (1 := H2)
        as (na' & ne' & H3 & H4 & H5); try omega.
      exists (list_repeat x na'++la), (list_repeat x ne'++le); split.
      * apply LR2_condition_perm_3 with (1 := Permutation_sym (perm_skip _ Hlh1)). 
        split.
        - intros d Hd; specialize (H1 _ Hd); revert H1.
          repeat rewrite occ_neq; auto.
          repeat rewrite occ_app.
          repeat rewrite occ_repeat_neq; auto.
        - revert H3.
          repeat rewrite occ_eq; auto.
          repeat rewrite occ_app.
          repeat rewrite occ_repeat_eq; auto.
          rewrite Hlh, Hle, Hla.
          repeat rewrite Nat.add_0_r; auto.
      * split.
        - apply list_contract_perm with (1 := Permutation_sym Hla1) (2 := Permutation_refl _).
          apply list_contract_app; auto.
          apply list_repeat_contract; auto.
        - apply list_contract_perm with (1 := Permutation_sym Hle1) (2 := Permutation_refl _).
          apply list_contract_app; auto.
          apply list_repeat_contract; auto.
    + destruct H as (H1 & H2).
      do 2 rewrite occ_neq in H2; auto.
      repeat rewrite occ_app in H2.
      do 3 rewrite occ_repeat_neq in H2; auto.
      simpl in H2.
      generalize (H1 _ D); intros H3.
      do 2 rewrite occ_eq in H3.
      repeat rewrite occ_app in H3.
      do 3 rewrite occ_repeat_eq in H3.
      rewrite Hlh, Hle, Hla in H3.
      repeat rewrite Nat.add_0_r in H3.
      destruct LR2_c1_contract with (h' := S nh) (1 := H3)
        as (na' & ne' & H4 & H5 & H6); try omega.
      exists (list_repeat y na'++la), (list_repeat y ne'++le); split.
      * apply LR2_condition_perm_3 with (1 := Permutation_sym (perm_skip _ Hlh1)). 
        split.
        - intros d Hd; destruct (eqX_dec d y) as [ ? | D1 ]; subst.
          ** repeat rewrite occ_eq.
             repeat rewrite occ_app.
             repeat rewrite occ_repeat_eq.
             rewrite Hlh, Hle, Hla.
             repeat rewrite Nat.add_0_r; auto.
          ** generalize (H1 _ Hd).
             repeat rewrite occ_neq; auto.
             repeat rewrite occ_app.
             repeat rewrite occ_repeat_neq; auto.
        - repeat rewrite occ_neq; auto.
          repeat rewrite occ_app.
          repeat rewrite occ_repeat_neq; auto.
      * split.
        - apply list_contract_perm with (1 := Permutation_sym Hla1) (2 := Permutation_refl _).
          apply list_contract_app; auto.
          apply list_repeat_contract; auto.
        - apply list_contract_perm with (1 := Permutation_sym Hle1) (2 := Permutation_refl _).
          apply list_contract_app; auto.
          apply list_repeat_contract; auto.
  Qed.

  (* Every contraction is a sequence of individual contractions
     of the components *)

  Hint Resolve list_contract_refl.

  Theorem LR2_cond_list_contract x ga de th th' :
       LR2_condition x ga de th
    -> th c>> th'
    -> exists ga' de', LR2_condition x ga' de' th'
                    /\ ga c>> ga' /\ de c>> de'.
  Proof.
    intros H1 H2.
    revert H2 x ga de H1.
    induction 1 as [ th th' H2 | y th | th1 th2 th3 IH1 IH2 ] using list_contract_one_rect;
      intros x ga de H1.
    + exists ga, de; split; auto.
      revert H1; apply LR2_condition_perm_3; auto.
    + apply LR2_condition_cntr with (1 := H1).
    + destruct (IH1 _ _ _ H1) as (ga1 & de1 & H2 & H3 & H4).
      destruct (IH2 _ _ _ H2) as (ga2 & de2 & ? & ? & ?).
      exists ga2, de2; split; auto; split.
      - apply list_contract_trans with (1 := H3); auto.
      - apply list_contract_trans with (1 := H4); auto.
  Qed.

  (* This is the instance of contraction with is needed for the proof of Curry's Lemma *)
  
  Lemma LR2c_contract_cons ga de th x l : 
        LR2c x ga de th
     -> x :: th c>> l
     -> exists ga' de' th', LR2c x ga' de' th' 
                         /\ ga c>> ga'
                         /\ de c>> de'
                         /\ l ~p x :: th'.
  Proof.
    intros H1 H2.
    rewrite <- LR2_condition_LR2c in H1.
    destruct (LR2_cond_list_contract H1 H2) as (ga' & de' & H3 & H4 & H5).
    destruct list_contract_one_perm with (1 := H2) as (l' & Hl').
    exists ga', de', l'; split; auto.
    rewrite <- LR2_condition_LR2c.
    revert H3; apply LR2_condition_perm_3; auto.
  Qed.
  
  Local Fact forall_split K (P Q : K -> Prop) :
               (forall x, P x \/ ~ P x) 
            -> (forall x, Q x) <-> (forall x, P x -> Q x)
                                /\ (forall x, ~ P x -> Q x).
  Proof.
    intros H; split.
    intros H1; split; intros ? ?; apply H1.
    intros (H1 & H2) x.
    destruct (H x).
    apply H1; auto.
    apply H2; auto.
  Qed.
  
  Local Fact forall_split_dec K (P Q : K -> Prop) :
               (forall x, P x \/ ~ P x) 
            -> { forall x, P x -> Q x } + { ~ forall x, P x -> Q x }
            -> (forall x, ~ P x -> Q x)
            -> { forall x, Q x } + { ~ forall x, Q x }.
  Proof.
    intros H1 [ H2 | H2 ] H3.
    left; apply forall_split with (1 := H1); auto.
    right; contradict H2; intros ? ?; auto.
  Qed.
  
  Fact forall_finite_t_decide K (P Q : K -> Prop) :
      finite_t P -> (forall x, P x -> { Q x } + { ~ Q x }) -> { forall x, P x -> Q x } + { ~ forall x, P x -> Q x }.
  Proof.
    intros H1 H2.
    destruct (finite_t_decide _ _ H1 H2) as [ (x & H3 & H4) | ].
    right; contradict H4; auto.
    left; auto.
  Qed.

  Section LR2_cond_dec.

    Local Fact or_dec (A B : Prop) : { A } + { ~ A } -> { B } + { ~ B } -> { A \/ B } + { ~ (A \/ B) }.
    Proof.
      intros [ ? | ? ] [ ? | ? ]; tauto.
    Qed.

    Local Fact and_dec (A B : Prop) : { A } + { ~ A } -> { B } + { ~ B } -> { A /\ B } + { ~ (A /\ B) }.
    Proof.
      intros [ ? | ? ] [ ? | ? ]; tauto.
    Qed.
  
    Local Fact imp_dec (A B : Prop) : { A } + { ~ A } -> { B } + { ~ B } -> { A -> B } + { ~ (A -> B) }.
    Proof.
      intros [ ? | ? ] [ ? | ? ]; tauto.
    Qed.
  
    Local Fact iff_dec (A B : Prop) : { A } + { ~ A } -> { B } + { ~ B } -> { A <-> B } + { ~ (A <-> B) }.
    Proof.
      intros [ ? | ? ] [ ? | ? ]; tauto.
    Qed.
  
    Local Fact neqX_dec (x y : X) : { x <> y } + { ~ x <> y }.
    Proof.
      destruct (eqX_dec x y); [ right | left ]; tauto.
    Qed.
  
    Ltac trydec :=
    repeat match goal with 
      | |- { _ = _ :> nat } + { _ } => apply eq_nat_dec
      | |- { _ <= _ } + { ~ ( _ <= _ ) } => apply le_dec 
      | |- { _ <> _ } + { ~ ( _ <> _) } => apply neqX_dec
      | |- { ?a /\ ?b } + { ~ (?a /\ ?b) } => apply and_dec
      | |- { ?a \/ ?b } + { ~ (?a \/ ?b) } => apply or_dec
      | |- { ?a -> ?b } + { ~ (?a -> ?b) } => apply imp_dec
      | |- { ?a <-> ?b } + { ~ (?a <-> ?b) } => apply iff_dec
    end.
    
    Fact LR2_condition_dec x ga de th : { LR2_condition x ga de th } + { ~ LR2_condition x ga de th }.
    Proof.
      unfold LR2_condition, LR2_condition_1, LR2_condition_2.
      apply and_dec.
      apply forall_split_dec with (P := fun x => In x (ga++de++th)).
      intros y; destruct (in_dec eqX_dec y (ga++de++th)); [ left | right ]; auto.
      apply forall_finite_t_decide.
      exists (ga++de++th); split; auto.
      intros y _; trydec.
      intros y Hy; split.
      split; apply not_in_occ_0; contradict Hy.
      apply in_or_app; left; auto.
      apply in_or_app; right; auto.
      apply in_or_app; left; auto.
      split.
      intros ?; contradict Hy.
      apply in_or_app; right.
      apply in_or_app; right.
      apply in_occ_neq0 with eqX_dec; omega.
      intros ?; contradict Hy.
      apply in_or_app; right.
      apply in_or_app; right.
      apply in_occ_neq0 with eqX_dec; omega.
      trydec.
    Qed.

    Fact LR2c_dec x ga de th : { LR2c x ga de th } + { ~ LR2c x ga de th }.
    Proof.
      destruct (LR2_condition_dec x ga de (x::th)); [ left | right ];
        rewrite <- LR2_condition_LR2c; auto.
    Qed.

  End LR2_cond_dec.
  
  Fact LR2_condition_finite_t x th : finite_t (fun p : _ * _ => let (ga, de) := p in LR2_condition x ga de th).
  Proof.
    generalize (subset_finite_t (th++th)); intros H2th.
    generalize (finite_t_product H2th H2th); intros H.
    destruct (finite_t_cap_dec (fun u : _ * _ => let (ga,de) := u in LR2_condition x ga de th) H) as (ll & Hll).
    intros (?&?); apply LR2_condition_dec.
    exists ll.
    intros (ga,de); rewrite Hll; simpl.
    split; try tauto.
    clear H H2th ll Hll.
    intros H; split; auto.
    split; simpl.
    generalize (LR2_condition_2contract_1 H).
    intros H1; apply occ_subset with eqX_dec.
    intros d; generalize (H1 d); rewrite occ_app; omega.
    generalize (LR2_condition_2contract_2 H).
    intros H1; apply occ_subset with eqX_dec.
    intros d; generalize (H1 d); rewrite occ_app; omega.
  Qed.

  Lemma LR2c_finite_t x th : finite_t (fun p : _ * _ => let (ga, de) := p in LR2c x ga de th).
  Proof.
    apply finite_t_eq with (2 := LR2_condition_finite_t x (x::th)).
    split; intros []; apply LR2_condition_LR2c.
  Qed.

End Relevant.
