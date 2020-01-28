(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Permutation.

Require Import tacs rel_utils list_utils.
Require Import finite.

Require Import tree proof.

(* Require Import list_contract. *)

Require Import formula sequent_rules.

Set Implicit Arguments.

Local Notation " g '|--' a " := ((g,a):Seq) (at level 70, no associativity).
Local Notation " l ≻c m " := (list_contract Form_eq_dec l m) (at level 70, no associativity).

Local Notation sf := LR_sf.

Section LI2.

 (* The LI2 system *)
  
  Definition LI2_rules := rule_ax cup2 LR_rule_r cup2 LI2_rule_l.
  
  Fact LI2_rules_reif c h : LI2_rules c h -> { rule_ax    c h }
                                           + { LR_rule_r  c h }
                                           + { LI2_rule_l c h }.
  Proof.
    unfold LI2_rules;
    destruct (rule_ax_dec c h);
    destruct (LR_rule_r_dec c h);
    destruct (LI2_rule_l_dec c h);
    tauto.
  Qed.
  
  Hint Resolve sf_rule_ax sf_LR_rule_r sf_LI2_rule_l : core.
  
  Fact sf_LI2_rules c ll : LI2_rules c ll -> Forall (sf c) ll.
  Proof. intros [[|]|]; auto. Qed.
  
  Hint Resolve rule_ax_finite_t LR_rule_r_finite_t LI2_rule_l_finite_t : core.
  
  Fact LI2_rules_finite_t c : finite_t (LI2_rules c).
  Proof. unfold LI2_rules; repeat apply finite_t_cup; auto. Qed.
  
  Definition LI2_bproof := bproof LI2_rules.

  Definition LI2_bprovable n s := exists t, LI2_bproof n s t.
  Definition LI2_proof s := { n : _ & { t | LI2_bproof n s t } }.
  
  Fact LI2_bprovable_mono n m : n <= m -> LI2_bprovable n inc1 LI2_bprovable m.
  Proof.
    intros H s (t & Ht); exists t; revert Ht. 
    apply bproof_mono; auto.
  Qed.
  
  Fact LI2_b_ax n l a r : LI2_bprovable (S n) (l ++ a :: r |-- a).
  Proof.
    exists (in_tree ( (l ++ a :: r) |-- a ) nil).
    apply rules_ax.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LI2_ax l a r : LI2_proof (l ++ a :: r |-- a).
  Proof.
    exists 1, (in_tree ( (l ++ a :: r) |-- a ) nil).
    apply rules_ax.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LI2_b_imp_r n ga a b :  LI2_bprovable n (a::ga |-- b) 
                            -> LI2_bprovable (S n) (ga |-- a %> b).
  Proof.
    intros (t & H).
    exists (in_tree (ga |-- a %> b) (t::nil)).
    apply LR_rules_imp_r; auto.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LI2_imp_r ga a b : LI2_proof (a::ga |-- b) 
                       -> LI2_proof (ga |-- a %> b).
  Proof.
    intros (n & t & H).
    exists (S n), (in_tree (ga |-- a %> b) (t::nil)).
    apply LR_rules_imp_r; auto.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LI2_b_imp_l n ga th a b d : 
        th ~p (a %> b) :: ga
     -> LI2_bprovable n (a %> b :: b::ga |-- d)
     -> LI2_bprovable n (a %> b :: ga |-- a)
     -> LI2_bprovable (S n) (th |-- d).
  Proof.
    intros H1 (td & Htd) (tg & Htg).
    exists (in_tree (th |-- d) (tg :: td :: nil)).
    apply LI2_rules_imp_l with ga a b; auto.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LR2_imp_l ga th a b d : 
        th ~p (a %> b) :: ga
     -> LI2_proof (a %> b :: b::ga |-- d)
     -> LI2_proof (a %> b :: ga |-- a)
     -> LI2_proof (th |-- d).
  Proof.
    intros H1 (nd & td & Htd) (ng & tg & Htg).
    exists (S (max ng nd)), (in_tree (th |-- d) (tg :: td :: nil)).
    apply LI2_rules_imp_l with ga a b; auto.
    intros ? ?; cbv; tauto.
    revert Htg; apply bproof_mono, le_max_l.
    revert Htd; apply bproof_mono, le_max_r.
  Qed.
  
  Section LI2_bproof_rect.

    Variable P : nat -> Seq -> Type.

    Hypothesis HP1 : forall n ga A de, P (S n) (ga ++ A :: de |-- A).

    Hypothesis HP2 : forall n ga A B,   P n (A :: ga |-- B) 
                                     -> P (S n) (ga |-- A %> B).

    Hypothesis HP3 : forall n ga th A B C,
                                        th ~p (A %> B) :: ga
                                     -> P n (A %> B :: ga |-- A)
                                     -> P n (A %> B :: B :: ga |-- C)
                                     -> P (S n) (th |-- C).

    Theorem LI2_bproof_rect n s t : LI2_bproof n s t -> P n s.
    Proof.
      induction 1 as [ n x ll tt H2 H3 H4 ] using bproof_rect.
      
      apply LI2_rules_reif in H2.
      destruct H2 as [ [ H2 | H2 ] | H2 ].
      
      apply rule_ax_reif in H2.
      destruct H2 as (((l,a),r) & Ha).
      simpl in Ha; inversion Ha; subst x ll; apply HP1.
      
      apply LR_rule_r_reif in H2.
      destruct H2 as ( ((ga,a),b) & E).
      cbv in E; inversion E; subst x ll; apply HP2.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (t' & mm & H3 & H5 & H6).
      apply Forall2_nil_inv_l in H6; subst mm.
      apply H4 with t'; auto.
      
      apply LI2_rule_l_reif in H2.
      destruct H2 as ( (((((ga,th),a),b),d) & H1) & E).
      simpl in E; inversion E; subst x ll; clear E.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (ta & mma & H3 & H5 & H6).
      apply Forall2_cons_inv_l in H6.
      destruct H6 as (tb & mmb & H6 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst mmb.
      subst.
      apply HP3 with ga a b; auto.
      apply H4 with ta; auto.
      apply H4 with tb; auto.
    Qed.
    
  End LI2_bproof_rect.
  
  Section LI2_bprovable_ind.
   
    Variable P : nat -> Seq -> Prop.
    
    Hypothesis HP1 : forall n ga a de, P (S n) (ga ++ a :: de |-- a).
                                     
    Hypothesis HP2 : forall n ga a b,  P n (a :: ga|-- b)
                                    -> P (S n) (ga |-- a %> b).
                                     
    Hypothesis HP3 : forall n ga th a b x,
                                        th ~p (a %> b) :: ga
                                     -> P n (a %> b :: ga |-- a)
                                     -> P n (a %> b :: b :: ga |-- x)
                                     -> P (S n) (th |-- x).

    Theorem LI2_bprovable_ind n c : LI2_bprovable n c -> P n c.
    Proof.
      intros (t & Ht); revert n c t Ht.
      apply LI2_bproof_rect; auto.
    Qed.
    
  End LI2_bprovable_ind.
  
  Section LI2_proof_rect.

    Variable P : Seq -> Type.

    Hypothesis HP1 : forall ga A de, P (ga ++ A :: de |-- A).

    Hypothesis HP2 : forall ga A B,     P (A :: ga |-- B) 
                                     -> P (ga |-- A %> B).

    Hypothesis HP3 : forall ga th A B C,
                                        th ~p (A %> B) :: ga
                                     -> P (A %> B :: ga |-- A)
                                     -> P (A %> B :: B :: ga |-- C)
                                     -> P (th |-- C).
    
    Theorem LI2_proof_rect s : LI2_proof s -> P s.
    Proof.
      intros (n & t & Ht); revert Ht.
      apply LI2_bproof_rect with (P := fun _ s => P s) (n := n); auto.
    Qed.

  End LI2_proof_rect.

  Notation Seq_incl := (fun s1 s2 : Seq =>
    match s1, s2 with
      | (l1,c1),(l2,c2) => c1 = c2 /\ incl l1 l2
    end).
 
  Lemma LI2_incl n l1 l2 a : 
         incl l1 l2 -> LI2_bprovable n (l1 |-- a) -> LI2_bprovable n (l2 |-- a).
  Proof.
    intros H.
    assert (Seq_incl (l1 |-- a) (l2 |-- a)) as G.
      split; auto.
    clear H; intros H; revert H G.
    generalize (l1 |-- a) (l2 |-- a); clear l1 l2 a.
    intros s1 s2 H; revert H s2.
    
    induction 1 as [ n l a r 
                   | n ga a b H2 
                   | n ga th a b x H1 H2 H3 ]
      using LI2_bprovable_ind; intros s2 Hs2.
      
    (* The axiom rule *)
    
    destruct s2 as (l' & b).
    destruct Hs2 as (? & Hs2); subst b.
    destruct (in_split a l') as (l1 & r1 & Hl'); subst.
    apply Hs2, in_or_app; right; left; auto.
    apply LI2_b_ax.
    
    (* The right implication rule *)
    
    destruct s2 as (l & x).
    destruct Hs2 as (? & Hs2); subst x.
    apply LI2_b_imp_r.
    apply H2; split; auto.
    intros d [ Hd | Hd ]; subst; [ left | right ]; auto.
      
    (* The left implication rule *)
    
    destruct s2 as (l & y).
    destruct Hs2 as (? & Hs2); subst y.
    destruct (perm_in_head (a %> b) l) as (l' & Hl').
    apply Hs2, Permutation_in with (1 := Permutation_sym H1); left; auto.
    apply LI2_b_imp_l with l' a b; auto.
    
    apply H3; split; auto.
    intros d [ Hd | [ Hd | Hd ] ]; subst.
    left; auto.
    right; left; auto.
    specialize (Hs2 d).
    spec_all Hs2.
    apply Permutation_in with (1 := Permutation_sym H1); right; auto.
    apply Permutation_in with (1 := Hl') in Hs2.
    revert Hs2; simpl; tauto.
    
    apply H2; split; auto.
    intros d Hd.
    apply Permutation_in with (1 := Hl'), Hs2,
          Permutation_in with (1 := Permutation_sym H1), Hd.
  Qed.

  Corollary LI2_contract n l1 l2 a : 
      l1 ≻c l2 -> LI2_bprovable n (l1 |-- a) -> LI2_bprovable n (l2 |-- a).
  Proof.
    intro; apply LI2_incl.
    revert H; apply list_contract_incl.
  Qed.
  
  Corollary LR2_perm n l1 l2 a : 
      l1 ~p l2 -> LI2_bprovable n (l1 |-- a) -> LI2_bprovable n (l2 |-- a).
  Proof.
    intros H; apply LI2_contract; revert H.
    apply perm_list_contract.
  Qed.
  
End LI2.

