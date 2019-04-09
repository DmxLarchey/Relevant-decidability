(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Permutation.

Require Import tacs rel_utils list_utils finite.

Require Import tree proof.

Require Import formula sequent_rules relevant_contract.

Set Implicit Arguments.

Local Notation " g '|--' a " := ((g,a):Seq) (at level 70, no associativity).
Local Notation " l 'c>>' m " := (list_contract Form_eq_dec l m) (at level 70, no associativity).

Local Notation sf := LR_sf.
Local Notation LR2c := (LR2c Form_eq_dec).

Section LR2.

 (* The LR2 system *)
  
  Definition LR2_rules := rule_id cup2 LR_rule_r cup2 LR2_rule_l.
  
  Fact LR2_rules_reif c h : LR2_rules c h -> { rule_id c h }
                                           + { LR_rule_r  c h }
                                           + { LR2_rule_l c h }.
  Proof.
    unfold LR2_rules;
    destruct (rule_id_dec c h);
    destruct (LR_rule_r_dec c h);
    destruct (LR2_rule_l_dec c h);
    tauto.
  Qed.
  
  Hint Resolve sf_rule_id sf_LR_rule_r sf_LR2_rule_l.
  
  Fact sf_LR2_rules c ll : LR2_rules c ll -> Forall (sf c) ll.
  Proof. intros [[|]|]; auto. Qed.
  
  Hint Resolve rule_id_finite_t LR_rule_r_finite_t LR2_rule_l_finite_t.
  
  Lemma LR2_rules_finite_t c : finite_t (LR2_rules c).
  Proof. unfold LR2_rules; repeat apply finite_t_cup; auto. Qed.
  
  Definition LR2_bproof := bproof LR2_rules.

  Definition LR2_bprovable n s := exists t, LR2_bproof n s t.
  Definition LR2_proof s := { n : _ & { t | LR2_bproof n s t } }.
  
  Fact LR2_bprovable_mono n m : n <= m -> LR2_bprovable n inc1 LR2_bprovable m.
  Proof.
    intros H s (t & Ht); exists t; revert Ht. 
    apply bproof_mono; auto.
  Qed.
  
  Fact LR2_b_id n a : LR2_bprovable (S n) (a :: nil |-- a).
  Proof.
    exists (in_tree ( (a :: nil) |-- a ) nil).
    apply rules_id.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LR2_id a : LR2_proof (a :: nil |-- a).
  Proof.
    exists 1, (in_tree ( (a :: nil) |-- a ) nil).
    apply rules_id.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LR2_b_imp_r n ga a b :  LR2_bprovable n (a::ga |-- b) 
                            -> LR2_bprovable (S n) (ga |-- a %> b).
  Proof.
    intros (t & H).
    exists (in_tree (ga |-- a %> b) (t::nil)).
    apply LR_rules_imp_r; auto.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LR2_imp_r ga a b : LR2_proof (a::ga |-- b) 
                       -> LR2_proof (ga |-- a %> b).
  Proof.
    intros (n & t & H).
    exists (S n), (in_tree (ga |-- a %> b) (t::nil)).
    apply LR_rules_imp_r; auto.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LR2_b_imp_l n ga de th th' a b d : 
        th ~p (a %> b) :: th'
     -> LR2c (a %> b) ga de th'
     -> LR2_bprovable n (b::de |-- d)
     -> LR2_bprovable n (ga |-- a)
     -> LR2_bprovable (S n) (th |-- d).
  Proof.
    intros H1 H2 (td & Htd) (tg & Htg).
    exists (in_tree (th |-- d) (tg :: td :: nil)).
    apply LR2_rules_imp_l with ga de th' a b; auto.
    intros ? ?; cbv; tauto.
  Qed.
  
  Fact LR2_imp_l ga de th th' a b d : 
        th ~p (a %> b) :: th'
     -> LR2c (a %> b) ga de th'
     -> LR2_proof (b::de |-- d)
     -> LR2_proof (ga |-- a)
     -> LR2_proof (th |-- d).
  Proof.
    intros H1 H2 (nd & td & Htd) (ng & tg & Htg).
    exists (S (max ng nd)), (in_tree (th |-- d) (tg :: td :: nil)).
    apply LR2_rules_imp_l with ga de th' a b; auto.
    intros ? ?; cbv; tauto.
    revert Htg; apply bproof_mono, le_max_l.
    revert Htd; apply bproof_mono, le_max_r.
  Qed.
  
  Section LR2_bproof_rect.

    Variable P : nat -> Seq -> Type.

    Hypothesis HP1 : forall n A, P (S n) (A :: nil |-- A).

    Hypothesis HP2 : forall n ga A B,   P n (A :: ga |-- B) 
                                     -> P (S n) (ga |-- A %> B).

    Hypothesis HP3 : forall n ga de th th' A B C,
                                        th ~p (A %> B) :: th'
                                     -> LR2c (A %> B) ga de th'
                                     -> P n (ga |-- A)
                                     -> P n (B :: de |-- C)
                                     -> P (S n) (th |-- C).

    Theorem LR2_bproof_rect n s t : LR2_bproof n s t -> P n s.
    Proof.
      induction 1 as [ n x ll tt H2 H3 H4 ] using bproof_rect.
      
      apply LR2_rules_reif in H2.
      destruct H2 as [ [ H2 | H2 ] | H2 ].
      
      apply rule_id_reif in H2.
      destruct H2 as (a & Ha); cbv in Ha.
      inversion Ha; subst x ll; apply HP1.
      
      apply LR_rule_r_reif in H2.
      destruct H2 as ( ((ga,a),b) & E).
      cbv in E; inversion E; subst x ll; apply HP2.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (t' & mm & H3 & H5 & H6).
      apply Forall2_nil_inv_l in H6; subst mm.
      apply H4 with t'; auto.
      
      apply LR2_rule_l_reif in H2.
      destruct H2 as ( (((((((ga,de),th),th'),a),b),d) & H1 & H2) & E).
      cbv in E; inversion E; subst x ll; clear E.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (ta & mma & H3 & H5 & H6).
      apply Forall2_cons_inv_l in H6.
      destruct H6 as (tb & mmb & H6 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst mmb.
      subst.
      apply HP3 with ga de th' a b; auto.
      apply H4 with ta; auto.
      apply H4 with tb; auto.
    Qed.
    
  End LR2_bproof_rect.
  
  Section LR2_bprovable_ind.
   
    Variable P : nat -> Seq -> Prop.
    
    Hypothesis HP1 : forall n a, P (S n) (a::nil |-- a).
                                     
    Hypothesis HP2 : forall n ga a b,  P n (a :: ga|-- b)
                                    -> P (S n) (ga |-- a %> b).
                                     
    Hypothesis HP3 : forall n ga de th th' a b x,
                                        th ~p (a %> b) :: th'
                                     -> LR2c (a %> b) ga de th'
                                     -> P n (ga |-- a)
                                     -> P n (b::de |-- x)
                                     -> P (S n) (th |-- x).

    Theorem LR2_bprovable_ind n c : LR2_bprovable n c -> P n c.
    Proof.
      intros (t & Ht); revert n c t Ht.
      apply LR2_bproof_rect; auto.
    Qed.
    
  End LR2_bprovable_ind.
  
  Section LR2_proof_rect.

    Variable P : Seq -> Type.

    Hypothesis HP1 : forall A, P (A :: nil |-- A).

    Hypothesis HP2 : forall ga A B,     P (A :: ga |-- B) 
                                     -> P (ga |-- A %> B).

    Hypothesis HP3 : forall ga de th th' A B C,
                                        th ~p (A %> B) :: th'
                                     -> LR2c (A %> B) ga de th'
                                     -> P (ga |-- A)
                                     -> P (B :: de |-- C)
                                     -> P (th |-- C).
    
    Theorem LR2_proof_rect s : LR2_proof s -> P s.
    Proof.
      intros (n & t & Ht); revert Ht.
      apply LR2_bproof_rect with (P := fun _ s => P s) (n := n); auto.
    Qed.

  End LR2_proof_rect.

  Notation Seq_contract := (fun s1 s2 : Seq =>
    match s1, s2 with
      | (l1,c1),(l2,c2) => c1 = c2 /\ l1 c>> l2
    end).
    
  (** This one is called Curry's lemma, that is height-preserving
      admissibility of contraction *)
 
  Lemma LR2_Curry n l1 l2 a : 
         l1 c>> l2 -> LR2_bprovable n (l1 |-- a) -> LR2_bprovable n (l2 |-- a).
  Proof.
    intros H.
    assert (Seq_contract (l1 |-- a) (l2 |-- a)) as G.
      split; auto.
    clear H; intros H; revert H G.
    generalize (l1 |-- a) (l2 |-- a); clear l1 l2 a.
    intros s1 s2 H; revert H s2.
    
    induction 1 as [ n a 
                   | n ga a b H2 
                   | n ga de th th' a b x H1 H2 H3 H4 ]
      using LR2_bprovable_ind; intros s2 Hs2.
      
    (* The identity rule *)
    
    assert (s2 = (a :: nil |-- a)).
      destruct s2 as (l & b).
      destruct Hs2 as (? & Hs2); subst b; f_equal.
      revert Hs2; apply list_contract_1.
    subst; apply LR2_b_id.
    
    (* The right implication rule *)
    
    destruct s2 as (l & x).
    destruct Hs2 as (? & Hs2); subst x.
    apply LR2_b_imp_r.
    apply H2; split; auto.
    intros d.
    generalize (Hs2 d).
    simpl.
    destruct (Form_eq_dec d a); 
      unfold nat_contract; omega.
      
    (* The left implication rule *)
    
    destruct s2 as (l & y).
    destruct Hs2 as (? & Hs2); subst y.
    destruct LR2c_contract_cons with (1 := H2) (l := l)
      as (ga1 & de1 & th1 & G1 & G2 & G3 & G5).
    revert Hs2; apply list_contract_perm; auto.
    apply LR2_b_imp_l with ga1 de1 th1 a b; auto.
    apply H4; split; auto.
    apply list_contract_cons; trivial.
  Qed.
  
  Corollary LR2_perm n l1 l2 a : 
      l1 ~p l2 -> LR2_bprovable n (l1 |-- a) -> LR2_bprovable n (l2 |-- a).
  Proof.
    intros H; apply LR2_Curry; revert H.
    apply perm_list_contract.
  Qed.
  
End LR2.

