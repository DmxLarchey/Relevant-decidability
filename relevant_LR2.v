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

Local Notation " g '|--' a " := ((g,a):Seq) (at level 69, no associativity).
(* Local Notation " l 'c>>' m " := (list_contract Form_eq_dec l m) (at level 70, no associativity). *)
Local Infix "≻c" := (list_contract Form_eq_dec) (at level 70, no associativity).

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
  
  Hint Resolve sf_rule_id sf_LR_rule_r sf_LR2_rule_l : core.
  
  Fact sf_LR2_rules c ll : LR2_rules c ll -> Forall (sf c) ll.
  Proof. intros [[|]|]; auto. Qed.
  
  Hint Resolve rule_id_finite_t LR_rule_r_finite_t LR2_rule_l_finite_t : core.
  
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

  Let Seq_redundant (s1 s2 : Seq) := 
    match s1, s2 with
      | (Δ,B),(Γ,A) => A = B /\ Γ ≻c Δ
    end.

  Infix "≺r" := Seq_redundant (at level 70, no associativity).

    
  (** This one is called Curry's lemma, that is height-preserving
      admissibility of contraction *)

  (* Γ Δ Θ Σ α *)  
 
  Lemma LR2_Curry n Γ Δ A B : 
         Δ |-- B ≺r Γ |-- A 
      -> LR2_bprovable n (Γ |-- A) 
      -> LR2_bprovable n (Δ |-- B) .
  Proof.
    generalize (Δ |-- B) (Γ |-- A); intros s1 s2.
    clear Γ Δ A B; intros H1 H2; revert H2 s1 H1.
    
    induction 1 as [ n A 
                   | n Γ A B H2 
                   | n Γ Δ Θ Σ A B x H1 H2 H3 H4 ]
      using LR2_bprovable_ind; intros s2 Hs2.
      
    (* The identity rule *)
    
    assert (s2 = (A :: nil |-- A)).
      destruct s2 as (l & b).
      destruct Hs2 as (? & Hs2); subst b; f_equal.
      revert Hs2; apply list_contract_1.
    subst; apply LR2_b_id.
    
    (* The right implication rule *)
    
    destruct s2 as (Δ & x).
    destruct Hs2 as (? & Hs2); subst x.
    apply LR2_b_imp_r, H2; split; auto.
    apply list_contract_cons; auto.
      
    (* The left implication rule *)
    
    destruct s2 as (Φ & y).
    destruct Hs2 as (? & Hs2); subst y.
    destruct LR2c_contract_cons with (1 := H2) (Σ := Φ)
      as (Γ' & Δ' & Θ' & G1 & G2 & G3 & G5).
    revert Hs2; apply list_contract_perm; auto.
    apply LR2_b_imp_l with Γ' Δ' Θ' A B; auto.
    apply H4; split; auto.
    apply list_contract_cons; trivial.
    apply H3; split; auto.
  Qed.
  
  Corollary LR2_perm n Γ Δ A : 
      Γ ~p Δ -> LR2_bprovable n (Γ |-- A) -> LR2_bprovable n (Δ |-- A).
  Proof.
    intros H; apply LR2_Curry.
    split; auto; apply perm_list_contract; auto.
  Qed.
  
End LR2.

