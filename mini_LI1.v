(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max List Permutation.

Require Import tacs rel_utils list_utils.
Require Import finite.

Require Import tree proof.

Require Import list_contract formula sequent_rules.

Set Implicit Arguments.

Local Notation " g '|--' a " := ((g,a):Seq) (at level 70, no associativity).
Local Notation " l 'c>>' m " := (list_contract Form_eq_dec l m) (at level 70, no associativity).

Section LI1.

  Definition LI1_rules    :=     rule_id
                            cup2 LR_rule_r
                            cup2 LR_rule_l
                            cup2 rule_cntr
                            cup2 rule_weak.

  Definition LI1_rules_wc :=     LI1_rules
                            cup2 rule_cut.

  (* LI1 rules are decidable and thus can be reified *)

  Fact LI1_rules_reif c h : LI1_rules c h -> { rule_id   c h }
                                           + { LR_rule_r c h }
                                           + { LR_rule_l c h }
                                           + { rule_cntr c h }
                                           + { rule_weak c h }.
  Proof.
    intros H.
    unfold LI1_rules in H.
    destruct (rule_id_dec c h);
    destruct (LR_rule_r_dec c h);
    destruct (LR_rule_l_dec c h);
    destruct (rule_cntr_dec c h);
    destruct (rule_weak_dec c h); tauto.
  Qed.

  Fact LI1_rules_wc_reif c h : LI1_rules_wc c h -> { rule_id    c h }
                                                 + { LR_rule_r  c h }
                                                 + { LR_rule_l  c h }
                                                 + { rule_cntr  c h }
                                                 + { rule_weak  c h }
                                                 + { rule_cut   c h }.
  Proof.
    intros H.
    unfold LI1_rules_wc, LI1_rules in H.
    destruct (rule_id_dec c h);
    destruct (LR_rule_r_dec c h);
    destruct (LR_rule_l_dec c h);
    destruct (rule_cntr_dec c h);
    destruct (rule_weak_dec c h);
    destruct (rule_cut_dec c h); tauto.
  Qed.

  Definition LI1_cf_bprovable n s := exists t, bproof LI1_rules n s t.

  Definition LI1_proof s := { n : _ & { t | bproof LI1_rules_wc n s t } }.
  Definition LI1_cf_proof s := { n : _ & { t | bproof LI1_rules n s t } }.

  Definition LI1_provable s := inhabited (LI1_proof s).
  Definition LI1_cf_provable s := exists n t, bproof LI1_rules n s t.

  Fact LI1_rule_b_id n a : LI1_cf_bprovable (S n) (a :: nil |-- a).
  Proof.
    exists (in_tree ( (a :: nil) |-- a ) nil).
    apply rules_id.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_rule_id a : LI1_proof (a :: nil |-- a).
  Proof.
    exists 1, (in_tree ( (a :: nil) |-- a ) nil).
    apply rules_id.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_cf_provable_id a : LI1_cf_provable (a :: nil |-- a).
  Proof. exists 1; apply LI1_rule_b_id. Qed.

  Fact LI1_provable_id a : LI1_provable (a :: nil |-- a).
  Proof. exists; apply LI1_rule_id. Qed.

  Fact LI1_rule_b_r n ga a b : LI1_cf_bprovable n     (a::ga |-- b)
                            -> LI1_cf_bprovable (S n) (ga |-- a %> b).
  Proof.
    intros (t & H).
    exists (in_tree (ga |-- a %> b) (t::nil)).
    apply LR_rules_imp_r; auto.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_rule_r ga a b : LI1_proof (a::ga |-- b)
                        -> LI1_proof (ga |-- a %> b).
  Proof.
    intros (n & t & H).
    exists (S n), (in_tree (ga |-- a %> b) (t::nil)).
    apply LR_rules_imp_r; auto.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_cf_provable_r ga a b : LI1_cf_provable (a::ga |-- b)
                               -> LI1_cf_provable (ga |-- a %> b).
  Proof. intros (n & Hn); exists (S n); revert Hn; apply LI1_rule_b_r. Qed.

  Fact LI1_provable_r ga a b : LI1_provable (a::ga |-- b)
                            -> LI1_provable (ga |-- a %> b).
  Proof. intros [H]; exists; revert H; apply LI1_rule_r. Qed.

  Fact LI1_rule_b_l n ga de th a b d :
         th ~p (a %> b) :: ga ++ de
      -> LI1_cf_bprovable n (ga  |-- a)
      -> LI1_cf_bprovable n (b::de |-- d)
      -> LI1_cf_bprovable (S n) (th  |-- d).
  Proof.
    intros H1 (tg & Htg) (td & Htd).
    exists (in_tree (th |-- d) (tg :: td :: nil)).
    apply LR_rules_imp_l with ga de a b; auto.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_rule_l ga de th a b d :
         th ~p (a %> b) :: ga ++ de
      -> LI1_proof (ga  |-- a)
      -> LI1_proof (b::de |-- d)
      -> LI1_proof (th  |-- d).
  Proof.
    intros H1 (ng & tg & Htg) (nd & td & Htd).
    exists (S (max ng nd)), (in_tree (th |-- d) (tg :: td :: nil)).
    apply LR_rules_imp_l with ga de a b; auto.
    intros ? ?; cbv; tauto.
    revert Htg; apply bproof_mono, le_max_l.
    revert Htd; apply bproof_mono, le_max_r.
  Qed.

  Fact LI1_cf_provable_l ga de th a b d :
         th ~p (a %> b) :: ga ++ de
      -> LI1_cf_provable (ga  |-- a)
      -> LI1_cf_provable (b::de |-- d)
      -> LI1_cf_provable (th  |-- d).
  Proof.
    intros H1 (n & tn & Hn) (p & tp & Hp); exists (S (max n p)).
    apply LI1_rule_b_l with (1 := H1).
    exists tn; revert Hn; apply bproof_mono, le_max_l.
    exists tp; revert Hp; apply bproof_mono, le_max_r.
  Qed.

  Fact LI1_provable_l ga de th a b d :
         th ~p (a %> b) :: ga ++ de
      -> LI1_provable (ga  |-- a)
      -> LI1_provable (b::de |-- d)
      -> LI1_provable (th  |-- d).
  Proof.
    intros H1 [H2] [H3]; exists; revert H1 H2 H3; apply LI1_rule_l.
  Qed.

  Fact LI1_rule_b_cntr n ga th x a :
         ga ~p x :: th
      -> LI1_cf_bprovable n (x :: x :: th |-- a)
      -> LI1_cf_bprovable (S n) (ga |-- a).
  Proof.
    intros H2 (t & Ht).
    exists (in_tree (ga |-- a) (t::nil)).
    apply rules_cntr with th x; auto.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_rule_cntr ga th x a :
         ga ~p x :: th
      -> LI1_proof (x :: x :: th |-- a)
      -> LI1_proof (ga |-- a).
  Proof.
    intros H2 (n & t & Ht).
    exists (S n), (in_tree (ga |-- a) (t::nil)).
    apply rules_cntr with th x; auto.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_cf_provable_cntr ga th x a :
         ga ~p x :: th
      -> LI1_cf_provable (x :: x :: th |-- a)
      -> LI1_cf_provable (ga |-- a).
  Proof. intros H1 (n & Hn); exists (S n); revert Hn; apply LI1_rule_b_cntr; auto. Qed.

  Fact LI1_provable_cntr ga th x a :
         ga ~p x :: th
      -> LI1_provable (x :: x :: th |-- a)
      -> LI1_provable (ga |-- a).
  Proof.
    intros H1 [H2]; exists; revert H1 H2; apply LI1_rule_cntr.
  Qed.

  Fact LI1_rule_b_weak n ga th x a :
         ga ~p x :: th
      -> LI1_cf_bprovable n (th |-- a)
      -> LI1_cf_bprovable (S n) (ga |-- a).
  Proof.
    intros H2 (t & Ht).
    exists (in_tree (ga |-- a) (t::nil)).
    apply rules_weak with th x; auto.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_rule_weak ga th x a :
         ga ~p x :: th
      -> LI1_proof (th |-- a)
      -> LI1_proof (ga |-- a).
  Proof.
    intros H2 (n & t & Ht).
    exists (S n), (in_tree (ga |-- a) (t::nil)).
    apply rules_weak with th x; auto.
    intros ? ?; cbv; tauto.
  Qed.

  Fact LI1_cf_provable_weak ga th x a :
         ga ~p x :: th
      -> LI1_cf_provable (th |-- a)
      -> LI1_cf_provable (ga |-- a).
  Proof. intros H1 (n & Hn); exists (S n); revert Hn; apply LI1_rule_b_weak with x; auto. Qed.

  Fact LI1_provable_weak ga th x a :
         ga ~p x :: th
      -> LI1_provable (th |-- a)
      -> LI1_provable (ga |-- a).
  Proof.
    intros H1 [H2]; exists; revert H1 H2; apply LI1_rule_weak.
  Qed.

  Fact LI1_rule_cut ga de th a b :
         th ~p ga ++ de
      -> LI1_proof (ga |-- a)
      -> LI1_proof (a::de |-- b)
      -> LI1_proof (th |-- b).
  Proof.
    intros H1 (na & ta & Hta) (nd & td & Htd).
    exists (S (max na nd)), (in_tree (th |-- b) (ta::td::nil)).
    apply rules_cut with ga de a; auto.
    intros ? ?; cbv; tauto.
    revert Hta; apply bproof_mono, le_max_l.
    revert Htd; apply bproof_mono, le_max_r.
  Qed.

  Fact LI1_provable_cut ga de th a b :
         th ~p ga ++ de
      -> LI1_provable (ga |-- a)
      -> LI1_provable (a::de |-- b)
      -> LI1_provable (th |-- b).
  Proof. intros H1 [H2] [H3]; exists; revert H1 H2 H3; apply LI1_rule_cut. Qed.

  (* Induction principles for LI1 bounded proofs, LI1 proofs,
     LI1 bounded provability, LI1 provability *)

  Section LI1_bproof_rect.

    Variable P : nat -> Seq -> Type.

    Hypothesis HP1 : forall n A, P (S n) (A :: nil |-- A).

    Hypothesis HP2 : forall n ga A B,   P n (A :: ga |-- B)
                                     -> P (S n) (ga |-- A %> B).

    Hypothesis HP3 : forall n ga de th A B C,
                                        th ~p (A %> B) :: ga ++ de
                                     -> P n (ga |-- A)
                                     -> P n (B :: de |-- C)
                                     -> P (S n) (th |-- C).

    Hypothesis HP4 : forall n de th A B,
                                        de ~p A :: th
                                     -> P n (A :: A :: th |-- B)
                                     -> P (S n) (de |-- B).

    Hypothesis HP5 : forall n de th A B,
                                        de ~p A :: th
                                     -> P n (th |-- B)
                                     -> P (S n) (de |-- B).

    Hypothesis HP6 : forall n ga de th A B,
                                        th ~p ga ++ de
                                     -> P n (ga |-- A)
                                     -> P n (A :: de |-- B)
                                     -> P (S n) (th |-- B).

    Theorem LI1_bproof_rect n s t : bproof LI1_rules_wc n s t -> P n s.
    Proof.
      induction 1 as [ n x ll tt H2 H3 H4 ] using bproof_rect.

      apply LI1_rules_wc_reif in H2.
      destruct H2 as [ [ [ [ [ H2 | H2 ] | H2 ] | H2 ] | H2 ] | H2 ].

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

      apply LR_rule_l_reif in H2.
      destruct H2 as ( ((((((ga,de),th),a),b),d) & H) & E).
      cbv in E; inversion E; subst x ll.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (ta & mma & H3 & H5 & H6).
      apply Forall2_cons_inv_l in H6.
      destruct H6 as (tb & mmb & H6 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst mmb.
      subst.
      apply HP3 with ga de a b; auto.
      apply H4 with ta; auto.
      apply H4 with tb; auto.

      apply rule_cntr_reif in H2.
      destruct H2 as ( ((((ga,th),a),b) & H) & E).
      cbv in E; inversion E; subst x ll.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (t' & mm & H3 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst.
      apply HP4 with th a; auto.
      apply H4 with t'; auto.

      apply rule_weak_reif in H2.
      destruct H2 as ( ((((ga,th),a),b) & H) & E).
      cbv in E; inversion E; subst x ll.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (t' & mm & H3 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst.
      apply HP5 with th a; auto.
      apply H4 with t'; auto.

      apply rule_cut_reif in H2.
      destruct H2 as ( (((((ga,de),th),a),b) & H) & E).
      cbv in E; inversion E; subst x ll.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (ta & mm & H3 & H7 & H8).
      apply Forall2_cons_inv_l in H8.
      destruct H8 as (tb & mmb & H8 & H9 & H10).
      apply Forall2_nil_inv_l in H10; subst.
      apply HP6 with ga de a; auto.
      apply H4 with ta; auto.
      apply H4 with tb; auto.
    Qed.

  End LI1_bproof_rect.

  Section LI1_cf_bproof_rect.

    Variable P : nat -> Seq -> Type.

    Hypothesis HP1 : forall n A, P (S n) (A :: nil |-- A).

    Hypothesis HP2 : forall n ga A B,   P n (A :: ga |-- B)
                                     -> P (S n) (ga |-- A %> B).

    Hypothesis HP3 : forall n ga de th A B C,
                                        th ~p (A %> B) :: ga ++ de
                                     -> P n (ga |-- A)
                                     -> P n (B :: de |-- C)
                                     -> P (S n) (th |-- C).

    Hypothesis HP4 : forall n de th A B,
                                        de ~p A :: th
                                     -> P n (A :: A :: th |-- B)
                                     -> P (S n) (de |-- B).

    Hypothesis HP5 : forall n de th A B,
                                        de ~p A :: th
                                     -> P n (th |-- B)
                                     -> P (S n) (de |-- B).

    Theorem LI1_cf_bproof_rect n s t : bproof LI1_rules n s t -> P n s.
    Proof.
      induction 1 as [ n x ll tt H2 H3 H4 ] using bproof_rect.

      apply LI1_rules_reif in H2.
      destruct H2 as [ [ [ [ H2 | H2 ] | H2 ] | H2 ] | H2 ].

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

      apply LR_rule_l_reif in H2.
      destruct H2 as ( ((((((ga,de),th),a),b),d) & H) & E).
      cbv in E; inversion E; subst x ll.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (ta & mma & H3 & H5 & H6).
      apply Forall2_cons_inv_l in H6.
      destruct H6 as (tb & mmb & H6 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst mmb.
      subst.
      apply HP3 with ga de a b; auto.
      apply H4 with ta; auto.
      apply H4 with tb; auto.

      apply rule_cntr_reif in H2.
      destruct H2 as ( ((((ga,th),a),b) & H) & E).
      cbv in E; inversion E; subst x ll.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (t' & mm & H3 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst.
      apply HP4 with th a; auto.
      apply H4 with t'; auto.

      apply rule_weak_reif in H2.
      destruct H2 as ( ((((ga,th),a),b) & H) & E).
      cbv in E; inversion E; subst x ll.
      apply Forall2_cons_inv_l in H3.
      destruct H3 as (t' & mm & H3 & H7 & H8).
      apply Forall2_nil_inv_l in H8; subst.
      apply HP5 with th a; auto.
      apply H4 with t'; auto.
    Qed.

  End LI1_cf_bproof_rect.

  Definition LI1_bproof_ind (P : _ -> _ -> Prop) := LI1_bproof_rect P.

  Section LI1_cf_bprovable_ind.

    Variable P : nat -> Seq -> Prop.

    Hypothesis HP1 : forall n A, P (S n) (A :: nil |-- A).

    Hypothesis HP2 : forall n ga A B,   P n (A :: ga |-- B)
                                     -> P (S n) (ga |-- A %> B).

    Hypothesis HP3 : forall n ga de th A B C,
                                        th ~p (A %> B) :: ga ++ de
                                     -> P n (ga |-- A)
                                     -> P n (B :: de |-- C)
                                     -> P (S n) (th |-- C).

    Hypothesis HP4 : forall n de th A B,
                                        de ~p A :: th
                                     -> P n (A :: A :: th |-- B)
                                     -> P (S n) (de |-- B).

    Hypothesis HP5 : forall n de th A B,
                                        de ~p A :: th
                                     -> P n (th |-- B)
                                     -> P (S n) (de |-- B).

    Theorem LI1_cf_bprovable_ind n s : LI1_cf_bprovable n s -> P n s.
    Proof.
      intros (t & Ht); revert Ht.
      apply LI1_cf_bproof_rect; auto.
    Qed.

  End LI1_cf_bprovable_ind.

  Section LI1_proof_rect.

    Variable P : Seq -> Type.

    Hypothesis HP1 : forall A, P (A :: nil |-- A).

    Hypothesis HP2 : forall ga A B,     P (A :: ga |-- B)
                                     -> P (ga |-- A %> B).

    Hypothesis HP3 : forall ga de th A B C,
                                        th ~p (A %> B) :: ga ++ de
                                     -> P (ga |-- A)
                                     -> P (B :: de |-- C)
                                     -> P (th |-- C).

    Hypothesis HP4 : forall de th A B,
                                        de ~p A :: th
                                     -> P (A :: A :: th |-- B)
                                     -> P (de |-- B).

    Hypothesis HP5 : forall de th A B,
                                        de ~p A :: th
                                     -> P (th |-- B)
                                     -> P (de |-- B).

    Hypothesis HP6 : forall ga de th A B,
                                        th ~p ga ++ de
                                     -> P (ga |-- A)
                                     -> P (A :: de |-- B)
                                     -> P (th |-- B).

    Theorem LI1_proof_rect s : LI1_proof s -> P s.
    Proof.
      intros (n & t & Ht); revert n s t Ht.
      apply LI1_bproof_rect with (P := fun _ s => P s); auto.
    Qed.

  End LI1_proof_rect.

  Section LI1_provable_ind.

    Variable P : Seq -> Prop.

    Hypothesis HP1 : forall A, P (A :: nil |-- A).

    Hypothesis HP2 : forall ga A B,     P (A :: ga |-- B)
                                     -> P (ga |-- A %> B).

    Hypothesis HP3 : forall ga de th A B C,
                                        th ~p (A %> B) :: ga ++ de
                                     -> P (ga |-- A)
                                     -> P (B :: de |-- C)
                                     -> P (th |-- C).

    Hypothesis HP4 : forall de th A B,
                                        de ~p A :: th
                                     -> P (A :: A :: th |-- B)
                                     -> P (de |-- B).

    Hypothesis HP5 : forall de th A B,
                                        de ~p A :: th
                                     -> P (th |-- B)
                                     -> P (de |-- B).

    Hypothesis HP6 : forall ga de th A B,
                                        th ~p ga ++ de
                                     -> P (ga |-- A)
                                     -> P (A :: de |-- B)
                                     -> P (th |-- B).

    Theorem LI1_provable_ind s : LI1_provable s -> P s.
    Proof.
      intros [ H ]; revert H.
      apply LI1_proof_rect; assumption.
    Qed.

  End LI1_provable_ind.

  Section LI1_cf_proof_rect.

    Variable P : Seq -> Type.

    Hypothesis HP1 : forall A, P (A :: nil |-- A).

    Hypothesis HP2 : forall ga A B,     P (A :: ga |-- B)
                                     -> P (ga |-- A %> B).

    Hypothesis HP3 : forall ga de th A B C,
                                        th ~p (A %> B) :: ga ++ de
                                     -> P (ga |-- A)
                                     -> P (B :: de |-- C)
                                     -> P (th |-- C).

    Hypothesis HP4 : forall de th A B,
                                        de ~p A :: th
                                     -> P (A :: A :: th |-- B)
                                     -> P (de |-- B).

    Hypothesis HP5 : forall de th A B,
                                        de ~p A :: th
                                     -> P (th |-- B)
                                     -> P (de |-- B).

    Theorem LI1_cf_proof_rect s : LI1_cf_proof s -> P s.
    Proof.
      intros (n & t & Ht); revert Ht.
      apply LI1_cf_bproof_rect with (P := fun _ s => P s) (n := n); auto.
    Qed.

  End LI1_cf_proof_rect.

  Section LI1_cf_provable_ind.

    Variable P : Seq -> Prop.

    Hypothesis HP1 : forall A, P (A :: nil |-- A).

    Hypothesis HP2 : forall ga A B,     P (A :: ga |-- B)
                                     -> P (ga |-- A %> B).

    Hypothesis HP3 : forall ga de th A B C,
                                        th ~p (A %> B) :: ga ++ de
                                     -> P (ga |-- A)
                                     -> P (B :: de |-- C)
                                     -> P (th |-- C).

    Hypothesis HP4 : forall de th A B,
                                        de ~p A :: th
                                     -> P (A :: A :: th |-- B)
                                     -> P (de |-- B).

    Hypothesis HP5 : forall de th A B,
                                        de ~p A :: th
                                     -> P (th |-- B)
                                     -> P (de |-- B).

    Theorem LI1_cf_provable_ind s : LI1_cf_provable s -> P s.
    Proof.
      intros (n & Hn).
      apply LI1_cf_bprovable_ind with (P := fun _ s => P s) (n := n); auto.
    Qed.

  End LI1_cf_provable_ind.

  Section LI1_cf_perm.

    Let bproof_perm_rec n c d : LI1_cf_bprovable n c
                             -> fst c ~p fst d
                             -> snd c = snd d
                             -> LI1_cf_bprovable n d.
    Proof.
      intros H; revert H d.
      induction 1 as [ n a
                     | n ga a b IH
                     | n ga de th a b x G1 G3 G4
                     | n de th a x G2 G3
                     | n de th a x G2 G3 ] using LI1_cf_bprovable_ind;
        intros (ka,d); simpl; intros E1 E2; subst d.

      apply Permutation_length_1_inv in E1; subst ka.
      apply LI1_rule_b_id.

      apply LI1_rule_b_r, IH; simpl; auto.

      apply LI1_rule_b_l with ga de a b.
      apply perm_trans with (2 := G1), Permutation_sym; auto.
      apply G3; auto.
      apply G4; auto.

      apply LI1_rule_b_cntr with th a; auto.
      apply perm_trans with (2 := G2), Permutation_sym; auto.

      apply LI1_rule_b_weak with th a; auto.
      apply perm_trans with (2 := G2), Permutation_sym; auto.
    Qed.

    Lemma LI1_cf_bprovable_perm n ga de a :
            ga ~p de
         -> LI1_cf_bprovable n (ga |-- a)
         -> LI1_cf_bprovable n (de |-- a).
    Proof.
      intros H1 H2.
      apply bproof_perm_rec with (1 := H2); auto.
    Qed.

    Lemma LI1_cf_provable_perm ga de a :
            ga ~p de
         -> LI1_cf_provable (ga |-- a)
         -> LI1_cf_provable (de |-- a).
    Proof.
      intros H1 (n & H2); exists n; revert H2; apply LI1_cf_bprovable_perm; auto.
    Qed.

  End LI1_cf_perm.

  Lemma LI1_cf_provable_contract ga de x :
            ga c>> de
         -> LI1_cf_provable (ga |-- x)
         -> LI1_cf_provable (de |-- x).
  Proof.
    intros H; revert x.
    apply list_contract_one_rect with (eqX_dec := Form_eq_dec) (4 := H);
      clear ga de H.
    intros ga de ? ?; apply LI1_cf_provable_perm; auto.
    intros ? ? ?; apply LI1_cf_provable_cntr; auto.
    auto.
  Qed.

  Lemma LI1_cf_provable_weakening ga de x :
         LI1_cf_provable (ga |-- x)
      -> LI1_cf_provable (ga ++ de |-- x).
  Proof.
    intros H.
    induction de as [ | a de IHde ].
    rewrite <- app_nil_end; auto.
    apply LI1_cf_provable_weak with (ga++de) a; auto.
    apply Permutation_sym, Permutation_cons_app; auto.
  Qed.

  Section LI1_perm.

    Let provable_perm_rec c :
                         LI1_provable c
                      -> forall d,
                         fst c ~p fst d
                      -> snd c = snd d
                      -> LI1_provable d.
    Proof.
      induction 1 as [ A
                     | ga A B IH
                     | ga de th A B C H1 IH1 IH2
                     | ga de A B IH
                     | ga de A B IH
                     | ga de th A B IH1 IH2 ] using LI1_provable_ind;
        intros (rho,D); simpl; intros E1 E2; subst D.

      apply Permutation_length_1_inv in E1; subst rho.
      apply LI1_provable_id.

      apply LI1_provable_r, IH; simpl; auto.

      apply LI1_provable_l with ga de A B; auto.
      apply perm_trans with (1 := Permutation_sym E1); auto.

      apply LI1_provable_cntr with de A; auto.
      apply perm_trans with (1 := Permutation_sym E1); auto.

      apply LI1_provable_weak with de A; auto.
      apply perm_trans with (1 := Permutation_sym E1); auto.

      apply LI1_provable_cut with ga de A; auto.
      apply perm_trans with (1 := Permutation_sym E1); auto.
    Qed.

    Lemma LI1_provable_perm ga de a :
           ga ~p de
        -> LI1_provable (ga |-- a)
        -> LI1_provable (de |-- a).
    Proof.
      intros H1 H2.
      apply provable_perm_rec with (1 := H2); auto.
    Qed.

  End LI1_perm.

  Lemma LI1_provable_contract ga de x :
         ga c>> de
      -> LI1_provable (ga |-- x)
      -> LI1_provable (de |-- x).
  Proof.
    intros H; revert x.
    apply list_contract_one_rect with (eqX_dec := Form_eq_dec) (4 := H);
      clear ga de H.
    intros ga de ? ?; apply LI1_provable_perm; auto.
    intros ? ? ?; apply LI1_provable_cntr; auto.
    auto.
  Qed.



End LI1.



