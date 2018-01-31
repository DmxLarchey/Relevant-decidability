(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List.

Require Import list_utils.
Require Import formula.

Set Implicit Arguments.

(** Hilbert rules for relevant logic *)

Section Hilbert.

  Reserved Notation "'|--' x" (at level 70, no associativity).

  Inductive HR_proof : Form -> Set :=
    | in_HR_ax   : forall A,     |-- A %> A
    | in_HR_pfx  : forall A B C, |-- (A %> B) %> (C %> A) %> (C %> B) 
    | in_HR_comm : forall A B C, |-- (A %> B %> C) %> (B %> A %> C)
    | in_HR_cntr : forall A B,   |-- (A %> A %> B) %> (A %> B)
    | in_HR_MP   : forall A B,   |-- A %> B -> |-- A -> |-- B
  where "|-- A" := (HR_proof A).

  Lemma HR_list_Form_to_Form_HR_proof l a b : 
      |-- a %> b -> |-- l %%> a -> |-- l %%> b.
  Proof.
    revert a b; induction l as [ | c l IHl ]; intros a b H1 H2.
    apply in_HR_MP with (2 := H2), H1.
    revert H2; simpl. 
    apply IHl, in_HR_MP with (2 := H1), in_HR_pfx.
  Qed.
  
  (** This one needs Permutation_rect (decidability of @eq is required)
      to compute an actual permutation from the knowledge that there
      exists one *)
  
  Lemma HR_proof_perm l m a : l ~p m -> |-- l %%> a -> |-- m %%> a.
  Proof.
    intros H; revert a.
    apply Permutation_rect with (1 := Form_eq_dec) (6 := H); 
      clear l m H; try (intros; simpl; auto; fail).
      
    intros ? ? ? ?; simpl; apply HR_list_Form_to_Form_HR_proof, in_HR_comm.
  Qed.
  
  Fact HR_proof_contract th a x : |-- (a::a::th) %%> x -> |-- (a::th) %%> x.
  Proof. simpl; apply HR_list_Form_to_Form_HR_proof, in_HR_cntr. Qed.
  
  (** This one needs list_contract_rect (decidability of @eq _ is required)
      to compute an actual contraction sequence from the knowledge that there
      exists one *)
  
  Lemma HR_proof_list_contract ga de x : 
          list_contract Form_eq_dec ga de -> |-- ga %%> x -> |-- de %%> x.
  Proof.
    intros H; revert x.
    apply list_contract_one_rect with (eqX_dec := Form_eq_dec) 
                                      (4 := H); clear ga de H.
    
    intros ? ? ? ?; apply HR_proof_perm; auto.
    intros ? ? ?; apply HR_proof_contract.
    intros; auto.
  Qed.

End Hilbert.

