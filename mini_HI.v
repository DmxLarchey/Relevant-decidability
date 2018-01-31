(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Permutation.

Require Import list_utils.
Require Import formula.

Set Implicit Arguments.

(** Hilbert rules for the implicational fragment of intuitionistic logic *)

Section Hilbert.

  Reserved Notation "'|--' x" (at level 70, no associativity).

  (* Łukasiewicz axiom system for the positive implicational calculus *)
   
  Inductive HI_proof : Form -> Set :=
    | in_HI_K  : forall A B,   |-- A %> B %> A
    | in_HI_S  : forall A B C, |-- (A %> B %> C) %> (A %> B) %> (A %> C) 
    | in_HI_MP : forall A B,   |-- A %> B -> |-- A -> |-- B
  where "|-- A" := (HI_proof A).
  
  (* This is the I combinator : W = S K K *)
  
  Fact HI_I A : |-- A %> A.
  Proof.
    exact (in_HI_MP (in_HI_MP (in_HI_S _ _ _) (in_HI_K _ _)) (in_HI_K _ A)).
  Qed.
  
  (* This is the W combinator : W = S S (S K) *)
  
  Fact HI_W A B : |-- (A %> A %> B) %> (A %> B).
  Proof.
    exact (in_HI_MP (in_HI_MP (in_HI_S _ _ _) (in_HI_S _ _ _))
                    (in_HI_MP (in_HI_S _ _ _) (in_HI_K _ _))).
  Qed.
  
  (* This is the B combinator : B = S (K S) K *)
  
  Fact HI_B A B C : |-- (B %> C) %> (A %> B) %> A %> C.
  Proof.
    exact (in_HI_MP (in_HI_MP (in_HI_S _ _ _) 
                       (in_HI_MP (in_HI_K _ _) (in_HI_S _ _ _)))
                    (in_HI_K _ _)).
  Qed.
  
  Fact HI_KK A B C : |-- C %> A %> B %> A.
  Proof.
    apply in_HI_MP with (1 := in_HI_K _ _), in_HI_K.
  Qed.

  (* This is the C combinator : C = S (S (K B) S) (K K) *)
  
  Fact HI_C A B C : |-- (A %> B %> C) %> (B %> A %> C).
  Proof.
    exact (in_HI_MP 
             (in_HI_MP (in_HI_S _ _ _) 
                       (in_HI_MP (in_HI_MP (in_HI_S _ _ _) 
                                 (in_HI_MP (in_HI_K _ _) (HI_B _ _ _))) (in_HI_S _ _ _)))
             (HI_KK _ _ _)).
  Qed.

  Fact HI_SI A B : |-- ((A %> B) %> A) %> (A %> B) %> B.
  Proof.
    apply in_HI_MP with (1 := in_HI_S _ _ _), HI_I.
  Qed.
  
  Fact HI_KSI A B C : |-- C %> ((A %> B) %> A) %> (A %> B) %> B.
  Proof.
    apply in_HI_MP with (1 := in_HI_K _ _), HI_SI.
  Qed.
  
  Fact HI_S_KSI A B : |-- (A %> (A %> B) %> A) %> A %> (A %> B) %> B.
  Proof.
    apply in_HI_MP with (1 := in_HI_S _ _ _), HI_KSI.
  Qed.
  
  Fact HI_app A B : |-- A %> (A %> B) %> B.
  Proof.
    apply in_HI_MP with (1 := HI_S_KSI _ _), in_HI_K.
  Qed.

  (* Another proof *)
  
  Fact HI_cntr A B : |-- (A %> A %> B) %> (A %> B).
  Proof.
    apply in_HI_MP with (1 := in_HI_S A (A %> B) B), HI_app.
  Qed.
  
  Fact HI_KS A B C D : |-- D %> (A %> B %> C) %> (A %> B) %> (A %> C).
  Proof.
    apply in_HI_MP with (1 := in_HI_K _ _), in_HI_S.
  Qed.
  
  Fact HI_S_KS A B C D : |-- (D %> A %> B %> C) %> D %> (A %> B) %> A %> C.
  Proof.
    apply in_HI_MP with (1 := in_HI_S _ _ _), HI_KS.
  Qed.
  
  Fact HI_tran A B C : |-- (A %> B) %> (B %> C) %> A %> C.
  Proof.
    apply in_HI_MP with (1 := HI_C _ _ _), HI_B.
  Qed.
  
  Lemma HI_list_Form_to_Form_HI_proof l a b : 
      |-- a %> b -> |-- l %%> a -> |-- l %%> b.
  Proof.
    revert a b; induction l as [ | c l IHl ]; intros a b H1 H2.
    apply in_HI_MP with (2 := H2), H1.
    revert H2; simpl. 
    apply IHl, in_HI_MP with (2 := H1), HI_B.
  Qed.
  
  Lemma HI_list_MP l a b : 
      |-- l%%> a %> b -> |-- l %%> a -> |-- l %%> b.
  Proof.
    revert a b; induction l as [ | x l IHl ]; intros a b.
    apply in_HI_MP.
    simpl; intros H; apply IHl.
    revert H; apply HI_list_Form_to_Form_HI_proof, in_HI_S.
  Qed.

  (** This one needs Permutation_rect (decidability of @eq is required)
      to compute an actual permutation from the knowledge that there
      exists one *)
  
  Lemma HI_proof_perm l m a : l ~p m -> |-- l %%> a -> |-- m %%> a.
  Proof.
    intros H; revert a.
    apply Permutation_rect with (1 := Form_eq_dec) (6 := H); 
      clear l m H; try (intros; simpl; auto; fail).
      
    intros ? ? ? ?; simpl; apply HI_list_Form_to_Form_HI_proof, HI_C.
  Qed.
  
  Fact HI_proof_contract th a x : |-- (a::a::th) %%> x -> |-- (a::th) %%> x.
  Proof. simpl; apply HI_list_Form_to_Form_HI_proof, HI_W. Qed.
  
  Fact HI_proof_weak th a x : |-- th %%> x -> |-- (a::th) %%> x.
  Proof. simpl; apply HI_list_Form_to_Form_HI_proof, in_HI_K. Qed.
  
  Fact HI_proof_weakening th x : |-- x -> |-- th %%> x.
  Proof.
    intros; induction th as [ | a th IH ].
    simpl; trivial.
    apply HI_proof_weak; trivial.
  Qed.
  
  (** This one needs list_contract_rect (decidability of @eq _ is required)
      to compute an actual contraction sequence from the knowledge that there
      exists one *)
  
  Lemma HI_proof_list_contract ga de x : 
          list_contract Form_eq_dec ga de -> |-- ga %%> x -> |-- de %%> x.
  Proof.
    intros H; revert x.
    apply list_contract_one_rect with (eqX_dec := Form_eq_dec) 
                                      (4 := H); clear ga de H.
    
    intros ? ? ? ?; apply HI_proof_perm; auto.
    intros ? ? ?; apply HI_proof_contract.
    intros; auto.
  Qed.

End Hilbert.

