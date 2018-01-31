(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Arith Wellfounded.

Set Implicit Arguments.

Section list_length_rect.
  
  Variables (X : Type) (P : list X -> Type).
  
  Hypothesis HP : forall l, (forall m, length m < length l -> P m) -> P l.
  
  Theorem list_length_rect : forall l, P l.
  Proof.
    apply well_founded_induction_type 
      with (R := fun l m => length l < length m); auto.
    apply wf_inverse_image, lt_wf.
  Qed.
  
End list_length_rect.
