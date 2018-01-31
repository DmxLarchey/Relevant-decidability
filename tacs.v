(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREER SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

(* with an Hypothesis H : A -> B, specializes H to H : B after
   having provided a proof of A. A is available under U : A
   afterwards 
*) 

Ltac spec H U :=
  match goal with [ G : ?h -> _ |- _ ] => 
    match G with H => assert h as U; [ idtac | specialize (H U) ] end end.

(* spec but forgets U : A *)

Ltac specf H := let U := fresh in spec H U; [ idtac | clear U ].

(* and do it as much as you can *)

Ltac spec_all_rec H U :=
  try match goal with [ G : ?h -> _ |- _ ] => 
    match G with H => assert h as U; [ idtac | specialize (H U); clear U; spec_all_rec H U ] end end.
      
Ltac spec_all H := let U := fresh in spec_all_rec H U.

(* with a goal H : A, ... |- B, replace it with A = B *)

Ltac replace_with H :=
  match goal with [ G : ?h |- ?c ] => match H with G => cutrewrite (c = h); [ exact H | f_equal ] end end.

Ltac inhabited_tac :=
  let H := fresh 
  in match goal with 
       | |- inhabited _ -> _ => intros [ H ]; inhabited_tac; revert H
       | |- inhabited _      => exists
     end.

Definition ex_rect (A : Prop) (P : A -> Prop) (Q : Type) : (forall x : A, P x -> Q) -> (exists x, P x) -> Q.
Proof.
  intros HA H.
  cut({ x | P x}).
  intros [ ? H1 ]; revert H1; apply HA.
  destruct H as (x & ?); exists x; assumption.
Qed.
