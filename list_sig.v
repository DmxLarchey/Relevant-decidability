(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List.

Require Import list_in.
Require Import list_forall.

Set Implicit Arguments.

Section sig_t_invert.

  Variable (X Y : Type) (R : X -> Y -> Prop).

  Definition sig_t_invert ll : (forall x, In_t x ll -> { y | R x y })
                           -> { mm | Forall2 R ll mm }.
  Proof.
    intros H.
    set (f x Hx := proj1_sig (H x Hx)).
    assert (Hf : forall x Hx, R x (f x Hx)).
      intros x Hx; apply (proj2_sig (H x Hx)).
    exists (list_In_t_map _ f).
    rewrite <- (map_id ll) at 1.
    rewrite <- list_In_t_map_t.
    apply Forall2_list_In_t_map.
    intros; rewrite map_t_prop; auto.
  Qed.
  
  Definition sig_invert_t ll : (forall x, In x ll -> { y | R x y })
                           -> { mm | Forall2 R ll mm }.
  Proof.
    intros H; apply sig_t_invert.
    intros; apply H, In_t_In; auto.
  Qed.
  
  Definition invert_sig_t ll mm : Forall2 R ll mm -> forall x, In_t x ll -> { y | R x y }.
  Proof.
    revert mm.
    induction ll as [ | x ll IH ]; intros [ | y mm ] H;
      try (exfalso; inversion H; fail).
    intros ? [].
    apply Forall2_cons_inv in H.
    destruct H as (H1 & H2).
    intros z [ Hx | Hx ]; subst.
    exists y; auto.
    apply IH with (1 := H2); auto.
  Qed.

End sig_t_invert.
           
Section sig_invert.

  Variable (X Y : Type) (R : X -> Y -> Prop).

  Definition sig_invert ll : (forall x, In x ll -> exists y, R x y)
                           -> exists mm, Forall2 R ll mm.
  Proof.
    induction ll as [ | x ll IH ]; intros H.
    exists nil; constructor.
    destruct (H x) as (y & Hy).
    left; auto.
    destruct IH as (mm & Hmm).
    intros; apply H; right; auto.
    exists (y::mm); constructor; auto.
  Qed.
  
  Definition invert_sig ll mm : Forall2 R ll mm -> forall x, In x ll -> exists y, R x y.
  Proof.
    intros H.
    generalize (invert_sig_t H); clear H; intros H.
    rewrite <- In_In_t.
    intros x Hx; destruct (H _ Hx) as (y & ?); exists y; auto.
  Qed.

End sig_invert. 

Section list_sig.

  Variables (X : Type) (P : X -> Prop).

  Fixpoint list_Forall_sig (ll : list X) : (forall x, In x ll -> P x) -> list (sig P).
  Proof.
    refine (
      match ll with 
        | nil   => fun _ => nil
        | x::mm => fun H => (exist _ x (H _ _))::list_Forall_sig mm _
      end).
    left; trivial.
    intros; apply H; right; trivial.
  Defined.

  Fact list_sig_Forall_eq ll Hll : map (@proj1_sig _ _) (list_Forall_sig ll Hll) = ll.
  Proof.
    induction ll; simpl; f_equal; auto.
  Qed.

  Fact list_sig_Forall (ll : list (sig P)) : Forall P (map (@proj1_sig _ _) ll).
  Proof.
    induction ll as [ | (? & ?) ]; simpl; constructor; auto.
  Qed.

  Fact list_Forall_sig_In ll Hll c : In c (list_Forall_sig ll Hll) <-> exists x Hx, c = exist _ x (Hll _ Hx).
  Proof.
    split.
    
    revert Hll c; induction ll as [ | x ll IH ]; simpl.
    destruct 1.
    intros Hll (a & Ha) [ H1 | H1 ].
    injection H1.
    intro; subst x.
    exists a, (or_introl eq_refl); auto.
    apply IH in H1.
    destruct H1 as (b & Hb & H1).
    exists b, (or_intror Hb); auto.
    
    intros (x & Hx & ?); subst.
    revert Hll x Hx.
    induction ll as [ | x ll IH ]; intros Hll y Hy.
    destruct Hy.
    destruct Hy as [ Hy | Hy ].
    subst; left; auto.
    right; apply IH with (Hll := fun x Hx => Hll x (or_intror Hx)).  
  Qed.

  Fact list_Forall_sig_In_refl ll Hll x Hx : In (exist _ x (Hll x Hx)) (list_Forall_sig ll Hll).
  Proof.
    apply list_Forall_sig_In.
    exists x, Hx; trivial.
  Qed.

End list_sig.

Section list_sigT.

  Variables (X : Type) (P : X -> Type).

  Fixpoint list_Forall_sigT (ll : list X) : (forall x, In x ll -> P x) -> list (sigT P).
  Proof.
    refine (
      match ll with 
        | nil   => fun _ => nil
        | x::mm => fun H => (existT _ x (H _ _))::list_Forall_sigT mm _
      end).
    left; trivial.
    intros; apply H; right; trivial.
  Defined.

  Fact list_sigT_Forall_eq ll Hll : map (@projT1 _ _) (list_Forall_sigT ll Hll) = ll.
  Proof.
    induction ll; simpl; f_equal; auto.
  Qed.

End list_sigT.

