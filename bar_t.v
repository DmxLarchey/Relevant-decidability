(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List.

Require Import rel_utils list_utils good_base.

Set Implicit Arguments.

Section Bar_type.

  Variables (A : Type) (P : list A -> Prop).

  Inductive bar_t l : Type :=
    | in_bar_t0 : P l -> bar_t l
    | in_bar_t1 : (forall a, bar_t (a::l)) -> bar_t l. 
  
  Fact in_bar_t_inv l : bar_t l -> P l + forall a, bar_t (a::l).
  Proof.
    induction 1 using bar_t_rect; [ left | right ]; auto.
  Qed.

  Implicit Type f : nat -> A.

  Local Lemma bar_t_recursion ws : bar_t ws -> forall f n, ws = pfx_rev f n -> { m | P (pfx_rev f m) }.
  Proof.
    induction 1 as [ ll Hll | ll Hll IH ] using bar_t_rect; intros f n ?; subst.
    exists n; auto.
    apply (IH (f n) f (S n)); auto.
  Qed.
  
  Theorem bar_t_inv : bar_t nil -> forall f, { m | P (pfx_rev f m) }.
  Proof.
    intros H f; apply bar_t_recursion with (1 := H) (n := 0); auto.
  Qed.

  Hypothesis P_mono : forall x ll, P ll -> P (x::ll).

  Theorem bar_t_app ll mm : bar_t ll -> bar_t (mm++ll).
  Proof.
    intros H.
    induction mm as [ | x mm IH ]; simpl; auto.
    apply in_bar_t_inv in IH; destruct IH as [ IH | IH ]; auto.
    apply in_bar_t0; apply P_mono; auto.
  Qed.

  Theorem bar_t_nil_all : bar_t nil -> forall ll, bar_t ll.
  Proof.
    intros H ll.
    rewrite app_nil_end.
    apply bar_t_app, H.
  Qed.

End Bar_type.

(* extending a list always leads to a list of length greater to a given
   value n *)

Theorem bar_t_length X n : bar_t (fun m => n <= @length X m) nil.
Proof.
  generalize (@nil X).
  induction n as [ | n IHn ]; intros l.
  apply in_bar_t0, le_0_n.
  generalize (IHn l); clear IHn.
  induction 1 using bar_t_rect.
  apply in_bar_t1; intro. 
  apply in_bar_t0; simpl; apply le_n_S; auto.
  apply in_bar_t1; auto.
Qed.

Section Bar_t_inc.

  Variable (A : Type) (P Q : list A -> Prop).

  Fact bar_t_inc : P inc1 Q -> bar_t P inc1 bar_t Q.
  Proof.
    intros H ?; induction 1 as [ ws Hws | ws IH ] using bar_t_rect.
    apply in_bar_t0, H, Hws.
    apply in_bar_t1; auto.
  Qed.

End Bar_t_inc.

Section Bar_lift.

  Variables (A : Type) (P : list A -> Prop).

  Let bar_lift1 k : bar_t P k -> forall u v, k = v++u -> bar_t (fun v => P (v++u)) v.
  Proof.
    induction 1 as [ k Hk | k Hk IH ] using bar_t_rect; intros u v H.
    
    apply in_bar_t0; subst; auto.
    
    apply in_bar_t1; intros a.
    apply (IH a u (a::v)).
    simpl; f_equal; auto.
  Qed.
  
  Let bar_lift2 u v : bar_t (fun v => P (v++u)) v -> bar_t P (v++u).
  Proof.
    induction 1 as [ v Hv | v Hv IH ] using bar_t_rect.
    apply in_bar_t0; auto.
    apply in_bar_t1; intros a.
    apply (IH a).
  Qed.

  Theorem bar_t_lift1 u : bar_t P u -> bar_t (fun v => P (v++u)) nil.
  Proof.
    intros H; apply bar_lift1 with (1 := H); auto.
  Qed.
  
  Theorem bar_t_lift2 u : bar_t (fun v => P (v++u)) nil -> bar_t P u. 
  Proof.
    apply bar_lift2.
  Qed.

End Bar_lift.

Section Bar_subst_eq.

  Variable (A : Type) (P : list A -> Prop) (a b : A).
  
  Hypothesis Hab : forall mm ll, P (mm++a::ll) -> P (mm++b::ll).
  
  Let bar_subst_eq_rec l : bar_t P l -> forall mm ll, l = mm++a::ll -> bar_t P (mm++b::ll).
  Proof.
    induction 1 as [ l Hl | l Hl IH ] using bar_t_rect; intros; subst.
    apply in_bar_t0; auto.
    apply in_bar_t1; intros c.
    apply (IH c (c::mm)); auto.
  Qed.
  
  Fact bar_t_subst_eq mm ll : bar_t P (mm++a::ll) -> bar_t P (mm++b::ll).
  Proof.
    intros H; apply bar_subst_eq_rec with (1 := H); auto.
  Qed.

End Bar_subst_eq.

Section Bar_inter.

  Variables (A : Type) (P Q : list A -> Prop).

  Hypothesis HP : forall x ll, P ll -> P (x::ll).
  Hypothesis HQ : forall x ll, Q ll -> Q (x::ll).

  Theorem bar_t_intersection u : bar_t P u -> bar_t Q u -> bar_t (fun x => P x /\ Q x) u.
  Proof.
    induction 1 as [ u Hu | u Hu IHu ] using bar_t_rect.
    induction 1 as [ v Hv | v Hv IHv ] using bar_t_rect.
    
    apply in_bar_t0; auto.
    
    apply in_bar_t1; intros a.
    apply IHv, HP; auto.
    
    induction 1 as [ v Hv | v Hv IHv ] using bar_t_rect.
    
    apply in_bar_t1; intros a.
    apply IHu.
    apply in_bar_t0.
    apply HQ; auto.
    
    apply in_bar_t1; intros a.
    apply IHu; auto.
  Qed.

End Bar_inter.

Section Bar_t_relmap.

  Variables (A B : Type) (R : A -> B -> Prop) 
            (HR : forall a, { b | R a b })
            (P : list A -> Prop) 
            (Q : list B -> Prop)
            (HPQ : forall ll mm, Forall2 R ll mm -> Q mm -> P ll).

  Lemma bar_t_relmap ll mm : Forall2 R ll mm -> bar_t Q mm -> bar_t P ll.
  Proof.
    intros H1 H2.
    revert ll H1.
    induction H2 as [ mm Hmm | mm Hmm IH ] using bar_t_rect; intros ll H1.
    
    apply in_bar_t0, HPQ with (1 := H1); auto.
    apply in_bar_t1; intros a.
    destruct (HR a) as (b & Hb).
    apply IH with (a := b); constructor; auto.
  Qed.

End Bar_t_relmap.

Section Bar_map_inv.

  Variables (A B : Type) (f : A -> B)
            (P : list A -> Prop) 
            (Q : list B -> Prop)
            (HPQ : forall ll, Q (map f ll) -> P ll).

  Lemma bar_t_map_inv ll : bar_t Q (map f ll) -> bar_t P ll.
  Proof.
    apply bar_t_relmap with (R := fun a b => b = f a).
    intros a; exists (f a); auto.
    clear ll.
    intros ll mm H.
    rewrite Forall2_exchg, <- Forall2_map_right, Forall2_eq in H.
    subst; auto.
    rewrite Forall2_exchg, <- Forall2_map_right, Forall2_eq; auto. 
  Qed.
  
End Bar_map_inv.

Section Bar_map.

  Variables (A B : Type) (f : A -> B) (Hf : forall b, { a | b = f a })
            (P : list A -> Prop) 
            (Q : list B -> Prop)
            (HPQ : forall ll, P ll -> Q (map f ll)).

  Lemma bar_t_map ll : bar_t P ll -> bar_t Q (map f ll). 
  Proof.
    apply bar_t_relmap with (R := fun b a => b = f a); auto.
    clear ll.
    intros ll mm H.
    rewrite <- Forall2_map_right, Forall2_eq in H; subst; auto.
    rewrite <- Forall2_map_right, Forall2_eq; auto.
  Qed.
  
End Bar_map.

Section fan_t.

  (* That proof of the FAN theorem is derived from Daniel Fridlender's paper *)

  Notation mono := ((fun X (P : list X -> Prop) => forall x l, P l -> P (x::l)) _).

  Variables (X : Type) (P : list X -> Prop) (HP : mono P).
  
  Let P_mono l m : P m -> P (l++m).
  Proof.
    induction l; simpl; auto.
  Qed.
  
  Let V u := fun lw => Forall (fun v => P (v++u)) (list_fan lw).

  Let V_mono u : mono (V u).
  Proof.
    unfold V; intros w lw H.
    apply list_fan_Forall.
    rewrite Forall_forall; intros x _.
    revert H; apply Forall_impl.
    intro; apply HP.
  Qed.

  Let bar_V u : bar_t P u -> bar_t (V u) nil.
  Proof.    
    induction 1 as [ u Hu | u Hu IHu ] using bar_t_rect.
    
    apply in_bar_t0; unfold V.
    simpl. 
    constructor; simpl; auto.
    
    apply in_bar_t1; intros w.
    induction w as [ | a w IHw ].
    
    apply in_bar_t0.
    unfold V; simpl.
    constructor.

    specialize (IHu a).
    apply bar_t_lift1 in IHw.
    unfold V in IHw.
    generalize (@V_mono (a::u)); intros HV1.
    assert (mono (fun lw => V u (lw++w::nil))) as HV2.
      intros x ll; simpl; apply V_mono.
    generalize (bar_t_intersection HV1 HV2 IHu IHw); intros HV3; clear HV1 HV2.
    apply bar_t_lift2.
    revert HV3; apply bar_t_inc.

    intros x; unfold V.
    intros [ H1 H2 ].
    rewrite (Forall_perm _ (list_fan_middle_cons x a w nil)).
    apply Forall_app; split; auto.
    rewrite list_fan_sg_right.
    rewrite Forall_map.
    revert H1; apply Forall_impl.
    intro; rewrite app_ass; auto.
  Qed.

  Theorem fan_t_on_list : bar_t P nil 
                       -> bar_t (fun ll => Forall P (list_fan ll)) nil.
  Proof.
    intros H.
    generalize (bar_V H).
    apply bar_t_inc.
    intros lw; unfold V.
    apply Forall_impl.
    intro; rewrite <- app_nil_end; auto.
  Qed.

End fan_t.



