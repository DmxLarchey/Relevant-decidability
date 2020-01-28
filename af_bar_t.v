(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREER SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

Require Import Arith List Permutation.

Require Import tacs rel_utils list_utils.
Require Import finite pigeonhole.
Require Import good_base af_t bar_t.

Set Implicit Arguments.

Section af_bar_t.

  Variable (X : Type).

  Implicit Type (R : X -> X -> Prop).
 
  Section bar_t_good_af.

    Lemma bar_good_af_t R ll : bar_t (good R) ll -> af_t (R lrlift ll).
    Proof.
      induction 1 as [ ll Hll | ll Hll IH ].
      
      apply in_af_t0.
      induction Hll as [ ll a b Hll Hab | ll a Hll IH ] .
      intros; simpl; right; apply lift_rel_list_In with (1 := Hab); auto.
      intros; simpl; left; auto.
      
      apply in_af_t1.
      exact IH.
    Qed.

    Let af_bar_good_rec R : af_t R -> forall S ll, R inc2 S lrlift ll -> bar_t (good S) ll.
    Proof.
      induction 1 as [ R HR | R HR IHR ]; intros S ll H.
      
      apply in_bar_t1; intros u.
      apply in_bar_t1; intros v.
      apply in_bar_t0.
      change (v::u::ll) with ((v::u::nil)++ll).
      apply good_lift_rel_list.
      apply good_inc with (1 := H).
      constructor 1 with u; auto; left; auto.
      
      apply in_bar_t1; intros a.
      apply (IHR a _ (a::ll)).
      simpl; unfold lift_rel.
      intros ? ? [ | ]; [ left | right ]; auto.
    Qed.
    
    Lemma af_bar_good_t R ll : af_t (R lrlift ll) -> bar_t (good R) ll.
    Proof.
      intros H; apply af_bar_good_rec with (1 := H); auto.
    Qed.
    
    Hint Resolve bar_good_af_t af_bar_good_t : core.
    
    Theorem bar_t_af_t_eq R ll : (af_t (R lrlift ll) -> bar_t (good R) ll)
                               * (bar_t (good R) ll -> af_t (R lrlift ll)).
    Proof. split; auto. Qed.

    Theorem af_t_bar_t R : af_t R -> bar_t (good R) nil.
    Proof. apply af_bar_good_t with (ll := nil). Qed.

    Theorem bar_t_af_t R : bar_t (good R) nil -> af_t R.
    Proof. apply bar_good_af_t. Qed.

  End bar_t_good_af.

End af_bar_t.

Fact bar_t_good_le : bar_t (good le) nil.
Proof.
  apply af_t_bar_t, le_af_t.
Qed.

Fact bar_t_ramsey X Y R S : bar_t (good R) nil 
                         -> bar_t (good S) nil 
                         -> bar_t (good (@rel_prod X Y R S)) nil.
Proof.
  intros; apply af_t_bar_t, af_t_prod; apply bar_t_af_t; trivial.
Qed.

Section bar_t_eq_list.

  (** We use the finite pigeon hole principle proved
   **  intuitionistically without decidability of (@eq X)
   **)

  Variable (X : Type).
  
  Implicit Type (l : list X).

  (* a list with a duplicate is exactly a good list for @eq X *)
  
  Let good_eq_prop l : good (@eq X) l <-> exists x a b c, l = a++x::b++x::c.
  Proof.
    rewrite good_inv.
    split.
    intros (a & x & b & y & c & ? & ?); subst l y; exists x, a, b, c; auto.
    intros (x & a & b & c & ?); subst l; exists a, x, b, x, c; auto.
  Qed.
  
  (* We also prove that one using the pigeon hole principle *)

  Fact length_good_eq (l : list X) (m : list { x | In x l }) :
     length l < length m -> good (eq <# fun x => In x l #>) m.
  Proof.
    intros H.
    apply good_map_inv with (S := @eq X) (f := @proj1_sig _ _); auto.
    apply good_eq_prop, (@finite_pigeon_hole _ l).
    rewrite map_length; auto.
    intros x; rewrite in_map_iff.
    intros ((? & ?) & [?]); simpl.
    simpl in *; subst; auto.
  Qed.

  Theorem bar_t_eq_list (ll : list X) : bar_t (good (eq <# fun x => In x ll #>)) nil.
  Proof.
    generalize (@bar_t_length {x | In x ll} (S (length ll))).
    apply bar_t_inc, length_good_eq.
  Qed.
  
End bar_t_eq_list.

Section af_bar_eq_finite.

  Variables (X : Type) (P : X -> Prop).
  
  Theorem af_t_eq_list (ll : list X) : af_t (eq <# fun x => In x ll #>).
  Proof.
    apply bar_t_af_t, bar_t_eq_list.
  Qed.
  
  Theorem af_t_eq_finite : finite_t P -> af_t (eq <# P #>).
  Proof.
    intros (ll & Hll).
    generalize (af_t_eq_list ll).
    apply af_t_relmap with (f := fun a b => proj1_sig a = proj1_sig b).
    intros (x & Hx); simpl.
    rewrite <- Hll in Hx.
    exists (exist _ x Hx); auto.
    intros [] [] [] []; simpl; cbv.
    intros; subst; auto.
  Qed.
  
  Theorem bar_t_eq_finite : finite_t P -> bar_t (good (eq <# P #>)) nil.
  Proof.
    intros HP; generalize (af_t_eq_finite HP); apply af_t_bar_t.
  Qed. 

End af_bar_eq_finite.

Lemma af_t_eq_finite_type X l : (forall x : X, In x l) -> af_t (@eq X).
Proof.
  intros Hl.
  generalize (af_t_eq_list l).
  apply af_t_relmap with (f := fun x y => proj1_sig x = y).
  intros b; exists (exist _ b (Hl b)); auto.
  intros [] [] ? ?; simpl; intros; subst; auto.
Qed.

Fact af_t_bool : af_t (@eq bool).
Proof.
  apply af_t_eq_finite_type with (l := true::false::nil).
  intros [|]; cbv; tauto.
Qed.

Section af_t_list_eq.

  Variable X : Type.
  
  Implicit Type ll : list X.
  
  Fact list_incl_quasi_finite_t ll : { mm | forall l, incl l ll <-> exists m, In m mm /\ eql l m }.
  Proof.
    exists (list_power ll).
    apply list_power_equiv.
  Qed.
  
  (* We also prove that one using the pigeon hole principle *)
  
  Fact bar_t_eql_list ll : bar_t (good (@eql _ <# fun l => incl l ll #>)) nil.
  Proof.
    destruct (list_incl_quasi_finite_t ll) as (mm & Hmm).
    generalize (@bar_t_length {l | incl l ll} (S (length mm))).
    apply bar_t_inc.
    intros kk Hkk.
    apply pigeon_hole_rel with (R := fun x y => eql (proj1_sig x) y) in Hkk.

    destruct Hkk as (ll1 & (l & Hl) & ll2 & (m & Hm) & ll3 & p & H1 & H2 & H3 & H4).
    simpl in *.
    subst.
    apply good_app_left.
    constructor 1 with (exist _ m Hm).
    apply in_or_app; right; left; auto.
    simpl.
    apply eql_trans with p; auto.
    apply eql_sym; auto.

    intros (l & Hl) _; simpl.
    rewrite Hmm in Hl.
    destruct Hl as (m & ? & ?); exists m; auto.
  Qed.
 
  Fact af_t_eql_list ll : af_t (@eql _ <# fun l => incl l ll #>).
  Proof.
    apply bar_t_af_t, bar_t_eql_list.
  Qed.

End af_t_list_eq.

Fact af_t_eql_finite X P : finite_t P -> af_t (@eql X <# Forall P #>).
Proof.
  intros (ll & Hll).
  generalize (af_t_eql_list ll).
  apply af_t_relmap with (f := fun x y => proj1_sig x = proj1_sig y).
  
  intros (l & Hl).
  assert (incl l ll) as Hl'.
    intros x Hx.
    apply Hll.
    revert Hx; apply Forall_forall; trivial.
  exists (exist _ l Hl'); auto.
  
  intros (? & ?) (? & ?) (? & ?) (? & ?); simpl.
  intros [] []; auto.
Qed.

Fact bar_t_eql_finite X P : finite_t P -> bar_t (good (@eql X <# Forall P #>)) nil.
Proof.
  intro; apply af_t_bar_t, af_t_eql_finite; auto.
Qed.
