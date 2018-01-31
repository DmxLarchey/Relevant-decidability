(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Permutation.

Require Import list_perm.

Set Implicit Arguments.

Section incl.

  Variable X : Type.
  
  Implicit Type l : list X.
  
  Fact incl_cons_linv l m x : incl (x::m) l -> In x l /\ incl m l.
  Proof.
    intros H; split.
    apply H; left; auto.
    intros ? ?; apply H; right; auto.
  Qed.

  Fact incl_app_rinv l m p : incl m (l++p) -> exists m1 m2, m ~p m1++m2 /\ incl m1 l /\ incl m2 p.
  Proof.
    induction m as [ | x m IHm ].
    exists nil, nil; simpl; repeat split; auto; intros ? [].
    intros H.
    apply incl_cons_linv in H.
    destruct H as (H1 & H2).
    destruct (IHm H2) as (m1 & m2 & H3 & H4 & H5).
    apply in_app_or in H1; destruct H1 as [ H1 | H1 ].
    exists (x::m1), m2; repeat split; auto.
    constructor 2; auto.
    intros ? [ ? | ? ]; subst; auto.
    exists m1, (x::m2); repeat split; auto.
    apply Permutation_cons_app; auto.
    intros ? [ ? | ? ]; subst; auto.
  Qed.
  
  Fact incl_cons_rinv x l m : incl m (x::l) -> exists m1 m2, m ~p m1 ++ m2 /\ (forall a, In a m1 -> a = x) /\ incl m2 l.
  Proof.
    intros H.
    apply (@incl_app_rinv (x::nil) _ l) in H.
    destruct H as (m1 & m2 & H1 & H2 & H3).
    exists m1, m2; repeat split; auto.
    intros a Ha; apply H2 in Ha; destruct Ha as [ | [] ]; auto.
  Qed.
  
End incl.

Section eql.

  Variable X : Type.
  
  Implicit Type l : list X.

  Definition eql l m := incl l m /\ incl m l.

  Fact eql_refl l : eql l l.
  Proof.
    split; red; auto.
  Qed.
  
  Fact eql_sym l m : eql l m -> eql m l.
  Proof.
    intros []; split; auto.
  Qed.
  
  Fact eql_trans l m k : eql l m -> eql m k -> eql l k.
  Proof.
    intros [] []; split; apply incl_tran with m; auto.
  Qed.
  
End eql.

(* a Type (instead of Prop) based predicate for is inside a list 
   In_t x ll (the name is not very wisely chosen) is an OCCURENCE
   of x in ll
*)
   
Section In_t.

  Variables X : Type.

  Fixpoint In_t (x : X) ll : Set :=
    match ll with
      | nil   => False
      | y::ll => (( x = y ) + In_t x ll)%type
    end.

  Fixpoint split_In_t l x r { struct l } : In_t x (l++x::r).
  Proof.
    destruct l as [ | y l ]; simpl.
    left; trivial.
    right; apply split_In_t.
  Defined.

  Fact In_t_In x ll : In_t x ll -> In x ll.
  Proof.
    induction ll.
    intros [].
    intros [ H | H ].
    subst; left; auto.
    right; auto.
  Qed.

  Fact In_t_plus_app x ll mm : In_t x ll + In_t x mm -> In_t x (ll++mm).
  Proof.
    induction ll; simpl; tauto.
  Qed.

  Fact In_t_app_plus x ll mm : In_t x (ll++mm) -> In_t x ll + In_t x mm.
  Proof.
    induction ll; simpl; tauto.
  Qed.

  Fact inhabited_In_t x ll : In x ll <-> inhabited (In_t x ll).
  Proof.
   split.
   
   induction ll as [ | y ll IH ].
   intros [].
   intros [ H | H ]; subst.
   exists; left; auto.
   destruct (IH H); exists; right; auto.
   
   intros []; apply In_t_In; auto.
  Qed.

  Fact In_t_P (P : Prop) x ll  : (In_t x ll -> P) -> In x ll -> P.
  Proof.
    rewrite inhabited_In_t.
    intros ? []; auto.
  Qed.

  Fact In_In_t (P : X -> Prop) ll : (forall x, In_t x ll -> P x) <-> forall x, In x ll -> P x.
  Proof.
    split.
    intros H x; specialize (H x); revert H; apply In_t_P.
    intros H x Hx; apply In_t_In in Hx; auto.
  Qed.

  (* given an heterogeneous list mm = [P1;...;Pn] computes P1 /\ P2 /\ ... /\ Pn *)

  Fixpoint list_conj (mm : list X) : (forall x, In_t x mm -> Prop) -> Prop.
  Proof.
    refine(match mm with
      | nil   => fun H => _
      | x::ll => fun H => _
    end).
    apply True.
    refine (H x _ /\ list_conj ll _).
    left; auto.
    intros y ?; apply (H y); right; auto.
  Defined.

  Fact list_conj_ext mm f1 f2 : (forall x Hx, f1 x Hx = f2 x Hx) -> list_conj mm f1 = list_conj mm f2.
  Proof.
    induction mm; simpl; intros; f_equal; auto.
  Qed.

  Fact list_conj_prop mm Hmm : list_conj mm Hmm <-> forall x (p : In_t x mm), Hmm x p.
  Proof.
    revert Hmm.
    induction mm as [ | x mm IH ]; intros Hmm; split; simpl; auto.
    intros _ ? [].
    intros [ H1 H2 ] y [ Hy | Hy ]; subst; auto.
    apply (IH (fun y Hy => Hmm y (inr Hy))); auto.
    intros H; split.
    apply H.
    apply IH.
    intros; apply H.
  Qed.

  (* given an heterogeneous list mm = [P1;...;Pn] computes P1 \/ P2 \/ ... \/ Pn *)
 
  Fixpoint list_disj (mm : list X) : (forall x, In_t x mm -> Prop) -> Prop.
  Proof.
    refine(match mm with
      | nil   => fun H => _
      | x::ll => fun H => _
    end).
    apply False.
    refine (H x _ \/ list_disj ll _).
    left; auto.
    intros y ?; apply (H y); right; auto.
  Defined.

  Fact list_disj_ext mm f1 f2 : (forall x Hx, f1 x Hx = f2 x Hx) -> list_disj mm f1 = list_disj mm f2.
  Proof.
    induction mm; simpl; intros; f_equal; auto.
  Qed.

  Fact list_disj_prop mm Hmm : list_disj mm Hmm <-> exists x (p : In_t x mm), Hmm x p.
  Proof.
    revert Hmm.
    induction mm as [ | x mm IH ]; intros Hmm; split; simpl; auto.
    intros [].
    intros (? & [] & _).
    intros [ H | H ].
    exists x, (inl eq_refl); auto.
    rewrite IH in H.
    destruct H as (y & Hy & H).
    exists y, (inr Hy); auto.
    intros (y & [ Hy | Hy ] & H).
    subst; left; auto.
    right; rewrite IH; exists y, Hy; auto.
  Qed.

End In_t.

Fact forall_exists_In_t U V (R : U -> V -> Prop) lu : (forall u, In u lu -> exists v, R u v)
                         -> exists f : forall u, In_t u lu -> V, forall u Hu, R u (f u Hu).
Proof.
  induction lu as [ | u lu IH ].
  intros _.
  exists (fun v (Hv : In_t v nil) => match Hv with end).
  intros ? [].
  intros H.
  destruct IH as (f & Hf).
  intros; apply H; right; auto.
  destruct (H u) as (w & Hw).
  left; auto.
  exists (fun v (Hv : In_t v (u::lu)) => match Hv with inl _ => w | inr H => f _ H end).
  intros v [ Hv | Hv ].
  subst; auto.
  apply Hf; auto.
Qed.

Section In_t_map.

  Variable (X Y : Type).

  Section In_t_map.
  
    Variable (f : X -> Y).
    
    Definition In_t_map ll y : In_t y (map f ll) -> { x : X & { _ : In_t x ll | y = f x } }.
    Proof.
      induction ll as [ | x ll IH ].
      intros [].
      intros [ H | H ]; subst.
      exists x, (inl eq_refl); auto.
      destruct (IH H) as (x' & H1 & H2).
      exists x', (inr H1); auto.
    Qed.
    
    Fixpoint map_In_t ll x { struct ll } : In_t x ll -> In_t (f x) (map f ll).
    Proof.
      refine(match ll return In_t x ll -> In_t (f x) (map f ll) with
        | nil   => fun H => _
        | y::mm => fun H => 
          match H with
            | inl E => inl (f_equal _ E)
            | inr G => inr (map_In_t _ _ G)
          end
      end).
      destruct H.
    Defined.

  End In_t_map.

  Section In_t_flat_map.

    Variable g : X -> list Y.
    
    Definition In_t_flat_map l y : In_t y (flat_map g l) -> { x :_ &  (In_t x l * In_t y (g x))%type }.
    Proof.
      induction l as [ | x l IHl ]; simpl.
      intros [].
      intros H.
      apply In_t_app_plus in H.
      destruct H as [ H | H ].
      exists x; split; auto.
      destruct (IHl H) as (x' & H1 & H2).
      exists x'; auto.
    Qed.
    
    Definition flat_map_In_t l x y : In_t y l -> In_t x (g y) -> In_t x (flat_map g l).
    Proof.
      induction l as [ | x' l IHl ]; simpl; auto.
      intros [ H1 | H1 ] H2; subst;
      apply In_t_plus_app; tauto.
    Qed.

  End In_t_flat_map.

End In_t_map.

Section map_t.

  Variable X : Type.
  Variable P : X -> Type.
  Variable f : forall x, P x.
  
  Fixpoint map_t ll : forall x, In_t x ll -> P x.
  Proof. 
    refine(match ll with 
      | nil   => fun x H => _
      | a::ll => fun x H => _
    end).
    elim H.
    destruct H as [ | H ].
    subst; apply f.
    apply (map_t _ _ H).
  Defined.
  
  Fact map_t_prop ll x (Hx : In_t x ll) : map_t ll x Hx = f x.
  Proof.
    induction ll; destruct Hx; simpl; subst; trivial.
  Qed.

End map_t.

(* VERY BAD name here, I know *)

Section list_In_map.

  Variable X Y : Type.

  Fixpoint list_In_map ll : (forall x : X, In x ll -> Y) -> list Y.
  Proof.
    refine (
      match ll with
        | nil   => fun _ => nil
        | x::mm => fun H => H x _ :: list_In_map mm _
      end).
    left; reflexivity.
    intros z ?; apply (H z); right; assumption.
  Defined.
    
  Fact list_In_map_length ll Hll : length (list_In_map ll Hll) = length ll.
  Proof.
    induction ll; simpl; f_equal; auto.
  Qed.

  Fact list_In_map_ext ll g h : (forall x (H : In x ll), g x H = h x H) -> list_In_map ll g = list_In_map ll h.
  Proof.
    induction ll; simpl; intros; f_equal; auto.
  Qed.
  
  Fact list_In_map_eq_map f ll : list_In_map ll (fun x _ => f x) = map f ll.
  Proof.
    induction ll; simpl; f_equal; assumption.
  Qed.

  Fact In_list_In_map l f x (Hx : In x l) : In (f x Hx) (list_In_map l f). 
  Proof.
    revert f x Hx; induction l; simpl; intros f x Hx.
    destruct Hx.
    destruct Hx as [ ? | Hx ].
    subst; left; auto.
    right. 
    apply IHl with (f := fun x Hx => f x (or_intror Hx)).
  Qed.

  Fact list_In_map_In l f y : In y (list_In_map l f) -> exists x Hx, y = f x Hx.
  Proof.
    revert f y; induction l as [ | x l IH ]; intros f y.
    intros [].
    intros [ ? | H ]; subst.
    exists x, (or_introl eq_refl); auto.
    destruct IH with (f := fun x Hx => f x (or_intror Hx))
                     (1 := H)
     as (u & Hu & ?).
    exists u, (or_intror Hu); auto.
  Qed.

  Hypothesis Yeq_dec : forall x y : Y, { x = y } + { x <> y }.

  Fact list_In_map_In_dec l f y : In y (list_In_map l f) -> {x : _ & { Hx | y = f x Hx } }.
  Proof.
    revert f y; induction l as [ | x l IH ]; intros f y.
    intros [].
    destruct (Yeq_dec y (f x (or_introl eq_refl))) as [ E | C ].
    exists x, (or_introl eq_refl); auto.
    intros H.
    assert (In y (list_In_map l (fun x Hx => f x (or_intror Hx)))) as Hy.
      destruct H; auto.
      contradict C; auto.
    destruct IH with (f := fun x Hx => f x (or_intror Hx))
                     (1 := Hy)
      as (u & Hu & ?); subst.
    exists u, (or_intror Hu); auto.
  Qed.
  
End list_In_map.

Fact map_list_In_map X Y Z (ll : list X) Hll (f : Y -> Z) : map f (@list_In_map X Y ll Hll) = list_In_map ll (fun x Hx => f (Hll x Hx)).  
Proof.
  induction ll; simpl; f_equal; auto.
Qed.

Fixpoint map_In X Y (f : X -> Y) l x { struct l } : In x l -> In (f x) (map f l).
Proof.
  destruct l as [ | y l ].
  intros [].
  intros [ [] | H ].
  left; reflexivity.
  right; apply map_In, H.
Defined.

Fact list_In_map_map X Y Z (ll : list X) (f : X -> Y) Hll : @list_In_map Y Z (map f ll) Hll = list_In_map ll (fun x Hx => Hll _ (map_In f ll x Hx)).
Proof.
  induction ll as [ | ? ? IH ]; simpl; f_equal.
  apply IH.
Qed.

Section list_In_t_map.

  Variables (X Y : Type).

  Fixpoint list_In_t_map ll : (forall x : X, In_t x ll -> Y) -> list Y.
  Proof.
    refine (match ll with
      | nil   => fun _ => nil
      | x::mm => fun H => H x _ :: list_In_t_map mm _
    end).
    left; reflexivity.
    intros z ?; apply (H z); right; assumption.
  Defined.

  Fact list_In_t_map_length ll Hll : length (list_In_t_map ll Hll) = length ll.
  Proof.
    induction ll; simpl; f_equal; auto.
  Qed.

  Fact list_In_t_map_ext ll f g : (forall x (H : In_t x ll), f x H = g x H) -> list_In_t_map ll f = list_In_t_map ll g.
  Proof.
    induction ll; simpl; intros; f_equal; auto.
  Qed.

  Definition In_t_list_In_t_map ll f u : In_t u (list_In_t_map ll f) -> { x : _ & { Hx : In_t x ll & u = f x Hx } }.
  Proof.
    revert f; induction ll as [ | a ll IH ]; simpl; intros f.
    intros [].
    intros [ H | H ].
    exists a, (inl eq_refl); auto.
    apply IH in H.
    destruct H as (x & Hx & H).
    exists x, (inr Hx); auto.
  Qed.
 
  Fact list_In_t_map_In_t ll f x Hx : In_t (f x Hx) (list_In_t_map ll f).
  Proof.
    revert f x Hx.
    induction ll as [ | x ll IH ]; intros f y Hy.
    destruct Hy.
    destruct Hy as [ Hy | Hy ].
    subst; simpl; left; auto.
    simpl; right; apply IH with (f := fun y Hy => f y (inr Hy)).
  Qed.

  Fact list_In_t_map_t f ll : list_In_t_map ll (map_t _ f ll) = map f ll.
  Proof.
    induction ll; simpl; f_equal; assumption.
  Qed.
 
End list_In_t_map.

Fact map_list_In_t_map X Y Z (ll : list X) Hll (f : Y -> Z) : map f (@list_In_t_map X Y ll Hll) = list_In_t_map ll (fun x Hx => f (Hll x Hx)).  
Proof.
  induction ll; simpl; f_equal; auto.
Qed.

Fact list_In_t_map_map X Y Z (ll : list X) (f : X -> Y) Hll : @list_In_t_map Y Z (map f ll) Hll = list_In_t_map ll (fun x Hx => Hll _ (map_In_t f ll x Hx)).
Proof.
  induction ll as [ | ? ? IH ]; simpl; f_equal.
  f_equal; auto.
 apply IH.
Qed.
