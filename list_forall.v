(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation Relations.

Require Import tacs.

Require Import rel_utils.

Require Import list_perm.
Require Import list_in.
Require Import list_prefix.

Set Implicit Arguments.

(* Forall tools *)

Section Forall.

  Variables (X : Type) (P : X -> Prop).

  Fact Forall_app ll mm : Forall P (ll++mm) <-> Forall P ll /\ Forall P mm.
  Proof.
    split.
    induction ll as [ | x ll ]; split; auto.
    constructor;
    inversion H; auto.
    apply IHll; auto.
    inversion H; apply IHll; auto.
    intros (H1 & H2).
    induction H1; simpl; auto; constructor; auto.
  Qed.

  Fact Forall_cons_inv x ll : Forall P (x::ll) <-> P x /\ Forall P ll.
  Proof.
    split.
    inversion_clear 1; auto.
    constructor; tauto.
  Qed.

End Forall.

Section Forall_rect.

  Variables (X : Type) (P : X -> Prop) (Q : list X -> Type) 
            (HP1 : Q nil) 
            (HP2 : forall x l, P x -> Forall P l -> Q l -> Q (x::l)).

  Fact Forall_rect l : Forall P l -> Q l.
  Proof.
    induction l as [ | x l IHl ].
    intros _; apply HP1.
    intros H; apply Forall_cons_inv in H; destruct H.
    apply HP2; auto.
  Qed.

End Forall_rect.

Section Forall_Permutation.

  Variables (X : Type) (P : X -> Prop).

  Let Forall_perm_rec ll mm : ll ~p mm -> Forall P ll -> Forall P mm.
  Proof.
    induction 1; auto.
    intros G; constructor; inversion_clear G; auto.
    intros G. 
    apply Forall_cons_inv in G; destruct G as [ Gy G ].
    apply Forall_cons_inv in G; destruct G as [ Gx G ].
    repeat constructor; auto.
  Qed.
 
  Fact Forall_perm ll mm : ll ~p mm -> (Forall P ll <-> Forall P mm).
  Proof.
    split; apply Forall_perm_rec; auto.
    apply Permutation_sym; auto.
  Qed.

End Forall_Permutation.

Section map_ext_Forall.

  Variable (X Y : Type) (f g : X -> Y).

  Fact map_ext_Forall ll : (Forall (fun x => f x = g x) ll) -> map f ll = map g ll.
  Proof.
    induction 1; simpl; f_equal; auto.
  Qed.

  Variable P : Y -> Prop.

  Fact Forall_map ll : Forall P (map f ll) <-> Forall (fun x => P (f x)) ll.
  Proof.
    split.
    induction ll as [ | x ll IH ]; constructor;
    simpl in H; inversion_clear H; auto.
    induction 1; constructor; auto.
  Qed.

End map_ext_Forall.

Section Forall_flat_map.

  Variable (A B C D : Type) (f f' : A -> list B) (P : B -> Prop).
  
  Fact Forall_flat_map ll : Forall P (flat_map f ll) <-> Forall (fun x => Forall P (f x)) ll.
  Proof.
    split.

    induction ll as [ | x ll IH ].
    constructor.
    simpl; intros H.
    rewrite Forall_app in H.
    constructor; try apply H.
    apply IH, H.
    
    induction 1; simpl.
    constructor.
    rewrite Forall_app; split; auto.
  Qed.

End Forall_flat_map.

(* Forall2 tools *)

Fact list_length_eq_Forall2 X Y (l : list X) (m : list Y) : length l = length m <-> Forall2 (fun _ _ => True) l m.
Proof.
  split.
  revert m; induction l; intros [|]; try discriminate 1; simpl; intros H; constructor; auto.
  induction 1; simpl; f_equal; auto.
Qed.

Fact Forall2_nil_inv_l X Y R m : @Forall2 X Y R nil m -> m = nil.
Proof.
  inversion_clear 1; reflexivity.
Qed.

Fact Forall2_nil_inv_r X Y R m : @Forall2 X Y R m nil -> m = nil.
Proof.
  inversion_clear 1; reflexivity.
Qed.

Fact Forall2_cons_inv X Y R x l y m : @Forall2 X Y R (x::l) (y::m) <-> R x y /\ Forall2 R l m.
Proof.
  split.
  inversion_clear 1; auto.
  intros []; constructor; auto.
Qed.

Fact Forall2_app_inv_l X Y R l1 l2 m : 
    @Forall2 X Y R (l1++l2) m -> { m1 : _ & { m2 | Forall2 R l1 m1 /\ Forall2 R l2 m2 /\ m = m1++m2 } }.
Proof.
  revert l2 m;
  induction l1 as [ | x l1 IH ]; simpl; intros l2 m H.
  exists nil, m; repeat split; auto.
  destruct m as [ | y m ].
  apply Forall2_nil_inv_r in H; discriminate H.
  apply Forall2_cons_inv in H; destruct H as [ H1 H2 ].
  apply IH in H2.
  destruct H2 as (m1 & m2 & H2 & H3 & H4); subst m.
  exists (y::m1), m2; repeat split; auto.
Qed.

Fact Forall2_app_inv_r X Y R l m1 m2 : 
    @Forall2 X Y R l (m1++m2) -> { l1 : _ & { l2 | Forall2 R l1 m1 /\ Forall2 R l2 m2 /\ l = l1++l2 } }.
Proof.
  revert m2 l;
  induction m1 as [ | y m1 IH ]; simpl; intros m2 l H.
  exists nil, l; repeat split; auto.
  destruct l as [ | x l ].
  apply Forall2_nil_inv_l in H; discriminate H.
  apply Forall2_cons_inv in H; destruct H as [ H1 H2 ].
  apply IH in H2.
  destruct H2 as (l1 & l2 & H2 & H3 & H4); subst l.
  exists (x::l1), l2; repeat split; auto.
Qed.

Fact Forall2_cons_inv_l X Y R a ll mm : 
      @Forall2 X Y R (a::ll) mm 
   -> { b : _ & { mm' | R a b /\ mm = b::mm' /\ Forall2 R ll mm' } }.
Proof.
  intros H.
  apply Forall2_app_inv_l with (l1 := a::nil) (l2 := ll) in H.
  destruct H as (l & mm' & H1 & H2 & H3).
  destruct l as [ | y l ].
  exfalso; inversion H1.
  apply Forall2_cons_inv in H1.
  destruct H1 as [ H1 H4 ].
  apply Forall2_nil_inv_l in H4; subst l.
  exists y, mm'; auto.
Qed.

Fact Forall2_cons_inv_r X Y R b ll mm : 
      @Forall2 X Y R ll (b::mm) 
   -> { a : _ & { ll' | R a b /\ ll = a::ll' /\ Forall2 R ll' mm } }.
Proof.
  intros H.
  apply Forall2_app_inv_r with (m1 := b::nil) (m2 := mm) in H.
  destruct H as (l & ll' & H1 & H2 & H3).
  destruct l as [ | x l  ].
  exfalso; inversion H1.
  apply Forall2_cons_inv in H1.
  destruct H1 as [ H1 H4 ].
  apply Forall2_nil_inv_r in H4; subst l.
  exists x, ll'; auto.
Qed.

Fact Forall2_rev X Y (R : X -> Y -> Prop) ll mm : Forall2 R ll mm <-> Forall2 R (rev ll) (rev mm).
Proof.
  assert (forall ll mm, Forall2 R ll mm -> Forall2 R (rev ll) (rev mm)) as H.
    induction 1; simpl; auto. 
    apply Forall2_app; auto.
  split; auto.
  rewrite <- (rev_involutive ll) at 2.
  rewrite <- (rev_involutive mm) at 2.
  auto.
Qed.

Fact Forall2_conj X Y (R S : X -> Y -> Prop) ll mm : Forall2 (fun x y => R x y /\ S x y) ll mm <-> Forall2 R ll mm /\ Forall2 S ll mm.
Proof.
  split.
  induction 1; split; constructor; tauto.
  intros [H1 H2]; revert H1 H2.
  induction 1 as [ | x ll y mm H1 H2 IH ]; intros H; auto.
  apply Forall2_cons_inv in H; constructor; tauto.
Qed.

Fact Forall2_map_left X Y Z (R : Y -> X -> Prop) (f : Z -> Y) ll mm : Forall2 R (map f ll) mm <-> Forall2 (fun x y => R (f x) y) ll mm.
Proof.
  split.
  revert mm.
  induction ll; intros [ | y mm ] H; simpl in H; auto; try (inversion H; fail).
  apply Forall2_cons_inv in H; constructor. 
  tauto.
  apply IHll; tauto.
  induction 1; constructor; auto.
Qed.

Fact Forall2_map_right X Y Z (R : Y -> X -> Prop) (f : Z -> X) mm ll : Forall2 R mm (map f ll) <-> Forall2 (fun y x => R y (f x)) mm ll.
Proof.
  split.
  revert mm.
  induction ll; intros [ | y mm ] H; simpl in H; auto; try (inversion H; fail).
  apply Forall2_cons_inv in H; constructor. 
  tauto.
  apply IHll; tauto.
  induction 1; constructor; auto.
Qed.

Fact Forall2_map_both X Y X' Y' (R : X -> Y -> Prop) (f : X' -> X) (g : Y' -> Y) ll mm : Forall2 R (map f ll) (map g mm) <-> Forall2 (fun x y => R (f x) (g y)) ll mm.
Proof.
  rewrite Forall2_map_left, Forall2_map_right; split; auto.
Qed.

Fact Forall2_Forall X (R : X -> X -> Prop) ll : Forall2 R ll ll <-> Forall (fun x => R x x) ll.
Proof.
  split.
  induction ll as [ | x ll ]; inversion_clear 1; auto.
  induction 1; auto.
Qed.

Fact Forall2_map_Forall X Y (R : Y -> X -> Prop) (f : X -> Y) ll : Forall2 R (map f ll) ll <-> Forall (fun x => R (f x) x) ll.
Proof.
  rewrite Forall2_map_left, Forall2_Forall; split; auto.
Qed.

Fact Forall2_exchg X Y (R : X -> Y -> Prop) ll mm : Forall2 R ll mm <-> Forall2 (fun y x => R x y) mm ll.
Proof.
  split; induction 1; constructor; tauto.
Qed.

Section Forall2_comp.

  Variable (X Y Z : Type) (R : X -> Y -> Prop) (S : Y -> Z -> Prop).
  
  Fact Forall2_compose k l m : Forall2 R k l -> Forall2 S l m 
                            -> Forall2 (fun x z => exists y, R x y /\ S y z) k m.
  Proof.
    intros H; revert H m.
    induction 1 as [ | x y k l H1 H2 H3 ]; intros [ | z m ] H4.
    constructor.
    inversion H4.
    inversion H4.
    apply Forall2_cons_inv in H4.
    destruct H4 as (H4 & H5).
    constructor; auto.
    exists y; auto.
  Qed.

End Forall2_comp.

Fact Forall2_length X Y (R : X -> Y -> Prop) ll mm : Forall2 R ll mm -> length ll = length mm.
Proof.
  induction 1; simpl; f_equal; auto.
Qed.

Fact Forall2_eq X ll mm : Forall2 (@eq X) ll mm <-> ll = mm.
Proof.
  split.
  induction 1; f_equal; auto.
  intros; subst; apply Forall2_Forall.
  induction mm; simpl; auto.
Qed.

Fact Forall2_In_inv_left X Y (R : X -> Y -> Prop) ll mm : Forall2 R ll mm -> forall x, In x ll -> exists y, In y mm /\ R x y.
Proof.
  induction 1 as [ | a b ll mm H1 H2 IH2 ].
  intros ? [].
  intros x [ Hx | Hx ]; subst.
  exists b; simpl; auto.
  destruct (IH2 _ Hx) as (y & H3 & H4).
  exists y; simpl; auto.
Qed.

Fact Forall2_In_inv_right X Y (R : X -> Y -> Prop) ll mm : Forall2 R ll mm -> forall y, In y mm -> exists x, In x ll /\ R x y.
Proof.
  induction 1 as [ | a b ll mm H1 H2 IH2 ].
  intros ? [].
  intros x [ Hx | Hx ]; subst.
  exists a; simpl; auto.
  destruct (IH2 _ Hx) as (y & H3 & H4).
  exists y; simpl; auto.
Qed.  

Fact Forall2_impl_Forall2_incl X Y (R S : X -> Y -> Prop) ll mm : 
      Forall2 (fun x y => R x y -> S x y) ll mm 
   -> Forall2 R ll mm -> Forall2 S ll mm.
Proof.
  induction 1 as [ | x y ll mm H1 H2 H3 ]; simpl.
  intros; constructor.
  intros H; apply Forall2_cons_inv in H.
  constructor; tauto.
Qed.

Fact Forall2_impl X Y (R S : X -> Y -> Prop) : R inc2 S -> Forall2 R inc2 Forall2 S.
Proof. intros ? ? ?; induction 1; constructor; auto. Qed.

Fact Forall2_True X Y (R : X -> Y -> Prop) : (forall x y, R x y) -> forall ll mm, length ll = length mm -> Forall2 R ll mm.
Proof.
  intros HR.
  induction ll as [ | x ll IH ]; intros [ | y mm ]; try discriminate 1; intros H.
  constructor.
  injection H; clear H; intros H.
  constructor; auto.
Qed.

Fact Forall2_incl_map X Y (f : list X -> list Y) l m : 
       (forall u v, incl u v -> incl (f u) (f v))
    -> Forall2 (@incl _) l m 
    -> Forall2 (@incl _) (map f l) (map f m).
Proof.
  intro; induction 1; simpl; constructor; auto.
Qed.

Fact Forall2_comp X Y Z (R : X -> Y -> Prop) (S : Y -> Z -> Prop) : Forall2 R o Forall2 S inc2 Forall2 (R o S).
Proof.
  intros ? ? (mm & ? & ?); apply Forall2_compose with mm; auto.
Qed.

Fact Forall2_pfx A B (R : A -> B -> Prop) f g n : Forall2 R (pfx f n) (pfx g n) <-> forall i, i < n -> R (f i) (g i).
Proof.
  revert f g;
  induction n as [ | n IHn ]; intros f g; simpl.
  split; intros; auto; omega.
  split.
  intros H.
  apply Forall2_cons_inv in H.
  destruct H as [ H1 H2 ].
  intros [ | i ]; auto.
  intros; apply IHn with (f := fun n => f (S n)) (g := fun n => g (S n)); auto; omega.
  intros H; constructor.
  apply H; omega.
  apply IHn with (f := fun n => f (S n)) (g := fun n => g (S n)).
  intros; apply H; omega.
Qed.

Section Forall2_tools.

  Variables (X Y : Type) (P : X -> Prop) (Q : Y -> Prop) (R S : relation X) (T : X -> Y -> Prop).

  Fact Forall2_Forall_left ll mm : Forall2 (fun x y => P x -> T x y) ll mm -> Forall P ll -> Forall2 T ll mm.
  Proof.
    induction 1 as [ | x y ll mm H1 IH ]; intros H2.
    constructor.
    apply Forall_cons_inv in H2; destruct H2.
    constructor; auto.
  Qed.

  Fact Forall2_Forall_right ll mm : Forall2 (fun x y => Q y -> T x y) ll mm -> Forall Q mm -> Forall2 T ll mm.
  Proof.
    induction 1 as [ | x y ll mm H1 IH ]; intros H2.
    constructor.
    apply Forall_cons_inv in H2; destruct H2.
    constructor; auto.
  Qed.

  Fact Forall_Forall2 ll : Forall (fun x => R x x) ll <-> Forall2 R ll ll.
  Proof.
    split.
    induction 1; constructor; auto.
    induction ll; intros H; constructor; inversion_clear H; auto.
  Qed.

  Fact Forall2_sym : symmetric _ R -> symmetric _ (Forall2 R).
  Proof. intros ? ? ?; induction 1; auto. Qed.

  Fact Forall2_trans : transitive _ R -> transitive _ (Forall2 R).
  Proof.
    intros HR ll mm kk H1; revert kk. 
    induction H1 as [ | x y ll mm H1 H2 IH ]; intros kk H3; auto.
    inversion_clear H3; constructor; auto.
    apply HR with (1 := H1); auto.
  Qed.
  
  Fact Forall2_Forall_Forall ll mm :
         (forall x y, T x y -> P x -> Q y)
      -> Forall2 T ll mm 
      -> Forall P ll
      -> Forall Q mm.
    Proof.
      intros H.
      induction 1 as [ | x y ll mm H1 H2 IH2 ]; intros Hll.
      constructor.
      apply Forall_cons_inv in Hll; destruct Hll as [ Hx Hll ].
      constructor; auto.
      revert Hx; apply H; auto.
    Qed.
  
  Fact Forall2_perm_comm ll mm kk : Forall2 R ll mm -> Permutation mm kk -> exists ll', Permutation ll ll' /\ Forall2 R ll' kk.
  Proof.
    intros H1; revert kk.
    induction H1; intros kk Hkk.
    apply Permutation_nil in Hkk; subst.
    exists nil; auto.
    destruct Permutation_In_inv with (1 := Hkk) (x := y) as (l'' & r'' & ?); subst.
    left; auto.
    apply Permutation_app_inv with (l1 := nil) in Hkk; simpl in Hkk.
    apply IHForall2 in Hkk.
    destruct Hkk as (l1 & H2 & H3).
    apply Forall2_app_inv_r in H3.
    destruct H3 as (l2 & l3 & H3 & H4 & ?); subst.
    exists (l2++x::l3); split.
    apply Permutation_add_one with (l1 := nil); auto.
    apply Forall2_app; auto.
  Qed.

  Variable (f : X -> list Y).

  Fact Forall2_In_map_impl ll mm ts : 
              Forall2 (fun x y => forall t, In x (f t) -> In y (f t)) ll mm       
           -> Forall2 (@In _) ll (map f ts) 
           -> Forall2 (@In _) mm (map f ts).
  Proof.
    intros H; revert ts.
    induction H.
    auto.
    intros [ | t ts ].
    inversion 1.
    simpl.
    inversion_clear 1; constructor; auto.
  Qed.

End Forall2_tools.

Fact Forall2_left_Forall X Y (P : X -> Prop) lx ly : Forall2 (fun x (_ : Y) => P x) lx ly <-> Forall P lx /\ length lx = length ly.
Proof.
  split.
  intros H; split.
  induction H; constructor; auto.
  revert H; apply Forall2_length.
  intros (H1 & H2); revert ly H2.
  induction H1; intros [ | ] H2; try discriminate H2; constructor; auto.
Qed. 

Fact Forall2_right_Forall X Y (P : Y -> Prop) lx ly : Forall2 (fun (_ : X) y => P y) lx ly <-> Forall P ly /\ length lx = length ly.
Proof.
  split.
  intros H; split.
  induction H; constructor; auto.
  revert H; apply Forall2_length.
  intros (H1 & H2); revert lx H2.
  induction H1; intros [ | ] H2; try discriminate H2; constructor; auto.
Qed. 

Fact Forall2_cond_left X Y (P : X -> Prop) (R : X -> Y -> Prop) ll mm : 
  Forall P ll -> Forall2 (fun x y => P x -> R x y) ll mm -> Forall2 R ll mm. 
Proof.
  intros H1 H2.
  apply (Forall2_impl_Forall2_incl _ H2).
  apply Forall2_left_Forall; split; auto.
  apply Forall2_length with (1 := H2).
Qed.

Fact Forall2_cond_right X Y (P : Y -> Prop) (R : X -> Y -> Prop) ll mm : 
  Forall P mm -> Forall2 (fun x y => P y -> R x y) ll mm -> Forall2 R ll mm. 
Proof.
  intros H1 H2.
  apply (Forall2_impl_Forall2_incl _ H2).
  apply Forall2_right_Forall; split; auto.
  apply Forall2_length with (1 := H2).
Qed.

Fact map_eq_Forall2 X Y Z (g1 : X -> Z) (g2 : Y -> Z) ll mm : map g1 ll = map g2 mm <-> Forall2 (fun x y => g1 x = g2 y) ll mm.
Proof.
  split.
  revert mm.
  induction ll as [ | x ll IH ]; intros [ | y mm ]; intros H; try discriminate H;
  constructor.
  injection H; auto.
  apply IH.
  injection H; auto.
  induction 1; simpl; f_equal; auto.
Qed.

Fact Forall2_list_In_map X Y Z (R : Y -> Z -> Prop) ll f g : (forall (x : X) (H : In x ll), R (f x H) (g x H)) <-> Forall2 R (list_In_map ll f) (list_In_map ll g). 
Proof.
  split.
  induction ll; simpl; auto.
  revert f g;
  induction ll; simpl; intros f g.
  intros _ _ [].
  intros H.
  apply Forall2_cons_inv in H.
  destruct H as ( H1 & H2 ).
  intros x [ Hx | Hx ]. 
  subst x; auto.
  apply IHll with (1 := H2). 
Qed.

Fact Forall2_list_In_t_map X Y Z (R : Y -> Z -> Prop) ll f g : (forall (x : X) (H : In_t x ll), R (f x H) (g x H)) <-> Forall2 R (list_In_t_map ll f) (list_In_t_map ll g). 
Proof.
  split.
  induction ll; simpl; auto.
  revert f g;
  induction ll; simpl; intros f g.
  intros _ _ [].
  intros H.
  apply Forall2_cons_inv in H.
  destruct H as ( H1 & H2 ).
  intros x [ Hx | Hx ]. 
  subst x; auto.
  apply IHll with (1 := H2). 
Qed.

Fact Forall2_to_list_In_t_map X Y (R : X -> Y -> Prop) l m : 
          Forall2 R l m 
       -> { f : forall x, In_t x l -> Y 
              | m = list_In_t_map l f 
             /\ forall x Hx, R x (f x Hx) }.
Proof.
  revert m.
  induction l as [ | x l IH ]; intros [ | y m ] H; try (exfalso; inversion H; fail).
  exists (fun x Hx => @False_rect _ Hx); split; auto; intros ? [].
  apply Forall2_cons_inv in H; destruct H as (H1 & H2).
  destruct (IH _ H2) as (f & Hf1 & Hf2).
  exists (fun x Hx => match Hx with inl _ => y | inr Hx => f _ Hx end); split.
  simpl; f_equal; apply Hf1.
  intros z [ Hz | Hz ]; simpl.
  subst; auto.
  apply Hf2.
Qed.

Fact Forall2_combine X Y (R : X -> Y -> Prop) l m : 
          Forall2 R l m -> Forall (fun c => R (fst c) (snd c)) (combine l m).
Proof.
  induction 1; simpl; constructor; auto.
Qed.

Fact Forall2_combine_In X Y (R : X -> Y -> Prop) l m : 
          Forall2 R l m -> forall x, In x l -> exists c, In c (combine l m) /\ fst c = x.
Proof.
  induction 1 as [ | x y l m H1 H2 IH2 ]; simpl; intros z.
  intros [].
  intros [ ? | H ].
  subst z; exists (x,y); tauto.
  destruct (IH2 _ H) as (c & H3 & H4).
  exists c; tauto.
Qed.

Section analysis_fun.

  Variable (X Y : Type) (P : X -> Prop) (f : X -> Y).
  
  Fact Forall2_analysis lx ly : Forall2 (fun x y => P x /\ f x = y) lx ly
                              <-> Forall P lx /\ map f lx = ly.
  Proof.
    rewrite Forall2_conj.
    rewrite Forall2_left_Forall.
    rewrite <- Forall2_map_left, Forall2_eq.
    split; try tauto.
    intros (? & ?); subst; rewrite map_length; auto.
  Qed.
    
End analysis_fun.        

Section list_sup.

  Variables (X : Type) 
            (P : nat -> X -> Prop) (P_mono : forall n x, P n x -> P (S n) x)
            (R : nat -> relation X) (R_mono : forall n, R n inc2 R (S n)).

  Let P_monotonic n m : n <= m -> forall x, P n x -> P m x.
  Proof.
    induction 1; intros; auto.
  Qed.

  Let R_monotonic n m : n <= m -> R n inc2 R m.
  Proof.
    induction 1; intros; auto.
  Qed.

  Fact list_Forall_sup ll : (forall x, In x ll -> exists n, P n x) -> exists n, forall x, In x ll -> P n x.
  Proof.
    induction ll as [ | x ll IH ]; intros H.
    exists 0; intros ? [].
    destruct (H x) as (n1 & H1).
    left; auto.
    destruct IH as (n2 & H2).
    intros; apply H; right; auto.
    exists (n1+n2); intros y [ Hy | Hy ].
    subst; revert H1; apply P_monotonic, le_plus_l.
    generalize (H2 _ Hy); apply P_monotonic, le_plus_r.
  Qed.

  Fact list_Forall2_mono Y Z (S T : Y -> Z -> Prop) : S inc2 T -> Forall2 S inc2 Forall2 T.
  Proof.
    intros ? ? ?; induction 1; constructor; auto.
  Qed.

  Fact list_Forall2_sup ll mm : Forall2 (fun x y => exists n, R n x y) ll mm -> exists n, Forall2 (R n) ll mm.
  Proof.
    induction 1 as [ | x y ll mm (n1 & H1) _ (n2 & IH2) ].
    exists 0; auto.
    exists (n1+n2); constructor.
    revert H1; apply R_monotonic, le_plus_l.
    revert IH2; apply list_Forall2_mono, R_monotonic, le_plus_r.
  Qed.

End list_sup.            

Fact Forall2_w_continuous X K ll mm : @seq_increasing X K -> Forall2 (fun x y => exists n, K n x y) ll mm -> exists n, Forall2 (K n) ll mm.
Proof.
  intros HK.
  induction 1 as [ | x y ll mm (n & Hn) H2 (m & Hm) ].
  exists 0; constructor.
  exists (n+m); constructor.
  revert Hn; apply seq_inc_all; auto; omega.
  revert Hm; apply Forall2_impl, seq_inc_all; auto; omega.
Qed.

Section Exists2.

  Variable (X Y : Type) (R : X -> Y -> Prop).

  Inductive Exists2 : list X -> list Y -> Prop :=
    | Exists2_start : forall x y l m, R x y -> length l = length m -> Exists2 (x::l) (y::m)
    | Exists2_cont  : forall x y l m, Exists2 l m -> Exists2 (x::l) (y::m).

  Fact Exists2_length l m : Exists2 l m -> length l = length m.
  Proof.
    induction 1; simpl; auto.
  Qed.

  Fact Exists2_nil_inv : ~ Exists2 nil nil.
  Proof. inversion 1. Qed.

  Fact Exists2_cons_inv x y l m : Exists2 (x::l) (y::m) -> R x y \/ Exists2 l m.
  Proof.
    inversion_clear 1; tauto.
  Qed.

  Fact Exists2_In ll mm : Exists2 ll mm -> exists x y, In x ll /\ In y mm /\ R x y.
  Proof.
    induction 1 as [ x y | a b ll mm _ (x & y & H1 & H2 & H3) ].
    exists x, y; simpl; auto.
    exists x, y; simpl; auto.
  Qed.

End Exists2.

Fact Exists2_inc X Y (R S : X -> Y -> Prop) : R inc2 S -> Exists2 R inc2 Exists2 S.
Proof.
  intros H ll mm.
  induction 1.
  constructor 1; auto.
  constructor 2; auto.
Qed.

Fact Exists2_exists_left X Y R ll mm : @Exists2 X Y (fun x _ => R x) ll mm <-> length ll = length mm /\ exists x, In x ll /\ R x.
Proof.
  split.
  induction 1 as [ | x y l m H1 (H2 & z & H3 & H4) ].
  split. 
  simpl; f_equal; auto.
  exists x; simpl; auto.
  split.
  simpl; f_equal; auto.
  exists z; simpl; auto.
  intros (H1 & x & H2 & H3).
  revert mm H1.
  induction ll as [ | z ll IH ].
  destruct H2.
  intros [ | y mm ] Hmm.
  discriminate Hmm.
  simpl in Hmm; injection Hmm; clear Hmm; intros Hmm.
  destruct H2 as [ H2 | H2 ].
  subst; constructor 1; auto.
  constructor 2; auto.
Qed.

Fact Exists2_exists_right X Y R ll mm : @Exists2 X Y (fun _ y => R y) ll mm <-> length ll = length mm /\ exists y, In y mm /\ R y.
Proof.
  split.
  induction 1 as [ | x y l m H1 (H2 & z & H3 & H4) ].
  split. 
  simpl; f_equal; auto.
  exists y; simpl; auto.
  split.
  simpl; f_equal; auto.
  exists z; simpl; auto.
  intros (H1 & y & H2 & H3).
  revert ll H1.
  induction mm as [ | z mm IH ].
  destruct H2.
  intros [ | x ll ] Hll.
  discriminate Hll.
  simpl in Hll; injection Hll; clear Hll; intros Hll.
  destruct H2 as [ H2 | H2 ].
  subst; constructor 1; auto.
  constructor 2; auto.
Qed.

Section Forall2_Exists2.

  Variable (X Y : Type) (R S : X -> Y -> Prop).
  
  Fact Forall2_decide_ind ll mm : Forall2 (R cup2 S) ll mm -> Forall2 R ll mm \/ Exists2 S ll mm.
  Proof.
    induction 1 as [ | x y ll mm [ H1 | H1 ] H2 [ H3 | H3 ] ].
    left; constructor.
    left; constructor; auto.
    right; constructor 2; auto.
    right; constructor 1; auto.
    apply Forall2_length with (1 := H2); auto.
    right; constructor 2; auto.
  Qed.

End Forall2_Exists2.

Section Forall2_dec.

  Variable (X Y : Type).
  
  Implicit Types (R S : X -> Y -> Prop).
  
  Fact Forall2_choose_t R S ll mm : (forall x y, In_t x ll -> In_t y mm -> { R x y } + { S x y })
                           -> length ll = length mm -> { Forall2 R ll mm } + { Exists2 S ll mm }.
  Proof.
    revert mm.
    induction ll as [ | x ll IHll ]; intros [ | y mm ] HRS H.
    left; constructor.
    discriminate H.
    discriminate H.
    simpl in H; injection H; clear H; intros H.
    destruct (IHll mm) as [ H1 | H1 ]; auto.
    intros; apply HRS; right; auto.
    destruct (HRS x y); try (left; auto; fail).
    right; constructor 1; auto.
    right; constructor 2; auto.
  Qed.

  Fact Forall2_dec_t R ll mm :  (forall x y, In_t x ll -> In_t y mm -> { R x y } + { ~ R x y })
                           -> { Forall2 R ll mm } + { ~ Forall2 R ll mm }.
  Proof.
    intros H1.
    destruct (eq_nat_dec (length ll) (length mm)) as [ H2 | H2 ].
    destruct (Forall2_choose_t _ _ _ _ H1 H2) as [ | C ].
    left; auto.
    right; intros H.
    clear H1 H2.
    induction H.
    apply Exists2_nil_inv in C; auto.
    apply Exists2_cons_inv in C.
    destruct C; tauto.
    right; contradict H2; revert H2; apply Forall2_length.
  Qed.
  
  Fact Forall2_dec R ll mm :  (forall x y, In x ll -> In y mm -> { R x y } + { ~ R x y })
                           -> { Forall2 R ll mm } + { ~ Forall2 R ll mm }.
  Proof.
    intros H; apply Forall2_dec_t.
    intros; apply H; apply In_t_In; auto.
  Qed.

  Fact Exists2_dec_t R ll mm :  (forall x y, In_t x ll -> In_t y mm -> { R x y } + { ~ R x y })
                           -> { Exists2 R ll mm } + { ~ Exists2 R ll mm }.
  Proof.
    intros H1.
    destruct (eq_nat_dec (length ll) (length mm)) as [ H2 | H2 ].
    assert (forall x y, In_t x ll -> In_t y mm -> { ~ R x y } + { R x y }) as H3.
      intros x y Hx Hy; destruct (H1 _ _ Hx Hy); tauto.
    destruct (Forall2_choose_t _ _ _ _ H3 H2) as [ C | C ].
    
    right.
    clear H1 H2 H3.
    induction C as [ | a b ll mm H1 H2 H3 ].
    apply Exists2_nil_inv.
    contradict H3.
    apply Exists2_cons_inv in H3; tauto.
    
    left; auto.
    
    right.
    contradict H2; revert H2.
    apply Exists2_length.
  Qed.
  
  Fact Exists2_dec R ll mm :  (forall x y, In x ll -> In y mm -> { R x y } + { ~ R x y })
                           -> { Exists2 R ll mm } + { ~ Exists2 R ll mm }.
  Proof.
    intros H; apply Exists2_dec_t.
    intros; apply H; apply In_t_In; auto.
  Qed.
  
End Forall2_dec.

Section Forall3. 

  Variable (X Y Z : Type).
  
  Implicit Type (R S : X -> Y -> Z -> Prop) (lx : list X).
  
  Inductive Forall3 R : list X -> list Y -> list Z -> Prop :=
    | in_Forall3_nil  : Forall3 R nil nil nil
    | in_Forall3_cons : forall x lx y ly z lz, R x y z 
                                            -> Forall3 R lx ly lz 
                                            -> Forall3 R (x::lx) (y::ly) (z::lz).

  Inductive Exists3 R : list X -> list Y -> list Z -> Prop :=
    | Exists3_start : forall x lx y ly z lz, R x y z 
                                          -> length lx = length ly
                                          -> length lx = length lz
                                          -> Exists3 R (x::lx) (y::ly) (z::lz)
    | Exists3_cont : forall x lx y ly z lz, Exists3 R lx ly lz 
                                         -> Exists3 R (x::lx) (y::ly) (z::lz).
    
  Fact Forall3_inc R S li : Forall (fun i => R i inc2 S i) li
                         -> Forall3 R li inc2 Forall3 S li.
  Proof.
    induction 1 as [ | i li H1 H2 ]; auto.
    intros [ | x lx ] [ | y ly ]; try (inversion 1; fail); constructor.
    intros [ | x lx ] [ | y ly ]; try (inversion 1; fail).
    inversion_clear 1.
    constructor; auto.
  Qed.
  
  Fact Forall3_length R lx ly lz : Forall3 R lx ly lz -> length lx = length ly /\ length lx = length lz.
  Proof.
    induction 1 as [ | x lx y ly z lz H1 H2 (H3 & H4) ]; simpl; auto.
  Qed.
  
  Fact Forall3_cup R S lx ly lz : Forall3 (fun i => R i cup2 S i) lx ly lz 
                               -> Forall3 R lx ly lz \/ Exists3 S lx ly lz.
  Proof.
    induction 1 as [ | x lx y ly z lz H1 H2 H3 ].
    left; constructor.
    destruct H1; destruct H3.
    left; constructor; auto.
    right; constructor 2; auto.
    apply Forall3_length in H2; destruct H2.
    right; constructor 1; auto.
    right; constructor 2; auto.
  Qed.

  Fact Forall3_Forall2_first K lx ly lz : Forall3 (fun _ => K) lx ly lz 
                                       -> Forall2 K ly lz.
  Proof.
    induction 1; simpl; constructor; auto.
  Qed.
  
  Fact Exists3_Exists2_last R lx ly lz : 
                Exists3 R lx ly lz 
             -> exists z, In z lz /\ Exists2 (fun x y => R x y z) lx ly.
  Proof.
    induction 1 as [ x lx y ly z lz H1 H2 H3 
                   | x lx y ly z lz H1 H2 ].
    exists z; simpl; split; try tauto.
    constructor 1; auto.
    destruct H2 as (z' & H2 & H3).
    exists z'; simpl; split; try tauto.
    constructor 2; auto.
  Qed.

End Forall3.
