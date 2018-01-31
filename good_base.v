(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List Omega.

Require Import tacs.

Require Import rel_utils.
Require Import list_utils.
Require Import sublist.

Set Implicit Arguments.

Section Ge_Good.

  Variables (A : Type) (R : A -> A -> Prop).

  Infix "<<" := R (at level 70).

  Definition Ge_ex a w := exists x, In x w /\ x << a.
  Definition Ge_fa a w := forall x, In x w -> x << a.
  Definition Ge_ex_fa a lw := exists w, In w lw /\ Ge_fa a w.
  Definition Ge_fa_fa a lw := forall w, In w lw -> Ge_fa a w.

  Fixpoint Incr w :=
    match w with
      | nil   => True
      | a::w  => Ge_fa a w /\ Incr w
    end.

  Fact Incr_spec w : Incr w <-> forall l a r, w = l++a::r -> Ge_fa a r.
  Proof.
    split.

    induction w as [ | b w IH ]; intros H [ | x l ] a r E; try discriminate E; simpl in E;
    injection E; clear E; intros; subst; simpl in H; auto.
    apply H.
    destruct H as [ _ H ]; apply (IH H) with (1 := eq_refl).
    
    intros H.
    induction w as [ | x w IH ]; simpl in H |- *; auto; split.
    apply H with (l := nil); auto.
    apply IH.
    intros l a r ?; apply (H (x::l)); simpl; f_equal; auto.
  Qed.  

  Fact Ge_ex_sg a b : Ge_ex a (b::nil) <-> b << a.
  Proof.
    split.
    intros (? & [ | [] ] & ?); subst; auto.
    exists b; split; auto; left; auto.
  Qed.

  Fact Ge_fa_sg a b : Ge_fa a (b::nil) <-> b << a.
  Proof.
    split.
    intros H; apply H; left; auto.
    intros ? ? [ ? | [] ]; subst; auto.
  Qed.

  Fact Ge_ex_fa_sg a w : Ge_ex_fa a (w::nil) <-> Ge_fa a w.
  Proof.
    split.
    intros (? & [ | [] ] & ?); subst; auto.
    exists w; split; auto; left; auto.
  Qed.

  Fact Ge_ex_fa_app a ll mm : Ge_ex_fa a (ll++mm) <-> (Ge_ex_fa a ll \/ Ge_ex_fa a mm).
  Proof.
    split.
    intros (x & H1 & H2).
    apply in_app_or in H1.
    destruct H1; [ left | right ]; exists x; auto.
    intros [ (x & ? & ?) | (x & ? & ?) ]; exists x; split; auto; 
      apply in_or_app; [ left | right ]; auto.
  Qed.

  Inductive good : list A -> Prop := 
    | in_good_0 : forall ll a b, In b ll -> b << a -> good (a::ll)
    | in_good_1 : forall ll a, good ll -> good (a::ll).

  Inductive bad : list A -> Prop :=
    | in_bad_0 : bad nil
    | in_bad_1 : forall ll a, (forall b, In b ll -> ~ b << a) -> bad ll -> bad (a::ll).
    
  Fact good_mono a ll : good ll -> good (a::ll).
  Proof.
    constructor 2; auto.
  Qed.

  Fact good_nil_inv : ~ good nil.
  Proof. intros H; inversion H. Qed.

  Fact good_cons_inv a ll : good (a::ll) -> Ge_ex a ll \/ good ll.
  Proof. 
    intros H; inversion_clear H.
    left; exists b; auto.
    right; auto.
  Qed.

  Fact good_sg_inv a : ~ good (a::nil).
  Proof.
    intros H; apply good_cons_inv in H.
    destruct H as [ (? & [] & _ ) | H ].
    revert H; apply good_nil_inv.
  Qed.

  Fact good_cons_not_inv a ll : good (a::ll) -> ~ good ll -> Ge_ex a ll.
  Proof.
    intros H ?; apply good_cons_inv in H; tauto.
  Qed.

  Fact good_two_inv a b : good (a::b::nil) -> b << a.
  Proof.
    intros H.
    apply good_cons_inv in H.
    destruct H as [ H | H ].
    apply Ge_ex_sg in H; auto.
    apply good_sg_inv in H; destruct H.
  Qed.

  Fact good_bad_False ll : good ll -> bad ll -> False.
  Proof.
    induction 1 as [ ll a b H1 H2 | ll a Hll IH ].
    inversion_clear 1.
    apply H0 with (1 := H1); auto.
    inversion_clear 1; auto.
  Qed.

  Fact not_good_eq_bad ll : ~ good ll <-> bad ll.
  Proof.
    split.

    induction ll; intros H.
    constructor.
    constructor.
    intros; contradict H.
    constructor 1 with (1 := H0); auto.
    apply IHll; contradict H.
    constructor 2; auto.
    
    intros ? ?; apply good_bad_False with ll; auto.
  Qed.

  Fact good_or_bad_implies_dec : (forall ll, { good ll } + { bad ll }) -> (forall x y, { x << y } + { ~ x << y }).
  Proof.
    intros H x y.
    destruct (H (y::x::nil)).
    left.
    inversion_clear g.
    destruct H0 as [ | [] ]; subst; tauto.
    inversion_clear H0.
    destruct H1.
    inversion_clear H1.
    right.
    inversion_clear b.
    apply H0; left; auto.
  Qed.
 
  Fact good_sublist ll mm : ll <sl mm -> good ll -> good mm.
  Proof.
    induction 1 as [ mm | a ll mm H IH | a ll mm H IH ].
    intros H; inversion H.
    intros H'; apply good_cons_inv in H'.
    destruct H' as [ (b & H1 & H2) | H' ].
    constructor 1 with b; auto.
    apply sl_In with (1 := H); auto.
    constructor 2; auto.
    constructor 2; auto.
  Qed.

  Fact good_app_left ll mm : good mm -> good (ll++mm).
  Proof.
    apply good_sublist, sl_app_left.
  Qed.

  Fact good_app_right ll mm : good ll -> good (ll++mm).
  Proof.
    apply good_sublist, sl_app_right.
  Qed.

  Fact good_pfx_rev f a b : a <= b -> good (pfx_rev f a) -> good (pfx_rev f b).
  Proof.
    intros H.
    rewrite (le_plus_minus _ _ H), plus_comm, pfx_rev_plus.
    apply good_app_left.
  Qed.
 
  Fact good_inv ll : good ll <-> exists l a m b r, ll = l++a::m++b::r /\ b << a.
  Proof.
    split.

    induction 1 as [ ll a b Hll H1 | ll x Hll IH ].
    apply in_split in Hll; destruct Hll as ( m & r & H2 ).
    exists nil, a, m, b, r; subst; auto.
    destruct IH as (l & a & m & b & r & H1 & H2).
    exists (x::l), a, m, b, r; subst; auto.
    
    intros (l & a & m & b & r & H1 & H2); subst.
    apply good_app_left.
    constructor 1 with b; auto.
    apply in_or_app; right; left; auto.
  Qed.

  Fact good_pfx_rev_eq n f : good (pfx_rev f n) <-> exists i j, i < j < n /\ R (f i) (f j).
  Proof.
    rewrite good_inv; split.
    
    intros (l & a & m & b & r & H1 & H2).
    exists (length r), (length (m++b::r)); split.
    apply f_equal with (f := @length _) in H1.
    rewrite pfx_rev_length in H1.
    rewrite H1.
    do 3 (rewrite app_length; simpl); split; omega.
    rewrite pfx_rev_eq with (1 := H1).
    cutrewrite (l++a::m++b::r = (l++a::m)++b::r) in H1.
    rewrite pfx_rev_eq with (1 := H1); auto.
    rewrite app_ass; simpl; auto.
    
    intros (i & j & (H1 & H2) & H3).
    exists (pfx_rev (fun x => f (S j + x)) (n - S j)), 
           (f j), 
           (pfx_rev (fun x => f (S i + x)) (j - S i)),
           (f i),
           (pfx_rev f i).
    split; auto.
    assert (n = (n - S i) + S i) as H; try omega.
    rewrite H at 1.
    rewrite pfx_rev_plus; simpl.
    assert (n - S i = (n - S j) + S (j - S i)) as H'; try omega.
    rewrite H' at 1.
    rewrite pfx_rev_plus; simpl.
    rewrite app_ass; simpl.
    f_equal.
    apply pfx_rev_ext; intros; f_equal; omega.
    f_equal.
    f_equal; omega.
  Qed.
  
  Fact good_pfx_eq n f : good (pfx f n) <-> exists i j, i < j < n /\ R (f j) (f i).
  Proof.    
    rewrite <- (rev_involutive (pfx f n)).
    rewrite <- pfx_pfx_rev_eq.
    rewrite pfx_rev_minus.
    rewrite <- pfx_pfx_rev_eq.
    rewrite good_pfx_rev_eq.
    split; intros (i & j & H1 & H2).
    exists (n - S j), (n - S i); split; auto; omega.
    exists (n - S j), (n - S i); split.
    omega.
    replace_with H2; f_equal; omega.
  Qed.
    
  Fact exists_good_app ll mm : (exists a b, In a ll /\ In b mm /\ R b a) -> good (ll++mm).
  Proof.
    intros (a & b & H1 & H2 & H3).
    revert a H1 b H2 H3.
    induction ll as [ | x ll IHll ].
    intros ? [].
    intros a [ ? | Ha ] b Hb ?; subst; simpl.
    constructor 1 with b; auto; apply in_or_app; tauto.
    constructor 2; apply IHll with (1 := Ha) (2 := Hb); auto.
  Qed.

  Fact good_app_inv ll mm : good (ll++mm) -> good ll
                                          \/ good mm
                                          \/ exists a b, In a ll /\ In b mm /\ b << a.
  Proof.
    induction ll as [ | x ll IH ]; simpl.
    tauto.
    intros H.
    apply good_cons_inv in H.
    destruct H as [ (a & H1 & H2) | H ].
    apply in_app_or in H1; destruct H1 as [ H1 | H1 ].
    left; constructor 1 with a; auto.
    right; right; exists x, a; tauto.
    apply IH in H.
    destruct H as [ H | [ H | (a & b & H1 & H2 & H3) ] ].
    left; constructor 2; auto.
    tauto.
    right; right; exists a, b; tauto.
  Qed.   

  Fact good_eq_exists ll : good ll <-> exists l a m b r, ll = l++a::m++b::r /\ b << a.
  Proof.
    apply good_inv.
  Qed.

  Fact sublist_good_eq ll : good ll <-> exists a b, R b a /\ a::b::nil <sl ll.
  Proof.
    split.

    induction 1 as [ l a b H1 H2 | l b H (u & v & H1 & H2)].
    exists a, b; split; auto; constructor 2; apply In_sl; auto.
    exists u, v; split; auto; constructor 3; auto.
   
    intros (a & b & H1 & H2).
    apply good_sublist with (1 := H2).
    constructor 1 with b; auto; left; auto.
  Qed.

  Section decision_procedures.

    Variable Rdec : forall x y, { x << y } + { ~ x << y }.
    
    Definition Ge_ex_dec a w : { Ge_ex a w } + { ~ Ge_ex a w }.
    Proof.
      destruct list_dec_rec with (P := fun x => x << a) (ll := w) 
        as [ (x & H1 & H2) | H ]; simpl; auto.
      left; exists x; auto.
      right; intros (x & H1 & H2); apply H with (1 := H1); auto.
    Qed.

    Definition Ge_fa_dec a w : { Ge_fa a w } + { ~ Ge_fa a w }.
    Proof.
      destruct list_dec_rec with (P := fun x => ~ x << a) (ll := w) 
        as [ (x & H1 & H2) | H ]; simpl; auto.
      intros x; destruct (Rdec x a); tauto.
      left; intros z Hz.
      destruct (Rdec z a) as [ | C ]; try tauto.
      apply H in C; tauto.
    Qed.

    Definition Ge_ex_fa_dec a lw : { Ge_ex_fa a lw } + { ~ Ge_ex_fa a lw }.
    Proof.
      destruct list_dec_rec with (P := fun w => Ge_fa a w) (ll := lw) 
        as [ (w & H1 & H2) | H ]; auto.
      intros; apply Ge_fa_dec.
      left; exists w; auto.
      right; intros (x & H1 & H2).
      revert H2; apply H; auto.
    Qed.

    Fact Ge_ex_fa_app_dec a ll mm : Ge_ex_fa a (ll++mm) -> { Ge_ex_fa a ll } + { Ge_ex_fa a mm }.
    Proof.
      intros H.
      rewrite Ge_ex_fa_app in H.
      destruct (Ge_ex_fa_dec a ll); 
      destruct (Ge_ex_fa_dec a mm); tauto.
    Qed.

    Definition good_bad_dec ll : { good ll } + { bad ll }.
    Proof.
      induction ll as [ | x ll [ IH | IH ] ].
      right; constructor 1.
      left; constructor 2; auto.
      destruct (list_dec_rec (fun y => y << x) ll) as [ (y & H1 & H2) | H ].
      intros; apply Rdec.
      left; constructor 1 with (1 := H1); auto.
      right; constructor; auto.
    Qed.

    Definition good_dec ll : { good ll } + { ~ good ll }.
    Proof. 
      destruct (good_bad_dec ll); [ left | right ]; auto.
      rewrite not_good_eq_bad; auto.
    Qed.

  End decision_procedures.

  Fact sublist_good ll mm : ll <sl mm -> good ll -> good mm.
  Proof.
    induction 1 as [ mm | x ll mm H IH | x ll mm H IH ]; intros H1.
    apply good_nil_inv in H1; tauto.
    apply good_cons_inv in H1; destruct H1 as [ (y & H1 & H2) | H1 ].
    constructor 1 with y; auto.
    apply sl_In with (1 := H); auto.
    constructor 2; auto.
    constructor 2; auto.
  Qed.

  (* From Fridlender Thesis *)

  Definition ctxt ll a1 a2 := good ll \/ Ge_ex a1 ll \/ a1 << a2.

  Fact ctxt_nil a1 a2 : ctxt nil a1 a2 <-> a1 << a2.
  Proof.
    split.
    intros [ H | [ H | H ] ]; auto.
    apply good_nil_inv in H; tauto.
    destruct H as (? & [] & _).
    right; right; auto.
  Qed.
  
  Fact ctxt_cons a ll a1 a2 : ctxt (a::ll) a1 a2 <-> ctxt ll a1 a2 \/ ctxt ll a a1.
  Proof.
    split.

    intros [ H | [ H | H ] ]; auto.
    apply good_cons_inv in H.
    destruct H as [ H | H ].
    right; right; left; auto.
    right; left; auto.
    destruct H as (x & [ H | H ] & H1); subst.
    right; right; right; auto.
    left; right; left; exists x; auto.
    left; right; right; auto.
    
    intros [ H | H ]; revert H; intros  [ H | [ H | H ] ].

    left; constructor 2; auto.
    destruct H as ( x & H1 & H2 ).
    right; left; exists x; split; auto; right; auto.
    right; right; auto.    
    
    left; constructor 2; auto.
    destruct H as ( x & H1 & H2 ).
    left; constructor 1 with x; auto.
    right; left; exists a; split; auto; left; auto.   

  Qed.

  (* this looks very much like Coquand lift_rel *)

  Fact lift_rel_list_ctxt ll : R lrlift ll ~eq2 ctxt ll.
  Proof.
    induction ll as [ | a ll IH ]; simpl; split; intros u v;
    (rewrite ctxt_nil || rewrite ctxt_cons); auto; unfold lift_rel;
    intros [ | ]; [ left | right | left | right ]; apply IH; auto.
  Qed.
  
End Ge_Good.

Fact good_inc X (R S : X -> X -> Prop) : R inc2 S -> good R inc1 good S.
Proof.
  intros H ll.
  induction 1 as [ ll a b Hll Hab | ].
  constructor 1 with (1 := Hll); auto.
  constructor 2; auto.
Qed.

Section good_map.
  
  Variable (X Y : Type) (f : X -> Y) (R : X -> X -> Prop) (S : Y -> Y -> Prop) 
           (HRS2 : forall x y, S (f x) (f y) -> R x y)
           (HRS1 : forall x y, R x y -> S (f x) (f y)).

  Fact good_map_inv ll : good S (map f ll) -> good R ll.
  Proof.
    set (ll' := map f ll).
    generalize (eq_refl ll').
    unfold ll' at 2.
    intros H1 H2.
    generalize ll' H2 ll H1.
    clear ll ll' H1 H2.
    induction 1 as [ ll' a b Hll Hab | ll' a H1 IH ]; intros [ | x ll ] Hll'; try discriminate Hll'; 
      simpl in Hll'; injection Hll'; clear Hll'; intros; subst.
    apply in_map_iff in Hll.
    destruct Hll as (y & H1 & H2); subst.
    constructor 1 with y; auto.
    specialize (IH _ eq_refl).
    constructor 2; auto.
  Qed.
  
  Fact good_map ll : good R ll -> good S (map f ll).
  Proof.
    induction 1 as [ ll a b Hll Hab | ll a H1 IH ]; simpl.
    constructor 1 with (f b); auto.
    apply in_map_iff; exists b; auto.
    constructor 2; auto.
  Qed.    
   
End good_map.

Fact good_lift_rel X R ll a : good (R rlift a) ll -> @good X R (ll++a::nil).
Proof.
  induction 1 as [ ll u v H1 [ H2 | H2 ] | ll u H IH ]; simpl.
  apply in_good_0 with v; auto.
  apply in_or_app; left; auto.
  apply in_good_1.
  induction ll as [ | x ll IH]; simpl; destruct H1; subst.
  simpl; apply in_good_0 with a; auto.
  apply in_or_app; right; left; auto.
  apply in_good_1; auto.
  apply in_good_1; auto.
Qed.

Fact good_lift_rel_list X R mm ll : good (R lrlift mm) ll -> @good X R (ll++mm).
Proof.
  revert ll.
  induction mm as [ | a mm IH ]; simpl; intros ll.
  rewrite <- app_nil_end; auto.
  intros H.
  apply good_lift_rel, IH in H.
  revert H.
  rewrite app_ass; simpl; auto.
Qed.

Fact good_snoc X R ll a : @good X R (ll++a::nil) -> good (R rlift a) ll \/ exists x, R a x /\ In x ll.
Proof.
  intros H2.
  apply good_app_inv in H2.
  destruct H2 as [ H2 | [ H2 | H2 ] ].
  left; revert H2; apply good_inc; red; auto.
  apply good_sg_inv in H2; destruct H2.
  destruct H2 as (x & b & H2 & [ | [] ] & H3); subst b.
  right; exists x; auto.
Qed. 

Fact Forall_map_proj1_sig X (P : X -> Prop) (ll : list (sig P)) : Forall P (map (@proj1_sig _ _) ll).
Proof.
  induction ll as [ | (x & Hx) ll IH ]; simpl; constructor; auto.
Qed.

Fact good_Restr X (R : X -> X -> Prop) P ll : good (R <# P #>) ll <-> good R (map (@proj1_sig _ _) ll) /\ Forall P (map (@proj1_sig _ _) ll).
Proof.
  split.

  induction 1 as [ ll (a & Ha) (b & Hb) H1 H2 | ll (a & Ha) H1 (H2 & H3) ]; split.

  simpl.
  constructor 1 with b.
  rewrite in_map_iff.
  exists (exist _ b Hb); auto.
  simpl in H2; auto.
  simpl; constructor; auto.
  apply Forall_map_proj1_sig.
  
  simpl; constructor 2; auto.
  simpl; constructor; auto.
  
  intros (H1 & H2).
  induction ll as [ | (a & Ha) ll IH ].
  apply good_nil_inv in H1; destruct H1.
  simpl in H1; apply good_cons_inv in H1.
  simpl in H2; apply Forall_cons_inv in H2.
  destruct H2 as [ H2 H3 ].
  destruct H1 as [ (b & Hb & H1) | H1 ].
  2: constructor 2; auto.
  rewrite in_map_iff in Hb.
  destruct Hb as ((b' & Hb) & H4 & H5); simpl in H4; subst b'.
  constructor 1 with (exist _ b Hb); auto.
Qed.

Section interleave.

  Variable X : Type.

  Inductive interleave : list X -> list X -> list X -> Prop :=
    | in_intl_0 : forall m, interleave nil m m
    | in_intl_1 : forall l, interleave l nil l
    | in_intl_2 : forall a l m k, interleave l m k -> interleave (a::l) m (a::k)
    | in_intl_3 : forall l b m k, interleave l m k -> interleave l (b::m) (b::k).

  Variable (R : X -> X -> Prop).

  Fact In_inlt_left x l m k : interleave l m k -> In x l -> In x k.
  Proof.
     induction 1 as [ m | l | a l m k H IH | l b m k H IH ]; auto.
     intros [].
     intros [ [] | ]; [ left | right ]; auto.
     right; auto.
  Qed.

  Fact In_inlt_right x l m k : interleave l m k -> In x m -> In x k.
  Proof.
     induction 1 as [ m | l | a l m k H IH | l b m k H IH ]; auto.
     intros [].
     right; auto.
     intros [ [] | ]; [ left | right ]; auto.
  Qed.

  Fact good_intl_left l m k : interleave l m k -> good R l -> good R k.
  Proof.
    induction 1 as [ m | l | a l m k H IH | l b m k H IH ]; auto.
    intros H; apply good_nil_inv in H; destruct H.
    intros H1; apply good_cons_inv in H1.
    destruct H1 as [ (x & H1 & H2) | H1 ].
    constructor 1 with x; auto.
    revert H1; apply In_inlt_left with (1 := H).
    constructor 2; auto.
    constructor 2; auto.
  Qed.

  Fact good_intl_right l m k : interleave l m k -> good R m -> good R k.
  Proof.
    induction 1 as [ m | l | a l m k H IH | l b m k H IH ]; auto.
    intros H; apply good_nil_inv in H; destruct H.
    constructor 2; auto.
    intros H1; apply good_cons_inv in H1.
    destruct H1 as [ (x & H1 & H2) | H1 ].
    constructor 1 with x; auto.
    revert H1; apply In_inlt_right with (1 := H).
    constructor 2; auto.
  Qed.

End interleave.

  
  
