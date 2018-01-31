(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega List Permutation Wellfounded.

Require Import tacs rel_utils list_utils.

Require Import sublist.

Set Implicit Arguments.

Definition finite_repr X (P : X -> Prop) ll := forall x, In x ll <-> P x.
Definition finite_inverse X Y (f : X -> Y) y ll := forall x, In x ll <-> y = f x.

Definition finite X (P : X -> Prop) := exists ll, forall x, In x ll <-> P x.

Definition finite_t X (P : X -> Prop) := { ll | forall x, In x ll <-> P x }.

Fact finite_inhabited X P : @finite X P <-> inhabited (finite_t P).
Proof.
  split.
  intros (l & ?); exists; exists l; auto.
  intros [ (l & ?) ]; exists l; auto.
Qed.

Fact finite_t_finite X P : @finite_t X P -> finite P.
Proof. intros [ x Hx ]; exists x; intro; rewrite Hx; split; auto. Qed.

Section finite_nat.

  Fact finite_t_lt n : finite_t (fun x => x < n).
  Proof.
    exists (list_n n).
    intros; symmetry; apply list_n_prop.
  Qed.
  
  Fact finite_lt n : finite (fun x => x < n).
  Proof.
    apply finite_t_finite, finite_t_lt.
  Qed.
 
End finite_nat.

Fact finite_t_eq X (P Q : X -> Prop) : P ~eq1 Q -> finite_t P -> finite_t Q.
Proof.
  intros H1; intros (ll & H2); exists ll; intros x; split; intros H3.
  apply H1, H2; auto.
  apply H2, H1; auto.
Qed.

Local Ltac solve H := repeat rewrite finite_inhabited; inhabited_tac; apply H; auto.
    
Fact finite_eq X (P Q : X -> Prop) : P ~eq1 Q -> finite P -> finite Q.
Proof. intro; solve finite_t_eq. Qed.
  
Fact finite_t_img (X Y : Type) (f : X -> Y) x : finite_t (fun y => y = f x).
Proof.
  exists ((f x)::nil).
  intro; simpl; split; auto.
  intros [ | []]; auto.
Qed.

Fact finite_img (X Y : Type) (f : X -> Y) x : finite (fun y => y = f x).
Proof. solve finite_t_img. Qed. 

Fact finite_t_cup (X : Type) (A B : X -> Prop) : finite_t A -> finite_t B -> finite_t (A cup1 B).
Proof.
  intros (lA & H1) (lB & H2); exists (lA++lB).
  intros x; rewrite <- H1, <- H2.
  split.
  apply in_app_or.
  apply in_or_app.
Qed.

Fact finite_cup (X : Type) (A B : X -> Prop) : finite A -> finite B -> finite (A cup1 B).
Proof. solve finite_t_cup. Qed.

Section finite_comp.

  Variable (X Y Z : Type) (R : X -> Y -> Prop) (S : Y -> Z -> Prop).
  
  Variable (x : X).  

  Section finite.

    Hypothesis HR : finite (R x).
    Hypothesis HQ : forall y, R x y -> finite (S y).
    
    Fact finite_comp : finite ((R o S) x).
    Proof.
      destruct HR as (ly & Hly).
      assert (HQ' : forall y, In y ly -> finite (S y)).
        intro; rewrite Hly; auto.
      apply sig_invert in HQ'.
      destruct HQ' as (mm & Hmm).
      exists (flat_map (fun x => x) mm).
      
      intros z; rewrite in_flat_map; split.
      
      intros (lz & H1 & H2).
      destruct (Forall2_In_inv_right Hmm _ H1) as (y & H3 & H4).
      exists y; rewrite <- H4, <- Hly; auto.
      
      intros (y & H1 & H2).
      rewrite <- Hly in H1.
      destruct (Forall2_In_inv_left Hmm _ H1) as (kk & H3 & H4).
      exists kk; rewrite H4; auto.     
    Qed.
    
  End finite.
  
  Section finite_t.

    Hypothesis HR : finite_t (R x).
    Hypothesis HQ : forall y, R x y -> finite_t (S y).
    
    Fact finite_t_comp : finite_t ((R o S) x).
    Proof.
      destruct HR as (ly & Hly).
      assert (HQ' : forall y, In_t y ly -> finite_t (S y)).
        intros y Hy.
        apply In_t_In in Hy.
        rewrite Hly in Hy; auto.
      apply sig_t_invert in HQ'.
      destruct HQ' as (mm & Hmm).
      exists (flat_map (fun x => x) mm).
      
      intros z; rewrite in_flat_map; split.
      
      intros (lz & H1 & H2).
      destruct (Forall2_In_inv_right Hmm _ H1) as (y & H3 & H4).
      exists y; rewrite <- H4, <- Hly; auto.
      
      intros (y & H1 & H2).
      rewrite <- Hly in H1.
      destruct (Forall2_In_inv_left Hmm _ H1) as (kk & H3 & H4).
      exists kk; rewrite H4; auto.    
    Qed.
    
  End finite_t.
    
End finite_comp.

Section finite_relmap.

  Variable (X Y : Type) (P : X -> Prop) (R : X -> Y -> Prop). 

  Section finite.

    Hypothesis HR : finite P.
    Hypothesis HQ : forall x, P x -> finite (R x).
    
    Fact finite_relmap : finite (fun y => exists x, P x /\ R x y).
    Proof.
      apply finite_comp with (x := tt) (R := fun _ x => P x); auto.
    Qed.
    
  End finite.
  
  Section finite_t.

    Hypothesis HR : finite_t P.
    Hypothesis HQ : forall x, P x -> finite_t (R x).
    
    Fact finite_t_relmap : finite_t (fun y => exists x, P x /\ R x y).
    Proof.
      apply finite_t_comp with (x := tt) (R := fun _ x => P x); auto.
    Qed.
    
  End finite_t.

End finite_relmap.

Section finite_relprod.

  Variables (X Y : Type) (P : X -> Prop) (R : X -> Y -> Prop).

  Section finite_t.
 
    Hypothesis HP : finite_t P.
    Hypothesis HR : forall x, P x -> finite_t (R x).
    
    Theorem finite_t_relprod : finite_t (fun c => P (fst c) /\ R (fst c) (snd c)).
    Proof.
      destruct HP as (lP & HlP).
      assert (forall x, In_t x lP -> finite_t (R x)) as H.
        intros x Hx.
        apply HR, HlP, In_t_In, Hx.
      apply sig_t_invert in H.
      destruct H as (mm & Hmm).
      exists (flat_map (fun c => map (fun y => (fst c, y)) (snd c)) (combine lP mm)).
      intros (x,y); rewrite in_flat_map; simpl.
      split.
      
      intros ((x',ly) & H1 & H2); simpl in H2 |- *.
      rewrite in_map_iff in H2.
      destruct H2 as (y' & H3 & H4).
      injection H3; clear H3; intros ? ?; subst x' y'.
      split.
      apply in_combine_l in H1.
      apply HlP; auto.
      apply Forall2_combine in Hmm.
      rewrite Forall_forall in Hmm.
      specialize (Hmm _ H1); simpl in Hmm.
      apply Hmm; auto.
      
      intros (H1 & H2).
      rewrite <- HlP in H1.
      destruct (Forall2_combine_In Hmm _ H1) as ((x',ly) & H3 & H4); simpl in H4; subst x'.
      exists (x,ly); split; auto.
      rewrite in_map_iff; simpl.
      apply Forall2_combine in Hmm.
      rewrite Forall_forall in Hmm.
      apply (Hmm _ H3) in H2.
      exists y; auto.
    Qed.

  End finite_t.

  Section finite.

    Hypothesis HP : finite P.
    Hypothesis HR : forall x, P x -> finite (R x).
  
    Theorem finite_relprod : finite (fun c => P (fst c) /\ R (fst c) (snd c)).
    Proof.
      destruct HP as (lP & HlP).
      assert (forall x, In x lP -> finite (R x)) as H.
        intros x Hx.
        apply HR, HlP, Hx.
      apply sig_invert in H.
      destruct H as (mm & Hmm).
      exists (flat_map (fun c => map (fun y => (fst c, y)) (snd c)) (combine lP mm)).
      intros (x,y); rewrite in_flat_map; simpl.
      split.
      
      intros ((x',ly) & H1 & H2); simpl in H2 |- *.
      rewrite in_map_iff in H2.
      destruct H2 as (y' & H3 & H4).
      injection H3; clear H3; intros ? ?; subst x' y'.
      split.
      apply in_combine_l in H1.
      apply HlP; auto.
      apply Forall2_combine in Hmm.
      rewrite Forall_forall in Hmm.
      specialize (Hmm _ H1); simpl in Hmm.
      apply Hmm; auto.
      
      intros (H1 & H2).
      rewrite <- HlP in H1.
      destruct (Forall2_combine_In Hmm _ H1) as ((x',ly) & H3 & H4); simpl in H4; subst x'.
      exists (x,ly); split; auto.
      rewrite in_map_iff; simpl.
      apply Forall2_combine in Hmm.
      rewrite Forall_forall in Hmm.
      apply (Hmm _ H3) in H2.
      exists y; auto.
    Qed.
    
  End finite.
 
End finite_relprod.
    
Section finite_product.

  Variable (X Y : Type) (P : X -> Prop) (Q : Y -> Prop).
  
  Fact finite_t_product : finite_t P -> finite_t Q -> finite_t (pred_prod P Q).
  Proof.
    intros (l & Hl) (m & Hm).
    exists (list_prod pair l m).
    intros (x,y); rewrite list_prod_spec; split.
    intros (a & b & H1 & H2 & H3); injection H3; intros ? ?; subst.
    red; rewrite <- Hl, <- Hm; auto.
    unfold pred_prod; rewrite <- Hl, <- Hm; simpl.
    intros []; exists x, y; auto.
  Qed.

  Fact finite_product : finite P -> finite Q -> finite (pred_prod P Q).
  Proof. solve finite_t_product. Qed.

End finite_product.

Section finite_inverse.

   Variable (X Y : Type).
   Implicit Type (f : X -> Y).
   
   Fact finite_inverse_map_t f ll (fi_f : forall x, In_t x ll -> list X) :
                                    (forall x Hx, finite_inverse f x (fi_f x Hx))
                                  -> finite_inverse (map f) ll (list_fan (list_In_t_map _ fi_f)).
   Proof.
     intros Hf fl; split.
     intros Hfl.
     apply list_fan_spec in Hfl.
     revert fl Hfl;
     induction ll as [ | x ll IHll ]; intros [ | y fl ] Hfl.
     auto.
     inversion Hfl.
     inversion Hfl.
     simpl in Hfl.
     apply Forall2_cons_inv in Hfl.
     destruct Hfl as [ H1 H2 ].
     simpl; f_equal.
     apply Hf in H1; auto.
     apply IHll with (2 := H2).
     intros; apply Hf.
     intros; subst. 
     apply list_fan_spec.
     induction fl; simpl; constructor; auto.
     apply Hf; auto.
   Qed.

End finite_inverse.

Section finite_rel_inv.

  Variable (X Y : Type) (R : X -> Y -> Prop).
  
  Fact finite_rel_inv ll : (forall x, In x ll -> finite (R x))
                         -> finite (Forall2 R ll).
  Proof.
    intros H.
    apply sig_invert in H.
    destruct H as (mm & Hmm).
    exists (list_fan mm).
    intros x.
    rewrite list_fan_spec.
    split.

    intros H; rewrite Forall2_exchg in H.
    generalize (Forall2_compose Hmm H); apply Forall2_impl.
    intros a b (c & H1 & H2); rewrite <- H1; auto.
    
    intros H; rewrite Forall2_exchg in H.
    generalize (Forall2_compose H Hmm); apply Forall2_impl.
    intros a b (c & H1 & H2); rewrite H2; auto.
  Qed.
  
End finite_rel_inv.

Notation finite_Forall2 := finite_rel_inv.

Section finite_t_rel_inv.

  Variable (X Y : Type) (R : X -> Y -> Prop).
  
  Fact finite_t_rel_inv_t ll : (forall x, In_t x ll -> finite_t (R x))
                         -> finite_t (Forall2 R ll).
  Proof.
    intros H.
    apply sig_t_invert in H.
    destruct H as (mm & Hmm).
    exists (list_fan mm).
    intros x.
    rewrite list_fan_spec.
    split.

    intros H; rewrite Forall2_exchg in H.
    generalize (Forall2_compose Hmm H); apply Forall2_impl.
    intros a b (c & H1 & H2); rewrite <- H1; auto.
    
    intros H; rewrite Forall2_exchg in H.
    generalize (Forall2_compose H Hmm); apply Forall2_impl.
    intros a b (c & H1 & H2); rewrite H2; auto.
  Qed.
  
  Fact finite_t_rel_inv ll : (forall x, In x ll -> finite_t (R x))
                         -> finite_t (Forall2 R ll).
  Proof.
    intros H; apply finite_t_rel_inv_t.
    intros; apply H, In_t_In; auto.
  Qed.

End finite_t_rel_inv.

Section list_rel_invert.

  Variables (X Y : Type) (R : X -> Y -> Prop) (ly : list Y).
  Hypothesis HQ : forall y, In_t y ly -> finite_t (fun x => R x y).
  
  Definition rel_list_invert : finite_t (fun lx => Forall2 R lx ly).
  Proof.
    destruct finite_t_rel_inv_t with (ll := ly) (R := fun x y => R y x) as (mm & Hmm).
    intros y Hy; destruct (HQ _ Hy) as (lx & Hlx).
    exists lx; intro; rewrite Hlx; split; auto.
    exists mm; intro; rewrite Hmm.
    rewrite Forall2_exchg; split; auto.
  Qed.

End list_rel_invert.

Section list_rel_invert'.

  Variables (X Y : Type) (R : X -> Y -> Prop) (P : X -> Prop) (ly : list Y).
  Hypothesis HQ : forall y, In_t y ly -> finite_t (fun x => P x /\ R x y).
  
  Definition rel_list_invert' : finite_t (fun lx => Forall P lx /\ Forall2 R lx ly).
  Proof.
    set (R' x y := P x /\ R x y).
    destruct (rel_list_invert R' ly) as (ll & Hll).
    apply HQ.
    exists ll.
    intros lx; rewrite Hll.
    unfold R'.
    rewrite Forall2_conj.
    rewrite Forall2_left_Forall.
    
    split; intros H;
    repeat split; try tauto.
    apply proj2 in H; revert H.
    apply Forall2_length.
  Qed.
 
End list_rel_invert'.

Section finite_utils.
  
  Variable X Y : Type.

  Fact finite_cap_dec P Q : finite P -> (forall x : X, Q x \/ ~ Q x) -> finite (P cap1 Q).
  Proof.
    intros (ll & Hll) HQ.
    revert P Hll.
    induction ll as [ | x ll IH ]; intros P Hll.

    exists nil.
    intros x; split.
    intros [].
    intros (? & _); apply Hll; auto. 
    
    destruct (IH (fun x => In x ll)) as (mm & Hmm).
    split; auto.
    destruct (HQ x) as [ Hx | Hx ].

    exists (x::mm).
    intros z; split; rewrite <- Hll.
    intros [ H1 | H1 ]; subst; simpl; auto.
    rewrite Hmm in H1; tauto.
    intros ([ H1 | H1 ] & H2).
    left; auto.
    right; auto.
    apply Hmm; auto.
    
    exists mm.
    intros z; split; rewrite <- Hll.
    intros H1; simpl; auto.
    rewrite Hmm in H1; tauto.
    intros ([ H1 | H1 ] & H2).
    subst; tauto.
    apply Hmm; auto.
  Qed.

  Fact finite_t_cap_dec P Q : finite_t P 
                           -> (forall x : X, { Q x } + { ~ Q x }) 
                           -> finite_t (P cap1 Q).
  Proof.
    intros (ll & Hll) HQ.
    revert P Hll.
    induction ll as [ | x ll IH ]; intros P Hll.

    exists nil.
    intros x; split.
    intros [].
    intros (? & _); apply Hll; auto.
    
    destruct (IH (fun x => In x ll)) as (mm & Hmm).
    split; auto.
    destruct (HQ x) as [ Hx | Hx ].

    exists (x::mm).
    intros z; split.
    intros [ H1 | H1 ]; subst; simpl; auto.
    rewrite <- Hll; simpl; tauto.
    rewrite Hmm in H1.
    rewrite <- Hll; simpl; tauto.
    rewrite <- Hll.
    intros ([ H1 | H1 ] & H2).
    left; auto.
    right; auto.
    apply Hmm; auto.
    
    exists mm.
    intros z; split; rewrite <- Hll.
    intros H1; simpl; auto.
    rewrite Hmm in H1; tauto.
    intros ([ H1 | H1 ] & H2).
    subst; tauto.
    apply Hmm; auto. 
  Qed.

  Fact finite_list_inv (f : X -> Y) Q ll : (forall y, In y ll -> finite (fun x => Q x /\ f x = y))
                                         -> finite (fun mm => ll = map f mm /\ Forall Q mm).
  Proof.
    intros H.
    apply finite_rel_inv in H.
    revert H.
    apply finite_eq.
    split; intros x;
    rewrite Forall2_exchg, Forall2_analysis; 
    intros [ ]; split; auto.
  Qed.

  Variable P : X -> Y -> Prop.

  Fact finite_list_repr ll : (forall x, In x ll -> finite (P x)) -> exists mm, Forall2 (fun x ly => finite_repr (P x) ly) ll mm.
  Proof.
    intros H.
    apply sig_invert in H.
    destruct H as (mm & Hmm).
    exists mm.
    revert Hmm; apply Forall2_impl.
    unfold finite_repr; auto.
  Qed.
    
End finite_utils.

Theorem sublist_finite_t X (l : list X) : finite_t (fun m => m <sl l).
Proof.
  exists (list_power l).
  apply list_power_spec.
Qed.

Section list_perms.

  Variable (X : Type).

  Implicit Type l : list X.  
  
  Notation R := (fun l m : list X => length l < length m).
  
  Let Rwf : well_founded R.
  Proof.
    apply wf_inverse_image, lt_wf.
  Qed.

  Theorem perm_finite_t l : finite_t (fun m => l ~p m).
  Proof.
    induction l as [ l IHl ] using (well_founded_induction_type Rwf).
    
    case_eq l.
    intros ?; subst.
    exists (nil::nil).
    intros; split.
    intros [ ? | [] ]; subst; auto.
    intros H; apply Permutation_nil in H; left; auto.
    
    intros a0 l' Hl.
    rewrite <- Hl.
    set (f (c : list X * (X * list X)) := match c with (l,(x,r)) => (x,l++r) end).
    set (ll := map f (lmr l)).
    assert (forall x, In_t x ll -> length (snd x) < length l) as Hll.
      intros x Hx.
      unfold ll in Hx. 
      apply In_t_map in Hx.
      destruct Hx as ( (a,(y,b)) & H1 & H2 ).
      unfold f in H2.
      apply In_t_In, lmr_spec in H1.
      destruct H1 as (l1 & z & r1 & H1 & H3).
      injection H3; clear H3; intros ? ? ?; subst l1 z r1.
      subst x; simpl.
      rewrite H1.
      do 2 rewrite app_length; simpl; omega.
    assert (forall x, In_t x ll -> finite_t (fun m => snd x ~p m)) as IH.
      intros (x,m) H; apply IHl, Hll; auto.
    generalize IH; clear IHl Hll IH; intros IH.
    unfold ll in IH; clear ll.
    exists (flat_map (fun x => x) (list_In_t_map _ (fun x Hx => map (cons (fst x)) (proj1_sig (IH _ Hx))))).
    intros m; split; rewrite in_flat_map.

    intros (k & H1 & H2).
    revert H1; apply In_t_P; intros H1.
    apply In_t_list_In_t_map in H1.
    destruct H1 as ( (x,p) & H1 & H3 ); simpl in H3.
    subst k.
    apply in_map_iff in H2.
    destruct H2 as ( m' & ? & H2 ); subst m.
    apply (proj2_sig (IH _ H1)) in H2; simpl in H2.
    apply In_t_In, in_map_iff in H1.
    destruct H1 as ( (a,(y,b)) & H1 & H3 ).
    unfold f in H1; injection H1; clear H1; intros ? ?; subst p y.
    apply lmr_spec in H3.
    destruct H3 as ( u & y & v & H3 & H4 ).
    injection H4; clear H4; intros ? ? ?; subst u y v.
    rewrite H3.
    apply Permutation_trans with (x::a++b).
    apply Permutation_sym, Permutation_cons_app; auto.
    constructor 2; auto.

    intros H1.
    destruct m as [ | x m ].
    exfalso.
    rewrite Hl in H1.
    apply Permutation_sym, Permutation_nil in H1.
    discriminate H1.
    clear a0 l' Hl.
    assert (In x l) as Hx.
      apply Permutation_in with (1 := Permutation_sym H1); left; auto.
    apply in_split in Hx.
    destruct Hx as (u & v & Hl).
    assert (In (x,u++v) (map f (lmr l))) as H2.
      apply in_map_iff.
      exists (u,(x,v)); split; auto.
      apply lmr_spec.
      exists u, x, v; auto.
    revert H2.
    apply In_t_P; intros H2.
    exists (map (cons (fst (x,u++v))) (proj1_sig (IH _ H2))); split.
    apply In_t_In.
    apply (list_In_t_map_In_t _ (fun x1 Hx1 => map (cons (fst x1)) (proj1_sig (IH _ Hx1)))).
    apply in_map_iff; simpl.
    exists m; split; simpl; auto.
    apply (proj2_sig (IH _ H2)).
    simpl.
    rewrite Hl in H1.
    apply Permutation_sym, Permutation_cons_app_inv in H1.
    apply Permutation_sym; auto.
  Qed.

End list_perms.

Section subset_finite_t.

  Variable (X : Type) (l : list X).

  Let ll := proj1_sig (perm_finite_t l).
  Let Hll m : In m ll <-> l ~p m.
  Proof. apply (proj2_sig (perm_finite_t l)). Qed.

  Fact subset_finite_t : finite_t (fun m => exists k, l ~p m ++ k).
  Proof.
    exists (flat_map (fun m => proj1_sig (sublist_finite_t m)) ll).
    intros m; rewrite in_flat_map; split.
    intros (p & H1 & H2).
    apply Hll in H1.
    apply (proj2_sig (sublist_finite_t p)) in H2.

    clear ll Hll; revert l H1.

    induction H2 as [ ll | x ll mm H IH | x ll mm H IH ]; intros l Hl.
    exists l; auto.
    destruct (IH mm) as (k & Hk); auto.
    exists k.
    apply Permutation_trans with (1 := Hl).
    simpl; constructor; auto.
    destruct (IH mm) as (k & Hk); auto.
    exists (x::k).
    apply Permutation_trans with (1 := Hl).
    apply Permutation_cons_app; auto.

    intros (k & Hk).
    exists (m++k); split.
    apply Hll; auto.
    apply (proj2_sig (sublist_finite_t (m++k))).
    apply sl_app_right.
  Qed.

End subset_finite_t.

Section finite_t_splits.

  Variable (X : Type).

  Let fperm (l : list X) := proj1_sig (perm_finite_t l).
  Let fperm_spec l m : In m (fperm l) <-> l ~p m.
  Proof. apply (proj2_sig (perm_finite_t l)). Qed.
  
  Fact pick_finite_t (l : list X) : finite_t ( fun c => match c with (x,m) => l ~p x::m end ).
  Proof.
    induction l as [ | x l (ll & Hll) ].
    
    exists nil.
    intros (x,m); split.
    intros [].
    intros H.
    apply Permutation_nil in H; discriminate.
    
    exists ( map (fun l => (x,l)) (fperm l) ++
             flat_map (fun c : X * list X => let (y,m) := c in map (fun q => (y,q)) (fperm (x::m))) ll ).
    intros (y,m).
    split.
    intros H.
    apply in_app_or in H.
    rewrite in_map_iff, in_flat_map in H.
    destruct H as [ (m' & E & H) | ((z,q) & H1 & H2) ].
    inversion E; subst m' y.
    apply fperm_spec in H.
    constructor; auto.
    apply in_map_iff in H2.
    destruct H2 as (q' & H2 & H3).
    inversion H2; subst z q'.
    apply fperm_spec in H3.
    apply Hll in H1.
    apply perm_trans with (1 := perm_skip _ H1),
          perm_trans with (2 := perm_skip _ H3).
    apply perm_swap.
    
    intros H; apply in_or_app.
    rewrite in_map_iff, in_flat_map.
    apply Permutation_cons_2_inv in H.
    destruct H as [ (E & H) | (k & H1 & H2) ].
    subst y; left; exists m; split; auto.
    apply fperm_spec; auto.
    right. exists (y,k); split.
    apply Hll; auto.
    apply in_map_iff.
    exists m; split; auto.
    apply fperm_spec, Permutation_sym; auto.
  Qed.
  
  Let pperm l := proj1_sig (pick_finite_t l).
  Let pperm_spec l c : In c (pperm l) <-> match c with (x,m) => l ~p x::m end.
  Proof.
    apply (proj2_sig (pick_finite_t l)).
  Qed.
  
  Fact split_finite_t (l : list X) : finite_t (fun c => match c with (p,q) => l ~p p++q end).
  Proof.
    induction l as [ | x l (ll & Hll) ].
    
    exists ((nil,nil)::nil).
    intros (p,q); split.
    intros [ E | [] ]; inversion E; subst p q; auto.
    intros H.
    apply Permutation_nil in H.
    destruct p; destruct q; try discriminate; simpl; auto.
    
    exists (  flat_map (fun c : list X * list X => let (p,q) := c in map (fun m => (m,q)) (fperm (x::p))) ll 
           ++ flat_map (fun c : list X * list X => let (p,q) := c in map (fun m => (p,m)) (fperm (x::q))) ll ).
    intros (p,q); split.
    intros H.
    apply in_app_or in H.
    do 2 rewrite in_flat_map in H.
    destruct H as [ ((p' & q') & H1 & H2) | ((p' & q') & H1 & H2) ].
    
    apply Hll in H1.
    apply in_map_iff in H2.
    destruct H2 as (u & E & H2).
    inversion E; subst u q'.
    apply fperm_spec in H2.
    apply Permutation_trans with (1 := perm_skip _ H1).
    apply Permutation_app with (l := x::p'); auto.
    
    apply Hll in H1.
    apply in_map_iff in H2.
    destruct H2 as (u & E & H2).
    inversion E; subst u p'.
    apply fperm_spec in H2.
    apply Permutation_trans with (1 := perm_skip _ H1).
    apply Permutation_trans with (2 := Permutation_app_comm _ _).
    apply Permutation_trans with (2 := Permutation_app H2 (Permutation_refl _)).
    simpl; apply perm_skip, Permutation_app_comm.
    
    intros H.
    assert (exists k, p ~p x::k \/ q ~p x::k) as H'.
      assert (In x (p++q)) as H'.
        apply Permutation_in with (1 := H); simpl; auto.
      apply in_app_or in H'.
      destruct H' as [ H' | H' ]; apply in_split in H';
        destruct H' as (k1 & k2 & H'); exists (k1++k2); [ left | right ];
        subst; apply Permutation_sym, Permutation_cons_app; auto.
    apply in_or_app; do 2 rewrite in_flat_map.
    destruct H' as (k & [ H' | H' ]); [ left | right ].
    exists (k,q); split. 
    apply Hll, Permutation_cons_inv with x, 
          Permutation_trans with (1 := H),
          Permutation_app with (l' := x::_); auto.
    apply in_map_iff; exists p; split; auto.
    apply fperm_spec, Permutation_sym; auto.
    exists (p,k); split. 
    apply Hll, Permutation_cons_inv with x, 
          Permutation_trans with (1 := H),
          Permutation_sym,
          Permutation_trans with (1 := Permutation_middle _ _ _),
          Permutation_app; auto.
    apply Permutation_sym; auto.
    apply in_map_iff; exists q; split; auto.
    apply fperm_spec, Permutation_sym; auto.
  Qed.
  
  Let sperm l := proj1_sig (split_finite_t l).
  Let sperm_spec l c : In c (sperm l) <-> match c with (a,b) => l ~p a++b end.
  Proof. apply (proj2_sig (split_finite_t l)). Qed.
  
  Fact pick_split_finite_t (l : list X) : finite_t (fun c => match c with (x,(p,q)) => l ~p x::p++q end).
  Proof.
    destruct (pick_finite_t l) as (l1 & Hl1).
    exists (flat_map (fun c : X * list X => let (x,m) := c in map (fun d => (x,d)) (sperm m)) l1).
    intros (x,(p,q)).
    rewrite in_flat_map.
    split.
    
    intros ((y,m) & H1 & H2).
    apply Hl1 in H1.
    apply in_map_iff in H2.
    destruct H2 as (z & H3 & H2).
    inversion H3; subst z y.
    apply sperm_spec in H2.
    apply Permutation_trans with (1 := H1).
    constructor; auto.
    
    intros H.
    exists (x,(p++q)); split.
    apply Hl1; auto.
    apply in_map_iff.
    exists (p,q); split; auto.
    apply sperm_spec; auto.
  Qed.
  
End finite_t_splits.

Section finite_t_decide.

  Variable (X : Type) (Q R S : X -> Prop).
  
  Hypothesis HQ1 : finite_t Q.
  Hypothesis HQ2 : forall x, Q x -> { R x } + { S x }.
  
  Fact finite_t_decide : { x | Q x /\ S x } + { forall x, Q x -> R x }.
  Proof.
    destruct HQ1 as (ll & Hll).
    assert (forall x, In_t x ll -> S x + R x) as H.
      intros x Hx; apply In_t_In in Hx.
      rewrite Hll in Hx; apply HQ2 in Hx.
      tauto.
    apply list_choose_rect in H.
    destruct H as [ (x & H1 & H2) | H ].
    left; exists x; split; auto; apply Hll, In_t_In; auto.
    right; intros x Hx; rewrite <- Hll in Hx.
    revert x Hx; apply In_In_t; auto.
  Qed.

End finite_t_decide.
    

