(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREER SOFTWARE LICENSE AGREEMENT         *)
(**************************************************************)

Require Import Arith Lia List Wellfounded Relations.

Require Import tacs rel_utils list_utils good_base.

Set Implicit Arguments.

(*

   This file contains the basic informative (or "type-bounded") definitions of the
   "Almost Full" AF predicate as defined in "Stop when your almost full" by Vytiniotis,
   Coquand and Wahlstedt. The logical/prop-bounded version is denoted af
   whereas the informative/type-bounded version is denoted af_t (and af_type, see below)

   Some proofs and results of this file are largely inspired by that work
   and its "Accompanying development" which is Coq code made available by
   the autors.

   In my opinion, the really non-trivial part of what I borrowed from those
   authors is the *very nice* proof of Ramsey's theorem (originally by Coquand),
   i.e. stability of the AF predicate by intersection (or isomorphically
   by products).

   From my point of view, a quite trivial but however VERY usefull addition
   to that code is the af_t_relmap theorem which says that the AF is stable
   under surjective *relational* maps. Hence, it works very well for subtypes
   { x | P x } which is not really the case with  af_t_cofmap, af_t_fmap or
   af_t_fmap_gen.

*)

Local Ltac squeeze := unfold lift_rel; intros ? ?; (tauto || firstorder || fail).

Section Almost_Full_type.

  Variable X : Type.

  Implicit Type R S : X -> X -> Prop.

  Inductive af_t R : Type :=
    | in_af_t0 : full R -> af_t R
    | in_af_t1 : (forall x, af_t (R rlift x)) -> af_t R.

  Fact af_t_inc R S : R inc2 S -> af_t R -> af_t S.
  Proof.
    intros H0 H1; revert S H0.
    induction H1 as [ R HR | R HR1 HR2 ] using af_t_rect; intros S H.
    apply in_af_t0.
    intros; apply H; auto.
    apply in_af_t1.
    intros a; apply (HR2 a), lift_rel_inc; auto.
  Qed.

  Fact af_t_eq R S : R ~eq2 S -> af_t R -> af_t S.
  Proof.
    intros [ ? _ ]; apply af_t_inc; auto.
  Qed.

  Definition af_t_inv R : af_t R -> forall a, af_t (R rlift a).
  Proof.
    induction 1 as [ R HR | R HR IHR ] using af_t_rect; intros a.
    apply in_af_t0; left; auto.
    auto.
  Qed.

  Fact af_t_always_good R : af_t R -> forall f, { n | good R (pfx_rev f n) }.
  Proof.
    induction 1 as [ R HR | R HR IHR ]; intros f.
    exists 2.
    constructor 1 with (f 0); simpl; auto.
    destruct (IHR (f 0) (fun n => f (S n))) as [ n Hn ].
    exists (S n).
    apply good_lift_rel in Hn.
    rewrite pfx_rev_S; auto.
  Qed.

  Corollary af_t_inf_chain R : af_t R -> forall f, { n | exists i j, i < j < n /\ R (f i) (f j) }.
  Proof.
    intros H f.
    destruct (af_t_always_good H f) as (n & Hn).
    exists n; apply good_pfx_rev_eq; trivial.
  Qed.

  Corollary af_t_includes_eq R : af_t R -> @eq _ inc2 R.
  Proof.
    intros H1 x y ?; subst.
    destruct (af_t_inf_chain H1 (fun _ => y)) as ( ? & ? & ? & ? & ? ); auto.
  Qed.

End Almost_Full_type.

Fact af_t_True X : @af_t X (fun _ _ => True).
Proof.
  apply in_af_t0; auto.
Qed.

Fact le_af_t : af_t le.
Proof.
  apply in_af_t1; intros n.
  induction n as [ n IHn ] using (well_founded_induction_type lt_wf).
  apply in_af_t1; intros m.
  destruct (le_lt_dec n m) as [ | H ].
  apply in_af_t0; squeeze.
  apply af_t_inc with (2 := IHn _ H); squeeze.
Qed.

Section af_t_union.

   Variables (X : Type) (R S : X -> X -> Prop).

   Fact af_t_union_left : af_t R -> af_t (fun x y => R x y \/ S x y).
   Proof.
     apply af_t_inc; squeeze.
   Qed.

   Fact af_t_union_right : af_t S -> af_t (fun x y => R x y \/ S x y).
   Proof.
     apply af_t_inc; squeeze.
   Qed.

End af_t_union.

(* a general projection principle with a surjective relation from R to S *)

Section af_t_relmap.

  Variables (X Y : Type) (f : X -> Y -> Prop)
            (R : X -> X -> Prop) (S : Y -> Y -> Prop)
            (Hf : forall y, { x | f x y })
            (HRS : forall x1 x2 y1 y2, f x1 y1 -> f x2 y2 -> R x1 x2 -> S y1 y2).

  Fact af_t_relmap : af_t R -> af_t S.
  Proof.
    intros H; revert S HRS.
    induction H as [ R HR | R HR IH ] using af_t_rect; intros S H.

    apply in_af_t0.
    intros y1 y2.
    destruct (Hf y1) as (x1 & Hx1).
    destruct (Hf y2) as (x2 & Hx2).
    apply H with (3 := HR x1 x2); auto.

    apply in_af_t1; intros y0.
    destruct (Hf y0) as (x0 & Hx0).
    apply IH with x0.
    intros x1 x2 y1 y2 H1 H2.
    generalize (H _ _ _ _ H1 H2).
    squeeze.
  Qed.

End af_t_relmap.

(* the reverse map of a total function is surjective *)

Section af_cofmap.

  Variables (X Y : Type) (f : Y -> X).

  Implicit Types (R : X -> X -> Prop).

  Fact af_t_cofmap R : af_t R -> af_t (fun x y => R (f x) (f y)).
  Proof.
    apply af_t_relmap with (f := fun x y => x = f y).
    intros y; exists (f y); auto.
    intros; subst; auto.
  Qed.

End af_cofmap.

(* two instances where the relation is a surjective function *)

Section af_t_fmap_gen.

  Variables (X Y : Type) (f : X -> Y) (Hf : forall y, { x | y = f x }).

  Implicit Types (R : X -> X -> Prop) (S : Y -> Y -> Prop).

  Fact af_t_fmap_gen R S : (forall x y, R x y -> S (f x) (f y)) -> af_t R -> af_t S.
  Proof.
    intros H.
    apply af_t_relmap with (f := fun x y => y = f x); auto.
    intros; subst; auto.
  Qed.

  Definition rel_fmap R (y1 y2 : Y) := exists x1 x2, y1 = f x1 /\ y2 = f x2 /\ R x1 x2.

  Fact af_t_fmap R : af_t R -> af_t (rel_fmap R).
  Proof.
    apply af_t_fmap_gen; auto.
    intros x1 x2; intros; subst; exists x1, x2; auto.
  Qed.

End af_t_fmap_gen.

Section af_t_rel_restr.

  Variables (X : Type) (P : X -> Prop) (R : X -> X -> Prop).

  Theorem af_t_rel_restr : af_t R -> af_t (R <# P #>).
  Proof.
    apply af_t_relmap with (f := fun x y => x = proj1_sig y).
    intros (y & ?); exists y; auto.
    intros x1 x2 (y1 & ?) (y2 & ?); cbv.
    intros; subst; auto.
  Qed.

End af_t_rel_restr.

(* This is the proof of Ramsey's theorem borrowed from Thierry Coquand's proof *)

Section af_t_intersection.

  Variable X : Type.

  Implicit Types (C : X -> X -> Prop).

  Local Lemma af_t_null_inter_rec A B R :
                 af_t R
    -> forall C, (forall x y, R x y <-> C x y \/ A)
              -> af_t (fun x y => C x y \/ B)
              -> af_t (fun x y => C x y \/ A /\ B).
  Proof.
    induction 1 as [ R HR | R HR1 HR2 ] using af_t_rect; intros C HC HB.

    apply af_t_inc with (2 := HB).
    intros x y [ Hxy | Hxy ]; auto.
    specialize (HR x y); rewrite HC in HR; tauto.

    apply in_af_t1.
    intros x.
    apply af_t_inc with (R := fun y z => (C y z \/ C x y) \/ A /\ B).
    squeeze.
    apply HR2 with x.
    intros ? ?; unfold lift_rel; do 2 rewrite HC; tauto.
    apply af_t_inc with (2 := HB); squeeze.
  Qed.

  Local Lemma af_t_null_inter C A B :
        af_t (fun x y => C x y \/ A)
     -> af_t (fun x y => C x y \/ B)
     -> af_t (fun x y => C x y \/ (A /\ B)).
  Proof.
    intros H.
    apply af_t_null_inter_rec with (1 := H).
    intros; tauto.
  Qed.

  Local Lemma af_t_una_inter_rec A B R :
                  af_t R
     -> forall T, af_t T
     -> forall C, (forall x y, R x y -> C x y \/ A x)
               -> (forall x y, T x y -> C x y \/ B x)
               -> af_t (fun x y => C x y \/ (A x /\ B x)).
  Proof.
    induction 1 as [ R HR | R HR IHR ] using af_t_rect.

    intros T HT C Req Teq.
    eapply af_t_inc with (2 := HT).
    intros x y; generalize (Req x y) (Teq x y) (HR x y); tauto.

    induction 1 as [ T HT | T HT IHT ] using af_t_rect.

    intros C Req Teq.
    apply af_t_inc with (R := R).
    intros x y; generalize (HT x y) (Req x y) (Teq x y); tauto.
    apply in_af_t1, HR.

    intros C Req Teq.
    apply in_af_t1; intros x.
    generalize (in_af_t1 HT); intros HT'.
    apply af_t_inc with (R := fun y z : X => ((C y z \/ A y /\ B y) \/ C x y) \/ A x /\ B x).
    squeeze.
    apply af_t_null_inter.

    generalize (IHR x _ HT' (fun y z => C y z \/ C x y \/ A x)); intros G0.
    eapply af_t_inc.
    2:{ apply G0.
        intros y z; generalize (Req y z) (Req x y); unfold lift_rel; tauto.
        intros y z Hyz; generalize (Teq y z); tauto. }

    squeeze.

    generalize (IHT x (fun y z => C y z \/ C x y \/ B x)); intros G0.
    eapply af_t_inc.
    2:{ apply G0.
        intros y z; generalize (Req y z) (Req x y); tauto.
        intros y z [ H1 | H1 ]; apply Teq in H1; tauto. }

    squeeze.
  Qed.

  Local Lemma af_t_una_inter C A B :
        af_t (fun x y => C x y \/ A x)
     -> af_t (fun x y => C x y \/ B x)
     -> af_t (fun x y => C x y \/ (A x /\ B x)).
  Proof.
    intros H1 H2.
    apply af_t_una_inter_rec with (1 := H1) (2 := H2); squeeze.
  Qed.

  Implicit Types (A B : X -> X -> Prop).

  Theorem af_t_inter A B : af_t A -> af_t B -> af_t (A cap2 B).
  Proof.
    intros HA HB.
    revert A HA B HB.
    induction 1 as [ A HA | A HA IHA ] using af_t_rect.

    intros B HB; apply af_t_inc with (2 := HB); squeeze.

    induction 1 as [ B HB | B HB IHB ] using af_t_rect.

    apply af_t_inc with (2 := in_af_t1 HA); squeeze.

    apply in_af_t1; intros x.
    unfold lift_rel.
    apply af_t_una_inter.
    apply af_t_inc with (2 := IHA x _ (in_af_t1 HB)); squeeze.
    apply af_t_inc with (2 := IHB x); squeeze.
  Qed.

End af_t_intersection.

Section af_t_prod.

  Variable (X Y : Type).
  Variable (R : X -> X -> Prop) (S : Y -> Y -> Prop).

  Theorem af_t_prod : af_t R
                   -> af_t S
                   -> af_t (rel_prod R S).
  Proof.
    intros HR HS;
    apply af_t_inter;
    apply af_t_cofmap; auto.
  Qed.

End af_t_prod.

Section af_t_sum.

  Variable (X Y : Type).

  Local Lemma af_t_sum_left R : af_t R -> af_t (@sum_left X Y R).
  Proof.
    induction 1 as [ R HR | R HR IH ] using af_t_rect.

    apply in_af_t1; intros x.
    apply in_af_t1; intros y.
    apply in_af_t0.
    intros [|] [|]; destruct x; destruct y; simpl; firstorder.

    apply in_af_t1; intros [ x | x ].
    apply af_t_inc with (2 := IH x).
    intros [|] [|]; unfold lift_rel, sum_left; tauto.
    apply in_af_t1; intros [ y | y ].
    apply af_t_inc with (2 := IH y).
    intros [|] [|]; unfold lift_rel, sum_left; tauto.
    apply in_af_t0.
    intros [|] [|]; unfold lift_rel, sum_left; tauto.
  Qed.

  Local Lemma af_t_sum_right R : af_t R -> af_t (@sum_right X Y R).
  Proof.
    induction 1 as [ R HR | R HR IH ] using af_t_rect.

    apply in_af_t1; intros x.
    apply in_af_t1; intros y.
    apply in_af_t0.
    intros [|] [|]; destruct x; destruct y; simpl; firstorder.

    apply in_af_t1; intros [ x | x ].
    apply in_af_t1; intros [ y | y ].
    apply in_af_t0.
    intros [|] [|]; unfold lift_rel, sum_right; tauto.
    apply af_t_inc with (2 := IH y).
    intros [|] [|]; unfold lift_rel, sum_right; tauto.
    apply af_t_inc with (2 := IH x).
    intros [|] [|]; unfold lift_rel, sum_right; tauto.
  Qed.

  Lemma af_t_sum_both R S : af_t R -> af_t S -> af_t (@sum_both X Y R S).
  Proof.
    intros HR HS.
    apply af_t_inc with (2 := af_t_inter (af_t_sum_left HR) (af_t_sum_right HS)).
    intros [|] [|] (H1 & H2); simpl in H1, H2 |- *; tauto.
  Qed.

End af_t_sum.

Lemma af_t_nat_equiv : af_t (fun x y => x = 0 <-> y = 0).
Proof.
  do 2 (apply in_af_t1; intro).
  apply in_af_t0; intros.
  cbv; lia.
Qed.




