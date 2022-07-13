(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import List Lia.

(* Require Import tacs. *)

Require Import list_nat list_in list_forall list_prefix.

Set Implicit Arguments.

Section decide.

  Variables X : Type.

  Implicit Type (ll : list X).

  Definition list_choose (P Q : X -> Prop) ll : (forall a, In a ll -> P a \/ Q a)
                                             -> (exists a, In a ll /\ P a)
                                             \/ (forall a, In a ll -> Q a).
  Proof.
    induction ll as [ | x ll IH ]; intros HP.
    right; intros ? [].
    destruct IH as [ (z & H1 & H2) | IH ].
    intros z Hz; apply HP; right; auto.
    left; exists z; split; auto; right; auto.
    destruct (HP x) as [ H3 | H3 ].
    left; auto.
    left; exists x; split; auto; left; auto.
    right; intros q [ | Hq]; auto; intros; subst; auto.
  Qed.

  (* for an heterogeneous list [P x1 + Q x1;...;Pxn + Q xn], either find i s.t. P xi or
     a proof that for any j, Q xj *)

  Definition list_dep_choice_rect ll (P Q : forall x, In_t x ll -> Type) :
       (forall x Hx, P x Hx + Q x Hx)
    -> { x : _ & { Hx : In_t x ll & P x Hx } }
     + (forall x Hx, Q x Hx).
  Proof.
    revert P Q.
    induction ll as [ | x ll IH ]; intros P Q HP.
    right; intros ? [].
    specialize (IH (fun x Hx => P _ (inr Hx)) (fun x Hx => Q _ (inr Hx))).
    destruct IH as [ (z & H1 & H2) | IH ].
    intros z Hz; apply HP; right; auto.
    left; exists z, (inr H1); auto.
    destruct (HP _ (inl eq_refl)) as [ H3 | H3 ].
    left; exists x, (inl eq_refl); auto.
    right; intros q [ | Hq]; auto; intros; subst; auto.
  Qed.

  Definition list_dep_choice_ind ll (P Q : forall x : X, In_t x ll -> Prop) :
    (forall x Hx, P x Hx \/ Q x Hx) -> (exists x Hx, P x Hx) \/ forall x Hx, Q x Hx.
  Proof.
    revert P Q.
    induction ll as [ | x ll IH ]; intros P Q HPQ.
    right; intros ? [].
    destruct (IH (fun x Hx => P _ (inr Hx)) (fun x Hx => Q _ (inr _ Hx))) as [ (z & H1 & H2) | IH' ].
    intros z Hz; apply HPQ; right; auto.
    left; exists z, (inr H1); auto.
    destruct (HPQ x (inl eq_refl)) as [ H3 | H3 ].
    left; exists x, (inl eq_refl); auto.
    right; intros q [ Hq | Hq]; subst; auto.
  Qed.

  Definition list_choose_rect (P Q : X -> Type) ll :
       (forall x, In_t x ll -> P x + Q x)
    -> { z : _ & (In_t z ll * P z)%type }
     + (forall z, In_t z ll -> Q z).
  Proof.
    intros H.
    destruct (list_dep_choice_rect ll (fun x _ => P x) (fun x _ => Q x) H) as [ (x & H1 & H2) | H1 ].
    left; exists x; auto.
    right; auto.
  Qed.

  Definition list_choose_ind (P Q : X -> Prop) ll :
       (forall x, In x ll -> P x \/ Q x)
    -> (exists z, In z ll /\ P z) \/ forall z, In z ll -> Q z.
  Proof.
    intros H.
    rewrite <- In_In_t in H.
    destruct (list_dep_choice_ind ll (fun x _ => P x) (fun x _ => Q x) H) as [ (x & H1 & H2) | H1 ].
    left; exists x; split; auto; apply In_t_In; auto.
    right; apply In_In_t; auto.
  Qed.

  Definition list_choose_rec (P Q : X -> Prop) ll :
    (forall x, In x ll -> {P x} + {Q x}) -> { z | In z ll /\ P z } + { forall z, In z ll -> Q z }.
  Proof.
    intros H.
    destruct (list_choose_rect P Q ll) as [ (z & H1 & H2) | H1 ].
    intros x Hx; destruct (H x); try tauto; apply In_t_In; auto.
    left; exists z; split; auto; apply In_t_In; auto.
    right; apply In_In_t; auto.
  Qed.

  Variable P : X -> Prop.

  Definition list_dec_rec ll :
    (forall x, In x ll -> {P x} + {~ P x}) -> { z | In z ll /\ P z } + { forall z, In z ll -> ~ P z }.
  Proof.
    apply list_choose_rec.
  Qed.

  Corollary list_reif_dec ll :
    (forall x, In x ll -> {P x} + {~ P x}) -> (exists x, P x /\ In x ll) -> { x | P x /\ In x ll }.
  Proof.
    intros Pdec H.
    destruct list_dec_rec with (ll := ll) as [ (x & ? & ?) | H0 ]; auto.
    exists x; auto.
    contradict H.
    intros (x & ? & ?); apply (H0 x); auto.
  Qed.

  Definition list_dec_ind ll :
    (forall x, In x ll -> P x \/ ~ P x) -> (exists z, In z ll /\ P z ) \/ forall z, In z ll -> ~ P z.
  Proof.
    apply list_choose_ind.
  Qed.

End decide.

Section list_eq_dec.

  Variable (X : Type).

  Fact list_eq_dect ll mm :  (forall x y : X, In_t x ll -> In_t y mm -> { x = y } + { x <> y })
                         -> { ll = mm } + { ll <> mm }.
  Proof.
    revert mm; induction ll as [ | x ll ]; intros [ | y mm ] H.
    left; auto.
    right; discriminate.
    right; discriminate.
    destruct (H x y) as [ H1 | H1 ]; try (left; auto; fail).
    subst y.
    destruct (IHll mm) as [ H2 | H2 ].
    intros; apply H; right; auto.
    subst mm; left; auto.
    right; contradict H2; injection H2; auto.
    right; contradict H1; injection H1; auto.
  Qed.

  Fact list_eq_dec ll mm :  (forall x y : X, In x ll -> In y mm -> { x = y } + { x <> y })
                         -> { ll = mm } + { ll <> mm }.
  Proof.
    intros H; apply list_eq_dect.
    intros; apply H; apply In_t_In; auto.
  Qed.

End list_eq_dec.

Section finite_decision.

  Variables (X : Type) (P : X -> Prop).

  (* Given x in ll s.t. P x, finds the first among them, i.e. y in ll s.t. P y
     and ~ P z for any z before y *)

  Fact In_first ll : (forall x, In x ll -> P x \/ ~ P x)
                   -> forall x, In x ll -> P x -> exists l y r, ll = l++y::r
                                                    /\ P y
                                                    /\ forall z, In z l -> ~ P z.
  Proof.
    induction ll as [ | y ll IH ]; simpl; intros Hll x H1 H2; destruct H1.
    subst; exists nil, x, ll; repeat split; auto.
    destruct (Hll y) as [ Hy | Hy ]; auto.
    exists nil, y, ll; repeat split; auto.
    destruct IH with (3 := H2) as (l & z & r & H3 & H4 & H5); auto.
    subst; exists (y::l), z, r; repeat split; auto.
    intros k [ ? | ? ].
    subst k; auto.
    apply H5; auto.
  Qed.

  Variable Q : list X -> list X -> Prop.

  (* if Q is decidable over the splits l++r of ll and Q nil ll holds then
     there is prefix l s.t Q l' r' holds whenever l' <= l
     and Q l' r' does not hold for the successor prefix of l'
     (if it exists).

  *)

  Definition largest_list_prefix ll : (forall l r, ll = l++r -> { Q l r } + { ~ Q l r })
                                   -> Q nil ll
                                   -> { l : _ & { r | ll = l++r
                                                   /\ Q l r
                                                   /\ (forall l' r', ll = l'++r' -> length l' = S (length l) -> ~ Q l' r')
                                                   /\ (forall l' r', ll = l'++r' -> length l' <= length l    ->   Q l' r') } }.
  Proof.
    intros HQ H0.
    set (K n := forall l r, ll = l++r -> length l = n -> Q l r).
    destruct (@largest_nat_prefix (length ll) K) as (i & H1 & H2 & H3 & H3').
    intros i Hi; unfold K.
    destruct (list_prefix _ Hi) as (l & r & H1 & H2).
    destruct (HQ _ _ H1) as [ H5 | H5 ].
    left.
    intros l' r' H3 H4; subst.
    destruct list_prefix_eq with (1 := H3); try lia; subst; auto.
    right; contradict H5; apply H5; auto.
    red.
    intros l r H1 H2 .
    destruct (list_prefix_eq l r nil ll); auto.
    subst l r; auto.
    destruct (list_prefix _ H1) as (l & r & H4 & H5).
    exists l, r.
    repeat split; auto.

    intros l' r' H6 H7.
    intros H8.
    assert (K (S i)) as C.
      red.
      intros l'' r'' H9 H10.
      rewrite <- H5, <- H7 in H10.
      rewrite H6 in H9.
      destruct list_prefix_eq with (1 := H9); auto.
      subst l'' r''; auto.
    apply H3 in C.
    apply f_equal with (f := @length X) in H6.
    rewrite app_length in H6.
    lia.

    intros l' r' H6 H7.
    rewrite H5 in H7.
    apply H3' in H7.
    apply H7; auto.
  Defined.

  Variables (R : list X -> X -> list X -> Prop).

  Definition list_find_split ll : (forall l x r, ll = l++x::r -> { R l x r } + { ~ R l x r })
                               -> { l : _ & { x : _ & { r | ll = l++x::r /\ R l x r } } }
                                + { forall l x r, ll = l++x::r -> ~ R l x r }.
  Proof.
    revert R.
    induction ll as [ | x ll IH ]; intros R HR.
    right; intros [ | ] ? ?; discriminate 1.
    destruct (HR nil x ll) as [ H0 | H0 ]; auto.
    left; exists nil, x, ll; auto.
    destruct (IH (fun l y r => R (x::l) y r)) as [ (l & y & r & H1 & H2) | H1 ].
    intros; apply HR; simpl; f_equal; auto.
    left; exists (x::l), y, r; split; simpl; auto; f_equal; auto.
    right.
    intros l y r H2.
    destruct l as [ | k l ];
    injection H2; intros; subst; auto.
  Defined.

End finite_decision.

Fact Forall_dec X (P : X -> Prop) ll :
       (forall x, In x ll -> { P x } + { ~ P x })
   -> { Forall P ll } + { ~ Forall P ll }.
Proof.
  intros H.
  destruct (list_choose_rec (fun x => ~ P x) P ll) as [ (x & H1 & H2) | H1 ].
  intros x Hx; specialize (H _ Hx); tauto.
  right; contradict H2; rewrite Forall_forall in H2; apply H2; auto.
  rewrite <- Forall_forall in H1; tauto.
Qed.

Fact finite_fall_disj U (P : U -> Prop) (Q : Prop) l : (forall u, In u l -> P u) \/ Q <-> forall u, In u l -> P u \/ Q.
Proof.
  split.
  intros [ H | H ] u Hu.
  left; auto.
  right; auto.
  intros H.
  destruct (list_choose (fun _ => Q) P l) as [ (u & H1 & H2) | H1 ].
  intros a; specialize (H a); tauto.
  right; auto.
  left; auto.
Qed.

Section combi_principle.

  Let seq (l : list Type) := forall X, In_t X l -> X.

  Let empseq : seq nil.
  Proof. intros ? []. Defined.

  Let consseq X (l : list Type) (a : X) : seq l -> seq (X::l).
  Proof.
    intros H Y [ HY | HY ].
    subst; apply a.
    apply (H _ HY).
  Defined.

(*
  Let hd X l : seq (X::l) -> X.
  Proof. intros H; apply (H _ (inl eq_refl)). Defined.

  Definition tl X l : seq (X::l) -> seq l.
  Proof. intros H Y HY; apply (H _ (inr HY)). Defined.
*)

  (* the combinatorial principle of page 241
     in a purely intuitionistic way

     Beware than universal quantification should be finite here otherwise
     we cannot replace (forall u, P u \/ Q) with (forall u, Pu) \/ Q

  *)

  Fact combi_principle (l : list Type) (A : forall X, In_t X l -> list X)
                                       (P : seq l -> Prop)
                                       (B : forall X, In_t X l -> X -> Prop) :
        (forall a : seq l, (forall X HX, In (a X HX) (A X HX)) -> P a \/ exists X HX, B X HX (a X HX))
     -> (exists a, P a /\ forall X HX, In (a X HX) (A X HX)) \/ exists X HX, forall x, In x (A X HX) -> B X HX x.
  Proof.
    revert A P B; induction l as [ | X l IH ]; intros A P B H.

    destruct (H empseq) as [ H1 | (? & [] & _) ].
    intros ? [].
    left; exists empseq; split; auto.
    intros ? [].

    set (P' s := forall a, In a (A _ (inl eq_refl)) -> P (consseq a s)\/ B _ (inl eq_refl) a).
    set (A' X HX := A X (inr HX)).
    set (B' X HX := B X (inr HX)).

    destruct (IH A' P' B') as [ (a & Ha & Ha') | (Y & HY1 & HY2) ].

    intros s Hs.
    unfold P'.
    apply finite_fall_disj.
    intros a Ha.
    destruct (H (consseq a s)) as [ H1 | (Y & HY & H1) ].
    intros Y [ HY | HY ]; subst; auto; apply Hs.
    left; left; auto.
    destruct HY as [ HY | HY ].
    subst Y.
    left; right; apply H1.
    right.
    exists Y, HY; apply H1.

    red in Ha.
    apply list_choose in Ha.
    destruct Ha as [ (Y & H1 & H2) | H1 ].
    left; exists (consseq Y a); split; auto.
    intros ? [ ? | ? ]; subst; auto; apply Ha'.
    right; exists X, (inl eq_refl); auto.

    unfold A', B' in HY2.
    right; exists Y, (inr HY1); auto.
  Qed.

End combi_principle.

Section list_fan_combi_principle.

  Variable X : Type.

  Fact list_fan_combi_principle ll P :
               (forall p, Forall2 (@In X) p (map (@fst _ _) ll)
                       -> P p \/ Exists2 (fun x B => B x) p (map (@snd _ _) ll))
            -> (exists p, Forall2 (@In _) p (map (@fst _ _) ll) /\ P p)
            \/ (exists A B, In (A,B) ll/\ forall x, In x A -> B x).
  Proof.
    revert P.
    induction ll as [ | (A,B) ll IH ]; intros P Hll.

    destruct (Hll nil) as [ H0 | H0 ]; simpl; auto.
    left; exists nil; simpl; auto.
    apply Exists2_nil_inv in H0; destruct H0.

    set (P' l := forall a, In a A -> P (a::l) \/ B a).
    destruct (IH P') as [ (p & H1 & H2) | (A1 & B1 & H1 & H2) ].

    intros l Hl.
    unfold P'.
    apply finite_fall_disj.
    intros a Ha.
    destruct (Hll (a::l)) as [ H1 | H1 ].
    simpl; constructor; auto.
    tauto.
    simpl in H1.
    apply Exists2_cons_inv in H1; tauto.

    apply list_choose in H2.
    destruct H2 as [ (a & H2 & H3) | H2 ].
    left; exists (a::p); simpl; split; auto.
    right; exists A, B; simpl; split; auto.

    right; exists A1, B1; simpl; split; auto.
  Qed.

End list_fan_combi_principle.

Section hig_combi_principle.

  Variable X : Type.
  Variable ll : list (list X).
  Variable P : list X -> Prop.
  Variable B : X -> Prop.

  Fact hig_combi_principle :
               (forall p, Forall2 (@In X) p ll -> P p \/ exists x, In x p /\ B x)
            -> (exists p, Forall2 (@In _) p ll /\ P p)
            \/ (exists A, In A ll/\ forall x, In x A -> B x).
  Proof.
    intros H.
    set (ll' := map (fun x => (x,B)) ll).
    destruct (list_fan_combi_principle ll' P) as [ (p & H1 & H2) | (A & B' & H1 & H2) ].

    intros p Hp.
    unfold ll' in Hp.
    rewrite map_map, map_id in Hp.
    destruct (H p) as [ H1 | (x & H1 & H2) ]; auto.
    right.
    unfold ll'; rewrite map_map; simpl.

    clear H ll'.
    induction Hp.
    destruct H1.
    destruct H1 as [ H1 | H1 ].
    subst; simpl.
    constructor 1; auto.
    rewrite map_length.
    revert Hp; apply Forall2_length.
    constructor 2; auto.

    left; exists p; split; auto.
    unfold ll' in H1; rewrite map_map, map_id in H1; auto.

    unfold ll' in H1.
    rewrite in_map_iff in H1.
    destruct H1 as (A' & H1 & H3).
    injection H1; intros; subst A' B'.
    right; exists A; auto.
  Qed.

End hig_combi_principle.

Section list_decide_special.

  Section one.

    Variable (X Y : Type) (Q R S : X -> Y -> Prop).

    Hypothesis HQ : forall x y, Q x y -> R x y \/ S x y.

    Fact one_list_decide ll : (forall x, In x ll -> exists y, Q x y)
                           -> (forall x, In x ll -> exists y, R x y)
                           \/ (exists x y, In x ll /\ S x y).
    Proof.
      intros H.
      destruct (list_choose_ind (fun x => exists y, S x y) (fun x => exists y, R x y) ll) as [ (x & H1 & y & H2) | H1 ].
      intros x Hx; destruct (H _ Hx) as (y & Hy).
      apply HQ in Hy.
      destruct Hy; [ right | left ]; exists y; auto.
      right; exists x, y; split; auto; apply In_t_In; auto.
      left; auto.
    Qed.

  End one.

  Section two_prop.

    Variable (X Y : Type) (P S : X -> Y -> Prop) (Q : X -> Prop) (R : Y -> Prop).

    Hypothesis HQ : forall x y, P x y -> Q x \/ R y \/ S x y.

    Variables (ll : list X) (mm : list Y).

    Let A : forall T, In_t T (X::Y::nil) -> list T.
    Proof.
      intros T [ ? | [ ? | [] ] ]; subst T.
      exact ll.
      exact mm.
    Defined.

    Let PA : (forall T, In_t T (X::Y::nil) -> T) -> Prop.
    Proof.
      intros H.
      apply S; apply H.
      left; auto.
      right; left; auto.
    Defined.

    Let PB : forall T, In_t T (X::Y::nil) -> T -> Prop.
    Proof.
      intros T [ ? | [ ? | [] ] ]; subst T.
      apply Q.
      apply R.
    Defined.

    Fact two_list_decide_prop       : (forall x y, In x ll -> In y mm -> P x y)
                                   -> (forall x, In x ll -> Q x)
                                   \/ (forall y, In y mm -> R y)
                                   \/ (exists x y, In x ll /\ In y mm /\ S x y).
    Proof.
      intros HP.
      destruct (@combi_principle (X::Y::nil) A PA PB) as [ (a & H1 & H2) | (X0 & HX0 & H1) ] .

      intros f Hf.
      generalize (Hf _ (inl eq_refl)) (Hf _ (inr (inl eq_refl))).
      simpl; unfold eq_rect_r; simpl.
      clear Hf; intros HX HY.
      destruct (HQ (HP _ _ HX HY)) as [ H | [ H | H ] ].
      right; exists X, (inl eq_refl); cbv; auto.
      right; exists Y, (inr (inl eq_refl)); cbv; auto.
      left; cbv; auto.

      cbv in H1.
      right; right.
      exists (a X (inl eq_refl)), (a Y (inr (inl eq_refl))); repeat split; auto; apply H2.

      destruct HX0 as [ ? | [ ? | [] ] ]; subst.

      left; apply H1.
      right; left; apply H1.
    Qed.

  End two_prop.

  Section two.

    Variable (X Y Z : Type) (P S : X -> Y -> Z -> Prop) (Q : X -> Z -> Prop) (R : Y -> Z -> Prop).

    Hypothesis HP : forall x y z, P x y z -> Q x z \/ R y z \/ S x y z.

    Fact two_list_decide ll mm : (forall x y, In x ll -> In y mm -> exists z, P x y z)
                              -> (forall x, In x ll -> exists z, Q x z)
                              \/ (forall y, In y mm -> exists z, R y z)
                              \/ (exists x y z, In x ll /\ In y mm /\ S x y z).
    Proof.
      intros H.
      destruct (two_list_decide_prop (fun x y => exists z, P x y z)
                                     (fun x y => exists z, S x y z)
                                     (fun x   => exists z, Q x z)
                                     (fun   y => exists z, R y z)
            ) with (2 := H) as [ HQ | [ HR | HS ] ]; try tauto.

      intros x y (z & Hz); apply HP in Hz; destruct Hz as [ | [|] ].
      left; exists z; auto.
      right; left; exists z; auto.
      right; right; exists z; auto.

      destruct HS as (x & y & ? & ? & z & ?).
      right; right; exists x, y, z; auto.
    Qed.

  End two.

End list_decide_special.

