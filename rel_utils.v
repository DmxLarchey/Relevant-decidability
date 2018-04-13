(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Bool List Relations Wf Eqdep_dec Omega.

Set Implicit Arguments.

(* Notations for subset or subrel set theoretic operators *)

Notation "A 'inc1' B" := (forall x, A x -> B x) (at level 75, no associativity).
Notation "A 'inc2' B" := (forall x y, A x y -> B x y) (at level 75, no associativity).

Fact inc1_refl X (A : X -> Prop) : A inc1 A.
Proof. auto. Qed.

Fact inc1_trans X (A B C : X -> Prop) : A inc1 B -> B inc1 C -> A inc1 C.
Proof. intros; auto. Qed.

Fact inc2_refl X (A : X -> X -> Prop) : A inc2 A.
Proof. auto. Qed.

Fact inc2_trans X (A B C : X -> X -> Prop) : A inc2 B -> B inc2 C -> A inc2 C.
Proof. intros; auto. Qed.

Notation "A '~eq1' B " := (A inc1 B /\ B inc1 A) (at level 75).
Notation "A '~eq2' B " := (A inc2 B /\ B inc2 A) (at level 75).

Fact eq1_refl X (A : X -> Prop) : A ~eq1 A.
Proof. tauto. Qed.

Fact eq1_sym X (A B : X -> Prop) : A ~eq1 B -> B ~eq1 A.
Proof. tauto. Qed.

Fact eq1_trans X (A B C : X -> Prop) : A ~eq1 B -> B ~eq1 C -> A ~eq1 C.
Proof. intros [] [];  split; intros; auto. Qed.

Fact eq2_refl X Y (A : X -> Y -> Prop) : A ~eq2 A.
Proof. tauto. Qed.

Fact eq2_sym X Y (A B : X -> Y -> Prop) : A ~eq2 B -> B ~eq2 A.
Proof. tauto. Qed.

Fact eq2_trans X Y (A B C : X -> Y -> Prop) : A ~eq2 B -> B ~eq2 C -> A ~eq2 C.
Proof. intros [] [];  split; intros; auto. Qed.

(* intersection *)

Notation "A 'cap1' B" := (fun z => A z /\ B z) (at level 72, left associativity).
Notation "A 'cap2' B" := (fun x y => A x y /\ B x y) (at level 72, left associativity).

(* union *)

Notation "A 'cup1' B" := (fun z => A z \/ B z) (at level 72, left associativity).
Notation "A 'cup2' B" := (fun x y => A x y \/ B x y) (at level 72, left associativity).

Notation union1 := ((fun X I (R : I -> X -> Prop) x => exists i, R i x) _ _). 
Notation union2 := ((fun X I (R : I -> X -> X -> Prop) x y => exists i, R i x y) _ _). 

Notation "R 'o' S" := (fun x z => exists y, R x y /\ S y z) (at level 60).

Notation ES := (Empty_set : Type).
Notation ER := (fun (_ _ : ES) => True).

Notation empty := ((fun X (P : X -> Prop) => forall x, ~ P x) _).
Notation full := ((fun X (R : X -> X -> Prop) => forall x y, R x y) _). 

Notation set_mono := ((fun X (R : X -> X -> Prop) (B : X -> Prop) => forall x y, R x y -> B x -> B y) _).
Notation seq_mono := ((fun X (R : X -> X -> Prop) (f : nat -> X) => forall n, R (f n) (f (S n))) _). 

Notation feq := ((fun U V (r s : U -> V) => forall u, r u = s u) _ _).
Notation comp := ((fun U V W (f : V -> W) (h : U -> V) u => f (h u)) _ _ _).   
     
Notation ext_pred := ((fun U V (P : (U -> V) -> Prop) => (forall r s, feq r s -> P r -> P s)) _ _).             
Notation ext_pred_t := ((fun U V (P : (U -> V) -> Type) => (forall r s, feq r s -> P r -> P s)) _ _).

Notation ext := ((fun U V (P : (U -> V) -> Prop) => forall s s', (forall i, s i = s' i) -> P s -> P s') _ _).
Notation ext2 := ((fun U V X Y (P : (U -> V) -> (X -> Y) -> Prop) 
                         => forall r s f g, (forall i, r i = s i) 
                                         -> (forall j, f j = g j) 
                                         -> P r f -> P s g) _ _ _ _).

(* Definition rel_restr X (R : X -> X -> Prop) (A : X -> Prop) (x y : sig A) := R (proj1_sig x) (proj1_sig y).

Implicit Arguments rel_restr [ X ].

*)

Notation "R '<#' A '#>'" := (fun (x y : sig A) => R (proj1_sig x) (proj1_sig y)) (at level 70, no associativity).
Notation "P '</' A '/>'" := (fun (x : sig A) => P (proj1_sig x)) (at level 70, no associativity).

Notation scons := ((fun U (x : U) s i => match i with 0 => x | S i => s i end) _).
Notation stail := ((fun U (s : nat -> U) i => s (S i)) _).

Fact scons_stail_feq U (s : nat -> U) : feq (scons (s 0) (stail s)) s.
Proof.
  intros [|]; reflexivity.
Qed.

Section rel_comps.

  Variables (X Y : Type) (P : X -> Prop) (Q : Y -> Prop) (R : X -> X -> Prop) (S : Y -> Y -> Prop).

  Definition pred_prod x := P (fst x) /\ Q (snd x).

  Definition rel_prod x y := R (fst x) (fst y) /\ S (snd x) (snd y).

  Definition pred_sum (c : X + Y) := match c with inl x => P x | inr y => Q y end.

  Definition sum_left R (x y : X+Y) :=
    match x, y with
      | inl x, inl y => R x y
      | inr x, inr y => True
      | _    , _     => False 
    end.

  Definition sum_right S (x y : X+Y) :=
    match x, y with
      | inl x, inl y => True
      | inr x, inr y => S x y
      | _    , _     => False 
    end.
    
  Definition sum_both R S (x y : X+Y) :=
    match x, y with
      | inl x, inl y => R x y
      | inr x, inr y => S x y
      | _    , _     => False 
    end.

End rel_comps.

Fact conj_eq_prop (A B B' : Prop) : (B <-> B') -> (A /\ B <-> A /\ B').
Proof. tauto. Qed.

Fact disj_eq_prop (A B B' : Prop) : (B <-> B') -> (A \/ B <-> A \/ B').
Proof. tauto. Qed.

(* transitivity *)

Fact not_or_and_not (A B : Prop) : ~ (A \/ B) <-> ~ A /\ ~ B.
Proof. tauto. Defined.
  
Fact not_exst_fall_not X (A P : X -> Prop) : (~ exists x, A x /\ P x) <-> forall x, A x -> ~ P x.
Proof.
  split.
  intros H x Hx; contradict H; exists x; auto.
  intros H (x & H1 & H2); revert H2; apply H; auto.
Qed.

Fact clos_trans_1n_lt x y : clos_trans_1n _ lt x y -> x < y.
Proof.
  induction 1 as [ | x y z H1 H2 IH ]; auto.
  apply lt_trans with (1 := H1); auto.
Qed.

Section transitivity.

  Variables (X : Type).

  Implicit Types R S : X -> X -> Prop.

  Fact clos_trans_n1_clos_rt R x z : clos_trans_n1 _ R x z <-> exists y, clos_refl_trans _ R x y /\ R y z.
  Proof.
    split.

    induction 1 as [ z | y z H1 H2 (k & H3 & H4) ].
    exists x; split; auto; constructor 2.
    exists y; split; auto.
    constructor 3 with k; auto; constructor 1; auto.
    
    intros (y & H1 & H2); revert z H2.
    rewrite clos_rt_rtn1_iff in H1.
    induction H1 as [ | y z Hyz H1 IH1 ]; intros k Hk.
    constructor 1; auto.
    apply IH1 in Hyz.
    constructor 2 with z; auto; constructor 1; auto.
  Qed.

  Let clos_trans_succ_rec R n f : (forall i, i < n -> clos_trans _ R (f i) (f (S i))) -> forall i k, S k + i <= n -> clos_trans _ R (f i) (f (S k + i)).
  Proof.
    intros Hf i.
    induction k as [ | k IHk ].
    apply Hf.
    intros Hn.
    constructor 2 with (f (S k+i)).
    apply IHk; omega.
    apply Hf; omega.
  Qed.
  
  Fact clos_trans_succ R n f : (forall i, i < n -> clos_trans _ R (f i) (f (S i))) -> forall i j, i < j <= n -> clos_trans _ R (f i) (f j).
  Proof.
    intros Hf i j Hij.
    cutrewrite (j = S (j - S i) + i).
    apply clos_trans_succ_rec with (n := n); auto.
    omega.
    omega.
  Qed.    

  Let sR R x y := R x y /\ ~ R y x.

  Fact trans_strict_prop R x y : transitive _ R -> clos_trans_1n _ (sR R) x y -> ~ R y x.
  Proof.
    intros HR; induction 1 as [ x y (H1 & H2) | x y z (H1 & H2) H IH ]; intros H3.
    contradict H2; auto.
    apply IH.
    apply HR with x; auto.
  Qed.

End transitivity.

(* p iterate of a binary relation *)

Section iterated.

  Variables (X : Type).

  Implicit Type (R : X -> X -> Prop). 

  Fixpoint rel_iter R p :=
    match p with 
      | 0   => @eq _
      | S p => R o rel_iter R p
    end.

  Fact rel_iter_mono (R S : X -> X -> Prop) p : R inc2 S -> rel_iter R p inc2 rel_iter S p.
  Proof.
    intros H.
    induction p; simpl; intros u v; auto.
    intros (k & ? & ?); exists k; split; auto.
  Qed.

  Fixpoint rel_iter_rev R p :=
    match p with 
      | 0   => @eq _
      | S p => rel_iter_rev R p o R
    end.

  Fact rel_comp_eq_left R : @eq _ o R ~eq2 R.
  Proof. 
    firstorder; subst; auto.
  Qed.

  Fact rel_comp_eq_right R : R o @eq _ ~eq2 R.
  Proof. 
    firstorder; subst; auto.
  Qed.

  Fact rel_comp_assoc (R S T : X -> X -> Prop) : (R o S) o T ~eq2 R o (S o T).
  Proof.
    firstorder.
  Qed.

  Fact rel_comp_congr_left (R S T : X -> X -> Prop) : S ~eq2 T -> R o S ~eq2 R o T.
  Proof.
    firstorder.
  Qed.  

  Fact rel_iter_assoc R p q : rel_iter_rev R (S p) o rel_iter R q 
                         ~eq2 rel_iter_rev R    p  o rel_iter R (S q).
  Proof.
    apply rel_comp_assoc.
  Qed.

  Fact rel_iter_plus R a b : rel_iter R (a+b) ~eq2 rel_iter R a o rel_iter R b.
  Proof.
    induction a; simpl.
    apply eq2_sym, rel_comp_eq_left.
    apply eq2_sym, eq2_trans with (1 := rel_comp_assoc _ _ _), 
          eq2_sym, rel_comp_congr_left; auto.
  Qed.

  Fact rel_iter_rev_plus R p q : rel_iter_rev R p o rel_iter R q
                          ~eq2 rel_iter R (p+q).
  Proof.
    revert q; induction p; intros q.
    apply eq2_trans with (1 := rel_comp_eq_left _), eq2_refl.

    apply eq2_trans with (1 := rel_iter_assoc _ _ _).
    cutrewrite (S p + q = p + S q); try omega; apply IHp.
  Qed.

  Fact rel_iter_rev_eq R p : rel_iter_rev R p ~eq2 rel_iter R p.
  Proof.
    apply eq2_trans with (1 := eq2_sym _ _ (rel_comp_eq_right _)).
    apply eq2_trans with (1 := rel_iter_rev_plus _ p 0); simpl.
    rewrite plus_comm.
    apply eq2_refl.
  Qed.

End iterated.

Section iter.
  
  Variable (A : Type) (f : A -> A).
  
  Definition iter n x := nat_rect _ x (fun _ => f) n.
  
  Fact iter_app x a b : iter (a+b) x = iter a (iter b x).
  Proof. induction a; simpl; f_equal; auto. Qed.
    
  Fact iter_S x n : iter (S n) x = iter n (f x).
  Proof.
    replace (S n) with (n+1) by omega.
    rewrite iter_app; auto.
  Qed.
    
End iter.
 
(* monotonicity / continuity *)

Section rel_props.

  Variable X : Type.

  Implicit Types (R S : relation X) (K : nat -> relation X).

  Section defs. 

    Variable (Y : Type).
 
    Variable f : relation X -> relation Y.
    
    Definition op_monotonic := forall R S, R inc2 S -> f R inc2 f S.
    Definition seq_increasing K := forall n, K n inc2 K (S n). 
    Definition op_w_continuous := forall K, seq_increasing K -> f (fun x y => exists n, K n x y) inc2 fun x y => exists n, f (K n) x y.

    Fact seq_inc_all K : seq_increasing K -> forall n m, n <= m -> K n inc2 K m.
    Proof.
      intros HK.
      induction 1; auto.
    Qed.

    Hypothesis H1 : op_monotonic.
    Hypothesis H2 : op_w_continuous.

    Fact op_mono_w_cont_eq K a b : seq_increasing K -> (f (fun x y => exists n, K n x y) a b <-> exists n, f (K n) a b).
    Proof.
      intros H; split.
      intros; apply H2; auto.
      intros (n & Hn); revert Hn; apply H1.
      exists n; auto.
    Qed.

  End defs.

  Fact clos_trans_mono : op_monotonic (clos_trans X).
  Proof.
    intros R S H x y.
    induction 1 as [ | ? y ].
    constructor 1; auto.
    constructor 2 with y; auto.
  Qed.
  
  Fact clos_trans_w_cont : op_w_continuous (clos_trans X).
  Proof.
    intros K HK x y.
    induction 1 as [ x y (n & Hxy) | x y z H1 (n & H2) H3 (m & H4)  ].
    exists n; constructor 1; auto.
    exists (n+m).
    constructor 2 with y.
    revert H2; apply clos_trans_mono, seq_inc_all with (1 := HK), le_plus_l.
    revert H4; apply clos_trans_mono, seq_inc_all with (1 := HK), le_plus_r.
  Qed.

End rel_props.

Section op_comp.

  Variable (X Y Z : Type) (f : relation X -> relation Y) (g : relation Y -> relation Z).
  
  Hypothesis Hf1 : op_monotonic f.
  Hypothesis Hf2 : op_w_continuous f.
  
  Hypothesis Hg1 : op_monotonic g.
  Hypothesis Hg2 : op_w_continuous g.
  
  Fact op_comp_monotonic : op_monotonic (fun R => g (f R)).
  Proof.
    intros ? ? H; apply Hg1, Hf1, H.
  Qed. 

  Fact op_comp_w_continuous : op_w_continuous (fun R => g (f R)).
  Proof.
    intros K HK x y H.
    rewrite <- op_mono_w_cont_eq; auto.
    revert H; apply Hg1.
    clear x y; intros x y.
    apply Hf2; auto.
    intros n; apply Hf1, HK.
  Qed.

End op_comp.

(* restrictions *)

Definition add_one X (A : X -> Prop) y := fun z => A z \/ y = z.
Definition rel_restriction X (R : X -> X -> Prop) A := fun x y => R x y /\ A x /\ A y.
    
Infix "restr" := (@rel_restriction _) (at level 71, left associativity).

Section restrictions.

  Variables X : Type.

  Implicit Types (A B : X -> Prop) (R S : X -> X -> Prop).

  Fact rel_restr_restr R A B : R restr A restr B ~eq2 R restr (A cap1 B).
  Proof.
    split; intros ? ?; cbv; tauto.
  Qed.

  Fact Acc_dec R S x : R inc2 S -> Acc S x -> Acc R x.
  Proof.
    intros HS; induction 1 as [ x _ IH ].
    constructor; intros; apply IH, HS, H.
  Qed.

End restrictions.

(* lifting, for almost full relations *)

Definition lift_rel X (R : X -> X -> Prop) a := fun x y => R x y \/ R a x.

Infix "rlift" := (@lift_rel _) (at level 69, left associativity).

Section rlift_rel_restr_eq.

  Variable (X : Type) (P : X -> Prop) (R S : X -> X -> Prop).
  
  Fact litf_rel_restr_eq t : P t -> R <# P #> ~eq2 S <# P #> -> (R rlift t) <# P #> ~eq2 (S rlift t) <# P #>.
  Proof.
    intros Ht (H1 & H2); split; intros a b; 
      [ generalize (H1 a b) (H1 (exist _ t Ht) a) | generalize (H2 a b) (H2 (exist _ t Ht) a) ]; 
      destruct a; destruct b; unfold lift_rel; simpl; tauto.
  Qed.

  Fact restr_lift_rel_eq t : R <# P #> rlift t ~eq2 (R rlift (proj1_sig t)) <# P #>.
  Proof.
    destruct t as (t & Ht); simpl.
    split; intros (?&?) (?&?); cbv; auto.
  Qed.

End rlift_rel_restr_eq.

Fixpoint lift_rel_list X (R : X -> X -> Prop) ll := 
  match ll with 
    | nil   => R
    | k::ll => (lift_rel_list R ll) rlift k
  end.

Infix "lrlift" := (@lift_rel_list _) (at level 69, left associativity).

Section lift.

  Variables (X : Type).

  Implicit Type R S : X -> X -> Prop.

  Fact lift_rel_inc R S a : R inc2 S -> R rlift a inc2 S rlift a.
  Proof.
    intros H x y; generalize (H x y) (H a x); unfold lift_rel; tauto.
  Qed.

  Fact lift_rel_list_incr R ll : R inc2 R lrlift ll.
  Proof.
    induction ll; simpl; auto.
    left; auto.
  Qed.

  Fact lift_rel_list_In R x y ll : R y x -> In y ll -> forall z, (R lrlift ll) x z.
  Proof.
    intros H1 H2; induction ll; simpl in H2 |- *; intros z.
    contradict H2.
    destruct H2 as [ | H2 ].
    subst; right; apply lift_rel_list_incr; auto.
    left; auto.
  Qed.

End lift.

Notation rel_pirr := ((fun X (R : relation X) => forall (x y : X) (H1 H2 : R x y), H1 = H2) _).

Fact eq_option_nat_dec (x y : option nat) : { x = y } + { x <> y }.
Proof.
  revert x y; intros [x|] [y|]; try (right; discriminate; fail); try (left; auto; fail).
  destruct (eq_nat_dec x y) as [ | C ]; subst; auto.
  right; contradict C; injection C; auto.
Defined.

Fact eq_dec_pirr X : (forall x y : X, { x = y } + { x <> y}) -> rel_pirr (@eq X).
Proof.
  simpl; intros; apply UIP_dec; auto.
Qed.

Definition eq_bool_pirr := eq_dec_pirr bool_dec.
Definition eq_nat_pirr := eq_dec_pirr eq_nat_dec.
Definition eq_option_nat_pirr := eq_dec_pirr eq_option_nat_dec.

Section le_pirr.

  (* a dependent induction principle for le *)
  
  Scheme le_indd := Induction for le Sort Prop.

  Theorem le_pirr : rel_pirr le.
  Proof.
    simpl; intros n ? H1.
    induction H1 as [ | m H1 IH ] using le_indd; intro H2.

    change (le_n n) with (eq_rect _ (fun n0 => n <= n0) (le_n n) _ eq_refl).
    generalize (eq_refl n).
    pattern n at 2 4 6 10, H2. 
    case H2; [intro E | intros m l E].
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
    contradiction (le_Sn_n m); subst; auto.
    
    change (le_S n m H1) with (eq_rect _ (fun n0 => n <= n0) (le_S n m H1) _ eq_refl).
    generalize (eq_refl (S m)).
    pattern (S m) at 1 3 4 6, H2.
    case H2; [intro E | intros p H3 E].
    contradiction (le_Sn_n m); subst; auto.
    injection E; intro; subst.
    rewrite (IH H3).
    rewrite UIP_dec with (p1 := E) (p2 := eq_refl); auto.
    apply eq_nat_dec.
  Qed.

End le_pirr.

Fact lt_pirr : rel_pirr lt.
Proof. simpl; intros; apply le_pirr. Qed.

Definition rel_fsum X (n : nat) : (forall k, k < n -> relation X) -> relation ({ k | k < n } * X).
Proof.
  intros Hll ((a & Ha) & y1) ((b & Hb) & y2).
  destruct (eq_nat_dec a b).
  exact (Hll _ Ha y1 y2).
  exact False.
Defined.

Section rel_dsum.

  Variables (X : nat -> Type) (R : forall n, X n -> X n -> Prop).

  Definition rel_dsum (a b : sigT X) :=
    match a, b with
      | existT _ n1 x1, existT _ n2 x2 => exists H : n1 = n2, R (eq_rect _  X x1 _ H) x2
    end.
    
  (* For those who are not conviced with what eq_rect means (type cast), here
     are the properties we want for the dependent sum *)
      
  Fact rel_dsum_prop1 n x y : @R n x y -> rel_dsum (existT _ _ x) (existT _ _ y).
  Proof.
    exists eq_refl; auto.
  Qed.
  
  Fact rel_dsum_prop2 n x m y : rel_dsum (existT _ n x) (existT _ m y) -> n = m.
  Proof. intros (? & _); auto. Qed.
  
  Fact rel_dsum_prop3 n x y : rel_dsum (existT _ n x) (existT _ n y) -> R x y.
  Proof.
    intros (E & H).
    rewrite (eq_nat_pirr E eq_refl) in H; auto.
  Qed.
  
End rel_dsum.

