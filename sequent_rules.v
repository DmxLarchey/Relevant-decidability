(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Permutation.

Require Import tacs rel_utils list_utils finite relevant_contract.
Require Import tree proof rules.
Require Import formula.

Set Implicit Arguments.

Definition Seq := (list Form * Form)%type.

Fact Seq_eq_dec (s1 s2 : Seq) : { s1 = s2 } + { s1 <> s2 }.
Proof.
  decide equality.
  apply Form_eq_dec.
  apply list_eq_dec.
  intros; apply Form_eq_dec.
Qed.

Local Hint Resolve Seq_eq_dec : core.

Local Notation " g '|--' a " := ((g,a):Seq) (at level 70, no associativity).

Implicit Type (c : Seq) (ll : list Seq).

Definition sf_Seq c := 
  match c with 
    (g, a) => fun y => (exists x, In x g /\ sf_Form x y) \/ sf_Form a y 
  end.

Fact sf_Seq_finite_t c : finite_t (sf_Seq c).
Proof.
  destruct c as (s,a); simpl.
  apply finite_t_cup.
  apply finite_t_relmap. 
  exists s; tauto.
  intros; apply sf_Form_finite_t.
  apply sf_Form_finite_t.
Qed.

Definition LR_sf c d := sf_Seq d inc1 sf_Seq c.

Local Notation sf := LR_sf.

Fact LR_sf_refl c : sf c c.
Proof. red; auto. Qed.
  
Fact LR_sf_trans c d e : sf c d -> sf d e -> sf c e.
Proof. unfold LR_sf; auto. Qed.

(** All the following rules are permutation absorbing meaning
   that they are stable under permutation on the LHS of |- *)

Section Identity_rule.

  (** Identity rule for R sequent systems 
  
               ---------- [id]
                 A |- A
  *)
  
  Inductive rule_id : Seq -> list Seq -> Prop :=
    | in_rule_id : forall a, rule_id (a::nil |-- a) nil.

  Fact rule_id_inv c ll : 
    rule_id c ll -> ll = nil /\ exists a, c = (a::nil |-- a).
  Proof. induction 1 as [ a ]; split; auto; exists a; auto. Qed.
  
  Fact sf_rule_id c ll : rule_id c ll -> Forall (sf c) ll.
  Proof. induction 1 as [ ? ]; constructor. Qed.
  
  Definition rule_id_inst := Form.
  Definition rule_id_map : rule_id_inst -> Seq * list Seq.
  Proof. intros a; exact ( a :: nil |-- a , nil ). Defined. 
  
  Fact rule_id_map_prop : soundly_represents rule_id rule_id_map.
  Proof. simpl; constructor. Qed. 
  
  Fact rule_id_finite : finitely_represents rule_id rule_id_map.
  Proof.
    intros ( [ | y [ | z ll ] ], a).
    
    exists nil.
    intros h; split.
    intros H.
    apply rule_id_inv in H.
    destruct H as (_ & ? & ?); discriminate.
    intros (? & ? & []).
    
    destruct (Form_eq_dec a y) as [ | C ].
    subst y.
    exists (a :: nil).
    intros h; split. 
    intros H.
    apply rule_id_inv in H.
    destruct H as (G & u & H).
    inversion H.
    subst u h.
    exists a; simpl; auto.
    intros (i & H1 & H2).
    inversion H1; subst i h.
    constructor.
    
    exists nil.
    intros h; split.
    intros H.
    apply rule_id_inv in H.
    destruct H as (_ & u & Hu).
    inversion Hu.
    subst y u.
    destruct C; trivial.
    intros (? & _ & []).
    
    exists nil.
    intros h; split.
    intros H.
    apply rule_id_inv in H.
    destruct H as (_ & u & Hu).
    discriminate.
    intros (? & _ & []).
  Qed.
  
  Hint Resolve rule_id_map_prop rule_id_finite : core.

  Fact rule_id_reif c hs : rule_id c hs -> { i | rule_id_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := rule_id); auto. Qed.
  
  Fact rule_id_dec c hs : { rule_id c hs } + { ~ rule_id c hs }.
  Proof. apply rule_dec with (f := rule_id_map); auto. Qed.

  Fact rule_id_finite_t c : finite_t (rule_id c).
  Proof. apply rule_finite_t with (f := rule_id_map); auto. Qed.
  
End Identity_rule.

Section Axiom_rule.

  (** Identity rule for R sequent systems 
  
               ------------- [ax]
                 A,ga |- A
  *)
  
  Inductive rule_ax : Seq -> list Seq -> Prop :=
    | in_rule_ax : forall l a r, rule_ax (l++a::r |-- a) nil.

  Fact rule_ax_inv c ll : 
    rule_ax c ll -> ll = nil /\ exists l a r, c = (l++a::r |-- a).
  Proof. induction 1 as [ l a r ]; split; auto; exists l, a, r; auto. Qed.
  
  Fact sf_rule_ax c ll : rule_ax c ll -> Forall (sf c) ll.
  Proof. induction 1 as [ ? ]; constructor. Qed.
  
  Definition rule_ax_inst := (list Form * Form * list Form)%type.
  Definition rule_ax_map : rule_ax_inst -> Seq * list Seq.
  Proof. intros ((l,a),r); exact ( l++a :: r |-- a , nil ). Defined. 
  
  Fact rule_ax_map_prop : soundly_represents rule_ax rule_ax_map.
  Proof. intros ((?,?),?); simpl; constructor. Qed. 
  
  Fact rule_ax_finite : finitely_represents rule_ax rule_ax_map.
  Proof.
    intros (ll, a).
    
    destruct (In_dec Form_eq_dec a ll) as [ H | H ].
    destruct (In_split_dec Form_eq_dec a ll H) as (l & r & ?); subst ll.
    
    clear H.
    exists (((l,a),r) :: nil).
    intros hs; split.
    
    intros H.
    apply rule_ax_inv, proj1 in H; subst.
    exists ((l,a),r); simpl; tauto.
    
    intros (((l',a'),r') & H1 & [ H2 | [] ]).
    inversion H2; subst l' a' r'; clear H2.
    simpl in H1.
    inversion H1; subst hs; constructor.
    
    exists nil.
    intros hs; split.
    
    intros H1.
    apply rule_ax_inv, proj2 in H1.
    exfalso; destruct H1 as (l & a' & r & H1).
    inversion H1; subst ll a'.
    apply H, in_or_app; right; left; auto.
    
    intros (? & _ & []).
  Qed.

  Hint Resolve rule_ax_map_prop rule_ax_finite : core.

  Fact rule_ax_reif c hs : rule_ax c hs -> { i | rule_ax_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := rule_ax); auto. Qed.
  
  Fact rule_ax_dec c hs : { rule_ax c hs } + { ~ rule_ax c hs }.
  Proof. apply rule_dec with (f := rule_ax_map); auto. Qed.

  Fact rule_ax_finite_t c : finite_t (rule_ax c).
  Proof. apply rule_finite_t with (f := rule_ax_map); auto. Qed.
  
End Axiom_rule.

Section Right_implication_rule.
  
  (** Right implication rule for R sequent systems 
  
            A,ga |- B
          -------------- [r]
            ga |- A%>B 

  *)

  Inductive LR_rule_r : Seq -> list Seq -> Prop :=
    | in_LR_r : forall th a b, LR_rule_r (th    |-- a %> b) 
                                        ((a::th |-- b) 
                                        :: nil ). 
                                         
  Fact LR_rule_r_inv c ll : LR_rule_r c ll -> exists ga a b,
                                        c  = (ga |-- a %> b)
                                     /\ ll = ((a::ga |-- b) :: nil).
  Proof. induction 1 as [ ga a b ]; exists ga, a, b; auto. Qed.
  
  Fact sf_LR_rule_r c ll : LR_rule_r c ll -> Forall (sf c) ll.
  Proof.
    induction 1 as [ ga a b ]; constructor.
    2: constructor.
    intros x [ (y & H1 & H2) | Hx ].
    destruct H1 as [ H1 | H1 ].
    subst.
    right; right; tauto.
    left; exists y; auto.
    right; right; tauto.
  Qed.
  
  Definition LR_rule_r_inst := (list Form * Form * Form)%type.
  
  Definition LR_rule_r_map : LR_rule_r_inst -> Seq * list Seq.
  Proof.
    intros ((ga,a),b).
    exact ((ga |-- a %> b), ((a::ga |-- b) :: nil) ).
  Defined.
  
  Fact LR_rule_r_map_prop : soundly_represents LR_rule_r LR_rule_r_map.
  Proof. intros ((ga,a),b); simpl; constructor. Qed.
  
  Fact LR_rule_r_finite : finitely_represents LR_rule_r LR_rule_r_map.
  Proof.
    intros (ga,[ v | op a b ]).
    
    exists nil.
    intros h; split.
    intros H.
    apply LR_rule_r_inv in H.
    destruct H as (? & ? & ? & ? & _); discriminate.
    intros ( ? & _ & [] ).
    
    exists ( ((ga,a),b) :: nil ).
    intros h; split.
    intros H.
    apply LR_rule_r_inv in H.
    destruct H as (th & u & v & H1 & H2).
    inversion H1; subst th u v h.
    exists ((ga,a),b); simpl; auto.
    intros ( ((th,u),v) & H1 & [ H2 | [] ] ).
    inversion H1.
    inversion H2. 
    subst th u v h.
    constructor.
  Qed.
  
  Hint Resolve LR_rule_r_map_prop LR_rule_r_finite : core.
  
  Fact LR_rule_r_reif c hs : LR_rule_r c hs -> { i | LR_rule_r_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := LR_rule_r); auto. Qed.
  
  Fact LR_rule_r_dec c hs : { LR_rule_r c hs } + { ~ LR_rule_r c hs }.
  Proof. apply rule_dec with (f := LR_rule_r_map); auto. Qed.
  
  Fact LR_rule_r_finite_t c : finite_t (LR_rule_r c).
  Proof. apply rule_finite_t with (f := LR_rule_r_map); auto. Qed.
  
End Right_implication_rule.

Section Right_disjunction_rule.
  
  (** Right implication rule for R sequent systems 
  
            ga |- A or B
          -------------- [r]
            ga |- A∨B 

  *)

  Inductive LR_disj_r : Seq -> list Seq -> Prop :=
    | in_LR_disj_r : forall (s : bool) th a b, LR_disj_r (th    |-- a∨b) 
                                           ((th |-- if s then a else b) 
                                           :: nil ). 
                                         
  Fact LR_disj_r_inv c ll : LR_disj_r c ll -> exists (s : bool) ga a b,
                                        c  = (ga |-- a∨b)
                                     /\ ll = ((ga |-- if s then a else b) :: nil).
  Proof. induction 1 as [ s ga a b ]; exists s, ga, a, b; auto. Qed.
  
  Fact sf_LR_disj_r c ll : LR_disj_r c ll -> Forall (sf c) ll.
  Proof.
    induction 1 as [ s ga a b ]; constructor.
    2: constructor.
    intros x [ (y & H1 & H2) | Hx ].
    left; exists y; auto.
    right; right; destruct s; tauto.
  Qed.
  
  Definition LR_disj_r_inst := (bool * list Form * Form * Form)%type.
  
  Definition LR_disj_r_map : LR_disj_r_inst -> Seq * list Seq.
  Proof.
    intros (((s,ga),a),b).
    exact ((ga |-- a ∨ b), ((ga |-- if s then a else b) :: nil) ).
  Defined.
  
  Fact LR_disj_r_map_prop : soundly_represents LR_disj_r LR_disj_r_map.
  Proof. intros (((s,ga),a),b); simpl; constructor. Qed.
  
  Fact LR_disj_r_finite : finitely_represents LR_disj_r LR_disj_r_map.
  Proof.
    intros (ga,[ v | op a b ]).
    
    exists nil.
    intros h; split.
    intros H.
    apply LR_disj_r_inv in H.
    destruct H as (? & ? & ? & ? & ? & _); discriminate.
    intros ( ? & _ & [] ).
    
    exists ( (((true,ga),a),b) :: (((false,ga),a),b) :: nil ).
    intros h; split.
    intros H.
    apply LR_disj_r_inv in H.
    destruct H as (s & th & u & v & H1 & H2).
    inversion H1; subst th u v h.
    destruct s.
      exists (((true,ga),a),b); simpl; auto.
      exists (((false,ga),a),b); simpl; auto.
    intros ( (((s,th),u),v) & H1 & [ H2 | [ H2 | [] ] ] ).
    inversion H1.
    inversion H2. 
    subst th u v h.
    constructor 1 with (s := true).
    inversion H1.
    inversion H2. 
    subst th u v h.
    constructor 1 with (s := false).
  Qed.
  
  Hint Resolve LR_disj_r_map_prop LR_disj_r_finite : core.
  
  Fact LR_disj_r_reif c hs : LR_disj_r c hs -> { i | LR_disj_r_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := LR_disj_r); auto. Qed.
  
  Fact LR_disj_r_dec c hs : { LR_disj_r c hs } + { ~ LR_disj_r c hs }.
  Proof. apply rule_dec with (f := LR_disj_r_map); auto. Qed.
  
  Fact LR_disj_r_finite_t c : finite_t (LR_disj_r c).
  Proof. apply rule_finite_t with (f := LR_disj_r_map); auto. Qed.
  
End Right_disjunction_rule.

Section Left_implication_rule_LR1.
  
  (** Left implication rule for R sequent systems 
      This is the "usual" rule that does not absorb contraction 
      
             ga |- A     B,de |- C
           ------------------------- [l]
                 A%>B,ga,de |- C
      
  *)

  Inductive LR_rule_l : Seq -> list Seq -> Prop :=
    | in_LR_l : forall ga de th a b x, 
                                 th ~p (a %> b) :: ga ++ de
                              -> LR_rule_l (th   |-- x)
                                        ( (ga    |-- a)
                                       :: (b::de |-- x)
                                       :: nil ).

  Fact LR_rule_l_inv c ll : LR_rule_l c ll -> exists ga de th a b x,
                                        c = (th |-- x)
                                     /\ ll = ( (ga |-- a) :: (b :: de |-- x) :: nil )
                                     /\ th ~p (a %> b) :: ga ++ de.
  Proof. induction 1 as [ ga de th a b x ]; exists ga, de, th, a, b, x; auto. Qed.

  Definition LR_rule_l_inst := { c : list Form * list Form * list Form * Form * Form * Form 
                                   | match c with (((((ga,de),th),a),b),x) => th ~p (a %> b) :: ga ++ de end }%type.
  
  Definition LR_rule_l_map : LR_rule_l_inst -> Seq * list Seq.
  Proof.
    intros ( (((((ga,de),th),a),b),x) & _ ).
    exact (th |-- x , ( (ga |-- a) :: (b :: de |-- x) :: nil ) ).
  Defined.
  
  Fact LR_rule_l_map_prop : soundly_represents LR_rule_l LR_rule_l_map.
  Proof. intros ((((((ga,de),th),a),b),x) & H); simpl; constructor; auto. Qed.

  Fact LR_rule_l_finite : finitely_represents LR_rule_l LR_rule_l_map.
  Proof.
    intros (th,x).
    generalize (pick_split_finite_t th); intros (l1 & Hl1).
    set (ll := flat_map (fun u => match u with 
                          | (a %> b,(ga,de)) => (((((ga,de),th),a),b),x) :: nil
                          | _ => nil
                        end) l1).
    assert (forall u, In u ll -> match u with (((((ga,de),th),a),b),x) => th ~p (a %> b) :: ga ++ de end) as Hll.
      intros (((((ga,de),th'),a),b),x'); unfold ll; rewrite in_flat_map.
      intros (([ | [] a' b' ],(p,q)) & H1 & H2);simpl in *; try tauto.
      destruct H2 as [ E | [] ].
      inversion E; subst p q th' a' b' x'.
      apply Hl1 in H1; auto.
      
    exists (list_Forall_sig _ _ Hll).
    intros h; split.
    
    intros H.
    apply LR_rule_l_inv in H.
    destruct H as (ga & de & th' & a & b & x' & E & H1 & H2).
    inversion E; subst th' x' h.
    assert (In (((((ga,de),th),a),b),x) ll) as H3.
      unfold ll; apply in_flat_map.
      exists (a %> b, (ga,de)); split; simpl; auto.
      apply Hl1; auto.
    generalize (list_Forall_sig_In_refl _ _ Hll _ H3).
    intros H4.
    match goal with [ H : In ?x _ |- _ ] => exists x end; split; auto.
    
    intros (((((((ga,de),th'),a),b),x') & H) & H1 & _).
    simpl in H1.
    inversion H1; subst th' x' h.
    constructor; auto.
  Qed.
  
  Hint Resolve LR_rule_l_map_prop LR_rule_l_finite : core.
 
  Fact LR_rule_l_reif c hs : LR_rule_l c hs -> { i | LR_rule_l_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := LR_rule_l); auto. Qed.
  
  Fact LR_rule_l_dec c hs : { LR_rule_l c hs } + { ~ LR_rule_l c hs }.
  Proof. apply rule_dec with (f := LR_rule_l_map); auto. Qed.
  
  Fact LR_rule_l_finite_t c : finite_t (LR_rule_l c).
  Proof. apply rule_finite_t with (f := LR_rule_l_map); auto. Qed.
  
End Left_implication_rule_LR1.

Section Left_disjunction_rule_LR1.
  
  (** Left implication rule for R sequent systems 
      This is the "usual" rule that does not absorb contraction 
      
             A,ga |- C   B,ga |- C
           ------------------------- [l]
                 A ∨ B,ga |- C
      
  *)

  Inductive LR_disj_l : Seq -> list Seq -> Prop :=
    | in_LR_disj_l : forall ga th a b x, 
                                 th ~p a ∨ b :: ga
                              -> LR_disj_l (th   |-- x)
                                        ( (a::ga |-- x)
                                       :: (b::ga |-- x)
                                       :: nil ).

  Fact LR_disj_l_inv c ll : LR_disj_l c ll -> exists ga th a b x,
                                        c = (th |-- x)
                                     /\ ll = ( (a::ga |-- x) :: (b :: ga |-- x) :: nil )
                                     /\ th ~p a∨b :: ga.
  Proof. induction 1 as [ ga th a b x ]; exists ga, th, a, b, x; auto. Qed.

  Definition LR_disj_l_inst := { c : list Form * list Form * Form * Form * Form 
                                   | match c with ((((ga,th),a),b),x) => th ~p a∨b :: ga end }%type.
  
  Definition LR_disj_l_map : LR_disj_l_inst -> Seq * list Seq.
  Proof.
    intros ( ((((ga,th),a),b),x) & _ ).
    exact (th |-- x , ( (a::ga |-- x) :: (b :: ga |-- x) :: nil ) ).
  Defined.
  
  Fact LR_disj_l_map_prop : soundly_represents LR_disj_l LR_disj_l_map.
  Proof. intros (((((ga,th),a),b),x) & H); simpl; constructor; auto. Qed.

  Fact LR_disj_l_finite : finitely_represents LR_disj_l LR_disj_l_map.
  Proof.
    intros (th,x).
    generalize (pick_finite_t th); intros (l1 & Hl1).
    set (ll := flat_map (fun u => match u with 
                          | (a∨b,ga) => ((((ga,th),a),b),x) :: nil
                          | _ => nil
                        end) l1).
    assert (forall u, In u ll -> match u with ((((ga,th),a),b),x) => th ~p a∨b :: ga end) as Hll.
      intros ((((ga,th'),a),b),x'); unfold ll; rewrite in_flat_map.
      intros (([ | [] a' b' ],p) & H1 & H2); simpl in *; try tauto.
      destruct H2 as [ E | [] ].
      inversion E; subst p a' b' x' th'.
      apply Hl1 in H1; auto.
      
    exists (list_Forall_sig _ _ Hll).
    intros h; split.
    
    intros H.
    apply LR_disj_l_inv in H.
    destruct H as (ga & th' & a & b & x' & E & H1 & H2).
    inversion E; subst th' x' h.
    assert (In ((((ga,th),a),b),x) ll) as H3.
      unfold ll; apply in_flat_map.
      exists (a∨b, ga); split; simpl; auto.
      apply Hl1; auto.
    generalize (list_Forall_sig_In_refl _ _ Hll _ H3).
    intros H4.
    match goal with [ H : In ?x _ |- _ ] => exists x end; split; auto.
    
    intros ((((((ga,th'),a),b),x') & H) & H1 & _).
    simpl in H1.
    inversion H1; subst th' x' h.
    constructor; auto.
  Qed.
  
  Hint Resolve LR_disj_l_map_prop LR_disj_l_finite : core.
 
  Fact LR_disj_l_reif c hs : LR_disj_l c hs -> { i | LR_disj_l_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := LR_disj_l); auto. Qed.
  
  Fact LR_disj_l_dec c hs : { LR_disj_l c hs } + { ~ LR_disj_l c hs }.
  Proof. apply rule_dec with (f := LR_disj_l_map); auto. Qed.
  
  Fact LR_disj_l_finite_t c : finite_t (LR_disj_l c).
  Proof. apply rule_finite_t with (f := LR_disj_l_map); auto. Qed.
  
End Left_disjunction_rule_LR1.


Section Left_implication_rule_LI2.
  
  (** Left implication rule for IL sequent systems 
      This is the contraction absorbing rule
      
             A%>B,ga |- A     A%>B,B,ga |- C
           ----------------------------------- [l]
                      A%>B,ga |- C
      
  *)

  Inductive LI2_rule_l : Seq -> list Seq -> Prop :=
    | in_LI2_l : forall ga th a b x, 
                                 th ~p (a %> b) :: ga
                              -> LI2_rule_l (th   |-- x)
                                        ( (a %> b :: ga  |-- a)
                                       :: (a %> b :: b::ga |-- x)
                                       :: nil ).

  Fact LI2_rule_l_inv c ll : LI2_rule_l c ll -> exists ga th a b x,
                                        c = (th |-- x)
                                     /\ ll = ( (a %> b :: ga |-- a) :: (a %> b :: b :: ga |-- x) :: nil )
                                     /\ th ~p (a %> b) :: ga.
  Proof. induction 1 as [ ga th a b x ]; exists ga, th, a, b, x; auto. Qed.
  
  Fact sf_LI2_rule_l c ll : LI2_rule_l c ll -> Forall (sf c) ll.
  Proof. 
    induction 1 as [ ga th a b x ]. 
    
    constructor.
    intros c [ (d & [ Hd1 | Hd1 ] & Hd2) | Hc ].
    
    subst; left; exists (a %> b); split; auto.
    apply Permutation_in with (1 := Permutation_sym H); left; auto.
    
    left; exists d; split; auto.
    apply Permutation_in with (1 := Permutation_sym H); right; auto.
    
    left; exists (a %> b); split.
    apply Permutation_in with (1 := Permutation_sym H); left; auto.
    right; left; auto.
    
    constructor.
    intros c [ (d & [ Hd1 | [ Hd1 | Hd1 ] ] & Hd2) | Hc ].
    
    subst d; left; exists (a %> b); split; auto.
    apply Permutation_in with (1 := Permutation_sym H); left; auto.
    
    subst d; left; exists (a %> b); split; auto.
    apply Permutation_in with (1 := Permutation_sym H); left; auto.
    
    right; auto.
    
    left; exists d; split; auto.
    apply Permutation_in with (1 := Permutation_sym H); right; auto.
    
    right; auto.
    
    constructor.
  Qed.
 
  Definition LI2_rule_l_inst := { c : list Form * list Form * Form * Form * Form 
                                   | match c with ((((ga,th),a),b),x) => th ~p (a %> b) :: ga end }%type.
  
  Definition LI2_rule_l_map : LI2_rule_l_inst -> Seq * list Seq.
  Proof.
    intros ( ((((ga,th),a),b),x) & _ ).
    exact (th |-- x , ( (a %> b :: ga |-- a) :: (a %> b :: b :: ga |-- x) :: nil ) ).
  Defined.
  
  Fact LI2_rule_l_map_prop : soundly_represents LI2_rule_l LI2_rule_l_map.
  Proof. intros (((((ga,th),a),b),x) & H); simpl; constructor; auto. Qed.
  
  Fact LI2_rule_l_finite : finitely_represents LI2_rule_l LI2_rule_l_map.
  Proof.
    intros (th,x).
    generalize (pick_finite_t th); intros (l1 & Hl1).
    set (ll := flat_map (fun u => match u with 
                          | (a %> b,ga) => ((((ga,th),a),b),x) :: nil
                          | _ => nil
                        end) l1).
    assert (forall u, In u ll -> match u with ((((ga,th),a),b),x) => th ~p (a %> b) :: ga end) as Hll.
      intros ((((ga,th'),a),b),x'); unfold ll; rewrite in_flat_map.
      intros (([ | [] a' b' ],p) & H1 & H2); simpl in *; try tauto.
      destruct H2 as [ E | [] ].
      inversion E; subst p th' a' b' x'.
      apply Hl1 in H1; auto.
      
    exists (list_Forall_sig _ _ Hll).
    intros h; split.
    
    intros H.
    apply LI2_rule_l_inv in H.
    destruct H as (ga & th' & a & b & x' & E & H1 & H2).
    inversion E; subst th' x' h.
    assert (In ((((ga,th),a),b),x) ll) as H3.
      unfold ll; apply in_flat_map.
      exists (a %> b, ga); split; simpl; auto.
      apply Hl1; auto.
    generalize (list_Forall_sig_In_refl _ _ Hll _ H3).
    intros H4.
    match goal with [ H : In ?x _ |- _ ] => exists x end; split; auto.
    
    intros ((((((ga,th'),a),b),x') & H) & H1 & _).
    simpl in H1.
    inversion H1; subst th' x' h.
    constructor; auto.
  Qed.
  
  Hint Resolve LI2_rule_l_map_prop LI2_rule_l_finite : core.
 
  Fact LI2_rule_l_reif c hs : LI2_rule_l c hs -> { i | LI2_rule_l_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := LI2_rule_l); auto. Qed.
  
  Fact LI2_rule_l_dec c hs : { LI2_rule_l c hs } + { ~ LI2_rule_l c hs }.
  Proof. apply rule_dec with (f := LI2_rule_l_map); auto. Qed.
  
  Fact LI2_rule_l_finite_t c : finite_t (LI2_rule_l c).
  Proof. apply rule_finite_t with (f := LI2_rule_l_map); auto. Qed.
  
End Left_implication_rule_LI2.

Section Contraction_rule.
  
  (** Contraction rule for R sequent systems 
  
             A,A,ga |- B
           -------------- [c]
              A,ga |- B
  
  *)
  
  Inductive rule_cntr : Seq -> list Seq -> Prop :=
    | in_rule_cntr : forall ga th a b, ga ~p a :: th
                                  -> rule_cntr (ga |-- b) ( (a :: a :: th |-- b) :: nil ).
                                 
  Fact rule_cntr_inv c ll : rule_cntr c ll -> exists ga th a b, 
                                        ga ~p a :: th 
                                     /\ c = (ga |-- b)
                                     /\ ll = ( (a :: a :: th |-- b) :: nil ).
  Proof.
    induction 1 as [ ga th a b H1 ].
    exists ga, th, a, b; auto.
  Qed.
  
  Definition rule_cntr_inst := { c : list Form * list Form * Form * Form 
                                   | match c with (((ga,th),a),_) => ga ~p a::th end }%type.
                                   
  Definition rule_cntr_map : rule_cntr_inst -> Seq * list Seq.
  Proof.
    intros ( (((ga,th),a),b) & _ ).
    exact (ga |-- b, (a :: a :: th |-- b) :: nil ).
  Defined.
  
  Fact rule_cntr_map_prop : soundly_represents rule_cntr rule_cntr_map. 
  Proof. intros ( (((ga,th),a),b) & ? ); simpl; constructor; auto. Qed.
  
  (* We do not need the finiteness of the contraction rule but it is
     used to show reification and decidability *)
  
  Fact rule_cntr_finite : finitely_represents rule_cntr rule_cntr_map. 
  Proof.
    intros (ga,b).
    generalize (pick_finite_t ga); intros (l1 & Hl1).
    set (ll := map (fun d : Form * list Form => let (a,th) := d in (((ga,th),a),b)) l1).
    assert (forall u, In u ll -> match u with (((ga,th),a),b) => ga ~p a::th end) as Hll.
      intros (((ga',th),a),b'); unfold ll; rewrite in_map_iff.
      intros ((a',th') & H1 & H2).
      inversion H1; subst ga' th' a' b'.
      apply Hl1 in H2; auto.
      
    exists (list_Forall_sig _ _ Hll).
    intros h; split.
    
    intros H.
    apply rule_cntr_inv in H.
    destruct H as (ga' & th & a & b' & H1 & E & H2).
    inversion E; subst ga' b' h.
    assert (In (((ga,th),a),b) ll) as H3.
      unfold ll; apply in_map_iff.
      exists (a, th); split; simpl; auto.
      apply Hl1; auto.
    generalize (list_Forall_sig_In_refl _ _ Hll _ H3).
    intros H4.
    match goal with [ H : In ?x (list_Forall_sig _ _ _) |- _ ] => exists x end; split; auto.
    
    intros (((((ga',th),a),b') & H) & H1 & _).
    simpl in H1.
    inversion H1; subst ga' b' h.
    constructor; auto.
  Qed.
  
  Hint Resolve rule_cntr_map_prop rule_cntr_finite : core.
  
  Fact rule_cntr_reif c hs : rule_cntr c hs -> { i | rule_cntr_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := rule_cntr); auto. Qed.
  
  Fact rule_cntr_dec c hs : { rule_cntr c hs } + { ~ rule_cntr c hs }.
  Proof. apply rule_dec with (f := rule_cntr_map); auto. Qed.
  
  Fact rule_cntr_finite_t c : finite_t (rule_cntr c).
  Proof. apply rule_finite_t with (f := rule_cntr_map); auto. Qed.
  
End Contraction_rule.

Section Weakening_rule.
  
  (** Contraction rule for R sequent systems 
  
                ga |- B
           -------------- [w]
              A,ga |- B
  
  *)
  
  Inductive rule_weak : Seq -> list Seq -> Prop :=
    | in_rule_weak : forall ga th a b, ga ~p a :: th
                                  -> rule_weak (ga |-- b) ( (th |-- b) :: nil ).
                                 
  Fact rule_weak_inv c ll : rule_weak c ll -> exists ga th a b, 
                                        ga ~p a :: th 
                                     /\ c = (ga |-- b)
                                     /\ ll = ( (th |-- b) :: nil ).
  Proof.
    induction 1 as [ ga th a b H1 ].
    exists ga, th, a, b; auto.
  Qed.
  
  Definition rule_weak_inst := { c : list Form * list Form * Form * Form 
                                   | match c with (((ga,th),a),_) => ga ~p a::th end }%type.
                                   
  Definition rule_weak_map : rule_weak_inst -> Seq * list Seq.
  Proof.
    intros ( (((ga,th),a),b) & _ ).
    exact (ga |-- b, (th |-- b) :: nil ).
  Defined.
  
  Fact rule_weak_map_prop : soundly_represents rule_weak rule_weak_map. 
  Proof. intros ( (((ga,th),a),b) & ? ); simpl; constructor 1 with a; auto. Qed.
  
  Fact rule_weak_finite : finitely_represents rule_weak rule_weak_map. 
  Proof.
    intros (ga,b).
    generalize (pick_finite_t ga); intros (l1 & Hl1).
    set (ll := map (fun d : Form * list Form => let (a,th) := d in (((ga,th),a),b)) l1).
    assert (forall u, In u ll -> match u with (((ga,th),a),b) => ga ~p a::th end) as Hll.
      intros (((ga',th),a),b'); unfold ll; rewrite in_map_iff.
      intros ((a',th') & H1 & H2).
      inversion H1; subst ga' th' a' b'.
      apply Hl1 in H2; auto.
      
    exists (list_Forall_sig _ _ Hll).
    intros h; split.
    
    intros H.
    apply rule_weak_inv in H.
    destruct H as (ga' & th & a & b' & H1 & E & H2).
    inversion E; subst ga' b' h.
    assert (In (((ga,th),a),b) ll) as H3.
      unfold ll; apply in_map_iff.
      exists (a, th); split; simpl; auto.
      apply Hl1; auto.
    generalize (list_Forall_sig_In_refl _ _ Hll _ H3).
    intros H4.
    match goal with [ H : In ?x (list_Forall_sig _ _ _) |- _ ] => exists x end; split; auto.
    
    intros (((((ga',th),a),b') & H) & H1 & _).
    simpl in H1.
    inversion H1; subst ga' b' h.
    constructor 1 with a; auto.
  Qed.
  
  Hint Resolve rule_weak_map_prop rule_weak_finite : core.
  
  Fact rule_weak_reif c hs : rule_weak c hs -> { i | rule_weak_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := rule_weak); auto. Qed.
  
  Fact rule_weak_dec c hs : { rule_weak c hs } + { ~ rule_weak c hs }.
  Proof. apply rule_dec with (f := rule_weak_map); auto. Qed.
  
  Fact rule_weak_finite_t c : finite_t (rule_weak c).
  Proof. apply rule_finite_t with (f := rule_weak_map); auto. Qed.
  
End Weakening_rule.

Section Cut_rule.
  
  (** Cut rule for R sequent systems 
  
           ga |- A   A,de |- B
         ----------------------- [cut]
                ga,de |- B
  
  *)

  Inductive rule_cut : Seq -> list Seq -> Prop :=
    | in_rule_cut : forall ga de th a b,    th ~p ga ++ de
                                       -> rule_cut (th |-- b)
                                            ( (ga |-- a) :: (a::de |-- b) :: nil ).
                                            
  Fact rule_cut_inv c ll : rule_cut c ll -> exists ga de th a b,
                                            th ~p ga ++ de
                                         /\ c = (th |-- b)
                                         /\ ll = (ga |-- a) :: (a::de |-- b) :: nil.
  Proof.
    induction 1 as [ ga de th a b ].
    exists ga, de, th, a, b; auto.
  Qed.
  
  (** There is no finiteness result for the cut rule because 
     it has an infinite number of instance for a given conclusion
     (there is *free* choice for A)
     
  *)
  
  Definition rule_cut_inst := { c : list Form * list Form * list Form * Form * Form 
                                   | match c with ((((ga,de),th),a),_) => th ~p ga++de end }%type.
  
  Definition rule_cut_map : rule_cut_inst -> Seq * list Seq.
  Proof.
    intros (((((ga,de),th),a),b) & _).
    split.
    exact (th |-- b).
    exact ((ga |-- a) :: (a::de |-- b) :: nil).
  Defined.
  
  Fact rule_cut_map_prop : soundly_represents rule_cut rule_cut_map. 
  Proof. intros (((((ga,de),th),a),b) & H); simpl; constructor; auto. Qed.
  
  Fact rule_cut_reif c hs : rule_cut c hs -> { i | rule_cut_map i = (c,hs) }.
  Proof.
    intros H.
    destruct c as (th,b).
    destruct hs as [ | (ga,a) [ | ([ | a' de ],c) [ | y hs ] ]]; try (exfalso; inversion H; fail).
    assert (th ~p ga ++ de /\ a = a' /\ b = c) as E.
      apply rule_cut_inv in H.
      destruct H as (ga' & de' & th' & a'' & b' & ? & E1 & E2).
      inversion E1; inversion E2; subst; auto.
    destruct E as (E & ? & ?); subst a' c.
    exists (exist _ ((((ga,de),th),a),b) E); simpl; auto.
  Qed.
  
  Fact rule_cut_dec c hs : { rule_cut c hs } + { ~ rule_cut c hs }.
  Proof.
    destruct c as (th,b).
    destruct hs as [ | (ga,a) [ | ([ | a' de ],c) [ | y hs ] ]]; 
      try (right; inversion 1; fail).
    destruct (Form_eq_dec a a') as [ | C ].
    2: right; contradict C; inversion C; auto.
    subst a'. 
    destruct (Form_eq_dec b c) as  [ | C ].
    2: right; contradict C; inversion C; auto.
    subst c.
    destruct (Permutation_dec Form_eq_dec th (ga++de)) as [ H | C ].
    2: right; contradict C; inversion C; auto.
    left; constructor 1 with (1 := H).
  Qed.
  
End Cut_rule.

Local Notation LR2c := (@LR2c _ Form_eq_dec).

Section Left_implication_rule_LR2.
  
  (** Left implication rule for LR2 with implicit but strictly
      controlled contraction 
  
             ga |- A     B,de |- C
           ------------------------- [l]
                     th |- C
                     
      where th is a contraction of A%>B,ga,de but not ANY
      contraction. Contractions are tightly controlled in
      this rule.
     
  *)
  
  Inductive LR2_rule_l : Seq -> list Seq -> Prop :=
    | in_LR2_l : forall ga de th th' a b x, 
                                 th ~p (a %> b) :: th'
                              -> LR2c (a %> b) ga de th'
                              -> LR2_rule_l (th |-- x)
                                        ( (ga |-- a) :: (b::de |-- x) :: nil ).
                                       
  Fact LR2_rule_l_inv c ll : LR2_rule_l c ll -> exists ga de th th' a b x,
                                                th ~p (a %> b) :: th'
                                             /\ LR2c (a %> b) ga de th'
                                             /\ c = (th |-- x)
                                             /\ ll = (ga |-- a) :: (b::de |-- x) :: nil.
  Proof.
    induction 1 as [ ga de th th' a b x H1 H2 ].
    exists ga, de, th, th', a, b, x; auto.
  Qed.
  
  Fact sf_LR2_rule_l c ll : LR2_rule_l c ll -> Forall (sf c) ll.
  Proof.
    induction 1 as [ ga de th th' a b x H2 H3 ].
    constructor; [ | constructor; [ | constructor ] ].
    + intros u [ (y & H4 & H5) | Hy ].
      apply LR2c_prop1 with (1 := H3) in H4.
      destruct H4 as [ H4 | H4 ].
      subst y.
      left; exists (a %> b); split; auto.
      apply Permutation_in with (1 := Permutation_sym H2).
      left; auto.
      left; exists y; split; auto.
      apply Permutation_in with (1 := Permutation_sym H2).
      simpl; auto.
      left; exists (a %> b); split.
      apply Permutation_in with (1 := Permutation_sym H2).
      left; auto.
      right; tauto.
    + intros u [ (y & H4 & H5) | Hy ].
      destruct H4 as [ ? | H4 ].
      subst y.
      left; exists (a %> b); split.
      apply Permutation_in with (1 := Permutation_sym H2).
      left; auto.
      right; tauto.
      apply LR2c_prop2 with (1 := H3) in H4.
      destruct H4 as [ H4 | H4 ].
      subst y.
      left; exists (a %> b); split; auto.
      apply Permutation_in with (1 := Permutation_sym H2).
      left; auto.
      left; exists y; split; auto.
      apply Permutation_in with (1 := Permutation_sym H2).
      simpl; auto.
      right; auto.
  Qed.
  
  Definition LR2_rule_l_inst := { c : list Form * list Form * list Form * list Form * Form * Form * Form 
                                    | match c with ((((((ga,de),th), th'),a),b),x) 
                                                 => th ~p (a %> b) :: th'
                                                 /\ LR2c (a %> b) ga de th' 
                                      end }%type.
  
  Definition LR2_rule_l_map : LR2_rule_l_inst -> Seq * list Seq.
  Proof.
    intros ( ((((((ga,de),th),th'),a),b),x) & _ ).
    exact (th |-- x , ( (ga |-- a) :: (b :: de |-- x) :: nil ) ).
  Defined.
  
  Fact LR2_rule_l_map_prop : soundly_represents LR2_rule_l LR2_rule_l_map.
  Proof.
    intros ( ((((((ga,de),th),th'),a),b),x) & H1 & H2 ); simpl. 
    constructor 1 with th'; auto.
  Qed.
  
  Fact LR2_rule_l_finite : finitely_represents LR2_rule_l LR2_rule_l_map.
  Proof.
    intros (th,x).
    generalize (pick_finite_t th); intros (l1 & Hl1).
    set (ll := flat_map (fun u => match u with 
                          | (a %> b,th') => let mm := proj1_sig (LR2c_finite_t Form_eq_dec (a %> b) th')
                                            in map (fun d : _ * _=> let (ga,de) := d in ((((((ga,de),th),th'),a),b),x)) mm
                          | _ => nil
                        end) l1).
    assert (forall u, In u ll -> match u with ((((((ga,de),th),th'),a),b),x) 
                                           => th ~p (a %> b) :: th'
                                           /\ LR2c (a %> b) ga de th' 
                                 end) as Hll.
    { intros ((((((ga,de),th'),th''),a),b),x'); unfold ll; rewrite in_flat_map.
      intros (([ | [] a' b' ],p) & H1 & H2); simpl in *; try tauto.
      apply in_map_iff in H2.
      destruct H2 as ((ga',de') & E & H3).
      inversion E; subst ga' de' th' th'' a' b' x'.
      apply (proj2_sig (LR2c_finite_t Form_eq_dec (a %> b) p)) in H3.
      apply Hl1 in H1.
      split; auto. }
    exists (list_Forall_sig _ _ Hll).
    intros h; split.
    + intros H.
      apply LR2_rule_l_inv in H.
      destruct H as (ga & de & th' & th'' & a & b & x' & H0 & H1 & E & H2).
      inversion E; subst th' x' h.
      assert (In ((((((ga,de),th),th''),a),b),x) ll) as H3.
        unfold ll; apply in_flat_map.
      exists (a %> b, th''); split; simpl; auto.
      apply Hl1; auto.
      apply in_map_iff.
      exists (ga, de); split; auto.
      apply (proj2_sig (LR2c_finite_t Form_eq_dec (a %> b) th'')).
      revert H1; apply LR2c_perm_3; auto.
      generalize (list_Forall_sig_In_refl _ _ Hll _ H3).
      intros H4.
      match goal with [ H : In ?x _ |- _ ] => exists x end; split; auto.
    + intros ((((((((ga,de),th'),th''),a),b),x') & H2 & H3) & H1 & _).
      simpl in H1.
      inversion H1; subst th' x' h.
      constructor 1 with th''; auto.
  Qed.
  
  Hint Resolve LR2_rule_l_map_prop LR2_rule_l_finite : core.
 
  Fact LR2_rule_l_reif c hs : LR2_rule_l c hs -> { i | LR2_rule_l_map i = (c,hs) }.
  Proof. intros ?; apply rule_reif with (r := LR2_rule_l); auto. Qed.
  
  Fact LR2_rule_l_dec c hs : { LR2_rule_l c hs } + { ~ LR2_rule_l c hs }.
  Proof. apply rule_dec with (f := LR2_rule_l_map); auto. Qed.
  
  Fact LR2_rule_l_finite_t c : finite_t (LR2_rule_l c).
  Proof. apply rule_finite_t with (f := LR2_rule_l_map); auto. Qed.
  
End Left_implication_rule_LR2.

Section Usable_rules.
  
  (* Now some more usable forms of LR{1,2} rules *)

  Implicit Type rules : Seq -> list Seq -> Prop.

  Fact rules_id rules : 
         rule_id inc2 rules
      -> forall a n, bproof rules (S n) (a::nil |-- a) (in_tree (a::nil |-- a) nil).
  Proof.
    intros H a n.
    rewrite bproof_S; repeat split.
    apply H.
    constructor.
    constructor.
  Qed.
  
  Fact rules_ax rules : 
         rule_ax inc2 rules
      -> forall l a r n, bproof rules (S n) (l++a::r |-- a) (in_tree (l++a::r |-- a) nil).
  Proof.
    intros H l a r n.
    rewrite bproof_S; repeat split.
    apply H.
    constructor.
    constructor.
  Qed.
  
  Fact LR_rules_imp_r rules :
         LR_rule_r inc2 rules
      -> forall n ga a b t,  
               bproof rules n (a::ga |-- b) t 
            -> bproof rules (S n) (ga |-- a %> b) (in_tree (ga |-- a %> b) (t::nil)).
  Proof.
    intros H n ga a b t H2.
    rewrite bproof_S; repeat split.
    apply H.
    unfold proof_sub; simpl.
    destruct H2 as ((H2 & H3) & H4).
    rewrite H3.
    constructor; auto.
    constructor.
    revert H2; apply bproof_root.
    constructor.
  Qed.

  Fact LR_rules_disj_r rules :
         LR_disj_r inc2 rules
      -> forall n (s : bool) ga a b t,  
               bproof rules n (ga |-- if s then a else b) t 
            -> bproof rules (S n) (ga |-- a ∨ b) (in_tree (ga |-- a ∨ b) (t::nil)).
  Proof.
    intros H n s ga a b t H2.
    rewrite bproof_S; repeat split.
    apply H.
    unfold proof_sub; simpl.
    destruct H2 as ((H2 & H3) & H4).
    rewrite H3.
    constructor; auto.
    constructor.
    revert H2; apply bproof_root.
    constructor.
  Qed.
  
  Fact LR_rules_imp_l rules :
         LR_rule_l inc2 rules
      -> forall n ga de th a b x ta tx, 
                                 th ~p (a %> b) :: ga ++ de
                              -> bproof rules n (ga     |-- a) ta
                              -> bproof rules n (b::de  |-- x) tx
                              -> bproof rules (S n) (th |-- x) (in_tree (th |-- x) (ta::tx::nil)).
  Proof.
    intros H0 n ga de th a b x ta tx H1 H3 H4.
    rewrite bproof_S; repeat split.
    unfold proof_sub; simpl.
    apply H0.
    destruct H3 as ((_ & H3) & _); rewrite H3.
    destruct H4 as ((_ & H4) & _); rewrite H4.
    apply in_LR_l with (1 := H1); auto.
    constructor.
    revert H3; apply bproof_root.
    constructor.
    revert H4; apply bproof_root.
    constructor.
  Qed.

  Fact LR_rules_disj_l rules :
         LR_disj_l inc2 rules
      -> forall n ga th a b x ta tx, 
                                 th ~p (a∨b) :: ga
                              -> bproof rules n (a::ga  |-- x) ta
                              -> bproof rules n (b::ga  |-- x) tx
                              -> bproof rules (S n) (th |-- x) (in_tree (th |-- x) (ta::tx::nil)).
  Proof.
    intros H0 n ga th a b x ta tx H1 H3 H4.
    rewrite bproof_S; repeat split.
    unfold proof_sub; simpl.
    apply H0.
    destruct H3 as ((_ & H3) & _); rewrite H3.
    destruct H4 as ((_ & H4) & _); rewrite H4.
    apply in_LR_disj_l with (1 := H1); auto.
    constructor.
    revert H3; apply bproof_root.
    constructor.
    revert H4; apply bproof_root.
    constructor.
  Qed.
  
  Fact LI2_rules_imp_l rules :
         LI2_rule_l inc2 rules
      -> forall n ga th a b x ta tx, 
                                 th ~p (a %> b) :: ga
                              -> bproof rules n (a %> b :: ga |-- a) ta
                              -> bproof rules n (a %> b :: b::ga  |-- x) tx
                              -> bproof rules (S n) (th |-- x) (in_tree (th |-- x) (ta::tx::nil)).
  Proof.
    intros H0 n ga th a b x ta tx H1 H3 H4.
    rewrite bproof_S; repeat split.
    unfold proof_sub; simpl.
    apply H0.
    destruct H3 as ((_ & H3) & _); rewrite H3.
    destruct H4 as ((_ & H4) & _); rewrite H4.
    apply in_LI2_l with (1 := H1); auto.
    constructor.
    revert H3; apply bproof_root.
    constructor.
    revert H4; apply bproof_root.
    constructor.
  Qed.
  
  Fact LR2_rules_imp_l rules :
       LR2_rule_l inc2 rules
    -> forall n ga de th th' a b x tg td, 
                                 th ~p (a %> b) :: th'
                              -> LR2c (a %> b) ga de th'
                              -> bproof rules n (ga     |-- a) tg
                              -> bproof rules n (b::de  |-- x) td
                              -> bproof rules (S n) (th |-- x) (in_tree (th |-- x) (tg::td::nil)).
  Proof.
    intros H0 n ga de th th' a b x ta td H1 H2 H3 H4.
    rewrite bproof_S; repeat split.
    unfold proof_sub; simpl.
    apply H0.
    destruct H3 as ((_ & H3) & _); rewrite H3.
    destruct H4 as ((_ & H4) & _); rewrite H4.
    apply in_LR2_l with (1 := H1); auto.
    constructor.
    revert H3; apply bproof_root.
    constructor.
    revert H4; apply bproof_root.
    constructor.
  Qed.
  
  Fact rules_cntr rules :
         rule_cntr inc2 rules
      -> forall n ga th x a t,
         ga ~p x :: th
      -> bproof rules n (x::x::th |-- a) t
      -> bproof rules (S n) (ga |-- a) (in_tree (ga |-- a) (t::nil)).
  Proof.
    intros H0 n ga th x a t H2 H3.
    rewrite bproof_S; repeat split.
    unfold proof_sub; simpl.
    apply H0.
    destruct H3 as ((_ & H3) & _); rewrite H3.
    apply in_rule_cntr; auto.
    constructor.
    revert H3; apply bproof_root.
    constructor.
  Qed.
  
  Fact rules_weak rules :
         rule_weak inc2 rules
      -> forall n ga th x a t,
         ga ~p x :: th
      -> bproof rules n (th |-- a) t
      -> bproof rules (S n) (ga |-- a) (in_tree (ga |-- a) (t::nil)).
  Proof.
    intros H0 n ga th x a t H2 H3.
    rewrite bproof_S; repeat split.
    unfold proof_sub; simpl.
    apply H0.
    destruct H3 as ((_ & H3) & _); rewrite H3.
    apply in_rule_weak with x; auto.
    constructor.
    revert H3; apply bproof_root.
    constructor.
  Qed.
  
  Fact rules_cut rules :
         rule_cut inc2 rules
      -> forall n ga de th a b ta tb,
         th ~p ga ++ de
      -> bproof rules n (ga |-- a) ta
      -> bproof rules n (a::de |-- b) tb
      -> bproof rules (S n) (th |-- b) (in_tree (th |-- b) (ta::tb::nil)).
  Proof.
    intros H0 n ga de th a b ta tb H1 H2 H3.
    rewrite bproof_S; repeat split.
    unfold proof_sub; simpl.
    apply H0.
    destruct H2 as ((_ & H2) & _); rewrite H2.
    destruct H3 as ((_ & H3) & _); rewrite H3.
    apply in_rule_cut; auto.
    constructor.
    revert H2; apply bproof_root.
    constructor.
    revert H3; apply bproof_root.
    constructor.
  Qed.
  
End Usable_rules.
