(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Max Omega List Relations Wellfounded.

Require Import tacs acc_utils rel_utils list_utils finite good_base.

Set Implicit Arguments.

Section trees.

  Variable (X : Type).

  (* we do not want the too weak Coq generated induction principles *)

  Unset Elimination Schemes.

  Inductive tree : Type := in_tree : X -> list tree -> tree.

  Set Elimination Schemes.

  Definition tree_root t := match t with in_tree x _ => x end.
  Definition tree_sons t := match t with in_tree _ l => l end.

  Fact tree_root_sons_eq t : t = in_tree (tree_root t) (tree_sons t).
  Proof. destruct t; auto. Qed.
  
  (* the immediate subtree relation *)
  
  Definition imsub_tree s t := match t with in_tree _ ll => In s ll end.
  
  Infix "<ist" := imsub_tree (at level 70).
  
  Fact imsub_tree_fix s t : s <ist t <-> exists x ll, In s ll /\ t = in_tree x ll.
  Proof.
    split.
    destruct t as [ x ll ]; exists x, ll; auto.
    intros (x & ll & H1 & ?); subst; auto.
  Qed.
  
  (* The immediate subtree relation is well founded *)
  
  Lemma imsub_tree_wf : well_founded imsub_tree.
  Proof.
    refine (fix loop t :=
      match t with
        | in_tree x ll => Acc_intro _ _
      end); simpl; clear x t.
    induction ll as [ | x ll IH ].
    intros _ [].
    intros ? [ [] | ].
    apply loop.
    apply IH; auto.
  Qed.

  (* let us define our own induction principles *)

  Section tree_rect.

    Variable P : tree -> Type.
    Hypothesis f : forall a ll, (forall x, In x ll -> P x) -> P (in_tree a ll).

    Let f' : forall t, (forall x, x <ist t -> P x) -> P t.
    Proof.
      intros []; apply f.
    Defined.

    Definition tree_rect t : P t.
    Proof.
      apply Fix with (1 := imsub_tree_wf), f'.
    Defined.

    Section tree_rect_fix.
    
      Variable E : forall t, P t -> P t -> Prop.

      Hypothesis f_ext : forall a ll f1 f2, (forall x Hx, E (f1 x Hx) (f2 x Hx)) -> E (f a ll f1) (f a ll f2).

      Fact tree_rect_fix a ll : E (tree_rect (in_tree a ll)) (f a ll (fun t _ => tree_rect t)).
      Proof.
        unfold tree_rect, Fix.
        rewrite <- Fix_F_eq; unfold f'.
        apply f_ext; intros; apply Fix_F_ext.
        intros [] ? ?; apply f_ext.
      Qed.
      
    End tree_rect_fix.
    
    Section tree_rect_fix_eq.

      Hypothesis f_ext : forall a ll f1 f2, (forall x Hx, f1 x Hx = f2 x Hx) -> f a ll f1 = f a ll f2.
      
      (* Coq recursive type-checking does not allow such a definition 
         but it is possible to prove this identity
      *)
      
      Fact tree_rect_fix_eq a ll : tree_rect (in_tree a ll) = f a ll (fun t _ => tree_rect t).
      Proof.
        apply tree_rect_fix with (E := fun _ => @eq _); simpl; auto.
      Qed.
      
    End tree_rect_fix_eq.

  End tree_rect.
  
  Definition tree_rec (P : tree -> Set)  := tree_rect P.
  Definition tree_ind (P : tree -> Prop) := tree_rect P.

  Section tree_recursion.

    (* the particular case when the output type does not depend on the tree *)

    Variables (Y : Type) (f : X -> list tree -> list Y -> Y).    
  
    Definition tree_recursion : tree -> Y.
    Proof.
      apply tree_rect.
      intros x ll IH.
      apply (f x ll (list_In_map _ IH)).
    Defined.
    
    (* In that case, extensionnality is for free *)

    Fact tree_recursion_fix x ll : tree_recursion (in_tree x ll) = f x ll (map tree_recursion ll).
    Proof.
      unfold tree_recursion at 1.
      rewrite tree_rect_fix with (E := fun _ => eq).
      f_equal; apply list_In_map_eq_map.
      clear x ll; intros x ll g h H; simpl.
      f_equal; apply list_In_map_ext, H.
    Qed.
  
  End tree_recursion.

  Section tree_eq_dec.

    Hypothesis eqX_dec : forall x y : X, { x = y } + { x <> y }.
    
    Theorem tree_eq_dec (t1 t2 : tree) : { t1 = t2 } + { t1 <> t2 }.
    Proof.
      revert t2; induction t1 as [ x ll IH ]; intros [ y mm ].
      destruct (eqX_dec x y) as [ H1 | H1 ].
      destruct (@list_eq_dec _ ll mm) as [ | C ].
      intros; apply IH; auto.
      subst; left; auto.
      right; contradict C; injection C; auto.
      right; contradict H1; injection H1; auto.
    Qed.

  End tree_eq_dec.

  Definition tree_size : tree -> nat.
  Proof.
    induction 1 as [ _ _ ll ] using tree_recursion.
    apply (S (lsum ll)).
  Defined.

  Fact tree_size_fix x ll : tree_size (in_tree x ll) = S (lsum (map tree_size ll)).
  Proof.
    apply tree_recursion_fix.
  Qed.

  Definition tree_ht : tree -> nat.
  Proof.
    induction 1 as [ _ _ IH ] using tree_recursion.
    apply (S (lmax IH)).
  Defined.
  
  Fact tree_ht_fix x ll : tree_ht (in_tree x ll) = S (lmax (map tree_ht ll)).
  Proof.
    apply tree_recursion_fix.
  Qed.
  
  Fact tree_ht_0 t : 0 < tree_ht t.
  Proof.
    destruct t; rewrite tree_ht_fix; omega.
  Qed.
  
  Definition tree_sum_ht : tree -> nat.
  Proof.
    induction 1 as [ x ll IH ] using tree_recursion.
    apply (tree_ht (in_tree x ll) + lsum IH).
  Defined.
  
  Fact tree_sum_ht_fix x ll : tree_sum_ht (in_tree x ll)
                            = tree_ht (in_tree x ll)
                            + lsum (map tree_sum_ht ll).
  Proof.
    apply tree_recursion_fix.
  Qed.
  
  Fact tree_ht_find x ll : ll <> nil -> { t | In t ll /\ tree_ht (in_tree x ll) = S (tree_ht t) }.
  Proof.
    intros H.
    destruct (lmax_map_inv tree_ht H) as (t & H1 & H2).
    exists t; rewrite tree_ht_fix, H2; auto.
  Qed.

  (* this is the subtree relation, aka inclusion *)   

  Reserved Notation "x '<st' y" (at level 70, no associativity).

  Inductive sub_tree : tree -> tree -> Prop :=
    | in_subtree_0 : forall t, t <st t
    | in_subtree_1 : forall s t x ll, In t ll -> s <st t -> s <st in_tree x ll 
  where "x <st y" := (sub_tree x y).

  Fact sub_tree_ht s t : s <st t -> tree_ht s <= tree_ht t.
  Proof.
    induction 1 as [ | s t x ll H1 H2 H3 ]; auto.
    rewrite tree_ht_fix.
    apply le_trans with (1 := H3).
    apply le_trans with (2 := le_n_Sn _).
    apply lmax_In.
    apply in_map_iff.
    exists t; auto.
  Qed.    

  (* this is the strict subtree relation *)

  Reserved Notation "x '<<st' y" (at level 70, no associativity).

  Inductive ssub_tree : tree -> tree -> Prop :=
    | in_ssubtree_0 : forall s   x ll, In s ll -> s <<st in_tree x ll
    | in_ssubtree_1 : forall s t x ll, In t ll -> s <<st t -> s <<st in_tree x ll 
  where "x <<st y" := (ssub_tree x y).

  Fact in_subtree_0' s t : s = t -> s <st t.
  Proof. intro; subst; constructor. Qed.
  
  Fact imsub_ssub_tree s t : s <ist t -> s <<st t.
  Proof.
    rewrite imsub_tree_fix.
    intros (x & ll & H1 & H2); subst.
    constructor 1; auto.
  Qed.
  
  Fact ssub_sub_tree s t : s <<st t -> s <st t.
  Proof.
    induction 1 as [ s | s t ].
    constructor 2 with s; auto.
    constructor 1.
    constructor 2 with t; auto.
  Qed.
  
  Fact ssub_tree_trans r s t : r <<st s -> s <<st t -> r <<st t.
  Proof.
    intro; induction 1 as [ s | ? t ]; auto.
    constructor 2 with s; auto.
    constructor 2 with t; auto.
  Qed.

  Fact ssub_imsub_tree : ssub_tree ~eq2 clos_trans _ imsub_tree.
  Proof.
    split; intros s t.

    induction 1 as [ s x ll | s t x ll H1 H2 H3 ].
    constructor 1; auto.
    constructor 2 with (1 := H3).
    constructor 1; auto.
    
    induction 1 as [ | ? s ].
    apply imsub_ssub_tree; auto.
    apply ssub_tree_trans with s; auto.
  Qed.
  
  Fact ssub_tree_wf : well_founded ssub_tree.
  Proof.
    generalize imsub_tree_wf; intros H.
    apply wf_clos_trans in H.
    revert H; apply wf_incl.
    intros ? ?; apply ssub_imsub_tree.
  Qed.

  Fact sub_tree_refl s : s <st s.
  Proof.
    constructor 1.
  Qed.

  Fact sub_tree_trans r s t : r <st s -> s <st t -> r <st t.
  Proof.
    intro; induction 1 as [ | ? t ]; auto.
    constructor 2 with t; auto.
  Qed.

  Fact ssub_tree_inv_left s t : s <<st t <-> exists s', s <ist s' /\ s' <st t.
  Proof.
    split.
    
    induction 1 as [ s x ll | s t x ll H1 H2 (s' & H3 & H4) ].
    exists (in_tree x ll); split; auto.
    constructor 1.
    exists s'; split; auto.
    constructor 2 with t; auto.
    
    intros (s' & H1 & H2).
    revert s H1.
    induction H2 as [ s' | s' t x ll H1 H2 H3 ].
    intro; apply imsub_ssub_tree.
    intros s Hs.
    constructor 2 with t; auto.
  Qed.

  Fact ssub_tree_inv_right s t : s <<st t <-> exists s', s <st s' /\ s' <ist t.
  Proof.
    split.

    intros H.
    apply ssub_imsub_tree in H.
    apply clos_trans_tn1_iff in H.
    induction H as [ | t u H1 H2 (s' & H3 & H4) ].
    exists s; split; auto; constructor.
    exists t; split; auto.
    apply sub_tree_trans with (1 := H3).
    apply ssub_sub_tree, imsub_ssub_tree, H4.
    
    destruct t as [ x ll ]; simpl.
    intros (s' & H1 & H2); subst.
    revert x ll H2.
    induction H1 as [ s | s t x ll H1 H2 IH ]; intros y ll' H3.
    constructor 1; auto.
    constructor 2 with (in_tree x ll); auto.
  Qed.
  
  Fact ssub_tree_inv s x ll : s <<st in_tree x ll <-> exists t, s <st t /\ In t ll.
  Proof.
    rewrite ssub_tree_inv_right; simpl; split; auto.
  Qed.

  Fact sub_ssub_tree_trans r s t : r <st s -> s <<st t -> r <<st t.
  Proof.
    intros H1 H2.
    rewrite ssub_tree_inv_right in H2.
    destruct H2 as (s' & H2 & H3).
    rewrite ssub_tree_inv_right.
    exists s'; split; auto.
    apply sub_tree_trans with (1 := H1); auto.
  Qed.
  
  Fact ssub_sub_tree_trans r s t : r <<st s -> s <st t -> r <<st t.
  Proof.
    intros H1 H2.
    rewrite ssub_tree_inv_left in H1.
    destruct H1 as (s' & H1 & H3).
    rewrite ssub_tree_inv_left.
    exists s'; split; auto.
    apply sub_tree_trans with (1 := H3); auto.
  Qed.

  Fact sub_tree_inv s t : s <st t <-> s = t \/ s <<st t.
  Proof.
    split.

    induction 1 as [ | s t x ll H1 H2 [ H3 | H3 ]]; subst; auto; right.
    constructor 1; auto.
    constructor 2 with t; auto.
    
    intros [ H | H ].
    subst; constructor.
    apply ssub_sub_tree; auto.
  Qed.

  Fact sub_in_tree_inv s x ll : s <st in_tree x ll -> s = in_tree x ll \/ exists t, s <st t /\ In t ll.
  Proof.
    intros H.
    apply sub_tree_inv in H.
    destruct H as [ H | H ]; auto; right.
    apply ssub_tree_inv_right in H; auto.
  Qed.

  Definition tree_leaf t : { x | in_tree x nil <st t }.
  Proof.
    induction t as [ x [ | t ll ] IH ] using tree_rect.
    
    exists x; constructor 1.
    destruct (IH t) as (y & Hy).
    left; auto.
    exists y; constructor 2 with t; simpl; auto.
  Qed.

  Section sub_trees.

    Definition sub_trees : tree -> list tree.
    Proof.
      induction 1 as [ a ll IH ] using tree_recursion.
      apply cons.
      apply (in_tree a ll).
      apply list_flatten, IH.
    Defined.

    Fact sub_trees_fix x ll : sub_trees (in_tree x ll) = in_tree x ll::list_flatten (map sub_trees ll).
    Proof.
      apply tree_recursion_fix.
    Qed.
    
    Fact sub_trees_sub_tree_eq t x : In x (sub_trees t) <-> x <st t.
    Proof.
      split.

      revert x.
      induction t as [ y ll IH ]; intros x Hx.
      rewrite sub_trees_fix in Hx.
      simpl In in Hx.
      destruct Hx as [ Hx | Hx ].
      subst x; constructor 1.
      rewrite list_flatten_spec in Hx.
      destruct Hx as (mm & H1 & H2).
      apply in_map_iff in H2.
      destruct H2 as (t & H2 & H3); subst mm.
      constructor 2 with t; auto.
      
      induction 1 as [ [ x ll ] | s t x ll H1 H2 H3 ]; rewrite sub_trees_fix.
      left; auto.
      right.
      apply list_flatten_spec.
      exists (sub_trees t); split; auto.
      apply in_map_iff.
      exists t; auto.
    Qed.

  End sub_trees.

  (* finite quantification over the nodes of trees *)

  Section tree_fall_exst.

    Variable P : X -> list tree -> Prop.

    Definition tree_fall (t : tree) : Prop.
    Proof.
      induction t as [ a ll IH ].
      exact (P a ll /\ forall x Hx, IH x Hx).
    Defined.

   (* this is how we would like tree_fall to be recursively defined but this would
       not be well-formed in Coq
    *)

    Fact tree_fall_fix x ll : tree_fall (in_tree x ll) <-> P x ll /\ forall t, In t ll -> tree_fall t. 
    Proof.
      unfold tree_fall at 1.
      rewrite tree_rect_fix 
        with (E := fun _ A B => A <-> B);
        firstorder.
    Qed.
 
    Section tree_fall_rect.
  
      Variable (Q : tree -> Type).
  
      Hypothesis HQ : forall x ll, tree_fall (in_tree x ll) -> (forall t, In t ll -> Q t) -> Q (in_tree x ll).
  
      Theorem tree_fall_rect t : tree_fall t -> Q t.
      Proof.
        induction t as [ x ll IH ]; intros H.
        apply HQ; auto.
        rewrite tree_fall_fix in H; destruct H; auto.
      Qed.

    End tree_fall_rect.
    
    Definition tree_fall_rec (Q : tree -> Set) := @tree_fall_rect Q.
    Definition tree_fall_ind (Q : tree -> Prop) := @tree_fall_rect Q.

    Fact tree_fall_sub_tree t : tree_fall t <-> forall x ll, in_tree x ll <st t -> P x ll.
    Proof.
      split.

      induction t as [ x ll IH ]; intros Ht.
      rewrite tree_fall_fix in Ht.
      destruct Ht as [ Hx Hll ].
      intros y mm H1.
      apply sub_in_tree_inv in H1.
      destruct H1 as [ H1 | (t & H1 & H2) ].
      injection H1; clear H1; intros; subst; auto.
      apply IH with t; auto.
      
      induction t as [ x ll IH ]; intros Ht.
      rewrite tree_fall_fix; split.
      apply Ht; constructor 1.
      intros u Hu; apply IH; auto.
      intros y mm Hmm; apply Ht.
      constructor 2 with u; auto.
    Qed.

    Definition tree_exst (t : tree) : Prop.
    Proof.
      induction t as [ a ll IH ].
      exact (P a ll \/ exists x Hx, IH x Hx).
    Defined.

    Let disj_eq_prop (A B B' : Prop) : (B <-> B') -> (A \/ B <-> A \/ B').
    Proof. tauto. Qed.

    Fact tree_exst_fix x ll : tree_exst (in_tree x ll) <-> P x ll \/ exists t, In t ll /\ tree_exst t. 
    Proof.
      unfold tree_exst at 1.
      rewrite tree_rect_fix 
        with (E := fun _ A B => A <-> B).
      apply disj_eq_prop.
      split; intros (y & ? & ?); exists y; split; auto.
      intros; apply disj_eq_prop.
      split; intros (y & Hy & ?); exists y, Hy; apply H; auto.
    Qed.

    Fact tree_exst_sub_tree t : tree_exst t <-> exists x ll, in_tree x ll <st t /\ P x ll.
    Proof.
      split.

      induction t as [ x ll IH ]; intros Ht.
      rewrite tree_exst_fix in Ht.
      destruct Ht as [ Ht | (t & H1 & H2) ].
      exists x, ll; split; auto; constructor.
      destruct (IH _ H1 H2) as (y & mm & H3 & H4).
      exists y, mm; split; auto.
      constructor 2 with t; auto.
      
      intros (x & ll & H1 & H2); revert x ll H1 H2.
      induction t as [ x ll IH ]; intros y mm H1 H2.
      rewrite tree_exst_fix.
      apply sub_in_tree_inv in H1.
      destruct H1 as [ H1 | (t & H1 & H3) ].
      left; injection H1; intros; subst; auto.
      right; exists t; split; auto.
      apply IH with (2 := H1); auto.
    Qed.

    Fact sub_tree_fall t1 t2 : t1 <st t2 -> tree_fall t2 -> tree_fall t1.
    Proof.
      induction 1; auto.
      rewrite tree_fall_fix.
      intros (? & ?); auto.
    Qed.

    Fact sub_tree_exst t1 t2 : t1 <st t2 -> tree_exst t1 -> tree_exst t2.
    Proof.
      induction 1 as [ | ? t ]; auto.
      rewrite tree_exst_fix.
      right; exists t; auto.
    Qed.

  End tree_fall_exst.

  Fact tree_fall_inc (P Q : _ -> _ -> Prop) : P inc2 Q -> tree_fall P inc1 tree_fall Q.
  Proof.
    intros H t; induction t as [ x ll IH ].
    repeat rewrite tree_fall_fix.
    intros []; split; auto.
  Qed.

  Fact tree_exst_inc (P Q : _ -> _ -> Prop) : P inc2 Q -> tree_exst P inc1 tree_exst Q.
  Proof.
    intros H t; induction t as [ x ll IH ].
    repeat rewrite tree_exst_fix.
    intros [| (t & ? & ?)]; [ left | right ]; auto; exists t; auto.
  Qed. 

  Section tree_fall_exst_dec.

    Variable (P Q : X -> list tree -> Prop).

    Hypothesis PQ_incomp : forall x ll, P x ll -> Q x ll -> False.
    
    Fact tree_fall_exst_incomp t : tree_fall P t -> tree_exst Q t -> False.
    Proof.
      induction t as [ x ll IH ].
      rewrite tree_fall_fix, tree_exst_fix.
      intros [ H1 H2 ] [ H3 | (t & H3 & H4) ].
      
      apply PQ_incomp with (1 := H1); auto.
      apply IH with (1 := H3); auto.
    Qed.      

    Hypothesis PQ_dec : forall x ll, { P x ll } + { Q x ll }.    
    
    Fact tree_fall_exst_dec t : { tree_fall P t } + { tree_exst Q t }.
    Proof.
      induction t as [ x ll IH ].
      destruct (list_choose_rec (tree_exst Q) (tree_fall P) ll) as [ (t & H1 & H2) | H1 ].
      intros z Hz; specialize (IH _ Hz); tauto.
      
      right.
      apply tree_exst_fix.
      right; exists t; auto.
      
      destruct (PQ_dec x ll) as [ | H2 ].
      
      left; apply tree_fall_fix; auto.
      
      right.
      apply tree_exst_fix.
      left; auto.
    Qed.
    
  End tree_fall_exst_dec.

  Section tree_fall_dec.
  
    Variable (P : X -> list tree -> Prop).

    Hypothesis PQ_dec : forall x ll, { P x ll } + { ~ P x ll }.
    
    Fact tree_fall_dec t : { tree_fall P t } + { ~ tree_fall P t }.
    Proof.
      destruct (tree_fall_exst_dec _ _ PQ_dec t) as [ | C ].
      tauto.
      right; intros H.
      apply tree_fall_exst_incomp with (2 := H) (3 := C).
      intros; tauto.
    Qed.
    
    Fact tree_exst_dec t : { tree_exst P t } + { ~ tree_exst P t }.
    Proof.
      destruct (tree_fall_exst_dec (fun x ll => ~ P x ll) P) with (t := t) as [ C | ].
      intros x ll; specialize (PQ_dec x ll); tauto.
      right; intros H.
      apply tree_fall_exst_incomp with (2 := C) (3 := H).
      intros; tauto.
      left; auto.
    Qed.

  End tree_fall_dec.

End trees.

Infix "<st" := (@sub_tree _) (at level 70, no associativity).
Infix "<<st" := (@ssub_tree _) (at level 70, no associativity).
Infix "<ist" := (@imsub_tree _) (at level 70, no associativity).
    
Section tree_branch.

  Variable X : Type.

  Inductive tree_branch : tree X -> list X -> Prop :=
    | in_tb0 : forall t, tree_branch t nil
    | in_tb1 : forall x, tree_branch (in_tree x nil) (x::nil)
    | in_tb2 : forall b x ll s, In s ll -> tree_branch s b -> tree_branch (in_tree x ll) (x::b).

  Fact tree_branch_inv t b : tree_branch t b 
                          -> b = nil
                          \/ tree_sons t = nil /\ b = tree_root t::nil
                          \/ exists b' x ll s,
                                t = in_tree x ll
                             /\ b = x::b'
                             /\ In s ll
                             /\ tree_branch s b'.
  Proof.
    intros [ | x | b' x ll s ]; auto.
    do 2 right; exists b', x, ll, s; auto.
  Qed.

  Fact tree_branch_cons_inv x ll y b : tree_branch (in_tree x ll) (y::b)
                                    -> x = y 
                                    /\  (ll = nil /\ b = nil 
                                      \/ exists s, In s ll /\ tree_branch s b).
  Proof.
    intros H.
    apply tree_branch_inv in H.
    destruct H as [ H | [ (H1 & H2) | (b' & z & m & s & H1 & H2 & H3 & H4) ] ].
    discriminate H.
    simpl in H1, H2.
    injection H2; clear H2; intros ? ?; subst y b ll; auto.
    injection H1; clear H1; intros ? ?; subst z m.
    injection H2; clear H2; intros ? ?; subst y b'.
    split; auto; right.
    exists s; auto.
  Qed.
  
  Definition tree_branch_list : tree X -> list (list X).
  Proof.
    apply tree_recursion.
    intros x [ | y ll ] lb.
    exact (nil::(x::nil)::nil).
    exact (nil::map (cons x) (concat lb)).
  Defined.
  
  Fact tree_branch_list_fix0 x : tree_branch_list (in_tree x nil) = nil::(x::nil)::nil.
  Proof.
    apply tree_recursion_fix.
  Qed.
  
  Fact tree_branch_list_fix1 x ll : ll <> nil -> tree_branch_list (in_tree x ll) = nil::map (cons x) (flat_map tree_branch_list ll).
  Proof.
    destruct ll as [ | y ll ].
    intros []; reflexivity.
    intros _.
    unfold tree_branch_list at 1.
    rewrite tree_recursion_fix.
    do 2 f_equal.
    symmetry; apply flat_map_concat_map.
  Qed.
  
  Fact tree_branch_list_nil t : In nil (tree_branch_list t).
  Proof.
    destruct t as [ x [ | y ll ] ].
    rewrite tree_branch_list_fix0; left; auto.
    rewrite tree_branch_list_fix1; try discriminate; left; auto.
  Qed.
  
  Fact tree_branch_list_eq t b : tree_branch t b <-> In b (tree_branch_list t).
  Proof.
    split.
    
    induction 1 as [ | x | b x ll s H1 H2 IH2 ].
    apply tree_branch_list_nil.
    rewrite tree_branch_list_fix0; right; left; auto.
    destruct ll.
    destruct H1.
    rewrite tree_branch_list_fix1; try discriminate.
    right; apply in_map_iff.
    exists b; split; auto.
    apply in_flat_map.
    exists s; auto.
    
    revert b; induction t as [ x [ | y ll ] IH ]; intros b.
    rewrite tree_branch_list_fix0.
    intros [ [] | [ [] | [] ] ].
    constructor 1.
    constructor 2.
    rewrite tree_branch_list_fix1; try discriminate.
    intros [ [] | H ].
    constructor 1.
    apply in_map_iff in H.
    destruct H as (b' & ? & H); subst b.
    apply in_flat_map in H.
    destruct H as (t & ? & ?).
    constructor 3 with t; auto.
  Qed.
  
  Fact tree_branch_finite_t t : finite_t (tree_branch t).
  Proof.
    exists (tree_branch_list t); symmetry; apply tree_branch_list_eq.
  Qed.

  Fact tree_branch_root t x l : tree_branch t (x::l) -> tree_root t = x.
  Proof.
    intros H.
    apply tree_branch_inv in H.
    destruct H as [ H | [ (H1 & H2) | (b & y & m & s & H1 & H2 & H3 & H4) ] ].
    discriminate H.
    injection H2; auto.
    subst t; simpl.
    injection H2; auto.
  Qed.
  
  (* Every branch is smaller than the height of the tree *)

  Fact tree_branch_length_ht t b : tree_branch t b -> length b <= tree_ht t.
  Proof.
    induction 1 as [ | x | b x ll s H1 H2 IH2 ].
    destruct t; rewrite tree_ht_fix; simpl; omega.
    rewrite tree_ht_fix; simpl; omega.
    rewrite tree_ht_fix; simpl; apply le_n_S.
    apply le_trans with (1 := IH2).
    apply lmax_In, in_map_iff.
    exists s; auto.
  Qed.
  
  (* and there is a computable branch which has exactly the height if the tree *)
  
  Fact tree_ht_branch t : { b | tree_branch t b /\ length b = tree_ht t }.
  Proof.
    induction t as [ x [ | y ll ] IH ].
    
    exists (x::nil); simpl; split; auto.
    constructor 2; auto.
    rewrite tree_ht_fix; auto.
    
    destruct (@tree_ht_find _ x (y::ll)) as (t & H1 & H2).
    discriminate.
    destruct (IH _ H1) as (b & H3 & H4).
    exists (x::b); split.
    constructor 3 with t; auto.
    rewrite H2; simpl; f_equal; auto.
  Qed.
  
  (* Hence n-bounded trees can be characterized by the length of their branches *)

  Fact branch_length_tree_ht t n : (forall b, tree_branch t b -> length b <= n) <-> tree_ht t <= n.
  Proof.
    split.
    intros H.
    destruct (tree_ht_branch t) as (b & H1 & H2).
    apply H in H1.
    rewrite <- H2; auto.
    intros H1 b H2.
    apply le_trans with (2 := H1).
    apply tree_branch_length_ht; auto.
  Qed.

  Fact tree_search t l m : tree_branch t (l++m) -> exists t', tree_branch t' m /\ t' <st t.
  Proof.
    revert t; induction l as [ | x l IH ]; intros t.
    exists t; split; auto; constructor 1.
    intros H; simpl in H.
    apply tree_branch_inv in H.
    destruct H as [ H | [ (H1 & H2) | (b & y & mm & s & H1 & H2 & H3 & H4) ] ].
    discriminate H.
    injection H2; clear H2; intros H2 H3.
    destruct l; try discriminate H2.
    destruct m; try discriminate H2.
    exists t; split.
    constructor 1.
    constructor 1.
    injection H2; clear H2; intros H2 ?; subst y b.
    apply IH in H4.
    destruct H4 as (t' & H4 & H5).
    exists t'; split; auto.
    subst t; constructor 2 with s; auto.
  Qed.
  
  Fact tree_split_search t l x r : 
       tree_branch t (l++x::r) -> 
            r = nil /\ in_tree x nil <st t
         \/ exists t' tx, tree_branch t' r /\ In t' tx /\ in_tree x tx <st t.
  Proof.
    intros Ht.
    apply tree_search in Ht.
    destruct Ht as ([ y tx ] & H1 & H2).
    apply tree_branch_cons_inv in H1.
    destruct H1 as (? & [ (H5 & H7) | (t' & H5 & H7) ]); subst y.
    left; subst; auto.
    right; exists t', tx; auto.
  Qed. 

  Definition bounded_tree n (t : tree X) := tree_ht t <= n.
  
  Fact bounded_tree_O : forall t, ~ bounded_tree 0 t.
  Proof.
    intros [ x ll ]; unfold bounded_tree; rewrite tree_ht_fix; omega.
  Qed.
  
  Fact bounded_tree_S n t : bounded_tree (S n) t <-> Forall (bounded_tree n) (tree_sons t).
  Proof.
    destruct t as [ x ll ]; simpl.
    unfold bounded_tree; rewrite tree_ht_fix.
    split.  
  
    intros H.
    apply le_S_n in H.
    induction ll as [ | y ll IH ]; simpl in H; constructor.
    apply le_trans with (2 := H), le_max_l.
    apply IH, le_trans with (2 := H), le_max_r.
    
    intros H; apply le_n_S.
    induction H as [ | y ll IH ]; simpl.
    omega.
    apply max_lub; auto.
  Qed.

End tree_branch.

Section tree_irredundant.

  Variables (X : Type) (R : X -> X -> Prop).
  
  Hypothesis Rdec : forall x y, { R x y } + { ~ R x y }.

  (* Irredundant tree : no branch is good for R *)
  
  Definition tree_irred t := forall b, tree_branch t b -> bad R (rev b).
  
  Definition tree_good_or_irred t : { b | tree_branch t b /\ good R (rev b) } + { tree_irred t }.
  Proof.
    destruct (finite_t_decide (fun l => bad R (rev l)) (fun l => good R (rev l)) (tree_branch_finite_t t)); auto.
    intros x _; destruct (good_bad_dec _ Rdec (rev x)); auto.
  Qed.
  
  Definition tree_irred_dec t : { tree_irred t } + { ~ tree_irred t }.
  Proof.
    destruct (tree_good_or_irred t) as [ (b & H1 & H2) | ]; auto.
    right; intros H.
    specialize (H _ H1).
    apply good_bad_False with (1 := H2); auto.
  Qed.

End tree_irredundant.


