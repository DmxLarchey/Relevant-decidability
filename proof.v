(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith Omega Max List.

Require Import tacs rel_utils list_utils tree.
Require Import finite minimizer almost_full koenig.

Set Implicit Arguments.

Section proofs.

  (** 1/ stm is a type of statements (typically sequents for
         sequent calculi or formulas for Hilbert style proof
         systems)
      2/ rules is a predicate relating a conclusion to a list
         of premises collecting all possible rule instances
         which are of the form
         
                     H1 ... Hn
                    -----------
                         C
                         
         C is the conclusion and H1 ... Hn are the premises
         
      3/ rules_fin states there is only a finite number of rule
         instances for a given conclusion, hence the proof search
         tree is finitely branching 
         
   *)

  Variable (stm : Type) 
           (rules : stm -> list stm -> Prop) 
           (rules_fin : forall x, finite_t (rules x)).
           
  (* proof trees are represented by trees of stm such that every node
     is an instance of some rule *)
     
  Definition proof_tree := tree_fall (fun x l => rules x (map (@tree_root _) l)).
  
  Fact proof_tree_fix x ll : 
         proof_tree (in_tree x ll) 
     <-> rules x (map (@tree_root _) ll) 
      /\ forall t, In t ll -> proof_tree t.
  Proof. apply tree_fall_fix. Qed.
  
  (* a proof of s is a proof tree with root s *) 
  
  Definition proof s t := proof_tree t /\ tree_root t = s.
  
  (* proof_sub t are the nodes which are the immediate
     successors of the root of t *)
  
  Definition proof_sub t := map (@tree_root stm) (tree_sons t).

  Section stm_dec.
  
    (* Small exercice, if equality is decidable between statements
       then being a proof is also decidable *)

    Hypothesis stm_eq_dec : forall a b : stm, { a = b } + { a <> b }.

    Let lstm_eq_dec (ll mm : list stm) : { ll = mm } + { ll <> mm }.
    Proof.
      apply list_eq_dec. 
      intros; apply stm_eq_dec.
    Qed.

    Fact rules_dec x ll : { rules x ll } + { ~ rules x ll }.
    Proof.
      destruct (rules_fin x) as (mm & Hmm).
      destruct (In_dec lstm_eq_dec ll mm) as [ H | H ]; [ left | right ];
      rewrite <- Hmm; auto.
    Qed.

    Fact ptree_dec t : { proof_tree t } + { ~ proof_tree t }.
    Proof.
      apply tree_fall_dec.
      intros x ll.
      destruct (rules_fin x) as (mm & Hmm).
      destruct (In_dec lstm_eq_dec (map (@tree_root _) ll) mm) as [ H | H ];
      rewrite Hmm in H; [ left | right ]; auto.
    Qed.
    
    Fact proof_dec x t : { proof x t } + { ~ proof x t }.
    Proof.
      unfold proof.
      destruct (ptree_dec t); 
      destruct (stm_eq_dec (tree_root t) x); 
      tauto.
    Qed.

  End stm_dec.
  
  (* In a proof tree, every subtree is a proof of its root *)

  Fact ptree_proof t : proof_tree t -> tree_fall (fun x ll => proof x (in_tree x ll)) t.
  Proof.
    induction 1 as [ x ll Hll IH ] using tree_fall_ind; auto.
    rewrite tree_fall_fix; split.
    split; auto.
    intros; auto.
  Qed.

  Fact proof_proof_sub x y ll : proof x (in_tree y ll) -> forall t, In t ll -> proof (tree_root t) t.
  Proof.
    unfold proof at 1.
    intros (H & _) t Ht.
    unfold proof.
    rewrite proof_tree_fix in H.
    apply proj2 in H.
    split; auto.
  Qed.
  
  (* bounded proof, p is a proof of x of height bounded by n *)
  
  Definition bproof n x p := proof x p /\ bounded_tree n p.
  
  Fact bproof_branch n x p : bproof n x p <-> proof x p /\ forall b, tree_branch p b -> length b <= n.
  Proof.
    rewrite branch_length_tree_ht.
    unfold bproof; tauto.
  Qed.
  
  Fact bproof_mono n m : n <= m -> bproof n inc2 bproof m.
  Proof.
    intros H x p (H1 & H2); split; auto.
    revert H2 H; unfold bounded_tree. 
    apply le_trans.
  Qed.
  
  Fact bproof_root n x t : bproof n x t -> bproof n (tree_root t) t.
  Proof.
    intros ((? & ?) & ?); repeat split; auto.
  Qed.
  
  (* bproof n is inductively characterized *)

  Fact bproof_O x p : ~ bproof 0 x p.
  Proof.
    destruct p as [ y ll ].
    unfold bproof, bounded_tree.
    rewrite tree_ht_fix.
    omega.
  Qed.   
  
  Fact bproof_S n x p : 
         bproof (S n) x p 
     <-> tree_root p = x 
      /\ rules x (proof_sub p) 
      /\ Forall2 (bproof n) (proof_sub p) (tree_sons p).
  Proof.
    unfold bproof at 1; rewrite bounded_tree_S.
    destruct p as [ y ll ]; simpl.
    unfold proof_sub; simpl.
    rewrite Forall2_map_left, Forall2_Forall.
    do 2 rewrite Forall_forall.
    unfold proof; rewrite proof_tree_fix.
    unfold bproof.
    split.

    intros (((H1 & H2) & H3) & H4); repeat split; auto.
    simpl in H3; subst y; auto.
    
    intros (H1 & H2 & H3); repeat split; subst; auto;
    intros t Ht; apply H3; auto.
  Qed.
  
  (* A dependent recursion principle for bproof *)

  Section bproof_rect.
  
    Variable P : nat -> stm -> tree stm -> Type.
    
    Hypothesis HP : forall n c ll tt, rules c ll 
                                   -> Forall2 (bproof n) ll tt 
                                   -> bproof n inc2 P n  
                                   -> P (S n) c (in_tree c tt).

    Theorem bproof_rect n x t : bproof n x t -> P n x t.
    Proof.
      revert x t.
      induction n as [ | n IHn ].
      intros x t H; exfalso; revert H; apply bproof_O.
      intros x [ c ll ] Ht.
      rewrite bproof_S in Ht; simpl in Ht.
      destruct Ht as (? & Hc & Ht); subst x.
      apply HP with (1 := Hc); trivial.
    Qed.

  End bproof_rect.
  
  (* Sinces rules are finitary, there are finitely many bounded proofs 
     which can be collected into a computable list *)
  
  Section bproof_finite_t.

    Let bproof_S_eq n x : 
            bproof (S n) x 
       ~eq1 fun p => exists c, 
                        (rules x (fst c) /\ Forall2 (bproof n) (fst c) (snd c)) 
                      /\ p = in_tree x (snd c).
    Proof.
      split; intros [y ll]; rewrite bproof_S.
      intros (H1 & H2 & H3); subst x.
      unfold proof_sub in H2, H3; simpl in H2, H3 |- *.
      exists (map (@tree_root _) ll,ll); repeat split; auto.
      intros ((mm,tt) & (H1 & H2) & H3).
      simpl in H3.
      injection H3; clear H3; intros; subst y tt; simpl in H1, H2 |- *.
      unfold proof_sub; simpl.
      assert (mm = map (@tree_root _) ll) as E.
        rewrite <- Forall2_eq, Forall2_map_right.
        revert H2; apply Forall2_impl.
        unfold bproof, proof.
        intros ? ? ((_ & ?) & _); auto.
      subst mm; auto.
    Qed.
    
    (* The argument is by induction on the height *)

    Theorem bproof_finite_t n x : finite_t (bproof n x).
    Proof.
      revert x; induction n as [ | n IHn ]; intros x.
      
      (* No proof at height 0 *)

      exists nil.
      split.
      intros [].
      intros H; exfalso; revert H; apply bproof_O.
      
      (* collect all proofs of all possible premises and
         build proofs in one step from those only *)
    
      apply finite_t_eq with (1 := eq1_sym _ _ (bproof_S_eq n x)).
      apply finite_t_relmap.
      2: intros; apply finite_t_img.
      apply finite_t_relprod; auto.
      intros; apply finite_t_rel_inv; auto.
    Qed.
    
  End bproof_finite_t.
  
  Corollary bproof_decidable_t n x : { p | bproof n x p } + { forall p, ~ bproof n x p }.
  Proof.
    destruct (bproof_finite_t n x) as ( [ | p ? ] & H ).
    right; intro; rewrite <- H; tauto.
    left; exists p; apply H; left; trivial.
  Qed.
  
  (* No proof of x has height below n *)
  
  Definition proof_min_ht x n := forall p, proof x p -> n <= tree_ht p.
  
  (* From a proof p of x one can compute a proof with minimal height 
     simply compute the list of proofs of height bounded by that of p
     and search for a minimal one in that list 
  *)
  
  Definition min_proof x t := proof x t /\ proof_min_ht x (tree_ht t).
  
  Lemma proof_minimize x p : proof x p -> { p | min_proof x p }.
  Proof.
    intros Hp.
    destruct (@minimizer_finite_t _ (@tree_ht _) (bproof (tree_ht p) x) (bproof_finite_t _ _))
      as (q & H1 & H2).
    exists p; split; auto; apply le_refl.
    exists q; split.
    apply H1.
    intros s Hs.
    destruct (le_lt_dec (tree_ht s) (tree_ht p)) as [ H3 | H3 ].
    apply H2; split; auto.
    apply lt_le_weak in H3.
    apply le_trans with (2 := H3).
    apply H2; split; auto; apply le_refl.
  Qed.
  
  (* This proof tree has minimal height *)
  
  Definition ptree_has_min_ht x ll := proof_min_ht x (tree_ht (in_tree x ll)).
  
  (* Every sub proof has minimal height, 
     this is an *everywhere minimal* proof tree
   *)

  Definition ptree_min_all_ht := tree_fall ptree_has_min_ht.
 
  Fact ptree_min_all_ht_fix x ll : 
           ptree_min_all_ht (in_tree x ll) 
       <-> ptree_has_min_ht  x ll
        /\ forall t, In t ll -> ptree_min_all_ht t.
  Proof. apply tree_fall_fix. Qed.

  Fact ptree_min_all_min_ht : forall p, ptree_min_all_ht p -> proof_min_ht (tree_root p) (tree_ht p).
  Proof.
    intros [? ?]; simpl tree_root; rewrite ptree_min_all_ht_fix; tauto.
  Qed.
  
  (* From a n-bounded proof of x, one can compute an everywhere minimal proof of x 
     The argument is by induction on n *)

  Local Lemma proof_minimize_all_rec n x p : bproof n x p -> { q | proof x q /\ ptree_min_all_ht q }.
  Proof.
    revert x p; induction n as [ | n IHn ].
     
    intros x p Hp.
    exfalso; revert Hp; apply bproof_O.
    
    intros x p (H1 & H2).
    destruct (proof_minimize H1) as (q & Hq1 & Hq2).
    assert (bproof (S n) x q) as Hq3.
      split; auto.
      unfold bounded_tree in H2 |- *.
      apply le_trans with (2 := H2).
      apply Hq2; auto.
    clear p H1 H2.
    
    destruct q as [ y ll ].
    rewrite bproof_S in Hq3.
    unfold proof_sub in Hq3; simpl in Hq3.
    destruct Hq3 as (H1 & H2 & H3); subst y.
    generalize (invert_sig_t H3); intros f.
    assert (forall y, In_t y (map (@tree_root _) ll) -> { q | proof y q /\ ptree_min_all_ht q }) as IH.
      intros y Hy.
      destruct (f _ Hy) as (p & Hp).
      apply IHn with (1 := Hp).
    clear IHn f.
    apply sig_t_invert in IH.
    destruct IH as (mm & Hmm).
    
    exists (in_tree x mm); split.
    split; auto.
    rewrite proof_tree_fix; split.
    replace_with H2; symmetry.
    apply Forall2_eq, Forall2_map_both.
    revert Hmm.
    rewrite Forall2_map_left.
    apply Forall2_impl.
    intros a b; intros ((? & ?) & ?); auto.
    apply Forall_forall.
    apply Forall2_conj, proj1 in Hmm.
    rewrite Forall2_map_left in Hmm.
    revert Hmm.
    clear H2 H3 Hq1 Hq2.
    induction 1 as [ | ? ? ? ? H1 ]; constructor; auto; apply H1.
    
    rewrite ptree_min_all_ht_fix.
    apply Forall2_conj in Hmm.
    destruct Hmm as (Hmm1 & Hmm2).
    apply Forall2_right_Forall, proj1 in Hmm2.
    rewrite Forall_forall in Hmm2.
    split; auto.
    assert (map (@tree_root _) ll = map (@tree_root _) mm) as Hlm.
      apply Forall2_eq, Forall2_map_right.
      revert Hmm1; apply Forall2_impl.
      intros ? ? (? & ?); auto.
    generalize (@proof_proof_sub _ _ _ Hq1); intros Hq3.
    intros t Ht.
    apply le_trans with (2 := Hq2 _ Ht).
    do 2 rewrite tree_ht_fix.
    apply le_n_S, Forall2_lmax.
    apply Forall2_map_both.
    clear t Ht Hmm1 H2 H3 Hq2 Hq1 n x.
    apply Forall2_eq in Hlm. 
    rewrite Forall2_map_both in Hlm.
    assert (forall x, In x mm -> proof_min_ht (tree_root x) (tree_ht x)) as H.
      intros x Hx; specialize (Hmm2 _ Hx); revert Hmm2; apply ptree_min_all_min_ht.
    clear Hmm2.
    revert H Hq3.
    induction Hlm as [ | x y ll mm H1 H2 IH2 ]; intros H3 H4; constructor; auto.
    apply (H3 y).
    left; auto.
    rewrite <- H1; apply H4; left; auto.
    apply IH2.
    intros; apply H3; right; auto.
    intros; apply H4; right; auto.
  Qed.
  
  Definition emin_ptree t := proof_tree t /\ ptree_min_all_ht t.
  
  Fact emin_ptree_fix x ll : emin_ptree (in_tree x ll) 
                         <-> min_proof x (in_tree x ll) 
                          /\ forall t, In t ll -> emin_ptree t.
  Proof.
    split; intros [H1 H2].
    
    rewrite ptree_min_all_ht_fix in H2.
    destruct H2 as [ H2 H3 ]; red in H2.
    repeat split; auto.
    rewrite proof_tree_fix in H1; apply H1; auto.
    
    destruct H1 as [ [ H1 H3 ] H4 ].
    split; auto.
    apply ptree_min_all_ht_fix; split.
    red; auto.
    intros ? ?; apply H2; auto.
  Qed.
  
  Definition emin_proof x t := proof x t /\ emin_ptree t.

  (* if x has a proof p then it has an everywhere minimal proof *)

  Theorem proof_eminimize x p : proof x p -> { q | emin_proof x q }.
  Proof.
    intros H.
    destruct (@proof_minimize_all_rec (tree_ht p) x p) as (q & H1 & H2).
    split; auto; red; auto.
    exists q; split; auto.
    split; auto; apply H1.
  Qed.
  
  (** The proof search sequence 
  
      Starting from a statement s, we define a sequence (proof_search s)
      of list of statements such that every branch of every
      proof of s is a choice sequence of (proof_search s)
    *)
  
  Definition rules_next l := flat_map (fun x => x) (flat_map (fun x => proj1_sig (rules_fin x)) l).
  
  (* rules_next l contains exactly those statements h such that 
     there is a rule instance of the form
     
            ...   h   ...
            -------------
                  c
                  
     where c belongs to l
   *)
  
  Fact rules_next_spec l h : In h (rules_next l) <-> exists c mm, In c l /\ In h mm /\ rules c mm.
  Proof.
    unfold rules_next.
    rewrite in_flat_map; split.
    
    intros (mm & H1 & H2).
    rewrite in_flat_map in H1.
    destruct H1 as (c & H1 & H3).
    apply (proj2_sig (rules_fin c)) in H3.
    exists c, mm; auto.
    
    intros (c & mm & H1 & H2 & H3).
    exists mm; split; auto.
    rewrite in_flat_map.
    exists c; split; auto.
    apply (proj2_sig (rules_fin c)), H3.
  Qed.

  Fact rules_next_mono l m : incl l m -> incl (rules_next l) (rules_next m).
  Proof.
    intros H x.
    do 2 rewrite rules_next_spec.
    intros (c & mm & ? & ? & ?).
    exists c, mm; auto.
  Qed.
  
  (** The iterated sequence of rules_next from a initial conclusion 
      This sequence collects every possible proof search branch.
      Beware that it collects MORE than that, it is a strict upper bound.
      
      But this is no problem for the rest of the development. 
  *)
  
  Fixpoint proof_search x n :=
    match n with
      | 0   => x::nil
      | S n => rules_next (proof_search x n)
    end.
    
  Fact proof_search_mono x y n :
       In x (rules_next (y::nil))
    -> Forall2 (@incl _) (pfx (proof_search x) n) 
                         (pfx (fun n => proof_search y (S n)) n).
  Proof.
    intros Hxy.
    apply Forall2_pfx.
    intros i _; clear n.
    induction i as [ | i IHi ]; simpl.
    intros ? [ [] | [] ]; auto.
    apply rules_next_mono, IHi.
  Qed.
  
  (* The proof_search s sequence collects all the
     branches of all the proofs of s in its FAN
     
     the Fan of [proof_search x 0; ...; proof_search x (n-1)] contains every
     branch of length n of any proof of x *)

  Fact ptree_proof_search t b : 
       tree_branch t b 
    -> proof_tree t 
    -> In b (list_fan (pfx (proof_search (tree_root t)) (length b))).
  Proof.
    induction 1 as [ | x | b x ll s H1 H2 IH2 ]; 
      try (simpl; left; auto; fail).
    
    rewrite proof_tree_fix; intros (H3 & H4).
    rewrite list_fan_spec.
    simpl tree_root; simpl pfx.
    constructor 2.
    left; auto.
    
    specialize (IH2 (H4 _ H1)).
    rewrite <- list_fan_spec.
    revert IH2; apply list_fan_mono.
    
    apply proof_search_mono, rules_next_spec.
    exists x, (map (@tree_root _) ll).
    simpl; repeat split; auto.
    apply in_map_iff; exists s; auto.
  Qed.
   
  (* (sf x y) means y is made only of subformulae of those of x *)

  Variable sf : stm -> stm -> Prop.                   
  Hypothesis sf_refl : forall s, sf s s.
  Hypothesis sf_trans : forall x y z, sf x y -> sf y z -> sf x z.
  
  (* rules are stable under subformulae *)
  
  Hypothesis sf_rules : forall c ll, rules c ll -> Forall (sf c) ll.
  
  (* proof search only contains subformulae of the initial formula *) 

  Fact proof_search_sf x n : Forall (sf x) (proof_search x n).
  Proof.
    rewrite Forall_forall.
    induction n; simpl.
    intros ? [ [] | [] ]; auto.
    unfold rules_next.
    intros s; rewrite in_flat_map.
    intros (l & H1 & H2).
    rewrite in_flat_map in H1.
    destruct H1 as (y & H1 & H3).
    apply (proj2_sig (rules_fin y)) in H3.
    apply IHn in H1.
    apply sf_trans with (1 := H1).
    specialize (sf_rules H3). 
    rewrite Forall_forall in sf_rules; auto.
  Qed.   

  (* any branch in a proof of x contains only subformulas of x *)
  
  Fact proof_sf x t b : proof x t -> tree_branch t b -> Forall (sf x) b.
  Proof.
    intros H1 H2.
    generalize (ptree_proof_search H2 (proj1 H1)).
    rewrite list_fan_spec, Forall_forall.
    intros H3 y Hy.
    destruct (Forall2_In_inv_left H3 _ Hy) as (u & H4 & H5).
    apply pfx_In in H4.
    destruct H4 as (i & H4 & H6); subst u.
    rewrite <- (proj2 H1); auto.
    revert H5; apply Forall_forall.
    apply proof_search_sf.
  Qed.

  (** We use a notion of redundancy for stm which is supposed
      to be almost full (on the subset of subformulae of a given stm)
  
      Typically in Relevant logic, redunt (Ga |- A) (De |- B) 
      
          means A = B and Ga is a contraction of De
          
      ie Ga has the same formulae of De except that De might have 
      more copies of them than in Ga (also called cognate sequents)
      
      Hence the relation between Ga and De is the intersection of two
      almost full relations:
        - having the same carrier set
        - Ga is below De in the product in <= (over nat)
          of every component of the multisets
          
      By Ramsey's theorem, it is thus an almost full relation as well 
    *)   

  Variable redund : stm -> stm -> Prop.
  
  (* A irreducible proof is one that has not redundant branch 
     and a redudant branch contains a redundant (or good) pair *)
  
  Definition irred_proof x p := proof x p /\ tree_irred redund p.
  
  (* We assume Curry's lemma holds, ie redundancies can be removed while preserving the height *)

  Hypothesis Currys_lemma : forall x y p, proof y p -> redund x y -> exists q, proof x q /\ tree_ht q <= tree_ht p.

  (* from Curry's lemma, we deduce that proofs which minimize the height of every of their subproofs
     are necessarily irredundant 
     
     and as a consequence, every provable stm has an irredundant proof *) 
  
  Theorem proof_min_all_imp_irred x p : proof x p -> ptree_min_all_ht p -> irred_proof x p.
  Proof.
    intros H1 H2; split; auto.
    intros b Hb.
    apply not_good_eq_bad.
    intros H3.
    
    (* we have a branch b with a redundancy *)
    (* let us find this redundancy (and clean up the mess) *)
    
    apply good_inv in H3.
    destruct H3 as (l & v & m & u & r & H3 & H4).
    apply f_equal with (f := @rev _) in H3.
    rewrite rev_involutive in H3.
    repeat (rewrite rev_app_distr in H3; simpl in H3).
    repeat (rewrite app_ass in H3; simpl in H3).
    subst b.
    revert Hb; generalize (rev r) (rev m) (rev l); clear r l m.
    intros l m r Hb.
    rename H4 into H3.
    
    (* v is redundant over u in branch l -- u -- m -- v -- r *)
    (* let us find the subproofs with root u and with root v *)

    apply tree_split_search in Hb.
    destruct Hb as [ (Hb & _) | (q & lu & Hb & H4 & H5) ].
    1: destruct m; discriminate.
    
    apply tree_search in Hb.
    destruct Hb as ([ y lv ] & H7 & H8).
    generalize (tree_branch_root H7); simpl; intro; subst y.
    
    (* we show that the subtree with root v is a proof of v *)
    
    assert (proof v (in_tree v lv)) as Hv.
      generalize (ptree_proof _ (proj1 H1)).
      rewrite tree_fall_sub_tree.
      intros H9; apply H9.
      apply sub_tree_trans with (2 := H5).
      constructor 2 with q; auto.
    
    (* We show that the subproof at v is strictly smaller than 
       the subproof at u *)

    assert (tree_ht (in_tree v lv) < tree_ht (in_tree u lu)) as C.
      rewrite tree_ht_fix with (x := u).
      apply le_n_S.
      assert (In (tree_ht q) (map (@tree_ht _) lu)) as H.
      apply in_map_iff; exists q; auto.
      apply le_trans with (2 := lmax_In _ _ H).
      apply sub_tree_ht; auto.
      
    (* by Curry's lemma, u has a smaller proof than that of v 
       which is itself stricly smaller that the proof of u 
       rooted at u in p *)
      
    destruct (Currys_lemma Hv H3) as (k & Hk1 & Hk2).
      
    (* This contradicts the everywhere minimality of p *)

    red in H2; rewrite tree_fall_sub_tree in H2.
    specialize (H2 _ _ H5 _ Hk1); omega.
  Qed.

  Theorem proof_emin_irred s t : emin_proof s t -> irred_proof s t.
  Proof.
    intros (H1 & H2).
    apply proof_min_all_imp_irred; auto.
    apply H2.
  Qed.
  
  (** As a consequence of Curry's lemma, every proof can be transformed
      into an irredundant proof *)
  
  Theorem proof_reduce x p : proof x p -> { q | irred_proof x q }.
  Proof.
    intros Hp.
    destruct proof_eminimize with (1 := Hp) as (q & Hq).
    exists q; apply proof_emin_irred, Hq.
  Qed.

  (** An essential ingredient of the decidability proof
      is that redundancy is supposed to be Almost Full (AF)
      (or classically speaking, a Well Quasi Order (WQO), 
       ie every infinite chain contains a redundant pair) 

      But the AF property needs only be fulfilled on the subset 
      of statements composed of subformulae of the initial stm.
     
      Otherwise the requirement would be too strong 
   *)
  
  Hypothesis redund_af_t : forall s, af_t (redund <# sf s #>).
  
  Section Koenigs_lemma_replacement.
 
    (* this replaces König's lemma: 
    
         a/ above a certain length, every list of a given FAN contains a good pair 
         b/ the branches of proof search of are choice sequences in
            the FANS of (proof_search _)
     *)

    Variable (s : stm) (f : nat -> list stm) (Hf : forall n : nat, Forall (sf s) (f n)).

    Notation P := (sf s).
    
    (* From a sequence f of list of stm st f n verifies Forall P
       we compute a sequence g of list (sig P) by decorating each
       element with its corresponding proof. 
     *)

    Let g (n : nat) : list (sig P).
    Proof.
      refine (list_Forall_sig P (f n) _).
      apply Forall_forall, Hf.
    Defined.
    
    (* Forgetting the proofs from g gives you f back *) 
    
    Let Hg n : map (@proj1_sig _ _) (g n) = f n .
    Proof. apply list_sig_Forall_eq. Qed.
    
    (* since redund is almost full on sig P, we can apply the constructive
       Koenigs lemma which is an instance if the FAN theorem *)

    Lemma irredundant_max_length : { n | forall m, n <= m -> Forall (good redund) (list_fan (pfx_rev f m)) }.
    Proof.
      destruct (Constructive_Koenigs_lemma (redund_af_t s) g) as (n & Hn).
      exists n.
      
      intros m Hm.
      specialize (Hn _ Hm); revert Hn.
      clear n Hm.
      
      apply Forall2_Forall_Forall with (T := fun x y => y = map (@proj1_sig _ _) x).
      
      intros x ? ?; subst; apply good_Restr.
      
      rewrite <- Forall2_exchg, <- Forall2_map_right, Forall2_eq, <- list_fan_map_map.
      f_equal; symmetry.
      rewrite <- pfx_rev_map.
      apply pfx_rev_ext.
      intros; apply Hg.
    Qed.
    
  End Koenigs_lemma_replacement.

  (* We deduce that for a given stm s, on can compute a bound n such that
     every irredundant proof of s much have a height bounded by n
     
     Notice that the bound n depends only on the initial statement s
   *)
  
  Theorem proof_irred_bounded s : { n | irred_proof s inc1 bproof n s }.
  Proof.
    destruct irredundant_max_length with s (proof_search s) as (n & Hn).
      
    apply proof_search_sf.
      
    exists n.
    intros p ((H1 & H0) & H2).
    apply bproof_branch; split; auto.
    split; auto.
    intros b Hb.
    destruct (le_lt_dec (length b) n) as [ | C ]; auto; exfalso.
    apply lt_le_weak, Hn in C; rewrite Forall_forall in C.
    generalize (ptree_proof_search Hb H1); rewrite H0; intros H5.
    apply H2 in Hb.
    revert Hb.
    apply good_bad_False, C.
    rewrite pfx_pfx_rev_eq, list_fan_rev; trivial.
  Qed.

  (** We collect our arguments. Let s be a stm. We compute
      n which bounds every irredundant proof of s
  
        1/ if s has a proof 
        2/ then s has an everywhere minimal proof (proof_minimize_all_ht)
        3/ then s has an irredundant proof (proof_min_all_imp_irred)
        4/ then s has a n-bounded proof (proof_irred_bounded)
  
     Decision is simple : since n-bounded proofs is a decidable
       type (it is described by a constructible (finite) list) 
       
     a/ either s has a n-bounded proof and then it obvisouly
        has a proof
     b/ or s has no n-bounded proof and thus it cannot have 
        a proof either by 1/-2/-3/-4/
        
     Being able to compute n is essential in this decision 
     algorithm 
   *)

  Theorem proof_decider x : { p | proof x p } + { forall p, ~ proof x p }.
  Proof.
    (* compute the bound n for x *)
    destruct (proof_irred_bounded x) as (n & Hn).
    
    (* search among the proof of height bounded by n *)
    destruct (bproof_decidable_t n x) as [ (p & Hp) | H ].
    
    (* there is a proof (of height bounded by n) *)
    left; exists p; apply Hp.
    
    (* there are no proofs of height bounded by n *)
    right; intros p Hp.
    destruct proof_reduce with (1 := Hp) as (q & Hq).
    apply (H q), Hn, Hq.
  Qed.

End proofs.

Check proof_decider.

