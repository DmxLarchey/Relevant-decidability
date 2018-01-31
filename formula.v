(**************************************************************)
(*   Copyright Dominique Larchey-Wendling [*]                 *)
(*                                                            *)
(*                             [*] Affiliation LORIA -- CNRS  *)
(**************************************************************)
(*      This file is distributed under the terms of the       *)
(*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
(**************************************************************)

Require Import Arith List.

Require Import list_utils finite.

Set Implicit Arguments.

Inductive Var : Set := in_Var : nat -> Var.

Inductive Form : Set := 
  | Form_var : Var -> Form
  | Form_op : Form -> Form -> Form.
  
Fact Var_eq_dec (x y : Var) : { x = y } + { x <> y }.
Proof.
  decide equality.
  apply eq_nat_dec.
Qed.
  
Fact Form_eq_dec (x y : Form) : { x = y } + { x <> y }.
Proof.
  decide equality.
  apply Var_eq_dec.
Qed.

Infix "%>" := Form_op (at level 49, right associativity).
Infix "⊃" := Form_op (at level 49, right associativity).
Notation "'£' x" := (Form_var x) (at level 49).
  
Fixpoint sf_Form f := 
  match f with 
    | £ x    => fun y => y = £ x
    | a %> b => fun y => y = a %> b \/ sf_Form a y \/ sf_Form b y
  end.

Fact sf_Form_refl f : sf_Form f f.
Proof. 
  induction f as [ v | a Ha b Hb ]; simpl; auto.
Qed.

Fact sf_Form_finite_t f : finite_t (sf_Form f).
Proof.
  induction f as [ v | a Ha b Hb ].
  exists (£ v :: nil); simpl; intros; split; auto.
  intros [ | [] ]; auto.
  generalize (finite_t_cup Ha Hb).
  intros (ll & Hll).
  exists ((a %> b) :: ll).
  intros x; split.
  intros [ ? | ? ].
  subst; left; auto.
  right; apply Hll; auto.
  intros [ ? | ? ].
  left; auto.
  right; apply Hll; auto.
Qed.

Reserved Notation "x '%%>' y" (at level 49, right associativity).

Fixpoint list_Form_to_Form l a := 
  match l with 
    | nil  => a
    | f::l => l %%> (f %> a)
  end
where "l %%> a" := (list_Form_to_Form l a).

Fact list_Form_to_Form_cons x l a : (x::l) %%> a = l %%> x %> a.
Proof. auto. Qed.
  
Fact list_Form_to_Form_app l m a : (l++m) %%> a = m %%> l %%> a.
Proof. revert a; induction l; simpl; auto. Qed.

