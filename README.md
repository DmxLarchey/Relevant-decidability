# A Constructive Mechanization of Kripke-Curry's method for the Decidability of Implicational Relevance Logic

        (**************************************************************)
        (*   Copyright Dominique Larchey-Wendling [*]                 *)
        (*                                                            *)
        (*                             [*] Affiliation LORIA -- CNRS  *)
        (**************************************************************)
        (*      This file is distributed under the terms of the       *)
        (*         CeCILL v2 FREE SOFTWARE LICENSE AGREEMENT          *)
        (**************************************************************)

### What is this repository for? ###

* This repository is a companion Coq development for the paper 
  [*Constructive Decision via Redundancy-free Proof-Search*](http://www.loria.fr/~larchey/papers/IJCAR-2018_paper_74.pdf) 
  by [Dominique Larchey-Wendling](http://www.loria.fr/~larchey).
  The paper has been accepted and is going to be presented at IJCAR 2018.

* The Coq mechanization of the decidability proof for Implicational Relevance 
  logic is purely constructive, replacing Kripke/Dickson's lemma and
  König's lemma but inductive counterparts based on the notion of
  Almost Full relations.

### How do I get a set up? ###

* This repository was designed under Coq 8.6. Compile it with `make logical_deciders.vo`
  (or `make -j 16 all` if you have 16 CPU cores available)
  and you can then review the proofs using your favourite Coq IDE.

* Compilation was tested and should also work under Coq 8.5pl[23] 
  and Coq 8.7.1.

