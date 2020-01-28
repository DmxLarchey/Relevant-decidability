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
  The paper has been presented at IJCAR 2018.
  A [*revised and extended version*](http://www.loria.fr/~larchey/papers/JAR-2019.pdf) 
  of this paper is going to appear in the _Journal of Automated Reasonning (JAR)_.

* The Coq mechanization of the decidability proof for Implicational Relevance 
  logic is purely constructive, replacing Kripke/Dickson's lemma and
  König's lemma by inductive counterparts based on the notion of
  Almost Full relations.

* The code in sync the IJCAR publication is tagged [`v1.0`](tree/v1.0).

* The code in sync with the JAR publication is tagged [`v2.0`](/tree/v2.0).

### How do I get a set up? ###

* Using `Coq 8.8+` (see below), compile this repository with `make all`
  (or `make -j 16 all` if you have 16 CPU cores available)
  and you can then review the proofs using your favorite Coq IDE.
  The file you want to review first in [`logical_deciders.v`](logical_deciders.v).

* Compilation was tested thoroughly and should work under the following
  versions of Coq: `Coq 8.8.2`, `Coq 8.9.1` and `Coq 8.10.1`.
  However, cleaning up with `make clean` might be necessary 
  when switching to another version of Coq.

* This repository was initially designed under `Coq 8.6.1`. However, due to changes in 
  more recent versions of Coq, e.g. the `Focus` command being marked deprecated, 
  the code has been updated and should now be compiled starting with `Coq 8.8`.

