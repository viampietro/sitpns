(* ***********************************************************************) 
(*                                                                       *)
(*   Synchronously executed Interpreted Time Petri Nets (SITPNs)         *)
(*                                                                       *)
(*                                                                       *)
(*   Copyright Université de Montpellier, contributor(s): Vincent        *)
(*   Iampietro, David Andreu, David Delahaye (May 2020)                  *)
(*                                                                       *)
(*   This software is governed by the CeCILL-C license under French law  *)
(*   and abiding by the rules of distribution of free software.  You can *)
(*   use, modify and/ or redistribute the software under the terms of    *)
(*   the CeCILL-C license as circulated by CEA, CNRS and INRIA at the    *)
(*   following URL "http://www.cecill.info".  The fact that you are      *)
(*   presently reading this means that you have had knowledge of the     *)
(*   CeCILL-C license and that you accept its terms.                     *)
(*                                                                       *)
(* ***********************************************************************) 

(** * Combination of [fst] and [split] on lists of couples. *)

(** Definitions, lemmas and tactics pertaining to the combination of
    the [fst] and [split] functions on lists of couples.  *)

Require Import Coqlib.
Require Import Coq.Setoids.Setoid.

(** Macro for [fst] and [split] composition. *)

Definition fs {A B} (l : list (A * B)) := fst (split l).

(** Proves a property over the combination of fst and split functions. *)

Lemma fst_split_cons_app {A B : Type} :
  forall (a : (A * B)) (l : list (A * B)),
    fst (split (a :: l)) = (fst (split [a])) ++ (fst (split l)).
Proof.
  intros. elim a; simpl. elim split; simpl. auto.
Qed.

(** Equality between [map fst] and [fst (split)]
    applied to some list l.
 *)

Lemma map_fst_split_eq {A B : Type} :
  forall (l : list (A * B)),
    List.map fst l = fst (split l).
Proof.
  induction l.

  (* l = [] *)
  - simpl; reflexivity.

  (* a::l *)
  - destruct a.
    rewrite fst_split_cons_app.
    simpl.
    rewrite IHl; reflexivity.
Qed.

(** Declares [fst (split)] as a morphism of the Permutation
    relation. *)

Add Parametric Morphism A B : (@fs A B)
    with signature (@Permutation (A * B)) ==> (@Permutation A)
      as fst_split_morphism.
Proof.
  intros x y Hperm.
  apply (Permutation_map fst) in Hperm.
  rewrite (map_fst_split_eq x) in Hperm.
  rewrite (map_fst_split_eq y) in Hperm.
  assumption.
Qed.

(** Proves a property over the combination of snd and split functions. *)

Lemma snd_split_cons_app {A B : Type} :
  forall (a : (A * B)) (l : list (A * B)),
    snd (split (a :: l)) = (snd (split [a])) ++ (snd (split l)).
Proof.
  intros. elim a; simpl. elim split; simpl. auto.
Qed.

(** Proves that applying the combination of [fst] and [split] on the concatenation
    of list [l] and [l'] is the same as applying separately [fst] and [split] on each list,
    and then concatenating the result. 
 *)

Lemma fst_split_app {A B : Type} :
  forall (l l' : list (A * B)),
    (fst (split (l ++ l'))) = fst (split l) ++ fst (split l').
Proof.
  intros.
  elim l; intros.
  - simpl; auto.
  - rewrite fst_split_cons_app.
    rewrite <- app_comm_cons.
    rewrite fst_split_cons_app.
    rewrite H.
    rewrite app_assoc_reverse.
    reflexivity.
Qed.

(** Proves that applying the combination of [snd] and [split] on the concatenation
    of list [l] and [l'] is the same as applying separately [snd] and [split] on each list,
    and then concatenating the result. 
 *)

Lemma snd_split_app {A B : Type} :
  forall (l l' : list (A * B)),
    (snd (split (l ++ l'))) = snd (split l) ++ snd (split l').
Proof.
  intros.
  elim l; intros.
  - simpl; auto.
  - rewrite snd_split_cons_app.
    rewrite <- app_comm_cons.
    rewrite snd_split_cons_app.
    rewrite H.
    rewrite app_assoc_reverse.
    reflexivity.
Qed.

(** For all list of pairs l and element a, if a is not in [(fst (split l))], 
    then there is no pair in l containing a as first element. *)

Lemma not_in_fst_split {A B : Type} :
  forall (l : list (A * B)) (a : A),
    ~In a (fst (split l)) -> (forall b : B, ~In (a, b) l).
Proof.
  induction l.
  - intros; intro; elim H0.
  - elim a; intros.
    rewrite fst_split_cons_app in H.
    simpl in H.
    apply Decidable.not_or in H.
    elim H; intros.
    apply not_in_cons.
    split.
    + injection; intros.
      symmetry in H4.
      contradiction.
    + generalize (IHl a1 H1); intro.
      apply H2.
Qed.

(** For all pairs in l, in there are no duplicates in the first 
    elements of the pairs in l, then there are no duplicates in l. *)

Lemma nodup_fst_split {A B : Type} :
  forall l : list (A * B), NoDup (fst (split l)) -> NoDup l.
Proof.
  induction l.
  - intro. apply NoDup_nil.
  - elim a.
    intros.
    rewrite fst_split_cons_app in H.
    simpl in H.
    apply NoDup_cons_iff in H.
    elim H; intros.
    apply IHl in H1.
    generalize (not_in_fst_split l a0 H0 b); intro.
    generalize (conj H2 H1); intro.
    apply <- NoDup_cons_iff in H3.
    auto.
Qed.

(** If a couple (a, b) is in the list of couples l 
    then a is in (fst (split l)). *)

Lemma in_fst_split {A B : Type} :
  forall  (a : A) (b : B) (l : list (A * B)),
    In (a, b) l -> In a (fst (split l)).
Proof.
  induction l.
  - auto.
  - elim a0.
    intros.
    rewrite fst_split_cons_app.
    simpl.
    apply in_inv in H.
    elim H; intros.
    + injection H0; intros.
      left; auto.
    + apply IHl in H0; right; auto.
Qed.

(** If a ∈ (fst (split l)) then
    ∃ b | (a,b) ∈ l. 
 *)
Lemma in_fst_split_in_pair {A B : Type} :
  forall  (a : A) (l : list (A * B)),
    In a (fst (split l)) -> exists b : B, In (a, b) l.
Proof.
  intros.
  induction l.
  - elim H.
  - dependent induction a0.
    rewrite fst_split_cons_app in H; simpl in H.
    elim H; intro.
    + exists b; rewrite H0; apply in_eq.
    + apply IHl in H0; elim H0; intros.
      exists x; apply in_cons; assumption.
Qed.
