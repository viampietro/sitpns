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

(** Finite sets of nat star (non-zero nat). *)

Require Import MSets.MSetWeakList.
Require Import Coq.Structures.OrdersEx.
Require Import Structures.Equalities.

(** Defines the module type of sig. that are decidable on their first argument. *)

Module Type DecidableTypeSubset (A : DecidableType) <: DecidableType.

  Parameter P : A.t -> Prop.
  
  Definition t := { a : A.t | P a }.
  Definition eq (x y : t) := A.eq (proj1_sig x) (proj1_sig y).
  
  Definition eq_refl : forall x, eq x x.
    intros x. apply (@Equivalence_Reflexive A.t A.eq A.eq_equiv (proj1_sig x)).
  Defined.
  Definition eq_sym : forall x y, eq x y -> eq y x.
    intros x y. apply (@Equivalence_Symmetric A.t A.eq A.eq_equiv (proj1_sig x)).
  Defined.
  Definition eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
    intros x y z. apply (@Equivalence_Transitive A.t A.eq A.eq_equiv (proj1_sig x)).
  Defined.

  Definition eq_equiv := Build_Equivalence eq eq_refl eq_sym eq_trans.
  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}. intros x y. apply A.eq_dec. Defined.
  
End DecidableTypeSubset.

(** Defines the module of nat star as a decidable type, without using
    the DecidableTypeSubset module.
 *)

Module NStar_as_DT <: DecidableType.
  
  Definition t := { n | n > 0 }.

  Definition eq (x y : t) := Nat_as_DT.eq (proj1_sig x) (proj1_sig y).
  Definition eq_refl : forall x, eq x x.
    intros x. apply (@Equivalence_Reflexive Nat_as_DT.t Nat_as_DT.eq Nat_as_DT.eq_equiv (proj1_sig x)).
  Defined.
  Definition eq_sym : forall x y, eq x y -> eq y x.
    intros x y. apply (@Equivalence_Symmetric Nat_as_DT.t Nat_as_DT.eq Nat_as_DT.eq_equiv (proj1_sig x)).
  Defined.
  Definition eq_trans : forall x y z, eq x y -> eq y z -> eq x z.
    intros x y z. apply (@Equivalence_Transitive Nat_as_DT.t Nat_as_DT.eq Nat_as_DT.eq_equiv (proj1_sig x)).
  Defined.

  Definition eq_equiv := Build_Equivalence eq eq_refl eq_sym eq_trans.
  Lemma eq_dec : forall x y, {eq x y} + {~eq x y}. intros x y. apply Nat_as_DT.eq_dec. Defined.
  
End NStar_as_DT.

Module NStarSet := Make NStar_as_DT.
Include NStarSet.
