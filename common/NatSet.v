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

Require Import MSets.MSetWeakList.
Require Import Coq.Structures.OrdersEx.
Require Import Arith.
Require Import SetoidList.

(** Defines finite sets of natural. *)

Module NatSet := Make (Nat_as_OT).
Import NatSet.

Declare Scope natset_scope.

Infix "U" := union (at level 60, right associativity).
Infix "U+" := add (at level 60, right associativity).
Notation "{[ ]}" := empty (format "{[ ]}") : natset_scope.
Notation "{[ x , y , .. , z ]}" := (add x (add y .. (add z empty) ..)) : natset_scope.
Notation "{[ x ]}" := (add x empty) (at level 0) : natset_scope.

(* Include NatSet.Raw. *)

(* Lemma for_all_ind : forall Q x s, For_all Q (x :: s) -> For_all Q s. *)
(* Proof. *)
(*   intros Q x s Hforall y Hin_y_s. *)
(*   apply (Hforall y (InA_cons_tl x Hin_y_s)). *)
(* Defined. *)

(* Fixpoint filter_ Q (EltSubset := { e : elt | Q e }) (f : EltSubset -> bool) (s : t) : For_all Q s -> t := *)
(*   match s return For_all Q s -> t with *)
(*   | nil => (fun _ => nil) *)
(*   | x :: l => *)
(*     (fun for_all : For_all Q _ => *)

(*        (* Existantial version of t of type {t | In t (this (transitions sitpn))} *) *)
(*        let xe := exist Q x (for_all x (InA_cons_hd l (eq_refl x))) in *)

(*        (* Proof that for_all is valid on decreasing list. *)        *)
(*        if f xe then x :: filter_ Q f l (for_all_ind Q x l for_all) else filter_ Q f l (for_all_ind Q x l for_all)) *)
(*   end. *)


