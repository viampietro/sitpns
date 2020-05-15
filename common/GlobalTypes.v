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

(** * Global type definitions. *)

Require Import Coqlib.
Require Import String.
Require Import Ascii.
Require Import HexString.

(** Type definitions used in all part of the Hilecop-Cert project. *)

(** Defines the set of strictly positive natural numbers. *)

Definition natstar := { n : nat | n > 0 }.

(** Casts a natstar into a nat. *)

Definition natstar_to_nat (ns : natstar) := proj1_sig ns.
Coercion natstar_to_nat : natstar >-> nat.

(** Defines some natstar. *)

Definition onens := exist _ 1 (gt_Sn_O 0).
Definition twons := exist _ 2 (gt_Sn_O 1).
Definition threens := exist _ 3 (gt_Sn_O 2).

(** Defines the type of relation that are a strict order 
    over a type A.
 *)

Inductive IsStrictOrderBRel {A} (brel : A -> A -> bool) : Prop :=
  MkStrictOrderB {
      brel_irrefl : forall a, brel a a = false;
      brel_trans : forall a b c, brel a b = true -> brel b c = true -> brel a c = true;

      (* Irreflexivity and transitivity entail anti-symmetry. *)
      (* brel_antisym : forall a b, brel a b = true -> brel b a = false; *)
    }.

(** States that two elements of type A are comparable through
    the boolean relation [brel]. *)

Definition AreComparableWithBRel {A} (x y : A) (brel : A -> A -> bool) : Prop :=
  brel x y <> false \/ brel y x <> false.

(** States that [brel] is a strict total order over a type A, that is:  
    - [brel] is a strict order over type A.
    - all elements of A that are different are comparable with [brel].
 *)

Definition IsStrictTotalOrderBRel {A}
           (eqA : A -> A -> Prop)
           (decEqA : forall x y, {eqA x y} + {~eqA x y})
           (brel : A -> A -> bool) :=
  IsStrictOrderBRel brel /\ forall x y, ~eqA x y -> AreComparableWithBRel x y brel.

(** Defines the type of Petri net arcs. *)

Inductive ArcT : Type := basic | test | inhibitor.

(** Implements the equality between two arc_t values. *)

Definition arct_eqb (a a' : ArcT) : bool :=
  match a, a' with
  | basic, basic => true
  | test, test => true
  | inhibitor, inhibitor => true
  | _, _ => false
  end.

(** Cast from ArcT to nat. *)

Definition ArcT_in_nat (a : ArcT) :=
  match a with
  | basic => 0
  | test => 1
  | inhibitor => 2
  end.

Coercion ArcT_in_nat : ArcT >-> nat.

(** Defines the type of Petri net transitions. *)

Inductive TransitionT : Type := not_temporal | temporal_a_b |
                                temporal_a_a | temporal_a_inf.

(** Cast from TransitionT to nat. *)

Definition TransitionT_in_nat (t : TransitionT) :=
  match t with
  | not_temporal => 0
  | temporal_a_b => 1
  | temporal_a_a => 2
  | temporal_a_inf => 3
  end.

Coercion TransitionT_in_nat : TransitionT >-> nat.

(** Implements the equality between two transition_t values. *)

Definition transt_eqb (t t' : TransitionT) : bool :=
  match t, t' with
  | not_temporal, not_temporal => true
  | temporal_a_b, temporal_a_b => true
  | temporal_a_a, temporal_a_a => true
  | temporal_a_inf, temporal_a_inf => true
  | _, _ => false
  end.

(** Defines an option type able to return error messages. *)

Inductive optionE (A : Type) : Type :=
| Success : A -> optionE A
| Err : string -> optionE A.

Arguments Success {A} a.
Arguments Err {A}.

(** Converts a nat into its hexadecimal string representation. Useful
    to display variable values in error messages.  *)

Notation "$$ n" := (of_nat n) (at level 0, only parsing).
