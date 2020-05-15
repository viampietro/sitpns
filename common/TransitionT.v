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

(** * The type of Petri net transitions (transition_t). *)

(** Defines the type of Petri net transitions. *)

Inductive transition_t : Type := not_temporal | temporal_a_b |
                                 temporal_a_a | temporal_a_inf.

(** Implements the equality between two transition_t values. *)

Definition eqb (t t' : transition_t) : bool :=
  match t, t' with
  | not_temporal, not_temporal => true
  | temporal_a_b, temporal_a_b => true
  | temporal_a_a, temporal_a_a => true
  | temporal_a_inf, temporal_a_inf => true
  | _, _ => false
  end.
