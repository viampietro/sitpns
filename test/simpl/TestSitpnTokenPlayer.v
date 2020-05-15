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

(* Import Sitpn types and token player functions. *)

Require Import simpl.Sitpn.
Require Import simpl.SitpnTokenPlayer.
Require Import simpl.SitpnSemantics.

(* Function returning the global condition values through time. *)

Definition env (c : Condition) (time_value : nat) : bool := negb (time_value mod 5 =? 0).

(** * Sitpn and SitpnState examples.  *)

(** Places and transitions sets. *)

Definition places1 := [ 0; 1; 12; 4; 5; 7; 2; 8; 9; 3; 10; 11 ].

Definition transs1 := [ 0; 12; 1; 9; 5; 13; 4; 14; 3; 6; 2; 8; 16 ].

(** Edge weights functions. *)

Definition pre1 (t : Trans) (p : Place) :=
  match (t, p) with
  | (0, 0)  | (0, 7)  | (0, 12)  | (1, 1)   | (2, 2)
  | (3, 3)  | (4, 4)  | (5, 5)   | (6, 8)   | (6, 9) 
  | (9, 11) | (12, 1) | (13, 11) | (14, 11) | (16, 3) | (16, 10) => 1
  | (8, 10) => 2
  | _ => 0
  end.

Definition post1 (t : Trans) (p : Place) :=
  match (t, p) with
  | (0, 4)  | (0, 5)  | (0, 12) | (1, 2) 
  | (2, 3)  | (3, 1)  | (4, 8)  | (5, 9) 
  | (6, 7)  | (6, 10) | (8, 11) | (12, 2) | (16, 3) | (16, 10) => 1
  | (13, 0) | (14, 0) | (9, 0) => 2
  | _ => 0
  end.

Definition test1 (t : Trans) (p : Place) :=
  match (t, p) with
  | (5, 2) => 1
  | (5, 12) => 1
  | _ => 0
  end.

Definition inhib1 (t : Trans) (p : Place) :=
  match (t, p) with
  | (2, 5) => 1
  | (4, 11) => 1
  | _ => 0
  end.

(** Initial marking. *)

Definition initial_marking1 (p : Place) :=
  match p with
  | 0 => 2
  | 1 => 1
  | 7 => 1
  | 12 => 1
  | _ => 0
  end.

(** Priority groups. *)

Definition pgroups1 := [ [1; 12]; [0; 2; 5];
                           [3; 8; 16]; [4; 9; 13; 14]; [6] ].

(** Static time intervals. *)

Definition s_intervals1 (t : Trans) : option TimeInterval :=
  match t with
  | 6 | 9 => Some {| min_t := 1; max_t := pos_val 2 |}
  | 4 => Some {| min_t := 2; max_t := pos_val 4 |}
  | _ => None
  end.

(** Conditions, actions and functions. *)

Definition conditions1 := [ 14; 2; 7 ].
Definition actions1 := [ 0; 1; 7; 12 ].
Definition functions1 := [ 0; 1; 2; 3 ].

Definition has_condition1 (t : Trans) (c : Condition) :=
  match (t, c) with
  | (2, 2) | (6, 7) | (3, 14) => true
  | _ => false
  end.

Definition has_action1 (p : Place) (a : Action) :=
  match (p, a) with
  | (0, 0) | (1, 1) | (7, 7) | (12, 12) => true
  | _ => false
  end.

Definition has_function1 (t : Trans) (f : IFunction) :=
  match (t, f) with
  | (0, 0) | (1, 1) | (2, 2) | (3, 3) => true
  | _ => false 
  end.

(** Neighbour places. *)

Definition lneighbours1 (t : Trans) : Neighbours :=
  match t with
  | 0  => mk_neighbours [0; 12; 7] [] [] [12; 5; 4]
  | 12 => mk_neighbours [1] [] [] [2]
  | 1  => mk_neighbours [1] [] [] [2]
  | 9  => mk_neighbours [11] [] [] [0]
  | 5  => mk_neighbours [5] [12; 2] [] [9]
  | 13 => mk_neighbours [11] [] [] [0]
  | 4  => mk_neighbours [4] [] [11] [8]
  | 14 => mk_neighbours [11] [] [] [0]
  | 3  => mk_neighbours [3] [] [] [1]
  | 6  => mk_neighbours [8; 9] [] [] [7; 10]
  | 2  => mk_neighbours [2] [] [5] [3]
  | 8  => mk_neighbours [10] [] [5] [11]
  | 16 => mk_neighbours [10; 3] [] [] [10; 3]
  | _ => mk_neighbours [] [] [] []
  end.

(** * Sitpn first example. *)

Definition sitpn1 :=
  mk_Sitpn places1 transs1 pre1 test1 inhib1 post1 initial_marking1
           pgroups1 s_intervals1 conditions1 actions1 functions1
           has_condition1 has_action1 has_function1 lneighbours1.



