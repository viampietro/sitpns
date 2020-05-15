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

(** * Well-definition predicate for the Sitpn Structure. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import NatSet.
Require Import dp.Sitpn.
Require Import dp.SitpnFacts.

Set Implicit Arguments.

(** States that a given place [p] of [sitpn] is isolated.  *)

Definition PlaceIsIsolated (sitpn : Sitpn) (p : P sitpn) : Prop :=
  forall t, pre p t = None /\ post t p = None.

(** States that [sitpn] has no isolated place. *)

Definition HasNoIsolatedPlace (sitpn : Sitpn) : Prop :=
  forall (p : P sitpn), ~PlaceIsIsolated p.

(** States that a given transition [t] of [sitpn] is isolated.  *)

Definition TransitionIsIsolated (sitpn : Sitpn) (t : T sitpn) : Prop :=
  forall p, pre p t = None /\ post t p = None.

(** States that [sitpn] has no isolated transition. *)

Definition HasNoIsolatedTransition (sitpn : Sitpn) : Prop :=
  forall (t : T sitpn), ~TransitionIsIsolated t.

(** ** Priority relation as a strict total order for conflict groups. *)

(** States that two transition are in conflict through a group of
    places. *)

Inductive AreInConflictThroughPlaces sitpn (t t' : T sitpn) : list (P sitpn) -> Prop :=
| AreInCTPCommonPlace :
    forall p,
      pre p t <> None ->
      pre p t' <> None ->
      AreInConflictThroughPlaces t t' [p]
| AreInCTPTrans :
    forall Pc Pc' t'',
      AreInConflictThroughPlaces t t'' Pc ->
      AreInConflictThroughPlaces t'' t' Pc' ->
      AreInConflictThroughPlaces t t' (Pc ++ Pc').

(** Priority relation between two transitions that are elements
    of a subset of T. *)

Definition pr' sitpn (Q : T sitpn -> Prop) (t t' : Tsubset Q) : bool :=
  pr (proj1_sig t) (proj1_sig t').

(** States that a group of transitions is a conflict group. *)

Definition IsConflictGroup sitpn (Tc : list (T sitpn)) : Prop :=
  exists Pc : list (P sitpn),
    let InPc := (fun pc => List.In pc Pc) in
    let InTc := (fun tc => List.In tc Tc) in
    (forall p : Psubset InPc, forall t, pre p t <> None -> List.In t Tc)
    /\ (forall t : Tsubset InTc, forall p, pre p t <> None -> List.In p Pc)
    /\ (forall t t' : Tsubset InTc, ~Teq t t' -> AreInConflictThroughPlaces t t' Pc).

(** States that the priority relation of a given [sitpn] is
    well-defined, that is, the priority relation is a strict total
    order over the elements of each conflict group of transitions. *)

Definition PriorityRelIsWellDefined (sitpn : Sitpn) : Prop :=
  forall Tc : list (T sitpn),
    IsConflictGroup Tc ->
    let InTc := (fun tc => List.In tc Tc) in
    @IsStrictTotalOrderBRel (Tsubset InTc) (@Teq' sitpn InTc) (@Teq'_dec sitpn InTc) (@pr' sitpn InTc).

(** Defines a predicate stating that an Sitpn is well-defined, that is: 

    - The set of places and transitions of the Sitpn must not be empty.
    - There are no isolated (unconnected) place or transition.
    - The priority relation is a strict _total_ order over the group
      of transitions in structural conflict.
 *)

Definition IsWellDefined (sitpn : Sitpn) :=
  ~NatSet.Empty (places sitpn)
  /\ ~NatSet.Empty (transitions sitpn)
  /\ HasNoIsolatedPlace sitpn
  /\ HasNoIsolatedTransition sitpn
  /\ PriorityRelIsWellDefined sitpn.

