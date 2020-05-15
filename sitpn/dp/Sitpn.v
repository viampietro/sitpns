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

(** * Sitpn and Sitpn state definitions. *)

Require Import Coqlib.
Require Import GlobalTypes.
Require Import NatSet.
Require Import SitpnTypes.
Require Import Datatypes.

Import ListNotations.

Set Implicit Arguments.

(** ** Sitpn structure definition. *)

(** Defines the Sitpn structure as a record. *)

Record Sitpn  :=
  BuildSitpn {
      
      (* A PlaceSet object representing the finite set of places. *)
      places : NatSet.t;
                 
      (* A TransitionSet object representing the finite set of transitions. *)
      transitions : NatSet.t;
      
      (* Alias for the set of elements that belong to the finite set [places]. *)
      InP := (fun p => In p (NatSet.this places));
      P := { p | InP p };
      
      (* Alias for the set of elements that belong to the finite set [transitions]. *)
      InT := (fun t => In t (NatSet.this transitions));
      T := { t | InT t };

      (* Given a place p ∈ P and t ∈ T:

         Yields a couple (a, n) where a is the type of the input arc
         between p and t, and n is the weight of the arc (therefore,
         strictly more than zero).
         
         Yields None if there is no arc between p and t.
         
       *)
      pre : P -> T -> option (ArcT * natstar);
      
      (* The function associating a weight to transition-place edges. *)
      post : T -> P -> option natstar;

      (* The initial marking of the SITPN. *)
      M0 : P -> nat;

      (* Associates a static time interval to certain transitions 
       * of the SITPN.
       *
       * For a given sitpn : Sitpn, and a transition t : Trans, 
       * Is sitpn t = None if no time interval
       * is associated with t in sitpn. *)
      Is : T -> option StaticTimeInterval;

      (* Finite sets of conditions, actions and functions. *)
      conditions : NatSet.t;
      actions : NatSet.t;
      functions : NatSet.t;

      (* Aliases for the set of elements that belong to the finite set
         [conditions] (resp. [actions] and [functions]). *)
      InC := (fun c => In c (NatSet.this conditions));
      C := { c | InC c };
      
      InA := (fun a => In a (NatSet.this actions));
      A := { a | InA a };

      InF := (fun f => In f (NatSet.this functions));
      F := { f | InF f };
      
      (* The function associating conditions to transitions. *)
      has_C : T -> C -> MOneZeroOne; 

      (* The function associating actions to places. *)
      has_A : P -> A -> bool;

      (* The function associating interpretation functions to
         transitions. *)
      has_F : T -> F -> bool;

      (* Priority relation between transitions. *)

      pr : T -> T -> bool;
      
    }.

(** Notations for Sitpn. *)

Notation "a '>~' b" := (pr a b) (at level 0).

(** ** Subsets of P and T, and misc. casting functions. *)

Definition Psubset sitpn Q := { p : P sitpn | Q p }.
Definition Psubset_in_P sitpn (Q : P sitpn -> Prop) (p : Psubset Q) := proj1_sig p.
Definition P_in_nat sitpn (p : P sitpn) : nat := proj1_sig p.
Definition nat_to_P {sitpn} p := (fun (pf : InP sitpn p) => exist _ p pf).

Definition Tsubset sitpn Q := { t : T sitpn | Q t }.
Definition Tsubset_in_T sitpn (Q : T sitpn -> Prop) (t : Tsubset Q) := proj1_sig t.
Definition T_in_nat sitpn (t : T sitpn) : nat := proj1_sig t.
Definition nat_to_T {sitpn} t := (fun (pf : InT sitpn t) => exist _ t pf).

Definition Ti (sitpn : Sitpn) := Tsubset (fun t : T sitpn => (Is t) <> None).
Definition Ti_in_T (sitpn : Sitpn) (t : Ti sitpn) := proj1_sig t.

Definition nat_to_C {sitpn} c := (fun (pf : InC sitpn c) => exist _ c pf).
Definition nat_to_A {sitpn} a := (fun (pf : InA sitpn a) => exist _ a pf).
Definition nat_to_F {sitpn} f := (fun (pf : InF sitpn f) => exist _ f pf).

(** Coercions for Sitpn. *)

Coercion P_in_nat : P >-> nat.
Coercion Psubset_in_P : Psubset >-> P.
Coercion Tsubset_in_T : Tsubset >-> T.
Coercion Ti_in_T : Ti >-> T. 
Coercion T_in_nat : T >-> nat.

(** Macro functions for Sitpn. *)

Definition P2List (sitpn : Sitpn) : list nat := NatSet.this (places sitpn).
Definition T2List (sitpn : Sitpn) : list nat := NatSet.this (transitions sitpn).
Definition C2List (sitpn : Sitpn) : list nat := NatSet.this (conditions sitpn).
Definition A2List (sitpn : Sitpn) : list nat := NatSet.this (actions sitpn).
Definition F2List (sitpn : Sitpn) : list nat := NatSet.this (functions sitpn).

(** ** Sitpn state definition. *)

(** Defines the Sitpn state structure as a record. *)

Record SitpnState (sitpn : Sitpn) :=
  BuildSitpnState {

      (* Fired set: transitions to be fired on falling edge, 
         and transitions that have been fired on rising edge.
       *)
      
      Fired : T sitpn -> Prop;
      
      (* Current marking of the Sitpn. *)
      
      M : P sitpn -> nat;

      (* Current state of time intervals. *)
      
      I : Ti sitpn -> DynamicTimeInterval;

      (* - On falling edge: orders to reset time counters at this
           cycle.  
         - On rising edge: orders to reset time counters at the
           next cycle. *)
      
      reset : Ti sitpn -> bool;

      (* Current condition (boolean) values. *)
      
      cond : C sitpn -> bool;

      (* Current activation state for continuous actions. *)
      
      exa : A sitpn -> bool;

      (* Current activation state for interpretation functions. *)
      
      exf : F sitpn -> bool;
    }.

