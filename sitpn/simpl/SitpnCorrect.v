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

(* Import Sitpn material. *)

Require Import simpl.Sitpn.
Require Import simpl.SitpnTokenPlayer.
Require Import simpl.SitpnSemantics.

(* Import falling edge correctness lemmas. *)

Require Import simpl.SitpnFallingEdgeCorrect.
Require Import simpl.SitpnFallingEdgeWellDef.

(* Import rising edge correctness lemmas. *)

Require Import simpl.SitpnRisingEdgeCorrect.

(** * Correctness theorem for SITPN token player program. *)

Theorem sitpn_cycle_correct :
  forall (sitpn : Sitpn)
         (s s' s'' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_cycle sitpn s time_value env = Some (s', s'') ->
    SitpnSemantics sitpn s s' time_value env falling_edge /\
    SitpnSemantics sitpn s' s'' time_value env rising_edge.
Proof.
  intros sitpn s s' s'' time_value env Hwell_def_sitpn Hwell_def_s Hfun.
  functional induction (sitpn_cycle sitpn s time_value env) using sitpn_cycle_ind.
  
  (* GENERAL CASE, all went well. *)
  - injection Hfun as Heq_s' Heq_s''.
    split.
    
    (* CASE falling edge correct. *)
    + rewrite <- Heq_s'.
      apply (sitpn_falling_edge_correct sitpn s s'0 time_value env
                                        Hwell_def_sitpn Hwell_def_s e).
      
    (* CASE rising edge correct. *)
    + specialize (sitpn_falling_edge_well_def_state
                    sitpn s s'0 time_value env Hwell_def_sitpn Hwell_def_s e)
        as Hwell_def_s'.
      rewrite <- Heq_s', <- Heq_s''.
      apply (sitpn_rising_edge_correct
               sitpn s'0 s''0 time_value env Hwell_def_sitpn Hwell_def_s' e0).
      
  (* ERROR CASE. *)
  - inversion Hfun.
    
  (* ERROR CASE. *)
  - inversion Hfun.
Qed.
