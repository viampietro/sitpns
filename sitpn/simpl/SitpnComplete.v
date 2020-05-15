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

(* Import falling edge and rising edge completeness lemmas. *)

Require Import simpl.SitpnFallingEdgeComplete.
Require Import simpl.SitpnRisingEdgeComplete.

(* Import lemmas on SITPN and states well-definition. *)

Require Import simpl.SitpnFallingEdgeWellDef.

(** * Completeness proof between [sitpn_cycle] and [SitpnSemantics]. *)

Theorem sitpn_cycle_complete :
  forall (sitpn : Sitpn)
         (s s' s'' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    IsWellDefinedSitpnState sitpn s'' ->
    SitpnSemantics sitpn s s' time_value env falling_edge ->
    SitpnSemantics sitpn s' s'' time_value env rising_edge ->
    exists (istate fstate : SitpnState),
      sitpn_cycle sitpn s time_value env = Some (istate, fstate) /\
      sitpn_state_eq s' istate /\
      sitpn_state_eq s'' fstate.
Proof.
  intros sitpn s s' s'' t env
         Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hwell_def_s''
         Hfall_spec Hrising_spec.

  (* Let's dig the function!! *)
  unfold sitpn_cycle.

  (* Specializes sitpn_falling_edge_complete then rewrites the goal *)

  specialize (sitpn_falling_edge_complete
                sitpn s s' t env Hwell_def_sitpn
                Hwell_def_s Hwell_def_s' Hfall_spec)
    as Hex_fall_fun.
  inversion_clear Hex_fall_fun as (istate & Hw_fall_fun).
  inversion_clear Hw_fall_fun as (Hfall_fun & Hsteq_s'_istate).
  rewrite Hfall_fun.
  
  (* Specializes sitpn_rising_edge_complete then rewrites the goal. *)

  specialize (sitpn_rising_edge_complete
                sitpn s' s'' t env istate
                Hwell_def_sitpn Hwell_def_s' Hwell_def_s'' Hrising_spec Hsteq_s'_istate)
    as Hex_rising_fun.
  inversion_clear Hex_rising_fun as (fstate & Hw_rising_fun).
  inversion_clear Hw_rising_fun as (Hrising_fun & Hsteq_s''_fs).
  
  (* Instantiates states and completes the proof. *)
  rewrite Hrising_fun.
  exists istate, fstate.
  apply (conj (eq_refl (Some (istate, fstate))) (conj Hsteq_s'_istate Hsteq_s''_fs)).
Qed.
