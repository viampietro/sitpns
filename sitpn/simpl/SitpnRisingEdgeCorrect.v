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

(* Import lemmas about well-definition. *)

Require Import simpl.SitpnRisingEdgeWellDef.
Require Import simpl.SitpnWellDefFired.
Require Import simpl.SitpnWellDefInterpretation.

(* Import lemmas about marking, time and interpretation. *)

Require Import simpl.SitpnRisingEdgeMarking.
Require Import simpl.SitpnRisingEdgeTime.
Require Import simpl.SitpnRisingEdgeInterpretation.

(** * Correctness of sitpn_rising_edge function. *)

Lemma sitpn_rising_edge_correct :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_rising_edge sitpn s = Some s' ->
    SitpnSemantics sitpn s s' time_value env rising_edge.
Proof.
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun.
  apply SitpnSemantics_rising_edge.

  (* CASE IsWellDefinedSitpn *)
  - assumption.

  (* CASE IsWellDefinedSitpnState sitpn s *)
  - assumption.

  (* CASE IsWellDefinedSitpnState sitpn s' *)
  - apply (sitpn_rising_edge_well_def_state
             sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE fired s = fired s' *)
  - apply (sitpn_rising_edge_same_fired sitpn s s' Hfun).

  (* CASE M' = M - pre + post *)
  - apply (sitpn_rising_edge_sub_pre_add_post sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE not sens by transient ⇒ reset' = true *)
  - apply (sitpn_rising_edge_decide_reset sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE sens by transient ⇒ reset' = false *)
  - apply (sitpn_rising_edge_decide_no_reset sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE 0 ∈ I(t) ∧ t ∉ fired ⇒ I'(t) = ψ *)
  - apply (sitpn_rising_edge_decide_blocked sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE 0 ∉ I(t) ∨ t ∈ fired ⇒ I'(t) = I(t) *)
  - apply (sitpn_rising_edge_decide_not_blocked sitpn s s' Hwell_def_sitpn Hwell_def_s Hfun).

  (* CASE cond_values s = cond_values s' *)
  - apply (sitpn_rising_edge_same_condv sitpn s s' Hfun).

  (* CASE exec_a s = exec_a s' *)
  - apply (sitpn_rising_edge_same_actions sitpn s s' Hfun).

  (* CASE ∀f, ∃t ∈ T, F(t, f) = true ∧ t ∈ fired ⇒ ex'(f) = true *)
  - apply (sitpn_rising_edge_exec_fun sitpn s s' Hfun).

  (* CASE ∀f, ∀t ∈ T, F(t, f) = false ∨ t ∉ fired ⇒ ex'(f) = true *)
  - apply (sitpn_rising_edge_not_exec_fun sitpn s s' Hfun). 
Qed.
