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

(* Import lemmas on well-definition. *)

Require Import simpl.SitpnWellDefFired.
Require Import simpl.SitpnWellDefTime.
Require Import simpl.SitpnWellDefInterpretation.
Require Import simpl.SitpnWellDefMarking.

(* Import Sitpn tactics. *)

Require Import simpl.SitpnTactics.

(** * sitpn_falling_edge and well-definedness of states. *)

  
(** [sitpn_falling_edge] returns a SitpnState that is well-defined. *)

Lemma sitpn_falling_edge_well_def_state :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    sitpn_falling_edge sitpn s time_value env = Some s' ->
    IsWellDefinedSitpnState sitpn s'.
Proof.
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun.
  unfold IsWellDefinedSitpnState.
  
  (* CASE incl (fired s') (transs sitpn) *)
  split.
  apply (sitpn_falling_edge_incl_fired
           sitpn s s' time_value env Hwell_def_sitpn Hfun).

  (* CASE NoDup (fired s') *)
  split.
  apply (sitpn_falling_edge_nodup_fired
           sitpn s s' time_value env Hwell_def_sitpn Hfun).           

  (* CASE places = fst (split (marking s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_marking sitpn s s' time_value env Hfun) as Heq_m.
  rewrite <- Heq_m; assumption.

  (* CASE t ∈ (d_intervals s') ⇔ t ∈ Ti *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_ditvals sitpn s s' time_value env Hfun)
    as Heq_fs_ditvals.
  rewrite <- Heq_fs_ditvals; assumption.

  (* CASE NoDup (fst (split (d_intervals s'))) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_ditvals sitpn s s' time_value env Hfun)
    as Heq_fs_ditvals.
  rewrite <- Heq_fs_ditvals; assumption.

  (* CASE t ∈ (reset s') ⇔ t ∈ Ti *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_reset sitpn s s' time_value env Hfun)
    as Heq_reset.
  rewrite <- Heq_reset; assumption.

  (* CASE NoDup (fst (split (reset s'))) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_reset sitpn s s' time_value env Hfun)
    as Heq_reset.
  rewrite <- Heq_reset; assumption.

  (* CASE C = fst (split (cond_values s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_condv sitpn s time_value env s' Hfun)
    as Heq_fs_condv; assumption.
  
  (* CASE A = fst (split (exec_a s')) *)
  split.
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_struct_actions sitpn s time_value env s' Hfun)
    as Heq_fs_actions; assumption.

  (* CASE F = fst (split (exec_f s')) *)
  explode_well_defined_sitpn_state Hwell_def_s.
  specialize (sitpn_falling_edge_same_functions sitpn s time_value env s' Hfun) as Heq_execf.
  rewrite <- Heq_execf; assumption.
Qed.

(** If s and s' differ only on their fired field and
    s' has an empty fired field and
    s is well-defined then s' is well-defined. *)

Lemma is_well_def_tmp_state :
  forall (sitpn : Sitpn)
         (s s' : SitpnState),
    (fired s') = [] ->
    (marking s) = (marking s') ->
    (d_intervals s) = (d_intervals s') ->
    (reset s) = (reset s') ->
    (cond_values s) = (cond_values s') ->
    (exec_a s) = (exec_a s') ->
    (exec_f s) = (exec_f s') ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s'.
Proof.
  intros sitpn s s' Hfired_nil Heq_m Heq_ditvals Heq_reset Heq_condv
         Heq_execa Heq_execf Hwell_def_s.

  (* Unfolds definition in goal and rewrites (fired s') with []. *)
  unfold IsWellDefinedSitpnState.
  rewrite Hfired_nil.

  (* Deals with incl [] (transs sitpn) and NoDup []. *)
  split.

  intros a Hin_nil; inversion Hin_nil.
  split. apply NoDup_nil.

  (* Rewrites the goal, unfolds IsWellDefinedSitpnState in the context 
       and complete the subgoal. *)
  unfold IsWellDefinedSitpnState in Hwell_def_s;
    do 2 (apply proj2 in Hwell_def_s).
  rewrite <- Heq_m, <- Heq_ditvals, <- Heq_reset, <- Heq_condv, <- Heq_execa, <- Heq_execf.
  assumption.
Qed.    
