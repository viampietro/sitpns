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

(* Import Sitpn core material. *)

Require Import simpl.Sitpn.
Require Import simpl.SitpnTokenPlayer.
Require Import simpl.SitpnSemantics.
Require Import simpl.SitpnTactics.

(* Import misc. lemmas, tactics and definitions. *)



(* Import lemmas about time, fired and interpretation. *)

Require Import simpl.SitpnFallingEdgeTimeComplete.
Require Import simpl.SitpnFallingEdgeFiredComplete.
Require Import simpl.SitpnFallingEdgeInterpretationComplete.

(** * Completeness of [sitpn_falling_edge]. *)

Lemma sitpn_falling_edge_complete :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    SitpnSemantics sitpn s s' time_value env falling_edge ->
    exists istate : SitpnState,
      sitpn_falling_edge sitpn s time_value env = Some istate /\
      sitpn_state_eq s' istate.
Proof.
  intros sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s
         Hwell_def_s' Hspec.

  (* Digs the function sitpn_falling_edge. *)
  unfold sitpn_falling_edge.

  (* Specializes update_time_intervals_complete, and
     rewrites the goal. 
     
     To do so, we have to build some premises. *)
  
  assert (His_dec_ditvals : IsDecListCons (d_intervals s) (d_intervals s)) by (apply IsDecListCons_refl).
  assert (Hperm_ds_ds' : Permutation (fs ([] ++ (d_intervals s))) (fs (d_intervals s'))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn_state Hwell_def_s.
    explode_well_defined_sitpn_state Hwell_def_s'.

    assert (Hequiv_ditvals : forall t : Trans, In t (fs (d_intervals s)) <-> In t (fs (d_intervals s'))).
    {
      intros t; split;
        [
          intros Hin_ditvals;
          rewrite <- (Hwf_state_ditvals t) in Hin_ditvals;
          rewrite Hwf_state_ditvals0 in Hin_ditvals;
          assumption |
          intros Hin_ditvals;
          rewrite <- Hwf_state_ditvals0 in Hin_ditvals;
          rewrite (Hwf_state_ditvals t) in Hin_ditvals;
          assumption
        ].
    }

    apply (NoDup_Permutation Hnodup_state_ditvals Hnodup_state_ditvals0 Hequiv_ditvals).
  }
  assert (Hincl_nil : incl [] (d_intervals s')) by (intros a Hin_nil; inversion Hin_nil).
  assert (Hnodup_app_nil : NoDup (fs ([] ++ (d_intervals s)))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn_state Hwell_def_s.
    assumption.
  }
  
  specialize (update_time_intervals_complete
                sitpn s s' time_value env (d_intervals s) []
                Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                His_dec_ditvals Hperm_ds_ds' Hincl_nil Hnodup_app_nil)
    as Hex_update_t_itvals.
  inversion_clear Hex_update_t_itvals as (ditvals' & Hw_update_t_itvals).
  inversion_clear Hw_update_t_itvals as (Hupdate_t_itvals & Hperm_ditvals).
  rewrite Hupdate_t_itvals.

  (* Makes the goal more readable. *)
  set (tmp_state := {|
            fired := [];
            marking := marking s;
            d_intervals := ditvals';
            reset := reset s;
            cond_values := get_condition_values (conditions sitpn) time_value env [];
            exec_a := get_action_states sitpn s (actions sitpn) [];
            exec_f := exec_f s |}).

  (* Specializes get_condition_values_complete, to get the hypothesis: 
     Permutation (cond_values tmp_state) (cond_values s').

     Necessary to prove sitpn_state_eq s' istate and to 
     specialize sitpn_map_fire_complete.  
   *)
  
  assert (His_dec_conds : IsDecListCons (conditions sitpn) (conditions sitpn)) by (apply IsDecListCons_refl).
  assert (Hperm_conds_cs' : Permutation ((@fs Condition bool []) ++ (conditions sitpn)) (fs (cond_values s'))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn_state Hwell_def_s'.
    rewrite Hwf_state_condv.
    auto.
  }
  assert (Hincl_nil_condv : incl [] (cond_values s')) by (intros a Hin_nil; inversion Hin_nil).
  assert (Hnodup_app_nil_conds : NoDup ((@fs Condition bool []) ++ (conditions sitpn))).
  {
    rewrite app_nil_l.
    explode_well_defined_sitpn.
    assumption.
  }

  specialize (get_condition_values_complete
                sitpn s s' time_value env (conditions sitpn) []
                Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                His_dec_conds Hperm_conds_cs' Hincl_nil_condv Hnodup_app_nil_conds)
    as Hperm_condv.

  (* Specializes sitpn_map_fire_complete (and builds hypotheses to do so). *)
  
  assert (Heq_m_tmp : marking tmp_state = marking s)
    by (simpl; reflexivity).

  specialize (@sitpn_map_fire_complete sitpn s s' time_value env tmp_state
                                       Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                                       Heq_m_tmp Hperm_ditvals Hperm_condv)
    as Hex_sitpn_map_fire.

  (* Explodes the sitpn_map_fire hypothesis, and rewrites the goal. *)
  inversion_clear Hex_sitpn_map_fire as (final_fired & Hsitpn_map_fire_w).
  inversion_clear Hsitpn_map_fire_w as (Hsitpn_map_fire & Hperm_ff).
  rewrite Hsitpn_map_fire.

  (* Instantiates istate. *)
  exists ({|
             fired := final_fired;
             marking := marking tmp_state;
             d_intervals := d_intervals tmp_state;
             reset := reset tmp_state;
             cond_values := cond_values tmp_state;
             exec_a := exec_a tmp_state;
             exec_f := exec_f tmp_state |}).

  (* Proves equality and relation sitpn_state_eq. *)
  split.

  (* Proves trivial equality. *)
  - reflexivity.

  (* Proves that sitpn_state_eq relation holds between s' and
     istate. *)
  - unfold sitpn_state_eq; repeat split; simpl.

    (* Permutation (marking s') (marking s)  *)
    + inversion Hspec; rewrite H2; reflexivity.

    (* Permutation (fired s') (fired istate) *)
    + symmetry; assumption.

    (* Permutation (d_intervals s') (d_intervals istate) *)
    + symmetry; assumption.
      
    (* Permutation (reset s') (reset istate) *)
    + inversion Hspec; rewrite H10; reflexivity.

    (* Permutation (cond_values s') (cond_values istate) *)
    + symmetry; assumption.

    (* Permutation (exec_a s') (exec_a istate) *)
    + symmetry.
      
      (* Specializes get_action_states_complete to solve the goal: 
         Permutation (get_action_states ...) (exec_a s'). *)
      
      assert (His_dec_acts : IsDecListCons (actions sitpn) (actions sitpn)) by (apply IsDecListCons_refl).
      assert (Hperm_acts_as' : Permutation ((@fs Action bool []) ++ (actions sitpn)) (fs (exec_a s'))).
      {
        rewrite app_nil_l.
        explode_well_defined_sitpn_state Hwell_def_s'.
        rewrite Hwf_state_execa.
        auto.
      }
      assert (Hincl_nil_acts : incl [] (exec_a s')) by (intros a Hin_nil; inversion Hin_nil).
      assert (Hnodup_app_nil_acts : NoDup ((@fs Action bool []) ++ (actions sitpn))).
      {
        rewrite app_nil_l.
        explode_well_defined_sitpn.
        assumption.
      }

      apply (get_action_states_complete
               sitpn s s' time_value env (actions sitpn) []
               Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
               His_dec_acts Hperm_acts_as' Hincl_nil_acts Hnodup_app_nil_acts).

    (* Permutation (exec_f s') (exec_f istate) *)
    + inversion Hspec; rewrite H3; reflexivity.
Qed.
