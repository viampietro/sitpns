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

(* Import misc. lemmas and tactics. *)

Require Import simpl.SitpnCoreLemmas.
Require Import simpl.SitpnTactics.

(** * Lemmas about [sitpn_map_fire] and well-definition.  *)

(** ** Lemmas on [incl fired T]. *)

Section SitpnFallingEdgeInclFired.

  (** Under some hypotheses, all fired transitions returned by sitpn_fire_aux
      are included in [(transs sitpn)]. *)

  Lemma sitpn_fire_aux_incl_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      incl (fired ++ pg) sitpn.(transs) ->
      sitpn_fire_aux sitpn s residual_marking fired pg = Some to_be_fired ->
      incl to_be_fired (transs sitpn).
  Proof.
    intros sitpn s residual_marking fired pg;
      functional induction (sitpn_fire_aux sitpn s residual_marking fired pg)
                 using sitpn_fire_aux_ind;
      intros final_fired Hwell_def_sitpn Hincl_f_pg Hfun.
    
    (* BASE CASE *)
    - injection Hfun;
        intro Heq_fired;
        rewrite <- Heq_fired;
        rewrite <- app_nil_end in Hincl_f_pg; assumption.
      
    (* GENERAL CASE, the strategy is to apply the induction hypothesis. *)
    - rewrite <- app_assoc in IHo.
      apply (IHo final_fired Hwell_def_sitpn Hincl_f_pg Hfun).
      
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
      
    (* CASE is_sensitized = Some false, the strategy is to apply IH. *)
    (* First, builds incl (fired ++ tail) (transs sitpn) *)
    - apply incl_app_inv in Hincl_f_pg; elim Hincl_f_pg; intros Hincl_f Hincl_pg.
      apply incl_cons_inv in Hincl_pg.
      specialize (incl_app Hincl_f Hincl_pg) as Hincl_f_tail.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_sitpn Hincl_f_tail Hfun).
      
    (* ERROR CASE, is_sensitized returns None. *)
    - inversion Hfun.
      
    (* CASE sitpn_is_firable returns Some false. *)
    (* First, builds incl (fired ++ tail) (transs sitpn) *)
    - apply incl_app_inv in Hincl_f_pg; elim Hincl_f_pg; intros Hincl_f Hincl_pg.
      apply incl_cons_inv in Hincl_pg.
      specialize (incl_app Hincl_f Hincl_pg) as Hincl_f_tail.
      (* Applies IHo *)
      apply (IHo final_fired Hwell_def_sitpn Hincl_f_tail Hfun).
      
    (* ERROR CASE. *)
    - inversion Hfun.
      
  Qed.  
  
  (** Under some hypotheses, all fired transitions returned by sitpn_fire
      are included in [sitpn.(transs)]. *)
  
  Lemma sitpn_fire_incl_fired_transs :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (pgroup : list Trans)
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      In pgroup sitpn.(priority_groups) ->
      sitpn_fire sitpn s pgroup = Some to_be_fired ->
      incl to_be_fired sitpn.(transs).
  Proof.
    intros sitpn s pgroup to_be_fired Hwell_def_sitpn Hin_sitpn_pgs Hfun.
    unfold sitpn_fire in Hfun.

    (* Builds incl ([] ++ pgroup) (transs sitpn)) *)
    explode_well_defined_sitpn.
    unfold NoUnknownInPriorityGroups in *.
    assert (Hincl_pg_transs : incl pgroup (transs sitpn))
      by (intros t Hin_pgroup;
          specialize (in_concat t pgroup (priority_groups sitpn) Hin_pgroup Hin_sitpn_pgs)
            as Hin_concat_pgs;
          rewrite Hno_unk_pgroups; assumption).
    rewrite <- app_nil_l with (l := pgroup) in Hincl_pg_transs.
    
    (* Apply sitpn_fire_aux_incl_fired_transs *)
    apply (sitpn_fire_aux_incl_fired
             sitpn s (marking s) [] pgroup to_be_fired
             Hwell_def_sitpn Hincl_pg_transs Hfun).
  Qed.
  
  (** Under some hypotheses, all fired transitions returned by 
      [sitpn_map_fire_aux sitpn s fired pgroups] are included
      in the list of transitions [sitpn.(transs)]. *)
  
  Lemma sitpn_map_fire_aux_incl_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      incl pgroups sitpn.(priority_groups) ->
      incl fired sitpn.(transs) ->
      sitpn_map_fire_aux sitpn s fired pgroups = Some to_be_fired ->
      incl to_be_fired sitpn.(transs).
  Proof.
    intros sitpn s fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn s fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros to_be_fired Hwell_def_sitpn Hincl_pgs Hincl_fired Hfun.
    
    (* BASE CASE *)
    - injection Hfun; intro Heq_fired; rewrite <- Heq_fired; assumption.
      
    (* GENERAL CASE, applying induction hypothesis. *)
    - specialize (incl_cons_inv pgroup pgroups_tail (priority_groups sitpn) Hincl_pgs) as Hincl_pgs'.
      (* Builds incl (fired_transitions ++ fired_trs) (transs sitpn). 
         First, we need (incl fired_trs (transs sitpn)), then apply incl_app. *)
      assert (Hin_pgs_tail : In pgroup (pgroup :: pgroups_tail)) by apply in_eq.
      specialize (Hincl_pgs pgroup Hin_pgs_tail) as Hin_sitpn_pgs.
      specialize (sitpn_fire_incl_fired_transs
                    sitpn s pgroup fired_trs Hwell_def_sitpn
                    Hin_sitpn_pgs e0) as Hincl_fired'.
      specialize (incl_app Hincl_fired Hincl_fired') as Hincl_app.
      apply (IHo to_be_fired Hwell_def_sitpn Hincl_pgs' Hincl_app Hfun).
      
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [sitpn_map_fire] returns a list of transitions to be fired 
    included in T. *)
  
  Lemma sitpn_map_fire_incl_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      sitpn_map_fire sitpn s = Some to_be_fired ->
      incl to_be_fired (transs sitpn).
  Proof.
    intros sitpn s to_be_fired Hwell_def_sitpn Hfun.
    unfold sitpn_map_fire in Hfun.

    (* Builds incl (priority_groups sitpn) (priority_groups sitpn) *)
    assert (incl (priority_groups sitpn) (priority_groups sitpn))
      as Hincl_pgs by (apply incl_refl). 
    
    (* Builds incl [] (transs sitpn) *)
    assert (incl [] (transs sitpn))
      as Hincl_nil by (intros x Hnil; inversion Hnil).

    (* Applies sitpn_map_fire_aux_incl_fired. *)
    apply (sitpn_map_fire_aux_incl_fired
             sitpn s [] (priority_groups sitpn) to_be_fired
             Hwell_def_sitpn Hincl_pgs Hincl_nil Hfun).
  Qed.

  (** [sitpn_falling_edge] produces a state having a list
    of fired transitions included in T. *)

  Lemma sitpn_falling_edge_incl_fired :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      IsWellDefinedSitpn sitpn ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      incl (fired s') (transs sitpn).
  Proof.
    intros sitpn s s' time_value env Hwell_def_sitpn Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.
    injection Hfun as Heq_s'.

    (* GENERAL CASE, all went well. *)
    - rewrite <- Heq_s'; simpl.
      set (tmp_state := {|
                         fired := [];
                         marking := marking s;
                         d_intervals := d_intervals';
                         reset := reset s;
                         cond_values := get_condition_values (conditions sitpn) time_value env [];
                         exec_a := get_action_states sitpn s (actions sitpn) [];
                         exec_f := exec_f s |}) in e0.
      apply (sitpn_map_fire_incl_fired sitpn tmp_state trs_2b_fired Hwell_def_sitpn e0).

    (* Error case. *)
    - inversion Hfun.

    (* Error case. *)
    - inversion Hfun.
  Qed.
  
End SitpnFallingEdgeInclFired.

(** ** Lemmas on [NoDup fired]. *)

Section SitpnFallingEdgeNoDupFired.

  (** Under some hypotheses, the list of fired transitions returned by
      [sitpn_fire_aux sitpn s pgroup] contains no duplicate and is
      included in [pgroup]. *)

  Lemma sitpn_fire_aux_nodup_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      NoDup (fired ++ pg) ->
      sitpn_fire_aux sitpn s residual_marking fired pg = Some to_be_fired ->
      NoDup to_be_fired /\ incl to_be_fired (fired ++ pg). 
  Proof.
    intros sitpn s residual_marking fired pg to_be_fired;
      functional induction (sitpn_fire_aux sitpn s residual_marking fired pg)
                 using sitpn_fire_aux_ind;
      intros Hwell_def_sitpn Hnodup_app Hfun.
    
    (* BASE CASE, pg = [] *)
    - rewrite <- app_nil_end in Hnodup_app.
      assert (Hincl_refl : incl to_be_fired to_be_fired) by apply incl_refl.
      rewrite <- app_nil_end.
      injection Hfun; intros Heq; rewrite Heq in *.
      apply (conj Hnodup_app Hincl_refl).
      
    (* GENERAL CASE *)
    - rewrite <- app_assoc in IHo.
      apply (IHo Hwell_def_sitpn Hnodup_app Hfun).
      
    (* ERROR CASE, update_residual_marking returns None *)
    - inversion Hfun.
      
    (* CASE is_sensitized = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo Hwell_def_sitpn Hnodup_app Hfun) as Hw.
      elim Hw; intros Hnodup_ff Hincl_ftail.
      split.
      + assumption.
      + intros a Hin_ff. specialize (Hincl_ftail a Hin_ff) as Hin_ftail.
        apply in_or_app.
        apply in_app_or in Hin_ftail; elim Hin_ftail; intro Hin.
        -- auto.
        -- apply in_cons with (a := t) in Hin; auto.
           
    (* ERROR CASE, is_sensitized = None *)
    - inversion Hfun.
      
    (* CASE sitpn_is_firable = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo Hwell_def_sitpn Hnodup_app Hfun) as Hw.
      elim Hw; intros Hnodup_ff Hincl_ftail.
      split.
      + assumption.
      + intros a Hin_ff. specialize (Hincl_ftail a Hin_ff) as Hin_ftail.
        apply in_or_app.
        apply in_app_or in Hin_ftail; elim Hin_ftail; intro Hin.
        -- auto.
        -- apply in_cons with (a := t) in Hin; auto.
           
    (* ERROR CASE, sitpn_is_firable returns None. *)
    - inversion Hfun.
  Qed.
  
  (** Under some hypotheses, the list of fired transitions returned by
      [sitpn_fire sitpn s pgroup] contains no duplicate and is
      included in [pgroup]. *)
  
  Lemma sitpn_fire_nodup_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      NoDup pgroup ->
      sitpn_fire sitpn s pgroup = Some fired ->
      NoDup fired /\ incl fired pgroup.
  Proof.
    intros sitpn s pgroup fired Hwell_def_sitpn Hnodup_pg Hfun.
    unfold sitpn_fire in Hfun.
    rewrite <- app_nil_l in Hnodup_pg.
    apply (sitpn_fire_aux_nodup_fired
             sitpn s (marking s) [] pgroup fired
             Hwell_def_sitpn Hnodup_pg Hfun).
  Qed.
  
  (** Under some hypotheses, the list of fired transitions returned by
      [sitpn_map_fire_aux sitpn s fired pgroups] contains no
      duplicates. *)
  
  Lemma sitpn_map_fire_aux_nodup_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      NoDup (fired ++ (concat pgroups)) ->
      sitpn_map_fire_aux sitpn s fired pgroups = Some to_be_fired ->
      NoDup to_be_fired.
  Proof.
    intros sitpn s fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn s fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros to_be_fired Hwell_def_sitpn Hnodup_fired_pgs Hfun.
    
    (* BASE CASE, pgroups = []. *)
    - simpl in Hnodup_fired_pgs;
        rewrite <- app_nil_end with (l := fired_transitions) in Hnodup_fired_pgs.
      injection Hfun; intros Heq_fired; rewrite <- Heq_fired; assumption.
      
    (* GENERAL CASE *)
    (* Builds (NoDup pgroup) to apply sitpn_fire_nodup_fired. *)
    - rewrite concat_cons in Hnodup_fired_pgs.
      specialize (nodup_app fired_transitions (pgroup ++ concat pgroups_tail) Hnodup_fired_pgs)
        as Hnodup_fpgs_wedge.
      elim Hnodup_fpgs_wedge; intros Hnodup_fired Hnodup_pg.
      apply nodup_app in Hnodup_pg; apply proj1 in Hnodup_pg. 
      specialize (sitpn_fire_nodup_fired sitpn s pgroup fired_trs Hwell_def_sitpn
                                         Hnodup_pg e0) as Hnodup_f_w_incl.
      (* Applies nodup_app_incl to get 
         NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail) *)
      elim Hnodup_f_w_incl; intros Hnodup_ftrs Hincl_fpg.
      specialize (nodup_app_incl fired_transitions pgroup (concat pgroups_tail) fired_trs
                                 Hnodup_fired_pgs Hnodup_ftrs Hincl_fpg)
        as Hnodup_ff_concat.
      rewrite app_assoc in Hnodup_ff_concat.
      (* Applies IHo *)
      apply (IHo to_be_fired Hwell_def_sitpn Hnodup_ff_concat Hfun).
      
    (* CASE sitpn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** Under some hypotheses, the list of fired transitions returned by
      [sitpn_map_fire sitpn s] contains no duplicates. *)
  
  Lemma sitpn_map_fire_nodup_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      sitpn_map_fire sitpn s = Some to_be_fired ->
      NoDup to_be_fired.
  Proof.
    intros sitpn s to_be_fired Hwell_def_sitpn Hfun.
    unfold sitpn_map_fire in Hfun.

    (* Builds NoDup ([] ++ concat (priority_groups sitpn)) *)
    assert (NoDup ([] ++ concat (priority_groups sitpn))) as Hnodup_concat.
    {
      simpl.
      explode_well_defined_sitpn.
      unfold NoDupTranss in Hnodup_transs.
      unfold NoUnknownInPriorityGroups in Hno_unk_pgroups.
      rewrite Hno_unk_pgroups in Hnodup_transs.
      assumption.
    }
    
    (* Applies sitpn_map_fire_aux_nodup_fired. *)
    apply (sitpn_map_fire_aux_nodup_fired
             sitpn s [] (priority_groups sitpn) to_be_fired
             Hwell_def_sitpn Hnodup_concat Hfun).
  Qed.
  
  (** [sitpn_falling_edge] produces a state having a list
      of fired transitions with no duplicates. *)

  Lemma sitpn_falling_edge_nodup_fired :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      IsWellDefinedSitpn sitpn ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      NoDup (fired s').
  Proof.
    intros sitpn s s' time_value env Hwell_def_sitpn Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.
    injection Hfun as Heq_s'.

    (* GENERAL CASE, all went well. *)
    - rewrite <- Heq_s'; simpl.
      set (tmp_state := {|
                         fired := [];
                         marking := marking s;
                         d_intervals := d_intervals';
                         reset := reset s;
                         cond_values := get_condition_values (conditions sitpn) time_value env [];
                         exec_a := get_action_states sitpn s (actions sitpn) [];
                         exec_f := exec_f s |}) in e0.
      apply (sitpn_map_fire_nodup_fired sitpn tmp_state trs_2b_fired Hwell_def_sitpn e0).

    (* Error case. *)
    - inversion Hfun.

    (* Error case. *)
    - inversion Hfun.
  Qed.
  
End SitpnFallingEdgeNoDupFired.

(** * sitpn_rising_edge preserves the list of fired transitions. *)

Section SitpnRisingEdgeSameFired.

  Lemma sitpn_rising_edge_same_fired :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      sitpn_rising_edge sitpn s = Some s' ->
      (fired s) = (fired s').
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s)
                 using sitpn_rising_edge_ind;
      intros s' Hfun;

      (* GENERAL CASE, all went well. *)
      (injection Hfun as Hfun; rewrite <- Hfun; simpl; reflexivity)

      (* ERROR CASES. *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeSameFired.
