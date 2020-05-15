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
Require Import simpl.SitpnCoreLemmas.

(* Import Hilecop utils. *)





(* Import lemmas about interpretation. *)

Require Import simpl.SitpnFallingEdgeInterpretation.

(** * Completeness of [get_condition_values]. *)

Section GetCondValuesComplete.

  (** Completeness lemma for [get_condition_values]. *)
  
  Lemma get_condition_values_complete :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (conds : list Condition)
           (new_conds : list (Condition * bool)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->
      IsDecListCons conds (conditions sitpn) ->
      Permutation ((fs new_conds) ++ conds) (fs (cond_values s')) ->
      incl new_conds (cond_values s') ->
      NoDup ((fs new_conds) ++ conds) ->
      Permutation (get_condition_values conds time_value env new_conds) (cond_values s').
  Proof.
    intros sitpn s s' time_value env;
      induction conds;
      intros new_conds Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             His_dec_list Hperm_app Hincl_newc Hnodup_app.

    (* BASE CASE, conds = []. *)
    - simpl.

      (* Proves Permutation new_conds (cond_values s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)

      (* Builds premises to apply [permutation_fs_permutation] *)

      (* Builds NoDup (fs new_conds) *)
      rewrite app_nil_r in Hnodup_app.

      (* Builds NoDup (fs (d_intervals s')) *)
      explode_well_defined_sitpn_state Hwell_def_s'.
      explode_well_defined_sitpn.
      unfold NoDupConditions in Hnodup_cond.
      rewrite Hwf_state_condv in Hnodup_cond.
      rename Hnodup_cond into Hnodup_fs_condv_s'.
      clear_well_defined_sitpn.
      clear_well_defined_sitpn_state.
      
      (* Builds Permutation (fs new_conds) (fs (d_intervals s')) *)
      rewrite app_nil_r in Hperm_app.

      (* Applies [permutation_fs_permutation]. *)
      apply (permutation_fs_permutation
               new_conds (cond_values s')
               Hnodup_app Hnodup_fs_condv_s'
               Hincl_newc Hperm_app).

    (* INDUCTION CASE, a :: conds *)
    - simpl.
      specialize (IHconds (new_conds ++ [(a, env a time_value)])).

      (* Strategy: apply IHconds, then we need premises. *)

      (* Builds incl (new_conds ++ [(a, env a time_value)]) (cond_values s') 
         To do that, we need to show (a, env a time_value) ∈ (cond_values s') 
         using Hspec.
       *)
      assert (Hin_a_condvs' : In (a, env a time_value) (cond_values s')).
      {
        
        (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
        inversion Hspec.
        clear H H0 H1 H2 H3 H5 H6 H7 H8 H9 H10 H11 H12.
        rename H4 into Hcondv.

        (* Gets In a (conditions sitpn) *)
        deduce_in_from_is_dec_list_cons His_dec_list as Hin_a_conds.
        
        apply (Hcondv a Hin_a_conds).
      }
      
      (* Then, we can deduce incl (new_conds ++ [(a, env)]) (cond_values s') *)
      assert (Hincl_newc_app : incl (new_conds ++ [(a, env a time_value)]) (cond_values s')).
      {
        intros x Hin_app.
        apply in_app_or in Hin_app.
        inversion_clear Hin_app as [Hin_x_newc | Heq_x_a];
          [ apply (Hincl_newc x Hin_x_newc) |
            inversion_clear Heq_x_a as [Heq | Hin_nil];
            [ rewrite <- Heq; assumption |
              inversion Hin_nil
            ]
          ].
      }

      (* Builds IsDecListCons conds (conditions sitpn) *)
      apply is_dec_list_cons_cons in His_dec_list.
      
      (* Builds Permutation and NoDup hyps by rewriting IH. *) 
            
      unfold fs in IHconds.
      rewrite fst_split_app in IHconds.
      simpl in IHconds.
      rewrite <- app_assoc in IHconds.

      (* Applies IHconds *)
      apply (IHconds Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                     His_dec_list Hperm_app Hincl_newc_app Hnodup_app).
  Qed.
  
End GetCondValuesComplete.


(** * Completeness of [get_action_states]. *)

Section GetActionStatesComplete.

  (** Correctness lemma for [is_activated]. *)
  
  Lemma is_activated_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (a : Action),
      is_activated sitpn marking a = true ->
      (exists (p : Place) (n : nat),
          In (p, n) marking /\ n > 0 /\ (has_action sitpn p a) = true).
  Proof.
    intros sitpn marking a;
      functional induction (is_activated sitpn marking a) using is_activated_ind;
      intros Hfun.

    (* BASE CASE, marking = [] *)
    - inversion Hfun.

    (* CASE has_action and n > 0 = true *)
    - exists p, n.
      repeat split.

      (* Proves In (p, n) ((p,n) :: tl) *)
      + apply in_eq.

      (* Proves n > 0 *)
      + apply andb_prop in e1.
        inversion_clear e1 as (Hhas_ac & Hgt_0_n).
        rewrite Nat.ltb_lt in Hgt_0_n.
        auto.

      (* Proves has_action = true *)
      + apply andb_prop in e1.
        inversion_clear e1 as (Hhas_ac & Hgt_0_n).
        assumption.

    (* CASE has_action and n > 0 = false *)
    - specialize (IHb Hfun).
      inversion_clear IHb as (pl & Hn).
      inversion_clear Hn as (nboftokens & Hw).
      exists pl, nboftokens.      
      repeat split.

      (* Proves In (pl, nboftokens) ((p,n) :: tl) *)
      + apply in_cons; apply proj1 in Hw; assumption.

      (* Proves n > 0 *)
      + apply proj2, proj1 in Hw; assumption.

      (* Proves has_action = true *)
      + apply proj2, proj2 in Hw; assumption.
  Qed.

  Lemma not_is_activated_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (a : Action),
      is_activated sitpn marking a = false ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> n = 0 \/ (has_action sitpn p a) = false.
  Proof.
    intros sitpn marking a;
      functional induction (is_activated sitpn marking a) using is_activated_ind;
      intros Hfun pl nb Hin_m.

    (* BASE CASE, marking = [] *)
    - inversion Hin_m.

    (* CASE has_action && n > 0 = true *)
    - inversion Hfun.

    (* CASE has_action && n > 0 = false *)
    - specialize (IHb Hfun).
      inversion_clear Hin_m as [Heq_pn | Hin_tl].

      (* Case (pl, nb) = (p, n) *)
      + injection Heq_pn as Heq_p Heq_n.
        rewrite andb_false_iff in e1.
        inversion_clear e1 as [Hhas_act_false | Heq_n_0].
        -- right; rewrite <- Heq_p; assumption.
        -- rewrite Nat.ltb_ge in Heq_n_0; left.
           rewrite Nat.le_0_r in Heq_n_0.
           rewrite Heq_n in Heq_n_0; assumption.
           
      (* Case In (pl, nb) tl *)
      + apply (IHb pl nb Hin_tl).
  Qed.
  
  (** Completeness lemma for [get_action_states]. *)
  
  Lemma get_action_states_complete :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (acts : list Action)
           (new_acts : list (Action * bool)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->
      IsDecListCons acts (actions sitpn) ->
      Permutation ((fs new_acts) ++ acts) (fs (exec_a s')) ->
      incl new_acts (exec_a s') ->
      NoDup ((fs new_acts) ++ acts) ->
      Permutation (get_action_states sitpn s acts new_acts) (exec_a s').
  Proof.
    intros sitpn s s' time_value env;
      induction acts;
      intros new_acts Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             His_dec_list Hperm_app Hincl_newa Hnodup_app.

    (* BASE CASE, acts = []. *)
    - simpl.

      (* Proves Permutation new_acts (exec_a s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)

      (* Builds premises to apply [permutation_fs_permutation] *)

      (* Builds NoDup (fs new_conds) *)
      rewrite app_nil_r in Hnodup_app.

      (* Builds NoDup (fs (d_intervals s')) *)
      explode_well_defined_sitpn_state Hwell_def_s'.
      explode_well_defined_sitpn.
      unfold NoDupActions in Hnodup_ac.
      rewrite Hwf_state_execa in Hnodup_ac.
      rename Hnodup_ac into Hnodup_fs_ac_s'.
      clear_well_defined_sitpn.
      clear_well_defined_sitpn_state.
      
      (* Builds Permutation (fs new_acts) (fs (exec_a s')) *)
      rewrite app_nil_r in Hperm_app.

      (* Applies [permutation_fs_permutation]. *)
      apply (permutation_fs_permutation
               new_acts (exec_a s')
               Hnodup_app Hnodup_fs_ac_s'
               Hincl_newa Hperm_app).

    (* INDUCTION CASE, a :: conds *)
    - simpl.

      (* Two cases for is_activated. *)
      case_eq (is_activated sitpn (marking s) a).
      
      (* CASE is_activated = true *)
      + intros His_act_true.
        
        specialize (IHacts (new_acts ++ [(a, true)])).

        (* Strategy: apply IHacts, then we need premises. *)

        (* Builds incl (new_acts ++ [(a, true)]) (exec_a s') 
           To do that, we need to show (a, true) ∈ (exec_a s') 
           using Hspec.
         *)
        assert (Hin_a_acts : In (a, true) (exec_a s')).
        {
          
          (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
          inversion Hspec.
          clear H H0 H1 H2 H3 H4 H6 H7 H8 H9 H10 H11 H12 H13.
          rename H5 into Hact.

          (* Gets In a (conditions sitpn) *)
          deduce_in_from_is_dec_list_cons His_dec_list as Hin_a_acts.

          (* Gets ∃p, n,... *)
          specialize (is_activated_correct sitpn (marking s) a His_act_true)
            as Hex_act.
          apply (Hact a Hin_a_acts Hex_act).
        }
      
        (* Then, we can deduce incl (new_acts ++ [(a, true)]) (exec_a s') *)
        assert (Hincl_newa_app : incl (new_acts ++ [(a, true)]) (exec_a s')).
        {
          intros x Hin_app.
          apply in_app_or in Hin_app.
          inversion_clear Hin_app as [Hin_x_newa | Heq_x_a];
            [ apply (Hincl_newa x Hin_x_newa) |
              inversion_clear Heq_x_a as [Heq | Hin_nil];
              [ rewrite <- Heq; assumption |
                inversion Hin_nil
              ]
            ].
        }

        (* Builds IsDecListCons conds (conditions sitpn) *)
        apply is_dec_list_cons_cons in His_dec_list.
        
        (* Builds Permutation and NoDup hyps by rewriting IH. *) 
        
        unfold fs in IHacts.
        rewrite fst_split_app in IHacts.
        simpl in IHacts.
        rewrite <- app_assoc in IHacts.

        (* Applies IHacts *)
        apply (IHacts Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                      His_dec_list Hperm_app Hincl_newa_app Hnodup_app).

      (* CASE is_activated = false *)
      + intros His_act_false.
        
        specialize (IHacts (new_acts ++ [(a, false)])).

        (* Strategy: apply IHacts, then we need premises. *)

        (* Builds incl (new_acts ++ [(a, false)]) (exec_a s') 
           To do that, we need to show (a, false) ∈ (exec_a s') 
           using Hspec.
         *)
        assert (Hnot_in_a_acts : In (a, false) (exec_a s')).
        {
          
          (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
          inversion Hspec.
          clear H H0 H1 H2 H3 H4 H5 H7 H8 H9 H10 H11 H12 H13.
          rename H6 into Hnot_act.

          (* Gets In a (conditions sitpn) *)
          deduce_in_from_is_dec_list_cons His_dec_list as Hin_a_acts.

          (* Gets ∀p, n,... *)
          specialize (not_is_activated_correct sitpn (marking s) a His_act_false)
            as Hnact.
          apply (Hnot_act a Hin_a_acts Hnact).
        }
        
        (* Then, we can deduce incl (new_acts ++ [(a, false)]) (exec_a s') *)
        assert (Hincl_newa_app : incl (new_acts ++ [(a, false)]) (exec_a s')).
        {
          intros x Hin_app.
          apply in_app_or in Hin_app.
          inversion_clear Hin_app as [Hin_x_newa | Heq_x_a];
            [ apply (Hincl_newa x Hin_x_newa) |
              inversion_clear Heq_x_a as [Heq | Hin_nil];
              [ rewrite <- Heq; assumption |
                inversion Hin_nil
              ]
            ].
        }

        (* Builds IsDecListCons conds (conditions sitpn) *)
        apply is_dec_list_cons_cons in His_dec_list.
        
        (* Builds Permutation and NoDup hyps by rewriting IH. *) 
        
        unfold fs in IHacts.
        rewrite fst_split_app in IHacts.
        simpl in IHacts.
        rewrite <- app_assoc in IHacts.

        (* Applies IHacts *)
        apply (IHacts Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                      His_dec_list Hperm_app Hincl_newa_app Hnodup_app).
  Qed.
  
End GetActionStatesComplete.
