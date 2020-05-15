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

(* Import classical prop. *)

Require Import Classical_Prop.

(** * Completeness of [get_function_states]. *)

Section GetFunctionStatesComplete.

  (** Correctness lemma for [is_executed]. *)
  
  Lemma is_executed_correct :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (f : IFunction),
      is_executed sitpn fired f = true ->
      (exists (t : Trans),
          In t fired /\ (has_function sitpn t f) = true).
  Proof.
    intros sitpn fired f;
      functional induction (is_executed sitpn fired f) using is_executed_ind;
      intros Hfun.

    (* BASE CASE, fired = [] *)
    - inversion Hfun.

    (* CASE has_function = true *)
    - exists t.
      split; [apply in_eq | assumption].

    (* CASE has_action = false *)
    - specialize (IHb Hfun).
      inversion_clear IHb as (t' & Hw).
      inversion_clear Hw as (Hin_t'_tl & Hhas_fun).
      exists t'.      
      split.

      (* Proves In t' (t :: tl) *)
      + apply in_cons; assumption.

      (* Proves has_fun t'. *)
      + assumption.
  Qed.

  Lemma not_is_executed_correct :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (f : IFunction),
      is_executed sitpn fired f = false ->
      (forall t : Trans, In t fired -> (has_function sitpn t f) = false).
  Proof.
    intros sitpn fired t;
      functional induction (is_executed sitpn fired t) using is_executed_ind;
      intros Hfun t' Hin_t'_fired.

    (* BASE CASE, fired = [] *)
    - inversion Hin_t'_fired.

    (* CASE has_function = true *)
    - inversion Hfun.

    (* CASE has_function = false *)
    - inversion Hin_t'_fired as [Heq_tt' | Hin_tl].

      (* Case t = t' *)
      + rewrite <- Heq_tt'; assumption.
        
      (* Case In t' tl *)
      + apply (IHb Hfun t' Hin_tl).
  Qed.
  
  (** Completeness lemma for [get_function_states]. *)
  
  Lemma get_function_states_complete :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env rising_edge ->

      forall (istate : SitpnState)
             (funs : list IFunction)
             (new_funs : list (IFunction * bool)),
        sitpn_state_eq s istate ->
        IsDecListCons funs (functions sitpn) ->
        Permutation ((fs new_funs) ++ funs) (fs (exec_f s')) ->
        incl new_funs (exec_f s') ->
        NoDup ((fs new_funs) ++ funs) ->
        Permutation (get_function_states sitpn istate funs new_funs) (exec_f s').
  Proof.
    intros sitpn s s' time_value env Hwell_def_sitpn
           Hwell_def_s Hwell_def_s' Hspec;
      induction funs;
      intros new_funs Hsteq_s_istate His_dec_list Hperm_app Hincl_newf Hnodup_app.

    (* BASE CASE, funs = []. *)
    - simpl.

      (* Proves Permutation new_funs (exec_f s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)

      (* Builds premises to apply [permutation_fs_permutation] *)

      (* Builds NoDup (fs new_funs) *)
      rewrite app_nil_r in Hnodup_app.

      (* Builds NoDup (fs (exec_f s')) *)
      explode_well_defined_sitpn_state Hwell_def_s'.
      explode_well_defined_sitpn.
      unfold NoDupFunctions in Hnodup_fun.
      rewrite Hwf_state_execf in Hnodup_fun.
      rename Hnodup_fun into Hnodup_fs_fun_s'.
      clear_well_defined_sitpn.
      clear_well_defined_sitpn_state.
      
      (* Builds Permutation (fs new_funs) (fs (exec_f s')) *)
      rewrite app_nil_r in Hperm_app.

      (* Applies [permutation_fs_permutation]. *)
      apply (permutation_fs_permutation
               new_funs (exec_f s')
               Hnodup_app Hnodup_fs_fun_s'
               Hincl_newf Hperm_app).

    (* INDUCTION CASE, a :: conds *)
    - simpl.

      (* Two cases for is_executed. *)
      case_eq (is_executed sitpn (fired istate) a).
      
      (* CASE is_executed = true *)
      
      + intros His_exec_true.
        
        specialize (IHfuns (new_funs ++ [(a, true)])).

        (* Strategy: apply IHfuns, then we need premises. *)

        (* Builds incl (new_acts ++ [(a, true)]) (exec_f s') 
           To do that, we need to show (a, true) ∈ (exec_f s') 
           using Hspec.
         *)
        assert (Hin_a_funs : In (a, true) (exec_f s')).
        {
          
          (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
          inversion Hspec.
          clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H11.
          rename H10 into His_exec.

          (* Gets In a (functions sitpn) *)
          deduce_in_from_is_dec_list_cons His_dec_list as Hin_a_funs.

          (* Gets ∃p, n,... *)
          assert (Hex_tfired_w_hasfun :
                    exists t : Trans, In t (fired s) /\ has_function sitpn t a = true).
          {
            specialize (is_executed_correct sitpn (fired istate) a His_exec_true)
              as Hex_fun.
            inversion_clear Hex_fun as (t & Hw).
            specialize (proj1 (proj2 Hsteq_s_istate)) as Hperm_fired.
            rewrite <- Hperm_fired in Hw.
            exists t; assumption.
          }

          apply (His_exec a Hin_a_funs Hex_tfired_w_hasfun).
        }

        (* Then, we can deduce incl (new_funs ++ [(a, true)]) (exec_f s') *)
        assert (Hincl_newf_app : incl (new_funs ++ [(a, true)]) (exec_f s')).
        {
          intros x Hin_app.
          apply in_app_or in Hin_app.
          inversion_clear Hin_app as [Hin_x_newf | Heq_x_a];
            [ apply (Hincl_newf x Hin_x_newf) |
              inversion_clear Heq_x_a as [Heq | Hin_nil];
              [ rewrite <- Heq; assumption |
                inversion Hin_nil
              ]
            ].
        }

        (* Builds IsDecListCons funs (functions sitpn) *)
        apply is_dec_list_cons_cons in His_dec_list.
        
        (* Builds Permutation and NoDup hyps by rewriting IH. *) 
        
        unfold fs in IHfuns.
        rewrite fst_split_app in IHfuns.
        simpl in IHfuns.
        rewrite <- app_assoc in IHfuns.

        (* Applies IHacts *)
        apply (IHfuns Hsteq_s_istate His_dec_list Hperm_app Hincl_newf_app Hnodup_app).

      (* CASE is_executed = false *)
        
      + intros His_exec_false.
        
        specialize (IHfuns (new_funs ++ [(a, false)])).

        (* Strategy: apply IHfuns, then we need premises. *)

        (* Builds incl (new_funs ++ [(a, false)]) (exec_f s') 
           To do that, we need to show (a, false) ∈ (exec_f s') 
           using Hspec.
         *)
        assert (Hnot_in_a_acts : In (a, false) (exec_f s')).
        {
          
          (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
          inversion Hspec.
          clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H9 H10.
          rename H11 into Hnot_exec.

          (* Gets In a (functions sitpn) *)
          deduce_in_from_is_dec_list_cons His_dec_list as Hin_a_funs.

          (* Gets ∀p, n,... *)
          assert (Hnexec : forall t : Trans, ~In t (fired s) \/ has_function sitpn t a = false).
          {
            specialize (not_is_executed_correct sitpn (fired istate) a His_exec_false)
              as Hnexec.
            intros t.
            specialize (Hnexec t).
            apply imply_to_or in Hnexec.
            specialize (proj1 (proj2 Hsteq_s_istate)) as Hperm_fired.
            rewrite Hperm_fired.
            assumption.
          }
                    
          apply (Hnot_exec a Hin_a_funs Hnexec).
        }
        
        (* Then, we can deduce incl (new_funs ++ [(a, false)]) (exec_f s') *)
        assert (Hincl_newf_app : incl (new_funs ++ [(a, false)]) (exec_f s')).
        {
          intros x Hin_app.
          apply in_app_or in Hin_app.
          inversion_clear Hin_app as [Hin_x_newf | Heq_x_a];
            [ apply (Hincl_newf x Hin_x_newf) |
              inversion_clear Heq_x_a as [Heq | Hin_nil];
              [ rewrite <- Heq; assumption |
                inversion Hin_nil
              ]
            ].
        }

        (* Builds IsDecListCons funs (functions sitpn) *)
        apply is_dec_list_cons_cons in His_dec_list.
        
        (* Builds Permutation and NoDup hyps by rewriting IH. *) 
        
        unfold fs in IHfuns.
        rewrite fst_split_app in IHfuns.
        simpl in IHfuns.
        rewrite <- app_assoc in IHfuns.

        (* Applies IHfuns *)
        apply (IHfuns Hsteq_s_istate His_dec_list Hperm_app Hincl_newf_app Hnodup_app).
  Qed.
  
End GetFunctionStatesComplete.
