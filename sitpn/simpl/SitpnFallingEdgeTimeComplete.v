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






(** * Completeness of [update_time_intervals]. *)

Section UpdateTimeIntervalsComplete.

  (** Completeness lemma for [update_time_intervals]. *)

  Lemma update_time_intervals_complete :
    forall (sitpn : Sitpn)
           (s s': SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (ditvals new_ditvals : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->

      (* Hypotheses on ditvals and new_ditvals. *)
      IsDecListCons ditvals (d_intervals s) ->
      Permutation (fs (new_ditvals ++ ditvals)) (fs (d_intervals s')) ->
      incl new_ditvals (d_intervals s') ->
      NoDup (fs (new_ditvals ++ ditvals)) ->

      (* Conclusion. *)
      exists ditvals' : list (Trans * DynamicTimeInterval),
        update_time_intervals sitpn s ditvals new_ditvals = Some ditvals'
        /\ Permutation ditvals' (d_intervals s').
  Proof.
    intros sitpn s s' time_value env ditvals.
    induction ditvals;
      intros new_ditvals Hwell_def_sitpn Hwell_def_s Hwell_def_s'
             Hspec His_dec_list Hperm_app Hincl_newd Hnodup_fs_newd.

    (* BASE CASE, ditvals = []. *)
    - simpl; exists new_ditvals; split.

      (* Proves equality. *)
      + trivial.

      (* Proves Permutation new_ditvals (d_intervals s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)
      +
        (* Builds premises to apply [permutation_fs_permutation] *)

        (* Builds NoDup (fs new_ditvals) *)

        rewrite app_nil_r in Hnodup_fs_newd.

        (* Builds NoDup (fs (d_intervals s')) *)

        explode_well_defined_sitpn_state Hwell_def_s'.
        assert (H := Hnodup_state_ditvals).
        clear_well_defined_sitpn_state.
        rename Hnodup_state_ditvals into Hnodup_fs_ditvals_s'.

        (* Builds Permutation (fs new_ditvals) (fs (d_intervals s')) *)

        rewrite app_nil_r in Hperm_app.

        (* Applies [permutation_fs_permutation]. *)

        apply (permutation_fs_permutation
                 new_ditvals (d_intervals s') Hnodup_fs_newd Hnodup_fs_ditvals_s'
                 Hincl_newd Hperm_app).

    (* INDUCTION CASE. *)
    - simpl; destruct a; case_eq (s_intervals sitpn t).

      (* CASE (s_intervals sitpn t) = Some stc_itval *)
      + intros sitval Heq_some_sitval.
        case_eq (is_sensitized sitpn (marking s) (lneighbours sitpn t) t).

        (* CASE (is_sensitized sitpn (marking s) (lneighbours sitpn t) t) = Some b *)
        * intros b His_sens; destruct b.
           
          (* CASE (is_sensitized sitpn (marking s) (lneighbours sitpn t) t) = Some true *)
          -- case_eq (in_list Nat.eq_dec (fired s) t); intros Hin_list.

             (* CASE in_list Nat.eq_dec (fired s) t = true *)
             ++ specialize (IHditvals (new_ditvals ++ [(t, active (dec_itval sitval))])).

                (* Strategy: apply IHditvals, then we need premises. *)

                (* Builds incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') 
                   To do that, we need to show (t, active (dec_itval sitval)) ∈ (d_intervals s') using
                   Hspec.
                 *)
                assert (Hin_t_ditvalss' : In (t, active (dec_itval sitval)) (d_intervals s')).
                {
                  
                  (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
                  inversion Hspec.
                  clear H H0 H1 H2 H3 H4 H5 H6 H8 H9 H10 H11 H12 H13.
                  rename H7 into Hsens_and_fired_reset.

                  (* Gets In t (fs (d_intervals s)) *)
                  deduce_in_from_is_dec_list_cons His_dec_list as Hin_t_fs_ditvals.
                  apply in_fst_split in Hin_t_fs_ditvals.

                  (* Gets In (t, true) (reset s) \/ In t (fired s) *)
                  specialize (in_list_correct Nat.eq_dec (fired s) t Hin_list) as Hin_fired.
                  specialize (or_intror (In (t, true) (reset s)) Hin_fired) as Hreset_or_fired.

                  (* Gets IsSensitized /\ (In (t, true) (reset s) \/ In t (fired s)) 
                     by specializing is_sensitized_correct. *)

                  assert (Hin_t_transs := Hin_t_fs_ditvals).
                  explode_well_defined_sitpn_state Hwell_def_s.
                  rewrite <- (Hwf_state_ditvals t) in Hin_t_transs.
                  apply proj1 in Hin_t_transs.

                  specialize (is_sensitized_correct
                                (marking s) t Hwell_def_sitpn
                                Hwf_state_marking Hin_t_transs His_sens)
                    as His_sens_spec.

                  clear_well_defined_sitpn_state.
                  specialize (conj His_sens_spec Hreset_or_fired) as Hw_sens_fired.

                  (* Gets ~IsSensitized \/ ... *)
                  specialize (or_intror (~ IsSensitized sitpn (marking s) t) Hw_sens_fired)
                    as Hv_notsens_sens.

                  symmetry in Heq_some_sitval.
                  apply (Hsens_and_fired_reset t sitval Hin_t_fs_ditvals Hv_notsens_sens
                                               Heq_some_sitval).
                }
                
                (* Then, we can deduce incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') *)
                assert (Hincl_newd_app : incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s')).
                {
                  intros x Hin_app.
                  apply in_app_or in Hin_app.
                  inversion_clear Hin_app as [Hin_x_newd | Heq_x_t];
                    [ apply (Hincl_newd x Hin_x_newd) |
                      inversion_clear Heq_x_t as [Heq | Hin_nil];
                      [ rewrite <- Heq; assumption |
                        inversion Hin_nil
                      ]
                    ].
                }

                (* Builds IsDecListCons ditvals (d_intervals s) *)
                apply is_dec_list_cons_cons in His_dec_list.
                
                (* Builds Permutation and NoDup hyps by rewriting IH. *) 

                unfold fs in Hperm_app.
                rewrite fst_split_app in Hperm_app.
                rewrite fst_split_cons_app in Hperm_app.
                simpl in Hperm_app.

                unfold fs in Hnodup_fs_newd.
                rewrite fst_split_app in Hnodup_fs_newd.
                rewrite fst_split_cons_app in Hnodup_fs_newd.
                simpl in Hnodup_fs_newd.
                
                unfold fs in IHditvals.
                rewrite fst_split_app in IHditvals.
                rewrite fst_split_app in IHditvals.
                simpl in IHditvals.

                rewrite <- app_assoc in IHditvals.

                (* Applies IHditvals *)
                apply (IHditvals Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                                 His_dec_list Hperm_app Hincl_newd_app Hnodup_fs_newd).

             (* CASE in_list Nat.eq_dec (fired s) t = false *)
             ++ case_eq (get_value Nat.eq_dec t (reset s)).

                (* CASE (get_value Nat.eq_dec t (reset s)) = Some b *)
                ** intros b Hget_v_some; destruct b.

                   (* CASE (get_value Nat.eq_dec t (reset s)) = Some true *)
                   --- specialize (IHditvals (new_ditvals ++ [(t, active (dec_itval sitval))])).

                       (* Strategy: apply IHditvals, then we need premises. *)

                       (* Builds incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') 
                          To do that, we need to show (t, active (dec_itval sitval)) ∈ (d_intervals s') using
                          Hspec.
                        *)
                       assert (Hin_t_ditvalss' : In (t, active (dec_itval sitval)) (d_intervals s')).
                       {
                         
                         (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
                         inversion Hspec.
                         clear H H0 H1 H2 H3 H4 H5 H6 H8 H9 H10 H11 H12 H13.
                         rename H7 into Hsens_and_fired_reset.

                         (* Gets In t (fs (d_intervals s)) *)
                         deduce_in_from_is_dec_list_cons His_dec_list as Hin_t_fs_ditvals.
                         apply in_fst_split in Hin_t_fs_ditvals.

                         (* Gets In (t, true) (reset s) \/ In t (fired s) *)
                         specialize (get_value_correct Nat.eq_dec t (reset s) Hget_v_some) as Hin_ttrue_reset.
                         specialize (or_introl (In t (fired s)) Hin_ttrue_reset) as Hreset_or_fired.

                         (* Gets IsSensitized /\ (In (t, true) (reset s) \/ In t (fired s)) 
                            by specializing is_sensitized_correct. *)

                         assert (Hin_t_transs := Hin_t_fs_ditvals).
                         explode_well_defined_sitpn_state Hwell_def_s.
                         rewrite <- (Hwf_state_ditvals t) in Hin_t_transs.
                         apply proj1 in Hin_t_transs.

                         specialize (is_sensitized_correct
                                       (marking s) t Hwell_def_sitpn
                                       Hwf_state_marking Hin_t_transs His_sens)
                           as His_sens_spec.

                         clear_well_defined_sitpn_state.
                         specialize (conj His_sens_spec Hreset_or_fired) as Hw_sens_fired.

                         (* Gets ~IsSensitized \/ ... *)
                         specialize (or_intror (~ IsSensitized sitpn (marking s) t) Hw_sens_fired)
                           as Hv_notsens_sens.

                         symmetry in Heq_some_sitval.
                         apply (Hsens_and_fired_reset t sitval Hin_t_fs_ditvals Hv_notsens_sens
                                                      Heq_some_sitval).
                       }
                       
                       (* Then, we can deduce incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') *)
                       assert (Hincl_newd_app : incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s')).
                       {
                         intros x Hin_app.
                         apply in_app_or in Hin_app.
                         inversion_clear Hin_app as [Hin_x_newd | Heq_x_t];
                           [ apply (Hincl_newd x Hin_x_newd) |
                             inversion_clear Heq_x_t as [Heq | Hin_nil];
                             [ rewrite <- Heq; assumption |
                               inversion Hin_nil
                             ]
                           ].
                       }

                       (* Builds IsDecListCons ditvals (d_intervals s) *)
                       apply is_dec_list_cons_cons in His_dec_list.
                       
                       (* Builds Permutation and NoDup hyps by rewriting IH. *) 

                       unfold fs in Hperm_app.
                       rewrite fst_split_app in Hperm_app.
                       rewrite fst_split_cons_app in Hperm_app.
                       simpl in Hperm_app.

                       unfold fs in Hnodup_fs_newd.
                       rewrite fst_split_app in Hnodup_fs_newd.
                       rewrite fst_split_cons_app in Hnodup_fs_newd.
                       simpl in Hnodup_fs_newd.
                       
                       unfold fs in IHditvals.
                       rewrite fst_split_app in IHditvals.
                       rewrite fst_split_app in IHditvals.
                       simpl in IHditvals.

                       rewrite <- app_assoc in IHditvals.

                       (* Applies IHditvals *)
                       apply (IHditvals Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                                        His_dec_list Hperm_app Hincl_newd_app Hnodup_fs_newd).
                       
                   (* CASE (get_value Nat.eq_dec t (reset s)) = Some false *)
                   --- destruct d.

                       (* CASE d = active t0 *)
                       +++ specialize (IHditvals (new_ditvals ++ [(t, active (dec_itval t0))])).

                           (* Strategy: apply IHditvals, then we need premises. *)

                           (* Builds incl (new_ditvals ++ [(t, active (dec_itval t0))]) (d_intervals s') 
                              To do that, we need to show (t, active (dec_itval t0)) ∈ (d_intervals s') using
                              Hspec.
                            *)
                           assert (Hin_t_ditvalss' : In (t, active (dec_itval t0)) (d_intervals s')).
                           {
                             
                             (* Strategy: get the right Sitpn semantics rule from
                                          Hspec and specialize it. *)
                             inversion Hspec.
                             clear H H0 H1 H2 H3 H4 H5 H6 H7 H9 H10 H11 H12.
                             rename H8 into Hsens_and_notfired_reset.

                             (* Gets In t (fs (d_intervals s)) *)
                             deduce_in_from_is_dec_list_cons His_dec_list as Hin_t_ditvals.

                             (* Gets IsSensitized by specializing is_sensitized_correct. *)
                             assert (Hin_t_transs := Hin_t_ditvals).
                             apply in_fst_split in Hin_t_transs.
                             explode_well_defined_sitpn_state Hwell_def_s.
                             rewrite <- (Hwf_state_ditvals t) in Hin_t_transs.
                             apply proj1 in Hin_t_transs.

                             specialize (is_sensitized_correct
                                           (marking s) t Hwell_def_sitpn
                                           Hwf_state_marking Hin_t_transs His_sens)
                               as His_sens_spec.
                             clear_well_defined_sitpn_state.
                             
                             (* Gets In (t, false) (reset s) *)
                             specialize (get_value_correct Nat.eq_dec t (reset s) Hget_v_some) as Hin_tfalse_reset.

                             (* Gets ~In t (fired s) *)
                             specialize (not_in_list_correct Nat.eq_dec (fired s) t Hin_list) as Hnot_in_t_fired.

                             apply (Hsens_and_notfired_reset t t0 Hin_t_ditvals His_sens_spec
                                                             Hin_tfalse_reset Hnot_in_t_fired).
                           }
                           
                           (* Then, we can deduce incl (new_ditvals ++ [(t, active (dec_itval t0))]) (d_intervals s') *)
                           assert (Hincl_newd_app : incl (new_ditvals ++ [(t, active (dec_itval t0))]) (d_intervals s')).
                           {
                             intros x Hin_app.
                             apply in_app_or in Hin_app.
                             inversion_clear Hin_app as [Hin_x_newd | Heq_x_t];
                               [ apply (Hincl_newd x Hin_x_newd) |
                                 inversion_clear Heq_x_t as [Heq | Hin_nil];
                                 [ rewrite <- Heq; assumption |
                                   inversion Hin_nil
                                 ]
                               ].
                           }

                           (* Builds IsDecListCons ditvals (d_intervals s) *)
                           apply is_dec_list_cons_cons in His_dec_list.
                           
                           (* Builds Permutation and NoDup hyps by rewriting IH. *) 

                           unfold fs in Hperm_app.
                           rewrite fst_split_app in Hperm_app.
                           rewrite fst_split_cons_app in Hperm_app.
                           simpl in Hperm_app.

                           unfold fs in Hnodup_fs_newd.
                           rewrite fst_split_app in Hnodup_fs_newd.
                           rewrite fst_split_cons_app in Hnodup_fs_newd.
                           simpl in Hnodup_fs_newd.
                           
                           unfold fs in IHditvals.
                           rewrite fst_split_app in IHditvals.
                           rewrite fst_split_app in IHditvals.
                           simpl in IHditvals.

                           rewrite <- app_assoc in IHditvals.

                           (* Applies IHditvals *)
                           apply (IHditvals Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                                            His_dec_list Hperm_app Hincl_newd_app Hnodup_fs_newd).

                       (* CASE d = blocked *)
                       +++ specialize (IHditvals (new_ditvals ++ [(t, blocked)])).

                           (* Strategy: apply IHditvals, then we need premises. *)

                           (* Builds incl (new_ditvals ++ [(t, blocked)]) (d_intervals s') 
                              To do that, we need to show (t, blocked) ∈ (d_intervals s') using
                              Hspec.
                            *)
                           assert (Hin_t_ditvalss' : In (t, blocked) (d_intervals s')).
                           {
                             
                             (* Strategy: get the right Sitpn semantics rule from
                                          Hspec and specialize it. *)
                             inversion Hspec.
                             clear H H0 H1 H2 H3 H4 H5 H6 H7 H8 H10 H11 H12 H13.
                             rename H9 into Hsens_and_notfired_reset.

                             (* Gets In t (fs (d_intervals s)) *)
                             deduce_in_from_is_dec_list_cons His_dec_list as Hin_t_ditvals.

                             (* Gets IsSensitized by specializing is_sensitized_correct. *)
                             assert (Hin_t_transs := Hin_t_ditvals).
                             apply in_fst_split in Hin_t_transs.
                             explode_well_defined_sitpn_state Hwell_def_s.
                             rewrite <- (Hwf_state_ditvals t) in Hin_t_transs.
                             apply proj1 in Hin_t_transs.

                             specialize (is_sensitized_correct
                                           (marking s) t Hwell_def_sitpn
                                           Hwf_state_marking Hin_t_transs His_sens)
                               as His_sens_spec.
                             clear_well_defined_sitpn_state.
                             
                             (* Gets In (t, false) (reset s) *)
                             specialize (get_value_correct Nat.eq_dec t (reset s) Hget_v_some) as Hin_tfalse_reset.

                             (* Gets ~In t (fired s) *)
                             specialize (not_in_list_correct Nat.eq_dec (fired s) t Hin_list) as Hnot_in_t_fired.

                             apply (Hsens_and_notfired_reset t Hin_t_ditvals His_sens_spec
                                                             Hin_tfalse_reset Hnot_in_t_fired).
                           }
                           
                           (* Then, we can deduce incl (new_ditvals ++ [(t, blocked)]) (d_intervals s') *)
                           assert (Hincl_newd_app : incl (new_ditvals ++ [(t, blocked)]) (d_intervals s')).
                           {
                             intros x Hin_app.
                             apply in_app_or in Hin_app.
                             inversion_clear Hin_app as [Hin_x_newd | Heq_x_t];
                               [ apply (Hincl_newd x Hin_x_newd) |
                                 inversion_clear Heq_x_t as [Heq | Hin_nil];
                                 [ rewrite <- Heq; assumption |
                                   inversion Hin_nil
                                 ]
                               ].
                           }

                           (* Builds IsDecListCons ditvals (d_intervals s) *)
                           apply is_dec_list_cons_cons in His_dec_list.
                           
                           (* Builds Permutation and NoDup hyps by rewriting IH. *) 

                           unfold fs in Hperm_app.
                           rewrite fst_split_app in Hperm_app.
                           rewrite fst_split_cons_app in Hperm_app.
                           simpl in Hperm_app.

                           unfold fs in Hnodup_fs_newd.
                           rewrite fst_split_app in Hnodup_fs_newd.
                           rewrite fst_split_cons_app in Hnodup_fs_newd.
                           simpl in Hnodup_fs_newd.
                           
                           unfold fs in IHditvals.
                           rewrite fst_split_app in IHditvals.
                           rewrite fst_split_app in IHditvals.
                           simpl in IHditvals.

                           rewrite <- app_assoc in IHditvals.

                           (* Applies IHditvals *)
                           apply (IHditvals Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                                            His_dec_list Hperm_app Hincl_newd_app Hnodup_fs_newd).
                         
                (* CASE (get_value Nat.eq_dec t (reset s)) = None *)
                ** intros Hget_v_reset.

                   deduce_in_from_is_dec_list_cons His_dec_list as Hin_t_fs_reset.
                   apply in_fst_split in Hin_t_fs_reset.
                   explode_well_defined_sitpn_state Hwell_def_s.
                   rewrite <- (Hwf_state_ditvals t) in Hin_t_fs_reset.
                   rewrite (Hwf_state_reset t) in Hin_t_fs_reset.
                   clear_well_defined_sitpn_state.

                   specialize (get_value_no_error Nat.eq_dec t (reset s) Hin_t_fs_reset)
                     as Hex_get_v.
                   inversion_clear Hex_get_v as (value & Hget_v_some).
                   rewrite Hget_v_reset in Hget_v_some.
                   inversion Hget_v_some.

          (* CASE (is_sensitized sitpn (marking s) (lneighbours sitpn t) t) = Some false *)
          -- specialize (IHditvals (new_ditvals ++ [(t, active (dec_itval sitval))])).

             (* Strategy: apply IHditvals, then we need premises. *)

             (* Builds incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') 
                   To do that, we need to show (t, active (dec_itval sitval)) ∈ (d_intervals s') using
                   Hspec.
              *)
             assert (Hin_t_ditvalss' : In (t, active (dec_itval sitval)) (d_intervals s')).
             {
               
               (* Strategy: get the right Sitpn semantics rule from
                               Hspec and specialize it. *)
               inversion Hspec.
               clear H H0 H1 H2 H3 H4 H5 H6 H8 H9 H10 H11 H12 H13.
               rename H7 into Hsens_and_fired_reset.

               (* Gets In t (fs (d_intervals s)) *)
               deduce_in_from_is_dec_list_cons His_dec_list as Hin_t_fs_ditvals.
               apply in_fst_split in Hin_t_fs_ditvals.

               (* Gets ~IsSensitized \/ ... *)
               assert (Hin_t_transs := Hin_t_fs_ditvals).
               explode_well_defined_sitpn_state Hwell_def_s.
               rewrite <- (Hwf_state_ditvals t) in Hin_t_transs.
               apply proj1 in Hin_t_transs.

               assert (Hnot_sens := His_sens).
               rewrite (not_is_sensitized_iff (marking s) t Hwell_def_sitpn
                                              Hwf_state_marking Hin_t_transs)
                 in Hnot_sens.
               clear_well_defined_sitpn_state.
               specialize (or_introl
                             (IsSensitized sitpn (marking s) t
                              /\ (In (t, true) (reset s) \/ In t (fired s)))
                             Hnot_sens)
                 as Hv_notsens_sens.
               
               symmetry in Heq_some_sitval.
               apply (Hsens_and_fired_reset t sitval Hin_t_fs_ditvals Hv_notsens_sens
                                            Heq_some_sitval).
             }
             
             (* Then, we can deduce incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s') *)
             assert (Hincl_newd_app : incl (new_ditvals ++ [(t, active (dec_itval sitval))]) (d_intervals s')).
             {
               intros x Hin_app.
               apply in_app_or in Hin_app.
               inversion_clear Hin_app as [Hin_x_newd | Heq_x_t];
                 [ apply (Hincl_newd x Hin_x_newd) |
                   inversion_clear Heq_x_t as [Heq | Hin_nil];
                   [ rewrite <- Heq; assumption |
                     inversion Hin_nil
                   ]
                 ].
             }

             (* Builds IsDecListCons ditvals (d_intervals s) *)
             apply is_dec_list_cons_cons in His_dec_list.
             
             (* Builds Permutation and NoDup hyps by rewriting IH. *) 

             unfold fs in Hperm_app.
             rewrite fst_split_app in Hperm_app.
             rewrite fst_split_cons_app in Hperm_app.
             simpl in Hperm_app.

             unfold fs in Hnodup_fs_newd.
             rewrite fst_split_app in Hnodup_fs_newd.
             rewrite fst_split_cons_app in Hnodup_fs_newd.
             simpl in Hnodup_fs_newd.
             
             unfold fs in IHditvals.
             rewrite fst_split_app in IHditvals.
             rewrite fst_split_app in IHditvals.
             simpl in IHditvals.

             rewrite <- app_assoc in IHditvals.

             (* Applies IHditvals *)
             apply (IHditvals Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                              His_dec_list Hperm_app Hincl_newd_app Hnodup_fs_newd).
            
        (* CASE (is_sensitized sitpn (marking s) (lneighbours sitpn t) t) = None, 
           impossible regarding the hypotheses.
         *)
        * intros His_sens_eq_none.
           
           (* Strategy: specialize [is_sensitized_no_error] then contradiction. 
         
              To specialize [is_sensitized_no_error], we need:
              incl (flatten_neighbours (lneighbours sitpn t)) (fs (marking s))
            *)

           deduce_in_from_is_dec_list_cons His_dec_list as Hin_td_sditvals.
           specialize (in_fst_split t d (d_intervals s) Hin_td_sditvals) as Hin_fs_sditvals.
           explode_well_defined_sitpn_state Hwell_def_s.
           rewrite <- (Hwf_state_ditvals t) in Hin_fs_sditvals.
           apply proj1 in Hin_fs_sditvals.
           rename Hin_fs_sditvals into Hin_t_transs.
           clear_well_defined_sitpn_state.

           (* Specializes in_transs_incl_flatten *)
           specialize (in_transs_incl_flatten t Hwell_def_sitpn Hin_t_transs)
             as Hincl_fl_fls.

           (* Gets incl (flatten_ln) places from IsWDSitpn, then use transitivity 
              to get incl flatten_n flatten_ln.
            *)
           explode_well_defined_sitpn.     
           unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
           specialize (incl_tran Hincl_fl_fls Hunk_pl_neigh) as Hincl_fn_fln.

           (* Gets places = (fs (marking s)) from IsWDSitpnState sitpn s *)
           explode_well_defined_sitpn_state Hwell_def_s.
           rewrite Hwf_state_marking in Hincl_fn_fln.

           (* Finally specializes is_sensitized_no_error *)
           specialize (is_sensitized_no_error sitpn (marking s) t Hincl_fn_fln)
             as Hex_is_sens.
           inversion_clear Hex_is_sens as (b & His_sens_eq_some).
           rewrite His_sens_eq_none in His_sens_eq_some; inversion His_sens_eq_some.
           
      (* CASE (s_intervals sitpn t) = None, 
         impossible regarding [IsWellDefinedSitpnState sitpn s]. 
       *)
      + intros Heq_none_sitval.
        explode_well_defined_sitpn_state Hwell_def_s.
        deduce_in_from_is_dec_list_cons His_dec_list as Hin_td_sditvals.
        specialize (in_fst_split t d (d_intervals s) Hin_td_sditvals) as Hin_fs_sditvals.
        rewrite <- (Hwf_state_ditvals t) in Hin_fs_sditvals.
        apply proj2 in Hin_fs_sditvals.
        contradiction.
  Qed.
           
End UpdateTimeIntervalsComplete.
