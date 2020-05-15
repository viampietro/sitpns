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





(* Import lemmas about time. *)

Require Import simpl.SitpnRisingEdgeTime.

(* Import lemmas about marking. *)

Require Import simpl.SitpnFallingEdgeFiredComplete.

(** * Completeness of [get_blocked_itvals_and_reset_orders]. *)

Section GetBlockedAndResetComplete.

  (** * Completeness lemma for [get_blocked_itvals_and_reset_orders]. *)
  
  Lemma get_blocked_and_reset_complete :
    forall (sitpn : Sitpn)
           (s s': SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env rising_edge ->

      forall (istate : SitpnState)
             (ditvals : list (Trans * DynamicTimeInterval))
             (transient_marking : list (Place * nat))
             (r_orders : list (Trans * bool))
             (new_ditvals : list (Trans * DynamicTimeInterval)),

        (* Hypotheses on istate. *)
        sitpn_state_eq s istate ->
        
        (* Hypotheses on ditvals and new_ditvals. *)
        incl ditvals (d_intervals s) ->
        Permutation (fs (new_ditvals ++ ditvals)) (fs (d_intervals s')) ->
        incl new_ditvals (d_intervals s') ->
        NoDup (fs (new_ditvals ++ ditvals)) ->

        (* Hypotheses on r_orders and ditvals. *)
        Permutation ((fs r_orders) ++ (fs ditvals)) (fs (reset s')) ->
        incl r_orders (reset s') ->
        NoDup ((fs r_orders) ++ (fs ditvals)) ->
        
        (* Hypotheses on transient_marking. *)
        Permutation (fs (marking s)) (fs transient_marking) ->
        (forall (p : Place) (n : nat),
            In (p, n) (marking istate) ->
            In (p, n - pre_sum sitpn p (fired istate)) transient_marking) ->
        
        (* Conclusion. *)
        exists (ditvals' : list (Trans * DynamicTimeInterval))
               (reset' : list (Trans * bool)),
          get_blocked_itvals_and_reset_orders
            sitpn istate ditvals transient_marking
            r_orders new_ditvals = Some (reset', ditvals')
          /\ Permutation reset' (reset s')
          /\ Permutation ditvals' (d_intervals s').
  Proof.                                                                  
    intros sitpn s s' time_value env Hwell_def_sitpn
           Hwell_def_s Hwell_def_s' Hspec istate.

    induction ditvals;

      intros transient_marking r_orders new_ditvals
             Hsteq_s_istate Hincl_ditvals Hperm_fs_newd Hincl_newd
             Hnodup_fs_newd Hperm_fs_rorders Hincl_rorders Hnodup_fs_rorders
             Hperm_fsms_fstm Hdef_tm.

    (* BASE CASE, ditvals = []. *)
    - simpl; exists new_ditvals, r_orders;  repeat split.

      (* Proves Permutation r_orders (reset s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)
      
      + (* Builds premises to apply [permutation_fs_permutation] *)

        (* Builds NoDup (fs r_orders) *)

        rewrite app_nil_r in Hnodup_fs_rorders.

        (* Builds NoDup (fs (d_intervals s')) *)

        assert (Hnodup_fs_rs' : NoDup (fs (reset s')))
          by (explode_well_defined_sitpn_state Hwell_def_s'; assumption).
        
        (* Builds Permutation (fs r_orders) (fs (reset s')) *)

        rewrite app_nil_r in Hperm_fs_rorders.

        (* Applies [permutation_fs_permutation]. *)

        apply (permutation_fs_permutation
                 r_orders (reset s') Hnodup_fs_rorders Hnodup_fs_rs'
                 Hincl_rorders Hperm_fs_rorders).
        
      (* Proves Permutation new_ditvals (d_intervals s'). 
         Strategy: use lemma [permutation_fs_permutation]. *)
        
      + (* Builds premises to apply [permutation_fs_permutation] *)

        (* Builds NoDup (fs new_ditvals) *)

        rewrite app_nil_r in Hnodup_fs_newd.

        (* Builds NoDup (fs (d_intervals s')) *)

        assert (Hnodup_fs_ditvals_s' : NoDup (fs (d_intervals s')))
          by (explode_well_defined_sitpn_state Hwell_def_s'; assumption).

        (* Builds Permutation (fs new_ditvals) (fs (d_intervals s')) *)

        rewrite app_nil_r in Hperm_fs_newd.

        (* Applies [permutation_fs_permutation]. *)

        apply (permutation_fs_permutation
                 new_ditvals (d_intervals s') Hnodup_fs_newd
                 Hnodup_fs_ditvals_s' Hincl_newd Hperm_fs_newd).

    (* INDUCTION CASE *)
        
    - destruct a; simpl.

      (* Specializes is_sensitized_no_error to skip the None case when
         rewriting the goal. *)

      assert (Hin_t_transs : In t (transs sitpn)).
      {
        specialize (Hincl_ditvals (t, d) (in_eq (t, d) ditvals)).
        apply in_fst_split in Hincl_ditvals.
        explode_well_defined_sitpn_state Hwell_def_s.
        rewrite <- (Hwf_state_ditvals t) in Hincl_ditvals.
        apply (proj1 Hincl_ditvals).
      }
      
      assert (Hincl_fl_m : incl (flatten_neighbours (lneighbours sitpn t)) (fs transient_marking)).
      {
        explode_well_defined_sitpn; unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        
        assert (Hincl_flat_lneigh : incl (flatten_neighbours (lneighbours sitpn t))
                                         (flatten_lneighbours sitpn (transs sitpn)))
          by (apply (in_transs_incl_flatten t Hwell_def_sitpn Hin_t_transs)).
        
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        explode_well_defined_sitpn_state Hwell_def_s.
        rewrite Hwf_state_marking in Hincl_fl_m.
        intros p Hin_p_fl.
        rewrite <- Hperm_fsms_fstm.
        apply (Hincl_fl_m p Hin_p_fl).
      }
      
      specialize (is_sensitized_no_error sitpn transient_marking t Hincl_fl_m)
        as Hex_is_sens_some.

      inversion_clear Hex_is_sens_some as (b & His_sens_some).
      rewrite His_sens_some.

      (* Two cases, is_sensitized = Some true or Some false. *)
      
      destruct b.

      (* CASE is_sensitized = Some true. *)

      + (* Two cases: d has reached upper bound and t not fired, or conversely. *)

        case_eq (has_reached_upper_bound d && negb (in_list Nat.eq_dec (fired istate) t)).

        (* CASE has_reached_upper_bound && t ∉ fired = true *)
        
        -- intros Hhas_reach_and_nfired_true.

           (* Strategy: apply IHditvals, then we need the proper premises. *)

           specialize (IHditvals transient_marking
                                 (r_orders ++ [(t, false)])
                                 (new_ditvals ++ [(t, blocked)])).

           (* Builds all premises to apply IHditvals. The hardest to
              get are:
              
              - incl (new_ditvals ++ [(t, blocked)]) (d_intervals s')
              - incl (r_orders ++ [(t, false)]) (reset s')
              
              To get these, the strategy is to specialize one rule of
              the Sitpn semantics. *)
           
             inversion Hspec.
             clear H H0 H1 H2 H3 H4 H7 H8 H9 H10 H11.
             rename H5 into His_sens_by_tm, H6 into Hhas_and_nfired.
             
             assert (Hin_tbl_ditvals_s' : In (t, blocked) (d_intervals s')).
             {
               apply andb_prop in Hhas_reach_and_nfired_true.
               inversion_clear Hhas_reach_and_nfired_true as (Hhas_reach_true & Hnfired_true).

               (* Builds premises to apply the Sitpn semantics rule Hhas_and_nfired. *)
               
               apply (has_reached_upper_bound_correct d) in Hhas_reach_true.
               rewrite negb_true_iff in Hnfired_true.
               apply not_in_list_correct in Hnfired_true.
               specialize (Hincl_ditvals (t, d) (in_eq (t, d) ditvals)).

               (* Rewrites ~In t (fired istate) with some hypotheses from
                  sitpn_state_eq s istate. Result is ~In t (fired s). *)

               unfold sitpn_state_eq in Hsteq_s_istate; apply proj2, proj1 in Hsteq_s_istate.
               rewrite <- Hsteq_s_istate in Hnfired_true.
               
               (* Applies the rule. *)
               apply (Hhas_and_nfired t d Hincl_ditvals Hhas_reach_true Hnfired_true).               
             }

             assert (Hincl_newd' : incl (new_ditvals ++ [(t, blocked)]) (d_intervals s')).
             {
               intros a Hin_newd_app.
               apply in_app_or in Hin_newd_app.
               inversion_clear Hin_newd_app as [Hin_nwd | Hin_tl];
                 [ apply (Hincl_newd a Hin_nwd)
                 | inversion_clear Hin_tl as [Heq_tbl | []];
                   rewrite <- Heq_tbl; assumption ].
             }

             assert (Hin_tfalse_reset_s' : In (t, false) (reset s')).
             {
               (* Builds premises to apply Sitpn semantics rule His_sens_by_tm. *)
               
               assert (Hperm_pls_fstm : Permutation (places sitpn) (fs transient_marking)).
               {
                 explode_well_defined_sitpn_state Hwell_def_s.
                 unfold fs in Hperm_fsms_fstm.
                 rewrite <- Hwf_state_marking in Hperm_fsms_fstm.
                 assumption.
               }

               assert (Hdef_tm_bis : forall (p : Place) (n : nat),
                          In (p, n) (marking s) ->
                          In (p, n - pre_sum sitpn p (fired s)) transient_marking).
               {
                 intros p n Hin_mistate.
                 unfold sitpn_state_eq in Hsteq_s_istate.
                 specialize (proj1 Hsteq_s_istate) as Hperm_m_s_istate.
                 rewrite Hperm_m_s_istate in Hin_mistate.
                 specialize (Hdef_tm p n Hin_mistate).

                 assert (Hnodup_fs : NoDup (fired s))
                   by (explode_well_defined_sitpn_state Hwell_def_s; assumption).

                 assert (Hnodup_fistate : NoDup (fired istate))
                   by (unfold sitpn_state_eq in Hsteq_s_istate;
                       apply proj2, proj1 in Hsteq_s_istate;
                       rewrite <- Hsteq_s_istate; assumption).

                 assert (Hequiv_fired : forall t : Trans, In t (fired istate) <-> In t (fired s))
                   by (intros a;
                       unfold sitpn_state_eq in Hsteq_s_istate;
                       apply proj2, proj1 in Hsteq_s_istate;
                       rewrite <- Hsteq_s_istate;
                       reflexivity).      
                 
                 assert (Heq_presum : pre_sum sitpn p (fired istate) = pre_sum sitpn p (fired s))
                   by (apply (pre_sum_eq_iff_incl sitpn p (fired istate) (fired s) Hnodup_fistate Hnodup_fs Hequiv_fired)).

                 rewrite <- Heq_presum; assumption.
               }
               
               assert (Hneq_sitvals_none : s_intervals sitpn t <> None).
               {
                 explode_well_defined_sitpn_state Hwell_def_s'.
                 apply in_fst_split in Hin_tbl_ditvals_s'.
                 apply Hwf_state_ditvals, proj2 in Hin_tbl_ditvals_s'.
                 assumption.
               }

               assert (His_sens : IsSensitized sitpn transient_marking t).
               {
                 apply (is_sensitized_correct_perm
                          transient_marking t Hwell_def_sitpn Hperm_pls_fstm
                          Hin_t_transs His_sens_some).
               }

               apply (His_sens_by_tm
                        t transient_marking Hperm_pls_fstm Hdef_tm_bis
                        Hin_t_transs Hneq_sitvals_none His_sens).
             }

             assert (Hincl_rorders' : incl (r_orders ++ [(t, false)]) (reset s')).
             {
               intros a Hin_rorders_app.
               apply in_app_or in Hin_rorders_app.
               inversion_clear Hin_rorders_app as [Hin_rorders | Hin_tl];
                 [ apply (Hincl_rorders a Hin_rorders)
                 | inversion_clear Hin_tl as [Heq_tfalse | []];
                   rewrite <- Heq_tfalse; assumption ].
             }

             (* Rewrites fs and app in IHditvals and in the context's
                hypotheses. *)
             
             unfold fs in *.

             do 2             
             (rewrite fst_split_app in IHditvals;
              (rewrite fst_split_app in IHditvals || auto);
              simpl in IHditvals;
              rewrite <- app_assoc in IHditvals).             

             let rewrite_nodup_and_perm H :=
                 ((rewrite fst_split_app in H || auto);
                  rewrite fst_split_cons_app in H;
                  simpl in H)
             in rewrite_nodup_and_perm Hperm_fs_newd;
                  rewrite_nodup_and_perm Hnodup_fs_newd;
                  rewrite_nodup_and_perm Hperm_fs_rorders;
                  rewrite_nodup_and_perm Hnodup_fs_rorders.

             (* Then applies IHditvals. *)
             apply (IHditvals
                      Hsteq_s_istate (incl_cons_inv (t, d) ditvals (d_intervals s) Hincl_ditvals)
                      Hperm_fs_newd Hincl_newd' Hnodup_fs_newd Hperm_fs_rorders Hincl_rorders'
                      Hnodup_fs_rorders Hperm_fsms_fstm Hdef_tm).

        (* CASE has_reached_upper_bound && t ∉ fired = false *)
        -- intros Hhas_reach_and_nfired_false.

           (* Strategy: apply IHditvals, then we need the proper premises. *)
           
           specialize (IHditvals transient_marking
                                 (r_orders ++ [(t, false)])
                                 (new_ditvals ++ [(t, d)])).

           (* Builds all premises to apply IHditvals. The hardest to
              get are:
              
              - incl (new_ditvals ++ [(t, d)]) (d_intervals s')
              - incl (r_orders ++ [(t, false)]) (reset s')
              
              To get these, the strategy is to specialize one rule of
              the Sitpn semantics. *)
           
           inversion Hspec.
           clear H H0 H1 H2 H3 H4 H6 H8 H9 H10 H11.
           rename H5 into His_sens_by_tm, H7 into Hnot_has_and_nfired.
           
           assert (Hin_td_ditvals_s' : In (t, d) (d_intervals s')).
           {
             apply andb_false_iff in Hhas_reach_and_nfired_false.
             inversion_clear Hhas_reach_and_nfired_false as [Hhas_reach_false | Hnfired_false].

             (* Case has_reached_upper_bound = false. *)
             - apply (not_has_reached_upper_bound_correct d) in Hhas_reach_false.
               apply or_introl with (B := In t (fired s)) in Hhas_reach_false.

               (* Applies the rule. *)
               apply (Hnot_has_and_nfired t d (Hincl_ditvals (t, d) (in_eq (t, d) ditvals)) Hhas_reach_false).

             (* Case negb (in_list) = false *)
             - rewrite negb_false_iff in Hnfired_false.
               apply in_list_correct in Hnfired_false.
               unfold sitpn_state_eq in Hsteq_s_istate; apply proj2, proj1 in Hsteq_s_istate.
               rewrite <- Hsteq_s_istate in Hnfired_false.
               apply or_intror with (A := ~HasReachedUpperBound d) in Hnfired_false.
               
               (* Applies the rule. *)
               apply (Hnot_has_and_nfired t d (Hincl_ditvals (t, d) (in_eq (t, d) ditvals)) Hnfired_false).
           }

           assert (Hincl_newd' : incl (new_ditvals ++ [(t, d)]) (d_intervals s')).
           {
             intros a Hin_newd_app.
             apply in_app_or in Hin_newd_app.
             inversion_clear Hin_newd_app as [Hin_nwd | Hin_tl];
               [ apply (Hincl_newd a Hin_nwd)
               | inversion_clear Hin_tl as [Heq_td | []];
                 rewrite <- Heq_td; assumption ].
           }

           assert (Hin_tfalse_reset_s' : In (t, false) (reset s')).
           {
             (* Builds premises to apply Sitpn semantics rule His_sens_by_tm. *)
             
             assert (Hperm_pls_fstm : Permutation (places sitpn) (fs transient_marking)).
             {
               explode_well_defined_sitpn_state Hwell_def_s.
               unfold fs in Hperm_fsms_fstm.
               rewrite <- Hwf_state_marking in Hperm_fsms_fstm.
               assumption.
             }

             assert (Hdef_tm_bis : forall (p : Place) (n : nat),
                        In (p, n) (marking s) ->
                        In (p, n - pre_sum sitpn p (fired s)) transient_marking).
             {
               intros p n Hin_mistate.
               unfold sitpn_state_eq in Hsteq_s_istate.
               specialize (proj1 Hsteq_s_istate) as Hperm_m_s_istate.
               rewrite Hperm_m_s_istate in Hin_mistate.
               specialize (Hdef_tm p n Hin_mistate).

               assert (Hnodup_fs : NoDup (fired s))
                 by (explode_well_defined_sitpn_state Hwell_def_s; assumption).

               assert (Hnodup_fistate : NoDup (fired istate))
                 by (unfold sitpn_state_eq in Hsteq_s_istate;
                     apply proj2, proj1 in Hsteq_s_istate;
                     rewrite <- Hsteq_s_istate; assumption).

               assert (Hequiv_fired : forall t : Trans, In t (fired istate) <-> In t (fired s))
                 by (intros a;
                     unfold sitpn_state_eq in Hsteq_s_istate;
                     apply proj2, proj1 in Hsteq_s_istate;
                     rewrite <- Hsteq_s_istate;
                     reflexivity).      
               
               assert (Heq_presum : pre_sum sitpn p (fired istate) = pre_sum sitpn p (fired s))
                 by (apply (pre_sum_eq_iff_incl sitpn p (fired istate) (fired s) Hnodup_fistate Hnodup_fs Hequiv_fired)).

               rewrite <- Heq_presum; assumption.
             }
             
             assert (Hneq_sitvals_none : s_intervals sitpn t <> None).
             {
               explode_well_defined_sitpn_state Hwell_def_s'.
               apply in_fst_split in Hin_td_ditvals_s'.
               apply Hwf_state_ditvals, proj2 in Hin_td_ditvals_s'.
               assumption.
             }

             assert (His_sens : IsSensitized sitpn transient_marking t).
             {
               apply (is_sensitized_correct_perm
                        transient_marking t Hwell_def_sitpn Hperm_pls_fstm
                        Hin_t_transs His_sens_some).
             }

             apply (His_sens_by_tm
                      t transient_marking Hperm_pls_fstm Hdef_tm_bis
                      Hin_t_transs Hneq_sitvals_none His_sens).
           }

           assert (Hincl_rorders' : incl (r_orders ++ [(t, false)]) (reset s')).
           {
             intros a Hin_rorders_app.
             apply in_app_or in Hin_rorders_app.
             inversion_clear Hin_rorders_app as [Hin_rorders | Hin_tl];
               [ apply (Hincl_rorders a Hin_rorders)
               | inversion_clear Hin_tl as [Heq_tfalse | []];
                 rewrite <- Heq_tfalse; assumption ].
           }

           (* Rewrites fs and app in IHditvals and in the context's
                hypotheses. *)
           
           unfold fs in *.

           do 2             
              (rewrite fst_split_app in IHditvals;
               (rewrite fst_split_app in IHditvals || auto);
               simpl in IHditvals;
               rewrite <- app_assoc in IHditvals).             

           let rewrite_nodup_and_perm H :=
               ((rewrite fst_split_app in H || auto);
                rewrite fst_split_cons_app in H;
                simpl in H)
           in rewrite_nodup_and_perm Hperm_fs_newd;
                rewrite_nodup_and_perm Hnodup_fs_newd;
                rewrite_nodup_and_perm Hperm_fs_rorders;
                rewrite_nodup_and_perm Hnodup_fs_rorders.

           (* Then applies IHditvals. *)
           apply (IHditvals
                    Hsteq_s_istate (incl_cons_inv (t, d) ditvals (d_intervals s) Hincl_ditvals)
                    Hperm_fs_newd Hincl_newd' Hnodup_fs_newd Hperm_fs_rorders Hincl_rorders'
                    Hnodup_fs_rorders Hperm_fsms_fstm Hdef_tm).

      (* CASE is_sensitized = Some false *)
           
      + (* Two cases: d has reached upper bound and t not fired, or conversely. *)

        case_eq (has_reached_upper_bound d && negb (in_list Nat.eq_dec (fired istate) t)).

        (* CASE has_reached_upper_bound && t ∉ fired = true *)
        
        -- intros Hhas_reach_and_nfired_true.

           (* Strategy: apply IHditvals, then we need the proper premises. *)

           specialize (IHditvals transient_marking
                                 (r_orders ++ [(t, true)])
                                 (new_ditvals ++ [(t, blocked)])).

           (* Builds all premises to apply IHditvals. The hardest to
              get are:
              
              - incl (new_ditvals ++ [(t, blocked)]) (d_intervals s')
              - incl (r_orders ++ [(t, true)]) (reset s')
              
              To get these, the strategy is to specialize one rule of
              the Sitpn semantics. *)
           
           inversion Hspec.
           clear H H0 H1 H2 H3 H5 H7 H8 H9 H10 H11.
           rename H4 into Hnot_sens_by_tm, H6 into Hhas_and_nfired.
           
           assert (Hin_tbl_ditvals_s' : In (t, blocked) (d_intervals s')).
           {
             apply andb_prop in Hhas_reach_and_nfired_true.
             inversion_clear Hhas_reach_and_nfired_true as (Hhas_reach_true & Hnfired_true).

             (* Builds premises to apply the Sitpn semantics rule Hhas_and_nfired. *)
             
             apply (has_reached_upper_bound_correct d) in Hhas_reach_true.
             rewrite negb_true_iff in Hnfired_true.
             apply not_in_list_correct in Hnfired_true.
             specialize (Hincl_ditvals (t, d) (in_eq (t, d) ditvals)).

             (* Rewrites ~In t (fired istate) with some hypotheses from
                  sitpn_state_eq s istate. Result is ~In t (fired s). *)

             unfold sitpn_state_eq in Hsteq_s_istate; apply proj2, proj1 in Hsteq_s_istate.
             rewrite <- Hsteq_s_istate in Hnfired_true.
             
             (* Applies the rule. *)
             apply (Hhas_and_nfired t d Hincl_ditvals Hhas_reach_true Hnfired_true).               
           }

           assert (Hincl_newd' : incl (new_ditvals ++ [(t, blocked)]) (d_intervals s')).
           {
             intros a Hin_newd_app.
             apply in_app_or in Hin_newd_app.
             inversion_clear Hin_newd_app as [Hin_nwd | Hin_tl];
               [ apply (Hincl_newd a Hin_nwd)
               | inversion_clear Hin_tl as [Heq_tbl | []];
                 rewrite <- Heq_tbl; assumption ].
           }

           assert (Hin_ttrue_reset_s' : In (t, true) (reset s')).
           {
             (* Builds premises to apply Sitpn semantics rule His_sens_by_tm. *)
             
             assert (Hperm_pls_fstm : Permutation (places sitpn) (fs transient_marking)).
             {
               explode_well_defined_sitpn_state Hwell_def_s.
               unfold fs in Hperm_fsms_fstm.
               rewrite <- Hwf_state_marking in Hperm_fsms_fstm.
               assumption.
             }

             assert (Hdef_tm_bis : forall (p : Place) (n : nat),
                        In (p, n) (marking s) ->
                        In (p, n - pre_sum sitpn p (fired s)) transient_marking).
             {
               intros p n Hin_mistate.
               unfold sitpn_state_eq in Hsteq_s_istate.
               specialize (proj1 Hsteq_s_istate) as Hperm_m_s_istate.
               rewrite Hperm_m_s_istate in Hin_mistate.
               specialize (Hdef_tm p n Hin_mistate).

               assert (Hnodup_fs : NoDup (fired s))
                 by (explode_well_defined_sitpn_state Hwell_def_s; assumption).

               assert (Hnodup_fistate : NoDup (fired istate))
                 by (unfold sitpn_state_eq in Hsteq_s_istate;
                     apply proj2, proj1 in Hsteq_s_istate;
                     rewrite <- Hsteq_s_istate; assumption).

               assert (Hequiv_fired : forall t : Trans, In t (fired istate) <-> In t (fired s))
                 by (intros a;
                     unfold sitpn_state_eq in Hsteq_s_istate;
                     apply proj2, proj1 in Hsteq_s_istate;
                     rewrite <- Hsteq_s_istate;
                     reflexivity).      
               
               assert (Heq_presum : pre_sum sitpn p (fired istate) = pre_sum sitpn p (fired s))
                 by (apply (pre_sum_eq_iff_incl sitpn p (fired istate) (fired s) Hnodup_fistate Hnodup_fs Hequiv_fired)).

               rewrite <- Heq_presum; assumption.
             }
             
             assert (Hneq_sitvals_none : s_intervals sitpn t <> None).
             {
               explode_well_defined_sitpn_state Hwell_def_s'.
               apply in_fst_split in Hin_tbl_ditvals_s'.
               apply Hwf_state_ditvals, proj2 in Hin_tbl_ditvals_s'.
               assumption.
             }

             assert (Hnot_sens : ~IsSensitized sitpn transient_marking t).
             {
               rewrite (not_is_sensitized_iff_perm
                          transient_marking t Hwell_def_sitpn Hperm_pls_fstm
                          Hin_t_transs) in His_sens_some.
               assumption.
             }

             apply (Hnot_sens_by_tm
                      t transient_marking Hperm_pls_fstm Hdef_tm_bis
                      Hin_t_transs Hneq_sitvals_none Hnot_sens).
           }

           assert (Hincl_rorders' : incl (r_orders ++ [(t, true)]) (reset s')).
           {
             intros a Hin_rorders_app.
             apply in_app_or in Hin_rorders_app.
             inversion_clear Hin_rorders_app as [Hin_rorders | Hin_tl];
               [ apply (Hincl_rorders a Hin_rorders)
               | inversion_clear Hin_tl as [Heq_tfalse | []];
                 rewrite <- Heq_tfalse; assumption ].
           }

           (* Rewrites fs and app in IHditvals and in the context's
                hypotheses. *)
           
           unfold fs in *.

           do 2             
              (rewrite fst_split_app in IHditvals;
               (rewrite fst_split_app in IHditvals || auto);
               simpl in IHditvals;
               rewrite <- app_assoc in IHditvals).             

           let rewrite_nodup_and_perm H :=
               ((rewrite fst_split_app in H || auto);
                rewrite fst_split_cons_app in H;
                simpl in H)
           in rewrite_nodup_and_perm Hperm_fs_newd;
                rewrite_nodup_and_perm Hnodup_fs_newd;
                rewrite_nodup_and_perm Hperm_fs_rorders;
                rewrite_nodup_and_perm Hnodup_fs_rorders.

           (* Then applies IHditvals. *)
           apply (IHditvals
                    Hsteq_s_istate (incl_cons_inv (t, d) ditvals (d_intervals s) Hincl_ditvals)
                    Hperm_fs_newd Hincl_newd' Hnodup_fs_newd Hperm_fs_rorders Hincl_rorders'
                    Hnodup_fs_rorders Hperm_fsms_fstm Hdef_tm).

        (* CASE has_reached_upper_bound && t ∉ fired = false *)
        -- intros Hhas_reach_and_nfired_false.

           (* Strategy: apply IHditvals, then we need the proper premises. *)
           
           specialize (IHditvals transient_marking
                                 (r_orders ++ [(t, true)])
                                 (new_ditvals ++ [(t, d)])).

           (* Builds all premises to apply IHditvals. The hardest to
              get are:
              
              - incl (new_ditvals ++ [(t, d)]) (d_intervals s')
              - incl (r_orders ++ [(t, true)]) (reset s')
              
              To get these, the strategy is to specialize one rule of
              the Sitpn semantics. *)
           
           inversion Hspec.
           clear H H0 H1 H2 H3 H5 H6 H8 H9 H10 H11.
           rename H4 into Hnot_sens_by_tm, H7 into Hnot_has_and_nfired.
           
           assert (Hin_td_ditvals_s' : In (t, d) (d_intervals s')).
           {
             apply andb_false_iff in Hhas_reach_and_nfired_false.
             inversion_clear Hhas_reach_and_nfired_false as [Hhas_reach_false | Hnfired_false].

             (* Case has_reached_upper_bound = false. *)
             - apply (not_has_reached_upper_bound_correct d) in Hhas_reach_false.
               apply or_introl with (B := In t (fired s)) in Hhas_reach_false.

               (* Applies the rule. *)
               apply (Hnot_has_and_nfired t d (Hincl_ditvals (t, d) (in_eq (t, d) ditvals)) Hhas_reach_false).

             (* Case negb (in_list) = false *)
             - rewrite negb_false_iff in Hnfired_false.
               apply in_list_correct in Hnfired_false.
               unfold sitpn_state_eq in Hsteq_s_istate; apply proj2, proj1 in Hsteq_s_istate.
               rewrite <- Hsteq_s_istate in Hnfired_false.
               apply or_intror with (A := ~HasReachedUpperBound d) in Hnfired_false.
               
               (* Applies the rule. *)
               apply (Hnot_has_and_nfired t d (Hincl_ditvals (t, d) (in_eq (t, d) ditvals)) Hnfired_false).
           }

           assert (Hincl_newd' : incl (new_ditvals ++ [(t, d)]) (d_intervals s')).
           {
             intros a Hin_newd_app.
             apply in_app_or in Hin_newd_app.
             inversion_clear Hin_newd_app as [Hin_nwd | Hin_tl];
               [ apply (Hincl_newd a Hin_nwd)
               | inversion_clear Hin_tl as [Heq_td | []];
                 rewrite <- Heq_td; assumption ].
           }

           assert (Hin_ttrue_reset_s' : In (t, true) (reset s')).
           {
             (* Builds premises to apply Sitpn semantics rule His_sens_by_tm. *)
             
             assert (Hperm_pls_fstm : Permutation (places sitpn) (fs transient_marking)).
             {
               explode_well_defined_sitpn_state Hwell_def_s.
               unfold fs in Hperm_fsms_fstm.
               rewrite <- Hwf_state_marking in Hperm_fsms_fstm.
               assumption.
             }

             assert (Hdef_tm_bis : forall (p : Place) (n : nat),
                        In (p, n) (marking s) ->
                        In (p, n - pre_sum sitpn p (fired s)) transient_marking).
             {
               intros p n Hin_mistate.
               unfold sitpn_state_eq in Hsteq_s_istate.
               specialize (proj1 Hsteq_s_istate) as Hperm_m_s_istate.
               rewrite Hperm_m_s_istate in Hin_mistate.
               specialize (Hdef_tm p n Hin_mistate).

               assert (Hnodup_fs : NoDup (fired s))
                 by (explode_well_defined_sitpn_state Hwell_def_s; assumption).

               assert (Hnodup_fistate : NoDup (fired istate))
                 by (unfold sitpn_state_eq in Hsteq_s_istate;
                     apply proj2, proj1 in Hsteq_s_istate;
                     rewrite <- Hsteq_s_istate; assumption).

               assert (Hequiv_fired : forall t : Trans, In t (fired istate) <-> In t (fired s))
                 by (intros a;
                     unfold sitpn_state_eq in Hsteq_s_istate;
                     apply proj2, proj1 in Hsteq_s_istate;
                     rewrite <- Hsteq_s_istate;
                     reflexivity).      
               
               assert (Heq_presum : pre_sum sitpn p (fired istate) = pre_sum sitpn p (fired s))
                 by (apply (pre_sum_eq_iff_incl sitpn p (fired istate) (fired s) Hnodup_fistate Hnodup_fs Hequiv_fired)).

               rewrite <- Heq_presum; assumption.
             }
             
             assert (Hneq_sitvals_none : s_intervals sitpn t <> None).
             {
               explode_well_defined_sitpn_state Hwell_def_s'.
               apply in_fst_split in Hin_td_ditvals_s'.
               apply Hwf_state_ditvals, proj2 in Hin_td_ditvals_s'.
               assumption.
             }

             assert (Hnot_sens : ~IsSensitized sitpn transient_marking t).
             {
               rewrite (not_is_sensitized_iff_perm
                          transient_marking t Hwell_def_sitpn Hperm_pls_fstm
                          Hin_t_transs) in His_sens_some.
               assumption.
             }

             apply (Hnot_sens_by_tm
                      t transient_marking Hperm_pls_fstm Hdef_tm_bis
                      Hin_t_transs Hneq_sitvals_none Hnot_sens).
           }

           assert (Hincl_rorders' : incl (r_orders ++ [(t, true)]) (reset s')).
           {
             intros a Hin_rorders_app.
             apply in_app_or in Hin_rorders_app.
             inversion_clear Hin_rorders_app as [Hin_rorders | Hin_tl];
               [ apply (Hincl_rorders a Hin_rorders)
               | inversion_clear Hin_tl as [Heq_tfalse | []];
                 rewrite <- Heq_tfalse; assumption ].
           }
           
           (* Rewrites fs and app in IHditvals and in the context's
                hypotheses. *)
           
           unfold fs in *.

           do 2             
              (rewrite fst_split_app in IHditvals;
               (rewrite fst_split_app in IHditvals || auto);
               simpl in IHditvals;
               rewrite <- app_assoc in IHditvals).             

           let rewrite_nodup_and_perm H :=
               ((rewrite fst_split_app in H || auto);
                rewrite fst_split_cons_app in H;
                simpl in H)
           in rewrite_nodup_and_perm Hperm_fs_newd;
                rewrite_nodup_and_perm Hnodup_fs_newd;
                rewrite_nodup_and_perm Hperm_fs_rorders;
                rewrite_nodup_and_perm Hnodup_fs_rorders.

           (* Then applies IHditvals. *)
           apply (IHditvals
                    Hsteq_s_istate (incl_cons_inv (t, d) ditvals (d_intervals s) Hincl_ditvals)
                    Hperm_fs_newd Hincl_newd' Hnodup_fs_newd Hperm_fs_rorders Hincl_rorders'
                    Hnodup_fs_rorders Hperm_fsms_fstm Hdef_tm).
  Qed.
  
End GetBlockedAndResetComplete.
