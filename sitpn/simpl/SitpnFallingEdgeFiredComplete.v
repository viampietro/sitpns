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

Require Import Coqlib.

(* Import Sitpn material. *)

Require Import simpl.Sitpn.
Require Import simpl.SitpnTokenPlayer.
Require Import simpl.SitpnSemantics.
Require Import simpl.SitpnTactics.
Require Import simpl.SitpnCoreLemmas.

(* Import misc. lemmas, tactics and definitions. *)




(* Import lemmas on marking functions. *)

Require Import simpl.SitpnRisingEdgeMarking.
Require Import simpl.SitpnWellDefMarking.

(* Import lemmas on fired functions. *)

Require Import simpl.SitpnFallingEdgeFired.
Require Import simpl.SitpnWellDefFired.

(* Misc. imports. *)

Require Import Classical_Prop.

(** * Completeness of [sitpn_map_fire]. *)

Section SitpnMapFireComplete.

  (** ** Lemmas on [pre_sum] functions. *)

  (** ∀ t, ∀ l, t ∈ l ∧ NoDup l ⇒ pre_sum l = pre t + pre_sum (l - {t}) 
   *  Needed to prove pre_sum_eq_iff_incl. *)

  Lemma pre_sum_add_rm : 
    forall (sitpn : Sitpn)
           (p : Place)
           (l : list Trans)
           (t : Trans),
      In t l ->
      NoDup l ->
      pre_sum sitpn p l = pre sitpn t p + pre_sum sitpn p (remove eq_nat_dec t l).
  Proof.
    intros sitpn p l;
      functional induction (pre_sum sitpn p l) using pre_sum_ind;
      intros a Hin_a_l Hnodup_l.
    - inversion Hin_a_l.
    - inversion_clear Hin_a_l as [Heq_at | Hin_a_tl].
      + rewrite <- Heq_at.
        simpl; case (Nat.eq_dec t t).
        -- intro Heq_refl.
           rewrite NoDup_cons_iff in Hnodup_l; apply proj1 in Hnodup_l.
           specialize (not_in_remove_eq Nat.eq_dec t tail Hnodup_l) as Heq_rm.
           rewrite Heq_rm; reflexivity.
        -- intro Heq_diff; elim Heq_diff; reflexivity.
      + simpl; case (Nat.eq_dec a t).
        -- rewrite NoDup_cons_iff in Hnodup_l; apply proj1 in Hnodup_l.
           specialize (not_in_in_diff t a tail (conj Hnodup_l Hin_a_tl)) as Hdiff_ta.
           intro Heq_at; symmetry in Heq_at; contradiction.
        -- intro Hdiff_at.
           simpl; symmetry; rewrite Nat.add_comm.
           rewrite <- Nat.add_assoc.
           rewrite Nat.add_cancel_l; symmetry; rewrite Nat.add_comm.
           rewrite NoDup_cons_iff in Hnodup_l; apply proj2 in Hnodup_l.
           apply (IHn a Hin_a_tl Hnodup_l).
  Qed.

  (** For all list of transitions l and l', if l is a permutation 
   *  of l', then pre_sum l = pre_sum l'. *)

  Lemma pre_sum_eq_iff_incl :
    forall (sitpn : Sitpn)
           (p : Place)
           (l l' : list Trans),
      NoDup l ->
      NoDup l' ->
      (forall t : Trans, In t l <-> In t l') ->
      pre_sum sitpn p l = pre_sum sitpn p l'.
  Proof.
    intros sitpn p l;
      functional induction (pre_sum sitpn p l) using pre_sum_ind;
      intros l' Hnodup_l Hnodup_l' Hequiv.
    (* BASE CASE *)
    - functional induction (pre_sum sitpn p l') using pre_sum_ind.
      + reflexivity.
      + assert (Hin_eq : In t (t :: tail)) by apply in_eq.
        rewrite <- Hequiv in Hin_eq; inversion Hin_eq.
    (* GENERAL CASE *)
    - assert (Hin_eq : In t (t :: tail)) by apply in_eq.
      rewrite Hequiv in Hin_eq.
      specialize (pre_sum_add_rm sitpn p l' t Hin_eq Hnodup_l') as Heq_presum.
      rewrite Heq_presum.
      rewrite Nat.add_cancel_l.
      assert (Hequiv_tl : forall t0 : Trans, In t0 tail <-> In t0 (remove Nat.eq_dec t l')).
      {
        intro t0; split.
        - intro Hin_tl; specialize (in_cons t t0 tail Hin_tl) as Hin_t0_ctl.
          rewrite NoDup_cons_iff in Hnodup_l.
          apply proj1 in Hnodup_l.
          specialize (not_in_in_diff t t0 tail (conj Hnodup_l Hin_tl)) as Hdiff_tt0.
          apply not_eq_sym in Hdiff_tt0.
          rewrite Hequiv in Hin_t0_ctl.
          rewrite in_remove_iff; apply (conj Hin_t0_ctl Hdiff_tt0).
        - intro Hin_rm.
          rewrite in_remove_iff in Hin_rm.
          elim Hin_rm; clear Hin_rm; intros Hin_t0_l' Hdiff_t0t.
          rewrite <- Hequiv in Hin_t0_l'.
          inversion_clear Hin_t0_l' as [Heq_t0t | Hin_t0_tl].
          + symmetry in Heq_t0t; contradiction.
          + assumption.
      }
      rewrite NoDup_cons_iff in Hnodup_l; apply proj2 in Hnodup_l.
      specialize (nodup_if_remove l' Hnodup_l' t Nat.eq_dec) as Hnodup_rm.
      apply (IHn (remove Nat.eq_dec t l') Hnodup_l Hnodup_rm Hequiv_tl). 
  Qed.
  
  (** Completeness lemma for sitpn_fire_aux. *)
  
  Lemma sitpn_fire_aux_complete :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (tmp_state : SitpnState)
           (pg pgroup : list Trans)
           (fired_transitions : list Trans)
           (residual_marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->

      (* Properties of tmp_state. *)
      (marking tmp_state) = (marking s) ->
      Permutation (d_intervals tmp_state) (d_intervals s') ->
      Permutation (cond_values tmp_state) (cond_values s') ->
      
      (* Hypotheses on pg, pgroup and fired_transitions *)
      In pgroup sitpn.(priority_groups) ->
      (forall t : Trans, In t pgroup /\ In t (fired s') ->
                         In t (fired_transitions ++ pg)) ->
      IsDecListCons pg pgroup ->
      NoDup (fired_transitions ++ pg) ->
      incl fired_transitions (fired s') ->
      (forall t : Trans,
          In t pg ->
          forall t' : Trans,
            In t' fired_transitions ->
            HasHigherPriority t' t pgroup /\ In t' (fired s')) ->
        
      (* Hypotheses on residual_marking. *)
      (forall (p : Place) (n : nat),
          In (p, n) (marking tmp_state) ->
          In (p, n - (pre_sum sitpn p fired_transitions)) residual_marking) ->
      (places sitpn) =  (fs residual_marking) ->

      (* Conclusion *)
      exists final_fired : list Trans,
        sitpn_fire_aux sitpn tmp_state residual_marking fired_transitions pg = Some final_fired /\
        incl final_fired s'.(fired) /\
        (forall t : Trans, In t pg /\ In t s'.(fired) -> In t final_fired).
  Proof.
    intros sitpn s s' time_value env tmp_state.
    induction pg;
      intros pgroup fired_transitions residual_marking
             Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
             Hin_pgs Hin_fpg_app His_dec Hnodup_app
             Hincl_sf Hhigh_w_sf Hresid_m Hsame_struct.
    
    (* BASE CASE *)
    - exists fired_transitions; simpl.
      split; [ reflexivity | split; [assumption | intros t Hw; apply proj1 in Hw; inversion Hw]].

    (* INDUCTION CASE *)
    - simpl sitpn_fire_aux.
      
      (* First, apply get_neighbours_complete. 
         To do so, we need (a, neigh_of_a) ∈ (lneighbours sitpn) ∧ NoDup (lneighbours sitpn) *)

      (* explode_well_defined_sitpn. *)
      (* assert (Hnodup_lneighbours := Hnodup_transs). *)
      (* unfold NoDupTranss in Hnodup_lneighbours. *)
      (* rewrite Hunk_tr_neigh in Hnodup_lneighbours. *)

      (* Builds In a (concat (priority_groups sitpn)) *)

      (* specialize (is_dec_list_cons_incl His_dec) as Hin_a_pg. *)
      (* assert (Hin_eq : In a (a :: pg)) by apply in_eq. *)
      (* specialize (Hin_a_pg a Hin_eq); clear Hin_eq. *)
      (* specialize (in_concat a pgroup (priority_groups sitpn) Hin_a_pg Hin_pgs) as Hin_a_concat. *)
      (* unfold NoUnknownInPriorityGroups in Hno_unk_pgroups. *)
      (* rewrite <- Hno_unk_pgroups in Hin_a_concat. *)
      (* rewrite Hunk_tr_neigh in Hin_a_concat. *)
      (* specialize (in_fst_split_in_pair a (lneighbours sitpn) Hin_a_concat) as Hin_lneigh_ex. *)
      (* inversion_clear Hin_lneigh_ex as (neigh_of_a & Hin_lneigh). *)

      (* Specializes get_neighbours_complete, then rewrite the goal. *)

      (* specialize (get_neighbours_complete *)
      (*               (lneighbours sitpn) a neigh_of_a Hnodup_lneighbours Hin_lneigh) *)
      (*   as Hget_neigh. *)
      (* rewrite Hget_neigh. *)    

      (* Specializes sitpn_is_firable_no_error to skip the error case
         when rewriting the goal. *)

      assert (Hincl_fl_m : incl (flatten_neighbours (lneighbours sitpn a)) (fs (marking tmp_state))).
      {
        explode_well_defined_sitpn; unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        
        assert (Hincl_flat_lneigh : incl (flatten_neighbours (lneighbours sitpn a))
                                         (flatten_lneighbours sitpn (transs sitpn))).
        {
          deduce_in_transs; apply (in_transs_incl_flatten a Hwell_def_sitpn Hin_t_transs).
        }
        
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        explode_well_defined_sitpn_state Hwell_def_s.
        rewrite Hwf_state_marking in Hincl_fl_m.
        rewrite <- Heq_m_tmp in Hincl_fl_m.
        assumption.
      }

      assert (Hin_t_fs_ditvals : s_intervals sitpn a = None \/ In a (fs (d_intervals tmp_state))).
      {
        assert (Hv_sitvals := classic ((s_intervals sitpn a) = None)).
        inversion_clear Hv_sitvals as [Heq_none_sitvals | Heq_some_sitvals].
        - left; assumption.
        - deduce_in_transs; explode_well_defined_sitpn_state Hwell_def_s'.
          assert (Hw_intranss_sitvals := conj Hin_t_transs Heq_some_sitvals).
          rewrite (Hwf_state_ditvals a) in Hw_intranss_sitvals.
          apply (in_fst_split_in_pair a (d_intervals s')) in Hw_intranss_sitvals.
          inversion_clear Hw_intranss_sitvals as (ditval & Hin_ditvals_s').
          right.
          apply in_fst_split with (b := ditval).
          rewrite Hperm_ditvals_tmp.
          assumption.
      }
      
      specialize (sitpn_is_firable_no_error sitpn tmp_state a Hincl_fl_m Hin_t_fs_ditvals) as Hfirable_ex.
      inversion_clear Hfirable_ex as (b & Hfirable).
      rewrite Hfirable.

      (* Two cases, either sitpn_is_firable = Some true or Some false. *)
      dependent induction b.

      (* CASE sitpn_is_firable = Some true, then continues to dig the function. *)
      
      +

        (* Specializes is_sensitized_no_error to skip the error case
           when rewriting the goal. *)

        assert (Hincl_fl_rm : incl (flatten_neighbours (lneighbours sitpn a)) (fs residual_marking)).
        {
          explode_well_defined_sitpn_state Hwell_def_s.
          rewrite <- Hsame_struct, Hwf_state_marking, <- Heq_m_tmp.
          assumption.
        }
        
        specialize (is_sensitized_no_error
                      sitpn residual_marking a Hincl_fl_rm)
          as Hsens_ex.
        inversion_clear Hsens_ex as (b & Hsens).
        rewrite Hsens.

        (* Two cases, either is_sensitized = Some true or Some false. *)
        destruct b.

        (* CASE is_sensitized = Some true, then continues to dig the function. *)
        --

          (* Specializes update_residual_marking_no_error to skip the  
             error case when rewriting the goal. *)    
                    
          specialize (update_marking_pre_no_error
                        sitpn residual_marking a Hwell_def_sitpn Hincl_fl_rm)
            as Hupdate_res_ex.
          
          inversion_clear Hupdate_res_ex as (residual_marking' & Hupdate_res).
          
          (* Rewrites update_residual_marking in the goal. *)
          rewrite Hupdate_res.

          (* Then, inversion Hspec and specialization of one of the spec rule, 
             to obtain In a (fired s'). *)
          inversion Hspec.
          clear H H0 H1 H3 H4 H5 H6 H7 H8 H9 H10 H11 H13;
            rename H2 into Heq_marking, H12 into Hsens_by_res.

          (* Builds SitpnIsfirable sitpn s' a *)

          assert (Heq_pls : places sitpn = fs (marking tmp_state)).
          {
            explode_well_defined_sitpn_state Hwell_def_s.
            rewrite <- Heq_m_tmp in Hwf_state_marking.
            assumption.
          }

          assert (Hperm_conditions : Permutation (conditions sitpn) (fs (cond_values tmp_state))).
          {
            explode_well_defined_sitpn_state Hwell_def_s'.
            rewrite Hperm_conds_tmp.
            rewrite Hwf_state_condv.
            reflexivity.
          }

          assert (Hin_a_transs : In a (transs sitpn)) by (deduce_in_transs; assumption).
          
          apply (sitpn_is_firable_correct_no_wd
                   tmp_state a Hwell_def_sitpn Heq_pls Hperm_conditions Hin_a_transs)
            in Hfirable.

          assert (Heq_m_tmp_s' : (marking tmp_state) = (marking s'))
            by (rewrite <- Heq_marking; assumption).
          
          specialize (sitpn_is_firable_iff_perm
                        sitpn tmp_state s' a Heq_m_tmp_s' Hperm_ditvals_tmp Hperm_conds_tmp)
            as Hequiv_firable.
          rewrite Hequiv_firable in Hfirable.

          (* Builds IsSensitized sitpn residual_marking a *)
          apply (is_sensitized_correct
                   residual_marking a Hwell_def_sitpn
                   Hsame_struct Hin_a_transs) in Hsens.

          (* Builds hypothesis about residual marking definition (the big one!!).
             To do so, we need to build:
             
             IsPrioritySet (fired s') pgroup t fired_transitions
             
             Then, we need to prove that fired_transitions is the only
             priority set defined by the IsPrioritySet relation.
             
           *)
          specialize (Hhigh_w_sf a (@in_eq Trans a pg)) as Hhigh_w_sf_a.
          assert (Hsf_w_high :
                    forall t : Trans,
                      HasHigherPriority t a pgroup /\ In t (fired s') ->
                      In t fired_transitions).
          {
            intros t Hw; elim Hw; intros Hhas_high Hin_t_ff; clear Hw.
            specialize (NoDup_remove fired_transitions pg a Hnodup_app) as Hnodup_app_rm;
              apply proj1 in Hnodup_app_rm.

            (* Explodes HasHigherpriority to obtain In t pgroup. *)
            unfold HasHigherPriority in Hhas_high.
            inversion_clear Hhas_high as (Hin_t_pg & Hw).
            inversion_clear Hw as (Hin_a_pg & His_pred).

            (* Then, specializes Hin_fpg_app. *)
            specialize (Hin_fpg_app t (conj Hin_t_pg Hin_t_ff)) as Hin_t_app.
            apply in_app_or in Hin_t_app; inversion_clear Hin_t_app as [Hin_t_ftrs | Hin_t_cpg].

            (* Two cases, either t ∈ fired_transitions or t ∈ (a :: pg) *)
            - assumption.
              
            (* If t ∈ (a :: pg), then two cases.  
               - t = a
               - t ∈ pg
               In both cases, contradicts IsPredInNodupList t a pgroup. *)
              
            - inversion_clear Hin_t_cpg as [Heq_ta | Hin_t_tl].

              (* Case t = a *)
              + unfold IsPredInNoDupList in His_pred.
                rewrite Heq_ta in His_pred;
                  apply proj1 in His_pred;
                  elim His_pred; reflexivity.

              (* Case In t pg. *)
              +

                (* Builds ~IsPredInNoDuplist t a (a :: pg) *)
                assert (Hnot_is_pred : ~IsPredInNoDupList t a (a :: pg)) by
                    apply not_is_pred_in_list_if_hd.
                specialize (not_is_pred_in_dec_list His_dec Hin_t_tl) as Hnot_is_pred_in_pg.
                contradiction.
          }
          
          assert (Hhigh_sf_iff :
                    forall t : Trans,
                      HasHigherPriority t a pgroup /\ In t (fired s') <->
                      In t fired_transitions) by (intros t'; split; [ auto | auto ]).
          clear Hsf_w_high.

          (* Builds NoDup fired_transitions *)
          specialize (nodup_app fired_transitions (a :: pg) Hnodup_app) as Hnodup_ftrs;
            apply proj1 in Hnodup_ftrs.
          
          (* Builds residual marking definition hypothesis. *)

          assert (Hresm_def :
                    forall pr : list Trans,
                      IsPrioritySet (fired s') pgroup a pr ->
                      forall (p : Place) (n : nat),
                        In (p, n) (marking s') -> In (p, n - pre_sum sitpn p pr) residual_marking).
          {
            intros pr His_prior p n Hin_m'.
            rewrite Heq_m_tmp in Hresid_m.
            rewrite Heq_marking in Hresid_m.
            specialize (Hresid_m p n Hin_m') as Hin_resm.

            unfold IsPrioritySet in His_prior;
              inversion_clear His_prior as (Hnodup_pr & Hdef_pr).
            
            assert (Heq_pr_ftrs: forall t : Trans, In t pr <-> In t fired_transitions).
            {
              intros t;
                split;
                intro Hin;
                ((rewrite <- (Hdef_pr t) in Hin; rewrite (Hhigh_sf_iff t) in Hin)
                 || (rewrite <- (Hhigh_sf_iff t) in Hin; rewrite (Hdef_pr t) in Hin));
                assumption.                            
            }
            
            specialize (pre_sum_eq_iff_incl
                          sitpn p pr fired_transitions Hnodup_pr
                          Hnodup_ftrs Heq_pr_ftrs)
              as Heq_presum.
            rewrite Heq_presum.
            assumption.
          }
          
          (* Specializes the spec rule in Hsens_by_res to obtain In a (fired s'). *)
          deduce_in_from_is_dec_list_cons His_dec as Hin_a_pg.
          rewrite Heq_marking in Hsens_by_res.
          specialize (Hsens_by_res
                        pgroup a residual_marking Hin_pgs Hin_a_pg
                        Hfirable Hsame_struct Hresm_def Hsens) as Hin_a_sf.
          
          (* Next step, specializes IH 
             with fired_transitions := fired_transitions ++ [a]  
             and residual_marking := residual_marking'. *)

          (* First, we need all hypotheses. *)
          
          (* Builds IsDecListCons pg pgroup *)
          specialize (is_dec_list_cons_cons His_dec) as His_dec_tl.

          (* Builds incl (fired_transitions ++ [a]) (fired s'). *)
          assert (Hincl_a_sf : incl (fired_transitions ++ [a]) (fired s')).
          {
            intros x Hin_x_app;
              apply in_app_or in Hin_x_app;
              inversion_clear Hin_x_app as [ Hin_x_ftrs | Hin_x_a ];
              [ apply (Hincl_sf x Hin_x_ftrs) |
                inversion_clear Hin_x_a as [ Heq_xa | Hin_nil ];
                [ rewrite Heq_xa in Hin_a_sf; assumption | inversion Hin_nil ] ].
          }
          
          (* Builds 
             ∀ t ∈ pgroup,  
             ∀ t' ∈ fired_transitions ⇒ t' ≻ t ∧ t' ∈ (fired s') *)
          assert (Hhigh_w_sf' :
                    forall t : Trans,
                      In t pg ->
                      forall t' : Trans,
                        In t' (fired_transitions ++ [a]) ->
                        HasHigherPriority t' t pgroup /\ In t' (fired s')).
          {
            
            intros t Hin_t_pg t' Hin_tp_app.
            apply in_app_or in Hin_tp_app;
              inversion_clear Hin_tp_app as [ Hin_tp_ftrs | Hin_tp_a ].
            - apply in_cons with (a := a) in Hin_t_pg.
              apply (Hhigh_w_sf t Hin_t_pg t' Hin_tp_ftrs).
            - inversion_clear Hin_tp_a as [ Heq_tpa | Hin_nil].
              + rewrite <- Heq_tpa; split.
                (* a ≻ t *)
                -- assert (Hsucc_a_t : HasHigherPriority a t pgroup).
                   {
                     unfold HasHigherPriority.
                     split. assumption.
                     split. apply in_cons with (a := a) in Hin_t_pg. apply (Hincl t Hin_t_pg).
                     unfold IsPredInNoDupList.
                     split.

                     (* Proves a <> t. *)
                     apply NoDup_remove_2 in Hnodup_app.
                     apply not_app_in in Hnodup_app; apply proj2 in Hnodup_app.
                     apply (not_in_in_diff a t pg (conj Hnodup_app Hin_t_pg)).
                     split.

                     (* Proves NoDup pgroup. *)
                     explode_well_defined_sitpn.
                     unfold NoIntersectInPriorityGroups in Hno_inter.
                     apply (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                             pgroup Hin_pgs).

                     (* Proves IsPredInlist *)
                     explode_well_defined_sitpn.
                     specialize (is_pred_in_list_in_tail a t pg Hin_t_pg) as His_pred'.
                     unfold NoIntersectInPriorityGroups in Hno_inter.
                     specialize (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                                  pgroup Hin_pgs) as Hnodup_pgroup.
                     apply (is_pred_in_dec_list His_pred' His_dec Hnodup_pgroup).
                   }
                   assumption.
                   
                (* a ∈ (fired s') *)
                -- assumption.
              + inversion Hin_nil.
          }          

          (* Builds ∀ (p, n) ∈ (marking s) ⇒ (p, n - pre_sum (fired_transitions ++ [a]))  *)
          
          (* We need 
             ∀ (p, n) ∈ residual_marking ⇒  
             (p, n - pre_sum sitpn p [t]) ∈ residual_marking' *)
                    
          (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
          assert (Hnodup_fs_rm : NoDup (fs residual_marking))
            by (explode_well_defined_sitpn;
                unfold NoDupPlaces in Hnodup_places;
                rewrite Hsame_struct in Hnodup_places;
                assumption).
          
          (* Builds In (t, neigh_of_t) (lneighbours sitpn) *)
          specialize (update_marking_pre_correct
                        sitpn residual_marking a residual_marking'
                        Hwell_def_sitpn Hnodup_fs_rm Hin_a_transs Hupdate_res)
            as Hin_res_in_fin.
          
          (* Then we need pre_sum_app_add *)
          specialize (pre_sum_app_add sitpn) as Heq_presum.
          
          (* Finally, deduces the hypothesis. *)
          assert (
              Hresid'_m :
                (forall (p : Place) (n : nat),
                    In (p, n) (marking tmp_state) ->
                    In (p, n - pre_sum sitpn p (fired_transitions ++ [a])) residual_marking')
            ).
          {
            intros p n Hin_ms.
            apply Hresid_m in Hin_ms.
            apply Hin_res_in_fin with (n := n - pre_sum sitpn p fired_transitions) in Hin_ms.
            assert (Heq_presum' : pre_sum sitpn p [a] = pre sitpn a p) by (simpl; auto).
            rewrite <- Nat.sub_add_distr in Hin_ms.
            specialize (Heq_presum p fired_transitions a).
            rewrite <- Heq_presum' in Hin_ms.
            rewrite Heq_presum in Hin_ms.
            assumption.
          }

          (* Builds MarkingHaveSameStruct (initial_marking sitpn) residual_marking' *)
          specialize (update_marking_pre_same_marking
                        sitpn residual_marking a residual_marking' Hupdate_res)
            as Hsame_struct'.
          unfold fs in Hsame_struct.
          rewrite <- Hsame_struct in Hsame_struct'.
          
          (* Finally, specializes IHpg. *)
          specialize (IHpg pgroup (fired_transitions ++ [a]) residual_marking').
          rewrite <- app_assoc in IHpg.
          specialize (@IHpg Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                            Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
                            Hin_pgs Hin_fpg_app His_dec_tl Hnodup_app
                            Hincl_a_sf Hhigh_w_sf' Hresid'_m Hsame_struct')
            as Hsitpn_fire_aux_ex.

          (* Explodes Hsitpn_fire_aux_ex. *)
          inversion_clear Hsitpn_fire_aux_ex as (final_fired & Hsitpn_fire_aux_w).
          inversion_clear Hsitpn_fire_aux_w as (Hsitpn_fire_aux & Hw);
            inversion_clear Hw as (Hincl_ff_sf & Hin_ff).
          
          (* Instantiates the existantial variable in the goal. *)
          exists final_fired.

          split. assumption.
          split. assumption.
          intros t Hin_t_w.
          inversion_clear Hin_t_w as (Hin_t_apg & Hin_t_fs).
          inversion_clear Hin_t_apg as [ Heq_ta | Hin_t_pg ].
          {
            assert (Hin_a_fired : In a (fired_transitions ++ [a]))
              by (apply in_or_app; right; apply in_eq).
            specialize (sitpn_fire_aux_in_fired sitpn tmp_state residual_marking' (fired_transitions ++ [a])
                                                pg final_fired a Hin_a_fired Hsitpn_fire_aux)
              as Hin_a_ff.
            rewrite <- Heq_ta; assumption.
          }
          { apply (Hin_ff t (conj Hin_t_pg Hin_t_fs)). }
          
        (* (* CASE is_sensitized = Some false, then apply IHpg *) *)
        --
          (* Then, inversion Hspec and specialization of one of the spec rule, 
             to obtain In a (fired s'). *)
          inversion Hspec.
          clear H H0 H1 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12;
            rename H2 into Heq_marking, H13 into Hnot_sens_by_res.

          (* Builds SitpnIsfirable sitpn s' a *)

          assert (Heq_pls : places sitpn = fs (marking tmp_state)).
          {
            explode_well_defined_sitpn_state Hwell_def_s.
            rewrite <- Heq_m_tmp in Hwf_state_marking.
            assumption.
          }

          assert (Hperm_conditions : Permutation (conditions sitpn) (fs (cond_values tmp_state))).
          {
            explode_well_defined_sitpn_state Hwell_def_s'.
            rewrite Hperm_conds_tmp.
            rewrite Hwf_state_condv.
            reflexivity.
          }

          assert (Hin_a_transs : In a (transs sitpn)) by (deduce_in_transs; assumption).
          
          apply (sitpn_is_firable_correct_no_wd
                   tmp_state a Hwell_def_sitpn Heq_pls Hperm_conditions Hin_a_transs)
            in Hfirable.

          assert (Heq_m_tmp_s' : (marking tmp_state) = (marking s'))
            by (rewrite <- Heq_marking; assumption).
          
          specialize (sitpn_is_firable_iff_perm
                        sitpn tmp_state s' a Heq_m_tmp_s' Hperm_ditvals_tmp Hperm_conds_tmp)
            as Hequiv_firable.
          rewrite Hequiv_firable in Hfirable.

          (* Builds IsSensitized sitpn residual_marking a *)
          rewrite (not_is_sensitized_iff
                     residual_marking a Hwell_def_sitpn
                     Hsame_struct Hin_a_transs) in Hsens.

          (* Builds hypothesis about residual marking definition (the big one!!).
             To do so, we need to build:
             
             IsPrioritySet (fired s') pgroup t fired_transitions
             
             Then, we need to prove that fired_transitions is the only
             priority set defined by the IsPrioritySet relation.
             
           *)
          specialize (Hhigh_w_sf a (@in_eq Trans a pg)) as Hhigh_w_sf_a.
          assert (Hsf_w_high :
                    forall t : Trans,
                      HasHigherPriority t a pgroup /\ In t (fired s') ->
                      In t fired_transitions).
          {
            intros t Hw; elim Hw; intros Hhas_high Hin_t_ff; clear Hw.
            specialize (NoDup_remove fired_transitions pg a Hnodup_app) as Hnodup_app_rm;
              apply proj1 in Hnodup_app_rm.

            (* Explodes HasHigherpriority to obtain In t pgroup. *)
            unfold HasHigherPriority in Hhas_high.
            inversion_clear Hhas_high as (Hin_t_pg & Hw).
            inversion_clear Hw as (Hin_a_pg & His_pred).

            (* Then, specializes Hin_fpg_app. *)
            specialize (Hin_fpg_app t (conj Hin_t_pg Hin_t_ff)) as Hin_t_app.
            apply in_app_or in Hin_t_app; inversion_clear Hin_t_app as [Hin_t_ftrs | Hin_t_cpg].

            (* Two cases, either t ∈ fired_transitions or t ∈ (a :: pg) *)
            - assumption.
              
            (* If t ∈ (a :: pg), then two cases.  
               - t = a
               - t ∈ pg
               In both cases, contradicts IsPredInNodupList t a pgroup. *)
              
            - inversion_clear Hin_t_cpg as [Heq_ta | Hin_t_tl].

              (* Case t = a *)
              + unfold IsPredInNoDupList in His_pred.
                rewrite Heq_ta in His_pred;
                  apply proj1 in His_pred;
                  elim His_pred; reflexivity.

              (* Case In t pg. *)
              +

                (* Builds ~IsPredInNoDuplist t a (a :: pg) *)
                assert (Hnot_is_pred : ~IsPredInNoDupList t a (a :: pg)) by
                    apply not_is_pred_in_list_if_hd.
                specialize (not_is_pred_in_dec_list His_dec Hin_t_tl) as Hnot_is_pred_in_pg.
                contradiction.
          }
          
          assert (Hhigh_sf_iff :
                    forall t : Trans,
                      HasHigherPriority t a pgroup /\ In t (fired s') <->
                      In t fired_transitions) by (intros t'; split; [ auto | auto ]).
          clear Hsf_w_high.

          (* Builds NoDup fired_transitions *)
          specialize (nodup_app fired_transitions (a :: pg) Hnodup_app) as Hnodup_ftrs;
            apply proj1 in Hnodup_ftrs.
          
          (* Builds residual marking definition hypothesis. *)

          assert (Hresm_def :
                    forall pr : list Trans,
                      IsPrioritySet (fired s') pgroup a pr ->
                      forall (p : Place) (n : nat),
                        In (p, n) (marking s') -> In (p, n - pre_sum sitpn p pr) residual_marking).
          {
            intros pr His_prior p n Hin_m'.
            rewrite Heq_m_tmp in Hresid_m.
            rewrite Heq_marking in Hresid_m.
            specialize (Hresid_m p n Hin_m') as Hin_resm.

            unfold IsPrioritySet in His_prior;
              inversion_clear His_prior as (Hnodup_pr & Hdef_pr).
            
            assert (Heq_pr_ftrs: forall t : Trans, In t pr <-> In t fired_transitions).
            {
              intros t;
                split;
                intro Hin;
                ((rewrite <- (Hdef_pr t) in Hin; rewrite (Hhigh_sf_iff t) in Hin)
                 || (rewrite <- (Hhigh_sf_iff t) in Hin; rewrite (Hdef_pr t) in Hin));
                assumption.                            
            }
            
            specialize (pre_sum_eq_iff_incl
                          sitpn p pr fired_transitions Hnodup_pr
                          Hnodup_ftrs Heq_pr_ftrs)
              as Heq_presum.
            rewrite Heq_presum.
            assumption.
          }
          
          (* Specializes the spec rule in Hnot_sens_by_res to obtain In a (fired s'). *)
          deduce_in_from_is_dec_list_cons His_dec as Hin_a_pg.
          rewrite Heq_marking in Hnot_sens_by_res.
          specialize (Hnot_sens_by_res
                        pgroup a residual_marking Hin_pgs Hin_a_pg
                        Hfirable Hsame_struct Hresm_def Hsens) as Hnot_in_a_sf.

          (* Build hypotheses to specialize IHpg *)
          
          specialize (is_dec_list_cons_cons His_dec) as His_dec_tl.
          apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.

          assert (Hin_fpg_app' :
                    forall t : Trans, In t pgroup /\ In t (fired s') ->
                                      In t (fired_transitions ++ pg)).
          {
            intros t Hin_t_w.
            specialize (Hin_fpg_app t Hin_t_w) as Hin_t_fpg.
            apply in_app_or in Hin_t_fpg.
            inversion_clear Hin_t_fpg as [ Hin_t_ftrs | Hin_t_pg ].
            - apply in_or_app; left; assumption.
            - inversion_clear Hin_t_pg as [ Heq_ta | Hin_t_pgtl ].
              + inversion_clear Hin_t_w as ( Hin_t_pg & Hin_t_fs ).
                rewrite Heq_ta in Hnot_in_a_sf; contradiction.
              + apply in_or_app; right; assumption.
          }
          
          assert (Hhigh_w_sf' :
                    forall t : Trans,
                      In t pg ->
                      forall t' : Trans,
                        In t' fired_transitions ->
                        HasHigherPriority t' t pgroup /\ In t' (fired s')).
          {
            intros t Hin_t_pg;
              apply in_cons with (a := a) in Hin_t_pg;
              apply (Hhigh_w_sf t Hin_t_pg).
          }
          
          specialize (@IHpg pgroup fired_transitions residual_marking
                            Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                            Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
                            Hin_pgs Hin_fpg_app' His_dec_tl Hnodup_app Hincl_sf
                            Hhigh_w_sf' Hresid_m Hsame_struct) as Hfire_aux_ex.

          (* Explodes the newly-built hypothesis. *)
          
          inversion_clear Hfire_aux_ex as (final_fired & Hfire_aux_w).
          exists final_fired.
          elim Hfire_aux_w; clear Hfire_aux_w; intros Hfire_aux Hfire_aux_w.
          elim Hfire_aux_w; clear Hfire_aux_w; intros Hincl_ff Hin_ff.

          (* Then, solves each branch of the conjunction. *)
          
          repeat (split; auto).

          (* Solves the last branch here. *)
          
          intros t Hin_t_w; elim Hin_t_w; clear Hin_t_w; intros Hin_t_pg Hin_t_fs.        
          inversion_clear Hin_t_pg as [Heq_ta | Hin_t_tl].
          
          (* Using spec to prove that t ∉ (fired s'). *)
          ++ rewrite Heq_ta in Hnot_in_a_sf; contradiction.
           
          (* Applies result for IHpg. *)
          ++ apply (Hin_ff t (conj Hin_t_tl Hin_t_fs)).
          
      (* CASE sitpn_is_firable = Some false. *)
      +
        (* First, we have to specialize one of the spec rules to show
           that a ∉ (fired s'). Very useful in the following proof. *)

        inversion Hspec.
        clear H H0 H1 H3 H4 H5 H6 H7 H8 H9 H10 H12 H13.
        rename H11 into Hnot_firable, H2 into Heq_marking.

        (* We need to specialize not_sitpn_is_firable_correct_no_wd 
           to get SitpnIsFirable sitpn tmp_state t. *)

        assert (Heq_pls : places sitpn = fs (marking tmp_state)).
        {
          explode_well_defined_sitpn_state Hwell_def_s.
          rewrite <- Heq_m_tmp in Hwf_state_marking.
          assumption.
        }

        assert (Hperm_conditions : Permutation (conditions sitpn) (fs (cond_values tmp_state))).
        {
          explode_well_defined_sitpn_state Hwell_def_s'.
          rewrite Hperm_conds_tmp.
          rewrite Hwf_state_condv.
          reflexivity.
        }

        assert (Hnodup_fs_ditvals : NoDup (fs (d_intervals tmp_state))).
        {
          explode_well_defined_sitpn_state Hwell_def_s'.
          rewrite Hperm_ditvals_tmp.
          assumption.
        }

        assert (Hin_a_transs : In a (transs sitpn)) by (deduce_in_transs; assumption).
        
        specialize (not_sitpn_is_firable_correct_no_wd
                      Hwell_def_sitpn Heq_pls Hperm_conditions
                      Hnodup_fs_ditvals Hin_a_transs Hfirable)
          as Hnfirable.

        (* Rewrites ~SitpnIsFirable tmp_state with ~SitpnIsFirable s'
           leveraging the fact that tmp_state and s' are almost equal. *)

        assert (Heq_m_tmp_s' : (marking tmp_state) = (marking s'))
          by (rewrite <- Heq_marking; assumption).
        
        specialize (sitpn_is_firable_iff_perm
                      sitpn tmp_state s' a Heq_m_tmp_s' Hperm_ditvals_tmp Hperm_conds_tmp)
          as Hequiv_nfirable.
        rewrite Hequiv_nfirable in Hnfirable.

        (* Builds In a pgroup before specializing Hnot_firable. *)
        deduce_in_from_is_dec_list_cons His_dec as Hin_a_pg.
        
        specialize (Hnot_firable pgroup a Hin_pgs Hin_a_pg Hnfirable) as Hnot_in_a_sf.
        
        (* Build hypotheses to specialize IHpg *)
        
        specialize (is_dec_list_cons_cons His_dec) as His_dec_tl.
        apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.

        assert (Hin_fpg_app' :
                  forall t : Trans, In t pgroup /\ In t (fired s') ->
                                    In t (fired_transitions ++ pg)).
        {
          intros t Hin_t_w.
          specialize (Hin_fpg_app t Hin_t_w) as Hin_t_fpg.
          apply in_app_or in Hin_t_fpg.
          inversion_clear Hin_t_fpg as [ Hin_t_ftrs | Hin_t_pg ].
          - apply in_or_app; left; assumption.
          - inversion_clear Hin_t_pg as [ Heq_ta | Hin_t_pgtl ].
            + inversion_clear Hin_t_w as ( Hin_t_pg & Hin_t_fs ).
              rewrite Heq_ta in Hnot_in_a_sf; contradiction.
            + apply in_or_app; right; assumption.
        }
        
        assert (Hhigh_w_sf' :
                  forall t : Trans,
                    In t pg ->
                    forall t' : Trans,
                      In t' fired_transitions ->
                      HasHigherPriority t' t pgroup /\ In t' (fired s')).
        {
          intros t Hin_t_pg;
            apply in_cons with (a := a) in Hin_t_pg;
            apply (Hhigh_w_sf t Hin_t_pg).
        }
        
        specialize (@IHpg pgroup fired_transitions residual_marking
                          Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                          Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
                          Hin_pgs Hin_fpg_app' His_dec_tl Hnodup_app Hincl_sf
                          Hhigh_w_sf' Hresid_m Hsame_struct) as Hfire_aux_ex.

        (* Explodes the newly-built hypothesis. *)
        
        inversion_clear Hfire_aux_ex as (final_fired & Hfire_aux_w).
        exists final_fired.
        elim Hfire_aux_w; clear Hfire_aux_w; intros Hfire_aux Hfire_aux_w.
        elim Hfire_aux_w; clear Hfire_aux_w; intros Hincl_ff Hin_ff.

        (* Then, solves each branch of the conjunction. *)
        
        repeat (split; auto).

        (* Solves the last branch here. *)
        
        intros t Hin_t_w; elim Hin_t_w; clear Hin_t_w; intros Hin_t_pg Hin_t_fs.        
        inversion_clear Hin_t_pg as [Heq_ta | Hin_t_tl].
        
        (* Using spec to prove that t ∉ (fired s'). *)
        -- rewrite Heq_ta in Hnot_in_a_sf; contradiction.
           
        (* Applies result for IHpg. *)
        -- apply (Hin_ff t (conj Hin_t_tl Hin_t_fs)).
  Qed.
  
  (** Completeness lemma for sitpn_map_fire_aux. *)

  Lemma sitpn_map_fire_complete_aux :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (tmp_state : SitpnState)
           (pgroups : list (list Trans))
           (fired_trs : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->
      
      (* Properties of tmp_state. *)
      (marking tmp_state) = (marking s) ->
      Permutation (d_intervals tmp_state) (d_intervals s') ->
      Permutation (cond_values tmp_state) (cond_values s') ->

      (* Properties of fired_trs and pgroups. *)
      IsDecListCons pgroups (priority_groups sitpn) ->
      NoDup (fired_trs ++ concat pgroups) ->
      incl s'.(fired) (fired_trs ++ concat pgroups) ->
      incl fired_trs s'.(fired) ->
      
      exists final_fired : list Trans,
        sitpn_map_fire_aux sitpn tmp_state fired_trs pgroups = Some final_fired
        /\ Permutation final_fired (fired s').
  Proof.
    intros sitpn s s' time_value env tmp_state pgroups;
      induction pgroups;
      intros fired_trs Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
             His_dec Hnodup_app Hincl_sf Hincl_f.
    
    (* BASE CASE, pgroups = []. *)
    - simpl; exists fired_trs.
      split.
      + reflexivity.
      + simpl in Hincl_sf; rewrite app_nil_r in Hincl_sf.
        simpl in Hnodup_app; rewrite app_nil_r in Hnodup_app.
        explode_well_defined_sitpn_state Hwell_def_s'.

        (* NoDup l ∧ NoDup l' ∧ incl l l' ∧ incl l' l ⇒ Permutation l l' *)
        assert (Hincl_iff : forall a : Trans, In a fired_trs <-> In a (fired s'))
          by (intros a; split; [ specialize (Hincl_f a); assumption |
                                 specialize (Hincl_sf a); assumption ]). 
        apply (NoDup_Permutation Hnodup_app Hnodup_state_fired Hincl_iff).

    (* INDUCTION CASE *)
    - simpl; unfold sitpn_fire.
      
      (* We need to specialize sitpn_fire_aux_complete to rewrite
         sitpn_fire_aux in the goal. Then, we'll be able to build premises
         necessary to apply IHpgroups. *)

      (* To specialize sitpn_fire_aux_complete, we need a few hypotheses: *)
      
      (* Builds In a (priority_groups sitpn) *)
      specialize (is_dec_list_cons_incl His_dec) as Hincl_a_pgs.
      assert (Hin_eq : In a (a :: pgroups)) by apply in_eq.
      specialize (Hincl_a_pgs a Hin_eq) as Hin_a_pgs; clear Hin_eq; clear Hincl_a_pgs.

      (* Builds IsDeclistcons a a *)
      assert (His_dec_refl : IsDecListCons a a) by apply IsDecListCons_refl.

      (* Builds NoDup ([] ++ a) *)
      specialize (nodup_app fired_trs (concat (a :: pgroups)) Hnodup_app) as Hnodup_a.
      apply proj2 in Hnodup_a.
      rewrite concat_cons in Hnodup_a.
      apply (nodup_app a (concat pgroups)) in Hnodup_a.
      apply proj1 in Hnodup_a.
      rewrite <- app_nil_l in Hnodup_a.

      (* Builds incl [] (fired s'). *)
      assert (Hincl_nil : incl [] (fired s')) by (intros x Hin_nil; inversion Hin_nil).

      (* Builds ∀ t ∈ a ⇒ t' ∈ [] ⇒ t' ≻ t ∧ t' ∈ (fired s'). *)
      assert (Hhigh_w_fired :
                forall t : Trans,
                  In t a ->
                  forall t' : Trans,
                    In t' [] ->
                    HasHigherPriority t' t a /\ In t' (fired s'))
        by (intros t Hin_a t' Hin_nil; inversion Hin_nil).

      (* Builds ∀ (p, n) ∈ (marking tmp_state) ⇒ (p, n - pre_sum sitpn p []) ∈ (marking s) *)
      assert (Hresid_m :
                forall (p : Place) (n : nat),
                  In (p, n) (marking tmp_state) -> In (p, n - pre_sum sitpn p []) (marking tmp_state))
        by (simpl; intros; rewrite Nat.sub_0_r; assumption).

      (* Builds places sitpn = (marking tmp_state) *)
      assert (Heq_pls : places sitpn = fs (marking tmp_state))
        by (explode_well_defined_sitpn_state Hwell_def_s;
            rewrite Heq_m_tmp;
            assumption).
      
      (* Builds ∀ t, t ∈ pgroup ∧ t ∈ (fired s') ⇒ t ∈ (fired_transitions ++ pg) *)
      assert (Hin_fpg_app :
                forall t : Trans,
                  In t a /\ In t (fired s') ->
                  In t ([] ++ a)) by (intros t Hin_t_a; apply proj1 in Hin_t_a; auto).

      (* Then, specializes sitpn_fire_aux *)
      specialize (@sitpn_fire_aux_complete
                    sitpn s s' time_value env tmp_state a a [] (marking tmp_state)
                    Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                    Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
                    Hin_a_pgs Hin_fpg_app His_dec_refl Hnodup_a Hincl_nil
                    Hhigh_w_fired Hresid_m Heq_pls) as Hsitpn_fire_aux_ex.

      (* Explodes the newly-built hypothesis. *)
      inversion_clear Hsitpn_fire_aux_ex as (fired_transitions & Hsitpn_fire_aux_w).
      elim Hsitpn_fire_aux_w; clear Hsitpn_fire_aux_w; intros Hsitpn_fire_aux Hincl_w.
      elim Hincl_w; clear Hincl_w; intros Hincl_ftrs Hin_ftrs.
      rewrite Hsitpn_fire_aux.

      (* Then, builds hypotheses to apply IHpgroups 
         with fired_transitions := fired_trs ++ fired_transitions. *)

      (* Builds IsDecListCons pgroups (priority_groups sitpn) *)
      assert (His_dec_tl : IsDecListCons pgroups (priority_groups sitpn))
        by (apply (is_dec_list_cons_cons His_dec)).
      
      (* Builds NoDup ((fired_trs ++ fired_transitions) ++ (concat pgroups)) *)
      assert (Hnodup_ftrs : NoDup ((fired_trs ++ fired_transitions) ++ (concat pgroups))).
      {
        rewrite concat_cons in Hnodup_app.
        specialize (sitpn_fire_aux_nodup_fired
                      sitpn tmp_state (marking tmp_state) [] a fired_transitions
                      Hwell_def_sitpn Hnodup_a
                      Hsitpn_fire_aux) as Hnodup_incl_w.
        inversion_clear Hnodup_incl_w as (Hnodup_ftrs & Hincl_ftrs_a).
        rewrite <- app_assoc.
        apply (nodup_app_incl
                 fired_trs a (concat pgroups) fired_transitions
                 Hnodup_app Hnodup_ftrs Hincl_ftrs_a).
      }

      (* Builds (fired s') ⊆ ((fired_trs ++ fired_transitions) ++ concat pgroups) *)
      assert (Hincl_fired_app : incl (fired s') ((fired_trs ++ fired_transitions) ++ concat pgroups)).
      {
        intros x Hin_x_fsp.
        rewrite <- app_assoc.
        specialize (Hincl_sf x Hin_x_fsp).
        apply in_app_or in Hincl_sf.
        inversion_clear Hincl_sf as [Hin_x_f | Hin_x_concat].
        -- apply in_or_app; left; assumption.
        -- rewrite concat_cons in Hin_x_concat.
           apply in_app_or in Hin_x_concat; inversion_clear Hin_x_concat as [Hin_x_a | Hin_x_conc].
           {
             specialize (Hin_ftrs x (conj Hin_x_a Hin_x_fsp));
               apply in_or_app; right; apply in_or_app; left; assumption.
           }
           { do 2 (apply in_or_app; right); assumption. }           
      }

      (* Builds (fired_trs ++ fired_transitions) ⊆ (fired s') *)
      assert (Hincl_app_fired : incl (fired_trs ++ fired_transitions) (fired s')).
      {
        intros x Hin_x_app;
          apply in_app_or in Hin_x_app;
          inversion_clear Hin_x_app as [Hin_x_fired | Hin_x_ftrs];
          [ apply (Hincl_f x Hin_x_fired) | apply (Hincl_ftrs x Hin_x_ftrs) ].
      }      
      
      (* Then apply IHpgroups with fired_transitions := fired_transitions ++ fired_trs *)
      apply (@IHpgroups (fired_trs ++ fired_transitions)
                        Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                        Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
                        His_dec_tl Hnodup_ftrs Hincl_fired_app Hincl_app_fired).
  Qed.
    
  (** Completeness lemma for sitpn_map_fire. *)

  Lemma sitpn_map_fire_complete :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (tmp_state : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env falling_edge ->
      
      (* Properties of tmp_state. *)
      (marking tmp_state) = (marking s) ->
      Permutation (d_intervals tmp_state) (d_intervals s') ->
      Permutation (cond_values tmp_state) (cond_values s') ->
      
      exists final_fired : list Trans,
        sitpn_map_fire sitpn tmp_state = Some final_fired
        /\ Permutation final_fired (fired s').
  Proof.
    intros sitpn s s' time_value env tmp_state Hwell_def_sitpn
           Hwell_def_s Hwell_def_s' Hspec Heq_m_tmp
           Hperm_ditvals_tmp Hperm_conds_tmp.

    unfold sitpn_map_fire.

    (* Strategy: build premises to apply sitpn_map_fire_aux_complete. *)

    assert (His_dec_refl : IsDecListCons (priority_groups sitpn) (priority_groups sitpn))
      by (apply IsDecListCons_refl).
    assert (Hnodup_app : NoDup ([] ++ concat (priority_groups sitpn))).
    {
      explode_well_defined_sitpn;
        assert (Hnodup_app := Hno_inter);
        unfold NoIntersectInPriorityGroups in Hnodup_app;
        rewrite <- app_nil_l in Hnodup_app;
        assumption.
    }        
    assert (Hincl_f_concat : incl (fired s') (concat (priority_groups sitpn))).
    {
      explode_well_defined_sitpn;
        explode_well_defined_sitpn_state Hwell_def_s';
        unfold NoUnknownInPriorityGroups in Hno_unk_pgroups;
        intros a Hin_fired_sp;
        apply Hincl_state_fired_transs in Hin_fired_sp;
        rewrite <- Hno_unk_pgroups;
        assumption.
    }
    assert (Hincl_nil : incl [] (fired s')) by (intros a Hin_nil; inversion Hin_nil).
    
    (* Applies sitpn_map_fire_aux with then newly-built premises. *)
    apply (sitpn_map_fire_complete_aux
             sitpn s s' time_value env tmp_state (priority_groups sitpn) []
             Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Heq_m_tmp Hperm_ditvals_tmp Hperm_conds_tmp
             His_dec_refl Hnodup_app Hincl_f_concat Hincl_nil).
  Qed.
  
End SitpnMapFireComplete.

        
