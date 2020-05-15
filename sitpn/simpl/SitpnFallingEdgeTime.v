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

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import simpl.SitpnTactics.



(* Import Sitpn core lemmas. *)

Require Import simpl.SitpnCoreLemmas.

(** * Falling Edge Lemmas about Time-Related Semantics Rules. *)


(** ** Reset dynamic time intervals on falling edge. *)

Section SitpnFallingEdgeResetDItvals.

  (** A couple [(t, ditval)] in [new_d_itvals] is in the list
      [ditvals'] returned by [update_time_intervals sitpn s d_itvals new_d_itvals]. *)

  Lemma update_time_intervals_in_newditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval))
           (t : Trans)
           (d : DynamicTimeInterval),
      In (t, d) new_d_itvals ->
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      In (t, d) d_itvals'.
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' t' d Hin_td_newditvals Hfun;

      (* BASE CASE. *)
      (injection Hfun as Heq; rewrite <- Heq; assumption)
      
      
      (* OTHERS CASES *)
      || (apply or_introl
            with (B := (In (t', d) [(t, active (dec_itval stc_itval))]))
           in Hin_td_newditvals;
          apply in_or_app in Hin_td_newditvals;
          apply (IHo d_itvals' t' d Hin_td_newditvals Hfun))

      || (apply or_introl
            with (B := (In (t', d) [(t, active (dec_itval itval))]))
           in Hin_td_newditvals;
          apply in_or_app in Hin_td_newditvals;
          apply (IHo d_itvals' t' d Hin_td_newditvals Hfun))

      || (apply or_introl
            with (B := (In (t', d) [(t, blocked)]))
           in Hin_td_newditvals;
          apply in_or_app in Hin_td_newditvals;
          apply (IHo d_itvals' t' d Hin_td_newditvals Hfun))

      (* ERROR CASES *)
      || (inversion Hfun).
  Qed.


  (** Auxialiary lemma to prove update_time_intervals_reset_ditvals *)
  
  Lemma update_time_intervals_in_newditvals_and_rew:
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals new_d_itvals : list (Trans * DynamicTimeInterval))
           (t : Trans)
           (stc_itval : TimeInterval)
           (d_itvals' : list (Trans * DynamicTimeInterval))
           (dyn_itval : DynamicTimeInterval) 
           (t' : Trans)
           (d : DynamicTimeInterval)
           (sitval : TimeInterval),
      s_intervals sitpn t = Some stc_itval ->
      Some sitval = s_intervals sitpn t' ->
      (t, dyn_itval) = (t', d) ->
      update_time_intervals sitpn s d_itvals (new_d_itvals ++ [(t, active (dec_itval stc_itval))]) = Some d_itvals' ->
      In (t', active (dec_itval sitval)) d_itvals'.
  Proof.
    intros sitpn s d_itvals new_d_itvals t stc_itval d_itvals'
           dyn_itval t' d sitval Heq_stc_itval Heq_some_sitval Heq_tt'_dditval Hfun.

    injection Heq_tt'_dditval as Heq_tt' Heq_dditval.

    (* Builds (t, active (dec_itval stc_itval)) ∈ 
         (new_d_itvals ++ [(t, active (dec_itval stc_itval))]),
         necessary to specialize update_time_intervals_in_newditvals. *)
    assert (Hin_newditvals_app :
              In (t, active (dec_itval stc_itval))
                 (new_d_itvals ++ [(t, active (dec_itval stc_itval))]))
      by (apply in_or_app; right; apply in_eq).    
    
    (* Specializes update_time_intervals_in_newditvals. *)
    specialize (update_time_intervals_in_newditvals
                  sitpn s d_itvals (new_d_itvals ++ [(t, active (dec_itval stc_itval))])
                  d_itvals' t (active (dec_itval stc_itval)) Hin_newditvals_app Hfun)
      as Hin_ditvals'.

    (* Rewrites sitval \w stc_itval and t \w t'. *)
    rewrite Heq_tt' in Heq_stc_itval.
    assert (Heq_some_sitval' : Some sitval = Some stc_itval)
      by (transitivity (s_intervals sitpn t'); [assumption | assumption]).
    injection Heq_some_sitval' as Heq_sitval.
    rewrite Heq_tt' in Hin_ditvals'.
    rewrite Heq_sitval.
    assumption.
  Qed.    
    
  (** All transitions referenced in the [d_itvals] list that are
      either not sensitized or sensitized and reset or fired 
      are in the [d_itvals'] returned by the [update_time_intervals]
      function. *)
  
  Lemma update_time_intervals_reset_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      incl (fst (split d_itvals)) (transs sitpn) ->
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      (forall (t : Trans)
              (itval : TimeInterval),
          In t (fst (split d_itvals)) ->
          (~IsSensitized sitpn s.(marking) t \/
           (IsSensitized sitpn s.(marking) t /\ (In (t, true) s.(reset) \/ In t s.(fired)))) ->
          Some itval = (s_intervals sitpn t) ->
          In (t, active (dec_itval itval)) d_itvals').
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
             Hfun t' sitval Hin_fs_ditvals Hnotsens_or_sens Hsome_itval.

    (* BASE CASE *)
    - inversion Hin_fs_ditvals.

    (* CASE (is_sens t M = Some true) ∧ (in_list t fired) *)
    - specialize (in_fst_split_in_pair t' ((t, dyn_itval) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].

      (* Case (t, dyn_itval) = (t', d) *)
      + apply (update_time_intervals_in_newditvals_and_rew
                 sitpn s tl new_d_itvals t stc_itval d_itvals' dyn_itval t' d sitval
                 e1 Hsome_itval Heq_tt'_dditval Hfun).
        
      (* Case (t', d) ∈ tl, apply IH. *)
      + specialize (in_fst_split t' d tl Hin_tl) as Hin_fs_tl;
          rewrite fst_split_cons_app in Hincl_ditvals_transs;
          simpl in Hincl_ditvals_transs;
          apply incl_cons_inv in Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' sitval Hin_fs_tl Hnotsens_or_sens Hsome_itval).

    (* CASE (is_sens t M = Some true) 
            ∧ (in_list t fired) = Some false
            ∧ get_value t reset = Some true *)
    - specialize (in_fst_split_in_pair t' ((t, dyn_itval) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].

      (* Case (t, dyn_itval) = (t', d) *)
      + apply (update_time_intervals_in_newditvals_and_rew
                 sitpn s tl new_d_itvals t stc_itval d_itvals' dyn_itval t' d sitval
                 e1 Hsome_itval Heq_tt'_dditval Hfun).
        
      (* Case (t', d) ∈ tl, apply IH. *)
      + specialize (in_fst_split t' d tl Hin_tl) as Hin_fs_tl;
          rewrite fst_split_cons_app in Hincl_ditvals_transs;
          simpl in Hincl_ditvals_transs;
          apply incl_cons_inv in Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' sitval Hin_fs_tl Hnotsens_or_sens Hsome_itval).
        
    (* CASE is_sens t M = Some true
            ∧  in_list t fired = Some false  
            ∧  get_value t reset = Some false
            ∧  dyn_itval = active itval. *)
    - specialize (in_fst_split_in_pair t' ((t, active itval) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].
        
      (* Case (t, active itval) = (t', d) *)
      + injection Heq_tt'_dditval as Heq_tt' Heq_dditval.

           (* 2 subcases: 
              - t' ∉ sens(M) 
              - t' ∈ sens(M) ∧ (reset(t') ∨ t' ∈ fired *)
           inversion_clear Hnotsens_or_sens as [Hnot_sens_t' | Hsens_t'_w].

           (* Subcase t' ∉ sens(M) *)
           
           (* Strategy: specialize is_sensitized_correct and show contradiction. *)
           -- (* Builds t ∈ T *)
             specialize (Hincl_ditvals_transs t' Hin_fs_ditvals)
               as Hin_t_transs;
               rewrite <- Heq_tt' in Hin_t_transs.

             (* Builds places sitpn = fst (split (marking s)) *)
             explode_well_defined_sitpn_state Hwell_def_s.

             (* Applies is_sensitized_correct in e2, and rewrites t with t'. *)
             apply (is_sensitized_correct
                      (marking s) t Hwell_def_sitpn Hwf_state_marking Hin_t_transs) in e2.
             rewrite Heq_tt' in e2.

             (* Then contradiction. *)
             contradiction.

           (* Subcase t' ∈ sens(M) ∧ (reset(t') ∨ t' ∈ fired) *)
           -- inversion_clear Hsens_t'_w as (Hsens_t' & Hreset_or_fired_t').

              (* Two cases: reset(t') ∨ t' ∈ fired *)
              inversion_clear Hreset_or_fired_t' as [Hreset_t' | Hin_t'_fired].

              (* reset(t') *)
              ++ (* Shows a contradiction between (get_value t reset) = false and 
                   In (t', true) reset, knowing that t' = t *)
                explode_well_defined_sitpn_state Hwell_def_s.
                specialize (get_value_complete Nat.eq_dec t' (reset s) true
                                               Hnodup_state_reset Hreset_t')
                  as Hget_value_true.
                rewrite Heq_tt' in e5.
                rewrite e5 in Hget_value_true.
                inversion Hget_value_true.
              

              (* t' ∈ fired *)
              ++ apply (not_in_list_correct Nat.eq_dec (fired s) t) in e4.
                rewrite Heq_tt' in e4; contradiction.
                
      (* Case (t', d) ∈ tl *)
      + specialize (in_fst_split t' d tl Hin_tl) as Hin_fs_tl.
        rewrite fst_split_cons_app in Hincl_ditvals_transs;
          simpl in Hincl_ditvals_transs;
          apply incl_cons_inv in Hincl_ditvals_transs.
        
        apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                   Hfun t' sitval Hin_fs_tl Hnotsens_or_sens Hsome_itval).

    (* CASE is_sens t M = Some true
            ∧  in_list t fired = Some false  
            ∧  get_value t reset = Some false
            ∧  dyn_itval = blocked. *)
        
    - specialize (in_fst_split_in_pair t' ((t, blocked) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].
      
      (* Case (t, active itval) = (t', d) *)
      + injection Heq_tt'_dditval as Heq_tt' Heq_dditval.

        (* 2 subcases: 
              - t' ∉ sens(M) 
              - t' ∈ sens(M) ∧ (reset(t') ∨ t' ∈ fired *)
        inversion_clear Hnotsens_or_sens as [Hnot_sens_t' | Hsens_t'_w].

        (* Subcase t' ∉ sens(M) *)
        
        (* Strategy: specialize is_sensitized_correct and show contradiction. *)
        -- (* Builds t ∈ T *)
          apply_incl Hin_t_transs.

          (* Builds places sitpn = fst (split (marking s)) *)
          explode_well_defined_sitpn_state Hwell_def_s.

          (* Applies is_sensitized_correct in e2, and rewrites t with t'. *)
          rewrite Heq_tt' in e2;
            apply (is_sensitized_correct (marking s) t' Hwell_def_sitpn
                                         Hwf_state_marking Hin_t_transs) in e2.

          (* Then contradiction. *)
          contradiction.

        (* Subcase t' ∈ sens(M) ∧ (reset(t') ∨ t' ∈ fired) *)
        -- inversion_clear Hsens_t'_w as (Hsens_t' & Hreset_or_fired_t').

           (* Two cases: reset(t') ∨ t' ∈ fired *)
           inversion_clear Hreset_or_fired_t' as [Hreset_t' | Hin_t'_fired].

           (* reset(t') *)
           ++ (* Shows a contradiction between (get_value t reset) = false and 
                   In (t', true) reset, knowing that t' = t *)
             explode_well_defined_sitpn_state Hwell_def_s.
             specialize (get_value_complete Nat.eq_dec t' (reset s) true
                                            Hnodup_state_reset Hreset_t')
               as Hget_value_true.
             rewrite Heq_tt' in e5.
             rewrite e5 in Hget_value_true.
             inversion Hget_value_true.
             

           (* t' ∈ fired *)
           ++ apply (not_in_list_correct Nat.eq_dec (fired s) t) in e4.
              rewrite Heq_tt' in e4; contradiction.
              
      (* Case (t', d) ∈ tl *)
      + specialize (in_fst_split t' d tl Hin_tl) as Hin_fs_tl.
        rewrite fst_split_cons_app in Hincl_ditvals_transs;
          simpl in Hincl_ditvals_transs;
          apply incl_cons_inv in Hincl_ditvals_transs.
        
        apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                   Hfun t' sitval Hin_fs_tl Hnotsens_or_sens Hsome_itval).

    (* ERROR CASE, get_value t reset = None *)
    - inversion Hfun.

    (* CASE (is_sens t M = Some false) *)
    - specialize (in_fst_split_in_pair t' ((t, dyn_itval) :: tl) Hin_fs_ditvals) as Hex_in_ditvals.
      inversion_clear Hex_in_ditvals as (d & Hin_ditvals).

      (* Two cases, (t', d) = (t, dyn_itval) ∨ (t', d) ∈ tl *)
      inversion_clear Hin_ditvals as [Heq_tt'_dditval | Hin_tl].

      (* Case (t, dyn_itval) = (t', d) *)
      + apply (update_time_intervals_in_newditvals_and_rew
                 sitpn s tl new_d_itvals t stc_itval d_itvals' dyn_itval t' d sitval
                 e1 Hsome_itval Heq_tt'_dditval Hfun).
      
      (* Case (t', d) ∈ tl, apply IH. *)
      + specialize (in_fst_split t' d tl Hin_tl) as Hin_fs_tl.
        rewrite fst_split_cons_app in Hincl_ditvals_transs;
          simpl in Hincl_ditvals_transs;
          apply incl_cons_inv in Hincl_ditvals_transs.
        
        apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                   Hfun t' sitval Hin_fs_tl Hnotsens_or_sens Hsome_itval). 
      
    (* ERROR CASE, is_sens = None *)
    - inversion Hfun.

    (* ERROR CASE, (s_intervals sitpn t) = None *)
    - inversion Hfun.
  Qed.
      
  (** All transitions that are not sensitized by the marking at state
      [s], or that are sensitized and either received a reset order or
      were fired at the last cycle, have their dynamic time intervals
      reset. *)

  Lemma sitpn_falling_edge_reset_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (t : Trans)
              (itval : TimeInterval),
          In t (fst (split s.(d_intervals))) ->
          (~IsSensitized sitpn s.(marking) t \/
           (IsSensitized sitpn s.(marking) t /\ (In (t, true) s.(reset) \/ In t s.(fired)))) ->
          Some itval = (s_intervals sitpn t) ->
          In (t, active (dec_itval itval)) s'.(d_intervals)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun;

      (* GENERAL CASE. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;

       (* Builds incl (fst (split (d_intervals s))) (transs sitpn) 
         to apply update_time_intervals_reset_ditvals. *)
       assert (Hincl_ditvals_transs : incl (fst (split (d_intervals s))) (transs sitpn))
         by (explode_well_defined_sitpn_state Hwell_def_s;
             intros t Hin_t_ditvals;
             rewrite <- (Hwf_state_ditvals t) in Hin_t_ditvals;
             apply proj1 in Hin_t_ditvals;
             assumption);
       
       (* Applies update_time_intervals_reset_ditvals *)
       apply (update_time_intervals_reset_ditvals
                sitpn s (d_intervals s) [] d_intervals'
                Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs e))
        
      (* ERROR CASE *)
      || (inversion Hfun).
  Qed.

End SitpnFallingEdgeResetDItvals.

(** ** Increment dynamic time intervals on falling edge. *)

Section SitpnFallingEdgeIncDItvals.

  (** All transitions referenced in the [d_itvals] list that are
      sensitized and neither reset nor fired are associated with an
      incremented time interval in the [d_itvals'] returned by the
      [update_time_intervals] function. *)
  
  Lemma update_time_intervals_inc_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      incl (fst (split d_itvals)) (transs sitpn) ->
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      forall (t : Trans)
             (itval : TimeInterval),
        In (t, active itval) d_itvals ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, active (dec_itval itval)) d_itvals'.
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs Hfun
             t' interval Hin_ditvals_t Hsens_t Hno_reset_t Hnot_in_fired_t.

    (* BASE CASE *)
    - inversion Hin_ditvals_t.

    (* INDUCTIVE CASE *)

    (* CASE is_sens t' ∧ t' ∈ fired. *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].

      (* Case (t, active interval) = (t', dyn_itval), 
         then t ∈ fired ∧ t ∉ fired ⇒ contradiction *)
      + injection Heq_tt'_itval as Heq_tt' Heq_ditval_aitval.
        apply (in_list_correct Nat.eq_dec (fired s) t) in e4.
        rewrite Heq_tt' in e4.
        contradiction.

      (* Case (t, active interval) ∈ tl, then applies IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' interval Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* CASE is_sensitized t' ∧ (t', true) ∈ s.(reset) *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].

      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt' Heq_ditval_aitval.

        (* Builds In (t, true) (reset s) from get_value t (reset s) = true *)
        apply (get_value_correct Nat.eq_dec t (reset s)) in e5.

        (* Specializes nodup_same_pair to obtain a contradiction. *)
        rewrite <- Heq_tt' in Hno_reset_t.
        explode_well_defined_sitpn_state Hwell_def_s.
        assert (Heq_fs_pair : fst (t, true) = fst (t, false)) by auto.
        specialize (nodup_same_pair (reset s) Hnodup_state_reset
                                    (t, true) (t, false) e5 Hno_reset_t Heq_fs_pair)
          as Heq_pair.
        injection Heq_pair as Heq_true_false; inversion Heq_true_false.

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' interval Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* CASE is_sens t' ∧ 
            t' ∉ (fired s) ∧ 
            (t', false) ∈ (reset s) ∧ 
            ditval ≠ ψ *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].

      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt' Heq_ditval_aitval.

        (* Necessary to apply update_time_intervals_in_newditvals *)
        assert (Hin_newditvals:
                  In (t, active (dec_itval itval)) (new_d_itvals ++ [(t, active (dec_itval itval))]))
          by (apply in_or_app; right; apply in_eq).

        
        rewrite <- Heq_tt'; rewrite <- Heq_ditval_aitval.
        apply (update_time_intervals_in_newditvals
                 sitpn s tl (new_d_itvals ++ [(t, active (dec_itval itval))]) d_itvals'
                 t (active (dec_itval itval)) Hin_newditvals Hfun).

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' interval Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* CASE is_sens t' ∧ 
            t' ∉ (fired s) ∧ 
            (t', false) ∈ (reset s) ∧ 
            ditval = ψ *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].
      
      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt' Heq_active_blocked.
        inversion Heq_active_blocked.

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' interval Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* ERROR CASE, get_value = None *)
    - inversion Hfun.

    (* CASE is_sens t' = false *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].
      
      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt' Heq_ditval_aitval.
      
        (* Builds t ∈ (fs (t, ditval) :: tl) *)
        assert (Hin_t_fs_ditvals: In t (fst (split ((t, dyn_itval) :: tl))))
          by (rewrite fst_split_cons_app; simpl; left; reflexivity).
        
        (* Builds t ∈ T *)
        apply_incl Hin_t_transs.

        (* Builds places sitpn = fst (split (marking s)) *)
        explode_well_defined_sitpn_state Hwell_def_s.

        (* Applies is_sensitized_correct in e2, and rewrites t with t'. *)
        rewrite (not_is_sensitized_iff (marking s) t Hwell_def_sitpn
                                       Hwf_state_marking Hin_t_transs) in e2.

        (* Rewrite e2 then contradiction with Hsens_t. *)
        rewrite Heq_tt' in e2; contradiction.

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' interval Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).
        
    (* ERROR CASE is_sensitized = None *)
    - inversion Hfun.

    (* ERROR CASE s_intervals = None *)
    - inversion Hfun.
  Qed.
  
  (** All transitions that are sensitized by the marking at state
      [s], and neither received a reset order nor
      were fired at the last cycle, have their dynamic time intervals
      incremented. *)

  Lemma sitpn_falling_edge_inc_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (t : Trans)
              (itval : TimeInterval),
          In (t, active itval) s.(d_intervals) ->
          IsSensitized sitpn s.(marking) t ->
          In (t, false) s.(reset) ->
          ~In t s.(fired) ->
          In (t, active (dec_itval itval)) s'.(d_intervals)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun;

      (* GENERAL CASE. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       
       (* Builds incl (fst (split (d_intervals s))) (transs sitpn) 
         to apply update_time_intervals_reset_ditvals. *)
       assert (Hincl_ditvals_transs : incl (fst (split (d_intervals s))) (transs sitpn))
         by (explode_well_defined_sitpn_state Hwell_def_s;
             intros t Hin_t_ditvals;
             rewrite <- (Hwf_state_ditvals t) in Hin_t_ditvals;
             apply proj1 in Hin_t_ditvals;
             assumption);
       
       (* Applies update_time_intervals_reset_ditvals *)
       apply (update_time_intervals_inc_ditvals
                sitpn s (d_intervals s) [] d_intervals'
                Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs e))
        
      (* ERROR CASE *)
      || (inversion Hfun).
  Qed.

End SitpnFallingEdgeIncDItvals.


(** ** Blocked time intervals stay blocked on falling edge. *)

Section SitpnFallingEdgeSameBlocked.

  (** All sensitized transitions associated with a blocked interval in
      the [d_itvals] list that have neither been fired nor reset are
      associated with a blocked interval in the [d_itvals'] returned
      by the [update_time_intervals] function. *)
  
  Lemma update_time_intervals_same_blocked :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      incl (fst (split d_itvals)) (transs sitpn) ->
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->            
      forall (t : Trans),
        In (t, blocked) d_itvals ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, blocked) d_itvals'.
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs Hfun
             t' Hin_ditvals_t Hsens_t Hno_reset_t Hnot_in_fired_t.

    (* BASE CASE *)
    - inversion Hin_ditvals_t.

    (* INDUCTIVE CASE *)

    (* CASE is_sens t' ∧ t' ∈ fired. *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].

      (* Case (t, active interval) = (t', dyn_itval), 
         then t ∈ fired ∧ t ∉ fired ⇒ contradiction *)
      + injection Heq_tt'_itval as Heq_tt' Heq_ditval_aitval.
        apply (in_list_correct Nat.eq_dec (fired s) t) in e4.
        rewrite Heq_tt' in e4.
        contradiction.

      (* Case (t, active interval) ∈ tl, then applies IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* CASE is_sensitized t' ∧ (t', true) ∈ s.(reset) *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].

      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt' Heq_ditval_aitval.

        (* Builds In (t, true) (reset s) from get_value t (reset s) = true *)
        apply (get_value_correct Nat.eq_dec t (reset s)) in e5.

        (* Specializes nodup_same_pair to obtain a contradiction. *)
        rewrite <- Heq_tt' in Hno_reset_t.
        explode_well_defined_sitpn_state Hwell_def_s.
        assert (Heq_fs_pair : fst (t, true) = fst (t, false)) by auto.
        specialize (nodup_same_pair (reset s) Hnodup_state_reset
                                    (t, true) (t, false) e5 Hno_reset_t Heq_fs_pair)
          as Heq_pair.
        injection Heq_pair as Heq_true_false; inversion Heq_true_false.

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* CASE is_sens t' ∧ 
            t' ∉ (fired s) ∧ 
            (t', false) ∈ (reset s) ∧ 
            ditval ≠ ψ *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].

      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt' Heq_active_blocked.
        inversion Heq_active_blocked.

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;        
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* CASE is_sens t' ∧ 
            t' ∉ (fired s) ∧ 
            (t', false) ∈ (reset s) ∧ 
            ditval = ψ *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].
      
      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt'.

        (* Necessary to apply update_time_intervals_in_newditvals *)
        assert (Hin_newditvals:
                  In (t, blocked) (new_d_itvals ++ [(t, blocked)]))
          by (apply in_or_app; right; apply in_eq).
        
        rewrite <- Heq_tt'.
        apply (update_time_intervals_in_newditvals
                 sitpn s tl (new_d_itvals ++ [(t, blocked)]) d_itvals'
                 t blocked Hin_newditvals Hfun).

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).

    (* ERROR CASE, get_value = None *)
    - inversion Hfun.

    (* CASE is_sens t' = false *)
    - inversion_clear Hin_ditvals_t as [Heq_tt'_itval | Hin_tl_t].
      
      (* Case (t, active interval) = (t', dyn_itval) *)
      + injection Heq_tt'_itval as Heq_tt' Heq_ditval_aitval.
      
        (* Builds t ∈ (fs (t, ditval) :: tl) *)
        assert (Hin_t_fs_ditvals: In t (fst (split ((t, dyn_itval) :: tl))))
          by (rewrite fst_split_cons_app; simpl; left; reflexivity).
        
        (* Builds t ∈ T *)
        apply_incl Hin_t_transs.

        (* Builds places sitpn = fst (split (marking s)) *)
        explode_well_defined_sitpn_state Hwell_def_s.

        (* Applies is_sensitized_correct in e2, and rewrites t with t'. *)
        rewrite (not_is_sensitized_iff (marking s) t Hwell_def_sitpn
                                       Hwf_state_marking Hin_t_transs) in e2.

        (* Rewrite e2 then contradiction with Hsens_t. *)
        rewrite Heq_tt' in e2; contradiction.

      (* Case (t, active interval) ∈ tl, then apply IH. *)
      + incl_rm_hd_fs Hincl_ditvals_transs;
          apply (IHo d_itvals' Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs
                     Hfun t' Hin_tl_t Hsens_t Hno_reset_t Hnot_in_fired_t).
        
    (* ERROR CASE is_sensitized = None *)
    - inversion Hfun.

    (* ERROR CASE s_intervals = None *)
    - inversion Hfun.
  Qed.
  
  (** All transitions that are sensitized by the marking at state
      [s], and neither received a reset order nor
      were fired at the last cycle, keep the same dynamic time interval
      if it is blocked. *)

  Lemma sitpn_falling_edge_same_blocked :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (t : Trans),
          In (t, blocked) s.(d_intervals) ->
          IsSensitized sitpn s.(marking) t ->
          In (t, false) s.(reset) ->
          ~In t s.(fired) ->
          In (t, blocked) s'.(d_intervals)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun;

      (* GENERAL CASE. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       
       (* Builds incl (fst (split (d_intervals s))) (transs sitpn) 
         to apply update_time_intervals_reset_ditvals. *)
       assert (Hincl_ditvals_transs : incl (fst (split (d_intervals s))) (transs sitpn))
         by (explode_well_defined_sitpn_state Hwell_def_s;
             intros t Hin_t_ditvals;
             rewrite <- (Hwf_state_ditvals t) in Hin_t_ditvals;
             apply proj1 in Hin_t_ditvals;
             assumption);
       
       (* Applies update_time_intervals_reset_ditvals *)
       apply (update_time_intervals_same_blocked
                sitpn s (d_intervals s) [] d_intervals'
                Hwell_def_sitpn Hwell_def_s Hincl_ditvals_transs e))
        
      (* ERROR CASE *)
      || (inversion Hfun).
  Qed.

End SitpnFallingEdgeSameBlocked.
