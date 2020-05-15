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
Require Import simpl.SitpnTactics.
Require Import simpl.SitpnCoreLemmas.

(* Import lemmas about well-definition. *)

Require Import simpl.SitpnWellDefMarking.

(* Import lemmas about marking. *)

Require Import simpl.SitpnRisingEdgeMarking.

(** * Lemmas about reset orders on rising edge.  *)

Section SitpnRisingEdgeDecideReset.

  (** All couple (Trans * bool) that are in [reset_orders] are in their
      [reset_orders'] list returned by [get_blocked_itvals_and_reset_orders]. *)
  
  Lemma get_blocked_and_reset_in_reset :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval))
           (t : Trans)
           (b : bool),
      In (t, b) reset_orders ->
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      In (t, b) reset_orders'.
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' t' b Hin_reset Hfun;

      (* deduce_goal is applied to induction cases. *)
      let deduce_goal reset_order := (assert (Hin_app : In (t', b) (reset_orders ++ [(t, reset_order)]))
                                       by (apply in_or_app; left; assumption);
                                      apply (IHo reset_orders' d_itvals' t' b Hin_app Hfun)) in
      (
        (* IND. CASES *)
        deduce_goal true || deduce_goal false
                                        
        (* BASE CASE *)
        || (injection Hfun as Heq_reset Heq_ditvals;
            rewrite Heq_reset in Hin_reset;
            assumption)
             
        (* ERROR CASES *)
        || inversion Hfun
      ).
  Qed.

  (** All transitions that are not sensitized by the transient marking 
      are reset in the reset_orders' list returned by 
      [get_blocked_itvals_and_reset_orders]. *)
    
  Lemma get_blocked_and_reset_decide_reset :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      places sitpn = fst (split transient_marking) ->
      IsDecListCons d_itvals (d_intervals s) ->
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      forall t : Trans,
        In t (fst (split d_itvals)) ->
        ~IsSensitized sitpn transient_marking t ->
        In (t, true) reset_orders'.
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' Hwell_def_sitpn Hwell_def_s
             Heq_places_tm His_dec_ditvals
             Hfun t' Hin_fs_ditvals Hnot_sens_t';
      
      (
        (* BASE CASE, ditvals = [] *)
        (simpl in Hin_fs_ditvals; inversion Hin_fs_ditvals)

        ||

        (* IND. CASES *)

        (* CASE is_sens = true  *)
        (rewrite fst_split_cons_app in Hin_fs_ditvals;
         inversion_clear Hin_fs_ditvals as [Heq_tt' | Hin_t'_tl];

         (* Case t = t' *)
         
         (* Builds premises to specialize is_sensitized_correct
            and to show a contradiction. *)
         [ specialize (is_dec_list_cons_incl His_dec_ditvals) as Hincl_ditvals;
           assert (Hin_ditvals : In (t, dyn_itval) ((t, dyn_itval) :: tl)) by apply in_eq;
           specialize (Hincl_ditvals (t, dyn_itval) Hin_ditvals) as Hin_fs_ditvals;
           apply in_fst_split in Hin_fs_ditvals;
           assert (Hin_t_transs : In t (transs sitpn))
             by (explode_well_defined_sitpn_state Hwell_def_s;
                 rewrite <- (Hwf_state_ditvals t) in Hin_fs_ditvals;
                 apply proj1 in Hin_fs_ditvals; assumption);

           (* Specializes is_sensitized_correct, then contradiction. *)
           specialize (@is_sensitized_correct
                         sitpn transient_marking t Hwell_def_sitpn
                         Heq_places_tm Hin_t_transs e1) as Hsens_t;
           rewrite Heq_tt' in Hsens_t;
           contradiction
         |
         
         (* Case t ∈ tl *)
         rewrite app_nil_l in Hin_t'_tl;
         apply (IHo reset_orders' d_itvals' Hwell_def_sitpn Hwell_def_s Heq_places_tm
                    (is_dec_list_cons_cons His_dec_ditvals) Hfun t' Hin_t'_tl Hnot_sens_t')
        ])
          
        ||
        
        (* CASE is_sens = false *)
        (
          let deduce_subgoal ditval :=
              (rewrite fst_split_cons_app in Hin_fs_ditvals;
               inversion_clear Hin_fs_ditvals as [Heq_tt' | Hin_t'_tl];
               
               (* Case t = t' *)
               
               (* Builds premises to specialize is_sensitized_correct
                  and to show a contradiction. *)
               [
                 assert (Hin_ttrue_reset : In (t, true) (reset_orders ++ [(t, true)]))
                 by (apply in_or_app; right; apply in_eq);
                 rewrite <- Heq_tt';
                 apply (get_blocked_and_reset_in_reset
                          sitpn s tl transient_marking (reset_orders ++ [(t , true)])
                          (new_d_itvals ++ [(t , ditval)])
                          reset_orders' d_itvals' t true Hin_ttrue_reset Hfun)
               |
               
               (* Case t ∈ tl *)
               rewrite app_nil_l in Hin_t'_tl;
               apply (IHo reset_orders' d_itvals' Hwell_def_sitpn Hwell_def_s Heq_places_tm
                          (is_dec_list_cons_cons His_dec_ditvals) Hfun t' Hin_t'_tl Hnot_sens_t')
              ]) in
          (deduce_subgoal dyn_itval || deduce_subgoal blocked)
        )
                
              || inversion Hfun
        ).
  Qed.
  
  (** All transitions disabled by the transient marking
      receive a reset order at state [s'], where
      [s'] is the state returned by [sitpn_rising_edge]. *)
  
  Lemma sitpn_rising_edge_decide_reset :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      forall (t : Trans)
             (transient_marking : list (Place * nat)),
        Permutation (places sitpn) (fs transient_marking) ->
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum sitpn p s.(fired)) transient_marking) ->
        In t sitpn.(transs) ->
        s_intervals sitpn t <> None ->
        ~IsSensitized sitpn transient_marking t ->
        In (t, true) s'.(reset).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun t transient_marking' Heq_places_tm'
             Hdef_tm' Hin_t_transs Hhas_itval_t Hnot_sens_by_tm';

      (* GENERAL CASE *)
      (injection Hfun as Hfun; rewrite <- Hfun; simpl;

       (* Builds premises to apply get_blocked_and_reset_decide_reset *)
       assert (Heq_fs_ms_tm : fst (split (marking s)) = fst (split transient_marking))
         by (specialize (map_update_marking_pre_same_marking
                           sitpn (marking s) (fired s) transient_marking e) as Heq_places_tm;
             assumption);
       
       assert (Heq_places_fs_tm : places sitpn = fst (split transient_marking))
         by (explode_well_defined_sitpn_state Hwell_def_s;
             rewrite <- Heq_fs_ms_tm;
             assumption);

       (* Specializes get_blocked_and_reset_decide_reset *)
       
       specialize (get_blocked_and_reset_decide_reset
                     sitpn s (d_intervals s) transient_marking [] [] reset' d_intervals'
                     Hwell_def_sitpn Hwell_def_s Heq_places_fs_tm (IsDecListCons_refl (d_intervals s)) e0)
         as Hin_ttrue_reset';

       (* Deduces that t ∈ (fs (d_intervals s)) to specialize
           Hin_ttrue_reset' *)
       
       assert (Hin_t_ditvals := conj Hin_t_transs Hhas_itval_t);
       explode_well_defined_sitpn_state Hwell_def_s;
       rewrite (Hwf_state_ditvals t) in Hin_t_ditvals;
       clear_well_defined_sitpn_state;

       specialize (Hin_ttrue_reset' t Hin_t_ditvals);

       (* We want to show that transient_marking and transient_marking'
           are equivalent using the lemma eq_if_eq_fs.  
         
         But first, we need some hypotheses. *)

       (* Builds: 
           ∀(a, b) ∈ (marking s) -> 
           ∃b', (a, b') ∈ transient_marking /\ (a, b') ∈ transient_marking' *)
       explode_well_defined_sitpn_state Hwell_def_s;
       deduce_nodup_state_marking;
       specialize (map_update_marking_pre_sub_pre
                     sitpn (marking s) (fired s) transient_marking
                     Hwell_def_sitpn Hnodup_fs_ms Hincl_state_fired_transs e)
         as Hdef_tm;
       clear_well_defined_sitpn_state;
       
       assert (Hin_ms_ex_in_tm :
                 forall (p : Place)
                        (n : nat),
                   In (p, n) (marking s) ->
                   exists (n' : Place), In (p, n') transient_marking /\
                                        In (p, n') transient_marking')
         by (intros p n Hin_ms;
             specialize (Hdef_tm p n Hin_ms);
             specialize (Hdef_tm' p n Hin_ms);
             exists (n - pre_sum sitpn p (fired s));
             split; [assumption | assumption]);
       
       (* Then builds: 
           Permutation (fs (marking s)) (fs transient) and  
           Permutation (fs (marking s)) (fs transient') *)
       explode_well_defined_sitpn_state Hwell_def_s;

       assert (Hperm_fs_ms_tm : Permutation (fs (marking s)) (fs transient_marking))
         by (unfold fs; rewrite Heq_fs_ms_tm; reflexivity);

       assert (Hperm_fs_ms_tm' : Permutation (fs (marking s)) (fs transient_marking'))
         by (unfold fs; rewrite <- Hwf_state_marking; rewrite <- Heq_places_tm'; reflexivity);
       
       (* Then builds, NoDup fs (marking s) ∧ NoDup fs transient ∧ NoDup fs transient' *)
       clear_well_defined_sitpn_state;
       assert (Hnodup_fs_tm : NoDup (fs transient_marking))
         by (unfold fs; rewrite <- Hperm_fs_ms_tm; assumption);
       assert (Hnodup_fs_tm' : NoDup (fs transient_marking'))
         by (unfold fs; rewrite <- Hperm_fs_ms_tm'; assumption);

       (* Then, specializes eq_if_eq_fs to add the equivalence
           hypothesis between transient and transient' in the context. *)
       specialize (equiv_if_perm_and_nodup_fs (marking s) transient_marking transient_marking'
                                              Hin_ms_ex_in_tm Hperm_fs_ms_tm Hperm_fs_ms_tm'
                                              Hnodup_fs_ms Hnodup_fs_tm Hnodup_fs_tm') as
           Heq_tm_tm';
       
       (* Now, we need to show that for all transition t, if t is
              sensitized by transient_marking then t is sensitized by
              transient_marking' *)
       assert (Hsens_iff : IsSensitized sitpn transient_marking t <->
                           IsSensitized sitpn transient_marking' t)
         by (split;
             (unfold IsSensitized;
              intros Hsens_tm p n Hin_tm';
              (rewrite <- (Heq_tm_tm' p n) in Hin_tm' || rewrite (Heq_tm_tm' p n) in Hin_tm');
              apply (Hsens_tm p n Hin_tm')));
       

       (* Then rewrite Hin_ttrue_reset', specializes it 
              the deduces the goal. *)                  
       rewrite Hsens_iff in Hin_ttrue_reset';
       specialize (Hin_ttrue_reset' Hnot_sens_by_tm');
       assumption)

      (* ERROR CASES *)
      || inversion Hfun.
  Qed.
      
End SitpnRisingEdgeDecideReset.

Section SitpnRisingEdgeDecideNoReset.

  (** All transitions that are sensitized by the transient marking 
      are not reset in the reset_orders' list returned by 
      [get_blocked_itvals_and_reset_orders]. *)
    
  Lemma get_blocked_and_reset_decide_no_reset :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      places sitpn = fst (split transient_marking) ->
      IsDecListCons d_itvals (d_intervals s) ->
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      forall t : Trans,
        In t (fst (split d_itvals)) ->
        IsSensitized sitpn transient_marking t ->
        In (t, false) reset_orders'.
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' Hwell_def_sitpn Hwell_def_s
             Heq_places_tm His_dec_ditvals
             Hfun t' Hin_fs_ditvals Hsens_t';
        
      (
        (* BASE CASE, ditvals = [] *)
        (simpl in Hin_fs_ditvals; inversion Hin_fs_ditvals)

        ||

        (* IND. CASES *)

        (* CASE is_sens = false  *)
        (rewrite fst_split_cons_app in Hin_fs_ditvals;
         inversion_clear Hin_fs_ditvals as [Heq_tt' | Hin_t'_tl];

         (* Case t = t' *)
         [
           (* Builds premises to specialize is_sensitized_correct
              and to show a contradiction. *)
           specialize (is_dec_list_cons_incl His_dec_ditvals) as Hincl_ditvals;
           assert (Hin_ditvals : In (t, dyn_itval) ((t, dyn_itval) :: tl)) by apply in_eq;
           specialize (Hincl_ditvals (t, dyn_itval) Hin_ditvals) as Hin_fs_ditvals;
           apply in_fst_split in Hin_fs_ditvals;
           assert (Hin_t_transs : In t (transs sitpn))
             by (explode_well_defined_sitpn_state Hwell_def_s;
                 rewrite <- (Hwf_state_ditvals t) in Hin_fs_ditvals;
                 apply proj1 in Hin_fs_ditvals; assumption);

           (* Specializes is_sensitized_correct, then contradiction. *)
           rewrite (@not_is_sensitized_iff
                      sitpn transient_marking t Hwell_def_sitpn
                      Heq_places_tm Hin_t_transs) in e1;
             rewrite Heq_tt' in e1;
             contradiction
           |
           
           (* Case t ∈ tl *)
           rewrite app_nil_l in Hin_t'_tl;
             apply (IHo reset_orders' d_itvals' Hwell_def_sitpn Hwell_def_s Heq_places_tm
                        (is_dec_list_cons_cons His_dec_ditvals) Hfun t' Hin_t'_tl Hsens_t')
         ])
          
        ||
        
        (* CASE is_sens = true *)
        (let deduce_subgoal ditval :=
             (rewrite fst_split_cons_app in Hin_fs_ditvals;
              inversion_clear Hin_fs_ditvals as [Heq_tt' | Hin_t'_tl];
              
              (* Case t = t' *)
              
              (* Builds premises to specialize is_sensitized_correct
                and to show a contradiction. *)
              [ assert (Hin_ttrue_reset : In (t, false) (reset_orders ++ [(t, false)]))
                by (apply in_or_app; right; apply in_eq);
                rewrite <- Heq_tt';
                apply (get_blocked_and_reset_in_reset
                         sitpn s tl transient_marking (reset_orders ++ [(t , false)])
                         (new_d_itvals ++ [(t , ditval)])
                         reset_orders' d_itvals' t false Hin_ttrue_reset Hfun)
                | 
                (* Case t ∈ tl *)
                rewrite app_nil_l in Hin_t'_tl;
                  apply (IHo reset_orders' d_itvals' Hwell_def_sitpn Hwell_def_s Heq_places_tm
                             (is_dec_list_cons_cons His_dec_ditvals) Hfun t' Hin_t'_tl Hsens_t')
             ]) in (deduce_subgoal dyn_itval || deduce_subgoal blocked))

        (* ERROR CASES *)
        || inversion Hfun
        ).
  Qed.
  
  (** All transitions disabled by the transient marking
      receive a reset order at state [s'], where
      [s'] is the state returned by [sitpn_rising_edge]. *)
  
  Lemma sitpn_rising_edge_decide_no_reset :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      forall (t : Trans)
             (transient_marking : list (Place * nat)),
        Permutation (places sitpn) (fs transient_marking) ->
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum sitpn p s.(fired)) transient_marking) ->
        In t sitpn.(transs) ->
        s_intervals sitpn t <> None ->
        IsSensitized sitpn transient_marking t ->
        In (t, false) s'.(reset).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun t transient_marking' Heq_places_tm'
             Hdef_tm' Hin_t_transs Hhas_itval_t Hsens_by_tm';

      (* GENERAL CASE *)
      (injection Hfun as Hfun; rewrite <- Hfun; simpl;

       (* Builds premises to apply get_blocked_and_reset_decide_no_reset *)
       assert (Heq_fs_ms_tm : fst (split (marking s)) = fst (split transient_marking))
         by (specialize (map_update_marking_pre_same_marking
                           sitpn (marking s) (fired s) transient_marking e) as Heq_places_tm;
             assumption);
       
       assert (Heq_places_fs_tm : places sitpn = fst (split transient_marking))
         by (explode_well_defined_sitpn_state Hwell_def_s;
             rewrite <- Heq_fs_ms_tm;
             assumption);

       (* Specializes get_blocked_and_reset_decide_no_reset *)
       specialize (get_blocked_and_reset_decide_no_reset
                     sitpn s (d_intervals s) transient_marking [] [] reset' d_intervals'
                     Hwell_def_sitpn Hwell_def_s Heq_places_fs_tm (IsDecListCons_refl (d_intervals s)) e0)
         as Hin_tfalse_reset';

       (* Deduces that t ∈ (fs (d_intervals s)) to specialize
          Hin_tfalse_reset' *)
       assert (Hin_t_ditvals := conj Hin_t_transs Hhas_itval_t);
       explode_well_defined_sitpn_state Hwell_def_s;
       rewrite (Hwf_state_ditvals t) in Hin_t_ditvals;
       clear_well_defined_sitpn_state;

       specialize (Hin_tfalse_reset' t Hin_t_ditvals);

       (* We want to show that transient_marking and transient_marking'
         are equivalent using the lemma eq_if_eq_fs.  
         
         But first, we need some hypotheses. *)

       (* Builds: 
          ∀(a, b) ∈ (marking s) -> 
          ∃b', (a, b') ∈ transient_marking /\ (a, b') ∈ transient_marking' *)
       explode_well_defined_sitpn_state Hwell_def_s;
       deduce_nodup_state_marking;
       specialize (map_update_marking_pre_sub_pre
                     sitpn (marking s) (fired s) transient_marking
                     Hwell_def_sitpn Hnodup_fs_ms Hincl_state_fired_transs e)
         as Hdef_tm;
       clear_well_defined_sitpn_state;
       
       assert (Hin_ms_ex_in_tm :
                 forall (p : Place)
                        (n : nat),
                   In (p, n) (marking s) ->
                   exists (n' : Place), In (p, n') transient_marking /\
                                        In (p, n') transient_marking')
         by (intros p n Hin_ms;
             specialize (Hdef_tm p n Hin_ms);
             specialize (Hdef_tm' p n Hin_ms);
             exists (n - pre_sum sitpn p (fired s));
             split; [assumption | assumption]);
       

       (* Then builds: 
           Permutation (fs (marking s)) (fs transient) and  
           Permutation (fs (marking s)) (fs transient') *)
       explode_well_defined_sitpn_state Hwell_def_s;

       assert (Hperm_fs_ms_tm : Permutation (fs (marking s)) (fs transient_marking))
         by (unfold fs; rewrite Heq_fs_ms_tm; reflexivity);

       assert (Hperm_fs_ms_tm' : Permutation (fs (marking s)) (fs transient_marking'))
         by (unfold fs; rewrite <- Hwf_state_marking; rewrite <- Heq_places_tm'; reflexivity);
       
       (* Then builds, NoDup fs (marking s) ∧ NoDup fs transient ∧ NoDup fs transient' *)
       clear_well_defined_sitpn_state;
       assert (Hnodup_fs_tm : NoDup (fs transient_marking))
         by (unfold fs; rewrite <- Hperm_fs_ms_tm; assumption);
       assert (Hnodup_fs_tm' : NoDup (fs transient_marking'))
         by (unfold fs; rewrite <- Hperm_fs_ms_tm'; assumption);

       (* Then, specializes eq_if_eq_fs to add the equivalence
           hypothesis between transient and transient' in the context. *)
       specialize (equiv_if_perm_and_nodup_fs (marking s) transient_marking transient_marking'
                                              Hin_ms_ex_in_tm Hperm_fs_ms_tm Hperm_fs_ms_tm'
                                              Hnodup_fs_ms Hnodup_fs_tm Hnodup_fs_tm') as
           Heq_tm_tm';
       
       (* Now, we need to show that for all transition t, if t is
              sensitized by transient_marking then t is sensitized by
              transient_marking' *)
       assert (Hsens_iff : IsSensitized sitpn transient_marking t <->
                           IsSensitized sitpn transient_marking' t)
         by (split;
             (unfold IsSensitized;
              intros Hsens_tm p n Hin_tm';
              (rewrite <- (Heq_tm_tm' p n) in Hin_tm' || rewrite (Heq_tm_tm' p n) in Hin_tm');
              apply (Hsens_tm p n Hin_tm')));

       (* Then rewrite Hin_tfalse_reset', specializes it 
              the deduces the goal. *)                  
       rewrite Hsens_iff in Hin_tfalse_reset';
       specialize (Hin_tfalse_reset' Hsens_by_tm');
       assumption)

      (* ERROR CASES *)
      || inversion Hfun.    
  Qed.
      
End SitpnRisingEdgeDecideNoReset.

(** * Lemmas about blocked intervals on rising edge. *)

Section SitpnRisingEdgeDecideBlocked.

  (** Correctness lemma for has_reached_upper_bound = false. *)
  
  Lemma not_has_reached_upper_bound_correct :
    forall (ditval : DynamicTimeInterval),
      has_reached_upper_bound ditval = false ->
      ~HasReachedUpperBound ditval.
  Proof.
    intros ditval Hfun Hhas_rub.
    unfold has_reached_upper_bound in Hfun.
    unfold HasReachedUpperBound in Hhas_rub.

    (* Cases of ditval. *)
    destruct ditval.

    (* Case ditval = active t. 
       
       Then two cases, 
       t = {| min_t := 0; max_t := pos_val 0 |} or t = {| _ |}
     *)
    - inversion_clear Hhas_rub as [Heq_active | Hcontrad].

      (* Case t = {| min_t := 0; max_t := pos_val 0 |} *)
      + injection Heq_active as Heq_active.
        rewrite Heq_active in Hfun.
        inversion Hfun.

      (* Case t = {| _ |} *)
      + inversion Hcontrad.
        
    (* Case ditval *)
    - inversion Hfun.
  Qed.

  (** If [(t, ditval)] ∈ [new_ditvals] then [(t, ditval)] ∈ [d_itvals'] 
      where [d_itvals'] is returned by [get_blocked_itvals_and_reset_orders]
      and [new_ditvals] is an argument of the function.
   *)

  Lemma get_blocked_and_reset_in_new_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval))
           (t : Trans)
           (ditval : DynamicTimeInterval),
      In (t, ditval) new_d_itvals ->
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      In (t, ditval) d_itvals'.
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' t' ditval' Hin_new_ditvals Hfun;

      (* deduce_goal is applied to induction cases. *)
      let deduce_goal ditval_state := (assert (Hin_app : In (t', ditval') (new_d_itvals ++ [(t, ditval_state)]))
                                       by (apply in_or_app; left; assumption);
                                      apply (IHo reset_orders' d_itvals' t' ditval' Hin_app Hfun)) in
      (
        (* IND. CASES *)
        deduce_goal blocked || deduce_goal dyn_itval
                                        
        (* BASE CASE *)
        || (injection Hfun as Heq_reset Heq_ditvals;
            rewrite Heq_ditvals in Hin_new_ditvals;
            assumption)
             
        (* ERROR CASES *)
        || inversion Hfun
      ).
  Qed.
  
  (** All dynamic intervals that both have reached their upper bound
      and are associated with transitions that haven't been fired are
      blocked in the [d_intervals'] list, where [d_intervals'] is the
      list returned by [get_blocked_itvals_and_reset_orders]. *)

  Lemma get_blocked_and_reset_decide_blocked :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      forall (t : Trans)
             (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) d_itvals ->
        HasReachedUpperBound dyn_itval ->
        ~In t s.(fired) ->
        In (t, blocked) d_itvals'.
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' Hfun t' ditval' Hin_ditvals Hhas_rub Hnin_fired.
      
      
    (* BASE CASE *)
    - inversion Hin_ditvals.

    (* CASE has_reached_upper_bound dyn_itval && 
            negb (in_list Nat.eq_dec (fired s) t) = true *)
    - let deduce_goal reset_order :=
          (
            inversion_clear Hin_ditvals as [Heq_pair | Hin_tl];
            [
              (* Subcase (t, dyn_itval) = (t', ditval') *)
              assert (Hin_new_ditvals_app : In (t, blocked) (new_d_itvals ++ [(t, blocked)]))
              by (apply in_or_app; right; apply in_eq);
              injection Heq_pair as Heq_tt' Heq_ditval;
              rewrite <- Heq_tt';
              apply (get_blocked_and_reset_in_new_ditvals
                       sitpn s tl transient_marking
                       (reset_orders ++ [(t, reset_order)]) (new_d_itvals ++ [(t, blocked)])
                       reset_orders' d_itvals' t blocked
                       Hin_new_ditvals_app Hfun)
            |

            (* Subcase (t', ditval') ∈ tl *)
            apply (IHo reset_orders' d_itvals' Hfun t' ditval' Hin_tl Hhas_rub Hnin_fired)
            ]
          )
      in (deduce_goal true || deduce_goal false).
        
    (* CASE has_reached_upper_bound dyn_itval && 
            negb (in_list Nat.eq_dec (fired s) t) = false *)     
    - inversion_clear Hin_ditvals as [Heq_pair | Hin_tl];
        [
          (* Subcase (t, dyn_itval) = (t', ditval') *)
          rewrite andb_false_iff in e3;
          inversion_clear e3 as [Hhas_rub_false | Hnin_fired_false];
          [
            (* Contrad. between Hhas_rub and Hhas_rub_false *)
            apply not_has_reached_upper_bound_correct in Hhas_rub_false;
            injection Heq_pair as Heq_tt' Heq_ditvals;
            rewrite Heq_ditvals in Hhas_rub_false;
            contradiction
          |
          
          (* Contrad. between Hnin_fired and Hnin_fired_false *)
          rewrite negb_false_iff in Hnin_fired_false;
          apply in_list_correct in Hnin_fired_false;
          injection Heq_pair as Heq_tt' Heq_ditvals;
          rewrite Heq_tt' in Hnin_fired_false;
          contradiction
          ]
        |

        (* Subcase (t', ditval') ∈ tl *)
        apply (IHo reset_orders' d_itvals' Hfun t' ditval' Hin_tl Hhas_rub Hnin_fired)
        ].

    (* CASE has_reached_upper_bound dyn_itval && 
            negb (in_list Nat.eq_dec (fired s) t) = true *)
    - let deduce_goal reset_order :=
          (
            inversion_clear Hin_ditvals as [Heq_pair | Hin_tl];
            [
              (* Subcase (t, dyn_itval) = (t', ditval') *)
              assert (Hin_new_ditvals_app : In (t, blocked) (new_d_itvals ++ [(t, blocked)]))
              by (apply in_or_app; right; apply in_eq);
              injection Heq_pair as Heq_tt' Heq_ditval;
              rewrite <- Heq_tt';
              apply (get_blocked_and_reset_in_new_ditvals
                       sitpn s tl transient_marking
                       (reset_orders ++ [(t, reset_order)]) (new_d_itvals ++ [(t, blocked)])
                       reset_orders' d_itvals' t blocked
                       Hin_new_ditvals_app Hfun)
            |

            (* Subcase (t', ditval') ∈ tl *)
            apply (IHo reset_orders' d_itvals' Hfun t' ditval' Hin_tl Hhas_rub Hnin_fired)
            ]
          )
      in (deduce_goal true || deduce_goal false).

    (* CASE has_reached_upper_bound dyn_itval && 
            negb (in_list Nat.eq_dec (fired s) t) = false *)     
    - inversion_clear Hin_ditvals as [Heq_pair | Hin_tl];
        [
          (* Subcase (t, dyn_itval) = (t', ditval') *)
          rewrite andb_false_iff in e3;
          inversion_clear e3 as [Hhas_rub_false | Hnin_fired_false];
          [
            (* Contrad. between Hhas_rub and Hhas_rub_false *)
            apply not_has_reached_upper_bound_correct in Hhas_rub_false;
            injection Heq_pair as Heq_tt' Heq_ditvals;
            rewrite Heq_ditvals in Hhas_rub_false;
            contradiction
          |
          
          (* Contrad. between Hnin_fired and Hnin_fired_false *)
          rewrite negb_false_iff in Hnin_fired_false;
          apply in_list_correct in Hnin_fired_false;
          injection Heq_pair as Heq_tt' Heq_ditvals;
          rewrite Heq_tt' in Hnin_fired_false;
          contradiction
          ]
        |

        (* Subcase (t', ditval') ∈ tl *)
        apply (IHo reset_orders' d_itvals' Hfun t' ditval' Hin_tl Hhas_rub Hnin_fired)
        ].
      
    (* ERROR CASES *)
    - inversion Hfun.           
  Qed.
  
  (** All dynamic intervals that both have reached their upper bound
      and are associated with transitions that haven't been fired are
      blocked in the [(d_intervals s')] list, where [s'] is the state
      returned by [sitpn_rising_edge]. *)
  
  Lemma sitpn_rising_edge_decide_blocked :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      forall (t : Trans)
             (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) s.(d_intervals) ->
        HasReachedUpperBound dyn_itval ->
        ~In t s.(fired) ->
        In (t, blocked) s'.(d_intervals).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun;

      (* GENERAL CASE *)
      (injection Hfun as Hfun; rewrite <- Hfun; simpl;
       apply (get_blocked_and_reset_decide_blocked
                sitpn s (d_intervals s) transient_marking
                [] [] reset' d_intervals' e0))
      (* ERROR CASES *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeDecideBlocked.

Section SitpnRisingEdgeDecideNotBlocked.

  (** Correctness lemma for has_reached_upper_bound = true. *)
  
  Lemma has_reached_upper_bound_correct :
    forall (ditval : DynamicTimeInterval),
      has_reached_upper_bound ditval = true ->
      HasReachedUpperBound ditval.
  Proof.
    intros ditval Hfun.
    unfold has_reached_upper_bound in Hfun.
    unfold HasReachedUpperBound.

    (* Cases of ditval. *)
    destruct ditval.

    (* CASE ditval = active t. *)
    - destruct t.
      destruct min_t.

      (* Case min_t = 0 *)
      + destruct max_t;
          [
            inversion Hfun | destruct n; [ left; reflexivity | inversion Hfun]
          ].

      (* Case min_t = _ *)
      + inversion Hfun.

    (* CASE ditval = blocked *)
    - auto.
  Qed.
  
  (** All dynamic intervals that either haven't reached their upper
      bound or are associated with fired transitions stay the same in
      the [d_intervals'] list, where [d_intervals'] is the list
      returned by [get_blocked_itvals_and_reset_orders]. *)

  Lemma get_blocked_and_reset_decide_not_blocked :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      forall (t : Trans)
             (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) d_itvals ->
        (~HasReachedUpperBound dyn_itval \/ In t s.(fired)) ->
        In (t, dyn_itval) d_itvals'.
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' Hfun t' ditval' Hin_ditvals Hv_rub_nin;

      (
        (* CASE has_reached_upper_bound dyn_itval && 
            negb (in_list Nat.eq_dec (fired s) t) = true *)
        (
          inversion_clear Hin_ditvals as [Heq_pair | Hin_tl];

          (* Subcase (t, dyn_itval) = (t', ditval') *)
          [ rewrite andb_true_iff in e3;
            inversion_clear e3 as (Hhas_rub_true & Hnin_fired_true);
            inversion_clear Hv_rub_nin as [Hnot_has_rub | Hin_fired];
        
            (* Contrad. between Hnot_has_rub and Hhas_rub_true *)
            [
              apply has_reached_upper_bound_correct in Hhas_rub_true;
              injection Heq_pair as Heq_tt' Heq_ditvals;
              rewrite Heq_ditvals in Hhas_rub_true;
              contradiction
            |
          
            (* Contrad. between Hin_fired and Hnin_fired_true *)
            rewrite negb_true_iff in Hnin_fired_true;
            apply not_in_list_correct in Hnin_fired_true;
            injection Heq_pair as Heq_tt' Heq_ditvals;
            rewrite Heq_tt' in Hnin_fired_true;
            contradiction
            ]
              
          |
          
          (* Subcase (t', ditval') ∈ tl *)
          apply (IHo reset_orders' d_itvals' Hfun t' ditval' Hin_tl Hv_rub_nin)
                
          ]
        )

        ||
        
        (* CASE has_reached_upper_bound dyn_itval && 
                negb (in_list Nat.eq_dec (fired s) t) = false *)     
        (
          let deduce_goal reset_order :=
              (inversion_clear Hin_ditvals as [Heq_pair | Hin_tl];

               (* Subcase (t, dyn_itval) = (t', ditval') *)
               [
                 assert (Hin_new_ditvals_app : In (t, dyn_itval) (new_d_itvals ++ [(t, dyn_itval)]))
                 by (apply in_or_app; right; apply in_eq);
                 rewrite <- Heq_pair;
                 apply (get_blocked_and_reset_in_new_ditvals
                          sitpn s tl transient_marking
                          (reset_orders ++ [(t, reset_order)]) (new_d_itvals ++ [(t, dyn_itval)])
                          reset_orders' d_itvals' t dyn_itval
                          Hin_new_ditvals_app Hfun)
               |

               (* Subcase (t', ditval') ∈ tl *)
               apply (IHo reset_orders' d_itvals' Hfun t' ditval' Hin_tl Hv_rub_nin)
              ])
          in (deduce_goal true || deduce_goal false)
        )
        (* BASE CASE and ERROR CASE *)
        || inversion Hin_ditvals; inversion Hfun
      ).           
  Qed.
  
  (** All dynamic intervals that either haven't reached their upper
      bound or are associated with fired transitions stay the same in
      the [(d_intervals s')] list, where [s'] is the state returned by
      [sitpn_rising_edge]. *)
  
  Lemma sitpn_rising_edge_decide_not_blocked :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      forall (t : Trans)
             (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) s.(d_intervals) ->
        (~HasReachedUpperBound dyn_itval \/ In t s.(fired)) ->
        In (t, dyn_itval) s'.(d_intervals).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun;

      (* GENERAL CASE *)
      (injection Hfun as Hfun;
       rewrite <- Hfun;
       simpl;
       apply (get_blocked_and_reset_decide_not_blocked
                sitpn s (d_intervals s) transient_marking
                [] [] reset' d_intervals' e0))
        
      (* ERROR CASES *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeDecideNotBlocked.
