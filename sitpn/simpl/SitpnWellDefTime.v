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

(** ** Lemmas about structure preservation of dynamic time intervals. *)

Section SitpnFallingEdgeSameStructDItvals.

  (** [update_time_intervals] preserves the structure of
      [new_d_itvals ++ d_itvals] in the returned [d_itvals']. *)
  
  Lemma update_time_intervals_same_struct_ditvals :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      update_time_intervals sitpn s d_itvals new_d_itvals = Some d_itvals' ->
      (fst (split (new_d_itvals ++ d_itvals))) = (fst (split d_itvals')).
  Proof.
    intros sitpn s d_itvals new_d_itvals;
      functional induction (update_time_intervals sitpn s d_itvals new_d_itvals)
                 using update_time_intervals_ind;
      intros d_itvals' Hfun;
      
      (* BASE CASE. *)
      ((injection Hfun as Heq_itvals; simpl; rewrite Heq_itvals; rewrite app_nil_r; reflexivity)
         
       (* GENERAL CASE *)
       || (specialize (IHo d_itvals' Hfun) as Heq_ditvals;
           rewrite fst_split_app in Heq_ditvals;
           rewrite fst_split_app in Heq_ditvals;
           simpl in Heq_ditvals;
           rewrite fst_split_app;
           rewrite fst_split_cons_app;
           simpl;
           rewrite <- app_assoc in Heq_ditvals;
           assumption)

       (* ERROR CASE *)
       || inversion Hfun).
  Qed.
  
  (** [sitpn_falling_edge] preserves the structure of the
      [d_intervals] in the returned state. *)
  
  Lemma sitpn_falling_edge_same_struct_ditvals :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (fst (split (d_intervals s))) = (fst (split (d_intervals s'))).
  Proof.
    intros sitpn s s' time_value env Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.

    (* GENERAL CASE, all went well. *)
    - simpl in Hfun; injection Hfun as Heq_s'; rewrite <- Heq_s'.
      simpl.
      specialize (update_time_intervals_same_struct_ditvals
                    sitpn s (d_intervals s) [] d_intervals' e)
        as Hsame_struct_ditvals.
      assumption.

    (* ERROR CASE. *)
    - inversion Hfun.

    (* ERROR CASE. *)
    - inversion Hfun.

  Qed.
  
End SitpnFallingEdgeSameStructDItvals.

(** ** Lemmas about structure preservation of reset orders. *)

Section SitpnFallingEdgeResetEq.

  (** [sitpn_falling_edge] preserves the structure of the
      [d_intervals] in the returned state. *)
  
  Lemma sitpn_falling_edge_same_reset :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (reset s) = (reset s').
  Proof.
    intros sitpn s s' time_value env Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

      (* GENERAL CASE, all went well. *)
      ((simpl in Hfun;
        injection Hfun as Heq_s';
        rewrite <- Heq_s'; simpl; reflexivity)
       (* ERROR CASE. *)
       || inversion Hfun).
  Qed.
  
End SitpnFallingEdgeResetEq.

(** ** Rising edge lemmas about structure preservation of dynamic time intervals  *)

Section SitpnRisingEdgeSameStructDItvals.


  Lemma get_blocked_and_reset_same_struct_ditvals :
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
      fst (split (new_d_itvals ++ d_itvals)) = fst (split d_itvals').
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' Hfun;

      (* BASE CASE *)
      (injection Hfun as Heq_reset Heq_ditvals;
       rewrite Heq_ditvals;
       rewrite app_nil_r;
       reflexivity) 

      (* CASE is_sens = true *)
      || (specialize (IHo reset_orders' d_itvals' Hfun) as Hsame_struct;
          rewrite fst_split_app; rewrite fst_split_cons_app; simpl;
          rewrite <- app_assoc in Hsame_struct;
          do 2 (rewrite fst_split_app in Hsame_struct);
          simpl in Hsame_struct;
          assumption)

      (* CASE has_reached && !in_list = false *)
      || (specialize (IHo reset_orders' d_itvals' Hfun) as Hsame_struct;
          rewrite <- app_assoc in Hsame_struct;
          assumption)

      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
  (** [sitpn_rising_edge] preserves the structure of the
      [d_intervals] in the returned state. *)
  
  Lemma sitpn_rising_edge_same_struct_ditvals :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      sitpn_rising_edge sitpn s = Some s' ->
      (fst (split (d_intervals s))) = (fst (split (d_intervals s'))).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hfun;
      
      (*GENERAL CASE *)
      (specialize (@get_blocked_and_reset_same_struct_ditvals
                     sitpn s (d_intervals s) transient_marking [] []
                     reset' d_intervals' e0) as Heq_fs_ditvals;
       rewrite app_nil_l in Heq_fs_ditvals;
       rewrite Heq_fs_ditvals;
       injection Hfun as Hfun;
       rewrite <- Hfun; simpl; reflexivity)
        
      (* ERROR CASES *)
      || inversion Hfun.
  Qed.
    
End SitpnRisingEdgeSameStructDItvals.

(** ** Rising edge lemmas about preservation of reset list structure. *)

Section SitpnRisingEdgeSameStructReset.

  (** [get_blocked_and_reset] preserves structure of reset list. *)

  Lemma get_blocked_and_reset_reset_incl_transs :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      (forall t : Trans, In t (transs sitpn) /\ (s_intervals sitpn t) <> None <->
                         In t (fst (split (new_d_itvals ++ d_itvals)))) ->
      fst (split reset_orders) = fst (split new_d_itvals) ->
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      forall t : Trans, In t (transs sitpn) /\ (s_intervals sitpn t) <> None <->
                        In t (fst (split reset_orders')).
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' Heq_ditvals_transs Heq_reset_newd Hfun.

      (* BASE CASE *)
    - injection Hfun as Heq_reset Heq_newd;
        rewrite <- Heq_reset;
        rewrite Heq_reset_newd;
        rewrite app_nil_r in Heq_ditvals_transs;
        assumption.

    (* CASE  *)
    - (assert (Heq_ditvals_transs':
                 forall t0 : Trans,
                   In t0 (transs sitpn) /\ s_intervals sitpn t0 <> None <->
                   In t0 (fst (split ((new_d_itvals ++ [(t, blocked)]) ++ tl))))
        by (intros t0;
            specialize (Heq_ditvals_transs t0);
            rewrite Heq_ditvals_transs;
            rewrite <- app_assoc;
            do 3 (rewrite fst_split_app);
            rewrite fst_split_cons_app;
            simpl;
            reflexivity);

       assert (Heq_reset_newd':
                 fst (split (reset_orders ++ [(t, false)])) = fst (split (new_d_itvals ++ [(t, blocked)])))
         by (do 2 (rewrite fst_split_app); simpl; rewrite Heq_reset_newd; reflexivity);

       apply (IHo reset_orders' d_itvals' Heq_ditvals_transs' Heq_reset_newd' Hfun)).

    (* CASE  *)                                               
    - (assert (Heq_ditvals_transs':
                 forall t0 : Trans,
                   In t0 (transs sitpn) /\ s_intervals sitpn t0 <> None <->
                   In t0 (fst (split ((new_d_itvals ++ [(t, dyn_itval)]) ++ tl))))
        by (intros t0;
            specialize (Heq_ditvals_transs t0);
            rewrite Heq_ditvals_transs;
            rewrite <- app_assoc;
            do 3 (rewrite fst_split_app);
            rewrite fst_split_cons_app;
            simpl;
            reflexivity);

       assert (Heq_reset_newd':
                 fst (split (reset_orders ++ [(t, false)])) = fst (split (new_d_itvals ++ [(t, dyn_itval)])))
         by (do 2 (rewrite fst_split_app); simpl; rewrite Heq_reset_newd; reflexivity);
       apply (IHo reset_orders' d_itvals' Heq_ditvals_transs' Heq_reset_newd' Hfun)).

    (* CASE  *)
    - (assert (Heq_ditvals_transs':
                 forall t0 : Trans,
                   In t0 (transs sitpn) /\ s_intervals sitpn t0 <> None <->
                   In t0 (fst (split ((new_d_itvals ++ [(t, blocked)]) ++ tl))))
        by (intros t0;
            specialize (Heq_ditvals_transs t0);
            rewrite Heq_ditvals_transs;
            rewrite <- app_assoc;
            do 3 (rewrite fst_split_app);
            rewrite fst_split_cons_app;
            simpl;
            reflexivity);

       assert (Heq_reset_newd':
                 fst (split (reset_orders ++ [(t, true)])) = fst (split (new_d_itvals ++ [(t, blocked)])))
         by (do 2 (rewrite fst_split_app); simpl; rewrite Heq_reset_newd; reflexivity);

       apply (IHo reset_orders' d_itvals' Heq_ditvals_transs' Heq_reset_newd' Hfun)).

    (* CASE  *)
    - (assert (Heq_ditvals_transs':
                 forall t0 : Trans,
                   In t0 (transs sitpn) /\ s_intervals sitpn t0 <> None <->
                   In t0 (fst (split ((new_d_itvals ++ [(t, dyn_itval)]) ++ tl))))
        by (intros t0;
            specialize (Heq_ditvals_transs t0);
            rewrite Heq_ditvals_transs;
            rewrite <- app_assoc;
            do 3 (rewrite fst_split_app);
            rewrite fst_split_cons_app;
            simpl;
            reflexivity);

       assert (Heq_reset_newd':
                 fst (split (reset_orders ++ [(t, true)])) = fst (split (new_d_itvals ++ [(t, dyn_itval)])))
         by (do 2 (rewrite fst_split_app); simpl; rewrite Heq_reset_newd; reflexivity);

       apply (IHo reset_orders' d_itvals' Heq_ditvals_transs' Heq_reset_newd' Hfun)).
      
    (* ERROR CASE *)
    - inversion Hfun. 
  Qed.
  
  (** [sitpn_rising_edge] preserves structure of reset list in [s']. *)
  
  Lemma sitpn_rising_edge_reset_incl_transs :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      forall t : Trans, In t (transs sitpn) /\ (s_intervals sitpn t) <> None <->
                        In t (fst (split (reset s'))).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s)
                 using sitpn_rising_edge_ind;
      intros s' Hwell_def_s Hfun;

      (* GENERAL CASE *)
      (assert (Hwf_ditvals_s :
                 forall t' : Trans, In t' (transs sitpn) /\ (s_intervals sitpn t') <> None <->
                                    In t' (fst (split ([] ++ (d_intervals s))))) 
        by (explode_well_defined_sitpn_state Hwell_def_s; rewrite app_nil_l; assumption);
       
       specialize (get_blocked_and_reset_reset_incl_transs
                     sitpn s (d_intervals s) transient_marking [] []
                     reset' d_intervals' Hwf_ditvals_s eq_refl e0)
         as Hwf_reset_s;
       injection Hfun as Hfun; rewrite <- Hfun; simpl; assumption)

      (* ERROR CASES *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeSameStructReset.

(** ** Rising edge lemmas about no dup in reset list. *)

Section SitpnRisingEdgeNoDupReset.

  (** [get_blocked_and_reset] returns a reset list with no dup. *)

  Lemma get_blocked_and_reset_nodup_reset :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           (reset_orders' : list (Trans * bool))
           (d_itvals' : list (Trans * DynamicTimeInterval)),
      NoDup (fst (split (new_d_itvals ++ d_itvals))) ->
      fst (split reset_orders) = fst (split new_d_itvals) ->
      get_blocked_itvals_and_reset_orders
        sitpn s d_itvals transient_marking reset_orders new_d_itvals = Some (reset_orders', d_itvals') ->
      NoDup (fst (split reset_orders')).
  Proof.
    intros sitpn s d_itvals transient_marking reset_orders new_d_itvals;
      functional induction (get_blocked_itvals_and_reset_orders
                              sitpn s d_itvals transient_marking reset_orders new_d_itvals)
                 using get_blocked_itvals_and_reset_orders_ind;
      intros reset_orders' d_itvals' Hnodup_ditvals Heq_reset_newd Hfun;

      (* Puts the instructions to solve most of the subgoals
         in a ltac variable with two parameters. *)
      let deduce_subgoal ditval reset_order := 
          (assert (Hnodup_ditvals': NoDup (fst (split ((new_d_itvals ++ [(t, ditval)]) ++ tl))))
            by (do 2 (rewrite fst_split_app);
                simpl;
                rewrite <- app_assoc;
                rewrite fst_split_app in Hnodup_ditvals;
                rewrite fst_split_cons_app in Hnodup_ditvals;
                simpl in Hnodup_ditvals;
                assumption);
           assert (Heq_reset_newd':
                     fst (split (reset_orders ++ [(t, reset_order)])) = fst (split (new_d_itvals ++ [(t, ditval)])))
             by (do 2 (rewrite fst_split_app); simpl; rewrite Heq_reset_newd; reflexivity);  
           apply (IHo reset_orders' d_itvals' Hnodup_ditvals' Heq_reset_newd' Hfun)) in 
      
      (
        (* BASE CASE *)
        (injection Hfun as Heq_reset Heq_newd;
         rewrite <- Heq_reset;
         rewrite Heq_reset_newd;
         rewrite app_nil_r in Hnodup_ditvals;
         assumption)
          
        (* OTHER CASES, apply deduce_subgoal with different parameters. *)
        || deduce_subgoal dyn_itval false
        || deduce_subgoal blocked false
        || deduce_subgoal blocked true
        || deduce_subgoal dyn_itval true
             
        (* ERROR CASE *)
        || inversion Hfun
      ).
  Qed.
  
  (** [sitpn_rising_edge] preserves structure of reset list in [s']. *)
  
  Lemma sitpn_rising_edge_nodup_reset :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      NoDup (fst (split (reset s'))).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s)
                 using sitpn_rising_edge_ind;
      intros s' Hwell_def_s Hfun;

      (* GENERAL CASE *)
      (assert (Hnodup_ditvals_s : NoDup (fst (split ([] ++ (d_intervals s))))) 
        by (explode_well_defined_sitpn_state Hwell_def_s; rewrite app_nil_l; assumption);
       
       specialize (get_blocked_and_reset_nodup_reset
                     sitpn s (d_intervals s) transient_marking [] []
                     reset' d_intervals' Hnodup_ditvals_s eq_refl e0)
         as Hwf_reset_s;
       injection Hfun as Hfun; rewrite <- Hfun; simpl; assumption)

      (* ERROR CASES *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeNoDupReset.
