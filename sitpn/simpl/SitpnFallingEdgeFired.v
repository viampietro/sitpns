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


(* Import lemmas on well-definition. *)

Require Import simpl.SitpnFallingEdgeWellDef.
Require Import simpl.SitpnWellDefMarking.
Require Import simpl.SitpnWellDefFired.

(* Import classic logic. *)

Require Import Classical_Prop.

(* Import lemmas on marking. *)

Require Import simpl.SitpnRisingEdgeMarking.

(** * Falling edge lemmas about synchronous execution rules. *)

(** ** Transitions that are not firable are not fired. *)

Section SitpnFallingEdgeNotFirableNotFired.

  (** ∀ t ∈ fired, 
      sitpn_fire_aux sitpn state residual_marking fired group = Some final_fired ⇒ 
      t ∈ final_fired *)
  
  Lemma sitpn_fire_aux_in_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      In t fired ->
      sitpn_fire_aux sitpn state residual_marking fired pgroup = Some final_fired ->
      In t final_fired.
  Proof.
    intros sitpn state residual_marking fired pgroup;
      functional induction (sitpn_fire_aux sitpn state residual_marking fired pgroup)
                 using sitpn_fire_aux_ind;
      intros final_fired t' Hin_t_fired Hfun.

    (* BASE CASE *)
    - injection Hfun; intro Heq; rewrite <- Heq; assumption.

    (* GENERAL CASE *)
    - apply or_introl with (B := In t' [t]) in Hin_t_fired.
      apply in_or_app in Hin_t_fired.
      apply (IHo final_fired t' Hin_t_fired Hfun).

    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.

    (* CASE is_sensitized = Some false. *)
    - apply (IHo final_fired t' Hin_t_fired Hfun).

    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.

    (* CASE sitpn_is_firable = Some false. *)
    - apply (IHo final_fired t' Hin_t_fired Hfun).

    (* ERROR CASE, sitpn_is_firable = None. *)
    - inversion Hfun.
  Qed.
  
  (** ∀ t ∉ pgroup, t ∉ fired, 
      sitpn_fire_aux sitpn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Lemma sitpn_fire_aux_not_in_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      ~In t fired ->
      ~In t pgroup ->
      sitpn_fire_aux sitpn state residual_marking fired pgroup = Some final_fired ->
      ~In t final_fired.
  Proof.
    intros sitpn state residual_marking fired pgroup;
      functional induction (sitpn_fire_aux sitpn state residual_marking fired pgroup)
                 using sitpn_fire_aux_ind;
      intros final_fired t' Hnot_in_fired Hnot_in_pg Hfun.

    (* BASE CASE, pgroup = []. *)
    - injection Hfun; intro Heq; rewrite <- Heq; assumption.

    (* GENERAL CASE, all went well. *)
    - apply not_in_cons in Hnot_in_pg.
      elim Hnot_in_pg; intros Hneq_t Hnot_in_tail.
      assert (Hnot_in_tt: ~In t' [t])
        by (apply (diff_not_in t' t Hneq_t)).
      assert (Hnot_in_app : ~In t' (fired ++ [t]))
        by (apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tt))).
      apply (IHo final_fired t' Hnot_in_app Hnot_in_tail Hfun).
    - inversion Hfun.

    (* CASE is_sensitized = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.

    (* CASE sitpn_is_firable = Some false, apply induction hypothesis. *)
    - apply not_in_cons in Hnot_in_pg; elim Hnot_in_pg; intros Hdiff_tt Hnot_in_tail.
      apply (IHo final_fired t' Hnot_in_fired Hnot_in_tail Hfun).
    - inversion Hfun.
  Qed.
  
  (** ∀ t ∈ pgroup, t ∉ fired, t ∉ firable(state),
      sitpn_fire_aux sitpn state residual_marking fired group = Some final_fired ⇒ 
      t ∉ final_fired *)
  
  Theorem sitpn_fire_aux_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (pgroup : list Trans)
           (final_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn state ->
      In pgroup sitpn.(priority_groups) ->
      IsDecListCons pg pgroup ->
      sitpn_fire_aux sitpn state residual_marking fired pg = Some final_fired ->
      forall t : Trans,
        In t pg ->
        ~In t fired ->
        ~SitpnIsFirable sitpn state t ->
        ~In t final_fired.
  Proof.
    intros sitpn state residual_marking fired pg;
      functional induction (sitpn_fire_aux sitpn state residual_marking fired pg)
                 using sitpn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
             His_dec Hfun t' Hin_pg Hnot_in_fired Hnot_firable.
    
    (* Base case, pg = []. *)
    - inversion Hin_pg.
      
    (* CASE sitpn_is_firable t' = Some true *)
    - inversion_clear Hin_pg as [Heq_t | Hin_tail].
      
      (* Case t' = t.
         
         We have to show ~SitpnIsFirable -> sitpn_is_firable = Some
         false, then contradiction. *)
      + (* Builds premises for sitpn_is_firable_correct. *)
        deduce_in_transs.
        
        (* Specializes sitpn_is_firable_correct, then contradiction. *)
        specialize (sitpn_is_firable_correct
                      t Hwell_def_sitpn Hwell_def_s Hin_t_transs e0) as Hfirable.
        rewrite Heq_t in Hfirable; contradiction.
        
      (* Case t' ∈ tail, then apply IH. *)
      + (* Builds premises for IH. *)

        (* Premise t' ∉ (fired ++ [t]) *)
        assert (Hnot_in_fired_app : ~In t' (fired ++ [t])).
        {
          deduce_nodup_in_dec_pgroup.
          deduce_nodup_hd_not_in.
          specialize (not_in_in_diff t t' tail (conj Hnot_in_tl Hin_tail)) as Hneq_tt'.
          assert (Hnot_in_tlist : ~In t' [t]) by (apply not_in_cons; auto).
          apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tlist)).            
        }

        (* Premise IsDecListCons tail pgroup *)
        apply is_dec_list_cons_cons in His_dec.

        (* Applies IH with premises. *)
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
                   His_dec Hfun t' Hin_tail Hnot_in_fired_app Hnot_firable).
           
    (* Case update_residual_marking returns None. *)
    - inversion Hfun.
      
    (* Case is_sensitized returns Some false. *)
    - inversion_clear Hin_pg as [Heq_tt' | Hin_t'_tail].

      (* Case t = t' *)
      +
        (* Premise to apply sitpn_fire_aux_not_in_not_fired *)
        deduce_nodup_in_dec_pgroup;
          rewrite NoDup_cons_iff in Hnodup_ttail;
          apply proj1 in Hnodup_ttail as Hnot_in_tail;
          rewrite Heq_tt' in Hnot_in_tail.

        (* Applies sitpn_fire_aux_not_in_not_fired. *)
        apply (sitpn_fire_aux_not_in_not_fired
                 sitpn state residual_marking fired tail final_fired t'
                 Hnot_in_fired Hnot_in_tail Hfun).

      (* Case t' ∈ tail, then apply IH. *)
      + (* Builds premises for IH. *)

        (* Premise t' ∉ (fired ++ [t]) *)
        assert (Hnot_in_fired_app : ~In t' (fired ++ [t])).
        {
          deduce_nodup_in_dec_pgroup.
          deduce_nodup_hd_not_in.
          specialize (not_in_in_diff t t' tail (conj Hnot_in_tl Hin_t'_tail)) as Hneq_tt'.
          assert (Hnot_in_tlist : ~In t' [t]) by (apply not_in_cons; auto).
          apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tlist)).            
        }

        (* Premise IsDecListCons tail pgroup *)
        apply is_dec_list_cons_cons in His_dec.

        (* Applies IH with premises. *)
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
                   His_dec Hfun t' Hin_t'_tail Hnot_in_fired Hnot_firable).
        
    (* ERROR CASE is_sensitized returns None. *)
    - inversion Hfun.
      
    (* CASE sitpn_is_firable returns Some false. *)
    - inversion_clear Hin_pg as [Heq_tt' | Hin_t'_tail].

      (* Case t = t' *)
      +
        (* Premise to apply sitpn_fire_aux_not_in_not_fired *)
        deduce_nodup_in_dec_pgroup;
          rewrite NoDup_cons_iff in Hnodup_ttail;
          apply proj1 in Hnodup_ttail as Hnot_in_tail;
          rewrite Heq_tt' in Hnot_in_tail.

        (* Applies sitpn_fire_aux_not_in_not_fired. *)
        apply (sitpn_fire_aux_not_in_not_fired
                 sitpn state residual_marking fired tail final_fired t'
                 Hnot_in_fired Hnot_in_tail Hfun).

      (* Case t' ∈ tail, then apply IH. *)
      + (* Builds premises for IH. *)

        (* Premise t' ∉ (fired ++ [t]) *)
        assert (Hnot_in_fired_app : ~In t' (fired ++ [t])).
        {
          deduce_nodup_in_dec_pgroup.
          deduce_nodup_hd_not_in.
          specialize (not_in_in_diff t t' tail (conj Hnot_in_tl Hin_t'_tail)) as Hneq_tt'.
          assert (Hnot_in_tlist : ~In t' [t]) by (apply not_in_cons; auto).
          apply (not_in_app t' fired [t] (conj Hnot_in_fired Hnot_in_tlist)).            
        }

        (* Premise IsDecListCons tail pgroup *)
        apply is_dec_list_cons_cons in His_dec.

        (* Applies IH with premises. *)
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s Hin_pgroups
                   His_dec Hfun t' Hin_t'_tail Hnot_in_fired Hnot_firable).
           
    (* ERROR CASE sitpn_is_firable = None *)
    - inversion Hfun.
      
  Qed.

  (** ∀ pgroup ∈ sitpn.(priority_groups),
      sitpn_fire sitpn state pgroup = Some fired ⇒ 
      ∀ t ∈ pgroup, t ∉ firable(state) ⇒ t ∉ fired. *)
  
  Theorem sitpn_fire_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (pgroup : list Trans)
           (fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn state ->
      In pgroup sitpn.(priority_groups) ->
      sitpn_fire sitpn state pgroup = Some fired ->
      (forall t : Trans,
          In t pgroup ->
          ~SitpnIsFirable sitpn state t ->
          ~In t fired).
  Proof.
    unfold sitpn_fire.
    intros sitpn state pgroup fired Hwell_def_sitpn Hwell_def_state
           Hin_pgroups Hfun t Hin_pgroup Hnot_firable.
    
    (* Applies sitpn_fire_aux_not_firable_not_fired. *)
    apply (sitpn_fire_aux_not_firable_not_fired
             sitpn state (marking state) [] pgroup pgroup fired
             Hwell_def_sitpn Hwell_def_state Hin_pgroups (IsDecListCons_refl pgroup) Hfun
             t Hin_pgroup (@in_nil Trans t) Hnot_firable).
  Qed.

  (** sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∉ fired ∧ t ∉ (concat pgroups) ⇒ t ∉ final_fired *)
  
  Theorem sitpn_map_fire_aux_not_in_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ->
      forall t : Trans, ~In t fired -> ~In t (concat pgroups) -> ~In t final_fired.
  Proof.
    intros sitpn state fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn state fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros final_fired Hfun t Hnot_in_fired Hnot_in_concat.
    (* Base case, pgroups = [] *)
    - injection Hfun; intro Heq; rewrite Heq in *; assumption.
    (* General case *)
    - unfold sitpn_fire in e0.
      (* Builds (~In t []) to apply sitpn_fire_aux_not_in_not_fired. *)
      assert (Hnot_in_nil : ~In t []) by apply in_nil.
      (* Builds (~In t pgroup) to apply sitpn_fire_aux_not_in_not_fired. *)
      simpl in Hnot_in_concat.
      generalize (not_app_in t pgroup (concat pgroups_tail) Hnot_in_concat)
        as Hnot_in_wedge; intro.
      elim Hnot_in_wedge; intros Hnot_in_pg Hnot_in_concat'.
      (* Applies sitpn_fire_aux_not_in_not_fired *)
      generalize (sitpn_fire_aux_not_in_not_fired
                    sitpn state (marking state) [] pgroup fired_trs t
                    Hnot_in_nil Hnot_in_pg e0) as Hnot_in_ff; intro.
      (* Builds ~In t (fired_transitions ++ fired_trs) to apply IHo. *)
      generalize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_ff))
        as Hnot_in_all_ff; intro.
      (* Applies induction hypothesis. *)
      apply (IHo final_fired Hfun t Hnot_in_all_ff Hnot_in_concat').
    (* Case sitpn_fire returns None. *)
    - inversion Hfun.
  Qed.

  (** sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ⇒ 
      ∀ t ∈ fired ⇒ t ∈ final_fired *)
  
  Theorem sitpn_map_fire_aux_in_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ->
      forall t : Trans, In t fired -> In t final_fired.
  Proof.
    intros sitpn state fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn state fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros final_fired Hfun t Hin_t_fired.
    (* BASE CASE *)
    - injection Hfun; intro Heq; rewrite Heq in *; assumption.
    (* GENERAL CASE *)
    - apply or_introl with (B := In t fired_trs) in Hin_t_fired.
      apply in_or_app in Hin_t_fired.
      apply (IHo final_fired Hfun t Hin_t_fired).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (** sitpn_map_fire_aux sitpn s fired pgroups = Some final_fired ⇒ 
      ∀ pgroup ∈ pgroups, ∀ t ∈ pgroup, 
      t ∉ fired ⇒ t ∉ firable(s) ⇒ t ∉ final_fired 
      
      N.B. firable(s) ≡ firable(s'), because 
      s.(marking) = s'.(marking) ∧ 
      s.(ditvals) = s'.(ditvals) ∧ 
      s.(condv) = s'.(condv) *)
  
  Theorem sitpn_map_fire_aux_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (state : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn state ->
      IsDecListCons pgroups (priority_groups sitpn) ->
      sitpn_map_fire_aux sitpn state fired pgroups = Some final_fired ->
      (forall (pgroup : list Trans)
              (t : Trans),
          In pgroup pgroups ->
          In t pgroup ->
          ~In t fired ->
          ~SitpnIsFirable sitpn state t ->
          ~In t final_fired).
  Proof.
    intros sitpn state fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn state fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros final_fired Hwell_def_sitpn Hwell_def_s His_dec
             Hfun pgroup' t Hin_pgs Hin_pg Hnot_in_fired Hnot_firable.

    (* BASE CASE, pgroups = []. *)
    - inversion Hin_pgs.

    (* INDUCTION CASE *)

    (* CASE sitpn_fire = Some fired_trs. *)
    - inversion_clear Hin_pgs as [Heq_pg | Hin_pgs_tail].

      (* CASE pgroup = pgroup'. 
         
         - If t ∉ firable then t ∉ fired_trs (sitpn_fire_not_firable_not_in).
         - If t ∉ fired_trs ∧ t ∉ fired_transitions ∧ t ∉ (concat pgroups_tail)
           then t ∉ final_fired (sitpn_map_fire_aux_not_in_not_fired)
       *)
      + (* First specializes, sitpn_fire_not_firable_not_fired to get 
           ~In t fired_trs. *)
        specialize (is_dec_list_cons_incl His_dec) as Hincl_pg_pgs.
        specialize (in_eq pgroup pgroups_tail) as Hin_pgs_tl.
        apply_incl Hin_sitpn_pgs.
        rewrite <- Heq_pg in Hin_pg.
        specialize (sitpn_fire_not_firable_not_fired
                      sitpn state pgroup fired_trs Hwell_def_sitpn Hwell_def_s
                      Hin_sitpn_pgs e0 t Hin_pg Hnot_firable) as Hnot_in_ftrs.

        (* Second, builds (~In t (fired_transitions ++ fired_trs)) 
           from ~In t fired_transitions and ~In t fired_trs. *)
        specialize (not_in_app t fired_transitions fired_trs
                               (conj Hnot_in_fired Hnot_in_ftrs))
          as Hnot_in_fired_app.
        
        (* Builds ~In t (concat pgroups_tail) to apply 
           sitpn_map_fire_aux_not_in_not_fired *)
        explode_well_defined_sitpn.
        unfold NoIntersectInPriorityGroups in Hno_inter.
        specialize (is_dec_list_cons_concat His_dec) as His_dec_concat.
        specialize (nodup_is_dec_list_cons Hno_inter His_dec_concat)
          as Hnodup_concat_pgs_cons.
        rewrite concat_cons in Hnodup_concat_pgs_cons.
        specialize (nodup_app_not_in pgroup (concat pgroups_tail) Hnodup_concat_pgs_cons t Hin_pg)
          as Hnot_in_concat.        
        
        (* Applies sitpn_map_fire_aux_not_in_not_fired *)
        apply (sitpn_map_fire_aux_not_in_not_fired
                 sitpn state (fired_transitions ++ fired_trs) pgroups_tail final_fired Hfun
                 t Hnot_in_fired_app Hnot_in_concat).
        
      (* CASE In pgroup' pgroups_tail, then apply IHo. *)
      + 
        (* Builds ~In t (fired_transitions ++ fired_trs). 

           First, we need (~In t pgroup) to apply sitpn_fire_aux_not_in_not_fired. *)

        assert (Hnot_in_t_pg : ~In t pgroup).
        {
          explode_well_defined_sitpn.
          unfold NoIntersectInPriorityGroups in Hno_inter.
          specialize (is_dec_list_cons_concat His_dec) as His_dec_concat.
          specialize (nodup_is_dec_list_cons Hno_inter His_dec_concat)
            as Hnodup_concat_pgs_cons.
          rewrite concat_cons in Hnodup_concat_pgs_cons.
          specialize (NoDup_app_comm pgroup (concat pgroups_tail) Hnodup_concat_pgs_cons)
            as Hnodup_concat_inv.
          specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_concat_inv)
            as Hfall_not_in_pg.
          specialize (in_concat t pgroup' pgroups_tail Hin_pg Hin_pgs_tail) as Hin_concat.
          specialize (Hfall_not_in_pg t Hin_concat) as Hnot_in_pg.
          assumption.
        }
        
        (* Second, we apply sitpn_fire_aux_not_in_not_fired
           to obtain ~In t fired_trs. *)
        unfold sitpn_fire in e0.
        specialize (sitpn_fire_aux_not_in_not_fired
                      sitpn state (marking state) [] pgroup fired_trs t
                      (@in_nil Trans t) Hnot_in_t_pg e0) as Hnot_in_fired'.
        
        (* Finally, builds (~In t (fired_transitions ++ fired_trs)) *)
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_fired_app.
        
        (* Applies IHo. *)
        apply (IHo final_fired Hwell_def_sitpn Hwell_def_s
                   (is_dec_list_cons_cons His_dec) Hfun pgroup' t Hin_pgs_tail
                   Hin_pg  Hnot_in_fired_app Hnot_firable).
        
    (* CASE sitpn_fire returns None. *)
    - inversion Hfun.
  Qed.
  
  (** All transitions that are not firable at state [s] are not in the
      list [to_be_fired] returned by the [sitpn_map_fire] function. *)
  
  Lemma sitpn_map_fire_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (to_be_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_map_fire sitpn s = Some to_be_fired ->
      forall (pgroup : list Trans)
             (t : Trans),
        In pgroup (priority_groups sitpn) ->
        In t pgroup ->
        ~ SitpnIsFirable sitpn s t ->
        ~ In t to_be_fired.
  Proof.
    intros sitpn s to_be_fired Hwell_def_sitpn Hwell_def_s Hfun
           pgroup t Hin_pg_pgs Hin_t_pg Hnot_firable;
      unfold sitpn_map_fire in Hfun.

    (* Applies sitpn_map_fire_aux_not_firable_not_fired. *)
    apply (sitpn_map_fire_aux_not_firable_not_fired
             sitpn s [] (priority_groups sitpn) to_be_fired
             Hwell_def_sitpn Hwell_def_s (IsDecListCons_refl (priority_groups sitpn))
             Hfun pgroup t Hin_pg_pgs Hin_t_pg (@in_nil Trans t) Hnot_firable).    
  Qed.
           
  (** All transitions that are not firable at state [s'] 
      are not in [(fired s')] where [s'] is the state
      returned by the [sitpn_falling_edge] function. *)

  Lemma sitpn_falling_edge_not_firable_not_fired :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      forall (pgroup : list Trans)
             (t : Trans),
        In pgroup (priority_groups sitpn) ->
        In t pgroup ->
        ~ SitpnIsFirable sitpn s' t ->
        ~ In t (fired s').
  Proof.
    intros sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun.

    (* We need to build IsWellDefinedSitpnState sitpn s' before
       functional induction. *)
    specialize (sitpn_falling_edge_well_def_state
                  sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun)
      as Hwell_def_s'.

    (* Fun ind. on sitpn_falling_edge. *)
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.

    (* GENERAL CASE. *)
    - simpl in Hfun;
        injection Hfun as Heq_s';

        (* Rewrites s' in the goal. *)
        rewrite <- Heq_s';
        simpl.

      (* Simplifies e0 with tmp_state. *)
      set (tmp_state :=
             {|
               fired := [];
               marking := marking s;
               d_intervals := d_intervals';
               reset := reset s;
               cond_values := get_condition_values (conditions sitpn) time_value env [];
               exec_a := get_action_states sitpn s (actions sitpn) [];
               exec_f := exec_f s
             |}) in e0.

      (* We need to introduce t and pgroup in the context to
         specialize sitpn_is_firable_iff_eq. *)
      intros pgroup t.

      (* Builds premises of sitpn_is_firable_iff_eq. *)
      assert (Heq_m : (marking tmp_state = marking s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_ditvals : (d_intervals tmp_state = d_intervals s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_condv : (cond_values tmp_state = cond_values s')) by (rewrite <- Heq_s'; reflexivity).

      (* Specializes sitpn_is_firable_iff to get: 
         SitpnIsfirable tmp_state t = SitpnIsfirable s' t *)
      specialize (sitpn_is_firable_iff_eq sitpn tmp_state s' t Heq_m Heq_ditvals Heq_condv)
        as Heq_sitpn_is_firable.

      (* Rewrites SitpnIsFirable sitpn s' t by SitpnIsfirable sitpn
         tmp_state t in the goal and generalizes pgroup and t to match
         conclusion of lemma sitpn_map_fire_not_firable_not_fired. *)
      rewrite Heq_s'.
      rewrite <- Heq_sitpn_is_firable.
      generalize pgroup, t. (* Revert previously introduced pgroup and t. *)

      (* Gets IsWellDefinedSitpnState tmp_state before applying lemma. *)
      assert (Hnil_fired_s': fired tmp_state = []) by auto.
      assert (Heq_reset: reset s' = reset tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execa: exec_a s' = exec_a tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execf: exec_f s' = exec_f tmp_state) by (rewrite <- Heq_s'; auto).

      (* Specializes well-definition on tmp_state. *)
      specialize (is_well_def_tmp_state
                    sitpn s' tmp_state Hnil_fired_s' (eq_sym Heq_m) (eq_sym Heq_ditvals)
                    Heq_reset (eq_sym Heq_condv) Heq_execa Heq_execf Hwell_def_s')
        as Hwell_def_tmp.                                        
      
      (* Applies sitpn_map_fire_not_firable_not_fired to complete the
         subgoal. *)
      apply (sitpn_map_fire_not_firable_not_fired
               sitpn tmp_state trs_2b_fired Hwell_def_sitpn Hwell_def_tmp e0).

    (* ERROR CASE *)
    - inversion Hfun.
    - inversion Hfun.
  Qed.
  
End SitpnFallingEdgeNotFirableNotFired.

(** ** Transitions that are both firable and sensitized
       by the residual marking are fired. *)

Section SitpnFallingEdgeSensByResidual.

  (** If : 
       - sitpn_fire_aux sitpn s residual fired pg = Some final_fired 
       - There are no duplicate in [(fired ++ pg)] 
       - [t] ∈ [final_fired] 
      
      Then : [t] ∈ [fired] ∨ [pg].
      
      Needed to prove CASE is_sensitized = Some false in
      sitpn_fire_aux_sens_by_residual. *)
  
  Theorem sitpn_fire_aux_final_fired_vee :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg : list Trans)
           (final_fired : list Trans)
           (t : Trans),
      NoDup (fired ++ pg) ->
      In t final_fired ->
      sitpn_fire_aux sitpn s residual_marking fired pg = Some final_fired ->
      In t fired \/ In t pg.
  Proof.
    intros sitpn s residual_marking fired pg;
      functional induction (sitpn_fire_aux sitpn s residual_marking fired pg)
                 using sitpn_fire_aux_ind;
      intros final_fired t' Hnodup_app Hin_t_ff Hfun.

    (* BASE CASE, pg = []. *)
    - injection Hfun as Heq_fired; left; rewrite Heq_fired; assumption.

    (* GENERAL CASE *)
    - rewrite <- app_assoc in IHo.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as H_ff_vee'.
      elim H_ff_vee'.
      + intro Hin_t_fired_app.
        apply in_app_or in Hin_t_fired_app.
        elim Hin_t_fired_app.
        -- auto.
        -- intro Hin_tt; simpl in Hin_tt.
           elim Hin_tt; [ intro Heq_tt; rewrite <- Heq_tt; right; apply in_eq |
                          intro Hfalse; inversion Hfalse].
      + intro Hin_t_tail; apply in_cons with (a := t) in Hin_t_tail; right; assumption.

    (* ERROR CASE *)
    - inversion Hfun.

    (* CASE is_sensitized = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as Hin_vee.
      elim Hin_vee.
      + intro Hin_t_fired; left; assumption.
      + intro Hin_t_tail; right; apply in_cons with (a := t) in Hin_t_tail; assumption.

    (* ERROR CASE *)
    - inversion Hfun.

    (* CASE sitpn_is_firable = Some false *)
    - apply NoDup_remove in Hnodup_app; apply proj1 in Hnodup_app.
      specialize (IHo final_fired t' Hnodup_app Hin_t_ff Hfun) as Hin_vee.
      elim Hin_vee.
      + intro Hin_t_fired; left; assumption.
      + intro Hin_t_tail; right; apply in_cons with (a := t) in Hin_t_tail; assumption.

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma sitpn_fire_aux_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg pgroup : list Trans)
           (final_fired : list Trans),
      (* Misc. hypotheses. *)
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->

      (* Hypotheses on pgroup. *)
      In pgroup sitpn.(priority_groups) ->

      (* Hypotheses on pg. *)
      IsDecListCons pg pgroup ->
      NoDup (fired ++ pg) ->

      (* Hypotheses on residual_marking. *)
      (forall (p : Place) (n : nat),
          In (p, n) (marking s) -> In (p, n - (pre_sum sitpn p fired)) residual_marking) ->
      (places sitpn) = (fst (split residual_marking)) ->

      (* Function ⇒ Specification *)
      sitpn_fire_aux sitpn s residual_marking fired pg = Some final_fired ->
      forall (t : Trans)
             (res_marking : list (Place * nat)),

        (* Hypotheses on t. *)
        In t pg ->
        SitpnIsFirable sitpn s t ->
        IsSensitized sitpn res_marking t ->
        
        (* Hypotheses on fired *)
        (forall t'' : Trans, In t'' fired -> HasHigherPriority t'' t pgroup /\
                                             In t'' final_fired) ->
        (* Hypotheses on res_marking. *)
        (places sitpn) = (fst (split res_marking)) ->
        (forall (pr : list Trans),
            NoDup pr /\
            (forall t' : Trans,
                HasHigherPriority t' t pgroup /\ In t' final_fired <->
                In t' pr) ->
            (forall (p : Place) (n : nat),
                In (p, n) (marking s) -> In (p, n - (pre_sum sitpn p pr)) res_marking)) ->
        In t final_fired.
  Proof.
    intros sitpn s residual_marking fired pg;
      functional induction (sitpn_fire_aux sitpn s residual_marking fired pg)
                 using sitpn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_sitpn Hwell_def_s
             Hin_sitpn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct Hfun
             t' res_marking Hin_t_pg Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m.

    (* BASE CASE, pg = []. *)
    - inversion Hin_t_pg.

    (* INDUCTION CASE *)
      
    (* CASE sitpn_is_firable t = true ∧ 
            is_sens t = true ∧ 
            update_marking_pre = residual_m' *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].

      (* First subcase, t = t' then t' ∈ (fired ++ [t]) ⇒ t' ∈ final_fired. *)
      + assert (Hin_t_fired : In t (fired ++ [t])) by (apply in_or_app; right; apply in_eq).
        rewrite <- Heq_tt'.
        apply (sitpn_fire_aux_in_fired sitpn s residual_marking' (fired ++ [t]) tail final_fired t
                                     Hin_t_fired Hfun).

      (* Second subcase, In t' tail then apply the induction hypothesis. *)
      + (* Builds condition 1:  
           ∀ (p, n) ∈ (marking s) ->  
           (p, n - pre_sum sitpn p (fired ++ [t])) ∈ residual_marking' *)

        (* We need ∀ (p, n) ∈ residual_marking ⇒  
           (p, n - pre_sum sitpn p [t]) ∈ residual_marking' *)

        (* Builds (fs (marking s)) = (fs res_marking) *)
        explode_well_defined_sitpn_state Hwell_def_s.
        unfold MarkingHaveSameStruct in *.
        assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
          by (rewrite <- Hwf_state_marking; rewrite <- Hsame_struct; reflexivity).

        (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
        explode_well_defined_sitpn;
          unfold NoDupPlaces in Hnodup_places;
          assert (Hnodup_fs_resm := Hnodup_places);
          rewrite Hsame_struct in Hnodup_fs_resm.
        
        (* We need In t (transs sitpn) to specialize 
           update_marking_pre_correct.
         *)
        deduce_in_transs.
        specialize (@update_marking_pre_correct
                      sitpn residual_marking t residual_marking' Hwell_def_sitpn
                      Hnodup_fs_resm Hin_t_transs e4) as Hin_res_in_fin.

        (* Then we need pre_sum_app_add *)
        specialize (pre_sum_app_add sitpn) as Heq_presum.
        
        (* Finally, deduces condition 1. *)
        assert (
            Hresid'_m :
              (forall (p : Place) (n : nat),
                  In (p, n) (marking s) ->
                  In (p, n - pre_sum sitpn p (fired ++ [t])) residual_marking')
          ).
        {
          intros p n Hin_ms.
          apply Hresid_m in Hin_ms.
          apply Hin_res_in_fin with (n := n - pre_sum sitpn p fired) in Hin_ms.
          assert (Heq_presum' : pre_sum sitpn p [t] = pre sitpn t p) by (simpl; auto).
          rewrite <- Nat.sub_add_distr in Hin_ms.
          specialize (Heq_presum p fired t).
          rewrite <- Heq_presum' in Hin_ms.
          rewrite Heq_presum in Hin_ms.
          assumption.
        }
        
        (* Builds condition 2:  
           ∀ t'' ∈ (fired ++ [t]), t'' ≻ t' ∧ t'' ∈ final_fired. *)
        assert(Hhigh_in_fired' :
                 forall t'' : Trans, In t'' (fired ++ [t]) ->
                                     HasHigherPriority t'' t' pgroup /\ In t'' final_fired).
        {
          intros t'' Hin_fired_app;
            apply in_app_or in Hin_fired_app;
            inversion Hin_fired_app as [Hin_fired | Heq_tst]; clear Hin_fired_app.
          - apply (Hhigh_in_fired t'' Hin_fired).
          - inversion Heq_tst as [Heq_tt | Hin_nil].
            (* Two things to build, t'' ≻ t' and t'' ∈ ff. *)
            + (* First, t'' ∈ ff *)
              assert (Hin_fired_app : In t (fired ++ [t]))
                by (apply in_or_app; right; apply in_eq).
              specialize (sitpn_fire_aux_in_fired
                            sitpn s residual_marking' (fired ++ [t]) tail final_fired t
                            Hin_fired_app Hfun) as Hin_ff.
              
              (* Second, t'' ≻ t' *)
              assert (Hsucc_ts_tp : HasHigherPriority t t' pgroup).
              {
                unfold HasHigherPriority.
                specialize (is_dec_list_cons_incl Hdec_list) as Hincl.
                split. assumption.
                split. unfold incl in Hincl. apply (Hincl t' (in_cons t t' tail Hin_t'_tail)).
                unfold IsPredInNoDupList.
                split.

                (* Proves t <> t'. *)
                apply NoDup_remove_2 in Hnodup_pg.
                apply not_app_in in Hnodup_pg; apply proj2 in Hnodup_pg.
                apply (not_in_in_diff t t' tail (conj Hnodup_pg Hin_t'_tail)).
                split.
                
                (* Proves NoDup pgroup. *)
                unfold NoIntersectInPriorityGroups in Hno_inter.
                apply (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                        pgroup Hin_sitpn_pgs).
                
                (* Proves IsPredInlist *)
                specialize (is_pred_in_list_in_tail t t' tail Hin_t'_tail) as His_pred.
                unfold NoIntersectInPriorityGroups in Hno_inter.
                specialize (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                             pgroup Hin_sitpn_pgs) as Hnodup_pgroup.
                apply (is_pred_in_dec_list His_pred Hdec_list Hnodup_pgroup).
              }
              
              rewrite <- Heq_tt.
              apply (conj Hsucc_ts_tp Hin_ff).
              
            + inversion Hin_nil.
        }
        
        (* Builds a few other hypotheses, and then applies IHo. *)
        apply update_marking_pre_same_marking in e4.
        rewrite e4 in Hsame_struct.
        rewrite <- app_assoc in IHo.
        apply (IHo pgroup final_fired
                   Hwell_def_sitpn Hwell_def_s Hin_sitpn_pgs (is_dec_list_cons_cons Hdec_list)
                   Hnodup_pg Hresid'_m Hsame_struct Hfun t' res_marking Hin_t'_tail
                   Hfirable_t Hsens_t Hhigh_in_fired' Hsame_struct' Hres_m).
        
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
      
    (* CASE, is_sensitized = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].

      (* First subcase, t = t'. *)
      
      (* What we want to show is a contradiction between is_sensitized = Some false
         and IsSensitized sitpn t' res_marking. 
         
         Then, we need to show that we have IsSensitized sitpn t' residual_marking. 
         We can deduce it from Hsens_t. *)
         
      (*   Hpr_is_fired is needed to specialize Hres_m. *)
      + assert (Hpr_is_fired :
                  forall t'' : Trans,
                    HasHigherPriority t'' t' pgroup /\ In t'' final_fired -> In t'' fired).
        {
          intros t'' Hw; elim Hw; intros Hhas_high Hin_ts_ff; clear Hw.
          specialize (NoDup_remove fired tail t Hnodup_pg) as Hnodup_app;
            apply proj1 in Hnodup_app.
          specialize (sitpn_fire_aux_final_fired_vee
                        sitpn s residual_marking fired tail final_fired t''
                        Hnodup_app Hin_ts_ff Hfun) as Hin_ts_vee.
          elim Hin_ts_vee.
          
          - auto.
          (* If t'' ∈ tail, then ~IsPredInNoDupList t'' t' (t' :: tail) ⇒  
             ~IsPredInNoDupList t'' t' pgroup, then contradiction. *)
          - intro Hin_ts_tail.
            unfold HasHigherPriority in Hhas_high.
            (* Builds ~IsPredInNoDuplist t'' t' (t' :: tail) *)
            assert (Hnot_is_pred : ~IsPredInNoDupList t'' t' (t' :: tail)) by
                apply not_is_pred_in_list_if_hd.
            rewrite Heq_tt' in Hdec_list.
            specialize (not_is_pred_in_dec_list Hdec_list Hin_ts_tail) as Hnot_is_pred_in_pg.
            decompose [and] Hhas_high; contradiction.
        }
        
        (* Now we have Hpr_is_fired, we can specialize Hres_m. *)
        assert (Hpr_iff :
                  forall t'' : Trans,
                    HasHigherPriority t'' t' pgroup /\ In t'' final_fired <-> In t'' fired)
          by (intros t'0; split; [apply (Hpr_is_fired t'0) | apply (Hhigh_in_fired t'0)]).
        specialize (nodup_app fired (t :: tail) Hnodup_pg) as Hnodup_fired.
        apply proj1 in Hnodup_fired.
        specialize (Hres_m fired (conj Hnodup_fired Hpr_iff)).

        (* Now we can show the equivalence between residual_marking and res_marking. *)
        assert (Hequiv_m : forall (p : Place) (n : nat), In (p, n) res_marking <->
                                                         In (p, n) residual_marking).
        {
          intros p n.
          split.
          - intro Hin_res_m.

            (* Builds (fs (marking s)) = (fs res_marking) *)
            explode_well_defined_sitpn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_resm_sm : fst (split res_marking) = fst (split (marking s)))
              by (rewrite <- Hwf_state_marking; rewrite <- Hsame_struct'; reflexivity).

            (* Builds In (p, x) (marking s) from In (p, n) res_marking. *)
            specialize (in_fst_split p n res_marking Hin_res_m) as Hin_fs_resm.
            rewrite Hsame_resm_sm in Hin_fs_resm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_resm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.

            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.

            (* Builds NoDup (fs res_marking) to apply nodup_same_pair. *)
            explode_well_defined_sitpn.
            unfold NoDupPlaces in Hnodup_places.
            assert (Hnodup_fs_resm := Hnodup_places).
            rewrite Hwf_state_marking in Hnodup_fs_resm.
            rewrite <- Hsame_resm_sm in Hnodup_fs_resm.

            (* Builds fs (p, n) = fs (p, x - pre_sum sitpn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum sitpn p fired))
              by (simpl; reflexivity).

            (* Applies nodup_same_pair to get n = x - pre_sum sitpn p fired. *)
            specialize (nodup_same_pair
                          res_marking Hnodup_fs_resm (p, n) (p, x - pre_sum sitpn p fired)
                          Hin_res_m Hin_res_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.

          - intro Hin_resid_m.

            (* Builds (fs (marking s)) = (fs res_marking) *)
            explode_well_defined_sitpn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
              by (rewrite <- Hwf_state_marking; rewrite <- Hsame_struct; reflexivity).

            (* Builds In (p, x) (marking s) from In (p, n) residual_marking. *)
            specialize (in_fst_split p n residual_marking Hin_resid_m) as Hin_fs_residm.
            rewrite Hsame_residm_sm in Hin_fs_residm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_residm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.

            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.

            (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
            explode_well_defined_sitpn.
            unfold NoDupPlaces in Hnodup_places.
            assert (Hnodup_fs_resm := Hnodup_places).
            rewrite Hwf_state_marking in Hnodup_fs_resm.
            rewrite <- Hsame_residm_sm in Hnodup_fs_resm.

            (* Builds fs (p, n) = fs (p, x - pre_sum sitpn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum sitpn p fired))
              by (simpl; reflexivity).

            (* Applies nodup_same_pair to get n = x - pre_sum sitpn p fired. *)
            specialize (nodup_same_pair
                          residual_marking Hnodup_fs_resm (p, n) (p, x - pre_sum sitpn p fired)
                          Hin_resid_m Hin_resid_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.
        }
        
        (* Then, we deduce IsSensitized sitpn residual_marking t' from Hequiv_m. *)
        assert (Hsens_t_in_residual_m : IsSensitized sitpn residual_marking t').
        {
          unfold IsSensitized.
          intros p n Hin_resid_m.
          rewrite <- Hequiv_m in Hin_resid_m.
          unfold IsSensitized in Hsens_t.
          apply (Hsens_t p n Hin_resid_m).
        }
        
        (* Then we apply is_sensitized_complete to show the contradiction with e3. *)
        deduce_in_transs.
        rewrite Heq_tt' in Hin_t_transs.
        specialize (is_sensitized_complete
                      Hwell_def_sitpn Hsame_struct Hin_t_transs Hsens_t_in_residual_m) as Hsens_t_false.
        rewrite Heq_tt' in e2.
        rewrite Hsens_t_false in e2; inversion e2.
        
      (* Second subcase, In t' tail then apply the induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list.
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s
                   Hin_sitpn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m).
        
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
      
    (* CASE, sitpn_is_firable = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].

      (* First subcase t = t', show a contradiction between e1 and Hfirable_t. *)
      + rewrite <- Heq_tt' in Hfirable_t.
        deduce_in_transs.
        apply (not_sitpn_is_firable_correct
                 Hwell_def_sitpn Hwell_def_s Hin_t_transs) in e0.
        contradiction.

      (* Second subcase, In t' tail, then apply induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list.
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s
                   Hin_sitpn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hsens_t Hhigh_in_fired Hsame_struct' Hres_m).
        
    (* ERROR CASE, sitpn_is_firable = None. *)
    - inversion Hfun.
  Qed.

  (** If [sitpn_fire_aux] returns a [fired] list and
      [sitpn_map_fire_aux] returns a [final_fired] list, when meeting
      certain conditions on the arguments of the two functions, the
      priority sets built based on [fired] or [final_fired] are
      equivalent. *)
  
  Lemma pr_is_unique :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (residual_marking : list (Place * nat))
           (pgroup : list Trans)
           (fired : list Trans)
           (fired' : list Trans)
           (pgroups : list (list Trans))
           (final_fired : list Trans)
           (t : Trans)
           (pr : list Trans),
      NoDup (fired' ++ pgroup ++ concat pgroups) ->
      sitpn_fire_aux sitpn s residual_marking [] pgroup = Some fired ->
      sitpn_map_fire_aux sitpn s (fired' ++ fired) pgroups = Some final_fired ->
      (forall t' : Trans, HasHigherPriority t' t pgroup /\ In t' fired <-> In t' pr) ->
      (forall t' : Trans, HasHigherPriority t' t pgroup /\ In t' final_fired <-> In t' pr).
  Proof.
    intros sitpn s residual_marking pgroup fired fired' pgroups final_fired t pr
           Hnodup_app Hfun_fire Hfun_map_fire Hin_pr t'.
    split.

    (* CASE, in context t' ≻ t ∧ t' ∈ final_fired *)
    - intro Hpr_wedge.

      (* Two subcases, either t' ∈ fired ∨ t' ∉ fired *)
      specialize (classic (In t' fired)) as Hin_fired_vee.
      inversion_clear Hin_fired_vee as [Hin_t'_fired | Hnot_in_t'_fired].

      (* First subcase, t' ∈ fired *)
      + elim Hpr_wedge; intros Hhas_high Hin_t'_ff.
        specialize (conj Hhas_high Hin_t'_fired) as Hpr_wedge'.
        rewrite Hin_pr in Hpr_wedge'.
        assumption.
        
      (* Second subcase,  
         t' ∈ pgroup ⇒
         t' ∉ fired' ∧ t' ∉ concat pgroups ∧ t' ∉ fired ⇒
         t' ∉ final_fired, contradicts Hpr_wedge. *)
        
      (* Builds In t' pgroup *)
      + elim Hpr_wedge; intros Hhas_high Hin_ff.
        unfold HasHigherPriority in Hhas_high;
          inversion_clear Hhas_high as (Hin_t'_pg & Hw);
          inversion_clear Hw as (Hin_t_pg & His_pred).

        (* Builds ~In t' fired /\ ~In t' concat pgroups *)
        apply NoDup_app_comm in Hnodup_app.
        rewrite <- app_assoc in Hnodup_app.
        specialize (nodup_app_not_in pgroup ((concat pgroups) ++ fired') Hnodup_app t' Hin_t'_pg)
          as Hnot_in_t'_app.
        apply not_app_in  in Hnot_in_t'_app.
        elim Hnot_in_t'_app; intros Hnot_in_concat Hnot_t'_in_fired.
        
        (* Builds ~In t' (fired' ++ fired) *)
        specialize (not_in_app t' fired' fired (conj Hnot_t'_in_fired Hnot_in_t'_fired))
          as Hnot_in_app.
        specialize (sitpn_map_fire_aux_not_in_not_fired
                      sitpn s (fired' ++ fired) pgroups final_fired Hfun_map_fire
                      t' Hnot_in_app Hnot_in_concat) as Hnot_in_ff.
        contradiction.
        
    (* CASE, in context t' ∈ pr *)
    - intro Hin_t'_pr.
      split.

      + rewrite <- Hin_pr in Hin_t'_pr.
        elim Hin_t'_pr; auto.
        
      (* t' ∈ fired ⇒ t' ∈ final_fired. *)
      + rewrite <- Hin_pr in Hin_t'_pr.
        elim Hin_t'_pr; intros Hhash_high Hin_t'_fired.

        (* Builds In t' (fired' ++ fired) to apply sitpn_map_fire_aux_in_fired. *)
        specialize (or_intror (In t' fired') Hin_t'_fired) as Hin_t'_vee.
        specialize (in_or_app fired' fired t' Hin_t'_vee) as Hin_t'_app.

        (* Applies sitpn_map_fire_aux_in_fired. *)
        apply (sitpn_map_fire_aux_in_fired
                 sitpn s (fired' ++ fired) pgroups final_fired
                 Hfun_map_fire t' Hin_t'_app).
  Qed.

  (** All transitions that are in the list [trs_2b_fired] returned by
      [sitpn_map_fire_aux] are both firable at state [s] and sensitized by
      the residual marking. *)
  
  Lemma sitpn_map_fire_aux_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (trs_2b_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      incl pgroups (priority_groups sitpn) ->
      NoDup (fired ++ concat pgroups) ->
      sitpn_map_fire_aux sitpn s fired pgroups = Some trs_2b_fired ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup pgroups ->
        In t pgroup ->
        ~In t fired ->
        (places sitpn) = (fst (split residual_marking)) ->
        SitpnIsFirable sitpn s t ->
        (forall (pr : list Trans),
            IsPrioritySet trs_2b_fired pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        IsSensitized sitpn residual_marking t ->
        In t trs_2b_fired.
  Proof.
    intros sitpn s fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn s fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros final_fired Hwell_def_sitpn Hwell_def_s Hincl_pgs Hnodup_concat_pgs
             Hfun pgroup' t residual_marking Hin_pgs Hin_t_pg Hnot_in_fired
             Hmark_struct Hfirable_t Hres_mark Hsens_t.

    (* BASE CASE *)
    - inversion Hin_pgs.

    (* GENERAL CASE, two subcases. *)
    - inversion Hin_pgs as [Heq_pg | Hin_pgtail].

      (* First subcase, pgroup = pgroup'. 
         
         Strategy:
         
         - apply sitpn_fire_aux_sens_by_residual ⇒ t ∈ fired_trs
         - t ∈ fired_trs ⇒ t ∈ (fired_transitions ++ fired_trs)
         - t ∈ (fired_transitions ++ fired_trs) ⇒ 
           apply sitpn_map_fire_aux_in_fired ⇒
           t ∈ trs_2b_fired *)
      + unfold sitpn_fire in *.
        rewrite Heq_pg in *.

        (* Step 1: Apply sitpn_fire_aux_sens_by_residual to get In t fired_trs *)
                
        (* Builds pgroup' ∈ (priority_groups sitpn). *)
        specialize (Hincl_pgs pgroup' Hin_pgs) as Hin_sitpn_pgs.

        (* Builds NoDup pgroup'. *)
        explode_well_defined_sitpn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups sitpn)
                                     Hno_inter pgroup' Hin_sitpn_pgs) as Hnodup_pg.

        (* Builds an hypothesis close to Hres_mark, except final_fired is replaced by fired_trs.  *)
        (* Necessary to apply sitpn_fire_aux_sens_by_residual. *)
        assert (Hres_mark' :
                  forall (pr : list Trans),
                    IsPrioritySet fired_trs pgroup t pr ->
                    forall (p : Place) (n : nat),
                      In (p, n) (marking s) ->
                      In (p, n - pre_sum sitpn p pr) residual_marking).
        {
          intros pr His_prior p n Hin_m_s.

          (* Unfolds and splits the content of IsPrioritySet *)
          unfold IsPrioritySet in His_prior;
            inversion_clear His_prior as (Hnodup_pr & Hhas_high).
          
          (* Builds hypotheses necessary to apply pr_is_unique. *)
          rewrite concat_cons in Hnodup_concat_pgs.

          (* Applies pr_is_unique. *)
          rewrite Heq_pg in Hhas_high.
          specialize (pr_is_unique
                        sitpn s (marking s) pgroup' fired_trs fired_transitions
                        pgroups_tail final_fired t pr Hnodup_concat_pgs e0 Hfun Hhas_high) as Hin_pr'.

          (* Unfolds IsPrioritySet in Hres_mark before completing the goal *)
          unfold IsPrioritySet in Hres_mark.          
          apply (Hres_mark pr (conj Hnodup_pr Hin_pr') p n Hin_m_s).
        }
        
        (* Builds ∀ (p, n) ∈ (marking s) ⇒ (p, n - pre_sum sitpn p []) ∈ residual *)
        assert (Hresid_m :
                  forall (p : Place) (n : nat),
                    In (p, n) (marking s) -> In (p, n - pre_sum sitpn p []) (marking s))
          by (simpl; intros; rewrite Nat.sub_0_r; assumption).
        
        (* Builds (places sitpn) (marking s) *)
        explode_well_defined_sitpn_state Hwell_def_s.

        (* Builds ∀ t' ∈ [] ⇒ t' ≻ t ∧ t' ∈ ff. *)
        assert (Hhigh_in_fired :
                  forall t' : Trans, In t' [] ->
                                     HasHigherPriority t' t pgroup' /\ In t' fired_trs)
          by (intros t' Hin_nil; inversion Hin_nil).

        (* Builds In t fired_trs. *)
        unfold IsPrioritySet in Hres_mark'.
        rewrite Heq_pg in Hres_mark'.
        specialize (@sitpn_fire_aux_sens_by_residual
                      sitpn s (marking s) [] pgroup' pgroup' fired_trs
                      Hwell_def_sitpn Hwell_def_s Hin_sitpn_pgs (IsDecListCons_refl pgroup')
                      Hnodup_pg Hresid_m Hwf_state_marking e0
                      t residual_marking Hin_t_pg Hfirable_t Hsens_t Hhigh_in_fired
                      Hmark_struct Hres_mark') as Hin_t_fired.

        (* Then if t ∈ fired_trs ⇒ t ∈ (fired_transitions ++ fired_trs) ⇒ t ∈ trs_2b_fired *)
        assert (Hin_fired_app : In t (fired_transitions ++ fired_trs))
          by (apply in_or_app; right; assumption).
        apply (sitpn_map_fire_aux_in_fired
                 sitpn s (fired_transitions ++ fired_trs) pgroups_tail
                 final_fired Hfun t Hin_fired_app).
        
      (* Second subcase, pgroup' ∈ pgroups_tail, then apply the induction hypothesis *)

      (* Builds incl pgroups_tail (priority_groups sitpn) *)
      + apply incl_cons_inv in Hincl_pgs.

        (* Builds ~In t fired_trs to build ~In t (fired_transitions ++ fired_trs). 
           But first, builds ~In t pgroup, because ~In t pgroup ⇒ ~In t fired_trs *)
        
        assert (Hnodup_concat_pgs_copy := Hnodup_concat_pgs).
        rewrite concat_cons in Hnodup_concat_pgs.
        apply NoDup_app_comm in Hnodup_concat_pgs.
        apply nodup_app in Hnodup_concat_pgs.
        elim Hnodup_concat_pgs; intros Hnodup_app Hnodup_fired.
        apply NoDup_app_comm in Hnodup_app.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_app)
          as Hnot_in_pgroup.
        specialize (in_concat t pgroup' pgroups_tail Hin_t_pg Hin_pgtail) as Hin_t_concat.
        specialize (Hnot_in_pgroup t Hin_t_concat) as Hnot_in_pgroup.
        unfold sitpn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (sitpn_fire_aux_not_in_not_fired
                      sitpn s (marking s) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pgroup e0) as Hnot_in_fired'.
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_app.

        (* Builds NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat_pgs_copy.
        
        (* First, we need NoDup fired_trs /\ incl fired_trs ([] ++ pgroup) *)
        apply nodup_app in Hnodup_app; elim Hnodup_app; intros Hnodup_concat_pgs' Hnodup_pg.
        rewrite <- app_nil_l in Hnodup_pg.
        specialize (@sitpn_fire_aux_nodup_fired
                      sitpn s (marking s) [] pgroup fired_trs
                      Hwell_def_sitpn Hnodup_pg e0)
          as Hnodup_incl.
        elim Hnodup_incl; intros Hnodup_fired_trs Hincl_fired.
        rewrite app_nil_l in Hincl_fired.
        specialize (nodup_app_incl
                      fired_transitions pgroup (concat pgroups_tail) fired_trs
                      Hnodup_concat_pgs_copy Hnodup_fired_trs Hincl_fired) as Hnodup_app'.
        rewrite app_assoc in Hnodup_app'.

        (* Finally applies the induction hypothesis. *)
        apply (IHo final_fired Hwell_def_sitpn Hwell_def_s
                   Hincl_pgs Hnodup_app' Hfun pgroup' t residual_marking
                   Hin_pgtail Hin_t_pg Hnot_in_app Hmark_struct Hfirable_t Hres_mark Hsens_t).
        
    (* ERROR CASE, sitpn_fire = None *)
    - inversion Hfun.
  Qed.

  (** All transitions that are in the list [trs_2b_fired] returned by
      [sitpn_map_fire] are both firable at state [s] and sensitized by
      the residual marking. *)
  
  Lemma sitpn_map_fire_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (trs_2b_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_map_fire sitpn s = Some trs_2b_fired ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        SitpnIsFirable sitpn s t ->
        (places sitpn) = (fst (split residual_marking)) ->
        (forall (pr : list Trans),
            IsPrioritySet trs_2b_fired pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        IsSensitized sitpn residual_marking t ->
        In t trs_2b_fired.
  Proof.
    intros sitpn s trs_2b_fired Hwell_def_sitpn Hwell_def_s Hfun
           pgroup t residual_marking Hin_pg_pgs Hin_t_pg Hfirable_t Heq_m
           Hresid_m His_sens_t.

    unfold sitpn_map_fire in Hfun.
    
    (* Builds NoDup ([] ++ concat (priority_groups sitpn)) *)
    explode_well_defined_sitpn.
    unfold NoIntersectInPriorityGroups in Hno_inter.
    rewrite <- app_nil_l in Hno_inter.
    
    (* Applies sitpn_map_fire_aux_sens_by_residual *)
    apply (@sitpn_map_fire_aux_sens_by_residual
             sitpn s [] (priority_groups sitpn) trs_2b_fired Hwell_def_sitpn Hwell_def_s
             (incl_refl (priority_groups sitpn)) Hno_inter Hfun pgroup t
             residual_marking Hin_pg_pgs Hin_t_pg (@in_nil Trans t)
             Heq_m Hfirable_t Hresid_m His_sens_t).
  Qed.
  
  (** All transitions that are firable a state [s'] and
      sensitized by the residual marking are fired. *)
  
  Lemma sitpn_falling_edge_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        SitpnIsFirable sitpn s' t ->
        (places sitpn) = (fst (split residual_marking)) ->
        (forall (pr : list Trans),
            IsPrioritySet s'.(fired) pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        IsSensitized sitpn residual_marking t ->
        In t s'.(fired).
  Proof.
    intros sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun.

    (* We need to build IsWellDefinedSitpnState sitpn s' before
       functional induction. *)
    specialize (sitpn_falling_edge_well_def_state
                  sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun)
      as Hwell_def_s'.

    (* Fun ind. on sitpn_falling_edge. *)
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.

    (* GENERAL CASE. *)
    - simpl in Hfun;
        injection Hfun as Heq_s';

        (* Rewrites s' in the goal. *)
        rewrite <- Heq_s';
        simpl.

      (* Simplifies e0 with tmp_state. *)
      set (tmp_state :=
             {|
               fired := [];
               marking := marking s;
               d_intervals := d_intervals';
               reset := reset s;
               cond_values := get_condition_values (conditions sitpn) time_value env [];
               exec_a := get_action_states sitpn s (actions sitpn) [];
               exec_f := exec_f s
             |}) in e0.

      (* We need to introduce t, pgroup and residual_marking in the
         context to specialize sitpn_is_firable_iff_eq and also
         to be able to rewrite SitpnIsFirable in the goal. *)
      intros pgroup t residual_marking.

      (* Builds premises of sitpn_is_firable_iff_eq. *)
      assert (Heq_m : (marking tmp_state = marking s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_ditvals : (d_intervals tmp_state = d_intervals s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_condv : (cond_values tmp_state = cond_values s')) by (rewrite <- Heq_s'; reflexivity).

      (* Specializes sitpn_is_firable_iff to get: 
         SitpnIsfirable tmp_state t = SitpnIsfirable s' t *)
      specialize (sitpn_is_firable_iff_eq sitpn tmp_state s' t Heq_m Heq_ditvals Heq_condv)
        as Heq_sitpn_is_firable.

      (* Rewrites SitpnIsFirable sitpn s' t by SitpnIsfirable sitpn
         tmp_state t in the goal and generalizes pgroup and t to match
         conclusion of lemma sitpn_map_fire_not_firable_not_fired. *)
      rewrite Heq_s'.
      rewrite <- Heq_sitpn_is_firable.
      generalize pgroup, t, residual_marking. (* Revert previously introduced pgroup and t. *)

      (* Gets IsWellDefinedSitpnState tmp_state before applying lemma. *)
      assert (Hnil_fired_s': fired tmp_state = []) by auto.
      assert (Heq_reset: reset s' = reset tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execa: exec_a s' = exec_a tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execf: exec_f s' = exec_f tmp_state) by (rewrite <- Heq_s'; auto).

      (* Specializes well-definition on tmp_state. *)
      specialize (is_well_def_tmp_state
                    sitpn s' tmp_state Hnil_fired_s' (eq_sym Heq_m) (eq_sym Heq_ditvals)
                    Heq_reset (eq_sym Heq_condv) Heq_execa Heq_execf Hwell_def_s')
        as Hwell_def_tmp.                                        
      
      (* Applies sitpn_map_fire_not_firable_not_fired to complete the
         subgoal. *)
      apply (sitpn_map_fire_sens_by_residual
               sitpn tmp_state trs_2b_fired Hwell_def_sitpn Hwell_def_tmp e0).

    (* ERROR CASE *)
    - inversion Hfun.
    - inversion Hfun.
  Qed.
  
End SitpnFallingEdgeSensByResidual.

(** Transitions that are firable but not sensitized
    by the residual marking are not fired. *)

Section SitpnNotSensitizedByResidual.

  Lemma sitpn_fire_aux_not_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pg pgroup : list Trans)
           (final_fired : list Trans),
      (* Misc. hypotheses. *)
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->

      (* Hypotheses on pgroup. *)
      In pgroup sitpn.(priority_groups) ->

      (* Hypotheses on pg. *)
      IsDecListCons pg pgroup ->
      NoDup (fired ++ pg) ->

      (* Hypotheses on residual_marking. *)
      (forall (p : Place) (n : nat),
          In (p, n) (marking s) -> In (p, n - (pre_sum sitpn p fired)) residual_marking) ->
      (places sitpn) = (fst (split residual_marking)) ->

      (* Function ⇒ Specification *)
      sitpn_fire_aux sitpn s residual_marking fired pg = Some final_fired ->
      forall (t : Trans)
             (res_marking : list (Place * nat)),

        (* Hypotheses on t. *)
        In t pg ->
        SitpnIsFirable sitpn s t ->
        ~IsSensitized sitpn res_marking t ->
        
        (* Hypotheses on fired *)
        (forall t'' : Trans, In t'' fired -> HasHigherPriority t'' t pgroup /\
                                             In t'' final_fired) ->
        (* Hypotheses on res_marking. *)
        (places sitpn) = (fst (split res_marking)) ->
        (forall (pr : list Trans),
            NoDup pr /\
            (forall t' : Trans,
                HasHigherPriority t' t pgroup /\ In t' final_fired <->
                In t' pr) ->
            (forall (p : Place) (n : nat),
                In (p, n) (marking s) -> In (p, n - (pre_sum sitpn p pr)) res_marking)) ->
        ~In t final_fired.
  Proof.
    intros sitpn s residual_marking fired pg;
      functional induction (sitpn_fire_aux sitpn s residual_marking fired pg)
                 using sitpn_fire_aux_ind;
      intros pgroup final_fired Hwell_def_sitpn Hwell_def_s
             Hin_sitpn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct Hfun
             t' res_marking Hin_t_pg Hfirable_t Hnotsens_t Hhigh_in_fired Hsame_struct' Hres_m.
    
    (* BASE CASE, pg = []. *)
    - inversion Hin_t_pg.
      
    (* GENERAL CASE, with two subcases. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].

      (* First subcase, t = t' *)
      (* We need to prove that residual_marking and res_marking are the same, 
         therefore, there is a contradiction between e3 and Hnotsens_t. *)
      + (* Hpr_is_fired is needed to specialize Hres_m. *)
        assert (Hpr_is_fired :
                  forall t'' : Trans, 
                    HasHigherPriority t'' t' pgroup /\ In t'' final_fired ->
                    In t'' fired). 
        {
          intros t'' Hw; elim Hw; intros Hhas_high Hin_ts_ff; clear Hw.
          specialize (sitpn_fire_aux_final_fired_vee
                        sitpn s residual_marking' (fired ++ [t]) tail final_fired t'')
            as Hff_vee.
          rewrite <- app_assoc in Hff_vee.
          specialize (Hff_vee Hnodup_pg Hin_ts_ff Hfun) as Hin_ts_vee; clear Hff_vee.
          inversion_clear Hin_ts_vee as [Hin_fired | Hin_ts_tail].

          - apply in_app_or in Hin_fired.
            inversion_clear Hin_fired as [Hin_fired_strict | Hin_tst].
            + assumption.
            + inversion Hin_tst as [Heq_tst | Hin_nil].

              (* Contradiction with the definition of t'' ≻ t' *)
              -- unfold HasHigherPriority in Hhas_high.
                 do 2 (apply proj2 in Hhas_high).
                 unfold IsPredInNoDupList in Hhas_high.
                 apply proj1 in Hhas_high.
                 symmetry in Heq_tst; rewrite Heq_tt' in Heq_tst.
                 contradiction.

              -- inversion Hin_nil.
                 
          (* If t'' ∈ tail, then ~IsPredInNoDupList t'' t' (t' :: tail) ⇒ 
             ~IsPredInNoDupList t'' t' pgroup, then contradiction. *)
          - unfold HasHigherPriority in Hhas_high.

            (* Builds ~IsPredInNoDuplist t'' t' (t' :: tail) *)
            assert (Hnot_is_pred : ~IsPredInNoDupList t'' t' (t' :: tail)) by
                apply not_is_pred_in_list_if_hd.
            rewrite Heq_tt' in Hdec_list.
            specialize (not_is_pred_in_dec_list Hdec_list Hin_ts_tail) as Hnot_is_pred_in_pg.
            decompose [and] Hhas_high; contradiction.
        }
        
        (* Now we have Hpr_is_fired, we can specialize Hres_m. *)
        assert (Hpr_iff :
                  forall t'' : Trans,
                    HasHigherPriority t'' t' pgroup /\ In t'' final_fired <-> In t'' fired)
          by (intros t'0; split; [apply (Hpr_is_fired t'0) | apply (Hhigh_in_fired t'0)]).
        specialize (nodup_app fired (t :: tail) Hnodup_pg) as Hnodup_fired.
        apply proj1 in Hnodup_fired.
        specialize (Hres_m fired (conj Hnodup_fired Hpr_iff)).
        
        (* Now we can show the equivalence between residual_marking and res_marking. *)
        assert (Hequiv_m : forall (p : Place) (n : nat), In (p, n) res_marking <->
                                                         In (p, n) residual_marking).
        {
          intros p n.
          split.
          - intro Hin_res_m.
            (* Builds (fs (marking s)) = (fs res_marking) *)
            explode_well_defined_sitpn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_resm_sm : fst (split res_marking) = fst (split (marking s)))
              by (rewrite <- Hwf_state_marking; rewrite <- Hsame_struct'; reflexivity).
            
            (* Builds In (p, x) (marking s) from In (p, n) res_marking. *)
            specialize (in_fst_split p n res_marking Hin_res_m) as Hin_fs_resm.
            rewrite Hsame_resm_sm in Hin_fs_resm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_resm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.
            
            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.
            
            (* Builds NoDup (fs res_marking) to apply nodup_same_pair. *)
            explode_well_defined_sitpn.
            unfold NoDupPlaces in Hnodup_places.
            assert (Hnodup_fs_resm := Hnodup_places).
            rewrite Hwf_state_marking in Hnodup_fs_resm;
              rewrite <- Hsame_resm_sm in Hnodup_fs_resm.
            
            (* Builds fs (p, n) = fs (p, x - pre_sum sitpn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum sitpn p fired))
              by (simpl; reflexivity).
            
            (* Applies nodup_same_pair to get n = x - pre_sum sitpn p fired. *)
            specialize (nodup_same_pair
                          res_marking Hnodup_fs_resm (p, n) (p, x - pre_sum sitpn p fired)
                          Hin_res_m Hin_res_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.
            
          - intro Hin_resid_m.

            (* Builds (fs (marking s)) = (fs res_marking) *)
            explode_well_defined_sitpn_state Hwell_def_s.
            unfold MarkingHaveSameStruct in *.
            assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
              by (rewrite <- Hwf_state_marking; rewrite <- Hsame_struct; reflexivity).
            
            (* Builds In (p, x) (marking s) from In (p, n) residual_marking. *)
            specialize (in_fst_split p n residual_marking Hin_resid_m) as Hin_fs_residm.
            rewrite Hsame_residm_sm in Hin_fs_residm.
            specialize (in_fst_split_in_pair p (marking s) Hin_fs_residm) as Hex_ms.
            elim Hex_ms; intros x Hin_x_ms.
            
            (* Applies Hresid_m and Hres_m. *)
            specialize (Hresid_m p x Hin_x_ms) as Hin_resid_m'.
            specialize (Hres_m p x Hin_x_ms) as Hin_res_m'.
            
            (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
            explode_well_defined_sitpn.
            unfold NoDupPlaces in Hnodup_places.
            assert (Hnodup_fs_residm := Hnodup_places);
              rewrite Hwf_state_marking in Hnodup_fs_residm;
              rewrite <- Hsame_residm_sm in Hnodup_fs_residm.

            (* Builds fs (p, n) = fs (p, x - pre_sum sitpn p fired) *)
            assert (Heq_fs : fst (p, n) = fst (p, x - pre_sum sitpn p fired))
              by (simpl; reflexivity).                    

            (* Applies nodup_same_pair to get n = x - pre_sum sitpn p fired. *)
            specialize (nodup_same_pair
                          residual_marking Hnodup_fs_residm (p, n) (p, x - pre_sum sitpn p fired)
                          Hin_resid_m Hin_resid_m' Heq_fs) as Heq_nx.
            injection Heq_nx as Heq_nx.
            rewrite Heq_nx.
            assumption.
        }
        
        (* Introduces IsSensitized sitpn res_marking t. *)
        deduce_in_transs.
        apply (@is_sensitized_correct
                 sitpn residual_marking t
                 Hwell_def_sitpn
                 Hsame_struct Hin_t_transs) in e2.
        
        assert (Hsens_t_in_res_m : IsSensitized sitpn res_marking t).
        {
          unfold IsSensitized.
          intros p n Hin_resid_m.
          rewrite Hequiv_m in Hin_resid_m.
          unfold IsSensitized in e2.
          apply (e2 p n Hin_resid_m).
        }
        
        rewrite Heq_tt' in Hsens_t_in_res_m.
        contradiction.

      (* Second subcase, In t' tail then apply the induction hypothesis. *)
      + (* Builds condition 1: 
           ∀ (p, n) ∈ (marking s) -> 
             (p, n - pre_sum sitpn p (fired ++ [t])) ∈ residual_marking' *)
        (* We need ∀ (p, n) ∈ residual_marking ⇒ 
                     (p, n - pre_sum sitpn p [t]) ∈ residual_marking' *)
        
        (* Builds (fs (marking s)) = (fs res_marking) *)
        explode_well_defined_sitpn_state Hwell_def_s.
        assert (Hsame_residm_sm : fst (split residual_marking) = fst (split (marking s)))
          by (rewrite <- Hwf_state_marking; rewrite <- Hsame_struct; reflexivity).
        
        (* Builds NoDup (fs residual_marking) to apply nodup_same_pair. *)
        explode_well_defined_sitpn.
        unfold NoDupPlaces in Hnodup_places.
        assert (Hnodup_fs_residm := Hnodup_places);
          rewrite Hwf_state_marking in Hnodup_fs_residm;
          rewrite <- Hsame_residm_sm in Hnodup_fs_residm.
        
        (* Builds In t (transs sitpn) *)
        deduce_in_transs.
        specialize (@update_marking_pre_correct
                      sitpn residual_marking t residual_marking'
                      Hwell_def_sitpn Hnodup_fs_residm Hin_t_transs e4) as Hin_res_in_fin.
        
        (* Then we need pre_sum_app_add *)
        specialize (pre_sum_app_add sitpn) as Heq_presum.
        
        (* Finally, deduces condition 1. *)
        assert (
            Hresid'_m :
              (forall (p : Place) (n : nat),
                  In (p, n) (marking s) ->
                  In (p, n - pre_sum sitpn p (fired ++ [t])) residual_marking')
          ).
        {
          intros p n Hin_ms.
          apply Hresid_m in Hin_ms.
          apply Hin_res_in_fin with (n := n - pre_sum sitpn p fired) in Hin_ms.
          assert (Heq_presum' : pre_sum sitpn p [t] = pre sitpn t p) by (simpl; auto).
          rewrite <- Nat.sub_add_distr in Hin_ms.
          specialize (Heq_presum p fired t).
          rewrite <- Heq_presum' in Hin_ms.
          rewrite Heq_presum in Hin_ms.
          assumption.
        }
        
        (* Builds condition 2: 
           ∀ t'' ∈ (fired ++ [t]), t'' ≻ t' ∧ t'' ∈ final_fired. *)
        assert(Hhigh_in_fired' :
                 forall t'' : Trans, In t'' (fired ++ [t]) ->
                                     HasHigherPriority t'' t' pgroup /\ In t'' final_fired).
        {
          intros t'' Hin_fired_app;
            apply in_app_or in Hin_fired_app;
            inversion Hin_fired_app as [Hin_fired | Heq_tst]; clear Hin_fired_app.
          
          - apply (Hhigh_in_fired t'' Hin_fired).
          - inversion Heq_tst as [Heq_tt | Hin_nil].

            (* Two things to build, t'' ≻ t' and t'' ∈ ff. *)
            + (* First, t'' ∈ ff *)
              assert (Hin_fired_app : In t (fired ++ [t]))
                by (apply in_or_app; right; apply in_eq).
              specialize (sitpn_fire_aux_in_fired
                            sitpn s residual_marking' (fired ++ [t]) tail final_fired t
                            Hin_fired_app Hfun) as Hin_ff.

              (* Second, t'' ≻ t' *)
              assert (Hsucc_ts_tp : HasHigherPriority t t' pgroup).
              {
                unfold HasHigherPriority.
                specialize (is_dec_list_cons_incl Hdec_list) as Hincl.
                split. assumption. 
                split. unfold incl in Hincl. apply (Hincl t' (in_cons t t' tail Hin_t'_tail)).
                unfold IsPredInNoDupList.
                split.

                (* Proves t <> t'. *)
                apply NoDup_remove_2 in Hnodup_pg.
                apply not_app_in in Hnodup_pg; apply proj2 in Hnodup_pg.
                apply (not_in_in_diff t t' tail (conj Hnodup_pg Hin_t'_tail)).
                split.

                (* Proves NoDup pgroup. *)
                unfold NoIntersectInPriorityGroups in Hno_inter.
                apply (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                        pgroup Hin_sitpn_pgs).

                (* Proves IsPredInlist *)
                specialize (is_pred_in_list_in_tail t t' tail Hin_t'_tail) as His_pred.
                unfold NoIntersectInPriorityGroups in Hno_inter.
                specialize (nodup_concat_gen (priority_groups sitpn) Hno_inter
                                             pgroup Hin_sitpn_pgs) as Hnodup_pgroup.
                apply (is_pred_in_dec_list His_pred Hdec_list Hnodup_pgroup).
              }
              rewrite <- Heq_tt.
              apply (conj Hsucc_ts_tp Hin_ff).
            + inversion Hin_nil.
        }

        (* Builds a few other hypotheses, and then applies IHo. *)
        apply update_marking_pre_aux_same_marking in e4.
        rewrite e4 in Hsame_struct.
        rewrite <- app_assoc in IHo.
        apply (IHo pgroup final_fired
                   Hwell_def_sitpn Hwell_def_s Hin_sitpn_pgs (is_dec_list_cons_cons Hdec_list)
                   Hnodup_pg Hresid'_m Hsame_struct Hfun t' res_marking Hin_t'_tail
                   Hfirable_t Hnotsens_t Hhigh_in_fired' Hsame_struct' Hres_m).
        
    (* ERROR CASE, update_residual_marking = None. *)
    - inversion Hfun.
      
    (* CASE is_sensitized = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_tail].
      
      (* Subcase 1, t = t', apply sitpn_fire_aux_not_in_not_fired. *)
      + apply NoDup_remove_2 in Hnodup_pg.
        apply not_app_in in Hnodup_pg.
        inversion_clear Hnodup_pg as (Hnot_in_fired & Hnot_in_tl).
        rewrite <- Heq_tt'.
        apply (sitpn_fire_aux_not_in_not_fired
                 sitpn s residual_marking fired tail final_fired t
                 Hnot_in_fired Hnot_in_tl Hfun).

      (* Subcase 2, t ∈ tail, then aplpy induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s 
                   Hin_sitpn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_tail Hfirable_t Hnotsens_t Hhigh_in_fired Hsame_struct' Hres_m).
        
    (* ERROR CASE, is_sensitized = None. *)
    - inversion Hfun.
      
    (* CASE, sitpn_is_firable = Some false. *)
    - inversion_clear Hin_t_pg as [ Heq_tt' | Hin_t'_tail ].

      (* First subcase t = t', show a contradiction between e1 and Hfirable_t. *)
      + rewrite <- Heq_tt' in Hfirable_t.
        deduce_in_transs.
        apply (not_sitpn_is_firable_correct
                 Hwell_def_sitpn Hwell_def_s Hin_t_transs) in e0.
        contradiction.

      (* Second subcase, In t' tail, then apply induction hypothesis. *)
      + apply is_dec_list_cons_cons in Hdec_list. 
        apply NoDup_remove in Hnodup_pg; apply proj1 in Hnodup_pg.
        apply (IHo pgroup final_fired Hwell_def_sitpn Hwell_def_s 
                   Hin_sitpn_pgs Hdec_list Hnodup_pg Hresid_m Hsame_struct
                   Hfun t' res_marking
                   Hin_t'_tail Hfirable_t Hnotsens_t Hhigh_in_fired Hsame_struct' Hres_m).
        
    (* ERROR CASE, sitpn_is_firable = None. *)
    - inversion Hfun.
  Qed.
  
  Lemma sitpn_map_fire_aux_not_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (fired : list Trans)
           (pgroups : list (list Trans))
           (trs_2b_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      incl pgroups (priority_groups sitpn) ->
      NoDup (fired ++ concat pgroups) ->
      sitpn_map_fire_aux sitpn s fired pgroups = Some trs_2b_fired ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup pgroups ->
        In t pgroup ->
        ~In t fired ->
        (places sitpn) = (fst (split residual_marking)) ->
        SitpnIsFirable sitpn s t ->
        (forall (pr : list Trans),
            IsPrioritySet trs_2b_fired pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        ~IsSensitized sitpn residual_marking t ->
        ~In t trs_2b_fired.
  Proof.
    intros sitpn s fired pgroups;
      functional induction (sitpn_map_fire_aux sitpn s fired pgroups)
                 using sitpn_map_fire_aux_ind;
      intros final_fired Hwell_def_sitpn Hwell_def_s Hincl_pgs Hnodup_concat_pgs
             Hfun pgroup' t residual_marking Hin_pgs Hin_t_pg Hnot_in_fired
             Hmark_struct Hfirable_t Hres_mark Hnotsens_t.
    
    (* BASE CASE *)
    - inversion Hin_pgs.
      
    (* GENERAL CASE, two subcases. *)
    - inversion Hin_pgs as [Heq_pg | Hin_pgtail].
      
      (* First case, pgroup = pgroup'.
         t ∉ fired_transitions ∧ t ∉ fired_trs ∧ t ∉ (concat pgroups_tail) ⇒ 
         t ∉ final_fired. *)
      
      + (* Builds t ∉ fired_trs from e0 (sitpn_fire). *)
        unfold sitpn_fire in *.
        rewrite Heq_pg in *.

        (* Builds pgroup' ∈ (priority_groups sitpn). *)
        specialize (Hincl_pgs pgroup' Hin_pgs) as Hin_sitpn_pgs.

        (* Builds NoDup pgroup'. *)
        explode_well_defined_sitpn.
        unfold NoIntersectInPriorityGroups in *.
        specialize (nodup_concat_gen (priority_groups sitpn)
                                     Hno_inter pgroup' Hin_sitpn_pgs) as Hnodup_pg.
        
        (* Builds an hypothesis close to Hres_mark, except final_fired is replaced by fired_trs. 
           Necessary to apply sitpn_fire_aux_sens_by_residual. *)
        assert (Hres_mark' :
                  forall (pr : list Trans),
                    NoDup pr /\
                    (forall t' : Trans,
                        HasHigherPriority t' t pgroup' /\ In t' fired_trs <-> In t' pr) ->
                    forall (p : Place) (n : nat),
                      In (p, n) (marking s) ->
                      In (p, n - pre_sum sitpn p pr) residual_marking).
        {
          intros pr [Hnodup_pr Hin_pr] p n Hin_m_s.

          (* Builds hypotheses necessary to apply pr_is_unique. *)
          rewrite concat_cons in Hnodup_concat_pgs.

          (* Applies pr_is_unique. *)
          unfold IsPrioritySet in Hres_mark.
          specialize (pr_is_unique
                        sitpn s (marking s) pgroup' fired_trs fired_transitions
                        pgroups_tail final_fired t pr Hnodup_concat_pgs e0 Hfun Hin_pr) as Hin_pr'.
          apply (Hres_mark pr (conj Hnodup_pr Hin_pr') p n Hin_m_s).
        }
        
        (* Builds ∀ (p, n) ∈ (marking s) ⇒ (p, n - pre_sum sitpn p []) ∈ residual *)
        assert (Hresid_m :
                  forall (p : Place) (n : nat),
                    In (p, n) (marking s) -> In (p, n - pre_sum sitpn p []) (marking s))
          by (simpl; intros; rewrite Nat.sub_0_r; assumption).

        (* Builds MarkingHaveSamestruct (initial_marking sitpn) (marking s) *)
        explode_well_defined_sitpn_state Hwell_def_s.

        (* Builds ∀ t' ∈ [] ⇒ t' ≻ t ∧ t' ∈ ff. *)
        assert (Hhigh_in_fired :
                  forall t' : Trans, In t' [] ->
                                     HasHigherPriority t' t pgroup' /\ In t' fired_trs)
          by (intros t' Hin_nil; inversion Hin_nil).
        
        (* Builds ~In t fired_trs. *)
        specialize (sitpn_fire_aux_not_sens_by_residual
                      sitpn s (marking s) [] pgroup' pgroup' fired_trs
                      Hwell_def_sitpn Hwell_def_s Hin_sitpn_pgs (IsDecListCons_refl pgroup')
                      Hnodup_pg Hresid_m Hwf_state_marking e0
                      t residual_marking Hin_t_pg Hfirable_t Hnotsens_t Hhigh_in_fired
                      Hmark_struct Hres_mark') as Hnot_in_fired'.
        
        (* Then we need, ~In t (concat pgroups_tail) *)
        specialize (nodup_app fired_transitions (concat (pgroup' :: pgroups_tail))
                              Hnodup_concat_pgs) as Hnodup_concat.
        apply proj2 in Hnodup_concat.
        rewrite concat_cons in Hnodup_concat.
        specialize (nodup_app_not_in pgroup' (concat pgroups_tail)
                                     Hnodup_concat t Hin_t_pg) as Hnot_in_concat.
        (* Then if t ∉ fired_trs ⇒ t ∉ (fired_transitions ++ fired_trs) ∧
                   t ∉ concat pgroups_tail ⇒ t ∈ final_fired *)
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnotin_fired_app.
        apply (sitpn_map_fire_aux_not_in_not_fired
                 sitpn s (fired_transitions ++ fired_trs) pgroups_tail
                 final_fired Hfun t Hnotin_fired_app Hnot_in_concat).
      (* Second subcase, pgroup' ∈ pgroups_tail, then apply the induction hypothesis *)
      (* Builds incl pgroups_tail (priority_groups sitpn) *)
      + apply incl_cons_inv in Hincl_pgs. 
        (* Builds ~In t fired_trs to build ~In t (fired_transitions ++ fired_trs). *)
        (* But first, builds ~In t pgroup, because ~In t pgroup ⇒ ~In t fired_trs *)
        assert (Hnodup_concat_pgs_copy := Hnodup_concat_pgs).
        rewrite concat_cons in Hnodup_concat_pgs.
        apply NoDup_app_comm in Hnodup_concat_pgs.
        apply nodup_app in Hnodup_concat_pgs.
        elim Hnodup_concat_pgs; intros Hnodup_app Hnodup_fired.
        apply NoDup_app_comm in Hnodup_app.
        specialize (nodup_app_not_in (concat pgroups_tail) pgroup Hnodup_app)
          as Hnot_in_pgroup.
        specialize (in_concat t pgroup' pgroups_tail Hin_t_pg Hin_pgtail) as Hin_t_concat.
        specialize (Hnot_in_pgroup t Hin_t_concat) as Hnot_in_pgroup.
        unfold sitpn_fire in e0.
        assert (Hnot_in_nil : ~In t []) by apply in_nil.
        specialize (sitpn_fire_aux_not_in_not_fired
                      sitpn s (marking s) [] pgroup fired_trs t
                      Hnot_in_nil Hnot_in_pgroup e0) as Hnot_in_fired'.
        specialize (not_in_app t fired_transitions fired_trs (conj Hnot_in_fired Hnot_in_fired'))
          as Hnot_in_app.

        (* Builds NoDup ((fired_transitions ++ fired_trs) ++ concat pgroups_tail). *)
        rewrite concat_cons in Hnodup_concat_pgs_copy.
        
        (* First, we need NoDup fired_trs /\ incl fired_trs ([] ++ pgroup) *)
        apply nodup_app in Hnodup_app; elim Hnodup_app; intros Hnodup_concat_pgs' Hnodup_pg.
        rewrite <- app_nil_l in Hnodup_pg.
        specialize (sitpn_fire_aux_nodup_fired sitpn s (marking s) [] pgroup fired_trs
                                             Hwell_def_sitpn Hnodup_pg e0)
          as Hnodup_incl.
        elim Hnodup_incl; intros Hnodup_fired_trs Hincl_fired.
        rewrite app_nil_l in Hincl_fired.
        specialize (nodup_app_incl
                      fired_transitions pgroup (concat pgroups_tail) fired_trs
                      Hnodup_concat_pgs_copy Hnodup_fired_trs Hincl_fired) as Hnodup_app'.
        rewrite app_assoc in Hnodup_app'.
        
        (* Finally applies the induction hypothesis. *)
        apply (IHo final_fired Hwell_def_sitpn Hwell_def_s
                   Hincl_pgs Hnodup_app' Hfun pgroup' t residual_marking
                   Hin_pgtail Hin_t_pg Hnot_in_app Hmark_struct Hfirable_t Hres_mark Hnotsens_t).
        
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (** Are not in the list [trs_2b_fired] returned by [sitpn_map_fire],
      all transitions that are firable at state [s] but not sensitized
      by the residual marking. *)
  
  Lemma sitpn_map_fire_not_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (trs_2b_fired : list Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_map_fire sitpn s = Some trs_2b_fired ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        SitpnIsFirable sitpn s t ->
        (places sitpn) = (fst (split residual_marking)) ->
        (forall (pr : list Trans),
            IsPrioritySet trs_2b_fired pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        ~IsSensitized sitpn residual_marking t ->
        ~In t trs_2b_fired.
  Proof.
    intros sitpn s trs_2b_fired Hwell_def_sitpn Hwell_def_s Hfun
           pgroup t residual_marking Hin_pg_pgs Hin_t_pg Hfirable_t Heq_m
           Hresid_m His_sens_t.

    unfold sitpn_map_fire in Hfun.
    
    (* Builds NoDup ([] ++ concat (priority_groups sitpn)) *)
    explode_well_defined_sitpn.
    unfold NoIntersectInPriorityGroups in Hno_inter.
    rewrite <- app_nil_l in Hno_inter.
    
    (* Applies sitpn_map_fire_aux_sens_by_residual *)
    apply (@sitpn_map_fire_aux_not_sens_by_residual
             sitpn s [] (priority_groups sitpn) trs_2b_fired Hwell_def_sitpn Hwell_def_s
             (incl_refl (priority_groups sitpn)) Hno_inter Hfun pgroup t
             residual_marking Hin_pg_pgs Hin_t_pg (@in_nil Trans t)
             Heq_m Hfirable_t Hresid_m His_sens_t).
  Qed.

  (** All transitions that are firable a state [s'] but not sensitized
      by the residual marking are not fired. *)
  
  Lemma sitpn_falling_edge_not_sens_by_residual :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      forall (pgroup : list Trans)
             (t : Trans)
             (residual_marking : list (Place * nat)),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        SitpnIsFirable sitpn s' t ->
        (places sitpn) = (fst (split residual_marking)) ->
        (forall (pr : list Trans),
            IsPrioritySet s'.(fired) pgroup t pr ->
            (forall (p : Place)
                    (n : nat),
                In (p, n) s.(marking) ->
                In (p, n - pre_sum sitpn p pr) residual_marking)) ->
        ~IsSensitized sitpn residual_marking t ->
        ~In t s'.(fired).
  Proof.
    intros sitpn s time_value env s' Hwell_def_sitpn Hwell_def_s Hfun.

    (* We need to build IsWellDefinedSitpnState sitpn s' before
       functional induction. *)
    specialize (sitpn_falling_edge_well_def_state
                  sitpn s s' time_value env Hwell_def_sitpn Hwell_def_s Hfun)
      as Hwell_def_s'.

    (* Fun ind. on sitpn_falling_edge. *)
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind.

    (* GENERAL CASE. *)
    - simpl in Hfun;
        injection Hfun as Heq_s';

        (* Rewrites s' in the goal. *)
        rewrite <- Heq_s';
        simpl.

      (* Simplifies e0 with tmp_state. *)
      set (tmp_state :=
             {|
               fired := [];
               marking := marking s;
               d_intervals := d_intervals';
               reset := reset s;
               cond_values := get_condition_values (conditions sitpn) time_value env [];
               exec_a := get_action_states sitpn s (actions sitpn) [];
               exec_f := exec_f s
             |}) in e0.

      (* We need to introduce t, pgroup and residual_marking in the
         context to specialize sitpn_is_firable_iff_eq and also
         to be able to rewrite SitpnIsFirable in the goal. *)
      intros pgroup t residual_marking.

      (* Builds premises of sitpn_is_firable_iff_eq. *)
      assert (Heq_m : (marking tmp_state = marking s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_ditvals : (d_intervals tmp_state = d_intervals s')) by (rewrite <- Heq_s'; reflexivity).
      assert (Heq_condv : (cond_values tmp_state = cond_values s')) by (rewrite <- Heq_s'; reflexivity).

      (* Specializes sitpn_is_firable_iff to get: 
         SitpnIsfirable tmp_state t = SitpnIsfirable s' t *)
      specialize (sitpn_is_firable_iff_eq sitpn tmp_state s' t Heq_m Heq_ditvals Heq_condv)
        as Heq_sitpn_is_firable.

      (* Rewrites SitpnIsFirable sitpn s' t by SitpnIsfirable sitpn
         tmp_state t in the goal and generalizes pgroup and t to match
         conclusion of lemma sitpn_map_fire_not_firable_not_fired. *)
      rewrite Heq_s'.
      rewrite <- Heq_sitpn_is_firable.
      generalize pgroup, t, residual_marking. (* Revert previously introduced pgroup and t. *)

      (* Gets IsWellDefinedSitpnState tmp_state before applying lemma. *)
      assert (Hnil_fired_s': fired tmp_state = []) by auto.
      assert (Heq_reset: reset s' = reset tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execa: exec_a s' = exec_a tmp_state) by (rewrite <- Heq_s'; auto).
      assert (Heq_execf: exec_f s' = exec_f tmp_state) by (rewrite <- Heq_s'; auto).

      (* Specializes well-definition on tmp_state. *)
      specialize (is_well_def_tmp_state
                    sitpn s' tmp_state Hnil_fired_s' (eq_sym Heq_m) (eq_sym Heq_ditvals)
                    Heq_reset (eq_sym Heq_condv) Heq_execa Heq_execf Hwell_def_s')
        as Hwell_def_tmp.                                        
      
      (* Applies sitpn_map_fire_not_firable_not_fired to complete the
         subgoal. *)
      apply (sitpn_map_fire_not_sens_by_residual
               sitpn tmp_state trs_2b_fired Hwell_def_sitpn Hwell_def_tmp e0).

    (* ERROR CASE *)
    - inversion Hfun.
    - inversion Hfun.
  Qed.
  
End SitpnNotSensitizedByResidual.
