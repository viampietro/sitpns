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

(* Import misc. lemmas, tactics and definitions. *)




(* Import lemmas about marking. *)

Require Import simpl.SitpnWellDefMarking.
Require Import simpl.SitpnRisingEdgeMarking.
Require Import simpl.SitpnFallingEdgeFiredComplete.

(* Import classical logic. *)

Require Import Classical_Prop.

(** * Completeness for [map_update_marking_pre]. *)

Section MapUpdateMarkingPreComplete.

  (** Completeness lemma for [modify_m]. *)

  Lemma modify_m_complete :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat),
      In p (fs marking) ->
      NoDup (fs marking) ->
      exists m' : list (Place * nat),
        modify_m marking p op nboftokens = Some m'
        /\ forall (n : nat), In (p, n) marking -> In (p, op n nboftokens) m'.
  Proof.
    induction marking.

    (* BASE CASE, marking = [] *)
    - intros p op nboftokens Hin; simpl in Hin; inversion Hin.

    (* INDUCTION CASE *)
    - destruct a; simpl; intros pl op nboftkens Hin_p_fsm Hnodup_fsm.

      (* Two case, for p =? pl *)
      case_eq (p =? pl); intros Heq_ppl.

      (* Case (p =? pl) = true *)
      + exists ((pl, op n nboftkens) :: marking).
        repeat split.
        intros nb Hv; inversion_clear Hv as [Heq_pn | Hin_m].
        
        (* Case (p, n) = (pl, nb) *)
        -- injection Heq_pn as Heq_p Heq_n; rewrite Heq_n; apply in_eq.

        (* Case (pl, nb) ∈ marking, contradiction with NoDup (fs ((p, n) :: marking)) 
           knowing that p = pl. *)
        -- apply beq_nat_true in Heq_ppl.
           rewrite Heq_ppl in Hnodup_fsm.
           unfold fs in Hnodup_fsm; rewrite fst_split_cons_app in Hnodup_fsm.
           simpl in Hnodup_fsm.
           rewrite NoDup_cons_iff in Hnodup_fsm.
           apply proj1 in Hnodup_fsm.
           apply in_fst_split in Hin_m.
           contradiction.

      (* Case (p =? pl) = false *)
      +
        (* Specializes IHmarking. *)

        assert (Hin_p_fsm' : In pl (fs marking)).
        {
          unfold fs in Hin_p_fsm; rewrite fst_split_cons_app in Hin_p_fsm.
          simpl in Hin_p_fsm.
          apply beq_nat_false in Heq_ppl.
          inversion_clear Hin_p_fsm as [Heq_ppl' | Hin_pl_fsm];
            [ contradiction | assumption ].
        }

        assert (Hnodup_fsm' : NoDup (fs marking)).
        {
          unfold fs in Hnodup_fsm; rewrite fst_split_cons_app in Hnodup_fsm.
          simpl in Hnodup_fsm.
          rewrite NoDup_cons_iff in Hnodup_fsm.
          apply proj2 in Hnodup_fsm.
          assumption.
        }

        specialize (IHmarking pl op nboftkens Hin_p_fsm' Hnodup_fsm')
          as Hex_modif_m.
        inversion_clear Hex_modif_m as (m' & Hw_modif_m).
        inversion_clear Hw_modif_m as (Hmodif_m & Hdef_m').

        (* Rewrites the goal with the newly-built hypothesis. *)
        rewrite Hmodif_m.

        (* Instantiates the new marking, then completes the goal. *)
        exists ((p, n) :: m').
        repeat split.
        intros nb Hw.
        inversion_clear Hw as [Heq_pn | Hin_m].
        -- injection Heq_pn as Heq_p Heq_n.
           apply beq_nat_false in Heq_ppl; contradiction.
        -- apply in_cons; apply (Hdef_m' nb Hin_m).           
  Qed.
  
  (** Completeness lemma for [update_marking_pre_aux]. *)

  Lemma update_marking_pre_aux_complete :
    forall (pre_places : list Place)
           (sitpn : Sitpn)
           (t : Trans)
           (marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      Permutation (places sitpn) (fs marking) ->
      IsDecListCons pre_places (pre_pl (lneighbours sitpn t)) ->
      NoDup pre_places ->
      exists m' : list (Place * nat),
        update_marking_pre_aux sitpn marking t pre_places = Some m'
        /\ (forall (p : Place) (n : nat), In p pre_places -> In (p, n) marking -> In (p, n - pre sitpn t p) m')
        /\ (fs marking) = (fs m').
  Proof.
    intros pre_places sitpn t;
      induction pre_places;
      intros marking Hwell_def_sitpn Hin_t_transs
             Hperm_pls His_dec Hnodup_prepl;
      simpl.

    (* BASE CASE, pre_places = [] *)
    
    - exists marking; repeat split.
      intros p n Hfalse; inversion Hfalse.

    (* INDUCTION CASE *)
    -
      (* Specializes modify_m_complete, then rewrites the goal. *)

      assert (Hin_a_fsm : In a (fs marking)).
      {
        assert (Hin_a_fn : In a (flatten_neighbours (lneighbours sitpn t))).
        {
          unfold flatten_neighbours.
          apply in_or_app; left.
          deduce_in_from_is_dec_list_cons His_dec as Hin_a_prepl.
          assumption.
        }

        specialize (in_transs_incl_flatten t Hwell_def_sitpn Hin_t_transs)
          as Hincl_fn_fl.
        specialize (Hincl_fn_fl a Hin_a_fn).
        explode_well_defined_sitpn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        specialize (Hunk_pl_neigh a Hincl_fn_fl).
        rewrite Hperm_pls in Hunk_pl_neigh; assumption.
      }

      assert (Hnodup_fsm : NoDup (fs marking)).
      {
        explode_well_defined_sitpn.
        unfold NoDupPlaces in Hnodup_places.
        rewrite Hperm_pls in Hnodup_places.
        assumption.
      }
      
      specialize (modify_m_complete marking a Nat.sub (pre sitpn t a) Hin_a_fsm Hnodup_fsm)
        as Hex_modif_m.

      (* Explodes the newly-built hypotheses, then rewrites the goal. *)
      inversion_clear Hex_modif_m as (m' & Hmodif_m_w).
      inversion_clear Hmodif_m_w as (Hmodif_m & Hdef_m').
      rewrite Hmodif_m.

      (* Then specializes IHpre_places. *)
      
      assert (Hperm_pls_m' : Permutation (places sitpn) (fs m')).
      {
        specialize (modify_m_same_struct marking a Nat.sub (pre sitpn t a) m' Hmodif_m)
          as Heq_fsm_fsm'.
        unfold fs; rewrite <- Heq_fsm_fsm'; assumption.
      }

      assert (Hnodup_prepl' : NoDup pre_places).
      {
        rewrite NoDup_cons_iff in Hnodup_prepl;
          apply proj2 in Hnodup_prepl;
          assumption.
      }
      
      specialize (@IHpre_places m' Hwell_def_sitpn Hin_t_transs Hperm_pls_m'
                                (is_dec_list_cons_cons His_dec) Hnodup_prepl')
        as Hex_up_mark_pre.

      (* Explodes the newly-built hypothesis. *)
      inversion_clear Hex_up_mark_pre as (final_marking & Hup_mark_pre_w).
      inversion_clear Hup_mark_pre_w as (Hup_mark_pre & Hw).
      inversion_clear Hw as (Hdef_fm & Heq_fsm'_fsfm).

      (* Instantiates final_marking, then solves each branch of the goal. *)
      exists final_marking.
      repeat split.

      (* Trivial case. *)
      + assumption.

      (* Case definition of final_marking. *)
      + intros p n Hin_prepl_v Hin_pn_m.

        (* Two case: a = p \/ In p pre_places. *)
        inversion_clear Hin_prepl_v as [Heq_ap | Hin_p_prepl].

        (* Case a = p *)
        -- rewrite <- Heq_ap in Hin_pn_m.
           specialize (Hdef_m' n Hin_pn_m) as Hin_ansub_m'.

           (* Specializes update_marking_pre_aux_not_in_pre_places 
              to deduce In (a, n - pre) final_marking. *)

           assert (Heq_fsm_fsm' : (fs marking) = (fs m')).
           {
             apply (modify_m_same_struct marking a Nat.sub (pre sitpn t a) m' Hmodif_m).
           }
           
           assert (Hnot_in_a_prepl : ~In a pre_places).
           {
             apply NoDup_cons_iff, proj1 in Hnodup_prepl; assumption.
           }
                  
           rewrite (update_marking_pre_aux_not_in_pre_places
                      sitpn m' t pre_places final_marking Hup_mark_pre
                      a Hnot_in_a_prepl (n - pre sitpn t a)) in Hin_ansub_m'.
           rewrite Heq_ap in Hin_ansub_m'.
           assumption.

        (* Case In p pre_places *)
        --
          (* Rewrites In (p, n) marking with modify_m_in_if_diff to
             get In (p, n) m'. *)

          assert (Hneq_ap : a <> p).
          {
            apply NoDup_cons_iff, proj1 in Hnodup_prepl.
            apply (not_in_in_diff a p pre_places (conj Hnodup_prepl Hin_p_prepl)).
          }
          
          rewrite (modify_m_in_if_diff marking a Nat.sub (pre sitpn t a) m'
                                       Hmodif_m p n Hneq_ap)
            in Hin_pn_m.

          (* Completes the goal by applying Hdef_fm. *)
          apply (Hdef_fm p n Hin_p_prepl Hin_pn_m).

      (* Case fs marking = fs final_marking *)
      +
        assert (Heq_fsm_fsm' : (fs marking) = (fs m')).
        {
          apply (modify_m_same_struct marking a Nat.sub (pre sitpn t a) m' Hmodif_m).
        }

        transitivity (fs m'); [assumption | assumption].
  Qed.
  
  (** Completeness lemma for [map_update_marking_pre]. *)

  Lemma map_update_marking_pre_complete :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (fired : list Trans)
           (marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env rising_edge ->
      Permutation (places sitpn) (fs marking) ->
      incl fired (Sitpn.fired s) ->
      NoDup fired ->
      exists transient_marking : list (Place * nat),
        map_update_marking_pre sitpn marking fired = Some transient_marking
        /\ forall (p : Place) (n : nat), In (p, n) marking ->
                                         In (p, n - pre_sum sitpn p fired) transient_marking.
  Proof.
    intros sitpn s s' time_value env;
      induction fired;
      intros marking Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Hperm_m Hincl_fired Hnodup_fired.

    (* BASE CASE, fired = [] *)
    - simpl; exists marking; split;
        [ reflexivity | intros p n Hin; rewrite <- minus_n_O; assumption ].

    (* INDUCTION CASE, a :: fired *)
    - simpl.
      unfold update_marking_pre.

      (* Specializes update_marking_pre_aux_complete *)

      assert (Hin_a_transs : In a (transs sitpn)).
      {
        specialize (Hincl_fired a (in_eq a fired)) as Hin_a_fired.
        explode_well_defined_sitpn_state Hwell_def_s.
        apply (Hincl_state_fired_transs a Hin_a_fired).
      }

      assert (Hnodup_prepl : NoDup (pre_pl (lneighbours sitpn a))).
      {
        explode_well_defined_sitpn.
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh a Hin_a_transs) as Hnodup_w.
        apply proj1 in Hnodup_w.
        apply nodup_app, proj1 in Hnodup_w.
        assumption.
      }

      specialize (update_marking_pre_aux_complete
                    (pre_pl (lneighbours sitpn a)) sitpn a marking
                    Hwell_def_sitpn Hin_a_transs Hperm_m
                    (IsDecListCons_refl (pre_pl (lneighbours sitpn a)))
                    Hnodup_prepl)
        as Hex_up_mark_pre.

      (* Explodes the newly-built hypothesis, then rewrites the goal. *)

      inversion_clear Hex_up_mark_pre as (m' & Hw).
      inversion_clear Hw as (Hup_mark_pre & H_defm'_w).
      inversion_clear H_defm'_w as (Hdef_m' & Heq_fsm_fsm').
      rewrite Hup_mark_pre.
      
      (* Then specializes IHfired. *)

      assert (Hperm_m' : Permutation (places sitpn) (fs m'))
        by (rewrite Heq_fsm_fsm' in Hperm_m; assumption).
      
      assert (Hincl_fired' : incl fired (Sitpn.fired s))
        by (apply (incl_cons_inv a fired (Sitpn.fired s) Hincl_fired)).

      assert (Hnodup_fired' : NoDup fired)
        by (apply NoDup_cons_iff, proj2 in Hnodup_fired; assumption).

      specialize (IHfired m' Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                          Hperm_m' Hincl_fired' Hnodup_fired')
        as Hex_map_up_pre.

      (* Explodes the newly-built hypothesis and instantiates
         transient_marking. *)
      
      inversion_clear Hex_map_up_pre as (transient_marking & Hw).
      inversion_clear Hw as (Hmap_up_pre & Hdef_tm).
      exists transient_marking.

      (* Splits and solves each branch of the goal. *)

      repeat split.

      (* Equality case, trivial. *)
      + trivial.

      (* Case transient_marking definition. *)
      + intros p n Hin_pn_m.

        (* Two cases, either p ∈ (pre_pl a) or p ∉ (pre_pl a) *)

        assert (Hin_prepl_v := classic (In p (pre_pl (lneighbours sitpn a)))).
        inversion_clear Hin_prepl_v as [Hin_prepl | Hnot_in_prepl].

        (* Case In p pre_pl *)
        -- specialize (Hdef_m' p n Hin_prepl Hin_pn_m) as Hin_pn_m'.
           rewrite Nat.sub_add_distr.
           apply (Hdef_tm p (n - pre sitpn a p) Hin_pn_m').

        (* Case ~In p pre_pl *)
        --
          (* If p in not is pre-places of a then there's no pre arc
             between p and a. *)

          assert (Heq_pre_0 : pre sitpn a p = 0).
          {
            explode_well_defined_sitpn.
            unfold AreWellDefinedPreEdges in Hwell_def_pre.
            specialize (Hwell_def_pre a p Hin_a_transs).
            apply proj2 in Hwell_def_pre.
            apply (Hwell_def_pre Hnot_in_prepl).
          }

          rewrite Heq_pre_0, Nat.add_0_l.

          (* Rewrites In (p, n) marking with
             update_marking_pre_aux_not_in_pre_places to get In (p, n) m'. *)

          rewrite (update_marking_pre_aux_not_in_pre_places
                     sitpn marking a (pre_pl (lneighbours sitpn a))
                     m' Hup_mark_pre p Hnot_in_prepl) in Hin_pn_m.

          (* Then completes the goal. *)

          apply (Hdef_tm p n Hin_pn_m).          
  Qed.
  
End MapUpdateMarkingPreComplete.


(** * Completeness for [map_update_marking_post]. *)

Section MapUpdateMarkingPostComplete.
  
  (** Completeness lemma for [update_marking_post_aux]. *)

  Lemma update_marking_post_aux_complete :
    forall (post_places : list Place)
           (sitpn : Sitpn)
           (t : Trans)
           (marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      Permutation (places sitpn) (fs marking) ->
      IsDecListCons post_places (post_pl (lneighbours sitpn t)) ->
      NoDup post_places ->
      exists m' : list (Place * nat),
        update_marking_post_aux sitpn marking t post_places = Some m'
        /\ (forall (p : Place) (n : nat), In p post_places -> In (p, n) marking -> In (p, n + post sitpn t p) m')
        /\ (fs marking) = (fs m').
  Proof.
    intros post_places sitpn t;
      induction post_places;
      intros marking Hwell_def_sitpn Hin_t_transs
             Hperm_pls His_dec Hnodup_postpl;
      simpl.

    (* BASE CASE, post_places = [] *)
    
    - exists marking; repeat split.
      intros p n Hfalse; inversion Hfalse.

    (* INDUCTION CASE *)
    -
      (* Specializes modify_m_complete, then rewrites the goal. *)

      assert (Hin_a_fsm : In a (fs marking)).
      {
        assert (Hin_a_fn : In a (flatten_neighbours (lneighbours sitpn t))).
        {
          unfold flatten_neighbours.
          do 3 (apply in_or_app; right).
          deduce_in_from_is_dec_list_cons His_dec as Hin_a_postpl.
          assumption.
        }

        specialize (in_transs_incl_flatten t Hwell_def_sitpn Hin_t_transs)
          as Hincl_fn_fl.
        specialize (Hincl_fn_fl a Hin_a_fn).
        explode_well_defined_sitpn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        specialize (Hunk_pl_neigh a Hincl_fn_fl).
        rewrite Hperm_pls in Hunk_pl_neigh; assumption.
      }

      assert (Hnodup_fsm : NoDup (fs marking)).
      {
        explode_well_defined_sitpn.
        unfold NoDupPlaces in Hnodup_places.
        rewrite Hperm_pls in Hnodup_places.
        assumption.
      }
      
      specialize (modify_m_complete marking a Nat.add (post sitpn t a) Hin_a_fsm Hnodup_fsm)
        as Hex_modif_m.

      (* Explodes the newly-built hypotheses, then rewrites the goal. *)
      inversion_clear Hex_modif_m as (m' & Hmodif_m_w).
      inversion_clear Hmodif_m_w as (Hmodif_m & Hdef_m').
      rewrite Hmodif_m.

      (* Then specializes IHpost_places. *)
      
      assert (Hperm_pls_m' : Permutation (places sitpn) (fs m')).
      {
        specialize (modify_m_same_struct marking a Nat.add (post sitpn t a) m' Hmodif_m)
          as Heq_fsm_fsm'.
        unfold fs; rewrite <- Heq_fsm_fsm'; assumption.
      }

      assert (Hnodup_postpl' : NoDup post_places).
      {
        rewrite NoDup_cons_iff in Hnodup_postpl;
          apply proj2 in Hnodup_postpl;
          assumption.
      }
      
      specialize (@IHpost_places m' Hwell_def_sitpn Hin_t_transs Hperm_pls_m'
                                (is_dec_list_cons_cons His_dec) Hnodup_postpl')
        as Hex_up_mark_post.

      (* Explodes the newly-built hypothesis. *)
      inversion_clear Hex_up_mark_post as (final_marking & Hup_mark_post_w).
      inversion_clear Hup_mark_post_w as (Hup_mark_post & Hw).
      inversion_clear Hw as (Hdef_fm & Heq_fsm'_fsfm).

      (* Instantiates final_marking, then solves each branch of the goal. *)
      exists final_marking.
      repeat split.

      (* Trivial case. *)
      + assumption.

      (* Case definition of final_marking. *)
      + intros p n Hin_postpl_v Hin_pn_m.

        (* Two case: a = p \/ In p post_places. *)
        inversion_clear Hin_postpl_v as [Heq_ap | Hin_p_postpl].

        (* Case a = p *)
        -- rewrite <- Heq_ap in Hin_pn_m.
           specialize (Hdef_m' n Hin_pn_m) as Hin_ansub_m'.

           (* Specializes update_marking_post_aux_not_in_post_places 
              to deduce In (a, n + post) final_marking. *)

           assert (Heq_fsm_fsm' : (fs marking) = (fs m')).
           {
             apply (modify_m_same_struct marking a Nat.add (post sitpn t a) m' Hmodif_m).
           }
           
           assert (Hnot_in_a_postpl : ~In a post_places).
           {
             apply NoDup_cons_iff, proj1 in Hnodup_postpl; assumption.
           }
                  
           rewrite (update_marking_post_aux_not_in_post_places
                      sitpn m' t post_places final_marking Hup_mark_post
                      a Hnot_in_a_postpl (n + post sitpn t a)) in Hin_ansub_m'.
           rewrite Heq_ap in Hin_ansub_m'.
           assumption.

        (* Case In p post_places *)
        --
          (* Rewrites In (p, n) marking with modify_m_in_if_diff to
             get In (p, n) m'. *)

          assert (Hneq_ap : a <> p).
          {
            apply NoDup_cons_iff, proj1 in Hnodup_postpl.
            apply (not_in_in_diff a p post_places (conj Hnodup_postpl Hin_p_postpl)).
          }
          
          rewrite (modify_m_in_if_diff marking a Nat.add (post sitpn t a) m'
                                       Hmodif_m p n Hneq_ap)
            in Hin_pn_m.

          (* Completes the goal by applying Hdef_fm. *)
          apply (Hdef_fm p n Hin_p_postpl Hin_pn_m).

      (* Case fs marking = fs final_marking *)
      +
        assert (Heq_fsm_fsm' : (fs marking) = (fs m')).
        {
          apply (modify_m_same_struct marking a Nat.add (post sitpn t a) m' Hmodif_m).
        }

        transitivity (fs m'); [assumption | assumption].
  Qed.
  
  (** Completeness lemma for [map_update_marking_post]. *)

  Lemma map_update_marking_post_complete :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (fired : list Trans)
           (marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env rising_edge ->
      Permutation (places sitpn) (fs marking) ->
      incl fired (Sitpn.fired s) ->
      NoDup fired ->
      exists transient_marking : list (Place * nat),
        map_update_marking_post sitpn marking fired = Some transient_marking
        /\ forall (p : Place) (n : nat), In (p, n) marking ->
                                         In (p, n + post_sum sitpn p fired) transient_marking.
  Proof.
    intros sitpn s s' time_value env;
      induction fired;
      intros marking Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
             Hperm_m Hincl_fired Hnodup_fired.

    (* BASE CASE, fired = [] *)
    - simpl; exists marking; split;
        [ reflexivity | intros p n Hin; rewrite <- plus_n_O; assumption ].

    (* INDUCTION CASE, a :: fired *)
    - simpl.
      unfold update_marking_post.

      (* Specializes update_marking_post_aux_complete *)

      assert (Hin_a_transs : In a (transs sitpn)).
      {
        specialize (Hincl_fired a (in_eq a fired)) as Hin_a_fired.
        explode_well_defined_sitpn_state Hwell_def_s.
        apply (Hincl_state_fired_transs a Hin_a_fired).
      }

      assert (Hnodup_postpl : NoDup (post_pl (lneighbours sitpn a))).
      {
        explode_well_defined_sitpn.
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh a Hin_a_transs) as Hnodup_w.
        apply proj2 in Hnodup_w.
        assumption.
      }

      specialize (update_marking_post_aux_complete
                    (post_pl (lneighbours sitpn a)) sitpn a marking
                    Hwell_def_sitpn Hin_a_transs Hperm_m
                    (IsDecListCons_refl (post_pl (lneighbours sitpn a)))
                    Hnodup_postpl)
        as Hex_up_mark_post.

      (* Explodes the newly-built hypothesis, then rewrites the goal. *)

      inversion_clear Hex_up_mark_post as (m' & Hw).
      inversion_clear Hw as (Hup_mark_post & H_defm'_w).
      inversion_clear H_defm'_w as (Hdef_m' & Heq_fsm_fsm').
      rewrite Hup_mark_post.
      
      (* Then specializes IHfired. *)

      assert (Hperm_m' : Permutation (places sitpn) (fs m'))
        by (rewrite Heq_fsm_fsm' in Hperm_m; assumption).
      
      assert (Hincl_fired' : incl fired (Sitpn.fired s))
        by (apply (incl_cons_inv a fired (Sitpn.fired s) Hincl_fired)).

      assert (Hnodup_fired' : NoDup fired)
        by (apply NoDup_cons_iff, proj2 in Hnodup_fired; assumption).

      specialize (IHfired m' Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
                          Hperm_m' Hincl_fired' Hnodup_fired')
        as Hex_map_up_post.

      (* Explodes the newly-built hypothesis and instantiates
         transient_marking. *)
      
      inversion_clear Hex_map_up_post as (transient_marking & Hw).
      inversion_clear Hw as (Hmap_up_post & Hdef_tm).
      exists transient_marking.

      (* Splits and solves each branch of the goal. *)

      repeat split.

      (* Equality case, trivial. *)
      + trivial.

      (* Case transient_marking definition. *)
      + intros p n Hin_pn_m.

        (* Two cases, either p ∈ (post_pl a) or p ∉ (post_pl a) *)

        assert (Hin_postpl_v := classic (In p (post_pl (lneighbours sitpn a)))).
        inversion_clear Hin_postpl_v as [Hin_postpl | Hnot_in_postpl].

        (* Case In p post_pl *)
        -- specialize (Hdef_m' p n Hin_postpl Hin_pn_m) as Hin_pn_m'.
           rewrite Nat.add_assoc.
           apply (Hdef_tm p (n + post sitpn a p) Hin_pn_m').

        (* Case ~In p post_pl *)
        --
          (* If p in not is post-places of a then there's no post arc
             between p and a. *)

          assert (Heq_post_0 : post sitpn a p = 0).
          {
            explode_well_defined_sitpn.
            unfold AreWellDefinedPostEdges in Hwell_def_post.
            specialize (Hwell_def_post a p Hin_a_transs).
            apply proj2 in Hwell_def_post.
            apply (Hwell_def_post Hnot_in_postpl).
          }

          rewrite Heq_post_0, Nat.add_0_l.

          (* Rewrites In (p, n) marking with
             update_marking_post_aux_not_in_post_places to get In (p, n) m'. *)

          rewrite (update_marking_post_aux_not_in_post_places
                     sitpn marking a (post_pl (lneighbours sitpn a))
                     m' Hup_mark_post p Hnot_in_postpl) in Hin_pn_m.

          (* Then completes the goal. *)

          apply (Hdef_tm p n Hin_pn_m).          
  Qed.
  
End MapUpdateMarkingPostComplete.

(** * Completeness of the combination of map_update_marking functions. *)

Section MapUpdateMarkingComplete.

  (** ∀ t, ∀ l, t ∈ l ∧ NoDup l ⇒ post_sum l = post t + post_sum (l - {t}) 
   *  Needed to prove post_sum_eq_iff_incl. *)

  Lemma post_sum_add_rm : 
    forall (sitpn : Sitpn)
           (p : Place)
           (l : list Trans)
           (t : Trans),
      In t l -> NoDup l -> post_sum sitpn p l = post sitpn t p + post_sum sitpn p (remove eq_nat_dec t l).
  Proof.
    intros sitpn p l;
      functional induction (post_sum sitpn p l) using post_sum_ind;
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
   *  of l', then post_sum l = post_sum l'. *)

  Lemma post_sum_eq_iff_incl :
    forall (sitpn : Sitpn)
           (p : Place)
           (l l' : list Trans),
      NoDup l ->
      NoDup l' ->
      (forall t : Trans, In t l <-> In t l') ->
      post_sum sitpn p l = post_sum sitpn p l'.
  Proof.
    intros sitpn p l;
      functional induction (post_sum sitpn p l) using post_sum_ind;
      intros l' Hnodup_l Hnodup_l' Hequiv.
    
    (* BASE CASE *)
    - functional induction (post_sum sitpn p l') using post_sum_ind.
      + reflexivity.
      + assert (Hin_eq : In t (t :: tail)) by apply in_eq.
        rewrite <- Hequiv in Hin_eq; inversion Hin_eq.
        
    (* GENERAL CASE *)
    - assert (Hin_eq : In t (t :: tail)) by apply in_eq.
      rewrite Hequiv in Hin_eq.
      specialize (post_sum_add_rm sitpn p l' t Hin_eq Hnodup_l') as Heq_postsum.
      rewrite Heq_postsum.
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
  
  (** Completeness lemma for map_update_marking functions. *)

  Lemma map_update_marking_complete :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (frd : list Trans)
           (m : list (Place * nat))
           (transient_marking : list (Place * nat))
           (final_marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      IsWellDefinedSitpnState sitpn s' ->
      SitpnSemantics sitpn s s' time_value env rising_edge ->
      (forall (p : Place) (n : nat),
          In (p, n) m ->
          In (p, n - pre_sum sitpn p frd) transient_marking) ->
      (forall (p : Place) (n : nat),
          In (p, n) transient_marking ->
          In (p, n + post_sum sitpn p frd) final_marking) ->
      Permutation (marking s) m ->
      Permutation (fired s) frd ->
      fs final_marking = fs m -> 
      NoDup final_marking ->
      Permutation final_marking (marking s').
  Proof.
    intros sitpn s s' time_value env frd m transient_marking final_marking
           Hwell_def_sitpn Hwell_def_s Hwell_def_s' Hspec
           Hdef_tm Hdef_fm Hperm_ms Hperm_fs Heq_fsfm_fsm Hnodup_fm.

    (* Strategy: apply NoDup_Permutation, then we need: 
       
       - NoDup (marking s')
       - ∀ x ∈ final_marking ⇔ x ∈ (marking s') *)

    assert (Hnodup_ms' : NoDup (marking s')).
    {
      explode_well_defined_sitpn_state Hwell_def_s'.
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      rewrite Hwf_state_marking in Hnodup_places.
      apply (nodup_fst_split (marking s') Hnodup_places).
    }

    assert (Hequiv_fm_ms' : forall x : (Place * nat), In x final_marking <-> In x (marking s')).
    {

      assert (Heq_fsm_fsm' : fst (split (marking s)) = fst (split (marking s'))).
      {
        explode_well_defined_sitpn_state Hwell_def_s.
        explode_well_defined_sitpn_state Hwell_def_s'.
        rewrite <- Hwf_state_marking, <- Hwf_state_marking0.
        reflexivity.
      }

      assert (Hnodup_fs : NoDup (fired s))
        by (explode_well_defined_sitpn_state Hwell_def_s; assumption).

      assert (Hnodup_frd : NoDup frd) by (rewrite <- Hperm_fs; assumption).

      assert (Hequiv_frd : forall t : Trans, In t frd <-> In t (fired s))
        by (intros t; rewrite Hperm_fs; reflexivity).      
      
      intros x; destruct x.

      assert (Heq_presum : pre_sum sitpn p frd = pre_sum sitpn p (fired s))
        by (apply (pre_sum_eq_iff_incl sitpn p frd (fired s) Hnodup_frd Hnodup_fs Hequiv_frd)).

      assert (Heq_postsum : post_sum sitpn p frd = post_sum sitpn p (fired s))
        by (apply (post_sum_eq_iff_incl sitpn p frd (fired s) Hnodup_frd Hnodup_fs Hequiv_frd)).

      split; intros Hin.
      
      - (* Builds In (p, x) m, then specializes Hdef_tm and Hdef_fm to
           get In (p, n - pre + post) final_marking *)
          
        specialize (in_fst_split p n final_marking Hin) as Hin_fsfm_ex.
        unfold fs in Heq_fsfm_fsm.
        rewrite Heq_fsfm_fsm in Hin_fsfm_ex.
        apply in_fst_split_in_pair in Hin_fsfm_ex.

        inversion_clear Hin_fsfm_ex as (x & Hin_m).

        (* Specializes Hdef_tm then Hdef_fm. *)

        specialize (Hdef_tm p x Hin_m) as Hin_tm.
        specialize (Hdef_fm p (x - pre_sum sitpn p frd) Hin_tm) as Hin_fm.

        (* Gets Sitpn semantics rule about definition of (marking s'), then deduces
           In (p, n - pre + post) (marking s') from it. *)

        inversion Hspec; clear H H0 H1 H2 H4 H5 H6 H7 H8 H9 H10 H11.
        rename H3 into Hdef_ms'.

        assert (Hin_ms : In (p, x) (marking s)) by (rewrite Hperm_ms; assumption).
        
        specialize (Hdef_ms' p x Hin_ms) as Hin_ms'.
        
        (* Gets (n = x - pre + post) by specializing nodup_same_pair. *)

        assert (Hnodup_fsfm : NoDup (fst (split final_marking))).
        {
          explode_well_defined_sitpn.
          explode_well_defined_sitpn_state Hwell_def_s.
          unfold NoDupPlaces in Hnodup_places.
          rewrite Hwf_state_marking in Hnodup_places.
          assert (Hnodup_fsms : NoDup (fs (marking s))) by (unfold fs; assumption).
          rewrite Hperm_ms in Hnodup_fsms.
          unfold fs in Hnodup_fsms.
          rewrite <- Heq_fsfm_fsm in Hnodup_fsms; assumption.
        }
        
        assert (Hfst_eq : fst (p, n) = fst (p, x - pre_sum sitpn p frd + post_sum sitpn p frd))
          by (simpl; reflexivity).
        
        specialize (nodup_same_pair
                      final_marking Hnodup_fsfm
                      (p, n)
                      (p, x - pre_sum sitpn p frd + post_sum sitpn p frd)
                      Hin Hin_fm Hfst_eq)
          as Heq_pair.        
        injection Heq_pair as Heq_nx.
        rewrite Heq_nx.

        (* Rewrites pre_sum frd and post_sum frd with pre_sum (fired s) 
           and post_sum (fired s) *)

        rewrite Heq_presum, Heq_postsum; assumption.

      - (* Builds In (p, x) (marking s), then specializes hyp. from Hspec to
           get In (p, n - pre + post) (marking s') *)
        
        specialize (in_fst_split p n (marking s') Hin) as Hin_fsm_ex.
        rewrite <- Heq_fsm_fsm' in Hin_fsm_ex.
        apply in_fst_split_in_pair in Hin_fsm_ex.

        inversion_clear Hin_fsm_ex as (x & Hin_ms).

        (* Gets Sitpn semantics rule about definition of (marking s'), then deduces
           In (p, n - pre + post) (marking s') from it. *)

        inversion Hspec; clear H H0 H1 H2 H4 H5 H6 H7 H8 H9 H10 H11.
        rename H3 into Hdef_ms'.
        
        specialize (Hdef_ms' p x Hin_ms) as Hin_ms'.
        
        (* Gets (n = x - pre + post) by specializing
           nodup_same_pair. *)

        assert (Hnodup_fs_ms' : NoDup (fst (split (marking s')))).
        {
          explode_well_defined_sitpn.
          explode_well_defined_sitpn_state Hwell_def_s'.
          unfold NoDupPlaces in Hnodup_places.
          rewrite Hwf_state_marking in Hnodup_places.
          assumption.
        }
        
        assert (Hfst_eq : fst (p, n) = fst (p, x - pre_sum sitpn p (fired s) + post_sum sitpn p (fired s)))
          by (simpl; reflexivity).
        
        specialize (nodup_same_pair
                      (marking s') Hnodup_fs_ms'
                      (p, n)
                      (p, x - pre_sum sitpn p (fired s) + post_sum sitpn p (fired s))
                      Hin Hin_ms' Hfst_eq)
          as Heq_pair.        
        injection Heq_pair as Heq_nx.
        rewrite Heq_nx.

        (* Specializes Hdef_tm then Hdef_fm to get
           In (p, x - pre + post) final_marking *)
        
        assert (Hin_m : In (p, x) m) by (rewrite <- Hperm_ms; assumption).
        specialize (Hdef_tm p x Hin_m) as Hin_tm.
        specialize (Hdef_fm p (x - pre_sum sitpn p frd) Hin_tm) as Hin_fm.
        
        (* Rewrites pre_sum frd and post_sum frd with 
           pre_sum (fired s) and post_sum (fired s) *)

        rewrite <- Heq_presum, <- Heq_postsum; assumption.
    }

    apply (NoDup_Permutation Hnodup_fm Hnodup_ms' Hequiv_fm_ms').    
  Qed.
  
End MapUpdateMarkingComplete.
