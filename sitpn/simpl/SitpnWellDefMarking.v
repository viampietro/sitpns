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

(** [sitpn_falling_edge] returns a SitpnState with the same marking 
    as the starting state. *)

Lemma sitpn_falling_edge_same_marking :
  forall (sitpn : Sitpn)
         (s s' : SitpnState)
         (time_value : nat)
         (env : Condition -> nat -> bool),
    sitpn_falling_edge sitpn s time_value env = Some s' ->
    (marking s) = (marking s').
Proof.
  intros sitpn s s' time_value env Hfun.
  functional induction (sitpn_falling_edge sitpn s time_value env)
             using sitpn_falling_edge_ind.

  (* GENERAL CASE, all went well. *)
  - simpl in Hfun; injection Hfun as Heq_s'; rewrite <- Heq_s'.
    simpl; reflexivity.

  (* ERROR CASE *)
  - inversion Hfun.

  (* ERROR CASE *)
  - inversion Hfun.
Qed.

(** * sitpn_rising_edge preserves marking structure. *)

Section SitpnRisingEdgeSameStructMarking.

  (** Proves that modify_m preserves the structure of the marking m
      passed as argument. *)
  
  Lemma modify_m_same_struct :
    forall (m : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (m' : list (Place * nat)),
      modify_m m p op nboftokens = Some m' ->
      fst (split m) = fst (split m').
  Proof.
    intros m p op nboftokens;
      functional induction (modify_m m p op nboftokens)
                 using modify_m_ind;
      intros fm Hfun.

    (* ERROR CASE *)
    - inversion Hfun.

    (* CASE p = hd *)
    - rewrite (beq_nat_true p' p e1);
        injection Hfun as Hfun;
        rewrite <- Hfun.
      rewrite fst_split_cons_app;
        symmetry;
        rewrite fst_split_cons_app.
      simpl; reflexivity.

    (* CASE p <> hd ∧ rec = Some m' *)
    - injection Hfun as Hfun;
        rewrite <- Hfun.
      rewrite fst_split_cons_app;
        symmetry;
        rewrite fst_split_cons_app;
        simpl;
        specialize (IHo m' e2) as Heq_fs;
        rewrite Heq_fs;
        reflexivity.

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.
  
  (** [update_marking_pre_aux] preserves marking structure. *)
  
  Lemma update_marking_pre_aux_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux sitpn m t pre_places = Some m' ->
      fst (split m) = fst (split m').
  Proof.
    intros sitpn m t pre_places;
      functional induction (update_marking_pre_aux sitpn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
      
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
      
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [update_marking_pre] preserves marking structure. *)
  
  Lemma update_marking_pre_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_pre sitpn m (lneighbours sitpn t) t = Some m' ->
      fst (split m) = fst (split m').
  Proof.
    intros sitpn m t;
      functional induction (update_marking_pre sitpn m (lneighbours sitpn t) t) using update_marking_pre_ind;
      intros m' Hfun;
      unfold update_marking_pre in Hfun;
      apply update_marking_pre_aux_same_marking in Hfun;
      assumption.
  Qed.

  (** [map_update_marking_pre] preserves marking structure. *)
  
  Lemma map_update_marking_pre_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_pre sitpn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_pre sitpn m fired) using map_update_marking_pre_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_pre_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [update_marking_post_aux] postserves marking structure. *)
  
  Lemma update_marking_post_aux_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux sitpn m t post_places = Some m' ->
       fst (split m) = fst (split m').
  Proof.
    intros sitpn m t post_places;
      functional induction (update_marking_post_aux sitpn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
      
    (* GENERAL CASE *)
    - apply modify_m_same_struct in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
      
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [update_marking_post] postserves marking structure. *)
  
  Lemma update_marking_post_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (m' : list (Place * nat)),
      update_marking_post sitpn m (lneighbours sitpn t) t = Some m' ->
      fst (split m) = fst (split m').
  Proof.
    intros sitpn m t;
      functional induction (update_marking_post sitpn m (lneighbours sitpn t) t) using update_marking_post_ind;
      intros m' Hfun;
      unfold update_marking_post in Hfun;
      apply update_marking_post_aux_same_marking in Hfun;
      assumption.
  Qed.

  (** [map_update_marking_post] postserves marking structure. *)
  
  Lemma map_update_marking_post_same_marking :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      map_update_marking_post sitpn m fired = Some m' ->
      MarkingHaveSameStruct m m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_post sitpn m fired) using map_update_marking_post_ind;
      intros fm Hfun.
    (* BASE CASE *)
    - injection Hfun as Hfun; rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply update_marking_post_same_marking in e0.
      specialize (IHo fm Hfun) as Hsame_struct.
      unfold MarkingHaveSameStruct in *.
      transitivity (fst (split m')); [assumption | assumption].
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** [sitpn_rising_edge] preserves the structure of 
      of marking at state s'. *)

  Lemma sitpn_rising_edge_same_struct_marking :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      (places sitpn) = fst (split (marking s')).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s)
                 using sitpn_rising_edge_ind;
      intros s' Hwell_def_s Hfun;

      (* GENERAL CASE *)
      (specialize (@map_update_marking_pre_same_marking
                     sitpn (marking s) (fired s) transient_marking e)
        as Heq_ms_tm;
       specialize (@map_update_marking_post_same_marking
                     sitpn transient_marking (fired s) final_marking e2)
         as Heq_tm_fm;
       
       assert (Heq_pl_fm : (places sitpn) = fst (split final_marking))
         by (explode_well_defined_sitpn_state Hwell_def_s;
             rewrite <- Heq_tm_fm, <- Heq_ms_tm;
             assumption);
       
       injection Hfun as Hfun; rewrite <- Hfun; simpl; assumption)
        
      (* ERROR CASES. *)
      || inversion Hfun.
  Qed.
  
  
End SitpnRisingEdgeSameStructMarking.
