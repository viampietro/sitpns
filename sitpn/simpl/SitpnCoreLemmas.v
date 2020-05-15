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

(* Import tertium non datur axiom. *)

Require Import Classical_Prop.

Set Implicit Arguments.

(** * Sitpn Core Lemmas. *)

(** ** Lemmas on the Sitpn structure. *)

Section SitpnLemmas.
  
  (** For all well-defined Sitpn, If a Place p ∈ neighbourhood of Trans t, then 
      p ∈ (flatten_lneighbours sitpn.(lneighbours)). *)

  Lemma in_neigh_in_flatten :
    forall (sitpn : Sitpn) (t : Trans) (p : Place),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      In p (flatten_neighbours (lneighbours sitpn t)) ->
      In p (flatten_lneighbours sitpn (transs sitpn)).
  Proof.
    intros sitpn;
      functional induction (flatten_lneighbours sitpn (transs sitpn))
                 using flatten_lneighbours_ind;
      intros t' p Hwell_def_sitpn Hin_t_transs Hin_p_flatn.

    (* BASE CASE. *)
    - inversion Hin_t_transs.

    (* GENERAL CASE *)
    - inversion_clear Hin_t_transs as [Heq_tt' | Hin_t'_tl].

      (* Case t = t' *)
      + rewrite Heq_tt'; apply in_or_app; left; assumption.

      (* Case t' ∈ tl *)
      + apply in_or_app; right.
        apply (IHl0 t' p Hwell_def_sitpn Hin_t'_tl Hin_p_flatn).
  Qed.

  (** Same as above, but more handy. *)

  Lemma in_transs_incl_flatten :
    forall (sitpn : Sitpn)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      incl (flatten_neighbours (lneighbours sitpn t)) (flatten_lneighbours sitpn (transs sitpn)).
  Proof.
    intros sitpn;
      functional induction (flatten_lneighbours sitpn (transs sitpn))
                 using flatten_lneighbours_ind;
      intros t' Hwell_def_sitpn Hin_t_transs p Hin_p_flatn.
    
    (* BASE CASE. *)
    - inversion Hin_t_transs.

    (* GENERAL CASE *)
    - inversion_clear Hin_t_transs as [Heq_tt' | Hin_t'_tl].

      (* Case t = t' *)
      + rewrite Heq_tt'; apply in_or_app; left; assumption.

      (* Case t' ∈ tl *)
      + apply in_or_app; right.
        apply (IHl0 t' Hwell_def_sitpn Hin_t'_tl p Hin_p_flatn).
  Qed.
  
End SitpnLemmas.

(** ** Lemmas on [get_value] function. *)

Section GetValueLemmas.

  Variable A B : Type.

  Lemma get_value_correct :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B))
           (value : B),
      get_value eq_dec key l = Some value ->
      In (key, value) l.
  Proof.
    intros eq_dec key l;
      functional induction (get_value eq_dec key l) using get_value_ind;
      intros v Hfun.

    (* BASE CASE. *)
    - inversion Hfun.

    (* CASE key is in head couple. *)
    - injection Hfun as Heq_v; rewrite Heq_v; apply in_eq.

    (* CASE key is not in head couple. *)
    - apply in_cons; apply IHo; assumption.
  Qed.
  
  Lemma get_value_complete :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B))
           (value : B),
      NoDup (fst (split l)) ->
      In (key, value) l ->
      get_value eq_dec key l = Some value.
  Proof.
    intros eq_dec key l;
      functional induction (get_value eq_dec key l) using get_value_ind;
      intros v Hnodup_fs_l Hin_kv_l.

    (* BASE CASE *)
    - inversion Hin_kv_l.

    (* CASE key is in head couple. *)
    - rewrite fst_split_cons_app in Hnodup_fs_l; simpl in Hnodup_fs_l.
      apply NoDup_cons_iff in Hnodup_fs_l.

      (* Two cases, (key, v) = (key, value) or (key, v) ∈ tl. *)
      inversion_clear Hin_kv_l as [Heq_kv | Hin_kv_tl].

      (* Case (key, v) = (key, value) *)
      + injection Heq_kv as Heq_v; rewrite Heq_v; reflexivity.

      (* Case (key, v) ∈ tl *)
      + apply proj1 in Hnodup_fs_l.
        apply in_fst_split in Hin_kv_tl; contradiction.

    (* CASE key not in head couple. *)
    - apply IHo.
      + rewrite fst_split_cons_app in Hnodup_fs_l; simpl in Hnodup_fs_l.
        apply NoDup_cons_iff in Hnodup_fs_l.
        apply proj2 in Hnodup_fs_l; assumption.
      + inversion_clear Hin_kv_l as [Heq_kv_xv | Hin_kv_tl].
        -- injection Heq_kv_xv as Heq_xk Heq_vv; contradiction.
        -- assumption.
  Qed.

  (** No error lemma for get_value. *)

  Lemma get_value_no_error :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B)),
      In key (fst (split l)) ->
      exists value : B, get_value eq_dec key l = Some value.
  Proof.
    intros eq_dec key l Hin_k_fsl.
    induction l.
    - simpl in Hin_k_fsl; inversion Hin_k_fsl.
    - dependent induction a; simpl; case (eq_dec a key).
      + intro; exists b; reflexivity.
      + intro Heq_false; rewrite fst_split_cons_app in Hin_k_fsl.
        simpl in Hin_k_fsl.
        inversion_clear Hin_k_fsl as [Heq_ak | Hin_k_tl].
        -- contradiction.
        -- apply (IHl Hin_k_tl).
  Qed.
  
End GetValueLemmas.

(** ** Lemmas on map_check functions. *)

Section MapCheckFunctions.

  (*! Map Check Pre functions. !*)
  
  (** Correctness proof for [check_pre]. *)

  Lemma check_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fst (split marking)) ->
      In (p, n) marking ->
      check_pre sitpn marking p t = Some true ->
      (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_pre sitpn marking p t) using check_pre_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (pre sitpn t p) n Hfun).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma check_pre_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In (p, n) marking ->
      check_pre sitpn marking p t = Some true ->
      (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_pre sitpn marking p t) using check_pre_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (pre sitpn t p) n Hfun).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for [check_pre]. *)

  Lemma check_pre_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In (p, n) marking ->
      (pre sitpn t p) <= n ->
      check_pre sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_pre.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
  Qed.

  Lemma check_pre_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In (p, n) marking ->
      (pre sitpn t p) <= n ->
      check_pre sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_pre.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
  Qed.

  (* No error lemma for check_pre. *)

  Lemma check_pre_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_pre sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_pre.
    specialize (get_value_no_error Nat.eq_dec p marking Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (pre sitpn t p <=? nboftokens).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, pre_places, t, b,
      map_check_pre_aux sitpn marking pre_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_pre_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_pre_aux sitpn marking pre_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking pre_places t b;
      functional induction (map_check_pre_aux sitpn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      map_check_pre_aux sitpn marking pre_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking pre_places t b;
      functional induction (map_check_pre_aux sitpn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
             Hfun p' n Hin_pre_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_pre_pl.

    (* INDUCTION CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_pre_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_pre_correct
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_pre_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma map_check_pre_aux_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      map_check_pre_aux sitpn marking pre_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking pre_places t b;
      functional induction (map_check_pre_aux sitpn marking pre_places t b)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
             Hfun p' n Hin_pre_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_pre_pl.

    (* INDUCTION CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_pre_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_pre_correct_perm
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_pre_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_pre_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_pre_aux. *)

  Lemma map_check_pre_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      (places sitpn) = fst (split marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre_aux sitpn marking pre_places t true = Some true.
  Proof.
    intros sitpn marking pre_places t;
      functional induction (map_check_pre_aux sitpn marking pre_places t true)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_pre_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_pre_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                    Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds pre sitpn t p <= x *)
      specialize (Hspec p x Hin_pre_pl Hin_m') as Hpre_le.
      
      (* Applies check_pre_complete, then the induction hypothesis. *)
      specialize (check_pre_complete marking p t
                    Hwell_def_sitpn Heq_pls_fsm Hin_m' Hpre_le) as Hcheck_pre.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_pre in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_pre_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> pre sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_pre_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_pre_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_pre_no_error. *)
      specialize (check_pre_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_pre_noerr.
      inversion_clear Hcheck_pre_noerr as (b & Hcheck_pre_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_pre_some; inversion Hcheck_pre_some.
  Qed.

  Lemma map_check_pre_aux_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      Permutation (places sitpn) (fs marking) ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p pre_places -> In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre_aux sitpn marking pre_places t true = Some true.
  Proof.
    intros sitpn marking pre_places t;
      functional induction (map_check_pre_aux sitpn marking pre_places t true)
                 using map_check_pre_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_pre_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_pre_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                                      Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds pre sitpn t p <= x *)
      specialize (Hspec p x Hin_pre_pl Hin_m') as Hpre_le.
      
      (* Applies check_pre_complete, then the induction hypothesis. *)
      specialize (check_pre_complete_perm marking p t
                                     Hwell_def_sitpn Heq_pls_fsm Hin_m' Hpre_le) as Hcheck_pre.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_pre in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_pre_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> pre sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_pre_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_pre_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_pre_pl p Hin_pre_pl) as Hin_pre_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours; apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_pre_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_pre_no_error. *)
      specialize (check_pre_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_pre_noerr.
      inversion_clear Hcheck_pre_noerr as (b & Hcheck_pre_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_pre_some; inversion Hcheck_pre_some.
  Qed.
  
  (** No error lemma for map_check_pre_aux. *)

  Lemma map_check_pre_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (check_result : bool),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre_aux sitpn marking pre_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction pre_places; intros check_result Hincl_prepl.

    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: pre_places)) by apply in_eq.
      apply (Hincl_prepl a) in Hin_a_fs.
      specialize (check_pre_no_error sitpn marking a t Hin_a_fs) as Hcheck_pre_ex.
      inversion_clear Hcheck_pre_ex as (b & Hcheck_pre).
      rewrite Hcheck_pre.
      apply incl_cons_inv in Hincl_prepl.
      apply (IHpre_places (b && check_result) Hincl_prepl).
  Qed.
  
  (** Correctness proof for map_check_pre. *)

  Lemma map_check_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t)
                 using map_check_pre_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (pre_pl (lneighbours sitpn t)) (pre_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_pre_pl := classic (In p (pre_pl (lneighbours sitpn t)))).
    inversion Hvee_in_pre_pl as [Hin_pre_pl | Hnotin_pre_pl]; clear Hvee_in_pre_pl.
    
    (* First stage, p ∈ pre_places, then we apply map_check_pre_aux_correct. *)
    - apply (map_check_pre_aux_correct
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_pre_pl Hin_m).
      
    (* Second stage, p ∉ pre_places, then (pre sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedPreEdges in Hwell_def_pre.
      specialize (Hwell_def_pre t p Hin_t_transs) as Hw_pre.
      apply proj2 in Hw_pre.
      specialize (Hw_pre Hnotin_pre_pl) as Hw_pre; rewrite Hw_pre; apply Peano.le_0_n.
  Qed.

  Lemma map_check_pre_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) ->
      map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t)
                 using map_check_pre_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (pre_pl (lneighbours sitpn t)) (pre_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_pre_pl := classic (In p (pre_pl (lneighbours sitpn t)))).
    inversion Hvee_in_pre_pl as [Hin_pre_pl | Hnotin_pre_pl]; clear Hvee_in_pre_pl.
    
    (* First stage, p ∈ pre_places, then we apply map_check_pre_aux_correct. *)
    - apply (map_check_pre_aux_correct_perm
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_pre_pl Hin_m).
      
    (* Second stage, p ∉ pre_places, then (pre sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedPreEdges in Hwell_def_pre.
      specialize (Hwell_def_pre t p Hin_t_transs) as Hw_pre.
      apply proj2 in Hw_pre.
      specialize (Hw_pre Hnotin_pre_pl) as Hw_pre; rewrite Hw_pre; apply Peano.le_0_n.
  Qed.
  
  (** Completeness proof for map_check_pre. *)

  Lemma map_check_pre_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t)
                 using map_check_pre_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t) 
       for map_check_pre_aux_complete. *)
    assert (Hincl_refl: incl (pre_pl (lneighbours sitpn t)) (pre_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ pre_places -> (p, n) ∈ marking -> pre sitpn t p <= n 
       to apply map_check_pre_aux_complete. *)
    assert (Hspec_check_pre :
              forall (p : Place) (n : nat),
                In p (pre_pl (lneighbours sitpn t)) -> In (p, n) marking -> pre sitpn t p <= n) 
      by (intros p n Hin_pre_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_pre_aux_complete. *)
    apply (map_check_pre_aux_complete
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_pre).    
  Qed.

  Lemma map_check_pre_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (pre sitpn t p) <= n) ->
      map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_pre sitpn marking (pre_pl (lneighbours sitpn t)) t)
                 using map_check_pre_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (pre_pl neighbours_of_t) (pre_pl neighbours_of_t) 
       for map_check_pre_aux_complete. *)
    assert (Hincl_refl: incl (pre_pl (lneighbours sitpn t)) (pre_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ pre_places -> (p, n) ∈ marking -> pre sitpn t p <= n 
       to apply map_check_pre_aux_complete. *)
    assert (Hspec_check_pre :
              forall (p : Place) (n : nat),
                In p (pre_pl (lneighbours sitpn t)) -> In (p, n) marking -> pre sitpn t p <= n) 
      by (intros p n Hin_pre_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_pre_aux_complete. *)
    apply (map_check_pre_aux_complete_perm
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_pre).    
  Qed.
  
  (** No error lemma for map_check_pre. *)

  Lemma map_check_pre_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place),
      incl pre_places (fst (split marking)) ->
      exists b : bool,
        map_check_pre sitpn marking pre_places t = Some b.
  Proof.
    intros sitpn marking t pre_places Hincl_prepl.
    unfold map_check_pre.
    apply (map_check_pre_aux_no_error sitpn marking t true Hincl_prepl).
  Qed.

  (*! Map Check Test functions. !*)
  
  (** Correctness proof for [check_test]. *)

  Lemma check_test_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fst (split marking)) ->
      In (p, n) marking ->
      check_test sitpn marking p t = Some true ->
      (test sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_test sitpn marking p t) using check_test_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (test sitpn t p) n Hfun).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma check_test_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In (p, n) marking ->
      check_test sitpn marking p t = Some true ->
      (test sitpn t p) <= n.
  Proof.
    intros sitpn marking p t;
      functional induction (check_test sitpn marking p t) using check_test_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply (leb_complete (test sitpn t p) n Hfun).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for [check_test]. *)

  Lemma check_test_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In (p, n) marking ->
      (test sitpn t p) <= n ->
      check_test sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_test.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
  Qed.

  Lemma check_test_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In (p, n) marking ->
      (test sitpn t p) <= n ->
      check_test sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_test.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m.
    apply leb_correct in Hspec; rewrite Hspec; reflexivity.
  Qed.

  (* No error lemma for check_test. *)

  Lemma check_test_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_test sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_test.
    specialize (get_value_no_error Nat.eq_dec p marking Hin_fs) as Hget_m_ex.
    inversion_clear Hget_m_ex as (nboftokens & Hget_m).
    rewrite Hget_m; exists (test sitpn t p <=? nboftokens).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, test_places, t, b,
      map_check_test_aux sitpn marking test_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_test_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_test_aux sitpn marking test_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking test_places t b;
      functional induction (map_check_test_aux sitpn marking test_places t b)
                 using map_check_test_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl test_places (test_pl (lneighbours sitpn t)) ->
      map_check_test_aux sitpn marking test_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p test_places -> In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking test_places t b;
      functional induction (map_check_test_aux sitpn marking test_places t b)
                 using map_check_test_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_test_pl
             Hfun p' n Hin_test_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_test_pl.

    (* INDUCTION CASE *)
    - inversion Hin_test_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_test_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_test_correct
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_test_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_test_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma map_check_test_aux_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      incl test_places (test_pl (lneighbours sitpn t)) ->
      map_check_test_aux sitpn marking test_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p test_places -> In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking test_places t b;
      functional induction (map_check_test_aux sitpn marking test_places t b)
                 using map_check_test_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_test_pl
             Hfun p' n Hin_test_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_test_pl.

    (* INDUCTION CASE *)
    - inversion Hin_test_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_test_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_test_correct_perm
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_test_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_test_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_test_aux. *)

  Lemma map_check_test_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      (places sitpn) = fst (split marking) ->
      incl test_places (test_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p test_places -> In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test_aux sitpn marking test_places t true = Some true.
  Proof.
    intros sitpn marking test_places t;
      functional induction (map_check_test_aux sitpn marking test_places t true)
                 using map_check_test_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_test_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_test_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                    Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds test sitpn t p <= x *)
      specialize (Hspec p x Hin_test_pl Hin_m') as Htest_le.
      
      (* Applies check_test_complete, then the induction hypothesis. *)
      specialize (check_test_complete marking p t
                    Hwell_def_sitpn Heq_pls_fsm Hin_m' Htest_le) as Hcheck_test.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_test in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_test_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> test sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_test_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_test_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_test_no_error. *)
      specialize (check_test_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_test_noerr.
      inversion_clear Hcheck_test_noerr as (b & Hcheck_test_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_test_some; inversion Hcheck_test_some.
  Qed.

  Lemma map_check_test_aux_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      Permutation (places sitpn) (fs marking) ->
      incl test_places (test_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p test_places -> In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test_aux sitpn marking test_places t true = Some true.
  Proof.
    intros sitpn marking test_places t;
      functional induction (map_check_test_aux sitpn marking test_places t true)
                 using map_check_test_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_test_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_test_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                    Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds test sitpn t p <= x *)
      specialize (Hspec p x Hin_test_pl Hin_m') as Htest_le.
      
      (* Applies check_test_complete, then the induction hypothesis. *)
      specialize (check_test_complete_perm marking p t
                    Hwell_def_sitpn Heq_pls_fsm Hin_m' Htest_le) as Hcheck_test.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_test in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_test_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail -> In (p, n) marking -> test sitpn t p <= n)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_test_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_test_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_test_pl p Hin_test_pl) as Hin_test_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            apply in_or_app; right;
            apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_test_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_test_no_error. *)
      specialize (check_test_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_test_noerr.
      inversion_clear Hcheck_test_noerr as (b & Hcheck_test_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_test_some; inversion Hcheck_test_some.
  Qed.

  (** No error lemma for map_check_test_aux. *)

  Lemma map_check_test_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place)
           (check_result : bool),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test_aux sitpn marking test_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction test_places; intros check_result Hincl_testpl.

    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: test_places)) by apply in_eq.
      apply (Hincl_testpl a) in Hin_a_fs.
      specialize (check_test_no_error sitpn marking a t Hin_a_fs) as Hcheck_test_ex.
      inversion_clear Hcheck_test_ex as (b & Hcheck_test).
      rewrite Hcheck_test.
      apply incl_cons_inv in Hincl_testpl.
      apply (IHtest_places (b && check_result) Hincl_testpl).
  Qed.
  
  (** Correctness proof for map_check_test. *)

  Lemma map_check_test_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fs marking) ->
      In t (transs sitpn) ->
      map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t)
                 using map_check_test_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (test_pl (lneighbours sitpn t)) (test_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_test_pl := classic (In p (test_pl (lneighbours sitpn t)))).
    inversion Hvee_in_test_pl as [Hin_test_pl | Hnotin_test_pl]; clear Hvee_in_test_pl.
    
    (* First stage, p ∈ test_places, then we apply map_check_test_aux_correct. *)
    - apply (map_check_test_aux_correct
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_test_pl Hin_m).
      
    (* Second stage, p ∉ test_places, then (test sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedTestEdges in Hwell_def_test.
      specialize (Hwell_def_test t p Hin_t_transs) as Hw_test.
      apply proj2 in Hw_test.
      specialize (Hw_test Hnotin_test_pl) as Hw_test; rewrite Hw_test; apply Peano.le_0_n.
  Qed.
  
  Lemma map_check_test_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) ->
      map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t)
                 using map_check_test_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (test_pl (lneighbours sitpn t)) (test_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_test_pl := classic (In p (test_pl (lneighbours sitpn t)))).
    inversion Hvee_in_test_pl as [Hin_test_pl | Hnotin_test_pl]; clear Hvee_in_test_pl.
    
    (* First stage, p ∈ test_places, then we apply map_check_test_aux_correct. *)
    - apply (map_check_test_aux_correct_perm
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_test_pl Hin_m).
      
    (* Second stage, p ∉ test_places, then (test sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedTestEdges in Hwell_def_test.
      specialize (Hwell_def_test t p Hin_t_transs) as Hw_test.
      apply proj2 in Hw_test.
      specialize (Hw_test Hnotin_test_pl) as Hw_test; rewrite Hw_test; apply Peano.le_0_n.
  Qed.
  
  (** Completeness proof for map_check_test. *)

  Lemma map_check_test_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t)
                 using map_check_test_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (test_pl neighbours_of_t) (test_pl neighbours_of_t) 
       for map_check_test_aux_complete. *)
    assert (Hincl_refl: incl (test_pl (lneighbours sitpn t)) (test_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ test_places -> (p, n) ∈ marking -> test sitpn t p <= n 
       to apply map_check_test_aux_complete. *)
    assert (Hspec_check_test :
              forall (p : Place) (n : nat),
                In p (test_pl (lneighbours sitpn t)) -> In (p, n) marking -> test sitpn t p <= n) 
      by (intros p n Hin_test_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_test_aux_complete. *)
    apply (map_check_test_aux_complete
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_test).    
  Qed.

  Lemma map_check_test_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat), In (p, n) marking -> (test sitpn t p) <= n) ->
      map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_test sitpn marking (test_pl (lneighbours sitpn t)) t)
                 using map_check_test_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (test_pl neighbours_of_t) (test_pl neighbours_of_t) 
       for map_check_test_aux_complete. *)
    assert (Hincl_refl: incl (test_pl (lneighbours sitpn t)) (test_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ test_places -> (p, n) ∈ marking -> test sitpn t p <= n 
       to apply map_check_test_aux_complete. *)
    assert (Hspec_check_test :
              forall (p : Place) (n : nat),
                In p (test_pl (lneighbours sitpn t)) -> In (p, n) marking -> test sitpn t p <= n) 
      by (intros p n Hin_test_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_test_aux_complete. *)
    apply (map_check_test_aux_complete_perm
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_test).    
  Qed.

  (** No error lemma for map_check_test. *)

  Lemma map_check_test_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (test_places : list Place),
      incl test_places (fst (split marking)) ->
      exists b : bool,
        map_check_test sitpn marking test_places t = Some b.
  Proof.
    intros sitpn marking t test_places Hincl_testpl.
    unfold map_check_test.
    apply (map_check_test_aux_no_error sitpn marking t true Hincl_testpl).
  Qed.

  (*! Map Check Inhib functions. !*)
  
  (** Correctness proof for [check_inhib]. *)

  Lemma check_inhib_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In (p, n) marking ->
      check_inhib sitpn marking p t = Some true ->
      (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking p t;
      functional induction (check_inhib sitpn marking p t) using check_inhib_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply orb_prop in Hfun.
      
      (* First case: n < (inhib spn t p), second case: (inhib spn t p) = 0 *)
      inversion Hfun as [Hinhib_lt | Hinhib_eq_0].
      + left; apply Nat.ltb_lt; assumption.
      + right; apply Nat.eqb_eq; assumption.
      
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma check_inhib_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fst (split marking)) ->
      In (p, n) marking ->
      check_inhib sitpn marking p t = Some true ->
      (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking p t;
      functional induction (check_inhib sitpn marking p t) using check_inhib_ind;
      intros n Hwel_def_sitpn Heq_pls_fsm Hin_m Hfun.
    
    (* GENERAL CASE, all went well. *)
    - apply get_value_correct in e.
      
      (* Proves that ∀ (p, n), (p, nboftokens) ∈ marking ⇒ n = nboftokens. *)
      explode_well_defined_sitpn.
      unfold NoDupPlaces in Hnodup_places.
      assert (Hnodup_fs_m := Hnodup_places).
      rewrite Heq_pls_fsm in Hnodup_fs_m.
      assert (Heq_pp : fst (p, n) = fst (p, nboftokens)) by (simpl; reflexivity).

      specialize (nodup_same_pair
                    marking Hnodup_fs_m (p, n) (p, nboftokens)
                    Hin_m e Heq_pp) as Heq_nnb.
      injection Heq_nnb as Heq_nnb.
      rewrite <- Heq_nnb in Hfun; injection Hfun as Hfun.
      apply orb_prop in Hfun.
      
      (* First case: n < (inhib spn t p), second case: (inhib spn t p) = 0 *)
      inversion Hfun as [Hinhib_lt | Hinhib_eq_0].
      + left; apply Nat.ltb_lt; assumption.
      + right; apply Nat.eqb_eq; assumption.
        
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for [check_inhib]. *)

  Lemma check_inhib_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In (p, n) marking ->
      (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0 ->
      check_inhib sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_inhib.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m; inversion Hspec as [Hinhib_lt | Hinhib_eq_0].
    - apply Nat.ltb_lt in Hinhib_lt; rewrite Hinhib_lt.
      rewrite orb_true_l; reflexivity.
    - apply Nat.eqb_eq in Hinhib_eq_0; rewrite Hinhib_eq_0.
      rewrite orb_comm; rewrite orb_true_l; reflexivity.
  Qed.

  Lemma check_inhib_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans)
           (n : nat),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In (p, n) marking ->
      (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0 ->
      check_inhib sitpn marking p t = Some true.
  Proof.
    intros sitpn marking p t n Hwell_def_sitpn Heq_pls_fsm Hin_m Hspec.
    unfold check_inhib.
    
    (* Builds the condition NoDup (fst (split marking)). 
       Necessary to apply get_value_complete. *)
    explode_well_defined_sitpn.
    unfold NoDupPlaces in Hnodup_places.
    assert (Hnodup_fs_m := Hnodup_places).
    rewrite Heq_pls_fsm in Hnodup_fs_m.

    (* Specializes get_value_complete. *)
    specialize (get_value_complete Nat.eq_dec p marking n Hnodup_fs_m Hin_m) as Hget_m.
    rewrite Hget_m; inversion Hspec as [Hinhib_lt | Hinhib_eq_0].
    - apply Nat.ltb_lt in Hinhib_lt; rewrite Hinhib_lt.
      rewrite orb_true_l; reflexivity.
    - apply Nat.eqb_eq in Hinhib_eq_0; rewrite Hinhib_eq_0.
      rewrite orb_comm; rewrite orb_true_l; reflexivity.
  Qed.

  (* No error lemma for check_inhib. *)

  Lemma check_inhib_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (p : Place)
           (t : Trans),
      In p (fst (split marking)) ->
      exists b : bool,
        check_inhib sitpn marking p t = Some b.
  Proof.
    intros sitpn marking p t Hin_fs.
    unfold check_inhib.
    specialize (get_value_no_error Nat.eq_dec p marking Hin_fs) as Hget_v_ex.
    inversion_clear Hget_v_ex as (nboftokens & Hget_v).
    rewrite Hget_v; exists ((nboftokens <? inhib sitpn t p) || (inhib sitpn t p =? 0)).
    reflexivity.
  Qed.
  
  (** ∀ sitpn, marking, inhib_places, t, b,
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ⇒
      b = true.
   *)
  Lemma map_check_inhib_aux_true_if_true :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (b : bool),
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ->
      b = true.
  Proof.
    intros sitpn marking inhib_places t b;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros.
    - injection H; auto.
    - apply IHo in H; apply andb_prop in H; elim H; auto.
    - inversion H.
  Qed.

  (** Correctness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      incl inhib_places (inhib_pl (lneighbours sitpn t)) ->
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p inhib_places ->
        In (p, n) marking ->
        (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking inhib_places t b;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_inhib_pl
             Hfun p' n Hin_inhib_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_inhib_pl.

    (* INDUCTION CASE *)
    - inversion Hin_inhib_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_inhib_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_inhib_correct
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_inhib_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_inhib_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  Lemma map_check_inhib_aux_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (b : bool),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      incl inhib_places (inhib_pl (lneighbours sitpn t)) ->
      map_check_inhib_aux sitpn marking inhib_places t b = Some true ->
      forall (p : Place) (n : nat),
        In p inhib_places ->
        In (p, n) marking ->
        (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking inhib_places t b;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t b)
                 using map_check_inhib_aux_ind;
      intros Hwell_def_sitpn Heq_pls_fsm Hincl_inhib_pl
             Hfun p' n Hin_inhib_pl Hin_m.
    
    (* BASE CASE *)
    - inversion Hin_inhib_pl.

    (* INDUCTION CASE *)
    - inversion Hin_inhib_pl as [Heq_pp' | Hin_p'_tail].
      + apply map_check_inhib_aux_true_if_true in Hfun.
        apply andb_prop in Hfun; apply proj1 in Hfun.
        rewrite Heq_pp' in e0; rewrite Hfun in e0.
        apply (check_inhib_correct_perm
                 marking p' t n
                 Hwell_def_sitpn Heq_pls_fsm Hin_m e0).
      + apply incl_cons_inv in Hincl_inhib_pl.
        apply (IHo Hwell_def_sitpn Heq_pls_fsm Hincl_inhib_pl
                   Hfun p' n Hin_p'_tail Hin_m).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Completeness proof for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      (places sitpn) = fst (split marking) ->
      incl inhib_places (inhib_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p inhib_places ->
          In (p, n) marking ->
          (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0) ->
      map_check_inhib_aux sitpn marking inhib_places t true = Some true.
  Proof.
    intros sitpn marking inhib_places t;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t true)
                 using map_check_inhib_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_inhib_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_inhib_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                    Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds inhib sitpn t p <= x *)
      specialize (Hspec p x Hin_inhib_pl Hin_m') as Hinhib_le.
      
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      specialize (check_inhib_complete marking p t
                    Hwell_def_sitpn Heq_pls_fsm Hin_m' Hinhib_le) as Hcheck_inhib.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_inhib in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_inhib_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail ->
                 In (p, n) marking ->
                 inhib sitpn t p > n \/ inhib sitpn t p = 0)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_inhib_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_inhib_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_inhib_no_error. *)
      specialize (check_inhib_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_inhib_noerr.
      inversion_clear Hcheck_inhib_noerr as (b & Hcheck_inhib_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_inhib_some; inversion Hcheck_inhib_some.
  Qed.

  Lemma map_check_inhib_aux_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      In t (transs sitpn) ->
      Permutation (places sitpn) (fs marking) ->
      incl inhib_places (inhib_pl (lneighbours sitpn t)) ->
      (forall (p : Place) (n : nat),
          In p inhib_places ->
          In (p, n) marking ->
          (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0) ->
      map_check_inhib_aux sitpn marking inhib_places t true = Some true.
  Proof.
    intros sitpn marking inhib_places t;
      functional induction (map_check_inhib_aux sitpn marking inhib_places t true)
                 using map_check_inhib_aux_ind;
      intros Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_inhib_pl Hspec.

    (* BASE CASE *)
    - reflexivity.

    (* GENERAL CASE *)
    - (* Strategy: build ∃ x, (p, x) ∈ marking to apply check_inhib_complete. *)

      (* Builds p ∈ (flatten_neighbours (lneighbours sitpn t)) 
         to specialize in_neigh_in_flatten. *)
      assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).

      (* Specializes in_neigh_in_flatten. *)
      specialize (in_neigh_in_flatten t p
                                      Hwell_def_sitpn Hin_t_transs Hin_flat) as Hin_flat_lneigh.

      (* Builds (p, x) ∈ marking *)
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      apply (Hunk_pl_neigh p) in Hin_flat_lneigh.
      rewrite Heq_pls_fsm in Hin_flat_lneigh.
      specialize (in_fst_split_in_pair p marking Hin_flat_lneigh) as Hin_m.
      inversion Hin_m as (x & Hin_m').

      (* Builds inhib sitpn t p <= x *)
      specialize (Hspec p x Hin_inhib_pl Hin_m') as Hinhib_le.
      
      (* Applies check_inhib_complete, then the induction hypothesis. *)
      specialize (check_inhib_complete_perm
                    marking p t Hwell_def_sitpn Heq_pls_fsm Hin_m' Hinhib_le) as Hcheck_inhib.
      
      (* Use b = true to rewrite the goal and apply the induction hypothesis. *)
      rewrite Hcheck_inhib in e0; injection e0 as Heq_btrue.
      rewrite <- Heq_btrue in IHo; rewrite andb_comm in IHo; rewrite andb_true_r in IHo.
      rewrite <- Heq_btrue; rewrite andb_comm; rewrite andb_true_r.
      
      (* Builds hypotheses and then applies IHo. *)
      apply incl_cons_inv in Hincl_inhib_pl.
      assert (Hspec' : forall (p : Place) (n : nat),
                 In p tail ->
                 In (p, n) marking ->
                 inhib sitpn t p > n \/ inhib sitpn t p = 0)
        by (intros p0 n Hin_tail;
            apply in_cons with (a := p) in Hin_tail;
            apply (Hspec p0 n Hin_tail)).
      apply (IHo Hwell_def_sitpn Hin_t_transs Heq_pls_fsm Hincl_inhib_pl Hspec').
      
    (* ERROR CASE, then contradiction. *)
    - assert (Hin_inhib_pl : In p (p :: tail)) by apply in_eq.
      specialize (Hincl_inhib_pl p Hin_inhib_pl) as Hin_inhib_pl_t.
      assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
        by (unfold flatten_neighbours;
            do 2 (apply in_or_app; right);
            apply in_or_app; left; assumption).

      (* Builds p ∈ fst (split marking) to specialize check_inhib_no_error. *)
      specialize (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_flat)
        as Hin_flat_lneigh.      
      explode_well_defined_sitpn.
      unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
      unfold incl in Hunk_pl_neigh.
      specialize (Hunk_pl_neigh p Hin_flat_lneigh) as Hin_p_fsm.
      rewrite Heq_pls_fsm in Hin_p_fsm.
      
      (* Applies check_inhib_no_error. *)
      specialize (check_inhib_no_error sitpn marking p t Hin_p_fsm)
        as Hcheck_inhib_noerr.
      inversion_clear Hcheck_inhib_noerr as (b & Hcheck_inhib_some).

      (* Then, shows a contradiction. *)
      rewrite e0 in Hcheck_inhib_some; inversion Hcheck_inhib_some.
  Qed.

  (** No error lemma for map_check_inhib_aux. *)

  Lemma map_check_inhib_aux_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place)
           (check_result : bool),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib_aux sitpn marking inhib_places t check_result = Some b.
  Proof.
    intros sitpn marking t; induction inhib_places; intros check_result Hincl_inhibpl.

    (* BASE CASE *)
    - simpl; exists check_result; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_a_fs: In a (a :: inhib_places)) by apply in_eq.
      apply (Hincl_inhibpl a) in Hin_a_fs.
      specialize (check_inhib_no_error sitpn marking a t Hin_a_fs) as Hcheck_inhib_ex.
      inversion_clear Hcheck_inhib_ex as (b & Hcheck_inhib).
      rewrite Hcheck_inhib.
      apply incl_cons_inv in Hincl_inhibpl.
      apply (IHinhib_places (b && check_result) Hincl_inhibpl).
  Qed.
  
  (** Correctness proof for map_check_inhib. *)

  Lemma map_check_inhib_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t)
                 using map_check_inhib_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (inhib_pl (lneighbours sitpn t)) (inhib_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_inhib_pl := classic (In p (inhib_pl (lneighbours sitpn t)))).
    inversion Hvee_in_inhib_pl as [Hin_inhib_pl | Hnotin_inhib_pl]; clear Hvee_in_inhib_pl.
    
    (* First stage, p ∈ inhib_places, then we apply map_check_inhib_aux_correct. *)
    - apply (map_check_inhib_aux_correct
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_inhib_pl Hin_m).
      
    (* Second stage, p ∉ inhib_places, then (inhib sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedInhibEdges in Hwell_def_inhib.
      specialize (Hwell_def_inhib t p Hin_t_transs) as Hw_inhib.
      apply proj2 in Hw_inhib.
      specialize (Hw_inhib Hnotin_inhib_pl) as Hw_inhib;
        rewrite Hw_inhib; right; reflexivity.
  Qed.

  Lemma map_check_inhib_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) ->
      map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t = Some true ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t)
                 using map_check_inhib_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun p n Hin_m.

    assert (Hincl_refl : incl (inhib_pl (lneighbours sitpn t)) (inhib_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Proof in two stages. *)
    assert (Hvee_in_inhib_pl := classic (In p (inhib_pl (lneighbours sitpn t)))).
    inversion Hvee_in_inhib_pl as [Hin_inhib_pl | Hnotin_inhib_pl]; clear Hvee_in_inhib_pl.
    
    (* First stage, p ∈ inhib_places, then we apply map_check_inhib_aux_correct. *)
    - apply (map_check_inhib_aux_correct_perm
               marking t true Hwell_def_sitpn Heq_pl_fsm
               Hincl_refl Hfun p n Hin_inhib_pl Hin_m).
      
    (* Second stage, p ∉ inhib_places, then (inhib sitpn t p) = 0 *)
    - explode_well_defined_sitpn.
      unfold AreWellDefinedInhibEdges in Hwell_def_inhib.
      specialize (Hwell_def_inhib t p Hin_t_transs) as Hw_inhib.
      apply proj2 in Hw_inhib.
      specialize (Hw_inhib Hnotin_inhib_pl) as Hw_inhib;
        rewrite Hw_inhib; right; reflexivity.
  Qed.
  
  (** Completeness proof for map_check_inhib. *)

  Lemma map_check_inhib_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) =  fst (split marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat),
          In (p, n) marking -> (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0) ->
      map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t)
                 using map_check_inhib_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (inhib_pl neighbours_of_t) (inhib_pl neighbours_of_t) 
       for map_check_inhib_aux_complete. *)
    assert (Hincl_refl: incl (inhib_pl (lneighbours sitpn t)) (inhib_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ inhib_places -> (p, n) ∈ marking -> inhib sitpn t p <= n 
       to apply map_check_inhib_aux_complete. *)
    assert (Hspec_check_inhib :
              forall (p : Place) (n : nat),
                In p (inhib_pl (lneighbours sitpn t)) ->
                In (p, n) marking ->
                inhib sitpn t p > n \/ inhib sitpn t p = 0) 
      by (intros p n Hin_inhib_pl Hin_m; apply (Hspec p n Hin_m)).
      
    (* Apply map_check_inhib_aux_complete. *)
    apply (map_check_inhib_aux_complete
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_inhib).    
  Qed.

  Lemma map_check_inhib_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) ->
      (forall (p : Place) (n : nat),
          In (p, n) marking -> (inhib sitpn t p) > n \/ (inhib sitpn t p) = 0) ->
      map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (map_check_inhib sitpn marking (inhib_pl (lneighbours sitpn t)) t)
                 using map_check_inhib_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hspec.
    
    (* Hypothesis : incl (inhib_pl neighbours_of_t) (inhib_pl neighbours_of_t) 
       for map_check_inhib_aux_complete. *)
    assert (Hincl_refl: incl (inhib_pl (lneighbours sitpn t)) (inhib_pl (lneighbours sitpn t)))
      by apply incl_refl.

    (* Builds ∀ p,n, p ∈ inhib_places -> (p, n) ∈ marking -> inhib sitpn t p <= n 
       to apply map_check_inhib_aux_complete. *)
    assert (Hspec_check_inhib :
              forall (p : Place) (n : nat),
                In p (inhib_pl (lneighbours sitpn t)) ->
                In (p, n) marking ->
                inhib sitpn t p > n \/ inhib sitpn t p = 0) 
      by (intros p n Hin_inhib_pl Hin_m; apply (Hspec p n Hin_m)).
    
    (* Apply map_check_inhib_aux_complete. *)
    apply (map_check_inhib_aux_complete_perm
             marking t Hwell_def_sitpn Hin_t_transs
             Heq_pl_fsm Hincl_refl Hspec_check_inhib).    
  Qed.

  (** No error lemma for map_check_inhib. *)

  Lemma map_check_inhib_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (inhib_places : list Place),
      incl inhib_places (fst (split marking)) ->
      exists b : bool,
        map_check_inhib sitpn marking inhib_places t = Some b.
  Proof.
    intros sitpn marking t inhib_places Hincl_inhibpl.
    unfold map_check_inhib.
    apply (map_check_inhib_aux_no_error sitpn marking t true Hincl_inhibpl).
  Qed.
  
End MapCheckFunctions.

(** ** Lemmas on [is_sensitized] function and its spec. *)

Section IsSensitized.
  
  (** Correctness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = (fs marking) ->
      In t (transs sitpn) -> 
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true ->
      IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t;
      functional induction (is_sensitized sitpn marking (lneighbours sitpn t) t)
                 using is_sensitized_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun.
    
    (* GENERAL CASE *)
    - injection Hfun; intro Heq_check.
      apply andb_prop in Heq_check; elim Heq_check; intros Heq_check' Heq_inhib.
      apply andb_prop in Heq_check'; elim Heq_check'; intros Heq_pre Heq_test.

      (* Determines ∀ (p, n) ∈ marking, (pre sitpn t p) <= n *)
      rewrite Heq_pre in e.
      specialize (map_check_pre_correct
                    marking t 
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e)
        as Hmap_pre.

      (* Determines ∀ (p, n) ∈ marking, (test sitpn t p) <= n *)
      rewrite Heq_test in e0.
      specialize (map_check_test_correct
                    marking t
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e0)
        as Hmap_test.
      
      (* Determines ∀ (p, n) ∈ marking, n < (inhib sitpn t p) ∨ (inhib sitpn t p) = 0 *)
      rewrite Heq_inhib in e1.
      specialize (map_check_inhib_correct
                    marking t
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e1)
        as Hmap_inhib.

      (* Unfolds IsSensitized and applies all previous lemmas. *)
      unfold IsSensitized; intros p n Hin_m.
      split;
        [apply (Hmap_pre p n Hin_m)
        | split; [ apply (Hmap_test p n Hin_m) |
                   apply (Hmap_inhib p n Hin_m) ]].

    (* ERROR CASES *)
    - inversion Hfun.
    - inversion Hfun.
    - inversion Hfun.
  Qed.

  Theorem is_sensitized_correct_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) -> 
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true ->
      IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t;
      functional induction (is_sensitized sitpn marking (lneighbours sitpn t) t)
                 using is_sensitized_ind;
      intros Hwell_def_sitpn Heq_pl_fsm Hin_t_transs Hfun.
    
    (* GENERAL CASE *)
    - injection Hfun; intro Heq_check.
      apply andb_prop in Heq_check; elim Heq_check; intros Heq_check' Heq_inhib.
      apply andb_prop in Heq_check'; elim Heq_check'; intros Heq_pre Heq_test.

      (* Determines ∀ (p, n) ∈ marking, (pre sitpn t p) <= n *)
      rewrite Heq_pre in e.
      specialize (map_check_pre_correct_perm
                    marking t 
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e)
        as Hmap_pre.

      (* Determines ∀ (p, n) ∈ marking, (test sitpn t p) <= n *)
      rewrite Heq_test in e0.
      specialize (map_check_test_correct_perm
                    marking t
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e0)
        as Hmap_test.
      
      (* Determines ∀ (p, n) ∈ marking, n < (inhib sitpn t p) ∨ (inhib sitpn t p) = 0 *)
      rewrite Heq_inhib in e1.
      specialize (map_check_inhib_correct_perm
                    marking t
                    Hwell_def_sitpn Heq_pl_fsm Hin_t_transs e1)
        as Hmap_inhib.

      (* Unfolds IsSensitized and applies all previous lemmas. *)
      unfold IsSensitized; intros p n Hin_m.
      split;
        [apply (Hmap_pre p n Hin_m)
        | split; [ apply (Hmap_test p n Hin_m) |
                   apply (Hmap_inhib p n Hin_m) ]].

    (* ERROR CASES *)
    - inversion Hfun.
    - inversion Hfun.
    - inversion Hfun.
  Qed.    
    
  (** Completeness proof for is_sensitized and IsSensitized *)

  Theorem is_sensitized_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) ->
      In t (transs sitpn) ->
      IsSensitized sitpn marking t ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (is_sensitized sitpn marking (lneighbours sitpn t) t)
                 using is_sensitized_ind;
      intros Hwell_defined_sitpn Heq_pl_fsm Hin_t_transs Hspec;
      unfold IsSensitized in Hspec;
      
      (* Builds ∀ (p,n) ∈ marking, (pre sitpn t p) ≤ n, 
         then applies map_check_pre_complete.
       *)
      assert (Hmap_check_pre :
                forall (p : Place) (n : nat), In (p, n) marking -> pre sitpn t p <= n) by
          (intros p n Hin_m; generalize (Hspec p n Hin_m) as Hend; intro; elim Hend; auto);
      generalize (map_check_pre_complete marking t
                                         Hwell_defined_sitpn
                                         Heq_pl_fsm
                                         Hin_t_transs
                                         Hmap_check_pre) as Hmap_check_pre';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (test sitpn t p) ≤ n, 
         then applies map_check_test_complete.
       *)
      assert (Hmap_check_test :
                forall (p : Place) (n : nat), In (p, n) marking -> test sitpn t p <= n)
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_test_complete marking t
                                          Hwell_defined_sitpn
                                          Heq_pl_fsm
                                          Hin_t_transs
                                          Hmap_check_test) as Hmap_check_test';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (inhib sitpn t p) ≤ n, 
         then applies map_check_inhib_complete.
       *)
      assert (Hmap_check_inhib :
                forall (p : Place) (n : nat),
                  In (p, n) marking -> (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0))
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_inhib_complete marking t
                                           Hwell_defined_sitpn
                                           Heq_pl_fsm
                                           Hin_t_transs
                                           Hmap_check_inhib) as Hmap_check_inhib';
      intro.

    (* General case, all went well. 
       Using IsSensitized to prove that all the map_check functions
       return true. *)
    (* Rewrites the results of map_check functions, then reflexivity. *)
    - rewrite Hmap_check_pre' in e;
        rewrite Hmap_check_test' in e0;
        rewrite Hmap_check_inhib' in e1.
      injection e as e_check_pre_value;
        injection e0 as e_check_test_value;
        injection e1 as e_check_inhib_value.
      rewrite <- e_check_inhib_value;
        rewrite <- e_check_pre_value;
        rewrite <- e_check_test_value.
      do 2 rewrite andb_true_r; reflexivity.
      
    (* CASE map_check_inhib returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_inhib' in e1; inversion e1.
      
    (* CASE map_check_test returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_test' in e0; inversion e0.
      
    (* CASE map_check_pre returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_pre' in e; inversion e.
  Qed.

  Theorem is_sensitized_complete_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) ->
      In t (transs sitpn) ->
      IsSensitized sitpn marking t ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true.
  Proof.
    intros sitpn marking t;
      functional induction (is_sensitized sitpn marking (lneighbours sitpn t) t)
                 using is_sensitized_ind;
      intros Hwell_defined_sitpn Heq_pl_fsm Hin_t_transs Hspec;
      unfold IsSensitized in Hspec;
      
      (* Builds ∀ (p,n) ∈ marking, (pre sitpn t p) ≤ n, 
         then applies map_check_pre_complete.
       *)
      assert (Hmap_check_pre :
                forall (p : Place) (n : nat), In (p, n) marking -> pre sitpn t p <= n) by
          (intros p n Hin_m; generalize (Hspec p n Hin_m) as Hend; intro; elim Hend; auto);
      generalize (map_check_pre_complete_perm marking t
                                              Hwell_defined_sitpn
                                              Heq_pl_fsm
                                              Hin_t_transs
                                              Hmap_check_pre) as Hmap_check_pre';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (test sitpn t p) ≤ n, 
         then applies map_check_test_complete.
       *)
      assert (Hmap_check_test :
                forall (p : Place) (n : nat), In (p, n) marking -> test sitpn t p <= n)
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_test_complete_perm marking t
                                               Hwell_defined_sitpn
                                               Heq_pl_fsm
                                               Hin_t_transs
                                               Hmap_check_test) as Hmap_check_test';
      intro;
      (* Builds ∀ (p,n) ∈ marking, (inhib sitpn t p) ≤ n, 
         then applies map_check_inhib_complete.
       *)
      assert (Hmap_check_inhib :
                forall (p : Place) (n : nat),
                  In (p, n) marking -> (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0))
        by (intros p n Hin_m;
            generalize (Hspec p n Hin_m) as Hend;
            intro; decompose [and] Hend; auto);
      generalize (map_check_inhib_complete_perm marking t
                                                Hwell_defined_sitpn
                                                Heq_pl_fsm
                                                Hin_t_transs
                                                Hmap_check_inhib) as Hmap_check_inhib';
      intro.

    (* General case, all went well. 
       Using IsSensitized to prove that all the map_check functions
       return true. *)
    (* Rewrites the results of map_check functions, then reflexivity. *)
    - rewrite Hmap_check_pre' in e;
        rewrite Hmap_check_test' in e0;
        rewrite Hmap_check_inhib' in e1.
      injection e as e_check_pre_value;
        injection e0 as e_check_test_value;
        injection e1 as e_check_inhib_value.
      rewrite <- e_check_inhib_value;
        rewrite <- e_check_pre_value;
        rewrite <- e_check_test_value.
      do 2 rewrite andb_true_r; reflexivity.
      
    (* CASE map_check_inhib returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_inhib' in e1; inversion e1.
      
    (* CASE map_check_test returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_test' in e0; inversion e0.
      
    (* CASE map_check_pre returns None, impossible regarding the hypotheses. *)
    - rewrite Hmap_check_pre' in e; inversion e.
  Qed.

  (** No error lemma for is_sensitized. *)

  Theorem is_sensitized_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      incl (flatten_neighbours (lneighbours sitpn t)) (fst (split marking)) ->
      exists b : bool,
        is_sensitized sitpn marking (lneighbours sitpn t) t = Some b.
  Proof.
    intros sitpn marking t Hincl_flat.
    unfold is_sensitized.

    (* Prepares hypotheses to apply no error lemmas. *)
    assert (Hincl_prepl : incl (pre_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros p Hin_prepl.
      apply or_introl
        with (B := In p ((test_pl (lneighbours sitpn t))
                           ++ (inhib_pl (lneighbours sitpn t))
                           ++ (post_pl (lneighbours sitpn t))))
        in Hin_prepl.
      apply in_or_app in Hin_prepl.
      apply (Hincl_flat p Hin_prepl).      
    }

    assert (Hincl_testpl : incl (test_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros p Hin_testpl.
      apply or_intror
        with (A := In p (pre_pl (lneighbours sitpn t)))
        in Hin_testpl.
      apply in_or_app in Hin_testpl.
      apply or_introl
        with (B := In p ((inhib_pl (lneighbours sitpn t)) ++ (post_pl (lneighbours sitpn t))))
        in Hin_testpl.
      apply in_or_app in Hin_testpl.
      rewrite <- app_assoc in Hin_testpl.
      apply (Hincl_flat p Hin_testpl).      
    }

    assert (Hincl_inhibpl : incl (inhib_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros p Hin_inhibpl.
      apply or_intror
        with (A := In p ((pre_pl (lneighbours sitpn t)) ++ (test_pl (lneighbours sitpn t))))
        in Hin_inhibpl.
      apply in_or_app in Hin_inhibpl.
      apply or_introl
        with (B := In p (post_pl (lneighbours sitpn t)))
        in Hin_inhibpl.
      apply in_or_app in Hin_inhibpl.
      do 2 (rewrite <- app_assoc in Hin_inhibpl).
      apply (Hincl_flat p Hin_inhibpl).      
    }

    specialize (map_check_pre_no_error sitpn marking t Hincl_prepl)
      as Hmap_check_pre_ex.

    specialize (map_check_test_no_error sitpn marking t Hincl_testpl)
      as Hmap_check_test_ex.

    specialize (map_check_inhib_no_error sitpn marking t Hincl_inhibpl)
      as Hmap_check_inhib_ex.

    inversion_clear Hmap_check_pre_ex as (check_pre_result & Hmap_check_pre).
    inversion_clear Hmap_check_test_ex as (check_test_result & Hmap_check_test).
    inversion_clear Hmap_check_inhib_ex as (check_inhib_result & Hmap_check_inhib).

    rewrite Hmap_check_pre, Hmap_check_test, Hmap_check_inhib.

    exists (check_pre_result && check_test_result && check_inhib_result); reflexivity.
  Qed.

  (** Conjunction of correction and completeness for is_sensitized. *)

  Theorem is_sensitized_iff :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) -> 
      In t (transs sitpn) ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true <->
      IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Heq_pl_fsm Hin_t_transs.
    split;
      [ intro Hfun;
        apply (is_sensitized_correct marking t
                                     Hwell_def_sitpn Heq_pl_fsm
                                     Hin_t_transs Hfun)
      | intro Hspec;
        apply (is_sensitized_complete Hwell_def_sitpn Heq_pl_fsm
                                      Hin_t_transs Hspec) ].
  Qed.

  Theorem is_sensitized_iff_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) -> 
      In t (transs sitpn) ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some true <->
      IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Heq_pl_fsm Hin_t_transs.
    split;
      [ intro Hfun;
        apply (is_sensitized_correct_perm marking t
                                          Hwell_def_sitpn Heq_pl_fsm
                                          Hin_t_transs Hfun)
      | intro Hspec;
        apply (is_sensitized_complete_perm Hwell_def_sitpn Heq_pl_fsm
                                           Hin_t_transs Hspec) ].
  Qed.

  (** Conjunction of correction and completeness for ~is_sensitized. *)

  Theorem not_is_sensitized_iff :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      (places sitpn) = fst (split marking) -> 
      In t (transs sitpn) ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some false <->
      ~IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Heq_pl_fsm Hin_t_transs.
    split.
    
    - intros Hfun Hspec;
        rewrite <- (is_sensitized_iff marking t
                                      Hwell_def_sitpn Heq_pl_fsm Hin_t_transs)
        in Hspec.
      rewrite Hfun in Hspec; inversion Hspec.

    - intro Hspec; case_eq (is_sensitized sitpn marking (lneighbours sitpn t) t).
      + dependent induction b.
        -- intros His_sens_fun.
           rewrite <- (is_sensitized_iff marking t
                                         Hwell_def_sitpn Heq_pl_fsm Hin_t_transs)
             in Hspec.
           contradiction.
        -- intros; reflexivity.
      + intros Hsens_fun.
        
        (* Specializes is_sensitized_no_error to solve the subgoal. *)
        explode_well_defined_sitpn.
        unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
        assert (Hincl_flat_lneigh : incl (flatten_neighbours (lneighbours sitpn t))
                                         (flatten_lneighbours sitpn (transs sitpn))).
        {
          intros p Hin_p_flat;
            apply (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_p_flat).
        }
        specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
        rewrite Heq_pl_fsm in Hincl_fl_m.

        specialize (is_sensitized_no_error sitpn marking t Hincl_fl_m)
          as Hsens_ex.
        inversion_clear Hsens_ex as (b & Hsens).
        rewrite Hsens_fun in Hsens; inversion Hsens.
  Qed.

  Theorem not_is_sensitized_iff_perm :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      Permutation (places sitpn) (fs marking) -> 
      In t (transs sitpn) ->
      is_sensitized sitpn marking (lneighbours sitpn t) t = Some false <->
      ~IsSensitized sitpn marking t.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Heq_pl_fsm Hin_t_transs.
    split.
    
    - intros Hfun Hspec;
        rewrite <- (is_sensitized_iff_perm marking t
                                           Hwell_def_sitpn Heq_pl_fsm Hin_t_transs)
        in Hspec.
      rewrite Hfun in Hspec; inversion Hspec.

    - intro Hspec; case_eq (is_sensitized sitpn marking (lneighbours sitpn t) t).
      + dependent induction b.
        -- intros His_sens_fun.
           rewrite <- (is_sensitized_iff_perm marking t
                                              Hwell_def_sitpn Heq_pl_fsm Hin_t_transs)
             in Hspec.
           contradiction.
        -- intros; reflexivity.
      + intros Hsens_fun.
        
        (* Specializes is_sensitized_no_error to solve the subgoal. *)

        assert (Hincl_flat_lneigh : incl (flatten_neighbours (lneighbours sitpn t))
                                         (flatten_lneighbours sitpn (transs sitpn))).
        {
          explode_well_defined_sitpn.
          unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
          intros p Hin_p_flat;
            apply (in_neigh_in_flatten t p Hwell_def_sitpn Hin_t_transs Hin_p_flat).
        }
        
        assert (Hincl_fl_m : incl (flatten_neighbours (lneighbours sitpn t)) (fs marking)).
        {
          explode_well_defined_sitpn.
          unfold NoUnknownPlaceInNeighbours in Hunk_pl_neigh.
          specialize (incl_tran Hincl_flat_lneigh Hunk_pl_neigh) as Hincl_fl_m.
          intros p Hin_p_fl.
          rewrite <- Heq_pl_fsm.
          apply (Hincl_fl_m p Hin_p_fl).
        }
        
        specialize (is_sensitized_no_error sitpn marking t Hincl_fl_m)
          as Hsens_ex.
        inversion_clear Hsens_ex as (b & Hsens).
        rewrite Hsens_fun in Hsens; inversion Hsens.
  Qed.
  
End IsSensitized.

(** ** Lemmas about [in_list] function. *)

Section InList.

  Variable A : Type.
  
  Lemma in_list_correct :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A)
           (a : A),
      in_list eq_dec l a = true -> In a l.
  Proof.
    intros eq_dec l a;
      functional induction (in_list eq_dec l a) using in_list_ind;
      intros Hfun.

    (* BASE CASE *)
    - inversion Hfun.

    (* CASE hd. *)
    - apply in_eq.

    (* CASE not hd. *)
    - apply in_cons.
      apply (IHb Hfun).
  Qed.

  Lemma not_in_list_correct :
    forall (eq_dec : forall x y : A, {x = y} + {x <> y})
           (l : list A)
           (a : A),
      in_list eq_dec l a = false -> ~In a l.
  Proof.
    intros eq_dec l a;
      functional induction (in_list eq_dec l a) using in_list_ind;
      intros Hfun.

    (* BASE CASE *)
    - intros Hin_nil; inversion Hin_nil.

    (* CASE hd. *)
    - inversion Hfun.

    (* CASE not hd. *)
    - rewrite not_in_cons.
      split; [auto | apply (IHb Hfun)].
  Qed.
      
End InList.

(** * Lemmas about [has_entered_time_window] and its spec. *)

Section HasEnteredTimeWindow.

  (** Correctness lemma for [has_entered_time_window]. *)

  Lemma has_entered_time_window_correct :
    forall (sitpn : Sitpn)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans),
      has_entered_time_window sitpn d_intervals t = Some true ->
      HasEnteredTimeWindow sitpn d_intervals t.
  Proof.
    intros sitpn d_intervals t;
      functional induction (has_entered_time_window sitpn d_intervals t)
                 using has_entered_time_window_ind;
      intro Hfun;
      unfold HasEnteredTimeWindow.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min = 0. *)
    - right; exists _x0; apply (get_value_correct Nat.eq_dec t d_intervals e0). 

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min <> 0. *)
    - injection Hfun as Hfun; inversion Hfun.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = blocked *)
    - injection Hfun as Hfun; inversion Hfun.

    (* ERROR CASE, get_value = None. *)
    - inversion Hfun.

    (* CASE s_intervals = None *)
    - left; assumption.
  Qed.

  (** Correctness lemma for has_entered_time_window = Some false. *)

  Lemma not_has_entered_time_window_correct :
    forall (sitpn : Sitpn)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans),
      NoDup (fst (split d_intervals)) ->
      has_entered_time_window sitpn d_intervals t = Some false ->
      ~HasEnteredTimeWindow sitpn d_intervals t.
  Proof.
    intros sitpn d_intervals t;
      functional induction (has_entered_time_window sitpn d_intervals t)
                 using has_entered_time_window_ind;
      intros Hnodup_fs_ditvals Hfun;
      unfold HasEnteredTimeWindow.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min = 0. *)
    - injection Hfun as Heq_true_false; inversion Heq_true_false.

    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = Some active min <> 0. *)
    - intro Hhas_entered_vee.
      inversion_clear Hhas_entered_vee as [Hs_itvals_none | Hex_active_0].

      (* Case s_intervals = None then contradiction. *)
      + rewrite e in Hs_itvals_none; inversion Hs_itvals_none.

      (* Case (t, active 0) ∈ ditvals, impossible as NoDup (fs ditvals) *)
      + specialize (get_value_correct Nat.eq_dec t d_intervals e0) as Hin_t_actS_ditvals.
        inversion_clear Hex_active_0 as (up_bound & Hin_t_act0_ditvals).

        contradiction_with_nodup_same_pair d_intervals
                                           (t, active {| min_t := S _x1; max_t := _x0 |})
                                           (t, active {| min_t := 0; max_t := up_bound |})
                                           Hin_t_actS_ditvals
                                           Hin_t_act0_ditvals.
                
    (* CASE s_intervals = Some itval ∧ get_value t d_intervals = blocked *)
    - intro Hhas_entered_vee.
      inversion_clear Hhas_entered_vee as [Hs_itvals_none | Hex_active_0].

      (* Case s_intervals = None then contradiction. *)
      + rewrite e in Hs_itvals_none; inversion Hs_itvals_none.

      (* Case (t, active 0) ∈ ditvals, impossible as NoDup (fs ditvals) *)
      + specialize (get_value_correct Nat.eq_dec t d_intervals e0) as Hin_t_actS_ditvals.
        inversion_clear Hex_active_0 as (up_bound & Hin_t_act0_ditvals).
        
        contradiction_with_nodup_same_pair d_intervals
                                           (t, blocked)
                                           (t, active {| min_t := 0; max_t := up_bound |})
                                           Hin_t_actS_ditvals
                                           Hin_t_act0_ditvals.
                
    (* ERROR CASE, get_value = None. *)
    - inversion Hfun.

    (* CASE s_intervals = None *)
    - injection Hfun as Hfun; inversion Hfun.
  Qed.

  (** No error lemma for [has_entered_time_window]. *)

  Lemma has_entered_time_window_no_error :
    forall (sitpn : Sitpn)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans),
      s_intervals sitpn t = None \/ In t (fs d_intervals) ->
      exists b : bool,
        has_entered_time_window sitpn d_intervals t = Some b.
  Proof.
    intros sitpn d_intervals t Hv_sitvals_ditvals.
    inversion_clear Hv_sitvals_ditvals as [Heq_none_sitvals | Hin_t_fs_ditvals].

    (* CASE s_intervals sitpn t = None *)
    - unfold has_entered_time_window.
      rewrite Heq_none_sitvals; exists true; reflexivity.
      
    (* CASE In t (fs (d_intervals)) *)
    - unfold has_entered_time_window.
      destruct (s_intervals sitpn t).

      (* CASE s_intervals = Some _ *)
      +
        
        (* Specializes get_value_no_error and rewrites the goal. *)
        specialize (get_value_no_error Nat.eq_dec t d_intervals Hin_t_fs_ditvals) as Hex_gv.
        inversion_clear Hex_gv as (value & Hgv).
        rewrite Hgv.
        destruct value.

        (* CASE value = active {| min_t := 0 |} *)
        -- destruct t1; destruct min_t; [exists true; auto | exists false; auto].

        (* CASE value = _ *)
        -- exists false; reflexivity.
           
      (* CASE s_intervals = None *)
      + exists true; reflexivity.      
  Qed.
  
End HasEnteredTimeWindow.

(** * Lemmas about [are_all_conditions_true] and its spec. *)

Section AreAllConditionsTrue.

  Lemma are_all_conditions_true_correct :
    forall (sitpn : Sitpn)
           (cond_values : list (Condition * bool))
           (t : Trans),
      are_all_conditions_true sitpn cond_values t = true ->
      forall c : Condition,
        In c (fst (split cond_values)) ->
        has_condition sitpn t c = true ->
        In (c, true) cond_values.
  Proof.
    intros sitpn cond_values t;
      functional induction (are_all_conditions_true sitpn cond_values t)
                 using are_all_conditions_true_ind;
      intros Hfun c' Hin_fs_condv Hhas_cond.

    (* BASE CASE, cond_values = []. *)
    - inversion Hin_fs_condv.

    (* CASE has_condition = true and b = true. *)
    - rewrite fst_split_cons_app in Hin_fs_condv; simpl in Hin_fs_condv.
      inversion_clear Hin_fs_condv as [Heq_cc' | Hin_c'_tl].

      (* Case c = c'. *)
      + rewrite <- Heq_cc'; apply in_eq.

      (* Case c' ∈ tl *)
      + apply in_cons; apply (IHb Hfun c' Hin_c'_tl Hhas_cond).

    (* CASE has_condition = true and b = false *)
    - inversion Hfun.

    (* CASE has_condition = false *)
    - rewrite fst_split_cons_app in Hin_fs_condv; simpl in Hin_fs_condv.
      inversion_clear Hin_fs_condv as [Heq_cc' | Hin_c'_tl].

      (* Case c = c'. *)
      + rewrite <- Heq_cc' in Hhas_cond; rewrite e1 in Hhas_cond; inversion Hhas_cond.

      (* Case c' ∈ tl *)
      + apply in_cons; apply (IHb Hfun c' Hin_c'_tl Hhas_cond).
  Qed.

  (** Correctness lemma for are_all_conditions_true = false. *)
  
  Lemma not_are_all_conditions_true_correct :
    forall (sitpn : Sitpn)
           (cond_values : list (Condition * bool))
           (t : Trans),
      are_all_conditions_true sitpn cond_values t = false ->
      exists c : Condition,
        In c (fst (split cond_values)) /\
        has_condition sitpn t c = true /\
        In (c, false) cond_values.
  Proof.
    intros sitpn cond_values t;
      functional induction (are_all_conditions_true sitpn cond_values t)
                 using are_all_conditions_true_ind;
      intro Hfun;
      
      (* CASE b = true or has_cond c = false. *)
      (specialize (IHb Hfun) as Hex_cond;
       inversion_clear Hex_cond as (cond & Hw_cond);
       
       (* Instantiates c and prove each part of the conjunction. *)
       exists cond;
       repeat split; [apply proj1 in Hw_cond; rewrite fst_split_cons_app; apply in_cons; auto |
                      apply proj2 in Hw_cond; apply proj1 in Hw_cond; auto |
                      do 2 (apply proj2 in Hw_cond); apply in_cons; auto ])

       (* CASE has_cond c = true ∧ b = false *)
      || (exists c; repeat split; [rewrite fst_split_cons_app; apply in_eq | auto | apply in_eq ])

      (* BASE CASE *)
      || inversion Hfun.
  Qed.
  
End AreAllConditionsTrue.

(** * Lemmas about [sitpn_is_firable] and its spec. *)

Section SitpnIsFirable.

  (** A transition t is firable at state s' if it is
      firable at state s and if s and s' have same
      marking, dynamic intervals, and condition values,
      and conversely. *)

  Lemma sitpn_is_firable_iff_eq :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (t : Trans),
      (marking s) = (marking s') ->
      (d_intervals s) = (d_intervals s') ->
      (cond_values s) = (cond_values s') ->
      SitpnIsFirable sitpn s t <-> SitpnIsFirable sitpn s' t.
  Proof.
    intros sitpn s s' t Heq_m Heq_ditvals Heq_condv;
      split;
      intro His_fira;
      unfold SitpnIsFirable in *;
      rewrite <- Heq_ditvals, <- Heq_condv, <- Heq_m
      || rewrite Heq_ditvals, Heq_condv, Heq_m;                                      
      assumption.
  Qed.

  (** A transition t is firable at state s' if it is
      firable at state s and if s and s' have same
      marking, dynamic intervals, and condition values modulo
      permutation, and conversely. *)

  Lemma sitpn_is_firable_iff_perm :
    forall (sitpn : Sitpn)
           (s s' : SitpnState)
           (t : Trans),
      (marking s) = (marking s') ->
      Permutation (d_intervals s) (d_intervals s') ->
      Permutation (cond_values s) (cond_values s') ->
      SitpnIsFirable sitpn s t <-> SitpnIsFirable sitpn s' t.
  Proof.
    intros sitpn s s' t Heq_m Hperm_ditvals Hperm_condv; split;

    let deduce_goal state :=
        (
          intros His_firable;
          unfold SitpnIsFirable in His_firable;

          (* Builds hypotheses composing SitpnIsFirable state *)
         
          assert (Hhas_ent : HasEnteredTimeWindow sitpn (d_intervals state) t)
            by 
              (
                apply proj2, proj1 in His_firable;
                unfold HasEnteredTimeWindow in *;
                inversion_clear His_firable as [Heq_sitvals_none | Hin_ditvals];
                [
                  left; auto
                |
                inversion_clear Hin_ditvals as (up_bound & Hin_upb_ditvals);
                (rewrite Hperm_ditvals in Hin_upb_ditvals || rewrite <- Hperm_ditvals in Hin_upb_ditvals);
                right; exists up_bound; auto
                ]
              );

          assert (Hhas_reached : HasReachedAllConditions sitpn (cond_values state) t)
            by
              (
                do 2 (apply proj2 in His_firable);
                unfold HasReachedAllConditions in *;
                intros c; (rewrite <- Hperm_condv || rewrite Hperm_condv);
                apply (His_firable c)
              );

         (* Gets IsSensitized (marking s') then concludes. *)
         
         apply proj1 in His_firable;
         (rewrite Heq_m in His_firable || rewrite <- Heq_m in His_firable);

         apply (conj His_firable (conj Hhas_ent Hhas_reached))
        )
    in deduce_goal s || deduce_goal s'.
  Qed.
  
  (** Correctness lemma for sitpn_is_firable. *)
  
  Lemma sitpn_is_firable_correct :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      In t (transs sitpn) ->
      sitpn_is_firable sitpn s (lneighbours sitpn t) t = Some true ->
      SitpnIsFirable sitpn s t.
  Proof.
    intros sitpn s t Hwell_def_sitpn Hwell_def_s
           Hin_t_transs Hfun;
      functional induction (sitpn_is_firable sitpn s (lneighbours sitpn t) t)
                 using sitpn_is_firable_ind;
      unfold SitpnIsFirable;

    (* GENERAL CASE, all went well. 

       We need to apply correctness lemmas is_sensitized,
       has_entered_time_window and are_all_conditions_true. *)
      (
        (* Builds premises and specializes is_sensitized_correct
         to get IsSensitized. *)
        explode_well_defined_sitpn_state Hwell_def_s;
        specialize (is_sensitized_correct (marking s) t Hwell_def_sitpn
                                          Hwf_state_marking Hin_t_transs e)
          as His_sens;

        (* Builds premises and specializes has_entered_time_window
         to get HasEnteredTimeWindow. *)
        specialize (has_entered_time_window_correct sitpn (d_intervals s) t e1)
          as Hhas_entered_time;

        (* Builds premises and specializes are_all_conditions_true 
           to get HasReachedAllConditions. *)
        injection Hfun as Hare_all_cond;
        specialize (are_all_conditions_true_correct sitpn (cond_values s) t Hare_all_cond)
          as Hhas_reached_all_cond;
        rewrite <- Hwf_state_condv in Hhas_reached_all_cond;

        (* Applies conjunctions of lemmas. *)
        apply (conj His_sens (conj Hhas_entered_time Hhas_reached_all_cond))
      )
        
      (* CASES true = false *)
      || (injection Hfun as Hfun; inversion Hfun) 

      (* ERROR CASES *)
      || inversion Hfun.      
  Qed.

  (** Correctness lemma for sitpn_is_firable,
      with a state [s] that is not well-defined. *)
  
  Lemma sitpn_is_firable_correct_no_wd :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      places sitpn = (fs (marking s)) ->
      Permutation (conditions sitpn) (fs (cond_values s)) ->
      In t (transs sitpn) ->
      sitpn_is_firable sitpn s (lneighbours sitpn t) t = Some true ->
      SitpnIsFirable sitpn s t.
  Proof.
    intros sitpn s t Hwell_def_sitpn Heq_ms Hperm_conds
           Hin_t_transs Hfun;
      functional induction (sitpn_is_firable sitpn s (lneighbours sitpn t) t)
                 using sitpn_is_firable_ind;
      unfold SitpnIsFirable;

      (* GENERAL CASE, all went well. 
      
       We need to apply correctness lemmas is_sensitized,
       has_entered_time_window and are_all_conditions_true. *)
      (
        (* Builds premises and specializes is_sensitized_correct
         to get IsSensitized. *)
        specialize (is_sensitized_correct (marking s) t Hwell_def_sitpn
                                          Heq_ms Hin_t_transs e)
        as His_sens;

        (* Builds premises and specializes has_entered_time_window
         to get HasEnteredTimeWindow. *)
        specialize (has_entered_time_window_correct sitpn (d_intervals s) t e1)
          as Hhas_entered_time;

        (* Builds premises and specializes are_all_conditions_true 
         to get HasReachedAllConditions. *)
        assert (Hhas_reached_all_cond : HasReachedAllConditions sitpn (cond_values s) t)
          by
            (injection Hfun as Hare_all_cond;
             specialize (are_all_conditions_true_correct sitpn (cond_values s) t Hare_all_cond)
               as Hhas_reached_all_cond;
             unfold HasReachedAllConditions;
             unfold fs in Hperm_conds;
             intros c; rewrite Hperm_conds;
             apply (Hhas_reached_all_cond c));
          
          (* Applies conjunctions of lemmas. *)
          apply (conj His_sens (conj Hhas_entered_time Hhas_reached_all_cond))
        
      )
        
      (* CASES true = false *)
      || (injection Hfun as Hfun; inversion Hfun) 

      (* ERROR CASES *)
      || inversion Hfun.      
  Qed.
  
  Lemma not_sitpn_is_firable_correct :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      In t (transs sitpn) ->
      sitpn_is_firable sitpn s (lneighbours sitpn t) t = Some false ->
      ~SitpnIsFirable sitpn s t.
  Proof.
    intros sitpn s t Hwell_def_sitpn Hwell_def_s Hin_t_transs;
      functional induction (sitpn_is_firable sitpn s (lneighbours sitpn t) t)
                 using sitpn_is_firable_ind;
      intros Hfun His_firable;
      unfold SitpnIsFirable in His_firable.

    (* CASE are_all_conditions_true = false. 
       
       Show that it is in contradiction with HasReacheAllConditions
       in SitpnIsFirable. *)
    
    - injection Hfun as Hare_all_cond_false.
      
      (* Gets ~HasReachedAllConditions, i.e: 
         ∃c, c ∈ conditions ∧ C(t, c) ∧ (c, false) ∈ cond_values. *)
      specialize (not_are_all_conditions_true_correct sitpn (cond_values s) t Hare_all_cond_false)
        as Hex_cond_false.

      (* Creates (c, false) ∈ cond_values has an independent hyp. in
         the context. *)
      inversion_clear Hex_cond_false as (c & Hcond_false).
      explode_well_defined_sitpn_state Hwell_def_s.
      rewrite <- Hwf_state_condv in Hcond_false.
      inversion_clear Hcond_false as (Hin_c_conds & Hw_cond_false);
        inversion_clear Hw_cond_false as (Hhas_cond_true & Hcond_false).

      (* Specializes HasReacheAllConditions in SitpnIsFirable to get
         (c, true) ∈ cond_values in the context. *)
      do 2 (apply proj2 in His_firable).
      unfold HasReachedAllConditions in His_firable.
      specialize (His_firable c Hin_c_conds Hhas_cond_true) as Hcond_true.

      (* Shows contradiction with (c, true) ∈ cond_values and
         (c, false) ∈ cond_values and NoDup (fs cond_values). *)
      explode_well_defined_sitpn.
      assert (Hnodup_condv := Hnodup_cond).
      unfold NoDupConditions in Hnodup_condv.
      rewrite Hwf_state_condv in Hnodup_condv.
      assert (Heq_fs_c : fst (c, true) = fst (c, false)) by auto.
      specialize (nodup_same_pair (cond_values s) Hnodup_condv (c, true) (c, false)
                                  Hcond_true Hcond_false Heq_fs_c)
        as Heq_pair_c.
      injection Heq_pair_c as Heq_true_false; inversion Heq_true_false.
      
    (* CASE has_entered_window = false. 
       
       Show that it is in contradiction with HasEnteredTimeWindow
       in SitpnIsFirable. *)
    - explode_well_defined_sitpn_state Hwell_def_s.
      specialize (not_has_entered_time_window_correct Hnodup_state_ditvals e1)
        as Hnot_has_entered.
      apply proj2 in His_firable; apply proj1 in His_firable.
      contradiction.

    (* ERROR CASE, has_entered_time_window = None *)
    - inversion Hfun.

    (* CASE is_sensitized = false. *)
    - (* Builds premises and specializes is_sensitized_correct
         to get IsSensitized. *)
        explode_well_defined_sitpn_state Hwell_def_s;
        specialize (not_is_sensitized_iff (marking s) t Hwell_def_sitpn
                                          Hwf_state_marking Hin_t_transs)
          as His_sens_eq.
        rewrite His_sens_eq in e.
        apply proj1 in His_firable.
        contradiction.

    (* ERROR CASE, is_sensitized = None *)
    - inversion Hfun.
  Qed.

  Lemma not_sitpn_is_firable_correct_no_wd :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      places sitpn = (fs (marking s)) ->
      Permutation (conditions sitpn) (fs (cond_values s)) ->
      NoDup (fs (d_intervals s)) ->
      In t (transs sitpn) ->
      sitpn_is_firable sitpn s (lneighbours sitpn t) t = Some false ->
      ~SitpnIsFirable sitpn s t.
  Proof.
    intros sitpn s t Hwell_def_sitpn Heq_ms Hperm_conds Hnodup_ditvals Hin_t_transs;
      functional induction (sitpn_is_firable sitpn s (lneighbours sitpn t) t)
                 using sitpn_is_firable_ind;
      intros Hfun His_firable;
      unfold SitpnIsFirable in His_firable.

    (* CASE are_all_conditions_true = false. 
       
       Show that it is in contradiction with HasReacheAllConditions
       in SitpnIsFirable. *)
    
    - injection Hfun as Hare_all_cond_false.
      
      (* Gets ~HasReachedAllConditions, i.e: 
         ∃c, c ∈ conditions ∧ C(t, c) ∧ (c, false) ∈ cond_values. *)
      specialize (not_are_all_conditions_true_correct sitpn (cond_values s) t Hare_all_cond_false)
        as Hex_cond_false.

      (* Creates (c, false) ∈ cond_values has an independent hyp. in
         the context. *)
      inversion_clear Hex_cond_false as (c & Hcond_false).
      rewrite <- Hperm_conds in Hcond_false.
      inversion_clear Hcond_false as (Hin_c_conds & Hw_cond_false);
        inversion_clear Hw_cond_false as (Hhas_cond_true & Hcond_false).

      (* Specializes HasReacheAllConditions in SitpnIsFirable to get
         (c, true) ∈ cond_values in the context. *)
      do 2 (apply proj2 in His_firable).
      unfold HasReachedAllConditions in His_firable.
      specialize (His_firable c Hin_c_conds Hhas_cond_true) as Hcond_true.
      
      (* Shows contradiction with (c, true) ∈ cond_values and
         (c, false) ∈ cond_values and NoDup (fs cond_values). *)
      explode_well_defined_sitpn.
      assert (Hnodup_condv := Hnodup_cond).
      unfold NoDupConditions in Hnodup_condv.
      rewrite Hperm_conds in Hnodup_condv.
      assert (Heq_fs_c : fst (c, true) = fst (c, false)) by auto.
      specialize (nodup_same_pair (cond_values s) Hnodup_condv (c, true) (c, false)
                                  Hcond_true Hcond_false Heq_fs_c)
        as Heq_pair_c.
      injection Heq_pair_c as Heq_true_false; inversion Heq_true_false.
      
    (* CASE has_entered_window = false. 
       
       Show that it is in contradiction with HasEnteredTimeWindow
       in SitpnIsFirable. *)
    - specialize (not_has_entered_time_window_correct Hnodup_ditvals e1)
        as Hnot_has_entered.
      apply proj2 in His_firable; apply proj1 in His_firable.
      contradiction.

    (* ERROR CASE, has_entered_time_window = None *)
    - inversion Hfun.

    (* CASE is_sensitized = false. *)
    - (* Builds premises and specializes is_sensitized_correct
         to get IsSensitized. *)
      specialize (not_is_sensitized_iff (marking s) t Hwell_def_sitpn
                                        Heq_ms Hin_t_transs)
        as His_sens_eq.
      rewrite His_sens_eq in e.
      apply proj1 in His_firable.
      contradiction.

    (* ERROR CASE, is_sensitized = None *)
    - inversion Hfun.
  Qed.
  
  (** No error lemma for [sitpn_is_firable]. *)

  Lemma sitpn_is_firable_no_error :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans),
      incl (flatten_neighbours (lneighbours sitpn t)) (fst (split (marking s))) ->
      s_intervals sitpn t = None \/ In t (fs (d_intervals s)) ->
      exists b : bool,
        sitpn_is_firable sitpn s (lneighbours sitpn t) t = Some b.
  Proof.
    intros sitpn s t Hincl_fn_ms Hin_t_fs_ditvals.

    unfold sitpn_is_firable.

    (* Specializes is_sensitized_no_error, then rewrites the goal. *)
    
    specialize (is_sensitized_no_error sitpn (marking s) t Hincl_fn_ms)
      as Hex_is_sens.
    inversion_clear Hex_is_sens as (is_sens_res & His_sens).
    rewrite His_sens.
    destruct is_sens_res.

    (* CASE is_sensitized = Some true. *)
    -
      
      (* Specializes has_entered_time_window_no_error, then rewrites the goal. *)
      specialize (has_entered_time_window_no_error sitpn (d_intervals s) t Hin_t_fs_ditvals)
        as Hex_ent_time.
      inversion_clear Hex_ent_time as (ent_time_res & Hent_time).
      rewrite Hent_time.
      destruct ent_time_res.

      (* CASE has_entered_time_window = Some true *)
      + exists (are_all_conditions_true sitpn (cond_values s) t); reflexivity.

      (* CASE has_entered_time_window = Some false *)
      + exists false; reflexivity.
        
    (* CASE is_sensitized = Some false. *)
    - exists false; reflexivity.    
  Qed.
  
End SitpnIsFirable.

