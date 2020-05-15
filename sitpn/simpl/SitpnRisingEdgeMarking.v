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



(* Import lemmas about marking and well-definition. *)

Require Import simpl.SitpnWellDefMarking.

(* Import tertium non datur *)

Require Import Classical_Prop.

(** * Lemmas on [modify_m] and its spec. *)

Section ModifyM.
  
  (** Correctness proof for [modify_m]. 
      
      Needed in update_marking_pre_aux_correct. *)
  
  Lemma modify_m_correct :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      NoDup (fst (split marking)) ->
      modify_m marking p op nboftokens = Some final_marking ->
      forall n : nat, In (p, n) marking -> In (p, op n nboftokens) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hnodup Hfun n' Hin_n'_m.
    
    (* ERROR CASE *)
    - inversion Hfun.
      
    (* INDUCTION CASE *)

    (* CASE p = hd. *)
    - inversion_clear Hin_n'_m as [Heq_pn'_p'n | Hin_pn'_tl].

      (* Case (p, n') = (p', n) *)
      + injection Heq_pn'_p'n as Heq_p'p Heqnn'.
        rewrite <- Heqnn';
          injection Hfun as Hfun;
          rewrite <- Hfun;
          apply in_eq.

      (* Case (p, n') ∈ tl *)
      + rewrite fst_split_cons_app in Hnodup.
        simpl in Hnodup.
        deduce_nodup_hd_not_in.
        apply in_fst_split in Hin_pn'_tl.
        rewrite (beq_nat_true p' p e1) in Hnot_in_tl.
        contradiction.

    (* CASE p <> hd ∧ rec = Some m'. *)
    - inversion_clear Hin_n'_m as [Heq_pn'_p'n | Hin_pn'_tl].

      (* Case (p, n') = (p', n) *)
      + injection Heq_pn'_p'n as Heq_p'p Heqnn'.
        apply beq_nat_false in e1.
        contradiction.

      (* Case (p, n') ∈ tl *)
      + rewrite fst_split_cons_app in Hnodup;
          simpl in Hnodup;
          rewrite NoDup_cons_iff in Hnodup;
          apply proj2 in Hnodup.
        injection Hfun as Hfun;
          rewrite <- Hfun;
          apply in_cons.
        apply (IHo m' Hnodup e2 n' Hin_pn'_tl). 

    (* ERROR CASE, rec = None *)
    - inversion Hfun.    
  Qed.

  Lemma modify_m_in_if_diff :
    forall (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat)
           (final_marking : list (Place * nat)),
      modify_m marking p op nboftokens = Some final_marking ->
      forall (p' : Place) (n : nat), p <> p' -> In (p', n) marking <-> In (p', n) final_marking.
  Proof.
    intros marking p op nboftokens;
      functional induction (modify_m marking p op nboftokens) using modify_m_ind;
      intros final_marking Hfun p'' n' Hdiff_pp.

    (* ERROR CASE *)
    - inversion Hfun.
      
    (* CASE p = hd *)
    - injection Hfun as Hfun.
      apply not_eq_sym in Hdiff_pp.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' n) as Hdiff_nn0.
      specialize (fst_diff_pair_diff p'' p Hdiff_pp n' (op n nboftokens)) as Hdiff_nnb.
      split.
      
      + intros Hin_p''n'.
        inversion_clear Hin_p''n' as [Heq_p''n'_p'n | Hin_tl].

        -- symmetry in Heq_p''n'_p'n.
           rewrite (beq_nat_true p' p e1) in Heq_p''n'_p'n.
           contradiction.

        -- rewrite <- Hfun; apply in_cons; assumption.

      + intros Hin_p''n'_fm.
        rewrite <- Hfun in Hin_p''n'_fm.

        inversion_clear Hin_p''n'_fm as [Heq_p''n'_pop | Hin_tl].

        -- symmetry in Heq_p''n'_pop; contradiction.
        -- apply in_cons; assumption.

    (* CASE p <> hd ∧ rec = Some m' *)
    - injection Hfun as Hfun.
      split.

      + intros Hin_p''n'.
        inversion_clear Hin_p''n' as [Heq_p''n'_p'n | Hin_tl].

        -- rewrite <- Hfun;
             rewrite <- Heq_p''n'_p'n;
             apply in_eq.

        -- specialize (IHo m' e2 p'' n' Hdiff_pp)
            as Heq.
           rewrite <- Hfun; apply in_cons.
           rewrite <- Heq.
           assumption.
           
      + intros Hin_p''n'.
        rewrite <- Hfun in Hin_p''n'.
        inversion_clear Hin_p''n' as [Heq_p''n'_p'n | Hin_tl].

        -- rewrite <- Heq_p''n'_p'n;
             apply in_eq.

        -- specialize (IHo m' e2 p'' n' Hdiff_pp)
            as Heq.
           apply in_cons.
           rewrite Heq.
           assumption.
           
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for modify_m. *)

  Lemma modify_m_no_error :
    forall (m : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat),
      In p (fst (split m)) ->
      exists m' : list (Place * nat),
        modify_m m p op nboftokens = Some m'.
  Proof.
    intros m p op nboftokens;
      functional induction (modify_m m p op nboftokens)
                 using modify_m_ind;
      intros Hin_p_fs.

    (* BASE CASE *)
    - simpl in Hin_p_fs; inversion Hin_p_fs.

    (* CASE p = hd *)
    - exists ((p, op n nboftokens) :: tl); reflexivity.

    (* CASE p <> hd ∧ rec = Some m' *)
    - exists ((p', n) :: m'); reflexivity.

    (* CASE p <> hd ∧ rec = None *)
    - rewrite fst_split_cons_app in Hin_p_fs; simpl in Hin_p_fs.
      inversion_clear Hin_p_fs as [Heq_p'p | Hin_p_fs_tl].

      + apply beq_nat_false in e1; contradiction.
      + specialize (IHo Hin_p_fs_tl) as Hex_modif.
        inversion_clear Hex_modif as (m' & Hmodif).
        rewrite e2 in Hmodif; inversion Hmodif.
  Qed.
  
End ModifyM.

(** Lemmas on update_marking_pre and update_marking_post functions,
    and their mapped versions. *)

Section SitpnUpdateMarking.

  (** Needed to prove update_marking_pre_aux_correct. *)

  Lemma update_marking_pre_aux_not_in_pre_places :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      update_marking_pre_aux sitpn m t pre_places = Some m' ->
      forall (p : Place),
        ~In p pre_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros sitpn m t pre_places;
      functional induction (update_marking_pre_aux sitpn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hfun p' Hnot_in_pre n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_pre.
      elim Hnot_in_pre; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking p Nat.sub (pre sitpn t p)
                    m' e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_pre_aux].
    Express the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_pre_correct. *)

  Lemma update_marking_pre_aux_correct :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (pre_places : list Place)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      NoDup pre_places ->
      incl pre_places (pre_pl (lneighbours sitpn t)) ->
      update_marking_pre_aux sitpn m t pre_places = Some m' ->
      forall (p : Place) (n : nat),
        In p pre_places ->
        In (p, n) m ->
        In (p, n - (pre sitpn t p)) m'.
  Proof.
    intros sitpn m t pre_places;
      functional induction (update_marking_pre_aux sitpn m t pre_places)
                 using update_marking_pre_aux_ind;
      intros fm Hwell_def_sitpn Hnodup_m
             Hnodup_pre_pl Hincl_pre_pl Hfun p' n Hin_pre_pl Hin_resid.
    
    (* BASE CASE, pre_places = []. *)
    - inversion Hin_pre_pl.
      
    (* GENERAL CASE *)
    - inversion Hin_pre_pl as [Heq_pp' | Hin_p'_tail].

      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_pre_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.sub (pre sitpn t p) m'
                      Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_pre_pl.
        elim Hnodup_pre_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_pre_aux_not_in_pre_places
                      sitpn m' t tail fm
                      Hfun p' Hnot_in_tl (n - pre sitpn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.

      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking p Nat.sub (pre sitpn t p) m' e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.

        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_pre_pl;
          elim Hnodup_pre_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_pre_pl.        

        (* Then specializes the induction hypothesis. *)
        specialize (IHo fm Hwell_def_sitpn Hnodup_m
                        Hnodup_tl Hincl_pre_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (modify_m_in_if_diff
                      marking p Nat.sub (pre sitpn t p) m'
                      e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
        
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for update_marking_pre_aux. *)
  
  Lemma update_marking_pre_aux_no_error :
    forall (sitpn : Sitpn)
           (t : Trans)
           (pre_places : list Place)
           (m : list (Place * nat)),
      incl pre_places (fst (split m)) ->
      exists m' : list (Place * nat),
        update_marking_pre_aux sitpn m t pre_places = Some m'.
  Proof.
    intros sitpn t; induction pre_places; intros residual_marking Hincl_pre.
    (* BASE CASE *)
    - simpl; exists residual_marking; reflexivity.
    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: pre_places)) by apply in_eq.
      specialize (Hincl_pre a Hin_eq) as Hin_a_res.
      specialize (modify_m_no_error residual_marking a Nat.sub (pre sitpn t a) Hin_a_res)
        as Hmodify_ex.
      inversion_clear Hmodify_ex as (m' & Hmodify).
      rewrite Hmodify.
      apply incl_cons_inv in Hincl_pre.
      specialize (modify_m_same_struct residual_marking a Nat.sub (pre sitpn t a) m' Hmodify)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_pre.
      apply (IHpre_places m' Hincl_pre).
  Qed.

  (** Correctness proof for [update_marking_pre]. 

      Needed to prove GENERAL CASE in sitpn_fire_aux_sens_by_residual. *)
  
  Lemma update_marking_pre_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split marking)) ->
      In t (transs sitpn) ->
      update_marking_pre sitpn marking (lneighbours sitpn t) t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n - (pre sitpn t p)) final_marking.
  Proof.
    intros sitpn marking t;
      functional induction (update_marking_pre sitpn marking (lneighbours sitpn t) t)
                 using update_marking_pre_ind;
      intros final_marking Hwell_def_sitpn Hnodup_resm Hin_t_transs Hfun p n Hin_resm.

    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (pre_pl neigh_of_t), or
       p ∉ (pre_pl neigh_of_t). *)
      assert (Hvee_in_pre_pl := classic (In p (pre_pl (lneighbours sitpn t)))).
      inversion_clear Hvee_in_pre_pl as [Hin_p_pre | Hnotin_p_pre].

      (* First case, p ∈ pre_pl, then applies update_marking_pre_aux_correct. *)
      + explode_well_defined_sitpn.

        (* Builds NoDup pre_pl. *)
        assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
          by (unfold flatten_neighbours; apply in_or_app; left; assumption).      
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t Hin_t_transs) as Hnodup_flat.
        apply proj1 in Hnodup_flat;
          apply nodup_app in Hnodup_flat;
          apply proj1 in Hnodup_flat.

        (* Then, applies update_marking_pre_aux_correct. *)
        apply (update_marking_pre_aux_correct
                 sitpn marking t (pre_pl (lneighbours sitpn t))
                 final_marking Hwell_def_sitpn Hnodup_resm Hnodup_flat
                 (incl_refl (pre_pl (lneighbours sitpn t)))
                 Hfun p n Hin_p_pre Hin_resm).
        
      (* Second case, p ∉ pre_pl, then applies 
       update_marking_pre_aux_not_in_pre_places. *)
      + explode_well_defined_sitpn.
        unfold AreWellDefinedPreEdges in Hwell_def_pre.
        specialize (Hwell_def_pre t p Hin_t_transs) as Hw_pre_edges.
        apply proj2 in Hw_pre_edges; specialize (Hw_pre_edges Hnotin_p_pre).
        rewrite Hw_pre_edges; rewrite Nat.sub_0_r.
        specialize (update_marking_pre_aux_not_in_pre_places
                      sitpn marking t (pre_pl (lneighbours sitpn t))
                      final_marking Hfun p Hnotin_p_pre n) as Hequiv.
        rewrite <- Hequiv; assumption.
  Qed.

  (** No error lemma for [update_marking_pre]. *)
  
  Lemma update_marking_pre_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      incl (flatten_neighbours (lneighbours sitpn t)) (fst (split marking)) ->
      exists final_marking : list (Place * nat),
        update_marking_pre sitpn marking (lneighbours sitpn t) t = Some final_marking.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Hincl_flat.
    explode_well_defined_sitpn.
    unfold NoDupTranss in Hnodup_transs.
    unfold update_marking_pre.
    assert (Hincl_prepl : incl (pre_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros x Hin_x_pre.
      apply or_introl
        with (B := In x ((test_pl (lneighbours sitpn t))
                           ++ (inhib_pl (lneighbours sitpn t))
                           ++ (post_pl (lneighbours sitpn t))))
        in Hin_x_pre.
      apply in_or_app in Hin_x_pre.
      apply (Hincl_flat x Hin_x_pre).
    }
    apply (update_marking_pre_aux_no_error
             sitpn t (pre_pl (lneighbours sitpn t)) marking Hincl_prepl).
  Qed.

  (** 
   * Correctness lemma for [map_update_marking_pre].
   * 
   * map_update_marking_pre sitpn m fired = m' ⇒ m' = m - ∑ pre(t), ∀ t ∈ fired
   * 
   * [map_update_marking_pre] substracts tokens in the pre-places 
   *  of all transitions ∈ fired. 
   *  
   *)
  
  Lemma map_update_marking_pre_sub_pre :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      incl fired (transs sitpn) ->
      map_update_marking_pre sitpn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n - pre_sum sitpn p fired) m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_pre sitpn m fired) using map_update_marking_pre_ind;
      intros fm Hwell_def_sitpn Hnodup_m Hincl_transs Hfun p n Hin_m.
    
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite Nat.sub_0_r; assumption.
      
    (* GENERAL CASE *)
    - specialize (Hincl_transs t (in_eq t tail)) as Hin_t_transs. 
      simpl. 
      rewrite Nat.sub_add_distr.
      specialize (update_marking_pre_correct
                    sitpn marking t m' Hwell_def_sitpn Hnodup_m Hin_t_transs e0 p n Hin_m) as Hin_m'.
      apply update_marking_pre_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_sitpn Hnodup_m (incl_cons_inv t tail (transs sitpn) Hincl_transs)
                 Hfun p (n - pre sitpn t p) Hin_m').

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for [map_update_marking_pre]. *)

  Lemma map_update_marking_pre_no_error :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (m : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      (forall (t : Trans),
          In t fired ->
          incl (flatten_neighbours (lneighbours sitpn t)) (fst (split m))) ->
      exists m' : list (Place * nat),
        map_update_marking_pre sitpn m fired = Some m'.
  Proof.
    intros sitpn; induction fired; intros m Hwell_def_sitpn Hincl_fl_m.

    (* BASE CASE *)
    - simpl; exists m; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: fired)) by apply in_eq.
      specialize (Hincl_fl_m a Hin_eq) as Hincl_flat.
      specialize (update_marking_pre_no_error
                    sitpn m a Hwell_def_sitpn Hincl_flat)
        as Hupdate_pre_ex.
      inversion_clear Hupdate_pre_ex as ( final_marking & Hupdate_pre ).
      rewrite Hupdate_pre.
      specialize (update_marking_pre_same_marking sitpn m a final_marking Hupdate_pre)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_fl_m.
      assert (Hincl_fl_tl :
                forall t : Trans,
                  In t fired ->
                  incl (flatten_neighbours (lneighbours sitpn t)) (fst (split final_marking))).
      {
        intros t Hin_t_fired;
          apply (in_cons a) in Hin_t_fired;
          apply (Hincl_fl_m t Hin_t_fired).
      }
      apply (IHfired final_marking Hwell_def_sitpn Hincl_fl_tl).
  Qed.  

  (** Needed to prove update_marking_post_aux_correct. *)

  Lemma update_marking_post_aux_not_in_post_places :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      update_marking_post_aux sitpn m t post_places = Some m' ->
      forall (p : Place),
        ~In p post_places ->
        forall (n : nat), In (p, n) m <-> In (p, n) m'.
  Proof.
    intros sitpn m t post_places;
      functional induction (update_marking_post_aux sitpn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hfun p' Hnot_in_post n.
    (* BASE CASE *)
    - injection Hfun as Hfun.
      rewrite Hfun; reflexivity.
    (* GENERAL CASE *)
    - apply not_in_cons in Hnot_in_post.
      elim Hnot_in_post; intros Hdiff_pp' Hnot_in_tl.
      apply not_eq_sym in Hdiff_pp'.
      specialize (modify_m_in_if_diff
                    marking p Nat.add (post sitpn t p)
                    m' e0 p' n Hdiff_pp') as Hequiv.
      rewrite Hequiv.
      apply (IHo fm Hfun p' Hnot_in_tl n).

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** Correctness proof for [update_marking_post_aux].
    Expostss the structure of the returned [m'] regarding the structure
    of [m]. 

    Needed to prove update_marking_post_correct. *)

  Lemma update_marking_post_aux_correct :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (t : Trans)
           (post_places : list Place)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      NoDup post_places ->
      incl post_places (post_pl (lneighbours sitpn t)) ->
      update_marking_post_aux sitpn m t post_places = Some m' ->
      forall (p : Place) (n : nat),
        In p post_places ->
        In (p, n) m ->
        In (p, n + (post sitpn t p)) m'.
  Proof.
    intros sitpn m t post_places;
      functional induction (update_marking_post_aux sitpn m t post_places)
                 using update_marking_post_aux_ind;
      intros fm Hwell_def_sitpn Hnodup_m
             Hnodup_post_pl Hincl_post_pl Hfun p' n Hin_post_pl Hin_resid.
    
    (* BASE CASE, post_places = []. *)
    - inversion Hin_post_pl.
      
    (* GENERAL CASE *)
    - inversion Hin_post_pl as [Heq_pp' | Hin_p'_tail].

      (* First subcase, p = p'. *)
      + rewrite <- Heq_pp' in Hin_post_pl.
        rewrite <- Heq_pp' in Hin_resid.
        specialize (modify_m_correct
                      marking p Nat.add (post sitpn t p)
                      m' Hnodup_m e0 n Hin_resid) as Hin_resid'.
        apply NoDup_cons_iff in Hnodup_post_pl.
        elim Hnodup_post_pl; intros Hnot_in_tl Hnodup_tl.
        rewrite Heq_pp' in Hnot_in_tl.
        specialize (update_marking_post_aux_not_in_post_places
                      sitpn m' t tail
                      fm Hfun p' Hnot_in_tl (n + post sitpn t p)) as Hin_equiv'.
        rewrite Heq_pp' in Hin_resid'.
        rewrite Heq_pp' in Hin_equiv'.
        rewrite Hin_equiv' in Hin_resid'; assumption.

      (* Second subcase, In p' tail, then apply induction hypothesis. *)
      (* But we need to show NoDup (fst (split residual')) first. *)
      + specialize (modify_m_same_struct
                      marking p Nat.add (post sitpn t p) m' e0)
          as Hsame_struct.
        unfold MarkingHaveSameStruct in Hsame_struct.
        rewrite Hsame_struct in Hnodup_m.

        (* Builds the other hypotheses, needed to specialize IHo. *)
        apply NoDup_cons_iff in Hnodup_post_pl;
          elim Hnodup_post_pl;
          intros Hnot_in_tl Hnodup_tl.
        apply incl_cons_inv in Hincl_post_pl.        

        (* Then specializes the induction hypothesis. *)
        specialize (IHo fm Hwell_def_sitpn Hnodup_m
                        Hnodup_tl Hincl_post_pl Hfun
                        p' n Hin_p'_tail) as Himpl.
        specialize (not_in_in_diff p p' tail (conj Hnot_in_tl Hin_p'_tail))
          as Hdiff_pp.
        specialize (@modify_m_in_if_diff
                      marking p Nat.add (post sitpn t p) m'
                      e0 p' n Hdiff_pp) as Hequiv'.
        rewrite <- Hequiv' in Himpl.
        apply (Himpl Hin_resid).
        
    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for update_marking_post_aux. *)
  
  Lemma update_marking_post_aux_no_error :
    forall (sitpn : Sitpn)
           (t : Trans)
           (post_places : list Place)
           (m : list (Place * nat)),
      incl post_places (fst (split m)) ->
      exists m' : list (Place * nat),
        update_marking_post_aux sitpn m t post_places = Some m'.
  Proof.
    intros sitpn t; induction post_places; intros residual_marking Hincl_post.
    (* BASE CASE *)
    - simpl; exists residual_marking; reflexivity.
    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: post_places)) by apply in_eq.
      specialize (Hincl_post a Hin_eq) as Hin_a_res.
      specialize (modify_m_no_error residual_marking a Nat.add (post sitpn t a) Hin_a_res)
        as Hmodify_ex.
      inversion_clear Hmodify_ex as (m' & Hmodify).
      rewrite Hmodify.
      apply incl_cons_inv in Hincl_post.
      specialize (@modify_m_same_struct residual_marking a Nat.add (post sitpn t a) m' Hmodify)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_post.
      apply (IHpost_places m' Hincl_post).
  Qed.

  (** Correctness proof for [update_marking_post]. 

      Needed to prove GENERAL CASE in sitpn_fire_aux_sens_by_residual. *)
  
  Lemma update_marking_post_correct :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (final_marking : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split marking)) ->
      In t (transs sitpn) ->
      update_marking_post sitpn marking (lneighbours sitpn t) t = Some final_marking ->
      forall (p : Place) (n : nat),
        In (p, n) marking -> In (p, n + (post sitpn t p)) final_marking.
  Proof.
    intros sitpn marking t;
      functional induction (update_marking_post sitpn marking (lneighbours sitpn t) t)
                 using update_marking_post_ind;
      intros final_marking Hwell_def_sitpn Hnodup_resm Hin_t_transs Hfun p n Hin_resm.

    (* GENERAL CASE *)
    - (* Two cases, either p ∈ (post_pl neigh_of_t), or
       p ∉ (post_pl neigh_of_t). *)
      assert (Hvee_in_post_pl := classic (In p (post_pl (lneighbours sitpn t)))).
      inversion_clear Hvee_in_post_pl as [Hin_p_post | Hnotin_p_post].

      (* First case, p ∈ post_pl, then applies update_marking_post_aux_correct. *)
      + explode_well_defined_sitpn.

        (* Builds NoDup post_pl. *)
        assert (Hin_flat : In p (flatten_neighbours (lneighbours sitpn t)))
          by (unfold flatten_neighbours; do 3 (apply in_or_app; right); assumption).      
        unfold NoDupInNeighbours in Hnodup_neigh.
        specialize (Hnodup_neigh t Hin_t_transs) as Hnodup_flat.
        apply proj2 in Hnodup_flat.

        (* Then, applies update_marking_post_aux_correct. *)
        apply (@update_marking_post_aux_correct
                 sitpn marking t (post_pl (lneighbours sitpn t)) final_marking
                 Hwell_def_sitpn Hnodup_resm Hnodup_flat
                 (incl_refl (post_pl (lneighbours sitpn t))) Hfun p n Hin_p_post Hin_resm).
        
      (* Second case, p ∉ post_pl, then applies 
       update_marking_post_aux_not_in_post_places. *)
      + explode_well_defined_sitpn.
        unfold AreWellDefinedPostEdges in Hwell_def_post.
        specialize (Hwell_def_post t p Hin_t_transs) as Hw_post_edges.
        apply proj2 in Hw_post_edges; specialize (Hw_post_edges Hnotin_p_post).
        rewrite Hw_post_edges. rewrite <- plus_n_O.
        specialize (update_marking_post_aux_not_in_post_places
                      sitpn marking t (post_pl (lneighbours sitpn t))
                      final_marking Hfun p Hnotin_p_post n) as Hequiv.
        rewrite <- Hequiv; assumption.
  Qed.

  (** No error lemma for [update_marking_post]. *)
  
  Lemma update_marking_post_no_error :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans),
      IsWellDefinedSitpn sitpn ->
      incl (flatten_neighbours (lneighbours sitpn t)) (fst (split marking)) ->
      exists final_marking : list (Place * nat),
        update_marking_post sitpn marking (lneighbours sitpn t) t = Some final_marking.
  Proof.
    intros sitpn marking t Hwell_def_sitpn Hincl_flat.
    explode_well_defined_sitpn.
    unfold NoDupTranss in Hnodup_transs.
    unfold update_marking_post.
    assert (Hincl_postpl : incl (post_pl (lneighbours sitpn t)) (fst (split marking))).
    {
      intros x Hin_x_post.
      apply or_intror
        with (A := In x (pre_pl (lneighbours sitpn t) ++ test_pl (lneighbours sitpn t) ++ inhib_pl (lneighbours sitpn t)))
        in Hin_x_post.
      apply in_or_app in Hin_x_post.
      rewrite <- app_assoc in Hin_x_post.
      rewrite <- app_assoc in Hin_x_post.
      apply (Hincl_flat x Hin_x_post).
    }
    apply (update_marking_post_aux_no_error sitpn t (post_pl (lneighbours sitpn t)) marking Hincl_postpl).
  Qed.

  (** 
   * Correctness lemma for [map_update_marking_post].
   * 
   * map_update_marking_post sitpn m fired = m' ⇒ m' = m - ∑ post(t), ∀ t ∈ fired
   * 
   * [map_update_marking_post] substracts tokens in the post-places 
   *  of all transitions ∈ fired. 
   *  
   *)
  
  Lemma map_update_marking_post_add_post :
    forall (sitpn : Sitpn)
           (m : list (Place * nat))
           (fired : list Trans)
           (m' : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      NoDup (fst (split m)) ->
      incl fired (transs sitpn) ->
      map_update_marking_post sitpn m fired = Some m' ->
      forall (p : Place) (n : nat),
        In (p, n) m -> In (p, n + post_sum sitpn p fired) m'.
  Proof.
    intros sitpn m fired;
      functional induction (map_update_marking_post sitpn m fired) using map_update_marking_post_ind;
      intros fm Hwell_def_sitpn Hnodup_m Hincl_transs Hfun p n Hin_m.
    
    (* BASE CASE *)
    - injection Hfun as Heq_marking; rewrite <- Heq_marking.
      simpl; rewrite <- (plus_n_O n); assumption.
      
    (* GENERAL CASE *)
    - specialize (Hincl_transs t (in_eq t tail)) as Hin_t_transs. 
      simpl.
      rewrite <- plus_assoc_reverse.
      specialize (@update_marking_post_correct
                    sitpn marking t m' Hwell_def_sitpn Hnodup_m Hin_t_transs e0 p n Hin_m) as Hin_m'.
      apply update_marking_post_same_marking in e0;
        unfold MarkingHaveSameStruct in e0;
        rewrite e0 in Hnodup_m.
      apply (IHo fm Hwell_def_sitpn Hnodup_m (incl_cons_inv t tail (transs sitpn) Hincl_transs)
                 Hfun p (n + post sitpn t p) Hin_m').

    (* ERROR CASE *)
    - inversion Hfun.
  Qed.

  (** No error lemma for [map_update_marking_post]. *)

  Lemma map_update_marking_post_no_error :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (m : list (Place * nat)),
      IsWellDefinedSitpn sitpn ->
      (forall (t : Trans),
          In t fired ->
          incl (flatten_neighbours (lneighbours sitpn t)) (fst (split m))) ->
      exists m' : list (Place * nat),
        map_update_marking_post sitpn m fired = Some m'.
  Proof.
    intros sitpn; induction fired; intros m Hwell_def_sitpn Hincl_fl_m.

    (* BASE CASE *)
    - simpl; exists m; reflexivity.

    (* INDUCTION CASE *)
    - simpl.
      assert (Hin_eq : In a (a :: fired)) by apply in_eq.
      specialize (Hincl_fl_m a Hin_eq) as Hincl_flat.
      specialize (@update_marking_post_no_error
                    sitpn m a Hwell_def_sitpn Hincl_flat)
        as Hupdate_post_ex.
      inversion_clear Hupdate_post_ex as ( final_marking & Hupdate_post ).
      rewrite Hupdate_post.
      specialize (@update_marking_post_same_marking sitpn m a final_marking Hupdate_post)
        as Hsame_struct.
      rewrite Hsame_struct in Hincl_fl_m.
      assert (Hincl_fl_tl :
                forall t : Trans,
                  In t fired ->
                  incl (flatten_neighbours (lneighbours sitpn t)) (fst (split final_marking))).
      {
        intros t Hin_t_fired;
          apply (in_cons a) in Hin_t_fired;
          apply (Hincl_fl_m t Hin_t_fired).
      }
      apply (IHfired final_marking Hwell_def_sitpn Hincl_fl_tl).
  Qed.  
  
End SitpnUpdateMarking.

(** * Lemmas on [sitpn_rising_edge] and new marking computation. *)

Section SitpnRisingEdgeSubPreAddPost.

  (** Marking at state [s'] is obtained by firing all transitions in (fired s) list. 
      [s'] is the state returned by [sitpn_rising_edge]. *)
  
  Lemma sitpn_rising_edge_sub_pre_add_post :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      IsWellDefinedSitpn sitpn ->
      IsWellDefinedSitpnState sitpn s ->
      sitpn_rising_edge sitpn s = Some s' ->
      forall (p : Place) (n : nat),
        In (p, n) (marking s) ->
        In (p, n - (pre_sum sitpn p s.(fired)) + (post_sum sitpn p s.(fired)))
           (marking s').
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hwell_def_sitpn Hwell_def_s Hfun p n Hin_ms;

      (* GENERAL CASE *)
      (
        (* Builds premises to specialize map_update_marking_pre_sub_pre. *)
        deduce_nodup_state_marking;
        explode_well_defined_sitpn_state Hwell_def_s;
        assert (Hincl_s_fired_transs := Hincl_state_fired_transs);
        clear_well_defined_sitpn_state;

        (* Specializes map_update_marking_pre_sub_pre. *)
        specialize (map_update_marking_pre_sub_pre
                      sitpn (marking s) (fired s) transient_marking Hwell_def_sitpn
                      Hnodup_fs_ms Hincl_state_fired_transs e) as Hsub_pre;

          (* Builds premises to specialize map_update_marking_post_add_post. *)
          specialize (map_update_marking_pre_same_marking sitpn (marking s) (fired s) transient_marking e)
          as Heq_ms_tm;
          assert (Hnodup_fs_tm : NoDup (fst (split transient_marking)))
            by (rewrite <- Heq_ms_tm; assumption);

          (* Specializes map_update_marking_post_add_post. *)
          specialize (map_update_marking_post_add_post
                        sitpn transient_marking (fired s) final_marking Hwell_def_sitpn
                        Hnodup_fs_tm Hincl_state_fired_transs e2) as Hadd_post;

          (* Specializes Hsub_pre then Hadd_post, then rewrite the goal
             to obtain an assumption. *)
          specialize (Hsub_pre p n Hin_ms) as Hin_tm;
          specialize (Hadd_post p (n - pre_sum sitpn p (fired s)) Hin_tm) as Hin_fm;
          injection Hfun as Hfun; rewrite <- Hfun; simpl; assumption
      )

      (* ERROR CASES *)
      || inversion Hfun.
  Qed.
    
End SitpnRisingEdgeSubPreAddPost.
