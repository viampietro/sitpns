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

(* Import lemmas on fired transitions. *)

Require Import simpl.SitpnWellDefFired.

(* Import lemmas on interpretation. *)

Require Import simpl.SitpnWellDefInterpretation.

(* Import lemmas on marking. *)

Require Import simpl.SitpnRisingEdgeMarking.

(* Import lemmas on well-definition. *)

Require Import simpl.SitpnRisingEdgeWellDef.

(* Import misc. tactics and lemmas. *)



Require Import simpl.SitpnTactics.

(** * [sitpn_rising_edge] and [sitpn_state_eq] relation. *)

(** ** [sitpn_state_eq], [sitpn_rising_edge] and marking. *)

(** Lemmas on [pre_sum] and [post_sum] functions. *)

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

Lemma sitpn_rising_edge_state_eq_perm_marking :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (marking s') (marking state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Stategy is to apply NoDup_Permutation, then we need: 
     - NoDup (marking s')
     - NoDup (marking state')
     - ∀(p, n) ∈ (marking s') ⇔ (p, n) ∈ (marking state'). *)

  (* Builds NoDup (marking s') and NoDup (marking state') *)
  
  specialize (sitpn_rising_edge_well_def_state
                sitpn s s' Hwell_def_sitpn Hwell_def_s Hrising_s)
    as Hwell_def_s'.  
  deduce_nodup_state_marking for s'.

  specialize (sitpn_rising_edge_well_def_state
                sitpn state state' Hwell_def_sitpn Hwell_def_state Hrising_state)
    as Hwell_def_state'.
  deduce_nodup_state_marking for state'.

  (* Saves the NoDup fs hypotheses for later. *)
  assert (Hnodup_ms := Hnodup_fs_ms).
  assert (Hnodup_mstate := Hnodup_fs_ms0).
  rename Hnodup_fs_ms0 into Hnodup_fs_mstate'.
  rename Hnodup_fs_ms into Hnodup_fs_ms'.
  
  apply nodup_fst_split in Hnodup_ms.
  apply nodup_fst_split in Hnodup_mstate.

  (* We must specialize eq_if_eq_fs to deduce
     ∀(p, n) ∈ (marking s') ⇔ (p, n) (marking state') *)

  (* First, we have to build:  
     ∀(a, b) ∈ (marking s) ⇒ ∃b', (a, b') ∈ (marking s') ∧
                                   (a, b') ∈ (marking state') *)
  
  (* Specializes sitpn_rising_edge_sub_pre_add_post for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_sub_pre_add_post
                sitpn s s' Hwell_def_sitpn Hwell_def_s Hrising_s)
    as Hdef_marking_s'.
  specialize (sitpn_rising_edge_sub_pre_add_post
                sitpn state state' Hwell_def_sitpn Hwell_def_state Hrising_state)
    as Hdef_marking_state'.

  assert (Hin_ms_ex_in :
            forall (a : Place) (b : nat),
              In (a, b) (marking s) ->
              exists b' : nat, In (a, b') (marking s') /\ In (a, b') (marking state')
         ).
  {
    (* Builds Permutation (marking s) (marking state) *)
    assert (Hperm_m := Hsteq_sstate).
    unfold sitpn_state_eq in Hperm_m.
    apply proj1 in Hperm_m.

    (* Specializes Hdef_*. *)
    intros a b Hin_ms.

    specialize (Hdef_marking_s' a b Hin_ms).
    rewrite Hperm_m in Hin_ms.
    specialize (Hdef_marking_state' a b Hin_ms).

    (* Builds pre_sum (fired s) = pre_sum (fired state). 
     * Deduced from Permutation (fired s) (fired state). *)

    assert (Hperm_fired := Hsteq_sstate).
    unfold sitpn_state_eq in Hperm_fired.
    apply proj2, proj1 in Hperm_fired.
    
    assert (Hequiv_fired: forall t : Trans, In t (fired s) <-> In t (fired state)) by
        (intros t; rewrite Hperm_fired; reflexivity).

    explode_well_defined_sitpn_state Hwell_def_s.
    explode_well_defined_sitpn_state Hwell_def_state.

    specialize (pre_sum_eq_iff_incl
                  sitpn a (fired s) (fired state)
                  Hnodup_state_fired Hnodup_state_fired0 Hequiv_fired)
      as Heq_presum.

    (* Builds post_sum (fired s) = post_sum (fired state). 
     * Deduced from Permutation (fired s) (fired state). *)

    specialize (post_sum_eq_iff_incl
                  sitpn a (fired s) (fired state)
                  Hnodup_state_fired Hnodup_state_fired0 Hequiv_fired)
      as Heq_postsum.

    do 2 clear_well_defined_sitpn_state.
    rewrite Heq_presum in Hdef_marking_s'.
    rewrite Heq_postsum in Hdef_marking_s'.
    
    (* Instantiates and deduces the goal. *)
    exists (b - pre_sum sitpn a (fired state) + post_sum sitpn a (fired state)).
    auto.
  }

  (* Second, we need: NoDup fs (marking s). *)
  deduce_nodup_state_marking for s.

  (* Third, we need: 
     fs (marking s) = fs (marking s') ∧ 
     fs (marking s) = fs (marking state') *)
  deduce_eq_from_wd_states_for s s'.
  deduce_eq_from_wd_states_for s state'.

  (* Finally, deduces: ∀(p, n) ∈ (marking s') ⇔ (p, n) (marking state') *)
  specialize (eq_if_eq_fs (marking s) (marking s') (marking state')
                          Hin_ms_ex_in Heq_state_marking Heq_state_marking0
                          Hnodup_fs_ms Hnodup_fs_ms' Hnodup_fs_mstate')
    as Hequiv_ms'_mstate'.

  (* Applies NoDup_Permutation, then QED. *)
  assert (Hequiv_simpl : forall (z : Place * nat), In z (marking s') <-> In z (marking state')) by 
      (intros z; destruct z; specialize (Hequiv_ms'_mstate' p n); assumption).
  apply (NoDup_Permutation Hnodup_ms Hnodup_mstate Hequiv_simpl).
Qed.
  
(** ** [sitpn_state_eq], [sitpn_rising_edge] and action states. *)

Lemma sitpn_rising_edge_state_eq_perm_actions :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (exec_a s') (exec_a state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Specializes sitpn_rising_edge_same_actions for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_same_actions sitpn s s' Hrising_s)
    as Heq_actions_s.
  specialize (sitpn_rising_edge_same_actions sitpn state state' Hrising_state)
    as Heq_actions_state.

  (* Decomposes sitpn_state_eq s state to 
     get Permutation (cond_values s) (cond_values state) *)
  unfold sitpn_state_eq in Hsteq_sstate.
  do 5 (apply proj2 in Hsteq_sstate).
  specialize (proj1 Hsteq_sstate) as Hperm_actions.

  (* Rewrites the goal and concludes. *)
  rewrite Heq_actions_s, Heq_actions_state in Hperm_actions; assumption.
Qed.

(** ** [sitpn_state_eq], [sitpn_rising_edge] and condition values. *)

Lemma sitpn_rising_edge_state_eq_perm_condv :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (cond_values s') (cond_values state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Specializes sitpn_rising_edge_same_condv for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_same_condv sitpn s s' Hrising_s)
    as Heq_condv_s.
  specialize (sitpn_rising_edge_same_condv sitpn state state' Hrising_state)
    as Heq_condv_state.

  (* Decomposes sitpn_state_eq s state to 
     get Permutation (cond_values s) (cond_values state) *)
  unfold sitpn_state_eq in Hsteq_sstate.
  do 4 (apply proj2 in Hsteq_sstate).
  specialize (proj1 Hsteq_sstate) as Hperm_condv.

  (* Rewrites the goal and concludes. *)
  rewrite Heq_condv_s, Heq_condv_state in Hperm_condv; assumption.
Qed.

(** ** [sitpn_state_eq], [sitpn_rising_edge] and fired transitions. *)

Lemma sitpn_rising_edge_state_eq_perm_fired :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (fired s') (fired state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.

  (* Specializes sitpn_rising_edge_same_fired for 
     Hrising_s and Hrising_state. *)
  specialize (sitpn_rising_edge_same_fired sitpn s s' Hrising_s)
    as Heq_fired_s.
  specialize (sitpn_rising_edge_same_fired sitpn state state' Hrising_state)
    as Heq_fired_state.

  (* Decomposes sitpn_state_eq s state to 
     get Permutation (fired s) (fired state) *)
  unfold sitpn_state_eq in Hsteq_sstate.
  specialize (proj1 (proj2 Hsteq_sstate)) as Hperm_fired. 

  (* Rewrites the goal and concludes. *)
  rewrite Heq_fired_s, Heq_fired_state in Hperm_fired; assumption.
Qed.

(** ** [sitpn_state_eq], [sitpn_rising_edge] and dynamic time intervals. *)

Lemma sitpn_rising_edge_state_eq_perm_ditvals :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    Permutation (d_intervals s') (d_intervals state').
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.
Admitted.
  
(** ** [sitpn_rising_edge] and [sitpn_state_eq]. *)

Lemma sitpn_rising_edge_state_eq :
  forall (sitpn : Sitpn)
         (s s' state state' : SitpnState),
    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn state ->
    sitpn_state_eq s state ->
    sitpn_rising_edge sitpn s = Some s' ->
    sitpn_rising_edge sitpn state = Some state' ->
    sitpn_state_eq s' state'.
Proof.
  intros sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
         Hwell_def_state Hsteq_sstate Hrising_s Hrising_state.
  unfold sitpn_state_eq.
  repeat split.

  (* CASE Permutation (marking s') (marking state') *)
  - apply (sitpn_rising_edge_state_eq_perm_marking
             sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
             Hwell_def_state Hsteq_sstate Hrising_s Hrising_state).

  (* CASE Permutation (fired s') (fired state') *)
  - apply (sitpn_rising_edge_state_eq_perm_fired
             sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
             Hwell_def_state Hsteq_sstate Hrising_s Hrising_state).

  (* CASE Permutation (d_intervals s') (d_intervals state') *)
  - admit.

  (* CASE Permutation (reset s') (reset state') *)
  - admit.

  (* CASE (cond_values s') (cond_values state') *)
  - apply (sitpn_rising_edge_state_eq_perm_condv
             sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
             Hwell_def_state Hsteq_sstate Hrising_s Hrising_state).

  (* CASE (exec_a s') (exec_a state') *)
  - apply (sitpn_rising_edge_state_eq_perm_actions
             sitpn s s' state state' Hwell_def_sitpn Hwell_def_s
             Hwell_def_state Hsteq_sstate Hrising_s Hrising_state).

  (* CASE (exec_f s') (exec_f state') *)
  - admit.
Admitted.
