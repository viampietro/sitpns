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

(* Import lemmas on synchronous execution rules. *)

Require Import simpl.SitpnFallingEdgeFired.

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import simpl.SitpnTactics.


(** * Falling Edge Lemmas about Interpretation-Related Semantics Rules. *) 

(** ** Condition values are retrieved for all conditions. *)

Section SitpnFallingEdgeGetCondv.

  (** All couple (cond, bool) that are in [cond_values]
      are in the final list returned by [get_condition_values]. *)

  Lemma get_condition_values_in_condv :
    forall (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool))
           (c : Condition)
           (b : bool),
      In (c, b) cond_values ->
      In (c, b) (get_condition_values conditions time_value env cond_values).
  Proof.
    intros conditions time_value env cond_values;
      functional induction (get_condition_values conditions time_value env cond_values)
                 using get_condition_values_ind;
      intros cond b Hin_condv.

    (* BASE CASE. *)
    - assumption.

    (* INDUCTION CASE. *)
    - apply or_introl with (B := (In (cond, b) [(c, env c time_value)])) in Hin_condv.
      apply in_or_app in Hin_condv.
      apply (IHl cond b Hin_condv).
  Qed.
      
  (** All conditions in [conditions] are associated to the boolean value
      [env c time_value] in the list returned by [get_condition_values]. *)

  Lemma get_condition_values_cons :
    forall (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool))
           (c : Condition),
      In c conditions ->
      In (c, env c time_value) (get_condition_values conditions time_value env cond_values).
  Proof.
    intros conditions time_value env cond_values;
      functional induction (get_condition_values conditions time_value env cond_values)
                 using get_condition_values_ind;
      intros cond Hin_conds.

    (* BASE CASE *)
    - inversion Hin_conds.

    (* INDUCTION CASE *)
    - inversion_clear Hin_conds as [Heq_cond | Hin_tl].

      (* Case c = cond *)
      + rewrite <- Heq_cond.

        (* Builds In (c, env) (cond_values ++ [(c, env)]) *)
        assert (Hin_condv: In (c, env c time_value) (cond_values ++ [(c, env c time_value)]))
          by (apply in_or_app; right; apply in_eq).

        (* Applies get_condition_values_in_condv. *)
        apply (get_condition_values_in_condv
                 tl time_value env (cond_values ++ [(c, env c time_value)])
                 c (env c time_value) Hin_condv).

      (* Case cond ∈ tl *)
      + apply (IHl cond Hin_tl).
  Qed.
        
  (** All condition values at the current time [time_value] are retrieved
      and put in the [s'.(cond_values)] list, where [s'] is the SitpnState
      returned by [sitpn_falling_edge]. *)

  Lemma sitpn_falling_edge_get_condv :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (c : Condition),
          In c sitpn.(conditions) ->
          In (c, (env c time_value)) s'.(cond_values)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hfun;

    (* GENERAL CASE *)
    (simpl in Hfun;
     injection Hfun as Heq_s';
     rewrite <- Heq_s';
     simpl;
     apply get_condition_values_cons)

    (* ERROR CASE *)
    || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeGetCondv.

(** ** Actions activation on falling edge. *)

Section SitpnFallingEdgeActivateActions.

  (** All couple (action, bool) that are in [a_states]
      are in the final list returned by [get_action_states]. *)

  Lemma get_action_states_in_astates :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (actions : list Action)
           (a_states : list (Action * bool))
           (a : Action)
           (b : bool),
      In (a, b) a_states ->
      In (a, b) (get_action_states sitpn s actions a_states).
  Proof.
    intros sitpn s actions a_states;
      functional induction (get_action_states sitpn s actions a_states)
                 using get_action_states_ind;
      intros action b Hin_astates.

    (* BASE CASE. *)
    - assumption.

    (* INDUCTION CASE. *)
    - apply or_introl
      with (B := (In (action, b) [(a, is_activated sitpn (marking s) a)]))
        in Hin_astates.
      apply in_or_app in Hin_astates.
      apply (IHl action b Hin_astates).
  Qed.
  
  Lemma is_activated_complete :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (a : Action),
      (exists (p : Place) (n : nat),
          In (p, n) marking /\ n > 0 /\ (has_action sitpn p a) = true) ->
      is_activated sitpn marking a = true.
  Proof.
    intros sitpn marking a;
      functional induction (is_activated sitpn marking a)
                 using is_activated_ind;
      intros Hex_p.

    (* BASE CASE *)
    - inversion Hex_p as (p & Hex_n).
      inversion Hex_n as (n & Hin_nil).
      apply proj1 in Hin_nil.
      inversion Hin_nil.

    (* CASE A(p, a) && n > 0 = true. *)
    - reflexivity.

    (* CASE A(p, a) && n > 0 = false. *)
    - (* Decomposes existential hypothesis. *)
      inversion_clear Hex_p as (place & Hex_n).
      inversion_clear Hex_n as (nboftokens & Hw_spec).
      inversion_clear Hw_spec as (Hin_pl_nb_m & Hw_spec').
      inversion_clear Hw_spec' as (Hnb_gt & Hhas_a_t).

      (* Two cases, (place, nboftokens) = (p, n) or 
         (place, nboftokens) ∈ tl *)
      inversion_clear Hin_pl_nb_m as [Heq_pn | Hin_pn_tl].

      (* Case (place, nboftokens) = (p, n) *)
      + injection Heq_pn as Heq_p Heq_n.
        rewrite andb_false_iff in e1.
        inversion e1 as [Hhas_a_f | Hn_le_0].

        (* Subcase A(p, a) = false *)
        -- rewrite Heq_p in Hhas_a_f.
           rewrite Hhas_a_t in Hhas_a_f;
             inversion Hhas_a_f.

        (* Subcase n <= 0 *)
        -- rewrite Nat.ltb_ge in Hn_le_0.
           rewrite Heq_n in Hn_le_0.
           inversion Hn_le_0 as [Hn_eq_0 | Hn_lt_0].
           rewrite Hn_eq_0 in Hnb_gt.
           inversion Hnb_gt.

      (* Case (place, nboftokens) ∈ tl *)
      + assert (Hex_pn :
                  exists (p : Place) (n : nat),
                    In (p, n) tl /\ n > 0 /\ has_action sitpn p a = true)
          by (exists place, nboftokens; auto).
        apply (IHb Hex_pn).
  Qed.
  
  (** Actions associated to marked places are activated (assoc. to
      true) in the list [exec_a'] returned by [get_action_states]. *)

  Lemma get_action_states_cons :
      forall (sitpn : Sitpn)
             (s : SitpnState)
             (actions : list Action)
             (a_states : list (Action * bool))
             (a : Action),
        In a actions ->
        (exists (p : Place) (n : nat),
            In (p, n) s.(marking) /\ n > 0 /\ (has_action sitpn p a) = true) ->
        In (a, true) (get_action_states sitpn s actions a_states).
  Proof.
    intros sitpn s actions a_states;
      functional induction (get_action_states sitpn s actions a_states)
                 using get_action_states_ind;
      intros action Hin_actions Hex_p.

    (* BASE CASE *)
    - inversion Hin_actions.

    (* INDUCTION CASE *)
    - inversion_clear Hin_actions as [Heq_action | Hin_act_tl].

      (* Case a = action *)
      + specialize (is_activated_complete sitpn (marking s) action Hex_p) as His_act_true.
        rewrite Heq_action; rewrite His_act_true.

        (* Builds In (action, true) (a_states ++ [(action, true)]) *)
        assert (Hin_astates: In (action, true) (a_states ++ [(action, true)]))
          by (apply in_or_app; right; apply in_eq).

        (* Applies get_action_states_in_astates. *)
        apply (get_action_states_in_astates
                 sitpn s tl (a_states ++ [(action, true)])
                 action true Hin_astates).
        
      (* Case In action tl *)
      + apply (IHl action Hin_act_tl Hex_p).
  Qed.
  
  (** Actions associated to marked places are activated (assoc. to
      true) in [s'.(exec_a)], where [s'] is the SitpnState returned by
      [sitpn_falling_edge]. *)
  
  Lemma sitpn_falling_edge_activate_actions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (a : Action),
          In a sitpn.(actions) ->
          (exists (p : Place) (n : nat),
              In (p, n) s.(marking) /\ n > 0 /\ (has_action sitpn p a) = true) ->
          In (a, true) s'.(exec_a)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hfun;

    (* GENERAL CASE *)
    (simpl in Hfun;
     injection Hfun as Heq_s';
     rewrite <- Heq_s';
     simpl;
     apply get_action_states_cons)

    (* ERROR CASE *)
    || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeActivateActions.

(** ** Deactivation of actions on falling edge. *)

Section SitpnFallingEdgeDeactivateActions.

  Lemma is_activated_complete_conv :
    forall (sitpn : Sitpn)
           (marking : list (Place * nat))
           (a : Action),
      (forall (p : Place) (n : nat),
          In (p, n) marking -> n = 0 \/ (has_action sitpn p a) = false) ->
      is_activated sitpn marking a = false.
  Proof.
    intros sitpn marking a;
      functional induction (is_activated sitpn marking a)
                 using is_activated_ind;
      intros Hunm_or_unassoc.

    (* BASE CASE. *)
    - reflexivity.

    (* CASE, test is true then contradiction. *)
    - assert (Hin_hd: In (p, n) ((p, n) :: tl)) by apply in_eq.
      specialize (Hunm_or_unassoc p n Hin_hd) as Hpunm_or_aunassoc.

      (* Two cases, n = 0 or A(p, a) = 0. *)
      inversion_clear Hpunm_or_aunassoc as [Hp_unm | Ha_unassoc];
        rewrite andb_true_iff in e1;
        inversion_clear e1 as (Ha_assoc & Hp_mrk).

      (* Case n = 0. *)
      + rewrite Hp_unm in Hp_mrk.
        rewrite Nat.ltb_irrefl in Hp_mrk.
        inversion Hp_mrk.

      (* Case A(p, a) = 0. *)
      + rewrite Ha_assoc in Ha_unassoc;
          inversion Ha_unassoc.

    (* INDUCTION CASE. *)
    - apply IHb.
      intros pl nboftokens Hin_tl.
      apply in_cons with (a := (p, n)) in Hin_tl.
      apply (Hunm_or_unassoc pl nboftokens Hin_tl).
  Qed.
  
  (** If action [a] ∈ [actions] is only associated to unmarked places
      in marking [(marking s)] then [(a, false)] is in the list returned by
      [get_action_states]. *)
  
  Lemma get_action_states_cons_conv :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (actions : list Action)
           (a_states : list (Action * bool))
           (a : Action),
      In a actions ->
      (forall (p : Place) (n : nat),
          In (p, n) s.(marking) -> n = 0 \/ (has_action sitpn p a) = false) ->
      In (a, false) (get_action_states sitpn s actions a_states).
  Proof.
    intros sitpn s actions a_states;
      functional induction (get_action_states sitpn s actions a_states);
      intros action Hin_a_actions Hunm_or_unassoc.

    (* BASE CASE. *)
    - inversion Hin_a_actions.

    (* INDUCTION CASE. *)
    - (* Two cases, action = a or action ∈ tl. *)
      inversion_clear Hin_a_actions as [Heq_aaction | Hin_action_tl].

      (* Case a = action. *)
      + (* We need to prove that is_activated sitpn (marking s) a
           returns false. *)
        specialize (is_activated_complete_conv sitpn (marking s) action Hunm_or_unassoc) as His_act_false.
        rewrite Heq_aaction; rewrite His_act_false.

        (* Builds In (action, true) (a_states ++ [(action, true)]) *)
        assert (Hin_astates: In (action, false) (a_states ++ [(action, false)]))
          by (apply in_or_app; right; apply in_eq).

        (* Applies get_action_states_in_astates. *)
        apply (get_action_states_in_astates
                 sitpn s tl (a_states ++ [(action, false)])
                 action false Hin_astates).
        
      (* Case In action tl *)
      + apply (IHl action Hin_action_tl Hunm_or_unassoc).
  Qed.
    
  (** All actions that are associated only with unmarked places
      are marked as deactivate in [s'.exec_a], where [s']
      is the SitpnState returned by [sitpn_falling_edge]. *)
  
  Lemma sitpn_falling_edge_deactivate_actions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (forall (a : Action),
          In a sitpn.(actions) ->
          (forall (p : Place) (n : nat),
              In (p, n) s.(marking) -> n = 0 \/ (has_action sitpn p a) = false) ->
          In (a, false) s'.(exec_a)).
  Proof.
    intros sitpn s time_value env;
      functional induction (sitpn_falling_edge sitpn s time_value env)
                 using sitpn_falling_edge_ind;
      intros s' Hfun;

      (* GENERAL CASE *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       apply get_action_states_cons_conv)

      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeDeactivateActions.
