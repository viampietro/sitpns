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

Require Import Coqlib.
Require Import ListsPlus.

(* Import Sitpn material. *)

Require Import simpl.Sitpn.
Require Import simpl.SitpnTokenPlayer.
Require Import simpl.SitpnSemantics.

(* Import Sitpn tactics, and misc. lemmas. *)

Require Import simpl.SitpnTactics.

(** * Lemmas about interpretation and well-definition. *)

(** ** All conditions are referenced in the condition values list. *)

Section SitpnFallingEdgeSameStructCondv.

  (** [get_condition_values] returns a list of condition values
      referencing all conditions defined in [conditions]. *)

  Lemma get_condition_values_same_struct_condv :
    forall (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool)),
      (fst (split cond_values)) ++ conditions =
      (fst (split (get_condition_values conditions time_value env cond_values))).
  Proof.
    intros conditions time_value env cond_values;
      functional induction (get_condition_values conditions time_value env cond_values)
                 using get_condition_values_ind.

    (* BASE CASE. *)
    - rewrite app_nil_r; reflexivity.

    (* INDUCTION CASE. *)
    - rewrite <- IHl;
        rewrite fst_split_app;
        simpl;
        rewrite <- app_assoc;
        reflexivity.
  Qed.
  
  (** All conditions defined in [sitpn] are referenced in the
      condition values list [s'.(cond_values)], where [s'] is the
      SitpnState returned by [sitpn_falling_edge] *)

  Lemma sitpn_falling_edge_same_struct_condv :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (conditions sitpn) = (fst (split (cond_values s'))).
  Proof.
    intros sitpn s time_value env s' Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

      (* GENERAL CASE, all went well. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       rewrite <- (get_condition_values_same_struct_condv
                     (conditions sitpn) time_value env []);
       simpl;
       reflexivity)
        
      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeSameStructCondv.

(** ** All actions are referenced in the action states list. *)

Section SitpnFallingEdgeSameStructActions.

  (** [get_action_states] returns a list of couples (action, state)
      referencing all actions defined in [actions]. *)

  Lemma get_action_states_same_struct_actions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (actions : list Action)
           (a_states : list (Action * bool)),
      (fst (split a_states)) ++ actions =
      (fst (split (get_action_states sitpn s actions a_states))).
  Proof.
    intros sitpn s actions a_states;
      functional induction (get_action_states sitpn s actions a_states)
                 using get_action_states_ind.

    (* BASE CASE. *)
    - rewrite app_nil_r; reflexivity.

    (* INDUCTION CASE. *)
    - rewrite <- IHl;
        rewrite fst_split_app;
        simpl;
        rewrite <- app_assoc;
        reflexivity.
  Qed.
  
  (** All actions defined in [sitpn] are referenced in the
      action states list [s'.(exec_a)], where [s'] is the
      SitpnState returned by [sitpn_falling_edge] *)

  Lemma sitpn_falling_edge_same_struct_actions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (actions sitpn) = (fst (split (exec_a s'))).
  Proof.
    intros sitpn s time_value env s' Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

      (* GENERAL CASE, all went well. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       rewrite <- (get_action_states_same_struct_actions sitpn s (actions sitpn) []);
       simpl;
       reflexivity)
        
      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeSameStructActions.

(** ** Function states stay the same on falling edge. *)

Section SitpnFallingEdgeSameFunctions.

  (** [sitpn_falling_edge] returns a SitpnState with the same function
      states list [exec_f] as in the starting state. *)

  Lemma sitpn_falling_edge_same_functions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (s' : SitpnState),
      sitpn_falling_edge sitpn s time_value env = Some s' ->
      (exec_f s) = (exec_f s').
  Proof.
    intros sitpn s time_value env s' Hfun.
    functional induction (sitpn_falling_edge sitpn s time_value env)
               using sitpn_falling_edge_ind;

      (* GENERAL CASE, all went well. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       reflexivity)
        
      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnFallingEdgeSameFunctions.

(** Condition values are unchanged by [sitpn_rising_edge]. *)

Section SitpnRisingEdgeSameCondv.

  (** [sitpn_rising_edge] returns a SitpnState with the same condition
      values list [cond_v] as in the starting state. *)

  Lemma sitpn_rising_edge_same_condv :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState),
      sitpn_rising_edge sitpn s = Some s' ->
      (cond_values s) = (cond_values s').
  Proof.
    intros sitpn s s' Hfun.
    functional induction (sitpn_rising_edge sitpn s)
               using sitpn_rising_edge_ind;

      (* GENERAL CASE, all went well. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       reflexivity)
        
      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeSameCondv.

(** Action states are unchanged by [sitpn_rising_edge]. *)

Section SitpnRisingEdgeSameActions.

  (** [sitpn_rising_edge] returns a SitpnState with the same condition
      values list [cond_v] as in the starting state. *)

  Lemma sitpn_rising_edge_same_actions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState),
      sitpn_rising_edge sitpn s = Some s' ->
      (exec_a s) = (exec_a s').
  Proof.
    intros sitpn s s' Hfun.
    functional induction (sitpn_rising_edge sitpn s)
               using sitpn_rising_edge_ind;

      (* GENERAL CASE, all went well. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       reflexivity)
        
      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeSameActions.

(** ** All functions are referenced in the function states list. *)

Section SitpnRisingEdgeSameStructFunctions.

  (** [get_function_states] returns a list of couples (function, state)
      referencing all functions defined in [functions]. *)

  Lemma get_function_states_same_struct_functions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (functions : list IFunction)
           (f_states : list (IFunction * bool)),
      (fst (split f_states)) ++ functions =
      (fst (split (get_function_states sitpn s functions f_states))).
  Proof.
    intros sitpn s functions f_states;
      functional induction (get_function_states sitpn s functions f_states)
                 using get_function_states_ind.

    (* BASE CASE. *)
    - rewrite app_nil_r; reflexivity.

    (* INDUCTION CASE. *)
    - rewrite <- IHl;
        rewrite fst_split_app;
        simpl;
        rewrite <- app_assoc;
        reflexivity.
  Qed.
  
  (** All functions defined in [sitpn] are referenced in the
      function states list [s'.(exec_f)], where [s'] is the
      SitpnState returned by [sitpn_rising_edge] *)

  Lemma sitpn_rising_edge_same_struct_functions :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState),
      sitpn_rising_edge sitpn s = Some s' ->
      (functions sitpn) = (fst (split (exec_f s'))).
  Proof.
    intros sitpn s s' Hfun.
    functional induction (sitpn_rising_edge sitpn s)
               using sitpn_rising_edge_ind;

      (* GENERAL CASE, all went well. *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       rewrite <- (get_function_states_same_struct_functions sitpn s (functions sitpn) []);
       simpl;
       reflexivity)
        
      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeSameStructFunctions.
