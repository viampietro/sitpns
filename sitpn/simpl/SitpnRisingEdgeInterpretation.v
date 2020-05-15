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

(** * Function executions on rising edge. *)

Section SitpnRisingEdgeExecFun.

  (** All couple (function, bool) that are in [f_states]
      are in the final list returned by [get_function_states]. *)

  Lemma get_function_states_in_fstates :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (functions : list IFunction)
           (f_states : list (IFunction * bool))
           (f : IFunction)
           (b : bool),
      In (f, b) f_states ->
      In (f, b) (get_function_states sitpn s functions f_states).
  Proof.
    intros sitpn s functions f_states;
      functional induction (get_function_states sitpn s functions f_states)
                 using get_function_states_ind;
      intros function b Hin_fstates.

    (* BASE CASE. *)
    - assumption.

    (* INDUCTION CASE. *)
    - apply or_introl
      with (B := (In (function, b) [(f, is_executed sitpn (fired s) f)]))
        in Hin_fstates.
      apply in_or_app in Hin_fstates.
      apply (IHl function b Hin_fstates).
  Qed.
  
  Lemma is_executed_complete :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (f : IFunction),
      (exists (t : Trans),
          In t fired /\ (has_function sitpn t f) = true) ->
      is_executed sitpn fired f = true.
  Proof.
    intros sitpn fired f;
      functional induction (is_executed sitpn fired f)
                 using is_executed_ind;
      intros Hex_t.

    (* BASE CASE *)
    - inversion_clear Hex_t as (t & Hw_in_has).
      apply proj1 in Hw_in_has.
      inversion Hw_in_has.

    (* CASE F(t, f) && t ∈ fired = true. *)
    - reflexivity.

    (* CASE F(t, f) = false. *)
    - (* Decomposes existential hypothesis. *)
      inversion_clear Hex_t as (trans & Hw_in_has).
      inversion_clear Hw_in_has as (Hin_t_fired & Hhas_fun).

      (* Two cases, trans = t or trans ∈ tl *)
      inversion_clear Hin_t_fired as [Heq_ttr | Hin_tr_tl].

      (* Case t = trans *)
      + rewrite Heq_ttr in e0; rewrite e0 in Hhas_fun; inversion Hhas_fun.

      (* Case trans ∈ tl *)
      + assert (Hex_tr :
                  exists (t : Trans),
                    In t tl /\ has_function sitpn t f = true)
          by (exists trans; auto).
        apply (IHb Hex_tr).
  Qed.
  
  (** Functions associated to fired transitions are executed
      (assoc. to true) in the list [exec_f'] returned by
      [get_function_states]. *)

  Lemma get_function_states_cons :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (functions : list IFunction)
           (f_states : list (IFunction * bool))
           (f : IFunction),
      In f functions ->
      (exists (t : Trans),
          In t (fired s) /\ (has_function sitpn t f) = true) ->
      In (f, true) (get_function_states sitpn s functions f_states).
  Proof.
    intros sitpn s functions f_states;
      functional induction (get_function_states sitpn s functions f_states)
                 using get_function_states_ind;
      intros function Hin_functions Hex_tr.

    (* BASE CASE *)
    - inversion Hin_functions.

    (* INDUCTION CASE *)
    - inversion_clear Hin_functions as [Heq_fun | Hin_fun_tl].

      (* Case f = function *)
      + specialize (is_executed_complete sitpn (fired s) function Hex_tr) as His_exec_true.
        rewrite Heq_fun; rewrite His_exec_true.

        (* Builds In (function, true) (f_states ++ [(function, true)]) *)
        assert (Hin_fstates: In (function, true) (f_states ++ [(function, true)]))
          by (apply in_or_app; right; apply in_eq).

        (* Applies get_function_states_in_fstates. *)
        apply (get_function_states_in_fstates
                 sitpn s tl (f_states ++ [(function, true)])
                 function true Hin_fstates).
        
      (* Case In function tl *)
      + apply (IHl function Hin_fun_tl Hex_tr).
  Qed.
  
  Lemma sitpn_rising_edge_exec_fun :
    forall (sitpn : Sitpn)
           (s s' : SitpnState),
      sitpn_rising_edge sitpn s = Some s' ->
      forall (f : IFunction),
        In f sitpn.(functions) ->
        (exists (t : Trans),
            In t s.(fired) /\ (has_function sitpn t f) = true) ->
        In (f, true) s'.(exec_f).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s) using sitpn_rising_edge_ind;
      intros s' Hfun;
      
      (* GENERAL CASE *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       apply get_function_states_cons)

      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
      
End SitpnRisingEdgeExecFun.

(** * Functions not executed on rising edge. *)

Section SitpnRisingEdgeNotExecFun.

  Lemma is_executed_complete_conv :
    forall (sitpn : Sitpn)
           (fired : list Trans)
           (f : IFunction),
      (forall t : Trans,
          ~In t fired \/ (has_function sitpn t f) = false) ->
      is_executed sitpn fired f = false.
  Proof.
    intros sitpn fired f;
      functional induction (is_executed sitpn fired f)
                 using is_executed_ind;
      intros Hnfired_or_unassoc.

    (* BASE CASE. *)
    - reflexivity.

    (* CASE, test is true then contradiction. *)
    - assert (Hin_hd: In t (t :: tl)) by apply in_eq.
      specialize (Hnfired_or_unassoc t).

      (* Two cases, t ∉ fired or F(t, f) = 0. *)
      inversion_clear Hnfired_or_unassoc as [Hnfired_t | Hf_unassoc].

      (* Case t ∉ fired. *)
      + contradiction.

      (* Case F(t, f) = 0. *)
      + rewrite e0 in Hf_unassoc;
          inversion Hf_unassoc.

    (* INDUCTION CASE. *)
    - apply IHb.
      intros tr.
      specialize (Hnfired_or_unassoc tr).
      inversion_clear Hnfired_or_unassoc as [Hnfired_tr | Hf_unassoc];
        [ rewrite not_in_cons in Hnfired_tr;
          apply proj2 in Hnfired_tr;
          left;
          assumption
        | right; assumption
        ].
  Qed.
  
  (** If function [f] ∈ [functions] is only associated to unfired transitions
      then [(f, false)] is in the list returned by
      [get_function_states]. *)
  
  Lemma get_function_states_cons_conv :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (functions : list IFunction)
           (f_states : list (IFunction * bool))
           (f : IFunction),
      In f functions ->
      (forall t : Trans,
          ~In t (fired s) \/ (has_function sitpn t f) = false) ->
      In (f, false) (get_function_states sitpn s functions f_states).
  Proof.
    intros sitpn s functions f_states;
      functional induction (get_function_states sitpn s functions f_states);
      intros function Hin_f_functions Hnfired_or_unassoc.

    (* BASE CASE. *)
    - inversion Hin_f_functions.

    (* INDUCTION CASE. *)
    - (* Two cases, f = function or function ∈ tl. *)
      inversion_clear Hin_f_functions as [Heq_ff | Hin_fun_tl].

      (* Case f = function. *)
      + (* We need to prove that is_executed sitpn (fired s) f
           returns false. *)
        specialize (is_executed_complete_conv sitpn (fired s) function Hnfired_or_unassoc) as His_exec_false.
        rewrite Heq_ff; rewrite His_exec_false.

        (* Builds In (function, false) (f_states ++ [(function, false)]) *)
        assert (Hin_fstates: In (function, false) (f_states ++ [(function, false)]))
          by (apply in_or_app; right; apply in_eq).

        (* Applies get_function_states_in_fstates. *)
        apply (get_function_states_in_fstates
                 sitpn s tl (f_states ++ [(function, false)])
                 function false Hin_fstates).
        
      (* Case In function tl *)
      + apply (IHl function Hin_fun_tl Hnfired_or_unassoc).
  Qed.  

  (** All functions that are associated only with transitions that
      have not been fired are not executed in [s'.exec_f],
      where [s'] is the SitpnState returned by
      [sitpn_rising_edge]. *)
  
  Lemma sitpn_rising_edge_not_exec_fun :
    forall (sitpn : Sitpn)
           (s : SitpnState)
           (s' : SitpnState),
      sitpn_rising_edge sitpn s = Some s' ->
      (forall (f : IFunction),
          In f sitpn.(functions) ->
          (forall t : Trans,
              ~In t (fired s) \/ (has_function sitpn t f) = false) ->
          In (f, false) s'.(exec_f)).
  Proof.
    intros sitpn s;
      functional induction (sitpn_rising_edge sitpn s)
                 using sitpn_rising_edge_ind;
      intros s' Hfun;

      (* GENERAL CASE *)
      (simpl in Hfun;
       injection Hfun as Heq_s';
       rewrite <- Heq_s';
       simpl;
       apply get_function_states_cons_conv)

      (* ERROR CASE *)
      || inversion Hfun.
  Qed.
  
End SitpnRisingEdgeNotExecFun.
