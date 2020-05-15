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

(*! =============================== !*)
(*! ======= SITPN SEMANTICS ======= !*)
(*! =============================== !*)

Require Export ListsPlus.
Require Import simpl.Sitpn.

(** * General preliminary definitions.  *)

(** Defines a priority relation between a transition t and t', where t
    has a higher priority than t', i.e: ∀ t ∈ T, t' ∈ T/{t}, t ≻ t' *)

Definition HasHigherPriority
           (t t' : Trans)
           (pgroup : list Trans) :=
  In t pgroup /\
  In t' pgroup /\
  IsPredInNoDupList t t' pgroup.

(** Defines [pr] as the set (therefore, with no duplicates) of
    transitions that are in the [fired] list and have a higher
    priority than transition [t] in [pgroup]. *)

Definition IsPrioritySet
           (fired pgroup : list Trans)
           (t : Trans)
           (pr : list Trans) :=
  NoDup pr /\
  (forall t' : Trans,
      HasHigherPriority t' t pgroup /\ In t' fired <-> In t' pr).

(** * Functions for marking update and facts. *)

(** Sums edge weight from place p to transitions of the l list. *)

Fixpoint pre_sum (sitpn : Sitpn) (p : Place) (l : list Trans) {struct l} : nat :=
  match l with
  | t :: tail => (pre sitpn t p) + pre_sum sitpn p tail
  | [] => 0
  end.

Functional Scheme pre_sum_ind := Induction for pre_sum Sort Prop.

(** pre_sum sitpn p l + pre_sum sitpn p [t] = pres_um sitpn p (l ++ [t]) *)

Lemma pre_sum_app_add :
  forall (sitpn : Sitpn) (p : Place) (l : list Trans) (t : Trans),
    pre_sum sitpn p l + pre_sum sitpn p [t] = pre_sum sitpn p (l ++ [t]).
Proof.
  intros sitpn p l; functional induction (pre_sum sitpn p l) using pre_sum_ind; intro t'.
  - simpl; reflexivity.
  - simpl; rewrite <- (IHn t'); simpl; rewrite plus_assoc_reverse; reflexivity.
Qed.

(** Sums edge weight from transitions of the l list to place p. *)

Fixpoint post_sum (sitpn : Sitpn) (p : Place) (l : list Trans) {struct l} : nat :=
  match l with
  | t :: tail => (post sitpn t p) + post_sum sitpn p tail
  | [] => 0
  end.

Functional Scheme post_sum_ind := Induction for post_sum Sort Prop.

(** Marking m and m' apply to the same set of places. *)

Definition MarkingHaveSameStruct (m m' : list (Place * nat)) :=
  fst (split m) = fst (split m').

(** * Sensitization definition. *)

(** ∀ t ∈ T, marking m, t ∈ sens(m) if
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ 
             m(p) ≥ Pre_t(p, t) ∧ 
             (m(p) < Pre_i(p, t) ∨ Pre_i(p, t) = 0) *)

Definition IsSensitized
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans) : Prop :=
  forall (p : Place)
         (n : nat),
    In (p, n) marking ->
    (pre sitpn t p) <= n  /\
    (test sitpn t p) <= n  /\
    (n < (inhib sitpn t p) \/ (inhib sitpn t p) = 0).

(** * Predicates for Time Petri nets semantics. *)

(** Tests if [t] is associated in [d_intervals] with is an active time
    interval with [min_t] = 0 (≡ 0 ∈ I) or if t has no static time
    interval in sitpn. *)

Definition HasEnteredTimeWindow
           (sitpn : Sitpn)
           (d_intervals : list (Trans * DynamicTimeInterval))
           (t : Trans) :=
  s_intervals sitpn t = None \/
  exists (upper_bound : PositiveIntervalBound),
    In (t, active {| min_t := 0; max_t := upper_bound |}) d_intervals.

(** Tests if the upper bound of a time interval equals 0. 
    Useful when determining if a dynamic time interval 
    should be blocked. *)

Definition HasReachedUpperBound (dyn_itval : DynamicTimeInterval) :=
  dyn_itval = active {| min_t := 0; max_t := pos_val 0 |} \/ dyn_itval = blocked.

(** Decrements the bounds of a time interval. *)

Definition dec_itval (itval : TimeInterval) :=
  match itval with
  | {| min_t := n; max_t := pos_val m |} =>
    {| min_t := n - 1; max_t := pos_val (m - 1) |}
  | {| min_t := n; max_t := pos_inf |} =>
    {| min_t := n - 1; max_t := pos_inf |}
  end.

(** * Predicates for Interpreted Petri nets semantics. *)

(** Tests if transition [t] is only associated with conditions
    evaluated to true in [cond_values]. *)

Definition HasReachedAllConditions
           (sitpn : Sitpn)
           (cond_values : list (Condition * bool))
           (t : Trans) :=
  forall (c : Condition),
    In c sitpn.(conditions) ->
    (has_condition sitpn t c) = true ->
    In (c, true) cond_values.

(** * Firability definition. *)

(** Expresses the firability of transition t at state s of SITPN
    sitpn.
    
    [t] is firable at state [s] of SITPN [sitpn] if m sensitizes [t], [t]
    has entered a specific time window, and all conditions associated to
    [t] are true, i.e: 

    ∀ t ∈ T, s = (Fired, M, cond, ex, I, reset), t ∈ firable(s) if 
    t ∈ sens(M) ∧ 0 ∈ I(t) ∧ (∀ c ∈ conditions, C(t, c) = 1 ⇒ cond(c) = 1). *)

Definition SitpnIsFirable
           (sitpn : Sitpn)
           (s : SitpnState)
           (t : Trans) :=
  IsSensitized sitpn s.(marking) t /\
  HasEnteredTimeWindow sitpn s.(d_intervals) t /\
  HasReachedAllConditions sitpn s.(cond_values) t.

(** * Sitpn Semantics definition.
    
      Inductive structure describing the rules regulating the
      evolution of a SITPN.

      Here, a given SITPN [sitpn] is moving from state [s] to state
      [s'] at a certain [time_value] (discrete time value
      corresponding to the count of clock cycles since the beginning).
      
      The [env] function gives the boolean value of conditions through
      time. It simulates the information coming from the environment
      of the SITPN.
      
      An instance of [Clock] parameterized the inductive structure,
      telling if the state changing is due to the occurence of a
      rising or a falling edge of a clock signal.  *)

(** Represents the two clock events regulating the Sitpn evolution. *)

Inductive Clock : Set :=
| falling_edge : Clock
| rising_edge : Clock.

(** Represents the Sitpn semantics. *)

Inductive SitpnSemantics
          (sitpn : Sitpn)
          (s s' : SitpnState)
          (time_value : nat)
          (env : Condition -> nat -> bool) : Clock -> Prop :=

(* ↓clock : s = (Fired, m, cond, ex, I, reset) ⇝ s' = (Fired', m, cond', ex', I', reset) *)
  
| SitpnSemantics_falling_edge :

    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->

    (* Marking stays the same between state s and s'. *)
    s.(marking) = s'.(marking) ->

    (* Function execution orders stay the same between s and s'. *)
    s.(exec_f) = s'.(exec_f) ->
    
    (* Conditions values in s' receive new values from the
       environment, i.e: 

       ∀ c ∈ conditions, cond'(c) = env(c). *)
    
    (forall (c : Condition),
        In c sitpn.(conditions) ->
        In (c, (env c time_value)) s'.(cond_values)) ->
    
    (* Actions associated to places with a non-zero marking are
       activated, i.e: 
       
       ∀ a ∈ actions, ∃ p ∈ P, m(p) > 0 ∧ A(p, a) = 1 ⇒ ex'(a) = 1. *)
    
    (forall (a : Action),
        In a sitpn.(actions) ->
        (exists (p : Place) (n : nat),
            In (p, n) s.(marking) /\ n > 0 /\ (has_action sitpn p a) = true) ->
        In (a, true) s'.(exec_a)) ->
    
    (* Actions only associated with unmarked places (no tokens) 
       are deactivated, i.e: 
       
       ∀ a ∈ actions, ∀ p ∈ P, m(p) = 0 ∨ A(p, a) = 0 ⇒ ex'(a) = 0. *)

    (forall (a : Action),
        In a sitpn.(actions) ->
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) -> n = 0 \/ (has_action sitpn p a) = false) ->
        In (a, false) s'.(exec_a)) ->
                   
    (* Time intervals are reset for all transitions sensitized by m
       and that received a reset order or were previously fired, i.e:
      
       ∀ t ∈ Ti, t ∉ sens(m) ∨ (t ∈ sens(m) ∧ (reset(t) = 1 ∨ t ∈ Fired)) ⇒ 
       I'(t) = Is(t) - 1 
       where Ti = { ti | I(ti) ≠ ∅ } *)
    
    (forall (t : Trans)
            (itval : TimeInterval),
        In t (fst (split s.(d_intervals))) ->
        (~IsSensitized sitpn s.(marking) t \/
         (IsSensitized sitpn s.(marking) t /\ (In (t, true) s.(reset) \/ In t s.(fired)))) ->
        Some itval = (s_intervals sitpn t) ->
        In (t, active (dec_itval itval)) s'.(d_intervals)) ->

    (* Time intervals evolve normally for all transitions sensitized
       by m, having an active time interval, that didn't receive a reset
       order and were not fired at the last clock cycle, i.e:
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ reset(t) = 0 ∧ t ∉ Fired ∧ I(t) ≠ ψ ⇒
       I'(t) = I(t) - 1 *)

    (forall (t : Trans)
            (itval : TimeInterval),
        In (t, active itval) s.(d_intervals) ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, active (dec_itval itval)) s'.(d_intervals)) ->
    
    (* Time intervals stay the same for all transitions with a blocked
       time interval that are sensitized by m, didn't receive a reset
       order and were not fired at the last clock cycle, i.e:
      
       ∀ t ∈ Ti, t ∈ sens(m) ∧ reset(t) = 0 ∧ t ∉ Fired ∧ I(t) = ψ ⇒
       I'(t) = I(t) *)

    (forall (t : Trans),
        In (t, blocked) s.(d_intervals) ->
        IsSensitized sitpn s.(marking) t ->
        In (t, false) s.(reset) ->
        ~In t s.(fired) ->
        In (t, blocked) s'.(d_intervals)) ->

    (* Reset orders stay the same. *)
    
    s.(reset) = s'.(reset) ->
    
    (* All transitions that are not firable are not fired, i.e:

       ∀ t ∉ firable(s') ⇒ t ∉ Fired' *)
    
    (forall (pgroup : list Trans)
            (t : Trans),
        In pgroup sitpn.(priority_groups) ->
        In t pgroup ->
        ~SitpnIsFirable sitpn s' t ->
        ~In t s'.(fired)) ->

    (* If t is firable and sensitized by the residual marking, result
       of the firing of all higher priority transitions, then t is
       fired, i.e: 

       ∀ t ∈ firable(s'), t ∈ sens(M - ∑ pre(t'), ∀ t'∈ Pr(t)) ⇒ t ∈ Fired' 
       where Pr(t) = {ti | ti ≻ t /\ ti ∈ Fired'} *)
    
    (forall (pgroup : list Trans)
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
        In t s'.(fired)) ->
    
    (* If t is firable and not sensitized by the residual marking then
       t is not fired, i.e:

       ∀ t ∈ firable(s'), t ∉ sens(M - ∑ pre(t'), ∀ t' ∈ Pr(t)) ⇒ t ∉
       Fired' *)
    
    (forall (pgroup : list Trans)
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
        ~In t s'.(fired)) ->

    SitpnSemantics sitpn s s' time_value env falling_edge
    
(* ↑clock : s = (Fired, m, cond, ex, I, reset) ⇝ s' = (Fired, m', cond, ex', I', reset') *)
                  
| SitpnSemantics_rising_edge :

    IsWellDefinedSitpn sitpn ->
    IsWellDefinedSitpnState sitpn s ->
    IsWellDefinedSitpnState sitpn s' ->
    
    (* Fired stays the same between state s and s'. *)
    s.(fired) = s'.(fired) ->
    
    (* M' = M - ∑ (pre(t_i) - post(t_i)), ∀ t_i ∈ Fired *)
    (forall (p : Place)
            (n : nat),
        In (p, n) s.(marking) ->
        In (p, n - (pre_sum sitpn p s.(fired)) + (post_sum sitpn p s.(fired)))
           s'.(marking)) ->

    (* All transitions disabled by the transient marking, result of
       the withdrawal of tokens in the input places of the fired
       transitions, receive a reset order, i.e: 
     
       ∀ t ∈ Ti, t ∉ sens(m - ∑ pre(ti), ∀ ti ∈ Fired) ⇒ reset'(t) = 1 *)

    (forall (t : Trans)
            (transient_marking : list (Place * nat)),
        Permutation (places sitpn) (fs transient_marking) ->
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum sitpn p s.(fired)) transient_marking) ->
        In t sitpn.(transs) ->
        s_intervals sitpn t <> None ->
        ~IsSensitized sitpn transient_marking t ->
        In (t, true) s'.(reset)) ->

    (* All transitions enabled by the transient marking receive no
       reset order, i.e: 

       ∀ t ∈ Ti, t ∈ sens(m - ∑ pre(ti), ∀ ti ∈ Fired) ⇒ reset'(t) = 0 *)

    (forall (t : Trans)
            (transient_marking : list (Place * nat)),
        Permutation (places sitpn) (fs transient_marking) ->
        (forall (p : Place) (n : nat),
            In (p, n) s.(marking) ->
            In (p, n - pre_sum sitpn p s.(fired)) transient_marking) ->
        In t sitpn.(transs) ->
        s_intervals sitpn t <> None ->
        IsSensitized sitpn transient_marking t ->
        In (t, false) s'.(reset)) ->

    (* Time intervals are blocked for all transitions that have
       reached the upper bound of their time intervals and were not
       fired at this clock cycle, i.e:  
     
       ∀ t ∈ Ti, ↑I(t) = 0 ∧ t ∉ Fired ⇒ I'(t) = ψ *)
    
    (forall (t : Trans)
            (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) s.(d_intervals) ->
        HasReachedUpperBound dyn_itval ->
        ~In t s.(fired) ->
        In (t, blocked) s'.(d_intervals)) ->

    (* Time intervals stay the same for all transitions that haven't
       reached the upper bound of their time intervals or were
       fired at this clock cycle, i.e:  
       
       ∀ t ∈ Ti, ↑I(t) ≠ 0 ∨ t ∈ Fired ⇒ I'(t) = I(t) *)
    
    (forall (t : Trans)
            (dyn_itval : DynamicTimeInterval),
        In (t, dyn_itval) s.(d_intervals) ->
        (~HasReachedUpperBound dyn_itval \/ In t s.(fired)) ->
        In (t, dyn_itval) s'.(d_intervals)) ->

    (* Condition values stay the same. *)

    s.(cond_values) = s'.(cond_values) ->

    (* Action activation states stay the same. *)

    s.(exec_a) = s'.(exec_a) ->
    
    (* All functions associated with fired transitions are executed, i.e: 

       ∀ f ∈ functions, ∃ t ∈ Fired | F(t, f) = 1 ⇒ ex'(f) = 1. *)

    (forall (f : IFunction),
        In f sitpn.(functions) ->
        (exists (t : Trans),
            In t s.(fired) /\ (has_function sitpn t f) = true) ->
        In (f, true) s'.(exec_f)) ->

    (* All functions not associated with fired transitions are not
       executed, i.e:

       ∀ f ∈ functions, ∀ t ∈ Fired | F(t, f) = 0 ⇒ ex'(f) = 0. *)

    (forall (f : IFunction),
        In f sitpn.(functions) ->
        (forall t : Trans, ~In t s.(fired) \/ (has_function sitpn t f) = false) ->
        In (f, false) s'.(exec_f)) ->
    
    SitpnSemantics sitpn s s' time_value env rising_edge.



