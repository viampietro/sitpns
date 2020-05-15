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

(*! ============================================================= !*)
(*! DEFINITION OF SYNCHRONOUSLY EXECUTED, GENERALIZED, EXTENDED,  !*)
(*! INTERPRETED, TIME PETRI NETS (SITPNs).                        !*)
(*! ============================================================= !*)
(*! SITPNs describe the behavior of digital components in HILECOP !*)
(*! high-level models.                                            !*)
(*! ============================================================= !*)

(*
 * ============ CODING GUIDELINES ============
 * 
 * - Function names, records, lemmas and theorems idents : 
 *   first letter in lower case, then snake case.
 *
 * - Logical propositions, predicates idents, or every ident that returns a Prop : 
 *   first letter in upper case, then camel case.  
 *  
 *)

Require Export Coqlib.
Require Import Setoid.

(*! ================================= !*)
(*! TYPES AND STRUCTURES DEFINITIONS. !*)
(*! ================================= !*)

(** * Basic types for Petri nets. *)

(** A place is identified by a unique index. *)

Definition Place := nat.

(** A transition is identified by a unique index. *)

Definition Trans := nat.

(** There are 4 kinds of edges : pre, post, inhib, test 
    along with "some" positive weight (default is 1 usually). *)

(** A given edge, either reaching in or coming out of a place,
    has some weight over 0 or 0 if the edge doesn't exist *)

Definition Weight := Trans -> Place -> nat.

(** ** Neighbour places for transitions. *)

(** Defines a structure associating a given transition t to its input
    and output places (see the [lneighbours] attribute in the Sitpn
    structure). *)

Structure Neighbours : Set := mk_neighbours {
                                  pre_pl : list Place;
                                  test_pl : list Place;
                                  inhib_pl : list Place;
                                  post_pl : list Place
                                }.

(** * Types for Time Petri Nets *)

(** Defines the inductive type to express positive or (positively)
    infinite values.  Useful to type the upper bound of the time
    interval in [TimeInterval]. *)

Inductive PositiveIntervalBound : Set :=
| pos_inf : PositiveIntervalBound
| pos_val : nat -> PositiveIntervalBound.

(** Defines the time interval structure associated with transitions. *)

Structure TimeInterval : Set :=
  mk_TimeItval {
      min_t : nat;
      max_t : PositiveIntervalBound;
    }.

(** Defines the dynamic time interval type. 
    
    Differentiate the behavior of static and dynamic time
    intervals as in the STPN semantics.

    A dynamic time interval is either active or blocked. *)

Inductive DynamicTimeInterval : Set :=
| active : TimeInterval -> DynamicTimeInterval
| blocked : DynamicTimeInterval.

(** * Types for Interpreted Petri nets. *)

(** Defines condition, action and function types.

    Conditions, actions and functions are represented as natural
    numbers.

    The boolean value of conditions at a discrete time is given by a
    function that is external to the structure of SITPNs. This
    function represents the information coming to the digital system,
    which behavior is modeled with an SITPN, through sensors. *)

Definition Condition := nat.

Definition Action := nat.

(** IFunction for Interpretation Functions. 
    Function is a reserved keyword in Coq. *)

Definition IFunction := nat.

(** * Sitpn structure *)

(** Defines the Sitpn structure. *)

Structure Sitpn : Set :=
  mk_Sitpn {

      (* The set of places. *)
      places : list Place;

      (* The set of transitions. *)
      transs : list Trans;

      (* The function associating a weight to place-transition edges
         that are not inhibitor or test edges. *)
      pre : Weight;

      (* The function associating a weight to test edges. *)
      test : Weight;

      (* The function associating a weight to inhibitor edges. *)
      inhib : Weight;

      (* The function associating a weight to transition-place edges. *)
      post : Weight;

      (* The initial marking of the SITPN. *)
      initial_marking : Place -> nat;

      (* Each list of transitions contained in priority_groups is 
       * a priority-ordered list of transitions.
       *
       * Defines priority relation between transitions,
       * necessary to obtain a deterministic Petri net. *)
      priority_groups : list (list Trans);

      (* Associates a static time interval to certain transitions 
       * of the SITPN.
       *
       * For a given sitpn : Sitpn, and a transition t : Trans, 
       * sitpn.(s_intervals) t = None if no time interval
       * is associated with t in sitpn. *)
      s_intervals : Trans -> option TimeInterval;

      (* The set of conditions. *)
      conditions : list Condition;

      (* The set of actions. *)
      actions : list Action;

      (* The set of functions. *)
      functions : list IFunction;

      (* The function associating conditions to transitions. *)
      has_condition : Trans -> Condition -> bool;

      (* The function associating actions to places. *)
      has_action : Place -> Action -> bool;

      (* The function associating interpretation functions to
         transitions. *)
      has_function : Trans -> IFunction -> bool;
                     
      (* Contains the list of neighbour places associated with each
         transition. *)
      lneighbours : Trans -> Neighbours;
      
    }.

(** * Properties on the Sitpn structure. *)

(** ** Properties on [places] and [transs] *)

Definition NoDupPlaces (sitpn : Sitpn) := NoDup sitpn.(places).  
Definition NoDupTranss (sitpn : Sitpn) := NoDup sitpn.(transs).

(** ** Properties on [priority_groups] *)

(** For all transition t, t is in [sitpn.(transs)] iff 
    there exists a group in [sitpn.(priority_groups)] containing t. *)

Definition NoUnknownInPriorityGroups (sitpn : Sitpn) :=
  Permutation sitpn.(transs) (concat sitpn.(priority_groups)).

(** All transitions are contained in only one priority group. *)

Definition NoIntersectInPriorityGroups (sitpn : Sitpn) :=
  NoDup (concat sitpn.(priority_groups)).

(** ** Properties on [s_intervals] *)

(** Predicate telling if a given [itval] is well-formed according to
    HILECOP standard.
    
    A itval is well-formed if its lower bound is greater than 0 and
    less than or equal to its upper bound. 

    This predicate doesn't stand for DynamicTimeInterval,
    as in dynamic time intervals, bounds can take zero as value.
 *)

Definition IsWellFormedTimeInterval (opt_itval : option TimeInterval) :=
  match opt_itval with
  | None => True
  | Some (mk_TimeItval min_t max_t) =>
    (* Checks min_t and max_t structure. *)
    match min_t, max_t with
    (* If min_t equals O then itval is ill-formed. *)
    | O, _ => False
    (* If max_t is infinite then itval is well-formed. *)
    | _, pos_inf => True
    (* Else if max_t has a finite positive value, then 
     * checks that it is greater than or equal to min_t. *)
    | _, pos_val max_val => min_t <= max_val
    end
  end.

(** All intervals in [Sitpn.(s_intervals)] are well-formed. *)

Definition AreWellFormedTimeIntervals (sitpn : Sitpn) :=
  forall (t : Trans),
    In t sitpn.(transs) -> IsWellFormedTimeInterval (s_intervals sitpn t).

(** ** Properties on [conditions], [actions] and [functions]. *)

Definition NoDupConditions (sitpn : Sitpn) := NoDup sitpn.(conditions).
Definition NoDupActions (sitpn : Sitpn) := NoDup sitpn.(actions).
Definition NoDupFunctions (sitpn : Sitpn) := NoDup sitpn.(functions).

(** ** Properties on [lneighbours]. *)

(** Returns the concatenation of all list of places contained in neighb. 
    
    Useful for [NoIsolatedPlace] sitpn's property. *)

Definition flatten_neighbours (neighb : Neighbours) : list Place :=
  neighb.(pre_pl) ++ neighb.(test_pl) ++ neighb.(inhib_pl) ++ neighb.(post_pl).

(** Returns the list of all places referenced as neighbour places 
    of transitions in the [transs] list.
    A same place can possibly appear multiple times in the
    resulting list.            
    
    Useful for NoIsolatedPlace sitpn's property. *)

Fixpoint flatten_lneighbours (sitpn : Sitpn) (transs : list Trans) :
  list Place :=
  match transs with
  | t :: tl => (flatten_neighbours (lneighbours sitpn t)) ++ (flatten_lneighbours sitpn tl)
  | [] => []
  end.

Functional Scheme flatten_lneighbours_ind := Induction for flatten_lneighbours Sort Prop.

(** No duplicates in pre places (including test and inhib) and
    post places in the neighbourhood of transitions.
 
    Forbid the fact that a place p is linked to a transition t
    by multiple edges. 
    
    Exception is the cycle: t is linked to p by one pre, 
    test or inhib edge and one post edge. *)

Definition NoDupInNeighbours (sitpn : Sitpn) :=
  forall (t : Trans),
    In t sitpn.(transs) ->
    NoDup ((pre_pl (lneighbours sitpn t))
             ++ (test_pl (lneighbours sitpn t))
             ++ (inhib_pl (lneighbours sitpn t))) /\
    NoDup (post_pl (lneighbours sitpn t)).

(** For all place p, p is in places iff p is in the neighbourhood 
    of at least one transition. *)

Definition NoIsolatedPlace (sitpn : Sitpn) := 
  incl sitpn.(places) (flatten_lneighbours sitpn sitpn.(transs)).

(** All places in [flatten_lneighbours sitpn.(lneighbours)] are in [sitpn.(places)]. *)

Definition NoUnknownPlaceInNeighbours (sitpn : Sitpn) :=
  incl (flatten_lneighbours sitpn sitpn.(transs)) sitpn.(places).

(** Forall neighbours_of_t in sitpn.(lneighbours), there exists one list
    of places that is not empty.  i.e. A transition has at least one
    neighbour place. *)

Definition NoIsolatedTrans (sitpn : Sitpn) :=
  forall (t : Trans),
    In t sitpn.(transs) ->
    (flatten_neighbours (lneighbours sitpn t)) <> [].

(** In the scope of a Sitpn sitpn:
    ∀ p ∈ P, ∀ t ∈ T, 
    if p is a "classic" input place of t then pre(p, t) >= 1 and
    if p is not a "classic" input place of t then pre(p, t) = 0. *)

Definition AreWellDefinedPreEdges (sitpn : Sitpn) :=
  forall (t : Trans)
         (p : Place),
    In t sitpn.(transs) ->
    (In p (pre_pl (lneighbours sitpn t)) -> (pre sitpn t p) >= 1) /\
    (~In p (pre_pl (lneighbours sitpn t)) -> (pre sitpn t p) = 0).

(** In the scope of a Sitpn sitpn:
    ∀ p ∈ P, ∀ t ∈ T, 
    if p is a "test" input place of t then test(p, t) >= 1 and
    if p is not a "test" input place of t then test(p, t) = 0. *)

Definition AreWellDefinedTestEdges (sitpn : Sitpn) :=
  forall (t : Trans)
         (p : Place),
    In t sitpn.(transs) ->
    (In p (test_pl (lneighbours sitpn t)) -> (test sitpn t p) >= 1) /\
    (~In p (test_pl (lneighbours sitpn t)) -> (test sitpn t p) = 0).

(** In the scope of a Sitpn sitpn:
    ∀ p ∈ P, ∀ t ∈ T, 
    if p is an "inhibiting" input place of t then inhib(p, t) >= 1 and
    if p is not an "inhibiting" input place of t then inhib(p, t) = 0. *)

Definition AreWellDefinedInhibEdges (sitpn : Sitpn) :=
  forall (t : Trans)
         (p : Place),
    In t sitpn.(transs) ->
    (In p (inhib_pl (lneighbours sitpn t)) -> (inhib sitpn t p) >= 1) /\
    (~In p (inhib_pl (lneighbours sitpn t)) -> (inhib sitpn t p) = 0).

(** In the scope of a Sitpn sitpn:
    ∀ p ∈ P, ∀ t ∈ T, 
    if p is an output place of t then post(p, t) >= 1 and
    if p is not an output place of t then post(p, t) = 0. *)

Definition AreWellDefinedPostEdges (sitpn : Sitpn) :=
  forall (t : Trans)
         (p : Place),
    In t sitpn.(transs) ->
    (In p (post_pl (lneighbours sitpn t)) -> (post sitpn t p) >= 1) /\
    (~In p (post_pl (lneighbours sitpn t)) -> (post sitpn t p) = 0).

(** Predicate of well-definition for an SITPN. *)

Definition IsWellDefinedSitpn (sitpn : Sitpn) :=
  NoDupPlaces sitpn /\
  NoDupTranss sitpn /\
  NoUnknownInPriorityGroups sitpn /\
  NoIntersectInPriorityGroups sitpn /\
  AreWellFormedTimeIntervals sitpn /\
  NoDupConditions sitpn /\
  NoDupActions sitpn /\
  NoDupFunctions sitpn /\
  NoDupInNeighbours sitpn /\
  NoIsolatedPlace sitpn /\
  NoUnknownPlaceInNeighbours sitpn /\
  NoIsolatedTrans sitpn /\
  AreWellDefinedPreEdges sitpn /\
  AreWellDefinedTestEdges sitpn /\
  AreWellDefinedInhibEdges sitpn /\
  AreWellDefinedPostEdges sitpn.

(** * Sitpn state structure.

      Describe the structure of an Sitpn state.
      
      An SitpnState instance has a meaning only if it is related to a
      given SITPN by the [IsWellDefinedSitpnState] relation (see
      definition below). Therefore, we express in comments properties
      of the SitpnState fields under the scope of an Sitpn instance.

      The rules defining how an Sitpn should go from one state to
      another are defined by the Sitpn semantics (see file
      SitpnSemantics.v).

      Depending on how a given Sitpn state is reached, i.e either
      after the occurence of falling edge or a rising edge of a clock
      signal, the meaning some of its fields changes. *)

Structure SitpnState :=
  mk_SitpnState {

      (* - On falling edge: the list transitions fired at the previous
           cycle.  
         - On rising edge: the list of transitions to be fired at
           this cycle. *)
      
      fired : list Trans;

      (* Current marking of the Sitpn. *)
      
      marking : list (Place * nat);

      (* Current state of time intervals. *)
      
      d_intervals : list (Trans * DynamicTimeInterval);

      (* - On falling edge: orders to reset time counters at this
           cycle.  
         - On rising edge: orders to reset time counters at the
           next cycle. *)
      
      reset : list (Trans * bool);

      (* Current condition (boolean) values. *)
      
      cond_values : list (Condition * bool);

      (* Current activation state for continuous actions. *)
      
      exec_a : list (Action * bool);

      (* Current activation state for interpretation functions. *)
      
      exec_f : list (IFunction * bool);
    }.

(** Tells that a SitpnState s is a well-defined state regarding 
    the Sitpn sitpn. *)

Definition IsWellDefinedSitpnState (sitpn : Sitpn) (s : SitpnState) :=

  (* All transitions in fired must be referenced in sitpn.(transs),
     i.e: *)
  incl s.(fired) sitpn.(transs) /\
  NoDup s.(fired) /\

  (* All places in marking must be places in sitpn.(places), and
     conversely, i.e: *)
  sitpn.(places) = fst (split s.(marking)) /\
  
  (* All transitions that own a time interval in sitpn.(s_intervals)
     must be referenced in d_intervals, and conversely, i.e: *)
  (forall (t : Trans),
      In t sitpn.(transs) /\ (s_intervals sitpn t) <> None <->
      In t (fst (split s.(d_intervals)))) /\

  (* There are no duplicates in d_intervals, i.e: *)
  NoDup (fst (split s.(d_intervals))) /\
  
  (* All transitions that own a time interval in sitpn.(s_intervals)
     must be referenced in reset, and conversely, i.e: *)
  (forall (t : Trans),
      In t sitpn.(transs) /\ (s_intervals sitpn t) <> None <->
      In t (fst (split s.(reset)))) /\

  (* There are no duplicates in reset, i.e: *)
  NoDup (fst (split s.(reset))) /\
  
  (* All conditions in cond_values must be in sitpn.(conditions), and
     conversely, i.e: *)
  sitpn.(conditions) = fst (split s.(cond_values)) /\

  (* All actions in exec_a must be in sitpn.(actions), and
     conversely, i.e: *)
  sitpn.(actions) = fst (split s.(exec_a)) /\

  (* All functions in exec_f must be in sitpn.(functions), and
     conversely, i.e: *)
  sitpn.(functions) = fst (split s.(exec_f)).

(** *** Equality between SitpnState. *)

(** Equality relation between two SitpnState. *)

Definition sitpn_state_eq (s s' : SitpnState) : Prop :=
  Permutation (marking s) (marking s') /\
  Permutation (fired s) (fired s') /\
  Permutation (d_intervals s) (d_intervals s') /\
  Permutation (reset s) (reset s') /\
  Permutation (cond_values s) (cond_values s') /\
  Permutation (exec_a s) (exec_a s') /\
  Permutation (exec_f s) (exec_f s').

(** Lemmas necessary to declare sitpn_state_eq as  
    a parametric relation. *)

Lemma sitpn_state_eq_refl :
  forall (s : SitpnState), sitpn_state_eq s s.
Proof.
  intros s; unfold sitpn_state_eq; repeat (split; auto).
Qed.

Lemma sitpn_state_eq_sym :
  forall (s s' : SitpnState),
    sitpn_state_eq s s' -> sitpn_state_eq s' s.
Proof.
  intros s s' Heq_ss'.
  unfold sitpn_state_eq in *.
  decompose [and] Heq_ss'.
  let rec decide_conj :=
      (symmetry; assumption) || (split; [symmetry; assumption | decide_conj])
  in decide_conj.
Qed.

Lemma sitpn_state_eq_trans :
  forall (s s' s'' : SitpnState),
    sitpn_state_eq s s' -> sitpn_state_eq s' s'' -> sitpn_state_eq s s''.
Proof.
  intros s s' s'' Heq_ss' Heq_sp_ss.
  unfold sitpn_state_eq in *.

  elim Heq_ss'; clear Heq_ss'; intros Hperm_m Heq_ss'.
  elim Heq_ss'; clear Heq_ss'; intros Hperm_f Heq_ss'.
  elim Heq_ss'; clear Heq_ss'; intros Hperm_ditval Heq_ss'.
  elim Heq_ss'; clear Heq_ss'; intros Hperm_reset Heq_ss'.
  elim Heq_ss'; clear Heq_ss'; intros Hperm_condv Heq_ss'.
  elim Heq_ss'; clear Heq_ss'; intros Hperm_execa Heq_ss'.
  rename Heq_ss' into Hperm_execf.

  elim Heq_sp_ss; clear Heq_sp_ss; intros Hperm_m' Heq_sp_ss.
  elim Heq_sp_ss; clear Heq_sp_ss; intros Hperm_f' Heq_sp_ss.
  elim Heq_sp_ss; clear Heq_sp_ss; intros Hperm_ditval' Heq_sp_ss.
  elim Heq_sp_ss; clear Heq_sp_ss; intros Hperm_reset' Heq_sp_ss.
  elim Heq_sp_ss; clear Heq_sp_ss; intros Hperm_condv' Heq_sp_ss.
  elim Heq_sp_ss; clear Heq_sp_ss; intros Hperm_execa' Heq_sp_ss.
  rename Heq_sp_ss into Hperm_execf'.
  repeat split;
  
  (
    apply (Permutation_trans Hperm_m Hperm_m')
    ||
    apply (Permutation_trans Hperm_f Hperm_f')
    ||
    apply (Permutation_trans Hperm_ditval Hperm_ditval')
    ||
    apply (Permutation_trans Hperm_reset Hperm_reset')
    ||
    apply (Permutation_trans Hperm_condv Hperm_condv')
    ||
    apply (Permutation_trans Hperm_execa Hperm_execa')
    ||
    apply (Permutation_trans Hperm_execf Hperm_execf')
  ).
Qed.

(** Declares sitpn_state_eq as a parametric relation. *)

Add Parametric Relation : (SitpnState) (sitpn_state_eq)
    reflexivity proved by (sitpn_state_eq_refl)
    symmetry proved by (sitpn_state_eq_sym)
    transitivity proved by (sitpn_state_eq_trans)
      as sitpn_state_eq_rel.
