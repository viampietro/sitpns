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

(** * Types and functions used by the generateInfo function. *)

Require Import Coqlib.
Require Import dp.Sitpn.
Require Import dp.SitpnTypes.
Require Import dp.SitpnFacts.
Require Import NatSet.
Require Import ListsDep.
Require Import InfosTypes.
Require Import GlobalTypes.
Require Import String.
  
Open Scope string_scope.

(** ** Informations about places. *)

Section PlaceInfos.

  Variable sitpn : Sitpn.

  (** Returns a couple of lists [(i, o)] where [i] is the list of
      input transitions of [p], and [o] is the list of output
      transitions of [p].

      Correctness: Correct iff all input transitions of [p] are in
      [i], and [i] has no duplicate, and all output transitions of [p]
      are in [o] and [o] has no duplicate.  *)

  Definition get_neighbors_of_p (p : P sitpn) : optionE (list (T sitpn) * list (T sitpn)) :=
    (* Adds the transition t to the list of input or output
       transitions of p. *)
    let get_neighbor_of_p :=
        (fun (tin_tout : (list (T sitpn) * list (T sitpn))) t =>
           let (tin, tout) := tin_tout in
           match post t p, pre p t with
           | Some _, Some (_, _) => ((tin ++ [t])%list, (tout ++ [t])%list)
           | Some _, None => ((tin ++ [t])%list, tout)
           | None, Some (_, _) => (tin, (tout ++ [t])%list)
           | None, None => tin_tout
           end) in

    (* Iterates over the list of transitions, and builds the couple of
       lists (tinputs, touputs) of p along the way by applying
       function is_neighbor_of_p.  *)
    match tfold_left get_neighbor_of_p (T2List sitpn) (nil, nil) nat_to_T with
    | (nil, nil) => Err ("Place " ++ $$p ++ " is an isolated place.")
    | tin_tout => Success tin_tout
    end.

  (** Injects transition [t] in the list [stranss] depending on the
      level of priority of [t] compared to the elements of the list
      [stranss].
    
      Returns the new priority-sorted list where [c] has been
      injected.

      Correctness hypotheses: (1) ~In t stranss, (2) NoDup stranss,
      (3) Elements of stranss are ordered by decreasing level of
      priority.

      Correct iff the returned list has no duplicate and its elements
      are ordered by decreasing level of priority. *)

  Fixpoint inject_t (t : T sitpn) (stranss : list (T sitpn)) {struct stranss} :
    optionE (list (T sitpn)) :=
    match stranss with
    (* If the list of priority-ordered transitions is empty, then
       returns a singleton list where t is the element with the highest
       priority. *)
    | [] => Success [t]

    (* If there is a head element, compares the head element with t
     priority-wise. *)
    | x :: tl =>

      (* If t and x are the same, then t has already been injected in
       stranss, then stranss is returned. That case does not happen
       given a proof of [~In t stranss], that is, t is not among 
       the first elements of stranss.

       Otherwise, checks if t has a higher firing priority than x. *)
      if Teqdec t x then Success stranss                                     
      else
        (* If t is the element with the highest priority, then puts it
           as the head element of stranss, and returns the list.
         
         Otherwise, checks if x has a higher priority than t.  *)
        if t >~ x then Success (t :: stranss)
        else
          (* If x has a higher priority than t, then tries to inject t
           in the list's tail.  *)
          if x >~ t then
            match inject_t t tl with
            | Success stranss' => Success (x :: stranss')
            (* Error case: found a transition that is not comparable with
               t in the list's tail.
             *)
            | Err msg => Err msg
            end
          else
            (* Error case: t >~ x and x >~ t evaluate to false. *)
            Err ("Transitions " ++ $$t ++ " and " ++ $$x ++ " are not comparable with the priority relation.")
    end.

  (** Injects all transitions of the [transs] list in the list [stranss]
      that contains transitions sorted by level of firing priority.  *)

  Fixpoint sort_by_priority_aux
           (transs : list (T sitpn))
           (stranss : list (T sitpn)) {struct transs} :
    optionE (list (T sitpn)) :=
    match transs with
    | [] => Success stranss
    | t :: tl => match inject_t t stranss with
                 | Success stranss' =>
                   sort_by_priority_aux tl stranss'
                 | Err msg => Err msg
                 end
    end.

  (** Takes a list of transitions [transs], and returns a new list of
      transitions where the elements are ordered by level of firing
      priority.

      Raises an error if no strict total ordering can be established
      in relation to the priority order.  *)

  Definition sort_by_priority (transs : list (T sitpn)) :
    optionE (list (T sitpn)) := sort_by_priority_aux transs [].

  (** Returns a PlaceInfo structure containing the information related
      to place [p], a place of [sitpn].

      Error cases :
      
      - p is an isolated place, i.e it doesn't have neither input nor
        output transitions.

      - the priority relation is not a strict total order over the
        output transitions of t. 
   *)

  Definition get_p_info (p : P sitpn) : optionE (P sitpn * PlaceInfo sitpn) :=

    (* Gets the input and output transitions list of place p. *)
    match get_neighbors_of_p p with
    (* Error case: p is an isolated place. *)
    | Err msg => Err msg
    | Success (tin, tout) =>
      (* Sorts the output transitions of p by decreasing level of firing
         priority. *)
      match sort_by_priority tout with
      | Success stout => Success (p, MkPlaceInfo _ tin stout)
      (* Error case: the priority relation is not a strict total order
         over the output transitions of p. *)
      | Err msg => Err msg
      end
    end.

  (** Computes information for all p ∈ P, and returns the list of
      couples implementing function P → PlaceInfo. *)
  
  Definition generate_place_infos : optionE (list (P sitpn * PlaceInfo sitpn)) :=    
    topte_map get_p_info (P2List sitpn) nat_to_P.
  
End PlaceInfos.

(** ** Informations about transitions. *)

Section TransitionInfos.

  Variable sitpn : Sitpn.
  
  (** Returns the list of input places of transition [t].

    Correctness: Correct iff all input places of [p] are in the
    returned list, and the returned has no duplicates.

    Does not raise an error if the returned list is nil because it
    doesn't mean that [t] is an isolated transition; however [t] is a
    "source" transition (without input).
    
   *)

  Definition get_inputs_of_t (t : T sitpn) : list (P sitpn) :=    
    (* Tests if a place is an input of t. *)
    let is_input_of_t := (fun p => if (pre p t) then true else false) in
    tfilter is_input_of_t (P2List sitpn) nat_to_P.

  (** Returns the list of conditions associated to transition [t].
    
    Correctness: Correct iff all conditions associated to [t] are in the
    returned list, and the returned has no duplicates.  *)

  Definition get_conds_of_t (t : T sitpn) : list (C sitpn) :=
    (* Tests if a condition is associated to t. *)
    let is_cond_of_t := (fun c => (match has_C t c with one | mone => true | zero => false end)) in
    tfilter is_cond_of_t (C2List sitpn) nat_to_C.

  (** Computes the information about transition t, and returns
    a couple [(t, info)].
   *)

  Definition get_t_info (t : T sitpn) : (T sitpn * TransInfo sitpn) :=
    (t, MkTransInfo _ (get_inputs_of_t t) (get_conds_of_t t)).

  (** Maps the function [get_t_info] to the list of transitions of [sitpn],
      and returns the resulting list of couples [(t, info)]. *)

  Definition generate_trans_infos : list (T sitpn * TransInfo sitpn) :=
    tmap get_t_info (T2List sitpn) nat_to_T.
  
End TransitionInfos.

Arguments generate_trans_infos {sitpn}.

(** ** Informations about conditions, actions and functions. *)

Section InterpretationInfos.

  Variable sitpn : Sitpn.
  
  (** Returns the list of transitions associated to condition [c]. *)

  Definition get_transs_of_c (c : C sitpn) : list (T sitpn) :=
    let is_trans_of_c := (fun t => (match has_C t c with one | mone => true | zero => false end)) in
    tfilter is_trans_of_c (T2List sitpn) nat_to_T.

  (** Returns the list of transitions associated to function [f]. *)

  Definition get_transs_of_f (f : F sitpn) : list (T sitpn) :=
    tfilter (fun t => has_F t f) (T2List sitpn) nat_to_T.

  (** Returns the list of places associated to action [a]. *)

  Definition get_places_of_a (a : A sitpn) : list (P sitpn) :=
    tfilter (fun p => has_A p a) (P2List sitpn) nat_to_P.

  (** Maps the function [get_transs_of_c] to the list of conditions of
      [sitpn]. Returns the resulting list of couples [(c, transs_of_c)]. *)
  
  Definition generate_cond_infos : list (C sitpn * list (T sitpn)) :=
    tmap (fun c => (c, get_transs_of_c c)) (C2List sitpn) nat_to_C.

  (** Maps the function [get_transs_of_f] to the list of functions of
      [sitpn]. Returns the resulting list of couples [(f, transs_of_f)]. *)
  
  Definition generate_fun_infos : list (F sitpn * list (T sitpn)) :=
    tmap (fun f => (f, get_transs_of_f f)) (F2List sitpn) nat_to_F.

  (** Maps the function [get_places_of_a] to the list of actions of
      [sitpn]. Returns the resulting list of couples [(a, places_of_a)]. *)
  
  Definition generate_action_infos : list (A sitpn * list (P sitpn)) :=
    tmap (fun a => (a, get_places_of_a a)) (A2List sitpn) nat_to_A.
  
End InterpretationInfos.

Arguments generate_cond_infos {sitpn}.
Arguments generate_action_infos {sitpn}.
Arguments generate_fun_infos {sitpn}.

(** ** Informations about an Sitpn. *)

Section SitpnInfos.

  Variable sitpn : Sitpn.

  (** Returns an SitpnInfo instance computed from [sitpn]. *)
  
  Definition generate_sitpn_infos : optionE (SitpnInfo sitpn) :=
    (* Raises an error if sitpn has an empty set of places or transitions. *)
    if NatSet.is_empty (places sitpn) then
      Err "Found an empty set of places."
    else
      if NatSet.is_empty (transitions sitpn) then
        Err "Found an empty set of transitions."
      else
        (* Otherwise, generates information about sitpn. *)
        match generate_place_infos sitpn with
        | Success pinfos =>
          let tinfos := generate_trans_infos in
          let cinfos := generate_cond_infos in
          let ainfos := generate_action_infos in
          let finfos := generate_fun_infos in
          Success (MkSitpnInfo _ pinfos tinfos cinfos ainfos finfos)
        (* Error case: propagates the error raised by generate_place_infos. *)
        | Err msg => Err msg
        end.
  
End SitpnInfos.

