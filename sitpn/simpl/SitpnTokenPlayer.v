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

(*! ================================== !*)
(*! ======= SITPN TOKEN PLAYER ======= !*)
(*! ================================== !*)

Require Import Coqlib.
Require Import simpl.Sitpn.
Require Import simpl.SitpnSemantics.

Set Implicit Arguments.

(** * General helper functions. *)

Section SitpnHelperFunctions.

  Variable A B : Type.

  (** Returns the value associated to key [key] in list [l],
      or error (None) if [key] is not in [l]. *)
  
  Fixpoint get_value
           (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (key : A)
           (l : list (A * B)) {struct l} : option B :=
    match l with
    | (x, value) :: tl =>
      if eq_dec x key then
        Some value
      else get_value eq_dec key tl
    (* Error, key is not in l. *)
    | [] => None
    end.

  Functional Scheme get_value_ind := Induction for get_value Sort Prop.
  
  (** Functional implementation of the [In] predicate, declared in the
      Coq Standard Library. *)

  Fixpoint in_list
           (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (l : list A)
           (a : A) {struct l} : bool :=
    match l with
    | x :: tl =>
      if eq_dec x a then
        true
      else in_list eq_dec tl a
    | [] => false
    end.

  Functional Scheme in_list_ind := Induction for in_list Sort Prop.
  
End SitpnHelperFunctions.

(** * Functions for Interpretation. *)

Section InterpretationFunctions.

  (** Returns a list of couples (condition, boolean value) denoting
      the value of conditions at time [time_value] according to the
      [env] function. *)
  
  Fixpoint get_condition_values
           (conditions : list Condition)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (cond_values : list (Condition * bool)) {struct conditions} :
    list (Condition * bool) :=
    match conditions with
    | c :: tl =>
      get_condition_values tl time_value env (cond_values ++ [(c, env c time_value)])
    | [] => cond_values
    end.

  Functional Scheme get_condition_values_ind :=
    Induction for get_condition_values Sort Prop.
  
  (** Returns true if for all conditions in [cond_values] 
      associated to t is sitpn are true. *)
  
  Fixpoint are_all_conditions_true
           (sitpn : Sitpn)
           (cond_values : list (Condition * bool))
           (t: Trans) {struct cond_values} : bool :=
    match cond_values with
    | (c, b) :: tl =>
      if has_condition sitpn t c then
        if b then
          are_all_conditions_true sitpn tl t
        else false
      else are_all_conditions_true sitpn tl t
    | [] => true
    end.

  Functional Scheme are_all_conditions_true_ind :=
    Induction for are_all_conditions_true Sort Prop.
  
  (** Returns true if there exists a place p in marking 
      with at least one token that is associated to action a
      in sitpn. *)
  
  Fixpoint is_activated
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (a : Action) {struct marking} : bool :=
    match marking with
    | (p, n) :: tl =>
      if (has_action sitpn p a) && (0 <? n) then
        true
      else
        is_activated sitpn tl a
    | [] => false
    end.

  Functional Scheme is_activated_ind := Induction for is_activated Sort Prop.

  (** Returns the list of couples (action, activated?) --where
      activated? is a boolean-- denoting the activation state of
      all actions of the actions list at state s of sitpn. *)
  
  Fixpoint get_action_states
           (sitpn : Sitpn)
           (s : SitpnState)
           (actions : list Action)
           (a_states : list (Action * bool)) {struct actions} :
    list (Action * bool) :=
  match actions with
  | a :: tl =>
    get_action_states sitpn s tl (a_states ++ [(a, is_activated sitpn s.(marking) a)])
  | [] => a_states
  end.

  Functional Scheme get_action_states_ind :=
    Induction for get_action_states Sort Prop.
  
  (** Returns true if there exists a transition [t] 
      in list [fired] that is associated to function [f]
      in [sitpn]. *)

  Fixpoint is_executed
           (sitpn : Sitpn)
           (fired : list Trans)
           (f : IFunction) {struct fired} : bool :=
  match fired with
  | t :: tl =>
    if has_function sitpn t f then
      true
    else
      is_executed sitpn tl f
  | [] => false
  end.

  Functional Scheme is_executed_ind :=
    Induction for is_executed Sort Prop.
  
  (** Returns a list (function, executed?)--where executed? is a
      boolean-- denoting the execution state of all functions of the
      [functions] list at state s of sitpn. *)

  Fixpoint get_function_states
           (sitpn : Sitpn)
           (s : SitpnState)
           (functions : list IFunction)
           (f_states : list (IFunction * bool)) {struct functions} :
    list (IFunction * bool) :=
  match functions with
  | f :: tl =>
    get_function_states sitpn s tl (f_states ++ [(f, is_executed sitpn s.(fired) f)])
  | [] => f_states
  end.

  Functional Scheme get_function_states_ind :=
    Induction for get_function_states Sort Prop.
  
End InterpretationFunctions.

(** * Sensitization functions. *)

Section Sensitization.

  (** Returns [Some true] if M(p) >= pre(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_value] fail. *)
  
  Definition check_pre
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_value eq_nat_dec p marking with
    | Some nboftokens => Some ((pre sitpn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_pre_ind := Induction for check_pre Sort Prop.

  (** Function : Returns [Some true] if ∀ p ∈ [pre_places], M(p) >= pre(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_pre_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (pre_places : list Place)
           (t : Trans)
           (check_result : bool) {struct pre_places} : option bool :=
    match pre_places with
    | p :: tail =>
      match check_pre sitpn marking p t with
      | None => None
      | Some b =>
        map_check_pre_aux sitpn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_pre_aux_ind := Induction for map_check_pre_aux Sort Prop.

  (** Wrapper around [map_check_pre_aux]. *)
  
  Definition map_check_pre
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (pre_places : list Place)
             (t : Trans) : option bool :=
    map_check_pre_aux sitpn marking pre_places t true.

  Functional Scheme map_check_pre_ind := Induction for map_check_pre Sort Prop.
  
  (** Returns [Some true] if M(p) >= test(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_test
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_value eq_nat_dec p marking with
    | Some nboftokens => Some ((test sitpn t p) <=? nboftokens)
    | None => None
    end.

  Functional Scheme check_test_ind := Induction for check_test Sort Prop.
  
  (** Function : Returns [Some true] if ∀ p ∈ [test_places], M(p) >= test(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_test_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (test_places : list Place)
           (t : Trans)
           (check_result : bool) {struct test_places} : option bool :=
    match test_places with
    | p :: tail =>
      match check_test sitpn marking p t with
      | None => None
      | Some b =>
        map_check_test_aux sitpn marking tail t (b && check_result)
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_test_aux_ind := Induction for map_check_test_aux Sort Prop.

  (** Wrapper around [map_check_test_aux]. *)
  
  Definition map_check_test
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (test_places : list Place)
             (t : Trans) : option bool :=
    map_check_test_aux sitpn marking test_places t true.

  Functional Scheme map_check_test_ind := Induction for map_check_test Sort Prop.
  
  (** Returns [Some true] if M(p) >= inhib(p, t), [Some false] otherwise. 
                 
      Raises an error (i.e. None) if [get_m] fail. *)
  
  Definition check_inhib
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (p : Place)
             (t : Trans) : option bool :=
    match get_value eq_nat_dec p marking with
    | Some nboftokens => Some ((nboftokens <? (inhib sitpn t p)) || ((inhib sitpn t p) =? 0))
    (* Error: p is not a key in marking. *)
    | None => None
    end.

  Functional Scheme check_inhib_ind := Induction for check_inhib Sort Prop.
  
  (** Function : Returns [Some true] if ∀ p ∈ [inhib_places], M(p) >= inhib(p, t).
                 
                 Raises an error if [get_m] fails. *)
  
  Fixpoint map_check_inhib_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (inhib_places : list Place)
           (t : Trans)
           (check_result : bool) {struct inhib_places} : option bool :=
    match inhib_places with
    | p :: tail =>
      match check_inhib sitpn marking p t with
      | Some b =>
        map_check_inhib_aux sitpn marking tail t (b && check_result)
      (* Error: p is not a key in marking. *)
      | None => None
      end 
    | [] => Some check_result
    end.  

  Functional Scheme map_check_inhib_aux_ind := Induction for map_check_inhib_aux Sort Prop.
  
  (** Wrapper around [map_check_inhib_aux]. *)
  
  Definition map_check_inhib
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (inhib_places : list Place)
             (t : Trans) : option bool :=
    map_check_inhib_aux sitpn marking inhib_places t true.

  Functional Scheme map_check_inhib_ind := Induction for map_check_inhib Sort Prop.

  (** Returns [Some true] if [t] is sensitized in marking [marking], 
      [Some false] otherwise. 
                 
      Raises an error if [map_check_pre], [map_check_test], [map_check_inhib] or
      [get_neighbours] fail. *)
  
  Definition is_sensitized
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (neighbours_of_t : Neighbours)
             (t : Trans) : option bool :=
    match map_check_pre sitpn marking (pre_pl neighbours_of_t) t with
    | Some check_pre_result =>  
      match map_check_test sitpn marking (test_pl neighbours_of_t) t with
      | Some check_test_result =>
        match map_check_inhib sitpn marking (inhib_pl neighbours_of_t) t with
        | Some check_inhib_result =>
          Some (check_pre_result && check_test_result && check_inhib_result)
        (* Error: some input place of t was not referenced in marking. *)
        | None => None
        end
      (* Error: some input place of t was not referenced in marking. *)
      | None => None
      end
    (* Error: some input place of t was not referenced in marking. *)
    | None => None
    end.

  Functional Scheme is_sensitized_ind := Induction for is_sensitized Sort Prop.
  
End Sensitization.

(** * Functions for Time. *)

Section TimeFunctions.

  (** Returns true if [dyn_itval] has reached its upper bound. 
      false otherwise. *)

  Definition has_reached_upper_bound (dyn_itval : DynamicTimeInterval) : bool :=
    match dyn_itval with
    | active {| min_t := 0; max_t := pos_val 0 |} | blocked => true
    | _ => false    
    end.

  (** Returns true if the dynamic time interval associated to in
      [d_intervals] has a lower bound equal to zero. 
      
      Raises an error if t is not referenced in [d_intervals]. *)
  
  Definition has_entered_time_window
             (sitpn : Sitpn)
             (d_intervals : list (Trans * DynamicTimeInterval))
             (t : Trans) : option bool :=
    (* Checks if t is associated with a time interval. *)
    match s_intervals sitpn t with
    | Some stc_itval =>
      match get_value eq_nat_dec t d_intervals with
      (* Checks if dyn_itval has a lower bound equal to 0. *)
      | Some dyn_itval =>
        match dyn_itval with
        | active {| min_t := 0; max_t := _ |} => Some true
        | _ => Some false
        end
      (* Error: t is not referenced in d_intervals. *)
      | None => None
      end
    (* If t is not associated with a time itval, then its 
       firability is not restricted to a time window. *)
    | None => Some true
    end.

  Functional Scheme has_entered_time_window_ind :=
    Induction for has_entered_time_window Sort Prop.
  
  (** Builds a new list of couples (Trans, DynamicTimeInterval) based 
      on the state of dynamic intervals in the [d_itvals] list, and
      of current state s of sitpn. *)
  
  Fixpoint update_time_intervals
           (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           {struct d_itvals} :
    option (list (Trans * DynamicTimeInterval)) :=
    match d_itvals with
    | (t, dyn_itval) :: tl =>
      (* Checks if t is associated with a static time interval in sitpn. *)
      match s_intervals sitpn t with
      (* Normal case, t is associated with a static itval. *)
      | Some stc_itval =>
        let neighbours_of_t := lneighbours sitpn t in
        (* Checks if t is sensitized by the marking at state s. *)
        match is_sensitized sitpn s.(marking) neighbours_of_t t with
        (* If t is sensitized, determines its time interval status. *)
        | Some true =>
          (* If t is in the fired list of state s then resets t's itval
           and goes on. *)
          if in_list eq_nat_dec s.(fired) t then
            let reset_itval := dec_itval stc_itval in
            update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active reset_itval)])
          (* Else looks at the reset orders given to t at state s. *)
          else
            match get_value eq_nat_dec t s.(reset) with
            (* If t received a reset order at state s, then resets t's
               itval and goes on. *)
            | Some true =>
              let reset_itval := dec_itval stc_itval in
              update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active reset_itval)])
            (* If t is not in the fired list and didn't receive a reset
               order at state s, then looks at the state of its dynamic
               interval. *)
            | Some false =>
              match dyn_itval with
              (* If the interval is active, then decrements the interval. *)
              | active itval =>
                let new_itval := dec_itval itval in
                update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active new_itval)])
              (* If dyn_itval is blocked, then it stays blocked. *)
              | blocked =>
                update_time_intervals sitpn s tl (new_d_itvals ++ [(t, blocked)])
              end
            (* Error: t is not in the reset list of state s. *)
            | None => None
            end
        (* If t is not sensitized by the current marking 
         then resets t's itval and goes on. *)
        | Some false =>
          let reset_itval := dec_itval stc_itval in
          update_time_intervals sitpn s tl (new_d_itvals ++ [(t, active reset_itval)])
        (* Error: is_sensitized raised an error. *)
        | None => None
        end
      (* Error: t is associated with a dynamic itval in d_itvals, 
         but with no static itval in sitpn. *)
      | None => None
      end
    | [] => Some new_d_itvals
    end.

  Functional Scheme update_time_intervals_ind :=
    Induction for update_time_intervals Sort Prop.
  
  (** Returns two lists build on the [d_itvals] list: 
      
      - A list of reset orders, computed for all transitions based
        on the sensitization by the transient marking.
      - A list of dynamic time intervals with newly blocked
        intervals. *)

  Fixpoint get_blocked_itvals_and_reset_orders
           (sitpn : Sitpn)
           (s : SitpnState)
           (d_itvals : list (Trans * DynamicTimeInterval))
           (transient_marking : list (Place * nat))
           (reset_orders : list (Trans * bool))
           (new_d_itvals : list (Trans * DynamicTimeInterval))
           {struct d_itvals} :
    option ((list (Trans * bool)) * (list (Trans * DynamicTimeInterval))) :=
    match d_itvals with
    | (t, dyn_itval) :: tl =>

      (* Retrieves neighbour places of t. *)
      let neighbours_of_t := lneighbours sitpn t in

      (* If t is sensitized by the transient marking, then 
         no reset order is given. *)
      match is_sensitized sitpn transient_marking neighbours_of_t t with
      | Some true =>
        let reset_orders' := reset_orders ++ [(t, false)] in

        (* If t is not a fired transition at state s, and its dynamic
           interval has reached its upper bound, then t is associated with 
           a blocked time interval in new_d_itvals'. *)
        if has_reached_upper_bound dyn_itval && negb (in_list eq_nat_dec s.(fired) t) then
          let new_d_itvals' := new_d_itvals ++ [(t, blocked)] in
          (* Recursive call. *)
          get_blocked_itvals_and_reset_orders sitpn s tl transient_marking reset_orders' new_d_itvals'
        else (* Else copies current dynamic interval. *)
          let new_d_itvals' := new_d_itvals ++ [(t, dyn_itval)] in
          (* Recursive call. *)
          get_blocked_itvals_and_reset_orders sitpn s tl transient_marking reset_orders' new_d_itvals'
                                              
      (* Else gives a reset order to t. *)
      | Some false =>
        let reset_orders' := reset_orders ++ [(t, true)] in
        
        (* If t is not a fired transition at state s, and its dynamic
           interval has reached its upper bound, then t is associated with 
           a blocked time interval in new_d_itvals'. *)
        if has_reached_upper_bound dyn_itval && negb (in_list eq_nat_dec s.(fired) t) then
          let new_d_itvals' := new_d_itvals ++ [(t, blocked)] in
          (* Recursive call. *)
          get_blocked_itvals_and_reset_orders sitpn s tl transient_marking reset_orders' new_d_itvals'
                                              (* Else copies current dynamic interval. *)
        else
          let new_d_itvals' := new_d_itvals ++ [(t, dyn_itval)] in
          (* Recursive call. *)
          get_blocked_itvals_and_reset_orders sitpn s tl transient_marking reset_orders' new_d_itvals'
                                              
      (* Error: is_sensitized raised an error. *)
      | None => None
      end
    | [] => Some (reset_orders, new_d_itvals)
    end.

  Functional Scheme get_blocked_itvals_and_reset_orders_ind :=
    Induction for get_blocked_itvals_and_reset_orders Sort Prop.
  
End TimeFunctions.

(** * Firability functions. *)

Section Firability.

  (** Returns true if transition t is firable according
      to SITPN semantics firability definition. *)
  
  Definition sitpn_is_firable
             (sitpn : Sitpn)
             (s : SitpnState)
             (neighbours_of_t : Neighbours)
             (t : Trans) : option bool :=
    (* Checks if t is sensitized by marking at state s. *)
    match is_sensitized sitpn s.(marking) neighbours_of_t t with
    | Some true =>
      (* Checks if t's time interval is ready for firing. *)
      match has_entered_time_window sitpn s.(d_intervals) t with
      | Some true =>
        (* Finlly, checks if all conditions associated to t are true. *)
        Some (are_all_conditions_true sitpn s.(cond_values) t)
      (* If time window not reached then t is not firable. *)
      | Some false => Some false
      (* Error: has_entered_time_window raised an error. *)
      | None => None
      end
    (* If t is not sensitized by marking at state s then t is not
       firable. *)
    | Some false => Some false
    (* Error: is_sensitized raised an error. *)
    | None => None
    end.

  Functional Scheme sitpn_is_firable_ind := Induction for sitpn_is_firable Sort Prop.
  
End Firability.

(** * Marking update. *)

Section Updatemarking.
  
  (** Adds/subtracts (according to [op]) [nboftokens] tokens from place [p] in
      marking [m], and returns an resulting marking [m']. 

      Raises an error if p is not referenced in marking [m]. *)

  Fixpoint modify_m
           (marking : list (Place * nat))
           (p : Place)
           (op : nat -> nat -> nat)
           (nboftokens : nat) {struct marking} :
    option (list (Place * nat)) :=
    match marking with
    | (p', n) :: tl =>      
      (* If p is a key in the head couple of marking then 
         either adds or substracts tokens according to op. *)
      if p' =? p then
        Some ((p, op n nboftokens) :: tl)
      (* Recursive call otherwise. *)
      else 
        match modify_m tl p op nboftokens with
        | Some m' => Some ((p', n) :: m')
        | None => None
        end
    | [] => None
    end.

  Functional Scheme modify_m_ind := Induction for modify_m Sort Prop.
  
  (** Removes some tokens from [pre_places], result  
      of the firing of t. 
                 
      Returns an updated marking. *)
  
  Fixpoint update_marking_pre_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (pre_places : list Place) : option (list (Place * nat)) :=
    match pre_places with
    | p :: tail =>
      match modify_m marking p Nat.sub (pre sitpn t p) with
      | Some m' => update_marking_pre_aux sitpn m' t tail
      (* Error: p is not referenced in sitpn.(marking). *)
      | None => None
      end
    | [] => Some marking
    end.

  Functional Scheme update_marking_pre_aux_ind := Induction for update_marking_pre_aux Sort Prop.
  
  (** Wrapper around [update_marking_pre_aux]. *)
  
  Definition update_marking_pre
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (neighbours_of_t : Neighbours)
             (t : Trans) : option (list (Place * nat)) :=
    update_marking_pre_aux sitpn marking t (pre_pl neighbours_of_t).

  Functional Scheme update_marking_pre_ind := Induction for update_marking_pre Sort Prop.

  (**  Applies [update_marking_pre] on every transition t ∈ fired,
       and returns the resulting marking. 
       
       Raises an error if update_marking_pre fails. *)
  
  Fixpoint map_update_marking_pre
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (fired : list Trans) {struct fired} :
    option (list (Place * nat)) :=
    match fired with
    | t :: tail =>
      (* Retrieves nieghbour places of t. *)
      let neighbours_of_t := lneighbours sitpn t in
      (* Substracts tokens from input places of t, and returns new
         marking. *)
      match update_marking_pre sitpn marking neighbours_of_t t with
      | Some m' => map_update_marking_pre sitpn m' tail
      (* Error: update_marking_pre failed. *)
      | None => None
      end
    | [] => Some marking
    end.

  Functional Scheme map_update_marking_pre_ind := Induction for map_update_marking_pre Sort Prop.

  (** Adds tokens from [post_places] (input places of t), result  
      of the firing of t. 
                 
      Returns an updated marking. *)
  
  Fixpoint update_marking_post_aux
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (t : Trans)
           (post_places : list Place) : option (list (Place * nat)) :=
    match post_places with
    | p :: tail =>
      match modify_m marking p Nat.add (post sitpn t p) with
      | Some m' => update_marking_post_aux sitpn m' t tail
      (* Error: p is not referenced in sitpn.(marking). *)
      | None => None
      end
    | [] => Some marking
    end.

  Functional Scheme update_marking_post_aux_ind := Induction for update_marking_post_aux Sort Prop.
  
  (** Wrapper around [update_marking_post_aux]. *)
  
  Definition update_marking_post
             (sitpn : Sitpn)
             (marking : list (Place * nat))
             (neighbours_of_t : Neighbours)
             (t : Trans) : option (list (Place * nat)) :=
    update_marking_post_aux sitpn marking t (post_pl neighbours_of_t).

  Functional Scheme update_marking_post_ind := Induction for update_marking_post Sort Prop.

  (**  Applies [update_marking_post] on every transition t ∈ fired,
       and returns the resulting marking. 
       
       Raises an error if update_marking_post fails. *)
  
  Fixpoint map_update_marking_post
           (sitpn : Sitpn)
           (marking : list (Place * nat))
           (fired : list Trans) {struct fired} :
    option (list (Place * nat)) :=
    match fired with
    | t :: tail =>
      (* Retrieves nieghbour places of t. *)
      let neighbours_of_t := lneighbours sitpn t in
      (* Substracts tokens from input places of t, and returns new
         marking. *)
      match update_marking_post sitpn marking neighbours_of_t t with
      | Some m' => map_update_marking_post sitpn m' tail
      (* Error: update_marking_post failed. *)
      | None => None
      end
    | [] => Some marking
    end.

  Functional Scheme map_update_marking_post_ind := Induction for map_update_marking_post Sort Prop.
  
End Updatemarking.

(** * Determining transitions to be fired. *)

Section TransitionsToBeFired.

  (** Returns the list of transitions to be fired in priority group
      [pgroup] at the state [s] of [sitpn]. *)
  
  Fixpoint sitpn_fire_aux
           (sitpn : Sitpn)
           (s : SitpnState)
           (residual_marking : list (Place * nat))
           (fired : list Trans)
           (pgroup : list Trans):
    option (list Trans) :=
    match pgroup with
    | t :: tail =>
      (* Retrieves the neighbour places of t. *)
      let neighbours_of_t := lneighbours sitpn t in
      match sitpn_is_firable sitpn s neighbours_of_t t with
      (* If t is firable, then checks if t is sensitized by residual_marking.  *)
      | Some true =>
        (* If t is sensitized by residual_marling, then, 
           updates the residual_marking, and add t to the fired transitions. *)
        match is_sensitized sitpn residual_marking neighbours_of_t t with
        | Some true =>
          match update_marking_pre sitpn residual_marking neighbours_of_t t with
          (* Recursive call with updated residual marking *)
          | Some residual_marking' =>
            sitpn_fire_aux sitpn s residual_marking' (fired ++ [t]) tail
          (* Something went wrong, error! *)
          | None => None
          end
        (* Else no changes but inductive progress. *)
        | Some false =>
          sitpn_fire_aux sitpn s residual_marking fired tail
        (* Something went wrong, error! *)
        | None => None
        end
      (* Else no changes but inductive progress. *)
      | Some false =>
        sitpn_fire_aux sitpn s residual_marking fired tail
      (* Something went wrong, error! *)
      | None => None
      end
    | []  => Some fired
    end.

  Functional Scheme sitpn_fire_aux_ind := Induction for sitpn_fire_aux Sort Prop.
  
  (* -------------------------------------------------- *)
  (* -------------------------------------------------- *)
  
  (** Wrapper function around sitpn_fire_pre_aux. *)
  
  Definition sitpn_fire
             (sitpn : Sitpn)
             (s : SitpnState)
             (pgroup : list Trans) :
    option (list Trans) :=
    sitpn_fire_aux sitpn s s.(marking) [] pgroup.

  (* -------------------------------------------------- *)
  (* -------------------------------------------------- *)
  
  (** Returns the list of transitions to be fired at state [s] of [sitpn].
               
      Applies sitpn_fire over ALL priority group of transitions. *)
  
  Fixpoint sitpn_map_fire_aux
           (sitpn : Sitpn)
           (s : SitpnState)
           (fired_transitions : list Trans)
           (priority_groups : list (list Trans)) :
    option (list Trans) :=
    match priority_groups with
    (* Loops over all priority group of transitions (pgroup) and
     * calls sitpn_fire. *)
    | pgroup :: pgroups_tail =>
      match sitpn_fire sitpn s pgroup with
      (* If sitpn_fire succeeds, then adds the fired transitions
       * in fired_transitions list. *)
      | Some fired_trs =>
        sitpn_map_fire_aux sitpn s (fired_transitions ++ fired_trs) pgroups_tail
      (* Case of error! *)
      | None => None
      end
    | [] => Some fired_transitions
    end.

  Functional Scheme sitpn_map_fire_aux_ind := Induction for sitpn_map_fire_aux Sort Prop.

  (* -------------------------------------------------- *)
  (* -------------------------------------------------- *)
  
  (** Wrapper around sitpn_map_fire_aux function. *)
  
  Definition sitpn_map_fire (sitpn : Sitpn) (s : SitpnState) :
    option (list Trans) := sitpn_map_fire_aux sitpn s [] sitpn.(priority_groups).

  Functional Scheme sitpn_map_fire_ind := Induction for sitpn_map_fire Sort Prop.
  
End TransitionsToBeFired.

(** * Falling edge state changing. *)

Section FallingEdge.

  (** Returns a new SitpnState computed from state [s] of [sitpn]
      by following the rules of state changing after the occurence of
      a falling edge event. 
      
      Raises an error (i.e, None) if one function call fails. *)
  
  Definition sitpn_falling_edge
             (sitpn : Sitpn)
             (s : SitpnState)
             (time_value : nat)
             (env : Condition -> nat -> bool) : option SitpnState :=
    (* Retrieves boolean values at the current time value for
       all conditions defined in sitpn. *)
    let cond_values' := get_condition_values (conditions sitpn) time_value env [] in
    (* Retrieves activation states for all actions defined in sitpn. *)
    let exec_a' := get_action_states sitpn s (actions sitpn) [] in
    (* Updates dynamic time intervals based on their values at state
       s, and returns a new dynamic time itvals list. *)
    match update_time_intervals sitpn s (d_intervals s) [] with
    | Some d_intervals' =>
      (* Builds a temporary state based on the results of the previous
         function calls. tmp_state has an empty list of transs to be
         fired, that's the only difference with the final state
         returned by sitpn_falling_edge. *)
      let tmp_state := mk_SitpnState
                         [] (marking s) d_intervals' (reset s)
                         cond_values' exec_a' (exec_f s) in
      (* Determines transitions to be fired from tmp_state. *)
      match sitpn_map_fire sitpn tmp_state with
      | Some trs_2b_fired =>
        (* Builds and returns the new SitpnState. *)
        Some
          (mk_SitpnState trs_2b_fired (marking tmp_state)
                         (d_intervals tmp_state) (reset tmp_state)
                         (cond_values tmp_state) (exec_a tmp_state)
                         (exec_f tmp_state))
      (* Error: something went wrong in sitpn_map_fire. *)
      | None => None
      end
    (* Error: something went wrong in update_time_intervals. *)
    | None => None
    end.

  Functional Scheme sitpn_falling_edge_ind :=
    Induction for sitpn_falling_edge Sort Prop.
  
End FallingEdge.


(** * Rising edge state changing. *)

Section RisingEdge.

  (** Returns a new SitpnState computed from state [s] of [sitpn]
      by following the rules of state changing after the occurence of
      a rising edge event. 
      
      Raises an error (i.e, None) if one function call fails. *)

  Definition sitpn_rising_edge
             (sitpn : Sitpn)
             (s : SitpnState) : option SitpnState :=
  (* Subtracts tokens from the input places of fired transitions, and
     returns the resulting transient marking. *)
    match map_update_marking_pre sitpn (marking s) (fired s) with
    | Some transient_marking =>
      (* Computes a new list of reset orders based on the transient
         marking, and determines which dynamic time intervals are
         blocked. *)
      match get_blocked_itvals_and_reset_orders sitpn s (d_intervals s) transient_marking [] [] with
      | Some (reset', d_intervals') =>
        (* Adds tokens in output places of fired transitions, and
           returns the resulting marking. *)
        match map_update_marking_post sitpn transient_marking (fired s) with
        | Some final_marking =>
          (* Retrieves function execution states, then builds and
             returns the final state. *)
          let exec_f' := get_function_states sitpn s (functions sitpn) [] in
          Some (mk_SitpnState (fired s) final_marking
                              d_intervals' reset'
                              (cond_values s) (exec_a s) exec_f')
          
        (* Error: something went wrong in map_update_marking_post. *)
        | None => None
        end
      (* Error: something went wrong in get_blocked_itvals_and_reset_orders. *)
      | None => None
      end
    (* Error: something went wrong in map_update_marking_pre. *)
    | None => None
    end.

  Functional Scheme sitpn_rising_edge_ind :=
    Induction for sitpn_rising_edge Sort Prop.
  
End RisingEdge.


Section SitpnCycle.

  (** Computes one evolution cycle for Sitpn [sitpn] starting from
      state [s].

      Returns a couple of SitpnState (s', s'') where s' is computed
      from s by applying the falling edge state changing rules, and
      s'' is computed from s' by applying the rising edge state
      changing rules. *)
  
  Definition sitpn_cycle
             (sitpn : Sitpn)
             (s : SitpnState)
             (time_value : nat)
             (env : Condition -> nat -> bool) :
    option (SitpnState * SitpnState) :=
    match sitpn_falling_edge sitpn s time_value env with
    | Some s' =>
      match sitpn_rising_edge sitpn s' with
      | Some s'' => Some (s', s'')
      (* Error: something went wrong in sitpn_rising_edge. *)
      | None => None
      end
    (* Error: something went wrong in sitpn_falling_edge. *)
    | None => None
    end.

  Functional Scheme sitpn_cycle_ind := Induction for sitpn_cycle Sort Prop.
  
End SitpnCycle.

(** * Animation function for Sitpn. *)

Section SitpnAnimate.

  (** Returns a list of couples (trans, dynamic itval) for all
      transitions associated with a static itval in [s_intervals]. 

      Useful to build the initial state of a Sitpn. *)
  
  Fixpoint s_intervals2d_intervals
           (transs : list Trans)
           (s_intervals : Trans -> option TimeInterval) :
    list (Trans * DynamicTimeInterval) :=
    match transs with
    | t :: tl =>
      match s_intervals t with
      | Some itval => (t, active itval) :: s_intervals2d_intervals tl s_intervals
      | None => s_intervals2d_intervals tl s_intervals
      end
    | [] => []
    end.
  
  (** Returns the marking of all places defined in the [places] list
      as a list of couples (place, nboftokens). 

      Useful to build the initial state of a Sitpn. *)

  Fixpoint marking2list
           (places : list Place)
           (marking : Place -> nat) {struct places} :
    list (Place * nat) :=
    match places with
    | p :: tl => (p, marking p) :: marking2list tl marking
    | [] => []
    end.

  (** Animates a Sitpn [sitpn] during [n] cycles, starting from state
      [s] of [sitpn].  *)

  Fixpoint sitpn_animate_aux
           (sitpn : Sitpn)
           (s : SitpnState)
           (n : nat)
           (time_value : nat)
           (env : Condition -> nat -> bool)
           (states : list (SitpnState * SitpnState)) {struct n} :
    option (list (SitpnState * SitpnState)) :=
    match n with
    | S m =>
      (* Plus one evolution cycle from state s. *)
      match sitpn_cycle sitpn s time_value env with
      | Some (s', s'') =>
        (* Decrements n, increments time value, and adds new state
           couple to states list. *)
        sitpn_animate_aux sitpn s'' m (S time_value) env (states ++ [(s', s'')])
      (* Error: something went wrong with sitpn_cycle.  *)
      | None => None
      end
    (* Animation is over, returns list of states. *)
    | O => Some states
    end. 

  (** Animates a Sitpn sitpn during n cycles, starting from the inital
      state of [sitpn], i.e s0 = (∅, m0, ∅, I0, ∅, ∅, ∅), where m0 is
      the initial marking of [sitpn] and I0 is the [s_intervals]
      function of [sitpn].  *)
  
  Definition sitpn_animate
             (sitpn : Sitpn)
             (n : nat)
             (env : Condition -> nat -> bool) :
    option (list (SitpnState * SitpnState)) := 
    let m0 := marking2list (places sitpn) (initial_marking sitpn) in
    let d_intervals0 := s_intervals2d_intervals (transs sitpn) (s_intervals sitpn) in
    let s0 := mk_SitpnState [] m0 d_intervals0 [] [] [] [] in
    sitpn_animate_aux sitpn s0 n 0 env [].
  
End SitpnAnimate.
