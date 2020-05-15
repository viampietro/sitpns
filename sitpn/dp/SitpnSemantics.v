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

(** * Sitpn semantics definition *)

Require Import Coqlib.
Require Import dp.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.

Set Implicit Arguments.

Local Notation "| e |" := (exist _ e _) (at level 50).

(** ∀ sitpn ∈ SITPN, ∀ t ∈ T, ∀ s ∈ S, 
    AllConditionsTrue(t) iff ∀ c ∈ C, has_C(t,c) ⇒ cond(c) = true
 *)

Definition AllConditionsEnabled (sitpn : Sitpn) (s : SitpnState sitpn) (t : (T sitpn)) :=
  forall c, has_C t c = one -> cond s c = true /\ has_C t c = mone -> cond s c = false.

(** ∀ t ∈ T, marking m, t ∈ sens(m) iff
    ∀ p ∈ P, m(p) ≥ Pre(p, t) ∧ m(p) ≥ Test(p, t) ∧ (m(p) < Inhib(p, t) ∨ Inhib(p, t) = 0) *)

Definition Sens (sitpn : Sitpn) (M : (P sitpn) -> nat) (t : (T sitpn)) :=
  forall p n,
    (pre p t = Some (test, n) \/ pre p t = Some (basic, n) -> (M p) >= n) /\
    (pre p t = Some (inhibitor, n) -> (M p) < n).

(** ∀ n ∈ N, ∀ i ∈ I+ ⊔ {ψ}, n ∈ i iff i = [a; b] ∧ a ≤ n ≤ b *)

Definition InItval (n : nat) (i : DynamicTimeInterval) :=
  forall nii,
    i = active nii ->
    (a nii) <= n /\ forall bnotinf, le_nat_natinf n (b nii) bnotinf.
  
(** t ∉ Ti ∨ 0 ∈ I(t) *)

Definition HasReachedTimeWindow (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  forall t_is_timet, InItval 0 (I s (exist _ t t_is_timet)).

(** ∀ t ∈ T, ∀ s ∈ S, t ∈ firable(s) iff
    t ∈ Sens(M) ∧ (t ∉ Ti ∨ 0 ∈ I(t)) ∧ AllConditionsTrue(t). 
 *)

Definition Firable (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) :=
  Sens (M s) t /\ HasReachedTimeWindow s t /\ AllConditionsEnabled s t.

(** ∀ t, t' ∈ T, ∀ s ∈ S, t' ∈ Pr(t) iff
    t' ≻ t ∧ t' ∈ Firable(s)
 *)

Definition IsPriorityAndFirable (sitpn : Sitpn) (s : SitpnState sitpn) (t t' : T sitpn) : Prop :=
  pr t' t = true /\ Firable s t'.

(** Subset of transitions that are firable and have a higher firing
    priority than [t]. *)

Definition Pr (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) := { t' | IsPriorityAndFirable s t t'}.

(** [Pr] is a subset of the set of transitions [T]. *)

Definition Pr_in_T (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) (t' : Pr s t) : T sitpn := proj1_sig t'.
Coercion Pr_in_T : Pr >-> T.

(** States that a given Set S is implemented by a list l.  As a side
    effect, states that a given set is finite and enumerable. *)

Definition Set_in_List (S : Type) (l : list S) : Prop := (forall s : S, In s l) /\ NoDup l.

(** Sums the weight of the pre-edges between the place [p] 
    and the transitions of a list given in parameter.

    ∑ pre(t, p), ∀ t ∈ some list of transitions.
 *)

Inductive PreSumList (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : list {t | P t} -> nat -> Prop :=
| PreSumListNil : PreSumList p P [] 0
| PreSumListCons :
    forall t l n m a gt_m_O,
      PreSumList p P l n ->
      pre p (proj1_sig t) = Some (a, exist _ m gt_m_O) ->
      PreSumList p P (t :: l) (n + m).

(** For all list [l] and natural [n] such that: 

    - [l] implements the subset of transitions verifying predicate [P] (i.e, {t' | P t'})
    - and, ∑ pre(p,t) = n, ∀ t ∈ l 
    
    then ∑ pre(p, t) = n, ∀ t ∈ {t' | P t'}    
*)

Inductive PreSum (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : nat -> Prop :=
| PreSum_ : forall l n, @Set_in_List {t | P t} l -> PreSumList p P l n -> PreSum p P n.

Inductive MarkingSubPreSum (sitpn : Sitpn) (s : SitpnState sitpn) (tSet : T sitpn -> Prop) (msub : P sitpn -> nat) : Prop :=
| MarkingSubPreSum_ : (forall p n, PreSum p tSet n -> msub p = M s p - n) -> MarkingSubPreSum s tSet msub.

(** States that marking [m] is the residual marking resulting of the
    withdrawal of the tokens from the input places of [t] after the
    "partial" firing (token consumption only) of the transitions with
    a higher priority than [t].  *)

Definition IsResidualMarking (sitpn : Sitpn) (s : SitpnState sitpn) (t : T sitpn) (m : P sitpn -> nat) :=
  MarkingSubPreSum s (IsPriorityAndFirable s t) m.

(** States that marking [m] is the residual marking resulting of the
    withdrawal of the tokens from the input places of transitions that
    belong to the [Fired] field of state s.  *)

Definition IsTransientMarking (sitpn : Sitpn) (s : SitpnState sitpn) (m : P sitpn -> nat) :=
  MarkingSubPreSum s (Fired s) m.

(** Sums the weight of the post-edges between the place [p] 
    and the transitions of a list given in parameter.

    ∑ post(t, p), ∀ t ∈ some list of transitions.
 *)

Inductive PostSumList (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : list {t | P t} -> nat -> Prop :=
| PostSumListNil : PostSumList p P [] 0
| PostSumListCons :
    forall t l n m gt_m_O,
      PostSumList p P l n ->
      post (proj1_sig t) p = Some (exist _ m gt_m_O) ->
      PostSumList p P (t :: l) (n + m).

(** For all list [l] and natural [n] such that: 

    - [l] implements the subset of transitions verifying predicate [P] (i.e, {t' | P t'})
    - and, ∑ post(p,t) = n, ∀ t ∈ l 
    
    then ∑ post(p, t) = n, ∀ t ∈ {t' | P t'}    
*)

Inductive PostSum (sitpn : Sitpn) (p : P sitpn) (P : T sitpn -> Prop) : nat -> Prop :=
| PostSum_ : forall l n, @Set_in_List {t | P t} l -> PostSumList p P l n -> PostSum p P n.

Inductive MarkingSubPreSumAddPostSum (sitpn : Sitpn) (s : SitpnState sitpn) (tSet : T sitpn -> Prop) (m : P sitpn -> nat) : Prop :=
| MarkingSubPreSumAddPostSum_ :
    (forall p n n', PreSum p tSet n -> PostSum p tSet n' -> m p = M s p - n + n') -> MarkingSubPreSumAddPostSum s tSet m.

(** States that marking [m] is the residual marking resulting of the
    withdrawal of the tokens from the input places of transitions that
    belong to the [Fired] field of state s.  *)

Definition IsNewMarking (sitpn : Sitpn) (s : SitpnState sitpn) (m : P sitpn -> nat) :=
  MarkingSubPreSumAddPostSum s (Fired s) m.

(** Defines the Sitpn state transition relation. *)

Inductive SitpnStateTransition (sitpn : Sitpn) (s s' : SitpnState sitpn) (env : C sitpn -> nat -> bool) (tau : nat) : Clk -> Prop :=
| SitpnStateTransition_falling :

    (** Captures the new value of conditions, and determines the
        activation status for actions.  *)
    (forall c, (cond s' c) = (env c tau)) ->
    (forall a, (exists p, (M s p) > 0 /\ has_A p a = true) -> (exa s' a) = true) ->
    (forall a, (forall p, (M s p) = 0 \/ has_A p a = false) -> (exa s' a) = false) ->    

    (** Updates the dynamic time intervals according to the firing
       status of transitions and the reset orders. *)
    (forall (t : Ti sitpn) i, Sens (M s) t -> (reset s t = true \/ Fired s t) -> Is t = Some i -> I s' t = (itval i)--) ->
    (forall (t : Ti sitpn) i, Sens (M s) t -> reset s t = false -> ~Fired s t -> I s t = active i -> I s' t = i--) ->
    (forall (t : Ti sitpn), Sens (M s) t -> reset s t = false -> ~Fired s t -> I s t = blocked -> I s' t = blocked) ->

    (** Determines transitions to be fired at the next clock event. *)
    (forall t, ~Firable s' t -> ~Fired s' t) ->
    (forall t m, Firable s' t -> IsResidualMarking s' t m  -> Sens m t -> Fired s' t) ->
    (forall t m, Firable s' t -> IsResidualMarking s' t m  -> ~Sens m t -> ~Fired s' t) ->

    (** Marking stays the same between s and s'. *)
    (forall p, M s p = M s' p) -> 

    (** Reset orders stay the same between s and s'. *)
    (forall t, reset s t = reset s' t) ->

    (** Function states stay the same between s and s'. *)
    (forall f, exf s f = exf s' f) ->
    
    (** Conclusion *)
    SitpnStateTransition s s' env tau falling_edge

| SitpnStateTransition_rising:

    (** Marking at state s' is the new marking resulting of the firing
        of all transitions belonging to the Fired subset at state
        s. *)
    IsNewMarking s (M s') ->

    (** Computes the reset orders for dynamic time intervals. *)
    (forall (t : Ti sitpn) m, IsTransientMarking s m -> ~Sens m t -> reset s' t = true) ->
    (forall (t : Ti sitpn) m, IsTransientMarking s m -> Sens m t -> reset s' t = false) ->

    (** Determines if some dynamic time intervals are blocked. *)
    (forall (t : Ti sitpn), eq_ditval (I s t) ditval00 /\ ~Fired s t -> eq_ditval (I s' t) blocked) ->
    (forall (t : Ti sitpn), eq_ditval (I s t) ditval00 \/ Fired s t -> eq_ditval (I s' t) (I s t)) ->

    (** Determines if some functions are executed. *)
    (forall f, (exists t, Fired s t /\ has_F t f = true) -> exf s' f = true) ->
    (forall f, (forall t, ~Fired s t \/ has_F t f = false) -> exf s' f = true) -> 
    
    (** Fired subset stays the same between s and s'. *)
    (forall t, Fired s' t <-> Fired s t) ->

    (** Condition values stay the same between s and s'. *)
    (forall c, cond s' c = cond s c) -> 

    (** Action states stay the same between s and s'. *)
    (forall a, exa s' a = exa s a) ->
    
    (** Conclusion *)
    SitpnStateTransition s s' env tau rising_edge.    





