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

(** * Utilities for lists of dependent elements. *)

Require Import List.
Require Import ListsPlus.
Require Import Coqlib.
Require Import GlobalTypes.
Require Import Nat.

Import ListNotations.

Local Notation "'|' e '|'" := (exist _ e _) (at level 50).

(** States that if one can obtain a term of B from a proof that 
    a ∈ (b :: l) then one can obtain a term of B from a proof that a ∈ l.  *)

Lemma in_T_in_sublist_T {A B} :
  forall b l, (forall a : A, In a (b :: l) -> B) -> (forall (a : A), In a l -> B).
  intros b l H a H'; apply (H a (in_cons b a l H')).
Defined.

(** ** Transform and filter elements of a list. *)

Section TFilter.

  Variable A B : Type.
  Variable ffilter : B -> bool.
  
  (** Given a proof that all elements in [lofAs] can yield a term of
    [B], transform each element of [lofAs] into a term [b] of [B].

    If [b] passes the [test] given in parameter then, adds [b]
    to the list [lofBs].
    
   *)

  Fixpoint tfilter_aux (lofAs : list A) (lofBs : list B) {struct lofAs} :
    (forall a, In a lofAs -> B) -> list B :=
    match lofAs with
    | nil => fun _ => lofBs
    | a :: tl =>
      fun pf : _ =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in

        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in

        (* If b passes the test, then adds it to lofBs. *)
        if ffilter b then
          tfilter_aux tl (lofBs ++ [b]) pf_tl
        else
          tfilter_aux tl lofBs pf_tl
    end.

  (** Wrapper around the [tfilter_aux] function. *)

  Definition tfilter (lofAs : list A) :
    (forall a, In a lofAs -> B) -> list B :=
    tfilter_aux lofAs nil.
  
End TFilter.

Arguments tfilter {A B}.

(** ** Transform and map elements of a list. *)

Section TMap.

  Variable A B C : Type.
  Variable fmap : B -> C.
  
  (** Given a proof that all elements in [lofAs] can yield a term of
      [B], transform each element of [lofAs] into a term [b] of [B], then
      maps [b] to a term [c] of [C].
    
   *)

  Fixpoint tmap_aux (lofAs : list A) (lofCs : list C) {struct lofAs} :
    (forall a, In a lofAs -> B) -> list C :=
    match lofAs with
    | nil => fun _ => lofCs
    | a :: tl =>
      fun pf : _ =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in

        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in
        
        tmap_aux tl (lofCs ++ [fmap b]) pf_tl
    end.

  (** Wrapper around the [tmap_aux] function. *)

  Definition tmap (lofAs : list A) :
    (forall a, In a lofAs -> B) -> list C :=
    tmap_aux lofAs nil.

  Variable fopte : B -> optionE C.
  
  (** Given a proof that all elements in [lofAs] can yield a term of
      [B], transform each element of [lofAs] into a term [b] of [B], then
      maps [b] to Some term [c] of [C] or return an error.
   *)

  Fixpoint topte_map_aux (lofAs : list A) (lofCs : list C) {struct lofAs} :
    (forall a, In a lofAs -> B) -> optionE (list C) :=
    match lofAs with
    | nil => fun _ => Success lofCs
    | a :: tl =>
      fun pf : _ =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in

        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in

        (* Continues the mapping or returns an error. *)
        match fopte b with
        | Success c => topte_map_aux tl (lofCs ++ [c]) pf_tl
        | Err msg => Err msg
        end
    end.

  (** Wrapper around the [topte_map_aux] function. *)

  Definition topte_map (lofAs : list A) :
    (forall a, In a lofAs -> B) -> optionE (list C) :=
    topte_map_aux lofAs nil.
  
End TMap.

Arguments tmap {A B C}.
Arguments topte_map {A B C}.

(** ** Transform and iterate from left to right on a list.  *)

Section TFold_Left_Recursor.
  
  Variable A B C : Type.
  Variable f : C -> B -> C.

  (** Given a proof that all elements in [lofAs] can yield a term of
      [B], transform each element of [lofAs] into a term [b] of [B], then
      calls [f] on [c] and [b] to build a new term of [C]. *)
  
  Fixpoint tfold_left (lofAs : list A) (c : C) : 
    (forall a, In a lofAs -> B) -> C :=
    match lofAs with
    | nil => fun _ => c
    | a :: tl =>
      fun pf : _ =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in

        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in

        (* Builds a new term of C by calling f on b and c and
           continues. *)
        tfold_left tl (f c b) pf_tl
    end.

  Variable fopte : C -> B -> optionE C.

  (** Given a proof that all elements in [lofAs] can yield a term of
      [B], transform each element of [lofAs] into a term [b] of [B],
      then calls [fopte] on [c] and [b] to build a new term of [C] or
      raises an error. *)
  
  Fixpoint topte_fold_left (lofAs : list A) (c : C) : 
    (forall a, In a lofAs -> B) -> optionE C :=
    match lofAs with
    | nil => fun _ => Success c
    | a :: tl =>
      fun pf : _ =>
        (* Creates a B from a proof that (In a (a :: tl)). *)
        let b := pf a (in_eq a tl) in

        (* Creates a proof that (forall a, In a tl -> B) *)
        let pf_tl := in_T_in_sublist_T a tl pf in

        (* Checks if calling fopte on b and c returns an error,
           otherwise continues. *)
        match fopte c b with
        | Success c' => topte_fold_left tl c' pf_tl
        | Err msg => Err msg
        end
    end.
  
End TFold_Left_Recursor.

Arguments tfold_left {A B C}.
Arguments topte_fold_left {A B C}.


