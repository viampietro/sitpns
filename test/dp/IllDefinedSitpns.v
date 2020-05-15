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

(** * Instance of Sitpn with an empty transition set. *)

Require Import Coqlib.
Require Import sets.Sitpn.
Require Import NatSet.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import GenerateInfos.
Require Import String.
Require Import HexString.

Open Scope natset_scope.
Open Scope string_scope.
Set Implicit Arguments.

(* Definition of the priority relation for the examples sitpns, and
   proof that it is a strict order over transitions.  *)

Definition pr_rel (transitions : NatSet.t) :=
  (fun (_ : {t : NatSet.Raw.elt | List.In t (NatSet.this transitions)})
       (_ : {t : NatSet.Raw.elt | List.In t (NatSet.this transitions)}) => false).

(* Definition of an example sitpn with an empty list of
   transitions. *)

Lemma pr_is_irrefl1 : forall x, pr_rel {[]} x x = false.
Proof. simpl; reflexivity. Defined.

Lemma pr_is_trans1 : forall x y z, pr_rel {[]} x y = true -> pr_rel {[]} y z = true -> pr_rel {[]} x z = true.
Proof. intros x y z Hpr_rel. unfold pr_rel in Hpr_rel. inversion Hpr_rel. Defined.
  
Definition pr_is_strict_order_pf1 :=
  MkStrictOrderB _ (pr_rel {[]}) pr_is_irrefl1 pr_is_trans1.

Example sitpn_emp_transs :=
  @BuildSitpn
    {[ 0, 1, 2 ]}
    {[ ]}
    (fun p t => None)
    (fun t p => None)
    (fun p => 0)
    (fun t => None)
    {[ ]}
    {[ ]}
    {[ ]}
    (fun t c => zero)
    (fun p a => false)
    (fun t f => false)
    (fun t t' => false)
    pr_is_strict_order_pf1.

(* Definition of an example sitpn with an empty list of
   places. *)

Lemma pr_is_irrefl2 : forall x, pr_rel {[0, 1, 2]} x x = false.
Proof. simpl; reflexivity. Defined.

Lemma pr_is_trans2 : forall x y z, pr_rel {[0, 1, 2]} x y = true -> pr_rel {[0, 1, 2]} y z = true -> pr_rel {[0, 1, 2]} x z = true.
Proof. intros x y z Hpr_rel. unfold pr_rel in Hpr_rel. inversion Hpr_rel. Defined.
  
Definition pr_is_strict_order_pf2 :=
  MkStrictOrderB _ (pr_rel {[0, 1, 2]}) pr_is_irrefl2 pr_is_trans2.

Example sitpn_emp_places :=
  @BuildSitpn
    {[ ]}
    {[ 0, 1, 2]}
    (fun p t => None)
    (fun t p => None)
    (fun p => 0)
    (fun t => None)
    {[ ]}
    {[ ]}
    {[ ]}
    (fun t c => zero)
    (fun p a => false)
    (fun t f => false)
    (fun t t' => false)
    pr_is_strict_order_pf2.

(* Definition of an example sitpn with isolated places. *)

Definition places_iso_places := {[ 0, 1, 2 ]}.
Definition transs_iso_places := {[ 0, 1, 2 ]}.
Definition Piso := { p | List.In p (NatSet.this places_iso_places)}.
Definition Tiso := { t | List.In t (NatSet.this transs_iso_places)}.

Notation "[ e ]" := (exist _ e _).

(* Input arcs function. Here, place 2 is isolated. *)

Definition pre_iso_places (p : Piso) (t : Tiso) : option (ArcT * natstar) :=
  match p, t with
  | [0], [0] => Some (basic, onens)
  | [1], [0] => Some (basic, onens)
  | [1], [1] => Some (basic, onens)
  | _, _ => None
  end.

Example sitpn_iso_places :=
  @BuildSitpn
    places_iso_places
    transs_iso_places
    pre_iso_places
    (fun t p => None)
    (fun p => 0)
    (fun t => None)
    {[ ]}
    {[ ]}
    {[ ]}
    (fun t c => zero)
    (fun p a => false)
    (fun t f => false)
    (fun t t' => false)
    pr_is_strict_order_pf2.

(* Getting infos for place 2 must raise an error. *)

Definition p0_in_P : In 0 (NatSet.this places_iso_places). simpl. auto. Defined.
Definition p1_in_P : In 1 (NatSet.this places_iso_places). simpl. auto. Defined.
Definition p2_in_P : In 2 (NatSet.this places_iso_places). simpl. auto. Defined.

Definition p0 : P sitpn_iso_places := exist _ 0 p0_in_P.
Definition p1 : P sitpn_iso_places := exist _ 1 p1_in_P.
Definition p2 : P sitpn_iso_places := exist _ 2 p2_in_P.

Compute (get_p_info sitpn_iso_places p0).
Compute (get_p_info sitpn_iso_places p1).
Compute (get_p_info sitpn_iso_places p2).

Example test_get_info_p2_err : (if (get_p_info sitpn_iso_places p2) then true else false) = false. simpl. reflexivity. Qed.



