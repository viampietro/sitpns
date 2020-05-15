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

(** * Types of Sitpn information structures. *)

Require Import dp.Sitpn.
Require Import SitpnTypes.
Require Import GlobalTypes.
Require Import NatSet.

Section SitpnInfoTypes.

  Variable sitpn : Sitpn.

  (** Defines the type of PlaceInfo, gathering informations about a
    given place of an SITPN. *)

  Inductive PlaceInfo : Type :=
    MkPlaceInfo { tinputs : list (T sitpn);
                  toutputs : list (T sitpn) }.
  
  (** Defines the type of TransInfo, gathering informations about a
    given transition of an SITPN. *)

  Inductive TransInfo : Type :=
    MkTransInfo { pinputs : list (P sitpn); conds : list (C sitpn) }.
  
  (** Defines the record type that stores information about an Sitpn. *)

  Inductive SitpnInfo : Type :=
    MkSitpnInfo {
        pinfos : list (P sitpn * PlaceInfo);
        tinfos : list (T sitpn * TransInfo);
        cinfos : list (C sitpn * list (T sitpn));
        ainfos : list (A sitpn * list (P sitpn));
        finfos : list (F sitpn * list (T sitpn));
      }.

End SitpnInfoTypes.

(** Set implicit arguments for PlaceInfo fields. *)

Arguments tinputs {sitpn}.
Arguments toutputs {sitpn}.

(** Set implicit arguments for TransInfo fields. *)

Arguments pinputs {sitpn}.
Arguments conds {sitpn}.

(** Set implicit arguments for SitpnInfo fields. *)

Arguments cinfos {sitpn}.
