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

(** * Global facts used in the overall project. *)

(** Completes the Coq standard library. *)

Set Implicit Arguments.

(** ** Equivalence relation for sig. *)

Section SigEq.

  Variable A : Type.
  Variable P : A -> Prop.
  Variable Aeqdec : forall x y : A, {x = y} + {x <> y}.
  
  (** Two sigs are seq-equivalent if there first element is Leibniz's equal. *)
  
  Definition seq (u v : {a : A | P a}) : Prop :=
    proj1_sig u = proj1_sig v.

  (** Given that the equality is decidable for Set A, seq A is decidable. *)
  
  Definition seqdec (u v : {a : A | P a}) : {seq u v} + {~seq u v} :=
    Aeqdec (proj1_sig u) (proj1_sig v).
  
End SigEq.

Arguments seq {A P}.
Arguments seqdec {A P}.

