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

(** Exports all modules pertaining to lists and defines new lists
    predicates.  The predicates are useful in the formalization 
    and the proofs.
 *)

Require Import Coqlib.
Require Import Omega.
Require Import Classical_Prop.
Require Import GlobalTypes.

Require Export FstSplit.
Require Export InAndNoDup.

Set Implicit Arguments.

(** ** Miscellaneous list functions. *)

Section ListPlusMisc.

  Variable A : Type.
  
  Definition is_empty (l : list A) : bool := if l then true else false.
  
End ListPlusMisc.

(** ** Finds and sets an element in a list of couple. *)

Section MapAsListOfCouples.

  Variable A B : Type.
  Variable eq : A -> A -> Prop.
  Variable eq_dec : forall x y : A, {eq x y} + {~eq x y}.
  
  (** Returns [Some a] if it is asscoiated with [k] in list [l].  
      Returns None, if k is not in the first elements of [l].
   *)

  Fixpoint getv (k : A) (l : list (A * B)) {struct l} : option B :=
    match l with
    | nil => None
    | cons (a, b) tl => if eq_dec k a then Some b else getv k tl
    end.

  (** Sets the couple [(k, v)] in list [l]. If [k] is in the first
      elements of [l], then the old binding of [k] to value in [l] is
      replaced by the binding of [k] to [v].  Puts the couple [(k,v)]
      at the end of list [l] otherwise. *)

  Fixpoint setv (k : A) (v : B) (l : list (A * B)) {struct l} : list (A * B) :=
    match l with
    | nil => [(k, v)]
    | cons (a, b) tl => if eq_dec k a then cons (k, v) tl else cons (a, b) (setv k v tl)
    end.
  
End MapAsListOfCouples.

Arguments getv {A B eq}.
Arguments setv {A B eq}.

(** ** Map function with possible errors. *)

Section OMap.

  Variable A B : Type.
  
  Variable fopt_map : A -> option B.
  
  (** Maps all elements of [lofAs] to a term [b] of [B] and returns
      the resulting list or return an error. *)

  Fixpoint omap_aux (lofAs : list A) (lofBs : list B) {struct lofAs} :
    option (list B) :=
    match lofAs with
    | nil => Some lofBs
    | a :: tl =>
      (* Continues the mapping or returns an error. *)
      match fopt_map a with
      | Some b => omap_aux tl (lofBs ++ [b])
      | None => None
      end
    end.

  (** Wrapper around the [omap_aux] function. *)

  Definition omap (lofAs : list A) : option (list B) :=
    omap_aux lofAs nil.

  (** Version with optionE used instead of option. *)

  Variable fopte_map : A -> optionE B.
  
  (** Maps all elements of [lofAs] to a term [b] of [B] and returns
      the resulting list or return an error. *)

  Fixpoint oemap_aux (lofAs : list A) (lofBs : list B) {struct lofAs} :
    optionE (list B) :=
    match lofAs with
    | nil => Success lofBs
    | a :: tl =>
      (* Continues the mapping or returns an error. *)
      match fopte_map a with
      | Success b => oemap_aux tl (lofBs ++ [b])
      | Err msg => Err msg
      end
    end.

  (** Wrapper around the [omap_aux] function. *)

  Definition oemap (lofAs : list A) : optionE (list B) :=
    oemap_aux lofAs nil.
  
End OMap.

Arguments omap_aux {A B}.
Arguments omap {A B}.
Arguments oemap_aux {A B}.
Arguments oemap {A B}.

(** Fold left function with possible errors. *)

Section OFold_left.

  Variable A B : Type.
  
  Variable f : A -> B -> option A.

  Fixpoint ofold_left (l:list B) (a0 : A) : option A :=
    match l with
    | nil => Some a0
    | cons b t => match f a0 b with
                  | None => None
                  | Some a => ofold_left t a
                  end
    end.

  (** Version with optionE used instead of option. *)
  
  Variable fe : A -> B -> optionE A.

  Fixpoint oefold_left (l:list B) (a0 : A) : optionE A :=
    match l with
    | nil => Success a0
    | cons b t => match fe a0 b with
                  | Err msg => Err msg
                  | Success a => oefold_left t a
                  end
    end.
  
End OFold_left.

Arguments ofold_left {A B}.
Arguments oefold_left {A B}.

(** ** Predicates IsDecListCons, IsDecListApp and facts. *)

Section DecreasedList.

  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)
  
  Inductive IsDecListCons {A: Type} : list A -> list A -> Prop :=
  | IsDecListCons_refl : forall l : list A, IsDecListCons l l
  | IsDecListCons_eq : forall (a : A) (l : list A), IsDecListCons l (a :: l)
  | IsDecListCons_cons :
      forall (a : A) (l l' : list A),
      IsDecListCons l l' ->      
      IsDecListCons l (a :: l').

  Hint Constructors IsDecListCons.
  
  (** Facts about IsDecListCons. *)
  
  Lemma is_dec_list_cons_nil {A : Type} :
    forall (l : list A), IsDecListCons [] l.
  Proof.
    induction l.
    - apply IsDecListCons_refl.
    - apply IsDecListCons_cons; assumption.
  Qed.

  Lemma is_dec_list_cons_app_eq {A : Type} :
    forall (l l' : list A),
      IsDecListCons l (l' ++ l).
  Proof.
    induction l'.

    (* BASE CASE *)
    - simpl; apply IsDecListCons_refl.

    (* INDUCTION CASE *)
    - rewrite <- app_comm_cons; apply IsDecListCons_cons; assumption.
  Qed.
  
  Lemma is_dec_list_cons_incl {A : Type} :
    forall l' l : list A, IsDecListCons l l' -> incl l l'.
  Proof.
    intros l l'; induction 1.
    - firstorder.
    - firstorder.
    - apply incl_tl; assumption.      
  Qed.

  Lemma is_dec_list_cons_cons {A : Type} :
    forall (a : A) (l' l : list A), IsDecListCons (a :: l) l' -> IsDecListCons l l'.
  Proof.
    intros a l'.
    induction l'; intros l His_dec.
    
    - inversion His_dec. 
    - inversion His_dec; auto.
  Qed.

  (** If l' has no duplicates and l is a decreased version of l' then
      l has no duplicates. *)
  
  Lemma nodup_is_dec_list_cons {A : Type} :
    forall (l' l : list A),
      NoDup l' ->
      IsDecListCons l l' ->
      NoDup l.
  Proof.
    induction l'; intros l Hnodup_l' His_dec.
    
    (* BASE CASE *)
    - inversion His_dec; apply NoDup_nil.

    (* INDUCTION CASE *)
    - inversion His_dec.
      
      (* Case IsDecListCons_refl *)
      + assumption.

      (* Case IsDecListCons_eq *)
      + rewrite NoDup_cons_iff in Hnodup_l';
          apply proj2 in Hnodup_l';
          assumption.

      (* Case IsDecListCons_cons *)
      + rewrite NoDup_cons_iff in Hnodup_l';
          apply proj2 in Hnodup_l';
          apply (IHl' l Hnodup_l' H1).
  Qed.

  (** If IsDecListCons l l' then it's possible to
      decompose l' in (m ++ l). *)
  
  Lemma is_dec_list_cons_exists_app {A : Type} :
    forall (l' l : list A),
      IsDecListCons l l' -> exists l'' : list A, l' = l'' ++ l.
  Proof.
    induction l'; intros l His_dec.

    (* BASE CASE *)
    - inversion His_dec.
      exists []; rewrite app_nil_r; auto.

    (* INDUCTION CASE *)
    - inversion His_dec.
      + exists []. simpl. reflexivity.
      + exists [a]. simpl. reflexivity.
      + specialize (IHl' l H1) as Hex.
        inversion_clear Hex as (m & Heq_l'_ml).
        rewrite Heq_l'_ml.
        exists (a :: m).
        auto.
  Qed.

  (** concat is a morphism for IsDecListCons. *)
  
  Lemma is_dec_list_cons_concat {A : Type} :
    forall (ll ll' : list (list A)),
      IsDecListCons ll ll' -> IsDecListCons (concat ll) (concat ll').
  Proof.
    intros ll ll' His_dec.
    specialize (is_dec_list_cons_exists_app His_dec) as Hex_l''.
    inversion_clear Hex_l'' as (l'' & Heq_l'_ll'').
    rewrite Heq_l'_ll''.
    rewrite concat_app.
    apply is_dec_list_cons_app_eq.
  Qed.
  
  (** List l is a decreased or equal version of list l'. 
      l' is built from l by adding elements in the front (cons).
       
      Useful for proof involving recursion on lists.  *)

  Inductive IsDecListApp {A : Type} : list A -> list A -> Prop :=
  | IsDecListApp_refl : forall l : list A, IsDecListApp l l
  | IsDecListApp_cons :
      forall (a : A) (l l' : list A),
        IsDecListApp l l' ->
        IsDecListApp l (l' ++ [a]).
  
End DecreasedList.

(** ** Predicate IsPredInList and facts. *)

Section PredInList.

  Variable A : Type.
    
  (** Tells if x is a predecessor of y in list l. 
      x and y are possibly equal and list l
      possibly contains duplicates. *)
  
  Inductive IsPredInList (x y : A) : list A -> Prop :=
  | IsPredInList_eq :
      forall l : list A, IsPredInList x y (x :: y :: l)
  | IsPredInList_rm_snd :
      forall (a : A) (l : list A), IsPredInList x y (x :: l) ->
                                   IsPredInList x y (x :: a :: l)
  | IsPredInList_rm_fst : 
      forall (a : A) (l : list A), IsPredInList x y l ->
                                   IsPredInList x y (a :: l).

  (** IsPredInList with no duplicates in list l, x and y different. *)
  
  Definition IsPredInNoDupList (x y : A) (l : list A) :=
    x <> y /\ NoDup l /\ IsPredInList x y l.

  (** Facts about IsPredInList and IsPredInNoDuplist. *)
  
  Lemma not_is_pred_in_list_nil :
    forall (x y : A), ~IsPredInList x y [].
  Proof.
    intros x y His_pred.
    inversion His_pred.
  Qed.

  Lemma is_pred_in_list_in_tail :
    forall (x y : A) (l : list A), In y l -> IsPredInList x y (x :: l).
  Proof.
    induction l.
    - intro Hnot_in; inversion Hnot_in.
    - intro Hin_y_l; inversion Hin_y_l.
      + rewrite H; apply IsPredInList_eq.
      + apply IsPredInList_rm_snd; apply (IHl H).
  Qed.
  
  Theorem is_pred_in_dec_list :
    forall (l l' : list A) (x y : A),
      IsPredInList x y l -> IsDecListCons l l' -> NoDup l' -> IsPredInList x y l'.
  Proof.
    induction l'.
    - intros x y His_pred His_dec Hnodup.
      induction l.
      + inversion His_pred.
      + inversion His_dec.
    - intros x y His_pred His_dec Hnodup.
      inversion His_dec.
      + rewrite <- H0; assumption.
      + rewrite <- H2; apply IsPredInList_rm_fst; assumption. 
      + apply IsPredInList_rm_fst.
        -- apply NoDup_cons_iff in Hnodup; apply proj2 in Hnodup.
           apply (IHl' x y His_pred H1 Hnodup).
  Qed.

  Lemma is_pred_cons_diff :
    forall (l : list A) (x y a : A) , IsPredInList x y (a :: l) ->
                                      x <> a ->
                                      IsPredInList x y l.
  Proof.
    induction l; intros x y a' His_pred Hdiff.
    - inversion His_pred; inversion H0.
    - inversion His_pred.
      + contradiction.
      + contradiction.
      + assumption.
  Qed.

  Lemma is_pred_in_tail :
    forall (l : list A) (x y : A) , IsPredInNoDupList x y (x :: l) -> In y l.
  Proof.
    induction l; intros x y His_pred;
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
    - inversion H2; inversion H3.
    - inversion H2.
      + apply in_eq.
      + apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 H3))) as Hin_y_l.
        apply in_cons.
        assumption.
      + inversion H1.
        apply not_in_cons in H7.
        apply proj1 in H7.
        specialize (is_pred_cons_diff H3 H7) as His_pred_in_l.
        apply IsPredInList_rm_fst with (a := x) in His_pred_in_l.
        apply in_cons.
        apply NoDup_remove with (l := [x]) in H1.
        apply proj1 in H1.
        unfold IsPredInNoDupList in IHl.
        specialize (IHl x y (conj H (conj H1 His_pred_in_l))) as Hin_y_l.
        assumption.
  Qed.

  Theorem not_is_pred_in_list_if_hd :
    forall (l : list A) (x y : A) , ~IsPredInNoDupList x y (y :: l).
  Proof.
    induction l; intros x y His_pred.
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      inversion H2; inversion H3.
    - unfold IsPredInNoDupList in His_pred.
      decompose [and] His_pred.
      inversion H2.
      + contradiction.
      + contradiction.
      + assert (Hvee := classic (x = a)).
        elim Hvee.
        -- intro Heq_xa.
           rewrite Heq_xa in H3.
           rewrite Heq_xa in H.
           apply NoDup_cons_iff in H1.
           elim H1; intros Hnot_in_y Hnodup.
           specialize (is_pred_in_tail (conj H (conj Hnodup H3))) as Hin_y_l.
           apply in_cons with (a := a) in Hin_y_l.
           contradiction.
        -- intro Hneq_xa.
           specialize (is_pred_cons_diff H3 Hneq_xa) as His_pred_in_l.
           apply IsPredInList_rm_fst with (a := y) in His_pred_in_l.
           apply NoDup_remove with (l := [y]) in H1.
           apply proj1 in H1.
           unfold IsPredInNoDupList in IHl.
           apply (IHl x y (conj H (conj H1 His_pred_in_l))).
  Qed.

  Theorem not_is_pred_in_dec_list :
    forall (l' l : list A) (x y : A),
      IsDecListCons (y :: l) l' ->
      In x l ->
      ~IsPredInNoDupList x y l'.
  Proof.
    induction l'; intros l x y His_dec Hin_x_l.
    - inversion His_dec.
    - intro His_pred.
      unfold IsPredInNoDupList in His_pred; decompose [and] His_pred.
      rename H into Hneq_xy; rename H1 into Hnodup; clear His_pred; rename H2 into His_pred.
      inversion His_pred.
      + inversion His_dec.
        -- rewrite <- H3 in H0; contradiction.
        -- rewrite <- H4 in Hnodup.
           rewrite <- H0 in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H3.
           apply is_dec_list_cons_incl in H3.
           apply H3 in Hin_x_l.
           rewrite <- H0 in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- rewrite <- H4 in H; contradiction.
        -- rewrite <- H5 in Hnodup.
           rewrite <- H in Hnodup.
           apply in_cons with (a := y) in Hin_x_l.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
        -- apply is_dec_list_cons_cons in H4.
           apply is_dec_list_cons_incl in H4.
           apply H4 in Hin_x_l.
           rewrite <- H in Hnodup.
           apply NoDup_cons_iff in Hnodup.
           apply proj1 in Hnodup; contradiction.
      + inversion His_dec.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l))
            by apply not_is_pred_in_list_if_hd.
           rewrite <- H4 in His_pred; rewrite <- H4 in Hnodup.
           rewrite <- H5 in His_pred; rewrite <- H5 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup His_pred)) as His_pred'.
           contradiction.
        -- assert (Hnot_is_pred : ~IsPredInNoDupList x y (y :: l))
            by apply not_is_pred_in_list_if_hd.
           rewrite <- H5 in Hnodup; rewrite <- H5 in H0.
           apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           specialize (conj Hneq_xy (conj Hnodup H0)) as His_pred'.
           contradiction.
        -- apply NoDup_cons_iff in Hnodup.
           apply proj2 in Hnodup.
           apply (IHl' l x y H4 Hin_x_l (conj Hneq_xy (conj Hnodup H0))).
  Qed.
  
End PredInList.



