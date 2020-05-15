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

(** * Facts about the [In] and [NoDup] predicates. *)

Require Import Coqlib.
Require Import FstSplit.

(** Lemmas and tactics pertaining to the [In] and [NoDup] predicates
    defined in the [Lists] library.
 *)

Section InAndNoDupLemmas.

  (** If a is in list l and l is in list of lists ll then a is in (concat ll).
      The result of (concat ll) is one list corresponding
      to the concatenation of all lists in ll. *)

  Lemma in_concat {A : Type} :
    forall (a : A) (l : list A) (ll : list (list A)),
      In a l -> In l ll -> In a (List.concat ll).
  Proof.
    intros.
    induction ll.
    (* Base case, ll = []. *)
    - elim H0.
    (* Inductive case. *)
    - apply in_inv in H0; elim H0; intros.
      + rewrite <- H1 in H.
        apply or_introl with (B := In a (List.concat ll)) in H.
        apply in_or_app in H.
        rewrite concat_cons.
        auto.
      + apply IHll in H1.
        apply or_intror with (A := In a a0) in H1.
        apply in_or_app in H1.
        rewrite concat_cons.
        auto.
  Qed.

  (** ∀ l, l', NoDup (l ++ l') ⇒ NoDup l ∧ NoDup l'. *)

  Lemma nodup_app {A : Type} :
    forall l l' : list A,
      NoDup (l ++ l') -> NoDup l /\ NoDup l'.
  Proof.
    intros l l'; intro Hnodup_app; split.
    - induction l.
      + apply NoDup_nil.
      + apply NoDup_cons;
          simpl in Hnodup_app;
          apply NoDup_cons_iff in Hnodup_app;
          elim Hnodup_app; intros Hnot_in_concat Hnodup_app'.
        -- intro.
           apply or_introl with (B := In a l') in H.
           apply in_app_iff in H.
           elim Hnot_in_concat; assumption.
        -- apply (IHl Hnodup_app').
           
    - induction l'.
      + apply NoDup_nil.
      + apply NoDup_cons;
          apply NoDup_remove in Hnodup_app;
          elim Hnodup_app; intros Hnodup_app' Hnot_in_concat.
        -- intro.
           apply or_intror with (A := In a l) in H.
           apply in_app_iff in H.
           elim Hnot_in_concat; assumption.
        -- apply (IHl' Hnodup_app').
           
  Qed.

  (** ∀ l, ll, NoDup (l ++ l') ⇒ 
    ∀ a ∈ l ⇒ a ∉ l'. *)

  Lemma nodup_app_not_in {A : Type} :
    forall l l': list A,
      NoDup (l ++ l') ->
      forall a : A, In a l -> ~In a l'.
  Proof.
    intros l l' Hnodup a Hin.
    induction l'.
    - simpl; auto.
    - apply not_in_cons.
      apply NoDup_remove in Hnodup.
      elim Hnodup; intros Hnodup_app Hnot_in.
      split.
      + intro; elim Hnot_in; apply in_or_app; left.
        rewrite <- H; assumption.
      + apply IHl'; assumption.
  Qed.

  (** ∀ ll : list (list), NoDup (concat ll) ⇒ ∀ l ∈ ll, NoDup l. *)

  Lemma nodup_concat_gen {A : Type} :
    forall ll : list (list A),
      NoDup (List.concat ll) ->
      forall l : list A, In l ll -> NoDup l.
  Proof.
    intros ll Hnodup_concat l Hin.
    induction ll.
    - inversion Hin.
    - apply in_inv in Hin;
        elim Hin;
        rewrite concat_cons in Hnodup_concat;
        apply nodup_app in Hnodup_concat;
        elim Hnodup_concat;
        intros Hnodup_a Hnodup_concat'.
      + intro Heq; rewrite Heq in Hnodup_a; assumption.
      + intro Hin_ll; apply (IHll Hnodup_concat' Hin_ll).
  Qed.

  (** If one element a is not in the list l and another element b 
    is in the list l then a and b are different. *)

  Lemma not_in_in_diff {A : Type} :
    forall (a b : A) (l : list A), ~In a l /\ In b l -> a <> b.
  Proof.
    intros.
    elim H; intros.
    intro.
    rewrite H2 in H0.
    contradiction.
  Qed.

  (** ∀ a, a ∉ l ∧ a ∉ l' ⇒ a ∉ (l ++ l') *)

  Lemma not_in_app {A : Type} :
    forall (a : A) (l l' : list A),
      ~In a l /\ ~In a l' -> ~In a (l ++ l').
  Proof.
    intros a l l' Hnot_in.
    elim Hnot_in; intros Hnot_in_l Hnot_in_l'.
    intro Hin_app.
    apply in_app_or in Hin_app.
    elim Hin_app.
    - intro Hin_l; elim Hnot_in_l; assumption.
    - intro Hin_l'; elim Hnot_in_l'; assumption.
  Qed.

  (** ∀ a, a ∉ (l ++ l') ⇒ a ∉ l ∧ a ∉ l' *)

  Lemma not_app_in {A : Type} :
    forall (a : A) (l l' : list A),
      ~In a (l ++ l') -> ~In a l /\ ~In a l'.
  Proof.
    intros a l l' Hnot_in_app.
    split.
    - induction l.
      + apply in_nil.
      + apply not_in_cons. split.
        -- intro Heq.
           elim Hnot_in_app.
           apply in_or_app.
           left.
           rewrite Heq; apply in_eq.
        -- simpl in Hnot_in_app.
           apply Decidable.not_or in Hnot_in_app.
           elim Hnot_in_app; intros Hdiff Hnot_in_app'.
           apply (IHl Hnot_in_app').
    - induction l.
      + simpl in Hnot_in_app; assumption.
      + simpl in Hnot_in_app.
        apply Decidable.not_or in Hnot_in_app.
        elim Hnot_in_app; intros Hdiff Hnot_in_app'.
        apply (IHl Hnot_in_app').
  Qed.

  (** ∀ a, b, a ≠ b ⇒ a ∉ [b] *)

  Lemma diff_not_in {A : Type} :
    forall a b : A, a <> b -> ~In a [b].
  Proof.
    intros a b Hdiff.
    intro Hin.
    simpl in Hin.
    elim Hin; [ intro Heq; symmetry in Heq; contradiction | auto].
  Qed.

  (** If the two elements are different then
    all pairs built with these elements are different. *)

  Lemma fst_diff_pair_diff {A B : Type} :
    forall (a x : A),
      a <> x -> (forall (b y : B), (a, b) <> (x, y)).
  Proof.
    intros.
    injection; intros.
    contradiction.
  Qed.

  (** 
    ∀ l : A ⨱ B, NoDup (fst (split l)) ⇒     
    ∀ p, p' ∈ l, fst p = fst p' ⇒ p = p'    

    If there are no duplicates in the first elements
    of l, then all pairs with the same first element
    are equal.
   *)

  Lemma nodup_same_pair {A B : Type} :
    forall (l : list (A * B)),
      NoDup (fst (split l)) ->
      forall (p p' : A * B),
        In p l -> In p' l -> fst p = fst p' -> p = p'.
  Proof.
    intro.
    induction l; intros.
    - inversion H0.
    - dependent induction a.
      rewrite fst_split_cons_app in H; simpl in H.
      apply NoDup_cons_iff in H; elim H; intros.
      apply in_inv in H0; elim H0; intros.
      + apply in_inv in H1.
        elim H1; intros.
        -- rewrite <- H5; rewrite <- H6; reflexivity.
        -- rewrite <- H5 in H2.
           dependent destruction p'.
           simpl in H2.
           apply in_fst_split in H6.
           rewrite <- H2 in H6.
           contradiction.
      + apply in_inv in H1.
        elim H1; intros.
        -- rewrite <- H6 in H2.
           dependent destruction p.
           simpl in H2.
           apply in_fst_split in H5.
           rewrite H2 in H5.
           contradiction.
        -- generalize (IHl H4); intro.
           apply (H7 p p' H5 H6 H2).
  Qed.

  (** incl (a :: l) l' ⇒ incl l l' *)

  Lemma incl_cons_inv {A : Type} :
    forall (a : A) (l l' : list A), incl (a :: l) l' -> incl l l'.
  Proof.
    intros a l l' Hincl_cons.
    induction l.
    - unfold incl; intros a' Hin_nil; inversion Hin_nil.
    - apply incl_cons.
      + unfold incl in Hincl_cons.
        assert (In a0 (a :: a0 :: l)) by (apply in_cons; apply in_eq).
        apply (Hincl_cons a0 H).
      + apply IHl. unfold incl.
        intros a' Hin_cons.
        apply in_inv in Hin_cons; elim Hin_cons.
        -- intro Heq; unfold incl in Hincl_cons.
           assert (Hin_cons' : In a (a :: a0 :: l)) by apply in_eq.
           rewrite <- Heq; apply (Hincl_cons a Hin_cons').
        -- intro Hin.
           apply in_cons with (a := a0) in Hin.
           apply in_cons with (a := a) in Hin.
           apply (Hincl_cons a' Hin).
  Qed.

  (** NoDup (l ++ l') ⇒ NoDup (l' ++ l) *)

  Lemma NoDup_app_comm {A : Type} :
    forall (l l' : list A), NoDup (l ++ l') -> NoDup (l' ++ l).
  Proof.
    intros l l' Hnodup.
    induction l'.
    - simpl; rewrite <- app_nil_end in Hnodup; assumption.
    - rewrite <- app_comm_cons. apply NoDup_cons.
      + apply NoDup_remove_2 in Hnodup.
        apply not_app_in in Hnodup.
        apply not_in_app.
        apply and_comm.
        assumption.
      + apply NoDup_remove in Hnodup; elim Hnodup; intros Hnodup' Hnot_in.
        apply (IHl' Hnodup').
  Qed.

  (** (l ++ l') ⊆ m ⇒ (l ⊆ m ∧ l' ⊆ m) *)

  Lemma incl_app_inv {A : Type} :
    forall (l l' m : list A), incl (l ++ l') m -> incl l m /\ incl l' m.
  Proof.
    intros l l' m Hincl_app. split.
    + unfold incl. induction l.
      -- intros a Hin_nil; inversion Hin_nil.
      -- intros a' Hin_cons.
         unfold incl in Hincl_app.
         apply or_introl with (B := In a' l') in Hin_cons.
         apply in_or_app in Hin_cons.
         apply (Hincl_app a' Hin_cons).
    + induction l'.
      -- intros a Hin_nil; inversion Hin_nil.
      -- apply incl_cons.
         ++ unfold incl in Hincl_app.
            assert (In a (l ++ a :: l')) by (apply in_or_app; right; apply in_eq).
            apply (Hincl_app a H).
            
         ++ unfold incl. intros a' Hin.
            apply in_cons with (a := a) in Hin.
            apply or_intror with (A := In a' l) in Hin.
            apply in_or_app in Hin.
            apply (Hincl_app a' Hin).
            
  Qed.

  (** NoDup (l ++ m ++ n) ∧ NoDup o ∧ o ⊆ m ⇒ NoDup (l ++ o ++ n) *)

  Theorem nodup_app_incl {A : Type} :
    forall (l m n o : list A),
      NoDup (l ++ m ++ n) ->
      NoDup o ->
      incl o m ->
      NoDup (l ++ o ++ n).
  Proof.
    intros l m n o Hnodup_lmn Hnodup_o Hincl_om.
    induction o.
    - simpl.
      apply NoDup_app_comm with (l' := (m ++ n)) in Hnodup_lmn.
      rewrite <- app_assoc in Hnodup_lmn.
      apply NoDup_app_comm with (l' := (n ++ l)) in Hnodup_lmn.
      apply nodup_app in Hnodup_lmn.
      elim Hnodup_lmn; intros Hnodup_ln Hnodup_m.
      apply NoDup_app_comm in Hnodup_ln.
      assumption.
    - apply NoDup_app_comm.
      rewrite <- app_assoc.
      rewrite <- app_comm_cons.
      apply NoDup_cons.
      + apply NoDup_cons_iff in Hnodup_o; elim Hnodup_o; intros Hnot_in_o Hnodup_o'.
        apply NoDup_app_comm with (l' := (m ++ n)) in Hnodup_lmn.
        rewrite <- app_assoc in Hnodup_lmn.
        specialize (nodup_app_not_in m (n ++ l) Hnodup_lmn) as Hin_m_not_in_nl.
        assert (Hin_ao : In a (a :: o)) by apply in_eq.
        specialize (Hincl_om a Hin_ao) as Hin_am.
        specialize (Hin_m_not_in_nl a Hin_am) as Hnot_in_nl.
        apply (not_in_app a o (n ++ l) (conj Hnot_in_o Hnot_in_nl)).
      + apply incl_cons_inv in Hincl_om.
        apply NoDup_cons_iff in Hnodup_o; elim Hnodup_o; intros Hnot_in Hnodup_o'.
        specialize (IHo Hnodup_o' Hincl_om) as Hnodup_lon.
        apply NoDup_app_comm in Hnodup_lon.
        rewrite app_assoc.
        assumption.      
  Qed.

  Theorem sub_exists :
    forall n m : nat, exists o : nat, n = o - m.
  Proof.
    intros n m.
    exists (n + m).
    omega.
  Qed.

  (** Lemmas about remove function. *)

  Functional Scheme remove_ind := Induction for remove Sort Prop.

  Lemma not_in_remove_eq {A : Type} :
    forall (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (a  : A)
           (l : list A),
      ~In a l -> remove eq_dec a l = l.
  Proof.
    intros eq_dec a l;
      functional induction (remove eq_dec a l) using remove_ind;
      intros Hnot_in_l.
    - reflexivity.
    - apply not_in_cons in Hnot_in_l; apply proj1 in Hnot_in_l.
      elim Hnot_in_l; reflexivity.
    - apply not_in_cons in Hnot_in_l; apply proj2 in Hnot_in_l.
      specialize (IHl0 Hnot_in_l) as Heq_rm; rewrite Heq_rm; reflexivity.
  Qed.

  Lemma in_remove_iff {A : Type} :
    forall (a  : A)
           (eq_dec : forall (x y : A), {x = y} + {x <> y})
           (x : A)
           (l : list A),
      In a (remove eq_dec x l) <-> In a l /\ a <> x.
  Proof.
    intros a eq_dec x l;
      functional induction (remove eq_dec x l) using remove_ind.
    - split; [auto | intro Hw_in; apply proj1 in Hw_in; inversion Hw_in].
    - split.
      + intro Hin_a_rm.
        rewrite  IHl0 in Hin_a_rm.
        split; [apply in_cons; apply proj1 in Hin_a_rm; assumption |
                apply proj2 in Hin_a_rm; assumption].
      + intro Hw_in.
        elim Hw_in; intros Hin_ctl Hdiff_ax; clear Hw_in.
        inversion Hin_ctl as [Heq_ax | Hin_tl];
          [ symmetry in Heq_ax; contradiction |
            rewrite IHl0; apply (conj Hin_tl Hdiff_ax) ].
    - split.
      + intro Hin_a_rm; inversion_clear Hin_a_rm as [Heq_ay | Hin_rm_tl].
        -- split.
           ++ rewrite Heq_ay; apply in_eq.
           ++ intro Heq_ax;
                symmetry in Heq_ax;
                rewrite <- Heq_ay in Heq_ax;
                contradiction.
        -- rewrite IHl0 in Hin_rm_tl; split.
           ++ apply in_cons; apply proj1 in Hin_rm_tl; assumption.
           ++ apply (proj2 Hin_rm_tl).
      + intro Hin_a_l.
        elim Hin_a_l; clear Hin_a_l; intros Hin_a_l Hdiff_ax.
        simpl; inversion_clear Hin_a_l as [Heq_ay | Hin_tl].
        -- left; assumption.
        -- right; rewrite IHl0; apply (conj Hin_tl Hdiff_ax). 
  Qed.

  Lemma not_in_not_in_remove {A : Type} :
    forall (a  : A) (l : list A),
      ~In a l ->
      forall (x : A)
             (eq_dec : forall (x y : A), {x = y} + {x <> y}),
        ~In a (remove eq_dec x l).
  Proof.
    intros a l Hnot_in_a_l x eq_dec;
      functional induction (remove eq_dec x l) using remove_ind.
    - apply in_nil.
    - rewrite (not_in_cons a y tl) in Hnot_in_a_l; apply proj2 in Hnot_in_a_l.
      apply (IHl0 Hnot_in_a_l).
    - rewrite not_in_cons; split.
      + rewrite (not_in_cons a y tl) in Hnot_in_a_l; apply proj1 in Hnot_in_a_l; assumption.
      + rewrite (not_in_cons a y tl) in Hnot_in_a_l; apply proj2 in Hnot_in_a_l.
        apply (IHl0 Hnot_in_a_l).
  Qed.

  (** If list l has no duplicates then removing one element from list l
    preserves this property. *)

  Lemma nodup_if_remove {A : Type} :
    forall (l : list A),
      NoDup l ->
      forall (a : A)
             (eq_dec : forall (x y : A), {x = y} + {x <> y}),
        NoDup (remove eq_dec a l).
  Proof.
    intros l Hnodup_l a eq_dec;
      functional induction (remove eq_dec a l) using remove_ind.
    - apply NoDup_nil.
    - rewrite NoDup_cons_iff in Hnodup_l;
        apply proj2 in Hnodup_l;
        apply (IHl0 Hnodup_l).
    - apply NoDup_cons.
      + rewrite NoDup_cons_iff in Hnodup_l; apply proj1 in Hnodup_l.
        apply (not_in_not_in_remove y tl Hnodup_l a eq_dec).
      + rewrite NoDup_cons_iff in Hnodup_l; apply proj2 in Hnodup_l.
        apply (IHl0 Hnodup_l).
  Qed.

  (** 
    Conditions: 
    - l and m are lists of couples
    - l and m have no duplicates in the first 
      elements of their couples
    - All couples of l are in m
    - The list of first elements of l and m are equal   
      modulo permutation
      
    Conclusion: l and m are equal modulo permutation
    
   *)

  Lemma permutation_fs_permutation {A B : Type} :
    forall (l m : list (A * B)),
      NoDup (fs l) ->
      NoDup (fs m) ->
      incl l m ->
      Permutation (fs l) (fs m) ->
      Permutation l m.
  Proof.
    intros l m Hnodup_fs_l Hnodup_fs_m Hincl Hperm_fs.

    (* Strategy: apply [NoDup_Permutation]. 
     
     Premises:
     - NoDup l
     - NoDup m
     - ∀x, x ∈ l ⇔ x ∈ m 
     *)

    (* Builds ∀x, x ∈ l ⇔ x ∈ m *)
    assert (Hequiv_lm : forall (x : A * B), In x l <-> In x m).
    {
      intros x; split.

      (* x ∈ l ⇒ x ∈ m *)
      - unfold incl in Hincl; apply (Hincl x).

      (* x ∈ m ⇒ x ∈ l *)
      - intros Hin_m.
        destruct x.
        specialize (in_fst_split a b m Hin_m) as Hin_fs_m.
        apply Permutation_sym in Hperm_fs.
        specialize (@Permutation_in A (fs m) (fs l) a Hperm_fs Hin_fs_m) as Hin_fs_l.
        specialize (@in_fst_split_in_pair A B a l Hin_fs_l) as Hex_in_l.
        inversion_clear Hex_in_l as (b' & Hin_ab'_l).
        specialize (Hincl (a, b') Hin_ab'_l) as Hin_ab'_m.

        (* Specializes nodup_same_pair. *)
        assert (Heq_ab : fst (a, b) = fst (a, b')) by auto.
        specialize (nodup_same_pair m Hnodup_fs_m (a, b) (a, b') Hin_m Hin_ab'_m Heq_ab)
          as Heq_ab_ab'.
        injection Heq_ab_ab' as Heq_bb'.

        (* Rewrites b' with b, then QED. *)
        rewrite <- Heq_bb' in Hin_ab'_l; assumption.
    }

    (* Builds NoDup l and NoDup m *)
    apply nodup_fst_split in Hnodup_fs_l.
    apply nodup_fst_split in Hnodup_fs_m.
    
    (* Applies  *)
    apply (NoDup_Permutation Hnodup_fs_l Hnodup_fs_m Hequiv_lm).
  Qed.
  
End InAndNoDupLemmas.

(** ** Tactics for [In] and [NoDup] *)

(** Search for a hypothesis H of the form (incl l l') 
      and a hypothesis H' of the form (In a l).
      If H and H' in the context then apply H a H'
      and name the resulting hypothesis as Hin. *)

Ltac apply_incl Hin :=
  lazymatch goal with
  | [ H: incl ?l ?l' |- _ ] =>
    lazymatch goal with
    | [H': In ?a l |- _ ] => specialize (H a H') as Hin
    | _ => fail "No hypotheses of the form (In ?a ?l) in the context"
    end
  | _ => fail "No hypotheses of the form (incl ?l ?l') in the context"
  end.

(** If Hincl_fs is a the form (incl (fst (split (?a, ?b) :: _)) _)
    then rewrites Hincl_fs in (incl (fst (split _))), i.e removes
    the head. *)

Ltac incl_rm_hd_fs Hincl_fs :=
  match Hincl_fs with
  | ?H: incl (fst (split ((_, _) :: _))) _ =>
    rewrite fst_split_cons_app in Hincl_fs;
    simpl in Hincl_fs;
    apply incl_cons_inv in Hincl_fs
  | _ => fail "Argument is not of the form (incl (fst (split (?a, ?b) :: _)) _)"
  end.

Ltac apply_nodup_same_pair :=

  lazymatch goal with
  | [ Hin_p_l: In (?x, ?y) ?l, Hin_p'_l: In (?x, ?z) ?l, Hnodup_l: NoDup (fst (split ?l)) |- _ ] =>
    assert (Heq_fs_pair : fst (x, y) = fst (x, z)) by (simpl; auto);
    specialize (nodup_same_pair l Hnodup_l (x, y) (x, z) Hin_p_l Hin_p'_l Heq_fs_pair);
    intros Heq_pairs;
    clear Heq_fs_pair
  | _ => fail "Missing hypotheses: In ?p ?l or In ?p' ?l or NoDup (fst (split ?l))"
  end.

(**  *)

Ltac contradiction_with_nodup_same_pair l p p' Hin_p_l Hin_p'_l :=

  (* Checks that arguments are well-typed. *)
  lazymatch Hin_p_l with
  | ?H: In p l =>
    lazymatch Hin_p'_l with
    | ?H': In p' l =>
      lazymatch goal with
      | [ Hnodup: NoDup (fst (split l)) |- _ ] =>
        
        (* Specializes nodup_same_pair then shows a contradiction. *)
        assert (Heq_fs_pair : fst p = fst p') by (simpl; auto);
        specialize (nodup_same_pair l Hnodup p p' Hin_p_l Hin_p'_l Heq_fs_pair);
        intros Heq_pp';
        (injection Heq_pp' as Heq_snd_pp'; inversion Heq_snd_pp') || auto
                                                                  
      | _ => fail "No hypothesis of the form NoDup (fst (split l))"
      end
    | _ => fail "Argument is not of the form In (?a, ?b) ?l" 
    end
  | _ => fail "Argument is not of the form In (?a, ?b) ?l"
  end.

(** Looks for a hypothesis of the form [NoDup (?a :: ?l)]
    in the context, and deduces [~In ?a ?l] from it. 
    
    Produces a new hypothesis [Hnot_in_tl : ~In ?a ?l]
    in the context. *)

Ltac deduce_nodup_hd_not_in :=
  match goal with
  | [ Hnodup: NoDup (?a :: ?l) |- _ ] =>
    let Hnot_in := fresh "Hnot_in_tl" in
    assert (Hnot_in := Hnodup);
    rewrite NoDup_cons_iff in Hnot_in;
    apply proj1 in Hnot_in
  | _ => fail "No hypothesis of the form 'NoDup (?a :: ?l)'"
  end.

(** *** Lemmas using the above tactics . *)

(** Proves the equivalence between to list 
      of couples l' and l'', with some hypotheses
      on these two lists.
 *)

Lemma eq_if_eq_fs {A B : Type} :
  forall (l l' l'' : list (A * B)),
    (forall (a : A)
            (b : B),
        In (a, b) l -> exists (b' : B), In (a, b') l' /\ In (a, b') l'') ->
    fst (split l) = fst (split l') ->
    fst (split l) = fst (split l'') ->
    NoDup (fst (split l)) ->
    NoDup (fst (split l')) ->
    NoDup (fst (split l'')) ->
    forall (x : A) (y : B), In (x, y) l' <-> In (x, y) l''.
Proof.
  intros l l' l'' Hin_l_in_ll Heq_fs_ll' Heq_fs_ll''
         Hnodup_l Hnodup_l' Hnodup_l'' x y.

  (* Proves both side of the implication. *)
  split;
    let deduce_goal list Heq_fs_list := 
        (intros Hin_xy_list;
         specialize (in_fst_split x y list Hin_xy_list) as Hin_x_fs_list;
         rewrite <- Heq_fs_list in Hin_x_fs_list;
         apply (in_fst_split_in_pair x l) in Hin_x_fs_list;
         inversion_clear Hin_x_fs_list as (z & Hin_xz_l);
         specialize (Hin_l_in_ll x z Hin_xz_l) as Hex_in_ll;
         inversion_clear Hex_in_ll as (c & Hw_in_xc_ll);
         inversion_clear Hw_in_xc_ll as (Hin_xc_list & Hin_xc_list');
         apply_nodup_same_pair;
         injection Heq_pairs as Heq_yc;
         rewrite Heq_yc;
         assumption) in
    (deduce_goal l' Heq_fs_ll' || deduce_goal l'' Heq_fs_ll'').
Qed.

(** Proves the equivalence between to list 
    of couples m and n, with some hypotheses
    on these two lists.
 *)

Lemma equiv_if_perm_and_nodup_fs {A B : Type} :
  forall (l m n : list (A * B)),
    (forall (a : A)
            (b : B),
        In (a, b) l -> exists (b' : B), In (a, b') m /\ In (a, b') n) ->
    Permutation (fs l) (fs m) ->
    Permutation (fs l) (fs n) ->
    NoDup (fs l) ->
    NoDup (fs m) ->
    NoDup (fs n) ->
    forall (x : A) (y : B), In (x, y) m <-> In (x, y) n.
Proof.
  intros l m n Hin_l_in_mn Hperm_fs_lm Hperm_fs_ln
         Hnodup_l Hnodup_m Hnodup_n x y.
  
  (* Proves both side of the implication. *)
  split;
    let deduce_goal list Heq_fs_list := 
        (intros Hin_xy_list;
         specialize (in_fst_split x y list Hin_xy_list) as Hin_x_fs_list;
         rewrite <- Heq_fs_list in Hin_x_fs_list;
         apply (in_fst_split_in_pair x l) in Hin_x_fs_list;
         inversion_clear Hin_x_fs_list as (z & Hin_xz_l);
         specialize (Hin_l_in_mn x z Hin_xz_l) as Hex_in_ll;
         inversion_clear Hex_in_ll as (c & Hw_in_xc_ll);
         inversion_clear Hw_in_xc_ll as (Hin_xc_list & Hin_xc_list');
         unfold fs in *;
         apply_nodup_same_pair;
         injection Heq_pairs as Heq_yc;
         rewrite Heq_yc;
         assumption) in
    (deduce_goal m Hperm_fs_lm || deduce_goal n Hperm_fs_ln).
Qed.

