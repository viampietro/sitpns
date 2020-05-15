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

Require Import ListsPlus.
Require Import simpl.Sitpn.
Require Import simpl.SitpnSemantics.

(** Renames all hypotheses resulting of the decomposition 
    of the IsWelldefinedSitpn predicate. *)

Ltac rename_well_defined_sitpn :=
  match goal with
  | [ H: NoDupPlaces ?sitpn |- _ ] =>
    let Hnodup_places := fresh "Hnodup_places" in
    rename H into Hnodup_places
  | _ => idtac "No hypothesis of the form NoDupPlaces ?sitpn"
  end;
  match goal with
  | [ H: NoDupTranss ?sitpn |- _ ] =>
    let Hnodup_transs := fresh "Hnodup_transs" in
    rename H into Hnodup_transs
  | _ => idtac "No hypothesis of the form NoDupTranss ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownInPriorityGroups ?sitpn |- _ ] =>
    let Hno_unk_pgroups := fresh "Hno_unk_pgroups" in
    rename H into Hno_unk_pgroups
  | _ => idtac "No hypothesis of the form NoUnknownInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: NoIntersectInPriorityGroups ?sitpn |- _ ] =>
    let Hno_inter := fresh "Hno_inter" in
    rename H into Hno_inter
  | _ => idtac "No hypothesis of the form NoIntersectInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: AreWellFormedTimeIntervals ?sitpn |- _ ] =>
    let Hwell_formed_itvals := fresh "Hwell_formed_itvals" in
    rename H into Hwell_formed_itvals
  | _ => idtac "No hypothesis of the form AreWellFormedTimeIntervals ?sitpn"
  end;
  match goal with
  | [ H: NoDupConditions ?sitpn |- _ ] =>
    let Hnodup_cond := fresh "Hnodup_cond" in
    rename H into Hnodup_cond
  | _ => idtac "No hypothesis of the form NoDupConditions ?sitpn"
  end;
  match goal with
  | [ H: NoDupActions ?sitpn |- _ ] =>
    let Hnodup_ac := fresh "Hnodup_ac" in
    rename H into Hnodup_ac
  | _ => idtac "No hypothesis of the form NoDupActions ?sitpn"
  end;
  match goal with
  | [ H: NoDupFunctions ?sitpn |- _ ] =>
    let Hnodup_fun := fresh "Hnodup_fun" in
    rename H into Hnodup_fun
  | _ => idtac "No hypothesis of the form NoDupFunctions ?sitpn"
  end;
  match goal with
  | [ H: NoDupInNeighbours ?sitpn |- _ ] =>
    let Hnodup_neigh := fresh "Hnodup_neigh" in
    rename H into Hnodup_neigh
  | _ => idtac "No hypothesis of the form NoDupInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedPlace ?sitpn |- _ ] =>
    let Hiso_place := fresh "Hiso_place" in
    rename H into Hiso_place
  | _ => idtac "No hypothesis of the form NoIsolatedPlace ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownPlaceInNeighbours ?sitpn |- _ ] =>
    let Hunk_pl_neigh := fresh "Hunk_pl_neigh" in
    rename H into Hunk_pl_neigh
  | _ => idtac "No hypothesis of the form NoUnknownPlaceInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedTrans ?sitpn |- _ ] =>
    let Hiso_trans := fresh "Hiso_trans" in
    rename H into Hiso_trans
  | _ => idtac "No hypothesis of the form NoIsolatedTrans ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPreEdges ?sitpn |- _ ] =>
    let Hwell_def_pre := fresh "Hwell_def_pre" in
    rename H into Hwell_def_pre
  | _ => idtac "No hypothesis of the form AreWellDefinedPreEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedTestEdges ?sitpn |- _ ] =>
    let Hwell_def_test := fresh "Hwell_def_test" in
    rename H into Hwell_def_test
  | _ => idtac "No hypothesis of the form AreWellDefinedTestEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedInhibEdges ?sitpn |- _ ] =>
    let Hwell_def_inhib := fresh "Hwell_def_inhib" in
    rename H into Hwell_def_inhib
  | _ => idtac "No hypothesis of the form AreWellDefinedInhibEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPostEdges ?sitpn |- _ ] =>
    let Hwell_def_post := fresh "Hwell_def_post" in
    rename H into Hwell_def_post
  | _ => idtac "No hypothesis of the form AreWellDefinedPostEdges ?sitpn"
  end.

(** Renames all hypotheses resulting of the decomposition 
    of the IsWelldefinedSitpn predicate. *)

Ltac clear_well_defined_sitpn :=
  match goal with
  | [ H: NoDupPlaces ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupPlaces ?sitpn"
  end;
  match goal with
  | [ H: NoDupTranss ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupTranss ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownInPriorityGroups ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoUnknownInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: NoIntersectInPriorityGroups ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoIntersectInPriorityGroups ?sitpn"
  end;
  match goal with
  | [ H: AreWellFormedTimeIntervals ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellFormedTimeIntervals ?sitpn"
  end;
  match goal with
  | [ H: NoDupConditions ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupConditions ?sitpn"
  end;
  match goal with
  | [ H: NoDupActions ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupActions ?sitpn"
  end;
  match goal with
  | [ H: NoDupFunctions ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupFunctions ?sitpn"
  end;
  match goal with
  | [ H: NoDupInNeighbours ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDupInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedPlace ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoIsolatedPlace ?sitpn"
  end;
  match goal with
  | [ H: NoUnknownPlaceInNeighbours ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoUnknownPlaceInNeighbours ?sitpn"
  end;
  match goal with
  | [ H: NoIsolatedTrans ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoIsolatedTrans ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPreEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedPreEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedTestEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedTestEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedInhibEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedInhibEdges ?sitpn"
  end;
  match goal with
  | [ H: AreWellDefinedPostEdges ?sitpn |- _ ] => clear H
  | _ => idtac "No hypothesis of the form AreWellDefinedPostEdges ?sitpn"
  end.

Ltac explode_well_defined_sitpn :=
  match goal with
  | [ H: IsWellDefinedSitpn _ |- _ ] =>
    assert (H' := H); 
    unfold IsWellDefinedSitpn in H;
    decompose [and] H;
    intros;
    rename_well_defined_sitpn;
    clear H;
    rename H' into Hwell_def_sitpn
  | _ => fail "No hypothesis matching the form IsWellDefinedSitpn ?sitpn"
  end.

(** Renames all hypotheses resulting of the decomposition
    of IsWellDefinedSitpnState. *)

Ltac rename_well_defined_sitpn_state :=
  match goal with
  | [ H: incl ?s.(Sitpn.fired) (transs ?sitpn) |- _ ] =>
    let Hincl_state_fired_transs := fresh "Hincl_state_fired_transs" in
    rename H into Hincl_state_fired_transs
  | _ => idtac "No hypothesis of the form incl (fired ?s) (transs ?sitpn) found"
  end;
  match goal with
  | [ H: NoDup ?s.(Sitpn.fired) |- _ ] =>
    let Hnodup_state_fired := fresh "Hnodup_state_fired" in
    rename H into Hnodup_state_fired
  | _ => idtac "No hypothesis of the form NoDup (fired ?s) found"
  end;
  match goal with
  | [ H: ?sitpn.(Sitpn.places) = fst (split (Sitpn.marking ?s))
      |- _ ] =>
    let Hwf_state_marking := fresh "Hwf_state_marking" in
    rename H into Hwf_state_marking
  | _ => idtac "No hypothesis of the form (places ?sitpn) = fst (split (marking ?s)) found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.d_intervals))))
      |- _ ] =>
    let Hwf_state_ditvals := fresh "Hwf_state_ditvals" in
    rename H into Hwf_state_ditvals
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ I(t) ≠ ∅' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.d_intervals ?s))) |- _ ] =>
    let Hnodup_state_ditvals := fresh "Hnodup_state_ditvals" in
    rename H into Hnodup_state_ditvals
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (d_intervals s)))' found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.reset))))
      |- _ ] =>
    let Hwf_state_reset := fresh "Hwf_state_reset" in
    rename H into Hwf_state_reset
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ t ∈ reset' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.reset ?s))) |- _ ] =>
    let Hnodup_state_reset := fresh "Hnodup_state_reset" in
    rename H into Hnodup_state_reset
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (reset s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.conditions ?sitpn) = fst (split (Sitpn.cond_values ?s)) |- _ ] =>
    let Hwf_state_condv := fresh "Hwf_state_condv" in
    rename H into Hwf_state_condv
  | _ => idtac "No hypothesis of the form 'C = (fst (split (cond_values s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.actions ?sitpn) = fst (split (Sitpn.exec_a ?s)) |- _ ] =>
    let Hwf_state_execa := fresh "Hwf_state_execa" in
    rename H into Hwf_state_execa
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_a s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.functions ?sitpn) = fst (split (Sitpn.exec_f ?s)) |- _ ] =>
    let Hwf_state_execf := fresh "Hwf_state_execf" in
    rename H into Hwf_state_execf
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_f s)))' found"
  end.

(** Clears all hypotheses resulting of the decomposition
    of IsWellDefinedSitpnState. *)

Ltac clear_well_defined_sitpn_state :=
  match goal with
  | [ H: incl ?s.(Sitpn.fired) (transs ?sitpn) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form incl (fired ?s) (transs ?sitpn) found"
  end;
  match goal with
  | [ H: NoDup ?s.(Sitpn.fired) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form NoDup (fired ?s) found"
  end;
  match goal with
  | [ H: ?sitpn.(Sitpn.places) = fst (split (Sitpn.marking ?s))
      |- _ ] => clear H
  | _ => idtac "No hypothesis of the form (places ?sitpn) = fst (split (marking ?s)) found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.d_intervals))))
      |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ I(t) ≠ ∅' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.d_intervals ?s))) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (d_intervals s)))' found"
  end;
  match goal with
  | [ H: (forall (t : Trans),
             In t ?sitpn.(Sitpn.transs) /\
             (Sitpn.s_intervals ?sitpn t) <> None <->
             In t (fst (split ?s.(Sitpn.reset))))
      |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 't ∈ Ti ⇔ t ∈ reset' found"
  end;
  match goal with
  | [ H: NoDup (fst (split (Sitpn.reset ?s))) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'NoDup (fst (split (reset s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.conditions ?sitpn) = fst (split (Sitpn.cond_values ?s)) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'C = (fst (split (cond_values s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.actions ?sitpn) = fst (split (Sitpn.exec_a ?s)) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_a s)))' found"
  end;
  match goal with
  | [ H: (Sitpn.functions ?sitpn) = fst (split (Sitpn.exec_f ?s)) |- _ ] => clear H
  | _ => idtac "No hypothesis of the form 'A = (fst (split (exec_f s)))' found"
  end.

Ltac explode_well_defined_sitpn_state Hwell_def_state :=
  lazymatch Hwell_def_state with
  | ?H : IsWellDefinedSitpnState _ _  =>
    assert (H' := H); 
    unfold IsWellDefinedSitpnState in H;
    decompose [and] H;
    rename_well_defined_sitpn_state;
    clear H;
    rename H' into Hwell_def_state
  | _ => fail "Hwell_def_state is not of the form IsWellDefinedSitpnState"
  end.

(** Deduces In t (transs sitpn) from the context:
    
    - IsDecListCons (t :: tl) pgroup
    - In pgroup (priority_groups sitpn) 
    - IsWellDefinedSitpn sitpn

    Produces a hypothesis Hin_t_transs: In t (transs sitpn) in the context. *)

Ltac deduce_in_transs :=
  lazymatch goal with
  | [H: IsDecListCons (?t :: ?tl) ?pgroup |- _ ] =>
    assert (Hin_t_pgroup := H);
    apply is_dec_list_cons_incl in Hin_t_pgroup;
    specialize (Hin_t_pgroup t (in_eq t tl));
    lazymatch goal with
    | [Hin_pg_pgs: In pgroup (priority_groups ?sitpn) |- _ ] =>
      specialize (in_concat t pgroup (priority_groups sitpn) Hin_t_pgroup Hin_pg_pgs);
      intros Hin_t_transs;
      lazymatch goal with
      | [Hwd_sitpn: IsWellDefinedSitpn sitpn |- _] =>
        explode_well_defined_sitpn;
        unfold NoUnknownInPriorityGroups in *;
        lazymatch goal with
        | [Hno_unk_pgroups: Permutation _ _ |- _] =>
          rewrite <- Hno_unk_pgroups in Hin_t_transs;
          clear_well_defined_sitpn;
          clear Hno_unk_pgroups
        | _ => fail "No hypothesis of the form 'Permutation _ _' found"
        end
      | _ => fail "No hypothesis of the form IsWellDefinedSitpn ?sitpn found"
      end
    | _ => fail "No hypothesis of the form 'In ?pgroup  (priority_groups ?sitpn)' found"
    end
  | _ => fail "No hypothesis of the form 'IsDecListCons (?t :: ?tl) ?pgroup' found" 
  end.

(** Deduces NoDup (t :: tl) from the context:
    
    - IsDecListCons (t :: tl) pgroup
    - In pgroup (priority_groups sitpn) 
    - IsWellDefinedSitpn sitpn

    Produces a hypothesis Hnodup_ttail: NoDup (t :: tl) in the context. *)

Ltac deduce_nodup_in_dec_pgroup :=          
  lazymatch goal with
  |  [ Hwd: IsWellDefinedSitpn ?sitpn,
            His_dec: IsDecListCons (?t :: ?tail) ?pgroup,
            Hin_pg_pgs: In ?pgroup (priority_groups ?sitpn)               
       |- _ ] =>
     assert (Hnodup_pg := Hin_pg_pgs);
     assert (Hnodup_ttail' := His_dec);
     explode_well_defined_sitpn;
     lazymatch goal with
     | [ Hno_inter: NoIntersectInPriorityGroups sitpn |- _ ] =>
       apply (nodup_concat_gen (priority_groups sitpn) Hno_inter pgroup) in Hnodup_pg;
       apply (nodup_is_dec_list_cons Hnodup_pg) in Hnodup_ttail';
       assert (Hnodup_ttail := Hnodup_ttail');

       clear_well_defined_sitpn;
       clear Hno_inter;
       clear Hnodup_pg;
       clear Hnodup_ttail'
     | _ => fail "No hypothesis of the form 'NoIntersectInPriorityGroups ?sitpn' found"
     end
  | _ => fail "Mandatory hypotheses are missing in the context:
               IsWellDefinedSitpn ?sitpn or IsDecListCons (?t :: ?tl) ?pgroup or In ?pgroup (priority_groups ?sitpn)"
  end.

(** Deduces NoDup (fst (split (marking s))) from context: 

    - IsWellDefinedSitpn sitpn
    - IsWellDefinedSitpnState sitpn s

 *)

Ltac deduce_nodup_state_marking :=
  lazymatch goal with
  |  [ Hwd: IsWellDefinedSitpn ?sitpn,
       Hwd_state: IsWellDefinedSitpnState ?sitpn ?s
       |- _ ] =>
     explode_well_defined_sitpn;
     explode_well_defined_sitpn_state Hwd_state;
     
     lazymatch goal with
     | [ Hnodup_places: NoDupPlaces _, Hwf_state_marking: (places _) = fst (split (marking _)) |- _ ] =>
       unfold NoDupPlaces in Hnodup_places;
       rewrite Hwf_state_marking in Hnodup_places;
       assert (Hnodup_fs_ms := Hnodup_places);
       clear_well_defined_sitpn;
       clear_well_defined_sitpn_state;
       clear Hnodup_places
     | _ => fail "No Hypotheses of the form 'NoDupPlaces' or '(places _) = fst (split _)'"
     end
  | _ => fail "No Hypotheses of the form 'IsWellDefinedSitpn' or 'IsWellDefinedSitpnState'"
  end.

(** Variant of deduce_nodup_state_marking *)

Ltac deduce_nodup_state_marking_for sitpn_state :=
  lazymatch goal with
  |  [ Hwd: IsWellDefinedSitpn ?sitpn,
            Hwd_state: IsWellDefinedSitpnState ?sitpn sitpn_state
       |- _ ] =>
     explode_well_defined_sitpn;
     explode_well_defined_sitpn_state Hwd_state;
     
     lazymatch goal with
     | [ Hnodup_places: NoDupPlaces _, Hwf_state_marking: (places _) = fst (split (marking sitpn_state)) |- _ ] =>
       unfold NoDupPlaces in Hnodup_places;
       rewrite Hwf_state_marking in Hnodup_places;
       let Hnodup_fs_ms := fresh "Hnodup_fs_ms" in
       assert (Hnodup_fs_ms := Hnodup_places);
       clear_well_defined_sitpn;
       clear_well_defined_sitpn_state;
       clear Hnodup_places
     | _ => fail "No Hypotheses of the form 'NoDupPlaces' or '(places _) = fst (split _)'"
     end
  | _ => fail "No Hypotheses of the form 'IsWellDefinedSitpn' or 'IsWellDefinedSitpnState'"
  end.

Tactic Notation "deduce_nodup_state_marking" "for" ident(sitpn_state)  :=
  deduce_nodup_state_marking_for sitpn_state.

(** Deduces equality hypotheses between two SitpnState which
    are well-defined regarding the same sitpn. *)

Ltac deduce_eq_from_wd_states :=
  lazymatch goal with
  | [
    Hwd_s: IsWellDefinedSitpnState ?sitpn ?s,
           Hwd_state: IsWellDefinedSitpnState ?sitpn ?state
    |- _
  ] =>

    (* Explodes IsWellDefinedSitpnState predicates. *)
    explode_well_defined_sitpn_state Hwd_s;
    explode_well_defined_sitpn_state Hwd_state;

    (* Deduces equalities between the two states. *)
    lazymatch goal with
    | [ Hwf_marking_s: places ?sitpn = fst (split (marking ?s)),
        Hwf_marking_state: places ?sitpn = fst (split (marking ?state)),
        Hwf_condv_s: conditions ?sitpn = fst (split (cond_values ?s)),
        Hwf_condv_state: conditions ?sitpn = fst (split (cond_values ?state)),
        Hwf_actions_s: actions ?sitpn = fst (split (exec_a ?s)),
        Hwf_actions_state: actions ?sitpn = fst (split (exec_a ?state)),
        Hwf_functions_s: functions ?sitpn = fst (split (exec_f ?s)),
        Hwf_functions_state: functions ?sitpn = fst (split (exec_f ?state))
        |- _ ] =>

      (* Deduces fst (split marking) = fst (split marking) *)
      let Heq_state_marking := fresh "Heq_state_marking" in
      assert (Heq_state_marking : fst (split (marking s)) = fst (split (marking state)))
        by (rewrite <- Hwf_marking_s; rewrite <- Hwf_marking_state; reflexivity);

      (* Deduces fst (split cond_values) = fst (split cond_values) *)
      let Heq_state_condv := fresh "Heq_state_condv" in
      assert (Heq_state_condv : fst (split (cond_values s)) = fst (split (cond_values state)))
        by (rewrite <- Hwf_condv_s; rewrite <- Hwf_condv_state; reflexivity);

      (* Deduces fst (split exec_a) = fst (split exec_a) *)
      let Heq_state_actions := fresh "Heq_state_actions" in
      assert (Heq_state_actions : fst (split (exec_a s)) = fst (split (exec_a state)))
        by (rewrite <- Hwf_actions_s; rewrite <- Hwf_actions_state; reflexivity);

      (* Deduces fst (split exec_f) = fst (split exec_f) *)
      let Heq_state_functions := fresh "Heq_state_functions" in
      assert (Heq_state_functions : fst (split (exec_f s)) = fst (split (exec_f state)))
        by (rewrite <- Hwf_functions_s; rewrite <- Hwf_functions_state; reflexivity);

      (* Clears the context. *)
      do 2 clear_well_defined_sitpn_state
         
    | _ => fail "No hypotheses resulting in the explosion of IsWellDefinedSitpnState predicate"
    end
  | _ => fail "No hypotheses matching the form 'IsWellDefinedSitpnState ?sitpn _'"
  end.


(** Variant of deduce_eq_from_wd_states. *)

Ltac deduce_eq_from_wd_states_for s state :=
  lazymatch goal with
  | [
    Hwd_s: IsWellDefinedSitpnState ?sitpn s,
           Hwd_state: IsWellDefinedSitpnState ?sitpn state
    |- _
  ] =>

    (* Explodes IsWellDefinedSitpnState predicates. *)
    explode_well_defined_sitpn_state Hwd_s;
    explode_well_defined_sitpn_state Hwd_state;

    (* Deduces equalities between the two states. *)
    lazymatch goal with
    | [ Hwf_marking_s: places ?sitpn = fst (split (marking s)),
        Hwf_marking_state: places ?sitpn = fst (split (marking state)),
        Hwf_condv_s: conditions ?sitpn = fst (split (cond_values s)),
        Hwf_condv_state: conditions ?sitpn = fst (split (cond_values state)),
        Hwf_actions_s: actions ?sitpn = fst (split (exec_a s)),
        Hwf_actions_state: actions ?sitpn = fst (split (exec_a state)),
        Hwf_functions_s: functions ?sitpn = fst (split (exec_f s)),
        Hwf_functions_state: functions ?sitpn = fst (split (exec_f state))
        |- _ ] =>

      (* Deduces fst (split marking) = fst (split marking) *)
      let Heq_state_marking := fresh "Heq_state_marking" in
      assert (Heq_state_marking : fst (split (marking s)) = fst (split (marking state)))
        by (rewrite <- Hwf_marking_s; rewrite <- Hwf_marking_state; reflexivity);

      (* Deduces fst (split cond_values) = fst (split cond_values) *)
      let Heq_state_condv := fresh "Heq_state_condv" in
      assert (Heq_state_condv : fst (split (cond_values s)) = fst (split (cond_values state)))
        by (rewrite <- Hwf_condv_s; rewrite <- Hwf_condv_state; reflexivity);

      (* Deduces fst (split exec_a) = fst (split exec_a) *)
      let Heq_state_actions := fresh "Heq_state_actions" in
      assert (Heq_state_actions : fst (split (exec_a s)) = fst (split (exec_a state)))
        by (rewrite <- Hwf_actions_s; rewrite <- Hwf_actions_state; reflexivity);

      (* Deduces fst (split exec_f) = fst (split exec_f) *)
      let Heq_state_functions := fresh "Heq_state_functions" in
      assert (Heq_state_functions : fst (split (exec_f s)) = fst (split (exec_f state)))
        by (rewrite <- Hwf_functions_s; rewrite <- Hwf_functions_state; reflexivity);

      (* Clears the context. *)
      do 2 clear_well_defined_sitpn_state
         
    | _ => fail "No hypotheses resulting in the explosion of IsWellDefinedSitpnState predicate"
    end
  | _ => fail "No hypotheses matching the form 'IsWellDefinedSitpnState ?sitpn _'"
  end.

Tactic Notation "deduce_eq_from_wd_states" "for" ident(sitpn_state) ident(sitpn_s)  :=
  deduce_nodup_state_marking_for sitpn_state sitpn_s.

(** Deduces [In a m] from [IsDecListCons (a :: l) m] *)

Ltac deduce_in_from_is_dec_list_cons_as hyp_is_dec intro_pattern :=
  lazymatch type of hyp_is_dec with
  | IsDecListCons (?a :: ?l) ?m =>
    specialize (is_dec_list_cons_incl hyp_is_dec);
    intros Hincl;
    assert (Hin_eq : In a (a :: l)) by (apply in_eq);
    specialize (Hincl a Hin_eq) as intro_pattern;
    clear Hin_eq
  | _ => fail "Expected parameter of type IsDecListCons (?a :: ?l) ?m"
  end.

Tactic Notation "deduce_in_from_is_dec_list_cons" ident(hyp_is_dec) "as" simple_intropattern(intro_pattern) :=
  deduce_in_from_is_dec_list_cons_as hyp_is_dec intro_pattern.

