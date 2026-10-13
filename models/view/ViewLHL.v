(** * VLHL in the paper's form, and the free choice of presentation (P1)

    The paper's VLHL (§6.2, App. I, Defs. I.7–I.8, Thms. I.9 and I.11)
    works over relaxed traces with futures.  Its possibility is a pair
    [(t, π)]: [t] is a view trace in [view(ν_F)] and [π] gives each pending
    overlay call its phase [inv f | lin (f, h) | lin (f, r, h)].
    VT-Invoke chooses a stamp [h] and extends [t] with the invocation;
    VT-Return extends it with the response.  Underlay steps range over
    [view(ν_E)].

    This file shows that this is the global simulation of [RelaxedGSim]
    (S1) with one particular choice of abstract LTS on each side:

    - [VT nu] (Part 2) is the LTS of view traces.  Its state is a trace
      with a stamp per call key; a step appends one event and must keep
      the trace in [view_rt] (Def. I.4 plus the real-time condition that
      Thm. I.11 needs, see [PrefixView]).  Stamps of keys already in the
      trace never change ([stable]).
    - With [VF := VT nuF], the two-phase pool of [RelaxedPossibility] is
      [π]: [ls_inv], [ls_lini], [ls_linr] are [inv f], [lin (f, h)],
      [lin (f, r, h)], with [h] kept in the stamp map.  The abstract
      steps on [InvEv] / [ResEv] are VT-Invoke / VT-Return.
      [poss_invoke] / [poss_return] are VS-Invoke / VS-Return.
    - With [VE := VT nuE], the universally quantified underlay steps of
      [GSimRel] are the UStep clause over [view(ν_E)].

    Differences from the paper: calls are keyed by (thread, handle), so a
    thread may have several pending calls (futures); every step of the
    simulation is universal (the paper's OStep is existential); and
    [view_rt] adds real time.

    Part 1 defines what it means for an abstract LTS to be a presentation
    of a relaxed specification [(ν, I)]:

    - [sound_pres]: every complete well-formed trace it produces is
      relaxed-linearizable.  This is what an overlay presentation needs.
    - [complete_pres]: it produces every prefix of every complete
      relaxed-linearizable trace.  This is what an underlay presentation
      needs.
    - [implements]: every trace of the actual underlay is such a prefix.
      This is the only thing a layer assumes about the layer below.

    Part 3 moves a module execution from one underlay LTS to another
    along trace inclusion ([exec_transport]).

    Part 4 states P1 ([presentation_choice]): a global simulation over
    any complete underlay presentation and any sound overlay presentation
    proves that the overlay of every complete execution, over every
    underlay that implements [(νE, IE)], is relaxed-linearizable to
    [(νF, IF)].  Neither presentation appears in the conclusion or in the
    assumption on the layer below, so adjacent layers may choose
    unrelated presentations of the object they share.

    [vlhl_sound] is the instance [VE := VT nuE], [VF := VT nuF]: the
    paper's Thms. I.9 and I.11 together, with real time added.
    [VT] is a sound presentation ([vt_sound]) and a complete one
    ([vt_complete], which is Prop. I.10 plus prefix closure).

    The two requirements differ, and one presentation can meet one
    without the other.  [VT0] is [VT] without real time, i.e. Def. I.4 as
    printed.  It is complete ([vt0_complete]) but not sound
    ([vt0_not_sound], on the counterexample to Thm. I.11 from
    [PrefixView]).  So the paper's views can present an underlay but
    not an overlay.  [complete_pres_enlarge] and [sound_pres_shrink]
    say how a presentation may be swapped for another along trace
    inclusion. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.

Import ListNotations.

Module ViewLHL.
  Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedTraceLin.
  Import RelaxedPossibility RelaxedModuleSemantics RelaxedGSim.

  (** ** Part 1: presentations of a relaxed specification *)

  Section Presentations.
    Context {E : RelaxedSig.t} (nu : list (Op E) -> Prop).

    (** [u] is a prefix of a complete relaxed-linearizable trace. *)
    Definition rl_prefix (u : list (ThreadEvent E)) : Prop :=
      exists w, PrefixView.wf (u ++ w) /\ PrefixView.complete (u ++ w) /\
        rel_lin (@PrefixView.sel E) (u ++ w) (semi_independent E) nu.

    Definition sound_pres (V : LTS E) (v0 : State V) : Prop :=
      forall T v, vf_path V v0 T v -> PrefixView.wf T -> PrefixView.complete T ->
        rel_lin (@PrefixView.sel E) T (semi_independent E) nu.

    Definition complete_pres (V : LTS E) (v0 : State V) : Prop :=
      forall u, rl_prefix u -> exists v, vf_path V v0 u v.

    Definition implements (U : LTS E) (q0 : State U) : Prop :=
      forall u q, vf_path U q0 u q -> rl_prefix u.

    Lemma rl_prefix_nil (nu_nil : nu []) : rl_prefix [].
    Proof.
      exists []. simpl. split; [|split].
      - split; [|split].
        + intros i j k op op' (x & Hx & _). destruct i; discriminate.
        + intros i j k op op' r r' (x & Hx & _). destruct i; discriminate.
        + intros j k op r (x & Hx & _). destruct j; discriminate.
      - intros i k op (x & Hx & _). destruct i; discriminate.
      - exists []. split; [exact nu_nil|]. split; [constructor|]. split; [|split].
        + intros o [].
        + intros i k op (x & Hx & _). destruct i; discriminate.
        + intros o o' [].
    Qed.


    (** Changing a presentation: a complete presentation stays complete
        when it is enlarged, and a sound one stays sound when it is
        shrunk.  Enlarging or shrinking is trace inclusion, which a
        forward simulation gives ([fsim_traces]). *)
    Definition traces_incl (V : LTS E) (v0 : State V) (V' : LTS E) (v0' : State V') : Prop :=
      forall T v, vf_path V v0 T v -> exists v', vf_path V' v0' T v'.

    Lemma complete_pres_enlarge V v0 V' v0' :
      complete_pres V v0 -> traces_incl V v0 V' v0' -> complete_pres V' v0'.
    Proof. intros Hc Hi u Hu. destruct (Hc u Hu) as (v & Hv). exact (Hi _ _ Hv). Qed.

    Lemma sound_pres_shrink V v0 V' v0' :
      sound_pres V' v0' -> traces_incl V v0 V' v0' -> sound_pres V v0.
    Proof. intros Hs Hi T v Hv. destruct (Hi _ _ Hv) as (v' & Hv'). exact (Hs _ _ Hv'). Qed.

    Lemma fsim_traces (V V' : LTS E) (R : State V -> State V' -> Prop) v0 v0' :
      (forall ev v1 v2 v1', R v1 v1' -> Step V ev v1 v2 -> exists v2', Step V' ev v1' v2' /\ R v2 v2') ->
      R v0 v0' -> traces_incl V v0 V' v0'.
    Proof.
      intros Hsim H0 T v Hp. revert v0' H0.
      induction Hp as [v | v ev v1 T v2 Hs Hp IH]; intros v0' H0.
      - exists v0'. constructor.
      - destruct (Hsim _ _ _ _ H0 Hs) as (v1' & Hs' & H1).
        destruct (IH _ H1) as (v2' & Hp'). exists v2'. econstructor; eauto.
    Qed.
  End Presentations.

  (** ** Part 2: the LTS of view traces *)

  Lemma firstn_app_len {A : Type} (l1 l2 : list A) : firstn (length l1) (l1 ++ l2) = l1.
  Proof. induction l1 as [|x l1 IH]; simpl; [reflexivity | f_equal; exact IH]. Qed.

  Section VT.
    Context {E : RelaxedSig.t} (nu : list (Op E) -> Prop).

    Abbreviation indep := (semi_independent E).
    Abbreviation inv L := (inv_at (@PrefixView.sel E) L).
    Abbreviation res L := (res_at (@PrefixView.sel E) L).

    Record vstate : Type := mkV { v_trace : list (ThreadEvent E); v_stamp : CallKey E -> nat }.

    (** Stamps of keys already invoked do not change. *)
    Definition stable (L : list (ThreadEvent E)) (H H' : CallKey E -> nat) : Prop :=
      forall i k m, inv L i k m -> H' k = H k.

    (** VT-Invoke and VT-Return in one rule: append the event, keeping
        the trace a real-time-respecting view trace.  For an invocation
        the stamp of the new key is chosen here. *)
    Inductive vt_step : ThreadEvent E -> vstate -> vstate -> Prop :=
    | vt_step_intro ev L H H' :
        stable L H H' -> PrefixView.view_rt indep nu H' (L ++ [ev]) ->
        vt_step ev (mkV L H) (mkV (L ++ [ev]) H').

    Definition VT : LTS E := {| State := vstate; Step := vt_step; Error := fun _ _ => False |}.

    (** *** Prefixes of view traces *)

    Lemma view_rt_firstn H L n : PrefixView.view_rt indep nu H L -> PrefixView.view_rt indep nu H (firstn n L).
    Proof.
      intros (((Hw1 & Hw2 & Hw3) & Hpo & Hpre) & Hrt). split; [split; [|split]|].
      - split; [|split].
        + intros i j k op op' Hi Hj. apply PrefixView.inv_firstn in Hi as [_ Hi].
          apply PrefixView.inv_firstn in Hj as [_ Hj]. exact (Hw1 _ _ _ _ _ Hi Hj).
        + intros i j k op op' r r' Hi Hj. apply PrefixView.res_firstn in Hi as [_ Hi].
          apply PrefixView.res_firstn in Hj as [_ Hj]. exact (Hw2 _ _ _ _ _ _ _ Hi Hj).
        + intros j k op r Hj. apply PrefixView.res_firstn in Hj as [Hjn Hj].
          destruct (Hw3 _ _ _ _ Hj) as (i & Hij & Hi). exists i. split; [exact Hij|].
          apply PrefixView.inv_firstn. split; [lia | exact Hi].
      - intros i j k k' op op' Hi Hj. apply PrefixView.inv_firstn in Hi as [_ Hi].
        apply PrefixView.inv_firstn in Hj as [_ Hj]. exact (Hpo _ _ _ _ _ _ Hi Hj).
      - intros m Hm. rewrite firstn_firstn. rewrite length_firstn in Hm.
        replace (Nat.min m n) with m by lia. apply Hpre. lia.
      - intros i j k k' op op' r Hi Hj. apply PrefixView.res_firstn in Hi as [_ Hi].
        apply PrefixView.inv_firstn in Hj as [_ Hj]. exact (Hrt _ _ _ _ _ _ _ Hi Hj).
    Qed.

    Lemma view_rt_nil (nu_nil : nu []) H : PrefixView.view_rt indep nu H [].
    Proof.
      split; [split; [|split]|].
      - split; [|split].
        + intros i j k op op' (x & Hx & _). destruct i; discriminate.
        + intros i j k op op' r r' (x & Hx & _). destruct i; discriminate.
        + intros j k op r (x & Hx & _). destruct j; discriminate.
      - intros i j k k' op op' (x & Hx & _). destruct i; discriminate.
      - intros n Hn. exists []. rewrite firstn_nil. split; [exact nu_nil|]. split; [constructor|]. split; [|split].
        + intros o [].
        + intros j k op r (x & Hx & _). destruct j; discriminate.
        + intros o o' [].
      - intros i j k k' op op' r (x & Hx & _). destruct i; discriminate.
    Qed.

    (** *** Soundness *)

    Lemma vt_path_gen v T v' : vf_path VT v T v' ->
      v_trace v' = v_trace v ++ T /\ (v' = v \/ PrefixView.view_rt indep nu (v_stamp v') (v_trace v')).
    Proof.
      induction 1 as [v | v ev v1 T v2 Hs Hp IH].
      - rewrite app_nil_r. auto.
      - simpl in Hs. inversion Hs as [ev0 L H H' Hst Hv]; subst. simpl in IH |- *.
        destruct IH as [Htr [-> | Hv2]].
        + split; [rewrite Htr, <- app_assoc; reflexivity | right; exact Hv].
        + split; [rewrite Htr, <- app_assoc; reflexivity | right; exact Hv2].
    Qed.

    Theorem vt_sound (nu_nil : nu []) H0 : sound_pres nu VT (mkV [] H0).
    Proof.
      intros T v Hp Hwf Hc. destruct (vt_path_gen _ _ _ Hp) as [Htr [-> | Hv]]; simpl in Htr.
      - subst T. exact (PrefixView.view_rt_rel_lin indep nu H0 [] Hc (view_rt_nil nu_nil H0)).
      - rewrite Htr in Hv. exact (PrefixView.view_rt_rel_lin indep nu _ _ Hc Hv).
    Qed.

    (** *** Completeness (Prop. I.10 plus prefix closure) *)

    Lemma vt_path_of_view H0 H u : u <> [] -> PrefixView.view_rt indep nu H u ->
      vf_path VT (mkV [] H0) u (mkV u H).
    Proof.
      induction u as [|x u IH] using rev_ind; intros Hne Hv; [contradiction|].
      assert (Hu : PrefixView.view_rt indep nu H u).
      { rewrite <- (firstn_app_len u [x]). exact (view_rt_firstn _ _ _ Hv). }
      destruct u as [|y u'].
      - simpl. econstructor; [|constructor]. simpl.
        change [x] with ([] ++ [x]). constructor; [|exact Hv].
        intros i k m (z & Hz & _). destruct i; discriminate.
      - apply (vf_path_snoc VT _ _ (mkV (y :: u') H)).
        + apply IH; [discriminate | exact Hu].
        + simpl. constructor; [unfold stable; intros; reflexivity | exact Hv].
    Qed.

    Theorem vt_complete (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'})
        (nu_prefix : forall l1 l2, nu (l1 ++ l2) -> nu l1) H0 :
      complete_pres nu VT (mkV [] H0).
    Proof.
      intros u (w & Hwf & Hc & Hrl).
      destruct (PrefixView.rel_lin_view_rt indep nu key_dec nu_prefix _ Hwf Hc Hrl) as (H & Hv).
      assert (Hu : PrefixView.view_rt indep nu H u).
      { rewrite <- (firstn_app_len u w). exact (view_rt_firstn _ _ _ Hv). }
      destruct u as [|x u'].
      - exists (mkV [] H0). constructor.
      - exists (mkV (x :: u') H). apply vt_path_of_view; [discriminate | exact Hu].
    Qed.

    (** *** The paper's views, without real time *)

    (** [VT0] is [VT] with Def. I.4 as printed: no real-time condition. *)
    Inductive vt0_step : ThreadEvent E -> vstate -> vstate -> Prop :=
    | vt0_step_intro ev L H H' :
        stable L H H' -> PrefixView.view indep nu H' (L ++ [ev]) ->
        vt0_step ev (mkV L H) (mkV (L ++ [ev]) H').

    Definition VT0 : LTS E := {| State := vstate; Step := vt0_step; Error := fun _ _ => False |}.

    Lemma view_firstn H L n : PrefixView.view indep nu H L -> PrefixView.view indep nu H (firstn n L).
    Proof.
      intros ((Hw1 & Hw2 & Hw3) & Hpo & Hpre). split; [|split].
      - split; [|split].
        + intros i j k op op' Hi Hj. apply PrefixView.inv_firstn in Hi as [_ Hi].
          apply PrefixView.inv_firstn in Hj as [_ Hj]. exact (Hw1 _ _ _ _ _ Hi Hj).
        + intros i j k op op' r r' Hi Hj. apply PrefixView.res_firstn in Hi as [_ Hi].
          apply PrefixView.res_firstn in Hj as [_ Hj]. exact (Hw2 _ _ _ _ _ _ _ Hi Hj).
        + intros j k op r Hj. apply PrefixView.res_firstn in Hj as [Hjn Hj].
          destruct (Hw3 _ _ _ _ Hj) as (i & Hij & Hi). exists i. split; [exact Hij|].
          apply PrefixView.inv_firstn. split; [lia | exact Hi].
      - intros i j k k' op op' Hi Hj. apply PrefixView.inv_firstn in Hi as [_ Hi].
        apply PrefixView.inv_firstn in Hj as [_ Hj]. exact (Hpo _ _ _ _ _ _ Hi Hj).
      - intros m Hm. rewrite firstn_firstn. rewrite length_firstn in Hm.
        replace (Nat.min m n) with m by lia. apply Hpre. lia.
    Qed.

    Lemma vt0_path_of_view H0 H u : u <> [] -> PrefixView.view indep nu H u ->
      vf_path VT0 (mkV [] H0) u (mkV u H).
    Proof.
      induction u as [|x u IH] using rev_ind; intros Hne Hv; [contradiction|].
      assert (Hu : PrefixView.view indep nu H u).
      { rewrite <- (firstn_app_len u [x]). exact (view_firstn _ _ _ Hv). }
      destruct u as [|y u'].
      - simpl. econstructor; [|constructor]. simpl.
        change [x] with ([] ++ [x]). constructor; [|exact Hv].
        intros i k m (z & Hz & _). destruct i; discriminate.
      - apply (vf_path_snoc VT0 _ _ (mkV (y :: u') H)).
        + apply IH; [discriminate | exact Hu].
        + simpl. constructor; [unfold stable; intros; reflexivity | exact Hv].
    Qed.

    (** Every [VT] trace is a [VT0] trace, so [VT0] is complete too. *)
    Lemma vt_incl_vt0 H0 : traces_incl VT (mkV [] H0) VT0 (mkV [] H0).
    Proof.
      apply (fsim_traces VT VT0 eq); [|reflexivity].
      intros ev v1 v2 v1' <- Hs. exists v2. split; [|reflexivity].
      simpl in Hs |- *. destruct Hs as [ev L H H' Hst Hv]. constructor; [exact Hst | exact (proj1 Hv)].
    Qed.

    Corollary vt0_complete (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'})
        (nu_prefix : forall l1 l2, nu (l1 ++ l2) -> nu l1) H0 :
      complete_pres nu VT0 (mkV [] H0).
    Proof. exact (complete_pres_enlarge nu _ _ _ _ (vt_complete key_dec nu_prefix H0) (vt_incl_vt0 H0)). Qed.
  End VT.

  (** [VT0] is not sound.  The trace [PrefixView.s0] of the counterexample
      to Thm. I.11 ("thread 1 writes 1 and returns; then thread 2 reads 0")
      is complete, well formed, a [VT0] trace, and not relaxed
      linearizable.  So the paper's views may present an underlay, but not
      an overlay. *)
  Theorem vt0_not_sound (H0 : CallKey PrefixView.Reg -> nat) :
    ~ sound_pres (PrefixView.reg_ok 0) (VT0 (E := PrefixView.Reg) (PrefixView.reg_ok 0)) (mkV [] H0).
  Proof.
    intros Hs. apply PrefixView.s0_not_rel_lin.
    apply (Hs PrefixView.s0 (mkV PrefixView.s0 (PrefixView.stamp PrefixView.s0))).
    - apply vt0_path_of_view; [discriminate|].
      exact (PrefixView.zero_reads_view PrefixView.s0 PrefixView.wf_s0 PrefixView.zero_reads_s0).
    - exact PrefixView.wf_s0.
    - exact PrefixView.complete_s0.
  Qed.


  (** ** Part 3: moving an execution to another underlay *)

  Section Transport.
    Context {E F : RelaxedSig.t} (M : RelaxedLang.RelaxedModuleImpl E F).

    Definition underlay_events (evs : list (ModuleEvent E F)) : list (ThreadEvent E) :=
      flat_map (fun ev => match ev with UnderlayEvent e => [e] | OverlayEvent _ => [] end) evs.

    Lemma vf_path_cons_inv {G : RelaxedSig.t} (V : LTS G) q e es q' :
      vf_path V q (e :: es) q' -> exists q1, Step V e q q1 /\ vf_path V q1 es q'.
    Proof. intros Hp. inversion Hp; subst. eauto. Qed.

    (** The underlay events of an execution form a path of its underlay. *)
    Lemma exec_underlay_path (U : LTS E) c evs c' :
      module_execution_tagged U M c evs c' ->
      vf_path U (tm_lts_state c) (underlay_events evs) (tm_lts_state c').
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; [constructor|].
      revert IH. destruct Hstep as [t h op q pool queue used tr ret Hfresh Hmeth Hft
                                   | cand q q' pool queue queue' used Hsel Hlts
                                   | t h op ret q pool pool' queue used Hfin Hdone];
        intros IH; simpl in *; [exact IH | econstructor; [exact Hlts | exact IH] | exact IH].
    Qed.

    (** Only the underlay steps look at the underlay LTS, so an execution
        moves to any underlay that has the same underlay trace. *)
    Lemma exec_transport (U V : LTS E) c evs c' :
      module_execution_tagged U M c evs c' ->
      forall q q', vf_path V q (underlay_events evs) q' ->
      exists d, module_execution_tagged V M
                  (Build_TaggedModuleConfig q (tm_calls c) (tm_queue c) (tm_used_underlay c)) evs d /\
                tm_calls d = tm_calls c'.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros q q' Hp.
      - eexists. split; [constructor | reflexivity].
      - revert IH Hp. destruct Hstep as [t h op qq pool queue used tr ret Hfresh Hmeth Hft
                                       | cand qq qq' pool queue queue' used Hsel Hlts
                                       | t h op ret qq pool pool' queue used Hfin Hdone];
          intros IH Hp; simpl in Hp |- *.
        + destruct (IH q q' Hp) as (d & Hd & Hc). exists d. split; [|exact Hc].
          econstructor; [eapply tagged_invoke; eauto | exact Hd].
        + destruct (vf_path_cons_inv V _ _ _ _ Hp) as (q1 & Hs & Hp').
          destruct (IH q1 q' Hp') as (d & Hd & Hc). exists d. split; [|exact Hc].
          econstructor; [eapply tagged_underlay; [exact Hsel | exact Hs] | exact Hd].
        + destruct (IH q q' Hp) as (d & Hd & Hc). exists d. split; [|exact Hc].
          econstructor; [eapply tagged_return; eauto | exact Hd].
    Qed.
  End Transport.

  (** ** Part 4: P1, and VLHL *)

  Section P1.
    Context {E F : RelaxedSig.t} (M : RelaxedLang.RelaxedModuleImpl E F).
    Context (nuE : list (Op E) -> Prop) (nuF : list (Op F) -> Prop).

    (** P1.  The proof of a layer may present the underlay by any complete
        LTS and the overlay by any sound LTS.  The conclusion mentions
        neither: it holds over every underlay that implements [(νE, IE)],
        and it states relaxed linearizability to [(νF, IF)]. *)
    Theorem presentation_choice (VE : LTS E) (q0 : State VE) (VF : LTS F) (v0 : State VF) S :
      complete_pres nuE VE q0 -> sound_pres nuF VF v0 ->
      GSimRel VE VF M S -> S (initial_tagged_module VE q0) (PossOk v0 []) ->
      forall (U : LTS E) (qU : State U), implements nuE U qU ->
      forall evs c, module_execution_tagged U M (initial_tagged_module U qU) evs c ->
        (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
        rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) nuF.
    Proof.
      intros Hcomp Hsound HS H0 U qU Himpl evs c Hex Hdead.
      pose proof (exec_underlay_path M U _ _ _ Hex) as Hu. simpl in Hu.
      destruct (Hcomp _ (Himpl _ _ Hu)) as (q' & Hq').
      destruct (exec_transport M U VE _ _ _ Hex q0 q' Hq') as (d & Hd & Hc).
      apply (gsim_rel_lin VE VF M v0 nuF S q0 evs d HS H0 Hd).
      - intros e He. rewrite Hc in He. exact (Hdead e He).
      - exact Hsound.
    Qed.

    (** The paper's VLHL: both presentations are view traces.  This is
        Thms. I.9 and I.11 together, with real time added to the views and
        with universal simulation steps. *)
    Corollary vlhl_sound (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'})
        (nuE_prefix : forall l1 l2, nuE (l1 ++ l2) -> nuE l1) (nuF_nil : nuF [])
        (HE : CallKey E -> nat) (HF : CallKey F -> nat) S :
      GSimRel (VT nuE) (VT nuF) M S ->
      S (initial_tagged_module (VT nuE) (mkV [] HE)) (@PossOk F (VT nuF) (mkV [] HF) []) ->
      forall (U : LTS E) (qU : State U), implements nuE U qU ->
      forall evs c, module_execution_tagged U M (initial_tagged_module U qU) evs c ->
        (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
        rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) nuF.
    Proof.
      intros HS H0. apply (presentation_choice (VT nuE) (mkV [] HE) (VT nuF) (mkV [] HF) S).
      - exact (vt_complete nuE key_dec nuE_prefix HE).
      - exact (vt_sound nuF nuF_nil HF).
      - exact HS.
      - exact H0.
    Qed.
  End P1.
End ViewLHL.
