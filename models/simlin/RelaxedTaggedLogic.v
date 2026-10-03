(** The relaxed program logic over the dependency frontier.

    [RelaxedLogic] certifies method bodies against the positional module
    scheduler ([module_step], [select_frontier], [event_can_cross]), in
    which every response is a barrier for every later event of its
    thread.  This file transfers the same proof architecture to the
    dependency frontier of [RelaxedModuleSemantics.module_step_tagged]
    (weak sequential composition): an event may be scheduled before an
    earlier event of its thread unless one of (F1)--(F3) of [must_precede]
    relates them.

    The rule set is unchanged.  What changes is the scheduler-facing
    obligation [TDebtSafe]: it quantifies over every selection of the
    dependency frontier, so a proof now has to account for the extra
    reorderings (an invocation overtaking a response it does not depend
    on, possibly of another method of the same thread).  Two new
    principles make this manageable:

    - [select_tobligation_independent] (the logical form of
      Rensink--Wehrheim's Prop. 1 / Lemma lem:wsc-indep): the selected
      obligation is unrelated by [must_precede] to every obligation of its
      thread that it overtakes;
    - [tdebt_safe_dependent_pair] ("wait-established knowledge"): an
      invocation tagged with a handle may assume that the response of that
      handle has already been consumed. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedModuleSemantics.

Import ListNotations.


Module RelaxedTaggedLogic.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedPossibility.
  Import RelaxedModuleSemantics.

  (** ** Owner-indexed tagged module steps *)

  Section OwnedSteps.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (M : RelaxedModuleImpl E F).

    Inductive module_step_tagged_at :
        CallKey F -> ModuleEvent E F ->
        TaggedModuleConfig VE -> TaggedModuleConfig VE -> Prop :=
    | tagged_at_invoke t h op q pool queue used trace ret
        (Hfresh_call : call_fresh (t, h) pool)
        (Hmethod : program_produces_tagged t (M op t) trace ret)
        (Hfresh_trace : trace_fresh used (map untag trace)) :
        module_step_tagged_at (t, h)
          (OverlayEvent (Build_ThreadEvent t (@InvEv F h op)))
          (Build_TaggedModuleConfig q pool queue used)
          (Build_TaggedModuleConfig q
            (Build_CallEntry t h (ActiveCall op ret) :: pool)
            (queue ++ schedule_trace_tagged (t, h) trace)
            (used ++ invocation_keys (map untag trace)))
    | tagged_at_underlay candidate q q' pool queue queue' used
        (Hselect : select_frontier_tagged candidate queue queue')
        (Hlts : RelaxedLTSSpec.Step VE (untag (ts_event candidate)) q q') :
        module_step_tagged_at (ts_owner candidate)
          (UnderlayEvent (untag (ts_event candidate)))
          (Build_TaggedModuleConfig q pool queue used)
          (Build_TaggedModuleConfig q' pool queue' used)
    | tagged_at_return t h op ret q pool pool' queue used
        (Hfinish : finish_call t h op ret pool pool')
        (Hdone : owner_done_tagged (t, h) queue) :
        module_step_tagged_at (t, h)
          (OverlayEvent (Build_ThreadEvent t (@ResEv F h op ret)))
          (Build_TaggedModuleConfig q pool queue used)
          (Build_TaggedModuleConfig q pool' queue used).

    Lemma module_step_tagged_at_is_step owner ev c c' :
      module_step_tagged_at owner ev c c' -> module_step_tagged VE M ev c c'.
    Proof.
      intro Hstep. inversion Hstep; subst.
      - eapply tagged_invoke; eauto.
      - eapply tagged_underlay; eauto.
      - eapply tagged_return; eauto.
    Qed.

    Lemma module_step_tagged_has_owner ev c c' :
      module_step_tagged VE M ev c c' ->
      exists owner, module_step_tagged_at owner ev c c'.
    Proof.
      intro Hstep. inversion Hstep; subst.
      - eexists. eapply tagged_at_invoke; eauto.
      - eexists. eapply tagged_at_underlay; eauto.
      - eexists. eapply tagged_at_return; eauto.
    Qed.

  End OwnedSteps.

  (** ** Joint states, relies, and the tagged simulation *)

  Section Simulation.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedModuleImpl E F).

    Definition TConcreteState : Type := @TaggedModuleConfig E F VE.
    Definition TAbstractState : Type := Poss VF.
    Definition TJointState : Type := (TConcreteState * TAbstractState)%type.
    Definition TConcreteRelation : Type := relation TConcreteState.
    Definition TAbstractRelation : Type := relation TAbstractState.
    Definition TJointRelation : Type := relation TJointState.
    Definition TAssertion : Type := TJointState -> Prop.

    Record TConcreteRely : Type := {
      tconcrete_thread_rely : tid -> TConcreteRelation;
      tconcrete_system_rely : tid -> TConcreteRelation;
    }.

    Record TAbstractRely : Type := {
      tabstract_thread_rely : tid -> TAbstractRelation;
      tabstract_system_rely : tid -> TAbstractRelation;
    }.

    Definition tinvariant_lift
        (I : TAssertion) (RC : TConcreteRelation) (RA : TAbstractRelation) :
        TJointRelation :=
      fun source target =>
        RC (fst source) (fst target) /\
        RA (snd source) (snd target) /\
        I source /\ I target.

    Definition trely_lift
        (I : TAssertion) (R : TConcreteRely) (AR : TAbstractRely)
        (alpha : tid) : TJointRelation :=
      fun source target =>
        ((tconcrete_thread_rely R alpha (fst source) (fst target) /\
          tabstract_thread_rely AR alpha (snd source) (snd target)) \/
         (tconcrete_system_rely R alpha (fst source) (fst target) /\
          tabstract_system_rely AR alpha (snd source) (snd target))) /\
        I source /\ I target.

    Definition tunderlay_step (alpha : tid) (source target : TConcreteState) : Prop :=
      exists h ev,
        module_step_tagged_at VE M (alpha, h) (UnderlayEvent ev) source target.

    Inductive tinvoke_transition (alpha : tid) :
        TConcreteState -> TAbstractState -> TConcreteState -> TAbstractState -> Prop :=
    | tinvoke_transition_intro h op c c' p p'
        (Hconcrete :
          module_step_tagged_at VE M (alpha, h)
            (OverlayEvent (Build_ThreadEvent alpha (@InvEv F h op))) c c')
        (Habstract : poss_invoke VF alpha h op p p') :
        tinvoke_transition alpha c p c' p'.

    Inductive treturn_transition (alpha : tid) :
        TConcreteState -> TAbstractState -> TConcreteState -> TAbstractState -> Prop :=
    | treturn_transition_intro h op ret c c' p p'
        (Hconcrete :
          module_step_tagged_at VE M (alpha, h)
            (OverlayEvent (Build_ThreadEvent alpha (@ResEv F h op ret))) c c')
        (Habstract : poss_return VF alpha h op ret p p') :
        treturn_transition alpha c p c' p'.

    Inductive toverlay_step (alpha : tid) :
        TConcreteState -> TAbstractState -> TConcreteState -> TAbstractState -> Prop :=
    | toverlay_step_invoke c p c' p'
        (Hinvoke : tinvoke_transition alpha c p c' p') :
        toverlay_step alpha c p c' p'
    | toverlay_step_return c p middle c' p'
        (Hsteps : poss_overlay_steps VF p middle)
        (Hreturn : treturn_transition alpha c middle c' p') :
        toverlay_step alpha c p c' p'.

    (** Def. C.3 over the dependency frontier.  Only the concrete module
        transition changes; the system rely [R_sys alpha] is still a
        parameter, and its canonical instance (any handle of [alpha])
        now covers every frontier selection of [alpha]'s own events. *)
    CoInductive TRGISimulation
        (A : tid -> Prop) (R : TConcreteRely) (AR : TAbstractRely)
        (G : TConcreteRelation) (AG : TAbstractRelation) (I : TAssertion) :
        TConcreteState -> TAbstractState -> Prop :=
    | TRGISim c p
        (trgisim_invariant : I (c, p))
        (trgisim_ustep :
          forall alpha, A alpha ->
          forall c', tunderlay_step alpha c c' ->
          exists p',
            poss_steps VF p p' /\
            tinvariant_lift I G AG (c, p) (c', p') /\
            TRGISimulation A R AR G AG I c' p')
        (trgisim_ostep :
          forall alpha, A alpha ->
          exists c' p',
            toverlay_step alpha c p c' p' /\
            tinvariant_lift I G AG (c, p) (c', p') /\
            TRGISimulation A R AR G AG I c' p')
        (trgisim_rely :
          forall alpha, A alpha ->
          forall c' p',
            trely_lift I R AR alpha (c, p) (c', p') ->
            TRGISimulation A R AR G AG I c' p') :
        TRGISimulation A R AR G AG I c p.

  End Simulation.

  (** ** Obligations *)

  Section Obligations.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedModuleImpl E F).
    Context (I : @TAssertion E F VE VF).
    Context (G : @TConcreteRelation E F VE).
    Context (AG : @TAbstractRelation F VF).

    Definition TUUpdate
        (candidate : TaggedScheduledEvent E F) (P Q : TAssertion VE VF) : Prop :=
      forall c p,
        P (c, p) ->
        forall c',
          module_step_tagged_at VE M (ts_owner candidate)
            (UnderlayEvent (untag (ts_event candidate))) c c' ->
          exists p',
            poss_steps VF p p' /\ Q (c', p') /\
            tinvariant_lift VE VF I G AG (c, p) (c', p').

    Definition TLinUpdate
        (candidate : TaggedScheduledEvent E F) (owner : CallKey F)
        (P Q : TAssertion VE VF) : Prop :=
      forall c p,
        P (c, p) ->
        forall c',
          module_step_tagged_at VE M (ts_owner candidate)
            (UnderlayEvent (untag (ts_event candidate))) c c' ->
          exists p',
            poss_step_at VF owner p p' /\ Q (c', p') /\
            tinvariant_lift VE VF I G AG (c, p) (c', p').

    Lemma tlin_update_is_update candidate owner P Q :
      TLinUpdate candidate owner P Q -> TUUpdate candidate P Q.
    Proof.
      intros Hlin c p HP c' Hstep.
      destruct (Hlin c p HP c' Hstep) as (p' & Hs & HQ & Hg).
      exists p'. split; [apply rt_step; exists owner; exact Hs | split; assumption].
    Qed.

    Definition TStable (R : TConcreteRely VE) (AR : TAbstractRely VF)
        (alpha : tid) (P : TAssertion VE VF) : Prop :=
      forall source target,
        P source -> trely_lift VE VF I R AR alpha source target -> P target.

    Record TEventObligation : Type := {
      tob_event : TaggedScheduledEvent E F;
      tob_pre : TAssertion VE VF;
      tob_post : TAssertion VE VF;
      tob_valid : TUUpdate tob_event tob_pre tob_post;
    }.

    Definition TObligations : Type := list TEventObligation.

    Definition terase (obligations : TObligations) : TaggedQueue E F :=
      map tob_event obligations.

    Definition tqueue_invariant (c : TaggedModuleConfig VE) (obligations : TObligations) : Prop :=
      terase obligations = tm_queue c.

    (** Logical selection mirrors the dependency frontier. *)
    Inductive select_tobligation (candidate : TEventObligation) :
        TObligations -> TObligations -> Prop :=
    | select_tobligation_here suffix :
        select_tobligation candidate (candidate :: suffix) suffix
    | select_tobligation_next earlier queue queue'
        (Hcross : tagged_can_cross (ts_event (tob_event earlier))
                                   (ts_event (tob_event candidate)))
        (Hselect : select_tobligation candidate queue queue') :
        select_tobligation candidate (earlier :: queue) (earlier :: queue').

    Lemma select_tobligation_erases candidate obligations obligations' :
      select_tobligation candidate obligations obligations' ->
      select_frontier_tagged (tob_event candidate) (terase obligations) (terase obligations').
    Proof.
      intro Hselect. induction Hselect; cbn.
      - apply tagged_select_here.
      - apply tagged_select_next; assumption.
    Qed.

    Lemma select_frontier_tagged_lifts candidate queue queue' :
      select_frontier_tagged candidate queue queue' ->
      forall obligations,
        terase obligations = queue ->
        exists obligation obligations',
          tob_event obligation = candidate /\
          select_tobligation obligation obligations obligations' /\
          terase obligations' = queue'.
    Proof.
      induction 1 as [suffix | earlier queue queue' Hcross Hsel IH];
        intros obligations Herase.
      - destruct obligations as [| ob obs]; cbn in Herase; [discriminate |].
        injection Herase as Hev Htail.
        exists ob, obs. split; [exact Hev |]. split; [apply select_tobligation_here | exact Htail].
      - destruct obligations as [| ob obs]; cbn in Herase; [discriminate |].
        injection Herase as Hev Htail.
        destruct (IH obs Htail) as (sel & obs' & Hsel_ev & Hlog & Herase').
        exists sel, (ob :: obs'). split; [exact Hsel_ev |]. split.
        + apply select_tobligation_next; [rewrite Hev, Hsel_ev; exact Hcross | exact Hlog].
        + change (tob_event ob :: terase obs' = earlier :: queue').
          rewrite Hev, Herase'. reflexivity.
    Qed.

    Lemma operational_tselection_has_obligation candidate c queue' obligations :
      tqueue_invariant c obligations ->
      select_frontier_tagged candidate (tm_queue c) queue' ->
      exists obligation obligations',
        tob_event obligation = candidate /\
        select_tobligation obligation obligations obligations' /\
        terase obligations' = queue'.
    Proof.
      intros Hq Hsel. rewrite <- Hq in Hsel.
      eapply select_frontier_tagged_lifts; [exact Hsel | reflexivity].
    Qed.

    (** The logical form of Lemma lem:wsc-indep: the selected obligation
        can cross everything queued before it; for an obligation of the
        same thread this means that none of (F1)--(F3) relates them. *)
    Lemma select_tobligation_split candidate obligations obligations' :
      select_tobligation candidate obligations obligations' ->
      exists pre post,
        obligations = pre ++ candidate :: post /\
        obligations' = pre ++ post /\
        Forall (fun e => tagged_can_cross (ts_event (tob_event e))
                                          (ts_event (tob_event candidate))) pre.
    Proof.
      induction 1 as [suffix | earlier queue queue' Hcross Hsel IH].
      - exists [], suffix. auto.
      - destruct IH as (pre & post & -> & -> & Hall).
        exists (earlier :: pre), post. cbn. auto.
    Qed.

    Lemma select_tobligation_independent candidate obligations obligations' :
      select_tobligation candidate obligations obligations' ->
      exists pre post,
        obligations = pre ++ candidate :: post /\
        forall e, In e pre ->
          te_tid E (untag (ts_event (tob_event e))) =
          te_tid E (untag (ts_event (tob_event candidate))) ->
          ~ must_precede (ts_event (tob_event e)) (ts_event (tob_event candidate)).
    Proof.
      intros Hsel. destruct (select_tobligation_split _ _ _ Hsel) as (pre & post & Heq & _ & Hall).
      exists pre, post. split; [exact Heq |].
      intros e He Ht. rewrite Forall_forall in Hall.
      destruct (Hall e He) as [Hneq | [_ Hno]]; [contradiction | exact Hno].
    Qed.

    Lemma select_tobligation_length selected obligations rest :
      select_tobligation selected obligations rest -> length obligations = S (length rest).
    Proof. induction 1; cbn; congruence. Qed.

    Lemma select_tobligation_member selected obligations rest :
      select_tobligation selected obligations rest -> In selected obligations.
    Proof. induction 1; cbn; auto. Qed.

  End Obligations.

  (** ** The logic *)

  Section Logic.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedModuleImpl E F).
    Context (I : @TAssertion E F VE VF).
    Context (G : @TConcreteRelation E F VE).
    Context (AG : @TAbstractRelation F VF).

    Definition TOb : Type := TEventObligation VE VF M I G AG.
    Definition TObs : Type := list TOb.
    Definition TA : Type := TAssertion VE VF.

    Definition tev (ob : TOb) : TaggedScheduledEvent E F := tob_event VE VF M I G AG ob.
    Definition tpre (ob : TOb) : TA := tob_pre VE VF M I G AG ob.
    Definition tpost (ob : TOb) : TA := tob_post VE VF M I G AG ob.

    Definition tselect : TOb -> TObs -> TObs -> Prop := select_tobligation VE VF M I G AG.

    Definition tobligation_trace (obligations : TObs) : list (TaggedEvent E) :=
      map (fun ob => ts_event (tev ob)) obligations.

    (** *** Certified executions over the tagged local semantics *)

    Inductive TCertifiedExecution (owner : CallKey F) (thread : tid) (A : Type) :
        ProgramConfig E A -> TObs -> ProgramConfig E A -> Prop :=
    | tcertified_refl config :
        TCertifiedExecution owner thread A config [] config
    | tcertified_silent config1 config2 config3 obligations
        (Hstep : program_step_tagged thread TSilent config1 config2)
        (Hexec : TCertifiedExecution owner thread A config2 obligations config3) :
        TCertifiedExecution owner thread A config1 obligations config3
    | tcertified_emit config1 config2 config3 m obligation obligations
        (Hstep : program_step_tagged thread (TEmit m) config1 config2)
        (Hevent : tev obligation = Build_TaggedScheduledEvent owner m)
        (Hexec : TCertifiedExecution owner thread A config2 obligations config3) :
        TCertifiedExecution owner thread A config1 (obligation :: obligations) config3.

    Lemma tcertified_is_program_execution owner thread A config obligations config' :
      TCertifiedExecution owner thread A config obligations config' ->
      program_execution_tagged thread config (tobligation_trace obligations) config'.
    Proof.
      intro H. induction H.
      - apply tagged_execution_refl.
      - eapply tagged_execution_silent; eauto.
      - cbn. rewrite Hevent. cbn. eapply tagged_execution_emit; eauto.
    Qed.

    Lemma tcertified_erases_to_schedule owner thread A config obligations config' :
      TCertifiedExecution owner thread A config obligations config' ->
      terase VE VF M I G AG obligations =
      schedule_trace_tagged owner (tobligation_trace obligations).
    Proof.
      intro H. induction H.
      - reflexivity.
      - exact IHTCertifiedExecution.
      - cbn. unfold tev in *. rewrite Hevent. cbn. f_equal. exact IHTCertifiedExecution.
    Qed.

    (** Every event a tagged step can emit must be covered by an obligation. *)
    Definition TObligationRule (owner : CallKey F) (thread : tid) : Prop :=
      forall (A : Type) (config config' : ProgramConfig E A) m,
        program_step_tagged thread (TEmit m) config config' ->
        exists obligation : TOb, tev obligation = Build_TaggedScheduledEvent owner m.

    (** Primitive obligations: one per invocation (for every tag) and one
        per response. *)
    Record TPrimitiveObligations (owner : CallKey F) (thread : tid) : Prop := {
      tfuture_obligation :
        forall (op : Sig.op (RelaxedSig.effect E)) (handle : RelaxedSig.handle E)
               (deps : RelaxedSig.handle E -> Prop),
          exists obligation : TOb,
            tev obligation =
            Build_TaggedScheduledEvent owner
              (Build_TaggedEvent (Build_ThreadEvent thread (InvEv handle op)) deps);
      tresponse_obligation :
        forall (op : Sig.op (RelaxedSig.effect E)) (handle : RelaxedSig.handle E)
               (ret : Sig.ar op),
          exists obligation : TOb,
            tev obligation =
            Build_TaggedScheduledEvent owner
              (Build_TaggedEvent (Build_ThreadEvent thread (ResEv handle op ret)) no_deps);
    }.

    Lemma tprimitive_obligations_complete owner thread :
      TPrimitiveObligations owner thread -> TObligationRule owner thread.
    Proof.
      intros Hp A config config' m Hstep. inversion Hstep; subst.
      - apply (tfuture_obligation owner thread Hp).
      - apply (tfuture_obligation owner thread Hp).
      - apply (tresponse_obligation owner thread Hp).
      - apply (tresponse_obligation owner thread Hp).
    Qed.

    Lemma tprogram_execution_can_be_certified owner thread
        (Hrule : TObligationRule owner thread) A config trace config' :
      program_execution_tagged thread config trace config' ->
      exists obligations,
        TCertifiedExecution owner thread A config obligations config' /\
        tobligation_trace obligations = trace.
    Proof.
      intro H. induction H.
      - exists []. split; [apply tcertified_refl | reflexivity].
      - destruct IHprogram_execution_tagged as (obs & Hc & Ht).
        exists obs. split; [eapply tcertified_silent; eauto | exact Ht].
      - destruct (Hrule A c1 c2 _ Hstep) as [ob Hev].
        destruct IHprogram_execution_tagged as (obs & Hc & Ht).
        exists (ob :: obs). split.
        + eapply tcertified_emit; eauto.
        + unfold tobligation_trace in *. cbn. rewrite Hev. cbn. rewrite Ht. reflexivity.
    Qed.

    (** *** Scheduler safety over the dependency frontier *)

    Inductive TDebtSafe (Q : TA) : TJointState VE VF -> TObs -> Prop :=
    | tdebt_safe_done state
        (Hpost : Q state) :
        TDebtSafe Q state []
    | tdebt_safe_pending state obligations
        (Hnonempty : obligations <> [])
        (Hconsume :
          forall selected rest,
            tselect selected obligations rest ->
            tpre selected state /\
            forall concrete',
              module_step_tagged_at VE M (ts_owner (tev selected))
                (UnderlayEvent (untag (ts_event (tev selected)))) (fst state) concrete' ->
              exists abstract',
                poss_steps VF (snd state) abstract' /\
                tpost selected (concrete', abstract') /\
                tinvariant_lift VE VF I G AG state (concrete', abstract') /\
                TDebtSafe Q (concrete', abstract') rest) :
        TDebtSafe Q state obligations.

    Definition TLinkedDebtSafe (Q : TA) (state : TJointState VE VF) (obligations : TObs) : Prop :=
      tqueue_invariant VE VF M I G AG (fst state) obligations /\ TDebtSafe Q state obligations.

    Lemma tdebt_safe_selected_pre Q state obligations selected rest :
      TDebtSafe Q state obligations -> tselect selected obligations rest -> tpre selected state.
    Proof.
      intros Hs Hsel. inversion Hs; subst.
      - inversion Hsel.
      - now destruct (Hconsume selected rest Hsel).
    Qed.

    Lemma tdebt_safe_consume Q state obligations selected rest concrete' :
      TDebtSafe Q state obligations ->
      tselect selected obligations rest ->
      module_step_tagged_at VE M (ts_owner (tev selected))
        (UnderlayEvent (untag (ts_event (tev selected)))) (fst state) concrete' ->
      exists abstract',
        poss_steps VF (snd state) abstract' /\
        tpost selected (concrete', abstract') /\
        tinvariant_lift VE VF I G AG state (concrete', abstract') /\
        TDebtSafe Q (concrete', abstract') rest.
    Proof.
      intros Hs Hsel Hstep. inversion Hs; subst.
      - inversion Hsel.
      - destruct (Hconsume selected rest Hsel) as [_ Hk]. now apply Hk.
    Qed.

    (** An operational step of the dependency frontier determines the
        logical occurrence it consumes. *)
    Lemma tlinked_debt_safe_underlay_step Q concrete abstract obligations owner event concrete' :
      TLinkedDebtSafe Q (concrete, abstract) obligations ->
      module_step_tagged_at VE M owner (UnderlayEvent event) concrete concrete' ->
      exists selected rest abstract',
        ts_owner (tev selected) = owner /\
        untag (ts_event (tev selected)) = event /\
        poss_steps VF abstract abstract' /\
        tpost selected (concrete', abstract') /\
        tinvariant_lift VE VF I G AG (concrete, abstract) (concrete', abstract') /\
        TLinkedDebtSafe Q (concrete', abstract') rest.
    Proof.
      intros [Hq Hs] Hstep. inversion Hstep; subst.
      destruct (operational_tselection_has_obligation VE VF M I G AG candidate
                  (Build_TaggedModuleConfig q pool queue used) queue' obligations Hq Hselect)
        as (sel & rest & Hev & Hlog & Herase).
      assert (Hsel_step :
        module_step_tagged_at VE M (ts_owner (tev sel))
          (UnderlayEvent (untag (ts_event (tev sel))))
          (Build_TaggedModuleConfig q pool queue used)
          (Build_TaggedModuleConfig q' pool queue' used)).
      { unfold tev. rewrite Hev. eapply tagged_at_underlay; eauto. }
      destruct (tdebt_safe_consume Q (Build_TaggedModuleConfig q pool queue used, abstract)
                  obligations sel rest _ Hs Hlog Hsel_step)
        as (abstract' & Hp & Hpost & Hinv & Hs').
      exists sel, rest, abstract'.
      assert (Htev : tev sel = candidate) by exact Hev.
      rewrite Htev.
      split; [reflexivity |]. split; [reflexivity |].
      split; [exact Hp |]. split; [exact Hpost |]. split; [exact Hinv |].
      split; [exact Herase | exact Hs'].
    Qed.

    Lemma tdebt_safe_empty_post Q state : TDebtSafe Q state [] -> Q state.
    Proof.
      intro Hs. inversion Hs; subst; [exact Hpost | exfalso; apply Hnonempty; reflexivity].
    Qed.

    Lemma tlinked_debt_safe_empty_owner_done Q concrete abstract owner :
      TLinkedDebtSafe Q (concrete, abstract) [] -> owner_done_tagged owner (tm_queue concrete).
    Proof.
      intros [Hq _]. unfold tqueue_invariant in Hq. cbn in Hq.
      unfold owner_done_tagged. rewrite <- Hq. cbn. tauto.
    Qed.

    Definition TDebtProtocol (K : TObs -> TA) : Prop :=
      forall obligations selected rest,
        tselect selected obligations rest ->
        forall concrete abstract,
          K obligations (concrete, abstract) ->
          tpre selected (concrete, abstract) /\
          forall concrete',
            module_step_tagged_at VE M (ts_owner (tev selected))
              (UnderlayEvent (untag (ts_event (tev selected)))) concrete concrete' ->
            exists abstract',
              poss_steps VF abstract abstract' /\
              tpost selected (concrete', abstract') /\
              tinvariant_lift VE VF I G AG (concrete, abstract) (concrete', abstract') /\
              K rest (concrete', abstract').

    Lemma tdebt_protocol_sound (Q : TA) (K : TObs -> TA) :
      TDebtProtocol K ->
      (forall state, K [] state -> Q state) ->
      forall obligations state, K obligations state -> TDebtSafe Q state obligations.
    Proof.
      intros Hprot Hfinal.
      assert (Hind : forall n obligations state,
                length obligations = n -> K obligations state -> TDebtSafe Q state obligations).
      { induction n as [| n IH]; intros obligations state Hlen HK.
        - destruct obligations; [apply tdebt_safe_done; now apply Hfinal | discriminate].
        - destruct obligations as [| ob obs]; [discriminate |].
          apply tdebt_safe_pending; [discriminate |].
          intros sel rest Hsel. destruct state as [concrete abstract].
          destruct (Hprot _ sel rest Hsel concrete abstract HK) as [Hpre Hk].
          split; [exact Hpre |].
          intros concrete' Hstep.
          destruct (Hk concrete' Hstep) as (abstract' & Hp & Hpost & Hinv & HK').
          exists abstract'. split; [assumption |]. split; [assumption |]. split; [assumption |].
          apply IH; [| exact HK'].
          pose proof (select_tobligation_length VE VF M I G AG _ _ _ Hsel) as Hl.
          unfold TOb, TObs in *. cbn in Hlen, Hl. lia. }
      intros obligations state HK. eapply Hind; [reflexivity | exact HK].
    Qed.

    Lemma tdebt_safe_is_protocol (Q : TA) :
      TDebtProtocol (fun obligations state => TDebtSafe Q state obligations).
    Proof.
      intros obligations sel rest Hsel concrete abstract Hs. split.
      - eapply tdebt_safe_selected_pre; eauto.
      - intros concrete' Hstep.
        exact (tdebt_safe_consume Q (concrete, abstract) obligations sel rest concrete' Hs Hsel Hstep).
    Qed.

    Lemma tdebt_safe_mono (Q Q' : TA) (Hw : forall s, Q s -> Q' s) state obligations :
      TDebtSafe Q state obligations -> TDebtSafe Q' state obligations.
    Proof.
      intro Hs.
      eapply tdebt_protocol_sound with (K := fun obs st => TDebtSafe Q st obs).
      - apply tdebt_safe_is_protocol.
      - intros st Hemp. apply Hw. now apply tdebt_safe_empty_post.
      - exact Hs.
    Qed.

    Definition TObligationPreserves (obligation : TOb) (Frame : TA) : Prop :=
      forall concrete abstract,
        tpre obligation (concrete, abstract) ->
        Frame (concrete, abstract) ->
        forall concrete',
          module_step_tagged_at VE M (ts_owner (tev obligation))
            (UnderlayEvent (untag (ts_event (tev obligation)))) concrete concrete' ->
          exists abstract',
            poss_steps VF abstract abstract' /\
            tpost obligation (concrete', abstract') /\
            Frame (concrete', abstract') /\
            tinvariant_lift VE VF I G AG (concrete, abstract) (concrete', abstract').

    Lemma tconsume_obligation (ob : TOb) c p c' :
      tpre ob (c, p) ->
      module_step_tagged_at VE M (ts_owner (tev ob)) (UnderlayEvent (untag (ts_event (tev ob)))) c c' ->
      exists p', poss_steps VF p p' /\ tpost ob (c', p') /\ tinvariant_lift VE VF I G AG (c, p) (c', p').
    Proof.
      intros HP Hstep. exact (tob_valid VE VF M I G AG ob c p HP c' Hstep).
    Qed.

    Lemma tdebt_safe_singleton_with_frame (Q Frame : TA) state (ob : TOb) :
      tpre ob state -> Frame state -> TObligationPreserves ob Frame ->
      (forall state', tpost ob state' -> Frame state' -> Q state') ->
      TDebtSafe Q state [ob].
    Proof.
      destruct state as [concrete abstract]. cbn.
      intros Hpre Hframe Hpres Hfinal.
      apply tdebt_safe_pending; [discriminate |].
      intros sel rest Hsel.
      inversion Hsel as [suffix | earlier queue queue' Hcross Htail]; subst.
      - split; [exact Hpre |]. intros concrete' Hstep.
        destruct (Hpres concrete abstract Hpre Hframe concrete' Hstep)
          as (abstract' & Hp & Hpost & Hframe' & Hinv).
        exists abstract'. split; [assumption |]. split; [assumption |]. split; [assumption |]. apply tdebt_safe_done. now apply Hfinal.
      - inversion Htail.
    Qed.

    Definition TObligationCompatible (earlier later : TOb) : Prop :=
      tagged_can_cross (ts_event (tev earlier)) (ts_event (tev later)) ->
      TObligationPreserves earlier (tpre later) /\
      TObligationPreserves later (tpre earlier) /\
      TObligationPreserves earlier (tpost later) /\
      TObligationPreserves later (tpost earlier).

    (** Two obligations that the dependency frontier may reorder must be
        safe in either order. *)
    Lemma tdebt_safe_compatible_pair (Q : TA) state (first second : TOb) :
      tpre first state -> tpre second state ->
      tagged_can_cross (ts_event (tev first)) (ts_event (tev second)) ->
      TObligationCompatible first second ->
      (forall state', tpost first state' -> tpost second state' -> Q state') ->
      TDebtSafe Q state [first; second].
    Proof.
      destruct state as [concrete abstract]. cbn.
      intros Hp1 Hp2 Hcross Hcomp Hfinal.
      destruct (Hcomp Hcross) as (H12 & H21 & H1post2 & H2post1).
      apply tdebt_safe_pending; [discriminate |].
      intros sel rest Hsel.
      inversion Hsel as [suffix | earlier queue queue' Hcan Htail]; subst.
      - split; [exact Hp1 |]. intros concrete' Hstep.
        destruct (H12 concrete abstract Hp1 Hp2 concrete' Hstep)
          as (abstract' & Hp & Hpost1 & Hp2' & Hinv).
        exists abstract'. split; [assumption |]. split; [assumption |]. split; [assumption |].
        eapply tdebt_safe_singleton_with_frame with (Frame := tpost first); eauto.
      - inversion Htail as [suffix2 | earlier2 queue2 queue3 Hcan2 Htail2]; subst.
        + split; [exact Hp2 |]. intros concrete' Hstep.
          destruct (H21 concrete abstract Hp2 Hp1 concrete' Hstep)
            as (abstract' & Hp & Hpost2 & Hp1' & Hinv).
          exists abstract'. split; [assumption |]. split; [assumption |]. split; [assumption |].
          eapply tdebt_safe_singleton_with_frame with (Frame := tpost second); eauto.
        + inversion Htail2.
    Qed.

    (** When the frontier cannot reorder the pair, only program order needs
        to be certified, and the second obligation may rely on the
        postcondition of the first. *)
    Lemma tdebt_safe_ordered_pair (Q : TA) state (first second : TOb) :
      tpre first state ->
      ~ tagged_can_cross (ts_event (tev first)) (ts_event (tev second)) ->
      (forall state', tpost first state' -> tpre second state') ->
      TObligationPreserves second (tpost first) ->
      (forall state', tpost first state' -> tpost second state' -> Q state') ->
      TDebtSafe Q state [first; second].
    Proof.
      destruct state as [concrete abstract]. cbn.
      intros Hp1 Hord Hready Hpres Hfinal.
      apply tdebt_safe_pending; [discriminate |].
      intros sel rest Hsel.
      inversion Hsel as [suffix | earlier queue queue' Hcross Htail]; subst.
      - split; [exact Hp1 |]. intros concrete' Hstep.
        destruct (tconsume_obligation first concrete abstract concrete' Hp1 Hstep)
          as (abstract' & Hp & Hpost1 & Hinv).
        exists abstract'. split; [assumption |]. split; [assumption |]. split; [assumption |].
        eapply tdebt_safe_singleton_with_frame with (Frame := tpost first).
        + now apply Hready.
        + exact Hpost1.
        + exact Hpres.
        + intros st Ha Hb. apply Hfinal; assumption.
      - inversion Htail as [suffix2 | earlier2 queue2 queue3 Hcross2 Htail2]; subst.
        + exfalso. apply Hord. exact Hcross.
        + inversion Htail2.
    Qed.

    (** Same-thread pairs that (F1)--(F3) keep in order. *)
    Lemma must_precede_blocks (e e' : TaggedEvent E) :
      te_tid E (untag e) = te_tid E (untag e') ->
      must_precede e e' -> ~ tagged_can_cross e e'.
    Proof.
      intros Ht Hm [Hneq | [_ Hno]]; [exact (Hneq Ht) | exact (Hno Hm)].
    Qed.

    (** Wait-established knowledge (derived rule E6 of the WSC notes): an
        invocation tagged with handle [q] may be certified assuming the
        response of [q] (by the same thread) has already been consumed. *)
    Lemma tdebt_safe_dependent_pair (Q : TA) state (first second : TOb)
        (t : tid) (q : RelaxedSig.handle E) (op : Sig.op (RelaxedSig.effect E)) (ret : Sig.ar op)
        (h' : RelaxedSig.handle E) (op' : Sig.op (RelaxedSig.effect E)) :
      untag (ts_event (tev first)) = Build_ThreadEvent t (ResEv q op ret) ->
      untag (ts_event (tev second)) = Build_ThreadEvent t (InvEv h' op') ->
      tev_deps (ts_event (tev second)) q ->
      tpre first state ->
      (forall state', tpost first state' -> tpre second state') ->
      TObligationPreserves second (tpost first) ->
      (forall state', tpost first state' -> tpost second state' -> Q state') ->
      TDebtSafe Q state [first; second].
    Proof.
      intros H1 H2 Hdep Hp1 Hready Hpres Hfinal.
      apply tdebt_safe_ordered_pair; auto.
      apply must_precede_blocks.
      - rewrite H1, H2. reflexivity.
      - unfold must_precede. rewrite H1, H2. cbn. exact Hdep.
    Qed.

    (** Program order between invocations that the underlay does not
        declare semi-independent (F2). *)
    Lemma tdebt_safe_program_order_pair (Q : TA) state (first second : TOb)
        (t : tid) (h : RelaxedSig.handle E) (op : Sig.op (RelaxedSig.effect E))
        (h' : RelaxedSig.handle E) (op' : Sig.op (RelaxedSig.effect E)) :
      untag (ts_event (tev first)) = Build_ThreadEvent t (InvEv h op) ->
      untag (ts_event (tev second)) = Build_ThreadEvent t (InvEv h' op') ->
      ~ RelaxedSig.semi_independent E op op' ->
      tpre first state ->
      (forall state', tpost first state' -> tpre second state') ->
      TObligationPreserves second (tpost first) ->
      (forall state', tpost first state' -> tpost second state' -> Q state') ->
      TDebtSafe Q state [first; second].
    Proof.
      intros H1 H2 Hdep Hp1 Hready Hpres Hfinal.
      apply tdebt_safe_ordered_pair; auto.
      apply must_precede_blocks.
      - rewrite H1, H2. reflexivity.
      - unfold must_precede. rewrite H1, H2. cbn. exact Hdep.
    Qed.

    (** Conversely, an invocation that does not depend on a response of its
        thread can overtake it, so a proof must certify both orders; this
        is the new proof obligation introduced by the dependency frontier. *)
    Lemma independent_invocation_crosses_response (e e' : TaggedEvent E)
        (t : tid) (q : RelaxedSig.handle E) (op : Sig.op (RelaxedSig.effect E)) (ret : Sig.ar op)
        (h' : RelaxedSig.handle E) (op' : Sig.op (RelaxedSig.effect E)) :
      untag e = Build_ThreadEvent t (ResEv q op ret) ->
      untag e' = Build_ThreadEvent t (InvEv h' op') ->
      ~ tev_deps e' q ->
      tagged_can_cross e e'.
    Proof.
      intros H1 H2 Hnd. right. split.
      - rewrite H1, H2. reflexivity.
      - unfold must_precede. rewrite H1, H2. cbn. exact Hnd.
    Qed.

    Definition TDebtCertificate (P Q : TA) (obligations : TObs) : Prop :=
      forall state, P state ->
        tqueue_invariant VE VF M I G AG (fst state) obligations ->
        TDebtSafe Q state obligations.

    Lemma tdebt_protocol_certificate (P Q : TA) (K : TObs -> TA) obligations :
      TDebtProtocol K ->
      (forall state, P state -> K obligations state) ->
      (forall state, K [] state -> Q state) ->
      TDebtCertificate P Q obligations.
    Proof. intros Hprot Hinit Hfinal state HP _. eapply tdebt_protocol_sound; eauto. Qed.

    Lemma tdebt_certificate_mono (P P' Q Q' : TA) obligations :
      (forall s, P s -> P' s) -> (forall s, Q' s -> Q s) ->
      TDebtCertificate P' Q' obligations -> TDebtCertificate P Q obligations.
    Proof.
      intros Hp Hq Hc state HP Hqi. eapply tdebt_safe_mono; [exact Hq |]. apply Hc; auto.
    Qed.

    (** *** Hoare derivations *)

    Definition THTripleDerivation (owner : CallKey F) (thread : tid) (A : Type)
        (P : TA) (program : Prog E A) (store : FutureStore E) (Q : A -> TA)
        (obligations : TObs) (result : A) (final : ProgramConfig E A) : Prop :=
      TCertifiedExecution owner thread A (Build_ProgramConfig program store) obligations final /\
      program_terminal final result /\
      TDebtCertificate P (Q result) obligations.

    Definition THTripleProvable (owner : CallKey F) (thread : tid) (A : Type)
        (P : TA) (program : Prog E A) (store : FutureStore E) (Q : A -> TA) : Prop :=
      exists obligations result final,
        THTripleDerivation owner thread A P program store Q obligations result final.

    Lemma tprovable_ret owner thread A (P : TA) (Q : A -> TA) result store :
      all_resolved store -> (forall s, P s -> Q result s) ->
      THTripleDerivation owner thread A P (Ret result) store Q [] result
        (Build_ProgramConfig (Ret result) store).
    Proof.
      intros Hres Hpost. split; [apply tcertified_refl |]. split.
      - now apply program_terminal_ret.
      - intros s HP _. apply tdebt_safe_done. now apply Hpost.
    Qed.

    Lemma tprovable_tau owner thread A P Q program store obligations result final :
      THTripleDerivation owner thread A P program store Q obligations result final ->
      THTripleDerivation owner thread A P (Tau program) store Q obligations result final.
    Proof.
      intros (Hx & Ht & Hd). split; [| now split].
      eapply tcertified_silent; [apply tagged_tau | exact Hx].
    Qed.

    (** An untagged invocation carries the conservative tag: every handle
        resolved so far. *)
    Lemma tprovable_future owner thread A P Q (op : Sig.op (RelaxedSig.effect E)) k handle store
        (ob : TOb) obligations result final :
      handle_fresh handle store ->
      tev ob = Build_TaggedScheduledEvent owner
                 (Build_TaggedEvent (Build_ThreadEvent thread (InvEv handle op)) (resolved_in store)) ->
      THTripleDerivation owner thread A P (k (MkFutureRef op handle)) (add_pending handle op store) Q
        obligations result final ->
      TDebtCertificate P (Q result) (ob :: obligations) ->
      THTripleDerivation owner thread A P (Future op k) store Q (ob :: obligations) result final.
    Proof.
      intros Hfresh Hev (Hx & Ht & _) Hd. split; [| now split].
      eapply tcertified_emit; [eapply tagged_future; exact Hfresh | exact Hev | exact Hx].
    Qed.

    (** A dependency-tagged invocation. *)
    Lemma tprovable_futureD owner thread A P Q (op : Sig.op (RelaxedSig.effect E)) deps k handle store
        (ob : TOb) obligations result final :
      handle_fresh handle store ->
      tev ob = Build_TaggedScheduledEvent owner
                 (Build_TaggedEvent (Build_ThreadEvent thread (InvEv handle op))
                    (fun q => deps q /\ resolved_in store q)) ->
      THTripleDerivation owner thread A P (k (MkFutureRef op handle)) (add_pending handle op store) Q
        obligations result final ->
      TDebtCertificate P (Q result) (ob :: obligations) ->
      THTripleDerivation owner thread A P (FutureD op deps k) store Q (ob :: obligations) result final.
    Proof.
      intros Hfresh Hev (Hx & Ht & _) Hd. split; [| now split].
      eapply tcertified_emit; [eapply tagged_futureD; exact Hfresh | exact Hev | exact Hx].
    Qed.

    Lemma tprovable_wait_resolved owner thread A P Q (op : Sig.op (RelaxedSig.effect E)) handle ret k store
        obligations result final :
      resolved_at handle op ret store ->
      THTripleDerivation owner thread A P (k ret) store Q obligations result final ->
      THTripleDerivation owner thread A P (Wait (MkFutureRef op handle) k) store Q obligations result final.
    Proof.
      intros Hres (Hx & Ht & Hd). split; [| now split].
      eapply tcertified_silent; [eapply tagged_wait_resolved; exact Hres | exact Hx].
    Qed.

    Lemma tprovable_wait_pending owner thread A P Q (op : Sig.op (RelaxedSig.effect E)) handle ret k
        store store' (ob : TOb) obligations result final :
      resolve_store handle op ret store store' ->
      tev ob = Build_TaggedScheduledEvent owner
                 (Build_TaggedEvent (Build_ThreadEvent thread (ResEv handle op ret)) no_deps) ->
      THTripleDerivation owner thread A P (k ret) store' Q obligations result final ->
      TDebtCertificate P (Q result) (ob :: obligations) ->
      THTripleDerivation owner thread A P (Wait (MkFutureRef op handle) k) store Q
        (ob :: obligations) result final.
    Proof.
      intros Hres Hev (Hx & Ht & _) Hd. split; [| now split].
      eapply tcertified_emit; [eapply tagged_wait_pending; exact Hres | exact Hev | exact Hx].
    Qed.

    Lemma tprovable_resolve owner thread A P Q (op : Sig.op (RelaxedSig.effect E)) handle ret program
        store store' (ob : TOb) obligations result final :
      resolve_store handle op ret store store' ->
      tev ob = Build_TaggedScheduledEvent owner
                 (Build_TaggedEvent (Build_ThreadEvent thread (ResEv handle op ret)) no_deps) ->
      THTripleDerivation owner thread A P program store' Q obligations result final ->
      TDebtCertificate P (Q result) (ob :: obligations) ->
      THTripleDerivation owner thread A P program store Q (ob :: obligations) result final.
    Proof.
      intros Hres Hev (Hx & Ht & _) Hd. split; [| now split].
      eapply tcertified_emit; [eapply tagged_resolve; exact Hres | exact Hev | exact Hx].
    Qed.

    Lemma tprovable_consequence owner thread A (P P' : TA) (Q Q' : A -> TA) program store :
      (forall s, P s -> P' s) -> (forall r s, Q r s -> Q' r s) ->
      THTripleProvable owner thread A P' program store Q ->
      THTripleProvable owner thread A P program store Q'.
    Proof.
      intros Hp Hq (obs & r & fin & Hx & Ht & Hd).
      exists obs, r, fin. split; [exact Hx |]. split; [exact Ht |].
      eapply tdebt_certificate_mono; [exact Hp | apply Hq | exact Hd].
    Qed.

    Lemma thtriple_derivation_sound owner thread A P program store Q obligations result final :
      THTripleDerivation owner thread A P program store Q obligations result final ->
      program_execution_tagged thread (Build_ProgramConfig program store)
        (tobligation_trace obligations) final /\
      program_terminal final result /\
      terase VE VF M I G AG obligations = schedule_trace_tagged owner (tobligation_trace obligations) /\
      TDebtCertificate P (Q result) obligations.
    Proof.
      intros (Hx & Ht & Hd). split; [eapply tcertified_is_program_execution; eauto |].
      split; [exact Ht |]. split; [eapply tcertified_erases_to_schedule; eauto | exact Hd].
    Qed.

    Lemma thtriple_initial_program_produces owner thread A P program Q obligations result final :
      THTripleDerivation owner thread A P program (@empty_store E) Q obligations result final ->
      program_produces_tagged thread program (tobligation_trace obligations) result.
    Proof.
      intros Hd. destruct (thtriple_derivation_sound _ _ _ _ _ _ _ _ _ _ Hd) as (Hx & Ht & _).
      exists final. split; assumption.
    Qed.

    (** The tagged invocation appends exactly the certified trace, so the
        proof-carrying obligations re-establish the queue invariant. *)
    Lemma thtriple_invocation_splices_debt thread (handle : RelaxedSig.handle F)
        (op : Sig.op (RelaxedSig.effect F)) (P : TA) (Q : Sig.ar op -> TA)
        obligations result final q pool queue used existing :
      THTripleDerivation (thread, handle) thread (Sig.ar op) P (M op thread) (@empty_store E) Q
        obligations result final ->
      call_fresh (thread, handle) pool ->
      trace_fresh used (map untag (tobligation_trace obligations)) ->
      tqueue_invariant VE VF M I G AG (Build_TaggedModuleConfig q pool queue used) existing ->
      module_step_tagged_at VE M (thread, handle)
        (OverlayEvent (Build_ThreadEvent thread (@InvEv F handle op)))
        (Build_TaggedModuleConfig q pool queue used)
        (Build_TaggedModuleConfig q
          (Build_CallEntry thread handle (ActiveCall op result) :: pool)
          (queue ++ schedule_trace_tagged (thread, handle) (tobligation_trace obligations))
          (used ++ invocation_keys (map untag (tobligation_trace obligations)))) /\
      tqueue_invariant VE VF M I G AG
        (Build_TaggedModuleConfig q
          (Build_CallEntry thread handle (ActiveCall op result) :: pool)
          (queue ++ schedule_trace_tagged (thread, handle) (tobligation_trace obligations))
          (used ++ invocation_keys (map untag (tobligation_trace obligations))))
        (existing ++ obligations).
    Proof.
      intros Hd Hfc Hft Hq.
      destruct (thtriple_derivation_sound _ _ _ _ _ _ _ _ _ _ Hd) as (Hx & Ht & Herase & _).
      split.
      - eapply tagged_at_invoke; [exact Hfc | exists final; split; assumption | exact Hft].
      - unfold tqueue_invariant, terase in *. cbn in *. rewrite map_app, Hq.
        unfold terase in Herase. rewrite Herase. reflexivity.
    Qed.

    Definition TMethodProvable (thread : tid) (op : Sig.op (RelaxedSig.effect F))
        (P : TA) (Q : Sig.ar op -> TA) : Prop :=
      forall handle : RelaxedSig.handle F,
        THTripleProvable (thread, handle) thread (Sig.ar op) P (M op thread) (@empty_store E) Q.

    Lemma tmethod_provable_trace_sound thread op P Q :
      TMethodProvable thread op P Q ->
      forall handle : RelaxedSig.handle F,
        exists obligations result,
          program_produces_tagged thread (M op thread) (tobligation_trace obligations) result /\
          terase VE VF M I G AG obligations =
            schedule_trace_tagged (thread, handle) (tobligation_trace obligations) /\
          TDebtCertificate P (Q result) obligations.
    Proof.
      intros Hm handle.
      destruct (Hm handle) as (obs & r & fin & Hd).
      destruct (thtriple_derivation_sound _ _ _ _ _ _ _ _ _ _ Hd) as (Hx & Ht & Herase & Hc).
      exists obs, r. split; [exists fin; split; assumption | split; assumption].
    Qed.

  End Logic.

End RelaxedTaggedLogic.
