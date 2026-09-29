(** Module-level scheduling for relaxed implementations. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import LinCCAL.
Require Import RelaxedLTS.
Require Import RelaxedLang.
Require Import RelaxedSemantics.

Import ListNotations.


Module RelaxedModuleSemantics.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.

  (** ** Active overlay invocations *)

  Inductive CallCell (F : RelaxedSig.t) : Type :=
  | ActiveCall
      (op : Sig.op (RelaxedSig.effect F))
      (ret : Sig.ar op)
  | DeadCall.

  Arguments CallCell _ : clear implicits.
  Arguments ActiveCall {F} _ _.
  Arguments DeadCall {F}.

  Record CallEntry (F : RelaxedSig.t) : Type := {
    ce_tid : tid;
    ce_handle : RelaxedSig.handle F;
    ce_cell : CallCell F;
  }.

  Arguments CallEntry _ : clear implicits.
  Arguments Build_CallEntry {F} _ _ _.

  Definition call_key {F} (entry : CallEntry F) : CallKey F :=
    (ce_tid F entry, ce_handle F entry).

  Definition CallPool (F : RelaxedSig.t) : Type := list (CallEntry F).

  Definition call_fresh {F}
      (key : CallKey F) (pool : CallPool F) : Prop :=
    ~ In key (map call_key pool).

  Definition call_pool_well_formed {F} (pool : CallPool F) : Prop :=
    NoDup (map call_key pool).

  (** A completed call remains as [DeadCall], preventing reuse of its
      overlay handle later in the same execution. *)
  Inductive finish_call {F}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (ret : Sig.ar op) : CallPool F -> CallPool F -> Prop :=
  | finish_here tail :
      finish_call t h op ret
        (Build_CallEntry t h (ActiveCall op ret) :: tail)
        (Build_CallEntry t h DeadCall :: tail)
  | finish_next t' h' cell pool pool'
      (Hneq : (t', h') <> (t, h))
      (Hfinish : finish_call t h op ret pool pool') :
      finish_call t h op ret
        (Build_CallEntry t' h' cell :: pool)
        (Build_CallEntry t' h' cell :: pool').

  Lemma finish_call_keys
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (ret : Sig.ar op)
      (pool pool' : CallPool F) :
    finish_call t h op ret pool pool' ->
    map call_key pool = map call_key pool'.
  Proof.
    intro Hfinish.
    induction Hfinish.
    - reflexivity.
    - cbn. f_equal. exact IHHfinish.
  Qed.

  Lemma finish_call_well_formed
      {F : RelaxedSig.t}
      (t : tid)
      (h : RelaxedSig.handle F)
      (op : Sig.op (RelaxedSig.effect F))
      (ret : Sig.ar op)
      (pool pool' : CallPool F) :
    finish_call t h op ret pool pool' ->
    call_pool_well_formed pool ->
    call_pool_well_formed pool'.
  Proof.
    intros Hfinish Hwf.
    unfold call_pool_well_formed in *.
    erewrite <- finish_call_keys; eauto.
  Qed.

  (** ** Pending underlay continuations *)

  Record ScheduledEvent
      (E F : RelaxedSig.t) : Type := {
    se_owner : CallKey F;
    se_event : ThreadEvent E;
  }.

  Arguments ScheduledEvent _ _ : clear implicits.
  Arguments Build_ScheduledEvent {E F} _ _.
  Arguments se_owner {E F} _.
  Arguments se_event {E F} _.

  Definition EventQueue (E F : RelaxedSig.t) : Type :=
    list (ScheduledEvent E F).

  Definition schedule_trace {E F}
      (owner : CallKey F)
      (trace : list (ThreadEvent E)) : EventQueue E F :=
    map (Build_ScheduledEvent owner) trace.

  Definition owner_done {E F}
      (owner : CallKey F) (queue : EventQueue E F) : Prop :=
    ~ In owner (map se_owner queue).

  (** Events from different threads may always interleave.  Within one
      thread, only two invocation events related by the directed
      semi-independence relation may commute.  In particular, a response is
      a barrier and therefore records the dependency introduced by [wait]. *)
  Definition invocation_can_cross {E}
      (earlier later : ThreadEvent E) : Prop :=
    match te_ev E earlier, te_ev E later with
    | InvEv _ op1, InvEv _ op2 => semi_independent E op1 op2
    | _, _ => False
    end.

  Definition event_can_cross {E}
      (earlier later : ThreadEvent E) : Prop :=
    te_tid E earlier <> te_tid E later \/
    (te_tid E earlier = te_tid E later /\
     invocation_can_cross earlier later).

  (** [select_frontier candidate queue queue'] removes one candidate that
      can commute left across every event preceding it. *)
  Inductive select_frontier {E F}
      (candidate : ScheduledEvent E F) :
      EventQueue E F -> EventQueue E F -> Prop :=
  | select_here suffix :
      select_frontier candidate
        (candidate :: suffix) suffix
  | select_next earlier queue queue'
      (Hcross : event_can_cross
        (se_event earlier) (se_event candidate))
      (Hselect : select_frontier candidate queue queue') :
      select_frontier candidate
        (earlier :: queue) (earlier :: queue').

  Lemma select_frontier_member
      {E F : RelaxedSig.t}
      (candidate : ScheduledEvent E F)
      (queue queue' : EventQueue E F) :
    select_frontier candidate queue queue' ->
    In candidate queue.
  Proof.
    intro Hselect.
    induction Hselect; cbn; auto.
  Qed.

  Lemma select_frontier_length
      {E F : RelaxedSig.t}
      (candidate : ScheduledEvent E F)
      (queue queue' : EventQueue E F) :
    select_frontier candidate queue queue' ->
    length queue = S (length queue').
  Proof.
    intro Hselect.
    induction Hselect; cbn; congruence.
  Qed.

  (** Invocation handles selected by a method trace must be globally fresh
      for their thread, including handles of calls that have already
      completed. *)
  Fixpoint invocation_keys {E}
      (trace : list (ThreadEvent E)) : list (CallKey E) :=
    match trace with
    | [] => []
    | ev :: trace' =>
        match te_ev E ev with
        | InvEv h _ => (te_tid E ev, h) :: invocation_keys trace'
        | ResEv _ _ _ => invocation_keys trace'
        end
    end.

  Definition trace_fresh {E}
      (used : list (CallKey E))
      (trace : list (ThreadEvent E)) : Prop :=
    NoDup (invocation_keys trace) /\
    forall key, In key (invocation_keys trace) -> ~ In key used.

  (** ** The dependency frontier (WSC edit, 2026-09-28)

      The scheduler of the paper's [Step] rule emits the events of the
      active continuations from a frontier that respects exactly three
      kinds of predecessor constraints between events of one thread:

      - (F1) an invocation precedes its own response;
      - (F2) two invocations that the underlay does not declare
        semi-independent keep their program order;
      - (F3) a response precedes every invocation that depends on it.

      Every other pair is unconstrained.  In particular an invocation may
      overtake a response it does not depend on, and a response may be
      emitted as soon as its own invocation has been.  [select_frontier]
      above is the previous, positional frontier: it is recovered by
      tagging every invocation with all handles resolved before it, and is
      strictly more restrictive ([select_frontier_tagged_of_positional]). *)

  Record TaggedScheduledEvent (E F : RelaxedSig.t) : Type := {
    ts_owner : CallKey F;
    ts_event : TaggedEvent E;
  }.

  Arguments TaggedScheduledEvent _ _ : clear implicits.
  Arguments Build_TaggedScheduledEvent {E F} _ _.
  Arguments ts_owner {E F} _.
  Arguments ts_event {E F} _.

  Definition TaggedQueue (E F : RelaxedSig.t) : Type :=
    list (TaggedScheduledEvent E F).

  Definition untag_scheduled {E F} (m : TaggedScheduledEvent E F) : ScheduledEvent E F :=
    Build_ScheduledEvent (ts_owner m) (untag (ts_event m)).

  Definition schedule_trace_tagged {E F}
      (owner : CallKey F)
      (trace : list (TaggedEvent E)) : TaggedQueue E F :=
    map (Build_TaggedScheduledEvent owner) trace.

  Definition owner_done_tagged {E F}
      (owner : CallKey F) (queue : TaggedQueue E F) : Prop :=
    ~ In owner (map ts_owner queue).

  (** [must_precede earlier later]: the constraints (F1)--(F3), for two
      events of the same thread. *)
  Definition must_precede {E}
      (earlier later : TaggedEvent E) : Prop :=
    match te_ev E (untag earlier), te_ev E (untag later) with
    | InvEv h _, ResEv h' _ _ => h = h'
    | InvEv _ op1, InvEv _ op2 => ~ semi_independent E op1 op2
    | ResEv h _ _, InvEv _ _ => tev_deps later h
    | ResEv _ _ _, ResEv _ _ _ => False
    end.

  Definition tagged_can_cross {E}
      (earlier later : TaggedEvent E) : Prop :=
    te_tid E (untag earlier) <> te_tid E (untag later) \/
    (te_tid E (untag earlier) = te_tid E (untag later) /\
     ~ must_precede earlier later).

  (** [select_frontier_tagged candidate queue queue'] removes one candidate
      that may move left across every event preceding it. *)
  Inductive select_frontier_tagged {E F}
      (candidate : TaggedScheduledEvent E F) :
      TaggedQueue E F -> TaggedQueue E F -> Prop :=
  | tagged_select_here suffix :
      select_frontier_tagged candidate
        (candidate :: suffix) suffix
  | tagged_select_next earlier queue queue'
      (Hcross : tagged_can_cross
        (ts_event earlier) (ts_event candidate))
      (Hselect : select_frontier_tagged candidate queue queue') :
      select_frontier_tagged candidate
        (earlier :: queue) (earlier :: queue').

  Lemma select_frontier_tagged_member
      {E F : RelaxedSig.t}
      (candidate : TaggedScheduledEvent E F)
      (queue queue' : TaggedQueue E F) :
    select_frontier_tagged candidate queue queue' ->
    In candidate queue.
  Proof.
    intro Hselect.
    induction Hselect; cbn; auto.
  Qed.

  Lemma select_frontier_tagged_length
      {E F : RelaxedSig.t}
      (candidate : TaggedScheduledEvent E F)
      (queue queue' : TaggedQueue E F) :
    select_frontier_tagged candidate queue queue' ->
    length queue = S (length queue').
  Proof.
    intro Hselect.
    induction Hselect; cbn; congruence.
  Qed.

  (** The positional frontier is contained in the dependency frontier:
      a same-thread pair the old rule lets commute is a pair of
      semi-independent invocations, which (F2) lets commute too. *)
  Lemma event_can_cross_tagged {E}
      (earlier later : TaggedEvent E) :
    event_can_cross (untag earlier) (untag later) ->
    tagged_can_cross earlier later.
  Proof.
    intros [Hneq | [Heq Hind]]; [left; exact Hneq |].
    right. split; [exact Heq |].
    unfold invocation_can_cross in Hind. unfold must_precede.
    destruct (te_ev E (untag earlier)) as [h1 op1 | h1 op1 r1];
      destruct (te_ev E (untag later)) as [h2 op2 | h2 op2 r2]; try contradiction.
    intros Hno. apply Hno. exact Hind.
  Qed.

  Lemma select_frontier_tagged_of_positional
      {E F : RelaxedSig.t}
      (cand : ScheduledEvent E F)
      (queue : TaggedQueue E F)
      (queue' : EventQueue E F) :
    select_frontier cand (map untag_scheduled queue) queue' ->
    exists candidate queue'',
      untag_scheduled candidate = cand /\
      select_frontier_tagged candidate queue queue'' /\
      map untag_scheduled queue'' = queue'.
  Proof.
    revert queue'. induction queue as [| m queue IH]; intros queue' Hselect.
    - inversion Hselect.
    - cbn in Hselect. inversion Hselect; subst.
      + exists m, queue. split; [reflexivity |]. split; [apply tagged_select_here | reflexivity].
      + destruct (IH _ Hselect0) as (candidate & queue'' & Hcand & Hsel'' & Heq'').
        exists candidate, (m :: queue''). split; [exact Hcand |]. split.
        * apply tagged_select_next; auto. apply event_can_cross_tagged.
          change (untag (ts_event candidate)) with (se_event (untag_scheduled candidate)).
          change (untag (ts_event m)) with (se_event (untag_scheduled m)).
          rewrite Hcand. exact Hcross.
        * cbn. congruence.
  Qed.

  (** ** Module configurations and transitions *)

  Inductive ModuleEvent (E F : RelaxedSig.t) : Type :=
  | UnderlayEvent (ev : ThreadEvent E)
  | OverlayEvent (ev : ThreadEvent F).

  Arguments ModuleEvent _ _ : clear implicits.
  Arguments UnderlayEvent {E F} _.
  Arguments OverlayEvent {E F} _.

  Record ModuleConfig {E F}
      (VE : RelaxedLTSSpec.LTS E) : Type := {
    mc_lts_state : RelaxedLTSSpec.State VE;
    mc_calls : CallPool F;
    mc_queue : EventQueue E F;
    mc_used_underlay : list (CallKey E);
  }.

  Arguments ModuleConfig {E F} _.
  Arguments Build_ModuleConfig {E F VE} _ _ _ _.
  Arguments mc_lts_state {E F VE} _.
  Arguments mc_calls {E F VE} _.
  Arguments mc_queue {E F VE} _.
  Arguments mc_used_underlay {E F VE} _.

  Section ModuleSemantics.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (M : RelaxedModuleImpl E F).

    Inductive module_step :
        ModuleEvent E F ->
        ModuleConfig VE -> ModuleConfig VE -> Prop :=
    | module_invoke t h op q pool queue used trace ret
        (Hfresh_call : call_fresh (t, h) pool)
        (Hmethod : program_produces t (M op t) trace ret)
        (Hfresh_trace : trace_fresh used trace) :
        module_step
          (OverlayEvent
            (Build_ThreadEvent t (@InvEv F h op)))
          (Build_ModuleConfig q pool queue used)
          (Build_ModuleConfig q
            (Build_CallEntry t h (ActiveCall op ret) :: pool)
            (queue ++ schedule_trace (t, h) trace)
            (used ++ invocation_keys trace))

    | module_underlay candidate q q' pool queue queue' used
        (Hselect : select_frontier candidate queue queue')
        (Hlts : RelaxedLTSSpec.Step VE
          (se_event candidate) q q') :
        module_step
          (UnderlayEvent (se_event candidate))
          (Build_ModuleConfig q pool queue used)
          (Build_ModuleConfig q' pool queue' used)

    | module_return t h op ret q pool pool' queue used
        (Hfinish : finish_call t h op ret pool pool')
        (Hdone : owner_done (t, h) queue) :
        module_step
          (OverlayEvent
            (Build_ThreadEvent t (@ResEv F h op ret)))
          (Build_ModuleConfig q pool queue used)
          (Build_ModuleConfig q pool' queue used).

    (** The ordinary module transition hides which overlay call owns an
        underlay event.  Handle-focused rely/guarantee simulation needs that
        owner explicitly in order to distinguish [G], [R_sys], and [R_env]. *)
    Inductive module_step_at :
        CallKey F ->
        ModuleEvent E F ->
        ModuleConfig VE -> ModuleConfig VE -> Prop :=
    | module_at_invoke t h op q pool queue used trace ret
        (Hfresh_call : call_fresh (t, h) pool)
        (Hmethod : program_produces t (M op t) trace ret)
        (Hfresh_trace : trace_fresh used trace) :
        module_step_at (t, h)
          (OverlayEvent
            (Build_ThreadEvent t (@InvEv F h op)))
          (Build_ModuleConfig q pool queue used)
          (Build_ModuleConfig q
            (Build_CallEntry t h (ActiveCall op ret) :: pool)
            (queue ++ schedule_trace (t, h) trace)
            (used ++ invocation_keys trace))

    | module_at_underlay candidate q q' pool queue queue' used
        (Hselect : select_frontier candidate queue queue')
        (Hlts : RelaxedLTSSpec.Step VE
          (se_event candidate) q q') :
        module_step_at (se_owner candidate)
          (UnderlayEvent (se_event candidate))
          (Build_ModuleConfig q pool queue used)
          (Build_ModuleConfig q' pool queue' used)

    | module_at_return t h op ret q pool pool' queue used
        (Hfinish : finish_call t h op ret pool pool')
        (Hdone : owner_done (t, h) queue) :
        module_step_at (t, h)
          (OverlayEvent
            (Build_ThreadEvent t (@ResEv F h op ret)))
          (Build_ModuleConfig q pool queue used)
          (Build_ModuleConfig q pool' queue used).

    Lemma module_step_at_is_step owner ev c c' :
      module_step_at owner ev c c' -> module_step ev c c'.
    Proof.
      intro Hstep.
      inversion Hstep; subst; econstructor; eauto.
    Qed.

    Lemma module_step_has_owner ev c c' :
      module_step ev c c' ->
      exists owner, module_step_at owner ev c c'.
    Proof.
      intro Hstep.
      inversion Hstep; subst.
      - eexists. eapply module_at_invoke; eauto.
      - eexists. eapply module_at_underlay; eauto.
      - eexists. eapply module_at_return; eauto.
    Qed.

    Inductive module_error : @ModuleConfig E F VE -> Prop :=
    | module_underlay_error candidate q pool queue queue' used
        (Hselect : select_frontier candidate queue queue')
        (Herror : RelaxedLTSSpec.Error VE
          (se_event candidate) q) :
        module_error (Build_ModuleConfig q pool queue used).

    Inductive module_error_at :
        CallKey F -> @ModuleConfig E F VE -> Prop :=
    | module_underlay_error_at candidate q pool queue queue' used
        (Hselect : select_frontier candidate queue queue')
        (Herror : RelaxedLTSSpec.Error VE
          (se_event candidate) q) :
        module_error_at (se_owner candidate)
          (Build_ModuleConfig q pool queue used).

    Lemma module_error_at_is_error owner c :
      module_error_at owner c -> module_error c.
    Proof.
      intro Herror.
      inversion Herror; subst. econstructor; eauto.
    Qed.

    Lemma module_error_has_owner c :
      module_error c -> exists owner, module_error_at owner c.
    Proof.
      intro Herror.
      inversion Herror; subst.
      exists (se_owner candidate). econstructor; eauto.
    Qed.

    Definition initial_module
        (q : RelaxedLTSSpec.State VE) : @ModuleConfig E F VE :=
      Build_ModuleConfig q [] [] [].

    Definition module_steps :=
      clos_refl_trans (@ModuleConfig E F VE)
        (fun c c' => exists ev, module_step ev c c').

    Inductive module_execution :
        @ModuleConfig E F VE ->
        list (ModuleEvent E F) ->
        @ModuleConfig E F VE -> Prop :=
    | module_execution_refl c :
        module_execution c [] c
    | module_execution_cons c1 c2 c3 ev trace
        (Hstep : module_step ev c1 c2)
        (Hexec : module_execution c2 trace c3) :
        module_execution c1 (ev :: trace) c3.

    Lemma initial_call_pool_well_formed q :
      call_pool_well_formed (mc_calls (initial_module q)).
    Proof.
      constructor.
    Qed.

    Lemma module_step_call_pool_well_formed ev c c' :
      module_step ev c c' ->
      call_pool_well_formed (mc_calls c) ->
      call_pool_well_formed (mc_calls c').
    Proof.
      intros Hstep Hwf.
      inversion Hstep; subst; cbn in *.
      - constructor; assumption.
      - exact Hwf.
      - eapply finish_call_well_formed; eauto.
    Qed.

  End ModuleSemantics.


  (** ** Module transitions over the dependency frontier (WSC edit) *)

  Record TaggedModuleConfig {E F}
      (VE : RelaxedLTSSpec.LTS E) : Type := {
    tm_lts_state : RelaxedLTSSpec.State VE;
    tm_calls : CallPool F;
    tm_queue : TaggedQueue E F;
    tm_used_underlay : list (CallKey E);
  }.

  Arguments TaggedModuleConfig {E F} _.
  Arguments Build_TaggedModuleConfig {E F VE} _ _ _ _.
  Arguments tm_lts_state {E F VE} _.
  Arguments tm_calls {E F VE} _.
  Arguments tm_queue {E F VE} _.
  Arguments tm_used_underlay {E F VE} _.

  Definition untag_config {E F} {VE : RelaxedLTSSpec.LTS E}
      (c : @TaggedModuleConfig E F VE) : @ModuleConfig E F VE :=
    Build_ModuleConfig (tm_lts_state c) (tm_calls c)
      (map untag_scheduled (tm_queue c)) (tm_used_underlay c).

  Lemma untag_schedule_trace {E F} (owner : CallKey F) (trace : list (TaggedEvent E)) :
    map untag_scheduled (schedule_trace_tagged owner trace) =
    schedule_trace owner (map untag trace).
  Proof.
    unfold schedule_trace_tagged, schedule_trace. rewrite !map_map. reflexivity.
  Qed.

  Lemma owner_done_tagged_iff {E F} (owner : CallKey F) (queue : TaggedQueue E F) :
    owner_done_tagged owner queue <-> owner_done owner (map untag_scheduled queue).
  Proof.
    unfold owner_done_tagged, owner_done. rewrite map_map. reflexivity.
  Qed.

  Section TaggedModuleSemantics.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (M : RelaxedModuleImpl E F).

    (** [Inv], [Step] and [Ret] of the paper, with [Step] emitting from the
        dependency frontier and erasing the tag as the event enters the
        global trace. *)
    Inductive module_step_tagged :
        ModuleEvent E F ->
        TaggedModuleConfig VE -> TaggedModuleConfig VE -> Prop :=
    | tagged_invoke t h op q pool queue used trace ret
        (Hfresh_call : call_fresh (t, h) pool)
        (Hmethod : program_produces_tagged t (M op t) trace ret)
        (Hfresh_trace : trace_fresh used (map untag trace)) :
        module_step_tagged
          (OverlayEvent
            (Build_ThreadEvent t (@InvEv F h op)))
          (Build_TaggedModuleConfig q pool queue used)
          (Build_TaggedModuleConfig q
            (Build_CallEntry t h (ActiveCall op ret) :: pool)
            (queue ++ schedule_trace_tagged (t, h) trace)
            (used ++ invocation_keys (map untag trace)))

    | tagged_underlay candidate q q' pool queue queue' used
        (Hselect : select_frontier_tagged candidate queue queue')
        (Hlts : RelaxedLTSSpec.Step VE
          (untag (ts_event candidate)) q q') :
        module_step_tagged
          (UnderlayEvent (untag (ts_event candidate)))
          (Build_TaggedModuleConfig q pool queue used)
          (Build_TaggedModuleConfig q' pool queue' used)

    | tagged_return t h op ret q pool pool' queue used
        (Hfinish : finish_call t h op ret pool pool')
        (Hdone : owner_done_tagged (t, h) queue) :
        module_step_tagged
          (OverlayEvent
            (Build_ThreadEvent t (@ResEv F h op ret)))
          (Build_TaggedModuleConfig q pool queue used)
          (Build_TaggedModuleConfig q pool' queue used).

    Definition initial_tagged_module
        (q : RelaxedLTSSpec.State VE) : @TaggedModuleConfig E F VE :=
      Build_TaggedModuleConfig q [] [] [].

    Inductive module_execution_tagged :
        @TaggedModuleConfig E F VE ->
        list (ModuleEvent E F) ->
        @TaggedModuleConfig E F VE -> Prop :=
    | tagged_module_execution_refl c :
        module_execution_tagged c [] c
    | tagged_module_execution_cons c1 c2 c3 ev trace
        (Hstep : module_step_tagged ev c1 c2)
        (Hexec : module_execution_tagged c2 trace c3) :
        module_execution_tagged c1 (ev :: trace) c3.

    (** *** (E1) Conservative extension: every positional module step is a
        step of the dependency frontier. *)

    Lemma module_step_lift ev cd c' :
      module_step VE M ev (untag_config cd) c' ->
      exists cd', module_step_tagged ev cd cd' /\ untag_config cd' = c'.
    Proof.
      intros Hstep. destruct cd as [q pool queue used]. cbn in Hstep.
      inversion Hstep; subst.
      - (* invoke *)
        destruct (program_produces_untag_tagged _ _ _ _ Hmethod) as (trace' & Hmethod' & Heq).
        eexists. split.
        + apply tagged_invoke; eauto. rewrite Heq. exact Hfresh_trace.
        + unfold untag_config. cbn. rewrite map_app, untag_schedule_trace, Heq. reflexivity.
      - (* underlay *)
        destruct (select_frontier_tagged_of_positional _ _ _ Hselect)
          as (candidate' & queue'' & Hcand & Hsel & Heq).
        eexists. split.
        + rewrite <- Hcand. apply tagged_underlay; eauto. rewrite <- Hcand in Hlts. exact Hlts.
        + unfold untag_config. cbn. rewrite Heq. reflexivity.
      - (* return *)
        eexists. split.
        + apply tagged_return; eauto. apply owner_done_tagged_iff. exact Hdone.
        + reflexivity.
    Qed.

    Lemma module_execution_lift cd trace c' :
      module_execution VE M (untag_config cd) trace c' ->
      exists cd', module_execution_tagged cd trace cd' /\ untag_config cd' = c'.
    Proof.
      intros Hexec. remember (untag_config cd) as c eqn:Hc. revert cd Hc.
      induction Hexec as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros cd Hc; subst.
      - exists cd. split; [apply tagged_module_execution_refl | reflexivity].
      - destruct (module_step_lift _ _ _ Hstep) as (cd2 & Hstep' & Heq2).
        destruct (IH cd2 (eq_sym Heq2)) as (cd3 & Hexec' & Heq3).
        exists cd3. split; auto. eapply tagged_module_execution_cons; eauto.
    Qed.

    Theorem positional_traces_are_tagged_traces q trace c' :
      module_execution VE M (initial_module VE q) trace c' ->
      exists cd', module_execution_tagged (initial_tagged_module q) trace cd' /\
                  untag_config cd' = c'.
    Proof.
      intros Hexec. apply module_execution_lift. exact Hexec.
    Qed.

    (** *** (E3) An emitted event is independent of everything it overtook
        (Lemma lem:wsc-indep; Rensink--Wehrheim's Prop. 1): every event
        queued before the selected one may be crossed by it, i.e. for a
        same-thread event none of (F1)--(F3) holds. *)

    Lemma select_frontier_tagged_split
        (candidate : TaggedScheduledEvent E F) (queue queue' : TaggedQueue E F) :
      select_frontier_tagged candidate queue queue' ->
      exists pre post,
        queue = pre ++ candidate :: post /\ queue' = pre ++ post /\
        Forall (fun e => tagged_can_cross (ts_event e) (ts_event candidate)) pre.
    Proof.
      intros Hsel. induction Hsel as [suffix | earlier queue queue' Hcross Hsel IH].
      - exists [], suffix. auto.
      - destruct IH as (pre & post & -> & -> & Hall).
        exists (earlier :: pre), post. cbn. auto.
    Qed.

    (** *** (E2) Dependency soundness: when the scheduler emits an invocation,
        the responses it is tagged with have already been emitted. *)

    Definition emitted_response
        (trace : list (ModuleEvent E F)) (t : tid) (q : RelaxedSig.handle E) : Prop :=
      exists j r, nth_error trace j = Some (UnderlayEvent r) /\
                  te_tid E r = t /\ is_response_of q r.

    (** The invariant: for every queued invocation and every handle in its
        tag, the response of that handle by the same thread is either
        queued before it or already in the global trace. *)
    Definition queue_dep_ok
        (trace : list (ModuleEvent E F)) (queue : TaggedQueue E F) : Prop :=
      forall j m q,
        nth_error queue j = Some m ->
        tev_deps (ts_event m) q ->
        (exists i r, i < j /\ nth_error queue i = Some r /\
                     te_tid E (untag (ts_event r)) = te_tid E (untag (ts_event m)) /\
                     is_response_of q (untag (ts_event r))) \/
        emitted_response trace (te_tid E (untag (ts_event m))) q.

    (** Responses in the queue carry no dependencies. *)
    Definition queue_deps_ok (queue : TaggedQueue E F) : Prop :=
      forall m q, In m queue -> tev_deps (ts_event m) q -> is_invocation (untag (ts_event m)).

    Lemma queue_deps_ok_app queue queue' :
      queue_deps_ok queue -> queue_deps_ok queue' -> queue_deps_ok (queue ++ queue').
    Proof.
      intros H1 H2 m q Hm Hq. apply in_app_or in Hm. destruct Hm as [Hm | Hm]; eauto.
    Qed.

    Lemma queue_deps_ok_sub queue queue' :
      (forall m, In m queue' -> In m queue) -> queue_deps_ok queue -> queue_deps_ok queue'.
    Proof. intros Hsub H m q Hm Hq. eapply H; eauto. Qed.

    Lemma queue_deps_ok_schedule {R : Type} (owner : CallKey F) t (p : Prog E R) trace' ret :
      program_produces_tagged t p trace' ret ->
      queue_deps_ok (schedule_trace_tagged owner trace').
    Proof.
      intros Hprod m q Hm Hq. unfold schedule_trace_tagged in Hm.
      apply in_map_iff in Hm. destruct Hm as (m' & <- & Hm'). cbn in *.
      pose proof (program_produces_tagged_deps_invocation _ _ _ _ Hprod) as Hall.
      rewrite Forall_forall in Hall. eapply Hall; eauto.
    Qed.

    Lemma module_step_tagged_deps_ok ev c c' :
      module_step_tagged ev c c' -> queue_deps_ok (tm_queue c) -> queue_deps_ok (tm_queue c').
    Proof.
      intros Hstep Hok. inversion Hstep; subst; cbn in *.
      - apply queue_deps_ok_app; auto. eapply queue_deps_ok_schedule; eauto.
      - eapply queue_deps_ok_sub; [| exact Hok].
        destruct (select_frontier_tagged_split _ _ _ Hselect) as (pre & post & -> & -> & _).
        intros m Hm. apply in_app_or in Hm. apply in_or_app. destruct Hm; [left | right; right]; auto.
      - exact Hok.
    Qed.

    Lemma module_execution_tagged_deps_ok c trace c' :
      module_execution_tagged c trace c' -> queue_deps_ok (tm_queue c) -> queue_deps_ok (tm_queue c').
    Proof.
      intros Hexec. induction Hexec; auto. intros Hok. apply IHHexec. eapply module_step_tagged_deps_ok; eauto.
    Qed.

    Lemma emitted_response_app trace trace' t q :
      emitted_response trace t q -> emitted_response (trace ++ trace') t q.
    Proof.
      intros (j & r & Hj & Ht & Hr). exists j, r. split; auto.
      rewrite nth_error_app1; auto. apply nth_error_Some. congruence.
    Qed.

    Lemma nth_error_remove_middle {A : Type} (pre post : list A) (c : A) i (x : A) :
      nth_error (pre ++ post) i = Some x ->
      (i < length pre /\ nth_error (pre ++ c :: post) i = Some x) \/
      (length pre <= i /\ nth_error (pre ++ c :: post) (S i) = Some x).
    Proof.
      intros Hi. destruct (lt_dec i (length pre)) as [Hlt | Hge].
      - left. split; auto. rewrite nth_error_app1 in Hi by auto. rewrite nth_error_app1; auto.
      - right. split; [lia |]. rewrite nth_error_app2 in Hi by lia.
        rewrite nth_error_app2 by lia.
        replace (S i - length pre) with (S (i - length pre)) by lia.
        cbn. exact Hi.
    Qed.

    Lemma queue_dep_ok_invoke {R : Type} trace queue ev (owner : CallKey F) t (p : Prog E R) trace' ret :
      program_produces_tagged t p trace' ret ->
      fst owner = t ->
      queue_dep_ok trace queue ->
      queue_dep_ok (trace ++ [ev]) (queue ++ schedule_trace_tagged owner trace').
    Proof.
      intros Hprod Howner Hok j m q Hj Hq.
      destruct (lt_dec j (length queue)) as [Hlt | Hge].
      - rewrite nth_error_app1 in Hj by auto.
        destruct (Hok j m q Hj Hq) as [(i & r & Hij & Hi & Ht & Hr) | Hem].
        + left. exists i, r. split; auto. split; auto. rewrite nth_error_app1; auto. lia.
        + right. apply emitted_response_app. exact Hem.
      - rewrite nth_error_app2 in Hj by lia.
        unfold schedule_trace_tagged in Hj. rewrite nth_error_map in Hj.
        destruct (nth_error trace' (j - length queue)) as [m' |] eqn:Hm'; [| discriminate].
        cbn in Hj. inversion Hj; subst m. cbn in Hq.
        destruct (program_produces_tagged_dependency _ _ _ _ Hprod _ _ _ Hm' Hq)
          as (j' & r' & Hj' & Hr' & Hresp).
        left. exists (length queue + j'), (Build_TaggedScheduledEvent owner r').
        split; [lia |]. split.
        + rewrite nth_error_app2 by lia. replace (length queue + j' - length queue) with j' by lia.
          unfold schedule_trace_tagged. rewrite nth_error_map, Hr'. reflexivity.
        + cbn. split; [| exact Hresp].
          pose proof (program_produces_tagged_trace_tid _ _ _ _ Hprod) as Htid.
          rewrite Forall_forall in Htid.
          rewrite (Htid r'); [| eapply nth_error_In; eauto].
          rewrite (Htid m'); [| eapply nth_error_In; eauto]. reflexivity.
    Qed.


    Lemma nth_error_middle_cases {A : Type} (pre post : list A) (c : A) i (x : A) :
      nth_error (pre ++ c :: post) i = Some x ->
      (i < length pre /\ nth_error (pre ++ post) i = Some x) \/
      (i = length pre /\ x = c) \/
      (length pre < i /\ nth_error (pre ++ post) (i - 1) = Some x).
    Proof.
      intros Hi. destruct (lt_eq_lt_dec i (length pre)) as [[Hlt | Heq] | Hgt].
      - left. split; auto. rewrite nth_error_app1 in Hi by auto. rewrite nth_error_app1; auto.
      - right. left. split; auto. subst i. rewrite nth_error_app2 in Hi by lia.
        rewrite Nat.sub_diag in Hi. cbn in Hi. inversion Hi. reflexivity.
      - right. right. split; auto. rewrite nth_error_app2 in Hi by lia.
        rewrite nth_error_app2 by lia.
        replace (i - length pre) with (S (i - 1 - length pre)) in Hi by lia.
        cbn in Hi. exact Hi.
    Qed.

    Lemma queue_dep_ok_underlay trace queue queue' candidate :
      select_frontier_tagged candidate queue queue' ->
      queue_dep_ok trace queue ->
      queue_dep_ok (trace ++ [UnderlayEvent (untag (ts_event candidate))]) queue'.
    Proof.
      intros Hsel Hok.
      destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & -> & -> & _).
      intros j' m q Hj' Hq.
      destruct (nth_error_remove_middle pre post candidate j' m Hj') as [[Hlt Hj] | [Hge Hj]].
      - (* [m] is in [pre] *)
        destruct (Hok j' m q Hj Hq) as [(i & r & Hij & Hi & Ht & Hr) | Hem].
        + left. exists i, r. split; auto. split; auto.
          rewrite nth_error_app1 in Hi by lia. rewrite nth_error_app1 by lia. exact Hi.
        + right. apply emitted_response_app. exact Hem.
      - (* [m] is in [post], at position [S j'] of the old queue *)
        destruct (Hok (S j') m q Hj Hq) as [(i & r & Hij & Hi & Ht & Hr) | Hem].
        + destruct (nth_error_middle_cases pre post candidate i r Hi) as [[Hlt Hi'] | [[Heq Hrc] | [Hgt Hi']]].
          * left. exists i, r. split; [lia |]. auto.
          * right. subst r. exists (length trace), (untag (ts_event candidate)).
            split; [| auto]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
          * left. exists (i - 1), r. split; [lia |]. auto.
        + right. apply emitted_response_app. exact Hem.
    Qed.

    Lemma queue_dep_ok_return trace queue ev :
      queue_dep_ok trace queue -> queue_dep_ok (trace ++ [ev]) queue.
    Proof.
      intros Hok j m q Hj Hq. destruct (Hok j m q Hj Hq) as [H | H]; [left; exact H |].
      right. apply emitted_response_app. exact H.
    Qed.

    Lemma queue_dep_ok_initial : queue_dep_ok [] [].
    Proof. intros j m q Hj. destruct j; discriminate. Qed.

    Lemma module_step_tagged_dep_ok trace ev c c' :
      module_step_tagged ev c c' ->
      queue_dep_ok trace (tm_queue c) ->
      queue_dep_ok (trace ++ [ev]) (tm_queue c').
    Proof.
      intros Hstep Hok. inversion Hstep; subst; cbn in *.
      - eapply queue_dep_ok_invoke; eauto.
      - eapply queue_dep_ok_underlay; eauto.
      - apply queue_dep_ok_return. exact Hok.
    Qed.

    Lemma module_execution_tagged_dep_ok trace0 c trace c' :
      module_execution_tagged c trace c' ->
      queue_dep_ok trace0 (tm_queue c) ->
      queue_dep_ok (trace0 ++ trace) (tm_queue c').
    Proof.
      intros Hexec. revert trace0. induction Hexec as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros trace0 Hok.
      - rewrite app_nil_r. exact Hok.
      - replace (trace0 ++ ev :: trace) with ((trace0 ++ [ev]) ++ trace) by (rewrite <- app_assoc; reflexivity).
        apply IH. eapply module_step_tagged_dep_ok; eauto.
    Qed.

    (** Lemma lem:wsc-dep at the module level: if the scheduler can emit an
        invocation from a reachable configuration, then the response of
        every handle in its tag has already been emitted by its thread. *)
    Theorem module_dependency_soundness q0 trace c candidate queue' q :
      module_execution_tagged (initial_tagged_module q0) trace c ->
      select_frontier_tagged candidate (tm_queue c) queue' ->
      tev_deps (ts_event candidate) q ->
      emitted_response trace (te_tid E (untag (ts_event candidate))) q.
    Proof.
      intros Hexec Hsel Hq.
      pose proof (module_execution_tagged_dep_ok [] _ _ _ Hexec queue_dep_ok_initial) as Hok.
      cbn in Hok.
      assert (Hinv : is_invocation (untag (ts_event candidate))).
      { pose proof (module_execution_tagged_deps_ok _ _ _ Hexec) as Hdeps.
        eapply Hdeps; eauto; [intros m q' [] |].
        eapply select_frontier_tagged_member; eauto. }
      destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & Hqueue & _ & Hall).
      rewrite Hqueue in Hok.
      assert (Hcand : nth_error (pre ++ candidate :: post) (length pre) = Some candidate).
      { rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
      destruct (Hok (length pre) candidate q Hcand Hq) as [(i & r & Hi & Hir & Ht & Hr) | Hem]; [| exact Hem].
      exfalso.
      rewrite nth_error_app1 in Hir by lia.
      rewrite Forall_forall in Hall. specialize (Hall r (nth_error_In _ _ Hir)).
      destruct Hall as [Hneq | [_ Hno]]; [apply Hneq; exact Ht |].
      apply Hno. unfold must_precede. unfold is_response_of in Hr. unfold is_invocation in Hinv.
      destruct (te_ev E (untag (ts_event r))) as [h' op' | h' op' ret']; [destruct Hr |].
      destruct (te_ev E (untag (ts_event candidate))) as [h op | h op ret]; [| destruct Hinv].
      subst h'. exact Hq.
    Qed.

  End TaggedModuleSemantics.

End RelaxedModuleSemantics.
