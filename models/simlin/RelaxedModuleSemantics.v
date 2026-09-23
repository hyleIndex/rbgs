(** Module-level scheduling for relaxed implementations. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Operators.

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

End RelaxedModuleSemantics.
