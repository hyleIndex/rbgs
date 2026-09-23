(** Assertions and delayed-event obligations for the relaxed future logic. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedRGISimulation.

Import ListNotations.


Module RelaxedAssertions.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedPossibility.
  Import RelaxedModuleSemantics.
  Import RelaxedRGISimulation.

  Section Assertions.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedLang.RelaxedModuleImpl E F).

    Definition RAssertion : Type :=
      @Assertion E F VE VF.

    Context (I : RAssertion).
    Context (G : @ConcreteRelation E F VE).
    Context (AG : @AbstractRelation F VF).

    (** An ordinary implementation command always takes the indicated
        concrete module step.  Its abstract match is [TInvoke+TReturn]* and
        may therefore stutter when the command is not a linearization
        point. *)
    Definition UUpdate
        (candidate : ScheduledEvent E F)
        (P Q : RAssertion) : Prop :=
      forall c p,
        P (c, p) ->
        forall c',
          module_step_at VE M (se_owner candidate)
            (UnderlayEvent (se_event candidate)) c c' ->
          exists p',
            poss_steps VF p p' /\
            Q (c', p') /\
            invariant_lift VE VF I G AG (c, p) (c', p').

    (** A command explicitly designated as a linearization point must take
        one real abstract owner step.  Reflexivity is not available in this
        judgement. *)
    Definition LinUpdate
        (candidate : ScheduledEvent E F)
        (owner : CallKey F)
        (P Q : RAssertion) : Prop :=
      forall c p,
        P (c, p) ->
        forall c',
          module_step_at VE M (se_owner candidate)
            (UnderlayEvent (se_event candidate)) c c' ->
          exists p',
            poss_step_at VF owner p p' /\
            Q (c', p') /\
            invariant_lift VE VF I G AG (c, p) (c', p').

    Lemma lin_update_is_u_update candidate owner P Q :
      LinUpdate candidate owner P Q ->
      UUpdate candidate P Q.
    Proof.
      intros Hlin c p HP c' Hconcrete.
      destruct (Hlin c p HP c' Hconcrete)
        as [p' [Hstep [HQ Hguarantee]]].
      exists p'. split.
      - apply rt_step.
        now apply poss_step_at_is_step with (owner := owner).
      - split; assumption.
    Qed.

    Lemma lin_update_changes_possibility candidate owner P Q :
      LinUpdate candidate owner P Q ->
      forall c p,
        P (c, p) ->
        forall c',
          module_step_at VE M (se_owner candidate)
            (UnderlayEvent (se_event candidate)) c c' ->
          exists p',
            p <> p' /\
            Q (c', p') /\
            invariant_lift VE VF I G AG (c, p) (c', p').
    Proof.
      intros Hlin c p HP c' Hconcrete.
      destruct (Hlin c p HP c' Hconcrete)
        as [p' [Hstep [HQ Hguarantee]]].
      exists p'. split.
      - now apply poss_step_at_not_refl with (owner := owner).
      - split; assumption.
    Qed.

    (** Stability is checked against the paired ordinary/system rely from
        the simulation relation. *)
    Definition Stable
        (R : @ConcreteRely E F VE)
        (AR : @AbstractRely F VF)
        (alpha : tid)
        (P : RAssertion) : Prop :=
      forall source target,
        P source ->
        rely_lift VE VF I R AR alpha source target ->
        P target.

    (** Logical tokens expose the three abstract phases without conflating
        them with concrete program control. *)
    Inductive FutureToken (F0 : RelaxedSig.t) : Type :=
    | future_pending
        (owner : CallKey F0)
        (op : Sig.op (RelaxedSig.effect F0))
    | future_linearized
        (owner : CallKey F0)
        (op : Sig.op (RelaxedSig.effect F0))
    | future_done
        (owner : CallKey F0)
        (op : Sig.op (RelaxedSig.effect F0))
        (ret : Sig.ar op).

    Arguments FutureToken _ : clear implicits.
    Arguments future_pending {F0} _ _.
    Arguments future_linearized {F0} _ _.
    Arguments future_done {F0} _ _ _.

    Definition token_holds
        (token : FutureToken F)
        (p : Poss VF) : Prop :=
      match p, token with
      | PossOk _ pool, future_pending owner op =>
          lin_lookup owner (ls_inv op) pool
      | PossOk _ pool, future_linearized owner op =>
          lin_lookup owner (ls_lini op) pool
      | PossOk _ pool, future_done owner op ret =>
          lin_lookup owner (ls_linr op ret) pool
      | PossError, _ => False
      end.

    Definition AFuture (token : FutureToken F) : RAssertion :=
      fun state => token_holds token (snd state).

    (** A program may move past a command once it has installed one of
        these obligations.  The obligation, rather than the continuation's
        assertion, remembers the update that still has to be performed when
        the scheduler consumes the event. *)
    Record EventObligation : Type := {
      obligation_event : ScheduledEvent E F;
      obligation_pre : RAssertion;
      obligation_post : RAssertion;
      obligation_valid :
        UUpdate obligation_event obligation_pre obligation_post;
    }.

    Record LinearizationObligation : Type := {
      lin_obligation_event : ScheduledEvent E F;
      lin_obligation_owner : CallKey F;
      lin_obligation_pre : RAssertion;
      lin_obligation_post : RAssertion;
      lin_obligation_valid :
        LinUpdate lin_obligation_event lin_obligation_owner
          lin_obligation_pre lin_obligation_post;
    }.

    Definition ObligationQueue : Type := list EventObligation.

    Definition erase_obligations
        (obligations : ObligationQueue) : EventQueue E F :=
      map obligation_event obligations.

    (** The operational queue and the logical debt queue contain exactly
        the same occurrences and order. *)
    Definition queue_invariant
        (c : @ModuleConfig E F VE)
        (obligations : ObligationQueue) : Prop :=
      erase_obligations obligations = mc_queue c.

    (** Logical frontier selection mirrors operational frontier selection,
        but retains the proof attached to the selected event. *)
    Inductive select_obligation
        (candidate : EventObligation) :
        ObligationQueue -> ObligationQueue -> Prop :=
    | select_obligation_here suffix :
        select_obligation candidate
          (candidate :: suffix) suffix
    | select_obligation_next earlier queue queue'
        (Hcross : event_can_cross
          (se_event (obligation_event earlier))
          (se_event (obligation_event candidate)))
        (Hselect : select_obligation candidate queue queue') :
        select_obligation candidate
          (earlier :: queue) (earlier :: queue').

    Lemma select_obligation_erases candidate obligations obligations' :
      select_obligation candidate obligations obligations' ->
      select_frontier (obligation_event candidate)
        (erase_obligations obligations)
        (erase_obligations obligations').
    Proof.
      intro Hselect.
      induction Hselect; cbn.
      - apply select_here.
      - apply select_next; assumption.
    Qed.

    Lemma select_frontier_lifts_obligation_aux
        candidate queue queue'
        (Hfrontier : select_frontier candidate queue queue') :
      forall obligations,
        erase_obligations obligations = queue ->
        exists obligation obligations',
          obligation_event obligation = candidate /\
          select_obligation obligation obligations obligations' /\
          erase_obligations obligations' = queue'.
    Proof.
      induction Hfrontier; intros obligations Herase.
      - destruct obligations as [| obligation obligations];
          cbn in Herase; [discriminate |].
        injection Herase as Hevent Htail.
        exists obligation, obligations. split; [exact Hevent |].
        split; [apply select_obligation_here | exact Htail].
      - destruct obligations as [| obligation obligations];
          cbn in Herase; [discriminate |].
        injection Herase as Hevent Htail.
        destruct (IHHfrontier obligations Htail)
          as [selected [obligations'
            [Hselected [Hlogical Herase']]]].
        exists selected, (obligation :: obligations').
        split; [exact Hselected |]. split.
        + apply select_obligation_next.
          * rewrite Hevent, Hselected. exact Hcross.
          * exact Hlogical.
        + change
            (obligation_event obligation ::
              erase_obligations obligations' = earlier :: queue').
          rewrite Hevent, Herase'. reflexivity.
    Qed.

    Lemma select_frontier_lifts_obligation
        candidate obligations queue' :
      select_frontier candidate
        (erase_obligations obligations) queue' ->
      exists obligation obligations',
        obligation_event obligation = candidate /\
        select_obligation obligation obligations obligations' /\
        erase_obligations obligations' = queue'.
    Proof.
      intro Hfrontier.
      eapply select_frontier_lifts_obligation_aux;
        [exact Hfrontier | reflexivity].
    Qed.

    Lemma selected_obligation_matches_queue
        candidate obligations obligations' c :
      queue_invariant c obligations ->
      select_obligation candidate obligations obligations' ->
      select_frontier (obligation_event candidate)
        (mc_queue c) (erase_obligations obligations').
    Proof.
      intros Hqueue Hselect.
      rewrite <- Hqueue.
      now apply select_obligation_erases.
    Qed.

    Lemma operational_selection_has_obligation
        candidate c queue' obligations :
      queue_invariant c obligations ->
      select_frontier candidate (mc_queue c) queue' ->
      exists obligation obligations',
        obligation_event obligation = candidate /\
        select_obligation obligation obligations obligations' /\
        erase_obligations obligations' = queue'.
    Proof.
      intros Hqueue Hfrontier.
      rewrite <- Hqueue in Hfrontier.
      now apply select_frontier_lifts_obligation.
    Qed.

    Lemma consume_obligation candidate c p c' :
      obligation_pre candidate (c, p) ->
      module_step_at VE M (se_owner (obligation_event candidate))
        (UnderlayEvent (se_event (obligation_event candidate))) c c' ->
      exists p',
        poss_steps VF p p' /\
        obligation_post candidate (c', p') /\
        invariant_lift VE VF I G AG (c, p) (c', p').
    Proof.
      intros HP Hstep.
      exact (obligation_valid candidate c p HP c' Hstep).
    Qed.

    Lemma consume_linearization_obligation candidate c p c' :
      lin_obligation_pre candidate (c, p) ->
      module_step_at VE M
        (se_owner (lin_obligation_event candidate))
        (UnderlayEvent (se_event (lin_obligation_event candidate))) c c' ->
      exists p',
        p <> p' /\
        lin_obligation_post candidate (c', p') /\
        invariant_lift VE VF I G AG (c, p) (c', p').
    Proof.
      intros HP Hstep.
      eapply lin_update_changes_possibility.
      - exact (lin_obligation_valid candidate).
      - exact HP.
      - exact Hstep.
    Qed.

  End Assertions.

End RelaxedAssertions.
