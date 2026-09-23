(** Program logic for relaxed programs with explicit future and wait. *)

Require Import Coq.Lists.List.
Require Import Lia.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedRGISimulation.
Require Import models.simlin.RelaxedAssertion.
Require Import models.simlin.RelaxedProofState.

Import ListNotations.


Module RelaxedLogic.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedPossibility.
  Import RelaxedModuleSemantics.
  Import RelaxedRGISimulation.
  Import RelaxedAssertions.
  Import RelaxedProofState.

  Section Logic.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (VF : RelaxedLTSSpec.LTS F).
    Context (M : RelaxedLang.RelaxedModuleImpl E F).

    Definition LogicAssertion : Type := @Assertion E F VE VF.

    Context (I : LogicAssertion).
    Context (G : @ConcreteRelation E F VE).
    Context (AG : @AbstractRelation F VF).

    Definition LogicObligation : Type :=
      EventObligation VE VF M I G AG.

    Definition LogicObligations : Type := list LogicObligation.

    Definition logic_obligation_event
        (obligation : LogicObligation) : ScheduledEvent E F :=
      obligation_event VE VF M I G AG obligation.

    Definition logic_obligation_pre
        (obligation : LogicObligation) : LogicAssertion :=
      obligation_pre VE VF M I G AG obligation.

    Definition logic_obligation_post
        (obligation : LogicObligation) : LogicAssertion :=
      obligation_post VE VF M I G AG obligation.

    Fixpoint obligation_trace
        (obligations : LogicObligations) : list (ThreadEvent E) :=
      match obligations with
      | [] => []
      | obligation :: obligations' =>
          se_event (logic_obligation_event obligation) ::
          obligation_trace obligations'
      end.

    (** [CertifiedExecution] is the executable core of the program logic.
        Silent commands advance immediately.  Every emitted command may
        also advance immediately, but only after installing an obligation
        for exactly the event emitted by the operational semantics. *)
    Inductive CertifiedExecution
        (owner : CallKey F) (thread : tid) (A : Type) :
        ProgramConfig E A -> LogicObligations ->
        ProgramConfig E A -> Prop :=
    | certified_refl config :
        CertifiedExecution owner thread A config [] config
    | certified_silent config1 config2 config3 obligations
        (Hstep : program_step thread Silent config1 config2)
        (Hexecution :
          CertifiedExecution owner thread A
            config2 obligations config3) :
        CertifiedExecution owner thread A
          config1 obligations config3
    | certified_emit config1 config2 config3 event
        obligation obligations
        (Hstep : program_step thread (Emit event) config1 config2)
        (Hevent : logic_obligation_event obligation =
          Build_ScheduledEvent owner event)
        (Hexecution :
          CertifiedExecution owner thread A
            config2 obligations config3) :
        CertifiedExecution owner thread A
          config1 (obligation :: obligations) config3.

    Lemma certified_execution_is_program_execution
        owner thread A config obligations config' :
      CertifiedExecution owner thread A
        config obligations config' ->
      program_execution thread config
        (obligation_trace obligations) config'.
    Proof.
      intro Hcertified.
      induction Hcertified.
      - apply program_execution_refl.
      - eapply program_execution_silent; eauto.
      - cbn [obligation_trace].
        rewrite Hevent. cbn.
        eapply program_execution_emit; eauto.
    Qed.

    Lemma certified_execution_erases_to_schedule
        owner thread A config obligations config' :
      CertifiedExecution owner thread A
        config obligations config' ->
      erase_obligations VE VF M I G AG obligations =
      schedule_trace owner (obligation_trace obligations).
    Proof.
      intro Hcertified.
      induction Hcertified.
      - reflexivity.
      - exact IHHcertified.
      - cbn [erase_obligations schedule_trace obligation_trace].
        fold (logic_obligation_event obligation).
        rewrite Hevent. cbn. f_equal.
        + exact Hevent.
        + exact IHHcertified.
    Qed.

    (** A proof rule provider supplies an update proof for every event that
        a program step can emit.  This is the interface between primitive
        Hoare rules and certified execution. *)
    Definition ObligationRule
        (owner : CallKey F) (thread : tid) : Prop :=
      forall (A : Type)
        (config config' : ProgramConfig E A) event,
        program_step thread (Emit event) config config' ->
        exists obligation : LogicObligation,
          logic_obligation_event obligation =
          Build_ScheduledEvent owner event.

    (** It is enough to provide obligations for invocation and response
        events.  Both [Wait] on a pending handle and asynchronous [Resolve]
        emit the same response form and therefore share the second rule. *)
    Record PrimitiveObligations
        (owner : CallKey F) (thread : tid) : Prop := {
      future_obligation :
        forall (op : Sig.op (RelaxedSig.effect E))
          (handle : RelaxedSig.handle E),
          exists obligation : LogicObligation,
            logic_obligation_event obligation =
            Build_ScheduledEvent owner
              (Build_ThreadEvent thread (InvEv handle op));
      response_obligation :
        forall (op : Sig.op (RelaxedSig.effect E))
          (handle : RelaxedSig.handle E)
          (ret : Sig.ar op),
          exists obligation : LogicObligation,
            logic_obligation_event obligation =
            Build_ScheduledEvent owner
              (Build_ThreadEvent thread (ResEv handle op ret));
    }.

    Lemma primitive_obligations_complete owner thread :
      PrimitiveObligations owner thread ->
      ObligationRule owner thread.
    Proof.
      intros Hprimitive A config config' event Hstep.
      inversion Hstep; subst.
      - now apply (future_obligation owner thread Hprimitive).
      - now apply (response_obligation owner thread Hprimitive).
      - now apply (response_obligation owner thread Hprimitive).
    Qed.

    Lemma program_execution_can_be_certified
        owner thread
        (Hrule : ObligationRule owner thread)
        A config trace config' :
      program_execution thread config trace config' ->
      exists obligations,
        CertifiedExecution owner thread A
          config obligations config' /\
        obligation_trace obligations = trace.
    Proof.
      intro Hexecution.
      induction Hexecution.
      - exists []. split.
        + apply certified_refl.
        + reflexivity.
      - destruct IHHexecution as [obligations [Hcertified Htrace]].
        exists obligations. split.
        + eapply certified_silent; eauto.
        + exact Htrace.
      - destruct (Hrule A c1 c2 ev Hstep) as [obligation Hevent].
        destruct IHHexecution as [obligations [Hcertified Htrace]].
        exists (obligation :: obligations). split.
        + eapply certified_emit; eauto.
        + cbn [obligation_trace]. rewrite Hevent. cbn.
          now rewrite Htrace.
    Qed.

    (** Primitive command rules.  They expose exactly which commands add
        debt and which commands are silent. *)
    Lemma certify_future
        owner thread A
        (op : Sig.op (RelaxedSig.effect E)) k handle store
        (obligation : LogicObligation) :
      handle_fresh handle store ->
      logic_obligation_event obligation =
        Build_ScheduledEvent owner
          (Build_ThreadEvent thread (InvEv handle op)) ->
      CertifiedExecution owner thread A
        (Build_ProgramConfig (Future op k) store)
        [obligation]
        (Build_ProgramConfig
          (k (MkFutureRef op handle))
          (add_pending handle op store)).
    Proof.
      intros Hfresh Hevent.
      eapply certified_emit.
      - eapply program_future. exact Hfresh.
      - exact Hevent.
      - apply certified_refl.
    Qed.

    Lemma certify_wait_resolved
        owner thread A
        (op : Sig.op (RelaxedSig.effect E)) handle ret k store :
      resolved_at handle op ret store ->
      CertifiedExecution owner thread A
        (Build_ProgramConfig
          (Wait (MkFutureRef op handle) k) store)
        []
        (Build_ProgramConfig (k ret) store).
    Proof.
      intro Hresolved.
      eapply certified_silent.
      - eapply program_wait_resolved. exact Hresolved.
      - apply certified_refl.
    Qed.

    Lemma certify_wait_pending
        owner thread A
        (op : Sig.op (RelaxedSig.effect E)) handle ret k store store'
        (obligation : LogicObligation) :
      resolve_store handle op ret store store' ->
      logic_obligation_event obligation =
        Build_ScheduledEvent owner
          (Build_ThreadEvent thread (ResEv handle op ret)) ->
      CertifiedExecution owner thread A
        (Build_ProgramConfig
          (Wait (MkFutureRef op handle) k) store)
        [obligation]
        (Build_ProgramConfig (k ret) store').
    Proof.
      intros Hresolve Hevent.
      eapply certified_emit.
      - eapply program_wait_pending. exact Hresolve.
      - exact Hevent.
      - apply certified_refl.
    Qed.

    Lemma certify_resolve
        owner thread A
        (op : Sig.op (RelaxedSig.effect E)) handle ret program store store'
        (obligation : LogicObligation) :
      resolve_store handle op ret store store' ->
      logic_obligation_event obligation =
        Build_ScheduledEvent owner
          (Build_ThreadEvent thread (ResEv handle op ret)) ->
      CertifiedExecution owner thread A
        (Build_ProgramConfig program store)
        [obligation]
        (Build_ProgramConfig program store').
    Proof.
      intros Hresolve Hevent.
      eapply certified_emit.
      - eapply program_resolve. exact Hresolve.
      - exact Hevent.
      - apply certified_refl.
    Qed.

    Lemma certify_tau owner thread A program store :
      CertifiedExecution owner thread A
        (Build_ProgramConfig (Tau program) store)
        []
        (Build_ProgramConfig program store).
    Proof.
      eapply certified_silent.
      - apply program_tau.
      - apply certified_refl.
    Qed.

    (** [P] is a readiness condition, evaluated when the scheduler selects
        the obligation rather than when the program first emits it. *)
    Definition ObligationReady
        (P : LogicAssertion) (obligation : LogicObligation) : Prop :=
      forall state, P state -> logic_obligation_pre obligation state.

    (** Executing [obligation] preserves [Frame].  This is the logical
        counterpart of declaring two underlay events reorderable: an event
        may commute operationally only when its proof also preserves the
        resources needed by the event it crosses. *)
    Definition ObligationPreserves
        (obligation : LogicObligation)
        (Frame : LogicAssertion) : Prop :=
      forall concrete abstract,
        logic_obligation_pre obligation (concrete, abstract) ->
        Frame (concrete, abstract) ->
        forall concrete',
          module_step_at VE M
            (se_owner (logic_obligation_event obligation))
            (UnderlayEvent
              (se_event (logic_obligation_event obligation)))
            concrete concrete' ->
          exists abstract',
            poss_steps VF abstract abstract' /\
            logic_obligation_post obligation
              (concrete', abstract') /\
            Frame (concrete', abstract') /\
            invariant_lift VE VF I G AG
              (concrete, abstract) (concrete', abstract').

    (** This deliberately requires both possible orders to preserve the
        other obligation's readiness and completed footprint.  It is a
        strong, compositional rule; weaker asymmetric rules can be derived
        later for dependencies that are not allowed to commute. *)
    Definition ObligationCompatible
        (earlier later : LogicObligation) : Prop :=
      event_can_cross
        (se_event (logic_obligation_event earlier))
        (se_event (logic_obligation_event later)) ->
      ObligationPreserves earlier
        (logic_obligation_pre later) /\
      ObligationPreserves later
        (logic_obligation_pre earlier) /\
      ObligationPreserves earlier
        (logic_obligation_post later) /\
      ObligationPreserves later
        (logic_obligation_post earlier).

    (** Scheduler soundness for outstanding debt.  The continuation is
        allowed to run while [obligations] is nonempty, but every eligible
        scheduler choice must satisfy its stored precondition and preserve
        safety after the corresponding concrete underlay transition. *)
    Inductive DebtSafe (Q : LogicAssertion) :
        @JointState E F VE VF -> LogicObligations -> Prop :=
    | debt_safe_done state
        (Hpost : Q state) :
        DebtSafe Q state []
    | debt_safe_pending state obligations
        (Hnonempty : obligations <> [])
        (Hconsume :
          forall selected rest,
            select_obligation VE VF M I G AG
              selected obligations rest ->
            logic_obligation_pre selected state /\
            forall concrete',
              module_step_at VE M
                (se_owner (logic_obligation_event selected))
                (UnderlayEvent
                  (se_event (logic_obligation_event selected)))
                (fst state) concrete' ->
              exists abstract',
                poss_steps VF (snd state) abstract' /\
                logic_obligation_post selected
                  (concrete', abstract') /\
                invariant_lift VE VF I G AG
                  state (concrete', abstract') /\
                DebtSafe Q (concrete', abstract') rest) :
        DebtSafe Q state obligations.

    Definition LinkedDebtSafe
        (Q : LogicAssertion)
        (state : @JointState E F VE VF)
        (obligations : LogicObligations) : Prop :=
      queue_invariant VE VF M I G AG
        (fst state) obligations /\
      DebtSafe Q state obligations.

    Lemma debt_safe_selected_pre
        Q state obligations selected rest :
      DebtSafe Q state obligations ->
      select_obligation VE VF M I G AG
        selected obligations rest ->
      logic_obligation_pre selected state.
    Proof.
      intros Hsafe Hselect.
      inversion Hsafe; subst.
      - inversion Hselect.
      - now destruct (Hconsume selected rest Hselect).
    Qed.

    Lemma debt_safe_consume
        Q state obligations selected rest concrete' :
      DebtSafe Q state obligations ->
      select_obligation VE VF M I G AG
        selected obligations rest ->
      module_step_at VE M
        (se_owner (logic_obligation_event selected))
        (UnderlayEvent
          (se_event (logic_obligation_event selected)))
        (fst state) concrete' ->
      exists abstract',
        poss_steps VF (snd state) abstract' /\
        logic_obligation_post selected (concrete', abstract') /\
        invariant_lift VE VF I G AG
          state (concrete', abstract') /\
        DebtSafe Q (concrete', abstract') rest.
    Proof.
      intros Hsafe Hselect Hstep.
      inversion Hsafe; subst.
      - inversion Hselect.
      - destruct (Hconsume selected rest Hselect) as [_ Hsafe_step].
        now apply Hsafe_step.
    Qed.

    (** An actual operational underlay step determines a matching logical
        occurrence through the queue invariant.  Consuming that occurrence
        preserves both scheduler safety and the operational/logical queue
        correspondence, even when equal event values occur more than once. *)
    Lemma linked_debt_safe_underlay_step
        (Q : LogicAssertion)
        concrete abstract obligations owner event concrete' :
      LinkedDebtSafe Q (concrete, abstract) obligations ->
      module_step_at VE M owner
        (UnderlayEvent event) concrete concrete' ->
      exists selected rest abstract',
        logic_obligation_event selected =
          Build_ScheduledEvent owner event /\
        poss_steps VF abstract abstract' /\
        logic_obligation_post selected (concrete', abstract') /\
        invariant_lift VE VF I G AG
          (concrete, abstract) (concrete', abstract') /\
        LinkedDebtSafe Q (concrete', abstract') rest.
    Proof.
      intros [Hqueue Hsafe] Hstep.
      inversion Hstep; subst.
      destruct (operational_selection_has_obligation
        VE VF M I G AG candidate
        (Build_ModuleConfig q pool queue used) queue'
        obligations Hqueue Hselect)
        as [selected [rest [Hevent [Hlogical Herase]]]].
      assert (Hselected_step :
        module_step_at VE M
          (se_owner (logic_obligation_event selected))
          (UnderlayEvent
            (se_event (logic_obligation_event selected)))
          (Build_ModuleConfig q pool queue used)
          (Build_ModuleConfig q' pool queue' used)).
      {
        unfold logic_obligation_event.
        rewrite Hevent.
        eapply module_at_underlay; eauto.
      }
      destruct (debt_safe_consume Q
        (Build_ModuleConfig q pool queue used, abstract)
        obligations selected rest
        (Build_ModuleConfig q' pool queue' used)
        Hsafe Hlogical Hselected_step)
        as [abstract' [Hposs [Hpost [Hinvariant Hsafe']]]].
      exists selected, rest, abstract'.
      split.
      - unfold logic_obligation_event.
        rewrite Hevent. destruct candidate. reflexivity.
      - split; [exact Hposs |].
        split; [exact Hpost |].
        split; [exact Hinvariant |].
        split.
        + exact Herase.
        + exact Hsafe'.
    Qed.

    Lemma debt_safe_empty_post Q state :
      DebtSafe Q state [] -> Q state.
    Proof.
      intro Hsafe. inversion Hsafe; subst.
      - exact Hpost.
      - exfalso. apply Hnonempty. reflexivity.
    Qed.

    Lemma linked_debt_safe_empty
        (Q : LogicAssertion) state :
      LinkedDebtSafe Q state [] ->
      Q state.
    Proof.
      intros [_ Hsafe]. now apply debt_safe_empty_post.
    Qed.

    Lemma linked_debt_safe_empty_owner_done
        (Q : LogicAssertion) concrete abstract owner :
      LinkedDebtSafe Q (concrete, abstract) [] ->
      owner_done owner (mc_queue concrete).
    Proof.
      intros [Hqueue _].
      unfold queue_invariant in Hqueue. cbn in Hqueue.
      unfold owner_done. rewrite <- Hqueue. cbn. tauto.
    Qed.

    Lemma select_obligation_length
        selected obligations rest :
      select_obligation VE VF M I G AG
        selected obligations rest ->
      length obligations = S (length rest).
    Proof.
      intro Hselect. induction Hselect; cbn; congruence.
    Qed.

    Lemma select_obligation_member
        selected obligations rest :
      select_obligation VE VF M I G AG
        selected obligations rest ->
      In selected obligations.
    Proof.
      intro Hselect. induction Hselect; cbn; auto.
    Qed.

    Lemma select_obligation_rest_included
        selected obligations rest :
      select_obligation VE VF M I G AG
        selected obligations rest ->
      forall obligation,
        In obligation rest -> In obligation obligations.
    Proof.
      intro Hselect. induction Hselect; intros obligation Hin; cbn in *.
      - now right.
      - destruct Hin as [Heq | Hin].
        + now left.
        + right. now apply IHHselect.
    Qed.

    Lemma select_obligation_preserves_forall
        (Property : LogicObligation -> Prop)
        selected obligations rest :
      select_obligation VE VF M I G AG
        selected obligations rest ->
      Forall Property obligations ->
      Forall Property rest.
    Proof.
      intros Hselect Hall.
      apply Forall_forall. intros obligation Hin.
      apply Forall_forall with (x := obligation) in Hall.
      - exact Hall.
      - eapply select_obligation_rest_included; eauto.
    Qed.

    (** [K obligations] is a queue-indexed invariant.  Unlike a fixed
        obligation precondition, it is allowed to change when the scheduler
        removes an arbitrary frontier event. *)
    Definition DebtProtocol
        (K : LogicObligations -> LogicAssertion) : Prop :=
      forall obligations selected rest,
        select_obligation VE VF M I G AG
          selected obligations rest ->
        forall concrete abstract,
          K obligations (concrete, abstract) ->
          logic_obligation_pre selected (concrete, abstract) /\
          forall concrete',
            module_step_at VE M
              (se_owner (logic_obligation_event selected))
              (UnderlayEvent
                (se_event (logic_obligation_event selected)))
              concrete concrete' ->
            exists abstract',
              poss_steps VF abstract abstract' /\
              logic_obligation_post selected
                (concrete', abstract') /\
              invariant_lift VE VF I G AG
                (concrete, abstract) (concrete', abstract') /\
              K rest (concrete', abstract').

    (** A protocol describes every local scheduler update.  Well-founded
        induction on queue length turns it into the complete nondeterministic
        execution tree required by [DebtSafe]. *)
    Lemma debt_protocol_sound
        (Q : LogicAssertion)
        (K : LogicObligations -> LogicAssertion) :
      DebtProtocol K ->
      (forall state, K [] state -> Q state) ->
      forall obligations state,
        K obligations state ->
        DebtSafe Q state obligations.
    Proof.
      intros Hprotocol Hfinal.
      assert (forall n obligations state,
        length obligations = n ->
        K obligations state ->
        DebtSafe Q state obligations) as Hinduction.
      {
        induction n as [| n IH]; intros obligations state Hlength HK.
        - destruct obligations as [| obligation obligations].
          + apply debt_safe_done. now apply Hfinal.
          + cbn in Hlength. discriminate.
        - destruct obligations as [| obligation obligations].
          + discriminate.
          + apply debt_safe_pending.
            * discriminate.
            * intros selected rest Hselect.
              destruct state as [concrete abstract].
              destruct (Hprotocol
                (obligation :: obligations) selected rest Hselect
                concrete abstract HK) as [Hpre Hstep_safe].
              split; [exact Hpre |].
              intros concrete' Hstep.
              destruct (Hstep_safe concrete' Hstep)
                as [abstract' [Hposs [Hpost [Hinvariant HKrest]]]].
              exists abstract'. split; [exact Hposs |].
              split; [exact Hpost |].
              split; [exact Hinvariant |].
              apply IH.
              -- pose proof
                   (select_obligation_length selected
                     (obligation :: obligations) rest Hselect)
                   as Hrest_length.
                 assert (Hobligations : length obligations = n).
                 { now inversion Hlength. }
                 assert (Hrest : length obligations = length rest).
                 { now inversion Hrest_length. }
                 exact (eq_trans (eq_sym Hrest) Hobligations).
              -- exact HKrest.
      }
      intros obligations state HK.
      eapply Hinduction; [reflexivity | exact HK].
    Qed.

    Lemma debt_safe_is_protocol (Q : LogicAssertion) :
      DebtProtocol
        (fun obligations state => DebtSafe Q state obligations).
    Proof.
      intros obligations selected rest Hselect concrete abstract Hsafe.
      split.
      - eapply debt_safe_selected_pre; eauto.
      - intros concrete' Hstep.
        exact (debt_safe_consume
          Q (concrete, abstract) obligations selected rest concrete'
          Hsafe Hselect Hstep).
    Qed.

    Lemma debt_safe_mono
        (Q Q' : LogicAssertion)
        (Hweaken : forall state, Q state -> Q' state)
        state obligations :
      DebtSafe Q state obligations ->
      DebtSafe Q' state obligations.
    Proof.
      intro Hsafe.
      eapply debt_protocol_sound
        with (K := fun obligations state =>
          DebtSafe Q state obligations).
      - apply debt_safe_is_protocol.
      - intros state' Hempty.
        apply Hweaken. now apply debt_safe_empty_post.
      - exact Hsafe.
    Qed.

    (** A framed singleton debt is safe when the obligation preserves the
        frame and its postcondition together with the frame entails [Q]. *)
    Lemma debt_safe_singleton_with_frame
        (Q Frame : LogicAssertion)
        state (obligation : LogicObligation) :
      logic_obligation_pre obligation state ->
      Frame state ->
      ObligationPreserves obligation Frame ->
      (forall state',
        logic_obligation_post obligation state' ->
        Frame state' -> Q state') ->
      DebtSafe Q state [obligation].
    Proof.
      destruct state as [concrete abstract].
      cbn. intros Hpre Hframe Hpreserves Hfinal.
      apply debt_safe_pending.
      - discriminate.
      - intros selected rest Hselect.
        inversion Hselect as [suffix | earlier queue queue' Hcross Htail];
          subst.
        + split; [exact Hpre |].
          intros concrete' Hstep.
          destruct (Hpreserves concrete abstract Hpre Hframe
            concrete' Hstep)
            as [abstract' [Hposs [Hpost [Hframe' Hinvariant]]]].
          exists abstract'. split; [exact Hposs |].
          split; [exact Hpost |].
          split; [exact Hinvariant |].
          apply debt_safe_done.
          now apply Hfinal.
        + inversion Htail.
    Qed.

    (** Two reorderable obligations are safe in either scheduler order
        when their update proofs preserve one another's pre/post footprint.
        This is the first compositional debt-extension rule. *)
    Lemma debt_safe_compatible_pair
        (Q : LogicAssertion)
        state (first second : LogicObligation) :
      logic_obligation_pre first state ->
      logic_obligation_pre second state ->
      event_can_cross
        (se_event (logic_obligation_event first))
        (se_event (logic_obligation_event second)) ->
      ObligationCompatible first second ->
      (forall state',
        logic_obligation_post first state' ->
        logic_obligation_post second state' ->
        Q state') ->
      DebtSafe Q state [first; second].
    Proof.
      destruct state as [concrete abstract].
      cbn. intros Hpre_first Hpre_second Hcross Hcompatible Hfinal.
      destruct (Hcompatible Hcross) as
        [Hfirst_pre_second
          [Hsecond_pre_first
            [Hfirst_post_second Hsecond_post_first]]].
      apply debt_safe_pending.
      - discriminate.
      - intros selected rest Hselect.
        inversion Hselect as [suffix | earlier queue queue' Hcan Htail];
          subst.
        + split; [exact Hpre_first |].
          intros concrete' Hstep.
          destruct (Hfirst_pre_second concrete abstract
            Hpre_first Hpre_second concrete' Hstep)
            as [abstract' [Hposs [Hpost_first
              [Hpre_second' Hinvariant]]]].
          exists abstract'. split; [exact Hposs |].
          split; [exact Hpost_first |].
          split; [exact Hinvariant |].
          eapply debt_safe_singleton_with_frame
            with (Frame := logic_obligation_post first).
          * exact Hpre_second'.
          * exact Hpost_first.
          * exact Hsecond_post_first.
          * intros state' Hpost_second Hpost_first'.
            now apply Hfinal.
        + inversion Htail as
            [suffix2 | earlier2 queue2 queue3 Hcan2 Htail2];
            subst.
          * split; [exact Hpre_second |].
            intros concrete' Hstep.
            destruct (Hsecond_pre_first concrete abstract
              Hpre_second Hpre_first concrete' Hstep)
              as [abstract' [Hposs [Hpost_second
                [Hpre_first' Hinvariant]]]].
            exists abstract'. split; [exact Hposs |].
            split; [exact Hpost_second |].
            split; [exact Hinvariant |].
            eapply debt_safe_singleton_with_frame
              with (Frame := logic_obligation_post second).
            -- exact Hpre_first'.
            -- exact Hpost_second.
            -- exact Hfirst_post_second.
            -- intros state' Hpost_first Hpost_second'.
               now apply Hfinal.
          * inversion Htail2.
    Qed.

    (** When the later event cannot cross the earlier one, its readiness
        may be established by the earlier postcondition.  Only the original
        scheduler order needs to be certified. *)
    Lemma debt_safe_ordered_pair
        (Q : LogicAssertion)
        state (first second : LogicObligation) :
      logic_obligation_pre first state ->
      ~ event_can_cross
        (se_event (logic_obligation_event first))
        (se_event (logic_obligation_event second)) ->
      (forall state',
        logic_obligation_post first state' ->
        logic_obligation_pre second state') ->
      ObligationPreserves second
        (logic_obligation_post first) ->
      (forall state',
        logic_obligation_post first state' ->
        logic_obligation_post second state' ->
        Q state') ->
      DebtSafe Q state [first; second].
    Proof.
      destruct state as [concrete abstract].
      cbn. intros Hpre_first Hordered Hready_second
        Hsecond_post_first Hfinal.
      apply debt_safe_pending.
      - discriminate.
      - intros selected rest Hselect.
        inversion Hselect as [suffix | earlier queue queue' Hcross Htail];
          subst.
        + split; [exact Hpre_first |].
          intros concrete' Hstep.
          destruct (consume_obligation VE VF M I G AG first
            concrete abstract concrete' Hpre_first Hstep)
            as [abstract' [Hposs [Hpost_first Hinvariant]]].
          exists abstract'. split; [exact Hposs |].
          split; [exact Hpost_first |].
          split; [exact Hinvariant |].
          eapply debt_safe_singleton_with_frame
            with (Frame := logic_obligation_post first).
          * now apply Hready_second.
          * exact Hpost_first.
          * exact Hsecond_post_first.
          * intros state' Hpost_second Hpost_first'.
            now apply Hfinal.
        + inversion Htail as
            [suffix2 | earlier2 queue2 queue3 Hcross2 Htail2]; subst.
          * exfalso. apply Hordered. exact Hcross.
          * inversion Htail2.
    Qed.

    (** A debt certificate is the scheduler-facing part of a Hoare proof.
        The queue equality prevents the safety premise from being used for
        a logical debt list unrelated to the operational module queue. *)
    Definition DebtCertificate
        (P Q : LogicAssertion)
        (obligations : LogicObligations) : Prop :=
      forall state,
        P state ->
        queue_invariant VE VF M I G AG
          (fst state) obligations ->
        DebtSafe Q state obligations.

    Lemma debt_protocol_certificate
        (P Q : LogicAssertion)
        (K : LogicObligations -> LogicAssertion)
        obligations :
      DebtProtocol K ->
      (forall state, P state -> K obligations state) ->
      (forall state, K [] state -> Q state) ->
      DebtCertificate P Q obligations.
    Proof.
      intros Hprotocol Hinitial Hfinal state HP _.
      eapply debt_protocol_sound; eauto.
    Qed.

    Lemma debt_certificate_mono
        (P P' Q Q' : LogicAssertion)
        obligations :
      (forall state, P state -> P' state) ->
      (forall state, Q' state -> Q state) ->
      DebtCertificate P' Q' obligations ->
      DebtCertificate P Q obligations.
    Proof.
      intros Hpre Hpost Hcertificate state HP Hqueue.
      eapply debt_safe_mono.
      - exact Hpost.
      - apply Hcertificate; [now apply Hpre | exact Hqueue].
    Qed.

    (** An indexed derivation exposes its generated debt, return value and
        final local configuration.  Keeping these as indices makes the
        primitive rules compositional without eliminating witnesses out of
        a proposition. *)
    Definition HTripleDerivation
        (owner : CallKey F) (thread : tid) (A : Type)
        (P : LogicAssertion)
        (program : Prog E A)
        (store : FutureStore E)
        (Q : A -> LogicAssertion)
        (obligations : LogicObligations)
        (result : A)
        (final : ProgramConfig E A) : Prop :=
      CertifiedExecution owner thread A
        (Build_ProgramConfig program store)
        obligations final /\
      program_terminal final result /\
      DebtCertificate P (Q result) obligations.

    Definition HTripleProvable
        (owner : CallKey F) (thread : tid) (A : Type)
        (P : LogicAssertion)
        (program : Prog E A)
        (store : FutureStore E)
        (Q : A -> LogicAssertion) : Prop :=
      exists obligations result final,
        HTripleDerivation owner thread A
          P program store Q obligations result final.

    Lemma provable_ret
        owner thread A
        (P : LogicAssertion) (Q : A -> LogicAssertion)
        (result : A) (store : FutureStore E) :
      all_resolved store ->
      (forall state, P state -> Q result state) ->
      HTripleDerivation owner thread A
        P (Ret result) store Q [] result
        (Build_ProgramConfig (Ret result) store).
    Proof.
      intros Hresolved Hpost. split.
      - apply certified_refl.
      - split.
        + now apply program_terminal_ret.
        + intros state HP _.
          apply debt_safe_done. now apply Hpost.
    Qed.

    Lemma provable_tau
        owner thread A
        (P : LogicAssertion) (Q : A -> LogicAssertion)
        (program : Prog E A) (store : FutureStore E)
        (obligations : LogicObligations) (result : A)
        (final : ProgramConfig E A) :
      HTripleDerivation owner thread A
        P program store Q obligations result final ->
      HTripleDerivation owner thread A
        P (Tau program) store Q obligations result final.
    Proof.
      intros [Hexecution [Hterminal Hdebt]].
      split.
      - eapply certified_silent.
        + apply program_tau.
        + exact Hexecution.
      - now split.
    Qed.

    Lemma provable_future
        owner thread A
        (P : LogicAssertion) (Q : A -> LogicAssertion)
        (op : Sig.op (RelaxedSig.effect E)) continuation
        handle (store : FutureStore E)
        (obligation : LogicObligation)
        (obligations : LogicObligations) (result : A)
        (final : ProgramConfig E A) :
      handle_fresh handle store ->
      logic_obligation_event obligation =
        Build_ScheduledEvent owner
          (Build_ThreadEvent thread (InvEv handle op)) ->
      HTripleDerivation owner thread A
        P (continuation (MkFutureRef op handle))
        (add_pending handle op store) Q
        obligations result final ->
      DebtCertificate P (Q result) (obligation :: obligations) ->
      HTripleDerivation owner thread A
        P (Future op continuation) store Q
        (obligation :: obligations) result final.
    Proof.
      intros Hfresh Hevent
        [Hexecution [Hterminal _]] Hdebt.
      split.
      - eapply certified_emit.
        + eapply program_future. exact Hfresh.
        + exact Hevent.
        + exact Hexecution.
      - now split.
    Qed.

    Lemma provable_wait_resolved
        owner thread A
        (P : LogicAssertion) (Q : A -> LogicAssertion)
        (op : Sig.op (RelaxedSig.effect E)) handle ret continuation
        (store : FutureStore E)
        (obligations : LogicObligations) (result : A)
        (final : ProgramConfig E A) :
      resolved_at handle op ret store ->
      HTripleDerivation owner thread A
        P (continuation ret) store Q
        obligations result final ->
      HTripleDerivation owner thread A
        P (Wait (MkFutureRef op handle) continuation) store Q
        obligations result final.
    Proof.
      intros Hresolved [Hexecution [Hterminal Hdebt]].
      split.
      - eapply certified_silent.
        + eapply program_wait_resolved. exact Hresolved.
        + exact Hexecution.
      - now split.
    Qed.

    Lemma provable_wait_pending
        owner thread A
        (P : LogicAssertion) (Q : A -> LogicAssertion)
        (op : Sig.op (RelaxedSig.effect E)) handle ret continuation
        (store store' : FutureStore E)
        (obligation : LogicObligation)
        (obligations : LogicObligations) (result : A)
        (final : ProgramConfig E A) :
      resolve_store handle op ret store store' ->
      logic_obligation_event obligation =
        Build_ScheduledEvent owner
          (Build_ThreadEvent thread (ResEv handle op ret)) ->
      HTripleDerivation owner thread A
        P (continuation ret) store' Q
        obligations result final ->
      DebtCertificate P (Q result) (obligation :: obligations) ->
      HTripleDerivation owner thread A
        P (Wait (MkFutureRef op handle) continuation) store Q
        (obligation :: obligations) result final.
    Proof.
      intros Hresolve Hevent
        [Hexecution [Hterminal _]] Hdebt.
      split.
      - eapply certified_emit.
        + eapply program_wait_pending. exact Hresolve.
        + exact Hevent.
        + exact Hexecution.
      - now split.
    Qed.

    Lemma provable_resolve
        owner thread A
        (P : LogicAssertion) (Q : A -> LogicAssertion)
        (op : Sig.op (RelaxedSig.effect E)) handle ret program
        (store store' : FutureStore E)
        (obligation : LogicObligation)
        (obligations : LogicObligations) (result : A)
        (final : ProgramConfig E A) :
      resolve_store handle op ret store store' ->
      logic_obligation_event obligation =
        Build_ScheduledEvent owner
          (Build_ThreadEvent thread (ResEv handle op ret)) ->
      HTripleDerivation owner thread A
        P program store' Q
        obligations result final ->
      DebtCertificate P (Q result) (obligation :: obligations) ->
      HTripleDerivation owner thread A
        P program store Q
        (obligation :: obligations) result final.
    Proof.
      intros Hresolve Hevent
        [Hexecution [Hterminal _]] Hdebt.
      split.
      - eapply certified_emit.
        + eapply program_resolve. exact Hresolve.
        + exact Hevent.
        + exact Hexecution.
      - now split.
    Qed.

    Lemma provable_consequence_pre
        owner thread A
        (P P' : LogicAssertion) (Q : A -> LogicAssertion)
        (program : Prog E A) (store : FutureStore E)
        obligations result final :
      (forall state, P state -> P' state) ->
      HTripleDerivation owner thread A
        P' program store Q obligations result final ->
      HTripleDerivation owner thread A
        P program store Q obligations result final.
    Proof.
      intros Hpre [Hexecution [Hterminal Hdebt]].
      split; [exact Hexecution |]. split; [exact Hterminal |].
      intros state HP Hqueue.
      apply Hdebt; [now apply Hpre | exact Hqueue].
    Qed.

    Lemma provable_consequence_post
        owner thread A
        (P : LogicAssertion) (Q Q' : A -> LogicAssertion)
        (program : Prog E A) (store : FutureStore E)
        obligations result final :
      (forall result state, Q result state -> Q' result state) ->
      HTripleDerivation owner thread A
        P program store Q obligations result final ->
      HTripleDerivation owner thread A
        P program store Q' obligations result final.
    Proof.
      intros Hpost [Hexecution [Hterminal Hdebt]].
      split; [exact Hexecution |]. split; [exact Hterminal |].
      intros state HP Hqueue.
      eapply debt_safe_mono.
      - apply Hpost.
      - now apply Hdebt.
    Qed.

    Lemma provable_consequence
        owner thread A
        (P P' : LogicAssertion) (Q Q' : A -> LogicAssertion)
        (program : Prog E A) (store : FutureStore E) :
      (forall state, P state -> P' state) ->
      (forall result state, Q result state -> Q' result state) ->
      HTripleProvable owner thread A P' program store Q ->
      HTripleProvable owner thread A P program store Q'.
    Proof.
      intros Hpre Hpost
        [obligations [result [final Hderivation]]].
      exists obligations, result, final.
      eapply provable_consequence_post; [exact Hpost |].
      eapply provable_consequence_pre.
      - exact Hpre.
      - exact Hderivation.
    Qed.

    (** Local soundness: every derivation has an ordinary program trace,
        the exact scheduled queue obtained by erasing proof payloads, a
        terminal future store, and scheduler safety for the whole debt. *)
    Lemma htriple_derivation_sound
        owner thread A
        (P : LogicAssertion) (program : Prog E A)
        (store : FutureStore E) (Q : A -> LogicAssertion)
        (obligations : LogicObligations) (result : A)
        (final : ProgramConfig E A) :
      HTripleDerivation owner thread A
        P program store Q obligations result final ->
      program_execution thread
        (Build_ProgramConfig program store)
        (obligation_trace obligations) final /\
      program_terminal final result /\
      erase_obligations VE VF M I G AG obligations =
        schedule_trace owner (obligation_trace obligations) /\
      DebtCertificate P (Q result) obligations.
    Proof.
      intros [Hexecution [Hterminal Hdebt]].
      split.
      - now apply certified_execution_is_program_execution
          with (owner := owner).
      - split; [exact Hterminal |].
        split.
        + now apply certified_execution_erases_to_schedule
            with (thread := thread) (A := A)
              (config := Build_ProgramConfig program store)
              (config' := final).
        + exact Hdebt.
    Qed.

    Lemma htriple_provable_sound
        owner thread A
        (P : LogicAssertion) (program : Prog E A)
        (store : FutureStore E) (Q : A -> LogicAssertion) :
      HTripleProvable owner thread A P program store Q ->
      exists obligations result final,
        program_execution thread
          (Build_ProgramConfig program store)
          (obligation_trace obligations) final /\
        program_terminal final result /\
        erase_obligations VE VF M I G AG obligations =
          schedule_trace owner (obligation_trace obligations) /\
        DebtCertificate P (Q result) obligations.
    Proof.
      intros [obligations [result [final Hderivation]]].
      exists obligations, result, final.
      now apply htriple_derivation_sound.
    Qed.

    Lemma htriple_initial_program_produces
        owner thread A
        (P : LogicAssertion) (program : Prog E A)
        (Q : A -> LogicAssertion)
        obligations result final :
      HTripleDerivation owner thread A
        P program (@empty_store E) Q
        obligations result final ->
      program_produces thread program
        (obligation_trace obligations) result.
    Proof.
      intro Hderivation.
      destruct (htriple_derivation_sound
        owner thread A P program (@empty_store E) Q
        obligations result final Hderivation)
        as [Hexecution [Hterminal _]].
      exists final. split; assumption.
    Qed.

    (** The module invocation appends exactly the trace certified by the
        Hoare derivation.  Appending the proof-carrying obligations therefore
        re-establishes the queue invariant on the invoked module state. *)
    Lemma htriple_invocation_splices_debt
        thread
        (handle : RelaxedSig.handle F)
        (op : Sig.op (RelaxedSig.effect F))
        (P : LogicAssertion)
        (Q : Sig.ar op -> LogicAssertion)
        obligations result final
        q pool queue used existing :
      HTripleDerivation (thread, handle) thread (Sig.ar op)
        P (M op thread) (@empty_store E) Q
        obligations result final ->
      call_fresh (thread, handle) pool ->
      trace_fresh used (obligation_trace obligations) ->
      queue_invariant VE VF M I G AG
        (Build_ModuleConfig q pool queue used) existing ->
      module_step_at VE M (thread, handle)
        (OverlayEvent
          (Build_ThreadEvent thread (@InvEv F handle op)))
        (Build_ModuleConfig q pool queue used)
        (Build_ModuleConfig q
          (Build_CallEntry thread handle (ActiveCall op result) :: pool)
          (queue ++ schedule_trace (thread, handle)
            (obligation_trace obligations))
          (used ++ invocation_keys (obligation_trace obligations))) /\
      queue_invariant VE VF M I G AG
        (Build_ModuleConfig q
          (Build_CallEntry thread handle (ActiveCall op result) :: pool)
          (queue ++ schedule_trace (thread, handle)
            (obligation_trace obligations))
          (used ++ invocation_keys (obligation_trace obligations)))
        (existing ++ obligations).
    Proof.
      intros Hderivation Hfresh_call Hfresh_trace Hqueue.
      destruct (htriple_derivation_sound
        (thread, handle) thread (Sig.ar op)
        P (M op thread) (@empty_store E) Q
        obligations result final Hderivation)
        as [Hexecution [Hterminal [Herase _]]].
      split.
      - eapply module_at_invoke.
        + exact Hfresh_call.
        + exists final. split; assumption.
        + exact Hfresh_trace.
      - unfold queue_invariant, erase_obligations in *.
        rewrite map_app, Hqueue, Herase. reflexivity.
    Qed.

    (** A method proof is uniform in the overlay handle allocated by its
        caller.  It produces a complete local trace and a scheduler-safe
        debt certificate for every such owner. *)
    Definition MethodProvable
        (thread : tid)
        (op : Sig.op (RelaxedSig.effect F))
        (P : LogicAssertion)
        (Q : Sig.ar op -> LogicAssertion) : Prop :=
      forall handle : RelaxedSig.handle F,
        HTripleProvable (thread, handle) thread (Sig.ar op)
          P (M op thread) (@empty_store E) Q.

    Lemma method_provable_trace_sound
        thread
        (op : Sig.op (RelaxedSig.effect F))
        (P : LogicAssertion)
        (Q : Sig.ar op -> LogicAssertion) :
      MethodProvable thread op P Q ->
      forall handle : RelaxedSig.handle F,
        exists obligations result,
          program_produces thread (M op thread)
            (obligation_trace obligations) result /\
          erase_obligations VE VF M I G AG obligations =
            schedule_trace (thread, handle)
              (obligation_trace obligations) /\
          DebtCertificate P (Q result) obligations.
    Proof.
      intros Hmethod handle.
      destruct (htriple_provable_sound
        (thread, handle) thread (Sig.ar op)
        P (M op thread) (@empty_store E) Q
        (Hmethod handle))
        as [obligations [result [final
          [Hexecution [Hterminal [Herase Hdebt]]]]]].
      exists obligations, result. split.
      - exists final. split; assumption.
      - now split.
    Qed.

  End Logic.

End RelaxedLogic.
