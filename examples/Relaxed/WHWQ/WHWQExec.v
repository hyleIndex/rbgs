(** * WHWQExec: concrete executions of the WHW queue module (T7)

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P5, target T7; review
    gate 3 (.rocq-review/latest-review.md).  Module executions of
    [WHWQProg.Mwhw] over [EI δRC] from the zero memory, built event by
    event in the tagged module semantics ([RelaxedHoareCompLin.MTraces]).
    Nothing here uses the RLHL proof (phases P6–P7) or T6; the
    trace-level facts are proved directly.

    Every execution below has an atomic underlay word ([ul_atomic]: each
    underlay invocation is immediately followed by its own response;
    [MTracesAtomic], with [mtraces_atomic] to [MTraces]).  Over [EI δRC]
    the underlay word is then a run of the sequential register file, a
    globally atomic register execution as in the target of
    Appendix/2Counter.tex:13 (read with decision D2′).  The weak steps are
    reorderings of same-thread calls that [rc_si] allows at the module
    frontier, not effects of [EI].

    ** T7(c): the code needs [I(enq, deq)] ([whw_needs_qsi],
       [whw_not_rel_lin_empty_all])

    The four-thread example of the commented-out spec.tex:89–110 (values
    1–4, threads t1–t4):

    - t1: [enq(1); enq(2)];
    - t2: [deq() -> 2; enq(3)];
    - t3: [deq() -> 3; deq() -> 4];
    - t4: [enq(4); deq() -> 1].

    The execution ([Tw_atomic]): t1 runs both enqueues (slots 0 and 1).
    t4 invokes [enq(4)], whose [FAA] takes slot 2, and then, while that
    enqueue is still pending, invokes [deq()].  The dequeue's [ld] and its
    [xchg] at slot 0 are emitted before the enqueue's [store] into slot 2
    ((store, ld) and (store, xchg at another slot) are semi-independent
    under D2′/D3′, and the dequeue is not tagged with the store; cf.
    [WHWQProg.deq_inv_crosses_store]), so the dequeue returns 1 while slot
    2 is still empty.  t2 dequeues 2 and enqueues 3 (slot 3); t3 dequeues:
    it finds slot 2 empty and takes 3 from slot 3.  Only then is t4's
    store emitted; t4's enqueue returns, and t3 dequeues 4 from slot 2.

    Its overlay trace [Tw] is well formed and complete; it is
    relaxed-linearizable under [I(enq, deq)] ([Tw_rel_lin], explicit
    witness: t4's dequeue is linearized before its own enqueue, which it
    overlaps) and not under the empty relation ([Tw_not_rel_lin_empty]:
    t1's program order and FIFO put the dequeue of 1 before the dequeue
    of 2; t4's and t2's program orders then put enq(4) before enq(3), so
    FIFO puts the dequeue of 4 before the dequeue of 3, against t3's
    program order).  [whw_not_rel_lin_empty_all]: the statement of T6
    (over [EI δRC]) with the empty relation in place of [I(enq, deq)] is
    false.

    Scope (review gate 3, WHWQ-g3-1):
    - The result is over [EI δRC].  By inspection, the same execution is
      one of the paper's module semantics over the target RCMem read with
      D2′ (its underlay word is atomic); it is not shown for every
      implementation of RCMem, since an implementation may lack it.
    - This execution needs both decisions: its exchange overtakes an
      older store, which is impossible under the plain-only relation of
      D2 ([WHWQProg.store_xchg_D2_ordered]) and when the exchange has a
      release write part, as the printed (rlx, rel) or (acq, rel)
      ([WHWQProg.store_xchg_rel_ordered]).  That every separating
      execution needs them is the gate-1 argument, not proved.
    - It needs a client that invokes a call before its own previous call
      has returned: on traces without such self-overlap the relation does
      not matter ([rel_lin_no_self_overlap]; [Tw_self_overlaps]).
    - The reordering used (a younger acquire overtaking an older release
      store to another location) is C11-style (RCpc).  The reviewer argues,
      not checked here, that x86-TSO and ARMv8 forbid the outcome of [Tw]
      and that RC11 (Lahav et al., PLDI 2017) allows it; to be checked
      against the primary sources (Arm ARM and Pulte et al., POPL 2018;
      the x86-TSO model of Sewell et al., CACM 2010).

    ** T7(b): a dequeue inside its own pending enqueue ([Tb6ov_atomic])

    The module produces [POQueueRExample.Tb6ov] (t1: [enq(1)] pending,
    [deq() -> 1] returns first).  The dequeue's [ld] overtakes the queued
    store into slot 0; its [xchg] at slot 0 must wait for the store's
    invocation ([WHWQProg.xchg_same_slot_blocked]), so the store is
    emitted between the dequeue's [ld] and its [xchg].  With
    [POQueueRExample.Tb6ov_b6]: every witness under [I(enq, deq)] is
    [enq(1); deq() -> 1].  The implementation-level B6 corollary (through
    T6) is [WHWQTop.whw_b6]; its hypotheses hold for this trace
    ([WHWQTop.whw_b6_Tb6ov]).

    ** T7(a): the order of two enqueues is decided by the future

    - [whw_future_dependent]: the module produces both
      [POQueueRExample.Tf 1] and [Tf 2].  Their overlay traces agree up to
      the dequeue, but the executions differ earlier, in the order of the
      two [FAA]s, which decides the slots.  With
      [POQueueRExample.future_dependent], every witness of [Tf 1] orders
      [enq(1)] first, although in [Tf1_atomic] the store of [enq(2)] is
      emitted first: a linearization of an enqueue at its store
      (Appendix/WHWQueue.tex:65 and :91) is refuted (review WHWQ-M-2).
    - [whw_future_dependent_module]: two executions with a common prefix
      (the same module configuration), after which [enq(2)] has returned
      and [enq(1)] is pending with its slot below; a dequeue's exchange at
      that slot either precedes [enq(1)]'s store (it returns 2, [Sr1]) or
      follows it (it returns 1, [Sr2]).  Every witness of [Sr1] orders
      [enq(2)] first, every witness of [Sr2] orders [enq(1)] first, and
      both are relaxed-linearizable ([Sr1_atomic], [Sr2_atomic]: both are
      executions with atomic underlay words).  So at the common
      configuration, where [enq(2)] has returned, the relative order of
      the two enqueues is not yet determined.  A proof that must fix it
      by [enq(2)]'s return fails on one of the two continuations; that
      includes a forward simulation against the sequential queue (a
      [GSimRel] with the overlay [EI δQ]) and the TR's single possibility
      (Appendix/WHWQueue.tex:53, :65, :91; review WHWQ-M-2).  This
      consequence is argued from the theorem, not proved.  A single
      possibility over [POQueueR], or over [POQueueRD], which T4 uses, is
      not affected: there the two vertices stay unordered.

    ** Not here

    - [T0] (the trace of [POQueueRExample.T0_needs_qsi]) is argued
      unproducible by the code (gate 1, H1).  That is a statement about
      every execution; it is not proved (review WHWQ-g3-7, open; see the
      scope of [WHWQTop]).

    No axiom is used ([Print Assumptions]; task log). *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareRun.
Require Import models.view.PrefixView.
Require Import examples.Relaxed.WHWQ.WHWQSpec.
Require Import examples.Relaxed.WHWQ.POQueueRWitness.
Require Import examples.Relaxed.WHWQ.POQueueRExample.
Require Import examples.Relaxed.WHWQ.WHWQProg.

Import ListNotations.

Module WHWQExec.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedHoareRun.
  Import WHWQSpec.
  Import POQueueRExample.
  Import WHWQProg.

  Local Abbreviation FP := (FQ positive).
  Local Abbreviation t1 := 1%positive.
  Local Abbreviation t2 := 2%positive.
  Local Abbreviation t3 := 3%positive.
  Local Abbreviation t4 := 4%positive.

  (** Overlay call keys. *)
  Definition ok (t : tid) (h : nat) : CallKey FP := (t, h).

  (** The underlay word of an execution is atomic: every underlay
      invocation is immediately followed by its own response, and no
      response occurs anywhere else.  Over [EI δRC] such a response
      returns the value [δRC] gives at that point, so the underlay word is
      a run of the sequential register file, i.e. a globally atomic
      register execution in the sense of the target of
      Appendix/2Counter.tex:13 (with the signature of decision D2′). *)
  Fixpoint ul_atomic (evs : list (ModuleEvent ERC FP)) : Prop :=
    match evs with
    | [] => True
    | OverlayEvent _ :: rest => ul_atomic rest
    | UnderlayEvent e :: rest =>
        match te_ev ERC e with
        | InvEv h o =>
            match rest with
            | UnderlayEvent e' :: rest' =>
                (exists r, e' = Build_ThreadEvent (te_tid ERC e) (@ResEv ERC h o r)) /\ ul_atomic rest'
            | _ => False
            end
        | ResEv _ _ _ => False
        end
    end.

  (** Overlay traces of executions of [Mwhw] over [EI δRC] from the zero
      memory whose underlay word is atomic. *)
  Definition MTracesAtomic (s : list (ThreadEvent FP)) : Prop :=
    exists evs c,
      module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw
        (initial_tagged_module (RelaxedHoareSpec.EI δRC) (mem0, [])) evs c /\
      RelaxedGSim.overlay_events evs = s /\ ul_atomic evs.

  Lemma mtraces_atomic s :
    MTracesAtomic s -> RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s.
  Proof. intros (evs & c & Hx & Ho & _). exists evs, c. split; assumption. Qed.

  Lemma exec_app_t c1 evs1 c2 evs2 c3 :
    module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw c1 evs1 c2 ->
    module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw c2 evs2 c3 ->
    module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw c1 (evs1 ++ evs2) c3.
  Proof.
    induction 1 as [c | c1 c2' c3' ev evs Hs Hx IH]; intros H; cbn; [exact H |].
    eapply tagged_module_execution_cons; [exact Hs | exact (IH H)].
  Qed.

  Lemma ul_atomic_app l1 l2 : ul_atomic l1 -> ul_atomic l2 -> ul_atomic (l1 ++ l2).
  Proof.
    intros H1 H2.
    assert (Hb : forall n l, length l <= n -> ul_atomic l -> ul_atomic (l ++ l2)).
    { induction n as [| n IH]; intros l Hl Hu.
      - destruct l; [exact H2 | cbn in Hl; lia].
      - destruct l as [| [e | e] l]; [exact H2 | |].
        + cbn in Hu |- *. destruct (te_ev ERC e) as [h o | h o r]; [| contradiction].
          destruct l as [| [e' | e'] l']; try contradiction.
          destruct Hu as [Hr Hu]. cbn. split; [exact Hr |]. apply IH; [cbn in Hl; lia | exact Hu].
        + cbn in Hu |- *. apply IH; [cbn in Hl; lia | exact Hu]. }
    exact (Hb (length l1) l1 (le_n _) H1).
  Qed.

  Lemma overlay_events_app (l1 l2 : list (ModuleEvent ERC FP)) :
    RelaxedGSim.overlay_events (l1 ++ l2) = RelaxedGSim.overlay_events l1 ++ RelaxedGSim.overlay_events l2.
  Proof. unfold RelaxedGSim.overlay_events. apply flat_map_app. Qed.

  Ltac atomic_ok :=
    cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn;
    repeat (split; [eexists; reflexivity |]); exact Logic.I.

  (** ** T7(c): the four-thread execution *)

  Definition Tw : list (ThreadEvent FP) :=
    [ie t1 0 1; re t1 0 1; ie t1 1 2; re t1 1 2;
     ie t4 0 4; idq t4 1; rdq t4 1 1;
     idq t2 0; rdq t2 0 2; ie t2 1 3; re t2 1 3;
     idq t3 0; rdq t3 0 3; re t4 0 4;
     idq t3 1; rdq t3 1 4].

  Theorem Tw_atomic : MTracesAtomic Tw.
  Proof.
    destruct (enq_prod t1 1 0 0) as (a & Ha & Hma & _).
    destruct (enq_prod t1 2 2 1) as (b & Hb & Hmb & _).
    destruct (enq_prod t4 4 0 2) as (c & Hc & Hmc & _).
    destruct (deq_prod t4 2 3 0 1 ltac:(lia) ltac:(lia)) as (d & Hd & Hmd & Hdd).
    destruct (deq_prod t2 0 3 1 2 ltac:(lia) ltac:(lia)) as (e & He & Hme & _).
    destruct (enq_prod t2 3 3 3) as (f & Hf & Hmf & _).
    destruct (deq_prod t3 0 4 3 3 ltac:(lia) ltac:(lia)) as (g & Hg & Hmg & _).
    destruct (deq_prod t3 5 4 2 4 ltac:(lia) ltac:(lia)) as (i & Hi & Hmi & _).
    destruct a as [|a0 [|a1 [|a2 [|a3 a]]]]; try discriminate Hma; destruct a; try discriminate Hma.
    pose proof Hma as Hma'. injection Hma' as A0 A1 A2 A3.
    destruct b as [|b0 [|b1 [|b2 [|b3 b]]]]; try discriminate Hmb; destruct b; try discriminate Hmb.
    pose proof Hmb as Hmb'. injection Hmb' as B0 B1 B2 B3.
    destruct c as [|c0 [|c1 [|c2 [|c3 c]]]]; try discriminate Hmc; destruct c; try discriminate Hmc.
    pose proof Hmc as Hmc'. injection Hmc' as C0 C1 C2 C3.
    destruct d as [|d0 [|d1 [|d2 [|d3 d]]]]; try discriminate Hmd; destruct d; try discriminate Hmd.
    pose proof Hmd as Hmd'. injection Hmd' as D0 D1 D2 D3.
    destruct e as [|e0 [|e1 [|e2 [|e3 [|e4 [|e5 e]]]]]]; try discriminate Hme; destruct e; try discriminate Hme.
    pose proof Hme as Hme'. injection Hme' as F0 F1 F2 F3 F4 F5.
    destruct f as [|f0 [|f1 [|f2 [|f3 f]]]]; try discriminate Hmf; destruct f; try discriminate Hmf.
    pose proof Hmf as Hmf'. injection Hmf' as G0 G1 G2 G3.
    destruct g as [|g0 [|g1 [|g2 [|g3 [|g4 [|g5 [|g6 [|g7 [|g8 [|g9 g]]]]]]]]]]; try discriminate Hmg;
      destruct g; try discriminate Hmg.
    pose proof Hmg as Hmg'. injection Hmg' as H0 H1 H2 H3 H4 H5 H6 H7 H8 H9.
    destruct i as [|i0 [|i1 [|i2 [|i3 [|i4 [|i5 [|i6 [|i7 i]]]]]]]]; try discriminate Hmi;
      destruct i; try discriminate Hmi.
    pose proof Hmi as Hmi'. injection Hmi' as I0 I1 I2 I3 I4 I5 I6 I7.
    unpack_forall Hdd.
    do 2 eexists. split; [| split].
    - (* t1: enq(1) into slot 0 *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t1) (h := 0); [call_fresh_ok | exact Ha | trace_fresh_ok Hma]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t1 0) a0 m_here ei_inv.
      m_step (ok t1 0) a1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t1 0) a2 m_here ei_inv.
      m_step (ok t1 0) a3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 1%positive).
      (* t1: enq(2) into slot 1 *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t1) (h := 1); [call_fresh_ok | exact Hb | trace_fresh_ok Hmb]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t1 1) b0 m_here ei_inv.
      m_step (ok t1 1) b1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t1 1) b2 m_here ei_inv.
      m_step (ok t1 1) b3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 2%positive).
      (* t4: enq(4); its FAA takes slot 2; the store stays queued *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t4) (h := 0); [call_fresh_ok | exact Hc | trace_fresh_ok Hmc]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t4 0) c0 m_here ei_inv.
      m_step (ok t4 0) c1 m_here ltac:(ei_res (@nil (Op ERC))).
      (* t4: deq(), invoked while enq(4) is pending; each of its events
         crosses the pending store's invocation and response *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t4) (h := 1); [call_fresh_ok | exact Hd | trace_fresh_ok Hmd]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t4 1) d0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t4 1) d1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t4 1) d2 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t4 1) d3 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      (* t2: deq() -> 2 (slot 1) *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t2) (h := 0); [call_fresh_ok | exact He | trace_fresh_ok Hme]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t2 0) e0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 0) e1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 0) e2 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 0) e3 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 0) e4 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 0) e5 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      (* t2: enq(3) into slot 3 *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t2) (h := 1); [call_fresh_ok | exact Hf | trace_fresh_ok Hmf]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t2 1) f0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 1) f1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 1) f2 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 1) f3 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 3%positive).
      (* t3: deq() -> 3; slot 2 is still empty *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t3) (h := 0); [call_fresh_ok | exact Hg | trace_fresh_ok Hmg]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t3 0) g0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) g1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) g2 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) g3 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) g4 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) g5 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) g6 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) g7 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) g8 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) g9 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      (* t4's store into slot 2; t4's enq(4) returns *)
      m_step (ok t4 0) c2 m_here ei_inv.
      m_step (ok t4 0) c3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 4%positive).
      (* t3: deq() -> 4 (slot 2) *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t3) (h := 1); [call_fresh_ok | exact Hi | trace_fresh_ok Hmi]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t3 1) i0 m_here ei_inv.
      m_step (ok t3 1) i1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 1) i2 m_here ei_inv.
      m_step (ok t3 1) i3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 1) i4 m_here ei_inv.
      m_step (ok t3 1) i5 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 1) i6 m_here ei_inv.
      m_step (ok t3 1) i7 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      apply tagged_module_execution_refl.
    - reflexivity.
    - atomic_ok.
  Qed.

  Corollary Tw_mtraces : RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) Tw.
  Proof. exact (mtraces_atomic _ Tw_atomic). Qed.

  (** *** The overlay trace [Tw] *)

  Local Abbreviation inv L := (inv_at (@PrefixView.sel FP) L).
  Local Abbreviation res L := (res_at (@PrefixView.sel FP) L).

  (** [exists i] for the first [i <= 15] for which [tac] succeeds. *)
  Ltac find_idx tac :=
    first [ exists 0; tac | exists 1; tac | exists 2; tac | exists 3; tac | exists 4; tac | exists 5; tac
          | exists 6; tac | exists 7; tac | exists 8; tac | exists 9; tac | exists 10; tac | exists 11; tac
          | exists 12; tac | exists 13; tac | exists 14; tac | exists 15; tac ].

  Lemma Tw_wf : PrefixView.wf Tw.
  Proof.
    apply wf_of_entries; [nodup_keys | nodup_keys |].
    cbn. repeat apply Forall_cons; [.. | apply Forall_nil]; find_idx ltac:(split; [cbn; lia | inv_here]).
  Qed.

  Lemma Tw_complete : PrefixView.complete Tw.
  Proof.
    apply complete_of_entries. cbn. repeat apply Forall_cons; [.. | apply Forall_nil];
      find_idx ltac:(eexists; inv_here).
  Qed.

  (** The operations of [Tw]. *)
  Local Abbreviation oE1 := (@Build_Op FP (t1, 0) (enq 1%positive) tt).
  Local Abbreviation oE2 := (@Build_Op FP (t1, 1) (enq 2%positive) tt).
  Local Abbreviation oE4 := (@Build_Op FP (t4, 0) (enq 4%positive) tt).
  Local Abbreviation oD4 := (@Build_Op FP (t4, 1) deq 1%positive).
  Local Abbreviation oD2 := (@Build_Op FP (t2, 0) deq 2%positive).
  Local Abbreviation oE3 := (@Build_Op FP (t2, 1) (enq 3%positive) tt).
  Local Abbreviation oD3 := (@Build_Op FP (t3, 0) deq 3%positive).
  Local Abbreviation oD3' := (@Build_Op FP (t3, 1) deq 4%positive).

  (** A relaxed-happens-before edge that [Tw] cannot have: the positions
      contradict it, the two calls are of different threads, or the pair
      is (enq, deq), which [I(enq, deq)] drops. *)
  Ltac rhb_absurd2 Hr :=
    destruct Hr as [(a & b & Ha & Hb & Hab) | (Ht & a & b & Ha & Hb & Hab & Hn)];
    cbn [op_key op_op op_ret] in Ha, Hb;
    [ apply res_entry in Ha; apply inv_entry in Hb; lookup Ha; lookup Hb; lia
    | first [ cbn in Ht; discriminate Ht
            | apply Hn; exact Logic.I
            | apply inv_entry in Ha; apply inv_entry in Hb; lookup Ha; lookup Hb; lia ] ].

  Ltac in_ok := repeat (first [left; reflexivity | right]).

  (** [exists o, In o W /\ op_key o = k] for a concrete witness [W]. *)
  Ltac cover_ok :=
    match goal with
    | |- exists o, In o ?W /\ op_key o = _ =>
        let rec go l :=
          match l with
          | ?x :: ?l' => first [ exists x; split; [in_ok | reflexivity] | go l' ]
          end in
        go W
    end.

  Ltac before_ok :=
    repeat (first [ apply POQueueRWitness.before_cons_hd; in_ok | apply POQueueRWitness.before_cons_tl ]).

  (** Under [I(enq, deq)]: t4's dequeue is linearized before its own
      overlapping enqueue. *)
  Lemma Tw_rel_lin : rel_lin (@PrefixView.sel FP) Tw (semi_independent FP) (νQ positive).
  Proof.
    exists [oE1; oE2; oD4; oD2; oE3; oE4; oD3; oD3'].
    split; [| split; [| split; [| split]]].
    - eexists. repeat (econstructor; [cbn; reflexivity |]). constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho.
      repeat (destruct Ho as [<- | Ho]; [split; find_idx inv_here |]). destruct Ho.
    - intros i k op Hi. apply inv_entry in Hi. lookup Hi; cover_ok.
    - intros o o' Ho Ho' Hr. cbn in Ho, Ho'.
      repeat (destruct Ho as [<- | Ho]; [| ]); [.. | destruct Ho];
        repeat (destruct Ho' as [<- | Ho']; [| ]); try destruct Ho';
        first [ solve [before_ok] | exfalso; rhb_absurd2 Hr ].
  Qed.

  (** *** Not relaxed-linearizable under ∅ *)

  Section DeqOrder.
    Local Abbreviation run := (@RelaxedHoareSpec.seq_run FP (list positive) (δQ positive)).

    Lemma before_irrefl {B : Type} (W : list B) a : NoDup W -> ~ before W a a.
    Proof.
      intros Hnd (l1 & l2 & -> & Ha). apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. right. exact Ha.
    Qed.

    Lemma before_in_l {B : Type} (W : list B) a b : before W a b -> In a W.
    Proof. intros (l1 & l2 & -> & _). apply in_or_app. right. left. reflexivity. Qed.

    (** FIFO, dequeue order: if [x] is enqueued before [y] (whose only
        enqueue is [oY]) and [y] is dequeued, then [x] is dequeued before. *)
    Lemma fifo_deq_before W (oX oY dY : Op FP) x y :
      νQ positive W -> NoDup W -> before W oX oY -> enq_val oX = Some x -> x <> y ->
      (forall o, In o W -> enq_val o = Some y -> o = oY) ->
      In dY W -> deq_ret dY = Some y ->
      exists dX, before W dX dY /\ deq_ret dX = Some x.
    Proof.
      intros (qf & Hrun) Hnd (W1 & W2 & HW & HoY) HX Hxy Huniq HdY Hy. subst W.
      apply run_app_inv in Hrun as (q1 & H1 & H2).
      destruct oX as [kX opX rX]. destruct opX as [vX |]; cbn in HX; [| discriminate HX].
      injection HX as ->. apply run_enq in H2.
      assert (HY1 : ~ In oY W1) by (intros Hin; exact (nodup_app_disj W1 _ oY Hnd Hin (or_intror HoY))).
      assert (Hy1 : ~ In y q1).
      { intros Hin. destruct (fifo_src _ _ _ _ H1 Hin) as [[] | (o & Ho & Hv)].
        apply HY1. rewrite <- (Huniq o (in_or_app _ _ _ (or_introl Ho)) Hv). exact Ho. }
      assert (HdY2 : In dY W2).
      { apply in_app_or in HdY as [HdY | [HdY | HdY]]; [| subst dY; cbn in Hy; discriminate Hy | exact HdY].
        exfalso. refine (fifo_absent _ _ _ _ H1 _ _ dY HdY Hy); [intros [] |].
        intros o Ho Hv. apply HY1. rewrite <- (Huniq o (in_or_app _ _ _ (or_introl Ho)) Hv). exact Ho. }
      apply in_split in HdY2 as (A & B & ->).
      assert (HA : exists m, run (q1 ++ [x]) (A ++ [dY]) m).
      { replace (A ++ dY :: B) with ((A ++ [dY]) ++ B) in H2 by (rewrite <- app_assoc; reflexivity).
        apply run_app_inv in H2 as (m & Hm & _). exists m. exact Hm. }
      destruct HA as (m & Hm).
      destruct (existsb (fun o => match deq_ret o with Some z => Pos.eqb z x | None => false end) A) eqn:Ex.
      - apply existsb_exists in Ex as (dX & HdX & Hz).
        destruct (deq_ret dX) as [z |] eqn:Hr; [| discriminate Hz]. apply Pos.eqb_eq in Hz. subst z.
        exists dX. split; [| exact Hr].
        apply in_split in HdX as (A1 & A2 & ->).
        exists (W1 ++ Build_Op kX (enq x) rX :: A1), (A2 ++ dY :: B). split.
        + rewrite <- app_assoc. cbn. rewrite <- app_assoc. reflexivity.
        + apply in_or_app. right. left. reflexivity.
      - exfalso. refine (fifo_ahead _ _ _ x y Hm _ _ dY (in_or_app A [dY] dY (or_intror (in_eq dY []))) Hy).
        + exists q1, []. split; [reflexivity | exact Hy1].
        + intros o Ho Hr. apply in_app_or in Ho as [Ho | [<- | []]].
          * assert (Et : existsb (fun o => match deq_ret o with Some z => Pos.eqb z x | None => false end) A = true).
            { apply existsb_exists. exists o. split; [exact Ho | rewrite Hr; apply Pos.eqb_refl]. }
            rewrite Et in Ex. discriminate Ex.
          * rewrite Hy in Hr. injection Hr as Hr. exact (Hxy (eq_sym Hr)).
    Qed.
  End DeqOrder.

  (** The operation of [W] with key [k] is the one of the trace. *)
  Ltac op_enq Hcov Hocc i k v :=
    destruct (Hcov i k (enq v) ltac:(inv_here)) as (o & Ho & Hk);
    destruct o as [k' op x]; cbn in Hk; subst k';
    destruct (Hocc _ Ho) as [(i' & Hi) _]; cbn in Hi; apply inv_entry in Hi; lookup Hi;
    destruct x; exact Ho.

  Ltac op_deq Hcov Hocc i k :=
    destruct (Hcov i k deq ltac:(inv_here)) as (o & Ho & Hk);
    destruct o as [k' op x]; cbn in Hk; subst k';
    let Hi := fresh "Hi" in let Hj := fresh "Hj" in let Hret := fresh "Hret" in
    destruct (Hocc _ Ho) as [(i' & Hi) (j & Hj)]; cbn in Hi, Hj; apply inv_entry in Hi; lookup Hi;
    pose proof (res_deq_ret _ _ _ _ Hj) as Hret; apply res_entry in Hj; lookup Hj;
    cbn in Hret; injection Hret as <-; exact Ho.

  Lemma Tw_not_rel_lin_empty : ~ rel_lin (@PrefixView.sel FP) Tw (fun _ _ => False) (νQ positive).
  Proof.
    intros (W & Hnu & Hnd & Hocc & Hcov & Hord).
    pose proof (NoDup_map_inv _ _ Hnd) as HndW.
    assert (HE1 : In oE1 W) by op_enq Hcov Hocc 0 (t1, 0) 1%positive.
    assert (HE2 : In oE2 W) by op_enq Hcov Hocc 2 (t1, 1) 2%positive.
    assert (HE4 : In oE4 W) by op_enq Hcov Hocc 4 (t4, 0) 4%positive.
    assert (HE3 : In oE3 W) by op_enq Hcov Hocc 9 (t2, 1) 3%positive.
    assert (HD4 : In oD4 W) by op_deq Hcov Hocc 5 (t4, 1).
    assert (HD2 : In oD2 W) by op_deq Hcov Hocc 7 (t2, 0).
    assert (HD3 : In oD3 W) by op_deq Hcov Hocc 11 (t3, 0).
    assert (HD3' : In oD3' W) by op_deq Hcov Hocc 14 (t3, 1).
    (* the only enqueue of 2 and of 3, and the only dequeues returning 1 and 4 *)
    assert (Ue2 : forall o, In o W -> enq_val o = Some 2%positive -> o = oE2).
    { intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [| discriminate Hv].
      injection Hv as ->. destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      apply (RelaxedHoareSpec.nodup_key_eq W _ oE2 Hnd Ho HE2). reflexivity. }
    assert (Ue3 : forall o, In o W -> enq_val o = Some 3%positive -> o = oE3).
    { intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [| discriminate Hv].
      injection Hv as ->. destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      apply (RelaxedHoareSpec.nodup_key_eq W _ oE3 Hnd Ho HE3). reflexivity. }
    assert (Ud1 : forall o, In o W -> deq_ret o = Some 1%positive -> o = oD4).
    { intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [discriminate Hv |].
      injection Hv as ->. destruct (Hocc _ Ho) as [_ (j & Hj)]. cbn in Hj.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj; cbn in Hret; try discriminate Hret.
      apply (RelaxedHoareSpec.nodup_key_eq W _ oD4 Hnd Ho HD4). reflexivity. }
    assert (Ud4 : forall o, In o W -> deq_ret o = Some 4%positive -> o = oD3').
    { intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [discriminate Hv |].
      injection Hv as ->. destruct (Hocc _ Ho) as [_ (j & Hj)]. cbn in Hj.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj; cbn in Hret; try discriminate Hret.
      apply (RelaxedHoareSpec.nodup_key_eq W _ oD3' Hnd Ho HD3'). reflexivity. }
    (* program order, which ∅ keeps for every same-thread pair *)
    assert (H12 : before W oE1 oE2).
    { apply Hord; [exact HE1 | exact HE2 |]. right. split; [reflexivity |].
      exists 0, 2. split; [inv_here |]. split; [inv_here |]. split; [lia | intros []]. }
    assert (H44 : before W oE4 oD4).
    { apply Hord; [exact HE4 | exact HD4 |]. right. split; [reflexivity |].
      exists 4, 5. split; [inv_here |]. split; [inv_here |]. split; [lia | intros []]. }
    assert (H22 : before W oD2 oE3).
    { apply Hord; [exact HD2 | exact HE3 |]. right. split; [reflexivity |].
      exists 7, 9. split; [inv_here |]. split; [inv_here |]. split; [lia | intros []]. }
    assert (H33 : before W oD3 oD3').
    { apply Hord; [exact HD3 | exact HD3' |]. right. split; [reflexivity |].
      exists 11, 14. split; [inv_here |]. split; [inv_here |]. split; [lia | intros []]. }
    (* FIFO: 1 is dequeued before 2, by t4 *)
    destruct (fifo_deq_before W oE1 oE2 oD2 1%positive 2%positive Hnu HndW H12 eq_refl ltac:(discriminate) Ue2 HD2 eq_refl)
      as (dX & HdX & Hr1).
    rewrite (Ud1 dX (before_in_l _ _ _ HdX) Hr1) in HdX.
    (* hence enq(4) before enq(3) *)
    pose proof (before_trans W _ _ _ HndW (before_trans W _ _ _ HndW H44 HdX) H22) as H43.
    (* FIFO: 4 is dequeued before 3, by t3's second dequeue *)
    destruct (fifo_deq_before W oE4 oE3 oD3 4%positive 3%positive Hnu HndW H43 eq_refl ltac:(discriminate) Ue3 HD3 eq_refl)
      as (dY & HdY & Hr4).
    rewrite (Ud4 dY (before_in_l _ _ _ HdY) Hr4) in HdY.
    exact (before_irrefl W _ HndW (before_trans W _ _ _ HndW H33 HdY)).
  Qed.

  (** T7(c). *)
  Theorem whw_needs_qsi :
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) Tw /\
    PrefixView.wf Tw /\ PrefixView.complete Tw /\
    rel_lin (@PrefixView.sel FP) Tw (semi_independent FP) (νQ positive) /\
    ~ rel_lin (@PrefixView.sel FP) Tw (fun _ _ => False) (νQ positive).
  Proof.
    split; [exact Tw_mtraces |]. split; [exact Tw_wf |]. split; [exact Tw_complete |].
    split; [exact Tw_rel_lin | exact Tw_not_rel_lin_empty].
  Qed.

  (** The statement of T6 with the empty relation in place of
      [I(enq, deq)] is false. *)
  Corollary whw_not_rel_lin_empty_all :
    ~ (forall s, RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s ->
         PrefixView.complete s -> rel_lin (@PrefixView.sel FP) s (fun _ _ => False) (νQ positive)).
  Proof. intros H. exact (Tw_not_rel_lin_empty (H Tw Tw_mtraces Tw_complete)). Qed.

  (** ** T7(b): a dequeue inside its own pending enqueue

      [POQueueRExample.Tb6ov]: t1 invokes [enq(1)] and, while it is
      pending, [deq()]; the dequeue returns 1 before the enqueue returns.
      The dequeue's [ld] overtakes the pending store into slot 0, but its
      [xchg] at slot 0 does not ([WHWQProg.xchg_same_slot_blocked]): the
      store (invocation and response) is emitted between the dequeue's
      [ld] and its [xchg].  No [rhb] edge relates the two calls
      ([POQueueRExample.Tb6ov_no_rhb]); [POQueueRExample.Tb6ov_b6]: every
      witness under [I(enq, deq)] is [enq(1); deq() -> 1]. *)

  Theorem Tb6ov_atomic : MTracesAtomic Tb6ov.
  Proof.
    destruct (enq_prod t1 1 0 0) as (a & Ha & Hma & _).
    destruct (deq_prod t1 2 1 0 1 ltac:(lia) ltac:(lia)) as (d & Hd & Hmd & Hdd).
    destruct a as [|a0 [|a1 [|a2 [|a3 a]]]]; try discriminate Hma; destruct a; try discriminate Hma.
    pose proof Hma as Hma'. injection Hma' as A0 A1 A2 A3.
    destruct d as [|d0 [|d1 [|d2 [|d3 d]]]]; try discriminate Hmd; destruct d; try discriminate Hmd.
    pose proof Hmd as Hmd'. injection Hmd' as D0 D1 D2 D3.
    unpack_forall Hdd.
    do 2 eexists. split; [| split].
    - (* t1: enq(1); its FAA takes slot 0 *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t1) (h := 0); [call_fresh_ok | exact Ha | trace_fresh_ok Hma]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t1 0) a0 m_here ei_inv.
      m_step (ok t1 0) a1 m_here ltac:(ei_res (@nil (Op ERC))).
      (* t1: deq(), while enq(1) is pending; its ld crosses the queued store *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t1) (h := 1); [call_fresh_ok | exact Hd | trace_fresh_ok Hmd]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t1 1) d0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t1 1) d1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      (* the exchange at slot 0 waits for the store's invocation; the store
         is emitted (invocation and response) between the ld and the xchg *)
      m_step (ok t1 0) a2 m_here ei_inv.
      m_step (ok t1 0) a3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t1 1) d2 m_here ei_inv.
      m_step (ok t1 1) d3 m_here ltac:(ei_res (@nil (Op ERC))).
      (* the dequeue returns before the enqueue *)
      m_return (@deq positive).
      m_return (@enq positive 1%positive).
      apply tagged_module_execution_refl.
    - reflexivity.
    - atomic_ok.
  Qed.

  Corollary Tb6ov_mtraces : RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) Tb6ov.
  Proof. exact (mtraces_atomic _ Tb6ov_atomic). Qed.

  (** ** T7(a): the future decides the order of two overlapping enqueues

      [POQueueRExample.Tf r]: t1 invokes [enq(1)], t2 invokes [enq(2)],
      t2 returns, t1 returns, then t3's dequeue returns [r].  Both [r = 1]
      and [r = 2] are produced by the module: the [FAA] order of the two
      enqueues decides the slots.  With
      [POQueueRExample.future_dependent], every witness of [Tf 1] orders
      [enq(1)] first and every witness of [Tf 2] orders [enq(2)] first,
      although the two traces agree up to the dequeue. *)

  Theorem Tf1_atomic : MTracesAtomic (Tf 1%positive).
  Proof.
    destruct (enq_prod t1 1 0 0) as (a & Ha & Hma & _).
    destruct (enq_prod t2 2 0 1) as (b & Hb & Hmb & _).
    destruct (deq_prod t3 0 2 0 1 ltac:(lia) ltac:(lia)) as (c & Hc & Hmc & _).
    destruct a as [|a0 [|a1 [|a2 [|a3 a]]]]; try discriminate Hma; destruct a; try discriminate Hma.
    pose proof Hma as Hma'. injection Hma' as A0 A1 A2 A3.
    destruct b as [|b0 [|b1 [|b2 [|b3 b]]]]; try discriminate Hmb; destruct b; try discriminate Hmb.
    pose proof Hmb as Hmb'. injection Hmb' as B0 B1 B2 B3.
    destruct c as [|c0 [|c1 [|c2 [|c3 c]]]]; try discriminate Hmc; destruct c; try discriminate Hmc.
    pose proof Hmc as Hmc'. injection Hmc' as C0 C1 C2 C3.
    do 2 eexists. split; [| split].
    - (* t1's FAA takes slot 0, then t2's takes slot 1 *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t1) (h := 0); [call_fresh_ok | exact Ha | trace_fresh_ok Hma]. }
      cbn [app schedule_trace_tagged map].
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t2) (h := 0); [call_fresh_ok | exact Hb | trace_fresh_ok Hmb]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t1 0) a0 m_here ei_inv.
      m_step (ok t1 0) a1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 0) b0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 0) b1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 0) b2 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 0) b3 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 2%positive).
      m_step (ok t1 0) a2 m_here ei_inv.
      m_step (ok t1 0) a3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 1%positive).
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t3) (h := 0); [call_fresh_ok | exact Hc | trace_fresh_ok Hmc]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t3 0) c0 m_here ei_inv.
      m_step (ok t3 0) c1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) c2 m_here ei_inv.
      m_step (ok t3 0) c3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      apply tagged_module_execution_refl.
    - reflexivity.
    - atomic_ok.
  Qed.

  Corollary Tf1_mtraces : RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) (Tf 1%positive).
  Proof. exact (mtraces_atomic _ Tf1_atomic). Qed.

  Theorem Tf2_atomic : MTracesAtomic (Tf 2%positive).
  Proof.
    destruct (enq_prod t1 1 0 1) as (a & Ha & Hma & _).
    destruct (enq_prod t2 2 0 0) as (b & Hb & Hmb & _).
    destruct (deq_prod t3 0 2 0 2 ltac:(lia) ltac:(lia)) as (c & Hc & Hmc & _).
    destruct a as [|a0 [|a1 [|a2 [|a3 a]]]]; try discriminate Hma; destruct a; try discriminate Hma.
    pose proof Hma as Hma'. injection Hma' as A0 A1 A2 A3.
    destruct b as [|b0 [|b1 [|b2 [|b3 b]]]]; try discriminate Hmb; destruct b; try discriminate Hmb.
    pose proof Hmb as Hmb'. injection Hmb' as B0 B1 B2 B3.
    destruct c as [|c0 [|c1 [|c2 [|c3 c]]]]; try discriminate Hmc; destruct c; try discriminate Hmc.
    pose proof Hmc as Hmc'. injection Hmc' as C0 C1 C2 C3.
    do 2 eexists. split; [| split].
    - (* t2's FAA takes slot 0, then t1's takes slot 1 *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t1) (h := 0); [call_fresh_ok | exact Ha | trace_fresh_ok Hma]. }
      cbn [app schedule_trace_tagged map].
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t2) (h := 0); [call_fresh_ok | exact Hb | trace_fresh_ok Hmb]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t2 0) b0 ltac:(do 4 m_next; m_here) ei_inv.
      m_step (ok t2 0) b1 ltac:(do 4 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 0) b2 ltac:(do 4 m_next; m_here) ei_inv.
      m_step (ok t2 0) b3 ltac:(do 4 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 2%positive).
      m_step (ok t1 0) a0 m_here ei_inv.
      m_step (ok t1 0) a1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t1 0) a2 m_here ei_inv.
      m_step (ok t1 0) a3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 1%positive).
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t3) (h := 0); [call_fresh_ok | exact Hc | trace_fresh_ok Hmc]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t3 0) c0 m_here ei_inv.
      m_step (ok t3 0) c1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) c2 m_here ei_inv.
      m_step (ok t3 0) c3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      apply tagged_module_execution_refl.
    - reflexivity.
    - atomic_ok.
  Qed.

  Corollary Tf2_mtraces : RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) (Tf 2%positive).
  Proof. exact (mtraces_atomic _ Tf2_atomic). Qed.

  Theorem whw_future_dependent :
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) (Tf 1%positive) /\
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) (Tf 2%positive).
  Proof. split; [exact Tf1_mtraces | exact Tf2_mtraces]. Qed.

  (** ** The self-overlap condition

      On a trace in which no thread overlaps two of its own calls, every
      program-order edge is also a real-time edge, so the semi-independence
      relation is irrelevant: [rel_lin] under any relation is [rel_lin]
      under ∅.  Hence the separation of T7(c) needs a client that invokes
      a call before its own previous call has returned. *)

  Section NoSelfOverlap.
    Context {E : RelaxedSig.t}.
    Local Abbreviation sinv L := (inv_at (@PrefixView.sel E) L).
    Local Abbreviation sres L := (res_at (@PrefixView.sel E) L).

    Definition no_self_overlap (L : list (ThreadEvent E)) : Prop :=
      forall i i' j (k k' : CallKey E) op op' (r : Sig.ar op),
        fst k = fst k' -> k <> k' ->
        sinv L i k op -> sinv L i' k' op' -> i < i' -> sres L j k op r -> j < i'.

    Lemma rel_lin_no_self_overlap L (indep : Sig.op (effect E) -> Sig.op (effect E) -> Prop) nu :
      PrefixView.wf L -> no_self_overlap L ->
      rel_lin (@PrefixView.sel E) L indep nu <-> rel_lin (@PrefixView.sel E) L (fun _ _ => False) nu.
    Proof.
      intros Hwf Hno. split; [| apply rel_lin_mono; intros a b []].
      intros (W & Hnu & Hnd & Hocc & Hall & Hord).
      exists W. split; [exact Hnu |]. split; [exact Hnd |]. split; [exact Hocc |]. split; [exact Hall |].
      intros o o' Ho Ho' Hr. apply Hord; [exact Ho | exact Ho' |].
      destruct Hr as [Hrt | (Ht & i & i' & Hi & Hi' & Hii & _)]; [left; exact Hrt |].
      left. destruct (Hocc o Ho) as [_ (j & Hj)].
      exists j, i'. split; [exact Hj |]. split; [exact Hi' |].
      refine (Hno i i' j (op_key o) (op_key o') (op_op o) (op_op o') (op_ret o) Ht _ Hi Hi' Hii Hj).
      intros Hk. destruct Hwf as (Hw1 & _ & _). rewrite Hk in Hi.
      pose proof (Hw1 i i' (op_key o') (op_op o) (op_op o') Hi Hi') as Heq. lia.
    Qed.
  End NoSelfOverlap.

  (** [Tw] has a thread that overlaps its own calls (t4), as it must. *)
  Corollary Tw_self_overlaps : ~ no_self_overlap Tw.
  Proof.
    intros Hno. apply Tw_not_rel_lin_empty.
    apply (proj1 (rel_lin_no_self_overlap Tw (semi_independent FP) (νQ positive) Tw_wf Hno)).
    exact Tw_rel_lin.
  Qed.

  (** ** T7(a), at the module level: the future decides the order

      Two executions share their whole prefix [evs0] (the same module
      configuration [c0]): t1 and t2 invoke [enq(1)] and [enq(2)], t1's
      [FAA] takes slot 0 and t2's takes slot 1, t2's store is emitted and
      t2 returns, while t1's store is still queued.  Then t3 invokes
      [deq()].  If its exchange at slot 0 comes before t1's store, it
      finds slot 0 empty and takes 2 from slot 1 ([Sr1]); if after, it
      takes 1 ([Sr2]).  Every witness of [Sr1] orders [enq(2)] first, every
      witness of [Sr2] orders [enq(1)] first, and both traces are
      relaxed-linearizable.  So at [c0], where [enq(2)] has returned, the
      relative order of the two enqueues is not yet determined; a proof
      that must fix it by [enq(2)]'s return (a forward simulation against
      the sequential queue, or the TR's single possibility; review
      WHWQ-M-2) fails on one of the two continuations (argued from this
      theorem, not proved).  (The module semantics fixes a method's whole
      trace at its invocation, so the common point is before t3's
      invocation.)  Every segment has an atomic underlay word. *)

  Definition Pre_r : list (ThreadEvent FP) := [ie t1 0 1; ie t2 0 2; re t2 0 2].
  Definition Fut_r1 : list (ThreadEvent FP) := [idq t3 0; rdq t3 0 2; re t1 0 1].
  Definition Fut_r2 : list (ThreadEvent FP) := [idq t3 0; re t1 0 1; rdq t3 0 1].
  Definition Sr1 : list (ThreadEvent FP) := Pre_r ++ Fut_r1.
  Definition Sr2 : list (ThreadEvent FP) := Pre_r ++ Fut_r2.

  Theorem whw_scan_race :
    exists evs0 c0,
      module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw
        (initial_tagged_module (RelaxedHoareSpec.EI δRC) (mem0, [])) evs0 c0 /\ ul_atomic evs0 /\
      RelaxedGSim.overlay_events evs0 = Pre_r /\
      (exists evs1 c1, module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw c0 evs1 c1 /\ ul_atomic evs1 /\
         RelaxedGSim.overlay_events evs1 = Fut_r1) /\
      (exists evs2 c2, module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw c0 evs2 c2 /\ ul_atomic evs2 /\
         RelaxedGSim.overlay_events evs2 = Fut_r2).
  Proof.
    destruct (enq_prod t1 1 0 0) as (a & Ha & Hma & _).
    destruct (enq_prod t2 2 0 1) as (b & Hb & Hmb & _).
    destruct (deq_prod t3 0 2 1 2 ltac:(lia) ltac:(lia)) as (c & Hc & Hmc & _).
    destruct (deq_prod t3 0 2 0 1 ltac:(lia) ltac:(lia)) as (d & Hd & Hmd & _).
    destruct a as [|a0 [|a1 [|a2 [|a3 a]]]]; try discriminate Hma; destruct a; try discriminate Hma.
    pose proof Hma as Hma'. injection Hma' as A0 A1 A2 A3.
    destruct b as [|b0 [|b1 [|b2 [|b3 b]]]]; try discriminate Hmb; destruct b; try discriminate Hmb.
    pose proof Hmb as Hmb'. injection Hmb' as B0 B1 B2 B3.
    destruct c as [|c0 [|c1 [|c2 [|c3 [|c4 [|c5 c]]]]]]; try discriminate Hmc; destruct c; try discriminate Hmc.
    pose proof Hmc as Hmc'. injection Hmc' as C0 C1 C2 C3 C4 C5.
    destruct d as [|d0 [|d1 [|d2 [|d3 d]]]]; try discriminate Hmd; destruct d; try discriminate Hmd.
    pose proof Hmd as Hmd'. injection Hmd' as D0 D1 D2 D3.
    eexists _, _. split; [| split; [| split; [| split]]].
    - (* the common prefix *)
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t1) (h := 0); [call_fresh_ok | exact Ha | trace_fresh_ok Hma]. }
      cbn [app schedule_trace_tagged map].
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t2) (h := 0); [call_fresh_ok | exact Hb | trace_fresh_ok Hmb]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t1 0) a0 m_here ei_inv.
      m_step (ok t1 0) a1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 0) b0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 0) b1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t2 0) b2 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t2 0) b3 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 2%positive).
      apply tagged_module_execution_refl.
    - atomic_ok.
    - reflexivity.
    - (* the exchange at slot 0 comes before t1's store: deq() -> 2 *)
      do 2 eexists. split; [| split].
      {
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t3) (h := 0); [call_fresh_ok | exact Hc | trace_fresh_ok Hmc]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t3 0) c0 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) c1 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) c2 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) c3 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) c4 ltac:(do 2 m_next; m_here) ei_inv.
      m_step (ok t3 0) c5 ltac:(do 2 m_next; m_here) ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      m_step (ok t1 0) a2 m_here ei_inv.
      m_step (ok t1 0) a3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 1%positive).
      apply tagged_module_execution_refl.
      }
      { atomic_ok. }
      reflexivity.
    - (* t1's store comes first: deq() -> 1 *)
      do 2 eexists. split; [| split].
      {
      eapply tagged_module_execution_cons.
      { eapply tagged_invoke with (t := t3) (h := 0); [call_fresh_ok | exact Hd | trace_fresh_ok Hmd]. }
      cbn [app schedule_trace_tagged map].
      m_step (ok t1 0) a2 m_here ei_inv.
      m_step (ok t1 0) a3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@enq positive 1%positive).
      m_step (ok t3 0) d0 m_here ei_inv.
      m_step (ok t3 0) d1 m_here ltac:(ei_res (@nil (Op ERC))).
      m_step (ok t3 0) d2 m_here ei_inv.
      m_step (ok t3 0) d3 m_here ltac:(ei_res (@nil (Op ERC))).
      m_return (@deq positive).
      apply tagged_module_execution_refl.
      }
      { atomic_ok. }
      reflexivity.
  Qed.

  Corollary Sr1_atomic : MTracesAtomic Sr1.
  Proof.
    destruct whw_scan_race as (evs0 & c0 & Hx0 & Ha0 & Ho0 & (evs1 & c1 & Hx1 & Ha1 & Ho1) & _).
    exists (evs0 ++ evs1), c1. split; [exact (exec_app_t _ _ _ _ _ Hx0 Hx1) |].
    split; [unfold Sr1; rewrite overlay_events_app, Ho0, Ho1; reflexivity | exact (ul_atomic_app _ _ Ha0 Ha1)].
  Qed.

  Corollary Sr2_atomic : MTracesAtomic Sr2.
  Proof.
    destruct whw_scan_race as (evs0 & c0 & Hx0 & Ha0 & Ho0 & _ & (evs2 & c2 & Hx2 & Ha2 & Ho2)).
    exists (evs0 ++ evs2), c2. split; [exact (exec_app_t _ _ _ _ _ Hx0 Hx2) |].
    split; [unfold Sr2; rewrite overlay_events_app, Ho0, Ho2; reflexivity | exact (ul_atomic_app _ _ Ha0 Ha2)].
  Qed.

  Local Abbreviation rE1 := (@Build_Op FP (t1, 0) (enq 1%positive) tt).
  Local Abbreviation rE2 := (@Build_Op FP (t2, 0) (enq 2%positive) tt).

  Lemma Sr1_rel_lin : rel_lin (@PrefixView.sel FP) Sr1 (semi_independent FP) (νQ positive).
  Proof.
    exists [rE2; @Build_Op FP (t3, 0) deq 2%positive; rE1].
    split; [| split; [| split; [| split]]].
    - eexists. repeat (econstructor; [cbn; reflexivity |]). constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho.
      repeat (destruct Ho as [<- | Ho]; [split; find_idx inv_here |]). destruct Ho.
    - intros i k op Hi. apply inv_entry in Hi. lookup Hi; cover_ok.
    - intros o o' Ho Ho' Hr. cbn in Ho, Ho'.
      repeat (destruct Ho as [<- | Ho]; [| ]); [.. | destruct Ho];
        repeat (destruct Ho' as [<- | Ho']; [| ]); try destruct Ho';
        first [ solve [before_ok] | exfalso; rhb_absurd2 Hr ].
  Qed.

  Lemma Sr2_rel_lin : rel_lin (@PrefixView.sel FP) Sr2 (semi_independent FP) (νQ positive).
  Proof.
    exists [rE1; rE2; @Build_Op FP (t3, 0) deq 1%positive].
    split; [| split; [| split; [| split]]].
    - eexists. repeat (econstructor; [cbn; reflexivity |]). constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho.
      repeat (destruct Ho as [<- | Ho]; [split; find_idx inv_here |]). destruct Ho.
    - intros i k op Hi. apply inv_entry in Hi. lookup Hi; cover_ok.
    - intros o o' Ho Ho' Hr. cbn in Ho, Ho'.
      repeat (destruct Ho as [<- | Ho]; [| ]); [.. | destruct Ho];
        repeat (destruct Ho' as [<- | Ho']; [| ]); try destruct Ho';
        first [ solve [before_ok] | exfalso; rhb_absurd2 Hr ].
  Qed.

  (** Every witness of [Sr1] orders [enq(2)] first. *)
  Lemma Sr1_order W :
    rel_lin_witness (@PrefixView.sel FP) Sr1 (semi_independent FP) (νQ positive) W -> before W rE2 rE1.
  Proof.
    intros (Hnu & Hnd & Hocc & Hcov & Hord).
    pose proof (NoDup_map_inv _ _ Hnd) as HndW.
    assert (HE1 : In rE1 W) by op_enq Hcov Hocc 0 (t1, 0) 1%positive.
    assert (HE2 : In rE2 W) by op_enq Hcov Hocc 1 (t2, 0) 2%positive.
    assert (HD : In (@Build_Op FP (t3, 0) deq 2%positive) W) by op_deq Hcov Hocc 3 (t3, 0).
    destruct (before_total W rE1 rE2 HE1 HE2 ltac:(discriminate)) as [H | H]; [| exact H].
    exfalso.
    refine (fifo_order W rE1 rE2 1%positive 2%positive Hnu HndW H eq_refl ltac:(discriminate) _ _ _ HD eq_refl).
    - intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [| discriminate Hv].
      injection Hv as ->. destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      apply (RelaxedHoareSpec.nodup_key_eq W _ rE2 Hnd Ho HE2). reflexivity.
    - intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [discriminate Hv |].
      injection Hv as ->. destruct (Hocc _ Ho) as [_ (j & Hj)]. cbn in Hj.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj; cbn in Hret; discriminate Hret.
  Qed.

  (** Every witness of [Sr2] orders [enq(1)] first. *)
  Lemma Sr2_order W :
    rel_lin_witness (@PrefixView.sel FP) Sr2 (semi_independent FP) (νQ positive) W -> before W rE1 rE2.
  Proof.
    intros (Hnu & Hnd & Hocc & Hcov & Hord).
    pose proof (NoDup_map_inv _ _ Hnd) as HndW.
    assert (HE1 : In rE1 W) by op_enq Hcov Hocc 0 (t1, 0) 1%positive.
    assert (HE2 : In rE2 W) by op_enq Hcov Hocc 1 (t2, 0) 2%positive.
    assert (HD : In (@Build_Op FP (t3, 0) deq 1%positive) W) by op_deq Hcov Hocc 3 (t3, 0).
    destruct (before_total W rE1 rE2 HE1 HE2 ltac:(discriminate)) as [H | H]; [exact H |].
    exfalso.
    refine (fifo_order W rE2 rE1 2%positive 1%positive Hnu HndW H eq_refl ltac:(discriminate) _ _ _ HD eq_refl).
    - intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [| discriminate Hv].
      injection Hv as ->. destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      apply (RelaxedHoareSpec.nodup_key_eq W _ rE1 Hnd Ho HE1). reflexivity.
    - intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [discriminate Hv |].
      injection Hv as ->. destruct (Hocc _ Ho) as [_ (j & Hj)]. cbn in Hj.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj; cbn in Hret; discriminate Hret.
  Qed.

  (** T7(a) at the module level. *)
  Theorem whw_future_dependent_module :
    (exists evs0 c0,
      module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw
        (initial_tagged_module (RelaxedHoareSpec.EI δRC) (mem0, [])) evs0 c0 /\ ul_atomic evs0 /\
      RelaxedGSim.overlay_events evs0 = Pre_r /\
      (exists evs1 c1, module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw c0 evs1 c1 /\ ul_atomic evs1 /\
         RelaxedGSim.overlay_events evs1 = Fut_r1) /\
      (exists evs2 c2, module_execution_tagged (RelaxedHoareSpec.EI δRC) Mwhw c0 evs2 c2 /\ ul_atomic evs2 /\
         RelaxedGSim.overlay_events evs2 = Fut_r2)) /\
    rel_lin (@PrefixView.sel FP) (Pre_r ++ Fut_r1) (semi_independent FP) (νQ positive) /\
    rel_lin (@PrefixView.sel FP) (Pre_r ++ Fut_r2) (semi_independent FP) (νQ positive) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) (Pre_r ++ Fut_r1) (semi_independent FP) (νQ positive) W ->
       before W rE2 rE1) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) (Pre_r ++ Fut_r2) (semi_independent FP) (νQ positive) W ->
       before W rE1 rE2).
  Proof.
    split; [exact whw_scan_race |]. split; [exact Sr1_rel_lin |]. split; [exact Sr2_rel_lin |].
    split; [exact Sr1_order | exact Sr2_order].
  Qed.

End WHWQExec.
