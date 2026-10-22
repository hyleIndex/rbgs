(** * WHWQTop: the weak Herlihy–Wing queue is relaxed-linearizable

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P8; review gate 5
    (.rocq-review/latest-review.md).  Everything here is a consequence of
    T4 ([WHWQDeq.whw_rlhl2]: the RLHL hypotheses of the module [Mwhw]
    over the handle-linear underlay [EIhl δRC], with the overlay
    presentation [POQueueRD]) and of T2D ([POQueueRD.poqrd_sound]:
    [POQueueRD] is a sound presentation of [(νQ, I(enq, deq))]).  No new
    proof obligation about the code is discharged here.

    ** Results

    - T5 [whw_complin]: copy-cat trace inclusion.  Every overlay trace of
      [Mwhw] over [EI δRC] from the zero memory, complete or not, is a
      trace of the copy-cat over [POQueueRD]
      ([RelaxedHoareCompLin.rlhl_complin], then
      [RelaxedHoareCompLinSpec.complin_hlift_under]).  The statement
      mentions the presentation, and the presentation is not complete:
      neither [POQueueR] ([POQueueRExample.POQueueR_incomplete]) nor
      [POQueueRD] ([POQueueRD_incomplete], [POQueueRD_not_complete_pres])
      accepts the relaxed-linearizable trace [Tinc].  So T5 is cited only
      as trace inclusion into that copy-cat (review gate 1, WHWQ-m-1), not
      as the interface of a layer above the queue.  See also the scope
      note on prefixes below.
    - T6 [whw_rel_lin]: every complete overlay trace of [Mwhw] over
      [EI δRC] from the zero memory is relaxed-linearizable to [νQ] under
      [semi_independent FP = I(enq, deq)].  The presentation does not
      occur in the statement.  The proof uses
      [RelaxedHoareGSim.rlhl_rsim] (the global simulation [RSim]),
      [RelaxedHoareCompLinSpec.gsim_rel_lin_traces] with
      [HVF := poqrd_sound], and [hlift_ei] from [EI δRC] to [EIhl δRC].
    - [whw_rel_lin_sharp]: T6 holds with [I(enq, deq)] and is false with
      the empty relation ([WHWQExec.whw_not_rel_lin_empty_all], the
      four-thread execution [Tw]).  This is a property of the module, not
      only of the presentation.  Its scope is that of review gate 3
      (WHWQ-g3-1):
      - it is shown over [EI δRC] only;
      - the separating execution needs decisions D2′ and D3′
        ([WHWQProg.store_xchg_D2_ordered], [store_xchg_rel_ordered]);
        that every separating execution does is argued;
      - its reordering (a younger acquire overtaking an older release
        store to another location) is RCpc-style, and argued to be
        forbidden on x86-TSO and ARMv8;
      - only clients that overlap their own calls can observe it
        ([WHWQExec.rel_lin_no_self_overlap]);
      - necessity is shown against the empty relation only, not against
        other sub-relations of [I(enq, deq)].
    - B6 at the implementation level ([whw_b6]): in a complete trace of
      the module whose only calls are [enq v] and [deq] of one thread, the
      dequeue returns [v] ([POQueueRExample.b6_returns] applied to T6).
      This follows from the blocking dequeue of [δQ] and from the
      hypothesis that these are the only calls.  It does not depend on the
      relation ([b6_enq_deq] holds for any relation).  So it answers the
      illustration of Review B through the blocking API (author response
      B6), not through the choice of [I(enq, deq)] (review WHWQ-g5-2).
      In the order dequeue first there is no complete trace at all
      ([whw_b6_enq_first]): [(deq, enq)] is not semi-independent, so the
      dequeue is [rhb]-before the enqueue, against the only witness
      [enq v; deq -> v].  In that order the guarantee is only that the
      execution does not complete (WHWQ-g3-6, WHWQ-g5-1).  Non-vacuity for
      the other order ([whw_b6_Tb6ov]): the module produces [Tb6ov], where
      the dequeue is invoked while the enqueue is pending and returns
      first ([WHWQExec.Tb6ov_mtraces]).
    - Consistency checks of T6 against the executions of P5
      ([whw_consistency]): [Tw], [Tb6ov] and [Tf 1], [Tf 2] are
      relaxed-linearizable by T6, as [WHWQExec] and [POQueueRExample]
      show directly.  [whw_future_dependent_lin]: both [Tf] traces are
      module traces, and their witnesses order the two enqueues in
      opposite ways.  This is at the trace level: the two executions
      differ earlier, in the order of the [FAA]s.  For two executions
      from one module configuration, see
      [WHWQExec.whw_future_dependent_module].

    ** Scope

    - Over [EI δRC] only.  [EI δRC] is not a complete presentation of
      RCMem (store buffering), so "for every underlay that refines
      ν_RCMem" would need absorption (latest-review M-22).  Its underlay
      word is a run of the sequential register file, with effects at
      invocation.  Every weak behaviour comes from the module frontier
      (the semi-independence of [ERC], decisions D2′ and D3′).
    - Complete traces only (T6), so T6 cannot feed a layer above the
      queue.  T5 covers every prefix, but only into the copy-cat over
      [POQueueRD], and these prefixes include an artifact of the module
      semantics (review WHWQ-g5-3).  A dequeue whose last [xchg] is
      committed with a non-null result and reads null never responds
      (decision C7, [POQueueRD.poqrd_dead]).  It does not block the later
      calls of its thread, while the code would keep them waiting behind
      its acquires.  Such a prefix is argued not to be a trace of the
      copy-cat over [EI δQ], where an emitted dequeue always consumes a
      value.  So the presentation-free prefix form ([RCompLin] into
      [EI δQ], research-intent §8) is expected to fail for [Mwhw].  This
      is argued, not proved.
    - Not proved here: that the code never produces the trace
      [POQueueRExample.T0] (WHWQ-g3-7).  [T0] is a path of [POQueueR], so
      T5 and T6 cannot exclude it.  A proof needs code-level facts of the
      dequeue's scan order.  Also not proved: that no [GSimRel] over the
      atomic [POQueueR] exists for [Mwhw] (decision C7).  The author
      deferred that decision to P8, and it is open.

    Assumptions ([Print Assumptions]; task log): [whw_complin] uses
    [classic], through [RelaxedHoareCompLin.gsim_complin].  T6 and its
    corollaries use [eq_rect_eq], through [RelaxedGSim.gsim_rel_lin].
    [whw_future_dependent_lin], [POQueueRD_incomplete] and
    [POQueueRD_not_complete_pres] are closed.  Nothing here or in T4 adds
    an axiom ([whw_rlhl2] and [poqrd_sound] are closed). *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.view.ViewLHL.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareGSim.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import examples.Relaxed.WHWQ.WHWQSpec.
Require Import examples.Relaxed.WHWQ.POQueueR.
Require Import examples.Relaxed.WHWQ.POQueueRExample.
Require Import examples.Relaxed.WHWQ.POQueueRD.
Require Import examples.Relaxed.WHWQ.WHWQProg.
Require Import examples.Relaxed.WHWQ.WHWQExec.
Require Import examples.Relaxed.WHWQ.WHWQInv.
Require Import examples.Relaxed.WHWQ.WHWQDeq.

Import ListNotations.

Module WHWQTop.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import RelaxedHoareBase.
  Import RelaxedHoareGSim.
  Import RelaxedHoareCompLin.
  Import RelaxedHoareCompLinSpec.
  Import WHWQSpec.
  Import POQueueR.
  Import POQueueRExample.
  Import POQueueRD.
  Import WHWQProg.
  Import WHWQExec.
  Import WHWQInv.
  Import WHWQDeq.

  Local Abbreviation FP := (FQ positive).
  Local Abbreviation VE := (EIhl (E := ERC) δRC).
  Local Abbreviation VF := (POQueueRD.POQueueRD positive).
  Local Abbreviation t1 := 1%positive.

  (** ** T5: copy-cat trace inclusion, for every execution *)

  Theorem whw_complin : RCompLin Mwhw (RelaxedHoareSpec.EI δRC) (mem0, []) VF poqr_init.
  Proof.
    apply (proj2 (complin_hlift_under Mwhw (RelaxedHoareSpec.EI δRC) (mem0, []) VF poqr_init)).
    exact (rlhl_complin Iq Rq Gq Mwhw ((mem0, []), []) poqr_init whw_rlhl2).
  Qed.

  (** ** T6: relaxed linearizability of every complete trace *)

  (** The global simulation of T4, from the initial configuration over
      [EIhl δRC]. *)
  Lemma whw_rsim :
    GSimRel VE VF Mwhw (RSim Iq Rq Gq) /\
    RSim Iq Rq Gq (initial_tagged_module VE ((mem0, []), [])) (@PossOk FP VF poqr_init []).
  Proof. exact (rlhl_rsim Iq Rq Gq Mwhw ((mem0, []), []) poqr_init whw_rlhl2). Qed.

  Theorem whw_rel_lin s :
    MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s -> PrefixView.complete s ->
    rel_lin (@PrefixView.sel FP) s (semi_independent FP) (νQ positive).
  Proof.
    intros Htr Hc. apply (hlift_ei δRC Mwhw (mem0, []) s) in Htr.
    destruct whw_rsim as [HS H0].
    exact (gsim_rel_lin_traces VE VF Mwhw (RSim Iq Rq Gq) ((mem0, []), []) poqr_init HS H0 (νQ positive)
             (@poqrd_sound positive) s Htr Hc).
  Qed.

  (** Every overlay trace of the module is well formed. *)
  Lemma whw_trace_wf s : MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s -> PrefixView.wf s.
  Proof.
    intros Htr. apply (hlift_ei δRC Mwhw (mem0, []) s) in Htr.
    destruct whw_rsim as [HS H0].
    exact (gsim_trace_wf VE VF Mwhw (RSim Iq Rq Gq) ((mem0, []), []) poqr_init HS H0 s Htr).
  Qed.

  (** T6 is sharp: it fails with the empty relation in place of
      [I(enq, deq)]. *)
  Corollary whw_rel_lin_sharp :
    (forall s, MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s -> PrefixView.complete s ->
       rel_lin (@PrefixView.sel FP) s (semi_independent FP) (νQ positive)) /\
    ~ (forall s, MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s -> PrefixView.complete s ->
         rel_lin (@PrefixView.sel FP) s (fun _ _ => False) (νQ positive)).
  Proof. split; [exact whw_rel_lin | exact whw_not_rel_lin_empty_all]. Qed.

  (** ** B6 at the implementation level *)

  Local Abbreviation inv L := (inv_at (@PrefixView.sel FP) L).
  Local Abbreviation res L := (res_at (@PrefixView.sel FP) L).

  Corollary whw_b6 (v : positive) s t h1 h2 :
    MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s -> PrefixView.complete s -> h1 <> h2 ->
    (forall i k op, inv s i k op -> (k = (t, h1) /\ op = enq v) \/ (k = (t, h2) /\ op = deq)) ->
    (exists i, inv s i (t, h1) (enq v)) -> (exists i, inv s i (t, h2) deq) ->
    forall j (r : positive), res s j (t, h2) deq r -> r = v.
  Proof.
    intros Htr Hc Hh Hinv Hi1 Hi2.
    exact (b6_returns v s t h1 h2 Hh (whw_trace_wf s Htr) Hinv Hi1 Hi2 (whw_rel_lin s Htr Hc)).
  Qed.

  (** In the order dequeue first there is no complete trace: [(deq, enq)]
      is not semi-independent, so the dequeue is [rhb]-before the
      enqueue, against the only witness [enq v; deq -> v]
      ([b6_enq_deq]).  (Proof by the gate-5 reviewer, review WHWQ-g5-1.) *)
  Corollary whw_b6_enq_first (v : positive) s t h1 h2 :
    MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) s -> PrefixView.complete s -> h1 <> h2 ->
    (forall i k op, inv s i k op -> (k = (t, h1) /\ op = enq v) \/ (k = (t, h2) /\ op = deq)) ->
    forall i1 i2, inv s i1 (t, h1) (enq v) -> inv s i2 (t, h2) deq -> i1 < i2.
  Proof.
    intros Htr Hc Hh Hinv i1 i2 Hi1 Hi2.
    destruct (whw_rel_lin s Htr Hc) as (W & HW).
    pose proof (b6_enq_deq v s t h1 h2 W Hh Hinv (ex_intro _ i1 Hi1) (ex_intro _ i2 Hi2) HW) as HWeq.
    assert (Hne : i1 <> i2).
    { intros ->. destruct Hi1 as (x & Hx & Hs1), Hi2 as (y & Hy & Hs2). rewrite Hx in Hy. injection Hy as <-.
      unfold PrefixView.sel in Hs1, Hs2. rewrite Hs1 in Hs2. injection Hs2 as H. exact (Hh H). }
    destruct (Nat.lt_ge_cases i1 i2) as [H | H]; [exact H | exfalso].
    destruct HW as (_ & _ & _ & _ & Hord).
    assert (Hr : rhb (@PrefixView.sel FP) s (semi_independent FP)
                   (@Build_Op FP (t, h2) deq v) (@Build_Op FP (t, h1) (enq v) tt)).
    { right. split; [reflexivity |]. exists i2, i1. split; [exact Hi2 |]. split; [exact Hi1 |].
      split; [lia |]. cbn. intros []. }
    rewrite HWeq in Hord.
    specialize (Hord _ _ ltac:(right; left; reflexivity) ltac:(left; reflexivity) Hr).
    destruct Hord as (l1 & l2 & Heq & Hin).
    destruct l1 as [| a [| b l1]]; cbn in Heq; inversion Heq; subst.
    all: try (destruct Hin; fail).
    all: try (match goal with H : [] = _ ++ _ |- _ => destruct (app_cons_not_nil _ _ _ H) end).
  Qed.

  (** The hypotheses of [whw_b6] hold for a trace of the module in which
      the enqueue is invoked first, and the dequeue is invoked while the
      enqueue is pending and returns first ([Tb6ov]). *)
  Corollary whw_b6_Tb6ov :
    MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) Tb6ov /\ PrefixView.complete Tb6ov /\
    (forall i k op, inv Tb6ov i k op -> (k = (t1, 0) /\ op = enq 1%positive) \/ (k = (t1, 1) /\ op = deq)) /\
    (exists i, inv Tb6ov i (t1, 0) (enq 1%positive)) /\ (exists i, inv Tb6ov i (t1, 1) deq) /\
    (forall j (r : positive), res Tb6ov j (t1, 1) deq r -> r = 1%positive).
  Proof.
    assert (Hinv : forall i k op, inv Tb6ov i k op -> (k = (t1, 0) /\ op = enq 1%positive) \/ (k = (t1, 1) /\ op = deq)).
    { intros i k op Hi. apply inv_entry in Hi. lookup Hi; [left | right]; split; reflexivity. }
    split; [exact Tb6ov_mtraces |]. split; [exact Tb6ov_complete |]. split; [exact Hinv |].
    split; [exists 0; inv_here |]. split; [exists 1; inv_here |].
    exact (whw_b6 1%positive Tb6ov t1 0 1 Tb6ov_mtraces Tb6ov_complete ltac:(discriminate) Hinv
             ltac:(exists 0; inv_here) ltac:(exists 1; inv_here)).
  Qed.

  (** ** Consistency with the executions of P5 *)

  (** T6 re-derives the relaxed linearizability of the traces that
      [WHWQExec] and [POQueueRExample] prove directly. *)
  Corollary whw_consistency :
    rel_lin (@PrefixView.sel FP) Tw (semi_independent FP) (νQ positive) /\
    rel_lin (@PrefixView.sel FP) Tb6ov (semi_independent FP) (νQ positive) /\
    rel_lin (@PrefixView.sel FP) (Tf 1%positive) (semi_independent FP) (νQ positive) /\
    rel_lin (@PrefixView.sel FP) (Tf 2%positive) (semi_independent FP) (νQ positive).
  Proof.
    split; [exact (whw_rel_lin Tw Tw_mtraces Tw_complete) |].
    split; [exact (whw_rel_lin Tb6ov Tb6ov_mtraces Tb6ov_complete) |].
    split; [exact (whw_rel_lin _ Tf1_mtraces (Tf_complete _)) | exact (whw_rel_lin _ Tf2_mtraces (Tf_complete _))].
  Qed.

  (** The future decides the order of two overlapping enqueues, at the
      trace level: both traces are module traces with a common prefix of
      four events, and every witness of one orders the enqueues against
      every witness of the other ([POQueueRExample.future_dependent]).
      The two executions differ earlier, in the order of the [FAA]s; for
      two continuations of one module configuration see
      [WHWQExec.whw_future_dependent_module]. *)
  Corollary whw_future_dependent_lin :
    MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) (Tf 1%positive) /\
    MTraces (RelaxedHoareSpec.EI δRC) Mwhw (mem0, []) (Tf 2%positive) /\
    firstn 4 (Tf 1%positive) = firstn 4 (Tf 2%positive) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) (Tf 1%positive) (semi_independent FP) (νQ positive) W ->
       before W Ea Eb) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) (Tf 2%positive) (semi_independent FP) (νQ positive) W ->
       before W Eb Ea).
  Proof.
    destruct future_dependent as (Hpre & _ & H1 & H2).
    split; [exact Tf1_mtraces |]. split; [exact Tf2_mtraces |]. split; [exact Hpre |]. split; [exact H1 | exact H2].
  Qed.

  (** ** [POQueueRD] is not a complete presentation

      As [POQueueR] ([POQueueRExample.POQueueR_incomplete]): the dead step
      is a dequeue invocation, so it does not help the two overlapping
      enqueues of [Tinc].  (Proof of [Tinc_no_path_D] by the gate-5
      reviewer, review WHWQ-g5-6.) *)
  Lemma Tinc_no_path_D c : ~ vf_path VF poqr_init Tinc c.
  Proof.
    intros Hp. unfold Tinc in Hp.
    apply vf_path_cons_inv in Hp as (c1 & Hs1 & Hp). apply vf_path_cons_inv in Hp as (c2 & Hs2 & _).
    destruct Hs1 as [Hs1 | Hs1]; [| cbn in Hs1; contradiction].
    destruct Hs2 as [Hs2 | Hs2]; [| cbn in Hs2; contradiction].
    cbn in Hs1, Hs2. destruct Hs1 as (s & Hs & _ & ->). destruct Hs2 as (s' & Hs' & Hf & _).
    unfold poqr_init in Hs. injection Hs as <-. injection Hs' as <-. cbn in Hf. discriminate Hf.
  Qed.

  Theorem POQueueRD_incomplete :
    PrefixView.wf Tinc /\ PrefixView.complete Tinc /\
    rel_lin (@PrefixView.sel FP) Tinc (semi_independent FP) (νQ positive) /\
    (forall c, ~ vf_path VF poqr_init Tinc c).
  Proof.
    split; [exact Tinc_wf |]. split; [exact Tinc_complete |]. split; [exact Tinc_rel_lin | exact Tinc_no_path_D].
  Qed.

  Corollary POQueueRD_not_complete_pres : ~ ViewLHL.complete_pres (νQ positive) VF poqr_init.
  Proof.
    intros Hc. destruct (Hc Tinc) as (c & Hp).
    - exists []. rewrite app_nil_r. split; [exact Tinc_wf |]. split; [exact Tinc_complete | exact Tinc_rel_lin].
    - exact (Tinc_no_path_D c Hp).
  Qed.

End WHWQTop.
