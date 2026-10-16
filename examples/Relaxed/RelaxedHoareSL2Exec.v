(** * RelaxedHoareSL2Exec: SB, LB, MP, single-writer and retry
      witnesses, and negatives, for the RLHL SeqLock (WRd)

    Task .3 of RLHL-seqlock ([.rocq-review/tasks/RLHL-seqlock.md],
    Addendum "Witnesses and negatives", which replaces §2.6; Addendum 2),
    with the follow-ups of the waves 2-3 review (M-23, m-55, m-60, m-61,
    m-62: Parts 5 and 6 and this header).  Built on
    [RelaxedHoareSL2Prog] (the module [M2w rc si tw], the register file
    [δS], the overlay specification [δF], [slRA], [slsi], the production
    lemmas and the execution tactics), which is not edited, and on
    [RelaxedHoareLog] (only [EIhlv] and [rlhl_complin_eihlv], for two
    corollaries of Part 5).  This file proves no RLHL triple for the
    SeqLock: the RLHL proof is tasks .4-.7, and the one result here that
    needs it ([lb2_not_trace_rd_of_rel_lin]) takes it as a hypothesis;
    that hypothesis is discharged in [RelaxedHoareSL2Read]
    ([lb2_not_trace_rd]).

    ** The writer, and what the weak data depend on (review M-23)

    WRd is a single-writer seqcount whose closing increment reuses the
    opening read (cached v, Boehm-style):
    [v <- rd Sq_i; wr Sq_i (v+1); wmb; wr Sx_i vx; wr Sy_i vy; wmb;
    wr Sq_i (v+2)].  It is NOT the Linux seqcount writer, which reloads
    [Sq_i] before its closing increment.  (RelaxedHoareSL2Prog's header
    and the comment on its [wnext] said "Linux-seqcount" in an earlier
    version; they now use this wording.)
    - The SB datum of Part 2 and the single-writer datum of Part 5 depend
      on the cached v.  On this underlay (a sequential register file, no
      store forwarding) the reloading writer has no SB execution.  This
      is argued (review M-23), not proved here.  The reload is a [DR]
      access at the location of [wr Sq_i (v+1)], so it follows that
      write; every [rmb] of a younger read of another instance on the
      same thread is ordered after the reload ([dto DR Rmb]).  So the
      final [rd Sq_j] of the read [R_j] that returns (0,0) follows
      [W_i]'s [wr Sq_i (v+1)], and, reading 0, it precedes [W_j]'s
      [wr Sq_j (v+1)]; symmetrically for [R_i]; this is a cycle.  The
      same argument removes the single-writer datum ([R_j] cannot respond
      before [wr Sq_i (v+1)], so [R_i] cannot return (0,0)).
    - The reload is an own read after an own write.  Reusing the opening
      read removes it, so the encoding emulates at the program level part
      of what store forwarding gives.
    - Nothing here claims that the reloading writer is SC.  Only the
      absence of SB (and of the single-writer datum) is argued for it,
      and that argument is not kernel-checked.

    ** Map

    - Part 1 (generic, over [F2 si]).
      - First-order projections [rval], [tev_isres], [tev_rval], [tev_h],
        [tev_op] (used instead of dependent injection on [ResEv]);
        [ev_inv]/[ev_res]/[evs_of] (the events of operation records);
        [occurs_in_ops]: an operation occurring in a trace whose events
        are those of a list of records is one of them.
      - Positions: [nth_in_inj], [before_idx].
      - Legality of [δF]: [seq_rd_cases] (a read returns the initial pair
        and follows no write of its instance, or returns the pair of an
        earlier write of its instance); [leg_read_before];
        [leg_write_before].
      - [rel_lin_four]: the common shape of the three negatives (four
        operations with distinct keys, two same-thread [rhb] edges).
    - Part 2 (store buffering, SB).  [sb2_trace_ij si i j t1 t2]: [t1]
      writes (1,1) into instance [i], then reads instance [j]; [t2]
      writes (1,1) into [j], then reads [i]; all invocations precede all
      responses; both reads return (0,0).  This is SB WITHOUT own reads
      (no thread reads the instance it writes), and it depends on the
      cached-v writer (above).  [sb2_trace si t1 t2] is the task's
      instance [i = 1], [j = 2].
      - [sb2_exec_rd_ij], [sb2_exec_rd] (the go/no-go item): the trace
        is in [MTraces (EI δS) (M2w rc si tw) (regs0, [])] and complete,
        for every [rc], [si], and every [tw] with [tw i = t1],
        [tw j = t2], [t1 ≠ t2], [i ≠ j].  The schedule is in the comment
        before [sb2_exec_rd_mtraces_ij]: after its write's [rd Sq_i],
        each read overtakes the rest of its own thread's pending write
        ([sb_blocking]: only ([rd Sq_i], [rmb]) is ordered); every
        crossing is checked by the kernel against [must_precede].
      - [sb2_rel_lin_ij], [sb2_rel_lin_gen], [sb2_rel_lin_slRA]: the SB
        trace is relaxed-linearizable under every [indep ⊇ slRA]
        ([t1 ≠ t2]; direct witness [R_j; R_i; W_i; W_j]; no [rhb] edge).
      - [sb2_not_rel_lin_ij], [sb2_not_rel_lin_gen], [sb2_not_rel_lin0]:
        it is not, under any [indep] that relaxes neither (W_i, R_j) nor
        (W_j, R_i), in particular ∅ (legality cycle, as
        [RelaxedHoareCounterXY.sb_not_rel_lin0]).
      - [sl2rd_no_rlhl2_gen], [sl2rd_no_rlhl2_empty]: universal
        negatives, [forall I R G, ~ RLHL2Hyps … (M2w rc si tw)
        ((regs0, []), []) (A0, [])] over [EIhl δS], for such [si] (in
        particular ∅) and every [tw] with two distinct writer threads;
        through [rlhl_complin_eihl] and [cc_rel_lin] (pattern
        [RelaxedHoareCounterXY.cxy0_no_rlhl2]).  [sb2_exec_rd_ij] holds
        for every overlay relation, so no re-signature is needed.  These
        two are kept unchanged; Part 5 supersedes them
        ([sl2rd_no_rlhl2_empty_any] has no hypothesis on [tw]).
    - Part 3 (load buffering, LB).  [lb2_trace si t1 t2] (plan §2.6
      shape): [t1] reads instance 1 and then writes (1,1) into instance
      2; [t2] reads instance 2 and then writes instance 1; both reads
      return (1,1).
      - [lb2_not_rel_lin_gen], [lb2_not_rel_lin]: not
        relaxed-linearizable under any [indep ⊆ slRA] (in particular
        [slRA]): [R_2 → W_1], [R_1 → W_2] are [rhb] edges; legality puts
        [W_1] before [R_1] and [W_2] before [R_2].
      - [lb2_rel_lin_slsi_gen], [lb2_rel_lin_slsi] (contrast, not asked
        by the task): relaxed-linearizable under every [indep ⊇ slsi]
        ([t1 ≠ t2]).
      - [lb2_not_trace_rd_of_rel_lin]: conditional in this file.  If
        every complete trace of [M2w rc slRA tw] is relaxed-linearizable
        under [slRA] (the [slRA] instance of the main theorem's
        corollary), then the LB trace is a trace of [M2w rc si tw] for no
        [si] ([RelaxedHoareResig.mtraces_resig_iff] moves the trace to
        [slRA]).  The hypothesis is discharged by
        [RelaxedHoareSL2Read.sl2_rel_lin] at [slRA]; the unconditional
        result is [RelaxedHoareSL2Read.lb2_not_trace_rd].
    - Part 4 (message passing, MP).  [mp_ops], [mp_shaped s]: the events
      of [s] are those of [W_1], [W_2] (writer [tw], (1,1)), [R_2]
      returning (1,1) and [R_1] returning (0,0) (reader [tr]), with
      distinct keys, [W_1] invoked before [W_2] and [R_2] before [R_1];
      any interleaving, repetitions allowed.
      - [mp2_not_rel_lin]: no MP-shaped trace is relaxed-linearizable
        under any [indep ⊆ slsi].
      - Non-vacuity: [mp2_trace] with [mp2_trace_shaped],
        [mp2_trace_complete].
    - Part 5 (one writer thread; reviews m-60, m-62).
      [sw_trace_ij si i j vx vy t1 t2]: [t1] writes [(vx, vy)] into
      instance [i], then reads instance [j], which returns (0,0) while
      the write is pending; then [t2] reads instance [i] and gets (0,0);
      the write responds last.  [sw_trace si t1 t2] is the instance
      [i = 1], [j = 2], (1,1).  The datum depends on the cached-v writer
      (above).
      - [sw_exec_mtraces_ij], [sw_exec_ij], [sw_exec], [sw_complete_ij],
        [sw_complete]: a complete module trace of [M2w rc si tw] over
        [EI δS], for every [rc], [si], [vx], [vy], [i ≠ j], and every
        [tw] with [tw i = t1 ≠ t2] (one writer thread suffices).
      - [sw_not_rel_lin_ij], [sw_not_rel_lin]: not relaxed-linearizable
        under any [indep] lacking [(fW i vx vy, fR j)], if
        [(vx, vy) ≠ (0, 0)]: [W_i → R_j] (same thread), [R_j → R_i]
        (real time), and legality puts [R_i] before [W_i].
      - [sw_rel_lin_ij], [sw_rel_lin_slRA]: relaxed-linearizable under
        every [indep] containing that pair ([t1 ≠ t2]), with witness
        [R_j; R_i; W_i].
      - Presentation-free negatives: [sl2rd_no_complin_pair],
        [sl2rd_no_complin_missing] (the per-pair table),
        [sl2rd_no_complin_empty]:
        [~ RCompLin (M2w rc si tw) (EI δS) (regs0, []) (EI δF) (A0, [])]
        for every [rc], every [tw], and every [si] lacking one [slRA]
        pair [(fW i vx vy, fR j)] with [(vx, vy) ≠ (0, 0)], in
        particular ∅; through [complin_ei_rel_lin] ([cc_rel_lin]).
      - Their corollaries over the two underlay presentations, universal
        in [I], [R], [G]: [sl2rd_no_rlhl2_pair],
        [sl2rd_no_rlhl2_empty_any] (over [EIhl δS], via
        [rlhl_complin_eihl]); [sl2rd_no_rlhl2v_pair],
        [sl2rd_no_rlhl2v_empty] (over [EIhlv δS], via
        [RelaxedHoareLog.rlhl_complin_eihlv]).
      - Generic: [rel_lin_ops] (a witness contains exactly the invoked
        operations of the list).
    - Part 6 (a reader that retries; review m-55).
      [retry_trace si t1 t2]: [t1 = tw 1] writes (1,1) into instance 1;
      [t2 ≠ t1] reads instance 1, overlapping with the write, and gets
      (1,1).
      - [retry_exec]: a module execution of [M2w rc si tw] over [EI δS]
        with overlay trace [retry_trace], in which [t2]'s underlay events
        are exactly two reader iterations
        ([underlay_of_thread t2 evs = rd_iter_evs … ++ rd_iter_evs …]).
        The first reads [Sq_1 = 1] (odd), the torn pair (1, 0), and
        [Sq_1 = 1], so it fails validation; the second reads 2, 1, 1, 2
        and returns (1,1).  The underlay conjunct is needed: a run without
        retry has the same overlay trace.
      - [retry_exec_mtraces], [retry_complete]; [retry_rel_lin],
        [retry_rel_lin_slRA]: relaxed-linearizable under every [indep]
        (no [rhb] edge), in particular [slRA].
    - Part 7 (trace-level facts cited elsewhere; reviews m-68, M-29).
      - [ov_trace si t], the trace of
        [RelaxedHoareSL2Prog.sl2_read_overtakes_write] ([ov_exec]):
        relaxed-linearizable under every relation ([ov_rel_lin]), in
        particular ∅ ([ov_rel_lin_empty]).
      - [sbo si t1 t2], store buffering WITH own reads at the SeqLock
        level: [t1] writes (1,1) into instance 1, reads it back as (1,1)
        and reads instance 2 as (0,0); [t2] symmetrically; all
        invocations precede all responses; complete ([sbo_complete]).
        [sbo_not_rel_lin]: not relaxed-linearizable under any [indep]
        contained in [slRA].  So the verified [slRA] contract excludes
        it; that the WRd module over this MCA underlay does not produce
        it is [RelaxedHoareSL2Read.sbo_not_trace_rd].

    ** Deviations from the task text

    - [sl2rd_no_rlhl2_empty] (task .3) carries the hypothesis
      [exists i j, tw i <> tw j] (two distinct writer threads), absent
      from the task's statement, because its route is the SB execution,
      which needs each of two threads to write one instance (the guard of
      [M2w] lets only [tw i] write instance [i]).  The hypothesis is not
      necessary: [sl2rd_no_rlhl2_empty_any] (Part 5) is the task's
      statement with no hypothesis on [tw], through the single-writer
      execution (review m-60).  An earlier version of this header said
      the single-writer negative was "not known to hold"; that is
      refuted.  [sl2rd_no_rlhl2_gen] and [sl2rd_no_rlhl2_empty] are kept
      unchanged.
    - The per-pair table of Part 5 covers the pairs [(fW i vx vy, fR j)]
      with [(vx, vy) ≠ (0, 0)].  For an [si] that lacks only pairs whose
      written value is (0,0), this file proves nothing.  In the
      single-writer shape such a write cannot be told apart from the
      initial state; a longer witness (a completed write of (1,1), then
      a write of (0,0) overtaken by the read) would be needed, and is not
      done here.
    - The SB execution and the SB trace results are also given for any
      two instances [i ≠ j] ([_ij]); the task's statements (instances 1
      and 2) are corollaries with unchanged names.
    - The traces of Parts 2-4 use distinct overlay handles 0..3 (the
      plan's [lb2_trace] uses 0, 1 per thread), Part 5 uses 0..2 and
      Part 6 uses 0..1, so the keys are distinct for every [t1], [t2]:
      the trace-level negatives need no thread hypothesis.  The positive
      results need [t1 ≠ t2].
    - [mp2_not_rel_lin] has no [PrefixView.complete] hypothesis (plan
      §2.6 has one): [rel_lin] itself requires every invoked operation
      to respond, so the statement is stronger.
    - [sb2_exec_rd] is stated with [MTraces] (an existential over module
      executions), not with an explicit underlay event list.  The
      outcome (0,0) for both reads forces at least one read to overtake
      the pending write of its own thread (the usual SB argument); in
      the execution constructed here both do (see the schedule).
      [retry_exec] does state the reader's underlay events, because there
      the overlay trace does not determine them.

    ** K / S / P / R

    - K (kernel): [Print Assumptions] (Rocq 9.3.0) on each of the 76
      [Lemma]/[Theorem]/[Corollary] declarations of this file: all are
      closed under the global context except nine, which use
      [Eqdep.Eq_rect_eq.eq_rect_eq] and [Classical_Prop.classic]:
      [sl2rd_no_rlhl2_gen], [sl2rd_no_rlhl2_empty],
      [sl2rd_no_complin_pair], [sl2rd_no_complin_missing],
      [sl2rd_no_complin_empty], [sl2rd_no_rlhl2_pair],
      [sl2rd_no_rlhl2_empty_any], [sl2rd_no_rlhl2v_pair],
      [sl2rd_no_rlhl2v_empty].  Both axioms are inherited from
      [RelaxedHoareCompLinSpec.cc_rel_lin] ([classic], [eq_rect_eq];
      directly or through [complin_ei_rel_lin]), and for the RLHL forms
      also from [RelaxedHoareCompLinSpec.rlhl_complin_eihl] or
      [RelaxedHoareLog.rlhl_complin_eihlv] ([classic]).  No proof in
      this file uses an axiom directly.  In particular the three module
      executions ([sb2_exec_rd_ij], [sw_exec_ij], [retry_exec]), all
      trace-level results (including Part 7: [ov_exec], [ov_rel_lin],
      [ov_rel_lin_empty], [sbo_complete], [sbo_not_rel_lin]) and
      [lb2_not_trace_rd_of_rel_lin] are closed.
    - S (statements): as listed in the map.  Scope:
      - the underlay is RelaxedHoareSL2Prog's sequential,
        multi-copy-atomic register file with ordering-only barriers
        ([E_S rc], [δS]); module traces are taken over the plain
        [EI δS] from [(regs0, [])], as in [MTraces];
      - the presentation-free negatives [sl2rd_no_complin_*] negate
        [RCompLin (M2w rc si tw) (EI δS) (regs0, []) (EI δF) (A0, [])],
        which is the body of RelaxedHoareSL2InvLog's
        [sl2rd_complin_target] (the citable correctness statement of task
        .7) at an [si] outside its domain [slRA ⊆ si].  The [EIhlv]
        negatives ([sl2rd_no_rlhl2v_*]) negate the [RLHL2Hyps] conjunct
        of SL2InvLog's [sl2rd_prov_target_v] (option B, the main
        theorem's presentation).  The [EIhl] negatives (Part 2's and
        [sl2rd_no_rlhl2_pair], [sl2rd_no_rlhl2_empty_any]) have the
        shape of RelaxedHoareSL2Prog's [sl2rd_target], which is
        superseded (review m-51) and is not the citable target;
      - Part 5 shows that the domain [slRA ⊆ si] of the targets cannot
        lose any one pair (for written values ≠ (0,0)), for every [rc]
        and [tw], independently of the presentation.  That [RCompLin]
        holds for every [si ⊇ slRA] is task .7, proved as
        [RelaxedHoareSL2Read.sl2_complin];
      - the traces use fixed values (1,1) and instances 1 and 2, except
        the general forms: SB for any [i ≠ j]; the single-writer trace
        for any [i ≠ j] and [(vx, vy)];
      - the RLHL negatives are universal in [I], [R], [G] but concern the
        one module [M2w rc si tw] and its initial states; the Part 2
        RLHL negatives need two distinct writer threads, the Part 5 ones
        hold for every [tw];
      - the SB and single-writer data depend on the cached-v writer
        (M-23, above).
    - P (paper): there is no SeqLock text in the main paper (plan §1).
      [slRA] has the shape of I_RA (trace.tex:96) with instances for
      locations.  The SB trace is store buffering without own reads
      (each thread writes one instance and reads the other), lifted to
      SeqLock calls; it has the shape of implex.tex:84 (ex:view-sb).  It
      is not the store-buffering-with-own-reads example of
      trace.tex:94-107 (store forwarding), which ordinary registers
      cannot explain under I_RA (:107).  The verified [slRA] contract is
      falsified under store forwarding: the SB-with-own-reads outcome
      ([sbo]) is not relaxed-linearizable under any relation contained in
      [slRA] ([sbo_not_rel_lin], kernel-checked at trace level; that
      x86-TSO and ARMv8 produce it is argued, not mechanized).  This is
      an MCA-only data point (review M-29).  The earlier anchors
      trace.tex:204/:207 were stale (those lines are now Flush/tensor
      text; review m-61).  implex.tex:3 and relatedwork.tex:32 say that
      RLHL can specify load buffering; this file shows that the [slRA]
      contract excludes LB ([lb2_not_rel_lin]) and, conditionally on
      task .7 (discharged: [RelaxedHoareSL2Read.lb2_not_trace_rd]), that
      the WRd module does not exhibit it.  So the WRd
      SeqLock is not an LB datum (consistent with RelaxedHoareSL2Prog's
      [lb_blocking] and the author decision RS-1).
    - R (reviewers): popl2027-reviews.md:215 ("No example verified on
      the COH model").  This file supplies witnesses and negatives only.
      Together with tasks .4-.7 they are meant to show that the verified
      contract [slRA] is exercised by the module (SB, the single-writer
      trace and the retry are module traces) and that it cannot be
      strengthened by dropping a pair (Part 5, presentation-free).
      Nothing here answers :212 or :309-316.  The SB datum is not the
      store-forwarding datum asked about by Review A (A:37-40), and the
      underlay is not RC11 (M-23, B-1).  For A:37-40 Part 7 is a negative
      datum only: the [slRA] contract does not carry over to an underlay
      with store forwarding ([sbo_not_rel_lin]), so nothing here is
      evidence about TSO, ARMv8 or oMCA (M-29). *)

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
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareRun.
Require Import models.simlin.RelaxedHoareResig.
Require Import models.view.PrefixView.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.RelaxedHoareSL2Prog.
Require Import models.simlin.RelaxedHoareLog.

Import ListNotations.

Module RelaxedHoareSL2Exec.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedHoareRun.
  Import RelaxedHoareSL2Prog.

  (** ** Part 1. Generic trace-level facts over [F2 si] *)

  Section F2Ops.
    Context {si : FOp -> FOp -> Prop}.
    Local Abbreviation F := (F2 si).
    Local Abbreviation OpF := (RelaxedTraceLin.Op F).
    Local Abbreviation sel := (@PrefixView.sel F).

    (** The value of a result, first-order (as [pairv]): [pairv o] is
        [rval (op_op o) (op_ret o)] by conversion. *)
    Definition rval (o : FOp) : far o -> nat * nat :=
      match o as o0 return far o0 -> nat * nat with
      | fR _ => fun r => r
      | fW _ _ _ => fun _ => (0, 0)
      end.

    Lemma rval_inj o (r r' : far o) : rval o r = rval o r' -> r = r'.
    Proof. destruct o; cbn; [destruct r, r'; reflexivity | intros H; exact H]. Qed.

    (** First-order projections of overlay events (they replace dependent
        injection on [ResEv], so no [eq_rect_eq] is needed). *)
    Definition tev_isres (e : ThreadEvent F) : bool :=
      match te_ev F e with ResEv _ _ _ => true | InvEv _ _ => false end.

    Definition tev_rval (e : ThreadEvent F) : nat * nat :=
      match te_ev F e with ResEv _ o r => rval o r | InvEv _ _ => (0, 0) end.

    Definition tev_h (e : ThreadEvent F) : nat := event_handle (te_ev F e).

    Definition tev_op (e : ThreadEvent F) : FOp := event_op (te_ev F e).

    (** The invocation and the response event of an operation record. *)
    Definition ev_inv (o : OpF) : ThreadEvent F :=
      Build_ThreadEvent (fst (RelaxedTraceLin.op_key o)) (@InvEv F (snd (RelaxedTraceLin.op_key o)) (RelaxedTraceLin.op_op o)).

    Definition ev_res (o : OpF) : ThreadEvent F :=
      Build_ThreadEvent (fst (RelaxedTraceLin.op_key o))
        (@ResEv F (snd (RelaxedTraceLin.op_key o)) (RelaxedTraceLin.op_op o) (RelaxedTraceLin.op_ret o)).

    (** The events of a list of operations. *)
    Definition evs_of (Os : list OpF) : list (ThreadEvent F) := flat_map (fun o => [ev_inv o; ev_res o]) Os.

    Lemma inv_at_in (s : list (ThreadEvent F)) i k op :
      RelaxedTraceLin.inv_at sel s i k op -> In (Build_ThreadEvent (fst k) (@InvEv F (snd k) op)) s.
    Proof. intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as Hs. subst x. exact (nth_error_In _ _ Hx). Qed.

    Lemma res_at_in (s : list (ThreadEvent F)) j k op (r : far op) :
      RelaxedTraceLin.res_at sel s j k op r -> In (Build_ThreadEvent (fst k) (@ResEv F (snd k) op r)) s.
    Proof. intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as Hs. subst x. exact (nth_error_In _ _ Hx). Qed.

    Lemma nodup_map_eq {A B : Type} (f : A -> B) (l : list A) a b :
      NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
    Proof.
      induction l as [| x l IH]; [intros _ [] |]. cbn. intros Hnd Ha Hb Hf. inversion Hnd as [| y l' Hnin Hnd']; subst.
      destruct Ha as [-> | Ha], Hb as [-> | Hb]; [reflexivity | | | exact (IH Hnd' Ha Hb Hf)].
      - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hb.
      - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Ha.
    Qed.

    (** An operation that occurs in a trace whose events all come from a
        list of operations is one of them (its response event fixes its
        key, operation and result). *)
    Lemma occurs_in_ops (s : list (ThreadEvent F)) (Os : list OpF) (o : OpF) :
      (forall e, In e s -> In e (evs_of Os)) -> RelaxedTraceLin.occurs sel s o -> In o Os.
    Proof.
      intros Hsub [_ (j & Hj)]. apply res_at_in, Hsub in Hj.
      unfold evs_of in Hj. apply in_flat_map in Hj as (o2 & Ho2 & Hj).
      destruct Hj as [Hj | [Hj | []]]; [exfalso; apply (f_equal tev_isres) in Hj; discriminate Hj |].
      assert (Ht2 := f_equal (te_tid F) Hj). assert (Hh2 := f_equal tev_h Hj). assert (Ho2' := f_equal tev_op Hj).
      assert (Hr2 := f_equal tev_rval Hj). clear Hj.
      destruct o as [[t h] op r], o2 as [[t2 h2] op2 r2].
      cbn in Ht2, Hh2, Ho2', Hr2. subst t2 h2 op2.
      apply rval_inj in Hr2. subst r2. exact Ho2.
    Qed.

    (** Positions in a sequential witness. *)
    Lemma nth_in_inj {A : Type} (W : list A) i j a :
      NoDup W -> nth_error W i = Some a -> nth_error W j = Some a -> i = j.
    Proof.
      intros Hnd Hi Hj. apply (proj1 (NoDup_nth_error W) Hnd); [apply nth_error_Some; rewrite Hi; discriminate |].
      rewrite Hi, Hj. reflexivity.
    Qed.

    Lemma before_idx {A : Type} (W : list A) a b i j :
      NoDup W -> RelaxedTraceLin.before W a b -> nth_error W i = Some a -> nth_error W j = Some b -> i < j.
    Proof.
      intros Hnd (l1 & l2 & -> & Hb) Hi Hj.
      assert (Ha : nth_error (l1 ++ a :: l2) (length l1) = Some a)
        by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
      rewrite (nth_in_inj _ i (length l1) a Hnd Hi Ha).
      destruct (In_nth_error _ _ Hb) as (j' & Hj').
      assert (Hb' : nth_error (l1 ++ a :: l2) (length l1 + S j') = Some b).
      { rewrite nth_error_app2 by lia. replace (length l1 + S j' - length l1) with (S j') by lia. exact Hj'. }
      rewrite (nth_in_inj _ j (length l1 + S j') b Hnd Hj Hb'). lia.
    Qed.

    (** *** Legality of the sequential specification [δF] *)

    (** A read at position [p] of a legal run returns either the initial
        pair (and no write of its instance precedes it), or the pair of an
        earlier write of its instance. *)
    Lemma seq_rd_cases (A : AS) (W : list OpF) A' p o i :
      RelaxedHoareSpec.seq_run (F := F) δF A W A' -> nth_error W p = Some o -> RelaxedTraceLin.op_op o = fR i ->
      (pairv o = A i /\
       forall q oq vx vy, q < p -> nth_error W q = Some oq -> RelaxedTraceLin.op_op oq <> fW i vx vy) \/
      (exists q oq vx vy, q < p /\ nth_error W q = Some oq /\ RelaxedTraceLin.op_op oq = fW i vx vy /\
                          pairv o = (vx, vy)).
    Proof.
      intros Hrun. revert p. induction Hrun as [A | A o0 A1 W A2 Hd Hrun IH]; intros p Hp Hop;
        [destruct p; discriminate Hp |].
      destruct p as [| p]; cbn in Hp.
      - injection Hp as Ho. subst o0. left. destruct o as [k op r]. cbn in Hop, Hd |- *. subst op. cbn in Hd.
        destruct Hd as [-> _]. split; [reflexivity | intros q oq vx vy Hq; lia].
      - destruct (IH p Hp Hop) as [[Hv Hno] | (q & oq & vx & vy & Hq & Hnq & Hoq & Hv)].
        + destruct o0 as [k op r]. destruct op as [j wx wy | j]; cbn in Hd.
          * subst A1. destruct (Nat.eq_dec j i) as [-> | Hji].
            -- right. exists 0, (@RelaxedTraceLin.Build_Op F k (fW i wx wy) r), wx, wy.
               split; [lia |]. split; [reflexivity |]. split; [reflexivity |].
               rewrite Hv. unfold Aupd. rewrite Nat.eqb_refl. reflexivity.
            -- left. split.
               ++ rewrite Hv. unfold Aupd. apply Nat.eqb_neq in Hji. rewrite Hji. reflexivity.
               ++ intros q oq vx vy Hq Hnq. destruct q as [| q]; cbn in Hnq.
                  ** injection Hnq as <-. cbn. intros H. injection H as H. congruence.
                  ** apply (Hno q); [lia | exact Hnq].
          * destruct Hd as [_ ->]. left. split; [exact Hv |].
            intros q oq vx vy Hq Hnq. destruct q as [| q]; cbn in Hnq.
            -- injection Hnq as <-. cbn. discriminate.
            -- apply (Hno q); [lia | exact Hnq].
        + right. exists (S q), oq, vx, vy. split; [lia |]. split; [exact Hnq |]. split; assumption.
    Qed.

    (** A read whose value no write of its instance in the run writes
        precedes every such write. *)
    Lemma leg_read_before A (W : list OpF) A' p q oR oW i vx vy :
      RelaxedHoareSpec.seq_run (F := F) δF A W A' -> nth_error W p = Some oR -> nth_error W q = Some oW ->
      RelaxedTraceLin.op_op oR = fR i -> RelaxedTraceLin.op_op oW = fW i vx vy ->
      (forall o ux uy, In o W -> RelaxedTraceLin.op_op o = fW i ux uy -> pairv oR <> (ux, uy)) -> p < q.
    Proof.
      intros Hrun Hp Hq HoR HoW Hval.
      destruct (seq_rd_cases A W A' p oR i Hrun Hp HoR) as [[_ Hno] | (q' & oq & ux & uy & _ & Hq' & Hoq & Hv)].
      - destruct (Nat.lt_trichotomy p q) as [H | [H | H]]; [exact H | | ].
        + subst q. rewrite Hp in Hq. injection Hq as ->. rewrite HoR in HoW. discriminate HoW.
        + exfalso. exact (Hno q oW vx vy H Hq HoW).
      - exfalso. exact (Hval oq ux uy (nth_error_In _ _ Hq') Hoq Hv).
    Qed.

    (** A read whose value is not the initial one follows a write of its
        instance; if that write is unique, it follows that write. *)
    Lemma leg_write_before A (W : list OpF) A' p q oR oW i :
      NoDup W -> RelaxedHoareSpec.seq_run (F := F) δF A W A' -> nth_error W p = Some oR -> nth_error W q = Some oW ->
      RelaxedTraceLin.op_op oR = fR i -> pairv oR <> A i ->
      (forall o ux uy, In o W -> RelaxedTraceLin.op_op o = fW i ux uy -> o = oW) -> q < p.
    Proof.
      intros Hnd Hrun Hp Hq HoR Hne Hw.
      destruct (seq_rd_cases A W A' p oR i Hrun Hp HoR) as [[Hv _] | (q' & oq & ux & uy & Hlt & Hq' & Hoq & _)].
      - contradiction.
      - pose proof (Hw oq ux uy (nth_error_In _ _ Hq') Hoq) as ->.
        rewrite (nth_in_inj W q q' oW Hnd Hq Hq'). exact Hlt.
    Qed.

    (** *** The four-operation cycle

        Every negative below has the same shape: a trace whose events are
        those of four operations [oa], [ob], [oc], [od] with distinct
        keys, two same-thread invocation orders [oa → ob] and [oc → od]
        that [indep] does not relax (two [rhb] edges), and two legality
        constraints.  This lemma extracts from a relaxed-linearizability
        witness the facts the legality argument needs. *)
    Lemma rel_lin_four (s : list (ThreadEvent F)) indep (nu : list OpF -> Prop) (oa ob oc od : OpF) ia ib ic idd :
      NoDup (map (@RelaxedTraceLin.op_key F) [oa; ob; oc; od]) -> (forall e, In e s -> In e (evs_of [oa; ob; oc; od])) ->
      RelaxedTraceLin.inv_at sel s ia (RelaxedTraceLin.op_key oa) (RelaxedTraceLin.op_op oa) ->
      RelaxedTraceLin.inv_at sel s ib (RelaxedTraceLin.op_key ob) (RelaxedTraceLin.op_op ob) ->
      RelaxedTraceLin.inv_at sel s ic (RelaxedTraceLin.op_key oc) (RelaxedTraceLin.op_op oc) ->
      RelaxedTraceLin.inv_at sel s idd (RelaxedTraceLin.op_key od) (RelaxedTraceLin.op_op od) ->
      fst (RelaxedTraceLin.op_key oa) = fst (RelaxedTraceLin.op_key ob) -> ia < ib ->
      ~ indep (RelaxedTraceLin.op_op oa) (RelaxedTraceLin.op_op ob) ->
      fst (RelaxedTraceLin.op_key oc) = fst (RelaxedTraceLin.op_key od) -> ic < idd ->
      ~ indep (RelaxedTraceLin.op_op oc) (RelaxedTraceLin.op_op od) ->
      RelaxedTraceLin.rel_lin sel s indep nu ->
      exists W, nu W /\ NoDup W /\ (forall o, In o W -> In o [oa; ob; oc; od]) /\
        In oa W /\ In ob W /\ In oc W /\ In od W /\ RelaxedTraceLin.before W oa ob /\ RelaxedTraceLin.before W oc od.
    Proof.
      intros Hnd Hsub Ia Ib Ic Id Hab Hiab Hnab Hcd Hicd Hncd (W & Hnu & HndW & Hocc & Hall & Hord).
      assert (HW : forall o, In o W -> In o [oa; ob; oc; od])
        by (intros o Ho; exact (occurs_in_ops s _ o Hsub (Hocc o Ho))).
      assert (Hin : forall x i, In x [oa; ob; oc; od] ->
                      RelaxedTraceLin.inv_at sel s i (RelaxedTraceLin.op_key x) (RelaxedTraceLin.op_op x) -> In x W).
      { intros x i Hx Hi. destruct (Hall _ _ _ Hi) as (o & Ho & Hk).
        assert (o = x) as <- by exact (nodup_map_eq _ _ o x Hnd (HW o Ho) Hx Hk). exact Ho. }
      assert (Ha : In oa W) by (apply (Hin oa ia); [cbn; tauto | exact Ia]).
      assert (Hb : In ob W) by (apply (Hin ob ib); [cbn; tauto | exact Ib]).
      assert (Hc : In oc W) by (apply (Hin oc ic); [cbn; tauto | exact Ic]).
      assert (Hd : In od W) by (apply (Hin od idd); [cbn; tauto | exact Id]).
      exists W. split; [exact Hnu |]. split; [exact (NoDup_map_inv _ _ HndW) |]. split; [exact HW |].
      do 4 (split; [assumption |]). split.
      - apply Hord; [exact Ha | exact Hb |]. right. split; [exact Hab |]. exists ia, ib. auto.
      - apply Hord; [exact Hc | exact Hd |]. right. split; [exact Hcd |]. exists ic, idd. auto.
    Qed.
  End F2Ops.

  (** Membership in a concrete list of events. *)
  Local Ltac in_tac := cbn; solve [repeat (first [left; reflexivity | right])].

  (** Distinct keys of four concrete operations (distinct handles). *)
  Local Ltac nodup_keys := cbn; repeat constructor; cbn; let H := fresh in intros H;
    repeat (destruct H as [H | H]; [discriminate H |]); exact H.

  (** ** Part 2. Store buffering (SB) *)

  (** The SB trace over two instances [i ≠ j]: [t1] writes (1,1) into
      instance [i] and then reads instance [j]; [t2] writes (1,1) into
      instance [j] and then reads instance [i]; all four invocations
      precede all responses; both reads return (0,0).  Overlay handles
      0..3 are distinct, so the keys are distinct even if [t1 = t2].
      The task's trace is the instance [i = 1], [j = 2] ([sb2_trace]). *)
  Definition sb2_trace_ij (si : FOp -> FOp -> Prop) (i j : nat) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
    [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW i 1 1)); Build_ThreadEvent t1 (@InvEv (F2 si) 1 (fR j));
     Build_ThreadEvent t2 (@InvEv (F2 si) 2 (fW j 1 1)); Build_ThreadEvent t2 (@InvEv (F2 si) 3 (fR i));
     Build_ThreadEvent t1 (@ResEv (F2 si) 1 (fR j) (0, 0)); Build_ThreadEvent t2 (@ResEv (F2 si) 3 (fR i) (0, 0));
     Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW i 1 1) tt); Build_ThreadEvent t2 (@ResEv (F2 si) 2 (fW j 1 1) tt)].

  Definition sb2_trace (si : FOp -> FOp -> Prop) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
    sb2_trace_ij si 1 2 t1 t2.

  (** The four operations of the SB trace. *)
  Definition sbWt1 (si : FOp -> FOp -> Prop) (i : nat) (t1 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t1, 0) (fW i 1 1) tt.
  Definition sbRt1 (si : FOp -> FOp -> Prop) (j : nat) (t1 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t1, 1) (fR j) (0, 0).
  Definition sbWt2 (si : FOp -> FOp -> Prop) (j : nat) (t2 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t2, 2) (fW j 1 1) tt.
  Definition sbRt2 (si : FOp -> FOp -> Prop) (i : nat) (t2 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t2, 3) (fR i) (0, 0).

  (** [inv_here]/[find_idx] locate a concrete event of a concrete trace;
      [complete8] proves [PrefixView.complete] of an eight-event trace. *)
  Local Ltac inv_here := eexists; split; reflexivity.

  Local Ltac find_idx :=
    first [ solve [exists 0; inv_here] | solve [exists 1; inv_here] | solve [exists 2; inv_here]
          | solve [exists 3; inv_here] | solve [exists 4; inv_here] | solve [exists 5; inv_here]
          | solve [exists 6; inv_here] | solve [exists 7; inv_here] ].

  Local Ltac find_res :=
    first [ solve [exists 0; eexists; inv_here] | solve [exists 1; eexists; inv_here]
          | solve [exists 2; eexists; inv_here] | solve [exists 3; eexists; inv_here]
          | solve [exists 4; eexists; inv_here] | solve [exists 5; eexists; inv_here]
          | solve [exists 6; eexists; inv_here] | solve [exists 7; eexists; inv_here] ].

  Local Ltac complete8 :=
    let i := fresh "i" in let kt := fresh "kt" in let kh := fresh "kh" in let op := fresh "op" in
    let x := fresh "x" in let Hn := fresh "Hn" in let Hs := fresh "Hs" in
    intros i [kt kh] op (x & Hn & Hs);
    do 8 (destruct i as [| i];
            [ cbn in Hn; injection Hn as <-; unfold PrefixView.sel in Hs;
              first [ discriminate Hs | injection Hs as <- <- <-; find_res ]
            | ]);
    destruct i; cbn in Hn; discriminate Hn.

  Local Ltac inv_cases_tac i k :=
    let x := fresh "x" in let Hx := fresh "Hx" in let Hs := fresh "Hs" in
    let t := fresh "t" in let h := fresh "h" in
    let Ht := fresh "Ht" in let Hh := fresh "Hh" in let Ho := fresh "Ho" in
    intros (x & Hx & Hs); destruct k as [t h]; cbn [fst snd] in Hs;
    do 8 (destruct i as [| i]; [cbn in Hx; injection Hx as <-; cbn in Hs;
           first [discriminate Hs | injection Hs as Ht Hh Ho; subst; tauto] |]);
    destruct i; cbn in Hx; discriminate Hx.

  Local Ltac res_idx_tac j :=
    let x := fresh "x" in let Hx := fresh "Hx" in let Hs := fresh "Hs" in
    intros (x & Hx & Hs);
    repeat (destruct j as [| j]; [cbn in Hx; injection Hx as <-; cbn in Hs; discriminate Hs |]); lia.

  Section SBTrace.
    Context (si : FOp -> FOp -> Prop) (i j : nat) (t1 t2 : tid).
    Local Abbreviation sel := (@PrefixView.sel (F2 si)).

    Lemma sb2_complete_ij : PrefixView.complete (sb2_trace_ij si i j t1 t2).
    Proof. complete8. Qed.

    Lemma sb2_sub_ij :
      forall e, In e (sb2_trace_ij si i j t1 t2) -> In e (evs_of [sbWt1 si i t1; sbRt1 si j t1; sbWt2 si j t2; sbRt2 si i t2]).
    Proof. intros e He. cbn in He. repeat (destruct He as [<- | He]; [in_tac |]). destruct He. Qed.

    Lemma sb2_inv_cases_ij n k op :
      RelaxedTraceLin.inv_at sel (sb2_trace_ij si i j t1 t2) n k op ->
      (n = 0 /\ k = (t1, 0) /\ op = fW i 1 1) \/ (n = 1 /\ k = (t1, 1) /\ op = fR j) \/
      (n = 2 /\ k = (t2, 2) /\ op = fW j 1 1) \/ (n = 3 /\ k = (t2, 3) /\ op = fR i).
    Proof. inv_cases_tac n k. Qed.

    Lemma sb2_res_idx_ij n k op (r : far op) : RelaxedTraceLin.res_at sel (sb2_trace_ij si i j t1 t2) n k op r -> 4 <= n.
    Proof. res_idx_tac n. Qed.

    (** Under any relation containing [slRA], with two distinct instances
        and two distinct threads, the SB trace has no [rhb] edge: every
        invocation precedes every response, and the two same-thread pairs
        are (W_i, R_j) and (W_j, R_i). *)
    Lemma sb2_no_rhb_ij indep :
      (forall o o', slRA o o' -> indep o o') -> i <> j -> t1 <> t2 ->
      forall o o', ~ RelaxedTraceLin.rhb sel (sb2_trace_ij si i j t1 t2) indep o o'.
    Proof.
      intros Hsub Hij Ht o o' [(n & m & Hn & Hm & Hnm) | (Hth & n & m & Hn & Hm & Hnm & Hni)].
      - apply sb2_res_idx_ij in Hn.
        destruct (sb2_inv_cases_ij _ _ _ Hm) as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]]; lia.
      - destruct (sb2_inv_cases_ij _ _ _ Hn) as [(-> & Hk & Ho) | [(-> & Hk & Ho) | [(-> & Hk & Ho) | (-> & Hk & Ho)]]];
        destruct (sb2_inv_cases_ij _ _ _ Hm) as [(-> & Hk' & Ho') | [(-> & Hk' & Ho') | [(-> & Hk' & Ho') | (-> & Hk' & Ho')]]];
        try lia; rewrite Hk, Hk' in Hth; cbn in Hth;
        first [ exact (Ht Hth) | exact (Ht (eq_sym Hth)) | apply Hni, Hsub; rewrite Ho, Ho'; cbn; lia ].
    Qed.
  End SBTrace.

  (** *** The module execution (go/no-go item of task .3)

      Underlay handles: [t1]'s write 0..6, [t1]'s read 10..15, [t2]'s
      write 20..26, [t2]'s read 30..35.  The four overlay invocations
      come first, so the queue is [t1]'s write of instance [i] (14
      events), [t1]'s read of instance [j] (12), [t2]'s write of
      instance [j] (14), [t2]'s read of instance [i] (12).  The schedule:
      - [t1]'s [rd Sq_i] (invocation, response) at the head of the queue;
      - [t2]'s [rd Sq_j], each event crossing the 24 queued events of
        [t1] (other thread);
      - [t1]'s read of instance [j], each event crossing the 12 remaining
        events of [t1]'s write.  Same thread: by [sb_blocking] the only
        ordered pair between a WRd write of instance [i] and a read of
        instance [j ≠ i] is ([rd Sq_i], [rmb]), and [rd Sq_i] is already
        emitted; an invocation and a response of different calls are
        never ordered (F1 needs the same handle); the read is untagged
        (F3).  It reads [Sq_j = 0], [Sx_j = 0], [Sy_j = 0], [Sq_j = 0]
        and returns (0,0);
      - [t2]'s read of instance [i], each event crossing [t1]'s 12
        remaining write events (other thread) and [t2]'s 12 remaining
        write events (same thread, [sb_blocking] again); it returns
        (0,0);
      - the two writes complete in program order.
      Every crossing is discharged against
      [RelaxedModuleSemantics.must_precede] by [cross_ok_ij], the
      [cross_ok] of RelaxedHoareSL2Prog with one extra case: a
      same-kind pair of locations of instances [i] and [j] is decided by
      the hypotheses [(i =? j) = false], [(j =? i) = false]
      (kernel-checked; nothing is assumed). *)
  Local Ltac fresh_call := cbn; let H := fresh in intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.

  Local Ltac fresh_used Hk Hu :=
    cbn [map app] in Hu; untag_rw_in Hu; cbn in Hk, Hu;
    repeat (destruct Hk as [<- | Hk]; [repeat (destruct Hu as [Hu | Hu]; [discriminate Hu |]); exact Hu |]); exact Hk.

  Local Ltac res0 rc := ei_res (@nil (RelaxedTraceLin.Op (E_S rc))).

  Local Ltac sindep_ok_ij Eij Eji :=
    let Hn := fresh "Hn" in
    intros Hn; apply Hn; unfold sindep; cbn; rewrite ?Eij, ?Eji; cbn;
    solve [reflexivity | match goal with r : bool |- _ => destruct r; reflexivity end].

  Local Ltac cross_ok_ij Eij Eji :=
    first
      [ left; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn; first [discriminate | assumption | congruence]
      | right; split; [cbn [RelaxedModuleSemantics.ts_event]; untag_rw; reflexivity |];
        unfold RelaxedModuleSemantics.must_precede; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn;
        first
          [ solve [discriminate]
          | solve [let H := fresh in intros H; exact H]
          | solve [sindep_ok]
          | solve [sindep_ok_ij Eij Eji]
          | solve [match goal with Hd : forall q, ~ tev_deps ?m q |- ~ tev_deps ?m _ => apply Hd end] ] ].

  Local Ltac m_next_ij Eij Eji := apply RelaxedModuleSemantics.tagged_select_next; [cross_ok_ij Eij Eji |].

  Theorem sb2_exec_rd_mtraces_ij rc si tw i j t1 t2 :
    i <> j -> t1 <> t2 -> tw i = t1 -> tw j = t2 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
      (sb2_trace_ij si i j t1 t2).
  Proof.
    intros Hij Ht12 Htw1 Htw2.
    assert (Eij : Nat.eqb i j = false) by (apply Nat.eqb_neq; exact Hij).
    assert (Eji : Nat.eqb j i = false) by (apply Nat.eqb_neq; congruence).
    destruct (wr_guard_prod rc si tw t1 i 0 0 1 1 Htw1) as (trw1 & Hpw1 & Hmw1 & _).
    destruct (rd_prod rc si t1 j 10 0 0 0 eq_refl) as (trr1 & Hpr1 & Hmr1 & Hdr1).
    destruct (wr_guard_prod rc si tw t2 j 20 0 1 1 Htw2) as (trw2 & Hpw2 & Hmw2 & _).
    destruct (rd_prod rc si t2 i 30 0 0 0 eq_refl) as (trr2 & Hpr2 & Hmr2 & Hdr2).
    destruct trw1 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 trw1]]]]]]]]]]]]]]];
      try discriminate Hmw1.
    pose proof Hmw1 as Hmw1'. injection Hmw1' as V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13.
    destruct trr1 as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 [|r9 [|r10 [|r11 [|r12 trr1]]]]]]]]]]]]];
      try discriminate Hmr1.
    pose proof Hmr1 as Hmr1'. injection Hmr1' as R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11.
    destruct trw2 as [|u0 [|u1 [|u2 [|u3 [|u4 [|u5 [|u6 [|u7 [|u8 [|u9 [|u10 [|u11 [|u12 [|u13 [|u14 trw2]]]]]]]]]]]]]]];
      try discriminate Hmw2.
    pose proof Hmw2 as Hmw2'. injection Hmw2' as U0 U1 U2 U3 U4 U5 U6 U7 U8 U9 U10 U11 U12 U13.
    destruct trr2 as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 [|x10 [|x11 [|x12 trr2]]]]]]]]]]]]];
      try discriminate Hmr2.
    pose proof Hmr2 as Hmr2'. injection Hmr2' as X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11.
    unpack_forall Hdr1. unpack_forall Hdr2.
    do 2 eexists. split.
    - (* the four invocations *)
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t1) (h := 0); [intros [] | exact Hpw1 |].
        rewrite Hmw1. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t1) (h := 1); [fresh_call | exact Hpr1 |].
        rewrite Hmr1. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. fresh_used Hk Hu. }
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t2) (h := 2); [fresh_call | exact Hpw2 |].
        rewrite Hmw2. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. fresh_used Hk Hu. }
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t2) (h := 3); [fresh_call | exact Hpr2 |].
        rewrite Hmr2. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. fresh_used Hk Hu. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      (* t1's rd Sq_i *)
      m_step (sk si t1 0) w0 m_here ei_inv. m_step (sk si t1 0) w1 m_here ltac:(res0 rc).
      (* t2's rd Sq_j, past t1's 24 queued events *)
      m_step (sk si t2 2) u0 ltac:(do 24 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 2) u1 ltac:(do 24 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      (* t1's read of instance j overtakes the rest of t1's write *)
      m_step (sk si t1 1) r0 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r1 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r2 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r3 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r4 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r5 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r6 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r7 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r8 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r9 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r10 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r11 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_return (fR j).
      (* t2's read of instance i overtakes t1's write and the rest of t2's write *)
      m_step (sk si t2 3) x0 ltac:(do 24 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 3) x1 ltac:(do 24 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 3) x2 ltac:(do 24 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 3) x3 ltac:(do 24 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 3) x4 ltac:(do 24 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 3) x5 ltac:(do 24 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 3) x6 ltac:(do 24 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 3) x7 ltac:(do 24 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 3) x8 ltac:(do 24 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 3) x9 ltac:(do 24 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 3) x10 ltac:(do 24 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 3) x11 ltac:(do 24 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_return (fR i).
      (* the writes complete *)
      m_step (sk si t1 0) w2 m_here ei_inv. m_step (sk si t1 0) w3 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w4 m_here ei_inv. m_step (sk si t1 0) w5 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w6 m_here ei_inv. m_step (sk si t1 0) w7 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w8 m_here ei_inv. m_step (sk si t1 0) w9 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w10 m_here ei_inv. m_step (sk si t1 0) w11 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w12 m_here ei_inv. m_step (sk si t1 0) w13 m_here ltac:(res0 rc).
      m_return (fW i 1 1).
      m_step (sk si t2 2) u2 m_here ei_inv. m_step (sk si t2 2) u3 m_here ltac:(res0 rc).
      m_step (sk si t2 2) u4 m_here ei_inv. m_step (sk si t2 2) u5 m_here ltac:(res0 rc).
      m_step (sk si t2 2) u6 m_here ei_inv. m_step (sk si t2 2) u7 m_here ltac:(res0 rc).
      m_step (sk si t2 2) u8 m_here ei_inv. m_step (sk si t2 2) u9 m_here ltac:(res0 rc).
      m_step (sk si t2 2) u10 m_here ei_inv. m_step (sk si t2 2) u11 m_here ltac:(res0 rc).
      m_step (sk si t2 2) u12 m_here ei_inv. m_step (sk si t2 2) u13 m_here ltac:(res0 rc).
      m_return (fW j 1 1).
      apply RelaxedModuleSemantics.tagged_module_execution_refl.
    - reflexivity.
  Qed.

  (** A complete SB execution of the guarded WRd module over the plain
      sequential register file, for every [rc], every overlay relation
      [si], every two instances [i ≠ j] and every writer map [tw] whose
      writer threads [tw i = t1], [tw j = t2] differ.

      M-23: this is SB WITHOUT own reads, and it depends on the WRd
      writer being a single-writer seqcount whose closing increment
      reuses the opening read (cached v), not the Linux seqcount writer.
      A writer that reloads [Sq_i] before its closing write has no SB
      execution on this underlay (argued in review M-23 and in the file
      header; not proved here).  No claim is made that the reloading
      writer is SC. *)
  Theorem sb2_exec_rd_ij rc si tw i j t1 t2 :
    i <> j -> t1 <> t2 -> tw i = t1 -> tw j = t2 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
      (sb2_trace_ij si i j t1 t2) /\
    PrefixView.complete (sb2_trace_ij si i j t1 t2).
  Proof.
    intros Hij Ht12 Htw1 Htw2.
    split; [exact (sb2_exec_rd_mtraces_ij rc si tw i j t1 t2 Hij Ht12 Htw1 Htw2) | apply sb2_complete_ij].
  Qed.

  (** The go/no-go item, as stated by task .3: instances 1 and 2,
      [tw 1 = t1], [tw 2 = t2], [t1 ≠ t2].  SB without own reads, for the
      cached-v writer only (M-23; see [sb2_exec_rd_ij]). *)
  Theorem sb2_exec_rd rc si tw t1 t2 :
    t1 <> t2 -> tw 1 = t1 -> tw 2 = t2 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) (sb2_trace si t1 t2) /\
    PrefixView.complete (sb2_trace si t1 t2).
  Proof. intros Ht12 Htw1 Htw2. exact (sb2_exec_rd_ij rc si tw 1 2 t1 t2 ltac:(lia) Ht12 Htw1 Htw2). Qed.

  (** *** SB is relaxed-linearizable under [slRA] (direct witness) *)

  (** The witness [R_j (0,0); R_i (0,0); W_i; W_j]: legal, and the trace
      has no [rhb] edge ([sb2_no_rhb_ij]).  For every relation [indep]
      that contains [slRA] (so for every [si ⊇ slRA] of the main
      theorem), with distinct instances and distinct threads (with
      [t1 = t2] the same-instance pair (W_i, R_i) would be an [rhb]
      edge). *)
  Theorem sb2_rel_lin_ij si indep i j t1 t2 :
    (forall o o', slRA o o' -> indep o o') -> i <> j -> t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sb2_trace_ij si i j t1 t2) indep
      (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hsub Hij Ht. exists [sbRt1 si j t1; sbRt2 si i t2; sbWt1 si i t1; sbWt2 si j t2].
    assert (Eji : Nat.eqb j i = false) by (apply Nat.eqb_neq; congruence).
    split; [| split; [| split; [| split]]].
    - eexists. econstructor; [split; reflexivity |]. econstructor; [split; reflexivity |].
      econstructor; [reflexivity |]. econstructor; [reflexivity |]. constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [split; [find_idx | find_res] |]). destruct Ho.
    - intros n k op Hn.
      destruct (sb2_inv_cases_ij si i j t1 t2 _ _ _ Hn) as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]];
        [exists (sbWt1 si i t1) | exists (sbRt1 si j t1) | exists (sbWt2 si j t2) | exists (sbRt2 si i t2)];
        (split; [in_tac | reflexivity]).
    - intros o o' _ _ Hr. exfalso. exact (sb2_no_rhb_ij si i j t1 t2 indep Hsub Hij Ht o o' Hr).
  Qed.

  Corollary sb2_rel_lin_gen si indep t1 t2 :
    (forall o o', slRA o o' -> indep o o') -> t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sb2_trace si t1 t2) indep
      (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof. intros Hsub Ht. exact (sb2_rel_lin_ij si indep 1 2 t1 t2 Hsub ltac:(lia) Ht). Qed.

  (** The task's [sb2_rel_lin_slRA]. *)
  Corollary sb2_rel_lin_slRA t1 t2 :
    t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 slRA)) (sb2_trace slRA t1 t2) slRA
      (RelaxedHoareSpec.seq_legal (F := F2 slRA) δF A0).
  Proof. intros Ht. exact (sb2_rel_lin_gen slRA slRA t1 t2 (fun _ _ H => H) Ht). Qed.

  (** *** SB is not relaxed-linearizable without the (W_i, R_j) pairs *)

  (** A legality cycle, as [RelaxedHoareCounterXY.sb_not_rel_lin0]: the
      two same-thread invocation orders [W_i → R_j] and [W_j → R_i] are
      [rhb] edges; legality puts [R_j] (which returns (0,0)) before [W_j]
      (the only write of instance [j], of (1,1)), and [R_i] before
      [W_i].  For every [t1], [t2] (the keys are distinct by their
      handles). *)
  Theorem sb2_not_rel_lin_ij si indep i j t1 t2 :
    i <> j -> ~ indep (fW i 1 1) (fR j) -> ~ indep (fW j 1 1) (fR i) ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sb2_trace_ij si i j t1 t2) indep
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hij Hn1 Hn2 Hrl.
    destruct (rel_lin_four (sb2_trace_ij si i j t1 t2) indep _ (sbWt1 si i t1) (sbRt1 si j t1) (sbWt2 si j t2)
                (sbRt2 si i t2) 0 1 2 3
                ltac:(nodup_keys) (sb2_sub_ij si i j t1 t2) ltac:(inv_here) ltac:(inv_here) ltac:(inv_here)
                ltac:(inv_here) eq_refl ltac:(lia) Hn1 eq_refl ltac:(lia) Hn2 Hrl)
      as (W & (A' & Hrun) & Hnd & HW & Ha & Hb & Hc & Hd & Hab & Hcd).
    destruct (In_nth_error _ _ Ha) as (ia & Hia). destruct (In_nth_error _ _ Hb) as (ib & Hib).
    destruct (In_nth_error _ _ Hc) as (ic & Hic). destruct (In_nth_error _ _ Hd) as (id' & Hid).
    pose proof (before_idx W _ _ _ _ Hnd Hab Hia Hib). pose proof (before_idx W _ _ _ _ Hnd Hcd Hic Hid).
    assert (ib < ic).
    { apply (leg_read_before A0 W A' ib ic (sbRt1 si j t1) (sbWt2 si j t2) j 1 1 Hrun Hib Hic eq_refl eq_refl).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | []]]]]; cbn in Hop;
        try discriminate Hop; injection Hop; intros; subst; first [exfalso; lia | cbn; discriminate]. }
    assert (id' < ia).
    { apply (leg_read_before A0 W A' id' ia (sbRt2 si i t2) (sbWt1 si i t1) i 1 1 Hrun Hid Hia eq_refl eq_refl).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | []]]]]; cbn in Hop;
        try discriminate Hop; injection Hop; intros; subst; first [exfalso; lia | cbn; discriminate]. }
    lia.
  Qed.

  Corollary sb2_not_rel_lin_gen si indep t1 t2 :
    ~ indep (fW 1 1 1) (fR 2) -> ~ indep (fW 2 1 1) (fR 1) ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sb2_trace si t1 t2) indep
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof. intros Hn1 Hn2. exact (sb2_not_rel_lin_ij si indep 1 2 t1 t2 ltac:(lia) Hn1 Hn2). Qed.

  (** The task's [sb2_not_rel_lin0]. *)
  Corollary sb2_not_rel_lin0 si t1 t2 :
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sb2_trace si t1 t2) (fun _ _ => False)
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof. apply sb2_not_rel_lin_gen; intros []. Qed.

  (** *** No RLHL proof of the WRd module without the (W_i, R_j) pairs *)

  (** The route of [RelaxedHoareCounterXY.cxy0_no_rlhl2]: [RLHL2Hyps]
      would give copy-cat inclusion over [EI δF] ([rlhl_complin_eihl]),
      hence relaxed linearizability under [si] of the complete trace of
      [sb2_exec_rd_ij] ([cc_rel_lin]), which [sb2_not_rel_lin_ij]
      refutes.  The module semantics reads only the underlay relation,
      and [sb2_exec_rd_ij] is proved for every overlay relation, so no
      re-signature ([mtraces_resig_iff]) is needed.  Hypothesis
      [tw i <> tw j]: two instances with distinct writer threads (the SB
      execution needs two writer threads; see the header).  The
      hypothesis is not needed for the negative itself: Part 5's
      [sl2rd_no_rlhl2_pair] goes through the single-writer execution.
      [classic] and [eq_rect_eq] enter through [rlhl_complin_eihl] and
      [cc_rel_lin]; this proof uses no axiom directly. *)
  Theorem sl2rd_no_rlhl2_gen rc si tw i j :
    tw i <> tw j -> ~ si (fW i 1 1) (fR j) -> ~ si (fW j 1 1) (fR i) ->
    forall (I : RelaxedHoareBase.Assn (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (RelaxedHoareSpec.EI (F := F2 si) δF))
           (R G : CallKey (F2 si) ->
                  RelaxedHoareBase.PRel (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (RelaxedHoareSpec.EI (F := F2 si) δF)),
      ~ RelaxedHoareBase.RLHL2Hyps
          (VE := RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
          I R G (M2w rc si tw) ((regs0, []), []) (A0, []).
  Proof.
    intros Htw Hn1 Hn2 I R G HH.
    assert (Hij : i <> j) by (intros ->; exact (Htw eq_refl)).
    pose proof (RelaxedHoareCompLinSpec.rlhl_complin_eihl (E := E_S rc) δS (F := F2 si) δF A0 I R G (M2w rc si tw)
                  (regs0, []) HH) as Hcc.
    destruct (sb2_exec_rd_ij rc si tw i j (tw i) (tw j) Hij Htw eq_refl eq_refl) as [Hm Hc].
    exact (sb2_not_rel_lin_ij si si i j (tw i) (tw j) Hij Hn1 Hn2
             (RelaxedHoareCompLinSpec.cc_rel_lin (F := F2 si) δF A0 _ (Hcc _ Hm) Hc)).
  Qed.

  (** The task's [sl2rd_no_rlhl2_empty]: at the empty overlay relation,
      for every writer map with at least two distinct writer threads.
      Superseded by [sl2rd_no_rlhl2_empty_any] (Part 5), which drops the
      hypothesis on [tw]; kept unchanged. *)
  Corollary sl2rd_no_rlhl2_empty rc tw :
    (exists i j, tw i <> tw j) ->
    forall (I : RelaxedHoareBase.Assn (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS)
                  (RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF))
           (R G : CallKey (F2 (fun _ _ => False)) ->
                  RelaxedHoareBase.PRel (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS)
                    (RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF)),
      ~ RelaxedHoareBase.RLHL2Hyps
          (VE := RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF)
          I R G (M2w rc (fun _ _ => False) tw) ((regs0, []), []) (A0, []).
  Proof. intros (i & j & Htw). apply (sl2rd_no_rlhl2_gen rc _ tw i j Htw); intros []. Qed.

  (** ** Part 3. Load buffering (LB) *)

  (** [before] in a concrete witness. *)
  Lemma before_here {A : Type} (a b : A) l : In b l -> RelaxedTraceLin.before (a :: l) a b.
  Proof. intros H. exists [], l. split; [reflexivity | exact H]. Qed.

  Lemma before_later {A : Type} (x a b : A) l : RelaxedTraceLin.before l a b -> RelaxedTraceLin.before (x :: l) a b.
  Proof. intros (l1 & l2 & -> & H). exists (x :: l1), l2. split; [reflexivity | exact H]. Qed.

  Local Ltac before_tac := solve [repeat (first [apply before_here; in_tac | apply before_later])].

  (** The four operations of the LB trace: [t1] reads instance 1 and then
      writes (1,1) into instance 2; [t2] reads instance 2 and then writes
      (1,1) into instance 1; both reads return (1,1).  (Plan §2.6 shape:
      [tw 1 = t2], [tw 2 = t1].) *)
  Definition lbR2 (si : FOp -> FOp -> Prop) (t2 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t2, 0) (fR 2) (1, 1).
  Definition lbW1 (si : FOp -> FOp -> Prop) (t2 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t2, 1) (fW 1 1 1) tt.
  Definition lbR1 (si : FOp -> FOp -> Prop) (t1 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t1, 2) (fR 1) (1, 1).
  Definition lbW2 (si : FOp -> FOp -> Prop) (t1 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t1, 3) (fW 2 1 1) tt.

  (** The plan's [lb2_trace] (§2.6), with distinct overlay handles 0..3:
      [t2] invokes its read of instance 2 and its write of instance 1;
      the write completes; [t1] reads instance 1 (1,1), then writes
      instance 2; finally [t2]'s read returns (1,1). *)
  Definition lb2_trace (si : FOp -> FOp -> Prop) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
    [Build_ThreadEvent t2 (@InvEv (F2 si) 0 (fR 2)); Build_ThreadEvent t2 (@InvEv (F2 si) 1 (fW 1 1 1));
     Build_ThreadEvent t2 (@ResEv (F2 si) 1 (fW 1 1 1) tt); Build_ThreadEvent t1 (@InvEv (F2 si) 2 (fR 1));
     Build_ThreadEvent t1 (@ResEv (F2 si) 2 (fR 1) (1, 1)); Build_ThreadEvent t1 (@InvEv (F2 si) 3 (fW 2 1 1));
     Build_ThreadEvent t1 (@ResEv (F2 si) 3 (fW 2 1 1) tt); Build_ThreadEvent t2 (@ResEv (F2 si) 0 (fR 2) (1, 1))].

  Section LBTrace.
    Context (si : FOp -> FOp -> Prop) (t1 t2 : tid).
    Local Abbreviation sel := (@PrefixView.sel (F2 si)).

    Lemma lb2_complete : PrefixView.complete (lb2_trace si t1 t2).
    Proof. complete8. Qed.

    Lemma lb2_sub : forall e, In e (lb2_trace si t1 t2) -> In e (evs_of [lbR2 si t2; lbW1 si t2; lbR1 si t1; lbW2 si t1]).
    Proof. intros e He. cbn in He. repeat (destruct He as [<- | He]; [in_tac |]). destruct He. Qed.

    Lemma lb2_inv_cases i k op :
      RelaxedTraceLin.inv_at sel (lb2_trace si t1 t2) i k op ->
      (i = 0 /\ k = (t2, 0) /\ op = fR 2) \/ (i = 1 /\ k = (t2, 1) /\ op = fW 1 1 1) \/
      (i = 3 /\ k = (t1, 2) /\ op = fR 1) \/ (i = 5 /\ k = (t1, 3) /\ op = fW 2 1 1).
    Proof. inv_cases_tac i k. Qed.

    Lemma lb2_res_cases j k op (r : far op) :
      RelaxedTraceLin.res_at sel (lb2_trace si t1 t2) j k op r ->
      (j = 2 /\ k = (t2, 1)) \/ (j = 4 /\ k = (t1, 2)) \/ (j = 6 /\ k = (t1, 3)) \/ (j = 7 /\ k = (t2, 0)).
    Proof.
      intros (x & Hx & Hs). destruct k as [t h]. cbn [fst snd] in Hs.
      do 8 (destruct j as [| j];
             [ cbn in Hx; injection Hx as <-; cbn in Hs;
               first [ discriminate Hs
                     | pose proof (f_equal (option_map (te_tid (F2 si))) Hs) as Ht;
                       pose proof (f_equal (option_map tev_h) Hs) as Hh; cbn in Ht, Hh;
                       injection Ht as <-; injection Hh as <-; tauto ]
             | ]).
      destruct j; cbn in Hx; discriminate Hx.
    Qed.
  End LBTrace.

  (** LB is not relaxed-linearizable when neither (R_2, W_1) nor
      (R_1, W_2) is relaxed: the same-thread invocation orders
      [R2 → W1] ([t2]) and [R1 → W2] ([t1]) are [rhb] edges; legality puts
      [W1] (the only write of instance 1) before [R1], which returns
      (1,1) ≠ [A0 1], and [W2] before [R2]: a cycle.  For every [t1],
      [t2]. *)
  Theorem lb2_not_rel_lin_gen si indep t1 t2 :
    ~ indep (fR 2) (fW 1 1 1) -> ~ indep (fR 1) (fW 2 1 1) ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (lb2_trace si t1 t2) indep
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hn1 Hn2 Hrl.
    destruct (rel_lin_four (lb2_trace si t1 t2) indep _ (lbR2 si t2) (lbW1 si t2) (lbR1 si t1) (lbW2 si t1) 0 1 3 5
                ltac:(nodup_keys) (lb2_sub si t1 t2) ltac:(inv_here) ltac:(inv_here) ltac:(inv_here) ltac:(inv_here)
                eq_refl ltac:(lia) Hn1 eq_refl ltac:(lia) Hn2 Hrl)
      as (W & (A' & Hrun) & Hnd & HW & Ha & Hb & Hc & Hd & Hab & Hcd).
    destruct (In_nth_error _ _ Ha) as (ia & Hia). destruct (In_nth_error _ _ Hb) as (ib & Hib).
    destruct (In_nth_error _ _ Hc) as (ic & Hic). destruct (In_nth_error _ _ Hd) as (id' & Hid).
    pose proof (before_idx W _ _ _ _ Hnd Hab Hia Hib). pose proof (before_idx W _ _ _ _ Hnd Hcd Hic Hid).
    assert (ib < ic).
    { apply (leg_write_before A0 W A' ic ib (lbR1 si t1) (lbW1 si t2) 1 Hnd Hrun Hic Hib eq_refl ltac:(cbn; discriminate)).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | []]]]]; cbn in Hop;
        first [reflexivity | discriminate Hop]. }
    assert (id' < ia).
    { apply (leg_write_before A0 W A' ia id' (lbR2 si t2) (lbW2 si t1) 2 Hnd Hrun Hia Hid eq_refl ltac:(cbn; discriminate)).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | []]]]]; cbn in Hop;
        first [reflexivity | discriminate Hop]. }
    lia.
  Qed.

  (** The task's [lb2_not_rel_lin]: under [slRA], and under every relation
      contained in [slRA] (no (R, W) pair is relaxed). *)
  Theorem lb2_not_rel_lin si indep t1 t2 :
    (forall o o', indep o o' -> slRA o o') ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (lb2_trace si t1 t2) indep
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof. intros Hsub. apply lb2_not_rel_lin_gen; intros H; exact (Hsub _ _ H). Qed.

  (** Contrast (not required by task .3): under every relation containing
      [slsi] (cross-instance (R, W) and (W, R) pairs), with distinct
      threads, LB is relaxed-linearizable, with witness
      [W1; R1; W2; R2].  So [lb2_not_rel_lin] is a property of the
      specification [slRA], not of the trace alone. *)
  Theorem lb2_rel_lin_slsi_gen si indep t1 t2 :
    (forall o o', slsi o o' -> indep o o') -> t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (lb2_trace si t1 t2) indep
      (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hsub Ht. exists [lbW1 si t2; lbR1 si t1; lbW2 si t1; lbR2 si t2].
    split; [| split; [| split; [| split]]].
    - eexists. econstructor; [reflexivity |]. econstructor; [split; reflexivity |].
      econstructor; [reflexivity |]. econstructor; [split; reflexivity |]. constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [split; [find_idx | find_res] |]). destruct Ho.
    - intros i k op Hi.
      destruct (lb2_inv_cases si t1 t2 _ _ _ Hi) as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]];
        [exists (lbR2 si t2) | exists (lbW1 si t2) | exists (lbR1 si t1) | exists (lbW2 si t1)];
        (split; [in_tac | reflexivity]).
    - intros o o' Ho Ho' Hr. cbn in Ho, Ho'.
      destruct Hr as [(i & j & Hi & Hj & Hij) | (Hth & i & j & Hi & Hj & Hij & Hn)].
      + destruct (lb2_res_cases si t1 t2 _ _ _ _ Hi) as [(-> & Hk) | [(-> & Hk) | [(-> & Hk) | (-> & Hk)]]];
        destruct (lb2_inv_cases si t1 t2 _ _ _ Hj) as [(-> & Hk' & _) | [(-> & Hk' & _) | [(-> & Hk' & _) | (-> & Hk' & _)]]];
        try lia;
        destruct Ho as [<- | [<- | [<- | [<- | []]]]]; cbn in Hk; try discriminate Hk;
        destruct Ho' as [<- | [<- | [<- | [<- | []]]]]; cbn in Hk'; try discriminate Hk';
        before_tac.
      + exfalso.
        destruct (lb2_inv_cases si t1 t2 _ _ _ Hi) as [(-> & Hk & Ho1) | [(-> & Hk & Ho1) | [(-> & Hk & Ho1) | (-> & Hk & Ho1)]]];
        destruct (lb2_inv_cases si t1 t2 _ _ _ Hj) as [(-> & Hk' & Ho2) | [(-> & Hk' & Ho2) | [(-> & Hk' & Ho2) | (-> & Hk' & Ho2)]]];
        try lia; rewrite Hk, Hk' in Hth; cbn in Hth;
        first [ exact (Ht Hth) | exact (Ht (eq_sym Hth)) | apply Hn, Hsub; rewrite Ho1, Ho2; cbn; lia ].
  Qed.

  Corollary lb2_rel_lin_slsi t1 t2 :
    t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 slsi)) (lb2_trace slsi t1 t2) slsi
      (RelaxedHoareSpec.seq_legal (F := F2 slsi) δF A0).
  Proof. intros Ht. exact (lb2_rel_lin_slsi_gen slsi slsi t1 t2 (fun _ _ H => H) Ht). Qed.

  (** *** LB is not a trace of the WRd module, conditionally (in this
      file) on the main theorem's [rel_lin] corollary

      The hypothesis [Hrl] is the [slRA] instance of the corollary of the
      main theorem: every complete trace of [M2w rc slRA tw] is
      relaxed-linearizable under [slRA].  Under it, the LB trace is a
      trace of [M2w rc si tw] for no overlay relation [si]: the module
      traces do not depend on [si] ([RelaxedHoareResig.mtraces_resig_iff]),
      and LB is not relaxed-linearizable under [slRA] ([lb2_not_rel_lin]).
      This result does not establish the hypothesis.  It is discharged by
      [RelaxedHoareSL2Read.sl2_rel_lin] (task .7); the unconditional
      result is [RelaxedHoareSL2Read.lb2_not_trace_rd]. *)
  Theorem lb2_not_trace_rd_of_rel_lin rc si tw t1 t2 :
    (forall s, RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc slRA tw) (regs0, []) s ->
       PrefixView.complete s ->
       RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 slRA)) s slRA (RelaxedHoareSpec.seq_legal (F := F2 slRA) δF A0)) ->
    ~ RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) (lb2_trace si t1 t2).
  Proof.
    intros Hrl Hm.
    pose proof (proj1 (RelaxedHoareResig.mtraces_resig_iff (F := F2 si) slRA (RelaxedHoareSpec.EI (F := E_S rc) δS)
                         (M2w rc si tw) (M2w rc slRA tw) (fun _ _ => eq_refl) (regs0, []) (lb2_trace si t1 t2)) Hm) as Hm'.
    change (map (RelaxedHoareResig.ev_resig (F := F2 si) slRA) (lb2_trace si t1 t2)) with (lb2_trace slRA t1 t2) in Hm'.
    exact (lb2_not_rel_lin slRA slRA t1 t2 (fun _ _ H => H) (Hrl _ Hm' (lb2_complete slRA t1 t2))).
  Qed.

  (** ** Part 4. Message passing (MP) *)

  (** The four operations of an MP trace: a writer thread [tw] writes
      (1,1) into instance 1 and then into instance 2; a reader thread [tr]
      reads instance 2, getting (1,1), and then instance 1, getting
      (0,0). *)
  Definition mp_ops (si : FOp -> FOp -> Prop) (tw tr : tid) (hw1 hw2 hr2 hr1 : nat) : list (RelaxedTraceLin.Op (F2 si)) :=
    [@RelaxedTraceLin.Build_Op (F2 si) (tw, hw1) (fW 1 1 1) tt; @RelaxedTraceLin.Build_Op (F2 si) (tw, hw2) (fW 2 1 1) tt;
     @RelaxedTraceLin.Build_Op (F2 si) (tr, hr2) (fR 2) (1, 1); @RelaxedTraceLin.Build_Op (F2 si) (tr, hr1) (fR 1) (0, 0)].

  (** [mp_shaped s]: the events of [s] are those of an MP operation set
      with distinct keys (each event may occur at any position, so this
      is uniform in the interleaving; repetitions are allowed), the
      writer invokes [W1] before [W2] and the reader invokes [R2] before
      [R1]. *)
  Definition mp_shaped {si : FOp -> FOp -> Prop} (s : list (ThreadEvent (F2 si))) : Prop :=
    exists tw tr hw1 hw2 hr2 hr1 i1 i2 j2 j1,
      NoDup (map (@RelaxedTraceLin.op_key (F2 si)) (mp_ops si tw tr hw1 hw2 hr2 hr1)) /\
      (forall e, In e s -> In e (evs_of (mp_ops si tw tr hw1 hw2 hr2 hr1))) /\
      i1 < i2 /\ RelaxedTraceLin.inv_at (@PrefixView.sel (F2 si)) s i1 (tw, hw1) (fW 1 1 1) /\
      RelaxedTraceLin.inv_at (@PrefixView.sel (F2 si)) s i2 (tw, hw2) (fW 2 1 1) /\
      j2 < j1 /\ RelaxedTraceLin.inv_at (@PrefixView.sel (F2 si)) s j2 (tr, hr2) (fR 2) /\
      RelaxedTraceLin.inv_at (@PrefixView.sel (F2 si)) s j1 (tr, hr1) (fR 1).

  (** No MP-shaped trace is relaxed-linearizable under any relation
      contained in [slsi] (same-instance-kind pairs (W, W) and (R, R) are
      never relaxed): [W1 → W2] and [R2 → R1] are [rhb] edges; legality
      puts [W2] (the only write of instance 2) before [R2], which returns
      (1,1) ≠ [A0 2], and [R1], which returns (0,0), before [W1] (the
      only write of instance 1, of (1,1)).  No completeness hypothesis is
      needed: [rel_lin] already requires every invoked operation to
      respond. *)
  Theorem mp2_not_rel_lin si indep (s : list (ThreadEvent (F2 si))) :
    (forall o o', indep o o' -> slsi o o') -> mp_shaped s ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) s indep (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hsub (tw & tr & hw1 & hw2 & hr2 & hr1 & i1 & i2 & j2 & j1 & Hk & Hs & H12 & I1 & I2 & H21 & J2 & J1) Hrl.
    destruct (rel_lin_four s indep _ (@RelaxedTraceLin.Build_Op (F2 si) (tw, hw1) (fW 1 1 1) tt)
                (@RelaxedTraceLin.Build_Op (F2 si) (tw, hw2) (fW 2 1 1) tt)
                (@RelaxedTraceLin.Build_Op (F2 si) (tr, hr2) (fR 2) (1, 1))
                (@RelaxedTraceLin.Build_Op (F2 si) (tr, hr1) (fR 1) (0, 0)) i1 i2 j2 j1
                Hk Hs I1 I2 J2 J1 eq_refl H12 (fun H => Hsub _ _ H) eq_refl H21 (fun H => Hsub _ _ H) Hrl)
      as (W & (A' & Hrun) & Hnd & HW & Ha & Hb & Hc & Hd & Hab & Hcd).
    destruct (In_nth_error _ _ Ha) as (ia & Hia). destruct (In_nth_error _ _ Hb) as (ib & Hib).
    destruct (In_nth_error _ _ Hc) as (ic & Hic). destruct (In_nth_error _ _ Hd) as (id' & Hid).
    pose proof (before_idx W _ _ _ _ Hnd Hab Hia Hib). pose proof (before_idx W _ _ _ _ Hnd Hcd Hic Hid).
    assert (ib < ic).
    { apply (leg_write_before A0 W A' ic ib _ _ 2 Hnd Hrun Hic Hib eq_refl ltac:(cbn; discriminate)).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | []]]]]; cbn in Hop;
        first [reflexivity | discriminate Hop]. }
    assert (id' < ia).
    { apply (leg_read_before A0 W A' id' ia _ _ 1 1 1 Hrun Hid Hia eq_refl eq_refl).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | []]]]]; cbn in Hop;
        try discriminate Hop; injection Hop as <- <-; cbn; discriminate. }
    lia.
  Qed.

  (** Non-vacuity of [mp_shaped]: a concrete MP trace (writer [tw],
      reader [tr], any threads). *)
  Definition mp2_trace (si : FOp -> FOp -> Prop) (tw tr : tid) : list (ThreadEvent (F2 si)) :=
    [Build_ThreadEvent tw (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent tw (@ResEv (F2 si) 0 (fW 1 1 1) tt);
     Build_ThreadEvent tw (@InvEv (F2 si) 1 (fW 2 1 1)); Build_ThreadEvent tw (@ResEv (F2 si) 1 (fW 2 1 1) tt);
     Build_ThreadEvent tr (@InvEv (F2 si) 2 (fR 2)); Build_ThreadEvent tr (@ResEv (F2 si) 2 (fR 2) (1, 1));
     Build_ThreadEvent tr (@InvEv (F2 si) 3 (fR 1)); Build_ThreadEvent tr (@ResEv (F2 si) 3 (fR 1) (0, 0))].

  Lemma mp2_trace_shaped si tw tr : mp_shaped (mp2_trace si tw tr).
  Proof.
    exists tw, tr, 0, 1, 2, 3, 0, 2, 4, 6. split; [nodup_keys |]. split.
    - intros e He. cbn in He. repeat (destruct He as [<- | He]; [in_tac |]). destruct He.
    - repeat split; first [lia | inv_here].
  Qed.

  Lemma mp2_trace_complete si tw tr : PrefixView.complete (mp2_trace si tw tr).
  Proof. complete8. Qed.


  (** ** Part 5. A single-writer witness: the ∅ negative for every writer
      map, and the per-pair si table (reviews m-60, m-62)

      [sw_trace_ij si i j vx vy t1 t2]: [t1] writes [(vx, vy)] into
      instance [i] and then reads instance [j]; the read returns (0,0)
      while the write is pending; then [t2] reads instance [i] and gets
      (0,0); the write responds last.  Overlay handles 0, 1, 2 (distinct
      keys for every [t1], [t2]).  One writer thread suffices: [t1] is the
      only writer, and the observation is made by [t2]'s read through
      real time ([R_j] responds before [R_i] is invoked).  The cycle under
      a relation that does not relax (W_i, R_j): [W_i → R_j] (same-thread
      [rhb]), [R_j → R_i] (real time), and legality puts [R_i] (which
      returns (0,0) ≠ (vx,vy)) before [W_i], the only write of instance
      [i].

      M-23: this datum depends on the cached-v WRd writer exactly as the
      SB datum does.  With a writer that reloads [Sq_i] before its closing
      write, the reload (a [DR], after [wr Sq_i (v+1)] at the same
      location) blocks [R_j]'s [rmb]s ([dto DR Rmb]), so [R_j] cannot
      respond before [wr Sq_i (v+1)] and [R_i] cannot return (0,0)
      (argued in review M-23; no theorem here). *)
  Definition sw_trace_ij (si : FOp -> FOp -> Prop) (i j vx vy : nat) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
    [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW i vx vy)); Build_ThreadEvent t1 (@InvEv (F2 si) 1 (fR j));
     Build_ThreadEvent t1 (@ResEv (F2 si) 1 (fR j) (0, 0)); Build_ThreadEvent t2 (@InvEv (F2 si) 2 (fR i));
     Build_ThreadEvent t2 (@ResEv (F2 si) 2 (fR i) (0, 0)); Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW i vx vy) tt)].

  (** The instance of the review's script: instances 1 and 2, values (1,1). *)
  Definition sw_trace (si : FOp -> FOp -> Prop) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
    sw_trace_ij si 1 2 1 1 t1 t2.

  (** The three operations of the single-writer trace. *)
  Definition swW (si : FOp -> FOp -> Prop) (i vx vy : nat) (t1 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t1, 0) (fW i vx vy) tt.
  Definition swRj (si : FOp -> FOp -> Prop) (j : nat) (t1 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t1, 1) (fR j) (0, 0).
  Definition swRi (si : FOp -> FOp -> Prop) (i : nat) (t2 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t2, 2) (fR i) (0, 0).

  (** Variants of [complete8], [inv_cases_tac] for traces of [n] events
      ([injection] fails on [None = Some _], so the count must be exact). *)
  Local Tactic Notation "complete_n" int_or_var(n) :=
    let i := fresh "i" in let kt := fresh "kt" in let kh := fresh "kh" in let op := fresh "op" in
    let x := fresh "x" in let Hn := fresh "Hn" in let Hs := fresh "Hs" in
    intros i [kt kh] op (x & Hn & Hs);
    do n (destruct i as [| i];
            [ cbn in Hn; injection Hn as <-; unfold PrefixView.sel in Hs;
              first [ discriminate Hs | injection Hs as <- <- <-; find_res ]
            | ]);
    destruct i; cbn in Hn; discriminate Hn.

  Local Tactic Notation "inv_cases_n" int_or_var(n) ident(i) ident(k) :=
    let x := fresh "x" in let Hx := fresh "Hx" in let Hs := fresh "Hs" in
    let t := fresh "t" in let h := fresh "h" in
    let Ht := fresh "Ht" in let Hh := fresh "Hh" in let Ho := fresh "Ho" in
    intros (x & Hx & Hs); destruct k as [t h]; cbn [fst snd] in Hs;
    do n (destruct i as [| i]; [cbn in Hx; injection Hx as <-; cbn in Hs;
           first [discriminate Hs | injection Hs as Ht Hh Ho; subst; tauto] |]);
    destruct i; cbn in Hx; discriminate Hx.

  Local Tactic Notation "res_cases_n" int_or_var(n) constr(F) ident(j) :=
    let x := fresh "x" in let Hx := fresh "Hx" in let Hs := fresh "Hs" in
    let Ht := fresh "Ht" in let Hh := fresh "Hh" in
    intros (x & Hx & Hs);
    do n (destruct j as [| j];
           [ cbn in Hx; injection Hx as <-; cbn in Hs;
             first [ discriminate Hs
                   | pose proof (f_equal (option_map (te_tid F)) Hs) as Ht;
                     pose proof (f_equal (option_map tev_h) Hs) as Hh; cbn in Ht, Hh;
                     injection Ht as <-; injection Hh as <-; tauto ]
           | ]);
    destruct j; cbn in Hx; discriminate Hx.

  (** A relaxed-linearizability witness of a trace whose events are those
      of a list of operations with distinct keys contains exactly the
      invoked operations of the list (the generic part of [rel_lin_four]). *)
  Section F2OpsGen.
    Context {si : FOp -> FOp -> Prop}.
    Local Abbreviation F := (F2 si).
    Local Abbreviation OpF := (RelaxedTraceLin.Op F).
    Local Abbreviation sel := (@PrefixView.sel F).

    Lemma rel_lin_ops (s : list (ThreadEvent F)) indep (nu : list OpF -> Prop) (Os : list OpF) :
      NoDup (map (@RelaxedTraceLin.op_key F) Os) -> (forall e, In e s -> In e (evs_of Os)) ->
      RelaxedTraceLin.rel_lin sel s indep nu ->
      exists W, nu W /\ NoDup W /\ (forall o, In o W -> In o Os) /\
        (forall o n, In o Os -> RelaxedTraceLin.inv_at sel s n (RelaxedTraceLin.op_key o) (RelaxedTraceLin.op_op o) ->
                     In o W) /\
        (forall o o', In o W -> In o' W -> RelaxedTraceLin.rhb sel s indep o o' -> RelaxedTraceLin.before W o o').
    Proof.
      intros Hnd Hsub (W & Hnu & HndW & Hocc & Hall & Hord).
      assert (HW : forall o, In o W -> In o Os) by (intros o Ho; exact (occurs_in_ops s _ o Hsub (Hocc o Ho))).
      exists W. split; [exact Hnu |]. split; [exact (NoDup_map_inv _ _ HndW) |]. split; [exact HW |].
      split; [| exact Hord].
      intros x n Hx Hn. destruct (Hall _ _ _ Hn) as (o & Ho & Hk).
      assert (o = x) as <- by exact (nodup_map_eq _ _ o x Hnd (HW o Ho) Hx Hk). exact Ho.
    Qed.
  End F2OpsGen.

  Section SWTrace.
    Context (si : FOp -> FOp -> Prop) (i j vx vy : nat) (t1 t2 : tid).
    Local Abbreviation sel := (@PrefixView.sel (F2 si)).

    Lemma sw_complete_ij : PrefixView.complete (sw_trace_ij si i j vx vy t1 t2).
    Proof. complete_n 6. Qed.

    Lemma sw_sub_ij :
      forall e, In e (sw_trace_ij si i j vx vy t1 t2) -> In e (evs_of [swW si i vx vy t1; swRj si j t1; swRi si i t2]).
    Proof. intros e He. cbn in He. repeat (destruct He as [<- | He]; [in_tac |]). destruct He. Qed.

    Lemma sw_inv_cases_ij n k op :
      RelaxedTraceLin.inv_at sel (sw_trace_ij si i j vx vy t1 t2) n k op ->
      (n = 0 /\ k = (t1, 0) /\ op = fW i vx vy) \/ (n = 1 /\ k = (t1, 1) /\ op = fR j) \/
      (n = 3 /\ k = (t2, 2) /\ op = fR i).
    Proof. inv_cases_n 6 n k. Qed.

    Lemma sw_res_cases_ij n k op (r : far op) :
      RelaxedTraceLin.res_at sel (sw_trace_ij si i j vx vy t1 t2) n k op r ->
      (n = 2 /\ k = (t1, 1)) \/ (n = 4 /\ k = (t2, 2)) \/ (n = 5 /\ k = (t1, 0)).
    Proof. destruct k as [t h]. cbn [fst snd]. res_cases_n 6 (F2 si) n. Qed.
  End SWTrace.

  (** *** The module execution

      Underlay handles: [t1]'s write 0..6, [t1]'s read 10..15, [t2]'s read
      20..25.  The schedule:
      - [t1]'s write and read are invoked; [t1]'s [rd Sq_i] (invocation,
        response) at the head of the queue;
      - [t1]'s read of instance [j]: each event crosses the 12 remaining
        events of [t1]'s write (same thread; [sb_blocking]: the only
        ordered pair is ([rd Sq_i], [rmb]), already emitted); it reads
        [Sq_j = Sx_j = Sy_j = 0] and returns (0,0);
      - [t2]'s read of instance [i] is invoked; each event crosses the 12
        remaining events of [t1]'s write (other thread); [Sq_i] is still
        0, so it reads 0, 0, 0, 0 and returns (0,0);
      - [t1]'s write completes.
      Every crossing is checked by the kernel against [must_precede]
      ([cross_ok_ij]). *)
  Theorem sw_exec_mtraces_ij rc si tw i j vx vy t1 t2 :
    i <> j -> t1 <> t2 -> tw i = t1 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
      (sw_trace_ij si i j vx vy t1 t2).
  Proof.
    intros Hij Ht12 Htw1.
    assert (Eij : Nat.eqb i j = false) by (apply Nat.eqb_neq; exact Hij).
    assert (Eji : Nat.eqb j i = false) by (apply Nat.eqb_neq; congruence).
    destruct (wr_guard_prod rc si tw t1 i 0 0 vx vy Htw1) as (trw1 & Hpw1 & Hmw1 & _).
    destruct (rd_prod rc si t1 j 10 0 0 0 eq_refl) as (trr1 & Hpr1 & Hmr1 & Hdr1).
    destruct (rd_prod rc si t2 i 20 0 0 0 eq_refl) as (trr2 & Hpr2 & Hmr2 & Hdr2).
    destruct trw1 as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 trw1]]]]]]]]]]]]]]];
      try discriminate Hmw1.
    pose proof Hmw1 as Hmw1'. injection Hmw1' as V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13.
    destruct trr1 as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 [|r9 [|r10 [|r11 [|r12 trr1]]]]]]]]]]]]];
      try discriminate Hmr1.
    pose proof Hmr1 as Hmr1'. injection Hmr1' as R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11.
    destruct trr2 as [|x0 [|x1 [|x2 [|x3 [|x4 [|x5 [|x6 [|x7 [|x8 [|x9 [|x10 [|x11 [|x12 trr2]]]]]]]]]]]]];
      try discriminate Hmr2.
    pose proof Hmr2 as Hmr2'. injection Hmr2' as X0 X1 X2 X3 X4 X5 X6 X7 X8 X9 X10 X11.
    unpack_forall Hdr1. unpack_forall Hdr2.
    do 2 eexists. split.
    - eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t1) (h := 0); [intros [] | exact Hpw1 |].
        rewrite Hmw1. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t1) (h := 1); [fresh_call | exact Hpr1 |].
        rewrite Hmr1. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. fresh_used Hk Hu. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      (* t1's rd Sq_i *)
      m_step (sk si t1 0) w0 m_here ei_inv. m_step (sk si t1 0) w1 m_here ltac:(res0 rc).
      (* t1's read of instance j overtakes the rest of t1's write *)
      m_step (sk si t1 1) r0 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r1 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r2 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r3 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r4 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r5 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r6 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r7 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r8 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r9 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t1 1) r10 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t1 1) r11 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_return (fR j).
      (* t2's read of instance i, after R_j's response, overtakes t1's pending write *)
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t2) (h := 2); [fresh_call | exact Hpr2 |].
        rewrite Hmr2. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. fresh_used Hk Hu. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      m_step (sk si t2 2) x0 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 2) x1 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 2) x2 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 2) x3 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 2) x4 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 2) x5 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 2) x6 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 2) x7 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 2) x8 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 2) x9 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_step (sk si t2 2) x10 ltac:(do 12 (m_next_ij Eij Eji); m_here) ei_inv.
      m_step (sk si t2 2) x11 ltac:(do 12 (m_next_ij Eij Eji); m_here) ltac:(res0 rc).
      m_return (fR i).
      (* t1's write completes *)
      m_step (sk si t1 0) w2 m_here ei_inv. m_step (sk si t1 0) w3 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w4 m_here ei_inv. m_step (sk si t1 0) w5 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w6 m_here ei_inv. m_step (sk si t1 0) w7 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w8 m_here ei_inv. m_step (sk si t1 0) w9 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w10 m_here ei_inv. m_step (sk si t1 0) w11 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w12 m_here ei_inv. m_step (sk si t1 0) w13 m_here ltac:(res0 rc).
      m_return (fW i vx vy).
      apply RelaxedModuleSemantics.tagged_module_execution_refl.
    - reflexivity.
  Qed.

  (** A complete single-writer execution of the guarded WRd module over
      the plain sequential register file, for every [rc], [si], [vx],
      [vy], every two instances [i ≠ j], every writer map [tw] with
      [tw i = t1], and every reader thread [t2 ≠ t1]. *)
  Theorem sw_exec_ij rc si tw i j vx vy t1 t2 :
    i <> j -> t1 <> t2 -> tw i = t1 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
      (sw_trace_ij si i j vx vy t1 t2) /\
    PrefixView.complete (sw_trace_ij si i j vx vy t1 t2).
  Proof.
    intros Hij Ht12 Htw1.
    split; [exact (sw_exec_mtraces_ij rc si tw i j vx vy t1 t2 Hij Ht12 Htw1) | apply sw_complete_ij].
  Qed.

  (** The review's [sw_exec]: instances 1 and 2, values (1,1),
      [tw 1 = t1 ≠ t2]. *)
  Theorem sw_exec rc si tw t1 t2 :
    t1 <> t2 -> tw 1 = t1 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) (sw_trace si t1 t2).
  Proof. intros Ht12 Htw1. exact (sw_exec_mtraces_ij rc si tw 1 2 1 1 t1 t2 ltac:(lia) Ht12 Htw1). Qed.

  Lemma sw_complete si t1 t2 : PrefixView.complete (sw_trace si t1 t2).
  Proof. apply sw_complete_ij. Qed.

  (** *** The single-writer trace and the overlay relation *)

  (** Not relaxed-linearizable under any [indep] that does not relax
      [(fW i vx vy, fR j)], provided [(vx, vy) ≠ (0, 0)]: for every
      [i], [j], [t1], [t2]. *)
  Theorem sw_not_rel_lin_ij si indep i j vx vy t1 t2 :
    (vx, vy) <> (0, 0) -> ~ indep (fW i vx vy) (fR j) ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sw_trace_ij si i j vx vy t1 t2) indep
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hv Hn Hrl.
    destruct (rel_lin_ops (sw_trace_ij si i j vx vy t1 t2) indep _ [swW si i vx vy t1; swRj si j t1; swRi si i t2]
                ltac:(nodup_keys) (sw_sub_ij si i j vx vy t1 t2) Hrl)
      as (W & (A' & Hrun) & Hnd & HW & Hin & Hord).
    assert (Ha : In (swW si i vx vy t1) W) by (apply (Hin _ 0); [in_tac | inv_here]).
    assert (Hb : In (swRj si j t1) W) by (apply (Hin _ 1); [in_tac | inv_here]).
    assert (Hc : In (swRi si i t2) W) by (apply (Hin _ 3); [in_tac | inv_here]).
    assert (Hab : RelaxedTraceLin.before W (swW si i vx vy t1) (swRj si j t1)).
    { apply Hord; [exact Ha | exact Hb |]. right. split; [reflexivity |].
      exists 0, 1. split; [inv_here |]. split; [inv_here |]. split; [lia | exact Hn]. }
    assert (Hbc : RelaxedTraceLin.before W (swRj si j t1) (swRi si i t2)).
    { apply Hord; [exact Hb | exact Hc |]. left. exists 2, 3. split; [inv_here |]. split; [inv_here | lia]. }
    destruct (In_nth_error _ _ Ha) as (ia & Hia). destruct (In_nth_error _ _ Hb) as (ib & Hib).
    destruct (In_nth_error _ _ Hc) as (ic & Hic).
    pose proof (before_idx W _ _ _ _ Hnd Hab Hia Hib). pose proof (before_idx W _ _ _ _ Hnd Hbc Hib Hic).
    assert (ic < ia).
    { apply (leg_read_before A0 W A' ic ia (swRi si i t2) (swW si i vx vy t1) i vx vy Hrun Hic Hia eq_refl eq_refl).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | []]]]; cbn in Hop; try discriminate Hop.
      injection Hop; intros; subst. cbn. intros Heq. exact (Hv (eq_sym Heq)). }
    lia.
  Qed.

  (** The review's [sw_not_rel_lin]. *)
  Corollary sw_not_rel_lin si indep t1 t2 :
    ~ indep (fW 1 1 1) (fR 2) ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sw_trace si t1 t2) indep
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof. intros Hn. exact (sw_not_rel_lin_ij si indep 1 2 1 1 t1 t2 ltac:(discriminate) Hn). Qed.

  (** Relaxed-linearizable under every [indep] that relaxes
      [(fW i vx vy, fR j)], with distinct threads: witness
      [R_j; R_i; W_i] (the only [rhb] edge is [R_j → R_i]). *)
  Theorem sw_rel_lin_ij si indep i j vx vy t1 t2 :
    indep (fW i vx vy) (fR j) -> t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sw_trace_ij si i j vx vy t1 t2) indep
      (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hsi Ht. exists [swRj si j t1; swRi si i t2; swW si i vx vy t1].
    split; [| split; [| split; [| split]]].
    - eexists. econstructor; [split; reflexivity |]. econstructor; [split; reflexivity |].
      econstructor; [reflexivity |]. constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [split; [find_idx | find_res] |]). destruct Ho.
    - intros n k op Hn.
      destruct (sw_inv_cases_ij si i j vx vy t1 t2 _ _ _ Hn) as [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]];
        [exists (swW si i vx vy t1) | exists (swRj si j t1) | exists (swRi si i t2)];
        (split; [in_tac | reflexivity]).
    - intros o o' Ho Ho' Hr. cbn in Ho, Ho'.
      destruct Hr as [(n & m & Hn & Hm & Hnm) | (Hth & n & m & Hn & Hm & Hnm & Hni)].
      + destruct (sw_res_cases_ij si i j vx vy t1 t2 _ _ _ _ Hn) as [(-> & Hk) | [(-> & Hk) | (-> & Hk)]];
        destruct (sw_inv_cases_ij si i j vx vy t1 t2 _ _ _ Hm) as [(-> & Hk' & _) | [(-> & Hk' & _) | (-> & Hk' & _)]];
        try lia;
        destruct Ho as [<- | [<- | [<- | []]]]; cbn in Hk; try discriminate Hk;
        destruct Ho' as [<- | [<- | [<- | []]]]; cbn in Hk'; try discriminate Hk';
        before_tac.
      + exfalso.
        destruct (sw_inv_cases_ij si i j vx vy t1 t2 _ _ _ Hn) as [(-> & Hk & Ho1) | [(-> & Hk & Ho1) | (-> & Hk & Ho1)]];
        destruct (sw_inv_cases_ij si i j vx vy t1 t2 _ _ _ Hm) as [(-> & Hk' & Ho2) | [(-> & Hk' & Ho2) | (-> & Hk' & Ho2)]];
        try lia; rewrite Hk, Hk' in Hth; cbn in Hth;
        first [ exact (Ht Hth) | exact (Ht (eq_sym Hth)) | apply Hni; rewrite Ho1, Ho2; exact Hsi ].
  Qed.

  (** The review's [slRA] witness (order [R_j; R_i; W_i]). *)
  Corollary sw_rel_lin_slRA t1 t2 :
    t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 slRA)) (sw_trace slRA t1 t2) slRA
      (RelaxedHoareSpec.seq_legal (F := F2 slRA) δF A0).
  Proof. intros Ht. apply (sw_rel_lin_ij slRA slRA 1 2 1 1 t1 t2); [cbn; lia | exact Ht]. Qed.

  (** *** Presentation-free negatives: no copy-cat inclusion (review m-62)

      [RCompLin (M2w rc si tw) (EI δS) (regs0, []) (EI δF) (A0, [])] is
      the body of RelaxedHoareSL2InvLog's [sl2rd_complin_target] at
      [(rc, si, tw)], the paper-facing correctness statement of task .7.
      It fails for every [si] that lacks one [slRA] pair
      [(fW i vx vy, fR j)] with [(vx, vy) ≠ (0, 0)], for every [rc] and
      every writer map [tw]: the single-writer execution with
      [t1 = tw i] and [t2 = Pos.succ (tw i)] is a complete module trace
      ([sw_exec_ij]); copy-cat inclusion would make it relaxed-
      linearizable under [si] ([complin_ei_rel_lin], i.e. [cc_rel_lin]),
      which [sw_not_rel_lin_ij] refutes.  [classic] and [eq_rect_eq]
      enter through [cc_rel_lin]; this proof uses no axiom directly.  No
      presentation of the underlay ([EIhl], [EIhlv]) appears. *)
  Theorem sl2rd_no_complin_pair rc si tw i j vx vy :
    i <> j -> (vx, vy) <> (0, 0) -> ~ si (fW i vx vy) (fR j) ->
    ~ RelaxedHoareCompLin.RCompLin (M2w rc si tw) (RelaxedHoareSpec.EI (F := E_S rc) δS) (regs0, [])
        (RelaxedHoareSpec.EI (F := F2 si) δF) (A0, []).
  Proof.
    intros Hij Hv Hn HC.
    destruct (sw_exec_ij rc si tw i j vx vy (tw i) (Pos.succ (tw i)) Hij (Pos.succ_discr (tw i)) eq_refl) as [Hm Hc].
    exact (sw_not_rel_lin_ij si si i j vx vy (tw i) (Pos.succ (tw i)) Hv Hn
             (RelaxedHoareCompLinSpec.complin_ei_rel_lin (F := F2 si) δF A0 (M2w rc si tw)
                (RelaxedHoareSpec.EI (F := E_S rc) δS) (regs0, []) HC _ Hm Hc)).
  Qed.

  (** The per-pair table: every [si] missing one [slRA] pair with a
      non-initial written pair fails. *)
  Corollary sl2rd_no_complin_missing rc si tw :
    (exists i vx vy j, slRA (fW i vx vy) (fR j) /\ (vx, vy) <> (0, 0) /\ ~ si (fW i vx vy) (fR j)) ->
    ~ RelaxedHoareCompLin.RCompLin (M2w rc si tw) (RelaxedHoareSpec.EI (F := E_S rc) δS) (regs0, [])
        (RelaxedHoareSpec.EI (F := F2 si) δF) (A0, []).
  Proof. intros (i & vx & vy & j & Hra & Hv & Hn). exact (sl2rd_no_complin_pair rc si tw i j vx vy Hra Hv Hn). Qed.

  (** At the empty overlay relation, for every [rc] and every writer map. *)
  Corollary sl2rd_no_complin_empty rc tw :
    ~ RelaxedHoareCompLin.RCompLin (M2w rc (fun _ _ => False) tw) (RelaxedHoareSpec.EI (F := E_S rc) δS) (regs0, [])
        (RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF) (A0, []).
  Proof. exact (sl2rd_no_complin_pair rc _ tw 1 2 1 1 ltac:(lia) ltac:(discriminate) (fun H => H)). Qed.

  (** *** Corollaries for RLHL over [EIhl δS] (the superseded
      presentation of SL2Prog's [sl2rd_target]) *)

  (** [RLHL2Hyps] over [EIhl δS] would give copy-cat inclusion over the
      plain [EI δS] ([rlhl_complin_eihl], [classic]). *)
  Theorem sl2rd_no_rlhl2_pair rc si tw i j vx vy :
    i <> j -> (vx, vy) <> (0, 0) -> ~ si (fW i vx vy) (fR j) ->
    forall (I : RelaxedHoareBase.Assn (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (RelaxedHoareSpec.EI (F := F2 si) δF))
           (R G : CallKey (F2 si) ->
                  RelaxedHoareBase.PRel (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (RelaxedHoareSpec.EI (F := F2 si) δF)),
      ~ RelaxedHoareBase.RLHL2Hyps
          (VE := RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
          I R G (M2w rc si tw) ((regs0, []), []) (A0, []).
  Proof.
    intros Hij Hv Hn I R G HH.
    exact (sl2rd_no_complin_pair rc si tw i j vx vy Hij Hv Hn
             (RelaxedHoareCompLinSpec.rlhl_complin_eihl (E := E_S rc) δS (F := F2 si) δF A0 I R G (M2w rc si tw)
                (regs0, []) HH)).
  Qed.

  (** The review's [sl2rd_no_rlhl2_empty_any]: the ∅ negative over
      [EIhl δS] with no hypothesis on [tw].  It subsumes
      [sl2rd_no_rlhl2_empty], which is kept unchanged. *)
  Corollary sl2rd_no_rlhl2_empty_any rc tw :
    forall (I : RelaxedHoareBase.Assn (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS)
                  (RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF))
           (R G : CallKey (F2 (fun _ _ => False)) ->
                  RelaxedHoareBase.PRel (RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS)
                    (RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF)),
      ~ RelaxedHoareBase.RLHL2Hyps
          (VE := RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF)
          I R G (M2w rc (fun _ _ => False) tw) ((regs0, []), []) (A0, []).
  Proof. exact (sl2rd_no_rlhl2_pair rc _ tw 1 2 1 1 ltac:(lia) ltac:(discriminate) (fun H => H)). Qed.

  (** *** Corollaries for RLHL over [EIhlv δS] (option B, the
      presentation of the main theorem; RelaxedHoareSL2InvLog's
      [sl2rd_prov_target_v]) *)

  (** [RLHL2Hyps] over [EIhlv δS := Log (EIhl δS)] from
      [(((regs0, []), []), [])] would give copy-cat inclusion over the
      plain [EI δS] ([RelaxedHoareLog.rlhl_complin_eihlv], [classic]). *)
  Theorem sl2rd_no_rlhl2v_pair rc si tw i j vx vy :
    i <> j -> (vx, vy) <> (0, 0) -> ~ si (fW i vx vy) (fR j) ->
    forall (I : RelaxedHoareBase.Assn (RelaxedHoareLog.EIhlv (E := E_S rc) δS) (RelaxedHoareSpec.EI (F := F2 si) δF))
           (R G : CallKey (F2 si) ->
                  RelaxedHoareBase.PRel (RelaxedHoareLog.EIhlv (E := E_S rc) δS) (RelaxedHoareSpec.EI (F := F2 si) δF)),
      ~ RelaxedHoareBase.RLHL2Hyps
          (VE := RelaxedHoareLog.EIhlv (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
          I R G (M2w rc si tw) ((((regs0, []), []), [])) (A0, []).
  Proof.
    intros Hij Hv Hn I R G HH.
    exact (sl2rd_no_complin_pair rc si tw i j vx vy Hij Hv Hn
             (RelaxedHoareLog.rlhl_complin_eihlv (E := E_S rc) (F := F2 si) δS δF A0 I R G (M2w rc si tw)
                (regs0, []) HH)).
  Qed.

  (** The ∅ negative over [EIhlv δS], for every [rc] and every writer
      map. *)
  Corollary sl2rd_no_rlhl2v_empty rc tw :
    forall (I : RelaxedHoareBase.Assn (RelaxedHoareLog.EIhlv (E := E_S rc) δS)
                  (RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF))
           (R G : CallKey (F2 (fun _ _ => False)) ->
                  RelaxedHoareBase.PRel (RelaxedHoareLog.EIhlv (E := E_S rc) δS)
                    (RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF)),
      ~ RelaxedHoareBase.RLHL2Hyps
          (VE := RelaxedHoareLog.EIhlv (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 (fun _ _ => False)) δF)
          I R G (M2w rc (fun _ _ => False) tw) ((((regs0, []), []), [])) (A0, []).
  Proof. exact (sl2rd_no_rlhl2v_pair rc _ tw 1 2 1 1 ltac:(lia) ltac:(discriminate) (fun H => H)). Qed.

  (** ** Part 6. A reader that retries (review m-55)

      Writer [t1 = tw 1] writes (1,1) into instance 1; reader [t2 ≠ t1]
      reads instance 1.  Underlay handles: the write 0..6, the read
      10..21.  The schedule:
      - the write and the read are invoked;
      - the write's first four calls: [rd Sq_1] (0), [wr Sq_1 1], [wmb],
        [wr Sx_1 1];
      - the read's first iteration, each event crossing the write's six
        remaining events (other thread): [rd Sq_1] returns 1 (odd),
        [rd Sx_1] returns 1, [rd Sy_1] returns 0 (a torn pair), the
        second [rd Sq_1] returns 1; validation fails ([rok 1 1 = false]);
      - the write completes ([wr Sy_1 1], [wmb], [wr Sq_1 2]) and responds;
      - the read's second iteration reads 2, 1, 1, 2, validates and
        returns (1,1).
      The overlay trace [retry_trace] is the same as that of a run
      without retry, so the statement exposes the reader's underlay
      events in the execution ([underlay_of_thread]). *)
  Definition retry_trace (si : FOp -> FOp -> Prop) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
    [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t2 (@InvEv (F2 si) 1 (fR 1));
     Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW 1 1 1) tt); Build_ThreadEvent t2 (@ResEv (F2 si) 1 (fR 1) (1, 1))].

  (** The underlay events of thread [t] in a module execution, in order. *)
  Definition underlay_of_thread {E F : RelaxedSig.t} (t : tid) (evs : list (RelaxedModuleSemantics.ModuleEvent E F)) :
      list (ThreadEvent E) :=
    flat_map (fun me => match me with
                        | RelaxedModuleSemantics.UnderlayEvent e => if Pos.eqb (te_tid E e) t then [e] else []
                        | RelaxedModuleSemantics.OverlayEvent _ => []
                        end) evs.

  Theorem retry_exec rc si tw t1 t2 :
    t1 <> t2 -> tw 1 = t1 ->
    exists evs c,
      RelaxedModuleSemantics.module_execution_tagged (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw)
        (RelaxedModuleSemantics.initial_tagged_module (RelaxedHoareSpec.EI (F := E_S rc) δS) (regs0, [])) evs c /\
      RelaxedGSim.overlay_events evs = retry_trace si t1 t2 /\
      underlay_of_thread t2 evs = rd_iter_evs rc t2 1 10 1 1 0 1 ++ rd_iter_evs rc t2 1 16 2 1 1 2.
  Proof.
    intros Ht12 Htw1.
    assert (E12 : Pos.eqb t1 t2 = false) by (apply Pos.eqb_neq; exact Ht12).
    destruct (wr_guard_prod rc si tw t1 1 0 0 1 1 Htw1) as (trw & Hpw & Hmw & _).
    destruct (rd_retry_prod_gen rc si t2 1 10 1 1 0 1 2 1 1 eq_refl eq_refl) as (trr & Hpr & Hmr & Hdr).
    destruct trw as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 trw]]]]]]]]]]]]]]];
      try discriminate Hmw.
    pose proof Hmw as Hmw'. injection Hmw' as V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13.
    destruct trr as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 [|r9 [|r10 [|r11
                    [|r12 [|r13 [|r14 [|r15 [|r16 [|r17 [|r18 [|r19 [|r20 [|r21 [|r22 [|r23 [|r24 trr]]]]]]]]]]]]]]]]]]]]]]]]];
      try discriminate Hmr.
    pose proof Hmr as Hmr'.
    injection Hmr' as R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11 R12 R13 R14 R15 R16 R17 R18 R19 R20 R21 R22 R23.
    unpack_forall Hdr.
    do 2 eexists. split; [| split].
    - eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t1) (h := 0); [intros [] | exact Hpw |].
        rewrite Hmw. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t2) (h := 1); [fresh_call | exact Hpr |].
        rewrite Hmr. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. fresh_used Hk Hu. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      (* the write's rd Sq_1, wr Sq_1 1, wmb, wr Sx_1 1 *)
      m_step (sk si t1 0) w0 m_here ei_inv. m_step (sk si t1 0) w1 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w2 m_here ei_inv. m_step (sk si t1 0) w3 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w4 m_here ei_inv. m_step (sk si t1 0) w5 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w6 m_here ei_inv. m_step (sk si t1 0) w7 m_here ltac:(res0 rc).
      (* the read's failing iteration, past the write's six remaining events *)
      m_step (sk si t2 1) r0 ltac:(do 6 m_next; m_here) ei_inv.
      m_step (sk si t2 1) r1 ltac:(do 6 m_next; m_here) ltac:(res0 rc).
      m_step (sk si t2 1) r2 ltac:(do 6 m_next; m_here) ei_inv.
      m_step (sk si t2 1) r3 ltac:(do 6 m_next; m_here) ltac:(res0 rc).
      m_step (sk si t2 1) r4 ltac:(do 6 m_next; m_here) ei_inv.
      m_step (sk si t2 1) r5 ltac:(do 6 m_next; m_here) ltac:(res0 rc).
      m_step (sk si t2 1) r6 ltac:(do 6 m_next; m_here) ei_inv.
      m_step (sk si t2 1) r7 ltac:(do 6 m_next; m_here) ltac:(res0 rc).
      m_step (sk si t2 1) r8 ltac:(do 6 m_next; m_here) ei_inv.
      m_step (sk si t2 1) r9 ltac:(do 6 m_next; m_here) ltac:(res0 rc).
      m_step (sk si t2 1) r10 ltac:(do 6 m_next; m_here) ei_inv.
      m_step (sk si t2 1) r11 ltac:(do 6 m_next; m_here) ltac:(res0 rc).
      (* the write completes *)
      m_step (sk si t1 0) w8 m_here ei_inv. m_step (sk si t1 0) w9 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w10 m_here ei_inv. m_step (sk si t1 0) w11 m_here ltac:(res0 rc).
      m_step (sk si t1 0) w12 m_here ei_inv. m_step (sk si t1 0) w13 m_here ltac:(res0 rc).
      m_return (fW 1 1 1).
      (* the read's validating iteration *)
      m_step (sk si t2 1) r12 m_here ei_inv. m_step (sk si t2 1) r13 m_here ltac:(res0 rc).
      m_step (sk si t2 1) r14 m_here ei_inv. m_step (sk si t2 1) r15 m_here ltac:(res0 rc).
      m_step (sk si t2 1) r16 m_here ei_inv. m_step (sk si t2 1) r17 m_here ltac:(res0 rc).
      m_step (sk si t2 1) r18 m_here ei_inv. m_step (sk si t2 1) r19 m_here ltac:(res0 rc).
      m_step (sk si t2 1) r20 m_here ei_inv. m_step (sk si t2 1) r21 m_here ltac:(res0 rc).
      m_step (sk si t2 1) r22 m_here ei_inv. m_step (sk si t2 1) r23 m_here ltac:(res0 rc).
      m_return (fR 1).
      apply RelaxedModuleSemantics.tagged_module_execution_refl.
    - reflexivity.
    - unfold underlay_of_thread. cbn [flat_map app RelaxedModuleSemantics.ts_event].
      untag_rw. cbn [te_tid]. rewrite E12, Pos.eqb_refl. reflexivity.
  Qed.

  (** The retry trace is complete. *)
  Lemma retry_complete si t1 t2 : PrefixView.complete (retry_trace si t1 t2).
  Proof. complete_tac. Qed.
  (** The two operations of the retry trace, and its invocation and
      response positions. *)
  Definition rtW (si : FOp -> FOp -> Prop) (t1 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t1, 0) (fW 1 1 1) tt.
  Definition rtR (si : FOp -> FOp -> Prop) (t2 : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t2, 1) (fR 1) (1, 1).

  Section RetryTrace.
    Context (si : FOp -> FOp -> Prop) (t1 t2 : tid).
    Local Abbreviation sel := (@PrefixView.sel (F2 si)).

    Lemma retry_inv_cases n k op :
      RelaxedTraceLin.inv_at sel (retry_trace si t1 t2) n k op ->
      (n = 0 /\ k = (t1, 0) /\ op = fW 1 1 1) \/ (n = 1 /\ k = (t2, 1) /\ op = fR 1).
    Proof. inv_cases_n 4 n k. Qed.

    Lemma retry_res_idx n k op (r : far op) : RelaxedTraceLin.res_at sel (retry_trace si t1 t2) n k op r -> 2 <= n.
    Proof. res_idx_tac n. Qed.
  End RetryTrace.

  (** The retry trace is relaxed-linearizable under every [indep], with
      distinct threads: both invocations precede both responses, so there
      is no [rhb] edge; witness [W; R]. *)
  Theorem retry_rel_lin si indep t1 t2 :
    t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (retry_trace si t1 t2) indep
      (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Ht. exists [rtW si t1; rtR si t2].
    split; [| split; [| split; [| split]]].
    - eexists. econstructor; [reflexivity |]. econstructor; [split; reflexivity |]. constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [split; [find_idx | find_res] |]). destruct Ho.
    - intros n k op Hn.
      destruct (retry_inv_cases si t1 t2 _ _ _ Hn) as [(_ & -> & _) | (_ & -> & _)];
        [exists (rtW si t1) | exists (rtR si t2)]; (split; [in_tac | reflexivity]).
    - intros o o' _ _ [(n & m & Hn & Hm & Hnm) | (Hth & n & m & Hn & Hm & Hnm & _)]; exfalso.
      + apply retry_res_idx in Hn. destruct (retry_inv_cases si t1 t2 _ _ _ Hm) as [(-> & _) | (-> & _)]; lia.
      + destruct (retry_inv_cases si t1 t2 _ _ _ Hn) as [(-> & Hk & _) | (-> & Hk & _)];
        destruct (retry_inv_cases si t1 t2 _ _ _ Hm) as [(-> & Hk' & _) | (-> & Hk' & _)]; try lia.
        rewrite Hk, Hk' in Hth. cbn in Hth. exact (Ht Hth).
  Qed.

  (** The [slRA] instance (m-55: the retry execution is relaxed-
      linearizable under the main theorem's relation). *)
  Corollary retry_rel_lin_slRA t1 t2 :
    t1 <> t2 ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 slRA)) (retry_trace slRA t1 t2) slRA
      (RelaxedHoareSpec.seq_legal (F := F2 slRA) δF A0).
  Proof. exact (retry_rel_lin slRA slRA t1 t2). Qed.

  (** [MTraces] form of [retry_exec], with completeness. *)
  Corollary retry_exec_mtraces rc si tw t1 t2 :
    t1 <> t2 -> tw 1 = t1 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) (retry_trace si t1 t2) /\
    PrefixView.complete (retry_trace si t1 t2).
  Proof.
    intros Ht12 Htw1. destruct (retry_exec rc si tw t1 t2 Ht12 Htw1) as (evs & c & Hx & Ho & _).
    split; [exists evs, c; split; assumption | apply retry_complete].
  Qed.

  (** ** Part 7. Trace-level facts cited by other headers (reviews m-68, M-29)

      Added after the final review of RLHL-seqlock; earlier versions cited
      these facts as checked in scratch sessions only. *)

  (** *** The overtaking trace of [RelaxedHoareSL2Prog.sl2_read_overtakes_write]

      [ov_trace si t]: on one thread [t], a write of (1,1) into instance 1
      (handle 0) is invoked, then a read of instance 2 (handle 1); the
      read returns (0,0), then the write responds.  It is the trace of
      [sl2_read_overtakes_write] ([ov_exec]).  It is relaxed-linearizable
      under every relation, in particular ∅ ([ov_rel_lin],
      [ov_rel_lin_empty]): the only possible [rhb] edge is program order
      W → R, and the witness [W; R] is legal (the read is of another
      instance and returns its initial pair).  So this module-level
      reordering is no evidence that [slRA] is needed. *)
  Definition ov_trace (si : FOp -> FOp -> Prop) (t : tid) : list (ThreadEvent (F2 si)) :=
    [Build_ThreadEvent t (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t (@InvEv (F2 si) 1 (fR 2));
     Build_ThreadEvent t (@ResEv (F2 si) 1 (fR 2) (0, 0)); Build_ThreadEvent t (@ResEv (F2 si) 0 (fW 1 1 1) tt)].

  Definition ovW (si : FOp -> FOp -> Prop) (t : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t, 0) (fW 1 1 1) tt.
  Definition ovR (si : FOp -> FOp -> Prop) (t : tid) : RelaxedTraceLin.Op (F2 si) :=
    @RelaxedTraceLin.Build_Op (F2 si) (t, 1) (fR 2) (0, 0).

  (** [ov_trace] is the trace of [RelaxedHoareSL2Prog.sl2_read_overtakes_write],
      and it is complete. *)
  Corollary ov_exec rc si tw t :
    tw 1 = t ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) (ov_trace si t) /\
    PrefixView.complete (ov_trace si t).
  Proof.
    intros Ht. split; [exact (sl2_read_overtakes_write rc si tw t Ht) | exact (sl2_read_overtakes_write_complete si t)].
  Qed.

  Section OvTrace.
    Context (si : FOp -> FOp -> Prop) (t : tid).
    Local Abbreviation sel := (@PrefixView.sel (F2 si)).

    Lemma ov_inv_cases n k op :
      RelaxedTraceLin.inv_at sel (ov_trace si t) n k op ->
      (n = 0 /\ k = (t, 0) /\ op = fW 1 1 1) \/ (n = 1 /\ k = (t, 1) /\ op = fR 2).
    Proof. inv_cases_n 4 n k. Qed.

    Lemma ov_res_idx n k op (r : far op) : RelaxedTraceLin.res_at sel (ov_trace si t) n k op r -> 2 <= n.
    Proof. res_idx_tac n. Qed.
  End OvTrace.

  Theorem ov_rel_lin si indep t :
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (ov_trace si t) indep
      (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    exists [ovW si t; ovR si t].
    split; [| split; [| split; [| split]]].
    - eexists. econstructor; [reflexivity |]. econstructor; [split; reflexivity |]. constructor.
    - nodup_keys.
    - intros o Ho. cbn in Ho. repeat (destruct Ho as [<- | Ho]; [split; [find_idx | find_res] |]). destruct Ho.
    - intros n k op Hn.
      destruct (ov_inv_cases si t _ _ _ Hn) as [(_ & -> & _) | (_ & -> & _)];
        [exists (ovW si t) | exists (ovR si t)]; (split; [in_tac | reflexivity]).
    - intros o o' Ho Ho' [(n & m & Hn & Hm & Hnm) | (Hth & n & m & Hn & Hm & Hnm & _)].
      + exfalso. apply ov_res_idx in Hn. destruct (ov_inv_cases si t _ _ _ Hm) as [(-> & _) | (-> & _)]; lia.
      + destruct (ov_inv_cases si t _ _ _ Hn) as [(-> & Hk & _) | (-> & Hk & _)];
        destruct (ov_inv_cases si t _ _ _ Hm) as [(-> & Hk' & _) | (-> & Hk' & _)]; try lia.
        cbn in Ho, Ho'.
        destruct Ho as [<- | [<- | []]]; cbn in Hk; try discriminate Hk;
        destruct Ho' as [<- | [<- | []]]; cbn in Hk'; try discriminate Hk'.
        before_tac.
  Qed.

  (** The ∅ instance cited in the header of [RelaxedHoareSL2Prog]. *)
  Corollary ov_rel_lin_empty si t :
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (ov_trace si t) (fun _ _ => False)
      (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof. exact (ov_rel_lin si _ t). Qed.

  (** *** Store buffering with own reads (review M-29)

      [sbo si t1 t2]: [t1] writes (1,1) into instance 1, reads instance 1
      (its own write) and gets (1,1), then reads instance 2 and gets
      (0,0); [t2] symmetrically on instances 2 and 1.  All six
      invocations precede all responses; the reads respond before the
      writes.  This is the SeqLock-level shape of the
      store-buffering-with-own-reads example of trace.tex:94-107, which
      store forwarding produces (each reader forwards its own buffered
      [Sq], [Sx], [Sy] and reads the other instance from memory).

      [sbo_not_rel_lin]: the trace is not relaxed-linearizable under any
      relation contained in [slRA], so the verified [slRA] contract
      ([RelaxedHoareSL2Read.sl2_rel_lin] at [slRA]) excludes it.  Proof:
      the pairs [(fW i, fR i)] (own read) and [(fR, fR)] are not in
      [slRA], so program order gives [W_1 → R_1 → R_2] and
      [W_2 → R_2' → R_1']; legality puts [R_2] (returning (0,0)) before
      [W_2] and [R_1'] before [W_1]; this is a cycle.

      Trace level: over this MCA underlay [sbo] is not a module trace of
      [M2w rc si tw] for any [si] ([RelaxedHoareSL2Read.sbo_not_trace_rd],
      from this theorem and the main theorem).  That x86-TSO (where
      [smp_rmb]/[smp_wmb] are compiler barriers) and ARMv8 (where
      [rfi ∉ obs] and [DMB LD] orders no write before a later read)
      produce this outcome for the SeqLock is argued, not mechanized; no
      buffered or oMCA underlay is used here. *)
  Definition sbo (si : FOp -> FOp -> Prop) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
    [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t1 (@InvEv (F2 si) 1 (fR 1));
     Build_ThreadEvent t1 (@InvEv (F2 si) 2 (fR 2));
     Build_ThreadEvent t2 (@InvEv (F2 si) 3 (fW 2 1 1)); Build_ThreadEvent t2 (@InvEv (F2 si) 4 (fR 2));
     Build_ThreadEvent t2 (@InvEv (F2 si) 5 (fR 1));
     Build_ThreadEvent t1 (@ResEv (F2 si) 1 (fR 1) (1, 1)); Build_ThreadEvent t1 (@ResEv (F2 si) 2 (fR 2) (0, 0));
     Build_ThreadEvent t2 (@ResEv (F2 si) 4 (fR 2) (1, 1)); Build_ThreadEvent t2 (@ResEv (F2 si) 5 (fR 1) (0, 0));
     Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW 1 1 1) tt); Build_ThreadEvent t2 (@ResEv (F2 si) 3 (fW 2 1 1) tt)].

  (** The six operations of [sbo]. *)
  Definition sboWi (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 0) (fW 1 1 1) tt.
  Definition sboRi (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 1) (fR 1) (1, 1).
  Definition sboRj (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 2) (fR 2) (0, 0).
  Definition sboWj (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 3) (fW 2 1 1) tt.
  Definition sboRj' (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 4) (fR 2) (1, 1).
  Definition sboRi' (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 5) (fR 1) (0, 0).

  Lemma sbo_sub si t1 t2 :
    forall e, In e (sbo si t1 t2) ->
      In e (evs_of [sboWi si t1; sboRi si t1; sboRj si t1; sboWj si t2; sboRj' si t2; sboRi' si t2]).
  Proof. intros e He. cbn in He. repeat (destruct He as [<- | He]; [in_tac |]). destruct He. Qed.

  (** [sbo] is complete (so the negative below is not due to a missing
      response). *)
  Lemma sbo_complete si t1 t2 : PrefixView.complete (sbo si t1 t2).
  Proof.
    intros i [kt kh] op (x & Hn & Hs).
    do 12 (destruct i as [| i];
            [ cbn in Hn; injection Hn as <-; unfold PrefixView.sel in Hs;
              first [ discriminate Hs
                    | injection Hs as <- <- <-;
                      first [ solve [exists 6; eexists; inv_here] | solve [exists 7; eexists; inv_here]
                            | solve [exists 8; eexists; inv_here] | solve [exists 9; eexists; inv_here]
                            | solve [exists 10; eexists; inv_here] | solve [exists 11; eexists; inv_here] ] ]
            | ]).
    destruct i; cbn in Hn; discriminate Hn.
  Qed.

  Theorem sbo_not_rel_lin si indep t1 t2 :
    (forall o o', indep o o' -> slRA o o') ->
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sbo si t1 t2) indep
        (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof.
    intros Hsub Hrl.
    destruct (rel_lin_ops (sbo si t1 t2) indep _
                [sboWi si t1; sboRi si t1; sboRj si t1; sboWj si t2; sboRj' si t2; sboRi' si t2]
                ltac:(nodup_keys) (sbo_sub si t1 t2) Hrl)
      as (W & (A' & Hrun) & Hnd & HW & Hin & Hord).
    assert (H0 : In (sboWi si t1) W) by (apply (Hin _ 0); [in_tac | inv_here]).
    assert (H1 : In (sboRi si t1) W) by (apply (Hin _ 1); [in_tac | inv_here]).
    assert (H2 : In (sboRj si t1) W) by (apply (Hin _ 2); [in_tac | inv_here]).
    assert (H3 : In (sboWj si t2) W) by (apply (Hin _ 3); [in_tac | inv_here]).
    assert (H4 : In (sboRj' si t2) W) by (apply (Hin _ 4); [in_tac | inv_here]).
    assert (H5 : In (sboRi' si t2) W) by (apply (Hin _ 5); [in_tac | inv_here]).
    assert (B01 : RelaxedTraceLin.before W (sboWi si t1) (sboRi si t1)).
    { apply Hord; [exact H0 | exact H1 |]. right. split; [reflexivity |]. exists 0, 1.
      split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact (H eq_refl). }
    assert (B12 : RelaxedTraceLin.before W (sboRi si t1) (sboRj si t1)).
    { apply Hord; [exact H1 | exact H2 |]. right. split; [reflexivity |]. exists 1, 2.
      split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact H. }
    assert (B34 : RelaxedTraceLin.before W (sboWj si t2) (sboRj' si t2)).
    { apply Hord; [exact H3 | exact H4 |]. right. split; [reflexivity |]. exists 3, 4.
      split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact (H eq_refl). }
    assert (B45 : RelaxedTraceLin.before W (sboRj' si t2) (sboRi' si t2)).
    { apply Hord; [exact H4 | exact H5 |]. right. split; [reflexivity |]. exists 4, 5.
      split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact H. }
    destruct (In_nth_error _ _ H0) as (i0 & E0). destruct (In_nth_error _ _ H1) as (i1 & E1).
    destruct (In_nth_error _ _ H2) as (i2 & E2). destruct (In_nth_error _ _ H3) as (i3 & E3).
    destruct (In_nth_error _ _ H4) as (i4 & E4). destruct (In_nth_error _ _ H5) as (i5 & E5).
    pose proof (before_idx W _ _ _ _ Hnd B01 E0 E1). pose proof (before_idx W _ _ _ _ Hnd B12 E1 E2).
    pose proof (before_idx W _ _ _ _ Hnd B34 E3 E4). pose proof (before_idx W _ _ _ _ Hnd B45 E4 E5).
    assert (i2 < i3).
    { apply (leg_read_before A0 W A' i2 i3 (sboRj si t1) (sboWj si t2) 2 1 1 Hrun E2 E3 eq_refl eq_refl).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hop;
        try discriminate Hop; injection Hop; intros; subst; cbn; congruence. }
    assert (i5 < i0).
    { apply (leg_read_before A0 W A' i5 i0 (sboRi' si t2) (sboWi si t1) 1 1 1 Hrun E5 E0 eq_refl eq_refl).
      intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hop;
        try discriminate Hop; injection Hop; intros; subst; cbn; congruence. }
    lia.
  Qed.

End RelaxedHoareSL2Exec.
