(** * RelaxedHoareSL2Inv: invariant, rely, guarantee and the side fields
      of the RLHL SeqLock (WRd writer) — RLHL-seqlock tasks .4 and .B6

    Plan: [.rocq-review/tasks/RLHL-seqlock.md] §2.4 and task .4, with its
    Addendum (author decision RS-1: WRd only, overlay relation [slRA]),
    Addendum 2 ("RLHL in full": every method is a [MethodProvable]
    derivation through [run_method_provable]/[rp_run]; soundness only
    through [method_sound] and [RLHL2Hyps]) and Addendum 3 (author
    decision option B; task .B6: the read postcondition [Qrd] and the
    per-operation assembly lemmas, Part 9; reader-eval §1.3 and
    latest-review m-51, m-58).  The program and the signatures are those
    of [RelaxedHoareSL2Prog] ([M2w rc si tw] over [E_S rc], overlay
    [F2 si]).  This file proves no method derivation except the [div]
    case of a write ([sl2_write_other_provable]).  The derivations are
    [RelaxedHoareSL2Write.write_provable] (over [EIhl], lifted to
    [EIhlv]) and [RelaxedHoareSL2Read.read_provable_v] (over [EIhlv]);
    the main theorem is [RelaxedHoareSL2Read.sl2_main].  The [EIhl]
    targets of this file are superseded (see Part 9 and OPEN).

    ** The frozen statements (Part 1)

    Underlay [VE := EIhl (E := E_S rc) δS], overlay
    [VF := EI (F := F2 si) δF]; a proof state is
    [(((m, U), used), PossOk (A, Pf) P, γ)].

    - [Isl rc si tw s]: [∃ A Pf P, ps_poss s = PossOk (A, Pf) P ∧
      eihl_rec_used ∧ IslC m A Pf P γ], where the record [IslC] has the
      fields
      - [ic_wf] the pool is well formed; [ic_age] [GAge P γ]; [ic_gwf]
        every ghost entry is an invocation of its owner's thread;
        [ic_rec]/[ic_recnd] every overlay record belongs to an [ls_lini]
        entry, one record per key; [ic_gnd] the ghost has no duplicate;
      - [ic_coup] ([Coup]): a read is at [ls_inv] iff it owns a pending
        [rmb]; a write at [ls_inv] owns a pending [wmb] and a pending
        access to [Sq_i];
      - [ic_tw] (P1): a pool write of instance [i] is on thread [tw i];
      - [ic_word] ([WOrd]): of two writes of instance [i], once the younger
        has emitted its [rd Sq_i], the older owns no pending access to
        [Sq_i];
      - [ic_jeven] ([JEven]): [Sq_i] even ⟹ [(Sx_i, Sy_i) = A i];
      - [ic_jodd] ([JOdd]): [Sq_i] odd ⟹ some [Holder i k] with operation
        [fW i vx vy] is past [ls_inv] and [A i = (vx, vy)].
      [Holder i k]: [k] is a write of [i] with no pending [rd Sq_i] and a
      pending write of [Sq_i].
    - [Rsl rc si k]: memory moves by [eihl_steps δS]; [k]'s pool entry,
      overlay records and ghost entries are kept; [OlderSub k] (no ghost
      entry of a call older than [k] appears; this keeps [RecNB]); every
      instance that [k] holds is frozen ([InstFrozen]: its three registers
      and [A i]); [SeqMono].
    - [Gsl rc si k]: memory moves by [eihl_steps δS]; the pool entries,
      records and ghost entries of every other call are kept;
      [OlderSub k'] for every [k']; the instances held by other calls are
      frozen; [SeqMono].
      [SeqMono]: every [Sq_i] only grows; while [Sq_i] is unchanged,
      [A i] is unchanged, and if [Sq_i] is even so are [Sx_i], [Sy_i].
    - [Osl rc tw t op h evs] (the footprint [Ω]): for [fR i], [RdShape t i
      evs] (one or more iterations [rd Sq_i; rmb; rd Sx_i; rd Sy_i; rmb;
      rd Sq_i], distinct handles); for [fW i vx vy], [t = tw i ∧ WrShape t
      i vx vy evs] (the seven WRd invocations, distinct handles).  P1
      enters here: a write by [t ≠ tw i] runs [div] and has footprint
      [False].
    - [Qsl rc si k op r] (the postcondition [Q]): [k] is at [ls_linr op r],
      or at [ls_lini op] with its record [Op k op r].  As the *read*
      postcondition it is superseded by [Qrd] (Part 9, B-6): no
      derivation of the read can reach [Qsl] at [Close] (argued in
      reader-eval §1.3; [owns_rmb_not_qsl] is the closed key lemma).  [Qsl] stays the write postcondition.

    Linearization points (plan §2.4, adapted to WRd): a read at the
    emission of its last [rmb] (the final iteration's [rmb_b]; "last" is
    read off the ghost: [k] owns no [rmb] afterwards, decidable by
    [owns_dec]); a write at the emission of its first write
    [wr Sq_i (v+1)], which makes [Sq_i] odd and sets [A i := (vx, vy)].

    ** Readiness (Part 5): which overlay pairs need semi-independence

    At the LP of a call [(t, h)], every older [ls_inv] call [k1] of thread
    [t] must be crossed ([RelaxedHoareReady.emit_ready_rec]):

    | older \ younger | read_i (LP: last [rmb])        | write_i (LP: [wr Sq_i (v+1)])    |
    |-----------------|--------------------------------|----------------------------------|
    | read_j          | direct: pending [rmb], Rmb/Rmb | recorded: a pending [rmb] would have blocked the write's [rd Sq_i] (Rmb→DR, [lb_blocking]) |
    | write_j, j ≠ i  | overlay SI: [slRA (fW j _ _) (fR i)] | direct: pending [wmb], Wmb→DW |
    | write_i         | recorded: a pending access to [Sq_i] would have blocked the read's [rd Sq_i] of the same iteration | direct: pending [wmb] (and same location) |

    "Recorded" means: the derivation carries [RecNB] of the earlier
    invocation to the LP ([KRecNB] is stable under [Rsl] and every [Gsl]).
    Only (older write_j, younger read_i), [j ≠ i], uses the overlay
    relation: by [sb_blocking], once the write's [rd Sq_j] is emitted the
    read's events cross the rest of the write, so the read's LP can come
    before the write's ([sl2_read_overtakes_write] is such a module
    trace).  [ready_write] uses no overlay relation, [ready_read] needs
    [si ⊇ slRA].  Answer to the Addendum's question: the statements hold
    for every [si ⊇ slRA]; no upper bound such as [si ⊆ slsi] is needed
    (a larger [si] only makes readiness easier), and the side fields hold
    for every [si].

    ** Contents
    - Part 2-3: ownership/pool/order facts; [holder_unique] (at most one
      holder per instance, from [WOrd] and P1), [holder_inv_even] (a
      holder before its LP sees an even [Sq_i]), [holder_odd].
    - Part 4: the fields of [RLHL2Hyps] other than [h_sem]: [gsl_rsl]
      ([h_guar_rely]), [invoke_rely], [return_rely], [isl_ok], [isl_init];
      [mp_PI] = [isl_postinvoke], [mp_ret] = [qsl_ret];
      [sl2_method_provable]; the assembly [sl2rd_rlhl2_of_provable]
      (every [h_sem] through [RelaxedHoareSound.method_sound]).
    - Part 5: [ready_write], [ready_read].
    - Part 6, stability kit: [KLook], [KRec], [KOwns], [KNotOwns],
      [KHolder], [KHeld] (stable under [Rsl k]); [KRecNB], [KSeqGe],
      [KRdVal] (the reader's value fact: [Sq_i ≥ s] and, while [Sq_i = s]
      even, [pr (A i) = x]), [KMine], [KDoomRd] (stable under [Rsl k]
      and every [Gsl k']).  These are the plan's "seq monotone", "data
      frozen while seq is even and unchanged" and "copy-freeze" stability
      facts.  Identification of a read's response value with its record
      value: [read_inv_mine] (the emitted read owns its record, whose value
      is the register), [good_or_doom], [kdoomrd_refuted] (a wrong
      prophecy is stable and refuted only by the read's own response).
    - Part 7, maintenance, each giving the post-state [Isl] and the
      [Gsl k] step: [isl_response] (any response), [isl_inv_noreg] (an
      invocation that writes no register: the reader's events other than
      its LP, the writer's [rd Sq_i] and [wmb]s), [isl_read_lp] (readiness
      and [psa_inv] with result [A i]), [isl_wr_lp] (readiness and
      [psa_inv]), [isl_wr_data], [isl_wr_end].
    - Part 8, entry points: [m2w_read_body], [m2w_write_body],
      [m2w_write_div], [pinit_facts], [rprovable_div],
      [sl2_write_other_provable] (the [div] case of a write, closed here),
      [sl2_read_run_provable], [sl2_write_run_provable],
      [sl2rd_rlhl2_of_methods]; after the section,
      [sl2rd_target_of_methods] (the target [sl2rd_target] of
      [RelaxedHoareSL2Prog] from the two method derivations).  For reads,
      [sl2_read_run_provable], [sl2rd_rlhl2_of_provable],
      [sl2rd_rlhl2_of_methods] and [sl2rd_target_of_methods] are
      superseded by their [_rd] versions of Part 9 (B-6: their read
      premise asks for [Qsl], which no derivation reaches, as argued in
      reader-eval §1.3); they are kept unchanged.
    - Part 9 (B-6, m-51): [owns_rmb_not_qsl] (the cause of B-6: [Qsl]
      fails while the read owns an [rmb]); the read postcondition
      [Qrd k i r := Qsl k (fR i) r ∨ ¬ NoOwn k γ] and the per-operation
      postcondition [Qop] ([Qrd] for reads, [Qsl] for writes);
      [qrd_ret]/[qop_ret] ([mp_ret]: the new disjunct is refuted by
      [NoOwn], through [RelaxedHoareReady.retcond_or_owned]);
      [qrd_of_owns] ([Qrd] holds wherever the read still owns an entry);
      [sl2_method_provable_op], [sl2_read_run_provable_rd],
      [sl2rd_rlhl2_of_provable_rd] (premise [∀ t op, ∃ Ω Q,
      MethodProvable …], the shape of [rlhl_sound_complin]),
      [sl2_provable_op_of_methods_rd], [sl2rd_rlhl2_of_methods_rd]; after
      the section, [sl2rd_prov_target] (the target with derivations,
      m-51, script S3), [sl2rd_prov_target_imp] (it implies
      [sl2rd_target]), [sl2rd_prov_target_of_methods_rd],
      [sl2rd_target_of_methods_rd].

    ** K / S / P / R
    - K: all 140 [Lemma]/[Theorem] results of this file are closed under
      the global context ([Print Assumptions], Rocq 9.3.0): no
      [classic], no [eq_rect_eq], no other axiom.
    - S: every statement is for every [rc], [si], [tw]; [ready_read],
      [isl_read_lp] for every [si ⊇ slRA].  The side fields are proved
      outright; [h_sem] is a hypothesis of [sl2rd_rlhl2_of_provable]
      (for all methods) and of [sl2rd_rlhl2_of_methods] (reads on every
      thread, writes on [tw i]; writes on other threads are discharged by
      [sl2_write_other_provable]); likewise for the [_rd] versions, whose
      read premise has [Qrd] and whose generic form takes any footprint
      and postcondition per operation.  The [_rd] assembly and target
      lemmas ([sl2rd_rlhl2_of_provable_rd], [sl2rd_rlhl2_of_methods_rd],
      [sl2rd_target_of_methods_rd]; and [sl2rd_prov_target_of_methods_rd],
      whose conclusion [sl2rd_prov_target] implies [sl2rd_target]) have
      weaker premises than the originals and the same conclusions.
      [sl2_read_run_provable_rd] does not have the same conclusion: its
      step premise asks for [Qrd] instead of [Qsl] at [Close], and it
      concludes [MethodProvable … Qrd], a weaker postcondition than the
      [MethodProvable … Qsl] of [sl2_read_run_provable].  Every method
      premise is a hypothesis in
      this file.  The write premise is discharged by
      [RelaxedHoareSL2Write.write_provable].  Over [EIhl] the read
      premise, even with [Qrd], is believed unsatisfiable (see OPEN), so
      the [EIhl] targets ([sl2rd_prov_target] here,
      [RelaxedHoareSL2Prog.sl2rd_target]) and the theorems concluding
      them are superseded and not citable; the citable targets are over
      [EIhlv] ([RelaxedHoareSL2InvLog.sl2rd_prov_target_v],
      [sl2rd_complin_target]), proved as [RelaxedHoareSL2Read.sl2_main]
      and [RelaxedHoareSL2Read.sl2_complin].  Nothing here is a relaxed
      linearizability or copy-cat result.
    - P: no SeqLock text in the main paper (plan §1); Appendix/SeqLock.tex
      is a different, TicketLock-based object.  The proof pattern is
      RLHL's rely/guarantee with the ghost frontier, in the mechanized
      RLHL of [RelaxedHoare] (the printed rules of
      Appendix/programlogic.tex §app:program-logic differ, and have no
      ghost; see the table in [RelaxedHoare]'s header, M-21, m-66).
    - R: groundwork for popl2027-reviews.md:215 ("No example verified on
      the COH model"); answers nothing by itself.

    ** OPEN: the read derivation (task .5) over [EIhl]; author decision:
       option B (history presentation), under which it is done

    Status: over [EIhl] the question below stays open (argued only).
    Over [EIhlv] the read derivation is mechanized:
    [RelaxedHoareSL2Read.read_provable_v], with the lifted
    [Isl]/[Rsl]/[Gsl]/[Osl]/[Qrd] of [RelaxedHoareSL2InvLog].

    Over the presentation [VE := EIhl δS] used in this file, the read of
    [RelaxedHoareSL2Prog] (no tags) is believed to have no
    [MethodProvable] derivation.  Status (reader-eval §2,
    .rocq-review/tasks/RLHL-seqlock-reader-eval.md): with the frozen
    [Isl]/[Rsl]/[Gsl]/[Osl] and [Qrd], a rigorous argument whose key
    lemmas are closed as scratch scripts ([fam_merge], [rsl_step],
    [m24_not_stable], [doom_vacuous_after_consumption] in
    .rocq-review/scripts/RLHLsl_readerC_fam_merge.v), not a theorem; for
    every [I], [R], [G], argued only.  Neither is stated as a theorem
    here.  The mechanism:
    - The read returns [(a, c)], the responses of its [rd Sx_i] and
      [rd Sy_i], and validates with the responses [s], [s'] of its two
      [rd Sq_i].  These responses carry no tag, so the module may emit
      each of them after the LP and after the final [rd Sq_i], when [Sq_i]
      has moved on.
    - The [EIhl] state forgets the value of an underlay record once a
      response consumes it, and it does not record which call owns an
      emitted underlay key.  The rely of a call contains the guarantees of
      the other calls of its thread, which consume their own records; in
      this state such a step cannot be told apart from one that consumes
      the reading call's pending record.  Hence "record value = response
      value" is available only in the precondition of that response
      ([eihl_mine_res], [kdoomrd_refuted]); in any other assertion a
      disjunct "the record is gone" survives to the return and cannot be
      refuted.
    - The correctness of the result needs four record values (two reads of
      [Sq_i], one of [Sx_i], one of [Sy_i]) and the LP's [A i] to meet in
      one assertion, through a fact that holds only while [Sq_i] is
      unchanged.  A response's own postcondition can relate its value
      only to the current [Sq_i], which is stale at the return; the
      frame state of a call (its pool phase and its record [A i]) cannot
      store the [Sq_i] seen at the validation.
    - The write has no such problem: its value-carrying response
      ([rd Sq_i]) is a tagged predecessor ([dix [0]]) of both writes of
      [Sq_i], so the value reaches the LP along an F3 edge.
    - The limitation is in the lossy presentation [EIhl], not in the
      derivation system (correction m-58 of an earlier version of this
      header): the paper's proof state carries the trace [s]
      (Appendix/programlogic.tex:530; :579, rule EStep; lines as in
      async-ccal commit 4a2db8e1, 42 higher than in 01484091), and over a
      presentation that keeps the underlay history ([EIhlv], which
      restores the underlay projection of [s]) the same RLHL rules
      suffice for this read (mechanized:
      [RelaxedHoareSL2Read.read_provable_v] over [EIhlv]; the sketch of
      reader-eval §4 needed the additions G1-G6 listed in
      [RelaxedHoareSL2InvLog]).  For implex.tex:3 ("RLHL is
      complete with respect to relaxed linearizability") this is an
      incompleteness datum for the lossy presentation only; "RLHL is
      complete" is not claimed.  The semantic triple [MethodSem] (route S,
      excluded by the author) is not affected.
    - Independently of the presentation, the frozen read postcondition
      [Qsl] is unreachable at [Close] (B-6, argued in reader-eval §1.3);
      Part 9
      replaces it by [Qrd].
    Author decision (2026-10-15, option B): the underlay presentation of
    the method derivations and of the main theorem is the history
    presentation [EIhlv := Log (EIhl δS)] (task .L,
    [RelaxedHoareLog]), trace-equivalent to [EIhl]; the program and the
    RLHL rules are unchanged.  The derivations of the main theorem are
    over [EIhlv]: [RelaxedHoareSL2InvLog] (task .4v) lifts
    [Isl]/[Rsl]/[Gsl]/[Osl]/[Qrd] to [EIhlv];
    [RelaxedHoareSL2Write.write_provable_v] (.6) is the [EIhl] write
    derivation lifted by [methodprovable_lift];
    [RelaxedHoareSL2Read.read_provable_v] (.5) is the read derivation,
    directly over [EIhlv].  Not chosen: tagging the reader (option A; the tags
    are outside the paper's dependency policy, impl.tex:120, and results
    would transfer to the untagged module for complete traces only).
    Withdrawn: recording the owners of pending responses in the proof
    state (option (b) of an earlier version of this header) is neither
    needed nor sufficient (reader-eval §2, §4).

    ** What remained after this file (all done elsewhere)
    - .4v: the frozen definitions and [Qrd] lifted to [EIhlv], and the
      target over [EIhlv] in the shape of [sl2rd_prov_target]:
      [RelaxedHoareSL2InvLog] ([IslV]/[RslV]/[GslV]/[QrdV],
      [sl2rd_prov_target_v], [sl2rd_complin_target]).
    - .6 (write by [tw i]): a machine invariant over [wnext] with the
      Part 7 lemmas and Part 6's stability lemmas, over [EIhl] through
      [sl2_write_run_provable]: [RelaxedHoareSL2Write.write_provable],
      lifted to [EIhlv] as [write_provable_v].
    - .5 (read), over [EIhlv], with [Qrd]:
      [RelaxedHoareSL2Read.read_provable_v] (through
      [RelaxedHoareSL2InvLog.sl2_read_run_provable_v], the [EIhlv]
      counterpart of [sl2_read_run_provable_rd]).
    - .7: the main theorem over [EIhlv], [RelaxedHoareSL2Read.sl2_main];
      [RCompLin] over [EI δS] through the [EIhlv]-to-[EI] transfer of
      [RelaxedHoareLog], [RelaxedHoareSL2Read.sl2_complin]; then
      [cc_rel_lin], [RelaxedHoareSL2Read.sl2_rel_lin].

    ** Limitations
    - [Rsl]/[Gsl] let memory move by any [EIhl δS] steps (as
      [RelaxedHoareInherit.Rren]); value facts are carried by [SeqMono]
      and the holder protection, record facts by [eihl_mine].
    - Part 7's lemmas take the facts a derivation knows locally as
      hypotheses (the call's phase, [Holder], [RecNB], the coupling after
      the emission, the register values); they do not choose the slot
      assertions.
    - The underlay is the sequential register file of
      [RelaxedHoareSL2Prog] (scope as stated there). *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia Relations.Relation_Operators.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import models.simlin.RelaxedHoareRun.
Require Import models.simlin.RelaxedHoareReady.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.RelaxedHoareSL2Prog.

Import ListNotations.

Module RelaxedHoareSL2Inv.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareCompLinSpec.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.
  Import RelaxedHoareRun.
  Import RelaxedHoareReady.
  Import RelaxedHoareSL2Prog.

  Section SL2.
    Context (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid).

    Local Abbreviation ES := (E_S rc).
    Local Abbreviation FS := (F2 si).
    Local Abbreviation VE := (EIhl (E := E_S rc) δS).
    Local Abbreviation VF := (RelaxedHoareSpec.EI (F := F2 si) δF).
    Local Abbreviation POk v pool := (@PossOk FS VF v pool).
    Local Abbreviation OpF := (RelaxedTraceLin.Op FS).
    Local Abbreviation okey := (@RelaxedTraceLin.op_key FS).
    Local Abbreviation oop := (@RelaxedTraceLin.op_op FS).

    (** ** Part 1. The frozen definitions *)

    (** *** Ghost and pool vocabulary *)

    (** The underlay operation of a ghost entry. *)
    Definition gop (e : ScheduledEvent ES FS) : SOp := event_op (te_ev ES (se_event e)).

    (** [k] owns a pending invocation whose operation satisfies [Q]. *)
    Definition Owns (k : CallKey FS) (Q : SOp -> Prop) (γ : Ghost ES FS) : Prop :=
      exists e, In e γ /\ se_owner e = k /\ Q (gop e).

    Definition lsop (ls : LinState FS) : FOp :=
      match ls with ls_inv o | ls_lini o | ls_linr o _ => o end.

    Definition is_inv (ls : LinState FS) : bool :=
      match ls with ls_inv _ => true | _ => false end.

    (** The overlay operation of a pool entry, whatever its phase. *)
    Definition HasOp (k : CallKey FS) (o : FOp) (P : LinPool FS) : Prop :=
      exists ls, lin_lookup k ls P /\ lsop ls = o.

    Definition IsWr (i : nat) (k : CallKey FS) (P : LinPool FS) : Prop :=
      exists vx vy, HasOp k (fW i vx vy) P.

    Definition atSq (i : nat) (o : SOp) : Prop := ogl o = GD (Sq i).
    Definition isRdSq (i : nat) (o : SOp) : Prop := o = sRd (Sq i).
    Definition isWrSq (i : nat) (o : SOp) : Prop := exists v, o = sWr (Sq i) v.
    Definition isRmb (o : SOp) : Prop := o = sRmb.
    Definition isWmb (o : SOp) : Prop := o = sWmb.

    (** [k] holds instance [i]: a write of [i] that has emitted its
        [rd Sq_i] and still has a write of [Sq_i] pending (from its
        [rd Sq_i] to its last [wr Sq_i]). *)
    Definition Holder (i : nat) (k : CallKey FS) (P : LinPool FS) (γ : Ghost ES FS) : Prop :=
      IsWr i k P /\ ~ Owns k (isRdSq i) γ /\ Owns k (isWrSq i) γ.

    (** The coupling of a call's phase with its pending invocations: a
        read is at [ls_inv] iff it owns a pending [rmb] (its LP is its last
        [rmb]); a write at [ls_inv] owns a pending [wmb] and a pending
        access to [Sq_i] (its LP is its first [wr Sq_i]). *)
    Definition Coup (k : CallKey FS) (ls : LinState FS) (γ : Ghost ES FS) : Prop :=
      match lsop ls with
      | fR _ => is_inv ls = true <-> Owns k isRmb γ
      | fW i _ _ => is_inv ls = true -> Owns k isWmb γ /\ Owns k (atSq i) γ
      end.

    (** Writes of one instance start in age order: once a younger write
        has emitted its [rd Sq_i], an older one has no pending access to
        [Sq_i] left.  With P1 this gives at most one holder per instance
        ([holder_unique]). *)
    Definition WOrd (P : LinPool FS) (γ : Ghost ES FS) : Prop :=
      forall i k1 k2, IsWr i k1 P -> IsWr i k2 P -> key_older (lin_domain P) k1 k2 ->
        ~ Owns k2 (isRdSq i) γ -> ~ Owns k1 (atSq i) γ.

    (** *** The per-instance value clauses *)

    (** An even sequence number: the data registers are the abstract pair. *)
    Definition JEven (m : Regs) (A : AS) : Prop :=
      forall i, Nat.even (m (Sq i)) = true -> (m (Sx i), m (Sy i)) = A i.

    (** An odd sequence number: some holder has linearized, and the
        abstract pair is its pair. *)
    Definition JOdd (m : Regs) (A : AS) (P : LinPool FS) (γ : Ghost ES FS) : Prop :=
      forall i, Nat.even (m (Sq i)) = false ->
        exists k vx vy, Holder i k P γ /\ HasOp k (fW i vx vy) P /\
          ~ lin_lookup k (@ls_inv FS (fW i vx vy)) P /\ A i = (vx, vy).

    (** *** The invariant, the rely and the guarantee *)

    (** The clauses of the invariant on the registers [m], the abstract
        state [(A, Pf)], the pool [P] and the ghost [γ]: bookkeeping
        ([ic_wf] .. [ic_recnd], [ic_gnd]), coupling ([ic_coup]), P1
        ([ic_tw]), start order ([ic_word]), values ([ic_jeven], [ic_jodd]). *)
    Record IslC (m : Regs) (A : AS) (Pf : list OpF) (P : LinPool FS) (γ : Ghost ES FS) : Prop := {
      ic_wf : lin_pool_well_formed P;
      ic_age : GAge P γ;
      ic_gwf : Forall RelaxedHoareInherit.gwf γ;
      ic_rec : forall o, In o Pf -> lin_lookup (okey o) (ls_lini (oop o)) P;
      ic_recnd : NoDup (map okey Pf);
      ic_coup : forall e, In e P -> Coup (lin_key e) (lin_state FS e) γ;
      ic_tw : forall e i vx vy, In e P -> lsop (lin_state FS e) = fW i vx vy -> lin_tid FS e = tw i;
      ic_word : WOrd P γ;
      ic_jeven : JEven m A;
      ic_jodd : JOdd m A P γ;
      ic_gnd : NoDup γ
    }.

    Definition regs (s : PState VE VF) : Regs := fst (fst (ps_mem s)).

    Definition Isl : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ eihl_rec_used (E := ES) δS (ps_mem s) /\
        IslC (regs s) A Pf P (ps_ghost s).

    (** Instance [i] (its three registers and its abstract pair) does not
        change. *)
    Definition InstFrozen (i : nat) (m m' : Regs) (A A' : AS) : Prop :=
      m' (Sq i) = m (Sq i) /\ m' (Sx i) = m (Sx i) /\ m' (Sy i) = m (Sy i) /\ A' i = A i.

    (** Sequence numbers only grow; while one is unchanged the abstract
        pair is unchanged, and so are the data registers if it is even. *)
    Definition SeqMono (m m' : Regs) (A A' : AS) : Prop :=
      forall i, m (Sq i) <= m' (Sq i) /\
        (m' (Sq i) = m (Sq i) -> A' i = A i /\
           (Nat.even (m (Sq i)) = true -> m' (Sx i) = m (Sx i) /\ m' (Sy i) = m (Sy i))).

    (** The rely of [k] (frame style, as [RelaxedHoareInherit.Rren]):
        memory moves by [EIhl δS] steps; [k]'s pool entry, overlay records
        and ghost entries are kept; no older entry is added ([OlderSub],
        which keeps [RecNB]); an instance [k] holds is frozen; [SeqMono]. *)
    Definition Rsl (k : CallKey FS) : PRel VE VF := fun s s' =>
      eihl_steps (E := ES) δS (ps_mem s) (ps_mem s') /\
      exists A Pf P A' Pf' P', ps_poss s = POk (A, Pf) P /\ ps_poss s' = POk (A', Pf') P' /\
        (forall ls, lin_lookup k ls P -> lin_lookup k ls P') /\
        (forall o : OpF, okey o = k -> In o Pf -> In o Pf') /\
        (forall e, se_owner e = k -> (In e (ps_ghost s) <-> In e (ps_ghost s'))) /\
        OlderSub k P (ps_ghost s) P' (ps_ghost s') /\
        (forall i, Holder i k P (ps_ghost s) -> InstFrozen i (regs s) (regs s') A A') /\
        SeqMono (regs s) (regs s') A A'.

    (** The guarantee of [k]: the dual frame, for every other call. *)
    Definition Gsl (k : CallKey FS) : PRel VE VF := fun s s' =>
      eihl_steps (E := ES) δS (ps_mem s) (ps_mem s') /\
      exists A Pf P A' Pf' P', ps_poss s = POk (A, Pf) P /\ ps_poss s' = POk (A', Pf') P' /\
        (forall k' ls, k' <> k -> lin_lookup k' ls P -> lin_lookup k' ls P') /\
        (forall o : OpF, okey o <> k -> In o Pf -> In o Pf') /\
        (forall e, se_owner e <> k -> (In e (ps_ghost s) <-> In e (ps_ghost s'))) /\
        (forall k', OlderSub k' P (ps_ghost s) P' (ps_ghost s')) /\
        (forall i k', k' <> k -> Holder i k' P (ps_ghost s) -> InstFrozen i (regs s) (regs s') A A') /\
        SeqMono (regs s) (regs s') A A'.

    (** *** Footprints and postconditions *)

    Definition IE (t : tid) (h : nat) (o : SOp) : ThreadEvent ES := Build_ThreadEvent t (@InvEv ES h o).

    Definition rd_iter (t : tid) (i : nat) (hs : nat * nat * nat * nat * nat * nat) : list (ThreadEvent ES) :=
      let '(hG, hA, hX, hY, hB, hT) := hs in
      [IE t hG (sRd (Sq i)); IE t hA sRmb; IE t hX (sRd (Sx i)); IE t hY (sRd (Sy i)); IE t hB sRmb; IE t hT (sRd (Sq i))].

    Definition hs_list (hs : nat * nat * nat * nat * nat * nat) : list nat :=
      let '(hG, hA, hX, hY, hB, hT) := hs in [hG; hA; hX; hY; hB; hT].

    (** The invocations of a read: one or more iterations
        [rd Sq_i; rmb; rd Sx_i; rd Sy_i; rmb; rd Sq_i], distinct handles. *)
    Definition RdShape (t : tid) (i : nat) (evs : list (ThreadEvent ES)) : Prop :=
      exists hss, hss <> [] /\ NoDup (flat_map hs_list hss) /\ evs = flat_map (rd_iter t i) hss.

    (** The invocations of a WRd write ([v] is the value its [rd Sq_i]
        returns), distinct handles. *)
    Definition WrShape (t : tid) (i vx vy : nat) (evs : list (ThreadEvent ES)) : Prop :=
      exists v h0 h1 h2 h3 h4 h5 h6, NoDup [h0; h1; h2; h3; h4; h5; h6] /\
        evs = [IE t h0 (sRd (Sq i)); IE t h1 (sWr (Sq i) (v + 1)); IE t h2 sWmb; IE t h3 (sWr (Sx i) vx);
               IE t h4 (sWr (Sy i) vy); IE t h5 sWmb; IE t h6 (sWr (Sq i) (v + 2))].

    (** The footprint [Ω] of [MethodProvable].  A write by a thread other
        than [tw i] has the footprint [False]: its body [div] never runs,
        and [mp_PI] is vacuous (P1 enters here). *)
    Definition Osl (t : tid) (op : FOp) (h : nat) (evs : list (ThreadEvent ES)) : Prop :=
      match op with
      | fR i => RdShape t i evs
      | fW i vx vy => t = tw i /\ WrShape t i vx vy evs
      end.

    (** The postcondition [Q]: [k] has linearized with result [r]
        (returned, or about to return through [psa_ret]).  For reads
        superseded by [Qrd] (Part 9, B-6); still the write
        postcondition. *)
    Definition Qsl (k : CallKey FS) (op : FOp) (r : far op) : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\
        (lin_lookup k (@ls_linr FS op r) P \/ (lin_lookup k (@ls_lini FS op) P /\ In (RelaxedTraceLin.Build_Op k op r) Pf)).


    (** ** Part 2. Ownership, the pool, the age order *)

    Lemma callkey_eq_dec (k1 k2 : CallKey FS) : {k1 = k2} + {k1 <> k2}.
    Proof.
      destruct k1 as [t1 h1], k2 as [t2 h2].
      destruct (Pos.eq_dec t1 t2) as [-> | Ht]; [| right; congruence].
      destruct (Nat.eq_dec h1 h2) as [-> | Hh]; [left; reflexivity | right; congruence].
    Qed.

    Lemma owns_incl k Q (γ γ' : Ghost ES FS) : incl γ' γ -> Owns k Q γ' -> Owns k Q γ.
    Proof. intros Hi (e & He & Ho & Hq). exists e. split; [exact (Hi e He) | auto]. Qed.

    Lemma owns_frame k Q (γ γ' : Ghost ES FS) :
      (forall e, se_owner e = k -> (In e γ <-> In e γ')) -> (Owns k Q γ <-> Owns k Q γ').
    Proof.
      intros Hf. split; intros (e & He & Ho & Hq); exists e; (split; [apply (Hf e Ho); exact He | auto]).
    Qed.

    Lemma owns_app_other k k0 Q (γ γn : Ghost ES FS) :
      (forall e, In e γn -> se_owner e = k0) -> k <> k0 -> (Owns k Q (γ ++ γn) <-> Owns k Q γ).
    Proof.
      intros Hn Hne. split.
      - intros (e & He & Ho & Hq). apply in_app_or in He as [He | He]; [exists e; auto |].
        exfalso. apply Hne. rewrite <- Ho. exact (Hn e He).
      - intros (e & He & Ho & Hq). exists e. split; [apply in_or_app; left; exact He | auto].
    Qed.

    Lemma owns_app_r k Q (γ γn : Ghost ES FS) : Owns k Q γn -> Owns k Q (γ ++ γn).
    Proof. intros (e & He & Ho & Hq). exists e. split; [apply in_or_app; right; exact He | auto]. Qed.

    Lemma owns_emit k Q (g1 g2 : Ghost ES FS) x :
      Owns k Q (g1 ++ x :: g2) -> Owns k Q (g1 ++ g2) \/ (se_owner x = k /\ Q (gop x)).
    Proof.
      intros (e & He & Ho & Hq). apply in_app_or in He as [He | [<- | He]].
      - left. exists e. split; [apply in_or_app; left; exact He | auto].
      - right. auto.
      - left. exists e. split; [apply in_or_app; right; exact He | auto].
    Qed.

    Lemma incl_remove_mid (g1 g2 : Ghost ES FS) x : incl (g1 ++ g2) (g1 ++ x :: g2).
    Proof. intros y Hy. apply in_app_or in Hy as [Hy | Hy]; apply in_or_app; [left | right; right]; exact Hy. Qed.

    Lemma owns_emit_other k Q (g1 g2 : Ghost ES FS) x :
      se_owner x <> k -> (Owns k Q (g1 ++ x :: g2) <-> Owns k Q (g1 ++ g2)).
    Proof.
      intros Hne. split.
      - intros H. destruct (owns_emit k Q g1 g2 x H) as [H' | [Ho _]]; [exact H' | contradiction].
      - apply owns_incl. apply incl_remove_mid.
    Qed.

    Lemma owns_dec k Q (γ : Ghost ES FS) : (forall o, {Q o} + {~ Q o}) -> {Owns k Q γ} + {~ Owns k Q γ}.
    Proof.
      intros Hq. induction γ as [| e γ IH].
      - right. intros (e & [] & _).
      - destruct IH as [IH | IH].
        + left. apply (owns_incl k Q (e :: γ) γ); [intros x Hx; right; exact Hx | exact IH].
        + destruct (callkey_eq_dec (se_owner e) k) as [Ho | Ho]; [destruct (Hq (gop e)) as [Hqe | Hqe] |].
          * left. exists e. split; [left; reflexivity | auto].
          * right. intros (e' & [<- | He'] & Ho' & Hq'); [contradiction | apply IH; exists e'; auto].
          * right. intros (e' & [<- | He'] & Ho' & Hq'); [contradiction | apply IH; exists e'; auto].
    Qed.

    Lemma isRmb_dec o : {isRmb o} + {~ isRmb o}.
    Proof. unfold isRmb. destruct o; first [left; reflexivity | right; discriminate]. Qed.

    Lemma isWmb_dec o : {isWmb o} + {~ isWmb o}.
    Proof. unfold isWmb. destruct o; first [left; reflexivity | right; discriminate]. Qed.

    Lemma isRdSq_dec i o : {isRdSq i o} + {~ isRdSq i o}.
    Proof.
      unfold isRdSq. destruct o as [l | l v | |]; try (right; discriminate).
      destruct (SLoc_eq_dec l (Sq i)) as [-> | Hl]; [left; reflexivity | right; congruence].
    Qed.

    Lemma wrsq_atsq i o : isWrSq i o -> atSq i o.
    Proof. intros (v & ->). reflexivity. Qed.

    Lemma rdsq_atsq i o : isRdSq i o -> atSq i o.
    Proof. intros ->. reflexivity. Qed.

    (** [key_older] is total on the domain of a well-formed pool. *)
    Lemma key_older_total (ks : list (CallKey FS)) k1 k2 :
      In k1 ks -> In k2 ks -> k1 <> k2 -> key_older ks k1 k2 \/ key_older ks k2 k1.
    Proof.
      unfold key_older. induction ks as [| k ks IH]; intros H1 H2 Hne; [destruct H1 |].
      destruct H1 as [<- | H1], H2 as [<- | H2].
      - contradiction.
      - right. apply subseq_keep. apply subseq_single. exact H2.
      - left. apply subseq_keep. apply subseq_single. exact H1.
      - destruct (IH H1 H2 Hne) as [H | H]; [left | right]; apply subseq_skip; exact H.
    Qed.

    Lemma lookup_in_dom k ls (P : LinPool FS) : lin_lookup k ls P -> In k (lin_domain P).
    Proof. intros H. unfold lin_domain. rewrite <- (lin_key_make_lin_entry k ls). apply in_map. exact H. Qed.

    Lemma hasop_in_dom k o (P : LinPool FS) : HasOp k o P -> In k (lin_domain P).
    Proof. intros (ls & H & _). exact (lookup_in_dom k ls P H). Qed.

    Lemma entry_eta (e : LinEntry FS) : e = make_lin_entry (lin_key e) (lin_state FS e).
    Proof. destruct e. reflexivity. Qed.

    Lemma entry_lookup (e : LinEntry FS) (P : LinPool FS) : In e P -> lin_lookup (lin_key e) (lin_state FS e) P.
    Proof. intros H. unfold lin_lookup. rewrite <- entry_eta. exact H. Qed.

    Lemma hasop_unique k o1 o2 (P : LinPool FS) : lin_pool_well_formed P -> HasOp k o1 P -> HasOp k o2 P -> o1 = o2.
    Proof.
      intros Hwf (ls1 & H1 & <-) (ls2 & H2 & <-).
      rewrite (RelaxedHoareInherit.lookup_unique_gen P k ls1 ls2 Hwf H1 H2). reflexivity.
    Qed.

    Lemma iswr_unique i j k (P : LinPool FS) : lin_pool_well_formed P -> IsWr i k P -> IsWr j k P -> i = j.
    Proof.
      intros Hwf (vx & vy & H1) (wx & wy & H2). pose proof (hasop_unique k _ _ P Hwf H1 H2) as E.
      injection E as E _ _. exact E.
    Qed.

    Lemma make_entry_inj k1 k2 ls1 ls2 :
      @make_lin_entry FS k1 ls1 = make_lin_entry k2 ls2 -> k1 = k2 /\ ls1 = ls2.
    Proof.
      intros H. pose proof (f_equal lin_key H) as Hk. rewrite !lin_key_make_lin_entry in Hk.
      split; [exact Hk |]. exact (f_equal (lin_state FS) H).
    Qed.

    Lemma lin_update_incl k b a (P P' : LinPool FS) e :
      lin_update k b a P P' -> In e P' -> In e P \/ e = make_lin_entry k a.
    Proof.
      induction 1 as [tail | e0 P0 P0' Hne Hu IH]; intros He.
      - destruct He as [<- | He]; [right; reflexivity | left; right; exact He].
      - destruct He as [<- | He]; [left; left; reflexivity |].
        destruct (IH He) as [H | H]; [left; right; exact H | right; exact H].
    Qed.

    Lemma lin_update_lookup_back k b a (P P' : LinPool FS) k' ls :
      lin_update k b a P P' -> k' <> k -> lin_lookup k' ls P' -> lin_lookup k' ls P.
    Proof.
      intros Hu Hne Hl. destruct (lin_update_incl k b a P P' _ Hu Hl) as [H | H]; [exact H |].
      exfalso. apply Hne. exact (proj1 (make_entry_inj _ _ _ _ H)).
    Qed.

    Lemma lin_remove_incl k st (P P' : LinPool FS) : lin_remove k st P P' -> incl P' P.
    Proof.
      induction 1 as [tail | e0 P0 P0' Hne Hr IH]; intros x Hx; [right; exact Hx |].
      destruct Hx as [<- | Hx]; [left; reflexivity | right; exact (IH x Hx)].
    Qed.

    (** Phase changes that keep the operation keep [HasOp]. *)
    Lemma hasop_update k b a (P P' : LinPool FS) k' o :
      lin_pool_well_formed P -> lin_update k b a P P' -> lsop a = lsop b ->
      (HasOp k' o P <-> HasOp k' o P').
    Proof.
      intros Hwf Hu Hab. assert (Hwf' : lin_pool_well_formed P').
      { exact (lin_update_well_formed _ _ _ _ _ Hu Hwf). }
      split.
      - intros (ls & Hl & Ho). destruct (callkey_eq_dec k' k) as [-> | Hne].
        + rewrite (RelaxedHoareInherit.lookup_unique_gen P k ls b Hwf Hl (lin_update_source _ _ _ _ _ Hu)) in Ho.
          exists a. split; [exact (lin_update_target _ _ _ _ _ Hu) | rewrite Hab; exact Ho].
        + exists ls. split; [exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu Hne Hl) | exact Ho].
      - intros (ls & Hl & Ho). destruct (callkey_eq_dec k' k) as [-> | Hne].
        + rewrite (RelaxedHoareInherit.lookup_unique_gen P' k ls a Hwf' Hl (lin_update_target _ _ _ _ _ Hu)) in Ho.
          exists b. split; [exact (lin_update_source _ _ _ _ _ Hu) | rewrite <- Hab; exact Ho].
        + exists ls. split; [exact (lin_update_lookup_back k b a P P' k' ls Hu Hne Hl) | exact Ho].
    Qed.

    Lemma coup_ext k ls (γ γ' : Ghost ES FS) :
      (forall Q, Owns k Q γ <-> Owns k Q γ') -> Coup k ls γ -> Coup k ls γ'.
    Proof.
      intros Hq. unfold Coup. destruct (lsop ls) as [i vx vy | i].
      - intros H Hi. destruct (H Hi) as [H1 H2]. split; apply Hq; assumption.
      - rewrite (Hq isRmb). exact (fun H => H).
    Qed.

    Lemma holder_ext i k (P P' : LinPool FS) (γ γ' : Ghost ES FS) :
      (forall o, HasOp k o P -> HasOp k o P') -> (forall Q, Owns k Q γ <-> Owns k Q γ') ->
      Holder i k P γ -> Holder i k P' γ'.
    Proof.
      intros Hp Hq (( vx & vy & Hw) & Hr & Hs). split; [exists vx, vy; exact (Hp _ Hw) |].
      split; [rewrite <- Hq; exact Hr | rewrite <- Hq; exact Hs].
    Qed.

    (** ** Part 3. Consequences of the invariant *)

    Section Consequences.
      Context (m : Regs) (A : AS) (Pf : list OpF) (P : LinPool FS) (γ : Ghost ES FS).
      Context (HI : IslC m A Pf P γ).

      Lemma isl_tw k i vx vy : HasOp k (fW i vx vy) P -> fst k = tw i.
      Proof.
        intros (ls & Hl & Ho). exact (ic_tw _ _ _ _ _ HI (make_lin_entry k ls) i vx vy Hl Ho).
      Qed.

      Lemma iswr_tw i k : IsWr i k P -> fst k = tw i.
      Proof. intros (vx & vy & H). exact (isl_tw k i vx vy H). Qed.

      (** At most one holder per instance (from [WOrd] and P1). *)
      Theorem holder_unique i k1 k2 : Holder i k1 P γ -> Holder i k2 P γ -> k1 = k2.
      Proof.
        intros (Hw1 & Hr1 & Hs1) (Hw2 & Hr2 & Hs2).
        destruct (callkey_eq_dec k1 k2) as [-> | Hne]; [reflexivity | exfalso].
        destruct Hw1 as (vx1 & vy1 & Hw1'), Hw2 as (vx2 & vy2 & Hw2').
        destruct (key_older_total (lin_domain P) k1 k2 (hasop_in_dom _ _ _ Hw1') (hasop_in_dom _ _ _ Hw2') Hne)
          as [Ho | Ho].
        - apply (ic_word _ _ _ _ _ HI i k1 k2 (ex_intro _ vx1 (ex_intro _ vy1 Hw1')) (ex_intro _ vx2 (ex_intro _ vy2 Hw2')) Ho Hr2).
          destruct Hs1 as (e & He & Hoe & Hq). exists e. split; [exact He |]. split; [exact Hoe | exact (wrsq_atsq _ _ Hq)].
        - apply (ic_word _ _ _ _ _ HI i k2 k1 (ex_intro _ vx2 (ex_intro _ vy2 Hw2')) (ex_intro _ vx1 (ex_intro _ vy1 Hw1')) Ho Hr1).
          destruct Hs2 as (e & He & Hoe & Hq). exists e. split; [exact He |]. split; [exact Hoe | exact (wrsq_atsq _ _ Hq)].
      Qed.

      (** A holder that has not linearized sees an even sequence number. *)
      Theorem holder_inv_even i k vx vy :
        Holder i k P γ -> lin_lookup k (@ls_inv FS (fW i vx vy)) P -> Nat.even (m (Sq i)) = true.
      Proof.
        intros Hh Hl. destruct (Nat.even (m (Sq i))) eqn:Ev; [reflexivity | exfalso].
        destruct (ic_jodd _ _ _ _ _ HI i Ev) as (k' & wx & wy & Hh' & Hop & Hnl & _).
        rewrite (holder_unique i k' k Hh' Hh) in Hop, Hnl.
        assert (Hop0 : HasOp k (fW i vx vy) P) by (exists (@ls_inv FS (fW i vx vy)); auto).
        pose proof (hasop_unique k _ _ P (ic_wf _ _ _ _ _ HI) Hop Hop0) as E. injection E as <- <-. exact (Hnl Hl).
      Qed.

      (** An odd sequence number determines the abstract value through the holder. *)
      Theorem holder_odd i k vx vy :
        Holder i k P γ -> HasOp k (fW i vx vy) P -> Nat.even (m (Sq i)) = false -> A i = (vx, vy).
      Proof.
        intros Hh Hop Ev. destruct (ic_jodd _ _ _ _ _ HI i Ev) as (k' & wx & wy & Hh' & Hop' & _ & HA).
        rewrite (holder_unique i k' k Hh' Hh) in Hop'.
        pose proof (hasop_unique k _ _ P (ic_wf _ _ _ _ _ HI) Hop Hop') as E. injection E as <- <-. exact HA.
      Qed.
    End Consequences.

    (** ** Part 4. The fields of [RLHL2Hyps] other than [h_sem], and the
        method-level premises [mp_PI], [mp_ret] *)

    Lemma seqmono_refl m A : SeqMono m m A A.
    Proof. intros i. split; [lia | intros _; split; [reflexivity | intros _; split; reflexivity]]. Qed.

    Lemma frozen_refl i m A : InstFrozen i m m A A.
    Proof. repeat split. Qed.

    (** [h_guar_rely]. *)
    Theorem gsl_rsl k k' s s' : k <> k' -> Gsl k s s' -> Rsl k' s s'.
    Proof.
      intros Hne (Hm & A & Pf & P & A' & Pf' & P' & Hp & Hp' & Hpool & Hrec & Hgh & Hos & Hhp & Hmono).
      assert (Hne' : k' <> k) by (intros E; apply Hne; symmetry; exact E).
      split; [exact Hm |]. exists A, Pf, P, A', Pf', P'. split; [exact Hp |]. split; [exact Hp' |].
      split; [intros ls Hl; exact (Hpool k' ls Hne' Hl) |].
      split; [intros o Ho Hin; apply Hrec; [rewrite Ho; exact Hne' | exact Hin] |].
      split; [intros e Ho; apply Hgh; rewrite Ho; exact Hne' |].
      split; [exact (Hos k') |].
      split; [intros i Hh; exact (Hhp i k' Hne' Hh) | exact Hmono].
    Qed.

    Lemma ghost_new_in_owner (k : CallKey FS) (tr : list (TaggedEvent ES)) e : In e (ghost_new k tr) -> se_owner e = k.
    Proof. apply ghost_new_owner. Qed.

    (** [h_invoke_rely]. *)
    Theorem invoke_rely k k' op tr ret s p' :
      k <> k' -> program_produces_tagged (fst k) (M2w rc si tw op (fst k)) tr ret -> Isl s ->
      poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
      Rsl k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr).
    Proof.
      intros Hne _ (A & Pf & P & Hp & _ & HI) Hinv. destruct k as [t h].
      rewrite Hp in Hinv. destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hinv) as [-> Hfr].
      split; [apply rt_refl |]. exists A, Pf, P, A, Pf, (make_lin_entry (t, h) (ls_inv op) :: P).
      cbn [ps_poss ps_mem ps_ghost fst snd]. split; [exact Hp |]. split; [reflexivity |].
      split; [intros ls Hl; right; exact Hl |].
      split; [auto |].
      split.
      { intros e Ho. split; [intros He; apply in_or_app; left; exact He |].
        intros He. apply in_app_or in He as [He | He]; [exact He | exfalso].
        apply Hne. rewrite <- Ho. symmetry. exact (ghost_new_in_owner _ _ _ He). }
      split; [apply (oldersub_invoke k' (t, h) _ P _ _ Hfr); [intros E; apply Hne; symmetry; exact E | apply ghost_new_owner] |].
      split; [intros i _; apply frozen_refl | apply seqmono_refl].
    Qed.

    (** [h_return_rely]. *)
    Theorem return_rely k k' op r s p2 :
      k <> k' -> Isl s -> poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
      Rsl k' s (ps_mem s, p2, ps_ghost s).
    Proof.
      intros Hne (A & Pf & P & Hp & _ & HI) Hret _. destruct k as [t h].
      rewrite Hp in Hret. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hret) as (P2 & -> & Hrem).
      split; [apply rt_refl |]. exists A, Pf, P, A, Pf, P2.
      cbn [ps_poss ps_mem ps_ghost fst snd]. split; [exact Hp |]. split; [reflexivity |].
      split; [intros ls Hl; apply (lin_remove_other_lookup _ _ _ _ _ _ Hrem); [intros E; apply Hne; symmetry; exact E | exact Hl] |].
      split; [auto |]. split; [intros e _; reflexivity |].
      split; [exact (oldersub_lin_remove k' _ _ P P2 _ Hrem) |].
      split; [intros i _; apply frozen_refl | apply seqmono_refl].
    Qed.

    (** [h_ok]. *)
    Theorem isl_ok s : Isl s -> exists v pool, ps_poss s = POk v pool /\ lin_pool_well_formed pool.
    Proof. intros (A & Pf & P & Hp & _ & HI). exists (A, Pf), P. split; [exact Hp | exact (ic_wf _ _ _ _ _ HI)]. Qed.

    (** [h_init]. *)
    Theorem isl_init : Isl (((regs0, []), []), POk (A0, []) [], []).
    Proof.
      exists A0, [], []. split; [reflexivity |]. split; [exact (eihl_rec_used_init (E := ES) δS regs0) |].
      constructor; cbn.
      - constructor.
      - apply gage_nil.
      - constructor.
      - intros o [].
      - constructor.
      - intros e [].
      - intros e i vx vy [].
      - intros i k1 k2 (vx & vy & ls & [] & _).
      - intros i _. reflexivity.
      - intros i Ev. discriminate Ev.
      - constructor.
    Qed.

    (** *** [mp_PI]: the state right after an overlay invocation *)

    Lemma owns_new k Q (evs : list (ThreadEvent ES)) ev :
      In ev evs -> Q (event_op (te_ev ES ev)) -> Owns k Q (map (Build_ScheduledEvent k) evs).
    Proof. intros Hin Hq. exists (Build_ScheduledEvent k ev). split; [apply in_map; exact Hin | auto]. Qed.

    Lemma hasop_cons_other k k' ls o (P : LinPool FS) :
      k' <> k -> HasOp k' o (make_lin_entry k ls :: P) -> HasOp k' o P.
    Proof.
      intros Hne (ls' & [Hl | Hl] & Ho); [| exists ls'; auto].
      exfalso. apply Hne. symmetry. exact (proj1 (make_entry_inj _ _ _ _ Hl)).
    Qed.

    Lemma hasop_cons x k o (P : LinPool FS) : HasOp k o P -> HasOp k o (x :: P).
    Proof. intros (ls & Hl & Ho). exists ls. split; [right; exact Hl | exact Ho]. Qed.

    Lemma rdshape_rmb t i evs : RdShape t i evs -> exists hu, In (IE t hu sRmb) evs.
    Proof.
      intros (hss & Hne & _ & ->). destruct hss as [| [[[[[hG hA] hX] hY] hB] hT] hss]; [contradiction |].
      exists hA. cbn. right. left. reflexivity.
    Qed.

    Lemma nodup_app_disj {X : Type} (l1 l2 : list X) :
      NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
    Proof.
      induction l1 as [| a l1 IH]; intros H1 H2 Hd; [exact H2 |]. cbn. apply NoDup_cons_iff in H1 as [Ha H1].
      constructor.
      - intros Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Ha Hin) | exact (Hd a (or_introl eq_refl) Hin)].
      - apply IH; [exact H1 | exact H2 | intros b Hb; apply Hd; right; exact Hb].
    Qed.

    Lemma nodup_map_inj {X Y : Type} (f : X -> Y) (l : list X) :
      (forall a b, f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
    Proof.
      intros Hf. induction 1 as [| a l Ha Hl IH]; cbn; constructor; [| exact IH].
      intros Hin. apply in_map_iff in Hin as (b & Hb & Hin). rewrite (Hf b a Hb) in Hin. exact (Ha Hin).
    Qed.

    Definition ie_handle (ev : ThreadEvent ES) : nat := event_handle (te_ev ES ev).

    Lemma rd_iter_handles t i hss : map ie_handle (flat_map (rd_iter t i) hss) = flat_map hs_list hss.
    Proof.
      induction hss as [| [[[[[hG hA] hX] hY] hB] hT] hss IH]; [reflexivity |].
      cbn [flat_map]. rewrite map_app, IH. reflexivity.
    Qed.

    (** The footprint has no duplicate invocation (distinct handles). *)
    Lemma osl_nodup t op h evs : Osl t op h evs -> NoDup evs.
    Proof.
      destruct op as [i vx vy | i]; cbn.
      - intros (_ & v & h0 & h1 & h2 & h3 & h4 & h5 & h6 & Hnd & ->). apply (NoDup_map_inv ie_handle). exact Hnd.
      - intros (hss & _ & Hnd & ->). apply (NoDup_map_inv ie_handle). rewrite rd_iter_handles. exact Hnd.
    Qed.

    Theorem isl_postinvoke t h op s : PostInvoke Isl (t, h) op (Osl t op h) s -> Isl s.
    Proof.
      intros (p0 & γ0 & evs & (A & Pf & P0 & Hp0 & Hru & HC) & Hinv & Hg & HΩ & Htid).
      cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, Hru, Hinv. subst p0.
      destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hinv) as [Hp Hfr].
      set (k := (t, h)) in *. set (γn := map (Build_ScheduledEvent k) evs) in *.
      assert (Hown : forall e, In e γn -> se_owner e = k).
      { intros e He. apply in_map_iff in He as (ev & <- & _). reflexivity. }
      assert (Hdom : forall k', In k' (lin_domain P0) -> k' <> k) by (intros k' Hk E; subst k'; exact (Hfr Hk)).
      assert (Htr : forall k' Q, In k' (lin_domain P0) -> (Owns k' Q (γ0 ++ γn) <-> Owns k' Q γ0))
        by (intros k' Q Hk; exact (owns_app_other k' k Q γ0 γn Hown (Hdom k' Hk))).
      assert (HnewW : forall i vx vy, op = fW i vx vy -> t = tw i /\ Owns k (isRdSq i) (γ0 ++ γn) /\
                        Owns k isWmb (γ0 ++ γn) /\ Owns k (atSq i) (γ0 ++ γn)).
      { intros i vx vy ->. destruct HΩ as (Ht & v & h0 & h1 & h2 & h3 & h4 & h5 & h6 & _ & Hevs).
        split; [exact Ht |].
        split; [apply owns_app_r; apply (owns_new k _ evs (IE t h0 (sRd (Sq i)))); [rewrite Hevs; left; reflexivity | reflexivity] |].
        split; [apply owns_app_r; apply (owns_new k _ evs (IE t h2 sWmb)); [rewrite Hevs; right; right; left; reflexivity | reflexivity] |].
        apply owns_app_r; apply (owns_new k _ evs (IE t h0 (sRd (Sq i)))); [rewrite Hevs; left; reflexivity | reflexivity]. }
      assert (HnewR : forall i, op = fR i -> Owns k isRmb (γ0 ++ γn)).
      { intros i ->. destruct (rdshape_rmb t i evs HΩ) as (hu & Hin).
        apply owns_app_r. exact (owns_new k _ _ _ Hin eq_refl). }
      exists A, Pf, (make_lin_entry k (ls_inv op) :: P0). split; [exact Hp |]. split; [exact Hru |].
      rewrite Hg. change (regs s) with (fst (fst (ps_mem s))). cbn [regs ps_mem fst snd] in HC.
      destruct HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd].
      constructor.
      - eapply lin_insert_well_formed; [constructor; exact Hfr | exact Hwf].
      - exact (gage_invoke k _ P0 γ0 γn Hfr Hown Hage).
      - apply Forall_app. split; [exact Hgwf |]. subst γn. apply Forall_map.
        eapply Forall_impl; [| exact Htid]. intros ev [Ht Hi]. split; [exact Ht | exact Hi].
      - intros o Ho. right. exact (Hrec o Ho).
      - exact Hrnd.
      - intros e [<- | He].
        + cbn [lin_state lin_key make_lin_entry]. change (lin_key (make_lin_entry k (ls_inv op))) with k.
          unfold Coup. cbn [lsop is_inv]. destruct op as [i vx vy | i].
          * intros _. destruct (HnewW i vx vy eq_refl) as (_ & _ & H1 & H2). split; assumption.
          * split; [intros _; exact (HnewR i eq_refl) | intros _; reflexivity].
        + apply (coup_ext (lin_key e) _ γ0); [| exact (Hcoup e He)].
          intros Q. symmetry. apply Htr. unfold lin_domain. apply in_map. exact He.
      - intros e i vx vy [<- | He] Ho; [| exact (Htw e i vx vy He Ho)].
        cbn in Ho |- *. exact (proj1 (HnewW i vx vy Ho)).
      - intros i k1 k2 Hw1 Hw2 Ho Hr2. cbn [lin_domain map] in Ho. rewrite lin_key_make_lin_entry in Ho.
        destruct (key_older_cons _ _ _ _ Ho) as [(-> & Hk1) | Ho'].
        + exfalso. apply Hr2. destruct Hw2 as (vx & vy & ls & [Hl | Hl] & Hop).
          * destruct (make_entry_inj _ _ _ _ Hl) as [_ <-]. cbn in Hop. subst op.
            exact (proj1 (proj2 (HnewW i vx vy eq_refl))).
          * exfalso. exact (Hfr (lookup_in_dom _ _ _ Hl)).
        + destruct (key_older_in _ _ _ Ho') as [Hk1 Hk2].
          assert (Hw1' : IsWr i k1 P0) by (destruct Hw1 as (vx & vy & Hw); exists vx, vy; exact (hasop_cons_other _ _ _ _ _ (Hdom _ Hk1) Hw)).
          assert (Hw2' : IsWr i k2 P0) by (destruct Hw2 as (vx & vy & Hw); exists vx, vy; exact (hasop_cons_other _ _ _ _ _ (Hdom _ Hk2) Hw)).
          rewrite (Htr k1 _ Hk1). apply (Hword i k1 k2 Hw1' Hw2' Ho'). rewrite <- (Htr k2 _ Hk2). exact Hr2.
      - exact Hjev.
      - intros i Ev. destruct (Hjodd i Ev) as (k0 & vx & vy & Hh & Hop & Hnl & HA).
        assert (Hk0 : In k0 (lin_domain P0)) by exact (hasop_in_dom _ _ _ Hop).
        exists k0, vx, vy. split; [| split; [exact (hasop_cons _ _ _ _ Hop) | split; [| exact HA]]].
        + apply (holder_ext i k0 P0 _ γ0); [intros o Ho; exact (hasop_cons _ _ _ _ Ho) | intros Q; symmetry; exact (Htr k0 Q Hk0) | exact Hh].
        + intros [Hl | Hl]; [| exact (Hnl Hl)]. apply (Hdom k0 Hk0). exact (eq_sym (proj1 (make_entry_inj _ _ _ _ Hl))).
      - apply nodup_app_disj; [exact Hgnd | | ].
        + subst γn. apply nodup_map_inj; [intros a b E; injection E as E; exact E | exact (osl_nodup t op h evs HΩ)].
        + intros e He Hn. subst γn. apply in_map_iff in Hn as (ev & <- & _). exact (Hfr (proj1 Hage _ He)).
    Qed.

    (** *** [mp_ret]: from [Qsl] to [RetCond] *)

    Lemma isl_return σ A Pf P P2 γ k ls :
      Isl (σ, POk (A, Pf) P, γ) -> lin_remove k ls P P2 -> NoOwn k γ ->
      (forall o : OpF, In o Pf -> okey o <> k) -> Isl (σ, POk (A, Pf) P2, γ).
    Proof.
      intros (A' & Pf' & P' & Hp & Hru & HC) Hrem Hno Hrk. cbn in Hp. injection Hp as <- <- <-.
      exists A, Pf, P2. split; [reflexivity |]. split; [exact Hru |]. cbn [regs ps_mem ps_ghost ps_poss fst snd] in HC |- *.
      destruct HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd].
      pose proof (lin_remove_incl _ _ _ _ Hrem) as Hincl.
      assert (Hback : forall k' o, HasOp k' o P2 -> HasOp k' o P).
      { intros k' o (ls' & Hl & Ho). exists ls'. split; [exact (Hincl _ Hl) | exact Ho]. }
      assert (Hfwd : forall k' o, k' <> k -> HasOp k' o P -> HasOp k' o P2).
      { intros k' o Hne (ls' & Hl & Ho). exists ls'. split; [exact (lin_remove_other_lookup _ _ _ _ _ _ Hrem Hne Hl) | exact Ho]. }
      constructor.
      - exact (lin_remove_well_formed _ _ _ _ Hrem Hwf).
      - exact (gage_lin_remove _ _ _ _ _ Hrem Hno Hage).
      - exact Hgwf.
      - intros o Ho. exact (lin_remove_other_lookup _ _ _ _ _ _ Hrem (Hrk o Ho) (Hrec o Ho)).
      - exact Hrnd.
      - intros e He. exact (Hcoup e (Hincl e He)).
      - intros e i vx vy He. exact (Htw e i vx vy (Hincl e He)).
      - intros i k1 k2 (vx1 & vy1 & H1) (vx2 & vy2 & H2) Ho Hr2.
        apply (Hword i k1 k2 (ex_intro _ vx1 (ex_intro _ vy1 (Hback _ _ H1))) (ex_intro _ vx2 (ex_intro _ vy2 (Hback _ _ H2))));
          [exact (key_older_mono _ _ _ _ (lin_remove_domain_subseq _ _ _ _ Hrem) Ho) | exact Hr2].
      - exact Hjev.
      - intros i Ev. destruct (Hjodd i Ev) as (k0 & vx & vy & Hh & Hop & Hnl & HA).
        assert (Hk0 : k0 <> k).
        { intros ->. destruct Hh as (_ & _ & (e & He & Ho & _)). exact (Hno e He Ho). }
        exists k0, vx, vy. split; [| split; [exact (Hfwd _ _ Hk0 Hop) | split; [intros Hl; exact (Hnl (Hincl _ Hl)) | exact HA]]].
        apply (holder_ext i k0 P _ γ); [intros o Ho; exact (Hfwd _ _ Hk0 Ho) | intros Q; reflexivity | exact Hh].
      - exact Hgnd.
    Qed.

    Lemma recs_not_linr σ A Pf P γ k op (r : far op) :
      Isl (σ, POk (A, Pf) P, γ) -> lin_lookup k (@ls_linr FS op r) P -> forall o : OpF, In o Pf -> okey o <> k.
    Proof.
      intros (A' & Pf' & P' & Hp & _ & HC) Hl o Ho Hk. cbn in Hp. injection Hp as <- <- <-.
      pose proof (ic_rec _ _ _ _ _ HC o Ho) as Hlo. rewrite Hk in Hlo.
      pose proof (RelaxedHoareInherit.lookup_unique_gen P k _ _ (ic_wf _ _ _ _ _ HC) Hl Hlo) as E. discriminate E.
    Qed.

    (** The abstract return step of [k] at [ls_lini op] with its record. *)
    Lemma isl_psa_ret (σ : State VE) (A : AS) (Pa Pb : list OpF) (P P' : LinPool FS) (γ : Ghost ES FS)
        (k : CallKey FS) (op : FOp) (r : far op) :
      Isl (σ, POk (A, Pa ++ @RelaxedTraceLin.Build_Op FS k op r :: Pb) P, γ) ->
      lin_update k (@ls_lini FS op) (@ls_linr FS op r) P P' ->
      Isl (σ, POk (A, Pa ++ Pb) P', γ).
    Proof.
      intros (A' & Pf' & P0 & Hp & Hru & HC) Hu. cbn in Hp. injection Hp as <- <- <-.
      exists A, (Pa ++ Pb), P'. split; [reflexivity |]. split; [exact Hru |]. cbn [regs ps_mem ps_ghost ps_poss fst snd] in HC |- *.
      destruct HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd].
      assert (Hkeys : lin_domain P = lin_domain P') by exact (lin_update_keys _ _ _ _ _ Hu).
      assert (Hrk : forall o : OpF, In o (Pa ++ Pb) -> okey o <> k).
      { intros o Ho Hk. rewrite map_app in Hrnd. cbn [map] in Hrnd. apply NoDup_remove_2 in Hrnd. apply Hrnd.
        cbn [RelaxedTraceLin.op_key]. rewrite <- map_app. apply in_map_iff. exists o. split; [exact Hk | exact Ho]. }
      assert (Hsub : forall o : OpF, In o (Pa ++ Pb) -> In o (Pa ++ RelaxedTraceLin.Build_Op k op r :: Pb))
        by (intros o Ho; apply in_app_or in Ho as [Ho | Ho]; apply in_or_app; [left | right; right]; exact Ho).
      assert (Hk_lini : lin_lookup k (@ls_lini FS op) P) by exact (lin_update_source _ _ _ _ _ Hu).
      assert (Hcoupk : Coup k (@ls_linr FS op r) γ).
      { pose proof (Hcoup _ Hk_lini) as Hc. cbn [lin_key lin_state make_lin_entry] in Hc.
        rewrite lin_key_make_lin_entry in Hc. exact Hc. }
      assert (Hop : forall k' o, HasOp k' o P <-> HasOp k' o P') by (intros k' o; exact (hasop_update _ _ _ _ _ k' o Hwf Hu eq_refl)).
      constructor.
      - exact (lin_update_well_formed _ _ _ _ _ Hu Hwf).
      - exact (gage_lin_update _ _ _ _ _ _ Hu Hage).
      - exact Hgwf.
      - intros o Ho. exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu (Hrk o Ho) (Hrec o (Hsub o Ho))).
      - rewrite map_app in Hrnd |- *. cbn [map] in Hrnd. exact (NoDup_remove_1 _ _ _ Hrnd).
      - intros e He. destruct (lin_update_incl _ _ _ _ _ _ Hu He) as [He0 | ->]; [exact (Hcoup e He0) |].
        rewrite lin_key_make_lin_entry. exact Hcoupk.
      - intros e i vx vy He Ho. destruct (lin_update_incl _ _ _ _ _ _ Hu He) as [He0 | ->]; [exact (Htw e i vx vy He0 Ho) |].
        exact (Htw _ i vx vy Hk_lini Ho).
      - intros i k1 k2 (vx1 & vy1 & H1) (vx2 & vy2 & H2) Ho Hr2.
        apply (Hword i k1 k2 (ex_intro _ vx1 (ex_intro _ vy1 (proj2 (Hop _ _) H1))) (ex_intro _ vx2 (ex_intro _ vy2 (proj2 (Hop _ _) H2))));
          [rewrite Hkeys; exact Ho | exact Hr2].
      - exact Hjev.
      - intros i Ev. destruct (Hjodd i Ev) as (k0 & vx & vy & Hh & Hop0 & Hnl & HA).
        exists k0, vx, vy. split; [| split; [exact (proj1 (Hop _ _) Hop0) | split; [| exact HA]]].
        + apply (holder_ext i k0 P _ γ); [intros o Ho; exact (proj1 (Hop _ _) Ho) | intros Q; reflexivity | exact Hh].
        + intros Hl. destruct (lin_update_incl _ _ _ _ _ _ Hu Hl) as [Hl0 | Hl0]; [exact (Hnl Hl0) |].
          destruct (make_entry_inj _ _ _ _ Hl0) as [_ E]. discriminate E.
      - exact Hgnd.
    Qed.

    Theorem qsl_ret t h op r s :
      Qsl (t, h) op r s -> Isl s -> NoOwn (t, h) (ps_ghost s) -> RetCond Isl Gsl (t, h) op r s.
    Proof.
      destruct s as [[σ p] γ]. intros (A & Pf & P & Hp & Hq) HI Hno. cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
      destruct Hq as [Hl | (Hl & Hrec)].
      - exists (POk (A, Pf) P). split; [apply rt_refl |]. split; [exists (A, Pf), P; split; [reflexivity | exact Hl] |].
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hret. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hret) as (P2 & -> & Hrem).
        exact (isl_return σ A Pf P P2 γ (t, h) _ HI Hrem Hno (recs_not_linr σ A Pf P γ (t, h) op r HI Hl)).
      - pose proof HI as (A' & Pf' & P0 & Hp0 & Hru & HC). cbn in Hp0. injection Hp0 as <- <- <-.
        destruct (RelaxedHoareInherit.lin_update_exists_gen (t, h) (@ls_lini FS op) (@ls_linr FS op r) P (ic_wf _ _ _ _ _ HC) Hl)
          as (P' & Hu).
        destruct (in_split _ _ Hrec) as (Pa & Pb & HPf). rewrite HPf in HI.
        assert (HI1 : Isl (σ, POk (A, Pa ++ Pb) P', γ)) by exact (isl_psa_ret σ A Pa Pb P P' γ (t, h) op r HI Hu).
        exists (POk (A, Pa ++ Pb) P'). split.
        { apply rt_step. exists (t, h). apply (psa_ret VF t h op r (A, Pf) (A, Pa ++ Pb) P P' Hu). cbn.
          exists Pa, Pb. split; [exact HPf | reflexivity]. }
        split; [exists (A, Pa ++ Pb), P'; split; [reflexivity | exact (lin_update_target _ _ _ _ _ Hu)] |].
        split; [exact HI1 |].
        split.
        { apply r_step. split; [apply rt_refl |]. exists A, Pf, P, A, (Pa ++ Pb), P'.
          cbn [ps_poss ps_mem ps_ghost fst snd]. split; [reflexivity |]. split; [reflexivity |].
          split; [intros k' ls Hne Hl'; exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu Hne Hl') |].
          split.
          { intros o Ho Hin. rewrite HPf in Hin. apply in_app_or in Hin as [Hin | [<- | Hin]];
              [apply in_or_app; left; exact Hin | contradiction Ho; reflexivity | apply in_or_app; right; exact Hin]. }
          split; [intros e _; reflexivity |].
          split; [intros k'; apply oldersub_same_domain; [symmetry; exact (lin_update_keys _ _ _ _ _ Hu) | intros x Hx; exact Hx] |].
          split; [intros i k' _ _; apply frozen_refl | apply seqmono_refl]. }
        intros p2 Hret. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hret) as (P2 & -> & Hrem).
        apply (isl_return σ A (Pa ++ Pb) P' P2 γ (t, h) _ HI1 Hrem Hno).
        exact (recs_not_linr σ A (Pa ++ Pb) P' γ (t, h) op r HI1 (lin_update_target _ _ _ _ _ Hu)).
    Qed.

    (** *** Assembly *)

    (** A derivation of the body gives [MethodProvable] with the frozen
        footprint [Osl] and postcondition [Qsl] ([mp_PI], [mp_ret] are
        [isl_postinvoke], [qsl_ret]).  For reads superseded by
        [sl2_method_provable_op] (Part 9, B-6: no read derivation reaches
        [Qsl], argued); kept unchanged. *)
    Theorem sl2_method_provable t op :
      (forall h, RProvable Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) op (Osl t op h))
         (fun a Γ H => Close Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) op (Osl t op h)) (fun r => Qsl (t, h) op r) a Γ H /\
                       Osl t op h (own_invs Γ))
         [] empty_store (M2w rc si tw op t)) ->
      MethodProvable Isl Rsl Gsl (M2w rc si tw) t op (fun h => Osl t op h) (fun h r => Qsl (t, h) op r).
    Proof.
      intros Ht. constructor.
      - intros h s Hs. exact (isl_postinvoke t h op s Hs).
      - intros h r s Hq HI Hno. exact (qsl_ret t h op r s Hq HI Hno).
      - exact Ht.
    Qed.

    (** The assembly through soundness: [MethodProvable] for every thread
        and operation gives every field of [RLHL2Hyps] ([h_sem] by
        [RelaxedHoareSound.method_sound]).  No hypothesis on [si].
        Superseded by [sl2rd_rlhl2_of_provable_rd] (Part 9: any footprint
        and postcondition per operation; here the read premise asks for
        [Qsl], unreachable by B-6, argued); kept unchanged. *)
    Theorem sl2rd_rlhl2_of_provable :
      (forall t op, MethodProvable Isl Rsl Gsl (M2w rc si tw) t op (fun h => Osl t op h) (fun h r => Qsl (t, h) op r)) ->
      RLHL2Hyps (VE := VE) (VF := VF) Isl Rsl Gsl (M2w rc si tw) ((regs0, []), []) (A0, []).
    Proof.
      intros Hmp. constructor.
      - intros t op. exact (method_sound Isl Rsl Gsl (M2w rc si tw) t op _ _ (Hmp t op)).
      - intros k k' s s' Hne HG. exact (gsl_rsl k k' s s' Hne HG).
      - exact invoke_rely.
      - exact return_rely.
      - exact isl_ok.
      - exact isl_init.
    Qed.

    (** ** Part 5. Readiness at the linearization points *)

    Lemma wmb_blocks_wr l v : ~ sindep rc sWmb (sWr l v).
    Proof. unfold sindep. destruct rc; cbn; discriminate. Qed.

    Lemma rmb_blocks_rmb : ~ sindep rc sRmb sRmb.
    Proof. unfold sindep. destruct rc; cbn; discriminate. Qed.

    Lemma blocks_of_gwf (e1 e2 : ScheduledEvent ES FS) :
      RelaxedHoareInherit.gwf e1 -> RelaxedHoareInherit.gwf e2 -> fst (se_owner e1) = fst (se_owner e2) ->
      ~ sindep rc (gop e1) (gop e2) -> inv_blocks (se_event e1) (se_event e2).
    Proof.
      destruct e1 as [k1 [t1 [h1 o1 | h1 o1 r1]]], e2 as [k2 [t2 [h2 o2 | h2 o2 r2]]];
        unfold RelaxedHoareInherit.gwf, gop, inv_blocks, is_invocation; cbn; intros [H1 I1] [H2 I2] Ht Hn;
        try contradiction.
      split; [congruence | exact Hn].
    Qed.

    Lemma blocks_ie (e : ScheduledEvent ES FS) t hu o :
      RelaxedHoareInherit.gwf e -> fst (se_owner e) = t -> ~ sindep rc (gop e) o -> inv_blocks (se_event e) (IE t hu o).
    Proof.
      destruct e as [k1 [t1 [h1 o1 | h1 o1 r1]]]; unfold RelaxedHoareInherit.gwf, gop, inv_blocks, is_invocation, IE; cbn;
        intros [H1 I1] Ht Hn; [| contradiction]. split; [congruence | exact Hn].
    Qed.

    Lemma ghost_emit_ie k t hu o (γ γ' : Ghost ES FS) :
      ghost_emit k (IE t hu o) γ γ' ->
      exists g1 g2, γ = g1 ++ Build_ScheduledEvent k (IE t hu o) :: g2 /\ γ' = g1 ++ g2 /\
        Forall (fun e => ~ inv_blocks (se_event e) (IE t hu o)) g1.
    Proof. intros H. exact H. Qed.

    Lemma coup_inv k o (γ : Ghost ES FS) :
      Coup k (@ls_inv FS o) γ ->
      match o with fR _ => Owns k isRmb γ | fW i _ _ => Owns k isWmb γ /\ Owns k (atSq i) γ end.
    Proof. unfold Coup. destruct o as [i vx vy | i]; cbn; intros H; [exact (H eq_refl) | exact (proj1 H eq_refl)]. Qed.

    (** At the linearization point of a write ([wr Sq_i (v+1)]): an older
        same-thread [ls_inv] write owns a pending [wmb] (direct block,
        Wmb→DW); an older same-thread [ls_inv] read owns a pending [rmb],
        which blocks the write's earlier [rd Sq_i] (recorded block,
        Rmb→DR, carried by [RecNB]).  The overlay relation is not used. *)
    Theorem ready_write m A Pf P (γ γ' : Ghost ES FS) t h i vx vy h0 h1 w :
      IslC m A Pf P γ -> lin_lookup (t, h) (@ls_inv FS (fW i vx vy)) P ->
      ghost_emit (t, h) (IE t h1 (sWr (Sq i) w)) γ γ' ->
      RecNB P (t, h) (IE t h0 (sRd (Sq i))) γ ->
      exists P', lin_invoke_update t h (fW i vx vy) P P' /\ lin_pool_well_formed P'.
    Proof.
      intros HC Hl Hge Hrec. destruct (ghost_emit_ie _ _ _ _ _ _ Hge) as (g1 & g2 & Hγ & _ & Hnb).
      apply (emit_ready_rec P γ g1 g2 t h (fW i vx vy) (IE t h1 (sWr (Sq i) w)) (ic_wf _ _ _ _ _ HC) Hl (ic_age _ _ _ _ _ HC));
        [| exact Hγ | exact Hnb].
      intros k1 o1 Ht Ho Hl1.
      pose proof (coup_inv k1 o1 γ ltac:(pose proof (ic_coup _ _ _ _ _ HC _ Hl1) as Hc; rewrite lin_key_make_lin_entry in Hc; exact Hc)) as Hc.
      pose proof (ic_gwf _ _ _ _ _ HC) as Hgwf. rewrite Forall_forall in Hgwf.
      destruct o1 as [j wx wy | j].
      - destruct Hc as [(e & He & Hoe & Hq) _]. right. left. exists e. split; [exact He |]. split; [exact Hoe |].
        apply blocks_ie; [exact (Hgwf e He) | rewrite Hoe; exact Ht |]. unfold isWmb in Hq. rewrite Hq. apply wmb_blocks_wr.
      - destruct Hc as (e & He & Hoe & Hq). right. right. exists (IE t h0 (sRd (Sq i))), e.
        split; [exact Hrec |]. split; [exact He |]. split; [exact Hoe |].
        apply blocks_ie; [exact (Hgwf e He) | rewrite Hoe; exact Ht |]. unfold isRmb in Hq. rewrite Hq. apply rmb_blocks_rd.
    Qed.

    (** At the linearization point of a read (its final [rmb]): an older
        same-thread [ls_inv] read owns a pending [rmb] (direct block,
        Rmb/Rmb); an older same-thread [ls_inv] write of the same instance
        owns a pending access to [Sq_i], which blocks the read's earlier
        [rd Sq_i] of the same iteration (recorded block, same location);
        an older [ls_inv] write of another instance is crossed through the
        overlay relation, which must contain [slRA]. *)
    Theorem ready_read (Hsi : forall o o', slRA o o' -> si o o') m A Pf P (γ γ' : Ghost ES FS) t h i hG hB :
      IslC m A Pf P γ -> lin_lookup (t, h) (@ls_inv FS (fR i)) P ->
      ghost_emit (t, h) (IE t hB sRmb) γ γ' ->
      RecNB P (t, h) (IE t hG (sRd (Sq i))) γ ->
      exists P', lin_invoke_update t h (fR i) P P' /\ lin_pool_well_formed P'.
    Proof.
      intros HC Hl Hge Hrec. destruct (ghost_emit_ie _ _ _ _ _ _ Hge) as (g1 & g2 & Hγ & _ & Hnb).
      apply (emit_ready_rec P γ g1 g2 t h (fR i) (IE t hB sRmb) (ic_wf _ _ _ _ _ HC) Hl (ic_age _ _ _ _ _ HC));
        [| exact Hγ | exact Hnb].
      intros k1 o1 Ht Ho Hl1.
      pose proof (coup_inv k1 o1 γ ltac:(pose proof (ic_coup _ _ _ _ _ HC _ Hl1) as Hc; rewrite lin_key_make_lin_entry in Hc; exact Hc)) as Hc.
      pose proof (ic_gwf _ _ _ _ _ HC) as Hgwf. rewrite Forall_forall in Hgwf.
      destruct o1 as [j wx wy | j].
      - destruct (Nat.eq_dec j i) as [-> | Hji].
        + destruct Hc as [_ (e & He & Hoe & Hq)]. right. right. exists (IE t hG (sRd (Sq i))), e.
          split; [exact Hrec |]. split; [exact He |]. split; [exact Hoe |].
          apply blocks_ie; [exact (Hgwf e He) | rewrite Hoe; exact Ht |]. apply sindep_same_loc. exact Hq.
        + left. apply Hsi. exact Hji.
      - destruct Hc as (e & He & Hoe & Hq). right. left. exists e. split; [exact He |]. split; [exact Hoe |].
        apply blocks_ie; [exact (Hgwf e He) | rewrite Hoe; exact Ht |]. unfold isRmb in Hq. rewrite Hq. apply rmb_blocks_rmb.
    Qed.

    (** ** Part 6. The stability kit *)

    Definition KLook (k : CallKey FS) (ls : LinState FS) : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ lin_lookup k ls P.

    Definition KRec (o : OpF) : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ In o Pf.

    Definition KOwns (k : CallKey FS) (Q : SOp -> Prop) : Assn VE VF := fun s => Owns k Q (ps_ghost s).

    Definition KNotOwns (k : CallKey FS) (Q : SOp -> Prop) : Assn VE VF := fun s => ~ Owns k Q (ps_ghost s).

    Definition KHolder (i : nat) (k : CallKey FS) : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ Holder i k P (ps_ghost s).

    Definition KRecNB (k : CallKey FS) (ev : ThreadEvent ES) : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ RecNB P k ev (ps_ghost s).

    Definition KSeqGe (i v : nat) : Assn VE VF := fun s => v <= regs s (Sq i).

    (** The value fact of a reader: the sequence number has not dropped
        below [v], and while it is [v] (even) the projection [pr] of the
        abstract value of instance [i] is [x]. *)
    Definition KRdVal (i v : nat) (pr : nat * nat -> nat) (x : nat) : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ v <= regs s (Sq i) /\
        (regs s (Sq i) = v -> Nat.even v = true -> pr (A i) = x).

    (** A fact [φ] about the registers and the abstract value of instance
        [i], while [k] holds it. *)
    Definition KHeld (i : nat) (k : CallKey FS) (φ : nat -> nat -> nat -> nat * nat -> Prop) : Assn VE VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ Holder i k P (ps_ghost s) /\
        φ (regs s (Sq i)) (regs s (Sx i)) (regs s (Sy i)) (A i).

    Definition KMine (key : CallKey ES) (x0 : RelaxedTraceLin.Op ES) : Assn VE VF := fun s =>
      eihl_mine (E := ES) δS key x0 (ps_mem s).

    (** The prophesied response [w] of a read of [l] on [key] is wrong: the
        record of [key] holds another value.  Stable under [Rsl] and every
        [Gsl], and refuted by the response itself ([kdoomrd_refuted]); a
        derivation uses it as the alternative to the identified fact on the
        edge from a read to its own response ([good_or_doom]).  This is the
        only place where a record value is identified with a response
        value. *)
    Definition KDoomRd (key : CallKey ES) (l : SLoc) (w : nat) : Assn VE VF := fun s =>
      exists v, v <> w /\ eihl_mine (E := ES) δS key (@RelaxedTraceLin.Build_Op ES key (sRd l) v) (ps_mem s).

    Section Stab.
      Context (k : CallKey FS).

      Lemma klook_stable ls : Stable Isl (Rsl k) (KLook k ls).
      Proof.
        intros s s' (A & Pf & P & Hp & Hl) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & Hlk & _) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' | exact (Hlk ls Hl)].
      Qed.

      Lemma krec_stable o : okey o = k -> Stable Isl (Rsl k) (KRec o).
      Proof.
        intros Ho s s' (A & Pf & P & Hp & Hin) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & _ & Hrec & _) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' | exact (Hrec o Ho Hin)].
      Qed.

      Lemma kowns_stable Q : Stable Isl (Rsl k) (KOwns k Q).
      Proof.
        intros s s' Hs (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & _ & _ & _ & _ & Hgh & _) _.
        unfold KOwns in *. rewrite <- (owns_frame k Q _ _ Hgh). exact Hs.
      Qed.

      Lemma knotowns_stable Q : Stable Isl (Rsl k) (KNotOwns k Q).
      Proof.
        intros s s' Hs (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & _ & _ & _ & _ & Hgh & _) _.
        unfold KNotOwns in *. rewrite <- (owns_frame k Q _ _ Hgh). exact Hs.
      Qed.

      Lemma kholder_stable i : Stable Isl (Rsl k) (KHolder i k).
      Proof.
        intros s s' (A & Pf & P & Hp & Hh) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & Hlk & _ & Hgh & _) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' |].
        apply (holder_ext i k P P1' (ps_ghost s)); [| intros Q; exact (owns_frame k Q _ _ Hgh) | exact Hh].
        intros o (ls & Hl & Ho). exists ls. split; [exact (Hlk ls Hl) | exact Ho].
      Qed.

      Lemma krecnb_stable_r ev : Stable Isl (Rsl k) (KRecNB k ev).
      Proof.
        intros s s' (A & Pf & P & Hp & Hr) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & _ & _ & _ & Hos & _) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' |].
        exact (recnb_oldersub k P _ P1' _ ev Hos Hr).
      Qed.

      Lemma krecnb_stable_g k' ev : Stable Isl (Gsl k') (KRecNB k ev).
      Proof.
        intros s s' (A & Pf & P & Hp & Hr) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & _ & _ & _ & Hos & _) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' |].
        exact (recnb_oldersub k P _ P1' _ ev (Hos k) Hr).
      Qed.

      Lemma kseqge_stable_r i v : Stable Isl (Rsl k) (KSeqGe i v).
      Proof.
        intros s s' Hs (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & _ & _ & _ & _ & _ & _ & _ & Hmono) _.
        unfold KSeqGe in *. pose proof (proj1 (Hmono i)). lia.
      Qed.

      Lemma kseqge_stable_g k' i v : Stable Isl (Gsl k') (KSeqGe i v).
      Proof.
        intros s s' Hs (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & _ & _ & _ & _ & _ & _ & _ & Hmono) _.
        unfold KSeqGe in *. pose proof (proj1 (Hmono i)). lia.
      Qed.

      Lemma krdval_of_mono i v (pr : nat * nat -> nat) x (A A' : AS) (m m' : Regs) :
        SeqMono m m' A A' -> v <= m (Sq i) -> (m (Sq i) = v -> Nat.even v = true -> pr (A i) = x) ->
        v <= m' (Sq i) /\ (m' (Sq i) = v -> Nat.even v = true -> pr (A' i) = x).
      Proof.
        intros Hmono Hle Hv. destruct (Hmono i) as [Hge Heq]. split; [lia |].
        intros Hm Ev. assert (Hm0 : m (Sq i) = v) by lia. rewrite (proj1 (Heq ltac:(lia))). exact (Hv Hm0 Ev).
      Qed.

      Lemma krdval_stable_r i v pr x : Stable Isl (Rsl k) (KRdVal i v pr x).
      Proof.
        intros s s' (A & Pf & P & Hp & Hle & Hv) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & _ & _ & _ & _ & _ & Hmono) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' |].
        exact (krdval_of_mono i v pr x _ _ _ _ Hmono Hle Hv).
      Qed.

      Lemma krdval_stable_g k' i v pr x : Stable Isl (Gsl k') (KRdVal i v pr x).
      Proof.
        intros s s' (A & Pf & P & Hp & Hle & Hv) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & _ & _ & _ & _ & _ & Hmono) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' |].
        exact (krdval_of_mono i v pr x _ _ _ _ Hmono Hle Hv).
      Qed.

      Lemma kheld_stable i φ : Stable Isl (Rsl k) (KHeld i k φ).
      Proof.
        intros s s' (A & Pf & P & Hp & Hh & Hφ) (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & Hlk & _ & Hgh & _ & Hhp & _) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1 Pf1 P1. exists A1', Pf1', P1'. split; [exact Hp1' |].
        destruct (Hhp i Hh) as (E1 & E2 & E3 & E4). split.
        - apply (holder_ext i k P P1' (ps_ghost s)); [| intros Q; exact (owns_frame k Q _ _ Hgh) | exact Hh].
          intros o (ls & Hl & Ho). exists ls. split; [exact (Hlk ls Hl) | exact Ho].
        - rewrite E1, E2, E3, E4. exact Hφ.
      Qed.

      Lemma kmine_stable_r key x0 : Stable Isl (Rsl k) (KMine key x0).
      Proof. intros s s' Hm (Hs & _) _. exact (eihl_mine_steps (E := ES) δS _ _ _ _ Hs Hm). Qed.

      Lemma kmine_stable_g k' key x0 : Stable Isl (Gsl k') (KMine key x0).
      Proof. intros s s' Hm (Hs & _) _. exact (eihl_mine_steps (E := ES) δS _ _ _ _ Hs Hm). Qed.

      Lemma kdoomrd_stable_r key l w : Stable Isl (Rsl k) (KDoomRd key l w).
      Proof. intros s s' (v & Hne & Hm) (Hs & _) _. exists v. split; [exact Hne | exact (eihl_mine_steps (E := ES) δS _ _ _ _ Hs Hm)]. Qed.

      Lemma kdoomrd_stable_g k' key l w : Stable Isl (Gsl k') (KDoomRd key l w).
      Proof. intros s s' (v & Hne & Hm) (Hs & _) _. exists v. split; [exact Hne | exact (eihl_mine_steps (E := ES) δS _ _ _ _ Hs Hm)]. Qed.
    End Stab.

    Lemma kdoomrd_refuted key l w (σ σ' : State VE) p (γ : Ghost ES FS) :
      KDoomRd key l w (σ, p, γ) -> Step VE (Build_ThreadEvent (fst key) (@ResEv ES (snd key) (sRd l) w)) σ σ' -> False.
    Proof.
      intros (v & Hne & Hm) Hst. pose proof (eihl_mine_res (E := ES) δS key _ (sRd l) w σ σ' Hm Hst) as E.
      apply Hne. exact (rd_rec_inj (rc := rc) _ _ _ _ E).
    Qed.

    Lemma good_or_doom key l (v w : nat) (s : PState VE VF) :
      eihl_mine (E := ES) δS key (@RelaxedTraceLin.Build_Op ES key (sRd l) v) (ps_mem s) -> v = w \/ KDoomRd key l w s.
    Proof. intros Hm. destruct (Nat.eq_dec v w) as [-> | Hne]; [left; reflexivity | right; exists v; auto]. Qed.

    (** The emission of a read: the registers are unchanged and the call
        owns the new record, whose value is the register read. *)
    Lemma read_inv_mine t hu l (σ σ' : State VE) :
      eihl_rec_used (E := ES) δS σ -> Step VE (IE t hu (sRd l)) σ σ' ->
      fst (fst σ') = fst (fst σ) /\
      eihl_mine (E := ES) δS (t, hu) (@RelaxedTraceLin.Build_Op ES (t, hu) (sRd l) (fst (fst σ) l)) σ'.
    Proof.
      intros Hru Hst. destruct (eihl_mine_inv (E := ES) δS t hu (sRd l) σ σ' Hst Hru) as (r & st' & Hd & Hσ' & Hm).
      destruct Hd as [-> ->]. split; [rewrite Hσ'; reflexivity | exact Hm].
    Qed.

    (** ** Part 7. Maintenance of the invariant, event by event

        Each lemma below states, for one kind of underlay event of a call
        [k], the [Isl] of the post-state (with the exact abstract update)
        and the [Gsl k] step.  They are what the derivations of the read
        and the write (tasks .5, .6) need at each [ns_update]. *)

    (** *** Underlay steps of [EIhl δS] *)

    Lemma step_ie (σ σ' : State VE) t hu o :
      Step VE (IE t hu o) σ σ' ->
      ~ In (t, hu) (snd σ) /\ exists r m', δS (fst (fst σ)) o r m' /\
        σ' = ((m', @RelaxedTraceLin.Build_Op ES (t, hu) o r :: snd (fst σ)), (t, hu) :: snd σ).
    Proof.
      destruct σ as [[m U] u], σ' as [[m' U'] u']. cbn. intros (Hnu & (r & st' & Hd & Heq) & Hu).
      injection Heq as -> ->. subst u'. split; [exact Hnu |]. exists r, st'. split; [exact Hd | reflexivity].
    Qed.

    Lemma step_res (σ σ' : State VE) t hu o (r : sar o) :
      Step VE (Build_ThreadEvent t (@ResEv ES hu o r)) σ σ' -> fst (fst σ') = fst (fst σ).
    Proof.
      destruct σ as [[m U] u], σ' as [[m' U'] u']. cbn. intros ((Q1 & Q2 & _ & Heq) & _). injection Heq as -> _. reflexivity.
    Qed.

    Lemma deltaS_noreg (m : Regs) (o : SOp) (r : sar o) (m' : Regs) : (forall l v, o <> sWr l v) -> δS m o r m' -> m' = m.
    Proof.
      destruct o as [l | l v | |]; cbn; intros Hn Hd.
      - exact (proj2 Hd).
      - exfalso. exact (Hn l v eq_refl).
      - exact Hd.
      - exact Hd.
    Qed.

    Lemma step_ie_regs (σ σ' : State VE) t hu o :
      Step VE (IE t hu o) σ σ' -> (forall l v, o <> sWr l v) -> fst (fst σ') = fst (fst σ).
    Proof.
      intros Hs Hn. destruct (step_ie _ _ _ _ _ Hs) as (_ & r & m' & Hd & ->). cbn. exact (deltaS_noreg _ _ _ _ Hn Hd).
    Qed.

    Lemma step_ie_wr (σ σ' : State VE) t hu l w :
      Step VE (IE t hu (sWr l w)) σ σ' -> fst (fst σ') = upd (fst (fst σ)) l w.
    Proof. intros Hs. destruct (step_ie _ _ _ _ _ Hs) as (_ & r & m' & Hd & ->). exact Hd. Qed.

    Lemma upd_sq_same (m : Regs) i w : upd m (Sq i) w (Sq i) = w.
    Proof. apply upd_eq. Qed.

    Lemma upd_sq_other (m : Regs) i j w : i <> j -> upd m (Sq i) w (Sq j) = m (Sq j).
    Proof. intros H. apply upd_neq. congruence. Qed.

    Lemma upd_neq_x (m : Regs) l j w : l <> Sx j -> upd m l w (Sx j) = m (Sx j).
    Proof. intros H. apply upd_neq. exact H. Qed.

    Lemma upd_neq_y (m : Regs) l j w : l <> Sy j -> upd m l w (Sy j) = m (Sy j).
    Proof. intros H. apply upd_neq. exact H. Qed.

    Lemma upd_neq_q (m : Regs) l j w : l <> Sq j -> upd m l w (Sq j) = m (Sq j).
    Proof. intros H. apply upd_neq. exact H. Qed.

    Lemma aupd_same (A : AS) i p : Aupd A i p i = p.
    Proof. unfold Aupd. rewrite Nat.eqb_refl. reflexivity. Qed.

    Lemma aupd_other (A : AS) i j p : i <> j -> Aupd A i p j = A j.
    Proof. intros H. unfold Aupd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

    (** *** Generic pieces *)

    Lemma gsl_intro k (σ σ' : State VE) (A : AS) (Pf : list OpF) (P : LinPool FS) (A' : AS) (Pf' : list OpF)
        (P' : LinPool FS) (γ γ' : Ghost ES FS) :
      eihl_steps (E := ES) δS σ σ' ->
      (forall k' ls, k' <> k -> lin_lookup k' ls P -> lin_lookup k' ls P') ->
      (forall o : OpF, okey o <> k -> In o Pf -> In o Pf') ->
      (forall e, se_owner e <> k -> (In e γ <-> In e γ')) ->
      (forall k', OlderSub k' P γ P' γ') ->
      (forall i k', k' <> k -> Holder i k' P γ -> InstFrozen i (fst (fst σ)) (fst (fst σ')) A A') ->
      SeqMono (fst (fst σ)) (fst (fst σ')) A A' ->
      Gsl k (σ, POk (A, Pf) P, γ) (σ', POk (A', Pf') P', γ').
    Proof.
      intros Hm Hp Hr Hg Ho Hh Hs. split; [exact Hm |]. exists A, Pf, P, A', Pf', P'.
      split; [reflexivity |]. split; [reflexivity |]. split; [exact Hp |]. split; [exact Hr |].
      split; [exact Hg |]. split; [exact Ho |]. split; [exact Hh | exact Hs].
    Qed.

    Lemma emit_frame k (g1 g2 : Ghost ES FS) x : se_owner x = k ->
      forall e, se_owner e <> k -> (In e (g1 ++ x :: g2) <-> In e (g1 ++ g2)).
    Proof.
      intros Hx e He. split; [| apply incl_remove_mid].
      intros H. apply in_app_or in H as [H | [<- | H]]; [apply in_or_app; left; exact H | contradiction | apply in_or_app; right; exact H].
    Qed.

    Lemma gwf_emit (g1 g2 : Ghost ES FS) x :
      Forall RelaxedHoareInherit.gwf (g1 ++ x :: g2) -> Forall RelaxedHoareInherit.gwf (g1 ++ g2).
    Proof. intros H. apply Forall_app in H as [H1 H2]. apply Forall_app. split; [exact H1 | exact (Forall_inv_tail H2)]. Qed.

    (** [WOrd] after an emission.  The only case that needs an argument is
        a write starting (its [rd Sq_i] leaves the ghost): an older write of
        the same instance has the same thread (P1) and a pending access to
        [Sq_i] would precede and block the emitted [rd Sq_i]. *)
    Lemma word_emit (P : LinPool FS) (g1 g2 : Ghost ES FS) x :
      GAge P (g1 ++ x :: g2) -> Forall RelaxedHoareInherit.gwf (g1 ++ x :: g2) ->
      (forall i k, IsWr i k P -> fst k = tw i) ->
      Forall (fun e => ~ inv_blocks (se_event e) (se_event x)) g1 ->
      WOrd P (g1 ++ x :: g2) -> WOrd P (g1 ++ g2).
    Proof.
      intros Hage Hgwf Htw Hnb Hword i k1 k2 Hw1 Hw2 Ho Hr2 Hown1.
      destruct (owns_dec k2 (isRdSq i) (g1 ++ x :: g2) (isRdSq_dec i)) as [Hr | Hr].
      - destruct (owns_emit _ _ _ _ _ Hr) as [Hr' | [Hox Hqx]]; [exact (Hr2 Hr') |].
        destruct Hown1 as (e & He & Hoe & Hqe).
        assert (He0 : In e (g1 ++ x :: g2)) by exact (incl_remove_mid g1 g2 x e He).
        assert (He1 : In e g1).
        { apply (gage_before P _ g1 g2 x e Hage eq_refl He0). rewrite Hoe, Hox. exact Ho. }
        rewrite Forall_forall in Hnb, Hgwf. apply (Hnb e He1). apply blocks_of_gwf.
        + exact (Hgwf e He0).
        + apply Hgwf. apply in_or_app. right. left. reflexivity.
        + rewrite Hoe, Hox, (Htw i k1 Hw1), (Htw i k2 Hw2). reflexivity.
        + apply sindep_same_loc. unfold isRdSq in Hqx. rewrite Hqx. exact Hqe.
      - apply (Hword i k1 k2 Hw1 Hw2 Ho Hr). exact (owns_incl _ _ _ _ (incl_remove_mid g1 g2 x) Hown1).
    Qed.

    Lemma word_update k b a (P P' : LinPool FS) (γ : Ghost ES FS) :
      lin_pool_well_formed P -> lin_update k b a P P' -> lsop a = lsop b -> WOrd P γ -> WOrd P' γ.
    Proof.
      intros Hwf Hu Hab Hw i k1 k2 (vx1 & vy1 & H1) (vx2 & vy2 & H2) Ho Hr2.
      apply (Hw i k1 k2 (ex_intro _ vx1 (ex_intro _ vy1 (proj2 (hasop_update _ _ _ _ _ _ _ Hwf Hu Hab) H1)))
                       (ex_intro _ vx2 (ex_intro _ vy2 (proj2 (hasop_update _ _ _ _ _ _ _ Hwf Hu Hab) H2)))).
      - rewrite (lin_update_keys _ _ _ _ _ Hu). exact Ho.
      - exact Hr2.
    Qed.

    Lemma holder_emit i k0 (P : LinPool FS) (g1 g2 : Ghost ES FS) x :
      Holder i k0 P (g1 ++ x :: g2) -> ~ (se_owner x = k0 /\ isWrSq i (gop x)) -> Holder i k0 P (g1 ++ g2).
    Proof.
      intros (Hw & Hr & Hs) Hn. split; [exact Hw |]. split.
      - intros H. apply Hr. exact (owns_incl _ _ _ _ (incl_remove_mid g1 g2 x) H).
      - destruct (owns_emit _ _ _ _ _ Hs) as [Hs' | Hx]; [exact Hs' | contradiction].
    Qed.

    Lemma coup_emit_other k ls (g1 g2 : Ghost ES FS) x :
      se_owner x <> k -> Coup k ls (g1 ++ x :: g2) -> Coup k ls (g1 ++ g2).
    Proof. intros Hne. apply coup_ext. intros Q. apply owns_emit_other. exact Hne. Qed.

    (** An emission that writes no [Sq] register, the pool and the
        abstract state unchanged; the emitter re-establishes its own
        coupling ([Hk]). *)
    Lemma islc_emit m A Pf P (g1 g2 : Ghost ES FS) x :
      IslC m A Pf P (g1 ++ x :: g2) -> Forall (fun e => ~ inv_blocks (se_event e) (se_event x)) g1 ->
      (forall j v, gop x <> sWr (Sq j) v) ->
      (forall ls, lin_lookup (se_owner x) ls P -> Coup (se_owner x) ls (g1 ++ g2)) ->
      IslC m A Pf P (g1 ++ g2).
    Proof.
      intros HC Hnb Hnw Hk. pose proof HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd].
      constructor.
      - exact Hwf.
      - exact (gage_remove P g1 g2 x Hage).
      - exact (gwf_emit g1 g2 x Hgwf).
      - exact Hrec.
      - exact Hrnd.
      - intros e He. destruct (callkey_eq_dec (lin_key e) (se_owner x)) as [Hk' | Hk'].
        + rewrite Hk'. apply Hk. rewrite <- Hk'. exact (entry_lookup e P He).
        + apply (coup_emit_other _ _ g1 g2 x); [intros E; apply Hk'; symmetry; exact E | exact (Hcoup e He)].
      - exact Htw.
      - exact (word_emit P g1 g2 x Hage Hgwf (iswr_tw _ _ _ _ _ HC) Hnb Hword).
      - exact Hjev.
      - intros i Ev. destruct (Hjodd i Ev) as (k0 & vx & vy & Hh & Hop & Hnl & HA).
        exists k0, vx, vy. split; [| auto]. apply (holder_emit i k0 P g1 g2 x Hh).
        intros [_ (v & Hv)]. exact (Hnw i v Hv).
      - exact (NoDup_remove_1 _ _ _ Hgnd).
    Qed.

    (** A register change that keeps every [Sq] register and keeps the
        data registers of the instances with an even sequence number. *)
    Lemma islc_regs m m' A Pf P (γ : Ghost ES FS) :
      IslC m A Pf P γ -> (forall j, m' (Sq j) = m (Sq j)) ->
      (forall j, Nat.even (m (Sq j)) = true -> m' (Sx j) = m (Sx j) /\ m' (Sy j) = m (Sy j)) ->
      IslC m' A Pf P γ.
    Proof.
      intros HC Hq Hd. destruct HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd]. constructor; try assumption.
      - intros j Ev. rewrite Hq in Ev. destruct (Hd j Ev) as [-> ->]. exact (Hjev j Ev).
      - intros j Ev. rewrite Hq in Ev. exact (Hjodd j Ev).
    Qed.

    (** The coupling of a writer that has linearized holds whatever its
        ghost entries. *)
    Lemma coup_lin_write k i vx vy (P : LinPool FS) (γ : Ghost ES FS) :
      lin_pool_well_formed P -> HasOp k (fW i vx vy) P -> ~ lin_lookup k (@ls_inv FS (fW i vx vy)) P ->
      forall ls, lin_lookup k ls P -> Coup k ls γ.
    Proof.
      intros Hwf Hop Hnl ls Hl. assert (Hls : lsop ls = fW i vx vy) by exact (hasop_unique k _ _ P Hwf (ex_intro _ ls (conj Hl eq_refl)) Hop).
      unfold Coup. rewrite Hls. intros Hi. exfalso. apply Hnl.
      destruct ls as [o | o | o r]; cbn in Hi, Hls; try discriminate Hi. rewrite <- Hls. exact Hl.
    Qed.

    (** *** Events without abstract steps *)

    (** Any response, of any call. *)
    Theorem isl_response k t hu o (r : sar o) (σ σ' : State VE) p (γ : Ghost ES FS) :
      Isl (σ, p, γ) -> Step VE (Build_ThreadEvent t (@ResEv ES hu o r)) σ σ' ->
      Isl (σ', p, γ) /\ Gsl k (σ, p, γ) (σ', p, γ).
    Proof.
      intros (A & Pf & P & Hp & Hru & HC) Hst. cbn in Hp. subst p.
      pose proof (step_res _ _ _ _ _ _ Hst) as Hregs.
      cbn [regs ps_mem ps_ghost ps_poss fst snd] in Hru, HC.
      split.
      - exists A, Pf, P. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δS _ _ _ Hst Hru) |].
        unfold regs; cbn [ps_mem ps_ghost fst snd]. rewrite Hregs. exact HC.
      - apply gsl_intro; auto.
        + apply rt_step. eexists. exact Hst.
        + intros e _. reflexivity.
        + intros k'. apply oldersub_refl.
        + intros i k' _ _. rewrite Hregs. apply frozen_refl.
        + rewrite Hregs. apply seqmono_refl.
    Qed.

    (** An invocation of a read, an [rmb] or a [wmb] by [k] (no register
        is written, no abstract step); [k] re-establishes its coupling. *)
    Theorem isl_inv_noreg k t hu o (σ σ' : State VE) A Pf P (γ γ' : Ghost ES FS) :
      Isl (σ, POk (A, Pf) P, γ) -> ghost_emit k (IE t hu o) γ γ' -> Step VE (IE t hu o) σ σ' ->
      (forall l v, o <> sWr l v) ->
      (forall ls, lin_lookup k ls P -> Coup k ls γ') ->
      Isl (σ', POk (A, Pf) P, γ') /\ Gsl k (σ, POk (A, Pf) P, γ) (σ', POk (A, Pf) P, γ').
    Proof.
      intros (A0 & Pf0 & P0 & Hp & Hru & HC) Hge Hst Hnw Hk. cbn in Hp. injection Hp as E1 E2 E3. subst A0 Pf0 P0.
      cbn [regs ps_mem ps_ghost ps_poss fst snd] in Hru, HC.
      destruct (ghost_emit_ie _ _ _ _ _ _ Hge) as (g1 & g2 & -> & -> & Hnb).
      pose proof (step_ie_regs _ _ _ _ _ Hst Hnw) as Hregs.
      split.
      - exists A, Pf, P. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δS _ _ _ Hst Hru) |].
        unfold regs; cbn [ps_mem ps_ghost fst snd]. rewrite Hregs.
        exact (islc_emit _ _ _ _ g1 g2 (Build_ScheduledEvent k (IE t hu o)) HC Hnb (fun j v => Hnw (Sq j) v) Hk).
      - apply gsl_intro; auto.
        + apply rt_step. eexists. exact Hst.
        + exact (emit_frame k g1 g2 (Build_ScheduledEvent k (IE t hu o)) eq_refl).
        + intros k'. apply oldersub_same_domain; [reflexivity | apply incl_remove_mid].
        + intros i k' _ _. rewrite Hregs. apply frozen_refl.
        + rewrite Hregs. apply seqmono_refl.
    Qed.

    (** *** The linearization point of a read: its final [rmb] *)

    Lemma islc_read_lp m A Pf P P' (g1 g2 : Ghost ES FS) t h i hB :
      IslC m A Pf P (g1 ++ Build_ScheduledEvent (t, h) (IE t hB sRmb) :: g2) ->
      Forall (fun e => ~ inv_blocks (se_event e) (IE t hB sRmb)) g1 ->
      lin_invoke_update t h (fR i) P P' ->
      ~ Owns (t, h) isRmb (g1 ++ g2) ->
      IslC m A (@RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf) P' (g1 ++ g2).
    Proof.
      set (x := Build_ScheduledEvent (t, h) (IE t hB sRmb)). intros HC Hnb Hu Hno.
      pose proof HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd].
      pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
      pose proof (lin_update_well_formed _ _ _ _ _ Hu2 Hwf) as Hwf'.
      pose proof (lin_update_source _ _ _ _ _ Hu2) as Hl.
      assert (Hop : forall k o, HasOp k o P <-> HasOp k o P') by (intros k o; exact (hasop_update _ _ _ _ _ k o Hwf Hu2 eq_refl)).
      assert (Hrk : forall o : OpF, In o Pf -> okey o <> (t, h)).
      { intros o Ho Hk. pose proof (Hrec o Ho) as Hlo. rewrite Hk in Hlo.
        pose proof (RelaxedHoareInherit.lookup_unique_gen P (t, h) _ _ Hwf Hl Hlo) as E. discriminate E. }
      constructor.
      - exact Hwf'.
      - exact (gage_after_lp P P' g1 g2 x t h (fR i) Hage Hu).
      - exact (gwf_emit g1 g2 x Hgwf).
      - intros o [<- | Ho]; [exact (lin_update_target _ _ _ _ _ Hu2) |].
        exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu2 (Hrk o Ho) (Hrec o Ho)).
      - constructor; [| exact Hrnd]. intros Hin. apply in_map_iff in Hin as (o & Hk & Ho). exact (Hrk o Ho Hk).
      - intros e He. destruct (callkey_eq_dec (lin_key e) (t, h)) as [Hk | Hk].
        + pose proof (entry_lookup e P' He) as Hle. rewrite Hk in Hle.
          rewrite Hk, (RelaxedHoareInherit.lookup_unique_gen P' (t, h) _ _ Hwf' Hle (lin_update_target _ _ _ _ _ Hu2)).
          unfold Coup. cbn. split; [discriminate | intros H; contradiction].
        + destruct (lin_update_incl _ _ _ _ _ _ Hu2 He) as [He0 | He0];
            [| exfalso; apply Hk; rewrite He0; apply lin_key_make_lin_entry].
          apply (coup_emit_other _ _ g1 g2 x); [intros E; apply Hk; symmetry; exact E | exact (Hcoup e He0)].
      - intros e j vx vy He Ho. destruct (lin_update_incl _ _ _ _ _ _ Hu2 He) as [He0 | ->]; [exact (Htw e j vx vy He0 Ho) |].
        discriminate Ho.
      - exact (word_update _ _ _ P P' _ Hwf Hu2 eq_refl (word_emit P g1 g2 x Hage Hgwf (iswr_tw _ _ _ _ _ HC) Hnb Hword)).
      - exact Hjev.
      - intros j Ev. destruct (Hjodd j Ev) as (k0 & vx & vy & Hh & Hop0 & Hnl & HA).
        exists k0, vx, vy. split; [| split; [exact (proj1 (Hop _ _) Hop0) | split; [| exact HA]]].
        + apply (holder_ext j k0 P P' (g1 ++ g2)); [intros o Ho; exact (proj1 (Hop _ _) Ho) | intros Q; reflexivity |].
          apply (holder_emit j k0 P g1 g2 x Hh). intros [_ (v & Hv)]. discriminate Hv.
        + intros Hl'. destruct (lin_update_incl _ _ _ _ _ _ Hu2 Hl') as [Hl0 | Hl0]; [exact (Hnl Hl0) |].
          destruct (make_entry_inj _ _ _ _ Hl0) as [_ E]. discriminate E.
      - exact (NoDup_remove_1 _ _ _ Hgnd).
    Qed.

    (** The read [k = (t, h)] of instance [i] emits an [rmb] after which it
        owns no [rmb] (the final iteration's [rmb_b]): readiness by
        [ready_read] (the [RecNB] of the iteration's [rd Sq_i] is carried by
        the derivation), then the abstract invocation [psa_inv] with result
        [A i]. *)
    Theorem isl_read_lp (Hsi : forall o o', slRA o o' -> si o o') t h i hB hG (σ σ' : State VE) A Pf P
        (γ γ' : Ghost ES FS) :
      Isl (σ, POk (A, Pf) P, γ) -> lin_lookup (t, h) (@ls_inv FS (fR i)) P ->
      ghost_emit (t, h) (IE t hB sRmb) γ γ' -> Step VE (IE t hB sRmb) σ σ' ->
      RecNB P (t, h) (IE t hG (sRd (Sq i))) γ -> ~ Owns (t, h) isRmb γ' ->
      exists P', lin_invoke_update t h (fR i) P P' /\
        poss_steps VF (POk (A, Pf) P) (POk (A, @RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf) P') /\
        Isl (σ', POk (A, @RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf) P', γ') /\
        Gsl (t, h) (σ, POk (A, Pf) P, γ) (σ', POk (A, @RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf) P', γ').
    Proof.
      intros (A0 & Pf0 & P0 & Hp & Hru & HC) Hl Hge Hst Hrec Hno. cbn in Hp. injection Hp as E1 E2 E3. subst A0 Pf0 P0.
      cbn [regs ps_mem ps_ghost ps_poss fst snd] in Hru, HC.
      destruct (ready_read Hsi _ _ _ _ _ _ t h i hG hB HC Hl Hge Hrec) as (P' & Hu & Hwf').
      destruct (ghost_emit_ie _ _ _ _ _ _ Hge) as (g1 & g2 & -> & -> & Hnb).
      pose proof (step_ie_regs _ _ _ _ _ Hst (fun l v (E : sRmb = sWr l v) => ltac:(discriminate E))) as Hregs.
      pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
      exists P'. split; [exact Hu |]. split.
      { apply rt_step. exists (t, h). apply (psa_inv VF t h (fR i) (A, Pf) _ P P' Hu). cbn.
        exists (A i), A. split; [split; reflexivity | reflexivity]. }
      split.
      - exists A, (RelaxedTraceLin.Build_Op (t, h) (fR i) (A i) :: Pf), P'. split; [reflexivity |].
        split; [exact (eihl_rec_used_step (E := ES) δS _ _ _ Hst Hru) |].
        unfold regs; cbn [ps_mem ps_ghost fst snd]. rewrite Hregs. exact (islc_read_lp _ _ _ _ _ g1 g2 t h i hB HC Hnb Hu Hno).
      - apply gsl_intro.
        + apply rt_step. eexists. exact Hst.
        + intros k' ls Hne Hl'. exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu2 Hne Hl').
        + intros o _ Ho. right. exact Ho.
        + exact (emit_frame (t, h) g1 g2 (Build_ScheduledEvent (t, h) (IE t hB sRmb)) eq_refl).
        + intros k'. apply oldersub_same_domain; [symmetry; exact (lin_invoke_update_keys _ _ _ _ _ Hu) | apply incl_remove_mid].
        + intros j k' _ _. rewrite Hregs. apply frozen_refl.
        + rewrite Hregs. apply seqmono_refl.
    Qed.

    (** *** The write: its linearization point [wr Sq_i (v+1)] *)

    Lemma islc_wr_lp m A Pf P P' (g1 g2 : Ghost ES FS) t h i vx vy h1 v :
      IslC m A Pf P (g1 ++ Build_ScheduledEvent (t, h) (IE t h1 (sWr (Sq i) (v + 1))) :: g2) ->
      Forall (fun e => ~ inv_blocks (se_event e) (IE t h1 (sWr (Sq i) (v + 1)))) g1 ->
      lin_invoke_update t h (fW i vx vy) P P' ->
      Holder i (t, h) P (g1 ++ Build_ScheduledEvent (t, h) (IE t h1 (sWr (Sq i) (v + 1))) :: g2) ->
      m (Sq i) = v -> Owns (t, h) (isWrSq i) (g1 ++ g2) ->
      IslC (upd m (Sq i) (v + 1)) (Aupd A i (vx, vy)) (@RelaxedTraceLin.Build_Op FS (t, h) (fW i vx vy) tt :: Pf) P'
        (g1 ++ g2).
    Proof.
      set (x := Build_ScheduledEvent (t, h) (IE t h1 (sWr (Sq i) (v + 1)))). intros HC Hnb Hu Hh Hv Hs.
      pose proof HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd].
      pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
      pose proof (lin_update_well_formed _ _ _ _ _ Hu2 Hwf) as Hwf'.
      pose proof (lin_update_source _ _ _ _ _ Hu2) as Hl.
      assert (Hev : Nat.even v = true) by (rewrite <- Hv; exact (holder_inv_even _ _ _ _ _ HC i (t, h) vx vy Hh Hl)).
      assert (Hodd : Nat.even (v + 1) = false) by (rewrite Nat.add_1_r, Nat.even_succ, <- Nat.negb_even, Hev; reflexivity).
      assert (Hop : forall k o, HasOp k o P <-> HasOp k o P') by (intros k o; exact (hasop_update _ _ _ _ _ k o Hwf Hu2 eq_refl)).
      assert (Hrk : forall o : OpF, In o Pf -> okey o <> (t, h)).
      { intros o Ho Hk. pose proof (Hrec o Ho) as Hlo. rewrite Hk in Hlo.
        pose proof (RelaxedHoareInherit.lookup_unique_gen P (t, h) _ _ Hwf Hl Hlo) as E. discriminate E. }
      assert (Htwk : t = tw i) by exact (Htw _ i vx vy Hl eq_refl).
      assert (Hwi : IsWr i (t, h) P) by (exists vx, vy, (@ls_inv FS (fW i vx vy)); split; [exact Hl | reflexivity]).
      constructor.
      - exact Hwf'.
      - exact (gage_after_lp P P' g1 g2 x t h (fW i vx vy) Hage Hu).
      - exact (gwf_emit g1 g2 x Hgwf).
      - intros o [<- | Ho]; [exact (lin_update_target _ _ _ _ _ Hu2) |].
        exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu2 (Hrk o Ho) (Hrec o Ho)).
      - constructor; [| exact Hrnd]. intros Hin. apply in_map_iff in Hin as (o & Hk & Ho). exact (Hrk o Ho Hk).
      - intros e He. destruct (callkey_eq_dec (lin_key e) (t, h)) as [Hk | Hk].
        + pose proof (entry_lookup e P' He) as Hle. rewrite Hk in Hle.
          rewrite Hk, (RelaxedHoareInherit.lookup_unique_gen P' (t, h) _ _ Hwf' Hle (lin_update_target _ _ _ _ _ Hu2)).
          unfold Coup. cbn. intros E. discriminate E.
        + destruct (lin_update_incl _ _ _ _ _ _ Hu2 He) as [He0 | He0];
            [| exfalso; apply Hk; rewrite He0; apply lin_key_make_lin_entry].
          apply (coup_emit_other _ _ g1 g2 x); [intros E; apply Hk; symmetry; exact E | exact (Hcoup e He0)].
      - intros e j wx wy He Ho. destruct (lin_update_incl _ _ _ _ _ _ Hu2 He) as [He0 | ->]; [exact (Htw e j wx wy He0 Ho) |].
        cbn in Ho |- *. injection Ho as <- _ _. exact Htwk.
      - exact (word_update _ _ _ P P' _ Hwf Hu2 eq_refl (word_emit P g1 g2 x Hage Hgwf (iswr_tw _ _ _ _ _ HC) Hnb Hword)).
      - intros j Ev. destruct (Nat.eq_dec i j) as [<- | Hij].
        + rewrite upd_sq_same, Hodd in Ev. discriminate Ev.
        + rewrite (upd_sq_other m i j _ Hij) in Ev. rewrite (upd_neq_x m (Sq i) j _ ltac:(discriminate)),
            (upd_neq_y m (Sq i) j _ ltac:(discriminate)), (aupd_other A i j _ Hij). exact (Hjev j Ev).
      - intros j Ev. destruct (Nat.eq_dec i j) as [<- | Hij].
        + exists (t, h), vx, vy. split; [| split; [exists (@ls_lini FS (fW i vx vy)); split; [exact (lin_update_target _ _ _ _ _ Hu2) | reflexivity] |]].
          * split; [exists vx, vy, (@ls_lini FS (fW i vx vy)); split; [exact (lin_update_target _ _ _ _ _ Hu2) | reflexivity] |].
            split; [| exact Hs]. intros H. apply (proj1 (proj2 Hh)). exact (owns_incl _ _ _ _ (incl_remove_mid g1 g2 x) H).
          * split; [| apply aupd_same]. intros Hl'.
            pose proof (RelaxedHoareInherit.lookup_unique_gen P' (t, h) _ _ Hwf' Hl' (lin_update_target _ _ _ _ _ Hu2)) as E.
            discriminate E.
        + rewrite (upd_sq_other m i j _ Hij) in Ev. destruct (Hjodd j Ev) as (k0 & wx & wy & Hh0 & Hop0 & Hnl & HA).
          assert (Hk0 : k0 <> (t, h)).
          { intros ->. apply Hij. exact (iswr_unique i j (t, h) P Hwf Hwi (proj1 Hh0)). }
          exists k0, wx, wy. split; [| split; [exact (proj1 (Hop _ _) Hop0) | split]].
          * apply (holder_ext j k0 P P' (g1 ++ g2)); [intros o Ho; exact (proj1 (Hop _ _) Ho) | intros Q; reflexivity |].
            apply (holder_emit j k0 P g1 g2 x Hh0). intros [E _]. exact (Hk0 (eq_sym E)).
          * intros Hl'. exact (Hnl (lin_update_lookup_back _ _ _ _ _ _ _ Hu2 Hk0 Hl')).
          * rewrite (aupd_other A i j _ Hij). exact HA.
      - exact (NoDup_remove_1 _ _ _ Hgnd).
    Qed.

    (** The write [k = (t, h)] of instance [i], holder (its [rd Sq_i] read
        [v]), emits [wr Sq_i (v+1)] and keeps a pending write of [Sq_i]:
        readiness by [ready_write], then [psa_inv] with [A i := (vx, vy)]. *)
    Theorem isl_wr_lp t h i vx vy v h0 h1 (σ σ' : State VE) A Pf P (γ γ' : Ghost ES FS) :
      Isl (σ, POk (A, Pf) P, γ) -> lin_lookup (t, h) (@ls_inv FS (fW i vx vy)) P ->
      Holder i (t, h) P γ -> fst (fst σ) (Sq i) = v ->
      ghost_emit (t, h) (IE t h1 (sWr (Sq i) (v + 1))) γ γ' -> Step VE (IE t h1 (sWr (Sq i) (v + 1))) σ σ' ->
      RecNB P (t, h) (IE t h0 (sRd (Sq i))) γ -> Owns (t, h) (isWrSq i) γ' ->
      exists P', lin_invoke_update t h (fW i vx vy) P P' /\
        poss_steps VF (POk (A, Pf) P)
          (POk (Aupd A i (vx, vy), @RelaxedTraceLin.Build_Op FS (t, h) (fW i vx vy) tt :: Pf) P') /\
        Isl (σ', POk (Aupd A i (vx, vy), @RelaxedTraceLin.Build_Op FS (t, h) (fW i vx vy) tt :: Pf) P', γ') /\
        Gsl (t, h) (σ, POk (A, Pf) P, γ)
          (σ', POk (Aupd A i (vx, vy), @RelaxedTraceLin.Build_Op FS (t, h) (fW i vx vy) tt :: Pf) P', γ').
    Proof.
      intros (A0 & Pf0 & P0 & Hp & Hru & HC) Hl Hh Hv Hge Hst Hrec Hs. cbn in Hp. injection Hp as E1 E2 E3. subst A0 Pf0 P0.
      cbn [regs ps_mem ps_ghost ps_poss fst snd] in Hru, HC.
      destruct (ready_write _ _ _ _ _ _ t h i vx vy h0 h1 _ HC Hl Hge Hrec) as (P' & Hu & Hwf').
      pose proof Hge as Hge0. destruct (ghost_emit_ie _ _ _ _ _ _ Hge0) as (g1 & g2 & Hγ & Hγ' & Hnb). subst γ γ'.
      pose proof (step_ie_wr _ _ _ _ _ _ Hst) as Hregs.
      pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
      
      assert (Hev : Nat.even v = true) by (rewrite <- Hv; exact (holder_inv_even _ _ _ _ _ HC i (t, h) vx vy Hh Hl)).
      exists P'. split; [exact Hu |]. split.
      { apply rt_step. exists (t, h). apply (psa_inv VF t h (fW i vx vy) (A, Pf) _ P P' Hu). cbn.
        exists tt, (Aupd A i (vx, vy)). split; reflexivity. }
      split.
      - exists (Aupd A i (vx, vy)), (RelaxedTraceLin.Build_Op (t, h) (fW i vx vy) tt :: Pf), P'. split; [reflexivity |].
        split; [exact (eihl_rec_used_step (E := ES) δS _ _ _ Hst Hru) |].
        unfold regs; cbn [ps_mem ps_ghost fst snd]. rewrite Hregs. exact (islc_wr_lp _ _ _ _ _ g1 g2 t h i vx vy h1 v HC Hnb Hu Hh Hv Hs).
      - apply gsl_intro.
        + apply rt_step. eexists. exact Hst.
        + intros k' ls Hne Hl'. exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu2 Hne Hl').
        + intros o _ Ho. right. exact Ho.
        + exact (emit_frame (t, h) g1 g2 (Build_ScheduledEvent (t, h) (IE t h1 (sWr (Sq i) (v + 1)))) eq_refl).
        + intros k'. apply oldersub_same_domain; [symmetry; exact (lin_invoke_update_keys _ _ _ _ _ Hu) | apply incl_remove_mid].
        + intros j k' Hne Hh'. rewrite Hregs. destruct (Nat.eq_dec i j) as [<- | Hij].
          * exfalso. exact (Hne (holder_unique _ _ _ _ _ HC i k' (t, h) Hh' Hh)).
          * split; [exact (upd_sq_other (fst (fst σ)) i j _ Hij) |]. split; [apply upd_neq_x; discriminate |].
            split; [apply upd_neq_y; discriminate | exact (aupd_other A i j _ Hij)].
        + rewrite Hregs. intros j. destruct (Nat.eq_dec i j) as [<- | Hij].
          * rewrite upd_sq_same, Hv. split; [lia | intros E; lia].
          * rewrite (upd_sq_other (fst (fst σ)) i j _ Hij). split; [lia |]. intros _. split; [exact (aupd_other A i j _ Hij) |].
            intros _. split; [apply upd_neq_x; discriminate | apply upd_neq_y; discriminate].
    Qed.

    (** *** The write: its data writes [wr Sx_i], [wr Sy_i] (sequence number odd) *)

    Theorem isl_wr_data t h i vx vy l w hu (σ σ' : State VE) A Pf P (γ γ' : Ghost ES FS) :
      Isl (σ, POk (A, Pf) P, γ) -> HasOp (t, h) (fW i vx vy) P -> ~ lin_lookup (t, h) (@ls_inv FS (fW i vx vy)) P ->
      Holder i (t, h) P γ -> Nat.even (fst (fst σ) (Sq i)) = false -> (l = Sx i \/ l = Sy i) ->
      ghost_emit (t, h) (IE t hu (sWr l w)) γ γ' -> Step VE (IE t hu (sWr l w)) σ σ' ->
      Isl (σ', POk (A, Pf) P, γ') /\ Gsl (t, h) (σ, POk (A, Pf) P, γ) (σ', POk (A, Pf) P, γ').
    Proof.
      intros (A0 & Pf0 & P0 & Hp & Hru & HC) Hop Hnl Hh Hodd Hl Hge Hst. cbn in Hp. injection Hp as E1 E2 E3. subst A0 Pf0 P0.
      cbn [regs ps_mem ps_ghost ps_poss fst snd] in Hru, HC.
      destruct (ghost_emit_ie _ _ _ _ _ _ Hge) as (g1 & g2 & Hγ & Hγ' & Hnb). subst γ γ'.
      pose proof (step_ie_wr _ _ _ _ _ _ Hst) as Hregs. 
      assert (Hlq : forall j, l <> Sq j) by (intros j; destruct Hl as [-> | ->]; discriminate).
      assert (Hdat : forall j, j <> i -> upd (fst (fst σ)) l w (Sx j) = (fst (fst σ)) (Sx j) /\ upd (fst (fst σ)) l w (Sy j) = (fst (fst σ)) (Sy j)).
      { intros j Hj. split; [apply upd_neq_x | apply upd_neq_y]; destruct Hl as [-> | ->]; congruence. }
      split.
      - exists A, Pf, P. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δS _ _ _ Hst Hru) |].
        unfold regs; cbn [ps_mem ps_ghost fst snd]. rewrite Hregs.
        apply (islc_regs (fst (fst σ))).
        + apply (islc_emit _ _ _ _ g1 g2 (Build_ScheduledEvent (t, h) (IE t hu (sWr l w))) HC Hnb).
          * intros j v E. injection E as E _. exact (Hlq j E).
          * exact (coup_lin_write _ _ _ _ P _ (ic_wf _ _ _ _ _ HC) Hop Hnl).
        + intros j. exact (upd_neq_q (fst (fst σ)) l j w (Hlq j)).
        + intros j Ev. destruct (Nat.eq_dec j i) as [-> | Hj]; [rewrite Hodd in Ev; discriminate Ev | exact (Hdat j Hj)].
      - apply gsl_intro; auto.
        + apply rt_step. eexists. exact Hst.
        + exact (emit_frame (t, h) g1 g2 (Build_ScheduledEvent (t, h) (IE t hu (sWr l w))) eq_refl).
        + intros k'. apply oldersub_same_domain; [reflexivity | apply incl_remove_mid].
        + intros j k' Hne Hh'. rewrite Hregs. destruct (Nat.eq_dec j i) as [-> | Hj].
          * exfalso. exact (Hne (holder_unique _ _ _ _ _ HC i k' (t, h) Hh' Hh)).
          * split; [exact (upd_neq_q (fst (fst σ)) l j w (Hlq j)) |]. destruct (Hdat j Hj) as [-> ->]. split; [reflexivity | split; reflexivity].
        + rewrite Hregs. intros j. rewrite (upd_neq_q (fst (fst σ)) l j w (Hlq j)). split; [lia |]. intros _. split; [reflexivity |].
          intros Ev. destruct (Nat.eq_dec j i) as [-> | Hj]; [rewrite Hodd in Ev; discriminate Ev | exact (Hdat j Hj)].
    Qed.

    (** *** The write: its last [wr Sq_i (v+2)] *)

    Lemma islc_wr_end m A Pf P (g1 g2 : Ghost ES FS) t h i vx vy v hu :
      IslC m A Pf P (g1 ++ Build_ScheduledEvent (t, h) (IE t hu (sWr (Sq i) (v + 2))) :: g2) ->
      Forall (fun e => ~ inv_blocks (se_event e) (IE t hu (sWr (Sq i) (v + 2)))) g1 ->
      HasOp (t, h) (fW i vx vy) P -> ~ lin_lookup (t, h) (@ls_inv FS (fW i vx vy)) P -> Nat.even v = true ->
      m (Sx i) = vx -> m (Sy i) = vy -> A i = (vx, vy) ->
      IslC (upd m (Sq i) (v + 2)) A Pf P (g1 ++ g2).
    Proof.
      set (x := Build_ScheduledEvent (t, h) (IE t hu (sWr (Sq i) (v + 2)))). intros HC Hnb Hop Hnl Hev Hx Hy HA.
      pose proof HC as [Hwf Hage Hgwf Hrec Hrnd Hcoup Htw Hword Hjev Hjodd Hgnd].
      assert (Hwi : IsWr i (t, h) P) by (exists vx, vy; exact Hop).
      constructor.
      - exact Hwf.
      - exact (gage_remove P g1 g2 x Hage).
      - exact (gwf_emit g1 g2 x Hgwf).
      - exact Hrec.
      - exact Hrnd.
      - intros e He. destruct (callkey_eq_dec (lin_key e) (t, h)) as [Hk' | Hk'].
        + rewrite Hk'. apply (coup_lin_write _ _ _ _ P _ Hwf Hop Hnl). rewrite <- Hk'. exact (entry_lookup e P He).
        + apply (coup_emit_other _ _ g1 g2 x); [intros E; apply Hk'; symmetry; exact E | exact (Hcoup e He)].
      - exact Htw.
      - exact (word_emit P g1 g2 x Hage Hgwf (iswr_tw _ _ _ _ _ HC) Hnb Hword).
      - intros j Ev. destruct (Nat.eq_dec i j) as [<- | Hij].
        + rewrite (upd_neq_x m (Sq i) i _ ltac:(discriminate)), (upd_neq_y m (Sq i) i _ ltac:(discriminate)), Hx, Hy, HA.
          reflexivity.
        + rewrite (upd_sq_other m i j _ Hij) in Ev. rewrite (upd_neq_x m (Sq i) j _ ltac:(discriminate)),
            (upd_neq_y m (Sq i) j _ ltac:(discriminate)). exact (Hjev j Ev).
      - intros j Ev. destruct (Nat.eq_dec i j) as [<- | Hij].
        + rewrite upd_sq_same in Ev. replace (v + 2) with (S (S v)) in Ev by lia. cbn [Nat.even] in Ev.
          rewrite Hev in Ev. discriminate Ev.
        + rewrite (upd_sq_other m i j _ Hij) in Ev. destruct (Hjodd j Ev) as (k0 & wx & wy & Hh0 & Hop0 & Hnl0 & HA0).
          assert (Hk0 : k0 <> (t, h)).
          { intros ->. apply Hij. exact (iswr_unique i j (t, h) P Hwf Hwi (proj1 Hh0)). }
          exists k0, wx, wy. split; [| auto].
          apply (holder_emit j k0 P g1 g2 x Hh0). intros [E _]. exact (Hk0 (eq_sym E)).
      - exact (NoDup_remove_1 _ _ _ Hgnd).
    Qed.

    Theorem isl_wr_end t h i vx vy v hu (σ σ' : State VE) A Pf P (γ γ' : Ghost ES FS) :
      Isl (σ, POk (A, Pf) P, γ) -> HasOp (t, h) (fW i vx vy) P -> ~ lin_lookup (t, h) (@ls_inv FS (fW i vx vy)) P ->
      Holder i (t, h) P γ -> fst (fst σ) (Sq i) = v + 1 -> Nat.even v = true ->
      fst (fst σ) (Sx i) = vx -> fst (fst σ) (Sy i) = vy -> A i = (vx, vy) ->
      ghost_emit (t, h) (IE t hu (sWr (Sq i) (v + 2))) γ γ' -> Step VE (IE t hu (sWr (Sq i) (v + 2))) σ σ' ->
      Isl (σ', POk (A, Pf) P, γ') /\ Gsl (t, h) (σ, POk (A, Pf) P, γ) (σ', POk (A, Pf) P, γ').
    Proof.
      intros (A0 & Pf0 & P0 & Hp & Hru & HC) Hop Hnl Hh Hv Hev Hx Hy HA Hge Hst. cbn in Hp.
      injection Hp as E1 E2 E3. subst A0 Pf0 P0.
      cbn [regs ps_mem ps_ghost ps_poss fst snd] in Hru, HC.
      destruct (ghost_emit_ie _ _ _ _ _ _ Hge) as (g1 & g2 & Hγ & Hγ' & Hnb). subst γ γ'.
      pose proof (step_ie_wr _ _ _ _ _ _ Hst) as Hregs. 
      split.
      - exists A, Pf, P. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δS _ _ _ Hst Hru) |].
        unfold regs; cbn [ps_mem ps_ghost fst snd]. rewrite Hregs. exact (islc_wr_end _ _ _ _ g1 g2 t h i vx vy v hu HC Hnb Hop Hnl Hev Hx Hy HA).
      - apply gsl_intro; auto.
        + apply rt_step. eexists. exact Hst.
        + exact (emit_frame (t, h) g1 g2 (Build_ScheduledEvent (t, h) (IE t hu (sWr (Sq i) (v + 2)))) eq_refl).
        + intros k'. apply oldersub_same_domain; [reflexivity | apply incl_remove_mid].
        + intros j k' Hne Hh'. rewrite Hregs. destruct (Nat.eq_dec i j) as [<- | Hij].
          * exfalso. exact (Hne (holder_unique _ _ _ _ _ HC i k' (t, h) Hh' Hh)).
          * split; [exact (upd_sq_other (fst (fst σ)) i j _ Hij) |]. split; [apply upd_neq_x; discriminate |].
            split; [apply upd_neq_y; discriminate | reflexivity].
        + rewrite Hregs. intros j. destruct (Nat.eq_dec i j) as [<- | Hij].
          * rewrite upd_sq_same, Hv. split; [lia | intros E; lia].
          * rewrite (upd_sq_other (fst (fst σ)) i j _ Hij). split; [lia |]. intros _. split; [reflexivity |].
            intros _. split; [apply upd_neq_x; discriminate | apply upd_neq_y; discriminate].
    Qed.

    (** ** Part 8. Entry points for the method derivations (tasks .5, .6) *)

    Lemma m2w_read_body t i : M2w rc si tw (fR i) t = run (G := ES) (rnext i) [] RG.
    Proof. reflexivity. Qed.

    Lemma m2w_write_body i vx vy : M2w rc si tw (fW i vx vy) (tw i) = run (G := ES) (wnext i vx vy) [] W0.
    Proof. cbn [M2w]. rewrite Pos.eqb_refl. reflexivity. Qed.

    Lemma m2w_write_div t i vx vy : t <> tw i -> M2w rc si tw (fW i vx vy) t = div.
    Proof. intros Hne. cbn [M2w]. apply Pos.eqb_neq in Hne. rewrite Hne. reflexivity. Qed.

    (** What the call knows right after its invocation: it is at [ls_inv],
        and its pending ghost entries are exactly its footprint [evs]. *)
    Theorem pinit_facts t h op s :
      PostInvoke Isl (t, h) op (Osl t op h) s ->
      KLook (t, h) (@ls_inv FS op) s /\
      exists evs, Osl t op h evs /\
        forall e, se_owner e = (t, h) -> (In e (ps_ghost s) <-> exists ev, In ev evs /\ e = Build_ScheduledEvent (t, h) ev).
    Proof.
      intros (p0 & γ0 & evs & (A & Pf & P0 & Hp0 & _ & HC) & Hinv & Hg & HΩ & _).
      cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, HC, Hinv. subst p0.
      destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hinv) as [Hp Hfr].
      split; [exists A, Pf, (make_lin_entry (t, h) (ls_inv op) :: P0); split; [exact Hp | left; reflexivity] |].
      exists evs. split; [exact HΩ |]. intros e Ho. rewrite Hg. split.
      - intros He. apply in_app_or in He as [He | He].
        + exfalso. apply Hfr. rewrite <- Ho. exact (proj1 (ic_age _ _ _ _ _ HC) e He).
        + apply in_map_iff in He as (ev & <- & Hev). exists ev. auto.
      - intros (ev & Hev & ->). apply in_or_app. right. apply in_map. exact Hev.
    Qed.

    Lemma rprovable_div {B : Type} k Pinit (K : B -> list (Slot VE VF) -> FutureStore ES -> Prop) Γ H :
      RProvable Isl Rsl Gsl k Pinit K Γ H (@div ES B).
    Proof.
      apply (RProvable_coind Isl Rsl Gsl k Pinit K (fun _ _ p => p = div)); [| reflexivity].
      intros Γ' H' p ->. rewrite div_unfold. cbn. exact div_unfold.
    Qed.

    (** A write by a thread other than the writer of its instance: the
        body never runs ([div]), and [Osl] is [False] there, so the method
        is provable outright. *)
    Theorem sl2_write_other_provable t i vx vy :
      t <> tw i ->
      MethodProvable Isl Rsl Gsl (M2w rc si tw) t (fW i vx vy) (fun h => Osl t (fW i vx vy) h)
        (fun h r => Qsl (t, h) (fW i vx vy) r).
    Proof.
      intros Hne. apply sl2_method_provable. intros h. rewrite (m2w_write_div t i vx vy Hne). apply rprovable_div.
    Qed.

    (** The read through [run_method_provable] (hence [rp_run]): a machine
        invariant [Inv] over [rnext i] whose steps satisfy [RunStepOK].
        Superseded by [sl2_read_run_provable_rd] (Part 9): with [Qsl] the
        step premise cannot hold for any [Inv] (B-6, argued in reader-eval
        §1.3; not mechanized as a theorem);
        kept unchanged. *)
    Theorem sl2_read_run_provable t i
        (Inv : handle FS -> RSt -> list (RCall ES) -> list (Slot VE VF) -> FutureStore ES -> Prop) :
      (forall h, Inv h RG [] [] empty_store) ->
      (forall h st cs Γ H, RunCtx (t, h) Γ H cs -> Inv h st cs Γ H ->
         RunStepOK Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) (fR i) (Osl t (fR i) h)) (Inv h)
           (fun a Γ' H' => Close Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) (fR i) (Osl t (fR i) h))
                             (fun r => Qsl (t, h) (fR i) r) a Γ' H' /\ Osl t (fR i) h (own_invs Γ'))
           cs Γ H (rnext i st)) ->
      MethodProvable Isl Rsl Gsl (M2w rc si tw) t (fR i) (fun h => Osl t (fR i) h) (fun h r => Qsl (t, h) (fR i) r).
    Proof.
      intros Hi0 Hstep. apply (run_method_provable Isl Rsl Gsl (M2w rc si tw) t (fR i) _ _ (rnext i) RG Inv).
      - reflexivity.
      - intros h s Hs. exact (isl_postinvoke t h (fR i) s Hs).
      - intros h r s Hq HI Hno. exact (qsl_ret t h (fR i) r s Hq HI Hno).
      - exact Hi0.
      - exact Hstep.
    Qed.

    (** The write by its writer [tw i], through [run_method_provable]. *)
    Theorem sl2_write_run_provable i vx vy
        (Inv : handle FS -> WSt -> list (RCall ES) -> list (Slot VE VF) -> FutureStore ES -> Prop) :
      (forall h, Inv h W0 [] [] empty_store) ->
      (forall h st cs Γ H, RunCtx (tw i, h) Γ H cs -> Inv h st cs Γ H ->
         RunStepOK Isl Rsl Gsl (tw i, h) (PostInvoke Isl (tw i, h) (fW i vx vy) (Osl (tw i) (fW i vx vy) h)) (Inv h)
           (fun a Γ' H' => Close Isl Rsl Gsl (tw i, h) (PostInvoke Isl (tw i, h) (fW i vx vy) (Osl (tw i) (fW i vx vy) h))
                             (fun r => Qsl (tw i, h) (fW i vx vy) r) a Γ' H' /\ Osl (tw i) (fW i vx vy) h (own_invs Γ'))
           cs Γ H (wnext i vx vy st)) ->
      MethodProvable Isl Rsl Gsl (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl (tw i) (fW i vx vy) h)
        (fun h r => Qsl (tw i, h) (fW i vx vy) r).
    Proof.
      intros Hi0 Hstep. apply (run_method_provable Isl Rsl Gsl (M2w rc si tw) (tw i) (fW i vx vy) _ _ (wnext i vx vy) W0 Inv).
      - exact (m2w_write_body i vx vy).
      - intros h s Hs. exact (isl_postinvoke (tw i) h (fW i vx vy) s Hs).
      - intros h r s Hq HI Hno. exact (qsl_ret (tw i) h (fW i vx vy) r s Hq HI Hno).
      - exact Hi0.
      - exact Hstep.
    Qed.

    (** The assembly from the two run derivations: what tasks .5 and .6
        must provide (for every handle-indexed machine invariant).
        Superseded by [sl2rd_rlhl2_of_methods_rd] (Part 9: read premise
        with [Qrd]; the [Qsl] read premise here is unsatisfiable by B-6,
        argued); kept unchanged. *)
    Theorem sl2rd_rlhl2_of_methods :
      (forall t i, MethodProvable Isl Rsl Gsl (M2w rc si tw) t (fR i) (fun h => Osl t (fR i) h) (fun h r => Qsl (t, h) (fR i) r)) ->
      (forall i vx vy, MethodProvable Isl Rsl Gsl (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl (tw i) (fW i vx vy) h)
                         (fun h r => Qsl (tw i, h) (fW i vx vy) r)) ->
      RLHL2Hyps (VE := VE) (VF := VF) Isl Rsl Gsl (M2w rc si tw) ((regs0, []), []) (A0, []).
    Proof.
      intros Hrd Hwr. apply sl2rd_rlhl2_of_provable. intros t [i vx vy | i].
      - destruct (Pos.eq_dec t (tw i)) as [-> | Hne]; [exact (Hwr i vx vy) | exact (sl2_write_other_provable t i vx vy Hne)].
      - exact (Hrd t i).
    Qed.

    (** ** Part 9. The read postcondition [Qrd] (B-6) and per-operation
        postconditions (m-51)

        B-6 (reader-eval §1.3).  [RunCallOK] asks the derivation to cover
        every response value, so it must reach [Close] on a machine path
        that validates after fewer iterations than the footprint in the
        ghost (the ghost records invocations, not response values).  On
        such a path the read still owns the [rmb]s of the remaining
        iterations, and [owns_rmb_not_qsl] ([Coup]) refutes [Qsl] there,
        while [bw_sum] must prove the postcondition before [NoOwn] is in
        scope.  Hence the read premise of [sl2_read_run_provable],
        [sl2rd_rlhl2_of_provable], [sl2rd_rlhl2_of_methods] and
        [sl2rd_target_of_methods] cannot hold for any machine invariant
        (argued in reader-eval §1.3 from closed lemmas; the 12-step run is
        not mechanized).  The fix: the read postcondition [Qrd] adds the
        disjunct "[k] still owns a ghost entry", which [mp_ret] refutes by
        its [NoOwn] hypothesis ([qrd_ret], through the generic
        [RelaxedHoareReady.retcond_or_owned]).  Writes keep [Qsl] ([Qop]):
        their footprint has exactly seven entries and every write path has
        seven invocations, so a run that reaches the return has emitted
        them all and the new disjunct would be false there (argued, not
        checked; the same disjunct could be added for writes, sound by the
        same [retcond_or_owned], if task .6 needs it).

        The assembly lemmas below take per-operation postconditions; the
        generic one ([sl2rd_rlhl2_of_provable_rd]) has exactly the method
        premise of [RelaxedHoareCompLin.rlhl_sound_complin] /
        [RelaxedHoareGSim.rlhl2_of_provable], [∀ t op, ∃ Ω Q,
        MethodProvable …] (m-51).  These lemmas are over [VE := EIhl δS];
        by the author's option B the method derivations are over the
        history presentation [Log (EIhl δS)] ([RelaxedHoareSL2InvLog]
        lifts [Qrd] to [QrdV]; the read derivation is
        [RelaxedHoareSL2Read.read_provable_v]). *)

    Lemma owns_not_noown k Q (γ : Ghost ES FS) : Owns k Q γ -> ~ NoOwn k γ.
    Proof. intros (e & He & Ho & _) Hno. exact (Hno e He Ho). Qed.

    (** B-6, the cause: [Qsl] of a read is false while the read owns an
        [rmb] (script .rocq-review/scripts/RLHLsl_readerB6_qsl.v, proof
        unchanged up to the section parameters). *)
    Lemma owns_rmb_not_qsl k i r s : Isl s -> Owns k isRmb (ps_ghost s) -> ~ Qsl k (fR i) r s.
    Proof.
      intros (A & Pf & P & Hp & _ & HC) Hown (A' & Pf' & P' & Hp' & Hq).
      rewrite Hp in Hp'. injection Hp' as <- <- <-.
      destruct Hq as [Hl | [Hl _]];
        pose proof (ic_coup _ _ _ _ _ HC _ Hl) as Hc;
        unfold Coup in Hc; rewrite lin_key_make_lin_entry in Hc; cbn in Hc;
        apply Hc in Hown; discriminate Hown.
    Qed.

    (** The read postcondition: [k] has linearized with result [r]
        ([Qsl]), or [k] still owns a pending ghost entry (the path
        returned before its footprint was used up; refuted at the return
        by [NoOwn]). *)
    Definition Qrd (k : CallKey FS) (i : nat) (r : far (fR i)) : Assn VE VF := fun s =>
      Qsl k (fR i) r s \/ ~ NoOwn k (ps_ghost s).

    (** The per-operation postcondition: [Qrd] for reads, [Qsl] for
        writes. *)
    Definition Qop (k : CallKey FS) (op : FOp) : far op -> Assn VE VF :=
      match op as o return far o -> Assn VE VF with
      | fR i => fun r => Qrd k i r
      | fW i vx vy => fun r => Qsl k (fW i vx vy) r
      end.

    Lemma qrd_of_qsl k i r s : Qsl k (fR i) r s -> Qrd k i r s.
    Proof. intros H. left. exact H. Qed.

    (** [Qrd] holds wherever the read still owns an entry, in particular
        in the B-6 state, where [Qsl] fails ([owns_rmb_not_qsl]). *)
    Lemma qrd_of_owns k Q i r s : Owns k Q (ps_ghost s) -> Qrd k i r s.
    Proof. intros H. right. exact (owns_not_noown k Q _ H). Qed.

    Lemma qrd_noown k i r s : Qrd k i r s -> NoOwn k (ps_ghost s) -> Qsl k (fR i) r s.
    Proof. intros [H | H] Hno; [exact H | contradiction (H Hno)]. Qed.

    (** [mp_ret] for [Qrd]: the new disjunct is refuted by [NoOwn]. *)
    Theorem qrd_ret t h i r s :
      Qrd (t, h) i r s -> Isl s -> NoOwn (t, h) (ps_ghost s) -> RetCond Isl Gsl (t, h) (fR i) r s.
    Proof.
      exact (retcond_or_owned Isl Gsl (t, h) (fR i) (fun r => Qsl (t, h) (fR i) r)
               (fun r s => qsl_ret t h (fR i) r s) r s).
    Qed.

    Theorem qop_ret t h op r s :
      Qop (t, h) op r s -> Isl s -> NoOwn (t, h) (ps_ghost s) -> RetCond Isl Gsl (t, h) op r s.
    Proof. destruct op as [i vx vy | i]; cbn [Qop]; [apply qsl_ret | apply qrd_ret]. Qed.

    (** [sl2_method_provable] with the per-operation postcondition. *)
    Theorem sl2_method_provable_op t op :
      (forall h, RProvable Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) op (Osl t op h))
         (fun a Γ H => Close Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) op (Osl t op h)) (fun r => Qop (t, h) op r) a Γ H /\
                       Osl t op h (own_invs Γ))
         [] empty_store (M2w rc si tw op t)) ->
      MethodProvable Isl Rsl Gsl (M2w rc si tw) t op (fun h => Osl t op h) (fun h r => Qop (t, h) op r).
    Proof.
      intros Ht. constructor.
      - intros h s Hs. exact (isl_postinvoke t h op s Hs).
      - intros h r s Hq HI Hno. exact (qop_ret t h op r s Hq HI Hno).
      - exact Ht.
    Qed.

    (** [sl2_read_run_provable] with [Qrd]: the read through
        [run_method_provable] (hence [rp_run]), for a machine invariant
        [Inv] over [rnext i] whose steps satisfy [RunStepOK]. *)
    Theorem sl2_read_run_provable_rd t i
        (Inv : handle FS -> RSt -> list (RCall ES) -> list (Slot VE VF) -> FutureStore ES -> Prop) :
      (forall h, Inv h RG [] [] empty_store) ->
      (forall h st cs Γ H, RunCtx (t, h) Γ H cs -> Inv h st cs Γ H ->
         RunStepOK Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) (fR i) (Osl t (fR i) h)) (Inv h)
           (fun a Γ' H' => Close Isl Rsl Gsl (t, h) (PostInvoke Isl (t, h) (fR i) (Osl t (fR i) h))
                             (fun r => Qrd (t, h) i r) a Γ' H' /\ Osl t (fR i) h (own_invs Γ'))
           cs Γ H (rnext i st)) ->
      MethodProvable Isl Rsl Gsl (M2w rc si tw) t (fR i) (fun h => Osl t (fR i) h) (fun h r => Qrd (t, h) i r).
    Proof.
      intros Hi0 Hstep. apply (run_method_provable Isl Rsl Gsl (M2w rc si tw) t (fR i) _ _ (rnext i) RG Inv).
      - reflexivity.
      - intros h s Hs. exact (isl_postinvoke t h (fR i) s Hs).
      - intros h r s Hq HI Hno. exact (qrd_ret t h i r s Hq HI Hno).
      - exact Hi0.
      - exact Hstep.
    Qed.

    (** The assembly in the [∃ Ω Q] shape of [rlhl_sound_complin] (m-51):
        a derivation for every thread and operation, each with its own
        footprint and postcondition, gives [RLHL2Hyps] ([h_sem] by
        [RelaxedHoareSound.method_sound]).  No hypothesis on [si]. *)
    Theorem sl2rd_rlhl2_of_provable_rd :
      (forall t op, exists Ω Q, MethodProvable Isl Rsl Gsl (M2w rc si tw) t op Ω Q) ->
      RLHL2Hyps (VE := VE) (VF := VF) Isl Rsl Gsl (M2w rc si tw) ((regs0, []), []) (A0, []).
    Proof.
      intros Hmp. constructor.
      - intros t op. destruct (Hmp t op) as (Ω & Q & Hm). exact (method_sound Isl Rsl Gsl (M2w rc si tw) t op Ω Q Hm).
      - intros k k' s s' Hne HG. exact (gsl_rsl k k' s s' Hne HG).
      - exact invoke_rely.
      - exact return_rely.
      - exact isl_ok.
      - exact isl_init.
    Qed.

    (** From the two run derivations that tasks .5 ([Qrd]) and .6
        ([Qsl]) are to provide, a derivation of every method with the
        frozen footprint [Osl] and the per-operation postcondition [Qop]
        (writes on a thread other than [tw i]: [sl2_write_other_provable]). *)
    Theorem sl2_provable_op_of_methods_rd :
      (forall t i, MethodProvable Isl Rsl Gsl (M2w rc si tw) t (fR i) (fun h => Osl t (fR i) h) (fun h r => Qrd (t, h) i r)) ->
      (forall i vx vy, MethodProvable Isl Rsl Gsl (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl (tw i) (fW i vx vy) h)
                         (fun h r => Qsl (tw i, h) (fW i vx vy) r)) ->
      forall t op, MethodProvable Isl Rsl Gsl (M2w rc si tw) t op (fun h => Osl t op h) (fun h r => Qop (t, h) op r).
    Proof.
      intros Hrd Hwr t [i vx vy | i]; cbn [Qop].
      - destruct (Pos.eq_dec t (tw i)) as [-> | Hne]; [exact (Hwr i vx vy) | exact (sl2_write_other_provable t i vx vy Hne)].
      - exact (Hrd t i).
    Qed.

    Theorem sl2rd_rlhl2_of_methods_rd :
      (forall t i, MethodProvable Isl Rsl Gsl (M2w rc si tw) t (fR i) (fun h => Osl t (fR i) h) (fun h r => Qrd (t, h) i r)) ->
      (forall i vx vy, MethodProvable Isl Rsl Gsl (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl (tw i) (fW i vx vy) h)
                         (fun h r => Qsl (tw i, h) (fW i vx vy) r)) ->
      RLHL2Hyps (VE := VE) (VF := VF) Isl Rsl Gsl (M2w rc si tw) ((regs0, []), []) (A0, []).
    Proof.
      intros Hrd Hwr. apply sl2rd_rlhl2_of_provable_rd. intros t op.
      exists (fun h => Osl t op h), (fun h r => Qop (t, h) op r).
      exact (sl2_provable_op_of_methods_rd Hrd Hwr t op).
    Qed.

  End SL2.

  (** The target statement of tasks .4-.7
      ([RelaxedHoareSL2Prog.sl2rd_target]) from the two method
      derivations, for every [si ⊇ slRA].  Superseded by
      [sl2rd_target_of_methods_rd] and [sl2rd_prov_target_of_methods_rd]
      (Part 9: read premise with [Qrd]; the [Qsl] read premise here is
      unsatisfiable by B-6, argued); kept unchanged. *)
  Theorem sl2rd_target_of_methods :
    (forall rc si tw, (forall o o', slRA o o' -> si o o') ->
       (forall t i, MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) t (fR i)
                      (fun h => Osl rc tw t (fR i) h) (fun h r => Qsl rc si (t, h) (fR i) r)) /\
       (forall i vx vy, MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) (tw i) (fW i vx vy)
                          (fun h => Osl rc tw (tw i) (fW i vx vy) h) (fun h r => Qsl rc si (tw i, h) (fW i vx vy) r))) ->
    sl2rd_target.
  Proof.
    intros H rc si tw Hsi. destruct (H rc si tw Hsi) as [Hrd Hwr].
    exists (Isl rc si tw), (Rsl rc si), (Gsl rc si). exact (sl2rd_rlhl2_of_methods rc si tw Hrd Hwr).
  Qed.

  (** *** Part 9, continued: the targets with derivations (m-51, B-6) *)

  (** The target in the shape of the premises of
      [RelaxedHoareCompLin.rlhl_sound_complin] (latest-review m-51, script
      S3): a derivation ([MethodProvable], each operation with its own
      footprint and postcondition) for every thread and operation, and
      the side conditions (the fields of [RLHL2Hyps] other than [h_sem],
      which the first conjunct gives through [method_sound]).  Unlike
      [RelaxedHoareSL2Prog.sl2rd_target], it cannot be met by a direct
      [MethodSem] proof (route S).  Over [VE := EIhl δS], as
      [sl2rd_target]; by option B the target of the derivations moved to
      [Log (EIhl δS)].  Superseded and not citable: the citable target is
      [RelaxedHoareSL2InvLog.sl2rd_prov_target_v], proved as
      [RelaxedHoareSL2Read.sl2_main]. *)
  Definition sl2rd_prov_target : Prop :=
    forall rc si tw, (forall o o', slRA o o' -> si o o') ->
      exists I R G,
        (forall t op, exists Ω Q,
           MethodProvable (VE := EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
             I R G (M2w rc si tw) t op Ω Q) /\
        RLHL2Hyps (VE := EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
          I R G (M2w rc si tw) ((regs0, []), []) (A0, []).

  (** Script S3 of latest-review ([prov_imp]). *)
  Lemma sl2rd_prov_target_imp : sl2rd_prov_target -> sl2rd_target.
  Proof. intros H rc si tw Hs. destruct (H rc si tw Hs) as (I & R & G & _ & HH). exists I, R, G. exact HH. Qed.

  (** [sl2rd_target_of_methods] with the B-6 read postcondition [Qrd],
      concluding the derivation-carrying target. *)
  Theorem sl2rd_prov_target_of_methods_rd :
    (forall rc si tw, (forall o o', slRA o o' -> si o o') ->
       (forall t i, MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) t (fR i)
                      (fun h => Osl rc tw t (fR i) h) (fun h r => Qrd rc si (t, h) i r)) /\
       (forall i vx vy, MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) (tw i) (fW i vx vy)
                          (fun h => Osl rc tw (tw i) (fW i vx vy) h) (fun h r => Qsl rc si (tw i, h) (fW i vx vy) r))) ->
    sl2rd_prov_target.
  Proof.
    intros H rc si tw Hsi. destruct (H rc si tw Hsi) as [Hrd Hwr].
    exists (Isl rc si tw), (Rsl rc si), (Gsl rc si). split.
    - intros t op. exists (fun h => Osl rc tw t op h), (fun h r => Qop rc si (t, h) op r).
      exact (sl2_provable_op_of_methods_rd rc si tw Hrd Hwr t op).
    - exact (sl2rd_rlhl2_of_methods_rd rc si tw Hrd Hwr).
  Qed.

  (** [sl2rd_target_of_methods] with [Qrd] (supersedes it). *)
  Theorem sl2rd_target_of_methods_rd :
    (forall rc si tw, (forall o o', slRA o o' -> si o o') ->
       (forall t i, MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) t (fR i)
                      (fun h => Osl rc tw t (fR i) h) (fun h r => Qrd rc si (t, h) i r)) /\
       (forall i vx vy, MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) (tw i) (fW i vx vy)
                          (fun h => Osl rc tw (tw i) (fW i vx vy) h) (fun h r => Qsl rc si (tw i, h) (fW i vx vy) r))) ->
    sl2rd_target.
  Proof. intros H. exact (sl2rd_prov_target_imp (sl2rd_prov_target_of_methods_rd H)). Qed.

End RelaxedHoareSL2Inv.
