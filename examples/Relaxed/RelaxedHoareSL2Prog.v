(** * RelaxedHoareSL2Prog: the program layer of the RLHL SeqLock (WRd)

    One object with N SeqLock instances ([i : nat]) over one shared
    memory: sequential COH registers plus ordering-only barriers.
    Cross-instance order comes from the shared barriers (the barrier
    ghost locations [GBw]/[GBr] are global, and [dto] orders a data
    access of any instance against a barrier of any instance), not from
    the tensor ⊗ of separate SeqLock objects (relaxedlin.tex:191, which
    combines specifications by the fence-mode contract; the [mode]
    fields here are all [Local], see Scope) (review m-70).  The writer
    is WRd (author decision RS-1, 2026-10-15: "only WRd"): a
    single-writer seqcount whose closing
    increment reuses the opening read (cached v; Boehm-style), in the
    wording of the author decision on review M-23.  It is not the Linux
    seqcount writer.  The Linux-literal writer reloads [Sq i] before the
    closing increment; on this underlay (no store forwarding) that
    reloading writer has no SB execution (argued, review M-23; not
    proved, and "is SC" is not claimed).  So the SB datum
    ([RelaxedHoareSL2Exec.sb2_exec_rd], SB without own reads) and the
    single-writer datum ([RelaxedHoareSL2Exec.sw_exec]) depend on the
    cached-v encoding.  This file holds the definitions and
    execution-level facts.  It proves no RLHL triple and no
    relaxed-linearizability result; the RLHL proof is in
    [RelaxedHoareSL2Write] and [RelaxedHoareSL2Read] (main theorem
    [RelaxedHoareSL2Read.sl2_main]).

    Plan: [.rocq-review/tasks/RLHL-seqlock.md] §2.1-§2.3 together with its
    Addendum, which overrides §2-§3 (no [WMode], no [sInc], overlay
    relation [slRA]); task .2.

    ** Map to the plan

    - Part 1 (§2.1, underlay).
      - [SLoc] ([Sq i | Sx i | Sy i]); [GLoc] (data locations plus the
        barrier ghosts [GBw]/[GBr]); [SOp] = [sRd]/[sWr]/[sWmb]/[sRmb].
        [sInc] is omitted: WRd increments [Sq i] by a read and a write.
      - [ocat] (rd ↦ DR, wr ↦ DW, wmb ↦ Wmb, rmb ↦ Rmb); [sindep rc]
        (different ghost location and [WindowTable.dto rc] false);
        [E_S rc] and [E_S_well_formed].
      - [sindep_coh]: on reads and writes, [sindep] holds iff the
        locations differ, which is I_COH (overview.tex:164).
        [E_S_table]: the barrier entries.  [sindep_rc_vacuous]:
        [sindep true] and [sindep false] coincide.
      - The register file [Regs]/[upd]/[δS] (barriers are no-ops); the
        underlay record extractor [natv] with [rd_rec_inj].
    - Part 2 (§2.2, overlay).
      - [FOp] = [fW i vx vy] (result unit) | [fR i] (result nat*nat).
      - [slsi]: cross-instance read/write pairs in both directions, which
        is the [fcat]-table complement on distinct instances
        ([slsi_table]); kept for comparison.
      - [slRA]: older [fW i], younger [fR j], i ≠ j.  This is the
        Addendum's target relation; it has the shape of I_RA
        (trace.tex:96: an older write and a younger read of a different
        location), with instances for locations.  [slRA_slsi]:
        [slRA ⊆ slsi].
      - [F2 si] (well-formed if [si] is irreflexive; only this direction
        is proved); [δF] over
        [AS = nat -> nat*nat]; [A0]; the overlay record extractor [pairv]
        with [fR_rec_inj].
    - Part 3 (§2.3 and Addendum, program).
      - [wnext], the WRd writer: [v <- rd Sq_i; wr Sq_i (v+1) [dix 0];
        wmb; wr Sx_i vx; wr Sy_i vy; wmb; wr Sq_i (v+2) [dix 0]].  The
        closing write uses the cached [v] (no reload of [Sq_i]; M-23).
      - [rnext], the reader: [s <- rd Sq_i; rmb; a <- rd Sx_i;
        c <- rd Sy_i; rmb; s' <- rd Sq_i; if rok s s' then ret (a,c)
        else loop], with [rok s s' = even s && (s =? s')].  The parity
        check is deferred to the end of the iteration; the Linux reader
        instead spins until the sequence number is even before its first
        [rmb].
      - The module [M2 rc si] and the guarded module [M2w rc si tw]: a
        write [fW i ..] by a thread [t ≠ tw i] is [div] (P1 as a guard,
        port of RelaxedHoareLatchProg Part 8: [div], [div_no_produce]).
      - [P1 tw]: only [tw i] writes instance [i].  [mtraces_guard]
        (under P1, every trace of [M2] is one of [M2w]),
        [mtraces_unguard], [mtraces_guard_P1] (every trace of [M2w]
        satisfies P1), for every underlay LTS [V].
    - Part 4 (blocking facts).
      - [lb_blocking]: between an older read of instance j and a younger
        WRd write of instance i ≠ j, the only ordered pair is
        ([rmb], [rd Sq_i]); in particular [rmb_blocks_rd].  So a write
        cannot start before every older same-thread read has emitted its
        [rmb]s.  That this excludes cross-SeqLock LB for WRd (plan §0, §7
        check 3) is argued here, not proved; the formal negative is
        [RelaxedHoareSL2Read.lb2_not_trace_rd] (through the main
        theorem's [rel_lin] corollary).
      - [sb_blocking]: between an older WRd write of instance i and a
        younger read of instance j ≠ i, the only ordered pair is
        ([rd Sq_i], [rmb]).  Once the write's [rd Sq_i] is emitted, the
        whole read may overtake the rest of the write (the SB direction).
      - [same_instance_blocking]; the in-call orders [rd_order] and
        [wr_order] (plan §2.3: no tag is needed for them).
      - Lifting to the module frontier: [inv_cross_iff] (two same-thread
        invocations may cross iff [sindep]), [select_blocked] (generic)
        and [rmb_blocks_select].
    - Part 5 (tactics): ports of the [ex_*] and [m_*] tactics of
      RelaxedHoareLatchProg Part 10.  Changes: [ex_step] proves handle
      freshness by [lia] (handles [h + k] for a variable [h]); [cross_ok]
      also uses tag bounds [forall q, tev_deps m q -> q = h]; [m_finish]
      skips finished pool entries; [rok_simpl], [unpack_forall],
      [untag_rw_in], [deps_none]/[deps_within] and [complete_tac] are
      new.
    - Part 6 (method executions), for every handle base [h], every value
      read and every [rc], [si]: [rd_prod] (one validating iteration),
      [rd_retry_prod_gen] (one failed iteration, then a validating one),
      [rd_retry_prod] (the plan's 24-event read of instance 2 with one
      retry returning (1,1)), [wr_prod], [wr_guard_prod] (the guarded
      write by [tw i]), [wr_guard_none] (by any other thread: no trace).
      Each states the exact untagged events and an upper bound on the
      tags: reads are untagged; the write's tags are within its first
      handle.
    - Part 7 (non-vacuity: module executions of [M2w] over [EI δS] from
      [regs0], for every [rc], [si], [tw] with [tw 1] the writer).
      - [sl2_write_read_mtraces]: a write of (1,1) into instance 1 by
        [t1 = tw 1], then a read of instance 1 by any [t2] (in particular
        another thread) returning (1,1); each call's events are in
        program order.  The trace is complete ([sl2_write_read_complete]).
      - [sl2_read_overtakes_write]: on one thread [t = tw 1], a write of
        instance 1 is invoked, then a read of instance 2.  After the
        write's [rd Sq_1], each of the read's 12 events crosses the 12
        pending events of the write.  The younger read returns (0,0)
        while the older write is pending, and then the write completes
        ([sl2_read_overtakes_write_complete]).  This is a module-level
        (W, R) reordering across instances, of the kind that an [slRA]
        pair relaxes.  It is single-threaded, and its overlay trace is
        relaxed-linearizable already at ∅ (witness W; R: the read is of
        another instance and returns its initial pair;
        [RelaxedHoareSL2Exec.ov_rel_lin_empty], with [ov_exec] tying its
        trace [ov_trace] to this theorem), so it is no
        evidence that [slRA] is needed.  That evidence is two-thread:
        [RelaxedHoareSL2Exec.sb2_exec_rd] with [sb2_not_rel_lin0], and
        [sw_exec] with [sw_not_rel_lin].
    - Part 8 (targets, NOT proved in this file): [sl2rd_target] and
      [sl2rd_relin_target], the statement shapes of tasks .4-.7, as
      [Definition ... : Prop].  [sl2rd_relin_target] is proved as
      [RelaxedHoareSL2Read.sl2_rel_lin].  [sl2rd_target] (over [EIhl])
      is superseded and not citable (see Part 8).

    ** Scope and limitations

    - The underlay is a sequential, multi-copy-atomic register file (one
      value per location, [δS]) with ordering-only barriers ([wmb]/[rmb]
      change no register; their only role is the [WindowTable.dto]
      entries of [ocat]) and the table-derived semi-independence
      [sindep rc] (same-location pairs are always ordered).  It is not
      RC11, ARMv8, oMCA, or the buffered cell of [memory/Cell.v].
    - [rc] is vacuous.  On the categories used here ([DR], [DW], [Rmb],
      [Wmb]) the table [WindowTable.dto rc] is the same for both
      profiles: its [rc] disjunct needs acquire/release categories,
      which [ocat] and [fcat] never produce.  So [sindep true] and
      [sindep false] coincide ([sindep_rc_vacuous], by case analysis),
      and every statement
      quantified over [rc] says nothing more than its instance at one
      profile.
    - The [mode] fields of [E_S] and [F2] are all [Local] and play no
      role: modes matter only under horizontal composition, which
      nothing here uses.
    - Writer WRd only; the plan's WInc row and [sInc] are dropped (RS-1).
      So no cross-SeqLock LB is exhibited here (see [lb_blocking]); the LB
      datum of implex.tex:3 is not part of this deliverable.
    - The writer is a single-writer seqcount whose closing increment
      reuses the opening read (cached v; Boehm-style), not the Linux
      seqcount writer (see the first paragraph; M-23).
    - The reader checks parity only at the end of an iteration
      ([rok]); the Linux reader spins until the sequence number is even
      before its first [rmb].
    - P1 (one writer thread [tw i] per instance) is a guard in [M2w], not
      a hypothesis: a write by another thread runs [div], which produces
      no trace, so that invocation is never taken (P1 is modelled by
      disabled invocations, not by an error or a checked precondition).
      Every result about [M2w] is therefore a result for one writer
      thread per instance.  Overlapping writes of one instance by [tw i]
      are allowed; they are ordered by the same-location clause.  The
      precondition form, for the unguarded [M2] and its traces that
      satisfy [P1 tw], is [RelaxedHoareSL2Read.sl2_complin_unguarded]
      (and [sl2_rel_lin_unguarded]; review m-69).
    - Tags: written by hand, not computed by the paper's dependency
      policy (impl.tex:120).  The reader uses none.  The writer's two
      [wr Sq_i] are tagged with its [rd Sq_i] ([dix [0]]), the data
      dependency of [v+1]/[v+2].  Under the paper's memory instance of
      the policy (every operation except a plain read is
      control-ordered, impl.tex:141), the barriers of reader iterations
      2 and later would also carry the handles of the failed validation
      (control dependency, the set κ), which [rnext] omits.
      That fewer tags give more module traces, so that the untagged
      reader is more permissive than the policy-tagged one, is argued,
      not proved (no tag-monotonicity lemma for [MTraces]).
    - The traces of [M2 rc si] are the same events for every [si], but
      typed by [F2 si].
    - The production lemmas give tag upper bounds only.  The witnesses of
      Part 7 use fixed values and fixed instances 1 and 2.

    ** K / S / P / R

    - K (kernel): all 56 [Lemma]/[Theorem] declarations of this file are
      closed under the global context ([Print Assumptions] run on each,
      Rocq 9.3.0).  In particular no [classic] and no [eq_rect_eq].  Record
      values are compared through the first-order projections
      [natv]/[pairv], and [sindep] is a boolean equation, so its double
      negation is eliminated by [sindep_dec].
    - S (statements): as listed above.  The guard theorems hold for every
      underlay LTS; the productions for every handle base and value; the
      two module executions for every [rc], [si], [tw] (with [tw 1] the
      writer's thread).
    - P (paper): there is no SeqLock text in the main paper (spec.tex is
      not input, main.tex:229).  Appendix/SeqLock.tex describes a
      different, TicketLock-based object over TSO cells (plan §1).  The
      underlay is the COH interface of overview.tex:164 extended with
      barriers.  The barrier categories [Wmb]/[Rmb] used by [ocat] and
      [fcat] are not among the paper's four fence modes (plan RS-7); the
      [mode] fields here are all [Local].  [slRA] has the shape of I_RA
      (trace.tex:96).  The SB data of this development are SB without
      own reads; the store-buffering-with-own-reads example of
      trace.tex:94-107, which ordinary registers cannot explain under
      I_RA (:107), needs store forwarding, which this underlay lacks.
      Reusing the opening read removes the reload, an own read after an
      own write, so the cached-v encoding emulates at the program level
      part of what store forwarding gives (M-23).  The verified [slRA]
      contract is falsified under store forwarding: the SB-with-own-reads
      outcome is not relaxed-linearizable under any relation contained
      in [slRA] ([RelaxedHoareSL2Exec.sbo_not_rel_lin], kernel-checked at
      trace level; that x86-TSO and ARMv8 produce this outcome is argued,
      not mechanized).  This is an MCA-only data point (review M-29).
    - R (reviewers): groundwork for popl2027-reviews.md:215 ("No example
      verified on the COH model").  Nothing here answers :212 or
      :311-316.  This file alone verifies nothing; the RLHL proof is
      [RelaxedHoareSL2Inv], [RelaxedHoareSL2InvLog],
      [RelaxedHoareSL2Write] and [RelaxedHoareSL2Read] (tasks .4-.7;
      main theorem [RelaxedHoareSL2Read.sl2_main]). *)

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
Require Import models.view.PrefixView.
Require Import examples.Relaxed.WindowTable.

Import ListNotations.

Module RelaxedHoareSL2Prog.
  Module WT := WindowTable.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedHoareRun.

  (** ** Part 1. The underlay [E_S rc]: COH registers plus barriers *)

  (** Locations of instance [i]: the sequence number [Sq i] and the two
      data registers [Sx i], [Sy i]. *)
  Inductive SLoc : Type := Sq (i : nat) | Sx (i : nat) | Sy (i : nat).

  Definition SLoc_eq_dec (a b : SLoc) : {a = b} + {a <> b}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  (** Boolean location equality (it computes on concrete locations, so
      [upd] below reduces by [cbn]). *)
  Definition sl_beq (a b : SLoc) : bool :=
    match a, b with
    | Sq i, Sq j | Sx i, Sx j | Sy i, Sy j => Nat.eqb i j
    | _, _ => false
    end.

  Lemma sl_beq_spec a b : sl_beq a b = true <-> a = b.
  Proof.
    destruct a, b; cbn; try (split; intros H; discriminate H);
      rewrite Nat.eqb_eq; split; intros H; first [subst; reflexivity | injection H as H; exact H].
  Qed.

  Lemma sl_beq_refl a : sl_beq a a = true.
  Proof. apply sl_beq_spec. reflexivity. Qed.

  Lemma sl_beq_false_iff a b : sl_beq a b = false <-> a <> b.
  Proof. rewrite <- not_true_iff_false, sl_beq_spec. reflexivity. Qed.

  Lemma sl_beq_false a b : a <> b -> sl_beq a b = false.
  Proof. intros Hn. destruct (sl_beq a b) eqn:E; [apply sl_beq_spec in E; contradiction | reflexivity]. Qed.

  (** Ghost locations for the same-location clause: the data locations
      and one ghost location per barrier kind ([TableBarrier]'s [GBw],
      [GBr]), so that two barriers of one kind are always ordered. *)
  Inductive GLoc : Type := GD (l : SLoc) | GBw | GBr.

  Definition gl_beq (a b : GLoc) : bool :=
    match a, b with
    | GD l, GD l' => sl_beq l l'
    | GBw, GBw | GBr, GBr => true
    | _, _ => false
    end.

  Lemma gl_beq_spec a b : gl_beq a b = true <-> a = b.
  Proof.
    destruct a as [l | |], b as [l' | |]; cbn; try (split; intros H; first [reflexivity | discriminate H]).
    rewrite sl_beq_spec. split; intros H; [subst; reflexivity | injection H as H; exact H].
  Qed.

  (** The operations: read, write, and the two barriers.  (No [sInc]: the
      WRd writer increments [Sq i] by a read and a write.) *)
  Inductive SOp : Type :=
  | sRd (l : SLoc)
  | sWr (l : SLoc) (v : nat)
  | sWmb
  | sRmb.

  Definition sar (o : SOp) : Type := match o with sRd _ => nat | _ => unit end.

  Definition SSig : Sig.t := {| Sig.op := SOp; Sig.ar := sar |}.

  Definition ogl (o : SOp) : GLoc :=
    match o with sRd l | sWr l _ => GD l | sWmb => GBw | sRmb => GBr end.

  Definition ocat (o : SOp) : WT.DCat :=
    match o with sRd _ => WT.DR | sWr _ _ => WT.DW | sWmb => WT.Wmb | sRmb => WT.Rmb end.

  (** Semi-independence: a different (ghost) location, and no order in the
      table [WindowTable.dto rc]. *)
  Definition sindep (rc : bool) (o o' : SOp) : Prop :=
    (gl_beq (ogl o) (ogl o') || WT.dto rc (ocat o) (ocat o')) = false.

  Definition E_S (rc : bool) : RelaxedSig.t :=
    {| effect := SSig; handle := nat; semi_independent := sindep rc; mode := fun _ => Local |}.

  Lemma sindep_dec rc o o' : {sindep rc o o'} + {~ sindep rc o o'}.
  Proof. unfold sindep. destruct (_ || _); [right; discriminate | left; reflexivity]. Defined.

  Lemma sindep_iff rc o o' :
    sindep rc o o' <-> ogl o <> ogl o' /\ WT.dto rc (ocat o) (ocat o') = false.
  Proof.
    unfold sindep. rewrite orb_false_iff. split.
    - intros [Hg Hd]. split; [| exact Hd]. intros E. rewrite E, (proj2 (gl_beq_spec _ _) eq_refl) in Hg. discriminate.
    - intros [Hg Hd]. split; [| exact Hd]. destruct (gl_beq _ _) eqn:E; [apply gl_beq_spec in E; contradiction | reflexivity].
  Qed.

  (** Two calls at one (ghost) location are never semi-independent; in
      particular [sindep] is irreflexive. *)
  Lemma sindep_same_loc rc o o' : ogl o = ogl o' -> ~ sindep rc o o'.
  Proof. intros E H. apply sindep_iff in H as [H _]. contradiction. Qed.

  Lemma E_S_well_formed rc : RelaxedSig.well_formed (E_S rc).
  Proof.
    constructor; cbn.
    - intros o H. exact (sindep_same_loc rc o o eq_refl H).
    - intros; exact I.
    - intros; exact I.
  Qed.

  (** On reads and writes, [sindep] is exactly I_COH (overview.tex:164):
      the four kinds of pairs at distinct locations (DR/DW pairs are
      never ordered by the table, both profiles). *)
  Lemma sindep_coh rc l l' v v' :
    (sindep rc (sRd l) (sRd l') <-> l <> l') /\
    (sindep rc (sRd l) (sWr l' v') <-> l <> l') /\
    (sindep rc (sWr l v) (sRd l') <-> l <> l') /\
    (sindep rc (sWr l v) (sWr l' v') <-> l <> l').
  Proof.
    assert (E : forall c d, (c = WT.DR \/ c = WT.DW) -> (d = WT.DR \/ d = WT.DW) -> WT.dto rc c d = false)
      by (intros c d [-> | ->] [-> | ->]; destruct rc; reflexivity).
    unfold sindep; cbn [ogl ocat gl_beq].
    rewrite !E by auto. rewrite !orb_false_r, !sl_beq_false_iff. tauto.
  Qed.

  (** The barrier table (both profiles): a read is ordered with [rmb] in
      both directions, a write with [wmb] in both directions, two barriers
      of one kind are ordered; reads and [wmb], writes and [rmb], and the
      two kinds of barrier are not. *)
  Lemma E_S_table rc l v :
    ~ sindep rc (sRd l) sRmb /\ ~ sindep rc sRmb (sRd l) /\
    ~ sindep rc (sWr l v) sWmb /\ ~ sindep rc sWmb (sWr l v) /\
    ~ sindep rc sWmb sWmb /\ ~ sindep rc sRmb sRmb /\
    sindep rc (sRd l) sWmb /\ sindep rc sWmb (sRd l) /\
    sindep rc (sWr l v) sRmb /\ sindep rc sRmb (sWr l v) /\
    sindep rc sWmb sRmb /\ sindep rc sRmb sWmb.
  Proof. unfold sindep. repeat split; destruct rc; cbn; first [reflexivity | discriminate]. Qed.

  (** [rc] is vacuous (review m-68): on the categories that [ocat]
      produces ([DR], [DW], [Wmb], [Rmb]) the table [WT.dto rc] does not
      depend on [rc], so the two profiles give the same semi-independence.
      By case analysis on both operations. *)
  Lemma sindep_rc_vacuous o o' : sindep true o o' <-> sindep false o o'.
  Proof. destruct o as [l | l v | |], o' as [l' | l' v' | |]; unfold sindep; cbn; reflexivity. Qed.

  (** *** The sequential COH register file *)

  Definition Regs : Type := SLoc -> nat.

  Definition regs0 : Regs := fun _ => 0.

  Definition upd (m : Regs) (l : SLoc) (v : nat) : Regs :=
    fun l' => if sl_beq l l' then v else m l'.

  Lemma upd_eq m l v : upd m l v l = v.
  Proof. unfold upd. rewrite sl_beq_refl. reflexivity. Qed.

  Lemma upd_neq m l l' v : l <> l' -> upd m l v l' = m l'.
  Proof. intros Hn. unfold upd. rewrite (sl_beq_false _ _ Hn). reflexivity. Qed.

  (** A read returns the current value, a write updates it, the barriers
      leave the registers unchanged. *)
  Definition δS (m : Regs) (o : SOp) : sar o -> Regs -> Prop :=
    match o as o0 return sar o0 -> Regs -> Prop with
    | sRd l => fun r m' => r = m l /\ m' = m
    | sWr l v => fun _ m' => m' = upd m l v
    | sWmb | sRmb => fun _ m' => m' = m
    end.

  (** The value of an underlay record: the result of a read, [0]
      otherwise.  A first-order projection, so that equal read records
      have equal results without [eq_rect_eq]. *)
  Definition natv {rc : bool} (x : RelaxedTraceLin.Op (E_S rc)) : nat :=
    match RelaxedTraceLin.op_op x as o return sar o -> nat with
    | sRd _ => fun r => r
    | _ => fun _ => 0
    end (RelaxedTraceLin.op_ret x).

  Lemma natv_rd {rc : bool} u l (r : nat) : natv (@RelaxedTraceLin.Build_Op (E_S rc) u (sRd l) r) = r.
  Proof. reflexivity. Qed.

  Lemma rd_rec_inj {rc : bool} u l (r1 r2 : nat) :
    @RelaxedTraceLin.Build_Op (E_S rc) u (sRd l) r1 = @RelaxedTraceLin.Build_Op (E_S rc) u (sRd l) r2 -> r1 = r2.
  Proof. intros H. exact (f_equal natv H). Qed.

  (** ** Part 2. The overlay [F2 si]: one object with N SeqLock instances
      (over one shared memory; see the header, review m-70) *)

  (** [fW i vx vy] writes the pair [(vx, vy)] into instance [i]; [fR i]
      reads the pair of instance [i]. *)
  Inductive FOp : Type := fW (i vx vy : nat) | fR (i : nat).

  Definition far (o : FOp) : Type := match o with fW _ _ _ => unit | fR _ => (nat * nat)%type end.

  Definition FSig : Sig.t := {| Sig.op := FOp; Sig.ar := far |}.

  Definition finst (o : FOp) : nat := match o with fW i _ _ | fR i => i end.

  (** The categories a SeqLock exports: write ↦ [Wmb], read ↦ [Rmb]. *)
  Definition fcat (o : FOp) : WT.DCat := match o with fW _ _ _ => WT.Wmb | fR _ => WT.Rmb end.

  (** Cross-instance read/write pairs, in both directions (the plan's
      WInc relation; kept for comparison). *)
  Definition slsi (o o' : FOp) : Prop :=
    match o, o' with
    | fR i, fW j _ _ | fW i _ _, fR j => i <> j
    | _, _ => False
    end.

  (** The WRd target relation (Addendum): an older write of instance [i]
      and a younger read of instance [j ≠ i] (the I_RA shape of
      trace.tex:96, with instances for locations). *)
  Definition slRA (o o' : FOp) : Prop :=
    match o, o' with
    | fW i _ _, fR j => i <> j
    | _, _ => False
    end.

  Definition F2 (si : FOp -> FOp -> Prop) : RelaxedSig.t :=
    {| effect := FSig; handle := nat; semi_independent := si; mode := fun _ => Local |}.

  (** [slsi] is the complement of the table on the exported categories,
      restricted to distinct instances (both profiles). *)
  Lemma slsi_table rc o o' : slsi o o' <-> finst o <> finst o' /\ WT.dto rc (fcat o) (fcat o') = false.
  Proof. destruct o, o', rc; cbn; split; first [intros [_ H]; discriminate H | tauto]. Qed.

  Lemma slRA_slsi o o' : slRA o o' -> slsi o o'.
  Proof. destruct o, o'; cbn; tauto. Qed.

  Lemma slRA_iff o o' : slRA o o' <-> exists i vx vy j, o = fW i vx vy /\ o' = fR j /\ i <> j.
  Proof.
    split.
    - destruct o as [i vx vy | i], o' as [j wx wy | j]; cbn; try contradiction.
      intros H. exists i, vx, vy, j. auto.
    - intros (i & vx & vy & j & -> & -> & H). exact H.
  Qed.

  Lemma slsi_irrefl o : ~ slsi o o.
  Proof. destruct o; cbn; auto. Qed.

  Lemma slRA_irrefl o : ~ slRA o o.
  Proof. destruct o; cbn; auto. Qed.

  (** [F2 si] is well-formed if [si] is irreflexive (the modes are
      [Local]); the converse is not proved here. *)
  Lemma F2_well_formed (si : FOp -> FOp -> Prop) :
    (forall o, ~ si o o) -> RelaxedSig.well_formed (F2 si).
  Proof.
    intros Hirr. constructor; cbn.
    - intros o H. exact (Hirr o H).
    - intros; exact I.
    - intros; exact I.
  Qed.

  Lemma F2_slRA_well_formed : RelaxedSig.well_formed (F2 slRA).
  Proof. apply F2_well_formed. exact slRA_irrefl. Qed.

  Lemma F2_slsi_well_formed : RelaxedSig.well_formed (F2 slsi).
  Proof. apply F2_well_formed. exact slsi_irrefl. Qed.

  Lemma F2_empty_well_formed : RelaxedSig.well_formed (F2 (fun _ _ => False)).
  Proof. apply F2_well_formed. intros o []. Qed.

  (** *** The sequential specification: N atomic pair registers *)

  Definition AS : Type := nat -> (nat * nat).

  Definition A0 : AS := fun _ => (0, 0).

  Definition Aupd (A : AS) (i : nat) (p : nat * nat) : AS := fun j => if Nat.eqb i j then p else A j.

  Definition δF (A : AS) (o : FOp) : far o -> AS -> Prop :=
    match o as o0 return far o0 -> AS -> Prop with
    | fW i vx vy => fun _ A' => A' = Aupd A i (vx, vy)
    | fR i => fun r A' => r = A i /\ A' = A
    end.

  (** The value of an overlay record: the result of a read, [(0, 0)]
      otherwise (first-order, as [natv]). *)
  Definition pairv {si : FOp -> FOp -> Prop} (x : RelaxedTraceLin.Op (F2 si)) : nat * nat :=
    match RelaxedTraceLin.op_op x as o return far o -> nat * nat with
    | fR _ => fun r => r
    | _ => fun _ => (0, 0)
    end (RelaxedTraceLin.op_ret x).

  Lemma fR_rec_inj {si : FOp -> FOp -> Prop} u i (r1 r2 : nat * nat) :
    @RelaxedTraceLin.Build_Op (F2 si) u (fR i) r1 = @RelaxedTraceLin.Build_Op (F2 si) u (fR i) r2 -> r1 = r2.
  Proof. intros H. exact (f_equal pairv H). Qed.

  (** ** Part 3. The programs and the modules *)

  (** States of the WRd writer: [W0] before [rd Sq_i]; then, with the
      value [v] read, before each of its six remaining calls. *)
  Inductive WSt : Type := W0 | W1 (v : nat) | W2 (v : nat) | W3 (v : nat) | W4 (v : nat) | W5 (v : nat) | W6 (v : nat) | WD.

  (** The WRd writer, a single-writer seqcount whose closing increment
      reuses the opening read (cached v; Boehm-style): call 0 reads
      [Sq i]; the two writes of [Sq i] are tagged with call 0
      ([dix [0]]), the data dependency of their values; no other call is
      tagged.  The closing write [wr Sq_i (v+2)] uses the cached [v] of
      call 0.  It is not the Linux seqcount writer: the Linux-literal
      writer reloads [Sq i] before the closing increment, and on this
      underlay (no store forwarding) that reloading writer has no SB
      execution (argued, review M-23; not proved).  So the SB datum of
      [RelaxedHoareSL2Exec] depends on this encoding. *)
  Definition wnext (i vx vy : nat) (st : WSt) : SStep SSig WSt unit :=
    match st with
    | W0 => SCall (sRd (Sq i)) [] (fun v => W1 v)
    | W1 v => SCall (sWr (Sq i) (v + 1)) [0] (fun _ => W2 v)
    | W2 v => SCall sWmb [] (fun _ => W3 v)
    | W3 v => SCall (sWr (Sx i) vx) [] (fun _ => W4 v)
    | W4 v => SCall (sWr (Sy i) vy) [] (fun _ => W5 v)
    | W5 v => SCall sWmb [] (fun _ => W6 v)
    | W6 v => SCall (sWr (Sq i) (v + 2)) [0] (fun _ => WD)
    | WD => SDone tt
    end.

  (** States of the reader: [RG] begins an iteration; [RA s] .. [RT s a c]
      carry the values read so far; [RD a c] is done. *)
  Inductive RSt : Type :=
  | RG | RA (s : nat) | RX (s : nat) | RY (s a : nat) | RB (s a c : nat) | RT (s a c : nat) | RD (a c : nat).

  (** The reader's validation: the first read of [Sq i] is even and equal
      to the second. *)
  Definition rok (s s' : nat) : bool := Nat.even s && Nat.eqb s s'.

  Lemma rok_true s : Nat.even s = true -> rok s s = true.
  Proof. intros H. unfold rok. rewrite H, Nat.eqb_refl. reflexivity. Qed.

  Lemma rok_spec s s' : rok s s' = true <-> Nat.even s = true /\ s = s'.
  Proof. unfold rok. rewrite andb_true_iff, Nat.eqb_eq. tauto. Qed.

  (** The reader; no call is tagged. *)
  Definition rnext (i : nat) (st : RSt) : SStep SSig RSt (nat * nat) :=
    match st with
    | RG => SCall (sRd (Sq i)) [] (fun s => RA s)
    | RA s => SCall sRmb [] (fun _ => RX s)
    | RX s => SCall (sRd (Sx i)) [] (fun a => RY s a)
    | RY s a => SCall (sRd (Sy i)) [] (fun c => RB s a c)
    | RB s a c => SCall sRmb [] (fun _ => RT s a c)
    | RT s a c => SCall (sRd (Sq i)) [] (fun s' => if rok s s' then RD a c else RG)
    | RD a c => SDone (a, c)
    end.

  (** The module, for an arbitrary overlay relation [si] (the traces of
      [M2 rc si] are the same events for every [si], typed differently). *)
  Definition M2 (rc : bool) (si : FOp -> FOp -> Prop) : RelaxedModuleImpl (E_S rc) (F2 si) :=
    fun op _ =>
      match op as o return Prog (E_S rc) (far o) with
      | fW i vx vy => run (G := E_S rc) (wnext i vx vy) [] W0
      | fR i => run (G := E_S rc) (rnext i) [] RG
      end.

  (** *** The guarded module [M2w] (precondition P1 by a thread guard) *)

  (** A body that never produces a trace (port of
      RelaxedHoareLatchProg.div). *)
  CoFixpoint div {E : RelaxedSig.t} {R : Type} : Prog E R := Tau div.

  Lemma div_unfold {E R} : @div E R = Tau div.
  Proof. rewrite (PPid div) at 1. reflexivity. Qed.

  Lemma div_no_produce {E R} t (tr : list (TaggedEvent E)) (r : R) : ~ program_produces_tagged t div tr r.
  Proof.
    intros (c' & Hex & Hterm).
    assert (Hinv : forall (c : ProgramConfig E R) tr c', program_execution_tagged t c tr c' ->
                     pc_prog c = div -> pc_prog c' = div).
    { clear. intros c tr c' H. induction H as [c | c1 c2 c3 tr Hs Hx IH | c1 c2 c3 m tr Hs Hx IH]; intros Hc; auto;
        apply IH; destruct c1 as [p H]; cbn in Hc; subst p; rewrite div_unfold in Hs; inversion Hs; subst; cbn;
        first [reflexivity | symmetry; apply div_unfold]. }
    specialize (Hinv _ _ _ Hex eq_refl). destruct Hterm as [H0 r0 _]. cbn in Hinv. rewrite div_unfold in Hinv.
    discriminate.
  Qed.

  (** Writes of instance [i] by a thread other than its writer [tw i]
      never produce a trace, so they are never invoked (invocation is
      prophetic: [tagged_invoke] needs a complete method trace). *)
  Definition M2w (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid) : RelaxedModuleImpl (E_S rc) (F2 si) :=
    fun op t =>
      match op as o return Prog (E_S rc) (far o) with
      | fW i vx vy => if Pos.eqb t (tw i) then M2 rc si (fW i vx vy) t else div
      | fR i => M2 rc si (fR i) t
      end.

  (** P1: only [tw i] writes instance [i]. *)
  Definition P1 {si : FOp -> FOp -> Prop} (tw : nat -> tid) (s : list (ThreadEvent (F2 si))) : Prop :=
    forall t h i vx vy, In (Build_ThreadEvent t (@InvEv (F2 si) h (fW i vx vy))) s -> t = tw i.

  Lemma overlay_events_in {E F : RelaxedSig.t} (evs : list (RelaxedModuleSemantics.ModuleEvent E F)) e :
    In (RelaxedModuleSemantics.OverlayEvent e) evs -> In e (RelaxedGSim.overlay_events evs).
  Proof.
    induction evs as [| ev evs IH]; [intros [] |]. intros [Heq | Hin].
    - subst ev. cbn. left. reflexivity.
    - cbn. apply in_or_app. right. exact (IH Hin).
  Qed.

  Section Guard.
    Import RelaxedModuleSemantics.
    Context (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid).
    Context (V : LTS (E_S rc)).

    Lemma exec_guard (c c' : TaggedModuleConfig V) evs :
      module_execution_tagged V (M2 rc si) c evs c' ->
      (forall t h i vx vy, In (OverlayEvent (Build_ThreadEvent t (@InvEv (F2 si) h (fW i vx vy)))) evs -> t = tw i) ->
      module_execution_tagged V (M2w rc si tw) c evs c'.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros Hg; [constructor |].
      econstructor; [| apply IH; intros t h i vx vy Hin; apply (Hg t h i vx vy); right; exact Hin].
      destruct Hstep as [t h op q pool queue used tr ret Hfc Hm Hft | cand q q' pool queue queue' used Hsel Hlts
                        | t h op ret q pool pool' queue used Hfin Hdone].
      - apply tagged_invoke; [exact Hfc | | exact Hft].
        destruct op as [i vx vy | i]; [| exact Hm].
        assert (Ht : t = tw i) by (apply (Hg t h i vx vy); left; reflexivity). subst t.
        cbn [M2w]. rewrite Pos.eqb_refl. exact Hm.
      - apply tagged_underlay; assumption.
      - apply tagged_return; assumption.
    Qed.

    (** Under P1 every trace of [M2] is a trace of the guarded [M2w]. *)
    Theorem mtraces_guard σ0 s :
      RelaxedHoareCompLin.MTraces V (M2 rc si) σ0 s -> P1 tw s -> RelaxedHoareCompLin.MTraces V (M2w rc si tw) σ0 s.
    Proof.
      intros (evs & c & Hex & Hs) HP. exists evs, c. split; [| exact Hs].
      apply (exec_guard _ _ _ Hex). intros t h i vx vy Hin. apply (HP t h i vx vy). rewrite <- Hs.
      exact (overlay_events_in _ _ Hin).
    Qed.

    (** Conversely, the guarded module has no more traces. *)
    Lemma exec_unguard (c c' : TaggedModuleConfig V) evs :
      module_execution_tagged V (M2w rc si tw) c evs c' ->
      module_execution_tagged V (M2 rc si) c evs c'.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; [constructor |].
      econstructor; [| exact IH].
      destruct Hstep as [t h op q pool queue used tr ret Hfc Hm Hft | cand q q' pool queue queue' used Hsel Hlts
                        | t h op ret q pool pool' queue used Hfin Hdone].
      - apply tagged_invoke; [exact Hfc | | exact Hft].
        destruct op as [i vx vy | i]; [| exact Hm]. cbn [M2w] in Hm.
        destruct (Pos.eqb t (tw i)); [exact Hm | exfalso; exact (div_no_produce t tr ret Hm)].
      - apply tagged_underlay; assumption.
      - apply tagged_return; assumption.
    Qed.

    Theorem mtraces_unguard σ0 s :
      RelaxedHoareCompLin.MTraces V (M2w rc si tw) σ0 s -> RelaxedHoareCompLin.MTraces V (M2 rc si) σ0 s.
    Proof. intros (evs & c & Hex & Hs). exists evs, c. split; [exact (exec_unguard _ _ _ Hex) | exact Hs]. Qed.

    (** Every trace of the guarded module satisfies P1. *)
    Lemma exec_P1 (c c' : TaggedModuleConfig V) evs :
      module_execution_tagged V (M2w rc si tw) c evs c' ->
      forall t h i vx vy, In (OverlayEvent (Build_ThreadEvent t (@InvEv (F2 si) h (fW i vx vy)))) evs -> t = tw i.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros t0 h0 i0 vx0 vy0 Hin; [destruct Hin |].
      destruct Hin as [Heq | Hin]; [| exact (IH t0 h0 i0 vx0 vy0 Hin)]. subst ev.
      inversion Hstep as [t h op q pool queue used tr ret Hfc Hm Hft E1 E2 E3 | | ]; subst.
      cbn [M2w] in Hm. destruct (Pos.eqb_spec t0 (tw i0)) as [-> | Hne]; [reflexivity |].
      exfalso. exact (div_no_produce t0 tr ret Hm).
    Qed.

    Theorem mtraces_guard_P1 σ0 s : RelaxedHoareCompLin.MTraces V (M2w rc si tw) σ0 s -> P1 tw s.
    Proof.
      intros (evs & c & Hex & Hs) t h i vx vy Hin. rewrite <- Hs in Hin.
      apply (exec_P1 _ _ _ Hex t h i vx vy). clear - Hin.
      induction evs as [| ev evs IH]; cbn in Hin; [destruct Hin |].
      destruct ev as [e | e]; cbn in Hin.
      - right. exact (IH Hin).
      - destruct Hin as [<- | Hin]; [left; reflexivity | right; exact (IH Hin)].
    Qed.
  End Guard.

  (** ** Part 4. Blocking facts *)

  (** The operations of a read of instance [j] (as a set: the iteration's
      [rd Sq_j] twice, [rmb] twice, and the two data reads), and those of
      a WRd write of instance [i] having read [v]. *)
  Definition rd_ops (j : nat) : list SOp := [sRd (Sq j); sRmb; sRd (Sx j); sRd (Sy j)].

  Definition wr_ops (i v vx vy : nat) : list SOp :=
    [sRd (Sq i); sWr (Sq i) (v + 1); sWmb; sWr (Sx i) vx; sWr (Sy i) vy; sWr (Sq i) (v + 2)].

  (** An older read's queued [rmb] blocks a younger [rd] (in particular
      the WRd write's [rd Sq_i]): [dto Rmb DR = true]. *)
  Lemma rmb_blocks_rd rc l : ~ sindep rc sRmb (sRd l).
  Proof. unfold sindep. destruct rc; cbn; discriminate. Qed.

  Ltac block_cases rc :=
    destruct rc; cbn;
    split; intros H;
    first [ split; reflexivity
          | exfalso; apply H; reflexivity
          | discriminate H
          | let H' := fresh in intros H'; discriminate H'
          | destruct H as [H1 H2]; first [discriminate H1 | discriminate H2] ].

  (** Older read of instance [j], younger WRd write of instance [i ≠ j]:
      the only ordered pair is ([rmb], [rd Sq_i]).  So a write cannot start
      before every older read's [rmb]s are emitted.  That this excludes
      cross-SeqLock LB for WRd (plan §0, §7 check 3) is argued here; the
      formal negative is [RelaxedHoareSL2Read.lb2_not_trace_rd]. *)
  Lemma lb_blocking rc i j v vx vy c w :
    i <> j -> In c (rd_ops j) -> In w (wr_ops i v vx vy) ->
    (~ sindep rc c w <-> c = sRmb /\ w = sRd (Sq i)).
  Proof.
    intros Hij Hc Hw. assert (Hji : Nat.eqb j i = false) by (apply Nat.eqb_neq; congruence).
    unfold sindep.
    destruct Hc as [<-|[<-|[<-|[<-|[]]]]]; destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]];
      cbn [ogl ocat gl_beq sl_beq]; rewrite ?Hji; block_cases rc.
  Qed.

  (** Older WRd write of instance [i], younger read of instance [j ≠ i]:
      the only ordered pair is ([rd Sq_i], [rmb]).  Once the write's
      [rd Sq_i] is emitted, the whole read may overtake the rest of the
      write (the SB direction, [slRA]). *)
  Lemma sb_blocking rc i j v vx vy w c :
    i <> j -> In w (wr_ops i v vx vy) -> In c (rd_ops j) ->
    (~ sindep rc w c <-> w = sRd (Sq i) /\ c = sRmb).
  Proof.
    intros Hij Hw Hc. assert (Hij' : Nat.eqb i j = false) by (apply Nat.eqb_neq; exact Hij).
    unfold sindep.
    destruct Hw as [<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]; destruct Hc as [<-|[<-|[<-|[<-|[]]]]];
      cbn [ogl ocat gl_beq sl_beq]; rewrite ?Hij'; block_cases rc.
  Qed.

  (** Calls of one instance: a read's [rd Sq_i] and a write's accesses to
      [Sq_i] are pairwise ordered (same location), and so are the data
      accesses at one location (the same-instance rows of the plan's §2.4
      readiness table rely on these). *)
  Lemma same_instance_blocking rc i v w a :
    ~ sindep rc (sRd (Sq i)) (sRd (Sq i)) /\ ~ sindep rc (sRd (Sq i)) (sWr (Sq i) w) /\
    ~ sindep rc (sWr (Sq i) v) (sRd (Sq i)) /\ ~ sindep rc (sWr (Sq i) v) (sWr (Sq i) w) /\
    ~ sindep rc (sRd (Sx i)) (sWr (Sx i) a) /\ ~ sindep rc (sWr (Sx i) a) (sRd (Sx i)) /\
    ~ sindep rc (sRd (Sy i)) (sWr (Sy i) a) /\ ~ sindep rc (sWr (Sy i) a) (sRd (Sy i)).
  Proof. repeat split; apply sindep_same_loc; reflexivity. Qed.

  (** The order inside a read (plan §2.3: [G → rmb_a → {rd x, rd y} →
      rmb_b → T]); the two data reads are not ordered with each other. *)
  Lemma rd_order rc i :
    ~ sindep rc (sRd (Sq i)) sRmb /\ ~ sindep rc sRmb (sRd (Sx i)) /\ ~ sindep rc sRmb (sRd (Sy i)) /\
    ~ sindep rc (sRd (Sx i)) sRmb /\ ~ sindep rc (sRd (Sy i)) sRmb /\ ~ sindep rc sRmb (sRd (Sq i)) /\
    ~ sindep rc sRmb sRmb /\ ~ sindep rc (sRd (Sq i)) (sRd (Sq i)) /\
    sindep rc (sRd (Sx i)) (sRd (Sy i)) /\ sindep rc (sRd (Sy i)) (sRd (Sx i)).
  Proof. unfold sindep. cbn [ogl ocat gl_beq sl_beq]. rewrite Nat.eqb_refl. repeat split; destruct rc; cbn; first [reflexivity | discriminate]. Qed.

  (** The order inside a WRd write ([rd Sq_i → wr Sq_i → wmb_a → {wr x,
      wr y} → wmb_b → wr Sq_i]); the two data writes are not ordered
      with each other, and neither are [rd Sq_i] and [wmb_a] directly. *)
  Lemma wr_order rc i v vx vy :
    ~ sindep rc (sRd (Sq i)) (sWr (Sq i) (v + 1)) /\ ~ sindep rc (sWr (Sq i) (v + 1)) sWmb /\
    ~ sindep rc sWmb (sWr (Sx i) vx) /\ ~ sindep rc sWmb (sWr (Sy i) vy) /\
    ~ sindep rc (sWr (Sx i) vx) sWmb /\ ~ sindep rc (sWr (Sy i) vy) sWmb /\
    ~ sindep rc sWmb (sWr (Sq i) (v + 2)) /\ ~ sindep rc (sWr (Sq i) (v + 1)) (sWr (Sq i) (v + 2)) /\
    ~ sindep rc sWmb sWmb /\
    sindep rc (sWr (Sx i) vx) (sWr (Sy i) vy) /\ sindep rc (sRd (Sq i)) sWmb.
  Proof. unfold sindep. cbn [ogl ocat gl_beq sl_beq]. rewrite Nat.eqb_refl. repeat split; destruct rc; cbn; first [reflexivity | discriminate]. Qed.

  (** *** Lifting to the module frontier *)

  (** Two invocations of one thread may cross iff they are
      semi-independent. *)
  Lemma inv_cross_iff rc (e c : TaggedEvent (E_S rc)) t h h' o o' :
    untag e = Build_ThreadEvent t (@InvEv (E_S rc) h o) ->
    untag c = Build_ThreadEvent t (@InvEv (E_S rc) h' o') ->
    RelaxedModuleSemantics.tagged_can_cross e c <-> sindep rc o o'.
  Proof.
    intros He Hc. unfold RelaxedModuleSemantics.tagged_can_cross, RelaxedModuleSemantics.must_precede.
    rewrite He, Hc. cbn. split.
    - intros [Hne | [_ Hn]]; [contradiction Hne; reflexivity |].
      destruct (sindep_dec rc o o') as [Hs | Hs]; [exact Hs | contradiction].
    - intros Hs. right. split; [reflexivity |]. intros Hn. exact (Hn Hs).
  Qed.

  (** A candidate cannot be selected past a queued event it cannot cross
      (for its first occurrence in the queue). *)
  Lemma select_blocked {E F : RelaxedSig.t} (cand e : RelaxedModuleSemantics.TaggedScheduledEvent E F)
      (queue queue' : RelaxedModuleSemantics.TaggedQueue E F) pre post :
    queue = pre ++ cand :: post -> ~ In cand pre -> In e pre ->
    ~ RelaxedModuleSemantics.tagged_can_cross (RelaxedModuleSemantics.ts_event e) (RelaxedModuleSemantics.ts_event cand) ->
    ~ RelaxedModuleSemantics.select_frontier_tagged cand queue queue'.
  Proof.
    intros Hq Hnin Hin Hnc Hsel. revert pre Hq Hnin Hin.
    induction Hsel as [suffix | earlier queue queue' Hcross Hsel IH]; intros pre Hq Hnin Hin.
    - destruct pre as [| x pre]; [destruct Hin |]. injection Hq as -> _. apply Hnin. left. reflexivity.
    - destruct pre as [| x pre]; [destruct Hin |]. injection Hq as -> Hq.
      destruct Hin as [-> | Hin]; [exact (Hnc Hcross) |].
      apply (IH pre Hq); [intros H; apply Hnin; right; exact H | exact Hin].
  Qed.

  (** [rmb_blocks_rd] at the module level: a [rd] invocation cannot be
      emitted past a queued [rmb] invocation of the same thread. *)
  Lemma rmb_blocks_select rc {F : RelaxedSig.t} (cand e : RelaxedModuleSemantics.TaggedScheduledEvent (E_S rc) F)
      queue queue' pre post t h h' l :
    untag (RelaxedModuleSemantics.ts_event e) = Build_ThreadEvent t (@InvEv (E_S rc) h sRmb) ->
    untag (RelaxedModuleSemantics.ts_event cand) = Build_ThreadEvent t (@InvEv (E_S rc) h' (sRd l)) ->
    queue = pre ++ cand :: post -> ~ In cand pre -> In e pre ->
    ~ RelaxedModuleSemantics.select_frontier_tagged cand queue queue'.
  Proof.
    intros He Hc Hq Hnin Hin. apply (select_blocked cand e queue queue' pre post Hq Hnin Hin).
    rewrite (inv_cross_iff rc _ _ t h h' sRmb (sRd l) He Hc). apply rmb_blocks_rd.
  Qed.

  (** ** Part 5. Tactics for method and module executions (ports of
      RelaxedHoareLatchProg Part 10) *)

  (** [ex_step hh v] issues the next call of a [run] on handle [hh] and
      receives [v]; handle freshness by [lia], so that [hh] may be [h + k]
      for a variable [h].  [ex_done] ends at [SDone]. *)
  Ltac ex_wait v :=
    match goal with
    | |- program_execution_tagged ?t (Build_ProgramConfig (@Wait ?E ?R _ (@MkFutureRef _ ?o ?h) ?k) ?H) _ _ =>
        eapply tagged_execution_emit;
        [ eapply (@tagged_wait_pending E R t o h v k H); apply resolve_here | cbn beta ]
    end.

  (** [rok] is kept folded by [ex_step], so that a symbolic validation
      [rok s s'] can be rewritten; [rok_simpl] evaluates closed instances. *)
  Ltac rok_simpl :=
    repeat match goal with
           | |- context [rok ?a ?b] =>
               let x := eval cbv in (rok a b) in
               match x with
               | true => change (rok a b) with true
               | false => change (rok a b) with false
               end
           end.

  Ltac ex_step hh v :=
    rewrite run_unfold; rok_simpl; cbn -[run rok];
    eapply tagged_execution_emit;
    [ apply tagged_futureD with (h := hh); unfold handle_fresh; cbn; lia
    | cbn beta ];
    ex_wait v.

  Ltac ex_done := rewrite run_unfold; cbn -[run]; apply tagged_execution_refl.

  (** Tag bounds of a produced trace: reads untagged, writes tagged within
      their first handle. *)
  Ltac deps_none :=
    repeat constructor; intros q Hq; cbn in Hq;
    first [ solve [destruct Hq as [(ix & Hi & _) _]; destruct Hi]
          | destruct Hq ].

  Ltac deps_within :=
    repeat constructor; intros q Hq; cbn in Hq;
    first [ solve [destruct Hq as [(ix & Hi & Hn) _]; destruct Hi as [<- | []]; cbn in Hn; injection Hn as <-; reflexivity]
          | solve [destruct Hq as [(ix & Hi & _) _]; destruct Hi]
          | destruct Hq ].

  (** Module executions.  [m_here] emits the head of the queue; [m_next]
      crosses one earlier queue event, whose crossing [cross_ok] proves:
      a different thread, or for the same thread none of (F1)-(F3)
      ([must_precede]).  Hypotheses [untag m = ...] compute abstract
      tagged events ([untag_rw]); tag facts come from hypotheses
      [forall q, ~ tev_deps m q] or [forall q, tev_deps m q -> q = h]. *)
  Ltac untag_rw := repeat match goal with H : untag ?m = _ |- context [untag ?m] => rewrite H end.

  Ltac untag_rw_in Hx :=
    repeat match goal with H : untag ?m = _ |- _ => match type of Hx with context [untag m] => rewrite H in Hx end end.

  (** Split a hypothesis [Forall P (x :: l)] into one hypothesis per
      element (beta-reduced, so that [cross_ok] finds tag facts). *)
  Ltac unpack_forall Hx :=
    repeat match type of Hx with
           | Forall _ (_ :: _) => let D := fresh "D" in apply Forall_cons_iff in Hx as [D Hx]; cbv beta in D
           end.

  Ltac not_dep :=
    let i := fresh "i" in
    let Hi := fresh "Hi" in
    let Hn := fresh "Hn" in
    intros [(i & Hi & Hn) _]; cbn in Hi;
    repeat (destruct Hi as [<- | Hi]; [cbn in Hn; try discriminate Hn; try (injection Hn as Hn; discriminate Hn) |]);
    try exact Hi.

  Ltac sindep_ok :=
    let Hn := fresh "Hn" in
    intros Hn; apply Hn; unfold sindep; cbn;
    solve [reflexivity | match goal with r : bool |- _ => destruct r; reflexivity end].

  Ltac cross_ok :=
    first
      [ left; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn; first [discriminate | assumption | congruence]
      | right; split; [cbn [RelaxedModuleSemantics.ts_event]; untag_rw; reflexivity |];
        unfold RelaxedModuleSemantics.must_precede; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn;
        first
          [ solve [discriminate]
          | solve [let H := fresh in intros H; exact H]
          | solve [sindep_ok]
          | solve [match goal with Hd : forall q, ~ tev_deps ?m q |- ~ tev_deps ?m _ => apply Hd end]
          | solve [match goal with Hd : forall q, tev_deps ?m q -> q = _ |- ~ tev_deps ?m _ =>
                     let H := fresh in intros H; apply Hd in H; discriminate H end]
          | solve [not_dep] ] ].

  Ltac m_next := apply RelaxedModuleSemantics.tagged_select_next; [cross_ok |].
  Ltac m_here := apply RelaxedModuleSemantics.tagged_select_here.

  (** [ei_inv] solves an [EI δS] invocation step (unit-valued operations
      first, then reads); [ei_res pre] a response step whose record is
      after the records [pre]. *)
  Ltac ei_inv :=
    cbn; untag_rw; cbn;
    first [ exists tt; eexists; split; reflexivity
          | eexists _, _; split; [split; reflexivity | reflexivity] ].
  Ltac ei_res pre := cbn; untag_rw; cbn; exists pre; eexists; split; reflexivity.

  Ltac m_step k m sel lts :=
    eapply RelaxedModuleSemantics.tagged_module_execution_cons;
    [ apply RelaxedModuleSemantics.tagged_underlay with
        (candidate := @RelaxedModuleSemantics.Build_TaggedScheduledEvent _ _ k m);
      [ cbn; sel | lts ]
    | ].

  (** [m_finish] finds the call's entry in the pool (the key of the
      returning call is fixed by [finish_here] before the inequalities of
      the skipped entries are discharged). *)
  Ltac m_finish :=
    first [ apply RelaxedModuleSemantics.finish_here
          | eapply RelaxedModuleSemantics.finish_next; [ | m_finish ]; discriminate ].

  Ltac m_return o :=
    eapply RelaxedModuleSemantics.tagged_module_execution_cons;
    [ eapply RelaxedModuleSemantics.tagged_return with (op := o);
      [ m_finish
      | cbn; intros Hin; repeat (destruct Hin as [Hin | Hin]; [discriminate Hin |]); exact Hin ]
    | ].

  (** ** Part 6. Method executions *)

  (** The untagged events of one reader iteration on handles [h .. h+5]
      that reads [s], [a], [c], [s']. *)
  Definition rd_iter_evs (rc : bool) (t : tid) (i h s a c s' : nat) : list (ThreadEvent (E_S rc)) :=
    [Build_ThreadEvent t (@InvEv (E_S rc) h (sRd (Sq i))); Build_ThreadEvent t (@ResEv (E_S rc) h (sRd (Sq i)) s);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 1) sRmb); Build_ThreadEvent t (@ResEv (E_S rc) (h + 1) sRmb tt);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 2) (sRd (Sx i))); Build_ThreadEvent t (@ResEv (E_S rc) (h + 2) (sRd (Sx i)) a);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 3) (sRd (Sy i))); Build_ThreadEvent t (@ResEv (E_S rc) (h + 3) (sRd (Sy i)) c);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 4) sRmb); Build_ThreadEvent t (@ResEv (E_S rc) (h + 4) sRmb tt);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 5) (sRd (Sq i))); Build_ThreadEvent t (@ResEv (E_S rc) (h + 5) (sRd (Sq i)) s')].

  (** The untagged events of a WRd write on handles [h .. h+6] that reads
      [v] from [Sq i]. *)
  Definition wr_evs (rc : bool) (t : tid) (i h v vx vy : nat) : list (ThreadEvent (E_S rc)) :=
    [Build_ThreadEvent t (@InvEv (E_S rc) h (sRd (Sq i))); Build_ThreadEvent t (@ResEv (E_S rc) h (sRd (Sq i)) v);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 1) (sWr (Sq i) (v + 1)));
     Build_ThreadEvent t (@ResEv (E_S rc) (h + 1) (sWr (Sq i) (v + 1)) tt);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 2) sWmb); Build_ThreadEvent t (@ResEv (E_S rc) (h + 2) sWmb tt);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 3) (sWr (Sx i) vx)); Build_ThreadEvent t (@ResEv (E_S rc) (h + 3) (sWr (Sx i) vx) tt);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 4) (sWr (Sy i) vy)); Build_ThreadEvent t (@ResEv (E_S rc) (h + 4) (sWr (Sy i) vy) tt);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 5) sWmb); Build_ThreadEvent t (@ResEv (E_S rc) (h + 5) sWmb tt);
     Build_ThreadEvent t (@InvEv (E_S rc) (h + 6) (sWr (Sq i) (v + 2)));
     Build_ThreadEvent t (@ResEv (E_S rc) (h + 6) (sWr (Sq i) (v + 2)) tt)].

  (** A read that validates at its first iteration ([s] even, read twice):
      its trace, for every handle base [h] and every values read. *)
  Lemma rd_prod rc si t i h s a c :
    Nat.even s = true ->
    exists tr, program_produces_tagged t (M2 rc si (fR i) t) tr (a, c) /\
      map untag tr = rd_iter_evs rc t i h s a c s /\ Forall (fun m : TaggedEvent (E_S rc) => forall q, ~ tev_deps m q) tr.
  Proof.
    intros Hs. eexists. split; [eexists; split |].
    - unfold initial_program. cbn [M2].
      ex_step h s. ex_step (h + 1) tt. ex_step (h + 2) a. ex_step (h + 3) c. ex_step (h + 4) tt. ex_step (h + 5) s.
      rewrite (rok_true s Hs). ex_done.
    - constructor. repeat constructor.
    - split; [reflexivity | deps_none].
  Qed.

  (** A read whose first iteration fails validation and whose second
      validates (24 events, handles [h .. h+11]). *)
  Lemma rd_retry_prod_gen rc si t i h s1 a1 c1 s1' s a c :
    rok s1 s1' = false -> Nat.even s = true ->
    exists tr, program_produces_tagged t (M2 rc si (fR i) t) tr (a, c) /\
      map untag tr = rd_iter_evs rc t i h s1 a1 c1 s1' ++ rd_iter_evs rc t i (h + 6) s a c s /\
      Forall (fun m : TaggedEvent (E_S rc) => forall q, ~ tev_deps m q) tr.
  Proof.
    intros Hf Hs. eexists. split; [eexists; split |].
    - unfold initial_program. cbn [M2].
      ex_step h s1. ex_step (h + 1) tt. ex_step (h + 2) a1. ex_step (h + 3) c1. ex_step (h + 4) tt. ex_step (h + 5) s1'.
      rewrite Hf.
      ex_step (h + 6) s. ex_step (h + 6 + 1) tt. ex_step (h + 6 + 2) a. ex_step (h + 6 + 3) c. ex_step (h + 6 + 4) tt.
      ex_step (h + 6 + 5) s.
      rewrite (rok_true s Hs). ex_done.
    - constructor. repeat constructor.
    - split; [reflexivity | deps_none].
  Qed.

  (** The plan's retry witness: a read of instance 2 that first sees an
      odd sequence number (1) and a torn pair (0, 1), retries, and returns
      (1, 1) (24 events). *)
  Lemma rd_retry_prod rc si tw t :
    exists tr, program_produces_tagged t (M2w rc si tw (fR 2) t) tr (1, 1) /\ length tr = 24 /\
      map untag tr = rd_iter_evs rc t 2 0 1 0 1 2 ++ rd_iter_evs rc t 2 6 2 1 1 2.
  Proof.
    destruct (rd_retry_prod_gen rc si t 2 0 1 0 1 2 2 1 1 eq_refl eq_refl) as (tr & Hp & Hm & _).
    exists tr. split; [exact Hp |]. split; [| exact Hm].
    rewrite <- (length_map untag tr), Hm. reflexivity.
  Qed.

  (** A WRd write, for every handle base [h] and every value [v] read
      from [Sq i]; its tags are within its first handle. *)
  Lemma wr_prod rc si t i h v vx vy :
    exists tr, program_produces_tagged t (M2 rc si (fW i vx vy) t) tr tt /\
      map untag tr = wr_evs rc t i h v vx vy /\ Forall (fun m : TaggedEvent (E_S rc) => forall q, tev_deps m q -> q = h) tr.
  Proof.
    eexists. split; [eexists; split |].
    - unfold initial_program. cbn [M2].
      ex_step h v. ex_step (h + 1) tt. ex_step (h + 2) tt. ex_step (h + 3) tt. ex_step (h + 4) tt. ex_step (h + 5) tt.
      ex_step (h + 6) tt. ex_done.
    - constructor. repeat constructor.
    - split; [reflexivity | deps_within].
  Qed.

  (** The guarded write by its writer thread. *)
  Lemma wr_guard_prod rc si tw t i h v vx vy :
    tw i = t ->
    exists tr, program_produces_tagged t (M2w rc si tw (fW i vx vy) t) tr tt /\
      map untag tr = wr_evs rc t i h v vx vy /\ Forall (fun m : TaggedEvent (E_S rc) => forall q, tev_deps m q -> q = h) tr.
  Proof.
    intros Ht. destruct (wr_prod rc si t i h v vx vy) as (tr & Hp & Hm & Hd).
    exists tr. split; [| split; assumption].
    cbn [M2w]. rewrite Ht, Pos.eqb_refl. exact Hp.
  Qed.

  (** The guarded write by any other thread produces nothing. *)
  Lemma wr_guard_none rc si tw t i vx vy tr r :
    t <> tw i -> ~ program_produces_tagged t (M2w rc si tw (fW i vx vy) t) tr r.
  Proof.
    intros Hne. cbn [M2w]. destruct (Pos.eqb_spec t (tw i)) as [E | _]; [contradiction | apply div_no_produce].
  Qed.

  (** ** Part 7. Non-vacuity: module executions over [EI δS] *)

  Definition sk (si : FOp -> FOp -> Prop) (t : tid) (h : nat) : CallKey (F2 si) := (t, h).

  (** One write of [(1, 1)] into instance 1 by its writer [t1], then one
      read of instance 1 by a thread [t2] (any thread, in particular
      another one), returning [(1, 1)]: each call's events in program
      order, over the sequential register file from [regs0]. *)
  Theorem sl2_write_read_mtraces rc si tw t1 t2 :
    tw 1 = t1 ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
      [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW 1 1 1) tt);
       Build_ThreadEvent t2 (@InvEv (F2 si) 1 (fR 1)); Build_ThreadEvent t2 (@ResEv (F2 si) 1 (fR 1) (1, 1))].
  Proof.
    intros Ht.
    destruct (wr_guard_prod rc si tw t1 1 0 0 1 1 Ht) as (tw' & Hpw & Hmw & _).
    destruct (rd_prod rc si t2 1 10 2 1 1 eq_refl) as (tr & Hpr & Hmr & _).
    destruct tw' as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 tw']]]]]]]]]]]]]]];
      try discriminate Hmw.
    pose proof Hmw as Hmw'. injection Hmw' as V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13.
    destruct tr as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 [|r9 [|r10 [|r11 [|r12 tr]]]]]]]]]]]]];
      try discriminate Hmr.
    pose proof Hmr as Hmr'. injection Hmr' as R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11.
    do 2 eexists. split.
    - eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (h := 0); [intros [] | exact Hpw |].
        rewrite Hmw. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      m_step (sk si t1 0) w0 m_here ei_inv. m_step (sk si t1 0) w1 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t1 0) w2 m_here ei_inv. m_step (sk si t1 0) w3 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t1 0) w4 m_here ei_inv. m_step (sk si t1 0) w5 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t1 0) w6 m_here ei_inv. m_step (sk si t1 0) w7 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t1 0) w8 m_here ei_inv. m_step (sk si t1 0) w9 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t1 0) w10 m_here ei_inv. m_step (sk si t1 0) w11 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t1 0) w12 m_here ei_inv. m_step (sk si t1 0) w13 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_return (fW 1 1 1).
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t2) (h := 1); [cbn; intros [H | []]; discriminate H | exact Hpr |].
        rewrite Hmr. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. untag_rw_in Hu. cbn in Hk, Hu.
        repeat (destruct Hk as [<- | Hk]; [repeat (destruct Hu as [Hu | Hu]; [discriminate Hu |]); exact Hu |]); exact Hk. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      m_step (sk si t2 1) r0 m_here ei_inv. m_step (sk si t2 1) r1 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t2 1) r2 m_here ei_inv. m_step (sk si t2 1) r3 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t2 1) r4 m_here ei_inv. m_step (sk si t2 1) r5 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t2 1) r6 m_here ei_inv. m_step (sk si t2 1) r7 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t2 1) r8 m_here ei_inv. m_step (sk si t2 1) r9 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t2 1) r10 m_here ei_inv. m_step (sk si t2 1) r11 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_return (fR 1).
      apply RelaxedModuleSemantics.tagged_module_execution_refl.
    - reflexivity.
  Qed.

  (** Every invocation of a concrete four-event trace has a response. *)
  Ltac complete_tac :=
    let i := fresh "i" in let kt := fresh "kt" in let kh := fresh "kh" in let op := fresh "op" in
    let x := fresh "x" in let Hn := fresh "Hn" in let Hs := fresh "Hs" in
    intros i [kt kh] op (x & Hn & Hs);
    do 4 (destruct i as [| i];
            [ cbn in Hn; injection Hn as <-; unfold PrefixView.sel in Hs;
              first [ discriminate Hs
                    | injection Hs as <- <- <-;
                      first [ solve [exists 0; eexists; eexists; split; reflexivity]
                            | solve [exists 1; eexists; eexists; split; reflexivity]
                            | solve [exists 2; eexists; eexists; split; reflexivity]
                            | solve [exists 3; eexists; eexists; split; reflexivity] ] ]
            | ]);
    destruct i; cbn in Hn; discriminate Hn.

  Lemma sl2_write_read_complete si t1 t2 :
    PrefixView.complete
      [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW 1 1 1) tt);
       Build_ThreadEvent t2 (@InvEv (F2 si) 1 (fR 1)); Build_ThreadEvent t2 (@ResEv (F2 si) 1 (fR 1) (1, 1))].
  Proof. complete_tac. Qed.

  (** One thread [t = tw 1] invokes a write of instance 1 and then a read
      of instance 2.  After the write's [rd Sq_1], each of the read's
      twelve events crosses the write's twelve pending events
      ([sb_blocking]: no other pair is ordered), the read returns [(0, 0)]
      while the older write is still pending, and then the write
      completes.  This is a (W, R) reordering across instances, of the
      kind that an [slRA] pair relaxes, produced by the module itself.
      The trace is single-threaded and its overlay trace is already
      relaxed-linearizable at ∅ (witness W; R:
      [RelaxedHoareSL2Exec.ov_rel_lin_empty], and under every relation,
      [RelaxedHoareSL2Exec.ov_rel_lin]; stated there because this file
      precedes the trace-level kit), so it shows that the module
      reorders, not that [slRA] is needed (for that, see
      [RelaxedHoareSL2Exec]: SB and the single-writer trace). *)
  Theorem sl2_read_overtakes_write rc si tw t :
    tw 1 = t ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
      [Build_ThreadEvent t (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t (@InvEv (F2 si) 1 (fR 2));
       Build_ThreadEvent t (@ResEv (F2 si) 1 (fR 2) (0, 0)); Build_ThreadEvent t (@ResEv (F2 si) 0 (fW 1 1 1) tt)].
  Proof.
    intros Ht.
    destruct (wr_guard_prod rc si tw t 1 0 0 1 1 Ht) as (tw' & Hpw & Hmw & _).
    destruct (rd_prod rc si t 2 10 0 0 0 eq_refl) as (tr & Hpr & Hmr & Hdr).
    destruct tw' as [|w0 [|w1 [|w2 [|w3 [|w4 [|w5 [|w6 [|w7 [|w8 [|w9 [|w10 [|w11 [|w12 [|w13 [|w14 tw']]]]]]]]]]]]]]];
      try discriminate Hmw.
    pose proof Hmw as Hmw'. injection Hmw' as V0 V1 V2 V3 V4 V5 V6 V7 V8 V9 V10 V11 V12 V13.
    destruct tr as [|r0 [|r1 [|r2 [|r3 [|r4 [|r5 [|r6 [|r7 [|r8 [|r9 [|r10 [|r11 [|r12 tr]]]]]]]]]]]]];
      try discriminate Hmr.
    pose proof Hmr as Hmr'. injection Hmr' as R0 R1 R2 R3 R4 R5 R6 R7 R8 R9 R10 R11.
    unpack_forall Hdr.
    do 2 eexists. split.
    - eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (h := 0); [intros [] | exact Hpw |].
        rewrite Hmw. split; [cbn; repeat constructor; cbn; intuition discriminate | intros key _ []]. }
      eapply RelaxedModuleSemantics.tagged_module_execution_cons.
      { eapply RelaxedModuleSemantics.tagged_invoke with (t := t) (h := 1); [cbn; intros [H | []]; discriminate H | exact Hpr |].
        rewrite Hmr. split; [cbn; repeat constructor; cbn; intuition discriminate |].
        intros key Hk Hu. cbn [map app] in Hu. untag_rw_in Hu. cbn in Hk, Hu.
        repeat (destruct Hk as [<- | Hk]; [repeat (destruct Hu as [Hu | Hu]; [discriminate Hu |]); exact Hu |]); exact Hk. }
      cbn [app RelaxedModuleSemantics.schedule_trace_tagged map].
      m_step (sk si t 0) w0 m_here ei_inv. m_step (sk si t 0) w1 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 1) r0 ltac:(do 12 m_next; m_here) ei_inv.
      m_step (sk si t 1) r1 ltac:(do 12 m_next; m_here) ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 1) r2 ltac:(do 12 m_next; m_here) ei_inv.
      m_step (sk si t 1) r3 ltac:(do 12 m_next; m_here) ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 1) r4 ltac:(do 12 m_next; m_here) ei_inv.
      m_step (sk si t 1) r5 ltac:(do 12 m_next; m_here) ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 1) r6 ltac:(do 12 m_next; m_here) ei_inv.
      m_step (sk si t 1) r7 ltac:(do 12 m_next; m_here) ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 1) r8 ltac:(do 12 m_next; m_here) ei_inv.
      m_step (sk si t 1) r9 ltac:(do 12 m_next; m_here) ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 1) r10 ltac:(do 12 m_next; m_here) ei_inv.
      m_step (sk si t 1) r11 ltac:(do 12 m_next; m_here) ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_return (fR 2).
      m_step (sk si t 0) w2 m_here ei_inv. m_step (sk si t 0) w3 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 0) w4 m_here ei_inv. m_step (sk si t 0) w5 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 0) w6 m_here ei_inv. m_step (sk si t 0) w7 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 0) w8 m_here ei_inv. m_step (sk si t 0) w9 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 0) w10 m_here ei_inv. m_step (sk si t 0) w11 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_step (sk si t 0) w12 m_here ei_inv. m_step (sk si t 0) w13 m_here ltac:(ei_res (@nil (RelaxedTraceLin.Op (E_S rc)))).
      m_return (fW 1 1 1).
      apply RelaxedModuleSemantics.tagged_module_execution_refl.
    - reflexivity.
  Qed.

  Lemma sl2_read_overtakes_write_complete si t :
    PrefixView.complete
      [Build_ThreadEvent t (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t (@InvEv (F2 si) 1 (fR 2));
       Build_ThreadEvent t (@ResEv (F2 si) 1 (fR 2) (0, 0)); Build_ThreadEvent t (@ResEv (F2 si) 0 (fW 1 1 1) tt)].
  Proof. complete_tac. Qed.

  (** ** Part 8. Targets of tasks .4-.7 (NOT proved in this file)

      Statement shapes only, typechecked so that the definitions above fit
      [RLHL2Hyps] (over the handle-linear underlay [EIhl δS] and the
      effect-at-invocation overlay [EI δF]) and [rel_lin]; neither is
      claimed by this file.

      Status (RLHL-seqlock .7):
      - The question of the Addendum, whether the RLHL theorem holds for
        every [si ⊇ slRA] or needs an upper bound such as [si ⊆ slsi],
        is answered: [si ⊇ slRA] suffices and no upper bound is needed
        ([RelaxedHoareSL2Inv]: [slRA] is used only by [ready_read], and
        the side fields hold for every [si]).
      - [sl2rd_target] (over [EIhl]) is superseded and not citable.  Over
        [EIhl] the read premise is believed unsatisfiable
        ([RelaxedHoareSL2Inv], OPEN, argued), and the main theorem is over
        the history presentation [EIhlv] (author decision option B).  The
        citable statements are [RelaxedHoareSL2InvLog.sl2rd_prov_target_v]
        (derivations and [RLHL2Hyps] over [EIhlv]) and
        [RelaxedHoareSL2InvLog.sl2rd_complin_target] ([RCompLin] over the
        plain [EI δS], every trace), proved as
        [RelaxedHoareSL2Read.sl2_main] and [RelaxedHoareSL2Read.sl2_complin].
        [sl2rd_prov_target_v] does not imply [sl2rd_target].
      - [sl2rd_relin_target] (complete traces) is proved as
        [RelaxedHoareSL2Read.sl2_rel_lin]. *)
  Definition sl2rd_target : Prop :=
    forall rc si tw, (forall o o', slRA o o' -> si o o') ->
      exists I R G, RelaxedHoareBase.RLHL2Hyps
        (VE := RelaxedHoareCompLinSpec.EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
        I R G (M2w rc si tw) ((regs0, []), []) (A0, []).

  Definition sl2rd_relin_target : Prop :=
    forall rc si tw s, (forall o o', slRA o o' -> si o o') ->
      RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) s ->
      PrefixView.complete s ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) s si (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).

End RelaxedHoareSL2Prog.
