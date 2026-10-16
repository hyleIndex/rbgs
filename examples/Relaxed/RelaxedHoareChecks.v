(** * Sanity checks for the RLHL judgement of [models/simlin/RelaxedHoare*.v]
      (task RLHL-1, iterations 2 and 3; the end-to-end counter of RLHL-2).

    Underlay: the three-location relaxed memory signature [RlxSig] of
    [DependencyFrontierExamples] (well-formed, [RlxSig_wf]: two accesses
    are semi-independent iff they touch different locations), with the LTS
    [MemLTS] (writes take effect at their response).  [MemLTS] is *not*
    per-location coherent under the tagged scheduler (latest-review m-14,
    see its comment and [own_reorder_not_one]); the checks over it test
    the logic, they are not weak-memory evidence.  The counters use their
    own FAA underlays ([Counter.CVE]; [CounterHL.HVE], [CounterHL.OVE]).

    Every overlay signature is well-formed (latest-review M-13):
    [OSig], [PairSig], [XYSig], [OneSig], [TSig], [AwSig] (lemmas [*_wf]);
    no operation is semi-independent of itself, so two overlapping
    same-thread calls of one operation must linearize in invocation order
    ([invocation_ready]).  The order is discharged in two ways:
    - by the ghost thread frontier, when the abstract invocation step is
      effectful ([Counter], [CounterHL]: the invariant couples the
      [ls_inv] calls of each thread with the pending invocations of the
      ghost, and the emission of an FAA may assume it is on the thread
      frontier).  Two [Inc]s of one thread do not commute (they return
      different values).  This is the specification style the author
      chose for RLHL-2 (effect at the abstract invocation, latest-review
      M-17); [CounterHL] builds its specification with
      [RelaxedHoareSpec.EI], so [HVF] holds for it ([counter_spec_hvf]).
      It applies to invocation-ordered underlays such as [HVE] and the
      handle-linear [RelaxedHoareCompLinSpec.EIhl uδ] ([CounterEIhl]);
      it is the overlay of the decided copy-cat route (author decision
      M-20, [RelaxedHoareCompLin]).  The stamp-based pair [VE :=
      ViewLHL.VT nuE], [VF := ViewLHL.VT nuF] of latest-review M-18 is a
      complete-trace corollary only (no instance), and [EI] is not
      expected to have an instance over [ViewLHL.VT] for ordered
      same-thread operations ([CounterRelLin.vt_junk],
      [CounterRelLin.counter_vt_no_rlhl2]);
    - by helping, when the abstract invocation step is a no-op
      ([linearize_response]: a call first moves every pending abstract
      invocation to [ls_lini], oldest first, then takes its own response
      step; the relies [keeps] allow exactly this).  Used by (a), (b),
      (c), M-11 and M-14.  Helping orders the no-op abstract invocations,
      not the effects, so the specification LTS itself may produce traces
      that are not relaxed-linearizable, and [HVF] of
      [RelaxedGSim.gsim_rel_lin] can fail.  It fails for [TLTS], whose
      same-thread pairs do not commute ([tas_not_hvf]), and also for
      [PairLTS], whose same-thread pairs (two reads) do commute
      ([pair_not_hvf]: same-thread order by invocation combined with real
      time through another thread's write); the same trace shape applies
      to [LogRead.LLTS].  So [tas_sound], [pair_rlhl2] and
      [LogRead.log_rlhl2] are checks of the logic over specifications that
      fail [HVF] under their natural sequential specification; [XYLTS],
      [LeLTS] and [AwLTS] are not claimed either way.

    Contents:
    - B-5 ([Counter], acceptance of the ghost redesign):
      [Counter.counter_methodsem_unsat] (the iteration-1 triple
      [RelaxedHoareBase.Iter1.MethodSem] has no model; regression),
      [counter_b5_excluded] (the counterexample's schedule has no ghost
      transition), [counter_provable] / [counter_methodsem] (the redesigned
      triple, by the rules), [counter_init], [counter_b5].
    - M-16 ([CounterHL], author decision "handle-linear VE"):
      [counter_ow_unsat] (over the overwriting underlay [OVE], keyed by
      (thread, handle), [RLHL2Hyps] has no model, for any [I], [R], [G];
      the reviewers' counterexample, regression; the same holds over
      [EI uδ], [CounterEI.counter_ei_unsat] below), [counter_hl_rlhl2]
      (over the handle-linear [HVE], every field of [RLHL2Hyps] holds for
      an invariant that reads the ghost and a guarantee that constrains
      memory), [HVE_handle_linear], [OVE_not_handle_linear],
      [counter_hl_contrast], [counter_spec_hvf].
    - M-16 (iii) ([TwoCallsGen], [IncTwo]): a generic two-call prototype
      of RLHL-2 for every [RLHL2Hyps] instance ([gtwo_init], [gtwo_step],
      [gtwo_execution]); its instance for two overlapping [Inc]s of one
      thread ([inc_two_init], [inc_two_step], [inc_two_execution]); and
      [inc_two_blocked]: (F2) across the two calls, in the module and in
      the ghost ([inv_blocks]).  [call_trace]: the traces of [call op].
      The general case (any number of calls) is
      [RelaxedHoareGSim.rlhl_gsim] (RLHL-2).
    - RLHL-2 acceptance ([CounterRelLin]): [counter_rel_lin] (every
      complete execution of the counter over [HVE] is relaxed-linearizable
      to [seq_legal cδ 0]; [RelaxedHoareGSim.rlhl_rel_lin] with
      [counter_hl_rlhl2] and [counter_spec_hvf]).  Scope (latest-review
      M-19): the I=∅ fragment (no pair of operations is
      semi-independent, at either level); underlay atomic at invocation
      ([HVE], not [complete_pres]); a single-future body.
      [counter_rel_lin_by_rules] (the same, through the paper-facing
      [RelaxedHoareGSim.rlhl_sound] from the derivation
      [counter_hl_provable]); [inc_ooo_exec] and [inc_ooo_rel_lin] (a
      complete execution, derived from module steps, in which two
      overlapping [Inc]s of one thread return out of order);
      [inc_bad_not_rel_lin], [inc_bad_no_exec] (an execution-level check
      (m-23): no complete execution over [HVE] produces the wrong-result
      trace; by a direct argument, not mechanized, this already follows
      from (F2) and the atomic [HVE], so it does not test the logic);
      [bad_counter_no_rlhl2] (m-24, a universal
      negative: for a wrong counter [Mbad], no [I], [R], [G] satisfy
      [RLHL2Hyps] over [HVE] with [CVFe], by
      [RelaxedHoareGSim.rlhl_rel_lin_ei] on the module-derived execution
      [bad_exec]); [hve_not_complete] (M-18 regression: [HVE] is not a
      complete presentation, so [rlhl_rel_lin_pres] does not apply to
      this instance); [vt_junk], [vt_junk_not_rl_prefix] (M-18
      regression: [ViewLHL.VT] accepts a one-thread FAA path in which the
      younger call responds [0] while the older is pending, and the path
      is not an [rl_prefix]; why [EI] over [VT] has no [GSimRel] for
      ordered same-thread operations); [vt_not_implements] ([VT unu]
      does not satisfy [ViewLHL.implements unu]); [counter_vt_no_rlhl2]
      (M-18: for the counter over [VE := VT unu] with [VF := CVFe], no
      [I], [R], [G] satisfy [RLHL2Hyps], from every initial stamp map).
    - RLHL-3a ([CounterCompLin], author decision M-20): [counter_complin]
      (every overlay trace of the counter over [HVE], complete or not, is
      an overlay trace of the relaxed copy-cat
      [RelaxedHoareCompLin.idF] over [CVFe];
      [RelaxedHoareCompLin.rlhl_complin_ei] with [counter_hl_rlhl2]);
      [ooo_copycat_trace] (the out-of-order trace of [inc_ooo_exec] is a
      copy-cat trace); [junkF_not_rtrace] (the incomplete overlay trace
      [Inv(t0,1) Inv(t0,2) Res(t0,2,0)] is not a copy-cat trace over
      [CVFe]: (F2) emits the older call's increment first; closed) and
      [junkF_not_counter_trace] (hence no counter execution over [HVE]
      produces it).  Same scope as [CounterRelLin] (I=∅, [HVE]).
    - RLHL-3a iteration 2 (latest-review m-20, M-20 (b)):
      [CounterEI.EVE_not_handle_linear] and [CounterEI.counter_ei_unsat]
      (review T1: [EI uδ] is not handle-linear, and over it no [I], [R],
      [G] satisfy [RLHL2Hyps] for the overlapping counter; why the
      layering interface is [RelaxedHoareCompLinSpec.EIhl]; closed);
      [WRCopyCat.si_overtake_rtrace] (review T2: with [semi_independent
      := o1 <> o2], a younger read of a thread returns the initial value
      while the thread's older write is pending, in a copy-cat execution
      over [EI rdelta]; closed) and [WRCopyCat.si_overtake_not_rtrace0]
      (its mirror: under the empty relation no copy-cat execution has
      that trace; [classic], through
      [RelaxedHoareCompLinSpec.cc_gsim]).  Copy-cat-level witnesses, not
      module-derived (latest-review M-19).
      [CounterEIhl.counter_eihl_rlhl2] (the decided layering interface
      has an instance: every field of [RLHL2Hyps] holds for the
      overlapping counter over [VE := RelaxedHoareCompLinSpec.EIhl uδ];
      closed), [counter_complin_eihl], [counter_complin_ei] (copy-cat
      inclusion over [EIhl uδ] and over the plain [EI uδ]; [classic]),
      [counter_eihl_rel_lin] (complete traces over [EI uδ] are
      relaxed-linearizable), [inc_ooo_exec_ei], [ooo_trace_eihl] (the
      module-derived overlapping execution of [inc_ooo_exec] runs over
      [EI uδ] and [EIhl uδ]; non-vacuity).  Same I=∅ scope as
      [CounterHL].
    - RLHL-3a iteration 3 (latest-review m-34, m-35, m-24):
      [CounterEIhlFrame.counter_frame_rlhl2] (the same counter over
      [EIhl uδ], with a rely and a guarantee whose memory part is "any
      [EIhl uδ] steps", no value; the call's FAA record is tracked by
      [RelaxedHoareCompLinSpec.eihl_mine]; closed),
      [counter_frame_complin_ei], [counter_frame_rel_lin],
      [ooo_rtrace_frame], [ooo_rel_lin_frame] (non-vacuity, on
      [CounterEIhl.inc_ooo_exec_ei]); [WRCopyCat.WRSig_wf],
      [WRCopyCat.WRSig0_wf]; [ReadPairUniversal.read_pair_no_rlhl2]
      (item (a) below).
    - (a) [PairSig] with a writer: [read_pair_no_certificate],
      [read_pair_not_methodsem], [read_pair_not_rlhl] (the unlocked double
      read is refuted *relative to (I2, R2)*: under the coupling
      invariant [I2] and a rely [R2] that contains the guarantee [G2] of
      another call, for every guarantee [G]; not for every [I] and [R]);
      positive controls [read_one_sound], [writer_sound],
      [pair_discriminates]; [pair_rlhl2] (every field of [RLHL2Hyps]
      holds for [I2], [R2], [G2], [M2good]).  The universal negative
      (latest-review m-24): [ReadPairUniversal.read_pair_no_rlhl2] (for
      every [I], [R], [G], no [RLHL2Hyps] for [M2] over [MemLTS] with
      [PairLTS] from the initial states of [pair_rlhl2]; through
      [RelaxedHoareCompLin.rlhl_complin] and a two-thread execution
      derived from module steps; [classic]) and
      [read_pair_no_rlhl2_gen], [pair_discriminates_rlhl2]; its semantic
      core, without the logic, is [read_pair_not_complin] (closed;
      latest-review m-38).
      [CounterRelLin.bad_counter_no_rlhl2] is the other universal
      negative.
    - (a1) [read_pair_old_derivation], [read_pair_old_method_provable]:
      the old existential judgement is satisfied by an infeasible path.
    - (c) [M4], two independent reads: [m4_provable], [m4_sound];
      [m4_invY_unordered], [m4_invY_overtakes_resX] (statements about
      the hand-built list [m4_ctx], which is not derived from the
      derivation, latest-review m-23).  Its own-interference premises are
      discharged through [newslot_guar_in_rely].
    - (b) [XYSig], two calls of one thread: [rdx_sound], [wry_sound],
      [xy_rlhl2]; M-12 prototype [two_calls_init], [two_calls_step],
      [two_calls_execution]; [two_calls_reorder] (on the configuration of
      [two_calls_init], the write of [k2] overtakes the read of [k1]).
      No operation of [M5] writes [X], and [R5]/[G5] keep [X]: the read
      of [RdX] is never interfered with (latest-review m-23).
    - (a1), (b) and (c) are smoke tests of the logic, superseded as
      witnesses (latest-review m-50): [two_calls_reorder] has
      conditional premises and no lemma constructs its configurations,
      [m4_ctx] is hand-written and frame-only, and (a1)'s claim that
      [OQ (0, 1)] is false in every execution is argued only in a
      comment.  The module-derived, observable witnesses of same-thread
      overtaking are [RelaxedHoareCounterXY.sb_exec], [sb_exec_gen],
      [lb_exec] and [CounterXYZ.z_reorder_exec].
    - M-11 (i): [own_reorder_not_one] (a read after an own write may
      return the old value: "result = 1" is not [MethodSem]) and
      [own_reorder_le1_sound] ("result <= 1" is derivable).
    - M-11 (ii): [tas_derivation], [tas_sound]: interference premises
      that hold only by the [~ before] hypotheses ([tas_before]); they are
      not provable by stability ([tas_needs_order]) and
      [newslot_guar_in_rely] does not apply ([tas_guar_not_in_rely]).
      M-17: [tas_not_hvf], [pair_not_hvf].
    - M-14: [await_sound], a spin loop through [cprov_dowhile].
    - M-11 (partial) ([LogRead]): an [RLHL2Hyps] instance ([log_rlhl2])
      with a non-blocking body (a read of [X] and an unordered log write
      of [Y]) and a concurrent writer of [X]; the unordered own
      linearization changes the call's pool entry, which an edge
      assertion of the log write reads ([KAlive_GLin]); the natural edge
      is not stable under it ([log_needs_alive]) and the guarantee is not
      in the rely ([log_guar_not_in_rely]).

    Single-call checks (latest-review m-19): [m4_single_call],
    [own_reorder_le1_single_call], [tas_single_call] and
    [await_single_call] state the initial invariant and the triple for
    every thread, but no [RLHL2Hyps] instance: [M4impl]'s writer cannot
    satisfy [G4], which freezes memory; [Mtas] is not atomic ([GT] is not
    in [RT]); [RA] and [Rrw] allow no concurrent writer.  They test the
    rules, not the composition.  [RLHL2Hyps] instances: [pair_rlhl2],
    [xy_rlhl2] (ghost-free invariants, commuting pairs, helping),
    [LogRead.log_rlhl2] (non-blocking body, helping),
    [CounterHL.counter_hl_rlhl2] (an invariant that reads the ghost),
    [CounterEIhl.counter_eihl_rlhl2] (the same counter over [EIhl uδ])
    and [CounterEIhlFrame.counter_frame_rlhl2] (the same, with a
    value-free memory rely).

    Limitations stated where they occur: [Counter] (records keyed by
    underlay handle only, over the overwriting [CVE]) is not claimed to
    satisfy [RLHL2Hyps]; [CounterHL] is its handle-linear redo.  The
    two-call prototypes cover the closed system of two calls (no third
    invocation); [RelaxedHoareGSim.rlhl_gsim] covers every number of
    calls.  The end-to-end counter theorem ([CounterRelLin]) covers the
    I=∅ fragment, over an underlay atomic at invocation ([HVE], not
    [complete_pres]; latest-review M-19), and is over [HVE] only: [HVE]
    is not a complete presentation ([hve_not_complete]), so the result
    does not transfer to other underlays implementing the FAA
    specification and does not compose vertically (latest-review M-18).
    No load-buffering example in this file (M-11 (iii) is not done).
    The RLHL-level load-buffering datum is in
    examples/Relaxed/RelaxedHoareCounterXY.v (latest-review m-46): the
    module-derived LB execution [lb_exec] is accepted through the
    instance [cxy_rlhl2] ([lb_rel_lin]) and excludes any RLHL proof of
    the by-location module for [si_cb] ([cxy_mixed_no_rlhl2]; at trace
    level, LB is rejected by any overlay relation lacking both
    (Get, Inc) cross pairs, [lb_not_rel_lin_gen]; nothing is claimed
    for narrower relations that keep one of them); it is a renaming, not
    an own-event OG instance.
    Only [CounterHL]'s specification is shown to satisfy [HVF]
    ([counter_spec_hvf]); [TLTS] and [PairLTS] provably do not
    ([tas_not_hvf], [pair_not_hvf]); the other helping-based
    specifications are not claimed to. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedRGISimulation.
Require Import models.simlin.RelaxedAssertion.
Require Import models.simlin.RelaxedLogic.
Require Import examples.Relaxed.DependencyFrontierExamples.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.view.ViewLHL.
Require Import models.view.ViewPossibility.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareGSim.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.

Import ListNotations.


Module RelaxedHoareChecks.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.
  Import DependencyFrontierExamples.

  (** ** The memory LTS

      An invocation does not change the memory, a read response returns
      the current value, a write takes effect at its response.  Under the
      tagged scheduler this LTS is *not* per-location coherent
      (latest-review m-14): response/response pairs are unordered and an
      invocation may overtake an earlier response it is not tagged with, so
      a read of [x] can return a value older than that of a write of [x]
      issued before it by the same thread ([own_reorder_not_one] below).
      The checks over [MemLTS] test the logic, not a weak-memory model. *)

  Definition Mem : Type := Location -> nat.

  Definition loc_eqb (l1 l2 : Location) : bool :=
    match l1, l2 with
    | X, X | U, U | Y, Y => true
    | _, _ => false
    end.

  Definition upd (σ : Mem) (l : Location) (v : nat) : Mem :=
    fun l' => if loc_eqb l l' then v else σ l'.

  Definition mem_step (ev : ThreadEvent RlxSig) (σ σ' : Mem) : Prop :=
    match te_ev _ ev with
    | InvEv _ _ => σ' = σ
    | ResEv _ op r =>
        match op return memory_arity op -> Prop with
        | MRead l => fun v => v = σ l /\ σ' = σ
        | MWrite l v => fun _ => σ' = upd σ l v
        end r
    end.

  Definition MemLTS : LTS RlxSig :=
    {| State := Mem; Step := mem_step; Error := NoError |}.

  Definition σ0 : Mem := fun _ => 0.

  (** The underlay signature is well-formed. *)
  Lemma RlxSig_wf : RelaxedSig.well_formed RlxSig.
  Proof. constructor; [intros x H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

  (** ** Lin-pool helpers *)

  Section PoolHelpers.
    Context {F : RelaxedSig.t}.

    Lemma lin_update_in (key : CallKey F) before after (pool pool' : LinPool F) e :
      lin_update key before after pool pool' -> In e pool' ->
      In e pool \/ e = make_lin_entry key after.
    Proof.
      intros Hu. induction Hu as [tail | entry pool0 pool0' Hneq Hu IH]; intros Hin.
      - destruct Hin as [<- | Hin]; [right; reflexivity | left; right; exact Hin].
      - destruct Hin as [<- | Hin]; [left; left; reflexivity |].
        destruct (IH Hin) as [H | H]; [left; right; exact H | right; exact H].
    Qed.

    Lemma lin_update_exists (key : CallKey F) before after (pool : LinPool F) :
      lin_pool_well_formed pool -> lin_lookup key before pool ->
      exists pool', lin_update key before after pool pool'.
    Proof.
      induction pool as [| e pool IH]; intros Hwf Hl; [destruct Hl |].
      unfold lin_pool_well_formed, lin_domain in Hwf. cbn in Hwf.
      apply NoDup_cons_iff in Hwf as [Hnin Hwf].
      destruct Hl as [He | Hl].
      - subst e. eexists. apply lin_update_here.
      - destruct (IH Hwf Hl) as (pool' & Hu). exists (e :: pool').
        apply lin_update_next; [| exact Hu].
        intros Hk. apply Hnin. rewrite Hk. apply in_map_iff.
        exists (make_lin_entry key before). split; [apply lin_key_make_lin_entry | exact Hl].
    Qed.

    Lemma lin_invoke_update_prefix t h op (pre P P' : LinPool F) :
      (forall e, In e pre -> lin_key e <> (t, h)) ->
      lin_invoke_update t h op P P' -> lin_invoke_update t h op (pre ++ P) (pre ++ P').
    Proof.
      induction pre as [| e pre IH]; intros Hpre Hu; cbn; [exact Hu |].
      apply lin_invoke_update_next; [apply Hpre; left; reflexivity |].
      apply IH; [intros e' He'; apply Hpre; right; exact He' | exact Hu].
    Qed.

    (** *** Helping: linearizing every pending invocation

        For a specification whose invocation step is a no-op, every
        [ls_inv] entry of a well-formed pool can be moved to [ls_lini],
        oldest first; each step is enabled ([invocation_ready]) because
        every older entry has already been moved.  This discharges the
        *abstract* same-thread order of well-formed overlays
        ([invocation_ready]) for calls that linearize at a response or at
        return: a call first helps all pending invocations, then takes its
        own response step.  [poss_step] is [exists owner], so helping is a
        legal abstract step.

        What helping does not achieve (latest-review M-17): it orders the
        no-op abstract invocations, not the effects, which happen at the
        responses, in any order.  [RelaxedGSim.gsim_rel_lin] additionally
        needs [HVF] (every complete well-formed trace of the specification
        LTS is relaxed-linearizable), and [rhb] orders two same-thread,
        non-semi-independent operations by invocation.  For [TLTS], whose
        same-thread pairs do not commute, [HVF] fails ([tas_not_hvf]);
        this one instance suggests, but does not prove, that commuting is
        needed for helping to be safe.  Commuting is not sufficient:
        [HVF] also fails for [PairLTS] (commuting reads, with another
        thread's write between their responses, [pair_not_hvf]).  RLHL-2
        specifications take effect at the abstract invocation instead
        ([RelaxedHoareSpec.EI], [CounterHL]), and their [HVF] is a library
        fact ([RelaxedHoareSpec.ei_hvf]).  For the over-every-underlay
        route of RLHL-3 the author chose the stamp-based overlay
        [ViewLHL.VT nuF] instead (latest-review M-18,
        [CounterRelLin.vt_junk], [CounterRelLin.counter_vt_no_rlhl2]). *)

    Definition lin_help (e : LinEntry F) : LinEntry F :=
      match lin_state F e with
      | ls_inv o => Build_LinEntry (lin_tid F e) (lin_handle F e) (ls_lini o)
      | _ => e
      end.

    Lemma lin_help_key e : lin_key (lin_help e) = lin_key e.
    Proof. destruct e as [t h [o | o | o r]]; reflexivity. Qed.

    Lemma lin_help_domain (pool : LinPool F) : lin_domain (map lin_help pool) = lin_domain pool.
    Proof.
      unfold lin_domain. rewrite map_map. apply map_ext. apply lin_help_key.
    Qed.

    Lemma lin_help_wf (pool : LinPool F) :
      lin_pool_well_formed pool -> lin_pool_well_formed (map lin_help pool).
    Proof. unfold lin_pool_well_formed. rewrite lin_help_domain. auto. Qed.

    Lemma lin_help_ready t op (pool : LinPool F) : invocation_ready t op (map lin_help pool).
    Proof.
      induction pool as [| e pool IH]; cbn; constructor; [| exact IH].
      right. destruct e as [te he [o | o | o r]]; cbn; exact Logic.I.
    Qed.

    Context (VF : LTS F).

    Lemma drain_gen v :
      (forall t h o, Step VF (Build_ThreadEvent t (InvEv h o)) v v) ->
      forall (pool pre : LinPool F), NoDup (lin_domain (pre ++ pool)) ->
        poss_steps VF (PossOk v (pre ++ pool)) (PossOk v (pre ++ map lin_help pool)).
    Proof.
      intros Hnoop. induction pool as [| e pool IH]; intros pre Hnd; cbn [map].
      - apply rt_refl.
      - eapply rt_trans.
        + specialize (IH (pre ++ [e])). rewrite <- !app_assoc in IH. apply IH. exact Hnd.
        + cbn [app]. destruct e as [te he [o | o | o r]]; cbn [lin_help lin_state]; [| apply rt_refl | apply rt_refl].
          apply rt_step. exists (te, he). apply (psa_inv VF te he o v v); [| apply Hnoop].
          apply lin_invoke_update_prefix.
          * intros e' He' Hk. unfold lin_domain in Hnd. rewrite map_app in Hnd. cbn in Hnd.
            apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. left.
            change (lin_key (Build_LinEntry te he (ls_inv o))) with (te, he). rewrite <- Hk. apply in_map. exact He'.
          * apply (lin_invoke_update_here te he o (map lin_help pool)). apply lin_help_ready.
    Qed.

    Lemma drain v (pool : LinPool F) :
      (forall t h o, Step VF (Build_ThreadEvent t (InvEv h o)) v v) ->
      lin_pool_well_formed pool ->
      poss_steps VF (PossOk v pool) (PossOk v (map lin_help pool)).
    Proof. intros Hnoop Hwf. exact (drain_gen v Hnoop pool [] Hwf). Qed.

    (** [keeps k pool pool']: the phase of [k] can only be moved from
        [ls_inv] to [ls_lini] (by helping); every other entry of [k] is
        kept. *)
    Definition keeps (k : CallKey F) (pool pool' : LinPool F) : Prop :=
      forall ls, lin_lookup k ls pool ->
        lin_lookup k ls pool' \/ exists o, ls = ls_inv o /\ lin_lookup k (ls_lini o) pool'.

    Lemma keeps_refl k pool : keeps k pool pool.
    Proof. intros ls Hl. left. exact Hl. Qed.

    Lemma keeps_trans k p1 p2 p3 : keeps k p1 p2 -> keeps k p2 p3 -> keeps k p1 p3.
    Proof.
      intros H12 H23 ls Hl. destruct (H12 ls Hl) as [Hl2 | (o & -> & Hl2)].
      - exact (H23 _ Hl2).
      - right. exists o. split; [reflexivity |].
        destruct (H23 _ Hl2) as [Hl3 | (o' & Heq & _)]; [exact Hl3 | discriminate Heq].
    Qed.

    Lemma keeps_help k (pool : LinPool F) : keeps k pool (map lin_help pool).
    Proof.
      intros ls Hl. unfold lin_lookup in *.
      pose proof (in_map lin_help _ _ Hl) as Hm.
      destruct ls as [o | o | o r]; cbn in Hm.
      - right. exists o. split; [reflexivity | exact Hm].
      - left. exact Hm.
      - left. exact Hm.
    Qed.

    Lemma keeps_update_other k k' before after (pool pool' : LinPool F) :
      lin_update k' before after pool pool' -> k <> k' -> keeps k pool pool'.
    Proof. intros Hu Hne ls Hl. left. eapply lin_update_other_lookup; eauto. Qed.

    Lemma keeps_insert k k' st (pool pool' : LinPool F) :
      lin_insert k' st pool pool' -> keeps k pool pool'.
    Proof. intros Hi ls Hl. left. destruct Hi. right. exact Hl. Qed.

    Lemma keeps_remove_other k k' st (pool pool' : LinPool F) :
      lin_remove k' st pool pool' -> k <> k' -> keeps k pool pool'.
    Proof. intros Hr Hne ls Hl. left. eapply lin_remove_other_lookup; eauto. Qed.

    (** [k] has not linearized its response yet. *)
    Definition KPhase (k : CallKey F) (o : Sig.op (RelaxedSig.effect F)) (pool : LinPool F) : Prop :=
      lin_lookup k (ls_inv o) pool \/ lin_lookup k (ls_lini o) pool.

    Lemma keeps_phase k o pool pool' : keeps k pool pool' -> KPhase k o pool -> KPhase k o pool'.
    Proof.
      intros Hk [Hl | Hl].
      - destruct (Hk _ Hl) as [Hl' | (o' & Heq & Hl')]; [left; exact Hl' |].
        injection Heq as <-. right. exact Hl'.
      - destruct (Hk _ Hl) as [Hl' | (o' & Heq & _)]; [right; exact Hl' | discriminate Heq].
    Qed.

    Lemma keeps_linr k o r pool pool' :
      keeps k pool pool' -> lin_lookup k (ls_linr o r) pool -> lin_lookup k (ls_linr o r) pool'.
    Proof. intros Hk Hl. destruct (Hk _ Hl) as [Hl' | (o' & Heq & _)]; [exact Hl' | discriminate Heq]. Qed.

    (** Linearizing [k] at its response (or at return): help every pending
        invocation, then take [k]'s response step. *)
    Lemma linearize_response (k : CallKey F) o r v v' (pool : LinPool F) :
      (forall t h o', Step VF (Build_ThreadEvent t (InvEv h o')) v v) ->
      lin_pool_well_formed pool -> KPhase k o pool ->
      Step VF (Build_ThreadEvent (fst k) (ResEv (snd k) o r)) v v' ->
      exists pool', poss_steps VF (PossOk v pool) (PossOk v' pool') /\
        lin_lookup k (ls_linr o r) pool' /\ lin_pool_well_formed pool' /\
        forall k', k' <> k -> keeps k' pool pool'.
    Proof.
      intros Hnoop Hwf Hph Hst.
      assert (Hl : lin_lookup k (ls_lini o) (map lin_help pool))
        by (destruct (keeps_phase k o _ _ (keeps_help k pool) Hph) as [Hl | Hl];
            [exfalso; destruct (in_map_iff lin_help pool (make_lin_entry k (ls_inv o))) as [Hm _];
             destruct (Hm Hl) as ([te he [o1 | o1 | o1 r1]] & Heq & _); discriminate Heq | exact Hl]).
      destruct (lin_update_exists k (ls_lini o) (ls_linr o r) (map lin_help pool) (lin_help_wf _ Hwf) Hl)
        as (pool' & Hu).
      exists pool'. split; [| split; [| split]].
      - eapply rt_trans; [apply drain; assumption |].
        apply rt_step. exists k. destruct k as [t h]. apply (psa_ret VF t h o r v v' _ _ Hu Hst).
      - eapply lin_update_target. exact Hu.
      - eapply lin_update_well_formed; [exact Hu | apply lin_help_wf; exact Hwf].
      - intros k' Hne. eapply keeps_trans; [apply keeps_help | eapply keeps_update_other; eauto].
    Qed.
  End PoolHelpers.


  (** ** Store helpers *)

  Section StoreHelpers.
    Context {E : RelaxedSig.t}.

    Lemma resolve_store_keep_pending h op r (H H' : FutureStore E) e :
      resolve_store h op r H H' -> In e H -> fe_handle E e <> h -> In e H'.
    Proof.
      intros Hres Hin Hne. destruct (resolve_store_fwd _ _ _ _ _ _ Hres Hin) as [Hin' | ->];
        [exact Hin' | exfalso; apply Hne; reflexivity].
    Qed.

    Lemma resolve_two h1 op1 r1 h2 op2 r2 (H' H'' : FutureStore E) :
      h2 <> h1 ->
      resolve_store h1 op1 r1 (add_pending h2 op2 (add_pending h1 op1 empty_store)) H' ->
      resolve_store h2 op2 r2 H' H'' -> all_resolved H''.
    Proof.
      intros Hne Hr1 Hr2. unfold add_pending, empty_store in Hr1.
      inversion Hr1 as [tail Heq1 Heq2 | h' cell H0 H0' Hneq Hres' Heq1 Heq2]; subst.
      - exfalso. apply Hne. reflexivity.
      - inversion Hres' as [tail' Heq1' Heq2' | h'' cell' H1 H1' Hneq' Hres'' Heq1' Heq2']; subst;
          [| exfalso; apply Hneq'; reflexivity].
        inversion Hr2 as [tail2 Heq3 Heq4 | h3 cell3 H3 H3' Hneq3 Hres3 Heq3 Heq4]; subst;
          [| exfalso; apply Hneq3; reflexivity].
        repeat constructor.
    Qed.
  End StoreHelpers.

  (** ** The traces of a blocking call

      [call_trace]: a trace of [call op] is its invocation (tagged with the
      resolved handles of the empty store, i.e. with nothing) followed by
      responses only.  The proof reads the program through small-inversion
      views ([after_future], [NoFut]) computed by [match], so it never
      inverts a step at a [Wait] (no [eq_rect_eq]). *)

  Section CallTrace.
    Context {E : RelaxedSig.t} {R : Type}.

    Definition is_ret (p : Prog E R) : Prop := match p with Ret _ => True | _ => False end.

    Definition NoFut (p : Prog E R) : Prop :=
      match p with
      | Wait f k => forall x, is_ret (k x)
      | Ret _ => True
      | _ => False
      end.

    Definition after_future (p : Prog E R) : Prop :=
      match p with
      | Future o k => forall h, NoFut (k (MkFutureRef o h))
      | _ => False
      end.

    Definition prog_fop (p : Prog E R) : option (Sig.op (RelaxedSig.effect E)) :=
      match p with Future o _ => Some o | _ => None end.

    Lemma nofut_step t a (c c' : ProgramConfig E R) :
      program_step_tagged t a c c' -> NoFut (pc_prog c) ->
      NoFut (pc_prog c') /\ forall m, a = TEmit m -> is_response (untag m).
    Proof.
      intros Hstep. destruct Hstep as [op k h H Hfresh | op deps k h H Hfresh | op h ret k H Hres
                                     | op h ret k H H' Hres | op h ret p H H' Hres | p H];
        cbn [pc_prog]; intros Hn; try destruct Hn.
      - specialize (Hn ret). split; [| intros m Hm; discriminate Hm].
        destruct (k ret); cbn in Hn |- *; tauto.
      - specialize (Hn ret). split; [| intros m Hm; injection Hm as <-; exact Logic.I].
        destruct (k ret); cbn in Hn |- *; tauto.
      - split; [exact Hn |]. intros m Hm. injection Hm as <-. exact Logic.I.
    Qed.

    Lemma nofut_exec t c tr c' :
      program_execution_tagged t c tr c' -> @NoFut (pc_prog c) ->
      Forall (fun m => is_response (untag m)) tr.
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hstep Hexec IH | c1 c2 c3 m tr Hstep Hexec IH]; intros Hn.
      - constructor.
      - apply IH. exact (proj1 (nofut_step _ _ _ _ Hstep Hn)).
      - destruct (nofut_step _ _ _ _ Hstep Hn) as [Hn' Hm]. constructor; [exact (Hm m eq_refl) | apply IH; exact Hn'].
    Qed.
  End CallTrace.

  Lemma call_trace {E : RelaxedSig.t} t (op : Sig.op (RelaxedSig.effect E)) tr r :
    program_produces_tagged t (call op) tr r ->
    exists h rest, tr = Build_TaggedEvent (Build_ThreadEvent t (InvEv h op)) (resolved_in empty_store) :: rest /\
                   Forall (fun m => is_response (untag m)) rest.
  Proof.
    intros (c' & Hexec & Hterm). unfold initial_program in Hexec.
    remember (Build_ProgramConfig (call op) (@empty_store E)) as c0 eqn:Hc0.
    assert (Hview : after_future (pc_prog c0)) by (rewrite Hc0; cbn; intros h x; exact Logic.I).
    assert (Hop : prog_fop (pc_prog c0) = Some op) by (rewrite Hc0; reflexivity).
    assert (Hst : pc_futures c0 = empty_store) by (rewrite Hc0; reflexivity).
    clear Hc0.
    destruct Hexec as [c | c1 c2 c3 trace Hstep Hexec | c1 c2 c3 m trace Hstep Hexec].
    - destruct Hterm as [H x Hres]. cbn in Hview. destruct Hview.
    - exfalso. remember (@TSilent E) as a eqn:Ha.
      destruct Hstep as [op0 k h H Hfresh | op0 deps k h H Hfresh | op0 h ret k H Hres
                        | op0 h ret k H H' Hres | op0 h ret p H H' Hres | p H];
        cbn [pc_prog] in Hview; try discriminate Ha; destruct Hview.
    - remember (TEmit m) as a eqn:Ha.
      destruct Hstep as [op0 k h H Hfresh | op0 deps k h H Hfresh | op0 h ret k H Hres
                        | op0 h ret k H H' Hres | op0 h ret p H H' Hres | p H];
        cbn [pc_prog pc_futures] in Hview, Hop, Hst; try discriminate Ha; try destruct Hview.
      + injection Hop as ->. subst H. injection Ha as <-.
        exists h, trace. split; [reflexivity |].
        eapply nofut_exec; [exact Hexec | exact (Hview h)].
      + subst H. inversion Hres.
  Qed.

  (** ** B-5: the overlapping same-thread counter

      The counterexample of latest-review B-5: a counter [Inc] implemented
      by one FAA on an underlay counter; both signatures are well-formed
      and no pair of operations is semi-independent, so the module orders
      two overlapping same-thread FAA invocations by (F2) across calls.

      - [counter_methodsem_unsat]: the iteration-1 triple
        ([RelaxedHoareBase.Iter1.MethodSem]) has no model, for any I, R,
        G (regression; verbatim from the review, on [Iter1]).
      - [counter_b5_excluded]: the schedule of that proof (the newer
        call's FAA first) has no ghost transition.
      - [counter_provable] / [counter_methodsem]: the redesigned triple is
        derivable with the rules, with the invariant [Ic] (per thread, the
        [ls_inv] calls are the owners of the pending FAA invocations of the
        ghost, in age order), true initially ([counter_init]).
      - [counter_b5] conjoins both halves.

      Limitation of this instance (corrected in iteration 3, latest-review
      M-16 (iv)): it is not claimed to satisfy [RLHL2Hyps].  [Gc]
      constrains only the abstract pool, not the memory, so [Gc k ⊆ Rc k']
      fails without any handle collision (a [Gc] step may erase a record,
      an [Rc] step may not).  The obstacle is not the choice of [Gc]:
      [CVE]'s invocation overwrites the record of its key, and the per-call
      triple carries no used-key information, so a certificate must also
      cover a later call of the same thread that re-invokes an underlay
      key already used (the module's [trace_fresh] excludes it).  Over such
      an underlay no [I], [R], [G] satisfy [RLHL2Hyps], also with records
      keyed by (thread, handle) ([CounterHL.counter_ow_unsat]); over a
      handle-linear underlay the counter does
      ([CounterHL.counter_hl_rlhl2]).  In addition, [CVE] and [CVF] key
      their records by handle only, which is wrong across threads (handles
      are fresh per thread only). *)

  Module Counter.

    Inductive UOp := FAA.
    Definition u_ar (o:UOp):Type := match o with FAA => nat end.
    Canonical Structure UEff : Sig.t := {| Sig.op := UOp; Sig.ar := u_ar |}.
    Definition USig : RelaxedSig.t := {| RelaxedSig.effect := UEff; RelaxedSig.handle := nat; RelaxedSig.semi_independent := fun _ _ => False; RelaxedSig.mode := fun _ => Local |}.
    Inductive OOp := Inc.
    Definition o_ar (o:OOp):Type := match o with Inc => nat end.
    Canonical Structure OEff : Sig.t := {| Sig.op := OOp; Sig.ar := o_ar |}.
    Definition OSig : RelaxedSig.t := {| RelaxedSig.effect := OEff; RelaxedSig.handle := nat; RelaxedSig.semi_independent := fun _ _ => False; RelaxedSig.mode := fun _ => Local |}.
    Lemma USig_wf : RelaxedSig.well_formed USig. Proof. constructor; [intros x H; exact H | intros _ _ [] | intros _ _ []]. Qed.
    Lemma OSig_wf : RelaxedSig.well_formed OSig. Proof. constructor; [intros x H; exact H | intros _ _ [] | intros _ _ []]. Qed.
    Definition CState := (nat * (nat -> option nat))%type.
    Definition rupd (rec : nat -> option nat) (h v : nat) : nat -> option nat := fun h' => if Nat.eqb h h' then Some v else rec h'.
    Definition u_step (ev : ThreadEvent USig) (s s' : CState) : Prop :=
      match te_ev _ ev with
      | InvEv h _ => s' = (S (fst s), rupd (snd s) h (fst s))
      | ResEv h op r => match op return u_ar op -> Prop with FAA => fun r => snd s h = Some r /\ s' = s end r
      end.
    Definition CVE : LTS USig := {| State := CState; Step := u_step; Error := NoError |}.
    Definition o_step (ev : ThreadEvent OSig) (s s' : CState) : Prop :=
      match te_ev _ ev with
      | InvEv h _ => s' = (S (fst s), rupd (snd s) h (fst s))
      | ResEv h op r => match op return o_ar op -> Prop with Inc => fun r => snd s h = Some r /\ s' = s end r
      end.
    Definition CVF : LTS OSig := {| State := CState; Step := o_step; Error := NoError |}.
    Definition body : Prog USig nat := @Future USig nat FAA (fun f => Wait f (fun (r : nat) => Ret r)).
    Definition Mc : RelaxedModuleImpl USig OSig := fun op t => match op as o return Prog USig (Sig.ar o) with Inc => body end.
    Definition t0 : tid := 1%positive.
    Definition σ0 : CState := (0, fun _ => None).

    (** ** The redesigned triple holds *)

    Abbreviation PA := (Assn CVE CVF).
    Abbreviation COk v pool := (@PossOk OSig CVF v pool).

    Definition ek (t : tid) (e : LinEntry OSig) : list (CallKey OSig) :=
      if Pos.eqb (lin_tid OSig e) t then
        match lin_state OSig e with ls_inv _ => [lin_key e] | _ => [] end
      else [].

    (** The [ls_inv] calls of thread [t], oldest first (pools are newest
        first). *)
    Fixpoint inv_keys (t : tid) (P : LinPool OSig) : list (CallKey OSig) :=
      match P with
      | [] => []
      | e :: P' => inv_keys t P' ++ ek t e
      end.

    (** The owners of the pending ghost invocations of thread [t], in queue
        order. *)
    Definition gkeys (t : tid) (g : Ghost USig OSig) : list (CallKey OSig) :=
      map se_owner (filter (fun e => Pos.eqb (fst (se_owner e)) t) g).

    Definition Jwf (e : ScheduledEvent USig OSig) : Prop :=
      te_tid USig (se_event e) = fst (se_owner e) /\ is_invocation (se_event e).

    (** The invariant: the concrete and the abstract counter agree, the pool
        is duplicate-free, and, per thread, the [ls_inv] calls are exactly
        the owners of the pending FAA invocations, in the same age order. *)
    Definition Ic : PA := fun s => exists ca reca pool,
      ps_poss s = COk (ca, reca) pool /\ fst (ps_mem s) = ca /\ lin_pool_well_formed pool /\
      (forall t', inv_keys t' pool = gkeys t' (ps_ghost s)) /\
      Forall Jwf (ps_ghost s).

    Lemma gkeys_app t g1 g2 : gkeys t (g1 ++ g2) = gkeys t g1 ++ gkeys t g2.
    Proof. unfold gkeys. rewrite filter_app, map_app. reflexivity. Qed.

    Lemma inv_keys_in t P k : In k (inv_keys t P) -> In k (lin_domain P).
    Proof.
      induction P as [| e P IH]; cbn; [intros [] |]. intros Hin. apply in_app_or in Hin.
      destruct Hin as [Hin | Hin]; [right; auto |].
      unfold ek in Hin. destruct (Pos.eqb (lin_tid OSig e) t); [| destruct Hin].
      destruct (lin_state OSig e); [| destruct Hin | destruct Hin].
      destruct Hin as [<- | []]. left. reflexivity.
    Qed.

    Lemma inv_keys_lookup t h P :
      lin_lookup (t, h) (@ls_inv OSig Inc) P -> In (t, h) (inv_keys t P).
    Proof.
      induction P as [| e P IH]; cbn; [intros [] |]. intros [-> | Hin].
      - apply in_or_app. right. unfold ek. cbn. rewrite Pos.eqb_refl. left. reflexivity.
      - apply in_or_app. left. auto.
    Qed.

    Lemma inv_keys_nil_ready t P : inv_keys t P = [] -> @invocation_ready OSig t Inc P.
    Proof.
      induction P as [| e P IH]; cbn; intros Hnil; [constructor |].
      apply app_eq_nil in Hnil as [H1 H2]. constructor; [| apply IH; exact H1].
      unfold older_entry_allows_invocation. unfold ek in H2.
      destruct (Pos.eqb_spec (lin_tid OSig e) t) as [Heq | Hne]; [right | left; exact Hne].
      destruct (lin_state OSig e); [discriminate | exact Logic.I | exact Logic.I].
    Qed.

    Lemma app_head {A : Type} (l1 l2 : list A) x rest :
      l1 <> [] -> l1 ++ l2 = x :: rest -> exists rest', l1 = x :: rest' /\ rest = rest' ++ l2.
    Proof.
      destruct l1 as [| y l1]; [intros H; contradiction H; reflexivity |].
      intros _ Heq. cbn in Heq. injection Heq as -> <-. eexists. split; reflexivity.
    Qed.

    (** The oldest [ls_inv] call of its thread may linearize its invocation. *)
    Lemma oldest_invoke t h P :
      lin_pool_well_formed P -> lin_lookup (t, h) (@ls_inv OSig Inc) P ->
      forall rest, inv_keys t P = (t, h) :: rest ->
      exists P', @lin_invoke_update OSig t h Inc P P' /\ inv_keys t P' = rest /\
                 (forall t', t' <> t -> inv_keys t' P' = inv_keys t' P).
    Proof.
      induction P as [| e P IH]; intros Hwf Hl rest Hk; [destruct Hl |].
      unfold lin_pool_well_formed, lin_domain in Hwf. cbn in Hwf.
      apply NoDup_cons_iff in Hwf as [Hnin Hwf].
      destruct Hl as [He | Hl].
      - subst e. cbn in Hk. unfold ek in Hk. cbn in Hk. rewrite Pos.eqb_refl in Hk.
        assert (Hnil : inv_keys t P = []).
        { destruct (inv_keys t P) as [| x l] eqn:HP; [reflexivity |].
          exfalso. cbn in Hk. injection Hk as -> _. apply Hnin.
          replace (lin_key (make_lin_entry (t, h) (@ls_inv OSig Inc))) with (t, h) by reflexivity.
          apply (inv_keys_in t). rewrite HP. left. reflexivity. }
        rewrite Hnil in Hk. cbn in Hk. injection Hk as <-.
        exists (make_lin_entry (t, h) (@ls_lini OSig Inc) :: P). split.
        + apply lin_invoke_update_here. apply inv_keys_nil_ready. exact Hnil.
        + split.
          * cbn. rewrite Hnil. unfold ek. cbn. rewrite Pos.eqb_refl. reflexivity.
          * intros t' Hne. cbn. unfold ek. cbn.
            destruct (Pos.eqb_spec t t') as [-> | _]; [contradiction Hne; reflexivity | reflexivity].
      - assert (Hne : lin_key e <> (t, h)).
        { intros Heq. apply Hnin. rewrite Heq. apply in_map_iff.
          exists (make_lin_entry (t, h) (@ls_inv OSig Inc)). split; [reflexivity | exact Hl]. }
        cbn in Hk. destruct (app_head (inv_keys t P) (ek t e) (t, h) rest) as (rest' & HP & ->).
        { intros Hnil. pose proof (inv_keys_lookup _ _ _ Hl) as Hin. rewrite Hnil in Hin. destruct Hin. }
        { exact Hk. }
        destruct (IH Hwf Hl rest' HP) as (P' & Hu & Hk' & Hoth).
        exists (e :: P'). split; [apply lin_invoke_update_next; assumption |].
        split; [cbn; rewrite Hk'; reflexivity |].
        intros t' Hne'. cbn. rewrite (Hoth t' Hne'). reflexivity.
    Qed.

    Lemma ek_noninv t e : (forall o, lin_state OSig e <> ls_inv o) -> ek t e = [].
    Proof.
      intros H. unfold ek. destruct (Pos.eqb (lin_tid OSig e) t); [| reflexivity].
      destruct (lin_state OSig e) eqn:Hs; [exfalso; exact (H _ eq_refl) | reflexivity | reflexivity].
    Qed.

    Lemma inv_keys_update key r P P' t :
      lin_update key (@ls_lini OSig Inc) (@ls_linr OSig Inc r) P P' -> inv_keys t P' = inv_keys t P.
    Proof.
      intros Hu. induction Hu as [tail | e P0 P0' Hne Hu IH]; cbn.
      - rewrite !ek_noninv by (cbn; discriminate). reflexivity.
      - rewrite IH. reflexivity.
    Qed.

    Lemma inv_keys_remove key r P P' t :
      lin_remove key (@ls_linr OSig Inc r) P P' -> inv_keys t P' = inv_keys t P.
    Proof.
      intros Hu. induction Hu as [tail | e P0 P0' Hne Hu IH]; cbn.
      - rewrite (ek_noninv t (make_lin_entry key _)) by (cbn; discriminate). apply eq_sym, app_nil_r.
      - rewrite IH. reflexivity.
    Qed.

    (** The FAA invocation of [(t, h)] on the thread frontier. *)
    Lemma emit_ready t h hu P g1 g2 :
      lin_pool_well_formed P -> lin_lookup (t, h) (@ls_inv OSig Inc) P ->
      (forall t', inv_keys t' P = gkeys t' (g1 ++ Build_ScheduledEvent (t, h) (Build_ThreadEvent t (@InvEv USig hu FAA)) :: g2)) ->
      Forall Jwf g1 ->
      Forall (fun e => ~ inv_blocks (se_event e) (Build_ThreadEvent t (@InvEv USig hu FAA))) g1 ->
      exists P', @lin_invoke_update OSig t h Inc P P' /\ lin_pool_well_formed P' /\
                 forall t', inv_keys t' P' = gkeys t' (g1 ++ g2).
    Proof.
      intros Hwf Hl HJ Hwf1 Hnb.
      assert (Hg1 : gkeys t g1 = []).
      { unfold gkeys. destruct (filter (fun e => Pos.eqb (fst (se_owner e)) t) g1) as [| x l] eqn:Hf;
          [reflexivity | exfalso].
        assert (Hx : In x (filter (fun e => Pos.eqb (fst (se_owner e)) t) g1)) by (rewrite Hf; left; reflexivity).
        apply filter_In in Hx as [Hx Hxt]. apply Pos.eqb_eq in Hxt.
        rewrite Forall_forall in Hwf1, Hnb. destruct (Hwf1 x Hx) as [Htid Hinv].
        apply (Hnb x Hx). split; [cbn; rewrite Htid; exact Hxt |].
        unfold is_invocation in Hinv. destruct (te_ev USig (se_event x)) as [hx [] | ]; [| destruct Hinv].
        cbn. intros []. }
      specialize (HJ t) as HJt. rewrite gkeys_app, Hg1 in HJt. cbn in HJt. rewrite Pos.eqb_refl in HJt.
      cbn in HJt. destruct (oldest_invoke t h P Hwf Hl _ HJt) as (P' & Hu & Hk & Hoth).
      exists P'. split; [exact Hu |]. split; [eapply lin_invoke_update_well_formed; eauto |].
      intros t'. destruct (Pos.eq_dec t' t) as [-> | Hne].
      - rewrite Hk, gkeys_app, Hg1. reflexivity.
      - rewrite (Hoth t' Hne), HJ, !gkeys_app. f_equal. cbn.
        destruct (Pos.eqb_spec t t') as [-> | _]; [contradiction Hne; reflexivity | reflexivity].
    Qed.

    (** Rely of [k]: the concrete and the abstract records only grow, and the
        pool entries of [k] are kept.  Guarantee of [k]: the pool entries of
        the other calls are kept. *)
    Definition Rc (k : CallKey OSig) : PRel CVE CVF := fun s s' =>
      (forall hu c, snd (ps_mem s) hu = Some c -> snd (ps_mem s') hu = Some c) /\
      exists v pool v' pool', ps_poss s = COk v pool /\ ps_poss s' = COk v' pool' /\
        (forall h c, snd v h = Some c -> snd v' h = Some c) /\
        (forall ls, lin_lookup k ls pool -> lin_lookup k ls pool').

    Definition Gc (k : CallKey OSig) : PRel CVE CVF := fun s s' =>
      exists v pool v' pool', ps_poss s = COk v pool /\ ps_poss s' = COk v' pool' /\
        forall k' ls, k' <> k -> lin_lookup k' ls pool -> lin_lookup k' ls pool'.

    Definition KInv (k : CallKey OSig) : PA := fun s =>
      exists v pool, ps_poss s = COk v pool /\ lin_lookup k (@ls_inv OSig Inc) pool.

    (** After the FAA of [k] with underlay handle [hu]: both records hold the
        fetched value, and [k] is at [ls_lini]. *)
    Definition KLini (k : CallKey OSig) (hu : nat) : PA := fun s =>
      exists c v pool, ps_poss s = COk v pool /\ snd (ps_mem s) hu = Some c /\
        snd v (snd k) = Some c /\ lin_lookup k (@ls_lini OSig Inc) pool.

    Definition KLinr (k : CallKey OSig) (r : nat) : PA := fun s =>
      exists v pool, ps_poss s = COk v pool /\ lin_lookup k (@ls_linr OSig Inc r) pool.

    Lemma KInv_stable k : Stable Ic (Rc k) (KInv k).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & _ & Hlk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Lemma KLini_stable k hu : Stable Ic (Rc k) (KLini k hu).
    Proof.
      intros s s' (c & v & pool & Hp & Hc & Hv & Hl) (Hrec & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hv1 & Hlk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists c, v1', pool1'.
      split; [exact Hp1' |]. split; [apply Hrec; exact Hc |]. split; [apply Hv1; exact Hv | apply Hlk; exact Hl].
    Qed.

    Lemma KLinr_stable k r : Stable Ic (Rc k) (KLinr k r).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & _ & Hlk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Lemma rupd_same rec h v : rupd rec h v h = Some v.
    Proof. unfold rupd. rewrite Nat.eqb_refl. reflexivity. Qed.

    Section CounterProof.
      Context (t : tid) (h : nat).
      Local Abbreviation kc := (@pair tid (RelaxedSig.handle OSig) t h).

      Definition Ωc (evs : list (ThreadEvent USig)) : Prop :=
        exists hu, evs = [Build_ThreadEvent t (@InvEv USig hu FAA)].

      Definition Qc (r : nat) : PA := KLinr kc r.

      Abbreviation Pc := (PostInvoke Ic kc Inc Ωc).

      Lemma pinit_KInv : Impl Ic Pc (KInv kc).
      Proof.
        intros [[σ p] γ] _ (p0 & γ0 & evs & _ & Hinv & _). cbn [ps_poss ps_mem ps_ghost fst snd] in Hinv.
        destruct Hinv as [st pool pool' Hins].
        destruct Hins as [pool0 Hfresh]. exists st, (make_lin_entry kc (@ls_inv OSig Inc) :: pool0).
        split; [reflexivity | left; reflexivity].
      Qed.

      Definition sl_faa (hu : nat) : Slot CVE CVF :=
        mkSlot (inv_tev (E := USig) (F := OSig) kc empty_store hu FAA) (KInv kc) (fun _ _ => True)
          (KLini kc hu) (Gc kc).

      Definition sl_res (hu : nat) (r : nat) : Slot CVE CVF :=
        mkSlot (res_tev (E := USig) (F := OSig) kc hu FAA r) (fun _ => True) (fun _ => KLini kc hu)
          (KLinr kc r) (Gc kc).

      (** The FAA update: by the ghost frontier and the invariant, [kc] is the
          oldest [ls_inv] call of its thread, so its abstract invocation is
          enabled. *)
      Lemma faa_update hu :
        EvUpdate Ic (Gc kc) kc (Build_ThreadEvent t (@InvEv USig hu FAA)) (KInv kc) (KLini kc hu).
      Proof.
        intros σ p γ γ' (v & pool & Hp & Hl) (ca & reca & pool1 & Hp1 & Hc & Hwf & HJ & HJwf) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        cbn in Hge. destruct Hge as (g1 & g2 & -> & -> & Hnb).
        cbn in Hstep. subst σ'.
        apply Forall_app in HJwf as [HJwf1 HJwf2]. pose proof (Forall_inv_tail HJwf2) as HJwf2'.
        destruct (emit_ready t h hu pool g1 g2 Hwf Hl HJ HJwf1 Hnb) as (pool' & Hu & Hwf' & HJ').
        exists (COk (S ca, rupd reca h ca) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_inv CVF t h Inc); [exact Hu | reflexivity].
        - exists ca, (S ca, rupd reca h ca), pool'. cbn. split; [reflexivity |].
          rewrite Hc. split; [apply rupd_same |]. split; [apply rupd_same |].
          apply lin_update_target with (before := @ls_inv OSig Inc) (pool := pool).
          exact (lin_invoke_update_is_update _ _ _ _ _ Hu).
        - exists (S ca), (rupd reca h ca), pool'. cbn. rewrite Hc.
          split; [reflexivity |]. split; [reflexivity |]. split; [exact Hwf' |].
          split; [exact HJ' | apply Forall_app; split; assumption].
        - exists (ca, reca), pool, (S ca, rupd reca h ca), pool'. split; [reflexivity |]. split; [reflexivity |].
          intros k' ls Hne Hlk. eapply lin_update_other_lookup; [exact (lin_invoke_update_is_update _ _ _ _ _ Hu) | exact Hne | exact Hlk].
      Qed.

      Lemma res_update hu r :
        EvUpdate Ic (Gc kc) kc (Build_ThreadEvent t (@ResEv USig hu FAA r)) (KLini kc hu) (KLinr kc r).
      Proof.
        intros σ p γ γ' (c & v & pool & Hp & Hc & Hv & Hl) (ca & reca & pool1 & Hp1 & Hca & Hwf & HJ & HJwf) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hge. subst γ'.
        cbn in Hstep. destruct Hstep as [Hr ->]. rewrite Hc in Hr. injection Hr as <-.
        rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        destruct (lin_update_exists kc (@ls_lini OSig Inc) (@ls_linr OSig Inc c) pool Hwf Hl) as (pool' & Hu).
        exists (COk (ca, reca) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_ret CVF t h Inc c _ _ _ _ Hu). cbn. split; [exact Hv | reflexivity].
        - exists (ca, reca), pool'. split; [reflexivity | eapply lin_update_target; exact Hu].
        - exists ca, reca, pool'. cbn. split; [reflexivity |]. split; [exact Hca |].
          split; [eapply lin_update_well_formed; eauto |]. split; [| exact HJwf].
          intros t'. rewrite (inv_keys_update _ _ _ _ t' Hu). apply HJ.
        - exists (ca, reca), pool, (ca, reca), pool'. split; [reflexivity |]. split; [reflexivity |].
          intros k' ls Hne Hlk. eapply lin_update_other_lookup; [exact Hu | exact Hne | exact Hlk].
      Qed.

      Lemma dprec_faa_res hu r :
        dprec [inv_tev (E := USig) (F := OSig) kc empty_store hu FAA; res_tev (E := USig) (F := OSig) kc hu FAA r] 0 1.
      Proof. econstructor; [lia | reflexivity | reflexivity |]. unfold must_precede. cbn. reflexivity. Qed.

      Lemma counter_derivation :
        RProvable Ic Rc Gc kc Pc
          (fun a Γ H => Close Ic Rc Gc kc Pc Qc a Γ H /\ Ωc (own_invs Γ)) [] empty_store (Mc Inc t).
      Proof.
        cbn. unfold body.
        apply rp_future with (sl := sl_faa); [intros; reflexivity | |].
        { intros hu _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faa].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faa].
            intros σ p γ γ' [HK _]. apply (faa_update hu σ p γ γ' HK).
          - exact pinit_KInv.
          - intros d sd _ Hd. destruct d; discriminate.
          - apply KInv_stable.
          - intros d _. apply Stable_true.
          - intros g sg Hg. destruct g; discriminate.
          - intros d g sg _ Hg. destruct g; discriminate.
          - intros y sy Hy. destruct y; discriminate.
          - intros y sy d Hy. destruct y; discriminate. }
        intros hu Hf. cbv beta.
        apply rp_wait_pending with (sl := sl_res hu); [left; reflexivity | intros; reflexivity | |].
        { intros r. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_res].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_res].
            intros σ p γ γ' [_ Hin]. apply (res_update hu r σ p γ γ'). apply (Hin 0).
            exact (dprec_faa_res hu r).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [|]]; try discriminate.
            cbn in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
          - apply Stable_true.
          - intros d _. apply KLini_stable.
          - intros g sg _. apply Stable_true.
          - intros d g sg Hd Hg Hnb. exfalso. apply dprec_lt in Hd. cbn in Hd.
            destruct g as [| g]; [| destruct g; discriminate]. assert (d = 0) by lia. subst d.
            apply Hnb. apply before_refl.
          - intros y sy Hy Hnb. exfalso. destruct y as [| y]; [| destruct y; discriminate].
            apply Hnb. apply before_dprec. exact (dprec_faa_res hu r).
          - intros y sy d Hy _ Hd. exfalso. apply dprec_lt in Hd. destruct y as [| y]; [lia |].
            destruct y; discriminate. }
        intros r H2 Hres. cbv beta. apply rp_ret. split.
        - apply close_done with
            (fin := fun d => match d with 1 => KLinr kc r | _ => fun _ => True end)
            (fin0 := fun _ => True).
          + eapply resolve_fresh_all_resolved; [constructor | exact Hres].
          + constructor.
            * intros d sd Hd. destruct d as [| [| d]]; cbn in Hd; try (destruct d; discriminate).
              -- intros s _ _. exact Logic.I.
              -- injection Hd as <-. intros s _ Hs. exact Hs.
            * intros s _ _. exact Logic.I.
            * intros d g sg Hd Hg Hnb. destruct d as [| [| d]]; [apply Stable_true | | cbn in Hd; lia].
              exfalso. apply Hnb. destruct g as [| [| g]]; [| apply before_refl | destruct g; discriminate].
              apply before_dprec. exact (dprec_faa_res hu r).
            * intros g sg _. apply Stable_true.
            * intros [| [| d]]; [apply Stable_true | apply KLinr_stable | apply Stable_true].
            * apply Stable_true.
            * intros s _ _ Hfin. exact (Hfin 1 _ eq_refl Logic.I).
        - exists hu. reflexivity.
      Qed.

      Lemma counter_PI : forall s, PostInvoke Ic kc Inc Ωc s -> Ic s.
      Proof.
        intros [[σ p] γ] (p0 & γ0 & evs & (ca & reca & pool0 & Hp0 & Hc & Hwf & HJ & HJwf) & Hinv & Hg & (hu & ->) & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst γ.
        destruct Hinv as [st pool pool' Hins]. injection Hp0 as -> <-.
        exists ca, reca, pool'. split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_insert_well_formed; eauto |]. split.
        - destruct Hins as [pool0 Hfresh]. intros t'. cbn [ps_ghost snd inv_keys]. rewrite HJ, gkeys_app. f_equal.
          unfold ek, gkeys. cbn. destruct (Pos.eqb t t'); reflexivity.
        - apply Forall_app. split; [exact HJwf |]. constructor; [| constructor].
          split; [reflexivity | exact Logic.I].
      Qed.

      Lemma counter_ret r s : Qc r s -> Ic s -> NoOwn kc (ps_ghost s) -> RetCond Ic Gc kc Inc r s.
      Proof.
        intros (v & pool & Hp & Hl) HI _. destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        exists p. split; [apply rt_refl |]. split; [exists v, pool; split; [exact Hp | exact Hl] |].
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hret. subst p. inversion Hret as [st pool1 pool2 Hrem]; subst.
        destruct HI as (ca & reca & pool3 & Hp3 & Hc & Hwf & HJ & HJwf). cbn in Hp3. injection Hp3 as -> <-.
        exists ca, reca, pool2. cbn. split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_remove_well_formed; eauto |]. split; [| exact HJwf].
        intros t'. rewrite (inv_keys_remove _ _ _ _ t' Hrem). apply HJ.
      Qed.
    End CounterProof.

    (** B-5 acceptance: the redesigned triple is provable, by the rules, for
        the overlapping same-thread counter. *)
    Theorem counter_provable t : MethodProvable Ic Rc Gc Mc t Inc (fun _ => Ωc t) (fun h => Qc t h).
    Proof.
      constructor.
      - intros h s Hs. exact (counter_PI t h s Hs).
      - intros h r s HQ HI Hno. exact (counter_ret t h r s HQ HI Hno).
      - intros h. exact (counter_derivation t h).
    Qed.

    Theorem counter_methodsem t : MethodSem Ic Rc Gc Mc t Inc.
    Proof. eapply method_sound. exact (counter_provable t). Qed.

    Lemma counter_init : Ic (σ0, COk σ0 [], []).
    Proof.
      exists 0, (fun _ => None), []. cbn. split; [reflexivity |]. split; [reflexivity |].
      split; [constructor |]. split; [reflexivity | constructor].
    Qed.

    (** ** Regression: the iteration-1 triple has no model (latest-review B-5)

        Verbatim from the Appendix of the iteration-1 review, with the
        triple qualified as [Iter1]. *)

    Lemma inc_trace : exists tr, program_produces_tagged t0 (Mc Inc t0) tr 0 /\
      map untag tr = [Build_ThreadEvent t0 (@InvEv USig 0 FAA); Build_ThreadEvent t0 (@ResEv USig 0 FAA 0)].
    Proof.
      eexists. split.
      - eexists. split.
        + cbn. eapply tagged_execution_emit.
          { apply tagged_future with (h := 0). unfold handle_fresh. cbn. tauto. }
          eapply tagged_execution_emit.
          { apply (@tagged_wait_pending USig nat t0 FAA 0 0). apply resolve_here. }
          apply tagged_execution_refl.
        + apply program_terminal_ret. repeat constructor.
      - reflexivity.
    Qed.

    Definition key1 : CallKey OSig := (t0, 1).
    Definition key0 : CallKey OSig := (t0, 0).

    Definition lin_ok (s : LinState OSig) : Prop :=
      match s with ls_linr op r => match op return o_ar op -> Prop with Inc => fun r => 1 <= r end r | _ => True end.

    Definition Inv (p : Poss CVF) : Prop :=
      exists c rec s1 s0, p = @PossOk OSig CVF (c, rec) [make_lin_entry key1 s1; make_lin_entry key0 s0] /\
       (s0 <> @ls_inv OSig Inc -> 1 <= c) /\
       (s1 <> @ls_inv OSig Inc -> exists r, rec 1 = Some r /\ 1 <= r) /\ lin_ok s1.

    Lemma inv_step_at owner p p' : poss_step_at CVF owner p p' -> Inv p -> Inv p'.
    Proof.
      intros Hst. destruct Hst as [t h op st st' pool pool' Hlin Hlts | t h op ret st st' pool pool' Hlin Hlts | t h op st pool Hlin Herr | t h op ret st pool Hlin Herr];
        intros (c & rec & s1 & s0 & Heq & H0 & H1 & Hok); injection Heq as Hst Hpool; subst.
      - unfold make_lin_entry, key1, key0 in Hlin. cbn in Hlin.
        inversion Hlin as [older Hready Heq1 Heq2 | entry pool0 pool0' Hneq Hupd Heq1 Heq2]; subst.
        + destruct op. inversion Hready as [| ? ? Hal _]; subst. cbn in Hal.
          cbn in Hlts. subst st'.
          assert (Hc : 1 <= c).
          { apply H0. intros ->. destruct Hal as [Hal | Hal]; [apply Hal; reflexivity | exact Hal]. }
          exists (S c), (rupd rec 1 c), (@ls_lini OSig Inc), s0. split; [reflexivity |].
          split; [intros _; lia |]. split; [intros _; exists c; cbn; split; [reflexivity | exact Hc] | exact Logic.I].
        + inversion Hupd as [older Hready Heq1' Heq2' | entry' pool1 pool1' Hneq' Hupd' Heq1' Heq2']; subst.
          * destruct op. cbn in Hlts. subst st'.
            exists (S c), (rupd rec 0 c), s1, (@ls_lini OSig Inc). split; [reflexivity |].
            split; [intros _; lia |]. split; [| exact Hok].
            intros Hs1. destruct (H1 Hs1) as (r & Hr & Hr1). exists r. cbn. split; [exact Hr | exact Hr1].
          * inversion Hupd'.
      - unfold make_lin_entry, key1, key0 in Hlin. cbn in Hlin.
        inversion Hlin as [tail Heq1 Heq2 | entry pool0 pool0' Hneq Hupd Heq1 Heq2]; subst.
        + destruct op. cbn in Hlts. destruct Hlts as [Hr ->].
          exists c, rec, (@ls_linr OSig Inc ret), s0. split; [reflexivity |].
          split; [exact H0 |]. destruct (H1 ltac:(discriminate)) as (r & Hr' & Hr1).
          split; [intros _; exists r; split; assumption |]. cbn. rewrite Hr' in Hr. injection Hr as <-. exact Hr1.
        + inversion Hupd as [tail Heq1' Heq2' | entry' pool1 pool1' Hneq' Hupd' Heq1' Heq2']; subst.
          * destruct op. cbn in Hlts. destruct Hlts as [_ ->].
            exists c, rec, s1, (@ls_linr OSig Inc ret). split; [reflexivity |].
            split; [intros _; apply H0; discriminate |]. split; assumption.
          * inversion Hupd'.
      - destruct Herr.
      - destruct Herr.
    Qed.

    Lemma inv_steps p p' : poss_steps CVF p p' -> Inv p -> Inv p'.
    Proof.
      intros Hs. induction Hs as [p p' (o & Hs) | p | p p1 p' Hs1 IH1 Hs2 IH2]; intros HI; eauto.
      eapply inv_step_at; eauto.
    Qed.

    Theorem counter_methodsem_unsat (I : Iter1.Assn CVE CVF) (R G : CallKey OSig -> Iter1.PRel CVE CVF) :
      I (σ0, @PossOk OSig CVF σ0 []) -> Iter1.MethodSem I R G Mc t0 Inc -> False.
    Proof.
      intros HI0 Hsem.
      destruct inc_trace as (tr & Hprod & Htr).
      destruct (Hsem 0 tr 0 Hprod) as (A0 & _ & Hinit0).
      destruct (Hinit0 σ0 (@PossOk OSig CVF σ0 []) (@PossOk OSig CVF σ0 [make_lin_entry key0 (@ls_inv OSig Inc)]) HI0) as [HI1 _].
      { constructor. constructor. intros []. }
      destruct (Hsem 1 tr 0 Hprod) as (A & [Hemit Hstab Hret] & Hinit).
      destruct (Hinit σ0 _ (@PossOk OSig CVF σ0 [make_lin_entry key1 (@ls_inv OSig Inc); make_lin_entry key0 (@ls_inv OSig Inc)]) HI1) as [HI2 HA].
      { constructor. constructor. intros [H | []]. discriminate H. }
      destruct tr as [| m1 [| m2 [| m3 tr]]]; try discriminate. cbn in Htr. injection Htr as H1 H2.
      set (σ1 := (S (fst σ0), rupd (snd σ0) 0 (fst σ0)) : CState).
      destruct (Hemit [] m1 [m2] ltac:(constructor) σ0 _ HA HI2 σ1) as (p1 & Hps1 & HA1 & HI1' & _).
      { rewrite H1. reflexivity. }
      destruct (Hemit [] m2 [] ltac:(constructor) σ1 p1 HA1 HI1' σ1) as (p2 & Hps2 & HA2 & HI2' & _).
      { rewrite H2. cbn. split; reflexivity. }
      destruct (Hret _ HA2 HI2') as (p3 & Hps3 & (v & pool & Hp3 & Hlk) & _).
      assert (Hinv : Inv (@PossOk OSig CVF σ0 [make_lin_entry key1 (@ls_inv OSig Inc); make_lin_entry key0 (@ls_inv OSig Inc)])).
      { exists 0, (fun _ => None), (@ls_inv OSig Inc), (@ls_inv OSig Inc). split; [reflexivity|]. split; [intros H; congruence|]. split; [intros H; congruence | exact Logic.I]. }
      pose proof (inv_steps _ _ (rt_trans _ _ _ _ _ Hps1 (rt_trans _ _ _ _ _ Hps2 Hps3)) Hinv) as (c & rec & s1 & s0 & Heq & _ & _ & Hok).
      subst p3. injection Heq as _ Hpool. subst pool.
      unfold lin_lookup in Hlk.
      destruct Hlk as [Hl | [Hl | []]]; unfold make_lin_entry, key1, key0 in Hl; cbn in Hl.
      - injection Hl as Hs1. subst s1. cbn in Hok. lia.
      - discriminate Hl.
    Qed.

    (** The schedule of the B-5 counterexample is excluded by the ghost:
        with the pending FAA invocations of [key0] (older, underlay handle
        [0]) and [key1] (underlay handle [1]; distinct handles, as
        [trace_fresh] makes reachable, latest-review m-18) in the ghost, the
        FAA of [key1] has no ghost transition. *)
    Lemma counter_b5_excluded γ' :
      ~ ghost_emit key1 (Build_ThreadEvent t0 (@InvEv USig 1 FAA))
          [Build_ScheduledEvent key0 (Build_ThreadEvent t0 (@InvEv USig 0 FAA));
           Build_ScheduledEvent key1 (Build_ThreadEvent t0 (@InvEv USig 1 FAA))] γ'.
    Proof.
      cbn. intros (g1 & g2 & Hg & _ & Hnb).
      destruct g1 as [| x [| y g1]]; cbn in Hg.
      - discriminate Hg.
      - injection Hg as <- _. inversion Hnb as [| ? ? Hx _]; subst. apply Hx. split; [reflexivity |]. cbn. intros [].
      - injection Hg as _ _ Hg. destruct g1; discriminate Hg.
    Qed.

    (** B-5, both halves: the iteration-1 triple has no model for the
        counter; the redesigned triple holds, with an invariant that is true
        initially. *)
    Theorem counter_b5 :
      (forall (I : Iter1.Assn CVE CVF) R G, I (σ0, @PossOk OSig CVF σ0 []) -> ~ Iter1.MethodSem I R G Mc t0 Inc) /\
      (Ic (σ0, COk σ0 [], []) /\ forall t, MethodSem Ic Rc Gc Mc t Inc).
    Proof.
      split; [intros I R G HI Hsem; exact (counter_methodsem_unsat I R G HI Hsem) |].
      split; [exact counter_init | exact counter_methodsem].
    Qed.

  End Counter.

  (** ** M-16: the overlapping counter over a handle-linear underlay

      The author's decision on latest-review M-16 (research-intent §8):
      the underlay presentation is handle-linear
      ([RelaxedHoareBase.HandleLinear]); the triple and the proof state
      are unchanged.  The counter of [Counter] is redone with
      - underlay records keyed by the underlay key [(thread, handle)];
      - the specification [CVFe := EI cδ] built by
        [RelaxedHoareSpec.EI] from the sequential counter [cδ] (effect at
        the abstract invocation, latest-review M-17), so that
        [counter_spec_hvf] discharges [HVF] of [gsim_rel_lin] for it.
      Two underlays share the counter's FAA: [HVE] (an invocation is
      enabled only on an unused key; handle-linear, [HVE_handle_linear])
      and [OVE] (the invocation overwrites the record; not handle-linear,
      [OVE_not_handle_linear]).

      - [counter_ow_unsat]: over [OVE], [RLHL2Hyps] has no model, for any
        [I], [R], [G], initial underlay state and initial counter value
        (the reviewers' scratch counterexample of iteration 2, in the
        repository).  The schedule: [key0]'s FAA on underlay key
        [(t0, 0)]; [key1] of the same thread is invoked with a trace that
        reuses [(t0, 0)] (the triple quantifies over it, the module's
        [trace_fresh] would exclude it); [key1]'s FAA overwrites the record
        (a step of [G key1], hence of [R key0]); [key0] reads [key1]'s
        value, but [invocation_ready] forces [key0]'s abstract [Inc]
        first.
      - [counter_hl_rlhl2]: over [HVE], every field of [RLHL2Hyps] holds
        for [Ih], [Rh], [Gh].  [Ih] reads the ghost (per thread, the
        [ls_inv] calls are the owners of the pending FAA invocations, as
        in [Counter.Ic]).  [Gh k] constrains memory: per-key records only
        grow, and the pool entries and pending abstract results of every
        other call are kept; [Rh k] keeps the records and [k]'s own pool
        entries and pending results.  Both are robust to the reuse of an
        overlay key after its return (the triple only requires
        [lin_fresh]): pending results belong to [ls_lini] calls ([Ih]),
        and a returned key has none.  Handle-linearity enters at one
        place, [faa_updateh]: the FAA's underlay step requires an unused
        key, which is what makes "records only grow" a guarantee.  With
        [OVE] instead, [Gh] would have to allow overwriting, and the
        assertion [KLinih] of another call would not be stable. *)

  Module CounterHL.
    Import Counter.

    Definition KRec : Type := tid -> nat -> option nat.

    Definition kupd (rec : KRec) (t : tid) (h v : nat) : KRec :=
      fun t' h' => if andb (Pos.eqb t t') (Nat.eqb h h') then Some v else rec t' h'.

    Definition HState : Type := (nat * KRec)%type.

    Definition hσ0 : HState := (0, fun _ _ => None).

    (** Handle-linear: an FAA invocation is enabled only on an unused
        underlay key. *)
    Definition hl_step (ev : ThreadEvent USig) (s s' : HState) : Prop :=
      match te_ev _ ev with
      | InvEv h _ => snd s (te_tid _ ev) h = None /\
                     s' = (S (fst s), kupd (snd s) (te_tid _ ev) h (fst s))
      | ResEv h op r => match op return u_ar op -> Prop with
                        | FAA => fun r => snd s (te_tid _ ev) h = Some r /\ s' = s end r
      end.

    Definition HVE : LTS USig := {| State := HState; Step := hl_step; Error := NoError |}.

    (** Overwriting: the same LTS without the freshness check. *)
    Definition ow_step (ev : ThreadEvent USig) (s s' : HState) : Prop :=
      match te_ev _ ev with
      | InvEv h _ => s' = (S (fst s), kupd (snd s) (te_tid _ ev) h (fst s))
      | ResEv h op r => match op return u_ar op -> Prop with
                        | FAA => fun r => snd s (te_tid _ ev) h = Some r /\ s' = s end r
      end.

    Definition OVE : LTS USig := {| State := HState; Step := ow_step; Error := NoError |}.

    Definition hused (s : HState) (k : CallKey USig) : Prop := snd s (fst k) (snd k) <> None.

    Lemma kupd_same rec t h v : kupd rec t h v t h = Some v.
    Proof. unfold kupd. rewrite Pos.eqb_refl, Nat.eqb_refl. reflexivity. Qed.

    Lemma kupd_grow rec t h v t' h' c :
      rec t h = None -> rec t' h' = Some c -> kupd rec t h v t' h' = Some c.
    Proof.
      intros Hn Hs. unfold kupd.
      destruct (Pos.eqb_spec t t') as [<- | _]; destruct (Nat.eqb_spec h h') as [<- | _]; cbn; try exact Hs.
      rewrite Hn in Hs. discriminate.
    Qed.

    Theorem HVE_handle_linear : HandleLinear HVE hused.
    Proof.
      constructor.
      - intros t h op σ σ' [_ ->]. unfold hused. cbn. rewrite kupd_same. discriminate.
      - intros [t [h op | h op r]] σ σ' [t' h'] Hs Hu; unfold hused in *; cbn in *.
        + destruct Hs as [Hn ->]. cbn. destruct (snd σ t' h') as [c |] eqn:Hc; [| contradiction Hu; reflexivity].
          rewrite (kupd_grow _ _ _ _ _ _ c Hn Hc). discriminate.
        + destruct op. destruct Hs as [_ ->]. exact Hu.
      - intros t h op σ σ' [Hn _] Hu. apply Hu. exact Hn.
    Qed.

    Theorem OVE_not_handle_linear used : ~ HandleLinear OVE used.
    Proof.
      intros Hhl.
      assert (H1 : Step OVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) hσ0 (1, kupd (snd hσ0) t0 0 0))
        by reflexivity.
      assert (H2 : Step OVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) (1, kupd (snd hσ0) t0 0 0)
                     (2, kupd (kupd (snd hσ0) t0 0 0) t0 0 1)) by reflexivity.
      exact (hl_fresh _ _ Hhl t0 0 FAA _ _ H2 (hl_inv_used _ _ Hhl t0 0 FAA _ _ H1)).
    Qed.

    (** The sequential counter: [Inc] returns the value and increments. *)
    Definition cδ (n : nat) (o : Sig.op (RelaxedSig.effect OSig)) : Sig.ar o -> nat -> Prop :=
      match o as o0 return Sig.ar o0 -> nat -> Prop with Inc => fun r n' => r = n /\ n' = S n end.

    Definition CVFe : LTS OSig := RelaxedHoareSpec.EI cδ.

    (** M-17: [HVF] of [gsim_rel_lin] holds for this specification. *)
    Corollary counter_spec_hvf :
      forall T v, RelaxedGSim.vf_path CVFe (0, []) T v -> PrefixView.wf T -> PrefixView.complete T ->
        RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) T (RelaxedSig.semi_independent OSig)
          (RelaxedHoareSpec.seq_legal cδ 0).
    Proof. exact (RelaxedHoareSpec.ei_hvf cδ 0). Qed.

    Abbreviation EOk v pool := (@PossOk OSig CVFe v pool).
    Abbreviation COp := (RelaxedTraceLin.Op OSig).
    Abbreviation cop k r := (@RelaxedTraceLin.Build_Op OSig k Inc r).
    Abbreviation okey := (@RelaxedTraceLin.op_key OSig).
    Abbreviation HA := (Assn HVE CVFe).

    Lemma pinv_inv {F : RelaxedSig.t} {VF : LTS F} t h op v pool p' :
      poss_invoke VF t h op (PossOk v pool) p' ->
      p' = PossOk v (make_lin_entry (t, h) (ls_inv op) :: pool) /\ lin_fresh (t, h) pool.
    Proof. intros Hi. inversion Hi as [v0 pool0 pool' Hins]; subst. inversion Hins; subst. auto. Qed.

    Lemma pret_inv {F : RelaxedSig.t} {VF : LTS F} t h op r v pool p' :
      poss_return VF t h op r (PossOk v pool) p' ->
      exists pool', p' = PossOk v pool' /\ lin_remove (t, h) (ls_linr op r) pool pool'.
    Proof. intros Hr. inversion Hr; subst. eauto. Qed.

    Lemma lookup_unique (pool : LinPool OSig) k ls1 ls2 :
      lin_pool_well_formed pool -> lin_lookup k ls1 pool -> lin_lookup k ls2 pool -> ls1 = ls2.
    Proof.
      intros Hwf H1 H2.
      assert (Hk : lin_key (make_lin_entry k ls1) = lin_key (make_lin_entry k ls2))
        by (rewrite !lin_key_make_lin_entry; reflexivity).
      pose proof (nodup_map_in_inj lin_key pool _ _ Hwf H1 H2 Hk) as Heq.
      apply (f_equal (lin_state OSig)) in Heq. exact Heq.
    Qed.

    (** The invariant: [Counter.Ic], plus the pending abstract results of
        [CVFe]: they belong to [ls_lini] calls, one per call. *)
    Definition Ih : HA := fun s => exists ca P pool,
      ps_poss s = EOk (ca, P) pool /\ fst (ps_mem s) = ca /\ lin_pool_well_formed pool /\
      (forall t', inv_keys t' pool = gkeys t' (ps_ghost s)) /\ Forall Jwf (ps_ghost s) /\
      (forall o, In o P -> lin_lookup (okey o) (@ls_lini OSig Inc) pool) /\
      NoDup (map okey P).

    Definition grow (σ σ' : HState) : Prop :=
      forall t h c, snd σ t h = Some c -> snd σ' t h = Some c.

    (** Rely of [k]: records only grow; [k]'s pool entries and pending
        results are kept. *)
    Definition Rh (k : CallKey OSig) : PRel HVE CVFe := fun s s' =>
      grow (ps_mem s) (ps_mem s') /\
      exists v pool v' pool', ps_poss s = EOk v pool /\ ps_poss s' = EOk v' pool' /\
        (forall ls, lin_lookup k ls pool -> lin_lookup k ls pool') /\
        (forall o, okey o = k -> In o (snd v) -> In o (snd v')).

    (** Guarantee of [k]: records only grow; the pool entries and pending
        results of every other call are kept. *)
    Definition Gh (k : CallKey OSig) : PRel HVE CVFe := fun s s' =>
      grow (ps_mem s) (ps_mem s') /\
      exists v pool v' pool', ps_poss s = EOk v pool /\ ps_poss s' = EOk v' pool' /\
        (forall k' ls, k' <> k -> lin_lookup k' ls pool -> lin_lookup k' ls pool') /\
        (forall o, okey o <> k -> In o (snd v) -> In o (snd v')).

    Lemma Gh_in_Rh k k' s s' : k' <> k -> Gh k' s s' -> Rh k s s'.
    Proof.
      intros Hne (Hg & v & pool & v' & pool' & Hp & Hp' & Hlk & HP). split; [exact Hg |].
      exists v, pool, v', pool'. split; [exact Hp |]. split; [exact Hp' |]. split.
      - intros ls Hl. apply Hlk; [intros Heq; apply Hne; symmetry; exact Heq | exact Hl].
      - intros o Hk. apply HP. rewrite Hk. intros Heq. apply Hne. symmetry. exact Heq.
    Qed.

    Definition KInvh (k : CallKey OSig) : HA := fun s =>
      exists v pool, ps_poss s = EOk v pool /\ lin_lookup k (@ls_inv OSig Inc) pool.

    (** After the FAA of [k] on underlay handle [hu]: the record of
        [(fst k, hu)] holds the fetched value, which is [k]'s pending
        abstract result, and [k] is at [ls_lini]. *)
    Definition KLinih (k : CallKey OSig) (hu : nat) : HA := fun s =>
      exists c v pool, ps_poss s = EOk v pool /\ snd (ps_mem s) (fst k) hu = Some c /\
        In (cop k c) (snd v) /\ lin_lookup k (@ls_lini OSig Inc) pool.

    Definition KLinrh (k : CallKey OSig) (r : nat) : HA := fun s =>
      exists v pool, ps_poss s = EOk v pool /\ lin_lookup k (@ls_linr OSig Inc r) pool.

    Lemma KInvh_stable k : Stable Ih (Rh k) (KInvh k).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Lemma KLinih_stable k hu : Stable Ih (Rh k) (KLinih k hu).
    Proof.
      intros s s' (c & v & pool & Hp & Hc & HP & Hl) (Hg & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & HPk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists c, v1', pool1'.
      split; [exact Hp1' |]. split; [apply Hg; exact Hc |].
      split; [apply HPk; [reflexivity | exact HP] | apply Hlk; exact Hl].
    Qed.

    Lemma KLinrh_stable k r : Stable Ih (Rh k) (KLinrh k r).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Section CounterHLProof.
      Context (t : tid) (h : nat).
      Local Abbreviation kc := (@pair tid (RelaxedSig.handle OSig) t h).

      Abbreviation Pch := (PostInvoke Ih kc Inc (Ωc t)).

      Lemma pinit_KInvh : Impl Ih Pch (KInvh kc).
      Proof.
        intros [[σ p] γ] _ (p0 & γ0 & evs & (ca & P & pool0 & Hp0 & _) & Hinv & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, Hinv. rewrite Hp0 in Hinv.
        destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> _].
        exists (ca, P), (make_lin_entry kc (@ls_inv OSig Inc) :: pool0). split; [reflexivity | left; reflexivity].
      Qed.

      (** The FAA: by the ghost frontier and [Ih], [kc] is the oldest
          [ls_inv] call of its thread, so its abstract invocation is
          enabled; the underlay step is enabled only on an unused key
          (handle-linearity), so the record grows. *)
      Lemma faa_updateh hu :
        EvUpdate Ih (Gh kc) kc (Build_ThreadEvent t (@InvEv USig hu FAA)) (KInvh kc) (KLinih kc hu).
      Proof.
        intros σ p γ γ' (v & pool & Hp & Hl) (ca & P & pool1 & Hp1 & Hc & Hwf & HJ & HJwf & HPl & HPnd) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        cbn in Hge. destruct Hge as (g1 & g2 & -> & -> & Hnb).
        cbn in Hstep. destruct Hstep as [Hnone ->].
        apply Forall_app in HJwf as [HJwf1 HJwf2]. pose proof (Forall_inv_tail HJwf2) as HJwf2'.
        destruct (emit_ready t h hu pool g1 g2 Hwf Hl HJ HJwf1 Hnb) as (pool' & Hu & Hwf' & HJ').
        pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu'.
        assert (HPk : forall o, In o P -> okey o <> kc).
        { intros o Ho Hk. pose proof (HPl o Ho) as Hlo. rewrite Hk in Hlo.
          pose proof (lookup_unique pool kc _ _ Hwf Hl Hlo) as Heq. discriminate Heq. }
        exists (EOk (S ca, cop kc ca :: P) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_inv CVFe t h Inc); [exact Hu |].
          cbn. exists ca, (S ca). split; [split; reflexivity | reflexivity].
        - exists ca, (S ca, cop kc ca :: P), pool'. cbn. split; [reflexivity |].
          rewrite Hc. split; [apply kupd_same |]. split; [left; reflexivity |].
          exact (lin_update_target _ _ _ _ _ Hu').
        - exists (S ca), (cop kc ca :: P), pool'. cbn. rewrite Hc.
          split; [reflexivity |]. split; [reflexivity |]. split; [exact Hwf' |].
          split; [exact HJ' |]. split; [apply Forall_app; split; assumption |]. split.
          + intros o [<- | Ho]; [exact (lin_update_target _ _ _ _ _ Hu') |].
            eapply lin_update_other_lookup; [exact Hu' | exact (HPk o Ho) | exact (HPl o Ho)].
          + constructor; [| exact HPnd]. intros Hin. apply in_map_iff in Hin as (o & Hk & Ho). exact (HPk o Ho Hk).
        - split.
          + intros t' h' c Hs. cbn. exact (kupd_grow _ _ _ _ _ _ c Hnone Hs).
          + exists (ca, P), pool, (S ca, cop kc ca :: P), pool'. split; [reflexivity |]. split; [reflexivity |].
            split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu' | exact Hne | exact Hlk] |].
            intros o _ Ho. right. exact Ho.
      Qed.

      Lemma res_updateh hu r :
        EvUpdate Ih (Gh kc) kc (Build_ThreadEvent t (@ResEv USig hu FAA r)) (KLinih kc hu) (KLinrh kc r).
      Proof.
        intros σ p γ γ' (c & v & pool & Hp & Hc & HP & Hl) (ca & P & pool1 & Hp1 & Hca & Hwf & HJ & HJwf & HPl & HPnd) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hge. subst γ'.
        cbn in Hstep. destruct Hstep as [Hr ->]. rewrite Hc in Hr. injection Hr as <-.
        rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        cbn in HP. destruct (in_split _ _ HP) as (P1 & P2 & HPs).
        destruct (lin_update_exists kc (@ls_lini OSig Inc) (@ls_linr OSig Inc c) pool Hwf Hl) as (pool' & Hu).
        assert (HPk : forall o, In o (P1 ++ P2) -> okey o <> kc).
        { intros o Ho Hk. rewrite HPs, map_app in HPnd. cbn [map] in HPnd.
          apply NoDup_remove_2 in HPnd. apply HPnd. rewrite <- map_app.
          apply in_map_iff. exists o. split; [exact Hk | exact Ho]. }
        assert (HPsub : forall o, In o (P1 ++ P2) -> In o P).
        { intros o Ho. rewrite HPs. apply in_app_or in Ho. apply in_or_app. destruct Ho; [left | right; right]; assumption. }
        exists (EOk (ca, P1 ++ P2) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_ret CVFe t h Inc c _ _ _ _ Hu). cbn. exists P1, P2.
          split; [exact HPs | reflexivity].
        - exists (ca, P1 ++ P2), pool'. split; [reflexivity | eapply lin_update_target; exact Hu].
        - exists ca, (P1 ++ P2), pool'. cbn. split; [reflexivity |]. split; [exact Hca |].
          split; [eapply lin_update_well_formed; eauto |].
          split; [intros t'; rewrite (inv_keys_update _ _ _ _ t' Hu); apply HJ |].
          split; [exact HJwf |]. split.
          + intros o Ho. eapply lin_update_other_lookup; [exact Hu | exact (HPk o Ho) | exact (HPl o (HPsub o Ho))].
          + rewrite HPs, map_app in HPnd. cbn [map] in HPnd. rewrite map_app. exact (NoDup_remove_1 _ _ _ HPnd).
        - split.
          + intros t' h' c' Hs. exact Hs.
          + exists (ca, P), pool, (ca, P1 ++ P2), pool'. split; [reflexivity |]. split; [reflexivity |].
            split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu | exact Hne | exact Hlk] |].
            intros o Hk Ho. cbn in Ho |- *. rewrite HPs in Ho. apply in_app_or in Ho. apply in_or_app.
            destruct Ho as [Ho | [<- | Ho]]; [left; exact Ho | contradiction Hk; reflexivity | right; exact Ho].
      Qed.

      Definition sl_faah (hu : nat) : Slot HVE CVFe :=
        mkSlot (inv_tev (E := USig) (F := OSig) kc empty_store hu FAA) (KInvh kc) (fun _ _ => True)
          (KLinih kc hu) (Gh kc).

      Definition sl_resh (hu : nat) (r : nat) : Slot HVE CVFe :=
        mkSlot (res_tev (E := USig) (F := OSig) kc hu FAA r) (fun _ => True) (fun _ => KLinih kc hu)
          (KLinrh kc r) (Gh kc).

      Lemma counter_derivationh :
        RProvable Ih Rh Gh kc Pch
          (fun a Γ H => Close Ih Rh Gh kc Pch (KLinrh kc) a Γ H /\ Ωc t (own_invs Γ)) [] empty_store (Mc Inc t).
      Proof.
        cbn. unfold body.
        apply rp_future with (sl := sl_faah); [intros; reflexivity | |].
        { intros hu _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faah].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faah].
            intros σ p γ γ' [HK _]. apply (faa_updateh hu σ p γ γ' HK).
          - exact pinit_KInvh.
          - intros d sd _ Hd. destruct d; discriminate.
          - apply KInvh_stable.
          - intros d _. apply Stable_true.
          - intros g sg Hg. destruct g; discriminate.
          - intros d g sg _ Hg. destruct g; discriminate.
          - intros y sy Hy. destruct y; discriminate.
          - intros y sy d Hy. destruct y; discriminate. }
        intros hu Hf. cbv beta.
        apply rp_wait_pending with (sl := sl_resh hu); [left; reflexivity | intros; reflexivity | |].
        { intros r. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_resh].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_resh].
            intros σ p γ γ' [_ Hin]. apply (res_updateh hu r σ p γ γ'). apply (Hin 0).
            exact (dprec_faa_res t h hu r).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [|]]; try discriminate.
            cbn in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
          - apply Stable_true.
          - intros d _. apply KLinih_stable.
          - intros g sg _. apply Stable_true.
          - intros d g sg Hd Hg Hnb. exfalso. apply dprec_lt in Hd. cbn in Hd.
            destruct g as [| g]; [| destruct g; discriminate]. assert (d = 0) by lia. subst d.
            apply Hnb. apply before_refl.
          - intros y sy Hy Hnb. exfalso. destruct y as [| y]; [| destruct y; discriminate].
            apply Hnb. apply before_dprec. exact (dprec_faa_res t h hu r).
          - intros y sy d Hy _ Hd. exfalso. apply dprec_lt in Hd. destruct y as [| y]; [lia |].
            destruct y; discriminate. }
        intros r H2 Hres. cbv beta. apply rp_ret. split.
        - apply close_done with
            (fin := fun d => match d with 1 => KLinrh kc r | _ => fun _ => True end)
            (fin0 := fun _ => True).
          + eapply resolve_fresh_all_resolved; [constructor | exact Hres].
          + constructor.
            * intros d sd Hd. destruct d as [| [| d]]; cbn in Hd; try (destruct d; discriminate).
              -- intros s _ _. exact Logic.I.
              -- injection Hd as <-. intros s _ Hs. exact Hs.
            * intros s _ _. exact Logic.I.
            * intros d g sg Hd Hg Hnb. destruct d as [| [| d]]; [apply Stable_true | | cbn in Hd; lia].
              exfalso. apply Hnb. destruct g as [| [| g]]; [| apply before_refl | destruct g; discriminate].
              apply before_dprec. exact (dprec_faa_res t h hu r).
            * intros g sg _. apply Stable_true.
            * intros [| [| d]]; [apply Stable_true | apply KLinrh_stable | apply Stable_true].
            * apply Stable_true.
            * intros s _ _ Hfin. exact (Hfin 1 _ eq_refl Logic.I).
        - exists hu. reflexivity.
      Qed.

      Lemma counter_PIh : forall s, Pch s -> Ih s.
      Proof.
        intros [[σ p] γ] (p0 & γ0 & evs & (ca & P & pool0 & Hp0 & Hc & Hwf & HJ & HJwf & HPl & HPnd) & Hinv & Hg & (hu & ->) & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst γ. rewrite Hp0 in Hinv.
        destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> Hfresh].
        exists ca, P, (make_lin_entry kc (@ls_inv OSig Inc) :: pool0). split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_insert_well_formed; [constructor; exact Hfresh | exact Hwf] |]. split.
        - intros t'. cbn [ps_ghost snd inv_keys]. rewrite HJ, gkeys_app. f_equal.
          unfold ek, gkeys. cbn. destruct (Pos.eqb t t'); reflexivity.
        - split; [apply Forall_app; split; [exact HJwf | constructor; [split; [reflexivity | exact Logic.I] | constructor]] |].
          split; [| exact HPnd]. intros o Ho. right. exact (HPl o Ho).
      Qed.

      Lemma counter_reth r s : KLinrh kc r s -> Ih s -> NoOwn kc (ps_ghost s) -> RetCond Ih Gh kc Inc r s.
      Proof.
        intros (v & pool & Hp & Hl) HI _. destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        subst p. exists (EOk v pool). split; [apply rt_refl |]. split; [exists v, pool; split; [reflexivity | exact Hl] |].
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hret. destruct (pret_inv _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        destruct HI as (ca & P & pool3 & Hp3 & Hc & Hwf & HJ & HJwf & HPl & HPnd). cbn in Hp3.
        injection Hp3 as Hv Hpool. subst v pool3.
        exists ca, P, pool2. cbn. split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_remove_well_formed; eauto |].
        split; [intros t'; rewrite (inv_keys_remove _ _ _ _ t' Hrem); apply HJ |].
        split; [exact HJwf |]. split; [| exact HPnd].
        intros o Ho. eapply lin_remove_other_lookup; [exact Hrem | | exact (HPl o Ho)].
        intros Hk. pose proof (HPl o Ho) as Hlo. rewrite Hk in Hlo.
        pose proof (lookup_unique pool kc _ _ Hwf Hl Hlo) as Heq. discriminate Heq.
      Qed.
    End CounterHLProof.

    Theorem counter_hl_provable t :
      MethodProvable Ih Rh Gh Mc t Inc (fun _ => Ωc t) (fun h => KLinrh (t, h)).
    Proof.
      constructor.
      - intros h s Hs. exact (counter_PIh t h s Hs).
      - intros h r s HQ HI Hno. exact (counter_reth t h r s HQ HI Hno).
      - intros h. exact (counter_derivationh t h).
    Qed.

    Theorem counter_hl_methodsem t : MethodSem Ih Rh Gh Mc t Inc.
    Proof. eapply method_sound. exact (counter_hl_provable t). Qed.

    Lemma counter_hl_init : Ih (hσ0, EOk (0, []) [], []).
    Proof.
      exists 0, [], []. cbn. split; [reflexivity |]. split; [reflexivity |].
      split; [constructor |]. split; [reflexivity |]. split; [constructor |].
      split; [intros o [] | constructor].
    Qed.

    (** M-16 acceptance (ii): every field of [RLHL2Hyps] holds for the
        overlapping counter over the handle-linear underlay [HVE]. *)
    Theorem counter_hl_rlhl2 : RLHL2Hyps Ih Rh Gh Mc hσ0 (0, []).
    Proof.
      constructor.
      - intros t []. exact (counter_hl_methodsem t).
      - intros k k' s s' Hne HG. exact (Gh_in_Rh k' k s s' Hne HG).
      - intros k k' op tr ret s p' Hne _ HI Hinv. destruct s as [[σ p] γ].
        destruct HI as (ca & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> _].
        split; [intros t' h' c Hs; exact Hs |].
        exists (ca, P), pool, (ca, P), (make_lin_entry (t, h) (ls_inv op) :: pool).
        split; [reflexivity |]. split; [reflexivity |]. split; [intros ls Hl; right; exact Hl | auto].
      - intros k k' op r s p2 Hne HI Hret _. destruct s as [[σ p] γ].
        destruct HI as (ca & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pret_inv _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        split; [intros t' h' c Hs; exact Hs |].
        exists (ca, P), pool, (ca, P), pool2. split; [reflexivity |]. split; [reflexivity |].
        split; [| auto]. intros ls Hl. eapply lin_remove_other_lookup; [exact Hrem | | exact Hl].
        intros Heq. apply Hne. symmetry. exact Heq.
      - intros s (ca & P & pool & Hp & _ & Hwf & _). exists (ca, P), pool. auto.
      - exact counter_hl_init.
    Qed.

    (** *** M-16 acceptance (i): over the overwriting underlay [OVE] there
        is no model *)

    Lemma inc_trace_gen t hu r : exists tr, program_produces_tagged t (Mc Inc t) tr r /\
      map untag tr = [Build_ThreadEvent t (@InvEv USig hu FAA); Build_ThreadEvent t (@ResEv USig hu FAA r)].
    Proof.
      eexists. split.
      - eexists. split.
        + cbn. eapply tagged_execution_emit.
          { apply tagged_future with (h := hu). unfold handle_fresh. cbn. tauto. }
          eapply tagged_execution_emit.
          { apply (@tagged_wait_pending USig nat t FAA hu r). apply resolve_here. }
          apply tagged_execution_refl.
        + apply program_terminal_ret. repeat constructor.
      - reflexivity.
    Qed.

    Definition op_nat (o : COp) : nat :=
      match RelaxedTraceLin.op_op o as op return o_ar op -> nat with Inc => fun r => r end
        (RelaxedTraceLin.op_ret o).

    Definition lin_okm (m0 : nat) (s : LinState OSig) : Prop :=
      match s with
      | ls_linr op r => match op return o_ar op -> Prop with Inc => fun r => r = m0 end r
      | _ => True
      end.

    (** The abstract possibilities of the counterexample: [key0], and
        possibly [key1] newer than it; while [key0] is at [ls_inv], [key1]
        is too and the counter is [m0]; every pending result of [key0] is
        [m0]. *)
    Definition Good (m0 : nat) (p : Poss CVFe) : Prop :=
      exists c P pre s0, p = EOk (c, P) (pre ++ [make_lin_entry key0 s0]) /\
        (pre = [] \/ exists s1, pre = [make_lin_entry key1 s1] /\
                                (s0 = @ls_inv OSig Inc -> s1 = @ls_inv OSig Inc)) /\
        (s0 = @ls_inv OSig Inc -> c = m0) /\
        (forall o, In o P -> okey o = key0 -> op_nat o = m0) /\
        lin_okm m0 s0.

    Lemma not_ready_inv s0 :
      @invocation_ready OSig t0 Inc [make_lin_entry key0 s0] -> s0 <> @ls_inv OSig Inc.
    Proof.
      intros Hr ->. inversion Hr as [| e es Hal _]; subst. unfold older_entry_allows_invocation in Hal.
      cbn in Hal. destruct Hal as [Hne | []]. apply Hne. reflexivity.
    Qed.

    Lemma liu_one {F : RelaxedSig.t} t h op (e : LinEntry F) pool' :
      lin_invoke_update t h op [e] pool' ->
      e = make_lin_entry (t, h) (ls_inv op) /\ pool' = [make_lin_entry (t, h) (ls_lini op)].
    Proof. intros H. inversion H as [older Hr | e0 p0 p0' Hne Hu]; subst; [auto | inversion Hu]. Qed.

    Lemma liu_two {F : RelaxedSig.t} t h op (e1 e2 : LinEntry F) pool' :
      lin_invoke_update t h op [e1; e2] pool' ->
      (e1 = make_lin_entry (t, h) (ls_inv op) /\ pool' = [make_lin_entry (t, h) (ls_lini op); e2] /\
       invocation_ready t op [e2]) \/
      (e2 = make_lin_entry (t, h) (ls_inv op) /\ pool' = [e1; make_lin_entry (t, h) (ls_lini op)]).
    Proof.
      intros H. inversion H as [older Hr | e0 p0 p0' Hne Hu]; subst; [left; auto |].
      right. destruct (liu_one _ _ _ _ _ Hu) as [-> ->]. auto.
    Qed.

    Lemma lu_one {F : RelaxedSig.t} k b a (e : LinEntry F) pool' :
      lin_update k b a [e] pool' -> e = make_lin_entry k b /\ pool' = [make_lin_entry k a].
    Proof. intros H. inversion H as [tail | e0 p0 p0' Hne Hu]; subst; [auto | inversion Hu]. Qed.

    Lemma lu_two {F : RelaxedSig.t} k b a (e1 e2 : LinEntry F) pool' :
      lin_update k b a [e1; e2] pool' ->
      (e1 = make_lin_entry k b /\ pool' = [make_lin_entry k a; e2]) \/
      (e2 = make_lin_entry k b /\ pool' = [e1; make_lin_entry k a]).
    Proof.
      intros H. inversion H as [tail | e0 p0 p0' Hne Hu]; subst; [left; auto |].
      right. destruct (lu_one _ _ _ _ _ Hu) as [-> ->]. auto.
    Qed.

    Lemma mle_inj (k k' : CallKey OSig) s s' :
      make_lin_entry k s = make_lin_entry k' s' -> k = k' /\ s = s'.
    Proof.
      intros H. split.
      - rewrite <- (lin_key_make_lin_entry k s), <- (lin_key_make_lin_entry k' s'). rewrite H. reflexivity.
      - apply (f_equal (lin_state OSig)) in H. exact H.
    Qed.

    Lemma good_step_at m0 owner p p' : poss_step_at CVFe owner p p' -> Good m0 p -> Good m0 p'.
    Proof.
      intros Hst (c & P & pre & s0 & Hp & Hpre & Hc & HP & Hok).
      destruct Hst as [t h op st st' pool pool' Hlin Hlts | t h op ret st st' pool pool' Hlin Hlts
                      | t h op st pool Hlin Herr | t h op ret st pool Hlin Herr];
        [| | destruct Herr | destruct Herr]; injection Hp as -> ->.
      - destruct op. cbn in Hlts. destruct Hlts as (r & st'' & [-> ->] & ->).
        destruct Hpre as [-> | (s1 & -> & Hs1)]; cbn [app] in Hlin.
        + destruct (liu_one _ _ _ _ _ Hlin) as [He ->]. apply mle_inj in He as [Hk ->].
          specialize (Hc eq_refl). subst c. injection Hk as <- <-.
          exists (S m0), (cop key0 m0 :: P), [], (@ls_lini OSig Inc). split; [reflexivity |].
          split; [left; reflexivity |]. split; [discriminate |]. split; [| exact Logic.I].
          intros o [<- | Ho] Hk; [reflexivity | exact (HP o Ho Hk)].
        + destruct (liu_two _ _ _ _ _ _ Hlin) as [(He & -> & Hready) | (He & ->)].
          * apply mle_inj in He as [Hk ->]. injection Hk as <- <-.
            pose proof (not_ready_inv s0 Hready) as Hs0.
            exists (S c), (cop key1 c :: P), [make_lin_entry key1 (@ls_lini OSig Inc)], s0.
            split; [reflexivity |]. split; [right; eexists; split; [reflexivity | intros H; contradiction] |].
            split; [intros H; contradiction |]. split; [| exact Hok].
            intros o [<- | Ho] Hk; [discriminate Hk | exact (HP o Ho Hk)].
          * apply mle_inj in He as [Hk ->]. injection Hk as <- <-.
            specialize (Hc eq_refl). subst c.
            exists (S m0), (cop key0 m0 :: P), [make_lin_entry key1 s1], (@ls_lini OSig Inc).
            split; [reflexivity |]. split; [right; exists s1; split; [reflexivity | discriminate] |].
            split; [discriminate |]. split; [| exact Logic.I].
            intros o [<- | Ho] Hk; [reflexivity | exact (HP o Ho Hk)].
      - cbn in Hlts. destruct Hlts as (P1 & P2 & HPs & ->).
        assert (HPsub : forall o, In o (P1 ++ P2) -> In o P).
        { intros o Ho. rewrite HPs. apply in_app_or in Ho. apply in_or_app. destruct Ho; [left | right; right]; assumption. }
        assert (HPo : In (RelaxedTraceLin.Build_Op (t, h) op ret) P) by (rewrite HPs; apply in_or_app; right; left; reflexivity).
        destruct Hpre as [-> | (s1 & -> & Hs1)]; cbn [app] in Hlin.
        + destruct (lu_one _ _ _ _ _ Hlin) as [He ->]. apply mle_inj in He as [Hk ->].
          exists c, (P1 ++ P2), [], (ls_linr op ret). split; [rewrite <- Hk; reflexivity |].
          split; [left; reflexivity |]. split; [discriminate |].
          split; [intros o Ho Hk'; exact (HP o (HPsub o Ho) Hk') |].
          destruct op. exact (HP _ HPo (eq_sym Hk)).
        + destruct (lu_two _ _ _ _ _ _ Hlin) as [(He & ->) | (He & ->)].
          * apply mle_inj in He as [Hk ->].
            exists c, (P1 ++ P2), [make_lin_entry key1 (ls_linr op ret)], s0.
            split; [rewrite <- Hk; reflexivity |].
            split; [right; eexists; split; [reflexivity | intros Hs0; specialize (Hs1 Hs0); discriminate Hs1] |].
            split; [exact Hc |]. split; [intros o Ho Hk'; exact (HP o (HPsub o Ho) Hk') | exact Hok].
          * apply mle_inj in He as [Hk ->].
            exists c, (P1 ++ P2), [make_lin_entry key1 s1], (ls_linr op ret). split; [rewrite <- Hk; reflexivity |].
            split; [right; exists s1; split; [reflexivity | discriminate] |]. split; [discriminate |].
            split; [intros o Ho Hk'; exact (HP o (HPsub o Ho) Hk') |].
            destruct op. exact (HP _ HPo (eq_sym Hk)).
    Qed.

    Lemma good_steps m0 p p' : poss_steps CVFe p p' -> Good m0 p -> Good m0 p'.
    Proof.
      intros Hs. induction Hs as [p p' (o & Hs) | p | p p1 p' Hs1 IH1 Hs2 IH2]; intros HG; eauto.
      eapply good_step_at; eauto.
    Qed.

    Lemma good_invoke1 m0 p p' : Good m0 p -> poss_invoke CVFe t0 1 Inc p p' -> Good m0 p'.
    Proof.
      intros (c & P & pre & s0 & -> & Hpre & Hc & HP & Hok) Hi.
      destruct (pinv_inv _ _ _ _ _ _ Hi) as [-> Hfresh].
      destruct Hpre as [-> | (s1 & -> & Hs1)].
      - exists c, P, [make_lin_entry key1 (@ls_inv OSig Inc)], s0. split; [reflexivity |].
        split; [right; eexists; split; [reflexivity | auto] |]. auto.
      - exfalso. apply Hfresh. left. reflexivity.
    Qed.

    Lemma good_linr m0 v pool r :
      Good m0 (EOk v pool) -> lin_lookup key0 (@ls_linr OSig Inc r) pool -> r = m0.
    Proof.
      intros (c & P & pre & s0 & Heq & Hpre & _ & _ & Hok) Hl. injection Heq as _ ->.
      unfold lin_lookup in Hl. apply in_app_or in Hl.
      destruct Hl as [Hl | [Hl | []]].
      - destruct Hpre as [-> | (s1 & -> & _)]; [destruct Hl |]. destruct Hl as [Hl | []].
        apply (f_equal (lin_handle OSig)) in Hl. discriminate Hl.
      - apply (f_equal (lin_state OSig)) in Hl. cbn in Hl. subst s0. exact Hok.
    Qed.

    (** The same obstruction over the effect-at-invocation LTS [EI uδ],
        which keeps a record per invocation: [CounterEI.counter_ei_unsat]
        (after [CounterRelLin], which defines [uδ]). *)
    Theorem counter_ow_unsat (I : Assn OVE CVFe) (R G : CallKey OSig -> PRel OVE CVFe) (q0 : HState) (m0 : nat) :
      ~ RLHL2Hyps I R G Mc q0 (m0, []).
    Proof.
      intros HH. destruct q0 as [n0 rec0].
      pose proof (h_sem _ _ _ _ _ _ HH) as Hsem.
      set (q1 := (S n0, kupd rec0 t0 0 n0) : HState).
      (* the first call [key0], up to its FAA *)
      assert (Hfirst : forall r : nat, exists A0 m2 p1,
        CallTriple I R G key0 Inc r A0 /\ untag m2 = Build_ThreadEvent t0 (@ResEv USig 0 FAA r) /\
        A0 [m2] (q1, p1, []) /\ I (q1, p1, []) /\ Good m0 p1 /\
        exists v pool, p1 = EOk v pool /\ lin_domain pool = [key0]).
      { intros r. destruct (inc_trace_gen t0 0 r) as (tr & Hprod & Htr).
        destruct (Hsem t0 Inc 0 tr r Hprod) as (A0 & Htri & Hinit0).
        set (p0 := EOk (m0, []) [make_lin_entry key0 (@ls_inv OSig Inc)]).
        assert (Hpi : poss_invoke CVFe t0 0 Inc (EOk (m0, []) []) p0) by (constructor; constructor; intros []).
        destruct (Hinit0 (n0, rec0) _ [] p0 (h_init _ _ _ _ _ _ HH) Hpi) as [HI0 HA0].
        destruct tr as [| m1 [| m2 [| m3 tr]]]; try discriminate. cbn in Htr. injection Htr as H1 H2.
        unfold ghost_new in HI0, HA0. cbn [app map] in HI0, HA0. rewrite H1, H2 in HI0, HA0.
        cbn [inv_events te_ev map] in HI0, HA0.
        pose proof Htri as [Hemit _ _].
        destruct (Hemit [] m1 [m2] ltac:(constructor) (n0, rec0) p0 _ [] ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA0 HI0 q1 ltac:(rewrite H1; reflexivity))
          as (p1 & Hps & HA1 & HI1 & _).
        exists A0, m2, p1. split; [exact Htri |]. split; [exact H2 |]. split; [exact HA1 |]. split; [exact HI1 |].
        split.
        - eapply good_steps; [exact Hps |]. exists m0, [], [], (@ls_inv OSig Inc).
          split; [reflexivity |]. split; [left; reflexivity |]. split; [reflexivity |].
          split; [intros o [] | exact Logic.I].
        - destruct (h_ok _ _ _ _ _ _ HH _ HI1) as (v & pool & Hp1 & _). cbn in Hp1. subst p1.
          exists v, pool. split; [reflexivity |].
          rewrite <- (poss_steps_ok_domain CVFe _ _ _ _ Hps). reflexivity. }
      (* schedule A: [key0] alone; it reads its own value [n0] *)
      assert (HA : n0 = m0).
      { destruct (Hfirst n0) as (A0 & m2 & p1 & [Hemit _ Hret] & Hm2 & HA1 & HI1 & HG1 & _).
        destruct (Hemit [] m2 [] ltac:(constructor) q1 p1 [] [] ltac:(rewrite Hm2; reflexivity) HA1 HI1 q1
                    ltac:(rewrite Hm2; cbn; split; [first [reflexivity | apply kupd_same] | reflexivity]))
          as (p2 & Hps2 & HA2 & HI2 & _).
        destruct (Hret _ HA2 HI2 ltac:(intros e [])) as (p3 & Hps3 & (v & pool & -> & Hl) & _).
        exact (good_linr m0 v pool n0 (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps2 Hps3) HG1) Hl). }
      (* schedule B: [key1] reuses the underlay key [(t0, 0)] and
         overwrites the record before [key0] reads it *)
      assert (HB : S n0 = m0).
      { destruct (Hfirst (S n0)) as (A0 & m2 & p1 & [Hemit0 Hstab0 Hret0] & Hm2 & HA1 & HI1 & HG1 & v & pool & -> & Hdom).
        destruct (inc_trace_gen t0 0 0) as (tr1 & Hprod1 & Htr1).
        destruct (Hsem t0 Inc 1 tr1 0 Hprod1) as (A1 & [Hemit1 _ _] & Hinit1).
        set (p1' := EOk v (make_lin_entry key1 (@ls_inv OSig Inc) :: pool)).
        assert (Hpi : poss_invoke CVFe t0 1 Inc (EOk v pool) p1').
        { constructor. constructor. unfold lin_fresh. rewrite Hdom. intros [H | []]. discriminate H. }
        destruct (Hinit1 q1 _ [] p1' HI1 Hpi) as [HI1' HA1'].
        pose proof (h_invoke_rely _ _ _ _ _ _ HH key1 key0 Inc tr1 0 (q1, EOk v pool, []) p1'
                      ltac:(discriminate) Hprod1 HI1 Hpi) as HR.
        pose proof (Hstab0 [m2] _ _ HA1 HR HI1') as HA0'. cbn [ps_mem ps_ghost snd fst] in HA0'.
        destruct tr1 as [| n1 [| n2 [| n3 tr1]]]; try discriminate. cbn in Htr1. injection Htr1 as H1 H2.
        cbn [ps_mem ps_ghost snd fst] in HA0', HI1', HA1'.
        unfold ghost_new in HI1', HA1', HA0'. cbn [app map] in HI1', HA1', HA0'. rewrite H1, H2 in HI1', HA1', HA0'.
        cbn [inv_events te_ev map] in HI1', HA1', HA0'.
        set (q2 := (S (S n0), kupd (kupd rec0 t0 0 n0) t0 0 (S n0)) : HState).
        destruct (Hemit1 [] n1 [n2] ltac:(constructor) q1 p1' _ [] ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA1' HI1' q2 ltac:(rewrite H1; reflexivity))
          as (p2 & Hps2 & _ & HI2 & HG2).
        pose proof (h_guar_rely _ _ _ _ _ _ HH key1 key0 _ _ ltac:(discriminate) HG2) as HR2.
        pose proof (Hstab0 [m2] _ _ HA0' HR2 HI2) as HA2.
        destruct (Hemit0 [] m2 [] ltac:(constructor) q2 p2 [] [] ltac:(rewrite Hm2; reflexivity) HA2 HI2 q2
                    ltac:(rewrite Hm2; cbn; split; [first [reflexivity | apply kupd_same] | reflexivity]))
          as (p3 & Hps3 & HA3 & HI3 & _).
        destruct (Hret0 _ HA3 HI3 ltac:(intros e [])) as (p4 & Hps4 & (v4 & pool4 & -> & Hl) & _).
        assert (HG2' : Good m0 p2) by exact (good_steps _ _ _ Hps2 (good_invoke1 _ _ _ HG1 Hpi)).
        exact (good_linr m0 v4 pool4 (S n0) (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps3 Hps4) HG2') Hl). }
      lia.
    Qed.

    (** M-16, (i) and (ii) together: the overwriting underlay admits no
        model; the handle-linear one admits a model whose invariant reads
        the ghost and whose guarantee constrains memory. *)
    Theorem counter_hl_contrast :
      (forall (I : Assn OVE CVFe) R G q0 m0, ~ RLHL2Hyps I R G Mc q0 (m0, [])) /\
      (forall used, ~ HandleLinear OVE used) /\
      HandleLinear HVE hused /\ RLHL2Hyps Ih Rh Gh Mc hσ0 (0, []).
    Proof.
      split; [exact counter_ow_unsat |]. split; [exact OVE_not_handle_linear |].
      split; [exact HVE_handle_linear | exact counter_hl_rlhl2].
    Qed.
  End CounterHL.

  (** ** Generic assertions on the phase of a call *)

  Section Phase.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.

    Definition KPh (k : CallKey F) (o : Sig.op (RelaxedSig.effect F)) : Assn VE VF :=
      fun s => exists v pool, ps_poss s = PossOk v pool /\ KPhase k o pool.

    Definition KLr (k : CallKey F) (o : Sig.op (RelaxedSig.effect F)) (r : Sig.ar o) : Assn VE VF :=
      fun s => exists v pool, ps_poss s = PossOk v pool /\ lin_lookup k (ls_linr o r) pool.

    (** A relation that keeps the entries of [k] (up to helping). *)
    Definition KeepsRel (k : CallKey F) (r : PRel VE VF) : Prop :=
      forall s s', r s s' -> forall v pool, ps_poss s = PossOk v pool ->
        exists v' pool', ps_poss s' = PossOk v' pool' /\ keeps k pool pool'.

    Lemma KPh_stable (I : Assn VE VF) r k o : KeepsRel k r -> Stable I r (KPh k o).
    Proof.
      intros Hk s s' (v & pool & Hp & Hph) Hr _.
      destruct (Hk s s' Hr v pool Hp) as (v' & pool' & Hp' & Hkp).
      exists v', pool'. split; [exact Hp' | eapply keeps_phase; eauto].
    Qed.

    Lemma KLr_stable (I : Assn VE VF) r k o res : KeepsRel k r -> Stable I r (KLr k o res).
    Proof.
      intros Hk s s' (v & pool & Hp & Hl) Hr _.
      destruct (Hk s s' Hr v pool Hp) as (v' & pool' & Hp' & Hkp).
      exists v', pool'. split; [exact Hp' | eapply keeps_linr; eauto].
    Qed.

    Lemma Stable_I (I : Assn VE VF) r : Stable I r I.
    Proof. intros s s' _ _ HI. exact HI. Qed.

    Lemma pinit_KPh (I : Assn VE VF) k op Ω : Impl I (PostInvoke I k op Ω) (KPh k op).
    Proof.
      intros [[σ p] γ] _ (p0 & γ0 & evs & _ & Hinv & _). cbn [ps_poss ps_mem ps_ghost fst snd] in Hinv.
      destruct Hinv as [st pool pool' Hins]. destruct Hins as [pool0 Hfresh].
      exists st, (make_lin_entry k (ls_inv op) :: pool0). split; [reflexivity | left; left; reflexivity].
    Qed.
  End Phase.

  (** ** (a) Reading a pair without a lock, against a concurrent writer

      Overlay [PairSig] (well-formed: [RdPair] and [WrPair] are
      semi-independent of each other, not of themselves): [RdPair] returns
      the abstract pair, [WrPair] sets it to [(1, 1)].  The writer
      ([writer]: write [X := 1], then [Y := 1], blocking) linearizes at its
      write of [X].  Coupling invariant [I2] (latest-review M-10): the
      abstract pair is [(σX, σX)], [σY <= σX <= 1].  (The review suggested
      [abstract = (σX, σY)] with [σX = σY]; that is not invariant for a
      two-write writer over [MemLTS], which has no two-location atomic
      write, so the closest invariant such a writer maintains is used.)
      The rely [R2] is the closure of the guarantees [G2] of the other
      calls ([G2_in_R2]) and of their invocations and returns
      ([pair_rlhl2]).

      - [read_pair_no_certificate], [read_pair_not_methodsem],
        [read_pair_not_rlhl]: the unlocked double read [read_pair] has no
        certificate, for every guarantee [G], since the writer's two steps
        (guarantee steps of another call) can fall between its reads.
        Relative to (I2, R2): the invariant and the rely are fixed.  For
        every [I], [R], [G]: [ReadPairUniversal.read_pair_no_rlhl2]
        (m-24).
      - Positive controls under the same [I2], [R2], [G2]:
        [read_one_sound] (read [X] once, return [(a, a)]) and
        [writer_sound].
      - [pair_rlhl2]: [I2], [R2], [G2] and [M2good] satisfy every
        hypothesis of [RLHL2Hyps]: a non-vacuity instance of the RLHL-2
        bundle with a well-formed overlay, a concurrent writer and
        interference on the location the reader reads. *)

  Inductive PairOp : Type := RdPair | WrPair.

  Definition pair_ar (o : PairOp) : Type :=
    match o with RdPair => (nat * nat)%type | WrPair => unit end.

  Canonical Structure PairEffect : Sig.t :=
    {| Sig.op := PairOp; Sig.ar := pair_ar |}.

  Definition PairSig : RelaxedSig.t :=
    {|
      RelaxedSig.effect := PairEffect;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := fun o1 o2 => o1 <> o2;
      RelaxedSig.mode := fun _ => Local;
    |}.

  Lemma PairSig_wf : RelaxedSig.well_formed PairSig.
  Proof. constructor; [intros x H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

  Definition pair_step (ev : ThreadEvent PairSig) (v v' : nat * nat) : Prop :=
    match te_ev _ ev with
    | InvEv _ _ => v' = v
    | ResEv _ op r =>
        match op return pair_ar op -> Prop with
        | RdPair => fun r => r = v /\ v' = v
        | WrPair => fun _ => v' = (1, 1)
        end r
    end.

  Definition PairLTS : LTS PairSig :=
    {| State := (nat * nat)%type; Step := pair_step; Error := NoError |}.

  Abbreviation POk v pool := (@PossOk PairSig PairLTS v pool).

  Lemma pair_noop t h o v : Step PairLTS (Build_ThreadEvent t (@InvEv PairSig h o)) v v.
  Proof. reflexivity. Qed.

  (** [call (MRead X) p>= a => call (MRead Y) p>= b => Ret (a, b)], unfolded. *)
  Definition read_pair : Prog RlxSig (nat * nat) :=
    @Future RlxSig (nat * nat) (MRead X) (fun fx => Wait fx (fun (a : nat) =>
    @Future RlxSig (nat * nat) (MRead Y) (fun fy => Wait fy (fun (b : nat) =>
    Ret (a, b))))).

  Definition read_one : Prog RlxSig (nat * nat) :=
    @Future RlxSig (nat * nat) (MRead X) (fun fx => Wait fx (fun (a : nat) => Ret (a, a))).

  Definition writer : Prog RlxSig unit :=
    @Future RlxSig unit (MWrite X 1) (fun fx => Wait fx (fun _ =>
    @Future RlxSig unit (MWrite Y 1) (fun fy => Wait fy (fun _ => Ret tt)))).

  Definition M2 : RelaxedModuleImpl RlxSig PairSig :=
    fun op t => match op as o return Prog RlxSig (Sig.ar o) with
                | RdPair => read_pair
                | WrPair => writer
                end.

  Definition M2good : RelaxedModuleImpl RlxSig PairSig :=
    fun op t => match op as o return Prog RlxSig (Sig.ar o) with
                | RdPair => read_one
                | WrPair => writer
                end.

  Definition t0 : tid := 1%positive.
  Definition k0 : CallKey PairSig := (t0, 0).

  Definition ix : ThreadEvent RlxSig := Build_ThreadEvent t0 (@InvEv RlxSig 0 (MRead X)).
  Definition rx (v : nat) : ThreadEvent RlxSig := Build_ThreadEvent t0 (@ResEv RlxSig 0 (MRead X) v).
  Definition iy : ThreadEvent RlxSig := Build_ThreadEvent t0 (@InvEv RlxSig 1 (MRead Y)).
  Definition ry (v : nat) : ThreadEvent RlxSig := Build_ThreadEvent t0 (@ResEv RlxSig 1 (MRead Y) v).

  (** A produced trace returning [(a, b)] (responses are guessed by the
      method body; the underlay validates them when they are emitted). *)
  Lemma read_pair_trace (a b : nat) :
    exists tr, program_produces_tagged t0 (M2 RdPair t0) tr (a, b) /\
               map untag tr = [ix; rx a; iy; ry b].
  Proof.
    eexists. split.
    - eexists. split.
      + cbn. eapply tagged_execution_emit.
        { apply tagged_future with (h := 0). unfold handle_fresh. cbn. tauto. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending RlxSig (nat * nat) t0 (MRead X) 0 a). apply resolve_here. }
        eapply tagged_execution_emit.
        { apply tagged_future with (h := 1). unfold handle_fresh. cbn. intros [H | []]. discriminate. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending RlxSig (nat * nat) t0 (MRead Y) 1 b). apply resolve_here. }
        apply tagged_execution_refl.
      + apply program_terminal_ret. repeat constructor.
    - reflexivity.
  Qed.

  Abbreviation PA2 := (Assn MemLTS PairLTS).

  Definition I2 : PA2 :=
    fun s => exists a pool, ps_poss s = POk (a, a) pool /\ ps_mem s X = a /\ a <= 1 /\
                            ps_mem s Y <= a /\ lin_pool_well_formed pool.

  (** The memory steps any call may take: none, or a write of [1] to [X]
      or to [Y]. *)
  Definition MemW (σ σ' : Mem) : Prop := σ' = σ \/ σ' = upd σ X 1 \/ σ' = upd σ Y 1.

  Definition G2 (k : CallKey PairSig) : PRel MemLTS PairLTS := fun s s' =>
    MemW (ps_mem s) (ps_mem s') /\
    exists v pool v' pool', ps_poss s = POk v pool /\ ps_poss s' = POk v' pool' /\
      (v' = v \/ v' = (1, 1)) /\ forall k', k' <> k -> keeps k' pool pool'.

  Definition R2 (k : CallKey PairSig) : PRel MemLTS PairLTS := fun s s' =>
    MemW (ps_mem s) (ps_mem s') /\
    exists v pool v' pool', ps_poss s = POk v pool /\ ps_poss s' = POk v' pool' /\
      (v' = v \/ v' = (1, 1)) /\ keeps k pool pool'.

  Lemma G2_in_R2 k k' s s' : k' <> k -> G2 k' s s' -> R2 k s s'.
  Proof.
    intros Hne (Hm & v & pool & v' & pool' & Hp & Hp' & Hv & Hk). split; [exact Hm |].
    exists v, pool, v', pool'. repeat split; auto.
  Qed.

  Lemma R2_keeps k : KeepsRel k (R2 k).
  Proof.
    intros s s' (_ & v & pool & v' & pool' & Hp & Hp' & _ & Hk) v1 pool1 Hp1.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists v', pool'. auto.
  Qed.

  Lemma MemW_X σ σ' : MemW σ σ' -> σ X = 1 -> σ' X = 1.
  Proof. intros [-> | [-> | ->]] H; cbn; auto. Qed.

  Lemma I2_return k op r s p2 :
    I2 s -> poss_return PairLTS (fst k) (snd k) op r (ps_poss s) p2 -> I2 (ps_mem s, p2, ps_ghost s).
  Proof.
    destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd]. intros HI Hret.
    destruct Hret as [st pool1 pool2 Hrem].
    destruct HI as (a & pool & Hp & HX & Ha & HY & Hwf). cbn in Hp, HX, HY. injection Hp as -> <-.
    exists a, pool2. cbn. repeat split; auto. eapply lin_remove_well_formed; eauto.
  Qed.

  Lemma I2_invoke k op σ p γ p' γ' :
    I2 (σ, p, γ) -> poss_invoke PairLTS (fst k) (snd k) op p p' -> I2 (σ, p', γ').
  Proof.
    intros HI Hinv. destruct Hinv as [st pool1 pool2 Hins].
    destruct HI as (a & pool & Hp & HX & Ha & HY & Hwf). cbn in Hp, HX, HY. injection Hp as -> <-.
    exists a, pool2. cbn. repeat split; auto. eapply lin_insert_well_formed; eauto.
  Qed.

  (** *** The positive controls *)

  Section PairProofs.
    Context (t : tid).

    Definition P2 (o : PairOp) (h : nat) : PA2 := fun s => KPh (VE := MemLTS) (VF := PairLTS) (t, h) o s /\ I2 s.
    Definition Q2 (h : nat) (r : nat * nat) : PA2 := fun s => KLr (VE := MemLTS) (VF := PairLTS) (t, h) RdPair r s /\ I2 s.
    Definition QW2 (h : nat) (r : unit) : PA2 := fun s => KLr (VE := MemLTS) (VF := PairLTS) (t, h) WrPair r s /\ I2 s.
    Definition QW2x (h : nat) : PA2 := fun s => KLr (VE := MemLTS) (VF := PairLTS) (t, h) WrPair tt s /\ ps_mem s X = 1 /\ I2 s.

    Lemma P2_stable o h : Stable I2 (R2 (t, h)) (P2 o h).
    Proof. apply Stable_and; [apply KPh_stable, R2_keeps | apply Stable_I]. Qed.

    Lemma Q2_stable h r : Stable I2 (R2 (t, h)) (Q2 h r).
    Proof. apply Stable_and; [apply KLr_stable, R2_keeps | apply Stable_I]. Qed.

    Lemma QW2_stable h r : Stable I2 (R2 (t, h)) (QW2 h r).
    Proof. apply Stable_and; [apply KLr_stable, R2_keeps | apply Stable_I]. Qed.

    Lemma QW2x_stable h : Stable I2 (R2 (t, h)) (QW2x h).
    Proof.
      intros s s' [HK [HX HI]] Hr HI'. split; [eapply KLr_stable; [apply R2_keeps | exact HK | exact Hr | exact HI'] |].
      split; [| exact HI']. destruct Hr as [Hm _]. eapply MemW_X; eauto.
    Qed.

    (** An event that changes neither the memory nor the possibility. *)
    Lemma pupdate_id (k : CallKey PairSig) (P : PA2) ev :
      (forall σ σ', Step MemLTS ev σ σ' -> σ' = σ) ->
      (forall σ p γ γ', P (σ, p, γ) -> P (σ, p, γ')) ->
      (forall s, P s -> I2 s) ->
      PUpdate (VE := MemLTS) (VF := PairLTS) k (G2 k) ev P P.
    Proof.
      intros Hev HP HPI σ p γ γ' Hs _ σ' Hst. apply Hev in Hst. subst σ'.
      exists p. split; [apply rt_refl |]. split; [eapply HP; exact Hs |].
      destruct (HPI _ Hs) as (a & pool & Hp & _). cbn in Hp.
      split; [left; reflexivity |]. exists (a, a), pool, (a, a), pool.
      repeat split; auto. intros; apply keeps_refl.
    Qed.

    Lemma read_one_chain : MethodProvableChain I2 R2 G2 M2good t RdPair (P2 RdPair) Q2.
    Proof.
      constructor.
      - intros h [[σ p] γ] Hs. split; [eapply pinit_KPh; [| exact Hs]; destruct Hs as (p0 & γ0 & evs & HI0 & Hinv & _); eapply I2_invoke; eauto |].
        destruct Hs as (p0 & γ0 & evs & HI0 & Hinv & _). eapply I2_invoke; eauto.
      - intros h s [_ HI]. exact HI.
      - intros h. apply P2_stable.
      - intros h r s p2 [_ HI] Hret. eapply I2_return with (k := (t, h)); eauto.
      - intros h r s [(v & pool & Hp & Hl) _]. exists v, pool. auto.
      - intros h. cbn. unfold read_one.
        apply cprov_call with (P' := P2 RdPair h) (Q' := fun a => Q2 h (a, a)).
        + intros s [_ HI]. exact HI.
        + intros r s [_ HI]. exact HI.
        + apply P2_stable.
        + intros r. apply Q2_stable.
        + intros h'. apply pupdate_id; [intros σ σ' H; exact H | intros σ p γ γ' H; exact H | intros s [_ H]; exact H].
        + (* the read response: help, then linearize with the abstract pair *)
          intros h' a σ p γ γ' [(v & pool & Hp & Hph) (b & pool1 & Hp1 & HX & Hb & HY & Hwf)] _ σ' Hst.
          cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hst. destruct Hst as [-> ->].
          rewrite Hp in Hp1. injection Hp1 as -> <-. subst p. subst b.
          destruct (linearize_response PairLTS (t, h) RdPair (σ X, σ X) (σ X, σ X) (σ X, σ X) pool
                      (fun t' h' o' => pair_noop t' h' o' _) Hwf Hph (conj eq_refl eq_refl))
            as (pool' & Hps & Hl' & Hwf' & Hkeep).
          exists (POk (σ X, σ X) pool'). split; [exact Hps |].
          split; [split; [exists (σ X, σ X), pool'; split; [reflexivity | exact Hl'] |] |].
          * exists (σ X), pool'. cbn. repeat split; auto.
          * split; [left; reflexivity |]. exists (σ X, σ X), pool, (σ X, σ X), pool'.
            split; [reflexivity |]. split; [reflexivity |]. split; [left; reflexivity |]. exact Hkeep.
        + intros a. apply cprov_ret. intros s Hs. exact Hs.
    Qed.

    Lemma writer_chain : MethodProvableChain I2 R2 G2 M2good t WrPair (P2 WrPair) QW2.
    Proof.
      constructor.
      - intros h [[σ p] γ] Hs. destruct Hs as (p0 & γ0 & evs & HI0 & Hinv & Hrest).
        split; [eapply pinit_KPh; [| exists p0, γ0, evs; split; [exact HI0 | split; [exact Hinv | exact Hrest]]]; eapply I2_invoke; eauto |].
        eapply I2_invoke; eauto.
      - intros h s [_ HI]. exact HI.
      - intros h. apply P2_stable.
      - intros h r s p2 [_ HI] Hret. eapply I2_return with (k := (t, h)); eauto.
      - intros h r s [(v & pool & Hp & Hl) _]. exists v, pool. auto.
      - intros h. cbn. unfold writer.
        apply cprov_call with (P' := P2 WrPair h) (Q' := fun _ => QW2x h).
        + intros s [_ HI]. exact HI.
        + intros r s (_ & _ & HI). exact HI.
        + apply P2_stable.
        + intros r. apply QW2x_stable.
        + intros h'. apply pupdate_id; [intros σ σ' H; exact H | intros σ p γ γ' H; exact H | intros s [_ H]; exact H].
        + (* the write of X: help, then linearize the writer *)
          intros h' u σ p γ γ' [(v & pool & Hp & Hph) (b & pool1 & Hp1 & HX & Hb & HY & Hwf)] _ σ' Hst.
          cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hst. subst σ'.
          rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
          destruct (linearize_response PairLTS (t, h) WrPair tt (b, b) (1, 1) pool
                      (fun t' h' o' => pair_noop t' h' o' _) Hwf Hph eq_refl) as (pool' & Hps & Hl' & Hwf' & Hkeep).
          exists (POk (1, 1) pool'). split; [exact Hps |].
          split; [split; [exists (1, 1), pool'; split; [reflexivity | exact Hl'] |] |].
          * split; [reflexivity |]. exists 1, pool'. cbn. repeat split; auto. lia.
          * split; [right; left; reflexivity |]. exists (b, b), pool, (1, 1), pool'.
            split; [reflexivity |]. split; [reflexivity |]. split; [right; reflexivity | exact Hkeep].
        + intros u.
          apply cprov_call with (P' := QW2x h) (Q' := fun _ => QW2x h).
          * intros s (_ & _ & HI). exact HI.
          * intros r s (_ & _ & HI). exact HI.
          * apply QW2x_stable.
          * intros r. apply QW2x_stable.
          * intros h'. apply pupdate_id; [intros σ σ' H; exact H | intros σ p γ γ' H; exact H | intros s (_ & _ & H); exact H].
          * (* the write of Y: no abstract step *)
            intros h' u' σ p γ γ' (HK & HX & (b & pool & Hp & HXb & Hb & HY & Hwf)) _ σ' Hst.
            cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hst. subst σ'.
            exists p. split; [apply rt_refl |].
            split; [split; [exact HK |] |].
            -- split; [cbn; exact HX |]. exists b, pool. cbn. repeat split; auto; lia.
            -- split; [right; right; reflexivity |]. exists (b, b), pool, (b, b), pool.
               repeat split; auto. intros; apply keeps_refl.
          * intros r. apply cprov_ret. intros s (HK & _ & HI). split; [exact HK | exact HI].
    Qed.
  End PairProofs.

  Theorem read_one_sound t : MethodSem I2 R2 G2 M2good t RdPair.
  Proof. eapply chain_sound. apply read_one_chain. Qed.

  Theorem writer_sound t : MethodSem I2 R2 G2 M2good t WrPair.
  Proof. eapply chain_sound. apply writer_chain. Qed.

  Lemma I2_init : I2 (σ0, POk (0, 0) [], []).
  Proof. exists 0, []. cbn. repeat split; auto. constructor. Qed.

  (** Every hypothesis of RLHL-2 holds for the correct module [M2good]. *)
  Theorem pair_rlhl2 : RLHL2Hyps I2 R2 G2 M2good σ0 (0, 0).
  Proof.
    constructor.
    - intros t [|]; [apply read_one_sound | apply writer_sound].
    - intros k k' s s' Hne HG. apply (G2_in_R2 k' k s s' Hne HG).
    - intros k k' op tr ret [[σ p] γ] p' Hne _ HI Hinv. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
      destruct HI as (a & pool & Hp & _). cbn in Hp. subst p.
      inversion Hinv as [st pool1 pool2 Hins]; subst.
      split; [left; reflexivity |]. exists (a, a), pool, (a, a), pool2.
      split; [reflexivity |]. split; [reflexivity |]. split; [left; reflexivity |].
      eapply keeps_insert. exact Hins.
    - intros k k' op r [[σ p] γ] p2 Hne HI Hret _. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
      destruct HI as (a & pool & Hp & _). cbn in Hp. subst p.
      inversion Hret as [st pool1 pool2 Hrem]; subst.
      split; [left; reflexivity |]. exists (a, a), pool, (a, a), pool2.
      split; [reflexivity |]. split; [reflexivity |]. split; [left; reflexivity |].
      eapply keeps_remove_other; [exact Hrem |]. destruct k. intros Heq. apply Hne. symmetry. exact Heq.
    - intros s (a & pool & Hp & _ & _ & _ & Hwf). exists (a, a), pool. auto.
    - exact I2_init.
  Qed.

  (** *** The negative check *)

  Definition lin_good (ls : LinState PairSig) : Prop :=
    match ls with
    | ls_linr op r =>
        match op return pair_ar op -> Prop with
        | RdPair => fun r => r = (0, 0) \/ r = (1, 1)
        | WrPair => fun _ => True
        end r
    | _ => True
    end.

  Definition Good (p : Poss PairLTS) : Prop :=
    exists v pool, p = POk v pool /\ (v = (0, 0) \/ v = (1, 1)) /\
                   forall e, In e pool -> lin_good (lin_state _ e).

  Lemma good_step_at owner p p' : poss_step_at PairLTS owner p p' -> Good p -> Good p'.
  Proof.
    intros Hst. destruct Hst as [t h op st st' pool0 pool' Hlin Hlts | t h op ret st st' pool0 pool' Hlin Hlts
                                | t h op st pool0 Hlin Herr | t h op ret st pool0 Hlin Herr];
      intros (v1 & pool1 & Hp & Hv & Hall); injection Hp as Hst Hpool; subst.
    - cbn in Hlts. subst st'. exists v1, pool'.
      split; [reflexivity |]. split; [exact Hv |]. intros e He.
      apply lin_invoke_update_is_update in Hlin.
      destruct (lin_update_in _ _ _ _ _ _ Hlin He) as [He0 | ->]; [apply Hall; exact He0 | exact Logic.I].
    - revert ret Hlin Hlts. destruct op; intros ret Hlin Hlts; cbn in Hlts.
      + destruct Hlts as [-> ->]. exists v1, pool'.
        split; [reflexivity |]. split; [exact Hv |]. intros e He.
        destruct (lin_update_in _ _ _ _ _ _ Hlin He) as [He0 | ->]; [apply Hall; exact He0 |].
        cbn. exact Hv.
      + subst st'. exists (1, 1), pool'. split; [reflexivity |]. split; [right; reflexivity |].
        intros e He. destruct (lin_update_in _ _ _ _ _ _ Hlin He) as [He0 | ->]; [apply Hall; exact He0 |].
        exact Logic.I.
    - destruct Herr.
    - destruct Herr.
  Qed.

  Lemma good_steps p p' : Good p -> poss_steps PairLTS p p' -> Good p'.
  Proof.
    intros Hg Hs. induction Hs as [p p' (o & Hs) | p | p p1 p' Hs1 IH1 Hs2 IH2]; auto.
    eapply good_step_at; eauto.
  Qed.

  (** The negatives of this section are relative to (I2, R2)
      (latest-review m-23, m-24): they hold for every guarantee [G], but
      for the fixed invariant [I2] and rely [R2] only, not for every
      [I], [R].  Universal negatives (for every [I], [R], [G]):
      [ReadPairUniversal.read_pair_no_rlhl2] below, for this module, and
      [CounterRelLin.bad_counter_no_rlhl2]. *)
  Section NegativeTriple.
    Context (G : CallKey PairSig -> PRel MemLTS PairLTS).

    (** Another call (the writer). *)
    Definition kw : CallKey PairSig := (t0, 7).

    Definition s0 (tr : list (TaggedEvent RlxSig)) : PState MemLTS PairLTS :=
      (σ0, POk (0, 0) [make_lin_entry k0 (@ls_inv PairSig RdPair)], ghost_new k0 tr).

    (** No certificate of the per-call triple contains the post-invocation
        state, for the trace returning [(0, 1)]: the writer's two steps,
        guarantee steps [G2 kw] of another call, fall between the reads. *)
    Theorem read_pair_no_certificate (A : list (TaggedEvent RlxSig) -> PA2) tr :
      map untag tr = [ix; rx 0; iy; ry 1] ->
      CallTriple I2 R2 G k0 RdPair (0, 1) A -> ~ A tr (s0 tr).
    Proof.
      intros Htr [Hemit Hstab Hret] HA.
      destruct tr as [| m1 [| m2 [| m3 [| m4 [| m5 tr]]]]]; try discriminate.
      cbn in Htr. injection Htr as H1 H2 H3 H4.
      assert (Hg0 : ghost_new k0 [m1; m2; m3; m4] =
                    [Build_ScheduledEvent k0 ix; Build_ScheduledEvent k0 iy]).
      { unfold ghost_new. cbn [map]. rewrite H1, H2, H3, H4. reflexivity. }
      unfold s0 in HA. rewrite Hg0 in HA.
      assert (Hfr : forall m, local_frontier (@nil (TaggedEvent RlxSig)) m) by (intros; constructor).
      (* the invocation of X *)
      destruct (Hemit [] m1 [m2; m3; m4] (Hfr m1) σ0 (POk (0, 0) [make_lin_entry k0 (@ls_inv PairSig RdPair)])
                 [Build_ScheduledEvent k0 ix; Build_ScheduledEvent k0 iy] [Build_ScheduledEvent k0 iy]) with (σ' := σ0)
        as (p1 & Hps1 & HA1 & HI1 & _).
      { rewrite H1. cbn. exists [], [Build_ScheduledEvent k0 iy]. split; [reflexivity |]. split; [reflexivity | constructor]. }
      { exact HA. }
      { exists 0, [make_lin_entry k0 (@ls_inv PairSig RdPair)]. cbn. repeat split; auto.
        constructor; [intros [] | constructor]. }
      { rewrite H1. reflexivity. }
      assert (Hg1 : Good p1).
      { eapply good_steps; [| exact Hps1]. eexists _, _. split; [reflexivity |].
        split; [left; reflexivity |]. intros e [<- | []]. exact Logic.I. }
      (* the response of X, value 0 *)
      destruct (Hemit [] m2 [m3; m4] (Hfr m2) σ0 p1 [Build_ScheduledEvent k0 iy] [Build_ScheduledEvent k0 iy]) with (σ' := σ0)
        as (p2 & Hps2 & HA2 & HI2 & _).
      { rewrite H2. reflexivity. }
      { exact HA1. }
      { exact HI1. }
      { rewrite H2. cbn. split; reflexivity. }
      pose proof (good_steps _ _ Hg1 Hps2) as (v2 & pool2 & Hp2 & _ & Hall2).
      destruct HI2 as (a2 & pool2' & Hp2' & _ & _ & _ & Hwf2). cbn in Hp2'. rewrite Hp2 in Hp2'.
      injection Hp2' as _ <-.
      (* the writer: two guarantee steps of the call [kw] *)
      set (σ1 := upd σ0 X 1). set (σ2 := upd σ1 Y 1).
      set (γ1 := [Build_ScheduledEvent k0 iy]).
      assert (HA2' : A [m3; m4] (σ1, POk (1, 1) pool2, γ1)).
      { eapply (Hstab [m3; m4] (σ0, p2, γ1)); [exact HA2 | |].
        - apply (G2_in_R2 k0 kw); [discriminate |]. split; [right; left; reflexivity |].
          exists v2, pool2, (1, 1), pool2. split; [exact Hp2 |]. split; [reflexivity |].
          split; [right; reflexivity |]. intros; apply keeps_refl.
        - exists 1, pool2. cbn. repeat split; auto. }
      assert (HA2'' : A [m3; m4] (σ2, POk (1, 1) pool2, γ1)).
      { eapply (Hstab [m3; m4] (σ1, POk (1, 1) pool2, γ1)); [exact HA2' | |].
        - apply (G2_in_R2 k0 kw); [discriminate |]. split; [right; right; reflexivity |].
          exists (1, 1), pool2, (1, 1), pool2. split; [reflexivity |]. split; [reflexivity |].
          split; [left; reflexivity |]. intros; apply keeps_refl.
        - exists 1, pool2. cbn. repeat split; auto. }
      (* the invocation of Y *)
      destruct (Hemit [] m3 [m4] (Hfr m3) σ2 (POk (1, 1) pool2) γ1 []) with (σ' := σ2)
        as (p3 & Hps3 & HA3 & HI3 & _).
      { rewrite H3. cbn. exists [], []. split; [reflexivity |]. split; [reflexivity | constructor]. }
      { exact HA2''. }
      { exists 1, pool2. cbn. repeat split; auto. }
      { rewrite H3. reflexivity. }
      assert (Hg3 : Good p3).
      { eapply good_steps; [| exact Hps3]. exists (1, 1), pool2. split; [reflexivity |].
        split; [right; reflexivity | exact Hall2]. }
      (* the response of Y, value 1 *)
      destruct (Hemit [] m4 [] (Hfr m4) σ2 p3 [] []) with (σ' := σ2)
        as (p4 & Hps4 & HA4 & HI4 & _).
      { rewrite H4. reflexivity. }
      { exact HA3. }
      { exact HI3. }
      { rewrite H4. cbn. split; reflexivity. }
      pose proof (good_steps _ _ Hg3 Hps4) as Hg4.
      (* the return: the pair (0, 1) never was the abstract state *)
      destruct (Hret (σ2, p4, []) HA4 HI4 ltac:(intros e [])) as (p5 & Hps5 & (v & pool & Hp5 & Hlk) & _).
      cbn in Hps5. destruct (good_steps _ _ Hg4 Hps5) as (v5 & pool5 & Hp5' & _ & Hall5).
      rewrite Hp5 in Hp5'. injection Hp5' as _ <-.
      specialize (Hall5 _ Hlk). cbn in Hall5. destruct Hall5 as [Hc | Hc]; discriminate.
    Qed.

    Corollary read_pair_not_methodsem : ~ MethodSem I2 R2 G M2 t0 RdPair.
    Proof.
      intros Hsem. destruct (read_pair_trace 0 1) as (tr & Hprod & Htr).
      destruct (Hsem 0 tr (0, 1) Hprod) as (A & Htriple & Hinit).
      destruct (Hinit σ0 (POk (0, 0) []) [] (POk (0, 0) [make_lin_entry k0 (@ls_inv PairSig RdPair)]))
        as [_ HA].
      - exact I2_init.
      - constructor. constructor. intros [].
      - exact (read_pair_no_certificate A tr Htr Htriple HA).
    Qed.

    (** Hence no RLHL derivation exists, whatever the footprint and the
        postcondition (relative to (I2, R2): for this invariant and
        rely). *)
    Corollary read_pair_not_rlhl Ω Q : ~ MethodProvable I2 R2 G M2 t0 RdPair Ω Q.
    Proof. intros Hp. apply read_pair_not_methodsem. eapply method_sound. exact Hp. Qed.
  End NegativeTriple.

  (** The check discriminates: under the same [I2], [R2], [G2], the correct
      reader is verified and the unlocked double read is refuted. *)
  Corollary pair_discriminates :
    (forall t, MethodSem I2 R2 G2 M2good t RdPair) /\ ~ MethodSem I2 R2 G2 M2 t0 RdPair.
  Proof. split; [exact read_one_sound | apply read_pair_not_methodsem]. Qed.

  (** *** m-24: a universal negative for [read_pair]

      [ReadPairUniversal.read_pair_no_rlhl2]: *no* [I], [R], [G] satisfy
      [RLHL2Hyps] for [M2] (the unlocked double read and the writer) over
      [MemLTS] with the overlay [PairLTS], from the initial states of
      [pair_rlhl2]; [read_pair_no_rlhl2_gen] for every initial memory and
      pair with the side condition stated there.  Route (latest-review
      m-24): [RelaxedHoareCompLin.rlhl_complin] needs no [HVF], so
      [RLHL2Hyps] would put every overlay trace of [M2] into the copy-cat
      traces over [PairLTS]; those only return [RdPair] results [v0] or
      [(1, 1)] ([pair_rtraces_good]); a two-thread execution of [M2],
      built from module steps ([rp_mtraces]), returns [(σi X, 1)].  The
      negatives of [NegativeTriple] above stay as they are (relative to
      [(I2, R2)]).  [MemLTS] is not a weak-memory model (see its
      comment); the bad execution is an interleaving.  The negative is
      relative to the [PairLTS] reference (an effect-at-response overlay
      without a specification meaning, [pair_not_hvf]); it is the
      contrapositive of soundness: its semantic core is
      [read_pair_not_complin] (no copy-cat inclusion of [M2]'s traces
      into [PairLTS]; closed), and [classic] enters only through
      [rlhl_complin] (latest-review m-38). *)

  Module ReadPairUniversal.
    Import RelaxedHoareCompLin.

    (** The writer runs on a second thread. *)
    Definition t1 : tid := 2%positive.

    Definition iwx : ThreadEvent RlxSig := Build_ThreadEvent t1 (@InvEv RlxSig 0 (MWrite X 1)).
    Definition rwx : ThreadEvent RlxSig := Build_ThreadEvent t1 (@ResEv RlxSig 0 (MWrite X 1) tt).
    Definition iwy : ThreadEvent RlxSig := Build_ThreadEvent t1 (@InvEv RlxSig 1 (MWrite Y 1)).
    Definition rwy : ThreadEvent RlxSig := Build_ThreadEvent t1 (@ResEv RlxSig 1 (MWrite Y 1) tt).

    Lemma writer_trace :
      exists tr, program_produces_tagged t1 (M2 WrPair t1) tr tt /\ map untag tr = [iwx; rwx; iwy; rwy].
    Proof.
      eexists. split.
      - eexists. split.
        + cbn. eapply tagged_execution_emit.
          { apply tagged_future with (h := 0). unfold handle_fresh. cbn. tauto. }
          eapply tagged_execution_emit.
          { apply (@tagged_wait_pending RlxSig unit t1 (MWrite X 1) 0 tt). apply resolve_here. }
          eapply tagged_execution_emit.
          { apply tagged_future with (h := 1). unfold handle_fresh. cbn. intros [H | []]. discriminate. }
          eapply tagged_execution_emit.
          { apply (@tagged_wait_pending RlxSig unit t1 (MWrite Y 1) 1 tt). apply resolve_here. }
          apply tagged_execution_refl.
        + apply program_terminal_ret. repeat constructor.
      - reflexivity.
    Qed.

    (** The overlay trace of the bad execution: the reader returns
        [(σi X, 1)]: it reads [X] before the writer's write of [X] and [Y]
        after the writer's write of [Y]. *)
    Definition rp_trace (σi : Mem) : list (ThreadEvent PairSig) :=
      [Build_ThreadEvent t0 (@InvEv PairSig 0 RdPair); Build_ThreadEvent t1 (@InvEv PairSig 0 WrPair);
       Build_ThreadEvent t1 (@ResEv PairSig 0 WrPair tt); Build_ThreadEvent t0 (@ResEv PairSig 0 RdPair (σi X, 1))].

    (** The bad execution, from module steps: reader on [t0], writer on
        [t1]; the reader's read of [X], the writer's four events, the
        writer's return, the reader's read of [Y], the reader's return. *)
    Lemma rp_mtraces (σi : Mem) : MTraces MemLTS M2 σi (rp_trace σi).
    Proof.
      destruct (read_pair_trace (σi X) 1) as (trR & HpR & HtR).
      destruct writer_trace as (trW & HpW & HtW).
      destruct trR as [| r1 [| r2 [| r3 [| r4 [| ? ?]]]]]; try discriminate. cbn in HtR. injection HtR as Hr1 Hr2 Hr3 Hr4.
      destruct trW as [| w1 [| w2 [| w3 [| w4 [| ? ?]]]]]; try discriminate. cbn in HtW. injection HtW as Hw1 Hw2 Hw3 Hw4.
      set (R1 := @Build_TaggedScheduledEvent RlxSig PairSig (t0, 0) r1).
      set (R2 := @Build_TaggedScheduledEvent RlxSig PairSig (t0, 0) r2).
      set (R3 := @Build_TaggedScheduledEvent RlxSig PairSig (t0, 0) r3).
      set (R4 := @Build_TaggedScheduledEvent RlxSig PairSig (t0, 0) r4).
      set (W1 := @Build_TaggedScheduledEvent RlxSig PairSig (t1, 0) w1).
      set (W2 := @Build_TaggedScheduledEvent RlxSig PairSig (t1, 0) w2).
      set (W3 := @Build_TaggedScheduledEvent RlxSig PairSig (t1, 0) w3).
      set (W4 := @Build_TaggedScheduledEvent RlxSig PairSig (t1, 0) w4).
      assert (Hx3 : forall w, te_tid _ (untag w) = t1 -> tagged_can_cross r3 w)
        by (intros w Hw; left; rewrite Hr3, Hw; discriminate).
      assert (Hx4 : forall w, te_tid _ (untag w) = t1 -> tagged_can_cross r4 w)
        by (intros w Hw; left; rewrite Hr4, Hw; discriminate).
      set (σ1 := upd σi X 1). set (σ2 := upd σ1 Y 1).
      eexists. eexists. split.
      - eapply tagged_module_execution_cons.
        { apply (tagged_invoke MemLTS M2 t0 0 RdPair σi [] [] [] [r1; r2; r3; r4] (σi X, 1)).
          - intros [].
          - exact HpR.
          - cbn [map]. rewrite Hr1, Hr2, Hr3, Hr4. split; [| intros k _ []].
            cbn. constructor; [intros [H | []]; discriminate H | constructor; [intros [] | constructor]]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke MemLTS M2 t1 0 WrPair σi _ _ _ [w1; w2; w3; w4] tt).
          - intros [H | []]. discriminate H.
          - exact HpW.
          - cbn [map]. rewrite Hw1, Hw2, Hw3, Hw4. rewrite Hr1, Hr2, Hr3, Hr4. split.
            + cbn. constructor; [intros [H | []]; discriminate H | constructor; [intros [] | constructor]].
            + cbn. intros k [<- | [<- | []]] [H | [H | []]]; discriminate H. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 R1 σi σi). - apply tagged_select_here. - cbn. rewrite Hr1. reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 R2 σi σi). - apply tagged_select_here. - cbn. rewrite Hr2. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 W1 σi σi).
          - apply tagged_select_next; [apply Hx3; cbn; rewrite Hw1; reflexivity |].
            apply tagged_select_next; [apply Hx4; cbn; rewrite Hw1; reflexivity |]. apply tagged_select_here.
          - cbn. rewrite Hw1. reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 W2 σi σ1).
          - apply tagged_select_next; [apply Hx3; cbn; rewrite Hw2; reflexivity |].
            apply tagged_select_next; [apply Hx4; cbn; rewrite Hw2; reflexivity |]. apply tagged_select_here.
          - cbn. rewrite Hw2. reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 W3 σ1 σ1).
          - apply tagged_select_next; [apply Hx3; cbn; rewrite Hw3; reflexivity |].
            apply tagged_select_next; [apply Hx4; cbn; rewrite Hw3; reflexivity |]. apply tagged_select_here.
          - cbn. rewrite Hw3. reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 W4 σ1 σ2).
          - apply tagged_select_next; [apply Hx3; cbn; rewrite Hw4; reflexivity |].
            apply tagged_select_next; [apply Hx4; cbn; rewrite Hw4; reflexivity |]. apply tagged_select_here.
          - cbn. rewrite Hw4. reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_return MemLTS M2 t1 0 WrPair tt).
          - apply finish_here.
          - intros [H | [H | []]]; discriminate H. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 R3 σ2 σ2). - apply tagged_select_here. - cbn. rewrite Hr3. reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay MemLTS M2 R4 σ2 σ2). - apply tagged_select_here. - cbn. rewrite Hr4. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_return MemLTS M2 t0 0 RdPair (σi X, 1)).
          - apply finish_next; [intros H; discriminate H | apply finish_here].
          - intros []. }
        apply tagged_module_execution_refl.
      - reflexivity.
    Qed.

    (** The copy-cat over [PairLTS]: the states reachable from [v0] are
        [v0] and [(1, 1)] ([pair_step_good]), a read response returns the
        current state ([pair_step_rd]), and an overlay [RdPair] return
        repeats the result of its call's emitted underlay response
        ([cc_trace], invariant [CCP]). *)

    Definition rd_val (ev : ThreadEvent PairSig) : option (nat * nat) :=
      match te_ev _ ev with
      | ResEv _ op r => match op return pair_ar op -> option (nat * nat) with RdPair => fun r => Some r | WrPair => fun _ => None end r
      | InvEv _ _ => None
      end.

    Definition cell_rd (e : CallEntry PairSig) : option (nat * nat) :=
      match ce_cell PairSig e with
      | ActiveCall op r => match op return pair_ar op -> option (nat * nat) with RdPair => fun r => Some r | WrPair => fun _ => None end r
      | DeadCall => None
      end.

    Definition pgood (v0 r : nat * nat) : Prop := r = v0 \/ r = (1, 1).

    Definition CCP (v0 : nat * nat) (c : @TaggedModuleConfig PairSig PairSig PairLTS) : Prop :=
      pgood v0 (tm_lts_state c) /\
      forall e r, In e (tm_calls c) -> cell_rd e = Some r ->
        pgood v0 r \/ exists x, In x (tm_queue c) /\ ts_owner x = call_key e /\ rd_val (untag (ts_event x)) = Some r.

    Lemma pair_step_rd ev q q' r : Step PairLTS ev q q' -> rd_val ev = Some r -> r = q.
    Proof.
      destruct ev as [t [h op | h op r']]; cbn; [intros _ H; discriminate H |].
      destruct op; cbn; [intros [-> _] H; injection H as <-; reflexivity | intros _ H; discriminate H].
    Qed.

    Lemma pair_step_good v0 ev q q' : Step PairLTS ev q q' -> pgood v0 q -> pgood v0 q'.
    Proof.
      destruct ev as [t [h op | h op r']]; cbn; [intros -> H; exact H |].
      destruct op; cbn; [intros [_ ->] H; exact H | intros -> _; right; reflexivity].
    Qed.

    Lemma ccp_step v0 ev c c' : module_step_tagged PairLTS idF ev c c' -> CCP v0 c ->
      CCP v0 c' /\ forall e r, In e (RelaxedGSim.overlay_events [ev]) -> rd_val e = Some r -> pgood v0 r.
    Proof.
      destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft
                    | cand q q' calls Q Q' used Hsel Hlts
                    | t h op ret q calls calls' Q used Hfin Hdone]; intros (Hq & Hc); cbn [tm_lts_state tm_calls tm_queue] in *.
      - destruct (cc_trace t op trace ret Hprod) as (u & ->). split.
        + split; [exact Hq |]. cbn [tm_calls tm_queue]. intros e r [<- | He] Hr.
          * right. exists (Build_TaggedScheduledEvent (t, h) (cc_res_ev t u op ret)).
            split; [apply in_or_app; right; right; left; reflexivity |]. split; [reflexivity | exact Hr].
          * destruct (Hc e r He Hr) as [Hg | (x & Hx & Ho & Hv)]; [left; exact Hg |].
            right. exists x. split; [apply in_or_app; left; exact Hx | auto].
        + intros e r [<- | []] Hr. discriminate Hr.
      - destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & HQ & HQ' & _). split.
        + split; [exact (pair_step_good v0 _ _ _ Hlts Hq) |]. cbn [tm_calls tm_queue]. intros e r He Hr.
          destruct (Hc e r He Hr) as [Hg | (x & Hx & Ho & Hv)]; [left; exact Hg |].
          rewrite HQ in Hx. apply in_app_or in Hx as [Hx | [<- | Hx]].
          * right. exists x. rewrite HQ'. split; [apply in_or_app; left; exact Hx | auto].
          * left. rewrite (pair_step_rd _ _ _ _ Hlts Hv). exact Hq.
          * right. exists x. rewrite HQ'. split; [apply in_or_app; right; exact Hx | auto].
        + intros e r [].
      - split.
        + split; [exact Hq |]. cbn [tm_calls tm_queue]. intros e r He Hr.
          destruct (RelaxedGSim.finish_back _ _ _ _ _ _ _ Hfin He) as [He' | ->]; [| discriminate Hr].
          exact (Hc e r He' Hr).
        + intros e r [<- | []] Hr. pose proof (RelaxedGSim.finish_src _ _ _ _ _ _ Hfin) as Hsrc.
          destruct (Hc _ r Hsrc Hr) as [Hg | (x & Hx & Ho & _)]; [exact Hg |].
          exfalso. apply Hdone. change (t, h) with (call_key (Build_CallEntry t h (ActiveCall op ret))).
          rewrite <- Ho. apply in_map. exact Hx.
    Qed.

    Lemma ccp_exec v0 c evs c' : module_execution_tagged PairLTS idF c evs c' -> CCP v0 c ->
      forall e r, In e (RelaxedGSim.overlay_events evs) -> rd_val e = Some r -> pgood v0 r.
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros Hc e r He Hr; [destruct He |].
      destruct (ccp_step v0 ev c1 c2 Hst Hc) as [Hc2 Hev].
      rewrite RelaxedGSim.overlay_events_cons in He.
      apply in_app_or in He as [He | He]; [exact (Hev e r He Hr) | exact (IH Hc2 e r He Hr)].
    Qed.

    (** Every [RdPair] result in a copy-cat trace over [PairLTS] from
        [v0] is [v0] or [(1, 1)]. *)
    Theorem pair_rtraces_good v0 s : RTraces PairLTS v0 s -> forall e r, In e s -> rd_val e = Some r -> pgood v0 r.
    Proof.
      intros (evs & c & Hex & <-). apply (ccp_exec v0 _ _ _ Hex).
      split; [left; reflexivity | intros e r []].
    Qed.

    (** latest-review m-38: the semantic core of the negative, without
        the logic.  The traces of [M2] over [MemLTS] are not included in
        the copy-cat traces over [PairLTS] from [v0], under the side
        conditions of [read_pair_no_rlhl2_gen]. *)
    Theorem read_pair_not_complin (σi : Mem) (v0 : nat * nat) :
      (σi X, 1) <> v0 -> σi X <> 1 -> ~ RCompLin M2 MemLTS σi PairLTS v0.
    Proof.
      intros Hv HX Hcc.
      destruct (pair_rtraces_good v0 _ (Hcc (rp_trace σi) (rp_mtraces σi))
                  (Build_ThreadEvent t0 (@ResEv PairSig 0 RdPair (σi X, 1))) (σi X, 1)) as [H | H].
      - right. right. right. left. reflexivity.
      - reflexivity.
      - exact (Hv H).
      - injection H as H. exact (HX H).
    Qed.

    (** m-24: for every invariant, rely and guarantee, [RLHL2Hyps] fails
        for [M2] over [MemLTS] with the overlay [PairLTS], from every
        initial memory [σi] and abstract pair [v0] for which [(σi X, 1)]
        is neither [v0] nor [(1, 1)].  The side condition is needed: from
        [v0 = (σi X, 1)] the bad result is a legal abstract state.
        [classic] enters through [RelaxedHoareCompLin.rlhl_complin]
        ([rinv_val]); no [HVF] is needed. *)
    Theorem read_pair_no_rlhl2_gen (σi : Mem) (v0 : nat * nat) :
      (σi X, 1) <> v0 -> σi X <> 1 ->
      forall (I : PA2) (R G : CallKey PairSig -> PRel MemLTS PairLTS), ~ RLHL2Hyps I R G M2 σi v0.
    Proof.
      intros Hv HX I R G HH.
      pose proof (rlhl_complin I R G M2 σi v0 HH (rp_trace σi) (rp_mtraces σi)) as Hcc.
      destruct (pair_rtraces_good v0 _ Hcc (Build_ThreadEvent t0 (@ResEv PairSig 0 RdPair (σi X, 1))) (σi X, 1))
        as [H | H].
      - right. right. right. left. reflexivity.
      - reflexivity.
      - exact (Hv H).
      - injection H as H. exact (HX H).
    Qed.

    (** The instance at the initial states of [pair_rlhl2]. *)
    Theorem read_pair_no_rlhl2 :
      forall (I : PA2) (R G : CallKey PairSig -> PRel MemLTS PairLTS), ~ RLHL2Hyps I R G M2 σ0 (0, 0).
    Proof. apply read_pair_no_rlhl2_gen; cbn; intros H; discriminate H. Qed.

    (** The universal form of [pair_discriminates]: from the same initial
        states, [M2good] has an [RLHL2Hyps] instance and [M2] has none. *)
    Corollary pair_discriminates_rlhl2 :
      RLHL2Hyps I2 R2 G2 M2good σ0 (0, 0) /\
      forall (I : PA2) (R G : CallKey PairSig -> PRel MemLTS PairLTS), ~ RLHL2Hyps I R G M2 σ0 (0, 0).
    Proof. exact (conj pair_rlhl2 read_pair_no_rlhl2). Qed.
  End ReadPairUniversal.

  (** *** (a1) The previous, existential judgement is satisfied by an
      infeasible path

      [RelaxedLogic.MethodProvable] (positional semantics, one certified
      execution path, a debt certificate that only applies when the whole
      module queue is the method's own debt, and no rely) holds for the
      [RdPair] method of [M2] with the precondition "both cells hold [0]
      and the queue is non-empty" and the postcondition "a call of thread
      [t0] is linearized with result [r] while the abstract pair is
      [(0, 0)]".  The certified path is [tr01]: [X] returns [0], [Y]
      returns [1].  Under the precondition, the last response ([Y] returns
      [1]) is not enabled ([ry1_disabled]), so its obligation holds
      vacuously: the old judgement is satisfied by an infeasible path, and
      it has no rely in which a writer that would make the path feasible
      could be stated.  The postcondition is false in every execution:
      [PairLTS] only linearizes a read with the current abstract pair. *)

  Section OldDerivation.
    Import RelaxedRGISimulation.
    Import RelaxedAssertions.
    Import RelaxedLogic.

    Abbreviation OAssn := (@RelaxedRGISimulation.Assertion RlxSig PairSig MemLTS PairLTS).

    Definition OI : OAssn := fun _ => True.
    Definition OG : @ConcreteRelation RlxSig PairSig MemLTS := fun _ _ => True.
    Definition OAG : @AbstractRelation PairSig PairLTS := fun _ _ => True.

    Definition mem00_state (σ : Mem) : Prop := σ X = 0 /\ σ Y = 0.

    Definition mem00 : OAssn := fun st => mem00_state (mc_lts_state (fst st)).

    Definition OP : OAssn := fun st => mem00 st /\ mc_queue (fst st) <> [].

    Definition OQ (r : nat * nat) : OAssn :=
      fun st => exists pool h, snd st = POk (0, 0) pool /\
                               lin_lookup (t0, h) (@ls_linr PairSig RdPair r) pool.

    Abbreviation Obl := (EventObligation MemLTS PairLTS M2 OI OG OAG).
    Abbreviation oev o := (se_event (obligation_event MemLTS PairLTS M2 OI OG OAG o)).

    Lemma old_underlay_step o ev c c' :
      module_step_at MemLTS M2 o (UnderlayEvent ev) c c' ->
      Step MemLTS ev (mc_lts_state c) (mc_lts_state c').
    Proof.
      intros Hst. inversion Hst as [| cand q q' pool queue queue' used Hsel Hlts |]; subst.
      cbn. exact Hlts.
    Qed.

    Lemma old_lift st st' : invariant_lift MemLTS PairLTS OI OG OAG st st'.
    Proof. repeat split. Qed.

    Lemma sel_single (c o : Obl) r :
      select_obligation MemLTS PairLTS M2 OI OG OAG c [o] r -> c = o /\ r = [].
    Proof.
      intros Hs. inversion Hs as [suf | e q q' Hc Hs']; subst; [auto |]. inversion Hs'.
    Qed.

    Lemma sel_blocked (c a b : Obl) l r :
      select_obligation MemLTS PairLTS M2 OI OG OAG c (a :: b :: l) r ->
      ~ event_can_cross (oev a) (oev b) ->
      (forall x, In x l -> ~ event_can_cross (oev b) (oev x)) ->
      c = a /\ r = b :: l.
    Proof.
      intros Hs Hab Hb. inversion Hs as [suf | e q q' Hc Hs']; subst; [auto |].
      exfalso. inversion Hs' as [suf' | e' q2 q2' Hc' Hs'']; subst.
      - exact (Hab Hc).
      - apply (Hb c); [eapply select_obligation_member; eauto | exact Hc'].
    Qed.

    Lemma ds_cons (Q : OAssn) (o : Obl) l st :
      (forall c r, select_obligation MemLTS PairLTS M2 OI OG OAG c (o :: l) r -> c = o /\ r = l) ->
      obligation_pre MemLTS PairLTS M2 OI OG OAG o st ->
      (forall st', obligation_post MemLTS PairLTS M2 OI OG OAG o st' ->
         DebtSafe MemLTS PairLTS M2 OI OG OAG Q st' l) ->
      DebtSafe MemLTS PairLTS M2 OI OG OAG Q st (o :: l).
    Proof.
      intros Hsel Hpre Hnext. apply debt_safe_pending; [discriminate |].
      intros c r Hs. destruct (Hsel c r Hs) as [-> ->]. split; [exact Hpre |].
      intros c' Hst. destruct st as [cc p].
      destruct (obligation_valid MemLTS PairLTS M2 OI OG OAG o cc p Hpre c' Hst)
        as (p' & Hps & Hpost & Hlift).
      exists p'. split; [exact Hps |]. split; [exact Hpost |]. split; [exact Hlift |].
      apply Hnext. exact Hpost.
    Qed.

    Ltac no_cross := unfold event_can_cross, invocation_can_cross; cbn; intros [Hne | [_ Hc]];
                     [apply Hne; reflexivity | exact Hc].

    Context (h : nat).

    Definition sev (ev : ThreadEvent RlxSig) : ScheduledEvent RlxSig PairSig :=
      @Build_ScheduledEvent RlxSig PairSig (t0, h) ev.

    Lemma uu_keep (ev : ThreadEvent RlxSig) :
      (forall σ σ', Step MemLTS ev σ σ' -> σ' = σ) ->
      UUpdate MemLTS PairLTS M2 OI OG OAG (sev ev) mem00 mem00.
    Proof.
      intros Hev c p HP c' Hst. apply old_underlay_step in Hst. apply Hev in Hst.
      exists p. split; [apply rt_refl |]. split; [| apply old_lift].
      unfold mem00 in *. cbn in *. rewrite Hst. exact HP.
    Qed.

    Lemma uu_vacuous (ev : ThreadEvent RlxSig) (Post : OAssn) :
      (forall σ σ', mem00_state σ -> ~ Step MemLTS ev σ σ') ->
      UUpdate MemLTS PairLTS M2 OI OG OAG (sev ev) mem00 Post.
    Proof.
      intros Hev c p HP c' Hst. apply old_underlay_step in Hst.
      exfalso. eapply Hev; [exact HP | exact Hst].
    Qed.

    Definition o1 : Obl :=
      {| obligation_event := sev ix; obligation_pre := mem00; obligation_post := mem00;
         obligation_valid := uu_keep ix (fun σ σ' H => H) |}.
    Definition o2 : Obl :=
      {| obligation_event := sev (rx 0); obligation_pre := mem00; obligation_post := mem00;
         obligation_valid := uu_keep (rx 0) (fun σ σ' H => proj2 H) |}.
    Definition o3 : Obl :=
      {| obligation_event := sev iy; obligation_pre := mem00; obligation_post := mem00;
         obligation_valid := uu_keep iy (fun σ σ' H => H) |}.

    Lemma ry1_disabled σ σ' : mem00_state σ -> ~ Step MemLTS (ry 1) σ σ'.
    Proof. intros [_ HY] [H _]. rewrite HY in H. discriminate. Qed.

    Definition o4 : Obl :=
      {| obligation_event := sev (ry 1); obligation_pre := mem00; obligation_post := OQ (0, 1);
         obligation_valid := uu_vacuous (ry 1) (OQ (0, 1)) ry1_disabled |}.

    Lemma ds4 st : mem00 st -> DebtSafe MemLTS PairLTS M2 OI OG OAG (OQ (0, 1)) st [o4].
    Proof.
      intros H0. apply ds_cons; [intros c r Hs; exact (sel_single c o4 r Hs) | exact H0 |].
      intros st' Hpost. apply debt_safe_done. exact Hpost.
    Qed.

    Lemma ds34 st : mem00 st -> DebtSafe MemLTS PairLTS M2 OI OG OAG (OQ (0, 1)) st [o3; o4].
    Proof.
      intros H0. apply ds_cons; [| exact H0 | intros st' Hpost; apply ds4; exact Hpost].
      intros c r Hs. eapply sel_blocked; [exact Hs | no_cross | intros x []].
    Qed.

    Lemma ds234 st : mem00 st -> DebtSafe MemLTS PairLTS M2 OI OG OAG (OQ (0, 1)) st [o2; o3; o4].
    Proof.
      intros H0. apply ds_cons; [| exact H0 | intros st' Hpost; apply ds34; exact Hpost].
      intros c r Hs. eapply sel_blocked; [exact Hs | no_cross |].
      intros x [<- | []]. no_cross.
    Qed.

    Lemma ds1234 st : mem00 st -> DebtSafe MemLTS PairLTS M2 OI OG OAG (OQ (0, 1)) st [o1; o2; o3; o4].
    Proof.
      intros H0. apply ds_cons; [| exact H0 | intros st' Hpost; apply ds234; exact Hpost].
      intros c r Hs. eapply sel_blocked; [exact Hs | no_cross |].
      intros x [<- | [<- | []]]; no_cross.
    Qed.

    Lemma cert (obs : list Obl) :
      (forall st, mem00 st -> DebtSafe MemLTS PairLTS M2 OI OG OAG (OQ (0, 1)) st obs) ->
      DebtCertificate MemLTS PairLTS M2 OI OG OAG OP (OQ (0, 1)) obs.
    Proof. intros Hds st [H0 _] _. apply Hds. exact H0. Qed.

    Lemma read_pair_old_derivation :
      exists final, HTripleDerivation MemLTS PairLTS M2 OI OG OAG (t0, h) t0 (nat * nat)
        OP read_pair empty_store OQ [o1; o2; o3; o4] (0, 1) final.
    Proof.
      eexists. unfold read_pair.
      eapply provable_future with (handle := 0) (obligation := o1).
      - unfold handle_fresh. cbn. tauto.
      - reflexivity.
      - cbv beta. eapply provable_wait_pending with (ret := 0) (obligation := o2).
        + apply resolve_here.
        + reflexivity.
        + cbv beta. eapply provable_future with (handle := 1) (obligation := o3).
          * unfold handle_fresh. cbn. intros [Hc | []]. discriminate.
          * reflexivity.
          * cbv beta. eapply provable_wait_pending with (ret := 1) (obligation := o4).
            -- apply resolve_here.
            -- reflexivity.
            -- cbv beta. split; [apply certified_refl |]. split.
               ++ apply program_terminal_ret. repeat constructor.
               ++ intros st [_ Hne] Hq. exfalso. apply Hne. symmetry. exact Hq.
            -- apply cert. apply ds4.
          * apply cert. apply ds34.
        + apply cert. apply ds234.
      - apply cert. apply ds1234.
    Qed.
  End OldDerivation.

  (** The old method-level judgement holds for [M2], for every handle. *)
  Corollary read_pair_old_method_provable :
    RelaxedLogic.MethodProvable MemLTS PairLTS M2 OI OG OAG t0 RdPair OP OQ.
  Proof.
    intros h. destruct (read_pair_old_derivation h) as (final & Hd).
    exists (o1 h :: o2 h :: o3 h :: o4 h :: []), (0, 1), final. exact Hd.
  Qed.

  (** ** (c) Two independent reads: own-event interference

      [x <- ?rd(X); a <- wait x; y <- ?rd(Y); b <- wait y; ret (a, b)], with
      empty dependency tags: the read of [Y] uses no value of the read of
      [X], so the tagged scheduler may emit its invocation before the
      response of [X].  No other call writes memory ([R4]); the method
      linearizes at return, after helping ([linearize_response]).  The
      own-event interference premises are discharged by
      [newslot_guar_in_rely]: the own events change neither the memory nor
      the possibility ([Own4]).  [G4] is tightened (latest-review m-10):
      it keeps the memory, the abstract state and the entries of the other
      calls (up to helping), so [G4_in_R4] holds. *)

  Definition M4 : Prog RlxSig (nat * nat) :=
    @FutureD RlxSig (nat * nat) (MRead X) no_deps (fun fx => Wait fx (fun (a : nat) =>
    @FutureD RlxSig (nat * nat) (MRead Y) no_deps (fun fy => Wait fy (fun (b : nat) =>
    Ret (a, b))))).

  Definition M4impl : RelaxedModuleImpl RlxSig PairSig :=
    fun op t => match op as o return Prog RlxSig (Sig.ar o) with
                | RdPair => M4
                | WrPair => writer
                end.

  Definition I4 : PA2 :=
    fun s => exists pool, ps_poss s = POk (ps_mem s X, ps_mem s Y) pool /\ lin_pool_well_formed pool.

  Definition R4 (k : CallKey PairSig) : PRel MemLTS PairLTS :=
    fun s s' => ps_mem s' = ps_mem s /\
      exists v pool pool', ps_poss s = POk v pool /\ ps_poss s' = POk v pool' /\ keeps k pool pool'.

  Definition G4 (k : CallKey PairSig) : PRel MemLTS PairLTS :=
    fun s s' => ps_mem s' = ps_mem s /\
      exists v pool pool', ps_poss s = POk v pool /\ ps_poss s' = POk v pool' /\
        forall k', k' <> k -> keeps k' pool pool'.

  Lemma G4_in_R4 k k' s s' : k' <> k -> G4 k' s s' -> R4 k s s'.
  Proof.
    intros Hne (Hm & v & pool & pool' & Hp & Hp' & Hk). split; [exact Hm |].
    exists v, pool, pool'. repeat split; auto.
  Qed.

  Lemma R4_keeps k : KeepsRel k (R4 k).
  Proof.
    intros s s' (_ & v & pool & pool' & Hp & Hp' & Hk) v1 pool1 Hp1.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists v, pool'. auto.
  Qed.

  (** The guarantee of an own event of [M4]: nothing changes but the
      ghost. *)
  Definition Own4 : PRel MemLTS PairLTS :=
    fun s s' => ps_mem s' = ps_mem s /\
      exists v pool, ps_poss s = POk v pool /\ ps_poss s' = POk v pool.

  Definition MX (a : nat) : PA2 := fun s => ps_mem s X = a.
  Definition MY (b : nat) : PA2 := fun s => ps_mem s Y = b.

  Lemma mem_stable k (P : Mem -> Prop) : Stable I4 (R4 k) (fun s => P (ps_mem s)).
  Proof. intros s s' Hs (Hm & _) _. rewrite Hm. exact Hs. Qed.

  Abbreviation KPh4 k := (KPh (VE := MemLTS) (VF := PairLTS) k RdPair).

  Definition slot_of (k : CallKey PairSig) (ev : TaggedEvent RlxSig) (post : Mem -> Prop) :
      Slot MemLTS PairLTS :=
    mkSlot ev (KPh4 k) (fun _ => KPh4 k) (fun s => post (ps_mem s) /\ KPh4 k s) Own4.

  Definition SlotShape (k : CallKey PairSig) (sl : Slot MemLTS PairLTS) : Prop :=
    exists ev post, sl = slot_of k ev post.

  Lemma ns_slot k Pinit (Γ : list (Slot MemLTS PairLTS)) ev post :
    Forall (SlotShape k) Γ -> Impl I4 Pinit (KPh4 k) ->
    (forall σ σ', Step MemLTS (untag ev) σ σ' -> σ' = σ /\ post σ') ->
    NewSlotOK I4 R4 G4 k Pinit Γ (slot_of k ev post).
  Proof.
    intros HΓ Hpinit Hstep. rewrite Forall_forall in HΓ.
    assert (Hshape : forall g sg, nth_error Γ g = Some sg -> SlotShape k sg)
      by (intros g sg Hg; apply HΓ; eapply nth_error_In; eauto).
    assert (HownR : forall s s', Own4 s s' -> R4 k s s').
    { intros s s' (Hm & v & pool & Hp & Hp'). split; [exact Hm |]. exists v, pool, pool.
      repeat split; auto. apply keeps_refl. }
    apply newslot_guar_in_rely; cbn [sl_ev sl_start sl_in sl_post sl_guar slot_of].
    - intros g sg Hg. destruct (Hshape g sg Hg) as (ev' & post' & ->). cbn. exact HownR.
    - intros y sy Hy. destruct (Hshape y sy Hy) as (ev' & post' & ->). cbn.
      split; [apply KPh_stable, R4_keeps | intros; apply KPh_stable, R4_keeps].
    - exact HownR.
    - intros s0 s1 (Hm & v & pool & Hp & Hp'). split; [exact Hm |]. exists v, pool, pool.
      repeat split; auto. intros; apply keeps_refl.
    - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar slot_of].
      intros σ p γ γ' [HK _] HI _ σ' Hst. destruct (Hstep σ σ' Hst) as [-> Hpost].
      exists p. split; [apply rt_refl |]. split; [split; [exact Hpost | exact HK] |].
      split; [exact HI |]. destruct HI as (pool & Hp & _). split; [reflexivity |].
      exists (σ X, σ Y), pool. auto.
    - exact Hpinit.
    - intros d sd _ Hd. destruct (Hshape d sd Hd) as (ev' & post' & ->). cbn.
      intros s _ [_ H]. exact H.
    - apply KPh_stable, R4_keeps.
    - intros; apply KPh_stable, R4_keeps.
  Qed.

  Section M4Proof.
    Context (t : tid) (h : nat).

    Abbreviation P4 := (PostInvoke I4 (t, h) RdPair (fun _ => True)).

    Definition Q4 (r : nat * nat) : PA2 := fun s => MX (fst r) s /\ MY (snd r) s /\ KPh4 (t, h) s.

    Lemma m4_derivation :
      RProvable I4 R4 G4 (t, h) P4
        (fun a Γ H => Close I4 R4 G4 (t, h) P4 Q4 a Γ H /\ True) [] empty_store M4.
    Proof.
      assert (Hpinit : Impl I4 P4 (KPh4 (t, h))) by apply pinit_KPh.
      unfold M4.
      apply rp_futureD with (sl := fun hX => slot_of (t, h) (invD_tev (E := RlxSig) (F := PairSig) (t, h) empty_store no_deps hX (MRead X)) (fun _ => True)).
      { intros; reflexivity. }
      { intros hX _. apply ns_slot; [constructor | exact Hpinit |].
        cbn. intros σ σ' ->. auto. }
      intros hX HfX. cbv beta.
      apply rp_wait_pending with (sl := fun a => slot_of (t, h) (res_tev (E := RlxSig) (F := PairSig) (t, h) hX (MRead X) a) (fun σ => σ X = a)).
      { left. reflexivity. }
      { intros; reflexivity. }
      { intros a. apply ns_slot; [repeat constructor; eexists _, _; reflexivity | exact Hpinit |].
        cbn. intros σ σ' [Ha ->]. auto. }
      intros a H2 HresX. cbv beta.
      apply rp_futureD with (sl := fun hY => slot_of (t, h) (invD_tev (E := RlxSig) (F := PairSig) (t, h) H2 no_deps hY (MRead Y)) (fun _ => True)).
      { intros; reflexivity. }
      { intros hY _. apply ns_slot; [repeat constructor; eexists _, _; reflexivity | exact Hpinit |].
        cbn. intros σ σ' ->. auto. }
      intros hY HfY. cbv beta.
      apply rp_wait_pending with (sl := fun b => slot_of (t, h) (res_tev (E := RlxSig) (F := PairSig) (t, h) hY (MRead Y) b) (fun σ => σ Y = b)).
      { left. reflexivity. }
      { intros; reflexivity. }
      { intros b. apply ns_slot; [repeat constructor; eexists _, _; reflexivity | exact Hpinit |].
        cbn. intros σ σ' [Hb ->]. auto. }
      intros b H4 HresY. cbv beta. apply rp_ret. split; [| exact Logic.I].
      apply close_done with
        (fin := fun d => match d with 1 => MX a | 3 => MY b | _ => fun _ => True end)
        (fin0 := KPh4 (t, h)).
      - eapply resolve_fresh_all_resolved; [| exact HresY].
        eapply resolve_fresh_all_resolved; [constructor | exact HresX].
      - apply barrier_guar_in_rely.
        + intros g sg Hg s s' Hs.
          destruct g as [| [| [| [| g]]]]; cbn in Hg; try (destruct g; discriminate);
            injection Hg as <-; destruct Hs as (Hm & v & pool & Hp & Hp'); (split; [exact Hm |]);
            exists v, pool, pool; repeat split; auto; apply keeps_refl.
        + intros d sd Hd.
          destruct d as [| [| [| [| d]]]]; cbn in Hd; try (destruct d; discriminate);
            injection Hd as <-; cbn; intros s _ Hs; try exact Logic.I; apply Hs.
        + exact Hpinit.
        + intros [| [| [| [| d]]]]; try apply Stable_true.
          * exact (mem_stable (t, h) (fun σ => σ X = a)).
          * exact (mem_stable (t, h) (fun σ => σ Y = b)).
        + apply KPh_stable, R4_keeps.
        + intros s _ HKI Hfin. unfold Q4. cbn.
          split; [exact (Hfin 1 _ eq_refl Logic.I) |].
          split; [exact (Hfin 3 _ eq_refl Logic.I) | exact HKI].
    Qed.
  End M4Proof.

  Lemma m4_provable t : MethodProvable I4 R4 G4 M4impl t RdPair (fun _ _ => True) (Q4 t).
  Proof.
    constructor.
    - intros h [[σ p] γ] (p0 & γ0 & evs & (pool0 & Hp0 & Hwf) & Hinv & _).
      cbn [ps_poss ps_mem ps_ghost fst snd] in *. destruct Hinv as [st pool pool' Hins].
      injection Hp0 as -> <-. exists pool'. split; [reflexivity |]. eapply lin_insert_well_formed; eauto.
    - intros h r [[σ p] γ] (HX & HY & (v & pool & Hp & Hph)) (pool1 & Hp1 & Hwf) _.
      cbn [ps_poss ps_mem ps_ghost fst snd] in *. unfold MX, MY in HX, HY. cbn in HX, HY.
      rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
      destruct r as [a b]. cbn in HX, HY. subst a b.
      destruct (linearize_response PairLTS (t, h) RdPair (σ X, σ Y) (σ X, σ Y) (σ X, σ Y) pool
                  (fun t' h' o' => pair_noop t' h' o' _) Hwf Hph (conj eq_refl eq_refl))
        as (pool' & Hps & Hl' & Hwf' & Hkeep).
      exists (POk (σ X, σ Y) pool'). cbn [ps_poss ps_mem ps_ghost fst snd].
      split; [exact Hps |]. split; [eexists _, _; split; [reflexivity | exact Hl'] |].
      split; [exists pool'; split; [reflexivity | exact Hwf'] |].
      split; [apply r_step; split; [reflexivity |]; exists (σ X, σ Y), pool, pool'; repeat split; auto |].
      intros p2 Hret. inversion Hret as [st pool3 pool4 Hrem]; subst.
      exists pool4. split; [reflexivity |]. eapply lin_remove_well_formed; eauto.
    - intros h. exact (m4_derivation t h).
  Qed.

  (** The semantic triple, for every produced trace (every response, every
      order of the asynchronous responses). *)
  Theorem m4_sound t : MethodSem I4 R4 G4 M4impl t RdPair.
  Proof. eapply method_sound. apply m4_provable. Qed.

  Lemma m4_init : I4 (σ0, POk (0, 0) [], []).
  Proof. exists []. split; [reflexivity | constructor]. Qed.

  (** m-19: a single-call check (the [RdPair] method only; the writer of
      [M4impl] cannot satisfy [G4], which freezes memory, so there is no
      [RLHL2Hyps] instance). *)
  Corollary m4_single_call : I4 (σ0, POk (0, 0) [], []) /\ forall t, MethodSem I4 R4 G4 M4impl t RdPair.
  Proof. split; [exact m4_init | exact m4_sound]. Qed.

  (** Non-vacuity of the interference premises.  [m4_ctx t h a] is
      written by hand (latest-review m-23): it is meant to be the list of
      slot events that [m4_derivation] builds for the call [(t, h)] when
      the underlay handles are [0] and [1] and [X] returns [a] (the lazy
      store after the first [Wait] is the one-entry store below), but this
      correspondence is not checked; no lemma derives [m4_ctx] from a
      produced trace or from the derivation.  The two examples below are
      statements about this list: in it, the invocation of [Y] is not
      ordered after the invocation or the response of [X].  If the list is
      the derivation's context, the premises [ns_if_new_start] and
      [ns_if_old_start]/[ns_if_old_in] of the [Y] slot are instantiated
      with pairs that can fire concurrently.  (They are discharged by
      [newslot_guar_in_rely]; a derivation whose premises need the
      [~ before] hypotheses is [tas_derivation] below.) *)
  Definition m4_ctx (t : tid) (h a : nat) : list (TaggedEvent RlxSig) :=
    [invD_tev (E := RlxSig) (F := PairSig) (t, h) empty_store no_deps 0 (MRead X);
     res_tev (E := RlxSig) (F := PairSig) (t, h) 0 (MRead X) a;
     invD_tev (E := RlxSig) (F := PairSig) (t, h) [@Build_FutureEntry RlxSig 0 (@Resolved RlxSig (MRead X) a)] no_deps 1 (MRead Y)].

  Example m4_invY_unordered t h a :
    ~ before (m4_ctx t h a) 0 2 /\ ~ before (m4_ctx t h a) 1 2.
  Proof.
    assert (Hno : forall d, ~ dprec (m4_ctx t h a) d 2).
    { intros d Hd. inversion Hd as [d0 j0 x y Hlt Hx Hy Hm]; subst.
      cbn in Hy. injection Hy as <-.
      destruct d as [| [| d]]; [| | lia]; cbn in Hx; injection Hx as <-.
      - unfold must_precede in Hm. cbn in Hm. apply Hm. cbn. unfold rlx_independent. cbn. discriminate.
      - unfold must_precede in Hm. cbn in Hm. destruct Hm as [[] _]. }
    split; intros Hb; destruct (before_split _ _ _ Hb) as [Heq | (d & _ & Hd)];
      solve [discriminate | exact (Hno d Hd)].
  Qed.

  (** The semantic counterpart: on the call's local queue, the invocation
      of [Y] is on the frontier while the response of [X] is pending. *)
  Example m4_invY_overtakes_resX t h a :
    local_frontier [res_tev (E := RlxSig) (F := PairSig) (t, h) 0 (MRead X) a]
      (invD_tev (E := RlxSig) (F := PairSig) (t, h) [@Build_FutureEntry RlxSig 0 (@Resolved RlxSig (MRead X) a)] no_deps 1 (MRead Y)).
  Proof.
    constructor; [| constructor]. unfold must_precede. cbn. intros [[] _].
  Qed.

  (** ** (b) Two calls of the same thread

      Overlay [XYSig] (well-formed, latest-review M-13: [RdX] and [WrY] are
      semi-independent of each other, not of themselves); [RdX] reads the
      abstract [x], [WrY] sets the abstract [y] to [1].  [k1] reads [X],
      [k2] writes [Y]; both methods are blocking calls.
      [two_calls_reorder] (below, in the section "(b), M-12, m-18: the
      reordering", after the M-14 await example): on the configuration
      of [two_calls_init], the tagged frontier emits [k2]'s invocation
      before [k1]'s invocation and response.  [rdx_sound], [wry_sound]:
      both methods satisfy the triple under the same [I5], [R5], [G5];
      [xy_rlhl2]: the RLHL-2 bundle holds.  The two-call configuration is
      derived from two [tagged_invoke] steps and its invariant is checked
      against every later module step in [two_calls_*] below. *)

  Inductive XYOp : Type := RdX | WrY.

  Definition xy_ar (o : XYOp) : Type :=
    match o with RdX => nat | WrY => unit end.

  Canonical Structure XYEffect : Sig.t := {| Sig.op := XYOp; Sig.ar := xy_ar |}.

  Definition XYSig : RelaxedSig.t :=
    {|
      RelaxedSig.effect := XYEffect;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := fun o1 o2 => o1 <> o2;
      RelaxedSig.mode := fun _ => Local;
    |}.

  Lemma XYSig_wf : RelaxedSig.well_formed XYSig.
  Proof. constructor; [intros x H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

  (** Abstract state [(x, y)]: [RdX] returns [x]; [WrY] sets [y] to [1]. *)
  Definition xy_step (ev : ThreadEvent XYSig) (v v' : nat * nat) : Prop :=
    match te_ev _ ev with
    | InvEv _ _ => v' = v
    | ResEv _ op r =>
        match op return xy_ar op -> Prop with
        | RdX => fun r => r = fst v /\ v' = v
        | WrY => fun _ => v' = (fst v, 1)
        end r
    end.

  Definition XYLTS : LTS XYSig :=
    {| State := (nat * nat)%type; Step := xy_step; Error := NoError |}.

  Abbreviation XOk v pool := (@PossOk XYSig XYLTS v pool).

  Lemma xy_noop t h o v : Step XYLTS (Build_ThreadEvent t (@InvEv XYSig h o)) v v.
  Proof. reflexivity. Qed.

  Definition M5 : RelaxedModuleImpl RlxSig XYSig :=
    fun op t => match op as o return Prog RlxSig (Sig.ar o) with
                | RdX => @call RlxSig (MRead X)
                | WrY => @call RlxSig (MWrite Y 1)
                end.

  Definition t5 : tid := 3%positive.
  Definition k1 : CallKey XYSig := (t5, 1).
  Definition k2 : CallKey XYSig := (t5, 2).

  Abbreviation XA := (Assn MemLTS XYLTS).

  Definition I5 : XA :=
    fun s => exists y pool, ps_poss s = XOk (ps_mem s X, y) pool /\ lin_pool_well_formed pool.

  (** Rely of a call [k]: other calls keep [X], the abstract [x], and the
      entries of [k] (up to helping). *)
  Definition R5 (k : CallKey XYSig) : PRel MemLTS XYLTS :=
    fun s s' => ps_mem s' X = ps_mem s X /\
      exists v pool v' pool', ps_poss s = XOk v pool /\ ps_poss s' = XOk v' pool' /\ fst v' = fst v /\
        keeps k pool pool'.

  (** Guarantee of a call [k]: it keeps [X], the abstract [x], and the
      entries of every other call (up to helping). *)
  Definition G5 (k : CallKey XYSig) : PRel MemLTS XYLTS :=
    fun s s' => ps_mem s' X = ps_mem s X /\
      exists v pool v' pool', ps_poss s = XOk v pool /\ ps_poss s' = XOk v' pool' /\ fst v' = fst v /\
        (forall k', k' <> k -> keeps k' pool pool').

  Lemma G5_in_R5 k k' s s' : k' <> k -> G5 k' s s' -> R5 k s s'.
  Proof.
    intros Hne (HX & v & pool & v' & pool' & Hp & Hp' & Hv & Hl). split; [exact HX |].
    exists v, pool, v', pool'. repeat split; auto.
  Qed.

  Lemma R5_keeps k : KeepsRel k (R5 k).
  Proof.
    intros s s' (_ & v & pool & v' & pool' & Hp & Hp' & _ & Hk) v1 pool1 Hp1.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists v', pool'. auto.
  Qed.

  Lemma I5_return k op r s p2 :
    I5 s -> poss_return XYLTS (fst k) (snd k) op r (ps_poss s) p2 -> I5 (ps_mem s, p2, ps_ghost s).
  Proof.
    destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd]. intros HI Hret.
    destruct Hret as [st pool1 pool2 Hrem].
    destruct HI as (y & pool & Hp & Hwf). cbn in Hp. injection Hp as -> <-.
    exists y, pool2. cbn. split; [reflexivity | eapply lin_remove_well_formed; eauto].
  Qed.

  Lemma I5_invoke k op σ p γ p' γ' :
    I5 (σ, p, γ) -> poss_invoke XYLTS (fst k) (snd k) op p p' -> I5 (σ, p', γ').
  Proof.
    intros HI Hinv. destruct Hinv as [st pool1 pool2 Hins].
    destruct HI as (y & pool & Hp & Hwf). cbn in Hp. injection Hp as -> <-.
    exists y, pool2. cbn. split; [reflexivity | eapply lin_insert_well_formed; eauto].
  Qed.

  Section XYProofs.
    Context (t : tid).

    Definition P5 (o : XYOp) (h : nat) : XA := fun s => KPh (VE := MemLTS) (VF := XYLTS) (t, h) o s /\ I5 s.
    Definition Q5 (h : nat) (r : nat) : XA := fun s => KLr (VE := MemLTS) (VF := XYLTS) (t, h) RdX r s /\ I5 s.
    Definition QW5 (h : nat) (r : unit) : XA := fun s => KLr (VE := MemLTS) (VF := XYLTS) (t, h) WrY r s /\ I5 s.

    Lemma P5_stable o h : Stable I5 (R5 (t, h)) (P5 o h).
    Proof. apply Stable_and; [apply KPh_stable, R5_keeps | apply Stable_I]. Qed.

    Lemma Q5_stable h r : Stable I5 (R5 (t, h)) (Q5 h r).
    Proof. apply Stable_and; [apply KLr_stable, R5_keeps | apply Stable_I]. Qed.

    Lemma QW5_stable h r : Stable I5 (R5 (t, h)) (QW5 h r).
    Proof. apply Stable_and; [apply KLr_stable, R5_keeps | apply Stable_I]. Qed.

    Lemma pupdate_id5 (k : CallKey XYSig) (P : XA) ev :
      (forall σ σ', Step MemLTS ev σ σ' -> σ' = σ) ->
      (forall σ p γ γ', P (σ, p, γ) -> P (σ, p, γ')) ->
      (forall s, P s -> I5 s) ->
      PUpdate (VE := MemLTS) (VF := XYLTS) k (G5 k) ev P P.
    Proof.
      intros Hev HP HPI σ p γ γ' Hs _ σ' Hst. apply Hev in Hst. subst σ'.
      exists p. split; [apply rt_refl |]. split; [eapply HP; exact Hs |].
      destruct (HPI _ Hs) as (y & pool & Hp & _). cbn in Hp.
      split; [reflexivity |]. exists (σ X, y), pool, (σ X, y), pool.
      repeat split; auto. intros; apply keeps_refl.
    Qed.

    Lemma chain_PI5 o h s : PostInvoke I5 (t, h) o (fun _ => True) s -> P5 o h s.
    Proof.
      destruct s as [[σ p] γ]. intros Hs. pose proof Hs as (p0 & γ0 & evs & HI0 & Hinv & _).
      split; [eapply pinit_KPh; [| exact Hs] |]; eapply I5_invoke; eauto.
    Qed.

    (** [k1]'s method, through the blocking fragment: [call (MRead X)]. *)
    Lemma rdx_chain : MethodProvableChain I5 R5 G5 M5 t RdX (P5 RdX) Q5.
    Proof.
      constructor.
      - apply chain_PI5.
      - intros h s [_ HI]. exact HI.
      - intros h. apply P5_stable.
      - intros h r s p2 [_ HI] Hret. eapply I5_return with (k := (t, h)); eauto.
      - intros h r s [(v & pool & Hp & Hl) _]. exists v, pool. auto.
      - intros h. cbn. unfold call.
        apply cprov_call with (P' := P5 RdX h) (Q' := Q5 h).
        + intros s [_ HI]. exact HI.
        + intros r s [_ HI]. exact HI.
        + apply P5_stable.
        + intros r. apply Q5_stable.
        + intros h'. apply pupdate_id5; [intros σ σ' H; exact H | intros σ p γ γ' H; exact H | intros s [_ H]; exact H].
        + (* the response: help, then linearize the call *)
          intros h' r σ p γ γ' [(v & pool & Hp & Hph) (y & pool1 & Hp1 & Hwf)] _ σ' Hst.
          cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hst. destruct Hst as [-> ->].
          rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
          destruct (linearize_response XYLTS (t, h) RdX (σ X) (σ X, y) (σ X, y) pool
                      (fun t' h' o' => xy_noop t' h' o' _) Hwf Hph (conj eq_refl eq_refl))
            as (pool' & Hps & Hl' & Hwf' & Hkeep).
          exists (XOk (σ X, y) pool'). split; [exact Hps |].
          split; [split; [exists (σ X, y), pool'; split; [reflexivity | exact Hl'] | exists y, pool'; split; [reflexivity | exact Hwf']] |].
          split; [reflexivity |]. exists (σ X, y), pool, (σ X, y), pool'. repeat split; auto.
        + intros r. apply cprov_ret. intros s Hs. exact Hs.
    Qed.

    (** [k2]'s method: [call (MWrite Y 1)] (latest-review M-12). *)
    Lemma wry_chain : MethodProvableChain I5 R5 G5 M5 t WrY (P5 WrY) QW5.
    Proof.
      constructor.
      - apply chain_PI5.
      - intros h s [_ HI]. exact HI.
      - intros h. apply P5_stable.
      - intros h r s p2 [_ HI] Hret. eapply I5_return with (k := (t, h)); eauto.
      - intros h r s [(v & pool & Hp & Hl) _]. exists v, pool. auto.
      - intros h. cbn. unfold call.
        apply cprov_call with (P' := P5 WrY h) (Q' := QW5 h).
        + intros s [_ HI]. exact HI.
        + intros r s [_ HI]. exact HI.
        + apply P5_stable.
        + intros r. apply QW5_stable.
        + intros h'. apply pupdate_id5; [intros σ σ' H; exact H | intros σ p γ γ' H; exact H | intros s [_ H]; exact H].
        + (* the write response: help, then linearize the call *)
          intros h' u σ p γ γ' [(v & pool & Hp & Hph) (y & pool1 & Hp1 & Hwf)] _ σ' Hst.
          cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hst. subst σ'.
          rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
          destruct u.
          destruct (linearize_response XYLTS (t, h) WrY tt (σ X, y) (σ X, 1) pool
                      (fun t' h' o' => xy_noop t' h' o' _) Hwf Hph eq_refl)
            as (pool' & Hps & Hl' & Hwf' & Hkeep).
          exists (XOk (σ X, 1) pool'). split; [exact Hps |].
          split; [split; [exists (σ X, 1), pool'; split; [reflexivity | exact Hl'] | exists 1, pool'; split; [reflexivity | exact Hwf']] |].
          split; [reflexivity |]. exists (σ X, y), pool, (σ X, 1), pool'. repeat split; auto.
        + intros r. apply cprov_ret. intros s Hs. exact Hs.
    Qed.
  End XYProofs.

  Theorem rdx_sound t : MethodSem I5 R5 G5 M5 t RdX.
  Proof. eapply chain_sound. apply rdx_chain. Qed.

  Theorem wry_sound t : MethodSem I5 R5 G5 M5 t WrY.
  Proof. eapply chain_sound. apply wry_chain. Qed.

  Lemma I5_init : I5 (σ0, XOk (0, 0) [], []).
  Proof. exists 0, []. split; [reflexivity | constructor]. Qed.

  Theorem xy_rlhl2 : RLHL2Hyps I5 R5 G5 M5 σ0 (0, 0).
  Proof.
    constructor.
    - intros t [|]; [apply rdx_sound | apply wry_sound].
    - intros k k' s s' Hne HG. apply (G5_in_R5 k' k s s' Hne HG).
    - intros k k' op tr ret [[σ p] γ] p' Hne _ HI Hinv. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
      destruct HI as (y & pool & Hp & _). cbn in Hp. subst p.
      inversion Hinv as [st pool1 pool2 Hins]; subst.
      split; [reflexivity |]. exists (σ X, y), pool, (σ X, y), pool2.
      split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
      eapply keeps_insert. exact Hins.
    - intros k k' op r [[σ p] γ] p2 Hne HI Hret _. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
      destruct HI as (y & pool & Hp & _). cbn in Hp. subst p.
      inversion Hret as [st pool1 pool2 Hrem]; subst.
      split; [reflexivity |]. exists (σ X, y), pool, (σ X, y), pool2.
      split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
      eapply keeps_remove_other; [exact Hrem |]. destruct k. intros Heq. apply Hne. symmetry. exact Heq.
    - intros s (y & pool & Hp & Hwf). exists (ps_mem s X, y), pool. auto.
    - exact I5_init.
  Qed.

  (** ** M-11 (i): a negative own-reordering check

      [rw_body]: [w <- ?wr(X, 1); r <- ?rd(X); wait w; a <- wait r; ret a],
      both futures with empty tags.  The two invocations are ordered by
      (F2) (same location), but the two responses are not, so the read's
      response may be emitted before the write's response, i.e. before the
      write takes effect in [MemLTS]: the read returns [0].
      [own_reorder_not_one]: "the result is [1]" ([OneLTS]) is not
      [MethodSem], for any [I], [R], [G] with [I] true initially (the rely
      is never used); [own_reorder_le1_sound]: "the result is [0] or [1]"
      ([LeLTS]) is derivable. *)

  Inductive OneOp : Type := Get.

  Definition one_ar (o : OneOp) : Type := match o with Get => nat end.

  Canonical Structure OneEffect : Sig.t := {| Sig.op := OneOp; Sig.ar := one_ar |}.

  Definition OneSig : RelaxedSig.t :=
    {| RelaxedSig.effect := OneEffect; RelaxedSig.handle := nat;
       RelaxedSig.semi_independent := fun _ _ => False; RelaxedSig.mode := fun _ => Local |}.

  Lemma OneSig_wf : RelaxedSig.well_formed OneSig.
  Proof. constructor; [intros x H; exact H | intros _ _ [] | intros _ _ []]. Qed.

  Definition one_step (P : nat -> Prop) (ev : ThreadEvent OneSig) (v v' : unit) : Prop :=
    match te_ev _ ev with
    | InvEv _ _ => True
    | ResEv _ op r => match op return one_ar op -> Prop with Get => fun r => P r end r
    end.

  Definition OneLTS : LTS OneSig := {| State := unit; Step := one_step (fun r => r = 1); Error := NoError |}.
  Definition LeLTS : LTS OneSig := {| State := unit; Step := one_step (fun r => r <= 1); Error := NoError |}.

  Definition rw_body : Prog RlxSig nat :=
    @FutureD RlxSig nat (MWrite X 1) no_deps (fun fw =>
    @FutureD RlxSig nat (MRead X) no_deps (fun fr =>
    Wait fw (fun _ => Wait fr (fun (a : nat) => Ret a)))).

  Definition Mrw : RelaxedModuleImpl RlxSig OneSig :=
    fun op t => match op as o return Prog RlxSig (Sig.ar o) with Get => rw_body end.

  Definition kr : CallKey OneSig := (t0, 0).
  Definition iw : ThreadEvent RlxSig := Build_ThreadEvent t0 (@InvEv RlxSig 0 (MWrite X 1)).
  Definition ir : ThreadEvent RlxSig := Build_ThreadEvent t0 (@InvEv RlxSig 1 (MRead X)).
  Definition rsw : ThreadEvent RlxSig := Build_ThreadEvent t0 (@ResEv RlxSig 0 (MWrite X 1) tt).
  Definition rsr (v : nat) : ThreadEvent RlxSig := Build_ThreadEvent t0 (@ResEv RlxSig 1 (MRead X) v).

  Lemma rw_trace a :
    exists tr, program_produces_tagged t0 (Mrw Get t0) tr a /\ map untag tr = [iw; ir; rsw; rsr a].
  Proof.
    eexists. split.
    - eexists. split.
      + cbn. eapply tagged_execution_emit.
        { apply tagged_futureD with (h := 0). unfold handle_fresh. cbn. tauto. }
        eapply tagged_execution_emit.
        { apply tagged_futureD with (h := 1). unfold handle_fresh. cbn. intros [H | []]. discriminate. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending RlxSig nat t0 (MWrite X 1) 0 tt).
          apply resolve_next; [discriminate | apply resolve_here]. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending RlxSig nat t0 (MRead X) 1 a). apply resolve_here. }
        apply tagged_execution_refl.
      + apply program_terminal_ret. repeat constructor.
    - reflexivity.
  Qed.

  Definition one_good (p : Poss OneLTS) : Prop :=
    exists v pool, p = @PossOk OneSig OneLTS v pool /\
      forall e, In e pool -> match lin_state _ e with
                             | ls_linr op r => match op return one_ar op -> Prop with Get => fun r => r = 1 end r
                             | _ => True end.

  Lemma one_good_steps p p' : one_good p -> poss_steps OneLTS p p' -> one_good p'.
  Proof.
    intros Hg Hs. induction Hs as [p p' (o & Hs) | p | p p1 p' Hs1 IH1 Hs2 IH2]; auto.
    destruct Hs as [t h op st st' pool0 pool' Hlin Hlts | t h op ret st st' pool0 pool' Hlin Hlts
                   | t h op st pool0 Hlin Herr | t h op ret st pool0 Hlin Herr];
      destruct Hg as (v1 & pool1 & Hp & Hall); injection Hp as Hst Hpool; subst.
    - exists st', pool'. split; [reflexivity |]. intros e He.
      apply lin_invoke_update_is_update in Hlin.
      destruct (lin_update_in _ _ _ _ _ _ Hlin He) as [He0 | ->]; [apply Hall; exact He0 | exact Logic.I].
    - exists st', pool'. split; [reflexivity |]. intros e He.
      destruct (lin_update_in _ _ _ _ _ _ Hlin He) as [He0 | ->]; [apply Hall; exact He0 |].
      destruct op. exact Hlts.
    - destruct Herr.
    - destruct Herr.
  Qed.

  Theorem own_reorder_not_one (I : Assn MemLTS OneLTS) (R G : CallKey OneSig -> PRel MemLTS OneLTS) :
    I (σ0, @PossOk OneSig OneLTS tt [], []) -> ~ MethodSem I R G Mrw t0 Get.
  Proof.
    intros HI0 Hsem. destruct (rw_trace 0) as (tr & Hprod & Htr).
    destruct (Hsem 0 tr 0 Hprod) as (A & [Hemit _ Hret] & Hinit).
    destruct (Hinit σ0 (@PossOk OneSig OneLTS tt []) [] (@PossOk OneSig OneLTS tt [make_lin_entry kr (@ls_inv OneSig Get)]) HI0)
      as [HI HA].
    { constructor. constructor. intros []. }
    destruct tr as [| m1 [| m2 [| m3 [| m4 [| m5 tr]]]]]; try discriminate.
    cbn in Htr. injection Htr as H1 H2 H3 H4.
    assert (Hg0 : [] ++ ghost_new (@pair tid (RelaxedSig.handle OneSig) t0 0) [m1; m2; m3; m4] = [Build_ScheduledEvent kr iw; Build_ScheduledEvent kr ir]).
    { unfold ghost_new. cbn [map app]. rewrite H1, H2, H3, H4. reflexivity. }
    rewrite Hg0 in HI, HA.
    (* the two invocations, in order *)
    destruct (Hemit [] m1 [m2; m3; m4] ltac:(constructor) σ0 _ _ [Build_ScheduledEvent kr ir] ltac:(rewrite H1; cbn; exists [], [Build_ScheduledEvent kr ir]; split; [reflexivity | split; [reflexivity | constructor]]) HA HI σ0)
      as (p1 & Hps1 & HA1 & HI1 & _).
    { rewrite H1. reflexivity. }
    destruct (Hemit [] m2 [m3; m4] ltac:(constructor) σ0 p1 _ [] ltac:(rewrite H2; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA1 HI1 σ0)
      as (p2 & Hps2 & HA2 & HI2 & _).
    { rewrite H2. reflexivity. }
    (* the read's response overtakes the write's response: it reads 0 *)
    destruct (Hemit [m3] m4 [] ltac:(constructor; [| constructor]; unfold must_precede; rewrite H3, H4; cbn; tauto) σ0 p2 [] [] ltac:(rewrite H4; reflexivity) HA2 HI2 σ0)
      as (p3 & Hps3 & HA3 & HI3 & _).
    { rewrite H4. cbn. split; reflexivity. }
    (* the write's response *)
    destruct (Hemit [] m3 [] ltac:(constructor) σ0 p3 [] [] ltac:(rewrite H3; reflexivity) HA3 HI3 (upd σ0 X 1))
      as (p4 & Hps4 & HA4 & HI4 & _).
    { rewrite H3. reflexivity. }
    destruct (Hret (upd σ0 X 1, p4, []) HA4 HI4 ltac:(intros e [])) as (p5 & Hps5 & (v & pool & Hp5 & Hlk) & _).
    assert (Hg : one_good p5).
    { eapply one_good_steps; [| exact Hps5]. cbn [ps_poss fst snd].
      eapply one_good_steps; [| exact Hps4]. eapply one_good_steps; [| exact Hps3].
      eapply one_good_steps; [| exact Hps2]. eapply one_good_steps; [| exact Hps1].
      eexists _, _. split; [reflexivity |]. intros e [<- | []]. exact Logic.I. }
    destruct Hg as (v' & pool' & Hp' & Hall). rewrite Hp5 in Hp'. injection Hp' as _ <-.
    specialize (Hall _ Hlk). cbn in Hall. discriminate Hall.
  Qed.

  (** The positive counterpart: [0] or [1]. *)
  Abbreviation LOk v pool := (@PossOk OneSig LeLTS v pool).
  Abbreviation LA := (Assn MemLTS LeLTS).

  Definition Irw : LA := fun s => exists pool, ps_poss s = LOk tt pool /\ ps_mem s X <= 1 /\ lin_pool_well_formed pool.

  Definition Rrw (k : CallKey OneSig) : PRel MemLTS LeLTS := fun s s' =>
    exists pool pool', ps_poss s = LOk tt pool /\ ps_poss s' = LOk tt pool' /\ keeps k pool pool'.

  Definition Grw (k : CallKey OneSig) : PRel MemLTS LeLTS := fun s s' =>
    exists pool pool', ps_poss s = LOk tt pool /\ ps_poss s' = LOk tt pool' /\
      forall k', k' <> k -> keeps k' pool pool'.

  Definition OwnRW : PRel MemLTS LeLTS := fun s s' =>
    exists pool, ps_poss s = LOk tt pool /\ ps_poss s' = LOk tt pool.

  Lemma Rrw_keeps k : KeepsRel k (Rrw k).
  Proof.
    intros s s' (pool & pool' & Hp & Hp' & Hk) v1 pool1 Hp1.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists tt, pool'. auto.
  Qed.

  Abbreviation KPhG k := (KPh (VE := MemLTS) (VF := LeLTS) k Get).

  Definition rw_slot (k : CallKey OneSig) (ev : TaggedEvent RlxSig) (post : LA) : Slot MemLTS LeLTS :=
    mkSlot ev (KPhG k) (fun _ => KPhG k) (fun s => post s /\ KPhG k s) OwnRW.

  Definition RWShape (k : CallKey OneSig) (sl : Slot MemLTS LeLTS) : Prop :=
    exists ev post, sl = rw_slot k ev post.

  Lemma rw_ns k Pinit (Γ : list (Slot MemLTS LeLTS)) ev (post : LA) :
    Forall (RWShape k) Γ -> Impl Irw Pinit (KPhG k) -> Stable Irw (Rrw k) post ->
    (forall σ p γ σ', Irw (σ, p, γ) -> Step MemLTS (untag ev) σ σ' ->
       forall γ', post (σ', p, γ') /\ Irw (σ', p, γ')) ->
    NewSlotOK Irw Rrw Grw k Pinit Γ (rw_slot k ev post).
  Proof.
    intros HΓ Hpinit Hpost Hstep. rewrite Forall_forall in HΓ.
    assert (Hshape : forall g sg, nth_error Γ g = Some sg -> RWShape k sg)
      by (intros g sg Hg; apply HΓ; eapply nth_error_In; eauto).
    assert (HownR : forall s s', OwnRW s s' -> Rrw k s s').
    { intros s s' (pool & Hp & Hp'). exists pool, pool. repeat split; auto. apply keeps_refl. }
    apply newslot_guar_in_rely; cbn [sl_ev sl_start sl_in sl_post sl_guar rw_slot].
    - intros g sg Hg. destruct (Hshape g sg Hg) as (ev' & post' & ->). cbn. exact HownR.
    - intros y sy Hy. destruct (Hshape y sy Hy) as (ev' & post' & ->). cbn.
      split; [apply KPh_stable, Rrw_keeps | intros; apply KPh_stable, Rrw_keeps].
    - exact HownR.
    - intros s0 s1 (pool & Hp & Hp'). exists pool, pool. repeat split; auto. intros; apply keeps_refl.
    - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar rw_slot].
      intros σ p γ γ' [HK _] HI _ σ' Hst. destruct (Hstep σ p γ σ' HI Hst γ') as [Hp' HI'].
      exists p. split; [apply rt_refl |]. split; [split; [exact Hp' | exact HK] |].
      split; [exact HI' |]. destruct HI as (pool & Hp & _). exists pool. auto.
    - exact Hpinit.
    - intros d sd _ Hd. destruct (Hshape d sd Hd) as (ev' & post' & ->). cbn.
      intros s _ [_ H]. exact H.
    - apply KPh_stable, Rrw_keeps.
    - intros; apply KPh_stable, Rrw_keeps.
  Qed.

  Ltac shape_tac := repeat (first [apply Forall_nil | apply Forall_cons | apply Forall_app; split | eexists _, _; reflexivity]).

  Section RWProof.
    Context (t : tid) (h : nat).
    Local Abbreviation krw := (@pair tid (RelaxedSig.handle OneSig) t h).
    Abbreviation Prw := (PostInvoke Irw krw Get (fun _ => True)).

    Definition Qrw (a : nat) : LA := fun s => a <= 1 /\ KPhG krw s.

    Lemma rw_derivation :
      RProvable Irw Rrw Grw krw Prw
        (fun a Γ H => Close Irw Rrw Grw krw Prw Qrw a Γ H /\ True) [] empty_store (Mrw Get t).
    Proof.
      assert (Hpinit : Impl Irw Prw (KPhG krw)) by apply pinit_KPh.
      assert (Htrue : Stable Irw (Rrw krw) (fun _ => True)) by apply Stable_true.
      cbn. unfold rw_body.
      apply rp_futureD with (sl := fun hw => rw_slot krw (invD_tev (E := RlxSig) (F := OneSig) krw empty_store no_deps hw (MWrite X 1)) (fun _ => True)).
      { intros; reflexivity. }
      { intros hw _. apply rw_ns; [constructor | exact Hpinit | exact Htrue |].
        cbn. intros σ p γ σ' HI -> γ'. split; [exact Logic.I |].
        destruct HI as (pool & Hp & HX & Hwf). exists pool. auto. }
      intros hw Hfw. cbv beta.
      apply rp_futureD with (sl := fun hr => rw_slot krw (invD_tev (E := RlxSig) (F := OneSig) krw (add_pending hw (MWrite X 1) empty_store) no_deps hr (MRead X)) (fun _ => True)).
      { intros; reflexivity. }
      { intros hr _. apply rw_ns; [shape_tac | exact Hpinit | exact Htrue |].
        cbn. intros σ p γ σ' HI -> γ'. split; [exact Logic.I |].
        destruct HI as (pool & Hp & HX & Hwf). exists pool. auto. }
      intros hr Hfr. cbv beta.
      apply rp_wait_pending with (sl := fun u => rw_slot krw (res_tev (E := RlxSig) (F := OneSig) krw hw (MWrite X 1) u) (fun _ => True)).
      { right. left. reflexivity. }
      { intros; reflexivity. }
      { intros u. apply rw_ns; [shape_tac | exact Hpinit | exact Htrue |].
        cbn. intros σ p γ σ' HI -> γ'. split; [exact Logic.I |].
        destruct HI as (pool & Hp & HX & Hwf). exists pool. cbn. repeat split; auto. }
      intros u H3 Hres3. cbv beta.
      apply rp_wait_pending with (sl := fun a => rw_slot krw (res_tev (E := RlxSig) (F := OneSig) krw hr (MRead X) a) (fun _ => a <= 1)).
      { unfold pending_at. eapply resolve_store_keep_pending; [exact Hres3 | left; reflexivity |].
        intros Heq. cbn in Heq. apply Hfr. rewrite Heq. left. reflexivity. }
      { intros; reflexivity. }
      { intros a. apply rw_ns; [shape_tac | exact Hpinit | intros s s' Hs _ _; exact Hs |].
        cbn. intros σ p γ σ' HI [-> ->] γ'. destruct HI as (pool & Hp & HX & Hwf).
        split; [exact HX |]. exists pool. auto. }
      intros a H4 Hres4. cbv beta. apply rp_ret. split; [| exact Logic.I].
      apply close_done with
        (fin := fun d => match d with 3 => fun _ => a <= 1 | _ => fun _ => True end)
        (fin0 := KPhG krw).
      - eapply (resolve_two hw _ _ hr); [| exact Hres3 | exact Hres4].
        intros Heq. apply Hfr. rewrite Heq. left. reflexivity.
      - apply barrier_guar_in_rely.
        + intros g sg Hg s s' Hs.
          destruct g as [| [| [| [| g]]]]; cbn in Hg; try (destruct g; discriminate);
            injection Hg as <-; destruct Hs as (pool & Hp & Hp');
            exists pool, pool; repeat split; auto; apply keeps_refl.
        + intros d sd Hd.
          destruct d as [| [| [| [| d]]]]; cbn in Hd; try (destruct d; discriminate);
            injection Hd as <-; cbn; intros s _ Hs; try exact Logic.I; apply Hs.
        + exact Hpinit.
        + intros d s s' Hs _ _. destruct d as [| [| [| [| d]]]]; exact Hs.
        + apply KPh_stable, Rrw_keeps.
        + intros s _ HK Hfin. split; [exact (Hfin 3 _ eq_refl Logic.I) | exact HK].
    Qed.
  End RWProof.

  Lemma rw_provable t : MethodProvable Irw Rrw Grw Mrw t Get (fun _ _ => True) (fun h => Qrw t h).
  Proof.
    constructor.
    - intros h [[σ p] γ] (p0 & γ0 & evs & (pool0 & Hp0 & HX & Hwf) & Hinv & _).
      cbn [ps_poss ps_mem ps_ghost fst snd] in *. destruct Hinv as [st pool pool' Hins].
      injection Hp0 as -> <-. exists pool'. split; [reflexivity |]. split; [exact HX |].
      eapply lin_insert_well_formed; eauto.
    - intros h r [[σ p] γ] (Hr & v & pool & Hp & Hph) (pool1 & Hp1 & HX & Hwf) _.
      cbn [ps_poss ps_mem ps_ghost fst snd] in *.
      rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
      destruct (linearize_response LeLTS (t, h) Get r tt tt pool (fun _ _ _ => Logic.I) Hwf Hph Hr)
        as (pool' & Hps & Hl' & Hwf' & Hkeep).
      exists (LOk tt pool'). cbn [ps_poss ps_mem ps_ghost fst snd].
      split; [exact Hps |]. split; [eexists _, _; split; [reflexivity | exact Hl'] |].
      split; [exists pool'; auto |].
      split; [apply r_step; exists pool, pool'; repeat split; auto |].
      intros p2 Hret. inversion Hret as [st pool3 pool4 Hrem]; subst.
      exists pool4. split; [reflexivity |]. split; [exact HX |]. eapply lin_remove_well_formed; eauto.
    - intros h. exact (rw_derivation t h).
  Qed.

  Theorem own_reorder_le1_sound t : MethodSem Irw Rrw Grw Mrw t Get.
  Proof. eapply method_sound. apply rw_provable. Qed.

  Lemma rw_init : Irw (σ0, LOk tt [], []).
  Proof. exists []. split; [reflexivity |]. split; [exact (le_S _ _ (le_n 0)) | constructor]. Qed.

  (** m-19: a single-call check ([Grw] is not claimed to be in [Rrw] of
      another call; no [RLHL2Hyps] instance). *)
  Corollary own_reorder_le1_single_call : Irw (σ0, LOk tt [], []) /\ forall t, MethodSem Irw Rrw Grw Mrw t Get.
  Proof. split; [exact rw_init | exact own_reorder_le1_sound]. Qed.

  (** ** M-11 (ii): interference premises that need the dependency dag

      [tas_body]: a test-and-set of [X] followed by an independent flag
      write of [Y]:
      [r <- ?rd(X); a <- wait r; w <- wr(X, 1) (tag: resolved = {r});
       wait w; y <- ?wr(Y, 1) (empty tag); wait y; ret a].
      The write of [Y] is ordered after nothing, so it may fire anywhere
      among the [X] events (its own-interference premises are discharged
      by stability: it changes neither [X] nor the possibility).  The
      response of the write of [X] linearizes the call ([GL]: [X := 1],
      abstract flag [1]); its guarantee would break the edge assertions
      [σX = a] and "the call has not linearized" of the earlier [X] events,
      but each of these events is ordered before it by the dag
      ((F1) [0 -> 1], (F3) [1 -> 2], (F1) [2 -> 3]), so the corresponding
      premises [ns_if_old_start] / [ns_if_old_in] hold by their
      [~ before] hypothesis ([tas_before]).  They are not provable by
      stability ([tas_needs_order]), and [newslot_guar_in_rely] does not
      apply: [GL] is not in the rely, which freezes [X]
      ([tas_guar_not_in_rely]).  The implementation is not atomic, so the
      rely [RT] excludes other writers of [X]; [GT k ⊆ RT k'] is not
      claimed for this instance. *)

  Inductive TOp : Type := TAS.

  Definition t_ar (o : TOp) : Type := match o with TAS => nat end.

  Canonical Structure TEffect : Sig.t := {| Sig.op := TOp; Sig.ar := t_ar |}.

  Definition TSig : RelaxedSig.t :=
    {| RelaxedSig.effect := TEffect; RelaxedSig.handle := nat;
       RelaxedSig.semi_independent := fun _ _ => False; RelaxedSig.mode := fun _ => Local |}.

  Lemma TSig_wf : RelaxedSig.well_formed TSig.
  Proof. constructor; [intros x H; exact H | intros _ _ [] | intros _ _ []]. Qed.

  (** The flag: [TAS] returns it and sets it to [1]. *)
  Definition t_step (ev : ThreadEvent TSig) (v v' : nat) : Prop :=
    match te_ev _ ev with
    | InvEv _ _ => v' = v
    | ResEv _ op r => match op return t_ar op -> Prop with TAS => fun r => r = v /\ v' = 1 end r
    end.

  Definition TLTS : LTS TSig := {| State := nat; Step := t_step; Error := NoError |}.

  Abbreviation TOk v pool := (@PossOk TSig TLTS v pool).
  Abbreviation TA := (Assn MemLTS TLTS).

  Lemma t_noop t h o v : Step TLTS (Build_ThreadEvent t (@InvEv TSig h o)) v v.
  Proof. reflexivity. Qed.

  Definition tas_body : Prog RlxSig nat :=
    @FutureD RlxSig nat (MRead X) no_deps (fun fx => Wait fx (fun (a : nat) =>
    @Future RlxSig nat (MWrite X 1) (fun fw => Wait fw (fun _ =>
    @FutureD RlxSig nat (MWrite Y 1) no_deps (fun fy => Wait fy (fun _ => Ret a)))))).

  Definition Mtas : RelaxedModuleImpl RlxSig TSig :=
    fun op t => match op as o return Prog RlxSig (Sig.ar o) with TAS => tas_body end.

  Definition IT : TA := fun s => exists v pool, ps_poss s = TOk v pool /\ v = ps_mem s X /\ v <= 1 /\
                                               lin_pool_well_formed pool.

  Definition RT (k : CallKey TSig) : PRel MemLTS TLTS := fun s s' =>
    ps_mem s' X = ps_mem s X /\
    exists v pool pool', ps_poss s = TOk v pool /\ ps_poss s' = TOk v pool' /\ keeps k pool pool'.

  Definition GT (k : CallKey TSig) : PRel MemLTS TLTS := fun s s' =>
    exists v pool v' pool', ps_poss s = TOk v pool /\ ps_poss s' = TOk v' pool' /\
      forall k', k' <> k -> keeps k' pool pool'.

  Lemma RT_keeps k : KeepsRel k (RT k).
  Proof.
    intros s s' (_ & v & pool & pool' & Hp & Hp' & Hk) v1 pool1 Hp1.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists v, pool'. auto.
  Qed.

  (** The guarantees of the own events. *)
  Definition Gid : PRel MemLTS TLTS := fun s s' =>
    ps_mem s' = ps_mem s /\ exists v pool, ps_poss s = TOk v pool /\ ps_poss s' = TOk v pool.

  Definition GYw : PRel MemLTS TLTS := fun s s' =>
    ps_mem s' = upd (ps_mem s) Y 1 /\ exists v pool, ps_poss s = TOk v pool /\ ps_poss s' = TOk v pool.

  Definition GL (k : CallKey TSig) : PRel MemLTS TLTS := fun s s' =>
    ps_mem s' = upd (ps_mem s) X 1 /\
    exists v pool pool', ps_poss s = TOk v pool /\ ps_poss s' = TOk 1 pool' /\
      forall k', k' <> k -> keeps k' pool pool'.

  (** Assertions that do not read the ghost are stable under [Gid]. *)
  Lemma Gid_stable (P : TA) :
    (forall σ p γ γ', P (σ, p, γ) -> P (σ, p, γ')) -> Stable IT Gid P.
  Proof.
    intros HP [[σ p] γ] [[σ' p'] γ'] Hs (Hm & v & pool & Hp & Hp') _.
    cbn [ps_mem ps_poss ps_ghost fst snd] in *. subst σ'. rewrite Hp' , <- Hp. eapply HP. exact Hs.
  Qed.

  Lemma Gid_in_GT k s s' : Gid s s' -> GT k s s'.
  Proof. intros (_ & v & pool & Hp & Hp'). exists v, pool, v, pool. repeat split; auto. intros; apply keeps_refl. Qed.

  Section TASProof.
    Context (t : tid) (h : nat).
    Local Abbreviation kt := (@pair tid (RelaxedSig.handle TSig) t h).
    Abbreviation PT := (PostInvoke IT kt TAS (fun _ => True)).
    Abbreviation KPhT := (KPh (VE := MemLTS) (VF := TLTS) kt TAS).

    Definition XAt (a : nat) : TA := fun s => ps_mem s X = a /\ KPhT s.
    Definition KLrT (a : nat) : TA := KLr (VE := MemLTS) (VF := TLTS) kt TAS a.

    Definition tev0 hx := invD_tev (E := RlxSig) (F := TSig) kt empty_store no_deps hx (MRead X).
    Definition tev1 hx (a : nat) := res_tev (E := RlxSig) (F := TSig) kt hx (MRead X) a.
    Definition tev2 H2 hw := inv_tev (E := RlxSig) (F := TSig) kt H2 hw (MWrite X 1).
    Definition tev3 hw (u : unit) := res_tev (E := RlxSig) (F := TSig) kt hw (MWrite X 1) u.

    Definition tsl0 hx : Slot MemLTS TLTS := mkSlot (tev0 hx) KPhT (fun _ _ => True) KPhT Gid.
    Definition tsl1 hx a : Slot MemLTS TLTS := mkSlot (tev1 hx a) (fun _ => True) (fun _ => KPhT) (XAt a) Gid.
    Definition tsl2 H2 hw a : Slot MemLTS TLTS :=
      mkSlot (tev2 H2 hw) (fun _ => True) (fun d => if Nat.eqb d 1 then XAt a else fun _ => True) (XAt a) Gid.
    Definition tsl3 hw a u : Slot MemLTS TLTS :=
      mkSlot (tev3 hw u) (fun _ => True) (fun d => if Nat.eqb d 2 then XAt a else fun _ => True) (KLrT a) (GL kt).
    Definition tsl4 H4 hy : Slot MemLTS TLTS :=
      mkSlot (invD_tev (E := RlxSig) (F := TSig) kt H4 no_deps hy (MWrite Y 1)) (fun _ => True) (fun _ _ => True) (fun _ => True) Gid.
    Definition tsl5 hy (u : unit) : Slot MemLTS TLTS :=
      mkSlot (res_tev (E := RlxSig) (F := TSig) kt hy (MWrite Y 1) u) (fun _ => True) (fun _ _ => True) (fun _ => True) GYw.

    Lemma KPhT_RT : Stable IT (RT kt) KPhT.
    Proof. apply KPh_stable, RT_keeps. Qed.

    Lemma XA_RT a : Stable IT (RT kt) (XAt a).
    Proof.
      intros s s' [HX HK] Hr HI. split; [destruct Hr as [Hm _]; rewrite Hm; exact HX |].
      eapply KPhT_RT; eauto.
    Qed.

    Lemma KLrT_RT a : Stable IT (RT kt) (KLrT a).
    Proof. apply KLr_stable, RT_keeps. Qed.

    Lemma GYw_keeps (P : TA) :
      (forall σ p γ γ', P (σ, p, γ) -> P (upd σ Y 1, p, γ')) -> Stable IT GYw P.
    Proof.
      intros HP [[σ p] γ] [[σ' p'] γ'] Hs (Hm & v & pool & Hp & Hp') _.
      cbn [ps_mem ps_poss ps_ghost fst snd] in *. subst σ'. rewrite Hp', <- Hp. eapply HP. exact Hs.
    Qed.

    (** The dag: every [X] event before the linearizing response. *)
    Lemma tas_before hx a H2 hw u :
      resolved_in H2 hx -> forall y, y < 3 -> before [tev0 hx; tev1 hx a; tev2 H2 hw; tev3 hw u] y 3.
    Proof.
      intros Hres y Hy.
      assert (D01 : dprec [tev0 hx; tev1 hx a; tev2 H2 hw; tev3 hw u] 0 1)
        by (econstructor; [lia | reflexivity | reflexivity | unfold must_precede; cbn; reflexivity]).
      assert (D12 : dprec [tev0 hx; tev1 hx a; tev2 H2 hw; tev3 hw u] 1 2)
        by (econstructor; [lia | reflexivity | reflexivity | unfold must_precede; cbn; exact Hres]).
      assert (D23 : dprec [tev0 hx; tev1 hx a; tev2 H2 hw; tev3 hw u] 2 3)
        by (econstructor; [lia | reflexivity | reflexivity | unfold must_precede; cbn; reflexivity]).
      destruct y as [| [| [| y]]]; [| | | lia].
      - eapply before_step; [eapply before_step; [apply before_dprec; exact D01 | exact D12] | exact D23].
      - eapply before_step; [apply before_dprec; exact D12 | exact D23].
      - apply before_dprec. exact D23.
    Qed.

    Ltac gi := let H := fresh in intros ? ? ? ? H; exact H.

    Ltac slot_cases n Hn :=
      destruct n as [| [| [| [| [| [| n]]]]]]; cbn in Hn;
      try (destruct n; discriminate); try discriminate; injection Hn as <-;
      cbn [sl_ev sl_start sl_in sl_post sl_guar tsl0 tsl1 tsl2 tsl3 tsl4 tsl5].

    Lemma tas_derivation :
      RProvable IT RT GT kt PT
        (fun a Γ H => Close IT RT GT kt PT KLrT a Γ H /\ True) [] empty_store (Mtas TAS t).
    Proof.
      assert (Hpinit : Impl IT PT KPhT) by apply pinit_KPh.
      cbn. unfold tas_body.
      apply rp_futureD with (sl := tsl0); [intros; reflexivity | |].
      { intros hx _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar tsl0].
        - apply Gid_in_GT.
        - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar tsl0].
          intros σ p γ γ' [HK _] HI _ σ' Hst. cbn in Hst. subst σ'.
          exists p. split; [apply rt_refl |]. split; [exact HK |]. split; [exact HI |].
          destruct HI as (v & pool & Hp & _). split; [reflexivity |]. exists v, pool. auto.
        - exact Hpinit.
        - intros d sd _ Hd. destruct d; discriminate.
        - exact KPhT_RT.
        - intros d _. apply Stable_true.
        - intros g sg Hg. destruct g; discriminate.
        - intros d g sg _ Hg. destruct g; discriminate.
        - intros y sy Hy. destruct y; discriminate.
        - intros y sy d Hy. destruct y; discriminate. }
      intros hx Hfx. cbv beta.
      apply rp_wait_pending with (sl := tsl1 hx); [left; reflexivity | intros; reflexivity | |].
      { intros a. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar tsl1].
        - apply Gid_in_GT.
        - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar tsl1].
          intros σ p γ γ' [_ Hin] HI _ σ' Hst. cbn in Hst. destruct Hst as [-> ->].
          assert (HK : KPhT (σ, p, γ)).
          { apply (Hin 0). econstructor; [cbn; lia | reflexivity | reflexivity | unfold must_precede; cbn; reflexivity]. }
          exists p. split; [apply rt_refl |]. split; [split; [reflexivity | exact HK] |]. split; [exact HI |].
          destruct HI as (v & pool & Hp & _). split; [reflexivity |]. exists v, pool. auto.
        - intros s _ _. exact Logic.I.
        - intros d sd _ Hd. slot_cases d Hd. cbn. intros s _ Hs. exact Hs.
        - apply Stable_true.
        - intros d _. exact KPhT_RT.
        - intros g sg _. apply Stable_true.
        - intros d g sg _ Hg _. slot_cases g Hg. apply Gid_stable. gi.
        - intros y sy Hy _. slot_cases y Hy. apply Gid_stable. gi.
        - intros y sy d Hy _ _. slot_cases y Hy. apply Stable_true. }
      intros a H2 Hres2. cbv beta.
      assert (Hr2 : resolved_in H2 hx) by (exists (MRead X), a; eapply resolve_store_resolved; exact Hres2).
      apply rp_future with (sl := fun hw => tsl2 H2 hw a); [intros; reflexivity | |].
      { intros hw _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar tsl2].
        - apply Gid_in_GT.
        - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar tsl2].
          intros σ p γ γ' [_ Hin] HI _ σ' Hst. cbn in Hst. subst σ'.
          assert (HXA : XAt a (σ, p, γ)).
          { specialize (Hin 1). apply Hin.
            econstructor; [cbn; lia | reflexivity | reflexivity | unfold must_precede; cbn; exact Hr2]. }
          exists p. split; [apply rt_refl |]. split; [exact HXA |]. split; [exact HI |].
          destruct HI as (v & pool & Hp & _). split; [reflexivity |]. exists v, pool. auto.
        - intros s _ _. exact Logic.I.
        - intros d sd _ Hd. slot_cases d Hd; cbn; intros s _ Hs; [exact Logic.I | exact Hs].
        - apply Stable_true.
        - intros [| [|]] _; cbn; [apply Stable_true | apply XA_RT | apply Stable_true].
        - intros g sg _. apply Stable_true.
        - intros d g sg _ Hg _. slot_cases g Hg; apply Gid_stable;
            destruct (Nat.eqb d 1); gi.
        - intros y sy Hy _. slot_cases y Hy; apply Gid_stable; gi.
        - intros y sy d Hy _ _. slot_cases y Hy; apply Gid_stable; gi. }
      intros hw Hfw. cbv beta.
      apply rp_wait_pending with (sl := tsl3 hw a); [left; reflexivity | intros; reflexivity | |].
      { intros u. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar tsl3].
        - intros s s' (_ & v & pool & pool' & Hp & Hp' & Hk). exists v, pool, 1, pool'. auto.
        - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar tsl3].
          intros σ p γ γ' [_ Hin] HI _ σ' Hst. cbn in Hst. subst σ'.
          assert (HXA : XAt a (σ, p, γ)).
          { specialize (Hin 2). apply Hin.
            econstructor; [cbn; lia | reflexivity | reflexivity | unfold must_precede; cbn; reflexivity]. }
          destruct HXA as [HX (v & pool & Hp & Hph)]. cbn [ps_mem ps_poss fst snd] in HX, Hp.
          destruct HI as (v1 & pool1 & Hp1 & Hv1 & Hle & Hwf). cbn [ps_mem ps_poss fst snd] in *.
          rewrite Hp in Hp1. injection Hp1 as <- <-. subst p.
          destruct (linearize_response TLTS kt TAS a v 1 pool (fun t' h' o' => t_noop t' h' o' _) Hwf Hph
                      (conj (eq_trans (eq_sym HX) (eq_sym Hv1)) eq_refl)) as (pool' & Hps & Hl' & Hwf' & Hkeep).
          exists (TOk 1 pool'). split; [exact Hps |].
          split; [exists 1, pool'; split; [reflexivity | exact Hl'] |].
          split; [exists 1, pool'; cbn; repeat split; auto |].
          split; [reflexivity |]. exists v, pool, pool'. auto.
        - intros s _ _. exact Logic.I.
        - intros d sd _ Hd. slot_cases d Hd; cbn; intros s _ Hs; [exact Logic.I | exact Logic.I | exact Hs].
        - apply Stable_true.
        - intros [| [| [|]]] _; cbn; [apply Stable_true | apply Stable_true | apply XA_RT | apply Stable_true].
        - intros g sg _. apply Stable_true.
        - intros d g sg Hd Hg _. destruct (Nat.eqb_spec d 2) as [-> | Hne]; [| apply Stable_true].
          slot_cases g Hg; apply Gid_stable; gi.
        - (* the earlier events are ordered before the linearizing response *)
          intros y sy Hy Hnb. exfalso. apply Hnb. apply tas_before; [exact Hr2 |].
          apply nth_error_lt in Hy. cbn in Hy. exact Hy.
        - intros y sy d Hy Hnb _. exfalso. apply Hnb. apply tas_before; [exact Hr2 |].
          apply nth_error_lt in Hy. cbn in Hy. exact Hy. }
      intros u H3 Hres3. cbv beta.
      apply rp_futureD with (sl := fun hy => tsl4 H3 hy); [intros; reflexivity | |].
      { intros hy _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar tsl4].
        - apply Gid_in_GT.
        - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar tsl4].
          intros σ p γ γ' _ HI _ σ' Hst. cbn in Hst. subst σ'.
          exists p. split; [apply rt_refl |]. split; [exact Logic.I |]. split; [exact HI |].
          destruct HI as (v & pool & Hp & _). split; [reflexivity |]. exists v, pool. auto.
        - intros s _ _. exact Logic.I.
        - intros d sd _ _ s _ _. exact Logic.I.
        - apply Stable_true.
        - intros d _. apply Stable_true.
        - intros g sg _. apply Stable_true.
        - intros d g sg _ _ _. apply Stable_true.
        - intros y sy Hy _. slot_cases y Hy; apply Gid_stable; gi.
        - intros y sy d Hy _ _. slot_cases y Hy; apply Gid_stable;
            try (destruct (Nat.eqb d 1)); try (destruct (Nat.eqb d 2)); gi. }
      intros hy Hfy. cbv beta.
      apply rp_wait_pending with (sl := tsl5 hy); [left; reflexivity | intros; reflexivity | |].
      { intros u'. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar tsl5].
        - intros s s' (_ & v & pool & Hp & Hp'). exists v, pool, v, pool. repeat split; auto.
          intros; apply keeps_refl.
        - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar tsl5].
          intros σ p γ γ' _ HI _ σ' Hst. cbn in Hst. subst σ'.
          exists p. split; [apply rt_refl |]. split; [exact Logic.I |].
          destruct HI as (v & pool & Hp & Hv & Hle & Hwf). cbn [ps_mem ps_poss fst snd] in *.
          split; [exists v, pool; cbn; repeat split; auto |].
          split; [reflexivity |]. exists v, pool. auto.
        - intros s _ _. exact Logic.I.
        - intros d sd _ _ s _ _. exact Logic.I.
        - apply Stable_true.
        - intros d _. apply Stable_true.
        - intros g sg _. apply Stable_true.
        - intros d g sg _ _ _. apply Stable_true.
        - (* the flag write against every earlier assertion: by stability *)
          intros y sy Hy _. slot_cases y Hy; apply GYw_keeps; gi.
        - intros y sy d Hy _ _. slot_cases y Hy; apply GYw_keeps;
            try (destruct (Nat.eqb d 1)); try (destruct (Nat.eqb d 2)); gi. }
      intros u' H5 Hres5. cbv beta. apply rp_ret. split; [| exact Logic.I].
      apply close_done with
        (fin := fun d => match d with 3 => KLrT a | _ => fun _ => True end) (fin0 := fun _ => True).
      - eapply resolve_fresh_all_resolved; [| exact Hres5].
        eapply resolve_fresh_all_resolved; [| exact Hres3].
        eapply resolve_fresh_all_resolved; [constructor | exact Hres2].
      - constructor.
        + intros d sd Hd. slot_cases d Hd; cbn; intros s _ Hs; first [exact Logic.I | exact Hs].
        + intros s _ _. exact Logic.I.
        + intros d g sg Hd Hg Hnb. destruct d as [| [| [| [| d]]]]; try apply Stable_true.
          slot_cases g Hg; try (apply Gid_stable; gi).
          * exfalso. apply Hnb. apply before_refl.
          * apply GYw_keeps. gi.
        + intros g sg _. apply Stable_true.
        + intros [| [| [| [| d]]]]; try apply Stable_true. apply KLrT_RT.
        + apply Stable_true.
        + intros s _ _ Hfin. exact (Hfin 3 _ eq_refl Logic.I).
    Qed.

    (** Without the dag, the premise for the in-edge [(1, 2)] (the read
        value is still in [X]) against the linearizing response fails:
        [GL] writes [X]. *)
    Lemma tas_needs_order : ~ Stable IT (GL kt) (XAt 0).
    Proof.
      intros Hst.
      set (s := (σ0, TOk 0 [make_lin_entry kt (@ls_lini TSig TAS)], @nil (ScheduledEvent RlxSig TSig))).
      set (s' := (upd σ0 X 1, TOk 1 [make_lin_entry kt (@ls_linr TSig TAS 0)], @nil (ScheduledEvent RlxSig TSig))).
      assert (Hs' : XAt 0 s').
      { apply (Hst s s').
        - split; [reflexivity |]. exists 0, [make_lin_entry kt (@ls_lini TSig TAS)]. split; [reflexivity | right; left; reflexivity].
        - split; [reflexivity |]. exists 0, [make_lin_entry kt (@ls_lini TSig TAS)], [make_lin_entry kt (@ls_linr TSig TAS 0)].
          split; [reflexivity |]. split; [reflexivity |].
          intros k' Hne ls [Hl | []]. exfalso. apply Hne. injection Hl as Ht Hh _. destruct k'. cbn in *. subst. reflexivity.
        - exists 1, [make_lin_entry kt (@ls_linr TSig TAS 0)]. cbn. repeat split; auto. constructor; [intros [] | constructor]. }
      destruct Hs' as [HX _]. cbn in HX. discriminate HX.
    Qed.

    Lemma tas_guar_not_in_rely : ~ (forall s s', GL kt s s' -> RT kt s s').
    Proof.
      intros Hsub.
      destruct (Hsub (σ0, TOk 0 [], @nil (ScheduledEvent RlxSig TSig)) (upd σ0 X 1, TOk 1 [], @nil (ScheduledEvent RlxSig TSig))) as [HX _].
      - split; [reflexivity |]. exists 0, [], []. split; [reflexivity |]. split; [reflexivity |].
        intros k' _ ls [].
      - cbn in HX. discriminate HX.
    Qed.
  End TASProof.

  Lemma tas_provable t : MethodProvable IT RT GT Mtas t TAS (fun _ _ => True) (fun h => KLrT t h).
  Proof.
    constructor.
    - intros h [[σ p] γ] (p0 & γ0 & evs & (v & pool0 & Hp0 & Hv & Hle & Hwf) & Hinv & _).
      cbn [ps_poss ps_mem ps_ghost fst snd] in *. destruct Hinv as [st pool pool' Hins].
      injection Hp0 as -> <-. exists v, pool'. cbn. repeat split; auto. eapply lin_insert_well_formed; eauto.
    - intros h r [[σ p] γ] (v & pool & Hp & Hl) HI _. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
      exists p. split; [apply rt_refl |]. split; [exists v, pool; split; [exact Hp | exact Hl] |].
      split; [exact HI |]. split; [apply r_refl |].
      intros p2 Hret. subst p. inversion Hret as [st pool1 pool2 Hrem]; subst.
      destruct HI as (v1 & pool3 & Hp3 & Hv1 & Hle & Hwf). cbn in Hp3. injection Hp3 as -> <-.
      exists v1, pool2. cbn. repeat split; auto. eapply lin_remove_well_formed; eauto.
    - intros h. exact (tas_derivation t h).
  Qed.

  Theorem tas_sound t : MethodSem IT RT GT Mtas t TAS.
  Proof. eapply method_sound. apply tas_provable. Qed.

  Lemma tas_init : IT (σ0, TOk 0 [], []).
  Proof. exists 0, []. cbn. split; [reflexivity |]. split; [reflexivity |]. split; [lia | constructor]. Qed.

  (** m-19: a single-call check.  [IT] holds initially and the triple holds
      for every thread, but [GT] is not in [RT] (the implementation is not
      atomic), so there is no [RLHL2Hyps] instance. *)
  Corollary tas_single_call : IT (σ0, TOk 0 [], []) /\ forall t, MethodSem IT RT GT Mtas t TAS.
  Proof. split; [exact tas_init | exact tas_sound]. Qed.

  (** *** M-17: [TLTS] does not satisfy [HVF]

      [TLTS] takes effect at the response, and its invocation step is a
      no-op; certificates for it use helping ([linearize_response]).  Its
      natural sequential specification is [tδ] ("TAS returns the flag and
      sets it to 1").  [tas_not_hvf]: the hypothesis [HVF] of
      [RelaxedGSim.gsim_rel_lin] fails for [TLTS] under [seq_legal tδ 0].
      The trace [Inv(t0,1) Inv(t0,2) Res(t0,2,0) Res(t0,1,1)] is a complete,
      well-formed path of [TLTS] from [0]; [rhb] orders the first TAS
      before the second (same thread, not semi-independent), so the first
      must return [0] in any witness, but it returned [1].  So [tas_sound]
      certifies the method against a specification LTS whose own traces
      are not relaxed-linearizable under [tδ]; the end-to-end theorem of
      RLHL-2 does not apply to it.  The author's decision (M-17) is to use
      effect-at-invocation specifications ([RelaxedHoareSpec.EI]), which
      satisfy [HVF] ([RelaxedHoareSpec.ei_hvf]). *)

  Definition tδ (v : nat) (o : Sig.op (RelaxedSig.effect TSig)) : Sig.ar o -> nat -> Prop :=
    match o as o0 return Sig.ar o0 -> nat -> Prop with TAS => fun r v' => r = v /\ v' = 1 end.

  Definition tas_trace : list (ThreadEvent TSig) :=
    [Build_ThreadEvent t0 (@InvEv TSig 1 TAS); Build_ThreadEvent t0 (@InvEv TSig 2 TAS);
     Build_ThreadEvent t0 (@ResEv TSig 2 TAS 0); Build_ThreadEvent t0 (@ResEv TSig 1 TAS 1)].

  Definition inv_key_of (e : ThreadEvent TSig) : option (CallKey TSig) :=
    match te_ev _ e with InvEv h _ => Some (te_tid _ e, h) | ResEv _ _ _ => None end.

  Definition res_key_of (e : ThreadEvent TSig) : option (CallKey TSig * nat) :=
    match te_ev _ e with
    | ResEv h op r => Some ((te_tid _ e, h), match op return t_ar op -> nat with TAS => fun r => r end r)
    | InvEv _ _ => None
    end.

  Definition tval (o : RelaxedTraceLin.Op TSig) : nat :=
    match RelaxedTraceLin.op_op o as op return t_ar op -> nat with TAS => fun r => r end (RelaxedTraceLin.op_ret o).

  Lemma tinv_at L i k op :
    RelaxedTraceLin.inv_at (@PrefixView.sel TSig) L i k op -> exists x, nth_error L i = Some x /\ inv_key_of x = Some k.
  Proof.
    intros (x & Hx & Hs). exists x. split; [exact Hx |]. unfold PrefixView.sel in Hs. injection Hs as ->.
    destruct k; reflexivity.
  Qed.

  Lemma tres_at L i k op (r : Sig.ar op) :
    RelaxedTraceLin.res_at (@PrefixView.sel TSig) L i k op r ->
    exists x, nth_error L i = Some x /\ res_key_of x = Some (k, tval (RelaxedTraceLin.Build_Op k op r)).
  Proof.
    intros (x & Hx & Hs). exists x. split; [exact Hx |]. unfold PrefixView.sel in Hs. injection Hs as ->.
    destruct k, op; reflexivity.
  Qed.

  Lemma tseq_one s W s' : RelaxedHoareSpec.seq_run tδ s W s' -> s = 1 -> forall o, In o W -> tval o = 1.
  Proof.
    induction 1 as [s | s o s1 W s2 Hd Hr IH]; intros Hs o' Ho; [destruct Ho |]. subst s.
    destruct o as [k op r]. destruct op. cbn in Hd. destruct Hd as [Hr1 Hs1].
    destruct Ho as [<- | Ho]; [exact Hr1 | exact (IH Hs1 o' Ho)].
  Qed.

  Theorem tas_not_hvf :
    ~ (forall T v, RelaxedGSim.vf_path TLTS 0 T v -> PrefixView.wf T -> PrefixView.complete T ->
         RelaxedTraceLin.rel_lin (@PrefixView.sel TSig) T (RelaxedSig.semi_independent TSig)
           (RelaxedHoareSpec.seq_legal tδ 0)).
  Proof.
    intros HVF.
    assert (Hp : RelaxedGSim.vf_path TLTS 0 tas_trace 1).
    { unfold tas_trace. econstructor; [reflexivity |]. econstructor; [reflexivity |].
      econstructor; [split; reflexivity |]. econstructor; [split; reflexivity |]. constructor. }
    assert (Hwf : PrefixView.wf tas_trace).
    { split; [| split].
      - intros i j k op op' Hi Hj.
        destruct (tinv_at _ _ _ _ Hi) as (x & Hx & Hkx). destruct (tinv_at _ _ _ _ Hj) as (y & Hy & Hky).
        destruct i as [|[|[|[|i]]]]; cbn in Hx; try (destruct i; discriminate Hx); injection Hx as <-;
          destruct j as [|[|[|[|j]]]]; cbn in Hy; try (destruct j; discriminate Hy); injection Hy as <-;
          cbn in Hkx, Hky; congruence.
      - intros i j k op op' r r' Hi Hj.
        destruct (tres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (tres_at _ _ _ _ _ Hj) as (y & Hy & Hky).
        destruct i as [|[|[|[|i]]]]; cbn in Hx; try (destruct i; discriminate Hx); injection Hx as <-;
          destruct j as [|[|[|[|j]]]]; cbn in Hy; try (destruct j; discriminate Hy); injection Hy as <-;
          cbn in Hkx, Hky; congruence.
      - intros j k op r Hj. destruct (tres_at _ _ _ _ _ Hj) as (x & Hx & Hkx).
        destruct j as [|[|[|[|j]]]]; cbn in Hx; try (destruct j; discriminate Hx); injection Hx as <-;
          cbn in Hkx; try discriminate Hkx; injection Hkx as <- _; destruct op.
        + exists 1. split; [lia |]. eexists. split; reflexivity.
        + exists 0. split; [lia |]. eexists. split; reflexivity. }
    assert (Hc : PrefixView.complete tas_trace).
    { intros i k op Hi. destruct (tinv_at _ _ _ _ Hi) as (x & Hx & Hkx).
      destruct i as [|[|[|[|i]]]]; cbn in Hx; try (destruct i; discriminate Hx); injection Hx as <-;
        cbn in Hkx; try discriminate Hkx; injection Hkx as <-; destruct op.
      - exists 3, 1. eexists. split; reflexivity.
      - exists 2, 0. eexists. split; reflexivity. }
    destruct (HVF tas_trace 1 Hp Hwf Hc) as (W & (s & Hrun) & Hnd & Hocc & Hcov & Hord).
    assert (Hi0 : RelaxedTraceLin.inv_at (@PrefixView.sel TSig) tas_trace 0 (t0, 1) TAS) by (eexists; split; reflexivity).
    assert (Hi1 : RelaxedTraceLin.inv_at (@PrefixView.sel TSig) tas_trace 1 (t0, 2) TAS) by (eexists; split; reflexivity).
    destruct (Hcov _ _ _ Hi0) as (o1 & Ho1 & Hk1). destruct (Hcov _ _ _ Hi1) as (o2 & Ho2 & Hk2).
    (* the values and the invocation positions of [o1] and [o2] *)
    assert (Hv : forall o k i, In o W -> RelaxedTraceLin.op_key o = k ->
               RelaxedTraceLin.inv_at (@PrefixView.sel TSig) tas_trace i k TAS ->
               (exists i', RelaxedTraceLin.inv_at (@PrefixView.sel TSig) tas_trace i' (RelaxedTraceLin.op_key o) (RelaxedTraceLin.op_op o) /\ i' = i) /\
               exists j x, nth_error tas_trace j = Some x /\ res_key_of x = Some (k, tval o)).
    { intros o k i Ho Hk Hi. destruct (Hocc o Ho) as [(i' & Hi') (j & Hj)]. split.
      - exists i'. split; [exact Hi' |].
        destruct (tinv_at _ _ _ _ Hi') as (x & Hx & Hkx). destruct (tinv_at _ _ _ _ Hi) as (y & Hy & Hky).
        rewrite Hk in Hkx.
        destruct i' as [|[|[|[|i']]]]; cbn in Hx; try (destruct i'; discriminate Hx); injection Hx as <-;
          destruct i as [|[|[|[|i]]]]; cbn in Hy; try (destruct i; discriminate Hy); injection Hy as <-;
          cbn in Hkx, Hky; congruence.
      - destruct (tres_at _ _ _ _ _ Hj) as (x & Hx & Hkx). exists j, x. split; [exact Hx |]. rewrite <- Hk. exact Hkx. }
    destruct (Hv o1 _ 0 Ho1 Hk1 Hi0) as ((i1 & Hin1 & ->) & j1 & x1 & Hx1 & Hkx1).
    destruct (Hv o2 _ 1 Ho2 Hk2 Hi1) as ((i2 & Hin2 & ->) & j2 & x2 & Hx2 & Hkx2).
    assert (Hval1 : tval o1 = 1).
    { destruct j1 as [|[|[|[|j1]]]]; cbn in Hx1; try (destruct j1; discriminate Hx1); injection Hx1 as <-;
        cbn in Hkx1; congruence. }
    assert (Hval2 : tval o2 = 0).
    { destruct j2 as [|[|[|[|j2]]]]; cbn in Hx2; try (destruct j2; discriminate Hx2); injection Hx2 as <-;
        cbn in Hkx2; congruence. }
    assert (Hbef : RelaxedTraceLin.before W o1 o2).
    { apply Hord; [exact Ho1 | exact Ho2 |]. right. split; [rewrite Hk1, Hk2; reflexivity |].
      exists 0, 1. split; [exact Hin1 |]. split; [exact Hin2 |]. split; [lia | cbn; tauto]. }
    destruct W as [| w0 rest]; [destruct Ho1 |].
    inversion Hrun as [| s0' o s1 W' s2 Hd Hr]; subst.
    assert (Hw0 : tval w0 = 0 /\ s1 = 1) by (destruct w0 as [k op r]; destruct op; exact Hd).
    destruct Hw0 as [Hw0 ->].
    pose proof (tseq_one _ _ _ Hr eq_refl) as Hrest.
    destruct Hbef as (l1 & l2 & Heq & Hl2).
    destruct l1 as [| y l1]; cbn in Heq; injection Heq as Hy Hrest'.
    - subst w0. destruct Ho2 as [<- | Ho2]; [congruence |].
      rewrite (Hrest o2 Ho2) in Hval2. discriminate Hval2.
    - assert (Hin : In o2 rest) by (rewrite Hrest'; apply in_or_app; right; right; exact Hl2).
      rewrite (Hrest o2 Hin) in Hval2. discriminate Hval2.
  Qed.

  (** *** M-17, refined: commuting same-thread pairs are not enough

      The iteration-2 review states that helping is safe for [HVF] only
      when the same-thread, non-semi-independent pairs commute.  That is a
      necessary condition, not a sufficient one.  [PairLTS] is the
      specification of [pair_rlhl2]; its only such pairs are two [RdPair]s,
      which commute.  Its natural sequential specification is [pδ] (a read
      returns the pair, a write sets it to [(1, 1)]).  [pair_not_hvf]: the
      complete, well-formed [PairLTS] path
      [Inv(1,1,Rd) Inv(1,2,Rd) Res(1,2,Rd,(0,0)) Inv(2,3,Wr) Res(2,3,Wr)
       Res(1,1,Rd,(1,1))] (thread [1] reads twice, thread [2] writes in
      between) is not relaxed-linearizable: [rhb] orders read [1] before
      read [2] (same thread, by invocation) and read [2] before the write
      (real time), so read [1] would return [(0, 0)].  Same-thread order
      by invocation plus real time through another thread's write is what
      helping cannot respect.  So [pair_rlhl2] (and, by the same trace
      shape, [LogRead.log_rlhl2]) are checks of the logic over
      specifications that fail [HVF]; [XYLTS], [LeLTS] and [AwLTS] have no
      write that a same-thread pair of reads could observe, and are not
      claimed either way. *)

  Definition ikop {F : RelaxedSig.t} (e : ThreadEvent F) : option (CallKey F * Sig.op (RelaxedSig.effect F)) :=
    match te_ev F e with InvEv h o => Some ((te_tid F e, h), o) | ResEv _ _ _ => None end.

  Definition rkop {F : RelaxedSig.t} (e : ThreadEvent F) : option (CallKey F * Sig.op (RelaxedSig.effect F)) :=
    match te_ev F e with ResEv h o _ => Some ((te_tid F e, h), o) | InvEv _ _ => None end.

  Lemma ginv_at {F : RelaxedSig.t} L i (k : CallKey F) op :
    RelaxedTraceLin.inv_at (@PrefixView.sel F) L i k op -> exists x, nth_error L i = Some x /\ ikop x = Some (k, op).
  Proof.
    intros (x & Hx & Hs). exists x. split; [exact Hx |]. unfold PrefixView.sel in Hs. injection Hs as ->.
    destruct k; reflexivity.
  Qed.

  Lemma gres_at {F : RelaxedSig.t} L i (k : CallKey F) op (r : Sig.ar op) :
    RelaxedTraceLin.res_at (@PrefixView.sel F) L i k op r -> exists x, nth_error L i = Some x /\ rkop x = Some (k, op).
  Proof.
    intros (x & Hx & Hs). exists x. split; [exact Hx |]. unfold PrefixView.sel in Hs. injection Hs as ->.
    destruct k; reflexivity.
  Qed.

  Lemma before_trans_keys {A K : Type} (f : A -> K) (W : list A) a b c :
    NoDup (map f W) -> RelaxedTraceLin.before W a b -> RelaxedTraceLin.before W b c -> RelaxedTraceLin.before W a c.
  Proof.
    intros Hnd (l1 & l2 & -> & Hb) (m1 & m2 & Heq & Hc).
    destruct (in_split _ _ Hb) as (n1 & n2 & ->).
    assert (Hl : l1 ++ a :: n1 ++ b :: n2 = (l1 ++ a :: n1) ++ b :: n2) by (rewrite <- app_assoc; reflexivity).
    destruct (RelaxedGSim.key_position f _ _ _ _ _ _ _ Hnd Hl Heq eq_refl) as (_ & _ & <-).
    exists l1, (n1 ++ b :: n2). split; [reflexivity |]. apply in_or_app. right. right. exact Hc.
  Qed.

  Lemma nodup_app_both {A K : Type} (f : A -> K) (l1 l2 : list A) a c :
    NoDup (map f (l1 ++ a :: l2)) -> In c l1 -> In c l2 -> False.
  Proof.
    induction l1 as [| x l1 IH]; intros Hnd H1 H2; [destruct H1 |].
    cbn in Hnd. inversion Hnd as [| ? ? Hnin Hnd']; subst. destruct H1 as [<- | H1].
    - apply Hnin. rewrite map_app. apply in_or_app. right. right. apply in_map. exact H2.
    - exact (IH Hnd' H1 H2).
  Qed.

  Definition pδ (v : nat * nat) (o : Sig.op (RelaxedSig.effect PairSig)) : Sig.ar o -> nat * nat -> Prop :=
    match o as o0 return Sig.ar o0 -> nat * nat -> Prop with
    | RdPair => fun r v' => r = v /\ v' = v
    | WrPair => fun _ v' => v' = (1, 1)
    end.

  Definition pval (o : RelaxedTraceLin.Op PairSig) : option (nat * nat) :=
    match RelaxedTraceLin.op_op o as op return pair_ar op -> option (nat * nat) with
    | RdPair => fun r => Some r
    | WrPair => fun _ => None
    end (RelaxedTraceLin.op_ret o).

  Definition pres_val (e : ThreadEvent PairSig) : option (CallKey PairSig * option (nat * nat)) :=
    match te_ev _ e with
    | ResEv h op r =>
        Some ((te_tid _ e, h), match op return pair_ar op -> option (nat * nat) with
                              | RdPair => fun r => Some r | WrPair => fun _ => None end r)
    | InvEv _ _ => None
    end.

  Lemma pres_at L i k op (r : Sig.ar op) :
    RelaxedTraceLin.res_at (@PrefixView.sel PairSig) L i k op r ->
    exists x, nth_error L i = Some x /\ pres_val x = Some (k, pval (RelaxedTraceLin.Build_Op k op r)).
  Proof.
    intros (x & Hx & Hs). exists x. split; [exact Hx |]. unfold PrefixView.sel in Hs. injection Hs as ->.
    destruct k, op; reflexivity.
  Qed.

  Lemma pseq_reads v W o W' s :
    RelaxedHoareSpec.seq_run pδ v (W ++ o :: W') s ->
    Forall (fun x : RelaxedTraceLin.Op PairSig => RelaxedTraceLin.op_op x = RdPair) W -> RelaxedTraceLin.op_op o = RdPair -> pval o = Some v.
  Proof.
    revert v. induction W as [| x W IH]; intros v Hr Hall Ho; cbn in Hr.
    - inversion Hr as [| ? ? s1 ? ? Hd _]; subst. destruct o as [k op r]. cbn in Ho. subst op.
      cbn in Hd |- *. destruct Hd as [-> _]. reflexivity.
    - inversion Hr as [| ? ? s1 ? ? Hd Hr']; subst. inversion Hall as [| ? ? Hx Hall']; subst.
      destruct x as [k op r]. cbn in Hx. subst op. cbn in Hd. destruct Hd as [_ ->]. exact (IH v Hr' Hall' Ho).
  Qed.

  Definition pair_trace : list (ThreadEvent PairSig) :=
    [Build_ThreadEvent 1%positive (@InvEv PairSig 1 RdPair); Build_ThreadEvent 1%positive (@InvEv PairSig 2 RdPair);
     Build_ThreadEvent 1%positive (@ResEv PairSig 2 RdPair (0, 0)); Build_ThreadEvent 2%positive (@InvEv PairSig 3 WrPair);
     Build_ThreadEvent 2%positive (@ResEv PairSig 3 WrPair tt); Build_ThreadEvent 1%positive (@ResEv PairSig 1 RdPair (1, 1))].

  Ltac idx6 i H := destruct i as [|[|[|[|[|[|i]]]]]]; cbn in H; try (destruct i; discriminate H); injection H as <-.

  Theorem pair_not_hvf :
    ~ (forall T v, RelaxedGSim.vf_path PairLTS (0, 0) T v -> PrefixView.wf T -> PrefixView.complete T ->
         RelaxedTraceLin.rel_lin (@PrefixView.sel PairSig) T (RelaxedSig.semi_independent PairSig)
           (RelaxedHoareSpec.seq_legal pδ (0, 0))).
  Proof.
    intros HVF.
    assert (Hp : RelaxedGSim.vf_path PairLTS (0, 0) pair_trace (1, 1)).
    { unfold pair_trace. econstructor; [reflexivity |]. econstructor; [reflexivity |].
      econstructor; [split; reflexivity |]. econstructor; [reflexivity |].
      econstructor; [reflexivity |]. econstructor; [split; reflexivity |]. constructor. }
    assert (Hwf : PrefixView.wf pair_trace).
    { split; [| split].
      - intros i j k op op' Hi Hj.
        destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
        idx6 i Hx; idx6 j Hy; cbn in Hkx, Hky; congruence.
      - intros i j k op op' r r' Hi Hj.
        destruct (gres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (gres_at _ _ _ _ _ Hj) as (y & Hy & Hky).
        idx6 i Hx; idx6 j Hy; cbn in Hkx, Hky; congruence.
      - intros j k op r Hj. destruct (gres_at _ _ _ _ _ Hj) as (x & Hx & Hkx).
        idx6 j Hx; cbn in Hkx; try discriminate Hkx; injection Hkx as <- <-.
        + exists 1. split; [lia | eexists; split; reflexivity].
        + exists 3. split; [lia | eexists; split; reflexivity].
        + exists 0. split; [lia | eexists; split; reflexivity]. }
    assert (Hc : PrefixView.complete pair_trace).
    { intros i k op Hi. destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx).
      idx6 i Hx; cbn in Hkx; try discriminate Hkx; injection Hkx as <- <-.
      - exists 5, (1, 1). eexists; split; reflexivity.
      - exists 2, (0, 0). eexists; split; reflexivity.
      - exists 4, tt. eexists; split; reflexivity. }
    destruct (HVF pair_trace (1, 1) Hp Hwf Hc) as (W & (s & Hrun) & Hnd & Hocc & Hcov & Hord).
    assert (Hi0 : RelaxedTraceLin.inv_at (@PrefixView.sel PairSig) pair_trace 0 (1%positive, 1) RdPair)
      by (eexists; split; reflexivity).
    assert (Hi1 : RelaxedTraceLin.inv_at (@PrefixView.sel PairSig) pair_trace 1 (1%positive, 2) RdPair)
      by (eexists; split; reflexivity).
    assert (Hi3 : RelaxedTraceLin.inv_at (@PrefixView.sel PairSig) pair_trace 3 (2%positive, 3) WrPair)
      by (eexists; split; reflexivity).
    destruct (Hcov _ _ _ Hi0) as (o1 & Ho1 & Hk1).
    destruct (Hcov _ _ _ Hi1) as (o2 & Ho2 & Hk2).
    destruct (Hcov _ _ _ Hi3) as (o3 & Ho3 & Hk3).
    (* read 1: invoked at 0, returns (1, 1) *)
    destruct (Hocc o1 Ho1) as [(i1 & Hin1) (j1 & Hre1)].
    destruct (ginv_at _ _ _ _ Hin1) as (x1 & Hx1 & Hkx1). rewrite Hk1 in Hkx1.
    idx6 i1 Hx1; cbn in Hkx1; try congruence.
    assert (Hop1 : RelaxedTraceLin.op_op o1 = RdPair) by congruence.
    destruct (pres_at _ _ _ _ _ Hre1) as (y1 & Hy1 & Hky1). rewrite Hk1 in Hky1.
    idx6 j1 Hy1; cbn in Hky1; try congruence.
    assert (Hv1 : pval o1 = Some (1, 1)) by (change (pval o1) with (pval (RelaxedTraceLin.Build_Op (RelaxedTraceLin.op_key o1) (RelaxedTraceLin.op_op o1) (RelaxedTraceLin.op_ret o1))); congruence).
    (* read 2: invoked at 1, responds at 2 *)
    destruct (Hocc o2 Ho2) as [(i2 & Hin2) (j2 & Hre2)].
    destruct (ginv_at _ _ _ _ Hin2) as (x2 & Hx2 & Hkx2). rewrite Hk2 in Hkx2.
    idx6 i2 Hx2; cbn in Hkx2; try congruence.
    assert (Hop2 : RelaxedTraceLin.op_op o2 = RdPair) by congruence.
    destruct (gres_at _ _ _ _ _ Hre2) as (y2 & Hy2 & Hky2). rewrite Hk2 in Hky2.
    idx6 j2 Hy2; cbn in Hky2; try congruence.
    (* the write: invoked at 3 *)
    destruct (Hocc o3 Ho3) as [(i3 & Hin3) _].
    destruct (ginv_at _ _ _ _ Hin3) as (x3 & Hx3 & Hkx3). rewrite Hk3 in Hkx3.
    idx6 i3 Hx3; cbn in Hkx3; try congruence.
    assert (H12 : RelaxedTraceLin.before W o1 o2).
    { apply Hord; [exact Ho1 | exact Ho2 |]. right. split; [rewrite Hk1, Hk2; reflexivity |].
      exists 0, 1. split; [exact Hin1 |]. split; [exact Hin2 |]. split; [lia |].
      cbn. rewrite Hop1, Hop2. intros H. apply H. reflexivity. }
    assert (H23 : RelaxedTraceLin.before W o2 o3).
    { apply Hord; [exact Ho2 | exact Ho3 |]. left. exists 2, 3. split; [exact Hre2 |]. split; [exact Hin3 | lia]. }
    destruct (before_trans_keys _ W o1 o2 o3 Hnd H12 H23) as (l1 & l2 & -> & Hl2).
    assert (Hreads : Forall (fun x : RelaxedTraceLin.Op PairSig => RelaxedTraceLin.op_op x = RdPair) l1).
    { apply Forall_forall. intros x Hx.
      assert (HxW : In x (l1 ++ o1 :: l2)) by (apply in_or_app; left; exact Hx).
      destruct (Hocc x HxW) as [(i & Hin) _].
      destruct (ginv_at _ _ _ _ Hin) as (z & Hz & Hkz).
      idx6 i Hz; cbn in Hkz; try congruence.
      exfalso. assert (Hx3 : x = o3).
      { apply (RelaxedHoareSpec.nodup_key_eq _ _ _ Hnd HxW Ho3). rewrite Hk3. congruence. }
      subst x. exact (nodup_app_both _ _ _ _ _ Hnd Hx Hl2). }
    pose proof (pseq_reads _ _ _ _ _ Hrun Hreads Hop1) as Hv. congruence.
  Qed.

  (** ** M-14: a loop through [cprov_dowhile]

      [await_body]: spin on [X] until it reads [1], then return.  The
      overlay [AwSig] has one operation [Await], whose response is enabled
      only when the abstract flag is [1]; the flag is [X] ([IA]).  The loop
      body is a blocking read; its response linearizes the call exactly
      when it reads [1] (a conditional linearization point), and otherwise
      re-establishes the loop invariant. *)

  Inductive AwOp : Type := Await.

  Definition aw_ar (o : AwOp) : Type := match o with Await => unit end.

  Canonical Structure AwEffect : Sig.t := {| Sig.op := AwOp; Sig.ar := aw_ar |}.

  Definition AwSig : RelaxedSig.t :=
    {| RelaxedSig.effect := AwEffect; RelaxedSig.handle := nat;
       RelaxedSig.semi_independent := fun _ _ => False; RelaxedSig.mode := fun _ => Local |}.

  Lemma AwSig_wf : RelaxedSig.well_formed AwSig.
  Proof. constructor; [intros x H; exact H | intros _ _ [] | intros _ _ []]. Qed.

  Definition aw_step (ev : ThreadEvent AwSig) (v v' : nat) : Prop :=
    match te_ev _ ev with
    | InvEv _ _ => v' = v
    | ResEv _ _ _ => v = 1 /\ v' = v
    end.

  Definition AwLTS : LTS AwSig := {| State := nat; Step := aw_step; Error := NoError |}.

  Abbreviation AOk v pool := (@PossOk AwSig AwLTS v pool).
  Abbreviation AA := (Assn MemLTS AwLTS).

  Definition spin_test (a : nat) : bool := negb (Nat.eqb a 1).

  Definition await_body : Prog RlxSig unit :=
    bindProg (doWhileR spin_test (@call RlxSig (MRead X))) (fun _ => Ret tt).

  Definition Maw : RelaxedModuleImpl RlxSig AwSig :=
    fun op t => match op as o return Prog RlxSig (Sig.ar o) with Await => await_body end.

  Definition IA : AA := fun s => exists v pool, ps_poss s = AOk v pool /\ v = ps_mem s X /\
                                               lin_pool_well_formed pool.

  Definition RA (k : CallKey AwSig) : PRel MemLTS AwLTS := fun s s' =>
    exists v pool v' pool', ps_poss s = AOk v pool /\ ps_poss s' = AOk v' pool' /\ keeps k pool pool'.

  Definition GA (k : CallKey AwSig) : PRel MemLTS AwLTS := fun s s' =>
    ps_mem s' = ps_mem s /\
    exists v pool pool', ps_poss s = AOk v pool /\ ps_poss s' = AOk v pool' /\
      forall k', k' <> k -> keeps k' pool pool'.

  Lemma RA_keeps k : KeepsRel k (RA k).
  Proof.
    intros s s' (v & pool & v' & pool' & Hp & Hp' & Hk) v1 pool1 Hp1.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists v', pool'. auto.
  Qed.

  Lemma IA_invoke k op σ p γ p' γ' :
    IA (σ, p, γ) -> poss_invoke AwLTS (fst k) (snd k) op p p' -> IA (σ, p', γ').
  Proof.
    intros HI Hinv. destruct Hinv as [st pool1 pool2 Hins].
    destruct HI as (v & pool & Hp & Hv & Hwf). cbn in Hp, Hv. injection Hp as -> <-.
    exists v, pool2. cbn. repeat split; auto. eapply lin_insert_well_formed; eauto.
  Qed.

  Section AwaitProof.
    Context (t : tid).

    Definition PA (h : nat) : AA := fun s => KPh (VE := MemLTS) (VF := AwLTS) (t, h) Await s /\ IA s.
    Definition QA (h : nat) (u : unit) : AA := fun s => KLr (VE := MemLTS) (VF := AwLTS) (t, h) Await tt s /\ IA s.
    Definition QB (h : nat) (a : nat) : AA := fun s => (a = 1 /\ QA h tt s) \/ (a <> 1 /\ PA h s).

    Lemma PA_stable h : Stable IA (RA (t, h)) (PA h).
    Proof. apply Stable_and; [apply KPh_stable, RA_keeps | apply Stable_I]. Qed.

    Lemma QA_stable h u : Stable IA (RA (t, h)) (QA h u).
    Proof. apply Stable_and; [apply KLr_stable, RA_keeps | apply Stable_I]. Qed.

    Lemma QB_stable h a : Stable IA (RA (t, h)) (QB h a).
    Proof.
      intros s s' [[Ha Hq] | [Ha Hp]] Hr HI; [left | right]; split; auto.
      - eapply QA_stable; eauto.
      - eapply PA_stable; eauto.
    Qed.

    Lemma await_chain : MethodProvableChain IA RA GA Maw t Await PA QA.
    Proof.
      constructor.
      - intros h [[σ p] γ] Hs. pose proof Hs as (p0 & γ0 & evs & HI0 & Hinv & _).
        split; [eapply pinit_KPh; [| exact Hs] |]; eapply IA_invoke; eauto.
      - intros h s [_ HI]. exact HI.
      - intros h. apply PA_stable.
      - intros h r [[σ p] γ] p2 [_ HI] Hret. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        destruct Hret as [st pool1 pool2 Hrem]. destruct HI as (v & pool & Hp & Hv & Hwf).
        cbn in Hp, Hv. injection Hp as -> <-. exists v, pool2. cbn. repeat split; auto.
        eapply lin_remove_well_formed; eauto.
      - intros h r s [(v & pool & Hp & Hl) _]. exists v, pool. destruct r. auto.
      - intros h. cbn. unfold await_body.
        apply cprov_seq with (Q' := fun a s => QB h a s /\ spin_test a = false).
        + apply cprov_dowhile.
          * unfold call. apply cprov_call with (P' := PA h) (Q' := QB h).
            -- intros s [_ HI]. exact HI.
            -- intros r s [[_ [_ HI]] | [_ [_ HI]]]; exact HI.
            -- apply PA_stable.
            -- intros r. apply QB_stable.
            -- (* the invocation of the read *)
               intros h' σ p γ γ' Hs _ σ' Hst. cbn in Hst. subst σ'.
               exists p. split; [apply rt_refl |]. split; [exact Hs |].
               destruct Hs as [_ (v & pool & Hp & _ & _)]. split; [reflexivity |].
               exists v, pool, pool. repeat split; auto. intros; apply keeps_refl.
            -- (* the read's response: linearize iff it reads 1 *)
               intros h' a σ p γ γ' [(v & pool & Hp & Hph) (v1 & pool1 & Hp1 & Hv1 & Hwf)] _ σ' Hst.
               cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hst. destruct Hst as [Ha ->].
               rewrite Hp in Hp1. injection Hp1 as <- <-. subst p.
               destruct (Nat.eq_dec a 1) as [-> | Hne].
               ++ destruct (linearize_response AwLTS (t, h) Await tt v v pool (fun _ _ _ => eq_refl) Hwf Hph
                             (conj (eq_trans Hv1 (eq_sym Ha)) eq_refl)) as (pool' & Hps & Hl' & Hwf' & Hkeep).
                  exists (AOk v pool'). split; [exact Hps |].
                  split; [left; split; [reflexivity |]; split; [exists v, pool'; split; [reflexivity | exact Hl'] | exists v, pool'; cbn; repeat split; auto] |].
                  split; [reflexivity |]. exists v, pool, pool'. auto.
               ++ exists (AOk v pool). split; [apply rt_refl |].
                  split; [right; split; [exact Hne |]; split; [exists v, pool; split; [reflexivity | exact Hph] | exists v, pool; cbn; repeat split; auto] |].
                  split; [reflexivity |]. exists v, pool, pool. repeat split; auto. intros; apply keeps_refl.
            -- intros r. apply cprov_ret. intros s Hs. exact Hs.
          * intros a Hb s [[-> _] | [_ Hs]]; [discriminate Hb | exact Hs].
        + intros a. apply cprov_ret. intros s [[[_ Hs] | [Hne _]] Hb]; [exact Hs |].
          exfalso. unfold spin_test in Hb. destruct (Nat.eqb_spec a 1); [exact (Hne e) | discriminate Hb].
    Qed.
  End AwaitProof.

  Theorem await_sound t : MethodSem IA RA GA Maw t Await.
  Proof. eapply chain_sound. apply await_chain. Qed.

  Lemma await_init : IA (σ0, AOk 0 [], []).
  Proof. exists 0, []. split; [reflexivity |]. split; [reflexivity | constructor]. Qed.

  (** m-19: a single-call check ([RA] admits no concurrent writer of [X]
      that the spin could wait for; no [RLHL2Hyps] instance). *)
  Corollary await_single_call : IA (σ0, AOk 0 [], []) /\ forall t, MethodSem IA RA GA Maw t Await.
  Proof. split; [exact await_init | exact await_sound]. Qed.

  (** ** M-12: the two-call configuration of (b), derived from the module

      Prototype of the RLHL-2 composition argument for the closed system of
      the two calls [k1] ([RdX]) and [k2] ([WrY]) of thread [t5]:
      - [two_calls_init]: every configuration reached from the initial
        module by the two overlay invocations of [k1] and [k2]
        ([tagged_invoke], with arbitrary produced traces and results)
        satisfies [Inv2] together with the two abstract invocations;
      - [two_calls_step]: [Inv2] is preserved by every later
        [module_step_tagged] that is not an overlay invocation (no third
        call is started: the invariant only tracks [k1] and [k2]); an
        underlay step is matched by [poss_steps], an overlay return by
        [poss_steps] followed by [poss_return] with the returned value;
      - [two_calls_execution]: hence by every such execution.
      [Inv2] is "[I5] at the projected state [(tm_lts_state c, p,
      ghost_of (tm_queue c))], and every active call has a [CallSafe] on
      its owner sub-queue".  The underlay case uses [select_project] and
      [ghost_of_select] for the emitting call and [G5_in_R5] for the other
      one; the return case uses [osq_done], [ghost_of_done], the
      existential return step ([lin_remove_exists]) and [return_in_rely]
      (the content of the [h_return_rely] field of [xy_rlhl2]).  The
      generic version for every [RLHL2Hyps] instance is [TwoCallsGen]
      below. *)

  Abbreviation TCfg := (@TaggedModuleConfig RlxSig XYSig MemLTS).

  Definition proj5 (c : TCfg) (p : Poss XYLTS) : PState MemLTS XYLTS :=
    (tm_lts_state c, p, ghost_of (tm_queue c)).

  Definition CallSt (k : CallKey XYSig) (op : XYOp) (ret : xy_ar op) (cell : CallCell XYSig)
      (c : TCfg) (p : Poss XYLTS) : Prop :=
    (cell = @ActiveCall XYSig op ret /\
     exists l, owner_subqueue k (tm_queue c) l /\ Forall (fun m => te_tid RlxSig (untag m) = fst k) l /\
               CallSafe I5 R5 G5 k op ret l (proj5 c p))
    \/ (cell = DeadCall /\ owner_done_tagged k (tm_queue c)).

  Record Inv2 (ret1 : nat) (ret2 : unit) (c : TCfg) (p : Poss XYLTS) : Prop := {
    i2_I : I5 (proj5 c p);
    i2_owner : forall x, In x (tm_queue c) -> ts_owner x = k1 \/ ts_owner x = k2;
    i2_calls : exists cell1 cell2,
      tm_calls c = [@Build_CallEntry XYSig t5 2 cell2; @Build_CallEntry XYSig t5 1 cell1] /\
      CallSt k1 RdX ret1 cell1 c p /\ CallSt k2 WrY ret2 cell2 c p
  }.

  Lemma callsafe_inv k op ret l s :
    CallSafe I5 R5 G5 k op ret l s ->
    I5 s /\
    (forall pre m post, l = pre ++ m :: post -> local_frontier pre m ->
       forall γ' σ', ghost_emit k (untag m) (ps_ghost s) γ' -> Step MemLTS (untag m) (ps_mem s) σ' ->
         exists p', poss_steps XYLTS (ps_poss s) p' /\ I5 (σ', p', γ') /\
                    G5 k s (σ', p', γ') /\ CallSafe I5 R5 G5 k op ret (pre ++ post) (σ', p', γ')) /\
    (forall s', R5 k s s' -> I5 s' -> CallSafe I5 R5 G5 k op ret l s') /\
    (l = [] -> NoOwn k (ps_ghost s) -> RetCond I5 G5 k op ret s).
  Proof. intros Hcs. destruct Hcs as [l s HI Hemit Hrely Hret]. auto. Qed.

  Lemma callsafe_refl_rely k op ret l k' s s' :
    k <> k' -> clos_refl _ (G5 k') s s' -> I5 s' ->
    CallSafe I5 R5 G5 k op ret l s -> CallSafe I5 R5 G5 k op ret l s'.
  Proof.
    intros Hne HG HI Hcs. destruct HG as [s'' HG |]; [| exact Hcs].
    destruct (callsafe_inv _ _ _ _ _ Hcs) as (_ & _ & Hrely & _).
    apply Hrely; [apply (G5_in_R5 k k'); [intros Heq; apply Hne; symmetry; exact Heq | exact HG] | exact HI].
  Qed.

  Lemma select_sub (cand : TaggedScheduledEvent RlxSig XYSig) q q' x :
    select_frontier_tagged cand q q' -> In x q' -> In x q.
  Proof.
    intros Hsel Hx. destruct (select_split _ _ _ Hsel) as (pre & post & -> & -> & _).
    apply in_app_or in Hx. apply in_or_app. destruct Hx; [left | right; right]; assumption.
  Qed.

  Lemma done_select k (cand : TaggedScheduledEvent RlxSig XYSig) q q' :
    select_frontier_tagged cand q q' -> owner_done_tagged k q -> owner_done_tagged k q'.
  Proof.
    intros Hsel Hd Hin. apply Hd. apply in_map_iff in Hin. destruct Hin as (x & <- & Hx).
    apply in_map. eapply select_sub; eauto.
  Qed.

  Lemma Forall_remove {A : Type} (P : A -> Prop) pre (m : A) post :
    Forall P (pre ++ m :: post) -> Forall P (pre ++ post).
  Proof.
    rewrite !Forall_forall. intros H x Hx. apply H. apply in_app_or in Hx. apply in_or_app.
    destruct Hx; [left | right; right]; assumption.
  Qed.

  Lemma finish_two t h op ret cell1 cell2 (pool' : CallPool XYSig) :
    finish_call t h op ret [@Build_CallEntry XYSig t5 2 cell2; @Build_CallEntry XYSig t5 1 cell1] pool' ->
    (t = t5 /\ h = 2 /\ cell2 = @ActiveCall XYSig op ret /\
     pool' = [@Build_CallEntry XYSig t5 2 DeadCall; @Build_CallEntry XYSig t5 1 cell1]) \/
    (t = t5 /\ h = 1 /\ cell1 = @ActiveCall XYSig op ret /\
     pool' = [@Build_CallEntry XYSig t5 2 cell2; @Build_CallEntry XYSig t5 1 DeadCall]).
  Proof.
    intros Hf. inversion Hf as [tail Heq1 Heq2 | t' h' cell pool pool'' Hneq Hf' Heq1 Heq2]; subst.
    - left. auto.
    - right. inversion Hf' as [tail' Heq1' Heq2' | t'' h'' cell' pool1 pool1' Hneq' Hf'' Heq1' Heq2']; subst.
      + auto.
      + inversion Hf''.
  Qed.

  Definition cell_op (c : CallCell XYSig) : option XYOp :=
    match c with ActiveCall o _ => Some o | DeadCall => None end.

  Definition cell_rdx (c : CallCell XYSig) : option nat :=
    match c with
    | ActiveCall o r => match o return xy_ar o -> option nat with RdX => fun r => Some r | WrY => fun _ => None end r
    | DeadCall => None
    end.

  (** The rely of the other call contains a return. *)
  Lemma return_in_rely k k' op r σ v pool pool2 γ :
    k <> k' -> I5 (σ, XOk v pool, γ) -> lin_remove k (ls_linr op r) pool pool2 ->
    R5 k' (σ, XOk v pool, γ) (σ, XOk v pool2, γ).
  Proof.
    intros Hne HI Hrem. split; [reflexivity |]. exists v, pool, v, pool2.
    split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
    eapply keeps_remove_other; [exact Hrem |]. intros Heq. apply Hne. symmetry. exact Heq.
  Qed.

  Lemma I5_remove k op r σ v pool pool2 γ :
    I5 (σ, XOk v pool, γ) -> lin_remove k (ls_linr op r) pool pool2 -> I5 (σ, XOk v pool2, γ).
  Proof.
    intros (y & pool1 & Hp & Hwf) Hrem. cbn in Hp. injection Hp as -> <-.
    exists y, pool2. split; [reflexivity | eapply lin_remove_well_formed; eauto].
  Qed.

  (** The return of an active call whose sub-queue is empty. *)
  Lemma call_return k op ret (c : TCfg) p :
    owner_done_tagged k (tm_queue c) ->
    (exists l, owner_subqueue k (tm_queue c) l /\ CallSafe I5 R5 G5 k op ret l (proj5 c p)) ->
    exists p1 v pool pool2,
      poss_steps XYLTS p p1 /\ p1 = XOk v pool /\ lin_remove k (ls_linr op ret) pool pool2 /\
      I5 (tm_lts_state c, p1, ghost_of (tm_queue c)) /\
      clos_refl _ (G5 k) (proj5 c p) (tm_lts_state c, p1, ghost_of (tm_queue c)) /\
      I5 (tm_lts_state c, XOk v pool2, ghost_of (tm_queue c)).
  Proof.
    intros Hdone (l & Hosq & Hcs). pose proof (osq_done _ _ _ Hdone Hosq) as ->.
    destruct (callsafe_inv _ _ _ _ _ Hcs) as (_ & _ & _ & Hret).
    destruct (Hret eq_refl (ghost_of_done _ _ Hdone)) as (p1 & Hps & (v & pool & -> & Hlk) & HI1 & HG & Hrm).
    destruct HI1 as (y & pool1 & Hp1 & Hwf). cbn in Hp1. injection Hp1 as Hv <-.
    destruct (lin_remove_exists k _ pool Hwf Hlk) as (pool2 & Hrem).
    exists (XOk v pool), v, pool, pool2. split; [exact Hps |]. split; [reflexivity |]. split; [exact Hrem |].
    split; [exists y, pool; cbn; split; [rewrite <- Hv; reflexivity | exact Hwf] |].
    split; [exact HG |].
    apply Hrm. constructor. destruct k as [tk hk]. exact Hrem.
  Qed.

  Definition NotInvoke (ev : ModuleEvent RlxSig XYSig) : Prop :=
    match ev with OverlayEvent x => is_response x | UnderlayEvent _ => True end.

  Definition StepMatch (ev : ModuleEvent RlxSig XYSig) (p p' : Poss XYLTS) : Prop :=
    match ev with
    | UnderlayEvent _ => poss_steps XYLTS p p'
    | OverlayEvent x =>
        match te_ev XYSig x with
        | InvEv _ _ => False
        | ResEv h op r => exists p1, poss_steps XYLTS p p1 /\ poss_return XYLTS (te_tid XYSig x) h op r p1 p'
        end
    end.

  Lemma k1_ne_k2 : k1 <> k2.
  Proof. discriminate. Qed.

  (** The emitting call moves by [ct_emit]; the other call by its rely. *)
  Lemma emit_case kE opE retE cellE kO opO retO cellO (c : TCfg) p cand queue' q' :
    kE <> kO -> ts_owner cand = kE ->
    select_frontier_tagged cand (tm_queue c) queue' ->
    Step MemLTS (untag (ts_event cand)) (tm_lts_state c) q' ->
    CallSt kE opE retE cellE c p -> CallSt kO opO retO cellO c p ->
    exists p', poss_steps XYLTS p p' /\
      I5 (q', p', ghost_of queue') /\
      CallSt kE opE retE cellE (Build_TaggedModuleConfig q' (tm_calls c) queue' (tm_used_underlay c)) p' /\
      CallSt kO opO retO cellO (Build_TaggedModuleConfig q' (tm_calls c) queue' (tm_used_underlay c)) p'.
  Proof.
    intros Hne Ho Hsel Hlts HstE HstO.
    destruct HstE as [[HcE (lE & HosqE & HtidE & HcsE)] | [_ HdoneE]].
    2: { exfalso. apply HdoneE. rewrite <- Ho. apply in_map. eapply select_frontier_tagged_member. exact Hsel. }
    destruct (select_project kE _ lE cand queue' HosqE HtidE Hsel)
      as [(_ & pre & post & -> & Hfr & HosqE') | (Hne' & _)]; [| contradiction].
    destruct (callsafe_inv _ _ _ _ _ HcsE) as (_ & Hemit & _ & _).
    assert (Hge : ghost_emit kE (untag (ts_event cand)) (ps_ghost (proj5 c p)) (ghost_of queue')).
    { rewrite <- Ho. exact (ghost_of_select _ _ _ Hsel). }
    destruct (Hemit pre (ts_event cand) post eq_refl Hfr (ghost_of queue') q' Hge Hlts)
      as (p' & Hps & HI' & HG & HcsE').
    exists p'. split; [exact Hps |]. split; [exact HI' |]. split.
    - left. split; [exact HcE |]. exists (pre ++ post). cbn [tm_queue].
      split; [exact HosqE' |]. split; [eapply Forall_remove; exact HtidE | exact HcsE'].
    - destruct HstO as [[HcO (lO & HosqO & HtidO & HcsO)] | [HcO HdoneO]].
      + left. split; [exact HcO |]. exists lO. cbn [tm_queue].
        destruct (select_project kO _ lO cand queue' HosqO HtidO Hsel)
          as [(Hown & _) | (_ & HosqO')]; [exfalso; apply Hne; rewrite <- Ho, Hown; reflexivity |].
        split; [exact HosqO' |]. split; [exact HtidO |].
        destruct (callsafe_inv _ _ _ _ _ HcsO) as (_ & _ & HrelyO & _).
        apply HrelyO; [| exact HI']. apply (G5_in_R5 kO kE); [exact Hne | exact HG].
      + right. split; [exact HcO |]. cbn [tm_queue]. eapply done_select; eauto.
  Qed.

  (** The returning call; the other call moves by its rely twice. *)
  Lemma return_case kR opR (retR : xy_ar opR) cellR kO opO retO cellO (c : TCfg) p :
    kR <> kO -> owner_done_tagged kR (tm_queue c) ->
    CallSt kR opR retR cellR c p -> cellR <> DeadCall -> CallSt kO opO retO cellO c p ->
    exists p1 p2, poss_steps XYLTS p p1 /\ poss_return XYLTS (fst kR) (snd kR) opR retR p1 p2 /\
      I5 (tm_lts_state c, p2, ghost_of (tm_queue c)) /\
      forall pool', CallSt kO opO retO cellO (Build_TaggedModuleConfig (tm_lts_state c) pool' (tm_queue c) (tm_used_underlay c)) p2.
  Proof.
    intros Hne Hdone HstR HnotDead HstO.
    destruct HstR as [[HcR (lR & HosqR & _ & HcsR)] | [HcR _]]; [| contradiction].
    destruct (call_return kR opR retR c p Hdone (ex_intro _ lR (conj HosqR HcsR)))
      as (p1 & v & pool & pool2 & Hps & -> & Hrem & HI1 & HG & HI2).
    exists (XOk v pool), (XOk v pool2). split; [exact Hps |].
    split; [constructor; destruct kR; exact Hrem |]. split; [exact HI2 |].
    intros pool'. destruct HstO as [[HcO (lO & HosqO & HtidO & HcsO)] | [HcO HdoneO]].
    - left. split; [exact HcO |]. exists lO. cbn [tm_queue]. split; [exact HosqO |]. split; [exact HtidO |].
      unfold proj5. cbn [tm_lts_state tm_queue].
      assert (Hcs1 : CallSafe I5 R5 G5 kO opO retO lO (tm_lts_state c, XOk v pool, ghost_of (tm_queue c)))
        by (eapply callsafe_refl_rely; [intros Heq; apply Hne; symmetry; exact Heq | exact HG | exact HI1 | exact HcsO]).
      destruct (callsafe_inv _ _ _ _ _ Hcs1) as (_ & _ & Hrely1 & _).
      apply Hrely1; [| exact HI2]. eapply return_in_rely; [exact Hne | exact HI1 | exact Hrem].
    - right. split; [exact HcO | exact HdoneO].
  Qed.

  Theorem two_calls_step ret1 ret2 ev c c' p :
    Inv2 ret1 ret2 c p -> module_step_tagged MemLTS M5 ev c c' -> NotInvoke ev ->
    exists p', StepMatch ev p p' /\ Inv2 ret1 ret2 c' p'.
  Proof.
    intros [HI Howner (cell1 & cell2 & Hcalls & Hst1 & Hst2)] Hstep Hni.
    destruct Hstep as [t h op q pool queue used trace ret Hfc Hmeth Hft
                     | cand q q' pool queue queue' used Hsel Hlts
                     | t h op ret q pool pool' queue used Hfinish Hdone].
    - (* an overlay invocation: excluded *) destruct Hni.
    - (* an underlay step *)
      cbn [tm_queue tm_calls tm_lts_state tm_used_underlay] in *.
      destruct (Howner cand (select_frontier_tagged_member _ _ _ Hsel)) as [Ho | Ho].
      + destruct (emit_case k1 RdX ret1 cell1 k2 WrY ret2 cell2 (Build_TaggedModuleConfig q pool queue used) p cand queue' q'
                    k1_ne_k2 Ho Hsel Hlts Hst1 Hst2) as (p' & Hps & HI' & Hst1' & Hst2').
        exists p'. split; [exact Hps |]. constructor; [exact HI' | |].
        * intros x Hx. apply Howner. eapply select_sub; eauto.
        * exists cell1, cell2. auto.
      + destruct (emit_case k2 WrY ret2 cell2 k1 RdX ret1 cell1 (Build_TaggedModuleConfig q pool queue used) p cand queue' q'
                    (not_eq_sym k1_ne_k2) Ho Hsel Hlts Hst2 Hst1) as (p' & Hps & HI' & Hst2' & Hst1').
        exists p'. split; [exact Hps |]. constructor; [exact HI' | |].
        * intros x Hx. apply Howner. eapply select_sub; eauto.
        * exists cell1, cell2. auto.
    - (* an overlay return *)
      cbn [tm_queue tm_calls tm_lts_state tm_used_underlay] in *. subst pool.
      destruct (finish_two _ _ _ _ _ _ _ Hfinish) as [(-> & -> & Hc2 & ->) | (-> & -> & Hc1 & ->)].
      + (* k2 returns *)
        assert (Hop : op = WrY).
        { destruct Hst2 as [[Hc _] | [Hc _]]; rewrite Hc2 in Hc; [| discriminate Hc].
          apply (f_equal cell_op) in Hc. cbn in Hc. injection Hc as ->. reflexivity. }
        subst op. destruct ret, ret2.
        destruct (return_case k2 WrY tt cell2 k1 RdX ret1 cell1 (Build_TaggedModuleConfig q _ queue used) p
                    (not_eq_sym k1_ne_k2) Hdone Hst2 ltac:(rewrite Hc2; discriminate) Hst1)
          as (p1 & p2 & Hps & Hret & HI2 & Hst1').
        exists p2. split; [exists p1; split; [exact Hps | exact Hret] |].
        constructor; [exact HI2 | exact Howner |].
        exists cell1, DeadCall. split; [reflexivity |]. split; [apply Hst1' |].
        right. split; [reflexivity | exact Hdone].
      + (* k1 returns *)
        assert (Hop : op = RdX).
        { destruct Hst1 as [[Hc _] | [Hc _]]; rewrite Hc1 in Hc; [| discriminate Hc].
          apply (f_equal cell_op) in Hc. cbn in Hc. injection Hc as ->. reflexivity. }
        subst op.
        assert (Hr : ret = ret1).
        { destruct Hst1 as [[Hc _] | [Hc _]]; rewrite Hc1 in Hc; [| discriminate Hc].
          apply (f_equal cell_rdx) in Hc. cbn in Hc. injection Hc as ->. reflexivity. }
        subst ret.
        destruct (return_case k1 RdX ret1 cell1 k2 WrY ret2 cell2 (Build_TaggedModuleConfig q _ queue used) p
                    k1_ne_k2 Hdone Hst1 ltac:(rewrite Hc1; discriminate) Hst2)
          as (p1 & p2 & Hps & Hret & HI2 & Hst2').
        exists p2. split; [exists p1; split; [exact Hps | exact Hret] |].
        constructor; [exact HI2 | exact Howner |].
        exists DeadCall, cell2. split; [reflexivity |]. split; [| apply Hst2'].
        right. split; [reflexivity | exact Hdone].
  Qed.

  Corollary two_calls_execution ret1 ret2 c p evs c' :
    Inv2 ret1 ret2 c p -> module_execution_tagged MemLTS M5 c evs c' -> Forall NotInvoke evs ->
    exists p', Inv2 ret1 ret2 c' p'.
  Proof.
    intros HI Hexec. revert p HI. induction Hexec as [c | c1 c2 c3 ev evs Hstep Hexec IH]; intros p HI Hall.
    - exists p. exact HI.
    - inversion Hall as [| ? ? Hni Hall']; subst.
      destruct (two_calls_step _ _ _ _ _ _ HI Hstep Hni) as (p' & _ & HI').
      exact (IH p' HI' Hall').
  Qed.

  (** The two overlay invocations, from the initial module. *)
  Theorem two_calls_init c1 c2 :
    module_step_tagged MemLTS M5 (OverlayEvent (Build_ThreadEvent t5 (@InvEv XYSig 1 RdX)))
      (initial_tagged_module MemLTS σ0) c1 ->
    module_step_tagged MemLTS M5 (OverlayEvent (Build_ThreadEvent t5 (@InvEv XYSig 2 WrY))) c1 c2 ->
    exists ret1 ret2 p1 p2,
      poss_invoke XYLTS t5 1 RdX (XOk (0, 0) []) p1 /\ poss_invoke XYLTS t5 2 WrY p1 p2 /\
      Inv2 ret1 ret2 c2 p2.
  Proof.
    intros H1 H2. unfold initial_tagged_module in H1.
    inversion H1 as [t h op q pool queue used tr1 ret1 Hfc1 Hprod1 Hft1 | |]; subst.
    inversion H2 as [t h op q pool queue used tr2 ret2 Hfc2 Hprod2 Hft2 | |]; subst.
    set (p1 := XOk (0, 0) [make_lin_entry k1 (@ls_inv XYSig RdX)]).
    set (p2 := XOk (0, 0) [make_lin_entry k2 (@ls_inv XYSig WrY); make_lin_entry k1 (@ls_inv XYSig RdX)]).
    assert (Hinv1 : poss_invoke XYLTS t5 1 RdX (XOk (0, 0) []) p1) by (constructor; constructor; intros []).
    assert (Hinv2 : poss_invoke XYLTS t5 2 WrY p1 p2).
    { constructor. constructor. intros [H | []]. discriminate H. }
    exists ret1, ret2, p1, p2. split; [exact Hinv1 |]. split; [exact Hinv2 |].
    destruct (methodsem_safe I5 R5 G5 M5 t5 RdX (rdx_sound t5) 1 tr1 ret1 Hprod1 σ0 (XOk (0, 0) []) [] p1 I5_init Hinv1)
      as [HI1 Hcs1].
    destruct (methodsem_safe I5 R5 G5 M5 t5 WrY (wry_sound t5) 2 tr2 ret2 Hprod2 σ0 p1 _ p2 HI1 Hinv2)
      as [HI2 Hcs2].
    assert (Hcs1' : CallSafe I5 R5 G5 k1 RdX ret1 tr1 (σ0, p2, ([] ++ ghost_new k1 tr1) ++ ghost_new k2 tr2)).
    { destruct (callsafe_inv _ _ _ _ _ Hcs1) as (_ & _ & Hrely & _). apply Hrely; [| exact HI2].
      exact (h_invoke_rely _ _ _ _ _ _ xy_rlhl2 k2 k1 WrY tr2 ret2 (σ0, p1, [] ++ ghost_new k1 tr1) p2
               (not_eq_sym k1_ne_k2) Hprod2 HI1 Hinv2). }
    constructor.
    - unfold proj5. cbn [tm_lts_state tm_queue]. rewrite ghost_of_app, !ghost_of_schedule. exact HI2.
    - intros x Hx. cbn [tm_queue] in Hx. apply in_app_or in Hx.
      destruct Hx as [Hx | Hx]; unfold schedule_trace_tagged in Hx; apply in_map_iff in Hx;
        destruct Hx as (m & <- & _); [left | right]; reflexivity.
    - exists (@ActiveCall XYSig RdX ret1), (@ActiveCall XYSig WrY ret2). cbn [tm_calls]. split; [reflexivity |]. split.
      + left. split; [reflexivity |]. exists (tr1 ++ []). cbn [tm_queue].
        split; [apply osq_app; [apply osq_schedule_own | apply osq_schedule_other; discriminate] |].
        split; [rewrite app_nil_r; exact (program_produces_tagged_trace_tid _ _ _ _ Hprod1) |].
        unfold proj5. cbn [tm_lts_state tm_queue]. rewrite ghost_of_app, !ghost_of_schedule, app_nil_r. exact Hcs1'.
      + left. split; [reflexivity |]. exists ([] ++ tr2). cbn [tm_queue].
        split; [apply osq_app; [apply osq_schedule_other; discriminate | apply osq_schedule_own] |].
        split; [exact (program_produces_tagged_trace_tid _ _ _ _ Hprod2) |].
        unfold proj5. cbn [tm_lts_state tm_queue]. rewrite ghost_of_app, !ghost_of_schedule. exact Hcs2.
  Qed.

  (** ** The two overlay invocations from the initial module *)

  Lemma two_invokes {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) q0
      ta ha opa tb hb opb c1 c2 :
    module_step_tagged VE M (OverlayEvent (Build_ThreadEvent ta (@InvEv F ha opa)))
      (initial_tagged_module VE q0) c1 ->
    module_step_tagged VE M (OverlayEvent (Build_ThreadEvent tb (@InvEv F hb opb))) c1 c2 ->
    exists tr1 ret1 tr2 ret2,
      program_produces_tagged ta (M opa ta) tr1 ret1 /\ program_produces_tagged tb (M opb tb) tr2 ret2 /\
      trace_fresh (invocation_keys (map untag tr1)) (map untag tr2) /\
      c2 = Build_TaggedModuleConfig q0
             [Build_CallEntry tb hb (ActiveCall opb ret2); Build_CallEntry ta ha (ActiveCall opa ret1)]
             (schedule_trace_tagged (ta, ha) tr1 ++ schedule_trace_tagged (tb, hb) tr2)
             (invocation_keys (map untag tr1) ++ invocation_keys (map untag tr2)).
  Proof.
    intros H1 H2.
    remember (OverlayEvent (Build_ThreadEvent ta (@InvEv F ha opa))) as e1 eqn:He1.
    remember (initial_tagged_module VE q0) as c0 eqn:Hc0.
    destruct H1 as [t h op q pool queue used tr1 ret1 Hfc1 Hprod1 Hft1 | cand q q' pool queue queue' used Hsel Hlts
                   | t h op ret q pool pool' queue used Hfin Hdone]; [| discriminate He1 | discriminate He1].
    injection He1 as Ht Hh Hop. subst t h op.
    unfold initial_tagged_module in Hc0. injection Hc0 as -> -> -> ->.
    remember (OverlayEvent (Build_ThreadEvent tb (@InvEv F hb opb))) as e2 eqn:He2.
    remember (Build_TaggedModuleConfig q0 [Build_CallEntry ta ha (ActiveCall opa ret1)]
               ([] ++ schedule_trace_tagged (ta, ha) tr1) ([] ++ invocation_keys (map untag tr1))) as c1 eqn:Hc1.
    destruct H2 as [t h op q pool queue used tr2 ret2 Hfc2 Hprod2 Hft2 | cand q q' pool queue queue' used Hsel Hlts
                   | t h op ret q pool pool' queue used Hfin Hdone]; [| discriminate He2 | discriminate He2].
    injection He2 as Ht Hh Hop. subst t h op.
    injection Hc1 as -> -> -> ->.
    exists tr1, ret1, tr2, ret2. split; [exact Hprod1 |]. split; [exact Hprod2 |]. split; [exact Hft2 |].
    reflexivity.
  Qed.

  Lemma select_cross {E F : RelaxedSig.t} (cand : TaggedScheduledEvent E F) pre post :
    Forall (fun e => tagged_can_cross (ts_event e) (ts_event cand)) pre ->
    select_frontier_tagged cand (pre ++ cand :: post) (pre ++ post).
  Proof.
    induction pre as [| x pre IH]; intros Hall; cbn; [apply tagged_select_here |].
    inversion Hall as [| ? ? Hx Hall']; subst. apply tagged_select_next; [exact Hx | exact (IH Hall')].
  Qed.

  Lemma inv_events_responses {E : RelaxedSig.t} (l : list (TaggedEvent E)) :
    Forall (fun m => is_response (untag m)) l -> inv_events (map untag l) = [].
  Proof.
    induction 1 as [| m l Hm Hl IH]; cbn; [reflexivity |].
    unfold is_response in Hm. destruct (te_ev E (untag m)); [destruct Hm | exact IH].
  Qed.

  (** ** (b), M-12, m-18: the reordering on the configuration of
      [two_calls_init]

      From every configuration reached by the two overlay invocations of
      [two_calls_init], the module can emit the invocation of [k2] (a
      write of [Y]) before any event of [k1] (a read of [X]): it crosses
      the invocation of [k1] ((F2) does not apply, the locations differ)
      and its response ((F3) does not apply, the tag is empty).  The
      traces are derived from the module steps and [call_trace]. *)

  Theorem two_calls_reorder c1 c2 :
    module_step_tagged MemLTS M5 (OverlayEvent (Build_ThreadEvent t5 (@InvEv XYSig 1 RdX)))
      (initial_tagged_module MemLTS σ0) c1 ->
    module_step_tagged MemLTS M5 (OverlayEvent (Build_ThreadEvent t5 (@InvEv XYSig 2 WrY))) c1 c2 ->
    exists hy c3,
      module_step_tagged MemLTS M5 (UnderlayEvent (Build_ThreadEvent t5 (@InvEv RlxSig hy (MWrite Y 1)))) c2 c3 /\
      (forall x, In x (tm_queue c2) -> ts_owner x = k1 -> In x (tm_queue c3)).
  Proof.
    intros H1 H2.
    destruct (two_invokes MemLTS M5 σ0 t5 1 RdX t5 2 WrY c1 c2 H1 H2)
      as (tr1 & ret1 & tr2 & ret2 & Hp1 & Hp2 & _ & ->).
    destruct (call_trace (E := RlxSig) t5 (MRead X) tr1 ret1 Hp1) as (hx & rest1 & -> & Hrest1).
    destruct (call_trace (E := RlxSig) t5 (MWrite Y 1) tr2 ret2 Hp2) as (hy & rest2 & -> & _).
    set (inv2 := Build_TaggedEvent (Build_ThreadEvent t5 (@InvEv RlxSig hy (MWrite Y 1))) (resolved_in (@empty_store RlxSig))).
    exists hy. eexists.
    split.
    - change (Build_ThreadEvent t5 (@InvEv RlxSig hy (MWrite Y 1))) with (untag (ts_event (Build_TaggedScheduledEvent k2 inv2))).
      apply tagged_underlay; [| reflexivity].
      cbn [schedule_trace_tagged map]. apply select_cross.
      constructor.
      + right. split; [reflexivity |]. unfold must_precede. cbn. intros Hm. apply Hm.
        unfold rlx_independent. cbn. discriminate.
      + rewrite Forall_forall in Hrest1 |- *. intros e He. apply in_map_iff in He as (m & <- & Hm).
        pose proof (Hrest1 m Hm) as Hr. unfold is_response in Hr. right. cbn [ts_event]. split.
        * pose proof (program_produces_tagged_trace_tid _ _ _ _ Hp1) as Ht. inversion Ht as [| ? ? _ Ht']; subst.
          rewrite Forall_forall in Ht'. rewrite (Ht' m Hm). reflexivity.
        * unfold must_precede. destruct (te_ev RlxSig (untag m)); [destruct Hr |]. cbn. apply resolved_in_empty.
    - intros x Hx Ho. cbn [tm_queue] in Hx |- *. apply in_app_or in Hx. apply in_or_app.
      destruct Hx as [Hx | Hx]; [left; exact Hx |].
      exfalso. unfold schedule_trace_tagged in Hx. apply in_map_iff in Hx as (m & <- & _). discriminate Ho.
  Qed.

  (** ** M-16 (iii): a generic two-call prototype of RLHL-2

      [TwoCallsGen] generalizes the XY prototype [two_calls_*] above to
      every instance of [RLHL2Hyps] and every two calls [ka = (ta, ha)],
      [kb = (tb, hb)] invoked in this order from the initial module
      (the same thread is allowed):
      - [gtwo_init]: after the two [tagged_invoke] steps, [GInv2] holds
        together with the two abstract invocations;
      - [gtwo_step]: every later module step that is not an overlay
        invocation preserves [GInv2]; an underlay step is matched by
        [poss_steps], an overlay return by [poss_steps] and [poss_return]
        with the returned value (the clauses of [RelaxedGSim.gsim_step]).
      [GInv2] is "[I] at the projected state [(tm_lts_state c, p,
      ghost_of (tm_queue c))], and every active call has a [CallSafe] on
      its owner sub-queue".  Every field of [RLHL2Hyps] is used: [h_sem]
      and [h_init] in [gtwo_init], [h_invoke_rely] for the first call at
      the second invocation, [h_guar_rely] for the other call at an
      underlay step, [h_ok] and [h_return_rely] at a return.  This is the
      shape of RLHL-2 for two calls; a third invocation is not covered.
      The general case is [RelaxedHoareGSim.rlhl_gsim]. *)

  Lemma gfinish_two {F : RelaxedSig.t} (ta tb : tid) (ha hb : RelaxedSig.handle F) t h op ret cella cellb
      (pool' : CallPool F) :
    finish_call t h op ret [Build_CallEntry tb hb cellb; Build_CallEntry ta ha cella] pool' ->
    (t = tb /\ h = hb /\ cellb = ActiveCall op ret /\
     pool' = [Build_CallEntry tb hb DeadCall; Build_CallEntry ta ha cella]) \/
    (t = ta /\ h = ha /\ cella = ActiveCall op ret /\
     pool' = [Build_CallEntry tb hb cellb; Build_CallEntry ta ha DeadCall]).
  Proof.
    intros Hf. inversion Hf as [tail Heq1 Heq2 | t' h' cell pool pool'' Hneq Hf' Heq1 Heq2]; subst.
    - left. auto.
    - right. inversion Hf' as [tail' Heq1' Heq2' | t'' h'' cell' pool1 pool1' Hneq' Hf'' Heq1' Heq2']; subst.
      + auto.
      + inversion Hf''.
  Qed.

  Section TwoCallsGen.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (M : RelaxedModuleImpl E F).
    Context (σi : State VE) (vi : State VF) (HH : RLHL2Hyps I R G M σi vi).
    Context (ta tb : tid) (ha hb : RelaxedSig.handle F).
    Local Abbreviation ka := (@pair tid (RelaxedSig.handle F) ta ha).
    Local Abbreviation kb := (@pair tid (RelaxedSig.handle F) tb hb).
    Context (Hab : ka <> kb).

    Abbreviation GCfg := (@TaggedModuleConfig E F VE).

    Definition gproj (c : GCfg) (p : Poss VF) : PState VE VF := (tm_lts_state c, p, ghost_of (tm_queue c)).

    Definition GCallSt (k : CallKey F) (cell : CallCell F) (c : GCfg) (p : Poss VF) : Prop :=
      match cell with
      | ActiveCall op ret => exists l, owner_subqueue k (tm_queue c) l /\
          Forall (fun m => te_tid E (untag m) = fst k) l /\ CallSafe I R G k op ret l (gproj c p)
      | DeadCall => owner_done_tagged k (tm_queue c)
      end.

    Record GInv2 (c : GCfg) (p : Poss VF) : Prop := {
      g2_I : I (gproj c p);
      g2_owner : forall x, In x (tm_queue c) -> ts_owner x = ka \/ ts_owner x = kb;
      g2_calls : exists cella cellb,
        tm_calls c = [Build_CallEntry tb hb cellb; Build_CallEntry ta ha cella] /\
        GCallSt ka cella c p /\ GCallSt kb cellb c p
    }.

    Lemma gcallsafe_inv k op ret l s :
      CallSafe I R G k op ret l s ->
      I s /\
      (forall pre m post, l = pre ++ m :: post -> local_frontier pre m ->
         forall γ' σ', ghost_emit k (untag m) (ps_ghost s) γ' -> Step VE (untag m) (ps_mem s) σ' ->
           exists p', poss_steps VF (ps_poss s) p' /\ I (σ', p', γ') /\
                      G k s (σ', p', γ') /\ CallSafe I R G k op ret (pre ++ post) (σ', p', γ')) /\
      (forall s', R k s s' -> I s' -> CallSafe I R G k op ret l s') /\
      (l = [] -> NoOwn k (ps_ghost s) -> RetCond I G k op ret s).
    Proof. intros Hcs. destruct Hcs as [l s HI Hemit Hrely Hret]. auto. Qed.

    Lemma gcallsafe_refl_rely k op ret l k' s s' :
      k <> k' -> clos_refl _ (G k') s s' -> I s' ->
      CallSafe I R G k op ret l s -> CallSafe I R G k op ret l s'.
    Proof.
      intros Hne HG HI Hcs. destruct HG as [s'' HG |]; [| exact Hcs].
      destruct (gcallsafe_inv _ _ _ _ _ Hcs) as (_ & _ & Hrely & _).
      apply Hrely; [| exact HI].
      apply (h_guar_rely _ _ _ _ _ _ HH k' k); [intros Heq; apply Hne; symmetry; exact Heq | exact HG].
    Qed.

    Lemma gselect_sub (cand : TaggedScheduledEvent E F) q q' x :
      select_frontier_tagged cand q q' -> In x q' -> In x q.
    Proof.
      intros Hsel Hx. destruct (select_split _ _ _ Hsel) as (pre & post & -> & -> & _).
      apply in_app_or in Hx. apply in_or_app. destruct Hx; [left | right; right]; assumption.
    Qed.

    Lemma gdone_select k (cand : TaggedScheduledEvent E F) q q' :
      select_frontier_tagged cand q q' -> owner_done_tagged k q -> owner_done_tagged k q'.
    Proof.
      intros Hsel Hd Hin. apply Hd. apply in_map_iff in Hin. destruct Hin as (x & <- & Hx).
      apply in_map. eapply gselect_sub; eauto.
    Qed.

    (** The emitting call moves by its [CallSafe]; the other call by its
        rely ([h_guar_rely]). *)
    Lemma gemit_case kE cellE kO cellO (c : GCfg) p cand queue' q' :
      kE <> kO -> ts_owner cand = kE ->
      select_frontier_tagged cand (tm_queue c) queue' ->
      Step VE (untag (ts_event cand)) (tm_lts_state c) q' ->
      GCallSt kE cellE c p -> GCallSt kO cellO c p ->
      exists p', poss_steps VF p p' /\ I (q', p', ghost_of queue') /\
        GCallSt kE cellE (Build_TaggedModuleConfig q' (tm_calls c) queue' (tm_used_underlay c)) p' /\
        GCallSt kO cellO (Build_TaggedModuleConfig q' (tm_calls c) queue' (tm_used_underlay c)) p'.
    Proof.
      intros Hne Ho Hsel Hlts HstE HstO.
      destruct cellE as [opE retE |]; cbn [GCallSt] in HstE.
      2: { exfalso. apply HstE. rewrite <- Ho. apply in_map. eapply select_frontier_tagged_member. exact Hsel. }
      destruct HstE as (lE & HosqE & HtidE & HcsE).
      destruct (select_project kE _ lE cand queue' HosqE HtidE Hsel)
        as [(_ & pre & post & -> & Hfr & HosqE') | (Hne' & _)]; [| contradiction].
      destruct (gcallsafe_inv _ _ _ _ _ HcsE) as (_ & Hemit & _ & _).
      assert (Hge : ghost_emit kE (untag (ts_event cand)) (ps_ghost (gproj c p)) (ghost_of queue')).
      { rewrite <- Ho. exact (ghost_of_select _ _ _ Hsel). }
      destruct (Hemit pre (ts_event cand) post eq_refl Hfr (ghost_of queue') q' Hge Hlts)
        as (p' & Hps & HI' & HG & HcsE').
      exists p'. split; [exact Hps |]. split; [exact HI' |]. split.
      - exists (pre ++ post). cbn [tm_queue].
        split; [exact HosqE' |]. split; [eapply Forall_remove; exact HtidE | exact HcsE'].
      - destruct cellO as [opO retO |]; cbn [GCallSt] in HstO |- *.
        + destruct HstO as (lO & HosqO & HtidO & HcsO). exists lO. cbn [tm_queue].
          destruct (select_project kO _ lO cand queue' HosqO HtidO Hsel)
            as [(Hown & _) | (_ & HosqO')]; [exfalso; apply Hne; rewrite <- Ho, Hown; reflexivity |].
          split; [exact HosqO' |]. split; [exact HtidO |].
          destruct (gcallsafe_inv _ _ _ _ _ HcsO) as (_ & _ & HrelyO & _).
          apply HrelyO; [| exact HI']. apply (h_guar_rely _ _ _ _ _ _ HH kE kO); [exact Hne | exact HG].
        + cbn [tm_queue]. eapply gdone_select; eauto.
    Qed.

    (** The return of an active call whose sub-queue is empty ([h_ok]). *)
    Lemma gcall_return k op ret (c : GCfg) p :
      owner_done_tagged k (tm_queue c) ->
      (exists l, owner_subqueue k (tm_queue c) l /\ CallSafe I R G k op ret l (gproj c p)) ->
      exists v pool pool2,
        poss_steps VF p (PossOk v pool) /\ lin_remove k (ls_linr op ret) pool pool2 /\
        I (tm_lts_state c, PossOk v pool, ghost_of (tm_queue c)) /\
        clos_refl _ (G k) (gproj c p) (tm_lts_state c, PossOk v pool, ghost_of (tm_queue c)) /\
        I (tm_lts_state c, PossOk v pool2, ghost_of (tm_queue c)).
    Proof.
      intros Hdone (l & Hosq & Hcs). pose proof (osq_done _ _ _ Hdone Hosq) as ->.
      destruct (gcallsafe_inv _ _ _ _ _ Hcs) as (_ & _ & _ & Hret).
      destruct (Hret eq_refl (ghost_of_done _ _ Hdone)) as (p1 & Hps & (v & pool & -> & Hlk) & HI1 & HG & Hrm).
      destruct (h_ok _ _ _ _ _ _ HH _ HI1) as (v' & pool' & Hp1 & Hwf). cbn in Hp1. injection Hp1 as <- <-.
      destruct (lin_remove_exists k _ pool Hwf Hlk) as (pool2 & Hrem).
      exists v, pool, pool2. split; [exact Hps |]. split; [exact Hrem |]. split; [exact HI1 |].
      split; [exact HG |]. apply Hrm. constructor. destruct k as [tk hk]. exact Hrem.
    Qed.

    (** The returning call; the other call moves by its rely twice
        ([h_guar_rely], then [h_return_rely]). *)
    Lemma greturn_case kR opR (retR : Sig.ar opR) kO cellO (c : GCfg) p :
      kR <> kO -> owner_done_tagged kR (tm_queue c) ->
      GCallSt kR (ActiveCall opR retR) c p -> GCallSt kO cellO c p ->
      exists p1 p2, poss_steps VF p p1 /\ poss_return VF (fst kR) (snd kR) opR retR p1 p2 /\
        I (tm_lts_state c, p2, ghost_of (tm_queue c)) /\
        forall pool', GCallSt kO cellO
                        (Build_TaggedModuleConfig (tm_lts_state c) pool' (tm_queue c) (tm_used_underlay c)) p2.
    Proof.
      intros Hne Hdone HstR HstO. cbn [GCallSt] in HstR. destruct HstR as (lR & HosqR & _ & HcsR).
      destruct (gcall_return kR opR retR c p Hdone (ex_intro _ lR (conj HosqR HcsR)))
        as (v & pool & pool2 & Hps & Hrem & HI1 & HG & HI2).
      assert (Hpr : poss_return VF (fst kR) (snd kR) opR retR (PossOk v pool) (PossOk v pool2))
        by (constructor; destruct kR; exact Hrem).
      exists (PossOk v pool), (PossOk v pool2). split; [exact Hps |]. split; [exact Hpr |]. split; [exact HI2 |].
      intros pool'. destruct cellO as [opO retO |]; cbn [GCallSt] in HstO |- *.
      - destruct HstO as (lO & HosqO & HtidO & HcsO). exists lO. cbn [tm_queue].
        split; [exact HosqO |]. split; [exact HtidO |].
        unfold gproj. cbn [tm_lts_state tm_queue].
        assert (Hcs1 : CallSafe I R G kO opO retO lO (tm_lts_state c, PossOk v pool, ghost_of (tm_queue c)))
          by (eapply gcallsafe_refl_rely; [intros Heq; apply Hne; symmetry; exact Heq | exact HG | exact HI1 | exact HcsO]).
        destruct (gcallsafe_inv _ _ _ _ _ Hcs1) as (_ & _ & Hrely1 & _).
        apply Hrely1; [| exact HI2].
        exact (h_return_rely _ _ _ _ _ _ HH kR kO opR retR (tm_lts_state c, PossOk v pool, ghost_of (tm_queue c))
                 (PossOk v pool2) Hne HI1 Hpr (ghost_of_done _ _ Hdone)).
      - exact HstO.
    Qed.

    Definition GNotInvoke (ev : ModuleEvent E F) : Prop :=
      match ev with OverlayEvent x => is_response x | UnderlayEvent _ => True end.

    Definition GStepMatch (ev : ModuleEvent E F) (p p' : Poss VF) : Prop :=
      match ev with
      | UnderlayEvent _ => poss_steps VF p p'
      | OverlayEvent x =>
          match te_ev F x with
          | InvEv _ _ => False
          | ResEv h op r => exists p1, poss_steps VF p p1 /\ poss_return VF (te_tid F x) h op r p1 p'
          end
      end.

    Theorem gtwo_step ev c c' p :
      GInv2 c p -> module_step_tagged VE M ev c c' -> GNotInvoke ev ->
      exists p', GStepMatch ev p p' /\ GInv2 c' p'.
    Proof.
      intros [HI Howner (cella & cellb & Hcalls & Hsta & Hstb)] Hstep Hni.
      destruct Hstep as [t h op q pool queue used trace ret Hfc Hmeth Hft
                       | cand q q' pool queue queue' used Hsel Hlts
                       | t h op ret q pool pool' queue used Hfinish Hdone].
      - destruct Hni.
      - cbn [tm_queue tm_calls tm_lts_state tm_used_underlay] in *.
        destruct (Howner cand (select_frontier_tagged_member _ _ _ Hsel)) as [Ho | Ho].
        + destruct (gemit_case ka cella kb cellb (Build_TaggedModuleConfig q pool queue used) p cand queue' q'
                      Hab Ho Hsel Hlts Hsta Hstb) as (p' & Hps & HI' & Hsta' & Hstb').
          exists p'. split; [exact Hps |]. constructor; [exact HI' | |].
          * intros x Hx. apply Howner. eapply gselect_sub; eauto.
          * exists cella, cellb. auto.
        + destruct (gemit_case kb cellb ka cella (Build_TaggedModuleConfig q pool queue used) p cand queue' q'
                      (not_eq_sym Hab) Ho Hsel Hlts Hstb Hsta) as (p' & Hps & HI' & Hstb' & Hsta').
          exists p'. split; [exact Hps |]. constructor; [exact HI' | |].
          * intros x Hx. apply Howner. eapply gselect_sub; eauto.
          * exists cella, cellb. auto.
      - cbn [tm_queue tm_calls tm_lts_state tm_used_underlay] in *. subst pool.
        destruct (gfinish_two ta tb ha hb _ _ _ _ _ _ _ Hfinish) as [(-> & -> & -> & ->) | (-> & -> & -> & ->)].
        + destruct (greturn_case kb op ret ka cella (Build_TaggedModuleConfig q
                      [Build_CallEntry tb hb (ActiveCall op ret); Build_CallEntry ta ha cella] queue used) p
                      (not_eq_sym Hab) Hdone Hstb Hsta) as (p1 & p2 & Hps & Hret & HI2 & Hsta').
          exists p2. split; [exists p1; split; [exact Hps | exact Hret] |].
          constructor; [exact HI2 | exact Howner |].
          exists cella, DeadCall. split; [reflexivity |]. split; [apply Hsta' | exact Hdone].
        + destruct (greturn_case ka op ret kb cellb (Build_TaggedModuleConfig q
                      [Build_CallEntry tb hb cellb; Build_CallEntry ta ha (ActiveCall op ret)] queue used) p
                      Hab Hdone Hsta Hstb) as (p1 & p2 & Hps & Hret & HI2 & Hstb').
          exists p2. split; [exists p1; split; [exact Hps | exact Hret] |].
          constructor; [exact HI2 | exact Howner |].
          exists DeadCall, cellb. split; [reflexivity |]. split; [exact Hdone | apply Hstb'].
    Qed.

    Corollary gtwo_execution c p evs c' :
      GInv2 c p -> module_execution_tagged VE M c evs c' -> Forall GNotInvoke evs ->
      exists p', GInv2 c' p'.
    Proof.
      intros HI Hexec. revert p HI. induction Hexec as [c | c1 c2 c3 ev evs Hstep Hexec IH]; intros p HI Hall.
      - exists p. exact HI.
      - inversion Hall as [| ? ? Hni Hall']; subst.
        destruct (gtwo_step _ _ _ _ HI Hstep Hni) as (p' & _ & HI').
        exact (IH p' HI' Hall').
    Qed.

    (** The two overlay invocations, from the initial module. *)
    Theorem gtwo_init opa opb c1 c2 :
      module_step_tagged VE M (OverlayEvent (Build_ThreadEvent ta (@InvEv F ha opa)))
        (initial_tagged_module VE σi) c1 ->
      module_step_tagged VE M (OverlayEvent (Build_ThreadEvent tb (@InvEv F hb opb))) c1 c2 ->
      exists p1 p2, poss_invoke VF ta ha opa (PossOk vi []) p1 /\ poss_invoke VF tb hb opb p1 p2 /\
        GInv2 c2 p2.
    Proof.
      intros H1 H2.
      destruct (two_invokes VE M σi ta ha opa tb hb opb c1 c2 H1 H2)
        as (tr1 & ret1 & tr2 & ret2 & Hprod1 & Hprod2 & _ & ->).
      set (p1 := PossOk vi [make_lin_entry ka (ls_inv opa)] : Poss VF).
      set (p2 := PossOk vi [make_lin_entry kb (ls_inv opb); make_lin_entry ka (ls_inv opa)] : Poss VF).
      assert (Hinv1 : poss_invoke VF ta ha opa (PossOk vi []) p1) by (constructor; constructor; intros []).
      assert (Hinv2 : poss_invoke VF tb hb opb p1 p2).
      { constructor. constructor. intros [Heq | []]. apply Hab. exact Heq. }
      exists p1, p2. split; [exact Hinv1 |]. split; [exact Hinv2 |].
      destruct (methodsem_safe I R G M ta opa (h_sem _ _ _ _ _ _ HH ta opa) ha tr1 ret1 Hprod1 σi (PossOk vi []) [] p1
                  (h_init _ _ _ _ _ _ HH) Hinv1) as [HI1 Hcs1].
      destruct (methodsem_safe I R G M tb opb (h_sem _ _ _ _ _ _ HH tb opb) hb tr2 ret2 Hprod2 σi p1 _ p2 HI1 Hinv2)
        as [HI2 Hcs2].
      assert (Hcs1' : CallSafe I R G ka opa ret1 tr1 (σi, p2, ([] ++ ghost_new ka tr1) ++ ghost_new kb tr2)).
      { destruct (gcallsafe_inv _ _ _ _ _ Hcs1) as (_ & _ & Hrely & _). apply Hrely; [| exact HI2].
        exact (h_invoke_rely _ _ _ _ _ _ HH kb ka opb tr2 ret2 (σi, p1, [] ++ ghost_new ka tr1) p2
                 (not_eq_sym Hab) Hprod2 HI1 Hinv2). }
      cbn [app] in HI2, Hcs1', Hcs2.
      constructor.
      - unfold gproj. cbn [tm_lts_state tm_queue]. rewrite ghost_of_app, !ghost_of_schedule. exact HI2.
      - intros x Hx. cbn [tm_queue] in Hx. apply in_app_or in Hx.
        destruct Hx as [Hx | Hx]; unfold schedule_trace_tagged in Hx; apply in_map_iff in Hx;
          destruct Hx as (m & <- & _); [left | right]; reflexivity.
      - exists (ActiveCall opa ret1), (ActiveCall opb ret2). cbn [tm_calls]. split; [reflexivity |]. split.
        + exists (tr1 ++ []). cbn [tm_queue].
          split; [apply osq_app; [apply osq_schedule_own | apply osq_schedule_other; exact (not_eq_sym Hab)] |].
          split; [rewrite app_nil_r; exact (program_produces_tagged_trace_tid _ _ _ _ Hprod1) |].
          unfold gproj. cbn [tm_lts_state tm_queue]. rewrite ghost_of_app, !ghost_of_schedule, app_nil_r. exact Hcs1'.
        + exists ([] ++ tr2). cbn [tm_queue].
          split; [apply osq_app; [apply osq_schedule_other; exact Hab | apply osq_schedule_own] |].
          split; [exact (program_produces_tagged_trace_tid _ _ _ _ Hprod2) |].
          unfold gproj. cbn [tm_lts_state tm_queue]. rewrite ghost_of_app, !ghost_of_schedule. exact Hcs2.
    Qed.
  End TwoCallsGen.

  (** ** M-16 (iii): two overlapping [Inc] calls of one thread

      The instance of [TwoCallsGen] for [CounterHL] ([counter_hl_rlhl2])
      and the calls [(t, 1)] and [(t, 2)] of one thread: [inc_two_init],
      [inc_two_step], [inc_two_execution].  [inc_two_blocked]: in the
      configuration after the two invocations, the ghost holds the two
      pending FAA invocations in age order, [inv_blocks] relates them, the
      second call's FAA has no [ghost_emit] transition, and the module
      cannot select any invocation of the second call.  So the (F2) order
      across calls is enforced by the module, mirrored by the ghost, and
      used by [CounterHL.faa_updateh] (through [Counter.emit_ready]); it is
      what makes the counter's abstract invocations linearize in
      invocation order. *)

  Module IncTwo.
    Import Counter CounterHL.

    Section S.
      Context (t : tid).

      Lemma k12_ne : (@pair tid (RelaxedSig.handle OSig) t 1) <> (t, 2).
      Proof. intros Heq. injection Heq. discriminate. Qed.

      Theorem inc_two_init c1 c2 :
        module_step_tagged HVE Mc (OverlayEvent (Build_ThreadEvent t (@InvEv OSig 1 Inc)))
          (initial_tagged_module HVE hσ0) c1 ->
        module_step_tagged HVE Mc (OverlayEvent (Build_ThreadEvent t (@InvEv OSig 2 Inc))) c1 c2 ->
        exists p1 p2, poss_invoke CVFe t 1 Inc (EOk (0, []) []) p1 /\ poss_invoke CVFe t 2 Inc p1 p2 /\
          GInv2 Ih Rh Gh t t 1 2 c2 p2.
      Proof. exact (gtwo_init Ih Rh Gh Mc hσ0 (0, []) counter_hl_rlhl2 t t 1 2 k12_ne Inc Inc c1 c2). Qed.

      Theorem inc_two_step ev c c' p :
        GInv2 Ih Rh Gh t t 1 2 c p -> module_step_tagged HVE Mc ev c c' -> GNotInvoke ev ->
        exists p', GStepMatch ev p p' /\ GInv2 Ih Rh Gh t t 1 2 c' p'.
      Proof. exact (gtwo_step Ih Rh Gh Mc hσ0 (0, []) counter_hl_rlhl2 t t 1 2 k12_ne ev c c' p). Qed.

      Corollary inc_two_execution c p evs c' :
        GInv2 Ih Rh Gh t t 1 2 c p -> module_execution_tagged HVE Mc c evs c' -> Forall GNotInvoke evs ->
        exists p', GInv2 Ih Rh Gh t t 1 2 c' p'.
      Proof. exact (gtwo_execution Ih Rh Gh Mc hσ0 (0, []) counter_hl_rlhl2 t t 1 2 k12_ne c p evs c'). Qed.

      Theorem inc_two_blocked c1 c2 :
        module_step_tagged HVE Mc (OverlayEvent (Build_ThreadEvent t (@InvEv OSig 1 Inc)))
          (initial_tagged_module HVE hσ0) c1 ->
        module_step_tagged HVE Mc (OverlayEvent (Build_ThreadEvent t (@InvEv OSig 2 Inc))) c1 c2 ->
        exists hu1 hu2,
          ghost_of (tm_queue c2) =
            [@Build_ScheduledEvent USig OSig (t, 1) (Build_ThreadEvent t (@InvEv USig hu1 FAA));
             @Build_ScheduledEvent USig OSig (t, 2) (Build_ThreadEvent t (@InvEv USig hu2 FAA))] /\
          inv_blocks (Build_ThreadEvent t (@InvEv USig hu1 FAA)) (Build_ThreadEvent t (@InvEv USig hu2 FAA)) /\
          (forall γ', ~ ghost_emit (F := OSig) (t, 2) (Build_ThreadEvent t (@InvEv USig hu2 FAA)) (ghost_of (tm_queue c2)) γ') /\
          (forall cand q', select_frontier_tagged cand (tm_queue c2) q' -> ts_owner cand = (t, 2) ->
             ~ is_invocation (untag (ts_event cand))).
      Proof.
        intros H1 H2.
        destruct (two_invokes HVE Mc hσ0 t 1 Inc t 2 Inc c1 c2 H1 H2)
          as (tr1 & ret1 & tr2 & ret2 & Hp1 & Hp2 & _ & ->).
        destruct (call_trace (E := USig) t FAA tr1 ret1 Hp1) as (hu1 & rest1 & -> & Hrest1).
        destruct (call_trace (E := USig) t FAA tr2 ret2 Hp2) as (hu2 & rest2 & -> & Hrest2).
        assert (Hblk : inv_blocks (Build_ThreadEvent t (@InvEv USig hu1 FAA)) (Build_ThreadEvent t (@InvEv USig hu2 FAA)))
          by (split; [reflexivity | cbn; intros []]).
        exists hu1, hu2. cbn [tm_queue].
        assert (Hg : ghost_of (schedule_trace_tagged (F := OSig) (t, 1)
                        (Build_TaggedEvent (Build_ThreadEvent t (@InvEv USig hu1 FAA)) (resolved_in empty_store) :: rest1) ++
                      schedule_trace_tagged (F := OSig) (t, 2)
                        (Build_TaggedEvent (Build_ThreadEvent t (@InvEv USig hu2 FAA)) (resolved_in empty_store) :: rest2)) =
                     [@Build_ScheduledEvent USig OSig (t, 1) (Build_ThreadEvent t (@InvEv USig hu1 FAA));
                      @Build_ScheduledEvent USig OSig (t, 2) (Build_ThreadEvent t (@InvEv USig hu2 FAA))]).
        { rewrite ghost_of_app, !ghost_of_schedule. unfold ghost_new. cbn [map inv_events untag te_ev tev_ev].
          rewrite !inv_events_responses by assumption. reflexivity. }
        split; [exact Hg |]. split; [exact Hblk |]. split.
        - intros γ'.
          assert (Hne : forall γ, γ = [@Build_ScheduledEvent USig OSig (t, 1) (Build_ThreadEvent t (@InvEv USig hu1 FAA));
                                       @Build_ScheduledEvent USig OSig (t, 2) (Build_ThreadEvent t (@InvEv USig hu2 FAA))] ->
                          ~ ghost_emit (F := OSig) (t, 2) (Build_ThreadEvent t (@InvEv USig hu2 FAA)) γ γ').
          { intros γ ->. cbn. intros (g1 & g2 & Heq & _ & Hnb).
            destruct g1 as [| x [| y g1]]; cbn in Heq.
            - injection Heq as Hk _. discriminate Hk.
            - injection Heq as <- _. inversion Hnb as [| ? ? Hx _]; subst. exact (Hx Hblk).
            - injection Heq as _ _ Heq. destruct g1; discriminate Heq. }
          exact (Hne _ Hg).
        - intros cand q' Hsel Ho Hinv.
          destruct (select_split _ _ _ Hsel) as (pre & post & Hq & _ & Hall).
          cbn [schedule_trace_tagged map app] in Hq.
          destruct pre as [| x pre]; cbn in Hq; injection Hq as Hx _.
          + rewrite <- Hx in Ho. cbn in Ho. injection Ho. discriminate.
          + subst x. inversion Hall as [| ? ? Hc _]; subst. cbn [ts_event] in Hc.
            assert (Hin : In cand (schedule_trace_tagged (F := OSig) (t, 2)
                          (Build_TaggedEvent (Build_ThreadEvent t (@InvEv USig hu2 FAA)) (resolved_in empty_store) :: rest2))).
            { pose proof (select_frontier_tagged_member _ _ _ Hsel) as Hm. cbn [tm_queue] in Hm.
              apply in_app_or in Hm as [Hm | Hm]; [| exact Hm].
              exfalso. unfold schedule_trace_tagged in Hm. apply in_map_iff in Hm as (m & <- & _). discriminate Ho. }
            unfold schedule_trace_tagged in Hin. apply in_map_iff in Hin as (m & <- & Hm). cbn [ts_event] in Hc, Hinv.
            pose proof (program_produces_tagged_trace_tid _ _ _ _ Hp2) as Ht. rewrite Forall_forall in Ht.
            pose proof (Ht m Hm) as Htm.
            destruct Hc as [Hne | [_ Hnm]]; [apply Hne; cbn; rewrite Htm; reflexivity |].
            apply Hnm. unfold must_precede. cbn. unfold is_invocation in Hinv.
            destruct (te_ev USig (untag m)) as [h' o' | h' o' r']; [| destruct Hinv]. cbn. intros [].
      Qed.
    End S.
  End IncTwo.

  (** ** RLHL-2 acceptance: the overlapping counter, end to end

      [counter_rel_lin]: every complete module execution of the counter
      [Mc] over the handle-linear FAA underlay [HVE] (any number of
      threads and calls, overlapping same-thread calls included) has a
      relaxed-linearizable overlay trace with respect to the sequential
      counter [seq_legal cδ 0].  It is [RelaxedHoareGSim.rlhl_rel_lin]
      for the [RLHL2Hyps] instance [counter_hl_rlhl2], with [HVF]
      discharged by [counter_spec_hvf] (that is, [ei_hvf]); the only
      remaining hypothesis is that the execution is complete.
      [counter_rel_lin_by_rules] is the same statement obtained through
      the paper-facing [RelaxedHoareGSim.rlhl_sound], from the derivation
      [counter_hl_provable].

      Scope (latest-review M-19): this covers the I=∅ fragment; the
      underlay is atomic at invocation ([HVE], not [complete_pres]).
      [USig] and [OSig] have [semi_independent := fun _ _ => False], so
      [rhb] keeps every same-thread edge and no semi-independence
      relaxation is exercised (a one-operation well-formed overlay is
      forced to I=∅); [HVE] linearizes each FAA at its invocation in
      global order; the body has one future, so the own-event premises
      ([ns_if_*]) are discharged by dag precedence, not by a stability
      argument.  What the instance does exercise: two overlapping calls
      of one thread, a cross-call (F3) crossing of a pending response,
      out-of-order returns, and the ghost thread frontier across calls.

      [inc_ooo_exec] is one such execution, derived from module steps:
      thread [t0] invokes [Inc] twice (calls [(t0, 1)] and [(t0, 2)])
      before either returns; the second call's FAA invocation overtakes
      the first call's pending FAA response (allowed by (F3): the
      invocation's tag is empty), the second call returns [1] *before*
      the first returns [0].  [inc_ooo_rel_lin] is the conclusion for its
      overlay trace [Inv(t0,1) Inv(t0,2) Res(t0,2,1) Res(t0,1,0)].

      Limitation (latest-review M-18).  [HVE] fixes each FAA's value at
      its invocation in global invocation order; it is *not* a complete
      presentation of the natural sequential FAA specification
      [seq_legal uδ 0] ([hve_not_complete], the reviewers' script of
      iteration 3, adopted here as a regression).  So
      [ViewLHL.presentation_choice] / [RelaxedHoareGSim.rlhl_rel_lin_pres]
      are not available for this instance: the theorem holds for
      executions over [HVE] itself, not over every underlay implementing
      the FAA specification, and it does not compose vertically. *)

  Module CounterRelLin.
    Import Counter CounterHL.

    Theorem counter_rel_lin evs c :
      module_execution_tagged HVE Mc (initial_tagged_module HVE hσ0) evs c ->
      (forall e, In e (tm_calls c) -> ce_cell OSig e = DeadCall) ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) (RelaxedGSim.overlay_events evs)
        (RelaxedSig.semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof.
      intros Hex Hdone.
      exact (RelaxedHoareGSim.rlhl_rel_lin Ih Rh Gh Mc hσ0 (0, []) (RelaxedHoareSpec.seq_legal cδ 0)
               counter_hl_rlhl2 counter_spec_hvf evs c Hex Hdone).
    Qed.

    (** latest-review m-26: the same conclusion through the paper-facing
        [RelaxedHoareGSim.rlhl_sound], from the derivation
        [counter_hl_provable] (with footprint [Ωc]) and the five side
        conditions, read off the fields of [counter_hl_rlhl2] other than
        [h_sem].  This is an instance of [rlhl_sound]; it is outside the
        [MethodProvableChain] fragment ([Ih] reads the ghost). *)
    Corollary counter_rel_lin_by_rules evs c :
      module_execution_tagged HVE Mc (initial_tagged_module HVE hσ0) evs c ->
      (forall e, In e (tm_calls c) -> ce_cell OSig e = DeadCall) ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) (RelaxedGSim.overlay_events evs)
        (RelaxedSig.semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof.
      intros Hex Hdone.
      destruct counter_hl_rlhl2 as [_ Hgr Hir Hrr Hok Hinit].
      refine (RelaxedHoareGSim.rlhl_sound Ih Rh Gh Mc hσ0 (0, []) (RelaxedHoareSpec.seq_legal cδ 0)
                _ Hgr Hir Hrr Hok Hinit counter_spec_hvf evs c Hex Hdone).
      intros t []. exists (fun _ => Ωc t), (fun h => KLinrh (t, h)). exact (counter_hl_provable t).
    Qed.

    (** *** A concrete complete execution with two overlapping Incs *)

    Definition fi (hu : nat) : TaggedEvent USig :=
      Build_TaggedEvent (Build_ThreadEvent t0 (@InvEv USig hu FAA)) (resolved_in (@empty_store USig)).
    Definition fr (hu r : nat) : TaggedEvent USig :=
      Build_TaggedEvent (Build_ThreadEvent t0 (@ResEv USig hu FAA r)) no_deps.

    Lemma body_produces (hu r : nat) :
      program_produces_tagged t0 (Mc Inc t0) [fi hu; fr hu r] r.
    Proof.
      exists (Build_ProgramConfig (Ret r) [@Build_FutureEntry USig hu (@Resolved USig FAA r)]). split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future USig nat t0 FAA (fun f => Wait f (fun (x : nat) => Ret x)) hu (@empty_store USig)).
          intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending USig nat t0 FAA hu r (fun (x : nat) => Ret x)). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. constructor; [exact Logic.I | constructor].
    Qed.

    Definition inc_ooo_evs : list (ModuleEvent USig OSig) :=
      [OverlayEvent (Build_ThreadEvent t0 (@InvEv OSig 1 Inc));
       OverlayEvent (Build_ThreadEvent t0 (@InvEv OSig 2 Inc));
       UnderlayEvent (Build_ThreadEvent t0 (@InvEv USig 0 FAA));
       UnderlayEvent (Build_ThreadEvent t0 (@InvEv USig 1 FAA));
       UnderlayEvent (Build_ThreadEvent t0 (@ResEv USig 1 FAA 1));
       OverlayEvent (Build_ThreadEvent t0 (@ResEv OSig 2 Inc 1));
       UnderlayEvent (Build_ThreadEvent t0 (@ResEv USig 0 FAA 0));
       OverlayEvent (Build_ThreadEvent t0 (@ResEv OSig 1 Inc 0))].

    Theorem inc_ooo_exec :
      exists c, module_execution_tagged HVE Mc (initial_tagged_module HVE hσ0) inc_ooo_evs c /\
        (forall e, In e (tm_calls c) -> ce_cell OSig e = DeadCall).
    Proof.
      eexists. split.
      - unfold inc_ooo_evs.
        (* the two overlay invocations *)
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke HVE Mc t0 1 Inc hσ0 [] [] [] [fi 0; fr 0 0] 0).
          - intros [].
          - apply body_produces.
          - split; [repeat constructor; intros [] | intros key Hk []]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke HVE Mc t0 2 Inc hσ0 _ _ _ [fi 1; fr 1 1] 1).
          - intros [Heq | []]. discriminate Heq.
          - apply body_produces.
          - split; [repeat constructor; intros [] |].
            intros key [<- | []] [Heq | []]. discriminate Heq. }
        (* the first call's FAA invocation, at the head of the queue *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay HVE Mc (@Build_TaggedScheduledEvent USig OSig (t0, 1) (fi 0))).
          - cbn. apply tagged_select_here.
          - cbn. split; reflexivity. }
        (* the second call's FAA invocation overtakes the first call's
           pending response: (F3) does not apply, the tag is empty *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay HVE Mc (@Build_TaggedScheduledEvent USig OSig (t0, 2) (fi 1))).
          - cbn. apply tagged_select_next; [| apply tagged_select_here].
            right. split; [reflexivity |]. unfold must_precede. cbn. apply resolved_in_empty.
          - cbn. split; reflexivity. }
        (* the second call's FAA response, crossing the first call's *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay HVE Mc (@Build_TaggedScheduledEvent USig OSig (t0, 2) (fr 1 1))).
          - cbn. apply tagged_select_next; [| apply tagged_select_here].
            right. split; [reflexivity |]. unfold must_precede. cbn. intros [].
          - cbn. split; reflexivity. }
        (* the second call returns 1 while the first is still pending *)
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_here.
          - intros [Heq | []]. discriminate Heq. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay HVE Mc (@Build_TaggedScheduledEvent USig OSig (t0, 1) (fr 0 0))).
          - cbn. apply tagged_select_here.
          - cbn. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros Heq; discriminate Heq | apply finish_here].
          - intros []. }
        apply tagged_module_execution_refl.
      - intros e He. cbn in He. destruct He as [<- | [<- | []]]; reflexivity.
    Qed.

    Theorem inc_ooo_rel_lin :
      RelaxedTraceLin.rel_lin (@PrefixView.sel OSig)
        [Build_ThreadEvent t0 (@InvEv OSig 1 Inc); Build_ThreadEvent t0 (@InvEv OSig 2 Inc);
         Build_ThreadEvent t0 (@ResEv OSig 2 Inc 1); Build_ThreadEvent t0 (@ResEv OSig 1 Inc 0)]
        (RelaxedSig.semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof.
      destruct inc_ooo_exec as (c & Hex & Hdone). exact (counter_rel_lin _ _ Hex Hdone).
    Qed.

    (** *** The conclusion discriminates

        The overlay trace in which the younger [Inc] of [t0] returns [0]
        and the older one [1] is not relaxed-linearizable for
        [seq_legal cδ 0] ([inc_bad_not_rel_lin]: [Inc] is not
        semi-independent of itself, so [rhb] orders the older call first,
        and it must then return [0]).  By [counter_rel_lin], no complete
        execution of the counter over [HVE] produces it
        ([inc_bad_no_exec]).  This is an execution-level check
        (latest-review m-23): the same fact follows, by a direct argument
        not mechanized here, from (F2), which orders the two FAA
        invocations of [t0], the atomic [HVE], which then gives the older
        call's FAA [0], and the body, which returns the FAA result; it
        does not test the logic.
        A negative that does test it is [bad_counter_no_rlhl2] below. *)

    Definition oret (o : RelaxedTraceLin.Op OSig) : nat :=
      match RelaxedTraceLin.op_op o as x return Sig.ar x -> nat with Inc => fun r => r end (RelaxedTraceLin.op_ret o).

    Definition res_val (e : ThreadEvent OSig) : option nat :=
      match te_ev OSig e with
      | ResEv _ o r => match o as o0 return Sig.ar o0 -> option nat with Inc => fun r => Some r end r
      | InvEv _ _ => None
      end.

    Definition ev_handle (e : ThreadEvent OSig) : nat :=
      match te_ev OSig e with ResEv h _ _ => h | InvEv h _ => h end.

    Lemma cd_run n W n' :
      RelaxedHoareSpec.seq_run cδ n W n' ->
      forall l1 o l2, W = l1 ++ o :: l2 -> oret o = n + length l1.
    Proof.
      induction 1 as [s | s o0 s1 W s2 Hd Hr IH]; intros l1 o l2 Heq.
      - destruct l1; discriminate Heq.
      - destruct l1 as [| x l1]; cbn in Heq; injection Heq as Hx HW.
        + subst o0. destruct o as [k [] r]. cbn in Hd |- *. destruct Hd as [-> _]. lia.
        + subst x. rewrite (IH l1 o l2 HW). destruct o0 as [k [] r]. cbn in Hd. destruct Hd as [_ ->].
          cbn. lia.
    Qed.

    Definition inc_bad : list (ThreadEvent OSig) :=
      [Build_ThreadEvent t0 (@InvEv OSig 1 Inc); Build_ThreadEvent t0 (@InvEv OSig 2 Inc);
       Build_ThreadEvent t0 (@ResEv OSig 2 Inc 0); Build_ThreadEvent t0 (@ResEv OSig 1 Inc 1)].

    Lemma inc_bad_ret (h : nat) (r : nat) j :
      RelaxedTraceLin.res_at (@PrefixView.sel OSig) inc_bad j (t0, h) Inc r ->
      (h = 2 /\ r = 0) \/ (h = 1 /\ r = 1).
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct j as [|[|[|[|j]]]]; cbn in Hx; try discriminate Hx.
      - pose proof (f_equal (fun o => match o with Some e => res_val e | None => None end) Hx) as Hv.
        cbn in Hv. injection Hv as <-.
        pose proof (f_equal (fun o => match o with Some e => ev_handle e | None => 0 end) Hx) as Hh.
        cbn in Hh. left. split; [exact (eq_sym Hh) | reflexivity].
      - pose proof (f_equal (fun o => match o with Some e => res_val e | None => None end) Hx) as Hv.
        cbn in Hv. injection Hv as <-.
        pose proof (f_equal (fun o => match o with Some e => ev_handle e | None => 0 end) Hx) as Hh.
        cbn in Hh. right. split; [exact (eq_sym Hh) | reflexivity].
      - destruct j; discriminate Hx.
    Qed.

    Theorem inc_bad_not_rel_lin :
      ~ RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) inc_bad
          (RelaxedSig.semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof.
      intros (W & (s & Hrun) & Hnd & Hocc & Hcov & Hord).
      destruct (Hcov 0 (t0, 1) Inc ltac:(eexists; split; reflexivity)) as (o1 & Ho1 & Hk1).
      destruct (Hcov 1 (t0, 2) Inc ltac:(eexists; split; reflexivity)) as (o2 & Ho2 & Hk2).
      assert (Hr1 : oret o1 = 1).
      { destruct (Hocc o1 Ho1) as [_ (j & Hj)]. destruct o1 as [k1 [] r1]. cbn in Hk1, Hj |- *. subst k1.
        destruct (inc_bad_ret 1 r1 j Hj) as [[Hh _] | [_ ->]]; [discriminate Hh | reflexivity]. }
      assert (Hr2 : oret o2 = 0).
      { destruct (Hocc o2 Ho2) as [_ (j & Hj)]. destruct o2 as [k2 [] r2]. cbn in Hk2, Hj |- *. subst k2.
        destruct (inc_bad_ret 2 r2 j Hj) as [[_ ->] | [Hh _]]; [reflexivity | discriminate Hh]. }
      assert (Hb : RelaxedTraceLin.before W o1 o2).
      { apply Hord; [exact Ho1 | exact Ho2 |]. right. rewrite Hk1, Hk2. split; [reflexivity |].
        exists 0, 1. split; [eexists; split; [reflexivity | destruct o1 as [k1 [] r1]; cbn in Hk1 |- *; subst k1; reflexivity] |].
        split; [eexists; split; [reflexivity | destruct o2 as [k2 [] r2]; cbn in Hk2 |- *; subst k2; reflexivity] |].
        split; [auto | intros []]. }
      destruct Hb as (l1 & l2 & HW & Hin). apply in_split in Hin as (m1 & m2 & ->).
      pose proof (cd_run 0 W s Hrun l1 o1 _ HW) as H1.
      pose proof (cd_run 0 W s Hrun (l1 ++ o1 :: m1) o2 m2 ltac:(rewrite HW, <- app_assoc; reflexivity)) as H2.
      rewrite length_app in H2. cbn in H1, H2. lia.
    Qed.

    Corollary inc_bad_no_exec evs c :
      module_execution_tagged HVE Mc (initial_tagged_module HVE hσ0) evs c ->
      (forall e, In e (tm_calls c) -> ce_cell OSig e = DeadCall) ->
      RelaxedGSim.overlay_events evs <> inc_bad.
    Proof.
      intros Hex Hdone Heq. apply inc_bad_not_rel_lin. rewrite <- Heq. exact (counter_rel_lin _ _ Hex Hdone).
    Qed.

    (** *** m-24: a universal negative, through soundness

        The reviewers' script (latest-review m-24, lens 3), adopted
        verbatim up to the qualified names.  [Mbad] is a wrong counter: it
        takes the FAA result [r] and returns [S r].  [bad_exec] is a
        complete execution of [Mbad] over [HVE], derived from module steps,
        whose overlay trace [Inv(t0,1) Res(t0,1,1)] is not
        relaxed-linearizable for [seq_legal cδ 0] ([bad_not_rel_lin]: the
        only operation is first in every witness, so it must return [0]).
        By [RelaxedHoareGSim.rlhl_rel_lin_ei], [bad_counter_no_rlhl2]: *no*
        [I], [R], [G] satisfy [RLHL2Hyps] for [Mbad] over [HVE] with the
        overlay [CVFe] ([EI cδ]) from [(0, [])].  This is universal in the
        assertions and relations (unlike [read_pair_*] below, which are
        relative to one choice [(I2, R2)]); the underlay [HVE], the
        overlay [CVFe] and the initial states are fixed.  By
        [RelaxedHoareGSim.rlhl2_of_provable] it also rules out every
        derivation of [Mbad] that comes with the five side conditions
        (the contrapositive; not stated as a separate lemma). *)

    Definition bad_body : Prog USig nat := @Future USig nat FAA (fun f => Wait f (fun (r : nat) => Ret (S r))).
    Definition Mbad : RelaxedModuleImpl USig OSig := fun op t => match op as o return Prog USig (Sig.ar o) with Inc => bad_body end.

    Lemma bad_produces : program_produces_tagged Counter.t0 (Mbad Inc Counter.t0) [fi 0; fr 0 0] 1.
    Proof.
      exists (Build_ProgramConfig (Ret 1) [@Build_FutureEntry USig 0 (@Resolved USig FAA 0)]). split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future USig nat Counter.t0 FAA (fun f => Wait f (fun (x : nat) => Ret (S x))) 0 (@empty_store USig)).
          intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending USig nat Counter.t0 FAA 0 0 (fun (x : nat) => Ret (S x))). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. constructor; [exact Logic.I | constructor].
    Qed.

    Definition bad_evs : list (ModuleEvent USig OSig) :=
      [OverlayEvent (Build_ThreadEvent Counter.t0 (@InvEv OSig 1 Inc));
       UnderlayEvent (Build_ThreadEvent Counter.t0 (@InvEv USig 0 FAA));
       UnderlayEvent (Build_ThreadEvent Counter.t0 (@ResEv USig 0 FAA 0));
       OverlayEvent (Build_ThreadEvent Counter.t0 (@ResEv OSig 1 Inc 1))].

    Lemma bad_exec : exists c, module_execution_tagged HVE Mbad (initial_tagged_module HVE hσ0) bad_evs c /\
      (forall e, In e (tm_calls c) -> ce_cell OSig e = DeadCall).
    Proof.
      eexists. split.
      - unfold bad_evs.
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke HVE Mbad Counter.t0 1 Inc hσ0 [] [] [] [fi 0; fr 0 0] 1).
          - intros [].
          - apply bad_produces.
          - split; [repeat constructor; intros [] | intros key Hk []]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay HVE Mbad (@Build_TaggedScheduledEvent USig OSig (Counter.t0, 1) (fi 0))).
          - cbn. apply tagged_select_here.
          - cbn. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay HVE Mbad (@Build_TaggedScheduledEvent USig OSig (Counter.t0, 1) (fr 0 0))).
          - cbn. apply tagged_select_here.
          - cbn. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return. - apply finish_here. - intros []. }
        apply tagged_module_execution_refl.
      - intros e He. cbn in He. destruct He as [<- | []]; reflexivity.
    Qed.

    Definition bad_tr : list (ThreadEvent OSig) :=
      [Build_ThreadEvent Counter.t0 (@InvEv OSig 1 Inc); Build_ThreadEvent Counter.t0 (@ResEv OSig 1 Inc 1)].

    Lemma bad_tr_eq : RelaxedGSim.overlay_events bad_evs = bad_tr.
    Proof. reflexivity. Qed.

    Lemma bad_nth i x : nth_error bad_tr i = Some x ->
      x = Build_ThreadEvent Counter.t0 (@InvEv OSig 1 Inc) \/ x = Build_ThreadEvent Counter.t0 (@ResEv OSig 1 Inc 1).
    Proof. destruct i as [|[|[|i]]]; cbn; intros H; try discriminate H; injection H as <-; auto. Qed.

    Lemma bad_not_rel_lin :
      ~ RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) bad_tr (RelaxedSig.semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof.
      intros (W & (s & Hrun) & Hnd & Hocc & Hcov & Hord).
      assert (Hk : forall o, In o W -> RelaxedTraceLin.op_key o = (Counter.t0, 1)).
      { intros o Ho. destruct (Hocc o Ho) as [(i & x & Hx & Hs) _].
        unfold PrefixView.sel in Hs. injection Hs as ->.
        destruct (bad_nth i _ Hx) as [Heq | Heq]; [| discriminate Heq].
        injection Heq as H1 H2 _. destruct (RelaxedTraceLin.op_key o) as [a b]. cbn in H1, H2. subst. reflexivity. }
      destruct (Hcov 0 (Counter.t0, 1) Inc ltac:(eexists; split; reflexivity)) as (o1 & Ho1 & Hk1).
      assert (Hr1 : oret o1 = 1).
      { destruct (Hocc o1 Ho1) as [_ (j & Hj)]. destruct o1 as [k1 [] r1]. cbn in Hk1, Hj |- *. subst k1.
        destruct Hj as (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
        destruct (bad_nth j _ Hx) as [Heq | Heq]; [discriminate Heq |].
        apply (f_equal res_val) in Heq. cbn in Heq. injection Heq as ->. reflexivity. }
      apply in_split in Ho1 as (l1 & l2 & HW).
      pose proof (cd_run 0 W s Hrun l1 o1 l2 HW) as Hlen.
      destruct l1 as [| o0 l1].
      - cbn in Hlen. lia.
      - assert (Hin0 : In o0 W) by (rewrite HW; cbn; left; reflexivity).
        assert (Hin1 : In o1 W) by (rewrite HW; cbn; right; apply in_or_app; right; left; reflexivity).
        rewrite HW in Hnd. cbn in Hnd. apply NoDup_cons_iff in Hnd as [Hn _]. apply Hn.
        rewrite (Hk o0 Hin0), <- (Hk o1 Hin1).
        apply in_map. apply in_or_app. right. left. reflexivity.
    Qed.

    Theorem bad_counter_no_rlhl2 :
      forall (I : Assn HVE CVFe) (R G : CallKey OSig -> PRel HVE CVFe), ~ RLHL2Hyps I R G Mbad hσ0 (0, []).
    Proof.
      intros I R G HH.
      destruct bad_exec as (c & Hex & Hdone).
      apply bad_not_rel_lin. rewrite <- bad_tr_eq.
      exact (RelaxedHoareGSim.rlhl_rel_lin_ei cδ 0 I R G Mbad hσ0 HH bad_evs c Hex Hdone).
    Qed.

    (** *** M-18 regression: [HVE] is not a complete presentation

        The reviewers' script of iteration 3 (latest-review M-18, lens 1),
        adopted verbatim up to names.  [uδ] is the sequential FAA
        ([FAA] returns the counter and increments it); [uu] is the
        complete trace in which thread 2's FAA returns [0] although
        thread 1 invoked first; it is relaxed-linearizable for
        [seq_legal uδ 0] (witness: thread 2's FAA, then thread 1's), but
        [HVE] has no path for it (values are fixed at the invocation, in
        global invocation order). *)

    Definition uδ (n : nat) (o : Sig.op (RelaxedSig.effect USig)) : Sig.ar o -> nat -> Prop :=
      match o as o0 return Sig.ar o0 -> nat -> Prop with FAA => fun r n' => r = n /\ n' = S n end.
    Definition unu := RelaxedHoareSpec.seq_legal uδ 0.
    Definition uu : list (ThreadEvent USig) :=
      [Build_ThreadEvent 1%positive (@InvEv USig 0 FAA); Build_ThreadEvent 2%positive (@InvEv USig 0 FAA);
       Build_ThreadEvent 2%positive (@ResEv USig 0 FAA 0); Build_ThreadEvent 1%positive (@ResEv USig 0 FAA 1)].

    Lemma hve_no_path v : ~ RelaxedGSim.vf_path HVE hσ0 uu v.
    Proof.
      intros Hp. unfold uu in Hp.
      inversion Hp as [|? ? v1 ? ? H1 Hp1]; subst.
      inversion Hp1 as [|? ? v2 ? ? H2 Hp2]; subst.
      inversion Hp2 as [|? ? v3 ? ? H3 Hp3]; subst.
      cbn in H1. destruct H1 as [_ ->]. cbn in H2. destruct H2 as [_ ->]. cbn in H3. destruct H3 as [H3 _].
      discriminate H3.
    Qed.

    Local Ltac idx4 i H := destruct i as [|[|[|[|i]]]]; cbn in H; try (destruct i; discriminate H); injection H as <-.

    Definition ukey2 : CallKey USig := (2%positive, 0).
    Definition ukey1 : CallKey USig := (1%positive, 0).
    Definition uo2 : RelaxedTraceLin.Op USig := @RelaxedTraceLin.Build_Op USig ukey2 FAA 0.
    Definition uo1 : RelaxedTraceLin.Op USig := @RelaxedTraceLin.Build_Op USig ukey1 FAA 1.

    Lemma uu_rl_prefix : ViewLHL.rl_prefix unu uu.
    Proof.
      exists []. rewrite app_nil_r. split; [| split].
      - split; [| split].
        + intros i j k op op' Hi Hj.
          destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
          idx4 i Hx; idx4 j Hy; cbn in Hkx, Hky; congruence.
        + intros i j k op op' r r' Hi Hj.
          destruct (gres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (gres_at _ _ _ _ _ Hj) as (y & Hy & Hky).
          idx4 i Hx; idx4 j Hy; cbn in Hkx, Hky; congruence.
        + intros j k op r Hj. destruct (gres_at _ _ _ _ _ Hj) as (x & Hx & Hkx).
          idx4 j Hx; cbn in Hkx; try discriminate Hkx; inversion Hkx; subst; destruct op.
          * exists 1. split; [lia | eexists; split; reflexivity].
          * exists 0. split; [lia | eexists; split; reflexivity].
      - intros i k op Hi. destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx).
        idx4 i Hx; cbn in Hkx; try discriminate Hkx; inversion Hkx; subst; destruct op.
        + exists 3, 1. eexists; split; reflexivity.
        + exists 2, 0. eexists; split; reflexivity.
      - exists [uo2; uo1]. split; [| split; [| split; [| split]]].
        + exists 2. econstructor; [split; reflexivity |]. econstructor; [split; reflexivity |]. constructor.
        + constructor; [cbn; intros [H | []]; discriminate H | constructor; [intros [] | constructor]].
        + intros o [<- | [<- | []]]; split.
          * exists 1. eexists; split; reflexivity.
          * exists 2. eexists; split; reflexivity.
          * exists 0. eexists; split; reflexivity.
          * exists 3. eexists; split; reflexivity.
        + intros i k op Hi. destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx).
          idx4 i Hx; cbn in Hkx; try discriminate Hkx; inversion Hkx; subst.
          * exists uo1. split; [right; left; reflexivity | reflexivity].
          * exists uo2. split; [left; reflexivity | reflexivity].
        + intros o o' Ho Ho' Hr.
          destruct Ho as [<- | [<- | []]]; destruct Ho' as [<- | [<- | []]].
          * exfalso. destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
            -- destruct (gres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
               idx4 i Hx; idx4 j Hy; cbn in Hkx, Hky; try congruence; lia.
            -- destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
               idx4 i Hx; idx4 j Hy; cbn in Hkx, Hky; try congruence; lia.
          * exists [], [uo1]. split; [reflexivity | left; reflexivity].
          * exfalso. destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
            -- destruct (gres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
               idx4 i Hx; idx4 j Hy; cbn in Hkx, Hky; try congruence; lia.
            -- cbn in Ht. discriminate Ht.
          * exfalso. destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
            -- destruct (gres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
               idx4 i Hx; idx4 j Hy; cbn in Hkx, Hky; try congruence; lia.
            -- destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
               idx4 i Hx; idx4 j Hy; cbn in Hkx, Hky; try congruence; lia.
    Qed.

    Theorem hve_not_complete : ~ ViewLHL.complete_pres unu HVE hσ0.
    Proof. intros Hc. destruct (Hc uu uu_rl_prefix) as (v & Hp). exact (hve_no_path v Hp). Qed.

    (** *** M-18 regression: [VT] accepts a dead-end prefix ([vt_junk])

        Why an effect-at-invocation overlay ([EI], [CVFe]) admits no
        [GSimRel] over the complete underlay presentation [ViewLHL.VT]
        when same-thread operations are ordered (latest-review M-18; the
        author's decision is the stamp-based overlay [VF := ViewLHL.VT
        nuF], research-intent §8).  [junk] is the underlay path
        [Inv(1,0,FAA) Inv(1,1,FAA) Res(1,1,FAA,0)] of one thread: the
        younger FAA returns [0] while the older one is pending.

        - [vt_junk]: [ViewLHL.VT unu] accepts it from [mkV [] H0], for
          every initial stamp map [H0] (the review's instance is
          [H0 := jstamp]): the stamps [jstamp] order [(1,0)] before
          [(1,1)] (as [po_ok] requires, FAA is not semi-independent of
          itself), and every prefix has a stamp-ordered witness, because
          [lin_h] need not contain the pending older call (the full
          trace's witness is [[(1,1) ↦ 0]]).  Closed.
        - [vt_junk_not_rl_prefix]: [junk] is not a prefix of any complete
          relaxed-linearizable trace of [unu] ([rhb] orders [(1,0)] before
          [(1,1)], which must then return at least [1]).  So [VT] has
          paths beyond [rl_prefix]; [complete_pres] allows this.  Closed.
        - [vt_not_implements]: hence [VT unu] does not satisfy
          [ViewLHL.implements unu], from any initial stamp map.  [VT] is
          generic in the signature, so the same path shape should refute
          it for [VT nuF] as an overlay whenever two same-thread
          operations are ordered (argued, mechanized for [unu] only):
          "every [VF] path is an [rl_prefix]" is then not free for [VF :=
          VT nuF] (relevant to the prefix-soundness plan of latest-review
          M-1).  Closed.
        - [counter_vt_no_rlhl2] (latest-review M-18 "Required" 2, the
          optional item): for every initial stamp map [H0] and every [I],
          [R], [G], [RLHL2Hyps I R G Mc (mkV [] H0) (0, [])] fails over
          [VE := VT unu], [VF := CVFe].  Proof: [vt_exec] is a module
          execution of [Mc] over [VT unu] in which two overlapping [Inc]s
          of [t0] emit their FAAs on [(t0,0)] and [(t0,1)], the underlay
          follows [junk], and the younger [Inc] returns [0] while the older
          is pending (an incomplete execution).  [rlhl_gsim] gives a
          [GSimRel]; [RelaxedGSim.rinv_exec] (which holds for incomplete
          executions) gives a [TValid] abstract run whose abstract part is
          a path of [EI cδ]; [TValid] puts the older call's abstract
          invocation first (same thread, [Inc] not semi-independent of
          itself), so in the [EI] witness ([RelaxedHoareSpec.einv_path])
          the younger call's result is at least [1], not [0].  [GSimRel]
          constrains every reachable configuration, including those from
          which no complete execution exists, so the complete-trace
          corollaries do not avoid the obligation.

        This is why [rlhl_rel_lin_ei_pres] is not expected to have an
        instance over [VT] for ordered same-thread operations, and why
        RLHL-3 takes [VF := ViewLHL.VT nuF] instead.  Mechanized for this
        counter only; for other effect-at-invocation specifications over
        [VT] the argument is the same in prose (latest-review M-18). *)

    Definition junk : list (ThreadEvent USig) :=
      [Build_ThreadEvent 1%positive (@InvEv USig 0 FAA); Build_ThreadEvent 1%positive (@InvEv USig 1 FAA);
       Build_ThreadEvent 1%positive (@ResEv USig 1 FAA 0)].

    Definition jstamp (k : CallKey USig) : nat := match snd k with 0 => 0 | _ => 1 end.

    Definition jo1 : RelaxedTraceLin.Op USig := @RelaxedTraceLin.Build_Op USig (1%positive, 1) FAA 0.

    Lemma jnth i x : nth_error junk i = Some x ->
      (i = 0 /\ x = Build_ThreadEvent 1%positive (@InvEv USig 0 FAA)) \/
      (i = 1 /\ x = Build_ThreadEvent 1%positive (@InvEv USig 1 FAA)) \/
      (i = 2 /\ x = Build_ThreadEvent 1%positive (@ResEv USig 1 FAA 0)).
    Proof. destruct i as [|[|[|i]]]; cbn; intros H; try (destruct i; discriminate H); injection H as <-; auto. Qed.

    Definition ures (e : ThreadEvent USig) : option nat :=
      match te_ev USig e with
      | ResEv _ o r => match o as o0 return Sig.ar o0 -> option nat with FAA => fun r => Some r end r
      | InvEv _ _ => None
      end.

    Lemma junk_res j k (r : nat) :
      RelaxedTraceLin.res_at (@PrefixView.sel USig) junk j k FAA r -> j = 2 /\ k = (1%positive, 1) /\ r = 0.
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct (jnth _ _ Hx) as [[-> H] | [[-> H] | [-> H]]];
        try (apply (f_equal ures) in H; discriminate H).
      pose proof (f_equal ures H) as Hr. cbn in Hr. injection Hr as ->.
      pose proof (f_equal (te_tid USig) H) as Ht. pose proof (f_equal (fun e => event_handle (te_ev USig e)) H) as Hh.
      cbn in Ht, Hh. destruct k as [t h]. cbn in Ht, Hh. subst. auto.
    Qed.

    Lemma junk_nores n j k op (r : Sig.ar op) : n <= 2 ->
      ~ RelaxedTraceLin.res_at (@PrefixView.sel USig) (firstn n junk) j k op r.
    Proof.
      intros Hn Hr. destruct (gres_at _ _ _ _ _ Hr) as (x & Hx & Hkx).
      destruct n as [|[|[|n]]]; [| | | lia]; cbn in Hx;
        destruct j as [|[|j]]; cbn in Hx; try (destruct j; discriminate Hx); try discriminate Hx;
        injection Hx as <-; discriminate Hkx.
    Qed.

    Lemma junk_lin_h_nil n : n <= 2 -> PrefixView.lin_h unu jstamp (firstn n junk) [].
    Proof.
      intros Hn. split; [exists 0; constructor |]. split; [constructor |]. split; [intros o [] |].
      split; [intros j k op r Hr; destruct (junk_nores n j k op r Hn Hr) | intros o o' []].
    Qed.

    Lemma junk_lin_h : PrefixView.lin_h unu jstamp junk [jo1].
    Proof.
      split; [exists 1; econstructor; [split; reflexivity | constructor] |].
      split; [constructor; [intros [] | constructor] |].
      split; [| split].
      - intros o [<- | []]. split; [exists 1; eexists; split; reflexivity |].
        intros j r Hr. destruct (junk_res _ _ _ Hr) as (_ & _ & ->). reflexivity.
      - intros j k op r Hr. destruct op. destruct (junk_res _ _ _ Hr) as (_ & -> & ->). left. reflexivity.
      - intros o o' [<- | []] [<- | []] Hlt. lia.
    Qed.

    Lemma junk_view_rt : PrefixView.view_rt (RelaxedSig.semi_independent USig) unu jstamp junk.
    Proof.
      split; [split; [| split] |].
      - split; [| split].
        + intros i j k op op' Hi Hj.
          destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
          destruct (jnth _ _ Hx) as [[-> ->] | [[-> ->] | [-> ->]]];
          destruct (jnth _ _ Hy) as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hkx, Hky; congruence.
        + intros i j k op op' r r' Hi Hj.
          destruct (gres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (gres_at _ _ _ _ _ Hj) as (y & Hy & Hky).
          destruct (jnth _ _ Hx) as [[-> ->] | [[-> ->] | [-> ->]]];
          destruct (jnth _ _ Hy) as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hkx, Hky; congruence.
        + intros j k op r Hj. destruct (gres_at _ _ _ _ _ Hj) as (x & Hx & Hkx).
          destruct (jnth _ _ Hx) as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hkx; try discriminate Hkx.
          inversion Hkx; subst. destruct op. exists 1. split; [lia | eexists; split; reflexivity].
      - intros i j k k' op op' Hi Hj Hij _ _.
        destruct (ginv_at _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
        destruct (jnth _ _ Hx) as [[-> ->] | [[-> ->] | [-> ->]]];
        destruct (jnth _ _ Hy) as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hkx, Hky; try discriminate; try lia.
        injection Hkx; injection Hky; intros; subst; cbn; lia.
      - intros n Hn. destruct n as [|[|[|[|n]]]]; cbn in Hn; try lia.
        + exists []. apply junk_lin_h_nil. lia.
        + exists []. apply junk_lin_h_nil. lia.
        + exists []. apply junk_lin_h_nil. lia.
        + exists [jo1]. exact junk_lin_h.
      - intros i j k k' op op' r Hi Hj Hij.
        destruct (gres_at _ _ _ _ _ Hi) as (x & Hx & Hkx). destruct (ginv_at _ _ _ _ Hj) as (y & Hy & Hky).
        destruct (jnth _ _ Hx) as [[-> ->] | [[-> ->] | [-> ->]]];
        destruct (jnth _ _ Hy) as [[-> ->] | [[-> ->] | [-> ->]]]; cbn in Hkx, Hky; try discriminate; lia.
    Qed.

    Theorem vt_junk H0 : exists v, RelaxedGSim.vf_path (ViewLHL.VT unu) (ViewLHL.mkV [] H0) junk v.
    Proof. eexists. apply ViewLHL.vt_path_of_view; [discriminate | exact junk_view_rt]. Qed.

    Definition uret (o : RelaxedTraceLin.Op USig) : nat :=
      match RelaxedTraceLin.op_op o as x return Sig.ar x -> nat with FAA => fun r => r end (RelaxedTraceLin.op_ret o).

    Lemma ud_run n W n' :
      RelaxedHoareSpec.seq_run uδ n W n' ->
      forall l1 o l2, W = l1 ++ o :: l2 -> uret o = n + length l1.
    Proof.
      induction 1 as [s | s o0 s1 W s2 Hd Hr IH]; intros l1 o l2 Heq.
      - destruct l1; discriminate Heq.
      - destruct l1 as [| x l1]; cbn in Heq; injection Heq as Hx HW.
        + subst o0. destruct o as [k [] r]. cbn in Hd |- *. destruct Hd as [-> _]. lia.
        + subst x. rewrite (IH l1 o l2 HW). destruct o0 as [k [] r]. cbn in Hd. destruct Hd as [_ ->].
          cbn. lia.
    Qed.

    Theorem vt_junk_not_rl_prefix : ~ ViewLHL.rl_prefix unu junk.
    Proof.
      intros (w & (_ & Hwf2 & _) & _ & (W & (s & Hrun) & Hnd & Hocc & Hcov & Hord)).
      destruct (Hcov 0 (1%positive, 0) FAA ltac:(eexists; split; reflexivity)) as (o0 & Ho0 & Hk0).
      destruct (Hcov 1 (1%positive, 1) FAA ltac:(eexists; split; reflexivity)) as (o1 & Ho1 & Hk1).
      assert (Hr1 : uret o1 = 0).
      { destruct (Hocc o1 Ho1) as [_ (j & Hj)]. destruct o1 as [k1 [] r1]. cbn in Hk1, Hj |- *. subst k1.
        assert (H2 : RelaxedTraceLin.res_at (@PrefixView.sel USig) (junk ++ w) 2 (1%positive, 1) FAA 0)
          by (eexists; split; reflexivity).
        pose proof (Hwf2 _ _ _ _ _ _ _ Hj H2) as ->.
        destruct Hj as (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
        apply (f_equal (fun o => match o with Some e => ures e | None => None end)) in Hx. cbn in Hx.
        injection Hx; intros; subst; reflexivity. }
      assert (Hb : RelaxedTraceLin.before W o0 o1).
      { apply Hord; [exact Ho0 | exact Ho1 |]. right. rewrite Hk0, Hk1. split; [reflexivity |].
        exists 0, 1. split; [destruct o0 as [k0 [] r0]; cbn in Hk0 |- *; subst k0; eexists; split; reflexivity |].
        split; [destruct o1 as [k1 [] r1]; cbn in Hk1 |- *; subst k1; eexists; split; reflexivity |].
        split; [auto | intros []]. }
      destruct Hb as (l1 & l2 & HW & Hin). apply in_split in Hin as (m1 & m2 & ->).
      pose proof (ud_run 0 W s Hrun (l1 ++ o0 :: m1) o1 m2 ltac:(rewrite HW, <- app_assoc; reflexivity)) as H2.
      rewrite length_app in H2. cbn in H2. lia.
    Qed.

    Corollary vt_not_implements H0 : ~ ViewLHL.implements unu (ViewLHL.VT unu) (ViewLHL.mkV [] H0).
    Proof. intros Himpl. destruct (vt_junk H0) as (v & Hp). exact (vt_junk_not_rl_prefix (Himpl _ _ Hp)). Qed.

    Definition vt_evs : list (ModuleEvent USig OSig) :=
      [OverlayEvent (Build_ThreadEvent t0 (@InvEv OSig 1 Inc));
       OverlayEvent (Build_ThreadEvent t0 (@InvEv OSig 2 Inc));
       UnderlayEvent (Build_ThreadEvent t0 (@InvEv USig 0 FAA));
       UnderlayEvent (Build_ThreadEvent t0 (@InvEv USig 1 FAA));
       UnderlayEvent (Build_ThreadEvent t0 (@ResEv USig 1 FAA 0));
       OverlayEvent (Build_ThreadEvent t0 (@ResEv OSig 2 Inc 0))].

    (** A module execution of [Mc] over [VT unu], from every initial stamp
        map: the underlay follows [junk] (stamps [jstamp] chosen at the
        first step), and the younger [Inc] returns [0]. *)
    Lemma vt_exec H0 :
      exists c, module_execution_tagged (ViewLHL.VT unu) Mc
                  (initial_tagged_module (ViewLHL.VT unu) (ViewLHL.mkV [] H0)) vt_evs c.
    Proof.
      eexists. unfold vt_evs.
      eapply tagged_module_execution_cons.
      { apply (tagged_invoke (ViewLHL.VT unu) Mc t0 1 Inc (ViewLHL.mkV [] H0) [] [] [] [fi 0; fr 0 1] 1).
        - intros [].
        - apply body_produces.
        - split; [repeat constructor; intros [] | intros key Hk []]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_invoke (ViewLHL.VT unu) Mc t0 2 Inc (ViewLHL.mkV [] H0) _ _ _ [fi 1; fr 1 0] 0).
        - intros [Heq | []]. discriminate Heq.
        - apply body_produces.
        - split; [repeat constructor; intros [] |].
          intros key [<- | []] [Heq | []]. discriminate Heq. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (ViewLHL.VT unu) Mc (@Build_TaggedScheduledEvent USig OSig (t0, 1) (fi 0))).
        - cbn. apply tagged_select_here.
        - cbn. apply (ViewLHL.vt_step_intro unu _ [] H0 jstamp).
          + intros i k m Hi. exfalso. destruct Hi as (x & Hx & _). destruct i; discriminate Hx.
          + exact (ViewLHL.view_rt_firstn unu jstamp junk 1 junk_view_rt). }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (ViewLHL.VT unu) Mc (@Build_TaggedScheduledEvent USig OSig (t0, 2) (fi 1))).
        - cbn. apply tagged_select_next; [| apply tagged_select_here].
          right. split; [reflexivity |]. unfold must_precede. cbn. apply resolved_in_empty.
        - cbn. apply (ViewLHL.vt_step_intro unu _ _ jstamp jstamp).
          + intros i k m Hi. reflexivity.
          + exact (ViewLHL.view_rt_firstn unu jstamp junk 2 junk_view_rt). }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (ViewLHL.VT unu) Mc (@Build_TaggedScheduledEvent USig OSig (t0, 2) (fr 1 0))).
        - cbn. apply tagged_select_next; [| apply tagged_select_here].
          right. split; [reflexivity |]. unfold must_precede. cbn. intros [].
        - cbn. apply (ViewLHL.vt_step_intro unu _ _ jstamp jstamp).
          + intros i k m Hi. reflexivity.
          + exact junk_view_rt. }
      eapply tagged_module_execution_cons.
      { apply tagged_return.
        - apply finish_here.
        - intros [Heq | []]. discriminate Heq. }
      apply tagged_module_execution_refl.
    Qed.

    Theorem counter_vt_no_rlhl2 H0 :
      forall (I : Assn (ViewLHL.VT unu) CVFe) (R G : CallKey OSig -> PRel (ViewLHL.VT unu) CVFe),
        ~ RLHL2Hyps I R G Mc (ViewLHL.mkV [] H0) (0, []).
    Proof.
      intros I R G HH.
      destruct (RelaxedHoareGSim.rlhl_gsim I R G Mc (ViewLHL.mkV [] H0) (0, []) HH) as (S & HS & HS0).
      destruct (vt_exec H0) as (c & Hex).
      destruct (RelaxedGSim.rinv_exec (ViewLHL.VT unu) CVFe Mc ((0, []) : State CVFe) S _ _ _ HS Hex
                  [] ((0, []) : State CVFe) [] HS0 (RelaxedGSim.RInv_init CVFe _))
        as (run & v & pool & _ & HI & Hc).
      cbn [app] in HI.
      assert (Hconc : ViewPossibility.conc run =
        [Build_ThreadEvent t0 (@InvEv OSig 1 Inc); Build_ThreadEvent t0 (@InvEv OSig 2 Inc);
         Build_ThreadEvent t0 (@ResEv OSig 2 Inc 0)]) by (rewrite Hc; reflexivity).
      pose proof (RelaxedGSim.ri_lwf _ _ _ _ _ _ HI) as Hcwf.
      pose proof (RelaxedGSim.ri_valid _ _ _ _ _ _ HI) as HV.
      (* the abstract response of (t0, 2), with result 0 *)
      destruct (RelaxedGSim.ri_dead _ _ _ _ _ _ HI 2 (t0, 2) Inc 0) as (_ & b & Hb).
      { rewrite Hconc. eexists. split; reflexivity. }
      destruct (RelaxedGSim.ri_ares _ _ _ _ _ _ HI _ _ _ _ Hb) as (a2 & _ & Ha2).
      (* its abstract invocation comes after that of (t0, 1) ([TValid]) *)
      destruct (ViewPossibility.abs_inv_step _ _ _ _ Ha2) as (q1 & q2 & Hrun).
      pose proof (RelaxedGSim.abs_inv_index q1 q2 (t0, 2) Inc) as Hai. rewrite <- Hrun in Hai.
      pose proof (RelaxedGSim.ri_auinv _ _ _ _ _ _ HI _ _ _ _ _ Ha2 Hai) as ->.
      destruct (HV q1 _ q2 Hrun) as ((i0 & Hi0) & Hpo).
      assert (Hi0' : RelaxedTraceLin.inv_at (@PrefixView.sel OSig) (ViewPossibility.conc run) i0 (t0, 2) Inc)
        by (rewrite Hrun, ViewPossibility.conc_app; exact (ViewPossibility.inv_app_l _ _ _ _ _ Hi0)).
      assert (Hi01 : i0 = 1).
      { apply (proj1 Hcwf i0 1 (t0, 2) Inc Inc Hi0'). rewrite Hconc. eexists. split; reflexivity. }
      subst i0.
      assert (Hq1 : RelaxedTraceLin.inv_at (@PrefixView.sel OSig) (ViewPossibility.conc q1) 0 (t0, 1) Inc).
      { apply (ViewPossibility.inv_app_lt _ (ViewPossibility.conc (@ViewPossibility.AInv OSig (t0, 2) Inc :: q2))).
        - pose proof (ViewPossibility.inv_lt _ _ _ _ Hi0). lia.
        - rewrite <- ViewPossibility.conc_app, <- Hrun, Hconc. eexists. split; reflexivity. }
      destruct (Hpo 1 0 (t0, 1) Inc Hi0 Hq1 ltac:(lia) eq_refl (fun H => H)) as (a1 & Ha1).
      assert (Ha1' : RelaxedTraceLin.inv_at (@PrefixView.sel OSig) (ViewPossibility.abs run) a1 (t0, 1) Inc)
        by (rewrite Hrun, ViewPossibility.abs_app; exact (ViewPossibility.inv_app_l _ _ _ _ _ Ha1)).
      pose proof (ViewPossibility.inv_lt _ _ _ _ Ha1) as Ha12.
      (* the abstract trace is a path of [EI cδ]; its witness orders (t0, 1) first *)
      assert (Hawf : PrefixView.wf (ViewPossibility.abs run)).
      { split; [exact (RelaxedGSim.ri_auinv _ _ _ _ _ _ HI) |
               split; [exact (RelaxedGSim.ri_aures _ _ _ _ _ _ HI) | exact (RelaxedGSim.ri_ares _ _ _ _ _ _ HI)]]. }
      destruct (RelaxedHoareSpec.einv_path cδ (RelaxedSig.semi_independent OSig) 0 _ _
                  (RelaxedGSim.ri_path _ _ _ _ _ _ HI) Hawf) as (W & HE).
      pose proof (RelaxedHoareSpec.ei_res _ _ _ _ _ _ _ HE _ _ _ _ Hb) as Ho2.
      destruct (RelaxedHoareSpec.ei_cov _ _ _ _ _ _ _ HE _ _ _ Ha1') as (o1 & Ho1 & Hk1).
      set (o2 := @RelaxedTraceLin.Build_Op OSig (t0, 2) Inc 0) in Ho2.
      assert (Hb12 : RelaxedTraceLin.before W o1 o2).
      { apply (RelaxedHoareSpec.ei_ord _ _ _ _ _ _ _ HE); [exact Ho1 | exact Ho2 |].
        right. rewrite Hk1. split; [reflexivity |].
        exists a1, (length (ViewPossibility.abs q1)).
        split; [destruct o1 as [k1 [] r1]; cbn in Hk1 |- *; subst k1; exact Ha1' |].
        split; [exact Hai |]. split; [exact Ha12 |]. intros []. }
      destruct Hb12 as (l1 & l2 & HW & Hin). apply in_split in Hin as (m1 & m2 & ->).
      pose proof (cd_run 0 W _ (RelaxedHoareSpec.ei_run _ _ _ _ _ _ _ HE) (l1 ++ o1 :: m1) o2 m2
                    ltac:(rewrite HW, <- app_assoc; reflexivity)) as H2.
      rewrite length_app in H2. cbn in H2. lia.
    Qed.
  End CounterRelLin.

  (** ** RLHL-3a: copy-cat soundness for the counter, for every execution

      The counter instance of [RelaxedHoareCompLin.rlhl_complin_ei]
      (research-intent §8, M-20: CompLin-style soundness over the
      sequential specification's effect-at-invocation LTS [CVFe]).

      - [counter_complin]: every overlay trace of [Mc] over [HVE] from
        [hσ0], complete or not, is an overlay trace of the relaxed copy-cat
        [RelaxedHoareCompLin.idF] over [CVFe] from [(0, [])].
      - [ooo_counter_trace], [ooo_copycat_trace]: the overlay trace of
        [inc_ooo_exec] (two overlapping [Inc]s of [t0], the younger
        returns [1] first, the older [0] afterwards) is a counter trace,
        hence a copy-cat trace.
      - [junkF_not_rtrace]: the incomplete trace [junkF] =
        [Inv(t0,1) Inv(t0,2) Res(t0,2,0)] (the younger [Inc] returns [0]
        while the older is pending; the overlay analogue of [junk]) is not
        a copy-cat trace over [CVFe].  Proof: an invariant of every
        copy-cat execution over [CVFe] ([JInv]); a pending record of value
        [0] belongs to the first emitted underlay increment, whose call has
        no older call of its thread, because (F2) emits the increment of an
        older same-thread call first ([Inc] is not semi-independent of
        itself).  This agrees with the REW reading of prefixes
        (relaxedlin.tex:29), which rejects [junkF]; the [V] reading
        (viewbased.tex:35) accepts its underlay analogue ([vt_junk];
        latest-review M-20).  It is one data point, not a proof that
        copy-cat traces coincide with REW prefixes.  Closed.
      - [junkF_not_counter_trace]: hence no execution of [Mc] over [HVE],
        complete or not, has the overlay trace [junkF].  As for
        [inc_bad_no_exec], a direct argument from (F2) and the atomic
        [HVE] gives the same fact (not mechanized); here it is derived from
        the RLHL hypotheses through [counter_complin].

      Scope: the I=∅ fragment and the underlay [HVE] of [CounterRelLin]
      (latest-review M-19); [JInv] is specific to [CVFe]. *)

  Module CounterCompLin.
    Import Counter CounterHL CounterRelLin.
    Import RelaxedHoareCompLin.

    (** The counter instance of [RelaxedHoareCompLin.rlhl_complin_ei]. *)
    Theorem counter_complin : RCompLin Mc HVE hσ0 CVFe (0, []).
    Proof. exact (rlhl_complin_ei cδ 0 Ih Rh Gh Mc hσ0 counter_hl_rlhl2). Qed.

    Definition ooo_trace : list (ThreadEvent OSig) :=
      [Build_ThreadEvent t0 (@InvEv OSig 1 Inc); Build_ThreadEvent t0 (@InvEv OSig 2 Inc);
       Build_ThreadEvent t0 (@ResEv OSig 2 Inc 1); Build_ThreadEvent t0 (@ResEv OSig 1 Inc 0)].

    Theorem ooo_counter_trace : MTraces HVE Mc hσ0 ooo_trace.
    Proof. destruct inc_ooo_exec as (c & Hex & _). exists inc_ooo_evs, c. split; [exact Hex | reflexivity]. Qed.

    Theorem ooo_copycat_trace : RTraces CVFe (0, []) ooo_trace.
    Proof. exact (counter_complin _ ooo_counter_trace). Qed.

    Definition junkF : list (ThreadEvent OSig) :=
      [Build_ThreadEvent t0 (@InvEv OSig 1 Inc); Build_ThreadEvent t0 (@InvEv OSig 2 Inc);
       Build_ThreadEvent t0 (@ResEv OSig 2 Inc 0)].

    (** *** Copy-cat configurations over [CVFe] *)

    Abbreviation CCfg := (@TaggedModuleConfig OSig OSig CVFe).
    Abbreviation TSE := (TaggedScheduledEvent OSig OSig).

    Definition gient (k : CallKey OSig) (u : nat) : TSE :=
      Build_TaggedScheduledEvent k (@cc_inv_ev OSig (fst k) u Inc).
    Definition grent (k : CallKey OSig) (u r : nat) : TSE :=
      Build_TaggedScheduledEvent k (@cc_res_ev OSig (fst k) u Inc r).
    Definition ukey (x : TSE) : CallKey OSig :=
      (te_tid OSig (untag (ts_event x)), event_handle (te_ev OSig (untag (ts_event x)))).

    Lemma gient_ne_grent k u k' u' r : gient k u <> grent k' u' r.
    Proof. intros H. apply (f_equal (fun x => te_ev OSig (untag (ts_event x)))) in H. discriminate H. Qed.

    Lemma gient_inj k u k' u' : gient k u = gient k' u' -> k = k' /\ u = u'.
    Proof.
      intros H. split; [exact (f_equal ts_owner H) |].
      apply (f_equal (fun x => snd (ukey x))) in H. exact H.
    Qed.

    Lemma grent_inj k u r k' u' r' : grent k u r = grent k' u' r' -> k = k' /\ u = u'.
    Proof.
      intros H. split; [exact (f_equal ts_owner H) |].
      apply (f_equal (fun x => snd (ukey x))) in H. exact H.
    Qed.

    Definition cell_val (c : CallCell OSig) : nat :=
      match c with
      | ActiveCall o r => match o as o0 return Sig.ar o0 -> nat with Inc => fun r => r end r
      | DeadCall => 0
      end.

    (** [older keys a b]: in the call pool's key list (newest first), [b]
        is newer than [a], i.e. [a] was invoked before [b]. *)
    Definition older (keys : list (CallKey OSig)) (a b : CallKey OSig) : Prop :=
      exists i j, i < j /\ nth_error keys i = Some b /\ nth_error keys j = Some a.

    Definition NoOlder (keys : list (CallKey OSig)) (b : CallKey OSig) : Prop :=
      forall a, older keys a b -> fst a <> fst b.

    Lemma older_cons z keys a b : older keys a b -> older (z :: keys) a b.
    Proof. intros (i & j & Hij & Hi & Hj). exists (S i), (S j). split; [lia | auto]. Qed.

    Lemma older_cons_inv z keys a b : older (z :: keys) a b -> b <> z -> older keys a b.
    Proof.
      intros (i & j & Hij & Hi & Hj) Hne. destruct i as [| i]; [cbn in Hi; injection Hi as ->; congruence |].
      destruct j as [| j]; [lia |]. exists i, j. split; [lia | auto].
    Qed.

    Lemma older_new z keys a : In a keys -> older (z :: keys) a z.
    Proof. intros Ha. apply In_nth_error in Ha as (j & Hj). exists 0, (S j). split; [lia | auto]. Qed.

    Lemma nodup_pos (keys : list (CallKey OSig)) i j x :
      NoDup keys -> nth_error keys i = Some x -> nth_error keys j = Some x -> i = j.
    Proof.
      intros Hnd Hi Hj. rewrite NoDup_nth_error in Hnd. apply Hnd; [apply nth_error_Some; congruence | congruence].
    Qed.

    Lemma older_asym keys a b : NoDup keys -> older keys a b -> older keys b a -> False.
    Proof.
      intros Hnd (i & j & Hij & Hi & Hj) (i' & j' & Hij' & Hi' & Hj').
      pose proof (nodup_pos _ _ _ _ Hnd Hi Hj'). pose proof (nodup_pos _ _ _ _ Hnd Hj Hi'). lia.
    Qed.

    Lemma older_neq keys a b : NoDup keys -> older keys a b -> a <> b.
    Proof. intros Hnd (i & j & Hij & Hi & Hj) ->. pose proof (nodup_pos _ _ _ _ Hnd Hi Hj). lia. Qed.

    Lemma older_in keys a b : older keys a b -> In a keys /\ In b keys.
    Proof. intros (i & j & _ & Hi & Hj). split; eapply nth_error_In; eauto. Qed.

    Lemma noolder_cons z keys b : NoOlder keys b -> b <> z -> NoOlder (z :: keys) b.
    Proof. intros H Hne a Ha. exact (H a (older_cons_inv _ _ _ _ Ha Hne)). Qed.

    Lemma pairwise_remove (P : TSE -> TSE -> Prop) (Q pre post : list TSE) x0 :
      Q = pre ++ x0 :: post ->
      (forall p q y x, nth_error Q p = Some y -> nth_error Q q = Some x -> p < q -> P y x) ->
      forall p q y x, nth_error (pre ++ post) p = Some y -> nth_error (pre ++ post) q = Some x -> p < q -> P y x.
    Proof.
      intros HQ Hord p q y x Hp Hq Hpq.
      destruct (nth_remove pre post x0 p y Hp) as (p' & Hp' & Hp1 & Hp2).
      destruct (nth_remove pre post x0 q x Hq) as (q' & Hq' & Hq1 & Hq2).
      rewrite <- HQ in Hp', Hq'. apply (Hord p' q' y x Hp' Hq').
      destruct (Nat.lt_ge_cases p (length pre)); destruct (Nat.lt_ge_cases q (length pre)).
      - rewrite Hp1, Hq1 by assumption. exact Hpq.
      - rewrite Hp1, Hq2 by assumption. lia.
      - lia.
      - rewrite Hp2, Hq2 by assumption. lia.
    Qed.

    Lemma remove_pos (pre post : list TSE) x0 y :
      In y (pre ++ post) -> exists p', nth_error (pre ++ x0 :: post) p' = Some y /\ p' <> length pre.
    Proof.
      intros Hy. apply In_nth_error in Hy as (p & Hp).
      destruct (nth_remove pre post x0 p y Hp) as (p' & Hp' & H1 & H2). exists p'. split; [exact Hp' |].
      destruct (Nat.lt_ge_cases p (length pre)) as [Hl | Hg]; [rewrite (H1 Hl); lia | rewrite (H2 Hg); lia].
    Qed.

    Lemma invocation_keys_app (l l' : list (ThreadEvent OSig)) :
      invocation_keys (l ++ l') = invocation_keys l ++ invocation_keys l'.
    Proof. induction l as [| e l IH]; [reflexivity |]. cbn. destruct (te_ev OSig e); cbn; rewrite IH; reflexivity. Qed.

    Lemma owner_key (x : TSE) (r : nat) (pool : CallPool OSig) :
      In (Build_CallEntry (fst (ts_owner x)) (snd (ts_owner x)) (@ActiveCall OSig Inc r)) pool ->
      In (ts_owner x) (map call_key pool).
    Proof.
      intros Hin. rewrite (surjective_pairing (ts_owner x)).
      change (fst (ts_owner x), snd (ts_owner x))
        with (call_key (Build_CallEntry (fst (ts_owner x)) (snd (ts_owner x)) (@ActiveCall OSig Inc r))).
      apply in_map. exact Hin.
    Qed.

    (** Two queue entries, [y] before [x]: the invocation and the response
        entry of one call (same underlay handle), or entries of two calls,
        [y]'s invoked first. *)
    Definition ORel (keys : list (CallKey OSig)) (y x : TSE) : Prop :=
      (ts_owner y = ts_owner x /\ exists u r, y = gient (ts_owner x) u /\ x = grent (ts_owner x) u r) \/
      (ts_owner y <> ts_owner x /\ older keys (ts_owner y) (ts_owner x)).

    (** The invariant of every copy-cat execution over [CVFe] (state
        [(n, P)]: the counter and the pending records).  [j_*]: the queue
        of the copy-cat (shape, order by invocation and (F1), unique
        underlay keys); [n_*]: the counter.  A pending record with value
        [0] was created by the first emitted invocation, whose call has no
        older call of its thread ([n_rec0]); [n_hist] carries this to the
        overlay returns of value [0]. *)
    Record JInv (evs : list (ModuleEvent OSig OSig)) (c : CCfg) : Prop := {
      j_shape : forall x, In x (tm_queue c) -> exists u (r : nat),
        In (Build_CallEntry (fst (ts_owner x)) (snd (ts_owner x)) (@ActiveCall OSig Inc r)) (tm_calls c) /\
        (x = gient (ts_owner x) u \/ x = grent (ts_owner x) u r) /\
        In (fst (ts_owner x), u) (tm_used_underlay c);
      j_ord : forall p q y x, nth_error (tm_queue c) p = Some y -> nth_error (tm_queue c) q = Some x -> p < q ->
        ORel (map call_key (tm_calls c)) y x;
      j_ukey : forall x y, In x (tm_queue c) -> In y (tm_queue c) -> ukey x = ukey y -> ts_owner x = ts_owner y;
      j_cwf : NoDup (map call_key (tm_calls c));
      j_pair : forall k u, In (gient k u) (tm_queue c) -> exists r, In (grent k u r) (tm_queue c);
      n_zero : fst (tm_lts_state c) = 0 -> snd (tm_lts_state c) = [] /\
        forall e, In e (tm_calls c) -> exists u, In (gient (call_key e) u) (tm_queue c);
      n_rec0 : forall o, In o (snd (tm_lts_state c)) -> oret o = 0 ->
        exists x u r, In x (tm_queue c) /\ x = grent (ts_owner x) u r /\
          (fst (ts_owner x), u) = RelaxedTraceLin.op_key o /\ NoOlder (map call_key (tm_calls c)) (ts_owner x);
      n_done : forall t h, In (Build_CallEntry t h (@ActiveCall OSig Inc 0)) (tm_calls c) ->
        owner_done_tagged (t, h) (tm_queue c) -> NoOlder (map call_key (tm_calls c)) (t, h);
      n_hist : forall t h, In (Build_ThreadEvent t (@ResEv OSig h Inc 0)) (RelaxedGSim.overlay_events evs) ->
        In (t, h) (map call_key (tm_calls c)) /\ NoOlder (map call_key (tm_calls c)) (t, h);
      n_keys : map call_key (tm_calls c) = rev (invocation_keys (RelaxedGSim.overlay_events evs));
      n_pnd : NoDup (map RelaxedTraceLin.op_key (snd (tm_lts_state c)));
      n_prec : forall o x, In o (snd (tm_lts_state c)) -> In x (tm_queue c) -> ukey x = RelaxedTraceLin.op_key o ->
        exists u r, x = grent (ts_owner x) u r;
      n_pused : forall o, In o (snd (tm_lts_state c)) -> In (RelaxedTraceLin.op_key o) (tm_used_underlay c);
    }.

    Lemma jinv_init : JInv [] (initial_tagged_module CVFe (0, [])).
    Proof.
      constructor; cbn.
      - intros x [].
      - intros p q y x Hp. destruct p; discriminate Hp.
      - intros x y [].
      - constructor.
      - intros k u [].
      - intros _. split; [reflexivity | intros e []].
      - intros o [].
      - intros t h [].
      - intros t h [].
      - reflexivity.
      - constructor.
      - intros o x [].
      - intros o [].
    Qed.

    Lemma overlay_inv_ne t h (op : Sig.op (RelaxedSig.effect OSig)) t' h' (r : nat) :
      Build_ThreadEvent t (@InvEv OSig h op) <> Build_ThreadEvent t' (@ResEv OSig h' Inc r).
    Proof. intros H. apply (f_equal (te_ev OSig)) in H. discriminate H. Qed.

    (** *** Preservation: an overlay invocation *)

    Lemma jinv_invoke evs t h op q pool queue used trace ret :
      JInv evs (@Build_TaggedModuleConfig OSig OSig CVFe q pool queue used) ->
      call_fresh (t, h) pool ->
      program_produces_tagged t (@idF OSig op t) trace ret ->
      trace_fresh used (map untag trace) ->
      JInv (evs ++ [OverlayEvent (Build_ThreadEvent t (@InvEv OSig h op))])
        (@Build_TaggedModuleConfig OSig OSig CVFe q (Build_CallEntry t h (ActiveCall op ret) :: pool)
           (queue ++ schedule_trace_tagged (t, h) trace) (used ++ invocation_keys (map untag trace))).
    Proof.
      intros HJ Hcf Hprod Hft.
      destruct (cc_trace t op trace ret Hprod) as (u & ->).
      destruct op.
      destruct Hft as [_ Hfu].
      assert (Hu : ~ In (t, u) used) by (apply Hfu; left; reflexivity).
      destruct HJ as [Hshape Hord Hukey Hcwf Hpair Hzero Hrec0 Hdone Hhist Hkeys Hpnd Hprec Hpused];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      change (schedule_trace_tagged (t, h) [cc_inv_ev t u Inc; cc_res_ev t u Inc ret])
        with [gient (t, h) u; grent (t, h) u ret].
      change (invocation_keys (map untag [@cc_inv_ev OSig t u Inc; @cc_res_ev OSig t u Inc ret])) with [(t, u)].
      assert (Hov : RelaxedGSim.overlay_events (evs ++ [OverlayEvent (Build_ThreadEvent t (@InvEv OSig h Inc))]) =
                    RelaxedGSim.overlay_events evs ++ [Build_ThreadEvent t (@InvEv OSig h Inc)])
        by (rewrite overlay_events_app; reflexivity).
      assert (Hown : forall x, In x queue -> In (ts_owner x) (map call_key pool)).
      { intros x Hx. destruct (Hshape x Hx) as (u' & r' & Hin & _). exact (owner_key x r' pool Hin). }
      assert (Hnk : forall k, In k (map call_key pool) -> k <> (t, h)).
      { intros k Hk ->. exact (Hcf Hk). }
      assert (Hne : forall x, In x queue -> ts_owner x <> (t, h)) by (intros x Hx; exact (Hnk _ (Hown x Hx))).
      assert (Hukold : forall x, In x queue -> ukey x <> (t, u)).
      { intros x Hx Heq. destruct (Hshape x Hx) as (u' & r' & _ & Hform & Hused').
        assert (Hux : ukey x = (fst (ts_owner x), u')) by (destruct Hform as [Hx' | Hx']; rewrite Hx'; reflexivity).
        rewrite Hux in Heq. rewrite Heq in Hused'. exact (Hu Hused'). }
      assert (HK : map call_key (Build_CallEntry t h (@ActiveCall OSig Inc ret) :: pool) = (t, h) :: map call_key pool)
        by reflexivity.
      constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay]; rewrite ?HK, ?Hov.
      - intros x Hx. apply in_app_or in Hx as [Hx | Hx].
        + destruct (Hshape x Hx) as (u' & r' & Hin & Hform & Hused'). exists u', r'.
          split; [right; exact Hin |]. split; [exact Hform | apply in_or_app; left; exact Hused'].
        + destruct Hx as [<- | [<- | []]]; exists u, ret; (split; [left; reflexivity |]);
            (split; [| apply in_or_app; right; left; reflexivity]); [left | right]; reflexivity.
      - intros p q1 y x Hp Hq Hpq.
        destruct (nth_app_cases queue _ p y Hp) as [(Hp1 & Hp2) | (Hp1 & Hp2)];
          destruct (nth_app_cases queue _ q1 x Hq) as [(Hq1 & Hq2) | (Hq1 & Hq2)].
        + destruct (Hord p q1 y x Hp2 Hq2 Hpq) as [Hl | (Hn & Ho)]; [left; exact Hl |].
          right. split; [exact Hn | apply older_cons; exact Ho].
        + pose proof (nth_error_In _ _ Hp2) as Hy. right.
          destruct (nth_two _ _ _ _ Hq2) as [(_ & ->) | (_ & ->)]; cbn [ts_owner gient grent];
            (split; [exact (Hne y Hy) | apply older_new; exact (Hown y Hy)]).
        + lia.
        + left. destruct (nth_two _ _ _ _ Hp2) as [(E1 & ->) | (E1 & ->)];
            destruct (nth_two _ _ _ _ Hq2) as [(E2 & ->) | (E2 & ->)]; try lia.
          split; [reflexivity |]. exists u, ret. split; reflexivity.
      - intros x y Hx Hy Heq. apply in_app_or in Hx as [Hx | Hx]; apply in_app_or in Hy as [Hy | Hy].
        + exact (Hukey x y Hx Hy Heq).
        + exfalso. apply (Hukold x Hx). rewrite Heq. destruct Hy as [<- | [<- | []]]; reflexivity.
        + exfalso. apply (Hukold y Hy). rewrite <- Heq. destruct Hx as [<- | [<- | []]]; reflexivity.
        + destruct Hx as [<- | [<- | []]]; destruct Hy as [<- | [<- | []]]; reflexivity.
      - constructor; [exact Hcf | exact Hcwf].
      - intros k u' Hin. apply in_app_or in Hin as [Hin | Hin].
        + destruct (Hpair k u' Hin) as (r' & Hr'). exists r'. apply in_or_app. left. exact Hr'.
        + destruct Hin as [Heq | [Heq | []]].
          * apply gient_inj in Heq as [<- <-]. exists ret. apply in_or_app. right. right. left. reflexivity.
          * exfalso. exact (gient_ne_grent _ _ _ _ _ (eq_sym Heq)).
      - intros Hn. destruct (Hzero Hn) as [HP Hall]. split; [exact HP |].
        intros e [<- | He].
        + exists u. apply in_or_app. right. left. reflexivity.
        + destruct (Hall e He) as (u' & Hu'). exists u'. apply in_or_app. left. exact Hu'.
      - intros o Ho H0. destruct (Hrec0 o Ho H0) as (x & u' & r' & Hx & Hxf & Hk & Hno).
        exists x, u', r'. split; [apply in_or_app; left; exact Hx |]. split; [exact Hxf |]. split; [exact Hk |].
        exact (noolder_cons _ _ _ Hno (Hne x Hx)).
      - intros t' h' Hin Hd. destruct Hin as [Heq | Hin].
        + exfalso. assert (Htk : (t, h) = (t', h')) by exact (f_equal call_key Heq). rewrite <- Htk in Hd.
          apply Hd. apply in_map_iff. exists (gient (t, h) u). split; [reflexivity |].
          apply in_or_app. right. left. reflexivity.
        + assert (Hk : In (t', h') (map call_key pool)).
          { change (t', h') with (call_key (Build_CallEntry t' h' (@ActiveCall OSig Inc 0))). apply in_map. exact Hin. }
          apply noolder_cons; [| exact (Hnk _ Hk)]. apply (Hdone t' h' Hin).
          intros Hin'. apply Hd. rewrite map_app. apply in_or_app. left. exact Hin'.
      - intros t' h' Hin. apply in_app_or in Hin as [Hin | [Heq | []]].
        + destruct (Hhist t' h' Hin) as (Hk & Hno). split; [right; exact Hk |].
          exact (noolder_cons _ _ _ Hno (Hnk _ Hk)).
        + exfalso. exact (overlay_inv_ne _ _ _ _ _ _ Heq).
      - rewrite Hkeys, invocation_keys_app, rev_app_distr. reflexivity.
      - exact Hpnd.
      - intros o x Ho Hx Heq. apply in_app_or in Hx as [Hx | Hx]; [exact (Hprec o x Ho Hx Heq) |].
        exfalso. pose proof (Hpused o Ho) as Hin. rewrite <- Heq in Hin.
        destruct Hx as [<- | [<- | []]]; exact (Hu Hin).
      - intros o Ho. apply in_or_app. left. exact (Hpused o Ho).
    Qed.

    (** *** Preservation: an underlay emission *)

    Lemma tse_eq_dec_key (a b : CallKey OSig) : a = b \/ a <> b.
    Proof.
      destruct a as [t h], b as [t' h']. destruct (Pos.eq_dec t t') as [-> | Ht]; [| right; congruence].
      destruct (Nat.eq_dec h h') as [-> | Hh]; [left; reflexivity | right; congruence].
    Qed.

    Lemma jinv_underlay evs cand q q' pool queue queue' used :
      JInv evs (@Build_TaggedModuleConfig OSig OSig CVFe q pool queue used) ->
      select_frontier_tagged cand queue queue' ->
      Step CVFe (untag (ts_event cand)) q q' ->
      JInv (evs ++ [UnderlayEvent (untag (ts_event cand))]) (@Build_TaggedModuleConfig OSig OSig CVFe q' pool queue' used).
    Proof.
      intros HJ Hsel Hlts.
      destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & HQ & -> & Hcross).
      rewrite Forall_forall in Hcross.
      destruct HJ as [Hshape Hord Hukey Hcwf Hpair Hzero Hrec0 Hdone Hhist Hkeys Hpnd Hprec Hpused];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      assert (Hov : RelaxedGSim.overlay_events (evs ++ [@UnderlayEvent OSig OSig (untag (ts_event cand))]) =
                    RelaxedGSim.overlay_events evs) by (rewrite overlay_events_app, app_nil_r; reflexivity).
      assert (Hcand : In cand queue) by (rewrite HQ; apply in_or_app; right; left; reflexivity).
      assert (Hp : nth_error queue (length pre) = Some cand)
        by (rewrite HQ, nth_error_app2, Nat.sub_diag by lia; reflexivity).
      assert (Hsub : forall y, In y (pre ++ post) -> In y queue) by (intros y Hy; rewrite HQ; exact (in_remove_in _ _ _ _ Hy)).
      assert (Hpre : forall y p', nth_error queue p' = Some y -> p' < length pre -> In y pre).
      { intros y p' Hy Hlt. rewrite HQ, nth_error_app1 in Hy by exact Hlt. exact (nth_error_In _ _ Hy). }
      destruct (Hshape cand Hcand) as (u & r & HinC & Hform & Hused0).
      remember (ts_owner cand) as k eqn:Hk.
      destruct q as [n P].
      destruct Hform as [Hc | Hc]; subst cand; cbn [ts_owner gient grent] in *.
      - (* the emission of an invocation: a new record [(fst k, u) ↦ n] *)
        cbn in Hlts. destruct Hlts as (r' & st' & (-> & ->) & ->). cbn [fst snd] in *.
        (* any other remaining entry of [k] is its response entry *)
        assert (Hrest : forall y, In y (pre ++ post) -> ts_owner y = k -> exists u0 r0, y = grent k u0 r0).
        { intros y Hy Hyk. destruct (remove_pos pre post (gient k u) y Hy) as (p' & Hp' & Hne). rewrite <- HQ in Hp'.
          destruct (Nat.lt_ge_cases p' (length pre)) as [Hlt | Hge].
          - destruct (Hord p' (length pre) y _ Hp' Hp Hlt) as [(_ & u0 & r0 & _ & Heq) | (Hn & _)].
            + exfalso. exact (gient_ne_grent _ _ _ _ _ Heq).
            + exfalso. exact (Hn Hyk).
          - destruct (Hord (length pre) p' _ y Hp Hp' ltac:(lia)) as [(_ & u0 & r0 & _ & Heq) | (Hn & _)].
            + exists u0, r0. rewrite Hyk in Heq. exact Heq.
            + exfalso. exact (Hn (eq_sym Hyk)). }
        assert (Hgr : exists r0, In (grent k u r0) (pre ++ post)).
        { destruct (Hpair k u Hcand) as (r0 & Hr0). exists r0. rewrite HQ in Hr0.
          apply (in_remove_ne _ _ _ _ Hr0). intros Heq. exact (gient_ne_grent _ _ _ _ _ (eq_sym Heq)). }
        assert (Hfreshk : ~ In (fst k, u) (map RelaxedTraceLin.op_key P)).
        { intros Hin. apply in_map_iff in Hin as (o & Hok & Ho).
          destruct (Hprec o (gient k u) Ho Hcand (eq_sym Hok)) as (u0 & r0 & Heq).
          exact (gient_ne_grent _ _ _ _ _ Heq). }
        assert (Hfirst : n = 0 -> NoOlder (map call_key pool) k).
        { intros Hn0 a Ha Hth. destruct (Hzero Hn0) as [_ Hall].
          pose proof (older_neq _ _ _ Hcwf Ha) as Hak.
          destruct (older_in _ _ _ Ha) as (Hain & _). apply in_map_iff in Hain as (e & Hea & He).
          destruct (Hall e He) as (u' & Hu'). rewrite Hea in Hu'.
          apply In_nth_error in Hu' as (p' & Hp').
          destruct (Nat.lt_total p' (length pre)) as [Hlt | [Heq | Hgt]].
          - pose proof (Hcross _ (Hpre _ _ Hp' Hlt)) as Hc.
            unfold tagged_can_cross, must_precede in Hc. cbn in Hc.
            destruct Hc as [Hc | (_ & Hc)]; [exact (Hc Hth) | exact (Hc (fun x => x))].
          - subst p'. rewrite Hp in Hp'. apply some_inj in Hp'. apply gient_inj in Hp' as [Hp' _]. exact (Hak (eq_sym Hp')).
          - destruct (Hord (length pre) p' _ _ Hp Hp' Hgt) as [(Heq & _) | (_ & Ho)].
            + exact (Hak (eq_sym Heq)).
            + exact (older_asym _ _ _ Hcwf Ha Ho). }
        assert (Hnotk : forall t' h', owner_done_tagged (t', h') (pre ++ post) -> (t', h') <> k ->
                          owner_done_tagged (t', h') queue).
        { intros t' h' Hd Hne Hin. apply in_map_iff in Hin as (x & Hxo & Hx). rewrite HQ in Hx.
          apply in_app_or in Hx as [Hx | [<- | Hx]].
          - apply Hd. apply in_map_iff. exists x. split; [exact Hxo | apply in_or_app; left; exact Hx].
          - exact (Hne (eq_sym Hxo)).
          - apply Hd. apply in_map_iff. exists x. split; [exact Hxo | apply in_or_app; right; exact Hx]. }
        constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay fst snd]; rewrite ?Hov.
        + intros x Hx. exact (Hshape x (Hsub x Hx)).
        + exact (pairwise_remove (ORel (map call_key pool)) queue pre post _ HQ Hord).
        + intros x y Hx Hy. exact (Hukey x y (Hsub x Hx) (Hsub y Hy)).
        + exact Hcwf.
        + intros k' u' Hin. destruct (Hpair k' u' (Hsub _ Hin)) as (r0 & Hr0). exists r0. rewrite HQ in Hr0.
          apply (in_remove_ne _ _ _ _ Hr0). intros Heq. exact (gient_ne_grent _ _ _ _ _ (eq_sym Heq)).
        + intros Hn. discriminate Hn.
        + intros o [<- | Ho] H0.
          * cbn in H0. subst n. destruct Hgr as (r0 & Hr0). exists (grent k u r0), u, r0.
            split; [exact Hr0 |]. split; [reflexivity |]. split; [reflexivity |]. exact (Hfirst eq_refl).
          * destruct (Hrec0 o Ho H0) as (x & u' & r' & Hx & Hxf & Hko & Hno). exists x, u', r'.
            split; [| auto]. rewrite HQ in Hx. apply (in_remove_ne _ _ _ _ Hx).
            intros Heq. rewrite Heq in Hxf. exact (gient_ne_grent _ _ _ _ _ Hxf).
        + intros t' h' Hin Hd. destruct (tse_eq_dec_key (t', h') k) as [Heq | Hne].
          * exfalso. destruct Hgr as (r0 & Hr0). apply Hd. rewrite Heq. apply in_map_iff.
            exists (grent k u r0). split; [reflexivity | exact Hr0].
          * exact (Hdone t' h' Hin (Hnotk t' h' Hd Hne)).
        + exact Hhist.
        + exact Hkeys.
        + constructor; [exact Hfreshk | exact Hpnd].
        + intros o x [<- | Ho] Hx Heq.
          * assert (Hxk : ts_owner x = k) by exact (Hukey x (gient k u) (Hsub x Hx) Hcand Heq).
            destruct (Hrest x Hx Hxk) as (u0 & r0 & Hx'). exists u0, r0. rewrite Hxk. exact Hx'.
          * exact (Hprec o x Ho (Hsub x Hx) Heq).
        + intros o [<- | Ho]; [exact Hused0 | exact (Hpused o Ho)].
      - (* the emission of a response: the record [(fst k, u) ↦ r] is consumed *)
        cbn in Hlts. destruct Hlts as (P1 & P2 & HP & ->). cbn [fst snd] in *. subst P.
        (* no other entry of [k] remains *)
        assert (Hnone : forall y, In y (pre ++ post) -> ts_owner y <> k).
        { intros y Hy Hyk. destruct (remove_pos pre post (grent k u r) y Hy) as (p' & Hp' & Hne). rewrite <- HQ in Hp'.
          destruct (Nat.lt_ge_cases p' (length pre)) as [Hlt | Hge].
          - destruct (Hord p' (length pre) y _ Hp' Hp Hlt) as [(_ & u0 & r0 & Hy' & Heq) | (Hn & _)];
              [| exact (Hn Hyk)].
            apply grent_inj in Heq as [_ <-].
            pose proof (Hcross _ (Hpre _ _ Hp' Hlt)) as Hc. rewrite Hy' in Hc.
            unfold tagged_can_cross, must_precede in Hc. cbn in Hc.
            destruct Hc as [Hc | (_ & Hc)]; [exact (Hc eq_refl) | exact (Hc eq_refl)].
          - destruct (Hord (length pre) p' _ y Hp Hp' ltac:(lia)) as [(_ & u0 & r0 & Heq & _) | (Hn & _)].
            + exact (gient_ne_grent _ _ _ _ _ (eq_sym Heq)).
            + exact (Hn (eq_sym Hyk)). }
        assert (Hzero_r : r = 0 -> NoOlder (map call_key pool) k).
        { intros Hr0. assert (Ho : In (@RelaxedTraceLin.Build_Op OSig (fst k, u) Inc r) (P1 ++ @RelaxedTraceLin.Build_Op OSig (fst k, u) Inc r :: P2))
            by (apply in_or_app; right; left; reflexivity).
          destruct (Hrec0 _ Ho Hr0) as (x & u' & r' & Hx & Hxf & Hko & Hno).
          assert (Hux : ukey x = (fst k, u)) by (rewrite Hxf; exact Hko).
          rewrite (Hukey x (grent k u r) Hx Hcand Hux) in Hno. exact Hno. }
        assert (Hnotk : forall t' h', owner_done_tagged (t', h') (pre ++ post) -> (t', h') <> k ->
                          owner_done_tagged (t', h') queue).
        { intros t' h' Hd Hne Hin. apply in_map_iff in Hin as (x & Hxo & Hx). rewrite HQ in Hx.
          apply in_app_or in Hx as [Hx | [<- | Hx]].
          - apply Hd. apply in_map_iff. exists x. split; [exact Hxo | apply in_or_app; left; exact Hx].
          - exact (Hne (eq_sym Hxo)).
          - apply Hd. apply in_map_iff. exists x. split; [exact Hxo | apply in_or_app; right; exact Hx]. }
        rewrite map_app in Hpnd. cbn [map] in Hpnd.
        constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay fst snd]; rewrite ?Hov.
        + intros x Hx. exact (Hshape x (Hsub x Hx)).
        + exact (pairwise_remove (ORel (map call_key pool)) queue pre post _ HQ Hord).
        + intros x y Hx Hy. exact (Hukey x y (Hsub x Hx) (Hsub y Hy)).
        + exact Hcwf.
        + intros k' u' Hin. destruct (Hpair k' u' (Hsub _ Hin)) as (r0 & Hr0). exists r0. rewrite HQ in Hr0.
          apply (in_remove_ne _ _ _ _ Hr0). intros Heq. apply grent_inj in Heq as [-> _].
          exact (Hnone _ Hin eq_refl).
        + intros Hn. destruct (Hzero Hn) as [HP _]. exfalso. destruct P1; discriminate HP.
        + intros o Ho H0. assert (Ho' : In o (P1 ++ @RelaxedTraceLin.Build_Op OSig (fst k, u) Inc r :: P2))
            by (exact (in_remove_in _ _ _ _ Ho)).
          destruct (Hrec0 o Ho' H0) as (x & u' & r' & Hx & Hxf & Hko & Hno). exists x, u', r'.
          split; [| auto]. rewrite HQ in Hx. apply (in_remove_ne _ _ _ _ Hx).
          intros Heq. apply (NoDup_remove_2 _ _ _ Hpnd). rewrite <- map_app. apply in_map_iff.
          exists o. split; [| exact Ho].
          pose proof Hxf as Hxf'. rewrite Heq in Hxf'. apply grent_inj in Hxf' as [_ Hu1].
          rewrite <- Hko, Heq. cbn. rewrite Hu1. reflexivity.
        + intros t' h' Hin Hd. destruct (tse_eq_dec_key (t', h') k) as [Heq | Hne].
          * assert (Hr0 : r = 0).
            { assert (Hkk : call_key (Build_CallEntry t' h' (@ActiveCall OSig Inc 0)) =
                            call_key (Build_CallEntry (fst k) (snd k) (@ActiveCall OSig Inc r)))
                by (change ((t', h') = (fst k, snd k)); rewrite Heq; apply surjective_pairing).
              pose proof (ViewPossibility.NoDup_key_eq call_key _ _ _ Hcwf Hin HinC Hkk) as Hce.
              exact (eq_sym (f_equal (fun e => cell_val (ce_cell OSig e)) Hce)). }
            rewrite Heq. exact (Hzero_r Hr0).
          * exact (Hdone t' h' Hin (Hnotk t' h' Hd Hne)).
        + exact Hhist.
        + exact Hkeys.
        + rewrite map_app. exact (NoDup_remove_1 _ _ _ Hpnd).
        + intros o x Ho Hx Heq. exact (Hprec o x (in_remove_in _ _ _ _ Ho) (Hsub x Hx) Heq).
        + intros o Ho. exact (Hpused o (in_remove_in _ _ _ _ Ho)).
    Qed.

    (** *** Preservation: an overlay return *)

    Lemma jinv_return evs t h op ret q pool pool' queue used :
      JInv evs (@Build_TaggedModuleConfig OSig OSig CVFe q pool queue used) ->
      finish_call t h op ret pool pool' -> owner_done_tagged (t, h) queue ->
      JInv (evs ++ [OverlayEvent (Build_ThreadEvent t (@ResEv OSig h op ret))])
        (@Build_TaggedModuleConfig OSig OSig CVFe q pool' queue used).
    Proof.
      intros HJ Hfin Hd. destruct op.
      destruct HJ as [Hshape Hord Hukey Hcwf Hpair Hzero Hrec0 Hdone Hhist Hkeys Hpnd Hprec Hpused];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      assert (Hkeq : map call_key pool' = map call_key pool) by exact (eq_sym (finish_call_keys _ _ _ _ _ _ Hfin)).
      pose proof (RelaxedGSim.finish_src _ _ _ _ _ _ Hfin) as HinA.
      assert (Hov : RelaxedGSim.overlay_events (evs ++ [OverlayEvent (Build_ThreadEvent t (@ResEv OSig h Inc ret))]) =
                    RelaxedGSim.overlay_events evs ++ [Build_ThreadEvent t (@ResEv OSig h Inc ret)])
        by (rewrite overlay_events_app; reflexivity).
      assert (Hnq : forall x, In x queue -> ts_owner x <> (t, h)).
      { intros x Hx Heq. apply Hd. rewrite <- Heq. apply in_map. exact Hx. }
      constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay]; rewrite ?Hkeq, ?Hov.
      - intros x Hx. destruct (Hshape x Hx) as (u & r & Hin & Hform & Hu). exists u, r.
        split; [| auto]. apply (finish_keep _ _ _ _ _ _ _ Hfin Hin).
        intros Hk. apply (Hnq x Hx). rewrite (surjective_pairing (ts_owner x)). exact Hk.
      - exact Hord.
      - exact Hukey.
      - rewrite <- Hkeq. exact (finish_call_well_formed _ _ _ _ _ _ Hfin Hcwf).
      - exact Hpair.
      - intros Hn. exfalso. destruct (Hzero Hn) as [_ Hall]. destruct (Hall _ HinA) as (u & Hu).
        exact (Hnq _ Hu eq_refl).
      - exact Hrec0.
      - intros t' h' Hin Hd'. destruct (RelaxedGSim.finish_back _ _ _ _ _ _ _ Hfin Hin) as [Hin' | Heq].
        + exact (Hdone t' h' Hin' Hd').
        + apply (f_equal (ce_cell OSig)) in Heq. discriminate Heq.
      - intros t' h' Hin. apply in_app_or in Hin as [Hin | [Heq | []]]; [exact (Hhist t' h' Hin) |].
        pose proof (f_equal (te_tid OSig) Heq) as Ht. pose proof (f_equal (fun e => event_handle (te_ev OSig e)) Heq) as Hh.
        pose proof (f_equal res_val Heq) as Hv. cbn in Ht, Hh, Hv. injection Hv as Hv. subst t' h' ret.
        split; [change (t, h) with (call_key (Build_CallEntry t h (@ActiveCall OSig Inc 0))); apply in_map; exact HinA |].
        exact (Hdone t h HinA Hd).
      - rewrite Hkeys, invocation_keys_app, app_nil_r. reflexivity.
      - exact Hpnd.
      - exact Hprec.
      - exact Hpused.
    Qed.

    Lemma jinv_step evs c ev c' : JInv evs c -> module_step_tagged CVFe idF ev c c' -> JInv (evs ++ [ev]) c'.
    Proof.
      intros HJ Hst. revert HJ.
      destruct Hst as [t h op q pool queue used trace ret Hcf Hm Hft | cand q q' pool queue queue' used Hsel Hlts
                      | t h op ret q pool pool' queue used Hfin Hd]; intros HJ.
      - exact (jinv_invoke evs t h op q pool queue used trace ret HJ Hcf Hm Hft).
      - exact (jinv_underlay evs cand q q' pool queue queue' used HJ Hsel Hlts).
      - exact (jinv_return evs t h op ret q pool pool' queue used HJ Hfin Hd).
    Qed.

    Lemma jinv_exec c1 evs c2 :
      module_execution_tagged CVFe idF c1 evs c2 -> forall pre, JInv pre c1 -> JInv (pre ++ evs) c2.
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros pre HJ.
      - rewrite app_nil_r. exact HJ.
      - replace (pre ++ ev :: evs) with ((pre ++ [ev]) ++ evs) by (rewrite <- app_assoc; reflexivity).
        apply IH. exact (jinv_step _ _ _ _ HJ Hst).
    Qed.

    (** The copy-cat over the sequential counter rejects [junkF]: in every
        copy-cat execution, an overlay call that returns [0] has no older
        call of its thread (it owns the first emitted underlay increment,
        and (F2) emits the increment of an older call of the same thread
        first), while in [junkF] the call [(t0, 2)] returns [0] although
        [(t0, 1)] is older. *)
    Theorem junkF_not_rtrace : ~ RTraces CVFe (0, []) junkF.
    Proof.
      intros (evs & c & Hex & Hov).
      pose proof (jinv_exec _ _ _ Hex [] jinv_init) as HJ. cbn [app] in HJ.
      pose proof (n_keys _ _ HJ) as Hk. rewrite Hov in Hk. cbn in Hk.
      destruct (n_hist _ _ HJ t0 2) as (_ & Hno); [rewrite Hov; right; right; left; reflexivity |].
      apply (Hno (t0, 1)); [| reflexivity].
      exists 0, 1. rewrite Hk. split; [lia | split; reflexivity].
    Qed.

    (** Hence, through [counter_complin], no execution of the counter over
        [HVE] (complete or not) has the overlay trace [junkF]. *)
    Corollary junkF_not_counter_trace : ~ MTraces HVE Mc hσ0 junkF.
    Proof. intros H. exact (junkF_not_rtrace (counter_complin _ H)). Qed.
  End CounterCompLin.

  (** ** RLHL-3a iteration 2: regressions T1 and T2 of the RLHL-3a review

      [CounterEI] (latest-review m-20, the review's scratch session T1,
      adopted verbatim up to names; it belongs with
      [CounterHL.counter_ow_unsat], but needs [CounterRelLin.uδ]): the
      effect-at-invocation LTS of the sequential FAA, [EI uδ], is not
      handle-linear ([EVE_not_handle_linear]: it keeps one record per
      invocation and never disables a re-invocation), and over it
      [RLHL2Hyps] has no model for the overlapping counter
      ([counter_ei_unsat], for every [I], [R], [G], initial state and
      initial counter value).  The reason is that of [counter_ow_unsat]:
      the triple quantifies over schedules in which two calls of one
      thread invoke the same underlay key, which the module excludes
      ([trace_fresh]); [EI] keeps both records, so the response of the
      first call may consume the record of the second.  Over the
      handle-linear presentation the counter is provable
      ([CounterHL.counter_hl_rlhl2] over [HVE]), which isolates
      handle-linearity as the cause.  Hence the layering interface is
      [RelaxedHoareCompLinSpec.EIhl], connected to [EI] by
      [RelaxedHoareCompLinSpec.hlift] / [rlhl_complin_eihl].  Closed. *)

  Module CounterEI.
    Import Counter CounterHL.

    Definition EVE : LTS USig := RelaxedHoareSpec.EI CounterRelLin.uδ.

    Theorem EVE_not_handle_linear used : ~ HandleLinear EVE used.
    Proof.
      intros Hhl.
      assert (H1 : Step EVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) (0, []) (1, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0])).
      { cbn. exists 0, 1. split; [split; reflexivity | reflexivity]. }
      assert (H2 : Step EVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) (1, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0])
                     (2, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 1; @RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0])).
      { cbn. exists 1, 2. split; [split; reflexivity | reflexivity]. }
      exact (hl_fresh _ _ Hhl t0 0 FAA _ _ H2 (hl_inv_used _ _ Hhl t0 0 FAA _ _ H1)).
    Qed.

    Theorem counter_ei_unsat (I : Assn EVE CVFe) (R G : CallKey OSig -> PRel EVE CVFe) (q0 : State EVE) (m0 : nat) :
      ~ RLHL2Hyps I R G Mc q0 (m0, []).
    Proof.
      intros HH. destruct q0 as [n0 l0].
      pose proof (h_sem _ _ _ _ _ _ HH) as Hsem.
      set (q1 := (S n0, @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0) : State EVE).
      assert (Hfirst : forall r : nat, exists A0 m2 p1,
        CallTriple I R G key0 Inc r A0 /\ untag m2 = Build_ThreadEvent t0 (@ResEv USig 0 FAA r) /\
        A0 [m2] (q1, p1, []) /\ I (q1, p1, []) /\ Good m0 p1 /\
        exists v pool, p1 = @PossOk OSig CVFe v pool /\ lin_domain pool = [key0]).
      { intros r. destruct (inc_trace_gen t0 0 r) as (tr & Hprod & Htr).
        destruct (Hsem t0 Inc 0 tr r Hprod) as (A0 & Htri & Hinit0).
        set (p0 := @PossOk OSig CVFe (m0, []) [make_lin_entry key0 (@ls_inv OSig Inc)]).
        assert (Hpi : poss_invoke CVFe t0 0 Inc (@PossOk OSig CVFe (m0, []) []) p0) by (constructor; constructor; intros []).
        destruct (Hinit0 (n0, l0) _ [] p0 (h_init _ _ _ _ _ _ HH) Hpi) as [HI0 HA0].
        destruct tr as [| m1 [| m2 [| m3 tr]]]; try discriminate. cbn in Htr. injection Htr as H1 H2.
        unfold ghost_new in HI0, HA0. cbn [app map] in HI0, HA0. rewrite H1, H2 in HI0, HA0.
        cbn [inv_events te_ev map] in HI0, HA0.
        pose proof Htri as [Hemit _ _].
        destruct (Hemit [] m1 [m2] ltac:(constructor) (n0, l0) p0 _ []
                    ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA0 HI0 q1
                    ltac:(rewrite H1; cbn; exists n0, (S n0); split; [split; reflexivity | reflexivity]))
          as (p1 & Hps & HA1 & HI1 & _).
        exists A0, m2, p1. split; [exact Htri |]. split; [exact H2 |]. split; [exact HA1 |]. split; [exact HI1 |].
        split.
        - eapply good_steps; [exact Hps |]. exists m0, [], [], (@ls_inv OSig Inc).
          split; [reflexivity |]. split; [left; reflexivity |]. split; [reflexivity |].
          split; [intros o [] | exact Logic.I].
        - destruct (h_ok _ _ _ _ _ _ HH _ HI1) as (v & pool & Hp1 & _). cbn in Hp1. subst p1.
          exists v, pool. split; [reflexivity |].
          rewrite <- (poss_steps_ok_domain CVFe _ _ _ _ Hps). reflexivity. }
      assert (HA : n0 = m0).
      { destruct (Hfirst n0) as (A0 & m2 & p1 & [Hemit _ Hret] & Hm2 & HA1 & HI1 & HG1 & _).
        destruct (Hemit [] m2 [] ltac:(constructor) q1 p1 [] [] ltac:(rewrite Hm2; reflexivity) HA1 HI1 (S n0, l0)
                    ltac:(rewrite Hm2; cbn; exists [], l0; split; reflexivity))
          as (p2 & Hps2 & HA2 & HI2 & _).
        destruct (Hret _ HA2 HI2 ltac:(intros e [])) as (p3 & Hps3 & (v & pool & -> & Hl) & _).
        exact (good_linr m0 v pool n0 (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps2 Hps3) HG1) Hl). }
      assert (HB : S n0 = m0).
      { destruct (Hfirst (S n0)) as (A0 & m2 & p1 & [Hemit0 Hstab0 Hret0] & Hm2 & HA1 & HI1 & HG1 & v & pool & -> & Hdom).
        destruct (inc_trace_gen t0 0 0) as (tr1 & Hprod1 & Htr1).
        destruct (Hsem t0 Inc 1 tr1 0 Hprod1) as (A1 & [Hemit1 _ _] & Hinit1).
        set (p1' := @PossOk OSig CVFe v (make_lin_entry key1 (@ls_inv OSig Inc) :: pool)).
        assert (Hpi : poss_invoke CVFe t0 1 Inc (@PossOk OSig CVFe v pool) p1').
        { constructor. constructor. unfold lin_fresh. rewrite Hdom. intros [H | []]. discriminate H. }
        destruct (Hinit1 q1 _ [] p1' HI1 Hpi) as [HI1' HA1'].
        pose proof (h_invoke_rely _ _ _ _ _ _ HH key1 key0 Inc tr1 0 (q1, @PossOk OSig CVFe v pool, []) p1'
                      ltac:(discriminate) Hprod1 HI1 Hpi) as HR.
        pose proof (Hstab0 [m2] _ _ HA1 HR HI1') as HA0'. cbn [ps_mem ps_ghost snd fst] in HA0'.
        destruct tr1 as [| n1 [| n2 [| n3 tr1]]]; try discriminate. cbn in Htr1. injection Htr1 as H1 H2.
        cbn [ps_mem ps_ghost snd fst] in HA0', HI1', HA1'.
        unfold ghost_new in HI1', HA1', HA0'. cbn [app map] in HI1', HA1', HA0'. rewrite H1, H2 in HI1', HA1', HA0'.
        cbn [inv_events te_ev map] in HI1', HA1', HA0'.
        set (q2 := (S (S n0), @RelaxedTraceLin.Build_Op USig (t0, 0) FAA (S n0) :: @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0) : State EVE).
        destruct (Hemit1 [] n1 [n2] ltac:(constructor) q1 p1' _ []
                    ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA1' HI1' q2
                    ltac:(rewrite H1; cbn; exists (S n0), (S (S n0)); split; [split; reflexivity | reflexivity]))
          as (p2 & Hps2 & _ & HI2 & HG2).
        pose proof (h_guar_rely _ _ _ _ _ _ HH key1 key0 _ _ ltac:(discriminate) HG2) as HR2.
        pose proof (Hstab0 [m2] _ _ HA0' HR2 HI2) as HA2.
        destruct (Hemit0 [] m2 [] ltac:(constructor) q2 p2 [] [] ltac:(rewrite Hm2; reflexivity) HA2 HI2
                    (S (S n0), @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0)
                    ltac:(rewrite Hm2; cbn; exists [], (@RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0); split; reflexivity))
          as (p3 & Hps3 & HA3 & HI3 & _).
        destruct (Hret0 _ HA3 HI3 ltac:(intros e [])) as (p4 & Hps4 & (v4 & pool4 & -> & Hl) & _).
        assert (HG2' : Good m0 p2) by exact (good_steps _ _ _ Hps2 (good_invoke1 _ _ _ HG1 Hpi)).
        exact (good_linr m0 v4 pool4 (S n0) (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps3 Hps4) HG2') Hl). }
      lia.
    Qed.
  End CounterEI.

  (** [CounterEIhl] (latest-review m-20, the decided layering interface
      has an instance): the overlapping counter verified by RLHL over the
      handle-linear sequential-specification LTS
      [VE := RelaxedHoareCompLinSpec.EIhl uδ] (state [((n, P), used)]: the
      counter, the pending FAA records, the invoked keys), with the same
      overlay [CVFe] and module [Mc] as [CounterHL].

      - [counter_eihl_rlhl2]: every field of [RLHL2Hyps] holds, by the
        rules ([counter_eihl_provable], a [MethodProvable] derivation; the
        derivation itself is [CounterHL]'s, copied with the new
        assertions).
      - [counter_complin_eihl]: hence copy-cat inclusion over [EIhl uδ]
        ([RelaxedHoareCompLin.rlhl_complin_ei]), and
        [counter_complin_ei]: over the plain [EI uδ]
        ([RelaxedHoareCompLinSpec.rlhl_complin_eihl], through [hlift]),
        although over [EI uδ] itself no [RLHL2Hyps] instance exists
        ([CounterEI.counter_ei_unsat]).
      - [counter_eihl_rel_lin]: every complete overlay trace of the
        counter over [EI uδ] is relaxed-linearizable to [seq_legal cδ 0]
        ([RelaxedHoareCompLinSpec.complin_ei_rel_lin]).

      What changes against [CounterHL]: [EI] removes a record at the
      response, so "records only grow" is not available.  The rely of [k]
      instead keeps every concrete record whose value is the value of one
      of [k]'s abstract records ([Re], last clause), and the guarantee of
      [k] keeps every concrete record whose value belongs to an abstract
      record of another call ([Ge]).  This uses that the counter's values
      are unique (the abstract values are distinct, [Ie]).  That is a
      choice of this proof, not a need of [EIhl]: a
      specification-independent alternative exists,
      [CounterEIhlFrame] below, whose rely and guarantee constrain memory
      only by "any [EIhl uδ] steps" and whose assertions use the frame
      lemmas [RelaxedHoareCompLinSpec.eihl_mine_*] (latest-review m-34).
      This module is kept unchanged.  Handle-linearity enters at the FAA:
      its key is unused, so the concrete records keep distinct keys
      ([Ie]), and the response of [k] consumes [k]'s record.

      Scope: as [CounterHL] (I=∅ at both levels, a single-future body; the
      module is the FAA-to-[Inc] copy-cat). *)

  Module CounterEIhl.
    Import Counter CounterHL RelaxedHoareCompLin RelaxedHoareCompLinSpec.

    Definition EHL : LTS USig := @EIhl USig nat CounterRelLin.uδ.
    Abbreviation EA := (Assn EHL CVFe).

    Definition ehσ0 : State EHL := ((0, []), []).

    Definition uval (x : RelaxedTraceLin.Op USig) : nat :=
      match RelaxedTraceLin.op_op x as o return u_ar o -> nat with FAA => fun r => r end (RelaxedTraceLin.op_ret x).
    Definition oval (o : COp) : nat :=
      match RelaxedTraceLin.op_op o as x return o_ar x -> nat with Inc => fun r => r end (RelaxedTraceLin.op_ret o).

    (** The concrete counter, the pending FAA records, the invoked keys. *)
    Definition ecnt (σ : State EHL) : nat := fst (fst σ).
    Definition erec (σ : State EHL) : list (RelaxedTraceLin.Op USig) := snd (fst σ).
    Definition eused (σ : State EHL) : list (CallKey USig) := snd σ.

    (** The invariant: [CounterHL.Ih] (with the counter of [EHL]), plus:
        the concrete records have distinct keys, all invoked; the abstract
        records have distinct values, all below the counter. *)
    Definition Ie : EA := fun s => exists ca P pool,
      ps_poss s = EOk (ca, P) pool /\ ecnt (ps_mem s) = ca /\ lin_pool_well_formed pool /\
      (forall t', inv_keys t' pool = gkeys t' (ps_ghost s)) /\ Forall Jwf (ps_ghost s) /\
      (forall o, In o P -> lin_lookup (okey o) (@ls_lini OSig Inc) pool) /\
      NoDup (map okey P) /\
      (forall x, In x (erec (ps_mem s)) -> In (RelaxedTraceLin.op_key x) (eused (ps_mem s))) /\
      NoDup (map (@RelaxedTraceLin.op_key USig) (erec (ps_mem s))) /\
      (forall o, In o P -> oval o < ca) /\ NoDup (map oval P).

    (** Rely of [k]: [k]'s pool entries and abstract records are kept, and
        so is every concrete record whose value is that of an abstract
        record of [k]. *)
    Definition Re (k : CallKey OSig) : PRel EHL CVFe := fun s s' =>
      exists v pool v' pool', ps_poss s = EOk v pool /\ ps_poss s' = EOk v' pool' /\
        (forall ls, lin_lookup k ls pool -> lin_lookup k ls pool') /\
        (forall o, okey o = k -> In o (snd v) -> In o (snd v')) /\
        (forall x, In x (erec (ps_mem s)) -> In (cop k (uval x)) (snd v) -> In x (erec (ps_mem s'))).

    (** Guarantee of [k]: the same for every other call. *)
    Definition Ge (k : CallKey OSig) : PRel EHL CVFe := fun s s' =>
      exists v pool v' pool', ps_poss s = EOk v pool /\ ps_poss s' = EOk v' pool' /\
        (forall k' ls, k' <> k -> lin_lookup k' ls pool -> lin_lookup k' ls pool') /\
        (forall o, okey o <> k -> In o (snd v) -> In o (snd v')) /\
        (forall x k', k' <> k -> In x (erec (ps_mem s)) -> In (cop k' (uval x)) (snd v) -> In x (erec (ps_mem s'))).

    Lemma Ge_in_Re k k' s s' : k' <> k -> Ge k' s s' -> Re k s s'.
    Proof.
      intros Hne (v & pool & v' & pool' & Hp & Hp' & Hlk & HP & Hx).
      exists v, pool, v', pool'. split; [exact Hp |]. split; [exact Hp' |]. split; [| split].
      - intros ls Hl. apply Hlk; [intros Heq; apply Hne; symmetry; exact Heq | exact Hl].
      - intros o Hk. apply HP. rewrite Hk. intros Heq. apply Hne. symmetry. exact Heq.
      - intros x Hxin Hc. apply (Hx x k); [intros Heq; apply Hne; symmetry; exact Heq | exact Hxin | exact Hc].
    Qed.

    Definition KInve (k : CallKey OSig) : EA := fun s =>
      exists v pool, ps_poss s = EOk v pool /\ lin_lookup k (@ls_inv OSig Inc) pool.

    (** After the FAA of [k] on underlay handle [hu]: the concrete record
        of [(fst k, hu)] holds the fetched value, which is [k]'s abstract
        record, and [k] is at [ls_lini]. *)
    Definition KLinie (k : CallKey OSig) (hu : nat) : EA := fun s =>
      exists c v pool, ps_poss s = EOk v pool /\
        In (@RelaxedTraceLin.Build_Op USig (fst k, hu) FAA c) (erec (ps_mem s)) /\
        In (cop k c) (snd v) /\ lin_lookup k (@ls_lini OSig Inc) pool.

    Definition KLinre (k : CallKey OSig) (r : nat) : EA := fun s =>
      exists v pool, ps_poss s = EOk v pool /\ lin_lookup k (@ls_linr OSig Inc r) pool.

    Lemma KInve_stable k : Stable Ie (Re k) (KInve k).
    Proof.
      intros s s' (v & pool & Hp & Hl) (v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _ & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Lemma KLinie_stable k hu : Stable Ie (Re k) (KLinie k hu).
    Proof.
      intros s s' (c & v & pool & Hp & Hx & HP & Hl) (v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & HPk & Hxk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists c, v1', pool1'.
      split; [exact Hp1' |]. split; [exact (Hxk _ Hx HP) |].
      split; [apply HPk; [reflexivity | exact HP] | apply Hlk; exact Hl].
    Qed.

    Lemma KLinre_stable k r : Stable Ie (Re k) (KLinre k r).
    Proof.
      intros s s' (v & pool & Hp & Hl) (v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _ & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Section CounterEIhlProof.
      Context (t : tid) (h : nat).
      Local Abbreviation kc := (@pair tid (RelaxedSig.handle OSig) t h).

      Abbreviation Pce := (PostInvoke Ie kc Inc (Ωc t)).

      Lemma pinit_KInve : Impl Ie Pce (KInve kc).
      Proof.
        intros [[σ p] γ] _ (p0 & γ0 & evs & (ca & P & pool0 & Hp0 & _) & Hinv & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, Hinv. rewrite Hp0 in Hinv.
        destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> _].
        exists (ca, P), (make_lin_entry kc (@ls_inv OSig Inc) :: pool0). split; [reflexivity | left; reflexivity].
      Qed.

      (** The FAA: as in [CounterHL.faa_updateh]; the key of the new record
          is unused (handle-linearity), so the records keep distinct keys. *)
      Lemma faa_updatee hu :
        EvUpdate Ie (Ge kc) kc (Build_ThreadEvent t (@InvEv USig hu FAA)) (KInve kc) (KLinie kc hu).
      Proof.
        intros σ p γ γ' (v & pool & Hp & Hl)
          (ca & P & pool1 & Hp1 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hku & Hndk & Hlt & Hndv) Hge σ' Hstep.
        destruct σ as [[n Pc] u]. unfold ecnt, erec, eused in *.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. rewrite Hp in Hp1. injection Hp1 as -> <-. subst p n.
        cbn in Hge. destruct Hge as (g1 & g2 & -> & -> & Hnb).
        cbn in Hstep. destruct Hstep as (Hnu & (r & st' & (-> & ->) & Hq') & Hu').
        destruct σ' as [[n' Pc'] u']. cbn in Hq', Hu'. injection Hq' as -> ->. subst u'.
        apply Forall_app in HJwf as [HJwf1 HJwf2]. pose proof (Forall_inv_tail HJwf2) as HJwf2'.
        destruct (emit_ready t h hu pool g1 g2 Hwf Hl HJ HJwf1 Hnb) as (pool' & Hu & Hwf' & HJ').
        pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
        assert (HPk : forall o, In o P -> okey o <> kc).
        { intros o Ho Hk. pose proof (HPl o Ho) as Hlo. rewrite Hk in Hlo.
          pose proof (lookup_unique pool kc _ _ Hwf Hl Hlo) as Heq. discriminate Heq. }
        exists (EOk (S ca, cop kc ca :: P) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_inv CVFe t h Inc); [exact Hu |].
          cbn. exists ca, (S ca). split; [split; reflexivity | reflexivity].
        - exists ca, (S ca, cop kc ca :: P), pool'. cbn. split; [reflexivity |].
          split; [left; reflexivity |]. split; [left; reflexivity |].
          exact (lin_update_target _ _ _ _ _ Hu2).
        - exists (S ca), (cop kc ca :: P), pool'. cbn [ps_poss ps_mem ps_ghost fst snd ecnt erec eused].
          split; [reflexivity |]. split; [reflexivity |]. split; [exact Hwf' |].
          split; [exact HJ' |]. split; [apply Forall_app; split; assumption |]. split.
          + intros o [<- | Ho]; [exact (lin_update_target _ _ _ _ _ Hu2) |].
            eapply lin_update_other_lookup; [exact Hu2 | exact (HPk o Ho) | exact (HPl o Ho)].
          + split; [constructor; [| exact HPnd]; intros Hin; apply in_map_iff in Hin as (o & Hk & Ho); exact (HPk o Ho Hk) |].
            split; [intros x [<- | Hx]; [left; reflexivity | right; exact (Hku x Hx)] |].
            split; [constructor; [| exact Hndk] |].
            { intros Hin. apply in_map_iff in Hin as (x & Hk & Hx). apply Hnu. cbn in Hk. rewrite <- Hk. exact (Hku x Hx). }
            split; [intros o [<- | Ho]; [cbn; lia | pose proof (Hlt o Ho); lia] |].
            cbn [map]. constructor; [| exact Hndv]. intros Hin. apply in_map_iff in Hin as (o & Hv & Ho).
            pose proof (Hlt o Ho). cbn in Hv. lia.
        - exists (ca, P), pool, (S ca, cop kc ca :: P), pool'. split; [reflexivity |]. split; [reflexivity |].
          split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu2 | exact Hne | exact Hlk] |].
          split; [intros o _ Ho; right; exact Ho |].
          intros x k' _ Hx _. right. exact Hx.
      Qed.

      (** The response: the record of [(t, hu)] is [kc]'s (distinct keys), so
          the response value is [kc]'s abstract value; removing the record
          keeps the records of the other calls, whose values differ. *)
      Lemma res_updatee hu r :
        EvUpdate Ie (Ge kc) kc (Build_ThreadEvent t (@ResEv USig hu FAA r)) (KLinie kc hu) (KLinre kc r).
      Proof.
        intros σ p γ γ' (c & v & pool & Hp & Hx & HP & Hl)
          (ca & P & pool1 & Hp1 & Hca & Hwf & HJ & HJwf & HPl & HPnd & Hku & Hndk & Hlt & Hndv) Hge σ' Hstep.
        destruct σ as [[n Pc] u]. unfold ecnt, erec, eused in *.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hge. subst γ'.
        cbn in Hstep. destruct Hstep as ((P1 & P2 & HPc & Hq') & Hu').
        destruct σ' as [[n' Pc'] u']. cbn in Hq', Hu', HPc. injection Hq' as -> ->. subst u'.
        rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        assert (Hcr : c = r).
        { assert (Hxr : In (@RelaxedTraceLin.Build_Op USig (t, hu) FAA r) Pc) by (rewrite HPc; apply in_elt).
          pose proof (ViewPossibility.NoDup_key_eq (@RelaxedTraceLin.op_key USig) _ _ _ Hndk Hx Hxr eq_refl) as Heq.
          exact (f_equal uval Heq). }
        subst r.
        cbn in HP. destruct (in_split _ _ HP) as (Pa1 & Pa2 & HPs).
        destruct (lin_update_exists kc (@ls_lini OSig Inc) (@ls_linr OSig Inc c) pool Hwf Hl) as (pool' & Hu).
        assert (HPk : forall o, In o (Pa1 ++ Pa2) -> okey o <> kc).
        { intros o Ho Hk. rewrite HPs, map_app in HPnd. cbn [map] in HPnd.
          apply NoDup_remove_2 in HPnd. apply HPnd. rewrite <- map_app.
          apply in_map_iff. exists o. split; [exact Hk | exact Ho]. }
        assert (HPsub : forall o, In o (Pa1 ++ Pa2) -> In o P) by (intros o Ho; rewrite HPs; exact (in_remove_in _ _ _ _ Ho)).
        assert (HPcsub : forall x, In x (P1 ++ P2) -> In x Pc) by (intros x Hx'; rewrite HPc; exact (in_remove_in _ _ _ _ Hx')).
        exists (EOk (ca, Pa1 ++ Pa2) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_ret CVFe t h Inc c _ _ _ _ Hu). cbn. exists Pa1, Pa2.
          split; [exact HPs | reflexivity].
        - exists (ca, Pa1 ++ Pa2), pool'. split; [reflexivity | eapply lin_update_target; exact Hu].
        - exists ca, (Pa1 ++ Pa2), pool'. cbn [ps_poss ps_mem ps_ghost fst snd ecnt erec eused].
          split; [reflexivity |]. split; [exact Hca |].
          split; [eapply lin_update_well_formed; eauto |].
          split; [intros t'; rewrite (inv_keys_update _ _ _ _ t' Hu); apply HJ |].
          split; [exact HJwf |]. split.
          + intros o Ho. eapply lin_update_other_lookup; [exact Hu | exact (HPk o Ho) | exact (HPl o (HPsub o Ho))].
          + split; [rewrite HPs, map_app in HPnd; cbn [map] in HPnd; rewrite map_app; exact (NoDup_remove_1 _ _ _ HPnd) |].
            split; [intros x Hx'; exact (Hku x (HPcsub x Hx')) |].
            split; [rewrite HPc, map_app in Hndk; cbn [map] in Hndk; rewrite map_app; exact (NoDup_remove_1 _ _ _ Hndk) |].
            split; [intros o Ho; exact (Hlt o (HPsub o Ho)) |].
            rewrite HPs, map_app in Hndv. cbn [map] in Hndv. rewrite map_app. exact (NoDup_remove_1 _ _ _ Hndv).
        - exists (ca, P), pool, (ca, Pa1 ++ Pa2), pool'. split; [reflexivity |]. split; [reflexivity |].
          split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu | exact Hne | exact Hlk] |].
          split.
          + intros o Hk Ho. cbn in Ho |- *. rewrite HPs in Ho. apply (in_remove_ne _ _ _ _ Ho).
            intros ->. apply Hk. reflexivity.
          + intros x k' Hne Hx' Hck. cbn in Hck |- *. rewrite HPc in Hx'. apply (in_remove_ne _ _ _ _ Hx').
            intros ->. cbn in Hck. apply Hne.
            assert (Hv : oval (cop k' c) = oval (cop kc c)) by reflexivity.
            pose proof (ViewPossibility.NoDup_key_eq oval _ _ _ Hndv Hck HP Hv) as Heq.
            exact (f_equal okey Heq).
      Qed.

      Definition sl_faae (hu : nat) : Slot EHL CVFe :=
        mkSlot (inv_tev (E := USig) (F := OSig) kc empty_store hu FAA) (KInve kc) (fun _ _ => True)
          (KLinie kc hu) (Ge kc).

      Definition sl_rese (hu : nat) (r : nat) : Slot EHL CVFe :=
        mkSlot (res_tev (E := USig) (F := OSig) kc hu FAA r) (fun _ => True) (fun _ => KLinie kc hu)
          (KLinre kc r) (Ge kc).

      (** The derivation of [CounterHL.counter_derivationh], with the new
          assertions. *)
      Lemma counter_derivatione :
        RProvable Ie Re Ge kc Pce
          (fun a Γ H => Close Ie Re Ge kc Pce (KLinre kc) a Γ H /\ Ωc t (own_invs Γ)) [] empty_store (Mc Inc t).
      Proof.
        cbn. unfold body.
        apply rp_future with (sl := sl_faae); [intros; reflexivity | |].
        { intros hu _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faae].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faae].
            intros σ p γ γ' [HK _]. apply (faa_updatee hu σ p γ γ' HK).
          - exact pinit_KInve.
          - intros d sd _ Hd. destruct d; discriminate.
          - apply KInve_stable.
          - intros d _. apply Stable_true.
          - intros g sg Hg. destruct g; discriminate.
          - intros d g sg _ Hg. destruct g; discriminate.
          - intros y sy Hy. destruct y; discriminate.
          - intros y sy d Hy. destruct y; discriminate. }
        intros hu Hf. cbv beta.
        apply rp_wait_pending with (sl := sl_rese hu); [left; reflexivity | intros; reflexivity | |].
        { intros r. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_rese].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_rese].
            intros σ p γ γ' [_ Hin]. apply (res_updatee hu r σ p γ γ'). apply (Hin 0).
            exact (dprec_faa_res t h hu r).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [|]]; try discriminate.
            cbn in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
          - apply Stable_true.
          - intros d _. apply KLinie_stable.
          - intros g sg _. apply Stable_true.
          - intros d g sg Hd Hg Hnb. exfalso. apply dprec_lt in Hd. cbn in Hd.
            destruct g as [| g]; [| destruct g; discriminate]. assert (d = 0) by lia. subst d.
            apply Hnb. apply before_refl.
          - intros y sy Hy Hnb. exfalso. destruct y as [| y]; [| destruct y; discriminate].
            apply Hnb. apply before_dprec. exact (dprec_faa_res t h hu r).
          - intros y sy d Hy _ Hd. exfalso. apply dprec_lt in Hd. destruct y as [| y]; [lia |].
            destruct y; discriminate. }
        intros r H2 Hres. cbv beta. apply rp_ret. split.
        - apply close_done with
            (fin := fun d => match d with 1 => KLinre kc r | _ => fun _ => True end)
            (fin0 := fun _ => True).
          + eapply resolve_fresh_all_resolved; [constructor | exact Hres].
          + constructor.
            * intros d sd Hd. destruct d as [| [| d]]; cbn in Hd; try (destruct d; discriminate).
              -- intros s _ _. exact Logic.I.
              -- injection Hd as <-. intros s _ Hs. exact Hs.
            * intros s _ _. exact Logic.I.
            * intros d g sg Hd Hg Hnb. destruct d as [| [| d]]; [apply Stable_true | | cbn in Hd; lia].
              exfalso. apply Hnb. destruct g as [| [| g]]; [| apply before_refl | destruct g; discriminate].
              apply before_dprec. exact (dprec_faa_res t h hu r).
            * intros g sg _. apply Stable_true.
            * intros [| [| d]]; [apply Stable_true | apply KLinre_stable | apply Stable_true].
            * apply Stable_true.
            * intros s _ _ Hfin. exact (Hfin 1 _ eq_refl Logic.I).
        - exists hu. reflexivity.
      Qed.

      Lemma counter_PIe : forall s, Pce s -> Ie s.
      Proof.
        intros [[σ p] γ] (p0 & γ0 & evs & (ca & P & pool0 & Hp0 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hrest) & Hinv & Hg & (hu & ->) & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst γ. rewrite Hp0 in Hinv.
        destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> Hfresh].
        exists ca, P, (make_lin_entry kc (@ls_inv OSig Inc) :: pool0). split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_insert_well_formed; [constructor; exact Hfresh | exact Hwf] |]. split.
        - intros t'. cbn [ps_ghost snd inv_keys]. rewrite HJ, gkeys_app. f_equal.
          unfold ek, gkeys. cbn. destruct (Pos.eqb t t'); reflexivity.
        - split; [apply Forall_app; split; [exact HJwf | constructor; [split; [reflexivity | exact Logic.I] | constructor]] |].
          split; [intros o Ho; right; exact (HPl o Ho) |]. split; [exact HPnd | exact Hrest].
      Qed.

      Lemma counter_rete r s : KLinre kc r s -> Ie s -> NoOwn kc (ps_ghost s) -> RetCond Ie Ge kc Inc r s.
      Proof.
        intros (v & pool & Hp & Hl) HI _. destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        subst p. exists (EOk v pool). split; [apply rt_refl |]. split; [exists v, pool; split; [reflexivity | exact Hl] |].
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hret. destruct (pret_inv _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        destruct HI as (ca & P & pool3 & Hp3 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hrest). cbn in Hp3.
        injection Hp3 as Hv Hpool. subst v pool3.
        exists ca, P, pool2. cbn. split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_remove_well_formed; eauto |].
        split; [intros t'; rewrite (inv_keys_remove _ _ _ _ t' Hrem); apply HJ |].
        split; [exact HJwf |]. split; [| split; [exact HPnd | exact Hrest]].
        intros o Ho. eapply lin_remove_other_lookup; [exact Hrem | | exact (HPl o Ho)].
        intros Hk. pose proof (HPl o Ho) as Hlo. rewrite Hk in Hlo.
        pose proof (lookup_unique pool kc _ _ Hwf Hl Hlo) as Heq. discriminate Heq.
      Qed.
    End CounterEIhlProof.

    Theorem counter_eihl_provable t :
      MethodProvable Ie Re Ge Mc t Inc (fun _ => Ωc t) (fun h => KLinre (t, h)).
    Proof.
      constructor.
      - intros h s Hs. exact (counter_PIe t h s Hs).
      - intros h r s HQ HI Hno. exact (counter_rete t h r s HQ HI Hno).
      - intros h. exact (counter_derivatione t h).
    Qed.

    Theorem counter_eihl_methodsem t : MethodSem Ie Re Ge Mc t Inc.
    Proof. eapply method_sound. exact (counter_eihl_provable t). Qed.

    Lemma counter_eihl_init : Ie (ehσ0, EOk (0, []) [], []).
    Proof.
      exists 0, [], []. cbn. split; [reflexivity |]. split; [reflexivity |].
      split; [constructor |]. split; [reflexivity |]. split; [constructor |].
      split; [intros o [] |]. split; [constructor |]. split; [intros x [] |].
      split; [constructor |]. split; [intros o [] | constructor].
    Qed.

    (** m-20: every field of [RLHL2Hyps] holds for the overlapping counter
        over the handle-linear specification LTS [EIhl uδ]. *)
    Theorem counter_eihl_rlhl2 : RLHL2Hyps Ie Re Ge Mc ehσ0 (0, []).
    Proof.
      constructor.
      - intros t []. exact (counter_eihl_methodsem t).
      - intros k k' s s' Hne HG. exact (Ge_in_Re k' k s s' Hne HG).
      - intros k k' op tr ret s p' Hne _ HI Hinv. destruct s as [[σ p] γ].
        destruct HI as (ca & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> _].
        exists (ca, P), pool, (ca, P), (make_lin_entry (t, h) (ls_inv op) :: pool).
        split; [reflexivity |]. split; [reflexivity |]. split; [intros ls Hl; right; exact Hl |].
        split; [auto | auto].
      - intros k k' op r s p2 Hne HI Hret _. destruct s as [[σ p] γ].
        destruct HI as (ca & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pret_inv _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        exists (ca, P), pool, (ca, P), pool2. split; [reflexivity |]. split; [reflexivity |].
        split; [| split; [auto | auto]]. intros ls Hl. eapply lin_remove_other_lookup; [exact Hrem | | exact Hl].
        intros Heq. apply Hne. symmetry. exact Heq.
      - intros s (ca & P & pool & Hp & _ & Hwf & _). exists (ca, P), pool. auto.
      - exact counter_eihl_init.
    Qed.

    (** Copy-cat inclusion over [EIhl uδ], and over the plain [EI uδ]. *)
    Theorem counter_complin_eihl : RCompLin Mc EHL ehσ0 CVFe (0, []).
    Proof. exact (rlhl_complin_ei cδ 0 Ie Re Ge Mc ehσ0 counter_eihl_rlhl2). Qed.

    Theorem counter_complin_ei : RCompLin Mc (RelaxedHoareSpec.EI CounterRelLin.uδ) (0, []) CVFe (0, []).
    Proof. exact (rlhl_complin_eihl CounterRelLin.uδ cδ 0 Ie Re Ge Mc (0, []) counter_eihl_rlhl2). Qed.

    (** Every complete overlay trace of the counter over [EI uδ] is
        relaxed-linearizable to the sequential counter. *)
    Corollary counter_eihl_rel_lin s :
      MTraces (RelaxedHoareSpec.EI CounterRelLin.uδ) Mc (0, []) s -> PrefixView.complete s ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) s (RelaxedSig.semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof. exact (complin_ei_rel_lin cδ 0 Mc (RelaxedHoareSpec.EI CounterRelLin.uδ) (0, []) counter_complin_ei s). Qed.

    (** Non-vacuity: the module-derived execution of
        [CounterRelLin.inc_ooo_exec] (two overlapping [Inc]s of [t0]; the
        younger returns [1] first, the older [0] afterwards) also runs over
        [EI uδ], hence over [EIhl uδ] ([hlift_ei]), so the conclusions
        above are about non-empty trace sets with overlapping same-thread
        calls. *)
    Theorem inc_ooo_exec_ei :
      exists c, module_execution_tagged (RelaxedHoareSpec.EI CounterRelLin.uδ) Mc
                  (initial_tagged_module (RelaxedHoareSpec.EI CounterRelLin.uδ) (0, [])) CounterRelLin.inc_ooo_evs c /\
        (forall e, In e (tm_calls c) -> ce_cell OSig e = DeadCall).
    Proof.
      set (V := RelaxedHoareSpec.EI CounterRelLin.uδ).
      eexists. split.
      - unfold CounterRelLin.inc_ooo_evs.
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V Mc t0 1 Inc (0, []) [] [] [] [CounterRelLin.fi 0; CounterRelLin.fr 0 0] 0).
          - intros [].
          - apply CounterRelLin.body_produces.
          - split; [repeat constructor; intros [] | intros key Hk []]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V Mc t0 2 Inc (0, []) _ _ _ [CounterRelLin.fi 1; CounterRelLin.fr 1 1] 1).
          - intros [Heq | []]. discriminate Heq.
          - apply CounterRelLin.body_produces.
          - split; [repeat constructor; intros [] |].
            intros key [<- | []] [Heq | []]. discriminate Heq. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mc (@Build_TaggedScheduledEvent USig OSig (t0, 1) (CounterRelLin.fi 0))).
          - cbn. apply tagged_select_here.
          - cbn. exists 0, 1. split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mc (@Build_TaggedScheduledEvent USig OSig (t0, 2) (CounterRelLin.fi 1))).
          - cbn. apply tagged_select_next; [| apply tagged_select_here].
            right. split; [reflexivity |]. unfold must_precede. cbn. apply resolved_in_empty.
          - cbn. exists 1, 2. split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mc (@Build_TaggedScheduledEvent USig OSig (t0, 2) (CounterRelLin.fr 1 1))).
          - cbn. apply tagged_select_next; [| apply tagged_select_here].
            right. split; [reflexivity |]. unfold must_precede. cbn. intros [].
          - cbn. exists [], [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0]. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_here.
          - intros [Heq | []]. discriminate Heq. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mc (@Build_TaggedScheduledEvent USig OSig (t0, 1) (CounterRelLin.fr 0 0))).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros Heq; discriminate Heq | apply finish_here].
          - intros []. }
        apply tagged_module_execution_refl.
      - intros e He. cbn in He. destruct He as [<- | [<- | []]]; reflexivity.
    Qed.

    Corollary ooo_trace_ei : MTraces (RelaxedHoareSpec.EI CounterRelLin.uδ) Mc (0, []) CounterCompLin.ooo_trace.
    Proof. destruct inc_ooo_exec_ei as (c & Hex & _). exists CounterRelLin.inc_ooo_evs, c. split; [exact Hex | reflexivity]. Qed.

    Corollary ooo_trace_eihl : MTraces EHL Mc ehσ0 CounterCompLin.ooo_trace.
    Proof. exact (proj1 (hlift_ei CounterRelLin.uδ Mc (0, []) _) ooo_trace_ei). Qed.
  End CounterEIhl.

  (** [CounterEIhlFrame] (latest-review m-34): the counter of
      [CounterEIhl] (same module [Mc], underlay [EIhl uδ], overlay [CVFe],
      initial states), verified again with a rely and a guarantee whose
      memory part mentions no value: "memory moves by [EIhl uδ] steps"
      ([RelaxedHoareCompLinSpec.eihl_steps]).  The call's own FAA record
      is tracked by ownership ([RelaxedHoareCompLinSpec.eihl_mine]), not
      by the uniqueness of the counter's values.

      - [KLinim k hu]: [k] owns the record of its FAA; established by
        [eihl_mine_inv] at the FAA ([faa_updatem]), stable under the rely
        by [eihl_mine_steps] ([KLinim_stable]), and used at the response
        by [eihl_mine_res] ([res_updatem]).
      - [Ifm]: [CounterEIhl.Ie] without its clauses on concrete keys and
        on values; the coupling [ecnt = ca] of the two counters stays (an
        invariant, not a rely clause).
      - [counter_frame_rlhl2]: every field of [RLHL2Hyps], by the rules
        ([counter_frame_provable], through [method_sound]); closed.
      - [counter_frame_complin_eihl], [counter_frame_complin_ei],
        [counter_frame_rel_lin]: as in [CounterEIhl].
      - Non-vacuity: [ooo_rtrace_frame], [ooo_rel_lin_frame] apply the
        instance to the module-derived overlapping execution
        [CounterEIhl.inc_ooo_exec_ei].
      - [Rfm_any_mem]: the rely admits every memory step.

      Scope: as [CounterEIhl] (I=∅ at both levels, a single-future body,
      the module is the FAA-to-[Inc] copy-cat).  Only the memory part of
      the rely and the guarantee is specification-independent; the
      invariant still couples the concrete and the abstract counter. *)

  Module CounterEIhlFrame.
    Import Counter CounterHL RelaxedHoareCompLin RelaxedHoareCompLinSpec CounterEIhl.

    Abbreviation uδ := CounterRelLin.uδ.

    (** The invariant: [CounterEIhl.Ie] without its three clauses on
        values and concrete keys (distinct concrete keys, abstract values
        below the counter, distinct abstract values), plus
        [eihl_rec_used] (every pending FAA record has a used key).  The
        coupling of the two counters ([ecnt = ca]) stays. *)
    Definition Ifm : EA := fun s => exists ca P pool,
      ps_poss s = EOk (ca, P) pool /\ ecnt (ps_mem s) = ca /\ lin_pool_well_formed pool /\
      (forall t', inv_keys t' pool = gkeys t' (ps_ghost s)) /\ Forall Jwf (ps_ghost s) /\
      (forall o, In o P -> lin_lookup (okey o) (@ls_lini OSig Inc) pool) /\
      NoDup (map okey P) /\
      eihl_rec_used uδ (ps_mem s).

    (** Rely of [k]: memory moves by any [EIhl uδ] steps (no value, no
        key, no operation is mentioned); [k]'s pool entries and abstract
        records are kept. *)
    Definition Rfm (k : CallKey OSig) : PRel EHL CVFe := fun s s' =>
      eihl_steps uδ (ps_mem s) (ps_mem s') /\
      exists v pool v' pool', ps_poss s = EOk v pool /\ ps_poss s' = EOk v' pool' /\
        (forall ls, lin_lookup k ls pool -> lin_lookup k ls pool') /\
        (forall o, okey o = k -> In o (snd v) -> In o (snd v')).

    (** Guarantee of [k]: memory moves by [EIhl uδ] steps; the pool
        entries and abstract records of every other call are kept. *)
    Definition Gfm (k : CallKey OSig) : PRel EHL CVFe := fun s s' =>
      eihl_steps uδ (ps_mem s) (ps_mem s') /\
      exists v pool v' pool', ps_poss s = EOk v pool /\ ps_poss s' = EOk v' pool' /\
        (forall k' ls, k' <> k -> lin_lookup k' ls pool -> lin_lookup k' ls pool') /\
        (forall o, okey o <> k -> In o (snd v) -> In o (snd v')).

    Lemma Gfm_in_Rfm k k' s s' : k' <> k -> Gfm k' s s' -> Rfm k s s'.
    Proof.
      intros Hne (Hm & v & pool & v' & pool' & Hp & Hp' & Hlk & HP). split; [exact Hm |].
      exists v, pool, v', pool'. split; [exact Hp |]. split; [exact Hp' |]. split.
      - intros ls Hl. apply Hlk; [intros Heq; apply Hne; symmetry; exact Heq | exact Hl].
      - intros o Hk. apply HP. rewrite Hk. intros Heq. apply Hne. symmetry. exact Heq.
    Qed.

    (** The rely admits every memory step of [EIhl uδ], whatever the
        values (contrast [CounterEIhl.Re], which forbids removing a record
        whose value is one of [k]'s abstract values). *)
    Lemma Rfm_any_mem k σ σ' v pool γ γ' :
      eihl_steps uδ σ σ' -> Rfm k (σ, EOk v pool, γ) (σ', EOk v pool, γ').
    Proof.
      intros Hs. split; [exact Hs |]. exists v, pool, v, pool. repeat split; auto.
    Qed.

    (** After the FAA of [k] on underlay handle [hu]: [k] owns the FAA
        record of [(fst k, hu)], with the fetched value [c]
        ([eihl_mine]), [c] is [k]'s abstract record, and [k] is at
        [ls_lini].  Stable under [Rfm k] by [eihl_mine_steps]. *)
    Definition KLinim (k : CallKey OSig) (hu : nat) : EA := fun s =>
      exists c v pool, ps_poss s = EOk v pool /\
        eihl_mine uδ (fst k, hu) (@RelaxedTraceLin.Build_Op USig (fst k, hu) FAA c) (ps_mem s) /\
        In (cop k c) (snd v) /\ lin_lookup k (@ls_lini OSig Inc) pool.

    Lemma KInve_stablem k : Stable Ifm (Rfm k) (KInve k).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Lemma KLinim_stable k hu : Stable Ifm (Rfm k) (KLinim k hu).
    Proof.
      intros s s' (c & v & pool & Hp & Hm & HP & Hl) (Hs & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & HPk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists c, v1', pool1'.
      split; [exact Hp1' |]. split; [exact (eihl_mine_steps uδ _ _ _ _ Hs Hm) |].
      split; [apply HPk; [reflexivity | exact HP] | apply Hlk; exact Hl].
    Qed.

    Lemma KLinre_stablem k r : Stable Ifm (Rfm k) (KLinre k r).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hlk & _) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' | apply Hlk; exact Hl].
    Qed.

    Section CounterFrameProof.
      Context (t : tid) (h : nat).
      Local Abbreviation kc := (@pair tid (RelaxedSig.handle OSig) t h).

      Abbreviation Pcm := (PostInvoke Ifm kc Inc (Ωc t)).

      Lemma pinit_KInvm : Impl Ifm Pcm (KInve kc).
      Proof.
        intros [[σ p] γ] _ (p0 & γ0 & evs & (ca & P & pool0 & Hp0 & _) & Hinv & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, Hinv. rewrite Hp0 in Hinv.
        destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> _].
        exists (ca, P), (make_lin_entry kc (@ls_inv OSig Inc) :: pool0). split; [reflexivity | left; reflexivity].
      Qed.

      (** The FAA: the abstract invocation as in
          [CounterEIhl.faa_updatee]; ownership of the new record by
          [eihl_mine_inv]. *)
      Lemma faa_updatem hu :
        EvUpdate Ifm (Gfm kc) kc (Build_ThreadEvent t (@InvEv USig hu FAA)) (KInve kc) (KLinim kc hu).
      Proof.
        intros σ p γ γ' (v & pool & Hp & Hl)
          (ca & P & pool1 & Hp1 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        cbn in Hge. destruct Hge as (g1 & g2 & -> & -> & Hnb).
        pose proof (eihl_rec_used_step uδ _ σ σ' Hstep Hru) as Hru'.
        destruct (eihl_mine_inv uδ t hu FAA σ σ' Hstep Hru) as (r & st' & Hd & Hσ' & Hm).
        destruct σ as [[n Pc] u]. unfold ecnt in Hc. cbn [fst snd] in Hc, Hd, Hσ'. subst n.
        destruct Hd as [Hr Hst']. subst r st'.
        apply Forall_app in HJwf as [HJwf1 HJwf2]. pose proof (Forall_inv_tail HJwf2) as HJwf2'.
        destruct (emit_ready t h hu pool g1 g2 Hwf Hl HJ HJwf1 Hnb) as (pool' & Hu & Hwf' & HJ').
        pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
        assert (HPk : forall o, In o P -> okey o <> kc).
        { intros o Ho Hk. pose proof (HPl o Ho) as Hlo. rewrite Hk in Hlo.
          pose proof (lookup_unique pool kc _ _ Hwf Hl Hlo) as Heq. discriminate Heq. }
        exists (EOk (S ca, cop kc ca :: P) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_inv CVFe t h Inc); [exact Hu |].
          cbn. exists ca, (S ca). split; [split; reflexivity | reflexivity].
        - exists ca, (S ca, cop kc ca :: P), pool'. cbn [ps_poss ps_mem ps_ghost fst snd].
          split; [reflexivity |]. split; [exact Hm |]. split; [left; reflexivity |].
          exact (lin_update_target _ _ _ _ _ Hu2).
        - exists (S ca), (cop kc ca :: P), pool'. cbn [ps_poss ps_mem ps_ghost fst snd].
          split; [reflexivity |]. split; [rewrite Hσ'; reflexivity |]. split; [exact Hwf' |].
          split; [exact HJ' |]. split; [apply Forall_app; split; assumption |]. split.
          + intros o [<- | Ho]; [exact (lin_update_target _ _ _ _ _ Hu2) |].
            eapply lin_update_other_lookup; [exact Hu2 | exact (HPk o Ho) | exact (HPl o Ho)].
          + split; [| exact Hru'].
            constructor; [| exact HPnd]; intros Hin; apply in_map_iff in Hin as (o & Hk & Ho); exact (HPk o Ho Hk).
        - split; [apply rt_step; exists (Build_ThreadEvent t (@InvEv USig hu FAA)); exact Hstep |].
          exists (ca, P), pool, (S ca, cop kc ca :: P), pool'. split; [reflexivity |]. split; [reflexivity |].
          split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu2 | exact Hne | exact Hlk] |].
          intros o _ Ho. right. exact Ho.
      Qed.

      (** The response: by ownership ([eihl_mine_res]) the response
          value is the fetched value [c]; no value of another call is
          consulted. *)
      Lemma res_updatem hu r :
        EvUpdate Ifm (Gfm kc) kc (Build_ThreadEvent t (@ResEv USig hu FAA r)) (KLinim kc hu) (KLinre kc r).
      Proof.
        intros σ p γ γ' (c & v & pool & Hp & Hm & HP & Hl)
          (ca & P & pool1 & Hp1 & Hca & Hwf & HJ & HJwf & HPl & HPnd & Hru) Hge σ' Hstep.
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hge. subst γ'.
        pose proof (eihl_mine_res uδ (t, hu) _ FAA r σ σ' Hm Hstep) as Hx.
        assert (Hcr : c = r) by exact (f_equal uval Hx). subst r.
        pose proof (eihl_rec_used_step uδ _ σ σ' Hstep Hru) as Hru'.
        assert (Hcnt : ecnt σ' = ecnt σ).
        { destruct σ as [[n Pc] u], σ' as [[n' Pc'] u']. cbn in Hstep. destruct Hstep as ((P1 & P2 & _ & Hq') & _).
          injection Hq' as -> _. reflexivity. }
        rewrite Hp in Hp1. injection Hp1 as -> <-. subst p.
        cbn in HP. destruct (in_split _ _ HP) as (Pa1 & Pa2 & HPs).
        destruct (lin_update_exists kc (@ls_lini OSig Inc) (@ls_linr OSig Inc c) pool Hwf Hl) as (pool' & Hu).
        assert (HPk : forall o, In o (Pa1 ++ Pa2) -> okey o <> kc).
        { intros o Ho Hk. rewrite HPs, map_app in HPnd. cbn [map] in HPnd.
          apply NoDup_remove_2 in HPnd. apply HPnd. rewrite <- map_app.
          apply in_map_iff. exists o. split; [exact Hk | exact Ho]. }
        assert (HPsub : forall o, In o (Pa1 ++ Pa2) -> In o P) by (intros o Ho; rewrite HPs; exact (in_remove_in _ _ _ _ Ho)).
        exists (EOk (ca, Pa1 ++ Pa2) pool'). split; [| split; [| split]].
        - apply rt_step. exists kc. apply (psa_ret CVFe t h Inc c _ _ _ _ Hu). cbn. exists Pa1, Pa2.
          split; [exact HPs | reflexivity].
        - exists (ca, Pa1 ++ Pa2), pool'. split; [reflexivity | eapply lin_update_target; exact Hu].
        - exists ca, (Pa1 ++ Pa2), pool'. cbn [ps_poss ps_mem ps_ghost fst snd].
          split; [reflexivity |]. split; [rewrite Hcnt; exact Hca |].
          split; [eapply lin_update_well_formed; eauto |].
          split; [intros t'; rewrite (inv_keys_update _ _ _ _ t' Hu); apply HJ |].
          split; [exact HJwf |]. split.
          + intros o Ho. eapply lin_update_other_lookup; [exact Hu | exact (HPk o Ho) | exact (HPl o (HPsub o Ho))].
          + split; [rewrite HPs, map_app in HPnd; cbn [map] in HPnd; rewrite map_app; exact (NoDup_remove_1 _ _ _ HPnd) |].
            exact Hru'.
        - split; [apply rt_step; exists (Build_ThreadEvent t (@ResEv USig hu FAA c)); exact Hstep |].
          exists (ca, P), pool, (ca, Pa1 ++ Pa2), pool'. split; [reflexivity |]. split; [reflexivity |].
          split; [intros k' ls Hne Hlk; eapply lin_update_other_lookup; [exact Hu | exact Hne | exact Hlk] |].
          intros o Hk Ho. cbn in Ho |- *. rewrite HPs in Ho. apply (in_remove_ne _ _ _ _ Ho).
          intros ->. apply Hk. reflexivity.
      Qed.

      Definition sl_faam (hu : nat) : Slot EHL CVFe :=
        mkSlot (inv_tev (E := USig) (F := OSig) kc empty_store hu FAA) (KInve kc) (fun _ _ => True)
          (KLinim kc hu) (Gfm kc).

      Definition sl_resm (hu : nat) (r : nat) : Slot EHL CVFe :=
        mkSlot (res_tev (E := USig) (F := OSig) kc hu FAA r) (fun _ => True) (fun _ => KLinim kc hu)
          (KLinre kc r) (Gfm kc).

      (** The derivation of [CounterEIhl.counter_derivatione], with the
          new assertions and relations. *)
      Lemma counter_derivationm :
        RProvable Ifm Rfm Gfm kc Pcm
          (fun a Γ H => Close Ifm Rfm Gfm kc Pcm (KLinre kc) a Γ H /\ Ωc t (own_invs Γ)) [] empty_store (Mc Inc t).
      Proof.
        cbn. unfold body.
        apply rp_future with (sl := sl_faam); [intros; reflexivity | |].
        { intros hu _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faam].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_faam].
            intros σ p γ γ' [HK _]. apply (faa_updatem hu σ p γ γ' HK).
          - exact pinit_KInvm.
          - intros d sd _ Hd. destruct d; discriminate.
          - apply KInve_stablem.
          - intros d _. apply Stable_true.
          - intros g sg Hg. destruct g; discriminate.
          - intros d g sg _ Hg. destruct g; discriminate.
          - intros y sy Hy. destruct y; discriminate.
          - intros y sy d Hy. destruct y; discriminate. }
        intros hu Hf. cbv beta.
        apply rp_wait_pending with (sl := sl_resm hu); [left; reflexivity | intros; reflexivity | |].
        { intros r. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_resm].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_resm].
            intros σ p γ γ' [_ Hin]. apply (res_updatem hu r σ p γ γ'). apply (Hin 0).
            exact (dprec_faa_res t h hu r).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [|]]; try discriminate.
            cbn in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
          - apply Stable_true.
          - intros d _. apply KLinim_stable.
          - intros g sg _. apply Stable_true.
          - intros d g sg Hd Hg Hnb. exfalso. apply dprec_lt in Hd. cbn in Hd.
            destruct g as [| g]; [| destruct g; discriminate]. assert (d = 0) by lia. subst d.
            apply Hnb. apply before_refl.
          - intros y sy Hy Hnb. exfalso. destruct y as [| y]; [| destruct y; discriminate].
            apply Hnb. apply before_dprec. exact (dprec_faa_res t h hu r).
          - intros y sy d Hy _ Hd. exfalso. apply dprec_lt in Hd. destruct y as [| y]; [lia |].
            destruct y; discriminate. }
        intros r H2 Hres. cbv beta. apply rp_ret. split.
        - apply close_done with
            (fin := fun d => match d with 1 => KLinre kc r | _ => fun _ => True end)
            (fin0 := fun _ => True).
          + eapply resolve_fresh_all_resolved; [constructor | exact Hres].
          + constructor.
            * intros d sd Hd. destruct d as [| [| d]]; cbn in Hd; try (destruct d; discriminate).
              -- intros s _ _. exact Logic.I.
              -- injection Hd as <-. intros s _ Hs. exact Hs.
            * intros s _ _. exact Logic.I.
            * intros d g sg Hd Hg Hnb. destruct d as [| [| d]]; [apply Stable_true | | cbn in Hd; lia].
              exfalso. apply Hnb. destruct g as [| [| g]]; [| apply before_refl | destruct g; discriminate].
              apply before_dprec. exact (dprec_faa_res t h hu r).
            * intros g sg _. apply Stable_true.
            * intros [| [| d]]; [apply Stable_true | apply KLinre_stablem | apply Stable_true].
            * apply Stable_true.
            * intros s _ _ Hfin. exact (Hfin 1 _ eq_refl Logic.I).
        - exists hu. reflexivity.
      Qed.

      Lemma counter_PIm : forall s, Pcm s -> Ifm s.
      Proof.
        intros [[σ p] γ] (p0 & γ0 & evs & (ca & P & pool0 & Hp0 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) & Hinv & Hg & (hu & ->) & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst γ. rewrite Hp0 in Hinv.
        destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> Hfresh].
        exists ca, P, (make_lin_entry kc (@ls_inv OSig Inc) :: pool0). split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_insert_well_formed; [constructor; exact Hfresh | exact Hwf] |]. split.
        - intros t'. cbn [ps_ghost snd inv_keys]. rewrite HJ, gkeys_app. f_equal.
          unfold ek, gkeys. cbn. destruct (Pos.eqb t t'); reflexivity.
        - split; [apply Forall_app; split; [exact HJwf | constructor; [split; [reflexivity | exact Logic.I] | constructor]] |].
          split; [intros o Ho; right; exact (HPl o Ho) |]. split; [exact HPnd | exact Hru].
      Qed.

      Lemma counter_retm r s : KLinre kc r s -> Ifm s -> NoOwn kc (ps_ghost s) -> RetCond Ifm Gfm kc Inc r s.
      Proof.
        intros (v & pool & Hp & Hl) HI _. destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        subst p. exists (EOk v pool). split; [apply rt_refl |]. split; [exists v, pool; split; [reflexivity | exact Hl] |].
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hret. destruct (pret_inv _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        destruct HI as (ca & P & pool3 & Hp3 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru). cbn in Hp3.
        injection Hp3 as Hv Hpool. subst v pool3.
        exists ca, P, pool2. cbn. split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_remove_well_formed; eauto |].
        split; [intros t'; rewrite (inv_keys_remove _ _ _ _ t' Hrem); apply HJ |].
        split; [exact HJwf |]. split; [| split; [exact HPnd | exact Hru]].
        intros o Ho. eapply lin_remove_other_lookup; [exact Hrem | | exact (HPl o Ho)].
        intros Hk. pose proof (HPl o Ho) as Hlo. rewrite Hk in Hlo.
        pose proof (lookup_unique pool kc _ _ Hwf Hl Hlo) as Heq. discriminate Heq.
      Qed.
    End CounterFrameProof.

    Theorem counter_frame_provable t :
      MethodProvable Ifm Rfm Gfm Mc t Inc (fun _ => Ωc t) (fun h => KLinre (t, h)).
    Proof.
      constructor.
      - intros h s Hs. exact (counter_PIm t h s Hs).
      - intros h r s HQ HI Hno. exact (counter_retm t h r s HQ HI Hno).
      - intros h. exact (counter_derivationm t h).
    Qed.

    Theorem counter_frame_methodsem t : MethodSem Ifm Rfm Gfm Mc t Inc.
    Proof. eapply method_sound. exact (counter_frame_provable t). Qed.

    Lemma counter_frame_init : Ifm (ehσ0, EOk (0, []) [], []).
    Proof.
      exists 0, [], []. cbn. split; [reflexivity |]. split; [reflexivity |].
      split; [constructor |]. split; [reflexivity |]. split; [constructor |].
      split; [intros o [] |]. split; [constructor |]. exact (eihl_rec_used_init uδ 0).
    Qed.

    (** latest-review m-34: every field of [RLHL2Hyps] holds for the
        overlapping counter over [EIhl uδ], with a value-free memory part
        of the rely and the guarantee. *)
    Theorem counter_frame_rlhl2 : RLHL2Hyps Ifm Rfm Gfm Mc ehσ0 (0, []).
    Proof.
      constructor.
      - intros t []. exact (counter_frame_methodsem t).
      - intros k k' s s' Hne HG. exact (Gfm_in_Rfm k' k s s' Hne HG).
      - intros k k' op tr ret s p' Hne _ HI Hinv. destruct s as [[σ p] γ].
        destruct HI as (ca & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pinv_inv _ _ _ _ _ _ Hinv) as [-> _].
        split; [apply rt_refl |].
        exists (ca, P), pool, (ca, P), (make_lin_entry (t, h) (ls_inv op) :: pool).
        split; [reflexivity |]. split; [reflexivity |]. split; [intros ls Hl; right; exact Hl | auto].
      - intros k k' op r s p2 Hne HI Hret _. destruct s as [[σ p] γ].
        destruct HI as (ca & P & pool & Hp & _). cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
        destruct k as [t h]. destruct (pret_inv _ _ _ _ _ _ _ Hret) as (pool2 & -> & Hrem).
        split; [apply rt_refl |].
        exists (ca, P), pool, (ca, P), pool2. split; [reflexivity |]. split; [reflexivity |].
        split; [| auto]. intros ls Hl. eapply lin_remove_other_lookup; [exact Hrem | | exact Hl].
        intros Heq. apply Hne. symmetry. exact Heq.
      - intros s (ca & P & pool & Hp & _ & Hwf & _). exists (ca, P), pool. auto.
      - exact counter_frame_init.
    Qed.

    (** Copy-cat inclusion over [EIhl uδ] and over the plain [EI uδ];
        [classic] enters through [RelaxedHoareCompLin.rlhl_complin]
        ([rinv_val]). *)
    Theorem counter_frame_complin_eihl : RCompLin Mc EHL ehσ0 CVFe (0, []).
    Proof. exact (rlhl_complin_ei cδ 0 Ifm Rfm Gfm Mc ehσ0 counter_frame_rlhl2). Qed.

    Theorem counter_frame_complin_ei : RCompLin Mc (RelaxedHoareSpec.EI uδ) (0, []) CVFe (0, []).
    Proof. exact (rlhl_complin_eihl uδ cδ 0 Ifm Rfm Gfm Mc (0, []) counter_frame_rlhl2). Qed.

    (** Complete traces are relaxed-linearizable ([cc_rel_lin]: also
        [eq_rect_eq], from [RelaxedGSim.gsim_rel_lin]). *)
    Corollary counter_frame_rel_lin s :
      MTraces (RelaxedHoareSpec.EI uδ) Mc (0, []) s -> PrefixView.complete s ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) s (RelaxedSig.semi_independent OSig) (RelaxedHoareSpec.seq_legal cδ 0).
    Proof. exact (complin_ei_rel_lin cδ 0 Mc (RelaxedHoareSpec.EI uδ) (0, []) counter_frame_complin_ei s). Qed.

    (** Non-vacuity: the module-derived execution
        [CounterEIhl.inc_ooo_exec_ei] (two overlapping [Inc]s of [t0],
        out-of-order returns) is an execution of the same module over the
        same underlay; through this instance its trace is a copy-cat trace
        and relaxed-linearizable.  [ooo_rel_lin_frame] lifts the execution
        to [EIhl uδ] ([lift_exec]) and applies
        [rlhl_rel_lin_ei_via_cc]. *)
    Corollary ooo_rtrace_frame : RTraces CVFe (0, []) CounterCompLin.ooo_trace.
    Proof. exact (counter_frame_complin_ei _ ooo_trace_ei). Qed.

    Corollary ooo_rel_lin_frame :
      RelaxedTraceLin.rel_lin (@PrefixView.sel OSig) CounterCompLin.ooo_trace (RelaxedSig.semi_independent OSig)
        (RelaxedHoareSpec.seq_legal cδ 0).
    Proof.
      destruct inc_ooo_exec_ei as (c & Hex & Hdone).
      destruct (lift_exec (RelaxedHoareSpec.EI uδ) Mc _ _ _ Hex [] ltac:(split; [constructor | split; [intros k [] | intros k []]]))
        as (u & Hex').
      exact (rlhl_rel_lin_ei_via_cc cδ 0 Ifm Rfm Gfm Mc ehσ0 counter_frame_rlhl2 _ _ Hex' Hdone).
    Qed.
  End CounterEIhlFrame.

  (** [WRCopyCat] (latest-review M-20 (b), M-19; the review's scratch
      session T2 and its I=∅ mirror).  A write [WX] (sets the cell to [1])
      and a read [RX] of one cell, as a sequential specification [rdelta];
      [sw] = [Inv(t1,1,WX) Inv(t1,2,RX) Res(t1,2,RX,0)]: the younger read
      of thread [t1] returns the initial value while the older write of
      the same thread is pending.

      - [si_overtake_rtrace] (T2, adopted verbatim up to names): with
        [semi_independent := o1 <> o2] ([WRSig]), [sw] is a copy-cat trace
        over [EI rdelta]: the read's underlay invocation overtakes the
        pending write's through the frontier ((F2) does not order them).
      - [si_overtake_not_rtrace0] (the mirror): with the empty relation
        ([WRSig0]), the same trace is not a copy-cat trace, for any
        copy-cat execution.  Proof: the identity simulation
        [RelaxedHoareCompLinSpec.cc_gsim] gives a run with [TValid];
        [TValid] puts the write's abstract invocation before the read's
        ((F2) under the empty relation), and on every path of [EI rdelta]
        a read that returns [0] has no write invoked before it
        ([res0_noW]).

      Together they are the copy-cat-level relaxation witness: the
      semi-independence relation alone decides whether the trace is
      accepted.  Not a module-derived witness (latest-review M-19).
      Both signatures are well-formed ([WRSig_wf], [WRSig0_wf]).

      What it is not (latest-review m-35): a memory-model behaviour.  It
      is a mechanism witness for the copy-cat's frontier: a *single* cell
      with [semi_independent := o1 <> o2] on [{WX, RX}], so that a read
      may miss the same thread's pending write to the same location.  No
      memory instance of the paper does this: COH forbids it, and TSO and
      the buffered cell (memory/Cell.v) forward the pending write to the
      read.  The module-derived, memory-shaped counterpart is in
      examples/Relaxed/RelaxedHoareCounterXY.v (RLHL-3b, latest-review
      M-19 item 5): [RelaxedHoareCounterXY.sb_exec] (a complete SB
      execution of Counter_xy over the two-location SC cell with
      semi-independence by location: each read passes its own thread's
      pending FAA on the other location), [sb_si_decides] (the SB trace
      is relaxed-linearizable under the counter relation and not under
      the empty one) and [cxy_discriminates_rlhl2] (the same bodies have
      an RLHL proof under the counter relation and none, for any [I],
      [R], [G], under ∅).  This module stays as the copy-cat-level
      mechanism check. *)

  Module WRCopyCat.
    Import RelaxedTraceLin RelaxedGSim ViewPossibility RelaxedHoareCompLin RelaxedHoareCompLinSpec.

    Inductive WROp := WX | RX.
    Definition wr_ar (o : WROp) : Type := match o with WX => unit | RX => nat end.
    Canonical Structure WREff : Sig.t := {| Sig.op := WROp; Sig.ar := wr_ar |}.

    Definition WRSig : RelaxedSig.t :=
      {| RelaxedSig.effect := WREff; RelaxedSig.handle := nat;
         RelaxedSig.semi_independent := fun o1 o2 => o1 <> o2; RelaxedSig.mode := fun _ => Local |}.

    Definition WRSig0 : RelaxedSig.t :=
      {| RelaxedSig.effect := WREff; RelaxedSig.handle := nat;
         RelaxedSig.semi_independent := fun _ _ => False; RelaxedSig.mode := fun _ => Local |}.

    (** Both signatures are well-formed (latest-review m-35; the review's
        scratch S3). *)
    Lemma WRSig_wf : RelaxedSig.well_formed WRSig.
    Proof. constructor; [intros x H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

    Lemma WRSig0_wf : RelaxedSig.well_formed WRSig0.
    Proof. constructor; [intros x H; exact H | intros _ _ [] | intros _ _ []]. Qed.

    Definition rdelta (n : nat) (o : WROp) : wr_ar o -> nat -> Prop :=
      match o as o0 return wr_ar o0 -> nat -> Prop with WX => fun _ n' => n' = 1 | RX => fun r n' => r = n /\ n' = n end.

    Definition t1 : tid := 1%positive.

    (** *** T2: overtaking under [o1 <> o2] *)

    Definition sw : list (ThreadEvent WRSig) :=
      [Build_ThreadEvent t1 (@InvEv WRSig 1 WX); Build_ThreadEvent t1 (@InvEv WRSig 2 RX);
       Build_ThreadEvent t1 (@ResEv WRSig 2 RX 0)].
    Definition EV : LTS WRSig := @RelaxedHoareSpec.EI WRSig nat rdelta.
    Definition trW := [@cc_inv_ev WRSig t1 1 WX; @cc_res_ev WRSig t1 1 WX tt].
    Definition trR := [@cc_inv_ev WRSig t1 2 RX; @cc_res_ev WRSig t1 2 RX 0].
    Definition k2 : CallKey WRSig := (t1, 2).
    Definition candI : TaggedScheduledEvent WRSig WRSig := Build_TaggedScheduledEvent k2 (@cc_inv_ev WRSig t1 2 RX).
    Definition candR : TaggedScheduledEvent WRSig WRSig := Build_TaggedScheduledEvent k2 (@cc_res_ev WRSig t1 2 RX 0).

    Theorem si_overtake_rtrace : RTraces EV (0, []) sw.
    Proof.
      eexists. eexists. split.
      - eapply tagged_module_execution_cons.
        { apply (@tagged_invoke WRSig WRSig EV idF t1 1 WX (0, []) [] [] [] trW tt).
          - intros [].
          - apply idF_produces.
          - split; [cbn; constructor; [intros [] | constructor] | intros k [<- | []] []]. }
        eapply tagged_module_execution_cons.
        { apply (@tagged_invoke WRSig WRSig EV idF t1 2 RX (0, []) _ _ _ trR 0).
          - intros [H | []]. cbn in H. discriminate H.
          - apply idF_produces.
          - split; [cbn; constructor; [intros [] | constructor] |]. intros k [<- | []] [H | []]. discriminate H. }
        eapply tagged_module_execution_cons.
        { eapply (tagged_underlay EV idF candI).
          - cbn. apply tagged_select_next.
            { right. split; [reflexivity |]. cbn. intros H. apply H. discriminate. }
            apply tagged_select_next.
            { right. split; [reflexivity |]. cbn. intros (op' & ret' & Hres). exact Hres. }
            apply tagged_select_here.
          - cbn. exists 0, 0. split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { eapply (tagged_underlay EV idF candR).
          - cbn. apply tagged_select_next.
            { right. split; [reflexivity |]. cbn. intros H. discriminate H. }
            apply tagged_select_next.
            { right. split; [reflexivity |]. cbn. intros H. exact H. }
            apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (@tagged_return WRSig WRSig EV idF t1 2 RX 0).
          - apply finish_here.
          - cbn. intros [H | [H | []]]; discriminate H. }
        apply tagged_module_execution_refl.
      - reflexivity.
    Qed.

    (** *** The mirror: no overtaking under the empty relation *)

    Definition sw0 : list (ThreadEvent WRSig0) :=
      [Build_ThreadEvent t1 (@InvEv WRSig0 1 WX); Build_ThreadEvent t1 (@InvEv WRSig0 2 RX);
       Build_ThreadEvent t1 (@ResEv WRSig0 2 RX 0)].
    Definition EV0 : LTS WRSig0 := @RelaxedHoareSpec.EI WRSig0 nat rdelta.

    Abbreviation inv0 L := (inv_at (@PrefixView.sel WRSig0) L).
    Abbreviation res0 L := (res_at (@PrefixView.sel WRSig0) L).

    Definition rval (o : Op WRSig0) : option nat :=
      match op_op o as x return wr_ar x -> option nat with RX => fun r => Some r | WX => fun _ => None end (op_ret o).

    (** No write is invoked before position [a]. *)
    Definition NoW (T : list (ThreadEvent WRSig0)) (a : nat) : Prop :=
      forall a' k', a' < a -> ~ inv0 T a' k' WX.

    Lemma NoW_app T L a : a <= length T -> NoW T a -> NoW (T ++ L) a.
    Proof.
      intros Hle Hn a' k' Hlt Ha. apply (Hn a' k' Hlt). apply (RelaxedHoareSpec.inv_app_lt T L); [lia | exact Ha].
    Qed.

    (** Along a path of [EI rdelta] from [(0, [])]: while the cell is [0],
        no write has been invoked; a pending read record of value [0] was
        created with no write invoked before it. *)
    Record WInv (T : list (ThreadEvent WRSig0)) (n : nat) (P : list (Op WRSig0)) : Prop := {
      w_zero : n = 0 -> NoW T (length T);
      w_rec : forall o, In o P -> rval o = Some 0 -> exists a, inv0 T a (op_key o) RX /\ NoW T a
    }.

    Lemma winv_path T v : vf_path EV0 (0, []) T v -> WInv T (fst v) (snd v).
    Proof.
      revert v. induction T as [| ev T IH] using rev_ind; intros v Hp.
      - inversion Hp; subst. constructor; cbn.
        + intros _ a' k' Hlt. lia.
        + intros o [].
      - destruct (RelaxedHoareSpec.vf_path_app_inv _ _ _ _ _ Hp) as (v1 & Hp1 & Hp2).
        inversion Hp2 as [| ? ? v2 ? ? Hs Hp3]; subst. inversion Hp3; subst.
        destruct (IH v1 Hp1) as [Hz Hr]. destruct v1 as [n1 P1]. cbn [fst snd] in Hz, Hr.
        assert (Hlift : forall o, In o P1 -> rval o = Some 0 ->
                  exists a, inv0 (T ++ [ev]) a (op_key o) RX /\ NoW (T ++ [ev]) a).
        { intros o Ho Hv. destruct (Hr o Ho Hv) as (a & Ha & Hn). exists a.
          split; [exact (RelaxedHoareSpec.inv_app_l _ _ _ _ _ Ha) |].
          apply NoW_app; [pose proof (RelaxedHoareSpec.inv_lt _ _ _ _ Ha); lia | exact Hn]. }
        destruct ev as [t [h op | h op r]]; cbn in Hs.
        + destruct Hs as (r & st' & Hd & ->). cbn [fst snd]. destruct op; cbn in Hd.
          * subst st'. constructor.
            -- intros H. discriminate H.
            -- intros o [<- | Ho] Hv; [discriminate Hv | exact (Hlift o Ho Hv)].
          * destruct Hd as (-> & ->). constructor.
            -- intros Hn0 a' k' Hlt Ha. apply RelaxedHoareSpec.inv_snoc_inv in Ha as [Ha | [_ Heq]].
               ++ exact (Hz Hn0 a' k' (RelaxedHoareSpec.inv_lt _ _ _ _ Ha) Ha).
               ++ apply (f_equal (fun e => event_op (te_ev _ e))) in Heq. discriminate Heq.
            -- intros o [<- | Ho] Hv; [| exact (Hlift o Ho Hv)].
               cbn in Hv. injection Hv as Hv. exists (length T).
               split; [exact (RelaxedHoareSpec.inv_snoc_last T t h RX) |].
               apply NoW_app; [lia | exact (Hz Hv)].
        + destruct Hs as (Pa & Pb & HP & ->). cbn [fst snd]. constructor.
          * intros Hn0 a' k' Hlt Ha. pose proof (RelaxedHoareSpec.inv_not_res_ev _ _ _ _ _ _ _ _ Ha) as Ha'.
            exact (Hz Hn0 a' k' (RelaxedHoareSpec.inv_lt _ _ _ _ Ha') Ha').
          * intros o Ho Hv. apply Hlift; [| exact Hv]. rewrite HP. exact (in_remove_in _ _ _ _ Ho).
    Qed.

    (** On a path of [EI rdelta], a read that returns [0] was invoked with
        no write invoked before it. *)
    Lemma res0_noW T v b k :
      vf_path EV0 (0, []) T v -> res0 T b k RX 0 -> exists a, inv0 T a k RX /\ NoW T a.
    Proof.
      intros Hp (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct (nth_error_split T b Hx) as (T1 & T2 & -> & Hlen).
      destruct (RelaxedHoareSpec.vf_path_app_inv _ _ _ _ _ Hp) as (v1 & Hp1 & Hp2).
      inversion Hp2 as [| ? ? v2 ? ? Hs Hp3]; subst.
      destruct (winv_path T1 v1 Hp1) as [_ Hr].
      destruct v1 as [n1 P1]. destruct k as [tk hk]. cbn in Hs, Hr. destruct Hs as (Pa & Pb & HP & _).
      assert (Ho : In (@Build_Op WRSig0 (tk, hk) RX 0) P1) by (rewrite HP; apply in_elt).
      destruct (Hr _ Ho eq_refl) as (a & Ha & Hn).
      exists a. split; [exact (RelaxedHoareSpec.inv_app_l _ _ _ _ _ Ha) |].
      apply NoW_app; [pose proof (RelaxedHoareSpec.inv_lt _ _ _ _ Ha); lia | exact Hn].
    Qed.

    Theorem si_overtake_not_rtrace0 : ~ RTraces EV0 (0, []) sw0.
    Proof.
      intros (evs & c & Hex & Hov).
      destruct (gsim_run EV0 EV0 (@idF WRSig0) (@SCC WRSig0 nat rdelta) (0, []) (0, [])
                  (@cc_gsim WRSig0 nat rdelta) (@cc_init WRSig0 nat rdelta 0) evs c Hex) as (run & v & pool & HI & Hc).
      rewrite Hov in Hc.
      pose proof (ri_valid _ _ _ _ _ _ HI) as HV.
      pose proof (ri_path _ _ _ _ _ _ HI) as HP.
      assert (Hr2 : res0 (conc run) 2 (t1, 2) RX 0) by (rewrite Hc; eexists; split; reflexivity).
      destruct (conc_res_step _ _ _ _ _ Hr2) as (r1 & r2 & Hrun).
      destruct (HV r1 _ r2 Hrun (t1, 2) RX 0 eq_refl) as (b & Hb).
      assert (Hb' : res0 (abs run) b (t1, 2) RX 0)
        by (rewrite Hrun, abs_app; exact (RelaxedHoareSpec.res_app_l _ _ _ _ _ _ Hb)).
      destruct (res0_noW _ _ _ _ HP Hb') as (a & Ha & Hn).
      destruct (abs_inv_step _ _ _ _ Ha) as (u1 & u2 & Hrun2).
      assert (Haeq : a = length (abs u1)).
      { apply (ri_auinv _ _ _ _ _ _ HI a (length (abs u1)) (t1, 2) RX RX Ha). rewrite Hrun2. apply abs_inv_index. }
      destruct (HV u1 _ u2 Hrun2) as ((i & Hi) & Hpo).
      assert (Hcu : conc run = conc u1 ++ conc (@AInv WRSig0 (t1, 2) RX :: u2)) by (rewrite Hrun2, conc_app; reflexivity).
      assert (Hi1 : i = 1).
      { pose proof (RelaxedHoareSpec.inv_app_l _ (conc (@AInv WRSig0 (t1, 2) RX :: u2)) _ _ _ Hi) as Hi'.
        rewrite <- Hcu, Hc in Hi'. destruct Hi' as (x & Hx & Hs). unfold PrefixView.sel in Hs.
        destruct i as [| [| [| i]]]; cbn in Hx;
          [injection Hx as <-; discriminate Hs | reflexivity | injection Hx as <-; discriminate Hs | destruct i; discriminate Hx]. }
      subst i.
      assert (Hw : inv0 (conc u1) 0 (t1, 1) WX).
      { pose proof (RelaxedHoareSpec.inv_lt _ _ _ _ Hi) as Hlt.
        exists (Build_ThreadEvent t1 (@InvEv WRSig0 1 WX)). split; [| reflexivity].
        rewrite <- (nth_error_app1 _ (conc (@AInv WRSig0 (t1, 2) RX :: u2))) by lia. rewrite <- Hcu, Hc. reflexivity. }
      destruct (Hpo _ _ _ _ Hi Hw ltac:(lia) eq_refl (fun H => H)) as (a' & Ha').
      apply (Hn a' (t1, 1)).
      - rewrite Haeq. exact (RelaxedHoareSpec.inv_lt _ _ _ _ Ha').
      - rewrite Hrun2, abs_app. exact (RelaxedHoareSpec.inv_app_l _ _ _ _ _ Ha').
    Qed.

    (** The two together: the semi-independence relation alone decides
        whether the copy-cat accepts [sw]. *)
    Corollary si_decides_overtake : RTraces EV (0, []) sw /\ ~ RTraces EV0 (0, []) sw0.
    Proof. exact (conj si_overtake_rtrace si_overtake_not_rtrace0). Qed.
  End WRCopyCat.

  (** ** M-11 (partial): own-event interference in an [RLHL2Hyps] instance

      [LogRead]: an overlay with a read [LRd] and a write [LWr] of one
      abstract cell ([LLTS]: [LRd] returns the cell, [LWr] sets it to
      [1]; effects at the response).  [LRd] is implemented by a
      non-blocking body over [MemLTS]: a read of [X] and, without waiting
      for it, a log write of [Y]:
      [r <- ?rd(X); y <- ?wr(Y, 1); a <- wait r; wait y; ret a],
      both futures with empty tags.  The read and the log write are
      unordered by the dag ((F2) does not apply: different locations; no
      tag), so the log write's events may fire before or after the read's
      response, which linearizes the call ([GLin]).  [LWr] is a blocking
      write of [X]: other calls write the location [LRd] reads.

      - [lr_derivation]: the slots of the log write carry the edge
        assertion [KAlive] ("the call has not returned": at [ls_inv],
        [ls_lini] or [ls_linr]), which reads the call's own pool entry;
        the unordered own linearization [GLin] changes that entry, and the
        premises [ns_if_old_start] (slot 1 against slot 2) and
        [ns_if_new_in] (the in-edge [1 -> 3] against slot 2) are proved by
        [KAlive_GLin], a genuine own-interference argument.
      - [log_needs_alive]: the natural start assertion of a
        pre-linearization event, [KPh] ("the call has not linearized"),
        is not stable under [GLin]; so the start edge of the log write
        cannot be [KPh].  The read's own start edge is [KPh]; the premise
        for it against [GLin] holds only because the dag orders the read's
        invocation before its response ([~ before], as in
        [tas_derivation]).
      - [log_guar_not_in_rely]: [GLin] is not in the rely [Rl], so
        [newslot_guar_in_rely] does not apply.
      - [log_rlhl2]: every field of [RLHL2Hyps] holds for [Il], [Rl],
        [Gl], [Ml]; the rely does not freeze [X], and [LWr] writes it.

      Limitations: [MemLTS] is not coherent (m-14), so this is a check of
      the logic, not weak-memory evidence.  The log write's own update does
      not use [KAlive]; the assertion is there because a start edge must
      follow from [Pinit] and survive every own event that may fire before
      it, so the check is non-trivial, but the instance does not show an
      own event whose correctness depends on such an edge.  [LLTS] takes
      effect at the response and uses helping; like [PairLTS]
      ([pair_not_hvf]), it does not satisfy [HVF]: the [LLTS] path [Inv(t1,1,LRd)
      Inv(t1,2,LRd) Res(t1,2,LRd,0) Inv(t2,3,LWr) Res(t2,3,LWr)
      Res(t1,1,LRd,1)] is complete and well formed, and [rhb] orders call
      [1] before call [2] before call [3], so call [1] would read [1]
      before the only write (not mechanized).  No load-buffering example
      (M-11 (iii)). *)

  Module LogRead.

    Inductive LOp : Type := LRd | LWr.

    Definition l_ar (o : LOp) : Type := match o with LRd => nat | LWr => unit end.

    Canonical Structure LEffect : Sig.t := {| Sig.op := LOp; Sig.ar := l_ar |}.

    Definition LSig : RelaxedSig.t :=
      {| RelaxedSig.effect := LEffect; RelaxedSig.handle := nat;
         RelaxedSig.semi_independent := fun o1 o2 => o1 <> o2; RelaxedSig.mode := fun _ => Local |}.

    Lemma LSig_wf : RelaxedSig.well_formed LSig.
    Proof. constructor; [intros x H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

    Definition l_step (ev : ThreadEvent LSig) (v v' : nat) : Prop :=
      match te_ev _ ev with
      | InvEv _ _ => v' = v
      | ResEv _ op r =>
          match op return l_ar op -> Prop with
          | LRd => fun r => r = v /\ v' = v
          | LWr => fun _ => v' = 1
          end r
      end.

    Definition LLTS : LTS LSig := {| State := nat; Step := l_step; Error := NoError |}.

    Abbreviation QOk v pool := (@PossOk LSig LLTS v pool).
    Abbreviation QA := (Assn MemLTS LLTS).

    Lemma l_noop t h o v : Step LLTS (Build_ThreadEvent t (@InvEv LSig h o)) v v.
    Proof. reflexivity. Qed.

    Definition rd_body : Prog RlxSig nat :=
      @FutureD RlxSig nat (MRead X) no_deps (fun fx =>
      @FutureD RlxSig nat (MWrite Y 1) no_deps (fun fy =>
      Wait fx (fun (a : nat) => Wait fy (fun _ => Ret a)))).

    Definition Ml : RelaxedModuleImpl RlxSig LSig :=
      fun op t => match op as o return Prog RlxSig (Sig.ar o) with
                  | LRd => rd_body
                  | LWr => @call RlxSig (MWrite X 1)
                  end.

    (** The abstract cell is [X]. *)
    Definition Il : QA := fun s =>
      exists v pool, ps_poss s = QOk v pool /\ v = ps_mem s X /\ lin_pool_well_formed pool.

    (** Rely of [k]: its pool entries are kept (up to helping); memory
        and the abstract cell may change (other calls write [X] and [Y]). *)
    Definition Rl (k : CallKey LSig) : PRel MemLTS LLTS := fun s s' =>
      exists v pool v' pool', ps_poss s = QOk v pool /\ ps_poss s' = QOk v' pool' /\ keeps k pool pool'.

    Definition Gl (k : CallKey LSig) : PRel MemLTS LLTS := fun s s' =>
      exists v pool v' pool', ps_poss s = QOk v pool /\ ps_poss s' = QOk v' pool' /\
        forall k', k' <> k -> keeps k' pool pool'.

    Lemma Gl_in_Rl k k' s s' : k' <> k -> Gl k' s s' -> Rl k s s'.
    Proof.
      intros Hne (v & pool & v' & pool' & Hp & Hp' & Hk). exists v, pool, v', pool'.
      split; [exact Hp |]. split; [exact Hp' |]. apply Hk. intros Heq. apply Hne. symmetry. exact Heq.
    Qed.

    Lemma Rl_keeps k : KeepsRel k (Rl k).
    Proof.
      intros s s' (v & pool & v' & pool' & Hp & Hp' & Hk) v1 pool1 Hp1.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v', pool'. auto.
    Qed.

    Lemma lookup_unique_l (pool : LinPool LSig) k ls1 ls2 :
      lin_pool_well_formed pool -> lin_lookup k ls1 pool -> lin_lookup k ls2 pool -> ls1 = ls2.
    Proof.
      intros Hwf H1 H2.
      assert (Hk : lin_key (make_lin_entry k ls1) = lin_key (make_lin_entry k ls2))
        by (rewrite !lin_key_make_lin_entry; reflexivity).
      pose proof (nodup_map_in_inj lin_key pool _ _ Hwf H1 H2 Hk) as Heq.
      apply (f_equal (lin_state LSig)) in Heq. exact Heq.
    Qed.

    (** The guarantees of the own events. *)
    Definition Gidl : PRel MemLTS LLTS := fun s s' =>
      ps_mem s' = ps_mem s /\ exists v pool, ps_poss s = QOk v pool /\ ps_poss s' = QOk v pool.

    Definition GYl : PRel MemLTS LLTS := fun s s' =>
      ps_mem s' = upd (ps_mem s) Y 1 /\ exists v pool, ps_poss s = QOk v pool /\ ps_poss s' = QOk v pool.

    (** The call's own entry is kept or advanced to [ls_linr]. *)
    Definition advances (k : CallKey LSig) (pool pool' : LinPool LSig) : Prop :=
      forall ls, lin_lookup k ls pool -> lin_lookup k ls pool' \/
        exists o r, (ls = ls_inv o \/ ls = ls_lini o) /\ lin_lookup k (ls_linr o r) pool'.

    (** The linearizing response of the read: memory unchanged, helping of
        the other calls, and [k] at [ls_linr]. *)
    Definition GLin (k : CallKey LSig) : PRel MemLTS LLTS := fun s s' =>
      ps_mem s' = ps_mem s /\
      exists v pool pool', ps_poss s = QOk v pool /\ ps_poss s' = QOk v pool' /\
        (forall k', k' <> k -> keeps k' pool pool') /\ advances k pool pool'.

    Lemma Gidl_in_Gl k s s' : Gidl s s' -> Gl k s s'.
    Proof. intros (_ & v & pool & Hp & Hp'). exists v, pool, v, pool. repeat split; auto. intros; apply keeps_refl. Qed.

    Lemma GYl_in_Gl k s s' : GYl s s' -> Gl k s s'.
    Proof. intros (_ & v & pool & Hp & Hp'). exists v, pool, v, pool. repeat split; auto. intros; apply keeps_refl. Qed.

    Lemma GLin_in_Gl k s s' : GLin k s s' -> Gl k s s'.
    Proof. intros (_ & v & pool & pool' & Hp & Hp' & Hk & _). exists v, pool, v, pool'. auto. Qed.

    Lemma Gidl_stable (P : QA) :
      (forall σ p γ γ', P (σ, p, γ) -> P (σ, p, γ')) -> Stable Il Gidl P.
    Proof.
      intros HP [[σ p] γ] [[σ' p'] γ'] Hs (Hm & v & pool & Hp & Hp') _.
      cbn [ps_mem ps_poss ps_ghost fst snd] in *. subst σ'. rewrite Hp', <- Hp. eapply HP. exact Hs.
    Qed.

    Lemma GYl_stable (P : QA) :
      (forall σ p γ γ', P (σ, p, γ) -> P (upd σ Y 1, p, γ')) -> Stable Il GYl P.
    Proof.
      intros HP [[σ p] γ] [[σ' p'] γ'] Hs (Hm & v & pool & Hp & Hp') _.
      cbn [ps_mem ps_poss ps_ghost fst snd] in *. subst σ'. rewrite Hp', <- Hp. eapply HP. exact Hs.
    Qed.

    (** "The call has not returned". *)
    Definition KAlive (k : CallKey LSig) : QA := fun s =>
      exists v pool, ps_poss s = QOk v pool /\
        (KPhase k LRd pool \/ exists a, lin_lookup k (@ls_linr LSig LRd a) pool).

    Lemma KAlive_Rl k : Stable Il (Rl k) (KAlive k).
    Proof.
      intros s s' (v & pool & Hp & HA) (v1 & pool1 & v1' & pool1' & Hp1 & Hp1' & Hk) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v1', pool1'. split; [exact Hp1' |].
      destruct HA as [Hph | (a & Hl)]; [left; eapply keeps_phase; eauto | right; exists a; eapply keeps_linr; eauto].
    Qed.

    (** The own-interference argument: the linearizing response keeps
        "the call has not returned". *)
    Lemma KAlive_GLin k : Stable Il (GLin k) (KAlive k).
    Proof.
      intros s s' (v & pool & Hp & HA) (_ & v1 & pool1 & pool1' & Hp1 & Hp1' & _ & Hadv) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v, pool1'. split; [exact Hp1' |].
      destruct HA as [[Hl | Hl] | (a & Hl)].
      - destruct (Hadv _ Hl) as [Hl' | (o & r & [Heq | Heq] & Hl')].
        + left. left. exact Hl'.
        + injection Heq as <-. right. exists r. exact Hl'.
        + discriminate Heq.
      - destruct (Hadv _ Hl) as [Hl' | (o & r & [Heq | Heq] & Hl')].
        + left. right. exact Hl'.
        + discriminate Heq.
        + injection Heq as <-. right. exists r. exact Hl'.
      - destruct (Hadv _ Hl) as [Hl' | (o & r & [Heq | Heq] & _)]; [right; exists a; exact Hl' | discriminate Heq | discriminate Heq].
    Qed.

    Lemma KPh_alive k s : KPh (VE := MemLTS) (VF := LLTS) k LRd s -> KAlive k s.
    Proof. intros (v & pool & Hp & Hph). exists v, pool. split; [exact Hp | left; exact Hph]. Qed.

    Lemma KLr_GLin k a : Stable Il (GLin k) (KLr (VE := MemLTS) (VF := LLTS) k LRd a).
    Proof.
      intros s s' (v & pool & Hp & Hl) (_ & v1 & pool1 & pool1' & Hp1 & Hp1' & _ & Hadv) _.
      rewrite Hp in Hp1. injection Hp1 as <- <-. exists v, pool1'. split; [exact Hp1' |].
      destruct (Hadv _ Hl) as [Hl' | (o & r & [Heq | Heq] & _)]; [exact Hl' | discriminate Heq | discriminate Heq].
    Qed.

    Section LogProof.
      Context (t : tid) (h : nat).
      Local Abbreviation kq := (@pair tid (RelaxedSig.handle LSig) t h).
      Abbreviation Pq := (PostInvoke Il kq LRd (fun _ => True)).
      Abbreviation KPhq := (KPh (VE := MemLTS) (VF := LLTS) kq LRd).

      Definition KLrq (a : nat) : QA := KLr (VE := MemLTS) (VF := LLTS) kq LRd a.

      Definition lsl0 hx : Slot MemLTS LLTS :=
        mkSlot (invD_tev (E := RlxSig) (F := LSig) kq empty_store no_deps hx (MRead X))
          KPhq (fun _ _ => True) KPhq Gidl.
      Definition lsl1 H1 hy : Slot MemLTS LLTS :=
        mkSlot (invD_tev (E := RlxSig) (F := LSig) kq H1 no_deps hy (MWrite Y 1))
          (KAlive kq) (fun _ _ => True) (KAlive kq) Gidl.
      Definition lsl2 hx (a : nat) : Slot MemLTS LLTS :=
        mkSlot (res_tev (E := RlxSig) (F := LSig) kq hx (MRead X) a)
          (fun _ => True) (fun d => if Nat.eqb d 0 then KPhq else fun _ => True) (KLrq a) (GLin kq).
      Definition lsl3 hy (u : unit) : Slot MemLTS LLTS :=
        mkSlot (res_tev (E := RlxSig) (F := LSig) kq hy (MWrite Y 1) u)
          (fun _ => True) (fun d => if Nat.eqb d 1 then KAlive kq else fun _ => True) (fun _ => True) GYl.

      Ltac gi := let H := fresh in intros ? ? ? ? H; exact H.

      Ltac lslot_cases n Hn :=
        destruct n as [| [| [| [| n]]]]; cbn in Hn;
        try (destruct n; discriminate); try discriminate; injection Hn as <-;
        cbn [sl_ev sl_start sl_in sl_post sl_guar lsl0 lsl1 lsl2 lsl3].

      Lemma lr_derivation :
        RProvable Il Rl Gl kq Pq
          (fun a Γ H => Close Il Rl Gl kq Pq KLrq a Γ H /\ True) [] empty_store (Ml LRd t).
      Proof.
        assert (Hpinit : Impl Il Pq KPhq) by apply pinit_KPh.
        assert (HKR : Stable Il (Rl kq) KPhq) by apply KPh_stable, Rl_keeps.
        cbn. unfold rd_body.
        (* slot 0: the read of [X] *)
        apply rp_futureD with (sl := lsl0); [intros; reflexivity | |].
        { intros hx _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar lsl0].
          - apply Gidl_in_Gl.
          - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar lsl0].
            intros σ p γ γ' [HK _] HI _ σ' Hst. cbn in Hst. subst σ'.
            exists p. split; [apply rt_refl |]. split; [exact HK |]. split; [exact HI |].
            destruct HI as (v & pool & Hp & _). split; [reflexivity |]. exists v, pool. auto.
          - exact Hpinit.
          - intros d sd _ Hd. destruct d; discriminate.
          - exact HKR.
          - intros d _. apply Stable_true.
          - intros g sg Hg. destruct g; discriminate.
          - intros d g sg _ Hg. destruct g; discriminate.
          - intros y sy Hy. destruct y; discriminate.
          - intros y sy d Hy. destruct y; discriminate. }
        intros hx Hfx. cbv beta.
        (* slot 1: the log write, unordered with the read *)
        apply rp_futureD with (sl := lsl1 (add_pending hx (MRead X) empty_store)); [intros; reflexivity | |].
        { intros hy _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar lsl1].
          - apply Gidl_in_Gl.
          - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar lsl1].
            intros σ p γ γ' [HA _] HI _ σ' Hst. cbn in Hst. subst σ'.
            exists p. split; [apply rt_refl |].
            split; [destruct HA as (v & pool & Hp & HA); exists v, pool; split; [exact Hp | exact HA] |].
            split; [exact HI |].
            destruct HI as (v & pool & Hp & _). split; [reflexivity |]. exists v, pool. auto.
          - intros s HI Hs. apply KPh_alive. exact (Hpinit s HI Hs).
          - intros d sd _ _ s _ _. exact Logic.I.
          - apply KAlive_Rl.
          - intros d _. apply Stable_true.
          - intros g sg Hg. lslot_cases g Hg. apply Gidl_stable.
            intros σ p γ γ' (v & pool & Hp & HA). exists v, pool. auto.
          - intros d g sg _ _ _. apply Stable_true.
          - intros y sy Hy _. lslot_cases y Hy. apply Gidl_stable. gi.
          - intros y sy d Hy _ _. lslot_cases y Hy. apply Stable_true. }
        intros hy Hfy. cbv beta.
        (* slot 2: the response of the read linearizes the call *)
        apply rp_wait_pending with (sl := lsl2 hx); [right; left; reflexivity | intros; reflexivity | |].
        { intros a. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar lsl2].
          - apply GLin_in_Gl.
          - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar lsl2].
            intros σ p γ γ' [_ Hin] HI _ σ' Hst. cbn in Hst. destruct Hst as [Ha ->].
            assert (HK : KPhq (σ, p, γ)).
            { specialize (Hin 0). cbn in Hin. apply Hin.
              econstructor; [cbn; lia | reflexivity | reflexivity | unfold must_precede; cbn; reflexivity]. }
            destruct HK as (v & pool & Hp & Hph). destruct HI as (v1 & pool1 & Hp1 & Hv1 & Hwf).
            cbn [ps_mem ps_poss ps_ghost fst snd] in *.
            rewrite Hp in Hp1. injection Hp1 as <- <-. subst p.
            destruct (linearize_response LLTS kq LRd a v v pool (fun t' h' o' => l_noop t' h' o' _) Hwf Hph
                        (conj (eq_trans Ha (eq_sym Hv1)) eq_refl)) as (pool' & Hps & Hl' & Hwf' & Hkeep).
            exists (QOk v pool'). split; [exact Hps |].
            split; [exists v, pool'; split; [reflexivity | exact Hl'] |].
            split; [exists v, pool'; split; [reflexivity |]; split; [exact Hv1 | exact Hwf'] |].
            split; [reflexivity |]. exists v, pool, pool'. split; [reflexivity |]. split; [reflexivity |].
            split; [exact Hkeep |].
            intros ls Hls. right. exists LRd, a. split; [| exact Hl'].
            destruct Hph as [Hph | Hph]; [left | right]; exact (lookup_unique_l pool kq _ _ Hwf Hls Hph).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| d]; cbn.
            + cbn in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
            + intros s _ _. exact Logic.I.
          - apply Stable_true.
          - intros [| d] _; cbn; [exact HKR | apply Stable_true].
          - intros g sg _. apply Stable_true.
          - intros d g sg _ Hg _. destruct d as [| d]; cbn; [| apply Stable_true].
            lslot_cases g Hg; apply Gidl_stable; gi.
          - (* the linearizing response against the older start edges *)
            intros y sy Hy Hnb. lslot_cases y Hy.
            + (* the read's invocation is ordered before its response *)
              exfalso. apply Hnb. apply before_dprec.
              econstructor; [cbn; lia | reflexivity | reflexivity | unfold must_precede; cbn; reflexivity].
            + (* the log write is unordered: own interference *)
              apply KAlive_GLin.
          - intros y sy d Hy _ _. lslot_cases y Hy; apply Stable_true. }
        intros a H2 Hres2. cbv beta.
        (* slot 3: the response of the log write *)
        apply rp_wait_pending with (sl := lsl3 hy).
        { unfold pending_at. eapply resolve_store_keep_pending; [exact Hres2 | left; reflexivity |].
          intros Heq. cbn in Heq. apply Hfy. rewrite Heq. left. reflexivity. }
        { intros; reflexivity. }
        { intros u. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar lsl3].
          - apply GYl_in_Gl.
          - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar lsl3].
            intros σ p γ γ' _ HI _ σ' Hst. cbn in Hst. subst σ'.
            exists p. split; [apply rt_refl |]. split; [exact Logic.I |].
            destruct HI as (v & pool & Hp & Hv & Hwf). cbn [ps_mem ps_poss ps_ghost fst snd] in *.
            split; [exists v, pool; split; [exact Hp |]; split; [exact Hv | exact Hwf] |].
            split; [reflexivity |]. exists v, pool. auto.
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [| d]]; cbn.
            + intros s _ _. exact Logic.I.
            + cbn in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
            + intros s _ _. exact Logic.I.
          - apply Stable_true.
          - intros [| [| d]] _; cbn; [apply Stable_true | apply KAlive_Rl | apply Stable_true].
          - intros g sg _. apply Stable_true.
          - (* the in-edge [1 -> 3] against the unordered linearizing response *)
            intros d g sg _ Hg _. destruct d as [| [| d]]; cbn; try apply Stable_true.
            lslot_cases g Hg.
            + apply Gidl_stable. intros σ p γ γ' (v & pool & Hp & HA). exists v, pool. auto.
            + apply Gidl_stable. intros σ p γ γ' (v & pool & Hp & HA). exists v, pool. auto.
            + apply KAlive_GLin.
          - intros y sy Hy _. lslot_cases y Hy; apply GYl_stable; first [gi | intros σ p γ γ' (v & pool & Hp & HA); exists v, pool; auto | intros; exact Logic.I].
          - intros y sy d Hy _ _. lslot_cases y Hy; try apply Stable_true.
            destruct (Nat.eqb d 0); [apply GYl_stable; gi | apply Stable_true]. }
        intros u H3 Hres3. cbv beta. apply rp_ret. split; [| exact Logic.I].
        apply close_done with
          (fin := fun d => match d with 2 => KLrq a | _ => fun _ => True end) (fin0 := fun _ => True).
        - eapply (resolve_two hx _ _ hy); [| exact Hres2 | exact Hres3].
          intros Heq. apply Hfy. rewrite Heq. left. reflexivity.
        - constructor.
          + intros d sd Hd. lslot_cases d Hd; cbn; intros s _ Hs; first [exact Logic.I | exact Hs].
          + intros s _ _. exact Logic.I.
          + intros d g sg Hd Hg Hnb. destruct d as [| [| [| d]]]; try apply Stable_true.
            lslot_cases g Hg.
            * apply Gidl_stable. gi.
            * apply Gidl_stable. gi.
            * apply KLr_GLin.
            * apply GYl_stable. gi.
          + intros g sg _. apply Stable_true.
          + intros [| [| [| d]]]; try apply Stable_true. apply KLr_stable, Rl_keeps.
          + apply Stable_true.
          + intros s _ _ Hfin. exact (Hfin 2 _ eq_refl Logic.I).
      Qed.

      (** The natural edge of a pre-linearization event is not stable
          under the unordered own linearization. *)
      Lemma log_needs_alive : ~ Stable Il (GLin kq) KPhq.
      Proof.
        intros Hst.
        set (s := (σ0, QOk 0 [make_lin_entry kq (@ls_inv LSig LRd)], @nil (ScheduledEvent RlxSig LSig))).
        set (s' := (σ0, QOk 0 [make_lin_entry kq (@ls_linr LSig LRd 0)], @nil (ScheduledEvent RlxSig LSig))).
        assert (Hs' : KPhq s').
        { apply (Hst s s').
          - exists 0, [make_lin_entry kq (@ls_inv LSig LRd)]. split; [reflexivity | left; left; reflexivity].
          - split; [reflexivity |]. exists 0, [make_lin_entry kq (@ls_inv LSig LRd)], [make_lin_entry kq (@ls_linr LSig LRd 0)].
            split; [reflexivity |]. split; [reflexivity |]. split.
            + intros k' Hne ls [Hl | []]. exfalso. apply Hne.
              rewrite <- (lin_key_make_lin_entry kq (@ls_inv LSig LRd)), <- (lin_key_make_lin_entry k' ls), Hl. reflexivity.
            + intros ls [Hl | []]. right. exists LRd, 0. split; [left | left; reflexivity].
              apply (f_equal (lin_state LSig)) in Hl. exact (eq_sym Hl).
          - exists 0, [make_lin_entry kq (@ls_linr LSig LRd 0)]. split; [reflexivity |].
            split; [reflexivity |]. constructor; [intros [] | constructor]. }
        destruct Hs' as (v & pool & Hp & [Hl | Hl]); cbn in Hp; injection Hp as <- <-;
          destruct Hl as [Hl | []]; apply (f_equal (lin_state LSig)) in Hl; discriminate Hl.
      Qed.

      Lemma log_guar_not_in_rely : ~ (forall s s', GLin kq s s' -> Rl kq s s').
      Proof.
        intros Hsub.
        set (s := (σ0, QOk 0 [make_lin_entry kq (@ls_inv LSig LRd)], @nil (ScheduledEvent RlxSig LSig))).
        set (s' := (σ0, QOk 0 [make_lin_entry kq (@ls_linr LSig LRd 0)], @nil (ScheduledEvent RlxSig LSig))).
        destruct (Hsub s s') as (v & pool & v' & pool' & Hp & Hp' & Hk).
        - split; [reflexivity |]. exists 0, [make_lin_entry kq (@ls_inv LSig LRd)], [make_lin_entry kq (@ls_linr LSig LRd 0)].
          split; [reflexivity |]. split; [reflexivity |]. split.
          + intros k' Hne ls [Hl | []]. exfalso. apply Hne.
            rewrite <- (lin_key_make_lin_entry kq (@ls_inv LSig LRd)), <- (lin_key_make_lin_entry k' ls), Hl. reflexivity.
          + intros ls [Hl | []]. right. exists LRd, 0. split; [left | left; reflexivity].
            apply (f_equal (lin_state LSig)) in Hl. exact (eq_sym Hl).
        - cbn in Hp, Hp'. injection Hp as <- <-. injection Hp' as <- <-.
          destruct (Hk (@ls_inv LSig LRd) (or_introl eq_refl)) as [[Hl | []] | (o & Heq & [Hl | []])];
            apply (f_equal (lin_state LSig)) in Hl; discriminate Hl.
      Qed.
    End LogProof.

    Lemma Il_invoke k op σ p γ p' γ' :
      Il (σ, p, γ) -> poss_invoke LLTS (fst k) (snd k) op p p' -> Il (σ, p', γ').
    Proof.
      intros HI Hinv. destruct Hinv as [st pool1 pool2 Hins].
      destruct HI as (v & pool & Hp & Hv & Hwf). cbn in Hp. injection Hp as -> <-.
      exists v, pool2. cbn. split; [reflexivity |]. split; [exact Hv | eapply lin_insert_well_formed; eauto].
    Qed.

    Lemma Il_return k op r s p2 :
      Il s -> poss_return LLTS (fst k) (snd k) op r (ps_poss s) p2 -> Il (ps_mem s, p2, ps_ghost s).
    Proof.
      destruct s as [[σ p] γ]. cbn [ps_poss ps_mem ps_ghost fst snd]. intros HI Hret.
      destruct Hret as [st pool1 pool2 Hrem].
      destruct HI as (v & pool & Hp & Hv & Hwf). cbn in Hp. injection Hp as -> <-.
      exists v, pool2. cbn. split; [reflexivity |]. split; [exact Hv | eapply lin_remove_well_formed; eauto].
    Qed.

    Lemma lr_provable t : MethodProvable Il Rl Gl Ml t LRd (fun _ _ => True) (fun h => KLrq t h).
    Proof.
      constructor.
      - intros h [[σ p] γ] (p0 & γ0 & evs & HI0 & Hinv & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. exact (Il_invoke (t, h) LRd σ p0 γ0 p γ HI0 Hinv).
      - intros h r s Hl HI _. destruct s as [[σ p] γ]. destruct Hl as (v & pool & Hp & Hl).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        exists p. split; [apply rt_refl |]. split; [exists v, pool; split; [exact Hp | exact Hl] |].
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hret. exact (Il_return (t, h) LRd r (σ, p, γ) p2 HI Hret).
      - intros h. exact (lr_derivation t h).
    Qed.

    Theorem lr_sound t : MethodSem Il Rl Gl Ml t LRd.
    Proof. eapply method_sound. apply lr_provable. Qed.

    (** [LWr]: a blocking write of [X]. *)
    Section WrProof.
      Context (t : tid).

      Definition Pw (h : nat) : QA := fun s => KPh (VE := MemLTS) (VF := LLTS) (t, h) LWr s /\ Il s.
      Definition Qw (h : nat) (u : unit) : QA := fun s => KLr (VE := MemLTS) (VF := LLTS) (t, h) LWr u s /\ Il s.

      Lemma wr_chain : MethodProvableChain Il Rl Gl Ml t LWr Pw Qw.
      Proof.
        constructor.
        - intros h [[σ p] γ] Hs. pose proof Hs as (p0 & γ0 & evs & HI0 & Hinv & _).
          split; [eapply pinit_KPh; [| exact Hs] |].
          + cbn [ps_poss ps_mem ps_ghost fst snd] in *. exact (Il_invoke (t, h) LWr σ p0 γ0 p γ HI0 Hinv).
          + cbn [ps_poss ps_mem ps_ghost fst snd] in *. exact (Il_invoke (t, h) LWr σ p0 γ0 p γ HI0 Hinv).
        - intros h s [_ HI]. exact HI.
        - intros h. apply Stable_and; [apply KPh_stable, Rl_keeps | apply Stable_I].
        - intros h r s p2 [_ HI] Hret. exact (Il_return (t, h) LWr r s p2 HI Hret).
        - intros h r s [(v & pool & Hp & Hl) _]. exists v, pool. auto.
        - intros h. cbn. unfold call.
          apply cprov_call with (P' := Pw h) (Q' := Qw h).
          + intros s [_ HI]. exact HI.
          + intros r s [_ HI]. exact HI.
          + apply Stable_and; [apply KPh_stable, Rl_keeps | apply Stable_I].
          + intros r. apply Stable_and; [apply KLr_stable, Rl_keeps | apply Stable_I].
          + intros h' σ p γ γ' Hs _ σ' Hst. cbn in Hst. subst σ'.
            exists p. split; [apply rt_refl |]. split; [destruct Hs as [HK HI]; split; [| exact HI] |].
            * destruct HK as (v & pool & Hp & Hph). exists v, pool. auto.
            * destruct Hs as [_ (v & pool & Hp & _)]. exists v, pool, v, pool. repeat split; auto.
              intros; apply keeps_refl.
          + (* the write response: help, then linearize the call *)
            intros h' u σ p γ γ' [(v & pool & Hp & Hph) (v1 & pool1 & Hp1 & Hv1 & Hwf)] _ σ' Hst.
            cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hst. subst σ'.
            rewrite Hp in Hp1. injection Hp1 as <- <-. subst p. destruct u.
            destruct (linearize_response LLTS (t, h) LWr tt v 1 pool
                        (fun t' h' o' => l_noop t' h' o' _) Hwf Hph eq_refl)
              as (pool' & Hps & Hl' & Hwf' & Hkeep).
            exists (QOk 1 pool'). split; [exact Hps |].
            split; [split; [exists 1, pool'; split; [reflexivity | exact Hl'] | exists 1, pool'; split; [reflexivity |]; split; [reflexivity | exact Hwf']] |].
            exists v, pool, 1, pool'. auto.
          + intros r. apply cprov_ret. intros s Hs. exact Hs.
      Qed.
    End WrProof.

    Theorem wr_sound t : MethodSem Il Rl Gl Ml t LWr.
    Proof. eapply chain_sound. apply wr_chain. Qed.

    Lemma Il_init : Il (σ0, QOk 0 [], []).
    Proof. exists 0, []. split; [reflexivity |]. split; [reflexivity | constructor]. Qed.

    (** Every field of [RLHL2Hyps] holds. *)
    Theorem log_rlhl2 : RLHL2Hyps Il Rl Gl Ml σ0 0.
    Proof.
      constructor.
      - intros t [|]; [apply lr_sound | apply wr_sound].
      - intros k k' s s' Hne HG. exact (Gl_in_Rl k' k s s' Hne HG).
      - intros k k' op tr ret [[σ p] γ] p' Hne _ HI Hinv. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        destruct HI as (v & pool & Hp & _). cbn in Hp. subst p.
        inversion Hinv as [st pool1 pool2 Hins]; subst.
        exists v, pool, v, pool2. split; [reflexivity |]. split; [reflexivity |].
        eapply keeps_insert. exact Hins.
      - intros k k' op r [[σ p] γ] p2 Hne HI Hret _. cbn [ps_poss ps_mem ps_ghost fst snd] in *.
        destruct HI as (v & pool & Hp & _). cbn in Hp. subst p.
        inversion Hret as [st pool1 pool2 Hrem]; subst.
        exists v, pool, v, pool2. split; [reflexivity |]. split; [reflexivity |].
        eapply keeps_remove_other; [exact Hrem |]. destruct k. intros Heq. apply Hne. symmetry. exact Heq.
      - intros s (v & pool & Hp & _ & Hwf). exists v, pool. auto.
      - exact Il_init.
    Qed.
  End LogRead.

End RelaxedHoareChecks.
