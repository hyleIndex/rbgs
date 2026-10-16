(** * RLHL, part 3: the syntactic judgement, the method level, the
      derived rules (including a loop rule), and LHL's call rule in the
      blocking fragment.

    ** The judgement

    [RProvable I R G k Pinit K Γ H p] (notation-free) is a coinductive,
    program-order proof outline for the method body [p] of the call
    [k = (t, h)], in the style of [RGILogic.HTripleProvable]:

    - [Γ] is the slot context built so far ([RelaxedHoareDag]), one slot
      per underlay event already passed in program order;
    - [H] is the *lazy* future store: a handle becomes resolved only at
      its first [Wait] (rule [rp_wait_pending]) or at return ([Close]);
    - [K a Γ' H'] is the continuation obligation at [Ret a].

    Rules:
    - [rp_future] / [rp_futureD]: for every fresh handle, a new
      invocation slot whose premises [NewSlotOK] are the invocation's
      update ([ns_update], from the conjunction of the edge assertions
      into the event; the update receives the ghost transition
      [ghost_emit k] of the event, so an invocation may assume that it is
      on the thread frontier, see [RelaxedHoareBase]), the stability of
      the new edge assertions under the rely [R k], and the own-event
      interference checks ([ns_if_*]).  The invocation's lazy tag is
      [resolved_in H] for [Future] and [deps ∩ resolved_in H] for
      [FutureD], i.e. the tag the program semantics computes from the
      lazy store.
    - [rp_wait_pending]: for every response [r] the underlay may give, a
      response slot with its own premises, and the continuation [c r]; this
      is the ∀-response Wait rule.
    - [rp_wait_resolved]: the handle was already resolved by an earlier
      [Wait] on it; the continuation is checked for the resolved value.
    - [rp_ret], [rp_tau].
    - [Close] (at [Ret]): futures never waited for are resolved one by one,
      for every response, with a response slot each ([close_resolve]); then
      the final edges and the summary into the postcondition are given by
      [BarrierWith] ([close_done]).

    There is deliberately no rule for an early, asynchronous response
    ([tagged_resolve]): placing a response before its [Wait] would create
    dependency edges (F3) that executions without the early response do
    not have.  The soundness proof ([RelaxedHoareSound]) handles early
    responses by placing them lazily.

    Derived rules: [rp_conseq], [rp_bind] (through the coinduction
    principle [RProvable_coind], as [RGILogic.v:110]); the loop rule
    [rp_dowhile] for [doWhileR] (latest-review M-14; a loop invariant on
    the slot context and the lazy store); [stable_footprint];
    [EvGuarDefault] / [evupdate_default] (a canonical per-event
    guarantee); and [newslot_guar_in_rely] / [barrier_guar_in_rely], which
    derive the paper's coarser reading of own-event interference (own
    events inside the rely) as a sufficient condition for the pairwise
    premises.  There is no single-response [Wait]-resolved rule: it would
    need the uniqueness of resolved values, i.e. an injectivity of
    [Resolved op] on a dependent argument ([eq_rect_eq]).

    ** Method level

    [MethodProvable I R G M t op Ω Q]: for every overlay handle [h], the
    body [M op t] is derivable from the empty context and store, with
    [Pinit := PostInvoke I (t, h) op (Ω h)] (the state right after the
    overlay invocation, whose ghost already contains the call's own
    invocations) and the obligation [Close (Q h)] at return, together with
    [Ω h (own_invs Γ)]: the own invocations of the path, in program order,
    satisfy the footprint [Ω h].  [mp_PI] (LHL's [PI]) asks that the
    post-invocation state satisfies [I]; [mp_ret] asks that [Q h r], [I]
    and "no pending ghost entry of the call" give [RetCond] (LHL's [Qlin]
    and [Qret]).  [Ω] is prophetic in the same sense as the certificate of
    [MethodSem] (see [RelaxedHoareBase]): [mp_PI] may assume the call's
    own future invocations, which [tagged_invoke] commits; it is checked
    on every path at [Ret].  Methods whose [I] does not read the ghost
    take [Ω := fun _ _ => True].

    ** LHL's call rule in the blocking fragment (A5)

    [CProv P p Q] is the blocking fragment: a judgement whose contexts are
    *barriers* (every earlier event is ordered before the next untagged
    invocation).  [cprov_call] is the derived rule for [call op] followed
    by a continuation, i.e. [Future op (fun f => Wait f c)].  Its premises
    are those of [RGILogic.provable_vis] ([HinvP'], [HinvQ'], [HstableP'],
    [HstableQ'], the invocation update, the ∀-ret response update, the
    continuation), except that:
    - the error premises [Hperror]/[Herror] are dropped (the tagged module
      semantics has no error transition and [GSimRel] excludes
      [PossError]; this is partial correctness);
    - the handle [h] is universally quantified;
    - the updates ([PUpdate]) see the ghost transition of the event.
    No own-interference obligation remains: in the blocking fragment every
    event is ordered before the next one, so all [ns_if_*] premises hold
    by their [~ before] hypotheses ([barrier_all_before]).
    [cprov_ret], [cprov_tau], [cprov_conseq], [cprov_seq] and the loop
    rule [cprov_dowhile] (LHL's [provable_dowhile]) complete the fragment.
    [MethodProvableChain] mirrors the fields of [RGILogic.MethodProvable]
    and implies [MethodProvable] with [Ω := fun _ _ => True]
    ([chain_provable]).

    What this is not (latest-review M-14): there is no translation theorem
    from [RGILogic] derivations (no file of the RLHL development imports
    [RGILogic]), so "RLHL is a conservative extension of LHL" is supported
    only at the level of individual rules: LHL's call rule without its
    error premises, its sequencing and its do-while rule are derivable in
    the blocking fragment.  LHL stability proofs do not transfer verbatim:
    [R k] must contain the guarantees of the other calls of the same
    thread.  Two further differences from [RGILogic.MethodProvable]
    (latest-review M-14, residual):
    - the precondition at the invocation.  LHL's [Pinv] is
      [Ginv t f ⊚ I ==>> P], where [Ginv t f] (Assertion.v) starts from a
      state with [TMap.find t π = None]: the thread is idle.  RLHL's
      [PostInvoke I (t, h) op Ω] (in [mc_Pinv], [mp_PI] and [Pinit]) only
      asks [lin_fresh (t, h)] of the abstract pool ([poss_invoke]), so the
      thread may have other active calls, whose pool and ghost entries
      are present in the state;
    - [ValidRGI] (RGISimulation.v:335, "the rely does not change whether
      thread [t] is idle") is a premise of LHL's [logic_soundness]; it has
      no counterpart in [method_sound].  Its role (other agents do not
      touch the call's own abstract entry) is played by the rely [R k] of
      each instance (e.g. [keeps]) and, for the composition, by the
      [RLHL2Hyps] fields [h_guar_rely], [h_invoke_rely] and
      [h_return_rely] ([RelaxedHoareBase]).  A [ValidRGI] proof does not
      translate into these.

    ** The printed rules and their Coq counterparts (latest-review M-21)

    Documentation only; nothing below is a theorem.  Lines refer to
    ../async-ccal/drafts/relaxed-lin/Appendix/programlogic.tex, numbered
    as in async-ccal commit 4a2db8e1 (review m-67).  (That commit inserts
    a 42-line subsection after :468, so every line cited here from :511
    on was 42 lower in the earlier commit 01484091, which older review
    records use, e.g. Return :563 was :521 and EStep :579 was :537;
    lines up to :468 have the same numbers in both.)  The printed logic
    is not the mechanized one: the Coq rules are those of this file,
    and the paper prints none of them.  The last
    four rows (latest-review m-64) are devices that the RLHL SeqLock
    ([RelaxedHoareSL2Read], [RelaxedHoareSL2Write]) relies on.

    | Paper rule (line)           | Coq counterpart                     | Difference                            |
    |-----------------------------|-------------------------------------|---------------------------------------|
    | derived R, G (:518-526):    | one [R k], one [G k] per overlay    | [R k] covers every other call, also   |
    | R = R[t] ∪ R[π],            | call key [k = (t, h)]               | same-thread calls that are not        |
    | G = G[t] ∩ G[π]             |                                     | semi-independent of [k] (R[π]: only   |
    |                             |                                     | independent ones, App. relaxedlin.tex |
    |                             |                                     | :626)                                 |
    | top-level judgement         | [MethodProvable I R G M t op Ω Q]:  | post [idle(t, π) ∧ I] becomes         |
    | (:534-538)                  | [Pinit := PostInvoke I (t, h) op    | [RetCond] (LHL's Qlin and Qret) under |
    |                             | (Ω h)], [mp_PI], [mp_ret]; premise  | [NoOwn]; footprint [Ω] and the ghost  |
    |                             | [Invoke ∈ G] ↦ [h_invoke_rely]      | are new; every overlay handle [h];    |
    |                             | ([RelaxedHoareBase.RLHL2Hyps])      | [h_invoke_rely] is weaker than        |
    |                             |                                     | [Invoke ∈ G] (RelaxedHoareGSim, 1.)   |
    | Prop. Logic Soundness       | [RelaxedHoareSound.method_sound];   | a global simulation in one step, not  |
    | (:540-552)                  | [RelaxedHoareGSim.rlhl_gsim],       | thread-local; see RelaxedHoareGSim,   |
    |                             | [rlhl_sound];                       | items 1-14                            |
    |                             | [RelaxedHoareCompLin                |                                       |
    |                             | .rlhl_sound_complin]                |                                       |
    | EStep, syntactic (:557-559) | [rp_future] / [rp_futureD] (new     | the printed own-event premise is      |
    |                             | invocation slot, [NewSlotOK]) and   | commented out (:558); Coq checks own  |
    |                             | [rp_wait_pending] (a response slot  | events pairwise ([ns_if_*]); issue    |
    |                             | for every response); derived, in    | and wait are separate rules           |
    |                             | the blocking fragment: [cprov_call] |                                       |
    | Atomic (:561)               | [RelaxedHoareBase.EvUpdate] (in     | one definition for Atomic, semantic   |
    |                             | [ns_update]); [PUpdate] in          | EStep and Poss; it receives the ghost |
    |                             | [cprov_call]'s premises, converted  | transition [ghost_emit]               |
    |                             | to [EvUpdate] by [newslot_inv]      |                                       |
    |                             | (invocation) and [newslot_res]      |                                       |
    |                             | (response)                          |                                       |
    | Return (:563)               | [rp_ret] with [Close]               | [Close] (unprinted) resolves the      |
    |                             | ([close_resolve], [close_done]),    | futures never waited for; stability   |
    |                             | then [mp_ret]                       | under [R k], not [R[t]]               |
    | Iter (:565)                 | [rp_dowhile] ([doWhileR]);          | a do-while over [Prog], not [C^*]     |
    |                             | [cprov_dowhile]                     | over Imp; invariant on the slot       |
    |                             |                                     | context and the lazy store            |
    | Choice (:567)               | none                                | [Prog] has no choice; nondeterminism  |
    |                             |                                     | only through responses and handles    |
    | Seq (:569)                  | [rp_bind] (derived through          | none beyond Imp vs [Prog]             |
    |                             | [RProvable_coind]); [cprov_seq]     |                                       |
    | EStep, semantic (:579)      | the [Step VE ev σ σ'] premise of    | the underlay is an LTS [VE], not      |
    |                             | [EvUpdate]                          | membership in ν_E; no "σ'.s ∈ ⟦M⟧"    |
    |                             |                                     | restriction (cyan): unreachable       |
    |                             |                                     | states are covered too                |
    | Poss (:581)                 | [poss_steps VF p p'] (existential   | one possibility, not a set            |
    |                             | in [EvUpdate] and [RetCond])        |                                       |
    | ReturnCommit (:583)         | last clause of [RetCond] (every     | none beyond the single possibility    |
    |                             | [poss_return] keeps [I]); the       |                                       |
    |                             | return clause of [GSimRel]          |                                       |
    | consequence (:585)          | [rp_conseq], [cprov_conseq], [Impl] | none                                  |
    | Invoke_t(f), idle(t, π),    | [poss_invoke] / [PostInvoke];       | no idle predicate                     |
    | [P] (:592-599)              | [NoOwn] with [RetCond]; none        |                                       |
    | (unprinted)                 | [rp_wait_resolved], [rp_tau],       | Coq-only rules and premises           |
    |                             | [FutureD] tags, [Close], [ns_if_*], |                                       |
    |                             | [Ω], the ghost,                     |                                       |
    |                             | [newslot_guar_in_rely],             |                                       |
    |                             | [barrier_guar_in_rely]              |                                       |
    | loops over a step machine   | [RelaxedHoareRun.rp_run],           | Coq-only derived rule (by             |
    | (unprinted; cf. Iter :565)  | [run_method_provable]; used by      | [RProvable_coind]) for a body         |
    |                             | [write_provable]                    | [run next hs st]: a machine invariant |
    |                             | (RelaxedHoareSL2Write) and          | on the machine state, the calls       |
    |                             | [read_provable_v]                   | issued, the slot context and the lazy |
    |                             | (RelaxedHoareSL2Read)               | store, re-established by every step   |
    |                             |                                     | ([RunStepOK]); Iter (:565) maps only  |
    |                             |                                     | to [rp_dowhile]                       |
    | proof state s (:528-532, s  | [RelaxedHoareLog.Log VE],           | restores only the underlay projection |
    | at :530); EStep, semantic   | [EIhlv δ := Log (EIhl δ)]: the      | of the paper's s; the overlay         |
    | (:579)                      | state also logs the underlay events | invocations of s (:530) and the       |
    |                             | ([loglift], [rlhl_complin_eihlv]);  | reachability clause σ'.s ∈ ⟦M⟧ (cyan) |
    |                             | the SeqLock derivations are over    | of :579 are not represented; a        |
    |                             | [EIhlv δS]                          | presentation of the underlay          |
    |                             |                                     | justified by the trace equivalence    |
    |                             |                                     | [loglift], not a change of the rules  |
    | Return (:563): post         | [Qrd k i r] := [Qsl k (fR i) r] ∨   | a postcondition disjunct with no      |
    | idle(t, π) ∧ I              | [¬ NoOwn k γ] (RelaxedHoareSL2Inv)  | paper counterpart: the call still     |
    |                             | (lifted: [QrdV]); [qrd_ret], by     | owns a ghost entry (a path that       |
    |                             | [retcond_or_owned]                  | returns before its footprint is used  |
    |                             | (RelaxedHoareReady)                 | up; B-6); [bw_sum] may conclude it    |
    |                             |                                     | before [NoOwn] is in scope, and       |
    |                             |                                     | [mp_ret] refutes it by [NoOwn]        |
    | single possibility vs       | the SeqLock read's linearization    | App. relaxedlin.tex:520 and :628 say  |
    | possibility sets (App.      | point at its last [rmb], last read  | single possibilities are not          |
    | relaxedlin.tex:520, :628;   | off the ghost ([isl_read_lp] of     | generally sufficient, especially when |
    | Poss :581)                  | RelaxedHoareSL2Inv, [rd_rmb_update] | linearization points are              |
    |                             | of RelaxedHoareSL2InvLog); one      | future-dependent. This LP is          |
    |                             | possibility                         | future-dependent: the ghost stores no |
    |                             |                                     | response values, but its remaining    |
    |                             |                                     | invocations, committed at invocation, |
    |                             |                                     | determine the outcome of the call's   |
    |                             |                                     | own future validation (the SeqLock    |
    |                             |                                     | read LP is such a future-dependent    |
    |                             |                                     | LP). Sound by run-to-completion       |
    |                             |                                     | (impl.tex:141, a method returns only  |
    |                             |                                     | after all its underlay calls          |
    |                             |                                     | completed; impl.tex:172, Inv picks    |
    |                             |                                     | (r, t:u) in ⟦M^f⟧_t at invocation;    |
    |                             |                                     | m-33, m-65)                           |

    Further differences between the printed and the mechanized logic
    (complementing RelaxedHoareGSim, items 1-14):
    - Imp vs [Prog].  The paper verifies Imp commands compiled to the
      future language (:69-93), whose dependency tags come from a
      dependency policy (data, address, control; :97-200, with the
      environment δ and the control set κ).  The Coq rules are over
      [RelaxedLang.Prog] ([Future], [FutureD], [Wait], [Ret], [Tau]); the
      tags of [FutureD] are written by hand, and no compilation from Imp
      and no policy is mechanized.
    - Proof state.  The paper's proof configuration is [(s, possibility
      set)], with [s] the whole concrete trace (:528-532).  Coq's is
      [(σ, p, γ)]: a state of the underlay LTS [VE], one possibility [p],
      and the ghost [γ] of pending underlay invocations
      ([RelaxedHoareBase.PState]).  With the history presentation
      [VE := RelaxedHoareLog.EIhlv δ], [σ] also carries the underlay
      projection of [s], not its overlay invocations (see the table).
    - The two readings of own-thread interference (latest-review m-43).
      The printed [R = R[t] ∪ R[π]] (:521-522) uses R[π], which
      App. relaxedlin.tex:626 defines as "the rely condition that needs
      to be followed when the *same thread* is executing some other
      independent operation"; implex.tex:3 says the rely admits "the
      verifying thread's own independent futures"; intro.tex:99 speaks
      of "pending, independent operations within the verifying thread".
      Each of these sentences fits either of two readings, both with a
      Coq counterpart; attributing :626 to the first one is one reading
      of two, not the paper's stated intent:
      + Inter-call (one reading of relaxedlin.tex:626): other pending
        operations of the same thread interfere with the call under
        verification.  Coq: [R k] contains [G k'] for every other call
        [k'], same-thread calls included ([RLHL2Hyps.h_guar_rely]; call
        keys are [(t, h)]).  This is necessarily larger than an R[π]
        restricted to independent operations: the module semantics runs
        an older non-independent same-thread call's events while [k] is
        pending.  [RelaxedModuleSemantics.tagged_invoke] checks only
        [call_fresh], so [k] may be invoked while an older same-thread
        call [k'] that is not semi-independent of [k] is pending (in
        Counter_xy: [k] a [Get CX] while [k'], an [Inc CX] of the same
        thread, is pending); F2 ([must_precede], which reads the
        underlay relation) then forces [k']'s [Faa CX] before [k]'s
        [Rd CX], so a [G k'] step happens while [k] is pending and the
        stability of [k]'s assertions must absorb it.  It is
        exercised at nonempty semi-independence by
        [RelaxedHoareCounterXY.cxy_rlhl2], whose module-derived
        executions [sb_exec] (a read crossing its own thread's pending
        FAA) and [lb_exec] (an FAA crossing its own thread's pending
        read) have same-thread pending calls that interfere and are
        crossed, and by [cxyb_rlhl2], whose module-derived SB execution
        is [sb_exec_gen] at [si_mb] ([sb_mtraces_b]; LB is not a trace
        of that module, [lb_not_trace_b]); readiness by
        [RelaxedHoareInherit.emit_ready_SI].
      + Intra-call: the own underlay events of one call interfere with
        each other.  The live prose for this reading is
        programlogic.tex:308 ("treat the events a method emits out of
        program order as interference by the thread's own independent
        operations"); its closest printed counterpart is the
        commented-out EStep premise (programlogic.tex:558), which
        quantifies over every [e' ∈ M^O_E] with [I_E(e', e)], so the
        identification is itself an interpretation.  Coq checks own
        events pairwise ([ns_if_*], [bw_if]), never by putting them into
        [R k].  The closest Coq counterparts of a coarse "own events in
        the rely" reading, [newslot_guar_in_rely] and
        [barrier_guar_in_rely] below, derive the [ns_if_*] premises from "the guarantee of
        every own event is in [R k]", so every edge assertion must be
        stable under *all* own events, including the ones the dependency
        dag orders; the pairwise premises are finer than both.  They are
        exercised with genuine premises only as frame facts
        ([RelaxedHoareCounterXY.CounterXYZ.cxyz_rlhl2]: ownership and an
        unchanged possibility; latest-review m-45).
    - intro.tex:99 ("We build RLHL on LHL, extending its reasoning to
      pending, independent operations within the verifying thread").
      On the inter-call reading above (one of the two), the "pending,
      independent operations within the verifying thread" are the other
      same-thread calls ([h_guar_rely]; [cxy_rlhl2] with [sb_exec]);
      readiness for an older pending same-thread call is
      [invocation_ready], discharged by [emit_ready_SI] for overlay
      relations inherited from the underlay.  "On LHL": see the M-14
      paragraph above (rule-level only; no file imports [RGILogic]).
    - intro.tex:106 ("We develop RLHL and a view-based proof interface
      on top of LHL ... one layered verification").  "On top of LHL":
      as for :99 (M-14).  "One layered verification" (LatchSet and the
      write-snapshot object): not mechanized for RLHL.  There is no RLHL
      layering theorem (absorption, linking and [mtraces_mono] are
      missing, latest-review M-22), and LatchSet occurs only on the
      window route: the window-composition tables
      (examples/Relaxed/WindowTable.v, WindowComposition.v) and the
      latch's racy layer in examples/Relaxed/IntervalWindow.v (Part 2,
      interval inheritance under the default table); none of these uses
      RLHL.
    - [cprov_ret] (latest-review m-41).  It asks only [Entails P (Q a)].
      LHL's [RGILogic.provable_ret] also asks [Q a ==>> I] ([HinvQ]),
      the stability of [Q a] under the rely ([HstableQ]), and an error
      disjunct ([Hperror]); none of these has a counterpart in
      [cprov_ret].  In RLHL the invariant is re-established by every
      event update ([EvUpdate]) and assumed, not proved, at return
      ([mp_ret]); stability is asked of the final edges summarised into
      [Q a] ([bw_R], [bw_R0] of [BarrierWith]), not of [Q a] itself; the
      error premise has no counterpart (partial correctness).
    - Claims about completeness and load buffering (latest-review m-41,
      m-46).  implex.tex:3: "RLHL is complete with respect to relaxed
      linearizability, and can specify patterns such as load buffering";
      relatedwork.tex:32: "Load-buffering patterns are expressible".
      Completeness is not mechanized (see the next item).  For load
      buffering there is one RLHL-level datum, on a renaming over the SC
      cell (examples/Relaxed/RelaxedHoareCounterXY.v):
      [lb_exec] is a module-derived, complete LB execution of Counter_xy
      with semi-independence by location; it is accepted under the
      overlay relation [by_counter] through the instance [cxy_rlhl2]
      ([lb_rel_lin]), it is not relaxed-linearizable under the relation
      [si_cb] (matching the readiness of 2Counter.tex:41/:53) nor under
      ∅ ([lb_not_rel_lin_gen]), so no [I], [R], [G] verify the same
      bodies against [si_cb] over the by-location underlay [EM]
      ([cxy_mixed_no_rlhl2]).  Over the narrower underlay relation
      [si_mb] the same body text does verify against [si_cb]
      ([cxyb_rlhl2]), and LB is not a trace of that module
      ([lb_not_trace_b]).  No LB example over a relaxed memory from
      [memory/], and none with a non-renaming body.
    - relatedwork.tex:32 ("sound and complete with respect to the
      criterion").  Only soundness is mechanized ([rlhl_sound],
      [rlhl_sound_complin]).  Completeness is not, and with one
      possibility it is not expected: a same-thread call whose
      linearization depends on the future needs prophecy (latest-review
      m-36).
    - relatedwork.tex:34 (the mechanization is "developed directly on top
      of the Rocq development of [lhl], reusing its SC proof architecture
      and isolating the new timestamp reasoning in a small adapter").
      This describes VLHL (examples/View/*TSO.v, [ViewLift]), not RLHL: no
      [RelaxedHoare*.v] file imports [RGILogic] or [Assertion], and RLHL's
      soundness proof ([RelaxedHoareSound], [RelaxedHoareGSim.RSim]) is
      new (latest-review M-14). *)

Require Import Stdlib.Lists.List.
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

Import ListNotations.


Module RelaxedHoare.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.

  (** ** A do-while loop over the future language

      [doWhileR b body] runs [body] and repeats while [b] holds of its
      result ([Lang.doWhile] for the future language). *)

  Section Loops.
    Context {E : RelaxedSig.t} {A : Type} (b : A -> bool) (body : Prog E A).

    CoFixpoint loop_aux (p : Prog E A) : Prog E A :=
      match p with
      | Future op k => Future op (fun f => loop_aux (k f))
      | FutureD op deps k => FutureD op deps (fun f => loop_aux (k f))
      | Wait f k => Wait f (fun x => loop_aux (k x))
      | Ret r => if b r then Tau (loop_aux body) else Ret r
      | Tau p' => Tau (loop_aux p')
      end.

    Definition doWhileR : Prog E A := loop_aux body.

    Lemma loop_aux_future op k : loop_aux (Future op k) = Future op (fun f => loop_aux (k f)).
    Proof. rewrite PPid at 1. unfold PP, loop_aux. reflexivity. Qed.

    Lemma loop_aux_futureD op deps k :
      loop_aux (FutureD op deps k) = FutureD op deps (fun f => loop_aux (k f)).
    Proof. rewrite PPid at 1. unfold PP, loop_aux. reflexivity. Qed.

    Lemma loop_aux_wait {X} (f : FutureRef E X) k :
      loop_aux (Wait f k) = Wait f (fun x => loop_aux (k x)).
    Proof. rewrite PPid at 1. unfold PP, loop_aux. reflexivity. Qed.

    Lemma loop_aux_ret r : loop_aux (Ret r) = if b r then Tau (loop_aux body) else Ret r.
    Proof. rewrite PPid at 1. unfold PP, loop_aux. destruct (b r); reflexivity. Qed.

    Lemma loop_aux_tau p : loop_aux (Tau p) = Tau (loop_aux p).
    Proof. rewrite PPid at 1. unfold PP, loop_aux. reflexivity. Qed.
  End Loops.

  Section Judgement.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
    Context (k : CallKey F) (Pinit : Assn VE VF).

    Local Abbreviation SlotT := (Slot VE VF).
    Local Abbreviation NewOK := (NewSlotOK I R G k Pinit).

    Definition inv_tev (H : FutureStore E) (h : RelaxedSig.handle E)
        (op : Sig.op (RelaxedSig.effect E)) : TaggedEvent E :=
      Build_TaggedEvent (Build_ThreadEvent (fst k) (InvEv h op)) (resolved_in H).

    Definition invD_tev (H : FutureStore E) (deps : RelaxedSig.handle E -> Prop)
        (h : RelaxedSig.handle E) (op : Sig.op (RelaxedSig.effect E)) : TaggedEvent E :=
      Build_TaggedEvent (Build_ThreadEvent (fst k) (InvEv h op))
        (fun q => deps q /\ resolved_in H q).

    Definition res_tev (h : RelaxedSig.handle E) (op : Sig.op (RelaxedSig.effect E))
        (r : Sig.ar op) : TaggedEvent E :=
      Build_TaggedEvent (Build_ThreadEvent (fst k) (ResEv h op r)) no_deps.

    CoInductive RProvable {A : Type} (K : A -> list SlotT -> FutureStore E -> Prop) :
        list SlotT -> FutureStore E -> Prog E A -> Prop :=
    | rp_ret Γ H r :
        K r Γ H ->
        RProvable K Γ H (Ret r)
    | rp_tau Γ H p :
        RProvable K Γ H p ->
        RProvable K Γ H (Tau p)
    | rp_future Γ H op c (sl : RelaxedSig.handle E -> SlotT) :
        (forall h, sl_ev (sl h) = inv_tev H h op) ->
        (forall h, handle_fresh h H -> NewOK Γ (sl h)) ->
        (forall h, handle_fresh h H ->
           RProvable K (Γ ++ [sl h]) (add_pending h op H) (c (MkFutureRef op h))) ->
        RProvable K Γ H (Future op c)
    | rp_futureD Γ H op deps c (sl : RelaxedSig.handle E -> SlotT) :
        (forall h, sl_ev (sl h) = invD_tev H deps h op) ->
        (forall h, handle_fresh h H -> NewOK Γ (sl h)) ->
        (forall h, handle_fresh h H ->
           RProvable K (Γ ++ [sl h]) (add_pending h op H) (c (MkFutureRef op h))) ->
        RProvable K Γ H (FutureD op deps c)
    | rp_wait_resolved Γ H op h (c : Sig.ar op -> Prog E A) :
        (exists r0, resolved_at h op r0 H) ->
        (forall r, resolved_at h op r H -> RProvable K Γ H (c r)) ->
        RProvable K Γ H (Wait (MkFutureRef op h) c)
    | rp_wait_pending Γ H op h (c : Sig.ar op -> Prog E A) (sl : Sig.ar op -> SlotT) :
        pending_at h op H ->
        (forall r, sl_ev (sl r) = res_tev h op r) ->
        (forall r, NewOK Γ (sl r)) ->
        (forall r H', resolve_store h op r H H' -> RProvable K (Γ ++ [sl r]) H' (c r)) ->
        RProvable K Γ H (Wait (MkFutureRef op h) c).

    (** Unwaited futures are resolved at return, for every response. *)
    Inductive Close {A : Type} (Q : A -> Assn VE VF) (a : A) :
        list SlotT -> FutureStore E -> Prop :=
    | close_done Γ H fin fin0 :
        all_resolved H ->
        BarrierWith I R k Pinit Γ fin fin0 (Q a) ->
        Close Q a Γ H
    | close_resolve Γ H h op (sl : Sig.ar op -> SlotT) :
        pending_at h op H ->
        (forall r, sl_ev (sl r) = res_tev h op r) ->
        (forall r, NewOK Γ (sl r)) ->
        (forall r H', resolve_store h op r H H' -> Close Q a (Γ ++ [sl r]) H') ->
        Close Q a Γ H.

    (** *** One-step unfolding (small-inversion view) *)

    Definition rp_view_gen {A : Type}
        (X : list SlotT -> FutureStore E -> Prog E A -> Prop)
        (K : A -> list SlotT -> FutureStore E -> Prop)
        (Γ : list SlotT) (H : FutureStore E) (p : Prog E A) : Prop :=
      match p with
      | Ret r => K r Γ H
      | Tau p' => X Γ H p'
      | Future op c =>
          exists sl : RelaxedSig.handle E -> SlotT,
            (forall h, sl_ev (sl h) = inv_tev H h op) /\
            (forall h, handle_fresh h H -> NewOK Γ (sl h)) /\
            (forall h, handle_fresh h H ->
               X (Γ ++ [sl h]) (add_pending h op H) (c (MkFutureRef op h)))
      | FutureD op deps c =>
          exists sl : RelaxedSig.handle E -> SlotT,
            (forall h, sl_ev (sl h) = invD_tev H deps h op) /\
            (forall h, handle_fresh h H -> NewOK Γ (sl h)) /\
            (forall h, handle_fresh h H ->
               X (Γ ++ [sl h]) (add_pending h op H) (c (MkFutureRef op h)))
      | Wait f c =>
          match f in FutureRef _ B return (B -> Prog E A) -> Prop with
          | MkFutureRef op h => fun c =>
              ((exists r0, resolved_at h op r0 H) /\
               (forall r, resolved_at h op r H -> X Γ H (c r))) \/
              (exists sl : Sig.ar op -> SlotT,
                 pending_at h op H /\
                 (forall r, sl_ev (sl r) = res_tev h op r) /\
                 (forall r, NewOK Γ (sl r)) /\
                 (forall r H', resolve_store h op r H H' -> X (Γ ++ [sl r]) H' (c r)))
          end c
      end.

    Lemma rp_unfold {A} (K : A -> list SlotT -> FutureStore E -> Prop) Γ H p :
      RProvable K Γ H p -> rp_view_gen (RProvable K) K Γ H p.
    Proof.
      intros D. destruct D; cbn.
      - assumption.
      - assumption.
      - exists sl. auto.
      - exists sl. auto.
      - left. auto.
      - right. exists sl. auto.
    Qed.

    Lemma rp_view_mono {A} (X Y : list SlotT -> FutureStore E -> Prog E A -> Prop)
        (K K' : A -> list SlotT -> FutureStore E -> Prop) Γ H p :
      (forall Γ H p, X Γ H p -> Y Γ H p) ->
      (forall a Γ H, K a Γ H -> K' a Γ H) ->
      rp_view_gen X K Γ H p -> rp_view_gen Y K' Γ H p.
    Proof.
      intros HXY HK. destruct p as [op c | op deps c | B f c | r | p']; cbn.
      - intros (sl & H1 & H2 & H3). exists sl. auto.
      - intros (sl & H1 & H2 & H3). exists sl. auto.
      - destruct f as [op h]. cbn.
        intros [[H1 H2] | (sl & H1 & H2 & H3 & H4)]; [left | right]; [split; auto |].
        exists sl. auto 10.
      - apply HK.
      - apply HXY.
    Qed.

    (** The coinduction principle (as [RGILogic.HTripleProvable_invariant_sound]). *)
    Lemma RProvable_coind {A} (K : A -> list SlotT -> FutureStore E -> Prop)
        (X : list SlotT -> FutureStore E -> Prog E A -> Prop) :
      (forall Γ H p, X Γ H p -> rp_view_gen X K Γ H p) ->
      forall Γ H p, X Γ H p -> RProvable K Γ H p.
    Proof.
      intros HX. cofix CIH. intros Γ H p Hx.
      pose proof (HX Γ H p Hx) as V. clear Hx.
      destruct p as [op c | op deps c | B f c | r | p']; cbn in V.
      - destruct V as (sl & H1 & H2 & H3).
        apply (rp_future K Γ H op c sl H1 H2). intros h Hf. apply CIH. apply H3. exact Hf.
      - destruct V as (sl & H1 & H2 & H3).
        apply (rp_futureD K Γ H op deps c sl H1 H2). intros h Hf. apply CIH. apply H3. exact Hf.
      - revert c V. destruct f as [op h]. intros c V. cbn in V.
        destruct V as [[H1 H2] | (sl & H1 & H2 & H3 & H4)].
        + apply (rp_wait_resolved K Γ H op h c H1). intros r Hr. apply CIH. apply H2. exact Hr.
        + apply (rp_wait_pending K Γ H op h c sl H1 H2 H3).
          intros r H' Hres. apply CIH. apply H4. exact Hres.
      - apply rp_ret. exact V.
      - apply rp_tau. apply CIH. exact V.
    Qed.

    (** *** Derived rules *)

    Lemma rp_conseq {A} (K K' : A -> list SlotT -> FutureStore E -> Prop) Γ H p :
      RProvable K Γ H p ->
      (forall a Γ H, K a Γ H -> K' a Γ H) ->
      RProvable K' Γ H p.
    Proof.
      intros D HK. revert Γ H p D.
      apply (RProvable_coind K' (RProvable K)).
      intros Γ H p D. eapply rp_view_mono; [| exact HK | apply rp_unfold; exact D].
      auto.
    Qed.

    Lemma rp_bind {A B} (K' : A -> list SlotT -> FutureStore E -> Prop)
        (K : B -> list SlotT -> FutureStore E -> Prop) (c : A -> Prog E B) Γ H p :
      RProvable K' Γ H p ->
      (forall a Γ' H', K' a Γ' H' -> RProvable K Γ' H' (c a)) ->
      RProvable K Γ H (bindProg p c).
    Proof.
      intros D Hc.
      set (X := fun Γ H q => (exists p, q = bindProg p c /\ RProvable K' Γ H p) \/
                             RProvable K Γ H q).
      apply (RProvable_coind K X); [| left; exists p; auto].
      clear Γ H p D. intros Γ H q [(p & -> & D) | D].
      - pose proof (rp_unfold K' Γ H p D) as V. clear D.
        destruct p as [op c' | op deps c' | B' f c' | r | p']; cbn in V.
        + rewrite bindFutureUnfold. cbn. destruct V as (sl & H1 & H2 & H3).
          exists sl. split; [exact H1 |]. split; [exact H2 |].
          intros h Hf. left. eexists. split; [reflexivity | auto].
        + rewrite bindFutureDUnfold. cbn. destruct V as (sl & H1 & H2 & H3).
          exists sl. split; [exact H1 |]. split; [exact H2 |].
          intros h Hf. left. eexists. split; [reflexivity | auto].
        + rewrite bindWaitUnfold. revert c' V. destruct f as [op h]. intros c' V. cbn in V |- *.
          destruct V as [[H1 H2] | (sl & H1 & H2 & H3 & H4)].
          * left. split; [exact H1 |]. intros r Hr. left. eexists. split; [reflexivity | auto].
          * right. exists sl. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
            intros r H' Hres. left. eexists. split; [reflexivity | eauto].
        + rewrite bindRetUnfold.
          eapply rp_view_mono; [| | apply rp_unfold; apply Hc; exact V].
          * intros. right. assumption.
          * auto.
        + rewrite bindTauUnfold. cbn. left. eexists. split; [reflexivity | exact V].
      - eapply rp_view_mono; [| | apply rp_unfold; exact D].
        + intros. right. assumption.
        + auto.
    Qed.

    (** The loop rule (latest-review M-14): a loop invariant on the slot
        context and the lazy store, re-established by every iteration that
        continues. *)
    Lemma rp_dowhile {A} (b : A -> bool) (body : Prog E A)
        (Inv : list SlotT -> FutureStore E -> Prop) (K : A -> list SlotT -> FutureStore E -> Prop) :
      (forall Γ H, Inv Γ H ->
         RProvable (fun a Γ' H' => (b a = true /\ Inv Γ' H') \/ (b a = false /\ K a Γ' H')) Γ H body) ->
      forall Γ H, Inv Γ H -> RProvable K Γ H (doWhileR b body).
    Proof.
      intros Hbody.
      set (K' := fun a Γ' H' => (b a = true /\ Inv Γ' H') \/ (b a = false /\ K a Γ' H')).
      set (X := fun Γ H q => exists p, q = loop_aux b body p /\ RProvable K' Γ H p).
      intros Γ H HI. apply (RProvable_coind K X); [| exists body; split; [reflexivity | apply Hbody; exact HI]].
      clear Γ H HI. intros Γ H q (p & -> & D).
      pose proof (rp_unfold K' Γ H p D) as V. clear D.
      destruct p as [op c | op deps c | B f c | r | p']; cbn in V.
      - rewrite loop_aux_future. cbn. destruct V as (sl & H1 & H2 & H3).
        exists sl. split; [exact H1 |]. split; [exact H2 |].
        intros h Hf. exists (c (MkFutureRef op h)). split; [reflexivity | auto].
      - rewrite loop_aux_futureD. cbn. destruct V as (sl & H1 & H2 & H3).
        exists sl. split; [exact H1 |]. split; [exact H2 |].
        intros h Hf. exists (c (MkFutureRef op h)). split; [reflexivity | auto].
      - rewrite loop_aux_wait. revert c V. destruct f as [op h]. intros c V. cbn in V |- *.
        destruct V as [[H1 H2] | (sl & H1 & H2 & H3 & H4)].
        + left. split; [exact H1 |]. intros r Hr. exists (c r). auto.
        + right. exists sl. split; [exact H1 |]. split; [exact H2 |]. split; [exact H3 |].
          intros r H' Hres. exists (c r). eauto.
      - rewrite loop_aux_ret. destruct V as [[Hb HInv] | [Hb HK]]; rewrite Hb; cbn.
        + exists body. split; [reflexivity | apply Hbody; exact HInv].
        + exact HK.
      - rewrite loop_aux_tau. cbn. exists p'. split; [reflexivity | exact V].
    Qed.

    (** Interference with a footprint: a relation that preserves a
        projection preserves every assertion that only reads it. *)
    Lemma stable_footprint {T : Type} (proj : PState VE VF -> T) (g : PRel VE VF)
        (P : T -> Prop) :
      (forall s s', g s s' -> proj s' = proj s) ->
      Stable I g (fun s => P (proj s)).
    Proof. intros Hg s s' Hp Hss' _. rewrite (Hg s s' Hss'). exact Hp. Qed.

    (** A canonical per-event guarantee: the steps that the event's update
        itself performs. *)
    Definition EvGuarDefault (pre post : Assn VE VF) (ev : ThreadEvent E) : PRel VE VF :=
      fun s s' => pre s /\ I s /\ ghost_emit k ev (ps_ghost s) (ps_ghost s') /\
                  Step VE ev (ps_mem s) (ps_mem s') /\
                  poss_steps VF (ps_poss s) (ps_poss s') /\ G k s s' /\ post s' /\ I s'.

    Lemma evupdate_default (pre post : Assn VE VF) ev :
      EvUpdate I (G k) k ev pre post ->
      EvUpdate I (EvGuarDefault pre post ev) k ev pre post.
    Proof.
      intros Hup σ p γ γ' Hpre HI Hge σ' Hstep.
      destruct (Hup σ p γ γ' Hpre HI Hge σ' Hstep) as (p' & Hps & Hpost & HI' & HG).
      exists p'. repeat split; assumption.
    Qed.

    (** *** Own events inside the rely (a derived, coarser rule)

        Appendix/programlogic.tex:302--308 describes the treatment of a
        call's own out-of-order events as "interference by the thread's own
        independent operations".  The judgement does not put own events into
        [R k]; it checks them pairwise ([ns_if_*]).  The two lemmas below
        derive the paper's coarser reading as a sufficient condition: if the
        guarantee of every event of the call is contained in [R k], then all
        own-interference premises follow from stability under [R k].  The
        price is that every edge assertion must then be stable under the
        call's own events, including the ones the dependency dag orders. *)

    Lemma newslot_guar_in_rely Γ sl :
      (forall g sg, nth_error Γ g = Some sg -> forall s s', sl_guar sg s s' -> R k s s') ->
      (forall y sy, nth_error Γ y = Some sy ->
         Stable I (R k) (sl_start sy) /\ forall d, Stable I (R k) (sl_in sy d)) ->
      (forall s s', sl_guar sl s s' -> R k s s') ->
      (forall s s', sl_guar sl s s' -> G k s s') ->
      EvUpdate I (sl_guar sl) k (untag (sl_ev sl)) (pre_of (Γ ++ [sl]) (length Γ) sl) (sl_post sl) ->
      Impl I Pinit (sl_start sl) ->
      (forall d sd, dprec (evs (Γ ++ [sl])) d (length Γ) -> nth_error Γ d = Some sd ->
         Impl I (sl_post sd) (sl_in sl d)) ->
      Stable I (R k) (sl_start sl) -> (forall d, Stable I (R k) (sl_in sl d)) ->
      NewOK Γ sl.
    Proof.
      intros HgR HstOld HslR HslG Hup Hest Hin HstS HstI.
      constructor; auto.
      - intros g sg Hg. eapply Stable_mono; [apply (HgR g sg Hg) | exact HstS].
      - intros d g sg _ Hg _. eapply Stable_mono; [apply (HgR g sg Hg) | apply HstI].
      - intros y sy Hy _. eapply Stable_mono; [exact HslR | apply (HstOld y sy Hy)].
      - intros y sy d Hy _ _. eapply Stable_mono; [exact HslR | apply (HstOld y sy Hy)].
    Qed.

    Lemma barrier_guar_in_rely Γ fin fin0 (P : Assn VE VF) :
      (forall g sg, nth_error Γ g = Some sg -> forall s s', sl_guar sg s s' -> R k s s') ->
      (forall d sd, nth_error Γ d = Some sd -> Impl I (sl_post sd) (fin d)) ->
      Impl I Pinit fin0 ->
      (forall d, Stable I (R k) (fin d)) -> Stable I (R k) fin0 ->
      (forall s, I s -> fin0 s ->
         (forall d sd, nth_error Γ d = Some sd -> is_response (untag (sl_ev sd)) -> fin d s) ->
         P s) ->
      BarrierWith I R k Pinit Γ fin fin0 P.
    Proof.
      intros HgR Hest Hest0 HR HR0 Hsum. constructor; auto.
      - intros d g sg _ Hg _. eapply Stable_mono; [apply (HgR g sg Hg) | apply HR].
      - intros g sg Hg. eapply Stable_mono; [apply (HgR g sg Hg) | exact HR0].
    Qed.

    (** ** A5: the blocking fragment and the conservative extension *)

    Definition Entails (P Q : Assn VE VF) : Prop := forall s, P s -> Q s.

    (** [Assertion.PUpdate] (LHL's [G ⊨ P [ev]⭆ Q]), with the ghost
        transition of the event ([ghost_emit k ev]): an invocation may
        assume that it is on the thread frontier. *)
    Definition PUpdate (g : PRel VE VF) (ev : ThreadEvent E) (P Q : Assn VE VF) : Prop :=
      forall σ p γ γ', P (σ, p, γ) -> ghost_emit k ev γ γ' -> forall σ', Step VE ev σ σ' ->
        exists p', poss_steps VF p p' /\ Q (σ', p', γ') /\ g (σ, p, γ) (σ', p', γ').

    Definition Barrier (Γ : list SlotT) (H : FutureStore E) (P : Assn VE VF) : Prop :=
      all_resolved H /\ exists fin fin0, BarrierWith I R k Pinit Γ fin fin0 P.

    Definition BlockWF (Γ : list SlotT) (H : FutureStore E) : Prop :=
      (forall d sd q, nth_error Γ d = Some sd -> is_response_of q (untag (sl_ev sd)) ->
         resolved_in H q) /\
      (forall d sd q op, nth_error Γ d = Some sd -> te_ev E (untag (sl_ev sd)) = InvEv q op ->
         exists j sj, d < j /\ nth_error Γ j = Some sj /\ is_response_of q (untag (sl_ev sj))).

    Definition CProv {A} (P : Assn VE VF) (p : Prog E A) (Q : A -> Assn VE VF) : Prop :=
      forall Γ H, Barrier Γ H P -> BlockWF Γ H ->
        RProvable (fun a Γ' H' => Barrier Γ' H' (Q a) /\ BlockWF Γ' H') Γ H p.

    Lemma dprec_snoc_last (L : list (TaggedEvent E)) x d a :
      nth_error L d = Some a -> must_precede a x -> dprec (L ++ [x]) d (length L).
    Proof.
      intros Ha Hm. econstructor; [eapply nth_error_lt; eauto | | | exact Hm].
      - apply nth_error_snoc_old. exact Ha.
      - apply nth_error_snoc_last.
    Qed.

    Lemma resp_dprec_inv Γ H h op j sj q :
      BlockWF Γ H -> nth_error Γ j = Some sj -> is_response_of q (untag (sl_ev sj)) ->
      dprec (evs Γ ++ [inv_tev H h op]) j (length Γ).
    Proof.
      intros [Hres _] Hj Hq. pose proof (Hres j sj q Hj Hq) as Hrq.
      rewrite <- (length_evs Γ). apply (dprec_snoc_last _ _ _ (sl_ev sj)).
      - unfold evs. rewrite nth_error_map, Hj. reflexivity.
      - unfold must_precede. unfold is_response_of in Hq.
        destruct (te_ev E (untag (sl_ev sj))) as [q' op' | q' op' r']; [destruct Hq |].
        cbn. subst q'. exact Hrq.
    Qed.

    (** In a blocking context, every earlier event is ordered before the
        next untagged invocation. *)
    Lemma barrier_all_before Γ H h op :
      BlockWF Γ H -> forall d, d < length Γ ->
      before (evs Γ ++ [inv_tev H h op]) d (length Γ).
    Proof.
      intros Hwf d Hd. pose proof Hwf as [_ Hinv].
      destruct (nth_error Γ d) as [sd |] eqn:Hsd; [| apply nth_error_None in Hsd; lia].
      destruct (te_ev E (untag (sl_ev sd))) as [q op' | q op' r'] eqn:Hev.
      - destruct (Hinv d sd q op' Hsd Hev) as (j & sj & Hdj & Hj & Hq).
        eapply before_step; [| exact (resp_dprec_inv Γ H h op j sj q Hwf Hj Hq)].
        apply before_dprec. econstructor; [exact Hdj | | |].
        + rewrite nth_error_app1 by (rewrite length_evs; lia).
          unfold evs. rewrite nth_error_map, Hsd. reflexivity.
        + rewrite nth_error_app1 by (rewrite length_evs; eapply nth_error_lt; eauto).
          unfold evs. rewrite nth_error_map, Hj. reflexivity.
        + unfold must_precede. rewrite Hev. unfold is_response_of in Hq.
          destruct (te_ev E (untag (sl_ev sj))); [destruct Hq | symmetry; exact Hq].
      - apply before_dprec. apply (resp_dprec_inv Γ H h op d sd q Hwf Hsd).
        unfold is_response_of. rewrite Hev. reflexivity.
    Qed.

    Lemma is_response_of_handle (ev : ThreadEvent E) :
      is_response ev -> is_response_of (event_handle (te_ev E ev)) ev.
    Proof.
      unfold is_response, is_response_of. destruct (te_ev E ev); [intros [] | reflexivity].
    Qed.

    Lemma before_snoc_lift (L : list (TaggedEvent E)) x a b :
      b < length L -> before L a b -> before (L ++ [x]) a b.
    Proof. intros Hb Hab. apply (proj2 (before_app_iff L [x] a b Hb)). exact Hab. Qed.

    Lemma barrier_weaken Γ fin fin0 (P P' : Assn VE VF) :
      BarrierWith I R k Pinit Γ fin fin0 P -> Entails P P' ->
      BarrierWith I R k Pinit Γ fin fin0 P'.
    Proof.
      intros [Hest Hest0 Hif Hif0 HR HR0 Hsum] HP.
      constructor; [exact Hest | exact Hest0 | exact Hif | exact Hif0 | exact HR | exact HR0 |].
      intros s HI H0 Hd. apply HP. apply Hsum; assumption.
    Qed.

    Lemma resolve_fresh_all_resolved (H H' : FutureStore E) h op r :
      all_resolved H -> resolve_store h op r (add_pending h op H) H' -> all_resolved H'.
    Proof.
      intros Hall Hres. unfold add_pending in Hres.
      inversion Hres as [tail Htail | h' cell H0 H0' Hneq Hres0]; subst.
      - constructor; [cbn; trivial | exact Hall].
      - exfalso. apply Hneq. reflexivity.
    Qed.

    Lemma resolved_in_resolve_mono (H H' : FutureStore E) h op r q :
      resolve_store h op r H H' -> resolved_in H q -> resolved_in H' q.
    Proof.
      intros Hres. induction Hres as [tail | h' cell H0 H0' Hneq Hres IH];
        intros (op' & r' & Hin).
      - destruct Hin as [Heq | Hin]; [discriminate | exists op', r'; right; exact Hin].
      - destruct Hin as [Heq | Hin]; [exists op', r'; left; exact Heq |].
        destruct (IH (ex_intro _ op' (ex_intro _ r' Hin))) as (op'' & r'' & Hin'').
        exists op'', r''. right. exact Hin''.
    Qed.

    (** The invocation slot of [call op] in a barrier context. *)
    Lemma newslot_inv Γ H fin fin0 (P P' : Assn VE VF) op h :
      BarrierWith I R k Pinit Γ fin fin0 P -> BlockWF Γ H -> Entails P' I ->
      PUpdate (G k) (Build_ThreadEvent (fst k) (InvEv h op)) P P' ->
      NewOK Γ (mkSlot (inv_tev H h op) fin0 fin P' (G k)).
    Proof.
      intros Hbw Hwf HinvP' Hup.
      pose proof Hbw as [Hest Hest0 Hif Hif0 HR HR0 Hsum].
      assert (Hevs : evs (Γ ++ [mkSlot (inv_tev H h op) fin0 fin P' (G k)]) =
                     evs Γ ++ [inv_tev H h op]) by (rewrite evs_app; reflexivity).
      pose proof (barrier_all_before Γ H h op Hwf) as Hall.
      constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar]; rewrite ?Hevs.
      - auto.
      - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar]. rewrite Hevs.
        intros σ p γ γ' [Hst Hin] HI Hge σ' Hstep.
        assert (HP : P (σ, p, γ)).
        { apply Hsum; [exact HI | exact Hst |].
          intros d sd Hd Hr. apply Hin.
          apply (resp_dprec_inv Γ H h op d sd (event_handle (te_ev E (untag (sl_ev sd)))) Hwf Hd).
          apply is_response_of_handle. exact Hr. }
        destruct (Hup σ p γ γ' HP Hge σ' Hstep) as (p' & Hps & HP' & HG).
        exists p'. split; [exact Hps |]. split; [exact HP' |]. split; [apply HinvP'; exact HP' | exact HG].
      - exact Hest0.
      - intros d sd _ Hd. eapply Hest; eauto.
      - exact HR0.
      - intros d _. apply HR.
      - intros g sg Hg. eapply Hif0; eauto.
      - intros d g sg Hd Hg Hnb. eapply Hif; eauto.
        apply dprec_lt in Hd. exact Hd.
      - intros y sy Hy Hnb. exfalso. apply Hnb. apply Hall. eapply nth_error_lt; eauto.
      - intros y sy d Hy Hnb. exfalso. apply Hnb. apply Hall. eapply nth_error_lt; eauto.
    Qed.

    Definition res_slot (n : nat) (h : RelaxedSig.handle E) op (r : Sig.ar op)
        (P' Q'r : Assn VE VF) : SlotT :=
      mkSlot (res_tev h op r) (fun _ => True)
        (fun d => if Nat.eqb d n then P' else fun _ => True) Q'r (G k).

    Section AfterCall.
      Context (Γ : list SlotT) (H : FutureStore E) (Hwf : BlockWF Γ H).
      Context (h : RelaxedSig.handle E) (op : Sig.op (RelaxedSig.effect E)).
      Context (slv : SlotT) (Hslv : sl_ev slv = inv_tev H h op).

      Let n := length Γ.
      Let L1 := evs Γ ++ [inv_tev H h op].

      Let Hevs1 : evs (Γ ++ [slv]) = L1.
      Proof. unfold L1. rewrite evs_app. cbn. rewrite Hslv. reflexivity. Qed.

      Let Hlen1 : length (Γ ++ [slv]) = S n.
      Proof. unfold n. rewrite length_app. cbn. lia. Qed.

      Let HlenL1 : length L1 = S n.
      Proof. unfold L1, n. rewrite length_app, length_evs. cbn. lia. Qed.

      Lemma all_before_L1 y : y < n -> before L1 y n.
      Proof. intros Hy. apply barrier_all_before; assumption. Qed.

      Lemma inv_res_dprec r : dprec (L1 ++ [res_tev h op r]) n (S n).
      Proof.
        rewrite <- HlenL1. apply (dprec_snoc_last L1 _ n (inv_tev H h op)).
        - unfold L1. rewrite nth_error_app2 by (rewrite length_evs; unfold n; lia).
          rewrite length_evs. fold n. rewrite Nat.sub_diag. reflexivity.
        - unfold must_precede. cbn. reflexivity.
      Qed.

      Lemma all_before_res r y : y <= n -> before (L1 ++ [res_tev h op r]) y (S n).
      Proof.
        intros Hy. eapply before_step; [| apply inv_res_dprec].
        destruct (Nat.eq_dec y n) as [-> | Hne]; [apply before_refl |].
        apply before_snoc_lift; [lia |]. apply all_before_L1. lia.
      Qed.

      Context (P' : Assn VE VF) (Hslv_post : sl_post slv = P').

      Lemma newslot_res (Q'r : Assn VE VF) r :
        Entails Q'r I -> Stable I (R k) P' ->
        PUpdate (G k) (Build_ThreadEvent (fst k) (ResEv h op r)) P' Q'r ->
        NewOK (Γ ++ [slv]) (res_slot n h op r P' Q'r).
      Proof.
        intros HinvQ HstP Hup.
        assert (Hevs2 : evs ((Γ ++ [slv]) ++ [res_slot n h op r P' Q'r]) = L1 ++ [res_tev h op r])
          by (rewrite evs_app, Hevs1; reflexivity).
        unfold res_slot in Hevs2 |- *. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar].
        - auto.
        - unfold EvUpdate, pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar].
          intros σ p γ γ' [_ Hin] HI Hge σ' Hstep.
          assert (HP : P' (σ, p, γ)).
          { specialize (Hin n). rewrite Nat.eqb_refl in Hin. apply Hin.
            rewrite Hevs2, Hlen1. apply inv_res_dprec. }
          destruct (Hup σ p γ γ' HP Hge σ' Hstep) as (p' & Hps & HQ & HG).
          exists p'. split; [exact Hps |]. split; [exact HQ |]. split; [apply HinvQ; exact HQ | exact HG].
        - intros s _ _. constructor.
        - intros d sd Hd Hsd. destruct (Nat.eqb_spec d n) as [-> | Hne]; [| intros; constructor].
          assert (Hsd' : sd = slv).
          { unfold n in Hsd. rewrite nth_error_app2 in Hsd by lia. rewrite Nat.sub_diag in Hsd.
            cbn in Hsd. congruence. }
          subst sd. rewrite Hslv_post. intros s _ Hs. exact Hs.
        - apply Stable_true.
        - intros d _. destruct (Nat.eqb d n); [exact HstP | apply Stable_true].
        - intros g sg _. apply Stable_true.
        - intros d g sg Hd Hg Hnb. destruct (Nat.eqb_spec d n) as [-> | Hne]; [| apply Stable_true].
          exfalso. apply Hnb. rewrite Hevs1.
          apply nth_error_lt in Hg. rewrite Hlen1 in Hg.
          destruct (Nat.eq_dec g n) as [-> | Hgn]; [apply before_refl | apply all_before_L1; lia].
        - intros y sy Hy Hnb. exfalso. apply Hnb. rewrite Hevs2, Hlen1.
          apply all_before_res. apply nth_error_lt in Hy. rewrite Hlen1 in Hy. lia.
        - intros y sy d Hy Hnb. exfalso. apply Hnb. rewrite Hevs2, Hlen1.
          apply all_before_res. apply nth_error_lt in Hy. rewrite Hlen1 in Hy. lia.
      Qed.

      Lemma barrier_after_res (Q'r : Assn VE VF) r :
        Stable I (R k) Q'r ->
        BarrierWith I R k Pinit ((Γ ++ [slv]) ++ [res_slot n h op r P' Q'r])
          (fun d => if Nat.eqb d (S n) then Q'r else fun _ => True) (fun _ => True) Q'r.
      Proof.
        intros HstQ.
        assert (Hevs2 : evs ((Γ ++ [slv]) ++ [res_slot n h op r P' Q'r]) = L1 ++ [res_tev h op r])
          by (rewrite evs_app, Hevs1; reflexivity).
        assert (Hlast : nth_error ((Γ ++ [slv]) ++ [res_slot n h op r P' Q'r]) (S n) =
                        Some (res_slot n h op r P' Q'r))
          by (rewrite <- Hlen1; apply nth_error_snoc_last).
        assert (Hlen2 : length ((Γ ++ [slv]) ++ [res_slot n h op r P' Q'r]) = S (S n))
          by (rewrite length_app, Hlen1; cbn; lia).
        constructor.
        - intros d sd Hd. destruct (Nat.eqb_spec d (S n)) as [-> | Hne]; [| intros; constructor].
          rewrite Hlast in Hd. injection Hd as <-. cbn. intros s _ Hs. exact Hs.
        - intros s _ _. constructor.
        - intros d g sg Hd Hg Hnb. destruct (Nat.eqb_spec d (S n)) as [-> | Hne]; [| apply Stable_true].
          exfalso. apply Hnb. rewrite Hevs2.
          apply nth_error_lt in Hg. rewrite Hlen2 in Hg.
          destruct (Nat.eq_dec g (S n)) as [-> | Hgn]; [apply before_refl | apply all_before_res; lia].
        - intros g sg _. apply Stable_true.
        - intros d. destruct (Nat.eqb d (S n)); [exact HstQ | apply Stable_true].
        - apply Stable_true.
        - intros s HI _ Hfin. specialize (Hfin (S n) _ Hlast). rewrite Nat.eqb_refl in Hfin.
          apply Hfin. cbn. exact Logic.I.
      Qed.

      Lemma blockwf_after_res (Q'r : Assn VE VF) r H' :
        resolve_store h op r (add_pending h op H) H' ->
        BlockWF ((Γ ++ [slv]) ++ [res_slot n h op r P' Q'r]) H'.
      Proof.
        intros Hres. destruct Hwf as [Hwf1 Hwf2]. split.
        - intros d sd q Hd Hq.
          destruct (nth_error_snoc_cases _ _ _ _ Hd) as [[Hlt Hd'] | [-> ->]].
          + destruct (nth_error_snoc_cases _ _ _ _ Hd') as [[Hlt' Hd''] | [-> ->]].
            * eapply resolved_in_resolve_mono; [exact Hres |].
              destruct (Hwf1 d sd q Hd'' Hq) as (op' & r' & Hin). exists op', r'. right. exact Hin.
            * exfalso. rewrite Hslv in Hq. exact Hq.
          + cbn in Hq. subst q. exists op, r. eapply resolve_store_resolved. exact Hres.
        - intros d sd q op' Hd Hq.
          destruct (nth_error_snoc_cases _ _ _ _ Hd) as [[Hlt Hd'] | [-> ->]].
          + destruct (nth_error_snoc_cases _ _ _ _ Hd') as [[Hlt' Hd''] | [-> ->]].
            * destruct (Hwf2 d sd q op' Hd'' Hq) as (j & sj & Hdj & Hj & Hrj).
              exists j, sj. split; [exact Hdj |]. split; [| exact Hrj].
              apply nth_error_snoc_old. apply nth_error_snoc_old. exact Hj.
            * rewrite Hslv in Hq. cbn in Hq. injection Hq as <- <-.
              exists (S n), (res_slot n h op r P' Q'r). split; [rewrite Hlen1 in Hlt; lia |].
              split; [rewrite <- Hlen1; apply nth_error_snoc_last | reflexivity].
          + cbn in Hq. discriminate.
      Qed.
    End AfterCall.

    (** *** The derived rule for a blocking call (A5) *)

    Lemma cprov_call {A} (P P' : Assn VE VF) op (Q' : Sig.ar op -> Assn VE VF)
        (c : Sig.ar op -> Prog E A) (Q : A -> Assn VE VF) :
      Entails P' I ->                                                   (* HinvP' *)
      (forall r, Entails (Q' r) I) ->                                   (* HinvQ' *)
      Stable I (R k) P' ->                                              (* HstableP' *)
      (forall r, Stable I (R k) (Q' r)) ->                              (* HstableQ' *)
      (forall h, PUpdate (G k) (Build_ThreadEvent (fst k) (InvEv h op)) P P') ->
      (forall h r, PUpdate (G k) (Build_ThreadEvent (fst k) (ResEv h op r)) P' (Q' r)) ->
      (forall r, CProv (Q' r) (c r) Q) ->
      CProv P (Future op (fun f => Wait f c)) Q.
    Proof.
      intros HinvP' HinvQ' HstP' HstQ' Hinv Hres Hcont Γ H [Hall (fin & fin0 & Hbw)] Hwf.
      apply (rp_future _ Γ H op (fun f => Wait f c) (fun h => mkSlot (inv_tev H h op) fin0 fin P' (G k))).
      - intros h. reflexivity.
      - intros h Hf. eapply newslot_inv; eauto.
      - intros h Hf. cbv beta.
        set (slv := mkSlot (inv_tev H h op) fin0 fin P' (G k)).
        apply (rp_wait_pending _ (Γ ++ [slv]) (add_pending h op H) op h c
                 (fun r => res_slot (length Γ) h op r P' (Q' r))).
        + left. reflexivity.
        + intros r. reflexivity.
        + intros r. apply (newslot_res Γ H Hwf h op slv eq_refl P' eq_refl);
            [apply HinvQ' | exact HstP' | apply Hres].
        + intros r H' Hres'. apply Hcont.
          * split; [eapply resolve_fresh_all_resolved; eauto |].
            eexists _, _. apply (barrier_after_res Γ H Hwf h op slv eq_refl P'). apply HstQ'.
          * exact (blockwf_after_res Γ H Hwf h op slv eq_refl P' (Q' r) r H' Hres').
    Qed.

    Lemma cprov_ret {A} (P : Assn VE VF) (a : A) (Q : A -> Assn VE VF) :
      Entails P (Q a) -> CProv P (Ret a) Q.
    Proof.
      intros HPQ Γ H [Hall (fin & fin0 & Hbw)] Hwf. apply rp_ret. split; [| exact Hwf].
      split; [exact Hall |]. exists fin, fin0. eapply barrier_weaken; eauto.
    Qed.

    Lemma cprov_tau {A} P (p : Prog E A) Q : CProv P p Q -> CProv P (Tau p) Q.
    Proof. intros Hp Γ H HB Hwf. apply rp_tau. apply Hp; assumption. Qed.

    Lemma cprov_conseq {A} (P P0 : Assn VE VF) (p : Prog E A) (Q0 Q : A -> Assn VE VF) :
      Entails P P0 -> CProv P0 p Q0 -> (forall a, Entails (Q0 a) (Q a)) -> CProv P p Q.
    Proof.
      intros HP Hp HQ Γ H [Hall (fin & fin0 & Hbw)] Hwf.
      eapply rp_conseq.
      - apply Hp; [| exact Hwf]. split; [exact Hall |]. exists fin, fin0. eapply barrier_weaken; eauto.
      - intros a Γ' H' [[Hall' (fin' & fin0' & Hbw')] Hwf']. split; [| exact Hwf'].
        split; [exact Hall' |]. exists fin', fin0'. eapply barrier_weaken; eauto.
    Qed.

    Lemma cprov_seq {A B} (P : Assn VE VF) (p : Prog E A) (Q' : A -> Assn VE VF)
        (c : A -> Prog E B) (Q : B -> Assn VE VF) :
      CProv P p Q' -> (forall a, CProv (Q' a) (c a) Q) -> CProv P (bindProg p c) Q.
    Proof.
      intros Hp Hc Γ H HB Hwf. eapply rp_bind; [apply Hp; eauto |].
      intros a Γ' H' [HB' Hwf']. apply Hc; assumption.
    Qed.

    (** LHL's do-while rule ([RGILogic.provable_dowhile]) in the blocking
        fragment. *)
    Lemma cprov_dowhile {A} (b : A -> bool) (body : Prog E A) (Iloop : Assn VE VF)
        (Q : A -> Assn VE VF) :
      CProv Iloop body Q ->
      (forall a, b a = true -> Entails (Q a) Iloop) ->
      CProv Iloop (doWhileR b body) (fun a s => Q a s /\ b a = false).
    Proof.
      intros Hbody Hcont Γ H HB Hwf.
      apply (rp_dowhile b body (fun Γ H => Barrier Γ H Iloop /\ BlockWF Γ H)); [| split; assumption].
      intros Γ' H' [HB' Hwf']. eapply rp_conseq; [apply Hbody; assumption |].
      intros a Γ'' H'' [[Hall (fin & fin0 & Hbw)] Hwf'']. destruct (b a) eqn:Hb.
      - left. split; [reflexivity |]. split; [| exact Hwf'']. split; [exact Hall |].
        exists fin, fin0. eapply barrier_weaken; [exact Hbw | apply Hcont; exact Hb].
      - right. split; [reflexivity |]. split; [| exact Hwf'']. split; [exact Hall |].
        exists fin, fin0. eapply barrier_weaken; [exact Hbw |]. intros s Hs. split; [exact Hs | reflexivity].
    Qed.

  End Judgement.

  (** ** Method level *)

  Section Method.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
    Context (M : RelaxedModuleImpl E F).

    (** [Ω h]: the footprint of the call's own invocations (in program
        order); it is checked on every path at [Ret] ([own_invs]) and
        assumed by [mp_PI] and by [Pinit] (see [PostInvoke]). *)
    Record MethodProvable (t : tid) (op : Sig.op (RelaxedSig.effect F))
        (Ω : RelaxedSig.handle F -> list (ThreadEvent E) -> Prop)
        (Q : RelaxedSig.handle F -> Sig.ar op -> Assn VE VF) : Prop := {
      mp_PI : forall h s, PostInvoke I (t, h) op (Ω h) s -> I s;
      mp_ret : forall h r s, Q h r s -> I s -> NoOwn (t, h) (ps_ghost s) -> RetCond I G (t, h) op r s;
      mp_triple : forall h,
        RProvable I R G (t, h) (PostInvoke I (t, h) op (Ω h))
          (fun a Γ H => Close I R G (t, h) (PostInvoke I (t, h) op (Ω h)) (Q h) a Γ H /\
                        Ω h (own_invs Γ))
          [] empty_store (M op t)
    }.

    (** The fields of [RGILogic.MethodProvable], over the blocking fragment
        (no footprint: [Ω := fun _ _ => True]). *)
    Record MethodProvableChain (t : tid) (op : Sig.op (RelaxedSig.effect F))
        (P : RelaxedSig.handle F -> Assn VE VF)
        (Q : RelaxedSig.handle F -> Sig.ar op -> Assn VE VF) : Prop := {
      mc_Pinv : forall h s, PostInvoke I (t, h) op (fun _ => True) s -> P h s;
      mc_PI : forall h s, P h s -> I s;
      mc_Pstable : forall h, Stable I (R (t, h)) (P h);
      mc_Qret : forall h r s p2, Q h r s -> poss_return VF t h op r (ps_poss s) p2 ->
                  I (ps_mem s, p2, ps_ghost s);
      mc_Qlin : forall h r s, Q h r s ->
                  exists v pool, ps_poss s = PossOk v pool /\ lin_lookup (t, h) (ls_linr op r) pool;
      mc_Triple : forall h, CProv I R G (t, h) (PostInvoke I (t, h) op (fun _ => True)) (P h) (M op t) (Q h)
    }.

    Lemma chain_provable t op P Q :
      MethodProvableChain t op P Q -> MethodProvable t op (fun _ _ => True) Q.
    Proof.
      intros [HPinv HPI HPst HQret HQlin HT]. constructor.
      - intros h s Hs. exact (HPI h s (HPinv h s Hs)).
      - intros h r s HQ HI _. exists (ps_poss s). split; [apply rt_refl |].
        split; [apply HQlin; exact HQ |]. destruct s as [[σ p] γ]. cbn.
        split; [exact HI |]. split; [apply r_refl |].
        intros p2 Hp2. exact (HQret h r (σ, p, γ) p2 HQ Hp2).
      - intros h. eapply rp_conseq.
        + apply (HT h [] empty_store).
          * split; [constructor |]. exists (fun _ _ => True), (P h). constructor.
            -- intros d sd Hd. destruct d; discriminate.
            -- intros s _ Hs. apply HPinv. exact Hs.
            -- intros d g sg _ Hg. destruct g; discriminate.
            -- intros g sg Hg. destruct g; discriminate.
            -- intros d. apply Stable_true.
            -- apply HPst.
            -- intros s _ Hs _. exact Hs.
          * split; intros d sd; destruct d; discriminate.
        + intros a Γ' H' [[Hall' (fin & fin0 & Hbw)] _]. split; [| exact Logic.I].
          eapply close_done; eauto.
    Qed.
  End Method.

End RelaxedHoare.
