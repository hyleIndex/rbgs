(** * RLHL, part 6: soundness down to relaxed linearizability (RLHL-2)

    This file connects the RLHL judgement of [RelaxedHoare*.v] to the
    semantic criterion (latest-review B-1, m-21).

    ** Results

    - [rlhl_gsim] (and [rlhl_rsim], which names the relation): if
      [RLHL2Hyps I R G M σ0 v0] holds, there is an [S] with
      [GSimRel VE VF M S] and [S (initial_tagged_module VE σ0)
      (PossOk v0 [])].  Generic in the underlay [VE], the overlay [VF],
      the module [M] and the number of calls (any pool of active and
      returned calls, invocations from any reachable configuration,
      returns of any call; re-invoking a returned overlay key is excluded
      by the module itself, [returned_not_fresh], while the abstract pool
      forgets returned keys, [pool_dom_sub]).  Closed: no axiom.
    - [rlhl_rel_lin]: [rlhl_gsim] composed with
      [RelaxedGSim.gsim_rel_lin].  Two named hypotheses: [HVF] (every
      complete well-formed trace of [VF] from [v0] is relaxed-linearizable
      to [nu]; this is [ViewLHL.sound_pres nu VF v0]) and [Hcomplete]
      (the execution ends with every call returned).  Conclusion: the
      overlay trace of every complete execution of [M] over [VE] is
      relaxed-linearizable to [nu].
    - [rlhl_sound] (latest-review m-26): the paper-facing soundness
      theorem in the shape of LHL's [RGILogic.soundness]: derivations
      ([RelaxedHoare.MethodProvable] for every thread and operation), the
      five side conditions of [rlhl2_of_provable], [HVF] and [Hcomplete]
      give relaxed linearizability of every complete execution over
      [VE].  It is [rlhl2_of_provable] followed by [rlhl_rel_lin];
      premise table below.
    - [rlhl_rel_lin_pres]: the same through
      [ViewLHL.presentation_choice]: if moreover [VE] is a complete
      presentation of [nuE] from [σ0], the conclusion holds for every
      complete execution over every underlay [U] that implements [nuE].
      No instance yet.  The intended RLHL-3 instance (author decision on
      latest-review M-18, research-intent §8) is [VE := ViewLHL.VT nuE]
      and the stamp-based overlay [VF := ViewLHL.VT nuF], with [Hsound :=
      ViewLHL.vt_sound]; whether [RLHL2Hyps] is satisfiable over that
      pair is open.
    - [rlhl_rel_lin_ei], [rlhl_rel_lin_ei_pres]: for an
      effect-at-invocation overlay [VF := EI δ] (author decision M-17),
      [HVF] is discharged by [RelaxedHoareSpec.ei_hvf] and the conclusion
      is relaxed linearizability to the sequential specification
      [seq_legal δ s0].  These apply to invocation-ordered underlays (such
      as [RelaxedHoareChecks.CounterHL.HVE]).  For the over-every-underlay
      route M-17 is superseded by M-18: [rlhl_rel_lin_ei_pres] is not
      expected to have an instance over [ViewLHL.VT nuE] for ordered
      same-thread operations, because [VT] accepts dead-end prefixes in
      which a younger same-thread call responds first, which an [EI]
      overlay cannot match ([RelaxedHoareChecks.CounterRelLin.vt_junk],
      [vt_junk_not_rl_prefix]).  For the counter this is mechanized:
      [RelaxedHoareChecks.CounterRelLin.counter_vt_no_rlhl2] (no [I], [R],
      [G] satisfy [RLHL2Hyps] for [Mc] over [VE := VT unu] with [VF := EI
      cδ], through [rlhl_gsim] and [RelaxedGSim.rinv_exec] on an
      incomplete execution); for other specifications the argument is
      the review's prose (latest-review M-18).
    - [rlhl2_of_provable]: derivations ([RelaxedHoare.MethodProvable],
      for every thread and operation) give the field [h_sem] of
      [RLHL2Hyps] ([RelaxedHoareSound.method_sound]); the other fields are
      side conditions on [I], [R], [G] and the initial state.
    - m-21: [finish_stored_sig] (closed) and [finish_stored_ret]
      ([eq_rect_eq], through [Eqdep.EqdepTheory.inj_pair2]): in a
      well-formed pool, the module's [finish_call t h op ret] identifies
      the stored [ActiveCall op' ret'] of [(t, h)].  The soundness proof
      does not need them: it reads the returned entry off [finish_call]
      itself ([finish_src]) and never inverts a stored cell.
      [owners_active_reachable]: in every reachable configuration the call
      pool is duplicate-free and every queue owner is an active call.

    End-to-end instance: [RelaxedHoareChecks.CounterRelLin].
    [counter_rel_lin]: complete executions of the overlapping counter
    over [HVE] are relaxed-linearizable to [seq_legal cδ 0]; [HVF]
    discharged; with a concrete module-derived execution
    ([inc_ooo_exec]: two overlapping [Inc]s of one thread, out-of-order
    returns) and a universal negative ([bad_counter_no_rlhl2]: no [I],
    [R], [G] satisfy [RLHL2Hyps] for a wrong counter, by
    [rlhl_rel_lin_ei]).  Scope of this instance (latest-review M-19): it
    covers the I=∅ fragment (both signatures have [semi_independent :=
    fun _ _ => False], so [rhb] keeps every same-thread edge and no
    semi-independence relaxation is exercised); the underlay is atomic at
    invocation ([HVE] fixes each FAA's value at its invocation; it is not
    [complete_pres], [hve_not_complete]); the body has a single future.
    No instance with nonempty semi-independence, over a complete
    presentation, or over a memory model from [memory/] exists.  The
    counter's methods are verified with the rules
    ([CounterHL.counter_hl_provable], a [MethodProvable] derivation with
    footprint [Ωc]); [counter_rel_lin_by_rules] obtains [counter_rel_lin]
    through [rlhl_sound] from that derivation and the side conditions.
    It is outside the [MethodProvableChain] fragment (below): its
    invariant [Ih] reads the ghost and needs the footprint.

    ** Premise table: [rlhl_sound] against [RGILogic.soundness]

    [RGILogic.soundness] (RGILogic.v:829) concludes
    [TPSimulation.cal M σ0 ρ0]; [rlhl_sound] concludes [rel_lin] of the
    complete executions over [VE] (the simulation-level counterpart is
    [rlhl_gsim]).  Rely and guarantee are indexed by thread there, by
    overlay call key [(t, h)] here; [k <> k'] includes two calls of one
    thread.

    | [RGILogic.soundness]                    | [rlhl_sound]                           |
    |-----------------------------------------|----------------------------------------|
    | [HvalidRG : ValidRGI (R t) (G t) I t]   | dropped (no counterpart; its role is   |
    |                                         | played by each instance's rely and by  |
    |                                         | [Hgr]/[Hir]/[Hrr], see RelaxedHoare.v) |
    | [HRG]: [G t1 ⊆ R t2]                    | [Hgr]: [G k ⊆ R k'] ([h_guar_rely])    |
    | [HRG]: [GINV t1 ⊆ R t2]                 | [Hir] ([h_invoke_rely]): the abstract  |
    |                                         | invocation of [k], with its ghost      |
    |                                         | entries, from an [I]-state             |
    | [HRG]: [GRET t1 ⊆ R t2]                 | [Hrr] ([h_return_rely]): the abstract  |
    |                                         | return of [k] from an [I]-state where  |
    |                                         | [k] owns no ghost entry                |
    | [HRG]: [GId ⊆ R t2]                     | no counterpart premise                 |
    | [Hprovable : MethodProvable ... t f P Q]| [Hprov : MethodProvable I R G M t op   |
    |                                         | Ω Q] (footprint [Ω] in place of [P];   |
    |                                         | every overlay handle)                  |
    | [Hinit : I (σ0, ρ0, TMap.empty)]        | [Hinit : I (σ0, PossOk v0 [], [])]     |
    | -                                       | [Hok] (new): [I] gives a [PossOk] with |
    |                                         | a duplicate-free pool ([h_ok])         |
    | -                                       | [HVF] (overlay presentation sound for  |
    |                                         | [nu]), [Hexec] over [VE] itself,       |
    |                                         | [Hcomplete]                            |

    The LHL-shaped fragment ([RelaxedHoare.MethodProvableChain], mirroring
    the fields of [RGILogic.MethodProvable]) enters [rlhl_sound] only
    through [RelaxedHoare.chain_provable], which fixes the footprint
    [Ω := fun _ _ => True].  Then [mp_PI] requires [I] after the abstract
    invocation for *every* list of own pending invocations appended to
    the ghost, so invariants that count or constrain a call's own ghost
    entries (such as [RelaxedHoareChecks.CounterHL.Ih]) are outside the
    fragment (latest-review m-26, lens 2's analysis; no negative lemma).
    No [MethodProvableChain] instance reaches [rel_lin]: of its users in
    [RelaxedHoareChecks] (pair, xy, await, log), the pair specification
    fails [HVF] ([pair_not_hvf]), [HVF] is not proved for [XYLTS] or
    [LogRead.LLTS] (the latter fails it on a trace given in prose), and
    await has no [RLHL2Hyps] instance.  The only [rlhl_sound] instance is
    the counter ([counter_rel_lin_by_rules]), outside the fragment.

    ** The relation [RSim]

    [RSim I R G c p] is: [I] at [proj c p = (tm_lts_state c, p, ghost_of
    (tm_queue c))]; [OwnersActive] (the pool is duplicate-free, every
    queue owner is active); the domain of the abstract pool is contained
    in the active keys ([pool_dom_sub]); and every entry of the call pool
    satisfies [CallSt]: an active call [(k, ActiveCall op ret)] has an
    owner sub-queue [l] of the queue, whose events carry the call's
    thread, and [CallSafe I R G k op ret l (proj c p)]; a dead call owns
    no queue event.  Every field of [RLHL2Hyps] is used: [h_sem] at
    invocation ([methodsem_safe]), [h_invoke_rely] for the other calls at
    an invocation, [h_guar_rely] for the other calls at an underlay step
    and at the linearization steps of a return, [h_return_rely] for the
    other calls at a return, [h_ok] for the [PossOk] clause of
    [gsim_step], for [pool_dom_steps] and for the existential abstract
    return (the argument of [retcond_return]), [h_init] at the initial
    configuration.  [HandleLinear] is not used (it is a property an
    instance may use to discharge [RLHL2Hyps], see [RelaxedHoareBase]).

    What [RSim] keeps that the proof state [(σ, ρ, γ)] of a call drops
    (latest-review m-25): the module's used underlay keys
    ([tm_used_underlay]; hence M-16 and [HandleLinear]); the committed
    results ([ActiveCall op ret]) and the tags of the other calls; and
    their pending responses ([ghost_of] keeps pending invocations only).
    A call's assertions see only its own remaining events (the index [l]
    of [CallSafe]).  Also, [MethodSem]'s (init) clause and [h_invoke_rely]
    quantify over every ghost satisfying [I], including ghosts that
    already own entries of the fresh key [(t, h)], although
    [rsim_invoke] knows that no queue event is owned by [(t, h)]
    ([Hnown]).  The triple therefore covers states the module never
    reaches; passing [NoOwn (t, h) γ] as a premise would weaken the
    obligation and is not done.

    ** Relation to the paper, and differences

    Paper: Appendix/programlogic.tex:498-505 (Prop. "Logic Soundness": the
    top-level judgement [I, R, G ⊨_t M[t]] of :492-496 gives the
    thread-local simulation [∼_M^t] from the initial state);
    Appendix/relaxedlin.tex:709 (Prop. "Parallel Composition") and its
    corollary (thread-local simulations with compatible rely/guarantee
    give the global one); Appendix/relaxedlin.tex:665-667 (Prop.
    "Soundness": the global simulation gives [ν_E ; cc_E ; M ⊆ ν_F ;
    cc_F]).  Over the LTS [VE] (not over [ν_E], except through the
    uninstantiated [rlhl_rel_lin_pres]), Coq proves the composite of the
    three in one step, with these differences:

    1. Route.  No thread-local simulation and no parallel-composition
       theorem: the per-call triples are composed once, in the global
       relation [RSim].  The rely and the guarantee are indexed by the
       overlay call key [(t, h)], not by thread and pointer.  The
       compatibility conditions of Parallel Composition ([G[B] ∪ R_sys[B]
       ⊆ R_t[A]], ...) and the premise [Invoke_{t,p}(f) ∈ G] of the
       top-level judgement correspond to [h_guar_rely], [h_invoke_rely]
       and [h_return_rely].  [h_invoke_rely] is implied by the paper's
       [Invoke ∈ G] together with [h_guar_rely], not conversely, so it is
       the weaker (more permissive) condition (latest-review M-15,
       verifiers' correction).
    2. Simulation.  [GSimRel] is universal in every clause; the paper's
       OStep (relaxedlin.tex, simulation definition) is existential.
    3. Single possibility.  The proof state carries one possibility, not
       a set (author decision, research-intent §8); future-dependent
       linearization points are out of scope, and so is the paper's
       Completeness proposition.
    4. Complete traces only.  [rlhl_rel_lin] concludes for executions in
       which every call has returned ([Hcomplete]); nothing is stated
       about executions with pending calls, and no theorem concludes
       [ViewLHL.implements nuF], so RLHL-verified layers cannot yet be
       stacked (latest-review M-1).  The author chose prefix soundness
       ([gsim_implements] / [rlhl_implements]) for RLHL-3
       (research-intent §8, Q3/M-1); not done.  Caveat for that plan:
       "every [VF] path is an [rl_prefix]" is not free for [VF := VT nuF]
       when same-thread operations are ordered
       ([RelaxedHoareChecks.CounterRelLin.vt_not_implements], shown for
       the FAA specification [unu]).  The paper's Soundness is a trace
       inclusion for all traces.
    5. [HVF] explicit.  The conclusion is relaxed linearizability to [nu]
       under the hypothesis that the overlay presentation [VF] itself only
       produces relaxed-linearizable complete traces.  For [EI δ] it is
       discharged ([rlhl_rel_lin_ei]).  For the over-every-underlay
       version, [VE] must in addition be a complete presentation
       ([rlhl_rel_lin_pres]); no [RLHL2Hyps] instance over a complete
       presentation exists yet.  The intended one is [VE := ViewLHL.VT
       nuE], [VF := ViewLHL.VT nuF] with [Hsound := vt_sound] (author
       decision M-18, RLHL-3); [EI] over [ViewLHL.VT] is not expected to
       work for ordered same-thread operations (see [rlhl_rel_lin_ei]
       above; [counter_vt_no_rlhl2] for the counter).  The counter instance runs over [HVE], which is not
       complete ([RelaxedHoareChecks.CounterRelLin.hve_not_complete]).
    6. Generic [VE].  The underlay is an arbitrary LTS; nothing here is
       about a memory model (no RC11, x86-TSO or buffered-cell instance).
    7. Partial correctness.  The tagged module semantics has no error
       transition and [GSimRel] no error clause; underlay [Error] is
       invisible (latest-review m-8).
    8. Prophetic certificate.  [MethodSem]'s certificate is chosen after
       the produced trace and result (latest-review m-11); this is sound
       for the module because [tagged_invoke] commits both at the overlay
       invocation.
    9. Semantics.  The module is the dependency-only tagged semantics
       ([module_step_tagged], (F1)-(F3)), so a call's own underlay events
       may leave program order (author decision, research-intent §8).
    10. VLHL (latest-review m-18 (i)).  implex.tex:162-179 (the top-level
        judgement, :162-167, and Prop. "Logic Soundness",
        [prop:rlhl-sc], :170-179, in the VLHL subsection that starts at
        :114) corresponds to [ViewLHL.vlhl_sound] (premise: a [GSimRel]
        over [VT nuE], [VT nuF], not a judgement; uninstantiated), and on
        the RLHL side to [rlhl_rel_lin_pres] with [VE := VT nuE], [VF :=
        VT nuF], [Hcomp := ViewLHL.vt_complete] and [Hsound :=
        ViewLHL.vt_sound] (also uninstantiated).  The paper's proposition
        concludes from the judgement for one thread [t] (no [∀ t]) and
        states no R/G-compatibility premise (latest-review M-15); here
        [RLHL2Hyps] requires the triple for every thread and the
        compatibility fields [h_guar_rely], [h_invoke_rely] and
        [h_return_rely].
    11. Same-thread rely (m-18 (ii)).  Appendix/relaxedlin.tex:626: the
        paper's [R_π] covers only the *independent* operations of the
        same thread running concurrently; here [R k] covers every other
        call, of any thread, including same-thread calls that are not
        semi-independent of [k].
    12. Definition of relaxed linearizability (m-18 (iii)).  The
        conclusion is [RelaxedTraceLin.rel_lin], the witness form (a
        sequential witness preserving [rhb]); the paper's equivalence of
        its two definitions, [prop:rhb-equiv] (relaxedlin.tex:39), is not
        mechanized.
    13. Guarantee (m-18 (iv)).  Appendix/programlogic.tex:479-482 and
        :503 use [R = R[t] ∪ R[π]] and [G = G[t] ∩ G[π]]; here there is
        one guarantee [G k] per call and one rely [R k].
    14. Overlapping calls (m-18 (v)).  The paper's soundness proof
        composes the calls of one thread sequentially
        (Appendix/programlogic.tex:509, "After executing f, we will apply
        the argument above again"); [RSim] handles any number of
        overlapping active calls per thread, ordered only by the module's
        (F1)-(F3) and, in the proof state, by the ghost thread frontier.

    Assumptions: [rlhl_gsim], [rlhl_rsim], [rlhl2_of_provable],
    [finish_stored_sig], [owners_active_reachable] are closed;
    [rlhl_rel_lin], [rlhl_sound], [rlhl_rel_lin_pres],
    [rlhl_rel_lin_ei], [rlhl_rel_lin_ei_pres] use
    [Eqdep.Eq_rect_eq.eq_rect_eq], inherited from
    [RelaxedGSim.gsim_rel_lin]; [finish_stored_ret] uses it through
    [inj_pair2]. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Logic.Eqdep.

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
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.

Import ListNotations.


Module RelaxedHoareGSim.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import ViewLHL.
  Import RelaxedHoareBase.
  Import RelaxedHoare.
  Import RelaxedHoareSound.
  Import RelaxedHoareSpec.

  (** ** Part 1: module-level facts (latest-review m-21)

      Nothing here mentions the logic.  [active_key calls k]: the call
      pool has an entry with key [k] whose cell is [ActiveCall]. *)

  Definition is_active {F : RelaxedSig.t} (cell : CallCell F) : Prop :=
    match cell with ActiveCall _ _ => True | DeadCall => False end.

  Definition active_key {F : RelaxedSig.t} (calls : CallPool F) (k : CallKey F) : Prop :=
    exists e, In e calls /\ call_key e = k /\ is_active (ce_cell F e).

  Section CallPoolFacts.
    Context {F : RelaxedSig.t}.

    Lemma entry_key_unique (calls : CallPool F) e1 e2 :
      call_pool_well_formed calls -> In e1 calls -> In e2 calls -> call_key e1 = call_key e2 -> e1 = e2.
    Proof.
      unfold call_pool_well_formed. induction calls as [| a l IH]; intros Hnd Hx Hy Hf; [destruct Hx |].
      cbn in Hnd. apply NoDup_cons_iff in Hnd as [Hna Hnd].
      destruct Hx as [<- | Hx], Hy as [<- | Hy]; [reflexivity | | | exact (IH Hnd Hx Hy Hf)].
      - exfalso. apply Hna. rewrite Hf. apply in_map. exact Hy.
      - exfalso. apply Hna. rewrite <- Hf. apply in_map. exact Hx.
    Qed.

    Lemma active_key_in (calls : CallPool F) k : active_key calls k -> In k (map call_key calls).
    Proof. intros (e & He & <- & _). apply in_map. exact He. Qed.

    Lemma finish_src t h op (ret : Sig.ar op) (calls calls' : CallPool F) :
      finish_call t h op ret calls calls' -> In (Build_CallEntry t h (ActiveCall op ret)) calls.
    Proof. induction 1; [left; reflexivity | right; exact IHfinish_call]. Qed.

    Lemma finish_tgt t h op (ret : Sig.ar op) (calls calls' : CallPool F) :
      finish_call t h op ret calls calls' -> In (@Build_CallEntry F t h DeadCall) calls'.
    Proof. induction 1; [left; reflexivity | right; exact IHfinish_call]. Qed.

    Lemma finish_back t h op (ret : Sig.ar op) (calls calls' : CallPool F) e :
      finish_call t h op ret calls calls' -> In e calls' -> In e calls \/ e = Build_CallEntry t h DeadCall.
    Proof.
      induction 1 as [tail | t' h' cell pool pool' Hneq Hf IH]; intros [<- | Hin].
      - right. reflexivity.
      - left. right. exact Hin.
      - left. left. reflexivity.
      - destruct (IH Hin) as [H | H]; [left; right; exact H | right; exact H].
    Qed.

    Lemma finish_other t h op (ret : Sig.ar op) (calls calls' : CallPool F) e :
      finish_call t h op ret calls calls' -> In e calls -> call_key e <> (t, h) -> In e calls'.
    Proof.
      induction 1 as [tail | t0 h0 cell pool pool' Hneq Hfin IH]; intros Hin Hk.
      - destruct Hin as [<- | Hin]; [exfalso; apply Hk; reflexivity | right; exact Hin].
      - destruct Hin as [<- | Hin]; [left; reflexivity | right; apply IH; assumption].
    Qed.

    (** A returned call keeps its key in the pool as [DeadCall], so the
        module never re-invokes an overlay key ([call_fresh] fails). *)
    Lemma returned_not_fresh t h (calls : CallPool F) :
      In (@Build_CallEntry F t h DeadCall) calls -> ~ call_fresh (t, h) calls.
    Proof. intros Hin Hf. apply Hf. exact (in_map call_key _ _ Hin). Qed.

    (** m-21, first half: the module's [finish_call t h op ret] removes
        the stored entry of [(t, h)].  In a well-formed pool the stored
        [ActiveCall op' ret'] of [(t, h)] is the returned one, as a
        dependent pair.  Closed (no axiom). *)
    Lemma finish_stored_sig t h op (ret : Sig.ar op) op' (ret' : Sig.ar op') (calls calls' : CallPool F) :
      call_pool_well_formed calls -> finish_call t h op ret calls calls' ->
      In (Build_CallEntry t h (ActiveCall op' ret')) calls ->
      existT (fun o => Sig.ar o) op' ret' = existT (fun o => Sig.ar o) op ret.
    Proof.
      intros Hwf Hfin Hin.
      pose proof (entry_key_unique calls _ _ Hwf Hin (finish_src _ _ _ _ _ _ Hfin) eq_refl) as Heq.
      injection Heq as _ Hsig. exact Hsig.
    Qed.

    (** The same with the result itself: injectivity of the second
        component of a dependent pair, which uses [Eqdep.inj_pair2]
        (axiom [Eq_rect_eq.eq_rect_eq], in the baseline).  Not used by the
        soundness proof below, which never inverts the stored cell: it
        reads the returned entry off [finish_call] itself
        ([finish_src]). *)
    Corollary finish_stored_ret t h op (ret ret' : Sig.ar op) (calls calls' : CallPool F) :
      call_pool_well_formed calls -> finish_call t h op ret calls calls' ->
      In (Build_CallEntry t h (ActiveCall op ret')) calls -> ret' = ret.
    Proof.
      intros Hwf Hfin Hin.
      exact (Eqdep.EqdepTheory.inj_pair2 _ (fun o => Sig.ar o) op ret' ret
               (finish_stored_sig t h op ret op ret' calls calls' Hwf Hfin Hin)).
    Qed.
  End CallPoolFacts.

  (** m-21, second half: in every configuration reachable from the
      initial module, the call pool is well formed and the owner of every
      pending queue event is an active call.  A property of the module
      semantics alone, for arbitrary pools. *)

  Section OwnerActive.
    Context {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F).

    Definition OwnersActive (c : @TaggedModuleConfig E F VE) : Prop :=
      call_pool_well_formed (tm_calls c) /\
      forall x, In x (tm_queue c) -> active_key (tm_calls c) (ts_owner x).

    Lemma select_sub (cand : TaggedScheduledEvent E F) q q' x :
      select_frontier_tagged cand q q' -> In x q' -> In x q.
    Proof.
      intros Hsel Hx. destruct (select_split _ _ _ Hsel) as (pre & post & -> & -> & _).
      apply in_app_or in Hx. apply in_or_app. destruct Hx; [left | right; right]; assumption.
    Qed.

    Lemma owners_active_step ev c c' :
      OwnersActive c -> module_step_tagged VE M ev c c' -> OwnersActive c'.
    Proof.
      intros [Hwf Hown] Hst.
      destruct Hst as [t h op q pool queue used trace ret Hfresh Hmeth Hft
                     | cand q q' pool queue queue' used Hsel Hlts
                     | t h op ret q pool pool' queue used Hfin Hdone];
        cbn [tm_calls tm_queue] in *.
      - split.
        + unfold call_pool_well_formed. cbn. constructor; [exact Hfresh | exact Hwf].
        + intros x Hx. apply in_app_or in Hx as [Hx | Hx].
          * destruct (Hown x Hx) as (e & He & Hk & Ha). exists e. split; [right; exact He | auto].
          * unfold schedule_trace_tagged in Hx. apply in_map_iff in Hx as (m & <- & _).
            exists (Build_CallEntry t h (ActiveCall op ret)). cbn.
            split; [left; reflexivity | split; [reflexivity | exact Logic.I]].
      - split; [exact Hwf |]. intros x Hx. apply Hown. exact (select_sub _ _ _ _ Hsel Hx).
      - split; [exact (finish_call_well_formed _ _ _ _ _ _ Hfin Hwf) |].
        intros x Hx. destruct (Hown x Hx) as (e & He & Hk & Ha). exists e.
        split; [| auto]. apply (finish_other t h op ret pool pool' e Hfin He).
        intros Heq. apply Hdone. rewrite <- Heq, Hk. apply in_map. exact Hx.
    Qed.

    Lemma owners_active_exec c evs c' :
      OwnersActive c -> module_execution_tagged VE M c evs c' -> OwnersActive c'.
    Proof.
      intros H0 Hex. induction Hex as [c | c1 c2 c3 ev trace Hstep Hexec IH]; [exact H0 |].
      apply IH. exact (owners_active_step _ _ _ H0 Hstep).
    Qed.

    Theorem owners_active_reachable q0 evs c :
      module_execution_tagged VE M (initial_tagged_module VE q0) evs c -> OwnersActive c.
    Proof.
      intros Hex. apply (owners_active_exec (initial_tagged_module VE q0) evs c); [| exact Hex].
      split; [constructor | intros x []].
    Qed.
  End OwnerActive.

  (** ** Part 2: the simulation relation [RSim] *)

  Lemma forall_drop {A : Type} (P : A -> Prop) pre (m : A) post :
    Forall P (pre ++ m :: post) -> Forall P (pre ++ post).
  Proof.
    rewrite !Forall_forall. intros H x Hx. apply H.
    apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left | right; right]; exact Hx.
  Qed.

  Section Bridge.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).

    Abbreviation Cfg := (@TaggedModuleConfig E F VE).

    (** The proof state of a module configuration: its underlay state, the
        possibility, and the ghost computed from the queue. *)
    Definition proj (c : Cfg) (p : Poss VF) : PState VE VF :=
      (tm_lts_state c, p, ghost_of (tm_queue c)).

    (** The state of one entry of the call pool: an active call of [op]
        with committed result [ret] is safe ([CallSafe]) on its owner
        sub-queue; a dead call owns no pending event. *)
    Definition CallSt (k : CallKey F) (cell : CallCell F) (c : Cfg) (p : Poss VF) : Prop :=
      match cell with
      | ActiveCall op ret =>
          exists l, owner_subqueue k (tm_queue c) l /\
            Forall (fun m => te_tid E (untag m) = fst k) l /\
            CallSafe I R G k op ret l (proj c p)
      | DeadCall => owner_done_tagged k (tm_queue c)
      end.

    (** The relation of [rlhl_gsim] (latest-review B-1, "Required" 1). *)
    Record RSim (c : Cfg) (p : Poss VF) : Prop := {
      rs_inv : I (proj c p);
      rs_owners : OwnersActive VE c;
      rs_dom : pool_dom_sub (active_key (tm_calls c)) p;
      rs_calls : forall e, In e (tm_calls c) -> CallSt (call_key e) (ce_cell F e) c p
    }.

    (** How an abstract run matches one module step (the three clauses of
        [RelaxedGSim.gsim_step]). *)
    Definition StepMatch (ev : ModuleEvent E F) (p p' : Poss VF) : Prop :=
      match ev with
      | UnderlayEvent _ => poss_steps VF p p'
      | OverlayEvent x =>
          match te_ev F x with
          | InvEv h op => poss_invoke VF (te_tid F x) h op p p'
          | ResEv h op r => exists p1, poss_steps VF p p1 /\ poss_return VF (te_tid F x) h op r p1 p'
          end
      end.

    Lemma callsafe_inv k op ret l s :
      CallSafe I R G k op ret l s ->
      I s /\
      (forall pre m post, l = pre ++ m :: post -> local_frontier pre m ->
         forall γ' σ', ghost_emit k (untag m) (ps_ghost s) γ' -> Step VE (untag m) (ps_mem s) σ' ->
           exists p', poss_steps VF (ps_poss s) p' /\ I (σ', p', γ') /\
                      G k s (σ', p', γ') /\ CallSafe I R G k op ret (pre ++ post) (σ', p', γ')) /\
      (forall s', R k s s' -> I s' -> CallSafe I R G k op ret l s') /\
      (l = [] -> NoOwn k (ps_ghost s) -> RetCond I G k op ret s).
    Proof. intros Hcs. destruct Hcs as [l s HI Hemit Hrely Hret]. auto. Qed.

    Lemma pool_dom_mono (P P' : CallKey F -> Prop) (p : Poss VF) :
      (forall k, P k -> P' k) -> pool_dom_sub P p -> pool_dom_sub P' p.
    Proof.
      intros Himp (v & pool & -> & Hd). exists v, pool.
      split; [reflexivity | intros k Hk; exact (Himp k (Hd k Hk))].
    Qed.

    Lemma done_app_other k k' (q : TaggedQueue E F) (tr : list (TaggedEvent E)) :
      owner_done_tagged k q -> k <> k' -> owner_done_tagged k (q ++ schedule_trace_tagged k' tr).
    Proof.
      intros Hd Hne Hin. rewrite map_app in Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Hd Hin) |].
      unfold schedule_trace_tagged in Hin. rewrite map_map in Hin. apply in_map_iff in Hin as (m & Hm & _).
      exact (Hne (eq_sym Hm)).
    Qed.

    Lemma done_select k (cand : TaggedScheduledEvent E F) q q' :
      select_frontier_tagged cand q q' -> owner_done_tagged k q -> owner_done_tagged k q'.
    Proof.
      intros Hsel Hd Hin. apply Hd. apply in_map_iff in Hin as (x & <- & Hx).
      apply in_map. exact (select_sub _ _ _ _ Hsel Hx).
    Qed.

    (** *** Preservation, assuming the hypotheses of RLHL-2 *)

    Context (M : RelaxedModuleImpl E F) (σ0 : State VE) (v0 : State VF).
    Context (HH : RLHL2Hyps I R G M σ0 v0).

    Lemma callsafe_refl_rely k op ret l k' s s' :
      k' <> k -> clos_refl _ (G k') s s' -> I s' ->
      CallSafe I R G k op ret l s -> CallSafe I R G k op ret l s'.
    Proof.
      intros Hne HG HI Hcs. destruct HG as [s'' HG |]; [| exact Hcs].
      destruct (callsafe_inv _ _ _ _ _ Hcs) as (_ & _ & Hrely & _).
      apply Hrely; [| exact HI]. exact (h_guar_rely _ _ _ _ _ _ HH k' k _ _ Hne HG).
    Qed.

    (** Overlay invocation, from an arbitrary configuration: [call_fresh]
        and the pool domain give [lin_fresh] ([lin_fresh_of_dom]), hence
        the abstract invocation ([poss_invoke_exists]); the new call gets
        its [CallSafe] from [MethodSem] ([methodsem_safe]); every other
        active call moves by its rely ([h_invoke_rely]). *)
    Lemma rsim_invoke t h op q pool queue used trace ret p :
      RSim (Build_TaggedModuleConfig q pool queue used) p ->
      call_fresh (t, h) pool ->
      program_produces_tagged t (M op t) trace ret ->
      OwnersActive VE (Build_TaggedModuleConfig (F := F) q (Build_CallEntry t h (ActiveCall op ret) :: pool)
                          (queue ++ schedule_trace_tagged (t, h) trace) (used ++ invocation_keys (map untag trace))) ->
      exists p', poss_invoke VF t h op p p' /\
        RSim (Build_TaggedModuleConfig q (Build_CallEntry t h (ActiveCall op ret) :: pool)
                (queue ++ schedule_trace_tagged (t, h) trace) (used ++ invocation_keys (map untag trace))) p'.
    Proof.
      intros [HI [Hcwf Hown] Hdom Hcalls] Hfresh Hprod Hoa'.
      cbn [tm_calls tm_queue tm_lts_state] in *.
      destruct Hdom as (v & lpool & -> & Hd).
      assert (Hnact : ~ active_key pool (t, h)) by (intros Ha; exact (Hfresh (active_key_in _ _ Ha))).
      assert (Hlf : lin_fresh (t, h) lpool).
      { apply (lin_fresh_of_dom (VF := VF) (active_key pool) (t, h) v lpool); [| exact Hnact].
        exists v, lpool. split; [reflexivity | exact Hd]. }
      destruct (poss_invoke_exists (VF := VF) t h op v lpool Hlf) as (p' & Hpi).
      destruct (methodsem_safe I R G M t op (h_sem _ _ _ _ _ _ HH t op) h trace ret Hprod
                  q (PossOk v lpool) (ghost_of queue) p' HI Hpi) as [HI' Hcs].
      assert (Hg : ghost_of (queue ++ schedule_trace_tagged (t, h) trace) = ghost_of queue ++ ghost_new (t, h) trace)
        by (rewrite ghost_of_app, ghost_of_schedule; reflexivity).
      assert (Hnown : forall x, In x queue -> ts_owner x <> (t, h))
        by (intros x Hx Heq; apply Hnact; rewrite <- Heq; exact (Hown x Hx)).
      exists p'. split; [exact Hpi |].
      constructor; cbn [tm_calls tm_queue tm_lts_state].
      - unfold proj. cbn [tm_lts_state tm_queue]. rewrite Hg. exact HI'.
      - exact Hoa'.
      - apply (pool_dom_mono (fun k => active_key pool k \/ k = (t, h))).
        + intros k [(e & He & Hk & Ha) | ->].
          * exists e. split; [right; exact He | auto].
          * exists (Build_CallEntry t h (ActiveCall op ret)). split; [left; reflexivity |]. split; [reflexivity | exact Logic.I].
        + apply (pool_dom_invoke (VF := VF) (active_key pool) t h op (PossOk v lpool) p' Hpi).
          exists v, lpool. split; [reflexivity | exact Hd].
      - intros e [<- | He].
        + cbn [CallSt call_key ce_tid ce_handle ce_cell fst]. exists trace. split.
          * exact (osq_app _ _ _ _ _ (osq_none _ _ Hnown) (osq_schedule_own _ _)).
          * split; [exact (program_produces_tagged_trace_tid _ _ _ _ Hprod) |].
            unfold proj. cbn [tm_lts_state tm_queue]. rewrite Hg. exact Hcs.
        + assert (Hne : (t, h) <> call_key e) by (intros Heq; apply Hfresh; rewrite Heq; apply in_map; exact He).
          pose proof (Hcalls e He) as Hst. destruct e as [te he [op' ret' |]].
          * cbn [CallSt call_key ce_tid ce_handle ce_cell fst] in Hst, Hne |- *.
            destruct Hst as (l & Hosq & Htid & Hcs0). exists (l ++ []). split.
            -- exact (osq_app _ _ _ _ _ Hosq (osq_schedule_other _ _ _ Hne)).
            -- rewrite app_nil_r. split; [exact Htid |].
               destruct (callsafe_inv _ _ _ _ _ Hcs0) as (_ & _ & Hrely & _).
               unfold proj. cbn [tm_lts_state tm_queue]. rewrite Hg.
               apply Hrely; [| exact HI'].
               exact (h_invoke_rely _ _ _ _ _ _ HH (t, h) (te, he) op trace ret
                        (q, PossOk v lpool, ghost_of queue) p' Hne Hprod HI Hpi).
          * cbn [CallSt call_key ce_tid ce_handle ce_cell] in Hst, Hne |- *.
            exact (done_app_other _ _ _ _ Hst (fun Heq => Hne (eq_sym Heq))).
    Qed.

    (** Underlay step: the owner of the emitted event is active
        ([OwnersActive]); its sub-queue loses the event at a local-frontier
        position ([select_project]) with the ghost transition
        [ghost_of_select], so its [CallSafe] answers; by key uniqueness
        every other entry is another call, whose sub-queue is untouched
        and whose [CallSafe] moves by its rely ([h_guar_rely]). *)
    Lemma rsim_underlay cand q q' pool queue queue' used p :
      RSim (Build_TaggedModuleConfig q pool queue used) p ->
      select_frontier_tagged cand queue queue' ->
      Step VE (untag (ts_event cand)) q q' ->
      exists p', poss_steps VF p p' /\ RSim (Build_TaggedModuleConfig q' pool queue' used) p'.
    Proof.
      intros [HI [Hcwf Hown] Hdom Hcalls] Hsel Hlts. cbn [tm_calls tm_queue tm_lts_state] in *.
      destruct (Hown cand (select_frontier_tagged_member _ _ _ Hsel)) as (e0 & He0 & Hk0 & Ha0).
      pose proof (Hcalls e0 He0) as Hst0.
      destruct e0 as [t0 h0 [op0 ret0 |]]; [| destruct Ha0].
      cbn [CallSt call_key ce_tid ce_handle ce_cell] in Hst0.
      unfold call_key in Hk0. cbn [ce_tid ce_handle] in Hk0.
      destruct Hst0 as (l0 & Hosq0 & Htid0 & Hcs0).
      destruct (select_project (t0, h0) queue l0 cand queue' Hosq0 Htid0 Hsel)
        as [(_ & pre & post & -> & Hfr & Hosq0') | (Hne0 & _)]; [| contradiction (Hne0 (eq_sym Hk0))].
      destruct (callsafe_inv _ _ _ _ _ Hcs0) as (_ & Hemit & _ & _).
      assert (Hge : ghost_emit (t0, h0) (untag (ts_event cand)) (ghost_of queue) (ghost_of queue')).
      { rewrite Hk0. exact (ghost_of_select _ _ _ Hsel). }
      destruct (Hemit pre (ts_event cand) post eq_refl Hfr (ghost_of queue') q' Hge Hlts)
        as (p' & Hps & HI' & HG & Hcs0').
      exists p'. split; [exact Hps |].
      constructor; cbn [tm_calls tm_queue tm_lts_state].
      - exact HI'.
      - split; [exact Hcwf | intros x Hx; exact (Hown x (select_sub _ _ _ _ Hsel Hx))].
      - apply (pool_dom_steps _ p p' Hps); [| exact Hdom].
        destruct (h_ok _ _ _ _ _ _ HH _ HI') as (v' & pool' & Hp' & _). cbn in Hp'. rewrite Hp'. discriminate.
      - intros e He. pose proof (Hcalls e He) as Hst.
        enough (Hc : e = Build_CallEntry t0 h0 (ActiveCall op0 ret0) \/
                     CallSt (call_key e) (ce_cell F e) (Build_TaggedModuleConfig q' pool queue' used) p').
        { destruct Hc as [-> | Hc]; [| exact Hc].
          cbn [CallSt call_key ce_tid ce_handle ce_cell]. exists (pre ++ post).
          split; [exact Hosq0' |]. split; [exact (forall_drop _ _ _ _ Htid0) | exact Hcs0']. }
        destruct e as [te he [op ret |]]; cbn [CallSt call_key ce_tid ce_handle ce_cell] in Hst |- *.
        + destruct Hst as (l & Hosq & Htid & Hcs).
          destruct (select_project (te, he) queue l cand queue' Hosq Htid Hsel)
            as [(Hown' & _) | (Hne & Hosq')].
          * left. apply (entry_key_unique pool _ _ Hcwf He He0). unfold call_key. cbn [ce_tid ce_handle].
            rewrite <- Hown', Hk0. reflexivity.
          * right. exists l. split; [exact Hosq' |]. split; [exact Htid |].
            destruct (callsafe_inv _ _ _ _ _ Hcs) as (_ & _ & Hrely & _).
            apply Hrely; [| exact HI'].
            apply (h_guar_rely _ _ _ _ _ _ HH (t0, h0) (te, he) _ _); [| exact HG].
            intros Heq. apply Hne. rewrite <- Hk0. exact Heq.
        + right. exact (done_select _ _ _ _ Hsel Hst).
    Qed.

    (** Overlay return of [(t, h)] with result [ret]: the returned entry is
        read off [finish_call] ([finish_src]), so no inversion of the
        stored cell is needed; its sub-queue is empty ([osq_done]), its
        [RetCond] applies with [NoOwn] from [ghost_of_done], and [h_ok]
        makes the abstract return existential; every other active call
        moves by its rely twice ([h_guar_rely] for the linearization
        steps, [h_return_rely] for the abstract return). *)
    Lemma rsim_return t h op (ret : Sig.ar op) q pool pool' queue used p :
      RSim (Build_TaggedModuleConfig q pool queue used) p ->
      finish_call t h op ret pool pool' -> owner_done_tagged (t, h) queue ->
      exists p1 p2, poss_steps VF p p1 /\ poss_return VF t h op ret p1 p2 /\
        RSim (Build_TaggedModuleConfig q pool' queue used) p2.
    Proof.
      intros [HI [Hcwf Hown] Hdom Hcalls] Hfin Hdone. cbn [tm_calls tm_queue tm_lts_state] in *.
      pose proof (Hcalls _ (finish_src _ _ _ _ _ _ Hfin)) as HstR.
      cbn [CallSt call_key ce_tid ce_handle ce_cell] in HstR.
      destruct HstR as (l & Hosq & _ & HcsR).
      pose proof (osq_done _ _ _ Hdone Hosq) as ->.
      destruct (callsafe_inv _ _ _ _ _ HcsR) as (_ & _ & _ & Hret).
      pose proof (ghost_of_done _ _ Hdone) as Hno.
      destruct (Hret eq_refl Hno) as (p1 & Hps & (v & lpool & -> & Hlk) & HI1 & HG & Hrm).
      destruct (h_ok _ _ _ _ _ _ HH _ HI1) as (v' & lpool' & Hp1 & Hwf1). cbn in Hp1.
      injection Hp1 as <- <-.
      destruct (lin_remove_exists (t, h) _ lpool Hwf1 Hlk) as (lpool2 & Hrem).
      assert (Hpr : poss_return VF t h op ret (PossOk v lpool) (PossOk v lpool2)) by (constructor; exact Hrem).
      pose proof (Hrm _ Hpr) as HI2.
      assert (Hcwf' := finish_call_well_formed _ _ _ _ _ _ Hfin Hcwf).
      exists (PossOk v lpool), (PossOk v lpool2). split; [exact Hps |]. split; [exact Hpr |].
      constructor; cbn [tm_calls tm_queue tm_lts_state].
      - exact HI2.
      - split; [exact Hcwf' |]. intros x Hx. destruct (Hown x Hx) as (e & He & Hk & Ha). exists e.
        split; [| auto]. apply (finish_other t h op ret pool pool' e Hfin He).
        intros Heq. apply Hdone. rewrite <- Heq, Hk. apply in_map. exact Hx.
      - apply (pool_dom_mono (fun k => active_key pool k /\ k <> (t, h))).
        + intros k ((e & He & Hk & Ha) & Hne). exists e.
          split; [apply (finish_other t h op ret pool pool' e Hfin He); rewrite Hk; exact Hne | auto].
        + apply (pool_dom_return (VF := VF) (active_key pool) t h op ret (PossOk v lpool) (PossOk v lpool2) Hpr).
          * intros v1 pool1 Heq. injection Heq as _ <-. exact Hwf1.
          * apply (pool_dom_steps _ p _ Hps); [discriminate | exact Hdom].
      - intros e He. destruct (finish_back _ _ _ _ _ _ _ Hfin He) as [Hin | ->].
        + pose proof (Hcalls e Hin) as Hst.
          destruct e as [te he [op' ret' |]]; cbn [CallSt call_key ce_tid ce_handle ce_cell] in Hst |- *.
          * assert (Hne : (t, h) <> (te, he)).
            { intros Heq.
              assert (Hx : Build_CallEntry te he (ActiveCall op' ret') = Build_CallEntry t h DeadCall).
              { apply (entry_key_unique pool' _ _ Hcwf' He (finish_tgt _ _ _ _ _ _ Hfin)).
                unfold call_key. cbn [ce_tid ce_handle]. rewrite Heq. reflexivity. }
              discriminate Hx. }
            destruct Hst as (l' & Hosq' & Htid' & Hcs'). exists l'. split; [exact Hosq' |]. split; [exact Htid' |].
            assert (Hcs1 : CallSafe I R G (te, he) op' ret' l' (q, PossOk v lpool, ghost_of queue))
              by exact (callsafe_refl_rely _ _ _ _ (t, h) _ _ Hne HG HI1 Hcs').
            destruct (callsafe_inv _ _ _ _ _ Hcs1) as (_ & _ & Hrely1 & _).
            apply Hrely1; [| exact HI2].
            exact (h_return_rely _ _ _ _ _ _ HH (t, h) (te, he) op ret
                     (q, PossOk v lpool, ghost_of queue) (PossOk v lpool2) Hne HI1 Hpr Hno).
          * exact Hst.
        + cbn [CallSt call_key ce_tid ce_handle ce_cell]. exact Hdone.
    Qed.

    Lemma rsim_step ev c c' p :
      RSim c p -> module_step_tagged VE M ev c c' -> exists p', StepMatch ev p p' /\ RSim c' p'.
    Proof.
      intros HS Hst.
      pose proof (owners_active_step VE M ev c c' (rs_owners _ _ HS) Hst) as Hoa'.
      destruct Hst as [t h op q pool queue used trace ret Hfresh Hmeth Hft
                     | cand q q' pool queue queue' used Hsel Hlts
                     | t h op ret q pool pool' queue used Hfin Hdone].
      - destruct (rsim_invoke t h op q pool queue used trace ret p HS Hfresh Hmeth Hoa') as (p' & Hpi & HS').
        exists p'. split; [exact Hpi | exact HS'].
      - destruct (rsim_underlay cand q q' pool queue queue' used p HS Hsel Hlts) as (p' & Hps & HS').
        exists p'. split; [exact Hps | exact HS'].
      - destruct (rsim_return t h op ret q pool pool' queue used p HS Hfin Hdone) as (p1 & p2 & Hps & Hpr & HS').
        exists p2. split; [exists p1; split; [exact Hps | exact Hpr] | exact HS'].
    Qed.

    Theorem rsim_gsim : GSimRel VE VF M RSim.
    Proof.
      intros c p HS. split; [| split; [| split]].
      - destruct (h_ok _ _ _ _ _ _ HH _ (rs_inv _ _ HS)) as (v & pool & Hp & _). exists v, pool. exact Hp.
      - intros t h op c' Hst. exact (rsim_step _ _ _ _ HS Hst).
      - intros ev c' Hst. exact (rsim_step _ _ _ _ HS Hst).
      - intros t h op ret c' Hst.
        destruct (rsim_step _ _ _ _ HS Hst) as (p'' & (p' & Hps & Hpr) & HS').
        exists p', p''. split; [exact Hps | split; [exact Hpr | exact HS']].
    Qed.

    Lemma rsim_init : RSim (initial_tagged_module VE σ0) (PossOk v0 []).
    Proof.
      constructor; cbn [tm_calls tm_queue tm_lts_state initial_tagged_module].
      - exact (h_init _ _ _ _ _ _ HH).
      - split; [constructor | intros x []].
      - exists v0, []. split; [reflexivity | intros k []].
      - intros e [].
    Qed.
  End Bridge.

  (** ** Part 3: soundness theorems *)

  Section Soundness.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (M : RelaxedModuleImpl E F).
    Context (σ0 : State VE) (v0 : State VF).

    (** RLHL-2, B-1 "Required" 1: the hypotheses of RLHL-2 give a global
        simulation from the initial module, for every number of calls.
        The relation is [RSim I R G] ([rlhl_rsim] names it). *)
    Theorem rlhl_rsim (HH : RLHL2Hyps I R G M σ0 v0) :
      GSimRel VE VF M (RSim I R G) /\ RSim I R G (initial_tagged_module VE σ0) (PossOk v0 []).
    Proof. split; [exact (rsim_gsim I R G M σ0 v0 HH) | exact (rsim_init I R G M σ0 v0 HH)]. Qed.

    Theorem rlhl_gsim (HH : RLHL2Hyps I R G M σ0 v0) :
      exists S, GSimRel VE VF M S /\ S (initial_tagged_module VE σ0) (PossOk v0 []).
    Proof. exists (RSim I R G). exact (rlhl_rsim HH). Qed.

    (** RLHL-2, B-1 "Required" 2: relaxed linearizability of every
        complete module execution over [VE].  Named hypotheses: [HVF]
        (every complete well-formed trace of the overlay presentation [VF]
        from [v0] is relaxed-linearizable to [nu]; verbatim the hypothesis
        of [RelaxedGSim.gsim_rel_lin], i.e. [ViewLHL.sound_pres nu VF v0])
        and [Hcomplete] (the execution ends with every call returned). *)
    Theorem rlhl_rel_lin (nu : list (Op F) -> Prop)
        (HH : RLHL2Hyps I R G M σ0 v0)
        (HVF : forall T v, vf_path VF v0 T v -> PrefixView.wf T -> PrefixView.complete T ->
                 rel_lin (@PrefixView.sel F) T (semi_independent F) nu)
        evs c
        (Hexec : module_execution_tagged VE M (initial_tagged_module VE σ0) evs c)
        (Hcomplete : forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) :
      rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) nu.
    Proof.
      destruct (rlhl_gsim HH) as (S & HS & H0).
      exact (gsim_rel_lin VE VF M v0 nu S σ0 evs c HS H0 Hexec Hcomplete HVF).
    Qed.

    (** The version over every underlay that implements [(nuE, IE)]
        ([ViewLHL.presentation_choice]): [VE] must be a complete
        presentation of [nuE] from [σ0] ([Hcomp]) and [VF] a sound
        presentation of [nuF] from [v0] ([Hsound], which is [HVF]). *)
    Theorem rlhl_rel_lin_pres (nuE : list (Op E) -> Prop) (nuF : list (Op F) -> Prop)
        (HH : RLHL2Hyps I R G M σ0 v0)
        (Hcomp : complete_pres nuE VE σ0) (Hsound : sound_pres nuF VF v0)
        (U : LTS E) (qU : State U) (Himpl : implements nuE U qU)
        evs c
        (Hexec : module_execution_tagged U M (initial_tagged_module U qU) evs c)
        (Hcomplete : forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) :
      rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) nuF.
    Proof.
      destruct (rlhl_gsim HH) as (S & HS & H0).
      exact (presentation_choice M nuE nuF VE σ0 VF v0 S Hcomp Hsound HS H0 U qU Himpl evs c Hexec Hcomplete).
    Qed.

    (** From derivations: [h_sem] follows from [MethodProvable] by
        [RelaxedHoareSound.method_sound]; the other five fields of
        [RLHL2Hyps] are side conditions on [I], [R], [G], [σ0], [v0]. *)
    Theorem rlhl2_of_provable
        (Hprov : forall t op, exists Ω Q, MethodProvable I R G M t op Ω Q)
        (Hgr : forall k k' s s', k <> k' -> G k s s' -> R k' s s')
        (Hir : forall k k' op tr ret s p', k <> k' ->
           program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
           poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
           R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr))
        (Hrr : forall k k' op r s p2, k <> k' -> I s ->
           poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
           R k' s (ps_mem s, p2, ps_ghost s))
        (Hok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool)
        (Hinit : I (σ0, PossOk v0 [], [])) :
      RLHL2Hyps I R G M σ0 v0.
    Proof.
      constructor; try assumption.
      intros t op. destruct (Hprov t op) as (Ω & Q & Hm). exact (method_sound I R G M t op Ω Q Hm).
    Qed.

    (** latest-review m-26: the paper-facing soundness theorem, in the
        shape of [RGILogic.soundness] (premise table in the header):
        derivations for every thread and operation, the five side
        conditions of [rlhl2_of_provable], [HVF] and [Hcomplete] give
        relaxed linearizability of every complete execution over [VE].  It
        is [rlhl2_of_provable] followed by [rlhl_rel_lin]; nothing is
        added. *)
    Theorem rlhl_sound (nu : list (Op F) -> Prop)
        (Hprov : forall t op, exists Ω Q, MethodProvable I R G M t op Ω Q)
        (Hgr : forall k k' s s', k <> k' -> G k s s' -> R k' s s')
        (Hir : forall k k' op tr ret s p', k <> k' ->
           program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
           poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
           R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr))
        (Hrr : forall k k' op r s p2, k <> k' -> I s ->
           poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
           R k' s (ps_mem s, p2, ps_ghost s))
        (Hok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool)
        (Hinit : I (σ0, PossOk v0 [], []))
        (HVF : forall T v, vf_path VF v0 T v -> PrefixView.wf T -> PrefixView.complete T ->
                 rel_lin (@PrefixView.sel F) T (semi_independent F) nu)
        evs c
        (Hexec : module_execution_tagged VE M (initial_tagged_module VE σ0) evs c)
        (Hcomplete : forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) :
      rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) nu.
    Proof.
      exact (rlhl_rel_lin nu (rlhl2_of_provable Hprov Hgr Hir Hrr Hok Hinit) HVF evs c Hexec Hcomplete).
    Qed.
  End Soundness.

  (** Effect-at-invocation overlays ([RelaxedHoareSpec.EI], author
      decision M-17): [HVF] is discharged by [ei_hvf], so the conclusion
      is relaxed linearizability to the sequential specification
      [seq_legal δ s0] with no hypothesis on the overlay. *)
  Section EISoundness.
    Context {E F : RelaxedSig.t} {VE : LTS E} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) (s0 : St).
    Context (I : Assn VE (EI δ)) (R G : CallKey F -> PRel VE (EI δ)) (M : RelaxedModuleImpl E F).
    Context (σ0 : State VE).

    Corollary rlhl_rel_lin_ei (HH : RLHL2Hyps I R G M σ0 (s0, []))
        evs c
        (Hexec : module_execution_tagged VE M (initial_tagged_module VE σ0) evs c)
        (Hcomplete : forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) :
      rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) (seq_legal δ s0).
    Proof. exact (rlhl_rel_lin I R G M σ0 (s0, []) (seq_legal δ s0) HH (ei_hvf δ s0) evs c Hexec Hcomplete). Qed.

    Corollary rlhl_rel_lin_ei_pres (nuE : list (Op E) -> Prop)
        (HH : RLHL2Hyps I R G M σ0 (s0, []))
        (Hcomp : complete_pres nuE VE σ0)
        (U : LTS E) (qU : State U) (Himpl : implements nuE U qU)
        evs c
        (Hexec : module_execution_tagged U M (initial_tagged_module U qU) evs c)
        (Hcomplete : forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) :
      rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) (seq_legal δ s0).
    Proof.
      exact (rlhl_rel_lin_pres I R G M σ0 (s0, []) nuE (seq_legal δ s0) HH Hcomp (ei_sound_pres δ s0)
               U qU Himpl evs c Hexec Hcomplete).
    Qed.
  End EISoundness.

End RelaxedHoareGSim.
