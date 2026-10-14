(** * RLHL, part 1: proof states with a ghost thread frontier, and the
      semantic per-call triple.

    This file fixes what an RLHL judgement *means* (task RLHL-1).
    [RelaxedHoareDag.v] and [RelaxedHoare.v] define the syntactic
    judgement; [RelaxedHoareSound.v] proves that every derivation implies
    the semantic triple of this file ([RelaxedHoareSound.method_sound]).
    The connection to [RelaxedGSim.GSimRel] (task RLHL-2) is not proved
    in this file; its hypotheses are stated as the Rocq record
    [RLHL2Hyps] at the end of this file, and it is proved in
    [RelaxedHoareGSim.v] ([RelaxedHoareGSim.rlhl_gsim]: [RLHL2Hyps]
    gives a [GSimRel] from the initial module for any number of calls;
    [rlhl_rel_lin], [rlhl_sound]: relaxed linearizability of the complete
    executions over the underlay LTS [VE]).

    ** Proof states

    A proof state is [(σ, ρ, γ)] ([PState]):
    - [σ : State VE], a state of the underlay LTS;
    - [ρ : Poss VF], a single possibility (abstract state plus
      linearization pool) of the overlay specification; this is LHL's
      [(σ, ρ, π)] (Assertion.v, [PUpdate]) with the per-thread map [π]
      replaced by the per-call pool of [RelaxedPossibility];
    - [γ : Ghost E F], the *ghost thread frontier* (iteration 2, author
      decision on latest-review B-5, research-intent §8): the pending
      underlay invocations of all active calls, each with its owner call
      key, in module queue order.  The component of thread [t] is
      [gthread t γ].  [γ] is one global list rather than a map
      [tid -> list] (so that states need no functional extensionality);
      its cross-thread order is extra information that no clause uses,
      because [inv_blocks] never relates events of different threads.

    Why the ghost: the module scheduler checks [tagged_can_cross] of an
    emitted event against *every* earlier queue event, including the
    events of other calls of the same thread.  For two invocations of one
    thread whose operations are not semi-independent this is the (F2)
    order *across calls*.  A per-call triple that only sees the call's own
    events must then cover schedules that the module never produces; the
    iteration-1 triple ([Iter1.MethodSem] below) is unsatisfiable for a
    correct overlapping counter
    ([RelaxedHoareChecks.Counter.counter_methodsem_unsat]).
    With the ghost, the emission of an invocation may assume that no older
    pending invocation of the thread blocks it ([ghost_emit]), and
    assertions (in particular [I]) may mention the pending invocations of
    the other calls of the thread.  Responses carry no cross-call
    constraint ((F2) relates invocations only; cross-call (F1)/(F3) would
    need equal underlay handles, which [trace_fresh] excludes in the
    module), so a response leaves the ghost unchanged and responses can
    still be placed lazily by the soundness proof.

    The module queue, the tags and the call pool are not part of the proof
    state.  RLHL-2 projects a module configuration [c] to
    [(tm_lts_state c, ρ, ghost_of (tm_queue c))]; the ghost is a function
    of the queue, and [ghost_of_schedule], [ghost_of_select] and
    [ghost_of_done] compute its change for the three module steps.

    The rely and the guarantee are indexed by an overlay call key
    [k = (t, h)]: [G k] covers the steps of [k] itself (its underlay
    events and its return-time linearization steps), [R k] covers
    everything other calls do while [k] is active: calls of other threads
    (the paper's [R_tau]) and other calls of the same thread ([R_alpha]).
    The call's own events are never in [R k]; when the tagged scheduler
    reorders them, they are handled as interference inside the call (see
    [RelaxedHoareDag.v]).  [R] and [G] are kept abstract.

    ** The semantic per-call triple, [CallTriple k op ret A]

    For a call [k] of [op] whose method body produced the tagged trace
    [tr] (with its guessed underlay responses) and the result [ret], a
    certificate is a family [A l] of assertions indexed by the list [l] of
    the call's not-yet-emitted events, in queue order (= the order of
    [tr]).  It must satisfy:

    - (emit, [ct_emit]) for every split [l = pre ++ m :: post] such that
      [m] is on the call's local frontier ([local_frontier pre m]), every
      ghost transition [ghost_emit k (untag m) γ γ'] (for an invocation:
      [m] is pending in [γ] as an entry of [k], no older entry of [γ]
      [inv_blocks] it, and [γ'] is [γ] without that entry; for a response:
      [γ' = γ]), every state [(σ, p, γ)] satisfying [A l] and [I], and
      every underlay step [σ --untag m--> σ'], there are abstract steps
      [poss_steps p p'] reaching [A (pre ++ post)] and [I] at
      [(σ', p', γ')], and the transition is in [G k];
    - (stable, [ct_stable]) every [A l] is stable under [R k];
    - (return, [ct_return]) [A []], [I] and [NoOwn k γ] (no pending entry
      of [k] is left; the module provides this through
      [owner_done_tagged], see [ghost_of_done]) imply [RetCond k op ret]:
      abstract steps (within [G k]) reach a possibility in which [k] has
      linearized with result [ret], and the abstract removal of [k] keeps
      [I].

    [MethodSem t op] quantifies universally over the overlay handle [h],
    every tagged trace [tr] and every result [ret] the body [M op t] can
    produce ([program_produces_tagged]: all guessed responses, all tags,
    early [tagged_resolve] steps included), and asks for a certificate
    with the (init) clause: from [I (σ, p, γ)] and the abstract invocation
    [poss_invoke p p'], both [I] and [A tr] hold at
    [(σ, p', γ ++ ghost_new (t, h) tr)], i.e. after the call's
    invocations have been appended to the ghost in trace order (exactly
    what [tagged_invoke] does to the queue, [ghost_of_schedule]).

    The certificate is *prophetic* (latest-review m-11): [exists A] comes
    after [forall tr ret], so [A] may depend on the guessed future
    responses and on the result, and the (init) clause may depend on the
    call's own future invocations.  This is sound for the module because
    [tagged_invoke] commits [tr] and [ret] at the overlay invocation, and
    every later step of the call follows [tr].

    Relation to the iteration-1 triple: [Iter1] keeps the iteration-1
    definitions verbatim under qualified names (a rename of the old
    definitions, needed because the canonical names now denote the
    redesigned triple).  [methodsem_of_iter1] shows that the new triple is
    implied by the old one (it is weaker); [RelaxedHoareChecks] shows that
    it is strictly weaker ([Counter.counter_methodsem_unsat] for [Iter1]
    against [Counter.counter_methodsem] for the new triple).

    [CallSafe] is a coinductive packaging without the certificate
    existential (only the abstract witnesses remain)
    ([triple_callsafe], [methodsem_safe]).

    ** What RLHL-2 needs ([RLHL2Hyps]; the bridge itself is in
       [RelaxedHoareGSim.v])

    RLHL-2 builds a [GSimRel] relation of the shape
    [S c p := I (tm_lts_state c, p, ghost_of (tm_queue c)) /\ ... /\
    for every active call k of op with result ret, A_k l_k (tm_lts_state
    c, p, ghost_of (tm_queue c))], where [l_k] is the owner sub-queue of
    [k] ([owner_subqueue]) and [A_k] a certificate of [k]
    ([RelaxedHoareGSim.RSim] has this shape, with [CallSafe] in place of
    the certificate).  The ghost
    needs no extra invariant in [S]: it is computed from the queue.  [S]
    must also say that the domain of the abstract pool is contained in
    the keys of the active calls (latest-review m-16): the module's
    [call_fresh] then gives the [lin_fresh] that the existential
    [poss_invoke] of [GSimRel] needs ([pool_dom_steps], [pool_dom_invoke],
    [pool_dom_return], [lin_fresh_of_dom], [poss_invoke_exists] below).
    [select_project] shows that an underlay step of the module either
    emits a local-frontier event of exactly one call (whose certificate
    uses [ct_emit], with the ghost transition of [ghost_of_select]) or
    leaves the sub-queue of a call untouched (whose certificate uses
    [ct_stable]).  The record [RLHL2Hyps] lists the remaining hypotheses:
    [G k ⊆ R k'] for [k <> k']; the invoke and return transitions of [k]
    (with their ghost effect) are in [R k']; [I] implies a [PossOk]
    possibility with a well-formed pool (latest-review m-9: this gives the
    existential [poss_return] that [GSimRel] needs, [retcond_return]);
    [I] holds initially; and [MethodSem t op] for every [t] and [op].
    For a closed system of two calls this shape is proved for every
    [RLHL2Hyps] instance ([RelaxedHoareChecks.gtwo_init],
    [RelaxedHoareChecks.gtwo_step]); the general list of calls is
    [RelaxedHoareGSim.rlhl_gsim] (relation [RelaxedHoareGSim.RSim]).

    Only one direction of the scheduling interface is proved
    (latest-review m-17): every underlay step of the module is a
    [local_frontier] emission of one call with a [ghost_emit] transition
    ([select_project], [ghost_of_select]).  The converse (a pending
    event with [local_frontier] and [ghost_emit] at [ghost_of q] is
    selectable) is not stated: it needs that the underlay keys of
    different calls are distinct ([trace_fresh], i.e. the module's
    [tm_used_underlay]) and that the tags of a call only name the call's
    own handles, neither of which is visible in the proof state.  So the
    triple may have to cover emissions the module never performs.

    Underlay-key freshness (latest-review M-16).  The triple carries no
    used-key information ([tm_used_underlay], [trace_fresh]): a
    certificate must also cover schedules in which a call re-invokes an
    underlay key [(thread, handle)] that another call of the same thread
    has already invoked, although the module excludes them.  Over an
    underlay whose invocation *overwrites* a per-key record this makes
    [RLHL2Hyps] unsatisfiable for a correct overlapping counter, for every
    choice of [I], [R] and [G], also when the records are keyed by
    [(thread, handle)] ([RelaxedHoareChecks.CounterHL.counter_ow_unsat]).
    The author's decision (research-intent §8, M-16) leaves the proof
    state and the triple unchanged and asks the underlay presentation to
    be handle-linear ([HandleLinear] below): an invocation of a key that
    is already invoked is disabled.  This is the paper's condition on
    plays (Appendix/gamemodel.tex:19, "no two moves with the same
    polarity and the same future handle"), and [ViewLHL.VT] satisfies it
    ([RelaxedHoareSpec.vt_handle_linear]).  Over a handle-linear [VE],
    once a key is used its re-invocation has no underlay step, so
    [ct_emit] is vacuous for it, and a guarantee may state that per-key
    records only grow;
    [RelaxedHoareChecks.CounterHL.counter_hl_rlhl2] is a closed
    [RLHL2Hyps] proof for the overlapping counter over such an underlay.
    Where the hypothesis enters: it is *not* a premise of [method_sound]
    nor a field of [RLHL2Hyps].  Soundness does not need it (the module
    performs fewer emissions than the triple covers, and an underlay with
    fewer steps only removes obligations); it is a property of the chosen
    [VE] that an instance uses when it discharges [RLHL2Hyps] (in the
    counter: the guarantee "records only grow" holds because an
    invocation is enabled only on an unused key).  The end-to-end
    theorem over every underlay ([RelaxedHoareGSim.rlhl_rel_lin_pres])
    needs a complete presentation such as [ViewLHL.VT nuE], which is
    handle-linear.  The intended RLHL-3 instance (author decision on
    latest-review M-18, research-intent §8) is [VE := ViewLHL.VT nuE]
    with the stamp-based overlay [VF := ViewLHL.VT nuF] ([Hsound :=
    ViewLHL.vt_sound]); it is not done.  The effect-at-invocation
    overlays [RelaxedHoareSpec.EI] apply to invocation-ordered underlays
    and are not expected to have an instance over [ViewLHL.VT] for
    ordered same-thread operations
    ([RelaxedHoareChecks.CounterRelLin.vt_junk]; for the counter,
    [RelaxedHoareChecks.CounterRelLin.counter_vt_no_rlhl2]).

    Scope: one possibility (no sets, no future-dependent linearization
    points); generic underlay LTS [VE] (nothing about a particular memory
    model); the tagged module semantics has no error transition, so there
    is no error clause (partial correctness).  No definition or theorem of
    the logic assumes a property of [semi_independent] (in particular not
    [RelaxedSig.well_formed]).  The ghost records exactly the cross-call
    constraint of the Coq scheduler ([tagged_can_cross] between events of
    different calls of one thread: (F2) between pending invocations).
    The paper's cross-invocation clause (Appendix/programlogic.tex:286)
    quantifies over [event^P(c(π'))], the P-moves of the E-side play of
    an older active call; by the polarity convention
    (Appendix/gamemodel.tex:171 and :346: [λ_E(e(a)) = O] and
    [λ_{A⊸B} = dual(λ_A) + λ_B]) these are exactly the pending underlay
    invocations, so the paper and the ghost constrain the same events
    (latest-review m-15).  Residual difference, not checked: the paper
    relates the older call [π'] to [π] by [hb_s] (:289), the Coq by "same
    thread, older in the module queue". *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.

Import ListNotations.


Module RelaxedHoareBase.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.

  (** ** The ghost thread frontier *)

  Definition Ghost (E F : RelaxedSig.t) : Type := list (ScheduledEvent E F).

  (** The cross-call constraint the module enforces between two pending
      invocations of one thread: (F2). *)
  Definition inv_blocks {E : RelaxedSig.t} (e m : ThreadEvent E) : Prop :=
    te_tid E e = te_tid E m /\
    match te_ev E e, te_ev E m with
    | InvEv _ o1, InvEv _ o2 => ~ semi_independent E o1 o2
    | _, _ => False
    end.

  Fixpoint inv_events {E : RelaxedSig.t} (l : list (ThreadEvent E)) : list (ThreadEvent E) :=
    match l with
    | [] => []
    | ev :: l' =>
        match te_ev E ev with
        | InvEv _ _ => ev :: inv_events l'
        | ResEv _ _ _ => inv_events l'
        end
    end.

  (** The ghost entries of a new call: its invocations, in trace order. *)
  Definition ghost_new {E F : RelaxedSig.t} (k : CallKey F) (tr : list (TaggedEvent E)) :
      Ghost E F :=
    map (Build_ScheduledEvent k) (inv_events (map untag tr)).

  (** The ghost transition of an emitted event of [k]: an invocation must
      be pending as an entry of [k] and on the thread frontier; a response
      leaves the ghost unchanged.  A [Definition] by [match] (not an
      [Inductive]), so that its inversion needs no [existT] equations. *)
  Definition ghost_emit {E F : RelaxedSig.t} (k : CallKey F) (ev : ThreadEvent E)
      (g g' : Ghost E F) : Prop :=
    match te_ev E ev with
    | InvEv _ _ =>
        exists g1 g2, g = g1 ++ Build_ScheduledEvent k ev :: g2 /\ g' = g1 ++ g2 /\
                      Forall (fun e => ~ inv_blocks (se_event e) ev) g1
    | ResEv _ _ _ => g' = g
    end.

  Definition NoOwn {E F : RelaxedSig.t} (k : CallKey F) (g : Ghost E F) : Prop :=
    forall e, In e g -> se_owner e <> k.

  (** The component of thread [t]. *)
  Definition gthread {E F : RelaxedSig.t} (t : tid) (g : Ghost E F) : Ghost E F :=
    filter (fun e => Pos.eqb (te_tid E (se_event e)) t) g.

  (** The ghost of a tagged module queue: its pending invocations. *)
  Fixpoint ghost_of {E F : RelaxedSig.t} (q : TaggedQueue E F) : Ghost E F :=
    match q with
    | [] => []
    | x :: q' =>
        match te_ev E (untag (ts_event x)) with
        | InvEv _ _ => untag_scheduled x :: ghost_of q'
        | ResEv _ _ _ => ghost_of q'
        end
    end.

  Section GhostFacts.
    Context {E F : RelaxedSig.t}.

    Lemma inv_events_app (l1 l2 : list (ThreadEvent E)) :
      inv_events (l1 ++ l2) = inv_events l1 ++ inv_events l2.
    Proof.
      induction l1 as [| ev l1 IH]; cbn; [reflexivity |].
      destruct (te_ev E ev); cbn; rewrite ?IH; reflexivity.
    Qed.

    Lemma inv_events_in (l : list (ThreadEvent E)) ev :
      In ev (inv_events l) -> In ev l /\ is_invocation ev.
    Proof.
      induction l as [| ev0 l IH]; cbn; [intros [] |].
      destruct (te_ev E ev0) eqn:Hev; intros Hin.
      - destruct Hin as [<- | Hin].
        + split; [left; reflexivity |]. unfold is_invocation. rewrite Hev. exact Logic.I.
        + destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
      - destruct (IH Hin) as [H1 H2]. split; [right; exact H1 | exact H2].
    Qed.

    Lemma ghost_of_app (q1 q2 : TaggedQueue E F) :
      ghost_of (q1 ++ q2) = ghost_of q1 ++ ghost_of q2.
    Proof.
      induction q1 as [| x q1 IH]; cbn; [reflexivity |].
      destruct (te_ev E (untag (ts_event x))); cbn; rewrite ?IH; reflexivity.
    Qed.

    Lemma ghost_of_schedule (k : CallKey F) (tr : list (TaggedEvent E)) :
      ghost_of (schedule_trace_tagged k tr) = ghost_new k tr.
    Proof.
      unfold ghost_new, schedule_trace_tagged.
      induction tr as [| m tr IH]; cbn; [reflexivity |].
      destruct (te_ev E (untag m)); cbn; rewrite ?IH; reflexivity.
    Qed.

    Lemma ghost_of_in (q : TaggedQueue E F) e :
      In e (ghost_of q) -> exists x, In x q /\ e = untag_scheduled x.
    Proof.
      induction q as [| x q IH]; cbn; [intros [] |].
      destruct (te_ev E (untag (ts_event x))); intros Hin.
      - destruct Hin as [<- | Hin]; [exists x; split; [left |]; reflexivity |].
        destruct (IH Hin) as (y & Hy & ->). exists y. split; [right; exact Hy | reflexivity].
      - destruct (IH Hin) as (y & Hy & ->). exists y. split; [right; exact Hy | reflexivity].
    Qed.

    (** A crossing allowed by the scheduler is never an (F2) block. *)
    Lemma cross_not_blocks (x c : TaggedEvent E) :
      tagged_can_cross x c -> ~ inv_blocks (untag x) (untag c).
    Proof.
      intros [Hne | [_ Hnm]] [Htid Hb]; [exact (Hne Htid) |].
      unfold must_precede in Hnm.
      destruct (te_ev E (untag x)), (te_ev E (untag c)); contradiction.
    Qed.

    Lemma select_split (cand : TaggedScheduledEvent E F) (q q' : TaggedQueue E F) :
      select_frontier_tagged cand q q' ->
      exists pre post, q = pre ++ cand :: post /\ q' = pre ++ post /\
        Forall (fun e => tagged_can_cross (ts_event e) (ts_event cand)) pre.
    Proof.
      intros Hsel. induction Hsel as [suffix | earlier queue queue' Hcross Hsel IH].
      - exists [], suffix. auto.
      - destruct IH as (pre & post & -> & -> & Hall).
        exists (earlier :: pre), post. cbn. auto.
    Qed.

    (** The ghost transition of an underlay step of the module. *)
    Lemma ghost_of_select (cand : TaggedScheduledEvent E F) (q q' : TaggedQueue E F) :
      select_frontier_tagged cand q q' ->
      ghost_emit (ts_owner cand) (untag (ts_event cand)) (ghost_of q) (ghost_of q').
    Proof.
      intros Hsel. destruct (select_split _ _ _ Hsel) as (pre & post & -> & -> & Hall).
      rewrite !ghost_of_app. cbn [ghost_of]. unfold ghost_emit.
      destruct (te_ev E (untag (ts_event cand))) eqn:Hev.
      - exists (ghost_of pre), (ghost_of post). split; [reflexivity |]. split; [reflexivity |].
        apply Forall_forall. intros e He. destruct (ghost_of_in _ _ He) as (x & Hx & ->).
        cbn. apply cross_not_blocks. rewrite Forall_forall in Hall. exact (Hall x Hx).
      - reflexivity.
    Qed.

    (** At an overlay return the call has no pending ghost entry. *)
    Lemma ghost_of_done (k : CallKey F) (q : TaggedQueue E F) :
      owner_done_tagged k q -> NoOwn k (ghost_of q).
    Proof.
      intros Hdone e He Heq. destruct (ghost_of_in _ _ He) as (x & Hx & ->).
      apply Hdone. cbn in Heq. rewrite <- Heq. apply in_map. exact Hx.
    Qed.

    Lemma NoOwn_app (k : CallKey F) (g1 g2 : Ghost E F) :
      NoOwn k g1 -> NoOwn k g2 -> NoOwn k (g1 ++ g2).
    Proof. intros H1 H2 e He. apply in_app_or in He. destruct He; auto. Qed.

    Lemma ghost_new_owner (k : CallKey F) (tr : list (TaggedEvent E)) (e : ScheduledEvent E F) :
      In e (ghost_new k tr) -> se_owner e = k.
    Proof.
      unfold ghost_new. intros He. apply in_map_iff in He. destruct He as (ev & <- & _). reflexivity.
    Qed.
  End GhostFacts.

  (** ** Proof states, assertions, relations *)

  Definition PState {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) : Type :=
    (State VE * Poss VF * Ghost E F)%type.

  Definition ps_mem {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F} (s : PState VE VF) : State VE :=
    fst (fst s).
  Definition ps_poss {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F} (s : PState VE VF) : Poss VF :=
    snd (fst s).
  Definition ps_ghost {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F} (s : PState VE VF) : Ghost E F :=
    snd s.

  Definition Assn {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) : Type :=
    PState VE VF -> Prop.

  Definition PRel {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) : Type :=
    PState VE VF -> PState VE VF -> Prop.

  (** The local frontier of one call: [m] may be emitted before the
      pending events [pre] of the same call that precede it in the queue
      exactly when none of them must precede it by (F1)--(F3). *)
  Definition local_frontier {E : RelaxedSig.t}
      (pre : list (TaggedEvent E)) (m : TaggedEvent E) : Prop :=
    Forall (fun e => ~ must_precede e m) pre.

  Section Assertions.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF).

    (** Stability under a relation, relative to the global invariant at the
        target (as [Assertion.Stable]: [R ⊚ P ∧ I ⇒ P]). *)
    Definition Stable (r : PRel VE VF) (P : Assn VE VF) : Prop :=
      forall s s', P s -> r s s' -> I s' -> P s'.

    (** Implication relative to the invariant. *)
    Definition Impl (P Q : Assn VE VF) : Prop :=
      forall s, I s -> P s -> Q s.

    (** An underlay event [ev] of the call [k] from [P] reaches [Q] after
        abstract linearization steps, within [g], preserving [I]; the
        ghost moves by [ghost_emit k ev]. *)
    Definition EvUpdate (g : PRel VE VF) (k : CallKey F) (ev : ThreadEvent E)
        (P Q : Assn VE VF) : Prop :=
      forall σ p γ γ', P (σ, p, γ) -> I (σ, p, γ) -> ghost_emit k ev γ γ' ->
        forall σ', Step VE ev σ σ' ->
          exists p', poss_steps VF p p' /\ Q (σ', p', γ') /\ I (σ', p', γ') /\
                     g (σ, p, γ) (σ', p', γ').

    (** The state right after the overlay invocation of [k] ([Ginv ⊚ I] of
        LHL), whose own invocations [evs] (with footprint [Ω]) were
        appended to the ghost. *)
    Definition PostInvoke (k : CallKey F) (op : Sig.op (RelaxedSig.effect F))
        (Ω : list (ThreadEvent E) -> Prop) : Assn VE VF :=
      fun s => exists p0 γ0 evs,
        I (ps_mem s, p0, γ0) /\
        poss_invoke VF (fst k) (snd k) op p0 (ps_poss s) /\
        ps_ghost s = γ0 ++ map (Build_ScheduledEvent k) evs /\
        Ω evs /\
        Forall (fun ev => te_tid E ev = fst k /\ is_invocation ev) evs.

    Lemma Stable_and r P Q :
      Stable r P -> Stable r Q -> Stable r (fun s => P s /\ Q s).
    Proof. intros HP HQ s s' [Hp Hq] Hr HI. split; eauto. Qed.

    Lemma Stable_true r : Stable r (fun _ => True).
    Proof. intros; constructor. Qed.

    Lemma Stable_mono (r r' : PRel VE VF) P :
      (forall s s', r s s' -> r' s s') -> Stable r' P -> Stable r P.
    Proof. intros Hsub HP s s' Hs Hr HI. eapply HP; eauto. Qed.
  End Assertions.

  (** ** The semantic per-call triple *)

  Section Triple.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF).
    Context (R G : CallKey F -> PRel VE VF).

    (** What must hold when the call [k] returns [r]: [poss_steps] within
        [G k] reach a possibility where [k] is linearized with result [r]
        (LHL's [Qlin]), [I] holds there, and the abstract removal of [k]
        keeps [I] (LHL's [Qret]). *)
    Definition RetCond (k : CallKey F) (op : Sig.op (RelaxedSig.effect F))
        (r : Sig.ar op) : Assn VE VF :=
      fun s => exists p1,
        poss_steps VF (ps_poss s) p1 /\
        (exists v pool, p1 = PossOk v pool /\ lin_lookup k (ls_linr op r) pool) /\
        I (ps_mem s, p1, ps_ghost s) /\
        clos_refl _ (G k) s (ps_mem s, p1, ps_ghost s) /\
        (forall p2, poss_return VF (fst k) (snd k) op r p1 p2 -> I (ps_mem s, p2, ps_ghost s)).

    (** The semantic per-call triple; see the file header. *)
    Record CallTriple (k : CallKey F) (op : Sig.op (RelaxedSig.effect F))
        (ret : Sig.ar op) (A : list (TaggedEvent E) -> Assn VE VF) : Prop := {
      ct_emit : forall pre m post, local_frontier pre m ->
        forall σ p γ γ', ghost_emit k (untag m) γ γ' ->
        A (pre ++ m :: post) (σ, p, γ) -> I (σ, p, γ) ->
        forall σ', Step VE (untag m) σ σ' ->
          exists p', poss_steps VF p p' /\ A (pre ++ post) (σ', p', γ') /\
                     I (σ', p', γ') /\ G k (σ, p, γ) (σ', p', γ');
      ct_stable : forall l, Stable I (R k) (A l);
      ct_return : forall s, A [] s -> I s -> NoOwn k (ps_ghost s) -> RetCond k op ret s
    }.

    Context (M : RelaxedModuleImpl E F).

    (** The method-level semantic triple: universal over the overlay
        handle, every produced tagged trace and every produced result. *)
    Definition MethodSem (t : tid) (op : Sig.op (RelaxedSig.effect F)) : Prop :=
      forall (h : RelaxedSig.handle F) tr ret,
        program_produces_tagged t (M op t) tr ret ->
        exists A, CallTriple (t, h) op ret A /\
          (forall σ p γ p', I (σ, p, γ) -> poss_invoke VF t h op p p' ->
             I (σ, p', γ ++ ghost_new (t, h) tr) /\ A tr (σ, p', γ ++ ghost_new (t, h) tr)).

    (** Packaging of the per-call obligations without the certificate
        existential. *)
    CoInductive CallSafe (k : CallKey F) (op : Sig.op (RelaxedSig.effect F))
        (ret : Sig.ar op) : list (TaggedEvent E) -> PState VE VF -> Prop :=
    | cs_intro l s
        (Hinv : I s)
        (Hemit : forall pre m post, l = pre ++ m :: post -> local_frontier pre m ->
           forall γ' σ', ghost_emit k (untag m) (ps_ghost s) γ' ->
             Step VE (untag m) (ps_mem s) σ' ->
             exists p', poss_steps VF (ps_poss s) p' /\ I (σ', p', γ') /\
                        G k s (σ', p', γ') /\ CallSafe k op ret (pre ++ post) (σ', p', γ'))
        (Hrely : forall s', R k s s' -> I s' -> CallSafe k op ret l s')
        (Hret : l = [] -> NoOwn k (ps_ghost s) -> RetCond k op ret s) :
      CallSafe k op ret l s.

    Lemma triple_callsafe k op ret A :
      CallTriple k op ret A ->
      forall l s, I s -> A l s -> CallSafe k op ret l s.
    Proof.
      intros [Hemit Hstab Hret]. cofix CIH. intros l s HI HA.
      constructor.
      - exact HI.
      - intros pre m post -> Hfr γ' σ' Hge Hstep. destruct s as [[σ p] γ].
        destruct (Hemit pre m post Hfr σ p γ γ' Hge HA HI σ' Hstep)
          as (p' & Hps & HA' & HI' & HG).
        exists p'. split; [exact Hps |]. split; [exact HI' |]. split; [exact HG |].
        apply CIH; assumption.
      - intros s' HR HI'. apply CIH; [exact HI' |]. eapply Hstab; eauto.
      - intros -> Hno. apply Hret; assumption.
    Qed.

    Definition MethodSafe (t : tid) (op : Sig.op (RelaxedSig.effect F)) : Prop :=
      forall (h : RelaxedSig.handle F) tr ret,
        program_produces_tagged t (M op t) tr ret ->
        forall σ p γ p', I (σ, p, γ) -> poss_invoke VF t h op p p' ->
          I (σ, p', γ ++ ghost_new (t, h) tr) /\
          CallSafe (t, h) op ret tr (σ, p', γ ++ ghost_new (t, h) tr).

    Corollary methodsem_safe t op : MethodSem t op -> MethodSafe t op.
    Proof.
      intros Hsem h tr ret Hprod σ p γ p' HI Hinv.
      destruct (Hsem h tr ret Hprod) as (A & Htriple & Hinit).
      destruct (Hinit σ p γ p' HI Hinv) as [HI' HA].
      split; [exact HI' |]. eapply triple_callsafe; eauto.
    Qed.
  End Triple.

  (** ** The iteration-1 triple, kept under qualified names

      Verbatim copies of the iteration-1 definitions (proof state
      [State VE * Poss VF], no ghost).  Only the paths changed
      ([RelaxedHoareBase.Iter1.MethodSem] instead of
      [RelaxedHoareBase.MethodSem]).  Used by the regression theorem
      [RelaxedHoareChecks.Counter.counter_methodsem_unsat]. *)

  Module Iter1.
    Definition PState {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) : Type :=
      (State VE * Poss VF)%type.

    Definition Assn {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) : Type :=
      PState VE VF -> Prop.

    Definition PRel {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) : Type :=
      PState VE VF -> PState VE VF -> Prop.

    Section Iter1Triple.
      Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
      Context (I : Assn VE VF).

      Definition Stable (r : PRel VE VF) (P : Assn VE VF) : Prop :=
        forall s s', P s -> r s s' -> I s' -> P s'.

      Context (R G : CallKey F -> PRel VE VF).

      Definition RetCond (k : CallKey F) (op : Sig.op (RelaxedSig.effect F))
          (r : Sig.ar op) : Assn VE VF :=
        fun s => exists p1,
          poss_steps VF (snd s) p1 /\
          (exists v pool, p1 = PossOk v pool /\ lin_lookup k (ls_linr op r) pool) /\
          I (fst s, p1) /\
          clos_refl _ (G k) s (fst s, p1) /\
          (forall p2, poss_return VF (fst k) (snd k) op r p1 p2 -> I (fst s, p2)).

      Record CallTriple (k : CallKey F) (op : Sig.op (RelaxedSig.effect F))
          (ret : Sig.ar op) (A : list (TaggedEvent E) -> Assn VE VF) : Prop := {
        ct_emit : forall pre m post, local_frontier pre m ->
          forall σ p, A (pre ++ m :: post) (σ, p) -> I (σ, p) ->
          forall σ', Step VE (untag m) σ σ' ->
            exists p', poss_steps VF p p' /\ A (pre ++ post) (σ', p') /\
                       I (σ', p') /\ G k (σ, p) (σ', p');
        ct_stable : forall l, Stable (R k) (A l);
        ct_return : forall s, A [] s -> I s -> RetCond k op ret s
      }.

      Context (M : RelaxedModuleImpl E F).

      Definition MethodSem (t : tid) (op : Sig.op (RelaxedSig.effect F)) : Prop :=
        forall (h : RelaxedSig.handle F) tr ret,
          program_produces_tagged t (M op t) tr ret ->
          exists A, CallTriple (t, h) op ret A /\
            (forall σ p p', I (σ, p) -> poss_invoke VF t h op p p' ->
               I (σ, p') /\ A tr (σ, p')).
    End Iter1Triple.
  End Iter1.

  (** The redesigned triple is implied by the iteration-1 triple (read
      through the projection that forgets the ghost). *)
  Section FromIter1.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Iter1.Assn VE VF) (R G : CallKey F -> Iter1.PRel VE VF).
    Context (M : RelaxedModuleImpl E F).

    Definition drop (s : PState VE VF) : Iter1.PState VE VF := fst s.

    Theorem methodsem_of_iter1 t op :
      Iter1.MethodSem I R G M t op ->
      MethodSem (fun s => I (drop s)) (fun k s s' => R k (drop s) (drop s'))
        (fun k s s' => G k (drop s) (drop s')) M t op.
    Proof.
      intros Hsem h tr ret Hprod.
      destruct (Hsem h tr ret Hprod) as (A & [Hemit Hstab Hret] & Hinit).
      exists (fun l s => A l (drop s)). split.
      - constructor.
        + intros pre m post Hfr σ p γ γ' _ HA HI σ' Hstep.
          destruct (Hemit pre m post Hfr σ p HA HI σ' Hstep) as (p' & Hps & HA' & HI' & HG).
          exists p'. auto.
        + intros l s s' HA HR HI. exact (Hstab l (drop s) (drop s') HA HR HI).
        + intros [[σ p] γ] HA HI _.
          destruct (Hret (σ, p) HA HI) as (p1 & Hps & Hlk & HI1 & HG & Hrm).
          exists p1. split; [exact Hps |]. split; [exact Hlk |]. split; [exact HI1 |].
          split; [| exact Hrm].
          cbn in HG |- *. remember (σ, p1) as y eqn:Hy. destruct HG as [y0 HG | ].
          * apply r_step. subst y0. exact HG.
          * injection Hy as ->. apply r_refl.
      - intros σ p γ p' HI Hinv. exact (Hinit σ p p' HI Hinv).
    Qed.
  End FromIter1.

  (** ** Owner sub-queues (for RLHL-2)

      [owner_subqueue k q l]: [l] is the list of events of the global
      tagged queue [q] owned by [k], in queue order.  Relational, so that
      no decidable equality on handles is needed. *)

  Section Subqueue.
    Context {E F : RelaxedSig.t}.

    Inductive owner_subqueue (k : CallKey F) :
        TaggedQueue E F -> list (TaggedEvent E) -> Prop :=
    | osq_nil : owner_subqueue k [] []
    | osq_own m q l :
        owner_subqueue k q l ->
        owner_subqueue k (Build_TaggedScheduledEvent k m :: q) (m :: l)
    | osq_other x q l :
        ts_owner x <> k ->
        owner_subqueue k q l ->
        owner_subqueue k (x :: q) l.

    (** An underlay step either emits a local-frontier event of [k] or
        does not touch the sub-queue of [k]. *)
    Lemma select_project k q l cand q' :
      owner_subqueue k q l ->
      Forall (fun m => te_tid E (untag m) = fst k) l ->
      select_frontier_tagged cand q q' ->
      (ts_owner cand = k /\
       exists pre post, l = pre ++ ts_event cand :: post /\
                        local_frontier pre (ts_event cand) /\
                        owner_subqueue k q' (pre ++ post))
      \/ (ts_owner cand <> k /\ owner_subqueue k q' l).
    Proof.
      intros Hosq Htid Hsel. revert l Hosq Htid.
      induction Hsel as [suffix | earlier queue queue' Hcross Hsel IH];
        intros l Hosq Htid.
      - inversion Hosq as [| m q0 l0 Hosq0 Heq1 Heq2 | x q0 l0 Hne Hosq0 Heq1 Heq2]; subst.
        + left. split; [reflexivity |]. exists [], l0. cbn.
          split; [reflexivity |]. split; [constructor | exact Hosq0].
        + right. split; assumption.
      - inversion Hosq as [| m q0 l0 Hosq0 Heq1 Heq2 | x q0 l0 Hne Hosq0 Heq1 Heq2]; subst.
        + inversion Htid as [| ? ? Hm Htid0]; subst.
          destruct (IH l0 Hosq0 Htid0) as
            [(Hown & pre & post & -> & Hfr & Hosq') | (Hne & Hosq')].
          * left. split; [exact Hown |]. exists (m :: pre), post. cbn.
            split; [reflexivity |]. split.
            -- constructor; [| exact Hfr].
               destruct Hcross as [Hneq | [_ Hno]]; [| exact Hno].
               exfalso. apply Hneq. cbn. rewrite Hm.
               rewrite Forall_forall in Htid0. symmetry. apply Htid0.
               apply in_or_app. right. left. reflexivity.
            -- apply osq_own. exact Hosq'.
          * right. split; [exact Hne |]. apply osq_own. exact Hosq'.
        + destruct (IH l Hosq0 Htid) as
            [(Hown & pre & post & -> & Hfr & Hosq') | (Hne' & Hosq')].
          * left. split; [exact Hown |]. exists pre, post.
            split; [reflexivity |]. split; [exact Hfr |]. apply osq_other; assumption.
          * right. split; [exact Hne' |]. apply osq_other; assumption.
    Qed.

    Lemma osq_app k q1 l1 q2 l2 :
      owner_subqueue k q1 l1 -> owner_subqueue k q2 l2 ->
      owner_subqueue k (q1 ++ q2) (l1 ++ l2).
    Proof.
      intros H1 H2. induction H1; cbn.
      - exact H2.
      - apply osq_own. assumption.
      - apply osq_other; assumption.
    Qed.

    Lemma osq_schedule_own k tr :
      owner_subqueue k (schedule_trace_tagged k tr) tr.
    Proof.
      induction tr as [| m tr IH]; cbn; [constructor |]. apply osq_own. exact IH.
    Qed.

    Lemma osq_schedule_other k k' tr :
      k' <> k -> owner_subqueue k (schedule_trace_tagged k' tr) [].
    Proof.
      intros Hne. induction tr as [| m tr IH]; cbn; [constructor |].
      apply osq_other; [exact Hne | exact IH].
    Qed.

    Lemma osq_none k q :
      (forall x, In x q -> ts_owner x <> k) -> owner_subqueue k q [].
    Proof.
      induction q as [| x q IH]; intros Hall; [constructor |].
      apply osq_other.
      - apply Hall. left. reflexivity.
      - apply IH. intros y Hy. apply Hall. right. exact Hy.
    Qed.

    Lemma osq_done k q l :
      owner_done_tagged k q -> owner_subqueue k q l -> l = [].
    Proof.
      intros Hdone Hosq. induction Hosq as [| m q l Hosq IH | x q l Hne Hosq IH].
      - reflexivity.
      - exfalso. apply Hdone. left. reflexivity.
      - apply IH. intros Hin. apply Hdone. right. exact Hin.
    Qed.

    Lemma osq_owner_in k q l m :
      owner_subqueue k q l -> In m l -> In (Build_TaggedScheduledEvent k m) q.
    Proof.
      intros Hosq. induction Hosq as [| m0 q l Hosq IH | x q l Hne Hosq IH]; intros Hin.
      - destruct Hin.
      - destruct Hin as [<- | Hin]; [left; reflexivity | right; apply IH; exact Hin].
      - right. apply IH. exact Hin.
    Qed.
  End Subqueue.

  (** ** The hypotheses of RLHL-2 (latest-review m-9, m-10)

      Stated, not used here (used in [RelaxedHoareGSim]; every field
      enters the proof of [rlhl_gsim]).  [h_guar_rely]: a call's guarantee is in the
      rely of every other call.  [h_invoke_rely] / [h_return_rely]: the
      abstract invoke (with the new ghost entries) and return transitions
      of a call are in the rely of every other call.  [h_ok]: [I] gives a
      [PossOk] possibility with a duplicate-free pool, which makes the
      [∀ p2] of [RetCond] existential ([retcond_return]).  [h_init]: the
      initial state.  [h_sem]: every method satisfies the triple. *)

  Section Hyps.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.

    Record RLHL2Hyps (I : Assn VE VF) (R G : CallKey F -> PRel VE VF)
        (M : RelaxedModuleImpl E F) (σ0 : State VE) (v0 : State VF) : Prop := {
      h_sem : forall t op, MethodSem I R G M t op;
      h_guar_rely : forall k k' s s', k <> k' -> G k s s' -> R k' s s';
      h_invoke_rely : forall k k' op tr ret s p', k <> k' ->
        program_produces_tagged (fst k) (M op (fst k)) tr ret -> I s ->
        poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
        R k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr);
      h_return_rely : forall k k' op r s p2, k <> k' -> I s ->
        poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
        R k' s (ps_mem s, p2, ps_ghost s);
      h_ok : forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool;
      h_init : I (σ0, PossOk v0 [], [])
    }.

    Lemma lin_remove_exists (key : CallKey F) st (pool : LinPool F) :
      lin_pool_well_formed pool -> lin_lookup key st pool ->
      exists pool', lin_remove key st pool pool'.
    Proof.
      induction pool as [| e pool IH]; intros Hwf Hl; [destruct Hl |].
      unfold lin_pool_well_formed, lin_domain in Hwf. cbn in Hwf.
      apply NoDup_cons_iff in Hwf as [Hnin Hwf].
      destruct Hl as [He | Hl].
      - subst e. eexists. apply lin_remove_here.
      - destruct (IH Hwf Hl) as (pool' & Hu). exists (e :: pool').
        apply lin_remove_next; [| exact Hu].
        intros Hk. apply Hnin. rewrite Hk. apply in_map_iff.
        exists (make_lin_entry key st). split; [apply lin_key_make_lin_entry | exact Hl].
    Qed.

    (** m-9: with [h_ok], [RetCond] yields the existential return step that
        [GSimRel]'s return clause needs. *)
    Lemma retcond_return (I : Assn VE VF) (G : CallKey F -> PRel VE VF) k op r s :
      (forall s, I s -> exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool) ->
      RetCond I G k op r s ->
      exists p1 p2, poss_steps VF (ps_poss s) p1 /\
        poss_return VF (fst k) (snd k) op r p1 p2 /\ I (ps_mem s, p2, ps_ghost s).
    Proof.
      intros Hok (p1 & Hps & (v & pool & -> & Hlk) & HI1 & _ & Hrm).
      destruct (Hok _ HI1) as (v' & pool' & Hp & Hwf). cbn in Hp.
      injection Hp as <- <-.
      destruct (lin_remove_exists k _ pool Hwf Hlk) as (pool2 & Hrem).
      exists (PossOk v pool), (PossOk v pool2). split; [exact Hps |].
      assert (Hret : poss_return VF (fst k) (snd k) op r (PossOk v pool) (PossOk v pool2)).
      { constructor. destruct k as [t h]. exact Hrem. }
      split; [exact Hret | apply Hrm; exact Hret].
    Qed.

    (** *** The pool domain (latest-review m-16)

        RLHL-2's relation [S] carries "the domain of the abstract pool is
        contained in the active call keys" ([pool_dom_sub (active c)]).
        Abstract linearization steps keep the domain, the abstract
        invocation adds the invoked key, the abstract return removes the
        returned key; with [call_fresh] the domain fact gives the
        [lin_fresh] that [poss_invoke] needs. *)

    Definition pool_dom_sub (P : CallKey F -> Prop) (p : Poss VF) : Prop :=
      exists v pool, p = PossOk v pool /\ forall k, In k (lin_domain pool) -> P k.

    Lemma pool_dom_steps P p p' :
      poss_steps VF p p' -> p' <> PossError -> pool_dom_sub P p -> pool_dom_sub P p'.
    Proof.
      intros Hs Hne (v & pool & -> & Hd). destruct p' as [v' pool' |]; [| contradiction Hne; reflexivity].
      exists v', pool'. split; [reflexivity |].
      rewrite <- (poss_steps_ok_domain VF _ _ _ _ Hs). exact Hd.
    Qed.

    Lemma pool_dom_invoke P t h op p p' :
      poss_invoke VF t h op p p' -> pool_dom_sub P p ->
      pool_dom_sub (fun k => P k \/ k = (t, h)) p'.
    Proof.
      intros Hi (v & pool & -> & Hd). inversion Hi as [v0 pool0 pool' Hins]; subst.
      destruct Hins as [pool0 Hfresh]. exists v, (make_lin_entry (t, h) (ls_inv op) :: pool0).
      split; [reflexivity |]. intros k [Hk | Hk]; [right; exact (eq_sym Hk) | left; exact (Hd k Hk)].
    Qed.

    Lemma pool_dom_return P t h op r p p' :
      poss_return VF t h op r p p' ->
      (forall v pool, p = PossOk v pool -> lin_pool_well_formed pool) ->
      pool_dom_sub P p -> pool_dom_sub (fun k => P k /\ k <> (t, h)) p'.
    Proof.
      intros Hr Hwf (v & pool & -> & Hd). inversion Hr as [v0 pool0 pool' Hrem]; subst.
      exists v, pool'. split; [reflexivity |]. intros k Hk. split.
      - apply Hd. exact (lin_remove_domain_subset _ _ _ _ Hrem k Hk).
      - intros ->. exact (lin_remove_absent _ _ _ _ Hrem (Hwf _ _ eq_refl) Hk).
    Qed.

    Lemma lin_fresh_of_dom P k v pool :
      pool_dom_sub P (PossOk v pool) -> ~ P k -> lin_fresh k pool.
    Proof.
      intros (v' & pool' & Heq & Hd) Hn Hin. injection Heq as <- <-. exact (Hn (Hd k Hin)).
    Qed.

    Lemma poss_invoke_exists t h op v pool :
      lin_fresh (t, h) pool -> exists p', poss_invoke VF t h op (PossOk v pool) p'.
    Proof. intros Hf. eexists. constructor. constructor. exact Hf. Qed.
  End Hyps.

  (** ** Handle-linear underlay presentations (author decision M-16)

      [HandleLinear VE used]: [used σ k] records that the underlay key
      [k = (thread, handle)] has been invoked in [σ]; an invocation step
      marks its key used ([hl_inv_used]), no step forgets a used key
      ([hl_mono]), and an invocation of a used key is disabled
      ([hl_fresh]).  Along every path of a handle-linear [VE] each key is
      therefore invoked at most once
      ([RelaxedHoareSpec.hl_path_inv_unique]), which is the invocation half
      of Appendix/gamemodel.tex:19 ("no two moves with the same polarity
      and the same future handle") and of [PrefixView.wf].  [used] cannot
      be chosen trivially: [fun _ _ => False] violates [hl_inv_used] and
      [fun _ _ => True] violates [hl_fresh] as soon as [VE] has an
      invocation step.  [ViewLHL.VT] is handle-linear with [used] = "the
      key is invoked in the view trace"
      ([RelaxedHoareSpec.vt_handle_linear]).

      See the file header for where this property enters: not in the
      triple, not in [method_sound], not in [RLHL2Hyps]; it is what makes
      [RLHL2Hyps] satisfiable for the B-5 counter class
      ([RelaxedHoareChecks.CounterHL]). *)

  Section HandleLinear.
    Context {E : RelaxedSig.t}.

    Record HandleLinear (VE : LTS E) (used : State VE -> CallKey E -> Prop) : Prop := {
      hl_inv_used : forall t h op σ σ',
        Step VE (Build_ThreadEvent t (InvEv h op)) σ σ' -> used σ' (t, h);
      hl_mono : forall ev σ σ' k, Step VE ev σ σ' -> used σ k -> used σ' k;
      hl_fresh : forall t h op σ σ',
        Step VE (Build_ThreadEvent t (InvEv h op)) σ σ' -> ~ used σ (t, h)
    }.

    (** The emission of an invocation whose key is used has no underlay
        step, so the [ct_emit] obligation for it is vacuous. *)
    Lemma hl_emit_vacuous VE used t h op σ σ' :
      HandleLinear VE used -> used σ (t, h) ->
      ~ Step VE (Build_ThreadEvent t (InvEv h op)) σ σ'.
    Proof. intros Hhl Hu Hs. exact (hl_fresh _ _ Hhl t h op σ σ' Hs Hu). Qed.
  End HandleLinear.

End RelaxedHoareBase.
