# Task WHWQ: the weak Herlihy–Wing queue over RCMem, by RLHL with a partial-order overlay presentation

Prepared 2026-10-21 (session plan; author decisions recorded below).
Updated 2026-10-21 after review gate 1 (`.rocq-review/latest-review.md`).
Background analysis: project doc `claude/fdlp-whwqueue-rlhl-2026-10-21.md`
(routes, why a single possibility suffices once the future-dependent choice
is moved into the overlay presentation, bounded checks).

Review text is cited by line of `.rocq-review/popl2027-reviews.md` and not
quoted (this repository is public; `.rocq-review/.gitignore`).

## Status (2026-10-21)

- P0–P3 done, plus the examples file of gate 1. Review gate 1: no BLOCKER;
  two research-level MAJOR findings (WHWQ-M-1, WHWQ-M-2) and one
  research-level MINOR (WHWQ-m-4) need author decisions; the actionable
  minors are addressed (see "Gate 1" below).
- **WHWQ-M-1 decided (author, 2026-10-21): option (b)** — decisions D2′
  and D3′ below. `WHWQSpec` is updated accordingly (P2–P3 unchanged, as
  predicted). P5 can start.
- **P5 done (2026-10-21); review gate 3 passed** (no BLOCKER; one
  research-level MAJOR, WHWQ-g3-1, on the scope of T7(c); the actionable
  minors are fixed; see "Gate 3" below). T7(a)–(c) are kernel-checked
  (`WHWQExec`). P6 can start.
- **C7 decided (author, 2026-10-21): option 1, `POQueueRD`** (C7 below).
  The atomic dequeue of `POQueueR` cannot handle a dequeue that can never
  respond. P5b (`examples/Relaxed/WHWQ/POQueueRD.v`, `poqrd_sound`, closed
  under the global context) builds and is reviewed with gate 4. The Rocq
  theorem that no `GSimRel` over `POQueueR` exists for `Mwhw` is deferred
  (author: decide at P8; still open after P8, see "Gate 5"). P6 starts
  over `POQueueRD`.
- **P6–P8 done (2026-10-21); review gates 4 and 5 passed** (no BLOCKER,
  no redesign; actionable findings fixed; see "Gate 4" and "Gate 5").
  - P6 `WHWQInv.v`: invariant, rely, guarantee, footprints,
    postcondition, and every field of `RLHL2Hyps` except `h_sem`.
  - P7 `WHWQProof.v` (enqueue) and `WHWQDeq.v` (dequeue, T4): both
    methods are `MethodProvable` derivations through
    `run_method_provable`. T4 `WHWQDeq.whw_rlhl2` is closed under the
    global context.
  - P8 `WHWQTop.v`: T5, T6, the sharpness of T6, the B6 corollary, and
    the consistency checks against P5. T5 uses `classic` and T6
    `eq_rect_eq`, both inherited from the framework.
  - Not done: T0 unproducible (WHWQ-g3-7, needs code-level facts), and
    the impossibility of a `GSimRel` over the atomic `POQueueR` (C7).
- **Scope decided (author, 2026-10-21, after gate 5):** the task needs
  only the WHW specification and its proof by the mechanized VLHL route
  (T4 with HVF, giving T6). Both are done. No further Coq work: the C7
  impossibility theorem and T0 are not pursued (they stay argued, in C7
  and in WHWQ-g3-7). The other optional items of gates 3–5 are dropped
  as well.

## Concerns and claims in scope

- **R / B6** (Review B, popl2027-reviews.md:261–276): a general concern
  that a relation fixed in advance may permit behaviours the
  implementation never exhibits, at a cost to clients; illustrated by a
  single thread's dequeue being ordered ahead of its own earlier enqueue on
  an empty queue, so that a one-thread `enq(1); deq()` could be explained by
  a failing dequeue although the code returns 1. The B6 lemmas of
  `POQueueRExample` answer the illustration at the specification level,
  not the general concern (see WHWQ-M-1).
  Author response B6 (:541–545): the queue is specified with a dequeue
  that blocks, so any completed dequeue needs a witness with the enqueue
  first; the paper is to state this API and its sequential traces.
- **R / B (mechanization)** (Review B, :248–254): the queue is missing from
  the mechanization. Author response, proposed change 2 (:387): say exactly
  what is mechanized, case study by case study.
- **R / C2** (Review C question and response C2, :577): the choice of the
  relations for the data structures; the response treats the relation as a
  contract to be validated against code and clients.
- **R / minor** (Review B, :301): the exchange of the queue code, rel in the
  appendix, is asked to be acq.
- **P** (current draft):
  - The main text has no queue: `spec.tex` is not input (main.tex:229,
    main-tr.tex:229), its weak-queue example is commented out
    (spec.tex:84–112), and the contributions list (intro.tex:106) names no
    queue. Only the TR appendix remains (main-tr.tex:261 inputs
    Appendix/WHWQueue.tex; main.tex:260 has it commented out). It uses
    ν_queue and I_WkQueue, which are no longer defined anywhere.
  - Appendix/WHWQueue.tex: code (:14–17), invariant (:55–61), proof outline;
    the single-possibility proof at :65 and :150 does not go through
    (background doc §2; review WHWQ-M-2), and the claims at :93 and :148
    are contradicted by 2Counter.tex:13 (review WHWQ-M-1). Under D2′/D3′
    they become consistent with the Coq RCMem, but only together with the
    acq exchange: with the printed `rel` exchange the younger operation has
    a release part and the pair (store, xchg) is still ordered. So the paper
    must change both 2Counter.tex:13 and WHWQueue.tex:17.
  - Appendix/2Counter.tex:6–13 (RCMem); trace.tex:274–301 (Ex. rc-cell,
    `po \ I_RC = po_loc ∪ [acq];po ∪ po;[rel]`).
- research-intent Q5 (keep the weak HW queue in the paper?).
  Concern-matrix rows B6/C2.

## Author decisions (2026-10-21)

- **D1 route.** "VLHL as mechanized": `ViewLHL`/`RelaxedGSim` with a free
  choice of overlay presentation (P1). The overlay presentation is
  `POQueueR`, a relaxed port of master's `examples/HWQ/POQueueSpec.v`. The
  final theorem does not mention the presentation.
- **D2 underlay.** RCMem, the paper's register/RMW specification
  (Appendix/2Counter.tex:6–13), presented as `EIhl δRC` (the decided
  layering interface, research-intent §8, M-20). Its internal relation is
  modified by D2′.
- **D3 xchg mode.** `(rlx, rel)`, as printed in the paper. (Review B asks for
  acq; with RCMem's internal I containing no RMW pair, the choice does not
  change I; it changes the label and the exported mode, LFence.) Gate 1:
  under D2 the mode is invisible to every statement (WHWQ-m-4).
  **Superseded by D3′.**
- **D2′ RCMem semi-independence (2026-10-21, M-1 option (b)).** RCMem is read
  as the tensor of per-location cells with empty internal I, so RMWs enter I
  by the cross-component rule of Def. tensor-sig with their join modes:
  `rc_si o1 o2 := loc o1 ≠ loc o2 ∧ mode o1 ≤ LFence ∧ mode o2 ≤ RFence`
  (equivalently: different locations, no acquire part in the older
  operation, no release part in the younger one). On plain operations this
  is unchanged (Ex. rc-cell). It departs from 2Counter.tex:13 ("no RMW
  pairs"); the paper's RCMem and the Counter_xy appendix must follow. The
  new pairs are C11-style; x86-TSO does not exhibit them (a locked
  exchange is a full barrier), and ARMv8 (RCsc release/acquire) may not
  exhibit the WHW pair (store rel, xchg acq); checking the targets against
  primary sources (Arm ARM, Pulte et al. POPL 2018; RC11, Lahav et al.
  PLDI 2017) is open and decides whether the weak behaviour is presented as
  hardware-level or C11-level.
- **D3′ xchg mode (2026-10-21).** `(acq, rlx)` (Review B, :301), mode
  RFence. With D2′, a dequeue's successful `xchg` may overtake older stores
  of its thread to other slots, so a dequeue may linearize before its
  thread's older pending enqueue. (The pair (faa, xchg) is also
  semi-independent, but in an execution the dequeue's leading `ld`, at the
  counter's location, keeps every older `faa` first.)
- **D4 values.** Overlay values are `positive`; RCMem values are `nat`; null
  is `0`. `enq v` stores `Pos.to_nat v`; a successful `deq` returns
  `Pos.of_nat x` for the non-zero `x` it swapped out. No distinctness of
  values is assumed.
- **D5 theorem form.** Copy-cat route: `RCompLin` for every execution
  (complete or not), then relaxed linearizability of complete traces.
  Gate 1: both are obtained from existing lemmas; P4 is not needed (see T3,
  T5, T6).
- **D6 delivery.** Uncommitted files in the author's working tree on branch
  `rlhl`. The author commits.

## Implementation choices (orchestrator; open to review)

- **C1 overlay signature `FQ`.** Operations `enq (v : positive) : unit` and
  `deq : positive`; handles `nat`; `semi_independent FQ o1 o2 :=
  (o1 = enq _ ∧ o2 = deq)` (a younger deq may be linearized before an older
  pending enq of its thread); modes `enq ↦ LFence`, `deq ↦ RFence` (the
  largest modes that `RelaxedSig.well_formed` allows with this relation).
  `ν_Q := RelaxedHoareSpec.seq_legal δQ []`, where `δQ` is the FIFO queue
  with a blocking dequeue (no transition on the empty queue): the blocking
  API of response B6 (:545).
- **C2 RCMem signature `ERC`.** Locations `nat` (location 0 is the counter
  `q[0]`, slot `s` is location `s + 1`; the paper's dequeue index `i ∈ 1..t`
  is slot `i - 1`); operations `rd l mR`, `wrt l v mW`, `faa l n mR mW`,
  `xchg l v mR mW`, `cas l e n mR mW` with `mR ∈ {rlx, acq}`,
  `mW ∈ {rlx, rel}`. Modes: rd rlx/acq ↦ Local/RFence, wrt rlx/rel ↦
  Local/LFence, RMW ↦ join of its read and write modes (2Counter.tex:13).
  Semi-independence (D2′): at different locations, `mode o1 ≤ LFence` and
  `mode o2 ≤ RFence`, for all operations (the tensor rule over per-location
  cells with empty internal I; on plain operations equal to Ex. rc-cell's
  `po \ I_RC`). WHW pairs (`whw_rc_si`), pairwise: a younger `xchg` may
  overtake an older `faa`; a younger `ld` or `xchg` may overtake an older
  `store` to another slot; nothing overtakes an older `ld`/`xchg`; a
  `faa`/`store` overtakes nothing. In an execution the dequeue's leading
  `ld` keeps older `faa`s first. `δRC`: the sequential register file.
- **C3 `POQueueR`.** master's `POQueueSpec` with relaxed events: the pending
  map stays keyed by thread (master's `Hidle`), the deq control state
  `POQAtomic` is keyed by thread, and handles are ignored. Same-thread pairs
  in a `POQueueR` trace are either real-time ordered or (older pending enq,
  younger deq), which `FQ` declares semi-independent. Kernel-checked in
  `POQueueRExample`: `POQueueR` is unsound under ∅ (`T0_needs_qsi`); the
  trace `Tk` is not rel_lin under `I(enq, deq)` and `POQueueR` rejects it
  (`Tk_not_rel_lin`, `Tk_no_path`); `POQueueR` is not a complete
  presentation (`POQueueR_incomplete`; WHWQ-m-1). Only by inspection: a
  call-keyed variant without the per-thread condition would accept `Tk`
  (the variant is not defined in Rocq).
- **C4 HVF proof.** Direct witness construction (`POQueueRWitness`), not the
  speculation presentation of the background doc.
- **C5 copy-cat over a handle-oblivious presentation.** Superseded by gate 1
  (WHWQ-m-1): not needed for T6. Kept only as an option.
- **C6 dependency tags (P5, gate 3).** Hand-written, following the paper's
  policy for memory cells (Appendix/programlogic.tex:106–112, invocation
  rule :163–172): the FAA and every `ld` untagged; the store tagged with
  the FAA (address); each `xchg` tagged with every earlier call of its
  dequeue (κ). Within a call (F2) already orders all invocations, so over
  `EI δRC` the tags are expected not to change the overlay traces (argued
  at gate 3, not proved).
- **C7 doomed dequeues (found 2026-10-21 while preparing P6; author
  chose option 1 the same day).**
  - The case. `tagged_invoke` commits the whole method trace, underlay
    responses included, at the overlay invocation, and `EI δRC` fixes an
    underlay response at its invocation. A dequeue whose last `xchg` was
    committed with a non-null result but reads null can never respond.
    It has no pending invocation left, so (F1)–(F3) do not order the later
    calls of its thread after it (no cross-call tags), and they can
    complete. Their `AInv` needs the dequeue out of `ls_inv`
    (`invocation_ready`; `(deq, enq)` and `(deq, deq)` are not in
    `I(enq, deq)`). In `POQueueR` the dequeue cannot take `AInv`:
    `POQAtomic` enables only its response, which removes a complete
    minimal vertex, and removing a vertex whose value is still in memory
    breaks the later dequeue that reads it.
  - Hand counterexample (not in Rocq): t2 enq(a) does its `faa` (slot 0);
    t1 deq reads the counter (1) and its `xchg` at slot 0 reads null
    (committed: a); t1 enq(b) completes (slot 1); t3 deq returns b; t2
    stores a; t4 deq returns a. Any `GSimRel` over `POQueueR` must put t1's
    deq through `POQAtomic` before t1.enq(b)'s `AInv`; then only vertex a
    can be removed, and t4's response a has no live vertex.
  - The other mismatches are harmless. A mismatch at an earlier response
    leaves a later `xchg` (tagged with it, and an acquire) pending, which
    (F2) puts before every invocation of a later call of the thread. An
    enq whose `faa` mismatches keeps its release `store` pending, which
    blocks a later enq of the thread; a later deq is semi-independent of
    it. An `xchg` that reads a non-null value linearizes the dequeue as a
    normal removal, whatever its committed result.
  - The paper's sketch has the same gap: Appendix/WHWQueue.tex:65 (the
    enq's TInvoke claim) and :146–150 (the deq at the successful
    exchange). The paper's only readiness argument
    (Appendix/programlogic.tex:712, through pending ghost entries) does
    not cover a call without pending invocations, such as this dequeue
    (wording corrected at gate 4, WHWQ-g4-4).
  - Options. (1) `POQueueRD` (recommended): `POQueueR` plus a dead
    dequeue invocation (`poqrd_dead`: in `POQReady s` a deq invocation
    leaves the state unchanged). Sound by counting: a complete
    well-formed trace has as many dequeue invocations as responses, each
    response consumes one `POQAtomic`, and a dead step enters none, so a
    complete path has no dead step and is a `POQueueR` path
    (`poqrd_complete_path`, `poqrd_sound` from `poqr_sound`). P2–P5
    unchanged. (2) A non-atomic dequeue killed by a later invocation of
    its thread: needs a new HVF proof. (3) A drop rule for `ls_inv` entries
    in `RelaxedPossibility`: generic, but changes the framework and its
    soundness proof.

## Target statements

- T1 `WHWQSpec.FQ_wf : RelaxedSig.well_formed (FQ A)`, `WHWQSpec.ERC_wf`. Done.
- T2 `POQueueRSound.poqr_sound : forall A, ViewLHL.sound_pres (νQ A) (POQueueR A) poqr_init`.
  Done (closed).
- T2D (C7) `POQueueRD.poqrd_sound : forall A, ViewLHL.sound_pres (νQ A)
  (POQueueRD A) poqr_init`, via `poqrd_complete_path`. Done (closed); review
  with gate 4.
- T2′ (gate 1, m-5/m-6/m-8) `POQueueRExample.{future_dependent, T0_needs_qsi,
  Tk_not_rel_lin, Tk_no_path, b6_enq_deq, b6_returns, Tb6_b6, Tb6ov_b6,
  Tb6ov_no_rhb, POQueueR_incomplete}`. Done (closed). The B6 results are
  about the specification. The implementation-level corollary (T6 composed
  with `b6_returns`) is `WHWQTop.whw_b6`. Its hypotheses hold for the
  overlapping trace `Tb6ov`, which the module produces
  (`WHWQExec.Tb6ov_atomic`, `WHWQTop.whw_b6_Tb6ov`). Done at P8.
- T3 (dropped; optional) `RelaxedHoareCompLinObl.cc_rel_lin_obl`.
- T4 `WHWQDeq.whw_rlhl2 : RLHL2Hyps Iq Rq Gq Mwhw ((mem0, []), []) poqr_init`
  over `VE := EIhl δRC`, `VF := POQueueRD positive` (C7), every method a
  `MethodProvable` derivation (no `ren_rlhl2` shortcut): the enqueue in
  `WHWQProof.enq_provable`, the dequeue in `WHWQDeq.deq_provable`, the
  side fields in `WHWQInv` (`whw_rlhl2_of_provable`). **Done (closed).**
- T5 `WHWQTop.whw_complin : RCompLin Mwhw (EI δRC) (mem0, []) (POQueueRD positive) poqr_init`
  (`rlhl_complin` + `complin_hlift_under`). It mentions the presentation and,
  `POQueueRD` being incomplete, cannot be the interface of a layer above the
  queue; cite it only as trace inclusion into the copy-cat of `POQueueRD`
  (WHWQ-m-1; `WHWQTop.POQueueRD_incomplete`). **Done** (`classic`, from
  `gsim_complin`). Its prefixes include abandoned dequeues (C7), an
  artifact of the module semantics, so no prefix-level claim about the
  queue follows; the presentation-free prefix form (`RCompLin` into
  `EI δQ`, M-20) is expected to fail for `Mwhw` (argued, not in Rocq;
  WHWQ-g5-3).
- T6 `WHWQTop.whw_rel_lin : forall s, MTraces (EI δRC) Mwhw (mem0, []) s ->
  PrefixView.complete s -> rel_lin sel s (semi_independent FQ) (seq_legal δQ [])`,
  by `gsim_rel_lin_traces` with `S := RSim` from `rlhl_rsim`,
  HVF := `poqrd_sound`, then `hlift_ei`. Scope: over `EI δRC` only; `EI δRC` is
  not a complete presentation of RCMem (store buffering), so "every
  underlay refining ν_RCMem" needs absorption (M-22). **Done**
  (`eq_rect_eq`, from `gsim_rel_lin`). With it:
  - `whw_rel_lin_sharp`: T6 holds with `I(enq, deq)` and fails with ∅
    (`whw_not_rel_lin_empty_all`);
  - `whw_b6`: B6 at the implementation level (a complete trace whose only
    calls are one thread's `enq v` and `deq`: the dequeue returns `v`).
    It holds for any relation (WHWQ-g5-2). In the order dequeue first
    there is no complete trace (`whw_b6_enq_first`), so the guarantee is
    only that the execution does not complete (WHWQ-g3-6, WHWQ-g5-1).
    `whw_b6_Tb6ov`: its hypotheses hold for the module trace `Tb6ov`
    (the enqueue is invoked first, the dequeue returns first);
  - `whw_consistency`, `whw_future_dependent_lin`: T6 re-derives the
    rel_lin facts of `Tw`, `Tb6ov`, `Tf 1`, `Tf 2`.
- T7 non-vacuity, done at P5 (`examples/Relaxed/WHWQ/WHWQExec.v`, all
  closed). Every execution is over `EI δRC` from `mem0`, built event by
  event, with an atomic underlay word (`ul_atomic`, `MTracesAtomic`).
  - (a) `whw_future_dependent` (`Tf 1`, `Tf 2`; the FAA order decides the
    slots; `Tf1` also refutes a linearization of an enqueue at its store)
    and `whw_future_dependent_module` (two executions from one module
    configuration whose witnesses order two enqueues oppositely; both
    complete executions are atomic, `Sr1_atomic`, `Sr2_atomic`). This is
    kernel evidence for the first part of WHWQ-M-2: a proof that must fix
    the order of the two enqueues by the return of `enq(2)`, such as a
    forward simulation against the sequential queue or the TR's single
    possibility, fails on one of the continuations (argued from the
    theorem). It says nothing against `POQueueR`, where the two vertices
    stay unordered.
  - (b) `Tb6ov_atomic`: a dequeue inside its own pending enqueue returns
    first.
  - (c) **Proved:** `whw_needs_qsi` (the 4-thread example of
    spec.tex:89–110 is a complete, well-formed execution; rel_lin under
    `I(enq, deq)`, not under ∅) and `whw_not_rel_lin_empty_all` (the
    statement of T6 with ∅ is false). Scope (gate 3, WHWQ-g3-1): over
    `EI δRC`; this execution needs D2′ and D3′
    (`WHWQProg.store_xchg_D2_ordered`, `store_xchg_rel_ordered`), and that
    every separation does is argued (gate 1); observable only by clients
    that overlap
    their own calls (`rel_lin_no_self_overlap`, `Tw_self_overlaps`); the
    reordering is C11-style (argued by the reviewer, not checked:
    forbidden on x86-TSO and ARMv8, allowed by RC11).
  - With T6 (P8): apply `whw_rel_lin` to these traces as a consistency
    check. **Done** (`WHWQTop.whw_consistency`).
  - **Deferred to P8 (WHWQ-g3-7):** `T0` is unproducible by the code. It
    needs a code-level argument (the slot-order scan: t1's second dequeue
    reaches slot 1 only after both stores), as extra facts of the P6
    invariant or as a separate execution invariant; T5/T6 cannot exclude
    `T0`, which is a `POQueueR` path.

## Phases and review gates

| Phase | Files (all new unless noted) | Gate | Status |
|---|---|---|---|
| P0 | toolchain (Rocq 9.2.0 + Stdlib 9.2.0 from source), baseline build of `rlhl` | baseline recorded | done |
| P1 | `examples/Relaxed/WHWQ/WHWQSpec.v` (FQ, δQ, ν_Q, RCMem ERC, δRC) | | done |
| P2 | `examples/Relaxed/WHWQ/POQueueR.v` (presentation, wf (W1)–(W8)) | | done |
| P3 | `examples/Relaxed/WHWQ/POQueueRWitness.v`, `POQueueRSound.v` (T2) | review 1 | done; reviewed |
| P3′ | `examples/Relaxed/WHWQ/POQueueRExample.v` (T2′, gate-1 fixes) | review 1 follow-up | done |
| P4 | dropped (WHWQ-m-1) | | — |
| P5 | `examples/Relaxed/WHWQ/WHWQProg.v` (module via `RelaxedHoareRun.run`, production lemmas), `examples/Relaxed/WHWQ/WHWQExec.v` (T7 executions) | review 3 | done; reviewed |
| P5b | `examples/Relaxed/WHWQ/POQueueRD.v` (C7: dead dequeue, `poqrd_sound`) | with review 4 | done; reviewed |
| P6 | `examples/Relaxed/WHWQ/WHWQInv.v` (invariant, rely/guarantee, stability) | with review 4 | done; reviewed |
| P7 | `examples/Relaxed/WHWQ/WHWQProof.v` (enq derivation), `examples/Relaxed/WHWQ/WHWQDeq.v` (deq derivation, T4) | review 4 | done; reviewed |
| P8 | `examples/Relaxed/WHWQ/WHWQTop.v` (T5, T6, T7 checks, B6, incompleteness of `POQueueRD`); concern matrix B6/C2 | review 5 | done; reviewed; T0 and the C7 impossibility open |

Each gate: build of every changed target, admit/axiom grep,
`Print Assumptions` ⊆ {`eq_rect_eq`, `classic`}, then an independent
review by a read-only reviewer following
`.rocq-review/claude-config/agents/rocq-research-reviewer.md`.

## Gate 1 (2026-10-21)

Review: `.rocq-review/latest-review.md` (iteration 1). Verdict: P1–P3
correct and closed; `poqr_sound` is exactly HVF; continue after the M-1
decision; drop P4.

- **Open author decisions.**
  - **WHWQ-M-1 — DECIDED 2026-10-21: option (b)** (D2′, D3′ above). The
    analysis that motivated it, as recorded at gate 1, follows. Argued, not kernel-checked (the module
    semantics' frontier rule, `whw_rc_si`, and the background bounded
    check): under D2/D3 no RMW of the code can overtake an older operation
    of its thread, so the code is not expected to use `I(enq, deq)`; T6
    would then be weaker than what the code satisfies, which bears out the
    general B6 concern for this code, and the case study cannot carry the
    C2 answer. Options:
    (a) keep D2/D3, additionally prove the ∅ result (reviewer's route: an
    overlay `FQ0` with ∅ and a presentation `POQueueRstrict` in which a
    dequeue cannot start while its thread has a pending enqueue; HVF under
    ∅ is a small variant of `poqr_sound`; Layer 1 gains one obligation,
    discharged like `Hidle`; then `rel_lin_mono`), and rewrite
    WHWQueue.tex:63, :93, :148 and the C2 answer;
    (b) let RMWs enter I by the tensor rule with the join modes, and set the
    exchange to (acq, rlx) (Review B, :301): a deq may then linearize before
    its thread's older pending enqueue; `Hidle` still holds (faa stays
    ordered after older operations) and P2–P3 are unchanged; the 4-thread
    example of spec.tex:89–110 becomes producible (argued) and is not
    rel_lin under ∅, so a module-level separation of `I(enq, deq)` from ∅
    becomes possible; the 10-event trace `T0` stays unproducible by the
    code; a paper-wide change of RCMem (Counter_xy uses it too), to be
    checked against primary sources for the intended targets;
    (c) drop "weak".
  - **WHWQ-M-2** (paper). The TR's single-possibility proof fails (checked
    by hand: overlapping enqueues A, B, B stores first, a dequeue takes A's
    value); the "VLHL" of App. J (view-based compatible objects) does not
    match: (νQ, I_WkQueue) is not `compat_fixed` (counterexample checked by
    hand, review H5). Required wording: do not write "verified in VLHL" in
    the App. J sense; either drop compatibility from App. J (`vlhl_sound`
    and `presentation_choice` need none) or write "RLHL over a partial-order
    overlay presentation". Rewrite the TR section around `POQueueR`, HVF
    and the RLHL proof; restore the definitions of a blocking ν_queue and
    I_WkQueue.
  - **WHWQ-m-4** (D3 and the queue modes). The exchange mode is now decided
    (D3′, acq) and matters under D2′. Still open: the modes enq ↦ LFence,
    deq ↦ RFence promise message passing to clients under the tensor rule
    and are not validated.
- **Addressed (actionable).**
  - m-1: P4 dropped; T5/T6 rewritten above.
  - m-2: citations above corrected; concern matrix and research-intent
    updated.
  - m-3: `WHWQSpec` header: slot convention, tensor rule on plain
    operations only, RMW modes never consulted.
  - m-5: `POQueueRExample` (future-dependent order, necessity of
    `I(enq, deq)`, the B6 lemma and an instance).
  - m-6: `POQueueR` header now cites the kernel-checked counterexample and
    states what is only by inspection (the call-keyed variant is not
    defined in Rocq).
- **Iteration 2 (follow-up review, 2026-10-21).** m-1 … m-6 resolved; M-1,
  M-2, m-4 open (author). New, addressed: m-7 (remaining near-verbatim
  review wording in this file and `latest-review.md` reworded), m-8 (the
  overlapping B6 instance `Tb6ov`, with `Tb6ov_no_rhb`; plus
  `POQueueR_incomplete`), m-9 (this section: hedges and the omitted
  requirements restored), m-10 (`WHWQSpec` header: provenance of the
  Example 3.11 remark; the change from the submitted non-blocking
  `deq : N + {⊥}` to the blocking `δQ` stated explicitly). Aside from the
  reviewer: the Rocq headers cite the review file by line and name the
  anonymized submission, as elsewhere in this repository; scrub them before
  any anonymous artifact submission.

## Gate 3 (2026-10-21)

Review: `.rocq-review/latest-review.md` (iteration 4, with the
orchestrator's note; follow-up iteration 5 in `iteration-log.md`).
Verdict: P5 establishes what it is cited for, at the kernel level and over
`EI δRC`; continue to P6.

- **WHWQ-g3-1 (MAJOR, research-level, open: authors).** T7(c) comes from
  the RCpc-style reorderings that D2′/D3′ add (a younger acquire
  overtaking an older release store to another location), not from `EI`:
  the underlay word is atomic. It supports "the code needs I(enq, deq)"
  only for C11-style targets and only for clients that overlap their own
  calls. The reviewer argues, without a machine check, that x86-TSO and
  ARMv8 forbid the outcome of `Tw` and RC11 allows it; to be checked
  against the primary sources. The authors decide whether D2′ is the RCMem
  the paper means (gate-1b b-1, now concrete) and state the scope in the
  paper and in the C2 answer.
- **WHWQ-g3-6 (research-level, open: authors / P8).** Under `I(enq, deq)`
  a client's own frontier may issue a `deq` before its earlier `enq`. Then
  rhb orders the dequeue first under both relations, the specification
  blocks the dequeue, and the module (argued) blocks the enqueue as well.
  The B6 guarantee is partial in this case; P8 states the B6 corollary for
  both invocation orders. **Resolved at P8 (gate 5, WHWQ-g5-1):** in the
  dequeue-first order no complete trace exists
  (`WHWQTop.whw_b6_enq_first`; rhb orders the dequeue first already
  under `I(enq, deq)`).
- **Fixed (actionable):** g3-2 ("over `EI δRC`"; `ul_atomic`; `Tb6ov`
  reordered), g3-3 (the re-read `ld` untagged; tag policy in the
  WHWQProg header; C6 above), g3-4 (WHWQProg header on the frontier
  facts), g3-5 (T7(a) retitled; `Tf1` under M-2; the scan-race pair
  `whw_future_dependent_module`), g3-7 (T0 deferral recorded under T7).
  Stronger approach 1: `rel_lin_no_self_overlap`.
- **Optional, not done:** tag irrelevance over `EI` as a lemma; herd7
  runs, or RMWs in `memory/RC11.v` and `memory/ARM.v`, for the target
  question; a kernel proof of the first part of M-2 from the scan race
  (no `GSimRel` from `Mwhw` over `EI δRC` to `EI δQ`, after the pattern of
  `RelaxedHoareChecks.counter_vt_no_rlhl2`).
- **Iteration 5 (follow-up, same reviewer):** g3-2 … g3-5 and g3-7
  resolved; 35/35 checked results closed; tags now exactly the paper's.
  New documentation minors, fixed: g3-8 (the scan-race conclusion holds
  only for proofs that must fix the order by `enq(2)`'s return, e.g. a
  forward simulation against the sequential queue or the TR's single
  possibility, not for `POQueueR`), g3-9 (atomicity of the scan race:
  `whw_scan_race` now states `ul_atomic` for every segment,
  `Sr1_atomic`/`Sr2_atomic`; stale statements after the `Tb6ov` reorder;
  `inv_crosses_store_res`), g3-10 (necessity wording: this execution
  needs D2′/D3′, `store_xchg_D2_ordered`/`store_xchg_rel_ordered`, any
  separation by argument; "(argued) forbidden on x86-TSO and ARMv8"; a
  short quotation of Review B in the records paraphrased; programlogic.tex
  line numbers), g3-11 (watch-list item on the untagged re-read `ld`).
  Gate 3 passes; P6 can start.

## Gate 4 (2026-10-21)

Review: `.rocq-review/latest-review.md` (iteration 6). Verdict: P5b–P7
establish what they are cited for. K: everything closed. S: the targets
above. The derivations check own interference pairwise; nothing in
`RLHL2Hyps` is discharged vacuously; the dead step is sound by the
kernel-checked counting argument and used only in the intended case. No
BLOCKER, no redesign.

- **WHWQ-g4-1 (MAJOR, research-level, open: authors).** The paper's RLHL
  proof of the queue, and its readiness account, do not cover doomed
  dequeues. They follow from the paper's own Inv rule (responses committed
  at invocation, impl.tex:212) over an underlay with effects at
  invocation. The TR proof linearizes a dequeue only at a successful
  exchange, so the TInvoke of a later enqueue of the thread
  (Appendix/WHWQueue.tex:65) is never ready. This is a second failure of
  the TR proof besides WHWQ-M-2; it is independent of D2′/D3′, and it
  also defeats a proof over the atomic `POQueueR`. Required in the paper:
  present the dead dequeue step and the counting argument; explain doomed
  calls; add at programlogic.tex:712 that a call without pending
  invocations, which can never respond, needs an abstract invocation that
  consumes nothing. Recommended in Coq: the impossibility over
  `POQueueR` (C7, deferred by the author).
- **Fixed (actionable):**
  - g4-2: the tag-irrelevance claim (`WHWQProg` header, C6) is restricted
    to complete executions. On incomplete ones the tags keep a doomed
    call's later tagged invocations from being emitted. The headers of
    `WHWQProof` and `WHWQDeq` state that the derivations use the address
    and κ tag edges.
  - g4-3: headers. K lines (`WHWQInv`, `WHWQProof`, `POQueueRD`); the
    scope in `WHWQInv` (over `EIhl δRC`, atomic underlay word, weak
    behaviour from the frontier; `POQueueRD`; where `I(enq, deq)` enters:
    `deq_ready` as a convenience, and HVF); the wording of `POQueueRD` on
    `POQAtomic`.
  - g4-4: this file (readiness at a dequeue's AInv; the programlogic.tex
    sentence under C7).
- **Optional, not done:** executions in `WHWQExec` with a doomed dequeue
  and with a retry (both derivation branches reachable); a generic form
  of `poqrd_count`; tag irrelevance on complete executions as a lemma.

## Gate 5 (2026-10-21)

Review: `.rocq-review/latest-review.md` (iteration 7). Verdict: T6 is
what D1 asks for: universal, presentation-free, over every complete
trace of `Mwhw` over `EI δRC` (under D2′/D3′), sharp against ∅, and
non-vacuous on interesting witnesses. No Coq BLOCKER; no redesign of T6.

- **WHWQ-g5-1 (MAJOR, actionable): fixed.** In the dequeue-first order
  `whw_b6` is vacuous, and the header said otherwise. Added
  `WHWQTop.whw_b6_enq_first` (the reviewer's proof): no complete trace has
  the dequeue invoked first, because `(deq, enq)` is not
  semi-independent, so rhb orders the dequeue first, against the only
  witness. Header and this file corrected.
- **WHWQ-g5-2 (MAJOR, research-level, open: authors).** `whw_b6` does not
  depend on I (`b6_enq_deq` does not use the rhb part of the witness). B6
  is answered by the blocking API and the closed-world hypothesis, for
  any I, not by the choice of I. The general concern of Review B (a fixed
  I admits behaviours the code lacks) stands: `T0` (open, g3-7) and
  clients that reorder their own calls (g5-1). The paper must present B6
  this way. Headers of `WHWQTop` and `POQueueRExample` updated.
- **WHWQ-g5-3 (MAJOR, research-level, open: authors).** T5's prefixes
  absorb abandoned dequeues (C7). A dequeue whose last `xchg` mismatches
  never responds and does not block the later calls of its thread, while
  the code would keep them waiting behind its acquires. Such a prefix is
  argued not to be in `RTraces (EI δQ)` (an emitted dequeue there always
  consumes a value) nor a REW prefix. So the presentation-free prefix
  form (`RCompLin` into `EI δQ`, M-20) is expected to fail for `Mwhw`
  (argued, not in Rocq), and no prefix-level claim about the queue is
  available. Authors: decide whether the module semantics should allow
  abandoned calls. Recorded in the scope of `WHWQTop` and in T5 above.
- **Fixed (actionable):** g5-4 (records: concern-matrix rows A3, B6/C2,
  case studies, baseline list, Q5; research-intent Q5; iteration log),
  g5-5 (scope of the necessity result in the `WHWQTop` header, from g3-1;
  against ∅ only), g5-6 (`POQueueRD_incomplete`,
  `POQueueRD_not_complete_pres`, with the reviewer's `Tinc_no_path_D`),
  g5-7 (`whw_future_dependent_lin` is a trace-level statement; the
  module level is `whw_future_dependent_module`), g5-8 (stale text in
  `WHWQExec`, `POQueueRExample` and this file).
- **What the paper may claim (proposed by the reviewer; for the
  authors).** For the WHW queue with the exchange (acq, rlx), over RCMem
  with the tensor-rule semi-independence (RMWs taking part by their join
  modes), presented by its register file with effects at invocation:
  every complete trace from the empty queue is relaxed-linearizable to
  the FIFO queue with a blocking dequeue under I = {(enq, deq)}, and not
  under ∅. The proof is RLHL with one possibility over a partial-order
  overlay presentation, whose soundness is proved separately. Not to be
  claimed: verification "in VLHL" in the App. J sense; anything for every
  prefix; the result for every implementation of RCMem; weak behaviour at
  the hardware level; that I is minimal or precise; client or termination
  guarantees; the result for the printed variant.
- **Open (carry-overs):** WHWQ-g3-7 (T0), the C7 impossibility (author
  decision deferred to P8, open), WHWQ-g3-1, WHWQ-m-4, and WHWQ-M-1/M-2
  in the paper. The TR still prints the refuted proof (WHWQueue.tex:17,
  :65, :91, :150; 2Counter.tex:13): by the review rubric this is
  BLOCKER-level for the paper until rewritten.
- **Optional, not done:** a prefix-level B6 from T5; a transfer of T6 to
  the printed variant (the module semantics reads only the
  semi-independence, never the modes); a kernel form of C7 (no `GSimRel`
  over `POQueueR`, or the C7 prefix not in `RTraces (EI δQ)`).

## Layer 1 sketch (P5–P7)

- Abstract steps at invocation emissions (where EI applies effects): the
  `faa` invocation of `enq` takes `AInv enq` (vertex = slot); the `wrt`
  **invocation** takes `ARet enq` (at its response, a younger `faa` could be
  emitted in between and `POQueueR` would reject the path); a successful
  `xchg` invocation takes `AInv deq` and `ARet deq` in one `poss_steps`. The
  `POQueueR` state is `POQReady` between steps.
  - Revised for C7 (option 1): "successful" means that the EI
    record of the `xchg` is non-null, whatever its committed result; the
    `xchg` that is last in the committed trace and reads null takes
    `poqrd_dead`. The invariant clause "a deq in `ls_inv` still owns its
    successful-`xchg` entry" becomes "… owns the entry of the last `xchg`
    of its committed trace".
- Invariant: master's (I1)–(I3) (`I_cells`, counter = `poq_next`, ready),
  `pending_tokens`, the RLHL coupling of pool phases with ghost entries
  (cf. `RelaxedHoareSL2Inv.IslC`); `Hidle` support couples "t ↦ n in
  `poq_pending`" with "the owner of vertex n still owns its `wrt` entry",
  and needs `GAge` (not a field of `RLHL2Hyps`); a deq in `ls_inv` still
  owns its successful-`xchg` entry.
- Readiness at `AInv` (D2′/D3′): at an enq's `AInv` (its `faa`) every older
  `ls_inv` call of the thread owns a blocking entry, because a `faa`
  overtakes nothing (`rc_si_not_before_rel`; `emit_ready_block_older`). At a
  deq's `AInv` (its successful `xchg`), every older enqueue of the thread
  has already taken its `AInv` (its `faa` precedes the dequeue's `ld`), so
  it is not in `ls_inv` and `invocation_ready` puts no constraint on it,
  even if its `store` (its `ARet`) is still to come; `qsi`/`emit_ready_mixed`
  is a convenience there, not a necessity. Older dequeues own blocking
  entries (`rc_si_not_after_acq`). `I(enq, deq)` is used in the overlay
  rel_lin (the dropped program-order edge), through `poqr_sound`.
- New Layer-1 cases under D2′: a dequeue's `xchg` may be issued while an
  older enqueue of its thread has done its `faa` but not its `store`; the
  dequeue then linearizes first, and `POQueueR` accepts it (the dequeue's
  invocation needs only `POQReady`; its response needs a minimal complete
  vertex, at a slot below the pending one, and the pending vertex is never
  a predecessor since edges only point to complete vertices; gate 1b,
  b-4). The dequeue's scan now interleaves with its own thread's older
  stores to other slots: keep master's state-based `Scan` (the vertex is
  garbage, or its store did not precede the scan's `ld`), which is stable
  under them; a formulation like "all older same-thread stores done" is
  not.
- `deq`: loop machine (read the counter, scan slots with control
  dependencies), loop invariant master's `Scan` (its program-order uses are
  ld before xchg and each xchg before the next).

- Watch list from gate 3 (P6–P7):
  - ARet at the store's invocation is forced, for two reasons: a younger
    `faa` of the thread may come before the store's response, and the
    thread's own `xchg` at the store's slot may come between the store's
    invocation and its response ((F1)–(F3) allow it,
    `WHWQProg.inv_crosses_store_res`; no execution in `WHWQExec` shows
    it).
  - Same-thread interference across calls runs both ways: in `Tw` a
    younger dequeue's AInv/ARet and return fall between the older
    enqueue's `faa` and `store`; in `Tb6ov` the older store falls between
    the dequeue's `ld` and `xchg`. So the rely must cover the other calls
    of the same thread.
  - `ghost_emit` and `GAge` must work while an older owner's `store` entry
    is still in the ghost.
  - The state-based Scan must stay true when a slot the scan passed empty
    is filled later (`Tw`: t3 passes slot 2).
  - Readiness at a dequeue's AInv: the proof crosses an older enqueue at
    `ls_inv` by `I(enq, deq)` (`WHWQInv.deq_ready`, `emit_ready_mixed`).
    That case cannot occur: the leading `ld`, which (F2) orders after
    older `faa`s at the counter's location, has already put every older
    enqueue past its `AInv` (pairwise, (faa, xchg) is semi-independent).
    (Corrected at gate 4, WHWQ-g4-4.)
  - Retry loops and `t = 0` have no execution in `WHWQExec`; `rp_run` must
    cover them.
  - The re-read `ld` is untagged (C6), so no response edge enters it in
    `dprec_run`: its invocation may be emitted before the response of the
    previous `xchg` (or of the previous `ld` when `t = 0`), though after
    that call's invocation (F2). P7's retry step must not use those
    response slots in the `ld`'s precondition, and its assertions must be
    stable under those later own responses (under `EIhl` a response only
    consumes a record) (gate 3, WHWQ-g3-11).
  - T0's unproducibility (P8) needs code-level facts (see T7).

## Risks

- Layer 1 size (estimate 4–8k lines; SeqLock's RLHL proof is ≈ 8k).
- D2′ departs from the paper's RCMem (2Counter.tex:13): the paper (RCMem, the
  Counter_xy appendix, WHWQueue.tex:17) must be updated, and the intended
  target models checked for the new RMW reorderings.
- `EIhl` keeps no consumed record values (`RelaxedHoareLog`); the queue
  proof is expected not to need them (the scan facts are about current
  cells). If it does, switch to `EIhlv`.
- `POQueueR` ignores handles: correct on well-formed traces only, which is
  all that `sound_pres` and the module produce.
