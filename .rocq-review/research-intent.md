# Research intent: Relaxed Linearizability (rbgs, branch `relaxed-lin`)

Baseline written 2026-10-13 from the sources listed below. Statements marked **[author to confirm]** are inferences, not author statements. Agents must not treat them as settled. Everything else cites a file.

## 1. Sources (do not invent beyond these)

| Source | Location | Notes |
|---|---|---|
| Paper, POPL 2027 submission #180 | `../async-ccal/drafts/relaxed-lin/` (absolute: `/Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin`) | `main.tex` inputs `intro`, `overview`, `trace`, `impl`, `relaxedlin`, `implex`, `relatedwork`. `main-tr.tex` (the TR) also inputs `Appendix/{intro,gamemodel,relaxedlin,programlogic,edag,2Counter,WHWQueue,viewbased,SeqLock,Mem}.tex`. PDFs: `main.pdf` (2026-07-04), `main-tr.pdf` (2026-09-23). `Appendix/Mem.tex` (buffered cell, OMCA, RC11/ARMv8 comparison) is in the TR only. |
| POPL reviews, author response, meta-review | `.rocq-review/popl2027-reviews.md` | Verbatim, as the author pasted them on 2026-10-13. |
| Revision plans | `../async-ccal/drafts/relaxed-lin/{todo.md,todo-oopsla.md,todo-oopsla-v2.md}` | The plans (2026-09-30) target OOPSLA 2027 Round 2, 2027-04-07 **[author to confirm]**. Some ✅ marks in `todo-oopsla-v2.md` overclaim; see `concern-matrix.md`. |
| Notes cited by `todo-oopsla.md` as `claude/…` | **missing**: not in either folder | `popl-reviews-reconstruction`, `novelty-argument-and-handles`, `rmc-locality-related-work`, `ordering-table-generalization`, `latchset-mechanization-plan`, `own-case-study-candidates`, `rbgs-window-composition`, `power-non-mca-scope`, `seqlock-latch-showcase`, `perf-ring-object-design` (all 2026-09-30). |
| Rocq development | this repository | `README.mdwn`; `docs/README.md`; `examples/View/README.md`, which documents the view files and the ViewLift theory. |
| Checkers and experiments | `../async-ccal/drafts/relaxed-lin/Claude outputs/litmus-check/`, `…/experiments/` | Python brute-force checkers and C++ stress tests. Not verified. Not herd7. |

## 2. The research idea, as the paper states it

1. **Relaxed linearizability** (overview.tex `def:relaxed-hb`, trace.tex `def:rlxlin-po`, relaxedlin.tex `def:relaxed-lin-rew`). It is a correctness condition for concurrent objects under relaxed memory consistency.
   - Operations of one thread may overlap (intra-thread concurrency).
   - The relaxed happens-before keeps every response-before-invocation edge. Between overlapping same-thread operations it keeps the edge unless the pair is semi-independent (`I`).
   - The witness is still a sequential trace that is legal for the object's specification.
   - It is a conservative extension: with `I = ∅`, under SC, it coincides with Herlihy–Wing linearizability (relaxedlin.tex `prop:sanity-check`).
2. **Relaxed object interface** (trace.tex `def:relaxed-effect`). An interface is a set of operations, handles, a semi-independence relation `I`, and fence modes Local / LFence (release-like) / RFence (acquire-like) / Fence.
   - The interface is the object's synchronization contract.
   - The client's program order is supplied at link time and is not hard-coded in the spec (response A4, C1).
3. **Memory as objects.** Memory cells are instances: COH, RA, RC, TSO and LRA in trace.tex; the buffered cell with store forwarding in Appendix/Mem.tex.
   - The response restricts the scope to MCA ("we rather restrict our scope to MCA, not oMCA"; response A2).
   - Mem.tex works under OMCA instead. **This is a conflict to resolve [author to confirm].**
4. **Implementations** (impl.tex, Appendix/programlogic.tex).
   - Imp is compiled to a future-based language with a dependency policy (data / address / control).
   - Load buffering is admitted at the object level, and dependency-forced OOTA is rejected (intro.tex:110).
   - A method returns only after all its underlay calls complete (response A21).
5. **Composition** (overview.tex `prop:vertical-composition`, `prop:locality`; relaxedlin.tex observational refinement, Def. Compatibility, Prop. Horizontal Composition).
   - Vertical composition is layering.
   - Horizontal composition is the tensor. It needs a fence-mode compatibility condition.
   - Revision plan: replace Def. 5.8 by window/mode inheritance (todo-oopsla.md C4).
6. **Verification.**
   - RLHL is a possibility-based rely-guarantee Hoare logic over the future language (Appendix/programlogic.tex §"Program Logic", Prop. Logic Soundness; Appendix/relaxedlin.tex §Possibility, §Simulation, Soundness / Completeness / Parallel Composition).
   - VLHL is a view-based restriction that allows SC LHL proofs to be reused (implex.tex, `prop:rlhl-sc`; Appendix/viewbased.tex).
   - Case studies: Counter_xy, SeqLock, the weak Herlihy–Wing queue, the exchanger, the EB stack (intro.tex:113).
   - Planned case studies: Lock(O) ⊗ plain cell, LatchSet on COH, the perf ring buffer (todo-oopsla-v2.md).

## 3. Claims the revision intends to make (from todo-oopsla*.md) [author to confirm]

- **Pillar A, expressiveness.**
  - Standard memory models are instances of the object interface.
  - Object-level load buffering is allowed while OOTA is forbidden.
  - Comparison with RC11 / ARMv8: they are pairwise incomparable, and the differences are localized to Δ1–Δ5.
- **Pillar B, compositionality.**
  - Relaxed linearizability is local relative to the ordering contract each object exports.
  - Locality fails once same-thread operations overlap (`fence_claim_fails`).
  - A per-implementation sufficient condition is mode inheritance at the window endpoints (`window_composition`, `window_link`).
- **Pillar C, verification.**
  - RLHL and VLHL, with precision examples (LatchSet: SC linearizability "proves" wrong readers; RC11-based logics cannot verify the correct one).
  - Proof reuse (exchanger 1,195 → 1,503 lines).
- **Explicit non-claims** (todo-oopsla.md R4): memory-model parameterization, invocation/response events, contextual refinement and spec/po separation are not new. The paper should not say "first".

## 4. What the reviewers require (details and status in `concern-matrix.md`)

- **Meta-review:**
  - the scope of supported memory models (MCA, store forwarding);
  - the correspondence with existing memory models;
  - a demonstration of client verification;
  - an incomplete mechanization with many admits is "insufficient to establish confidence".
- **Reviewer B, post-rebuttal:** "fully formalize the metatheory". The specific question asks for a mechanized chain: "the program logic, its soundness proof against a weak memory model such as RC11, and the verification of a concurrent object alongside the verification of its client program".

## 5. Four levels that must be kept apart

Every claim in `concern-matrix.md` and in every review records these four levels:
- **K (kernel):** what Rocq actually checked, and with which assumptions (`Print Assumptions`, plus trusted `vm_compute`).
- **S (statement):** what the theorem formally expresses: its hypotheses, quantifiers, the fragment it covers, complete vs. incomplete traces, and which scheduler and underlay it uses.
- **P (paper):** what the paper says, with file:line.
- **R (reviewer):** what the reviewer concern requires, quoted.

Any difference between them must be stated explicitly. Compiling establishes K only.

## 6. Safeguards (apply to every agent)

- Compiling is not evidence of conceptual correctness.
- No `Admitted`, `admit`, `Axiom`, new top-level `Parameter`, or disabled checking.
- No silent weakening. A stronger assumption, narrower statement or changed semantics must be named and justified. If it changes what the paper may claim, the author decides.
- Do not optimize for the Reviewer's approval at the expense of the research claim.
- Do not reconstruct paper statements or reviewer comments from memory. Quote the files.
- The Writer does not commit. The author commits.

## 7. Open research decisions: escalate, do not decide silently

From todo-oopsla.md §3, still open as far as the files show:
- **D3:** mode representation. Keep the 4-element lattice, or move to the ordering table of `WindowTable.v`.
- **D5:** Mem.tex Δ2/Δ3.
- **D6:** rename the SeqLock/exchanger "TSO" cells, or redo them over the buffered cell.
- **D7:** which end-to-end links to mechanize and which to state as limitations.

Raised by the 2026-10-13 baseline audit (`latest-review.md`):
- **Q1:** Should the RLHL judgement be redesigned? It is existential today. The question is whether to target `RelaxedGSim.GSimRel`, which is already proved sound for complete traces, as the semantic model of the logic.
- **Q2:** Scope statement. The MCA restriction in the response conflicts with the OMCA buffered cell in Mem.tex. Coq proves equality only for x86-TSO (read/write fragment). For RC11 and ARMv8 it proves only partial one-direction containment, plus incomparability witnesses. What may the paper claim about "soundness against a weak memory model"?
- **Q3:** Is soundness for complete traces only acceptable, or are incomplete traces needed? Vertical composition needs the conclusion `implements ν_F`.
- **Q4:** Which case study is the flagship for the client-verification requirement? Candidates: SeqLock a=b, Lock(O) ⊗ plain cell, LatchSet.
- **Q5:** Is the weak HW queue kept in the paper? Today it is not mechanized and its spec in trace.tex:92 is not blocking.

Raised by the RLHL-3c design panel (2026-10-14; `.rocq-review/tasks/RLHL-3c.md`, section "Research-level decisions"). Not yet put to the author. Work proceeds provisionally with the recommended options, all as additive definitions with no paper claim:
- **D1:** semantic layering. The composite is `ModLTS` ("N over M", an LTS), not a syntactic inlining construct in `RelaxedLang`. Recommended (a). Consequence: relaxedlin.tex:62-70 (inlining, ⟦M;N⟧ = ⟦M⟧;⟦N⟧, associativity) cannot be cited as mechanized.
- **D2:** saturation (App. relaxedlin.tex:53-56) only on the E-side, over `CCClosed` specification presentations. Over handle-sensitive underlays it is false (counterexample planned: `absorb_needs_closure`). The F-side is probably false without SI inheritance (planned: `fside_not_saturated`). Recommended (a): restrict the proposition.
- **D3:** verimpl (relaxedlin.tex:74) in copy-cat form (`VerImpl`/`CCRefines`). The rel_lin form needs the open M-20 converse. Recommended (a), rewording :74 and prop:vertical-composition.
- **D4:** the client. A semantic theorem modular over `CCRefines`, for Counter_xy (SB client with Wait). Recommended now; the SeqLock a=b client promised in the author response B4 (popl2027-reviews.md:531-533) as the paper's flagship later.
- **D5:** the m-8 bundle: (i) accept the implementation-side obligation; (ii) `EIe` with an explicit precondition; (iii) a licensed `cte_noerr`; (iv) `TErr` tagged with (key, op); (v) layering with errors out of scope; (vi) `PossError` absorbs. **Blocks RLHL-3c.8.**
- **D6:** the client for all executions (via absorption); rel_lin corollaries complete-only. Recommended.
- **D7:** claim wording after RLHL-3c. Copy-cat vertical composition over EI interfaces; E-side saturation over spec presentations; a client verified from its spec and transferred. Not: inlining, F-side saturation, rel_lin-quantified verimpl, RC11.
- **D8:** order. M-22 and the client before m-8. Recommended.

Raised by the RLHL-latch design panel (2026-10-15; `.rocq-review/tasks/RLHL-latch.md` §4). Not yet put to the author. Work proceeds provisionally with the recommended options:
- **RD-1:** first deliverable is an error-free RLHL proof of the guarded module `M_Lw`, plus conditional statements for `M_L` and `latch_complin_err` derived via the trace-level error definitions (L.10/L.11). Rationale: `EIhl δcoh` has `Error := False`, so the implementation-side obligation is vacuous for LatchSet. The full `GSimRelErr`/`RLHL2HypsE` comes later.
- **RD-2:** capacity is handled by the saturating spec `δbset`, recovering the unbounded set under P2; it is not an `EIe` error.
- **RD-3:** P1 = "only `tw` inserts". The non-overlap clause is dropped, because the panel found it unnecessary (a weaker precondition, so a stronger result). This differs from the window-route P1 in `../rbgs` latchset-plan.
- **RD-4:** export I_L as in the paper and also state the ∅ corollary. Panel finding: over COH the implementation never uses I_L, so load buffering is admitted by the contract but not exhibited (`lbw`). overview.tex:333 needs rewording.
- **RD-5:** the trailing `mb` is not needed for single-object correctness here. `no_mb` is not mechanized for now.
- **RD-6:** route L (syntactic `RProvable` via a generic `run` interpreter), with the reader proof (L.5) as the go/no-go checkpoint. The fallback is route S (direct `MethodSem`).
- **RD-7:** the LP is identified through the ghost (the committed trace); this relies on run-to-completion (m-33). A past-determined alternative exists.
- **RD-8:** paper scope: a sequential, multi-copy-atomic register file with ordering-only barriers and table SI; ν_E;cc only. Not ARMv8, buffered or oMCA. A COH+barriers definition is needed in trace.tex.
- **RD-9:** D5 (ii) `bad` with thread id, (iv) TErr tagged with key+op, (vi) `PossError` absorbs: adopted. (iii) and (v) deferred.
- **RD-10:** include the negative half of `m8_gap` in the first deliverable, so that the implementation-side clause is exercised.

## 8. Author decisions (log)

- **2026-10-13 — Scope = oMCA.** The paper targets other-multicopy-atomic models (store forwarding included, via the buffered cell of Mem.tex). Non-MCA models (POWER, ARMv7) are out of scope. This resolves the MCA/oMCA part of Q2; what may be claimed about RC11/ARMv8 (incomparability, partial containment) is still open.
- **2026-10-13 — Current priority: two flagship examples.** (1) LatchSet + write snapshot (COH, address dependency); (2) SeqLock on COH (Counter → TicketLock → SeqLock tower, rmb/wmb). `/rocq-loop` tasks should serve these first.
- **2026-10-13 — Clarification of Q1.** The paper's RLHL rules (Appendix/programlogic.tex, EStep: `∀v`, stability under R) are not the problem. The problem is the Coq encoding in `RelaxedLogic.v` / `RelaxedTaggedLogic.v`: the Wait rule fixes one response (`provable_wait_pending … ret …`), so `HTripleProvable` certifies one execution path; `queue_invariant` equates one call's debts with the whole module queue (vacuous under concurrency); rely/stability is not used; and there is no theorem to `GSimRel`/`rel_lin`. Separately, the paper's simulation (Appendix/relaxedlin.tex, OStep) is existential; `RelaxedGSim.GSimRel` is the corrected, universal version. RLHL is **not** on the critical path of the two examples, which use the window route (per-layer witness proof + `WindowLinkTable.window_link_table`). Open: whether the paper claims RLHL as mechanized.
- **2026-10-13 — RLHL-1 design (answers to `/rocq-loop RLHL`).**
  - **Futures semantics: dependency-only waits.** Author's words: "we want to use the future semantics that could make our ARM model equivalent to the declarative one. So the wait should only block the later invocation with actual data dependence." The new judgement must be sound for the tagged module semantics (`module_step_tagged`, (F1)–(F3)), in which a `Wait` orders only later invocations whose tag names the awaited handle. A method's own underlay events may therefore leave program order; RLHL is **not** restricted to blocking calls. This also decides D5/Δ3 in that direction; consequences for Mem.tex (Δ3, :528, (W) `dep;po? ⊆ pre`) and `ARM.v` hypothesis (W) are recorded in `iteration-log.md` and are not part of RLHL-1.
  - **Single possibility** ("lets only focus on single possibility at this moment"). Future-dependent linearization points and the paper's Completeness proposition stay out of scope.
  - **A method's own reordered events are interference** among the call's events (Owicki–Gries on the call's (F1)–(F3) dependency dag), with a program-order proof outline and a ∀-response Wait rule; underneath, a semantic per-call triple covering every frontier order (chosen option "Interference among own events").
  - **Generic underlay LTS `VE`**; `complete_pres νE VE` appears only as a hypothesis of the end-to-end theorem (RLHL-2, via `presentation_choice`).
  - **Toolchain: newest Rocq** ("let's use the newest rocq"): Homebrew Rocq 9.3.0, not the 9.2.0 pinned in `rocq-rbgs.opam`/CLAUDE.md. Baseline under 9.3.0: 170/171 files; `structures/DCPOs.v` fails (record field named `is`), nothing imports it.
- **2026-10-13 — B-5 (latest-review, RLHL-1 iter 1): ghost thread frontier.** The per-call triple `MethodSem` of iteration 1 is unsatisfiable for a correct overlapping same-thread counter: `counter_methodsem_unsat`, reproduced by the orchestrator. The author chose the option "Ghost thread frontier": add a ghost per-thread component (the pending underlay invocations of the thread's active calls, in queue order) to the proof state. A call's emit step may then assume its invocation is on the thread frontier, and assertions may mention other same-thread calls' pending invocations. Responses stay lazily placed, because F2 relates invocations only. Acceptance: the redesigned triple is provable for that counter. The alternatives "full concrete state" and "restrict overlap" were rejected.
- **2026-10-13 — M-16 (RLHL-1 iteration-2 review): handle-linear VE.** The per-call triple lacks underlay-key freshness. The author chose "Handle-linear VE": assume of the underlay presentation that an invocation is disabled for an already-invoked (thread, handle). This is faithful to Appendix/gamemodel.tex:19 ("no two moves with the same polarity and the same future handle"), and `ViewLHL.VT` should satisfy it. The proof state is unchanged. Fallback if the acceptance proof fails: a used-key ghost.
- **2026-10-13 — M-17: effect-at-invocation specifications.** RLHL-2/3 abstract specifications take effect at the abstract invocation, and same-thread order is discharged through the ghost. A generic lemma should show that such a VF, built from a sequential specification, satisfies `gsim_rel_lin`'s HVF; HVF stays an explicit hypothesis of the RLHL-2 theorem. Rejected: per-spec response ordering; commuting pairs only.
- **2026-10-13 — Ghost representation (m-18).** The B-5 "per-thread component" is implemented as one global list of pending underlay invocations. A helper `gthread` exists but is unused; the per-thread view is implicit, because `inv_blocks` requires the same thread. This is equivalent to the per-thread component. (Corrected after review iteration 3, m-18.)
- **2026-10-13 — M-18 (RLHL-1 iteration-3 review): stamp-based VT overlay for RLHL-3.** Effect-at-invocation overlays (EI) admit no `GSimRel` over a complete underlay presentation (`VT`) for ordered same-thread operations (`vt_junk`, reproduced). The author chose "Stamp-based VT overlay": VF := `ViewLHL.VT nuF`, where the abstract invocation commits a stamp and the value is checked at the response; HVF comes from `vt_sound`. Known caveat: positions that depend on the future are not covered. Note (2026-10-13, RLHL-2 iteration-2 review M-1): VE := `VT nuE` conflicts with the Q3 prefix-soundness goal, because VT accepts dead-end prefixes. VT×VT can at most give complete-trace soundness. This supersedes the M-17 choice for the end-to-end route; `ei_hvf`/EI remain valid for invocation-ordered underlays. Rejected: deferred-result EI, prophecy/possibility sets (for now), restricting claims.
- **2026-10-13 — Case studies in intro.tex:115 (working tree): plan an RLHL instance.** The author keeps the sentence that RLHL verifies a latched set and a write snapshot, and adds an RLHL verification of the latched set to the queue (after RLHL-3, on the M-18 route). Until that exists, the claim is unsupported (latest-review M-15) and is tracked as ⚠️ in the concern matrix.
- **2026-10-13 — Q3 / M-1 (RLHL-2 iteration-1 review): prove prefix soundness.** The author chose "Prove prefix soundness". RLHL-3's acceptance includes `gsim_implements`/`rlhl_implements`: from `GSimRel` and "every VF path is an `rl_prefix`" ~~(free for the stamp-based `VT nuF` overlay)~~ (struck 2026-10-13: false. `vt_not_implements` / `vtF_not_implements` show VT has dead-end prefixes, and the review's S1 shows that over VE := `VT nuE` no VF satisfying the premise admits a GSimRel for the correct counter; see latest-review M-1, M-20), conclude `implements nuF` for the module's overlay, including executions with pending calls. It also includes showing that two layers compose through `presentation_choice`. This resolves research-intent §7 Q3 in favour of incomplete traces, as needed for vertical composition. Design step needed: an overlay LTS that hides the module's internal steps.
- **2026-10-13 — M-20 / Q3 (RLHL-2 iteration-2 review): follow the original RG simulation (CompLin), copy-cat over the sequential spec.**
  - The author's words: "follow the work in original RG sim, they also need to deal with the incomplete trace". Then, in answer to the follow-up, "Sequential spec, EI".
  - **Soundness statement.** RLHL soundness is stated like `CompLin.CompLin` (Def 4.1; `CompLinSound.cal_to_CompLin`): every overlay trace of M over the underlay, complete or not, is an overlay trace of the copy-cat identity module run over the overlay's sequential spec LTS (effect at the abstract invocation, `RelaxedHoareSpec.EI δF`). It is proved by reifying the `GSimRel` run into one copy-cat execution, as in `TPSimulation_abs_reaches` / `abs_reaches_reify`.
  - **Induced prefix notion.** This is intended to be the paper's REW notion (relaxedlin.tex:29), in the shape of the paper's Soundness ν_E;cc_E;M ⊆ ν_F;cc_F (relaxedlin.tex:665). The REW agreement is argued, not proved (RLHL-3a review M-20); the mechanized data points are `junkF_not_rtrace` (it rejects `junk`) and T2 `si_overtake_rtrace`. Semi-independent invocations may still overtake one another through the copy-cat's frontier, and that is where relaxation comes from.
  - **Layering.** As in LinCCAL, each layer is verified over the sequential spec LTS of the layer below. Correction (2026-10-13, RLHL-3a review m-20): this must be the handle-linear variant VE := `EIhl δE`, because plain `EI` admits no `RLHL2Hyps` for overlapping same-thread calls (T1 `counter_ei_unsat`, reproduced; script in `.rocq-review/scripts/`). `EIhl` is connected to `EI` by an HLift lemma. Replacing `presentation_choice` is conditional on the absorption, linking and monotonicity lemmas of RLHL-3c (review M-22).
  - **Mechanized so far (RLHL-3a iteration 2).** Complete-trace ν;cc ⊆ rel_lin: `RelaxedHoareCompLinSpec.cc_rel_lin` (`eq_rect_eq`, `classic`). In the orientation of App. relaxedlin.tex:47-50 (`rlx(ν) = ν;seqcopy`) this is the ⊇ half, for concurrent traces in the EI presentation. The converse rel_lin ⊆ ν;cc is open; it is needed only for "every underlay relaxed-linearizable" (M-22).
  - **Effect on earlier decisions.** The stamp-based VT pair (M-18) is kept only for the complete-trace corollary. The Q3 "prove prefix soundness" goal is realized as copy-cat trace inclusion. K/REW/V need not be added as separate prefix predicates.
- **2026-10-13 — Decisions after the RLHL-3a iteration-1 review.**
  - **m-8, error clause:** "Add TErr like CompLin". RLHL-3c adds a CompLin-style undefined-behaviour clause to the relaxed copy-cat comparison: a spec error at some prefix licenses every continuation (`CompLin.v` TErr / `ImplTracesClosed`), so lock-based specs may have preconditions. `gsim_complin` is to be re-proved with it. Amendment needed (RLHL-3a iteration-2 review, m-8 promoted to MAJOR; not yet put to the author): a spec-side license alone is unsound for layering. In CompLin, `TraceStepError` is part of the implementation's own `ImplTraces`, so the implementation must also be obliged to show it never misuses the underlay. Counterexample: M2 = acquire; release; release has RLHL2Hyps over `EIhl δ_lock` because the second release blocks, yet a lower lock that does not block on misuse is licensed after the error prefix. Proposed: new definitions beside the old ones (a tagged error rule, `RCompLinErr`, `GSimRelErr`, a `ct_noerr` clause as in LHL's `Herror`, and `EIe` with `Error` when δ has no successor), plus inclusion lemmas from the old relations.
  - **B-1, memory route:** "Thread-aware buffered spec". The memory spec is a sequential, thread-aware state machine with per-thread buffers and flushes (the buffered cell's own transitions as δ_mem), with semi-independence I_Mem. Objects are verified over `EIhl δ_mem`, and the buffered cell (memory/Cell.v) is shown to produce only copy-cat traces of it. Rejected: the raw cell LTS as VE; deferring the memory layer. Gap (RLHL-3a iteration-2 review, m-37): δ in `ei_step` takes no thread id, so δ_mem as decided is not expressible. Either an `EIt` variant (δ with tid) or tid-carrying operations is needed before RLHL-mem. Narrowed (RLHL-3a iteration-3 review): the paper's COH and RC specs are thread-unaware sequential cells plus SI (trace.tex:190, :205; 2Counter.tex:5), so they are expressible today as `EIhl δ_coh`; the thread id is needed only for the buffered/TSO route (store forwarding).
  - **M-15, write-snapshot:** "Plan interval-spec overlay". Keep the target. After RLHL-3c, add an interval-sequential spec LTS (EI generalised to interval effects) with its own bridge to interval linearizability, as part of the RLHL latched-set/snapshot work. Until then the intro claim stays unsupported.
  - **M-20(c), paper presentation:** "Define via copy-cat". The paper defines incomplete-trace correctness as ν;cc inclusion (as mechanized), presents REW as an argued characterization, and restricts prop:rhb-equiv to complete traces.
- **2026-10-15 — Author decisions on m-8 / D5 (i) and the RLHL LatchSet.**
  - **m-8 / D5 (i): accepted.** The author's words (Chinese, translated): "m-8 adopts the scheme in which the implementation side also bears the error obligation". The CompLin-style TErr clause therefore carries an implementation-side obligation: a module that misuses its underlay produces an error trace that its own specification must license. It is built in as new definitions beside the old ones (`MTracesE`/`RCompLinErr`, `GSimRelErr`, an error-aware `CallTriple`/`RLHL2Hyps`). D5 (ii)-(vi) (`EIe` with an explicit precondition, licensed `cte_noerr`, `TErr` tagged with (key, op), no error-aware layering in RLHL-3c, `PossError` absorbs) remain the panel's recommendations and are not yet decided.
  - **RLHL LatchSet: COH registers plus barriers first.** The author's words: "the RLHL version of LatchSet first does the COH registers plus barrier version". The underlay is a sequential COH register spec with wmb/rmb (and the trailing mb) as operations, and semi-independence from the ordering table, presented as `EIhl δ_coh`. The buffered-cell/ARMv8 LatchSet of the window route (sibling checkout `../rbgs`, branch `relaxed-lin`, `latchset-plan.md` v2.2) stays on that route; its RLHL version waits for a thread-aware EI (m-37).
  - **Priority:** "you do latch set first and see". RLHL-latch now precedes the rest of RLHL-3c. Error infrastructure (3c.8) is needed for LatchSet's client preconditions P1 (single writer, non-overlapping inserts) and P2 (capacity), so it moves forward. Absorption, linking and the client (3c.5-3c.7) are deferred.
- **2026-10-15 — Author: switch the RLHL target to two SeqLocks on COH with LB.** The author's words (Chinese, translated): "or set aside latch set for now, and try two seqlocks on COH with LB?" The RLHL-latch work is paused after wave 1. Wave 1's generic pieces (`RelaxedHoareRun` `run`/`rp_run`/`emit_ready_block`, `RelaxedHoareResig`, `RelaxedHoareErrSpec`) are reused; `RelaxedHoareLatchProg` is kept as LatchSet groundwork. Rationale recorded by the orchestrator:
  - SeqLock is simpler (two data registers, no arrays or capacity);
  - cross-object LB between two SeqLocks over COH is actually exhibited by the implementation, whereas the LatchSet panel found LatchSet's own I_L unused;
  - it answers Reviewer B's "No example verified on the COH model" (popl2027-reviews.md:215) and the paper's LB claims.
  
  Design questions (single writer vs a lock in the underlay spec; reuse of `SeqLockProg.v`'s module) go to a read-only design panel first.
  - **Correction (2026-10-15, RLHL-seqlock design panel, `tasks/RLHL-seqlock.md` §0, §5).** The orchestrator's rationale above, "cross-object LB between two SeqLocks over COH is actually exhibited by the implementation", is **false** for:
    - the TicketLock SeqLock of `SeqLockCOH`/`SeqLockProg` (acquire/release are DRMW);
    - any writer that reads `seq` (Linux seqcount style).
    
    In the dto table `Rmb` orders every later read-kind operation (`dto Rmb DR = dto Rmb DRMW = true`), so the younger write cannot start before the older read's queued `rmb`s. Cross-SeqLock LB is a module trace only when the writer's publication path has no read-kind access, e.g. a single writer with a blind increment `inc seq` of category DW (scratch `lb_reorder_prefix`, closed; re-run by the orchestrator, copy in `.rocq-review/scripts/`). Whether `inc ↦ DW` is faithful depends on LKMM's rmb excluding non-value-returning RMWs (`[R \ Noreturn]`; the panel's recollection, unverified). Under ARMv8 (DMB LD orders R→W) this LB would not be observable for any writer. Decision RS-1 (which writer) goes to the author.
- **2026-10-15 — Author decision RS-1: "只做 WRd" (only WRd).** (Wording corrected 2026-10-15 per review M-23: this writer is *a single-writer seqcount whose closing increment reuses the opening read* (Boehm-style), not the Linux seqcount writer, which reloads `seq`; see the M-23 decision below.) The SeqLock writer is WRd: `v <- rd seq; wr seq (v+1); wmb; wr x; wr y; wmb; wr seq (v+2)`, single writer per instance (P1 guard). It was chosen over WInc (blind inc, LB), TicketLock (SC) and returning to LatchSet. Consequences:
  - the overlay relation is RA-shaped (`slRA`: older write_i, younger read_j, i≠j);
  - the deliverable shows SB (module-derived, accepted) and **no LB** (`lb2_not_trace_rd`);
  - the cross-SeqLock LB datum for implex.tex:3 is therefore not part of this deliverable;
  - RS-2 (LKMM `inc`) is moot.
- **2026-10-15 — Author: "可以暂时不考虑LB 但是要完整使用RLHL"** (LB may be set aside for now, but RLHL must be used in full). Binding for RLHL-seqlock:
  - every method (WRd write, reader with retry) is verified by an RLHL derivation, i.e. a syntactic `MethodProvable` built with the RProvable rules (route L: `run_method_provable`/`rp_run`, which are derived from `RProvable_coind`);
  - soundness goes through `method_sound` → `RLHL2Hyps` → `rlhl_complin_eihl` → `cc_rel_lin`;
  - the route-S fallback (a direct semantic `MethodSem` proof) is **excluded**, and so are generic shortcuts such as `ren_rlhl2` for the main object;
  - if the RLHL derivation stalls (the reader checkpoint .5), escalate to the author instead of switching routes.
- **2026-10-15 — Author decision on M-23: "保留缓存 v" (keep the cached v).** The WRd writer keeps its closing write `wr seq (v+2)` with the cached `v`. It must be described honestly: "a single-writer seqcount whose closing increment reuses the opening read" (Boehm-style), not "the Linux seqcount writer". State also that the Linux-literal writer, which reloads `seq` before the closing increment, has no SB execution on this underlay (no store forwarding; argued, review M-23 — "SC" is not proved), so the SB datum depends on the cached-v encoding.
- **2026-10-15 — Author decision on the SeqLock reader blocker: "B：加历史变量" (option B, history variable).** The underlay presentation becomes `EIhlv := Log (EIhl δS)`, which records the underlay event history and is trace-equivalent to `EIhl` (`loglift`, `rlhl_complin_eihlv`). The program (untagged reader) and the RLHL rules are unchanged. The soundness chain of "use RLHL in full" becomes `method_sound` → `RLHL2Hyps (VE := EIhlv)` → `rlhl_complin_eihlv` → `cc_rel_lin`, giving `RCompLin` for every prefix. This matches the paper's proof state, which carries the underlay trace (programlogic.tex:537). Option A (tagging the barriers) is rejected: it violates the dependency-only principle. Recorded datum: the lossy `EIhl` presentation is incomplete for validate-after-read programs (argued). "RLHL is complete" must not be claimed. The B-6 fix (`Qrd := Qsl ∨ ¬NoOwn`; per-operation postconditions in the assembly lemmas) is needed either way.
