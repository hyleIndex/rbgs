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
