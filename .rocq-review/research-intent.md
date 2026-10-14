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
- **Q7 (raised 2026-10-13, G-3 review M-15; axiomatic part kernel-checked in `memory/ARMBar.v`-based scratch, Hν rejection a derivation):** can the paper claim ARMv8 for the running example? A client that waits on `zr()` and then calls `read()` forces an underlay real-time edge zr → get_ticket (F3 + rhb real time), and ARMv8 lets `LDR z = 1; LDR s = 0` happen even with the SeqLock's barriers (Δ3 at the object level). Options: **R3** x86 only (reviewer-recommended for F-2 now); **R4** ARMv8 under a stated Wait-compilation scheme (DMB LD / ISB / LDAR after waited loads, DMB after RMWs whose result is waited on) — changes the code mapping; (iii) change real-time treatment in rel_lin — excluded by the author. Also M-16: the writer-side version-word outcome is likely admitted (R1 may be unnecessary). **F-2 waits on this decision.**
- **Q6 — CONFIRMED IN COQ 2026-10-13 (piped toplevel sessions; to be committed as `examples/Relaxed/SeqLockQ6.v`, task Q6-1): `q6_not_rel_lin` (overlay, every rc, closed), `q6_underlay_no_WF` / `q6_underlay_not_rel_lin` (underlay, closed), `sq_V`/`sq_nu`/`q6_cells_TSO_consistent` (the buffered TSO cell of memory/ admits the cell-level history, `classic` only); hardware verdicts (x86-TSO allowed, ARMv8 allowed) are hand derivations, herd7 not installed. Plan: `.rocq-review/buffered-cell-plan.md`. Original text:** (raised 2026-10-13, running-example assessment; derivation, not yet checked in Coq or herd7): Is the SeqLock ⊎ COH[z] interface sound for an oMCA memory with store forwarding? The object-level SB-with-forwarding outcome T1: `zw(1); zr()=1; read()=(0,0)` ‖ T2: `write(1,1); read()=(1,1); zr()=0` is not rel_lin under `findep` (cycle through zw<zr (same object), zr<read (`dto DR Rmb`), write<read, read<zr (`dto Rmb DR`), and the values), and its underlay history is not rel_lin under `sindep` either; but on x86-TSO (rmb a no-op, T1 has no fence between its buffered `z` store and its `x` read) it looks allowed. If confirmed, SL-mem's planned direction ("OMCA-consistent underlay ⇒ the cell part of the module theorem's hypothesis") is false as posed for the buffered cell with forwarding. Options: restrict the example to a forwarding-free fragment (COH registers, i.e. MCA-like cells); make `rmb` (or a read after a same-location write) drain/order the buffer; or switch the example's cells to buffered specs and redo `seqlock_S1` and the categories. This is Reviewer A's transitivity/store-forwarding objection (popl2027-reviews.md:69–81) applied to the running example.

## 8. Author decisions (log)

- **2026-10-13 — Scope = oMCA.** The paper targets other-multicopy-atomic models (store forwarding included, via the buffered cell of Mem.tex). Non-MCA models (POWER, ARMv7) are out of scope. This resolves the MCA/oMCA part of Q2; what may be claimed about RC11/ARMv8 (incomparability, partial containment) is still open.
- **2026-10-13 — Current priority: two flagship examples.** (1) LatchSet + write snapshot (COH, address dependency); (2) SeqLock on COH (Counter → TicketLock → SeqLock tower, rmb/wmb). `/rocq-loop` tasks should serve these first.
- **2026-10-13 — Clarification of Q1.** The paper's RLHL rules (Appendix/programlogic.tex, EStep: `∀v`, stability under R) are not the problem. The problem is the Coq encoding in `RelaxedLogic.v` / `RelaxedTaggedLogic.v`: the Wait rule fixes one response (`provable_wait_pending … ret …`), so `HTripleProvable` certifies one execution path; `queue_invariant` equates one call's debts with the whole module queue (vacuous under concurrency); rely/stability is not used; and there is no theorem to `GSimRel`/`rel_lin`. Separately, the paper's simulation (Appendix/relaxedlin.tex, OStep) is existential; `RelaxedGSim.GSimRel` is the corrected, universal version. RLHL is **not** on the critical path of the two examples, which use the window route (per-layer witness proof + `WindowLinkTable.window_link_table`). Open: whether the paper claims RLHL as mechanized.
- **2026-10-13 — Running example (after the running-example assessment, `.rocq-review/running-example-gap.md`).** Author's answers:
  - **Q4 / D3 / D6:** the paper's running example is the COH SeqLock (SeqLock ⊎ COH[z] with rmb/wmb), with the category table `WindowTable.dto` in the main text and the four fence modes as its rectangular special case. The printed TSO SeqLock is retired or relabelled.
  - **Q6 (store forwarding):** redesign the example with buffered cells, keeping forwarding in scope: switch the example's cells to buffered specifications and redo `seqlock_S1`, the categories and the module proof. (Q6 is still a derivation; confirming it in Coq is the first step of the redesign.)
  - **Code faithfulness (RE-04):** the paper prints the futures program as verified (extra waits, positional tags) and names each deviation; no Coq rework of `SeqLockProg` for this.
  - **Depth:** full Tier B — module-level tower including a Counter layer, plus `memory/` grounding.
- **2026-10-13 — Buffered-cell redesign plan (`.rocq-review/buffered-cell-plan.md`), author's answers:**
  - **Amend the Q6 decision:** only the object specifications change (cells, barriers, overlay spec), `seqlock_S1` is reached by an SC-ification reduction, and the module proof is redone. The categories, the table `WindowTable.dto`, `findep`/`sindep`, the futures program and the windows stay. All work goes in new files.
  - **Exported interface (main text):** the marker spec. The SeqLock is an atomic pair register `nu_sl` with a hidden publication marker per write, placed before its next operation, joint with Buf[z] under a contract read off `findep`. It is a contract tensor, so the product ⊗ is not used for this example. "SeqLock ⊎ z is a two-location buffered memory" (ν_{I_F}[{sl,z}] ∩ Lin_sl) is a proved corollary.
  - **Hardware scope: x86-TSO and ARMv8.** The ARM check (plan task G-3: dmb ld/st and RMW flavours in a copy of `memory/ARM.v`, the Q6 / RSW-through-object / LDADD tests) is required, as are herd7 runs (x86tso.cat, aarch64.cat), which the author runs (herd7 is not installed on this machine).
    - Memory convention: not changed by the author, so it stays memory/'s "plain writes respond at issue". By Q6-2 (`rt_iteration_not_rel_lin`), x and y must be buffered as well as z. A returned z write need not be visible (no freshness claim for z).
  - **Tier B:**
    - the Counter is a near-identity module over `own` as an atomic faa register;
    - memory grounding is the history-level declarative bridge (G-1), with the x86 end-to-end theorem (G-2) optional;
    - existing register-cell SeqLock files get comment-only header notes labelling them the forwarding-free instance, and stay in the mechanization table as such (task R-1).
- **2026-10-13 — After the Q6-evidence review (M-12, M-4), author's answers:**
  - **Old register-cell results** (`SeqLockModule`, `SeqLockClients`, `SeqLockLB`, and `SeqLockCOH`'s z-composition parts) are **removed from the paper's mechanization table**. They stay in the repository as development history and comparison. This supersedes the earlier "keep them in the table as the forwarding-free instance". Q6-2 showed that label is wrong: the register-cell results cover only the publication-at-response, forwarding-free class of underlays. Task R-1 becomes comment-only header notes saying this, with no paper role.
  - **Order:** the ARM check G-3 moves forward. The order is Phase 0 wrap-up → F-1, F-3 and G-3 → F-2. G-3 includes the TicketLock version-word question (whether, on ARMv8 under issue-time responses, the abstract TicketLock also needs a hidden publication point) and produces herd7 test files for the author.
  - **LatchSet (flagship 2)** is designed directly on the buffered-cell infrastructure. The Q6-2 obstruction applies to any register-cell underlay grounded in x86/ARM. LatchSet starts after the Phase 1–2 foundations and still needs the author's definition of "write snapshot".

- **2026-10-13 (after T-1 review, M-18): priority, ARM, flush events.**
  - **Priority: LatchSet first.** This follows the author's paper edits: overview.tex makes LatchSet → WriteSnapshot the vertical-composition case study, and the intro claims both are verified.
    - The SeqLock buffered route (F-2 → S-1 → S-2 → D-2) and the tower (T-2/T-3) come after LatchSet.
    - T-1 is finished as is (minor fixes only).
  - **ARM: option C (x86-TSO only).**
    - ARMv8 is stated as a limitation, and the code is unchanged.
    - F-2 is unfrozen, under the constraint that the TicketLock module theorem is not presented as ARM-sound for arbitrary clients.
    - M-15's client-visible cases (the TicketLock interface; Δ3 for ≥2-cell interfaces, LatchSet included) are part of the ARM limitation.
  - **Flush events: not yet.**
    - The Coq trace model (`RelaxedTraceLin`) stays as is; flushes remain hidden inside the specs (buffered-cell redesign).
    - The paper's trace.tex now adds `{flush, ok}` to M_E and drops the handle-name component. This paper/Coq difference is recorded, not mechanized.
- **2026-10-13: LatchSet design (author).**
  - **Object:** the sorted-array LatchSet of `async-ccal/drafts/relaxed-lin/Claude outputs/litmus-check/tests_latch_set.py`.
    - Two copies of a small sorted array (size + keys) behind a latch `seq`, with wmb/rmb.
    - `insert(k)` shifts cells in place in each copy.
    - `contains(k)` is a linear scan whose reads depend on the `seq` read through the base address (`FutureD`).
    - The checker's verdicts: the full idiom forbids the bad `contains`; each of the five broken variants allows it.
  - **Writers:** single-writer discipline, as a client precondition in the spec (at most one insert in flight); no lock.
  - **WriteSnapshot:** LatchSet only for now. WriteSnapshot stays paper-level, because `rel_lin` and LinCCAL target only sequential/atomic specs. **The paper must not claim WriteSnapshot is mechanized** until an interval target exists in Coq.
- **2026-10-13: LatchSet decisions after the design review (B-5, precision, details).**
  - **Spec: buffered set ν_BS.** A sequential set with hidden FIFO publication markers. Non-writers see published inserts; the writer sees its own issued inserts. ν_Set ⊆ ν_BS. The paper's "atomic set specification" (overview.tex:278/300/329) must change accordingly.
  - **ARM: "we want latch set over ARM v8".** This overrides option C for LatchSet: the LatchSet result must target ARMv8. Option C (x86 only) stands for the SeqLock route unless the author says otherwise. The ARM route for LatchSet (compilation scheme and/or ARM grounding of ν_{I_tab}; cf. G-3, M-15, m-45) is to be planned; see `latchset-plan.md`.
  - **Details:**
    - P1 = one designated writer thread, whose inserts are pairwise non-overlapping;
    - contains exports DR (not Rmb);
    - no MP-through-latch client for now.
- **2026-10-13: LatchSet must support all overview claims (author instruction). Decisions after the claim-coverage workflow** (`latchset-claim-coverage.md`):
  1. **Spec: atomic set (ν_Set = `nuset_from`) with a trailing `smp_mb` in insert.**
     - x86: MFENCE or a locked RMW; ARMv8: DMB ISH.
     - Exports: insert ↦ DRFence (= emb RFence), window [wmb0, mb]; contains ↦ DR.
     - **ν_BS is withdrawn** (it reverses the earlier entry of the same day). CE1 and CE2 remain the evidence for why the fence is needed.
  2. **Write-snapshot and vertical composition: full chain.**
     - First, the interval target `rel_lin_ev` and the write-snapshot module theorem.
     - Then relaxed vertical composition (`vcomp`, XL) and the end-to-end write-snapshot theorem.
     - This reverses "WriteSnapshot not mechanized for now". Until `vcomp` lands, ov:339's vertical step is stated as paper/TR-level.
  3. **ARMv8: litmus now, grounding later.**
     - Now: litmus-level validation of the final code in ARMBar's three readings, plus herd7 files (the author runs herd7). The ARM code mapping is fixed now.
     - Theorems are grounded in x86-TSO. Full ARMv8 grounding is a research task; the paper says "litmus-level" until it lands.
  4. **The §3.7 rewordings of the coverage file are approved.** These are the paper-wording targets:
     - compatible → window dominance;
     - disjoint underlays → disjoint locations of one memory;
     - "admits LB" → the interface permits LB (shown with a client cell; x86 never exhibits it);
     - RC11 soundness → coherence containment;
     - RLHL "verifies LatchSet" → a semantic module theorem;
     - dependencies → hand-annotated and audited;
     - the wait/control wording at ov:23 and in:28;
     - complete executions only;
     - in:105 memory-model wording.
  - **Defaults taken by the orchestrator** (the coverage file's recommendations, unless the author says otherwise):
    - decision 2: drain placement = trailing mb;
    - decision 3: new memory/ infrastructure in new files;
    - decision 6: joint memory for the n components;
    - decision 8: WS definition = the 2023 `nu_writesnap` with participant ids;
    - decision 11: hand-written tags plus an audit lemma;
    - decisions 12/13/16: keep rhb clause (i) thread-agnostic; conservative extension on complete traces; complete executions only;
    - decision 18: commit the scratch evidence.
