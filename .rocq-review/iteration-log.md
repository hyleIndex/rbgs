# Iteration log: /rocq-loop

Append-only. Each `/rocq-loop` iteration adds one entry in the format given in `.claude/skills/rocq-loop/SKILL.md` (Step 11). Do not rewrite past entries. Record corrections as new entries.

## 2026-10-13 — setup — iteration 0 (baseline; no Rocq changes)

- **HEAD:** `dcccce0` (relaxed-lin), plus 19 uncommitted files (unchanged by this session).
- **Task:** create the Writer–Reviewer configuration and a baseline audit. No `.v` file was edited.
- **Files created:**
  - `.claude/agents/rocq-writer.md`
  - `.claude/agents/rocq-research-reviewer.md`
  - `.claude/skills/rocq-loop/SKILL.md`
  - `.rocq-review/{research-intent,concern-matrix,latest-review,iteration-log,popl2027-reviews}.md`
  - `.rocq-review/.gitignore`
  - `CLAUDE.md` (new; none existed)
- **Verification:**
  - Clean build with Rocq 9.2.0 / Stdlib 9.2.0 (from source) in a cloud container, with the uncommitted files overlaid: 171/171 files, 251 s at -j2.
  - No admits.
  - `Print Assumptions` of 109 key theorems ⊆ {`eq_rect_eq`, `classic`, `Parameter A` (3 view examples)}.
  - `rocqchk` crashes on `models/Sets.v`.
  - The author's machine was **not** built: the session's shell on that computer has no Rocq toolchain installed.
- **Review:** baseline by the orchestrator, not by `rocq-research-reviewer`. BLOCKER 4, MAJOR 9, MINOR 7. Verdict: continue; the RLHL judgement needs redesign.
- **Escalated to the author:** Q1–Q5 in `research-intent.md` §7, and the missing `claude/…` notes cited by `todo-oopsla.md`.
- **Concern-matrix rows changed:** all rows created.

## 2026-10-13 — author decisions (no Rocq changes)

- Scope fixed to oMCA. Priority: LatchSet + write snapshot, SeqLock on COH.
- Q1 clarified: the RLHL issue is the Coq encoding (one-path Wait rule, global queue equality, no rely, no soundness theorem) and the paper's existential OStep, not the paper's EStep rule. Recorded in research-intent.md §8; queue updated in concern-matrix.md §6.


## 2026-10-13 — loop RLHL (group: RLHL-1 → RLHL-2 → RLHL-3) — preconditions and author decisions

- **HEAD at start:** `6e2b575` (branch `rlhl`, worktree `rbgs-rlhl`), tree clean.
- **Toolchain:** Rocq 9.2.0 not installed. Homebrew Rocq changed from 9.1.0 to 9.3.0 at 05:49 during setup (not by the orchestrator). Author: "let's use the newest rocq" → all builds in this loop use Homebrew Rocq 9.3.0 (`PATH=/opt/homebrew/bin:$PATH`; bare `coqc` resolves to an opam 8.15.2 switch).
- **Baseline build (9.3.0, `make -k -j10`, 181 s):** 170/171 files. `structures/DCPOs.v` fails at :488 ("[record_fields] expected after '{'", a record field named `is`); no file imports it. coqrel rebuilt from scratch (its artifacts had been built by coqc 8.15.2).
- **Admit/axiom grep:** clean (only comments and Module Type `Axiom` fields in `interfaces/`).
- **Print Assumptions (45 key theorems of concern-matrix §4):** identical to the matrix: closed / `eq_rect_eq` / `classic` / `eq_rect_eq + classic`, plus `Parameter A` in ExchangerTSO, TryStackTSO, EBStackTSO.
- **Source checks for RLHL-1 (orchestrator, against the code):** `RelaxedLogic.HTripleProvable` (:869) is existential; `provable_wait_pending` (:970) takes one `ret`; `DebtCertificate` (:814) applies only when `queue_invariant` (RelaxedAssertion.v:183) equates the obligations with the whole module queue; `Stable`/`TStable` unused; `RelaxedTaggedLogic` has the same structure. The paper's RLHL rules (Appendix/programlogic.tex:512–549) reason in program order over blocking source calls (EStep); :308 claims wsc-indep lets the logic treat a method's out-of-order events as interference, but no printed rule does this. The COH SeqLock program (`examples/Relaxed/SeqLockProg.v:220–237`) issues up to five outstanding futures per method.
- **Author decisions (also in research-intent §8):** (1) futures semantics with dependency-only waits ("the wait should only block the later invocation with actual data dependence"), i.e. the tagged frontier (F1)–(F3), no blocking restriction; (2) single possibility; (3) RLHL as a conservative extension of LHL ("the thing in paper actually follow this idea, but we may need some extra changes"); (4) a method's own reordered events are interference (Owicki–Gries on the call's dependency dag), semantic per-call triple underneath; (5) generic underlay LTS `VE`.
- **Consequence outside RLHL-1, recorded for the author (not acted on):** decision (1) settles D5/Δ3 in the "only what ARM's dob orders" direction. The paper and Coq still describe the barrier reading: Mem.tex:524–533 ("Since wait is a sequential command it emits the source read's response before the invocation of everything po-after it"), Δ3 (Mem.tex:568–574), hypothesis (W) `dep;po? ⊆ pre` (Mem.tex:738–753; `ARM.v` `HW_dep`/`HW_dep_po`, `ARMDecl.v` Containment section). Under dependency-only waits (W)'s `dep;po` half no longer holds for compiled programs; the hypothesis would become the dependency part of `dob` (addr ∪ data ∪ ctrl;[W] ∪ addr;po;[W]). Candidate follow-up task (E3/D5): restate (W), re-prove `arm_containment`, and examine the converse direction.
- **Claim ↔ Coq mapping for RLHL-1:** see the Writer brief (RLHL-1.1). Rows: RLHL rules (programlogic.tex:492–549) ↔ `RelaxedTaggedLogic.THTripleProvable` (existential) → redesign; own-event interference (programlogic.tex:308, implex.tex:3, relaxedlin.tex:625) ↔ none; Logic Soundness (programlogic.tex:498, implex.tex:170) ↔ none (RLHL-2); conservative extension of LHL (intro.tex:111–113) ↔ `RGILogic` (SC) as template; completeness (implex.tex:3) ↔ out of scope (single possibility).

### Superseded review (archived summary before overwriting `latest-review.md`, 2026-10-13)
- Iteration 0 baseline (orchestrator audit, not by `rocq-research-reviewer`): BLOCKER B-1 (existential RLHL, no link to rel_lin), B-2 (no object/client verified via RLHL/VLHL; §6.3 inaccurate), B-3 (memory models not connected to the object level), B-4 (paper prints statements the Coq refutes); MAJOR M-1 (complete traces only), M-2 (no general composition theorems), M-3 (weak non-vacuity witnesses), M-4 (RC11/ARM correspondence partial), M-5 (OOTA unmechanized; hand-written tags), M-6 (Counter_xy, weak HW queue not mechanized), M-7 (client verification thin), M-8 ("advantage" evidence mostly memory-level), M-9 (single possibility vs sets); MINOR m-1…m-7. Only B-1 is in RLHL-1's scope; the others remain open as recorded there.

## 2026-10-13 — loop RLHL-1 — iteration 1

- **HEAD before/after:** `6e2b575` → uncommitted.
- **Task:** RLHL-1.1, a universal RLHL over `module_step_tagged` (dependency-only waits), a conservative extension of single-possibility LHL, own reordered events as Owicki–Gries interference, sound against an explicit per-call triple. Concerns: latest-review B-1; matrix B3/B-post, Meta-4.
- **Process.** The first Writer agent stalled after the move to the desktop app: no files written, no tokens used after resume. The orchestrator stopped it and, with ultracode on, re-ran RLHL-1 as a workflow:
  - three read-only designers took angles A (pending-obligation context), B (annotated trace) and C (semantic-first);
  - a read-only judge picked A (8/10, against B 6 and C 5.5) and grafted on B's Wait-slot and per-method I-preservation;
  - one `rocq-writer` implemented the result.
- **Writer:**
  - New files: `models/simlin/RelaxedHoare{Base,Dag,,Sound}.v` and `examples/Relaxed/RelaxedHoareChecks.v` (about 3,780 lines), added to `_CoqProject`.
  - Header-only "superseded" notes in `RelaxedLogic`, `RelaxedTaggedLogic`, `RelaxedAssertion`, `RelaxedProofState` and `RelaxedRGISimulation`.
  - Main results: `RProvable` (universal), `method_sound` (derivation ⇒ `MethodSem`), `cprov_call` (blocking rule with LHL's `provable_vis` shape), and B(a)–B(c) checks.
  - Disclosed deviations:
    - the proof state is `State VE * Poss VF` rather than `TaggedModuleConfig * Poss`;
    - the example overlay signatures make every pair semi-independent, so they are not `well_formed`;
    - the B(b) queue is written by hand;
    - open issue 1, same-thread linearization order, raised as NEEDS-AUTHOR.
  - Report: `.rocq-review/writer-report-latest.md`.
- **Verification (orchestrator, Rocq 9.3.0):**
  - Existing `.v` files: comment-only diff; no declaration changes.
  - The new files' build products were deleted and the files rebuilt from scratch: 175/176 compile, and the only failure is the known `structures/DCPOs.v`.
  - Admit/axiom/vm_compute grep: clean.
  - `Print Assumptions`: all 180 lemmas and theorems of the new files are closed; the 45 baseline theorems are identical to the baseline.
- **Review:**
  - Run as a workflow: three lens reviewers (`rocq-research-reviewer`), a skeptic verifier per lens, then a synthesis.
  - Counts: BLOCKER 2 (B-1 narrowed; B-5 new), MAJOR 6 (M-10…M-15), MINOR 7 (m-8…m-14).
  - Verdict: "Continue, with a partial redesign of the semantic triple (not of the rules), gated on a research-level decision (B-5), before RLHL-2."
  - Saved verbatim to `latest-review.md`.
- **Factual check by the orchestrator:** B-5's counterexample `counter_methodsem_unsat` (latest-review Appendix) compiles and prints "Closed under the global context". I also re-read `select_frontier_tagged`/`must_precede`: the module never emits a later same-thread call's non-semi-independent invocation before an earlier call's. So the counter is correct and `MethodSem` is too strong. B-5 is confirmed.
- **Disputes:** none marked DISPUTED. The Reviewer rejects four Writer claims, and the orchestrator agrees with all four, which match the code:
  - that "open issue 1" is the real defect: helping is expressible, and B-5 is the real one;
  - that `cprov_call` corresponds "one to one" to `provable_vis`: the error premises are dropped;
  - that B(c)'s `¬before` facts are used: they are not;
  - the B(a) "wrong program" framing.
- **Escalated to the author:** B-5 (how to restore cross-call same-thread F2 order in the semantic triple: ghost per-thread frontier, history-based state, or restricting overlap), with M-13/M-15 tied to it.
- **Concern-matrix rows changed:**
  - B3/B-post sub-item (i) now 🟡, and `prop:rlhl-sc` moved out of that row (it is a VLHL claim);
  - §3 "RLHL rules" and "Prop. Logic Soundness" updated; `prop:rlhl-sc` row annotated;
  - new §3 rows: conservative extension (🟡), implex.tex:3 (⚠️), intra-thread cross-call ordering (❌), underlay errors (📝);
  - §4 regression list extended;
  - §6 queue: B-5 decision before RLHL-2.
- **Author decision after iteration 1 (B-5):** "Ghost thread frontier", recorded in research-intent §8. The other two options were full concrete state and restricting overlap. Iteration 2 implements it together with the actionable findings.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-1 iteration-1 review
- BLOCKER: B-1 (narrowed: universal judgement sound against a per-call triple, no link to `GSimRel`/`rel_lin`); B-5 (`MethodSem` unsatisfiable for an overlapping same-thread counter: F2 lost).
- MAJOR: M-10 (B(a) not discriminating), M-11 (no non-trivial own-event OG instance), M-12 (B(b) hand-written queue), M-13 (ill-formed overlay signatures), M-14 (A5 rule-level only, no loop rule), M-15 (paper RLHL statements differ from Coq).
- MINOR: m-8 … m-14.

## 2026-10-13 — loop RLHL-1 — iteration 2

- **HEAD before/after:** `6e2b575` → uncommitted.
- **Task:** RLHL-1.2. Implement the author's B-5 decision (ghost thread frontier) and the actionable iteration-1 findings (M-10…M-14, m-9…m-14).
- **Process:** a workflow with one read-only designer (Plan agent) formulating the ghost against the code, then one `rocq-writer`.
- **Writer:**
  - Proof state `State VE * Poss VF * Ghost`. The ghost is a single global list of pending underlay invocations; `gthread` filters per thread, and cross-thread order is unused because `inv_blocks` is False across threads. This realizes the author's "per-thread component"; m-18 asks for it to be recorded, which is done here.
  - Redesigned `CallTriple`/`MethodSem`: `ghost_emit` in emit, `NoOwn` at return, `ghost_new` at init. `method_sound` re-proved.
  - The iteration-1 triple is kept as `RelaxedHoareBase.Iter1`; this is a qualified rename, reported.
  - Acceptance theorem `Counter.counter_b5`: the old triple is unsat for the counter, the new one holds.
  - Loop rules `rp_dowhile`/`cprov_dowhile`; A5 renamed "LHL's call rule (without error premises) is derivable in the blocking fragment".
  - Checks rewritten on well-formed signatures; `RLHL2Hyps` Record; `two_calls_*` derived from module steps.
  - Semantic changes are listed in the report: the meaning of the triple changes, which is the task.
- **Verification (orchestrator, Rocq 9.3.0):**
  - Tracked `.v` files: still header-only, 0 declaration lines changed.
  - The five files rebuilt from scratch; 175/176, only `DCPOs.v` fails.
  - Grep clean.
  - All 332 lemmas and theorems closed.
  - 45 baseline theorems identical.
  - `Check counter_b5` / `method_sound` / `methodsem_of_iter1` match the report.
- **Review:**
  - Counts: BLOCKER 1 (B-1, scheduled as RLHL-2); MAJOR 4 (M-16 new, M-17 new, M-11 partial, M-15 author); MINOR M-14 (downgraded), m-15…m-19, m-8, m-12.
  - Resolved: B-5, M-10, M-12, M-13, m-9, m-10, m-11, m-13, m-14.
  - Verdict: "Continue. No redesign."
  - M-16 is a gate for RLHL-2.
- **Factual status of M-16:** it rests on reviewer scratch proofs (`rlhl2_counter_unsat`, `counter_rlhl2_unsat`, `counter2_rlhl2_unsat`) reported closed by three independent reviewer agents. The full script is elided in the output, so the orchestrator could not re-run it. It is not disputed: the Writer's own open issue 1 says the counter violates G ⊆ R and that a used-key ghost may be needed. Its acceptance item (i) puts a negative regression theorem into the checks file, where it will be kernel-checked.
- **Escalated to the author:**
  - M-16: (a) a handle-linear VE hypothesis, recommended by the Reviewer, or (b) a used-key ghost.
  - M-17: the specification style for same-thread order and HVF.
  - Still pending from iteration 1: M-15 (paper rewrite), m-8 (scope statement), m-12 (auxiliary state).
- **Concern-matrix rows changed:**
  - B3/B-post sub-item (i) text, still 🟡;
  - "RLHL rules" and "conservative extension" notes updated;
  - "intra-thread cross-call ordering" ❌ → 🟡;
  - new rows: underlay-key freshness ❌, spec style and HVF ❌, relatedwork.tex:32 ⚠️, relaxedlin.tex R_π 📝;
  - §4 list extended.
- **Author decisions after iteration 2:** M-16 → handle-linear VE (fallback: used-key ghost); M-17 → effect-at-invocation specs plus a generic HVF lemma. Recorded in research-intent §8, together with the global-list realization of the ghost (m-18).

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-1 iteration-2 review
- BLOCKER B-1 (scheduled as RLHL-2).
- MAJOR: M-16 (no underlay-key freshness; RLHL2Hyps unsatisfiable for overwriting per-key counters), M-17 (helping vs HVF), M-11 (partial), M-15 (paper).
- MINOR: M-14 (downgraded), m-15 … m-19, m-8, m-12.
- Resolved in iteration 2: B-5, M-10, M-12, M-13, m-9, m-10, m-11, m-13, m-14.

## 2026-10-13 — loop RLHL-1 — iteration 3 (final iteration of RLHL-1)

- **HEAD before/after:** `6e2b575` → uncommitted.
- **Task:** RLHL-1.3. Implement M-16 as a handle-linear VE (author decision) and M-17 as effect-at-invocation specs with a generic HVF lemma (author decision), plus minors m-15 … m-19, M-14 and part of M-11.
- **Writer** (one `rocq-writer` in a workflow):
  - Base: `HandleLinear` (a property of VE, not a soundness hypothesis), pool-domain lemmas, `poss_invoke_exists`.
  - New `models/simlin/RelaxedHoareSpec.v`: `vt_handle_linear`, `hl_path_inv_unique`, `EI`, `ei_hvf`.
  - Checks: `CounterHL` (`counter_ow_unsat`, `counter_hl_rlhl2`), `IncTwo`, `TwoCallsGen` (`gtwo_*`), `LogRead`; `tas_not_hvf`, `pair_not_hvf`.
  - `_CoqProject` adds Spec and moves Checks after ViewLHL.
  - The triple, `MethodSem`, `RLHL2Hyps` and `method_sound` are unchanged.
- **Verification (orchestrator, Rocq 9.3.0):**
  - Tracked `.v` files still header-only.
  - The six RLHL files rebuilt from scratch: 176/177, only `DCPOs.v` fails.
  - Grep clean.
  - All 472 lemmas and theorems closed.
  - 45 baseline theorems identical.
- **Review** (workflow; the synthesis step was re-run after a network error, with the lens results replayed from cache):
  - Counts: BLOCKER 1 (B-1, RLHL-2 scope); MAJOR 3 (M-18 new and research-level; M-11 partial, gated on M-18; M-15 author); MINOR m-20 … m-23 new, m-18, m-15 residual, m-8, m-12, M-14 resolved.
  - Verdict: "stopping iteration on RLHL-1 and continuing to RLHL-2 … no redesign of the logic"; the specification layer is possibly to be redesigned before RLHL-3, which is the author's decision.
- **Factual checks by the orchestrator:** re-ran the reviewers' complete scripts `memlts_not_hl`, `hve_not_complete` (two independent scripts) and `vt_junk`; all are Closed. The M-18 impossibility argument itself is prose, not mechanized; the review proposes mechanizing it as `counter_vt_no_gsim`.
- **Disputes:** none.
- **Escalated to the author:**
  - M-18: overlay spec style × complete underlay presentation. Options: `VT nuF` overlay, deferred-result EI, EI with abort, prophecy-visible ghost or possibility sets, or restricting claims.
  - M-15 now includes the working-tree `intro.tex:115` claim of RLHL-verified latch/write-snapshot case studies, which no RLHL instance supports.
  - m-8 and m-12 remain open.
- **Concern-matrix rows changed:**
  - B3/B-post sub-item (i) text (🟡);
  - underlay-key freshness ❌ → 🟡;
  - spec style ❌ → 🟡;
  - new rows: end-to-end route (❌, M-18), HL WLOG (❌, m-20), possibility sets (🟡), intro.tex:115 (⚠️);
  - §4 list extended.

## 2026-10-13 — RLHL-1 closed after 3 iterations

- **Stop rule met.** Step 9: the remaining in-scope items are research-level (M-18, M-15, m-8, m-12), or depend on M-18 (M-11's substance needs the chosen spec style), or belong to RLHL-2 (B-1, m-21).
- **Delivered (K):**
  - a universal RLHL judgement (`RelaxedHoare.RProvable`) over the dependency-only tagged futures semantics, with per-call rely/guarantee, own reordered events as Owicki–Gries premises, loop rules, and LHL's call rule derivable in the blocking fragment;
  - an explicit semantic per-call triple with a ghost thread frontier (`RelaxedHoareBase.MethodSem`), and soundness `method_sound`, all closed;
  - module ⇒ triple interface lemmas (`select_project`, `ghost_of_*`); the `RLHL2Hyps` bundle; a generic HVF lemma (`ei_hvf`); a two-call GSim prototype (`gtwo_*`).
- **Not delivered:** the bridge to `GSimRel`/`rel_lin` (RLHL-2), a weak-memory VE, an object with its client (RLHL-3), and the paper rewrite (author).
- **Next in the group:** RLHL-2. It is generic in VF with HVF explicit, so the review finds it unaffected by M-18. RLHL-3 waits for the M-18 decision.

## 2026-10-13 — loop RLHL-2 — iteration 1 started

- Workflow with one `rocq-writer`, brief "RLHL-2.1". Targets:
  - `rlhl_gsim : RLHL2Hyps ⇒ ∃ S, GSimRel ∧ S initial`, generic in VE/VF and in the number of calls;
  - the m-21 lemmas;
  - `rlhl_rel_lin` (via `gsim_rel_lin`, with HVF and complete traces named) and `rlhl_rel_lin_pres` (via `presentation_choice`);
  - an end-to-end CounterHL instance over HVE with HVF discharged by `ei_hvf`;
  - a header mapping to programlogic.tex:498-505 and relaxedlin.tex:709.
- Constraint: no change to the RLHL-1 definitions, and `HandleLinear` must not become a hypothesis; any insufficiency of `RLHL2Hyps` is to be reported as NEEDS-AUTHOR.
- **Author decisions while RLHL-2 runs:** M-18 → stamp-based VT overlay (`VF := VT nuF`) for RLHL-3. intro.tex:115 latch/snapshot sentence → keep, and plan an RLHL latched-set instance after RLHL-3. Recorded in research-intent §8 and the concern matrix.
- **RLHL-2 iteration 1, Writer finished and orchestrator verification done** (Rocq 9.3.0):
  - New `models/simlin/RelaxedHoareGSim.v` (`rlhl_gsim`, `rlhl_rel_lin`, `rlhl_rel_lin_pres`, EI corollaries, m-21 lemmas) and `CounterRelLin` in the checks file; `_CoqProject` +1 entry.
  - Tracked `.v` files: still 0 declaration changes. Grep clean.
  - The seven RLHL files rebuilt from scratch; 177/178, only `DCPOs.v` fails.
  - 515 lemmas: 507 closed, 8 `eq_rect_eq` only (`rlhl_rel_lin*`, `counter_rel_lin`, `inc_ooo_rel_lin`, `inc_bad_no_exec`, `finish_stored_ret`), inherited from `gsim_rel_lin` or `inj_pair2`.
  - 45 baseline theorems identical.
  - `Check rlhl_gsim` / `counter_rel_lin` match the report.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-1 iteration-3 review
- BLOCKER B-1 (RLHL-2 scope).
- MAJOR: M-18 (EI × complete VT infeasible; research-level), M-11 (partial), M-15 (author).
- MINOR: m-20 (HL WLOG), m-21 (RLHL-2 readiness), m-22 (`cprov_call` P' independent of h), m-23 (weak checks), m-18, m-15 residual, m-8, m-12; M-14 resolved.
- Verdict: stop RLHL-1, continue to RLHL-2.

## 2026-10-13 — loop RLHL-2 — iteration 1

- **HEAD before/after:** `6e2b575` → uncommitted.
- **Task:** RLHL-2.1, RLHL2Hyps ⇒ GSimRel ⇒ rel_lin. Concerns: B-1 (Required items 1-4 of the RLHL-1 iteration-3 review), m-21.
- **Writer:** new `RelaxedHoareGSim.v`, containing:
  - `RSim`;
  - `rlhl_gsim` (closed, any number of calls);
  - `rlhl_rel_lin` and `rlhl_rel_lin_pres` (`eq_rect_eq`);
  - the EI corollaries and `rlhl2_of_provable`;
  - the m-21 lemmas.

  Checks: `CounterRelLin` (`counter_rel_lin`, `inc_ooo_exec`, `inc_bad_*`, `hve_not_complete`). No existing definition changed.
- **Verification:** see the entry above. Rebuilt from scratch; 515 lemmas, 507 closed and 8 `eq_rect_eq`; baseline identical.
- **Review** (workflow):
  - Counts: BLOCKER 2 (B-1 narrowed: RLHL-2 part FIXED, residual for RLHL-3; B-4, intro.tex:105 memory claims, outside scope); MAJOR 4 (M-1 prefixes/`implements`, research-level Q3; M-19 nonempty-SI instance, actionable; M-18 route decided, not implemented; M-15 author); MINOR m-18, m-23, m-24, m-25, m-26; m-21 resolved.
  - Verdict: the bridge is "established … needs no redesign"; stop iterating RLHL-2 after cheap documentation fixes; proceed to RLHL-3 with the acceptance list VT×VT (M-18), nonempty SI (M-19) and the Q3 decision (M-1).
- **Factual checks by the orchestrator:** re-ran the m-24 script `bad_counter_no_rlhl2` (`∀ I R G, ¬RLHL2Hyps` for a bad counter): it checks, using `eq_rect_eq` only.
- **Disputes:** none. The Reviewer rejected as stale the Writer's "M-18 NEEDS-AUTHOR" (decided at research-intent §8); the orchestrator agrees.
- **Escalated to the author:**
  - Q3/M-1: complete traces only, or prefix soundness (`implements`) for layering.
  - B-4: intro.tex:105 memory-correspondence claims.
  - M-15 additions.
- **Concern-matrix rows changed:**
  - B3/B-post sub-item (i) text and next action;
  - "Prop. Logic Soundness" ❌ → 🟡;
  - "RLHL rules" note; intro row citations;
  - "Intra-thread cross-call ordering" note;
  - new rows: intro.tex:105 (⚠️/❌), RLHL layering (❌), nonempty-SI instance (❌), universal negatives (❌);
  - §4 extended.
- **Author decision during RLHL-2 iteration 2:** Q3/M-1 → prove prefix soundness (`gsim_implements`/`rlhl_implements`, two-layer composition through `presentation_choice`) as part of RLHL-3. Recorded in research-intent §8.

## 2026-10-13 — loop RLHL-2 — iteration 2 (Writer + verification)

- **Writer:** cheap fixes from the RLHL-2 iteration-1 review.
  - Headers aligned with M-18 and the I=∅ label.
  - New theorems: `rlhl_sound` (LHL-shaped soundness), with the premise table against `RGILogic.soundness`; `counter_rel_lin_by_rules`; the adopted universal negative `bad_counter_no_rlhl2`.
  - `vt_junk` (for every initial stamp map).
  - Beyond the brief: `vt_junk_not_rl_prefix`, `vt_not_implements` and `counter_vt_no_rlhl2`, which mechanizes the M-18 impossibility for the counter over `VT`.
  - No existing definition changed.
- **Verification (orchestrator):**
  - Tracked `.v`: 0 declaration lines. Grep clean.
  - The seven RLHL files rebuilt from scratch; only `DCPOs.v` fails.
  - 535 lemmas: 524 closed, 11 `eq_rect_eq` only, as reported.
  - Baseline identical.
  - `Check` confirms `vt_not_implements : ∀ H0, ¬ implements unu (VT unu) (mkV [] H0)`, `counter_vt_no_rlhl2` and `vt_junk_not_rl_prefix`.
- **Consequence for the Q3/M-1 plan (raised by the Writer, confirmed by the orchestrator from the statements):** "every VF path is an `rl_prefix`" is NOT free for `VT`. `VT` accepts dead-end prefixes. So the prefix-soundness route via the stamp-based `VT nuF` overlay needs another premise or another presentation. Escalated to the author.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-2 iteration-1 review
- BLOCKER: B-1 (narrowed; RLHL-3 residual), B-4 (intro.tex:105 memory claims; author).
- MAJOR: M-1 (prefixes/`implements`, Q3), M-19 (nonempty SI), M-18 (route decided, not implemented), M-15 (author).
- MINOR: m-18, m-23, m-24, m-25, m-26; m-21 resolved.

## 2026-10-13 — loop RLHL-2 — iteration 2 (review) and close

- **Review** (workflow):
  - Counts: BLOCKER 2 (B-1 continues, RLHL-3 residual; B-4 author); MAJOR 6 (M-1: the recorded Q3 route is refuted; M-20 new: prefix notion K/REW/V; M-18; M-19; M-15; M-21 new: paper rule figures not mapped); MINOR m-27, m-28 (EI fails over dead-end-free presentations too, argued), m-29, m-24, m-23. Resolved: m-18, m-25, m-26.
  - Verdict: "RLHL-2 delivers what it claims. Stop iterating on it. … The bridge needs no redesign." The RLHL-3 presentation plan must be redesigned before implementation; this is research-level.
- **Factual checks by the orchestrator:** re-ran the review's scratch proofs.
  - S1 `vt_underlay_no_rl_prefix_overlay`: closed. Over VE := `VT unu`, no VF whose paths are all rl_prefixes admits a GSimRel for the correct counter.
  - S2 `vt_overlay_not_rl_prefix`: `eq_rect_eq`.
  - S3 `vtF_not_implements`: closed. It was assembled from the review's body plus S2's preamble, as the review instructs.
  - RP lemmas: `rp_complete` and `rp_implements` closed, `rp_sound` `eq_rect_eq`.
- **Records corrected:**
  - research-intent §8, Q3 entry: struck "(free for the stamp-based VT nuF overlay)".
  - M-18 entry: notes that VT×VT gives complete traces only.
  - The iteration-1 review's M-1 Required item 2 ("holds by construction for VT nuF") was wrong; corrected by this review.
- **Concern-matrix rows changed:**
  - RLHL layering row text;
  - new rows: prefix notion (⚠️, M-20) and paper rule figures (⚠️, M-21);
  - universal negatives ❌ → 🟡;
  - Prop. Logic Soundness mapped to `rlhl_sound`;
  - §4 extended.

## 2026-10-13 — RLHL-2 closed after 2 iterations

- **Stop rule met.** Step 9: the remaining in-scope items are research-level (M-1/M-20/M-21/M-15, B-4) or belong to RLHL-3 (B-1 residual, M-18 item 3, M-19).
- **Delivered (K):**
  - `rlhl_gsim` (closed; any number of calls);
  - `rlhl_rel_lin`, `rlhl_rel_lin_pres` and `rlhl_sound` (`eq_rect_eq`; HVF and Hcomplete named);
  - the end-to-end I=∅ counter over HVE (`counter_rel_lin`, `counter_rel_lin_by_rules`, `inc_ooo_exec`);
  - universal negatives (`bad_counter_no_rlhl2`, `counter_vt_no_rlhl2`);
  - VT dead-end facts (`vt_not_implements`).
- **Group status:** RLHL-3 depends on the M-20/M-1 decisions (prefix notion and presentation), so it is escalated before starting, per the skill's group rule.

## 2026-10-13 — RLHL-3 re-scoped after author decisions (no Rocq changes)

- **M-20/Q3:** the author said "follow the work in original RG sim, they also need to deal with the incomplete trace", then chose "Sequential spec, EI" for the copy-cat. So RLHL soundness = CompLin-style copy-cat trace inclusion over `EI δF`, which is the REW notion, with each layer verified over the sequential spec LTS below. Recorded in research-intent §8.
- **Effect on earlier decisions:** M-18's stamp-based VT pair is kept only for complete traces; Q3 is realized as copy-cat inclusion.
- **`tasks/RLHL-3.md`:** an "Adjustment" section was appended (the original text is kept). RLHL-3 is split into 3a (copy-cat soundness `rlhl_complin` + counter), 3b (nonempty-SI instance + relaxation witness), 3c (vertical composition + object/client).
- **Next:** start RLHL-3a.

## 2026-10-13 — loop RLHL-3a — iteration 1 (Writer + verification)

- **Task:** CompLin-style copy-cat soundness for all (incomplete) executions; author decision M-20/Q3.
- **Writer:**
  - New `models/simlin/RelaxedHoareCompLin.v`: `idF`, `MTraces`, `RTraces`, `RCompLin`, `reify`, `gsim_complin`, `rlhl_complin`, `rlhl_complin_ei`, `cc_trace`.
  - Checks: `CounterCompLin` (`counter_complin`, `ooo_copycat_trace`, `junkF_not_rtrace`, `junkF_not_counter_trace`).
  - `_CoqProject` +1 entry. No existing definition changed.
  - Optional item 5 (complete-trace link from RTraces(EI) to rel_lin) not done.
- **Verification (orchestrator):**
  - Tracked `.v`: 0 declaration lines. Grep clean.
  - The eight RLHL files rebuilt from scratch; 178/179, only `DCPOs.v` fails.
  - 611 lemmas: 592 closed, 11 `eq_rect_eq`, 8 `classic` (`rinv_val`, `rinv_reify`, `gsim_complin`, `rlhl_complin`, `rlhl_complin_ei`, `counter_complin`, `ooo_copycat_trace`, `junkF_not_counter_trace`). `classic` is baseline; the Writer says it is needed to decide whether a call already has an abstract response, since handles lack decidable equality.
  - Baseline identical.
  - `Print RCompLin` / `MTraces` and `Check gsim_complin`, `junkF_not_rtrace`, `counter_complin` match the report.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-2 iteration-2 review
- BLOCKER: B-1, B-4.
- MAJOR: M-1 (Q3 route refuted), M-20 (prefix notion), M-18, M-19, M-15, M-21.
- MINOR: m-27, m-28, m-29, m-24, m-23.
- Verdict: stop RLHL-2.

## 2026-10-13 — loop RLHL-3a — iteration 1 (review)

- **Review** (workflow):
  - Counts: BLOCKER 1 (B-1 narrowed); MAJOR 5 (M-20 narrowed to the meaning bridge; m-20 escalated to MAJOR, since `EI` is not handle-linear and T1 refutes RLHL2Hyps over plain EI; M-22 new, absorption/linking needed for layering; M-19; M-15 + write-snapshot scope); MINOR m-30, m-8 (CompLin TErr difference), m-32.
  - Status changes: M-1 closed for RLHL (VLHL residual); M-18 superseded for prefixes.
  - Verdict: "RLHL-3a delivers the author's decision, and its formulation is the right one … continue, no redesign. One more cheap RLHL-3a round is worthwhile."
- **Factual checks by the orchestrator:** re-ran the review scripts T1 (`EVE_not_handle_linear`, `counter_ei_unsat`) and T2 (`si_overtake_rtrace`). All are closed. Copies are kept in `.rocq-review/scripts/`.
- **Records corrected:**
  - research-intent §8, M-20 entry: REW agreement marked as argued; layering VE corrected to `EIhl` (T1).
  - Concern matrix: B3/B-post (i) text and next action; RLHL layering row ❌ → 🟡; prefix-notion row ⚠️ → 🟡.
- **Next:** RLHL-3a iteration 2. Research-level items go to the author: M-20(c), m-8, M-15 write-snapshot, and the memory route under B-1.
- **Author decisions during RLHL-3a iteration 2 (recorded in research-intent §8):** m-8 → add a TErr-like error clause (RLHL-3c); memory route → thread-aware buffered spec δ_mem, with the buffered cell shown to produce copy-cat traces; write-snapshot → plan an interval-spec overlay after RLHL-3c; M-20(c) → the paper defines correctness via copy-cat and presents REW as argued.
