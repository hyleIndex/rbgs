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

## 2026-10-13 — loop RLHL-3a — iteration 2 (Writer + verification)

- **HEAD:** the author committed `6aef511 "rlhl"` during this iteration. It contains the RLHL work so far and the `.rocq-review` records. The remaining uncommitted diff is in RLHL files only: 36 added declarations and removed header comment text, with no declaration removed.
- **Writer:**
  - New `RelaxedHoareCompLinSpec.v`: `gsim_rel_lin_traces`, `cc_gsim` (identity simulation), `cc_rel_lin`, `cc_trace_wf`, `complin_ei_rel_lin`, `rlhl_complin_ei_rel_lin`, `rlhl_rel_lin_ei_via_cc`, `HL`, `HL_handle_linear`, `hlift` (MTraces over VE ⟺ over HL VE), `EIhl`, `rlhl_complin_eihl`.
  - In `RelaxedHoareCompLin.v`: `mtraces_prefix`, `rtraces_prefix`, `rlhl_sound_complin`.
  - Checks: `CounterEI` (T1), `CounterEIhl` (`counter_eihl_rlhl2`, closed; `counter_complin_eihl`; non-vacuity executions), `WRCopyCat` (T2 and its I=∅ mirror `si_overtake_not_rtrace0`, `si_decides_overtake`).
  - Headers fixed (m-30); m-8 documented.
- **Verification (orchestrator):**
  - Older tracked files: still header-only relative to `6e2b575`. Grep clean.
  - The nine RLHL files rebuilt from scratch; only `DCPOs.v` fails.
  - 697 lemmas: 663 closed, 12 `eq_rect_eq`, 17 `classic`, 5 both. All baseline.
  - The 45 baseline theorems are identical.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-3a iteration-1 review
- BLOCKER: B-1 (narrowed).
- MAJOR: M-20 (meaning bridge), m-20 (EI not handle-linear; T1), M-22 (absorption/linking), M-19, M-15.
- MINOR: m-30, m-8, m-32.
- Verdict: continue, no redesign; one more cheap RLHL-3a round.

## 2026-10-13 — loop RLHL-3a — iteration 2 (review)

- **Review** (workflow; three lenses, skeptic per lens, synthesis):
  - Counts: BLOCKER 1 (B-1, narrowed again); MAJOR 5 (m-8 promoted, M-22, M-19, M-14 promoted, M-21); MINOR 7 (M-20 demoted to MINOR, new m-33 to m-37, m-24, m-30 residual).
  - Resolved: m-20 (HL, `hlift`, `rtraces_hlift`, `rlhl_complin_eihl`, `counter_eihl_rlhl2`), m-32, and the Coq part of M-20.
  - Verdict: "The RLHL-3a claims are established … The stop rule for RLHL-3a's actionable items is met once the cheap fixes (m-34, m-35, the M-20 relabel, m-30) are done. Proceed to RLHL-3b … Decision: continue. No redesign."
  - Rejected writer open issue: "a general EIhl instance would need an ownership notion in the proof state" (m-34 frame lemmas give a spec-independent rely).
- **Factual checks by the orchestrator:** re-ran the complete lens scratch scripts. `never_produced` (m-33) is closed; `FrameCheck.mine_step` and `mine_res` (m-34) are closed. Copies are in `.rocq-review/scripts/RLHL3a2_*.v`. The other lens checks (S1, S3) were cited by the review as single-line `exact` proofs or `well_formed` checks; S3 will be re-checked when m-35 is added to the repository.
- **Records:**
  - `latest-review.md` overwritten with this review.
  - Concern matrix: rows B3/B-post (Meaning, layering interface, Missing list), conservative extension 🟡 → ⚠️ (M-14), layering, prefix notion (relabel), rule figures (M-21 sub-items), nonempty-SI instance ❌ → 🟡 at copy-cat level, universal negatives, key freshness 🟡 → ✅, route ❌ → 🟡, HL WLOG ❌ → ✅, "sound and complete" (m-36), underlay errors 📝 → ❌ (m-8), Logic Soundness and Simulation rows; two new rows (run-to-completion m-33, thread-aware δ_mem m-37); §4 regressions for RLHL-3a iterations 1 and 2.
  - research-intent §8: M-20 entry records `cc_rel_lin` and its orientation; m-8 entry records the needed implementation-side obligation (amendment not yet put to the author); B-1 memory entry records the m-37 gap.
- **Research-level items for the author** (needed before RLHL-3c / RLHL-mem; RLHL-3b does not depend on them): m-8 amendment, m-37 (EIt vs tid-carrying ops), m-36 (completeness claim), m-33 (run to completion), M-14/M-21 paper wording.
- **Next:** RLHL-3a iteration 3 (cheap fixes: m-34 frame kit, m-35 `WRSig_wf` + header, M-20 relabel, m-30 residual, and m-24 universal `read_pair` negative), then RLHL-3b.

## 2026-10-13 — loop RLHL-3a — iteration 3 (Writer + verification)

- **HEAD:** 6aef511. Changes are uncommitted.
- **Task:** cheap actionable MINOR items of the iteration-2 review: m-34, m-35, M-20 relabel, M-22 header, m-30 residual, m-24; optionally the M-21 rule table.
- **Writer** (all FIXED; paper parts NEEDS-AUTHOR):
  - `RelaxedHoareCompLinSpec`: EIhl frame kit `eihl_rec_used`, `eihl_mine`, `eihl_steps`, `eihl_rec_used_{init,step,steps}`, `eihl_mine_{step,steps,res,inv}` (all closed).
  - Checks `CounterEIhlFrame`: a value-free counter instance. `counter_frame_rlhl2` is closed; the memory part of R/G is `eihl_steps`. Corollaries `counter_frame_complin_ei` and `counter_frame_rel_lin`; non-vacuity `ooo_rtrace_frame`.
  - Checks `ReadPairUniversal`: `read_pair_no_rlhl2` (∀ I R G; `classic`), `read_pair_no_rlhl2_gen` (side conditions `(σi X, 1) ≠ v0`, `σi X ≠ 1`), `pair_discriminates_rlhl2`, module-derived `rp_mtraces`.
  - `WRCopyCat.WRSig_wf` / `WRSig0_wf` (closed).
  - Headers: the `cc_rel_lin` label is now "ν;cc ⊆ rel_lin, the ⊇ half"; the `cc_gsim` role corrected (M-22); GSim item 10, item 15 and the end-to-end paragraph; M-21 rule table and further-differences list in `RelaxedHoare.v`.
  - The Writer could not write `.rocq-review/writer-report-latest.md` (harness restriction); the orchestrator copied the report there verbatim.
- **Verification (orchestrator):**
  - 58 declarations added, none removed. All 42 removed `.v` lines (relative to the pre-iteration tree) are header-comment text.
  - Grep: only baseline hits (`Assertion.v`, `AssertionOld.v`, `LazyCoin.v`, View examples).
  - `make -n` lists only `DCPOs.v`.
  - Statements checked with `Check`/`Print`. Notably `Rfm`/`Gfm` memory part = `eihl_steps uδ`, and `Ifm` keeps `ecnt = ca` and adds `eihl_rec_used`.
  - `Print Assumptions` of the 27 new and key theorems matches the report.
  - All 734 lemmas in the nine RLHL files: 692 closed, 12 `eq_rect_eq`, 23 `classic`, 7 both; nothing outside the baseline.
  - The 45 baseline theorems are identical.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-3a iteration-2 review
- BLOCKER: B-1.
- MAJOR: m-8 (promoted; implementation-side error obligation), M-22, M-19, M-14 (promoted), M-21.
- MINOR: M-20 (relabel), m-33, m-34, m-35, m-36, m-37, m-24, m-30.
- Verdict: continue, no redesign; RLHL-3a stop rule met after the cheap fixes.

## 2026-10-14 — loop RLHL-3a — iteration 3 (review); RLHL-3a closed

- **Review** (workflow; three lenses, a skeptic per lens, a synthesis):
  - Counts: BLOCKER 1 (B-1, unchanged); MAJOR 1 open in scope (M-19, now "ready"; m-8, M-22, M-14, M-21 carried unchanged); MINOR m-30 (range pointers), m-38 (new; `read_pair` core implicit), m-39 (new; absorption caveat at GSim item 10(a)), m-40 (new; research-level: I_RC lacks RMW rows, I_Counter_xy unprinted), m-41 (new; delta list incomplete), m-37 (narrowed), m-36 (two observations).
  - Resolved (verified): m-34, m-35, m-24, M-20 (Coq relabel), M-22 (header), m-30 (`.v` headers apart from ranges), M-21 (Coq-side table).
  - Writer claims accepted: σ0/v0 cannot be universally quantified in `read_pair_no_rlhl2_gen`; the ownership open issue is withdrawn; "Gfm's memory part is trivially met" is acceptable, because the invariant carries the values and it is sound to rely on.
  - Verdict: "RLHL-3a can be closed … Decision: stop RLHL-3a and proceed to RLHL-3b. No redesign."
- **Orchestrator:** the review proved nothing new in scratch sessions, so there is nothing to re-run. The claims it relies on (Print Assumptions, side conditions) match my iteration-3 verification.
- **Records:** `latest-review.md` overwritten. Concern-matrix rows: B3/B-post (frame kit, value-free counter; next action RLHL-3b), conservative extension (m-41), rule figures (mapped, range :476-557, m-41), nonempty-SI instance (RLHL-3b plan), universal negatives 🟡 → ✅, EI route, "sound and complete" (+ implex.tex:3), thread-aware δ_mem (narrowed), Counter_xy (RLHL-3b target); new rows m-40 and m-39; §4 regressions for iteration 3. research-intent §8: B-1 memory entry, m-37 narrowing recorded.
- **RLHL-3a outcome.** Closed after 3 iterations. Proved:
  - the copy-cat soundness of RLHL for all traces (`rlhl_complin`, `rlhl_complin_eihl`);
  - complete-trace meaning (`cc_rel_lin`);
  - handle-linear WLOG (`hlift`);
  - the EIhl frame kit;
  - two SI=∅ counter instances;
  - copy-cat-level relaxation witness (WRCopyCat);
  - universal negatives.
  
  Open in RLHL-3a scope: MINOR documentation residuals (m-30 ranges, m-39, m-41, m-38), carried into RLHL-3b iteration 1.
- **Next:** RLHL-3b (M-19), Counter_xy, as planned by the review. SI choice (a), by location / by counter, is used as a recorded simplification pending the author's decision on m-40.

## 2026-10-14 — loop RLHL-3b — iteration 1 (Writer launched)

- **Task:** M-19, following the review's plan. Counter_xy with E ≠ F:
  - underlay: two-location SC cell (Rd/Faa) with SI_E by location, VE := `EIhl δ_mem`;
  - overlay: {inc_x, inc_y, get_x, get_y} with SI_F by counter, VF := `EI δ_cxy`;
  - instance `cxy_rlhl2` via `method_sound`, with a generic readiness-from-inheritance lemma (`emit_ready_SI`);
  - module-derived complete SB witness, rel_lin under SI_F and ¬rel_lin under ∅;
  - universal negative under SI = ∅;
  - an ns_if premise discharged by stability (two-future variant) or DEFERRED;
  - cheap documentation residuals m-30, m-39, m-41 (and m-38 optional).
- **Recorded simplification:** SI choice (a) (by location / by counter) instead of the paper's RC version, pending the author's decision on m-40. This is stated in the brief and must appear in the file header.
- **Pre-iteration snapshot** for verification: in the scratchpad (`pre3b1.*`).

## 2026-10-14 — loop RLHL-3b — iteration 1 (Writer + verification)

- **Writer:** M-19 FIXED, with item 7 option (a). Plus m-30, m-39, m-41 and the required part of m-38. m-40 and m-37 NEEDS-AUTHOR. B-1, M-22, m-8, M-14 and M-21 DEFERRED.
  - New `models/simlin/RelaxedHoareInherit.v` (802 lines):
    - `emit_ready_SI` (closed, no NNPP);
    - generic renaming theorem `ren_rlhl2` (closed): the renaming copy-cat module has RLHL2Hyps over `EIhl δE` into `EI δF` under spec simulation Hδ, SI inheritance `~~SI_E(ρ o1, ρ o2) → SI_F(o1, o2)`, `lz`, arity injectivity Hinj, and single-future bodies; derived via `method_sound`;
    - `ren_complin_ei`, `ren_rel_lin`.
  - New `examples/Relaxed/RelaxedHoareCounterXY.v` (~1400 lines):
    - `EM` (Rd/Faa on CX, CY; `by_location`), `FC = CxySig by_counter`, `F0 = CxySig (λ_ _. False)`, `δmem`, `δcxy` (Inc returns the old value);
    - `cxy_rlhl2` (closed) and its corollaries `cxy_complin_ei`, `cxy_rel_lin`;
    - `sb_exec` (∀ si; complete; module-derived), `sb_rel_lin`, `sb_rel_lin_direct`, `sb_not_rel_lin0` (closed; ∀ si), `sb_si_decides`;
    - `cxy0_no_rlhl2` (∀ I R G), `cxy_discriminates_rlhl2`;
    - `CounterAsRename.counter_ren_rlhl2`;
    - `CounterXYZ.cxyz_rlhl2` (two-future body with an own Faa z; the genuine own-event premises are discharged by stability), `z_reorder_exec`.
  - `ReadPairUniversal.read_pair_not_complin` (closed). Headers of `RelaxedHoare.v` / `RelaxedHoareGSim.v` (m-30, m-39, m-41).
  - `_CoqProject` +2 entries; Makefile regenerated.
  - The Writer flags as open: a stale WRCopyCat comment ("planned … in RLHL-3b"); the 7a premises are frame facts (z invisible to the overlay); the main instance and `ren_provable` are single-future; choice (a) is more permissive than the paper's RC reading (the paper's inc_x has no overtaking).
- **Verification (orchestrator):**
  - No declaration removed. The 9 removed lines in `RelaxedHoare.v`, `RelaxedHoareGSim.v` and `RelaxedHoareChecks.v` are header text, and the GSim item-10 sentence on the paper's premises is reflowed, not dropped. Other RLHL files are unchanged.
  - Grep in the new files: clean. `make -n` lists only `DCPOs.v`.
  - All 842 lemmas in the 11 RLHL files: 791 closed, 12 `eq_rect_eq`, 26 `classic`, 13 both; nothing outside the baseline.
    - Closed: `emit_ready_SI`, `ren_rlhl2`, `cxy_rlhl2`, `sb_exec`, `sb_not_rel_lin0`, `sb_rel_lin_direct`, `sb_si_decides`, `counter_ren_rlhl2`, `cxyz_rlhl2`, `z_reorder_exec`, `read_pair_not_complin`.
    - `classic`: `cxy_complin_ei`.
    - `eq_rect_eq` + `classic`: `cxy_rel_lin`, `sb_rel_lin`, `cxy0_no_rlhl2`, `cxy_discriminates_rlhl2`, `ren_rel_lin`, `cxyz_rel_lin`.
  - Statements checked with `Print`/`Check`: `EM`, `FC`, `F0`, `δmem`, `δcxy`, `M_cxy`/`M_cxy0` (the same `Mcxy si`), the initial states, `sb_evs`/`sb_trace` (four invocations, the two Rd's emitted before the two Faa's, eight responses; gets and incs all return 0), and `ren_rlhl2`.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-3a iteration-3 review
- BLOCKER: B-1 (unchanged).
- MAJOR: M-19 (ready); m-8, M-22, M-14 and M-21 carried.
- MINOR: m-30 (ranges), m-38, m-39, m-40 (research-level), m-41, m-37 (narrowed), m-36.
- Verdict: close RLHL-3a; proceed to RLHL-3b.

## 2026-10-14 — loop RLHL-3b — iteration 1 (review)

- **Review** (workflow; three lenses, a skeptic per lens, a synthesis; all BLOCKER/MAJOR upheld):
  - BLOCKER B-1 (narrowed): the only verified nonempty-SI object is a one-to-one renaming over an SC cell. New sub-item (4′): a non-renaming object at nonempty SI whose invariant carries value content.
  - MAJOR M-22 (carried; plan sharpened). In order: `mtraces_mono` → module trace-LTS and absorption (idF first) → semantic linking → m-8 on a spec with a precondition → an SB-with-Wait client of Counter_xy. `ren_rlhl2` does not give absorption, but it gives composable test layers.
  - MINOR, new:
    - m-42: stale headers in GSim:101-102, CompLinSpec:141-145, Checks WRCopyCat, and CounterXY difference (1);
    - m-43: R_π mis-mapped to intra-call own events; the paper's R_π is other same-thread independent operations, which Coq supports via `h_guar_rely`;
    - m-44: Hinj and the ¬¬ in Hsi carry no content; the header misstates Hinj;
    - m-45: intra-call own-event interference exercised only as frame facts;
    - m-46: choice (b), the (∅,∅) instance and an LB twin are cheap through `ren_rlhl2`, which decouples the Coq from m-40.
  - Resolved: M-19, m-30, m-38, m-39, m-41.
  - Verdict: "RLHL-3b can close. The documentation minors (m-42, m-43, m-44) are cheap; the orchestrator can check them by diff without another review iteration. m-46 is optional but recommended … Proceed to RLHL-3c. No redesign."
- **Factual check by the orchestrator:** re-ran the review's complete choice-(b) script `cxyb_rlhl2`: Closed. Copy in `.rocq-review/scripts/RLHL3b1_m46_cxyb_rlhl2.v`.
- **Records:**
  - `latest-review.md` overwritten.
  - Concern matrix:
    - row 43: RLHL-3b results; missing list now has the non-renaming object; next action is the RLHL-3c order;
    - row 64: end-to-end instances;
    - row 65: anchors, `cprov_ret` documented;
    - row 66 split into inter-call (🟡), intra-call (🟡 frame-level) and completeness/LB (⚠️);
    - row 67 → ✅ for the inherited-SI class;
    - row 71 residual m-43;
    - row 72 ❌ → ✅ (M-19);
    - row 73 negatives;
    - row 76 → ✅;
    - m-40 row: choice (b) closed, COH re-target option;
    - m-39 row → ✅;
    - Counter_xy row ❌ → 🟡;
    - new rows `ren_rlhl2`, m-42, m-45, m-46;
    - §4 entry for RLHL-3b iteration 1.
- **Next:** RLHL-3b iteration 2, cheap: m-42, m-43, m-44 (docs, plus optional lemmas) and m-46 (choice (b), the (∅,∅) instance, the LB twin). Then RLHL-3c, starting with `mtraces_mono` and absorption for idF. Those do not depend on the escalated m-8 amendment.

## 2026-10-14 — loop RLHL-3b — iteration 2 (Writer + verification)

- **Task:** the MINOR findings m-42, m-43, m-44 and m-46 of the RLHL-3b iteration-1 review.
- **Writer** (4.5 h): all FIXED, including the optional parts.
  - m-42: stale headers in GSim, CompLinSpec, Checks (WRCopyCat and "No load-buffering example") and CounterXY difference (1).
  - m-43: two readings of R_π in `RelaxedHoare.v`/CounterXY; `intro.tex:99`/`:106` mapped.
  - m-44:
    - Inherit header corrected;
    - `ren_inj_of_dec` (closed), `ren_inj_generic` (`eq_rect_eq`);
    - `ren_si_of_stable`/`_of_dec`/`_plain_of_nn` (closed), `ren_si_of_plain` (`classic`);
    - `CounterXYZ.Gz_breaks_KInv` (closed).
  - m-46:
    - choice (b): `si_mb`, `si_cb`, `EMb`, `FCb`, `Mb`; `cxyb_rlhl2` (closed), `cxyb_rel_lin`;
    - the (∅,∅) instance `cxy00_rlhl2` (closed);
    - `sb_exec_gen` over every SI_E containing the two crossings (closed); `sb_exec_gen_loc` reproduces `sb_exec`, which itself is unchanged;
    - `sb_rel_lin_b`;
    - the LB twin: `lb_exec` (module-derived, complete; closed), `lb_si_decides` (rel_lin under by_counter, not under si_cb nor ∅; closed);
    - `cxy_mixed_no_rlhl2` (∀ I R G for SI_E by location and SI_F = si_cb);
    - `lb_not_trace_b`;
    - `cxy_si_table`, the conjunction of three instances and two ∀ I R G negatives.
- **Verification (orchestrator):**
  - Against the pre-iteration snapshot (`pre3b2tree`):
    - with comments stripped, `RelaxedHoare.v`, `RelaxedHoareGSim.v`, `RelaxedHoareCompLinSpec.v` and `RelaxedHoareChecks.v` are code-identical;
    - in `RelaxedHoareInherit.v` and `RelaxedHoareCounterXY.v`, no code span was deleted or replaced (insertions only);
    - the other RLHL files are unchanged.
  - Grep clean. `make -n` lists only `DCPOs.v`.
  - All 901 lemmas in the 11 RLHL files: 841 closed, 13 `eq_rect_eq`, 28 `classic`, 19 both; nothing outside the baseline.
  - The 45 baseline theorems are identical.
  - Statements checked: `si_mb`, `si_cb`, `by_location`, `by_counter`, `lb_trace` (four invocations; incs respond 0, then gets respond 1), `lb_exec`, `lb_si_decides`, `cxy_mixed_no_rlhl2`, `M_mixed = Mcxy si_cb`, `lb_not_trace_b`, `cxy_si_table`, `sb_exec_gen`, `sb_rel_lin_b`, `cxy00_rlhl2`.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-3b iteration-1 review
- BLOCKER: B-1 (narrowed; sub-item (4′) non-renaming object).
- MAJOR: M-22 (plan sharpened).
- MINOR: m-42, m-43, m-44, m-45, m-46.
- Verdict: RLHL-3b can close after the documentation minors; m-46 recommended; proceed to RLHL-3c.

## 2026-10-14 — loop RLHL-3b — iteration 2 (review); RLHL-3b closes after comment residuals

- **Review** (workflow; three lenses, skeptics, synthesis; 2.9 h):
  - BLOCKER B-1 (carried; wording: "every nonempty-SI positive with a rel_lin consequence").
  - MAJOR M-22 (carried).
  - MINOR:
    - m-42 residual (CompLinSpec instance list; `IntervalWindow.v`);
    - m-43 residual: "coarser than R_π" should be "necessarily larger"; :626 is one reading; cite programlogic.tex:308; GSim :345 wording;
    - m-46 residual: four table sentences say more than proved;
    - new m-47 (research-level: what the LB datum supports for implex.tex:3 / relatedwork.tex:32);
    - new m-48: `si_mb` is I_RC restricted to the 2Counter modes, not "ad hoc";
    - new m-49 (optional: free cells, or the characterisation "RLHL2Hyps iff SI_E∘ρ ⊆ SI_F");
    - new m-50 (optional: legacy lens checks are smoke tests);
    - m-40 now purely a paper decision; m-45 carried.
  - m-44 resolved; m-42/m-43/m-46 resolved apart from wording.
  - Verdict: "RLHL-3b can close … Close RLHL-3b once the comment-only residuals (m-42, m-43, m-46, m-48) are checked by diff."
  - Hand derivations, not kernel-checked:
    1. `si_mb` = I_RC on the 2Counter modes;
    2. under {(Get CX, Inc CY)} alone, LB is rel_lin. This bounds `lb_not_rel_lin_gen`'s premises.
- **Records:**
  - `latest-review.md` overwritten.
  - Concern matrix:
    - row 43 (SI-table results);
    - inter-call R_π row ("necessarily larger"; one reading);
    - LB row split from completeness (LB ⚠️ → 🟡 with m-47 caveats; completeness ⚠️);
    - "sound and complete" row; R_π-only-independent row (paper point);
    - m-40 row (both choices in repo; m-48);
    - m-39 locator; `ren_rlhl2` row (side conditions); m-42 row → ✅ with residual; m-46 row → ✅ with residuals;
    - new m-50 row; Counter_xy row;
    - §4 entry for iteration 2.
- **Next:** RLHL-3b iteration 3, comment-only (m-42, m-43, m-46, m-48 wording; m-50 header sentence), with the optional m-49 cells. The orchestrator checks it by diff (code-identical apart from any m-49 additions) and closes RLHL-3b without another review round, as the review advises. Then RLHL-3c from the design panel.

## 2026-10-14 — loop RLHL-3b — iteration 3 (Writer + verification); RLHL-3b closed

- **Writer** (13 min):
  - Comment-only residuals m-42, m-43, m-46 (i)-(iv), m-48 and m-50: FIXED.
  - m-49: new final section of `RelaxedHoareCounterXY.v`:
    - free cells `cxy0cb_rlhl2`, `cxy0cnt_rlhl2`, `cxybcnt_rlhl2` (closed) and `cxyb0_no_rlhl2` (∀ I R G);
    - generic `mgen_rlhl2` (closed);
    - `cxy_si_char : ∀ r c, cxy_cell (siE_of r) (siF_of c) ↔ (∀ o1 o2, siE_of r (ρ o1) (ρ o2) → siF_of c o1 o2)` over the 3×3 family (`eq_rect_eq` + `classic`).
  - The general iff over all relations: DEFERRED. The optional faithful modes on EMb/FCb (m-48): DEFERRED.
- **Verification (orchestrator, by diff, as the review advised):**
  - With comments stripped (string-aware), ten of the eleven RLHL files are code-identical to the pre-iteration snapshot. In `RelaxedHoareCounterXY.v` the old code is an exact prefix, and the new code is inserted only before the final `End`.
  - `make -n` lists only `DCPOs.v`.
  - All 910 lemmas: 848 closed, 13 `eq_rect_eq`, 28 `classic`, 21 both; nothing outside the baseline.
  - The 45 baseline theorems are identical.
  - Statements checked: `cxy_cell`, `siE_of`, `siF_of`, `cxy_si_char`, `cxyb0_no_rlhl2`, `mgen_rlhl2`.
- **No further review round,** per the iteration-2 review ("Close RLHL-3b once the comment-only residuals … are checked by diff").
- **Concern matrix:** m-42 row → ✅; SI table row extended with `cxy_si_char` and the free cells; m-50 row → ✅; inter-call R_π row (m-43 resolved in Coq); §4 entry for iteration 3.
- **RLHL-3b outcome (closed after 3 iterations).**
  - Proved:
    - the generic readiness lemma `emit_ready_SI` and the renaming theorem `ren_rlhl2`;
    - Counter_xy at nonempty SI, with spec meaning (`cxy_rlhl2`, `cxyb_rlhl2`);
    - module-derived complete SB and LB witnesses;
    - the full 3×3 SI characterisation (`cxy_si_char`): overlay SI alone decides provability, and SB vs LB;
    - a two-future variant with genuine own-event premises (frame-level).
  - Open, outside RLHL-3b: B-1 (memory link, client, non-renaming object), M-22 (RLHL-3c), m-45, m-47, m-40 (paper), m-36, m-37, m-8.

## 2026-10-14 — RLHL-3c design panel (no Rocq changes)

- **Workflow:** three read-only Plan agents (operational, trace-theoretic, incremental) and one skeptical `rocq-research-reviewer` synthesis; 8 h.
- **Plan** saved to `.rocq-review/tasks/RLHL-3c.md`; individual designs in `tasks/RLHL-3c-designs/`.
- **Route.** ModLTS composite plus trace-determinedness:
  - `mtraces_mono` and `modlts_paths`: Closed in scratch sessions;
  - generic absorption over `CCClosed` presentations (Design A), proved by a forward simulation into a FreeLTS target and then `exec_transport`;
  - `VerImpl` in copy-cat form (`verimpl_vcomp` Closed in scratch);
  - a modular SB client of Counter_xy;
  - m-8 last.
  
  Absorption (3c.5) is the main risk: about 1200-2000 lines, 3-5 iterations. Fallback if it stalls: the TrLTS + `cc_rel_lin` client route, complete runs only.
- **Sub-tasks:** 3c.1 (Layer) → 3c.4 (`CCClosed`, `ei_ccclosed`) → 3c.5 (absorb) → 3c.6 (Link) → 3c.7 (client part 2). 3c.2 (client spec part) and 3c.3 (`unabsorb`) can run in parallel. 3c.8 (m-8) is blocked on D5. 3c.9 (F-side counterexample) is research.
- **Research-level decisions D1-D8** recorded in research-intent §7 for the author. Work proceeds provisionally with the recommended options; these are additive definitions, and no paper claim is made.
- **Panel finding for the paper (D2):** saturation as printed (App. relaxedlin.tex:53-56) is probably false on the F-side without SI inheritance, and false on the E-side for handle-sensitive underlays.
- **Next:** RLHL-3c.1 and 3c.2 in parallel. Each owns its new file; the orchestrator pre-registers both files in `_CoqProject`.

## 2026-10-14 — loop RLHL-3c — iteration 1 (two Writers launched in parallel)

- **Setup (orchestrator):**
  - Created placeholder files `models/simlin/RelaxedHoareLayer.v`, `models/simlin/RelaxedHoareAbsorb.v` and `examples/Relaxed/RelaxedHoareClientSB.v` (header comment only).
  - Registered them in `_CoqProject` after `RelaxedHoareInherit.v` and after `RelaxedHoareCounterXY.v`; Makefile regenerated; the stubs compile.
  - Snapshot of the RLHL files and the old `_CoqProject` in the scratchpad (`pre3c1*`).
- **Writer A (3c.1 + 3c.3, stretch 3c.4):** Layer (`mtraces_mono` … `modlts_trlts`), then `produced_inv_answered` and `unabsorb`; stretch goal `CCClosed`/`ei_ccclosed`/`absorb_needs_closure`.
- **Writer B (3c.2):** spec-level SB client: `GS`, `Mcl_si`/`Mnw_si`, `mcl_trace`, `ei_sb_cycle`, `sb_client_spec`, `sb_nowait_si_decides`.
- **Constraints:** disjoint file ownership; targeted `make` only; neither Writer edits `_CoqProject`/Makefile; B must not import Layer/Absorb.

## 2026-10-14 — loop RLHL-3c — iteration 1 (Writers + verification)

- **Writer A (3c.1, 3c.3, stretch 3c.4: all done):**
  - `RelaxedHoareLayer.v` (355 lines): `LPaths`, `mtraces_mono`, `mtraces_ext`, `complin_mono_under`/`_over`, `FreeLTS`, `mtraces_free`, `exec_app`, `mod_step`, `ModLTS`, `modlts_paths`, `TrLTS`, `trlts_paths`, `modlts_trlts`, and `hlift_drop_via_mono` (a sanity re-derivation of half of `hlift`).
  - `RelaxedHoareAbsorb.v` (1413 lines): `produced_inv_answered`, `unabsorb` for every VF. The route changed from the plan: `rtraces_of_ccwf` (a CCWF path of V is a copy-cat trace) plus `underlay_ccwf`/`underlay_rtraces` (every module execution's underlay trace is CCWF), then `modlts_paths` and `exec_transport`. Also `complin_unabsorb`, `rehandle`/`is_res`/`ccimg` (with snoc lemmas), `CCClosed`, `ei_ccclosed`, `eihl_ccclosed`, and `absorb_needs_closure` with `vf0_not_ccclosed`. `absorb` itself is PENDING (3c.5).
  - Statements exactly as in the plan.
- **Writer B (3c.2: done):** `RelaxedHoareClientSB.v` (1704 lines):
  - `GS`, `Mcl_si`, `Mnw_si`, `mcl_trace`, `mnw_trace`;
  - generic module facts: `exec_underlay_nodup`, `ucount_*`, `returned_emitted`, `forced_order`;
  - the EI path lemma `ei_sb_cycle`;
  - `SBShape`, `sb_cycle_of_shape`;
  - `sb_client_spec` (exact plan statement), `sb_nowait_si_decides` (exact), `sb_spec_live` (both waiting calls return with (0,1)), `sb_wait_decides`.
  - The (F3) chain inv(inc) → res(inc) → inv(get) is used; (F2) is not, even for same-thread calls. The mixed-SI no-wait case is only argued by hand.
- **Verification (orchestrator):**
  - All pre-existing RLHL files are byte-identical to the pre-iteration snapshot. `_CoqProject` differs only by the orchestrator's three placeholder entries.
  - Grep clean in the three new files. `make -n` lists only `DCPOs.v`.
  - All 1071 lemmas in the 14 RLHL files: 1009 closed, 13 `eq_rect_eq`, 28 `classic`, 21 both. The 161 new ones (Layer 20, Absorb 64, ClientSB 77) are all closed.
  - The 45 baseline theorems are identical.
  - Statements checked: `mtraces_mono`, `modlts_paths`, `modlts_trlts`, `ModLTS`/`mod_step`, `unabsorb`, `underlay_rtraces`, `rtraces_of_ccwf`, `CCWF`, `CCClosed`, `ei_ccclosed`, `absorb_needs_closure`, `sb_client_spec`, `sb_nowait_si_decides`, `sb_spec_live`, `Mcl_si`.

## 2026-10-14 — STOPPED by the author

- The RLHL-3c iteration-1 review workflow (`wf_1af4c861-0b6`) was stopped before it finished. RLHL-3c iteration 1 is therefore verified by the orchestrator only, not reviewed. `latest-review.md` is still the RLHL-3b iteration-2 review.
- Nothing else is running. No commits.

## 2026-10-15 — author decisions; RLHL-latch started

- **Author:** accepted m-8 / D5 (i) (implementation-side error obligation); RLHL LatchSet over COH registers plus barriers first; "do latch set first". Recorded in research-intent §8.
- **Plan:** an RLHL-latch design panel (read-only), then Writers for:
  - error infrastructure;
  - the COH+barrier memory spec;
  - the LatchSet program and RLHL proof;
  - witnesses and negatives for broken variants.
- RLHL-3c 3c.5-3c.7 deferred. The RLHL-3c iteration-1 review is still pending (it was stopped).

## 2026-10-15 — RLHL-latch design panel (no Rocq changes)

- **Workflow:** (A) error infrastructure, (B) LatchSet object and proof, (C) adversarial semantic check; skeptical synthesis. 50 min.
- **Plan** in `.rocq-review/tasks/RLHL-latch.md`; designs in `tasks/RLHL-latch-designs/`.
- **Semantic findings (hand-checked by the synthesizer against `must_precede` and the evaluated `dto` table; not yet mechanized):**
  - The correct LatchSet satisfies the target.
  - All five broken variants fail, each with a concrete complete execution in which print returns `[0]` (legal results are `[]` and `[5]`).
  - I_L is never used: LPs are `Lseq` accesses, so same-location F2 orders them.
  - The trailing `mb` is not needed.
  - Non-overlap in P1 is unnecessary.
  - Module traces cannot be transported across overlay relations by conversion (needs L.8).
  - The underlay is multi-copy atomic, so it does not support ARMv8 claims.
- **Corrections to the reports:**
  - LatchSet does not need `GSimRelErr`/`RLHL2HypsE`, because the underlay has `Error := False`.
  - Report B's "trace reuse by conversion" claim is wrong (repl rejects it).
- **Tasks:** L.1-L.11, about 7.5-11k lines, 14-20 Writer iterations. The reader proof L.5 is the go/no-go checkpoint.
- **RD-1…RD-10** recorded in research-intent §7; proceeding provisionally with the recommendations.
- **Next:** wave 1 in parallel on disjoint files:
  - Writer A: L.1 generic `run` interpreter and `rp_run`, then L.2 the LatchSet program port;
  - Writer B: L.8 resig transport;
  - Writer C: L.10 error trace definitions plus the `m8_gap` negative half.

## 2026-10-15 — author redirects RLHL target: two SeqLocks on COH with LB

- Recorded in research-intent §8. RLHL-latch is paused after wave 1 (still running; its generic parts are reused).
- Next: an RLHL-seqlock design panel (read-only, concurrent with wave 1).

## 2026-10-15 — RLHL-latch wave 1 STOPPED by the author ("stop the latch set first")

- Workflow `wf_e8f78ef1-d22` was stopped mid-run, with no Writer report.
- **State left behind (orchestrator check):**
  - all five files compile; no admits or axioms;
  - 258 lemmas, all within {`eq_rect_eq`, `classic`};
  - `make -n` lists only `DCPOs.v`.
- **Files:**
  - `RelaxedHoareRun.v` (1150 lines; `run`, `rp_run`, `run_method_provable`, `dprec_run`, `GAge` and preservation, `emit_ready_block`, EIhl Done monotonicity);
  - `RelaxedHoareResig.v` (893; `resig`, configuration transport, `mtraces_resig(_iff)`);
  - `RelaxedHoareErrSpec.v` (954; `MTracesE`, `RTracesClosed`, `RCompLinErr`, `Licensed`, `EIe`, `hliftE`, `mtraces_eie_ei`, `complin_err_rel_lin`, `pool_keys_trace`, part of `cc_license_indep` machinery);
  - `RelaxedHoareLatchProg.v` (1018; LatchSet port, partial);
  - `RelaxedHoareLockErr.v` (287; partial).
- These files are unreviewed and their completeness relative to the plan is unverified. They are kept as they are, with nothing deleted. The generic three are candidates for reuse by RLHL-seqlock.
- The RLHL-seqlock design panel (`wf_3099ab09-bbf`, read-only) is still running.

## 2026-10-15 — RLHL-seqlock design panel (no Rocq changes)

- **Workflow:** (A) object/proof, (B) adversarial, (C) reuse; skeptical synthesis. 3 h. Plan in `.rocq-review/tasks/RLHL-seqlock.md`; designs in `tasks/RLHL-seqlock-designs/`.
- **Key finding:** realistic writers (TicketLock, or a writer that reads `seq`) do not exhibit cross-SeqLock LB in this semantics, because `Rmb` orders later read-kind operations.
  - TicketLock SeqLocks are predicted SC (no LB, no SB).
  - A seq-reading writer (WRd) gives SB but not LB.
  - Only a single writer with a blind `inc` (WInc, `inc ↦ DW`) gives LB.
  - MP is forbidden in all variants.
  - The read LP must be prophetic (final `rmb_b` via the ghost; report C's "past-determined" claim is refuted).
- **Orchestrator re-ran the panel's scripts A, B and C:**
  - `emit_ready_mixed`, `lb_cross`, `rmb_blocks_rd`, `rd_retry_prod`, `wr_guard_prod`, `rd_prod`, `wr_prod` and `lb_reorder_prefix` are all closed;
  - copies of A and C are in `.rocq-review/scripts/`.
- research-intent §8: rationale corrected.
- **RS-1 (which writer) is decisive** and is put to the author.

## 2026-10-15 — author decision RS-1 = WRd only; RLHL-seqlock wave 1

- Recorded in research-intent §8; addendum appended to `tasks/RLHL-seqlock.md`.
- Placeholders `RelaxedHoareReady.v` and `RelaxedHoareSL2Prog.v` registered; snapshot `presltree`.
- Wave 1: Writer A does .0 (Run/Resig headers) and .1 (Ready); Writer B does .2 (SL2Prog, WRd).

## 2026-10-15 — author requirement: use RLHL in full

- Route L only (MethodProvable derivations via `run_method_provable`/`rp_run`); route S excluded; checkpoint escalates to the author. Recorded in research-intent §8 and the plan (Addendum 2). The running wave 1 (.0/.1/.2) is unaffected.

## 2026-10-15 — loop RLHL-seqlock — wave 1 (Writers + verification)

- **Writer A:**
  - .0: Run.v gets a 157-line K/S/P/R header; Resig.v gets a provenance and plan-check paragraph. Code unchanged. All L.1/L.8 plan items are present, including the smoke tests `ren_run_provable`/`RunCounter` and `CounterXYResig`.
  - .1: new `RelaxedHoareReady.v` (607 lines): `emit_ready_mixed`, `emit_ready_block_older_of_mixed`, `emit_ready_si_older`, `RecNB` (establish plus stability per transition), `emit_ready_rec` (three-way readiness), `OlderSub`, `GMove`, `GMovesIn`, `ghost_never_readded`, `gmove_recnb`, `gage_gmoves`.
- **Writer B (.2):** new `RelaxedHoareSL2Prog.v` (1137 lines):
  - underlay `E_S` and `δS`, with `sindep_coh` = I_COH;
  - overlay `F2 si`, `slsi`, `slRA`, `δF`;
  - the WRd writer and the reader via `run`; `M2`, `M2w`, `P1`, `mtraces_guard`/`_unguard`;
  - blocking facts `rmb_blocks_rd`, `lb_blocking`, `sb_blocking`;
  - productions `rd_prod`, `rd_retry_prod` (24 events, exact), `wr_guard_prod`, `wr_guard_none`;
  - non-vacuity `sl2_write_read_mtraces`, `sl2_read_overtakes_write` (single-thread, not discriminating);
  - targets `sl2rd_target` / `sl2rd_relin_target` as definitions only.
- **Verification (orchestrator):**
  - Against snapshot `presltree`: Run/Resig code-identical (comments only); Ready and SL2Prog new; all other RLHL files byte-identical. `_CoqProject` has only my two entries.
  - Grep clean. A full `make` leaves only `DCPOs.v` failing; LatchProg rebuilt OK after Run.vo changed.
  - `Print Assumptions` over Run/Resig/Ready/SL2Prog (244): Ready 45 and SL2Prog 55 closed; Run 73 closed + 1 classic; Resig 66 closed + 4 {eq_rect_eq, classic}.
  - The 45 baseline theorems are identical.
- **Open question raised by Writer B:** whether the target holds for every `si ⊇ slRA`. The orchestrator's reading of `lb_blocking`/`sb_blocking`: only (older write_i, younger read_j) LPs can be reordered, and a larger `si` only eases `invocation_ready`. So `si ⊇ slRA` is expected; this goes to task .4 as a design point, not an author decision.
- **Next:** independent review of wave 1 (Run, Resig, Ready, SL2Prog) in parallel with wave 2 (.3 SL2Exec, .4 SL2Inv). The wave-2 files are new and do not modify the reviewed files.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-3b iteration-2 review
- BLOCKER: B-1. MAJOR: M-22.
- MINOR: m-42, m-43, m-46, m-47, m-48, m-49, m-50, m-40, m-45.
- Verdict: close RLHL-3b after comment residuals (done in RLHL-3b iteration 3).
- Note: the RLHL-3c iteration-1 review was stopped before completion, so no RLHL-3c review exists.

## 2026-10-15 — loop RLHL-seqlock — wave 1 (review)

- **Review** (workflow; three lenses, skeptics, synthesis):
  - **MAJOR:**
    - B-1 (carried, rated MAJOR this wave: the intro.tex:105-106 anchor was rewritten in the working tree);
    - **M-23** (new, research-level): the WRd writer's closing write reuses the cached `v` instead of reloading `seq`. The SB datum and the need for `slRA` depend on this elision. With the Linux-literal reloading writer the object is SC on this underlay (no store forwarding). Author options: (a) keep and describe honestly; (b) model the reload and verify at ∅; (c) move SB to a store-forwarding underlay (m-37);
    - **M-24** (new, actionable): the plan §2.4 read-value assertion is not stable (counterexample state given); fix in .4 before .5.
  - **MINOR:** m-51 (state the target with route-L premises, `rlhl_sound_complin`-style), m-52 (Ready persistence dual; `ghost_emit_keeps_other`), m-53 (retry-loop readiness under `rp_run`: pilot, `before_run`, `div_method_provable`, longer `complete_tac`, move `lb2_not_trace_rd` to .7), m-54 (comment precision), m-55 (overlapping and retrying executions), m-56 (undocumented modelling choices), m-33 (extended), m-57 (`models/` importing `examples/`).
  - **Confirmed:**
    - `rp_run`/`run_method_provable` are genuine derived RLHL rules (`RProvable_coind` with `rp_futureD`/`rp_wait_pending` premises, full `NewSlotOK` including `ns_if_*`), so route L counts as "RLHL in full";
    - Resig transport faithful; `sindep_coh` = I_COH; `slRA` = LRA shape; `lb_blocking`/`sb_blocking` correct;
    - `si ⊇ slRA` suffices with no upper bound (overlay SI read only positively).
  - Verdict: "Continue to wave 2; no redesign is needed", but M-23 needs the author's reconfirmation and M-24 must be fixed in .4.
- **Wave 2 (.3 Exec, .4 Inv)** was launched before this review finished. Its Writers do not know M-23/M-24; their output will be checked against them.
- M-23 is put to the author.

## 2026-10-15 — author decision on M-23: keep the cached v (option (a)); recorded in research-intent §8

## 2026-10-15 — loop RLHL-seqlock — wave 2 (Writers + verification)

- **Writer A (.3, `RelaxedHoareSL2Exec.v`, 1038 lines): GO.**
  - `sb2_exec_rd`: a complete module-derived SB execution, both reads (0,0); also in the `_ij` form.
  - `sb2_rel_lin_slRA`, `sb2_not_rel_lin0`, `sl2rd_no_rlhl2_gen`.
  - `sl2rd_no_rlhl2_empty`: extra hypothesis `∃ i j, tw i ≠ tw j` (two writer threads needed for SB).
  - `lb2_not_rel_lin`, `lb2_rel_lin_slsi`, `mp2_not_rel_lin` (stronger: no `complete` premise).
  - `lb2_not_trace_rd_of_rel_lin`: conditional on .7.
  - Negatives only via `rlhl_complin_eihl` and `cc_rel_lin`.
- **Writer B (.4, `RelaxedHoareSL2Inv.v`, 1916 lines):**
  - frozen `Isl`/`Rsl`/`Gsl`/`Osl`/`Qsl`;
  - all `RLHL2Hyps` fields except `h_sem`; `mp_PI`, `mp_ret`, `ready_read`, `ready_write`; the stability kit; per-event maintenance; run entry points;
  - the `div` case closed;
  - `sl2rd_rlhl2_of_provable`/`_of_methods`, and `sl2rd_target_of_methods` (∀ si ⊇ slRA).
- **NEEDS-AUTHOR (Writer B, argued, not mechanized):** the reader as written (untagged) has no `MethodProvable` derivation for any I R G. This agrees with review M-24. Reason:
  - the read's values come from untagged responses that can be emitted after the LP;
  - the proof state forgets consumed record values and does not record which call owns an emitted underlay key, so the rely admits steps consuming the reader's own record;
  - value facts are usable only in the response's own precondition.
  
  Options: (a) tag `rmb_a` on the `rd Sq_i` response and `rmb_b` on the `rd Sx`/`rd Sy` responses (a program change; hand-checked sufficient); (b) extend the proof state or presentation with response ownership or value history; (c) route S (excluded by the author).
- **Verification (orchestrator):**
  - only the two new files changed relative to `presl2tree`; grep clean; `make -n` leaves only `DCPOs.v`;
  - 166 lemmas: Inv 125 closed, Exec 39 closed + 2 {eq_rect_eq, classic};
  - statements of `sb2_exec_rd`, `sb2_not_rel_lin0`, `sl2rd_no_rlhl2_empty` and `sb2_trace_ij` checked.
- The reader blocker is put to the author.

## 2026-10-15 — author: evaluate first, then decide (reader blocker)

- A read-only design evaluation is running (`wf_a84b7a71-b23`):
  - (A) tag the reader barriers;
  - (B) value-history / response-ownership extension;
  - (C) adjudicate whether the untagged reader is derivable with the current logic.
- No Writer runs meanwhile; .5/.6 wait for the decision. The writer derivation (.6) is not blocked, but it is held so that the frozen definitions stay stable until the decision.

## 2026-10-15 — SeqLock reader blocker: design evaluation (no Rocq changes)

- **Workflow:** (A) tags, (B) state/presentation extension, (C) adjudication; skeptical synthesis. 67 min. Report in `tasks/RLHL-seqlock-reader-eval.md`; evaluations in `tasks/RLHL-seqlock-reader-eval/`.
- **Findings:**
  - **Untagged reader over EIhl** with the frozen definitions: not derivable (rigorous argument; key lemmas closed). "For every I R G": argued only. The cause is the lossy `EIhl` presentation (consumed values forgotten), not the paper's rules, whose proof state carries the underlay trace (programlogic.tex:537).
  - **M-24's repair (i)-(iv) refuted** (`m24_not_stable`, closed); M-24 is superseded by M-25 (research-level).
  - **New BLOCKER B-6:** the frozen read postcondition `Qsl` cannot be reached at `Close` on paths whose iteration count disagrees with the ghost; this affects every option. Fix: `Qrd := Qsl ∨ ¬NoOwn`, and per-operation postconditions in the assembly lemmas. Optionally, at logic level, give `bw_sum` `NoOwn`.
  - **Option B:** `EIhlv := Log (EIhl δ)`, a history presentation with an MTraces equivalence (`loglift`, closed) and `rlhl_complin_eihlv` (classic). It keeps the program and the logic unchanged, gives `RCompLin` for every prefix, and the reader derivation is hand-checked sufficient.
  - **Option A (tags):** violates the dependency-only principle (research-intent:129) and is outside the impl.tex:120 policy. It transfers to the untagged program for complete traces only, and only via an unmechanized insensitivity theorem.
  - **Recommendation: B.**
- **Orchestrator re-ran the scripts:**
  - B §7: 9 closed + `rlhl_complin_eihlv` classic;
  - C §7: `fam_merge`, `doom_vacuous_after_consumption`, `m24_not_stable` closed;
  - B-6 script: 4 closed.
  
  Copies in `.rocq-review/scripts/RLHLsl_reader*.v`.
- The (A)/(B) decision is put to the author.

## 2026-10-15 — author decision: option B (history presentation); wave 3 launched

- research-intent §8 updated; plan Addendum 3.
- Placeholder `RelaxedHoareLog.v` registered; snapshot `presl3tree`.
- Wave 3: Writer A .L (`RelaxedHoareLog.v`); Writer B .B6 (SL2Inv additions, m-58, Ready m-52).

## 2026-10-15 — loop RLHL-seqlock — wave 3 (Writers + verification)

- **Writer A (.L, `RelaxedHoareLog.v`, 1244 lines):**
  - **Port:** `Log`, `loglift` (MTraces equivalence), `log_handle_linear`, `complin_log_under`, `EIhlv`, `rlhl_complin_eihlv`, the `logval`/`logok` lemmas, `logval_unique` (replacing the SeqLock-specific `sl_logval_rd`).
  - **m-59:** `liftGL` (base relation plus `log_steps`) and `evupdate_liftL`.
  - **Side-field transfer:** `guar_rely_lift`, `invoke_rely_lift`, `return_rely_lift`, `ok_lift`, `init_lift`, `postinvoke_lift`, `retcond_lift`, `methodsem_lift`, `rlhl2_lift`, `rlhl2_lift_of_provable`.
  - **Part 5:** `methodprovable_lift` (every derivation over VE lifts to `Log VE`).
  - **Corollaries:** `rlhl2_eihlv_of_provable`, `rlhl_sound_complin_eihlv`, `rlhl_sound_rel_lin_eihlv`.
  - **Smoke test** `RunCounterLog`: a transferred and a direct derivation over EIhlv; `counter_log_complin`/`_rel_lin`.
- **Writer B (.B6, m-58, m-52):**
  - SL2Inv Part 9: `Qrd`, `Qop`, `qrd_ret`, `qop_ret`, `owns_rmb_not_qsl`, the `_rd` versions of the read, assembly and target lemmas; `sl2rd_prov_target` (m-51 shape) with `sl2rd_prov_target_imp`. The old declarations are marked superseded.
  - SL2Inv OPEN section rewritten (m-58).
  - Ready Part 5: `ghost_emit_keeps_other`, `OwnKeep` closure, `GMoveBy`, `GMovesOther`, `owned_persists`, `retcond_or_owned`.
- **Verification (orchestrator):**
  - Against `presl3tree`, with comments stripped: SL2Inv/Ready/Log have insertions only (0 deleted or replaced code spans); other files unchanged.
  - Full `make`: only `DCPOs.v` fails. Grep clean.
  - `Print Assumptions` over Ready/Log/SL2Inv/SL2Exec (329): Ready 71 closed; Log 71 closed + 3 classic + 3 {classic, eq_rect_eq}; SL2Inv 140 closed; SL2Exec 39 closed + 2 {classic, eq_rect_eq}.
  - The 45 baseline theorems are identical.
- **Next, in parallel:**
  - review of waves 2 and 3;
  - wave 4: .6 writer derivation over EIhl (lifted later) in `RelaxedHoareSL2Write.v`, and .4v lifted kit over EIhlv in `RelaxedHoareSL2InvLog.v`.

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-seqlock wave-1 review
- MAJOR: B-1 (carried), M-23 (cached-v writer fidelity; author chose to keep it, honestly labelled), M-24 (superseded by M-25).
- MINOR: m-51…m-57, m-33.
- Verdict: continue, no redesign.

## 2026-10-15 — loop RLHL-seqlock — waves 2-3 (review)

- **Review** (workflow; three lenses, skeptics, synthesis). No BLOCKER.
  - **MAJOR:**
    - B-1 (carried);
    - M-23 (carried): the author-mandated "cached v" relabel is not yet applied (SL2Prog.v:4/:453, the SL2Exec header, research-intent RS-1 entry, plan :210); the SB datum must say it depends on the cached-v encoding (SB without own reads);
    - M-25 (supersedes M-24): the reader is not derived; option B plausible by hand; .5 is the go/no-go.
  - **MINOR:**
    - m-60: the ∅ negative's `∃ i j, tw i ≠ tw j` is unnecessary. The single-writer witness `sw_*` (lens scratch, re-run closed) proves it for every tw and gives per-pair necessity of slRA.
    - m-61: stale trace.tex anchors (I_RA is now :96, store forwarding :94-107); SL2Inv :157 wording; Log :40-47 should say "restores the underlay projection of the paper's s"; SL2Prog :1117 si question answered.
    - m-62: negatives over EIhl vs positive over EIhlv; state them at RCompLin level and derive both RLHL2Hyps negatives.
    - m-63: the reader route is hand-sketched only, with six obligations (B-6 path, tight per-slot guarantees, `ns_if_old_in`/`bw_if` stability, phantom paths and NoOwn, consistent keys, `sl_logval_rd`); a looping validate-after-read pilot over EIhlv is recommended before .5.
    - m-64: delta-table rows for `rp_run`, Log/EIhlv, the `Qrd` ¬NoOwn postcondition, and the ghost-prophetic LP.
    - m-51 (EIhl target not citable; .4v provides the EIhlv one), m-53 (`before_run`, generic `div_method_provable`), m-55 (retry execution missing), m-54/m-56/m-57 (carried), m-33 (narrowed: impl.tex:172/:141 support commit-at-invocation; relaxedlin.tex:628 to qualify).
  - **Closed:** B-6 (interface), M-24, M-26, m-52, m-58, m-59 (half).
  - **Confirmed:** `sb2_exec_rd` is genuine and complete; the legality cycles are correct; the invariant and side fields are correct; `loglift` is exact; `liftGL` is right; `methodprovable_lift` and `rlhl2_eihlv_of_provable` are sound; an EIhlv target assembles today (lens scratch).
  - Verdict: "Continue to .4v/.6 and the .5 checkpoint; no redesign."
- **Records:** `latest-review.md` overwritten. research-intent RS-1 entry annotated per M-23 (below).
- **Next** (after wave 4 is verified):
  - a cleanup Writer: M-23 relabel in the `.v` headers, m-60 `sw_*`, m-61, m-62, m-64, m-55 retry execution, m-54/56/57;
  - in parallel, a reader pilot plus .5 with the m-63 obligations in its brief.

## 2026-10-15 — loop RLHL-seqlock — wave 4 (Writers + verification)

- **Writer A (.6, `RelaxedHoareSL2Write.v`, 1316 lines):**
  - `write_provable`: a closed syntactic RLHL derivation of the writer over EIhl, via `sl2_write_run_provable` → `run_method_provable` → `rp_run` → `RProvable_coind`;
  - `write_provable_v` (lifted by `methodprovable_lift`), `write_other_provable_v`, `write_fits_eihlv`, `rlhl2_v_of_reads` (a fit check);
  - the header lists the genuine own-interference premises (data writes in both directions, floating responses) and five awkward points of `RunCallOK`/`NewSlotOK`.
- **Writer B (.4v, `RelaxedHoareSL2InvLog.v`, 1407 lines):**
  - `IslV`/`RslV`/`GslV`/`QrdV`; side fields transferred;
  - `SL2ReadV` (premise (a): the read over EIhlv with `QrdV ∧ X`), `SL2WriteB` (premise (b): the write over EIhl);
  - `sl2rd_prov_target_v`, `sl2rd_v_of_methods(_v)`, `sl2rd_complin_target` (RCompLin over plain `EI δS`, every prefix), `sl2rd_relin_target`;
  - the reader value kit (`KRd`, `EdgeG`/`EdgeD`/`Pkg`/`PkgT`, `GslFix`/`GslRes`, `KHas`, the stability lemmas, the per-event updates for G/A/X/Y/B/T/responses, `sl_read_close_rd`);
  - gaps G1-G6 in the eval1 sketch identified and handled in the kit.
- **Verification (orchestrator):**
  - only the two new files changed; grep clean (the only hit is a header sentence); `make -n` leaves only `DCPOs.v`;
  - 177 lemmas: Write 61 closed; InvLog 112 closed + 2 classic + 2 {classic, eq_rect_eq} (inherited);
  - `write_provable` type-checks as `SL2WriteB` (premise (b) discharged).
  
  **Only `SL2ReadV` (.5) remains for the main theorem.**
- **Next, wave 5:**
  - Writer A: .5 reader (`RelaxedHoareSL2Read.v`), the checkpoint;
  - Writer B: SL2Exec-only cleanup (M-23 disclosure in its header, m-60 `sw_*`, m-62 RCompLin-level negatives, m-55 retry execution, m-61 anchors).
  
  The header edits upstream of the reader (SL2Prog, RelaxedHoare.v, SL2Inv, Log) are deferred until after .5 to avoid rebuild races.

## 2026-10-15 — loop RLHL-seqlock — wave 5 (Writers + verification): CHECKPOINT .5 PASSED; main theorem proved

- **Writer A (.5 + .7, `RelaxedHoareSL2Read.v`, 1542 lines, under budget):**
  - `read_provable_v : ∀ rc si tw, slRA ⊆ si → SL2ReadV rc si tw` (closed). It is a syntactic RLHL derivation of the untagged retrying reader over EIhlv via `sl2_read_run_provable_v` → `run_method_provable` → `rp_run`, using the SL2InvLog kit (G1-G6); `rnew` gives every `NewSlotOK` for all 12 slot positions of every iteration.
  - `sl2_main : sl2rd_prov_target_v` (closed).
  - `sl2_complin : sl2rd_complin_target` (RCompLin over plain `EI δS`, every prefix; classic).
  - `sl2_rel_lin : sl2rd_relin_target` (complete traces; classic + eq_rect_eq).
  - `lb2_not_trace_rd` (unconditional; classic + eq_rect_eq).
  - m-63 handled: phantom-path NoOwn not needed (Close needs only `Pkg`/`PkgT` ∨ owns rmb).
- **Writer B (SL2Exec cleanup):**
  - M-23 disclosure in the header and comments;
  - m-60: `sw_*` single-writer witness and `sl2rd_no_rlhl2_empty_any` (∅ negative for every tw);
  - m-62: RCompLin-level negatives with EIhl and EIhlv corollaries;
  - m-55: retry execution with rel_lin at slRA;
  - m-61 anchors.
  - The lens-1 `sw_*` script was not in `latest-review.md`; the Writer wrote its own.
- **Verification (orchestrator):**
  - Only SL2Read (new) and SL2Exec changed; SL2Exec has 0 deleted or replaced code spans.
  - Grep clean (header sentences only). Full `make`: only `DCPOs.v` fails.
  - 142 lemmas: SL2Read 71 closed + 1 classic + 2 {classic, eq_rect_eq}; SL2Exec 59 closed + 9 {classic, eq_rect_eq}.
  - Statements checked: `read_provable_v`, `sl2_main`, `sl2_complin`, `sl2_rel_lin`, `sl2rd_relin_target`, `lb2_not_trace_rd`.
  - **Chain confirmed in source:** `sl2rd_v_of_methods` → `rlhl2_eihlv_of_provable` → `rlhl2_lift_of_provable` → `RelaxedHoareGSim.rlhl2_of_provable` → `method_sound` on the MethodProvable derivations. No route S and no `ren_rlhl2`.
  - The 45 baseline theorems are identical.
- **Next:** a comment-only docs pass on the stale headers (SL2Prog M-23/m-54/m-56/Part 8; RelaxedHoare.v m-64 rows; SL2Inv; Log; Run; SL2InvLog; SL2Write; SL2Exec), then a final review of the SeqLock development.

## 2026-10-15 — RLHL-seqlock docs pass (comment-only)

- **Writer:** comment and header edits in SL2Prog (M-23, m-54, m-56, Part 8, m-61), RelaxedHoare.v (m-64 delta rows), SL2Inv, Log, Run, SL2InvLog, SL2Write and SL2Exec.
  - Scratch-checked claims: `rc` is vacuous; `sl2_read_overtakes_write` is rel_lin at ∅; `rlhl2_v_of_reads` is discharged by `read_provable_v`.
  - Notes that programlogic.tex line numbers refer to async-ccal commit 01484091 (the working tree is shifted by 42 lines from :466).
- **Verification (orchestrator):**
  - comment-stripped comparison against `predocstree`: all 8 edited files are comment-only;
  - `make -n` leaves only `DCPOs.v`;
  - the 45 baseline theorems are identical; the main statements re-checked.
- **Next:** final review of the SeqLock development (waves 4-5 and docs).

### Superseded review (archived summary before overwriting `latest-review.md`): RLHL-seqlock waves 2-3 review
- MAJOR: B-1, M-23, M-25.
- MINOR: m-60…m-64, m-51, m-53, m-55, m-54/56/57, m-33.
- Verdict: continue; no redesign.

## 2026-10-15 — loop RLHL-seqlock — FINAL review; task closed

- **Review** (workflow; three lenses, skeptics, synthesis). No BLOCKER. "The RLHL-seqlock Coq task can be closed."
  - **Confirmed:**
    - "RLHL used in full" is true: `read_provable_v` and `write_provable` are syntactic derivations (`run_method_provable` → `rp_run` → `RProvable_coind`); every `RunStepOK` is discharged; `rnew` builds every `NewSlotOK` (each `ns_if_*` is a stability fact or refuted by order); `rclose` gives a genuine `BarrierWith`; `h_sem` only via `method_sound`; no MethodSem/route S/`ren_rlhl2` in SL2Read/Write/InvLog/Inv (grep: comments only).
    - The final statements concern the original untagged `M2w` over plain `EI δS`, with no hidden hypotheses.
    - The reader argument is sound (LP via the ghost; `pkgT_vals` and `logval_unique` at Close; the B-6 disjunct refuted by NoOwn; any number of iterations).
    - The witnesses and negatives are genuine; `sl2rd_no_complin_pair` is tight per pair.
  - **MAJOR:**
    - B-1 (carried: the SeqLock provides only the object link).
    - **M-28** (research-level): what B:215 may claim. The verified model (COH registers plus ordering-only Wmb/Rmb) and the mechanized logic do not exist in the paper. Before any citation, authors must address (a)-(i): define COH+rmb/wmb in trace.tex (MCA); state RCompLin all prefixes plus rel_lin complete, at slRA; name the writer honestly; state P1; qualify relaxedlin.tex:520/:628; present the mechanized RLHL; tags (m-54); mention M-22; decide RS-6. Citing without (a)-(c) and (f) is a BLOCKER.
    - **M-29** (research-level plus actionable): the verified slRA contract is MCA-specific. The SB-with-own-reads outcome that store forwarding produces (x86-TSO, ARMv8) is not rel_lin under any si ⊆ slRA (`sbo_not_rel_lin`, closed). Citing the SeqLock as evidence about TSO/ARMv8/oMCA/forwarding is a BLOCKER; the "Scope = oMCA" decision must be reconciled with RD-8.
  - **MINOR:** M-23 (records residue only), m-54 (tag-monotonicity), m-65 (prophecy wording: the committed iterations prophesy the call's own validation outcome), m-66 (SL2Read/Write P paragraphs vs M-21), m-67 (programlogic.tex numbering: HEAD 4a2db8e1, EStep now :579), m-68 (scratch-only facts → lemmas), m-69 (`sl2_no_mp`, `sl2_complin_unguarded` corollaries), m-70 (one N-instance object, shared barriers).
- **Orchestrator re-ran:** `sbo_not_rel_lin` (closed), `sl2_no_mp` and `sl2_complin_unguarded` (baseline axioms), rc vacuity (Goal passes). Copies in `.rocq-review/scripts/RLHLsl_final_*.v`.
- **Records:** `latest-review.md` overwritten; research-intent M-23 residue annotated; concern-matrix SeqLock rows updated.
- **RLHL-seqlock outcome.** Closed in the Coq. Proved:
  - `sl2_main` (closed);
  - `sl2_complin` (RCompLin for every prefix, classic);
  - `sl2_rel_lin` (complete traces);
  - `lb2_not_trace_rd`;
  - SB witness, the ∅ negative for every tw, per-pair tightness.
  
  Open: M-28 and M-29 (authors), the actionable minors (cleanup pass), B-1.

## 2026-10-15 — RLHL-seqlock final cleanup (Writer + verification); RLHL-seqlock CLOSED

- **Writer** (all actionable items of the final review; m-54 left optional):
  - **M-29:** `sbo_not_rel_lin` and `sbo_complete` in SL2Exec; `sbo_not_trace_rd` (every si) in SL2Read; MCA-only sentences in SL2Prog, SL2Read and SL2Exec.
  - **m-68:** `sindep_rc_vacuous` (SL2Prog); `ov_exec`, `ov_rel_lin`, `ov_rel_lin_empty` (SL2Exec); `rlhl2_v_of_reads_inst` (SL2Read).
  - **m-69:** `sl2_complin_unguarded`, `sl2_rel_lin_unguarded`, and `sl2_no_mp` (every si, via resig).
  - **Wording:** m-65 (prophecy, RelaxedHoare.v/Log.v); m-66 (SL2Read/Write/Inv P paragraphs: the mechanized RLHL, printed rules differ); m-67 (programlogic.tex anchors renumbered to async-ccal 4a2db8e1, commit named); m-70 (one N-instance object, shared barriers).
- **Verification (orchestrator):**
  - Against `precleantree`, with comments stripped: SL2Exec/SL2Prog/SL2Read have additions only (0 deleted or replaced code spans); CounterXY, SL2Inv, SL2InvLog, SL2Write, RelaxedHoare.v, Dag, GSim and Log are comment-only.
  - Grep clean. `make -n` leaves only `DCPOs.v`.
  - **All 2005 lemmas in the 27 RelaxedHoare* files:** 1908 closed, 39 classic, 13 eq_rect_eq, 45 both; nothing outside the baseline.
  - The 45 baseline theorems are identical.
- **RLHL-seqlock is CLOSED in the Coq.** Remaining items are for the authors:
  - **M-28:** define COH+rmb/wmb (MCA) in trace.tex; state RCompLin for every prefix plus rel_lin on complete traces, at slRA; the honest writer name; P1 (`sl2_complin_unguarded`); qualify relaxedlin.tex:520/:628; present the mechanized RLHL; tags (m-54); M-22; RS-6.
  - **M-29:** the SeqLock is an MCA-only data point; reconcile "Scope = oMCA" with RD-8.
  - B-1 remains.
