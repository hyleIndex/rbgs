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

## 2026-10-13 — /rocq-loop SL — session baseline (Step 0; no Rocq changes)

- **HEAD:** `6e2b575` (relaxed-lin), working tree clean.
- **Toolchain deviation (author decision, 2026-10-13):** no Rocq 9.2.0 on the author's machine. Homebrew had 9.1.0, which cannot build coqrel `4e450c9` ("Upgrade to Rocq 9.2"; uses the 9.2 `Abbreviation` command). The author chose `brew upgrade rocq` → **Rocq 9.3.0** (OCaml 5.5.1) over a pinned opam 9.2.0 switch. All results in this session are checked with 9.3.0, not the pinned 9.2.0.
  - PATH pitfall: the shell profile puts opam `coq-8.15.2/bin` before `/opt/homebrew/bin`, so bare `coqc`/`coq_makefile` are Coq 8.15.2. The generated Makefile calls `rocq` (Homebrew), so `make` is safe; Makefile regeneration must use `rocq makefile` or `PATH=/opt/homebrew/bin:$PATH`.
- **Build (9.3.0, `make -k -j10`):** 170/171. The only failure is `structures/DCPOs.v:488`: `is` is a reserved word in Rocq 9.3 (`Record r := { is : nat }.` is a syntax error under 9.3.0), not a proof failure. No other file depends on it. Left unchanged (out of scope for SL).
- **Admits/axioms grep:** no `Admitted`/`admit` (two prose hits in comments); `Axiom` only as Module Type fields in `interfaces/`; top-level `Parameter`s are the known ones.
- **Print Assumptions:** all 45 tracked theorems of concern-matrix §4 match the recorded baseline (21 closed; the rest ⊆ {`eq_rect_eq`, `classic`, `Parameter A` in ExchangerTSO/TryStackTSO/EBStackTSO}).

## 2026-10-13 — archive of `latest-review.md` (iteration 0 baseline) before its first overwrite

`latest-review.md` is overwritten by the SL-client iteration-1 review. The repository-wide baseline findings it held (orchestrator audit, not `rocq-research-reviewer`) were, in full:
- **BLOCKER** B-1 RLHL judgement existential, no link to `rel_lin`/`GSimRel` (research-level Q1, then actionable); B-2 no object/client verified through RLHL/VLHL, §6.3 inaccurate; B-3 `memory/` not connected to any object underlay; B-4 paper prints statements Coq refutes or does not support (Thm I.11, Def. I.1, Def. 5.8, SeqLock signature, `rem:ra-tso`, IRIW remark, COH/RA equivalence, HW queue, handles).
- **MAJOR** M-1 complete traces only; M-2 no general composition theorems in `models/`; M-3 weak non-vacuity witnesses (`VE0`, one op); M-4 RC11/ARMv8 correspondence partial and one-directional; M-5 OOTA claim unmechanized, dependency tags trusted; M-6 Counter_xy and weak HW queue not mechanized; M-7 client verification thin (no SeqLock a=b client); M-8 "advantage over prior models" rests on memory-level facts; M-9 one possibility per execution, completeness unavailable.
- **MINOR** m-1 `Parameter A`; m-2 `rocqchk` crash, `vm_compute` trusted; m-3 uncommitted files (since committed); m-4 stale notes; m-5 dead/duplicated code; m-6 `.claude/` git-ignored; m-7 unused `rocq-iris` dependency.
Findings outside a loop's scope stay open with these IDs; the full text is in git (`git show 6e2b575:.rocq-review/latest-review.md`).

## 2026-10-13 — loop SL-client — iteration 1

- **HEAD before/after:** `6e2b575` → uncommitted (new `examples/Relaxed/SeqLockClients.v`, `_CoqProject` +1 line).
- **Task:** module-level SeqLock ⊎ COH[z] clients (a=b of response B4, MP forbidden) derived from `seqlock_module_rel_lin(_K)`; concerns Meta-3, B4, Reviewer B :214/:257–259/:312–317, baseline M-7.
- **Writer:** `SeqLockClients.v` (23 results): `seqlock_client_equal_pairs(_K)` (response-event form), `seqlock_client_mp_forbidden(_K)` (invocation order only, overlap allowed, both `rc`), spec/witness lemmas (`nu_sl_diag`, `nuF_all_diag`, `mp_no_witness`, sanity `nu_sl_nondiag`, `mp_witness_zr_sees_1`), category facts (`fcat_cross_table`, the two dependent and two independent pairs), and generic module facts (`over_res_unique`, `over_res_invoked`). Semantic/assumption changes: none (no existing definition touched; hypotheses = module theorem + client shape).
- **Verification (orchestrator):** independent `rocq compile` of the new file to a scratch path OK; `make -k -j10` 171/172 (only `DCPOs.v`, the 9.3 keyword issue); declaration diff on tracked `.v` empty; no forbidden constructs (two `Context` lines are section parameters, not hypotheses); Print Assumptions: all 23 new results closed; the 45 key theorems identical to the session baseline.
- **Review (rocq-research-reviewer):** BLOCKER 0 new (B-1/B-2/B-3/B-4 persist, out of scope); MAJOR 4 (M-3 non-vacuity, M-1 complete only, M-7 reduced, M-10 new: client = trace predicate, no refinement theorem); MINOR 4 (m-8 header, m-9 misplaced generic lemmas, m-10 report citations off by two, m-2 9.2.0/vm_compute/rocqchk). Verdict: no redesign; "stop SL-client, continue with SL-nonvac" after the m-8 fix.
- **Disputes and resolution:** none disputed. Reviewer rejected the Writer's "overlay I = ∅ → FIXED" (I is nonempty but unused by both proofs); M-7 stays open, reduced.
- **Orchestrator decision (target widened openly):** the review lists "a reusable client rule (the MP witness-order principle and the same-epoch theorem)" as *required* for M-7, and overview.tex:276 prints the same-epoch property with no Coq theorem. Iteration 2 therefore adds (i) m-8, (ii) a same-epoch theorem, (iii) MP as a witness-order rule, (iv) optionally a real-time `rhb` corollary, keeping the reviewed statements unchanged. This widens the prepared brief `tasks/SL-client.md`; recorded here.
- **Routed elsewhere:** M-3 → SL-nonvac, whose acceptance is extended openly (concern-matrix §6): the LB execution must also instantiate `seqlock_client_equal_pairs` with a read response; optionally the MP shape with zr() = 1 at module level. m-9 → separate task (touches `RelaxedModuleFacts.v`). m-2 → not possible here (no 9.2.0; author decision).
- **Escalated to author (research-level, batched for the end of the SL group):** M-10 (trace-predicate client vs client program; "contextual refinement" wording), M-1/Q3 (complete executions only vs B4's "every completed abstract read"), M-7/Q4 (flagship client). No later SL task depends on them.
- **Concern-matrix rows changed:** header note (9.3.0 build); Meta-3 ❌→🟡; B4 ❌→🟡 (K/S/P rewritten, m-10 citation fixes applied); B3 (iv) note; C5 ❌→🟡 (SeqLock only); §3 two new rows (client reasoning 🟡; same-epoch ❌); §4 four theorems added to the closed list and the regression list; §5 LB row note; §6 SL-client status and SL-nonvac acceptance extension.

## 2026-10-13 — archive of `latest-review.md` (SL-client iteration 1) before overwrite

Findings of the SL-client iteration-1 review (full text in the log entry "loop SL-client — iteration 1" above and in the reviewer's report, not committed): BLOCKER 0 new (B-1/B-2/B-3/B-4 persisting); MAJOR M-3 (non-vacuity), M-1 (complete only), M-7 (client verification thin, reduced), M-10 (client = trace predicate, no refinement theorem); MINOR m-8 (header), m-9 (generic lemmas in an example file), m-10 (report citations), m-2 (9.2.0 / vm_compute / rocqchk).
Note: the iteration-2 review of SL-client was first dispatched to the same reviewer instance, which was interrupted by a session restart without a report; it was re-run by a fresh `rocq-research-reviewer` instance.

## 2026-10-13 — loop SL-client — iteration 2

- **HEAD before/after:** `6e2b575` → uncommitted (only `examples/Relaxed/SeqLockClients.v` changed: 500 → 1113 lines, 23 → 61 results).
- **Task:** address SL-client.1 review: m-8 (header) and M-7's actionable part (reusable client rules), widened openly (see iteration 1 entry); concerns as in iteration 1 plus overview.tex:276 (same epoch).
- **Writer:** interface rules for every `trace_wf` trace and every witness (`client_rule_same_epoch`, `client_rule_read_not_future`, `client_rule_mp_order`, `client_rule_mp_zr_value`); module-level `seqlock_client_same_epoch(_K)`, `read_not_future(_po)(_K)`, `mp_order(_K)`, `mp_zr_value(_K)`; spec lemmas `reg_epoch`, `nu_sl_epoch`, `nuF_all_epoch`, `nuF_all_read_src`, `nuF_all_z_after`; `trace_wf` with `over_trace_wf` for every module trace. `equal_pairs` and `mp_forbidden` re-derived as corollaries. Semantic/assumption changes: none to existing statements or definitions.
- **Verification (orchestrator):** in-tree file = verified snapshot; independent scratch compile OK (an earlier scratch attempt failed only because the copy's basename differed from the module name — harness error, not a proof error); `make -k -j10` 171/172 (DCPOs only); 23 iteration-1 statements and 6 definitions textually identical; only new definition `trace_wf`; no module-level theorem has `trace_wf`; no forbidden constructs; Print Assumptions: 61/61 closed, 45 key theorems identical to baseline.
- **Review (fresh `rocq-research-reviewer`, the first dispatch was lost to a session restart):** BLOCKER 0 new (B-1/B-2/B-3/B-4 persisting, out of scope); MAJOR: M-3 (routed, SL-nonvac acceptance extended), M-1 and M-10 (research-level, author), M-7 actionable part RESOLVED; MINOR: m-8 RESOLVED, m-10 RESOLVED (one nit), new m-11 (header: non-sequitur on monotonicity, overstated "needs an execution"), m-12 (value-based "epoch" caveat missing from header), m-13 (`seqlock_client_mp_order(_K)` existential in W), m-14 optional (interface-level instance), m-9/m-2 persisting. Verdict: **SL-client done at 🟡, no further iteration required, no redesign.** Kernel-level check that iteration-1 statements are identical (`Set Printing All`).
- **Reviewer correction to iteration 1:** "nonempty I unused by the proofs" withdrawn as a gap: every for-all-witnesses safety fact holds for I = ∅ by `rel_lin_mono`; MP depends on the two pairs *not* being in I. Matrix updated.
- **Orchestrator check of a reviewer claim:** ran the reviewer's counter-witness script (`W1`: second writer of (1,1); `W2`: (x,y) = (0,0)): both `nuF_all` goals close, so the MP rule's side conditions are necessary.
- **Disputes:** none.
- **Orchestrator decision:** one more small iteration (3) for m-11, m-12, m-13 (m-14 optional). Reason: m-11 and m-12 are inaccuracies/omissions in the header of a file this loop created, and CLAUDE.md requires accurate headers; m-13 makes a cited module theorem weaker than its rule. The reviewer suggested bundling them with m-9; m-9 stays a separate task because it touches `RelaxedModuleFacts.v`.
- **Escalated to author (batched):** M-10, M-1/Q3, Q4 (unchanged from iteration 1).
- **Concern-matrix rows changed:** Meta-3 (handled-by text), B4 (K/S/P/next rewritten; "I nonempty but unused" replaced by the monotonicity remark), C5 note, B3 (iv) note, §3 client-reasoning row (rules added), §3 same-epoch row ❌→🟡, §4 closed list and regression list (+4 names), §6 SL-client done (🟡) and SL-nonvac acceptance (a)–(e).

## 2026-10-13 — archive of `latest-review.md` (SL-client iteration 2) before overwrite

SL-client iteration-2 review (fresh reviewer): BLOCKER 0 new; MAJOR M-3 (routed to SL-nonvac, acceptance a–e), M-1, M-10 (author), M-7 actionable part RESOLVED (with the correction that "nonempty I unused" is inherent to safety facts, `rel_lin_mono`); MINOR m-8, m-10 RESOLVED, new m-11 (header monotonicity/LB wording), m-12 (value-based epoch caveat), m-13 (`mp_order` existential in W), m-14 optional (interface-level instance), m-9, m-2 persisting. Verdict: done at 🟡. The full text is reproduced in the log entry for iteration 2's decisions and in the reviewer's report.

## 2026-10-13 — loop SL-client — iteration 3 (loop closed)

- **HEAD before/after:** `6e2b575` → uncommitted (only `examples/Relaxed/SeqLockClients.v`: 1113 → 1405 lines, 61 → 72 results).
- **Task:** MINOR findings m-11 (header monotonicity/LB wording), m-12 (value-based epoch caveat), m-13 (`mp_order` existential in W), m-14 optional (interface-level instance).
- **Writer:** header fixes; `seqlock_client_mp_order(_K)` restated as "rel_lin and every witness orders kz before kq" (**statement change, a strengthening; reported**); Part 5 `Section MPInstance`: an 8-event overlay trace with both same-thread overlaps and no real-time edges, all rule hypotheses discharged (`mp_trace_rule_hyps`), `mp_trace_rule_instance`, `mp_trace_zr0_not_rel_lin`, and the counterfactual `mp_trace_zr0_zw_write_indep` (with `dto DW Wmb` flipped the rules fail).
- **Verification (orchestrator):** of the 61 iteration-2 results, only the two `mp_order` statements changed; 11 new results; no definition changed; no forbidden constructs (six `Context` parameters); independent scratch compile OK; `make -k -j10` 171/172 (DCPOs only); Print Assumptions 72/72 closed; 45 key theorems identical to baseline.
- **Review (same reviewer instance as iteration 2):** BLOCKER 0 new; MAJOR M-3 (routed), M-1, M-10 (author) persisting, nothing actionable in scope; MINOR m-11..m-14 RESOLVED; reviewer independently proved the old existential `mp_order` from the new one (`old_from_new`, closed) and checked old statements kernel-identical; new optional m-15 (single-statement table-dependence corollary). **Verdict: SL-client done at 🟡; stop the loop.**
- **Disputes:** none.
- **Loop outcome (SL-client, 3 iterations):** module-level client layer for SeqLock ⊎ COH[z]: interface rules (every witness), module theorems with exactly the module theorem's hypotheses (same epoch, a=b, read-not-future, MP rule/value/forbidden), and an interface-level MP instance with a table-dependence counterexample. Open: M-3 non-vacuity at module level (SL-nonvac, extended acceptance a–f); m-9; m-15 optional; m-2 (9.2.0 not checked).
- **Escalated to author (batched):** M-10 (trace-predicate client vs client program / "contextual refinement"), M-1/Q3 (complete executions only), Q4 (flagship client).
- **Concern-matrix rows changed:** B4 (mp_order entry, Part 5, result count, next), §3 client-reasoning row (+Part 5), §3 same-epoch row (header caveat note), §4 closed list (72 results; mp_order strengthening noted), §5 LB row note, §6 SL-client closed after it. 3, SL-nonvac acceptance item (f).

## 2026-10-13 — loop SL-nonvac — iteration 1 started

- Brief based on `.rocq-review/tasks/SL-nonvac.md`, re-verified (frontier rules F1–F3, `tagged_invoke`, per-method future stores; `upres rc plainTL (RdZ _) c = false` for A's write calls, by hand — Writer to confirm in Coq).
- **Target widened openly** per the SL-client reviews (M-3): instantiate the SeqLockClients theorems on `T_lb`; a second MP-shaped execution `T_mp` with both overlaps is required for the task (optional (c) read-then-write same thread; optional (f) overlay projection = `SeqLockClients.mp_trace 1`). File placed after `SeqLockClients.v` in `_CoqProject` (imports it), not after `SeqLockModuleExample.v` as the prepared brief said.

## 2026-10-13 — running-example assessment (author question: "how far are we from a formalization usable as the paper's running example?"; no Rocq changes)

- Read-only workflow, 9 agents: 5 mappers, 1 synthesis, 3 `rocq-research-reviewer` verifications (overclaim / underclaim / paper fidelity). Output: `.rocq-review/running-example-gap.md` (41 rows, 24 rows corrected by verifiers, 14 rows added).
- Main conclusions (to be confirmed by the author's decisions):
  - The kernel side of a single-layer example (SeqLock ⊎ COH[z]) largely exists: `seqlock_module_rel_lin`, the `SeqLockClients` client layer, and now the `SeqLockLB` executions. TicketLock and the tower are witness-level only.
  - The largest gap is the paper: it prints a TSO SeqLock without barriers, with I = ∅ and rd ↦ rfence / wrt ↦ lfence, and an RLHL/VLHL outline. Coq verifies the COH barrier variant with the category table (write ↦ Wmb, read ↦ Rmb), which no .tex file mentions, and refutes the printed modes for that variant.
  - Further gaps:
    - no OOTA result at any level (headline claim);
    - code faithfulness: `SeqLockProg` adds waits after acq/get_ticket and before retry, and uses positional tags;
    - no Counter layer;
    - `memory/` not connected (no COH instance, barriers, RMW);
    - complete executions only;
    - full build fails on 9.3 (DCPOs.v) and nothing is rechecked on 9.2.0.
- **New research-level finding (verifier, derivation only):** store forwarding may make the example's interface unsound for x86-TSO-like oMCA memory. Recorded as research-intent Q6; SL-mem marked blocked on it in concern-matrix §6; A2 row annotated. I re-derived the overlay cycle and the TSO execution by hand and agree; it still needs a Coq lemma (interface level, S) and a herd7 run.
- Escalated to author: Q4 (which running example), D3 (categories + dto table in the main text), D6 (retire the TSO SeqLock), code faithfulness (print futures with waits vs. remove waits), Counter layer, Q3/D7, Q6.

## 2026-10-13 — author decisions on the running example (no Rocq changes)

- Recorded in research-intent §8: COH SeqLock + category table as the running example (TSO SeqLock retired/relabelled); Q6 → redesign with buffered cells; print the verified futures program; full Tier B.
- Consequence for the queue: the buffered-cell redesign changes the leaf specifications of every layer (x, y, z, nxt, own) and the categories, hence `seqlock_S1` and the module proof. SL-tower and SL-mem are therefore re-sequenced **after** a Q6 confirmation step and an author-approved redesign plan; doing SL-tower on COH registers first would be redone. SL-client and SL-nonvac results remain valid for the COH-register fragment.

## 2026-10-13 — archive of `latest-review.md` (SL-client iteration 3) before overwrite

SL-client iteration-3 review: BLOCKER 0 new; MAJOR M-3 (routed to SL-nonvac), M-1, M-10 (author); MINOR m-11..m-14 RESOLVED, m-15 new optional (single-statement table-dependence corollary), m-9, m-2 persisting. Verdict: SL-client done at 🟡; stop. The reviewer proved `old_from_new` (the iteration-2 existential `mp_order` follows from the iteration-3 universal one).

## 2026-10-13 — loop SL-nonvac — iteration 1

- **HEAD before/after:** `6e2b575` → uncommitted (new `examples/Relaxed/SeqLockLB.v`, 1082 lines, 54 results; `_CoqProject` +1 line after `SeqLockClients.v`).
- **Task:** concrete concurrent module executions making `seqlock_module_rel_lin` and the SeqLockClients theorems non-vacuous (acceptance widened openly: items a–f); concerns M-3, intro.tex:12/:74/:110, B5, §5.
- **Writer:** `T_lb` (LB, both same-thread overlaps) and `T_mp` (MP, both overlaps; overlay projection = `mp_trace 1`), both complete, over a new response-checking underlay `VEa` (atomic at responses, `SeqLockCOH.pre`/`post`); underlay `rel_lin` by explicit witnesses; `seqlock_lb_module`; `lb_refuted` (any relation keeping (zr,write),(read,zw)) with `seqlock_lb_not_classical`, `_paper_signature`, `_paper_modes`; client instances; packaged `seqlock_lb_nonvacuous`, `seqlock_mp_nonvacuous`. Semantic/assumption changes: none to existing files.
- **Verification (orchestrator):** no tracked `.v` change; `SeqLockClients.v` unchanged; no forbidden constructs (header prose mentions vm_compute only to say it is unused); scratch compile OK; `make -k -j10` 172/173 (DCPOs only); Print Assumptions 54/54 closed; key theorems identical to baseline. Read `VEa` and `seqlock_lb_nonvacuous`.
- **Review (fresh reviewer):** BLOCKER 0 new; **M-3 RESOLVED for the SeqLock scope**; new **MAJOR M-11**: `VEa` does not implement ν_E — the reviewer kernel-checked (toplevel) a complete `VEa` execution `T_bad` (MP with `zr()=0`) whose underlay and overlay parts are not `rel_lin`, so over `VEa` the SeqLock violates MP; the header omits this. M-1, M-5 (OOTA), B-4 persisting (B-4 now with a module-level refutation of the printed signature). MINOR m-16 (false wording "read responds while write pending"), m-17 ("classical linearizability" wording), optional m-18 (`fence_le` corollary in the paper's vocabulary), m-19 (no retrying read at module level), hygiene (`Local` abbreviations). Verdict: one small iteration 2, then close; suggests a new optional task SL-VE (`VEb` implementing ν_E).
- **Orchestrator check of a reviewer claim:** re-ran the reviewer's `T_bad` script: `bad_execution` and `bad_underlay_not_rel_lin` are closed under the global context. M-11 confirmed.
- **Disputes:** none.
- **Concern-matrix rows changed:** Meta-3, B4 (non-vacuity text, next), B5 (K/S + next), §3 client-reasoning and same-epoch gap lists (M-3 → M-11), §4 closed list (+54) and regression list (+7 SeqLockLB names), §5 LB row rewritten (Coq ✅ existential at module level, paper ❌), §5 OOTA row (SeqLockLB has no dependencies; todo-oopsla-v2.md:25 overclaims), §6 SL-nonvac status and new optional SL-VE entry.

## 2026-10-13 — archive of `latest-review.md` (SL-nonvac iteration 1) before overwrite

SL-nonvac iteration-1 review: BLOCKER 0 new; M-3 RESOLVED (SeqLock scope); new MAJOR M-11 (`VEa` does not implement ν_E; `T_bad` kernel-checked by the reviewer and re-run by the orchestrator); M-1, M-5, B-4 persisting; MINOR m-16, m-17, optional m-18, m-19, hygiene. Verdict: one small iteration, then close; suggested optional task SL-VE.

## 2026-10-13 — loop SL-nonvac — iteration 2 (loop closed)

- **HEAD before/after:** `6e2b575` → uncommitted (only `examples/Relaxed/SeqLockLB.v`: 1082 → 1460 lines, 54 → 67 results).
- **Task:** M-11 (actionable: header + `T_bad`), m-16, m-17; optional m-18, underlay-level LB, hygiene.
- **Writer:** Part 9 `T_bad` (`bad_execution`, `bad_underlay_not_rel_lin`, `bad_overlay_not_rel_lin`); header rewritten on `VEa` (value check in response order only, barriers no-ops, adds no logical strength); wording fixes m-16/m-17; `seqlock_lb_paper_tensor` (paper's `Tens.tensor_semi_independent` with rd ↦ RFence, wrt ↦ LFence, for every I_SeqLock, I_z, z-modes); `lb_underlay_not_classical` (memory-level LB inside `T_lb`); `Local` abbreviations. m-19 deferred. Semantic/assumption changes: none.
- **Verification (orchestrator):** all 54 iteration-1 statements and all iteration-1 definitions textually unchanged (against my it1 snapshot); 13 new results; scratch compile OK; `make -k -j10` 172/173 (DCPOs only); Print Assumptions 67/67 closed; key theorems identical to baseline.
- **Review (same reviewer instance):** BLOCKER 0 new; M-11 actionable part RESOLVED (research part → author, with B-3); m-16, m-17, m-18 RESOLVED; reviewer confirmed at kernel level that 54 statements + 35 definitions are identical (89 pairs, 0 mismatches); accepted the Writer's correction of its phrasing (F2 keeps cross-call invocation order; the response/effect is what `VEa` leaves unconstrained); new optional m-21 (header nit: effects also unordered within one call), m-22 (one-statement B-4 corollary). **Verdict: SL-nonvac done; stop.**
- **Disputes:** one (phrasing of M-11), resolved in the Writer's favour by the reviewer with a cited rule (`must_precede`, RelaxedModuleSemantics.v:256).
- **Loop outcome (SL-nonvac, 2 iterations):** module-level non-vacuity of the SeqLock module theorem and its client theorems (LB and MP executions with overlaps); LB accepted under the exported interface and rejected classically at object and memory level; the printed SeqLock signature refuted at module level in the paper's own tensor rule; `T_bad` shows the underlay hypothesis is load-bearing and that `VEa` is not an adequate underlay.
- **Escalated to author:** which operational underlay stands for COH (SL-VE vs SL-mem), now subsumed by the buffered-cell redesign decision (Q6, research-intent §8).
- **Concern-matrix rows changed:** §6 SL-nonvac closed; §4 counts and regression list (+4); B3 (iii) note; B4 (T_bad in-tree; next); B5 note (+ `seqlock_lb_paper_tensor`); §5 LB row (+ `lb_underlay_not_classical`, `seqlock_lb_paper_tensor`); §3 new row (LB rejected classically, intro.tex:12/:74).

## 2026-10-13 — buffered-cell redesign: Q6 confirmation and plan (read-only workflow; no Rocq changes)

- 7-agent workflow (1 confirmation, 3 designs, 2 `rocq-research-reviewer` judges, 1 synthesis). Output: `.rocq-review/buffered-cell-plan.md`; confirmation scripts in the job's tmp (`q6_scripts.txt`), not in the tree.
- **Q6 confirmed in Coq** (piped, closed): overlay `q6_not_rel_lin` (every rc); underlay `q6_underlay_no_WF` and `q6_underlay_not_rel_lin` (hypothesis shape of `seqlock_module_rel_lin`); memory/ admits the cell history with forwarding (`sq_V`, `sq_nu`, `q6_cells_TSO_consistent`, `classic`). Controls closed: same trace with zr()=1 is rel_lin; plain SB is rel_lin. Hardware: derivation only (herd7 unavailable). Consequence: `seqlock_module_rel_lin` is not wrong but its hypothesis fails on this x86 execution; SL-mem's direction is false as posed.
- **Plan (merge, MEM-FIRST base, judges 7.5/7.0):** keep categories, table, `findep`/`sindep`, futures program, windows, `rel_lin`/`rhb`; replace the specs: underlay hybrid Hν (buffered x,y,z via memory/ `V`, ghost barrier locations Bw≠Br, atomic TicketLock/own/nxt with an atomic clause), overlay joint marker spec nuJ (atomic `nu_sl` + hidden publication marker, contract with Buf[z] read off `findep`; corollary ⊆ ν_{I_F}[{sl,z}] ∩ Lin_sl). Reuse existing proofs unchanged via SC-ification into `SeqLockCOH.WF`/`SeqLockTower.WF0`; new files only. Phases 0–7, ~20–28 Writer iterations for full Tier B (G-2 x86 end-to-end optional, XL).
- **Author questions** (amend decision: categories stay; exported interface; memory convention/hardware scope; Tier-B details and existing headers) put to the author. Phase 0 (Q6-1: commit the Q6 refutations as `SeqLockQ6.v`) is design-independent and starts now.

## 2026-10-13 — author decisions on the redesign plan (no Rocq changes)

- Recorded in research-intent §8: specs-only amendment (categories/table/program/windows stay); marker spec as exported interface; **x86-TSO + ARMv8** (G-3 ARM check and herd7 runs required; memory convention stays "writes respond at issue", so x, y and z are buffered); pragmatic Tier B (atomic-faa Counter, G-1 bridge, G-2 optional, R-1 header notes; old files kept as the forwarding-free instance).

## 2026-10-13 — loop Q6-evidence (Phase 0 of the redesign) — iteration 1 (Writer + verification; review pending)

- **HEAD before/after:** `6e2b575` → uncommitted (new `examples/Relaxed/SeqLockQ6.v` 1163 lines / 51 results, `examples/Relaxed/SeqLockQ6Mem.v` 356 lines / 18 results; `_CoqProject` +2 lines).
- **Task:** plan tasks Q6-1, Q6-3, Q6-2 as one bounded task: commit the kernel-checked Q6 refutations, memory/ admission, and the real-time obstruction.
- **Writer:** all scripts committed (B and D re-derived; `_any` generalizations; `q6_module_hypothesis_fails`); **Q6-2: the obstruction holds** (register x/y refuted under writes-respond-at-issue); Q6-3 plus `q6_cells_x86_trace`/`rt_cells_x86_trace` via `TSO.tso_traces`. No `vm_compute` (`exact eq_refl`). Semantic/assumption changes: none to existing files.
- **Verification (orchestrator):** no tracked `.v` change, memory/ untouched, SeqLockClients/SeqLockLB unchanged; no forbidden constructs (prose-only vm_compute mentions; `Context`s are parameters incl. a decidable-equality function); both files compile independently; `make -k -j10` 174/175 (DCPOs only); Print Assumptions 68/69 closed, `q6_cells_TSO_consistent` uses `classic` only; key theorems identical to baseline.

## 2026-10-13 — archive of `latest-review.md` (SL-nonvac iteration 2) before overwrite

SL-nonvac iteration-2 review: BLOCKER 0; M-11 actionable part, m-16, m-17, m-18 RESOLVED; 54 statements + 35 definitions kernel-identical; optional m-19, m-21, m-22. Verdict: SL-nonvac done.

- **Review of Q6-evidence it. 1 (fresh reviewer):** BLOCKER 0. MAJOR:
  - M-12 (Q6-2's run is forwarding-free, so the old register-cell results are the *publication-at-response, forwarding-free* instance, not "the forwarding-free instance"; the obstruction is generic and also hits the LatchSet-on-COH grounding — research-level label, author);
  - M-13 (locked-RMW approximation argued backwards; restore the reads);
  - M-14 (Reviewer A's literal two-location test and Mem.tex:14's ∀I claim still not in Coq);
  - B-3 persisting (hand mapping cells ↔ calls);
  - M-4 persisting plus a new risk: on ARMv8 the TicketLock version word may also need a hidden publication point; check in G-3 before F-2 freezes the TicketLock spec.

  MINOR: m-23 (controls do not isolate the forwarded read; reviewer kernel-checked d1/d2), m-24..m-29. Verdict: Phase 0 substantially done; one short iteration.
- **Concern-matrix rows changed:** Meta-1, A2 (K/S extended; still no literal test; next = M-14), new rows Q6 and Q6-2, §4 closed/classic/regression lists, §6 SL-mem superseded by Phase G, new §6 entry for the redesign (R-1 reword, G-3 moved forward with the version-word check).
- **Iteration 2 dispatched** to the same Writer: M-13, M-14 (a)(b), (b′) recommended, m-23, m-24, m-25/26/B-3/M-12 wording, m-29 (no unverified citations); m-27/m-28 → N-1; ∀I_F necessity theorem optional.
- **To the author:** M-12 label; M-4 re-sequencing (G-3 before F-2); the LatchSet consequence of Q6-2.

## 2026-10-13 — author decisions after the Q6-evidence review (no Rocq changes)

- Old register-cell results removed from the paper's mechanization table (kept in the repo); G-3 moved before F-2; LatchSet directly on buffered cells. Recorded in research-intent §8, concern-matrix (Q6-2 row, §6), and an amendment section in `buffered-cell-plan.md`.

## 2026-10-13 — archive of `latest-review.md` (Q6-evidence iteration 1) before overwrite

Q6-evidence it. 1 review: BLOCKER 0; MAJOR M-12 (label), M-13 (locked-RMW argument backwards), M-14 (Reviewer A's literal test), B-3, M-4 (+ ARM version-word risk); MINOR m-23..m-29. Verdict: substantially done, one short iteration.

## 2026-10-13 — loop Q6-evidence — iteration 2 (loop closed; Phase 0 done)

- **HEAD before/after:** `6e2b575` → uncommitted (`SeqLockQ6.v` 57 results, `SeqLockQ6Mem.v` 23 results, new `RegisterSB.v` 24 results; `_CoqProject` +1).
- **Writer:**
  - M-13: restored the XCHG reads; `locked_rmw`, `sq_locked`, `rt_cells_locked`. **Reported definition changes:** `sq`, `rt_cells`, with position/handle updates in 3 statements.
  - M-14: Reviewer A's literal test (`sbrfi_V/_nu/_x86_trace`, `sbrfi_not_rel_lin_TSO`).
  - **Disputed the reviewer's (b′) with a kernel counterexample** (`sbrfi_rel_lin_loc`) and proved the corrected form (`sbrfi_not_rel_lin_any`, `sbrfi_needs_rr_reordering`).
  - Controls d1/d2; header wording.
- **Verification (orchestrator):** statement/definition diff exactly as reported; three scratch compiles OK; `make -k -j10` 175/176 (DCPOs only); Print Assumptions 103/104 closed, `q6_cells_TSO_consistent` uses `classic`; key theorems identical; `sbrfi_rel_lin_loc` closed.
- **Review (same reviewer):** **Phase 0 done; stop.**
  - BLOCKER B-4 persists with two new paper refutations: Mem.tex:14's literal sentence (by `sbrfi_rel_lin_loc`) and trace.tex:262 `rem:ra-tso` (by `sbrfi_not_rel_lin_TSO` + `sbrfi_x86_trace`).
  - MAJOR resolved: M-13, M-14 (a, b, b′), M-12. B-3 and M-4 are scheduled (G-1, G-3).
  - MINOR resolved: m-23..m-26, m-29. New: m-30 (nit), m-31 (stale R-1 text in the plan body), m-32 (optional).
- **Disputes and resolution:** (b′) — a factual question, settled by kernel evidence (`sbrfi_rel_lin_loc`, closed; orchestrator-checked); the reviewer accepted the dispute.
- **Records:** m-31 fixed by the orchestrator (stale "forwarding-free instance" phrases in `buffered-cell-plan.md` annotated as superseded).
- **Concern-matrix rows changed:** A2 (literal test done; Mem.tex:14 refuted literally; next = paper edits), Meta-1 (+RegisterSB), Q6 (Phase 0 done), Q6-2, §4 (+RegisterSB; regression +4), §6 (Phase 0 done; optional closures).
- **To the author (paper):** Mem.tex:14 must become "no I keeping same-location and read–read order"; `rem:ra-tso` (trace.tex:262) and "TSO data cells" (overview.tex:278) are now kernel-refuted.

## 2026-10-13 — loop F-1 (Phase 1 of the redesign) — iteration 1 started

- **Order note:** in the plan, G-3 depends on F-1, because it compares F-1's abstract barrier semantics with ARM. So the author's order "F-1, F-3, G-3 → F-2" is executed as F-1 → G-3 → F-3 → F-2. G-3 still precedes F-2, as the author required.
- **Brief:** plan task F-1. New file `memory/TableBarrier.v`:
  - table-induced `I_tab`, with ghost barrier locations Bw ≠ Br;
  - `I_tab_cross`, `declarative_tab`, `ppo_wmb_WW`, `ppo_rmb_RR`;
  - `contract_handle_invariant`: stop and report if the planned statement is false;
  - non-vacuity: MP+wmb/rmb has no witness, and SB+rfi is in `nu`.
- **Constraints:** no import of `examples/`; no existing file changes.

- **F-1 it. 1 Writer:** new `memory/TableBarrier.v`, 76 results:
  - `I_tab`, `tab_cfg` with ghost GBw ≠ GBr, `declarative_tab`, `ppo_wmb_WW`, `ppo_rmb_RR`;
  - `contract_handle_invariant`, with two kernel-checked precisions of the plan: `Nat.compare` agreement, and the symmetry premise;
  - non-vacuity: MP+wmb/rmb forbidden via D2 and `declarative_tab`; SB+rfi allowed; controls.
  Premises reported: `write_symmetric`, `Idec`, section hypothesis `Hg`. No existing file changed; no examples/ import.
- **Verification (orchestrator):** scratch compile OK; `make -k -j10` 176/177 (DCPOs only); Print Assumptions: 72 closed, 4 `classic` only (`declarative_tab`, `mp_wmb_rmb_forbidden(_pre0)`, `sbrfi_tab_consistent`); key theorems identical; other uncommitted files unchanged. My first PA run reported 17 ERRORs: script-path errors (sub-module `NonVacuity`), re-run correctly.
- **Review dispatched** (fresh reviewer). It is asked in particular to verify `write_symmetric` for the real dto categories (DW, Wmb, DRMW).

## 2026-10-13 — archive of `latest-review.md` (Q6-evidence iteration 2) before overwrite

Q6-evidence it. 2 review: Phase 0 done. BLOCKER B-4 persists with two new paper refutations (Mem.tex:14 literal, trace.tex:262 `rem:ra-tso`). M-13, M-14 (a, b, b′), M-12 resolved. B-3 and M-4 scheduled. MINOR m-23..m-26 and m-29 resolved; m-30, m-31 (fixed in records), m-32 optional. The (b′) dispute was accepted.

- **Review of F-1 it. 1 (fresh reviewer):** BLOCKER 0, MAJOR 0 new (B-3 progress, M-4 scheduled).
  - MINOR: m-33 (ix := 0 makes the contract vacuous; program-order bridge and ν-level invariance missing), m-34 (scope limits of the table instance), m-35 (mo at Bw is an argument, not a lemma), m-36 (kernel versions of the dto/sindep evaluations), m-37 (nit), m-38 (optional).
  - Reviewer evaluations: `ato` = `dto`; write-symmetry on {DW, Wmb, DRMW} but not with DWrel; `I_tab` = `sindep` exactly on SeqLock cell ops.
  - Accepted the Writer's three plan corrections (`Nat.compare`, symmetry, the "presents ∧ respects" form of MP-forbidden).
  - Verdict: stop. Header patch now; carry m-33(i,ii) → D-2/G-1, m-35 → G-1, m-36 → S-1.
  - Suggested cheap x86 cell grounding via TSO contract monotonicity.
- **Orchestrator decision:** one more small F-1 iteration (2):
  - header patch for m-33 and m-34 (CLAUDE.md: headers must be accurate);
  - the x86 cell-level grounding addendum, pulled forward from G-1 because it is cheap, independent, serves the author's x86 scope, and avoids m-35 for x86;
  - optional m-38.
  The carried items are recorded in the plan amendments. Concern matrix: new row F-1; §4 closed list updated.

## 2026-10-13 — archive of `latest-review.md` (F-1 iteration 1) before overwrite

F-1 it. 1 review: BLOCKER 0, MAJOR 0 new. MINOR m-33..m-38. Reviewer evaluations: `ato` = `dto`, write-symmetry on {DW, Wmb, DRMW}, and `I_tab` = `sindep` on SeqLock cell ops. Verdict: stop, with a header patch; it suggested x86 cell grounding.

## 2026-10-13 — loop F-1 — iteration 2 (loop closed)

- **HEAD before/after:** `6e2b575` → uncommitted (`memory/TableBarrier.v`: header plus 2 new results, 78 total; new `memory/TableBarrierTSO.v`, 26 results; `_CoqProject` +1).
- **Writer:**
  - m-33 and m-34 header fixes;
  - x86 addendum: `contract_mono`, `contract_TSO_strongest`, `tab_cfg_TSO`, `x86_trace_V_tab(_index)`, and machine-level ghost insertion (~380 lines, against ~150 estimated);
  - m-38 positive control.
  No existing statement changed.
- **Verification (orchestrator):** all 76 it1 statements and definitions of TableBarrier unchanged (against my it1 snapshot, which the Writer had not found); scratch compiles OK; `make -k -j10` 177/178 (DCPOs only); Print Assumptions 100/104 closed, the same 4 `classic`; key theorems identical.
- **Review (same reviewer):** BLOCKER 0, MAJOR 0 new. m-33 (header part), m-34 and m-38 resolved. The x86 addendum is correct and as strong as claimed. It is FIFO-specific: it does not transfer to ARM, and on x86 the barriers play no role in V membership. New nits m-39 (iterated multi-barrier insertion, for G-1) and m-40 (boundary case). m-35 is reclassified: not needed for x86, needed for the ARM/declarative route. **Verdict: F-1 done; proceed to G-3.**
- **Records:** plan :250 "resolves" corrected to "partially resolves" (two occurrences annotated).
- **Concern-matrix rows changed:** F-1 row (done; TableBarrierTSO), Meta-1 (x86 cell-level containment), §4 closed list.
- **Open contested point for G-3:** the "RSW through the object" outcome (T1: zr()=1; zw(2); zr()=2; read()=(0,0) ‖ T2: write(1,1); zw(1)). Design 3 derived it **allowed** on ARMv8 (dmb ld/st). Judge 1 derived an ob cycle (Wx →bob Wz →rfe Rz1 →bob Rx →fre Wx), so **forbidden**. Neither is checked. G-3 must settle it in the extended ARM model, and herd7 must check it.

## 2026-10-13 — loop G-3 (ARMv8 check, moved before F-2) — iteration 1 started

- **Brief:** new `memory/ARMBar.v`, a copy-extension of `memory/ARM.v` with DMB LD/ST/SY and RMW flavours, each clause annotated against aarch64.cat. Deliverables:
  - named verdict lemmas: (a) the minimal SeqLockZ+rfi core; (b) the full test if feasible; (c) **RSW-through-object** (contested: design 3 says allowed, judge 1 says forbidden; relate to `Litmus.RSW` / Mem.tex Δ2); (d) the F-2 atomic clause vs RMW and get flavours;
  - the TicketLock version-word risk (M-4), framed as a research-level recommendation;
  - `memory/herd/*.litmus` (x86 + AArch64) and `README.md` for the author to run herd7.
- **Priority if too large:** 2(c), 3, 4, then the rest. Report only; no hardware soundness claim. Material: `g3_material.md` (unverified derivations).

- **G-3 it. 1 Writer:**
  - **Deliverables.** New `memory/ARMBar.v` (101 results, three model variants POPL18/Cur/CurSI, flagged uncertain readings F1/F2) and `memory/herd/` (README + 26 AArch64 + 8 x86 litmus files, UNVERIFIED).
  - **RSW-through-object FORBIDDEN** in all variants and flavours; Judge 1's cycle is correct and Design 3 was wrong. The LDAR control is allowed (the Δ2 shape). The cell-level ν_{I_tab} also forbids it.
  - **SeqLockZ+rfi** allowed (core and full).
  - **Atomic clause:** ordering realized by every RMW flavour with a plain LDR get, given DMB ST before and DMB LD after. The Writer disputes plan :647.
  - **Version word:** the risk is real on ARM in this model and absent on x86. Options R1/R2/R3 are NEEDS-AUTHOR.
- **Verification (orchestrator):** no existing file changed; scratch compile OK; `make -k -j10` 178/179 (DCPOs only); Print Assumptions 67/101 closed, 34 `classic` only; key theorems identical.
- **Review dispatched** (fresh reviewer): model fidelity against aarch64.cat (F1/F2), the RSW verdict, the version-word options, the atomic-clause dispute, herd7 syntax.
- **Pending author decision (queued; the author may be offline):** version word R1/R2/R3. F-2 depends on it; F-3 does not.

## 2026-10-13 — archive of `latest-review.md` (F-1 iteration 2) before overwrite

F-1 it. 2 review: F-1 done. m-33 (header part), m-34 and m-38 resolved. The x86 addendum is correct and FIFO-specific. New nits m-39 and m-40. m-35 is needed for the ARM/declarative route only.

- **Review of G-3 it. 1 (fresh reviewer):** BLOCKER 0.
  - MAJOR M-15 (new, research-level): Δ3 at object level — a reader waiting on zr breaks the hybrid underlay on ARMv8 regardless of R1/R2.
  - MAJOR M-16 (new): the VW conclusion overreaches; the writer side is likely admitted.
  - M-4 narrowed; B-3 persists. MINOR m-41 (paper Δ2 wording POPL'18-specific), m-42, m-43, m-44.
  - The model is faithful as far as the reviewer knows aarch64.cat. F1 is not a real uncertainty; F2 is real, and the reviewer predicts `VW+ldaddal` Forbidden.
  - RSW settled for Judge 1. The atomic-clause dispute was accepted.
  - Verdict: one more iteration before F-2. Reviewer recommends R3 (x86 only) for F-2 now; R4 (Wait-compilation scheme) for any ARM claim.
- **Orchestrator check:** ran the reviewer's RT-get scratch. `rt_get_allowed` is closed; `rt_get_dmbld_forbidden` uses `classic`. The axiomatic half of M-15 is confirmed in the model. The Hν half is a derivation, to be checked in F-2.
- **Records:** research-intent §7 Q7 (ARMv8 claim, R3 vs R4) added; plan amendments (atomic clause, RSW, Q7, M-16); concern matrix new row G-3, Meta-1 note. Guide `paper-running-example-guide.md` to be amended (ARMv8 section).
- **Next:** G-3 it. 2 (M-15 tests, herd files and derivation note; M-16 README/header; m-42/43/44); then F-3. F-2 is frozen on Q7 (author offline; not asked).

## 2026-10-13 — paper guide for the author (no Rocq changes)

- Wrote `.rocq-review/paper-running-example-guide.md` (Chinese, for paper editing on the road).
- Verified it with a 3-agent read-only workflow (Coq claims / paper locations / records). 52 errata, mostly low or medium, no high. Main points:
  - 6 overclaims: `ppo_wmb_WW` composite is in Dc⁺ not ppo; MP-forbidden needs the respects-pre clause; Q6-2 generality; the premise of `sbrfi_needs_rr_reordering`; `bracketed_not_compatible` cited wrongly for the running example; object vs. underlay LB lemmas.
  - Naming: "COH" is pre-redesign; the cells are buffered.
  - The oMCA scope reverses response A2 (:437).
  - Mem.tex:13, not :14.
  - lin-TSO is already cited; the first version invented venues and authors for prior work — removed.
  - Missing pending items: herd7 run, Q1, D5, Q2, Q5, D6, D7.
  - Nothing is committed yet.
- Rewrote the guide as v2 with all corrections and the G-3 §9 (ARM mapping, M-15, options C/A/B). Sent it to the author.

## 2026-10-13 — loop G-3 — iteration 2 (Writer + verification; review dispatched)

- **Writer:** `RTGet`, `MPObj`, 10 `nonvacuous` lemmas, 12 new herd files, README rewrite, `memory/README.md` row.
  - **Reported definition change:** `loc` gains constructor `ln`; `loc_eqb` gains a case.
  - **Key correction:** `mp_obj_forbidden` (classic). A client-visible MP-obj outcome (read()=(0,0) after zr()=1) is FORBIDDEN in the model. Only the stale get_ticket is allowed (`mp_obj_stale_get_allowed`), and the read retries.
  - So M-15 is a proof-route gap (Hν fails on a correct ARM run, like Q6-2), not a client-visible violation on this shape. The prologue DMB LD forbids the stale get.
- **Verification (orchestrator):**
  - Module-qualified diff: only `ARMBar.loc`/`loc_eqb` changed among it1 entries. A name-only diff gave false positives from reused local names in the new sub-modules.
  - Scratch compile OK; `make -k -j10` 178/179 (DCPOs only).
  - Print Assumptions: 82/119 closed, 37 `classic`. Key theorems identical; other uncommitted files unchanged.
- **Guide corrected:** §9.2/9.3 of `paper-running-example-guide.md` had said read() may return (0,0) on ARM. Corrected to: SeqLock correct on MP-obj, but the proof does not cover ARM. Options: C, A (prologue rmb, for the proof only), B, and new D (an overlay-level equivalence argument). Re-sent to the author.
- **Review dispatched** to the same reviewer (dispute of the MP-obj expectation; the `loc` change).

## 2026-10-13 — archive of `latest-review.md` (G-3 iteration 1) before overwrite

G-3 it. 1 review: BLOCKER 0; new MAJORs M-15 (reader-side Δ3 at object level, research-level) and M-16 (version-word conclusion overreached); M-4 narrowed; MINOR m-41..m-44. RSW settled for Judge 1. The atomic-clause dispute was accepted. Verdict: one more iteration.

## 2026-10-13 — loop G-3 — iteration 2 (review recorded; loop closed)

- HEAD before/after: `6e2b575` → uncommitted.
- Task: ARMv8 check (G-3). Concerns: M-4, M-15, M-16, m-42..m-44.
- Writer: see the entry above. Semantic change reported: `ARMBar.loc` gains `ln`. The reviewer accepted it: earlier results are preserved.
- Verification: build ok (DCPOs only); no admits or axioms. Print Assumptions: 82 closed, 37 `classic` (reviewer re-ran all 119).
- Review: BLOCKER 0, MAJOR 3 (M-15 research-level, now characterized correctly; M-4 and B-3 persist), MINOR: m-42/43/44 resolved, new m-45 (only if option B), m-46 (nit). **Verdict: G-3 done for its purpose; stop the loop.**
- Disputes and resolution:
  - The Writer disputed an "expected Allowed" for MP-obj. The reviewer: no such reviewer claim existed. The expectation came from the **orchestrator's brief** (my error in the G-3.2 brief).
  - The reviewer checked `mp_obj_forbidden` independently and accepted it. Settled by evidence (the kernel result plus an independent cycle derivation).
- New from the review, recorded in the matrix:
  - M-15 has **no object-spec repair**.
  - M-15 is **client-visible** at the TicketLock interface and for interfaces with ≥2 cells under a Wait (Δ3; LatchSet, Lock(O)⊗cell).
  - Option D was reframed as "a weaker Hν without Wait-induced load→load real-time edges".
- Escalated to author (queued; author may be offline):
  - ARM option C/B/A/D (Q7). Reviewer: C now, B principled.
  - herd7 runs.
- Concern-matrix rows changed:
  - G-3 → 🟡 done (it. 2).
  - New row M-15 (🟡 research-level).
  - Meta-1 ARM sentence re-characterized.
  - M-16 closed as a records item.
  - Plan :647/:700/:722/:765 marked superseded.
- m-46 (first half) fixed by the orchestrator. It was a non-Coq doc string: the process-history phrase was removed from `memory/herd/aarch64/MP-obj+ldadd.litmus:2` and `memory/herd/README.md:99`. The second half (`MPObj.Xs` has no reader ctrl) needs no change: the verdict is unaffected, and `rt_get_ctrl_allowed` covers it.
- Next: F-3 (independent of the ARM decision). F-2 stays frozen until the author picks the ARM option.

## 2026-10-13 — loop F-3 — iteration 1 (Writer dispatched)

- HEAD `6e2b575`; no prepared `tasks/F-3.md`. The brief is built from `buffered-cell-plan.md` :359–372 (+ :233, :251, :645, :649).
- **Orchestrator Step 1 finding, adjusted openly in the brief:** the plan says the J composition is "proved via `WindowTable.conclusion_of_lp_before`". That lemma's conclusion is existential in `ow`, so it cannot carry a joint `nuJ` that holds only on the lp-sorted list. The reusable part is `WT.lp_before`, whose proof never uses `h_S1`, together with `link_hyps0`/`link_inherit` at a trivial `nuFc`. The Writer is asked to confirm or refute this.
- Baseline: `window_link_table`, `window_link_rect`, `window_composition`, `conclusion_of_lp_before`, `lp_before` are all closed. Checksums of WindowTable/WindowLinkTable/BracketedLink/WindowComposition saved (`jobs/…/tmp/F3_base.sha`).
- Brief: `scratchpad/brief-F-3.1.md`. It adds a required header statement: spec modularity is lost (`p_S1J` is one joint obligation), while ordering stays component-wise.

## 2026-10-13 — loop F-3 — iteration 1 (Writer done; verification; review dispatched)

- **Writer:** `WindowTableJ.v` (319 lines) and `WindowLinkTableJ.v` (582 lines); `_CoqProject` +2 lines. No existing definition or theorem changed.
  - Orchestrator observation: half confirmed, half refuted. `conclusion_of_lp_before` *is* reusable, on `joint S nuJ` (S read as one `unit` component with `IFc := WT.IF`, `IEc := WT.IE`). `lp_before` is reused on `triv S`.
  - `window_link_table_J` is `WLT.window_link_table` at `Comp := unit`, with cross-component ordering supplied to `positional` by `link_lp_ord`.
  - `window_link_table_of_J` comes with an `Example` checking that its type is exactly that of `WLT.window_link_table`.
  - `window_link_table_J_jointE`: constant `compE` over `option Comp`.
- **Verification (orchestrator):**
  - The four protected files pass a shasum check against the pre-task snapshot.
  - `git status` delta: only the two new files, plus 2 `_CoqProject` lines.
  - The forbidden-construct grep finds only Section `Hypothesis` lines, which become theorem premises.
  - Clean rebuild of both files OK. `make -k -j10`: only DCPOs fails.
  - Print Assumptions: 37/37 Closed (36 Lemma/Theorem + Example; `unit_dec`/`opt_dec` are constructive `Defined`).
  - I read both files in full. The statements match the brief, and the theorem conclusion uses `semi_independent F`.
- **Review dispatched:** iteration-1 snapshots are in `jobs/…/tmp/*.it1.v`; the Writer report copy is `writer-F-3.1.md`.

## 2026-10-13 — archive of `latest-review.md` (G-3 iteration 2) before overwrite

G-3 it. 2 review:
- BLOCKER 0.
- MAJOR: M-15, research-level; now characterized as a proof-route gap for SeqLock ⊎ z, client-visible at the TicketLock interface and for ≥2-cell interfaces; no spec-only repair. M-4 and B-3 persist.
- MINOR: m-42/43/44 resolved; new m-45 (only if B), m-46 (nit, fixed).
- Verdict: G-3 done, loop stopped.
- ARM options: C now, B principled, A SeqLock-only, D deferred.

## 2026-10-13 — loop F-3 — iteration 1 (review recorded)

- Review: BLOCKER 0, MAJOR 0, MINOR m-47..m-55.
- Verdict: accept F-3. Fold the actionable minors into a short pass.
- The reviewer accepts the Writer's refutation of the orchestrator's Step-1 observation (`conclusion_of_lp_before` is reusable on `joint S nuJ`).
- Concern-matrix rows changed:
  - F-3 → ✅ (infrastructure) with its S-gaps;
  - "Horizontal composition / compatibility": the redesigned example is not an instance of the product rule (m-50);
  - plan risk :645 closed for BL/WLT, still open for D-1.
- Escalated to author (queued): m-50, i.e. paper wording for the loss of product ⊗ in the running example. overview.tex:341 no longer describes it.
- Iteration 2 sent to the same Writer, covering m-47 (header wording vs. `prop:locality`), m-48 (`link_lp_ord_fields` without `p_S1J`, plus the `lp` reflexivity lemma; needed by D-2), m-49 (inter-derivability) and m-52 (wording). m-51 and m-54 are optional.

## 2026-10-13 — loop F-3 — iteration 2 (minors; loop closed)

- HEAD before/after: `6e2b575` → uncommitted.
- Task: F-3 minors m-47, m-48, m-49, m-52 (required); m-51 and m-54 optional.
- **Writer (same agent):**
  - Additions only: `link_lp_ord_fields` (three ordering fields, no `p_S1J`; its type does not mention `nuJ`), `settingJ_lp` (reflexivity), and `link_lp_ord` re-derived from `link_lp_ord_fields` with its statement unchanged.
  - m-51 done as an addition: `lift` / `window_composition_of_J_any` (unconditional), plus an Example checking that its type equals `WT.window_composition`'s.
  - Headers rewritten for m-47 (overlay-spec shape only; five gaps listed), m-49 (inter-derivability; J-specific content is `link_lp_ord_fields`) and m-52.
  - m-54 DISPUTED: the three section contexts are needed for the exact closed statement shapes, in particular `window_link_table_of_J_statement`. Orchestrator: accepted. The reviewer had marked m-54 optional, and the Writer's reason is checkable from the `Example`.
- **Verification (orchestrator):**
  - Protected files: shasum OK. `_CoqProject` unchanged since it. 1.
  - Module-qualified statement diff it1 → it2: no removed or changed statements; added `lift`, `hyps0_lift`, `conclusion_unlift`, `window_composition_of_J_any`, `link_lp_ord_fields`, `settingJ_lp` (plus the Example).
  - Clean rebuild OK; `make -k -j10`: only DCPOs fails.
  - Print Assumptions: 43/43 Closed.
  - `Check @link_lp_ord_fields` confirms that it does not take `nuJ` or `p_S1J`.
  - I read the new header in full.
- **Review:** no further reviewer round. The it. 1 review already gave "accept F-3 and stop the loop" with no BLOCKER/MAJOR, and the it. 2 delta is additive plus the wording the reviewer asked for, verified above.
- **Loop closed.** Open: m-50 (paper wording, NEEDS-AUTHOR), m-53 (non-product instance → S-2/D-2), m-55 (9.2.0 not built).
- Snapshots: `jobs/…/tmp/*.it2.v`.
- Next: D-1. It is independent of the ARM decision; the brief is `scratchpad/brief-D-1.1.md`.

## 2026-10-13 — loop D-1 — iteration 1 (Writer dispatched)

- HEAD `6e2b575`. There is no prepared `tasks/D-1.md`; the brief is built from plan :416–425 (plus :234, :252, :644, :664, :870, :898).
- **Orchestrator Step 1 (verified):**
  - In `SeqLockModule.v`, `SX rc K VE ic Wu` does not depend on `HWu`.
  - `nuE_replay` (Merge) is the only register→validity bridge. `wit_replay` is used only in `SX_wf`'s `wf_valid` bullet (:999).
  - `SeqLockCOH.WF` (:338) has `wf_valid` as its only semantics field.
  - Print Assumptions of `SeqLockModule.positional`, `SX_wf` and `seqlock_module_rel_lin_K`: all Closed.
- **Brief refinement, stated openly:** the plan says "isolate validity as a section hypothesis". The brief additionally requires that every lemma not needing validity (WF core, the transport lemmas) is stated *without* that hypothesis. Reason: D-2 combines the bridge with S-1's SC-ification (`bwf_scify_WF`), and the `SL.Exec` built from a buffered witness is not SC-valid. This is a refinement within the plan's intent, not a widening of the target.
- Brief: `jobs/…/tmp/brief-D-1.1.md`. Checksums of the protected files: `D1_base.sha`.

- 2026-10-13: the D-1.1 Writer stopped on a network error (API ENOTFOUND). Partial `SeqLockModuleGen.v` (675 lines, compiled); `_CoqProject` not yet touched; protected files unchanged (shasum). Resumed the same Writer from its transcript.

## 2026-10-13 — loop D-1 — iteration 1 (Writer done after resume; verification; review dispatched)

- **Writer:** `SeqLockModuleGen.v` (675 lines); `_CoqProject` +1 line after `SeqLockModule.v`. No existing definition changed. New definitions: `Valid`, `WF_core`.
- **Verification (orchestrator):**
  - Protected files: shasum OK (SeqLockModule, SeqLockCOH, SeqLockProg, BracketedLink, WindowLinkTable, WindowLinkTableJ, WindowTableJ).
  - `git status` delta: only the new file.
  - Forbidden-construct grep: nothing (no Hypothesis/Variable; section `Context`s only).
  - Clean rebuild OK.
  - Print Assumptions: 32/32 Closed (29 Lemma/Theorem + 3 Example). The file has 32 `Qed`s.
  - `About` confirms that `SX_wf_core`, `S1_transport`, `phi_lpq` and `lpu_inj` take `P`/`HWu` and no validity premise, that `positional_gen` takes `Hvalid` (replay), and that `SX_valid_iff` is unconditional.
  - Side note: `About` through a `Module G := …` alias printed "transparent"; through the full path the lemmas are "opaque". It was an alias artifact, not a `Defined`.
- **Review dispatched:** snapshot `SeqLockModuleGen.it1.v`, Writer report copy `writer-D-1.1.md`.

## 2026-10-13 — archive of `latest-review.md` (F-3 iteration 1) before overwrite

F-3 it. 1 review: BLOCKER 0, MAJOR 0, MINOR m-47..m-55. Verdict: accept F-3, fold minors into a short pass (done in it. 2; loop closed). The reviewer accepted the Writer's refutation of the orchestrator's observation (reuse of `conclusion_of_lp_before` on `joint S nuJ`).

## 2026-10-13 — loop D-1 — iteration 1 (review recorded)

- Review: BLOCKER 0, MAJOR 1 (M-17, actionable), MINOR m-56, m-57, m-58 (actionable), m-55 (carry-over).
- Verdict: continue with one short iteration; no redesign.
- Kernel-confirmed: the register spec is used only through validity. The reused SLM names carry no witness: 12 of 49 constants do, and exactly those were copied.
- Concern-matrix rows changed:
  - D-1 (status and content);
  - F-3: risk :645 closed for D-1.
- Plan amendments: :898 corrected, :252 vs :664/:898 reconciled, D-2 route note, S-1/S-2 suggestions recorded (not adopted).
- Iteration 2 sent to the same Writer (M-17, m-56, m-57, m-58).

## 2026-10-13 — loop D-1 — iteration 2 (Writer done; verification; confirmation review dispatched)

- **Writer:** M-17, m-56, m-57 and m-58 FIXED. `SeqLockModuleGen.v` grew from 675 to 962 lines. 128 more lines copied from SeqLockCOH.v (ranges in the header).
- **Verification (orchestrator):**
  - Protected files: shasum OK. `_CoqProject` unchanged since it. 1.
  - Module-qualified statement diff it1 → it2: none removed or changed; 16 added (`K_ok_cats`, the `*_core` order chain, `lpu_window`, `lpu_S1_ord`, `S1_transport_gen/_all`, `positionalJ_of_S1J`, `positionalJ_of_ovl`).
  - Clean rebuild OK; `make -k -j10`: only DCPOs fails.
  - Print Assumptions: 48/48 Closed.
  - `About positionalJ_of_S1J`: arguments `rc K HK VE IT ic Hinv Hq Wu P HWu r0 u0 nuJ` plus the `p_S1J` premise; no validity premise.
  - I read the header in full.
- Confirmation review dispatched (scoped to the it. 2 delta). Snapshot: `SeqLockModuleGen.it2.v`.

## 2026-10-13 — archive of `latest-review.md` (D-1 iteration 1) before overwrite

D-1 it. 1 review: BLOCKER 0, MAJOR 1 (M-17: validity isolation not minimal; `p_S1_ord` needs only `WF_core`, kernel-checked by the reviewer), MINOR m-56, m-57, m-58, m-55. Confirmed: the register spec enters only through validity; 12 of 49 SLM constants carry the witness, and exactly those were copied. Verdict: one short iteration.

## 2026-10-13 — loop D-1 — iteration 2 (confirmation review recorded; loop closed)

- Review: BLOCKER 0, MAJOR 0. M-17, m-56 and m-57 RESOLVED (kernel-confirmed). m-58 resolved, with two cosmetic comment residues.
- Reviewer kernel checks:
  - 12 `core_of_WF` derivations show each `*_core` lemma has exactly the SeqLockCOH statement with `WF_core`;
  - `d2_entry` (scratch, Closed) reduces D-2 to `nuJ []` + `p_S1J`.
- **Verdict: stop the D-1 loop.**
- Orchestrator fixed the two m-58 cosmetic residues itself (comments only):
  - :287 now cites `SeqLockCOH.v:774-810`;
  - :76–78 now reads "No underlay specification that admits a non-SC witness (in particular no buffered or TSO one) satisfies it".
  - Verified: a diff against `it2.v` shows only these comment lines; the module-qualified statement diff is identical; rebuild OK.
- Concern-matrix rows changed: D-1 → ✅ infrastructure (it. 2, loop closed), with the D-2 entry point.
- Plan amendment: D-2 entry point plus the reviewer's S-2 index recommendation.
- Open: m-55 (9.2.0 not built).
- Next: T-1 (SL-tower part 1, the inlined M0 + `M0_shape`). It is independent of F-2. If the author picks ARM option A, `read()` gains a prologue rmb in all SeqLock programs, M0 included.

## 2026-10-13 — loop T-1 — iteration 1 (Writer dispatched)

- HEAD `6e2b575`. The brief is built from plan :495–499 and the prepared `tasks/SL-tower.md` (part 1).
- **Orchestrator Step 1 (verified):**
  - `SeqLockProg`'s `Stores`/`Exec`/`Methods` are fixed to `G := E rc K` (SOp/SL.UC), so they cannot be applied to a new underlay. The Writer either copy-adapts them or factors a generic helper into a new file.
  - SeqLockTower low-level model (`LC`, `LBlk`, `lcalls`, `blk_ok`, `abs`, `lpres`) re-read; `TL.tcalls`, `plainC`/`rcC` re-read.
  - Print Assumptions of `SeqLockProg.M_shape` and `SeqLockTower.tower_link`: Closed.
- **Brief decisions, stated openly:**
  - `M0` is the literal inlining of `SeqLockProg.M`. Waits follow the abstract waits (faa, spins, acq's final inc before wmb, get_ticket, non-silent test_ticket).
  - No prologue rmb: ARM option A is undecided.
  - `M0_shape` also concludes `blk_ok` (needed for `WF0.wf0_blk` in T-3).
  - A non-vacuity derivation is required.
- Brief: `jobs/…/tmp/brief-T-1.1.md`. Checksums: `T1_base.sha`.

## 2026-10-13 — loop T-1 — iteration 1 (Writer done; verification; review dispatched)

- **Writer:** new files `FuturesShape.v` (594 lines, the generic shape machinery adapted from SeqLockProg) and `SeqLockTowerProg.v` (725 lines: `E0`, `M0`, `M0_shape` and corollaries, non-vacuity Examples). `_CoqProject` +2 lines after SeqLockRT.v.
  - The `M0_shape` conclusion has an extra, unrequested conjunct `silent_r0` (canonical r = 0 for silent iterations).
- **Verification (orchestrator):**
  - Protected files: shasum OK (SeqLockProg, SeqLockTower, TicketLockCOH, SeqLockCOH, RelaxedLang/Semantics/ModuleSemantics, SeqLockModuleGen).
  - `git status` delta: only the two new files.
  - Forbidden-construct grep: nothing.
  - Clean rebuild OK; `make -k -j10`: only DCPOs fails.
  - Print Assumptions: 62/62 Closed.
  - I read the header and program (:1–320). The program is the literal inlining (spin/acq waits, rel's inc as f5, silent test_ticket for odd s, no prologue rmb).
  - `E0`'s `mode := fun _ => Local`, the same as `SeqLockProg.E`.
- Review dispatched. Snapshots: `FuturesShape.it1.v`, `SeqLockTowerProg.it1.v`. Report copy: `writer-T-1.1.md`.

## 2026-10-13 — archive of `latest-review.md` (D-1 iteration 2) before overwrite

D-1 it. 2 confirmation review: BLOCKER 0, MAJOR 0; M-17, m-56 and m-57 resolved and kernel-confirmed; m-58 resolved with two cosmetic residues (fixed by the orchestrator, comment-only). `d2_entry` (scratch, Closed) reduces D-2 to `nuJ []` + `p_S1J`. Verdict: stop the D-1 loop.

## 2026-10-13 — loop T-1 — iteration 1 (review recorded)

- Review: BLOCKER 0. MAJOR 1: M-18, research-level. MINOR m-59..m-64, all actionable.
- Verdict: T-1 does what it should (`M0` literal; `M0_shape` correct and universal; `FuturesShape` faithful). Continue after the minor fixes, but the author settles M-18 before T-2/T-3.
- **M-18 (escalated to author):** the author's uncommitted paper edits (async-ccal, 2026-10-13 16:58) change three things.
  - overview.tex: Fig. SeqLock and the SeqLock "Compositionality" text are removed. `prop:vertical-composition` is now illustrated by LatchSet → WriteSnapshot (fig:latech-set).
  - intro.tex: claims "We verify LatchSet … and an interval-linearizable [write-snapshot]".
  - trace.tex: drops the handle-name component of relaxed signatures, and adds `{flush, ok}` events to M_E.
  - SeqLock remains only at trace.tex:263 (dangling "SeqLock case study"), trace.tex:393–395 (the refuted signature) and Appendix/SeqLock.tex (TR).
  - No Coq exists for LatchSet or WriteSnapshot.
  - The orchestrator read the paper diff read-only.
- Orchestrator's dependency note: T-2/T-3 are L-sized and also wait on F-2 (ARM decision). So M-18 blocks nothing the loop could do now. All remaining plan items wait on the author.
- Concern-matrix rows changed:
  - T-1 (reviewed);
  - "Vertical composition" (M-18 note);
  - C1 (trace.tex:393–395 still prints the refuted signature).
- Iteration 2 sent to the same Writer (m-59..m-64; optional `parse0`).

## 2026-10-13 — author decisions (after M-18 escalation)

- AskUserQuestion, two rounds. The author answered:
  - Priority: **LatchSet first**.
  - ARM: **C (x86-TSO only)**.
  - Flush events: **not yet**.
  - LatchSet: **the checker's sorted-array design**, **single-writer discipline**, **LatchSet only for now** (WriteSnapshot paper-level; the paper must not claim it mechanized).
- Recorded in research-intent §8 and the M-15 matrix row.
- Consequences:
  - F-2 is unfrozen under C, but deprioritized behind LatchSet.
  - T-2/T-3 are deprioritized; M-18 is resolved by this decision.

## 2026-10-13 — loop T-1 — iteration 2 (Writer done; verification; confirmation review dispatched)

- **Writer:** m-59..m-64 FIXED, plus item 4 (`parse0`, `decode0`, `M0_shape_decoded`, window-index lemmas).
  - One sub-point of m-59 DISPUTED: whether the paper inlines the Counter.
- **Dispute settled by evidence** (orchestrator): Appendix/SeqLock.tex:7 reads `import owner : Counter`, so the Counter is an object in the paper too. The Writer is right; the reviewer's sub-claim was wrong.
- **Verification:**
  - Protected files: shasum OK. `_CoqProject` unchanged since it. 1.
  - Statement diff it1 → it2: none removed or changed (Example conjuncts are allowed and not tracked by the extractor); 27 added.
  - Clean rebuild OK; `make -k -j10`: only DCPOs fails.
  - Print Assumptions: 85/85 Closed.
- Confirmation review dispatched (background).

## 2026-10-13 — archive of `latest-review.md` (T-1 iteration 1) before overwrite

T-1 it. 1 review:
- BLOCKER 0.
- MAJOR: M-18, research-level (the paper's vertical-composition target moved to LatchSet → WriteSnapshot); resolved by the author's priority decision.
- MINOR: m-59..m-64.
- Verdict: T-1 correct (literal M0, universal `M0_shape`, faithful `FuturesShape`); continue after the minor fixes.

## 2026-10-13 — loop T-1 — iteration 2 (confirmation review recorded; loop closed)

- Review: BLOCKER 0, MAJOR 0. m-59..m-64 closed. The m-59 dispute was accepted by the reviewer: the paper keeps the Counter as an object.
- New m-65 (wording): "refuted" needs the COH-with-barriers/X_lb qualification. The orchestrator fixed it itself; comment only, statement diff identical, rebuild OK.
- **Verdict: stop the T-1 loop.**
- Concern-matrix row changed: T-1 → ✅ infrastructure (it. 2, loop closed); T-2/T-3 deprioritized by the author.
- Next: LatchSet. A plan draft is at `.rocq-review/latchset-plan.md` (v0, unreviewed). A design review comes before any Writer task. The main risk is R1 (writer store forwarding under buffered cells).

## 2026-10-13 — LatchSet plan v0: design review recorded

- The reviewer's design review is summarized in `.rocq-review/latchset-design-review.md`.
- **BLOCKER B-5** (research-level, author-gated): the atomic ν_Set over buffered cells is refuted.
  - CE1/CE2 underlay traces in V_{I_tab} (Closed, scratch).
  - CE1 overlay ∉ rel_lin(ν_Set) for every I (eq_rect_eq, scratch).
  - Cause: insert ends with plain stores and has no draining operation (the Q6-2 obstruction lifted to the overlay).
  - Options: (a) ν_BS buffered set (recommended), (b) a draining op (code change), (c) register cells, (d) withdraw.
- MAJOR M-19..M-24:
  - wrong route (use a direct buffered proof);
  - P1 refinement;
  - categories (insert ↦ Wmb, contains ↦ DR, no Rmb export);
  - precision is model-relative under option C (the five variants are x86-correct);
  - hand-written tags;
  - dependency corrections.
- MINOR m-66..m-70.
- Next:
  - get the reviewer's scratch scripts → LS-0a evidence Writer (design-independent);
  - escalate B-5 + M-20 + M-21 + M-22 to the author.

## 2026-10-13 — author decisions on LatchSet (B-5 etc.)

- Spec: ν_BS. ARM: the author wants LatchSet over ARMv8, which overrides option C for LatchSet. P1 = designated writer. contains ↦ DR.
- The design reviewer terminated on an API error before returning its scratch scripts. LS-0a will be rebuilt from `latchset-design-review.md`.

## 2026-10-13 — loop LS-0a — iteration 1 (Writer dispatched)

- Brief: `jobs/…/tmp/brief-LS-0a.1.md`, the evidence-only file `LatchSetRT.v` (CE1/CE2 in V_{I_tab}, TSO trace, ν_Set refuted for every I, controls).
- It is design-independent, so it does not presuppose ν_BS details.
- Baseline: shasum of all `.v` files under memory/, examples/ and models/ (`LS0a_base.sha`).

## 2026-10-13 — loop LS-0a — iteration 1 (Writer done; orchestrator verification)

- **Writer:** `examples/Relaxed/LatchSetRT.v` (811 lines, 46 results); `_CoqProject` +1 line at the end. No existing file changed: shasum over 177 `.v` files OK.
- **Verification:**
  - Clean rebuild OK.
  - Print Assumptions: 46/46 **Closed** (not even classic or eq_rect_eq).
  - No forbidden constructs; `vm_compute` appears only in comments.
  - `Check`/`Print` confirm the statements:
    - `ce1_overlay_not_rel_lin : forall indep, ~ rel_lin Some (ce1_ov indep false) indep (nuset indep)`, where `ce1_ov` = T1 Inv/Res `Ins 2`, then T3 Inv/Res `Mem 2 = b`;
    - `ce1_cells_V_any : forall Ir, V Ir ce1_cells` (FIFO flushes, so no table can exclude it);
    - `ce1_underlay_allowed rc` (nu, presents, respects po);
    - `ce1_x86 : TSO.Tr … ce1_x86_run`;
    - the general lemma `rt_ins_mem_false_not_rel_lin`.
  - The `ins2` and `other_contains` traces are as designed (LD-0 (a′)).
- **K/S gap (Writer, confirmed):** the module step (M_L producing `ce1_ov` from `ce1_hist`) is a derivation until LS-2/LS-6.
- **Writer's NEEDS-AUTHOR note:** write-snapshot over buffered LatchSets admits SB-style incomparable snapshots (derivation, unchecked).
- No reviewer round yet. It is folded into the claim-coverage workflow (wf_a636f32c-70f), which reads LatchSetRT.v.
- **New author instruction (2026-10-13):** "for LatchSet you must support all claims in the overview". The claim-coverage workflow was launched to map every claim to Coq obligations.

## 2026-10-13 — LatchSet claim-coverage workflow (wf_a636f32c-70f) recorded

- **Workflow:** 12 agents (3 extractors, 4 cluster mappers, 4 adversarial verifiers, 1 synthesizer), all done, 0 errors. 202 claims extracted from overview.tex, intro.tex and the formal sections (161 LatchSet-relevant). The verbatim synthesis is in `.rocq-review/latchset-claim-coverage.md`.
- **Headline:**
  - The atomic-set claim (ov:316/333/335) is refuted as written for the unfenced code (K: LatchSetRT).
  - Adding one trailing `smp_mb` (x86 MFENCE or locked RMW; ARMv8 DMB ISH) plus the exports insert ↦ DRFence and contains ↦ DR makes most claims mutually consistent. ν_BS must then be withdrawn as the export.
- **Refuted as written, beyond A1:**
  - write-snapshot over buffered LatchSets (Ks sb_ws_*);
  - Def. 5.8 compatibility for any non-degenerate design (K `bracketed_not_compatible`; Ks);
  - "soundness w.r.t. RC11" (K Litmus LB/ISA2);
  - the printed view compatibility (K `counterexample_I11`).
- **Refuted by derivation:**
  - LB through two LatchSets;
  - "LB in the layered case study" (in:106);
  - the wait/control wording at ov:23 and in:28;
  - "disjoint underlays" (shared ghosts).
- **New theory needed:**
  - drain primitive (M);
  - hidden-LP `Positional` extension (M, risk L);
  - `rel_lin_ev` interval target (M);
  - write-snapshot module theorem (L);
  - relaxed vertical composition (XL);
  - pending operations (M–L);
  - observational refinement (research);
  - ARMv8 grounding (research);
  - mechanized RLHL (research).
- **18 author decisions** are listed in §4 of the coverage file; the critical ones are 1 (atomic + drain vs ν_BS), 7 (WS mechanization), 10 (ARMv8 depth) and the §3.7 rewordings.
- **Scratch-only (Ks) results to commit before the paper cites them:**
  - `sb_ws_*`;
  - `tso_not_compatible`, `arm4_compatible`, `wf_forces_local`, `only_local`;
  - `latch_exports_not_rect`, `latch_drain_exports_rect`;
  - `md_false`/`md_true`.

## 2026-10-13 — author decisions on the claim coverage

- Atomic set + trailing smp_mb (ν_BS withdrawn); full chain for write-snapshot and vertical composition; ARMv8 litmus now, grounding later; all §3.7 rewordings approved.
- Orchestrator defaults for the remaining decisions are recorded in research-intent §8.
- The plan is now v2 (`latchset-plan.md` §6). Wave 1 (E-0, MD-1, LS-2, WS-1, A-1) is next.

