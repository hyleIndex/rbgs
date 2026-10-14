# Concern matrix: reviewer concerns and paper claims vs. the Rocq development

Baseline: 2026-10-13, iteration 0 (an orchestrator audit, not yet confirmed by `rocq-research-reviewer`).
- Repository: rbgs `relaxed-lin` at `dcccce0`, plus 19 uncommitted files (`models/view/*`, `models/simlin/{RelaxedGSim,RelaxedStamping,AtomicLTS}.v`, `examples/View/ViewLift*.v`, `EBStackViewLift.v`, and changes to `_CoqProject`, `EBStackTSO.v` and `examples/Common/AtomicLTS.v`).
- Build check: a clean Rocq 9.2.0 / Stdlib 9.2.0 build in a cloud container, with the uncommitted files overlaid. 171/171 files compile; `make -j2` took 251 s.

Status legend:
- ✅ K, S, P and R agree.
- 🟡 Partial: the gap is named.
- ❌ Missing.
- ⚠️ The paper text contradicts the Coq development or the author response.
- 📝 Paper-only: no Coq needed.

Columns: **K** = kernel-checked; **S** = what the statement says; **P** = what the paper claims; **R** = what the reviewer requires.

Reviewer quotes are in `popl2027-reviews.md`. IDs follow the author response numbering where one exists; `A-L<n>` refers to a line comment by Reviewer A.

## 1. Meta-review concerns

| ID | Concern (meta-review) | Status | Where it is handled |
|---|---|---|---|
| Meta-1 | "scope of the supported memory models (e.g., the restriction to multicopy-atomic models and the handling of store forwarding)" | ⚠️ | A1, A2 |
| Meta-2 | "insufficient justification of the correspondence with existing memory models" | 🟡 | B1, B2, A20 |
| Meta-3 | "lack of a demonstration of client verification" | ❌ | B4 |
| Meta-4 | "incomplete mechanization (with many admitted lemmas) insufficient to establish confidence" | 🟡 admits are gone; ❌ the end-to-end chain is missing | A3, B3 |

## 2. Reviewer concerns

| ID | Concern | K / S (Coq) | P (paper now) | Status | Next action |
|---|---|---|---|---|---|
| A1, A-L647, A18 | MCA scope; IRIW does not show non-MCA | Nothing in Coq on non-MCA models. The buffered cell (`memory/Cell.v`) is an OMCA model. Only the Python checker (`litmus-check/run_power.log`) forbids IRIW+addrs and WRC+addrs on COH/RA/TSO. | intro.tex:119, the "Scope" paragraph, is unchanged. trace.tex:225 still says "our COH model is not MCA" via IRIW. The response says "restrict our scope to MCA, not oMCA", while Mem.tex is OMCA. | ⚠️ | Decide Q2 (research-intent §7). Rewrite Scope. Cheap Coq: IRIW+addrs and WRC+addrs forbidden for the buffered instances (Litmus.v style). |
| A2 | Store forwarding; the SB variant with own reads | `TSO.tso_traces` (closed): erase(V↑_TSO) = x86-TSO machine traces, read/write fragment, flush labels visible. `Equivalence.declarative_TSO` (`classic`). Forwarding read in `Cell.v`. **No concrete theorem** puts the reviewer's outcome in ν_TSO. `ViewLiftOMCA.n6_mp_inseparable` and `tso_no_n6`: the view-TSO used by the case studies cannot produce n6 while forbidding MP. | trace.tex:262 `rem:ra-tso` ("RA and TSO coincide") is still printed. The main-text cells are pure reordering. Mem.tex:5 already says the remark is inexact. | ⚠️ | Coq lemma: SB-own-reads and n6 ∈ ν_TSO(buffered). Delete `rem:ra-tso`. D6: rename or redo the "TSO" cells of SeqLock/exchanger. |
| A3, Meta-4 | Map paper definitions to Rocq; admitted lemmas | No `Admitted`/`admit`. `Print Assumptions` of 109 key theorems ⊆ {`eq_rect_eq`, `classic`, `Parameter A : Type` in ExchangerTSO/TryStackTSO/EBStackTSO}. `rocqchk` crashes on `models/Sets.v`. `vm_compute` is used in SeqLockCOH, TicketLockCOH, SeqLockTower, SeqLockRT, WindowTable, IntervalWindow. | No mapping table. implex.tex §6.3 and intro.tex:113 describe the Coq inaccurately (see B7). | 🟡 | Commit the uncommitted files. Build a paper→Coq table (§3 below). Make `A` a section variable. |
| A7 | rf/mo/rb must not contradict po | `memory/Declarative.v` D1 (per-location coherence) and D2. Not audited against the main-text claim. | Response: acyclicity of the union. | 📝 / not audited | Reviewer to check D1 against the response wording. |
| A8 | Def 2.1 is wrong (missing different-thread condition) | `RelaxedTraceLin.rhb` (two disjuncts: real-time order, or same-thread overlapping and not independent) | overview.tex `def:relaxed-hb` not yet rewritten | 📝 | Rewrite following `RelaxedTraceLin.rhb`. |
| A-L445 (A10/A11 in the response) | Fence agreement in both directions; compatibility | Example level, closed: `BracketedComposition.bracketed_not_compatible` (old Def. 5.8 is unsatisfiable), `WindowComposition.window_composition`, `Necessity.fence_claim_fails`, `WindowLink.window_link`, `WindowTable.window_composition`, `wc_is_special_case`. **No general horizontal-composition theorem in `models/`.** | relaxedlin.tex:126 Def. Compatibility and :143 Prop. Horizontal Composition are still the old ones. | ⚠️ paper / 🟡 Coq | Replace Def. 5.8 by window inheritance (todo C4). Lift WindowLink into a general module-tensor theorem (M-2). |
| A12, A15, B10 | Handles | `RelaxedSignature.Tens` requires `handle E = handle F`: a shared namespace, keys (thread, handle) (RelaxedSignature.v:125–138). | Paper and response A12: disjoint union 𝒜_E + 𝒜_F. | ⚠️ | Align the paper with Coq (todo C3), or justify. |
| A20, A-L671 | Which MCA axiom; "sound w.r.t. RA" direction | `Equivalence.declarative_characterization` (`classic`): buffered cell ⟺ its own OMCA axioms D1 ∧ D2 under `pre`. **Main-text RA/COH instances: no theorem.** | trace.tex:255–258 is unchanged ("the proof is direct"; "this is straightforward"). | ⚠️ | Replace with Thm `mem:thm:decl` and its Coq name, or drop the claim. |
| A21, A-L786 | Return discharges dependencies; inlining | Enforced: `RelaxedSemantics` `program_terminal` needs `all_resolved` (:252); `RelaxedModuleSemantics` Ret needs `owner_done` (:401/:605). Inlining is not formalized. Hypothesis (W) `dep;po? ⊆ rhb_s` is an undischarged `Hypothesis` in ARM.v:78–79 and ARMDecl.v:398–399. | Response A21 promises a qualification of inlining. | 🟡 | Write it as a stated assumption. Optionally prove (W) for compiled programs (todo E3). |
| A22, C7 | Smith et al.; RELINCHE; Mowgli | — | related work | 📝 | todo R1–R3 |
| B1 | Reordering justification; weak-memory hb; RC11 correspondence | `RC11.v` defines `sw` and `rchb = (po ∪ sw)⁺`. `rc11_containment` (`classic`): D1 ∧ D2 ⇒ RC11 COHERENCE. ATOMICITY and SC are vacuous on the fragment; NO-THIN-AIR is **not** implied. `Litmus.LB.ours_allow` / `LB.rc11_forbid`, `ISA2.ours_forbid` / `ISA2.rc11_allow`: the models are **incomparable**. Fragment: reads and writes only, rlx/rel/acq, no RMW/CAS/fences. | Main text has no hb; Mem.tex §L.7 (TR only) has the comparison. | 🟡 | State the incomparability honestly in the main text. Say that "soundness against RC11" in reviewer B's sense **cannot** hold for this fragment (Q2). |
| B2 | "agree" has no theorem; RC correspondence not proved | COH and RA (main text): **no Coq theorem**. RC (buffered): ⊆ RC11-COHERENCE only. ARMv8: `ARM.arm_containment` needs (W) and gives only ours + S ⊆ ARM. `ARMDecl.arm_declarative` is pure relation algebra, and the buffered cell does not realize it. | intro.tex:112 claims "our COH instance is equivalent…, RA … equivalent under MCA". | ❌ / ⚠️ | Either mechanize COH ⟺ per-location SC (cheap: all-rlx with `pre0` reduces to D1) or drop the claim. |
| B3, B-post | Mechanized chain: logic + soundness vs. a weak memory model + object + client | (i) **RLHL rules → MethodSem → GSimRel → rel_lin (complete) and → copy-cat inclusion RCompLin (all executions)** (updated 2026-10-13, RLHL-3a iter 1, uncommitted). `rlhl_gsim` (closed) → `rlhl_rel_lin`/`rlhl_sound` (`eq_rect_eq`; complete traces) and `RelaxedHoareCompLin.gsim_complin`/`rlhl_complin`/`rlhl_complin_ei` (`classic`; every execution, CompLin-style copy-cat inclusion over the derivation's VE; `reify` closed). Instance: `counter_complin` (I=∅, over HVE); `junkF_not_rtrace` (closed). Missing: absorption/linking (M-22), EIhl/HLift (m-20; T1 refutes plain EI), item 5 RTraces(EI)↔rel_lin (M-20), nonempty-SI instance (M-19), client, memory VE. (ii) **Semantic simulation ⇒ rel_lin: proved** — `RelaxedGSim.gsim_rel_lin` (`eq_rect_eq`), for complete executions only (all `DeadCall`), assuming the spec traces of `VF` are rel_lin. `ViewLHL.presentation_choice` / `vlhl_sound`: if the underlay `implements νE`, then complete overlay traces are rel_lin. Never instantiated. (iii) **Memory ↔ underlay: missing**: no file outside `memory/` imports `memory.*`. (iv) **Object and client via the logic: missing.** | intro.tex:113, programlogic.tex Prop. Logic Soundness (`prop:rlhl-sc`, implex.tex:170, is a VLHL claim: see B7/B8 and §3). Response B3 concedes this. | ❌ (sub-item (i) 🟡) | RLHL-3a iter 2 (item 5, EIhl/HLift, corollaries); RLHL-3b (nonempty SI); RLHL-3c (absorption, linking, composition, client); memory route. Then logic ⇒ GSimRel, `implements ν_Mem` for a memory LTS, and one object plus client end to end. See §5. |
| B4 | Client verification | `LockedRegistersWindow.sb_forbidden_window` (closed): module level, but overlay I = ∅, the underlay is assumed rel_lin, and non-vacuity uses the trivial `VE0` (`Step := True`, LockedRegisters.v:703). `SeqLockCOH.mp_forbidden`: witness level. **No SeqLock a=b client.** No client of an object with nonempty overlay I. | Response B4 promises SeqLock a=b. | ❌ | Lock(O) ⊗ plain cell (todo M3) or SeqLock a=b, at module level. |
| B5 | No example on COH | `SeqLockModule.seqlock_module_rel_lin` (closed) is module level, via `window_link_table`, not RLHL. It covers a **modified** SeqLock with rmb/wmb over abstract per-location registers plus an ordering table (not `memory/Cell.v`). The underlay is assumed rel_lin. Non-vacuity is one write by one thread on `VE0`. `TicketLockCOH` and `SeqLockTower` are witness level. | Paper SeqLock uses "TSO" cells. | 🟡 | Make the COH SeqLock the paper's example, or explain the change. Add a concurrent non-vacuity witness. |
| B6, C2 | Weak HW queue `enq(1); deq()`; how I is chosen | **No queue in Coq** (only a toy enq/deq signature in `models/Signature.v`). | trace.tex:92 still `deq : N + {⊥}`. The appendix code loops. intro.tex:113 says "we also specify and verify the weak Herlihy-Wing queue". | ❌ / ⚠️ | Q5: keep it (mechanize with a blocking deq) or drop the claim. |
| B7, B8 | Views and rules unclear | `PrefixView.counterexample_I11`: printed Thm I.11 is **false** without real time. `reg_not_compat_printed` / `sc_reg_not_compat_printed`: printed Def. I.1 fails even for an SC register. `ViewLHL.vt0_not_sound`. Fixes: `thm_I11_rt`, `vlhl_sound` (real time), `ViewPossibility.timeline_rel_lin` (no compatibility needed). | implex.tex `def:view-compatible-main`, `prop:rlhl-sc` and Appendix/viewbased.tex print the refuted versions. §6.3 describes VLHL possibilities with timestamps, but the Coq proofs are SC LHL over view LTSs (README: "Possibility states carry no timestamps"). | ⚠️ | Rewrite §6 from PrefixView / ViewPossibility / ViewLHL. Correct the §6.3 description. |
| B9, C6 | Background terms; "TR" | — | — | 📝 | todo P2 |
| C1 | The spec should be memory-model agnostic; I looks implementation-specific | Derived modes: `window_link`, `WindowTable`. `SeqLockCOH.paper_signature_fails` / `paper_modes_fail`: the printed SeqLock signature is refuted for the COH barrier variant. `four_modes_force_local`, `torn_with_local_tl`: the 4-mode lattice is too coarse. | Response C1 | 🟡 | A running example that shows the derivation (todo P3). Decide D3. |
| C3 | Conditional po-forgetting | `RelaxedSig.semi_independent` is a static relation on operations, including their arguments. | Response C3 | 📝 | — |
| C4 | Novelty | Compositionality evidence, closed: `fence_claim_fails`, `bracketed_not_compatible`, `window_composition`, `wc_is_special_case`, `wmb_not_rectangular`. | related work not rewritten | 🟡 | todo R1–R4 |
| C5 | Effort of developing relaxed specs | Lock(O) ⊗ plain cell (nonempty overlay I) not started. LockedRegisters has I = ∅. | — | ❌ | todo M3 |

## 3. Paper result → Coq

| Paper item | Coq | Status |
|---|---|---|
| Relaxed effect signature, fence modes, tensor | `models/RelaxedSignature.v` (`RelaxedSig.t`, `fence_le`, `Tens`) | Defined; the handles differ from the paper (A12) |
| Def 2.1 rhb, `def:rlxlin-po` | `RelaxedTraceLin.rhb`, `rel_lin` | Defined for **complete traces only** |
| `prop:sanity-check`, `prop:rhb-equiv` | none (`RelaxedStamping.rel_lin_iff_rhb_stamping` is a restatement) | ❌ |
| Imp, compilation to futures, `depof` | none: shallow `RelaxedLang.Prog`; dependency tags hand-written (`FutureD deps`) | ❌ |
| Module semantics (positional / tagged frontier) | `RelaxedModuleSemantics.module_step`, `module_step_tagged`; `positional_traces_are_tagged_traces` | ✅ |
| Lem. wsc-dep, wsc-indep | `module_dependency_soundness` (first half only), `select_frontier_tagged_split` | 🟡 |
| RLHL rules | `RelaxedHoare` `rp_*`, `Close`, `cprov_*` (sound w.r.t. `MethodSem`); old `RelaxedLogic.provable_*`, `RelaxedTaggedLogic.tprovable_*` superseded | 🟡 connected (`rlhl2_of_provable` + `rlhl_gsim` + `rlhl_rel_lin`); end to end only for the I=∅ counter over HVE (M-19); no concurrent own-event OG instance with proved HVF (M-11); loop rule `rp_dowhile`/`cprov_dowhile`; overlays well-formed |
| RLHL as conservative extension of LHL (intro.tex:113, relatedwork.tex:34, research-intent §8) | `RelaxedHoare.cprov_call`, `MethodProvableChain` | 🟡 rule-level only (call, seq, do-while in the blocking fragment); error premises dropped; Pinv/Ginv difference; no translation theorem (M-14, now MINOR) |
| implex.tex:3: rely admits own futures; RLHL complete; load buffering | own events checked pairwise (`ns_if_*`, `bw_if`), rely reading only via `newslot_guar_in_rely`; no completeness; no LB example | ⚠️ unsupported (M-15) |
| Intra-thread cross-call ordering in RLHL (intro.tex:94, programlogic.tex:286) | ghost thread frontier; used end to end over HVE (`inc_ooo_exec`); agrees with programlogic.tex:286 modulo `hb_s` (m-15) | 🟡 |
| intro.tex:105 (working tree) memory correspondence: ARMv8 equivalence, RC11 soundness, "mechanized" | refuted for RC11 in both directions (`Litmus.LB`, `ISA2`); no ARMv8 instance of the cell (`arm_containment` one direction under (W)); SB/RSW incomparability | ⚠️/❌ (latest-review B-4; author) |
| RLHL layering / `implements` from RLHL | no theorem produces `implements`; the Q3 premise ("every VF path is an rl_prefix") is refuted for VT (`vt_not_implements`; review scratch S1-S3, reproduced); VE := VT nuE is infeasible for prefix soundness; needs the M-20 prefix notion plus a dead-end-free presentation (VTc, RP or VT′) and a premise for pending `ls_inv` calls; `rlhl_prefix_run` (= `rlhl_gsim ∘ rinv_exec`) not yet exported | 🟡 copy-cat prefix soundness exists (`gsim_complin`); `implements` route superseded for RLHL; composition missing (M-22) |
| Prefix notion for incomplete traces | Coq `rl_prefix` (K: all pending calls complete) vs relaxedlin.tex:29/:33 (REW: drop sets closed under same-thread non-independent successors) vs viewbased.tex:35 (V: drop any pending); `junk` separates them; prop:rhb-equiv unproved for incomplete traces | 🟡 decided: copy-cat over EI (author); data points `junkF_not_rtrace`, T2; REW / rel_lin agreement argued (M-20) |
| Paper rule figures (programlogic.tex:512-543) ↔ mechanized rules | not mapped; own-event premise commented out at :516; Choice has no counterpart | ⚠️ (M-21) |
| End-to-end RLHL instance with nonempty SI and a relaxation witness | none | ❌ actionable (M-19) |
| Universal negatives via soundness | `bad_counter_no_rlhl2` (`eq_rect_eq`) and `counter_vt_no_rlhl2` (closed) in the repository; `read_pair` still relative | 🟡 (m-24) |
| Underlay-key freshness in the RLHL triple | author option: handle-linear VE (instance-level; triple unchanged); no theorem consumes HL; WLOG `HLift` lemma missing (m-20); presentation dependence undocumented | 🟡 |
| Spec style and HVF for same-thread order | `ei_hvf` closed and exact; EI infeasible over `VT nuE` (M-18); candidate overlay `VT nuF` (`vt_sound`) | 🟡 research-level |
| End-to-end RLHL route: overlay spec style × complete underlay presentation | EI × VT admits no `GSimRel` for ordered same-thread ops (M-18, prose + `vt_junk`); author 2026-10-13: stamp-based overlay `VT nuF` | ❌ (decided; RLHL-3 to implement) |
| HL presentations WLOG | `HLift VE` lemma missing | ❌ actionable (m-20) |
| Single possibility vs the paper's possibility sets (relaxedlin.tex:520/:628) | single `Poss VF` | 🟡 author decision |
| intro.tex:7, :99, :106 and overview.tex:318, :331 (working tree; formerly :115) attribute latch / write-snapshot case studies and layered verification to RLHL | no RLHL instance of either; latch only on the window route | ⚠️ (M-15); author 2026-10-13: plan an RLHL latched-set instance after RLHL-3 (queue item `RLHL-latch`) |
| relatedwork.tex:32 "sound and complete" / load buffering | no completeness; no LB example | ⚠️ unsupported (M-15) |
| Appendix/relaxedlin.tex:518/:626: R_π only for independent operations | Coq `R k` must cover non-independent same-thread calls | 📝 paper (M-15) |
| Underlay errors / partial correctness | no error clause in `module_step_tagged`/`gsim_step`/`MethodSem` | 📝 scope statement (m-8) |
| Prop. Logic Soundness (programlogic.tex:498) | `RelaxedHoareGSim.rlhl_sound` (`rlhl_rel_lin ∘ rlhl2_of_provable`; premise table vs `RGILogic.soundness` in the GSim header); complete traces, over VE; no thread-local `∼^t` | 🟡 paper text to rewrite (M-15) |
| Simulation, Soundness (App. relaxedlin.tex:634/665) | `RelaxedRGISimulation`, `TRGISimulation` (unused); `RelaxedGSim.gsim_rel_lin` (a different, all-universal simulation) | 🟡 |
| Completeness, Parallel Composition (App. relaxedlin.tex:669/709) | none | ❌ |
| Thm I.9 + I.11 (VLHL semantic), Prop. I.10 | `ViewLHL.presentation_choice`, `vlhl_sound`; `PrefixView.rel_lin_view_rt` | ✅ with the real-time fix; never instantiated |
| `prop:rlhl-sc` (implex.tex:170; a VLHL claim, implex.tex:114), Prop. vlhl-logic-soundness | none; Coq candidate is `ViewLHL.vlhl_sound`/`presentation_choice` | ❌ |
| Vertical composition / observational refinement | none in `models/`; `SeqLockTower.tower_link` is SeqLock-specific, witness level | ❌ |
| Horizontal composition / compatibility | `WindowLink.window_link`, `WindowLinkTable.window_link_table`, `BracketedLink.bracketed_link` (module level, hypotheses `positional` / `local_correct`, underlay assumed rel_lin) | 🟡 |
| Mem.tex Thm `mem:thm:decl` | `Equivalence.declarative_characterization` (+ `extraction`, `realization`) | ✅ (TR only) |
| Mem.tex x86-TSO | `TSO.tso_traces` | ✅ read/write fragment |
| Mem.tex RC11 / ARM comparison, litmus | `RC11.rc11_containment`, `ARM.arm_containment`, `ARMDecl.*`, `Litmus.*` (5 tests: LB, ISA2, SB, RSW, MP) | 🟡: 6 of the 11 table rows are not mechanized; herd7 not run |
| Mem.tex Cor. `mem:cor:rlxlin` | none (undefined in the text too) | ❌ |
| SeqLock (App.), exchanger, EB stack (§6.3) | `examples/View/{SeqLockTSO,ExchangerTSO,EBStackTSO}.v`: SC `RGILogic` over view LTSs, blocking code; CAS/Mem views collapse to SC (`cas_tso_to_sc`) | 🟡 not VLHL as described |
| Counter_xy, weak HW queue | none | ❌ |

## 4. Key theorems: baseline assumptions (2026-10-13)

Regression check: after every Writer iteration, these must not gain assumptions. Names are fully qualified.

- **No axioms (closed):** all of `examples.Relaxed.*` listed below, `RelaxedLogic.*`, `RelaxedTaggedLogic.tmethod_provable_trace_sound`, `RelaxedModuleSemantics.module_dependency_soundness`, `RelaxedStamping.rel_lin_iff_rhb_stamping`, `TSO.tso_traces`, `Litmus.{ISA2.rc11_allow, SB.arm_forbid, RSW.arm_allow}`, `ViewLHL.vt_sound`, `UnderlayRefinement.*`, `ViewLiftAdequacy.{run_rel_lin, canon_*}`.
- **`eq_rect_eq` only:** `RelaxedGSim.{gsim_rel_lin, GSim_rel_lin, transfer}`, `ViewLHL.{vlhl_sound, presentation_choice, vt_complete, vt0_complete, vt0_not_sound}`, most of `PrefixView`, `ViewPossibility`, `ViewLift`, `ViewLiftTensor`, `ViewLiftCAS`, `ViewLiftMem`.
- **`classic`:** `Equivalence.*`, `RC11.rc11_containment`, `ARMDecl.arm_declarative`, `Litmus.{*.ours_*, LB.rc11_forbid, MP.*}`.
- **`eq_rect_eq` + `classic`:** `SeqLockTSO.SeqLockImpl.Mseqlock`, `ViewLiftSeqLock.Mseqlock_vl`, `PaperTheorems.framed_logic_soundness_CompLin`.
- **`eq_rect_eq` + `classic` + `Parameter A : Type`:** `ExchangerTSO.ExchangerImpl.Mexchanger`, `TryStackTSO.TryStackTSOImpl.Mtrystack`, `EBStackTSO.EBStackTSOImpl.*`, `EBStackViewLift.components_correct_sc`.

```
examples.Relaxed.BracketedComposition.BracketedComposition.bracketed_not_compatible
examples.Relaxed.LockedRegistersWindow.LockedRegistersWindow.window_hypotheses_satisfiable
examples.Relaxed.LockedRegistersWindow.LockedRegistersWindow.sb_forbidden_window
examples.Relaxed.SeqLockCOH.SeqLockCOH.seqlock_z_composition
examples.Relaxed.SeqLockCOH.SeqLockCOH.paper_modes_fail
examples.Relaxed.SeqLockModule.SeqLockModule.seqlock_module_rel_lin
examples.Relaxed.SeqLockTower.SeqLockTower.tower_composition
examples.Relaxed.TicketLockCOH.TicketLockCOH.ticketlock_S1_all
examples.Relaxed.WindowComposition.WindowComposition.window_composition
examples.Relaxed.WindowComposition.WindowComposition.Necessity.fence_claim_fails
examples.Relaxed.WindowLink.WindowLink.window_link
examples.View.EBStackTSO.EBStackTSOImpl.components_correct
examples.View.EBStackViewLift.EBStackViewLift.components_correct_sc
examples.View.ExchangerTSO.ExchangerImpl.Mexchanger
examples.View.SeqLockTSO.SeqLockImpl.Mseqlock
examples.View.TryStackTSO.TryStackTSOImpl.Mtrystack
examples.View.ViewLiftCAS.ViewLiftCAS.cas_tso_to_sc
examples.View.ViewLiftOMCA.ViewLiftOMCA.no_lb
examples.View.ViewLiftOMCA.ViewLiftOMCA.n6_mp_inseparable
examples.View.ViewLiftOMCA.ViewLiftOMCA.lb_rel_lin
examples.View.ViewLiftSeqLock.ViewLiftSeqLock.Mseqlock_vl
examples.View.ViewLiftSeqLock.ViewLiftSeqLock.stale_rel_lin
memory.ARMDecl.ARMDecl.arm_declarative
memory.Equivalence.Equivalence.declarative_characterization
memory.Equivalence.Equivalence.declarative_TSO
memory.Litmus.Litmus.LB.ours_allow
memory.Litmus.Litmus.LB.rc11_forbid
memory.Litmus.Litmus.ISA2.ours_forbid
memory.Litmus.Litmus.ISA2.rc11_allow
memory.Litmus.Litmus.SB.ours_allow
memory.Litmus.Litmus.SB.arm_forbid
memory.Litmus.Litmus.RSW.ours_forbid
memory.Litmus.Litmus.RSW.arm_allow
memory.RC11.RC11.rc11_containment
memory.TSO.TSO.tso_traces
models.simlin.RelaxedGSim.RelaxedGSim.gsim_rel_lin
models.simlin.RelaxedLogic.RelaxedLogic.method_provable_trace_sound
models.simlin.RelaxedTaggedLogic.RelaxedTaggedLogic.tmethod_provable_trace_sound
models.simlin.RelaxedModuleSemantics.RelaxedModuleSemantics.module_dependency_soundness
models.view.PrefixView.PrefixView.counterexample_I11
models.view.PrefixView.PrefixView.thm_I11_rt
models.view.PrefixView.PrefixView.reg_not_compat_printed
models.view.ViewLHL.ViewLHL.presentation_choice
models.view.ViewLHL.ViewLHL.vlhl_sound
models.view.ViewPossibility.ViewPossibility.timeline_rel_lin
```

Added 2026-10-13 (RLHL-1 iter 1, uncommitted; all closed; the 180 lemmas of the five `RelaxedHoare*` files are closed):

```
models.simlin.RelaxedHoareSound.RelaxedHoareSound.method_sound
models.simlin.RelaxedHoareSound.RelaxedHoareSound.chain_sound
models.simlin.RelaxedHoareDag.RelaxedHoareDag.ctx_triple
models.simlin.RelaxedHoare.RelaxedHoare.cprov_call
models.simlin.RelaxedHoareBase.RelaxedHoareBase.select_project
examples.Relaxed.RelaxedHoareChecks.RelaxedHoareChecks.read_pair_not_rlhl
```

Added 2026-10-13 (RLHL-1 iter 2; all 332 lemmas of the five files closed). Changed statements: `method_sound` (Ω parameter, ghost state), `ctx_triple` (NoOwn premise), `read_pair_not_rlhl` (∀Ω, new I2/R2). New: `Counter.counter_b5`, `methodsem_of_iter1`, `ghost_of_select`, `ghost_of_done`, `ghost_of_schedule`, `retcond_return`, `pair_rlhl2`, `xy_rlhl2`, `pair_discriminates`, `two_calls_init`, `two_calls_step`, `own_reorder_not_one`, `tas_sound`, `await_sound`, `cprov_dowhile`.

Added 2026-10-13 (RLHL-1 iter 3; all 472 lemmas of the six RLHL files closed): `ei_hvf`, `ei_hvf_indep`, `ei_sound_pres`, `vt_handle_linear`, `hl_path_inv_unique`, `poss_invoke_exists`, `pool_dom_steps`, `pool_dom_invoke`, `pool_dom_return`, `lin_fresh_of_dom`, `counter_ow_unsat`, `counter_hl_rlhl2`, `counter_hl_contrast`, `counter_spec_hvf`, `gtwo_init`, `gtwo_step`, `inc_two_blocked`, `tas_not_hvf`, `pair_not_hvf`, `log_rlhl2`, `log_needs_alive`. Restated: `two_calls_reorder` (module configurations), `counter_b5_excluded` (distinct handles), `emit_case` (hypothesis removed).

Added 2026-10-13 (RLHL-2 iter 1; 515 lemmas in the seven RLHL files: 507 closed, 8 `eq_rect_eq`). Closed: `rlhl_gsim`, `rlhl_rsim`, `rsim_gsim`, `rlhl2_of_provable`, `finish_stored_sig`, `owners_active_reachable`, `returned_not_fresh`, `inc_ooo_exec`, `inc_bad_not_rel_lin`, `hve_not_complete`. `eq_rect_eq` only: `rlhl_rel_lin`, `rlhl_rel_lin_pres`, `rlhl_rel_lin_ei`, `rlhl_rel_lin_ei_pres`, `finish_stored_ret`, `counter_rel_lin`, `inc_ooo_rel_lin`, `inc_bad_no_exec`.

Added 2026-10-13 (RLHL-2 iter 2; 535 lemmas: 524 closed, 11 `eq_rect_eq`). Closed: `vt_junk`, `vt_junk_not_rl_prefix`, `vt_not_implements`, `counter_vt_no_rlhl2`, `bad_exec`, `bad_not_rel_lin`. `eq_rect_eq` only: `rlhl_sound`, `counter_rel_lin_by_rules`, `bad_counter_no_rlhl2`. Review scratch (not in the repository, reproduced by the orchestrator): S1 `vt_underlay_no_rl_prefix_overlay` (closed), S2 `vt_overlay_not_rl_prefix` (`eq_rect_eq`), S3 `vtF_not_implements` (closed), RP lemmas `rp_complete`/`rp_implements` (closed), `rp_sound` (`eq_rect_eq`).

## 5. Evidence for "advantage over prior models"

| Claim | Evidence | Level | Status |
|---|---|---|---|
| LB allowed where RC11 forbids it | `Litmus.LB.ours_allow`, `LB.rc11_forbid` | memory, Coq | ✅ |
| OOTA (LB+ctrl/addr/data) forbidden | **none in Coq.** The closest is `DependencyFrontierExamples.dependent_store_waits`. todo-oopsla-v2 marks this ✅, which is an overclaim. | — | ❌ |
| Object-level LB through composition | `SeqLockCOH.lb_allowed`, `lb_refutes` (witness level); `ViewLiftOMCA.lb_rel_lin` (one trace) | object, Coq | 🟡 no module-level concurrent execution |
| Incomparable with RC11 / ARMv8, Δ1–Δ5 | `Litmus` (4 of the decisive tests), `rc11_containment`, `arm_containment` | memory, Coq | 🟡 partial; herd7 not run |
| Locality fails with overlap and is repaired per implementation | `fence_claim_fails`, `window_composition`, `bracketed_not_compatible`, `WindowTable.wc_is_special_case` | composition, Coq | 🟡 example level; the comparison with Mowgli's Def. 3.13 is unverified |
| View specs over SC memory cannot express LB / 2+2W / n6 | `ViewLiftOMCA.no_lb`, `no_2p2w`, `n6_mp_inseparable` | Coq | 🟡 about the paper's own ViewLift construction, not about published prior work |
| Precision: LatchSet (SC linearizability "proves" wrong readers; RC11 logics fail on the correct one) | Python checker only; "LKMM/Arm" labels set by hand; no SC-linearizability or RC11 verdict computed | — | ❌ |
| Real kernel code (perf ring), control dependency | Python checker only | — | ❌ |

## 6. Suggested queue for `/rocq-loop` (authors decide; see research-intent §7–8)

**Author priority (2026-10-13): LatchSet + write snapshot, and SeqLock on COH. Scope = oMCA.** Example-specific items:

- `SL-nonvac`: a concurrent module-level execution of SeqLock ⊎ COH[z] (e.g. the LB execution `X_lb`, or writer ∥ reader) over a non-trivial underlay LTS that satisfies every hypothesis of `seqlock_module_rel_lin` (today: one write, `VE0` with `Step := True`).
- `SL-client`: SeqLock clients at module level from `seqlock_module_rel_lin` + ν_SeqLock: a=b (response B4), MP forbidden, LB allowed.
- `SL-tower`: TicketLock at module level (as `SeqLockProg`/`SeqLockModule`), and the vertical story (general vertical theorem, or the SeqLock-specific `SeqLockTower` stated honestly as witness-level).
- `SL-mem`: connect the abstract cells/barriers used by `SeqLockCOH` (registers + `WindowTable.dto`) to `memory/` (COH instance of the buffered cell + `wmb`/`rmb`, todo E2), or state the gap.
- `LS-spec`: LatchSet + write snapshot: specification (needs the author's definition of "write snapshot"), program with address-dependency tags (`FutureD`), categories.
- `LS-proof`: witness-level S1 ("SC core + F0–F5"), concrete counterexample executions for the broken variants (no dependency / no rmb / missing wmb), module-level link via `window_link_table`, one client. Risk: `SeqLockProg` uses untagged futures only, so the dependency path through the tagged frontier into the witness-level preserved order is not yet exercised.

General queue (unchanged):


1. **Q1, then `B3-logic`**: redesign the RLHL judgement (universal over executions and responses, rely/guarantee stability, per-call debts) and prove that RLHL derivations yield `RelaxedGSim.GSimRel`. Research-level design first. The largest single item.
   - 2026-10-13: Q1 design decided (research-intent §8) and RLHL-1 iteration 1 delivered (`RelaxedHoare*`). Next: the **B-5 decision + semantic-triple redesign** (latest-review B-5), then RLHL-2. RLHL-3 non-vacuity must use well-formed overlays, R/G satisfying the RLHL-2 bundle, interference on locations the call reads, a dag-dependent OG discharge, and a COH or buffered-cell `VE`.
2. **`B3-instance`**: one non-trivial `GSimRel` instance (a concurrent object with weak behaviour, a non-trivial `VE`), so that `gsim_rel_lin` and `presentation_choice` are shown non-vacuous. It can start before item 1.
3. **`B3-memory`**: connect `memory/` to `RelaxedLTS`: erase blocks to `ThreadEvent`, define the buffered-cell LTS, prove `ViewLHL.implements ν_Mem` (i.e. `mem:cor:rlxlin`), including incomplete traces.
4. **`B4-client`**: a client at module level for an object with nonempty overlay I (Lock(O) ⊗ plain cell, or SeqLock a=b).
5. **Cheap closures**: SB-own-reads and n6 ∈ ν_TSO; IRIW+addrs and WRC+addrs forbidden; LB+ctrl forbidden (needs dependency edges); `A` as a section variable; commit the uncommitted files.
6. **`M-incomplete`**: incomplete traces in `RelaxedTraceLin` and `gsim_rel_lin`. This is a prerequisite for vertical composition.
7. **Q5**: weak HW queue, either mechanized with a blocking deq or the claim dropped.
