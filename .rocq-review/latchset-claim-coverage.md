# LatchSet claim coverage (workflow wf_a636f32c-70f, 2026-10-13)

Source: 12-agent workflow (3 extractors, 4 cluster mappers, 4 adversarial verifiers, 1 synthesizer); 202 claims extracted (161 LatchSet-relevant). Verbatim synthesis below.

# LatchSet claim coverage: synthesis of the four mapping clusters and their verifiers (2026-10-13)

**Evidence tags.** Every evidence item carries one of these tags:
- **K**: kernel-checked and in the tree. `Print Assumptions` gives Closed unless the entry says otherwise.
- **Ks**: kernel-checked only in a piped scratch session. It is in no file and must be committed before the paper cites it.
- **S**: what a Coq statement says, including its scope.
- **D**: a derivation that has not been checked.
- **P**: a claim in the paper's working copy.
- **R**: a reviewer requirement, cited as popl2027-reviews.md:line.

**Paths.**
- Paper files are relative to `async-ccal/drafts/relaxed-lin/`. `ov` is overview.tex, `in` is intro.tex, `rl` is relaxedlin.tex.
- Coq files are relative to `rbgs/`.
- `File.Mod.name` stands for the fully qualified `<dir>.<File>.<Mod>.name`. For example, `LatchSetRT.LatchSetRT.ce1_overlay_not_rel_lin` is `examples.Relaxed.LatchSetRT.LatchSetRT.ce1_overlay_not_rel_lin`.
- Each module has the same name as its file, except that `models/RelaxedSignature.v` declares `RelaxedSig`.

**Source of the instruction.** The new author instruction is recorded at `.rocq-review/iteration-log.md:630`: "for LatchSet you must support all claims in the overview".

**One new scratch result from this synthesis** (Ks, Rocq 9.3.0, piped, Closed under the global context):
- `latch_drain_exports_rect`: for every `rc` and all `c d ∈ {DRFence, DR}`, `dto rc c d = dto rc (emb (fm c)) (emb (fm d))`, where `fm DRFence = RFence` and `fm DR = Local`.
- Re-evaluated in the same session:
  - `dto rc` on (DRFence,DRFence), (DRFence,DR), (DR,DRFence), (DR,DR) = (true, true, false, false), for both `rc`;
  - `in_leb DRFence Wmb = true` and `out_leb DRFence DFence = true`, for both `rc`;
  - `out_leb DLocal DR = in_leb DLocal DR = true`.

---

## 1. Headline

- **Not as written, and not with the current code.** The LatchSet exports an "atomic set" (P: ov:316, ov:333, ov:335). For the code of tests_latch_set.py:21-29 under LD-0 (a′), whose insert ends in plain stores with no draining fence, this is refuted:
  - K at the overlay, cell and x86 levels: `LatchSetRT.LatchSetRT.ce1_overlay_not_rel_lin` (LatchSetRT.v:711, for every `indep`), `rt_ins_mem_false_not_rel_lin` (:614), `ce1_cells_V_any` (:403), `ce1_x86` (:517).
  - D: the module step and the program-point step (LatchSetRT.v:165-177).

  The earlier choice of ν_BS (research-intent.md:147) contradicts these overview sentences directly. Under the new instruction, it has to be withdrawn.
- **One code change makes most overview claims mutually consistent.** Add a draining full fence `smp_mb()` to insert (x86: MFENCE or a locked RMW; ARMv8: DMB ISH). Then export insert ↦ `DRFence` (= `emb RFence`, WindowTable.v:443, :504) and contains ↦ `DR`. With these exports:
  - the atomic set becomes reachable (D);
  - SB is excluded at ν_L (D);
  - load buffering is permitted at the interface (Ks table entries);
  - the "fence mode" sentence at ov:337 becomes literally true for ν_L. Ks `latch_drain_exports_rect` combined with K `WindowTable.WindowTable.abstract_is_rect` (WindowTable.v:507) gives this.
- **Refuted as written by kernel evidence:**
  - the atomic set, for the current code (above);
  - write-snapshot over buffered LatchSets. Ks `sb_ws_V_any`, `sb_ws_hist`, `sb_ws_x86` show it; the in-tree cores are K `SeqLockQ6Mem.SeqLockQ6Mem.sbrfi_*` (SeqLockQ6Mem.v:437-443) and `ARMBar.ARMBar.SBrfi.sbrfi_dmbld_allowed` (ARMBar.v:1511); the overlay step is D;
  - Def. 5.8 compatibility for any non-degenerate LatchSet configuration (K `BracketedComposition.BracketedComposition.bracketed_not_compatible`, BracketedComposition.v:123; Ks `tso_not_compatible`);
  - "soundness with respect to RC11" (K `Litmus.Litmus.LB`/`ISA2` pairs);
  - the printed view compatibility and prop:rlhl-sc (K `PrefixView.counterexample_I11`, :954).
- **Refuted as written by derivation:**
  - load buffering through two LatchSets, in the dto memory, on x86 and on ARMv8;
  - "brings load-buffering behavior … into one layered verification" (in:106), because the write-snapshot never issues contains before insert;
  - the wait/control-dependency wording at ov:23 and in:28;
  - "disjoint underlays" (ov:296-298, ov:337), which conflicts with the shared ghost barriers GBw/GBr (TableBarrier.v:900-912).
- **Claims that need new theory:**

  | Item | Size |
  |---|---|
  | A draining primitive in memory/ | M |
  | A hidden-linearization-point extension of `WindowLinkTable.Positional` | M, risk L |
  | An interval target `rel_lin_ev` | M |
  | The write-snapshot module theorem | L |
  | Relaxed vertical composition | XL |
  | Pending operations | M–L |
  | Observational refinement | research |
  | ARMv8 grounding (LS-A2: real time, converse containment, M-15, the n→a_i control edge) | research |
  | A universal RLHL judgement, if "a program logic verifies LatchSet" is kept | research |
- **Claims that need engineering only:**
  - M_L with S1 and the module theorem over the table-induced memory with the drain;
  - x86 grounding (mfence, G-1, VE_x86);
  - a relaxed module sum `msum` and the n-ary horizontal instance of `WindowLinkTable.WindowLinkTable.window_link_table` (WindowLinkTable.v:457);
  - an LB witness through LatchSet ⊗ a client cell;
  - OOTA rejection;
  - the conservative-extension theorem on complete traces;
  - the paper's LB example under I_COH;
  - the precision variants.
- **Already supported:**
  - the rel_lin definition for complete traces and atomic targets (ov:254; `RelaxedTraceLin.RelaxedTraceLin.rel_lin`, RelaxedTraceLin.v:82);
  - handles and intra-thread overlap (ov:4);
  - rhb clause (i) is thread-agnostic, as at ov:251 (RelaxedTraceLin.v:60-65);
  - dependency-frontier soundness (`RelaxedModuleSemantics.RelaxedModuleSemantics.module_dependency_soundness`, :878);
  - the V-level x86 equality (`TSO.TSO.tso_traces`, TSO.v:603);
  - the n-ary spec product (`BracketedLink.BracketedLink.nuF_all`, :322);
  - "may reorder only when both permit" (ov:337), in the necessary direction.
- **Bottom line.**
  - Over the table-induced memory grounded in x86-TSO, every LatchSet-layer, horizontal and write-snapshot-layer claim is reachable. The cost is XL plus one M item of new infrastructure.
  - Relaxed vertical composition is XL.
  - ARMv8 grounding, observational refinement and a mechanized RLHL remain research. The paper must schedule them or qualify the claims (§3.7).

---

## 2. Claim coverage matrix

Statuses below already include the verifier corrections. Where the mapper and the verifier disagreed, the status cell gives the adjudication.

### A. The LatchSet object

| # | Claims | Paper (P) | Required Coq | Existing (K/S/Ks/D) | Status (adjudicated) | What makes it true | Size |
|---|---|---|---|---|---|---|---|
| A1 | OV-70, OV-71, OV-73, OV-80, OV-43, FM-14, FM-38, IN-8 | ov:316 "Atomic set behavior + relaxed ordering"; ov:335 "exports an atomic set specification"; ov:325; in:7; in:106 | `latchset_module_atomic`: ∀ q0 T c, `module_execution_tagged VE M_L (initial_tagged_module VE q0) T c` → `tm_queue c = []` → every call is `DeadCall` → P1 T → P2 T → `rel_lin under_sel T (semi_independent E_tab) nu_tab_ops` → `rel_lin over_sel T I_L (nuset_from S0)` | K: `LatchSetRT.LatchSetRT.ce1_overlay_not_rel_lin` (:711), `_from` (:700), `ce2_overlay_not_rel_lin` (:736), `rt_ins_mem_false_not_rel_lin` (:614, uses only rhb clause (i)), `ce1_cells_V_any` (:403), `ce1_underlay_allowed` (:409), `ins2_all_pending` (:447), `ce1_x86` (:517); controls `ce1_flushed_first_not_V` (:473) and `ce1_flushed_true_V` (:480). S: TableBarrier.v:127-139, "this model has no draining fence". D: the module step and the program-point step (LatchSetRT.v:165-177). Missing: M_L and any module theorem. | **REFUTED AS WRITTEN** for the current code; all clusters agree. Size: mapper XL, grounding mapper L, verifiers XL/research. Adjudicated as XL for the dto/x86 setting and research for ARMv8, because the author requires ARMv8 (research-intent.md:148). | The drain in insert (§3.1). A drain primitive in memory/. The hidden-LP extension: the insert's LP is the hidden flush of `seq:=s+2`. Neither the issue nor the mb works as LP (verifier, D). Then M_L, S1 plus a publication lemma, and the module theorem. State P1/P2 at ov:335. | XL; ARM research |
| A2 | OV-77, OV-78, OV-79 (atomic part), FM-12; OV-64 | ov:333 "must supply the atomic update and observation interface required by the collect loop"; ov:305-309 | A1 plus `sb_forbidden_L`: a complete ν_L trace with T1: Ins₁; Mem₂=false and T2: Ins₂; Mem₁=false is not rel_lin to ⊗ `nuset` under I_L | K: `LatchSetRT.LatchSetRT.latch_table` (:333-341): `dto rc Wmb DR = dto rc DR Wmb = false`, so the Wmb/DR export leaves (insert_i, contains_j) open. Ks: `sb_ws_V_any`, `sb_ws_hist`, `sb_ws_x86`, `sb_ctl_not_V`. K cores: `SeqLockQ6Mem.SeqLockQ6Mem.sbrfi_V`/`sbrfi_nu`/`sbrfi_x86_trace` (:437-443) and `ARMBar.ARMBar.SBrfi.sbrfi_dmbld_allowed` (:1511, unvalidated reading). | OV-77 is a **correct requirement** that the current code does not meet; it is refuted together with A1. OV-64 is a design statement, **paper-only-ok** (verifier correction). The mapper's name `RelaxedSig.tensor_semi_independent` does not exist; the name is `RelaxedSig.Tens.tensor_semi_independent` (RelaxedSignature.v:99-115). | A1 plus insert ↦ DRFence. Ks: `dto DR DRFence = false`, `dto DRFence DR = true`, `in_leb DRFence Wmb = true`, `out_leb DRFence DFence = true`. A contains-only collect needs participant ids as inputs. | S after A1 |
| A3 | OV-79 (shape) | ov:333 "ν_L = ⊗ LatchSet_i"; ov:308 | n-ary product on sequential witnesses | K: `BracketedLink.BracketedLink.nuF_all` (:322); `WindowLinkTableJ.WindowLinkTableJ.window_link_table_of_J` (:537) | **SUPPORTED** for the shape | none | S |
| A4 | OV-72, OV-82, OV-4, OV-26, IN-22, IN-23, FM-20, FM-21, FM-24 | ov:317 "Memory-level dependencies preserved"; ov:335 "dependencies needed to realize this interface"; in:103; impl.tex:123-139 | M_L with `FutureD` on contains' data reads (deps = {rd seq}) and data/control tags on the writer's stores; `latch_addr_edge`; an audit or tag-policy lemma; for ARMv8, the order of rd n before rd a_i | K: `module_dependency_soundness` (RelaxedModuleSemantics.v:878); `must_precede` (:252-258). S: tags are hand-written (RelaxedLang.v:42-60). LatchSetRT does not model the address dependency (LatchSetRT.v:32-35). K: `ARMBar.ARMBar.Sanity.mp_dmbst_ctrl_allowed` (:1068). | ov:335 inherits A1's refutation, because "this interface" is the atomic set (verifier). After A1: **NOT YET SUPPORTABLE** for the dto memory and x86. ARMv8: **NEEDS NEW THEORY plus a code change**. The loop bound gives a control edge from rd n to rd a_i that ARMv8 does not enforce (D; Mem.tex:701-713). | LS-2 tags plus an audit lemma; an F3→rhb derivation. For ARM: scan all N slots without waiting on n (P2 bounds N), or use LDAR, or LDR followed by DMB ISHLD, on n. Reword ov:317 to "hand-annotated, audited". | L, plus ARM research |
| A5 | OV-23–29, OV-51 | ov:23 "A wait introduces a response-to-invocation edge to subsequent calls"; in:28 "a data or control dependency forces the dependent operation to wait"; in:30 | wording only | K/S: `RelaxedLang.Prog` (:63-76); `must_precede`; `DependencyFrontierExamples.load_overtakes_wait` (:151) and `dependent_store_waits` (:165); impl.tex:139 (κ: for memory, everything but a plain read is control-ordered) | **PARTIALLY**. ov:23 and in:28 overstate (D). The LatchSet scan itself relies on the loop-bound control dependency not ordering the reads (tests_latch_set.py:6-7). | Reword both, e.g. "…to the subsequent calls that depend on its result" | S |
| A6 | OV-2, OV-13, OV-19, OV-20, OV-22, OV-49, OV-50, IN-7, IN-20, IN-21, IN-32 | ov:7, ov:15, ov:174; in:26, in:89 | wording only | K: `rel_lin` takes indep and nu separately (RelaxedTraceLin.v:82). `Cell.Cell.V` and `nu` are indexed by I through the contract (Cell.v:603-627). `Tensor.Tensor.ContractMatters.contract_matters` (Tensor.v:727). P: trace.tex:188-190 (register cells: ν_SC = ν_COH = ν_RA) | **PARTIALLY**. in:89 is scoped to atomic specifications by its caption (in:92), so it holds once A1 holds (verifier adjudication). in:21's sentence is true for register cells; the buffered cell has no SC instance (mapper said "refuted"; the verifier's "partially" is accepted). | Qualifiers at ov:15, ov:174 and in:26. One sentence saying that LatchSet runs on the buffered cell. | S |

### B. Ordering contract, LB, OOTA, conservativity

| # | Claims | Paper | Required Coq | Existing | Status (adjudicated) | What makes it true | Size |
|---|---|---|---|---|---|---|---|
| B1 | OV-3, OV-34, OV-35, OV-44, OV-47, OV-48, OV-81, FM-39, IN-14, IN-24 | ov:2, :160, :174; ov:335 "a relaxed ordering contract that admits load buffering"; in:68, in:104 | A fixed I_L derived from the categories; dominance lemmas; an LB non-vacuity execution that is rel_lin under I_L and not under ∅ (templates: `SeqLockLB.seqlock_lb_nonvacuous` :1035, `seqlock_lb_not_classical` :953) | K: `latch_table`; `WindowTable.WindowTable.dto` (:460). Missing: I_L and any LatchSet LB execution. | **PARTIALLY: permitted at the interface only.** Adjudication 1: two-LatchSet LB is not realizable (spec-LB verifier, D from K table entries `dto DR Rmb = dto Rmb DR = true` plus LD-0 (a′) data dependencies), so the mapper's "trailing drain keeps LB realizable" through ⊗LatchSet_i is rejected. Adjudication 2: LatchSet ⊗ a client cell z (T1: contains(k)=true; z:=1 ‖ T2: r:=z; insert(k)) is realizable in the dto memory, with or without the drain, because `dto DR DFence` only puts rd z before the mb. It is also realizable on ARMv8 (D: no ob edge from rd z to insert's stores; DMB ISHST orders only W→W). x86 forbids it. The grounding verifier's "not realizable on ARMv8" therefore holds for two LatchSets but not for this configuration. | Directional export DRFence/DR. An LB witness on the joint spec (WindowLinkTableJ, LS-6). Reword ov:335 to "permits", with the x86 caveat. | M |
| B2 | OV-78 (SB part) | ov:333; ov:305-309 | `sb_forbidden_L` | none | **NOT YET**. True under the DRFence export (D: Ins₁ <rhb(ii) Mem₂ < Ins₂ <rhb(ii) Mem₁ < Ins₁). Under Wmb it holds only if M_WS waits. | Prove it (S) | S |
| B3 | OV-32, OV-40, OV-41, OV-60, IN-16, IN-25, IN-41 | ov:169; in:68; in:104 "admit load buffering while rejecting its dependency-guarded OOTA variant" | `oota_not_rel_lin` (memory spec, ∀ indep, rhb (i) only); a module-level guarded program; optionally LB+ctrl through LatchSet | None (concern-matrix.md:184). Template `rt_ins_mem_false_not_rel_lin` (:614). S: rhb clause (i) has no thread condition (RelaxedTraceLin.v:60-65). R: popl2027-reviews.md:108-110 asks to restrict clause (i), which would admit guarded OOTA under I_COH (D). todo-oopsla-v2.md:25 marks this done by citing Litmus.v, which has no dependency edges. | **NOT YET** | Prove it, and keep clause (i) thread-agnostic | M |
| B4 | OV-5, OV-21, OV-31, OV-33, OV-38, OV-39, OV-53, OV-54, OV-58, OV-59, OV-61, IN-15, IN-27 | ov:76-113, :199-245; in:10-14 | The paper's I_COH and register spec; the trace is rel_lin under I_COH and not under ∅ | K: `ViewLiftOMCA.lb_rel_lin` (:463; over SC ViewLift, not I_COH); `Litmus.Litmus.LB.ours_allow` (:204) and `rc11_forbid` (:227) | **PARTIALLY** | A small file | S |
| B5 | OV-63, IN-6, IN-33, IN-34, IN-38, FM-5 | ov:256 "proves coincidence with classical linearizability on SC histories"; in:7, :99, :103; rl:35-37 | `rel_lin_classical`: alternating traces → (rel_lin ↔ hw_lin), on complete traces | None (concern-matrix.md:70). P: rl:35-37 has no proof. | **NOT YET** | Prove the complete-trace version. Keep the pending version paper-level or address it in Q3. | S (M–L with pending ops) |
| B6 | FM-47, FM-50 | Not in the current ov or in; only todo-oopsla-v2.md:28 | Variant refutations | Python checker only (run_latch_set.log:5-11) | **NOT A CURRENT CLAIM**. If it is added, the variant table depends on where the drain goes (§3.1, decision 2). | LS-4. Drop the RC11 sentence. State verdicts relative to the dto memory. | L |

### C. Horizontal composition

| # | Claims | Paper | Required Coq | Existing | Status (adjudicated) | What makes it true | Size |
|---|---|---|---|---|---|---|---|
| C1 | OV-86, FM-33, FM-41, IN-10; rl:176-188 (prop:locality); rl:2; in:103 | ov:337 "combines the separately verified LatchSet components over disjoint underlays" | `msum` and a lifting lemma; a per-component certificate; `latch_hcomp_n` as an instance of `window_link_table` at Comp := participant index | K: `WindowLinkTable.WindowLinkTable.window_link_table` (:457). S: one module with `compE`/`compF`, complete executions, and a whole-execution `positional` premise (:186-190). K: `WindowLinkTableJ.WindowLinkTableJ.window_link_table_J_jointE` (:629); `nuE_all`/`nuF_all` (BracketedLink.v:321-322). SC only: `CompLinHComp.implHComp` (:295). Missing: a relaxed module sum and any verimpl. | **NOT YET** (dto/x86), and only conditionally. **NEEDS NEW THEORY** for ARMv8. Verifier additions: (i) `nuEc` takes Op lists, so this needs `nu_tab_ops` and the G-1 bridges; (ii) the shared GBw/GBr ghosts block assigning wmb/rmb to a component; (iii) WLT's `positional` has no trace-predicate slot, so a P1/P2 variant is needed; (iv) the tags. | `msum` (M); LS-5 stated per component (M); the instance (S); the P1/P2 variant of WLT (S); a joint underlay | L |
| C2 | OV-89, OV-90, OV-91, FM-31; OV-339 ("compatibility check") | ov:337 "must also be compatible … Atomic set behavior alone does not discharge this obligation"; ov:339; rl:146-161 | Def. 5.8 or its replacement | K: `BracketedComposition.BracketedComposition.compatible` (:94-101), `bracketed_not_compatible` (:123); `WindowComposition.WindowComposition.Necessity.fence_claim_fails` (:570). Ks: `tso_not_compatible`, `arm4_compatible` (holds when everything is Local), `compat_local_forces_local` | Mapper: refuted. Verifier: partially (degenerate). **Adjudication: REFUTED for every design that supports the rest of ov:337.** Def. 5.8 holds only when all exports are Local (Ks), and that makes "derives … from the fence mode" vacuous. For the drained design it fails (D: (insert₁, contains₂) is ordered at the overlay, while the called pair (wrt, rd) is in I_tab). "Atomic set behavior alone does not discharge" is true only for non-Local exports. | Replace it with window dominance (WindowTable.v:47-49; WLT `window_bodies` :110-116). This also answers R: popl2027-reviews.md:116-118 (A L445), which rl:161's iff cannot. | S paper, plus window_bodies inside LS-5 |
| C3 | OV-87, OV-88, FM-8, FM-48 | ov:337 "derives cross-component semi-independence from the fence mode exported by each operation … may reorder only when both modes permit"; trace.tex:350-371 ("exactly when") | Exports representable by modes, plus dominance | Ks: `latch_exports_not_rect` ({Wmb, DR} is not rectangular); `wf_forces_local` and `only_local` (four modes on the dto underlay force Local). Ks (this synthesis): `latch_drain_exports_rect`. K: `WindowTable.abstract_is_rect` (:507), `emb` (:504), `rect_indep_iff` (:241), `wmb_not_rectangular` (:390). | Current exports: **REFUTED** (vacuous or unrepresentable). Drained design: **SUPPORTABLE** for ν_L's cross-component pairs, which are the four-mode tensor of (RFence, Local). OV-88's "only when" holds for any table (definition of `dto`, WindowTable.v:460-464). "Exactly when" at trace.tex:371 holds only for rectangular exports (counterexample `dto Wmb Wmb = true`). The verifier's x86/I_TSO four-mode route is valid but moot given the ARMv8 target. | Commit the lemma. Use table wording in the main text, with the modes as the rectangular special case (the author's running-example decision, research-intent.md §8). Note that LatchSet's exports are rectangular. | S |
| C4 | OV-66, OV-67, OV-68, OV-74, FM-15, FM-16 | ov:289-298 "disjoint memory underlays with ordering primitives"; ov:325; rl:188 | ν_{E_i} defined over per-component locations; ν[⋃Locs_i] ⊆ ⊗ν[Locs_i] at the hidden level, with ghost renaming; the rel_lin transfer | K: `Tensor.Tensor.memory_tensor` (:562), `memory_is_tensor_of_cells` (:597), `contract_matters` (:727); `Litmus.Litmus.MP.hidden_tensor_is_not_a_product` (:793, uses classic). S: `tab_cfg` has a single GBw and GBr (TableBarrier.v:900-912). P: Mem.tex:23 excludes fences (the mapper's ":26" is corrected to :23; the quote it cites is at :221). | **NOT YET**. The paper does not define the ordering primitives. | Joint memory with a redrawn figure (recommended), or per-component ghosts plus `nu_joint_in_spec_tensor` | M after G-1 |
| C5 | FM-9, FM-10, FM-11 | trace.tex:373-376, :419-435; gamemodel.tex:606-611 | n-ary tensor and well-formedness (E_compat) | K: `RelaxedSig.Tens.tensor_semi_independent` (RelaxedSignature.v:99-115), `omap` (:128-135, shared handle); WLT `E_compat` (:97) and `F_cross` (:102) | **PARTIALLY**. WLT does not need `Tens.big`. trace.tex:21 says "four components" but writes a triple. | `latch_E_compat` (S). State ⊗_{i∈Ix} directly. | S |
| C6 | FM-29, FM-30, FM-32 | rl:112-174 (prop:tensor-impl) | ⟦M⊎N⟧ = ⟦M⟧⊗⟦N⟧ | none | **NOT YET**. The premise holds only in the all-Local reading. | Drop it, or restate it with dominance | XL in Coq |
| C7 | FM-13, FM-36 | trace.tex:454; gamemodel.tex:653-656 | A relaxed spec tensor | none | Needed only if ν_BS is kept (research). FM-36 is **paper-only-ok**. | Avoid it with the drain | research |
| C8 | IN-26 | in:70 | — | K: `memory_is_tensor_of_cells`; WLT needs categories and dominance | **PARTIALLY** | Reword to "spec, semi-independence, categories, and a dominance proof" | S |

### D. Write-snapshot and vertical composition

| # | Claims | Paper | Required Coq | Existing | Status (adjudicated) | What makes it true | Size |
|---|---|---|---|---|---|---|---|
| D1 | OV-57 | ov:254 | rel_lin for complete traces | K: `RelaxedTraceLin.RelaxedTraceLin.rhb` (:60-65), `rel_lin_witness` (:74-80), `rel_lin` (:82-84) | **SUPPORTED** (complete traces, atomic targets) | — | — |
| D2 | OV-45, OV-62, IN-18, FM-7, FM-43 (FM-2–4) | ov:172, ov:256; in:23, in:72; trace.tex:154, :182-188; rl:29-33 | `rel_lin_ev` (event-level witness, def:rlxlin-po) with a conservativity lemma; pending operations | No relaxed target. SC only: CompLin over non-atomic LTSs (ListPoolSpec.v:14-15) | **PARTIALLY** | `rel_lin_ev` (M); pending operations (L) | M / L |
| D3 | OV-75, OV-76 | ov:333, first sentence | none | 2023 draft program.tex:57-79 | **PAPER-ONLY-OK** | Cite `interval-seq` (references.bib:1238-1250) | S |
| D4 | OV-65, OV-69, OV-83, OV-84, IN-49, FM-40 | ov:269-273, :300-309; ov:335 "establish an interval-sequential specification"; in:106 | ν_WS; M_WS; `ws_verimpl` (event-level) over `BL.nuE_all` of `nuset`; non-vacuity (two overlapping calls that both return {1,2}) | none | Over ν_BS: **REFUTED** (Ks at cell and x86 level; D at the overlay). Over an atomic ν_L: **NOT YET**. Adjudication: the inter-collect waits alone exclude SB (verifier, D). Self-inclusion needs either an insert wait (Wmb export) or the DRFence export. On ARMv8 the inter-collect wait is M-15 (concern-matrix.md:38). | Tasks WS-0 to WS-2 | L, +M |
| D5 | OV-93, FM-26 | ov:339 "implements ν_F over any underlay relaxed-linearizable to ν_E"; rl:74 | `verimpl_c` (complete executions) | WLT has this shape. `RelaxedGSim.RelaxedGSim.gsim_rel_lin` (:1031); `ViewLHL.ViewLHL.implements` (:108). Completion: constructor `tagged_return` with `Hdone : owner_done_tagged` (RelaxedModuleSemantics.v:603-606). The mapper's IntervalWindow.v:52-54 citation is wrong. | **PARTIALLY** | Define it and prove that the WLT hypotheses imply it | S; prefix form M–L |
| D6 | FM-25, FM-28, OV-92; in:7 "vertical composition of implementation layers"; in:70; in:113 | rl:56-102 | Semantic stacking plus `vcomp` | SC only: `CompLinVComp.VComp.CompLin_vcomp` (CompLinVComp.v:1476-1483, eq_rect_eq). Relaxed, at witness level only: `WindowComposition.vertical_*` (:687-711). R: popl2027-reviews.md:166-168 ("function inlining is an unsound transformation"); A21 at :506-512. | **NEEDS NEW THEORY** | §3.5 | XL |
| D7 | OV-94, FM-42 | ov:339 "the upper proof applies to obtain write-snapshot over ⊗ν_{E_i}" | `ws_end_to_end` | Ks: `sb_ws_x86`. K: `ARMBar.ARMBar.Sanity.sb_dmbld_allowed` (:1095), `sb_dmbsy_forbidden` (:1106) | **REFUTED** for the current code (x86 machine trace in Ks; ARMv8 at core level, model-relative K; overlay D). After the drain: **NEEDS NEW THEORY** (D4, D6, C1, G-1). | The §5 chain | XL |
| D8 | OV-95 | ov:339 "Replacing … preserves the upper proof whenever its exported interface and the compatibility condition are preserved" | A corollary | none | **NOT YET**. "Compatibility condition" must become dominance. | A corollary of D6 | S after D6 |
| D9 | OV-96, OV-97, FM-27, IN-9, IN-39 | ov:339 "follows from observational refinement"; in:7, in:103; rl:76-84 | A relaxed strategy semantics and the proposition | None. The TR's saturation claim covers only sequential implementations and is unproved (Appendix/relaxedlin.tex:53-56). R: popl2027-reviews.md:305, :312-318. | **NEEDS NEW THEORY** (research) | Reword: reuse follows from the quantification over underlays plus D6 | research |
| D10 | OV-6, OV-85, IN-12, IN-13, IN-37, IN-48, FM-44 | ov:2; in:99; in:106 "brings load-buffering behavior and non-atomic object specifications into one layered verification" | The conjunction of the above, plus LB inside the case study | none | LB half: **REFUTED AS WRITTEN** for the case-study structure. M_WS never issues contains before insert, and LB through two LatchSets cannot be realized (D). WS half: **NEEDS NEW THEORY**. Correcting the WS mapper: under the DRFence export the WS proof does use the (insert, contains) rhb(ii) edge, in place of an insert wait. | Reword; exhibit LB at LatchSet ⊗ z | XL |

### E. Grounding, logic, presentation

| # | Claims | Paper | Required Coq | Existing | Status (adjudicated) | What makes it true | Size |
|---|---|---|---|---|---|---|---|
| E1 | IN-43, FM-17 | in:105 "equivalence with x86-TSO"; Mem.tex:256-258 | V-level equality; with the drain, an mfence | K: `TSO.TSO.tso_traces` (:603; TSO_cfg, read/write fragment, flushes visible); `TableBarrierTSO.TableBarrierTSO.x86_trace_V_tab_index` (:204, one direction), `x86_wmb_V_tab` (:627), `x86_rmb_V_tab` (:639) | **PARTIALLY**. TSO.v has no fence. | MD-2 | M |
| E2 | FM-19, IN-46 | in:105 "connect our object interface"; Mem.tex:231 refers to `mem:cor:rlxlin`, which is undefined | G-1 plus VE_x86 | None (TableBarrierTSO.v:77-78) | Split. Memory-level correspondences: **SUPPORTED**. Link to the object interface: **NOT YET**. | G-1, X-1 | L |
| E3 | FM-18, IN-44, IN-42 (ARM); research-intent.md:148 | in:105 "formal connection with the ARMv8 model"; Mem.tex:742, :754-758, :812 | A generic ARM model with DMB; a real-time convention; converse containment on the LatchSet fragment; G-1; R4 or an M-15 fix | K: `ARM.ARM.arm_containment` (:193; RC_cfg, no fences, (W) as hypothesis, ours+S ⊆ ARM, the wrong direction for grounding); `Litmus.Litmus.RSW.arm_allow` (:613) / `ours_forbid` (:523); `ARMBar.ARMBar.RTGet.rt_get_allowed` (:2017). S: ARMBar is litmus-only with an unvalidated reading (:16-21, fixed `loc` at :252, no rel_lin link at :206, no operational model at :210). No latch test exists in memory/herd. | **NEEDS NEW THEORY** (research). Verifier additions: the n→a_i edge; Δ2 for same-location `seq` re-reads under I_tab; a correspondence from tags to AArch64 dependencies; the author excluded changing real time in rel_lin (research-intent.md:100, option (iii)). | LS-A1 now plus rewording; LS-A2 later | research |
| E4 | IN-45 | in:105 "we prove soundness with respect to RC11" | — | K: `RC11.RC11.rc11_containment` (:340, COHERENCE only); `Litmus.LB.ours_allow` (:204) with `rc11_forbid` (:227); `ISA2.ours_forbid` (:276) with `rc11_allow` (:370) | **REFUTED AS WRITTEN**, in both directions. The todo at Mem.tex:819 is stale. | Reword | S |
| E5 | IN-11, IN-42, IN-51–53 | in:7; in:105 "instantiate … COH, TSO, ARMv8, and C/C++11"; in:111 | — | K: `Equivalence.declarative_characterization` (:40), `declarative_TSO`/`PSO`/`RC` (:65-77) | TSO: **SUPPORTED**. ARMv8 and C/C++11 "instance": **REFUTED** (memory/README.md:116-127). COH is not mechanized. RC11 is non-MCA, while the scope is oMCA (research-intent.md:105). | Reword | S |
| E6 | IN-35, IN-47, FM-35 | in:7 "a program logic that verifies LatchSet"; in:99; in:106 | RLHL soundness plus a LatchSet derivation | K: `RelaxedLogic.HTripleProvable` (:869) is existential; `provable_wait_pending` (:970). `gsim_rel_lin` (:1031) and `ViewLHL.vlhl_sound` (:419) are sound but never instantiated. | **NEEDS NEW THEORY** (Q1) | Reword to the semantic module theorem; give a paper-level RLHL sketch | research / S |
| E7 | IN-36, FM-34 | in:99; implex.tex:48-59, :170-179 | — | K: `PrefixView.counterexample_I11` (:954), `sc_reg_not_compat_printed` (:1018; the mapper cited :1004, which is the rd_bypass version); `ViewLiftOMCA.n6_mp_inseparable` (:258) | IN-36: **PARTIALLY**. FM-34: **REFUTED**. LatchSet does not go through views. | Rewrite implex §6 | M |
| E8 | FM-45 | R: popl2027-reviews.md:214, :311-316, :615 | A logic, its soundness against a weak memory model, an object and a client | A partial chain exists only for the register-cell SeqLock, which was removed from the table | **NEEDS NEW THEORY** as R states it. XL under a declared substitution: semantic theorem in place of the logic, x86 in place of RC11, LS-6 as the client. | Declare the substitution | XL |
| E9 | OV-1, IN-2, IN-5, IN-40 | ov:2; in:3, in:5, in:104 | M_L and layering | K: `FutureD` (RelaxedLang.v:65); `module_dependency_soundness` | **PARTIALLY** | LS-2 to LS-5 and D6 | L |
| E10 | OV-8, OV-9, IN-30 | ov:4; in:85; trace.tex:37 | Operations keyed by (thread, handle) | K: `RelaxedTraceLin.Op` (:28), `rhb`, `rel_lin`; `seqlock_lb_nonvacuous` | **SUPPORTED**. Flush events are paper-only (research-intent.md:135-137). | — | — |
| E11 | OV-7, OV-10, OV-12, OV-36, OV-42, OV-46 | ov:4, :7, :160, :172; trace.tex:175; Appendix/edag.tex:158-163 | none | K: `declarative_characterization` (block level); no EDAG in Coq | **PAPER-ONLY-OK / PARTIALLY** | Keep it at TR level | S |
| E12 | OV-11, OV-14–18, OV-30, OV-37 | ov:7-15, :43-74, :160-167 | none | — | **PAPER-ONLY-OK**. Add one sentence: LatchSet uses the buffered cell. The register EDAG would reject CE1, which x86 admits (D). | — | S |
| E13 | IN-17 | in:21 | — | `Litmus.LB.ours_allow`; (W) is a hypothesis (ARM.v:78-79) | **PARTIALLY** | A4 and B3 | M |
| E14 | IN-3, IN-4, IN-19, IN-54, IN-55, FM-46, FM-49 | in:5, :23; in:113 "Finally, \todo{example}" | — | main.tex:228-235 inputs no case-study section | **PAPER-ONLY** | Write the section | S |

**Claims the verifiers added, and where they are covered.**
- ov:296-298 and ov:337, disjoint underlays: C4.
- P1/P2 missing from ov:335: A1.
- ov:337, second half: C2.
- ov:308-310, "uses all n": A3 and D4.
- in:103 and in:104: C1 and C8.
- rl:2 and rl:161: C1 and C2.
- trace.tex:251 and :433-435: C3 and C5.
- in:111 versus C/C++11: E5.
- relatedwork.tex:4 and :34: D6 and B5.
- in:7, "vertical composition": D6.
- implex.tex:170-179: E7.
- in:28 and in:30, the ARMv8 dependency gap: A4 and A5.

---

## 3. Minimal consistent design that supports the overview claims

### 3.1 LatchSet code

Writer: one designated thread (P1); LD-0 (a′) (latchset-plan.md:147). The barrier sequence follows tests_latch_set.py:21-29.

```
insert(k):     // P1: only t_w; inserts pairwise non-overlapping
  s := rd seq; read copy 0; compute new sorted array      // LD-0 (a′)
  smp_wmb()                     // wmb0  (window start)
  wrt seq := s+1; smp_wmb()     // wmb1
  write copy 0 (a2, a1, n)      // C0
  smp_wmb(); wrt seq := s+2     // wmb2
  smp_wmb()                     // wmb3
  write copy 1                  // C1
  smp_mb()                      // NEW: draining full fence (window end) -- option 2
contains(k):
  s := rd seq                                    // window start
  m := rd n[s&1]; rd a[s&1][i] for i < m         // address-dependent on s (FutureD)
  smp_rmb(); if rd seq != s then retry           // window end (retry read)
```

**Is a draining fence needed?** Yes, for the atomic-set claim on x86-TSO and in memory/'s model.
- CE1 (K) shows that any insert that returns with plain stores still buffered fails, for every I.
- A drain placed after the issue of `seq:=s+2` suffices (D). The Ks single instance `md_false`/`md_true` supports this: it uses the unmodified `ins2` and models no drain block.
- The table alone is not evidence. Under TableBarrier.v:127-139 (scope note (a)), DFence used as mb orders issue only. So a DRFence export would pass the dominance check, but it would not exclude CE1 until memory/ has a real drain.

**Instruction mapping.**

| Linux primitive | x86 | ARMv8 |
|---|---|---|
| `smp_wmb` | compiler barrier | DMB ISHST |
| `smp_rmb` | compiler barrier | DMB ISHLD |
| `smp_mb` | MFENCE or a LOCK-prefixed RMW | DMB ISH (modelled as DMB SY in memory/ARMBar.v) |

**Placement.**
- **Option 2 (recommended): a trailing `smp_mb`.**
  - All of insert's stores are published at return.
  - The last window call is the mb, so the export check is `out_le DRFence DFence` (Ks).
  - The five checker variants are unchanged, and "drop mb" becomes a sixth variant (CE1).
- **Option 1: replace wmb3 with `smp_mb`.**
  - It saves one wmb.
  - Copy-1 stores are still buffered at return, so the proof relies on the next insert's wmb0.
  - Dropping the mb also loses W→W order and brings back the torn s=1 read (run_latch_set.log:11).

**ARMv8-only additions.** Fix these before the litmus files are written (decision 10):
- **(a) The n → a_i control edge.** Either issue the reads of all N capacity slots with deps = {rd seq} and filter by m (P2 bounds N), or make rd n an LDAR or an LDR followed by DMB ISHLD.
- **(b) M-15.** Either use R4 Wait compilation (research-intent.md:100), or put an `smp_rmb` at contains' entry. The entry barrier is an object-side alternative and is my derivation, unchecked: ARMv8's `[R];po;[dmb.ld];po` would order every earlier load of the caller, including waited loads of other components, before contains' reads. It must be validated in LS-A1, and contains' window dominance must be re-evaluated.

### 3.2 Exported specification and modes

**Specification.**
- Per component, the spec is ν_Set = `LatchSetRT.LatchSetRT.nuset_from S0` (LatchSetRT.v:606), the atomic grow-only set.
- Preconditions: P1 and P2 (latchset-plan.md:146), over complete executions.
- ν_BS is withdrawn as the export. CE1 and CE2 remain the evidence for why the drain is needed.

**Categories.**
- insert ↦ `DRFence` (= `emb RFence`), with window [wmb0, mb]. Ks: `in_leb DRFence Wmb = true` and `out_leb DRFence DFence = true` (both `rc`). A window ending in a plain Wmb cannot export DRFence: `out_leb DRFence Wmb = false` (Ks).
- contains ↦ `DR`, keeping the author's decision, with window [first rd seq, retry rd seq]; reflexive dominance (WindowTable.v:51, :54).

**Semi-independence within one component.** I_L is the complement of `dto` on the exports:
- relaxable: (contains, insert) and (contains, contains);
- ordered: insert followed by anything.
- This makes the contract directional: LB is permitted (B1) and SB is excluded (B2).
- Allowing (contains, insert) inside one component is harmless, because the underlying same-location pairs are never in I_tab (TableBarrier.v:542-543). So a writer's contains cannot observe a later insert in its own program order (D).

**Linearization points.**
- The insert's LP is the hidden flush of `seq:=s+2`. This needs an extension of `Positional`: positions in the V-trace behind the ν-witness, a tie-break against readers' LPs so that injectivity holds, and a bridge from Wu positions to V positions (verifier).
- contains' LP lies in its window, as planned.

**Memory.** ν_{I_tab}(dto) gains a draining block, enabled only if `pend t = []` at every location; DFence's table entries already order it both ways. This is a new cross-location clause in V (Cell.v:603-627).

### 3.3 Horizontal composition of n components

**Coq.**
- `msum` of n copies of M_L on disjoint location sets.
- Instantiate `window_link_table` at Comp := participant index, with `to := dtable rc` and `catF` as in §3.2.
- Use one joint table-induced underlay via `window_link_table_J_jointE` (WindowLinkTableJ.v:629). Reasons: the ghosts are shared, the hardware has one memory, and per-component S1 survives through `positional_J_of_positional` (:518).

**Table versus fence modes.**
- Cross-component semi-independence is `F_cross` (WindowLinkTable.v:102).
- On LatchSet's exports this equals the four-mode tensor of (insert: RFence, contains: Local): Ks `latch_drain_exports_rect` together with K `abstract_is_rect`.
- So ov:337's "fence mode" sentence is exact for ν_L.
- The underlay must stay the table: Wmb is not rectangular (`wmb_not_rectangular`, :390), and four modes force Local on the dto underlay (Ks `wf_forces_local`).
- Clients that use rmb/wmb also need the table, because DR, unlike Local, is ordered by a client rmb.

**Compatibility.** Def. 5.8 is replaced by per-implementation window dominance.

### 3.4 Interval-linearizability target and write-snapshot proof

**Target.** `rel_lin_ev sel L indep (nuI : list (ThreadEvent F) -> Prop)` holds when there is a well-formed event sequence Wev such that:
- `nuI Wev`;
- Wev has the same complete operations as L;
- `rhb_L ⊆ rhb_Wev` (def:rlxlin-po, trace.tex:182-188).

It also needs a conservativity lemma: for an alternating presentation of an atomic ν, `rel_lin_ev` is equivalent to `rel_lin`.

**Specification.** ν_WS is the 2023 `nu_writesnap` (ctlinear-examples/write-snapshot/program.tex:5-27; fix the `nu_exchanger` typo at :12 and :15), or a Castañeda–Rajsbaum–Raynal automaton. This is author decision 8. Inputs are participant ids.

**Program M_WS.** Thread i is participant i and runs once:
1. `Future insert_i(i)`.
2. Repeat: issue `contains_j(j)` for every j; Wait for all responses; stop when two consecutive collects agree.

The waits between collects are required. An insert wait is unnecessary under the DRFence export (D). It is required if the Wmb export is kept, for self-inclusion (verifier).

**Proof (D).**
- Work over the sequential ν_L witness. Place the invocation point at the insert's LP, and the response point in the gap between the two agreeing collects.
- Containment follows from grow-only monotonicity: `set_ok_ins_mem`, LatchSetRT.v:593.
- The proof uses only rhb(i) edges and the (insert, contains) rhb(ii) edge.

**Side obligations.**
- A one-shot precondition (program.tex:15).
- Discharge P1/P2 for every L_i on the middle trace: thread i is the only inserter into L_i and inserts once.
- State the result parametric in n.

### 3.5 Vertical composition theorem

- **Judgement.** `verimpl_c M nuE nuF`, with an optional precondition Pre on the overlay trace: every complete tagged execution whose underlay is rel_lin to nuE has an overlay rel_lin to nuF. An event-level variant serves ν_WS.
- **`vcomp`.** If `verimpl_c_pre M nuE Pre nuF`, every underlay trace of N satisfies Pre, and `verimpl_c N nuF nuG`, then `verimpl_c (stack N M) nuE nuG`.
  - Stacking is semantic, via the LTS of M over VE. Syntactic inlining is not used (R: popl2027-reviews.md:166-168).
  - Middle traces are complete because of `tagged_return`'s `Hdone` (RelaxedModuleSemantics.v:603-606).
- **Instance.** `ws_end_to_end` over `msum M_L` and the joint memory, grounded in x86 through G-1, MD-2 and X-1.
- **Replacement (ov:339)** becomes re-instantiation of these theorems.
- **Observational refinement** is reworded (D9).

### 3.6 ARMv8 grounding

**Minimal and honest (now).** LS-A1, checked in ARMBar's three readings, with herd7 files that the author runs:
- the full idiom with the mb forbids both the bad contains and CE1's stale read;
- each variant is allowed;
- SB over two LatchSets is forbidden with DMB ISH and allowed with DMB ISHLD only (cores: `sb_dmbsy_forbidden`, `sb_dmbld_allowed`);
- LB through LatchSet ⊗ z is allowed;
- the M-15 shape, with and without R4 or the entry barrier;
- the n→a_i retry variant.

The paper then says that ARMv8 is validated at litmus level and that the theorems are relative to the table-induced memory, which is grounded in x86-TSO.

**Full grounding (LS-A2, research).**
- A real-time convention or an operational ARMv8 model.
- Converse containment ARM ⊆ ν_{I_tab + drain} on the LatchSet fragment, covering Δ2 for the `seq` re-reads and m-35 for the ghost DMB.
- G-1.
- A correspondence between FutureD tags and AArch64 dependencies (ARM.v:62 takes them as parameters).

### 3.7 Minimal paper rewording, even with the drain

These are proposals, not existing text.
1. ov:335: say the interface "permits load buffering". It is exhibited with a client cell, and x86-TSO never exhibits it. Add "under a single designated writer and a capacity bound (P1, P2)".
2. ov:337:
   - "compatible" becomes "each implementation's window ends dominate its exported categories";
   - "disjoint underlays" becomes "disjoint location sets of one memory";
   - "fence mode" stays, with one sentence: LatchSet exports insert as RFence (acquire-like) and contains as a plain read, and among LatchSets the plain read acts as Local.
3. ov:339: "compatibility condition" becomes "dominance". "Follows from observational refinement" becomes "follows from the quantification over underlays and the vertical rule".
4. ov:317: "Memory-level dependencies (hand-annotated, audited) preserved".
5. ov:23, in:28, in:30: a wait or a dependency orders only the dependent and control-ordered operations (impl.tex:139).
6. ov:15, ov:174, in:26: for buffered cells, the hidden publication contract is induced by the same relation.
7. in:7 and in:106: LatchSet is verified "in Rocq by a semantic module theorem". RLHL is paper-level, unless Q1 is done.
8. in:106:
   - Replace "brings load-buffering behavior … into one layered verification" with: "LatchSet's interface admits load buffering (exhibited with a client), and its verified interface supports the interval-linearizable write-snapshot above it".
   - Add a footnote: the code is the latch technique plus one full fence per insert.
9. in:105:
   - RC11 becomes "COHERENCE containment; incomparable (LB, ISA2)";
   - ARMv8 becomes "litmus-level / one-direction";
   - "C/C++11 instance" becomes "its oMCA release/acquire restriction";
   - "connect our object interface" waits for G-1.
10. in:99: restrict view reuse to the mechanized SC-collapsing examples.
11. All module theorems: add "complete executions only" (Q3). ov:256: "proves coincidence for complete histories".

---

## 4. Decisions the author must make

Each decision lists the options with their consequences, then a recommendation. Conflicts with earlier decisions are marked **Conflict**.

1. **Exported specification.** **Conflict:** ν_BS (research-intent.md:147) versus the 2026-10-13 instruction (iteration-log.md:630).
   - (a) Atomic ν_Set with a drain. This needs the code change, memory/ infrastructure and the hidden-LP extension. It supports ov:316, :333 and :335, makes write-snapshot provable, and makes ov:337 exact.
   - (b) ν_BS. Reword ov:316, :333, :335, in:7 and in:89. Write-snapshot then needs an exported publication operation `sync_i`, which itself needs the drain primitive, or else write-snapshot fails (sb_ws).
   - (c) ν_BS and withdraw write-snapshot.
   - **Recommendation: (a).** It is the only option compatible with "support all overview claims".
2. **Placement of the drain.**
   - Option 2: trailing `smp_mb`.
   - Option 1: replace wmb3.
   - **Recommendation: option 2.** The proof is simpler, the window ends at the mb, and the variant table is stable.
3. **memory/ infrastructure.** Approve, in new files:
   - a draining block, a new cross-location clause in V;
   - a re-statement or exclusion of the per-location tensor and the declarative theorems;
   - an x86 machine with mfence and an extended inclusion proof.

   The alternative is to keep "no drain", which forces 1(b) or 1(c). **Recommendation: approve.**
4. **Export categories and vocabulary.** **Conflict:** insert ↦ Wmb (latchset-plan.md:148-151).
   - insert ↦ DRFence (= `emb RFence`) versus Wmb versus `Acc KW true false`. The last differs from DRFence only in its kind bit (verifier).
   - contains ↦ DR (kept) versus DLocal.
   - Main text: the table, with the modes as the rectangular special case. This is consistent with the running-example decision in research-intent.md §8.
   - **Recommendation:** DRFence/DR. Commit `latch_drain_exports_rect` as an evidence lemma.
5. **Compatibility.** Replace Def. 5.8, prop:tensor-impl and prop:locality (rl:146-188) with dominance and the module-level window theorem (todo-oopsla.md:95, C4). The alternative is to keep Def. 5.8 with all-Local exports, which empties ov:337. **Recommendation: replace.** This also answers A L445.
6. **Underlay presentation.**
   - One joint memory, using `window_link_table_J_jointE`, and redraw fig:latch-set.
   - Or disjoint underlays with per-component ghosts plus a containment lemma (M).
   - **Recommendation: the joint memory.**
7. **Write-snapshot mechanization.** **Conflict:** "WS not mechanized for now" (research-intent.md:145).
   - (a) Mechanize `rel_lin_ev` and `ws_verimpl` (M + L), and keep vertical composition paper-level.
   - (b) Additionally mechanize `vcomp` (XL).
   - (c) Paper-level only, with in:99 and in:106 qualified.
   - **Recommendation: (a) now and (b) as a stretch goal.** Until (b) lands, ov:339's vertical step is a paper proposition with a TR proof.
8. **Write-snapshot definition** (open, research-intent.md:125). The 2023 spec versus the CRR automaton; ids versus values. A contains-only collect needs ids. **Recommendation:** the 2023 spec with ids.
9. **Meaning of "admits load buffering".** Interface permission, exhibited with LatchSet ⊗ z. LB through two LatchSets is impossible (D). **Recommendation:** adopt this meaning, and drop "two single-writer LatchSets" from D-LS-E.
10. **ARMv8 depth.** **Conflict:** "LatchSet over ARMv8" (research-intent.md:148) versus LS-A2 being research.
    - (a) Litmus-level LS-A1 plus rewording.
    - (b) Additionally R4 or the entry `smp_rmb`, the n→a_i fix, and LS-A2.
    - (c) An operational ARMv8 model.
    - A real-time convention is needed in any case, and the author has excluded changing rel_lin's real time.
    - **Recommendation:** (a) for the paper now, with (b)'s code mapping fixed now so the litmus files test the final code; schedule LS-A2.
11. **Dependencies.** Hand-written tags plus an audit lemma (M-23) versus mechanized Imp/compile/depof (XL). **Recommendation:** tags plus audit, and reword ov:317.
12. **OOTA and rhb clause (i).** Keep clause (i) thread-agnostic, against popl2027-reviews.md:108-110, and mechanize OOTA rejection (M). **Recommendation:** yes, and explain to the reviewers.
13. **Conservative extension.** **Recommendation:** prove the complete-trace theorem (S), and keep the pending version paper-level (Q3).
14. **RLHL.** **Recommendation:** reword to the semantic module theorem. Q1 is research and not on the critical path.
15. **Observational refinement.** **Recommendation:** reword D9. The proposition may be ill-posed for concurrent futures modules (saturation).
16. **Complete executions only (Q3).** **Recommendation:** accept for now. Pending operations are needed only for the prefix-closed "implements".
17. **Precision story.** If it is included: LS-4, a variant table that depends on the drain placement, and no RC11 sentence.
18. **Commit scratch evidence** as design-independent evidence files:
    - `sb_ws_*`;
    - `tso_not_compatible`, `arm4_compatible`, `wf_forces_local`, `only_local`, `latch_exports_not_rect`, `latch_drain_exports_rect`;
    - `md_false`/`md_true`.

    **Recommendation:** authorize, so that the paper and records cite K rather than Ks.

---

## 5. Amended phased plan

This replaces the "Amended phases" list in latchset-plan.md §5. ν_BS is replaced by ν_Set with the drain. Tasks marked **[CP]** are on the critical path.

| Phase | Task | Size | Depends on |
|---|---|---|---|
| 0 | **D-ALL [CP]**: decisions 1–10 | — | — |
| 0 | E-0: commit the scratch evidence (decision 18) | S | decision 18 |
| 0 | P-1: paper rewordings in §3.7 that are independent of later results (items 5, 6, 9–11) | S | — |
| 1 | **MD-1 [CP]**: drain primitive (new memory/ file). Includes sanity lemmas: CE1 with the drain is in V for no Ir; SB over two latches with the drain is in V for no Ir. | M | decisions 1–3 |
| 1 | **G-1 [CP]**: Op-list `nu_tab_ops` (with the drain) exposing the V-trace; `E_tab`; `nu_handle_invariant`; `po_handles_vs_index`; history → rel_lin | L | MD-1 |
| 1 | MD-2: x86 with mfence, extended erasure, x86 ⊆ V_{I_tab + drain} (extends `x86_trace_V_tab_index`) | M | MD-1 |
| 2 | LS-1′: ν_Set interface lemmas (reuse `nuset_from`), I_L, `latch_E_compat`, `sb_forbidden_L` | S | decision 4 |
| 2 | **LS-2 [CP]**: M_L with the mb, tags, variant flags (including drop-mb) and the ARM scan option; FuturesShape lemma; F3→rhb; audit lemma | M | decisions 2, 10, 11 |
| 2 | **LS-HLP [CP]**: hidden-LP `Positional` extension, and a WLT variant with a P1/P2 trace predicate | M (risk L) | G-1 |
| 2 | **LS-3 [CP]**: S1/S1_ord: L1–L5, plus L6 (`seq:=s+2` is published before the mb), plus the SC core | L | LS-2, MD-1 |
| 2 | **LS-5 [CP]**: module theorem M_L ⇒ ν_Set (complete executions, P1/P2) | L | LS-3, LS-HLP, G-1 |
| 2 | LS-6: module-level CE1 with and without the mb; LB through LatchSet ⊗ z (WindowLinkTableJ); non-vacuity | M | LS-5 |
| 2 | LS-4 (optional): variant refutations | M | LS-2, LS-3 |
| 3 | H-1: `msum` and the lifting lemma | M | LS-2 |
| 3 | **H-2 [CP]**: ν_L theorem at Comp := participants over the joint underlay | S–M | H-1, LS-5 |
| 3 | OOTA-1, CE-1 (conservativity on complete traces), LBCOH-1 | M, S, S | none (can start now) |
| 4 | WS-0: write-snapshot definition (author) | — | decision 8 |
| 4 | WS-1: `rel_lin_ev` and conservativity | M | — |
| 4 | **WS-2 [CP]**: ν_WS, M_WS, `ws_verimpl` over ⊗ `nuset` for any rel_lin underlay; non-vacuity | L | WS-0, WS-1, LS-1′ (in parallel with LS-3/LS-5) |
| 5 | V-1: `verimpl_c` with precondition and guarantee; WLT ⇒ `verimpl_c` | S | LS-5 |
| 5 | **V-2 [CP]**: semantic stacking and `vcomp` (complete executions, event-level) | XL | V-1 (can start early) |
| 5 | X-1 (= LS-7): VE_x86 module-level grounding | L | MD-2, G-1 |
| 5 | **V-3 [CP]**: `ws_end_to_end` relative to x86 | M | V-2, H-2, WS-2, X-1 |
| 6 | A-1 (= LS-A1): litmus and herd7 files (run by the author) | M | decision 10; parallel from the start |
| 6 | A-2 (= LS-A2): ARMv8 grounding | research | A-1, G-1 |

**Longest chain:** decisions → MD-1 → G-1 → LS-HLP and LS-2 → LS-3 → LS-5 → H-2 → V-3. V-2 (XL) runs in parallel and gates V-3.

**Total:** XL for the x86-grounded end-to-end result; ARMv8 is research on top of that.

---

## 6. Risks and caveats

- **Atomicity with the drain is a derivation.** The only kernel evidence is the single-instance Ks `md_false`/`md_true`, and it models no drain block. The hidden-LP extension may force a redesign of `Positional` (M becomes L). An unexplored fallback: keep ν_BS as an intermediate and add a lifting lemma, "markers before the insert's response ⇒ ν_Set". ν_BS's Op-list form cannot express response times, so this also needs extra positional information.
- **The drain adds a cross-location clause to V.** `Tensor.memory_tensor`, `Equivalence.declarative_characterization` and `TableBarrier.declarative_tab` do not cover it, and the x86 inclusion must be re-proved. Following the CLAUDE.md rule, existing statements stay unchanged and the work goes in new files.
- **Code faithfulness.** The writer is no longer the verbatim Linux `raw_write_seqcount_latch`; it adds one full fence per insert. The precision story and its variant table change.
- **ARMv8 may not be reachable as a Coq theorem.** Obstacles: the axiomatic model has no response times; the author has excluded changing rel_lin's real time; converse containment fails in general (Mem.tex:812; K `Litmus.RSW`); M-15 hits the collect loop; there is the n→a_i edge and Δ2. If LS-A2 fails, the paper must say "ARMv8: litmus-level evidence (unvalidated reading until herd7 is run); theorems relative to the table-induced memory, grounded in x86-TSO". This contradicts the author's ARMv8 goal for LatchSet and must be said explicitly.
- **Load buffering is never observable on x86.** On ARMv8 it is observable only through a client cell (D), and write-snapshot never exercises it. The in:106 "layered" LB claim cannot be made true without changing its meaning.
- **Write-snapshot.** The definition is open. The write-snapshot proof is D. Complete executions only. The one-shot and P1/P2 discharge obligations are new. If the author keeps the Wmb export, M_WS needs an explicit insert wait, and the paper's write-snapshot code must show it.
- **Vertical composition and observational refinement.** Both are XL or research. Reviewer A calls inlining unsound (popl2027-reviews.md:166-168). The observational-refinement proposition may be ill-posed without saturation for concurrent modules (Appendix/relaxedlin.tex:53-56). Expect to reword it.
- **Reviewer conflict.** Keeping rhb clause (i) thread-agnostic goes against popl2027-reviews.md:108-110. It is needed both for OOTA rejection and for CE1's refutation (`rt_ins_mem_false_not_rel_lin` uses only clause (i)).
- **Scope of every module theorem:** complete executions, P1/P2, hand-written tags unless the audit lemma exists, and a G-1 link that does not exist yet.
- **Evidence status.** These results are Ks and must not be cited as Coq results until committed: `sb_ws_*`, `wf_forces_local`, `only_local`, `latch_exports_not_rect`, `tso_not_compatible`, `arm4_compatible`, `compat_local_forces_local`, `md_false`/`md_true`, `latch_drain_exports_rect`.
- **Stale records to fix:**
  - research-intent.md:147 cites ov:278/300/329; the current lines are ov:316/333/335.
  - `WindowTable.latch_*` (WindowTable.v:525-545) encode the older DW/DR design, not plan §5.
  - todo-oopsla-v2.md:25 marks OOTA done on the basis of Litmus.v, which has no dependency edges.
  - Mem.tex:819 still says RC11 is not mechanized, although RC11.v mechanizes it.
  - `Cor. mem:cor:rlxlin` (Mem.tex:231) is undefined.
  - The mapper's citations IntervalWindow.v:52-54 and PrefixView.v:1004 are wrong.
- **If the author rejects the drain.** These claims then cannot be supported and must be reworded or withdrawn:
  - ov:316, :333, :335 (atomic set and atomic update);
  - ov:337's fence-mode and compatibility sentences (degenerate or refuted);
  - ov:339's end-to-end write-snapshot, which then needs an exported `sync` operation, and that operation needs the same drain primitive;
  - in:7, in:89, in:99, in:106.

  Keeping ν_BS also reopens FM-13 (relaxed tensor, research).

**Relevant files:**
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/LatchSetRT.v
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/WindowTable.v
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/WindowLinkTable.v
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/WindowLinkTableJ.v
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/BracketedComposition.v
- /Users/index/Documents/GitHub/rbgs/memory/TableBarrier.v
- /Users/index/Documents/GitHub/rbgs/memory/TableBarrierTSO.v
- /Users/index/Documents/GitHub/rbgs/memory/TSO.v
- /Users/index/Documents/GitHub/rbgs/memory/ARMBar.v
- /Users/index/Documents/GitHub/rbgs/memory/Cell.v
- /Users/index/Documents/GitHub/rbgs/models/simlin/RelaxedTraceLin.v
- /Users/index/Documents/GitHub/rbgs/models/simlin/RelaxedModuleSemantics.v
- /Users/index/Documents/GitHub/rbgs/.rocq-review/latchset-plan.md
- /Users/index/Documents/GitHub/rbgs/.rocq-review/research-intent.md
- /Users/index/Documents/GitHub/rbgs/.rocq-review/iteration-log.md
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/overview.tex
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/intro.tex
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/Claude outputs/litmus-check/tests_latch_set.py