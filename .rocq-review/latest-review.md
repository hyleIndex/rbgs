<!-- WHWQ review gates 4 and 5 (iterations 6 and 7, 2026-10-21), saved by the orchestrator. Two independent read-only rocq-research-reviewer runs, in parallel: gate 4 on P5b–P7 (POQueueRD, WHWQInv, WHWQProof, WHWQDeq, T4), gate 5 on P8 (WHWQTop, T5, T6). Verbatim, except that the gate-5 scripts are replaced by a pointer to WHWQTop.v, where they were adopted. Both reviewers cite popl2027-reviews.md by line, with their own paraphrases. The orchestrator's dispositions are in .rocq-review/tasks/WHWQ.md ("Gate 4", "Gate 5"). The gate-3 reports and earlier ones are kept below. -->

# Gate 5 review (P8): the weak Herlihy–Wing queue — iteration 7, 2026-10-21

## Scope
- **Repository state:** branch `rlhl` at HEAD 8549663, plus the uncommitted `examples/Relaxed/WHWQ/` and `_CoqProject` (+13 lines).
- **Under review:** `WHWQTop.v` and `.rocq-review/tasks/WHWQ.md`.
- **Inputs:** T4 (`whw_rlhl2`) and T2D (`poqrd_sound`) are taken as given.
- **Concerns:** B6, C2, B (mechanization).
- **Discipline:** I wrote no files.

## Checks I ran
- **Build:** `make -n …/WHWQTop.vo` reports it up to date, and no WHWQ `.v` is newer than its `.vo`.
- **Print Assumptions:**
  - `whw_complin` uses `classic`.
  - `whw_rel_lin`, `whw_rel_lin_sharp`, `whw_b6`, `whw_b6_Tb6ov` and `whw_consistency` use `eq_rect_eq`.
  - Closed: `whw_trace_wf`, `whw_rsim`, `whw_future_dependent_lin`, `whw_rlhl2`, `poqrd_sound`, `whw_not_rel_lin_empty_all`, `Tb6ov_mtraces`, `b6_returns`, `future_dependent`.
  - This matches the header.
- **Grep of `examples/Relaxed/WHWQ/*.v`:** no `Admitted`, `admit`, `Axiom`, `Parameter`, `vm_compute`, `native_compute` or `Unset … Checking`.
- **Toplevel, piped input:** `b6_enq_first` (uses `eq_rect_eq`) and `Tinc_no_path_D` (closed) are both accepted. Their scripts are at the end.

## Verdict
T6 is what decision D1 asks for. It is universal, it does not mention the presentation, it covers every complete trace of `Mwhw` over `EI δRC` (under D2′/D3′), it is sharp against ∅, and the witnesses that make it non-vacuous are interesting ones. There is no Coq BLOCKER.

Four problems remain:
- The B6 corollary is described wrongly for the dequeue-first order, and it does not depend on I at all.
- T5's prefixes absorb an artifact of the module semantics, so no claim about prefixes of the queue is available.
- The P8 records were not updated.
- The TR still prints a proof that the kernel refutes.

Continue: the actionable findings go to the Writer; g5-2, g5-3 and the carry-overs go to the authors. The queue proof needs no redesign.

## Answers to Q1–Q7

**Q1 — what T5 and T6 say.**
- **T5 (S):**
  - For every `s` with `∃ evs c` such that `module_execution_tagged (EI δRC) Mwhw init(mem0,[]) evs c` and `overlay_events evs = s`, we get `RTraces (POQueueRD positive) poqr_init s`.
  - It covers executions of any length and pending calls. It has no error clause. It mentions the presentation.
- **T6 (S):**
  - Hypotheses: `MTraces (EI δRC) Mwhw (mem0,[]) s` and `complete s`.
  - Conclusion: there is a witness `W` with `νQ W`; `W` contains each call of `s` once, with its result; and `W` preserves rhb under `qsi = {(enq _, deq)}`.
  - `νQ = seq_legal δQ []`, where `deq` has no transition on `[]`.
  - Effects happen at invocation. Every weak behaviour comes from `must_precede` (RelaxedModuleSemantics.v:252–259) under `rc_si`.
  - T6 covers complete traces only, so it cannot feed a layer above the queue.
- **Decisions:** T6 meets D1. T5 meets D5 only in a weak form (see g5-3).
- **P:**
  - The main text has no queue (main.tex:229, :260; intro.tex:106).
  - The TR describes a different object:
    - an exchange with `rel` (WHWQueue.tex:17);
    - an RCMem with no RMW pairs (2Counter.tex:13);
    - a single-possibility proof with the linearization point at the store (:53, :65, :91, :150);
    - `ν_queue` and `I_WkQueue` that are not defined anywhere.
- **Header:** its scope statements are accurate (`absorb` is still PENDING), except where g5-1, g5-3 and g5-5–g5-7 apply.

**Q2 — non-vacuity.** Yes.
- `Tw`, `Tf 1/2` and `Tb6ov` are complete module traces.
- `Tb6ov` is not a `POQueueR` path, so T6 really goes through the reordering between the abstract and the concrete trace.
- `Tk` shows that rel_lin under `qsi` is not trivial on complete, well-formed traces.
- `whw_consistency` only re-derives facts already proved.

**Q3:** g5-5. **Q4:** g5-1 and g5-2. **Q5:** g5-4, the carry-overs and the proposed wording below. **Q6:** under "Checks I ran". **Q7:** the last section.

## Findings

### WHWQ-g5-1 — MAJOR (actionable; the paper wording is research-level): for the dequeue-first order `whw_b6` is vacuous, and the header misdescribes it
- **S/K:**
  - (deq, enq) is not in `qsi`. So a dequeue invoked first is rhb-before the enqueue.
  - But every witness is `[enq v; deq→v]` (`b6_enq_deq`).
  - So no complete module trace has the dequeue invoked first: `b6_enq_first`, checked in the kernel.
- **Header and task file:**
  - WHWQTop.v:37–41 attributes the exclusion to real time and suggests a non-vacuous case.
  - WHWQ.md:257–260 says this case handles g3-6.
- **R:**
  - Review B (popl2027-reviews.md:261–276) has the dequeue invoked ahead of enq(1).
  - The B6 response (:541–545) leaves termination out.
  - Then no execution completes: the client blocks (argued for the module) where the inlined code would complete (argued).
- **Fix:**
  - Add `b6_enq_first`.
  - Rewrite WHWQTop.v:35–44 and WHWQ.md:257–260 to say that in the dequeue-first order there is no complete trace, so the guarantee is only that the execution does not complete.

### WHWQ-g5-2 — MAJOR (research-level): `whw_b6` does not depend on I
- **K:**
  - `b6_enq_deq` throws away the rhb component of the witness (POQueueRExample.v:371, `& _`).
  - So it holds for every relation, including the full one.
  - Review B's example is excluded by the blocking δQ together with the closed-world hypothesis, not by the choice of I.
- **R:** Review B's general concern (a fixed I admits behaviours the code lacks, at a cost to clients) still stands:
  - `T0` is admitted by (νQ, I) but argued unproducible by the code (g3-7 is open);
  - a client may reorder its own calls (g5-1).
- **Fix:** present B6 as answered by the blocking API, for any I. Never present it as validating I.

### WHWQ-g5-3 — MAJOR (research-level): T5's prefixes absorb abandoned dequeues, and no prefix-level claim about the queue exists
- **S — how abandoned dequeues arise:**
  - `poqrd_dead` is a dequeue invocation with no effect. T4 needs it (WHWQDeq.v:1192, WHWQInv.v:1355).
  - The reason is C7: responses are committed at the invocation.
  - A dequeue whose last `xchg` mismatches is stuck with nothing left in its queue.
  - `must_precede` blocks invocations only behind tagged responses, so the later calls of its thread run.
- **Argued, from the C7 prefix (WHWQ.md:192–197; not in Rocq):**
  - **Not in `RTraces (EI δQ)`:** an emitted `deq` always consumes a value (RelaxedHoareSpec.v:310). (F2) forces t1's `deq` to be emitted before `enq(b)`, so it takes `a`, which t4 later returns.
  - **Not a REW prefix:** the pending `deq` can neither be completed nor dropped past `enq(b)`.
  - **Consequence:** the M-20 form, RCompLin into `EI δQ`, is expected to be false for `Mwhw`.
  - The real code would keep `enq(b)` waiting behind the `deq`'s acquires. So this is an artifact of the semantics, not of the code.
- **P:** intro.tex:106 claims trace inclusion for every prefix for SeqLock. The paper must not make that claim for the queue.
- **Fix:**
  - Say this in the Scope section of WHWQTop.v and in the T5 entry of WHWQ.md.
  - Optional: check the C7 prefix in the kernel.
  - Authors: decide whether the module semantics should allow abandoned calls.

### WHWQ-g5-4 — MINOR (actionable): the P8 records are missing
- These still say "RLHL proof and T6 pending":
  - concern-matrix.md:33, :46, :109, :115, :235;
  - research-intent.md:99–101.
- iteration-log stops at P5.
- WHWQ.md:312 marks "concern matrix B6/C2" as done.

### WHWQ-g5-5 — MINOR (actionable): WHWQTop.v:31–34 does not carry the scope of the necessity result
Carry over the g3-1 scope:
- the separating execution needs D2′/D3′ (`store_xchg_D2_ordered`, `store_xchg_rel_ordered`; in general this is argued);
- the reordering is RCpc-style, and is argued to be forbidden on x86-TSO and ARMv8;
- only clients that overlap their own calls can observe it.

Also say that necessity is shown against ∅ only, not against value-restricted sub-relations.

### WHWQ-g5-6 — MINOR (actionable): "neither is [POQueueRD]" (WHWQTop.v:18–20) is not proved
Add `Tinc_no_path_D` (below).

### WHWQ-g5-7 — MINOR (actionable): WHWQTop.v:218–221 says the future decides the order "at the module level"
`Tf 1` and `Tf 2` come from executions with different FAA orders (g3-5). Say "at the trace level", and cite `whw_future_dependent_module` for the module level.

### WHWQ-g5-8 — MINOR (actionable): stale text
- WHWQExec.v:82 and :116 still describe P8 work as pending.
- POQueueRExample.v:43 should point to `whw_b6`.
- WHWQ.md:30 and :43 still defer the C7 decision "to P8". Record the decision, or mark it open.

## Carry-overs
- **Still open:** WHWQ-g3-7 (T0 unproducible), the C7 impossibility proof, WHWQ-g3-1, WHWQ-m-4.
- **WHWQ-M-1 and WHWQ-M-2:** the TR still prints the following.
  - WHWQueue.tex:17: the `rel` exchange.
  - 2Counter.tex:13: "no RMW pairs".
  - The proof with the linearization point at the store (:65, :91, :150), which `Tf1_atomic` together with `future_dependent` refutes.
- By the review rubric, a printed claim the kernel refutes is BLOCKER-level for the paper. Rewrite these before the TR is used.

## Concern-matrix corrections (proposed text)
- **B6 🟡:** "Spec: for one thread's `enq v; deq`, every witness is `[enq v; deq→v]`, for any I. Implementation (`whw_b6`, `eq_rect_eq`): in every complete trace whose only calls are these two, the dequeue returns v. Non-vacuous for the overlapping order in which the enqueue is invoked first (`whw_b6_Tb6ov`). If the dequeue is invoked first, there is no complete trace (`b6_enq_first`) and the client blocks (argued). Open: `T0`; no client theorem; termination is excluded (:545)."
- **C2 🟡:** "Over `EI δRC` with D2′/D3′: I(enq, deq) suffices and ∅ does not. The separating execution needs D2′/D3′, is RCpc-style (argued to be forbidden on x86-TSO and ARMv8) and is visible only to clients that overlap their own calls. Not shown: minimality, precision (`T0`), adequacy for clients, or the printed variant."
- **Queue:** "Module, T4, T5 and T6 done. Cite T6. Cite T5 only as copy-cat inclusion into `POQueueRD`."

## What the paper may claim
"For the WHW queue with the exchange (acq, rlx), over RCMem with the tensor-rule semi-independence (RMWs taking part by their join modes), presented by its register file with effects at invocation: every complete trace from the empty queue is relaxed-linearizable to the FIFO queue with a blocking dequeue under I = {(enq, deq)}, and not under ∅. The proof is RLHL with one possibility over a partial-order overlay presentation, whose soundness is proved separately."

The paper must not claim:
- verification "in VLHL" in the App. J sense;
- anything for every prefix;
- the result for every implementation of RCMem;
- weak behaviour at the hardware level;
- that I is minimal or precise;
- client or termination guarantees;
- the result for the printed variant.

## Stronger or alternative approaches
1. **`b6_enq_first`** (below).
2. **A prefix-level B6 from T5.** In `POQueueRD`, a dequeue response needs a complete minimal vertex. So in every trace, complete or not, a dequeue that returns returns v, and a dequeue invoked first never returns.
3. **Robustness of T6.** The module semantics reads only `semi_independent`, never the modes. A monotonicity lemma in the underlay relation, plus a renaming of the exchange's mode, would transfer T6 to the printed variant.
4. **Kernel form of C7:** either prove that no `GSimRel` over `POQueueR` exists, or prove that the C7 prefix is not in `RTraces (EI δQ)`.
5. **Composition with a client:** not possible yet, because `absorb` and vertical composition are missing.

## Redesign assessment
None for T6. Claims about prefixes need the semantics question of g5-3 settled first.

## Scripts (piped into the toplevel, nothing written)

The two lemmas were adopted in `WHWQTop.v` as `whw_b6_enq_first` and `Tinc_no_path_D` (with `POQueueRD_incomplete`, `POQueueRD_not_complete_pres`); see that file for the final text.

---

# Research review, iteration 6 (task WHWQ, gate 4), 2026-10-21

## Scope
- **Repository state.** HEAD `8549663` on branch `rlhl`. Uncommitted changes:
  - `examples/Relaxed/WHWQ/` (untracked);
  - `_CoqProject` (+13 lines, registering the WHWQ files);
  - the `.rocq-review` records.
- **Files reviewed in full.** `POQueueRD.v` (P5b), `WHWQInv.v` (P6), `WHWQProof.v` and `WHWQDeq.v` (P7, T4).
- **Context.** `WHWQ.md`, `WHWQProg.v`, and the framework: `RelaxedHoare{Base,Dag,Run,Ready}.v`, `must_precede`, `ei_step`, `sound_pres`.
- **Paper.** `Appendix/WHWQueue.tex`, `programlogic.tex`, `impl.tex`.
- **Concerns in scope.** Review B on the mechanization (popl2027-reviews.md:249–255), WHWQ-M-2, C7.

## Checks I ran
- `make -n …/WHWQDeq.vo …/WHWQTop.vo`: nothing to rebuild (Rocq 9.2).
- `Print Assumptions` returns "Closed under the global context" for `whw_rlhl2`, `deq_provable`, `enq_provable`, `poqrd_sound`, `poqrd_complete_path`, `whw_rlhl2_of_provable`, `iq_init` and `dnew`.
- `Check` gives:
  - `poqrd_sound : sound_pres (νQ ?A) (POQueueRD ?A) poqr_init`;
  - `whw_rlhl2 : RLHL2Hyps Iq Rq Gq Mwhw (mem0, nil, nil) poqr_init`, with VE = `EIhl ERC Mem δRC` and VF = `POQueueRD positive` (shown with `Set Printing Implicit`).
- Grep for `Admitted|admit|Axiom|Parameter|Conjecture` in `examples/Relaxed/WHWQ`: 0 hits. Section hypotheses appear only in the gate-1 files. There is no `vm_compute` or `native_compute` in `models/`, `models/simlin`, `models/view` or WHWQ.
- `iq_xchg_dead` and `vf_dead` are used exactly once, at WHWQDeq.v:1193.
- `WHWQTop.v`:132, 142, 151 take `whw_rlhl2` and `poqrd_sound` unchanged.

## Verdict
P5b–P7 establish what they are cited for:
- **K.** Everything is closed and the build is up to date.
- **S.** The statements are the targets in WHWQ.md.
- **Derivations.** They are honest: own interference is checked pairwise, not assumed, and nothing in `RLHL2Hyps` is discharged vacuously.
- **Dead step.** It is sound by a kernel-checked counting argument, and it is used only in the intended case.

The main new issue is at the paper level. Doomed dequeues follow from the paper's own Inv rule (impl.tex:212). Neither the TR proof nor any proof over the atomic `POQueueR` handles them. This adds to the required WHWQ-M-2 rewrite. No redesign is needed. **Gate 4 passes; continue to gate 5.**

## Answers to the gate-4 questions

**Q1 (C7 / POQueueRD).**
- **What the step is.** `poqrd_dead` (POQueueRD.v:85–93) is a dequeue invocation that leaves `POQReady s` unchanged.
- **Soundness.** `poqrd_count` (:161) and `deq_inv_res_count` (:228) together show that a complete, well-formed path has no dead step (:266). `poqrd_sound` is then exactly `sound_pres (νQ A) (POQueueRD A) poqr_init` (checked with `Check`).
- **Minimality.** Only dequeues need the step:
  - an enqueue at `ls_inv` owns its FAA, which blocks the first invocation (`ld` or FAA, both at location 0) of every later call of its thread;
  - an enqueue whose FAA response mismatches has already taken AInv at its FAA.
- **The C7 analysis is right.** I re-checked the hand counterexample by reasoning:
  - t1.enq(b)'s AInv needs t1's deq out of `ls_inv`.
  - In `POQueueR` that means entering `POQAtomic s t1`, where only t1's deq response is enabled. That response must remove a complete, minimal vertex before b exists, so only a is available, and only if a was completed early.
  - t4's response a then has no live vertex.
  - This holds for any forward simulation, with one possibility or a set of them.
  - It needs neither D2′ nor D3′: (F2) only orders invocations, and the FAA is untagged.
- **Use in the proof.** The dead step is used only in `upd_xi` (WHWQDeq.v:1191–1201), when the record is 0 and `kg k γ' = []`, i.e. the emitted xchg is the last invocation of the committed trace. `iq_xchg_dead` itself does not require "last", which is harmless: a dequeue killed early could not take a later vertex.

**Q2 (fidelity of Iq, Rq, Gq, Oq, Qq).**
- **Iq** (WHWQInv.v:215–235) is the intended invariant:
  - the counter equals `poq_next`;
  - `CellOK`: a cell is 0 unless its vertex is complete and live, and then it holds that vertex's value;
  - `Coup`, `iq_pend`/`iq_uniq` (one pending vertex per thread), `Ord` (the cross-call (F2) order at the FAA), `GAge` and `poq_wf`.
- **Non-vacuity.** `iq_init` is closed. Every `EvUpdate` must re-establish Iq, so Iq holds along every execution.
- **Rq and Gq** are per call key, so other calls of the same thread count as environment. The three rely fields are genuine; `invoke_rely` even holds for an arbitrary `tr`.
- **Oq** matches `enext`/`dnext`:
  - enqueue: `[FAA; store i (Pos.to_nat v)]` with distinct handles;
  - dequeue: `ld`/`xchg` invocations of the thread, no duplicate handles, the last an xchg.
  - It is checked at Close on every derivation path (`eclose`, `dclose`:1518–1530).
- No field is weakened, and T4 is what P8 needs.

**Q3 (linearization points and the gate-3 watch list).**
- ARet is taken at the store's invocation (`upd_e2`).
- The rely is per key, so same-thread interference is covered in both directions.
- `GAge` works with an older store pending (`no_pending_at_faa`, `emit_ready_block_older`; `ghost_emit` rules out blocked emissions).
- `ScanC` is state-based and stable under `AMono` (`scanc_mono`:1483).
- Retry loops and t = 0 are covered: `dcall_ld` with r = 0 and `dcall_x` with r = 0 both go back to `DLd (S n)`.
- g3-11 holds: an `ld` slot asserts only the chain edge (`dkind`), and the chain is stable under responses.
- **Deviation.** Readiness at a dequeue's AInv is not argued through the leading `ld`. `deq_ready` (:1232) uses `emit_ready_mixed`, crossing older `ls_inv` enqueues by `qsi` (:1240). This is a convenience only: an older enqueue's FAA always precedes the dequeue's `ld` (same location).

**Q4 (WHWQDeq design).**
- **`dnew`.** Every asserted in-edge is shown to be an edge of the actual dag (:871–887).
  - `ns_if_new_in` (:938–973): only responses can fall in a chain edge's window; only `ld` invocations and responses fall in the other windows (`inv_before_all`, `lastx_spec`).
  - `ns_if_old_in` (:978–996): only the invocation→own-response edge can be open, and a new xchg comes after it (`res_before_x`).
- **Status edge.** It is a real tag edge. `XZero` gives `XFacts tl s 0`, which refutes the `ls_linr` case of the chain.
- **`XZero` and `dinv`** are history facts that every call re-establishes; neither is circular.
- **`dclose`.** Every slot precedes the last response, so `XLast x` gives `Qq`.
- **Dummy response value** (:1324, :1394). It only builds the run context needed to read `dprec`/`before` on positions ≤ p, and the `NewSlotOK` conclusion does not mention it. Harmless.

**Q5 (headers).** They are accurate where they speak; the gaps are in g4-3.

**Q6 (K level).** See "Checks I ran".

**Q7 (alternatives).** See the end of the report.

## Findings
### BLOCKER
None.

### MAJOR
- **[WHWQ-g4-1] The paper's RLHL proof of the queue, and its readiness account, do not cover doomed dequeues; the mechanized proof needs `POQueueRD` (research-level, paper).**
  - **Where.** POQueueRD.v; WHWQDeq.v:1191–1201; WHWQ.md:178–220. Paper: WHWQueue.tex:65 (the enqueue's TInvoke needs no earlier pending same-thread operation), :144–150 (the dequeue at a successful exchange), programlogic.tex:712 (readiness through pending ghost entries).
  - **K.** `poqrd_sound` is closed.
  - **S.** T4 is stated over `POQueueRD`; T6 does not mention the presentation (D1).
  - **P.**
    - The paper's Inv rule fixes the guessed response values of a call at invocation (impl.tex:212), and EI fixes the actual result at invocation. A dequeue whose last exchange is guessed non-null but reads null never responds, and it owns no pending invocation.
    - The TR proof linearizes a dequeue only at a successful exchange, so the TInvoke of a later enqueue of the same thread (:65) is never ready.
    - This is a second failure of the TR proof, besides WHWQ-M-2's. It is independent of D2′/D3′, and it also defeats a rewrite over the atomic `POQueueR`.
  - **R.** Review B (popl2027-reviews.md:249–255) asks for complete mechanized proofs or clearer pen-and-paper ones. A rewritten section that leaves out C7 would describe a proof that cannot be carried out.
  - **Required.**
    - In the M-2 rewrite, present the dead dequeue step and the counting argument.
    - Explain doomed calls as a consequence of commitment at Inv over an underlay with effect at invocation.
    - Add to programlogic.tex:712 that a call with no pending invocation, which can never respond, needs an abstract invocation that consumes nothing.
    - Recommended: kernel-check the impossibility over `POQueueR`, after the pattern of `RelaxedHoareChecks.counter_vt_no_rlhl2`.

### MINOR
- **[WHWQ-g4-2] The tag-irrelevance claim is false on incomplete executions, and P7 depends on the tags (actionable).**
  - **Where.** WHWQProg.v:40–48; WHWQ.md:171–177 (C6).
  - **Evidence.** (F3) is the only response→invocation edge (`must_precede`). With a doomed call, the tags become visible:
    - (a) Without the store's address tag, a doomed enqueue (FAA record n, guessed i ≠ n) emits `store(i, v)` after its FAA invocation and can overwrite another enqueue's value.
    - (b) Without the κ tags (each xchg tagged with every earlier call), a doomed dequeue's next xchg does not wait for the mismatched response. Example: t1 enqueues a, b, c (all complete); t2's xchg(0) takes a while its guessed response is 0, then xchg(1) takes b; t3's dequeue then returns c while t2 is still pending. With κ this is impossible, because t3 would find b.
    - This also contradicts the purpose of tags given in impl.tex:212.
  - **Dependence of P7.** The derivations use these tag edges: the edge 1→2 in `WHWQProof` (:193, `EA1`), and the `EkPrev`/`EkStatus` edges in `WHWQDeq`.
  - **Required.** Restrict the claim to complete executions, where every response matches its record. State in the `WHWQProof` and `WHWQDeq` headers that the proofs rely on the hand-written address and κ tags (C6).
- **[WHWQ-g4-3] Headers lack K lines and limitations, which CLAUDE.md requires (actionable).**
  - `WHWQInv` and `WHWQProof` have no `Print Assumptions` line.
  - None of the three P6/P7 headers states:
    - (i) the scope: over `EIhl δRC` only, an atomic underlay, where the weak behaviour comes only from the frontier (WHWQ-g3-1, M-22);
    - (ii) that VF is `POQueueRD`, which allows dead dequeues on incomplete traces, and that the impossibility over `POQueueR` is only argued;
    - (iii) where I(enq, deq) enters the proof: `deq_ready`, as a convenience, and essentially only in HVF (`poqr_sound`). The paper says otherwise: WHWQueue.tex:63 and :148 place it at TInvoke;
    - (iv) that the proofs depend on the tags (g4-2).
  - POQueueRD.v:21 says "cannot take its abstract invocation". It should say "can take it only together with its response, which needs a removable vertex".
- **[WHWQ-g4-4] The records are out of date (actionable).**
  - WHWQ.md:497–499 says readiness at a dequeue's AInv uses the leading `ld`; the proof uses `qsi` (WHWQInv.v:1240).
  - WHWQ.md:207–209 says programlogic.tex:712 assumes every unlinearized call owns a pending ghost entry. That sentence describes the SeqLock invariant. Reword it to: "the paper's only readiness argument, through pending ghost entries, does not cover a call without pending invocations".

## Responses to Writer disputes
None.

## Concern-matrix corrections
- **Row 46 (B6, C2).** Replace "The RLHL proof, T6 and … are due at P6–P8" with: T4 `WHWQDeq.whw_rlhl2` (`RLHL2Hyps` over `EIhl δRC`, VF = `POQueueRD`) and `POQueueRD.poqrd_sound` are both closed; C7 is recorded; the T6 and B6 parts await gate 5.
- **Row 109.** Change "RLHL proof and T6 pending" to "RLHL proof done (T4, closed, over `EIhl δRC`); T6 at gate 5". The mechanization concern (Review B :249–255) is addressed over EI δRC. The correspondence with an RC memory model (:245–247) is still open.

## Stronger or alternative approaches
1. Kernel-check the C7 impossibility (g4-1), and add to `WHWQExec` an execution with a doomed dequeue and one with a retry, so that both derivation branches are shown reachable.
2. Generalize `poqrd_count`: if a presentation enables responses of op o only through a token created by o's invocation, then adding a state-preserving invocation of o keeps `sound_pres`. This would be reusable for other destructive objects.
3. If more case studies run into doomed calls, consider the framework-level drop rule (C7 option 3).
4. Prove the complete-execution form of tag irrelevance (g4-2).

## Redesign assessment
None needed. The derivations are sound and honest. The remaining work is in the records and in the paper's text.

---

<!-- WHWQ review gate 3, follow-up (iteration 5, 2026-10-21), saved by the orchestrator. Same read-only rocq-research-reviewer run as iteration 4 (resumed). Verbatim except that absolute paths are made relative; the reviewer cited popl2027-reviews.md by line with its own paraphrases. The orchestrator's fixes of g3-8 … g3-11 follow the report. Iteration 4 and the gate-1 reports are kept below. -->

# Research review — iteration 5 (task WHWQ, gate 3 follow-up) — 2026-10-21

## Scope

- **Repository state.** rbgs, branch `rlhl`, HEAD `8549663`, with all work uncommitted. Paths below are relative to it.
- **Changed since iteration 4:**
  - `examples/Relaxed/WHWQ/WHWQProg.v` (430 lines, 18:34);
  - `examples/Relaxed/WHWQ/WHWQExec.v` (940 lines, 18:38);
  - the records: `tasks/WHWQ.md` (403 lines), `latest-review.md`, `concern-matrix.md`, `research-intent.md`, `iteration-log.md`.
- **Unchanged:** the gate-1/1b files (source mtimes at or before 14:50) and `_CoqProject`.
- **In scope:**
  - the fixes for WHWQ-g3-2, g3-3, g3-4, g3-5 and g3-7;
  - stronger approach 1 (`rel_lin_no_self_overlap`);
  - the scan-race pair;
  - the records.

## Checks I ran

**Build**
- `make -n` of `WHWQExec.vo` and `WHWQProg.vo` reports both up to date.
- `make -n` of the whole tree schedules no compile step.

**Print Assumptions: 35 of 35 "Closed under the global context"**
- The 13 new results:
  - `Tw_atomic`, `Tb6ov_atomic`, `Tf1_atomic`, `Tf2_atomic`, `mtraces_atomic`;
  - `rel_lin_no_self_overlap`, `Tw_self_overlaps`;
  - `whw_scan_race`, `Sr1_rel_lin`, `Sr2_rel_lin`, `Sr1_order`, `Sr2_order`, `whw_future_dependent_module`.
- The 22 results of iteration 4, re-checked after the tag change.

**Grep**
- There is no `Admitted`, `admit`, `Axiom`, `Parameter`, `Hypothesis`, `Variable`, `Unset`, `vm_compute`, `native_compute`, `Opaque` or `Abort`.
- The only `Context` is `{E : RelaxedSig.t}` in `Section NoSelfOverlap`. It is generalized at the end of the section.

**Statements read in the kernel**
- `rel_lin_no_self_overlap : ∀ E L indep nu, wf L → no_self_overlap L → (rel_lin L indep nu ↔ rel_lin L ∅ nu)`.
- The definitions of `no_self_overlap`, `ul_atomic`, `MTracesAtomic`, `Sr1` and `Sr2`.
- I also read every new proof script.

**Tags compared with the paper**
- The sources are programlogic.tex:109 (the memory policy), :163–172 (tag D and the address rule) and :209–210 (an assert adds to κ).
- The FAA is control-ordered, but κ is empty at the start of `enq` and its arguments are constants, so its tag is ∅.
- Every `ld` is a plain read, so its tag is ∅.
- The store's tag is {FAA}.
- Each `xchg`'s tag is κ, which is every earlier call of the dequeue.
- These are now exactly the paper's tags.

**Verbatim-wording scan**
- I ran a read-only n-gram scan (python on stdin/stdout, no files written) of the lines added to the four tracked records, of the untracked task file, and of both `.v` headers, against `popl2027-reviews.md`.
- At 6 words, the only overlap is the concern's own title (the queue name plus `enq(1); deq()`). At 4–5 words the overlaps are generic.
- A grep found one quoted two-word phrase from Review B (:265–266). It predates this iteration (see g3-10).

### Answers to the five questions

**1. Do the fixes resolve their findings?**
- **g3-2: resolved.** "Over EI δRC" now appears wherever T7(c) is stated. `ul_atomic` is proved for `Tw`, `Tb6ov` and `Tf1`/`Tf2`, and `Tb6ov` is reordered.
  - What remains is g3-9: the atomicity claim also covers the scan race, which does not prove it, and three statements went stale after the reorder.
- **g3-3: resolved.** The tags are exactly the paper's. The header gives the policy and marks tag-irrelevance as argued.
  - What remains is a records item, g3-11.
- **g3-4: resolved.** One nit is left (g3-9).
- **g3-5: resolved,** but the new conclusion sentence about the scan race overstates (g3-8).
- **g3-7: resolved.** The deferral of T0 is recorded in the header and under T7.

**2. Closed:** 35/35 (above).

**3. `rel_lin_no_self_overlap`: right on complete traces, and the direction is right.**
- **The notion.** On a complete trace, `no_self_overlap` is exactly per-thread alternation, i.e. SC well-formedness (trace.tex:35).
- **Incomplete traces.** There it ignores an earlier call that never returns: `[inv k; inv k'; res k']` satisfies it, although the thread does overlap. This is harmless, because `RelaxedTraceLin.rel_lin` is complete-only: it is false on such traces under every relation, so the equivalence holds trivially. But the notion would be wrong for the paper's append/drop version of incomplete traces. Optionally, add `complete L` or a remark.
- **The two directions.** The ← direction is `rel_lin_mono`. The → direction turns each same-thread order edge into a real-time edge, using `wf` to get k ≠ k′. The lemma is generic in `E`.
- **`Tw_self_overlaps`** is the correct contrapositive, via `Tw_rel_lin` and `Tw_not_rel_lin_empty`.
- **The header's use is correct as a necessary condition.** For `qsi` against ∅, the sharper condition (an `enq` followed by an overlapping `deq` of the same thread) is true but not stated, which is fine.

**4. `whw_future_dependent_module` supports a precise form of the sentence, not the sentence as written (WHWQ-g3-8).**
- The theorem proves the following:
  - there is one reachable configuration c₀, with overlay trace `Pre_r`, in which enq(2) has returned and enq(1) is pending;
  - two continuations from c₀ produce `Sr1` and `Sr2`, both relaxed-linearizable;
  - every witness of `Sr1` orders enq(2) first, and every witness of `Sr2` orders enq(1) first.
- **What follows (argued):**
  - (a) No total order of the operations invoked so far can be fixed by the execution prefix and kept in every continuation.
  - (b) No proof can exist that linearizes each call by its return and only appends, in particular no `GSimRel` with VF := `EI δQ`. `gsim_step` (RelaxedGSim.v:340–350) must match every step from a related pair, and requires enq(2) to be linearized at its return; every possibility at c₀ then fails one of the two continuations.
  - This is robust to the semantics fixing a method's trace at its invocation: c₀ precedes t3's invocation, and no active call's queued events depend on the dequeue.
- **What does not follow:**
  - "a single forward possibility cannot work at the implementation level": a single possibility over `POQueueR`, the route of D1 and T4, keeps the two vertices unordered at c₀;
  - "no linearization that is a function of the execution so far" without (a)'s or (b)'s qualifiers: a function may postpone placing pending calls and insert them later.

**5. Records:** accurate apart from the points in g3-9, g3-10 and g3-11. The research-intent sub-bullet and the iteration-log entry are accurate. `latest-review.md` holds my iteration-4 report verbatim, with relative paths, and the orchestrator note is accurate.

## Verdict

The fixes resolve g3-2, g3-3, g3-4, g3-5 and g3-7 in the Coq. All 35 results are closed, and the dequeue's tags now follow the paper's policy exactly.

There is no BLOCKER and no new MAJOR. There are four MINOR findings, all in documentation or records. The one to fix before anything cites it is g3-8: the scan-race sentence claims more than the theorem gives, and contradicts the project's own `POQueueR` route.

Gate 3 passes. P6 can start.

## Findings

### BLOCKER

None.

### MAJOR

None new. WHWQ-g3-1 stays open (research-level, for the authors); its scope is now stated in the header and in the records, subject to g3-10.

### MINOR

- **[WHWQ-g3-8] The scan-race conclusion is stated for every forward proof, but holds only for proofs over the sequential queue (actionable)**
  - **Where:**
    - `WHWQExec.v:97–100` and `:756–759`;
    - `tasks/WHWQ.md`, the T7(a) bullet, and `concern-matrix.md:46`, both of which call the theorem "a kernel-checked form of WHWQ-M-2".
  - **K / S:** the theorem is closed. It states two executions and the forced orders, and nothing about proofs (answer 4).
  - **P:** the claim it should be tied to is the TR's single possibility, which appends each enqueue at its store (WHWQueue.tex:53, :65 and :91).
  - **Required.** Replace the sentence. Suggested wording: "So at the common configuration, where enq(2) has returned, the relative order of the two enqueues is not yet determined. A proof that must fix it by enq(2)'s return fails on one of the two continuations. That includes a forward simulation against the sequential queue (`GSimRel` with VF := `EI δQ`) and the TR's single possibility (Appendix/WHWQueue.tex:53, :65, :91; WHWQ-M-2). This is argued from the theorem. A single possibility over `POQueueR`, which T4 uses, is not affected: there the two vertices stay unordered."
  - **Also:** write "kernel evidence for the first part of WHWQ-M-2" in the task file and the concern matrix.

- **[WHWQ-g3-9] Atomicity is claimed but not proved for the scan race; several statements went stale after the `Tb6ov` reorder (actionable)**
  - `WHWQExec.v:10–12` and the task file's T7 say "every execution" has an atomic underlay word. `whw_scan_race` does not state `ul_atomic`, although its three segments are atomic by inspection. Prove `MTracesAtomic Sr1`/`Sr2`, or narrow the sentence.
  - `WHWQExec.v:552–555` says the exchange then crosses only the store's response. In the new script it crosses nothing, because `a3` comes before `d2`.
  - The task file's first watch-list item cites `Tb6ov` for an `xchg` falling between the store's invocation and its response. `Tb6ov` no longer shows this. The fact still holds in the semantics, so keep the point but drop the citation.
  - `WHWQProg.v:62–64` ("may still be emitted before the store's response") is true by (F1)/(F3), but no lemma or execution supports it any more. Say so, or note that the proof of the second conjunct of `deq_inv_crosses_store` does not use the slot.
  - The task file's T2′ entry says the module is "argued to produce" `Tb6ov`. It is now kernel-checked (`Tb6ov_atomic`).

- **[WHWQ-g3-10] Records: some necessity and scope statements say more than was checked, and one quotation of the review remains (actionable)**
  - **"D2′ and D3′ are both needed"** appears in `WHWQExec.v:57–59`, `concern-matrix.md:46` and the task's T7(c); `concern-matrix.md:47` says "D3′ is necessary for the module-level separation". What is shown is narrower:
    - the crossing that `Tw` uses is impossible under D2 (by definition);
    - it is impossible when the exchange has a release write part (by definition; I checked it in memory at iteration 4, and it is not a lemma in the files);
    - that any separating execution needs both decisions is the gate-1 argument.
    - Write "this execution needs both; that any separation does is argued".
  - **The C2 status cell** says "forbidden on x86-TSO and (argued) ARMv8". Both cases are argued; my iteration-4 wording was imprecise. Write "(argued) forbidden on x86-TSO and ARMv8".
  - **The quotation.** The two words in quotation marks in the B6 status cell of `concern-matrix.md:46`, and the same words at two places of the gate-1 report in `latest-review.md`, come from Review B (:265–266). They are short, but they are presented as the reviewer's own words. Paraphrase them, for example "the general concern that I admits behaviours the code lacks". This predates the current iteration; the earlier 4- and 5-word scans missed it.
  - **Nit:** `WHWQProg.v:28–29` and C6 cite programlogic.tex:159–172 for the invocation rule. The rule is at :163–172; :159 is the `ret` rule.

- **[WHWQ-g3-11] The P6–P7 watch list does not record what the g3-3 fix changes (actionable)**
  - The re-read `ld` is now untagged, so in `dprec_run` no response edge enters it.
  - Its invocation may therefore be emitted before the response of the previous `xchg` (or of the previous `ld` when t = 0), though still after that call's invocation (F2).
  - P7's retry step must not use those response slots in the `ld`'s precondition. Its assertions must also be stable under those later own responses; under `EIhl` a response only consumes a record.
  - Add this to the watch list.

### Status of earlier findings

- **g3-1:** open, research-level; the scope is now recorded (with g3-10's corrections).
- **g3-2, g3-3, g3-4, g3-7:** resolved. What remains is in g3-9, g3-11 and g3-10.
- **g3-5:** resolved; see g3-8.
- **g3-6:** recorded (task file "Gate 3", concern-matrix B6 status, research intent); open, research-level.
- **WHWQ-M-1:** the necessity half is kernel-checked. T0 (P8) and the target model are open, and the records say so.
- **WHWQ-M-2:** open (paper). It now has kernel evidence: `Tf1_atomic` with `future_dependent`, and the scan race (worded as in g3-8).
- **WHWQ-m-4:** open, unchanged.

## Responses to Writer disputes

None.

## Concern-matrix corrections

- **:46**
  - "a kernel-checked form of WHWQ-M-2" → "kernel evidence for the first part of WHWQ-M-2".
  - The necessity wording: as in g3-10.
  - The C2 status: "(argued) forbidden on x86-TSO and ARMv8".
  - Paraphrase the quoted phrase.
- **:47:** "the crossing used by `whw_needs_qsi` needs D3′ (by definition); that the separation needs it is argued".
- **Unchanged:** A3/Meta-4, §3, §4 (every listed result is verified closed) and queue item 7 are accurate.

## Stronger or alternative approaches

1. **Prove M-2's first part in the kernel.** From `whw_scan_race`, prove `¬ ∃ S, GSimRel (EI δRC) (EI δQ) Mwhw S ∧ S init (PossOk ([], []) [])`. The precedent is `RelaxedHoareChecks.counter_vt_no_rlhl2` (examples/Relaxed/RelaxedHoareChecks.v:5963). This would turn g3-8's corrected sentence into a theorem, and contrast directly with T4 over `POQueueR`.
2. **`MTracesAtomic` for `Sr1` and `Sr2`** (g3-9).
3. **Optionally, add `complete L`** to `rel_lin_no_self_overlap`.

## Redesign assessment

No redesign is needed. P6 can start once the g3-8 wording is fixed. Add g3-11 to the watch list.

## Orchestrator note (after iteration 5)

- **g3-8.** The scan-race sentences in the WHWQExec header and before `whw_scan_race` are replaced by the suggested wording (a proof that must fix the order by enq(2)'s return fails; argued; `POQueueR` unaffected). The task file and the concern matrix say "kernel evidence for the first part of WHWQ-M-2".
- **g3-9.** `whw_scan_race` now states `ul_atomic` for each of its three segments; new `exec_app_t`, `ul_atomic_app`, `overlay_events_app`, and `Sr1_atomic`, `Sr2_atomic` (`MTracesAtomic` of both complete traces). The stale `Tb6ov` comment is fixed. New `WHWQProg.inv_crosses_store_res` (a store's response orders no later untagged invocation, an exchange at the store's slot included), cited in the WHWQProg header and the watch list (no execution shows that case; said so). The T2′ entry cites `Tb6ov_atomic`.
- **g3-10.** New `WHWQProg.store_xchg_rel_ordered` (with a release write part in the exchange, (store, xchg) is ordered) and `rc_si_D2`/`store_xchg_D2_ordered` (the plain-only relation of decision D2). The necessity wording now says "this execution needs both; that every separation does is argued" (WHWQExec header, task file, concern matrix :46, :47). The C2 cell says "(argued) forbidden on x86-TSO and ARMv8" (iteration 4's own wording is kept verbatim above). The quoted two-word phrase is paraphrased in the concern matrix and in the gate-1 report below. programlogic.tex line numbers corrected.
- **g3-11.** Added to the watch list in `tasks/WHWQ.md`.
- Not done: stronger approach 1 (a kernel proof that no `GSimRel` to `EI δQ` exists) is recorded as an option in the task file; approach 3 (`complete L`) is not needed while `rel_lin` is complete-only.
- All 19 re-checked results (including every new one) are closed.

---


<!-- WHWQ review gate 3 (2026-10-21), saved by the orchestrator. Produced by one rocq-research-reviewer run (read-only). Verbatim except that absolute paths are made relative and the toolchain path is dropped; the reviewer cited popl2027-reviews.md by line with its own paraphrases. The orchestrator's fixes and the follow-up iteration are recorded after the review ("Orchestrator note (after iteration 4)") and in iteration-log.md. Gate 1 and 1b are kept below. -->

# Research review — iteration 4 (task WHWQ, gate 3) — 2026-10-21

## Scope

- **Repository state.** The repository is rbgs, branch `rlhl`, HEAD `8549663`, with all work uncommitted.
  - Modified: `_CoqProject` and four `.rocq-review/` records.
  - Untracked: `tasks/WHWQ.md` and the seven files `examples/Relaxed/WHWQ/*.v`.
- **Under review: phase P5 of `.rocq-review/tasks/WHWQ.md`.**
  - New `examples/Relaxed/WHWQ/WHWQProg.v` (409 lines): `Mwhw`; `enq_prod`, `deq_prod`, `scan_exec`; `deq_inv_crosses_store`, `deq_res_crosses_store`, `xchg_same_slot_blocked`, `faa_after_older_inv`; the tactics.
  - New `examples/Relaxed/WHWQ/WHWQExec.v` (611 lines):
    - T7(c): `Tw_*`, `fifo_deq_before`, `whw_needs_qsi`, `whw_not_rel_lin_empty_all`;
    - T7(b): `Tb6ov_mtraces`;
    - T7(a): `Tf1_mtraces`, `Tf2_mtraces`, `whw_future_dependent`.
  - `_CoqProject`: `WHWQProg.v` and `WHWQExec.v` come after `POQueueRExample.v`, so the dependency order is right.
- **Gate-1/1b files.** I consulted these but did not re-review them. Their source mtimes are at or before 14:50, before their `.vo` files (14:51). The line counts of `POQueueR.v` (598) and `POQueueRExample.v` (1122) match the gate-1b patch in the project.
- **Paper.** `../async-ccal/drafts/relaxed-lin/` (paths below are relative to it).
- **Concerns in scope:**
  - B6 (popl2027-reviews.md:261–276; response :541–545);
  - B on mechanization (:250–254; proposed change 2 at :387);
  - C2 (:577–579);
  - B-minor (:301);
  - carry-overs WHWQ-M-1, WHWQ-M-2 and WHWQ-m-4.

## Checks I ran

**Build**
- `make -n examples/Relaxed/WHWQ/WHWQExec.vo examples/Relaxed/WHWQ/WHWQProg.vo` reports both up to date.
- `make -n` of the whole tree schedules no `coqc` step.
- The `.vo` files (18:01:45 and 18:01:54) are newer than their `.v` files (18:01:38).
- The toolchain is Rocq 9.2.

**Print Assumptions: 22 of 22 "Closed under the global context"**
- `WHWQExec`: `whw_needs_qsi`, `whw_not_rel_lin_empty_all`, `Tw_mtraces`, `Tw_wf`, `Tw_complete`, `Tw_rel_lin`, `Tw_not_rel_lin_empty`, `fifo_deq_before`, `Tb6ov_mtraces`, `Tf1_mtraces`, `Tf2_mtraces`, `whw_future_dependent`.
- `WHWQProg`: `enq_prod`, `deq_prod`, `scan_exec`, `deq_inv_crosses_store`, `deq_res_crosses_store`, `xchg_same_slot_blocked`, `faa_after_older_inv`, `pet_app`, `run_call_exec`, `run_done`.
- T7(a)/(b) are combined with three gate-1 results, so I re-checked those too: `POQueueRExample.{future_dependent, Tb6ov_b6, T0_needs_qsi}` are closed.

**Grep**
- In all seven WHWQ files there is no `Admitted`, `admit`, `Axiom`, `Conjecture`, `Parameter`, `Hypothesis`, `Variable`, `Context`, `Unset`, `vm_compute`, `native_compute`, `Opaque`, `Abort` or `bypass_check`. The one match is the word "Hypotheses" in a comment (`WHWQProg.v:334`).
- A leftover `examples/Relaxed/WHWQ/.WHWQExecDbg.aux` exists. It is git-ignored and harmless.

**Statements**
- `Set Printing Implicit` with `Check` confirms the following:
  - the LTS is `@EI ERC Mem δRC` with initial state `(mem0, [])`;
  - `sel` is `PrefixView.sel (FQ positive)`;
  - the relations are `semi_independent (FQ positive)` and `fun _ _ => False`, and the specification is `νQ positive`.
- `whw_not_rel_lin_empty_all` is exactly ¬(T6 with ∅), with T6 in the form of WHWQ.md:169–171.

**In-memory kernel checks** (piped `coqtop`, nothing written; each ended `No more goals`)
- `~ rc_si (op_store s v) (RCXchg (S s2) 0 RRlx WRel)`: the printed rel exchange.
- The same with `RAcq WRel`.
- `rc_si (op_store 2 4) (op_xchg 0) /\ rc_si (op_store 2 4) op_ld`.
- `~ rc_si op_faa op_ld`.
- `rc_mode (RCXchg 1 0 RRlx WRel)` evaluates to `LFence`.

**Read**
- Both new files in full.
- `RelaxedModuleSemantics.v`: `must_precede` at :252–259; the tagged rules at :578–610, where `tagged_invoke` has no per-thread condition.
- `RelaxedSemantics.v`: the tagged program semantics at :386–455.
- `RelaxedHoareRun.run` (:209–216).
- `RelaxedHoareSpec.EI` (:307–316).
- `RelaxedTraceLin.rel_lin`.
- `RelaxedLang.v`: the `FutureD` comment at :42–60.
- Paper: WHWQueue.tex; spec.tex:16 and :84–112; 2Counter.tex:6–13; trace.tex:33–90 and :274–301; programlogic.tex:106–310, :354–357 and :454–462.

### Claim by claim

**1. Fidelity of `Mwhw`: confirmed, with one conservative tag.**

The code is faithful:
- `enq` is `op_faa` (FAA(q,1,rel) read as (rlx, rel)), then `op_store i (Pos.to_nat v)` at location `i+1`, as in WHWQueue.tex:14–15.
- `deq` is `ld(q, acq)`, then exchanges at locations `1..t` (slots `0..t−1`), with D3′'s (acq, rlx), as in :16–18.
- The dequeue re-reads the counter after reading `t = 0` and after an empty scan (`dnext`, WHWQProg.v:105 and :108–110).
- D4 holds: `Pos.of_nat (Pos.to_nat v) = v`, and `DRet x` is reached only with `x ≠ 0`.

The tags compared with the paper's tag D (programlogic.tex:170), the assert rule (:209) and the memory policy at :109 (every operation except a plain read is control-ordered; taking all operations is "the conservative choice"):
- **The store's tag `[0]` = {h_faa}** is exactly the paper's address/data dependency.
- **The first `ld`'s tag ∅** matches the paper.
- **Every `xchg`'s tag (all earlier calls)** is exactly the paper's κ: the loop test on t, then every null test.
- **The re-read `ld` (`DLd n`, n > 0) is tagged with all earlier calls; the paper tags it ∅.** A plain read is not control-ordered, and its argument is the constant q. The two agree only under the conservative policy (WHWQ-g3-3).

Other tag choices do not change what matters for T6/T7 over `EI δRC` (argued, not mechanized):
- Cross-call tags cannot exist: `dep_of` names only the call's own handles, and programlogic.tex:290 says the same.
- Within one call, (F2) already orders every pair of invocations:
  - in the enqueue, `(faa, store) ∉ rc_si` because the store releases;
  - in the dequeue, every call acquires (`rc_si_not_after_acq`).
- `EI` fixes each result at the invocation (RelaxedHoareSpec.v:307–313), and a response step commutes with every other event of the execution.
- So any execution under weaker tags can be rearranged into one under positional tags with the same overlay trace: move each underlay response to right after its invocation.
- Hence the overlay trace set, and with it T6 and T7, is the same for every tag choice between "none" and "positional". The paper's policy is one of these. What does change is the module executions themselves and P7's dependency graph.

**2. Production lemmas: confirmed.**
- `map untag tr` equals exactly the events the method produces.
- The tag bounds are correct: enqueue tags ⊆ {h}, dequeue tags ⊆ [h, ∞). An existence proof needs only upper bounds on tags.
- Coverage is first-iteration success only, as the header says.

**3. T7(c) at the kernel level: confirmed. The scope is discussed in g3-1 and g3-2.**
- **`Tw` is spec.tex:89–110** with v_i = i and threads t1–t4.
- **The ∅ refutation is the cycle argument of spec.tex:112.** It uses only same-thread order, FIFO and the uniqueness of the values 1–4. It therefore applies to every interleaving with these results.
- **`Tw_rel_lin` is checked by hand** against the δQ run: [] → [1] → [1,2] → [2] → [] → [3] → [3,4] → [4] → [].
- **The crossing in `Tw` needs both D2′ and D3′.**
  - Under D2, RMW pairs are excluded by definition.
  - Under the printed (rlx, rel) exchange, and under (acq, rel), the pair (store, xchg) is not in `rc_si` (kernel checks above).
  - That *any* separation needs D2′/D3′ is still only the gate-1 argument.
- **EI artifact and the header's overlap claim:** see WHWQ-g3-1. The header's claim that the separation needs a client that overlaps its own calls is correct (trace.tex:68).

**4. T7(a)/(b): genuine module executions (kernel).**
- The framing of (a) is discussed in g3-5.
- The execution of (b) is not atomic: the store's response is emitted after the dequeue's `xchg` (g3-2).

**5. Client model: matches the paper.**
- The concurrent Inv rule (programlogic.tex:454; sequential version :260) asks only for a fresh, idle handle.
- trace.tex:37 allows several outstanding calls per thread.
- WHWQueue.tex:93 and the proof-figure captions use intra-thread concurrency.
- In the future language, `enq(4); deq()` issues the dequeue without waiting, because the unit result is never used (programlogic.tex:76–84). So the overlap in `Tw` is a client-level behaviour under either queue relation.
- Under `qsi`, the client's own frontier can also let the dequeue's *invocation* go first (g3-6).
- `Tw` also satisfies the paper's hb_s-restricted cross-call clause (:288–291; the known difference m-15). When t4's dequeue events are emitted, every O-event of t4's enqueue precedes them, and the store is semi-independent of `ld` and of `xchg@0`.

**6. Everything else.**
- Headers: g3-2 to g3-5.
- Assumptions and grep are clean.
- Readiness for P6: see the Redesign assessment.

## Verdict

P5 establishes what it is cited for, at the kernel level and over `EI δRC`:
- `Mwhw` is a faithful encoding of the WHW code with D3′ and D4. Its one conservative tag does not affect the overlay traces.
- The production lemmas are exact.
- `whw_needs_qsi` and `whw_not_rel_lin_empty_all` prove that, under D2′/D3′, the code has a complete, well-formed execution whose overlay trace is the four-thread example. That trace is relaxed-linearizable under I(enq, deq) and not under ∅.

This settles the necessity half of WHWQ-M-1 in the kernel.

The separation is not an artifact of `EI`. The memory behaves as SC, and the underlay word is globally atomic. The weak step is the RCpc-style overtaking that D2′/D3′ add to the signature. Two limits follow:
- the claim must be scoped to C11-style targets, because x86-TSO and ARMv8 forbid this outcome (argued);
- only clients that overlap their own calls can observe it.

There is no BLOCKER, one research-level MAJOR, and six MINOR findings. **Continue to P6.**

## Findings

### BLOCKER

None.

### MAJOR

- **[WHWQ-g3-1] T7(c) comes from the RCpc reorderings of D2′/D3′, not from EI. It supports "the code needs I(enq, deq)" only for C11-style targets and only for clients that overlap their own calls (research-level)**
  - **Where:** WHWQExec.v:9–46 and :453–468; WHWQSpec.v:51–92; WHWQ.md:78–97 and :175–188.
  - **K:** closed (see Checks). Under the printed or the acq_rel exchange, (store, xchg) ∉ `rc_si`.
  - **S:** one module execution over `EI δRC`, the SC register file with effect at invocation. The signature `ERC` carries D2′'s `rc_si`.
  - **P:** the paper states the scope differently.
    - spec.tex:84–112 (commented out) presents the example as allowed by the WHW queue and impossible under SC, because I_WkQueue relaxes the (enq, deq) order.
    - 2Counter.tex:13 defines the target as the prefix closure of globally atomic register executions with no RMW pairs.
    - trace.tex:278–301 places RC next to TSO and PSO, with TSO as all writes rel and all reads acq.
  - **R:** what the reviewers need.
    - C2 (:577–579): the authors treat I as a contract to check against the code. They say the multi-thread example motivates some (enq, deq) relaxation, not that it is minimal.
    - B (:261–276): a statically fixed relation may let the specification allow results that the code, run directly on RC, never produces.
    - B-minor (:301): the reviewer asks for an acquire exchange.
  - **Evidence, part (a): EI is not the source.**
    - In `Tw_mtraces` every underlay invocation is immediately followed by its response (script :161–242), with δRC's values at that point. The underlay word is therefore a globally atomic register execution in the sense of 2Counter.tex:13.
    - The weak step is t4's `ld` and `xchg@0` being emitted before t4's older `store@2`. `rc_si` licenses this through (F2).
    - The Coq frontier and tags are at least as restrictive as the paper's (claims 1 and 5).
    - So `Tw` is also an execution of the paper's module semantics over the target ν_RCMem read with D2′, and over every underlay whose traces contain this word (argued). It is not shown for every refinement of ν_RCMem, since a refinement may drop the word.
  - **Evidence, part (b): the weak step is RCpc.** The step is a younger acquire overtaking an older release store to another location. The paper's RC is already RCpc on plain operations: the header of `memory/Litmus.v` records SB+rel+acq as allowed by "ours" and forbidden by ARM (Δ1). D2′ extends this to RMWs. For the `Tw` outcome specifically (argued, not machine-checked):
    - **x86-TSO forbids it.** XCHG and LOCK XADD are locked, so `W4` reaches memory before `X4`. Then the chain X4 → X2a → FAA3 → LD3 → X3c makes X3c read 4.
    - **ARMv8 forbids it** (mapping STLR / LDAR / SWPA / LDADDL). There is a cycle in `ob`: W4 →bob([L];po;[A]) R(X4) →aob(rmw) W(X4) →rfe R(X2a) →bob([A];po) W(FAA3) →rfe R(LD3) →bob R(X3c) →fre W4.
      - X2a cannot read the initial 0 instead: that would close W1 →bob(po;[L]) W(FAA2) →rfe R(FAA4) →aob W(FAA4) →rfe R(LD2) →bob R(X2a) →fre W1.
      - `memory/ARM.v:8` has [rel];po;[acq] ⊆ bob, but only on the fragment without RMWs.
      - This is from memory of Pulte et al., POPL 2018; check it against the official AArch64 cat model.
    - **RC11 (Lahav et al., PLDI 2017) allows it.** There is no hb from W4 to t3's first xchg at slot 2:
      - X4's write is relaxed, so X2a synchronizes only with W1, the head of the release sequence;
      - the q-chain synchronizes LD2/LD3 only with FAA4, which is po-before W4;
      - the order mo(s2) = init, X3c, W4, X3g satisfies coherence and atomicity.
  - **Evidence, part (c): overlap is necessary.** Without same-thread overlap, rhb under `qsi` equals rhb under ∅ (trace.tex:68). So clients that alternate their calls get ordinary linearizability from T6.
  - **What can be claimed:** "Over effect-at-invocation RCMem, with D2′'s C11-style relation and the acquire exchange, the code has a complete execution, the 4-thread example, that is relaxed-linearizable under I(enq, deq) and not under ∅. It is observable only by self-overlapping clients, and the same outcome is forbidden on x86-TSO and (argued) ARMv8."
  - **What cannot be claimed:** a hardware-level weakness, or a property of every RCMem implementation.
  - **Required:**
    - The authors decide whether D2′ is the RCMem the paper means (this is b-1 of gate 1b, now concrete).
    - The paper and the C2 answer state the scope above.
    - Optional: herd7 runs of this litmus test for C11 and AArch64, or RMW support in `memory/RC11.v` and `memory/ARM.v`.

### MINOR

- **[WHWQ-g3-2] The transfer to the atomic target is only by inspection; the conclusion omits "over EI δRC"; `Tb6ov`'s execution is not atomic (actionable)**
  - **Where:** WHWQExec.v:41–46, :127–245 and :481–512.
  - **Evidence:**
    - `Tw` and `Tf*` emit each response right after its invocation.
    - `Tb6ov` emits the store's response `a3` after `d2` and `d3`. Emitting `a3` right after `a2` gives the same overlay trace, because `d2` is then at the head of the queue.
  - **Required:**
    - Write "over EI δRC" in :41–42.
    - State the atomicity of the underlay word, either as a lemma or by running the executions over an atomic presentation.
    - Reorder `a3` in `Tb6ov`.

- **[WHWQ-g3-3] The re-read `ld` carries a tag that the paper's memory policy does not give it (actionable; the "hand-written tags" risk pattern)**
  - **Where:** WHWQProg.v:19–25 and :104–105. Compare programlogic.tex:109 and :170, and RelaxedLang.v:42–60.
  - **Evidence:** claim 1. It is harmless for T7, which only needs fewer executions. It is argued harmless for T6 over EI. It does fix P7's dependency graph.
  - **Required:**
    - The header should name the policy: conservative, with all operations control-ordered. It should say that under :109 the re-read `ld` is untagged, and why that is invisible over EI.
    - Optional: a variant with the paper's tags and a proof that its `MTraces` over `EI δRC` are the same.

- **[WHWQ-g3-4] The WHWQProg header says the four frontier facts are "used by the executions"; no proof uses them (actionable)**
  - **Where:** WHWQProg.v:38–45; cited in WHWQExec.v:24, :53 and :475.
  - **Evidence:** a grep finds only comment references. `cross_ok` re-proves the crossings.
  - **Also:** "may not" at :43 is ambiguous. `xchg_same_slot_blocked` blocks only the crossing of the store's *invocation*; `Tb6ov` does cross the store's response.
  - **Required:** reword the header, or make `cross_ok` use the lemmas.

- **[WHWQ-g3-5] T7(a): in the module the past decides the order, and `Tf1` refutes the TR's enqueue linearization point; neither is stated (actionable)**
  - **Where:** WHWQExec.v:58–65 and :514–609.
  - **Evidence:**
    - `Tf1` and `Tf2` already differ in their FAA order before the dequeue.
    - In `Tf1`, enq(2)'s store comes first. Yet every witness puts enq(1) first (the third conjunct of `future_dependent`).
    - So no single possibility that appends enq(v) at its store (WHWQueue.tex:65 and :91) can be maintained. `Tf1_mtraces` with `future_dependent` is a kernel-checked form of M-2's hand-checked counterexample.
  - **Required:**
    - Retitle (a): the overlay trace does not determine the order, but the FAA order does.
    - Cite `Tf1` under M-2.
    - Optional: the scan-race pair. Run A's FAA, B's FAA, B's store, B returns, then the dequeue is invoked. Either the `xchg@0` comes before A's store (the dequeue returns B) or after it (the dequeue returns A). The module state is the same in both at the dequeue's invocation, so this is genuine implementation-level future dependence.

- **[WHWQ-g3-6] Client-level reordering: under I(enq, deq) a client's own frontier may issue `deq` before its earlier `enq`; the specification then blocks the dequeue, and the module also blocks the enqueue (research-level)**
  - **Where:** the B6 corollary planned for P8; `POQueueRExample.b6_*`.
  - **The client side:**
    - The client's own frontier rule (F2, programlogic.tex:280) uses `FQ`'s I. Under `qsi` it lets the `deq` invocation go first.
    - Then rhb has the edge deq→enq under both relations, because (deq, enq) ∉ `qsi`.
    - So a single-thread `enq(1); deq()` has no complete trace with deq → 1.
  - **The module side** (argued):
    - In `Mwhw` the `faa` cannot cross the dequeue's pending acquires, and the dequeue cannot succeed before that `faa`.
    - So only prefixes of [inv deq; inv enq(1)] are produced, and neither call returns.
    - The specification lets enq(1) return.
  - **The review:** B6 (:261–276) describes the dequeue being invoked first. The response (:545) leaves termination out of the guarantee.
  - **Required:**
    - The B6 paragraph should say that the guarantee is partial in this case, and that the layered composition can block where the inlined code completes.
    - P8 should state the corollary for both invocation orders.

- **[WHWQ-g3-7] T0's unproducibility is asked "next to T7(c)" (WHWQ.md:186–188) but deferred to P8; it needs a code-level argument (actionable)**
  - **Evidence:** `T0` is a `POQueueR` path (`T0_needs_qsi`), so T5/T6 cannot exclude it. The reason it is unproducible is the slot-order scan: t1's second dequeue reaches slot 1 after both stores are done.
  - **Required:** record the deferral in the task file, and plan the extra facts in P6's invariant or in a separate execution invariant.

### Carry-overs

- **WHWQ-M-1: partially resolved.** The necessity half is now kernel-checked over `EI δRC`, with the scope given in g3-1. Still open:
  - the imprecision side (T0, g3-7);
  - the choice of target model (g3-1).
- **WHWQ-M-2: open (paper).** There is new kernel evidence (g3-5).
- **WHWQ-m-4: open.** With D3′, the code's rel store and acquire exchange informally match the promised modes at the C11 level. The modes are still not validated through the tensor rule.

## Responses to Writer disputes

None.

## Concern-matrix corrections

- **B6/C2 (:46)**
  - Add `Mwhw` and the closed T7 executions.
  - C2: "separation proved in the kernel over EI δRC under D2′/D3′; C11-level; forbidden on x86-TSO and (argued) ARMv8; observable only by self-overlapping clients". Keep 🟡 and drop "argued producible".
  - B6: add `Tb6ov_mtraces`. The implementation-level corollary is still due at P8, with the case of g3-6.
- **B-minor (:47):** D3′ is necessary for the separation (kernel: (store, xchg) ∉ `rc_si` when the exchange has a release write part).
- **A3/Meta-4 (:33) and §3 (:109):** the queue now has a module and closed module-level executions. The RLHL proof and T6 are pending.
- **§4 (:115):** add the 22 results above.
- **M-2:** add `Tf1` as a kernel-checked counterexample.

## Stronger or alternative approaches

1. **Overlap lemma.** Prove that on traces without same-thread overlap, `rel_lin indep` ⟺ `rel_lin ∅`. This turns the header remark into a theorem.
2. **Tag irrelevance over EI.** Prove a general lemma: if (F2) totally orders each method's invocations, the overlay traces over `EI δ` do not depend on the tags. This closes the "hand-written tags" risk for this case study.
3. **Atomic underlay.** State T7 over an atomic presentation of ν_RCMem.
4. **Settle the target question.** Run herd7 (C11 and AArch64) on the four-thread litmus test, or extend `memory/RC11.v` and `memory/ARM.v` with RMWs.
5. **Consistency checks at P8.** Apply `whw_rel_lin` to `Tw`, `Tb6ov` and `Tf*`.

## Redesign assessment

No redesign is needed. P5 is complete enough for P6. P6 and P7 should watch for the following:

1. **ARet at the store's invocation is forced.** `Tb6ov` adds a second reason to the Layer-1 sketch's: the same thread's `xchg` falls between the store's invocation and its response.
2. **Same-thread interference across calls runs both ways.**
   - In `Tw`, the younger dequeue's AInv/ARet and its return happen between the older enqueue's `faa` and `store`.
   - In `Tb6ov`, the older store falls between the dequeue's `ld` and `xchg`.
   - So R must cover the other calls of the same thread.
3. **The ghost keeps an older owner's entry.** `ghost_emit` and `GAge` must work while the older owner's `store` entry is still in the ghost.
4. **State-based Scan.** In `Tw`, t3 passes the pending vertex at slot 2 and takes the younger vertex at slot 3. Scan must stay true when that slot is filled later.
5. **Readiness at a dequeue's AInv** must use the leading `ld`, which (F2) orders after older `faa`s at the counter's location. Pairwise, `(faa, xchg) ∈ rc_si`.
6. **Retry loops and `t = 0`.** No execution covers them; `rp_run` must.
7. **P8:**
   - T0 needs a code-level argument (g3-7).
   - The B6 corollary should cover both invocation orders (g3-6).
   - `Tb6ov` is not a `POQueueR` path, so T6 must go through the copy-cat.

## Orchestrator note (after iteration 4)

Fixes made before the follow-up review (iteration 5):

- **g3-2.** The WHWQExec header now says "over `EI δRC`" wherever T7(c) is stated. New `ul_atomic` (every underlay invocation is immediately followed by its own response, no response elsewhere) and `MTracesAtomic`; every execution is now proved in that form (`Tw_atomic`, `Tb6ov_atomic`, `Tf1_atomic`, `Tf2_atomic`), with `mtraces_atomic` giving the `MTraces` corollaries. In `Tb6ov` the store's response follows its invocation directly. The header states that the transfer to the paper's atomic target is by inspection.
- **g3-3.** The re-read `ld` is now untagged, so the tags are exactly those of the paper's policy for memory cells (programlogic.tex:106–112, :159–172). The WHWQProg header has a new "Dependency tags" paragraph that names the policy and says why the tags are expected not to matter for the overlay traces over EI (argued, not proved).
- **g3-4.** The header now says the frontier facts explain the crossings and that `cross_ok` re-proves them; `xchg_same_slot_blocked` is described as blocking only the store's invocation.
- **g3-5.** T7(a) is retitled. The header states that `Tf1` refutes a linearization of an enqueue at its store (WHWQ-M-2). The optional scan-race pair is added: `whw_scan_race`, `Sr1_rel_lin`, `Sr2_rel_lin`, `Sr1_order`, `Sr2_order`, `whw_future_dependent_module` (two executions from one module configuration whose witnesses order the two enqueues oppositely).
- **g3-7.** The deferral of T0's unproducibility to P8 and what it needs are recorded in `tasks/WHWQ.md`.
- **Stronger approach 1.** `rel_lin_no_self_overlap` (on well-formed traces without self-overlap, `rel_lin` under any relation equals `rel_lin` under ∅) and `Tw_self_overlaps`.
- **Not done:** approaches 2 (tag irrelevance as a lemma), 3 beyond `ul_atomic`, and 4 (herd7 / RMWs in `memory/`). g3-1 and g3-6 are research-level and go to the authors.


---

<!-- WHWQ review gate 1 (2026-10-21), saved by the orchestrator. Produced by one rocq-research-reviewer run (read-only). Verbatim except that quotations of popl2027-reviews.md are replaced by line references and reworded summaries (the repository is public; .rocq-review/.gitignore), absolute paths are made relative, and the toolchain path is dropped. Iterations 2 and 3 of this gate (follow-up reviews of the fixes) are summarized in iteration-log.md and tasks/WHWQ.md; iteration 3 is prepended below. -->

# Research review — iteration 3 (task WHWQ, gate 1) — 2026-10-21

## Scope

I checked only what changed since iteration 2. The repository is rbgs, branch `rlhl`, HEAD `8549663`, with all work still uncommitted.

- `examples/Relaxed/WHWQ/POQueueRExample.v` (now 1111 lines) has two new sections:
  - §5: the `Tb6ov` lemmas, the `rhb_absurd` tactic and `Tb6ov_b6`.
  - §6: the `Tinc` lemmas and `POQueueR_incomplete`.
  - Its header is updated.
- `examples/Relaxed/WHWQ/POQueueR.v` and `examples/Relaxed/WHWQ/WHWQSpec.v`: header edits only.
- `POQueueRSound.v` and `POQueueRWitness.v` are unchanged (same md5 as iterations 1 and 2).
- Records: `.rocq-review/tasks/WHWQ.md`, `.rocq-review/latest-review.md`, `.rocq-review/concern-matrix.md` (row B6/C2).

The concerns are the same as before. Statuses requested: m-7 to m-10. M-1, M-2 and m-4 stay open.

## Checks I ran

**Build and kernel**
- `make -n examples/Relaxed/WHWQ/POQueueRExample.vo` reports the target is up to date.
- I re-elaborated `WHWQSpec.v`, `POQueueR.v` and `POQueueRExample.v` from stdin with `rocq repl` (Rocq 9.2). There were no errors or warnings, and each file ended with "Module … is defined".

**Print Assumptions: 17 of 17 "Closed under the global context"**
- `poqr_sound`
- `FQ_wf`, `ERC_wf`, `rc_si_iff`, `whw_rc_si`
- `future_dependent`, `T0_needs_qsi`, `Tk_not_rel_lin`, `Tk_no_path`
- `b6_enq_deq`, `b6_returns`, `Tb6_b6`
- New: `Tb6ov_b6`, `Tb6ov_no_rhb`, `Tb6ov_rel_lin`, `POQueueR_incomplete`, `Tinc_rel_lin`

**Admit grep**
- No `Admitted`, `admit`, `Axiom`, `Parameter`, `Unset`, `vm_compute`, `native_compute` or `Abort`.
- The only section hypotheses are still `B_*` and `TfWitness`, and both are discharged.

**Statements of the new results (read and confirmed)**
- `Tb6ov` = `[inv enq 1 (t1,0); inv deq (t1,1); res deq → 1; res enq]`.
- `Tb6ov_no_rhb`: there is no `rhb` edge in either direction between the two operations as they occur in the trace.
  - enq→deq real time fails on positions.
  - enq→deq program order is removed by `qsi`.
  - deq→enq fails on positions.
- `Tb6ov_rel_lin` gives the witness `[enq 1; deq → 1]` directly.
- `Tb6ov_no_path`: at the deq response the only vertex is still pending.
- `Tb6ov_b6` bundles these and applies `b6_enq_deq`.
- `Tinc` = `[inv enq 1; inv enq 2; res; res]`, all by t1. `Tinc_rel_lin` gives the witness `[enq 1; enq 2]` directly, and `Tinc_no_path` rejects the second invocation.
- `POQueueR_incomplete` bundles wf, complete, rel_lin and "no path". So `~ complete_pres` follows immediately, since `Tinc` is an `rl_prefix` with an empty continuation.

**Comment-only edits**
- `POQueueR.v`: diffed against master `51f424a:…/POQueueSpec.v`. The hunk structure is unchanged, shifted by exactly 16 lines.
- `WHWQSpec.v`: the code part (line 85 on) has the same length as in iteration 2, and its definitions are unchanged on a grep of every definition.

**Review-text overlap**
- My read-only n-gram scan with 5-word windows over all WHWQ `.v` files and `WHWQ.md`, plus the lines added to the tracked records, finds only generic phrases ("the weak hw queue the", "of the weak hw queue").
- With 4-word windows it finds only generic phrases as well.
- The orchestrator's `check.py` (read-only, run with N = 5) gives the same result.
- I read the reworded passages for fidelity: WHWQ.md:23–39, and latest-review.md:1, :119–121 and :180.

## Verdict

Gate 1 passes. Every actionable finding from iterations 1 and 2 is resolved and the 17 checked results are closed. `Tb6ov` is the right B6 instance: no `rhb` edge relates the two calls, so only the blocking `δQ` forces the order. The B6 results are now labelled as specification-level, with the implementation-level corollary planned for P8. `POQueueR` is now proved to reject a complete, rel_lin trace. The headers match the code, and the review text is no longer quoted.

Two new minor documentation points remain (m-11, m-12); they can be fixed together with the next log entry. M-1, M-2 and m-4 stay open for the author, and P5 stays blocked on M-1.

## Findings

### BLOCKER
None.

### MAJOR
- **[WHWQ-M-1] — OPEN.** Awaiting the author's decision. WHWQ.md now gives the hedge ("argued, not kernel-checked") and the full option (b).
- **[WHWQ-M-2] — OPEN.** Awaiting the author (paper). WHWQ.md now states the wording requirement and the hand-checked counterexamples.

### MINOR
- **[WHWQ-m-1] to [WHWQ-m-6] — RESOLVED.** Unchanged since iteration 2. The optional m-1 item is now done: `POQueueR_incomplete` backs the header claim in POQueueR.v.
- **[WHWQ-m-4] — OPEN.** Research-level, awaiting the author.
- **[WHWQ-m-7] (verbatim review text) — RESOLVED.** The 5-word scan is clean apart from generic phrases. The rewordings are faithful: latest-review.md keeps B6's general worry, the reason behind the C2 response and the C5 commitment; its header comment lists all the edits made to the saved report.
- **[WHWQ-m-8] (B6 instance) — RESOLVED.** `Tb6ov` is proved well-formed, complete and rel_lin, with no `rhb` edge between its two calls, every witness equal to `[enq 1; deq → 1]`, and no `POQueueR` path. The POQueueRExample header says which instance exercises the dropped edge, and that the implementation-level corollary is not proved here. WHWQ.md and the concern matrix plan that corollary for P8 and mark it "argued to be produced".
- **[WHWQ-m-9] (task-file summaries) — RESOLVED.** C3 separates what is kernel-checked from what is only by inspection; the M-1 hedge and the (b) details (`Hidle`, P2–P3 unchanged, argued, `T0` unproducible) and the M-2 wording requirement and hand checks are restored.
- **[WHWQ-m-10] (provenance) — RESOLVED.** WHWQSpec.v places the Example 3.11 modes in the anonymized TR PDF, which is outside the repository, and states explicitly that `δQ` replaces the submitted non-blocking `deq : N + {⊥}`, which returns ⊥ on the empty queue. This matches spec.tex:87 and the PDF.
- **[WHWQ-m-11] (new, actionable, documentation) — the task file narrows B6 to the example.** WHWQ.md reduces Review B's concern (popl2027-reviews.md:261–276) to the single-thread example and drops the general point (a static relation may allow behaviours the implementation never shows, at a cost to clients); the M-1 entry mentions only the C2 consequence, not that a finished T6 under D2/D3 would bear out that general B6 worry. Required: add one paraphrased clause to each, so that the B6 lemmas are not read as answering all of B6.
- **[WHWQ-m-12] (new, actionable, records) — two records are out of date.** latest-review.md:1 says the iteration-2 follow-up is summarized in iteration-log.md, which it was not; concern-matrix §4 baseline omits `Tb6ov_b6`, `Tb6ov_no_rhb` and `POQueueR_incomplete`. Optional: a two-line corollary `~ ViewLHL.complete_pres (νQ positive) (POQueueR positive) poqr_init`; mention m-8 in the opening paragraph of the POQueueRExample header.

## Responses to Writer disputes

None. No item is marked DISPUTED.

## Concern-matrix corrections

- **Row B6/C2.** The update is correct. No further change is needed.
- **§4 baseline.** Add the three results named in m-12.

## Stronger or alternative approaches

No change since iteration 2. If the author chooses option M-1(a), the `FQ0`/`POQueueRstrict` route remains the cheapest way to make the "not exercised" claim a theorem.

## Redesign assessment

None needed. P1–P3 and P3′ are correct and closed, and they do not depend on which M-1 option is chosen. The only gate before P5 is the author's decision on WHWQ-M-1.

## Orchestrator note (after iteration 3)

m-11 and m-12 were fixed after this report (task file B6 and M-1 entries; iteration-log entry for iterations 2–3; §4 baseline), and the optional corollary `POQueueRExample.POQueueR_not_complete_pres` was added (closed).

---

The iteration-1 report of this gate follows; its finding IDs are the ones used above.


# Research review — iteration 1 (task WHWQ, gate 1) — 2026-10-21

## Scope

- **Repository.** rbgs, branch `rlhl`, HEAD `8549663`. The work under review is uncommitted.
  - `M _CoqProject`: one comment line plus 4 files after `RelaxedHoareSL2Read.v`, in dependency order.
  - `?? .rocq-review/tasks/WHWQ.md`.
  - `?? examples/Relaxed/WHWQ/`: `WHWQSpec.v` (339 lines, P1), `POQueueR.v` (582 lines, P2), `POQueueRWitness.v` (718 lines, P3), `POQueueRSound.v` (884 lines, P3).
  - `POQueueRExample.v` was not present and is out of scope.
- **Task.** WHWQ, review gate 1 (P1–P3). Main result T2: `POQueueRSound.poqr_sound : forall A, ViewLHL.sound_pres (νQ A) (POQueueR A) poqr_init`.
- **Concerns in scope:**
  - Review B, B6 (the single-thread `enq(1); deq()` example against the static I = {(enq, deq)}; popl2027-reviews.md:263–276).
  - Review B, mechanization (the weak HW queue is not mechanized; :248–254).
  - Review C question and response C2 (:577).
  - Review B minor (xchg should be acq; :301).
  - The author response's proposed change 2 (:387).
  - research-intent Q5.
  - Concern-matrix rows B6/C2 and §3 "Counter_xy, weak HW queue".
- **Sources.**
  - Paper: async-ccal/drafts/relaxed-lin. A read-only copy, not a git repository. Below, "paper/" means this directory.
  - Background project docs: `claude/fdlp-whwqueue-rlhl-2026-10-21.md` and `claude/poqueue-hvf-check-2026-10-21.py` (read, not run).

## Checks I ran

**Build and kernel status**
- `make -n examples/Relaxed/WHWQ/POQueueRSound.vo` reports "up to date", and `.Makefile.d` lists all four files.
- I did not rebuild. Instead I re-elaborated each of the four sources in `rocq repl -q -R …`, reading the `.v` file on stdin, with Rocq 9.2. There was no `Error:` and no warning. The POQueueRSound run ends with "Module POQueueRSound is defined" and then "Closed under the global context".

**Print Assumptions**
- All "Closed under the global context": `poqr_sound`, `WHWQSpec.FQ_wf`, `ERC_wf`, `whw_rc_si`, `rc_si_iff`, `qsi_iff`, `δRC_det`, `POQueueR.poqr_step_wf`, `poqr_step_inv_handle`, `poqr_step_res_handle`, `POQueueRWitness.W_vq`, `POQueueRSound.pinv_rel_lin`.
- None of them uses `eq_rect_eq` or `classic`.

**grep of the four files**
- There is no `Admitted`, `admit`, `Axiom`, `Parameter`, `Unset`, `vm_compute`, `native_compute` or `Abort`.
- The only section hypotheses are `B_mono … B_pos` (POQueueRWitness.v:480–489). They are discharged, since `poqr_sound` is closed.

**Plugging T2 into the existing theorems (type-checked in the toplevel)**
- `gsim_rel_lin VE (POQueueR A) M poqr_init (νQ A) S q0 evs c HS H0 Hex Hdead poqr_sound` type-checks.
- So does `gsim_rel_lin_traces VE (POQueueR A) M S q0 poqr_init HS H0 (νQ A) poqr_sound`. Its type is `forall s, MTraces VE M q0 s -> PrefixView.complete s -> rel_lin sel s (semi_independent (FQ A)) (νQ A)`.

**Port fidelity**
- I ran `diff <(git show 51f424a:examples/HWQ/POQueueSpec.v) examples/Relaxed/WHWQ/POQueueR.v`.
- The only differences are those the header lists: the handle is ignored, `POQAtomic` loses its op field, the step relation is defined by cases, and imports differ.
- The state, the transformers, (W1)–(W8) and the transformer facts are verbatim.

**Hand checks (argued, not kernel-checked)**
- **H1, the 10-event trace of the brief.**
  - It is a `POQueueR` path:
    - vertex 0 (v0) completes;
    - vertex 1 (v1) is pending while deq (1,2) removes vertex 0;
    - vertex 2 (v2) gets an edge only to vertex 0, because vertex 1 is pending at its invocation;
    - deq (1,3) removes vertex 2, which is minimal because vertex 0 is garbage.
  - Under qsi a witness is E0, D2, E2, E1, D3.
  - Under ∅, program order gives E0 < E1 < D2 < D3, and real time gives D2 < E2, E1 < D3 and E2 < D3. The only FIFO-legal order is then E0, E1, D2, E2, D3, in which D3 must return v1.
  - So the orchestrator's claim holds: POQueueR is unsound under ∅. The proof uses qsi exactly once, in the (enq, deq) program-order case of `rhb_before` (POQueueRSound.v:794–795).
- **H2, the frontier argument.** `must_precede (InvEv o1) (InvEv o2) = ~ rc_si o1 o2` (RelaxedModuleSemantics.v:252–259), and `rc_plain` is false for every RMW. So no invocation can overtake an older same-thread faa or xchg. No faa or xchg can overtake any older same-thread invocation. Nothing can overtake an older acq ld.
- **H3.** The 4-thread example of paper/spec.tex:89–110 under the decided RCMem and under a variant (see WHWQ-M-1).
- **H4.** The single-possibility proof of the TR (see WHWQ-M-2).
- **H5.** (νQ, qsi) against `PrefixView.compat_fixed` (see WHWQ-M-2).
- **H6.** Neither `POQueueR` nor `EI δRC` is a complete presentation (see WHWQ-m-1 and the redesign section).

**Confirmed at the S and fidelity levels**
- **`poqr_sound` is exactly HVF.** It is literally the HVF premise of `gsim_rel_lin` (RelaxedGSim.v:1035–1036), `rlhl_rel_lin` and `rlhl_rel_lin_pres` (`Hsound`), and `gsim_rel_lin_traces`.
  - The only restriction is "complete, well-formed traces", which is how HVF is consumed.
  - It is generic in `A`. It needs no decidable equality and does not assume distinct values: the witness works on vertex ids.
- **`PInv` and the witness hypotheses are faithful.** `PInv` is proved inductive along every path for well-formed traces. `B_*` are trace facts that it discharges, so no hypothesis makes the result easier.
- **`FQ`, `qsi` and the modes match the TR.** They match I_WkQueue (paper/Appendix/WHWQueue.tex:63).
  - The modes LFence/RFence are the maximal ones that `well_formed` allows. The paper fixes none.
  - `δQ` is the blocking API promised by response B6 (popl2027-reviews.md:541, :545). It agrees with the TR's state' function (WHWQueue.tex:42–49).
  - The commented-out main-text version was non-blocking (spec.tex:87: "either qstate(p) = k :: q' or qstate(p) = [] and k = ⊥").
- **`ERC`, `rc_si` and `δRC` follow the paper literally.**
  - They follow 2Counter.tex:6–13: the RMW mode is the join, and "with no RMW pairs" is read as "no pair involving an RMW", which is the natural reading.
  - `rc_si_iff` is the right characterization of eq. (main-preserved-order) (trace.tex:299) on plain operations.
- **The WHW operations match the code.** WHWQueue.tex:14–17, with FAA's single "rel" read as (rlx, rel). Indexing is re-based (see m-3).

## Verdict

P1–P3 are correct and establish what they are cited for, but they are not yet a mechanization of the queue. `poqr_sound` is closed and is exactly the HVF premise for VF := POQueueR. `POQueueR` is a faithful port of master's `POQueueSpec`. `FQ`/`δQ`/`νQ` make response B6's blocking API formal. The plan's argument that per-thread `Hidle` is compatible with the module over `EIhl δRC` is sound in this framework, with the constraints listed in the redesign section.

Continue, with two changes:
1. **Decide WHWQ-M-1 before P5.** Under RCMem as decided (D2 and D3), the code never uses I(enq, deq). The case study then cannot support the C2 answer, and it confirms rather than rebuts B6's general concern (that a fixed I admits behaviours the code lacks). The decision changes the inputs of P5–P7 (either `ERC` or the presentation to prove against), not P2–P3.
2. **Drop P4.** T6 follows from existing lemmas without it.

The B-mechanization concern stays missing until P5–P8 exist.

## Findings

### BLOCKER
None.

### MAJOR

- **[WHWQ-M-1] Under the decided RCMem, the code never uses I(enq, deq), so T6 will be strictly weaker than what the code satisfies, and the case study cannot carry the C2 answer (research-level)**
  - **Where:**
    - Coq: examples/Relaxed/WHWQ/WHWQSpec.v:216–224 (`rc_plain`, `rc_si`), :323 (`op_xchg`), :327–337 (`whw_rc_si`); models/simlin/RelaxedModuleSemantics.v:252–259, :578–611.
    - Paper: Appendix/WHWQueue.tex:63, :93, :148; Appendix/2Counter.tex:13; spec.tex:87–112 (commented out).
    - Plan: task T7 ("Expected limitation").
  - **K.** `whw_rc_si` (closed): among the WHW operations, the only semi-independent same-thread pair is (older store, younger ld).
  - **S.** In `module_step_tagged`, a younger invocation must cross every older queued invocation of its thread (H2). Consequences:
    - A deq's linearization point, its successful xchg, is emitted only after every older same-thread enq has emitted its faa and its store. Those are that enq's AInv and ARet.
    - The same xchg is also emitted only after every invocation of every older same-thread deq.
    - A younger enq's faa is likewise emitted only after all older same-thread invocations.
    - Hence every VF path the RLHL proof can produce is also a path of the stricter presentation "a dequeue cannot start while its thread has a pending enqueue".
    - The background bounded check (§5, last rows: 0 of 19,068 and 0 of 12,398 traces) finds that presentation sound under ∅. With `rel_lin_mono`, I(enq, deq) then adds nothing for this code. This is argued, not kernel-checked.
  - **P.** Relative to 2Counter.tex:13 ("with no RMW pairs"), no un-linearized older enq can exist at a successful xchg. So two TR statements are false:
    - WHWQueue.tex:148: "This is the point where the weak queue specification is used".
    - WHWQueue.tex:93: the deq is committed "because every earlier pending operation in the same thread is an enq".
  - **P, continued: the motivating example.** The 4-thread example of spec.tex:89–110 is not producible by this code over this RCMem (H3). The chain of effects is:
    1. store(v4) by T4 precedes T4.xchg(v1), because an RMW cannot pass an older store;
    2. which precedes T2's xchg at v1's slot (null);
    3. which precedes T2.xchg(v2);
    4. which precedes T2.faa(v3), because an RMW cannot pass an older RMW;
    5. which precedes T3.ld;
    6. which precedes T3's xchg at v4's slot (F2).
    So T3's first deq finds v4, not v3.
  - **R.** Three statements in the review file bear on this:
    - B6 (popl2027-reviews.md:263–276): the worry that the fixed relation is too permissive for this code, with costs for clients.
    - Response C2 (:577): the multi-threaded example is the stated reason for relaxing the queue's order.
    - Response C5 (:599): the authors commit to reporting what precision the single-thread client example loses.
  - **R, continued: a concrete loss of precision.** The 10-event trace of the brief is admitted by (νQ, qsi) (H1), but this code never produces it:
    - E1 responds (position 6) before D3 is invoked (position 8), so v1 is stored before D3 scans.
    - E1's faa precedes D2's ld (same location 0), and D2 returns (position 4) before E2 is invoked (position 5). So v1's slot is below v2's slot.
    - D3 therefore meets v1 first.
    - A reviewer would read a finished T6 as confirming B6's worry for this implementation.
  - **Evidence.** H1–H3. Background doc §0.5(b) and §10 say the same; the plan calls it an expected limitation.
  - **Required: an author decision before P5, recorded in the task file.** In every case, state T7's separation claim explicitly as proved, refuted or open.
    - **(a) Keep D2 and D3.** Prove the ∅ result as well (alternative 2 below; it is cheap). Rewrite WHWQueue.tex:63, :93 and :148 and the C2 answer: the case study demonstrates future-dependent linearization points with futures, not the need for the relaxation.
    - **(b) Let RMWs enter I by the tensor rule, and set xchg to (acq, rlx) as Review B asks (:301).** The tensor rule is Def. tensor-sig with the join modes of 2Counter.tex:13.
      - What changes: (wrt rel, xchg acq) and (faa (rlx, rel), xchg acq) at different locations become semi-independent, so a deq can linearize before its thread's older pending enq.
      - What stays: `Hidle` still holds. (wrt, faa), (xchg acq, faa) and (ld acq, faa) remain ordered, because faa has mode LFence, which is not below RFence. P2–P3 are unchanged.
      - What it gains: the 4-thread example becomes producible (argued, H3) and is not rel_lin under ∅ (spec.tex:112), which gives necessity at module level.
      - What it does not gain: the 10-event trace stays unproducible, for the reason given under R above.
      - Cost: this is a paper-wide change of RCMem. Counter_xy uses the same RCMem.
    - **(c) Drop "weak".**

- **[WHWQ-M-2] The TR's queue proof does not go through, and its "VLHL" framing does not match the mechanization (research-level)**
  - **Where:** Appendix/WHWQueue.tex:51–150 (invariant :55–61; enq linearization point at the store :65, :81; deq :150); Appendix/viewbased.tex:308; models/view/PrefixView.v:993–997 (`compat_fixed`); task D1.
  - **K/S.** The mechanization uses a different proof architecture:
    - The future-dependent order lives in the overlay presentation `POQueueR`: a vertex is created at the faa and completed at the store, and a deq removes any minimal complete vertex.
    - HVF is proved over whole complete traces (`poqr_sound`).
    - The planned RLHL proof keeps one possibility over `POQueueR`, not over ν_queue.
  - **P, the proof gap (H4).** The TR keeps a single possibility over ν_queue, with the enq linearization point at the store. That fails:
    1. A's faa takes slot 1 and B's faa takes slot 2.
    2. B stores, so the possibility's queue becomes [b].
    3. A stores: [b, a].
    4. D reads counter 2, and xchg(slot 1) returns a.
    The invariant still holds, since [b, a] ∈ A(s). But :150 passes from "some list in A(s1) has x at the head" to the possibility's own list, which has head b. That step does not follow.
  - **P, the VLHL framing (H5).** App. J's VLHL fixes "view-based compatible objects" (viewbased.tex:308). (νQ, I_WkQueue) is not compatible even in the weaker, fixed form `compat_fixed`. Take s1 = [enq_u v], s3 = [enq_t w, deq_u'→v], o = deq_t→v, with v ≠ w. All premises hold, but [enq v; deq_t→v; enq_t w; deq_u'→v] ∉ νQ.
  - **R.** Review B (popl2027-reviews.md:248–254: the library-correctness proofs are vague, and the mechanization does not cover the weak HW queue). The author response's proposed change 2 (:387).
  - **Required.**
    - Rewrite the TR section around `POQueueR`, HVF (ViewLHL, Part 1) and the P5–P7 RLHL proof.
    - Do not write "verified in VLHL" in the App. J sense. Either drop compatibility from App. J, which the Coq allows (`vlhl_sound` and `presentation_choice` need none), or write "RLHL over a partial-order overlay presentation".
    - Restore definitions of a blocking ν_queue and of I_WkQueue (see m-2).

### MINOR

- **[WHWQ-m-1] P4/T3 is not needed for T6, and T5 depends on the presentation (actionable; what to claim is research-level)**
  - **Where:** task C5, T3, T5, T6; models/simlin/RelaxedHoareCompLinSpec.v:276–284, :1114–1122, :1134–1139; models/simlin/RelaxedHoareCompLin.v:1206–1230; models/simlin/RelaxedHoareGSim.v:862–864.
  - **T6 needs no new lemma.** It is `gsim_rel_lin_traces` with VE := `EIhl δRC`, VF := `POQueueR A`, `S` := `RSim` from `rlhl_rsim`, and HVF := `poqr_sound`, followed by `hlift`, which gives MTraces (`EI δRC`) ↔ MTraces (`EIhl δRC`). The application type-checks.
  - **T5 needs no new lemma either.** It is `gsim_complin` or `rlhl_complin` plus `complin_hlift_under`, which work for any VF. T3 only re-derives T6 from T5.
  - **T5 is weaker than it looks.**
    - It mentions `POQueueR`, against D1's "the final theorem does not mention the presentation".
    - It is not the M-20 form (copy-cat over `EI δQ`).
    - `POQueueR` is not a complete presentation (H6): (1,0) inv enq a; (1,1) inv enq b; (1,0) res; (1,1) res is complete and rel_lin, yet `POQueueR` rejects the second invocation. So T5 cannot support a layer above the queue.
  - **Required.**
    - Drop P4, or make it optional, and prove T6 directly (about 20 lines).
    - If T5 is kept, cite it only as trace inclusion into the copy-cat of `POQueueR`.
    - A statement for every execution that does not mention the presentation would need the speculation presentation (background doc A2(ii)), not T3.

- **[WHWQ-m-2] Stale paper and review citations (actionable, documentation)**
  - **Where:** task WHWQ.md (§Concerns, T1); .rocq-review/concern-matrix.md:46; .rocq-review/research-intent.md:40, :99.
  - **What the current draft actually contains:**
    - intro.tex:113 is the outline. The contributions list (intro.tex:106) names no queue.
    - spec.tex is not input (main.tex:229 and main-tr.tex:229 have `% \input{spec}`), and its weak-queue example is commented out (spec.tex:84–112).
    - trace.tex:92 lies inside Def. coh-barriers.
    - Only the TR appendix remains (main-tr.tex:261). It uses ν_queue and I_WkQueue, which are now defined nowhere.
  - **Other corrections:**
    - The per-case-study status item comes from the author response's proposed change 2 (:387), not from the meta-review (:615).
    - The Coq name is `WHWQSpec.ERC_wf`, not `RCMem.ERC_wf`.

- **[WHWQ-m-3] Header precision in WHWQSpec (actionable)**
  - **Where:** examples/Relaxed/WHWQ/WHWQSpec.v:39–46, :315–323.
  - **Slot convention.** State it: location 0 is the counter, slot s is location `S s`, and the paper's loop index i ∈ 1..t is slot i−1 in `op_xchg`. Today :315–318 quotes "atomic-xchg(q + i, …)" above a definition at `S slot`.
  - **The tensor-rule sentence.** "The tensor rule … over per-location cells" holds only for plain operations. With the join modes, the tensor rule itself would relate, for example, (wrt rel, xchg (acq, rlx)). RMWs are excluded only by 2Counter.tex:13, and that exclusion is what makes I(enq, deq) unused (M-1).
  - **RMW modes.** Also note that RMW modes are never consulted, because `rc_si` requires `rc_plain`.

- **[WHWQ-m-4] D3 and the modes of `FQ` (research-level)**
  - **Where:** WHWQSpec.v:104–108, :323; task D3; popl2027-reviews.md:301; paper/Appendix/WHWQueue.tex:17.
  - **The xchg mode is invisible under D2.** No statement depends on it: `rc_si` excludes RMWs, and the exported RMW mode is unused because `ERC` is never tensored. So keeping rel neither tests nor answers Review B's minor comment. Acq costs no proof under D2 and is the choice that matters under M-1(b).
  - **The `FQ` modes are unvalidated interface claims.** Under the tensor rule, enq ↦ LFence and deq ↦ RFence promise message-passing order to clients:

    ```
    thread 1: x.wrt(1); enq v
    thread 2: deq -> v; x.rd     -- must return 1
    ```

    That is a strong guarantee for a "weak" queue. The header is accurate that nothing here depends on the modes.
  - **Required.** An author decision: either use acq, or justify rel in the paper. Also state what the queue modes mean.

- **[WHWQ-m-5] Non-vacuity examples and the B6 example are not mechanized (actionable)**
  - **Where:** P1–P3.
  - **Missing examples.** No Coq `POQueueR` path exhibits:
    - The future-dependent order. Example: (1,0) inv enq a; (2,0) inv enq b; (2,0) res; (1,0) res; (3,0) inv deq; (3,0) res → a. This is a path: b has no edge to a, because a was pending when b was invoked.
    - The overlap of a pending enq with a same-thread deq.
  - **Necessity.** I(enq, deq) is necessary for `POQueueR` only by hand (H1). POQueueRExample.v may cover this.
  - **Add a B6 lemma.** For one thread running `enq(1); deq()`, every complete well-formed trace of these two calls that is rel_lin to (νQ, qsi) has deq → 1 and the witness [enq 1; deq → 1].

- **[WHWQ-m-6] A header claim rests on a Python check outside the repository (actionable)**
  - **Where:** examples/Relaxed/WHWQ/POQueueR.v:31–32.
  - "With call keys and no per-thread condition the presentation is not sound" cites the bounded check. Either mechanize the counterexample or label the claim as a bounded check that the kernel did not verify.
  - The counterexample: (1,0) inv enq a; (1,1) inv enq b; (1,1) res; (2,0) inv deq; (2,0) res → b; (1,0) res. It is a path of the call-keyed variant. It is not rel_lin under qsi, because the program-order edge between the two enqueues forces a before b.

## Responses to Writer disputes

None. This is the first review of task WHWQ, and no item is marked DISPUTED.

## Concern-matrix corrections

1. **Row B6, C2 (§2).**
   - **K/S.** Replace "No queue in Coq" with:
     - `WHWQSpec` (I = {(enq, deq)}, blocking `δQ`, `νQ`, and `ERC`/`rc_si`/`δRC` per 2Counter.tex:13) and `POQueueR` with `POQueueRSound.poqr_sound`, all closed. These give HVF for (νQ, I(enq, deq)).
     - There is no module, no RLHL proof, no T6 and no execution yet.
     - Argued but not checked: the code does not need I(enq, deq) over this RCMem (M-1).
   - **P.** The main text has no queue (m-2). The TR keeps a failing single-possibility proof (M-2) and the claim at WHWQueue.tex:148, which 2Counter.tex:13 contradicts (M-1).
   - **Status.**
     - B6: partial. The blocking API is formal in Coq but not yet in the paper, and the general concern that a fixed I admits behaviours the code lacks stands.
     - C2: the paper contradicts the development, since the motivating example is not producible under D2.
     - The queue itself: still missing.
   - **Next action.** The M-1 decision, then P5–P8 and the rewrite of the TR section.
2. **§3 row "Counter_xy, weak HW queue".** Change "Weak HW queue: none" to "spec, presentation and HVF (closed); implementation, RLHL proof and T6 pending". The queue remains missing.
3. **New row: Review B minor (xchg should be acq; :301).**
   - K: `op_xchg` is (rlx, rel), and no Coq statement depends on it under D2.
   - P: WHWQueue.tex:17 is unchanged.
   - Status: open author decision (m-4, M-1(b)).
4. **§4 baseline, "No axioms".** Add `POQueueRSound.poqr_sound` and `WHWQSpec.{FQ_wf, ERC_wf, rc_si_iff, whw_rc_si}`.
5. **Row A3/Meta-4.** Record "weak-HW queue: spec and presentation soundness only". The request comes from proposed change 2 (:387).
6. **research-intent Q5.** Record the author decision of 2026-10-21 (D1–D6): keep the queue, with a blocking deq. Spec and HVF are done. The draft currently has no definition of the queue.

## Stronger or alternative approaches

1. **Prove T6 directly.** Use `gsim_rel_lin_traces`, `rlhl_rsim` and `hlift`, as described in m-1.
2. **Prove the ∅ result from the same Layer-1 proof.**
   - Define `FQ0` (semi-independence ∅) and `POQueueRstrict` (a deq invocation also requires that its thread has no pending enqueue).
   - HVF for `POQueueRstrict` under ∅ is a small variant of `poqr_sound`: the (enq, deq) case of `rhb_before` becomes a real-time edge.
   - Layer 1 gains one obligation, discharged by the same frontier argument as `Hidle`.
   - The trace set does not depend on the overlay's semi-independence. `RelaxedModuleImpl` depends only on the effect (RelaxedLang.v:222–225), and the module semantics uses only the underlay relation.
   - So a proof over `FQ0` gives rel_lin under ∅ for the same `MTraces`, and `rel_lin_mono` gives the I(enq, deq) version. This turns the "expected limitation" into a theorem and quantifies the precision loss (C5).
3. **Make the relaxation real (M-1(b)).** It keeps P2–P3 and lets a module-derived 4-thread execution separate ∅ from I(enq, deq). With T6, C2 would then get a precise answer: the relaxation is necessary and sufficient for this code. Before adopting it:
   - check, against primary sources, that the RMW reordering it permits is sound for the intended hardware or C11 targets;
   - revisit Counter_xy, which uses the same RCMem.
4. **Every execution, without the presentation.** If incomplete traces are needed (a client layer above the queue), the speculation presentation of background doc A2(ii) is required. The direct witness proves HVF only.
5. **Add the B6 single-thread lemma** (m-5).

## Redesign assessment

**P1–P3 need no redesign.** They are correct, closed and reusable under every option of M-1.

**Question 5: can every VF path the module generates be a `POQueueR` path?** Yes, and the plan's argument is correct in this framework, under the constraints below.

- **Abstract steps belong at invocation emissions**, which is where EI applies effects; the invariants (I2)/(I3) force this anyway.
  - The enq's AInv goes at the faa invocation; its vertex is the counter, which is the slot.
  - The enq's ARet goes at the wrt invocation, not its response. If ARet were at the response, a younger faa could be emitted in between, and `POQueueR` would reject the path.
  - The deq's AInv and ARet go together at the successful xchg invocation, in one `poss_steps`.
- **`Hidle`.** At the emission of B's faa, `ghost_emit` guarantees that no older entry of the thread `inv_blocks` B's faa (RelaxedHoareBase.v:289–296).
  - If an older enq A of the same thread were still pending in `POQueueR`, its wrt invocation would still be a ghost entry, and `GAge` would place that entry before B's faa.
  - That entry does block B's faa, because `rc_si wrt faa` is false.
  - So the invariant must couple "t ↦ n in `poq_pending`" with "the owner of n still owns its wrt entry".
  - It must also carry `GAge`, which is not a field of `RLHL2Hyps`.
- **Readiness.**
  - At an enq's AInv, and at a deq's AInv under D2, every older `ls_inv` call of the thread owns a blocking entry: an enq still owns its faa, and a deq still owns its ld or xchg. So `emit_ready_block_older` suffices.
  - Under M-1(b), older enqs at a deq's AInv are handled by qsi through `emit_ready_mixed`.
  - Either way the invariant needs "a deq in `ls_inv` still owns its successful-xchg entry".
- **Minimality** follows from master's `Scan`. Its two program-order uses are F2 edges: ld before xchg, and each xchg before the next.
- **Scope of T6.** T6 will hold over `EI δRC` only.
  - `EI δRC` is not a complete presentation of (`seq_legal δRC mem0`, `rc_si`) (H6). Store buffering is a counterexample: T1 inv wr x 1; T2 inv wr y 1; T1 inv rd y; T2 inv rd x, with both reads returning 0. This trace is rel_lin, but `EI` applies each write at its invocation, so the reads cannot return 0.
  - So `rlhl_rel_lin_pres` does not apply, and "every underlay that refines ν_RCMem" (2Counter.tex:13) needs absorption, which is open (M-22). State this in T6's header.
- **P4 is unnecessary** (m-1).
- **The only decision needed before P5 is WHWQ-M-1.** It fixes either `rc_si` and `op_xchg` (option b) or the presentation to prove against (option a: `POQueueRstrict` over `FQ0`).
