## Two SeqLocks on COH with LB: adversarial semantic check (part B)

### 0. Bottom line

- **The target is not met by a standard writer.** Under exactly the RLHL semantics, LB across two SeqLocks cannot come from the module when the writer is either:
  - a TicketLock writer (`plainTL`: acq and rel are `DRMW`), or
  - a single writer that reads `seq` (`s <- seq.rd(); seq.wr(s+1)`).
  
  The cause is one `dto` entry: `Rmb` orders every later R-category operation (`dto Rmb DR = dto Rmb DRMW = true`). The orchestrator's rationale in research-intent §8 ("cross-object LB … is actually exhibited") is therefore false for these writers.
- **LB does appear with a load-free single writer**, e.g. `seq.inc()` as a blind increment of category W. Section 2 gives a concrete execution. The spec's SI accepts it; ∅ rejects it.
- **Correctness holds** for a TicketLock writer, and for a single writer with a `tw_i` guard. Without the guard (two writers, no lock) it fails.
- **MP is forbidden.**
- **All four barriers are necessary only under paper-faithful tags.** With untagged `Future` (SeqLockProg's style), `rmb_a` is redundant, and so is `wmb_a` for a lock writer.
- **LP adequacy holds** under a single possibility. LPs: the final iteration's `rmb_b` for reads, `wmb_b` for writes.
- **The spec SI is not too small.** With `plainTL` it is predicted to be entirely unused: the pair is sequentially consistent across objects.

### 1. Semantics as checked

- `EIhl δ` takes effect at invocation: `RelaxedHoareSpec.ei_step` fixes the result when the invocation is emitted, and the response only matches the record.
- Frontier: `must_precede` (RelaxedModuleSemantics.v:252) gives F1 (Inv→own Res), F2 (Inv→Inv iff not SI) and F3 (Res→Inv iff in the tag). Res/Res and cross-call F1/F3 never fire, because `trace_fresh` keeps underlay handles distinct.
- Run-to-completion: the whole committed trace is queued at `tagged_invoke`. A later call's invocation must cross every pending invocation of every older same-thread call, blocked or not.
- Untagged `Future` carries the tag `resolved_in H`. With `run` (RelaxedHoareRun.v:70), each call is `FutureD (dep_of hs dix)` and is waited immediately.
- The paper's tag policy (impl.tex:120, :141): for memory, every operation except a plain read is control-ordered.

**`dto`, evaluated in the repl, both `rc`, on {DR, DW, DRMW, Rmb, Wmb, DLocal}.** Exactly these pairs are ordered:
- DR→Rmb, DW→Wmb, DRMW→Rmb, DRMW→Wmb;
- Rmb→DR, Rmb→DRMW, Rmb→Rmb;
- Wmb→DW, Wmb→DRMW, Wmb→Wmb.

Every other pair is false, in particular Rmb→DW, Rmb→Wmb, Wmb→Rmb, DW→Rmb, DR→DW, DR→Wmb, DR→DRMW, DW→DRMW and DRMW→DRMW.

### 2. Item verdicts

#### Item 1. Correctness: holds (TicketLock, or single writer with guard); fails for two writers without a lock

Underlay for the single-writer form: `E_S rc` is COH registers `LS i`, `LX i`, `LY i` (i : bool) with `oRd`/`oWr`/`oInc`/`oWmb`/`oRmb`. Barrier ghost locations are `GBw`/`GBr`, as in `RelaxedHoareLatchProg`. `sindep` means a different `ogloc` and `dto` false.

**Torn reads are impossible.** In the final iteration's emission order:
- `rd s` <F2 `rmb_a` (DR→Rmb) <F2 {`rd x`, `rd y`} (Rmb→DR) <F2 `rmb_b` (DR→Rmb) <F2 `rd s'` (Rmb→DR).
- Writer: `inc_a` <F2 `wmb_a` <F2 {`wr x`, `wr y`} <F2 `wmb_b` <F2 `inc_b`.
- For TL: `Acq` → `Wmb` holds because `DRMW` is W, and `Wmb` → `Rel` likewise.
- `s = s'` and `s` even, with `seq` strictly monotone ⇒ no `inc`/`Acq` was emitted in [rd s, rd s'] ⇒ no data write was emitted there. A data write lies strictly inside its writer's odd phase, and the phase cannot have started before `rd s` because `s` is even. So the values read are one snapshot.

**A writer's own read overlapping its own write is fine.** Same thread, same SeqLock:
- `rd s` of the read is blocked by the pending `inc` of the write (same location).
- `inc_a` of a later write is blocked by the pending `rd s`/`rd s'` of an earlier read.
- `rd x`/`wr x` are same-location.
- For TL, GT/TT/Acq/Rel are one object.
- So same-object calls serialize, in agreement with the spec's non-SI on same-component pairs.

**Retrying reader is fine.** Iterations are serialized by same-location `seq` reads and by Rmb→DR. Only the committed final iteration matters (RD-7, prophetic).

**Two writers, one SeqLock:**
- TL: `δ Acq` requires ¬held, which blocks emission, so it holds.
- Blind increment without a guard fails:
  1. w1: `inc`(1), `wmb`, `wr x 1`
  2. w2: `inc`(2)
  3. r: `rd s`=2, `rmb`, `rd x`=1
  4. w2: `wmb`, `wr x 2`, `wr y 2`
  5. r: `rd y`=2, `rmb`, `rd s`=2, so the read returns (1,2)
  6. Remaining writer events.
  
  Only (0,0), (1,1) and (2,2) are legal. So the precondition P1_i ("only `tw_i` writes SL_i") is needed, with the guard `div` as in `M_Lw`.
- Note on the TL form: `δ` has no thread id, so `Rel` can only require `held`. Holder identity must come from the ghost (an `Excl`-style clause).

#### Item 2. LB: fails for TL and seq-reading writers; holds for a load-free writer

**Obstruction (TL `plainTL`, or a seq-reading writer).** Take any execution with t1: `r1 := SL1.read(); SL2.write(1,1)` and t2 symmetric, both reads returning (1,1).
- Write2's first operation (`Acq2` of category DRMW, or `rd s2` of category DR) must cross read1's pending `rmb`s. Since `dto Rmb DRMW = dto Rmb DR = true`, F2 forbids this.
- Hence `rd x1` <F2 `rmb_b1` < `Acq2`/`rd s2` < `wmb_a2` (DRMW→Wmb, or the same location plus F3 data tag, then DW→Wmb) < `wr x2`.
- `rd x2` returns 1 ⇒ `wr x2` < `rd x2`.
- Symmetrically, `rd x2` < … < `wr x1` < `rd x1`.
- That is a cycle in a total emission order. This holds under both tag styles and any number of retries: run-to-completion queues every iteration's `rmb`.
- With `plainTL`, SB is also not derivable: `Rel2` (DRMW) blocks read1's `rmb_a`. With a seq-reading writer, SB is derivable.

**Positive design (load-free single writer).**
- Writer: `inc s; wmb; wr x vx; wr y vy; wmb; inc s`, all `dix = []`.
- Reader, paper tags: `rd s []`, `rmb [n]`, `rd x []`, `rd y []`, `rmb [n]`, `rd s []`, then the parity and equality checks, with `rnext` as below.
- Threads: `t1 = tw true` writes SL2, `t2 = tw false` writes SL1. Initial registers are 0.

The execution `lb2_exec`:
1. Overlay invocations:
   - `inv t1 0 (SRead false)`, committing trace rd 2 / rmb / 1 / 1 / rmb / 2;
   - `inv t1 1 (SWrite true 1 1)`;
   - `inv t2 0 (SRead true)`;
   - `inv t2 1 (SWrite false 1 1)`.
2. t1 emits all 12 events of write2 (`seq2`: 0→1, `x2`, `y2` := 1, `seq2`→2), each crossing all 12 pending events of read1. The checks:
   - **Inv/Inv:** pairs (DR,DW), (DR,Wmb), (Rmb,DW), (Rmb,Wmb), with distinct `ogloc`. `lb_cross` is closed in the repl.
   - **Res(read)/Inv(write):** `dep_of [] _` is False.
   - **Inv(read)/Res(write):** the handles differ.
   - **Res/Res:** False.
3. t2 emits write1 the same way.
4. t1 emits read1 in program order: `rd s1`=2, `rd x1`=1, `rd y1`=1, `rd s1`=2. All guesses match.
5. t2 emits read2 the same way.
6. Four returns (`owner_done`).

Overlay trace `lb2_trace`: four invocations, then `res write2 tt`, `res write1 tt`, `res read1 (1,1)`, `res read2 (1,1)`. It is complete.

- **Accepted at `findep2 rc`.** `findep2 (SRead i) (SWrite (negb i) _ _)` holds (`findep2_table`, closed). There are no real-time edges, so rhb is empty. The witness `[write2; write1; read1; read2]` is `seq_legal δSL s00`.
- **Rejected at ∅ (and at `si_sb := {(write_i, read_j) | i ≠ j}`):**
  - rhb edges: read1→write2 and read2→write1 (same thread, invocation order, not independent);
  - legality: read1 = (1,1) ⇒ write1 <W read1, and read2 = (1,1) ⇒ write2 <W read2;
  - so read1 < write2 < read2 < write1 < read1, a cycle.
  - Template: `RelaxedHoareCounterXY.sb_not_rel_lin0` (:832), with `seq_inc_get` (:769) and `before_idx` (:785).
- **SB** (t1: `write2; read1` = (0,0)) is also module-derived in this design.

#### Item 3. MP: forbidden

Trace: t1: `SL1.write(1,1); SL2.write(1,1)`; t2: `SL2.read()=(1,1); SL1.read()=(0,0)`.

- **Spec level,** for every `si ⊆ findep2`:
  - W/W and R/R are never independent, so w1→w2 and r2→r1 are rhb edges;
  - legality gives w2 < r2 and r1 < w1;
  - so w1 < w2 < r2 < r1 < w1, a cycle.
- **Module level,** directly:
  - `wmb_a2` waits for all of write1 (DW/Wmb→Wmb);
  - `rd x2` = 1 ⇒ after `wr x2`;
  - read1's `rd s1` and `rmb`s wait for read2's `rmb`s (Rmb→DR, Rmb→Rmb);
  - so read1 sees `seq1 ≥ 2` and `x1 = 1`, and returns (1,1) or retries.
- **Window-route shape** (client cell z: `z:=1; SL.write ‖ SL.read; z.rd`): forbidden too. The DW→Wmb and Rmb→DR entries are what decide it.

#### Item 4. Broken variants

Setup: blind-increment design, writer writes (1,1), initial (0,0), so legal results are (0,0) and (1,1). The `torn_not_rel_lin` argument uses legality only, uniformly in `si`. "Paper" means `run` with paper tags; "untagged" means the SeqLockProg shape (futures issued, waits afterwards).

| Variant | Paper tags | Untagged | Counterexample (emission order) |
|---|---|---|---|
| no `rmb_a` | broken | **correct** (`rd x` tagged with the waited `rd s`, F3) | `rd x`=0 crosses pending `rd s` (DR/DR, tag ∅); whole write; `rd s`=2, `rd y`=1, `rmb`, `rd s`=2 → (0,1) |
| no `rmb_b` | broken | broken | `rd s`=0, `rmb`, `rd x`=0, `rd s'`=0 crosses pending `rd y` (DR/DR; tag lacks `y`); whole write; `rd y`=1 → (0,1) |
| no `wmb_a` | broken | broken for an all-futures writer. TL writer with waited `Acq`: **correct** untagged, broken with paper tags (`dto DRMW DW = false`) | `wr x 1` crosses pending `inc` (DW/DW); reader `0, rmb, 1, 0, rmb, 0` → (1,0) |
| no `wmb_b` | broken | broken (TL: `Rel` crosses `WrY`, since `dto DW DRMW = false`) | `inc`(1), `wmb`, `wr x`, `inc`(2) crosses pending `wr y`; reader `2, rmb, 1, 0, rmb, 2` → (1,0) |
| no parity check | broken | broken | `inc`(1), `wmb`, `wr x 1`; reader `1, rmb, 1, 0, rmb, 1` → (1,0) |

Untagged futures over-order relative to impl.tex:120 (plain reads are not control-ordered), so they hide the necessity of `rmb_a`. Recommendation: use `run` with paper tags. Under those tags all four barriers are necessary.

#### Item 5. LP adequacy under a single possibility: holds

LPs:
- **read:** the invocation of the committed final iteration's `rmb_b`;
- **write:** `wmb_b`.

At the read's LP:
- `rd x` and `rd y` are emitted (DR→Rmb), so their actual results `rx` and `ry` are recorded.
- Linearize unconditionally (`psa_inv`) with `r_abs :=` the current abstract pair; read is total.
- Edge assertion: `reg (LS i) ≥ s ∧ (reg (LS i) = s → r_abs = (rx, ry))` together with `eihl_mine` records. It is stable because `seq` is monotone and `wr x_i`/`wr y_i` happen only while `seq_i` is odd (guarantee of `tw_i`).
- At `rd s'` with actual `s`: freeze `r_abs = (rx, ry)`.
- At return all responses matched, so `ret = (a,b) = (rx,ry) = r_abs`.

Writer: at `wmb_b`, x and y are already written, so the abstract value becomes `(vx,vy)`, which equals the concrete value. Invariant: the abstract pair equals the concrete pair except during the writer's [`inc_a`, `wmb_b`) phase; when `seq` is even they are equal.

No prophecy is needed beyond "final iteration", which is RD-7 / m-33. There is no same-thread future-dependent LP, so m-36 does not bite.

#### Item 6. Is the spec SI too small? No

Non-SI overlay pairs keep LP order in every frontier schedule:

| Pair | Readiness | Mechanism |
|---|---|---|
| R→R (any SL) | direct | the later `rmb_b` is blocked by the older read's pending `rmb`s (Rmb/Rmb; also same `GBr`) |
| W→W | direct | Wmb/Wmb (`GBw`) |
| same-SL R→W | two-step | the write's `inc_a` is blocked by the read's pending final `rd s'` (same location) |
| same-SL W→R | two-step | the read's `rd s` is blocked by the write's pending `inc_b` |

`emit_ready_block` (RelaxedHoareRun.v:780) needs direct blocking at the LP. The same-SL pairs need a phase fact: "older same-SL call not `ls_inv`", established at the earlier same-location emission and stable afterwards.

The only `si` the proof consults is (SRead j, SWrite i) and (SWrite i, SRead j) with i ≠ j, which is exactly `findep2`. So the proof is uniform for any `si ⊇ findep2`.

**With `plainTL`, prediction: provable at `si = ∅`.**
- R→W: `Acq` is blocked by `rmb` (two-step).
- W→R: `rmb_a` is blocked by the older write's pending `Rel` (DRMW→Rmb; direct).

So the TL pair never uses the SI (as with LatchSet's I_L), and LB/SB ∉ MTraces would follow for free via `rel_lin_empty_indep` (RelaxedTraceLin.v:107) and `mtraces_rel_lin_resig` (RelaxedHoareResig.v:752).

### 3. Exact statements

These typecheck in a piped repl. `lb_cross`, `rmb_blocks_read` and `findep2_table` are proved; their statements are shown below.

```coq
Inductive SLoc := LS (i : bool) | LX (i : bool) | LY (i : bool).
Inductive SOp := oRd (l : SLoc) | oWr (l : SLoc) (v : nat) | oInc (l : SLoc) | oWmb | oRmb.
Definition ocat o := match o with oRd _ => WT.DR | oWr _ _ | oInc _ => WT.DW | oWmb => WT.Wmb | oRmb => WT.Rmb end.
Definition sindep rc o o' := ((if GLoc_eq_dec (ogloc o) (ogloc o') then true else false) || WT.dto rc (ocat o) (ocat o')) = false.
Definition δS (m : Regs) (o : SOp) : sar o -> Regs -> Prop := (* oRd l: r = m l /\ m' = m; oWr l v: m' = upd m l v;
   oInc l: m' = upd m l (S (m l)); barriers: m' = m *)
Inductive FOp := SWrite (i : bool) (vx vy : nat) | SRead (i : bool).
Definition findep2 rc o o' := fobj o <> fobj o' /\ WT.dto rc (fcat o) (fcat o') = false.   (* write↦Wmb, read↦Rmb *)
Definition δSL (st : (nat*nat)*(nat*nat)) o : far o -> _ -> Prop := (* setp / getp *)
Definition M_S rc si (tw : bool -> tid) : RelaxedModuleImpl (E_S rc) (F_S si) := fun op t => match op with
  | SWrite i vx vy => if Pos.eqb t (tw i) then run (wnext i vx vy) [] W0 else div | SRead i => run (rnext i) [] (R0 0) end.
Lemma lb_cross rc i c w : In c [oRd (LS i); oRmb; oRd (LX i); oRd (LY i)] ->
  In w [oInc (LS (negb i)); oWmb; oWr (LX (negb i)) 1; oWr (LY (negb i)) 1] -> sindep rc c w.        (* proved *)
Lemma rmb_blocks_read rc l : ~ sindep rc oRmb (oRd l).                                              (* proved *)
Theorem sl2_rlhl2 rc si tw : (forall o o', findep2 rc o o' -> si o o') ->
  RelaxedHoareBase.RLHL2Hyps (VE := EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F_S si) δSL)
    (IS tw) (RS tw) (GS tw) (M_S rc si tw) ((regs0, []), []) (s00, []).            (* target, closed *)
Corollary sl2_complin : RCompLin (M_S rc si tw) (EI δS) (regs0,[]) (EI δSL) (s00,[]).  (* classic; rlhl_complin_eihl *)
Corollary sl2_rel_lin s : MTraces (EI δS) (M_S rc si tw) (regs0,[]) s -> PrefixView.complete s ->
  rel_lin sel s si (seq_legal δSL s00).                                             (* via complin_ei_rel_lin *)
Theorem lb2_exec rc si : exists evs c, module_execution_tagged (EI (F := E_S rc) δS) (M_S rc si tw12)
  (initial_tagged_module _ (regs0, [])) evs c /\ overlay_events evs = lb2_trace si /\ PrefixView.complete (lb2_trace si).
Lemma lb2_rel_lin rc : rel_lin sel (lb2_trace (findep2 rc)) (findep2 rc) (seq_legal δSL s00).
Lemma lb2_not_rel_lin0 : ~ rel_lin sel (lb2_trace ∅) (fun _ _ => False) (seq_legal δSL s00).
Theorem sl2_0_no_rlhl2 rc : forall I R G, ~ RLHL2Hyps (VE := EIhl δS) (VF := EI (F := F_S ∅) δSL) I R G (M_S rc ∅ tw12) _ _.
Theorem mp2_not_rel_lin rc si : (forall o o', si o o' -> findep2 rc o o') -> ~ rel_lin sel mp2_trace si (seq_legal δSL s00).
```

### 4. Writer sub-tasks

These follow the latch criteria: Rocq 9.3.0, new files only, no `Admitted`, `Axiom`, `vm_compute` or `native_compute`.

| ID | File(s) | Content | Accept | Size / iterations |
|---|---|---|---|---|
| SL2.0 | — | Author decision RF-1 | — | — |
| SL2.1 | `examples/Relaxed/RelaxedHoareSL2Prog.v` | §3 definitions; `sindep_iff`, `E_S_table`, `lb_cross`, `findep2_table`; `wnext`/`rnext` with flags; `M_S`; guard; `mtraces_guard` (port of LatchProg:717) | closed | 500–800 / 1 |
| SL2.2 (go/no-go, ‖) | `…/RelaxedHoareSL2Exec.v` | `lb2_exec`, `lb2_rel_lin`, `lb2_not_rel_lin0`/`_sb`; `sb2_exec`; `mp2_not_rel_lin`; `torn_exec` for 5 flags plus `torn_not_rel_lin`; `sl2_0_no_rlhl2` | closed; negatives ⊆ {classic, eq_rect_eq} | 1,500–2,200 / 2; about 56 module steps each, build a select tactic first |
| SL2.3 | `models/simlin/RelaxedHoareReady.v` | `ready_of_older_si` (`invocation_ready` from "older same-thread `ls_inv` ⇒ SI"; a sub-proof of `emit_ready_block_older`); phase-fact stability via `GAge`; `pending_upclosed` (a call's pending invocations are up-closed under its Inv–Inv `must_precede`, from `local_frontier`) | closed | 300–500 / 1 |
| SL2.4 | `…/RelaxedHoareSL2Inv.v` | `IS`/`RS`/`GS`: coupling `ls_inv` ⇔ LP pending; `seq` monotone; parity ⇔ writer phase; abstract = concrete outside [`inc_a`, `wmb_b`); writes only by `tw_i`; `eihl_rec_used`; `GAge` | closed, statements frozen | 900–1,300 / 2 |
| SL2.5 (checkpoint) | `…/RelaxedHoareSL2Reader.v` | `read_provable` via `rp_run`/`run_method_provable` (:466/:514), record facts (`eihl_mine_*`) | closed; stop if over 1,500 lines or 3 iterations | 1,000–1,500 / 2–3 |
| SL2.6 | `…/RelaxedHoareSL2Writer.v` | `write_provable` for `tw_i`; vacuous otherwise (`div_no_produce`) | closed | 700–1,100 / 2 |
| SL2.7 | `…/RelaxedHoareSL2.v` | §3 main theorem and corollaries; `sl2_discriminates` | as K | 300–500 / 1 |

Order: SL2.1 → (SL2.2 ‖ SL2.3) → SL2.4 → (SL2.5 ‖ SL2.6) → SL2.7. Total about 5,200–7,900 lines.

### 5. Research-level flags for the author

- **RF-1 (decisive).** Two-SeqLock LB needs a writer path with no R-category or `Rmb` operation. Options:
  - **(a)** blind increment `oInc` (category W). This extends COH; trace.tex:59/:83 has neither barriers nor RMW.
  - **(b)** writer-supplied version `write(n,vx,vy)` with a history precondition. This needs `EIe`.
  - **(c)** TicketLock exported as `DW`. This is a sound weakening (`out_leb`/`in_leb DW DRMW = true`, checked), but the LB then comes from the declaration, not from the lock.
  - **(d)** keep the standard writer and show LB via SL ⊎ z (the window-route `lb_wit` shape, derivable here with `plainTL`), plus "two-SL LB ∉ MTraces".
  
  Recommendation: (a), with scope wording, or (d) if hardware realism matters.
- **RF-2.** Hardware caveat, to be confirmed by the author:
  - arm64 and powerpc `smp_rmb` (DMB ISHLD / lwsync) also order R→W;
  - LKMM forbids this LB for the standard `sequence++` writer (rmb; data; wmb);
  - so the LB is table-level (`Rmb ↛ W`) and not observable on ARMv8.
- **RF-3.** Untagged futures versus the paper's tag policy (§4). This affects which barrier claims hold.
- **RF-4.** The TicketLock pair is predicted sequentially consistent across objects: its SI is admitted but unused.
- **RF-5.** Reviewer B :212 and :311-316 remain unaddressed. This is a reordering over sequentially consistent registers.

### 6. Checks run (read-only repl, Rocq 9.3.0)

- The `dto` table above.
- `out_leb`/`in_leb` for DW against DRMW.
- §3 definitions, `M_S` via `run`/`SStep`, and the `RLHL2Hyps`/`MTraces` statements typecheck.
- `lb_cross`, `rmb_blocks_read`, `rmb_blocks_rmw` and `findep2_table` are proved.
- Names confirmed by grep:
  - `must_precede` :252, `module_step_tagged` :578;
  - `RLHL2Hyps` RelaxedHoareBase.v:793;
  - `cc_rel_lin` :916, `rlhl_complin_eihl` :1265, `complin_ei_rel_lin` :936;
  - `emit_ready_block` :780;
  - `mtraces_resig_iff` :530, `mtraces_rel_lin_resig` :752;
  - `div_no_produce` LatchProg:651.

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareRun.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareLatchProg.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareCounterXY.v