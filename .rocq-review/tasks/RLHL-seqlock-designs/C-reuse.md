**Headline.** The target cannot be built from the window-route program text. With a TicketLock writer (or any writer that reads `seq`) and the `rmb` reader, no module execution over a `dto`-table COH underlay produces load buffering (LB) across two SeqLocks. The verified specification can admit LB, but the implementation never exhibits it — the same outcome as LatchSet's `lbw`. The orchestrator's rationale in research-intent §8 (2026-10-15), "cross-object LB between two SeqLocks over COH is actually exhibited by the implementation", is wrong for that text. LB becomes a module trace only if each writer's accesses before it publishes are neither reads nor releases. Concretely that means single-writer SeqLocks over COH registers, as in §3.

All Rocq checks below used a piped `rocq repl` (Rocq 9.3.0, this repository's `-R` flags). Nothing was written.

## 1. The window-route SeqLock (Q1)

**Program text** (`SeqLockProg.v:219-257`):
- Every call is an untagged `Future`. Under the lazy reading, every invocation after the first `Wait` is tagged with that call's handle: `{ha}` in `write`, `{hg}` in a read iteration. The next read iteration's `GT` is tagged with all earlier handles.
- `write vx vy`: `Future sAcq; Wait fa;` then five futures `sWmb, sWrX vx, sWrY vy, sWmb, sRel`, then five `Wait`s, then `Ret tt`.
- `read_body loop`: `Future sGt; Wait fg (s)`; then futures `sRmb, sRdX, sRdY, sRmb, sTt s`; then `Wait ft (r); Wait f1; Wait fx (a); Wait fy (b); Wait f2`; then `if r then Tau loop else Ret (a,b)`.
- `CoFixpoint read := read_body read`, with `read_unfold` via `PPid`. `zwrite` and `zread` are a single `Future` plus `Wait`.

**Underlay `E rc K`.**
- Operations: `SOp = sAcq | sRel | sGt | sTt s | sWrX v | sWrY v | sRdX | sRdY | sWmb | sRmb | sWrZ v | sRdZ`.
- SI: `sindep rc K o o' := SL.upres rc K (uc_of o dflt) (uc_of o' dflt) = false`, where `upres = same_obj (uobj ·) || dto rc (ucat K ·)`.
- `same_obj` orders TL/X/Y/Z among themselves but not B (barriers).
- `plainTL = {acq, rel ↦ DRMW (Acc KRW false false); gt, tt ↦ DR}`. The only assumption the window proof makes about it is `K_ok` (acq and rel are writes, gt and tt are reads).

**TicketLock specification** (window route, `SeqLockCOH.v:275-310`):
- State `mkSt own hold sx sy sz`.
- `Acq`: needs `own` even and `hold = None`; increments `own` and sets `hold := Some (th e)`.
- `Rel`: needs `hold = Some (th e)`; increments `own`.
- `GT v`: returns `v = own`. `TT s r`: returns `r = odd s || own ≠ s`.
- `TicketLockCOH` exports exactly `plainTL` (`exports_plainTL`).

**Overlay `F rc`.**
- Operations `fWrite`, `fRead`, `fZw`, `fZr`, with categories Wmb, Rmb, DW, DR.
- `findep rc o o' := fcomp o ≠ fcomp o' ∧ dto rc (fcat o) (fcat o') = false`.

**LB and MP on the window route.**
- `X_lb = mkX [BZr 1; BW 1 1] [BR [] 2 1 1; BZw 1] lb_wit`. The writer's whole block runs before its own earlier `RdZ`. This works because `dto DR DRMW = false`.
- `lb_wf` and `lb_allowed` are at witness level (`WT.Conclusion`).
- `mp_forbidden` holds for all retries, tickets and witnesses, from `seqlock_z_composition` alone.
- `seqlock_S1` places the linearization points at the first `wmb` of a write (index 1) and the first `rmb` of a read's final iteration (`base + 1`).

## 2. The blocker: LB across two SeqLocks (repl-checked)

**Repl facts (both `rc`).**
- `dto Rmb DRMW = true` and `dto DRMW Rmb = true`.
- `dto DR DRMW = false`, `dto Rmb DW = false`, `dto Wmb Rmb = dto Rmb Wmb = false`, `dto DW Rmb = false`.
- In `E rc plainTL`: `~SI sRmb sAcq`, `~SI sRmb sRel`, `SI sRdZ sAcq`. All three proved in the repl, closed.

**Argument.** Take t1: `SL1.read; SL2.write(1,1)` and t2: `SL2.read; SL1.write(1,1)`, with both reads returning (1,1).
1. A read's final iteration must start (`GT`/`G`) after the other thread's publication (`Rel`, or the final `seq` write). Otherwise `own`/`seq` changes inside the read window and `TT` retries.
2. `tagged_invoke` enqueues the whole prophesied trace of the read, retries included, before the write's events. A write event can therefore be emitted only by crossing every pending event of the read.
3. If neither thread's write crosses its own read's final-iteration `rmb`, the orders form a cycle: `Rel2 < GT2_fin < Rmb_t2 < Acq1 < Rel1 < GT1_fin < Rmb_t1 < Acq2 < Rel2`.
4. So some `Acq` must cross a pending `Rmb` of its own thread. `isRmb c && isR d` makes this impossible for any read-kind access (`Acq`, `Rel`, a `seq` read).

**Necessary condition.** Every event of the write up to and including its publication must cross a pending `rmb` and the read's pending plain reads. Under `dto` this means no read-kind access, no release, and no access to the reader's locations.

**Consequences.**
- `M rc plainTL` duplicated: LB is not a trace.
- Single-writer SeqLock whose writer reads `seq`: not a trace either.
- With `K_w = {acq, rel ↦ DW; gt, tt ↦ DR}`, LB is a trace. The repl confirms `out_leb rc DW DRMW = in_leb rc DW DRMW = true`, so TicketLock may soundly export DW, `K_ok K_w = true`, and every window lemma holds for `K_w`. But the LB then exists only over the weakened TicketLock interface, not over the TicketLock-over-COH tower. I do not recommend claiming it.

## 3. Ways to get LB, and the recommendation

| Variant | Writer | Reader | LB a trace? | Overlay SI used? | Underlay |
|---|---|---|---|---|---|
| (D) window text ×2 | TicketLock `Acq…Rel` | `rmb` | no | no; verifiable at ∅ (§4) | TL⊗X⊗Y ×2 ⊗B, TL atomic |
| (O3a) **recommended** | `inc seq; wmb; x; y; wmb; inc seq`, `inc` a blind increment of category DW | `rmb` | yes | yes | COH regs + wmb/rmb + `inc` |
| (O3b) | `v←lrd w` (DLocal); `wr seq (v+1)` (tag on `v`); `lwr w (v+2)`; `wmb`; `x`; `y`; `wmb`; `wr seq (v+2)` | `rmb` | yes | yes | COH regs + barriers + a writer-private register |
| (O3c) | `rd seq` / `wr seq` | address and fake data dependencies, no `rmb` | yes | yes, (rd, rd) too | pure `E_L` ops |
| (K_w) | TicketLock exported DW | `rmb` | yes | yes | interface fiction |

O3a and O3b need one writer per instance (a P1-style guard, as in `M_Lw`). A lock writer always has a read-kind prefix, so multi-writer SeqLocks cannot exhibit LB here. This settles the open question "single writer vs a lock in the underlay spec" in research-intent §8.

**Checks for O3a (by hand against `dto`).**
- Every write event (DW or Wmb, on `seq_j`, `x_j`, `y_j`) crosses every read event (DR or Rmb, on `seq_i`, `x_i`, `y_i`), so LB is a module trace.
- SB is also a trace (`R1` crosses DW and Wmb).
- MP is not a trace: Wmb/Wmb and Rmb/Rmb pairs are ordered.
- Within a thread, F2 alone orders `G→R1→{A,B}→R2→T` and `I1→W1→{X,Y}→W2→I2`. No `dix` tags are needed.

## 4. Reusing `M rc K` and `E rc K` on the RLHL route (Q2)

**What typechecks** (repl):
```coq
Definition δSL (s : SL.State) (o : SOp) (v : sar o) (s2 : SL.State) : Prop :=
  exists t, SL.pre s (SL.mkEv t 0 (uc_of o v)) = true /\ s2 = SL.post s (SL.mkEv t 0 (uc_of o v)).
Check (fun rc I R G => RLHL2Hyps (VE := EIhl (E := E rc SL.plainTL) δSL)
        (VF := RelaxedHoareSpec.EI (F := F rc) δF) I R G (M rc SL.plainTL) ((SL.init,[]),[]) (((0,0),0),[])).
```
Because `ei_step` passes no thread id (m-37), the existential `t` turns `Rel`'s holder check into "held by someone". The invariant tracks the holder instead.

**What blocks reuse.**
1. **Shape.**
   - `RProvable` covers every construct: `rp_future` handles untagged futures with the lazy tag `resolved_in H`, and `rp_wait_pending` handles the dependent `Wait (MkFutureRef op h)` after the continuation is applied.
   - But `M` is not `run`-shaped, so `run_method_provable`, `rp_run`, `RunCtx`/`dprec_run` and the wave-1 tactics (`ex_step`, `m_step`) do not apply.
   - Reuse would need a new kit: a dag for the "issue k futures, then wait k" shape under lazy tags, plus a custom coinduction for `read := read_body read`. It is not `doWhileR`, so `rp_dowhile` does not apply; `RProvable_coind` with a suffix-enumerating predicate or a hole-parametrised variant would. Estimate +700–1,100 lines. Rewriting `M` into `run` form changes the term and loses `M_shape` and `seqlock_module_rel_lin`.
2. **Underlay.** TicketLock is an atomic sequential object. The claim would read "over TL ⊗ COH cells ⊗ barriers", and there is no RLHL vertical composition yet to put TicketLock over COH below it (D3/D7, deferred).
3. **Two instances.** There is no RLHL tensor theorem, and `E rc K`/`F rc` contain one SeqLock and z. Two instances need new indexed signatures anyway.
4. **No LB** (§2).

**What remains feasible on the window text:**
- **(O1), SeqLock ⊎ z, maximum reuse.** `E rc plainTL`, `F rc` and `M rc plainTL` are used verbatim. LB with z *is* a module trace: it is `lb_wit`'s schedule, where `Acq`, `Wmb`, `WrX` and `Rel` cross `RdZ` (SI). Readiness for (zr, write) and (read, zw) uses `findep`, since `dto DR Wmb = dto Rmb DW = false`. The paper's signature gets a universal negative through `rlhl_complin_eihl` and `cc_rel_lin`, with `RelaxedHoareResig.mtraces_resig_iff` to move module traces from `F rc` to `paper_cf`'s SI.
- **(D), two TicketLock SeqLocks.** Verifiable at overlay SI = ∅ with these linearization points:
  - write at `Acq`;
  - read at the final iteration's second `Rmb`, identified through the ghost, with a dead-branch flag when `own ≠ s` or `s` is odd.
  - Every same-thread pair is then directly blocked: Rmb→DRMW, DRMW→Rmb, Rmb/Rmb, Wmb→DRMW, and same TicketLock.
  - Result: SC-linearizable, with LB admitted by the contract but not exhibited.

## 5. Two SeqLocks (Q3): a new indexed signature, not a renaming

There is no tensor theorem and `ren_rlhl2` only covers one-call renaming bodies, so the two instances need one module over indexed signatures. Proposed file `examples/Relaxed/RelaxedHoareSeqLock2Prog.v`, following `RelaxedHoareLatchProg.v`'s Part 1 pattern (`gloc`, `ccat`, `lpres`, `sindep`, `δcoh`, `opval`):
```coq
Inductive SLoc := Sq (i : bool) | Sx (i : bool) | Sy (i : bool) | Sw (i : bool).   (* Sw: O3b only *)
Inductive SOp := sRd (l : SLoc) | sWr (l : SLoc) (v : nat) | sInc (l : SLoc) | sWmb | sRmb.
Definition sar (o : SOp) : Type := match o with sRd _ => nat | _ => unit end.
Definition scat (o : SOp) : WT.DCat :=          (* Sw ↦ DLocal in O3b *)
  match o with sRd _ => WT.DR | sWr _ _ | sInc _ => WT.DW | sWmb => WT.Wmb | sRmb => WT.Rmb end.
Definition sindep rc o o' : Prop := (same_sgloc o o' || WT.dto rc (scat o) (scat o')) = false.
Definition E_S rc : RelaxedSig.t := {| effect := SSig; handle := nat; semi_independent := sindep rc; mode := fun _ => Local |}.
Definition δS (m : SLoc -> nat) (o : SOp) : sar o -> (SLoc -> nat) -> Prop :=
  match o with sRd l => fun r m' => r = m l /\ m' = m | sWr l v => fun _ m' => m' = upd m l v
             | sInc l => fun _ m' => m' = upd m l (S (m l)) | _ => fun _ m' => m' = m end.
Inductive FOp := fW (i : bool) (vx vy : nat) | fR (i : bool).
Definition F2 (si : FOp -> FOp -> Prop) : RelaxedSig.t := {| …; semi_independent := si; mode := fun _ => Local |}.
Definition slsi (o o' : FOp) : Prop :=            (* = findep, read ↦ Rmb, write ↦ Wmb, component = instance *)
  match o, o' with fR i, fW j _ _ | fW i _ _, fR j => i <> j | _, _ => False end.
Definition slRA (o o' : FOp) : Prop := match o, o' with fW i _ _, fR j => i <> j | _, _ => False end.  (* spec.tex:81 *)
Definition δF2 (st : bool -> nat * nat) (o : FOp) : far o -> (bool -> nat * nat) -> Prop := …
Definition M2 rc si : RelaxedModuleImpl (E_S rc) (F2 si) :=
  fun op _ => match op with fW i vx vy => run (wnext i vx vy) [] W0 | fR i => run (rnext i) [] (R0 0) end.
Definition M2w rc si (tw : bool -> tid) : RelaxedModuleImpl (E_S rc) (F2 si) :=
  fun op t => match op with fW i _ _ => if Pos.eqb t (tw i) then M2 rc si op t else div | fR _ => M2 rc si op t end.
```
`M2` must stay parametric in `si`: `ThreadEvent` is indexed by the signature (latch finding 4), so the negatives instantiate `si` directly and need no re-signature step.

**Linearization points and readiness** (all past-determined).
- **Write:** at `I1`, the first `seq` increment.
- **Read:** at the final `T`, when `s` is even and `seq = s`. Coupling: a read is `ls_inv` iff it owns a pending `seq_i` access.

Readiness for each pair (older call, then younger call on the same thread):
- **Same instance:** same location, so direct blocking (`emit_ready_block`).
- **Write j, then write i:** the older write's pending `W1` blocks the younger `I1` (`dto Wmb DW = true`).
- **Read j, then read i:** recorded blocking. The younger read's `R2` was blocked (DR→Rmb) by the older read's pending `seq` accesses, so these are no longer pending.
- **Read j, then write i, and write j, then read i:** overlay SI (`slsi`). This is where LB and SB live.

This needs one new generic lemma, a three-way `emit_ready_mixed` (SI, or direct block, or recorded block), generalising `emit_ready_block_older` and `emit_ready_SI`.

**Main statements:**
```coq
Theorem sl2_rlhl2 rc tw : RLHL2Hyps (VE := EIhl (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 slsi) δF2)
  (I2 tw) (R2 tw) (G2 tw) (M2w rc slsi tw) ((regs0,[]),[]) (st0,[]).
Corollary sl2_rel_lin rc tw s : MTraces (EI δS) (M2w rc slsi tw) (regs0,[]) s -> PrefixView.complete s ->
  rel_lin PrefixView.sel s slsi (seq_legal δF2 st0).
Theorem lb2_exec rc si tw : tw true = t2 -> tw false = t1 -> exists evs c,
  module_execution_tagged (EI δS) (M2w rc si tw) (initial_tagged_module _ (regs0,[])) evs c /\
  overlay_events evs = lb2_trace si /\ PrefixView.complete (lb2_trace si).
Lemma lb2_not_rel_lin_RA : ~ rel_lin sel (lb2_trace slRA) slRA (seq_legal δF2 st0).   (* also at ∅ *)
Corollary sl2_RA_no_rlhl2 rc tw : forall I R G, ~ RLHL2Hyps (VE := EIhl δS) (VF := EI (F := F2 slRA) δF2) I R G (M2w rc slRA tw) _ _.
Lemma mp2_not_rel_lin : ~ rel_lin sel mp2_trace slsi (seq_legal δF2 st0).
```
The universal negative follows the pattern of `cxy_mixed_no_rlhl2`. Expected `Print Assumptions`:
- `sl2_rlhl2` and the executions: closed.
- Copy-cat inclusion: {`classic`}.
- `rel_lin` corollaries and negatives: {`classic`, `eq_rect_eq`}.

**Invariant sketch.**
- Per instance: `seq_i` even implies `(x_i, y_i)` equals the abstract state; `seq_i` odd implies the writer `tw i` has a linearized write in progress whose values are the abstract state.
- Only `tw i` increments `seq_i`, by +1. Data writes happen only while `seq_i` is odd.
- Read edge assertion (latch §2.5 kit): `∃a', eihl_mine κ (Op κ (sRd (Sx i)) a') ∧ (even s ∧ seq_i = s → a' = x_i)`. It is stable because `seq` only increases.
- The window-route LP (first `rmb` of the final iteration) is unusable in a forward proof: `A` and `B` have not been emitted yet.

## 6. The paper (Q4)

**What `Appendix/SeqLock.tex` claims.**
- SeqLock is built over TicketLock (a Counter plus a TSO ticket cell) and TSO data cells. There are no barriers.
- The underlay is given as a TSO state with per-thread view frontiers `H`: rules Wrt, Rd, Acq, Rel, GetTick, TestTick.
- The overlay SI is **empty**: an SC SeqLock with timestamps.
- Invariant: `I^state` (`slstate = laststate`, under `∃H_O`) and `I^view` (`h_gt < h_x, h_y < h_tt`, and no `rel` fires in the window).
- The read's linearization point is `test_ticket` returning 0. The write effectively linearizes at `rel`, since `laststate` updates on release.
- The proof uses view-based (VLHL-style) reasoning and is not mechanized as described: `examples/View/SeqLockTSO.v` is SC `RGILogic`, per concern-matrix row 106.

**`spec.tex:71-81`** gives read ↦ `rfence` and write ↦ `lfence`, and says the tensor of SeqLocks gives `I_RA`, i.e. only (wrt, rd) pairs: SB yes, LB no.
- The window route already refutes this signature (`paper_signature_fails`, `paper_modes_fail`).
- O3 would refute it at the RLHL level through `sl2_RA_no_rlhl2`.

**What O3 supports (proposed wording).** "Two single-writer SeqLocks over a sequential, multi-copy-atomic register file with ordering-only barriers `wmb`/`rmb` (and a no-return increment), with SI from the ordering table plus same location, verified in RLHL (copy-cat inclusion ν_E;cc; `rel_lin` on complete traces) against two pair-registers with SI {(rd_i, wrt_j), (wrt_i, rd_j) | i≠j}. The implementation exhibits LB and SB, forbids MP, and is not relaxed-linearizable under `I_RA` or ∅."

**The paper must change:**
- trace.tex must define COH with barriers (and `inc`/local registers). The current `I_COH` (overview.tex:164) has none.
- spec.tex:78-81 must be rewritten.
- The single-writer precondition must be stated.
- State the scope: MCA, not RC11/ARMv8/TSO/oMCA, and not `memory/Cell.v`.
- State that a lock-based SeqLock does not exhibit LB here (the §2 necessary condition).
- Say that the appendix's TSO/TicketLock proof concerns a different object, or replace it.

## 7. Reviewers (Q5)

- **B:215 ("No example verified on the COH model"):** answered, provided the paper names the extension. It would be the first library verified over COH in RLHL, mechanized, with a module-derived concurrent relaxed execution. Weaker than "COH" as printed: the underlay adds barriers, ν;cc is only over `EI δS`, and the result does not cover "any underlay relaxed-linearizable to ν_E" (M-20/M-22).
- **B:212 (modelling relaxed consistency by instruction reordering):** **not** answered. The underlay *is* table-driven reordering over SC registers.
- **B:311-316 (RC11 soundness and a client):** not answered. Concern-matrix B1 records the models as incomparable. MP-forbidden and LB/SB-allowed are trace facts, not a verified client. The a=b client (B4/D4) remains open.

## 8. Which lemmas can be cited (Q6)

- **Window route only** (cite as such; they do not transfer, since the underlay, program and instance count all differ): `seqlock_S1`, `seqlock_S1_ord`, `z_S1`, `seqlock_z_composition`, `mp_forbidden`, `lb_wf`, `lb_allowed`, `retry_wf`, `lb_refutes`, `paper_signature_fails`, `paper_modes_fail`, `torn_with_local_tl`, `torn_impossible_with_plain_tl`, `tower_composition*`, `seqlock_module_rel_lin(_K)`.
- **`M_shape`:** module level, but specific to `M rc K`. RLHL route L does not need it. It only helps O1 build executions.
- **Signature-level facts, reusable:** `WT.dto`, `dtable`; `SL.dto_W_wmb`, `dto_wmb_W`, `dto_R_rmb`, `dto_rmb_R`; `sl_cf`, `sl_cf_unordered`; `barrier_exports_strictly_between`; `paper_signature_not_inheritable`; `exportable`, `out_leb`, `in_leb`.
- **O1 only:** `SOp`, `E`, `F`, `M`, `uc_of`, `of_uc`, `upres_ret_indep`, `read_unfold`; `SL.pre`, `post`, `State` (for `δSL`); `lb_wit` as a schedule template.
- **The proof idea transfers, not the lemmas:** `read_window`, `wr_disjoint`, `read_value` (parity and "no increment inside the window") become stability lemmas.

## 9. Writer sub-tasks for O3

Shared criteria: Rocq 9.3.0, new files only, `_CoqProject` updated, no `Admitted`, `Axiom` or `vm_compute`, and a K/S/P/R header.

| ID | File(s) | Accept when | Lines / iterations |
|---|---|---|---|
| SL2.1 | `examples/Relaxed/RelaxedHoareSeqLock2Prog.v` | the §5 definitions, `wnext`/`rnext`, `M2`/`M2w`, the guard lemmas (`mtraces_guard` pattern), `sindep_same_loc`, well-formedness, ported tactics; the `sl2_rlhl2` statement typechecks; smoke `program_produces_tagged` for a write and for a read that retries once | 700–1,000 / 1 |
| SL2.2 (go/no-go, right after SL2.1) | `…/RelaxedHoareSeqLock2Exec.v` | `lb2_exec` for all `si` (about 100 module steps), `lb2_rel_lin_direct`, `lb2_not_rel_lin_RA`, the ∅ variant, `mp2_not_rel_lin`; closed / {`classic`, `eq_rect_eq`}. **If `lb2_exec` fails, stop.** | 900–1,400 / 2 |
| SL2.3 (in parallel) | `models/simlin/RelaxedHoareReady.v` | `emit_ready_mixed` (SI, direct block, or recorded block); closed | 150–300 / 1 |
| SL2.4 | `…/RelaxedHoareSeqLock2Inv.v` | `I2`, `R2`, `G2`; coupling; `GAge`; `seq` monotonicity and data-frozen stability; `sl2_rlhl2_of_sem` | 900–1,300 / 2 |
| SL2.5 (checkpoint) | `…/RelaxedHoareSeqLock2Reader.v` | `read_provable` via `run_method_provable`; escalate to route S if over 1,500 lines or 3 iterations | 900–1,400 / 2–3 |
| SL2.6 (parallel to SL2.5) | `…/RelaxedHoareSeqLock2Writer.v` | `write_provable` for `t = tw i`; vacuous otherwise (`div_no_produce`) | 600–1,000 / 1–2 |
| SL2.7 | `…/RelaxedHoareSeqLock2.v` | `sl2_rlhl2`, `sl2_complin`, `sl2_rel_lin`, `sl2_RA_no_rlhl2`, ∅ negative, MP corollary | 300–500 / 1 |

Total about 4,400–7,000 lines over 10–14 iterations.

Optional:
- O1 (SeqLock ⊎ z on the window text): 3,600–5,600 lines.
- A mechanized §2 negative for the TicketLock text: heavy, since it is universal over schedules. I recommend stating it as a paper argument.

## 10. Research-level points for the author

1. **Writer variant.**
   - (a) `inc` classified DW. Physically this resembles a store-class atomic (ARM `ST<OP>`, LKMM `atomic_inc`); whether DMB LD or LKMM orders it is not verified here.
   - (b) A writer-private register classified DLocal. Justification: no other thread observes it.
   - (c) Keep the TicketLock text and give up LB (verifiable at ∅).
2. **Single writer per instance.** This is inherent to LB here, not a simplification.
3. **Overlay SI is `slsi`.** It is the window route's `rmb`/`wmb` signature. It refutes `I_RA` (spec.tex:81), and unlike LatchSet's `I_L` it is genuinely used.
4. **Linearization points.** Write at the first `seq` access, read at the final `seq` re-read, with ghost-based "pending `seq` access" coupling (the RD-7 analogue). The window route's barrier LPs cannot be used forward.
5. **Record the correction** to the research-intent §8 rationale (§2 above).
6. **Scope wording.** MCA register file, ν;cc only, COH+barriers needs a paper definition, and B:212 remains unaddressed.

### Critical files for implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareLatchProg.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareRun.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/SeqLockProg.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/SeqLockCOH.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareCounterXY.v