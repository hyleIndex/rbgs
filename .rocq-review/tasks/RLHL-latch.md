<!-- RLHL-latch plan, produced 2026-10-15 by a read-only design panel (three Plan agents: (A) error infrastructure, (B) LatchSet object and proof, (C) adversarial semantic check; one skeptical rocq-research-reviewer synthesis). Saved verbatim by the orchestrator. Individual designs in .rocq-review/tasks/RLHL-latch-designs/. -->

# RLHL-latch plan (design panel, 2026-10-15)

The correct LatchSet meets the target under this semantics, and all five broken variants fail. I checked this by hand against `must_precede` and an evaluated `dto` table. None of it is mechanized yet.

Two corrections to the reports:
- **LatchSet does not need `GSimRelErr` or `RLHL2HypsE`.** The planned underlay, `EIhl δcoh`, has `Error := False`, so the implementation-side error obligation of decision (a) is vacuous for this object. The decided error form, `RCompLinErr`, can be derived from an error-free RLHL proof plus a small licensing lemma. So A1 (the trace-level definitions) moves onto the LatchSet path, and A2–A4 come after it.
- **Report B is wrong about trace reuse.** It says the module's traces are the same for every overlay relation "by conversion". They are not: `ThreadEvent` is indexed by the whole signature, and the repl rejects the conversion. Comparing traces across overlay relations needs an explicit transport lemma.

## 1. Goal and claims (K/S/P/R targets)

**Goal.** An RLHL verification of LatchSet with:
- the full idiom from `../rbgs/examples/Relaxed/LatchSetProg.v` (decision LD-0 (a′), trailing `mb`, `print()`);
- the underlay `VE := EIhl (E := E_L rc) δcoh`: a sequential register file with `wmb`/`rmb`/`mb` as ordering-only operations, and semi-independence (SI) taken from `WindowTable.dto` plus "same location";
- the overlay spec `VF := EI (F := F_Lsi si) (δbset N)`;
- the error form required by decision (a);
- refutation of the five broken variants.

**K (kernel).**
- All new files build under Rocq 9.3.0.
- No `Admitted`, `Axiom`, `vm_compute` or `native_compute`.
- Expected `Print Assumptions`:
  - RLHL instance (`latch_rlhl2`) and executions: closed;
  - copy-cat inclusion: {`classic`}, via `rlhl_complin_eihl`;
  - `rel_lin` corollaries and universal negatives: {`classic`, `eq_rect_eq`}, via `cc_rel_lin`.

**S (statements).** Section 2.5.
- Every positive result is about the guarded module `M_Lw`, transferred to `M_L` under P1.
- Complete traces only for `rel_lin`; copy-cat inclusion for every prefix.
- Single possibility.
- The underlay is the copy-cat over `EI δcoh` (ν;cc), not "any underlay relaxed-linearizable to ν_E".

**P (paper), current text.** LatchSet is described only as planned or ongoing:
- intro.tex:7, :99, :106;
- overview.tex:2, :331;
- overview.tex:333: "an atomic set specification with a relaxed ordering contract that admits load buffering".

The paper's COH (trace.tex:59, :83) has **no barrier operations**. "COH + wmb/rmb/mb" therefore needs a new paper definition before the paper can cite this result.

**R (reviewers).**
- Reviewer B: "No example verified on the COH model" (popl2027-reviews.md:215). The response promises to "consider adding a library case study over COH" (:537).
  - Satisfiable, provided the paper says "COH registers with barrier operations, multi-copy-atomic sequential presentation".
- Reviewer B: "Insufficient justification for modeling relaxed consistency by instruction reordering" (:212). **Not** addressed: this underlay *is* instruction reordering over an SC register file.
- Reviewer B (:311-316) also asks for a logic sound against "a weak memory model such as RC11" and a client. **Not** addressed.

**Concern-matrix effect once delivered.**
- B5 can move toward ✅ with the scope wording above.
- The intro/overview LatchSet row (:82) becomes 🟡: the RLHL instance exists, the write-snapshot and tensor parts do not.
- The m-8 row stays 🟡 until a non-vacuous implementation-side error is exercised (`m8_gap`).

## 2. Exact definitions and statements

### 2.1 Error infrastructure (A1, `models/simlin/RelaxedHoareErrSpec.v`)

Report A's A1 is adopted with three changes:
- `bad` takes the thread id;
- the overlap clause is dropped from LatchSet's `bad`;
- a licensing lemma is added.

The definitions below typecheck in the repl (section 7, check 9).

```coq
Variant TItem (F : RelaxedSig.t) := TEv (e : ThreadEvent F) | TErr (k : CallKey F) (op : Sig.op (RelaxedSig.effect F)).
Inductive module_error_tagged {E F} (VE : LTS E) : CallKey F -> Sig.op (RelaxedSig.effect F) -> TaggedModuleConfig VE -> Prop :=
| tagged_error cand op (ret : Sig.ar op) q pool queue queue' used
    (Hsel : select_frontier_tagged cand queue queue')
    (Hact : In (Build_CallEntry (fst (ts_owner cand)) (snd (ts_owner cand)) (ActiveCall op ret)) pool)
    (Herr : Error VE (untag (ts_event cand)) q) :
    module_error_tagged VE (ts_owner cand) op (Build_TaggedModuleConfig q pool queue used).
Definition MTracesE VE M σ0 (s : list (TItem F)) := exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\
  (s = map TEv (overlay_events evs) \/ exists k op, module_error_tagged VE k op c /\ s = map TEv (overlay_events evs) ++ [TErr k op]).
Definition RTracesClosed VF v s := MTracesE VF idF v s \/ exists p k op tl, MTracesE VF idF v (p ++ [TErr k op]) /\ s = p ++ tl.
Definition RCompLinErr M VE σ0 VF v0 := forall s, MTracesE VE M σ0 s -> RTracesClosed VF v0 s.
Definition Licensed VF v (s : list (ThreadEvent F)) := exists p k op tl, MTracesE VF idF v (p ++ [TErr k op]) /\ map TEv s = p ++ tl.
Definition EIe δ (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop) : LTS F :=
  {| State := St * list (Op F); Step := ei_step δ;
     Error := fun ev s => match te_ev F ev with InvEv _ o => bad s (te_tid F ev) o | _ => False end |}.
```

**Lemmas.**
- `mtraces_in_mtracesE`.
- `mtracesE_noerr : (∀ ev q, ¬ Error VE ev q) → MTracesE VE M σ0 s → ∃ s', s = map TEv s' ∧ MTraces VE M σ0 s'`.
- `rtraces_closed_of_rtraces`, `rtraces_closed_split`, `rcomplin_err_of_rcomplin`, `rcomplin_of_err`, `hliftE`.
- `mtraces_eie_ei`: a configuration transport. `TaggedModuleConfig (EIe …)` and `TaggedModuleConfig (EI …)` are different types (check 9), so this cannot be done by conversion.
- `complin_err_rel_lin`: as in A §2.
- **New:** `pool_keys_trace`. The keys of `tm_calls c` are exactly the overlay keys invoked in `overlay_events evs`; `DeadCall` entries stay in the pool (`returned_not_fresh`).
- **New:** `cc_license_indep`:
  - Premises:
    - `RTraces (EI δ) (s0,[]) p`;
    - `(t,h)` was not invoked in `p`;
    - `∀ σ, bad σ t op` (a state-independent error);
    - every pending same-thread record of `p` has an op that is semi-independent of `op` in `F`.
  - Conclusion: `Licensed (EIe δ bad) (s0,[]) (p ++ [inv t h op])`.
  - Proof idea:
    1. Transport the copy-cat run.
    2. `tagged_invoke` of `idF` with a fresh inner handle.
    3. `select_frontier_tagged` of the new inner invocation (Res entries never block an untagged `idF` invocation).
    4. `tagged_error`.

**Validation of decision (a).** In `examples/Relaxed/RelaxedHoareLockErr.v`, part 1, prove the negative half of `m8_gap` (A §8): `[TEv inv(Go); TErr k Go] ∈ MTracesE Mbad (EIe δlock bad_lock)`, which `RTracesClosed (EI δG)` rejects. Together with the old positive half (`RLHL2Hyps` over `EIhl δlock`), this is the only evidence that the implementation-side obligation has teeth, since it is vacuous for LatchSet.

### 2.2 The COH+barrier underlay (port of sibling Part 1)

- Locations and operations: `LLoc := Lseq | Ln c | La c i`; `LOp := oRd l | oWr l v | oWmb | oRmb | oMb`; `lar (oRd _) = nat`, and `unit` otherwise.
- Ordering: `ogloc` (data locations, plus ghost locations `GBw`/`GBr`/`GMb`), `ocat` (rd↦DR, wrt↦DW, wmb↦Wmb, rmb↦Rmb, mb↦DFence).
- SI: `sindep rc o o' := (same ogloc || WT.dto rc (ocat o) (ocat o')) = false`.
- Signature: `E_L rc := {| effect := LSig; handle := nat; semi_independent := sindep rc; mode := fun _ => Local |}`.
- Port the lemmas `sindep_iff`, `mb_ordered`, `sindep_same_loc`, `E_L_well_formed`, `E_L_table`.

New definitions:

```coq
Definition Regs := LLoc -> nat.  Definition regs0 : Regs := fun _ => 0.
Definition upd (m : Regs) l v : Regs := fun l' => if LLoc_eq_dec l l' then v else m l'.
Definition δcoh (m : Regs) (o : LOp) : lar o -> Regs -> Prop :=
  match o with oRd l => fun r m' => r = m l /\ m' = m | oWr l v => fun _ m' => m' = upd m l v | _ => fun _ m' => m' = m end.
Definition opval (x : RelaxedTraceLin.Op (E_L rc)) : nat.   (* read value, 0 otherwise; avoids eq_rect_eq *)
```

What this underlay means:
- A read's value is fixed when its invocation is emitted (`ei_step`). Memory is multi-copy atomic and SC.
- All relaxation comes from the frontier: (F2) reorders invocations of one thread by `sindep`, and (F3) orders invocations after the responses named in their tags.

### 2.3 Overlay and preconditions (port of sibling Part 2, generalised)

```coq
Definition F_Lsi (si : POp -> POp -> Prop) : RelaxedSig.t := {| effect := PSig; handle := nat; semi_independent := si; mode := fun _ => Local |}.
Definition F_L rc := F_Lsi (findep rc).          (* I_L = {(print, insert k)}, F_L_indep_iff *)
Definition δbset N S (o : POp) : par o -> list nat -> Prop :=
  match o with OIns k => fun _ S' => S' = latch_new N k S | OPrint => fun r S' => r = S /\ S' = S end.
Definition δsetU S (o : POp) : par o -> list nat -> Prop :=
  match o with OIns k => fun _ S' => S' = ins_sorted k S | OPrint => fun r S' => r = S /\ S' = S end.
Definition P1 tw (s : list (ThreadEvent (F_Lsi si))) := forall t h k, In (Build_ThreadEvent t (InvEv h (OIns k))) s -> t = tw.
Definition P2 N s := exists K, NoDup K /\ length K <= N /\ forall t h k, In (Build_ThreadEvent t (InvEv h (OIns k))) s -> In k K.
Definition latch_badP1 tw : list nat * list (Op (F_Lsi si)) -> tid -> POp -> Prop :=
  fun _ t o => match o with OIns _ => t <> tw | OPrint => False end.
```

- P1 is "only `tw` inserts". The non-overlap clause is dropped (section 5).
- P2 is "at most N distinct inserted keys".

### 2.4 The program (port of sibling Parts 3–5, 7; text verbatim)

**Generic interpreter** in `models/simlin/RelaxedHoareRun.v`, generalised from the sibling to any signature `G`:
- `SStep St R := SDone r | SCall (op : Sig.op (effect G)) (dix : list nat) (k : Sig.ar op -> St)`;
- `dep_of (hs : list (handle G)) dix q := ∃ i, In i dix ∧ nth_error hs i = Some q`;
- `CoFixpoint run next hs st` and `run_unfold`, as in the sibling at `LatchSetProg.v:727-764`.

**Example side.** Port verbatim: `Flags`, `full_idiom`, `no_addr`, `no_rmb`, `no_wmb1..3`, `no_mb`, `ins_sorted`, `latch_new`, `ipos`, `wpos`, `cwr` (with `cwr_size` and `cwr_effect`), `wplan`, `wnext`, `cnt`, `adep`, `krmb`, `ridx`, `pval`, `retry_step`, `rnext`. Then:

```coq
Definition M_L N fl rc si : RelaxedModuleImpl (E_L rc) (F_Lsi si) := fun op _ =>
  match op with OIns k => run (wnext N fl k) [] WSeq | OPrint => run (rnext N fl) [] (RSeq 0 []) end.
CoFixpoint div {E R} : Prog E R := Tau div.          (* div_no_produce: closed, section 7 *)
Definition M_Lw N fl rc si tw : RelaxedModuleImpl (E_L rc) (F_Lsi si) := fun op t =>
  match op with OIns k => if Pos.eqb t tw then M_L N fl rc si op t else div | OPrint => M_L N fl rc si op t end.
Lemma mtraces_guard V σ0 s : MTraces V (M_L N fl rc si) σ0 s -> P1 tw s -> MTraces V (M_Lw N fl rc si tw) σ0 s.
```

- **File name.** Use `RelaxedHoareLatchProg.v`, not `LatchSetProg.v`, which exists on `relaxed-lin` and would collide on a merge.
- **What is not ported.** `FuturesShape` and Parts 6, 8–14 are needed only for the fallback route S. Part 17 depends on `memory.TableBarrier`/`Drain`, which this branch lacks.

### 2.5 Main theorem and corollaries

```coq
Theorem latch_rlhl2 N scan rc si tw :                                   (* closed *)
  RLHL2Hyps (VE := EIhl (E := E_L rc) δcoh) (VF := RelaxedHoareSpec.EI (F := F_Lsi si) (δbset N))
    (IL N tw) (LR N tw) (LG N tw) (M_Lw N (full_idiom scan) rc si tw) ((regs0, []), []) ([], []).
Corollary latch_complin : RCompLin (M_Lw …) (EI δcoh) (regs0, []) (EI (δbset N)) ([], []).            (* classic *)
Corollary latch_cc_P1 s : MTraces (EI δcoh) (M_L N (full_idiom scan) rc si) (regs0,[]) s -> P1 tw s ->
  RTraces (EI (δbset N)) ([],[]) s.                                     (* every prefix; classic *)
Corollary latch_rel_lin s : … -> PrefixView.complete s -> P1 tw s -> rel_lin sel s si (seq_legal (δbset N) []).
Corollary latch_rel_lin_set s : … -> P1 tw s -> P2 N s -> rel_lin sel s si (seq_legal δsetU []).
(* instances: si := findep rc (paper's I_L); si := (fun _ _ => False), then rel_lin_empty_indep for every indep *)
Theorem latch_complin_err N scan rc tw :                                (* classic; after A1 *)
  RCompLinErr (M_L N (full_idiom scan) rc (findep rc)) (EI δcoh) (regs0, [])
              (EIe (δbset N) (latch_badP1 tw)) ([], []).
Lemma latch_noerr : forall k op c, ~ module_error_tagged (EI δcoh) k op c.   (* Error := False *)
```

**Proof of `latch_complin_err` without `GSimRelErr`.**
- If the trace satisfies P1, use `latch_cc_P1` and `rtraces_closed_of_rtraces` (through `mtraces_eie_ei`).
- Otherwise, cut at the first insert invocation by `t ≠ tw`. Its prefix `p` satisfies P1, so `latch_cc_P1` applies to `p`.
- Then apply `cc_license_indep`. Its side condition holds at `si = findep rc`: pending older calls on `t` are prints, and `findep OPrint (OIns k)` holds.

**Proof architecture** (B's invariant, C's readiness coupling).

Linearization points (LPs): a call linearizes at the emission of the invocation of its **last pending `Lseq` access**, read from `γ′`.
- **Insert:** its `Wr(Lseq, s+2)`. Steps: `psa_inv` with `latch_new N k S`, then `psa_ret tt`.
- **Print:** its final `Rd(Lseq)`.
  - Take `psa_inv` with `r := S_now` unconditionally.
  - Take `psa_ret` inside `RetCond`.
  - Correctness flows through records, not DAG edges. The edge assertion is `∃ r_i, eihl_mine κ_i (Op κ_i (oRd (La c i)) r_i) ∧ (reg Lseq = s → r_i = reg (La c i))`. It is stable by monotonicity of `seq` and the copy-freeze fact.
  - `opval` and `eihl_mine_res` identify `r_i` with the prophesied `v_i` at return.

`IL` (B §2.3, I1–I9):
- I1 `Iren`-style pool and records;
- I2 `eihl_rec_used`;
- I3 `S` is sorted and `|S| ≤ N`;
- I4: if `q := reg Lseq`, then copy `odd q` represents `S`;
- I5: when no call is midflight, `q` is even and both copies represent `S`;
- I6;
- I7, replaced by C's coupling: for every pool entry `k`, `k` is `ls_inv` iff `k` owns a pending `Lseq` invocation in `γ`;
- I8 `GAge`;
- I9: inserts in the pool are on `tw`.

Guarantee and rely (frame style, as `Gren`/`Rren`):
- `seq` changes only by +1, and only under `Excl k`;
- a data write to location `l` requires `copy_of l ≠ odd q`;
- the abstract state `S` changes only under `Excl k`.

`Excl k := pendingMb k γ ∧ no older tw-entry is oMb`. It is unique by `GAge`.

Readiness (`emit_ready_block`, generic):
- An older same-thread `ls_inv` call has a pending `Lseq` entry earlier in the ghost.
- That entry `inv_blocks` the LP by `sindep_same_loc`, which contradicts `ghost_emit`.
- So `invocation_ready` never consults the overlay relation `si`.

### 2.6 Witnesses and negatives

The negatives use five concrete complete executions (C §3, re-checked in section 5). In each one:
- `N = 1`, initial memory is all zeros, writer `tw` runs `insert(5)`, and reader `r ≠ tw` runs `print()`, which returns `[0]`;
- the overlay trace is complete and satisfies P1 and P2.

```coq
Theorem torn_exec fl si : In fl [no_addr scan; no_rmb scan; no_wmb1 scan; no_wmb2 scan; no_wmb3 scan] ->
  exists evs c, module_execution_tagged (EI δcoh) (M_Lw 1 fl rc si tw) (initial_tagged_module _ (regs0,[])) evs c /\
    overlay_events evs = torn_trace /\ PrefixView.complete torn_trace /\ P1 tw torn_trace /\ P2 1 torn_trace.   (* closed *)
Lemma torn_not_rel_lin indep : ~ rel_lin sel torn_trace indep (seq_legal (δbset 1) []).   (* closed; legality only *)
Theorem latch_broken_no_rlhl2 scan rc si tw fl : In fl broken ->
  forall I R G, ~ RLHL2Hyps (VE := EIhl δcoh) (VF := EI (δbset 1)) I R G (M_Lw 1 fl rc si tw) ((regs0,[]),[]) ([],[]).
Theorem latch_flags_table : (positive for full_idiom) /\ (negatives for the five).
```

Positive non-vacuity (B §4):
- **`latch_retry_exec`:** a complete, overlapping run in which the print retries once.
- **`latch_reorder_exec`:** the verified module itself reorders underlay events. The reader emits `Rd(La c 0)` before `Rd(Ln c)`, and the writer emits `Wr(Ln false)` before `Wr(La false 0)`.
- **`lbw` datum:**
  - `lbw ∈ RTraces (EI (δbset 1))` at `F_L rc`, so the contract I_L admits it;
  - `lbw` is not `rel_lin` under ∅;
  - `lbw ∉ MTraces (EI δcoh) (M_L 1 full rc (findep rc))`. This last part needs the transport lemma of task L.8.

## 3. Writer sub-tasks

These criteria apply to every task:
- Rocq 9.3.0 with `PATH=/opt/homebrew/bin:$PATH`;
- `_CoqProject` updated and the Makefile regenerated;
- no edits to existing `.v` files, and no edits to the sibling checkout;
- no `Admitted`, `Axiom`, `vm_compute` or `native_compute`;
- a K/S/P/R header with `Print Assumptions`.

| ID | Files | Targets | Accept when | Size / iterations | Risks |
|---|---|---|---|---|---|
| **L.1** | `models/simlin/RelaxedHoareRun.v` | generic `SStep`/`dep_of`/`run`/`run_unfold`; `rp_run` (via `RProvable_coind`); `dprec_run` (Inv–Inv iff ¬SI, Res_i→Inv_j iff i ∈ dix_j, Inv_j→Res_j); `GAge` and its preservation under invoke/emit/return/`lin_update`; `emit_ready_block`; monotonicity of `Done` under `EIhl` | closed; smoke test: `rp_run` re-derives a one-call body (`RelaxedHoareInherit` renaming or `CounterEIhl`) | 600–1,000 / 1–2 | dependent `Wait (MkFutureRef op h)` |
| **L.2** (after L.1's `run`) | `examples/Relaxed/RelaxedHoareLatchProg.v` | sections 2.2–2.4: port, `δcoh`, `δbset`, `δsetU`, `opval`, `div_no_produce`, `M_Lw`, `mtraces_guard`, P1/P2; the sibling's `ex_step`/`ex_wait`/`ex_done` tactics plus a `select_next` crossing tactic | closed; the header maps each definition to sibling lines; the `M_L` body matches the sibling text | 800–1,100 / 1 | generic `run` vs the sibling's `E_L`-specialised one |
| **L.3** (‖ L.4) | `examples/Relaxed/RelaxedHoareLatchBroken.v` | section 2.6: `torn_exec` (five schedules), `torn_not_rel_lin`, `latch_broken_no_rlhl2` (∀ `si`) | closed / {`classic`, `eq_rect_eq`} | 1,200–1,800 / 2 | about 40 module steps each; build the tactic first, then one variant, then the rest |
| **L.4** | `examples/Relaxed/RelaxedHoareLatchInv.v` | `IL`, `LG`, `LR`, `Excl`, `midflight`, coupling, `Ω_ins`/`Ω_prt`; `excl_unique`, `seq_mono_R`, `stable_copy_R`, `regs_frozen_R`, generic location-frame lemma; `latch_rlhl2_of_sem : (∀ t op, MethodSem …) → RLHL2Hyps …` | closed; statements frozen before L.5/L.6 | 900–1,300 / 2 | stating phase facts stably at a stuck insert (count, not parity) |
| **L.5** (checkpoint) | `…/RelaxedHoareLatchReader.v` | `print_provable : MethodProvable … t OPrint Ω_prt Qprt`, both `scan` values, route L | closed; header lists the genuine `ns_if`/`bw_if` premises. **If over 1,500 lines or 3 iterations without closing: stop and escalate route S (RD-6)** | 1,000–1,500 / 2–3 | `ns_if` growth over the unbounded `Γ`; under `scan_all_N` the rmb lacks `#m`, so all value facts must be record-level |
| **L.6** (‖ L.5) | `…/RelaxedHoareLatchWriter.v` | `insert_provable` for `t = tw`; vacuous `MethodSem` for `t ≠ tw` | closed | 1,200–1,800 / 2–3 | `cwr_effect` coupling; wmb-chain edge design (phase facts on (F2) chains only) |
| **L.7** | `…/RelaxedHoareLatch.v` | section 2.5 (except the error form); `si := findep rc` and `si := ∅` instances; `latch_rel_lin_set` (P2 bridge) | as in section 1 K | 300–600 / 1 | none |
| **L.8** (‖ anytime) | `models/simlin/RelaxedHoareResig.v` | `resig F si`, `ev_resig`, configuration transport, `mtraces_resig` (both directions), `rel_lin_resig` | closed | 200–350 / 1 | configuration typing |
| **L.9** | `…/RelaxedHoareLatchExec.v` | `latch_retry_exec`, `latch_reorder_exec`, `lbw` datum (needs L.7, L.8) | closed / {`classic`, `eq_rect_eq`} | 600–1,000 / 1–2 | length |
| **L.10** (‖ anytime) | `models/simlin/RelaxedHoareErrSpec.v`; `examples/Relaxed/RelaxedHoareLockErr.v` part 1 | section 2.1 including `pool_keys_trace` and `cc_license_indep`; negative half of `m8_gap` | closed, except `complin_err_rel_lin` ⊆ {`classic`, `eq_rect_eq`} | 500–800 / 1–2 | the `EIe`↔`EI` configuration transport |
| **L.11** | `…/RelaxedHoareLatchErr.v` | `latch_noerr`, `latch_complin_err` (I_L) | {`classic`} | 250–400 / 1 | first-violation cut on the overlay trace |
| deferred | A2 `GSimRelErr`, A3 `RLHL2HypsE`/`method_soundE`, rest of A4, RLHL-internal error re-proof (LS-B), `no_mb` positive | — | after LatchSet, or when the first erroring underlay is verified | ~2,500+ | — |

**Order.** L.1 → L.2 → L.4 → (L.5 ‖ L.6) → L.7 → (L.9, L.11).
- L.3 can start right after L.2 and runs in parallel with L.4–L.6.
- L.8 and L.10 run in parallel with everything; they touch disjoint `models/` files.
- Estimated total: about 7,500–11,000 lines, 14–20 Writer iterations. The reader checkpoint (L.5) is the go/no-go point.

## 4. Research-level decisions still open for the author

- **RD-1. Form of the first deliverable.**
  - (a) An error-free RLHL proof of `M_Lw`; the conditional statements for `M_L`; `latch_complin_err` derived via L.10/L.11.
  - (b) Build A2/A3 first and re-prove LatchSet over `EIe` inside RLHL.
  - (c) (a) without the error form.
  - **Recommend (a).** For this underlay the implementation obligation is vacuous; (b) costs about +2,500 lines and adds nothing to the LatchSet claim.
- **RD-2. Capacity.**
  - (a) RLHL against the saturating `δbset`, which the code implements exactly, recovering the unbounded set under P2.
  - (b) Capacity as an `EIe` error. This is state-dependent, and licensing is existential over copy-cat runs, so it is angelic.
  - **Recommend (a).**
- **RD-3. P1 = "only `tw` inserts".** Drop non-overlap, which is shown unnecessary in section 5. **Recommend yes.** Also update the sibling's latchset-plan P1 note (author action).
- **RD-4. Exported relation.** Export I_L, as the paper does, and also state the ∅ corollary, which shows the implementation over COH never uses I_L.
  - Reword overview.tex:333: the contract admits load buffering; the COH implementation does not exhibit it (`lbw`).
- **RD-5. Trailing `mb`.** It is not needed for single-object relaxed linearizability here (section 5). The paper must not attribute it to object correctness. Decide whether `no_mb` should be mechanized (optional, about +600 lines and a two-writer invariant).
- **RD-6. Proof route.**
  - Route L (syntactic `RProvable`) supports "verified in RLHL".
  - The fallback route S (direct `MethodSem` via the ported `ML_shape`) supports only "satisfies the semantic RLHL triple".
  - **Recommend L,** with the L.5 checkpoint.
- **RD-7. LP identification.**
  - "Last `Lseq` access" reads the call's committed (prophetic) trace from the ghost; it relies on run-to-completion (m-33).
  - A past-determined alternative exists: linearize the print at a retry read whose current record equals `s`, with a flag for dead branches.
  - **Recommend the ghost form now;** record the caveat.
- **RD-8. Claim scope (paper).**
  - Claimable: "sequential, multi-copy-atomic register file with ordering-only barrier operations and table SI", plus ν_E;cc rather than `verimpl`'s "any underlay relaxed-linearizable to ν_E" (M-20 converse, M-22 open).
  - Not ARMv8, buffered or oMCA. Not the window-route LatchSet.
  - Needs a COH+barriers definition in trace.tex.
- **RD-9. D5 (ii)–(vi).**
  - Adopt: (ii) as `bad` with a thread id; (iv) key+op tags; (vi) `PossError` absorbs, which is forced, as A and C agree.
  - Defer (iii) the licensed `cte_noerr` and (v) error-aware layering until A2/A3.
- **RD-10. `m8_gap` in the first deliverable?** Recommend yes, negative half only. Otherwise decision (a)'s implementation-side clause is never exercised non-vacuously.

## 5. Semantic findings

- **The correct LatchSet satisfies the target (hand argument).**
  - Invariant J: when `seq = 2j`, copy 0 equals `A_j`; when `seq = 2j+1`, copy 1 equals `A_j`. The copy numbered `seq & 1` is never written while `seq` keeps its value.
    - Copy-0 writes lie between `wr seq 2j+1` and `wr seq 2j+2` (wmb1 W→Wmb→W, wmb2).
    - Copy-1 writes come after `wr seq 2j+2` (wmb3) and before the next `wr seq` (mb, or the next wmb0).
  - The reader's final iteration:
    - Its data-read invocations lie strictly between T1 and T3: the F3 address tag `{#s}` puts them after T1's response, and R→Rmb→R puts them before T3.
    - So `s(T3) = s` implies the values equal copy `s&1`, which is the abstract state at T3.
  - The writer's own reads are correct because every write is tagged after them, through `K2` and `{#s}` (F3).
- **All five broken variants fail.** I re-checked every crossing in C's schedules against `must_precede` and the evaluated `dto` table:
  - `no_wmb1`: w6/w7 cross pending w4 (W/W); r3 crosses r2 (R/R).
  - `no_wmb2`: w9 crosses w6/w7.
  - `no_wmb3`: w11/w12 cross w9.
  - `no_addr`: r2/r3 (tag {}) cross r1 using the predicted copy, which is value prediction of an address.
  - `no_rmb`: r5 (tag {}) crosses r2/r3.
  - In every case the print returns `[0]`, while the only legal results are `[]` and `[5]`.
  - These verdicts agree with LKMem on shapes only.
- **Surprises.**
  1. I_L is never used. Every LP is an `Lseq` access, so same-location (F2) orders a thread's LPs. The proof is uniform in `si`, including ∅.
  2. The trailing `mb` is not needed. Over this semantics `no_mb` is correct: same location plus wmb0 serializes overlapping same-thread inserts. Its role is to serialize same-thread calls cheaply (the `Excl` argument) and to give the DRFence export.
  3. Non-overlap in P1 is unnecessary. Overlay calls of one thread are asynchronous; only `call_fresh` is checked.
  4. Module traces cannot be shared across overlay relations by conversion. `Record ThreadEvent (E : RelaxedSig.t)` is indexed by the signature (check 5).
  5. Prophetic invocation means a `div` body or a stuck print can never be invoked. Liveness statements are meaningless here.
  6. Under `no_wmb1`, a writer with a wrong prophesied `seq` value can still perform copy-0 writes, which are tagged `K2` only. This is a second failure mode, harmless for the claims.
  7. The underlay is multi-copy atomic. It is not the oMCA scope adopted on 2026-10-13, so it does not support ARMv8 claims.

## 6. Disagreements and how they were resolved

| Topic | A | B | C | Resolution and evidence |
|---|---|---|---|---|
| What comes first | error infrastructure (A1–A3) | LatchSet stage 1, errors later | LatchSet; errors not needed (via `div` and bounded set) | B/C, refined: `EIhl δcoh` has `Error := False`, so A2/A3 are not needed; A1 plus a derived corollary give decision (a)'s form (section 2.5) |
| P1 | `tw` and no overlapping insert (pending record) | `tw` only | `tw` only | `tw` only (section 5, item 3); A's pending-record clause also makes licensing scheduler-dependent |
| `pre`/`bad` and thread id | `bad` with tid | needs tid | RLHL-3c.md:199 draft is thread-blind | A's `bad` with tid; it typechecks (check 9) |
| Readiness coupling | — | insert ⇒ pending `oMb`; print ⇒ pending `Rd(Lseq)` | `ls_inv` ⇔ pending `Lseq` access | C's uniform rule, independent of `mb`; B's `Excl` (pending `mb`) kept for writer exclusivity |
| Trace independence from `si` | — | "by conversion" | `rel_lin_mono` | B is **wrong** (check 5); prove `latch_rlhl2` for every `si`, and add L.8 for cross-relation claims |
| Port scope and file name | — | Parts 1–5, 7, new name | Parts 1–16 plus `FuturesShape`, same path | B (route L does not need the shape lemmas); new name avoids the `relaxed-lin` collision |
| Need for `mb` | — | conjecture: redundant | `no_mb` correct | C, by my check (section 5, item 2); optional mechanization |
| Negatives | — | one optional (`no_wmb1`) | all five, first | all five, early but parallel (L.3); they validate discriminating power |
| Print LP and prophecy | — | uses the call's prophesied future via the ghost | "no prophecy needed" | B is accurate: the ghost is the committed trace; RD-7 gives a past-determined alternative |
| `cprov_dowhile` | — | not applicable; needs `rp_run` | (L) via `RProvable_coind` | agreed: the body is a `CoFixpoint run` with `FutureD`, not `doWhileR` |
| Chaos-state fallback | rejected (linearized results cannot change) | — | — | agreed: `psa_*` never revert `ls_linr`; not needed |

## 7. Feasibility checks I ran

All checks used a piped `rocq repl` from the repo root with the `_CoqProject` `-R` flags, under Rocq 9.3.0. Nothing was written to disk.

1. **Build.** `make -n` reports nothing to do except the known `structures/DCPOs.v`.
2. **Byte identity.** `diff -q` against `../rbgs` shows that `RelaxedSemantics.v`, `RelaxedModuleSemantics.v`, `RelaxedLang.v` and `WindowTable.v` are identical. `FuturesShape.v` is absent here.
3. **`dto` (both `rc`).**
   - false: DR/DR, DR/DW, DW/DR, DW/DW, DR/Wmb, Wmb/DR, DW/Rmb, Rmb/DW, Wmb/Rmb, Rmb/Wmb, DR→DRFence;
   - true: DW→Wmb, Wmb→DW, DR→Rmb, Rmb→DR, DFence↔DR, DFence↔DW, Wmb/Wmb, Rmb/Rmb, DRFence→DR, DRFence/DRFence.
4. **Target statement typechecks.** `RLHL2Hyps (VE := EIhl (E := E_L rc) δcoh) (VF := RelaxedHoareSpec.EI (F := F_Lsi si) (δbset N)) I R G M ((fun _ => 0, []), []) ([], [])` typechecks.
5. **Conversion across overlay relations fails.**
   ```
   The term "s" has type "list (ThreadEvent (F_Lsi si1))"
   while it is expected to have type "list (ThreadEvent (F_Lsi si2))".
   ```
   The match-based `retag : ThreadEvent (F_Lsi si1) -> ThreadEvent (F_Lsi si2)` does typecheck.
6. **`div_no_produce`: Closed under the global context.**
   ```coq
   From Stdlib Require Import List. Import ListNotations.
   Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
   Require Import models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics.
   Import RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics.
   CoFixpoint div {E R} : Prog E R := Tau div.
   Lemma div_unfold {E R} : @div E R = Tau div. Proof. rewrite (PPid div) at 1. reflexivity. Qed.
   Lemma div_no_produce {E R} t (tr : list (TaggedEvent E)) (r : R) : ~ program_produces_tagged t div tr r.
   Proof.
     intros (c' & Hex & Hterm).
     assert (Hinv : forall (c : ProgramConfig E R) tr c', program_execution_tagged t c tr c' -> pc_prog c = div -> pc_prog c' = div).
     { clear. intros c tr c' H. induction H as [c | c1 c2 c3 tr Hs Hx IH | c1 c2 c3 m tr Hs Hx IH]; intros Hc; auto;
         apply IH; destruct c1 as [p H]; cbn in Hc; subst p; rewrite div_unfold in Hs; inversion Hs; subst; cbn;
         first [reflexivity | symmetry; apply div_unfold]. }
     specialize (Hinv _ _ _ Hex eq_refl). destruct Hterm as [H0 r0 _]. cbn in Hinv. rewrite div_unfold in Hinv. discriminate.
   Qed.
   Print Assumptions div_no_produce.   (* Closed under the global context *)
   ```
7. **Corollary chain at ∅: assumptions {`eq_rect_eq`, `classic`}.** The script uses abstract stand-ins for `E_L`/`F_Lsi`. The parts the chain uses (`δcoh`/`δbset`) are as in section 2, with `LLoc` simplified to `nat` and `latch_new` simplified to `if length S <? N then k :: S else S`.
   ```coq
   From Stdlib Require Import List Bool Arith.PeanoNat. Import ListNotations.
   Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
   Require Import models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics models.simlin.RelaxedModuleSemantics.
   Require Import models.simlin.RelaxedTraceLin models.simlin.RelaxedPossibility models.view.PrefixView.
   Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLin models.simlin.RelaxedHoareCompLinSpec.
   Import RelaxedSig RelaxedLTSSpec RelaxedModuleSemantics RelaxedTraceLin RelaxedHoareCompLin RelaxedHoareCompLinSpec.
   Inductive LOp : Type := oRd (l : nat) | oWr (l : nat) (v : nat) | oWmb | oRmb | oMb.
   Definition lar (o : LOp) : Type := match o with oRd _ => nat | _ => unit end.
   Definition LSig : Sig.t := {| Sig.op := LOp; Sig.ar := lar |}.
   Definition E_L (si : LOp -> LOp -> Prop) : RelaxedSig.t := {| effect := LSig; handle := nat; semi_independent := si; mode := fun _ => Local |}.
   Inductive POp : Type := OIns (k : nat) | OPrint.
   Definition par (o : POp) : Type := match o with OIns _ => unit | OPrint => list nat end.
   Definition PSig : Sig.t := {| Sig.op := POp; Sig.ar := par |}.
   Definition F_Lsi (si : POp -> POp -> Prop) : RelaxedSig.t := {| effect := PSig; handle := nat; semi_independent := si; mode := fun _ => Local |}.
   Definition δcoh (m : nat -> nat) (o : LOp) : lar o -> (nat -> nat) -> Prop :=
     match o with oRd l => fun r m' => r = m l /\ m' = m | oWr l v => fun _ m' => m' = (fun l' => if Nat.eqb l l' then v else m l') | _ => fun _ m' => m' = m end.
   Definition δbset (N : nat) (S : list nat) (o : POp) : par o -> list nat -> Prop :=
     match o with OIns k => fun _ S' => S' = (if length S <? N then k :: S else S) | OPrint => fun r S' => r = S /\ S' = S end.
   Definition IL := fun a b => a = OPrint /\ exists k, b = OIns k.
   Section C. Context (sE : LOp -> LOp -> Prop) (N : nat) (M : forall si, RelaxedModuleImpl (E_L sE) (F_Lsi si)).
   Lemma chain_0 σ0 I R G s :
     RelaxedHoareBase.RLHL2Hyps (VE := EIhl (E := E_L sE) δcoh) (VF := RelaxedHoareSpec.EI (F := F_Lsi (fun _ _ => False)) (δbset N)) I R G (M _) (σ0, []) ([], []) ->
     MTraces (RelaxedHoareSpec.EI (F := E_L sE) δcoh) (M (fun _ _ => False)) σ0 s -> PrefixView.complete s ->
     rel_lin (@PrefixView.sel (F_Lsi (fun _ _ => False))) s IL (RelaxedHoareSpec.seq_legal (F := F_Lsi (fun _ _ => False)) (δbset N) []).
   Proof.
     intros HH Hs Hc.
     pose proof (@rlhl_complin_eihl (E_L sE) _ δcoh (F_Lsi (fun _ _ => False)) _ (δbset N) [] I R G (M _) σ0 HH) as HC.
     pose proof (@complin_ei_rel_lin (E_L sE) (F_Lsi (fun _ _ => False)) _ (δbset N) [] (M _) _ σ0 HC s Hs Hc) as X.
     exact (rel_lin_empty_indep _ _ _ _ X).
   Qed.
   End C.
   Print Assumptions chain_0.   (* Eqdep.Eq_rect_eq.eq_rect_eq, Classical_Prop.classic *)
   ```
8. **Existing baselines.** `Print Assumptions rlhl_complin_eihl` gives {`classic`}; `cc_rel_lin` gives {`eq_rect_eq`, `classic`}. `Print RelaxedGSim.gsim_step` confirms its first conjunct is `∃ v pool, p = PossOk v pool`.
9. **A1 definitions.** `TItem`, `module_error_tagged`, `MTracesE` and `EIe` (with `bad : St * list (Op F) -> tid -> Sig.op F -> Prop`) all typecheck. Importing `RelaxedGSim` is needed for `overlay_events`. Coercing `TaggedModuleConfig (EIe δ bad)` to `TaggedModuleConfig (EI δ)` fails, so `mtraces_eie_ei` needs a transport.
10. **Name checks** (grep). Present:
    - `rel_lin_mono`, `rel_lin_empty_indep` (`RelaxedTraceLin.v:97,107`);
    - `mtraces_prefix` (`RelaxedHoareCompLin.v:295`);
    - `RProvable_coind` (`RelaxedHoare.v:511`), `rp_dowhile` (`RelaxedHoare.v:582`);
    - `emit_ready_SI` (`RelaxedHoareInherit.v:378`), `Counter.emit_ready` (`RelaxedHoareChecks.v:842`);
    - `returned_not_fresh` (`RelaxedHoareGSim.v:454`);
    - A's `rinv_*`, `reify_step`, `cinv_init`, `owners_active_reachable`.
    
    Absent: any "pool keys = invoked overlay keys" lemma, hence `pool_keys_trace` in L.10.

**Key files.**
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v (`must_precede` :252, `module_step_tagged` :578)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareBase.v (`ghost_emit` :289, `CallTriple` :508, `MethodSem` :524, `RLHL2Hyps` :793)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoare.v (`rp_futureD` :417, `RProvable_coind` :511)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v (`cc_rel_lin` :916, `HL` :987, `EIhl` :1156, `rlhl_complin_eihl` :1265)
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/LatchSetProg.v (source to port: Parts 1–5 and 7, plus the Part 15 tactics; read-only)
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/overview.tex:333, intro.tex:7/:99/:106, trace.tex:59/:83