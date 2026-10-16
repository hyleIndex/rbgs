The target holds in this semantics. All five broken variants fail with concrete executions, and the verdicts match LKMem. The semantics also gives four things that change the plan:
- The trailing mb is not needed for relaxed linearizability.
- The "non-overlapping inserts" clause of P1 is not needed.
- I_L is never used by this module.
- The `EIe` draft cannot express P1.

## 0. Verdicts

| # | Question | Verdict |
|---|---|---|
| 1 | Is the correct LatchSet (LD-0 (a′), trailing mb, P1, P2) rel_lin to the atomic set? | **Holds** (hand proof, §2). `no_mb` also holds. P1 can be weakened to "only t_w inserts"; overlapping writer calls are harmless. |
| 2 | Do the five broken variants fail? | **All five fail** (§3), each with a concrete complete execution. Setup: zero memory, N=1, the writer runs insert(5), a reader's print returns `[0]`. The scan option makes no difference: full idiom correct and the five broken, for both values of `scan_all_N`. |
| 3 | Are the LPs adequate with one possibility? | **Holds.** LP = emission of the call's last pending `seq` access. For insert that is `wr seq (s+2)`; for print it is the final retry `rd seq`. print's result is fixed by EI before its LP. No prophecy and no helping are needed. |
| 4 | Is I_L / underlay-SI inheritance consistent? | **Holds trivially.** Every LP is a `seq` access, so the same-location rule (F2) puts each thread's LPs in program order. `invocation_ready` never needs SI_F. RLHL2Hyps is not obstructed, and the same proof works with the empty overlay relation. `emit_ready_SI` does not apply (it covers renaming bodies only); a variant of `Counter.emit_ready` is needed. |
| 5 | Does the error infrastructure P1/P2 needs interact badly? | **Three issues.** (i) The drafted `EIe … (pre : St -> op -> Prop)` (RLHL-3c.md:199) cannot express P1, because P1 needs the thread id. (ii) PossError must absorb everything (D5 (vi) becomes necessary). (iii) P1 and P2 can both be handled without m-8 (§6), so LatchSet does not have to wait for 3c.8. |

## 1. Semantic facts used (checked)

- **EI is sequential.** `ei_step` (RelaxedHoareSpec.v:307) applies δ at `InvEv`; `ResEv` only returns the recorded value.
- **Frontier rules** (`must_precede`, RelaxedModuleSemantics.v:252):
  - (F1) Inv before its own Res;
  - (F2) two invocations of one thread keep their order unless the underlay relation (`sindep`) allows the crossing, and this holds across different overlay calls of the same thread;
  - (F3) a Res comes before the invocations tagged with its handle.
  - Res–Res pairs are never constrained, and a Res may move ahead of any untagged Inv.
- **Tags.** `tagged_futureD` tags with `deps ∩ resolved_in H` (RelaxedSemantics.v:397). `run` waits immediately, so every tag is the full `dep_of hs dix`.
- **Table entries** (evaluated in `rocq repl`, Rocq 9.3.0, both values of `rc`):
  - `dto` is false for DR/DR, DR/DW, DW/DR, DW/DW, Wmb↔DR, Rmb↔DW and Wmb↔Rmb;
  - `dto` is true for DW→Wmb, Wmb→DW, DR→Rmb and Rmb→DR, and for DFence with anything, in both directions.
  - Same `gloc` (including GBw/GBr) is always ordered.
  - So: different-location reads and writes commute freely; wmb orders writes only, rmb orders reads only; mb orders everything; same location is always ordered.
- **Run to completion.** `tagged_invoke` appends the whole prophetic method trace to the queue, and `tagged_return` needs `owner_done_tagged`. A thread may have several active overlay calls (`call_fresh` is the only check).
- **No trace, no obligation.** `MethodSem` (RelaxedHoareBase.v:524) and `h_invoke_rely` are vacuous when `program_produces_tagged` has no trace.
- **Error steps need readiness.** `psa_inv_error` requires `lin_invocation_enabled`, and `VF.Error` sees the whole `ThreadEvent`, tid included.
- **Porting.** RelaxedLang/RelaxedSemantics/RelaxedModuleSemantics/RelaxedSignature/RelaxedLTS/WindowTable.v are byte-identical in the two checkouts. Sibling `LatchSetProg.v` Parts 1–16 need only `FuturesShape.v` (602 lines, core imports only). Part 17 needs `memory.TableBarrier`/`Drain`, which this branch lacks; drop it.

Program names below follow sibling `LatchSetProg.v`.
- insert(5) from empty, N ≥ 1, writer thread w, 13 calls:
  - w1 `rd seq`→0, w2 `rd n_0`→0;
  - w3 wmb0 {#w2}, w4 `wr seq 1` {#w1,#w2}, w5 wmb1;
  - w6 `wr a_0_0 5`, w7 `wr n_0 1`;
  - w8 wmb2, w9 `wr seq 2`, w10 wmb3;
  - w11 `wr a_1_0 5`, w12 `wr n_1 1`, w13 mb.
- print, one iteration, m=1, reader thread r:
  - r1 `rd seq`;
  - r2 `rd n_c` {#r1}, r3 `rd a_c_0` {#r1};
  - r4 rmb {#r1,#r2};
  - r5 `rd seq` {}.

## 2. Q1: the correct LatchSet holds (hand proof)

**Writer discipline.** Under P1 only t_w writes; insert j+1 reads s=2j.
- The copy-0 writes come strictly after `wr seq 2j+1` (wmb1: Wmb→W) and strictly before `wr seq 2j+2` (wmb2).
- The copy-1 writes come strictly after `wr seq 2j+2` (wmb3). They come strictly before the next `wr seq 2j+3`, because of the next insert's wmb0 (W→Wmb, then Wmb→W) and, with mb, already because of this insert's mb.
- The writer's copy-0 reads come before its own wmb0 (tag K2, then F1) and so before `wr seq 2j+1`.
- They come after the previous insert's writes: same location, and the previous mb orders everything.
- `seq` only increases.

**Invariant J.** If seq = 2j then copy 0 = A_j; if seq = 2j+1 then copy 1 = A_j. The copy numbered seq&1 is never written while seq keeps its value.

**Reader iteration.**
- T1 = r1 (value s).
- The data reads come after T1 by F3 (address dependency) and before rmb (R→Rmb).
- rmb comes before T3 = retry read (Rmb→R).
- If seq(T3) = s, seq was constant on [T1, T3], so copy (s&1) = A_{⌊s/2⌋} throughout, and the returned list equals the abstract state at T3.

**LPs.** insert at its `wr seq 2j+2`; print at T3 of its final iteration. Both are inside the call's interval.

Cases checked:
- **Writer print younger than its own insert.**
  - With mb, every invocation of the print is emitted after the insert's mb.
  - Without mb, the print's `rd seq` still follows `wr seq s+2` (same location) and reads copy 0, which is complete by wmb2.
  - So the print sees k, as I_L requires (insert→print is ordered).
- **Writer print older than its own insert.** The insert's `wr seq s+1` cannot overtake the print's `rd seq`s (same location). Its copy writes follow wmb1, so the print never sees them. The insert's reads and wmb0 may overtake the print; that is harmless.
- **Two readers, or one reader with overlapping prints.**
  - print2's first `rd seq` follows print1's last `rd seq` (same location), and its data reads follow print1's rmb (Rmb→R).
  - So the LP order is the program order, and print2 sees a set that contains print1's.
- **Retries.** Iteration i's data reads come before rmb_i, which comes before iteration i+1's reads. Failed iterations are irrelevant.
- **Capacity.** The writer never writes `n > N` (`latch_new`), so `min(m,N) = m`. If k is absent and m = N, the insert is a no-op; that is P2's case. N = 0 is fine.
- **Writer reads after its own pending writes.** Same location forces them after the earlier insert's writes. In particular insert2's `rd seq` cannot see s+1, because `wr seq s+2` is ahead of it in the queue.
- **Overlapping writer inserts** (asynchronous calls).
  - With mb, all of insert2's invocations follow insert1's mb, so the inserts are serialized at the level of effects.
  - Without mb they are still correct: same location plus wmb0.

**Trailing mb.** Not needed for relaxed linearizability in this semantics; `no_mb` is correct. Its two roles here:
- It serializes the writer's later calls behind the insert, which simplifies the proof and makes the non-overlap clause of P1 unnecessary at no proof cost.
- It gives the DRFence export used in window composition.

wmb0 matters only when there is no mb *and* writer inserts overlap. In that case insert2's `wr seq 2j+3` can overtake insert1's copy-1 writes, which come after wmb3, and the variant is broken.

**I_L and the writer's later calls.** I_L orders insert before everything of the same thread, and the module does that through the same-location rule plus mb. The (print, insert) relaxation is never exhibited: the writer's younger insert writes `seq` only after its older print's last `rd seq`.

## 3. Q2: the five broken variants all fail (concrete executions)

Setup:
- Initial memory is all zeros; N = 1, which satisfies P2; only w inserts (P1); r is a different thread.
- Overlay events: Inv(w, insert 5), Inv(r, print), the underlay events, then Res(r, print, `[0]`) and Res(w, insert, tt). All underlay Res events are emitted right after their Inv.
- The trace is complete.
- It is not rel_lin for *any* `indep`: δ_set from ∅ with only `OIns 5` has states [] and [5], so print can never return `[0]`. No happens-before reasoning is needed.
- Global emission order of the invocations; "x crosses y" is justified by the table above.

| Variant | Execution (emission order) | Why legal |
|---|---|---|
| `no_wmb1` (no w5) | w1 w2 w3 · r1(0) r3(a_0_0→0) · w6 w7 · r2(n_0→1) r4 r5(0) · w4 w8 … w13 | w6 and w7 cross the unemitted w4 (W/W at different locations; wmb0 already emitted); r3 crosses r2 (R/R, both tagged #r1 only) |
| `no_wmb2` (no w8) | w1 … w5 w9 · r1(2) r3(→0) · w6 w7 · r2(→1) r4 r5(2) · w10 … w13 | w9 crosses w6 and w7 (W/W; w5 and w4 already emitted) |
| `no_wmb3` (no w10) | w1 … w8 · r1(1, so copy 1) r3(a_1_0→0) · w11 w12 · r2(n_1→1) r4 r5(1) · w9 w13 | w11 and w12 cross w9 (W/W; wmb2 already emitted) |
| `no_addr` (data reads tagged {}) | w1 … w5 · r3(a_0_0→0) · w6 w7 · r2(→1) · w8 w9 · r1(2) r4 r5(2) · w10 … w13 | The prophesied s = 2 selects copy 0; untagged r2 and r3 cross r1 (R/R); r4's tag {#r1,#r2} is satisfied |
| `no_rmb` (no r4) | r1(0) r5(0) · w1 … w7 with r3(→0) before w6 · r2(→1) · w8 … w13 | The retry read r5 (tag {}) crosses r2 and r3 (R/R) |

All five return `[0]`. These match the LKMem verdicts, but the agreement is about the shapes; this memory is not LKMem.

A version closer to the paper's bad outcome ("misses a key present before and after") starts from the memory for {1} and runs insert(0). Its writes are `a_c_1:=1; a_c_0:=0; n_c:=2`. The torn read takes n=1 (old) and a_0=0 (new), giving `[0]`.

**Scan option.** With N=1, `cnt m` = 1 either way, so the executions are identical. With N ≥ 2 and `scan_all_N`, the extra reads are discarded. The full idiom is correct for both values: all data reads lie in (T1, T3).

## 4. Q3: the LPs work with one possibility

Uniform rule: **a call linearizes when it emits its last pending `seq` access.** The update reads this off `γ`/`γ'`; LLoc and handles have decidable equality.
- insert: the last `seq` access is `wr seq s+2`. Abstract step `δbset A (OIns k) = latch_new N k A`. Copy 0 already equals `latch_new` (ordered by wmb2, with the K2 reads giving A).
- print: the last `seq` access is the final retry `rd seq` (r′), with result A (current).
  - The data-read invocations come before rmb, which comes before the retry read, so their EI values r_i are fixed.
  - Edge assertion from each data-read Inv slot: `seq > s ∨ copy_c[i] = r_i` (stable: the writer never writes copy c while seq = s), plus ownership of the EIhl record (`eihl_mine`).
  - At the LP: if r′ = s, then A = `pval m [r_i]`. If r′ ≠ s, the path is dead: the next `rd seq` has no ghost entry, so `ghost_emit` is impossible and the update is vacuous.
  - At `Ret`, `eihl_mine_res` gives v_i = r_i.
  - The data-read **Res** slots are not DAG predecessors of the retry Inv (they are untagged), so the value must flow through the records, not through program variables. This is a design point for the writer of the proof.
- No prophecy is needed: the decision uses only the ghost and the current EI value.

## 5. Q4: readiness is consistent; I_L is not used

- **Coupling invariant:** `ls_inv k ⇒ k owns a pending seq-access ghost entry`, and the order of distinct owners in the ghost agrees with the pool order.
- It holds at invocation: every trace contains `seq` accesses (an Ω footprint, or from `ghost_new`). It is preserved because the last-seq-entry LP removes `ls_inv` exactly when the last such entry goes.
- When a younger call emits its LP, any older `ls_inv` call of the same thread has a pending `seq` entry earlier in the ghost. That entry `inv_blocks` the LP (`sindep_same_loc`), which contradicts `ghost_emit`.
- So the emitting call is the oldest `ls_inv` call of its thread, and `older_entry_allows_invocation` never consults SI_F.
- No module-allowed reordering forces a pair outside I_L. The proof goes through unchanged for `F` with the empty relation, which is strictly stronger (`rel_lin_mono` then gives the I_L form).

## 6. Q5: errors

- **D5 (ii) as drafted is thread-blind.** `Error := … ~ pre (fst s) o` cannot say "insert by t ≠ t_w". Amend it to `pre : St -> tid -> Sig.op _ -> Prop`, with `Error ev s := match te_ev ev with InvEv _ o => ~ pre (fst s) (te_tid ev) o | _ => False end`.
  - Non-overlap would also need the pending list `snd s`, and an early LP of the older insert at the time of the overlap. Avoid it by dropping non-overlap from P1 (§2).
- **A reader thread calling insert** (Stage B).
  - Its first `seq` access (`rd seq` or `wr seq`) is emitted after every older same-thread `seq` entry, so it is ready. Linearize it there; it reaches PossError.
  - Its earlier events are reads and wmb0 and change no memory.
  - After its `wr seq` the invariant breaks, so `GSimRelErr` must let PossError absorb everything: D5 (vi) is required, not optional.
  - LatchSet needs neither `cte_noerr` nor D5 (iii): `EIhl δcoh` has no errors.
- **P2 without errors.** Use the bounded-set spec `δbset N`, which is exactly the implementation's `latch_new`. On traces with at most N distinct keys, `seq_legal (δbset N)` coincides with the unbounded set.
- **P1 without errors (Stage A).** Use `M_Lw`, in which a non-writer insert's body is `div` (`CoFixpoint div := Tau div`).
  - `div` produces no trace, so `MethodSem` and `h_invoke_rely` are vacuous for it, and `ILatch` may assume every pool insert is by t_w.
  - A transfer lemma moves `MTraces` of `M_L` that satisfy P1 into `MTraces` of `M_Lw`.
  - This gives an honest conditional theorem without 3c.8. Stage B re-proves it over the amended `EIe`, reusing everything.

## 7. Intended statements (new names; types as in the sibling)

```coq
(* LS-R1 *)
Definition Mem := LLoc -> nat.
Definition δcoh (m : Mem) (o : LOp) : lar o -> Mem -> Prop :=
  match o with oRd l => fun r m' => r = m l /\ m' = m
  | oWr l v => fun _ m' => m' = upd m l v | _ => fun _ m' => m' = m end.
Definition σcoh0 : State (RelaxedHoareSpec.EI δcoh) := (fun _ => 0, []).
Definition δbset (N : nat) (S : list nat) (o : POp) : par o -> list nat -> Prop :=
  match o with OIns k => fun _ S' => S' = latch_new N k S | OPrint => fun r S' => r = S /\ S' = S end.
Definition P1 tw (s : list (ThreadEvent (F_L rc))) := forall i t h k,
  nth_error s i = Some (Build_ThreadEvent t (InvEv h (OIns k))) -> t = tw.
Definition P2 N s := exists K, NoDup K /\ length K <= N /\ forall i t h k,
  nth_error s i = Some (Build_ThreadEvent t (InvEv h (OIns k))) -> In k K.
Definition M_Lw N fl rc tw : RelaxedModuleImpl (E_L rc) (F_L rc) := fun op t =>
  match op with OIns k => if Pos.eqb t tw then M_L N fl rc op t else div | OPrint => M_L N fl rc op t end.
Lemma div_no_produce t tr r : ~ program_produces_tagged t div tr r.
Lemma mtraces_refuse VE σ0 s : MTraces VE (M_L N fl rc) σ0 s -> P1 tw s -> MTraces VE (M_Lw N fl rc tw) σ0 s.
Lemma bset_set_P2 N s W : P2 N s -> (* ops of W from s *) … -> seq_legal (δbset N) [] W -> seq_legal δset [] W.

(* LS-R2 *)
Theorem latch_broken_no_rlhl2 scan rc tw fl :
  In fl [no_addr scan; no_rmb scan; no_wmb1 scan; no_wmb2 scan; no_wmb3 scan] ->
  forall I R G, ~ RLHL2Hyps (VE := EIhl δcoh) (VF := RelaxedHoareSpec.EI (δbset 1))
                  I R G (M_Lw 1 fl rc tw) (σcoh0, []) ([], []).
(* via torn_exec_fl : module_execution_tagged … ; torn_complete; torn_P1; torn_P2;
   torn_not_rel_lin : forall indep, ~ rel_lin sel torn_trace indep (seq_legal (δbset 1) []);
   proof as cxy0_no_rlhl2: rlhl_complin_eihl, then cc_rel_lin *)

(* LS-R6 *)
Theorem latch_rlhl2 N scan rc tw :
  RLHL2Hyps (VE := EIhl δcoh) (VF := RelaxedHoareSpec.EI (δbset N))
    ILatch RLatch GLatch (M_Lw N (full_idiom scan) rc tw) (σcoh0, []) ([], []).
Corollary latch_rel_lin N scan rc tw s :
  MTraces (RelaxedHoareSpec.EI δcoh) (M_L N (full_idiom scan) rc) σcoh0 s ->
  PrefixView.complete s -> P1 tw s ->
  rel_lin (@PrefixView.sel (F_L rc)) s (semi_independent (F_L rc)) (seq_legal (δbset N) []).
(* plus: _set under P2 (unbounded δset); _0 with the empty relation; latch_si_table packaging both *)
```

## 8. Proof strategy, reuse and risks

**Invariant `ILatch`.**
- J (§2) over `fst (fst σ)`, with A the `PossOk` state.
- `|A| ≤ N`, and A sorted with no duplicates.
- "seq even and copy1 ≠ A ⇒ some t_w insert owns a pending mb entry and is in its copy-1 phase."
- `eihl_rec_used`; the §5 coupling; "every pool insert is by tw".

**Rely/guarantee.** Frame style, as in `CounterEIhlFrame` / `ren_rlhl2`.
- Memory part: `eihl_steps`, with the writer's guarantee "copy c is written only while seq&1 ≠ c; seq only increases".
- Records are tracked by `eihl_mine*`.

**Readiness.** A new `latch_emit_ready`, modelled on `RelaxedHoareChecks.Counter.emit_ready` (RelaxedHoareChecks.v:842), with "older same-thread *seq* entries block" replacing "every same-thread entry blocks".

**Own-event interference.**
- Same-location pairs are always DAG-ordered.
- Every `ns_if_*` pair is at different locations or is a read: one generic location-frame lemma.
- The LP is DAG-after all of the insert's earlier events through the wmb chain; print's LP is after rmb.

**Route decision.**
- (L) RProvable over `run` via `RProvable_coind`, with an invariant on machine states (`WSt`/`RSt`, `hs`, `Γ`, `H`). This is faithful to the logic.
- (S) `MethodSem` directly, via `ML_shape` (ported `FuturesShape`) and a coinductive `CallSafe` over the decoded block, with an invariant on the downward-closed set of emitted events. Probably cheaper, but it is not a logic derivation.
- I recommend (L) for print first; fall back to (S) for insert if `run`'s coinduction becomes unwieldy.

**Risks.**
1. `ns_if` premises growing quadratically for insert (13 + 3m calls). Mitigation: the generic frame lemma.
2. Stating the ghost-phase clause of J and proving it stable.
3. Inversion of `run` traces when building the negative executions (use `run_unfold` and the sibling's `ML_insert_produces` pattern), plus about 50 `select_frontier_tagged` proofs; write a crossing tactic.

## 9. Writer sub-tasks

Acceptance for every task:
- Rocq 9.3.0 via `/opt/homebrew/bin`;
- `_CoqProject` updated;
- no `Admitted`/`Axiom`/`vm_compute`/`native_compute`;
- K/S/P/R header;
- `Print Assumptions` within {classic, eq_rect_eq} only where the result goes through `rlhl_complin_eihl`/`cc_rel_lin`.

| ID | Files | Content | Accept when | Size |
|---|---|---|---|---|
| LS-R0 | `examples/Relaxed/FuturesShape.v`, `examples/Relaxed/LatchSetProg.v` | Port sibling Parts 1–16; drop Part 17 and the `memory.*` imports | Builds; the diff against the sibling is only Part 17 and the imports | ~0.5 iter |
| LS-R1 | `examples/Relaxed/RelaxedHoareLatchSpec.v` | `δcoh`, `δbset`, P1/P2, `div_no_produce`, `M_Lw`, `mtraces_refuse`, `bset_set_P2` | Closed | 400–600 lines, 1 iter |
| LS-R2 (first; decisive) | `examples/Relaxed/RelaxedHoareLatchBroken.v` | The five executions of §3 (one file, shared tactic), `torn_not_rel_lin`, `latch_broken_no_rlhl2`; optional {1}+insert(0) variant | All five; P1/P2 proved for the trace | 1200–1800 lines, 2 iters |
| LS-R3 | `examples/Relaxed/RelaxedHoareLatchInv.v` | `ILatch`, `RLatch`, `GLatch`, J, the coupling, `latch_emit_ready`, location-frame lemma, stability lemmas, the fields of RLHL2Hyps other than `h_sem` | Closed | 800–1200 lines, 2 iters |
| LS-R4 | `examples/Relaxed/RelaxedHoareLatchRead.v` | Print `MethodSem` (route L), generic in `scan_all_N`; LP at the last `seq` entry | Closed | 1000–1500 lines, 2–3 iters |
| LS-R5 | `examples/Relaxed/RelaxedHoareLatchWrite.v` | Insert `MethodSem`; `latch_new` coupling through `cwr_effect` | Closed | 1500–2000 lines, 2–3 iters |
| LS-R6 | `examples/Relaxed/RelaxedHoareLatchSet.v` | `latch_rlhl2`, `latch_complin_ei`, `latch_rel_lin`, the `_set` and `_0` corollaries, a table theorem pairing them with LS-R2 | Within {classic, eq_rect_eq} | 300–500 lines, 1 iter |
| LS-R7 (optional) | same | `no_mb` positive | — | +600 lines |
| LS-B (after 3c.8) | same | Re-proof over `EIe` with a tid-aware `pre`; bad insert's PossError at its first `seq` entry | — | 500–800 lines |

The critical path is R0 → R1 → R2 → R3 → (R4 ∥ R5) → R6: about 5,000–7,500 lines and 9–13 iterations.

## 10. Research-level points for the author

1. **I_L is never used here.** LatchSet is rel_lin even with the empty relation, because all LPs are on `seq`. "Admits load buffering" cannot be witnessed by one LatchSet under P1 (that needs two inserting threads); it is a contract that matters only across components (the tensor). Should the stronger empty-relation corollary be stated?
2. **The trailing smp_mb is not needed for relaxed linearizability** in this semantics; it serializes the writer's calls and gives the DRFence export. The plan and paper should not attribute it to single-object correctness.
3. **P1 can be "only t_w inserts".** Non-overlap is unnecessary, and the D5 (ii) `pre` needs a tid argument. D5 (vi) (PossError absorbs everything) becomes necessary.
4. **Bounded-set spec.** Is `δbset` (insert into a full set is ignored) acceptable as the RLHL spec, with the unbounded set recovered under P2?
5. **Staging.** Is Stage A (refusal module, theorem conditional on P1) an acceptable first deliverable before the error-obligation version required by decision (a)?
6. **Scope of the claim.** This is an SC register file with location-based SI plus barrier reordering. The five refutations agree with LKMem on the litmus shapes only; this is not a weak-memory result (same caveat as D4 for Counter_xy). The insert's LP here is the *invocation* of `wr seq s+2`, not the sibling's "hidden flush" (LS-HLP).

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/LatchSetProg.v (sibling; port Parts 1–16)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareBase.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareCounterXY.v (pattern for negative executions and instances)