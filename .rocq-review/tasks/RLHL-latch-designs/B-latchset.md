# LatchSet over COH registers plus barriers: RLHL design (part B)

## 0. Key findings

1. **Sources checked.** The repl checks below were run read-only: piped `rocq repl` with the `_CoqProject` `-R` flags, Rocq 9.3.0.
   - These files are byte-identical on the two branches: `RelaxedSemantics.v`, `RelaxedModuleSemantics.v`, `examples/Relaxed/WindowTable.v`.
   - The sibling's `LatchSetProg.v` Parts 1–5 and 7 (the program, its tags, `cwr`/`cwr_effect`, the `run` interpreter) can be ported verbatim.
   - Part 17 cannot be ported, because `memory/TableBarrier.v` and `memory/Drain.v` do not exist on this branch. The SCM runs (Part 16) are not needed.
   - These sketches typecheck in a scratch repl:
     - `RLHL2Hyps (VE := EIhl δcoh) (VF := EI (δset …))` over a parametric `F_L si`;
     - the corollary chain `rlhl_complin_eihl` and `complin_ei_rel_lin`.
2. **The overlay relation I_L is never used.** Both LPs are ordered on one thread by the module's own (F2) edges:
   - print → insert: the insert's LP `Wr(Lseq,·)` cannot cross a pending `Rd(Lseq)`, because they are at the same location;
   - insert → print: the trailing `oMb` is not semi-independent of anything.
   
   So readiness comes from blocking ghost entries, not from inheritance. The same proof holds for every overlay relation `si`, including ∅. Over COH, LatchSet shows no overlay relaxation. The load-buffering-shaped behaviour that I_L admits is not produced (§4).
3. **P1 can be weakened.** "Inserts pairwise non-overlapping" is not needed. Same-thread inserts are serialized by `oMb` under (F2). Only "inserts only on `t_w`" is needed.
4. **Both LPs are past-determined.** The insert LP is at its second `Wr(Lseq)` invocation. The print LP is at the call's last `Rd(Lseq)` invocation, identified through the call's own pending ghost entries. Its abstract effect depends only on the current state.
5. **`cprov_dowhile` does not apply to the faithful text.** A new iteration starts with `FutureD (oRd Lseq) {}`, not an untagged `Future`, so there is no `Barrier` slot. Loops go through a generic state-machine rule `rp_run` (built by coinduction like `rp_dowhile`) over the sibling's `run`.
6. **Recommended staging.**
   - Stage 1 needs no error infrastructure:
     - P1 by a thread guard in the module;
     - P2 by the saturating spec `latch_new`, which is exactly what `cwr` implements;
     - corollaries with P1/P2 as trace hypotheses for the unguarded module.
   - Stage 2 adds `EIe` errors once part A lands. The module-side error obligation (D5 (i)) is vacuous here, because `EIhl δcoh` has `Error := False`.
7. **Size.** About 5,000–7,500 lines for stage 1 (10–13 Writer iterations), and 400–800 more for stage 2.

## 1. Objects

New file `examples/Relaxed/RelaxedHoareLatchProg.v`, ported from `/Users/index/Documents/GitHub/rbgs/examples/Relaxed/LatchSetProg.v` Parts 1–5 and 7. Its header must cite the source lines and list the differences.

**Underlay.** Ported verbatim:
- the types `LLoc`, `LOp` (`oRd l | oWr l v | oWmb | oRmb | oMb`), `lar`, `LSig`;
- `gloc`, `ccat`, `lpres`, `sindep rc`;
- `E_L rc := {| effect := LSig; handle := nat; semi_independent := sindep rc; mode := fun _ => Local |}`;
- the lemmas `sindep_iff`, `mb_ordered`, `sindep_same_loc`, `E_L_well_formed`, `E_L_table`.

The proof uses only facts that hold for both profiles `rc`:
- same location ⇒ ¬SI;
- `oMb` ⇒ ¬SI in both directions;
- (Rd, Rmb), (Rmb, Rd), (Wr, Wmb), (Wmb, Wr), (Wmb, Wmb) are ¬SI.

The executions in §4 also need (Rd l, Rd l′) and (Wr l, Wr l′) to be SI.

**Sequential COH spec.** New definitions:
```coq
Definition Regs := LLoc -> nat.   Definition regs0 : Regs := fun _ => 0.
Definition upd (m : Regs) l v : Regs := fun l' => if LLoc_eq_dec l l' then v else m l'.
Definition δcoh (m : Regs) (o : LOp) : lar o -> Regs -> Prop :=
  match o with oRd l => fun r m' => r = m l /\ m' = m
             | oWr l v => fun _ m' => m' = upd m l v
             | _ => fun _ m' => m' = m end.                  (* barriers: no-ops *)
Definition VE := RelaxedHoareCompLinSpec.EIhl (E := E_L rc) δcoh.
Definition opval (x : RelaxedTraceLin.Op (E_L rc)) : nat.   (* nat result of a read, 0 otherwise *)
```
`opval` gives injectivity of records without `eq_rect_eq`, in the same way as `cxy_inj`.

**Overlay.**
- Port `POp`, `par` and `PSig` verbatim.
- Generalize the overlay relation: `F_Lsi (si : POp -> POp -> Prop)`, so that `F_L rc := F_Lsi (findep rc)`.
- Port `F_L_indep_iff` and `F_L_well_formed`.
- Specs:
```coq
Definition δset (N : nat) (S : list nat) (o : POp) : par o -> list nat -> Prop :=
  match o with OIns k => fun _ S' => S' = latch_new N k S
             | OPrint => fun r S' => r = S /\ S' = S end.        (* stage 1: saturating *)
Definition δsetU S o : par o -> list nat -> Prop  (* ins_sorted, unbounded: ν_Set *).
Definition preL (tw : tid) (N : nat) (t : tid) (S : list nat) (o : POp) : Prop :=
  match o with OIns k => t = tw /\ length (ins_sorted k S) <= N | OPrint => True end.  (* stage 2 *)
```

**Program.** Port verbatim:
- `Flags`, `full_idiom`, the five variants and `no_mb`;
- Part 4 (`ins_sorted`, `latch_new`, `ipos`, `wpos`, `cwr`, `cwr_size`, `slots_after`, `cwr_effect`, `latch_new_wpos`);
- `wplan`, `wnext`, `cnt`, `adep`, `krmb`, `ridx`, `pval`, `retry_step`, `rnext`.

`SStep`, `dep_of`, `run` and `run_unfold` move to a generic model file (see L1), with `op : Sig.op G`. Then:
```coq
Definition M_L N fl rc si : RelaxedModuleImpl (E_L rc) (F_Lsi si).   (* verbatim body *)
CoFixpoint spin {G R} : Prog G R := Tau spin.
Definition M_Lg N fl rc si (tw : tid) : RelaxedModuleImpl (E_L rc) (F_Lsi si) :=
  fun op t => match op with OIns k => if Pos.eqb t tw then M_L N fl rc si op t else spin
                          | OPrint => M_L N fl rc si op t end.          (* stage-1 guard for P1 *)
```
- **Capacity.** `N` stays parametric. The derivation already quantifies over every response; `N` enters only through `Nat.min`, `latch_new` and `I3`.
- **Scan option.** Prove the theorem for `full_idiom scan` for both values of `scan`.
- **Entry rmb.** The rrec entry `rmb` is not in the sibling file yet, and over COH it is not needed. Note this in the header.

## 2. The RLHL proof

### 2.1 Route

Use the syntactic route: `MethodProvable` and then `RelaxedHoareSound.method_sound`, with `rp_futureD` and `rp_wait_pending` driven through `rp_run` (L1).

Fallback, if the slot bookkeeping explodes at checkpoint L3: prove `MethodSem` directly. The prophetic certificate would be `A l := Φ(tr,l)` and would reuse the sibling's `ML_shape`; that needs porting `FuturesShape.v` (602 lines) and Parts 6, 8–11 and 14.

### 2.2 Linearization points

- **insert (on `t_w`).** At the invocation of its second `Wr(Lseq,·)` — the paper's "seq := s+2" — identified as the call's last pending `Wr(Lseq)` in γ′.
  - Abstract steps: `psa_inv` with `δset: S ↦ latch_new N k S`, then `psa_ret` immediately, so the entry becomes `ls_linr tt`.
- **print.** At the invocation of the call's last `Rd(Lseq)`, identified as "no pending `Rd(Lseq)` entry of k in γ′".
  - The LP is taken unconditionally: `psa_inv` with r = S_now.
  - `psa_ret` happens at return, inside `RetCond`.
  - If the value read is not the iteration's s, the call can never return (its `Res` does not match its record, `eihl_mine_res`). The LP is still taken, so that the readiness coupling I7 below keeps holding.
- **Why this is not future-dependent.**
  - The effect uses only the current S.
  - "Last" is read from the call's own committed trace (the ghost; prophecy as in m-11/m-33), never from other calls' futures.
  - Linearizing at the successful iteration's first `Rd seq` would be future-dependent, and is rejected.
- **Why the result is right.** At the LP, `reg Lseq = s` holds. Each data-read fact "seq = s ⇒ w_i = reg(La c i)" together with I4 gives w_i = `nth i S`, and the size read gives m = |S|. With |S| ≤ N, `pval m vs = S`.

### 2.3 Invariant `IL N tw : Assn VE VF`

```
∃ S Pabs pool, ps_poss s = PossOk (S,Pabs) pool ∧
 I1  lin_pool_well_formed pool; ∀ o∈Pabs, lin_lookup (op_key o) (ls_lini (op_op o)) pool; NoDup keys Pabs  (as Iren)
 I2  eihl_rec_used σ (+ record keys NoDup, derived)
 I3  Sorted lt S ∧ length S ≤ N
 I4  let q := reg Lseq: reg (Ln (odd q)) = length S ∧ ∀ i < length S, reg (La (odd q) i) = nth i S 0
 I5  (∀ k, ¬ midflight k γ) → even q ∧ both copies represent S
 I6  ∀ k1 k2 on tw, k1 older than k2 in γ, midflight k2 γ → ¬ pendingMb k1 γ
 I7  ∀ k ls_inv in pool: (op=OIns ⇒ pendingMb k γ) ∧ (op=OPrint ⇒ ∃ pending Rd(Lseq) of k in γ)
 I8  GAge pool γ   (ghost entries grouped by owner, owners in pool age order); Forall gwf γ
 I9  every OIns entry of pool has tid tw     (guard; stage 2: or ps_poss = PossError)
midflight k γ := pendingMb k γ ∧ (#pending Wr(Lseq,·) of k) ≤ 1
Excl k γ      := pendingMb k γ ∧ no tw-entry older than k's entries is an oMb
```
"Midflight" is not defined by parity: if the prophesied s is wrong, the call is stuck and parity tells nothing. Instead it is counted, using the footprint "exactly two `Wr(Lseq)` and one `oMb`".

### 2.4 Guarantee and rely (frame style, as `Gren`/`Rren`)

```
LG k s s' := I s ∧ I s' ∧ FrameOthers k s s' ∧ (∃ev, te_tid ev = fst k ∧ ghost_emit k ev γ γ' ∧ Step VE ev σ σ') ∧
  q ≤ q' ∧ (q' ≠ q → q' = S q ∧ Excl k γ) ∧
  (∀ l ≠ Lseq, reg' l ≠ reg l → Excl k γ ∧ q' = q ∧ copy_of l ≠ odd q) ∧ (absS' ≠ absS → Excl k γ)
LR k s s' := (∃ k' ≠ k, LG k' s s') ∨ InvRel k' s s' ∨ RetRel k' s s'
```
`InvRel` and `RetRel` are exactly the shapes of `h_invoke_rely` and `h_return_rely`, so `h_guar_rely`, `h_invoke_rely` and `h_return_rely` hold by definition.

Key lemmas:
- `excl_unique`: `Excl k γ → Excl k' γ → k = k'`, from GAge and both having a pending `oMb`.
- `excl_stable`: older entries only disappear, and new entries are appended as younger.
- `seq_mono_R`: q never decreases under R.
- `stable_copy_R`: if q is unchanged, copy `(odd q)` is unchanged.
- `regs_frozen_R`: if `Excl k`, then R changes neither the registers nor S.

### 2.5 Readiness (new generic lemma, L1)

```coq
Lemma emit_ready_block (P : LinPool F) (γ g1 g2 : Ghost E F) t h o ev :
  lin_pool_well_formed P -> lin_lookup (t,h) (ls_inv o) P -> GAge P γ ->
  (forall k1 o1, fst k1 = t -> k1 <> (t,h) -> lin_lookup k1 (ls_inv o1) P ->
     exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) ->
  γ = g1 ++ Build_ScheduledEvent (t,h) ev :: g2 -> Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
  exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
```
- The blocking premise is supplied by I7. A pending `Rd(Lseq)` blocks both LP events (same location); a pending `oMb` blocks everything.
- `si` is never used.
- `emit_ready_SI` does not apply, because LatchSet is not a renaming and a print has several `Rd(Lseq)` entries.

### 2.6 Writer derivation (`OIns k`, t = tw)

Phase facts travel only along the (F2) barrier chain:
- `Wr seq(s+1) → wmb1 → copy-0 writes → wmb2 → LP → wmb3 → copy-1 writes → oMb`.

(F3) edges carry only phase-invariant value facts. These come from the K2 tags in `wplan` (`0 :: K2` for the seq writes); `rp_futureD`'s tag is `dep_of hs dix ∩ resolved_in H`, which equals `dep_of hs dix` because `run` waits for every call. The facts are:
- n0 = |S0|;
- olds = S0;
- s is the value read.

**Every read** re-establishes `Excl k` from `ghost_emit`, since an older pending `oMb` would block it. Then I5 and I6 give "q even ∧ both copies = S0", which `regs_frozen_R` keeps stable.

| Step | What it must show |
|---|---|
| `Wr seq(s+1)` | Its pre comes from the edge `Inv(Rd seq) →` (same location) and `Res(Rd seq) →` (F3 `#s`). It must re-establish I4 at odd q: copy 1 = S0. |
| copy-0 writes | Facts `reg(La false j) = v_j`. Each is stable under the other copy-0 writes. |
| edge `wmb1 → wmb2` | Carries the unwritten slots = S0. |
| LP | `cwr_effect` and `cwr_size` give copy 0 = `latch_new N k S0`. Then `psa_inv`/`psa_ret`, with readiness by `emit_ready_block`. |
| copy-1 writes | Same pattern as copy 0. |
| `oMb` | Re-establishes I5. |

**Footprint `Ω_ins`:** every own invocation is on t; exactly two `Wr(Lseq)`; exactly one `oMb`. This feeds `mp_PI` for I5, I6 and I7.

### 2.7 Reader derivation (`OPrint`)

The `rp_run` invariant tracks:
- the position o of the current iteration's `Rd seq`;
- `kap`;
- the slot shapes.

Per iteration:
- **`Rd seq₁` invocation.** Records w₁. From then on, `reg Lseq ≥ w₁` holds by `seq_mono_R`.
- **`Res(seq₁)`.** Gives w₁ = s, by `eihl_mine_res` and `opval`.
- **Data reads.** The F3 address tag `adep o = [o]` gives the in-edge from `Res(seq₁)`, hence `reg Lseq ≥ s` at the moment of the read. The post is `Mine κ_i w_i ∧ (reg Lseq = s → w_i = reg (La (odd s) i))`. This is stable by `seq_mono_R` and `stable_copy_R`. **This is where the FutureD tag is load-bearing:** without the address dependency the implication is not stable.
- **`oRmb`.** In-edges from all data-read invocations (F2), carrying the disjunction `(Mine κ_i w_i ∧ …) ∨ (Done(Res κ_i) ∧ v_i …)`.
- **`Rd seq₂` invocation.** In-edges from `oRmb` and `Rd seq₁`. If γ′ has no pending `Rd(Lseq)` of k, take the LP.
- **Close / `BarrierWith`.**
  - `fin(Res seq₂)` carries the LP record together with the data disjunction.
  - `bw_sum` with `NoOwn` refutes the alternative "k still has a pending `Rd(Lseq)`".
  - `mp_ret` then does `psa_ret ret`.

**Footprint `Ω_prt`:** at least one `Rd(Lseq)` invocation.

### 2.8 Own-interference premises (all discharged by stability)

Genuine `ns_if` premises:
- Reader:
  - `ns_if_new_in` at `oRmb`/`Rd seq₂`, against own data reads and their `Res`: `eihl_mine_step`, and `eihl_mine_res` moving the disjunct;
  - `bw_if` for `fin(Res seq₂)` against late `Res(a_i)`;
  - responses of earlier iterations firing late.
- Writer:
  - `ns_if_new_in` at `wmb2`/`oMb`, from each write against the other writes in the same block (distinct locations: an `upd` frame lemma);
  - `ns_if_old_in` for the edge `wmb1 → W_p` against `W_q`;
  - the initial reads, which are mutually unordered.

All other premises are trivial frame facts:
- `Done(Inv κ) := In κ used` and `Done(Res κ) := In κ used ∧ no record with key κ`. Both are monotone under every `EIhl` step, by handle linearity.
- Records are kept by `eihl_mine_steps`.
- `Excl` is stable.

`newslot_guar_in_rely` is not usable, because phase facts are not stable under the call's own barrier-ordered writes.

## 3. Corollaries (file L5)

```coq
Theorem latch_rlhl2 N rc scan si tw :
  RLHL2Hyps (IL N tw) (LR N tw) (LG N tw) (M_Lg N (full_idiom scan) rc si tw) ((regs0, []), []) ([], []).
Corollary latch_complin : RCompLin (M_Lg …) (RelaxedHoareSpec.EI δcoh) (regs0, []) (RelaxedHoareSpec.EI (δset N)) ([], []).
Corollary latch_rel_lin s : MTraces (EI δcoh) (M_Lg …) (regs0, []) s -> PrefixView.complete s ->
  rel_lin PrefixView.sel s si (seq_legal (δset N) []).
Lemma mtraces_guard : MTraces (EI δcoh) (M_L …) σ0 s -> (inserts of s on tw) -> MTraces (EI δcoh) (M_Lg … tw) σ0 s.
Lemma δset_sat_agree : (≤ N distinct keys inserted in W) -> seq_legal (δset N) [] W <-> seq_legal δsetU [] W.
Corollary latch_rel_lin_P12 : (* unguarded M_L, complete s, P1 (inserts on tw), P2 (≤ N keys) *)
  rel_lin PrefixView.sel s si (seq_legal δsetU []).
```
- `latch_complin`: via `rlhl_complin_eihl`; assumptions {classic}.
- `latch_rel_lin`: via `complin_ei_rel_lin`; assumptions {classic, eq_rect_eq}.
- `mtraces_guard`: by induction on `module_execution_tagged`; closed.
- `latch_rel_lin_P12` is instantiated at `si := findep rc` (the paper's I_L) and at `si := ∅`.

**Stage 2 (after part A).** `latch_rlhl2E` for the unguarded `M_L` over `EIe δsetU (preL tw N)`, then `RCompLinErr` (copy-cat inclusion with errors), and rel_lin for complete error-free traces. The error branches:
- a non-writer insert steps to `PossError` (`psa_inv_error`) at its first `Rd(Lseq)` invocation, with readiness by blocking;
- a capacity violation steps to `PossError` at the LP.

Also prove `latch_noerr : ¬ module_error_tagged (EIhl δcoh) …`. This makes D5 (i)'s implementation obligation vacuous.

## 4. Non-vacuity (file L6)

1. **`latch_retry_exec`** (N = 1, full idiom, `scan = false`; closed). A complete execution of `M_Lg`:
   - `t_w`: `insert(1)`, 14 calls;
   - `t_r`: one `print()` overlapping it;
   - iteration 1 reads seq = 1 and n₁ = 0, then the retry read returns 2, so it retries;
   - iteration 2 reads seq = 2, n₀ = 1, a₀₀ = 1 and returns `[1]`;
   - the print's LP lies after the insert's LP.
   
   Through `latch_rel_lin` it is rel_lin. Port the sibling's Part 15 `produces` proofs and the stepping tactics; write a `select` tactic.
2. **`latch_reorder_exec`.** Underlay reordering does happen in the verified module:
   - the reader emits `Rd(La c 0)` before `Rd(Ln c)`;
   - the writer emits `Wr(Ln false)` before `Wr(La false 0)`.
   
   This is the analogue of `z_reorder_exec`.
3. **LB-shaped datum.** `lbw := [inv tw 0 OPrint; inv tw 1 (OIns 1); res tw 1 (OIns 1) tt; res tw 0 OPrint [1]]`:
   - `lbw_cc`: it is in `RTraces (EI (δset 1)) ([],[])` under `F_L rc`, because the copy-cat lets the insert overtake (SI(print, insert));
   - `lbw_not_rel_lin0`: it is not rel_lin under ∅;
   - hence, through `latch_rel_lin` at ∅ and the independence of `M_L`'s traces from `si` (by conversion), `lbw` is not a trace of `M_Lg` for any `si`.
   
   So I_L admits a behaviour that this module never shows. The only relaxation actually visible is item 2 (underlay reordering) plus ordinary overlap.
4. **Optional.** `no_wmb1` gives an execution whose print returns a non-state, and hence the universal negative `∀ I R G, ¬ RLHL2Hyps …` for that variant, in the style of `cxy0_no_rlhl2`.

## 5. Writer tasks

Common acceptance for every task:
- builds with Rocq 9.3.0 under `/opt/homebrew/bin`; `_CoqProject` updated and the Makefile regenerated;
- no `Admitted`, `Axiom`, `vm_compute` or `native_compute`;
- K/S/P/R header with `Print Assumptions`;
- CounterXY, Inherit and the sibling repository are not edited.

| ID | Files | Content | Accept | Size / iterations |
|---|---|---|---|---|
| **L0** | `examples/Relaxed/RelaxedHoareLatchProg.v` | §1 port; `δcoh`, `δset`, `δsetU`, `preL`, `F_Lsi`, `M_L`, `M_Lg`, `spin`, `opval`; `latch_new` keeps sortedness, NoDup and length ≤ N; `spin_no_produce` | closed; header maps each definition to its sibling line range | 600–900 / 1 |
| **L1** | `models/simlin/RelaxedHoareRun.v` | generic `SStep`/`run`/`rp_run` (via `RProvable_coind`); `dprec_run` (dprec in run contexts: `(2i,2j)` iff ¬SI, `(2i+1,2j)` iff i ∈ dix_j, `(2j,2j+1)`); `Done` facts and their monotonicity under `EIhl`; record-key NoDup; `GAge` and its preservation under invoke/emit/return/`lin_update`; `emit_ready_block` | closed; smoke test: `rp_run` re-derives a one-call `call` body | 600–1000 / 1–2 |
| **L2** | `examples/Relaxed/RelaxedHoareLatchInv.v` | `IL`, `LG`, `LR`, `Excl`, `midflight`, `Ω_ins`, `Ω_prt`; `excl_unique`, `seq_mono_R`, `stable_copy_R`, `regs_frozen_R`; `latch_rlhl2_of_sem : (∀ t op, MethodSem …) → RLHL2Hyps …` (pattern of `ren_rlhl2_of_sem`); `mp_PI` for both methods | closed | 900–1300 / 2 |
| **L3** (checkpoint) | `…/RelaxedHoareLatchReader.v` | `print_provable : MethodProvable … t OPrint Ω_prt Qprt`, both `scan` values | closed; header lists the genuine `ns_if`/`bw_if` premises and where they are discharged. **If over 1,500 lines or stalled, switch the writer to the semantic route** | 1000–1500 / 2–3 |
| **L4** | `…/RelaxedHoareLatchWriter.v` | `insert_provable` for t = tw; `MethodSem` vacuous for t ≠ tw | closed | 1200–1800 / 2–3 |
| **L5** | `…/RelaxedHoareLatch.v` | §3 and the `lbw` datum | {classic} (+ eq_rect_eq through `cc_rel_lin`) | 300–600 / 1 |
| **L6** | `…/RelaxedHoareLatchExec.v` | §4 items 1–2 (optionally 4) | closed | 600–1000 / 1–2 |
| **L7** (after part A) | `…/RelaxedHoareLatchErr.v` | stage 2 | per part A's statements | 400–800 / 1–2 |

**Dependencies.**
- Order: L0 → L1 → L2 → {L3, L4} → L5 → L6. L3 and L4 can run in parallel once L2's statements are frozen.
- L7 depends on part A, which must provide:
  - `pre` taking the thread id (P1 needs it);
  - an error step at an emission, or at the overlay invocation;
  - `PossError` absorbing everything.

## 6. Research-level points for the author

1. **I_L is not exercised over COH.** The proof works for every overlay relation, including ∅. The LB-shaped behaviour that I_L admits is never produced here (§4 item 3). Decide:
   - whether this version exports I_L (contract weaker than the implementation, so it can still be replaced by an ARM implementation) or ∅;
   - how overview.tex:335 ("admits load buffering") should be worded.
2. **P1 non-overlap is unneeded.** The trailing `oMb` serializes same-thread inserts. Unverified conjecture: over COH even the `oMb` is redundant, since `wmb0` already orders the previous insert's copy-1 writes. A `no_mb` proof would need a two-writer invariant.
3. **P1 needs the thread id in `EIe`'s `pre`.** The RLHL-3c sketch has `pre : St → op → Prop`. Also decide where the error step may occur: at an underlay emission (needs readiness) or at the abstract invocation.
4. **The print LP uses the call's own prophesied future via the ghost.** This relies on run-to-completion (m-33). Under a non-prophetic semantics, a stuck print would break readiness for later same-thread prints unless helping is allowed.
5. **Scope of the claim.** The underlay is `EIhl` over an SC register file with table semi-independence ("COH + barriers"). Its relation to trace.tex:215–223's per-location COH model is unproved (M-20 converse, M-22). The result must not be cited as the ARMv8/buffered LatchSet; that remains on the window route. Re-word intro.tex:106/115 accordingly.
6. **Stage 1 versus the decided form.** Stage 1 states P1/P2 as trace hypotheses and uses the saturating spec. The decided form, errors via m-8/D5 (i), arrives in stage 2. Confirm that stage 1 is acceptable as an intermediate claim.

## 7. Main risks

1. **Slot bookkeeping in Γ** (dprec over `2j`/`2j+1`). Mitigation: the `dprec_run` lemma, and the edge-design rule: phase facts only on (F2) chains, value facts only on (F3) edges.
2. **The ghost-based "last `Rd(Lseq)`" case split in the reader's LP.**
3. **Dependent `Wait (MkFutureRef op h)` continuations.** Use `run_unfold` and `rp_wait_pending` over `lar`. Records go through `opval`.
4. **Maintaining I5 and I6 at a stuck insert.** Midflight is defined by counting, not parity.
5. **L6 length.** About 50 module steps; needs a `select` tactic.

### Critical files for implementation
- /Users/index/Documents/GitHub/rbgs/examples/Relaxed/LatchSetProg.v (source to port, Parts 1–5 and 7; read-only)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoare.v (`RProvable`, `rp_futureD`, `rp_wait_pending`, `RProvable_coind`, `rp_dowhile`, `MethodProvable`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareDag.v (`NewSlotOK`, `BarrierWith`, `dprec`, `before`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareBase.v (`RLHL2Hyps`, `ghost_emit`, `inv_blocks`, `PostInvoke`, `CallTriple`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v (`EIhl`, `eihl_mine*`, `rlhl_complin_eihl`, `complin_ei_rel_lin`, `cc_rel_lin`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareInherit.v (pattern for `Iren`/`Rren`/`Gren`, `ren_rlhl2_of_sem`, `emit_ready_SI`)