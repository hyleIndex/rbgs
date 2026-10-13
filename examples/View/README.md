# View-based (timestamped) specifications and proofs

Ported from CSL-Lin (`hyleIndex/CSL-Lin`, `master` at `3f7baaa`, 2026-06-16). These are the Rocq proofs that §6.3 of the paper cites: the exchanger (1,195 → 1,503 lines) and the elimination-backoff stack over TSO-style view specifications.

## Files

| rbgs file | CSL-Lin source | Content |
|---|---|---|
| `ViewSpecs.v` | `examples/Specs.v` (only the modules below) | `CASRegTSOSpec`, a CAS register with a timeline `cas_mem : Time → A` and per-thread views `cas_view : tid → Time`. `TryStackSpec` and `StackSpec`. `SeqLockUnderlaySpec`: x, y and a ticket lock in one LTS, with per-thread, per-location views and a ghost owner. `SeqLock`, the overlay, with a scalar per-thread frontier. |
| `LegacyNotations.v` | (new) | CSL-Lin's assertion notations, see below |
| `ExchangerTSO.v` | `examples/Exchanger.v` | Exchanger over `VCASRegTSO` → `VExch` (SC), with the `Tail` adapter |
| `TryStackTSO.v` | `examples/TryStackTSO.v` | `OwnedMemTSOSpec`; try-stack over `VCASRegTSO ⊗ VMemTSO` → `VTryStack` (SC) |
| `SeqLockTSO.v` | `examples/seqlock.v` | SeqLock over `VSeqLockUL` → `VSeqLock` |
| `EBStackTSO.v` | `examples/EBStackTSO.v` | The EB stack tower: `E = EShared` → `Fmid = VTryStack ⊗ VExch` → `VStack`. **Changed from CSL-Lin:** the bottom was `ECombo` (`VComboTSO`, a hand-built global view over the three objects), with a hand-written bridge of about 980 lines to the tensor of the per-object views. It is now `EShared`, the three objects on one shared clock derived with `ViewLift` (`Pall`), and the bridge is a composition of generic simulations (about 50 lines; see `ViewLiftTensor.v`). Differences of the new bottom: one atomic phase for all three objects, where `VComboTSO` let calls on different objects overlap; and no counterpart of `VMemTSO`'s pending-state error. The proofs of the component and stack layers are unchanged. |

Not ported: CSL-Lin's `Exchangersc.v`, `TryStack.v` and `EBStackSC.v` (rbgs already has newer versions of them in `examples/Exchanger` and `examples/Stacks`), and the non-view modules of `Specs.v` (FAI, Lock, Reg, Ticket).

## Proof framework

The proofs use rbgs's unchanged SC simlin logic: `AssertionsSingle`, `RGILogic.soundness`, `TPSimulation.cal`. The view lives entirely in the LTS specifications of the underlays. Possibility states carry no timestamps.

## Changes from the CSL-Lin sources

Each file starts with a banner naming its source. Apart from that, the changes are limited to the following.

- **Imports:**
  - `Stdlib.*` paths;
  - `examples.Common.AtomicLTS`, which is identical to CSL-Lin's `AtomicLTS`;
  - `examples.Exchanger.ExchangerSpec`, which differs from CSL-Lin's only in its imports.
- **Assertion API:**
  - `Assertions` → `AssertionsSingle`;
  - `@Assertion _ _ VE VF` → `@Assertion (@ProofState _ _ VE VF)`;
  - `Build_ProofState` → `Build_ProofStateSingle`;
  - `Assertions.Conj` → `Logics.Conj`.
- **`ModuleImpl` argument order:** `li_impl t m` / `fun t m` → `li_impl m t` / `fun m t` (rbgs: `forall m, tid -> Prog`).
- **Notations:** `TryStackTSO.v`, `SeqLockTSO.v` and `EBStackTSO.v` import `LegacyAssertionNotations` instead of `Logics`. It restores CSL-Lin's parsing of `//\\` (level 40, left associative), `\\//`, `==>>` and `⊨`, over the same rbgs constants. rbgs makes `//\\` right associative, and the proof scripts destruct conjunction chains in the left-nested shape. `ExchangerTSO.v` builds with rbgs's notations unchanged.
- **Rocq 9.2:**
  - `Context {A : Type}` outside a section → `#[local] Parameter A : Type` (`EBStackTSO.v`). This is what Coq 8 did implicitly.
  - Two `replace … by exact Hfind` → `by exact (eq_sym Hfind)` (`EBStackTSO.v`).
  - One `apply ImplRefl` → `all: apply ImplRefl` (`SeqLockTSO.v`), because rbgs's `solve_conj_impl` already closes that goal.

- **Bottom of the EB stack** (`EBStackTSO.v`, 2026-10-07): `ECombo` / `VComboTSO` and its 980-line bridge are replaced by the derived `EShared` and generic simulations. This is a change of specification, not of proof scripts; see the table above.

`ViewSpecs.v`'s modules are character-for-character identical to the corresponding modules of CSL-Lin's `Specs.v`.

## Assumptions

No `Admitted`, `admit` or `Axiom`. `Print Assumptions` on `ExchangerImpl.Mexchanger`, `TryStackTSOImpl.Mtrystack`, `SeqLockImpl.Mseqlock` and `EBStackTSOImpl.{components_correct_tensor, components_correct, ebstack_mid_correct, Mcomponents, MebstackMid}` shows three things:

- `eq_rect_eq` and `classic`, which come from the simlin framework;
- the opaque element type of the functor instantiation: `ExchangerImplParam.A`, `TryStackTSOImplParam.A`, `EBStackTSOImpl.A`.

`SeqLockImpl.Mseqlock` has only the first two.

## ViewLift: views derived from a sequential specification (new)

The generic part lives in `models/view/` (and `models/simlin/RelaxedStamping.v`). It does not depend on `examples/`.

| File | Content |
|---|---|
| `models/simlin/AtomicLTS.v` | Moved from `examples/Common/AtomicLTS.v`, unchanged. The old file re-exports it, so existing imports keep working. |
| `models/view/UnderlayRefinement.v` | `cal_refine`: a forward simulation between underlay LTSs (steps, plus errors reflected) transfers any `TPSimulation` / `cal` proof to the refined underlay. `EBStackTSO.v` uses it, with T1, for its bottom layer. Simulations compose: `us_refl`, `us_trans`, and `us_tens` for tensors. `us_reach` transfers finite executions. |
| `models/view/ViewLift.v` | `ViewLift.VL P`: the timestamped LTS derived from `P = (spec, err, retro, dep, sync)` (definition below). Theorems `vl_sim_by_sc` / `sc_sim_by_vl`, `cal_sc_to_view` / `cal_view_to_sc`. |
| `models/view/ViewLiftTensor.v` | T1, `shared_sim_by_tensor`: the shared-clock view of `P1 ⊗ P2` (with arbitrary cross-component dependencies) is simulated by `VL P1 ⊗ VL P2`. Corollary `cal_tensor_to_shared`. `PT_sync` / `PT_pres`: the collapse conditions carry over to the product. |
| `models/simlin/RelaxedStamping.v` | `rel_lin_iff_rhb_stamping`: `rel_lin` holds iff the operations can be stamped so that a legal witness is sorted by stamp and stamps increase along every `rhb` edge. This is close to a restatement of `rel_lin` (stamp = position in the witness, chosen after the whole trace is known). It is **not** a view in the sense of view-based models: load buffering on COH has such a stamping, but no incremental view produces it. Also: only the order of stamps matters (P2). |
| `models/view/PrefixView.v` | The paper's prefix views (Defs. I.2–I.4) on complete relaxed traces, with an optional real-time condition `rt_ok`. `rel_lin_iff_view_rt`: on complete traces, `rel_lin` holds iff there is a prefix view that respects real time; the direction from `rel_lin` (Prop. I.10) needs no view-based compatibility. `rel_lin_view_rt_chain`: the prefix witnesses form a chain of prefixes, so no operation is ever inserted below a justified one. `thm_I11_rt`: Thm. I.11 with real time. `counterexample_I11`: **without real time, Thm. I.11 is false**, see below. `reg_not_compat_printed` / `reg_compat_fixed`: Def. I.1 as printed fails even for a register; with the hypothesis that the inserted operation overtakes one of its own thread, it holds. |
| `models/view/ViewLiftAdequacy.v` | T2, see below. |
| `models/view/ViewPossibility.v` | The trace-level core of Thm. I.9, with real time and **without view-based compatibility**, see below. `poss_view_rt` / `poss_rel_lin`: a possibility run (concrete events interleaved with VT-Invoke / VT-Return steps) whose steps satisfy local conditions and the semantic side condition gives a real-time-respecting prefix view, for any `ν` with `ν []`. `timeline_valid` / `timeline_view_rt` / `timeline_rel_lin`: for `ν = nu_P`, the `ViewLift` timeline rule discharges the side condition. |
| `models/view/ViewLHL.v` | The paper's VLHL over relaxed traces with futures, as the global simulation of `models/simlin/RelaxedGSim.v` with view-trace LTSs on both sides. `VT nu`: an LTS whose state is a view trace that respects real time; a step is VT-Invoke / VT-Return. `vt_sound`, `vt_complete`: it is a sound presentation (complete traces are relaxed linearizable) and a complete one (every prefix of a complete relaxed linearizable trace is a trace). **P1**, `presentation_choice`: a global simulation over any complete underlay presentation and any sound overlay presentation proves relaxed linearizability over every underlay that implements `(νE, IE)`; neither presentation appears in the statement. `vlhl_sound`: the instance with `VT` on both sides, i.e. Thms. I.9 + I.11 with real time. `VT0` (Def. I.4 as printed, no real time): complete (`vt0_complete`) but not sound (`vt0_not_sound`), so the paper's views can present an underlay but not an overlay. `complete_pres_enlarge`, `sound_pres_shrink`, `fsim_traces`: swapping presentations along trace inclusion. |
| `examples/View/ViewLiftCAS.v` | `VCASRegTSO` is bisimilar to `VL CASP`. Together with the collapse theorem, `cas_tso_to_sc` / `cas_sc_to_tso`: `cal` proofs over the hand-written TSO register and over the atomic SC CAS register transfer in both directions. |
| `examples/View/ViewLiftMem.v` | `VMemTSO` as `VL MemP`, where `mread` is retroactive and `malloc` / `mwrite` are appended and synchronizing. `sc_sim_by_tso`, `vl_sim_by_tso`: the SC memory and `VL MemP` are simulated by `VMemTSO`. `mem_tso_to_sc`, `mem_tso_to_vl`: `cal` transfer. Only this direction: `VMemTSO`'s error `error_mwrite_racy` (raised in a pending state) has no counterpart in an atomic LTS. |
| `examples/View/EBStackViewLift.v` | `components_correct_sc`: the EB stack components over the atomic SC product, from `EBStackTSOImpl.components_correct` by the collapse theorem (every appended operation of `Pall` synchronizes). |
| `examples/View/ViewLiftMultiWriter.v` | Two writers under TSO (`TP`: two locations, writes appended and not synchronizing, reads retroactive, only write→read of the other location unordered). Thread 1 writes `x`, thread 2 writes `y`, thread 3 reads `y = 1` then `x = 0`. `no_issue_order_run`: no run of `VL TP` has the writes in issue order. `reorder_run`, `reorder_canon`, `reorder_rel_lin`: the run with thread 2's write first exists, and its canonical trace, where thread 1's write overlaps thread 3's read of `x`, is relaxed linearizable. `issue_trace_not_rel_lin`: the trace where thread 1's write responds before thread 2's is invoked is not. `poss_run_rel_lin`: the overlapping trace via `ViewPossibility.timeline_rel_lin`, so its hypotheses are satisfiable by a non-SC behaviour. |
| `examples/View/ViewLiftOMCA.v` | What `ViewLift` over SC memory cannot express, for any dependency and synchronization tables (`TPd`), when each thread's operations respond in program order (`Merge`). `no_lb`: load buffering is not a run. `no_2p2w`: 2+2W never ends in `x = 1, y = 1`. Both are allowed by ARMv8. `n6_mp_inseparable`: if the x86-TSO test n6 is a run, so is message passing (forbidden by x86-TSO); `tso_no_n6`: the TSO table rules n6 out. The cause is store forwarding. `lb_rel_lin`: load buffering as a futures trace is verified by a timeline possibility run (`ViewPossibility.timeline_rel_lin`) with every write appended. |
| `examples/View/ViewLiftSeqLock.v` | `VSeqLockUL` is bisimilar to `VL SLP` (`tso_sim_by_vl`, `vl_sim_by_tso`). `seqlock_tso_to_vl` / `seqlock_vl_to_tso`, and `Mseqlock_vl` (the SeqLock proof over the derived underlay). `vl_stale_read`, `sc_no_stale_read`, `tso_stale_read`: the object is not SC. `stale_run`, `stale_canon`, `stale_rel_lin`: the run of the stale read and its canonical trace. |

**How `ViewLift.VL P` works.**

- The state is a timeline `Time → state`, each thread's past operations with their timestamps, a visibility floor and a horizon.
- A response of `m` by thread `t` at timestamp `h` requires `h > floor` and `h >` every earlier operation `o` of `t` with `dep o m`.
- **Retroactive operations** (`retro m = true`) read the timeline at `h` and must leave the state unchanged.
- **All other operations** are appended: `h > horizon`, and the timeline is overwritten from `h` on.
- **Synchronizing operations** (`sync m = true`) raise the floor to `h`.

Since state-changing operations are only ever appended, no view-based-compatibility side condition is needed.

**Collapse.** If every appended operation synchronizes, the floor always sits at the last state change. So every operation observes the current state, and `VL P` is bisimilar to the atomic SC LTS `SC P`. This covers `CASP` and `MemP`, but not `SLP`.

**T2 (`ViewLiftAdequacy.v`).** A run of `VL P` is the sequence of its operations, each with the timestamp chosen at its response (`Run`).

- `run_rel_lin`: let `L` be any complete relaxed trace of the run's operations (`Del`) in which:
  - same-thread invocations keep the run order;
  - every response that precedes an invocation belongs to an operation that is smaller in (timestamp, run index) order.

  Then `L` is relaxed linearizable for the sequential specification `nu_P` of `P` and the semi-independence relation `dep = false`. The witness lists the operations in (timestamp, run index) order.
- `canon`, `canon_rel_lin`: every run has such a trace. Operations are invoked in run order, and each response immediately follows its invocation. The exception: if a later operation is timestamped strictly before it, the response is delayed to the end (`canon_prompt`).
- `canon_sync_prompt`: synchronizing operations are never delayed.
- `vl_exec_rel_lin`: every execution of `VL P` determines such a run, with the execution's responses in run order.

**SeqLock (`SLP`).**

- `rd` is retroactive. Every other operation is appended. Only `rel` synchronizes.
- `dep o (rd l)` holds exactly when `o` advances the thread's view of `l`. That excludes `wrt l'` for `l' ≠ l` (TSO's write-read reordering) and excludes `acq`.
- `acq` and `rel` read the lock at the thread's own view rather than at the current state. The invariant `k_stale` shows the two coincide whenever the step is enabled.
- `get_ticket` / `test_ticket` read above every view, so they are appended operations that leave the state unchanged.

**Assumptions.**

- Every theorem in these files depends on `eq_rect_eq` at most, through `LTSSpec.ResEvInversion`, `inj_pair2` or `dependent destruction`.
- `cal_refine`, `rel_lin_iff_rhb_stamping`, `run_rel_lin`, `canon_rel_lin`, `canon_sync_prompt` and `ViewLiftSeqLock.tso_sim_by_vl` are closed. `PrefixView` and `ViewPossibility` depend on `eq_rect_eq` only.
- In `ViewLiftMultiWriter`, `no_issue_order_run`, `reorder_rel_lin` and `overlap_is_canon` are closed; `issue_trace_not_rel_lin` and `poss_run_rel_lin` depend on `eq_rect_eq` only.
- In `ViewLiftOMCA`, `no_lb`, `no_2p2w`, `n6_mp_inseparable` and `tso_no_n6` are closed; `lb_rel_lin` depends on `eq_rect_eq` only.
- The layer-level corollaries also inherit the framework's `classic` (`Mcomponents_shared`, `components_correct_sc`, `Mseqlock_vl`). `EBStackViewLift` additionally inherits the opaque element type `EBStackTSOImpl.A`.

**Thm. I.11 needs real time (`PrefixView.v`, Part 2).** Def. I.2 orders only same-thread operations, so a prefix view may stamp an operation below an operation of another thread that has already responded. Paper Remark 2 notes that such view traces are not relaxed linearizable. The proof of Thm. I.11 nevertheless reads relaxed linearizability off the overlay's view. Counterexample:

- Take `M = {write(v) = E.wrt(v); read() = return 0}` over a register `E = F` whose reads may overtake earlier writes of the same thread.
- Every overlay trace of `M` has a prefix view (`zero_reads_view`): stamp the reads below all writes. So the premise of Thm. I.11 holds, and the VLHL possibility rules derive it.
- The execution "thread 1 writes 1 and returns; afterwards thread 2 reads 0" has a relaxed linearizable underlay and an overlay that is not relaxed linearizable (`s0_not_rel_lin`).

With `rt_ok` (an operation invoked after another has responded gets a larger stamp), the theorem holds (`thm_I11_rt`), and Prop. I.10 no longer needs view-based compatibility: its witnesses only grow at the end (`rel_lin_view_rt_chain`).

**Thm. I.9 without compatibility (`ViewPossibility.v`).** The possibility rules VT-Invoke / VT-Return already require `t · e ∈ view(ν)` of the abstract trace `t`. Compatibility is used in the proof of Thm. I.9 only to keep that witness after an operation is stamped below a justified one.

- Part 1: if the side condition is checked as stated (`side`: the extended abstract trace has a timestamp-ordered witness), together with local conditions (`ok`), the concrete trace has a `view_rt`. The local conditions include the real-time condition missing from the paper: an abstract invocation gets a stamp above every operation that responded before its concrete invocation. Several pending operations per thread are allowed. No hypothesis on `ν` beyond `ν []`.
- Part 2: if the abstract responses, with their stamps, form a run of `VL P`, the side condition holds at every step (`timeline_valid`). The witness is T2's incremental witness. So for every `ViewLift` object the `ViewLift` rule (only state-preserving operations may be stamped below an existing stamp) replaces compatibility.

**Not done yet.**

- ~~Relating `VComboTSO` to `VL Pall`~~: instead, `EBStackTSO.v` now uses `VL Pall` as its bottom and `VComboTSO` is gone (see the table above for the two differences).
- Thm. I.9 with real time at the level of the logic: done as a semantic simulation in `models/view/ViewLHL.v` (`vlhl_sound`, via `models/simlin/RelaxedGSim.v`). The rules of the logic (rely / guarantee, per-call simulation) are not done; they are shared with RLHL. The CSL-Lin proofs are SC LHL over blocking code.

## Known limitations (input for improving views)

- **The hand-written specifications are now all accounted for.**
  - `VCASRegTSO` and `VSeqLockUL` are bisimilar to `VL CASP` and `VL SLP`.
  - `VMemTSO` simulates `VL MemP`.
  - They remain in the layer interfaces of the ported proofs (`li_lts`). The derived versions are used in `EBStackViewLift.v` and `Mseqlock_vl`.
- **The overlays are SC** (`VExch`, `VTryStack`, `VStack`). `VSeqLock`'s timestamps do not affect its state.
- **Only the SeqLock underlay is weak.** `VCASRegTSO` and `VMemTSO` collapse to SC, so the TryStack / Exchanger / EB stack proofs do not exercise weak behaviour.
- **Duplicated specs.** `ViewSpecs.TryStackSpec` / `StackSpec` duplicate `examples/Stacks/StackSpec.v`, using CSL-Lin's older constructor shapes.
