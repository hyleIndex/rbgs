<!-- Writer report for RLHL-3a, iteration 1 (2026-10-13), copied verbatim by the orchestrator. It is the Writer's claim, not evidence. Overwritten each iteration. -->

## Writer report: RLHL-3a.1

### Summary
Done. RLHL soundness is now stated and proved in the style of CompLin, for **every** execution (complete or not) and **any** `VE` and `VF`. Every overlay trace of `M` over `VE` is an overlay trace of the relaxed copy-cat `idF` run over `VF`.

- **Proof route:** the run produced by `RelaxedGSim.rinv_exec` is replayed as one execution of `idF` (`reify`). This is the analogue of `CompLinSound.abs_reaches_reify` / `cal_to_CompLin`.
- **Counter instance:** proved (`counter_complin`).
- **Sanity checks:** the out-of-order counter trace is a copy-cat trace, and the overlay junk trace is not (proved for every copy-cat execution over `CVFe`, closed).
- **Not done:** optional item 5 (complete-trace link from `RTraces (EI δ)` to `rel_lin`). It is not cheap; see Open issues.
- **`RLHL2Hyps` itself is not instantiated by an interesting example here:** the only instance is still the counter (I=∅, over `HVE`).

### Files changed
- `/Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLin.v` (new, 1141 lines). It contains:
  - the definitions `idF`, `MTraces`, `RTraces`, `RCompLin`;
  - the replay invariant `CInv` and the four step lemmas;
  - `reify`, `rinv_val`, `rinv_reify`, `gsim_complin`, `rlhl_complin`, `rlhl_complin_ei`;
  - a generic `cc_trace` (every method trace of the copy-cat);
  - a header covering the items asked for in the brief.
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareChecks.v` (additions only):
  - `Require Import models.simlin.RelaxedHoareCompLin`;
  - new `Module CounterCompLin` after `End CounterRelLin`, with an invariant `JInv` for every copy-cat execution over `CVFe`;
  - one new bullet in the header's Contents list.
- `/Users/index/Documents/GitHub/rbgs-rlhl/_CoqProject`: `models/simlin/RelaxedHoareCompLin.v` added after `RelaxedHoareGSim.v`. Makefile regenerated with `coq_makefile -f _CoqProject -o Makefile`.

### New / changed statements
- `RelaxedHoareCompLin.idF : RelaxedModuleImpl F F := fun op _ => Future op (fun f => Wait f (fun r => Ret r))`
  - `idF_call`: `idF op t = call op`.
- `MTraces VE M σ0 s := exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\ overlay_events evs = s`
- `RTraces V v s := MTraces V idF v s`
- `RCompLin M VE σ0 VF v0 := forall s, MTraces VE M σ0 s -> RTraces VF v0 s`
  - Analogue of CompLin Def 4.1, with no error clause.
- `gsim_complin : forall VE VF M S σ0 v0, GSimRel VE VF M S -> S (initial_tagged_module VE σ0) (PossOk v0 []) -> RCompLin M VE σ0 VF v0`
  - Supports `cal_to_CompLin` and relaxedlin.tex:665-667.
- `rlhl_complin : RLHL2Hyps I R G M σ0 v0 -> RCompLin M VE σ0 VF v0` (any `VE`, `VF`).
- `rlhl_complin_ei : RLHL2Hyps I R G M σ0 (s0, []) -> RCompLin M VE σ0 (RelaxedHoareSpec.EI δ) (s0, [])`
- `reify` (inside `Section Reify`): from `vf_path VF v0 (abs R) vfin`, `TValid`, `wf (conc R)`, unique abstract invocations, `AUniq` and `Hval`, conclude `exists evs cf, module_execution_tagged VF idF (initial_tagged_module VF v0) evs cf /\ overlay_events evs = conc R`.
- `cc_trace : program_produces_tagged t (idF op0 t) tr r -> exists h, tr = [cc_inv_ev t h op0; cc_res_ev t h op0 r]`
- Counter instance (`CounterCompLin`):
  - `counter_complin : RCompLin Mc HVE hσ0 CVFe (0, [])`
  - `ooo_counter_trace : MTraces HVE Mc hσ0 ooo_trace` and `ooo_copycat_trace : RTraces CVFe (0, []) ooo_trace`
  - `junkF_not_rtrace : ~ RTraces CVFe (0, []) junkF`, with `junkF = [Inv(t0,1,Inc); Inv(t0,2,Inc); Res(t0,2,Inc,0)]`
  - `junkF_not_counter_trace : ~ MTraces HVE Mc hσ0 junkF`

### Semantic/assumption changes
None. No existing definition or theorem was changed:
- `git diff` on tracked `.v` files shows only the pre-existing comment changes.
- The `_CoqProject` diff adds one line (the other seven new lines were already there, uncommitted).
- The edits to the checks file are additive.

The new file uses `Classical_Prop.classic` once, in `rinv_val`. That is a baseline axiom; it is explained under Print Assumptions.

### Build
- Command: `export PATH=/opt/homebrew/bin:$PATH; coq_makefile -f _CoqProject -o Makefile; make -k -j10`
- Tail of the output:
  ```
  ROCQ compile structures/DCPOs.v
  Error: Syntax error: [record_fields] expected after '{' (in [constructors_or_record]).
  make[1]: *** [structures/DCPOs.vo] Error 1
  make: *** [all] Error 2
  ```
  This is the known baseline failure.
- 178 of 179 files are up to date. Rebuilt: `RelaxedHoareCompLin.v`, `RelaxedHoareChecks.v`; nothing else requires them.
- Grep is clean: no admit, Axiom, Parameter, Hypothesis, Variable, unset checking, `vm_compute` or `native_compute` in the touched files.

### Print Assumptions
| Theorem | Assumptions |
|---|---|
| `reify` | Closed |
| `cc_trace` | Closed |
| `junkF_not_rtrace` | Closed |
| `gsim_complin` | classic |
| `rlhl_complin` | classic |
| `rlhl_complin_ei` | classic |
| `rinv_reify` | classic |
| `counter_complin` | classic |
| `ooo_copycat_trace` | classic |
| `junkF_not_counter_trace` | classic |
| `rlhl_gsim` (unchanged) | Closed |
| `counter_rel_lin` (unchanged) | eq_rect_eq |
| `counter_vt_no_rlhl2` (unchanged) | Closed |

Why `classic` is needed: the copy-cat commits its result at the overlay invocation. The replay must therefore know whether the run has an abstract response for the call, and that is undecidable because handles have no decidable equality. When there is no abstract response, the default result is `M`'s own committed result (from `ri_cin`, `ri_cact`, `ri_cdead`), so no inhabitation assumption on `Sig.ar op` is needed. `eq_rect_eq` was avoided: results are compared through response events (`some_inj`, `abs_res_step_any`).

### Gap check (K / S / P / R)
- **K:** the kernel checked the statements above with the assumptions listed.
- **S:**
  - `gsim_complin` / `rlhl_complin` quantify over every execution, pending calls included, and over every `VE` and `VF`.
  - Single possibility.
  - No error clause: underlay `Error` is invisible, so this is partial correctness.
  - Traces are overlay `ThreadEvent` lists, not plays.
  - `RTraces` ranges over every copy-cat execution (any underlay handles, any committed results); `reify` exhibits one, with underlay handle = overlay handle.
- **vs CompLin.v Def 4.1:**
  - Same shape (`ImplTraces M ⊆ ImplTraces idImpl`).
  - Missing: the `TErr` / `ImplTracesClosed` clause.
  - The relaxed `idF` uses future + wait and the tagged frontier, not `Vis`.
- **P** (Appendix/relaxedlin.tex:665-667, `ν_E;cc_E;M[Threads] ⊆ ν_F;cc_F`):
  - `RTraces VF v0` plays `ν_F;cc_F`.
  - The left side is `M` over `VE`. No separate `cc_E` is composed in; `M`'s own frontier (F1)-(F3) does that relaxation. That the two left sides agree is **not mechanized**.
  - The hypothesis is `GSimRel` / `RLHL2Hyps`, not the paper's thread-local simulation.
  - The paper's Completeness proposition is out of scope.
- **Layering (author decision M-20):** `rlhl_complin_ei` provides `VF := EI δ`. The counter's `VE` is `HVE` (handle-linear, atomic at invocation), not literally `EI` of an FAA spec. The stamp-based VT route (M-18) stays complete-trace only.
- **R** (Reviewer B, popl2027-reviews.md:313-316, "program logic, its soundness proof against a weak memory model such as RC11, and … a concurrent object alongside … its client"):
  - Soundness of RLHL now covers incomplete traces, which composition with a client needs.
  - Still missing: any memory-model `VE` (RC11 or other), vertical composition and a client (RLHL-3c), and an instance with nonempty semi-independence (RLHL-3b; the counter is I=∅).

### Responses to reviewer findings
- **M-20 / Q3** (author decision: CompLin-style copy-cat soundness): **FIXED** for the RLHL-3a scope. `rlhl_complin` / `rlhl_complin_ei` cover all executions. `junkF_not_rtrace` shows the copy-cat over `EI` rejects the overlay junk trace, which agrees with REW on that trace. It is one data point, not a proof that copy-cat traces equal REW prefixes.
- **M-1** (no route to prefix soundness): partially addressed through copy-cat inclusion instead of `implements` / `rl_prefix`. **DEFERRED**: the link to `rel_lin` (item 5) and composition (RLHL-3c).

### Open issues / risks
1. **Item 5 not done.** It would show that copy-cat traces over `EI δ` are relaxed-linearizable on complete traces, so that `rlhl_complin_ei` implies `rlhl_rel_lin_ei`. It needs an `EInv`-style witness invariant over every copy-cat execution over `EI δ`: queue order (F2), record↔call correspondence, and the witness ordering by underlay-invocation time. That is roughly the size of `JInv` (about 500 lines). Until it exists, what `RCompLin` means as a correctness criterion rests on `RTraces (EI δ)`, supported here only by `junkF_not_rtrace` and `ooo_copycat_trace`.
2. **Headers outside my allowed scope are now partly out of date.** `RelaxedHoareGSim.v` (item 4 "Complete traces only … no theorem concludes … for executions with pending calls") and the corresponding text in `RelaxedHoareSpec.v` and `.rocq-review/concern-matrix.md` should point to `RelaxedHoareCompLin.rlhl_complin` for incomplete traces.
3. **Reusability.** The junk invariant `JInv` is specific to `CVFe`. `cc_trace` and the replay are generic.
4. **For the paper:** the identification of `M` over `VE` with `ν_E;cc_E;M` (copy-cat on the E side, idempotence) is unmechanized and should be stated if the paper cites this theorem.