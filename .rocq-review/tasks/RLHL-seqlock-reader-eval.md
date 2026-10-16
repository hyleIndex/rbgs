<!-- SeqLock reader blocker design evaluation (2026-10-15), read-only panel (A tags, B state/presentation extension, C adjudication) + skeptical synthesis. Saved verbatim by the orchestrator. -->

# SeqLock reader blocker: design evaluation (2026-10-15)

## Scope and summary

**What I reviewed**
- Branch `rlhl`, HEAD 6aef511, with the RLHL work uncommitted. `make -n` reports that `RelaxedHoareSL2Inv.vo` and `RelaxedHoareSL2Exec.vo` are up to date. Rocq 9.3.0.
- I wrote nothing. Every check ran through stdin to `rocq repl`.
- I re-ran all three panel scripts and two new scripts of my own (§9).

**Summary of conclusions**
1. **The panel's diagnosis is right for the presentation `EIhl`.** With the frozen `Isl`/`Rsl`/`Gsl`/`Osl` (and the corrected postcondition from point 2), the untagged reader has no `MethodProvable` derivation over `EIhl`. The argument (C) is rigorous, and its key lemmas are kernel-checked. The full construction is not mechanized. The stronger claim "for every I, R, G" is only argued.
2. **New BLOCKER B-6, missed by all three panels and by Writer B.** The frozen read postcondition `Qsl` can never be reached at `Close` on a machine path whose last iteration is not the ghost's last iteration. Consequences:
   - the read premise of `sl2_read_run_provable`, `sl2rd_rlhl2_of_methods` and `sl2rd_target_of_methods` cannot be satisfied for any `Inv`;
   - this holds for the untagged reader, for the tagged reader of (A), and for the lifted `Qsl` of (B);
   - the fix is cheap and can be done now in Coq.
3. **I recommend (B).** It keeps the program as written and changes no line of the logic. Its trace equivalence and the transfer to `EI` are kernel-checked. It matches the paper's own proof state, which carries the underlay trace. With B-6 fixed, its derivation sketch holds when I re-trace it by hand.
4. **(A) is a sound route to a different program.**
   - The tag `rmb_b ← X, Y` is not produced by the paper's dependency policy, and it contradicts the author's "dependency-only waits" principle.
   - Results transfer to the untagged module for complete traces only, and that transfer depends on an insensitivity theorem that is not written yet.
5. **M-24's proposed repair (i)–(iv) is refuted** by `m24_not_stable`, which is closed.

## 1. The blocker restated

### 1.1 The definitions that cause it

| Definition | Where | Effect |
|---|---|---|
| `rnext` | `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Prog.v:484-493` | Every `dix` is `[]`. A failed validation loops back to `RG`. |
| `dprec_run` | `…/models/simlin/RelaxedHoareRun.v:509` | An edge goes from the response of call i into the invocation of call j only if i ∈ `dix j`. A response receives an edge only from its own invocation. So no reader response is `before` any other slot. |
| `RunCallOK` | `RelaxedHoareRun.v:596` | Slots and `Inv` are required for every handle and every response value v. The machine values s, a, c, s' are therefore prophesied. |
| `Close`, `BarrierWith.bw_sum` | `models/simlin/RelaxedHoare.v:435`; `models/simlin/RelaxedHoareDag.v:424-436` | At return, `Q` must follow from `I ∧ fin0 ∧` the `fin`s of the response slots alone. `NoOwn` is not available there. |
| `FamAt` | `RelaxedHoareDag.v:602` | The certificate is a conjunction of independent per-slot facts. |
| `ei_step`, `hlx_step`, `EIhl` | `models/simlin/RelaxedHoareSpec.v:307`; `models/simlin/RelaxedHoareCompLinSpec.v:980-988, :1156` | A value is fixed at invocation. A response deletes the record, and `used` keeps only `(tid, handle)`. |
| `eihl_mine`; `eihl_done_res_mine` | `RelaxedHoareCompLinSpec.v:1178`; `RelaxedHoareRun.v:1081` | Once a record is consumed, "mine" holds for every value. |
| `ghost_emit` | `models/simlin/RelaxedHoareBase.v:289` | A response leaves the ghost unchanged. Nothing records which call owns an emitted key. |
| `Rsl` | `…/examples/Relaxed/RelaxedHoareSL2Inv.v:372` | Memory moves by arbitrary `eihl_steps`, including responses on k's own keys (`rsl_step`, closed). |
| `Coup`, `isl_read_lp`, `Qsl` | `RelaxedHoareSL2Inv.v:303, :1560, :427` | A read is at `ls_inv` exactly when it owns a pending `rmb`. Its LP is the `rmb` after which it owns none. `Q` says "linearized with r". |

### 1.2 Mechanism

- **Where record and response values meet.** "Record value = response value" is available only inside the response slot's own update (`eihl_mine_res`, CompLinSpec.v:1228). That slot has no outgoing edge, so the identification reaches only its own `fin`, and the `fin`s meet only at `bw_sum`.
- **What the LP needs, and what the return has.**
  - Correctness needs a relation between the four record values and the `A i` recorded at the LP. That relation held only while `Sq_i` was unchanged.
  - At the return, consumed records have lost their values.
  - k's frame state (its phase and its record) cannot store the `Sq_i` it saw at the LP.
- **Why "done κ → value = v" facts fail.** `R k` can consume k's own record. A genuine response and such a consumption are the same `EIhl` transition. So any assertion of the form "done κ → value = v" is unstable under the rely (`m24_not_stable`).

### 1.3 A second, independent blocker (new): B-6

**Claim.** For every `Inv`, the premises of `sl2_read_run_provable` (SL2Inv.v:1855) cannot all hold. The same holds for the tagged reader, and over `EIhlv` with the lifted `Qsl`.

**Argument.** Every step uses closed lemmas. The run in step 3 is not mechanized.
1. The invocation precondition admits a two-iteration footprint, and that state satisfies the invariant: `Mismatch.pinit0` and `Mismatch.isl0`, both closed.
2. The machine path π, where iteration 1 validates with s = a = c = s' = 0, reaches `SDone` (`rok 0 0 = true`). `RunCallOK` must re-establish `Inv` for every v, and `RunStepOK` at `SDone` is `Close (Qsl (0,0))`. So π's `Close` is demanded.
3. Start from the state of step 1. Emit π's 12 events in program order, all genuine, with no rely step. `ctx_triple`'s `fam_init`, `fam_emit` and `fam_return` (Dag.v:704-788) give `Isl Z` and `Qsl Z` at the end state Z.
4. At Z the ghost still holds iteration 2, including an `rmb` of k (`owns_after_iter1`). `owns_rmb_not_qsl` (closed) gives `¬Qsl Z`. Contradiction.

**Cause.**
- `bw_sum` must prove Q without `NoOwn`.
- The quantifier "for every v" forces the derivation to cover paths whose iteration count disagrees with the ghost, which records invocations but not response values.
- `Coup` forbids linearizing while an `rmb` is still owned.

**What the panels got wrong.** (A) wrote "a return with rmbs still owned contradicts NoOwn at RetCond". That contradiction is available at `mp_ret`, but `Close` needs `Q` first, before `NoOwn` is in scope.

**Fix.**
- Use `Qrd k i r s := Qsl k (fR i) r s ∨ ¬NoOwn k (ps_ghost s)`. `mp_ret` discharges the new disjunct by `NoOwn`.
- Generalize `sl2_read_run_provable`, `sl2rd_rlhl2_of_provable`/`_of_methods` and `sl2rd_target_of_methods` to a postcondition per operation, as in `rlhl_sound_complin`'s `∃ Ω Q`. This also serves m-51.
- Optional, at logic level: give `bw_sum` the hypothesis `NoOwn k (ps_ghost s)`. This is sound because `ct_return` already has it.

**Effect on (C).** (C)'s three-run argument survives `Qrd`. Its footprint has one iteration, so Z's ghost is empty and `Qrd` reduces to `Qsl`.

## 2. Is the untagged reader derivable with the current logic?

**Over `EIhl`, with frozen `Isl`/`Rsl`/`Gsl`/`Osl` and `Qrd`: no.**
- (C)'s evidence, re-run here, all closed:
  - `fam_merge`: two runs that reach the same state and between them emitted every response slot force Q;
  - `rsl_step`;
  - `m24_not_stable`;
  - `doom_vacuous_after_consumption`.
- I re-traced runs R1, R3 and R5. Their record values are 2/1/1/2, 0/0/1/2 and 2/0/1/4. Their genuine-response sets cover all four value responses pairwise. All three end with `Sq_0 = 4`, `Sx_0 = Sy_0 = 1` and `A 0 = (1,1)`, and the LP value is forced to (1,1).
- Not mechanized: driving the three runs through `ctx_triple`. The argument also uses function extensionality at the meta level, because the final registers are equal only extensionally.
- Status: a rigorous argument, not a theorem.

**Over `EIhl`, for any I, R, G: argued only.**
- Ingredient 2 assumes that the simulation picks equal possibilities in schedules S_A and S_B.
- The escape through k's phase bit (`lini`/`linr`) is not excluded.
- This must not be stated as a theorem.

**Same rules over `EIhlv` (option B): derivable, by hand.** The log defeats `fam_merge`, because R1, R3 and R5 log different values for κx and κG and so end in different states.

**M-24's repair.**
- (ii) is refuted by `m24_not_stable`.
- (i) does not help against R.
- (iv) is false as stated.
- I withdraw M-24's "Required" list.

**K/S/P/R**

| Level | Content |
|---|---|
| K | The lemmas above. No negative theorem exists. |
| S | Concerns `MethodProvable` over `VE := EIhl` only. `MethodSem` (route S) is not affected. |
| P | implex.tex:3: "RLHL is complete with respect to relaxed linearizability". The paper's proof state carries the underlay trace (Appendix/programlogic.tex:537, EStep: `σ'.s = σ.s · t:e`). So the incompleteness belongs to the lossy presentation `EIhl`, not to the paper's rules. |
| R | popl2027-reviews.md:215, "No example verified on the COH model", stays unanswered until .5 lands. |

**Corrections to Writer B's text** (SL2Inv.v header, "OPEN"):
- "the limitation is in the derivation system" should read "…over the lossy `EIhl` presentation".
- The suggestion "owners of pending responses" is neither needed nor sufficient. I agree with (B) §4 on this.

## 3. Option A (tags)

### Faithfulness

- **The paper's policy produces neither tag.**
  - impl.tex:120 makes every operation except a plain read control-ordered; :131 adds κ to the tag of such an operation.
  - `rnext` has no branch before `rmb_a` or `rmb_b` in the current iteration, so neither tag comes from the policy. I agree with (A).
- **`rmb_a ← G`.** This is the control dependency of Linux's spin in `read_seqcount_begin`, with the parity test folded into `rok`. It is argued, not derived.
  - A reader that actually spins would get this tag from the policy.
  - But spinning changes `RdShape`.
  - And that tag alone does not fix the problem (§5).
- **`rmb_b ← X, Y`.**
  - No rule produces it.
  - It contradicts research-intent.md:129 ("the wait should only block the later invocation with actual data dependence").
  - It is a completion barrier. It is inert over `EI`, where values are fixed at invocation, and becomes active over any underlay that fixes values at the response.
  - Reviewer B:212 ("Insufficient justification for modeling relaxed consistency by instruction reordering") would read tags added outside the policy, so that a proof goes through, as weakening the modelling story.

### Effect on traces

- **Tagged ⊆ untagged.** Immediate, once a simulation between `run` machines that differ only in `dix` is written. It is not written yet.
- **Untagged ⊆ tagged, complete traces: the argument is correct as far as I checked.**
  - Same-thread `must_precede` (ModuleSemantics.v:252-259) blocks a response only behind its own invocation; events of other threads always cross.
  - In `EI`, a response commutes left (`ei_res_inv_commute`, closed).
  - Frontier selection is monotone (`select_sub`, `res_select_eager`, closed).
  - Every tag source is an F2 predecessor of the tagged invocation (`E_S_table`).
  - Not mechanized: module-level commutation and the `run` simulation, estimated at 2–3 days.
- **Incomplete prefixes: not covered.**
  - Removed overlay behaviour on prefixes is not excluded. A doomed untagged reader still emits its `rmb`s and unblocks a younger write on the same thread (`lb_blocking`). This is unproved either way.
  - So `RCompLin` (every prefix, the soundness notion under M-20) for `M2w` is not obtained.
  - `sl2rd_target` (`RLHL2Hyps` for `M2w`) is not obtained either. It would hold only for the tagged module `M2wT`.
  - Only `sl2rd_relin_target` (complete traces) transfers, and only once the insensitivity theorem exists.

### Effect on the SB witness and the frozen definitions

- `sb2T_exec_rd_mtraces_ij` replays and is closed. `sl2_read_overtakes_write` was not re-checked.
- `Isl`, `Rsl`, `Gsl` and `Osl` do not depend on tags.
- `Qsl` must change (B-6). `m2w_read_body`, the entry points and the target move to `M2wT`.
- (A)'s derivation sketch holds modulo B-6 and finer per-slot guarantees.

### Cost

(A)'s estimates are plausible, with one addition: the insensitivity theorem is mandatory before any claim about the untagged program.

## 4. Option B (state or presentation extension)

### Design

- `Log VE`: a state paired with a list of events.
- `EIhlv := Log (EIhl δ)`.
- `recs` = pending records followed by the records consumed by logged responses.
- `LogVal`, and `LogOK` (keys used and without duplicates).
- `SL2Inv` is reused through `liftI`, `liftG` and `liftA`.

### Soundness

- Kernel-checked:
  - `loglift`: an `MTraces` equivalence, closed;
  - `complin_log_under`;
  - `log_handle_linear`;
  - `rlhl_complin_eihlv`, whose only axiom is `classic`, as for `rlhl_complin_eihl`.
- The logic is generic in `VE`, so it is untouched.
- End to end: `RCompLin` for the untagged `M2w` over `EI δS`, for every prefix.
- Faithful to programlogic.tex:537. It is the same kind of move as `HL` (decisions M-16 and M-20).

### Sufficiency for the reader

I re-traced (B) §3 by hand. With B-6 fixed it holds.
- `V(κ, o, v)` facts are monotone (`logval_step`) and unique per key (`logval_unique`).
- `logval_res` pins response values. In fact a response's `fin` follows from its own logged event, with no precondition needed.
- `Pkg` travels κB → κT inv → κT res. The identification happens at `bw_sum` through `sl_logval_rd`.
- When the rely consumes a reader record, the log records the same value, so this is harmless.

Obligations still open:
- B-6;
- response-slot guarantees must keep the possibility unchanged; `isl_response` already does (SL2Inv.v:1468);
- `G'` must include the `Log` step: `evupdate_lift` currently yields only `liftG g`, and needs a trivial variant;
- m-52 and m-53;
- a new target over `EIhlv`, because `sl2rd_target` (SL2Prog.v:1125) fixes `EIhl`. So (B)'s "SL2Prog untouched" holds only if the new target lives elsewhere.

### Generality

- **What it fixes.** It removes the incompleteness that the presentation causes for programs that validate after reading: the SeqLock, the LatchSet reader (whose designs already assume the value at return), double-collect snapshots, and optimistic concurrency control.
- **What it is.** It is the history half of auxiliary variables (Owicki–Gries; Abadi–Lamport).
- **What it does not fix.**
  - Prophecy is still absent: invocation slots cannot see future responses (m-36, LPs that depend on the future under a single possibility).
  - implex.tex:3 stays ⚠️.

### Cost

(B)'s estimates are plausible. About 180 lines of the infrastructure are already kernel-checked.

### Response ownership

Ownership of responses is neither needed nor sufficient alone, and it would disturb the lazy placement of responses. I agree with (B) §4.

## 5. Other options

- **(C)'s variant: `rmb_a ← G` and `T ← X, Y`.** It works by my re-trace: the edge from κx's invocation to its response can carry `KRec p → fst p = rx ∨ s < Sq_i ∨ odd s`. But T is a plain read, so the tag has no policy basis. Same verdict as (A).
- **(C)'s `EIhv`** (`used` stores full records). It carries the same information as (B)'s log but changes the state shape of `EIhl`, so `SL2Inv` would have to be re-instantiated. (B)'s generic wrapper is preferable. (C)'s cost row "changes frozen definitions" applies to `EIhv`, not to (B).
- **`rmb_a ← G` alone**, the only tag a spinning reader justifies: insufficient, because a and c remain untagged.
- **Logic level:**
  - `bw_sum` with `NoOwn`, which fixes B-6 generically;
  - a single theorem making `Log ∘ HL` the default presentation for every RLHL instance.
- **Route S:** excluded by the author. `MethodSem` is not affected by this obstruction.

## 6. Recommendation

The author is choosing between two routes. Both need the B-6 fix.

**(i) Option B.**
- **What is verified:** the reader exactly as written, over `EIhlv`.
- **What changes:**
  - Addendum 2's chain becomes `method_sound` → `RLHL2Hyps(EIhlv)` → `rlhl_complin_eihlv` → `cc_rel_lin`;
  - the target is restated over `EIhlv`.
- **What may be claimed:** "an RLHL derivation for the reader as written, over a presentation that carries the underlay history, as in the paper's proof state". `RCompLin` holds for every prefix.
- **What must be recorded:** an incompleteness datum for `EIhl`, in the implex.tex:3 / m-36 rows.

**(ii) Option A, plus the insensitivity theorem.**
- **What is verified:** a tagged program over `EIhl`.
- **Consequences:**
  - that program is outside the image of the policy in impl.tex:120 and violates research-intent.md:129;
  - for the untagged program the result covers complete traces only;
  - the plan's "no dependency tags anywhere" (§2.3) and "tags question moot" (§5) become false;
  - the SeqLock cannot be cited for completeness.

**Either way:**
- do not claim "RLHL is complete";
- do not state that the untagged reader is underivable over `EIhl` as a theorem.

**My recommendation: (i).**

## 7. Findings

### BLOCKER
- **[B-6] The frozen read postcondition `Qsl` cannot be reached at `Close` on paths whose iteration count disagrees with the ghost** (actionable).
  - The premises of `sl2_read_run_provable`, `sl2rd_rlhl2_of_methods` and `sl2rd_target_of_methods` cannot all hold.
  - This affects both (A) and (B).
  - Fix: §1.3.

### MAJOR
- **[M-24] (carried, status change).** The repair (i)–(iv) is refuted by `m24_not_stable`. M-24 is superseded by M-25.
- **[M-25] (new, research-level).** The untagged reader cannot be derived over `EIhl` (argued). The decision between (A) and (B) goes to the author.
- **[M-26] (new; research-level if (A) is chosen).**
  - (A) transfers to the untagged module for complete traces only.
  - It does not establish `RCompLin` or `sl2rd_target` for `M2w`.
  - The insensitivity theorem is not mechanized.

### MINOR
- **[m-58] The "OPEN" section of the SL2Inv header is inaccurate** (actionable). It says the limitation is in the derivation system, and it offers ownership as option (b). Correct it after the decision.
- **[m-59] (B) still needs two small pieces** (actionable): a variant of `evupdate_lift` that carries the `Log` step, and a note that `sl2rd_target` over `EIhl` is superseded.

## 8. Record corrections

- **Concern matrix row 69 (implex.tex:3).** Stays ⚠️. Add the datum: "untagged validate-after-read is not derivable over `EIhl` (argued); the history presentation removes this (hand-checked)".
- **Concern matrix, row for B:215.** Stays open. Task .5 is blocked by B-6 and by the decision.
- **latest-review M-24.** Mark it refuted and superseded.
- **Plan RLHL-seqlock.md.**
  - The read-value edge at :113-116 is false.
  - §2.3 ("no dependency tags anywhere") and §5 ("tags question moot") hold under (B) and are false under (A).

## 9. Feasibility checks (output)

- **Build:** `make -n` on SL2Inv.vo and SL2Exec.vo: "is up to date".
- **(C) §7 script, verbatim:**
  - `fam_merge`: Closed under the global context.
  - `doom_vacuous_after_consumption`: Closed under the global context.
  - `m24_not_stable`: Closed under the global context.
- **(B) §7 script, verbatim:**
  - `log_handle_linear`, `loglift`, `logok_step`, `logval_step`, `logval_res`, `logval_inv`, `sl_logval_rd`, `stable_lift`, `evupdate_lift`: Closed under the global context.
  - `rlhl_complin_eihlv`: Axioms: `Classical_Prop.classic`.
- **(A) §6 script:** run in four stdin batches, Coq text unchanged, including the sed extraction from SL2Exec.v:521-546 and :548-641. All closed:
  - `rdT_prod`, `rdT_retry_prod_gen`, `rdT_tags`;
  - `sb2T_exec_rd_mtraces_ij`;
  - `res_select_eager`, `select_sub`, `ei_res_inv_commute`.
- **New script (B-6), complete.** Output: four times "Closed under the global context".

```coq
From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareDag models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLinSpec models.simlin.RelaxedHoareRun.
Require Import examples.Relaxed.RelaxedHoareSL2Prog examples.Relaxed.RelaxedHoareSL2Inv.
Import ListNotations LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedModuleSemantics RelaxedPossibility RelaxedHoareCompLinSpec RelaxedHoareBase RelaxedHoareDag RelaxedHoareRun RelaxedHoareSL2Prog RelaxedHoareSL2Inv.
Lemma owns_rmb_not_qsl rc si tw k i r s :
  Isl rc si tw s -> Owns rc si k isRmb (ps_ghost s) -> ~ Qsl rc si k (fR i) r s.
Proof.
  intros (A & Pf & P & Hp & _ & HC) Hown (A' & Pf' & P' & Hp' & Hq).
  rewrite Hp in Hp'. injection Hp' as <- <- <-.
  destruct Hq as [Hl | [Hl _]];
    pose proof (ic_coup _ _ _ _ _ _ _ _ HC _ Hl) as Hc;
    unfold Coup in Hc; rewrite lin_key_make_lin_entry in Hc; cbn in Hc;
    apply Hc in Hown; discriminate Hown.
Qed.
Module Mismatch.
  Definition rc := true.
  Definition si : FOp -> FOp -> Prop := fun _ _ => False.
  Definition tw : nat -> tid := fun _ => 2%positive.
  Definition t : tid := 1%positive.
  Definition k : CallKey (F2 si) := (t, 0).
  Definition hs1 : nat * nat * nat * nat * nat * nat := (0, 1, 2, 3, 4, 5).
  Definition hs2 : nat * nat * nat * nat * nat * nat := (6, 7, 8, 9, 10, 11).
  Definition evs := flat_map (rd_iter rc t 0) [hs1; hs2].
  Definition P : LinPool (F2 si) := [make_lin_entry k (@ls_inv (F2 si) (fR 0))].
  Definition VE := EIhl (E := E_S rc) δS.
  Definition VF := RelaxedHoareSpec.EI (F := F2 si) δF.
  Definition s0 : PState VE VF :=
    (((regs0, []), []), @PossOk (F2 si) VF (A0, []) P, map (Build_ScheduledEvent k) evs).
  Lemma pinit0 : PostInvoke (Isl rc si tw) k (fR 0) (Osl rc tw t (fR 0) 0) s0.
  Proof.
    exists (@PossOk (F2 si) VF (A0, []) []), [], evs. split; [exact (isl_init rc si tw) |].
    split; [constructor; constructor; intros [] |].
    split; [reflexivity |]. split.
    - cbn. exists [hs1; hs2]. split; [discriminate |]. split; [| reflexivity].
      cbn. repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    - cbn. repeat constructor.
  Qed.
  Lemma islc0 : IslC rc si tw regs0 A0 [] P (map (Build_ScheduledEvent k) evs).
  Proof.
    constructor.
    - unfold lin_pool_well_formed, lin_domain. cbn. constructor; [intros [] | constructor].
    - split.
      + intros e He. apply in_map_iff in He as (x & <- & _). cbn. left. reflexivity.
      + intros i j e1 e2 H1 H2 Ho. exfalso. cbn in Ho. unfold key_older in Ho.
        inversion Ho; subst; repeat match goal with H : subseq _ [] |- _ => inversion H; clear H end;
        repeat match goal with H : subseq _ (_ :: _) |- _ => inversion H; clear H; subst end.
    - cbn. repeat constructor.
    - intros o [].
    - constructor.
    - intros e [<- | []]. cbn. split; [intros _ | reflexivity].
      exists (Build_ScheduledEvent k (IE rc t 1 sRmb)). split; [cbn; tauto |]. split; reflexivity.
    - intros e i vx vy [<- | []] H. discriminate.
    - intros i k1 k2 (vx & vy & ls & Hl & Hop). exfalso.
      destruct Hl as [Hl | []]. unfold make_lin_entry in Hl. injection Hl as _ _ Hls. subst ls. discriminate.
    - intros i _. reflexivity.
    - intros i He. discriminate.
    - cbn. repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
  Qed.
  Lemma isl0 : Isl rc si tw s0.
  Proof. exists A0, [], P. split; [reflexivity |]. split; [intros x [] | exact islc0]. Qed.
  Lemma owns_after_iter1 : Owns rc si k isRmb (map (Build_ScheduledEvent k) (rd_iter rc t 0 hs2)).
  Proof. exists (Build_ScheduledEvent k (IE rc t 7 sRmb)). split; [cbn; tauto |]. split; reflexivity. Qed.
  Lemma rok00 : rok 0 0 = true. Proof. reflexivity. Qed.
End Mismatch.
Print Assumptions owns_rmb_not_qsl.
Print Assumptions Mismatch.pinit0.
Print Assumptions Mismatch.isl0.
Print Assumptions Mismatch.owns_after_iter1.
```

**Not mechanized:**
- the 12-step `fam_emit` run of B-6, step 3;
- (C)'s three-run construction;
- (A)'s module-level insensitivity theorem;
- the derivations sketched in (A) and (B).