# Research review: iteration 2 (confirmation), 2026-10-13 (task T-1)

## Scope
- **Repository state.** `relaxed-lin`, HEAD `6e2b575`, all uncommitted.
  - `/Users/index/Documents/GitHub/rbgs/examples/Relaxed/FuturesShape.v` (602 lines) and `/Users/index/Documents/GitHub/rbgs/examples/Relaxed/SeqLockTowerProg.v` (1118 lines) are byte-identical to the `*.it2.v` snapshots.
  - `_CoqProject` still differs from `_CoqProject.preT1` by exactly the two T-1 lines.
- **Delta against `*.it1.v`.**
  - FuturesShape: header only.
  - SeqLockTowerProg:
    - header;
    - `lc_ok`, `lc_ok_uc0`, `lc_ok_inv`, `sindep0_lpres`, `sindep0_lpres_junk`;
    - the decoding section (`pw`, `pr`, `parse0`, `parse0_lcalls`, `lpi0`, `wcall0`, `M0_window_index` / `_first_wmb` / `_last_iter`, `res_find0`, `decode0`, `decode0_spec`);
    - `M0_shape_decoded`;
    - one added `res_list0` conjunct in each of `M0_write_produces` and `M0_read_produces`;
    - `M0_read_block`, `M0_write_block`, `res_list_SLP`, `M_shape_via_FS`.
- **Findings re-checked.** m-59 (one sub-point disputed), m-60 … m-64. M-18 is closed by the author and not re-raised.

## Checks I ran
- **Protected files.** `shasum -c T1_base.sha`: all 8 files OK.
- **Build.**
  - `make -n` reports both targets up to date; each `.vo` (18:57) is newer than its `.v` (18:45 / 18:46).
  - `make -n -k` lists only `structures/DCPOs.v`.
  - Replaying both sources with `Load` in `rocq repl` 9.3.0 gives 0 errors.
- **Forbidden constructs.** `grep` for `Admitted|admit|Axiom|Parameter|Unset|vm_compute|native_compute|Hypothesis|Variable|Transparent|Opaque` finds nothing in either file.
- **Print Assumptions.** All 85 Lemma/Theorem/Corollary/Example declarations (55 + 30) are "Closed under the global context".
- **Regressions.** `diff it1 it2` shows that the only changed hunks in existing declarations are the two Example statements, each with one appended `res_list0` conjunct, and their final `split`s. Every other hunk is an addition or a header change. `M0_shape` and all iteration-1 lemmas are unchanged.
- **Statements.** `Check` of `parse0_lcalls`, `M0_window_index`, `M0_window_first_wmb`, `M0_window_last_iter`, `sindep0_lpres`, `decode0_spec`; the read/write block Examples, `M0_shape_decoded` and `M_shape_via_FS` I read in the diff.
- **Header claims, by `Eval`.**
  - `ST.lcat C (LD (SL.GT 0))` equals `TL.k_get C` for both `plainC` (`Acc KR false false`) and `rcC`, and it differs from `k_inc plainC` (`Acc KRW …`).
  - `Check SeqLockCOH.paper_modes_fail` gives `forall rc, ~ Conclusion … (setting paper_cf_modes rc plainTL X_lb)`.
- **Paper lines cited in the header.**
  - Appendix/SeqLock.tex:7 is `import owner : Counter`, :8 is `import next_ticket : TSO`, :29 is `import x, y : TSO`, and the listing spans :5–45.
  - figures/SeqLock.tex:29–56 holds the `M_Counter^TSO` / `M_Counter^RC` boxes; no `.tex` file inputs it.

## Verdict
Iteration 2 closes m-59 through m-64 and adds the decoding infrastructure that T-3 would need. There are no regressions, and every new statement is stated only on well-formed input. The only thing left is a one-sentence wording fix (m-65 below), which is not blocking. **The T-1 loop can stop.** T-1 is finished infrastructure.

## Findings
### BLOCKER
None.

### MAJOR
None. M-18 was closed by the author's decision of 2026-10-13 and is not re-raised.

### MINOR
- **[m-59] Closed.** The header now has two paragraphs: "Scope of the tower" (the Counter is not inlined, and the Counter layer is outside T-1..T-3), and "Differences from the paper's printed code". Every line number cited there is correct. The disputed sub-point is resolved in the Writer's favour (see the disputes section).
- **[m-60] Closed.**
  - Both Examples now state the full `res_list0` with values.
  - `M0_read_block` and `M0_write_block` prove that every `k, cs` meeting M0_shape's conjuncts on that trace equals `LBR [(1,0,0,0)] 2 1 1` (resp. `LBW 1 1 2 [0]`). The conjuncts used are `lcalls`, inv, NoDup, Perm and `silent_r0`, and the Examples take no `blk_ok`, `spin_ok` or `blk_matches` premise, so they are stronger than needed.
  - They also prove that `parse0 (map snd (decode0 …))` is that block.
  - The `silent_r0` premise is necessary, not convenient: without it, `LBR [(1,0,0,5)] 2 1 1` would also qualify (my iteration-1 probe 1).
- **[m-61] Closed.**
  - `parse0_lcalls : silent_r0 k = true -> parse0 (lcalls k) = k` holds for every block, not only `blk_ok` ones.
  - The header now says the conjunct is needed and why.
- **[m-62] Closed.**
  - `M_shape_via_FS` has exactly `SeqLockProg.M_shape`'s type, built with `ltac:(type of …)`. It is Closed.
  - The FuturesShape header records that the duplication is deliberate.
  - Nit: the section comment at SeqLockTowerProg.v:1100–1101 says "from exec_shape and M_calls alone", but the proof also uses `res_list_SLP` and `inv_list_SLP`. The file header at :172–175 names `res_list_SLP` correctly.
- **[m-63] Closed.** The header now states:
  - the structural condition: every multi-call TicketLock operation is waited immediately, and the only un-waited TicketLock future (`rel`) is a single call;
  - that a non-waited multi-call method could not be inlined without a fork construct;
  - that `RelaxedLang` has no inlining or substitution operator, so no theorem relates `M0` to a module composition;
  - that the CPS `acq k` equals the `bindProg` form only up to bisimulation.
- **[m-64] Closed.**
  - `sindep0_lpres` is the iff restricted to `lc_ok` calls.
  - `lcalls_lc_ok` shows every call of a block is `lc_ok`.
  - `sindep0_lpres_junk` is a kernel-checked counterexample showing the unrestricted iff is false. The header's explanation of it matches the `Eval` results.
- **[m-65] New. Wording: "refuted" needs its qualification.** (actionable, one sentence)
  - **Where:** SeqLockTowerProg.v:38–39: "the fence modes printed for the SeqLock are refuted ([SeqLockCOH.paper_modes_fail])".
  - **K/S/P:** `paper_modes_fail` refutes `paper_cf_modes` on the load-buffering execution `X_lb` of the COH + barrier variant with `plainTL`. The paper prints the modes for a TSO SeqLock with no barriers. TSO forbids load buffering, so this refutation does not transfer to that object without further argument. The concern matrix's C1 row already words it correctly: "refuted for the COH barrier variant".
  - **Required:** add "for this COH variant with barriers (on the LB execution `SeqLockCOH.X_lb`)". This does not block stopping the loop.

### New statements: correctness and scope (item a)
| Statement | Assessment |
|---|---|
| `parse0_lcalls` | Correct. Premise `silent_r0` only. Works for any block, with or without `blk_ok`. Junk outputs (`LBZr 0`; `pr`'s fallbacks) are never reached on `lcalls k`. |
| `decode0_spec` | The same proof as `SeqLockModule.decode_spec`, with exactly M0_shape's inv / NoDup / Perm premises. `decode0`'s junk value (`LT IncO`) cannot be reached under those premises. |
| `M0_shape_decoded` | M0_shape's nine conjuncts at `cs := decode0 …` and `k := parse0 (map snd cs)`. It is the analogue of `produced_shape`, and it uses `silent_r0` to rewrite through `parse0_lcalls`. |
| `M0_window_index` | Total. Write: index `length sp + 3` is `LD WmbC`. Read: index `length (flat_map literq its) + 1` is `LD RmbC`. These are the windows `SeqLockModule` uses (first wmb; first rmb of the last iteration). |
| `M0_window_first_wmb` | "First" is proved: there is no `WmbC` at any smaller index. |
| `M0_window_last_iter` | The index just before the window is the last iteration's `get_ticket`. With `M0_window_index`, this fixes "first rmb of the last iteration". |
| `sindep0_lpres`, `sindep0_lpres_junk` | Correct and suitably restricted. The counterexample is kernel-checked. |
| `M0_read_block`, `M0_write_block` | Correct, with minimal premises (see m-60). |
| `M_shape_via_FS` | Exactly `M_shape`'s type. Closed. |

None of these mentions `rel_lin`, a module execution or an underlay specification. They are facts about one method trace and about SeqLockTower's model, as the header says.

## Responses to Writer disputes
- **m-59, the claim that "the paper inlines the Counter via its faa/rd code". I accept the dispute.**
  - Appendix/SeqLock.tex:7 reads `import owner : Counter`.
  - The faa/rd code is the Counter's own implementation layer (figures/SeqLock.tex:29–56, the `M_Counter^TSO` / `M_Counter^RC` boxes). The same figure states that "upper proofs see only spec{Counter}", and no `.tex` file currently inputs that figure.
  - So the paper's listing, like `M0`, keeps the Counter as an object. My iteration-1 wording was wrong.
  - The real gap is that the Counter layer is missing from the tower, against the "Counter → TicketLock → SeqLock" flagship. The new "Scope of the tower" paragraph now states it.

## Concern-matrix corrections
- **Row T-1.** Status 🟡 → 🟢 (closed).
  - K: 85/85 Closed; replay OK; protected files unchanged.
  - Add to the description: `parse0_lcalls`, `decode0_spec`, `M0_shape_decoded`, `M0_window_*`, `sindep0_lpres` (on `lc_ok` calls), `M0_read_block` / `M0_write_block`, `M_shape_via_FS`.
  - Replace "T-3 needs decoder `parse0`, block-dependent windows" with what T-3 would still need:
    - `wsel` / `window_at` / `window_bodies` analogues over `lpi0` / `wcall0`;
    - `E_compat` from `sindep0_lpres`;
    - the `SX`-style construction of an `Exec0` and its `WF0` / `BWF0`;
    - `positional` via `tower_link`.
  - Mark T-2/T-3 as deprioritized (author, 2026-10-13).
  - Optional: carry m-65 as a one-line header wording fix.
- **Row C1.** Unchanged. trace.tex:393–395 still prints the modes; the refutation applies to the COH variant with barriers, as the row already says.

## Stronger or alternative approaches
Nothing further for T-1. If T-3 is resumed, `M0_shape_decoded` together with `M0_window_index` gives it what `SeqLockModule.window_at` and `window_bodies` need, with no further work on the program side.

## Redesign assessment
No redesign is needed. T-1 is complete as infrastructure, and the loop can stop. The m-65 wording fix can go in with any later edit.
