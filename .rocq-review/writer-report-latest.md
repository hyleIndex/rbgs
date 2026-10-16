## Writer report — RLHL-seqlock final cleanup (M-29, m-65 to m-70)

### Summary
Every item that the final review marked actionable is done, except m-54, which was optional and is not cheap. New Rocq declarations sit at the ends of their files (SL2Prog: one lemma after `E_S_table`). One `Require` line was added to SL2Read. All other edits are comment edits. I compared every touched file, with comments stripped, against a backup taken before editing. Each diff has 0 removed lines; the only additions are the new declarations and the `Require` line. The full build passes, except `structures/DCPOs.v`, which is the known baseline failure.

Items I added beyond the brief, all small: `ov_exec`, `ov_rel_lin` (for every relation), `sbo_complete`, `sl2_rel_lin_unguarded` and `sbo_not_trace_rd`. I also applied the m-66 wording fix to SL2Inv.v, where the same sentence pattern appears.

### Files changed
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Prog.v`
  - New lemma `sindep_rc_vacuous` (:391).
  - Header first paragraph rewritten for m-70: "one object with N SeqLock instances over one shared memory; cross-instance order comes from the shared barriers, not from the tensor ⊗ (relaxedlin.tex:191)". The Part 2 title comment says the same.
  - Part 1 and Part 7 map entries and the comment before `sl2_read_overtakes_write` now cite `RelaxedHoareSL2Exec.ov_rel_lin_empty` and `ov_exec` instead of "scratch file".
  - Scope paragraph on `rc` now cites `sindep_rc_vacuous`.
  - P1 paragraph now cites `sl2_complin_unguarded`.
  - P paragraph: added the M-29 sentence.
  - K count changed from 55 to 56.
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Exec.v`
  - New Part 7 (:1793 onwards): `ov_trace`, `ovW`, `ovR`, `ov_exec`, `ov_inv_cases`, `ov_res_idx`, `ov_rel_lin`, `ov_rel_lin_empty`, `sbo`, `sboWi` and the other five `sbo*` operation records, `sbo_sub`, `sbo_complete`, `sbo_not_rel_lin`.
  - The `sbo_not_rel_lin` proof is the review script with the helper records renamed from `oWi` and so on to `sboWi` and so on.
  - Header: Part 7 added to the map; M-29 sentences added to P and R; K count changed from 68 to 76.
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Read.v`
  - `Require models.simlin.RelaxedHoareResig.` (:269).
  - New Part 10 (:1586 onwards): `rlhl2_v_of_reads_inst`, `sl2_complin_unguarded`, `sl2_rel_lin_unguarded`, `sl2_no_mp`, `sbo_not_trace_rd`.
  - Header:
    - Main results: Part 10 added.
    - K: 72 closed out of 79.
    - S: M-29 bullet and the P1-precondition pointer.
    - P: m-66 wording, and EStep renumbered to :579 with the commit named.
    - R: added "no evidence about TSO, ARMv8, oMCA or store forwarding".
    - Limitations: m-65 prophecy wording, and the dependency on Exec and Resig.
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Write.v`, comments only:
  - map (:42 onwards) and S (:166 onwards) now cite `RelaxedHoareSL2Read.rlhl2_v_of_reads_inst`;
  - P: m-66 wording, anchors :488 and :537 changed to :530 and :579, commit named.
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2InvLog.v` (:213-215): anchors :488, :537, :507 changed to :530, :579, :549; commit named.
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Inv.v`:
  - :183-187: m-66-style rewording ("mechanized RLHL of [RelaxedHoare]; printed rules differ and have no ghost; M-21, m-66");
  - :235-237: anchors renumbered, commit named.
- `/Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareCounterXY.v` (:274): :516 changed to :558; commit named. :308 is unchanged between the two commits.
- `/Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoare.v`:
  - The note (:124-133) now says lines are numbered as in 4a2db8e1, with the mapping back to 01484091.
  - Every anchor of :469 or later in the M-21 table, and at :244, :251 and :289, is renumbered by +42. All are three-digit to three-digit, so the table stays aligned.
  - The single-possibility row is rewritten for m-65.
- `/Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareLog.v`:
  - :42-47 and :184: anchors changed to :530, :579, :549;
  - note at :51-53 now names 4a2db8e1;
  - :55-70: m-65 prophecy paragraph rewritten.
- `/Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareGSim.v` (:203-206, :338-348): commit named; anchors changed:
  - 498-505 to 540-547;
  - 492-496 to 534-538;
  - 479-482 to 521-524;
  - 503 to 545;
  - 509 to 551;
  - 476-557 to 518-599.
- `/Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareDag.v` (:32): commit named. :302-308 is the same in both commits.

### New / changed statements
**SL2Prog**
- `RelaxedHoareSL2Prog.sindep_rc_vacuous`: `forall o o', sindep true o o' <-> sindep false o o'`. Supports m-68 and M-28(1).

**SL2Exec**
- `RelaxedHoareSL2Exec.ov_exec rc si tw t`: `tw 1 = t -> MTraces (EI δS) (M2w rc si tw) (regs0, []) (ov_trace si t) /\ PrefixView.complete (ov_trace si t)`.
- `ov_rel_lin si indep t`: `rel_lin (sel (F2 si)) (ov_trace si t) indep (seq_legal δF A0)`.
- `ov_rel_lin_empty si t`: the same at `indep := fun _ _ => False`. Supports m-68.
- `ov_inv_cases` and `ov_res_idx`: helper lemmas.
- `sbo_sub` and `sbo_complete si t1 t2 : PrefixView.complete (sbo si t1 t2)`.
- `sbo_not_rel_lin si indep t1 t2`: `(forall o o', indep o o' -> slRA o o') -> ~ rel_lin (sel (F2 si)) (sbo si t1 t2) indep (seq_legal (F := F2 si) δF A0)`. Supports M-29.

**SL2Read**
- `RelaxedHoareSL2Read.rlhl2_v_of_reads_inst rc si tw (Hsi : slRA ⊆ si)`: `RLHL2Hyps (liftIV δS δF (Isl rc si tw)) (liftGLk (Rsl rc si)) (liftGLk (Gsl rc si)) (M2w rc si tw) ((((regs0, []), []), [])) (A0, [])`. Supports m-68.
- `sl2_complin_unguarded rc si tw s`: `slRA ⊆ si -> MTraces (EI δS) (M2 rc si) (regs0, []) s -> P1 tw s -> RTraces (EI (F := F2 si) δF) (A0, []) s`. Supports m-69 and M-28(d).
- `sl2_rel_lin_unguarded rc si tw s`: `slRA ⊆ si -> MTraces … (M2 rc si) … s -> P1 tw s -> complete s -> rel_lin (sel (F2 si)) s si (seq_legal δF A0)`.
- `sl2_no_mp rc si tw s`: `MTraces (EI δS) (M2w rc si tw) (regs0, []) s -> complete s -> ~ RelaxedHoareSL2Exec.mp_shaped s`. This holds for every `si`, with no hypothesis. That is stronger than the brief's "every si ⊇ slRA". The proof moves the trace to `slRA` with `mtraces_resig_iff`, `complete_resig` and `rel_lin_resig_seq`. Supports m-69.
- `sbo_not_trace_rd rc si tw t1 t2`: `~ MTraces (EI δS) (M2w rc si tw) (regs0, []) (sbo si t1 t2)`, for every `si`. Supports M-29.

No existing statement changed.

### Semantic/assumption changes
None.
- No existing definition, statement or proof was edited. The comment-stripped diff against the pre-edit backups shows 0 removed lines in all 11 changed files.
- The added `Require models.simlin.RelaxedHoareResig.` in SL2Read is already a transitive dependency through SL2Exec, so it adds no new dependency.
- No new axioms were introduced.

### Build
- Command: `export PATH=/opt/homebrew/bin:$PATH; make -k -j4` (Rocq 9.3.0).
- All touched files and their dependents were rebuilt: RelaxedHoare, Sound, GSim, CompLin, CompLinSpec, Inherit, Layer, ErrSpec, Checks, Absorb, LockErr, Run, Ready, Log, LatchProg, CounterXY, Resig, ClientSB, and SL2Prog, SL2Inv, SL2InvLog, SL2Write, SL2Exec, SL2Read.
- The only error is `structures/DCPOs.v`, line 488: "Syntax error: [record_fields] expected after '{'". That is the baseline failure.
- After the build, `make -n -k` lists only `structures/DCPOs.v`.

### Print Assumptions
- Closed: `sindep_rc_vacuous`, `ov_exec`, `ov_inv_cases`, `ov_res_idx`, `ov_rel_lin`, `ov_rel_lin_empty`, `sbo_sub`, `sbo_complete`, `sbo_not_rel_lin`, `rlhl2_v_of_reads_inst`.
- {classic}: `sl2_complin_unguarded`.
- {classic, eq_rect_eq}: `sl2_rel_lin_unguarded`, `sl2_no_mp`, `sbo_not_trace_rd`.
- Unchanged:
  - `sl2_main`: closed;
  - `sl2_complin`: {classic};
  - `sl2_rel_lin` and `lb2_not_trace_rd`: {classic, eq_rect_eq};
  - `rlhl_gsim`: closed;
  - `rlhl_complin_eihlv`: {classic}.
- Batch over every Lemma/Theorem/Corollary of each file:

  | File | Declarations | Closed | With axioms |
  |---|---|---|---|
  | SL2Prog | 56 | 56 | 0 |
  | SL2Exec | 76 | 67 | 9 {classic, eq_rect_eq} |
  | SL2Read | 79 | 72 | 2 {classic}, 5 {classic, eq_rect_eq} |
  | SL2Write | 61 | 61 | 0 |

  These counts match the updated headers.

### Gap check (K / S / P / R)
- **M-29:**
  - K checks the trace-level negative `sbo_not_rel_lin` and that the MCA module does not produce `sbo` (`sbo_not_trace_rd`).
  - That x86-TSO and ARMv8 produce `sbo` for the SeqLock is argued only. Every header says so.
  - The author part, "Scope = oMCA" versus RD-8, is untouched.
- **m-65:**
  - The wording now matches the review.
  - The relaxedlin anchors are Appendix/relaxedlin.tex:520 and :628. The top-level relaxedlin.tex is a different file; I cite its :191 only for ⊗, in m-70.
  - The Log.v sentence on "LPs that depend on other calls' future behaviour … not covered" is a description, not a theorem.
- **m-67:**
  - I chose to renumber to 4a2db8e1 everywhere, naming the commit once per file.
  - The exact fact, checked by line comparison: lines of :469 or later at 01484091 are +42 at HEAD. :466 is edited in place, and :467-468 keep their numbers. The review's "from :466 on" is slightly off, but no anchor falls in :466-468.
  - Run.v and Base.v cite only lines below :466, which are identical in both commits, so I left them unchanged.
- **m-70:** the headers now describe the object correctly. The optional lemma "slRA = I_cross" is not done.
- **m-69:** `sl2_no_mp` covers every `si`, not only `si ⊇ slRA`.

### Responses to reviewer findings
- **M-29 (actionable part): FIXED.**
  - SL2Exec.v:1899-1984 has `sbo`, `sbo_complete` and `sbo_not_rel_lin`.
  - SL2Read.v:1649 has `sbo_not_trace_rd`.
  - The sentence is in SL2Prog (P), SL2Read (S, R) and SL2Exec (P, R, Part 7).
  - The author part is untouched; it needs the authors (NEEDS-AUTHOR).
- **m-65: FIXED.** RelaxedHoare.v single-possibility row (:216-232), Log.v:55-70, and SL2Read Limitations.
- **m-66: FIXED.** SL2Read P, SL2Write P, and the same pattern in SL2Inv:183-187.
- **m-67: FIXED.** Renumbered to 4a2db8e1, with the commit named in RelaxedHoare, Log, GSim, Dag, CounterXY, SL2Read, SL2Write, SL2InvLog and SL2Inv.
- **m-68: FIXED.** `sindep_rc_vacuous`, `ov_rel_lin_empty` (with `ov_exec`) and `rlhl2_v_of_reads_inst` are in the build. No "scratch file … outside the build" phrase remains in `examples/` or `models/`.
- **m-69: FIXED.** `sl2_no_mp` (every `si`), `sl2_complin_unguarded` and `sl2_rel_lin_unguarded`.
- **m-70: FIXED** for the wording, in the SL2Prog header and the Part 2 title. The slRA = I_cross lemma is DEFERRED; the review marked it optional.
- **m-54: DEFERRED.** It is not cheap. It needs a "fewer tags" relation on coinductive `Prog` bodies and a simulation through `program_produces_tagged` and `must_precede` in the tagged module semantics. M-28(g) stays open.

### Open issues / risks
- The author decisions M-28 and M-29 are not addressed.
- The records still need the orchestrator's changes, which I did not edit (`.rocq-review/` was out of bounds): M-23 residue at research-intent.md:178 and :165, and the concern-matrix updates.
- The task brief's "si ⊆ slRA" wording is rendered in the headers as "any relation contained in [slRA]". This matches the Coq hypothesis `indep ⊆ slRA`.