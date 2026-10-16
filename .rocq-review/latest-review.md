<!-- RLHL-seqlock final review (2026-10-15), saved verbatim by the orchestrator. Produced by the review workflow (three rocq-research-reviewer lenses, a skeptic per lens, a synthesis). -->

# Research review — RLHL-seqlock final — 2026-10-15

## Scope
- **Repository:** `/Users/index/Documents/GitHub/rbgs-rlhl`, branch `rlhl`, HEAD `6aef511`. All RLHL work is uncommitted and builds. `make -n` leaves only `structures/DCPOs.v`, which is the known baseline failure.
- **Paper:** async-ccal HEAD `4a2db8e1` ("sec3", 2026-10-15 22:34). Its `drafts/relaxed-lin` tree is clean, so the "working tree" equals HEAD.
- **Under review:** waves 4-5 and the docs pass:
  - `examples/Relaxed/RelaxedHoareSL2Write.v`, `RelaxedHoareSL2InvLog.v`, `RelaxedHoareSL2Read.v`;
  - the `RelaxedHoareSL2Exec.v` additions;
  - comment-only edits in SL2Prog, `models/simlin/RelaxedHoare.v` (m-64 delta rows), SL2Inv, Log, Run, SL2InvLog, SL2Write and SL2Exec.
- **Concerns:** popl2027-reviews.md B:215, B:212, B:309-316 (B-1), B4 :533, B5 :537, meta :615. Carried findings: M-23, M-25, m-33, m-51, m-53…m-64.
- **Method:** this report merges three lens reviews (soundness/fidelity; K/S/P/R and author decisions; non-vacuity and RLHL2 readiness) and their verifications. I re-checked the points where the lenses differed.

## Checks I ran
All checks were read-only: `PATH=/opt/homebrew/bin:$PATH`, Rocq 9.3.0, piped `rocq repl` with the `_CoqProject` `-R` flags. I wrote no files.

**Statements (`About` / `Print`)**
- `sl2_main : sl2rd_prov_target_v`, with `Arguments sl2_main rc si tw _`.
- `sl2rd_complin_target` = ∀ rc si tw, (slRA ⊆ si) → `RCompLin (M2w rc si tw) (EI δS) (regs0, nil) (EI δF) (A0, nil)`.
- `sl2rd_relin_target` = ∀ rc si tw s, slRA ⊆ si → `MTraces (EI δS) (M2w rc si tw) (regs0, nil) s` → `PrefixView.complete s` → `rel_lin sel s si (seq_legal δF A0)`.
- `lb2_not_trace_rd` = ∀ rc si tw t1 t2, ¬`MTraces (EI δS) (M2w rc si tw) (regs0, nil) (lb2_trace si t1 t2)`.
- None of these has a section hypothesis. All concern the original untagged `M2w` over plain `EI δS`, not EIhlv and not a tagged variant.

**Print Assumptions**

| Result | Axioms |
|---|---|
| `sl2_main`, `read_provable_v`, `RelaxedHoareSL2Write.write_provable` | none (closed) |
| `sl2_complin` | `classic` |
| `sl2_rel_lin`, `lb2_not_trace_rd` | `classic`, `eq_rect_eq` |

The lens batch runs give the same picture:
- SL2Read: 71 closed, 1 {classic}, 2 {classic, eq_rect_eq}.
- SL2Write: 61 closed.
- SL2Exec: 59 closed, 9 {classic, eq_rect_eq}.
- SL2InvLog: 112 closed, 4 inherited.
- No other axiom appears.

**Source**
- `SL2Read.v:1485-1531`: `read_provable_vti` applies `sl2_read_run_provable_v`, with `rinv_init` and `rstep_ok`. `sl2_main` = `sl2rd_v_of_methods` applied to `read_provable_v` and `write_provable`.
- A grep for `MethodSem`, `method_sound`, `ren_rlhl`, `CallTriple` and `h_sem` in SL2Read, SL2Write, SL2InvLog and SL2Inv finds comments only.
- `M2w` and `P1` (SL2Prog.v:601-610) and `mtraces_guard` (:643) are as described.
- `RelaxedHoareLayer.mtraces_mono` (:148) and `RelaxedHoareAbsorb.unabsorb` (:930) exist. `absorb` is still PENDING (Absorb.v:19).
- HVF is not needed on the CompLin route (CompLin.v:86).

**Scratch sessions (stdin only, all accepted)**
- (a) Lens 2's `sbo_not_rel_lin`, full script in M-29. Result: Closed under the global context.
- (b) Lens 3's `sl2_no_mp` ({eq_rect_eq, classic}) and `sl2_complin_unguarded` ({classic}), full script in m-69.
- (c) rc vacuity: `Goal forall o o2, sindep true o o2 <-> sindep false o o2. Proof. intros [l|l v| |] [l2|l2 v2| |]; unfold sindep; cbn; reflexivity. Qed.`

**Paper**
- `git diff 01484091 4a2db8e1 -- Appendix/programlogic.tex` gives the hunks `@@ -35,7 +35,7 @@` and `@@ -463,9 +463,51 @@`, so lines from :466 on move by +42.
- EStep is at :537 at 01484091 and at :579 at HEAD. HEAD :537 is a different rule.
- trace.tex:75 and overview.tex:164: COH with no barriers. trace.tex has no rmb or wmb.
- trace.tex:96-107: I_RA, and SB with own reads, which "Ordinary registers cannot explain".
- intro.tex:111: the oMCA focus applies "to the memory instances and their comparison theorems, rather than to every relaxed object".
- relaxedlin.tex:520 and :628: "Single possibilities are not generally sufficient … future-dependent".
- No main.tex input mentions SeqLock.

**Records**
- research-intent.md:178 still says that the reloading writer "is SC on this underlay". :165 says "Linux seqcount style". RD-8 (:119) sets the paper scope to MCA + barriers.
- concern-matrix row 45 (B5) lists only `SeqLockModule`, and the matrix has no SL2 entry.

## Verdict
The kernel-checked claims in scope hold exactly as stated, within the baseline {classic, eq_rect_eq}. **No BLOCKER. No redesign. The RLHL-seqlock Coq task can be closed.** The paper must not cite the result until the authors decide M-28 and M-29.

1. **"RLHL used in full": true.**
   - `read_provable_v` and `write_provable` are genuine syntactic derivations: `run_method_provable` → `rp_run` → `RProvable_coind`.
   - Every `RunStepOK` is discharged (`rstep_ok`/`wstep_ok`). `rnew` builds every `NewSlotOK` field: each `ns_if_*` premise is either a stability fact by class or is refuted by order (`bef_pos`, `fe_le`). `rclose` gives a genuine `BarrierWith`.
   - The writer is moved from EIhl to EIhlv by `methodprovable_lift`, a rule-by-rule coinductive transport, not route S.
   - The only route to `h_sem` is `method_sound`, inside `rlhl2_of_provable`.
   - Caveat: this is the mechanized RLHL, not the printed rules (M-21; see also m-66).
2. **The final statements are exactly as claimed** (see Checks).
3. **The reader argument is sound.**
   - The LP is at the rmb after which the call owns no rmb in the ghost (`isl_read_lp`).
   - `PkgAt`/`PkgT` plus `rok` force r0 = q = r0′, so the logged values at Close are the LP's `A i` (`pkgT_vals`, `logval_unique`).
   - The B-6 disjunct is refuted at `mp_ret` by `NoOwn`.
   - `rinv` over `length cs` covers any number of iterations.
   - The prophecy is sound by commit-at-invocation (impl.tex:141, :172), but it should be named as such (m-65).
4. **The witnesses and negatives are genuine.**
   - `sb2_exec_rd_ij`, `sw_exec_ij` and `retry_exec` are module-derived, complete executions over `EI δS`.
   - `sl2rd_no_complin_pair` is presentation-free and tight per pair when (vx, vy) ≠ (0, 0). The EIhl and EIhlv RLHL2Hyps negatives are corollaries of it.
   - `retry_exec` is a liveness/non-vacuity witness, not a discriminating one.
   - The M-23 caveat appears at every SB and single-writer citation in the Coq.
5. **B:215.** It may be claimed only as a partial answer: an RLHL-verified SeqLock over COH registers plus ordering-only barriers, with the M-28 caveats. M-29 adds that the verified contract is provably false under store forwarding. Still open: B:212, B:309-316 (B-1), M-22, m-8, m-36, m-37.
6. **Headers are accurate except for:**
   - m-65: the prophecy wording;
   - m-66: the SL2Read/SL2Write P paragraphs contradict M-21;
   - m-67: the mixed programlogic.tex numbering. "Working tree" now means HEAD 4a2db8e1, and SL2Read's ":537, rule EStep" is wrong at HEAD.
7. **Closure:** close the task. Before the paper cites it, the authors must decide M-28 and M-29. Recommended Writer follow-ups: m-65…m-69.

Precision fixes made during verification (no finding was withdrawn):
- Lens 1's B-1 parenthetical "mtraces_mono missing" is stale.
- Lens 2's M-29 cited `sindep_rc_vacuous` as a repository lemma; it exists only in scratch. trace.tex:392 restricts the comparison, not the COH definition.
- Lens 2's M-28 overstated the clash with intro.tex:111. The clash is with the author decision "Scope = oMCA" and with response A2.
- "IRIW with rmbs excluded" is argued, not kernel-checked.

## Findings

### BLOCKER
None.

### MAJOR

- **[B-1] (carried; status updated) Reviewer B's chain of logic, soundness against RC11, object and client is still not mechanized. The SeqLock now provides the object link only.** (research-level)
  - **Where:** SL2Read.v:1515-1531 and its header R (:189-194); SL2Prog.v E_S/δS; popl2027-reviews.md:313-316, :533, :615; concern-matrix rows 43 and 44.
  - **K:** `sl2_main` is closed, `sl2_complin` uses {classic} and `sl2_rel_lin` uses {classic, eq_rect_eq}. No RelaxedHoare*/SL2* file imports `memory/`.
  - **S:**
    - `RCompLin` holds over the sequential MCA register specification `EI δS`. This is not ν_COH;cc_E: `absorb` (⊇) and linking are pending, while `mtraces_mono` and `unabsorb` are done.
    - No client theorem exists. ClientSB.v:138 says it is not the a=b client.
    - `M2w` sends a write by any thread other than `tw i` to `div`. The B4 client "whose writers invoke write(v,v) … even with concurrent writers" (:533) therefore cannot be stated on a single instance with several writers.
  - **P:** intro.tex:105 limits the RC11 claim to coherence. The main text has no SeqLock.
  - **R:** B asks for "the program logic, its soundness proof against a weak memory model such as RC11, and the verification of a concurrent object alongside the verification of its client program" (:313-316). The meta-review (:615) names "the lack of a demonstration of client verification".
  - **Assessment:** the Coq does not overclaim (SL2Read:193-194).
  - **Required:**
    - Never cite the SeqLock for B:309-316 or B4. If that happens, this becomes a BLOCKER.
    - Next steps: (i) a property-level a=b corollary of `sl2_complin`; (ii) the module-level client through RLHL-3c (absorb and linking, M-22); (iii) the memory route (m-37).
    - For B4, decide between one writer thread per instance and a lock-protected writer, and change the response wording to match.

- **[M-28] (new; lens 1 M-28 + lens 2 M-29 + lens 3 M-28) What B:215 may claim. The verified model (COH registers plus ordering-only Wmb/Rmb) and the mechanized logic do not exist in the paper.** (research-level)
  - **Where:** SL2Prog.v:129-213 (Scope, P); SL2Read.v header; trace.tex:52, :75, :165-187; overview.tex:164; Appendix/SeqLock.tex:3, :47; relaxedlin.tex:520, :628; impl.tex:120-141, :172; concern-matrix row 45.
  - **K:** see Checks.
  - **S:** for every rc (vacuous), every tw and every si ⊇ slRA:
    - `RCompLin` holds for every reachable prefix;
    - `rel_lin` holds for complete traces;
    - the result is tight in si (`sl2rd_no_complin_pair`);
    - it is non-vacuous (`sb2_exec_rd_ij`, `sw_exec_ij`, `retry_exec`).
  - **Model and object restrictions:**
    1. A sequential, MCA register file. `δS` makes the barriers no-ops, and they order only through `WindowTable.dto` and same-location order. All modes are `Local`.
    2. One writer thread per instance, enforced by refusal (`div`), not by a precondition or an error clause (m-8, m-69).
    3. The cached-v writer: SB is shown without own reads (M-23).
    4. The reader is untagged with hand-written tags. The κ-policy reader (impl.tex:141) is covered only by an argued tag-monotonicity (m-54).
    5. The LP is ghost-prophetic with a single possibility (m-33, m-65).
    6. The logic is the mechanized RLHL (`rp_run`, Close, `ns_if_*`/`bw_if`, the ghost, Ω, `Qrd`'s ¬NoOwn disjunct, the EIhlv history). The printed EStep own-event premise is commented out at HEAD :558 (M-21).
    7. Copy-cat EI specifications; agreement with REW is argued only (M-20). `MTraces (EI δS)` vs ν;cc is unproved (M-22).
    8. The N instances form one object over one shared memory (m-70).
  - **P:**
    - The paper's COH has no barriers, and the four fence modes cannot express Wmb/Rmb (`paper_modes_fail`, `four_modes_force_local`).
    - Appendix/SeqLock.tex is a different TicketLock/TSO object (RS-6 is open).
    - relaxedlin.tex:520/:628 says single possibilities are insufficient for future-dependent LPs.
  - **R:** B:215 says "No example verified on the COH model". B5 (:537) answers "consider adding a library case study over COH". A:151-154 asks about COH-with-fences and MCA.
  - **Required (authors), before any citation:**
    - (a) Define "COH + rmb/wmb" in trace.tex (the dto rows R/Rmb and W/Wmb, and same-location order), relate it to the fence-mode lattice, and say it is MCA.
    - (b) State the result as copy-cat inclusion for all prefixes plus rel_lin for complete traces, at slRA (tight).
    - (c) Name the writer "a single-writer seqcount whose closing increment reuses the opening read". Never call it the Linux seqcount.
    - (d) State P1 by refusal (or cite the m-69 corollary).
    - (e) Qualify relaxedlin.tex:520/:628 with the commit-at-invocation prophecy.
    - (f) Present the mechanized RLHL, or say "a Rocq variant of RLHL".
    - (g) Prove tag-monotonicity (m-54) or present the reader with its hand-written tags.
    - (h) Mention M-22.
    - (i) Decide RS-6.
  - A citation for B:215 without (a)-(c) and (f) is a BLOCKER. So is citing the result as the mechanization of Appendix/SeqLock.tex.

- **[M-29] (new; lens 2's M-28) The verified contract (slRA over atomic pair registers) is MCA-specific. The SeqLock-level SB-with-own-reads outcome that store forwarding produces is not rel_lin under any si ⊆ slRA.** (research-level, with an actionable part)
  - **Where:** SL2Prog.v:131-136, :196-205; SL2Read.v:173-179; research-intent §8 "Scope = oMCA" (:125) vs RD-8 (:119); trace.tex:94-107; popl2027-reviews.md:38-40 (A), :437 (A2), :615.
  - **K:** `sbo_not_rel_lin` is closed under the global context in the scratch session; I re-ran it. The trace is t1: W₁(1,1); R₁ ↦ (1,1); R₂ ↦ (0,0), and t2 is symmetric. All six calls overlap. The (fW i, fR i) and (fR, fR) edges are not in slRA, so two legality edges close a cycle.
  - **S:**
    - On x86-TSO, smp_rmb/wmb are compiler barriers, so each reader forwards its own buffered seq, x and y, and reads the other instance from memory. This is a standard hand argument; I agree with it.
    - On ARMv8, rfi ∉ obs and DMB LD orders nothing from W to R, so the same outcome is allowed.
    - So the slRA contract cannot be carried to a buffered or oMCA underlay by the planned memory route without changing the contract, for example to a buffered pair register over a thread-aware EI (m-37).
  - **P:** trace.tex:107 makes exactly this point for registers. The headers say only that the underlay "lacks" forwarding.
  - **R:** A:38-40 says "Even TSO cannot be explain merely by store-load reorderings … but rewrites also store-forwarding". The meta-review names "the handling of store forwarding".
  - **Required:**
    - (actionable) Add `sbo_not_rel_lin` to SL2Exec (script below), and add to the SL2Prog and SL2Read S/P paragraphs: "the verified contract is falsified under store forwarding (trace: kernel-checked; hardware: argued)".
    - (authors) Reconcile the "Scope = oMCA" decision with RD-8 for this example, and present the SeqLock as an MCA-only data point, as response A2 promised.
    - Citing the SeqLock as evidence about TSO, ARMv8, oMCA or forwarding is a BLOCKER.
  - **Script** (complete; run from stdin from the repo root with the `_CoqProject` -R flags):
    ```
    From Stdlib Require Import List Arith.PeanoNat micromega.Lia.
    Require Import models.LinCCAL models.RelaxedSignature models.simlin.RelaxedLTS models.simlin.RelaxedTraceLin.
    Require Import models.simlin.RelaxedHoareSpec models.view.PrefixView.
    Require Import examples.Relaxed.RelaxedHoareSL2Prog examples.Relaxed.RelaxedHoareSL2Exec.
    Import ListNotations. Import LinCCALBase. Import RelaxedSig. Import RelaxedLTSSpec. Import RelaxedHoareSL2Prog. Import RelaxedHoareSL2Exec.
    Ltac in_tac := cbn; solve [repeat (first [left; reflexivity | right])].
    Ltac nodup_keys := cbn; repeat constructor; cbn; let H := fresh in intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    Ltac inv_here := eexists; split; reflexivity.
    Definition sbo (si : FOp -> FOp -> Prop) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
      [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t1 (@InvEv (F2 si) 1 (fR 1)); Build_ThreadEvent t1 (@InvEv (F2 si) 2 (fR 2));
       Build_ThreadEvent t2 (@InvEv (F2 si) 3 (fW 2 1 1)); Build_ThreadEvent t2 (@InvEv (F2 si) 4 (fR 2)); Build_ThreadEvent t2 (@InvEv (F2 si) 5 (fR 1));
       Build_ThreadEvent t1 (@ResEv (F2 si) 1 (fR 1) (1, 1)); Build_ThreadEvent t1 (@ResEv (F2 si) 2 (fR 2) (0, 0));
       Build_ThreadEvent t2 (@ResEv (F2 si) 4 (fR 2) (1, 1)); Build_ThreadEvent t2 (@ResEv (F2 si) 5 (fR 1) (0, 0));
       Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW 1 1 1) tt); Build_ThreadEvent t2 (@ResEv (F2 si) 3 (fW 2 1 1) tt)].
    Definition oWi (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 0) (fW 1 1 1) tt.
    Definition oRi (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 1) (fR 1) (1, 1).
    Definition oRj (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 2) (fR 2) (0, 0).
    Definition oWj (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 3) (fW 2 1 1) tt.
    Definition oRj' (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 4) (fR 2) (1, 1).
    Definition oRi' (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 5) (fR 1) (0, 0).
    Lemma sbo_sub si t1 t2 : forall e, In e (sbo si t1 t2) -> In e (evs_of [oWi si t1; oRi si t1; oRj si t1; oWj si t2; oRj' si t2; oRi' si t2]).
    Proof. intros e He. cbn in He. repeat (destruct He as [<- | He]; [in_tac |]). destruct He. Qed.
    Theorem sbo_not_rel_lin si indep t1 t2 : (forall o o', indep o o' -> slRA o o') ->
      ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sbo si t1 t2) indep (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
    Proof.
      intros Hsub Hrl.
      destruct (rel_lin_ops (sbo si t1 t2) indep _ [oWi si t1; oRi si t1; oRj si t1; oWj si t2; oRj' si t2; oRi' si t2] ltac:(nodup_keys) (sbo_sub si t1 t2) Hrl) as (W & (A' & Hrun) & Hnd & HW & Hin & Hord).
      assert (H0 : In (oWi si t1) W) by (apply (Hin _ 0); [in_tac | inv_here]).
      assert (H1 : In (oRi si t1) W) by (apply (Hin _ 1); [in_tac | inv_here]).
      assert (H2 : In (oRj si t1) W) by (apply (Hin _ 2); [in_tac | inv_here]).
      assert (H3 : In (oWj si t2) W) by (apply (Hin _ 3); [in_tac | inv_here]).
      assert (H4 : In (oRj' si t2) W) by (apply (Hin _ 4); [in_tac | inv_here]).
      assert (H5 : In (oRi' si t2) W) by (apply (Hin _ 5); [in_tac | inv_here]).
      assert (B01 : RelaxedTraceLin.before W (oWi si t1) (oRi si t1)).
      { apply Hord; [exact H0 | exact H1 |]. right. split; [reflexivity |]. exists 0, 1. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact (H eq_refl). }
      assert (B12 : RelaxedTraceLin.before W (oRi si t1) (oRj si t1)).
      { apply Hord; [exact H1 | exact H2 |]. right. split; [reflexivity |]. exists 1, 2. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact H. }
      assert (B34 : RelaxedTraceLin.before W (oWj si t2) (oRj' si t2)).
      { apply Hord; [exact H3 | exact H4 |]. right. split; [reflexivity |]. exists 3, 4. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact (H eq_refl). }
      assert (B45 : RelaxedTraceLin.before W (oRj' si t2) (oRi' si t2)).
      { apply Hord; [exact H4 | exact H5 |]. right. split; [reflexivity |]. exists 4, 5. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact H. }
      destruct (In_nth_error _ _ H0) as (i0 & E0). destruct (In_nth_error _ _ H1) as (i1 & E1).
      destruct (In_nth_error _ _ H2) as (i2 & E2). destruct (In_nth_error _ _ H3) as (i3 & E3).
      destruct (In_nth_error _ _ H4) as (i4 & E4). destruct (In_nth_error _ _ H5) as (i5 & E5).
      pose proof (before_idx W _ _ _ _ Hnd B01 E0 E1). pose proof (before_idx W _ _ _ _ Hnd B12 E1 E2).
      pose proof (before_idx W _ _ _ _ Hnd B34 E3 E4). pose proof (before_idx W _ _ _ _ Hnd B45 E4 E5).
      assert (i2 < i3).
      { apply (leg_read_before A0 W A' i2 i3 (oRj si t1) (oWj si t2) 2 1 1 Hrun E2 E3 eq_refl eq_refl).
        intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hop; try discriminate Hop; injection Hop; intros; subst; cbn; congruence. }
      assert (i5 < i0).
      { apply (leg_read_before A0 W A' i5 i0 (oRi' si t2) (oWi si t1) 1 1 1 Hrun E5 E0 eq_refl eq_refl).
        intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hop; try discriminate Hop; injection Hop; intros; subst; cbn; congruence. }
      lia.
    Qed.
    Print Assumptions sbo_not_rel_lin.
    ```

### MINOR

- **[M-23] (carried; Coq part fixed, downgraded to MINOR) Residue in the records.** (actionable for the orchestrator; author to confirm)
  - **Where:** research-intent.md:178, which says the reloading writer "is SC on this underlay", and :165 ("Linux seqcount style").
  - **K/S:** only "no SB" is argued (SL2Exec header, SL2Prog:4-18). SC is not proved. All `.v` headers are correct.
  - **Required:** annotate :178 as "no SB (argued); SC not proved", as was done for RS-1 at :168, and annotate :165. Optionally add a `wnextL` contrast theorem.

- **[m-54] (carried) Tag-monotonicity of `MTraces` is unproved.** (actionable)
  - **Where:** SL2Prog.v:167-174.
  - **Status:** the wording now says "argued, not proved", but the lemma is still missing.
  - **Required:** a generic lemma that if tags are pointwise contained, then MTraces(more tags) ⊆ MTraces(fewer tags). With it, `sl2_complin` transfers to the κ-tagged reader. Otherwise keep M-28(g).

- **[m-65] (new; lens 1 m-65, lens 3 m-67, lens 2 m-66 Log part) The prophecy wording is misleading.** (actionable)
  - **Where:** RelaxedHoare.v:213-228 (the single-possibility row: "no prophecy of responses"); RelaxedHoareLog.v:52-56 ("linearization points that depend on future responses under a single possibility remain out of reach").
  - **S:** the ghost stores invocations only (Base.v:281). But the committed body trace fixes the number of iterations, and that number is determined by the values the later reads return (`rok`). So "owns no rmb afterwards" (`isl_read_lp`) prophesies the outcome of the call's own future responses. The SeqLock read LP is exactly the kind of LP that Log.v says is out of reach.
  - **Required:** reword both passages along these lines: "the ghost stores no response values, but its remaining invocations, committed at invocation, determine the outcome of the call's own future validation; sound by run-to-completion (impl.tex:141, :172)". Cite relaxedlin.tex:520 and :628.

- **[m-66] (new; lens 2) The SL2Read and SL2Write P paragraphs say the rules "are those of Appendix/programlogic.tex".** (actionable)
  - **Where:** SL2Read.v:183-185; SL2Write.v:170-172.
  - **Problem:** this contradicts RelaxedHoare.v:130-131 ("The printed logic is not the mechanized one … the paper prints none of them") on exactly the M-21 point. I verified both texts.
  - **Required:** "the mechanized RLHL of RelaxedHoare.v (printed rules differ; see its table, M-21), in the run-interpreter form of RelaxedHoareRun".

- **[m-67] (new; m-61 residue) Mixed programlogic.tex numbering.** (actionable)
  - **Where:** RelaxedHoare.v:126-133 and Log.v:41-52 carry the shift note. SL2Read:184-187, SL2Write:173, SL2InvLog:212-214, SL2Inv:180-183/:224-227, GSim:203/:336-346, Dag:32 and CounterXY:274 cite 01484091 numbering without the note.
  - **Facts:** the "working tree" in the note is committed HEAD 4a2db8e1. SL2Read's ":537, rule EStep" points to a different rule at HEAD; EStep is now at :579.
  - **Required:** renumber all programlogic.tex anchors to 4a2db8e1 and name the commit once, or add the note to every file that cites lines ≥ :476.

- **[m-68] (new; lens 1 m-68, lens 2 m-67, lens 3 m-65 part) Facts described as "kernel-checked in a scratch file outside the build" cannot be reproduced.** (actionable)
  - **Where:**
    - SL2Prog.v:113-123 (overtakes trace rel_lin at ∅);
    - SL2Prog.v:140-153 (rc vacuous);
    - SL2Write.v:43-53 (`rlhl2_v_of_reads` discharged).
  - **Status:** none of these is saved in `.rocq-review/scripts/`.
  - **Required:** add `sindep_rc_vacuous` (script (c) in Checks), `ov_rel_lin_empty` and an `rlhl2_v_of_reads` instance as lemmas, add `sbo_not_rel_lin` (M-29), and cite them by name.

- **[m-69] (new; lens 2 m-68, lens 3 m-65) The precondition-form and MP corollaries are not stated.** (actionable)
  - **S:** `sl2_complin` concerns the non-receptive `M2w`. The P1-precondition form for the unguarded `M2` and the module-level MP exclusion are each two-line corollaries. I re-ran both.
  - **Required:** add them (generalize `sl2_no_mp` to every si as `lb2_not_trace_rd` does). Paper text should cite the P1-precondition form. Script:
    ```
    Require Import examples.Relaxed.RelaxedHoareSL2Read. Require Import examples.Relaxed.RelaxedHoareSL2Exec.
    Import RelaxedHoareSL2Prog.RelaxedHoareSL2Prog RelaxedHoareSL2Read.RelaxedHoareSL2Read RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.
    Lemma sl2_no_mp rc tw s : RelaxedHoareCompLin.RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc slRA tw) (regs0, nil) s -> PrefixView.PrefixView.complete s -> ~ mp_shaped s.
    Proof. intros Htr Hc Hmp. apply (mp2_not_rel_lin slRA slRA s slRA_slsi Hmp). exact (sl2_rel_lin rc slRA tw s (fun o o2 H => H) Htr Hc). Qed.
    Lemma sl2_complin_unguarded rc si tw s : (forall o o2, slRA o o2 -> si o o2) -> RelaxedHoareCompLin.RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.RelaxedHoareSpec.EI (F := E_S rc) δS) (M2 rc si) (regs0, nil) s -> P1 tw s -> RelaxedHoareCompLin.RelaxedHoareCompLin.RTraces (RelaxedHoareSpec.RelaxedHoareSpec.EI (F := F2 si) δF) (A0, nil) s.
    Proof. intros Hsi Htr HP. apply (sl2_complin rc si tw Hsi). exact (mtraces_guard rc si tw _ _ s Htr HP). Qed.
    ```
    Results: `sl2_no_mp` uses {eq_rect_eq, classic}; `sl2_complin_unguarded` uses {classic}.

- **[m-70] (new; lens 3 m-68) The "two SeqLocks" are one N-instance object over a shared memory, with `Local` modes.** (research-level)
  - **Where:** SL2Prog.v GLoc (:277, global GBw/GBr), F2 (:442).
  - **Facts:**
    - Cross-instance order comes from the shared barriers, not from ⊗ (relaxedlin.tex:191).
    - slRA coincides with I_cross for fW ↦ lfence, fR ↦ rfence (trace.tex:183-187; hand computation, unchecked).
    - `paper_modes_fail` refutes those modes for the window-route SeqLock. For WRd they are unverified.
  - **Required:** describe the object as "one object with N instances". Optionally, prove the slRA = I_cross lemma on a new signature.

**Withdrawn:** none. All three lenses' BLOCKER/MAJOR findings were upheld at MAJOR.

## Responses to Writer disputes
No item was marked DISPUTED.

| Writer status | Response |
|---|---|
| M-23 FIXED | Accept for the Coq; the records residue stays as MINOR. |
| M-25 | Accept: `read_provable_v` is genuine and closed. |
| m-51, m-55, m-60, m-62, m-63 | Accept. The phantom-path NoOwn is indeed unnecessary, because Close needs only `Pkg`/`PkgT` ∨ an owned rmb. |
| m-64 | Accept; the residue is m-65. |
| m-56, m-61 | Accept; the residue is m-67. |
| "Docs pass comment-only" | Accept. It is consistent with the unchanged statements and the current build. |
| NEEDS-AUTHOR on research-intent:178 | Agree (M-23 residue). |

## Concern-matrix corrections
- **Row 43 (B3):** (iv) object via the logic ✓ (SL2; M-28/M-29 caveats). B-1(4′) is met: non-renaming, nonempty SI, value-carrying `Isl`. The client and the memory link are still ✗. In the Missing list, write "absorb (⊇), linking pending; `mtraces_mono`, `unabsorb` done". The row stays ❌.
- **Row 44 (B4):** stays ❌. Note that P1 (one writer per instance) conflicts with the response's "even with concurrent writers".
- **Row 45 (B5):** add the RLHL WRd SeqLock: `sl2_main` (closed), `sl2_complin` (classic), `sl2_rel_lin` (classic + eq_rect_eq), the witnesses `sb2_exec_rd_ij`, `sw_exec_ij`, `retry_exec`, and the tight negatives `sl2rd_no_complin_*`. Status: "🟡 partially addressed; MCA only; M-28, M-29".
- **Row 32 (A2):** the SB datum is without own reads and depends on the cached v. Add M-29 (`sbo_not_rel_lin`): the slRA contract fails under forwarding.
- **Row 64 (RLHL rules):** add the first looping, multi-call, value-carrying concurrent instance at nonempty SI. HVF is not needed on the CompLin route.
- **Rows 67 and 92 (intra-call own events):** "frame-only" → value-level own interference is exercised by SL2Write (AW/GF) and SL2Read (Pkg/KOwns vs the own LP). The paper wording is still pending (M-21).
- **Rows 68 and 83 (LB):** `lb2_not_trace_rd` is unconditional; WRd excludes LB, so it is not an LB datum.
- **Row 69 (completeness):** unchanged ⚠️. Add: the lossy EIhl presentation is incomplete for validate-after-read (argued).
- **Row 74 (printed rules):** add m-66.
- **Row 75 (end-to-end nonempty SI):** add the SeqLock (non-renaming).
- **Row 76 (universal negatives):** add `sl2rd_no_complin_{pair,missing,empty}`, `sl2rd_no_rlhl2_empty_any`, `sl2rd_no_rlhl2v_*`.
- **Row 81 (single possibility):** add the ghost-prophetic read LP (m-33, m-65).
- **Row 86 (run-to-completion):** consumers are the SeqLock read LP and P1-by-div. Add m-69.
- **Row 89 (absorption):** `unabsorb` done; `absorb` pending.
- **New or closed rows:**
  - M-28 ⚠️ (author);
  - M-29 ⚠️ (author, with an actionable part);
  - m-65…m-70 📝;
  - closed: M-25, M-23 (Coq part), m-51, m-55, m-60, m-62, m-63, m-64;
  - m-33: the documentation half is done, the paper half is open;
  - m-57 unchanged.
- **research-intent.md:** :178 and :165 as in M-23. Record the tension between RD-8 (MCA + barriers) and "Scope = oMCA" for the SeqLock (M-29).

## Stronger or alternative approaches
1. Add `sbo_not_rel_lin`, `sl2_no_mp`, `sl2_complin_unguarded` and the scratch facts as lemmas (m-68, m-69, M-29). This is cheap and turns comments into checked claims.
2. Broken variants (no final rmb, missing wmb) with module-derived torn-read executions that refute `RCompLin` at every si. They would show that the proof uses the barriers essentially, which is strong evidence for B:215.
3. A generic tag-monotonicity lemma for `MTraces` (m-54), so the result covers the κ-compiled reader.
4. A `wnextL` reloading writer: a kernel-checked "no SB" (M-23) and, ideally, its RLHL proof reusing the reader unchanged.
5. A property-level a=b corollary of `sl2_complin`, then the module-level client through absorb and linking (B-1, M-22).
6. For oMCA: a buffered (Flush-lifted) pair-register overlay over a thread-aware EI (m-37). The current contract cannot transfer (M-29).
7. Longer term: fold the history (Log) into PState generically (programlogic.tex EStep) instead of a per-VE presentation. Also derive the N-instance object from a single SeqLock by ⊗ with exported modes (m-70).

## Redesign assessment
No redesign of the mechanization is needed. The pieces compose into a sound, kernel-checked, non-vacuous, si-tight end-to-end result about the original module over `EI δS`:
- the RProvable rules and the `run` interpreter;
- the ghost frontier;
- the HL and Log presentations, both justified by closed trace equivalences;
- `method_sound` → `rlhl_complin_eihlv`.

What remains is paper-side scope and research decisions:
- the COH+barrier definition and how to present the mechanized logic (M-28);
- MCA vs oMCA and store forwarding (M-29);
- the carried items B-1, M-22, m-8, m-36, m-37.

The RLHL-seqlock task can be closed. The paper may cite it only after M-28 and M-29 are decided.

Relevant files:
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Read.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Write.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2InvLog.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Exec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Prog.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoare.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareLog.v
- /Users/index/Documents/GitHub/rbgs-rlhl/.rocq-review/research-intent.md
- /Users/index/Documents/GitHub/rbgs-rlhl/.rocq-review/concern-matrix.md
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/trace.tex
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/Appendix/programlogic.tex
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/Appendix/relaxedlin.tex