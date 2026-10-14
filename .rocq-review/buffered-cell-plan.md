# Buffered-cell redesign of the SeqLock running example: plan (2026-10-13)

Produced by a read-only 7-agent workflow:
- 1 Q6 confirmation (piped Rocq; nothing written);
- 3 independent designs: reuse-first, memory-first, proof-architecture-first;
- 2 `rocq-research-reviewer` judges (soundness, effort);
- 1 synthesis.

**Status:** a proposal. It needs the author's answers to the questions at the end before Phase 1. Phase 0 (locking in the evidence) does not commit to a design.

## Q6 status

Q6 is CONFIRMED in Coq at three levels. The hardware part is still a derivation only. The kernel checks were run in piped toplevel sessions and are not yet in any committed file.

**K: what the kernel checked**

1. **Overlay: `q6_not_rel_lin`.**
   - Statement: ∀ rc, `~ rel_lin Some (q6_trace 0) (semi_independent (F rc)) (BL.nuF_all SL.comp_dec fcomp (SLM.nuFc rc))`.
   - I re-ran script A myself in this session (Rocq 9.3.0, nothing written; `git status` unchanged). Result: no errors, and `Print Assumptions` gives "Closed under the global context".
   - In the trace, all six invocations come before all six responses. So only the same-thread clause of rhb (RelaxedTraceLin.v:60-65) applies.
   - The four forced edges are:
     - zw<zr: same component;
     - zr<read: `dto DR Rmb`, from `fcat_cross_table`, SeqLockClients.v:617;
     - write<read: same component;
     - read<zr: `read_zr_dependent`, :630.
   - Controls (confirmation agent; closed): `q6_zr1_rel_lin` (same trace with zr()=1) and `sb_rel_lin` (plain SB). They show that the forwarded zr()=1 is what makes the interface forbid the outcome.

2. **Underlay.**
   - `q6_underlay_no_WF`: ∀ rc w, `~ SL.WF rc SL.plainTL (SL.mkX q6p0 q6p1 w)`. Closed. Re-run independently by judge 1.
   - `q6_underlay_not_rel_lin`: the 42-event trace, in exactly the hypothesis shape of `seqlock_module_rel_lin` (SeqLockModule.v:1247). Closed, per the confirmation agent. Its proof body is only outlined in the record, so committing it means re-deriving it.
   - Control: `ctl_wf` (zr()=1 instead) is WF.
   - The cycle: WrZ1 <obj RdZ1 <tab rmb <tab RdX0 <val WrX1 <obj RdX1 <tab rmb <tab RdZ0 <val WrZ1.
   - So `seqlock_module_rel_lin` is not wrong. Its hypothesis fails on this execution, so it says nothing about it.

3. **memory/.**
   - `sq_V` and `sq_nu` are closed.
   - `q6_cells_TSO_consistent` (D1∧D2 via `Equivalence.declarative_TSO`, even with pre = full po) uses `classic` only.
   - So the cell part of the run, store forwarding included, is TSO-OMCA-consistent.
   - memory/ cannot express rmb/wmb, RMW, ARM fences, or the retry loop.

**Derivation only**
- x86-TSO and ARMv8 "Allowed" are hand derivations. herd7 is not installed, and the SeqLockZ+rfi litmus tests in the confirmation have never been run.

**Not checked**
- The barrier-free, cell-only correspondence (SL-mem item 2).
- The real-time obstruction for register x/y (Design 1, BUF-0(c)). It is an independent second gap; see task Q6-2.

**Consequences**
- SL-mem item 3's direction ("OMCA-consistent underlay ⇒ underlay hypothesis") is false as posed.
- The author's redesign (research-intent.md:109) is necessary. This plan proceeds with it.


### Confirmation agent: hardware reasoning (derivation; herd7 not installed)

herd7 was not run (not installed). Both verdicts below are hand derivations.

x86-TSO: ALLOWED. Mapping: rmb/wmb are compiler barriers (no instruction); acq/rel are locked RMWs (XCHG); get_ticket/test_ticket are plain loads of s.

Operational run on the Owens–Sarkar–Sewell machine:
1. T1: z:=1 goes into T1's buffer. T1's load of z is forwarded (1). T1's loads of s, x, y, s read memory (0, 0, 0, 0), so the test passes and read()=(0,0).
2. T2: XCHG s (buffer empty; s := 1), x:=1 and y:=1 into the buffer. XCHG s drains the buffer, so x=1 and y=1 reach memory, then s := 2.
3. T2's loads: s=2, x=1, y=1, s=2, so read()=(1,1). T2's load of z reads memory: 0.
4. Only then does T1's buffer drain (z = 1).

Axiomatic check (x86tso: ghb = ppo(po minus W×R) ∪ implied-by-locked ∪ rfe ∪ fr ∪ co):
- T1's store Wz has no outgoing ghb edge. ppo excludes W→R. T1 has no later store and no locked instruction. Its only reader is internal (rfi ∉ ghb), and it is the only write to z.
- The only edge from T2 into T1 is Rz2 →fr Wz. Every cycle would have to pass through the sink Wz, so ghb is acyclic.
- uniproc and RMW atomicity hold.
- This is "SB+rfi" (reviewer A's test, popl2027-reviews.md:69-81) lifted through the object.

ARMv8: ALLOWED. Mapping: rmb = DMB LD, wmb = DMB ST, acq = SWPA, rel = SWPL. The argument also holds with plain, A, L or AL RMWs, and even with a DMB SY in T2.
- T1's STR z is a sink of ob:
  - obs: its only reader is rfi; no coe.
  - dob: none.
  - bob: DMB LD orders only earlier loads; DMB ST is W→W and T1 has no later store; T1 has no L, A or DMB SY.
- So the only cross edge back into T1, Rz2 →fre Wz, closes no cycle. EXTERNAL (acyclic ob), INTERNAL and ATOMIC hold.
- There is a second, independent instance on T2's side. read()=(1,1) reads T2's own stores (rfi). SWPL's write is not ordered before T2's later loads ([L];po;[A] does not apply to plain loads). So Wx2 and Wy2 are not ordered before Rz2 either. The interface's write<read<zr chain uses the same transitivity.

Litmus tests:

X86 SeqLockZ+rfi
{ x=0; y=0; z=0; s=0; }
 P0          | P1           ;
 MOV [z],$1  | MOV EAX,$1   ;
 MOV EAX,[z] | XCHG [s],EAX ;
 MOV EBX,[s] | MOV [x],$1   ;
 MOV ECX,[x] | MOV [y],$1   ;
 MOV EDX,[y] | MOV EBX,$2   ;
 MOV ESI,[s] | XCHG [s],EBX ;
             | MOV ECX,[s]  ;
             | MOV EDX,[x]  ;
             | MOV ESI,[y]  ;
             | MOV EDI,[s]  ;
             | MOV EAX,[z]  ;
exists (0:EAX=1 /\ 0:EBX=0 /\ 0:ECX=0 /\ 0:EDX=0 /\ 0:ESI=0 /\ 1:ECX=2 /\ 1:EDX=1 /\ 1:ESI=1 /\ 1:EDI=2 /\ 1:EAX=0)
Expected with herd7 -model x86tso.cat: Allowed (Sometimes).

AArch64 SeqLockZ+rfi
{ 0:X1=z; 0:X3=s; 0:X4=x; 0:X5=y; 1:X1=z; 1:X3=s; 1:X4=x; 1:X5=y; }
 P0          | P1               ;
 MOV W0,#1   | MOV W0,#1        ;
 STR W0,[X1] | SWPA W0,W2,[X3]  ;
 LDR W2,[X1] | DMB ST           ;
 LDR W6,[X3] | STR W0,[X4]      ;
 DMB LD      | STR W0,[X5]      ;
 LDR W7,[X4] | DMB ST           ;
 LDR W8,[X5] | MOV W6,#2        ;
 DMB LD      | SWPL W6,W9,[X3]  ;
 LDR W9,[X3] | LDR W10,[X3]     ;
             | DMB LD           ;
             | LDR W11,[X4]     ;
             | LDR W12,[X5]     ;
             | DMB LD           ;
             | LDR W13,[X3]     ;
             | LDR W14,[X1]     ;
exists (0:X2=1 /\ 0:X6=0 /\ 0:X7=0 /\ 0:X8=0 /\ 0:X9=0 /\ 1:X10=2 /\ 1:X11=1 /\ 1:X12=1 /\ 1:X13=2 /\ 1:X14=0)
Expected with herd7 -model aarch64.cat: Allowed. LDADDA/LDADDL can replace the SWPs.

Minimal cores, expected Allowed:
- X86: P0: MOV [z],$1; MOV EAX,[z]; MOV EBX,[x] ‖ P1: MOV [x],$1; MFENCE; MOV EAX,[z]; exists (0:EAX=1 /\ 0:EBX=0 /\ 1:EAX=0).
- AArch64: P0: STR z; LDR z; DMB LD; LDR x ‖ P1: STR x; DMB SY; LDR z, with the same condition.

On x86 the outcome becomes forbidden when T1's store is ordered before T1's loads: rmb as MFENCE, or a locked op between the z store and get_ticket.


### Confirmation agent: memory/ evidence

Kernel-checked in a piped repl over the TSO instance C := TSO_cfg Nat.eq_dec, with I := mode_indep. TSO_modes are at Cell.v:696; only cross-location W→R pairs are independent (TSO_indep_iff :764). Locations: z=0, x=1, y=2, s=3 (the lock/version word).

The trace `sq` (20 blocks):
- T1: W z 1 (h0); R z = 1 (h1). This read is the RdF rule (Cell.v:297): it is forwarded from T1's buffer.
- T1: R s=0, R x=0, R y=0, R s=0.
- T2: W s 1, flush s, W x 1, W y 1, W s 2, flush x, y, s.
- T2: R s=2, R x=1, R y=1, R s=2, then R z = 0. This read is RdM (:301): memory still holds 0.
- Finally T1's flush of z.

Results:
- `sq_V : V I sq` (Cell.v:624). The contract (:603) is shown by a boolean checker `chk` plus soundness lemma `contract_of_chk`. VBuf for every location goes through `VBuf_proj_iff` (:423) and `enabledb_sound`. "Closed under the global context".
- `sq_nu : nu I (hide sq)` (:627). Closed.
- Declaratively: X is the candidate of the 15 visible accesses, with po = same thread and increasing handle. I proved `wfX`, `admissible_po` (pre = po, the strongest admissible choice), `respects_po` and `presents`. Then
    q6_cells_TSO_consistent : exists w, wf_witness X w /\ consistent X I w (po X)
  follows via `Equivalence.declarative_TSO` (Equivalence.v:71). Print Assumptions: `classic` only, which is within the baseline.
- So the cell-level part, store forwarding included, is TSO-OMCA-consistent (D1 ∧ D2) even with full program order respected by the linearization. The mechanism: Dc (Declarative.v:147) uses rfe, not rf, and ppo (:133) is [rd];pre⁺ ∪ (pre0∩WW). T1's W z therefore has no outgoing Dc edge, and the internal edge W z → R z does not order W z before T1's later loads.
- The z-projection of hide sq is [W₁ z 1; R₁ z 1; R₂ z 0]. That is legal in nu because the flush is hidden, but illegal for `zreg`, the COH[z] register of nuEc. This is exactly where the abstract COH spec and the buffered cell differ.

What is expressible: all plain loads and stores to x, y, z; the get_ticket/test_ticket loads of s; store forwarding; buffer drains (hidden flushes).

What is not expressible:
- rmb/wmb: Cell has only wrt/rd/flush. On the TSO instance every read is RFence and every write LFence, so R→R and W→W are already preserved and rmb/wmb would be no-ops, consistent with x86.
- acq/rel as locked RMWs. There is no RMW. I approximated them by plain writes of s whose flushes are scheduled immediately, so the drain is chosen, not forced. This only removes constraints the real execution also meets, so admission is unaffected.
- ARMv8 dmb ld/st and RMWs: ARM.v:3-5 covers only rlx/rel/acq reads and writes, with no fences and no RMWs.
- The read's retry control flow.

Consequence for SL-mem item 3 (X ⊗ Y ⊗ Barrier ⊗ Z): the direction "OMCA-consistent underlay ⇒ underlay hypothesis of seqlock_module_rel_lin" is false as posed. The cells are TSO-consistent (proved), the full underlay is not rel_lin (proved), and rmb is a no-op on TSO.

Not checked: whether the barrier-free cell-only correspondence (item 2) is also refuted. Without rmb, dto orders no cross-object R→R, so for the overlapping trace I expect it to hold.


## Chosen design

A merge. The base is MEM-FIRST (Design 2), which both judges ranked first (7.5 and 7.0; mean 7.25, against 6.0 for BUF-ISSUE and 4.75 for rel_lin_pub).

**Taken from MEM-FIRST:**
- the memory/ instance whose semi-independence is read off the table;
- ghost barrier locations;
- the hybrid atomic clause;
- reuse of the existing proofs by SC-ification, so no existing file is edited;
- the joint-spec window variant;
- the "SeqLock ⊎ z is a buffered memory" story, kept as a corollary.

**Taken from BUF-ISSUE (Design 1):** the exported interface (Judge 2's recommendation).
- The SeqLock remains the atomic pair register `nu_sl`, ordered by linearization point.
- Each SeqLock write gets a hidden publication marker. The marker sits at the underlay flush of its first wmb, and before the next SeqLock op of any thread.
- The marker is composed with Buf[z] under a publication contract read off `findep`.
- This is stronger than MEM-FIRST's ν_{I_F}[{sl,z}] ∩ Lin_sl: a marker witness is a ν∩Lin witness, but not conversely. That spec is kept as a proved corollary.
- Also from BUF-ISSUE: its gates (the real-time obstruction).

**Taken from rel_lin_pub (Design 3):**
- a handle-free reading of the contract (witness order on dependent pairs, plus an invariance lemma);
- its no-forwarding facts F1/F2.

rel_lin, rhb, the module semantics and Def. 3.14 are unchanged.


**What does NOT change** (SeqLockProg.v unchanged):
- the categories: write↦Wmb, read↦Rmb, zw↦DW, zr↦DR, and the TL ops are DRMW/DR;
- the table `WindowTable.dto` (:460);
- `sindep` (:170), `findep` (:208) and `fcat` (:194);
- the futures program M (:251) and `M_shape`;
- the windows: the first wmb of a write, and the first rmb of a read's last iteration;
- `rel_lin` and `rhb`.

All four Q6 edges are genuine issue-order edges. The wrong edge is the value-derived one ("zr2=0 ⇒ zr2 before zw1"). It comes from the register specification, which makes a write's issue point and its publication point the same.

**Underlay specification (new, hybrid):**
- x, y and z are memory/ buffered cells: Cell.v:293 `cell_step`, `VBuf` :317, `contract` :603, `V` :624, `nu` :627.
- wmb is a write to a private ghost location Bw. rmb is a read of a ghost location Br, with Br ≠ Bw so that rmb and wmb stay unordered.
- I_tab(m,m') := loc m ≠ loc m' ∧ dto(cat m, cat m') = false. It is parametric in (Cat, to, cat), so memory/ does not import examples/.
- The TicketLock stays atomic. So do own and nxt at the tower bottom, since they are RMW-only.
- Atomic clause: at an atomic op o, every pending own write m' with dto(cat m', cat o) is already published. I checked the table in Rocq for both rc: dto(Wmb,DRMW) = true and dto(DW,DRMW) = false. So the clause publishes wmb2 before Rel, and plain writes may stay pending across an RMW.
- Handles are witness indices. A lemma shows the contract does not depend on the handle choice, given:
  - any two handle choices that agree on same-thread I-dependent write pairs;
  - dto symmetric on the buffered write categories (checked: DW/DW false both ways, DW/Wmb true both ways, Wmb/Wmb true).
- Plain writes respond at issue.

**Overlay specification (new, joint).** nuJ_SLZ W holds when there is a hidden trace, with markers and z flushes, such that:
- the SeqLock ops, in order of linearization point, are in `nu_sl` (SeqLockCOH.v:678);
- every SeqLock write's marker follows its linearization point and precedes the next SeqLock op of any thread;
- the z part, with its flushes, is in `VBuf_z`;
- the contract from `findep` holds between markers and z flushes. A pending own zw issued before a write is published before that write's marker, and the marker precedes the flush of a later own zw.

Corollary: nuJ_SLZ ⊆ ν_{I_F}[{sl,z}] ∩ Lin_sl, so clients can reason with memory/'s declarative characterization.

What the interface allows:
- **Allowed:** Q6 (zw1 stays unpublished until after zr2), LB (SeqLockCOH lb_allowed) and SB.
- **Forbidden:** MP with z as data, in both orders; MP with z as flag; OOTA.

**Proof route:**
1. **SC-ify** a buffered SeqLock-layer witness:
   - drop z, and drop z from the programs;
   - move every WrX, WrY and wmb ghost write to its flush position;
   - the result satisfies the unchanged `SeqLockCOH.WF`.

   I re-derived every upres pair against the table:
   - Acq < Iss(wmb1) < F(wmb1) < F(WrX) < F(wmb2) < Rel;
   - Rmb and reads stay at their issue positions.

   Validity follows from two facts: F1 (an x/y read never forwards, because the reader's own earlier writes are published before its own Rel, which precedes its GT), and Pending.cg_last_flush/read_value (Pending.v:576/:620).
2. **Apply the existing proofs unchanged:** `seqlock_S1` (:1267), `seqlock_S1_ord` (:1339), `wr_disjoint`/`ww_disjoint` (:1013/:1045).
3. **lp-order agreement and marker placement:**
   - `lp_order_agree`: the lp order of SeqLock ops in the witness equals their order after SC-ification, because no other SeqLock lp lies in (Iss wmb1, F wmb1).
   - The marker lies before the next SeqLock lp, because F(wmb1) < Rel_w.
4. **Composition:** a thin joint variant of `WindowTable.conclusion_of_lp_before` (:148) and `WindowLinkTable.window_link_table` (:461). The underlay is made joint with a constant compE.
5. **Module theorem:** a generalized copy of SeqLockModule Section Execution/Transport (:688-1225). The dependence on the register spec there is confined to `wit_replay`/`SX_wf` validity (:936-999).
6. **Tower:** the same SC-ification at the tower bottom gives `SeqLockTower.WF0` (:238), so `tower_link` (:1693) is reused unchanged.
7. **Grounding:** a history-level bridge through `Equivalence.declarative_characterization` (:40, generic in I) with pre := (po\I_tab) ∪ rt.
   - The TL/RMW objects remain a disclosed hypothesis.
   - The x86 end-to-end theorem is optional.

**Scope claimed:** x86-TSO (by derivation, plus an optional end-to-end theorem). ARMv8 stays open; any claim about it waits for ARM-CHK and herd7.


## Ideas grafted from the other designs

- BUF-ISSUE (Judge 2): the exported interface is an atomic `nu_sl` plus a hidden publication marker at F(wmb1(w)), placed before the next SeqLock op of any thread, with the findep contract against z flushes. It is strictly at least as strong as MEM-FIRST's ν_{I_F}[{sl,z}] ∩ Lin_sl, which becomes a proved corollary (`nuJ_to_mem`). It needs no Cantor pairing, and SeqLock-only clients still see an atomic register.
- BUF-ISSUE: a real-time obstruction gate (BUF-0(c)). Writes respond at issue, so register x/y plus rhb's real-time clause refute a failed read iteration that x86 allows. Kernel-check it first (task Q6-2); it is what justifies buffering x and y as well as z.
- BUF-ISSUE / MEM-FIRST: the atomic clause (hybrid HV). Checked in Rocq for both rc: dto(Wmb,DRMW) = true and dto(DW,DRMW) = false.
- MEM-FIRST / rel_lin_pub: reuse by SC-ification instead of BUF-ISSUE's in-place WF_core refactor. `SeqLockCOH.WF`, `seqlock_S1` and `SeqLockTower.tower_link` are applied unchanged, and SeqLockCOH.v and SeqLockTower.v are not edited. This satisfies SL-tower's acceptance rule: 'Existing files are unchanged except _CoqProject' (tasks/SL-tower.md:62).
- rel_lin_pub (Design 3): the named no-forwarding facts. F1: an x/y read never forwards. F2: no own SeqLock read lies inside a thread's own (Iss wmb1, F wmb1). Both follow from TicketLock same-object order and emission order, not from the extra waits, so they survive RE-04(b).
- rel_lin_pub / Judge 1: a handle-free contract. Handles are witness indices, and `contract_handle_invariant` proves the contract unchanged under any handle choice that agrees on same-thread I-dependent write pairs, given symmetric dto on the buffered write categories. This partially resolves [corrected 2026-10-13, F-1 review m-33: ix := 0 makes the contract vacuous; witness indices required; bridges (i) nu_handle_invariant and (ii) po_handles_vs_index still owed] the clash between `uev`'s ix := 0 (SeqLockModule.v:511) and `wf_cand.po_handles` (Declarative.v:59).
- Judge 2: a constant compE gives a joint underlay spec without an underlay J-variant. compE occurs in WindowLinkTable only as a parameter of BL lemmas and of `nuE_all` (:189, :199, :247, :266, :335, :353, :461), and ucomp comes from the owner (:167). Verified by grep.
- Judge 2 (refined here): copy and generalize SeqLockModule Section Execution/Transport (:688-1225) over an arbitrary underlay spec. Its dependence on the register spec is only `wit_replay`/`SX_wf` validity (:936-999); everything else goes through spec-generic BL lemmas. Verified by grep.
- MEM-FIRST: mechanize the refutation of the lp-anchored atomic interface (Atomic[sl] ⊗_Pc Buf[z] over plainTL). It is the paper's argument for why the marker must sit after the linearization point.
- Judge 1: the grounding bridge uses pre := (po \ I_tab) ∪ rt, so 'consistent ⇒ rel_lin' covers the real-time clause.
- Design 1/2: the barrier ghost locations Br ≠ Bw are distinct, matching same_obj OB OB = false (SeqLockCOH.v:182). Design 3's single β_t would order rmb against wmb.
- Commit the already kernel-checked Q6 scripts as a file instead of re-deriving them in BUF-0, Q6-0 or BP-0.
- Judge 1: do not print rel_lin_pub's claimed ARMv8 'RSW-through-object' gap. Judge 1 derives an ob cycle for it (Wx →bob Wz →rfe Rz1 →bob Rx →fre Wx). Add that litmus test, and a relaxed-LDADD-plus-plain-get test, to ARM-CHK/herd7.
- Keep BUF-ISSUE Stage A (product overlay `nu_sl` ⊗ hide(VBuf_z), with `window_link_table` unchanged) only as a fallback if WIN-J stalls. It loses `seqlock_client_mp_forbidden`.

## Phased plan

### Phase 0: lock in the evidence and the gates. No design commitment; every file is new.

- **Q6-1** (S; depends on: none)
  - Goal: Commit the kernel-checked Q6 refutations as a file.

Theorems: `q6_not_rel_lin`, the controls `q6_zr1_rel_lin` and `sb_rel_lin`, `q6_underlay_no_WF`, `ctl_wf`, and `q6_underlay_not_rel_lin`, with helpers `nuF_all_sl_after`, `field_const`, `replay_x1`, `zreg_1`.

The proof bodies of scripts B (sb_*) and D are only outlined in the confirmation record and must be re-derived from that outline.

The header states:
- the hardware 'Allowed' is a hand derivation pending herd7;
- the old module theorem is not contradicted, but its hypothesis fails on this execution.
  - Files: examples/Relaxed/SeqLockQ6.v (new); _CoqProject (one line after examples/Relaxed/SeqLockClients.v)
  - Acceptance: - `make examples/Relaxed/SeqLockQ6.vo` succeeds.
- `Print Assumptions` gives 'Closed under the global context' for each of the six named theorems.
- `Check (q6_not_rel_lin true)` and `Check (q6_not_rel_lin false)` both typecheck.
- The file does not import examples/Relaxed/SeqLockLB.v (grep).
- No existing file changes except the one _CoqProject line.
- **Q6-2** (S; depends on: Q6-1)
  - Goal: Kernel-check the real-time obstruction for register x/y (BUF-0(c)).

Theorem `rt_iteration_not_rel_lin`: build a module-shaped underlay trace (the same style as `q6_underlay_not_rel_lin`) in which:
- the writer's WrX(1) response precedes the invocation of a reader's RdX in a failed read iteration;
- that RdX returns 0;
- the reader later completes a successful iteration.

The trace must not be rel_lin under `sindep` w.r.t. `BL.nuE_all SL.comp_dec SLM.compE (SLM.nuEc rc plainTL)`.

Control `rt_iteration_overlap_rel_lin`: the same calls with the RdX invocation moved before the WrX response are rel_lin.
  - Files: examples/Relaxed/SeqLockQ6.v (extend)
  - Acceptance: - Builds.
- Both theorems are 'Closed under the global context'.
- The header records the outcome:
  - If the obstruction holds, x and y must be buffered under 'writes respond at issue'.
  - If it fails, report to the author: a z-only buffering variant then becomes a cheaper option.
- **Q6-3** (S; depends on: none)
  - Goal: memory/-level admission of the Q6 cells and of the real-time iteration.

Theorems:
- `sq_V`, `sq_nu` and `q6_cells_TSO_consistent` (script E);
- `rt_cells_nu`: a TSO_cfg trace with T2's W x 1 still pending while T1's R x reads 0, in nu.

The header lists what memory/ cannot express: rmb/wmb, RMW, ARM fences, and the retry loop.
  - Files: examples/Relaxed/SeqLockQ6Mem.v (new); _CoqProject (one line appended after memory/Litmus.v, because memory/ is listed after examples/Relaxed today: lines 189-202 vs 107-116)
  - Acceptance: - Builds.
- `sq_V`, `sq_nu` and `rt_cells_nu` are 'Closed under the global context'.
- `Print Assumptions q6_cells_TSO_consistent` ⊆ {classic}.
- memory/*.v is unchanged.
- **Q6-4** (S; depends on: Q6-1, Q6-2, Q6-3)
  - Goal: Update the records.

- research-intent §7 Q6: set the status to 'confirmed in Coq', naming Q6-1 to Q6-3, with the hardware part a derivation.
- concern-matrix: add rows for Q6 and for the real-time obstruction, with K/S/P/R recorded separately.
- tasks/SL-mem.md: mark item 3's direction as refuted as posed (cite `q6_cells_TSO_consistent` together with `q6_underlay_not_rel_lin`), and mark the task superseded by phase G.
- tasks/SL-tower.md: re-pose against the buffered spec.
- Do NOT edit §8; the author amends decisions.
  - Files: .rocq-review/research-intent.md, .rocq-review/concern-matrix.md, .rocq-review/tasks/SL-mem.md
  - Acceptance: - Every new claim cites a theorem name from Q6-1 to Q6-3, or is explicitly labelled 'derivation'.
- No paper or reviewer text is paraphrased without a file:line quote.
- §8 is untouched.

### Phase 1: foundations (new files only; memory/ stays independent of examples/)

- **F-1** (M; depends on: none)
  - Goal: Table-induced memory instance with ghost barriers.

- A Cfg whose locations include the ghost locations Bw ≠ Br. Categories are a parameter (Cat, to, cat). Define I_tab m m' := loc m ≠ loc m' ∧ to (cat m) (cat m') = false.
- Lemmas:
  - `I_tab_cross` (the HI hypothesis of declarative_characterization);
  - `declarative_tab` (the instance of `Equivalence.declarative_characterization`, :40);
  - `ppo_wmb_WW`: W→wmb→W' is in ppo (Declarative.v:133);
  - `ppo_rmb_RR`: R→rmb→R' is in ppo;
  - `contract_handle_invariant`: the contract is unchanged under two handle maps that agree on the order of same-thread write pairs with ¬I, assuming I is symmetric on writes.
  - Files: memory/TableBarrier.v (new); _CoqProject (after memory/Equivalence.v)
  - Acceptance: - Builds.
- `Print Assumptions` ⊆ {classic, eq_rect_eq} for every named lemma.
- No import of examples/ (grep).
- Non-vacuity, both instantiated with the abstract to := 'W/Wmb and R/Rmb ordered':
  - an MP+wmb/rmb trace has no nu witness;
  - an SB+rfi trace is in nu.
- Existing memory/ definitions are unchanged.
- **F-2** (M; depends on: F-1)
  - Goal: Hybrid memory and the SC-ify lemma.

Hybrid spec `HV` / `Hnu`: cells under V I_tab, atomic objects with a sequential spec, and the atomic clause.

Lemmas:
- `HV_no_atomic`: HV equals V when there are no atomic objects;
- `HV_prefix`;
- `HV_drain`: appending FIFO flushes preserves HV and hide;
- `scify_register`: for a set L of locations whose reads never forward, moving each L-write to its flush and deleting the flushes yields a register trace for L. Unmoved events keep their relative order, and a read returns the last published value. Built on `Pending.pending_iff`, `cg_last_flush` (:576) and `read_value` (:620).
  - Files: memory/Hybrid.v (new), memory/Publication.v (new); _CoqProject
  - Acceptance: - Builds.
- `Print Assumptions` ⊆ {classic, eq_rect_eq}.
- Positive instance: a trace where a pending independent DW write crosses an atomic op satisfies HV.
- Negative instance: a trace where a pending Wmb write crosses an atomic DRMW op violates HV.
- `scify_register` is instantiated on the Q6-3 trace for L = {x}.
- **F-3** (S-M; depends on: none)
  - Goal: Joint-spec window composition and link.

Composition: Hyps0J (h_S1J: a single nuJ on the lp-sorted list), ConclusionJ, and `window_composition_J`, proved via `WindowTable.conclusion_of_lp_before` (:148).

Link: PositionalJ and `window_link_table_J`, reusing the section lemmas of WindowLinkTable.

Also:
- `window_link_table_of_J`: conservativity; the product version follows with nuJ := nuF_all.
- A check lemma that a constant compE works for a joint underlay.
  - Files: examples/Relaxed/WindowTableJ.v, examples/Relaxed/WindowLinkTableJ.v (new); _CoqProject
  - Acceptance: - Builds.
- `Print Assumptions window_link_table_J` ⊆ `Print Assumptions WindowLinkTable.window_link_table` ⊆ baseline.
- `window_link_table_of_J` is proved.
- WindowTable.v and WindowLinkTable.v are unchanged.

### Phase 2: the SeqLock layer at witness level

- **S-1** (L; depends on: F-1, F-2)
  - Goal: Buffered SeqLock-layer executions and the SC-ify reduction.

Definitions:
- `BExec`: SeqLockCOH programs plus a hidden-trace witness of calls and flushes.
- `BWF`: upres pres on issue positions (upres unchanged), plus HV over {x, y, z, Bw, Br} ⊕ TL (SeqLockCOH.pre/post), with I_tab := ¬dto rc across locations.

Lemmas:
- `no_xy_forward` (F1);
- `scify`: BExec → z-free SeqLockCOH.Exec;
- `bwf_scify_WF`: BWF X → SeqLockCOH.WF rc K (scify X), for K_ok K;
- a monotone position map on unmoved events;
- `reg_to_buf`: SeqLockCOH.WF ⇒ BWF, by flushing immediately (conservativity).
  - Files: examples/Relaxed/SeqLockBuf.v (new); _CoqProject (after memory/ and the F-* files)
  - Acceptance: - Builds.
- `Print Assumptions bwf_scify_WF` ⊆ {classic, eq_rect_eq}.
- Non-vacuity: X_q6 (blocks q6p0/q6p1 of Q6-1) has a BWF witness, checked by a boolean checker with a soundness lemma, alongside `q6_underlay_no_WF`.
- SeqLockCOH.v is unchanged.
- **S-2** (M; depends on: S-1, F-3)
  - Goal: Overlay joint specification and its S1.

Definition `nuJ_SLZ`: the marker spec of design_summary.

Lemmas:
- `no_own_read_in_pending` (F2);
- `lp_order_agree`: lp order in the witness equals lp order after SC-ification, on SeqLock ops;
- `marker_before_next`: F(wmb1 w) < every later SeqLock lp, via wr_disjoint/ww_disjoint and the atomic clause;
- `seqlock_buf_S1`: nuJ_SLZ holds on the lp-sorted overlay;
- `nuJ_to_mem`: nuJ_SLZ ⊆ ν_{I_F}[{sl,z}] ∩ Lin_sl;
- `seqlock_z_composition_buf`: WT ConclusionJ, from setting_hyps0J and the reused `setting_inherit` (SeqLockCOH.v:1591).
  - Files: examples/Relaxed/SeqLockBufIface.v (new); _CoqProject
  - Acceptance: - Builds.
- `Print Assumptions` ⊆ baseline for all named lemmas.
- Non-vacuity:
  - X_q6 satisfies ConclusionJ;
  - a witness-level z-data MP execution (t1: zw(1); write(1,1) ‖ t2: read=(1,1); zr) forces zr=1 by the contract.

### Phase 3: module-level theorem

- **D-1** (L; depends on: none)
  - Goal: Generalize SeqLockModule's execution bridge over an arbitrary underlay spec.

Copy Section Execution/Transport (SeqLockModule.v:688-1225) with `Context (P : list (Op G) -> Prop) (HWu : rel_lin_witness … P Wu)`. Isolate validity (:936-999 `wit_replay`/`SX_wf`) as a section hypothesis, and give `positional_gen`.

Instance lemma `positional_of_gen`: recovers the existing `positional` (:1171) for the register nuEc.
  - Files: examples/Relaxed/SeqLockModuleGen.v (new); _CoqProject
  - Acceptance: - Builds.
- `positional_of_gen` is proved, and its `Print Assumptions` equals that of `SeqLockModule.positional`.
- SeqLockModule.v is unchanged (git diff empty).
- **D-2** (L; depends on: D-1, S-2, F-3)
  - Goal: The module theorem.

Specs:
- `nuE_hyb`: on Op lists, with compE constant, witness-index handles and F-1's invariance;
- `nuJ_F`.

Results:
- `positional_buf`, from D-1 plus S-1/S-2;
- `seqlock_buf_module_rel_lin`, and `seqlock_buf_module_rel_lin_K` (for K_ok), via `window_link_table_J`.

The header states:
- complete executions only;
- an atomic TicketLock;
- writes respond at issue;
- incomparable with `seqlock_module_rel_lin`, with a weaker hypothesis and a weaker z conclusion;
- x86-TSO only, ARMv8 open.
  - Files: examples/Relaxed/SeqLockBufModule.v (new); _CoqProject
  - Acceptance: - Builds.
- `Print Assumptions` ⊆ {classic, eq_rect_eq} for both theorems.
- The statement uses the unchanged `SeqLockProg.M`, `sindep` and `findep` (checked by `Check`).
- The header lists the four K/S/P/R levels.

### Phase 4: non-vacuity, refutations and clients

- **N-1** (M; depends on: D-2, Q6-1, Q6-2)
  - Goal: Concrete module executions, each with an explicit Hν underlay witness:
- T_q6: the hypothesis holds and the overlay is rel_lin w.r.t. nuJ_F. Its overlay projection is not rel_lin under the old interface (cite `q6_not_rel_lin`).
- T_rt: the Q6-2 iteration is admitted.
- T_lb, with `seqlock_buf_lb_not_classical`.
- T_mp.

Copy SeqLockLB's construction patterns; do not import it.
  - Files: examples/Relaxed/SeqLockBufExec.v (new); _CoqProject
  - Acceptance: - Builds.
- Named theorems: `seqlock_buf_q6_module`, `seqlock_buf_rt_module`, `seqlock_buf_lb_module`, `seqlock_buf_lb_not_classical`, `seqlock_buf_mp_module`.
- `Print Assumptions` ⊆ baseline.
- grep confirms SeqLockLB is not imported.
- **N-2** (M; depends on: N-1)
  - Goal: Refute the lp-anchored atomic interface at module level (MEM-FIRST B').

The execution: T1: zw(1); write(1,1); zw(2), where zw(2) returns before write does ‖ T3: zr()=0.
- First prove the frontier lemma: WrZ2 can be emitted before Rel (`must_precede`, RelaxedModuleSemantics.v:252).
- Then show the execution satisfies the nuE_hyb hypothesis, but its overlay is not rel_lin w.r.t. Atomic[sl] ⊗_Pc Buf[z] with publication at the lp.
- Show it IS rel_lin w.r.t. nuJ_F.
  - Files: examples/Relaxed/SeqLockBufRefute.v (new); _CoqProject
  - Acceptance: - Builds, with `Print Assumptions` ⊆ baseline.
- If the frontier lemma is false, stop. Report to the author, with the blocking `must_precede` clause, and drop the claim from the paper story.
- **N-3** (M; depends on: D-2, N-1)
  - Goal: Clients over nuJ_F.

SeqLock-only rules via a projection lemma nuJ → nu_sl, reusing `client_rule_same_epoch` (SeqLockClients.v:770) and `client_rule_read_not_future` (:786):
- equal_pairs;
- same_epoch;
- read_not_future.

MP results:
- `seqlock_buf_client_mp_forbidden`: z as data, both orders, re-proving the content of :1139/:871 with the contract;
- z-flag MP forbidden.

Allowed at interface level: Q6, SB and LB.

Instantiate everything on the N-1 executions.
  - Files: examples/Relaxed/SeqLockBufClients.v (new); _CoqProject
  - Acceptance: - Builds, with `Print Assumptions` ⊆ baseline.
- Each rule has at least one instantiation on an N-1 execution: a non-vacuity lemma that names it.

### Phase 5: tower and Counter (Tier B)

- **T-1** (L; depends on: none)
  - Goal: The inlined futures module M0 over own ⊗ nxt ⊗ x ⊗ y ⊗ Barrier ⊗ z, and its shape lemma. This is SL-tower part 1, unchanged: acq spin, silent test_ticket, following the SeqLockCOH/TicketLockCOH headers.
  - Files: examples/Relaxed/SeqLockTowerProg.v (new); _CoqProject
  - Acceptance: - Builds, with `Print Assumptions` ⊆ baseline.
- The shape lemma, `M0_shape`, states that every method trace is the trace of one SeqLockTower low-level block.
- **T-2** (L; depends on: S-1, S-2)
  - Goal: Bottom-level buffered witnesses.

`BWF0`: own and nxt are atomic RMW objects in the hybrid, with categories from TicketLockCOH CCats; x, y, z, Bw and Br are buffered.

Results:
- `bwf0_scify_WF0`: SC-ify to the unchanged `SeqLockTower.WF0` (:238);
- then `tower_link` (:1693), then `SeqLockCOH.WF`, then `seqlock_S1`;
- the marker and overlay at low-level positions, with the atomic clause transferred at the TL window calls.
  - Files: examples/Relaxed/SeqLockTowerBuf.v (new); _CoqProject
  - Acceptance: - Builds, with `Print Assumptions` ⊆ baseline.
- SeqLockTower.v and TicketLockCOH.v are unchanged.
- Non-vacuity: a low-level Q6 execution satisfies BWF0.
- **T-3** (L; depends on: T-1, T-2, D-1, F-3)
  - Goal: Tower module theorem `seqlock_tower_buf_module_rel_lin`.

- Hypothesis: rel_lin of the low-level underlay w.r.t. Hν0.
- Conclusion: rel_lin of the overlay w.r.t. nuJ_F.
- Proof: via `window_link_table_J`, with a D-1-style generic decode copy for M0.
- The header states: one inlined module, not general vertical composition; complete executions only.
  - Files: examples/Relaxed/SeqLockTowerBufModule.v (new); _CoqProject
  - Acceptance: - Builds, with `Print Assumptions` ⊆ baseline.
- The remaining hypothesis mentions only low-level objects (checked by `Check`).
- **T-4** (S-M; depends on: F-2, F-3)
  - Goal: Counter layer.

- ν_Counter, with inc = faa(1) and get = rd on own as an atomic faa register.
- A module theorem with identity windows.
- A lemma identifying the tower's own with it.
- The header states honestly that this layer is near-identity, because memory/ has no RMW (RE-22).
  - Files: examples/Relaxed/CounterAtomic.v (new); _CoqProject
  - Acceptance: - Builds, with `Print Assumptions` ⊆ baseline.
- Non-vacuity: a two-thread inc/get execution.

### Phase 6: memory/ grounding

- **G-1** (M-L; depends on: F-1, F-2, D-2, Q6-3)
  - Goal: History-level bridge.

`cell_part_of_consistent`: an OMCA-consistent candidate (D1∧D2) of the cell and barrier operations, with I_tab and pre := (po\I_tab) ∪ rt (admissibility proved), yields the cell part of nuE_hyb.

The atomic objects (TL, own, nxt) remain an explicit hypothesis.

Also:
- IRIW+rmb has no witness (RE-23);
- instantiate on the Q6-3 candidate.
  - Files: examples/Relaxed/SeqLockMem.v (new); _CoqProject
  - Acceptance: - Builds.
- `Print Assumptions` ⊆ {classic, eq_rect_eq}.
- The header states the remaining hypotheses: atomic RMW objects, complete executions, and the history-level link only (no LTS).
- **G-2 (optional)** (XL; depends on: G-1, T-3)
  - Goal: x86-TSO machine with locked RMW (empty-buffer guard), and a forward simulation into HV.

Then VE_TSO and `seqlock_x86_end_to_end`: every complete execution of M0 over VE_TSO is rel_lin w.r.t. nuJ_F, with no underlay hypothesis.
  - Files: memory/TSORMW.v, examples/Relaxed/SeqLockX86.v (new)
  - Acceptance: - Builds, with `Print Assumptions` ⊆ baseline.
- `Check` shows no rel_lin hypothesis on the underlay.
- **G-3 (optional, research)** (M; depends on: F-1)
  - Goal: ARM-CHK: add dmb ld/st and RMW flavours to a copy of ARM.v's bob. Then check:
- the Q6 litmus tests;
- the RSW-through-object test from Judge 1, expected Forbidden;
- relaxed LDADD + plain-LDR get against the atomic clause.

Report only.
  - Files: memory/ARMBar.v (new)
  - Acceptance: - Builds.
- Each litmus verdict is a named lemma.
- No soundness claim is made.

### Phase 7: headers and records (author approval needed for edits to existing headers)

- **R-1** (S; depends on: D-2, author OK)
  - Goal: Comment-only header notes. The register-cell results are the forwarding-free instance [SUPERSEDED 2026-10-13: see 'Amendments after Phase 0 review' at the end — old results are removed from the paper's table and cover only publication-at-response, forwarding-free underlays]; Q6 (`q6_underlay_not_rel_lin`) and Q6-2 show their hypothesis fails on x86 executions with store forwarding; point to the SeqLockBuf* files.

Also update the concern matrix: the new theorems become the oMCA result, and the old ones are not cited for it.
  - Files: examples/Relaxed/SeqLockCOH.v, examples/Relaxed/SeqLockModule.v, examples/Relaxed/SeqLockClients.v (headers only); .rocq-review/concern-matrix.md
  - Acceptance: - `git diff` shows changes inside the leading comment blocks only.
- `make` succeeds.
- SeqLockLB.v is edited only after its concurrent editing ends.

## What survives

Unchanged and still true, reused directly:
- **SeqLockProg** (all of it): M (:251), M_shape, E/F, sindep (:170), fcat (:194), findep (:208). The printed futures program is still the verified one.
- **WindowTable** (all of it): dto (:460), Hyps0 (:118), Conclusion (:138), conclusion_of_lp_before (:148), window_composition (:228).
- **WindowLinkTable.window_link_table** (:461) and its section lemmas. The J variant is built on them, and window_link_table itself remains the fallback for a product overlay.
- **TicketLockCOH** (all of it, including ticketlock_S1), because own and nxt are written only by RMWs and so stay atomic.
- **memory/*** (all of it, unedited): Cell (V :624, nu :627, contract :603, VBuf :317), Pending (cg_last_flush :576, read_value :620), Tensor (memory_tensor, contract_proj_closed :498), Equivalence (declarative_characterization :40, generic in I), Declarative, TSO.

Reused through SC-ification, with no edit:
- **SeqLockCOH:**
  - Part A;
  - Part B: seqlock_S1 (:1267), seqlock_S1_ord (:1339), wr_disjoint (:1013), ww_disjoint (:1045), read_value (:1150);
  - Part C: setting_inherit (:1591).
- **SeqLockTower:** WF0 (:238) and tower_link (:1693), including X1_wf.

Reused by copy-and-generalize:
- **SeqLockModule:**
  - the spec-free part of Section Execution/Transport (:688-1225): decode, parse, phi, SX, ix, src_order;
  - E_compat (:549), F_cross (:555), window_bodies (:638).

Still true, but describing the old, register-cell (forwarding-free) interface:
- **SeqLockCOH:** z_S1 (:1377), seqlock_z_composition (:1601), and the Part D refutations.
- **SeqLockModule:** seqlock_module_rel_lin (:1247) and seqlock_module_rel_lin_K (:1230). Their hypothesis is unsatisfiable on Q6 (`q6_underlay_not_rel_lin`) and, if Q6-2 confirms, on TSO failed-iteration runs.
- **SeqLockClients:**
  - Reusable through a projection lemma: client_rule_same_epoch (:770) and client_rule_read_not_future (:786). fcat_cross_table (:617) and read_zr_dependent (:630) are reused directly.
  - nuF_all_z_after (:582), client_rule_mp_zr_value (:871), seqlock_client_mp_forbidden (:1139) and _K (:1101), and the Part 5 mp_trace lemmas remain register-interface facts.
- **SeqLockLB:** seqlock_lb_module (:888), seqlock_lb_not_classical (:953), seqlock_mp_module (:1189) and seqlock_mp_nonvacuous (:1222) remain old-interface facts. These lines may shift because the file is being edited concurrently.
- SeqLockModuleExample.v and SeqLockRT.v are presumably in the same position (forwarding-free instance [SUPERSEDED 2026-10-13: see 'Amendments after Phase 0 review' at the end — old results are removed from the paper's table and cover only publication-at-response, forwarding-free underlays]), but not inspected.

## What is redone

All of the following go into new files:

1. **Underlay spec:** the register replay nuEc (SeqLockModule.v:534, replay :517, zreg :523) becomes the hybrid Hν. It has buffered x, y and z, ghost barriers Bw and Br, I_tab, an atomic TicketLock, and the atomic clause.
2. **Overlay spec:** the product nu_sl ⊗ nu_z (nuFc :543, via BL.nuF_all) becomes the joint marker spec nuJ_SLZ. A corollary places it inside ν_{I_F}[{sl,z}] ∩ Lin_sl.
3. **SeqLock S1:**
   - z_S1 becomes the identity projection;
   - seqlock_S1 is reached through scify, lp_order_agree and marker_before_next;
   - seqlock_z_composition is replaced by a ConclusionJ version.
4. **Composition:** WindowTableJ and WindowLinkTableJ, thin variants of the existing composition and link theorems.
5. **Module level:**
   - positional is redone as positional_buf over a generalized copy of SeqLockModule's bridge;
   - the module theorem statement becomes seqlock_buf_module_rel_lin(_K). It is incomparable with the old one.
6. **Clients and executions:**
   - the client theorems that involve z (MP with z as data or as flag);
   - the non-vacuity executions T_q6, T_rt, T_lb and T_mp, rebuilt without importing SeqLockLB.v.
7. **Tower and grounding:**
   - the tower module theorem, a new task replacing the plan in SL-tower.md;
   - the Counter layer;
   - the memory/ bridge, which replaces SL-mem items 1-3.

**Not redone, contrary to the 2026-10-13 decision text:**
- the categories;
- the table;
- I;
- the futures program;
- the windows.

This needs the author's sign-off (question 1).

## Risks

- The SC-ify reduction depends on a code property. x/y/wmb writes occur only inside critical sections and are never forwarded (F1/F2). This holds for SeqLockProg.M and the inlined M0. It breaks if the code changes (e.g. a writer reads x), and it relies on TL same-object order plus emission order.
- D-1 effort: about 540 lines of SeqLockModule.v (:688-1225) are copied and generalized. The dependence on the register spec is confined to :936-999 (checked by grep), but index bookkeeping may push D-1 or T-3 beyond L.
- The constant-compE trick assumes the BL lemmas (wu_src, wu_key_inj, before_pos, inv_order, link_rt) are generic in compE and nuEc. They take both as parameters (grep), but F-3 must confirm it in the kernel.
- The handle invariance (`contract_handle_invariant`) depends on dto being symmetric on the buffered write categories. I checked: DW/DW false both ways, DW/Wmb true both ways, Wmb/Wmb true. Adding Wrel/Racq categories, or an asymmetric table, would require program-order handles (Mem.tex Assumption handles) instead.
- ARMv8 is not established. memory/ARM.v has no fences or RMWs. The atomic-RMW-at-a-point abstraction needs LDADDAL with LDAR gets, and relaxed LDADD with plain gets may break the atomic clause. The paper may claim x86-TSO only until G-3 and herd7 have run. Do not print Design 3's 'RSW-through-object' ARM limitation; it is contested by Judge 1's ob-cycle derivation.
- RMW is not in memory/ (RE-22, XL). TL, own and nxt are atomic objects by hypothesis, so declarative grounding covers only cells and barriers (G-1). The hypothesis-free result is the optional G-2 (XL).
- The overlay is a joint, non-product spec. Product compositionality ⊗ is lost for buffered objects in the running example, and Mem.tex defines the contract tensor only for cells (Mem.tex:214-221, per the designs; not re-verified here). The paper must state the change of the exported spec from ν_SeqLock ⊗ ν_COH[z].
- The new module theorem is incomparable with seqlock_module_rel_lin: its hypothesis is weaker, and its z conclusion is weaker. The concern matrix must stop citing the old theorem as the oMCA result.
- By design, z has no real-time freshness: a returned zw may be unpublished. Any paper claim relying on freshness of z becomes false.
- N-2's refutation of the lp-anchored interface rests on a derivation that the emission frontier lets WrZ2 overtake Rel. If false, the marker is still sound, but the paper loses its motivating counterexample.
- The confirmation record only outlines the proofs of scripts B (sb_*) and D (`q6_underlay_not_rel_lin`). Q6-1 must re-derive them, which may cost an extra iteration.
- SeqLockLB.v is under concurrent edit. No new file imports it, and its line numbers may shift.
- Build order: memory/ is listed after examples/Relaxed in _CoqProject (lines 189-202 vs 107-116). New example files that import memory/ must be appended after line 202. Reordering the existing lines would be an unrequested change.
- Only complete executions are covered. There is no general vertical composition: the tower is one inlined module (RE-17/18).
- Budget for full Tier B: about 20-28 Writer iterations, plus XL for the optional G-2.

## Alternatives rejected

**BUF-ISSUE as proposed** (judge scores 6.5 / 5.5). Rejected for four reasons:
- Stage A as a deliverable regresses `seqlock_client_mp_forbidden` (SeqLockClients.v:1139).
- BUF-1's 'statements unchanged' WF_core refactor would weaken `Hypothesis HW : WF rc K X` in `Section Layer` (SeqLockCOH.v:713-715). That changes the signatures of the roughly 30 lemmas called by SeqLockModule, SeqLockTower, SeqLockClients and SeqLockLB, and it breaks SL-tower's acceptance rule.
- Its claim that SeqLockModule's Section Execution is spec-free is wrong at the type level: HWu, typed with the register nuEc (:695-696), is needed by wu_src (:807), wu_key_inj (:876) and wit_replay (:942).
- The tower had no reuse path.

Grafted from it: the marker interface, the gates and the atomic clause.

**MEM-FIRST's overlay ν_{I_F}[{sl,z}] ∩ Lin_sl as the primary spec.** Rejected:
- It is weaker than the marker spec: it allows another thread's SeqLock write between a write's issue and its publication.
- It needs Cantor pairing.
- Lin_sl is not a memory/ notion.

It is kept as a proved corollary (`nuJ_to_mem`). MEM-FIRST's X86-M/X86-E2E is demoted from the critical path to optional (XL).

**rel_lin_pub (Design 3)** (judge scores 5 / 4.5). Rejected for five reasons:
- It changes Def. 3.14/rhb, which goes beyond the author's spec-only decision. It needs WindowPub and WindowLinkPub (realistically XL), and it cuts the example off from GSimRel/ViewLHL, which are stated for rel_lin.
- BufPair puts real time on issue only, so the SeqLock is not linearizable even among its own operations.
- Its ARMv8 'RSW-through-object' limitation is contested by Judge 1's ob-cycle derivation, so it must not be printed.
- A single per-thread barrier location β_t contradicts same_obj OB OB = false.
- It has the highest effort (18-28 iterations).

Grafted from it: the handle-free contract and the no-forwarding facts F1/F2.

**Options listed in Q6 (research-intent.md:100):**
- *Restrict to forwarding-free (MCA-like) cells:* contradicts the decision 'scope = oMCA' (:104). It survives only as the label for the old files.
- *Make rmb drain, or order a read after a same-location write:* changes the code mapping (rmb becomes a full fence), which the author decision excludes. Design 2 also shows a draining wmb is unsound for TSO when rmb is a no-op.

**Rejected inside Design 1's analysis:**
- *A new category that drops the zr→read edge:* unsound once a sequential client waits on zr, and it loses z-flag MP.
- *Putting (zw, zr) into I:* the emission frontier could then emit a read before its own write, which loses read-own-write coherence.

**Buffering z only:** admits Q6, but under the issue-time response convention it is refuted by the real-time obstruction (to be kernel-checked in Q6-2). It is reconsidered only if Q6-2 fails or the author chooses publication-time responses.

## Questions for the author

- The judges found no reason to change the categories, the table, findep/sindep, the futures program or the windows: only the object specifications change. May the 2026-10-13 Q6 decision ('redo seqlock_S1, the categories and the module proof') be amended to 'redo the specifications, seqlock_S1's reduction and the module proof; the categories stay'?
- Exported interface. The recommended spec is the SeqLock as an atomic pair register (nu_sl) with a hidden publication marker before its next operation, joint with Buf[z] under the contract read off findep. It is a contract tensor, not ⊗, and it keeps z-data MP forbidden. ν_{I_F}[{sl,z}] ∩ Lin_sl ('SeqLock ⊎ z is a two-location buffered memory') is a proved corollary. Which one goes in the main text? Do you accept the loss of the product ⊗ for this example?
- Memory interface convention. Plain writes respond at issue (memory/'s atomic blocks), so a returned z write need not be visible to other threads. This is what forces x and y, not only z, to be buffered (task Q6-2). Confirm? Does any planned claim rely on z being visible once zw returns?
- Hardware scope. Is it acceptable to claim x86-TSO only, with ARMv8 open, and the TicketLock/own/nxt as atomic RMW objects under a disclosed hypothesis (locked RMW on x86; LDADDAL with LDAR gets on ARM)? Will you run herd7 (x86tso.cat, aarch64.cat) on the SeqLockZ+rfi tests, the minimal cores, Judge 1's RSW-through-object test and the LDADD-plus-plain-get test?
- Tier B scope. Is the Counter layer acceptable as a near-identity module over own as an atomic faa register (memory/ has no RMW; RE-22 is XL)? Is the history-level declarative bridge (G-1) enough for 'memory/ grounding', with the x86 end-to-end theorem (G-2, XL) optional?
- Existing files. May their headers get comment-only notes labelling them the forwarding-free instance [SUPERSEDED 2026-10-13: see 'Amendments after Phase 0 review' at the end — old results are removed from the paper's table and cover only publication-at-response, forwarding-free underlays] (task R-1)? Do they stay in the paper's mechanization table as that instance, or are they retired?

## Judges

### Recommendation

**Verdict.** Adopt Design 2's exported interface and story: ν_{I_F}[{sl,z}] ∩ Lin_sl, which is the same specification as Design 1 Stage B. Build it with Design 1's staging and gates. Do not change rel_lin.

**Sources checked:**
- dto, both rc, in a piped repl: DR/Rmb, Rmb/DR, DW/Wmb, Wmb/DW, Wmb/DRMW, DRMW/Wmb, Rmb/DRMW and DRMW/Rmb are ordered; DW/Rmb, Wmb/DR, DW/DRMW, DRMW/DW, DR/DRMW, Rmb/Wmb and Wmb/Rmb are not.
- I re-ran q6_underlay_no_WF independently: closed under the global context.
- must_precede (RelaxedModuleSemantics.v:252-258) orders two invocations only if they are not semi-independent.
- uev sets ix := 0 (SeqLockModule.v:511).
- declarative_characterization (Equivalence.v:40) needs only HI.
- memory/ARM.v:1-26 has no fences and no RMWs.

**Findings.**
1. All three designs admit Q6.
2. All three are sound for x86-TSO by derivation: x86's FIFO buffer makes the contract vacuous, and locked RMWs satisfy the atomic clause.
3. All three stay within oMCA.
4. None has an ARMv8 proof. With the decision "scope = oMCA", the paper may claim only x86-TSO until an ARM check of the exact fragment exists. The ARM mapping of the atomic-RMW-at-a-point abstraction needs LDADDAL with LDAR gets. With relaxed LDADD and plain gets, ARM lets a later read be satisfied before the RMW's write propagates, which the hybrid forbids.
5. The categories need not change. The four Q6 edges are genuine issue-order edges. Only the value-derived edge that comes from the register spec is wrong.
6. Design 1's real-time obstruction should be kernel-checked first. With writes responding at issue, register x/y plus rhb's real-time clause already refute an x86-allowed failed read iteration, so the current seqlock_module_rel_lin hypothesis is unsatisfiable on many TSO executions, independently of Q6.
7. Design 3's rel_lin_pub is principled but escalates beyond the author decision. It also exports a non-linearizable SeqLock, and its ARMv8 RSW-through-object claim is false.

**Order of work:**
1. Mechanize the Q6 lemmas from the confirmation: overlay, underlay, controls, and the memory/ TSO admission.
2. Prove the real-time obstruction lemma.
3. Prove the module-level refutation of Atomic[sl] ⊗_Pc Buf[z].
4. Run herd7 (x86tso.cat, aarch64.cat) on the SeqLockZ+rfi tests.
5. Build Stage A with WindowLinkTable unchanged, disclosed as incomparable with the old theorem.
6. Build the joint-spec J variants and Stage B, which restores seqlock_client_mp_forbidden.
7. Do history-level grounding with pre ⊇ po\I ∪ rt.
8. Optionally, the x86 end-to-end theorem.

**Paper consequences.** The paper must retract rem:ra-tso (trace.tex:262) and the claims that all models share the register spec and that COH is not MCA. It must state that the exported specification changed from ν_SeqLock ⊗ ν_COH[z] to a contract tensor.

- BUF-ISSUE (Design 1): buffered cells from Mem.tex under the unchanged table. rhb orders issues, and a contract read off the table orders publications. Stage A uses a product overlay; Stage B uses a joint contract tensor with publication markers.
  - Score: 6.5
  - Strengths: - **Faithful to the framework.** rel_lin and rhb (RelaxedTraceLin.v:60-65), sindep/findep/fcat (SeqLockProg.v:170/:194/:208) and dto (WindowTable.v:460) are all unchanged. Only the specifications change, which is exactly what the author decision authorizes (research-intent.md:109).
- **Diagnosis is correct.** I re-evaluated the table in a piped repl, for both rc. All four Q6 edges are real issue-order edges:
  - zw<zr: same object;
  - DR→Rmb = 1 and Rmb→DR = 1;
  - write<read: same component.
  Under x86 (rmb/wmb no-ops, in-order issue) and ARMv8 (dmb ld/st) these are genuine program-order constraints. The wrong edge is the value-derived one. So the categories do not need to be redone, contrary to the decision text. I agree with this.
- **It finds a second, independent unsoundness of the current hypothesis.** With writes responding at issue (memory/'s atomic blocks), the real-time clause of rhb plus register x/y already refutes a failed read iteration that x86 allows. So all plain cells must be buffered, not only z.
- **The atomic-contract is necessary and correctly stated.** I checked dto(Wmb,DRMW) = 1 and dto(DW,DRMW) = 0.
- **Stage A is sound and cheap.** compE occurs only in nuE_all, and the underlay component is taken from the owner (WindowLinkTable.v:167), so window_link_table applies unchanged.
- **It identifies a necessary refinement.** A contract anchored at the linearization point fails, so a later marker at flush(Wmb1) is needed.
- **It discloses incomparability.** It states that the new module theorem is incomparable with seqlock_module_rel_lin.
- **It proposes the right gate.** BUF-0 (a)-(d) comes first.
  - Fatal flaws: None found that would make it unsound for x86-TSO. Four issues block it from being the paper's running example as described:

(1) **Stage A drops the flagship client theorem.** It loses seqlock_client_mp_forbidden (SeqLockClients.v:1139; z-data MP), which is forbidden by both x86 and ARMv8. The headline "interface unchanged" is misleading. Only the categories and I are unchanged. The exported specification becomes, in Stage B, a non-product contract tensor with hidden markers. That is a change of ν_F, and the paper must say so.

(2) **handle := ix cannot be expressed by a ν on Op lists.**
- SeqLockModule.uev sets ix := 0 (SeqLockModule.v:511).
- Module handles are only fresh (RelaxedModuleSemantics.v:187-200; RelaxedSemantics.v:56).
- The contract must therefore use witness-index (issue-order) handles. That is correct here only because every dependent write pair is rhb-ordered. This needs a stated invariance lemma.

(3) **ARMv8 soundness is implied but not established.** The text implies it: "wmb ↦ DMB ISHST", and BUF-8 "answers RE-20 in the ARM direction". But:
- memory/ARM.v:1-26 has no fences and no RMWs;
- memory/ grounds only the paper's own OMCA D1/D2, which Mem.tex:681-694 shows is strictly stronger than ARMv8 on RSW+acq;
- the atomic-RMW-at-a-point abstraction needs LDADDAL/LDAR, which Design 1 notes only as a risk.

(4) **BUF-8's history-level bridge omits real time.** It does not put the real-time part of rhb into pre. Declarative.ppo (:133) depends on pre, so 'consistent ⇒ underlay rel_lin' needs pre ⊇ po\I ∪ rt, plus an argument that the hardware execution stays D2-consistent with that pre.
  - Fixes: - **Stage A:** keep it only as a milestone. The paper's running example needs Stage B.
- **Exported spec:** rename the claim to "categories and I unchanged; exported spec changed to a contract tensor". Record it as a definition change in the concern matrix.
- **Handles:** replace handle := ix by witness index. Prove `contract_handle_invariant`: the contract depends only on the order of I-dependent same-thread write pairs, and rhb fixes that order.
- **Scope:** state x86-TSO as the only proved hardware target. Add an ARM-CHK task on the exact fragment: plain R/W, dmb ld/st, and RMW with the stated LSE mapping.
- **BUF-8:** use pre := po\I_tab ∪ rt and prove admissibility.
- **Gate:** run BUF-0(c), the real-time obstruction, as a kernel lemma before any spec work, because it changes the justification for buffering x and y.
- **Tooling:** run herd7 on the Q6 litmus tests.
- MEM-FIRST (Design 2): the SeqLock as a buffered memory location. The overlay is ν_{I_F}[{sl,z}] ∩ Lin_sl. Barriers are ghost-location accesses, atomic objects take part in the flush contract, the register proof is reused by SC-ification, and there is an x86 end-to-end target.
  - Score: 7.5
  - Strengths: - **Best story for a weak-memory reviewer.** SeqLock ⊎ z refines memory/'s own two-location buffered memory, by memory_tensor (Tensor.v:562). Clients can therefore use litmus reasoning:
  - declarative_characterization (Equivalence.v:40) needs only HI (cross-location), so I_tab qualifies;
  - Q6 becomes SB+rfi through the object, exactly Mem.tex:5-13 and Reviewer A's test (popl2027-reviews.md:69-81);
  - MP becomes a D2 cycle.
- **The SC-ification reuse is correct.** I re-derived every upres pair after moving the x/y/wmb writes to their flushes:
  - Acq < Iss(wmb1) < F(wmb1) < F(Wx) < F(wmb2) < Rel;
  - Rmb and the reads stay at issue;
  - Wmb–Wmb pairs follow the contract;
  - Wmb–DRMW pairs follow the atomic clause.
  So SeqLockCOH.WF and seqlock_S1 are reused with no edit to existing files.
- **It finds a real constraint on the exported interface.** Atomic[sl] ⊗_Pc Buf[z] fails over a relaxed-RMW lock. I checked the premise: must_precede (RelaxedModuleSemantics.v:252-258) orders two invocations only if they are not semi-independent, and (DRMW,DW) is independent. So WrZ2 can overtake Rel, and the write needs a separate publication point. It also shows why a draining wmb is unsound.
- **Scoping is honest.** It claims x86-TSO only and leaves ARMv8 open.
- **Lin_sl keeps SeqLock-only clients linearizable.**
- **Strongest grounding target.** X86-E2E removes the underlay hypothesis for x86, which addresses the "underlay assumed rel_lin" risk pattern directly.
  - Fatal flaws: None found for x86-TSO soundness. Material gaps:

(1) **Joint, non-product overlay.** Horizontal compositionality for buffered objects is lost. The paper's ⊗ must become Mem.tex's contract tensor ⊗_Pc (Mem.tex:214-221) applied to objects, which Mem.tex defines only for cells.

(2) **Lin_sl is not a memory/ notion.** The "SeqLock implements a memory location" claim covers only the ν conjunct, and the declarative corollary says nothing about Lin_sl.

(3) **Handle conventions conflict.** Witness-index handles violate wf_cand.po_handles (Declarative.v:59) for independent underlay writes (WrX/WrY may issue out of program order). So the declarative grounding of the underlay needs a handle re-keying lemma, which MEM-HYB's 'order-preserving renaming' does not cover.

(4) **The oMCA decision is met only for x86.** The author decision targets oMCA, which includes ARMv8.

(5) **X86-M is XL new metatheory** (locked-RMW TSO machine plus forward simulation). The SeqLockModule Execution/Transport copies (SeqLockModule.v:688-1225, bound to HWu with the register nuEc :534) may also exceed L.

(6) **The atomic-sl refutation and the draining-lock variant are derivations,** not mechanized.
  - Fixes: - **Paper naming:** state the interface as "contract tensor of a buffered pair location with Buf[z], intersected with Lin_sl". Name the loss of product compositionality.
- **Mechanize the refutation:** turn the Atomic[sl] ⊗_Pc Buf[z] refutation into a module-level non-rel_lin lemma (SL-BUF-REF item 2). It is the paper's best argument for the interface shape.
- **Handles:** add a contract-invariance lemma for handle choices that agree on dependent same-thread write pairs. Use ix-handles for the declarative bridge and witness-index handles for ν.
- **Lin_sl:** keep it, but call it a separate object-level conjunct in the paper.
- **Plan the grounding in two tiers:**
  1. History-level grounding through declarative_characterization with pre ⊇ po\I ∪ rt (L).
  2. X86-E2E as the stretch goal.
- **ARM:** schedule ARM-CHK before any claim. Run herd7 on the Q6 litmus tests now.
- rel_lin_pub (Design 3): publication-point relaxed linearizability. Witnesses contain Iss/Pub events, rhb gains a third clause on publication points, the SeqLock becomes a BufPair cell over Buf[x] ⊗ Buf[y] ⊗ Barrier composed with Buf[z], and the proof is by retiming.
  - Score: 5
  - Strengths: - **Principled formulation.** A single sequential witness with issue and publication points belongs to the TSO-linearizability line of work (Burckhardt–Gotsman–Musuvathi–Yang 2012; Derrick–Dongol et al.), which reviewers recognize.
- **ν stays a product.** The cross-object publication order moves into rhb.
- **The contract uses trace invocation order on dependent pairs instead of handles.** This removes Mem.tex's Assumption handles and its open \todo (Mem.tex:98-103). This is the cleanest treatment of the handle problem among the three designs.
- **It is conservative over rel_lin** when nothing is buffered.
- **Retiming reuses** SeqLockCOH, TicketLockCOH and tower_link.
- **Its outcome claims check out:**
  - Q6 is admitted;
  - MP is forbidden in both orders. I re-derived Pub(zw) < Pub(write) < read < zr < Pub(zw).
  - Fatal flaws: (1) **It redefines the core notion.** It changes Def. 2.1/3.14: XEv witnesses and an rhb clause (iii). The author decision (research-intent.md:109) authorizes spec changes only, so this is a research-level escalation. Consequences:
- all window and link metatheory must be redone (WindowPub, WindowLinkPub);
- the running example is cut off from GSimRel/ViewLHL, which are stated for rel_lin;
- the Mem.tex appendix must be rewritten, or BP-17 proved.

(2) **The SeqLock is no longer linearizable even among its own operations.** BufPair has real time on issue only. A read invoked after a write has returned may return the old pair. This is a regression from nu_sl and from the current seqlock_client_read_not_future, and a POPL reviewer would attack it.

(3) **The claimed ARMv8 gap, "RSW through the object", is mis-derived.**
- T1's zr()=1 is in program order before the read's DMB LD, so [R];po;[dmb.ld];po orders it before LDR x.
- T2's DMB ST orders STR x before STR z.
- Hence Wx →bob Wz →rfe Rz1 →bob Rx →fre Wx is an ob cycle, so ARMv8 forbids the outcome.
- In the interface, zr1<read is a direct dto(DR,Rmb) edge, not transitivity through forwarding.
- Printing this as a limitation would be a false paper claim.

(4) **The barrier encoding contradicts the table.** A single per-thread β_t serves both rmb and wmb, which makes them a same-location, ordered pair. The table has same_obj OB OB = false and upres RmbC WmbC = false (SeqLockCOH.v:182). The memory bridge is therefore not an equivalence.

(5) **The Pub(wmb) ghost** is a non-standard device, and its equivalence with a closure formulation is not proved.

(6) **Largest effort:** 18-28 iterations.
  - Fixes: - **Defer the definition change:** do not change rel_lin for the running example. Escalate clause (iii) as a research option for the paper's general theory.
- **If it is pursued anyway:**
  - add a real-time clause on publication points for objects whose writes publish before they respond. The SeqLock has this property, since Pub(wmb1) < Rel < response. Alternatively, add a Lin_sl conjunct, so that the SeqLock stays linearizable;
  - use two per-thread barrier locations;
  - delete the RSW-through-object claim, or check it with herd7 first. Expected result: Forbidden;
  - prove BP-17, so that Mem.tex is backed literally.
- **Graft one idea into Designs 1/2:** compare invocation order on dependent pairs instead of handles.

### Recommendation

Use MEM-FIRST's architecture with BUF-ISSUE's interface, and drop rel_lin_pub. Concretely:

**What stays.** rel_lin, rhb, sindep/findep, the categories, the table, the futures program and the windows are unchanged. All three designs keep them, and no design shows a reason to "redo the categories". The author decision should be amended to say that only the specs change.

**Specs.**
- x, y and z become buffered cells (memory/ Cell with I_tab).
- wmb/rmb become ghost-location accesses.
- The TicketLock, own and nxt stay atomic. A small atomic clause makes pending dependent writes publish before a DRMW op.

**Main proof route: SC-ify, not refactor.**
- Map each buffered SL-layer witness to a z-free SeqLockCOH.Exec ordered by publication point. Prove SeqLockCOH.WF for it.
  - pres comes from the contract and the atomic clause.
  - Validity comes from Pending.read_value/cg_last_flush and the fact that a reader never has pending x/y.
- Apply seqlock_S1/seqlock_S1_ord unchanged.
- Do the same at the bottom level to get SeqLockTower.WF0, then tower_link unchanged.
- This keeps SeqLockCOH.v and SeqLockTower.v untouched. That is the decisive reuse argument against BUF-1's in-place WF_core refactor.

**Overlay.** Use the joint contract from day one: an atomic nu_sl with a hidden publication marker at F(wmb1) before the next SL op, plus Buf[z] under the findep contract. This goes through a ~150-line J-variant of WindowTable/WindowLinkTable, with compE constant for the joint underlay. It preserves seqlock_client_mp_forbidden and avoids a Stage-A regression.

**Budget correction.** Budget an explicit copy-adapt of SeqLockModule.v:688-1225. phi_lpq, S1_transport, wu_src, idx_pos and SX_wf are typed against the register nuEc (I checked this with `Check`). Alternatively, ask the author for a statement-preserving generalization.

**Critical path to Tier B, about 20–28 Writer iterations.**
1. Q6 file. Commit the existing kernel-checked scripts. Add the real-time obstruction for register x,y. (S)
2. memory/ table-I barrier instance and the atomic clause. (M)
3. Publication/SC-ify lemma and the buffered SL witness model. (L)
4. WIN-J. (S-M)
5. Overlay joint S1 with the marker. (M)
6. Module theorem, with the SeqLockModule copy-adapt. (L)
7. Q6/LB/MP module executions and clients. (M+M)
8. Inlined M0 program and shape lemma. (L, from SL-tower)
9. Bottom-level SC-ify, then tower_link, then the tower module theorem. (L+M)
10. Counter over an atomic faa register. (S; note that it is nearly an identity layer)
11. Declarative cells+barriers bridge, history level. (M-L)
12. Optional: x86 TSO LTS for a hypothesis-free end-to-end theorem. (XL)

**Records to update now.**
- SL-mem's planned direction is refuted as posed.
- If the real-time obstruction is confirmed, record that the current seqlock_module_rel_lin hypothesis fails on TSO runs with failed read iterations even without z (concern-matrix A2/B5).
- The register development should be kept and labelled as the forwarding-free instance [SUPERSEDED 2026-10-13: see 'Amendments after Phase 0 review' at the end — old results are removed from the paper's table and cover only publication-at-response, forwarding-free underlays].

- BUF-ISSUE (buffered cells from Mem.tex; table, rhb and rel_lin unchanged; Stage A product, Stage B contract tensor)
  - Score: 5.5
  - Strengths: 1. Smallest semantic change. rel_lin, rhb, sindep/findep, the categories, the futures program and the windows all stay as they are. Only the specs change. For a paper whose core is Def. 3.14, this is the right architectural instinct.
2. The claim that WindowLinkTable.window_link_table is reusable for Stage A is correct. It is generic in nuEc and nuFc (WindowLinkTable.v:88). compE occurs only inside BL.nuE_all (WindowLinkTable.v:189, :199, :247, :266, :335, :353, :461; I grep-confirmed this). So the trick of taking compE constant for a joint underlay spec is sound.
3. It is the only design that states the real-time obstruction for register x,y (BUF-0(c)): a WrX(1) that has returned but is still buffered, followed by RdX()=0. If confirmed, the current seqlock_module_rel_lin hypothesis fails on TSO runs even without z. This is the most important unchecked premise for the whole redesign.
4. The Stage B overlay contract (an atomic SeqLock write plus a publication marker at F(wmb1), placed before the next SeqLock op) is the strongest and simplest overlay interface of the three. My argument, built from the Part B lemmas, is that it holds: F(wmb1) < F(wmb2) < Rel_w, and every later SL lp lies after Rel_w by wr_disjoint/ww_disjoint. SL-only clients keep an atomic register and z-data MP is restored.
5. The atomic-contract (pending wmb published before a DRMW op; dto Wmb DRMW = true, dto DW DRMW = false, both re-evaluated in Rocq) is the right small piece of new metatheory.
  - Fatal flaws: 1. The reuse claim for SeqLockModule is false at the type level. "Section Execution (none of it depends on the spec): SX, ix, toEv, src_order, phi, phi_lpq, S1_transport" is wrong. `Check SLM.phi_lpq` and `Check SLM.S1_transport` both take `rel_lin_witness … (BL.nuE_all … (SLM.nuEc rc K)) Wu`, the register spec (SeqLockModule.v:695-696, :1018-1019). So do wu_src, wu_call, toEv_evt, idx_pos, wit_nodup and SX_wf. Only SX, ix, ix_src and src_order are free of the spec. About 540 lines (SeqLockModule.v:688-1225) must be copied and adapted, or generalized in place. BUF-4 is therefore L, not M.
2. BUF-1 (WF_core) is not a 'statements unchanged' refactor. Part B lives in `Section Layer` with `Hypothesis HW : WF rc K X` (SeqLockCOH.v:713-716). Weakening it changes the signatures of about 30 lemmas that SeqLockModule, SeqLockTower, SeqLockClients and SeqLockLB call (e.g. `SL.lp_inj rc K X X_wf`, `SL.seqlock_S1 rc K X X_wf HK`). That needs renaming plus wrappers, or a 700-line copy. It also contradicts the SL-tower acceptance criterion ("Existing files are unchanged except _CoqProject").
3. The tower (BUF-9: "a tower_link analogue producing WF_buf") has no reuse path. SeqLockTower.WF0's validity is register-state validity (`wf0_valid`, SeqLockTower.v:247). The data-call simulation inside X1_wf would have to be redone with flush positions over a 2048-line file. Rated L, it is underestimated, and it sits on the Tier-B critical path.
4. Stage A regresses an existing kernel-checked client theorem (seqlock_client_mp_forbidden). The design then carries two module theorems (A and B) and two client files, which duplicates work. Stage B needs WindowTableJ/WindowLinkTableJ plus a joint underlay over {x,y,z,Bw,Br}, which is most of MEM-FIRST's work anyway.
5. BUF-0 (a), (b) and (d) re-derive the Q6 confirmation that is already kernel-checked (q6_not_rel_lin, q6_underlay_no_WF, q6_underlay_not_rel_lin, q6_cells_TSO_consistent). Only (c) is new.
  - Fixes: 1. Replace WF_core/read_value_buf with the SC-ify reduction (MEM-FIRST/PUB): from the buffered witness, drop z, move every WrX/WrY/WmbC to its flush, and prove SeqLockCOH.WF of that z-free X' unchanged. pres follows from the contract plus the atomic-contract (wmb2 before Rel), and validity from 'the reader has no pending own x/y' plus Pending.read_value/cg_last_flush. Then seqlock_S1/seqlock_S1_ord apply untouched, and SeqLockCOH.v is not edited.
2. Apply the same reduction at the tower bottom to get SeqLockTower.WF0, so that tower_link is reused unchanged.
3. Budget BUF-4 as L, with an explicit copy-adapt of SeqLockModule.v:688-1225, or ask the author for a statement-preserving generalization of its Execution/Transport sections over an arbitrary underlay spec.
4. Skip Stage A as a deliverable. Go straight to WIN-J plus the joint contract with the marker, so mp_forbidden is never lost.
5. Shrink BUF-0 to committing the existing Q6 scripts plus (c).
- MEM-FIRST (every interface an instance of memory/'s hidden buffered memory; ghost-location barriers; hybrid atomic objects; SC-ify reuse; SeqLock as a buffered pair location ∩ Lin_sl)
  - Score: 7
  - Strengths: 1. Best reuse lever of the three: the SC-ify reduction to a z-free SeqLockCOH.Exec. I checked the pres obligations case by case against upres and the re-evaluated table:
   - same-object x/y pairs follow from issue order plus FIFO;
   - wmb1→W→wmb2 follows from the contract (handle order on dependent pairs);
   - wmb2→Rel follows from the atomic clause (dto Wmb DRMW = true);
   - Acq→wmb1 follows from rhb (dto DRMW Wmb = true);
   - cross-object W→R and R→W are not required (dto DW DR = dto DR DW = false).
   Validity follows from memory/Pending.read_value and cg_last_flush, plus the fact that a reader never has pending own x/y writes.
   So SeqLockCOH Part B (about 1900 lines) and SeqLockTower.tower_link/X1_wf (2048 lines) are reused with no edit. The same reduction at the bottom yields WF0 (SeqLockTower.v:238-249).
2. It correctly identifies the HWu-bound SeqLockModule lemmas as copy-adapt (SeqLockModule.v:688-1225). That matches what `Check` shows.
3. One notion of specification from memory to objects. Equivalence.declarative_characterization is generic in I with only HI (Equivalence.v:31-46), so the declarative corollary for a table-induced I_tab really is cheap. Tensor.memory_tensor makes ν[{sl,z}] = Buf[sl] ⊗_Pc Buf[z]. This gives the strongest paper story for Reviewer A and the meta-review ('correspondence with existing memory models').
4. It keeps rel_lin and window_link_table. The joint spec needs only a J-variant: h_S1 → h_S1J, proved by conclusion_of_lp_before (WindowTable.v:128, :148). That is genuinely small.
5. The honest scope (x86 only, ARMv8 open, RMW as atomic objects, complete executions) matches the oMCA decision without overclaiming.
  - Fatal flaws: No fatal flaw in the architecture, but three problems.
1. The justification for the interface change is an unchecked derivation (B': "Atomic[sl] ⊗_Pc Buf[z] refuted over plainTL"). It only refutes a contract anchored at the linearization point. BUF-ISSUE's atomic write with a publication marker at F(wmb1), placed before the next SL op of any thread, is derivable from the existing Part B lemmas and is stronger. If adopted, ν[{sl,z}] ∩ Lin_sl, Cantor pairing, and the risk that 'sl publication may lag' all disappear.
2. Grounding: X86-M (XL) plus X86-E2E (L) sit at the end of the critical path for 'no underlay hypothesis'. As scheduled they put the riskiest task last. Tier B's memory/ grounding can be met earlier by the declarative cells+barriers bridge (MEM-BAR plus a history-level corollary).
3. Putting the hybrid atomic-object spec (HV) into memory/ widens memory/'s scope. Acceptable only if it stays parametric (no import of examples/), as the design proposes.
  - Fixes: 1. Replace the overlay spec ν_{I_F}[{sl,z}] ∩ Lin_sl with BUF-ISSUE's Stage B contract: an atomic nu_sl plus a hidden publication marker at F(wmb1), placed before the next SL op, with the findep contract against z flushes. Keep B' as a SL-BUF-REF side result (refuting the lp-anchored version) rather than as the interface's justification.
2. Make X86-M and X86-E2E optional after the declarative bridge.
3. Add BUF-0(c), the real-time obstruction for register x,y, to Q6-0, because it decides whether x/y must be buffered at all.
4. Commit the existing Q6 scripts instead of redoing them.
5. Add an explicit file-level dependency rule: no new file imports SeqLockLB.v.
- rel_lin_pub (extended witnesses with publication events, a third rhb clause on publication points, retiming proof)
  - Score: 4.5
  - Strengths: 1. It is the most principled answer to Reviewer A's transitivity objection. Issue order and publication order are split inside the correctness criterion, and same-object pairs are excluded from the publication clause.
2. It reuses Part B, TicketLockCOH and tower_link through the same retiming as MEM-FIRST. It is precise about F1/F2 and that they do not depend on the waits (robust to RE-04(b)).
3. It keeps per-component products, and it records the ARMv8 RSW-through-object gap honestly.
  - Fatal flaws: 1. Under this lens it changes the core correctness criterion with no reuse gain over MEM-FIRST. rel_lin_pub replaces Def. 3.14 for the running example. That forces a new abstract window theorem (WindowPub) and a new module link (WindowLinkPub). The overlay conclusion must now establish the publication clause (vrhb), which window_link_table cannot produce. Rated L, WindowLinkPub is realistically XL: it is a generalization of WindowLinkTable (619 lines) interacting with BracketedLink (1137 lines) and RelaxedModuleFacts (1020 lines).
2. Nothing else in the development is about rel_lin_pub: RelaxedGSim.GSimRel, RLHL, ViewLHL and SeqLockClients are all about rel_lin. The paper would carry two linearizability notions, and conservativity is only for 'nothing buffered'.
3. The underlay hypothesis is a new notion with no memory/ theorem behind it until BP-17 (optional). So the memory/ grounding (BP-16) needs an extra equivalence layer that MEM-FIRST gets from Equivalence.declarative_characterization directly.
4. Self-estimated at 18–28 Writer iterations, the highest of the three, for no stronger end result than MEM-FIRST with the marker contract.
  - Fixes: 1. Do not change rel_lin. Keep the retiming idea (BP-8) and grafting it onto MEM-FIRST/BUF-ISSUE.
2. Recast clause (iii) as a contract inside the overlay spec, using memory/'s handle-ordered contract with handle := witness index on dependent pairs. Its cross-component coupling is then exactly the joint (J) spec, at the cost of WIN-J (S-M) instead of WindowPub plus WindowLinkPub.
3. If the authors still want a publication-aware criterion, make it a paper-level remark backed by BP-17-style equivalence, not the mechanized interface.


## Amendments after Phase 0 review (author, 2026-10-13)

- **R-1:** the old register-cell results are removed from the paper's mechanization table; header notes are comment-only and say they cover only publication-at-response, forwarding-free underlays (not "the forwarding-free instance [SUPERSEDED 2026-10-13: see 'Amendments after Phase 0 review' at the end — old results are removed from the paper's table and cover only publication-at-response, forwarding-free underlays]").
- **Order:** Phase 0 wrap-up (Q6-evidence it. 2) → F-1, F-3 and **G-3** (moved forward; adds the TicketLock version-word check on ARMv8 and herd7 test files for the author) → F-2 (freezes the TicketLock spec only after G-3).
- **LatchSet:** built directly on this buffered-cell infrastructure, after Phase 1–2.

## Amendments after F-1 review (orchestrator, 2026-10-13; from `latest-review.md` F-1 it. 1)

- **Wording fixes (records):**
  - The design summary's "This partially resolves [corrected 2026-10-13, F-1 review m-33: ix := 0 makes the contract vacuous; witness indices required; bridges (i) nu_handle_invariant and (ii) po_handles_vs_index still owed] the clash between `uev`'s ix := 0 … and `wf_cand.po_handles`" should read **"partially resolves"**. ix := 0 makes the contract vacuous; handles must be witness indices.
  - F-1's acceptance "an MP+wmb/rmb trace has no nu witness" is false as literally stated (`mp_wmb_rmb_nu_unordered`). It reads: **no ν-history presents the candidate and respects an admissible pre** (proved).
- **Carried into later acceptance criteria:**
  - **D-2 / G-1:**
    - (i) `nu_handle_invariant`: `hide` commutes with `relabel` up to monotone reindexing;
    - (ii) `po_handles_vs_index`: for `wf_cand X` and a history that presents X and respects `pre0 X I_tab`, under `write_symmetric`, program-order handles and issue positions agree in `Nat.compare` on dependent same-thread write pairs.
  - **G-1:** either the lemma "mo at the shared Bw adds no constraint" (m-35), or the x86 route below, which avoids it.
  - **S-1:** kernel versions of `ato_is_dto` (∀ rc), `write_symmetric (dto rc) slcat`, and `sindep_iff_I_tab` on cell ops (exact equivalence, ∀ K) (m-36).
- **Scope limits to state** (m-34):
  - W→R table entries order issue only, not publication; there is no draining fence.
  - Witness-index handles need write symmetry, which fails for DWrel. Generic `K` and LatchSet with rel/acq categories need program-order handles.
- **x86 cell-level grounding** (reviewer alternative 1): every x86-TSO read/write machine trace over data and ghost locations erases from `V_{I_tab}`, for every table. TSO's contract is the strongest, and `contract` is monotone in I. Pulled forward as an F-1 addendum; ~100–150 lines; avoids m-35 for x86.

## Amendments after G-3 review (orchestrator, 2026-10-13; `latest-review.md` G-3 it. 1)

- **Atomic clause:** the plan's "needs LDADDAL with LDAR gets" (:647, :700, :722, :765) is **wrong for the clause** (`ac_ldadd_ldr_forbidden`: any RMW flavour with plain LDR, given the SeqLock's DMB ST/LD) and **insufficient for the abstraction** (M-15).
- **RSW-through-object:** "do not print the ARMv8 RSW limitation" is now kernel-backed (`RSWObj.rsw_obj_forbidden`, all variants).
- **New research question Q7 (M-15):** ARMv8 for waiting clients needs a Wait-compilation scheme (R4) or the claim is x86 only (R3). F-2 is frozen until the author decides; F-3 proceeds.
- **Version word (M-16):** writer-side VW is likely admitted by the atomic TicketLock spec; R1 (RMW publication point) may be unnecessary for the SeqLock.

## Amendments after the D-1 review (2026-10-13)

- **:898 corrected.** "Only SX, ix, ix_src and src_order are free of the spec" is factually wrong. Of the 49 SeqLockModule Execution/Transport constants, 37 are spec-free and 12 carry the register witness: `wu_src`, `wu_call`, `toEv_evt`, `wit_nodup`, `idx_pos`, `wit_replay`, `SX_wf`, `X_wf`, `lpu_src`, `phi_lpq`, `S1_transport`, `positional`. Source: the D-1 reviewer's `Check` of each.
- **:252 vs :664/:898 reconciled.** :664/:898 are right at the type level. :252 is right semantically, and `SeqLockModuleGen.positional_of_gen` confirms it in the kernel.
- **D-2 route (reviewer's D-1 M-17).** The z-order for `PositionalJ.p_S1_ord` must come from `WF_core` of `SX` (D-1), not from the SC-ified execution, because scify drops z.
- **Suggestions for S-1/S-2, not yet adopted** (decide when S-1 is briefed):
  - (1) `BExec` contains an `SL.Exec` call part, and `BWF` = `WF_core` (call part) + hybrid validity, so D-1's `SX_wf_core` plugs in verbatim.
  - (2) State S-2's `lp_order_agree`/`seqlock_buf_S1` on the `BExec` built from `SX` (indices of `SX`, positions in `Wu`), or add a generic transport between two `SL.Exec`s along an injective op-map, to avoid a second index transport.
  - (3) For T-3, possibly abstract D-1 over the module's decode interface.
- **D-2 entry point (after the D-1 it. 2 review).** `SeqLockModuleGen.positionalJ_of_S1J` composed with `WindowLinkTableJ.window_link_table_J_jointE` reduces the D-2 module theorem to two obligations: `nuJ_F []`, and `p_S1J` for every complete execution with a `nuE_hyb` witness. The reviewer kernel-checked this composition as `d2_entry`, Closed, in scratch; it is not in the tree. The reviewer recommends stating S-2's `seqlock_buf_S1` / `lp_order_agree` on `SX`'s indices (the list consumed by `positionalJ_of_ovl`), because scify drops z blocks and changes `(t, j)` indices.
