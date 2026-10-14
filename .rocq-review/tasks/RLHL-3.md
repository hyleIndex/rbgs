# Task RLHL-3: first end-to-end object verified with RLHL (Counter_xy, then optionally a SeqLock operation)

Status: depends on RLHL-1 and RLHL-2. Prepared 2026-10-13 for `/rocq-loop RLHL-3`.

## Why

- Today no object is verified through RLHL or VLHL (latest-review B-2).
- The paper's own RLHL example is Counter_xy (Appendix/2Counter.tex): `inc_x`, `inc_y`, `get_x`, `get_y` over the RC memory object, with the invariant and the `get_x` proof outline given there.

## Target

1. Counter_xy as a futures program over an underlay presentation of `(ν_RCMem, I_RC)`, as chosen in RLHL-1.
2. Method proofs in the RLHL-1 judgement, following Appendix/2Counter.tex: the invariant, and the `get_x` linearization point at its read.
3. The end-to-end theorem through RLHL-2: relaxed linearizability of Counter_xy w.r.t. `(ν_Counter, I_Counter)`. Do this over every underlay implementing `(ν_RCMem, I_RC)` if RLHL-2 provides `presentation_choice`.
4. Non-vacuity: one concurrent execution, with overlapping same-thread calls, that the theorem covers.
5. Optional: re-prove one SeqLock operation through RLHL and compare effort with the window route (`SeqLockModule`). This feeds the paper's "proof effort" discussion, Reviewer C5.

## Acceptance

- Builds, with no new axioms.
- The proof follows the paper's outline, or the report says where it had to deviate and why.
- K/S/P/R gap check:
  - P: Appendix/2Counter.tex; intro.tex:113;
  - R: Reviewer B ("verification of a concurrent object alongside … its client"), and C5.

## Adjustment (2026-10-13, orchestrator; see research-intent §8 and iteration-log)

The original target (Counter_xy over RCMem with an underlay presentation of (ν_RCMem, I_RC) chosen in RLHL-1) is re-scoped by the author decisions made during RLHL-1/RLHL-2. These are the M-18 route, Q3 prefix soundness, and M-20 CompLin-style copy-cat soundness over the sequential (EI) spec. The work is split into bounded sub-tasks, run in order:
- **RLHL-3a.** Copy-cat soundness `rlhl_complin`:
  - Statement: RLHL2Hyps over (VE, VF := `EI δF`) implies that every overlay trace of M over VE, complete or not, is an overlay trace of the relaxed copy-cat (identity module) over `EI δF`.
  - Proof: reify the `GSimRel` run (relaxed analogue of `CompLinSound.cal_to_CompLin`).
  - Instance: the counter over `HVE`/`EI`.
- **RLHL-3b.** An end-to-end instance with nonempty semi-independence (latest-review M-19), e.g. Counter_xy or two counters. It comes with a relaxation witness (rel_lin under I, not under ∅) and an own-event premise needing a real stability proof.
- **RLHL-3c.** Vertical composition, the relaxed analogue of `CompLinVComp`: two RLHL-verified layers compose. Then an object plus its client end to end (Reviewer B).

### Further adjustment (2026-10-13, after RLHL-3a iteration-1 review and author decisions)
- **RLHL-3c additions** (review M-22 and author decisions):
  - `Lift`/`mtraces_mono`, absorption (the paper's saturation proposition), and linking;
  - a CompLin-style TErr error clause in the copy-cat comparison;
  - the composite of two layers; a client semantics.
- **New queue items after RLHL-3c:**
  - `RLHL-mem`: thread-aware buffered memory spec δ_mem with I_Mem, plus "the buffered cell produces only copy-cat traces of EIhl δ_mem".
  - `RLHL-latch` / `RLHL-snapshot`: the LatchSet instance, then the write-snapshot over an interval-sequential spec LTS with its own bridge.
