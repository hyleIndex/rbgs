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
