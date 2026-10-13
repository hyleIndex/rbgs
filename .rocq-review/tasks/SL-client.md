# Task SL-client: module-level client theorems for SeqLock ⊎ COH[z]

Status: ready. Depends on nothing new. Prepared 2026-10-13 for `/rocq-loop SL-client`.

## Concerns

- **Meta-review:** "the lack of a demonstration of client verification".
- **Reviewer B:** "the verification of a concurrent object alongside the verification of its client program".
- **Author response B4 (promised):** "a client of the SeqLock interface initialized to (0,0), whose writers invoke write(v,v). A reader obtains (a,b) and asserts a=b. … The implementation-level argument must then instantiate the library refinement theorem for this client and its actual underlay semantics."

## Current Coq state

- `examples/Relaxed/SeqLockModule.v`, `seqlock_module_rel_lin rc VE q0 T c` (closed).
  - Hypotheses: a complete execution, i.e. `module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c`, with `tm_queue c = []` and every call `DeadCall`; and the underlay part is `rel_lin` w.r.t. `BL.nuE_all … (nuEc rc plainTL)`.
  - Conclusion: `rel_lin BL.over_sel T (semi_independent (F rc)) (BL.nuF_all … (nuFc rc))`.
- `examples/Relaxed/SeqLockProg.v`: overlay operations `fWrite vx vy`, `fRead`, and the z operations; categories `fcat` (write ↦ Wmb, read ↦ Rmb, z ↦ W/R); `findep`.
- `examples/Relaxed/SeqLockCOH.v`: `nu_sl` (`reg_ok sl_wr sl_rd (0,0)`); `mp_forbidden`, at witness level only.
- Pattern to imitate for module-level clients: `LockedRegisters.sb_forbidden` and `LockedRegistersWindow.sb_forbidden_window` (keys k1..k4, invocation/response positions in T).

## Target

Create a new file `examples/Relaxed/SeqLockClients.v` and add it to `_CoqProject` after `SeqLockModuleExample.v`.

1. **Spec-level lemmas** about overlay traces and witnesses only, independent of the implementation:
   - (a) In any history legal for ν_SeqLock from (0,0) in which every write is `write(v,v)`, every read returns `(a,a)`.
   - (b) The MP pattern below has no witness that is legal for `nuF_all` and respects `rhb` under F's semi-independence.
2. **Module-level theorems.** They hold for every `rc`, `VE`, `q0`, `T`, `c`. Their hypotheses are **exactly** those of `seqlock_module_rel_lin`, plus client-shape hypotheses on T.
   - **`seqlock_client_equal_pairs`:** if every overlay write invocation in T is `fWrite v v`, then every overlay read response in T is `(a, a)`.
   - **`seqlock_client_mp_forbidden`:** the following pattern is impossible (⇒ `False`). z is initially 0.
     - Thread t1 invokes `zw 1` (key k1), then `fWrite 1 1` (k2).
     - Thread t2 invokes `fRead` (k3), which returns `(1,1)`, then a z read (k4), which returns 0.
     - The two calls of each thread **may overlap**: do not assume k1 responds before k2 is invoked, or k3 before k4. The ordering must come from the exported categories (wmb/rmb via F's semi-independence), not from real time.
     - Check, against `findep` and `WindowTable.dtable`, which same-thread pairs are ordered for each `rc`. If the result holds only for some `rc`, state which and why.
   - Derive both theorems from `seqlock_module_rel_lin` plus the spec-level lemmas. Do **not** re-prove SeqLock correctness.
3. **Header comment** covering:
   - what the theorems say;
   - what they assume;
   - what they do not show: joint satisfiability for a concurrent execution is task SL-nonvac; complete executions only; z's initial value.

## Acceptance

- The new file builds.
- No `Admitted`, `admit` or new axioms. `Print Assumptions` is reported for each new theorem.
- No existing file changes except `_CoqProject`.
- K/S/P/R gap check:
  - P = the B4 promise and the intro/implex claims about clients;
  - R = the meta-review and Reviewer B quotes above.
- If a target is false or ill-posed, stop and explain with evidence. Do not weaken it.
