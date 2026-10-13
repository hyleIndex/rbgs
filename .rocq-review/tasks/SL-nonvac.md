# Task SL-nonvac: a concurrent, weak, module-level instance of `seqlock_module_rel_lin` (load buffering)

Status: ready. Independent of SL-client. Prepared 2026-10-13 for `/rocq-loop SL-nonvac`.

## Concerns

- **latest-review M-3.** The only non-vacuity witnesses are one operation by one thread over `VE0` with `Step := True`: `SeqLockModuleExample.seqlock_module_nonvacuous` and `LockedRegisters.link_hypotheses_satisfiable`.
- **Pillar A, intro.tex:110:** object-level load buffering is admitted.
- **Reviewer B5:** an example on COH.

## Current Coq state

- `examples/Relaxed/SeqLockModuleExample.v`: the single-write module execution. It is the template: `write_produces`, `w_execution`, `W_w`, underlay `rel_lin`, then the application of the module theorem.
- `examples/Relaxed/SeqLockModule.v`: `seqlock_module_rel_lin`.
- `examples/Relaxed/SeqLockCOH.v` Part D: `X_lb` (= `mkX [BZr 1; BW 1 1] [BR [] 2 1 1; BZw 1] lb_wit`), `lb_wf`, `lb_allowed`, `lb_refutes`, `paper_signature_fails`. These hold at witness level only.
- `examples/Relaxed/SeqLockProg.v`: the module `M rc K`. Its futures are untagged: each invocation carries every handle resolved so far in its own method's store.

## Target

Create a new file `examples/Relaxed/SeqLockLB.v` and add it to `_CoqProject` after `SeqLockModuleExample.v`.

1. **The execution.** Build a concrete complete module execution `T_lb` of `M rc SL.plainTL`. Pick `rc`; do both values if that is cheap.
   - Thread A invokes `zr()`, which returns 1, then `write(1,1)`.
   - Thread B invokes `read()`, which returns `(1,1)`, then `zw(1)`.
   - In each thread the second call is invoked **before** the first returns.
   - The execution is complete: `tm_queue c = []` and every call is `DeadCall`.
2. **Underlay `rel_lin`.** The underlay part of `T_lb` is `rel_lin` w.r.t. `BL.nuE_all … (nuEc rc plainTL)`, shown by an explicit witness (adapt `lb_wit`).
3. **`seqlock_lb_module`.** The overlay part is `rel_lin` under F's semi-independence, by `seqlock_module_rel_lin`.
4. **`seqlock_lb_not_classical`.** The overlay part is **not** `rel_lin` under the empty semi-independence `(fun _ _ => False)` with the same spec, i.e. under classical linearizability with program order.
   - Optional, only if cheap: it is also not `rel_lin` under the paper's printed signature (read ↦ rfence, write ↦ lfence).
5. **Underlay LTS `VE`.** `VE0` is acceptable only with an explicit justification in the header: the theorem is uniform in `VE`, and its substantive underlay hypothesis is `rel_lin`, which is proved by witness. If a non-trivial `VE` is cheap, use it. Either way, say what you chose and why.
6. **Header comment.** Explain:
   - how the same-thread overlap arises in the tagged module semantics (cite the `must_precede` / frontier rules);
   - what is shown and what is not.

## Acceptance

- The new file builds.
- No `Admitted`, `admit` or new axioms. `Print Assumptions` is reported.
- No existing file changes except `_CoqProject`.
- K/S/P/R gap check.
- If the module semantics cannot produce this execution, stop and report the blocking rule. Do not change the semantics.
