# Task RLHL-1: re-encode the RLHL judgement so that it is a Hoare triple (as in the paper's EStep)

Status: ready, research-heavy. Escalate the design choices listed below; do not decide them silently. Prepared 2026-10-13 for `/rocq-loop RLHL-1`.

## Why (read `.rocq-review/research-intent.md` §8 and `latest-review.md` B-1)

The paper's rules (Appendix/programlogic.tex: EStep with `∀v. G ⊨ {P'} v {Q(v)}` and `stable(P, R)`, `stable(P', R)`, `stable(Q(v), R)`) are not the problem. The Coq encoding is:

1. **One path only.** `RelaxedLogic.provable_wait_pending` takes one response `ret` and continues with `continuation ret`. `HTripleProvable` (RelaxedLogic.v:869) is `exists obligations result final, …`. So a derivation certifies one execution path with one choice of underlay responses.
2. **No interference.** `queue_invariant` (RelaxedAssertion.v:183) equates the method's debts with the whole module queue (`erase_obligations obligations = mc_queue c`). As soon as another call has an outstanding event, the `DebtCertificate` premise is false, so the triple says nothing about concurrent states.
3. **No rely.** `Stable` (RelaxedAssertion.v:108) and `TStable` (RelaxedTaggedLogic.v:260) are defined but never used.
4. **No soundness theorem.** That is task RLHL-2.

## Target

New files, e.g. `models/simlin/RelaxedHoare.v`. Keep `RelaxedLogic.v`/`RelaxedTaggedLogic.v` building; mark them superseded in their headers, but do not delete them.

1. Define a judgement over the **tagged** module semantics (`module_step_tagged`; GSim, ViewLHL and the window results all use it) such that:
   - the Wait/response rule quantifies over **every** response the underlay may give (compare the SC logic: `RGILogicSet.v`, `CoreVis … forall ret`);
   - debts are per call and frameable: a method's obligations are a sub-queue of its own call, not the global queue;
   - assertions are stable under a rely relation (thread rely + same-thread-other-call rely, as in the paper's `R = (R_τ, R_α)`), with guarantee obligations for the method's own steps;
   - abstract updates use `RelaxedPossibility` (`poss_invoke`, `poss_steps`, `poss_return`). Independent same-thread calls may be linearized out of order, which is what object-level load buffering needs.
2. Prove the rules sound with respect to a **semantic** per-call triple, which RLHL-2 will connect to `RelaxedGSim.GSimRel`. State that semantic triple explicitly.
3. **Sanity checks**, required:
   - (a) the old judgement derives a triple for a wrong program (for example a method that reads two cells without the lock and returns them as an atomic pair), and the new one cannot;
   - (b) one rule instance is checked on a two-call same-thread overlap.

## Research-level choices to escalate (ask the author before committing to one)

- **Possibilities.** One possibility (as `GSimRel` and `RelaxedPossibility` today) or sets of possibilities (as the paper, needed for future-dependent linearization points such as the weak HW queue)? One possibility suffices for SeqLock and Counter_xy.
- **Underlay presentation.** RLHL reasons about the underlay through an LTS `VE`. For weak behaviour, `VE` must be a *complete presentation* of `(νE, IE)` (`ViewLHL.complete_pres`, e.g. `VT nuE`, or `ViewLift.VL P`), so that `ViewLHL.presentation_choice` transfers the result to every underlay that implements the spec. Which presentation do the rules assume?
- **Positional vs tagged** semantics for the logic (tagged recommended).

## Acceptance

- Builds; no `Admitted`/`admit`/new axioms; `Print Assumptions` reported.
- Existing files unchanged except headers (marked superseded) and `_CoqProject`.
- K/S/P/R gap check: P is Appendix/programlogic.tex EStep, Return and the top-level judgement; R is Reviewer B, "the program logic, its soundness proof …".
