# Task RLHL-2: soundness of RLHL — derivations give `GSimRel`, hence relaxed linearizability

Status: depends on RLHL-1. Prepared 2026-10-13 for `/rocq-loop RLHL-2`.

## Current Coq state

- `models/simlin/RelaxedGSim.v`:
  - `GSimRel S` and `gsim_step`. Every clause is universal: overlay invocation ↦ `poss_invoke`; underlay step ↦ `poss_steps`; overlay return ↦ `poss_steps` then `poss_return` with the same result.
  - `gsim_rel_lin` (`eq_rect_eq` only): a complete overlay trace of a simulated execution is `rel_lin`, provided every complete well-formed trace of `VF` is `rel_lin`.
- `models/view/ViewLHL.v`:
  - `presentation_choice`: a `GSimRel` over a complete underlay presentation and a sound overlay presentation proves relaxed linearizability over every underlay that `implements (νE, IE)`.
  - `vlhl_sound`: the instance with `VT` on both sides.
- Paper: Appendix/programlogic.tex, Prop. "Logic Soundness"; implex.tex `prop:rlhl-sc`. The paper's simulation (Appendix/relaxedlin.tex, OStep) is existential, and `GSimRel` is its corrected form. Record this as a paper change.

## Target

1. **`rlhl_gsim`.** If every method of `M` is provable in the RLHL-1 judgement for every thread and handle, and the rely and guarantee are compatible (each thread's guarantee is within the others' rely; invoke and return steps are within the guarantee), then there is an `S` with `GSimRel S` and `S (initial_tagged_module VE q0) (PossOk v0 [])`.
2. **`rlhl_rel_lin`.** Compose with `gsim_rel_lin`, and with `presentation_choice` / `vlhl_sound` for the version over every underlay implementing the spec.
3. **Header.** Map the result to the paper's Prop. "Logic Soundness" and state the differences:
   - complete traces only;
   - single possibility, unless RLHL-1 chose sets;
   - which presentation is used.

## Acceptance

- Builds, with no new axioms.
- Every hypothesis of `rlhl_gsim` / `rlhl_rel_lin` is named and justified in the report.
- K/S/P/R gap check.
- A non-vacuity remark: the hypotheses are instantiated in RLHL-3.
