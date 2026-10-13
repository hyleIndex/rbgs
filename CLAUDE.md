# CLAUDE.md — rbgs (branch `relaxed-lin`)

Instructions for Claude Code in this repository. `README.mdwn` (setup) and `docs/README.md` (documentation layout) remain authoritative. This file only adds working rules.

## Project

- Refinement-based game semantics in Rocq (CertiKOS rbgs). The `relaxed-lin` branch adds the mechanization of **relaxed linearizability**:
  - `models/RelaxedSignature.v` and `models/simlin/Relaxed*.v`: relaxed signatures, the future language, module semantics, RLHL, and the global simulation `RelaxedGSim`;
  - `models/view/`: prefix views, ViewLift, VLHL soundness;
  - `memory/`: the buffered memory cell, its OMCA declarative form, x86-TSO, and the RC11/ARMv8 comparison;
  - `examples/Relaxed/`: composition theorems, the COH SeqLock and TicketLock;
  - `examples/View/`: view-based ports of the exchanger, SeqLock and EB stack.
- The paper is in `../async-ccal/drafts/relaxed-lin/` (LaTeX).

## Build

- Rocq 9.2.0 and Stdlib 9.2.0 (`rocq-rbgs.opam`). Run `eval $(opam env)` if you use opam.
- Run `./configure` once. It initializes and builds the `coqrel` submodule, then generates `Makefile` from `_CoqProject`.
- Build with `make -jN`, or one target with `make path/File.vo`.
- New `.v` files go into `_CoqProject` in dependency order. Then regenerate the Makefile: `coq_makefile -f _CoqProject -o Makefile`.

## Rules

- The branch is admit-free. Do not add `Admitted`, `admit`, `Axiom`, top-level `Parameter`, or `Unset … Checking`.
- Check new results with `Print Assumptions`. The baseline is `eq_rect_eq` and `classic`.
- Do not weaken theorem statements or change the meaning of existing definitions without saying so explicitly.
- Keep the header comments of files accurate. They document intent and known limitations.
- Do not commit, push or rewrite git history unless asked.

## Research review workflow

- `/rocq-loop [concern-id] [max-iters≤5]` runs the Writer–Reviewer loop. It uses the agents `rocq-writer` (implements) and `rocq-research-reviewer` (read-only, skeptical review).
- State and records live in `.rocq-review/`:
  - `research-intent.md`: the claims, sources and safeguards;
  - `concern-matrix.md`: POPL concerns and paper claims → Coq → status;
  - `latest-review.md`: the most recent review;
  - `iteration-log.md`: the history of loop iterations;
  - `popl2027-reviews.md`: the verbatim reviews, git-ignored.
- Always distinguish what the kernel checked, what the statement says, what the paper claims, and what the reviewer concern requires.
- Compiling is not evidence of conceptual correctness.
