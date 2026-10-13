# Task SL-mem: connect the SeqLock-on-COH cell specifications to the oMCA memory model in `memory/`

Status: ready. Research-heavy: escalate design choices. Prepared 2026-10-13 for `/rocq-loop SL-mem`.

## Concerns

- **latest-review B-3:** `memory/` is not connected to any object; nothing outside `memory/` imports it.
- **latest-review M-4.**
- **Reviewer B2:** "there is no clear theorem statement (does 'agree' mean behavioral equivalence?)".
- **Reviewer B:** "soundness proof against a weak memory model".
- **Meta-review:** "correspondence with existing memory models".
- **Author decision:** scope = oMCA (research-intent §8).

## Current Coq state

- **SeqLock side.** `SeqLockCOH`, `SeqLockProg` and `SeqLockModule` use **abstract** object specifications:
  - x, y and z are sequential registers, with `I = ∅` inside each object;
  - a Barrier object provides `rmb` and `wmb`;
  - there is an abstract TicketLock;
  - cross-object order comes from `WindowTable.dtable rc`, over categories R, W, Rmb, Wmb, ….
- **`memory/` (TR Appendix L).**
  - `Cell.v`: the buffered cell with store forwarding. Reads and writes carry rlx/rel/acq modes. Instances include RC, TSO, PSO and others.
  - `Tensor.v`: memory = tensor of cells, plus a contract.
  - `Equivalence.declarative_characterization`: buffered-cell traces ⟺ D1 ∧ D2 under `pre`.
  - Also: `TSO.v`, `RC11.v`, `ARM.v`, `Litmus.v`.
  - There are no barriers and no RMW.

## Target

Create new files, e.g. `memory/Barrier.v` and/or `examples/Relaxed/SeqLockMem.v`.

1. **COH instance.** Identify the COH instance of the buffered cell (all accesses rlx; see `Cell.v` and Mem.tex). If there is none, define it as a new definition. Do not modify existing ones.
2. **Trace-level correspondence.**
   - Relate (a) COH[x] ⊗ COH[y] ⊗ COH[z], with the semi-independence that `dtable` induces on plain R/W, to (b) `memory/`'s COH specification on {x, y, z}, via `Tensor.v`.
   - Aim for equality of the specified traces, or of the legal witnesses. At minimum, prove the direction that makes a `memory/`-legal underlay history satisfy the corresponding part of `seqlock_module_rel_lin`'s underlay hypothesis.
   - Combine this with `declarative_characterization` for COH. The result: an OMCA-consistent COH execution yields the cell part of that hypothesis.
   - Check whether store forwarding breaks the correspondence. If it does, say exactly how.
3. **Barriers.** Add LKMM-style barriers: `wmb` orders W→W across it, and `rmb` orders R→R.
   - Extend `memory/` minimally, using new definitions only, so that the correspondence covers X ⊗ Y ⊗ Barrier ⊗ Z.
   - If the declarative side (D1/D2 with a barrier-induced preserved order) is too large, prove only the trace-level part. Document the declarative part as a precise gap in the header, never as a hidden hypothesis.
4. **Out of scope** (say so in the header): the TicketLock component; RMW (`faa`, needed by the tower's Counter/nxt); RC11/ARM soundness.

## Acceptance

- Builds.
- No `Admitted`, `admit` or new axioms beyond the baseline (`classic` is already used in `memory/`). `Print Assumptions` is reported.
- Existing definitions in `memory/` and `examples/` are unchanged. Do not add constructors to an existing Inductive.
- K/S/P/R gap check:
  - P: trace.tex:215–223 ("agrees with the declarative one") and intro.tex:112;
  - R: the quotes above.
- If the correspondence is false as posed, stop and give the counterexample.
