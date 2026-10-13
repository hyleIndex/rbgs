# Task SL-tower: the inlined SeqLock tower at module level (then, optionally, TicketLock at module level)

Status: ready. Larger than SL-client and SL-nonvac. Prepared 2026-10-13 for `/rocq-loop SL-tower`.

## Concerns

- **latest-review M-1 and M-2:** no module-level vertical composition.
- **Reviewer B's end-to-end chain.**
- **Paper:** the layered SeqLock (overview.tex `prop:vertical-composition`; Fig. SeqLock).

## Current Coq state

- `examples/Relaxed/SeqLockCOH.v`: the SeqLock layer over an **abstract** atomic TicketLock ⊗ COH[x] ⊗ COH[y] ⊗ Barrier ⊗ COH[z]. It is at witness level: `seqlock_S1`, `seqlock_S1_ord`, `z_S1`, `seqlock_z_composition`.
- `examples/Relaxed/TicketLockCOH.v`: the TicketLock over Counter[own] ⊗ COH[nxt], at witness level. For odd `s`, `test_ticket(s)` makes no memory call ("silent").
- `examples/Relaxed/SeqLockTower.v`: the vertical link at witness level. The SeqLock code with the TicketLock code inlined, running on Counter[own] ⊗ COH[nxt] ⊗ COH[x] ⊗ COH[y] ⊗ Barrier ⊗ COH[z], is linked by `tower_link`, `tower_composition`, `tower_composition_plain` and `_rt`.
- `examples/Relaxed/SeqLockProg.v` and `SeqLockModule.v`: the SeqLock layer (over the abstract TicketLock) written in the futures language and linked via `WindowLinkTable.window_link_table`.
  - Windows: a write's is its first wmb; a read's is the first rmb of its last iteration.
  - `positional` is built from `SeqLockCOH`.
  - This task is the analogue one level down.
- No general vertical composition theorem exists in `models/`. Building one is **out of scope**.

## Target

Add the new files to `_CoqProject` after `SeqLockRT.v`, or wherever their dependencies require.

1. **`examples/Relaxed/SeqLockTowerProg.v`.**
   - The inlined module `M0`, written in the futures language.
     - Overlay: write, read, zr, zw.
     - Underlay: the low-level objects of `SeqLockTower`.
   - It must follow the code in the headers of `SeqLockCOH.v` and `TicketLockCOH.v` exactly:
     - `acq = t <- nxt.faa(2); while (own.get() <> t) {}; own.inc()`
     - `rel = own.inc()`
     - `get_ticket = own.get()`
     - `test_ticket(s) = (s & 1) || own.get() <> s`; when the short-circuit applies, it makes no call.
   - A shape lemma, analogous to `SeqLockProg.M_shape`: every method trace is the trace of one low-level block of `SeqLockTower`'s model.
2. **`examples/Relaxed/SeqLockTowerModule.v`, theorem `seqlock_tower_module_rel_lin`.**
   - Statement: take a complete execution of `M0` whose underlay part is `rel_lin` w.r.t. the tensor of the **low-level** object specifications, under the table-induced semi-independence. Then its overlay part is `rel_lin` w.r.t. ν_SeqLock ⊗ ν_COH[z], with the same overlay semi-independence as `SeqLockModule`.
   - Proof route: use `window_link_table`, with `positional` coming from `SeqLockTower.tower_link` + `SeqLockCOH`.
   - Prove it for the plain counter at least, and more generally if that is cheap.
3. **Header comments** must state:
   - the remaining hypothesis concerns only low-level objects (Counter[own] with faa/inc/get, COH[nxt] with faa, x, y, Barrier, z); no abstract TicketLock;
   - this is an end-to-end result for **one inlined module**, not the paper's general vertical composition theorem;
   - only complete executions are covered.
4. **Optional, second iteration:** the TicketLock layer at module level (`TicketLockProg.v` / `TicketLockModule.v`, analogous to SeqLockProg/SeqLockModule).
   - Problems to handle honestly: the client discipline of `ticketlock_S1` (acq/rel alternate), and the silent `test_ticket`, which has no window.

## Known risks

- `acq`'s spin loop (coinductive `Prog`).
- The silent `test_ticket` inside a read iteration.
- Decoding method traces into `SeqLockTower` blocks.

If the full link cannot be completed:
- deliver what is solid, with no admits;
- keep unfinished parts out of `_CoqProject`;
- give a precise account of what remains.

## Acceptance

- The new files build.
- No `Admitted`, `admit` or new axioms. `Print Assumptions` is reported.
- Existing files are unchanged except `_CoqProject`. If an existing lemma needs generalizing, do it in a new file or report it.
- K/S/P/R gap check.
