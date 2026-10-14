# LatchSet plan v0: design review (rocq-research-reviewer, 2026-10-13)

The full review is in the orchestrator's session transcript. Its key content is recorded below; plan amendments are in `latchset-plan.md` v1.

## Verdict
Redesign the specification layer, then continue. Do not start LS-1..LS-5 as written in v0.

## BLOCKER
### B-5: the v0 target (atomic ν_Set over buffered cells) is refuted. Research-level, author-gated.

**The counterexamples:**
- **CE1.** `insert(2)` by T1 completes, but it ends with plain stores and has no draining operation. T3's later `contains(2)` then reads memory and returns false.
- **CE2.** The writer's own `contains` sees its own insert by forwarding before other threads see it. This is the object-level SB+rfi.

**Kernel facts** (reviewer scratch, piped, Closed):
- CE1 and CE2 underlay traces are in `V AI` / `nu AI` for the abstract table configuration.
- `respects` on the induced histories holds.
- `ce1_overlay_not_rel_lin : forall I, ~ rel_lin Some (L I) I (nuset I [])` holds (eq_rect_eq).

**Derivations (not yet in the kernel):**
- module realizability under issue-time write responses;
- the x86 store-buffer run.

**Options for the author:**
- (a) **ν_BS (recommended):** a buffered set. A sequential set with hidden FIFO publication markers, one per insert after its LP. Non-writers see published inserts; the writer sees its own issued inserts. Conservativity: ν_Set ⊆ ν_BS.
- (b) A draining operation at the end of insert: an RMW on seq under the atomic clause, or a new draining fence. This changes the Linux code and needs new memory/ infrastructure.
- (c) Register cells. Not x86-grounded (Q6-2).
- (d) Withdraw the claim.

## MAJOR
- **M-19.** Route LD-1(a) (register-first + SC-ification) and the relocation lemma are the wrong route.
  - The relocation of the writer's own contains crosses its rmb, and SC-ification breaks `h_rt`.
  - Use a direct buffered proof instead: L1 read-own-latest (single writer per location), L2 published seq monotone, L3 seq constant on [p1, p2], L4 copy s&1 stable and holding the ⌊s/2⌋-insert state, L5 data reads inside [p1, p2] (F3 tag + R→Rmb→R), plus a pure SC core. This is F0–F5 without the register detour.
- **M-20.** P1 must read: every insert is invoked by one designated thread t_w, and the inserts' intervals are pairwise disjoint.
- **M-21.** Categories.
  - Insert can export **Wmb** with window [wmb0, wmb3]; the LP is the issue of wrt(seq, s+2) and the marker is its flush.
  - Contains exports **DR**: window [rd(seq), retry rd(seq)] of the last iteration. It cannot export Rmb, because in_le(Rmb, DR) is false.
  - The checker's "latch read acts as an acquire" would need an asymmetric category (in = DR, out = Rmb), which is a table change (D3). This decides whether an MP-through-latch client is derivable.
  - Reuse `WindowTable.latch_*` (:526–545).
- **M-22.** Precision is model-relative.
  - Under option C, **all five broken variants are correct on x86-TSO** (x86 keeps R→R and W→W). They fail only in the dto-induced model.
  - LKMem = dto on these kinds, up to Wmb–Wmb and Rmb–Rmb, which is harmless.
  - The checker cannot see real-time or overlay violations (CE1).
  - Under ν_BS, refutations need an observing prefix.
- **M-23.** Dependency tags are hand-written.
  - M_L needs data and control tags on the writer's writes, as well as address tags on the reads.
  - Make the five variants flags of one M_L.
  - Add either a tag-policy check or an audit lemma, named in the header.
- **M-24.** Dependencies.
  - The underlay is ν_{I_tab}, not "hybrid": there is no atomic object, so F-2 is not a dependency.
  - LS-5 needs the Op-list ν_{I_tab} with witness-index handles, and F-1's owed bridges (i) `nu_handle_invariant` and (ii) `po_handles_vs_index`.
  - A D-1-style bridge for M_L is a second L-sized copy unless `SeqLockModuleGen` is first generalized over a FuturesShape decoding.

## MINOR
- m-66: the checker's "forbid" is a finite enumeration.
- m-67: LB through LatchSet needs a client cell (joint, F-3).
- m-68: the "RC11 logics cannot verify" claim has no evidence; keep it out of acceptance.
- m-69: `Cell.init_state` starts at 0, so the checker's INIT {1,3} needs a setup prefix.
- m-70: reuse `WindowTable.latch_*`.

## Answers (summary)
- **Q1.** The writer forwards (`Cell.cs_rdf`). S-1's F1 premise fails. The relocation is sound for seq reads but moot (B-5). Recommendation: a direct buffered proof (L1–L5).
- **Q2.** The stateless module forces the writer to read. Adopt LD-0(a′): the writer reads seq and copy 0 only, then writes both copies from the computed array.
- **Q3.** Categories and windows: see M-21. The LPs linearize a **buffered** grow-only set, not an atomic one.
- **Q4.** `FutureD` on the data reads gives `must_precede (Res seq) (Inv data)` (F3), hence an rhb clause-1 edge. LS-3 needs one non-vacuity derivation of this edge.
- **Q5.** LKMem = dto here up to barrier–barrier pairs. Verdicts transfer only at the underlay-outcome level and only for non-reading writers.
- **Q6.** Amended phases:
  - LS-0a (S): evidence file;
  - LS-0b (author): decisions;
  - LS-1 (M): ν_BS and client lemmas;
  - LS-2 (M): M_L, tags, shape;
  - LS-3 (L): direct buffered S1;
  - LS-4 (M): refutations;
  - LS-5 (L): module theorem;
  - LS-6 (M): clients and non-vacuity, including CE1/CE2 at module level, joint MP and LB with z;
  - LS-7 (M, optional): x86 module grounding.
- **Q7.** May claim / must not claim, after the redesigned LS-5.
  - **May claim:** relaxed-linearizable to a **buffered set** (sequential set with deferred FIFO publication and writer-local visibility). The address-dependent readers and the barriers are verified against the dto-induced buffered memory, which over-approximates x86-TSO. The variants are refuted in that model.
  - **Must not claim:**
    - "atomic set specification";
    - ν_E = "coherent cells";
    - ARM or LKMM soundness, or "agrees with LKMM" as a Coq result;
    - that the variants fail on x86;
    - "RC11 logics cannot verify";
    - WriteSnapshot verified, or vertical composition mechanized;
    - incomplete traces;
    - "dependencies preserved" derived from source, while the tags are hand-written.

## Stronger alternative
A generic buffered object `Buf(Σ)`: per-thread pending updates, own-view queries, hidden FIFO publication.
- memory/'s cell is Buf(register).
- SeqLock's marker spec is Buf(pair) plus the marker.
- LatchSet is Buf(set).
- This is TSO-linearizability (Burckhardt, Gotsman, Musuvathi, Yang, ESOP'12; Gotsman, Musuvathi, Yang, ICALP'12).

## Recommended first Writer task
LS-0a: an evidence-only file, `examples/Relaxed/LatchSetRT.v`.
- CE1 and CE2 cell traces in `V (I_tab (dto rc) cat)`.
- A TSO trace for CE1.
- `nuset` with `ce1_overlay_not_rel_lin` and `ce2_overlay_not_rel_lin` for every I.
- Controls: contains = true is rel_lin.
- A K/S/P/R header.
