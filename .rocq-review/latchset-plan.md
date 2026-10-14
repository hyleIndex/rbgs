# LatchSet mechanization plan (v2, 2026-10-13: §6 overrides §1–§5; source `latchset-claim-coverage.md` + author decisions)

## 0. Sources and decisions

- **Author decisions, 2026-10-13** (research-intent §8):
  - LatchSet first;
  - ARM option C (x86-TSO only);
  - flush events not in the Coq trace model;
  - LatchSet = the sorted-array design of `async-ccal/drafts/relaxed-lin/Claude outputs/litmus-check/tests_latch_set.py`;
  - single-writer discipline (client precondition, no lock);
  - LatchSet only for now (WriteSnapshot paper-level; the paper must not claim it is mechanized);
  - earlier: LatchSet is built directly on buffered cells (buffered-cell plan, author OK 2026-10-13).
- **Checker verdicts** (`run_latch_set.log`, `run_latch.log`; LKMem = COH cells + object-scoped wmb (W→W) and rmb (R→R)):
  - full idiom: bad `contains` forbidden;
  - each of the five broken variants allows it: no base-address dependency, no reader rmb, no wmb after seq:=1, no wmb before seq:=2, no wmb after seq:=2;
  - linearizable answers are allowed.
- **Paper:**
  - intro.tex:106 ("We verify LatchSet, a latched set based on the Linux kernel's latch technique …");
  - overview.tex:270–331 (fig:latech-set: LatchSet exports "atomic set specification + relaxed ordering", "load buffering admitted", "program dependencies preserved");
  - todo-oopsla.md CS1 (counterexamples, positive S1 = "SC core + F0–F5", link; ~5–6 w);
  - todo-oopsla-v2.md:28 (precision: SC linearizability "proves" two wrong readers; RC11-based logics cannot verify the correct one).
- **Reusable Coq infrastructure** (all Closed):
  - F-1 `memory/TableBarrier.v` (buffered cells under `I_tab`, ghost barriers, `contract_handle_invariant`);
  - F-3 `WindowTableJ`/`WindowLinkTableJ` (joint specs; `link_lp_ord_fields`; constant-compE joint underlay);
  - D-1 `SeqLockModuleGen` (pattern for a validity-isolated module bridge);
  - T-1 `FuturesShape` (generic shape machinery for futures programs);
  - `RelaxedLang.FutureD` (dependency-tagged invocations; frontier rule F3).

## 1. The object

Parameters: capacity `N`; keys `nat`.

Cells:
- `seq`;
- for each copy `c ∈ {0,1}`: `n_c` (size) and `a_c_0 … a_c_{N-1}` (sorted keys).

Barriers: `wmb`, `rmb` (ghost locations Bw ≠ Br, as in F-1).

```
insert(k)   [single writer]:
  wmb; s <- rd(seq); wrt(seq, s+1); wmb;     // s+1 odd: readers use copy 1
  modify copy 0 to insert k (read n_0, a_0_i; shift; write a_0_i, n_0);
  wmb; wrt(seq, s+2); wmb;                    // s+2 even: readers use copy 0
  modify copy 1 likewise
contains(k):
  do { s <- rd(seq); c := s & 1;
       m <- rdD(n_c) [dep s];                 // address dependency on s (FutureD)
       r := false; for i < m: v <- rdD(a_c_i) [dep s]; if v = k then r := true;
       rmb } while (rd(seq) <> s);
  return r
```

- **Open detail (LD-0):** whether the writer reads `seq` (Linux: `seq++`, a plain read-modify-write by the single writer) and its own copy, or writes known values. The checker's writer writes constants (writer-private knowledge). A stateless futures module must read the cells, so the writer reads its own earlier writes. See risk R1.
- Loop bounds are control dependencies and do not order plain reads (the checker's policy `rd ∉ K`). Only the address dependency on `s` orders the data reads after `rd(seq)`.

**Overlay** `F_L`:
- `insert(k) : unit` and `contains(k) : bool`;
- spec `ν_Set`: atomic set (grow-only), `contains(k) = (k ∈ state)`;
- client preconditions as hypotheses of the module theorem, not as part of `ν`:
  - (P1) inserts never overlap (single writer);
  - (P2) at most `N` distinct keys.

**Categories:** derived by window dominance from the table (`WindowTable.dto`), checked in Coq as for SeqLock. Expected: insert ↦ a Wmb-like category, contains ↦ an Rmb-like category (todo: "exports W / R instead of Local").

**Windows / LPs** (CS1):
- insert: the second switch write `wrt(seq, s+2)`. **To be checked:** the window must contain the LP, with dominance at its ends.
- contains: the successful retry read.

## 2. Design decisions to settle before code

- **LD-0: writer reads.** (a) The writer reads `seq` and its copy (faithful to Linux). (b) The writer writes known values (checker style; needs writer-private state, which `RelaxedModuleImpl` does not have). **Proposed: (a).**
- **LD-1: proof route over buffered cells.**
  - (a) **Register-first + SC-ification.**
    - Prove LatchSet at register level (COH registers + table): witness model, S1 = "SC core + F0–F5", module theorem.
    - Lift to buffered cells by SC-ifying hybrid witnesses (the SeqLock S-1 pattern).
    - Matches the paper's "conservative extension: SC proof + ordering facts".
  - (b) **Direct buffered proof** (publication reasoning in S1).
  - (c) **Register only**, stating the Q6-2-type x86 grounding gap.
  - **Proposed: (a).** Risk R1 is the crux.
- **R1 (the main technical risk): writer store forwarding.**
  - With (LD-0a), the writer's reads of `seq` and of its own copy may forward from its own pending writes.
  - SeqLock's SC-ify relied on "x/y reads never forward" (F1). That fails here.
  - **Candidate fix:** a "single-writer forwarding relocation" lemma. Every forwarded read of a single-writer location reads the co-latest write, so in the SC-ified order it can be placed immediately after that write's flush and before the flush of any later same-thread write it is ordered before (same-location coherence, or wmb). Validity then holds.
  - **Must be checked on a concrete execution before committing to (a).**
- **LD-2: overlay composition.**
  - LatchSet alone is one component: joint = product, `window_link_table` suffices.
  - LatchSet ⊗ client cell (MP through the latch, `tests_latch_mp.py`) needs the contract tensor (F-3 `window_link_table_J`), as for SeqLock ⊎ z.
  - **Proposed:** LatchSet alone first; ⊗ client later (LS-6).
- **LD-3: preconditions P1/P2 at module level.** State them as trace predicates on the overlay (no overlapping inserts; ≤ N distinct keys). The module theorem quantifies over executions satisfying them.

## 3. Phases (sizes S/M/L; dependencies)

- **LS-0 (S; none): design probe.** No new `.v` in `_CoqProject`; scratch only.
  - Fix the exact program text (LD-0) and `N`.
  - Compute categories and the windows' dominance in Coq (Eval on `WindowTable.dto`).
  - Map the checker's 6 + 2 cases to Coq candidate executions.
  - R1 feasibility: one concrete hybrid execution with a forwarded writer read, SC-ified by hand, checking validity.
  - Output: amendments to this plan.
- **LS-1 (L; LS-0): register-level witness model and refutations.**
  - `LatchSetCOH.v`: blocks (insert with shift data; contains with iterations and scan values), calls, `WF` (as `SeqLockCOH.WF`), and the five broken variants as program variants.
  - **Refutations (CS1 ①):** for each broken variant, a concrete WF execution whose overlay has no `ν_Set` witness (bad contains), with a decision procedure or a direct proof.
  - Non-vacuity: the full idiom on the same shape has no such execution (by S1, in LS-2).
- **LS-2 (L; LS-1): positive S1.**
  - `latch_S1`: `ν_Set` on the lp-sorted overlay ops of any `WF` execution, with P1/P2.
  - `latch_S1_ord`.
  - **Proof structure (CS1 ②):** SC core + ordering facts F0–F5, each tied to one barrier/dependency. Each broken variant's counterexample violates exactly one F_i (cross-reference LS-1).
- **LS-3 (M; none): futures program and shape.** `LatchSetProg.v`: `M_L` with `FutureD` address dependencies; `M_L_shape` via `FuturesShape`; non-vacuity derivations.
- **LS-4 (L; LS-1, F-1): buffered witnesses and SC-ification.**
  - `LatchSetBuf.v`: `BWF_L` (hybrid: cells under `I_tab`, ghost barriers);
  - the R1 relocation lemma;
  - `bwf_scify_WF_L : BWF_L X → WF (scify X)`;
  - lp-order agreement.
- **LS-5 (L; LS-2, LS-3, LS-4): module theorem.**
  - `latchset_module_rel_lin`: complete executions with P1/P2 whose underlay is rel_lin w.r.t. the hybrid spec have an overlay that is rel_lin w.r.t. `ν_Set`.
  - Route: a D-1-style generic bridge for `M_L`, plus `WindowLinkTable(J)`.
  - Header: x86-TSO scope (option C), complete executions only.
- **LS-6 (M; LS-5): non-vacuity and clients.**
  - Concrete module executions: LB through LatchSet ("load buffering admitted"), a contains overlapping an insert.
  - Module-level counterexamples for the broken variants (CS1 ①, at module level).
  - Optionally LatchSet ⊗ client cell (MP through the latch) via `window_link_table_J`.
- **LS-7 (S-M; LS-5, optional): x86 grounding** of the hybrid underlay (as G-1).

**Paper items:**
- the precision table (B1);
- the F0–F5 ↔ broken-variant correspondence;
- line counts ("SC proof + adapter");
- WriteSnapshot stays unmechanized (author decision);
- vertical composition LatchSet → WriteSnapshot is a paper claim with no Coq (M-18 record).

## 4. Risks

- **R1:** writer store forwarding (above).
- **R2:** variable-length scans (loops over `m`) make blocks and windows data-dependent. The block model must carry scan lengths.
- **R3:** the address-dependency tag (`FutureD`) must yield the underlay rhb edge `rd(seq)` → data reads. Check this against the frontier rule F3 in LS-0.
- **R4:** size. CS1 estimated 5–6 weeks. This plan is larger, because buffered cells make LS-4 L-sized.


## 5. v1 amendments (design review `latchset-design-review.md` + author decisions, 2026-10-13). These override §1–§4.

- **Spec (B-5, author):** the overlay spec is **ν_BS**, a buffered grow-only set.
  - Hidden publication markers, one per insert, placed after its LP, in FIFO order.
  - A non-writer's contains answers membership in the *published* inserts; the writer's contains answers membership in its *issued* inserts.
  - `OvOp` carries the thread id.
  - Conservativity lemma: `ν_Set ⊆ ν_BS` (marker right after the LP).
  - The atomic ν_Set is refuted over buffered cells (CE1), and CE2 is the object-level SB+rfi.
- **P1 (author):** one designated writer thread `t_w`; its inserts are pairwise non-overlapping. P1 is a module-trace predicate. **P2:** at most N distinct keys.
- **LD-0 (adopted):** (a′). The writer reads `seq` and copy 0 only, then writes both copies from the computed array.
- **Categories (author OK):**
  - insert ↦ **Wmb**, window [wmb0, wmb3], LP = issue of `wrt(seq, s+2)`, marker = its flush;
  - contains ↦ **DR**, window [first `rd(seq)`, retry `rd(seq)`] of the last iteration;
  - no Rmb export, and no MP-through-latch client for now;
  - reuse `WindowTable.latch_*` (:526–545).
- **Proof route (replaces LD-1(a) and R1):** a direct buffered proof, built from:
  - L1 read-own-latest (one writer per location);
  - L2 published `seq` monotone;
  - L3 `seq` constant on [p1, p2];
  - L4 copy `s&1` stable on [p1, p2], holding the state after ⌊s/2⌋ inserts;
  - L5 data reads inside [p1, p2] (F3 address tag, plus R→Rmb→R);
  - a pure SC core.
  - These are the paper's F0–F5. There is no register-level model and no SC-ification. R1 (writer forwarding) is handled by L1.
- **Underlay:** ν_{I_tab}(dto). There is no atomic object, so this is not "hybrid", and F-2 is **not** a dependency. LS-5 needs the Op-list ν_{I_tab} with witness-index handles, and F-1's owed bridges (i) `nu_handle_invariant` and (ii) `po_handles_vs_index`.
- **Tags (M-23):**
  - M_L carries address tags on the data reads, and data/control tags on the writer's writes;
  - the five broken variants are flags of one M_L;
  - a tag-policy check or an audit lemma, named in the header;
  - one kernel derivation of the F3 → rhb edge.
- **ARM (author: "we want latch set over ARM v8"):** LatchSet targets ARMv8, so option C does not apply to it.
  - **Model-relative precision** (M-22): on x86 all five variants are correct. On ARMv8 the address dependency and the barriers are load-bearing, which is the point of the example.
  - **New track LS-A (ARM):**
    - LS-A1 (M): litmus-level evidence in `memory/ARMBar.v`'s three readings for the latch idiom (full idiom forbidden; each broken variant allowed), with herd7 files in `memory/herd/aarch64/` (UNVERIFIED until the author runs herd7);
    - LS-A2 (research-level, to design with the author): how the module theorem reaches ARMv8. Options: an ARM grounding of ν_{I_tab}(dto) at cell level (as `TableBarrierTSO` for x86), or a compilation scheme (cf. option B, m-45).
    - M-15 (waited load, then another cell) applies to LatchSet's interface on ARM; LS-A2 must address it.
- **Amended phases:**
  - **LS-0a** (Writer, S): evidence file `LatchSetRT.v`. CE1/CE2 cell traces in V_{I_tab}; a TSO trace for CE1; ν_Set refuted for every I; controls. Design-independent.
  - **LS-1** (M): ν_BS, `ν_Set ⊆ ν_BS`, client lemmas (monotonicity, prefix); CE1/CE2 accepted by ν_BS.
  - **LS-2** (M): M_L with tags and variant flags; shape via `FuturesShape`; an F3 → rhb non-vacuity derivation.
  - **LS-3** (L): direct buffered S1 / S1_ord (L1–L5 + SC core).
  - **LS-4** (M): refutations of the variants on buffered traces (`V_of_tchk`), with an observing prefix under ν_BS.
  - **LS-5** (L): the module theorem (ν_{I_tab} underlay → ν_BS overlay), possibly via a generalized module bridge (D-1 suggestion 3).
  - **LS-6** (M): clients and non-vacuity at module level.
  - **LS-A1/A2:** the ARM track (above).
  - **LS-7** (optional): x86 module grounding.
- **Paper (Q7 of the review):**
  - **May claim:** relaxed-linearizable to a buffered set, under P1/P2, for complete executions, with hand-written tags unless a policy lemma exists.
  - **Must not claim:** "atomic set", ν_E = "coherent cells", LKMM agreement as a Coq result, "RC11 logics cannot verify", WriteSnapshot or vertical composition mechanized.
  - **ARM claims:** only after LS-A2.


## 6. v2 (author: support ALL overview claims; claim-coverage workflow). §6 overrides §1–§5.

- **Spec:** atomic ν_Set (`LatchSetRT.nuset_from`) with a trailing `smp_mb` in insert. ν_BS is withdrawn.
- **Exports:** insert ↦ DRFence (window [wmb0, mb]); contains ↦ DR (window [rd seq, retry rd seq]).
  - The insert's LP is the hidden flush of `seq:=s+2`, which needs the LS-HLP extension.
- **Code** (coverage §3.1):
  - the latch technique with LD-0 (a′) plus a trailing `smp_mb`;
  - ARM mapping wmb = DMB ISHST, rmb = DMB ISHLD, mb = DMB ISH;
  - ARM-only fixes (n → a_i edge; M-15) are to be decided from the LS-A1 litmus results.
- **Phases:** the table in `latchset-claim-coverage.md` §5 is authoritative:
  - MD-1, G-1, MD-2;
  - LS-1′, LS-2, LS-HLP, LS-3, LS-5, LS-6, (LS-4);
  - H-1, H-2;
  - OOTA-1, CE-1, LBCOH-1;
  - WS-0..WS-2;
  - V-1, V-2, X-1, V-3;
  - A-1, A-2;
  - E-0, P-1.
- **Critical path:** decisions → MD-1 → G-1 → LS-HLP + LS-2 → LS-3 → LS-5 → H-2 → V-3. V-2 (XL) runs in parallel.
- **Wave 1** (independent; parallel; each a separate new file):
  - E-0: commit the scratch evidence;
  - MD-1: drain primitive;
  - LS-2: M_L program, tags, variants, shape;
  - WS-1: `rel_lin_ev` + conservativity;
  - A-1: ARM litmus for the latch, plus herd files.
