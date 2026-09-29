# `memory/` — the buffered memory and its declarative characterization

Mechanization of Appendix L ("Memory Cells with Store Forwarding") of the
relaxed-linearizability paper: the buffered memory cell, the flush contract,
the OMCA declarative form, the equivalence theorem between the two, and the
comparison with x86-TSO, ARMv8 and RC11 (Section L.7).

This directory is self-contained apart from `models/RelaxedSignature.v`
(fence modes, `RelaxedSig.t`) and its dependency cone (`models/EffectSignatures.v`,
`models/Sets.v`, `interfaces/{Category,Functor,FunctorCategory,MonoidalCategory,Limits}.v`).
It does not depend on `models/simlin/`.  Logical root: `memory`.

## Files (in dependency order)

| File | Contents | Paper |
| --- | --- | --- |
| `Prelude.v` | relation algebra (`∪`, `;;`, `⦗P⦘;;R`, `R⁺`, `acyclic`), positions in lists (`before`), pigeonhole, **linear extension of a finite acyclic relation**, acyclicity from a strictly increasing potential, finite maxima | conventions |
| `Cell.v` | `Cell_M[Loc]` as an effect signature and as a relaxed effect signature whose semi-independence relation `mode_indep` is induced by the fence modes; blocks and traces; the cell `Buf_x` (`cell_step`, `VBuf`) and its functional presentation (`enabled`/`next`/`state_after`); pending writes `pend`; the bookkeeping lemma; the flush contract `contract I`; the memory `V I` and the hidden specification `nu I`; the instances `TSO_modes`, `PSO_modes`, `RC_modes` and the shape lemma | Def. cellsig, Def. instances, Lem. shape, Def. cell, Def. pend, Lem. book, Def. contract, Prop. contract, Def. model |
| `Tensor.v` | location sets, `proj_set` (`s↾A`), traces `over` a set; the **contract tensor** `tens Pc A B νA νB` of Def. mem:def:tensor (`ν_A ⊗ ν_B = {s | Pc(s) ∧ s↾A ∈ ν_A ∧ s↾B ∈ ν_B}`), its algebra (commutative; associative and unital when `Pc` is closed under projection; `Pc = True` gives Def. spec-tensor), the iterated tensor `big Pc fam ls` with its bracketing-free characterization `big_iff` (hence `big_perm`, `big_app`); `pend` commutes with projection, **`contract_proj_closed`**; `V_on I A` (= `V_I[A]`), **`memory_tensor : V_I[A ∪ B] = V_I[A] ⊗ V_I[B]`**, **`memory_is_tensor_of_cells : V_I[ls] = ⊗_{ℓ∈ls} VBuf_ℓ`**, `V_big`, `nu_big`; `ContractMatters` (a trace of `VBuf_x ⊗_True VBuf_y` outside `V_RC[{x,y}]`) | Def. tensor, Def. model, the remark after Def. model ("the two agree whenever Pc is closed under projection") |
| `Declarative.v` | candidates (`cand`, `wf_cand` incl. the handle discipline), witnesses `(mo, rf)` as relations, `rb`, `rfe`/`rfi`, `pre0 = po \ I`, `admissible`, `ppo`, `coh`/`D1`, `Dc`/`D2`, `consistent`, `presents`, `respects`; `D1` is stated once and shown equivalent to the per-location form | Ass. handles, Def. cand, Def. ppo, Def. cons, Def. present |
| `Pending.v` | bookkeeping along a fixed trace by index: `pending_iff` (a write is pending iff issued and not yet published), uniqueness of the publishing flush, head/last characterizations, the global value after a trace, effectiveness of flushes and the value read by a read block | (proof infrastructure for L.6) |
| `Extraction.v` | handle order, completion, the witness extracted from a completed trace, its well-formedness, (D1) via a lexicographic rank potential, (D2) via a position potential; `Extraction.extraction` | Lem. handleorder, Lem. complete, Lem. extract |
| `Realization.v` | consequences (C1)–(C3) of (D1); the clock; the scheduling graph `𝔄` (`node`, `E` = (E1)–(E6)); Claim 1 (acyclicity) by an explicit potential on nodes; the trace as a topological order; Claim 2 (every block enabled, the contract holds); `Realization.realization` | Lem. realize |
| `Equivalence.v` | `Equivalence.declarative_characterization` and its instances `declarative_RC`, `declarative_TSO`, `declarative_PSO` | Thm. decl |
| `Consequences.v` | consequences of (D1): `rfi ∪ moi ∪ rbi ⊆ po_loc`, same-location program order between writes is `mo`; for the release/acquire instance, `mode_indep_iff` and Cor. pre (`pre0_iff`: `po \ RC.I = po_loc ∪ [acq];po ∪ po;[rel]`); the `Dc` generators `[acq];po`, `po;[rel]`, `rfe`, `mo`, `rb`, `[rd];pre` | (C1)–(C3), Cor. pre |
| `RC11.v` | RC11 on the fragment: `rs`, `sw`, `hb`, `eco`, `coherence`, `no_thin_air`, `rc11_consistent = coherence ∧ no_thin_air` (ATOMICITY and SC are vacuous); shape of an `hb` path (program order, or `Dc⁺` between a release and an acquire); normal form of `eco`; `RC11.rc11_coherence` / `RC11.rc11_containment`: (D1) ∧ (D2) ⇒ COHERENCE | Prop. rc11 |
| `ARM.v` | ARMv8's `obs`, `dob`, `bob`, `ob` on the fragment, with dependency relations `addr`, `data`, `ctrl` as parameters and the wait placement (W) as hypothesis; `ARM.obs_dob_bob0_Dc : obs ∪ dob ∪ bob_0 ⊆ Dc⁺`, `ARM.ob_Dc_S : ob ⊆ (Dc ∪ S)⁺`, `ARM.arm_containment` | Prop. arm |
| `TSO.v` | the x86-TSO machine (read/write fragment) as an LTS, `V↑_TSO` (witnesses issuing writes in handle order), `erase`; the simulation `μ`; `TSO.tso_traces : erase(V↑_TSO) = Tr(TSO_Locs)` | Def. tsomachine, Prop. tso |
| `Litmus.v` | the four decisive litmus witnesses as concrete candidates (`cand_of`, `witness_of`): LB (ours allow, RC11 forbid), ISA2+rel+acq (ours forbid, RC11 allow), SB+rel+acq (ours allow, ARM forbid), RSW+rel (ours forbid, ARM allow); "forbid" quantifies over all well-formed witnesses (and, for us, all admissible `pre`); **MP+rel+acq** (`MP.ours_forbid`, and through Thm. decl the trace-level `MP.nu_forbid`): the trace `wy·wx·rx·ry` is in `ν_RC[{x}] ⊗_True ν_RC[{y}]` but not in `ν_RC[{x,y}]` (`MP.hidden_tensor_is_not_a_product`) | Ex. sbrelacq, isa2, rsw, LB; Δ1, Δ2, Δ4, Δ5; Def. tensor |
| `ARMDecl.v` | the ARM-shaped global axiom: `ppo_ARM = dob ∪ bob`, `Dc_ARM = ppo_ARM ∪ rfe ∪ mo ∪ rb`, `consistent_ARM = D1 ∧ acyclic Dc_ARM`; the generators of `ob` as an inductive `gen`; redirection of `ob` edges around internal `moi`/`rbi` edges (`gen_rbi`, `gen_moi`); `ARMDecl.arm_declarative : consistent_ARM ⟺ arm_consistent`; `Dc_ARM ⊆ (Dc_pre ∪ S)⁺` | (new; the exact-ARM version of (D2)) |

## Main statement

```coq
Theorem declarative_characterization
    (C : Cfg) (I : cell_op C -> cell_op C -> Prop)
    (HI : forall m m', I m m' -> op_loc m <> op_loc m')
    (X : cand C) (HX : wf_cand X)
    (pre : relation (block C)) (Hadm : admissible X I pre) :
  (exists w, wf_witness X w /\ consistent X I w pre) <->
  (exists s, nu I s /\ presents s X /\ respects s pre).
```

`consistent` is (D1) ∧ (D2); `nu I` is `hide(V_I[Locs])`.

### Comparison with the reference models (Section L.7)

All three are for the release/acquire instance `RC_cfg dec` and an
admissible `pre` (`Consequences.v` provides the shape facts).

```coq
(* RC11.v *)
Theorem rc11_coherence : coherence.          (* under D1 X w, D2 X I w pre *)
(* ARM.v *)
Theorem obs_dob_bob0_Dc : obs ∪ dob ∪ bob0 ⊆ Dc⁺.
Theorem ob_Dc_S : ob ⊆ (Dc ∪ S)⁺.
Theorem arm_containment : acyclic (Dc ∪ S) -> arm_consistent.
(* TSO.v *)
Theorem tso_traces l : (exists s, V_up s /\ erase s = l) <-> Tr l.
(* Litmus.v *)
Theorem LB.ours_allow    : exists w pre, wf_witness X w /\ admissible X I pre /\ consistent X I w pre.
Theorem LB.rc11_forbid   : forall w, wf_witness X w -> ~ rc11_consistent X w.
Theorem ISA2.ours_forbid : forall w pre, wf_witness X w -> admissible X I pre -> ~ consistent X I w pre.
Theorem ISA2.rc11_allow  : exists w, wf_witness X w /\ rc11_consistent X w.
Theorem SB.ours_allow / SB.arm_forbid / RSW.ours_forbid / RSW.arm_allow   (likewise, against arm_consistent)
(* ARMDecl.v *)
Theorem arm_declarative : consistent_ARM <-> arm_consistent.   (* D1 ∧ acyclic(Dc_ARM) ⟺ INTERNAL ∧ EXTERNAL *)
Theorem Dc_ARM_Dc_S : Dc_ARM ⊆ (Dc ∪ S)⁺.
```

### Composite memory (Def. mem:def:tensor)

```coq
(* Tensor.v; C : Cfg, I : cell_op C -> cell_op C -> Prop, A B : Loc C -> bool *)
Definition tens Pc A B nuA nuB s := over (lunion A B) s /\ Pc s /\ nuA (proj_set A s) /\ nuB (proj_set B s).
Lemma tens_true    : tens (fun _ => True) A B nuA nuB s <-> spec_tens A B nuA nuB s.   (* Def. spec-tensor *)
Lemma tens_comm    : tens Pc A B nuA nuB s <-> tens Pc B A nuB nuA s.
Lemma tens_assoc   : proj_closed Pc -> tens Pc (A ∪ B) D (tens Pc A B nuA nuB) nuD s <-> tens Pc A (B ∪ D) nuA (tens Pc B D nuB nuD) s.
Theorem big_iff    : proj_closed Pc -> Pc [] -> big Pc fam ls s <-> over (lset_of ls) s /\ Pc s /\ forall x, In x ls -> fam x (proj x s).
Theorem contract_proj_closed I : proj_closed (contract I).
Theorem memory_tensor : V_on I (A ∪ B) s <-> tens (contract I) A B (V_on I A) (V_on I B) s.        (* V_I[A ∪ B] = V_I[A] ⊗ V_I[B] *)
Theorem memory_is_tensor_of_cells : V_on I (lset_of ls) s <-> big (contract I) (fun x => VBuf x) ls s.  (* V_I[ls] = ⊗_{ℓ∈ls} VBuf_ℓ *)
Theorem V_big  : (forall x, In x ls) -> V I s <-> big (contract I) (fun x => VBuf x) ls s.
Corollary nu_big : (forall x, In x ls) -> nu I s <-> exists s', big (contract I) (fun x => VBuf x) ls s' /\ hide s' = s.
Theorem ContractMatters.contract_matters : spec_tens {x} {y} (VBuf x) (VBuf y) s /\ ~ tens (contract I) {x} {y} (VBuf x) (VBuf y) s.
(* Litmus.v *)
Theorem MP.hidden_tensor_is_not_a_product : spec_tens {x} {y} (nu_on I {x}) (nu_on I {y}) l /\ ~ nu_on I ({x} ∪ {y}) l.
```

* `V_on I A` is `V_I[A]` (traces over `A` satisfying the contract whose
  projection at every `ℓ ∈ A` is in `VBuf_ℓ`); `V_on I lfull = V I`.
  `big` folds the binary tensor along an enumeration of the locations,
  `big_iff` shows the result is independent of bracketing and order
  (`big_perm`, `big_app`) whenever `Pc` is closed under projection, and
  `contract_proj_closed` shows the flush contract is, for every `I`
  (the published write at a flush of `s↾A` is the one of `s`, and the
  pending writes quantified over form a subset).  This is the remark
  after Def. mem:def:model.
* The contract is what makes `⊗` differ from the product of its
  factors, before and after hiding: `contract_matters` (a release write
  flushed before an earlier relaxed write at another location) and
  `MP.hidden_tensor_is_not_a_product` (message passing with
  release/acquire: both single-cell projections are hidden-cell
  behaviours, the composite trace is not in `ν_RC[{x,y}]`, by
  `MP.ours_forbid` transported through Thm. decl).  So the hidden
  memory is `hide(⊗_{Pc} VBuf_ℓ)` and not `⊗_True hide(VBuf_ℓ)`.
* `Tensor.v` is axiom-free; the `MP` results use `classic` through
  `read_source` and Thm. decl.

* `RC11.v` and `ARM.v` take (D1) as a hypothesis (both use
  `rfi ∪ moi ∪ rbi ⊆ po_loc`); `RC11.v` also takes (D2).  `ARM.v` takes the
  dependency relations `addr data ctrl : relation block`, the assumption that
  every dependency starts at a read, and (W) in the two clauses
  `dep ⊆ pre` and `dep ; po ⊆ pre`.  It does not need `dep ⊆ po`.
* `ARMDecl.v` replaces `ppo_pre` by ARM's own intra-thread generators and
  keeps the communication part of (D2).  `Dc_ARM` differs from the
  generators of `ob` only by the internal edges `moi ∪ rbi`; under (D1)
  every `ob` edge into the source of such an edge can be redirected to its
  target, so the two acyclicity conditions agree.  The only assumption on
  the dependency relations is `data ⊆ _ × W`.  This is the declarative
  side of an "ARM instance"; the buffered cell does not realize it (its
  trace order chains through `po_loc`, Ex. rsw), see the project notes.
* Together: ours ⇒ COHERENCE (`rc11_containment`) but not NO-THIN-AIR
  (`LB`), and RC11 ⇏ ours (`ISA2`); ours + `S` ⇒ ARM (`arm_containment`),
  ARM ⇏ ours (`SB`), ours ⇏ ARM (`RSW`).  The three models are pairwise
  incomparable, and `ARMDecl.v` is the exact ARM axiom in our shape.
* `TSO.v` is stated over the `TSO_cfg` instance, where no two writes are
  semi-independent, so the contract at a flush says the published write has
  the least handle among the thread's pending writes.  The machine's
  successor states are specified pointwise (memory and buffers are
  functions), which avoids functional extensionality; `tstep_det` shows the
  machine is deterministic up to extensional equality.  `tso_traces` is
  axiom-free.

Axioms: `Classical_Prop.classic` only (check with `Print Assumptions`).
No `Admitted`.

## Design decisions (differences in presentation from the paper)

* **Traces are lists of blocks**, not of events. The transition labels of
  Def. cell are blocks, every block of `V` is atomic, and the `\todo` after
  Def. pend (flushes must appear atomically) is thereby settled by
  construction. An erasure to `RelaxedLTSSpec.ThreadEvent` lists is not
  part of this directory.
* **`I` is a parameter.** Section L.6 fixes `I = RC.I`, but its proofs use
  only that `I` relates no two invocations at the same location
  (Lemma shape). The theorem is proved for every such `I`, and instantiated
  to the mode-induced relations of TSO, PSO and RC.
* **Operations are blocks.** A candidate's operations carry thread,
  location, mode, value and handle, so `presents` is a permutation and the
  bijection of Def. present is the identity.
* **Witnesses are relations** (`mo`, `rf`), with the initial write implicit:
  `mo` is a strict total order on the writes of each location, `rf` is
  functional, a read without source reads `0`, and `rb r u` holds iff every
  source of `r` is `mo`-before `u` (vacuously, for the initial write).
* **Program order is a field of the candidate** (`po`), total per thread,
  with Assumption handles as the well-formedness condition `po_handles`.
* **Potentials instead of induction on cycles.** Both acyclicity claims of
  Lemma extract and Claim 1 of Lemma realize are proved by exhibiting a
  strictly increasing potential (`Prelude.acyclic_by_rel_potential`); the
  potential for Claim 1 gives issue nodes a value from the reads reaching
  them by `pre`, which replaces the "detour" argument of the paper.
* **Classical logic** is assumed (`Coq.Logic.Classical`) so that potentials
  and maxima can be specified rather than computed. Every concrete relation
  is decidable, so the axiom could be discharged with decidability
  hypotheses.

## Building

The files are listed in `_CoqProject` (root `-R memory memory`); the usual
`./configure && make` builds them with the rest of the development.  To
build only this directory against an already compiled `models/RelaxedSignature.vo`:

```sh
for f in Prelude Cell Tensor Declarative Pending Extraction Realization Equivalence \
         Consequences RC11 ARM TSO ARMDecl Litmus; do
  coqc -R interfaces interfaces -R models models -R memory memory memory/$f.v
done
```

Verified with Coq 8.18.0.
