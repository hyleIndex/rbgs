# Research review — iteration 0 (baseline) — 2026-10-13

> **Provenance.** This baseline audit was run by the orchestrator in a Cowork session, using three read-only audit subagents plus a clean build in a cloud container. It was **not** produced by `rocq-research-reviewer`. The first `/rocq-loop` run should have the Reviewer re-verify the findings in its scope rather than inherit them.

## Scope

- **Repository:** rbgs `relaxed-lin`, HEAD `dcccce0` ("minor", 2026-10-05), plus 19 uncommitted files (see `concern-matrix.md`).
- **Paper:** `../async-ccal/drafts/relaxed-lin/` (`main.tex`, `main-tr.tex`, `Appendix/*.tex`, `todo*.md`).
- **Reviews:** `popl2027-reviews.md`.
- **Concerns in scope:** all of them.

## Checks run

- **Clean build** with Rocq 9.2.0 and Stdlib 9.2.0, built from source; coqrel at `4e450c9`; the uncommitted files overlaid. `./configure && make -k -j2`: **171/171** files compile in 251 s.
- **Admits and axioms:** `grep -rnE '\b(Admitted|admit)\b|^\s*(Axiom|Conjecture)\b'` finds no admits. The `Axiom` lines in `interfaces/` are Module Type fields.
- **`Print Assumptions`** on 109 key theorems. The result is a subset of {`eq_rect_eq`, `classic`, `Parameter A : Type` in ExchangerTSO/TryStackTSO/EBStackTSO}. See `concern-matrix.md` §4.
- **`rocqchk`** crashes on `models/Sets.v` ("Incompatible resolver roots"), so there was no independent checker pass.
- **Source reading** (spot-verified by the orchestrator):
  - `RelaxedLogic.v:869–879` defines `HTripleProvable := exists obligations result final, …`.
  - Nothing outside the defining files uses `RelaxedTaggedLogic`, `GSimRel`, `gsim_rel_lin`, `vlhl_sound` or `presentation_choice`.
  - Nothing outside `memory/` imports `memory.*`.
  - No `ctrl`/OOTA litmus test exists in `memory/Litmus.v`.
  - No queue exists in Coq.
  - `LockedRegisters.VE0` has `Step := fun _ _ _ => True`.
  - The paper still prints `rem:ra-tso` (trace.tex:262), the IRIW remark (trace.tex:225), `deq : N + {⊥}` (trace.tex:92), and the COH/RA equivalence claim (intro.tex:112).

## Verdict

The development is **admit-free and builds**. It contains substantial, closed results:
- the semantic soundness of a global simulation for relaxed linearizability (`gsim_rel_lin`);
- a repaired VLHL semantic soundness theorem (`vlhl_sound`);
- an OMCA declarative characterization of the buffered memory cell, and equality with the x86-TSO machine on the read/write fragment;
- composition theorems with necessity counterexamples;
- a COH SeqLock at module level.

It does **not** yet establish the chain that Reviewer B and the meta-review ask for:
- the RLHL judgement is existential and has no soundness theorem;
- no object or client is verified through RLHL or VLHL;
- the memory models are not connected to any object's underlay;
- every result is about complete traces only.

Several statements printed in the paper are refuted by the Coq development. **Verdict: continue; partial redesign required** (B-1).

## Findings

### BLOCKER

- **[B-1] The RLHL judgement is existential and is not connected to relaxed linearizability.** (research-level design, then actionable)
  - **Where:** `models/simlin/RelaxedLogic.v:869` (`HTripleProvable`), `:1207` (`MethodProvable`), `:1216` (`method_provable_trace_sound`); `RelaxedTaggedLogic.v:997/1002`; `RelaxedRGISimulation.v:176`.
  - **K:** the rules are closed. **S:** a derivation asserts that there *exists* one certified execution with one choice of underlay responses and a `DebtCertificate`. The "soundness" lemmas only unpack this. No theorem maps a derivation, or `(T)RGISimulation`, to `RelaxedGSim.GSimRel` or to `RelaxedTraceLin.rel_lin`. `RelaxedRGISimulation` copies the paper's existential OStep, which is the wrong direction for soundness. `Stable`/`TStable` are defined and never used. **P:** intro.tex:113, implex.tex `prop:rlhl-sc`, programlogic.tex:498 (Logic Soundness). **R:** B: "the program logic, its soundness proof against a weak memory model …".
  - **Evidence:** source reading; no external uses (grep).
  - **Required:**
    - a universally quantified judgement, with rely/guarantee stability and per-call, frameable debts;
    - a theorem from derivations, for all methods and threads, to `GSimRel`, which is already proved sound;
    - a parallel-composition lemma.
    - The redesign choice is research-level (Q1).

- **[B-2] No object or client is verified through RLHL or VLHL. §6.3 describes the Coq inaccurately.** (actionable + paper)
  - **Where:** `examples/View/{ExchangerTSO,SeqLockTSO,EBStackTSO,TryStackTSO}.v`; `examples/Relaxed/SemanticsExamples.v` (the only RLHL use, with a toy `ToyLTS` whose `Step` is `True`).
  - **S:** the view examples use the SC `RGILogic` over view LTS underlays and blocking code; "Possibility states carry no timestamps" (README). `ViewLiftCAS.cas_tso_to_sc` / `cas_sc_to_tso` and `ViewLiftMem` show that the CAS and memory views collapse to SC, so the exchanger, TryStack and EB stack exercise no weak behaviour. Only SeqLock's underlay is weak. **P:** implex.tex §6.3 says "A VLHL possibility state adds only a timestamp to its SC counterpart…" and that the exchanger was "mechanized" in this pattern; intro.tex:113. **R:** B "verification of a concurrent object alongside … its client"; meta "client verification".
  - **Required:**
    - Rewrite §6.3 to say what is mechanized: the SC LHL over derived view underlays, with `ViewLift` collapse and transfer theorems.
    - Verify at least one weak object, and one client of it, end to end through `GSimRel` / `presentation_choice`.

- **[B-3] The weak-memory models are not connected to the object level.** (actionable)
  - **Where:** `memory/*.v`; Mem.tex:103 and :231 cite `mem:cor:rlxlin`, which is undefined.
  - **S:** `memory/` is a standalone trace/graph theory. No LTS built from the buffered cell is shown to satisfy `ViewLHL.implements ν_Mem`. The case studies' "COH" and "TSO" cells are separate abstract specifications. **R:** B "soundness proof against a weak memory model such as RC11".
  - **Required:**
    - an erasure from cell blocks to `RelaxedLTS.ThreadEvent`;
    - a cell LTS;
    - `implements` for that LTS, which needs incomplete prefixes (see M-1);
    - one case study re-run over it.

- **[B-4] The paper prints statements that the Coq development refutes or does not support.** (paper; research-level for what to claim instead)
  - Printed Thm I.11 and Def. I.1 are false as stated: `PrefixView.counterexample_I11`, `reg_not_compat_printed`, `sc_reg_not_compat_printed`, `ViewLHL.vt0_not_sound`. The fixes are `thm_I11_rt`, `vlhl_sound` and `timeline_rel_lin`.
  - Def. 5.8 (compatibility) is unsatisfiable for bracketed methods (`bracketed_not_compatible`), but relaxedlin.tex:126 is unchanged.
  - The printed SeqLock signature is refuted for the COH barrier variant (`SeqLockCOH.paper_signature_fails`, `paper_modes_fail`).
  - trace.tex:262 `rem:ra-tso`, trace.tex:225 (the IRIW ⇒ non-MCA argument), intro.tex:112 (COH/RA "equivalent", not mechanized), intro.tex:113 ("verify the weak Herlihy-Wing queue", not mechanized), trace.tex:92 (`deq : N + {⊥}`, contradicting response B6).
  - Handles: the paper and response A12 say disjoint sum, while Coq `Tens` uses a shared namespace.
  - **Required:** fix the text, or restore the claims in Coq. Decide which (Q2, Q5).

### MAJOR

- **[M-1] Complete traces only.** `RelaxedTraceLin` (by design), `gsim_rel_lin` (needs every call `DeadCall`), `presentation_choice` (complete-only conclusion). So no result yields `implements ν_F` for the next layer, and vertical composition cannot be stated. `SeqLockRT` handles incomplete executions at witness level, via the modelling assumption `wfi_closed`. (actionable; scope decision Q3)
- **[M-2] No general composition theorems in `models/`.**
  - Vertical composition and observational refinement: absent.
  - Horizontal: only `WindowLink`, `WindowLinkTable` and `BracketedLink`, over `module_execution_tagged`. Their hypothesis `positional` / `local_correct` is the component's whole correctness proof, and they assume that this execution's underlay part is rel_lin.
  - `WindowComposition` and `WindowTable` are about abstract settings. (actionable)
- **[M-3] Weak non-vacuity witnesses.**
  - `link_hypotheses_satisfiable`, `window_hypotheses_satisfiable` and `seqlock_module_nonvacuous` use `VE0` with `Step := True` and a single operation of a single thread.
  - No concurrent module execution with weak behaviour (for example load buffering) is shown to satisfy the hypotheses of a link theorem. (actionable)
- **[M-4] RC11 and ARMv8 correspondence is partial and one-directional; the fragment is narrow.**
  - `rc11_containment` gives D1 ∧ D2 ⇒ RC11-COHERENCE only. LB and ISA2 show incomparability.
  - `arm_containment` needs (W) (`ARM.v:78–79`, undischarged).
  - Only `tso_traces` is an equality.
  - Reads and writes only: no RMW/CAS or fences, although the case studies use CAS.
  - "Soundness against RC11" in B's sense cannot hold for this fragment. The paper must say exactly what is proved. (research-level Q2 + actionable)
- **[M-5] The OOTA claim is unmechanized; dependencies are trusted.**
  - No LB+ctrl/addr/data "forbid" theorem exists, even though intro.tex:110 and todo-oopsla-v2 (✅) say so.
  - Dependency tags are hand-written `FutureD deps`, with no "tag = policy(program)" lemma; Imp and its compilation are not mechanized.
  - `module_dependency_soundness` proves only the first half of Lem. wsc-dep. (actionable)
- **[M-6] Paper case studies not mechanized:** Counter_xy and the weak HW queue (no blocking-deq spec anywhere). (Q5)
- **[M-7] Client verification is thin.**
  - `sb_forbidden_window` is about an overlay with I = ∅.
  - `mp_forbidden` and `iriw_forbidden` are at witness level.
  - The SeqLock a=b client promised in response B4 does not exist. (actionable)
- **[M-8] The "advantage over prior models" rests mostly on memory-level facts and refutations of the paper's own earlier definitions.**
  - LatchSet precision, perf ring, and RC11 or SC-linearizability verdicts on object-level executions have no Coq or herd7 artifact.
  - The Python checker labels are set by hand. See `concern-matrix.md` §5. (actionable + research-level choice of the flagship)
- **[M-9] Possibilities.** Coq uses one possibility per execution, keyed by (thread, handle). The paper uses sets of possibilities. Completeness for future-dependent linearization points is therefore unavailable as formalized. (research-level: is completeness claimed?)

### MINOR

- [m-1] `Parameter A : Type` in ExchangerTSO, TryStackTSO and EBStackTSO appears in `Print Assumptions`. Make it a section variable or a functor argument.
- [m-2] `rocqchk` crashes on `models/Sets.v`. Investigate it, or document it in the artifact. `vm_compute` is trusted in six example files; say so in the artifact.
- [m-3] 19 files are uncommitted, including `models/view/*` and `RelaxedGSim.v`.
- [m-4] Stale notes:
  - Mem.tex:819 says the RC11 claim is not mechanized, but `rc11_coherence` mechanizes it.
  - Mem.tex says "twelve" litmus tests, but the table has 11.
  - todo-oopsla-v2 claims "12 litmus tests machine-checked" and OOTA ✅.
- [m-5] Dead or duplicated code: `Stable`/`TStable` are unused; `ViewSpecs.TryStackSpec`/`StackSpec` duplicate `examples/Stacks/StackSpec.v`.
- [m-6] `.claude/` is in `.gitignore`, so the agent and skill configuration is local only.
- [m-7] `rocq-rbgs.opam` requires `rocq-iris 4.5.0`, but no file uses Iris.

## Concern-matrix corrections

This review created the initial matrix. Every row has status 🟡/❌/⚠️ unless marked 📝.

## Stronger or alternative approaches

- **Make `GSimRel` the semantic model of RLHL.** It is already proved sound and uses universal clauses. Prove each rule sound as a closure property of `GSimRel`-style relations, instead of repairing `RelaxedRGISimulation` (copied from the existential paper definition).
- **Vertical composition:** state soundness as `implements ν_E U → implements ν_F (M ∘ U)`. That needs the incomplete-trace version of `rel_lin`, and it composes for free.
- **Memory:** prove `implements ν_TSO` for the x86-TSO machine via `tso_traces`. Then any `presentation_choice` result transfers to x86-TSO. That is the strongest weak-memory soundness statement the current fragment supports.
- **Comparison claims:** mechanize the prior-model verdict for the same object-level execution (for example RC11's verdict on the SeqLock ⊗ z load-buffering execution `X_lb`), instead of comparing only at the memory level.

## Redesign assessment

The RLHL program logic (`RelaxedLogic`, `RelaxedTaggedLogic`, `RelaxedRGISimulation`) needs redesign before any soundness proof is possible. The semantic layer (`RelaxedTraceLin`, the module semantics, `RelaxedGSim`, `ViewLHL`), the memory layer and the composition examples are sound foundations. They need connecting and generalizing, not redesigning.
