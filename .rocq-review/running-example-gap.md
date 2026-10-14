# Running example: gap assessment (2026-10-13)

Produced by a 9-agent read-only workflow: 5 mappers (paper obligations, example choice and plans, Coq SeqLock inventory, framework, reviewer requirements), 1 synthesis, and 3 independent `rocq-research-reviewer` verifications (overclaim, underclaim, paper fidelity), on HEAD `6e2b575` plus the uncommitted `SeqLockClients.v` and `SeqLockLB.v`, under Rocq 9.3.0.
The verifiers ran while `SeqLockLB.v` was still being written. Rows RE-06 and RE-07 therefore carry the orchestrator's verified final state, not the verifiers' intermediate views.
Statuses are claims checked by the verifiers, not author decisions.

## What "usable as the running example" means (synthesis)

Scope of the question. The paper calls LB/OOTA "the running example" (intro.tex:74). That example is a memory-level litmus test and stops at §3. SeqLock is introduced in §2.4 as the composition case study (overview.tex:276) and is then dropped. The author decisions of 2026-10-13 (research-intent.md §8) are: scope = oMCA; the two flagships are (1) SeqLock on COH (Counter → TicketLock → SeqLock tower, with rmb/wmb) and (2) LatchSet with write snapshot; RLHL is not on the critical path, and the examples are proved by the window route. Only flagship (1) has substantial Coq. I therefore define the running example as the object SeqLock ⊎ COH[z]: the SeqLock over TicketLock ⊗ COH[x] ⊗ COH[y] ⊗ Barrier, composed with a client cell z, on COH with selective barriers, built as the tower Counter → TicketLock → SeqLock. LB/OOTA stays as the memory-level motivating litmus in §1–§2, and the running example carries it to the object level: SeqLockCOH.X_lb is load buffering through the object. LatchSet is a separate case-study section; it carries address dependencies and is not on this path.

The example is "usable" only if every paper section that uses it is backed as follows. K = kernel-checked, S = what the statement says, P = what the paper claims, R = what a reviewer requires.
(1) Identity (P = S). The code, interface and sequential specifications printed in the paper are literally the Coq objects (SeqLockProg.M/E/F, nu_sl, nuEc/nuFc, TicketLockCOH.tl_step, the categories write ↦ Wmb, read ↦ Rmb and their derived I), or each deviation is named.
(2) Correctness at the level the paper claims (K). Module-level rel_lin theorems for the SeqLock layer and for the linked tower, the latter as one inlined module. Witness-level lemmas may be cited only as proof steps.
(3) Composition. The horizontal step is the general theorem WindowLinkTable.window_link_table, and §5 states that theorem rather than the refuted Def. 5.8. The vertical step is presented honestly as the inlined link, unless a general judgement is mechanized.
(4) Grounding in scope (oMCA). The lowest-level cells and barriers are tied to memory/ by a stated correspondence with a stated direction. Whatever is not tied (faa, an abstract TicketLock) is disclosed as a hypothesis.
(5) Non-vacuity and the point of the example (K). At least one concrete concurrent module execution meets every hypothesis, exhibits object-level LB with same-thread overlap, and is not classically linearizable. A writer/reader execution instantiates the client theorems. The OOTA variant is forbidden.
(6) Clients (K). a=b, same epoch and MP-forbidden are derived from the interface alone, at module level.
(7) Trust (K). Print Assumptions is within {eq_rect_eq, classic} per cited theorem, vm_compute use is disclosed, and "complete executions only" is disclosed.

This gives two tiers.
- Tier A (minimum citable running example): the single SeqLock layer over an abstract underlay, plus non-vacuity, OOTA, a faithful interface and code, and the paper rewrite.
- Tier B (the author's flagship as printed): Tier A plus the module-level tower, a Counter layer, and the COH/barrier grounding in memory/.
The §6 program logic is outside both tiers by the author's decision. The paper must then say that §6 uses a different example.

## Verdict (synthesis, before the SL-nonvac results)

Short answer: the kernel side of a single-layer running example mostly exists. The largest gap is the paper itself: it describes a different SeqLock from the one Coq verifies.

What the kernel has checked (Rocq 9.3.0; all closed under the global context):
- examples.Relaxed.SeqLockModule.SeqLockModule.seqlock_module_rel_lin is a module-level relaxed-linearizability theorem for SeqLock ⊎ COH[z]. It is obtained through the general theorem WindowLinkTable.window_link_table.
- The module-level client theorems hold: SeqLockClients.seqlock_client_equal_pairs, seqlock_client_mp_forbidden, and others.
- The TicketLock (ticketlock_S1_all) and the vertical tower (SeqLockTower.tower_composition_rt_plain) are checked at witness level only.

What the statements say:
- Only complete executions are covered.
- The underlay is an abstract atomic TicketLock plus registers plus no-op barriers, and is assumed rel_lin for each execution.
- The only module-level non-vacuity witness is one write by one thread over a trivial underlay LTS.
- The Counter is never implemented.
- memory/ is not connected: it has no COH instance, no barriers and no RMW.
- No OOTA result exists at any level, even though OOTA rejection is the abstract's headline claim.

What the paper prints: a TSO SeqLock without barriers, with I=∅ and rd↦rfence/wrt↦lfence, verified by an RLHL/VLHL outline. Coq refutes those modes for its COH variant (witness level), and the paper's own SeqLock exists only as an SC CSL-Lin port with no rel_lin statement. The selective barriers and the category table the Coq example depends on do not appear anywhere in the paper.

How far, in two tiers:
- **Tier A (minimum citable example, single layer).** About 5-9 Writer iterations plus a substantial paper rewrite:
  - author decisions D3, D6 and Q4;
  - code faithfulness (S or M);
  - SL-nonvac (M);
  - OOTA evidence (M);
  - the table-based signature lifted into models/ (M);
  - a paper rewrite of §2.4, §3, Def. 2.1, §5 and Appendix/SeqLock, a scope paragraph, and a mechanization table.
- **Tier B (the author's flagship tower on oMCA memory).** Add two multi-file tasks, SL-tower (L) and SL-mem (L, research-heavy), and a Counter layer (M).

General vertical composition, incomplete traces, RMW in memory/, the Imp compiler with hypothesis (W), and RLHL are XL or research. The paper should state them as limitations, not claim them for the running example.

## Gap matrix

Status is the synthesis status. → marks a verifier correction, listed under the table. `block` means the row blocks use as the running example.

| id | obligation | status | effort | block | covered by | gap |
|---|---|---|---|---|---|---|
| RE-01 | The SeqLock printed in the paper (code, cells, barriers, interface) is the SeqLock the Coq development verifies. | differs | research | yes | new (paper rewrite; decisions D6, D3) | P: TSO cells, no barriers, I=∅, rd↦rfence, wrt↦lfence. S (Coq): COH x,y plus a Barrier object, write↦Wmb, read↦Rmb, plus a client cell z. K refutes the printed modes only for the COH barrier variant, on the LB execution X_lb, which TSO forbids. Nothing proves or refutes the printed modes for the paper's TSO SeqLock at the rel_lin level. So the paper's figure, the §2.4 text, the §3 signature and the TR appendix describe an object the relaxed-linearizability development does not verify. The fix is a paper rewrite after decisions D6 and D3; this row needs no Coq work. |
| RE-02 | The example's exported interface (I, fence modes or categories) and the tensor that derives cross-object I are the paper's definitions (Def. relaxed-effect, Def. tensor-sig), so a reviewer can match the definitions. | differs → overclaim: differs; underclaim: differs | M | yes | new | K: under the four-mode lattice, a plain RMW or R call can export only Local, and wmb is not rectangular. So the example cannot be stated with the paper's Def. relaxed-effect. S: in the example's RelaxedSig records, mode := Local is a placeholder, so well_formed holds vacuously. I is defined by hand as 'same object or dto'. The table and the categories live only in examples/. models/ has no generic signature with categories whose tensor derives I. WindowLinkTable reaches the table only through the hypotheses E_compat and F_cross. P: no .tex file mentions rmb, wmb or categories. Needed after decision D3: a models/ file defining category signatures and the table-induced tensor I, with SeqLockProg.E/F and the TicketLock and tower signatures as instances, and the four-mode RelaxedSig as the rect instance. |
| RE-03 | The sequential specification of every layer (ν_SeqLock, ν_TicketLock, ν_Counter, ν_COH cells, Barrier) is stated in the paper and coincides with Coq. | done → overclaim: partial; paper-fidelity: partial | S | yes | new | These are spec-level (S) and complete on the Coq side, but the paper never defines ν_SeqLock, ν_TicketLock or ν_Counter in the main text. The TR TestTick rule is ambiguous, and the TicketLock modes are never stated (Coq uses the plainTL categories). In nuEc, the TicketLock ⊗ x ⊗ y ⊗ Barrier component is one joint replay, not a tensor of separately stated specs. A projection lemma (nuEc component = ν_TL ⊗ ν_x ⊗ ν_y ⊗ ν_B per Def. spec-tensor) would make the paper's definition literal (S). The Counter spec exists only as abstract steps inside TicketLockCOH. |
| RE-04 | The verified futures program is the compilation ⟦-⟧ of the code printed in the paper. | differs → paper-fidelity: differs | M | yes | new | P: ⟦x←e(v)⟧ inserts a wait only before a use. acq's result is never used, and `now` is used only by test_ticket, so the paper's compiler inserts neither early wait. S: Coq verifies a more synchronized futures program. Two fixes: (a) print the futures program verbatim in the paper (paper edit, S); or (b) remove the two waits and re-prove M_shape and positional, relying on dto to order acq→wmb and get_ticket→rmb (M). Decide before SL-nonvac and SL-tower build executions on the program. |
| RE-05 | SeqLock ⊎ COH[z] is relaxedly linearizable to ν_SeqLock ⊗ ν_COH[z] for every relaxed implementation of its underlay (the judgement ⊨ M : ν_E → ν_F). | partial → underclaim: partial | S | no | new | K/S: the theorem is at module level, but: (i) it covers complete executions only; (ii) the underlay hypothesis is per execution and refers to abstract specs (an atomic TicketLock-with-version, register cells, no-op barriers); (iii) it is uniform in VE. P: the paper's judgement 'for every relaxed implementation of ν_E' is not stated. A corollary is missing whose hypothesis is ViewLHL.implements (ViewLHL.v:108), or 'every complete trace of VE is rel_lin'. It needs a lemma that the underlay projection of a module execution is a VE trace. The paper must quote this statement, not 'verifies the SeqLock example'. |
| RE-06 | A concrete concurrent module execution of SeqLock ⊎ COH[z] meets every hypothesis of seqlock_module_rel_lin and exhibits object-level load buffering: zr()=1; write(1,1) ‖ read()=(1,1); zw(1), with each thread's second call invoked before its first returns. The execution is not rel_lin under the empty semi-independence (classical linearizability fails). | done (orchestrator-verified: `SeqLockLB.seqlock_lb_nonvacuous`, closed, in `_CoqProject`, uncommitted; SL-nonvac review pending) | M | yes | SL-nonvac | K: no module execution with a read, with two threads, or with same-thread overlap is known to meet the hypotheses. The module theorem is therefore shown non-vacuous only for a trivial execution. Needed: T_lb, a module_execution_tagged of M rc plainTL; its underlay witness (adapt lb_wit); seqlock_lb_module; and seqlock_lb_not_classical (not rel_lin under fun _ _ => False). Risk: whether the untagged frontier lets write's first call be issued before zr's response. |
| RE-07 | The module-level client theorems apply to at least one execution with a concurrent writer and reader, and to an MP-shaped execution with overlapping same-thread calls. | done for (a),(b),(f) (orchestrator-verified: `lb_client_*`, `seqlock_mp_nonvacuous`, `mp_overlay_projection`); open: ≥2 concurrent writers, a retrying read at module level | M | yes | SL-nonvac | This is the extended acceptance of SL-nonvac (concern-matrix.md:165, items a-c and f). Instantiate equal_pairs (with diagonal writes), same_epoch and read_not_future_po on T_lb. Build T_mp with zr()=1 and apply mp_zr_value. Optionally, lift mp_trace 1 to the overlay projection of T_mp. |
| RE-08 | Client properties are derived from the interface alone and transferred to the implementation: every successful read returns one epoch's pair (a=b for diagonal writers), and MP through the object is forbidden. | partial | S | no | SL-client | S: the clients are trace predicates over T, with exactly the hypotheses of seqlock_module_rel_lin plus shape conditions. There is no client program, no logic and no refinement theorem (file header). The epoch is identified by value, and there is no freshness or regularity rule. P: overview.tex:282 claims transfer by observational refinement. R: B4 (:531) asks for a contextual-refinement result. The rows above and below carry what remains: non-vacuity (RE-07) and the refinement form (RE-17). latest-review iteration 3 marks this 🟡 done. |
| RE-09 | The OOTA variant is forbidden, both at memory level (LB+ctrl on COH cells) and through the object: r←zr(); if r=1 then write(1,1) ‖ (a,b)←read(); if a=1 then zw(1) cannot end with r=1 and a=1. | missing → underclaim: missing | M | yes | new | K: there is no OOTA result at any level, although the abstract's headline claim depends on it. Cheapest route: (a) at trace level on COH cells, the LB trace with a resp(rd)→inv(wrt) edge in each thread is not rel_lin under I_COH (S); (b) at interface level on SeqLock ⊎ COH[z], the overlay trace with write invoked after zr responds and zw invoked after read responds is not rel_lin under findep, by rhb clause (i) (S, in the style of Part 5); (c) at module level, a client module with FutureD control tags over F, via module_dependency_soundness (M). The general claim rests on hypothesis (W) (RE-33). |
| RE-10 | The exported categories are necessary. A stronger interface (rel/acq or rfence/lfence) is refuted by an execution the implementation has. A weaker one (TicketLock exporting Local) admits a torn read. | partial → underclaim: partial (stronger direction done at module level, uncommitted) | S | no | SL-nonvac | S: all of this is at witness or interface level. The module-level version depends on RE-06 (optional item 4 of SL-nonvac). The header SeqLockClients.v:175-179 overstates: it says the printed signature of the paper's TSO SeqLock is refuted, but the refutation concerns the COH barrier variant on X_lb. |
| RE-11 | Every pair the interface declares semi-independent is actually exhibited by the implementation (no extra behaviours, as B6 asks), or the loss of precision is reported. | partial | M | no | new | SB through the object (write(1,1); zr()=0 ‖ zw(1); read()=(0,0)) is not shown to be an implementation execution at any level. Witness level is S; module level is M, after SL-nonvac. |
| RE-12 | Separately verified objects compose horizontally through their interfaces, accounting for cross-object same-thread order (SeqLock ⊎ COH[z]; ticketLock ⊗ x ⊗ y ⊗ Barrier). | differs → overclaim: differs; paper-fidelity: differs | S | yes | new | S: Coq replaces compatibility by window inheritance (out_le/in_le dominance at the window ends), and its theorem has a different shape: one module whose operations are partitioned into components; a per-component premise `positional` at underlay-witness level; complete executions only. There is no M1 ⊎ M2 operator, no ⟦M1⊎M2⟧ = ⟦M1⟧⊗⟦M2⟧, and no ⊨ M_i premise. P: the paper still prints the refuted Def. 5.8 and the judgement-level prop:locality. No Coq work is needed for the example; a judgement-form restatement is optional (S). Paper §5 must be rewritten around window_link_table (C4). |
| RE-13 | The fully linked tower (Counter → TicketLock → SeqLock over low-level cells) is relaxedly linearizable to ν_SeqLock ⊗ ν_COH[z] at module level. | partial | L | yes | SL-tower | K: there is no module-level tower. SL-tower part 1 needs: an inlined futures module M0 over Counter[own] ⊗ COH[nxt] ⊗ COH[x] ⊗ COH[y] ⊗ Barrier ⊗ COH[z]; a shape lemma mapping its traces to SeqLockTower blocks; and seqlock_tower_module_rel_lin via window_link_table, with positional from tower_link. It must handle the acq spin loop, the silent test_ticket, and response A21's requirement that inlined calls still complete at the old method boundaries. S: the result concerns one inlined module, not a vertical-composition theorem (RE-17). The Counter stays abstract unless RE-15 is done. |
| RE-14 | TicketLock is verified against its own specification over Counter ⊗ COH[nxt] ('component by component'). | partial → underclaim: partial | L | no | SL-tower | K: witness level only, with no module-level TicketLock program. The silent test_ticket has no window. The bracketed discipline belongs in the TicketLock contract; the header at :28-30 says the clients 'alternate', but the actual hypothesis is weaker. Not needed if the paper presents the tower as the inlined link (RE-13) and cites ticketlock_S1 as a proof step. |
| RE-15 | The Counter is implemented over a COH cell with faa (inc = faa(own,1), get = rd(own)) and verified against ν_Counter, so that the tower's bottom layer exists. | missing → underclaim: missing (relaxed); SC version exists | M | yes | new (extends SL-tower) | S: the Counter is a primitive object in all three files. Needed: ν_Counter (an inc/get register); a COH register spec with faa; a Counter module with one call per operation (trivial windows), at witness and module level; and its substitution into the tower, so that the remaining hypothesis is on cells only. faa itself is not grounded in memory/ (RE-22). P: the paper has four mutually inconsistent Counter codes and two arities (inc(loc) vs owner.inc()); it should adopt the Coq version. |
| RE-16 | One TicketLock proof works unchanged over Counter^TSO and Counter^RC (proof reuse independent of the counter's memory model). | partial → underclaim: partial | research | no | new | K: reuse is shown only as parametricity of the tower proof in the Counter's categories C, under K_ok (tl_cats C). Neither counter implementation exists, and TSO/RC cells with faa are not in memory/ (Mem.tex:23 excludes RMW). The paper should restate the claim as parametricity in the exported categories, or drop the two-underlay claim. |
| RE-17 | Vertical composition as a general principle: the ⊨ judgement, layering M;N, weakening, observational refinement, ⟦M;N⟧ = ⟦M⟧;⟦N⟧, and copycat. | missing → underclaim: missing (relaxed); classical analogue mechanized | XL | no | new | S: one layer's conclusion (rel_lin of complete overlay traces) is not the next layer's hypothesis (implements: every prefix satisfies rl_prefix, ViewLHL.v:108). So layers do not chain, even with module-level per-layer theorems. Closing this needs incomplete traces (RE-18) and a composition-with-hiding operator. Otherwise the paper must present the tower as an inlined end-to-end link and mark the vertical calculus and observational refinement as unmechanized. |
| RE-18 | Relaxed linearizability of incomplete traces (the append/drop convention), at module level. | missing → underclaim: partial (trace-level definitions); missing (module level) | XL | no | new | Disclose as a limitation of the example (open question Q3). It is a prerequisite for RE-17 and for an implements-style memory link (RE-21). |
| RE-19 | The example's COH cells are an instance of the oMCA memory of memory/, and that instance agrees with declarative coherence (COH trace model = declarative model; COH[Locs] = ⊗ COH[loc]). | missing → underclaim: partial | L | yes | SL-mem | K: there is no COH mode assignment, no tensor lemma, and no theorem behind the main-text COH claim (trace.tex:217-223 is only a sketch). SL-mem items 1-2: define COH as a new all-rlx instance; relate COH[x]⊗COH[y]⊗COH[z], with its dto-induced I, to memory/'s COH on {x,y,z} via Tensor.v; combine this with declarative_characterization; check whether store forwarding breaks the correspondence; state the direction. |
| RE-20 | The selective barriers wmb/rmb have a memory-level meaning (wmb orders W→W, rmb orders R→R) that agrees with the table entries the proof uses. | missing → overclaim: missing | L | yes | SL-mem | SL-mem item 3: extend memory/, with new definitions only, so that the correspondence covers X ⊗ Y ⊗ Barrier ⊗ Z. The declarative side may stay a documented gap. The paper also needs dto on {R, W, Rmb, Wmb, RMW} identified with a named model's ppo, for example LKMM smp_rmb/smp_wmb or ARMv8 dmb ld/st. |
| RE-21 | The actual memory semantics discharges the module theorem's underlay hypothesis: VE is a buffered-memory LTS over RelaxedLTSSpec whose complete traces are rel_lin w.r.t. the cell part of nuEc (Cor. mem:cor:rlxlin). | missing → underclaim: partial (LTS over blocks exists; erasure and corollary missing) | L | no | new | SL-mem proves a history-level direction: if an execution's underlay history is OMCA-consistent COH, then the overlay is rel_lin. That suffices for an honest end-to-end statement. This row is the LTS-level link that would let a memory VE be plugged in directly. The implements form also needs incomplete traces (RE-18). Disclose it if it is not done. |
| RE-22 | faa (nxt.faa(2), inc = faa) is an operation of the oMCA memory model. | missing | XL | no | new | Adding RMW to the buffered cell and its declarative characterization is new metatheory (atomicity of RMW versus buffering), and it is outside SL-mem's scope. Disclose that the tower's Counter[own] and COH[nxt] remain abstract specs. |
| RE-23 | The example states its model class (oMCA) and why COH ⊗ Barrier lies inside it. IRIW+rmb has no witness. The inference 'COH is not MCA' is removed. | missing | S | yes | new | Coq: a witness-level lemma that IRIW with rmb between the reads has no witness over COH[x] ⊗ COH[y] ⊗ Barrier (S). Paper: a scope paragraph naming oMCA, deletion of the trace.tex:225 claim, and an explanation of the change from the MCA promise at :437 (research-intent §8). |
| RE-24 | No part of the running example rests on the identification 'TSO = RA (pure reordering)'. | paper-only | S | yes | new | Paper only: retract rem:ra-tso and remove the TSO labels from the example (D6/C1). If a TSO variant stays (for example Counter^TSO), it must be the buffered TSO of memory/, which has no RMW. |
| RE-25 | The reviewer's SB-with-own-reads outcome is placed in the cell model the example uses. | missing → overclaim: missing; underclaim: missing | S | no | new | A witness-level lemma over COH (S) answers reviewer A for the running example's model. The TSO version needs forwarding reads in memory/. |
| RE-26 | The example's tensors (SeqLock ⊎ COH[z], and the six-way tower underlay) follow one handle convention in both the paper and Coq. | differs | S | no | new | Either align the paper with Coq's shared (thread, handle) namespace, which is close to reviewer A's suggestion of a global handle set, or justify the disjoint sum promised in the response. A paper edit is enough. |
| RE-27 | The paper's relaxed happens-before is the one Coq uses. The MP argument uses both clauses. | done → overclaim: done (Coq); paper formal clauses already match; paper-fidelity: done (Coq and formal statement agree) | S | yes | new | Paper only: rewrite Def. 2.1 to match Coq and the response. The example's client arguments (mp_rhb, read_not_future) use both clauses, so the printed definition must be correct. |
| RE-28 | Relaxed linearizability is formalized as in the paper (complete traces), and agrees with classical linearizability for I=∅ and with the rewrite presentation. The paper uses this agreement to read the SeqLock component as SC. | partial | M | no | new | In Coq, ν is a predicate on lists of operations rather than a set of alternating traces; the two are equivalent for atomic specs, but this is not proved. The claim 'SeqLock exposes only SC behaviour' (overview.tex:274) should cite a sanity-check theorem, which is missing. Not blocking, because the example uses rel_lin as defined. |
| RE-29 | The example is verified in the paper's module semantics: Inv/Step/Ret, a tag-based frontier, and a return only after every underlay call has completed. | done | S | no | new | S: three differences for the paper to describe: one global queue; a semantics closed over an underlay LTS VE (the open denotation only via VE := Step True); and no trace-set object ⟦M⟧_E. The paper should also state the Arm-8 limitation of discharging dependencies at return (A21). |
| RE-30 | The running example exercises dependency tags (data, address, control), so that §4's Step rule and the LB-versus-OOTA distinction are illustrated on it. | partial → overclaim: missing (for the running example); underclaim: partial | M | no | LS-spec | The SeqLock example never uses a dependency tag. The planned carrier for tags is LatchSet (address dependency), or a client-as-module for OOTA (RE-09c). This blocks only if the paper threads §4 through SeqLock. |
| RE-31 | The source language Imp and its compilation ⟦-⟧ to futures are mechanized, with tags computed from the program text. | missing | XL | no | new | E8-lite (a per-example lemma 'tag = policy(program)', M) or E8-full (deep embedding plus compiler, XL). Not blocking if the paper prints the example's futures program (RE-04). |
| RE-32 | LB on COH cells: the relaxed trace is rel_lin under I_COH and not under I_SC = ∅ (classical linearizability fails), and LB is allowed declaratively. | partial → underclaim: partial (object level done, uncommitted; COH-cell trace level missing) | S | no | new | Missing: a proof that the paper's exact trace (trace.tex:191-196, intro.tex:90) is not rel_lin with I=∅, and a proof that it is rel_lin under I_COH; the ViewLiftOMCA trace is a different interleaving. Both are S. The litmus verdicts were hand-checked, and herd7 was not run (Mem.tex:605-608; plan item E6). If SeqLock ⊎ COH[z] becomes the running example, object-level LB (RE-06) subsumes the intro's LB. |
| RE-33 | General dependency preservation (W): dep;po? ⊆ rhb_s for the traces of compiled programs. General OOTA rejection rests on it. | missing | XL | no | new | Requires the compiler and tag computation (RE-31). State it as a hypothesis or limitation. |
| RE-34 | The running example is verified with the paper's program logic (RLHL/VLHL), as Appendix/SeqLock.tex and intro.tex:113 describe. | differs | research | no | RLHL-1, RLHL-2, RLHL-3 | By the author's decision (research-intent §8) this is off the critical path. It stops blocking only if the paper says §6 uses a different example and Appendix/SeqLock.tex is replaced by the window-route outline (RE-35). If the paper claims RLHL as mechanized, RLHL-1..3 must be completed (research, Q1). RLHL-3's optional item re-proves one SeqLock operation. |
| RE-35 | The paper's proof outline of the example is the proof Coq checks. | paper-only | S | yes | new | Paper only: replace the VLHL/RLHL outline of the TSO SeqLock with the window-route outline: windows; the TicketLock invariant giving the linearization point; positional; window_link_table. Cite a Coq name at each step. This also fixes the internal inconsistency between :3 and :47. |
| RE-36 | A paper-to-Coq map with Print Assumptions per cited theorem, and a status row for the example. | partial → overclaim: partial | S | yes | new | The table is not written. The status row must disclose: complete executions only; an abstract underlay assumed rel_lin; a witness-level tower; clients as trace predicates; non-vacuity limited to one write. The pinned Rocq 9.2.0 was not rechecked, and no rocqchk was run. SeqLockClients.v is uncommitted. intro.tex:113 says SeqLock is verified, while implex.tex:187 lists only the exchanger and the EB stack. |
| RE-37 | A specification-effort report for the running object: lines of proof, and what is reused versus new. | missing | S | no | new | Count the lines and classify them per file (S). |
| RE-38 | The object's interface does not depend on the memory model below it (C1), and both counter variants yield the same overlay contract. | partial → underclaim: partial (content in files; the explicit equality lemma is unstated) | S | no | new | State the independence lemma in a file (S). The two-counter part depends on RE-15 and RE-16. |
| RE-39 | The file headers of the cited Coq files are accurate (CLAUDE.md rule). | partial → paper-fidelity: partial | S | no | new | Header edits only (S). Fix them before the paper cites these files. |
| RE-40 | Second flagship, LatchSet with write snapshot: COH, address dependency, the precision table, and the proof 'SC core + F0-F5'. | missing | research | no | LS-spec, LS-proof | The author must define 'write snapshot'. Then LS-spec: a specification, a FutureD program and categories (L). Then LS-proof: a witness-level S1, counterexamples, the module link, and one client (L). It is not on the SeqLock running-example path, but it is the only planned carrier of address dependencies. |
| RE-41 | The EDAG view of the example (code-to-graph semantics, and EDAG/trace agreement) is consistent with the trace semantics. | paper-only | L | no | new | The paper should keep it informal and label it as such, or move it to the TR. Not needed for the SeqLock example. |

## Verifier corrections (non-confirmed verdicts)

- **RE-02** (overclaim: overclaim → differs): The claim that 'wmb is not rectangular' is in Coq only for the toy table bar_to. Add `~ rectangular (dtable rc)` for the dto actually used (S; the same proof) before citing it as forcing D3. Disclose that four_modes_force_local uses vm_compute. Effort M for the models/ file is plausible.
- **RE-02** (underclaim: underclaim → differs): Paper-level mismatch as stated. The Coq work is mostly relocation and packaging: a record (sig, cat : op → Cat) with I := different-component ∧ ¬to. Then E_compat and F_cross become lemmas, not hypotheses, and window_link_rect becomes the rect instance. SeqLockProg.E/F are instances via findep_sl_cf. Effort S–M, not M. Blocking only through D3.
- **RE-03** (overclaim: overclaim → partial): Coq has ν_SeqLock, the lock-with-version TicketLock spec (tl_step ≡ SeqLockCOH.pre/post on TL calls, spec_match) and a z register. ν_Counter and standalone ν_COH[x], ν_COH[y] and ν_Barrier are missing; they exist only inside joint replays. No spec is printed in the paper. Needed: standalone specs plus the projection lemma nuEc CSL = ν_TL ⊗ ν_x ⊗ ν_y ⊗ ν_B per Def. spec-tensor (S), and the paper text (S).
- **RE-03** (paper-fidelity: overclaim → partial): Coq has ν_SeqLock, ν_z and an abstract SC TicketLock spec (tl_step), with a holder precondition and a client discipline bracketed. There is no standalone ν_Counter or ν_Barrier. The TicketLock spec is duplicated, and spec_match links the copies.
The paper's TR TicketLock spec differs: (nxt,own) state, no holder check, view-based. Needed:
- a standalone ν_Counter and ν_Barrier (S);
- the projection lemma nuEc CSL = ν_TL ⊗ ν_x ⊗ ν_y ⊗ ν_B (S);
- a paper rewrite printing tl_step, its holder precondition and bracketed.
- **RE-04** (paper-fidelity: underclaim → differs): Coq's program is more synchronized than ⟦paper code + barriers⟧ in three places:
- a wait after acq;
- a wait after get_ticket, instead of just before test_ticket;
- the waits on f1, fx, fy and f2 of a failed iteration before the retry.
It also uses positional tags instead of computed tags.
Option (b) as stated (remove two waits) does not make M = ⟦code⟧. Making M literally ⟦code⟧ would need: FutureD with the paper's computed tags; no early waits; no end-of-iteration waits; and a decision on the TicketLock's ctrlops (M, before SL-nonvac builds more executions).
The cheap fix is (a): print the futures program verbatim and state that it is more synchronized than the compiled code. Then the theorem covers the printed program, not ⟦code⟧.
- **RE-05** (underclaim: underclaim → partial): Module-level, complete-only, per-execution underlay hypothesis, as stated. The corollary needs (a) the selector bridge (S) and (b) the rl_prefix→rel_lin step from existing PrefixView/ViewLHL lemmas (S); exec_underlay_path is already there. A stronger alternative: instantiate with U := ViewLHL.VT (nuE_all … nuEc). vt_sound (:230) makes every complete VT path rel_lin, which gives a closed statement with no per-execution hypothesis over a canonical relaxed underlay. Proving the same for SeqLockLB.VEa is not automatic, because W_mp is not VEa's response order (SeqLockLB header :111-114).
- **RE-06** (overclaim: wrong → done-pending-review (uncommitted)): SL-nonvac core is implemented in the uncommitted, unregistered SeqLockLB.v. It is a two-thread complete module execution T_lb over VEa with same-thread overlap in both threads, a read returning (1,1), underlay rel_lin by an explicit witness, overlay rel_lin under findep, and not rel_lin under the empty relation. Remaining work (S): add the file to _CoqProject, commit it, run a reviewer iteration on the moving file, and recheck on Rocq 9.2.0. Caveats to disclose: no underlay-level writer/reader interleaving, no retry, complete-only, and an SC-at-response abstract underlay rather than memory/.
- **RE-06** (underclaim: underclaim → done (uncommitted, untracked file; not in _CoqProject)): K: seqlock_lb_nonvacuous, seqlock_lb_module and seqlock_lb_not_classical are closed and free of vm_compute. S: two concrete complete executions over VEa. VEa is SC at response points: the weak behaviour comes from emission order plus semi-independence, not from memory (header :128-134). There is no general 'module admits LB' theorem. Remaining: integration (new row NR-integrate), and rebuilding these if RE-04(b) changes the program.
- **RE-06** (paper-fidelity: wrong → partial (in progress, uncommitted)): Hypotheses (i)-(iii) of seqlock_module_rel_lin are now met by a concurrent module execution T_lb with same-thread overlap over a spec-checking underlay VEa (SeqLockLB.lb_execution, closed; file uncommitted and outside the build).
Still missing:
- hypothesis (iv): rel_lin of the underlay part of T_lb under sindep w.r.t. nuE_all … nuEc, by adapting lb_wit;
- the instance seqlock_lb_module;
- seqlock_lb_not_classical (not rel_lin under fun _ _ => False);
- adding the file to _CoqProject, writing its header, and committing it.
- **RE-07** (overclaim: underclaim → partial (uncommitted)): Items (a), (b) and (f) of the extended SL-nonvac acceptance are built in uncommitted SeqLockLB.v. Missing: an execution with ≥2 concurrent writers, which is what B4 claims, and a module-level retrying read (see new row). Both are S-M with the existing scaffolding.
- **RE-07** (underclaim: underclaim → done (uncommitted), except optional item (c)): The acceptance items a, b and f of SL-nonvac are kernel-checked in SeqLockLB.v. The open items: (c), a same-thread read-then-write overlap; a general bridge transferring rel_lin between the overlay part of a module trace and its projection (only equality with mp_trace 1 is shown, header :143-145; see new row NR-bridge); and integration.
- **RE-07** (paper-fidelity: wrong → missing (execution exists; client instances blocked on hypothesis (iv))): A module execution with a read and a concurrent writer exists (T_lb). The remaining steps:
- discharge underlay rel_lin for T_lb;
- instantiate seqlock_client_same_epoch, equal_pairs (diagonal write (1,1)) and read_not_future_po on T_lb;
- build T_mp for mp_zr_value.
- **RE-09** (underclaim: underclaim → missing): No OOTA result exists. (a') Memory level, general, under (W): D2 forbids every dep∪rfe cycle. This is S, from existing Consequences/ARM lemmas, and it subsumes an LB+ctrl litmus. (b) Interface level through SeqLock ⊎ COH[z]: S, from the existing client rules. (c) Module level with FutureD control tags: M. All are conditional on (W) (RE-33). This remains blocking for the abstract's claim.
- **RE-10** (underclaim: underclaim → partial (stronger direction done at module level, uncommitted)): 'A stronger interface is refuted by an implementation execution' is now module-level (SeqLockLB). 'A weaker TicketLock interface admits a torn read' remains witness-level and vm_compute-dependent. Its module-level version needs M rc K with a Local-exporting K, which fails K_ok, so the module theorem does not apply. The header overstatement at SeqLockClients.v:175-179 is unchanged.
- **RE-12** (overclaim: overclaim → differs): Confirmed as 'differs', but 'separately verified objects compose horizontally' is not demonstrated. The premise is about the joint module's executions, and the SeqLock proof is carried out in the presence of z. The §5 rewrite must explain instrumented executions and the positional premise, so its effort is M (paper), not S. A judgement-form restatement with per-component premises over component-only executions would be new Coq (M-L).
- **RE-12** (paper-fidelity: underclaim → differs): The paper's Def. 5.8 fails on its own running example, so §5 must be rewritten around window_link_table. Its hypotheses are E_compat, F_cross, nuF_nil, window_bodies (dominance) and positional, on complete executions (WindowLinkTable.v:97-186). Add a Coq lemma seqlock_z_not_compatible (S), the Def. 5.8 instance on SeqLockProg.E/F, so that the paper can motivate the change with the example rather than with an abstract lemma.
- **RE-14** (underclaim: underclaim → partial): Relaxed TicketLock: witness-level only, as stated. An SC module-level TicketLock tower exists (Locks/TicketLock.v, TicketDispenser.v). It does not discharge the relaxed obligation, but it is a reusable SC core for the C5 effort report (RE-37).
- **RE-15** (underclaim: wrong → missing (relaxed); SC version exists): No relaxed Counter over COH[own] with faa. The Counter module itself, over an abstract faa register, is S by the z-component pattern. Substituting it into the tower is M and depends on RE-13. faa remains ungrounded in memory/ (RE-22). The SC FAI counter (FAISet) can be cited as the SC analogue.
- **RE-16** (underclaim: underclaim → partial): Restate the claim as parametricity in the exported categories. Witness level: the tower over Counter categories C (tower_composition_plain/_rc). Module level: the SeqLock layer over TicketLock categories K (seqlock_module_rel_lin_K, clients *_K). Neither concrete TSO/RC counter exists.
- **RE-17** (underclaim: underclaim → missing (relaxed); classical analogue mechanized): No relaxed vertical theorem. The templates are CompLin_vcomp/implVComp (classical inlining plus vertical composition) and ViewLHL.presentation_choice (relaxed hypothesis shape). Still XL for the relaxed calculus. The paper must present the tower as the inlined link.
- **RE-18** (underclaim: underclaim → partial (trace-level definitions); missing (module level)): Definitions and the complete↔prefix bridge exist. A module-level theorem with an rl_prefix/implements conclusion is missing. It is hard because extending an incomplete execution needs progress for the acq spin and the read loop. Disclose as a limitation. Effort: L, or XL with progress.
- **RE-19** (underclaim: underclaim → partial): COH is the rlx fragment of RC_cfg. A dedicated ModeAssign is optional. The tensor and declarative theorems are generic and apply. Remaining: (a) a D1⇒D2 collapse lemma for all-rlx (S); (b) the correspondence to the SeqLock's register spec (shared with RE-21, L). Effort for the first two items: S–M, not L.
- **RE-20** (overclaim: overclaim → missing): Drop LKMM as a candidate. Target ARMv8 (dmb ishld ⊒ Rmb, dmb ishst = Wmb), stating the direction. Effort is research, not L: the barrier correspondence fails with store forwarding unless the cell specs or the scope change.
- **RE-21** (underclaim: overclaim → partial (LTS over blocks exists; erasure and corollary missing)): The memory LTS exists in block form. Missing: erasure to ThreadEvent, and 'complete hidden traces are rel_lin w.r.t. register specs' (Cor. mem:cor:rlxlin). The implements form also needs prefixes (RE-18). L. Disclose it if it is not done.
- **RE-25** (overclaim: overclaim → missing): The COH lemma answers A only for barrier-free COH. For the running example's model (COH ⊗ Barrier with Rmb exports) A's transitivity objection applies and is, by derivation, correct. See the new store-forwarding row.
- **RE-25** (underclaim: underclaim → missing): No lemma yet. Both versions are S: a COH witness at trace level, and a TSO buffered version as a Litmus.v 'ours_allow' test with internal reads. No new forwarding machinery is needed. This answers popl2027-reviews.md:69-71 directly.
- **RE-27** (overclaim: wrong → done (Coq); paper formal clauses already match): No rewrite of the formal definition is needed. Fix the informal sentences at overview.tex:255 so that they say (i) applies to any two operations, including the same thread. Paper edit only, S.
- **RE-27** (paper-fidelity: overclaim → done (Coq and formal statement agree)): Formal Def. 2.1 = Coq rhb. Paper edit (S, not blocking): fix the informal lead-in sentence and add one sentence explaining why clause (i) is not restricted to different threads (response A8).
- **RE-30** (overclaim: overclaim → missing (for the running example)): The SeqLock running example uses no dependency tag. Tags appear only in unrelated examples. Either carry §4 with another example (LatchSet or a client-as-module, RE-09c), or add a tagged variant.
- **RE-30** (underclaim: overclaim → partial): Dependency tags are exercised only by DependencyFrontierExamples (data-then-load) and by module_dependency_soundness. They are never exercised on SeqLock or any end-to-end example.
- **RE-32** (underclaim: underclaim → partial (object level done, uncommitted; COH-cell trace level missing)): The object-level image of the paper's LB trace is kernel-checked: allowed under findep, rejected classically. The 4-operation COH-cell version of trace.tex:191-196 (rel_lin under I_COH, not under ∅) is still S and missing.
- **RE-36** (overclaim: overclaim → partial): Correct the vm_compute disclosure to include four_modes_force_local. Add SeqLockLB.v (uncommitted, unregistered, moving) to the status row. The pinned 9.2.0 recheck and rocqchk are still missing.
- **RE-38** (underclaim: underclaim → partial (content in files; the explicit equality lemma is unstated)): Interface independence from the RCsc/RCpc profile follows from fcat_cross_table and upres_rc, and independence from the TicketLock categories from seqlock_module_rel_lin_K. Only a named lemma 'findep true = findep false' is missing (trivial). The two-counter part still depends on RE-15 and RE-16.
- **RE-39** (paper-fidelity: underclaim → partial): Add these four header fixes to the list (S).

## Rows added by the verifiers

- **NR-01** (overclaim) The running example's interface and underlay hypothesis are sound for an oMCA memory with store forwarding. In particular the object-level SB-with-forwarding outcome T1: zw(1); zr()=1; read()=(0,0) ‖ T2: write(1,1); read()=(1,1); zr()=0 is either produced by no oMCA execution or accepted by the interface. | status: missing (derivation only, not checked in Coq or herd7) | effort: research | By my derivation the outcome is not rel_lin under findep with ν_SeqLock ⊗ ν_z: the witness needs the cycle zw1<zr1<read1<write2<read2<zr2<zw1, because zr;read is ordered (dto DR Rmb) and read;zr is ordered (dto Rmb DR). Its underlay part has no dto witness either, since Wz→Rz (same_obj), then R→Rmb→R. On x86-TSO (rmb a no-op, locked RMWs) and on ARMv8 (rmb = dmb ld, wmb = dmb st, plain RMWs) the hardware execution looks allowed: the forwarded Rz does not order T1's store before T1's Rx, and T2's dmb.st/dmb.ld do not order Wx before Rz. So SL-mem's planned direction 'OMCA-consistent underlay ⇒ overlay rel_lin' would be false for SeqLock ⊎ COH[z] as specified. Needed: (a) a Coq lemma that this overlay trace is not rel_lin under findep (S); (b) a herd7 check on x86 and AArch64 (S); (c) an author decision: restrict the example to a forwarding-free fragment, make rmb drain the store buffer, or switch the cells to buffered specs and redo seqlock_S1 and the categories.
- **NR-02** (overclaim) A module-level execution that exercises the SeqLock protocol. Writer and reader underlay calls interleave, the read retries at least once, and there are at least two concurrent writers (B4: 'even with concurrent writers'). | status: missing at module level (witness level only: SeqLockCOH.X_retry/retry_wf, which uses vm_compute) | effort: S | In the uncommitted T_lb, all 12 underlay events of the write precede the reader's first call. In T_mp the reader also sees a completed write. There is a single writer, the read's Tau/retry branch is never taken, and the TicketLock version check is never exercised in a module execution. Build T_retry, adapting SeqLockCOH.retry_wit, and a two-writer execution with the SeqLockLB scaffolding. Instantiate equal_pairs on the two-writer run.
- **NR-03** (overclaim) The paper's framing of the example's SC behaviour is consistent with its point. The SeqLock is SC within its component (I=∅), but SeqLock ⊎ COH[z] exports a non-empty cross-object I and admits object-level LB. | status: paper-only | effort: S | SeqLockClients.zr_write_independent and read_zw_independent (SeqLockClients.v:638/:644), and the uncommitted seqlock_lb_module/seqlock_lb_not_classical, show that the composite is not SC. The paper must say what is SC: the component's sequential spec, and I restricted to the component. It must also say what is relaxed: the Rmb/Wmb cross-object contract.
- **NR-04** (overclaim) Registration, commit and review of SeqLockLB.v before it is cited as the non-vacuity evidence. | status: partial | effort: S | The file is untracked, absent from _CoqProject, and was being edited during this review (349 lines at 07:57, then 1082 lines at 08:06). It has had no reviewer iteration. Its .vo predates the current .v. Add it to _CoqProject after SeqLockClients.v, rebuild, run Print Assumptions on the 9.2.0 pin, and run a reviewer pass. The author commits.
- **NR-05** (underclaim) Integrate SeqLockLB.v into the artifact: add it to _CoqProject after SeqLockClients.v, regenerate the Makefile, commit it with SeqLockClients.v, and update the stale non-vacuity text in the SeqLockClients header (:130-165) and in concern-matrix M-3 and §5 ('Object-level LB through composition'). | status: The theorems are kernel-checked on 9.3.0 (closed, no vm_compute). The file is untracked, not in _CoqProject, and still being edited. | effort: S | RE-06, RE-07, the module-level part of RE-10, and the object-level part of RE-32 are done only in an untracked file outside the build. They cannot be cited until it is built by make and committed.
- **NR-06** (underclaim) A selector bridge: rel_lin BL.over_sel T ⟺ rel_lin PrefixView.sel (overlay_events T), and the under_sel/underlay_events analogue. | status: missing. RelaxedTraceLin.rel_lin_map (:173) handles relabelling only, not filtering. The SeqLockLB header (:143-145) records the absence. | effort: S | This bridge is needed for three things: the implements-form corollary of seqlock_module_rel_lin (RE-05); connecting window-route results (BL.*_sel) to the GSim/ViewLHL route (gsim_rel_lin and presentation_choice conclude on overlay_events with PrefixView.sel); and lifting SeqLockClients Part 5 (mp_trace_*) along SeqLockLB.mp_overlay_projection, instead of relying only on the projection equality.
- **NR-07** (underclaim) The running-example artifact builds end to end on one declared toolchain. | status: structures/DCPOs.v fails on Rocq 9.3.0 (syntax error; piped check), so a full `make` fails on the author's toolchain. rocq-rbgs.opam and CLAUDE.md pin 9.2.0, on which the current HEAD and the new files have not been rechecked. Nothing in the example's dependency cone requires DCPOs. | effort: S | Either fix DCPOs.v for 9.3 or re-verify everything on 9.2.0, then state the version in the mechanization table (RE-36).
- **NR-08** (paper-fidelity) The cell interface printed in the paper (COH[loc]) is the one the running example uses: reads and writes export kinds R/W, not Local, so that rmb/wmb can order them. The tensor of kinded cells still derives I_COH. | status: differs | effort: S | Under Local, selective barriers order nothing: dto false DLocal Wmb = false and dto false DLocal Rmb = false (checked). So the printed COH cell cannot carry the barrier code. Coq cells export DW/DR (SeqLockCOH.ucat :202), and dto is false on every DR/DW pair (checked), so the derived cross-location I is still I_COH. Paper: restate COH[loc] with kinded categories. Coq (optional, S): a lemma that the table-induced tensor of kinded single-location cells equals I_COH, so that §3's example survives the change. Blocking for the running example: yes (paper).
- **NR-09** (paper-fidelity) The Barrier object is specified in the paper: operations wmb/rmb, no-op sequential spec, categories Wmb/Rmb, and its internal semi-independence. The object hierarchy shows it. | status: differs | effort: S | Coq: uobj OB, same_obj OB OB = false. So Barrier's internal I = {(wmb,rmb),(rmb,wmb)}: upres WmbC RmbC = false and upres RmbC WmbC = false (checked), while wmb–wmb and rmb–rmb are ordered. The sequential spec is the identity (SeqLockCOH.pre/post). The underlay of the example is TicketLock ⊗ COH[x] ⊗ COH[y] ⊗ Barrier (⊗ COH[z]). Paper must add the object, its I and the box in the figure. Coq (optional): name ν_Barrier as a standalone spec.
- **NR-10** (paper-fidelity) The paper's horizontal-composition condition (Def. 5.8) is shown to fail on the running example itself, which motivates window inheritance. | status: missing | effort: S | By the table: (Acq, WrZ) ∈ sindep (upres false plainTL Acq (WrZ 1) = false, checked), but (fWrite, fZw) ∉ findep (dto false Wmb DW = true, checked). So the iff of Def. 5.8 fails for SeqLock ⊎ COH[z]. A small lemma seqlock_z_not_compatible over SeqLockProg.E/F turns this into a kernel fact that §5 can cite next to window_link_table. bracketed_not_compatible is four-mode and abstract.
- **NR-11** (paper-fidelity) The code change is justified: the paper's barrier-free SeqLock code is incorrect on COH (a torn read has a valid witness), which is why the running example adds rmb/wmb. | status: missing | effort: S | By the table, without barriers: GT→RdX is unordered (upres (GT 0) (RdX 0) = false, checked), and Acq→WrX and WrY→Rel are unordered (DRMW against DW). So the reader's data reads can escape the ticket window and the writer's writes can escape the critical section. torn_with_local_tl covers only the barrier code with a Local TicketLock. A witness-level lemma needs a barrier-free variant of calls and a torn execution valid under plainTL with no linearization. It tells a reader why the printed code changed.
- **NR-12** (paper-fidelity) If the paper keeps any TSO SeqLock material, the underlay LTS it prints (App. SeqLock.tex) is the one the Coq proof uses. Otherwise SeqLockTSO is not cited as a check of the paper's SeqLock. | status: differs | effort: research | ViewSpecs.SeqLockUnderlaySpec.StepSeqLockUL (ViewSpecs.v:314-410) differs from the TR rules:
- wrt (:320) needs sl_owner = Some t and global freshness ∀t0. H̄(t0) < h (TR: h > H̄(t));
- acq (:351) and rel (:370) use global freshness; rel advances every thread's view; acq needs even nxt and no owner;
- get_ticket (:387) and test_ticket (:403) use global freshness (TR: h > H(t,lk));
- test_ticket(n) requires the lock's nxt component to equal n (the TR's variable clash read literally).
My derivation, unchecked: with global freshness, nxt(h) is the latest nxt, which is even and grows. So test_ticket never returns true, and a reader whose window an acq overlaps blocks. The retry path of Mseqlock is unreachable. Mseqlock is also in the SC Lang, not the futures language. Resolution: retire the TSO SeqLock (D6), or fix the spec to the TR rules and re-prove (research). Suggested scratch check for the orchestrator: an invariant 'reachable ⇒ even (fst (sl_lock s h)) for all h', plus a lemma that ResEv (test_ticket n) true is never enabled from a reachable state.
- **NR-13** (paper-fidelity) The underlay semi-independence the paper prints for the SeqLock (I_E) is the one Coq uses. | status: differs | effort: S | The TR's I_E:
- contains TicketLock-internal pairs (rel, get_ticket) and (rel, test_ticket);
- has only TSO-shaped cross pairs (wrt l, rd l'), (wrt, get_ticket/test_ticket), (rel, rd l).
Coq's I_E = sindep (SeqLockProg.v:170) = negation of upres (SeqLockCOH.v:212):
- TicketLock I = ∅;
- all cross-cell pairs are independent (COH);
- TicketLock–cell pairs are independent unless a barrier intervenes;
- barrier pairs are decided by the table.
The printed relation must be replaced by the table-induced one, ideally printed as the dto table rather than as an enumeration.
- **NR-14** (paper-fidelity) The paper describes correctly what the running example demonstrates: a sequential SC spec with an exported interface that permits cross-object reordering (object-level LB). It does not claim that the implementation exposes 'only SC behavior'. | status: paper-only | effort: S | The overlay I of SeqLock ⊎ COH[z] is nonempty: findep contains (write,zr), (zr,write), (read,zw) and (zw,read), since dto is false on (Wmb,DR), (DR,Wmb), (Rmb,DW) and (DW,Rmb). X_lb/T_lb shows LB through the object. Only the SeqLock component's internal I is ∅. The vertical-compositionality paragraph must say: the sequential contract is SC, and the exported categories (Wmb/Rmb) state exactly which cross-object reorderings a client may observe.

## Critical path (synthesis)

- 1. Author decisions, before any Coq work: Q4 (the running example is SeqLock ⊎ COH[z] on COH with rmb/wmb; LB/OOTA stays as the memory-level motivating litmus); D3 (categories and the dto table in the main text, which four_modes_force_local and wmb_not_rectangular essentially force); D6 (retire the TSO SeqLock); the code-faithfulness choice of RE-04; whether the Counter layer stays; Q3/D7 (accept complete executions only and the inlined tower as the vertical story).
- 2. RE-04, if Coq rather than the paper changes: remove the early waits after acq and get_ticket in SeqLockProg.write/read_body and re-prove M_shape and positional (M). Do this before any new execution is built.
- 3. SL-nonvac (RE-06, RE-07; optionally RE-10 at module level): T_lb with same-thread overlap; seqlock_lb_module; seqlock_lb_not_classical; client instances on T_lb; the MP execution T_mp with mp_zr_value (M). This is the highest-weight reviewer gap and is cheap.
- 4. OOTA evidence (RE-09): the trace-level LB+ctrl trace on COH is not rel_lin, and the interface-level OOTA-through-SeqLock trace is not rel_lin under findep (S each). Optionally, a client-as-module with FutureD control tags (M).
- 5. Interface faithfulness in models/ (RE-02, M), together with the spec-tensor projection lemma (RE-03, S) and the implements-form corollary of seqlock_module_rel_lin (RE-05, S). These can run in parallel with steps 3-4.
- 6. SL-tower part 1 (RE-13, L): the inlined futures module M0 and seqlock_tower_module_rel_lin via window_link_table, justifying inlining under response A21. Then the Counter layer over an abstract COH register with faa, substituted into the tower (RE-15, M).
- 7. SL-mem (RE-19, RE-20, L): a COH instance of the buffered cell, minimal barriers, and the history-level correspondence with a stated direction, combined with declarative_characterization. Add the IRIW+rmb witness-level lemma (RE-23, S).
- 8. Paper rewrite, in parallel from step 1: §2.4 figure and text (RE-01); the §3 signature, specs and table (RE-02, RE-03); Def. 2.1 (RE-27); §5 window composition replacing Def. 5.8 (RE-12); the window-route outline in Appendix/SeqLock.tex (RE-35); the scope paragraph and the RA/TSO retraction (RE-23, RE-24); the mechanization table (RE-36).
- 9. Housekeeping before citation: header fixes (RE-39), commit SeqLockClients.v and its _CoqProject line, a recheck on the pinned Rocq 9.2.0, and the effort report (RE-37).
- Off the path, to be stated as limitations unless the author funds them: general vertical composition (RE-17, XL), incomplete traces (RE-18, XL), the memory LTS link (RE-21, L), RMW in memory/ (RE-22, XL), the compiler and (W) (RE-31, RE-33, XL), RLHL-1..3 (RE-34), TicketLock at module level (RE-14, L), and LatchSet (RE-40, a separate section).

## Decisions needed (synthesis)

- Q4: what is 'the running example'? Candidates: SeqLock ⊎ COH[z] on COH with rmb/wmb (recommended: it has nearly all the Coq); the current LB/OOTA litmus (intro.tex:74); Lock(O) ⊗ plain cell (todo-oopsla-v2.md:41/:47, no Coq); LatchSet (no Coq). Also decide whether LB/OOTA stays as a memory-level motivating litmus that the running example carries to the object level through X_lb.
- D3: put categories and the dto table (with Rmb/Wmb) in the main text, with the four fence modes as the rect special case. If the running example is the COH SeqLock, this is effectively forced: four_modes_force_local, wmb_not_rectangular and paper_signature_fails show it is not expressible in four modes.
- D6: what happens to the paper's TSO SeqLock with no barriers? Drop it, or keep it as a clearly labelled SC/CSL-Lin port (SeqLockTSO.Mseqlock, which proves no rel_lin statement). Either way the figure, overview.tex:278, trace.tex:395 and Appendix/SeqLock.tex change.
- Code faithfulness: print the futures program with the waits after acq and get_ticket, or remove those waits in SeqLockProg (M) so that the program is ⟦paper code + barriers⟧.
- Counter layer: keep the tower's bottom layer (needs a Counter module over an abstract COH register with faa; faa stays ungrounded in memory/), or start the tower at TicketLock over an abstract Counter spec. Separately: drop the 'one TicketLock proof over Counter^TSO and Counter^RC' claim, or restate it as parametricity in the exported categories (tower_composition_plain/_rc).
- Q3/D7: accept complete executions only and the inlined one-module tower as the vertical story, with Prop. vertical-composition and observational refinement marked unmechanized; or fund incomplete traces plus a general vertical judgement (XL).
- Q1: does the paper claim RLHL/VLHL as mechanized? If not, §6 needs its own example (or none), and the SeqLock proof is presented by the window route.
- Q2 and the scope wording: oMCA (decided 2026-10-13) versus the MCA scope promised in the response (popl2027-reviews.md:437); and what may be claimed about RC11/ARMv8 (incomparability, partial containment).
- Handle convention: Coq's shared (thread, handle) keys or the disjoint sum promised in response A12 (:475).
- OOTA through the object: is an interface-level trace lemma enough, or should the client be modelled as a module with FutureD control tags?
- RMW grounding: accept abstract faa cells at the bottom of the tower as a disclosed limitation, or extend memory/ with RMW (new metatheory).
- LatchSet: define 'write snapshot' so that LS-spec can start; decide whether LatchSet, not SeqLock, carries §4's dependency-tag story.

## Paper edits (synthesis)

- figures/SeqLock.tex:10-25 and overview.tex:278: COH data cells plus wmb/rmb (write = acq; wmb; x.wrt; y.wrt; wmb; rel; read = get_ticket; rmb; x.rd; y.rd; rmb; test_ticket) instead of 'two TSO data cells' with no barriers. Replace M_Counter^TSO and M_Counter^RC (figures/SeqLock.tex:29-68) by the Coq Counter over COH[own] (inc = faa, get = rd), and unify the arity with the TicketLock code (inc(loc) vs owner.inc()).
- trace.tex:393-396: replace the SeqLock signature (I=∅, rd↦rfence, wrt↦lfence) by write↦Wmb and read↦Rmb, with I derived from the table. Note that Coq refutes the printed modes for this variant (SeqLockCOH.paper_signature_fails, paper_modes_fail; witness level, execution X_lb).
- Main text (overview.tex:299-341, trace.tex:20-22, 352-355, 398-411): introduce the selective barriers and the category table WindowTable.dto, with the four fence modes as the rect special case (abstract_is_rect, wc_is_special_case). No .tex file currently mentions rmb, wmb or categories.
- Print ν_SeqLock (a pair register from (0,0)), ν_TicketLock (with the version/odd-ticket rule; fix the variable clash in Appendix/SeqLock.tex:106-111), ν_Counter and the layer categories (plainTL), matching SeqLockCOH.pre/post and TicketLockCOH.tl_step.
- relaxedlin.tex:126-153 and overview.tex:343-357: replace Def. compatible, Prop. tensor-impl and prop:locality with window inheritance and the module-level theorem window_link_table: one module with partitioned components, a positional premise, complete executions only. Cite bracketed_not_compatible as the refutation of the old definition.
- overview.tex:254-256: rewrite Def. 2.1 (rhb) to match RelaxedTraceLin.rhb and response A8.
- overview.tex:280-296: replace 'the compositionality theorem then combines these proofs' with the inlined end-to-end tower result (SL-tower, at module level once done; witness level today). Mark the vertical calculus and observational refinement as not mechanized. State that client facts transfer through rel_lin witnesses (SeqLockClients.client_rule_*), not through a refinement theorem.
- trace.tex:262-264: retract rem:ra-tso. trace.tex:225: delete 'our COH model is not MCA' (response A18). intro.tex:119: add the oMCA scope paragraph, place COH ⊗ Barrier in it, and explain the change from the MCA promise at popl2027-reviews.md:437.
- Appendix/SeqLock.tex: replace the VLHL/RLHL outline of the TSO SeqLock (two invariants; :3 and :47 contradict each other) with the window-route proof. Its steps: the windows (a write's first wmb; the first rmb of a read's last iteration); the TicketLock invariant giving the linearization point; seqlock_S1; seqlock_z_composition; positional; window_link_table.
- intro.tex:113 and implex.tex:184-199: name the COH SeqLock as the object Rocq verifies, and state the level: module level, abstract underlay assumed rel_lin, complete executions only. Stop presenting SeqLock as RLHL/VLHL-verified, and reconcile the list of mechanized examples.
- If SeqLockProg keeps its waits: print the futures program of the SeqLock methods, or note the explicit waits after acq and get_ticket (SeqLockProg.v:219-235). The paper's ⟦-⟧ would not insert them.
- Client claims (overview.tex:276): state a=b and same-epoch with the caveats in the SeqLockClients header (:38-53): the epoch is identified by value, and there is no freshness guarantee.
- trace.tex:398-408: align the handle namespace with Coq's shared (thread, handle) keys, or justify the disjoint sum.
- impl.tex: describe the module semantics as closed over an underlay LTS VE with a global queue, and state the Arm-8 limitation of discharging dependencies at return.
- Abstract and intro (main.tex:164, intro.tex:14, 110): the OOTA-rejection claim must cite the new Coq evidence (RE-09), or be labelled paper-only. General rejection rests on the unproved hypothesis (W) (Mem.tex:736-758).
- overview.tex:278: drop 'two Counter implementations with an unchanged TicketLock proof', or restate it as 'for any Counter whose exported categories dominate the plain ones (witness level)'. Remove or relabel the three other Counter versions in the TR (gamemodel.tex:92-130, programlogic.tex:317-333, 2Counter.tex).
- Add a mechanization table: paper result, Coq name, level (witness or module), hypotheses, Print Assumptions, vm_compute use, Rocq version. Remove the dangling reference to Cor. mem:cor:rlxlin, or make it point to an actual result.

## Verifier summaries

### overclaim

I checked the matrix with an overclaim lens, read-only, on Rocq 9.3.0, using inline rocq repl replays that wrote nothing. Repository state: HEAD 6e2b575, plus untracked SeqLockClients.v and SeqLockLB.v, and a one-line _CoqProject change.

**What holds up**
- **Main theorem.** SeqLockModule.seqlock_module_rel_lin (:1247) says what the matrix says:
  - it is module level and covers complete executions only;
  - its underlay hypothesis is per execution, over abstract specs;
  - it is closed under the global context, and no vm_compute lemma is on its path;
  - the hypothesis never mentions VE, so VE plays no role.
- **Clients.** The client theorems are closed conditionals with exactly those hypotheses.
- **Tower and TicketLock.** Both are witness-level only (tower_link: ∃ X : SL.Exec, SL.WF …).

**Material errors in the matrix**
1. **RE-06/RE-07 are stale.** SeqLockLB.v exists. It is untracked, not in _CoqProject, and grew from 349 to 1082 lines during this review. Both snapshots replayed without errors, and Print Assumptions is closed for lb_execution, seqlock_lb_nonvacuous and seqlock_mp_nonvacuous. What it contains:
   - T_lb: two threads, same-thread overlap, underlay rel_lin by an explicit witness, overlay rel_lin, and not rel_lin under the empty relation;
   - T_mp, whose overlay projection equals mp_trace 1;
   - client instances;
   - module-trace refutations of the paper's signature.

   What it does not show: writer/reader interleaving at the underlay, a retrying read, or two writers. The underlay VEa is SC at responses.
2. **RE-03 'done' overclaims.** There is no standalone ν_Counter or cell/barrier spec; they live only inside joint replays, and the paper defines none. Status should be partial.
3. **RE-30 overclaims.** SeqLock uses no dependency tags at all.
4. **RE-02.** wmb_not_rectangular is proved for the toy table bar_to, not for dto.
5. **RE-27 is wrong.** The formal clauses of Def. 2.1 already match RelaxedTraceLin.rhb; only the informal prose is off.
6. **RE-36.** vm_compute also appears in the general lemma four_modes_force_local.
7. **RE-12.** The positional premise of window_link_table is about executions of the joint module, and the SeqLock proof includes the z blocks. So 'separately verified objects compose' is not demonstrated. The §5 rewrite is M, not S.
8. **RE-20.** LKMM is inconsistent with the oMCA scope.
9. **RE-25.** Its claim that the COH lemma 'answers reviewer A for the running example's model' holds only without barriers.

**New research-level risk (my derivation; not checked in Coq or herd7)**
- With store forwarding, the object-level outcome zw(1); zr()=1; read()=(0,0) ‖ write(1,1); read()=(1,1); zr()=0 looks allowed on x86-TSO and on ARMv8 (dmb ld/st).
- But dto orders zr before read and read before zr in the same thread (the Rmb clauses), so the interface forbids that outcome.
- So SL-mem's planned direction from oMCA memory to overlay rel_lin would be false for SeqLock ⊎ COH[z] as specified. This is reviewer A's transitivity objection (popl2027-reviews.md:69-81) reappearing at the object level.
- It needs a Coq refutation lemma, a herd7 check and an author decision before Tier B (grounding in memory/) is pursued.

**Other new rows**
- A module-level retry/two-writer execution, which B4's 'even with concurrent writers' requires.
- Paper consistency of 'exposing only SC behavior' (overview.tex:274) with object-level LB.
- Registration and review of SeqLockLB.v.

**Effort estimates**
- RE-06 drops to S of remaining work.
- RE-12 (paper) rises to M.
- RE-20 becomes research.
- RE-05 is S-M; the path lemma already exists as ViewLHL.exec_underlay_path, but completeness, selector and prefix-closure lemmas are still needed.

### underclaim

The gap matrix underclaims the Coq development in several places. The biggest is that its critical-path step 3 (SL-nonvac) is already kernel-checked. The untracked file /Users/index/Documents/GitHub/rbgs/examples/Relaxed/SeqLockLB.v is still being edited and is not in _CoqProject, but its results are checked on Rocq 9.3.0, are closed under the global context, and use no vm_compute:
- seqlock_lb_nonvacuous: a two-thread complete module execution over the spec-checking underlay VEa (not VE0). Each thread overlaps its own calls, zr()=1 and read()=(1,1). The underlay rel_lin hypothesis is proved, the overlay is rel_lin under findep, and it is not rel_lin under the empty relation. Its overlay interleaving is exactly the paper's LB trace at trace.tex:191-196.
- Module-level refutation of the paper's signature and modes on this implementation execution (seqlock_lb_paper_signature/_paper_modes/_refutes).
- The a=b, same-epoch and read-not-future client corollaries on T_lb.
- An MP execution T_mp whose overlay projection equals SeqLockClients.mp_trace rc 1, with mp_zr_value applied.

Rows RE-06, RE-07, RE-10 (stronger direction) and RE-32 (object level) should move to done. They are blocked only on integration (new row) and on the caveats the file's header states: two concrete executions, complete only, and VEa is SC at response points.

Other underclaims:
- RE-05: ViewLHL.exec_underlay_path already exists. What is missing is a selector bridge (new row) and an rl_prefix-to-rel_lin step composable from existing PrefixView/ViewLHL lemmas. Instantiating with U := ViewLHL.VT gives a closed statement with no per-execution hypothesis.
- RE-19: COH is the rlx fragment of RC_cfg (Cell.v RC_shape_*). Tensor.memory_tensor, memory_is_tensor_of_cells and nu_big, and Equivalence.declarative_characterization, are generic in the configuration and I. The tensor lemma exists; effort drops from L to S–M for the first two items.
- RE-25: forwarding reads already exist in memory/, and D2 uses rfe. The TSO version of reviewer A's test is a Litmus.v-style lemma (S).
- RE-09: Consequences.read_pre_Dc, rfe_Dc and ARM.dep_Dc make 'under (W), D2 forbids every dep∪rfe cycle' a short general memory-level OOTA corollary. It is still missing, and still blocking at object level.
- RE-15: an SC counter exists (FAISpec/FAISet), so 'no Counter implementation at any level' is wrong. The relaxed Counter layer is S by the SeqLockModule z-component pattern and WindowTable.single_window_inherits.
- RE-14, RE-17: the SC TicketLock/TicketDispenser tower, and CompLin_vcomp/implVComp (classical vertical composition; eq_rect_eq only, despite a stale 'Admitted' plan doc), are unmentioned templates.
- RE-16, RE-38: seqlock_module_rel_lin_K gives module-level parametricity in the TicketLock categories K. fcat_cross_table and upres_rc already establish that the interface does not depend on rc.
- RE-18: trace-level incomplete-trace notions exist (PrefixView.lin_h, view_rt, ViewLHL.rl_prefix/implements); only the module level is missing.

Overclaims:
- RE-21: the buffered memory LTS exists over blocks; only the erasure to ThreadEvent and the rel_lin corollary are missing.
- RE-30: LockedRegisters does not use FutureD as a program.

Refinement for RE-20, from my reading of Declarative.v (not checked in Coq): rmb can be modelled as extra pre edges under the existing theorem, while wmb needs a contract extension.

New rows: (1) integrate and commit SeqLockLB.v and fix the stale SeqLockClients header; (2) the selector bridge; (3) the toolchain, since structures/DCPOs.v fails on 9.3.0 and 9.2.0 is unchecked.

Net effect: Tier A is about one to two Writer iterations closer than the matrix says. The remaining Tier A Coq work is:
- RE-04 code faithfulness (after RE-04(b), SeqLockLB must be rebuilt);
- OOTA (RE-09, now S at memory and interface level);
- the models/ category signature (RE-02, S–M, since window_link_table is already generic);
- the implements corollary (RE-05);
- the projection lemma (RE-03);
- integration.

The paper rewrite is unchanged.

### paper-fidelity

# Research review: paper fidelity of the SeqLock running example (2026-10-13)

## Scope

- **Repository state.** HEAD 6e2b575, plus:
  - `examples/Relaxed/SeqLockClients.v` (untracked; its `_CoqProject` line is uncommitted);
  - `examples/Relaxed/SeqLockLB.v` (untracked, not in `_CoqProject`, placeholder header "(header written last)").
- **Lens.** Line-by-line comparison of the paper's SeqLock tower with the Coq objects:
  - paper: `figures/SeqLock.tex`, `overview.tex:262-357`, `trace.tex:393-411`, `Appendix/SeqLock.tex`, `impl.tex:29-81`;
  - Coq: `SeqLockCOH`, `TicketLockCOH`, `SeqLockTower`, `SeqLockProg`, `SeqLockModule`, `WindowTable`/`WindowLinkTable`, `View/SeqLockTSO` + `ViewSpecs.SeqLockUnderlaySpec`.

## Checks I ran (Rocq 9.3.0, piped toplevel; nothing written)

- **`Print Assumptions`.**
  - Closed under the global context: `seqlock_module_rel_lin`, `paper_modes_fail`, `tower_composition_rc`, and `SeqLockLB.lb_execution` (new, uncommitted).
  - `SeqLockTSO.Mseqlock` uses `eq_rect_eq` and `classic`.
- **`About seqlock_module_rel_lin`.** Matches the gap matrix:
  - complete executions only;
  - per-execution underlay rel_lin hypothesis over `nuE_all … (nuEc rc plainTL)`;
  - `nuEc CSL` is one joint replay from `SL.init`.
- **Table entries, by `Eval compute`:**
  - `dto false DLocal Wmb = dto false DLocal Rmb = false`: barriers order nothing that exports Local.
  - `dto` on every DR/DW pair is false, so I_COH is unchanged.
  - `upres WmbC RmbC = upres RmbC WmbC = false`: the barrier object's internal I is nonempty.
  - `upres Acq (WrZ 1) = false` while `dto Wmb DW = true`.
  - `upres (GT 0) (RdX 0) = false`, and `GT→Rmb`, `Acq→Wmb`, `Wmb→Rel` are true.
- **Source reads.** I read every cited definition. The matrix's line numbers are accurate.

## Verdict

The rows of the matrix that describe the paper's SeqLock point at the right Coq objects. The central diagnosis is confirmed: the paper prints a different object from the one Coq verifies. On a line-by-line reading the gap is wider than the matrix says:

- the paper's own COH cell interface (exports Local) cannot carry the barriers;
- the barrier object has a semi-independence of its own that nothing in the paper describes;
- Def. 5.8 already fails on the running example itself, not only on abstract bracketed components;
- the futures program differs from the paper's compilation ⟦-⟧ in more places than the two early waits;
- the only Coq artifact for the paper's TSO SeqLock (`SeqLockTSO`) is verified against an underlay LTS that differs from the TR's in five rules.

Matrix corrections:
- RE-06 and RE-07 are stale: `SeqLockLB.v` now gives a closed module-level LB execution with same-thread overlap over a non-trivial underlay LTS.
- RE-03 overclaims "done".
- RE-27's gap is stale: the formal Def. 2.1 already matches `RelaxedTraceLin.rhb`.

No redesign is needed for fidelity. The Coq object is the right one to print. The fix is a paper rewrite, plus three small Coq lemmas that let the paper justify each change from the running example itself:
- `paper_code_torn_on_COH`;
- `seqlock_z_not_compatible`;
- `COH_kinded_tensor`.

## Line-by-line differences a reader would see

For each: Paper (P), Coq, and what must change.

**D1. Data cells.**
- P: `x, y : TSO` (figures/SeqLock.tex:10, overview.tex:278, App. SeqLock.tex:3,29).
- Coq: COH[x], COH[y], same-object I=∅ (SeqLockCOH.uobj/same_obj :182).
- Change: **paper** (D6).

**D2. Cell interface.**
- P: COH exports λ_.local (trace.tex:205, :411; overview.tex:341).
- Coq: kinded DW/DR (SeqLockCOH.ucat :202). Under Local, rmb/wmb order nothing (checked).
- Change: **paper**. The derived I_COH is unchanged, so COH[Locs]=⊗COH[loc] survives.

**D3. Barriers.**
- P: none.
- Coq:
  - `write = acq; wmb; x.wrt; y.wrt; wmb; rel`;
  - `read = get_ticket; rmb; x.rd; y.rd; rmb; test_ticket`;
  - the barriers live on a separate Barrier object: no-op sequential spec, internal I = {(wmb,rmb),(rmb,wmb)} (checked).
- The hierarchy in figures/SeqLock.tex:83-110 has no Barrier box.
- Change: **paper**.

**D4. Overlay interface.**
- P: I=∅, rd↦rfence, wrt↦lfence (trace.tex:395).
- Coq:
  - inside the SeqLock component I=∅; write↦Wmb, read↦Rmb (SeqLockProg.fcat :194);
  - across components I = findep (:208), i.e. LB pairs and SB pairs;
  - `mode := Local` is a placeholder (:211).
- The printed rfence/lfence modes are refuted for this object by `paper_modes_fail` (:1830; witness level, X_lb, vm_compute). `paper_signature_fails` (:1812) refutes the DWrel/DRacq variant, not the printed modes.
- Change: **paper** (D3). Using Rmb/Wmb also removes the rfence naming clash that reviewer A complained about (popl2027-reviews.md:112-114).

**D5. Client cell z.**
- P: absent.
- Coq: SeqLock ⊎ COH[z] is one module (SeqLockProg.M :251) with forwarding zw/zr. z also sits in the underlay State.
- Change: **paper** introduces it. Harmless for SeqLock correctness.

**D6. TicketLock code.**
- App. SeqLock.tex:6-25 is the code of TicketLockCOH.v:5-10 up to names.
- Coq's `||` short-circuits: for odd s, `test_ticket` makes no call (silent test_ticket).
- Change: harmless; the **paper** should state the short-circuit.

**D7. next_ticket.**
- P: TSO (figures/SeqLock.tex:103, App:8).
- Coq: COH[nxt] with faa. The rc instance also makes `nxt.faa` acq_rel (TicketLockCOH.rcC).
- Change: **paper**. faa is not grounded in memory/ (RE-22).

**D8. TicketLock specification.**
- P (TR :85-111): view LTS over (nxt,own); Acq needs nxt=own; Rel has no holder check; TestTick has a variable clash.
- Coq (TicketLockCOH.tl_step :197): an SC lock with a version counter. acq needs an even version and a free lock; rel needs caller = holder. Clients must satisfy `bracketed` (:151).
- Change: **paper**.

**D9. TicketLock interface.**
- P: not in the main text. The TR's I_E (App:50-57) puts (rel, get_ticket) and (rel, test_ticket) in I, and has only TSO-shaped cross pairs.
- Coq: TicketLock I=∅, `plainTL` = (RMW, RMW, R, R). Cell pairs are COH; barrier pairs come from the table.
- Change: **paper**.

**D10. Counter.**
- P: two implementations (faa/rd; faa rel / rd acq), with arity `inc(loc)` against the TicketLock's `owner.inc()`. The TR has three more Counter codes.
- Coq: no implementation. Counter[own] is abstract, with categories `CCats` (plainC, rcC). A TSO counter appears only as `tso_counter_exports_plain`.
- Change: **Coq** for Tier B; otherwise the **paper** calls the Counter an assumed specification.

**D11. Futures program.**
- P: ⟦-⟧ (impl.tex:29-42) waits only before a use.
- Coq is more synchronized:
  - a wait right after acq;
  - a wait right after get_ticket;
  - all five futures of a failed iteration are waited before the retry;
  - untagged `Future` (the positional tag).
- The paper's ctrlops of TicketLock are undefined, so ⟦read⟧ is not determined.
- Change: **paper** prints the futures program, or **Coq** switches to FutureD with the paper's tags and drops the three waits.

**D12. Retry loop.**
- Same structure, and Coq's COH writer may write y before x (`retry_wit`). Harmless.

**D13. Sequential specification.**
- P: no ν_SeqLock in the main text; the TR gives a timestamped LTS (:125-138).
- Coq: `nu_sl`, a pair register from (0,0) (:678).
- Change: **paper** prints the register.

**D14. Initial values.**
- Coq: everything is 0 and the lock is free. The paper does not say.
- Change: **paper** states them.

**D15. Linearization points.**
- TR: test_ticket (:173).
- Coq (SeqLockCOH.lpi :258): a read linearizes at the first rmb of its final iteration, a write at its first wmb. This choice is what makes read↦Rmb exportable.
- Change: **paper** (RE-35).

**D16. Parameters.**
- Coq is uniform in `rc` (the RCsc clause of dto) and parametric in the TicketLock categories K (K_ok).
- Change: **paper** names the table it uses.

**D17. Framing.**
- overview.tex:274 says the implementation exposes "only SC behavior". The example's overlay I is nonempty: it allows LB through the object.
- Change: **paper**.

**D18. Composition.**
- P: Def. 5.8 and prop:locality.
- Coq: `window_link_table`, with hypotheses E_compat, F_cross, window_bodies, positional (WindowLinkTable.v:97-186).
- Def. 5.8 fails for SeqLock ⊎ COH[z]: (acq, z.wrt) ∈ E.I, but (write, zw) ∉ F.I.
- Change: **paper**.

**D19. TSO artifact.**
- `SeqLockTSO` is written in the SC Lang, not in futures.
- Its underlay `ViewSpecs.StepSeqLockUL` (:314-410) differs from the TR LTS:
  - global freshness (∀t0. H̄(t0) < h) for wrt, acq, rel, get_ticket and test_ticket;
  - wrt is gated on ownership;
  - rel advances every thread's view;
  - test_ticket(n) requires nxt = n.
- My derivation, not checked in Coq: under these rules test_ticket never returns true, so the retry path of `Mseqlock` is unreachable.
- Change: **paper**. Retire the TSO SeqLock, or stop citing `Mseqlock` as "the SeqLock example" (intro.tex:113).

## Redesign assessment

No redesign of the formalization is needed for fidelity. Two conditions:
- The author confirms D3/D6: the COH, rmb/wmb, category-table object becomes the printed one.
- The code-faithfulness choice for D11 is made before SL-nonvac builds more executions on `SeqLockProg.M`.

