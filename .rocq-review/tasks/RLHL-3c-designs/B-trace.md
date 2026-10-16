# RLHL-3c design, trace-theoretic angle

## 0. Checked against the tree (Rocq 9.3.0, piped `rocq repl`, no files written)

**Existing names used below.** Their signatures were checked:
- `MTraces`, `RTraces`, `RCompLin`, `idF`, `idF_produces`, `cc_trace`, `exec_snoc`, `exec_app_inv`, `overlay_events_split`, `select_of_cross`, `mtraces_prefix` (`RelaxedHoareCompLin`);
- `vf_path`, `vf_path_snoc`, `overlay_events`, `GSimRel`, `rinv_exec` (`RelaxedGSim`);
- `RelaxedHoareSpec.vf_path_app_inv`, `RelaxedHoareSpec.EI`, `ei_step`, `ei_hvf`;
- `hlift`, `hlift_ei`, `rtraces_hlift`, `complin_hlift_under`, `EIhl`, `CCInv`, `SCC`, `scc_invoke`, `scc_underlay`, `scc_return`, `ACall`, `APhase`, `rekey`, `cc_rel_lin`, `rlhl_complin_eihl` (`RelaxedHoareCompLinSpec`);
- `module_dependency_soundness`, `select_frontier_tagged_split` (`RelaxedModuleSemantics`);
- `instrument`, `iinv_reach`, `IInv` with `ii_order`, `ii_no_overtake`, `ii_used_nodup`, `ii_partition`, `ii_ret_after`, `ii_returned_done`, `ii_pool_active`, and also `produced_response_invoked`, `local_inv_unique` (`RelaxedModuleFacts`).

**Names that do not exist yet:**
- `underlay_events`, `LTraces`, `Lift`, any chaos LTS;
- a tagged module error rule (only the positional `module_error` exists);
- an exec-append lemma;
- a lemma "every invocation of a completed method trace has its response".

**Proposed definitions that typecheck.** `Lift`, `lift_step`, `LTraces`, and the statements of `lift_traces`, `mtraces_mono`, `absorb_ei` and `rcomplin_layer` below all typecheck (`Abort`ed). A nested `Lift (Lift V M1) M2` also typechecks, so towers of layers raise no universe problem.

**`ResEvInversion` uses `eq_rect_eq`.** Results must be compared through event or record projections (as `entry_res_ev` and `some_inj` already do), not through `ResEvInversion`.

## 1. Trace-determinedness and `mtraces_mono` (M-22 item 1)

**Statements.** New file `models/simlin/RelaxedModuleLTS.v`.
```coq
Definition underlay_events {E F} (evs : list (ModuleEvent E F)) : list (ThreadEvent E) :=
  flat_map (fun ev => match ev with UnderlayEvent e => [e] | OverlayEvent _ => [] end) evs.
Definition LTraces {E} (V : LTS E) (v : State V) (u : list (ThreadEvent E)) : Prop :=
  exists v1, vf_path V v u v1.
Definition restate {E F} {V1 V2 : LTS E} (c : @TaggedModuleConfig E F V1) (q : State V2)
  : @TaggedModuleConfig E F V2 := Build_TaggedModuleConfig q (tm_calls c) (tm_queue c) (tm_used_underlay c).

Lemma exec_underlay_path {E F} V (M : RelaxedModuleImpl E F) c evs c' :
  module_execution_tagged V M c evs c' -> vf_path V (tm_lts_state c) (underlay_events evs) (tm_lts_state c').
Lemma exec_transfer {E F} (V1 V2 : LTS E) M (c : @TaggedModuleConfig E F V1) evs c' q2 q2' :
  module_execution_tagged V1 M c evs c' -> vf_path V2 q2 (underlay_events evs) q2' ->
  module_execution_tagged V2 M (restate c q2) evs (restate c' q2').
Theorem mtraces_mono {E F} (V1 V2 : LTS E) (v1 : State V1) (v2 : State V2) (M : RelaxedModuleImpl E F) :
  (forall u, LTraces V1 v1 u -> LTraces V2 v2 u) -> forall s, MTraces V1 M v1 s -> MTraces V2 M v2 s.
```
- An optional trace-determinedness corollary, `mtraces_decomp`, uses `Chaos E := {| State := unit; Step := fun _ _ _ => True; Error := fun _ _ => False |}`:
  - it states `MTraces V M σ s <-> exists evs, (exists c, module_execution_tagged (Chaos E) M (initial_tagged_module _ tt) evs c) /\ LTraces V σ (underlay_events evs) /\ overlay_events evs = s`;
  - it says that `MTraces` is fixed by M's scheduler traces together with the underlay trace set.
- **Proof.** Both lemmas go by induction on the execution. They work because `tagged_invoke` and `tagged_return` never read `q`, and `tagged_underlay` reads it only through `Step VE` (`RelaxedModuleSemantics.v:596`). Monotonicity is path extraction, then the inclusion, then transfer.
- **Sanity check.** Re-derive the ⇐ half of `hlift` from `mtraces_mono` using `hl_step_base`.
- **Risk:** low. **Effort:** about 150–250 lines.

## 2. The module trace-LTS (item 2, first half)

```coq
Definition is_underlay {E F} (e : ModuleEvent E F) : Prop :=
  match e with UnderlayEvent _ => True | OverlayEvent _ => False end.
Definition lift_step {E F} (V : LTS E) (M : RelaxedModuleImpl E F) (ev : ThreadEvent F) (c c1 : @TaggedModuleConfig E F V) :=
  exists evs, Forall is_underlay evs /\ module_execution_tagged V M c (evs ++ [OverlayEvent ev]) c1.
Definition Lift {E F} (V : LTS E) (M : RelaxedModuleImpl E F) : LTS F :=
  {| State := @TaggedModuleConfig E F V; Step := lift_step V M; Error := fun _ _ => False |}.
Theorem lift_traces {E F} (V : LTS E) M (σ0 : State V) s :
  LTraces (Lift V M) (initial_tagged_module V σ0) s <-> MTraces V M σ0 s.
Corollary rcomplin_lift {E F} M (VE : LTS E) σ0 (VF : LTS F) v0 :
  RCompLin M VE σ0 VF v0 <-> forall s, LTraces (Lift VE M) (initial_tagged_module VE σ0) s ->
                                         LTraces (Lift VF idF) (initial_tagged_module VF v0) s.
```
- **Proof of ⇒.** Concatenate the blocks with a new `exec_app` lemma (an `exec_snoc` induction).
- **Proof of ⇐.** Use the generalized lemma: from a pending underlay prefix `pre`, `exec c0 pre c`, and `exec c evs c'`, there is `c''` with a Lift path from `c0` labelled `overlay_events evs` ending in `c''`. Underlay steps after the last overlay event are dropped, which is harmless because `LTraces` is existential in the end state.
- **Risk:** low. `Error := False`, so this stays partial correctness, as `RCompLin` is. **Effort:** about 150–250 lines.

## 3. Absorption (item 2, second half): what holds and what does not

**General absorption fails for arbitrary V.** The claim is: `MTraces (Lift V idF) M (init v) ⊆ MTraces V M v` (cc_E;⟦M⟧ ⊆ ⟦M⟧). Counterexample sketch:
- M's body is `x <- Future op1; r <- Wait x; FutureD (if r=0 then opA else opB) no_deps …`. It is mis-tagged: control depends on `r` but the tag is empty. The shallow embedding trusts tags.
- M prophesies `r = 0`. The inner copy-cat commits `1`, and the V-response with value 1 happens.
- M never receives it, but emits `opA`.
- If V's state records responses and another thread's result reveals that, no direct execution of M has both "response with 1" and "`opA`".

There is a second obstacle: in the direct run the underlay keys are M's handles, not the inner copy-cat's. So the V path is only a key-renaming of the composite's path, and program continuations may inspect handles.

**Conclusion.** Absorption is a property of the presentation: responses must be delayable or droppable, and paths closed under key maps. `EI δ` from `(s0, [])` has both properties, and it is the only presentation the layering needs.

### Statements (new file `models/simlin/RelaxedAbsorb.v`)
```coq
Theorem transp {E F} (V : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State V) s :          (* ⟦M⟧ ⊆ cc_E;⟦M⟧, every V *)
  MTraces V M σ0 s -> MTraces (Lift V idF) M (initial_tagged_module V σ0) s.
Theorem absorb_ei {E F St} (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop)
    (M : RelaxedModuleImpl E F) (s0 : St) s :
  MTraces (Lift (RelaxedHoareSpec.EI δ) idF) M (initial_tagged_module _ (s0, [])) s ->
  MTraces (RelaxedHoareSpec.EI δ) M (s0, []) s.
Corollary saturation_ei … : MTraces (Lift (EI δ) idF) M (initial_tagged_module _ (s0,[])) s <-> MTraces (EI δ) M (s0,[]) s.
Corollary cc_idem …       : (* M := idF *) RTraces (Lift (EI δ) idF) (initial_tagged_module _ (s0,[])) s <-> RTraces (EI δ) (s0,[]) s.
Corollary absorb_eihl …   : MTraces (Lift (EIhl δ) idF) M (initial_tagged_module _ ((s0,[]),[])) s -> MTraces (EIhl δ) M ((s0,[]),[]) s.
Corollary rcomplin_paper … : RCompLin M (EI δE) (sE,[]) VF v <->
  (forall s, MTraces (Lift (EI δE) idF) M (initial_tagged_module _ (sE,[])) s -> RTraces VF v s).
```
- `absorb_eihl` follows from `lift_traces`, `rtraces_hlift`, `mtraces_mono`, `absorb_ei` and `hlift_ei`.
- `rcomplin_paper` is relaxedlin.tex:665, ν_E;cc_E;M ⊆ ν_F;cc_F, for EI presentations. It closes the "not mechanized" caveat in the `RelaxedHoareCompLin` header and at `RelaxedHoareGSim.v:303-305`.

### Proof of `transp` (simulation from the direct run to the composite)
- The inner copy-cat forwards at once. Each inner call reuses M's underlay key, so `call_fresh` and `trace_fresh` follow from M's `trace_fresh`, because the used list includes dead calls.
- Its commit is M's prophesied response value for that key. That value exists by the new lemma `produced_inv_resolved` (from `all_resolved` in `program_terminal`).
- V-invocations are bundled into the next Lift step, and V-responses into the Lift step of M's response. The V order is unchanged.
- The inner frontier holds: inner tags are `resolved_in empty_store`, so only (F1) bites.
- No `classic` is needed. **Effort:** about 300–450 lines.

### Proof of `absorb_ei` (simulation from the composite to the direct run)
- **Re-timing.** M's underlay invocation of key `k` is emitted in the direct run when the inner copy-cat emits V-inv(k). M's responses are emitted at the outer response time, when the inner copy-cat returns `k`.
  - The inner V-responses are therefore delayed to the outer response, or dropped when the inner commit differs from M's prophecy.
  - EI tolerates both. A dropped response leaves a pending record that nobody consumes.
- **Invariant.** It relates the outer instrumented run, the inner copy-cat config `ci` and the direct config `cd`:
  - (a) `IInv IT_o ic_o` at every prefix (`instrument`, `iinv_reach`);
  - (b) `CCInv δ ci Pa G` for the inner copy-cat (`Pa` ignored);
  - (c) `tm_queue cd` is `map snd` of the id-sorted merge of the outer queue with the set D of outer-emitted invocations whose inner call is in `ph0`;
  - (d) calls and used keys are equal;
  - (e) `fst` of the EI state is equal, and `Permutation (snd (state cd)) (rekey-mapped ph1 records ++ [Build_Op (ac_key a) (ac_op a) (ac_ret a) | (a, ph2) ∈ G])`.
- **Frontier cases** (same thread) when the direct run emits `inv k2` and an earlier, still pending entry e′ blocks it:
  - e′ = `inv k1` still in the outer queue: `ii_no_overtake`.
  - e′ = `inv k1` in D, outer-emitted after `k2`: `ii_order`, contrapositive. This is constructive, because tid equality is decidable and the triple negation collapses.
  - e′ = `inv k1` in D, outer-emitted before `k2`: then `k1` is older in G, so `sc_ord` puts the inner `a_inv k1` before `a_inv k2`. The inner selection crossed it, so ¬¬SI(op1, op2). `must_precede` on two invocations ignores tags and handles, so the same fact covers M's entries.
  - e′ = `res k1` still pending: `ii_no_overtake`.
- **Frontier case** when the direct run emits `res k`: only `inv k` itself could block it (`ii_used_nodup`), and it was emitted at V-inv time.
- **Outer return.** `owner_done` needs `produced_inv_resolved`, so that no D entry belongs to a returned call.
- **Reuse:** `select_of_cross`, `select_frontier_tagged_split`, `CCInv` and `sc_ord`, `rekey`.
- **New lemmas:**
  - phase-exposing variants `scc_underlay_inv` / `scc_underlay_res`, because `scc_underlay` hides which call changed phase. Add them beside the old lemmas, not as edits.
  - EI permutation-step lemmas.
- **Risks:**
  - The invariant design (highest risk).
  - Result equalities: compare through `f_equal` on event-to-record projections.
  - The initial pending list must be `[]`: otherwise an inner V-response could consume a foreign record with the same key.
  - Reusing the `CCInv` lemmas brings `classic` (NNPP in `scc_underlay`).
  - Incomplete composite runs, with calls stuck in any phase, are covered by the re-timing.
- **Effort:** about 800–1300 lines.

**The idF case.** cc;cc ⊆ cc is just `absorb_ei` with M := idF. As a separate warm-up it offers little: the forward version would need prophecy of the inner commit at the outer invocation, as in `rinv_val`.

## 4. Semantic layering (item 3)

New file `models/simlin/RelaxedLayer.v`.
```coq
Theorem rcomplin_layer {E F G St} (VE : LTS E) σ0 (δF : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop)
    (sF : St) (VG : LTS G) w0 (M1 : RelaxedModuleImpl E F) (M2 : RelaxedModuleImpl F G) :
  RCompLin M1 VE σ0 (RelaxedHoareSpec.EI δF) (sF, []) -> RCompLin M2 (RelaxedHoareSpec.EI δF) (sF, []) VG w0 ->
  forall s, MTraces (Lift VE M1) M2 (initial_tagged_module VE σ0) s -> RTraces VG w0 s.
Definition CCRefines {E} (W : LTS E) (w : State W) (V : LTS E) (v : State V) := forall s, LTraces W w s -> RTraces V v s.
Lemma layer_refines : CCRefines W w (EI δF) (sF,[]) -> RCompLin M (EI δF) (sF,[]) VG u ->
  CCRefines (Lift W M) (initial_tagged_module W w) VG u.            (* towers of any depth *)
Corollary rlhl_layer2 : RLHL2Hyps I1 R1 G1 M1 ((sE,[]),[]) (sF,[]) -> RLHL2Hyps I2 R2 G2 M2 ((sF,[]),[]) (sG,[]) ->
  forall s, MTraces (Lift (EI δE) M1) M2 (initial_tagged_module _ (sE,[])) s -> RTraces (EI δG) (sG,[]) s.
```
- **Proof of `rcomplin_layer`.** `lift_traces` and layer 1 give `L(Lift VE M1) ⊆ L(Lift (EI δF) idF)`. Then `mtraces_mono`, then `absorb_ei` at δF, then layer 2.
- **`rlhl_layer2`.** Each `RLHL2Hyps` goes through `rlhl_complin_eihl`. A complete-trace `rel_lin` corollary follows via `cc_rel_lin`.
- **Not blocked by absorption.** First prove `rcomplin_layer_abs` with the explicit hypothesis `Habs : forall s, MTraces (Lift VF idF) M2 (init v) s -> MTraces VF M2 v s`, and discharge it later with `absorb_ei`.
- **Regression.** Compose Counter_xy with a second `ren_rlhl2` layer (e.g. a renaming of the overlay) and print the assumptions.
- **Risk:** low. **Effort:** about 150–300 lines.

## 5. Client of Counter_xy (item 5)

New file `examples/Relaxed/RelaxedHoareClientSB.v`. It imports CounterXY and does not edit it, because the Writer is editing that file.

**Client.**
- Signature `GSB`: operations `RunSB (c : CLoc)`, arity `nat`, handles `nat`, SI ∅, mode `Local`.
- Module:
```coq
Csb (RunSB c) _ := Future (Inc c) (fun f => Wait f (fun _ => Future (Get (oth c)) (fun g => Wait g (fun r => Ret r)))).
```
The untagged `Future` after `Wait` has tag `{h_inc}`, so (F3) orders `res inc` before `inv get`.

**Main theorem.**
```coq
Theorem csb_no_00 : forall s, MTraces (Lift (RelaxedHoareSpec.EI δmem) M_cxy) Csb (initial_tagged_module _ (s00, [])) s ->
  forall t1 h1 t2 h2, In (Build_ThreadEvent t1 (@ResEv GSB h1 (RunSB CX) 0)) s ->
                      In (Build_ThreadEvent t2 (@ResEv GSB h2 (RunSB CY) 0)) s -> False.
```
- It holds for every execution, complete or not.
- **Proof.** `cxy_complin_ei` with `lift_traces` and `mtraces_mono`, then `absorb_ei` at δcxy, then the spec-only lemma `csb_spec_no_00` over `EI δcxy`. Steps of `csb_spec_no_00`:
  - instrument the run; a returned call has all its events emitted (`ii_returned_done`, `ii_partition`);
  - trace inversion `csb_trace`, in the view-function style of `cc_trace`;
  - `inv inc < res inc < inv get` (EI pairing and `module_dependency_soundness`);
  - an EI path value lemma (a Get returns the counter value at its invocation) and `δcxy_mono`;
  - the cycle argument on the two Get positions.
- **Non-vacuity:**
  - over EI δcxy both runs can return (e.g. with (0,1));
  - the client without `Wait` admits (0,0) at spec level, because `by_counter` lets the Get overtake the Inc at the client frontier.
  - An implementation-level (0,0) witness is optional. It needs a renaming-completeness lemma `RTraces (EI δcxy) ⊆ MTraces (EI δmem) M_cxy` plus `transp`.
- **Fallback route R1.** It needs no absorption and covers complete executions only. The FC trace lies in `MTraces (EI δmem) M_cxy`; apply `cxy_rel_lin`; the res→inv rhb edge plus `seq_legal` gives a contradiction, on the template of `sb_not_rel_lin0`. This is the review's "res→inv rhb edge" wording and can be built before item 3.
- **Risks:**
  - extracting the returned value (`ii_pool_active` plus `finish_call`, with dependent arities);
  - the `program_resolve` variants in trace inversion.
- **Effort:** about 600–1000 lines.

## 6. m-8: the error clause with an implementation-side obligation

### m-8a (new file `models/simlin/RelaxedHoareErr.v`, plus tests)
```coq
Inductive module_error_tagged_at {E F} (VE : LTS E) : CallKey F -> @TaggedModuleConfig E F VE -> Prop :=
| tagged_error_at cand q pool queue queue' used (Hsel : select_frontier_tagged cand queue queue')
    (Herr : Error VE (untag (ts_event cand)) q) :
    module_error_tagged_at VE (ts_owner cand) (Build_TaggedModuleConfig q pool queue used).
Variant TItem (F : RelaxedSig.t) := TEv (e : ThreadEvent F) | TErr (t : tid).
Definition MTracesE VE M σ0 s := exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\
  (s = map TEv (overlay_events evs) \/ exists k, module_error_tagged_at VE k c /\ s = map TEv (overlay_events evs) ++ [TErr (fst k)]).
Definition RTracesClosed VF v s := MTracesE VF idF v s \/ exists p t tl, MTracesE VF idF v (p ++ [TErr t]) /\ s = p ++ tl.
Definition RCompLinErr M VE σ0 VF v0 := forall s, MTracesE VE M σ0 s -> RTracesClosed VF v0 s.
Definition EIe δ (pre : St -> Sig.op (RelaxedSig.effect F) -> Prop) : LTS F :=
  {| State := St * list (Op F); Step := RelaxedHoareSpec.ei_step δ;
     Error := fun ev s => match te_ev F ev with InvEv _ o => ~ pre (fst s) o | _ => False end |}.
```
- **Inclusion lemmas:**
  - `rcomplin_err_of_rcomplin`, assuming `forall ev q, ~ Error VE ev q`;
  - `rcomplin_of_err`, assuming VF has no errors;
  - `mtracesE_noerr`.
- **`GSimRelErr`.** Either `p = PossError`, or the `gsim_step` clauses allowing `p' = PossError`, plus the clause `module_error_tagged_at VE k c -> poss_steps VF p PossError`.
- **`gsim_complin_err`.**
  - Generalize `rinv_exec` to stop at `PossError`.
  - Reify the `PossOk` prefix.
  - New `CInv` lemma: an enabled abstract invocation that errors (`psa_inv_error`) is on the reified copy-cat's frontier, so the copy-cat reaches `module_error_tagged_at`. Then take the closure branch.
- **RLHL side.** `CallTripleE` is `CallTriple` plus `ct_noerr`, in one of two forms:
  - (A) strict: `~ Error VE (untag m) σ`;
  - (B) LHL-style: `Error VE (untag m) σ -> poss_steps VF p PossError`.
  - Then `RLHL2HypsE` gives `GSimRelErr`, with S extended by `(c, PossError)`, and `rlhl_complin_err` follows.
- **Tests:**
  - δ_lock: a partial Acq means blocking; `pre s Rel := s = true`.
  - T1, the review's counterexample: `Bad ↦ acquire; release; release`. The old `RCompLin` over `EI δ_lock` holds (the call blocks), while `¬ RCompLinErr` over `EIe` (an explicit TErr trace).
  - T2 (positive): a renaming lock wrapper, which needs option (B).
- **Effort:** about 1000–1600 lines. **Risk:** medium-high (the extension of `rinv_exec`/`reify`).

### m-8b (deferred)
- Error-aware `LTracesE` with an `LErr e` item.
- `mono_err` with the closure.
- Error-aware layering, with an analogue of `CompLinVComp.closed_absorb`.

## 7. Writer sub-tasks (order: 1 → 2 → 3 → 4(Habs) → 5 → 6 → 7; then 8 if the author wants it)

1. **`RelaxedModuleLTS.v`** (and `_CoqProject`). Contents: `underlay_events`, `restate`, `exec_app`, `exec_underlay_path`, `exec_transfer`, `mtraces_mono`, `LTraces`, `Lift`, `lift_traces`, `rcomplin_lift`, optional `mtraces_decomp`, and the `hlift` sanity check. Accept if everything is Closed.
2. **Program-trace and instrumentation lemmas**, appended to `RelaxedModuleFacts.v` or in a new file: `produced_inv_resolved`, uniqueness of responses per handle, and return-value extraction from `IInv`. Accept if Closed.
3. **`RelaxedAbsorb.v`, part 1:** `transp`. Accept if Closed.
4. **`RelaxedLayer.v`:** `rcomplin_layer_abs` (with `Habs`), `layer_refines`, `rlhl_layer2_abs`, and the two-renaming-layer test. Accept if assumptions are within {`classic`}.
5. **`RelaxedAbsorb.v`, part 2**, plus phase lemmas beside `scc_underlay` in `RelaxedHoareCompLinSpec.v`: `absorb_ei`, `saturation_ei`, `cc_idem`, `absorb_eihl`, `rcomplin_paper`; then discharge `Habs` in `RelaxedLayer.v`. Accept if assumptions are within {`classic`} and no existing statement changes.
6. **`RelaxedHoareClientSB.v`:** `csb_trace`, `csb_spec_no_00`, `csb_no_00`, the non-vacuity witnesses, and optionally the R1 cross-check. Accept if assumptions are within {`classic`, `eq_rect_eq`} and the header has K/S/P/R.
7. **m-8a**, only after the author decisions D4–D6: `RelaxedHoareErr.v` plus lock tests. Accept on T1 and T2, the inclusion lemmas, and assumptions printed.
8. **m-8b**, optional.

## 8. Research-level decisions for the author

- **D1. Semantic layering.** `Prog` has no fork or substitution, so the composite is `MTraces (Lift VE M1) M2`, not a `RelaxedModuleImpl`. There is no relaxed analogue of ▶ₘ. This matches strategy composition in the paper, but not "M2∘M1 is an implementation".
- **D2. Scope of absorption.** It is proved for `EI δ` from `(s0, [])`, with `EIhl` as a corollary. For other underlays it is false in general (§3); for the memory route that means `EIhl δ_mem`, not the raw cell. The F-side of saturation (⟦M⟧;cc_F) is not needed.
- **D3. Which client.** The semantic theorem `csb_no_00`, or an RLHL client proof.
  - A deterministic spec "inc, then read the other counter" is not valid: (1,1) is a real outcome.
  - A nondeterministic δSB′ ("return ≥1 if the other run has already linearized") works.
  - That RLHL proof would carry value content (B-1 (4′)) and costs about 600–1000 extra lines.
- **D4. EIe semantics.** The review proposes "Error when δ has no successor". That conflicts with blocking: a partial δ already means a correct blocking acquire under EI. I propose an explicit precondition `pre` instead.
- **D5. The TErr tag:** tid (enough for vertical composition), or op/key, which CompLin uses for horizontal projection.
- **D6. The `ct_noerr` form.** (A) strict suffices for the counterexample. (B) LHL-style is needed for any layer that forwards a precondition.
- **D7. Errors through Lift.** LTS `Error` is indexed by an event, but M1's errors are internal. One option is that Lift's `Error` holds whenever M1 can reach an error by internal steps, for every event.
- **D8. Order.** I propose the client before m-8, because m-8 is blocked on D4–D6.

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleFacts.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLin.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareCounterXY.v