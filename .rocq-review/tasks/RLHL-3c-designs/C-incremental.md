# RLHL-3c design (minimal-risk incremental angle)

## Bottom line

The shortest honest path to one end-to-end client result for Counter_xy needs only three things:

- a trace-LTS of a module, `TLTS`/`MLTS`;
- its monotonicity, `tlts_mono`, as a stand-in for `mtraces_mono` (proved Closed in a scratch session);
- the existing `cxy_complin_ei` and `cc_rel_lin`, plus the instrumented facts already in `RelaxedModuleFacts`.

**Absorption is not on the critical path.** The client proof can be done semantically over the copy-cat-saturated spec, `MLTS (EI δcxy) idF`. Absorption becomes necessary only when the upper layer is itself verified by RLHL, i.e. over the plain `EI`/`EIhl`.

**m-8 is not on the critical path either.** Both `δcxy` and `δmem` are total.

General `mtraces_mono` is cheap and useful but optional for the client.

I checked in a piped `rocq repl` (Rocq 9.3.0; nothing written to disk):

- All definitions and the client statements below typecheck.
- `tlts_mono` (with `retag`, `retag_step`, `retag_exec`) is proved, and `Print Assumptions tlts_mono` reports "Closed under the global context".
- `RelaxedModuleFacts.finish_call_source`, `instrument`, `module_dependency_soundness`, `cc_trace_wf`, `cc_rel_lin` and `cxy_complin_ei` have the expected types.

**Expected axioms of the final client theorem:** `classic` (through `cxy_complin_ei` and `cc_trace_wf`) and `eq_rect_eq` (through `cc_rel_lin`). This is within the baseline.

---

## Item A. Module trace-LTS and semantic linking (critical path, cheap)

**(1) Statements.** New generic file `models/simlin/RelaxedHoareLink.v`, placed after `RelaxedHoareCompLinSpec.v` in `_CoqProject`. All of this typechecks.

```coq
Definition TLTS {F} (T : list (ThreadEvent F) -> Prop) : LTS F :=
  {| State := list (ThreadEvent F);
     Step := fun ev s s' => s' = s ++ [ev] /\ T s';
     Error := fun _ _ => False |}.
Definition MLTS {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) : LTS F :=
  TLTS (MTraces VE M σ0).
(* "N over (M over VE)" := MTraces (MLTS VE M σ0) N [] *)

Definition underlay_events {E F} (evs : list (ModuleEvent E F)) : list (ThreadEvent E) :=
  flat_map (fun ev => match ev with UnderlayEvent e => [e] | OverlayEvent _ => [] end) evs.

Theorem tlts_mono {F G} (T T' : list (ThreadEvent F) -> Prop) (P : RelaxedModuleImpl F G) :
  (forall s, T s -> T' s) -> forall s, MTraces (TLTS T) P [] s -> MTraces (TLTS T') P [] s.   (* proved, Closed *)
Lemma mtraces_nil VE M σ0 : MTraces VE M σ0 [].
Lemma tlts_exec_state T P c evs c' :
  module_execution_tagged (TLTS T) P c evs c' ->
  tm_lts_state c' = tm_lts_state c ++ underlay_events evs /\
  (underlay_events evs = [] \/ T (tm_lts_state c')).
Theorem link_mono {E F G} (M : RelaxedModuleImpl E F) VE σ VF v (N : RelaxedModuleImpl F G) :
  RCompLin M VE σ VF v -> forall s, MTraces (MLTS VE M σ) N [] s -> MTraces (MLTS VF idF v) N [] s.
Theorem rcomplin_link {E F G} (M1 : RelaxedModuleImpl E F) (M2 : RelaxedModuleImpl F G) VE σ VF v VG w :
  RCompLin M1 VE σ VF v -> RCompLin M2 (MLTS VF idF v) [] VG w -> RCompLin M2 (MLTS VE M1 σ) [] VG w.
Theorem client_rule {E F G} (M : RelaxedModuleImpl E F) VE σ VF v (P : RelaxedModuleImpl F G) (Φ : list (ThreadEvent G) -> Prop) :
  RCompLin M VE σ VF v -> (forall s, MTraces (MLTS VF idF v) P [] s -> Φ s) ->
  forall s, MTraces (MLTS VE M σ) P [] s -> Φ s.
```

**(2) Proof strategy.**

- `tlts_mono`: `retag` keeps all four config fields. It is done (the scratch proof above, about 15 lines).
- `link_mono`: from `tlts_mono` and `RCompLin`.
- `rcomplin_link` and `client_rule`: one-liners.
- `tlts_exec_state`: induction on the execution; only `tagged_underlay` touches the state.

**(3) Reuse.** `MTraces`, `RTraces`, `RCompLin`, `idF`, `mtraces_prefix`, and the `drop_cfg`/`drop_step` pattern of `hlift`.

**(4) Risks.**

- **Fidelity.** `TLTS` linking equals a joint execution (N interleaved with one M execution) only for finite traces. The joint-to-TLTS direction follows from `mtraces_prefix`. The TLTS-to-joint direction needs a merge argument (`link_joint`, deferred). Until then this is argued, not proved.
- **Not a module.** The composite is an LTS over F, not a module E→G. A third layer is `MLTS (MLTS VE M1 σ) M2 []`.

**(5) Effort.** 150–250 lines, about half a day.

---

## Item B. `mtraces_mono` (optional for the client; cheap; needed later for absorption)

**(1) Statements.** In `RelaxedHoareLink.v`, part 3.

```coq
Definition ltraces {E} (V : LTS E) (v : State V) l := exists v', vf_path V v l v'.
Theorem mtraces_tlts {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) σ s :
  MTraces VE M σ s <-> MTraces (TLTS (ltraces VE σ)) M [] s.        (* trace-determinedness *)
Corollary mtraces_mono VE VE' M σ σ' :
  (forall l, ltraces VE σ l -> ltraces VE' σ' l) -> forall s, MTraces VE M σ s -> MTraces VE' M σ' s.
```

**(2) Proof strategy.**

- **⇒ direction.** Invariant: `vf_path VE σ (tm_lts_state c_T) (tm_lts_state c_VE)`.
- **⇐ direction.** Take one `vf_path` for the final underlay trace. Replay the TLTS execution while carrying the remaining path suffix, using `vf_path_app_inv` from `RelaxedHoareSpec`.
- **Corollary.** `mtraces_mono` follows from `tlts_mono`.

**(3) Reuse.** `vf_path`, `vf_path_snoc` (`RelaxedGSim`), `vf_path_app_inv`.

**(4) Risk.** Low. The only care point is that TLTS steps do not fix one consistent VE path, so you must replay against the final path, not step by step.

**(5) Effort.** 200–300 lines, about one day.

---

## Item C. Absorption (deferred; not on the client's critical path)

**(1) Statements.**

```coq
Theorem absorb_cc_ei {F St} (δ : ...) s0 s :                 (* cc;cc ⊆ cc *)
  RTraces (MLTS (EI δ) idF (s0, [])) [] s -> RTraces (EI δ) (s0, []) s.
Theorem absorb_ei {F St G} (δ : ...) s0 (N : RelaxedModuleImpl F G) s :
  MTraces (MLTS (EI δ) idF (s0, [])) N [] s -> MTraces (EI δ) N (s0, []) s.
(* sanity, the cheap converse: *)
Lemma cc_unit_left VF v N s : (forall o, inhabited (Sig.ar o)) ->
  MTraces VF N v s -> MTraces (MLTS VF idF v) N [] s.
```

**(2) Proof strategy.**

- Instrument N's execution over TLTS. Take the copy-cat execution `w` that witnesses N's final underlay trace `s_u`, instrumented as well.
- Build N's execution over `EI δ` that emits its queue events in w's underlay order `u`, with copy-cat handles renamed back to N's keys. That map is a function because copy-cat underlay keys are fresh (`trace_fresh`).
- Place N's overlay events by their `s_u` positions in `w`.
- Frontier obligations:
  - (F1) is preserved by `u`.
  - (F2): non-SI same-thread invocations keep the copy-cat queue order, which is the `s_u` order.
  - (F3): u-res(r) < s-res(r) < s-inv(i) < u-inv(i).
  - Returns: u-inv < u-res < s-res ≤ N-Ret.
- `EI` paths are invariant under any key renaming. `ei_step` only adds, or removes by `In`, records keyed `(t, h)`.

**(3) Reuse.** `instrument`, `IInv` (`ii_order`, `ii_ret_after`, `ii_emitted_after`, `ii_partition`), `cc_trace`, `hlift` (to move to `EIhl`).

**(4) Risks (high).**

- Three-configuration simulation.
- Pending copy-cat calls at the end mean some N events have no u-counterpart. They stay queued; this must be shown not to block later events.
- Handle renaming.
- `cc_unit_left` needs an inhabited arity (for an empty arity, `idF` cannot invoke) and `classic`, as in `rinv_val`.

**(5) Effort.** 1,500–3,000 lines, 3–5 weeks.

---

## Item D. Semantic layering (TLTS form on the critical path; RLHL form deferred)

**On the critical path:** `rcomplin_link` and `client_rule` (Item A).

**Deferred, needs `absorb_ei`:**

```coq
Theorem rlhl_link ... :
  RLHL2Hyps I1 R1 G1 M1 (σ, []) (v0, [])      (* over EIhl δE into EI δF *) ->
  RLHL2Hyps I2 R2 G2 M2 (v0, []) (w0, [])     (* over EIhl δF into EI δG *) ->
  RCompLin M2 (MLTS (EI δE) M1 σ) [] (EI δG) (w0, []).
```

Proof: `rlhl_complin_eihl` for both layers, then `absorb_ei`, then `rcomplin_link`.

**EIhl vs EI.** This is not an obstacle at the trace level. `hlift` is an MTraces equivalence for every module, so absorption is stated over `EI` and moved to `EIhl` by `hlift_ei`.

---

## Item E. m-8: error clause with implementation-side obligation (deferred; needs the author)

**(1) Statements.** New definitions beside the old ones.

```coq
Definition EIe δ : LTS F := {| State := ...; Step := ei_step δ;
  Error := fun ev s => match te_ev F ev with InvEv _ o => ~ exists r s', δ (fst s) o r s' | _ => False end |}.
Definition module_error_tagged VE M (c : TaggedModuleConfig VE) (k : CallKey F) : Prop :=
  exists cand q', select_frontier_tagged cand (tm_queue c) q' /\ ts_owner cand = k /\
                  Error VE (untag (ts_event cand)) (tm_lts_state c).
Variant RItem F := REv (e : ThreadEvent F) | RErr (k : CallKey F).
Definition MTracesE VE M σ0 (s : list (RItem F)) : Prop :=
  exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\
   (s = map REv (overlay_events evs) \/ exists k, module_error_tagged VE M c k /\ s = map REv (overlay_events evs) ++ [RErr k]).
Definition RTracesClosed VF v s := MTracesE VF idF v s \/ exists p k tl, MTracesE VF idF v (p ++ [RErr k]) /\ s = p ++ tl.
Definition RCompLinErr M VE σ VF v := forall s, MTracesE VE M σ s -> RTracesClosed VF v s.
Lemma rcomplin_err_of_old : (forall ev q, ~ Error VE ev q) -> RCompLin M VE σ VF v -> RCompLinErr M VE σ VF v.
```

Then `GSimRelErr`, an error-free obligation `ct_noerr` in `CallTriple`, and the re-proof of `gsim_complin`.

**(4) Risks.** Medium–high:

- where the implementation-side obligation lives;
- the error-marker interaction with `reify`.

The amendment (implementation must not misuse the underlay; counterexample acquire; release; release) has not been put to the author.

**(5) Effort.** 800–1,500 lines, 1–2 weeks.

---

## Item F. Client semantics and the Counter_xy client theorem (critical path)

### What a client is here

A client is a module `P : RelaxedModuleImpl FC U` over a unit-style overlay signature `U`, whose operations are the "main" programs. The environment may invoke them any number of times, on any threads, overlapping. The claim quantifies over all such runs.

The client run over the implementation is `MTraces (MLTS (EI δmem) M_cxy (s00, [])) Psb [] s`, i.e. Psb over the trace-LTS of Counter_xy over the SC cell.

New file: `examples/Relaxed/RelaxedHoareCounterXYClient.v`, after `RelaxedHoareCounterXY.v`. It only imports that file, which the Writer is concurrently editing, so it must not edit it. These definitions typecheck:

```coq
Inductive UOp : Type := Main1 | Main2.
Definition u_ar (_ : UOp) : Type := nat.
Canonical Structure UEff : Sig.t := {| Sig.op := UOp; Sig.ar := u_ar |}.
Definition U : RelaxedSig.t := {| RelaxedSig.effect := UEff; RelaxedSig.handle := nat;
  RelaxedSig.semi_independent := fun _ _ => False; RelaxedSig.mode := fun _ => Local |}.
Definition sbw (c1 c2 : CLoc) : Prog FC nat :=
  @Future FC nat (Inc c1) (fun f => Wait f (fun _ => @Future FC nat (Get c2) (fun g => Wait g (fun r => Ret r)))).
Definition Psb : RelaxedModuleImpl FC U := fun o _ => match o with Main1 => sbw CX CY | Main2 => sbw CY CX end.
Definition sbw_outcome00 (s : list (ThreadEvent U)) : Prop :=
  exists t1 h1 t2 h2, In (Build_ThreadEvent t1 (@ResEv U h1 Main1 0)) s /\ In (Build_ThreadEvent t2 (@ResEv U h2 Main2 0)) s.

Theorem sbw_over_spec s :      (* mentions only δcxy, by_counter, idF: "uses the spec only" *)
  MTraces (MLTS (@RelaxedHoareSpec.EI FC MSt δcxy) idF (s00, [])) Psb [] s -> PrefixView.complete s -> ~ sbw_outcome00 s.
Theorem sbw_client s :
  MTraces (MLTS (RelaxedHoareSpec.EI δmem) M_cxy (s00, [])) Psb [] s -> PrefixView.complete s -> ~ sbw_outcome00 s.
(* proof: client_rule ... cxy_complin_ei sbw_over_spec *)
```

The second `Future` is untagged, so its tag is `resolved_in H`, and after the `Wait` that includes the first handle. So (F3) orders `Res(inc)` before `Inv(get)`. This is the res→inv rhb edge.

### Proof of `sbw_over_spec`: key lemmas

**F1. TLTS state.** By `tlts_exec_state` and `mtraces_nil`, P's underlay trace `s_u := underlay_events evs` is in `RTraces (EI δcxy) (s00, [])`.

**F2. Instrumentation.** `instrument` and `iinv_reach` on Psb's execution over the TLTS, giving `IInv`.

**F3. Returned value (new; the only gap in `IInv`).** Proved by induction on `iexec`, using `finish_call_source` and `ii_pool_active` at the return step. Records persist, and `ii_invs_nodup` gives uniqueness. Do not add a field to `IInv`, since `RelaxedHoareSound` and `BracketedLink` consume it.

```coq
Lemma iexec_over_res_rec q0 IT ic : iexec VE M (iinitial VE q0) IT ic ->
  forall p t h op ret, nth_error IT p = Some (IOver (Build_ThreadEvent t (@ResEv F h op ret))) ->
  exists r, In r (ic_invs VE ic) /\ ir_key r = (t, h) /\ @ResEv F h op ret = @ResEv F h (ir_op r) (ir_ret r).
```

**F4. Program trace shape.**

```coq
Lemma sbw_produces t c1 c2 tr (r : nat) : program_produces_tagged t (sbw c1 c2) tr r ->
  exists h1 h2 (r1 : nat) D1 D2, D2 h1 /\
   tr = [Build_TaggedEvent (Build_ThreadEvent t (@InvEv FC h1 (Inc c1))) D1;
         Build_TaggedEvent (Build_ThreadEvent t (@ResEv FC h1 (Inc c1) r1)) no_deps;
         Build_TaggedEvent (Build_ThreadEvent t (@InvEv FC h2 (Get c2))) D2;
         Build_TaggedEvent (Build_ThreadEvent t (@ResEv FC h2 (Get c2) r)) no_deps].
```

The proof uses stage lemmas modelled on `cc_trace` (`fut_view`/`wait_view`/`ret_match`, `stage_wait_pending`, `stage_wait_resolved`, `stage_ret`). It covers both `tagged_wait_pending` and `tagged_resolve` followed by `tagged_wait_resolved`. `program_terminal` requires `all_resolved`, so method traces are complete.

**F5. Returned implies all emitted.** If a record's call has an overlay `ResEv` in IT, every block entry is emitted (`ii_returned_done`, `ii_partition`, `ii_blocks`, `block_of_trace`).

**F6. Order.** `ii_order` on block ids `ir_start+1 < ir_start+2`. The pair (Res h1, Inv h2 tagged with `D2 h1`) satisfies `must_precede`, and the two events are on the same thread (`program_produces_tagged_trace_tid`), so `~ tagged_can_cross` holds. This yields p(Res inc) < p(Inv get) in IT. Prefer this to `module_dependency_soundness`, which identifies the response only by handle.

**F7. Position transfer (new).**

- `iunder IT` and `iover IT` (flat_map selections) and `ucount IT p` (underlay events before p).
- `underlay_events (map ierase IT) = iunder IT`, and the same for overlay.
- `nth_error IT p = Some (IUnder x) -> nth_error (iunder IT) (ucount IT p) = Some (untag (ts_event (snd x)))`.
- Monotonicity of `ucount`, and the converse `iunder_inv`.

**F8. `s_u` is complete.** For each underlay `Inv` in `s_u`:

- `emitted_source` gives its record;
- `ii_pos` puts the record's overlay `Inv` in s;
- `complete s` gives its overlay `Res`;
- F5 then gives the paired underlay `Res`, by F4's shape.

**F9 and F10.** `cc_trace_wf` gives wf of `s_u`. `cc_rel_lin` gives `rel_lin sel s_u by_counter (seq_legal δcxy s00)`.

**F11. Spec-only cycle lemma.**

```coq
Lemma sbw_cycle (L : list (ThreadEvent FC)) ka kb kc kd (ra rc : nat) i1 j1 jb i2 j2 jd :
  PrefixView.wf L -> RelaxedTraceLin.rel_lin PrefixView.sel L by_counter (RelaxedHoareSpec.seq_legal δcxy s00) ->
  res_at sel L i1 ka (Inc CX) ra -> inv_at sel L j1 kb (Get CY) -> i1 < j1 -> res_at sel L jb kb (Get CY) 0 ->
  res_at sel L i2 kc (Inc CY) rc -> inv_at sel L j2 kd (Get CX) -> i2 < j2 -> res_at sel L jd kd (Get CX) 0 -> False.
```

The proof is `sb_not_rel_lin0` with the res→inv clause of `rhb` instead of the same-thread clause:

- rhb gives inc_x < get_y and inc_y < get_x in W;
- legality (`seq_inc_get by_counter`) gives get_y < inc_y and get_x < inc_x;
- `before_idx` turns these into index inequalities, and `lia` closes the cycle.

Wf is used to identify ops and results of the witness entries. Results are compared via nat projections, as `sb_res_cases` does, to avoid `eq_rect_eq`. The lemma uses no SI at all: the Wait forbids (0,0) under every SI. Without the Wait, `sb_exec`/`sb_si_decides` show (0,0) is allowed under `by_counter`. That contrast is the reasoning principle to show Reviewer B.

**Reuse.** `seq_inc_get`, `seq_get_ge`, `before_idx`, `δcxy_mono` from `RelaxedHoareCounterXY` (Section SB, parameter `si`), plus `cc_trace`'s view technique.

### Non-vacuity (F12; strongly recommended)

- **`sbw_witness`.** A complete Psb execution over `MLTS (EI δmem) M_cxy` with outcome Main1 ↦ 0, Main2 ↦ 1. Build one sequential `M_cxy` execution in the `sb_exec` style; each TLTS step's membership then follows from `mtraces_prefix`.
- **`sbn_00` (contrast).** The no-Wait client `Future inc; Future get; Wait f; Wait g` reaches (0,0) over the same composite, reusing `sb_mtraces`. The early `Res g` comes via `tagged_resolve`.

### Risks for Item F

- **Dependent `Wait (MkFutureRef op h) k` inversion in F4.** Use views; otherwise accept `eq_rect_eq` and say so.
- **Position bookkeeping (F7, F8).**
- **Complete traces only.** `cc_rel_lin` is complete-only. A claim for prefixes would need the REW route, or reasoning inside copy-cat executions; deferred.
- **Prophecy.** Psb fixes its result at invocation. In complete traces the TLTS step has accepted the `Get` response value, so the value is the spec's.
- **No handle-linearity proof is needed.** Wf comes from `cc_trace_wf`.

### Effort for Item F

| Part | Lines | Time |
|---|---|---|
| F3 + F5 + F7 | 250–400 | 2–3 days |
| F4 | 150–300 | 1–2 days |
| F11 | 150–250 | 1 day |
| Assembly | 150–300 | 1–2 days |
| F12 | 300–600 | 2 days |

**Total critical path, including Item A:** about 1,100–1,800 lines, 8–12 working days.

---

## Writer-sized sub-tasks (in order)

1. **W1, `RelaxedHoareLink.v` part 1, plus a `_CoqProject` entry.**
   - Contents: `TLTS`, `MLTS`, `underlay_events`, `retag`, `tlts_mono`, `mtraces_nil`, `tlts_exec_state`, `link_mono`, `rcomplin_link`, `client_rule`.
   - Accept when: all Closed; header states "semantic linking only, no absorption, finite-trace fidelity argued".
2. **W2, same file, part 2.**
   - Contents: `iexec_over_res_rec`, `returned_emitted`, `iunder`/`iover`/`ucount` with `iunder_pos`/`iunder_inv`/`ucount_lt`, and `underlay_ierase`/`overlay_ierase`.
   - Accept when: Closed; `RelaxedModuleFacts.v` unchanged.
3. **W3, `RelaxedHoareCounterXYClient.v` part 1, plus a `_CoqProject` entry.**
   - Contents: `U`, `sbw`, `Psb`, `sbw_outcome00`, `sbw_produces`, `sbw_cycle`.
   - Accept when: `sbw_cycle` is Closed; `sbw_produces` is Closed, or uses `eq_rect_eq` only and documents it.
4. **W4, same file.**
   - Contents: `sbw_over_spec`, `sbw_client`.
   - Accept when: `Print Assumptions` shows only `classic` and `eq_rect_eq`; no CounterXY or Inherit edits; header has the K/S/P/R levels, including that the claim is for complete client runs and that the client proof is over `MLTS (EI δcxy) idF`.
5. **W5, same file.**
   - Contents: `sbw_witness`, `sbn_00`.
   - Accept when: Closed; built from `tagged_*` steps.
6. **W6 (optional), `RelaxedHoareLink.v` part 3.**
   - Contents: `ltraces`, `mtraces_tlts`, `mtraces_mono`, `cc_unit_left`.
7. **Deferred.**
   - W7: `absorb_cc_ei`, then `absorb_ei`.
   - W8: `rlhl_link`.
   - W9: m-8 (after an author answer).
   - W10: `link_joint`.

## Research-level points for the author

1. **Semantic vs syntactic layering.** `Prog` has no fork or substitution, so the composite is `MLTS`, an LTS rather than a module E→G. The paper's `M;N` is syntactic. Is TLTS linking acceptable as "vertical composition"? Is `link_joint` required before claiming it?
2. **Which premise the client claim uses.** The client claim's premise is over the copy-cat-saturated spec (`MLTS (EI δF) idF`). Composing an RLHL-verified upper layer needs the plain `EI δF`, i.e. absorption. The paper's saturation proposition (relaxedlin.tex:52-56) treats these as the same; the mechanization would need absorption to prove it.
3. **What absorption targets.** Options: `EI δ` (renaming-invariant for any key map), or a general `VF` under an explicit renaming-invariance hypothesis. `EIhl` is reached via `hlift`. The verimpl quantification "for every underlay rel-lin to ν" also needs the open M-20 converse.
4. **m-8.** Should the implementation-side no-misuse obligation (`ct_noerr`) be added? This has not been put to the author.
5. **Complete-run-only client claim.** Is a claim only for complete client runs (the "final outcome" reading) acceptable, or is a prefix version needed?
6. **Paper anchor for the client.** I found no printed client example in the paper for this SB-with-Wait client. Check `2Counter.tex` and `implex.tex` before claiming paper fidelity. The pattern comes from latest-review M-22 item 5.

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLin.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleFacts.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareCounterXY.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v