# RLHL-3c design, operational/simulation angle

## 0. What I checked in `rocq repl` (Rocq 9.3.0, nothing written to disk)

- **`ModLTS` typechecks, nested too.** `ModLTS (ModLTS VE M1) M2 : LTS G` is accepted. No universe problem showed up.
- **`mtraces_mono` is already a corollary of existing lemmas.** It takes five lines from `ViewLHL.exec_underlay_path` and `ViewLHL.exec_transport`. `Print Assumptions` reports "Closed under the global context". This is the "trace-determinedness" of M-22: `MTraces V M v` depends on `V` only through its path language from `v`.
- **`rcomplin_link` follows in four lines** from `mtraces_mono`, `modlts_paths` and `absorb`. I checked this with `absorb`, `modlts_paths` and `ei_ccclosed` declared as `Axiom`s. The `rlhl_link_ei` statement also typechecks.
- **General absorption is false for an arbitrary `VF`.** Two counterexamples:
  - *(R) handle-sensitive programs or LTSs.* Take `handle F = nat`, a `VF` that enables `InvEv` only on handle 0, and `M g := Future op (fun f => if future_handle f is 0 then Wait f (Ret 0) else Wait f (Ret 1))`. In the composite, M picks h = 5 and the inner `idF` picks h′ = 0, so the composite returns 1. M directly over `VF` never returns 1.
  - *(D) response-blocking LTSs.* The composite's prophetic result r_M can differ from the inner `idF`'s committed result r. The target then cannot emit that response, and a `VF` that blocks until a response arrives separates the two trace sets. This needs a careful example: the stuck call must have a non-semi-independent later invocation that blocks a second call.
  - So absorption needs a hypothesis `CCClosed VF v0`: paths closed under per-thread injective renaming of keys and under deleting responses. `EI δ` from `(s0,[])` satisfies both.
- **Why the (F2) frontier transfers.** For two invocations, `must_precede` is `~ semi_independent op1 op2`, whatever the tags. So `tagged_can_cross` is `~~SI` at both the M level and the inner-`idF` level, and the signature F is the same on both. An `idF` crossing therefore gives exactly the outer crossing.
- **What to reuse for absorption.** The instrumented semantics of `RelaxedModuleFacts` fits: `instrument`, `iinv_reach`, and the `IInv` fields `ii_no_overtake`, `ii_order`, `ii_used_nodup`. It solves queue-entry uniqueness and order agreement by event ids. The ghost/age-list machinery of `RelaxedHoareInherit` is not needed on this route.

## 1. `mtraces_mono` (file A: `models/simlin/RelaxedHoareLayer.v`)

**(1) Statements**
```coq
Definition LPaths {F} (V : LTS F) (v : State V) (u : list (ThreadEvent F)) : Prop :=
  exists v', vf_path V v u v'.
Theorem mtraces_mono {E F} (V1 V2 : LTS E) (M : RelaxedModuleImpl E F) v1 v2 :
  (forall u, LPaths V1 v1 u -> LPaths V2 v2 u) -> forall s, MTraces V1 M v1 s -> MTraces V2 M v2 s.
Proof. intros Hp s (evs & c & Hex & Hov).
  pose proof (exec_underlay_path M V1 _ _ _ Hex) as Hu.
  destruct (Hp _ (ex_intro _ _ Hu)) as (v2f & Hv2).
  destruct (exec_transport M V1 V2 _ _ _ Hex v2 v2f Hv2) as (d & Hd & _).
  exists evs, d. split; [exact Hd | exact Hov]. Qed.   (* checked: closed *)
```
Corollaries:
- `mtraces_ext` (the iff version);
- `rtraces_mono` (the case `M := idF`);
- `complin_mono_under : path inclusion V1→V2 -> RCompLin M V2 v2 VF w -> RCompLin M V1 v1 VF w`.

**(2)/(3) Strategy and reuse.** Done above, using `ViewLHL.exec_underlay_path`, `exec_transport`, `underlay_events` and `RelaxedGSim.vf_path`.

**(4) Risk:** none. **(5) Effort:** about 60 lines.

## 2. Module trace-LTS (file A)

**(1) Statements**
```coq
Definition mod_step {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) (ev : ThreadEvent F)
    (c c' : TaggedModuleConfig VE) : Prop :=
  exists us c1, module_execution_tagged VE M c (map (@UnderlayEvent E F) us) c1 /\
                module_step_tagged VE M (OverlayEvent ev) c1 c'.
Definition ModLTS {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) : LTS F :=
  {| State := @TaggedModuleConfig E F VE; Step := mod_step VE M; Error := fun _ _ => False |}.
Definition TrLTS {F} (T : list (ThreadEvent F) -> Prop) : LTS F :=
  {| State := list (ThreadEvent F); Step := fun e u u' => u' = u ++ [e] /\ T u'; Error := fun _ _ => False |}.
(* FreeLTS := TrLTS (fun _ => True) *)
Theorem modlts_paths {E F} VE (M : RelaxedModuleImpl E F) σ0 u :
  LPaths (ModLTS VE M) (initial_tagged_module VE σ0) u <-> MTraces VE M σ0 u.
Theorem trlts_paths {F} (T : list (ThreadEvent F) -> Prop) u :
  T [] -> (forall s1 s2, T (s1 ++ s2) -> T s1) -> (LPaths (TrLTS T) [] u <-> T u).
Corollary modlts_trlts {E F G} VE M1 σ0 (M2 : RelaxedModuleImpl F G) s :
  MTraces (ModLTS VE M1) M2 (initial_tagged_module VE σ0) s <-> MTraces (TrLTS (MTraces VE M1 σ0)) M2 [] s.
```

**(2) Strategy**
- `modlts_paths` (→): induction on `vf_path`, using an `exec_app` lemma (new, about 10 lines) and `overlay_events_app`.
- `modlts_paths` (←): induction on the events, accumulating the underlay prefix and cutting with `exec_app_inv`. Trailing underlay events are dropped.
- `modlts_trlts`: `mtraces_ext` with `mtraces_prefix`.

**(3) Reuse:** `exec_snoc`, `exec_app_inv`, `overlay_events_app`, `overlay_events_split`, `mtraces_prefix`.

**(4) Risk.** A `ModLTS` step bundles "underlay* then overlay". Inner steps that are pending at the end are invisible. That is harmless for overlay traces, but `unabsorb` has to defer inner steps (see §3).

**(5) Effort:** about 200 lines, under one Writer iteration.

## 3. Absorption: `idF` first, then general (file B: `models/simlin/RelaxedHoareAbsorb.v`)

**(1) Statements**
```coq
Definition rehandle {F} (h : handle F) (e : ThreadEvent F) : ThreadEvent F :=
  Build_ThreadEvent (te_tid F e) (match te_ev F e with InvEv _ o => InvEv h o | ResEv _ o r => ResEv h o r end).
Definition is_res {F} (e : ThreadEvent F) : Prop := match te_ev F e with ResEv _ _ _ => True | _ => False end.
Inductive ccimg {F} (Rk : CallKey F -> handle F -> Prop) : list (ThreadEvent F) -> list (ThreadEvent F) -> Prop :=
| ccimg_nil : ccimg Rk [] []
| ccimg_keep e h u u' : Rk (te_key e) h -> ccimg Rk u u' -> ccimg Rk (e :: u) (rehandle h e :: u')
| ccimg_drop e u u' : is_res e -> ccimg Rk u u' -> ccimg Rk (e :: u) u'.
Definition CCClosed {F} (V : LTS F) (v0 : State V) : Prop :=
  forall Rk u u', (forall k h1 h2, Rk k h1 -> Rk k h2 -> h1 = h2) ->
    (forall k1 k2 h, Rk k1 h -> Rk k2 h -> fst k1 = fst k2 -> k1 = k2) ->
    LPaths V v0 u -> ccimg Rk u u' -> LPaths V v0 u'.
Lemma ei_ccclosed {F St} δ (s0 : St) : CCClosed (@RelaxedHoareSpec.EI F St δ) (s0, []).
Theorem unabsorb {F G} (VF : LTS F) v0 (M : RelaxedModuleImpl F G) s :
  MTraces VF M v0 s -> MTraces (ModLTS VF idF) M (initial_tagged_module VF v0) s.
Theorem absorb_idF {F} (VF : LTS F) v0 : CCClosed VF v0 ->
  forall s, RTraces (ModLTS VF idF) (initial_tagged_module VF v0) s -> RTraces VF v0 s.   (* cc;cc ⊆ cc *)
Theorem absorb {F G} (VF : LTS F) v0 (M : RelaxedModuleImpl F G) : CCClosed VF v0 ->
  forall s, MTraces (ModLTS VF idF) M (initial_tagged_module VF v0) s -> MTraces VF M v0 s.
Corollary saturate_ei : MTraces (EI δ) M (s0,[]) s <-> MTraces (ModLTS (EI δ) idF) M (initial_tagged_module _ (s0,[])) s.
Corollary cc_idem_ei : RTraces (ModLTS (EI δ) idF) (...) s <-> RTraces (EI δ) (s0,[]) s.
```

**(2) Strategy: a forward simulation from the composite to a target**
- The composite is M over `ModLTS VF idF`. Instrument the outer M with `instrument`/`iinv_reach` over `VE := ModLTS VF idF`. The inner `idF` config is `ic_state ic`.
- The target is a plain execution of M over `FreeLTS`. It copies the outer prophecies and is then moved to `VF` with `exec_transport`, along `vf_path VF v0 uT`. That path comes from `CCClosed` applied to the composite inner path `uC`.
- **Target steps.** G-invocations and G-returns are copied, with the same pool, used list and trace. On an inner `idF` emission:
  - inner `inv (t,h')` ⇒ the target emits M's `inv (t,h)`;
  - inner `res (t,h') r` ⇒ the target emits M's `res (t,h) r_M` if `ResEv h op r = ResEv h op r_M`, and otherwise skips (`ccimg_drop`). Values are compared through events, not values, to avoid `eq_rect_eq`.
  - When M emits an F-event into `ModLTS`, the target does nothing; only bookkeeping changes.
- **Invariant `AbsInv IT ic T QTi Pairs uC`:**
  - `IInv (ModLTS VF idF) M IT ic`;
  - `tm_calls T = ic_calls ic` and `tm_used_underlay T = ic_used ic`;
  - `tm_queue T = map snd QTi`, with `QTi` sorted by id and contained in `ic_log ic`;
  - a three-way status of each log entry: composite-pending; composite-emitted but target-pending (only invocations, whose inner `ient`-shaped entry is in the `idF` queue); target-emitted but composite-pending (only responses whose inner response matched);
  - the QI-order field: for composite-emitted, target-pending invocations, composite emission order equals order in the inner queue (`RelaxedTraceLin.before`);
  - the inner `idF` shape, via `cc_trace`: owner (t,h), inner handle h′, `(t,h') ↦ (t,h)` recorded in `Pairs`, which is NoDup on both sides;
  - `vf_path VF v0 uC (tm_lts_state (ic_state ic))`;
  - `ccimg (fun k h => In (k,(fst k,h)) Pairs) uC (tm_lts_state T)`.
- **Frontier obligations** (target selection via `select_of_cross`):
  - Earlier composite-pending entries: crossable by `ii_no_overtake`.
  - An earlier composite-emitted, target-pending y (same thread, assume `must_precede y x`): `ii_order` puts y's composite emission before x's; QI-order puts the inner y before the inner x; `idF`'s crossing gives `~~SI`, a contradiction. The proof is constructive.
  - (F3): if x's tag names h1, the composite emitted `res(h1)` before x. That emission is an `idF` return, so the inner response came first, so the target already emitted `res(h1)`.
  - (F1): the target's `res(t,h)` is blocked only by `inv(t,h)`, which was target-emitted at the inner invocation. Key uniqueness comes from `ii_used_nodup`.
- **G-return.** Composite `owner_done` gives target `owner_done`. This needs a new local-trace lemma `produced_inv_answered`: every invocation of a produced trace is later answered with the same handle and op. If the call's response was composite-emitted, the `idF` call is dead and its inner events are done.
- **Pilot `absorb_idF`:** the same proof with M's traces read off `cc_trace` (tags empty, so (F3) is trivial). Then generalise.
- **`unabsorb`:** the inner `idF` uses handle h′ := h (fresh, because M's keys are) and commits r_M, taken from M's own trace via `produced_inv_answered`. So no `classic` is needed. Each inner invocation is deferred into the prefix of the next `ModLTS` step. The inner frontier is trivial (`idF` tags are empty).
- **`ei_ccclosed`:** induction on the path. The relation between EI states is: same `fst`, and the pending list is a permutation of `map rekey(P) ++ extra`. `extra` holds the records of dropped responses.

**(3) Reuse:** `cc_trace`, `idF_produces`, `cc_inv_ev`, `cc_res_ev`, `ient`, `rent`, `select_of_cross`, `select_frontier_tagged_split`, `instrument`, `IInv`, `produced_response_invoked`, `local_inv_unique`, `exec_transport`, `rekey`, `RelaxedHoareSpec.vf_path_app_inv`.

**(4) Risks**
- the (F1)–(F3) mapping above;
- duplicate queue entries (solved by ids);
- `DeadCall`s persisting in the `idF` pool (fine: `call_fresh` uses M's keys);
- prophetic mismatch (`ccimg_drop`);
- `trace_fresh` / `tm_used_underlay` copied verbatim;
- `ccimg` is cons-based while paths are built by snoc (needs a snoc lemma);
- dependent `ResEv` equalities.

**(5) Effort**
- `ei_ccclosed` + `CCClosed`: about 250 lines, 1 iteration.
- `unabsorb`: about 500 lines, 1–2 iterations.
- `absorb_idF`: about 900 lines, 2 iterations.
- generalisation: about 400 lines, 1–2 iterations.

## 4. Semantic linking/layering (file C: `models/simlin/RelaxedHoareLink.v`)

**(1) Statements**
```coq
Theorem link_under {E F G} VE σ0 (M1 : RelaxedModuleImpl E F) VF v0 (M2 : RelaxedModuleImpl F G) s :
  CCClosed VF v0 -> RCompLin M1 VE σ0 VF v0 ->
  MTraces (ModLTS VE M1) M2 (initial_tagged_module VE σ0) s -> MTraces VF M2 v0 s.
Theorem rcomplin_link {E F G} (VE : LTS E) (σ0 : State VE) (M1 : RelaxedModuleImpl E F) (VF : LTS F) (v0 : State VF)
    (M2 : RelaxedModuleImpl F G) (VG : LTS G) (w0 : State VG) :
  CCClosed VF v0 -> RCompLin M1 VE σ0 VF v0 -> RCompLin M2 VF v0 VG w0 ->
  RCompLin M2 (ModLTS VE M1) (initial_tagged_module VE σ0) VG w0.
Proof. intros Hcc H1 H2 s Hs. apply H2. apply (absorb VF v0 M2 Hcc). revert s Hs. apply mtraces_mono.
  intros u Hu. apply (proj2 (modlts_paths VF idF v0 u)). apply H1.
  apply (proj1 (modlts_paths VE M1 σ0 u)). exact Hu. Qed.     (* checked against the axiomatised pieces *)
Corollary rlhl_link_ei {E F G StE StF StG} δE δF δG (sE:StE) (sF:StF) (sG:StG) M1 M2 I1 R1 G1 I2 R2 G2 :
  RLHL2Hyps (VE := EIhl δE) (VF := EI δF) I1 R1 G1 M1 ((sE,[]),[]) (sF,[]) ->
  RLHL2Hyps (VE := EIhl δF) (VF := EI δG) I2 R2 G2 M2 ((sF,[]),[]) (sG,[]) ->
  RCompLin M2 (ModLTS (EI δE) M1) (initial_tagged_module (EI δE) (sE,[])) (EI δG) (sG,[]).
(* proof: apply (rcomplin_link _ _ _ (EI δF) (sF,[])); ei_ccclosed; rlhl_complin_eihl twice *)
```
Also:
- `rcomplin_link_trlts`: the same conclusion over `TrLTS (MTraces VE M1 σ0)`;
- towers: apply `rcomplin_link` with `VE := ModLTS VE M1`;
- a non-vacuity test: a renaming layer (via `ren_rlhl2`) on top of `cxy_rlhl2`.

**EIhl vs EI.** EIhl never needs to be absorbed. Layer 2's EIhl verification is converted to EI by `rlhl_complin_eihl` / `complin_hlift_under`, and absorption happens at the EI middle interface.

**Effort:** about 150 lines, half an iteration.

## 5. m-8: implementation-side error obligation (new files E/F/G)

**(1) Statements** (file E: `models/simlin/RelaxedHoareCompLinErr.v`)
```coq
Variant TItem (F : RelaxedSig.t) : Type := TEv (ev : ThreadEvent F) | TErr (k : CallKey F) (op : Sig.op (RelaxedSig.effect F)).
Inductive module_error_tagged {E F} (VE : LTS E) : CallKey F -> @TaggedModuleConfig E F VE -> Prop :=
| tagged_error cand q pool queue queue' used (Hselect : select_frontier_tagged cand queue queue')
    (Herror : Error VE (untag (ts_event cand)) q) :
    module_error_tagged VE (ts_owner cand) (Build_TaggedModuleConfig q pool queue used).
Definition MTracesE {E F} VE (M : RelaxedModuleImpl E F) σ0 (s : list (TItem F)) : Prop :=
  exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\
   (s = map (@TEv F) (overlay_events evs) \/
    exists k op ret, module_error_tagged VE k c /\ In (Build_CallEntry (fst k) (snd k) (@ActiveCall F op ret)) (tm_calls c) /\
                     s = map (@TEv F) (overlay_events evs) ++ [TErr k op]).
Definition RTracesE {F} V v := MTracesE V (@idF F) v.
Definition RTracesClosed {F} (V : LTS F) v s := RTracesE V v s \/ exists p k op tl, RTracesE V v (p ++ [TErr k op]) /\ s = p ++ tl.
Definition RCompLinErr {E F} M VE σ0 VF v0 := forall s, MTracesE VE M σ0 s -> RTracesClosed VF v0 s.
Definition EIe {F St} δ : LTS F := {| State := St * list (Op F); Step := RelaxedHoareSpec.ei_step δ;
  Error := fun ev s => match te_ev F ev with InvEv _ o => ~ exists r s', δ (fst s) o r s' | _ => False end |}.
Definition GSimRelErr VE VF M S := forall c p, S c p ->
  (forall k, module_error_tagged VE k c -> poss_steps VF p PossError) /\ gsim_step VE VF M S c p.
Theorem gsim_complin_err : GSimRelErr VE VF M S -> S (initial_tagged_module VE σ0) (PossOk v0 []) -> RCompLinErr M VE σ0 VF v0.
```
Inclusion lemmas:
- `rcomplin_err_of_rcomplin` (when `VE` has no errors);
- `rcomplin_of_err` (when neither side has errors);
- `rtraces_ei_eie`;
- `gsim_err_of_gsim`;
- `closed_absorb_r` (port of `CompLinVComp.closed_absorb`).

RLHL side (file F: `models/simlin/RelaxedHoareErrRLHL.v`):
```coq
Record CallTripleE k op ret A : Prop := { cte_triple : CallTriple I R G k op ret A;
  cte_noerr : forall pre m post, local_frontier pre m -> forall σ p γ, A (pre ++ m :: post) (σ,p,γ) -> I (σ,p,γ) ->
              Error VE (untag m) σ -> poss_steps VF p PossError }.
```
Plus `MethodSemE`, `CallSafeE` (coinductive, adds a no-error field), `RLHL2HypsE` (with `rlhl2_of_err` and `rlhl2_err_of_noerr`), `rlhl_gsim_err` and `rlhl_complin_err`.

**(2) Strategy**
- **`gsim_complin_err`.** Re-prove `rinv_step`/`rinv_exec`; they use `GSimRel` only at the current config and for the successor's `PossOk`. At the final config, take the error clause, then `poss_steps_prun` up to the error step.
- **`reify_err`.** Copy the `Reify` section. The frontier part of `step_ainv` becomes a lemma `ient_selectable`, fed by `lin_invocation_enabled` instead of `TValid`. The `ActiveCall` entry for the `TErr` op comes from `ci_act`.
- **`rlhl_gsim_err`.** Like `rsim_underlay`: the error candidate goes through `select_project` to its owner's local frontier, and then `cte_noerr` applies.
- **Lock example** (file G: `examples/Relaxed/RelaxedHoareLockErr.v`):
  - `m8_gap`: the review's `acquire; release; release` has `RLHL2Hyps` over `EIhl δlock` (the second release blocks), but `~ RCompLinErr` into an error-free `EIe δG`;
  - a positive `ren_rlhl2_err`: the renaming copy-cat plus `Hδerr` (no δE successor of `ρ o` ⇒ no δF successor of `o`), discharged with `emit_ready_SI` and `psa_inv_error`.

**(4) Risks**
- `module_error_tagged` does not exist yet; only a positional `module_error` exists.
- Showing the owner is active needs `owners_active_reachable`.
- `CallSafe` duplication.
- `psa_ret_error` for a generic `VF`.

**(5) Effort**
- definitions: about 300 lines, 1 iteration;
- `gsim_complin_err`: about 600 lines, 2 iterations;
- RLHL side: about 800 lines, 2–3 iterations;
- lock example: about 600 lines, 2 iterations;
- layering with errors (`ModLTSE`, absorption with errors, `link_err`): over 1000 lines, a stretch goal.

## 6. Client of Counter_xy (file D: `examples/Relaxed/RelaxedHoareSBClient.v`)

**(1) Statements**
```coq
Inductive SBOp := SB (c : CLoc).   (* Sig.ar := nat; GS: handle nat, SI ∅, mode Local *)
Definition other c := match c with CX => CY | CY => CX end.
Definition Mcl : RelaxedModuleImpl FC GS := fun o _ => match o as o0 return Prog FC (Sig.ar o0) with
  | SB c => Future (Inc c) (fun f => Wait f (fun _ => Future (Get (other c)) (fun g => Wait g (fun r => Ret r)))) end.
Theorem sb_client_spec s k1 k2 : MTraces (EI δcxy) Mcl (s00, []) s ->
  In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s ->
  In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False.
Corollary sb_client_impl s k1 k2 :
  MTraces (ModLTS (EI δmem) M_cxy) Mcl (initial_tagged_module (EI δmem) (s00, [])) s -> (same two Ins) -> False.
  (* = link_under _ _ M_cxy _ _ Mcl s (ei_ccclosed δcxy s00) cxy_complin_ei, then sb_client_spec *)
Theorem sb_nowait_00 : exists s k1 k2, MTraces (EI δcxy) Mnw (s00, []) s /\ (both return 0).
  (* Mnw: FutureD (Get ..) no_deps without the intermediate Wait *)
```

**(2) Strategy (uses the spec only)**
- `mcl_trace`, in the view style of `cc_trace`: the trace is inv(a) with empty tag, res(a), inv(b) whose tag contains a, res(b) r.
- Instrument the execution. `ii_order` gives (F1) and (F3), so in the EI path u: inv(a) < res(a) < inv(b).
- EI value lemmas: with unique keys (`ii_used_nodup`), a response with value r was decided by δ at its invocation, and counter c at a position equals the number of earlier `Inc c` invocations.
- If both results are 0: inv(a) < inv(b) < inv(c) < inv(d) < inv(a), a cycle.
- The same-thread case is closed by (F2): `Inc x` and `Get x` are not `by_counter`-SI.

**Effort:** about 900 lines, 2–3 iterations. `sb_client_spec` can start immediately; `sb_client_impl` needs §4.

## 7. Writer-sized sub-tasks (acceptance for all: builds under 9.3.0, `_CoqProject` updated, no `Admitted`, `Print Assumptions` as stated, header lists results and axioms)

| Task | Content | Files | Accept when |
|---|---|---|---|
| T1 | `LPaths`, `mtraces_mono`/`ext`, `ModLTS`, `TrLTS`, `modlts_paths`, `trlts_paths`, `modlts_trlts`, `exec_app` | A | all closed |
| T2 | `rehandle`, `ccimg` (+snoc lemma), `CCClosed`, `ei_ccclosed`; optional mechanised (R) counterexample | B | closed |
| T3 | `produced_inv_answered` (in B, not in `RelaxedModuleFacts`), `unabsorb` | B | closed |
| T4 | `AbsInv`, step lemmas, `absorb_idF`, `cc_idem_ei` | B | closed |
| T5 | general `absorb`, `saturate_ei` | B | closed |
| T6 | `link_under`, `rcomplin_link`, `_trlts`, towers, `rlhl_link_ei`, renaming-tower test | C | `rlhl_link_ei` axioms ⊆ those of `rlhl_complin_eihl` (`classic`) |
| T7a | `GS`, `Mcl`, `mcl_trace`, EI lemmas, `sb_client_spec`, `sb_nowait_00` | D | closed |
| T7b | `sb_client_impl` | D | only `classic` (via `cxy_complin_ei`) |
| T8 | `TItem`, `module_error_tagged`, `MTracesE`…`RCompLinErr`, `EIe`, inclusions, `closed_absorb_r` | E | closed |
| T9 | `GSimRelErr`, `reify_err`, `gsim_complin_err` | E | `classic` only |
| T10 | `CallTripleE`, `CallSafeE`, `RLHL2HypsE`, `rlhl_gsim_err`, `rlhl_complin_err` | F | only after the author decides R5 |
| T11 | `δlock`, `m8_gap`, `ren_rlhl2_err` + instance | G (+ a new `RelaxedHoareInheritErr.v`) | `m8_gap` proves both halves |
| T12 | `ModLTSE`, absorption with errors, `link_err` (stretch) | new | research decision R6 first |

- **Critical path for M-22 plus the client:** T1 → T2 → T4 → T5 → T6 → T7b, with T3 and T7a in parallel. That is about 3,300 lines and 9–11 iterations.
- **m-8 (T8–T11):** about 2,300 lines and 7–8 iterations.

## 8. Research-level points for the author

- **R1 — semantic vs syntactic layering.** Layering is semantic: M2 over `ModLTS`/`TrLTS` of M1. `RelaxedLang` has no substitution, so there is no `M1 ▷ M2`. Is this the paper's ⟦M2⟧∘⟦M1⟧?
- **R2 — absorption needs `CCClosed`.** It is false for a general `VF`, so linking works only through specification-like middle interfaces (EI, EIhl). Confirm this matches the M-20 layering.
- **R3 — EIhl vs EI.** This is bookkeeping, not research: `hlift` plus `mtraces_mono`. State everything over EI.
- **R4 — which half of saturation.** Only the E-side half (`absorb`/`unabsorb`) is planned. The F-side half (⟦M⟧;cc_F ⊆ ⟦M⟧) is not. Does prop:rlhl-sc need it?
- **R5 — shape of the m-8 obligation** (not yet put to the author). Two choices:
  - the licensed `cte_noerr` (an implementation error must be matched by a reachable abstract `PossError`) rather than a strict "no error";
  - a conjunction-form `GSimRelErr` (keep simulating after misuse; no `classic`) rather than the SC `ErrorCore` escape.
- **R6 — errors in layering.** How `ModLTSE` attributes a TErr when M1 errs internally, and whether layering with errors is in RLHL-3c at all.
- **R7 — form of client verification.** Here it is a trace property of the whole stack, proved over the spec. The alternative is an RLHL triple for the client into a nondeterministic SB spec.

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLin.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleFacts.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/view/ViewLHL.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v