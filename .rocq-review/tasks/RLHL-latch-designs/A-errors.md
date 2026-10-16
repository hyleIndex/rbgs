# Plan (A): error infrastructure for RLHL (m-8, implementation-side obligation)

## 0. Bottom line

**Recommended route.** Keep the user-facing semantics close to SC LHL/CompLin:
- a spec error is `PossError`, and `PossError` absorbs (D5 vi);
- an implementation error must be licensed by a reachable `PossError` (D5 iii, licensed form);
- `TErr` is tagged with `(key, op)` (D5 iv);
- `EIe` has an explicit `bad` predicate over the whole EI state and the tid (D5 ii).

**Soundness proof.** A **simulation that stops at the first abstract error** (`GSimRelErr`). The final abstract error step is replayed through an internal **sink LTS** `Sink VF`, in which `Error` becomes a step to `None`. That lets the existing `rinv_ainv`/`rinv_aret`, `reify_step`/`CInv` and `rinv_val` do the frontier work unchanged.

**What changes and what does not.**
- No existing file is edited.
- All rules, `RProvable`, `walk`/`close_sound`/`fam_*` and the whole `RelaxedGSim` invariant machinery are reused unchanged.
- Four things must be copied and adapted, because `RetCond`, `h_ok` and "no error" are hard-wired:
  - the per-call triple and its coinductive packaging;
  - the RLHL→GSim bridge (`RSim`/`rsim_*`);
  - `rinv_step`/`rinv_exec`, about 35 lines;
  - `method_sound`/`ctx_triple`, about 70 lines.

**Rejected reductions** (§6):
- **Blocking.** It is incomplete: LatchSet's bad inserts return.
- **Chaos state in VF, reusing `rlhl_gsim`/`gsim_complin` verbatim.** This is unsound as a generic translation. A call linearized `ls_linr op r'` before the error may later return `ret ≠ r'`, and a chaotic `GSimRel` cannot match that return.

**Effort.** About 1,900–2,700 lines for A1–A4, plus A5 (the LatchSet spec layer, about 600–900). Roughly 6–8 Writer iterations in total.

## 1. Facts checked in the source (Rocq 9.3.0, piped `rocq repl`, read-only)

**Module semantics and possibilities**
- `module_step_tagged` has no error rule. The only error rules are the positional `module_error`/`module_error_at` (`RelaxedModuleSemantics.v:460-480`).
- `Poss` has `PossError`, with `psa_inv_error` (needs `lin_invocation_enabled`) and `psa_ret_error` (`RelaxedPossibility.v:554-565`).
- `poss_steps_from_error` exists, so `PossError` is absorbing.
- `gsim_step` requires `PossOk` (`RelaxedGSim.v:340`).

**Lemmas whose proof bodies get copied**
- `rinv_step` uses only `gsim_step S c p` at the current configuration. Its 35-line body uses only exported lemmas: `poss_invoke_ok_inv`, `rinv_cinv`, `poss_steps_prun`, `rinv_prun`, `poss_return_inv`, `rinv_cret`.

**Signatures that can be instantiated at any `VF`, including `Sink VF`**
- `RInv : ∀ {F} (VF : LTS F), State VF → list (PStep F) → CallPool F → State VF → LinPool F → Prop`.
- `rinv_ainv`/`rinv_aret`/`rinv_prun`/`rinv_val`.
- `reify_step` (takes `HP HV Hwf Hauinv Hau Hval` explicitly), `CInv` (field `ci_path`), `cinv_init`.
- `owners_active_reachable` (generic in `VE`, `M`).
- `StepMatch {E F} {VF}`, `vf_path {F} VF`, `prun {F} VF`, `proj {E F} {VE VF}`.

**State exposure.** `reify`/`reify_loop` do not expose the final state, so the final-state version must be re-proved from `reify_step`. That is about 25 lines.

**RLHL hard-wiring**
- `ctx_triple` takes `Hret : … → RetCond …` and produces `CallTriple`.
- `fam_emit`, `fam_stable`, `fam_return`, `fam_init`, `walk`, `w_init`, `w_invs`, `rp_unfold`, `close_sound` are all exported.
- `MethodProvable.mp_ret` is typed `RetCond`.
- Instances obtain `h_sem` through `method_sound`, so the syntactic route must keep working.

**SC precedent**
- `TPSimulationSet`: `HeadError` (the abstract side can reach error, so the simulation stops), or `tpsim_noerror`.
- `RGILogic`: `Herror` (strict no-error) and `Hperror` (`Punsafe ⇒ P ∨ APError`).
- The licensed form below generalises the strict one.

**`HL` lifts `Error` pointwise:** `Error (HL V) ev σ = Error V ev (fst σ)` (`RelaxedHoareCompLinSpec.v:987`). See §7.

**Names.** None of the proposed new names occurs anywhere in `models/`, `examples/` or `memory/`.

## 2. A1 — `models/simlin/RelaxedHoareErrSpec.v` (trace-level definitions)

```coq
Module RelaxedHoareErrSpec.
Variant TItem (F : RelaxedSig.t) : Type :=
| TEv (e : ThreadEvent F)
| TErr (k : CallKey F) (op : Sig.op (RelaxedSig.effect F)).

(* Tagged error rule: a frontier candidate whose event is an Error of VE;
   tagged with the owner call's key and overlay op (D5 iv). *)
Inductive module_error_tagged {E F : RelaxedSig.t} (VE : LTS E) :
    CallKey F -> Sig.op (RelaxedSig.effect F) -> @TaggedModuleConfig E F VE -> Prop :=
| tagged_error (cand : TaggedScheduledEvent E F) (op : Sig.op (RelaxedSig.effect F)) (ret : Sig.ar op)
    q pool queue queue' used
    (Hsel : select_frontier_tagged cand queue queue')
    (Hact : In (Build_CallEntry (fst (ts_owner cand)) (snd (ts_owner cand)) (ActiveCall op ret)) pool)
    (Herr : Error VE (untag (ts_event cand)) q) :
    module_error_tagged VE (ts_owner cand) op (Build_TaggedModuleConfig q pool queue used).

Definition MTracesE {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) (s : list (TItem F)) : Prop :=
  exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\
    (s = map TEv (overlay_events evs) \/
     exists k op, module_error_tagged VE k op c /\ s = map TEv (overlay_events evs) ++ [TErr k op]).
Definition RTracesClosed {F} (VF : LTS F) (v : State VF) (s : list (TItem F)) : Prop :=
  MTracesE VF idF v s \/ exists p k op tl, MTracesE VF idF v (p ++ [TErr k op]) /\ s = p ++ tl.
Definition RCompLinErr {E F} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE) (VF : LTS F) (v0 : State VF) : Prop :=
  forall s, MTracesE VE M σ0 s -> RTracesClosed VF v0 s.
Definition Licensed {F} (VF : LTS F) (v : State VF) (s : list (ThreadEvent F)) : Prop :=
  exists p k op tl, MTracesE VF idF v (p ++ [TErr k op]) /\ map TEv s = p ++ tl.

Section EIe.
  Context {F : RelaxedSig.t} {St : Type}
          (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop)
          (bad : St * list (Op F) -> tid -> Sig.op (RelaxedSig.effect F) -> Prop).
  Definition eie_error (ev : ThreadEvent F) (s : St * list (Op F)) : Prop :=
    match te_ev F ev with InvEv _ o => bad s (te_tid F ev) o | ResEv _ _ _ => False end.
  Definition EIe : LTS F :=
    {| State := (St * list (Op F))%type; Step := RelaxedHoareSpec.ei_step δ; Error := eie_error |}.
  Definition EIhle : LTS F := RelaxedHoareCompLinSpec.HL EIe.
End EIe.
```

**Design notes**
- **`EIe.Step` is exactly `ei_step δ`.** Steps at bad invocations are not removed. Under the closure this makes no difference, and the error-free part of `EIe` is literally `EI δ`.
- **`bad` instead of `pre`.** It is positive, so it needs neither negation nor decidability. The author may prefer `pre` with `Error := ~pre`, which is equivalent under `classic`.

**Lemmas (all expected Closed except the last)**
- `mtraces_in_mtracesE : MTraces VE M σ0 s -> MTracesE VE M σ0 (map TEv s)`.
- `rtraces_closed_of_rtraces : RTraces VF v s -> RTracesClosed VF v (map TEv s)`.
- `rtraces_closed_split : RTracesClosed VF v (map TEv s) -> RTraces VF v s \/ Licensed VF v s`. Proof: list lemmas; `TEv ≠ TErr`; `map TEv` is injective.
- `rcomplin_err_of_rcomplin : (forall ev q, ~ Error VE ev q) -> RCompLin M VE σ0 VF v0 -> RCompLinErr M VE σ0 VF v0`.
- `rcomplin_of_err : (forall ev q, ~ Error VF ev q) -> RCompLinErr M VE σ0 VF v0 -> RCompLin M VE σ0 VF v0`. A copy-cat `TErr` needs `Error VF`.
- `hliftE : MTracesE VE M σ0 s <-> MTracesE (HL VE) M (σ0, []) s`.
  - It reuses `lift_exec`, `drop_exec`, `lift_cfg`, `drop_cfg` unchanged.
  - The error part is a one-step transport: same queue and pool, and `Error (HL VE) ev (q,u)` is `Error VE ev q` by conversion.
  - Corollary `complinE_hlift_under`.
- `mtraces_eie_ei {G} (M : RelaxedModuleImpl F G) σ s : MTraces (EIe δ bad) M σ s <-> MTraces (RelaxedHoareSpec.EI δ) M σ s`. The steps are convertible; the configurations are transported by induction (about 30 lines).
- **Error-free corollary** (axioms {`eq_rect_eq`, `classic`}, inherited from `cc_rel_lin`):

```coq
Theorem complin_err_rel_lin {E F St} δ bad (s0 : St) (M : RelaxedModuleImpl E F) (VE : LTS E) σ0 :
  RCompLinErr M VE σ0 (EIe δ bad) (s0, []) ->
  forall s, MTraces VE M σ0 s -> PrefixView.complete s -> ~ Licensed (EIe δ bad) (s0, []) s ->
  rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δ s0).
```

Proof: `mtraces_in_mtracesE`, then `rtraces_closed_split`, then `mtraces_eie_ei`, then `RelaxedHoareCompLinSpec.cc_rel_lin`.

## 3. A2 — `models/simlin/RelaxedHoareGSimErr.v` (the stop-at-first-error core)

```coq
Section GSimErr.
  Context {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) (M : RelaxedModuleImpl E F).
  Abbreviation Cfg := (@TaggedModuleConfig E F VE).
  Definition gsim_step_err (S : Cfg -> Poss VF -> Prop) (c : Cfg) (p : Poss VF) : Prop :=
    (exists v pool, p = PossOk v pool) /\
    (forall k op, module_error_tagged VE k op c -> poss_steps VF p PossError) /\   (* impl obligation, licensed *)
    (forall t h op c', module_step_tagged VE M (OverlayEvent (Build_ThreadEvent t (@InvEv F h op))) c c' ->
       exists p', poss_invoke VF t h op p p' /\ S c' p') /\
    (forall ev c', module_step_tagged VE M (UnderlayEvent ev) c c' ->
       poss_steps VF p PossError \/ exists p', poss_steps VF p p' /\ S c' p') /\
    (forall t h op (ret : Sig.ar op) c',
       module_step_tagged VE M (OverlayEvent (Build_ThreadEvent t (@ResEv F h op ret))) c c' ->
       poss_steps VF p PossError \/
       exists p' p'', poss_steps VF p p' /\ poss_return VF t h op ret p' p'' /\ S c' p'').
  Definition GSimRelErr (S : Cfg -> Poss VF -> Prop) : Prop := forall c p, S c p -> gsim_step_err S c p.
End GSimErr.

Lemma gsimerr_of_gsim : (forall ev q, ~ Error VE ev q) -> GSimRel VE VF M S -> GSimRelErr VE VF M S.
Theorem gsim_complin_err (S : TaggedModuleConfig VE -> Poss VF -> Prop) σ0 v0 :
  GSimRelErr VE VF M S -> S (initial_tagged_module VE σ0) (PossOk v0 []) -> RCompLinErr M VE σ0 VF v0.
```

`gsim_step_err` is equivalent to the plan's "p' may be PossError", but `S` only ever relates `PossOk` states.

### Helper lemmas, in proof order

**1. `poss_steps_error_split`**

```coq
poss_steps VF (PossOk v pool) PossError ->
exists evs v1 pool1 k,
  prun VF (PossOk v pool) evs (PossOk v1 pool1) /\
  poss_step_at VF k (PossOk v1 pool1) PossError
```

Proof: right induction via `clos_rt_rtn1`, then `poss_steps_prun`.

**2. Two pool lemmas**
- `lin_invoke_update_of_enabled`: the converse of `lin_invocation_enabled → ∃ pool', lin_invoke_update`. The existing `lin_invoke_update_enabled` goes the other way.
- `lin_update_of_lookup`: from `wf` and `lin_lookup k b pool`, `∃ pool', lin_update k b a pool pool'`. Modelled on `lin_remove_exists`.

**3. The sink LTS (internal)**

```coq
Definition Sink {F} (V : LTS F) : LTS F :=
  {| State := option (State V);
     Step := fun ev s s' => match s, s' with
              | Some v, Some v' => Step V ev v v' | Some v, None => Error V ev v | None, _ => False end;
     Error := fun _ _ => False |}.
```

It comes with `vf_path_sink` and `rinv_sink : RInv VF v0 run calls v pool -> RInv (Sink VF) (Some v0) run calls (Some v) pool`. Only `ri_path` changes; the other 20 fields never mention `VF`.

**4. `rinv_reify_to`**

```coq
RInv VF v0 run calls v pool ->
exists evs cf,
  module_execution_tagged VF idF (initial_tagged_module VF v0) evs cf /\
  overlay_events evs = conc run /\ tm_lts_state cf = v
```

Re-prove `reify_loop` from the exported `reify_step`/`cinv_init`. The base case reads the final state from `ci_path` with `abs [] = []`.

**5. `sink_proj_exec` and `sink_split`**

```coq
module_execution_tagged (Sink VF) idF (initial_tagged_module (Sink VF) (Some v0)) evs cf ->
tm_lts_state cf = None ->
exists evs1 c1 k op tl,
  module_execution_tagged VF idF (initial_tagged_module VF v0) evs1 c1 /\
  module_error_tagged VF k op c1 /\ overlay_events evs = overlay_events evs1 ++ tl
```

- Split at the first step into `None`. `None` has no steps, so the prefix stays in `Some`.
- Project the prefix to `VF`.
- `Hact` comes from `owners_active_reachable VF idF` on the projected prefix.

**6. `rinv_licensed`**

```coq
RInv VF v0 run calls v pool -> poss_steps VF (PossOk v pool) PossError ->
exists p k op tl, MTracesE VF idF v0 (p ++ [TErr k op]) /\ map TEv (conc run) = p ++ tl
```

1. Apply item 1, then `rinv_prun`.
2. Apply `rinv_sink`.
3. Take the final error step as `rinv_ainv` or `rinv_aret` over `Sink VF`, whose target state is `None` (item 2 supplies the pool update).
4. Apply `rinv_reify_to` over `Sink VF`, then `sink_split`.

`conc` of abstract steps is `[]`.

**7. `rinv_match`**

```coq
RInv VF v0 run (tm_calls c) v pool -> module_step_tagged VE M ev c c' ->
StepMatch ev (PossOk v pool) p' -> p' <> PossError ->
exists ext v' pool', p' = PossOk v' pool' /\
  RInv VF v0 (run ++ ext) (tm_calls c') v' pool' /\ conc ext = overlay_events [ev]
```

This is the body of `rinv_step`, copied.

**8. `rinv_exec_err`.** By induction on the execution, either:
- (normal) `S c' (PossOk v' pool') ∧ RInv … ∧ conc ext = overlay_events evs`; or
- (stopped) `∃ evs1 evs2 ext v1 pool1, evs = evs1 ++ evs2 ∧ RInv (run ++ ext) _ v1 pool1 ∧ conc ext = overlay_events evs1 ∧ poss_steps VF (PossOk v1 pool1) PossError`.

**9. `gsim_complin_err`.** Four cases:
- Stopped: `rinv_licensed` yields the prefix.
- Normal, no `TErr`: `rinv_reify`, which is reused unchanged.
- Normal ending in `TErr k op`: the error clause at `c`, then `rinv_licensed` with `tl := [TErr k op]`.

Assumptions: {`classic`}, via `rinv_val`.

**Size.** About 450–600 lines. The main bookkeeping risk is `sink_split` and the `Sink` instantiation of `reify_step`'s six hypotheses (from `ri_path`, `ri_valid`, `ri_lwf`, `ri_auinv`, `ri_aures`, `rinv_val`).

## 4. A3 — the RLHL side

### A3a — `models/simlin/RelaxedHoareBaseErr.v` (triple and hypotheses; independent of A1 and A2)

```coq
Section TripleE.
  Context {E F} {VE : LTS E} {VF : LTS F} (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
  Definition RetCondE k op (r : Sig.ar op) : Assn VE VF :=
    fun s => RetCond I G k op r s \/ poss_steps VF (ps_poss s) PossError.
  Record CallTripleE k op (ret : Sig.ar op) (A : list (TaggedEvent E) -> Assn VE VF) : Prop := {
    cte_emit   : (* verbatim ct_emit *);
    cte_stable : forall l, Stable I (R k) (A l);
    cte_return : forall s, A [] s -> I s -> NoOwn k (ps_ghost s) -> RetCondE k op ret s;
    cte_noerr  : forall pre m post, local_frontier pre m ->
      forall σ p γ γ', ghost_emit k (untag m) γ γ' -> A (pre ++ m :: post) (σ, p, γ) -> I (σ, p, γ) ->
      Error VE (untag m) σ -> poss_steps VF p PossError }.          (* licensed form, D5 iii *)
  Context (M : RelaxedModuleImpl E F).
  Definition MethodSemE t op := (* MethodSem with CallTripleE *).
  CoInductive CallSafeE k op ret : list (TaggedEvent E) -> PState VE VF -> Prop :=
  | cse_intro l s (Hinv : I s)
      (Herr : forall pre m post, l = pre ++ m :: post -> local_frontier pre m ->
         forall γ', ghost_emit k (untag m) (ps_ghost s) γ' -> Error VE (untag m) (ps_mem s) ->
         poss_steps VF (ps_poss s) PossError)
      (Hemit : (* as CallSafe, with CallSafeE *)) (Hrely : (* as CallSafe *))
      (Hret : l = [] -> NoOwn k (ps_ghost s) -> RetCondE k op ret s) : CallSafeE k op ret l s.
End TripleE.
Record RLHL2HypsE I R G M σ0 v0 : Prop := {
  hE_sem : forall t op, MethodSemE I R G M t op;
  hE_guar_rely; hE_invoke_rely; hE_return_rely;                       (* verbatim from RLHL2Hyps *)
  hE_ok : forall s, I s -> ps_poss s = PossError \/
            exists v pool, ps_poss s = PossOk v pool /\ lin_pool_well_formed pool;
  hE_init : I (σ0, PossOk v0 [], []) }.
Record MethodProvableE I R G M t op Ω Q : Prop :=
  { mpe_PI; mpe_ret : forall h r s, Q h r s -> I s -> NoOwn (t, h) (ps_ghost s) -> RetCondE I G (t, h) op r s;
    mpe_triple (* = mp_triple *) }.
Theorem method_soundE (Hne : forall ev σ, ~ Error VE ev σ) t op Ω Q :
  MethodProvableE I R G M t op Ω Q -> MethodSemE I R G M t op.
```

**Lemmas**
- `triple_callsafeE`, `methodsem_safeE`: copies, plus the non-coinductive `Herr` clause.
- `ctx_tripleE`: a copy of `ctx_triple` built from `fam_emit`, `fam_stable`, `fam_return`, `fam_init`.
- `method_soundE`: a copy of `method_sound` (`walk`, `rp_unfold`, `close_sound`, `w_invs`).
- Weakenings:
  - `mpE_of_mp : MethodProvable … -> MethodProvableE …`;
  - `methodsemE_of_methodsem : (∀ ev σ, ¬Error VE ev σ) -> MethodSem … -> MethodSemE …`;
  - `rlhl2E_of_rlhl2 : (∀ ev σ, ¬Error VE ev σ) -> RLHL2Hyps … -> RLHL2HypsE …`.
- `chainE_provable`: a CProv chain with `Q` allowed to hold at `PossError`. It is needed for single-call bodies that may err.
- An `OrErr` kit:
  - `OrErr P := fun s => P s \/ ps_poss s = PossError`;
  - `KeepsErr r := ∀ s s', r s s' → ps_poss s = PossError → ps_poss s' = PossError`;
  - `stable_orerr`, `retcondE_of_err`, and an `EvUpdate` lemma into `OrErr`.

**Why `RetCondE` is unavoidable (and therefore `MethodProvableE` too).** Once any call errs, every other active call's `A []` holds at a `PossError` state. The old `ct_return`, which requires `RetCond` and hence `PossOk`, is then unprovable.

**Why `cte_noerr` is semantic.**
- For error-free `VE` it is vacuous. This covers LatchSet's `EIhl δ_coh`, hence the `Hne` premise of `method_soundE`.
- For erroring underlays, a later lemma `errlift_methodsemE` would run the rules over an error-free `ErrE VE` (error becomes a step to a sink) together with "sink ⇒ `PossError`", and pull the result back. It is deferred to the lock instance and is not needed for LatchSet.

### A3b — `models/simlin/RelaxedHoareErrSound.v` (bridge and theorems)

```coq
Record RSimE (c : Cfg) (p : Poss VF) : Prop := {
  rse_inv : I (proj c p); rse_owners : OwnersActive VE c;
  rse_dom : pool_dom_sub (active_key (tm_calls c)) p;
  rse_calls : forall e, In e (tm_calls c) -> CallStE (call_key e) (ce_cell F e) c p }.   (* CallSafeE inside *)
Theorem rlhl_gsim_err : RLHL2HypsE I R G M σ0 v0 ->
  exists S, GSimRelErr VE VF M S /\ S (initial_tagged_module VE σ0) (PossOk v0 []).
Theorem rlhl_complin_err : RLHL2HypsE I R G M σ0 v0 -> RCompLinErr M VE σ0 VF v0.
Corollary rlhl_complin_err_hl : RLHL2HypsE (VE := HL VE0) I R G M (σ0, []) v0 -> RCompLinErr M VE0 σ0 VF v0.  (* hliftE *)
Corollary rlhl_err_rel_lin : RLHL2HypsE (VF := EIe δ bad) I R G M σ0 (s0, []) ->
  forall s, MTraces VE M σ0 s -> PrefixView.complete s -> ~ Licensed (EIe δ bad) (s0, []) s ->
  rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δ s0).
```

**The bridge** copies and adapts `RelaxedHoareGSim` Bridge (`rsim_invoke`, `rsim_underlay`, `rsim_return`, `rsim_step`, `rsim_gsim`, `rsim_init`):
- **Invoke:** verbatim.
- **Underlay:** destruct `p'` from `Hemit`. If it is `PossError`, take the error disjunct. Otherwise the old proof applies, with `hE_ok` replacing `h_ok` in `pool_dom_steps`.
- **Return:** split `RetCondE`.
- **New `rsimE_error`:** the owner of the error candidate comes from `OwnersActive`. Then `select_project` and `ghost_of_select` lead to `CallSafeE.Herr`, which gives `poss_steps p PossError`.

**Reused unchanged:** `proj`, `StepMatch`, `OwnersActive`, `owners_active_step`, `select_project`, `ghost_of_*`, `osq_*`, `pool_dom_*`, `lin_fresh_of_dom`, `poss_invoke_exists`, `lin_remove_exists`, `entry_key_unique`, `finish_*`, `done_app_other`, `done_select`, `methodsem_safe`-style argument order.

**Regression.** `rlhl2E_of_rlhl2` applied to `RelaxedHoareChecks.CounterEIhl.counter_eihl_rlhl2` yields `counter_complin_err`. Old instances transfer for free.

## 5. What is reused and what is copied

| Unchanged | Copied / adapted (new names) |
|---|---|
| All of `RelaxedHoare`/`RelaxedHoareDag`/`RelaxedHoareSound` rules; `fam_*`, `walk`, `close_sound`, `rp_unfold` | `method_sound` → `method_soundE`; `ctx_triple` → `ctx_tripleE`; `MethodProvable` → `MethodProvableE` |
| `RInv`, `RInv_init`, `rinv_cinv/ainv/aret/prun/cret`, `poss_steps_prun`, `prun`, `vf_path`, `overlay_events` (`RelaxedGSim`) | `rinv_step`/`rinv_exec` → `rinv_match`/`rinv_exec_err` |
| `reify_step`, `CInv`, `cinv_init`, `rinv_val`, `rinv_reify`, `exec_snoc`, `idF`, `MTraces`, `RTraces` | `reify_loop` → `reify_loop_to`/`rinv_reify_to` |
| `OwnersActive`, `owners_active_reachable`, `proj`, `StepMatch`, call-pool facts (`RelaxedHoareGSim`) | `CallSt`/`RSim`/`rsim_*` → `CallStE`/`RSimE`/`rsimE_*` |
| `HL`, `lift_exec`, `drop_exec`, `EIhl`, `cc_rel_lin`, `cc_gsim`/`SCC`/`CCInv` (`RelaxedHoareCompLinSpec`) | `CallTriple`/`CallSafe`/`MethodSem`/`RLHL2Hyps` → E-versions |

## 6. Rejected reductions

- **Blocking: `bad` invocations have no `EI` step.**
  - `RTraces(blocking) ⊆ RTracesClosed` is sound, but the old `RLHL2Hyps` over it is unprovable whenever the implementation returns from a misusing call. LatchSet does: a second writer's insert returns `tt`.
  - It is also the m-8 "spec-side only" gap.
- **Chaos state in `VF` (`Some → ⊤` on `Error`, `⊤` allows every step), reusing `rlhl_gsim`/`gsim_complin` verbatim.**
  - It needs no new soundness code. But `RetCond` in chaos still requires `lin_lookup k (ls_linr op ret)`.
  - Any call linearized with `r' ≠ ret` before chaos, by helping or by an early abstract response, makes the chaotic `GSimRel` stuck at its return. So a `PossError`-absorbing proof cannot be translated generically.
  - Users would carry chaos disjuncts with per-call consistency, plus a restricted chaos guarantee.
  - Keep it only as a fallback if A3b stalls.

## 7. Does `HL` lift `Error` correctly?

**Yes.** `Error (HL V) ev σ := Error V ev (fst σ)`.
- `hliftE` holds because `LiftOK` guarantees that every queued invocation key, including an error candidate, is unused. So the used-key list never matters for `MTracesE`.
- **Residual.** `Error (HL V)` still holds at an already-used key, where `Step` is disabled. This only adds `cte_noerr` obligations for schedules the module never produces, the analogue of M-16.
- For `EIe` it is harmless, because `bad` does not mention keys. No `HLe` variant is needed now.

## 8. A4 — `examples/Relaxed/RelaxedHoareLockErr.v`: m8_gap and non-vacuity

**Setup**
- Lower lock `E_lock`: `Acq | Rel : unit`, SI empty.
- `δlock false Acq tt true`, `δlock true Rel tt false`. Acquire while held has no successor (blocking).
- `bad_lock (s,_) _ Rel := s = false`.
- Overlay `G1`: `Go : unit`, `δG _ Go tt tt`, no `bad`.
- `Mbad Go t := Future Acq (λf, Wait f (λ_, Future Rel (λf, Wait f (λ_, Future Rel (λf, Wait f (λ_, Ret tt))))))`.

```coq
Theorem m8_gap :
  (exists I R G, RLHL2Hyps (VE := EIhl δlock) (VF := RelaxedHoareSpec.EI δG) I R G Mbad ((false, []), []) (tt, [])) /\
  ~ RCompLinErr Mbad (EIe δlock bad_lock) (false, []) (RelaxedHoareSpec.EI δG) (tt, []).
Corollary m8_no_rlhl2E :
  ~ exists I R G, RLHL2HypsE (VE := EIhle δlock bad_lock) (VF := RelaxedHoareSpec.EI δG) I R G Mbad ((false, []), []) (tt, []).
```

**Proofs**
- **Positive half (old notion).** Linearize `Go` (invocation and response) at its first emission. Set `SI_G1(Go, Go) := True` so that `invocation_ready` is trivial. About 250 lines.
- **Negative half.** One explicit execution: one call; `Acq`/`Rel` inv and res emitted; the third `Rel` candidate gives `module_error_tagged`. So `[TEv inv(Go); TErr k Go] ∈ MTracesE`. `RTracesClosed` rejects it because `Error (EI δG) = False`.
- **Corollary.** `rlhl_complin_err_hl` together with `hliftE` and the negative half.

**Positive non-vacuity (required before LatchSet).** "OneShot" register:
- Overlay `Set v : unit`, `Get : nat`; `bad := "Set while state is Some _"`. Module: `Set v ↦ write`, `Get ↦ read` over `EIhl δreg`.
- `oneshot_rlhl2E` must take `PossError` at the second `Set`'s write.
- `oneshot_wrong_no_rlhl2E`: a module writing `v+1` has no proof, via an unlicensed single-`Set` trace.

**Size.** 600–900 lines.

## 9. LatchSet's P1/P2 as `EIe` errors (A5, `examples/Relaxed/RelaxedHoareLatchSpec.v`)

```coq
Definition latch_bad (tw : tid) (N : nat) (s : list nat * list (Op F_L)) (t : tid)
    (o : Sig.op (RelaxedSig.effect F_L)) : Prop :=
  match o with
  | OIns k => t <> tw                                          (* P1: designated writer *)
           \/ (exists x, In x (snd s) /\ is_ins (op_op x))      (* P1: no overlapping insert (pending EI record) *)
           \/ (~ In k (fst s) /\ N <= length (fst s))           (* P2: capacity *)
  | OPrint => False end.
Definition VF_L tw N := EIe δ_set (latch_bad tw N).            (* δ_set total: ins_sorted / print returns s *)
Lemma latch_not_licensed tw N s : P1P2 tw N s -> ~ Licensed (VF_L tw N) ([], []) s.
(* target, later: *)
Theorem latch_rlhl2E : RLHL2HypsE (VE := EIhl δ_coh) (VF := VF_L tw N) I_L R_L G_L (M_L N) ((σc, []), []) ([], []).
Corollary latch_rel_lin : forall s, MTraces (RelaxedHoareSpec.EI δ_coh) (M_L N) (σc, []) s ->
  PrefixView.complete s -> P1P2 tw N s ->
  rel_lin (@PrefixView.sel F_L) s (semi_independent F_L) (RelaxedHoareSpec.seq_legal δ_set []).
```

`latch_rel_lin` comes from `rlhl_complin_err_hl`, `complin_err_rel_lin` and `latch_not_licensed`.

**`P1P2`** is a prefix-closed predicate on overlay traces:
- every insert is invoked by `tw`;
- an insert's response precedes every later insert's invocation;
- at most `N` distinct inserted keys.

**`latch_not_licensed`** needs a generic shape lemma `eie_error_shape`. From a copy-cat error over `EIe`, transported to `EI` by `mtraces_eie_ei`, it gives:
- the erroring call `k` is active with op `op`, invoked in `p`, and `bad (tm_lts_state c) (fst k) op` holds;
- every pending record belongs to a different active call with the same op;
- `seq_run δ s0 W (fst state)` holds, with `W` the ops of calls invoked in `p`.

Build it from `CCInv` (`sc_q`, `sc_pc`, `PhaseOK`) or from a small invariant of its own. It is about 200 lines and the risk sits in A5: `op_op x = ac_op` is not stated in `CCInv` and must be added as a lemma.

**Where the LatchSet proof will take the errors.** All of them can be taken at the bad call's first emission. If the earlier insert `k1` is still active, `poss_steps` may first lin-invoke `k1` (which adds its record) and then `psa_inv_error` for `k2`. If `k1` has already returned, all of its events were emitted before `k2`'s, which is safe. `RetCondE` is still needed so that every other call can return after the error.

## 10. Writer sub-tasks

These apply to every task:
- Rocq 9.3.0 (`export PATH=/opt/homebrew/bin:$PATH`); `_CoqProject` gets the new files after `RelaxedHoareAbsorb.v` and before `examples/`.
- No `Admitted`/`Axiom`/`vm_compute`/`native_compute`.
- No edits to existing `.v` files.
- Headers state K/S/P/R levels and axioms.

| ID | Files | Targets | Accept when | Size, iterations |
|---|---|---|---|---|
| A1 | `models/simlin/RelaxedHoareErrSpec.v` | §2 | all Closed except `complin_err_rel_lin` ⊆ {`eq_rect_eq`, `classic`}; `hliftE` both directions | 350–450, 1 |
| A3a (parallel with A1) | `models/simlin/RelaxedHoareBaseErr.v` | §4 A3a: triples, `CallSafeE`, `RLHL2HypsE`, `method_soundE`, `chainE_provable`, weakenings, `OrErr` kit | all Closed; `method_soundE` checked on `RelaxedHoareChecks.counter_provable` (via `mpE_of_mp`) | 350–450, 1 |
| A2 | `models/simlin/RelaxedHoareGSimErr.v` | §3 | `gsim_complin_err`, `rinv_licensed` ⊆ {`classic`}; `sink_split`, `rinv_reify_to`, `poss_steps_error_split` Closed | 450–600, 1–2 |
| A3b | `models/simlin/RelaxedHoareErrSound.v` | §4 A3b | `rlhl_gsim_err` Closed; `rlhl_complin_err` ⊆ {`classic`}; `counter_complin_err` regression | 400–550, 1–2 |
| A4 | `examples/Relaxed/RelaxedHoareLockErr.v` | §8: `m8_gap` (both halves), `m8_no_rlhl2E`, OneShot positive and wrong-module negative | all ⊆ {`classic`, `eq_rect_eq`} | 600–900, 2 |
| A5 | `examples/Relaxed/RelaxedHoareLatchSpec.v` | `F_L` (port of `LatchSetProg` Part 2), `δ_set`, `latch_bad`, `P1P2`, `eie_error_shape`, `latch_not_licensed` | Closed or {`classic`} | 600–900, 2 |

**Order.** {A1, A3a} → A2 → A3b → {A4, A5}. A5's `latch_not_licensed` and A4's negative half need only A1.

## 11. Risks

1. **`Sink` instantiation of `reify_step`.** It needs explicit hypotheses with dependent `Sig.ar` in `Hval`. Use `rinv_val` at `Sink VF`, which is generic.
2. **`sink_split`.** Overlay steps may continue after `None`; split at the first underlay step into `None` only.
3. **The `RSimE` copy.** About 300 lines of near-verbatim proof. The risk is mechanical (renames, the two new case splits).
4. **`eie_error_shape`.** `CCInv` does not record `op_op x = ac_op (fst g)` for `ph1` records, so it must be derived or an invariant of its own added.
5. **Dependent inversion of `module_error_tagged`.** The `op` comes from `ActiveCall op ret`. Avoid inverting `Hact`: use `In` lookups and compare through `call_key`.
6. **User burden.** Assertions need `OrErr` disjuncts. All `R`/`G` must keep `PossError` (`KeepsErr`). Keep the kit small but complete before LatchSet.

## 12. Research-level points for the author

1. **Licensing is existential over copy-cat runs**, as in CompLin's `ImplTracesClosed`: UB if *some* relaxed linearization of the prefix violates `bad`.
   - This is what lets an EI-state precondition ("a pending insert record") capture overlay-level overlap. The copy-cat may delay underlay responses, and a client that never overlaps cannot be licensed (`latch_not_licensed`).
   - For state-dependent preconditions this is angelic toward errors. The paper should say so.
2. **D5 (vi) is forced, not optional.** It needs `RetCondE` and a copy of `method_sound`/`MethodProvable`, because once anything errs, every pending call's return obligation must be vacuous.
3. **The syntactic rules have no error premise.**
   - `cte_noerr` is semantic: vacuous for COH+barriers, and via the `ErrE` lift for erroring underlays (later).
   - The `RelaxedHoare.v` header says `cprov_call` drops LHL's `Herror`/`Hperror`. With m-8, the paper's call rule could regain a licensed `Herror`. Decide whether the paper claims that.
4. **Layering with error specs is excluded (D5 v).** LatchSet with P1/P2 can only be a top layer under `VerImpl`. This matters later for SeqLock-like single-writer layers.
5. **The `rel_lin` corollary covers unlicensed complete traces only.** Connecting client-level P1/P2 to "unlicensed" is per-instance (A5).
6. **`bad` versus `pre` (D5 ii).** `bad` is proposed; it is equivalent to `~pre` under `classic`.

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLin.v (`reify_step`, `CInv`/`ci_path`, `cinv_init`, `rinv_val`, `rinv_reify`, `gsim_complin`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedGSim.v (`RInv`, `rinv_*`, `rinv_step`/`rinv_exec` templates, `prun`, `vf_path`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareGSim.v (Bridge `RSim`/`rsim_*` to copy-adapt, `OwnersActive`, `owners_active_reachable`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareBase.v and /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareSound.v (`CallTriple`/`CallSafe`/`RLHL2Hyps`/`RetCond`; `method_sound`/`ctx_triple` templates)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v (`HL`, `lift_exec`/`drop_exec`, `EIhl`, `cc_rel_lin`, `CCInv`/`SCC`)

New files: `models/simlin/RelaxedHoareErrSpec.v`, `models/simlin/RelaxedHoareGSimErr.v`, `models/simlin/RelaxedHoareBaseErr.v`, `models/simlin/RelaxedHoareErrSound.v`, `examples/Relaxed/RelaxedHoareLockErr.v`, `examples/Relaxed/RelaxedHoareLatchSpec.v`.