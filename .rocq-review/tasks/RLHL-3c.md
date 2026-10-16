<!-- RLHL-3c plan, produced 2026-10-14 by a read-only design panel (three Plan agents: operational, trace-theoretic, incremental; one skeptical rocq-research-reviewer synthesis). Saved verbatim by the orchestrator. The three individual designs are archived in .rocq-review/tasks/RLHL-3c-designs/. Research-level decisions D1-D8 below have NOT been put to the author yet (see research-intent.md §7). -->

# RLHL-3c plan (design panel, 2026-10-14)

**Scope.** Repository `/Users/index/Documents/GitHub/rbgs-rlhl`, branch `rlhl`, HEAD 6aef511, with the RLHL-3a/3b work uncommitted. The build is fresh under Rocq 9.3.0: `make -n` lists only `structures/DCPOs.v`, and the RLHL `.vo` files are newer than their sources. A Writer is editing `examples/Relaxed/RelaxedHoareCounterXY.v` and `models/simlin/RelaxedHoareInherit.v` at the same time. Their line numbers are moving (for example, `cxy_complin_ei` is now at :499), so this plan cites them by name.

**Bottom line.**
- Two of the three foundations are now proved in scratch sessions:
  - `mtraces_mono`: Closed.
  - `modlts_paths`: Closed.
- The third, absorption, is the only lemma with real content on the route. With absorption stated as a toplevel `Axiom`, the vertical composition rule follows by definition. So absorption is the main risk and the main deliverable.

## Goal and claims

| Target | P (paper) | R (reviewer) | S (planned Coq statement) | Remaining K/S/P gap |
|---|---|---|---|---|
| T1 trace-determinedness | — (prerequisite) | latest-review M-22 (1) | `mtraces_mono`: inclusion of path languages implies inclusion of MTraces, for any underlay LTS | none (scratch: Closed) |
| T2 saturation | `Appendix/relaxedlin.tex:53-56`: ⟦M⟧_E = cc_E;⟦M⟧_E;cc_F for every sequential M | M-22 (2) | `saturate_cc`/`saturate_ei`: `MTraces (ModLTS VF idF) M ↔ MTraces VF M`, for `CCClosed VF` (EI and EIhl from an empty pending list) | **E-side only.** Absorption is false for a general VF (A's counterexample (R), sound: programs can read raw handles, `RelaxedLang.v:25`). The F-side is probably false without SI inheritance (D2) |
| T3 certified-implementation equivalence | `Appendix/relaxedlin.tex:58-62, :64-72` | M-22 | `rcomplin_paper`: `RCompLin M (EI δE) … ↔ (cc_E;M ⊆ RTraces VF)` | copy-cat form instead of rlx(ν) |
| T4 Soundness | `Appendix/relaxedlin.tex:665`: ν_E;cc_E;M ⊆ ν_F;cc_F | B :313-316 | `rlhl_sound_paper`: RLHL2Hyps over `EIhl δE` ⇒ every trace of `M` over `ModLTS (EI δE) idF` is an `RTraces (EI δF)` trace | ν are EI presentations; the premise is `RLHL2Hyps`, not the printed simulation; one possibility only |
| T5 vertical composition | `relaxedlin.tex:56-71` (inlining, ⟦M;N⟧=⟦M⟧;⟦N⟧, associativity), `:74` (verimpl), `:76-84` (observational refinement), `:88-99` (prop:vertical-composition) | M-22 (3); B :313-316 | `VerImpl` (copy-cat form), `verimpl_of_rlhl`, `verimpl_vcomp`, `verimpl_weaken`, `obs_refinement_cc`, `modlts_trlts` | composition is semantic (`ModLTS`); there is no syntactic M;N (D1). verimpl quantifies over copy-cat-refining underlays, not over rel-lin ones: the M-20 converse is open (D3) |
| T6 prop:rlhl-sc | `implex.tex:170-178` | B-1 | T4 plus `cc_rel_lin` for complete traces | "view-based compatible objects" is not covered; rlxlin for prefixes is only argued (M-20) |
| T7 client | — (no printed client; author response B4 `popl2027-reviews.md:531-533` promises SeqLock a=b) | B :313-316 ("…the verification of a concurrent object alongside the verification of its client program"), :214 ("No demonstration … useful for nontrivial client verification"), :257-259; meta-review :615 ("the lack of a demonstration of client verification") | `sb_client_modular`, then `sb_client`, plus contrasts (`sb_nowait_00`, `sb_nowait_si_decides`) | the object is a renaming (B-1 (4′)); the memory is an SC cell with COH-style SI, not RC11; this is not the promised SeqLock a=b client |
| T8 error clause (m-8) | CompLin-style TErr (author decision §8) | latest-review m-8 | `RCompLinErr`, `GSimRelErr`, `RLHL2HypsE`, `m8_gap` | blocked on D5 |

## Recommended route

1. **Operational composite plus trace-determinedness.**
   - `ModLTS VE M` is the LTS over F whose step is a block of underlay steps followed by one overlay step (Design A; Design B calls it `Lift`).
   - `mtraces_mono` reuses `ViewLHL.exec_underlay_path` and `exec_transport` (`models/view/ViewLHL.v:353-388`).
   - `TrLTS` (Design C's TLTS) is kept as a tool and linked by `modlts_trlts`. That lemma reduces C's deferred `link_joint` to `mtraces_mono` + `modlts_paths` + `trlts_paths`.
   - Do not use B's names `lift_step`/`lift_exec`: they collide with `RelaxedHoareCompLinSpec.lift_step` (:1029) and `lift_exec`.
2. **Absorption in generic form (Design A).** The hypothesis is `CCClosed VF v0`: paths are closed under per-thread key renaming and under deleting responses. The proof is a forward simulation from the composite to a target M-execution:
   - the target runs over `FreeLTS` (`Step := True`) and copies M's prophecies;
   - each inner idF V-inv makes the target emit M's invocation;
   - each inner V-res makes the target emit M's response if the event matches (decided by `classic`), and otherwise the response is dropped;
   - the target is then moved to VF with `exec_transport` along the `ccimg` image, which `CCClosed` licenses.

   This keeps scheduling separate from VF-specific reasoning, which is isolated in `ei_ccclosed` and `eihl_ccclosed`. EI satisfies `CCClosed` for *any* key map: `ei_step` only adds a record keyed by the event key and removes a record by membership (`RelaxedHoareSpec.v:307-313`). The pending list must start empty (B's caveat).
3. **Verified implementation in copy-cat form.** `VerImpl M δE sE δF sF := ∀ U u, CCRefines U u δE sE → CCRefines (ModLTS U M) (init u) δF sF`.
   - The paper's first vertical composition rule then holds by definition (checked: Closed).
   - All the content sits in `verimpl_of_rcomplin`, which needs `absorb_ei`. Scratch `Print Assumptions` with the pieces axiomatised gives {modlts_paths (since proved), absorb_ei, classic}.
4. **Client.**
   - Spec level, prefix-general: `sb_client_spec` over the plain `EI δcxy`, with a pure EI-path cycle lemma.
   - Modular over every `CCRefines` underlay; instantiated with Counter_xy over `EI δmem` through `cxy_complin_ei` and `modlts_paths`.
   - This matches the author's B4 answer: "reason from an object's contract and use a contextual refinement result to transfer the property".
5. **m-8** comes after the client. It is blocked on D5.

Why this route beats the alternatives:
- **Against C (no absorption).** C cannot compose a layer verified by RLHL: it needs `RCompLin M2 (MLTS VF idF v) …`, and RLHL never gives that. C's client is limited to complete runs, because `cc_rel_lin` requires `PrefixView.complete`.
- **Against B (EI-specific absorption that re-times responses).** B's invariant needs permutation reasoning on pending lists and reuses `CCInv`, which is tied to EI. A's drop-at-mismatch keeps the inner VF order and only renames or drops events.

**Fallback.** If 3c.5 stalls after three iterations, use C's route for the client: `TrLTS` + `cxy_complin_ei` + `cc_rel_lin` + a cycle lemma on the `sb_not_rel_lin0` template, for complete runs only. Record absorption as open.

## Exact Rocq statements

### File `models/simlin/RelaxedHoareLayer.v` (new)
```coq
Definition LPaths {F} (V : LTS F) (v : State V) (u : list (ThreadEvent F)) : Prop := exists v', vf_path V v u v'.
Theorem mtraces_mono {E F} (V1 V2 : LTS E) (M : RelaxedModuleImpl E F) (v1 : State V1) (v2 : State V2) :
  (forall u, LPaths V1 v1 u -> LPaths V2 v2 u) -> forall s, MTraces V1 M v1 s -> MTraces V2 M v2 s.   (* scratch: Closed *)
Corollary mtraces_ext … : (forall u, LPaths V1 v1 u <-> LPaths V2 v2 u) -> forall s, MTraces V1 M v1 s <-> MTraces V2 M v2 s.
Corollary complin_mono_under {E F} (M : RelaxedModuleImpl E F) (V1 V2 : LTS E) v1 v2 (VF : LTS F) w :
  (forall u, LPaths V1 v1 u -> LPaths V2 v2 u) -> RCompLin M V2 v2 VF w -> RCompLin M V1 v1 VF w.
Definition FreeLTS (E : RelaxedSig.t) : LTS E := {| State := unit; Step := fun _ _ _ => True; Error := fun _ _ => False |}.
Theorem mtraces_free {E F} (V : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State V) s :
  MTraces V M σ0 s <-> exists evs c, module_execution_tagged (FreeLTS E) M (initial_tagged_module (FreeLTS E) tt) evs c /\
                                     LPaths V σ0 (ViewLHL.underlay_events evs) /\ overlay_events evs = s.
Lemma exec_app {E F} VE (M : RelaxedModuleImpl E F) c1 evs1 c2 evs2 c3 :
  module_execution_tagged VE M c1 evs1 c2 -> module_execution_tagged VE M c2 evs2 c3 -> module_execution_tagged VE M c1 (evs1 ++ evs2) c3.
Definition mod_step {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) (ev : ThreadEvent F) (c c' : @TaggedModuleConfig E F VE) : Prop :=
  exists us c1, module_execution_tagged VE M c (map (@UnderlayEvent E F) us) c1 /\ module_step_tagged VE M (OverlayEvent ev) c1 c'.
Definition ModLTS {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) : LTS F :=
  {| State := @TaggedModuleConfig E F VE; Step := mod_step VE M; Error := fun _ _ => False |}.
Theorem modlts_paths {E F} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) u :
  LPaths (ModLTS VE M) (initial_tagged_module VE σ0) u <-> MTraces VE M σ0 u.          (* scratch: Closed *)
Definition TrLTS {F} (T : list (ThreadEvent F) -> Prop) : LTS F :=
  {| State := list (ThreadEvent F); Step := fun e u u' => u' = u ++ [e] /\ T u'; Error := fun _ _ => False |}.
Lemma mtraces_nil {E F} VE (M : RelaxedModuleImpl E F) σ0 : MTraces VE M σ0 [].
Theorem trlts_paths {F} (T : list (ThreadEvent F) -> Prop) :
  T [] -> (forall s1 s2, T (s1 ++ s2) -> T s1) -> forall u, LPaths (TrLTS T) [] u <-> T u.
Corollary modlts_trlts {E F G} (VE : LTS E) (M1 : RelaxedModuleImpl E F) (σ0 : State VE) (M2 : RelaxedModuleImpl F G) s :
  MTraces (ModLTS VE M1) M2 (initial_tagged_module VE σ0) s <-> MTraces (TrLTS (MTraces VE M1 σ0)) M2 [] s.
```
Optional sanity check: re-derive the ⇐ half of `hlift` from `mtraces_mono` and `hl_step_base`.

### File `models/simlin/RelaxedHoareAbsorb.v` (new)
```coq
Lemma produced_inv_answered {E : RelaxedSig.t} {R : Type} t (p : Prog E R) tr (r : R) j h op :
  program_produces_tagged t p tr r -> nth_error (map untag tr) j = Some (Build_ThreadEvent t (@InvEv E h op)) ->
  exists j' (ret : Sig.ar op), j < j' /\ nth_error (map untag tr) j' = Some (Build_ThreadEvent t (@ResEv E h op ret)).
Theorem unabsorb {F G} (VF : LTS F) (v0 : State VF) (M : RelaxedModuleImpl F G) s :
  MTraces VF M v0 s -> MTraces (ModLTS VF idF) M (initial_tagged_module VF v0) s.     (* every VF *)
Definition rehandle {F} (h : RelaxedSig.handle F) (e : ThreadEvent F) : ThreadEvent F :=
  Build_ThreadEvent (te_tid F e) (match te_ev F e with InvEv _ o => InvEv h o | ResEv _ o r => ResEv h o r end).
Definition is_res {F} (e : ThreadEvent F) : Prop := match te_ev F e with ResEv _ _ _ => True | _ => False end.
Inductive ccimg {F} (Rk : CallKey F -> RelaxedSig.handle F -> Prop) : list (ThreadEvent F) -> list (ThreadEvent F) -> Prop :=
| ccimg_nil : ccimg Rk [] []
| ccimg_keep e h u u' : Rk (te_key e) h -> ccimg Rk u u' -> ccimg Rk (e :: u) (rehandle h e :: u')
| ccimg_drop e u u' : is_res e -> ccimg Rk u u' -> ccimg Rk (e :: u) u'.
Definition CCClosed {F} (V : LTS F) (v0 : State V) : Prop :=
  forall Rk u u', (forall k h1 h2, Rk k h1 -> Rk k h2 -> h1 = h2) ->
    (forall k1 k2 h, Rk k1 h -> Rk k2 h -> fst k1 = fst k2 -> k1 = k2) ->
    LPaths V v0 u -> ccimg Rk u u' -> LPaths V v0 u'.                                  (* typechecks *)
Lemma ei_ccclosed {F St} (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) (s0 : St) :
  CCClosed (RelaxedHoareSpec.EI δ) (s0, []).
Lemma eihl_ccclosed {F St} δ (s0 : St) : CCClosed (@EIhl F St δ) ((s0, []), []).
Theorem absorb {F G} (VF : LTS F) (v0 : State VF) (M : RelaxedModuleImpl F G) :
  CCClosed VF v0 -> forall s, MTraces (ModLTS VF idF) M (initial_tagged_module VF v0) s -> MTraces VF M v0 s.
Theorem absorb_needs_closure : exists (F G : RelaxedSig.t) (VF : LTS F) (v0 : State VF) (M : RelaxedModuleImpl F G) s,
  MTraces (ModLTS VF idF) M (initial_tagged_module VF v0) s /\ ~ MTraces VF M v0 s.      (* A's (R): handle-0-only VF, M branches on future_handle *)
Corollary absorb_ei {F G St} δ (s0 : St) (M : RelaxedModuleImpl F G) s :
  MTraces (ModLTS (RelaxedHoareSpec.EI δ) idF) M (initial_tagged_module (RelaxedHoareSpec.EI δ) (s0, [])) s -> MTraces (RelaxedHoareSpec.EI δ) M (s0, []) s.
Corollary saturate_ei {F G St} δ (s0 : St) (M : RelaxedModuleImpl F G) s :
  MTraces (ModLTS (RelaxedHoareSpec.EI δ) idF) M (initial_tagged_module _ (s0, [])) s <-> MTraces (RelaxedHoareSpec.EI δ) M (s0, []) s.
Corollary cc_idem_ei {F St} δ (s0 : St) s :                                             (* cc;cc = cc *)
  RTraces (ModLTS (RelaxedHoareSpec.EI δ) idF) (initial_tagged_module _ (s0, [])) s <-> RTraces (RelaxedHoareSpec.EI δ) (s0, []) s.
Corollary rcomplin_paper {E F StE} δE (sE : StE) (M : RelaxedModuleImpl E F) (VF : LTS F) (v : State VF) :
  RCompLin M (RelaxedHoareSpec.EI δE) (sE, []) VF v <->
  (forall s, MTraces (ModLTS (RelaxedHoareSpec.EI δE) idF) M (initial_tagged_module _ (sE, [])) s -> RTraces VF v s).
Corollary rlhl_sound_paper {E F StE StF} δE (sE : StE) δF (sF : StF) (M : RelaxedModuleImpl E F) I R G :
  RLHL2Hyps (VE := EIhl δE) (VF := RelaxedHoareSpec.EI δF) I R G M ((sE, []), []) (sF, []) ->
  forall s, MTraces (ModLTS (RelaxedHoareSpec.EI δE) idF) M (initial_tagged_module _ (sE, [])) s -> RTraces (RelaxedHoareSpec.EI δF) (sF, []) s.
(* + rlhl_sound_paper_rel_lin: same premises, PrefixView.complete s -> rel_lin sel s (semi_independent F) (seq_legal δF sF) *)
```

### File `models/simlin/RelaxedHoareLink.v` (new)
```coq
Definition CCRefines {F St} (U : LTS F) (u : State U) (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) (s : St) : Prop :=
  forall t, LPaths U u t -> RTraces (RelaxedHoareSpec.EI δ) (s, []) t.
Definition VerImpl {E F StE StF} (M : RelaxedModuleImpl E F) δE (sE : StE) δF (sF : StF) : Prop :=
  forall (U : LTS E) (u : State U), CCRefines U u δE sE -> CCRefines (ModLTS U M) (initial_tagged_module U u) δF sF.
Theorem verimpl_iff : VerImpl M δE sE δF sF <-> RCompLin M (RelaxedHoareSpec.EI δE) (sE, []) (RelaxedHoareSpec.EI δF) (sF, []).
  (* ⇐: mtraces_mono + modlts_paths + absorb_ei;  ⇒: U := ModLTS (EI δE) idF, then unabsorb *)
Corollary verimpl_of_rlhl : RLHL2Hyps (VE := EIhl δE) (VF := RelaxedHoareSpec.EI δF) I R G M ((sE, []), []) (sF, []) -> VerImpl M δE sE δF sF.
Theorem verimpl_vcomp : VerImpl M1 δE sE δF sF -> VerImpl M2 δF sF δG sG -> forall (U : LTS E) (u : State U), CCRefines U u δE sE ->
  CCRefines (ModLTS (ModLTS U M1) M2) (@initial_tagged_module F G (ModLTS U M1) (initial_tagged_module U u)) δG sG.   (* scratch: Closed *)
Theorem verimpl_weaken : VerImpl M δE sE δF sF ->
  (forall t, RTraces (RelaxedHoareSpec.EI δE') (sE', []) t -> RTraces (RelaxedHoareSpec.EI δE) (sE, []) t) ->
  (forall t, RTraces (RelaxedHoareSpec.EI δF) (sF, []) t -> RTraces (RelaxedHoareSpec.EI δF') (sF', []) t) -> VerImpl M δE' sE' δF' sF'.
Corollary obs_refinement_cc : CCRefines U u δE sE -> forall s, MTraces U M u s -> MTraces (RelaxedHoareSpec.EI δE) M (sE, []) s.
Corollary rlhl_link_ei : RLHL2Hyps (VE := EIhl δE) (VF := EI δF) I1 R1 G1 M1 ((sE,[]),[]) (sF,[]) ->
  RLHL2Hyps (VE := EIhl δF) (VF := EI δG) I2 R2 G2 M2 ((sF,[]),[]) (sG,[]) ->
  CCRefines (ModLTS (ModLTS (RelaxedHoareSpec.EI δE) M1) M2) (initial_tagged_module _ (initial_tagged_module _ (sE, []))) δG sG.
(* optional: eihl_ccrefines : CCRefines (EIhl δ) ((s0,[]),[]) δ s0.  NB: CCRefines (EI δ) (s0,[]) δ s0 is FALSE (EI admits duplicate keys). *)
```

### File `examples/Relaxed/RelaxedHoareClientSB.v` (new; imports CounterXY, does not edit it)
```coq
Definition other c := match c with CX => CY | CY => CX end.
Inductive SBOp := SB (c : CLoc).  (* Sig.ar := nat; GS: handle nat, SI ∅, mode Local — all typecheck *)
Definition Mcl_si si : RelaxedModuleImpl (CxySig si) GS := fun o _ => match o as o0 return Prog _ (Sig.ar o0) with
  | SB c => Future (Inc c) (fun f => Wait f (fun _ => Future (Get (other c)) (fun g => Wait g (fun r => Ret r)))) end.
Definition Mnw_si si : RelaxedModuleImpl (CxySig si) GS := (* Future inc; Future get; Wait g; Wait f; Ret r *).
Lemma mcl_trace t c tr (r : nat) : program_produces_tagged t (Mcl_si si (SB c) t) tr r ->
  exists h1 h2 (r1 : nat) D1 D2, h1 <> h2 /\ D2 h1 /\
   tr = [Build_TaggedEvent (Build_ThreadEvent t (InvEv h1 (Inc c))) D1; Build_TaggedEvent (Build_ThreadEvent t (ResEv h1 (Inc c) r1)) no_deps;
         Build_TaggedEvent (Build_ThreadEvent t (InvEv h2 (Get (other c)))) D2; Build_TaggedEvent (Build_ThreadEvent t (ResEv h2 (Get (other c)) r)) no_deps].
Lemma ei_sb_cycle (u : list (ThreadEvent FC)) v (ka kb kc kd : CallKey FC) ia ib jb ic id jd :
  vf_path (@RelaxedHoareSpec.EI FC MSt δcxy) (s00, []) u v -> NoDup (invocation_keys u) ->
  nth_error u ia = Some (Build_ThreadEvent (fst ka) (InvEv (snd ka) (Inc CX))) ->
  nth_error u ib = Some (Build_ThreadEvent (fst kb) (InvEv (snd kb) (Get CY))) ->
  nth_error u jb = Some (Build_ThreadEvent (fst kb) (@ResEv FC (snd kb) (Get CY) 0)) ->
  nth_error u ic = Some (Build_ThreadEvent (fst kc) (InvEv (snd kc) (Inc CY))) ->
  nth_error u id = Some (Build_ThreadEvent (fst kd) (InvEv (snd kd) (Get CX))) ->
  nth_error u jd = Some (Build_ThreadEvent (fst kd) (@ResEv FC (snd kd) (Get CX) 0)) -> ia < ib -> ic < id -> False.  (* spec only *)
Theorem sb_client_spec s (k1 k2 : CallKey GS) : MTraces (@RelaxedHoareSpec.EI FC MSt δcxy) (Mcl_si by_counter) (s00, []) s ->
  In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s -> In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False.
Theorem sb_client_modular (U : LTS FC) (u : State U) : CCRefines U u δcxy s00 -> forall s k1 k2, MTraces U (Mcl_si by_counter) u s -> (same two Ins) -> False.
Corollary sb_client s k1 k2 : MTraces (ModLTS (RelaxedHoareSpec.EI δmem) M_cxy) (Mcl_si by_counter)
  (initial_tagged_module (RelaxedHoareSpec.EI δmem) (s00, [])) s -> (same two Ins) -> False.      (* all executions; classic only *)
Theorem sb_client_live : exists s k1 k2, MTraces (ModLTS (EI δmem) M_cxy) (Mcl_si by_counter) (init) s /\ PrefixView.complete s /\
  In (… (SB CX) 0) s /\ In (… (SB CY) 1) s.
Theorem sb_nowait_00 : exists s k1 k2, MTraces (ModLTS (EI δmem) M_cxy) (Mnw_si by_counter) (init) s /\ (both return 0).  (* via modlts_trlts + sb_mtraces + mtraces_prefix *)
Theorem sb_nowait_si_decides : (exists s k1 k2, MTraces (@EI FC _ δcxy) (Mnw_si by_counter) (s00,[]) s /\ both 0) /\
  (forall s k1 k2, MTraces (@EI F0 _ δcxy) (Mnw_si (fun _ _ => False)) (s00,[]) s -> both 0 -> False).
```
The proof of `sb_client_spec` has these steps:
- instrument the run (`instrument`, `iinv_reach`);
- a call that has returned has emitted all its events (`ii_returned_done`, `ii_partition`);
- `mcl_trace`;
- `ii_order` on the (F3) pair res(inc) → inv(get): the tag `D2 h1` comes from `tagged_future`'s `resolved_in H` (`RelaxedSemantics.v:388-395`);
- map IT positions to underlay positions (`ucount`);
- apply `ei_sb_cycle`.

The same-thread case needs no (F2) argument (contrary to A §6).

### m-8 (after D5; definitions beside the old ones)
```coq
Variant TItem (F : RelaxedSig.t) := TEv (e : ThreadEvent F) | TErr (k : CallKey F) (op : Sig.op (RelaxedSig.effect F)).
Inductive module_error_tagged {E F} (VE : LTS E) : CallKey F -> Sig.op (RelaxedSig.effect F) -> @TaggedModuleConfig E F VE -> Prop :=
| tagged_error cand op ret q pool queue queue' used (Hsel : select_frontier_tagged cand queue queue')
    (Hact : In (Build_CallEntry (fst (ts_owner cand)) (snd (ts_owner cand)) (ActiveCall op ret)) pool)
    (Herr : Error VE (untag (ts_event cand)) q) : module_error_tagged VE (ts_owner cand) op (Build_TaggedModuleConfig q pool queue used).
Definition MTracesE VE M σ0 s := exists evs c, module_execution_tagged VE M (initial_tagged_module VE σ0) evs c /\
  (s = map (@TEv _) (overlay_events evs) \/ exists k op, module_error_tagged VE k op c /\ s = map (@TEv _) (overlay_events evs) ++ [TErr k op]).
Definition RTracesClosed VF v s := MTracesE VF idF v s \/ exists p k op tl, MTracesE VF idF v (p ++ [TErr k op]) /\ s = p ++ tl.
Definition RCompLinErr M VE σ0 VF v0 := forall s, MTracesE VE M σ0 s -> RTracesClosed VF v0 s.
Definition EIe {F St} δ (pre : St -> Sig.op (RelaxedSig.effect F) -> Prop) : LTS F :=
  {| State := St * list (Op F); Step := RelaxedHoareSpec.ei_step δ;
     Error := fun ev s => match te_ev F ev with InvEv _ o => ~ pre (fst s) o | _ => False end |}.
Lemma rcomplin_err_of_rcomplin : (forall ev q, ~ Error VE ev q) -> RCompLin M VE σ0 VF v0 -> RCompLinErr M VE σ0 VF v0.
Lemma rcomplin_of_err : (forall ev q, ~ Error VF ev q) -> RCompLinErr M VE σ0 VF v0 -> RCompLin M VE σ0 VF v0.
Definition GSimRelErr VE VF M S := forall c p, S c p -> p = PossError \/ ((exists v pool, p = PossOk v pool) /\
  (forall k op, module_error_tagged VE k op c -> poss_steps VF p PossError) /\ (gsim_step clauses with p' allowed to be PossError)).
Theorem gsim_complin_err : GSimRelErr VE VF M S -> S (initial_tagged_module VE σ0) (PossOk v0 []) -> RCompLinErr M VE σ0 VF v0.
Record CallTripleE … := { cte_triple : CallTriple …; cte_noerr : … Error VE (untag m) σ -> poss_steps VF p PossError }.  (* licensed form *)
Theorem m8_gap : (exists I R G, RLHL2Hyps (VE := EIhl δlock) … Mbad …) /\ ~ RCompLinErr Mbad (EIe δlock pre_lock) … (EIe δG preG) ….
```

## Writer sub-tasks

Acceptance for every task:
- builds with `/opt/homebrew/bin` Rocq 9.3.0;
- `_CoqProject` is updated and the Makefile regenerated;
- no `Admitted`, `Axiom`, `vm_compute` or `native_compute`;
- headers state the K/S/P/R levels and the axioms;
- `RelaxedHoareCounterXY.v` and `RelaxedHoareInherit.v` are not edited.

| ID | Scope | Targets | Accept when | Risks |
|---|---|---|---|---|
| **3c.1** | `models/simlin/RelaxedHoareLayer.v` (after `RelaxedHoareCompLinSpec.v`) | Layer file statements above | all Closed | name clashes (`vf_path_cons_inv` exists in ViewLHL and RelaxedHoareCompLin; `lift_*`): qualify names. About 300 lines, 1 iteration |
| **3c.2** (parallel) | `examples/Relaxed/RelaxedHoareClientSB.v`, part 1 | `mcl_trace`, `mnw_trace`, `ucount` position lemmas, `ei_sb_cycle`, `sb_client_spec`, `sb_nowait_si_decides` | Closed, or `eq_rect_eq` only and documented | inversion on dependent `Wait (MkFutureRef op h)`: use `cc_trace`-style views (`RelaxedHoareCompLin.v:450-566`); compare results through nat projections. About 700–1000 lines, 2 iterations |
| **3c.3** | `models/simlin/RelaxedHoareAbsorb.v`, part 1 | `produced_inv_answered`, `unabsorb` | Closed; no inhabited-arity hypothesis | deferring each inner V-inv into the next ModLTS step. About 400–600 lines, 1–2 iterations |
| **3c.4** | same file | `rehandle`, `ccimg` (with a snoc lemma), `CCClosed`, `ei_ccclosed`, `eihl_ccclosed`, `absorb_needs_closure` | Closed | relation between EI pending lists (multiset with extra records); start state `(s0,[])`. About 300–500 lines, 1 iteration |
| **3c.5** | same file | `absorb`, then `absorb_ei`, `saturate_ei`, `cc_idem_ei`, `rcomplin_paper`, `rlhl_sound_paper(_rel_lin)` | assumptions ⊆ {classic} (+ `eq_rect_eq` only for `_rel_lin`) | **Highest risk.** Checkpoint first: state `AbsInv` and prove the frontier lemma alone. Its cases: composite-pending y (`ii_no_overtake`); y composite-emitted but target-pending (`ii_order` or the inner idF crossing, ¬¬SI vs ¬SI); (F3) by the invariant clause "composite-emitted response ⇒ target-emitted"; (F1) by `ii_used_nodup`. Inner idF invariant: a generic `CCInv` without EI fields (`scc_underlay`'s NNPP brings `classic`). The idF case is an internal milestone, not a deliverable. About 1200–2000 lines, 3–5 iterations |
| **3c.6** | `models/simlin/RelaxedHoareLink.v` | Link file statements above; tower test: a `ren_rlhl2` swap layer over `cxy_rlhl2` (3 levels), with a non-trivial trace in the composite via `modlts_trlts` | `verimpl_vcomp` Closed; others ⊆ {classic} | low. About 300–500 lines, 1 iteration |
| **3c.7** | ClientSB, part 2 | `sb_client_modular`, `sb_client`, `sb_client_live`, `sb_nowait_00` | ⊆ {classic}; header says it covers all executions, uses the spec only, and lists the B-1 caveats | building the witnesses (sequential `M_cxy` run in the `sb_exec` style). About 400–700 lines, 1–2 iterations |
| **3c.8** | `RelaxedHoareCompLinErr.v`, `RelaxedHoareErrRLHL.v`, `examples/Relaxed/RelaxedHoareLockErr.v` | m-8 statements above | only after D5; inclusion lemmas; both halves of `m8_gap`; one positive renaming-lock instance | extending `rinv_exec`/`reify` up to `PossError`. About 1500–2500 lines, 4–6 iterations |
| **3c.9** (research) | `examples/Relaxed/RelaxedHoareFSide.v` | `fside_not_saturated : ∃ E F VE σ0 M s, RTraces (ModLTS VE M) (init σ0) s ∧ ¬ MTraces VE M σ0 s` | Closed, or classic | the negative half needs a full inversion. About 300–500 lines |
| **3c.10** | headers, `concern-matrix.md`, paper mapping | correct `RelaxedHoareCompLin.v:186-189` and `RelaxedHoareGSim.v` item 10(a); B3/B4/Meta-3 rows | orchestrator diff check | — |

Critical path for M-22 plus the client: 3c.1 → 3c.4 → 3c.5 → 3c.6 → 3c.7, with 3c.2 and 3c.3 in parallel. That is roughly 3,500–5,500 lines and 8–12 iterations. A estimated about 3,300 lines and C up to 3,000 lines for absorption alone; the panel's absorption estimate lies between the two.

## Research-level decisions for the author

- **D1. Semantic layering.**
  - (a) The composite is `ModLTS`: "N over M", an LTS, not a module E→G.
  - (b) Add a module-call or inlining construct to `RelaxedLang`. This needs asynchronous inlined bodies, because `Future` returns at once; that is a large change.
  - Consequence: `relaxedlin.tex:62-70` ("Inlining … ⟦M;N⟧ = ⟦M⟧;⟦N⟧ … associative") cannot be cited as mechanized; `modlts_trlts` gives the interaction-and-hiding reading.
  - **Recommend (a).**
- **D2. Scope of saturation (`Appendix/relaxedlin.tex:53-56`).**
  - **E-side:** proved only over `CCClosed` presentations. It is false in Coq for handle-sensitive underlays, by (R).
  - **F-side (panel finding, informal, to be mechanized in 3c.9):** take E with SI_E = ∅ over a counter EI; F with SI_F(a,b); M with a ↦ e and b ↦ e.
    - The copy-cat over M can deliver b to M first, so b gets 0 and a gets 1.
    - Directly, M's (F2) order is e(a) before e(b), so the overlay trace inv a, inv b, res b 0, res a 1 is impossible.
    - So ⟦M⟧;cc_F ⊄ ⟦M⟧ without SI inheritance.
  - Options: (a) restrict the proposition to the E-side over specification presentations; (b) add an inheritance hypothesis to the F-side (open, cost unknown); (c) keep it as printed (not supportable).
  - **Recommend (a).** `Appendix:58-62` uses only the E-side.
- **D3. Form of verimpl (`relaxedlin.tex:74`).**
  - (a) Copy-cat form `VerImpl` (CCRefines).
  - (b) Relaxed-linearizability form. This needs rel_lin ⊆ ν;cc, the open M-20 converse, and REW for prefixes.
  - **Recommend (a)**, rewording :74 and the second rule of prop:vertical-composition (copy-cat inclusion instead of ⇝rlx); keep (b) recorded as open.
- **D4. Form and choice of client.**
  - (a) A semantic theorem, modular over CCRefines (planned).
  - (b) An RLHL proof of the client into a nondeterministic SB spec (about 1000 extra lines; not stronger for Reviewer B).
  - (c) The promised SeqLock a=b client (B4 :533), which addresses B's "nontrivial" (:214).
  - **Recommend (a) now and (c) as the paper's flagship** once SeqLock on COH has a VerImpl-compatible interface.
  - The Counter_xy object is a renaming (B-1 (4′)) and its memory is SC with COH-style SI, so the paper must not present this client as weak-memory client verification against RC11.
- **D5. m-8 bundle.** None of this has been put to the author yet.
  - (i) Accept the implementation-side obligation. It is built into `MTracesE`/`RCompLinErr` as in CompLin; the RLHL side needs `cte_noerr`.
  - (ii) `EIe` with an explicit `pre`. Recommended (B's D4): with "no δ successor = error", a held-lock acquire, which is blocking today, would become an error.
  - (iii) The licensed form of `cte_noerr`. Recommended: it is needed for any layer that forwards a precondition; the strict form is a special case.
  - (iv) Tag `TErr` with `(k, op)`. Recommended: this keeps CompLin's projection for horizontal composition; a bare tid tag loses it.
  - (v) Layering with errors (`ModLTSE`) is outside RLHL-3c. Recommended: VerImpl is stated for error-free specs only.
  - (vi) In `GSimRelErr`, let `PossError` absorb everything, as in SC CompLin. Recommended, with low confidence; this is a Writer-level detail.
- **D6. Prefix or complete runs.** The client theorem holds for all executions (via absorption). The rel_lin corollaries stay complete-only. **Recommend all executions.** The fallback C route gives complete runs only.
- **D7. What may be claimed after 3c.**
  - "Vertical composition of RLHL-verified layers over sequential-specification (EI) interfaces, in copy-cat form."
  - "E-side saturation over specification presentations."
  - "A client of a relaxed object verified from its specification and transferred to the implementation."
  - Not: syntactic inlining, F-side saturation, rel-lin-quantified verimpl, or RC11.
- **D8. Order.** M-22 and the client before m-8, because m-8 is blocked on D5. **Recommend this order.**

## What the panel disagreed about, and how it was resolved

1. **Is absorption on the client's critical path?** C said no; A and B said yes.
   - **Resolved: yes.** `verimpl_of_rlhl`'s only non-trivial open assumption is `absorb_ei`, now that `modlts_paths` is proved (scratch `Print Assumptions`).
   - C's composition requires layer 2 to be verified over cc;EI, which RLHL never gives. C's client is complete-only (`cc_rel_lin` needs `complete`).
   - C's route is kept as the fallback.
2. **Generic `CCClosed` (A) or EI-specific re-timing (B)?** **Resolved: A.**
   - The FreeLTS target plus `exec_transport` keeps scheduling and VF reasoning apart.
   - Responses never need to be delayed: a response is on the frontier as soon as its invocation is emitted (`must_precede` Res–Res is False, and Inv–Res only on the same handle; `RelaxedModuleSemantics.v:252-259`).
   - The cost is one `classic` case split on the match. That axiom is in the baseline.
3. **Pilot for idF (review order, A) or not (B)?** **Resolved:** the general theorem is the deliverable and the idF case is a corollary (`cc_idem_ei`). Over idF, the general proof adds only the (F3) clause and `produced_inv_answered`.
4. **TLTS (C) or ModLTS/Lift (A, B)?** **Resolved: both, with ModLTS primary.**
   - `modlts_trlts` makes them equal on every finite trace, which removes C's `link_joint` worry.
   - TrLTS stays as the tool for building witnesses (membership by `mtraces_prefix`).
5. **Does `cc_unit_left` need an inhabited arity and `classic` (C), or neither (A, B)?** **Resolved for A and B.** `program_terminal` requires `all_resolved` (`RelaxedSemantics.v:251-254`), so the inner commit can be read off M's own trace.
6. **How to prove the spec-level client lemma: EI value lemmas (A, B) or a rel_lin cycle (C)?** **Resolved: EI path lemma**, which holds for all executions. The rel_lin variant is an optional cross-check.
7. **`EIe` definition: "no successor" (A, C, review) or explicit `pre` (B)?** **Resolved: `pre`** (D5 ii).
8. **`TErr` tag: tid (B), key (C), or key+op (A)?** **Resolved: key+op.**
9. **F-side of saturation.** A asked whether it is needed; B said not needed. **Panel addition:** it is probably false; mechanize the counterexample (3c.9) and tell the author (D2).
10. **The same-thread case of the client.** A invoked (F2). **Resolved: not needed**: the cycle uses only per-call (F3) edges and EI values.
11. **Effort.** The estimates for absorption differed; see the absorption row (3c.5) in the sub-task table.

## Feasibility checks I ran

All in a piped `rocq repl` from the repository root with the `_CoqProject` `-R` flags, Rocq 9.3.0. Nothing was written to disk.

- **Toolchain and build.**
  - `rocq --version` gives 9.3.0.
  - `make -n` lists only `structures/DCPOs.v`.
  - The `.vo` files of RelaxedHoareCompLin, CompLinSpec, Inherit and CounterXY are newer than their sources.
- **`mtraces_mono`.** The 5-line proof via `ViewLHL.exec_underlay_path`/`exec_transport` is accepted. `Print Assumptions mtraces_mono`: "Closed under the global context".
- **`modlts_paths`.** Proved with `exec_app`, `paths_exec` and `exec_paths` (about 40 lines). `Print Assumptions modlts_paths`: "Closed under the global context".
- **Nesting.**
  - `ModLTS (ModLTS (ModLTS VE M1) M2) M3 : LTS H` typechecks.
  - `ModLTS (RelaxedHoareSpec.EI δmem) M_cxy : LTS FC` typechecks.
  - `MTraces (TrLTS (MTraces (EI δmem) M_cxy (s00,[]))) idF []` typechecks.
- **`VerImpl`.**
  - `verimpl_vcomp`: "Closed under the global context".
  - `verimpl_of_rcomplin` and `verimpl_of_rlhl`, with `modlts_paths` and `absorb_ei` as toplevel `Axiom`s, report the axioms {modlts_paths, classic, absorb_ei}.
- **Statements that typecheck:** `ccimg`, `CCClosed`, `absorb`, `unabsorb`, `modlts_trlts`, `GS`, `Mcl`, `Mnw`, `sb_client`, `sb_client_spec`, `sb_nowait_00`.
- **Assumptions of existing results.**

  | Result | Axioms |
  |---|---|
  | `cxy_complin_ei`, `cc_trace_wf`, `scc_underlay` | classic |
  | `cc_rel_lin` | eq_rect_eq, classic |
  | `RelaxedLTSSpec.ResEvInversion` | eq_rect_eq |
  | `hlift`, `mtraces_prefix`, `cc_trace`, `instrument`, `iinv_reach`, `sb_exec`, `sb_not_rel_lin0` | Closed |

- **Source checks.**
  - **Frontier.** `must_precede` Inv/Inv is `~ semi_independent E op1 op2` whatever the tags (`RelaxedModuleSemantics.v:252-259`). The positional `module_error` is the only error rule (`:464-470`).
  - **Program semantics.**
    - `tagged_invoke` runs the body to completion prophetically (`:578-592`).
    - `FutureRef` exposes the raw handle (`future_handle`, `RelaxedLang.v:25`), so counterexample (R) is valid.
  - **Specs and simulation.**
    - `ei_step` (`RelaxedHoareSpec.v:307-313`); `EI.Error := False`.
    - `gsim_step` requires `PossOk` (`RelaxedGSim.v:340-350`), so `PossError` is unreachable today.
    - `CompLin` puts `TErr` in `ImplTraces`, which is the implementation-side obligation (`CompLin.v:122-168`).
  - **Client evidence.**
    - `LockedRegisters.sb_forbidden` is an object-level trace property that assumes the underlay is rel_lin; it is not a client program.
    - Author response B4 (`popl2027-reviews.md:531-533`) promises SeqLock a=b.

Not run, because each needs a scratch file the orchestrator would have to approve: the proofs of `trlts_paths` and `ei_ccclosed`, the F-side counterexample, and the absorb frontier checkpoint. Treat the absorption feasibility as argued, not checked.