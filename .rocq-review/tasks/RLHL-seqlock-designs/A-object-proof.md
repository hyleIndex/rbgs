# Two SeqLocks on COH with LB: RLHL design (Part A)

## 0. Main findings

1. **With an RMW lock acquire, the implementation never exhibits LB across two SeqLocks.** I checked this by hand against `must_precede` and the repl `dto` table (section 7).
   - `dto rc Rmb DRMW = true`. Under `SL.plainTL` (acq/rel = DRMW), a write's `acq` cannot overtake an earlier pending read's `rmb` in the same thread.
   - So in `t1: read_1; write_2`, all of `read_1`'s data reads (in every iteration, since traces are prophetic) are emitted before `write_2` starts. The same holds for `t2`. That gives a cycle.
   - The overlay contract (read ↦ Rmb, write ↦ Wmb, cross-object) admits LB, but plainTL does not exhibit it. This is the same situation as LatchSet's unused I_L.
   - **The orchestrator's rationale in research-intent.md §8 ("actually exhibited by the implementation") is false for plainTL.**
2. **LB is exhibited when the lock categories satisfy `dto Rmb k_acq = false` and `dto k_rel Rmb = false`.** Example: `wTL := {k_acq := DW; k_rel := DW; k_gt := DR; k_tt := DR}`.
   - `SL.K_ok wTL = true`.
   - `exportable rc DW DRMW` holds for both `rc` (checked), and DW is ordered with a subset of what DRMW is ordered with. So wTL is a legitimate weakening of the TicketLock contract.
   - But no faa-based lock over COH realises this reorder.
3. **One RLHL proof covers every K with `K_ok K`.** The proof is parametric in K and works for every overlay relation `si ⊇ need rc K`. It produces a mechanizable table:

   | K \ SI_F | ∅ | `osi rc` |
   |---|---|---|
   | plainTL | ✓ | ✓ |
   | wTL | ✗ (universal negative via LB) | ✓ |

   For plainTL, "LB is not a module trace" then follows from the ∅ instance, with no separate trace argument.
4. **The read's linearization point (LP) must be the final `rmb_b`, not `test_ticket`.** This is needed for the plainTL/∅ cell. With the LP at `tt`, plainTL needs `SI_F(read, write)`, because `rel_i` can pass a pending `tt_j`. The value is still validated at `tt`, through records.

## 1. Writer exclusion: recommend (ii), using the vocabulary of (iii)

The TicketLock is a sequential spec of blocking EI operations. Its categories are a parameter `K : SeqLockCOH.TLCats` with `SL.K_ok K = true`, exactly as in `SeqLockCOH`. Instances get separate locks and cells; barriers are shared.

- **Why (ii).**
  - No P1 guard (`M_Lw`/`div`), so the theorems are unconditional.
  - The implementation never misuses the lock. EI has `Error := False`, so m-8's implementation-side error obligation is vacuous here, as for LatchSet. In EI, a blocked `acq` simply has no step.
  - It is the paper's object: Appendix/SeqLock.tex:3 builds SeqLock on a ticket lock.
- **Why not (i), single writer.**
  - The writer must read `seq` (DR), which is ordered after an earlier `rmb`. So LB is blocked in the same way.
  - A writer-private counter would need a new "Local" location and P1.
- **Why not (iii) literally.** `SeqLockProg.M rc K` has these drawbacks:
  - it has one instance plus a client cell z;
  - it uses positional `Future` tags, which are stricter than the author's "dependency-only waits";
  - with z in the overlay, LP(write) = `rel` fails readiness: `zw` can pass a pending `rel` but is not SI_F with `write`, since `dto Wmb DW = true`. That would need LP(write) = `wmb_b`.
- **What is reused from (iii):** `SL.TLCats`, `SL.K_ok`, `SL.plainTL`, `SL.dto_W_wmb`/`dto_wmb_W`/`dto_R_rmb`/`dto_rmb_R`, and the code shapes of `SeqLockProg.write`/`read_body`.

## 2. Objects and module

I typechecked all of this in a piped repl (section 7). It goes in the new file `examples/Relaxed/RelaxedHoareSL2Prog.v`.

```coq
Inductive Loc := LTL (i : nat) | LX (i : nat) | LY (i : nat).
Inductive LOp := lAcq (i : nat) | lRel (i : nat) | lGt (i : nat) | lTt (i s : nat)
  | lWrX (i v : nat) | lWrY (i v : nat) | lRdX (i : nat) | lRdY (i : nat) | lWmb | lRmb.
Definition lar (o : LOp) : Type := match o with lGt _ | lRdX _ | lRdY _ => nat | lTt _ _ => bool | _ => unit end.
Definition loc (o : LOp) : option Loc := (* TL_i for acq/rel/gt/tt; X_i, Y_i; None for barriers *)
Definition lcat (K : SL.TLCats) (o : LOp) : WT.DCat :=
  match o with lAcq _ => SL.k_acq K | lRel _ => SL.k_rel K | lGt _ => SL.k_gt K | lTt _ _ => SL.k_tt K
  | lWrX _ _ | lWrY _ _ => WT.DW | lRdX _ | lRdY _ => WT.DR | lWmb => WT.Wmb | lRmb => WT.Rmb end.
Definition sindep rc K (o o' : LOp) : Prop := (same_loc o o' || WT.dto rc (lcat K o) (lcat K o')) = false.
Definition E2 rc K : RelaxedSig.t := {| effect := LSig; handle := nat; semi_independent := sindep rc K; mode := fun _ => Local |}.
Definition Regs := Loc -> nat.   Definition regs0 : Regs := fun _ => 0.
Definition δ2 (m : Regs) (o : LOp) : lar o -> Regs -> Prop := match o with
  | lAcq i => fun _ m' => Nat.even (m (LTL i)) = true /\ m' = upd m (LTL i) (S (m (LTL i)))   (* blocking *)
  | lRel i => fun _ m' => Nat.odd (m (LTL i)) = true /\ m' = upd m (LTL i) (S (m (LTL i)))
  | lGt i => fun r m' => r = m (LTL i) /\ m' = m
  | lTt i s => fun r m' => r = (Nat.odd s || negb (Nat.eqb (m (LTL i)) s)) /\ m' = m
  | lWrX i v => fun _ m' => m' = upd m (LX i) v   | lWrY i v => fun _ m' => m' = upd m (LY i) v
  | lRdX i => fun r m' => r = m (LX i) /\ m' = m  | lRdY i => fun r m' => r = m (LY i) /\ m' = m
  | lWmb | lRmb => fun _ m' => m' = m end.
Definition wTL : SL.TLCats := {| SL.k_acq := WT.DW; SL.k_rel := WT.DW; SL.k_gt := WT.DR; SL.k_tt := WT.DR |}.

Inductive OOp := oWrite (i vx vy : nat) | oRead (i : nat).
Definition oar (o : OOp) : Type := match o with oRead _ => (nat * nat)%type | _ => unit end.
Definition ocat o := match o with oWrite _ _ _ => WT.Wmb | oRead _ => WT.Rmb end.
Definition osi rc (o o' : OOp) : Prop := inst o <> inst o' /\ WT.dto rc (ocat o) (ocat o') = false.  (* paper-style *)
Definition need rc K (o1 o2 : OOp) : Prop := match o1, o2 with      (* older o1, younger o2 *)
  | oWrite j _ _, oRead i => j <> i /\ WT.dto rc (SL.k_rel K) WT.Rmb = false
  | oRead j, oWrite i _ _ => j <> i /\ WT.dto rc WT.Rmb (SL.k_acq K) = false
  | _, _ => False end.
Definition F2si (si : OOp -> OOp -> Prop) : RelaxedSig.t := {| effect := OSig; handle := nat; semi_independent := si; mode := fun _ => Local |}.
Definition A0 : nat -> nat * nat := fun _ => (0, 0).
Definition δsl (A : nat -> nat * nat) (o : OOp) : oar o -> (nat -> nat * nat) -> Prop := match o with
  | oWrite i vx vy => fun _ A' => A' = (fun j => if Nat.eqb i j then (vx, vy) else A j)
  | oRead i => fun r A' => r = A i /\ A' = A end.
Lemma need_plain rc o1 o2 : ~ need rc SL.plainTL o1 o2.      (* checked *)
Lemma need_wTL rc o1 o2 : need rc wTL o1 o2 <-> osi rc o1 o2.  (* checked *)
Lemma need_osi rc K o1 o2 : need rc K o1 o2 -> osi rc o1 o2.   (* checked *)

(* machines for RelaxedHoareRun.run; only data-dependency tags: tt ← gt *)
Definition wnext i vx vy (st : WSt) : SStep LSig WSt unit :=  (* acq; wmb; wrX; wrY; wmb; rel, all dix [] *)
Definition rnext i (st : RSt) : SStep LSig RSt (nat * nat) :=
  (* RGt b: gt [] | RRa: rmb [] | RRx: rdX [] | RRy: rdY [] | RRb: rmb [] | RTt b s a c: SCall (lTt i s) [b] (fun r => if r then RGt (b+6) else RDone a c) *)
Definition M2 rc K si : RelaxedModuleImpl (E2 rc K) (F2si si) := fun op _ => match op with
  | oWrite i vx vy => run (wnext i vx vy) [] (W 0) | oRead i => run (rnext i) [] (RGt 0) end.
```

Design notes:
- **Instances.** Instances are indexed by `i : nat`. The cost is the same as for two, and LB uses i = 1, 2.
- **Order comes from F2 alone.** F2 together with `K_ok` gives all the in-call order:
  - writes: acq → wmb_a → {wrX, wrY} → wmb_b → rel;
  - reads: gt → rmb_a → {rdX, rdY} → rmb_b → tt;
  - successive TL operations of one instance are ordered by same location.
- **Only `tt` needs a tag (on `gt`).** It makes `s` equal the `gt` record.
- **No client cell z** in the first deliverable (section 1).

## 3. The RLHL proof

### 3.1 Linearization points (identified through the ghost, as RLHL-latch RD-7)

- **Write.** LP = emission of its unique `lRel i`. Steps: `psa_inv (oWrite i vx vy)`, then `psa_ret tt` in `RetCond`.
- **Read.** LP = emission of an `lRmb` of k after which k owns no pending `lRmb` entry in γ′. Since Rmb/Rmb is F2-ordered, this is the final iteration's `rmb_b`.
  - Take `psa_inv` unconditionally, with result `A_lp := A i`.
  - The finality case split is decidable: owners are `positive * nat`, so no `classic` is needed.

### 3.2 Invariant `I2 rc K si` (frozen in S.2)

`I2 s := ∃ A Pf pool, ps_poss s = PossOk (A, Pf) pool` with the following clauses:

- **(a) Bookkeeping, taken from `Iren`:**
  - `lin_pool_well_formed`;
  - `RelaxedHoareRun.GAge pool γ`;
  - `eihl_rec_used δ2 σ`;
  - `Forall gwf γ`;
  - the overlay EI records ↔ `ls_lini` entries, with keys `NoDup`.
- **(b) Coupling.**
  - Read k: `ls_inv` ⟺ k owns a pending `lRmb`.
  - Write k: `ls_inv` ⟺ k owns a pending `lRel i`.
- **(c) Shapes.**
  - A call's entries are on its own instance or are barriers.
  - **TTfollow:** every pending `lRmb` of a read k is followed later in γ by a pending `lTt i` of k.
  - A write owns at most one `lAcq`/`lRel`, and "acq pending ⟹ rel pending".
  - All of these hold at invocation by the footprint Ω (see the method obligations below).
  - They are maintained generically, because `ghost_emit` checks the call's own earlier entries too.
- **(d) Per instance i.**
  - `J i : Nat.even (m (LTL i)) = true -> (m (LX i), m (LY i)) = A i`.
  - `LockInv i : (Nat.odd (m (LTL i)) = true <-> ∃ k, Holder i k) /\ Holder i unique`.
  - Here `Holder i k := k ∈ pool with op oWrite i _ _ ∧ ¬ owns pending lAcq i ∧ owns pending lRel i`.

**Footprints Ω** (the `MethodProvable` field `Ω h (own_invs Γ)`):
- `Ω_read`: there is at least one `lRmb`, and every `lRmb` is followed by an `lTt i`.
- `Ω_write`: exactly one `lAcq i` and one `lRel i`.
- Both are computed by `own_invs_run`.

### 3.3 Rely and guarantee (frame style, like `Rren`/`Gren`, plus three clauses)

`R2 k`:
- memory moves by `eihl_steps δ2`;
- k's pool entry and k's overlay records are kept; k's ghost entries are unchanged;
- **Mono:** `∀ i, own_i ≤ own_i' ∧ (own_i' = own_i → A' i = A i)`;
- **HolderProt:** `Holder i k s → own_i, x_i, y_i unchanged`.

`G2 k` is the dual (other calls' entries kept), with HolderProt for every `k' ≠ k`.

Discharges:
- At `acq`, HolderProt holds because `own_i` is even, so by `LockInv` there is no holder.
- At `rel` and `wrX`, the emitter is the unique holder.
- `h_guar_rely`, `h_invoke_rely` and `h_return_rely` are routine: `A` is unchanged, and the new entries belong to a fresh, younger key.

### 3.4 Value argument (records, through the `eihl_mine` frame kit)

- **gt post:** `eihl_mine κg (Op κg (lGt i) sg) ∧ sg ≤ own_i`. Stable by Mono.
- **rdX post:** `∃ ax, eihl_mine κx (Op κx (lRdX i) ax) ∧ (own_i = sg → Nat.even sg = true → ax = fst (A i))`.
  - It is established by `J i`.
  - It is stable because, when `own_i` is unchanged, `A i` is unchanged (Mono).
  - It reaches `rmb_b` along the edge rdX→rmb_b (DR→Rmb).
- **LP post:** `lin_lookup k (ls_lini (oRead i)) ∧ In (Op k (oRead i) A_lp) Pf ∧ sg ≤ own_i ∧ (own_i = sg → even sg → (ax, ay) = A_lp)`.
- **At `tt`:**
  - the tag gives the `gt` response, so `s = sg` (`eihl_mine_res`);
  - the record `r_tt = odd s || own_i ≠ s`;
  - so the post is `r_tt = false → (ax, ay) = A_lp`.
- **At return.**
  - The responses identify `ax`, `ay` and `r_tt` with the path's values. `r_tt = false` holds on the final path.
  - Then `psa_ret` consumes `Op k (oRead i) (a, b)`.
  - A non-final `rmb` cannot have been the LP: by coupling (b), a lini read owns no `lRmb`, which contradicts the `ghost_emit` of the current `rmb`.
- **Write.**
  - `wrX` post: `m (LX i) = vx`, stable by HolderProt.
  - At `rel`: `J i` is re-established with `A' i = (vx, vy)`, and `LockInv` holds.

### 3.5 Readiness

For an LP emission `ev` of k on thread t, and every older same-thread `ls_inv` call k1:

| k1 (older) / k (LP) | pending LP entry of k1 | argument | SI_F used |
|---|---|---|---|
| read_j / read_i (LP `rmb_b`) | `lRmb` | Rmb/Rmb `inv_blocks ev` | none |
| write_j / read_i | `lRel j` | if `dto k_rel Rmb`: blocks `ev`. Else, j = i: `rel_i` (TL_i) would have blocked the `gt_i` record. Else j ≠ i | `need` (wTL) |
| read_j / write_i (LP `rel`) | `lRmb` (and `lTt`, by TTfollow) | if `dto Rmb k_acq`: `lRmb` would have blocked the `acq_i` record. Else, j = i: `tt_i` (TL_i) would have blocked `acq_i`. Else j ≠ i | `need` (wTL) |
| write_j / write_i | `lRel j` (isW) | would have blocked the `wmb_b(i)` record (`dto_W_wmb`) | none |

**Records.** `RecNB P k ev γ := ∀ e ∈ γ, key_older (lin_domain P) (se_owner e) k → ¬ inv_blocks (se_event e) ev`.
- It is established at the emission of `gt`, `acq` and `wmb_b`, from `ghost_emit` plus `gage_before`.
- It is stable: older entries are only removed, and new entries belong to younger keys.
- It travels along in-edges to the LP.

**Inheritance answer.** The "younger write_2 before older read_1" case needs `SI_F(read_1, write_2) = (1 ≠ 2 ∧ dto Rmb Wmb = false)`, which holds. It is used only when `dto Rmb k_acq = false`.

`emit_ready_SI` does **not** apply. Pairs such as (rel_j, rel_i) or (tt_j, tt_i) are underlay-SI but not overlay-SI, so the new mixed lemma below is required.

```coq
Theorem emit_ready_mixed {E F} (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
  lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
  γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 -> Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
  (forall k1 o1, fst k1 = t -> key_older (lin_domain P) k1 (t, h) -> lin_lookup k1 (ls_inv o1) P ->
     semi_independent F o1 o \/ exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) ->
  exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
```

The record cases discharge the premise by deriving `False`. `emit_ready_block_older` (`RelaxedHoareRun.v:741`) becomes a corollary.

### 3.6 Which own-event interference (`ns_if`) premises are genuine

Only frame facts are genuine. All other pairs are vacuous by `before` (the dag order).

- **wrX ∥ wrY:** different locations.
- **rdX ∥ rdY:** a record is added.
- **Any response ∥ any edge:** a record is consumed (`eihl_mine_step`).
- **The read LP ∥ pending response edges:** the pool and overlay records change.
- **Late responses of iteration n ∥ edges of n+1.**

None needs `Stable_true`. One "own frame" lemma in S.2 covers all of them.

### 3.7 Use of `rp_run`

- Use `run_method_provable` with a machine invariant `Inv h st cs Γ H` that pins only the current iteration's slots.
- Earlier-iteration in-edges get `sl_in := True`. All Rmb/R/TL predecessors are earlier; finality is carried by I2(b), not by edges.
- `dprec_run` computes the edges:
  - Inv–Inv iff ¬`sindep`;
  - `Res gt → Inv tt` from `dix [b]`;
  - Inv→Res for each call.
- Record-value extractors `natv`/`boolv` follow `RelaxedHoareLatchProg.opval`, to avoid `eq_rect_eq`.

### 3.8 Main statement

```coq
Theorem sl2_rlhl2 rc K si : SL.K_ok K = true -> (forall o1 o2, need rc K o1 o2 -> si o1 o2) ->
  RLHL2Hyps (VE := EIhl (E := E2 rc K) δ2) (VF := RelaxedHoareSpec.EI (F := F2si si) δsl)
    (I2 rc K si) (R2 rc K si) (G2 rc K si) (M2 rc K si) ((regs0, []), []) (A0, []).   (* closed *)
```

This shape typechecks; section 7 check 3 used an abbreviated E2.

## 4. Corollaries, LB and the table

```coq
Corollary sl2_complin rc K si HK Hsi : RCompLin (M2 rc K si) (EI δ2) (regs0, []) (EI δsl) (A0, []).  (* {classic}; every prefix *)
Corollary sl2_rel_lin rc K si HK Hsi s : MTraces (EI δ2) (M2 rc K si) (regs0, []) s -> PrefixView.complete s ->
  rel_lin (@PrefixView.sel (F2si si)) s si (seq_legal δsl A0).                          (* {classic, eq_rect_eq} *)
Corollary sl2_osi rc K : SL.K_ok K = true -> RLHL2Hyps … (si := osi rc) …                 (need_osi)
Corollary sl2_plain_empty rc : RLHL2Hyps … (K := SL.plainTL) (si := fun _ _ => False) …  (need_plain)
Definition lb2 si : list (ThreadEvent (F2si si)) :=   (* t2: inv read 2; inv write 1 (1,1); res write 1;
   t1: inv read 1; res (1,1); inv write 2 (1,1); res; t2: res read 2 (1,1) *)
Theorem lb2_exec rc si : MTraces (EI δ2) (M2 rc wTL si) (regs0, []) (lb2 si) /\ PrefixView.complete (lb2 si).   (* closed *)
Lemma lb2_not_rel_lin0 : ~ rel_lin sel (lb2 ∅) (fun _ _ => False) (seq_legal δsl A0).   (* legality cycle; closed *)
Theorem wtl_empty_no_rlhl2 rc : forall I R G, ~ RLHL2Hyps … (K := wTL) (si := ∅) ….      (* universal negative *)
Theorem lb2_not_exhibited_plain rc si : ~ MTraces (EI δ2) (M2 rc SL.plainTL si) (regs0, []) (lb2 si).
  (* sl2_plain_empty + RelaxedHoareResig.mtraces_resig_iff + lb2_not_rel_lin0 *)
Theorem sl2_si_table rc : …  (* the 2×2 table *)
```

How `lb2_exec` runs:
- `t2`'s `write_1` (12 events) crosses all 12 queued events of `read_2`. This needs `DR→DW`, `Rmb→DW`, `DR→Wmb` and `Rmb→Wmb` all false, which they are.
- Each call returns.
- The tactics are ports of `ex_step`, `m_step`, `m_next`, `cross_ok`, `sindep_ok` and `m_return` (`RelaxedHoareLatchProg.v:791-870`).

Non-vacuity witnesses: one read retry, and one same-thread overlap in which a younger write returns before an older read.

## 5. Writer tasks

Common criteria for every task (as in RLHL-latch §3):
- Rocq 9.3.0 with `PATH=/opt/homebrew/bin:$PATH`;
- `_CoqProject` updated;
- no edits to existing `.v` files;
- no `Admitted`, `Axiom`, `vm_compute` or `native_compute`;
- a K/S/P/R header with `Print Assumptions`.

| ID | Files | Targets | Accept when | Size / iterations |
|---|---|---|---|---|
| S.0 (‖ S.1) | `models/simlin/RelaxedHoareReady.v` | `RecNB`, `recnb_establish`/stability; `emit_ready_mixed`; "a key's ghost entries are never re-added" | closed; `emit_ready_block_older` re-derived | 250–400 / 1 |
| S.1 | `examples/Relaxed/RelaxedHoareSL2Prog.v` | section 2; `need_*`; `natv`/`boolv`; ported execution tactics; produce-examples for write, read and a retry; one reorder example | closed; body text matches section 2 | 500–800 / 1 |
| S.2 (after S.0, S.1) | `…/RelaxedHoareSL2Inv.v` | `I2`, `R2`, `G2`, `Holder`, `LockInv`, `J`, coupling, shapes; the four `h_*` rely fields, `h_ok`, `h_init`; own-frame kit; per-event maintenance lemmas; `ready_read`/`ready_write` (section 3.5) | closed; statements frozen | 900–1,400 / 2 |
| S.3 (checkpoint) | `…/RelaxedHoareSL2Read.v` | `read_provable : MethodProvable … t (oRead i) Ω_read Q_read` via `rp_run`; the loop through `RGt (b+6)` | closed; header lists the genuine `ns_if`/`bw_if` premises. **Over 1,500 lines or 3 iterations: stop and fall back to route S (direct `MethodSem`)** | 1,000–1,500 / 2–3 |
| S.4 (‖ S.3) | `…/RelaxedHoareSL2Write.v` | `write_provable` | closed | 700–1,100 / 2 |
| S.5 | `…/RelaxedHoareSL2.v` | `sl2_rlhl2` via `method_sound`; section 4 positive corollaries | closed / {classic} / {classic, eq_rect_eq} | 250–450 / 1 |
| S.6 (exec after S.1; negatives after S.5) | `…/RelaxedHoareSL2LB.v` | `lb2_exec`, `lb2_not_rel_lin0`, `wtl_empty_no_rlhl2`, `lb2_not_exhibited_plain`, `sl2_si_table`, non-vacuity witnesses | closed / {classic, eq_rect_eq} | 700–1,100 / 1–2 |

**Order.** (S.0 ‖ S.1) → S.2 → (S.3 ‖ S.4) → S.5 → S.6 negatives. S.6's execution part can run right after S.1.

**Total.** About 4,300–6,700 lines and 10–15 iterations.

**Risks:**
- slot volume (6 calls × inv/res × `NewSlotOK`), which the frame-slot builders in S.2 address;
- dependent record values;
- `GAge`/`RecNB` bookkeeping across pool updates;
- `RelaxedHoareRun`/`Resig` are still in flux, so pin names before S.2.

## 6. Research-level points for the author

- **RP-1 (LB claim).**
  - With an RMW acquire (plainTL, the TicketLockCOH export), two-SeqLock LB is admitted by the contract and provably *not exhibited*.
  - It is exhibited with wTL. wTL is a sound weakening of the lock contract, but it is realised only by the abstract underlay spec, not by a faa-based lock.
  - Alternative (C): a single-writer seqcount whose writer keeps its sequence number in a private, Local-category register. That gives LB on pure COH, but needs P1 and a Local location.
  - **Recommend:** deliver the K-parametric table, and word the paper as "the spec admits LB; the module over its underlay spec exhibits it iff the lock is not ordered after rmb".
- **RP-2 (scope).**
  - The underlay is TicketLock ⊗ COH[x_i] ⊗ COH[y_i] ⊗ barriers, in a sequential presentation (as `SeqLockCOH`'s top layer).
  - "Verified on COH" covers the data cells and barriers only.
  - TicketLock-over-COH is window route only, so there is no RLHL layering link.
  - Reviewer B:212 (instruction reordering) and :311-316 (soundness against RC11) are not addressed.
- **RP-3 (LP).** This deviates from Appendix/SeqLock.tex:173 (LP at `test_ticket`):
  - the LP is at the final `rmb_b`, identified through the ghost, so it relies on prophetic traces (as RD-7 for LatchSet);
  - the paper's `tt` LP suffices only for the `osi` column.
- **RP-4 (tags).** The RLHL module uses dependency-only tags. Whether `SeqLockProg.M`'s positional traces are included in them is not proved; this is an optional bridge.
- **RP-5.** `δ2`'s `rel` is thread-blind (`SeqLockCOH.pre` checks the holder). Misuse-as-error would need a thread-aware EI (m-37).
- **RP-6 (client cell).** Adding z needs LP(write) = `wmb_b` plus a "rel follows" shape invariant.

## 7. Checks run (repl, Rocq 9.3.0, nothing written)

1. **`dto` (both `rc`)**, rows = earlier, columns = later, order [DR, DW, DRMW, Rmb, Wmb]:
   - DR: f f f T f
   - DW: f f f f T
   - DRMW: f f f T T
   - Rmb: T f T T f
   - Wmb: f T T f T
2. **Lock categories.**
   - `out_leb`/`in_leb rc DW DRMW = true` for both `rc`;
   - `isR DRMW = isW DRMW = true`;
   - `SL.K_ok wTL = SL.K_ok SL.plainTL = true`.
3. **Definitions.**
   - The section 2 definitions, `need_plain`, `need_wTL`, `need_osi` and `M2` (via `run`) typecheck, and the lemmas are proved.
   - The `RLHL2Hyps (VE := EIhl δ2) (VF := EI (F := F2si si) δsl) … ((regs0,[]),[]) (A0,[])` shape typechecks with an abbreviated E2.

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareRun.v (`run`, `rp_run`, `run_method_provable`, `GAge`, `emit_ready_block_older`, `eihl_done_*`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareBase.v (`ghost_emit`, `CallTriple`, `RLHL2Hyps`) and /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoare.v (`MethodProvable`, `NewSlotOK` via RelaxedHoareDag.v)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v (`EIhl`, `eihl_mine*`, `rlhl_complin_eihl`, `cc_rel_lin`)
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/SeqLockCOH.v (`TLCats`, `K_ok`, `plainTL`, `dto_*` lemmas) and /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/SeqLockProg.v (code shapes)
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareLatchProg.v (execution tactics, `opval` pattern) and /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareResig.v (`mtraces_resig_iff`)