**Verdict:** with the current logic the untagged reader is not derivable.

- **Frozen `Isl`/`Rsl`/`Gsl`/`Qsl`:** not derivable. The argument below is rigorous, with three kernel-checked lemmas. The full three-run construction is not mechanized.
- **Any I/R/G:** not derivable, I believe; this part is argued, not proved. The two load-bearing facts hold for every instance: the certificate splits into independent conjuncts (a theorem), and the rely must contain a step that consumes the reader's own record (argued from two reachable states that are identical).
- **No route without a program or logic change.** Two routes work: (A) tagging the barriers, or (B) an underlay presentation that keeps the values of consumed records.

## 1. Load-bearing definitions

- **The certificate is a conjunction.** `ctx_triple` (Dag.v:816) builds the certificate `Fam Γ fin fin0 tr`. `FamAt` (Dag.v:~640) is a conjunction of independent facts: `fa_I`, the start and in-edges of live slots, `fa_fin d` for every emitted slot `d`, and `fa_fin0`.
  - `bw_sum` (Dag.v:433) derives `Q` from `I ∧ fin0 ∧ ⋀_{response d} fin d` only.
  - Each `fin d` must be stable under `R k` (`bw_R`) and under every slot `g` with `~ before g d` (`bw_if`).
- **Untagged responses have no outgoing edges.** By `dprec_run` (Run.v:509), the only edge into a response is from its own invocation, and an edge leaves a response only into invocations that list it in `dix`. The reader has `dix = []` everywhere, so no response is `before` any other slot. Its value can only enter the context through `fin d`, which reaches `bw_sum` alone.
- **Response values are prophesied.** `RunCallOK` (Run.v:596) quantifies over every response `v`. Later slots know `s, a, c` as meta-values, so the derivation must also cover paths that never occur, such as `(s,a,c,s') = (2,0,1,2)`.
- **What the underlay keeps:**
  - `EIhl` (CompLinSpec.v:980, 1156) binds the value at the invocation, as a pending record.
  - A response deletes that record; the `used` list keeps only `(tid, handle)`, with no operation, value or owner.
  - The ghost forgets the owner at emission (`ghost_emit`, Base.v:287).
  - After consumption `eihl_mine κ x0` holds for every `x0` (`eihl_done_res_mine`, Run.v:1081). So `KDoomRd κ l w` is true and carries no information (lemma (2) in §7).
- **The frozen rely and LP:**
  - `Rsl` (SL2Inv.v:372) moves memory by arbitrary `eihl_steps`, including responses on `k`'s own keys. Lemma (3) in §7 exhibits one such step.
  - `Coup` (SL2Inv.v:303) fixes the read's LP at its last `rmb`, with value `A i` at that moment.

## 2. The obstruction, and a counterexample for the frozen definitions

**Lemma `fam_merge` (kernel-checked, §7).** Take one derivation and two runs that end in the same state `Z`, with remaining-event lists `l1` and `l2`. If every slot was emitted in at least one of the two runs, then `Q Z` holds.

The two runs need not be one execution: each `fin d` is a separate conjunct, justified by whichever run fired `d`. The semantic triple `MethodSem` (route S) does not have this weakness, because its certificate is indexed by `l` and knows which responses have fired.

**Path π.** Reader `k = (t,h)` of `fR 0`, one iteration, meta-values `s = 2, a = 0, c = 1, s' = 2`. Then `rok 2 2 = true`, so `RunCallOK` forces `Close (Qsl k (fR 0) (0,1))`.

**Runs.** Underlay events of `k` alternate with `Rsl` blocks `B1…B5`. Each block is four fresh-key `eihl_steps` on another thread, with fixed keys per block in every run.
- A *write block* `W(v)` writes `Sq_0 += 2` and the data `v`, and sets `A 0 := v`.
- A *dummy block* performs reads of an unrelated location.

Schedule: `B1, q1, ra, B2, x, B3, y, rb (LP), B4, q2, B5`. A response whose record matches the meta-value fires immediately. A doomed record is consumed by an `Rsl` step straight after its invocation; that step is allowed, as `rsl_step` shows.

| Run | Blocks | Records r1/rx/ry/r2 | Genuine | Doomed |
|---|---|---|---|---|
| R1 | B1 = W(1,1), B5 = W(1,1) | 2/1/1/2 | q1, y, q2 | x |
| R3 | B3 = W(1,1), B5 = W(1,1) | 0/0/1/2 | x, y, q2 | q1 |
| R5 | B1 = W(0,0), B3 = W(1,1) | 2/0/1/4 | q1, x, y | q2 |

**Checks.**
- Every step lies in `Rsl k`. `SeqMono` holds because `Sq_0` changes in every write block, and `InstFrozen` is vacuous because `k` holds no instance.
- `Isl` holds at every target state: `JEven` holds, `JOdd` is vacuous, and the only pool entry is `k`.
- Own events are emitted in program order except the skipped response. `local_frontier` holds because the reader is untagged, and `ghost_emit` holds.
- Before `rb`, `Coup` and `Gsl` force `p' = p`. At `rb` the LP is forced, with `A 0 = (1,1)` in all three runs. So the end state has `k` at `lini (1,1)` or `linr (1,1)`.
- All three runs end with the same:
  - registers `Sq_0 = 4, Sx_0 = Sy_0 = 1`;
  - `used` key sequence, the same `A`, no pending records, and an empty ghost.

  They can differ only in that `lini`/`linr` phase. By pigeonhole two runs share it, and the genuine sets of any two runs cover all four value responses (the `rmb` responses fire in every run).
- `fam_merge` then gives `Qsl k (fR 0) (0,1) Z`. But `Z` holds `k`'s unique entry or record with `(1,1)` (`ic_wf`, `ic_recnd`), a contradiction.

**Failing premise.** There is no choice of slot assertions, `fin` and `fin0` for path π that satisfies both `bw_sum` and the stability premises. Hence there is no `MethodProvable Isl Rsl Gsl (M2w rc si tw) t (fR i) (Osl …) (Qsl …)` for any `rc, si, tw, t, i`.

**Caveat.** The final register files are equal only extensionally (`upd` chains in different orders). So the argument uses functional extensionality at the meta level: a closed derivation would make Rocq + funext inconsistent.

## 3. M-24's repair (i)–(iv)

- **(ii) fails stability.** `ns_R_in` (for in-edges) and `bw_R` (for final edges) cannot be met. Counter-state `m24_not_stable` (kernel-checked):
  - registers `Sq_0 = 2`, `(Sx_0, Sy_0) = (1,1)`, `A 0 = (1,1)`;
  - κG consumed, κx pending with value 1, `Isl` holds.
  - The (ii) assertion holds with `r0 = 2, ax = 1`.
  - One `Rsl k` step consumes κx, landing in `Isl`, and the assertion is false afterwards: `done κx` forces `ax = 0`, and then `r0 = 2` contradicts `0 = fst (A 0) = 1`.
  - This is run R1 right after its spurious consumption.
- **(i)** helps only own-event stability. It cannot help against `R k`, which contains the identical transition.
- **(iii)** is fine and is not where the proof breaks.
- **(iv)** is false as stated.
- **Without the `done → value` clauses,** using only `∃ witness, KMine … ∧ fact(witness)`: every assertion is stable, but the witnesses of different `fin d` are independent once the records are consumed. The derivation then dies at `bw_sum`, as §2 shows.

## 4. Is this intrinsic, or a choice of I/R/G?

**Ingredient 1, the conjunctive certificate:** independent of I/R/G (`fam_merge`).

**Ingredient 2, "R k consumes k's own records" — forced for any R (argued).** `R k ⊇ G k'` (`h_guar_rely`). `G k'` contains `k'`'s response step from every state satisfying that slot's precondition (`ns_update`, `ns_guar`). That precondition holds at every real state where the response is pending, by soundness via `rlhl_gsim`. Two real schedules on one thread `t` give the same proof state:
- Calls: `W`, an older writer of instance `j`; `k'`, an older reader of `i`; `k`, a younger reader of `i`.
- **S_A:** `W.rdSq | k'.q1' … k'.q2' | k.q1 k.ra k.x | W`'s six writes.
- **S_B:** `W.rdSq` and `W`'s six writes `| k'.q1' k'.ra' k'.x' k'.y' k'.rb' k'.q2' | k.q1 k.ra k.x`.

The cross-call F2 constraints hold in both: an older pending `rmb` blocks younger reads and `rmb`s; writes and `wmb` cross reads and `rmb`. With handles chosen so that both key sequences are equal:
- the 10th key κ, with its pending record `(Sx_i, x_i)`, is `k`'s final-iteration `rd Sx_i` in S_A, and `k'`'s `rd Sx_i` in S_B;
- the pool (`k'` at `lini A_i`, `k` at `ls_inv`), the ghost (`k`'s y, rb, q2), the overlay records and the registers agree (registers again up to funext).

So `G k'`, and hence `R k`, must contain consuming `k`'s final record at a reachable state. Owner information in the ghost before emission cannot prevent this, since it is erased exactly at emission.

**Residual escape (argued).** In the general case, a derivation's only further freedom is `k`'s own pool bookkeeping: the LP's timing or value and one `lini → linr` bit. It would have to record which of four independently scheduled responses were genuine. That cannot be read off any own-step state, because a genuine response and a spurious consumption are the same transition. I expect a pigeonhole over more runs, as in §2, to close this. It is not proved; making the argument rigorous for all I/R/G is research-level.

**Consequence.** The mechanized rules are incomplete with respect to `MethodSem` for untagged multi-read validation over `EIhl`. This bears directly on implex.tex:3 ("RLHL is complete").

## 5. Routes that do work (none keeps both the program and the logic)

**(A) Tag the barriers:** `rmb_a ← res q1`, `rmb_b ← res x, res y`.
- This is ordinary read-barrier semantics: the barrier waits for earlier loads to complete. Under EI the value is bound at the invocation, so the tags only force earlier placement of the reports. I argue, without mechanizing it, that the overlay behaviours are unchanged.
- Slot sketch:
  - res q1 → rmb_a carries `KSeqGe i s`.
  - inv x → res x carries `∃rx, KMine κx rx ∧ s ≤ Sq_i ∧ (Sq_i = s → even s → rx = fst(A i))`.
  - res x → rb carries the same fact with `a` in place of `rx`.
  - At the LP, `lini v` with `v = A i`.
  - inv q2 → res q2 carries `∃r2, KMine κq2 r2 ∧ (r2 = s → even s → (a,c) = v)`.
  - `fin_q2 := (s' = s → even s → (a,c) = v)`.

  Only one untagged value, `s'`, is left. This agrees with Writer B's hand check that the frozen definitions suffice.
- A less restrictive variant: tag `q2`'s invocation with `res x, res y`, and keep `rmb_a ← res q1`.
- Either variant deviates from the control-dependency policy of impl.tex:120, which the compilation would not produce for the current iteration.

**(B) Value-history presentation `EIhv`:** `EIhl` whose `used` list stores the full record `Op` (key, op, value) instead of the key.
- History is immutable, so a spurious consumption no longer destroys information. Witnesses are pinned by the state, and the per-response `fin` facts correlate:
  - `fin_d := Hist κd = meta_d`;
  - `fin_q2` additionally carries `r1 = r2 even → (rx, ry) = v`, established at `T_q2` from the history.
- It keeps the untagged program and the paper's policy, and it is review recommendation 5. It needs an `hlift`-style `MTraces`/`RCompLin` equivalence: the history is a deterministic function of the run.
- Recording owners in the proof state is the heavier version of (B): it changes `PState` and the soundness files.

## 6. Effort and risks

| Item | Effort | Main risk |
|---|---|---|
| Mechanize §2 (three runs through `ctx_triple` + `fam_merge`) | 1.5–3 days | Building `Isl` and `Fam` at every state; funext |
| (A): `rnext` call counter for `dix`, SL2Prog Parts 6–7, SL2Exec rescheduling | 1–2 days | Witness schedules need responses placed early |
| (A): task .5 derivation | 2–4 days | Loop `Inv`; `ns_if` pairs |
| (B): `EIhv` + equivalence | 2–3 days | — |
| (B): re-instantiate SL2Inv over `EIhv` | 2–3 days | Changes frozen definitions; task .6 must be re-checked |
| (B): task .5 derivation | 3–5 days | — |

## 7. Complete scratch script (piped to `rocq repl`, `_CoqProject` -R flags)

All three printed `Closed under the global context`.

```coq
From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia Relations.Relation_Operators.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareDag models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLinSpec models.simlin.RelaxedHoareRun models.simlin.RelaxedHoareReady.
Require Import examples.Relaxed.RelaxedHoareSL2Prog examples.Relaxed.RelaxedHoareSL2Inv.
Import ListNotations LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedModuleSemantics RelaxedPossibility RelaxedHoareCompLinSpec RelaxedHoareBase RelaxedHoareDag RelaxedHoareRun RelaxedHoareReady RelaxedHoareSL2Prog RelaxedHoareSL2Inv.

Section Merge.
  Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
  Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (k : CallKey F) (Pinit : Assn VE VF).
  Lemma fam_merge Γ fin fin0 Q tr l1 l2 Z :
    BarrierWith I R k Pinit Γ fin fin0 Q ->
    Fam I Γ fin fin0 tr l1 Z -> Fam I Γ fin fin0 tr l2 Z ->
    (forall d, d < length Γ -> ~ rem Γ l1 d \/ ~ rem Γ l2 d) -> Q Z.
  Proof.
    intros Hbw H1 H2 Hcov. apply (bw_sum _ _ _ _ _ _ _ _ Hbw Z (fa_I _ _ _ _ _ _ _ H1) (fa_fin0 _ _ _ _ _ _ _ H1)).
    intros d sd Hd _. assert (Hlt : d < length Γ) by (apply nth_error_Some; congruence).
    destruct (Hcov d Hlt) as [Hn | Hn].
    - exact (fa_fin _ _ _ _ _ _ _ H1 d Hlt Hn).
    - exact (fa_fin _ _ _ _ _ _ _ H2 d Hlt Hn).
  Qed.
End Merge.

Module M24Scratch.
  Definition rc := true.
  Definition si : FOp -> FOp -> Prop := fun _ _ => False.
  Definition tw : nat -> tid := fun _ => 2%positive.
  Definition t : tid := 1%positive.
  Definition k : CallKey (F2 si) := (t, 0).
  Definition kG : CallKey (E_S rc) := (t, 10).
  Definition kA : CallKey (E_S rc) := (t, 11).
  Definition kX : CallKey (E_S rc) := (t, 12).
  Definition m : Regs := fun l => match l with Sq 0 => 2 | Sx 0 => 1 | Sy 0 => 1 | _ => 0 end.
  Definition A : AS := fun i => if Nat.eqb i 0 then (1, 1) else (0, 0).
  Definition recx : RelaxedTraceLin.Op (E_S rc) := RelaxedTraceLin.Build_Op kX (sRd (Sx 0)) 1.
  Definition VE := EIhl (E := E_S rc) δS.
  Definition VF := RelaxedHoareSpec.EI (F := F2 si) δF.
  Definition σ : State VE := ((m, [recx]), [kX; kA; kG]).
  Definition σ' : State VE := ((m, []), [kX; kA; kG]).
  Definition P : LinPool (F2 si) := [make_lin_entry k (@ls_inv (F2 si) (fR 0))].
  Definition γ : Ghost (E_S rc) (F2 si) := [Build_ScheduledEvent k (IE rc t 14 sRmb)].
  Definition p : Poss VF := @PossOk (F2 si) VF (A, []) P.
  Definition s : PState VE VF := (σ, p, γ).
  Definition s' : PState VE VF := (σ', p, γ).

  Lemma doom_vacuous_after_consumption key l w st :
    eihl_rec_used (E := E_S rc) δS (ps_mem st) -> eihl_done_res (E := E_S rc) δS key (ps_mem st) ->
    KDoomRd rc si key l w st /\ KMine rc si key (RelaxedTraceLin.Build_Op key (sRd l) w) st.
  Proof.
    intros Hru Hd. split.
    - exists (S w). split; [lia | exact (eihl_done_res_mine _ key _ _ Hru Hd)].
    - exact (eihl_done_res_mine _ key _ _ Hru Hd).
  Qed.

  Definition M24 (st : PState VE VF) : Prop :=
    exists (r0 ax : nat),
      KMine rc si kG (RelaxedTraceLin.Build_Op kG (sRd (Sq 0)) r0) st /\
      (eihl_done_res (E := E_S rc) δS kG (ps_mem st) -> r0 = 2) /\
      r0 <= regs rc si st (Sq 0) /\
      KMine rc si kX (RelaxedTraceLin.Build_Op kX (sRd (Sx 0)) ax) st /\
      (eihl_done_res (E := E_S rc) δS kX (ps_mem st) -> ax = 0) /\
      (forall A0 Pf0 P0, ps_poss st = @PossOk (F2 si) VF (A0, Pf0) P0 ->
         r0 = 2 -> regs rc si st (Sq 0) = 2 -> Nat.even 2 = true -> ax = fst (A0 0)).

  Lemma kX_kG : kX <> kG. Proof. unfold kX, kG. intros H. injection H. lia. Qed.

  Lemma m24_pre : M24 s.
  Proof.
    exists 2, 1. unfold KMine, eihl_mine, eihl_rec_used, eihl_done_res, regs, s, σ, ps_mem, ps_poss, p. cbn.
    split; [split; [intros x [<- | []]; left; reflexivity | split; [auto 10 | intros x [<- | []] Hk; exfalso; exact (kX_kG Hk)]] |].
    split; [reflexivity |]. split; [lia |].
    split; [split; [intros x [<- | []]; left; reflexivity | split; [left; reflexivity | intros x [<- | []] _; reflexivity]] |].
    split; [intros [_ Hn]; exfalso; exact (Hn recx (or_introl eq_refl) eq_refl) |].
    intros A0 Pf0 P0 Hp _ _ _. injection Hp as <- _ _. reflexivity.
  Qed.

  Lemma m24_post_false : ~ M24 s'.
  Proof.
    unfold M24, eihl_done_res, regs, s', σ', ps_mem, ps_poss, p. cbn.
    intros (r0 & ax & _ & HG & _ & _ & HX & Hv).
    specialize (HG (conj (or_intror (or_intror (or_introl eq_refl))) (fun x (H : In x []) => match H with end))).
    specialize (HX (conj (or_introl eq_refl) (fun x (H : In x []) => match H with end))).
    subst r0 ax. specialize (Hv A [] P eq_refl eq_refl eq_refl eq_refl). cbn in Hv. discriminate.
  Qed.

  Lemma rsl_step : Rsl rc si k s s'.
  Proof.
    unfold Rsl, s, s', ps_mem, ps_poss, ps_ghost, p, regs. cbn. split.
    - apply rt_step. exists (Build_ThreadEvent t (@ResEv (E_S rc) 12 (sRd (Sx 0)) 1)).
      cbn. split; [| reflexivity]. exists [], []. split; reflexivity.
    - exists A, [], P, A, [], P. split; [reflexivity |]. split; [reflexivity |].
      split; [auto |]. split; [auto |]. split; [tauto |]. split; [apply oldersub_refl |].
      split.
      + intros i _. unfold InstFrozen. auto.
      + intros i. split; [lia |]. intros _. split; [reflexivity | auto].
  Qed.

  Lemma islc_ok : IslC rc si tw m A [] P γ.
  Proof.
    constructor.
    - unfold lin_pool_well_formed, lin_domain. cbn. constructor; [intros [] | constructor].
    - split.
      + intros e [<- | []]. cbn. left. reflexivity.
      + intros i j e1 e2 H1 H2 Ho. exfalso.
        destruct i as [| i]; [| destruct i; discriminate]. cbn in H1. injection H1 as <-.
        destruct j as [| j]; [| destruct j; discriminate]. cbn in H2. injection H2 as <-.
        cbn in Ho. unfold key_older in Ho. inversion Ho; subst;
          repeat match goal with H : subseq _ [] |- _ => inversion H; clear H end.
    - constructor; [| constructor]. cbn. split; [reflexivity | exact I].
    - intros o [].
    - constructor.
    - intros e [<- | []]. cbn. split; [intros _ | reflexivity].
      exists (Build_ScheduledEvent k (IE rc t 14 sRmb)). split; [left; reflexivity |]. split; reflexivity.
    - intros e i vx vy [<- | []] H. discriminate.
    - intros i k1 k2 (vx & vy & ls & Hl & Hop). exfalso.
      destruct Hl as [Hl | []]. unfold make_lin_entry in Hl. injection Hl as _ _ Hls. subst ls. discriminate.
    - intros [| i] He; reflexivity.
    - intros [| i] He; discriminate.
    - constructor; [intros [] | constructor].
  Qed.

  Lemma isl_pre : Isl rc si tw s.
  Proof. exists A, [], P. split; [reflexivity |]. split; [intros x [<- | []]; left; reflexivity | exact islc_ok]. Qed.
  Lemma isl_post : Isl rc si tw s'.
  Proof. exists A, [], P. split; [reflexivity |]. split; [intros x [] | exact islc_ok]. Qed.

  Theorem m24_not_stable :
    Isl rc si tw s /\ M24 s /\ Rsl rc si k s s' /\ Isl rc si tw s' /\ ~ M24 s'.
  Proof. exact (conj isl_pre (conj m24_pre (conj rsl_step (conj isl_post m24_post_false)))). Qed.
End M24Scratch.
Print Assumptions fam_merge.
Print Assumptions M24Scratch.doom_vacuous_after_consumption.
Print Assumptions M24Scratch.m24_not_stable.
```

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareDag.v (`FamAt`, `BarrierWith.bw_sum`, `ctx_triple`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareRun.v (`dprec_run`, `RunCallOK`, `eihl_done_res_mine`)
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v (`HL`/`EIhl`, the place for an `EIhv` value history, `hlift`)
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Inv.v (`Rsl`/`Gsl`/`Coup`/`Qsl`, `KDoomRd`, `sl2rd_rlhl2_of_methods`)
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Prog.v (`rnext`, which needs `dix` tags under option (A))