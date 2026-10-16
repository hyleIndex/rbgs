**(B) verdict.** A value history is enough for the untagged reader. Response ownership is not needed. The history can sit entirely in the underlay presentation, as a generic event log `Log VE`, so RLHL itself is untouched: `PState`, `ghost_emit`, `CallTriple`, `method_sound` and `rlhl_gsim` do not change. I kernel-checked the trace equivalence, the transfer to plain `EI`, a value kit and a lifting kit in a stdin-only `rocq repl` session (complete script in §7). With the log, I believe the reader as written in SL2Prog has a `MethodProvable` derivation through `rp_run`. I checked this by hand (§3), not in Rocq. The four record values and the LP's `A i` meet in `bw_sum` at the return, linked by facts about each underlay key's logged value, not along dag edges. Writer B's impossibility argument is correct over `EIhl`, but its premise ("the proof state forgets a record's value once it is consumed") is exactly what the log removes.

## 1. The value-history presentation

- **`Log VE`.** State `(σ, l)`. Step: `Step VE ev σ σ' ∧ l' = ev :: l`.
- **`EIhlv δ := Log (EIhl δ)`.** A proof-state memory is `((((m,U),used),log)`.
- **`recs σ`.** The pending records followed by the records consumed by logged responses (`res_ops`). So every record ever created stays visible. Since `EI` fixes a record's value at invocation, `recs` is the record history.
- **`LogVal x σ := In x (recs σ)`.**
- **`LogOK σ`.** The keys of `recs` are used and have no duplicates. Every step preserves it.

**Kernel-checked results (script §7; Rocq 9.3.0; `Print Assumptions` for each):**
- `loglift : MTraces VE M σ0 s <-> MTraces (Log VE) M (σ0, []) s` (closed). It is simpler than `hlift`: no step is disabled, so no `LiftOK` is needed.
- `complin_log_under` (closed).
- `log_handle_linear`: `Log` preserves `HandleLinear` (closed).
- `rlhl_complin_eihlv`: `RLHL2Hyps I R G M ((σ0,[]),[]) (s0,[]) → RCompLin M (EI δ) σ0 (EI δF) (s0,[])`. Its only axiom is `classic`, inherited from `rlhl_complin_ei`, exactly as for the existing `rlhl_complin_eihl`.
- Value kit, all closed:
  - `logval_step`: `LogVal` is kept by every `EIhlv` step, of any thread and any call;
  - `logok_init`, `logok_step`;
  - `logval_unique`: one value per key, forever;
  - `logval_res`: a response returns the logged value of its key;
  - `logval_inv`: an invocation creates a logged record whose value is chosen by `δ`;
  - `sl_logval_rd`: two logged values of one `sRd` key are equal, via `rd_rec_inj`, so no `eq_rect_eq`.
- Lifting kit, closed: `dropS`, `liftA`, `liftI`, `liftG`, `stable_lift`, `evupdate_lift`.

**Does `rlhl_complin_eihl` transfer?** Yes. `rlhl_complin_ei` (`RelaxedHoareCompLin.v:1234`) is generic in `VE`, so it composes with `complin_log_under` and `complin_hlift_under`. `RLHL2Hyps`, `method_sound`, `rlhl_gsim` and `rlhl2_of_provable` are also generic in `VE`. The downstream step to `cc_rel_lin` is unchanged.

**Reusing SL2Inv without editing it.** Take `I' := liftI Isl`, with `J := LogOK` in `liftI`. Take `R' k := liftG (Rsl k) ∧ memory moves by EIhlv steps`, `G'` likewise, and `Q' := liftA Qsl`. Then:
- `stable_lift` and `evupdate_lift` carry Parts 6–7 of SL2Inv across.
- The side fields lift routinely. I checked the shapes by hand, not in Rocq: `h_invoke_rely` and `h_return_rely` leave memory unchanged, so the log part is reflexive; `h_init` uses `logok_init`; the `clos_refl` in `mp_ret` lifts because memory is unchanged.

**Fidelity to the paper.** The paper's proof state carries the underlay trace:
- Appendix/programlogic.tex:537, EStep: `σ'.s = σ.s · t:e`;
- the proof at :507 quantifies over `(t, poss) ∈ I`, with `t` a trace.

So `EIhl` is the lossy abstraction, and `Log` restores the paper's component. This is the same kind of move as `HL` (decisions M-16 and M-20), and like `HL` it is justified by a closed trace equivalence.

## 2. Why history suffices where `EIhl` fails

Over `EIhl`, once a record is consumed only its key remains, in `used`. `eihl_mine κ x0` then holds for every `x0` (`eihl_done_res_mine`). Value facts from different edges and fins are separate existentials that no state fact links. And `RunCallOK`'s invocation slot `si h` does not see the response value `v`. So the identification "record value = response value" exists only in that response's own precondition, as Writer B says.

Over `EIhlv`, `V(κ,o,v) := LogVal (Op κ o v)` names the value of key `κ` permanently. Any assertion established anywhere can mention it, and `logval_unique` equates witnesses that come from different edges or fins. The identification can therefore be moved from the LP to the return.

## 3. The reader derivation over `EIhlv` (by hand, not mechanized)

**Notation.** Iteration n has keys:

| key | event |
|---|---|
| κG | first `rd Sq_i` |
| κA | `rmb_a` |
| κx | `rd Sx_i` |
| κy | `rd Sy_i` |
| κB | `rmb_b` |
| κT | final `rd Sq_i` |

`seq := regs (Sq i)`.

**Dag.** By `dprec_run` and the `sindep` table (SL2Prog.v:280-299), the invocations are ordered κG → κA → {κx, κy} → κB → κT (F2: rd/rmb, rmb/rmb and same-location pairs). Each response is preceded only by its own invocation (F1). There are no response → invocation edges.

**Edges (final iteration; earlier iterations use `fin := True`):**

- **κG inv.** By `logval_inv` and `δS`, the record value is `r0 = seq`. Out-edge `E_G := ∃r0. V(κG,Sq,r0) ∧ r0 ≤ seq`. It is stable by `logval_step` and the `KSeqGe` kit. κA inv passes `E_G` on.
- **κx inv.** The record value is `ax = x_i`. Edge to κB: `E_x := ∃ r0 ax. V(κG,Sq,r0) ∧ V(κx,Sx,ax) ∧ KRdVal i r0 fst ax`.
  - It is established from `E_G` and `ic_jeven`.
  - It is stable because `KRdVal` is Writer B's kit lemma, stable under `Rsl` and every `Gsl`.
  - This is M-24(ii), with `r0` named by the log instead of by "G's record".
  - `E_y` is the same with `cy` and `snd`.
- **κB inv (the LP, taken when the ghost says this is the last `rmb`; `isl_read_lp`).**
  - The two copies of `r0` from `E_x` and `E_y` coincide by `sl_logval_rd` (`LogOK` comes from `I'`).
  - The LP records `Op k (fR i) (A i)` (SL2Inv.v:1566).
  - Post, and edge to κT: `Pkg := ∃ r0 ax cy q vx vy. V(κG,Sq,r0) ∧ V(κx,Sx,ax) ∧ V(κy,Sy,cy) ∧ KRec (Op k (fR i) (vx,vy)) ∧ r0 ≤ q ≤ seq ∧ (q = r0 → even r0 → vx = ax ∧ vy = cy)`, with `q := seq` and `(vx,vy) := A i` at the LP.
  - The last conjunct is `KRdVal` evaluated at the LP; it is pure from then on. `KRec` is stable by `krec_stable`, and `seq` growth by `KSeqGe`.
- **κT inv.** The record value is `r0' = seq ≥ q`. Edge to κT res: `Pkg ∧ ∃r0'. V(κT,Sq,r0') ∧ q ≤ r0'`.
- **Every response slot with value v.** The in-edge carries `V(κ,o,w)`, and `logval_res` gives `w = v`. A wrong prophecy makes the step impossible, so its update is vacuous; this replaces `KDoomRd`. The post and `fin` are `V(κ,o,v)`. For κT res, `fin` also carries `Pkg` and `q ≤ r0'`.
- **Return.** The machine is at `RD a c` with `rok s s' = true`, so `even s ∧ s = s'` by `rok_spec`. `bw_sum` has the fins of κG res (s), κx res (a), κy res (c) and κT res (s' and `Pkg`).
  - `sl_logval_rd` gives `r0 = s`, `ax = a`, `cy = c` and `r0' = s'`.
  - Then `s = r0 ≤ q ≤ r0' = s' = s`, so `q = r0`, and since `r0` is even, `(vx,vy) = (a,c)`.
  - So `KRec (Op k (fR i) (a,c))` holds, which is `Qsl`'s second disjunct, and `qsl_ret` (lifted) gives `RetCond`.

**The specific concerns:**
- **A rely step consuming the reader's own record.** Under `EIhlv`, consumption moves the record into the logged part of `recs` with the same value, so `V` facts survive any rely whose memory part is `EIhlv` steps. The reader's own response is then disabled forever, and there is nothing to prove. Ownership is not needed.
- **`rp_wait_pending` gives the continuation without the slot's postcondition.** That is harmless. The continuation only uses the Coq values `s, a, c, s'`; the link to the state is made in `bw_sum` through the fins.
- **Does the LP need `a`?** No. It records an implication between named values, and the identification happens at the return. This is the step Writer B's argument misses: it assumes the four values must meet in one edge assertion.
- **M-24 (i)–(iv) collapse:**
  - (i) is unnecessary: the log records the consumed value.
  - (ii) becomes conditioning on `V(κG,Sq,r0)`.
  - (iii) reduces to: every own `sl_guar` has `EIhlv` steps as its memory part, and own slots other than the LP keep k's pool entry and records.
  - (iv) is `logval_step`, already closed.

**Remaining obligations (checked by hand only):**
- (a) `Gsl k` does not constrain k's own entry. Response slots therefore need `sl_guar := G' k ∧ poss unchanged`, so that `KRec` survives `bw_if`. This requires `isl_response` to use the identity abstract update; check it.
- (b) `RunCtx` bookkeeping: `bw_sum` must locate the indices of the current iteration's four response slots (m-53).
- (c) The ghost-based "last `rmb`" LP and its persistence fact (m-52) are unaffected by (B) and still needed.
- (d) Non-final `rmb_b`s do not linearize, as required by `Coup`.

## 4. Response ownership: not needed, and a real RLHL change

- **What it would take.** The ghost would also list pending responses with their owners (the module queue already holds them); `ghost_of` would include them; and `ghost_emit`'s response case would remove an entry.
- **What changes:** `ghost_new`, `NoOwn`, the `PostInvoke`/`Ω` footprints, `GAge`, `ic_gwf`, and `Coup`/`RecNB`/`Owns` in SL2Inv. `ghost_emit`, `ghost_of`, `ghost_new` and `NoOwn` occur about 188 times across 10+ files: Base, Dag, Sound, GSim, Run, Ready, Inherit, Absorb, Resig, Spec and all instances.
- **Specific risk.** The Base.v header says the soundness proof places responses lazily because "a response leaves the ghost unchanged". Ownership removes that premise of `method_sound`.
- **Estimate:** 2,000–4,000 lines of churn, 3–6 iterations, plus re-proving lazy placement.
- **It is also not sufficient alone.** After the reader's own consumption, the value is still lost unless M-24(i) is added. History dominates ownership for this problem.
- I found no example in the repository that needs ownership; I did not search exhaustively.

## 5. Generality (implex.tex:3; m-36)

- **What it fixes.** It removes one concrete incompleteness of the mechanized rules relative to `MethodSem`: forgetting a value once it is consumed. The class is methods whose result or branch combines an untagged response value with facts established at other events. Facts that can travel along the response's own F1 edge, or along tagged F3 edges, do not need it. Consumers:
  - SeqLock readers, for both the cached-v writer and the Linux-literal writer of M-23(b);
  - the paused RLHL-latch LatchSet reader. Its designs already rely on the same invalid step ("`eihl_mine_res` … at Ret"): RLHL-latch.md:194-195, latch-designs/C-adversarial.md:121-124, B-latchset.md:192 and 207;
  - double-collect snapshots, version-validated optimistic reads, and read-only transactions.

  Not needed: a single read whose own invocation is the LP (F1 edge), tagged value flows, and the writer.
- **What it does not establish.** The log is the history half of the classical auxiliary-variable device. The prophecy half is only partly present: the ghost knows future own invocations, but invocation slots never see future response values, while `MethodSem` certificates do. So LP choices that depend on future responses (m-36, single possibility) remain out of reach, and implex.tex:3 stays unsupported.
- **What to record.** Writer B's conjectured datum ("no derivation for the untagged reader") is a property of `EIhl`'s lossy state, not of RLHL's rules. The support is the §3 sketch, which is not mechanized.

## 6. Cost and risk compared with (A)

| | (B) Log presentation | (A) tag the reader |
|---|---|---|
| Logic or infrastructure change | New file only; 0 lines changed in the logic | None |
| Program change | None; SL2Prog and SL2Exec (SB witness) untouched | Edits closed SL2Prog: `dix` indices, so the machine must count its calls; re-validate `sb2_exec_rd` and `complete_tac` |
| Paper fidelity | Matches the paper's trace-based proof state (programlogic.tex:537) | Tags not produced by the paper's dependency policy (impl.tex:120: plain reads are not control-ordered; `rmb` waits only on branch handles) |
| New infrastructure | 350–500 lines, 1 iteration (about 180 already checked), low risk | — |
| SL2 glue (lifted I'/R'/G', side fields) | 150–250 lines, low risk | — |
| .5 reader | Plan's 1,000–1,600 lines plus 150–300 for log bookkeeping; 2–3 iterations; medium risk (m-52, m-53, first looping `rp_run`) | About 10–20% smaller (values arrive along F3 edges) |
| .6 writer | Plus 50–150 lines (lifting) | Unchanged |
| .7 | Swap in `rlhl_complin_eihlv` | Unchanged |
| Reuse | LatchSet and other validate-after-read programs | Per-program |
| Main risk | Reviewers may see a third presentation (`EI` → `EIhl` → `EIhlv`) as a trick; mitigated by the paper alignment and the closed `loglift` | Verifies a stronger program than the paper's; the SB datum could shift |

**Net:** (B) costs about 700–1,200 extra lines and roughly one more iteration, keeps the program and the SB datum as they are, and is reusable. I recommend (B) with the reader left untagged, and not adding ownership. (A) remains compatible with (B) if the author also wants the tagged variant.

## 7. Complete scratch script (stdin to `rocq repl` with the _CoqProject `-R` flags; no errors; all closed except `rlhl_complin_eihlv`, whose only axiom is `classic`)

```coq
Require Import Stdlib.Lists.List Stdlib.Sorting.Permutation.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLin models.simlin.RelaxedHoareCompLinSpec.
Require Import examples.Relaxed.RelaxedHoareSL2Prog.
Import ListNotations.
Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedModuleSemantics RelaxedPossibility RelaxedTraceLin.
Import RelaxedHoareBase RelaxedHoareCompLin RelaxedHoareCompLinSpec.
(* Part 1: event-log presentation, trace equivalence, handle-linearity *)
Section Log.
  Context {E : RelaxedSig.t} (VE : LTS E).
  Definition logx_step (ev : ThreadEvent E) (σ σ' : State VE * list (ThreadEvent E)) : Prop :=
    Step VE ev (fst σ) (fst σ') /\ snd σ' = ev :: snd σ.
  Definition Log : LTS E :=
    {| State := (State VE * list (ThreadEvent E))%type; Step := logx_step;
       Error := fun ev σ => Error VE ev (fst σ) |}.
  Lemma log_handle_linear used : HandleLinear VE used -> HandleLinear Log (fun σ k => used (fst σ) k).
  Proof.
    intros [H1 H2 H3]. constructor.
    - intros t h op σ σ' [Hs _]. exact (H1 t h op _ _ Hs).
    - intros ev σ σ' k [Hs _]. exact (H2 ev _ _ k Hs).
    - intros t h op σ σ' [Hs _]. exact (H3 t h op _ _ Hs).
  Qed.
  Context {G : RelaxedSig.t} (M : RelaxedModuleImpl E G).
  Definition lift_cfgL (c : @TaggedModuleConfig E G VE) (l : list (ThreadEvent E)) : @TaggedModuleConfig E G Log :=
    @Build_TaggedModuleConfig E G Log (tm_lts_state c, l) (tm_calls c) (tm_queue c) (tm_used_underlay c).
  Definition drop_cfgL (c : @TaggedModuleConfig E G Log) : @TaggedModuleConfig E G VE :=
    @Build_TaggedModuleConfig E G VE (fst (tm_lts_state c)) (tm_calls c) (tm_queue c) (tm_used_underlay c).
  Lemma liftL_step ev c c' l :
    module_step_tagged VE M ev c c' -> exists l', module_step_tagged Log M ev (lift_cfgL c l) (lift_cfgL c' l').
  Proof.
    destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft | cand q q' calls Q Q' used Hsel Hlts
                  | t h op ret q calls calls' Q used Hfin Hdone].
    - exists l. exact (tagged_invoke Log M t h op (q, l) calls Q used trace ret Hcf Hprod Hft).
    - exists (untag (ts_event cand) :: l).
      exact (tagged_underlay Log M cand (q, l) (q', untag (ts_event cand) :: l) calls Q Q' used Hsel (conj Hlts eq_refl)).
    - exists l. exact (tagged_return Log M t h op ret (q, l) calls calls' Q used Hfin Hdone).
  Qed.
  Lemma liftL_exec c evs c' :
    module_execution_tagged VE M c evs c' -> forall l, exists l', module_execution_tagged Log M (lift_cfgL c l) evs (lift_cfgL c' l').
  Proof.
    induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros l.
    - exists l. constructor.
    - destruct (liftL_step ev c1 c2 l Hst) as (l2 & Hst'). destruct (IH l2) as (l3 & Hex').
      exists l3. econstructor; [exact Hst' | exact Hex'].
  Qed.
  Lemma dropL_step ev c c' : module_step_tagged Log M ev c c' -> module_step_tagged VE M ev (drop_cfgL c) (drop_cfgL c').
  Proof.
    destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft | cand q q' calls Q Q' used Hsel Hlts
                  | t h op ret q calls calls' Q used Hfin Hdone]; cbn.
    - exact (tagged_invoke VE M t h op (fst q) calls Q used trace ret Hcf Hprod Hft).
    - exact (tagged_underlay VE M cand (fst q) (fst q') calls Q Q' used Hsel (proj1 Hlts)).
    - exact (tagged_return VE M t h op ret (fst q) calls calls' Q used Hfin Hdone).
  Qed.
  Lemma dropL_exec c evs c' : module_execution_tagged Log M c evs c' -> module_execution_tagged VE M (drop_cfgL c) evs (drop_cfgL c').
  Proof. induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [constructor |]. econstructor; [exact (dropL_step _ _ _ Hst) | exact IH]. Qed.
  Theorem loglift (σ0 : State VE) (s : list (ThreadEvent G)) : MTraces VE M σ0 s <-> MTraces Log M (σ0, []) s.
  Proof.
    split.
    - intros (evs & c & Hex & Hov). destruct (liftL_exec _ _ _ Hex []) as (l & Hex').
      exists evs, (lift_cfgL c l). split; [exact Hex' | exact Hov].
    - intros (evs & c & Hex & Hov). exists evs, (drop_cfgL c). split; [exact (dropL_exec _ _ _ Hex) | exact Hov].
  Qed.
End Log.
Corollary complin_log_under {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE) (VF : LTS F) (v0 : State VF) :
  RCompLin M VE σ0 VF v0 <-> RCompLin M (Log VE) (σ0, []) VF v0.
Proof. split; intros HC s Hs; apply HC; apply (loglift VE M σ0 s); exact Hs. Qed.
(* Part 2: EIhlv, the transfer, and the value kit *)
Section LogVal.
  Context {E : RelaxedSig.t} {St : Type}.
  Context (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop).
  Definition EIhlv : LTS E := Log (EIhl δ).
  Local Notation V := EIhlv.
  Corollary rlhl_complin_eihlv {F : RelaxedSig.t} {StF : Type}
      (δF : StF -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> StF -> Prop) (s0 : StF)
      (I : Assn V (RelaxedHoareSpec.EI δF)) (R G : CallKey F -> PRel V (RelaxedHoareSpec.EI δF))
      (M : RelaxedModuleImpl E F) (σ0 : State (RelaxedHoareSpec.EI δ)) :
    RLHL2Hyps I R G M ((σ0, []), []) (s0, []) -> RCompLin M (RelaxedHoareSpec.EI δ) σ0 (RelaxedHoareSpec.EI δF) (s0, []).
  Proof.
    intros HH. apply (proj2 (complin_hlift_under M (RelaxedHoareSpec.EI δ) σ0 _ _)).
    apply (proj2 (complin_log_under M (EIhl δ) (σ0, []) _ _)).
    exact (rlhl_complin_ei δF s0 I R G M ((σ0, []), []) HH).
  Qed.
  Definition res_ops (ev : ThreadEvent E) : list (Op E) :=
    match te_ev E ev with ResEv h o r => [Build_Op (te_tid E ev, h) o r] | InvEv _ _ => [] end.
  Definition recs (σ : State V) : list (Op E) := snd (fst (fst σ)) ++ flat_map res_ops (snd σ).
  Definition LogVal (x : Op E) (σ : State V) : Prop := In x (recs σ).
  Definition LogOK (σ : State V) : Prop :=
    (forall x, In x (recs σ) -> In (op_key x) (snd (fst σ))) /\ NoDup (map (@op_key E) (recs σ)).
  Lemma logok_init (s : St) : LogOK (((s, []), []), []).
  Proof. split; [intros x [] | constructor]. Qed.
  Lemma logval_step ev (σ σ' : State V) x : Step V ev σ σ' -> LogVal x σ -> LogVal x σ'.
  Proof.
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs Hl] Hx. cbn in Hs, Hl. subst l'.
    unfold LogVal, recs in *. cbn in *. destruct ev as [t [h o | h o r]]; cbn in Hs |- *.
    - destruct Hs as (_ & (r & st' & _ & Heq) & _). injection Heq as -> ->. right. exact Hx.
    - destruct Hs as ((P1 & P2 & HP & Heq) & _). injection Heq as -> ->. cbn in HP. subst P.
      repeat rewrite in_app_iff in *. cbn in *. tauto.
  Qed.
  Lemma logok_step ev (σ σ' : State V) : Step V ev σ σ' -> LogOK σ -> LogOK σ'.
  Proof.
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs Hl] [Hu Hnd]. cbn in Hs, Hl. subst l'.
    unfold LogOK, recs in *. cbn [fst snd] in *.
    destruct ev as [t [h o | h o r]]; cbn in Hs; cbn [flat_map res_ops te_ev te_tid app].
    - destruct Hs as (Hnu & (r & st' & _ & Heq) & ->). injection Heq as -> ->. split.
      + intros x [<- | Hx]; [left; reflexivity | right; exact (Hu x Hx)].
      + constructor; [| exact Hnd]. intros Hin. apply in_map_iff in Hin as (x & Hk & Hx).
        cbn in Hk. apply Hnu. rewrite <- Hk. exact (Hu x Hx).
    - destruct Hs as ((P1 & P2 & HP & Heq) & ->). injection Heq as -> ->. cbn in HP. subst P.
      assert (Hp : Permutation ((P1 ++ Build_Op (t, h) o r :: P2) ++ flat_map res_ops l)
                               ((P1 ++ P2) ++ Build_Op (t, h) o r :: flat_map res_ops l)).
      { rewrite <- !app_assoc. apply Permutation_app_head. cbn [app]. apply Permutation_middle. }
      split.
      + intros x Hx. apply Hu. exact (Permutation_in _ (Permutation_sym Hp) Hx).
      + exact (Permutation_NoDup (Permutation_map _ Hp) Hnd).
  Qed.
  Lemma nodup_key_inj {A B : Type} (f : A -> B) (L : list A) x y :
    NoDup (map f L) -> In x L -> In y L -> f x = f y -> x = y.
  Proof.
    induction L as [| a L IH]; cbn; intros Hnd Hx Hy Hf; [destruct Hx |].
    inversion Hnd as [| ? ? Hnin Hnd']; subst. destruct Hx as [<- | Hx], Hy as [<- | Hy]; auto.
    - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hy.
    - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Hx.
  Qed.
  Lemma logval_unique (σ : State V) x y : LogOK σ -> LogVal x σ -> LogVal y σ -> op_key x = op_key y -> x = y.
  Proof. intros [_ Hnd] Hx Hy Hk. exact (nodup_key_inj _ _ x y Hnd Hx Hy Hk). Qed.
  Lemma logval_res t h o (r : Sig.ar o) x (σ σ' : State V) :
    LogOK σ -> LogVal x σ -> op_key x = (t, h) -> Step V (Build_ThreadEvent t (@ResEv E h o r)) σ σ' -> x = Build_Op (t, h) o r.
  Proof.
    intros Hok Hx Hk Hs. apply (logval_unique σ); [exact Hok | exact Hx | | exact Hk].
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. destruct Hs as [Hs _]. cbn in Hs.
    destruct Hs as ((P1 & P2 & HP & _) & _). cbn in HP. unfold LogVal, recs. cbn [fst snd]. rewrite HP.
    apply in_or_app. left. apply in_or_app. right. left. reflexivity.
  Qed.
  Lemma logval_inv t h o (σ σ' : State V) :
    Step V (Build_ThreadEvent t (@InvEv E h o)) σ σ' ->
    exists r st', δ (fst (fst (fst σ))) o r st' /\ fst (fst (fst σ')) = st' /\ LogVal (Build_Op (t, h) o r) σ'.
  Proof.
    destruct σ as [[[s P] u] l], σ' as [[[s' P'] u'] l']. intros [Hs _]. cbn in Hs.
    destruct Hs as (_ & (r & st' & Hd & Heq) & _). injection Heq as -> ->.
    exists r, st'. split; [exact Hd |]. split; [reflexivity |]. left. reflexivity.
  Qed.
End LogVal.
(* Part 3: SeqLock instance *)
Import RelaxedHoareSL2Prog.
Lemma sl_logval_rd {rc : bool} (σ : State (EIhlv (E := E_S rc) δS)) key l (v w : nat) :
  LogOK (E := E_S rc) δS σ -> LogVal (E := E_S rc) δS (@Build_Op (E_S rc) key (sRd l) v) σ ->
  LogVal (E := E_S rc) δS (@Build_Op (E_S rc) key (sRd l) w) σ -> v = w.
Proof. intros Hok Hv Hw. apply (rd_rec_inj (rc := rc) key l v w). exact (logval_unique (E := E_S rc) δS σ _ _ Hok Hv Hw eq_refl). Qed.
(* Part 4: lifting base-presentation results *)
Section Lift.
  Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
  Context (J : State (Log VE) -> Prop) (HJ : forall ev σ σ', Step (Log VE) ev σ σ' -> J σ -> J σ').
  Definition dropS (s : PState (Log VE) VF) : PState VE VF := (fst (ps_mem s), ps_poss s, ps_ghost s).
  Definition liftA (P : Assn VE VF) : Assn (Log VE) VF := fun s => P (dropS s).
  Definition liftI (I : Assn VE VF) : Assn (Log VE) VF := fun s => I (dropS s) /\ J (ps_mem s).
  Definition liftG (g : PRel VE VF) : PRel (Log VE) VF := fun s s' => g (dropS s) (dropS s').
  Lemma stable_lift (I : Assn VE VF) (r : PRel VE VF) P : Stable I r P -> Stable (liftI I) (liftG r) (liftA P).
  Proof. intros H s s' Hp Hr [HI _]. exact (H _ _ Hp Hr HI). Qed.
  Lemma evupdate_lift (I : Assn VE VF) g k ev P Q :
    EvUpdate I g k ev P Q -> EvUpdate (liftI I) (liftG g) k ev (liftA P) (liftA Q).
  Proof.
    intros H σ p γ γ' HP [HI HJσ] Hge σ' Hs.
    destruct (H (fst σ) p γ γ' HP HI Hge (fst σ') (proj1 Hs)) as (p' & Hps & HQ & HI' & Hg).
    exists p'. split; [exact Hps |]. split; [exact HQ |]. split; [split; [exact HI' | exact (HJ _ _ _ Hs HJσ)] | exact Hg].
  Qed.
End Lift.
Print Assumptions log_handle_linear. Print Assumptions loglift. Print Assumptions rlhl_complin_eihlv.
Print Assumptions logok_step. Print Assumptions logval_step. Print Assumptions logval_res.
Print Assumptions logval_inv. Print Assumptions sl_logval_rd. Print Assumptions stable_lift. Print Assumptions evupdate_lift.
```

### Critical Files for Implementation
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLinSpec.v — `HL`, `hlift`, `EIhl`, `rlhl_complin_eihl`. The new `Log`, `EIhlv` and `rlhl_complin_eihlv` follow this pattern, best placed in a new file such as `models/simlin/RelaxedHoareLog.v`.
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareRun.v — `RunCallOK`, `rp_run`, `run_method_provable`, `dprec_run`; the `eihl_done_*` lemmas, which the log versions replace.
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareDag.v — `NewSlotOK`, `BarrierWith` (`bw_sum`, `bw_if`), where the identification is made at the return.
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Inv.v — frozen `Isl`/`Rsl`/`Gsl`/`Qsl`, `KRdVal`, `KSeqGe`, `KRec`, `isl_read_lp`, `isl_response`, `qsl_ret`; reused unchanged through `liftI`/`liftG`.
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareSL2Prog.v — `rnext` (stays untagged), `rd_rec_inj`, `rok_spec`, `δS`.