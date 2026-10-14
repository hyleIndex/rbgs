<!-- RLHL-3a iteration-1 review (2026-10-13), saved verbatim by the orchestrator. Produced by the review workflow (three rocq-research-reviewer lenses, a skeptic per lens, a synthesis). -->

# Research review — RLHL-3a iteration 1 — 2026-10-13

## Scope
- **Repository.** `/Users/index/Documents/GitHub/rbgs-rlhl`, branch `rlhl`, HEAD 6e2b575. All RLHL work is uncommitted.
  - New in this task: `models/simlin/RelaxedHoareCompLin.v` (1141 lines) and `Module CounterCompLin` in the untracked `examples/Relaxed/RelaxedHoareChecks.v` (:5719-6247).
  - `_CoqProject`: +1 line for this task (+8 in total for the RLHL work).
  - Five tracked simlin files: header text only (`git diff --stat`: 54+/5-).
- **Task.** RLHL-3a (`.rocq-review/tasks/RLHL-3.md`, Adjustment): CompLin-style copy-cat soundness over the sequential spec EI. This implements the author decision at research-intent §8 :119-124.
- **Concerns in scope.** B-1, M-1, M-20/Q3, M-19, m-20 (handle-linearity WLOG), m-8, the layering plan (research-intent :123). New: M-22, m-30, m-32.
- **How this report was made.** It merges three lens reviews (soundness-fidelity, K/S/P/R-paper-decisions, nonvacuity) and their verifications. I spot-checked the points where they disagreed (below).

## Checks I ran
- **Build and hygiene.**
  - `make -n` reports `RelaxedHoareCompLin.vo` and `RelaxedHoareChecks.vo` up to date; the `.vo` files are newer than their `.v` files.
  - grep for Admitted, admit, Axiom, Parameter, Unset…Checking, vm_compute, native_compute in `RelaxedHoare*.v` and `RelaxedHoareChecks.v`: no hits.
  - `classic` is used once, at `RelaxedHoareCompLin.v:1070` (`rinv_val`).
- **`About`.**
  - `gsim_complin`: ∀ E F VE VF M S σ0 v0, `GSimRel VE VF M S → S (initial_tagged_module VE σ0) (PossOk v0 nil) → RCompLin M VE σ0 VF v0`. No other premise.
  - `rlhl_complin`: `RLHL2Hyps I R G M σ0 v0 → RCompLin M VE σ0 VF v0`.
- **`Print Assumptions`.**
  - `classic` only: `gsim_complin`, `rlhl_complin_ei`, `CounterCompLin.counter_complin`, `ooo_copycat_trace`, `junkF_not_counter_trace`.
  - Closed: `reify`, `cc_trace`, `junkF_not_rtrace`.
- **`Check`.**
  - `counter_complin : RCompLin Mc HVE hσ0 CVFe (0,nil)`.
  - `junkF_not_rtrace : ~ RTraces CVFe (0,nil) junkF`.
  - `ooo_trace` = [Inv1; Inv2; Res(2,1); Res(1,0)], all on thread t0.
- **Source read.**
  - `RelaxedHoareCompLin.v`: header :1-105, definitions :145-175, `rinv_val`/`rinv_reify`/`gsim_complin`/`rlhl_complin(_ei)` :1046-1141.
  - `RelaxedModuleSemantics.v:240-280` and `:575-625`. `must_precede` constrains only same-thread pairs (through `tagged_can_cross`). The Inv/Inv case is `~semi_independent op1 op2`, with op1 the earlier one.
  - `RelaxedHoareSpec.v:285-313`. `ei_step` has no freshness check, and a response matches its record by list membership.
  - `RelaxedTraceLin.v:55-90`. The same-thread clause of `rhb` is `~indep (op o) (op o')` with o earlier, so it runs in the same direction as F2.
  - `CompLin.v:100-170` (`TErr`, `ImplTraces`, `idImpl = Vis`, `ImplTracesClosed`).
  - `RelaxedHoareGSim.v:200-226`: items 4-5 are stale.
- **Repository-wide grep.**
  - No `.v` file in models/, examples/ or interfaces/ imports `memory.*`.
  - `RCompLin`/`RTraces`/`MTraces` are used only in the new file and in Checks.
  - There is no `MLTS`, absorption, `mtraces_prefix` or `rlhl_sound_complin`.
  - Nonempty SI exists in the RLHL instances `pair_rlhl2` (:2174), `xy_rlhl2` (:2996) and `log_rlhl2` (:6741), via `semi_independent := o1 <> o2` (:1916, :2808, :6306). The counter's SI is False (:623, :627).
- **Paper and reviews (quotes verified).**
  - Appendix/relaxedlin.tex:
    - :2-9 seqcopy;
    - :47-50 corollary rlx(ν_A) = ν_A;seqcopy_A;
    - :53-56 saturation proposition (no proof);
    - :58-61 the reduced correctness form;
    - :665-667 Soundness, ν_E;cc_E;M[Threads] ⊆ ν_F;cc_F.
  - relaxedlin.tex:
    - :17-24 ihbrew;
    - :29-30 REW;
    - :39-40 prop:rhb-equiv, "For all s,s′";
    - :62-69 the inlining equation;
    - :74 verimpl, "for every underlay implementation relaxed-linearizable to ν_E";
    - :88-99 vertical composition.
  - intro.tex:105-106; overview.tex:339; implex.tex:170-176 (prop:rlhl-sc concludes ⊑rlxlin).
  - popl2027-reviews.md:309-317 (Reviewer B) and :615 (meta-review).
- **Scratch sessions I re-ran** (piped `rocq repl`; nothing written). Both are Closed and produced no Error.

  **T1** (from the lens-3 verifier). `EVE_not_handle_linear` (∀ used, ¬HandleLinear (EI uδ) used) and `counter_ei_unsat` (∀ I R G q0 m0, ¬RLHL2Hyps I R G Mc q0 (m0,[]) over VE := EI uδ, VF := CVFe) are both "Closed under the global context":
```
Require Import Stdlib.Lists.List Stdlib.PArith.PArith Stdlib.Arith.PeanoNat Stdlib.micromega.Lia Stdlib.Relations.Relation_Operators.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareDag models.simlin.RelaxedHoare models.simlin.RelaxedHoareSound models.simlin.RelaxedTraceLin models.simlin.RelaxedHoareSpec.
Require Import examples.Relaxed.RelaxedHoareChecks.
Import ListNotations.
Module T1.
  Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedModuleSemantics RelaxedPossibility RelaxedHoareBase RelaxedHoareDag RelaxedHoare RelaxedHoareSound.
  Import RelaxedHoareChecks.Counter RelaxedHoareChecks.CounterHL.
  Definition EVE : LTS USig := RelaxedHoareSpec.EI RelaxedHoareChecks.CounterRelLin.uδ.
  Theorem EVE_not_handle_linear used : ~ HandleLinear EVE used.
  Proof.
    intros Hhl.
    assert (H1 : Step EVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) (0, []) (1, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0])).
    { cbn. exists 0, 1. split; [split; reflexivity | reflexivity]. }
    assert (H2 : Step EVE (Build_ThreadEvent t0 (@InvEv USig 0 FAA)) (1, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0]) (2, [@RelaxedTraceLin.Build_Op USig (t0, 0) FAA 1; @RelaxedTraceLin.Build_Op USig (t0, 0) FAA 0])).
    { cbn. exists 1, 2. split; [split; reflexivity | reflexivity]. }
    exact (hl_fresh _ _ Hhl t0 0 FAA _ _ H2 (hl_inv_used _ _ Hhl t0 0 FAA _ _ H1)).
  Qed.
  Theorem counter_ei_unsat (I : Assn EVE CVFe) (R G : CallKey OSig -> PRel EVE CVFe) (q0 : State EVE) (m0 : nat) :
    ~ RLHL2Hyps I R G Mc q0 (m0, []).
  Proof.
    intros HH. destruct q0 as [n0 l0].
    pose proof (h_sem _ _ _ _ _ _ HH) as Hsem.
    set (q1 := (S n0, @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0) : State EVE).
    assert (Hfirst : forall r : nat, exists A0 m2 p1,
      CallTriple I R G key0 Inc r A0 /\ untag m2 = Build_ThreadEvent t0 (@ResEv USig 0 FAA r) /\
      A0 [m2] (q1, p1, []) /\ I (q1, p1, []) /\ Good m0 p1 /\
      exists v pool, p1 = @PossOk OSig CVFe v pool /\ lin_domain pool = [key0]).
    { intros r. destruct (inc_trace_gen t0 0 r) as (tr & Hprod & Htr).
      destruct (Hsem t0 Inc 0 tr r Hprod) as (A0 & Htri & Hinit0).
      set (p0 := @PossOk OSig CVFe (m0, []) [make_lin_entry key0 (@ls_inv OSig Inc)]).
      assert (Hpi : poss_invoke CVFe t0 0 Inc (@PossOk OSig CVFe (m0, []) []) p0) by (constructor; constructor; intros []).
      destruct (Hinit0 (n0, l0) _ [] p0 (h_init _ _ _ _ _ _ HH) Hpi) as [HI0 HA0].
      destruct tr as [| m1 [| m2 [| m3 tr]]]; try discriminate. cbn in Htr. injection Htr as H1 H2.
      unfold ghost_new in HI0, HA0. cbn [app map] in HI0, HA0. rewrite H1, H2 in HI0, HA0.
      cbn [inv_events te_ev map] in HI0, HA0.
      pose proof Htri as [Hemit _ _].
      destruct (Hemit [] m1 [m2] ltac:(constructor) (n0, l0) p0 _ [] ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA0 HI0 q1 ltac:(rewrite H1; cbn; exists n0, (S n0); split; [split; reflexivity | reflexivity]))
        as (p1 & Hps & HA1 & HI1 & _).
      exists A0, m2, p1. split; [exact Htri |]. split; [exact H2 |]. split; [exact HA1 |]. split; [exact HI1 |].
      split.
      - eapply good_steps; [exact Hps |]. exists m0, [], [], (@ls_inv OSig Inc).
        split; [reflexivity |]. split; [left; reflexivity |]. split; [reflexivity |].
        split; [intros o [] | exact Logic.I].
      - destruct (h_ok _ _ _ _ _ _ HH _ HI1) as (v & pool & Hp1 & _). cbn in Hp1. subst p1.
        exists v, pool. split; [reflexivity |].
        rewrite <- (poss_steps_ok_domain CVFe _ _ _ _ Hps). reflexivity. }
    assert (HA : n0 = m0).
    { destruct (Hfirst n0) as (A0 & m2 & p1 & [Hemit _ Hret] & Hm2 & HA1 & HI1 & HG1 & _).
      destruct (Hemit [] m2 [] ltac:(constructor) q1 p1 [] [] ltac:(rewrite Hm2; reflexivity) HA1 HI1 (S n0, l0)
                  ltac:(rewrite Hm2; cbn; exists [], l0; split; reflexivity))
        as (p2 & Hps2 & HA2 & HI2 & _).
      destruct (Hret _ HA2 HI2 ltac:(intros e [])) as (p3 & Hps3 & (v & pool & -> & Hl) & _).
      exact (good_linr m0 v pool n0 (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps2 Hps3) HG1) Hl). }
    assert (HB : S n0 = m0).
    { destruct (Hfirst (S n0)) as (A0 & m2 & p1 & [Hemit0 Hstab0 Hret0] & Hm2 & HA1 & HI1 & HG1 & v & pool & -> & Hdom).
      destruct (inc_trace_gen t0 0 0) as (tr1 & Hprod1 & Htr1).
      destruct (Hsem t0 Inc 1 tr1 0 Hprod1) as (A1 & [Hemit1 _ _] & Hinit1).
      set (p1' := @PossOk OSig CVFe v (make_lin_entry key1 (@ls_inv OSig Inc) :: pool)).
      assert (Hpi : poss_invoke CVFe t0 1 Inc (@PossOk OSig CVFe v pool) p1').
      { constructor. constructor. unfold lin_fresh. rewrite Hdom. intros [H | []]. discriminate H. }
      destruct (Hinit1 q1 _ [] p1' HI1 Hpi) as [HI1' HA1'].
      pose proof (h_invoke_rely _ _ _ _ _ _ HH key1 key0 Inc tr1 0 (q1, @PossOk OSig CVFe v pool, []) p1'
                    ltac:(discriminate) Hprod1 HI1 Hpi) as HR.
      pose proof (Hstab0 [m2] _ _ HA1 HR HI1') as HA0'. cbn [ps_mem ps_ghost snd fst] in HA0'.
      destruct tr1 as [| n1 [| n2 [| n3 tr1]]]; try discriminate. cbn in Htr1. injection Htr1 as H1 H2.
      cbn [ps_mem ps_ghost snd fst] in HA0', HI1', HA1'.
      unfold ghost_new in HI1', HA1', HA0'. cbn [app map] in HI1', HA1', HA0'. rewrite H1, H2 in HI1', HA1', HA0'.
      cbn [inv_events te_ev map] in HI1', HA1', HA0'.
      set (q2 := (S (S n0), @RelaxedTraceLin.Build_Op USig (t0, 0) FAA (S n0) :: @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0) : State EVE).
      destruct (Hemit1 [] n1 [n2] ltac:(constructor) q1 p1' _ [] ltac:(rewrite H1; cbn; exists [], []; split; [reflexivity | split; [reflexivity | constructor]]) HA1' HI1' q2 ltac:(rewrite H1; cbn; exists (S n0), (S (S n0)); split; [split; reflexivity | reflexivity]))
        as (p2 & Hps2 & _ & HI2 & HG2).
      pose proof (h_guar_rely _ _ _ _ _ _ HH key1 key0 _ _ ltac:(discriminate) HG2) as HR2.
      pose proof (Hstab0 [m2] _ _ HA0' HR2 HI2) as HA2.
      destruct (Hemit0 [] m2 [] ltac:(constructor) q2 p2 [] [] ltac:(rewrite Hm2; reflexivity) HA2 HI2 (S (S n0), @RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0)
                  ltac:(rewrite Hm2; cbn; exists [], (@RelaxedTraceLin.Build_Op USig (t0, 0) FAA n0 :: l0); split; reflexivity))
        as (p3 & Hps3 & HA3 & HI3 & _).
      destruct (Hret0 _ HA3 HI3 ltac:(intros e [])) as (p4 & Hps4 & (v4 & pool4 & -> & Hl) & _).
      assert (HG2' : Good m0 p2) by exact (good_steps _ _ _ Hps2 (good_invoke1 _ _ _ HG1 Hpi)).
      exact (good_linr m0 v4 pool4 (S n0) (good_steps _ _ _ (rt_trans _ _ _ _ _ Hps3 Hps4) HG2') Hl). }
    lia.
  Qed.
End T1.
Print Assumptions T1.EVE_not_handle_linear.
Print Assumptions T1.counter_ei_unsat.
```
  **T2** (from the lens-3 verifier). `si_overtake_rtrace` is Closed: in the copy-cat over EI, a younger read overtakes an older pending semi-independent write of the same thread and reads 0.
```
Require Import Stdlib.Lists.List Stdlib.PArith.PArith.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics models.simlin.RelaxedModuleSemantics models.simlin.RelaxedTraceLin models.simlin.RelaxedGSim models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLin.
Import ListNotations.
Module T2.
  Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedLang RelaxedSemantics RelaxedModuleSemantics RelaxedHoareCompLin.
  Inductive WROp := WX | RX.
  Definition wr_ar (o : WROp) : Type := match o with WX => unit | RX => nat end.
  Canonical Structure WREff : Sig.t := {| Sig.op := WROp; Sig.ar := wr_ar |}.
  Definition WRSig : RelaxedSig.t := {| RelaxedSig.effect := WREff; RelaxedSig.handle := nat; RelaxedSig.semi_independent := fun o1 o2 => o1 <> o2; RelaxedSig.mode := fun _ => Local |}.
  Definition rdelta (n : nat) (o : Sig.op (RelaxedSig.effect WRSig)) : Sig.ar o -> nat -> Prop :=
    match o as o0 return Sig.ar o0 -> nat -> Prop with WX => fun _ n' => n' = 1 | RX => fun r n' => r = n /\ n' = n end.
  Definition t1 : tid := 1%positive.
  Definition sw : list (ThreadEvent WRSig) :=
    [Build_ThreadEvent t1 (@InvEv WRSig 1 WX); Build_ThreadEvent t1 (@InvEv WRSig 2 RX); Build_ThreadEvent t1 (@ResEv WRSig 2 RX 0)].
  Definition EV : LTS WRSig := RelaxedHoareSpec.EI rdelta.
  Definition trW := [@cc_inv_ev WRSig t1 1 WX; @cc_res_ev WRSig t1 1 WX tt].
  Definition trR := [@cc_inv_ev WRSig t1 2 RX; @cc_res_ev WRSig t1 2 RX 0].
  Definition k2 : CallKey WRSig := (t1, 2).
  Definition candI : TaggedScheduledEvent WRSig WRSig := Build_TaggedScheduledEvent k2 (@cc_inv_ev WRSig t1 2 RX).
  Definition candR : TaggedScheduledEvent WRSig WRSig := Build_TaggedScheduledEvent k2 (@cc_res_ev WRSig t1 2 RX 0).
  Theorem si_overtake_rtrace : RTraces EV (0, []) sw.
  Proof.
    eexists. eexists. split.
    - eapply tagged_module_execution_cons.
      { apply (@tagged_invoke WRSig WRSig EV idF t1 1 WX (0, []) [] [] [] trW tt).
        - intros [].
        - apply idF_produces.
        - split; [cbn; constructor; [intros [] | constructor] | intros k [<- | []] []]. }
      eapply tagged_module_execution_cons.
      { apply (@tagged_invoke WRSig WRSig EV idF t1 2 RX (0, []) _ _ _ trR 0).
        - intros [H | []]. cbn in H. discriminate H.
        - apply idF_produces.
        - split; [cbn; constructor; [intros [] | constructor] |]. intros k [<- | []] [H | []]. discriminate H. }
      eapply tagged_module_execution_cons.
      { eapply (tagged_underlay EV idF candI).
        - cbn. apply tagged_select_next.
          { right. split; [reflexivity |]. cbn. intros H. apply H. discriminate. }
          apply tagged_select_next.
          { right. split; [reflexivity |]. cbn. intros (op' & ret' & Hres). exact Hres. }
          apply tagged_select_here.
        - cbn. exists 0, 0. split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { eapply (tagged_underlay EV idF candR).
        - cbn. apply tagged_select_next.
          { right. split; [reflexivity |]. cbn. intros H. discriminate H. }
          apply tagged_select_next.
          { right. split; [reflexivity |]. cbn. intros H. exact H. }
          apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (@tagged_return WRSig WRSig EV idF t1 2 RX 0).
        - apply finish_here.
        - cbn. intros [H | [H | []]]; discriminate H. }
      apply tagged_module_execution_refl.
    - reflexivity.
  Qed.
End T2.
Print Assumptions T2.si_overtake_rtrace.
```
  Equivalent lens scripts: lens-1 S1 and lens-2 S5 are variants of T2, and lens-1 S2 is a variant of `EVE_not_handle_linear`. Each was reported Closed in its lens record, and I did not repeat them.

## Verdict
RLHL-3a delivers the author's decision, and its formulation is the right one.

**What holds.**
- **No hidden hypotheses.** `gsim_complin` and `rlhl_complin` are universal over every execution, complete or not, and over every VE and VF. They use `classic` once (`rinv_val`), for a case split that does not weaken the statement.
- **The replay is sound.** `reify` is Closed. Its frontier admissibility follows from TValid: F2 is the same-thread clause, in the same direction as `must_precede`; F1 is per handle; F3 is vacuous because the copy-cat's tags are empty.
- **MTraces is exactly "every prefix"**, like `CompLin.ImplTraces`. It is prefix-closed, because each module event contributes at most one overlay event.
- **`idF` is the paper's seqcopy** (Appendix/relaxedlin.tex:2-9).
- **The counter checks are genuine, and the copy-cat is neither too strict nor too lax at the mechanism level.** Junk is rejected for every copy-cat execution (`junkF_not_rtrace`, Closed), and semi-independent overtaking is admitted (T2, Closed).

**What does not yet hold.**
- (i) No theorem says what `RTraces (EI δ)` means, relative to `rel_lin` or REW (M-20, narrowed).
- (ii) The recorded layering interface "VE := EI δE" is mechanically refuted for RLHL2Hyps (T1; m-20 escalated to MAJOR).
- (iii) No absorption/saturation, linking or monotonicity lemmas exist, and RLHL-3c needs all of them (M-22).
- B-1 remains a BLOCKER against the paper and Reviewer B, narrowed to: memory VE, client, composition, and a nonempty-SI instance with a specification meaning.

**Recommendation: continue, no redesign.** One more cheap RLHL-3a round is worthwhile: item 5 via an identity GSimRel, EIhl plus HLift, the headers, and adopting T1/T2. Then RLHL-3b and RLHL-3c.

**Severity decisions.** No BLOCKER or MAJOR finding was withdrawn. I applied the verifier corrections. One verifier downgrade is overridden: the lens-1 verifier downgraded "EI is not handle-linear" to MINOR because "the consequence is only argued". T1 `counter_ei_unsat` mechanizes that consequence, and I re-ran it (Closed), so the item stays MAJOR.

## Findings

### BLOCKER

- **[B-1] (continues, narrowed) RLHL soundness now covers every execution, in copy-cat form, over the underlay LTS used in the derivation. Reviewer B's chain is still missing: no memory VE, no object with its client, no vertical composition, and no nonempty-SI instance with a specification meaning.** (research-level for the claims; RLHL-3b/3c and the memory route are actionable)
  - **Where.** `RelaxedHoareCompLin.v:1106-1139`; `RelaxedHoareChecks.v:5719-6247`; `RelaxedHoareGSim.v:852-872` (`rlhl_sound`, complete traces).
  - **K.** `gsim_complin`, `rlhl_complin_ei` and `counter_complin` depend on `classic`; `reify` and `junkF_not_rtrace` are Closed.
  - **S.**
    - For every VE and VF, every overlay trace of M over VE is an overlay trace of `idF` over VF. The statement fixes one VE, has one possibility and no error clause.
    - The only instance on the decided EI route is `Mc` over `HVE` into `EI cδ`. There SI = ∅ at both levels, and `Mc` is itself the FAA→Inc copy-cat. In effect this is SC linearizability with overlapping same-thread calls.
    - `pair_rlhl2`, `xy_rlhl2` and `log_rlhl2` (SI := o1≠o2) now also yield RCompLin, since there is no HVF premise. But their overlays take effect at the response and fail HVF (`pair_not_hvf`, Checks:3902), so those inclusions have no specification meaning.
  - **P.**
    - Appendix/relaxedlin.tex:665-667 (Soundness).
    - relaxedlin.tex:74 and overview.tex:339 ("over any underlay relaxed-linearizable to ν_E").
    - intro.tex:105 ("soundness with respect to RC11 … mechanized in Rocq").
    - intro.tex:106 ("one layered verification" of LatchSet and write-snapshot).
    - relaxedlin.tex:88-99 (Vertical Composition).
  - **R.** Reviewer B :313-316: "the program logic, its soundness proof against a weak memory model such as RC11, and the verification of a concurrent object alongside the verification of its client program". Meta-review :615: "the lack of a demonstration of client verification".
  - **Differences.**
    - The incomplete-trace part is now met, in the shape of P's Soundness, but without cc_E (M-22).
    - The weak-memory, client and layering parts are absent.
    - P's "any underlay" quantification is not covered.
    - The only window-route vertical link is example-specific: `SeqLockTower.tower_link`, at witness level, for complete traces only.
  - **Evidence (bottom layer, argued; the verifier upheld it with a refinement).** x86-TSO store forwarding is not a copy-cat trace over a thread-oblivious EI register δ, for any SI. The scenario: t0 runs Inv w x:=1; Inv r x; Res r 1, and then t1 runs Inv r x; Res r 0. The copy-cat forces eff(w) < eff(r_t0) < Res r_t0 < Inv r_t1 < eff(r_t1), so t1 must read 1. `ei_step`'s δ has no thread argument (RelaxedHoareSpec.v:296-302).
  - **Required.**
    1. RLHL-3b (M-19).
    2. RLHL-3c (M-22, m-20, M-20).
    3. A memory route: either memory LTS traces ⊆ `RTraces` of a thread-aware buffered δ_mem (ops carry tids, flushes nondeterministic inside δ), or a non-EI memory VF/VE. Both fit `gsim_complin`, which is generic.
    4. Until then, the paper may claim at most: "RLHL derivations imply that every (possibly incomplete) overlay trace of M over the underlay LTS used in the derivation is a trace of the relaxed copy-cat over the overlay LTS; for effect-at-invocation overlays of a sequential specification this is instantiated only for an I=∅ counter."

### MAJOR

- **[M-20] (continues, narrowed: the author decision is implemented; the residual is the *meaning* of RCompLin) No theorem relates `RTraces (EI δ)` to `rel_lin` (complete traces) or to REW (prefixes). The research record states the REW identity as fact.** (actionable (a)(b)(d); research-level (c))
  - Merges lens-1 M-23, lens-2 M-20 and lens-3 M-20.
  - **Where.** `RelaxedHoareCompLin.v:90-97` (item 5 "open") and :62-65; research-intent.md:122 ("This is the paper's REW notion").
  - **K.**
    - `junkF_not_rtrace` (Closed) is a negative point.
    - `ooo_copycat_trace` (`classic`) is a positive point, but it is linearizable in program order (W = [o1:0; o2:1]) at I=∅, so it is not a relaxation witness.
    - T2 (Closed) is the positive SI-overtaking point.
    - No general statement exists.
  - **S.** `rlhl_complin_ei` concludes `RTraces (EI δ)`; `rlhl_rel_lin_ei` separately concludes `rel_lin` for complete traces. Neither implies the other in Coq.
  - **P.**
    - implex.tex:170-176 (prop:rlhl-sc concludes ⊑rlxlin).
    - Appendix/relaxedlin.tex:47-50 (rlx(ν) = ν;seqcopy).
    - relaxedlin.tex:29-30 (REW) and :39-40 (prop:rhb-equiv "for all s, s′").
  - **R.** Reviewer B :309 ("difficult to trust them without a full formalization").
  - **Evidence (argued by all three lenses; I re-derived it).**
    - **Complete well-formed traces: RTraces(EI δ) = rel_lin (seq_legal δ s0).**
      - ⊆: take the effect order as W. Real time gives eff < res < inv < eff. Same-thread non-SI pairs are ordered by F2 = ¬SI(earlier, later), which equals rhb's ¬indep(op o, op o′).
      - ⊇: greedy placement of effect points in W order.
    - **Prefixes.** Copy-cat drop-closure equals REW's ihbrew (ii) closure.
    - **Non-well-formed traces.** `rel_lin` accepts some (for example a lone response, RelaxedTraceLin.v:79), so the equality needs wf.
    - **K.** `rl_prefix` is stricter for non-total δ.
    - **Consequence.** After vertical composition only `RTraces (EI δtop)` is available, so the end-to-end conclusion means relaxed linearizability only through this bridge.
  - **Required.**
    - (a) `cc_rel_lin`: every complete wf `RTraces (EI δ) (s0,[]) s` satisfies `rel_lin s (semi_independent F) (seq_legal δ s0)`. Recommended route: an explicit `GSimRel (EI δ) (EI δ) idF S_cc`, then `gsim_rel_lin` and `ei_hvf`, plus a small lemma that a complete idF trace makes every call DeadCall. This GSimRel sees `trace_fresh`; the RLHL2Hyps route over EI is blocked (T1). Alternative route: invert `reify` and reuse `transfer` and `ei_hvf`. Then derive `rlhl_complin_ei ⇒ rlhl_rel_lin_ei`.
    - (b) Adopt T2 and its I=∅ negative mirror as regressions.
    - (c) Research-level: either the paper defines incomplete-trace correctness as ν;cc and presents REW as an argued characterization, or Coq proves the REW agreement. In both cases, restrict prop:rhb-equiv to complete traces or prove it for prefixes.
    - (d) research-intent:122: change to "argued; data points `junkF_not_rtrace`, T2".

- **[m-20 → MAJOR] (escalated) The recorded layering interface "VE := EI δE, like HVE" is refuted for RLHL: EI is not handle-linear, and RLHL2Hyps has no model over literal EI for the correct overlapping counter.** (actionable)
  - Merges lens-1 M-24, lens-2 M-23(i) and lens-3 m-20.
  - **Where.** research-intent.md:123; `RelaxedHoareCompLin.v:51-56`; `RelaxedHoareSpec.v:296-302`; concern-matrix :74, :77.
  - **K.** T1 (re-run by me, Closed):
    - `EVE_not_handle_linear`: ∀ used, ¬HandleLinear (EI uδ) used;
    - `counter_ei_unsat`: ∀ I R G q0 m0, ¬RLHL2Hyps I R G Mc q0 (m0,[]) over VE := EI uδ.
  - **S.** The triple quantifies over the re-used-key schedule of `counter_ow_unsat`, which the module semantics excludes (`trace_fresh`).
    - EI keeps a duplicate record, and key0's response can match key1's record.
    - `invocation_ready` then forces n0 = m0 and S n0 = m0.
    - Over HVE (handle-linear, never removes records) the counter is provable (`counter_hl_rlhl2`), which isolates handle-linearity as the cause.
    - `gsim_complin` itself is unaffected; the defect is in the plan.
  - **P/R.** No paper statement. Reviewer B's layered object-plus-client requirement depends on this interface.
  - **Verifier disagreement resolved.**
    - The lens-1 verifier (MINOR, "consequence argued") and the lens-2 verifier ("EI keeps both records") predate the mechanization.
    - T1 shows the obstruction transfers precisely because EI keeps both records.
  - **Required.**
    1. Define `EIhl δ` (state (s, P, used); invocation only on unused keys) and prove `HandleLinear (EIhl δ)`.
    2. Prove `HLift`: MTraces (EI δ) M = MTraces (EIhl δ) M, from `trace_fresh`/`tm_used_underlay`. Optionally also prove `RTraces (EI δ) = RTraces (EIhl δ)`.
    3. Correct research-intent:123 and the CompLin header (:51-56) to read "VE := EIhl δE".
    4. Adopt T1 next to `counter_ow_unsat`.

- **[M-22] (new) RCompLin fixes one VE. Layering needs lemmas that do not exist, chiefly E-side copy-cat absorption (the paper's saturation proposition) and a semantic linking for futures. Until then "layering replaces presentation_choice" and the "every underlay" judgement are unsupported.** (actionable; it is the RLHL-3c prerequisite)
  - Merges lens-1 M-22, lens-2 M-23(ii)(iii) and lens-3 M-22.
  - **Where.**
    - `RelaxedHoareCompLin.v:69-78` (the header concedes the gap) and :163-175.
    - research-intent.md:123.
    - `RelaxedLang.v:61-74`: `Future` takes only a primitive op, and there is no fork.
    - `CompLinVComp.v:42-62`: `substProg` inlines at a blocking `Vis`.
  - **K.** Nothing is mechanized.
  - **S.** MTraces V M depends on V only through `Step` on emitted underlay events (`tagged_underlay`). Method traces and results are committed at invocation. So monotonicity in V's path language holds (argued).
  - **P.**
    - Appendix/relaxedlin.tex:53-56 (saturation, stated without proof) and :58-61 (the reduced form ν_E;⟦M⟧ ⊆ rlx(ν_F)). `RCompLin M (EI δE) … (EI δF)` matches this reduced form; the missing piece, in both the paper and Coq, is saturation.
    - relaxedlin.tex:62-69 (inlining), :74 (verimpl, "every underlay"), :88-99.
  - **R.** Reviewer B :313-316 (object plus client).
  - **Evidence (argued; two verifiers re-checked it).**
    - Absorption, `MTraces (Lift idF V) N ⊆ MTraces V N`: re-time each N underlay event to the copy-cat's V-emission.
      - F2 uses the same `semi_independent` on both sides.
      - F3 is preserved through V-res < C-res < N-inv < V-inv.
      - `owner_done` and `all_resolved` hold.
    - This needs V to be invariant under per-thread injective renaming of underlay handles, because `idF_produces` picks arbitrary handles while N computes on its FutureRefs. EI and EIhl satisfy this.
    - Over relaxed presentations no RLHL2Hyps exists for the counter (`counter_vt_no_rlhl2`, Closed; m-28). Absorption is therefore the only route to a relaxed underlay.
  - **Required (RLHL-3c, in order).**
    1. `Lift M VE σ0 : LTS F` (τ-closing internal underlay steps) with L(Lift) = MTraces.
    2. `mtraces_mono` (path-language inclusion lifts).
    3. `absorption` for renaming-invariant V, at least EI/EIhl.
    4. HLift (m-20).
    5. Item 5 (M-20). Its converse on prefixes is also needed if verimpl's "every underlay relaxed-linearizable to ν_E" is claimed.
    6. The composite: MTraces (Lift M1 VE σ0) M2 ⊆ RTraces (EI δG).
    7. A client semantics, for example a module into a one-operation "main" signature.
    8. Name the absorption lemma as the Coq counterpart of Appendix/relaxedlin.tex:53-56.

- **[M-19] (continues; title corrected) There is no nonempty-SI instance over a sequential-spec (EI/EIhl) overlay, and no relaxation witness at the module level.** (actionable, RLHL-3b)
  - **Where.** `RelaxedHoareCompLin.v:16-18` ("this is where relaxation comes from"); Checks:623, :627; Checks:5727-5729 (`ooo_trace`).
  - **K/S.**
    - `pair_rlhl2`, `xy_rlhl2` and `log_rlhl2` have SI := o1≠o2, but their overlays are not specifications (HVF refuted or unproved).
    - T2 gives only the copy-cat-level positive half.
    - The I=∅ negative mirror is argued from F2 and not mechanized.
  - **P.** intro.tex:99 ("pending, independent operations within the verifying thread").
  - **R.** Reviewer B :309-312 ("workable reasoning principles").
  - **Required.**
    - An RLHL2Hyps instance with nonempty SI over EIhl, for example a pass-through over T2's W/R signature, or two counters.
    - A three-level relaxation witness: positive under SI (T2), negative under ∅, and module-derived.
    - A two-future body whose own-event premise needs a genuine stability proof.

- **[M-15] (continues; one addition)** The decided EI layering covers sequential specifications only. intro.tex:106 attributes to RLHL an "interval-linearizable write-snapshot … one layered verification", and an interval-sequential write-snapshot is not `EI δ`: `ei_step` applies a single-operation δ once, at invocation. `rlhl_complin` is generic in VF, so this is a scope consequence of the author's "Sequential spec, EI" decision, not a limitation of the theorem. (research-level) **Required:** drop or re-attribute the write-snapshot claim, or record that it needs an interval-spec VF with its own item-5 analogue. The other M-15 items are unchanged.

### MINOR

- **[m-30] (new) Headers and records contradict `rlhl_complin`.** (actionable)
  - Stale text:
    - `RelaxedHoareGSim.v:202-213` (item 4: "nothing is stated about executions with pending calls … prefix soundness … not done");
    - `RelaxedHoareGSim.v:214-225` (item 5: "intended … VE := VT nuE, VF := VT nuF");
    - `RelaxedHoareSpec.v:21-42`; `RelaxedHoareBase.v:187-200`;
    - `RelaxedHoareCompLin.v:51-56` ("VE is meant to be EI δE");
    - concern-matrix rows 43, 69, 70, 76 and :207.
  - **Required.**
    - Point these to `RelaxedHoareCompLin.rlhl_complin` for incomplete traces.
    - Mark VT×VT as a complete-trace corollary only, and mark `implements`/`rl_prefix` as superseded for RLHL.
    - Cite T1 for the EI/handle-linearity caveat.

- **[m-8] (continues; new aspect relative to CompLin) There is no analogue of `TErr`/`ImplTracesClosed`.** (research-level)
  - Merges lens-1 m-8, lens-2 m-31 and lens-3 m-31.
  - **Where.** `RelaxedHoareCompLin.v:24-28`; `CompLin.v:120-125` and :151-168; `RelaxedModuleSemantics.v:578-610` (no error rule).
  - **The difference.**
    - Under EI (Error := False), a partial δ means the copy-cat blocks; it does not mean "undefined behaviour licenses any continuation".
    - So an implementation of a spec with preconditions (for example, a lock released when not held) is RCompLin only if it also blocks on misuse, or if δ has a chaos state.
    - Underlay `Error` is invisible.
  - **Required.**
    - Document "partial δ = blocking; differs from CompLin" (more precise than "underlay Error is invisible").
    - The author decides whether RLHL-3c, with lock-based layers, needs an error clause.

- **[m-32] (new; lens 2) Cheap paper-facing corollaries are missing.** (actionable) I confirmed by grep that none of these exist.
  - `rlhl_sound_complin`: derivations plus Hgr/Hir/Hrr/Hok/Hinit give RCompLin, with no HVF and no Hcomplete. The derivation route is already used by `counter_complin` (via `counter_hl_rlhl2`), but it is not stated generically.
  - `mtraces_prefix`: MTraces VE M σ0 (s1++s2) → MTraces VE M σ0 s1.

**Status changes without a finding entry.**
- **M-1:** superseded and closed for the RLHL route (copy-cat inclusion replaces `implements`/`rl_prefix`). A VLHL residual remains: prop:rlhl-sc (implex.tex:170) still rests on `vlhl_sound`/`presentation_choice`, complete traces only.
- **M-18:** VT×VT is a complete-trace corollary only; superseded for prefixes.
- **m-28:** still valid. It is now the reason that absorption (M-22) is the only route to relaxed underlays.

**Unchanged.** B-4, M-11, M-14, M-21 (add the row "Soundness, Appendix/relaxedlin.tex:665 ↔ `gsim_complin`/`rlhl_complin`"), m-12, m-15, m-22, m-23, m-24, m-27, m-29.

## Responses to Writer disputes
The Writer marked nothing DISPUTED. On its claims:
- **"M-20/Q3 FIXED for RLHL-3a scope": partly accepted.** The decision is implemented, and the theorem is universal and sound. M-20 stays open, narrowed to the meaning bridge (item 5, REW).
- **"M-1 DEFERRED": upgraded.** M-1 is closed for RLHL; only the VLHL residual remains.
- **Open issue 1 (item 5 ≈ 500 lines, JInv-style): accepted, but there is a cheaper route.** An identity GSimRel for `idF` over EI, plus `gsim_rel_lin` and `ei_hvf`, derives it from the general theorem and is reusable for RLHL-3c.
- **Open issue 2: accepted** (now m-30).
- **Open issue 4 (cc_E unmechanized): accepted** (now M-22, with an argued proof plan).
- **"No existing statement changed": accepted.** `git diff --stat` shows 54+/5- in five files; the orchestrator verified the diffs are comment-only, and the earlier `Check`s are unchanged.

## Concern-matrix corrections
- **:43 B3/B-post (i).** Add `gsim_complin`, `rlhl_complin`, `rlhl_complin_ei`, `counter_complin` (`classic`) and `reify` (Closed): every execution, copy-cat form, over the derivation's VE. Under Missing, replace "`implements`/prefixes (M-1, Q3)" with "absorption and linking (M-22), EIhl/HLift (m-20), item 5 (M-20), client, memory VE". The status stays ❌.
- **:69 RLHL layering / `implements`:** ❌ → 🟡. Copy-cat prefix soundness exists. The `implements` route is superseded for RLHL. Composition is missing (M-22).
- **:70 Prefix notion:** ⚠️ → 🟡 (decided: copy-cat over EI). Mechanized points: `junkF_not_rtrace`, T2. The equality with REW/rel_lin is argued (M-20). K differs for non-total δ; K and V matter only for VLHL.
- **:72 nonempty SI:** stays ❌. Add T2 as the copy-cat-level positive half, and note that pair/xy/log have nonempty SI over non-spec overlays.
- **:74 / :77 HL:** :77 stays ❌ but is now on the critical path (MAJOR). Add T1 (`EVE_not_handle_linear`, `counter_ei_unsat`). Required: EIhl plus HLift.
- **:75-76 spec style / end-to-end route:** the M-18 VT×VT route is superseded for prefixes. The decided route is VF := EI δF (copy-cat inclusion) and VE := EIhl δE, giving 🟡.
- **:82 m-8:** add the CompLin difference (partial δ means blocking).
- **:83 Prop. Logic Soundness:** add `rlhl_complin` as the all-traces form (generic derivation corollary m-32 pending).
- **:84 Simulation, Soundness (App. :665):** add `gsim_complin` (`classic`): copy-cat form, over M's VE, without cc_E (M-22).
- **:88 Vertical composition:** stays ❌. List the M-22 prerequisites.
- **:207 M-incomplete:** partially resolved by `gsim_complin` (copy-cat form). The `RelaxedTraceLin` side needs M-20.
- **§4 regressions.**
  - Closed: `reify`, `cc_trace`, `junkF_not_rtrace`.
  - `classic`: `gsim_complin`, `rlhl_complin`, `rlhl_complin_ei`, `rinv_reify`, `counter_complin`, `ooo_copycat_trace`, `junkF_not_counter_trace`.
  - After adoption: T1 (both theorems Closed) and T2 (Closed).
- **research-intent §8.**
  - :122: "REW … argued, not proved (M-20)".
  - :123: "VE := EIhl δE (EI admits no RLHL2Hyps for overlapping same-thread calls, T1); replacing presentation_choice is conditional on M-22".
- **Status summary.**
  - Closed for RLHL: M-1.
  - Narrowed: B-1, M-20.
  - Escalated: m-20 → MAJOR.
  - New: M-22, m-30, m-32.
  - Extended: m-8, M-15.
  - Superseded for prefixes: M-18.

## Stronger or alternative approaches
1. **Item 5 from the general theorem.** Build `GSimRel (EI δ) (EI δ) idF`, then use `gsim_rel_lin` and `ei_hvf`. This is the Coq ⊆ half of the corollary rlx(ν) = ν;seqcopy. The same construction is the unit law RLHL-3c needs.
2. **One uniform interface.** Define "correct w.r.t. a spec LTS V" as overlay traces ⊆ `RTraces V`. Use it for object layers (RCompLin), for the memory layer (with a thread-aware buffered δ_mem, or a non-EI LTS), and for clients (a module into a one-operation "main" signature). Compose with `mtraces_mono` and absorption.
3. **Prove absorption first.** It is the paper's own unproved saturation proposition, and it is the crux of every layering claim. State the handle-renaming invariance explicitly.
4. **EIhl as the canonical inter-layer presentation**, with HLift, instead of a used-key ghost in the triple.
5. **RLHL-3b cheaply.** Use T2's W/R signature (SI(W,R)) and verify a pass-through by RLHL over EIhl. That gives a nonempty-SI instance whose relaxation witness is module-derived.
6. **Paper.** State Soundness as mechanized: M over the derivation's VE, with M's own frontier. Present saturation as a separate (pending) lemma. Cite rlx(ν) = ν;cc only after item 5.

## Redesign assessment
- **No redesign** of RCompLin, `reify`, `gsim_complin` or `rlhl_complin`. CompLin-style copy-cat inclusion is the right formulation: it resolves the M-1/M-20 deadlock, matches the paper's ν;cc shape, and is generic in VE and VF.
- **Minimal plan correction, before RLHL-3b picks its VE.** The inter-layer underlay presentation must be handle-linear (EIhl, connected to EI by HLift). Layering must go through absorption plus monotonicity plus linking (M-22), not through a direct GSimRel over relaxed presentations (m-28).
- **Bottom-layer caveat.** Faithful oMCA store forwarding cannot be the copy-cat over a thread-oblivious EI register. The memory layer needs a thread-aware δ or a non-EI LTS, which the generic theorem already admits.

**Relevant files**
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareCompLin.v
- /Users/index/Documents/GitHub/rbgs-rlhl/examples/Relaxed/RelaxedHoareChecks.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareSpec.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedHoareGSim.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/RelaxedModuleSemantics.v
- /Users/index/Documents/GitHub/rbgs-rlhl/models/simlin/CompLin.v
- /Users/index/Documents/GitHub/rbgs-rlhl/.rocq-review/research-intent.md
- /Users/index/Documents/GitHub/rbgs-rlhl/.rocq-review/concern-matrix.md
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/relaxedlin.tex
- /Users/index/Documents/GitHub/async-ccal/drafts/relaxed-lin/Appendix/relaxedlin.tex