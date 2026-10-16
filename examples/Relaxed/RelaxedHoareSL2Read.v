(** * RelaxedHoareSL2Read: the RLHL derivation of the SeqLock reader over
      the history presentation [EIhlv], and the main theorem —
      RLHL-seqlock tasks .5 and .7

    Plan: .rocq-review/tasks/RLHL-seqlock.md, task .5 (the go/no-go
    checkpoint), with Addendum 2 ("RLHL in full": every method is a
    [MethodProvable] derivation through [run_method_provable]/[rp_run];
    no route S, no [ren_rlhl2] shortcut) and Addendum 3 (author decision
    option B: the underlay presentation is [EIhlv δS := Log (EIhl δS)]);
    reader evaluation .rocq-review/tasks/RLHL-seqlock-reader-eval.md
    (§1.3 B-6, §4); the gaps G1-G6 recorded in the header of
    [RelaxedHoareSL2InvLog]; review obligations m-63.  The program
    ([RelaxedHoareSL2Prog]), the frozen [Isl]/[Rsl]/[Gsl]/[Osl]/[Qrd]
    ([RelaxedHoareSL2Inv]), their lifts [IslV]/[RslV]/[GslV]/[QrdV] and
    the reader kit (Parts 5-6 of [RelaxedHoareSL2InvLog]) are used
    unchanged.  This file only adds.

    The reader [rnext i] (no call is tagged):
    [s <- rd Sq_i; rmb; a <- rd Sx_i; c <- rd Sy_i; rmb; s' <- rd Sq_i;
     if rok s s' then ret (a, c) else loop], where
    [rok s s' = even s && (s =? s')].

    ** Main results
    - [read_provable_v rc si tw Hsi : SL2ReadV rc si tw], for every [rc],
      every [tw] and every [si ⊇ slRA].  For every thread [t] and
      instance [i] it gives a syntactic derivation
      [MethodProvable IslV RslV GslV (M2w rc si tw) t (fR i) (Osl t (fR i))
       (fun h r s => QrdV (t, h) i r s /\ True)]
      over [VE := EIhlv δS], [VF := EI δF].  The derivation goes through
      [RelaxedHoareSL2InvLog.sl2_read_run_provable_v], hence
      [run_method_provable], [rp_run] and [RProvable_coind], with the
      machine invariant [rinv]; every [RunStepOK] is discharged by
      [rstep_ok].  [read_provable_vti] is the same for fixed [t] and [i].
    - [sl2_main : sl2rd_prov_target_v] (the derivation-carrying target of
      [RelaxedHoareSL2InvLog]).  It follows from [read_provable_v] and
      [RelaxedHoareSL2Write.write_provable] through
      [RelaxedHoareSL2InvLog.sl2rd_v_of_methods].  So for every
      [si ⊇ slRA] there are [I], [R], [G] (namely [IslV], [RslV], [GslV])
      with [MethodProvable] derivations of every method over [EIhlv δS],
      and [RLHL2Hyps] over [EIhlv δS] for [M2w rc si tw].
    - [sl2_complin : sl2rd_complin_target].  For every [si ⊇ slRA],
      [RCompLin (M2w rc si tw) (EI δS) (regs0, []) (EI δF) (A0, [])]: every
      overlay trace of the module, complete or not, is a trace of the
      copy-cat over the sequential specification
      ([sl2rd_complin_of_target_v], [RelaxedHoareLog.rlhl_complin_eihlv]).
    - [sl2_rel_lin : sl2rd_relin_target] (the target of
      [RelaxedHoareSL2Prog]).  Every complete trace of [M2w rc si tw] over
      [EI δS] is relaxed-linearizable at [si] ([sl2rd_relin_of_target_v]).
    - [lb2_not_trace_rd rc si tw t1 t2].  The cross-SeqLock LB trace
      [RelaxedHoareSL2Exec.lb2_trace si t1 t2] is not a trace of
      [M2w rc si tw] over [EI δS], for every [si].  This is
      [RelaxedHoareSL2Exec.lb2_not_trace_rd_of_rel_lin] with its
      hypothesis discharged by [sl2_rel_lin] at [slRA].
    - Part 10 (corollaries added after the final review; m-68, m-69,
      M-29):
      - [rlhl2_v_of_reads_inst]: the premise of
        [RelaxedHoareSL2Write.rlhl2_v_of_reads] discharged by
        [read_provable_v], for every [si ⊇ slRA];
      - [sl2_complin_unguarded], [sl2_rel_lin_unguarded]: P1 as a
        precondition.  For the unguarded [M2 rc si], every trace [s] with
        [P1 tw s] is a copy-cat trace (resp. relaxed-linearizable at [si]
        if complete), for every [si ⊇ slRA];
      - [sl2_no_mp]: no complete trace of [M2w rc si tw] is MP-shaped
        ([RelaxedHoareSL2Exec.mp_shaped]), for every [si];
      - [sbo_not_trace_rd]: the SeqLock-level SB-with-own-reads trace
        [RelaxedHoareSL2Exec.sbo] is not a trace of [M2w rc si tw] over
        [EI δS], for every [si].

    ** The derivation
    - Positions.  Call [c] of a run has its invocation slot at [2 c] and
      its response slot at [2 c + 1].  Iteration [m] is calls
      [6 m .. 6 m + 5] (G, A, X, Y, B, T: [rd Sq_i], [rmb_a], [rd Sx_i],
      [rd Sy_i], [rmb_b], the final [rd Sq_i]), at positions
      [12 m .. 12 m + 11].  The calls of any run, for any number of
      iterations, are a prefix of this pattern ([RCallsR]: call [c] has
      operation [rop (c mod 6)] and no tag).
    - The own dag (Part 2), from [RelaxedHoareRun.dprec_run] and the
      [sindep] table.  Every [rmb] is ordered with every other invocation,
      in both directions.  The final [rd Sq_i] of an iteration precedes
      the first one of the next (same location).  Each response follows
      only its own invocation.  Hence every invocation precedes every
      later slot, except that [rd Sx_i] does not precede the [rd Sy_i] of
      the same iteration or its response ([bef_inv], [bef_pos]);
      responses precede nothing.
    - Slots (Part 4).  The slot at position [j] is [rslot L j ev].  Its
      start, in-edges, post and guarantee are determined by [j mod 12],
      by its event (own handle and value), and by the handles of the
      iteration's G, X, Y and the value of G's response, read from the
      events [L] below [j] ([ghat], [gvat]).  [SlotsOK]: every slot of the
      context is canonical.  The in-edges that carry facts ([FE]):
      - [T] of the previous iteration [-> G]: [KHas];
      - [G -> A]: [EdgeG], [RecNB], [KHas];
      - [A -> X], [A -> Y]: [EdgeG], [KHas];
      - [G -> B]: [RecNB];
      - [X -> B], [Y -> B]: [EdgeD], [KHas];
      - [B -> T]: [Pkg] or "owns an [rmb]", [KHas];
      - [T ->] its response: [PkgT] or "owns an [rmb]", only when the
        response value validates.
      The posts are the kit's; a read's response logs its value ([KRd]).
    - Guarantees: [GslV k] at the two [rmb]s (each may be the
      linearization point); [liftGL (GslFix k)] at the reads (the
      possibility is kept); [liftGL (GslRes k)] at the responses (the
      possibility and the ghost are kept).
    - Interference: one lemma, [rnew], gives every [NewSlotOK].  Each
      assertion has a stability class ([kcls]):
      - 0 (logged values, [EdgeG], [EdgeD], [RecNB]): stable under every
        own guarantee;
      - 1 ([KHas]): stable under [GslFix] and [GslRes];
      - 2 ([Pkg]/[PkgT] or "owns an [rmb]"): stable under [GslRes] only.
      The order facts [fe_le] show that no [rmb] lies between the ends of
      a class-1 edge, and that every invocation before the target of a
      class-2 edge precedes its source.  So every [ns_if_*] premise is
      either a stability fact or refuted by the order ([bef_pos]).  The
      response of a final read that does not validate has in-edge
      [True] ([NoLoop]), so a later iteration's linearization point does
      not disturb it (G3).
    - Updates (Part 5): one per position, each an instance of a kit
      lemma by [evupdate_conseq]: [rd_G_update], [rd_rmbA_update],
      [rd_X_update], [rd_Y_update], [rd_rmbB_update], [rd_T_update],
      [rd_resT_update], [rd_res_logged_update], [rd_res_update].
    - One call (Part 6, [rcall]): [RunCallOK] from the two updates.  As in
      [RelaxedHoareSL2Write], the invocation slot is checked in the run
      context completed by a dummy response ([rsar_inh]), and the
      response slot in the context rebuilt by [runctx_snoc] and
      [resolve_here].
    - The loop (Part 7).  [rinv st cs Γ H] holds when: [RCallsR cs];
      [SlotsOK Γ]; [NoLoop] (the completed iterations did not validate);
      the position in the iteration ([length cs mod 6]) matches the
      machine state; and the values carried by the state are the values
      of the response slots at the corresponding positions.  It
      quantifies over the number of iterations through [length cs].
    - The return ([rclose]).  [Close] is by [close_done].  The [fin]s are
      nontrivial only at the four response slots of the validating (last)
      iteration ([rfin]).  [bw_sum] is
      [RelaxedHoareSL2InvLog.sl_read_close_rd]: the logged values of the
      four reads (the same keys as the package, by [hat_pair]),
      [rok s s' = true] from [rinv], and [PkgT] or "owns an [rmb]" give
      [QrdV k i (a, c)].  The footprint [Osl] ([RdShape]) is
      [rdshape_calls].

    ** Gaps G1-G6 (SL2InvLog header) and review m-63, as closed here
    - G1 (B-6 on the final edges): the [B -> T] and [T ->] response edges
      and the final [fin] carry [Pkg]/[PkgT] or "owns an [rmb]"; [QrdV]'s
      [¬ NoOwn] disjunct is used at [Close].
    - G2: the response slots guarantee [GslRes] (possibility and ghost
      kept).
    - G3: the in-edge and the post of the final read's response depend on
      [rok s v] ([rin_k] and [rpost_k] at position 11, [NoLoop]).
    - G4: [KHas] travels only on the invocation-chain edges listed above,
      never on [G -> B] (an [rmb] lies between).
    - G5: the [RecNB] of the iteration's first [rd Sq_i] is established at
      G ([rd_G_update]) and carried on [G -> A] and [G -> B].
    - G6: the validating iteration occupies positions
      [2 |cs| - 12 .. 2 |cs| - 1]; its handles and values are read off the
      events ([hat], [vat]).
    - m-63 (1), (2), (3), (5): as G1, as G2, by the interference argument
      above, and by [hat_pair] (the [fin]s and the package name the same
      keys).
    - m-63 (4), "phantom paths with more iterations than the ghost need
      [NoOwn]": not needed.  Every update lemma of the kit holds in every
      state whose ghost contains the emitted event, whether or not the
      ghost follows the machine path.  On any path, the last [rmb_b]
      yields [Pkg] or "still owns an [rmb]", and that is all [Close]
      uses.
    - m-63 (6): [sl_logval_rd] is in [RelaxedHoareSL2InvLog].

    ** K / S / P / R
    - K (Print Assumptions, Rocq 9.3.0): 72 of the 79
      [Lemma]/[Theorem]/[Corollary] results are closed under the global
      context, among them [read_provable_v], [read_provable_vti], [rnew],
      [rcall], [rclose], [rstep_ok], [sl2_main] and
      [rlhl2_v_of_reads_inst].
      - [sl2_complin] and [sl2_complin_unguarded] use
        [Classical_Prop.classic], inherited from
        [RelaxedHoareCompLin.rlhl_complin_ei] through
        [RelaxedHoareLog.rlhl_complin_eihlv].
      - [sl2_rel_lin], [lb2_not_trace_rd], [sl2_rel_lin_unguarded],
        [sl2_no_mp] and [sbo_not_trace_rd] use [classic] and
        [Eqdep.Eq_rect_eq.eq_rect_eq], the latter inherited from
        [RelaxedGSim.gsim_rel_lin] through [cc_rel_lin].
      No proof here uses an axiom directly; there is no [vm_compute] or
      [native_compute].
    - S: [read_provable_v] and [sl2_main] hold for every [rc], every [tw]
      and every [si ⊇ slRA].  [slRA] is used only by the readiness of the
      read's linearization point against an older write of another
      instance ([ready_read]).  [sl2_complin] is [RCompLin] over the plain
      [EI δS] (every trace, complete or not); [sl2_rel_lin] covers complete
      traces only.  There is no hypothesis beyond [si ⊇ slRA].  Scope, as
      stated in [RelaxedHoareSL2Prog]:
      - the underlay is a sequential, multi-copy-atomic register file with
        ordering-only barriers [wmb]/[rmb] (the [WindowTable.dto] table);
      - the overlay specification is effect-at-invocation [EI δF];
      - one writer per instance (P1: writes on other threads diverge;
        the precondition form for the unguarded [M2] is
        [sl2_complin_unguarded], Part 10);
      - the writer is "a single-writer seqcount whose closing increment
        reuses the opening read" (cached [v]; M-23), not the Linux
        writer; the SB datum of [RelaxedHoareSL2Exec] depends on it;
      - the verified [slRA] contract is falsified under store
        forwarding: the SB-with-own-reads outcome is not
        relaxed-linearizable under any relation contained in [slRA]
        ([RelaxedHoareSL2Exec.sbo_not_rel_lin], kernel-checked at trace
        level; that x86-TSO and ARMv8 produce it is argued, not
        mechanized).  This is an MCA-only data point (review M-29).
      The derivations are over the history presentation [EIhlv]; the
      conclusions are over [EI δS] ([RelaxedHoareLog.loglift_ei]).
    - P: there is no SeqLock text in the main paper (plan §1);
      Appendix/SeqLock.tex is a different, TicketLock-based object.  The
      rules are the mechanized RLHL of [RelaxedHoare] (the printed rules
      of Appendix/programlogic.tex differ; see the table in its header,
      M-21), in the run-interpreter form of [RelaxedHoareRun] (review
      m-66).  The history presentation restores the underlay projection
      of the paper's proof state (Appendix/programlogic.tex:579, rule
      EStep; lines as in async-ccal commit 4a2db8e1, where EStep moved
      from :537 of 01484091), not its overlay events or its reachability
      clause.  Nothing here supports implex.tex:3 ("RLHL
      is complete ..."), which is not claimed.
    - R: popl2027-reviews.md:215 ("No example verified on the COH model").
      This is an RLHL-verified object over COH registers with barriers,
      with the caveats above: the paper's COH (trace.tex:75) has no
      barriers; MCA; single writer; cached [v].  It does not answer
      B:212 or B:309-316 (no RC11 soundness, no client; B-1), and it is
      no evidence about TSO, ARMv8, oMCA or store forwarding (M-29:
      [RelaxedHoareSL2Exec.sbo_not_rel_lin]).

    ** Limitations
    - The read's linearization point is chosen through the ghost (its last
      [rmb]): the single-possibility, ghost-prophetic LP of m-33.  The
      ghost stores no response values, but its remaining invocations,
      committed at invocation, determine the outcome of the call's own
      future validation, so this is a future-dependent LP; it is sound by
      run-to-completion (impl.tex:141, :172).  Cf.
      Appendix/relaxedlin.tex:520, :628 (review m-65).
    - The run-context order facts ([bef_inv], [bef_pos], [hat_pair],
      [fe_kin_edge]) are proved for the reader's call pattern only, not as
      generic [RelaxedHoareRun] lemmas (m-53).
    - [lb2_not_trace_rd] and Part 10 require [RelaxedHoareSL2Exec]
      (only its traces [lb2_trace], [sbo], the predicate [mp_shaped] and
      the trace-level theorems about them are used) and
      [RelaxedHoareResig] (to move a trace to [slRA]). *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia Relations.Relation_Operators.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.view.PrefixView.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import models.simlin.RelaxedHoareRun.
Require Import models.simlin.RelaxedHoareReady.
Require Import models.simlin.RelaxedHoareLog.
Require Import examples.Relaxed.RelaxedHoareSL2Prog.
Require Import examples.Relaxed.RelaxedHoareSL2Inv.
Require Import examples.Relaxed.RelaxedHoareSL2InvLog.
Require Import examples.Relaxed.RelaxedHoareSL2Write.
Require examples.Relaxed.RelaxedHoareSL2Exec.
Require models.simlin.RelaxedHoareResig.

Import ListNotations.

Module RelaxedHoareSL2Read.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareCompLinSpec.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.
  Import RelaxedHoareRun.
  Import RelaxedHoareReady.
  Import RelaxedHoareLog.
  Import RelaxedHoareSL2Prog.
  Import RelaxedHoareSL2Inv.
  Import RelaxedHoareSL2InvLog.

  (** ** Part 0. Arithmetic: division and remainder by a constant *)

  (** [lia] does not reason about [x mod c] and [x / c]; [dlia] first
      replaces each such term by a fresh variable constrained by
      [x = c * (x / c) + x mod c] and [x mod c < c]. *)
  Ltac dm1 x c :=
    let r := fresh "r" in let q := fresh "q" in
    pose proof (Nat.div_mod_eq x c); pose proof (Nat.mod_upper_bound x c ltac:(discriminate));
    set (r := x mod c) in *; set (q := x / c) in *; clearbody r q.

  Ltac divmod := repeat match goal with
    | H : context [?x mod ?c] |- _ => dm1 x c
    | |- context [?x mod ?c] => dm1 x c
    | H : context [?x / ?c] |- _ => dm1 x c
    | |- context [?x / ?c] => dm1 x c
    end.

  Ltac dlia := divmod; lia.

  (** ** Part 1. Events by position *)

  Section Acc.
    Context {rc : bool}.
    Local Abbreviation ES := (E_S rc).

    (** The value of a response of [o]: the result of a read, [0]
        otherwise (first-order, as [RelaxedHoareSL2Prog.natv]). *)
    Definition sval (o : SOp) : sar o -> nat :=
      match o as o0 return sar o0 -> nat with sRd _ => fun r => r | _ => fun _ => 0 end.

    Definition evh (e : TaggedEvent ES) : nat := event_handle (te_ev ES (untag e)).

    Definition evv (e : TaggedEvent ES) : nat :=
      match te_ev ES (untag e) with ResEv _ o r => sval o r | InvEv _ _ => 0 end.

    (** The handle and the value of the event at position [p]. *)
    Definition hat (L : list (TaggedEvent ES)) (p : nat) : nat :=
      match nth_error L p with Some e => evh e | None => 0 end.

    Definition vat (L : list (TaggedEvent ES)) (p : nat) : nat :=
      match nth_error L p with Some e => evv e | None => 0 end.

    (** The same, read only below position [j] (what a slot appended at
        position [j] can see). *)
    Definition ghat (L : list (TaggedEvent ES)) (j p : nat) : nat := if p <? j then hat L p else 0.
    Definition gvat (L : list (TaggedEvent ES)) (j p : nat) : nat := if p <? j then vat L p else 0.

    Lemma hat_app (L L' : list (TaggedEvent ES)) p : p < length L -> hat (L ++ L') p = hat L p.
    Proof. intros Hp. unfold hat. rewrite nth_error_app1 by exact Hp. reflexivity. Qed.

    Lemma vat_app (L L' : list (TaggedEvent ES)) p : p < length L -> vat (L ++ L') p = vat L p.
    Proof. intros Hp. unfold vat. rewrite nth_error_app1 by exact Hp. reflexivity. Qed.

    Lemma ghat_app (L L' : list (TaggedEvent ES)) j p : j <= length L -> ghat (L ++ L') j p = ghat L j p.
    Proof.
      intros Hj. unfold ghat. destruct (Nat.ltb_spec p j); [apply hat_app; lia | reflexivity].
    Qed.

    Lemma gvat_app (L L' : list (TaggedEvent ES)) j p : j <= length L -> gvat (L ++ L') j p = gvat L j p.
    Proof.
      intros Hj. unfold gvat. destruct (Nat.ltb_spec p j); [apply vat_app; lia | reflexivity].
    Qed.

    Lemma ghat_lt (L : list (TaggedEvent ES)) j p : p < j -> ghat L j p = hat L p.
    Proof. intros Hp. unfold ghat. destruct (Nat.ltb_spec p j); [reflexivity | lia]. Qed.

    Lemma gvat_lt (L : list (TaggedEvent ES)) j p : p < j -> gvat L j p = vat L p.
    Proof. intros Hp. unfold gvat. destruct (Nat.ltb_spec p j); [reflexivity | lia]. Qed.

    Lemma ghat_full (L : list (TaggedEvent ES)) j p : length L <= j -> ghat L j p = hat L p.
    Proof.
      intros Hj. unfold ghat, hat. destruct (Nat.ltb_spec p j); [reflexivity |].
      rewrite (proj2 (nth_error_None L p)) by lia. reflexivity.
    Qed.

    Lemma gvat_full (L : list (TaggedEvent ES)) j p : length L <= j -> gvat L j p = vat L p.
    Proof.
      intros Hj. unfold gvat, vat. destruct (Nat.ltb_spec p j); [reflexivity |].
      rewrite (proj2 (nth_error_None L p)) by lia. reflexivity.
    Qed.

    Lemma hat_snoc_last (L : list (TaggedEvent ES)) e : hat (L ++ [e]) (length L) = evh e.
    Proof. unfold hat. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

    Lemma vat_snoc_last (L : list (TaggedEvent ES)) e : vat (L ++ [e]) (length L) = evv e.
    Proof. unfold vat. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

    Lemma hat_evs {F} {VE : LTS ES} {VF : LTS F} (Γ : list (Slot VE VF)) p sp :
      nth_error Γ p = Some sp -> hat (evs Γ) p = evh (sl_ev sp).
    Proof. intros Hp. unfold hat. rewrite nth_error_evs, Hp. reflexivity. Qed.

    Lemma vat_evs {F} {VE : LTS ES} {VF : LTS F} (Γ : list (Slot VE VF)) p sp :
      nth_error Γ p = Some sp -> vat (evs Γ) p = evv (sl_ev sp).
    Proof. intros Hp. unfold vat. rewrite nth_error_evs, Hp. reflexivity. Qed.
  End Acc.

  (** ** Part 2. The calls of the reader and its dependency dag *)

  Section Dag.
    Context (rc : bool) (si : FOp -> FOp -> Prop) (i : nat).

    Local Abbreviation ES := (E_S rc).
    Local Abbreviation FS := (F2 si).
    Local Abbreviation V := (EIhlv (E := E_S rc) δS).
    Local Abbreviation VF := (RelaxedHoareSpec.EI (F := F2 si) δF).

    (** The operation of the [c]-th call of the reader is [rop (c mod 6)]:
        an iteration is [rd Sq_i; rmb; rd Sx_i; rd Sy_i; rmb; rd Sq_i]. *)
    Definition rop (q : nat) : SOp :=
      match q with 0 => sRd (Sq i) | 1 => sRmb | 2 => sRd (Sx i) | 3 => sRd (Sy i) | 4 => sRmb | _ => sRd (Sq i) end.

    (** The calls [cs] of a run of the reader (any number of iterations):
        the [c]-th has operation [rop (c mod 6)] and no tag. *)
    Definition RCallsR (cs : list (RCall ES)) : Prop :=
      forall c x, nth_error cs c = Some x -> rc_op x = rop (c mod 6) /\ rc_dix x = [].

    Lemma rcalls_nil : RCallsR [].
    Proof. intros c x Hc. destruct c; discriminate. Qed.

    Lemma rcalls_snoc cs hu : RCallsR cs -> RCallsR (cs ++ [@mkRCall ES hu (rop (length cs mod 6)) []]).
    Proof.
      intros Hr c x Hc. destruct (nth_error_snoc_cases _ _ _ _ Hc) as [(_ & Hc') | (-> & ->)]; [exact (Hr c x Hc') |].
      split; reflexivity.
    Qed.

    Lemma nsi_rmb_r q : ~ sindep rc (rop q) sRmb.
    Proof. destruct q as [|[|[|[|[|q]]]]]; cbn [rop]; unfold sindep; destruct rc; cbn; discriminate. Qed.

    Lemma nsi_rmb_l q : ~ sindep rc sRmb (rop q).
    Proof. destruct q as [|[|[|[|[|q]]]]]; cbn [rop]; unfold sindep; destruct rc; cbn; discriminate. Qed.

    Lemma nsi_ord qa qj :
      qa = 1 \/ qa = 4 \/ qj = 1 \/ qj = 4 \/ ((qa = 0 \/ qa = 5) /\ (qj = 0 \/ qj = 5)) ->
      ~ sindep rc (rop qa) (rop qj).
    Proof.
      intros [-> | [-> | [-> | [-> | [[-> | ->] [-> | ->]]]]]];
        first [ exact (nsi_rmb_l qj) | exact (nsi_rmb_r qa) | apply sindep_same_loc; reflexivity ].
    Qed.

    Section Ctx.
      Context (k : CallKey FS).

      (** An (F2) edge between the invocations of calls [a < j]. *)
      Lemma dp_inv (Γ : list (Slot V VF)) H cs a j :
        RunCtx k Γ H cs -> RCallsR cs -> a < j -> j < length cs ->
        ~ sindep rc (rop (a mod 6)) (rop (j mod 6)) -> dprec (evs Γ) (2 * a) (2 * j).
      Proof.
        intros Hc Hr Ha Hj Hn.
        destruct (nth_error cs j) as [c |] eqn:Ej; [| apply nth_error_None in Ej; lia].
        destruct (nth_error cs a) as [ca |] eqn:Ea; [| apply nth_error_None in Ea; lia].
        apply (proj2 (dprec_run k Γ H cs (2 * a) (2 * j) Hc)).
        exists j, c. split; [exact Ej |]. left. split; [reflexivity |].
        exists a, ca. split; [exact Ea |]. split; [exact Ha |]. left. split; [reflexivity |].
        rewrite (proj1 (Hr a ca Ea)), (proj1 (Hr j c Ej)). exact Hn.
      Qed.

      Lemma dp_ord (Γ : list (Slot V VF)) H cs a j :
        RunCtx k Γ H cs -> RCallsR cs -> a < j -> j < length cs ->
        a mod 6 = 1 \/ a mod 6 = 4 \/ j mod 6 = 1 \/ j mod 6 = 4 \/
        ((a mod 6 = 0 \/ a mod 6 = 5) /\ (j mod 6 = 0 \/ j mod 6 = 5)) ->
        dprec (evs Γ) (2 * a) (2 * j).
      Proof. intros Hc Hr Ha Hj Ho. apply (dp_inv Γ H cs a j Hc Hr Ha Hj). apply nsi_ord. exact Ho. Qed.

      (** The edge from an invocation to its own response. *)
      Lemma dp_res (Γ : list (Slot V VF)) H cs j : RunCtx k Γ H cs -> j < length cs -> dprec (evs Γ) (2 * j) (S (2 * j)).
      Proof.
        intros Hc Hj. destruct (nth_error cs j) as [c |] eqn:Ej; [| apply nth_error_None in Ej; lia].
        apply (proj2 (dprec_run k Γ H cs (2 * j) (S (2 * j)) Hc)).
        exists j, c. split; [exact Ej |]. right. split; reflexivity.
      Qed.

      (** Every pair of invocations is ordered except a data read [rd Sx_i]
          and the [rd Sy_i] right after it: the [rmb]s are barriers, and the
          last read of an iteration precedes the first of the next (same
          location). *)
      Lemma bef_inv (Γ : list (Slot V VF)) H cs a j :
        RunCtx k Γ H cs -> RCallsR cs -> a <= j -> j < length cs -> ~ (a mod 6 = 2 /\ j = S a) ->
        before (evs Γ) (2 * a) (2 * j).
      Proof.
        intros Hc Hr Haj Hj Hx.
        assert (Hd : forall a' j', a' < j' -> j' < length cs ->
                  a' mod 6 = 1 \/ a' mod 6 = 4 \/ j' mod 6 = 1 \/ j' mod 6 = 4 \/
                  ((a' mod 6 = 0 \/ a' mod 6 = 5) /\ (j' mod 6 = 0 \/ j' mod 6 = 5)) ->
                  before (evs Γ) (2 * a') (2 * j')).
        { intros a' j' H1 H2 H3. apply before_dprec. exact (dp_ord Γ H cs a' j' Hc Hr H1 H2 H3). }
        destruct (Nat.eq_dec a j) as [-> | Hne]; [apply before_refl |].
        assert (Hm : a mod 6 < 6) by (apply Nat.mod_upper_bound; discriminate).
        destruct (Nat.eq_dec (a mod 6) 1) as [E | E1]; [apply Hd; dlia |].
        destruct (Nat.eq_dec (a mod 6) 4) as [E | E4]; [apply Hd; dlia |].
        destruct (Nat.eq_dec (a mod 6) 0) as [E | E0].
        { destruct (Nat.eq_dec j (S a)) as [-> | Hj1]; [apply Hd; dlia |].
          apply (before_trans _ _ (2 * S a)); apply Hd; dlia. }
        destruct (Nat.eq_dec (a mod 6) 3) as [E | E3].
        { destruct (Nat.eq_dec j (S a)) as [-> | Hj1]; [apply Hd; dlia |].
          apply (before_trans _ _ (2 * S a)); apply Hd; dlia. }
        destruct (Nat.eq_dec (a mod 6) 2) as [E | E2].
        { destruct (Nat.eq_dec j (S (S a))) as [-> | Hj2]; [apply Hd; dlia |].
          apply (before_trans _ _ (2 * S (S a))); apply Hd; dlia. }
        (* a mod 6 = 5 *)
        destruct (Nat.eq_dec j (S a)) as [-> | Hj1]; [apply Hd; dlia |].
        destruct (Nat.eq_dec j (S (S a))) as [-> | Hj2]; [apply Hd; dlia |].
        apply (before_trans _ _ (2 * S (S a))); apply Hd; dlia.
      Qed.

      (** The same, by slot position: an invocation slot [y] precedes
          every later slot [n], except the [rd Sy_i] invocation and
          response that follow an [rd Sx_i] invocation. *)
      Lemma bef_pos (Γ : list (Slot V VF)) H cs y n :
        RunCtx k Γ H cs -> RCallsR cs -> y mod 2 = 0 -> y <= n -> n < length Γ ->
        ~ (y mod 12 = 4 /\ (n = y + 2 \/ n = y + 3)) -> before (evs Γ) y n.
      Proof.
        intros Hc Hr Hy Hyn Hn Hx. pose proof (runctx_len k Γ H cs Hc) as Hl.
        assert (Ha : exists a, y = 2 * a) by (exists (y / 2); dlia). destruct Ha as [a ->].
        assert (Hj : exists j, n = 2 * j \/ n = S (2 * j)) by (exists (n / 2); dlia).
        destruct Hj as [j [-> | ->]].
        - apply (bef_inv Γ H cs a j Hc Hr); dlia.
        - apply (before_step _ _ (2 * j)); [| apply (dp_res Γ H cs j Hc); lia].
          apply (bef_inv Γ H cs a j Hc Hr); dlia.
      Qed.

      (** The invocation and the response of one call have the same handle. *)
      Lemma hat_pair (Γ : list (Slot V VF)) H cs j :
        RunCtx k Γ H cs -> j < length cs -> hat (evs Γ) (2 * j) = hat (evs Γ) (S (2 * j)).
      Proof.
        intros Hc Hj. destruct (nth_error cs j) as [c |] eqn:Ej; [| apply nth_error_None in Ej; lia].
        destruct (runctx_inv_at k Γ H cs j c Hc Ej) as (s1 & H1 & E1 & _).
        destruct (runctx_res_at k Γ H cs j c Hc Ej) as (s2 & v & H2 & E2).
        rewrite (hat_evs Γ _ _ H1), (hat_evs Γ _ _ H2). unfold evh. rewrite E1, E2. reflexivity.
      Qed.
    End Ctx.
  End Dag.

  (** ** Part 3. Slot kinds, in-edges and the order facts they need *)

  (** The kinds of slot assertions (interpreted by [ka] below). *)
  Inductive RK : Type :=
  | RKT                                     (* True *)
  | RKH                                     (* KHas: the read is in the pool *)
  | RKG (hG : nat)                          (* post of the first rd Sq_i *)
  | RKA (hG : nat)                          (* post of rmb_a *)
  | RKX (hG hX : nat)                       (* post of rd Sx_i *)
  | RKY (hG hY : nat)                       (* post of rd Sy_i *)
  | RKN (hG : nat)                          (* RecNB of the first rd Sq_i *)
  | RKB (hG hX hY : nat)                    (* post of rmb_b: Pkg or owns an rmb *)
  | RKT1 (hG hX hY hT : nat)                (* post of the final rd Sq_i *)
  | RKF (hG hX hY hT : nat)                 (* PkgT or owns an rmb *)
  | RKFR (hG hX hY hT v : nat)              (* the same, and the logged value of the final read *)
  | RKR (l : SLoc) (hu v : nat).            (* a logged read value *)

  (** Stability class: 0 under every own guarantee, 1 under every
      guarantee that keeps the possibility, 2 only under guarantees that
      also keep the ghost. *)
  Definition kcls (x : RK) : nat :=
    match x with
    | RKT | RKN _ | RKR _ _ _ => 0
    | RKH | RKG _ | RKA _ | RKX _ _ | RKY _ _ => 1
    | RKB _ _ _ | RKT1 _ _ _ _ | RKF _ _ _ _ | RKFR _ _ _ _ _ => 2
    end.

  Lemma rk_triv (x : RK) : x = RKT \/ x <> RKT.
  Proof. destruct x; [left; reflexivity | right; discriminate ..]. Qed.

  (** The in-edge into the slot at position [j] (position [q = j mod 12]
      in its iteration, which starts at [b]) from position [d].  The
      parameters are the handles of the iteration's first [rd Sq_i]
      ([hG]), [rd Sx_i] ([hX]), [rd Sy_i] ([hY]), the value [sv] of the
      first [rd Sq_i], and the slot's own handle [hO] and value [vO]. *)
  Definition rin_k (q j b hG hX hY sv hO vO d : nat) : RK :=
    match q with
    | 0 => if (0 <? j) && (d =? j - 2) then RKH else RKT
    | 2 => if d =? b then RKG hG else RKT
    | 4 | 6 => if d =? b + 2 then RKA hG else RKT
    | 8 => if d =? b then RKN hG else if d =? b + 4 then RKX hG hX else if d =? b + 6 then RKY hG hY else RKT
    | 10 => if d =? b + 8 then RKB hG hX hY else RKT
    | 11 => if (d =? b + 10) && rok sv vO then RKF hG hX hY hO else RKT
    | _ => RKT
    end.

  (** The postcondition of the slot at position [q] of an iteration. *)
  Definition rpost_k (i q hG hX hY sv hO vO : nat) : RK :=
    match q with
    | 0 => RKG hO
    | 1 => RKR (Sq i) hO vO
    | 2 => RKA hG
    | 4 => RKX hG hO
    | 5 => RKR (Sx i) hO vO
    | 6 => RKY hG hO
    | 7 => RKR (Sy i) hO vO
    | 8 => RKB hG hX hY
    | 10 => RKT1 hG hX hY hO
    | 11 => if rok sv vO then RKFR hG hX hY hO vO else RKR (Sq i) hO vO
    | _ => RKT
    end.

  (** The in-edges that carry a fact. *)
  Definition FE (q j b d : nat) : Prop :=
    (q = 0 /\ 0 < j /\ d = j - 2) \/ (q = 2 /\ d = b) \/ ((q = 4 \/ q = 6) /\ d = b + 2) \/
    (q = 8 /\ (d = b \/ d = b + 4 \/ d = b + 6)) \/ (q = 10 /\ d = b + 8) \/ (q = 11 /\ d = b + 10).

  Ltac eqb_cases H :=
    repeat match type of H with
           | context [?a =? ?b] => destruct (Nat.eqb_spec a b)
           | context [?a <? ?b] => destruct (Nat.ltb_spec a b)
           | context [rok ?a ?b] => destruct (rok a b) eqn:?
           end; cbn in H.

  Lemma rin_fe q j b hG hX hY sv hO vO d : rin_k q j b hG hX hY sv hO vO d <> RKT -> FE q j b d.
  Proof.
    unfold rin_k, FE. intros Hne.
    destruct q as [|[|[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]]]]; eqb_cases Hne;
      try (exfalso; apply Hne; reflexivity); lia.
  Qed.

  Lemma rin_fe1 q j b hG hX hY sv hO vO d :
    1 <= kcls (rin_k q j b hG hX hY sv hO vO d) -> FE q j b d /\ ~ (q = 8 /\ d = b).
  Proof.
    unfold rin_k, FE. intros Hne.
    destruct q as [|[|[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]]]]; eqb_cases Hne; cbn in Hne; try lia.
  Qed.

  Lemma rin_cls2 q j b hG hX hY sv hO vO d : kcls (rin_k q j b hG hX hY sv hO vO d) = 2 -> q = 10 \/ q = 11.
  Proof.
    unfold rin_k. intros Hne.
    destruct q as [|[|[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]]]]; eqb_cases Hne; cbn in Hne; lia.
  Qed.

  Lemma rin_q11 j b hG hX hY sv hO vO d : rin_k 11 j b hG hX hY sv hO vO d <> RKT -> rok sv vO = true.
  Proof. unfold rin_k. intros Hne. destruct (rok sv vO); [reflexivity |]. rewrite andb_false_r in Hne. contradiction. Qed.

  (** Order facts on the fact-carrying edges (except [G -> B], which
      carries only [RecNB]): no [rmb] lies strictly between source and
      target, and before the final read and its response no invocation
      does. *)
  Lemma fe_le n d g :
    FE (n mod 12) n (n - n mod 12) d -> ~ (n mod 12 = 8 /\ d = n - n mod 12) -> g < n ->
    (g mod 12 = 2 \/ g mod 12 = 8 \/ ((n mod 12 = 10 \/ n mod 12 = 11) /\ g mod 2 = 0)) ->
    g <= d /\ d mod 2 = 0 /\ ~ (g mod 12 = 4 /\ (d = g + 2 \/ d = g + 3)) /\ d < n.
  Proof. unfold FE. intros. dlia. Qed.

  Lemma fe_inv n d :
    FE (n mod 12) n (n - n mod 12) d -> n mod 12 <> 11 ->
    exists a j, n = 2 * j /\ d = 2 * a /\ a < j /\
      (a mod 6 = 1 \/ a mod 6 = 4 \/ j mod 6 = 1 \/ j mod 6 = 4 \/
       ((a mod 6 = 0 \/ a mod 6 = 5) /\ (j mod 6 = 0 \/ j mod 6 = 5))).
  Proof. unfold FE. intros H1 H2. exists (d / 2), (n / 2). dlia. Qed.

  Lemma fe_res n d : FE (n mod 12) n (n - n mod 12) d -> n mod 12 = 11 -> exists j, n = S (2 * j) /\ d = 2 * j.
  Proof. unfold FE. intros H1 H2. exists (n / 2). dlia. Qed.

  Lemma fe_d n d : FE (n mod 12) n (n - n mod 12) d -> d < n /\ d mod 2 = 0.
  Proof. unfold FE. intros. dlia. Qed.

  Lemma fe_kin_edge rc si i (k : CallKey (F2 si)) (Γx : list (Slot (EIhlv (E := E_S rc) δS) (RelaxedHoareSpec.EI (F := F2 si) δF)))
      Hx csx n d :
    RunCtx k Γx Hx csx -> RCallsR rc i csx -> n < length Γx -> FE (n mod 12) n (n - n mod 12) d -> dprec (evs Γx) d n.
  Proof.
    intros Hc Hr Hn Hfe. pose proof (runctx_len k Γx Hx csx Hc) as Hl.
    destruct (Nat.eq_dec (n mod 12) 11) as [E11 | N11].
    - destruct (fe_res n d Hfe E11) as (j & -> & ->). apply (dp_res rc si k Γx Hx csx j Hc). lia.
    - destruct (fe_inv n d Hfe N11) as (a & j & -> & -> & Haj & Ho). apply (dp_ord rc si i k Γx Hx csx a j Hc Hr Haj); [lia | exact Ho].
  Qed.

  (** *** The footprint of a finished run: [RdShape] *)

  Fixpoint chunk6 (l : list nat) : list (nat * nat * nat * nat * nat * nat) :=
    match l with
    | a :: b :: c :: d :: e :: f :: r => (a, b, c, d, e, f) :: chunk6 r
    | _ => []
    end.

  Lemma rcalls_shift6 rc i (c0 c1 c2 c3 c4 c5 : RCall (E_S rc)) rest :
    RCallsR rc i (c0 :: c1 :: c2 :: c3 :: c4 :: c5 :: rest) -> RCallsR rc i rest.
  Proof.
    intros Hr c x Hx. destruct (Hr (6 + c) x Hx) as [Ho Hd]. split; [| exact Hd].
    rewrite Ho. f_equal. dlia.
  Qed.

  Lemma chunk6_calls rc (t : tid) i n : forall cs : list (RCall (E_S rc)),
    length cs = 6 * n -> RCallsR rc i cs ->
    map (fun c => Build_ThreadEvent t (@InvEv (E_S rc) (rc_h c) (rc_op c))) cs =
      flat_map (rd_iter rc t i) (chunk6 (map rc_h cs)) /\
    flat_map hs_list (chunk6 (map rc_h cs)) = map rc_h cs.
  Proof.
    induction n as [| n IH]; intros cs Hl Hr.
    - destruct cs; [split; reflexivity | discriminate Hl].
    - destruct cs as [| c0 [| c1 [| c2 [| c3 [| c4 [| c5 rest]]]]]]; cbn in Hl; try lia.
      destruct (IH rest ltac:(lia) (rcalls_shift6 rc i c0 c1 c2 c3 c4 c5 rest Hr)) as [E1 E2].
      cbn [map chunk6 flat_map rd_iter hs_list app].
      rewrite (proj1 (Hr 0 c0 eq_refl)), (proj1 (Hr 1 c1 eq_refl)), (proj1 (Hr 2 c2 eq_refl)),
        (proj1 (Hr 3 c3 eq_refl)), (proj1 (Hr 4 c4 eq_refl)), (proj1 (Hr 5 c5 eq_refl)).
      rewrite E1, E2. split; reflexivity.
  Qed.

  Lemma rdshape_calls rc (t : tid) i (cs : list (RCall (E_S rc))) :
    RCallsR rc i cs -> length cs mod 6 = 0 -> 0 < length cs -> NoDup (map rc_h cs) ->
    RdShape rc t i (map (fun c => Build_ThreadEvent t (@InvEv (E_S rc) (rc_h c) (rc_op c))) cs).
  Proof.
    intros Hr Hm Hp Hnd.
    destruct (chunk6_calls rc t i (length cs / 6) cs ltac:(dlia) Hr) as [E1 E2].
    exists (chunk6 (map rc_h cs)). split; [| split; [rewrite E2; exact Hnd | exact E1]].
    destruct cs as [| c0 [| c1 [| c2 [| c3 [| c4 [| c5 rest]]]]]]; cbn in Hp, Hm |- *; try lia; discriminate.
  Qed.

  (** ** Part 4. The slots of a read call *)

  Section Read.
    Context (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid).
    Context (Hsi : forall o o', slRA o o' -> si o o').
    Context (t : tid) (i : nat).

    Local Abbreviation ES := (E_S rc).
    Local Abbreviation FS := (F2 si).
    Local Abbreviation V := (EIhlv (E := E_S rc) δS).
    Local Abbreviation VF := (RelaxedHoareSpec.EI (F := F2 si) δF).
    Local Abbreviation IV := (IslV rc si tw).
    Local Abbreviation RV := (RslV rc si).
    Local Abbreviation GV := (GslV rc si).

    Section Call.
      Context (h : nat).
      Local Abbreviation k := (@pair tid (handle FS) t h).
      Local Abbreviation Pinit := (PostInvoke IV k (fR i) (Osl rc tw t (fR i) h)).

      (** *** The assertions *)

      Definition KH : Assn V VF := KHas rc si k (fR i).

      Definition ka (x : RK) : Assn V VF :=
        match x with
        | RKT => fun _ => True
        | RKH => KH
        | RKG hG => fun s => (EdgeG rc si i (t, hG) s /\ liftA (KRecNB rc si k (IE rc t hG (sRd (Sq i)))) s) /\ KH s
        | RKA hG => fun s => EdgeG rc si i (t, hG) s /\ KH s
        | RKX hG hX => fun s => EdgeD rc si i (t, hG) (t, hX) (Sx i) fst s /\ KH s
        | RKY hG hY => fun s => EdgeD rc si i (t, hG) (t, hY) (Sy i) snd s /\ KH s
        | RKN hG => liftA (KRecNB rc si k (IE rc t hG (sRd (Sq i))))
        | RKB hG hX hY => fun s => (Pkg rc si k i (t, hG) (t, hX) (t, hY) s \/ liftA (KOwns rc si k isRmb) s) /\ KH s
        | RKT1 hG hX hY hT =>
            fun s => (PkgT rc si k i (t, hG) (t, hX) (t, hY) (t, hT) s \/ liftA (KOwns rc si k isRmb) s) /\ KH s
        | RKF hG hX hY hT => fun s => PkgT rc si k i (t, hG) (t, hX) (t, hY) (t, hT) s \/ liftA (KOwns rc si k isRmb) s
        | RKFR hG hX hY hT v =>
            fun s => (PkgT rc si k i (t, hG) (t, hX) (t, hY) (t, hT) s \/ liftA (KOwns rc si k isRmb) s) /\
                     KRd rc si (t, hT) (Sq i) v s
        | RKR l hu v => KRd rc si (t, hu) l v
        end.

      (** *** The guarantees: [GslV] at the two [rmb]s of an iteration
          (each may be the linearization point), a guarantee keeping the
          possibility ([GslFix]) at the reads, and one keeping also the
          ghost ([GslRes]) at the responses (gap G2). *)
      Definition GN : PRel V VF := liftGL (GslFix rc si k).
      Definition GR : PRel V VF := liftGL (GslRes rc si k).

      Definition rguar_q (q : nat) : PRel V VF :=
        match q with 2 | 8 => GV k | 1 | 3 | 5 | 7 | 9 | 11 => GR | _ => GN end.

      Lemma rguar_gv q s s' : rguar_q q s s' -> GV k s s'.
      Proof.
        do 12 (destruct q as [| q]; [cbn [rguar_q]; first [exact (fun H => H) | apply gslfixV_gslV | apply gslresV_gslV] |]).
        cbn [rguar_q]. apply gslfixV_gslV.
      Qed.

      Lemma rguar_pos n :
        (rguar_q (n mod 12) = GV k /\ (n mod 12 = 2 \/ n mod 12 = 8)) \/
        (rguar_q (n mod 12) = GR /\ n mod 2 = 1) \/
        (rguar_q (n mod 12) = GN /\ n mod 2 = 0 /\ n mod 12 <> 2 /\ n mod 12 <> 8).
      Proof.
        assert (Hm : n mod 12 < 12) by (apply Nat.mod_upper_bound; discriminate).
        assert (H2 : n mod 2 = (n mod 12) mod 2) by dlia. rewrite H2.
        destruct (n mod 12) as [|[|[|[|[|[|[|[|[|[|[|[|q]]]]]]]]]]]]; cbn [rguar_q];
          first [ left; split; [reflexivity | lia] | right; left; split; reflexivity
                | right; right; split; [reflexivity | split; [reflexivity | lia]] | lia ].
      Qed.

      (** *** Stability *)

      Lemma ka_stable_r x : Stable IV (RV k) (ka x).
      Proof.
        destruct x; cbn [ka]; unfold KH;
          repeat first [ apply Stable_and | apply Stable_or_v | apply Stable_true
                       | apply khas_stable_r | apply edgeG_stable_r | apply edgeD_stable_r | apply krecnbV_stable_r
                       | apply pkg_stable_r | apply pkgT_stable_r | apply kownsV_stable_r | apply krd_stable_r ].
      Qed.

      Lemma ka_stable_gr x : Stable IV GR (ka x).
      Proof.
        destruct x; cbn [ka]; unfold KH, GR;
          repeat first [ apply Stable_and | apply Stable_or_v | apply Stable_true
                       | apply pkgT_stable_res | apply kownsV_stable_res | apply krd_stable
                       | apply (stable_res_of_fix rc si tw k);
                         first [ apply khas_stable_fix | apply pkg_stable_fix
                               | apply stable_g_of_fix; first [ apply edgeG_stable_g | apply edgeD_stable_g | apply krecnbV_stable_g ] ] ].
      Qed.

      Lemma ka_stable_gn x : kcls x <= 1 -> Stable IV GN (ka x).
      Proof.
        destruct x; cbn [kcls]; intros Hx; try lia; cbn [ka]; unfold KH, GN;
          repeat first [ apply Stable_and | apply Stable_true | apply krd_stable | apply khas_stable_fix
                       | apply stable_g_of_fix; first [ apply edgeG_stable_g | apply edgeD_stable_g | apply krecnbV_stable_g ] ].
      Qed.

      Lemma ka_stable_gv x : kcls x = 0 -> Stable IV (GV k) (ka x).
      Proof.
        destruct x; cbn [kcls]; intros Hx; try lia; cbn [ka];
          first [ apply Stable_true | apply krecnbV_stable_g | apply krd_stable_g ].
      Qed.

      (** *** The canonical slots *)

      (** The start of the first call: the read is in the pool. *)
      Definition rstart (j : nat) : Assn V VF := if j =? 0 then KH else fun _ => True.

      (** The slot at position [j] (invocation of call [c] at [2 c], its
          response at [2 c + 1]; iteration [j / 12] starts at
          [j - j mod 12]), with event [ev], appended after the events
          [L]. *)
      Definition rslot (L : list (TaggedEvent ES)) (j : nat) (ev : TaggedEvent ES) : Slot V VF :=
        mkSlot ev (rstart j)
          (fun d => ka (rin_k (j mod 12) j (j - j mod 12) (ghat L j (j - j mod 12)) (ghat L j (j - j mod 12 + 4))
                          (ghat L j (j - j mod 12 + 6)) (gvat L j (j - j mod 12 + 1)) (evh ev) (evv ev) d))
          (ka (rpost_k i (j mod 12) (ghat L j (j - j mod 12)) (ghat L j (j - j mod 12 + 4))
                 (ghat L j (j - j mod 12 + 6)) (gvat L j (j - j mod 12 + 1)) (evh ev) (evv ev)))
          (rguar_q (j mod 12)).

      (** Every slot is the canonical one for its position. *)
      Definition SlotsOK (Γ : list (Slot V VF)) : Prop :=
        forall j sj, nth_error Γ j = Some sj -> sj = rslot (evs Γ) j (sl_ev sj).

      (** The iterations whose final response is below [N] did not
          validate (the machine looped): the in-edge of that response is
          [True] (gap G3). *)
      Definition NoLoop (Γ : list (Slot V VF)) (N : nat) : Prop :=
        forall y, y < N -> y mod 12 = 11 -> rok (vat (evs Γ) (y - 10)) (vat (evs Γ) y) = false.

      Lemma rslot_app L L' j ev : j <= length L -> rslot (L ++ L') j ev = rslot L j ev.
      Proof. intros Hj. unfold rslot. rewrite !ghat_app, !gvat_app by exact Hj. reflexivity. Qed.

      Lemma slotsok_nil : SlotsOK [].
      Proof. intros j sj Hj. destruct j; discriminate. Qed.

      Lemma slotsok_snoc Γ ev : SlotsOK Γ -> SlotsOK (Γ ++ [rslot (evs Γ) (length Γ) ev]).
      Proof.
        intros Hok j sj Hj. rewrite evs_app.
        destruct (nth_error_snoc_cases _ _ _ _ Hj) as [(Hlt & Hj') | (-> & ->)].
        - rewrite rslot_app by (rewrite length_evs; lia). exact (Hok j sj Hj').
        - rewrite rslot_app by (rewrite length_evs; lia). reflexivity.
      Qed.

      Lemma noloop_nil : NoLoop [] 0.
      Proof. intros y Hy. lia. Qed.

      Lemma noloop_snoc Γ sl N : NoLoop Γ N -> N <= length Γ -> NoLoop (Γ ++ [sl]) N.
      Proof.
        intros Hn HN y Hy Hq. rewrite evs_app, !vat_app by (rewrite length_evs; lia). exact (Hn y Hy Hq).
      Qed.

      Lemma noloop_ext Γ N N' : NoLoop Γ N -> (forall y, N <= y < N' -> y mod 12 <> 11) -> NoLoop Γ N'.
      Proof.
        intros Hn Hx y Hy Hq. destruct (Nat.lt_ge_cases y N) as [Hl | Hl]; [exact (Hn y Hl Hq) |].
        exfalso. exact (Hx y ltac:(lia) Hq).
      Qed.

      Lemma noloop_add Γ N N' :
        NoLoop Γ N -> (forall y, N <= y < N' -> y mod 12 = 11 -> rok (vat (evs Γ) (y - 10)) (vat (evs Γ) y) = false) ->
        NoLoop Γ N'.
      Proof.
        intros Hn Hx y Hy Hq. destruct (Nat.lt_ge_cases y N) as [Hl | Hl]; [exact (Hn y Hl Hq) |].
        exact (Hx y ltac:(lia) Hq).
      Qed.

      (** What the call knows at its start. *)
      Lemma pinit_kh : Impl IV Pinit KH.
      Proof.
        intros s _ Hp. destruct (postinvoke_lift (LogOK (E := ES) δS) (Isl rc si tw) k (fR i) _ s Hp) as [Hp' _].
        destruct (pinit_facts rc si tw t h (fR i) (dropS s) Hp') as [(A & Pf & P & Hpp & Hl) _].
        exists A, Pf, P. split; [exact Hpp |]. exists (@ls_inv FS (fR i)). split; [exact Hl | reflexivity].
      Qed.

      (** The postcondition of the source of a fact edge implies the
          in-edge (parameters read at the two positions agree). *)
      Lemma ka_eq x y : x = y -> Impl IV (ka x) (ka y).
      Proof. intros -> s _ H. exact H. Qed.

      Ltac eqb_simpl := repeat match goal with
        | |- context [?a =? ?b] => first [ rewrite (proj2 (Nat.eqb_eq a b)) by dlia | rewrite (proj2 (Nat.eqb_neq a b)) by dlia ]
        | |- context [?a <? ?b] => first [ rewrite (proj2 (Nat.ltb_lt a b)) by dlia | rewrite (proj2 (Nat.ltb_ge a b)) by dlia ]
        end; cbn [andb].

      Lemma est_in (L : list (TaggedEvent ES)) n d (evd ev : TaggedEvent ES) :
        FE (n mod 12) n (n - n mod 12) d -> hat L d = evh evd -> (n mod 12 = 11 -> evh evd = evh ev) ->
        Impl IV (ka (rpost_k i (d mod 12) (ghat L d (d - d mod 12)) (ghat L d (d - d mod 12 + 4))
                       (ghat L d (d - d mod 12 + 6)) (gvat L d (d - d mod 12 + 1)) (evh evd) (evv evd)))
                (ka (rin_k (n mod 12) n (n - n mod 12) (ghat L n (n - n mod 12)) (ghat L n (n - n mod 12 + 4))
                       (ghat L n (n - n mod 12 + 6)) (gvat L n (n - n mod 12 + 1)) (evh ev) (evv ev) d)).
      Proof.
        intros Hfe Hed H11. pose proof (fe_d n d Hfe) as [Hdn _].
        assert (Hb : exists b, b = n - n mod 12 /\ b mod 12 = 0 /\ b <= n) by (exists (n - n mod 12); dlia).
        destruct Hb as (b & Eb & Hb0 & Hbn). rewrite <- Eb in *. unfold FE in Hfe.
        destruct Hfe as [(Hq & Hn0 & ->) | [(Hq & ->) | [([Hq | Hq] & ->) | [(Hq & [-> | [-> | ->]]) | [(Hq & ->) | (Hq & ->)]]]]];
          rewrite Hq in *.
        - (* T_{m-1} -> G_m *)
          replace ((n - 2) mod 12) with 10 by dlia. cbn [rpost_k rin_k]. eqb_simpl.
          intros s _ [_ H]. exact H.
        - (* G -> A *)
          rewrite Hb0. cbn [rpost_k rin_k]. eqb_simpl.
          apply ka_eq. f_equal. rewrite ghat_lt by lia. symmetry. exact Hed.
        - (* A -> X *)
          replace ((b + 2) mod 12) with 2 by dlia. cbn [rpost_k rin_k]. eqb_simpl.
          apply ka_eq. f_equal. rewrite !ghat_lt by lia. f_equal. lia.
        - (* A -> Y *)
          replace ((b + 2) mod 12) with 2 by dlia. cbn [rpost_k rin_k]. eqb_simpl.
          apply ka_eq. f_equal. rewrite !ghat_lt by lia. f_equal. lia.
        - (* G -> B *)
          rewrite Hb0. cbn [rpost_k rin_k]. eqb_simpl.
          rewrite ghat_lt, Hed by lia. intros s _ [[_ H] _]. exact H.
        - (* X -> B *)
          replace ((b + 4) mod 12) with 4 by dlia. cbn [rpost_k rin_k]. eqb_simpl.
          apply ka_eq. rewrite !ghat_lt by lia. rewrite Hed. f_equal. f_equal. lia.
        - (* Y -> B *)
          replace ((b + 6) mod 12) with 6 by dlia. cbn [rpost_k rin_k]. eqb_simpl.
          apply ka_eq. rewrite !ghat_lt by lia. rewrite Hed. f_equal. f_equal. lia.
        - (* B -> T *)
          replace ((b + 8) mod 12) with 8 by dlia. cbn [rpost_k rin_k]. eqb_simpl.
          apply ka_eq. rewrite !ghat_lt by lia. f_equal; f_equal; lia.
        - (* T -> its response *)
          replace ((b + 10) mod 12) with 10 by dlia. cbn [rpost_k rin_k]. eqb_simpl.
          destruct (rok _ _); [| intros s _ _; exact Logic.I].
          rewrite !ghat_lt by lia. rewrite <- (H11 eq_refl).
          replace (b + 10 - 10) with b by lia. intros s _ [H _]. exact H.
      Qed.

      (** *** One lemma for every [NewSlotOK]

          A slot [rslot (evs Γ) (length Γ) ev] appended to a context of
          canonical slots satisfies [NewSlotOK], given its event update
          from its start and all its in-edges.  [Γx] is a run context of
          the reader extending [Γ ++ [sl]]: the order facts are read off it
          ([fe_kin_edge], [bef_pos]).  The interference premises hold by
          the stability classes of the assertions and by the order facts
          [fe_le] (no [rmb] between the ends of an edge that carries a
          possibility fact; no invocation between the ends of an edge that
          carries an ownership fact). *)
      Lemma rnew (Γ : list (Slot V VF)) (ev : TaggedEvent ES) (Γx : list (Slot V VF)) (Hx : FutureStore ES)
          (csx : list (RCall ES)) (rest : list (Slot V VF)) :
        RunCtx k Γx Hx csx -> RCallsR rc i csx -> Γx = (Γ ++ [rslot (evs Γ) (length Γ) ev]) ++ rest ->
        SlotsOK Γ -> NoLoop Γ (length Γ) ->
        EvUpdate IV (sl_guar (rslot (evs Γ) (length Γ) ev)) k (untag ev)
          (fun s => sl_start (rslot (evs Γ) (length Γ) ev) s /\ forall d, sl_in (rslot (evs Γ) (length Γ) ev) d s)
          (sl_post (rslot (evs Γ) (length Γ) ev)) ->
        NewSlotOK IV RV GV k Pinit Γ (rslot (evs Γ) (length Γ) ev).
      Proof.
        intros Hc Hr HΓx Hok Hnl Hupd.
        pose proof (runctx_len k Γx Hx csx Hc) as Hlen.
        assert (Hlx : length Γ < length Γx) by (rewrite HΓx, !length_app; cbn; lia).
        assert (Hbx : forall a b, b <= length Γ -> before (evs Γx) a b ->
                        before (evs (Γ ++ [rslot (evs Γ) (length Γ) ev])) a b).
        { intros a b Hb Hbf. rewrite HΓx, evs_app in Hbf.
          apply (before_app_iff (evs (Γ ++ [rslot (evs Γ) (length Γ) ev])) (evs rest) a b) in Hbf; [exact Hbf | rewrite length_evs, length_app; cbn; lia]. }
        assert (Hbo : forall a b, b < length Γ -> before (evs Γx) a b -> before (evs Γ) a b).
        { intros a b Hb Hbf. apply Hbx in Hbf; [| lia]. rewrite evs_app in Hbf.
          apply (before_app_iff (evs Γ) (evs [rslot (evs Γ) (length Γ) ev]) a b) in Hbf; [exact Hbf | rewrite length_evs; exact Hb]. }
        assert (Hdx : forall a b, b <= length Γ -> dprec (evs Γx) a b ->
                        dprec (evs (Γ ++ [rslot (evs Γ) (length Γ) ev])) a b).
        { intros a b Hb Hd. rewrite HΓx, evs_app in Hd.
          apply (dprec_app_iff (evs (Γ ++ [rslot (evs Γ) (length Γ) ev])) (evs rest) a b) in Hd; [exact Hd | rewrite length_evs, length_app; cbn; lia]. }
        assert (Hevx : evs Γx = evs Γ ++ ev :: evs rest) by (rewrite HΓx, !evs_app, <- app_assoc; reflexivity).
        assert (Hhat : forall p, p < length Γ -> hat (evs Γx) p = hat (evs Γ) p).
        { intros p Hp. rewrite Hevx. apply hat_app. rewrite length_evs. exact Hp. }
        assert (Hhn : hat (evs Γx) (length Γ) = evh ev).
        { rewrite Hevx. unfold hat. rewrite nth_error_app2 by (rewrite length_evs; lia).
          rewrite length_evs, Nat.sub_diag. reflexivity. }
        assert (Hjn : forall j sj, nth_error Γ j = Some sj -> j < length Γ)
          by (intros j sj Hj; apply nth_error_Some; rewrite Hj; discriminate).
        (* the in-edge kind of the new slot *)
        set (xin := fun d => rin_k (length Γ mod 12) (length Γ) (length Γ - length Γ mod 12)
                               (ghat (evs Γ) (length Γ) (length Γ - length Γ mod 12))
                               (ghat (evs Γ) (length Γ) (length Γ - length Γ mod 12 + 4))
                               (ghat (evs Γ) (length Γ) (length Γ - length Γ mod 12 + 6))
                               (gvat (evs Γ) (length Γ) (length Γ - length Γ mod 12 + 1)) (evh ev) (evv ev) d).
        assert (Hin : forall d, sl_in (rslot (evs Γ) (length Γ) ev) d = ka (xin d)) by reflexivity.
        constructor.
        - (* ns_guar *) intros s s' Hg. exact (rguar_gv _ s s' Hg).
        - (* ns_update *)
          intros σ p γ γ' [Hst Hpre] HI Hge σ' Hs. apply (Hupd σ p γ γ'); [| exact HI | exact Hge | exact Hs].
          split; [exact Hst |]. intros d. rewrite Hin.
          destruct (rk_triv (xin d)) as [E | Hne]; [rewrite E; exact Logic.I |].
          rewrite <- Hin. apply Hpre. apply Hdx; [lia |]. apply (fe_kin_edge rc si i k Γx Hx csx); [exact Hc | exact Hr | exact Hlx |].
          exact (rin_fe _ _ _ _ _ _ _ _ _ _ Hne).
        - (* ns_est_start *)
          cbn [rslot sl_start]. unfold rstart. destruct (length Γ =? 0); [exact pinit_kh | intros s _ _; exact Logic.I].
        - (* ns_est_in *)
          intros d sd Hd Hsd. rewrite Hin. rewrite (Hok d sd Hsd). cbn [rslot sl_post].
          destruct (rk_triv (xin d)) as [E | Hne]; [rewrite E; intros s _ _; exact Logic.I |].
          pose proof (rin_fe _ _ _ _ _ _ _ _ _ _ Hne) as Hfe.
          pose proof (Hjn d sd Hsd) as Hdn.
          assert (Hed : hat (evs Γ) d = evh (sl_ev sd)) by exact (hat_evs Γ d sd Hsd).
          apply est_in; [exact Hfe | exact Hed |].
          intros E11. destruct (fe_res _ _ Hfe E11) as (j & Hnj & ->).
          rewrite <- Hed, <- (Hhat (2 * j)) by lia. rewrite (hat_pair rc si k Γx Hx csx j Hc) by lia.
          rewrite <- Hnj. exact Hhn.
        - (* ns_R_start *)
          cbn [rslot sl_start]. unfold rstart. destruct (length Γ =? 0); [apply khas_stable_r | apply Stable_true].
        - (* ns_R_in *) intros d _. rewrite Hin. apply ka_stable_r.
        - (* ns_if_new_start *)
          intros g sg Hg. cbn [rslot sl_start]. unfold rstart.
          destruct (Nat.eqb_spec (length Γ) 0) as [E | _]; [| apply Stable_true].
          apply length_zero_iff_nil in E. subst Γ. destruct g; discriminate Hg.
        - (* ns_if_new_in *)
          intros d g sg Hd Hg Hnb. rewrite Hin. rewrite (Hok g sg Hg). cbn [rslot sl_guar].
          pose proof (Hjn g sg Hg) as Hgn.
          destruct (rk_triv (xin d)) as [E | Hne]; [rewrite E; apply Stable_true |].
          pose proof (rin_fe _ _ _ _ _ _ _ _ _ _ Hne) as Hfe.
          assert (Hbef : (g mod 12 = 2 \/ g mod 12 = 8 \/
                          ((length Γ mod 12 = 10 \/ length Γ mod 12 = 11) /\ g mod 2 = 0)) ->
                         ~ (length Γ mod 12 = 8 /\ d = length Γ - length Γ mod 12) -> False).
          { intros Hcase Hx8. destruct (fe_le (length Γ) d g Hfe Hx8 Hgn Hcase) as (Hgd & Hde & Hx4 & Hdn).
            apply Hnb. apply Hbo; [exact Hdn |].
            apply (bef_pos rc si i k Γx Hx csx g d Hc Hr); [| exact Hgd | lia | exact Hx4].
            destruct Hcase as [E | [E | [_ E]]]; [dlia | dlia | exact E]. }
          destruct (rguar_pos g) as [(-> & Hg28) | [(-> & _) | (-> & Hg2 & _)]].
          + destruct (Nat.eq_dec (kcls (xin d)) 0) as [E0 | N0]; [exact (ka_stable_gv _ E0) |].
            exfalso. apply Hbef; [destruct Hg28; auto |].
            assert (H1 : 1 <= kcls (xin d)) by lia. exact (proj2 (rin_fe1 _ _ _ _ _ _ _ _ _ _ H1)).
          + apply ka_stable_gr.
          + destruct (Nat.le_gt_cases (kcls (xin d)) 1) as [L1 | G1]; [exact (ka_stable_gn _ L1) |].
            assert (E2 : kcls (xin d) = 2) by (destruct (xin d); cbn in G1 |- *; lia).
            exfalso. apply Hbef; [right; right; split; [exact (rin_cls2 _ _ _ _ _ _ _ _ _ _ E2) | exact Hg2] |].
            assert (H1 : 1 <= kcls (xin d)) by lia. exact (proj2 (rin_fe1 _ _ _ _ _ _ _ _ _ _ H1)).
        - (* ns_if_old_start *)
          intros y sy Hy Hnb. rewrite (Hok y sy Hy). cbn [rslot sl_start sl_guar]. unfold rstart.
          destruct (Nat.eqb_spec y 0) as [-> | _]; [| apply Stable_true].
          exfalso. apply Hnb. apply Hbx; [lia |].
          apply (bef_pos rc si i k Γx Hx csx 0 (length Γ) Hc Hr); [reflexivity | lia | lia | cbn; lia].
        - (* ns_if_old_in *)
          intros y sy d Hy Hnb Hd. rewrite (Hok y sy Hy). cbn [rslot sl_in sl_guar].
          pose proof (Hjn y sy Hy) as Hyn.
          set (xy := rin_k (y mod 12) y (y - y mod 12) (ghat (evs Γ) y (y - y mod 12)) (ghat (evs Γ) y (y - y mod 12 + 4))
                       (ghat (evs Γ) y (y - y mod 12 + 6)) (gvat (evs Γ) y (y - y mod 12 + 1)) (evh (sl_ev sy)) (evv (sl_ev sy)) d).
          destruct (rk_triv xy) as [E | Hne]; [rewrite E; apply Stable_true |].
          pose proof (rin_fe _ _ _ _ _ _ _ _ _ _ Hne) as Hfe. pose proof (fe_d y d Hfe) as [_ Hde].
          destruct (Nat.eq_dec (y mod 12) 11) as [E11 | N11].
          { exfalso. unfold xy in Hne. rewrite E11 in Hne. pose proof (rin_q11 _ _ _ _ _ _ _ _ _ Hne) as Hok11.
            rewrite <- E11, gvat_lt in Hok11 by dlia. rewrite <- (vat_evs Γ y sy Hy) in Hok11.
            replace (y - y mod 12 + 1) with (y - 10) in Hok11 by dlia.
            rewrite (Hnl y Hyn E11) in Hok11. discriminate Hok11. }
          assert (Hye : y mod 2 = 0) by (unfold FE in Hfe; dlia).
          assert (Hyb : forall n', y < n' -> n' <= length Γ -> ~ (y mod 12 = 4 /\ (n' = y + 2 \/ n' = y + 3)) ->
                          before (evs (Γ ++ [rslot (evs Γ) (length Γ) ev])) y n').
          { intros n' Hn1 Hn2 Hx4. apply Hbx; [exact Hn2 |].
            apply (bef_pos rc si i k Γx Hx csx y n' Hc Hr Hye); [lia | lia | exact Hx4]. }
          destruct (rguar_pos (length Γ)) as [(-> & Hn28) | [(-> & _) | (-> & Hn2 & Hn28)]].
          + exfalso. apply Hnb. apply Hyb; [lia | lia | dlia].
          + apply ka_stable_gr.
          + destruct (Nat.le_gt_cases (kcls xy) 1) as [L1 | G1]; [exact (ka_stable_gn _ L1) |].
            assert (E2 : kcls xy = 2) by (destruct xy; cbn in G1 |- *; lia).
            destruct (rin_cls2 _ _ _ _ _ _ _ _ _ _ E2) as [E10 | E11]; [| contradiction].
            exfalso. apply Hnb. apply Hyb; [lia | lia | dlia].
      Qed.


      (** ** Part 5. The event updates, one per slot position *)

      (** The [ns_update] premise of [rnew] for the slot at position [n]
          with event [ev] after the events [L]. *)
      Definition SUpd (L : list (TaggedEvent ES)) (n : nat) (ev : TaggedEvent ES) : Prop :=
        EvUpdate IV (sl_guar (rslot L n ev)) k (untag ev)
          (fun s => sl_start (rslot L n ev) s /\ forall d, sl_in (rslot L n ev) d s) (sl_post (rslot L n ev)).

      (** The first [rd Sq_i] of an iteration ([rd_G_update]); [KHas]
          comes from the start (first iteration) or from the previous
          iteration's final [rd Sq_i]. *)
      Lemma upd_G L n ev hu : n mod 12 = 0 -> untag ev = IE rc t hu (sRd (Sq i)) -> SUpd L n ev.
      Proof.
        intros Hq Hu. assert (Hh : evh ev = hu) by (unfold evh; rewrite Hu; reflexivity).
        unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hq, Hu, Hh. cbn [rguar_q rpost_k rin_k].
        eapply evupdate_conseq; [exact (rd_G_update rc si tw t h i hu) | | intros s Hs; exact Hs].
        intros s [Hst Hin]. split; [exact Logic.I |].
        unfold rstart in Hst. destruct (Nat.eqb_spec n 0) as [-> | Hn0]; [exact Hst |].
        specialize (Hin (n - 2)). rewrite (proj2 (Nat.ltb_lt 0 n)) in Hin by lia. rewrite Nat.eqb_refl in Hin. exact Hin.
      Qed.

      (** A response of a read ([rd_res_logged_update]): the post logs the
          value.  The final read's response when the validation fails is
          one of them. *)
      Lemma upd_res_rd L n ev hu l (v : nat) :
        untag ev = Build_ThreadEvent t (@ResEv ES hu (sRd l) v) ->
        (n mod 12 = 1 /\ l = Sq i) \/ (n mod 12 = 5 /\ l = Sx i) \/ (n mod 12 = 7 /\ l = Sy i) \/
        (n mod 12 = 11 /\ l = Sq i /\ rok (gvat L n (n - n mod 12 + 1)) v = false) ->
        SUpd L n ev.
      Proof.
        intros Hu Hq.
        assert (Hh : evh ev = hu) by (unfold evh; rewrite Hu; reflexivity).
        assert (Hv : evv ev = v) by (unfold evv; rewrite Hu; reflexivity).
        assert (Hupd : EvUpdate IV GR k (Build_ThreadEvent t (@ResEv ES hu (sRd l) v)) (fun _ => True) (ka (RKR l hu v))).
        { eapply evupdate_conseq;
            [exact (rd_res_logged_update rc si tw k t hu l v (fun _ => True) (fun _ _ _ _ _ _ => Logic.I)) | |].
          - intros s _. exact Logic.I.
          - intros s [_ Hs]. exact Hs. }
        unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hu, Hh, Hv.
        destruct Hq as [(Hq & ->) | [(Hq & ->) | [(Hq & ->) | (Hq & -> & Hr)]]]; rewrite Hq in *; cbn [rguar_q rpost_k];
          [ | | | rewrite Hr ]; (eapply evupdate_conseq; [exact Hupd | intros; exact Logic.I | intros s Hs; exact Hs]).
      Qed.

      (** A response of an [rmb]. *)
      Lemma upd_res_rmb L n ev hu (r : unit) :
        untag ev = Build_ThreadEvent t (@ResEv ES hu sRmb r) -> (n mod 12 = 3 \/ n mod 12 = 9) -> SUpd L n ev.
      Proof.
        intros Hu Hq.
        assert (Hupd : EvUpdate IV GR k (Build_ThreadEvent t (@ResEv ES hu sRmb r)) (fun _ => True) (fun _ => True))
          by exact (rd_res_update rc si tw k t hu sRmb r _ _ (fun _ _ _ _ _ _ _ => Logic.I)).
        unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hu.
        destruct Hq as [Hq | Hq]; rewrite Hq; cbn [rguar_q rpost_k ka];
          (eapply evupdate_conseq; [exact Hupd | intros; exact Logic.I | intros s Hs; exact Hs]).
      Qed.

      (** [rmb_a] ([rd_rmbA_update]: the linearization point if the ghost
          has no later [rmb] of the read, which only happens on paths the
          ghost does not follow). *)
      Lemma upd_A L n ev hu : n mod 12 = 2 -> untag ev = IE rc t hu sRmb -> SUpd L n ev.
      Proof.
        intros Hq Hu. unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hq, Hu. cbn [rguar_q rpost_k rin_k].
        eapply evupdate_conseq; [exact (rd_rmbA_update rc si tw Hsi t h i (ghat L n (n - 2)) (ghat L n (n - 2)) hu) | |].
        - intros s [_ Hin]. specialize (Hin (n - 2)). rewrite Nat.eqb_refl in Hin. cbn [ka] in Hin.
          destruct Hin as [[HG Hn] Hk]. split; [exact Logic.I | split; [exact HG | split; [exact Hn | exact Hk]]].
        - intros s (_ & HG & Hk). split; [exact HG | exact Hk].
      Qed.

      (** The data reads ([rd_X_update], [rd_Y_update]). *)
      Lemma upd_X L n ev hu : n mod 12 = 4 -> untag ev = IE rc t hu (sRd (Sx i)) -> SUpd L n ev.
      Proof.
        intros Hq Hu. assert (Hh : evh ev = hu) by (unfold evh; rewrite Hu; reflexivity).
        unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hq, Hu, Hh. cbn [rguar_q rpost_k rin_k].
        eapply evupdate_conseq; [exact (rd_X_update rc si tw t h i (ghat L n (n - 4)) hu) | |].
        - intros s [_ Hin]. specialize (Hin (n - 4 + 2)). rewrite Nat.eqb_refl in Hin. exact Hin.
        - intros s Hs. exact Hs.
      Qed.

      Lemma upd_Y L n ev hu : n mod 12 = 6 -> untag ev = IE rc t hu (sRd (Sy i)) -> SUpd L n ev.
      Proof.
        intros Hq Hu. assert (Hh : evh ev = hu) by (unfold evh; rewrite Hu; reflexivity).
        unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hq, Hu, Hh. cbn [rguar_q rpost_k rin_k].
        eapply evupdate_conseq; [exact (rd_Y_update rc si tw t h i (ghat L n (n - 6)) hu) | |].
        - intros s [_ Hin]. specialize (Hin (n - 6 + 2)). rewrite Nat.eqb_refl in Hin. exact Hin.
        - intros s Hs. exact Hs.
      Qed.

      (** [rmb_b] ([rd_rmbB_update]): the linearization point when the read
          owns no [rmb] afterwards ([Pkg]); otherwise it still owns one
          (gap G1). *)
      Lemma upd_B L n ev hu : n mod 12 = 8 -> untag ev = IE rc t hu sRmb -> SUpd L n ev.
      Proof.
        intros Hq Hu. unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hq, Hu. cbn [rguar_q rpost_k rin_k].
        eapply evupdate_conseq;
          [exact (rd_rmbB_update rc si tw Hsi t h i (ghat L n (n - 8)) (ghat L n (n - 8)) hu
                    (t, ghat L n (n - 8 + 4)) (t, ghat L n (n - 8 + 6))) | |].
        - intros s [_ Hin].
          pose proof (Hin (n - 8)) as H0. rewrite Nat.eqb_refl in H0.
          pose proof (Hin (n - 8 + 4)) as H4.
          rewrite (proj2 (Nat.eqb_neq (n - 8 + 4) (n - 8))), Nat.eqb_refl in H4 by lia.
          pose proof (Hin (n - 8 + 6)) as H6.
          rewrite (proj2 (Nat.eqb_neq (n - 8 + 6) (n - 8))), (proj2 (Nat.eqb_neq (n - 8 + 6) (n - 8 + 4))), Nat.eqb_refl in H6 by lia.
          cbn [ka] in H0, H4, H6. destruct H4 as [Hx Hk]. destruct H6 as [Hy _].
          split; [split; [exact Hx | exact Hy] |]. split; [exact Logic.I |]. split; [exact H0 | exact Hk].
        - intros s (Hp & _ & Hk). split; [exact Hp | exact Hk].
      Qed.

      (** The final [rd Sq_i] ([rd_T_update]). *)
      Lemma upd_T L n ev hu : n mod 12 = 10 -> untag ev = IE rc t hu (sRd (Sq i)) -> SUpd L n ev.
      Proof.
        intros Hq Hu. assert (Hh : evh ev = hu) by (unfold evh; rewrite Hu; reflexivity).
        unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hq, Hu, Hh. cbn [rguar_q rpost_k rin_k].
        eapply evupdate_conseq;
          [exact (rd_T_update rc si tw t h i hu (t, ghat L n (n - 10)) (t, ghat L n (n - 10 + 4)) (t, ghat L n (n - 10 + 6))) | |].
        - intros s [_ Hin]. specialize (Hin (n - 10 + 8)). rewrite Nat.eqb_refl in Hin. exact Hin.
        - intros s Hs. exact Hs.
      Qed.

      (** The response of the final [rd Sq_i] when the validation succeeds
          ([rd_resT_update]; gap G3: only then does its in-edge carry the
          package). *)
      Lemma upd_rT L n ev hu (v : nat) :
        n mod 12 = 11 -> untag ev = Build_ThreadEvent t (@ResEv ES hu (sRd (Sq i)) v) ->
        rok (gvat L n (n - n mod 12 + 1)) v = true -> SUpd L n ev.
      Proof.
        intros Hq Hu Hr. assert (Hh : evh ev = hu) by (unfold evh; rewrite Hu; reflexivity).
        assert (Hv : evv ev = v) by (unfold evv; rewrite Hu; reflexivity).
        unfold SUpd. cbn [rslot sl_guar sl_start sl_in sl_post]. rewrite Hq in *. rewrite Hu, Hh, Hv.
        cbn [rguar_q rpost_k rin_k]. rewrite Hr.
        eapply evupdate_conseq;
          [exact (rd_resT_update rc si tw k i (t, ghat L n (n - 11)) (t, ghat L n (n - 11 + 4)) (t, ghat L n (n - 11 + 6)) t hu v) | |].
        - intros s [_ Hin]. specialize (Hin (n - 11 + 10)). rewrite Nat.eqb_refl in Hin. cbn [andb] in Hin. exact Hin.
        - intros s Hs. exact Hs.
      Qed.

      (** ** Part 6. One call of the machine *)

      Definition rsi (Γ : list (Slot V VF)) (H : FutureStore ES) (cs : list (RCall ES)) (op : SOp) (hu : nat) : Slot V VF :=
        rslot (evs Γ) (length Γ) (invD_tev (E := ES) k H (dep_of (map rc_h cs) []) hu op).

      Definition rsr (Γ : list (Slot V VF)) (H : FutureStore ES) (cs : list (RCall ES)) (op : SOp) (hu : nat) (v : sar op) :
          Slot V VF :=
        rslot (evs (Γ ++ [rsi Γ H cs op hu])) (length (Γ ++ [rsi Γ H cs op hu])) (res_tev (E := ES) k hu op v).

      Definition rsar_inh (o : SOp) : sar o := match o with sRd _ => 0 | _ => tt end.

      (** [RunCallOK] for a call of the reader, from the two updates and
          the machine invariant after the call.  The invocation slot's
          [NewSlotOK] is checked in a run context completed by a dummy
          response ([rsar_inh]), as in [RelaxedHoareSL2Write.wnew]. *)
      Lemma rcall (Inv : RSt -> list (RCall ES) -> list (Slot V VF) -> FutureStore ES -> Prop) cs Γ H op
          (kc : sar op -> RSt) :
        RunCtx k Γ H cs -> RCallsR rc i cs -> SlotsOK Γ -> NoLoop Γ (length Γ) -> op = rop i (length cs mod 6) ->
        (forall hu, SUpd (evs Γ) (length Γ) (invD_tev (E := ES) k H (dep_of (map rc_h cs) []) hu op)) ->
        (forall hu (v : sar op), SUpd (evs (Γ ++ [rsi Γ H cs op hu])) (length (Γ ++ [rsi Γ H cs op hu]))
                                   (res_tev (E := ES) k hu op v)) ->
        (forall hu (v : sar op) H', handle_fresh hu H -> resolve_store hu op v (add_pending hu op H) H' ->
           RunCtx k ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v]) H' (cs ++ [@mkRCall ES hu op []]) ->
           Inv (kc v) (cs ++ [@mkRCall ES hu op []]) ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v]) H') ->
        RunCallOK IV RV GV k Pinit Inv cs Γ H op [] kc (rsi Γ H cs op) (rsr Γ H cs op).
      Proof.
        intros Hc Hr Hok Hnl Hop Hui Hur Hinv.
        pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        assert (Hctx : forall hu (v : sar op), handle_fresh hu H ->
                  RunCtx k ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v]) (Build_FutureEntry hu (@Resolved ES op v) :: H)
                    (cs ++ [@mkRCall ES hu op []])).
        { intros hu v Hf. apply (runctx_snoc k Γ H cs _ _ hu op [] v _ Hc Hf); [reflexivity | reflexivity | apply resolve_here]. }
        assert (Hr' : forall hu, RCallsR rc i (cs ++ [@mkRCall ES hu op []])) by (intros hu; rewrite Hop; apply rcalls_snoc; exact Hr).
        assert (Hok' : forall hu, SlotsOK (Γ ++ [rsi Γ H cs op hu])) by (intros hu; apply slotsok_snoc; exact Hok).
        assert (Hnl' : forall hu, NoLoop (Γ ++ [rsi Γ H cs op hu]) (length (Γ ++ [rsi Γ H cs op hu]))).
        { intros hu. apply (noloop_ext _ (length Γ)); [apply noloop_snoc; [exact Hnl | lia] |].
          intros y Hy. rewrite length_app in Hy. cbn [length] in Hy. rewrite HlΓ in Hy. dlia. }
        split; [| split; [| split; [| split]]].
        - intros hu. reflexivity.
        - intros hu Hf. exact (rnew Γ _ _ _ _ [rsr Γ H cs op hu (rsar_inh op)] (Hctx hu _ Hf) (Hr' hu) eq_refl Hok Hnl (Hui hu)).
        - intros hu v. reflexivity.
        - intros hu v Hf.
          exact (rnew (Γ ++ [rsi Γ H cs op hu]) _ _ _ _ [] (Hctx hu v Hf) (Hr' hu) (eq_sym (app_nil_r _)) (Hok' hu) (Hnl' hu)
                   (Hur hu v)).
        - intros hu v H' Hf Hres Hc'. exact (Hinv hu v H' Hf Hres Hc').
      Qed.


      (** ** Part 7. The machine invariant, the steps, the return *)

      (** After the calls [cs]: they are a prefix of the reader's calls
          ([RCallsR]), every slot is canonical ([SlotsOK]), the completed
          iterations did not validate ([NoLoop]), and the machine state
          records the position in the iteration ([length cs mod 6]) and
          the values read so far in it, which are the values of the
          response slots at the corresponding positions (gap G6).  Any
          number of iterations. *)
      Definition rinv (st : RSt) (cs : list (RCall ES)) (Γ : list (Slot V VF)) (H : FutureStore ES) : Prop :=
        RCallsR rc i cs /\ SlotsOK Γ /\
        match st with
        | RG => NoLoop Γ (length Γ) /\ length cs mod 6 = 0
        | RA s => NoLoop Γ (length Γ) /\ length cs mod 6 = 1 /\ vat (evs Γ) (2 * length cs - 1) = s
        | RX s => NoLoop Γ (length Γ) /\ length cs mod 6 = 2 /\ vat (evs Γ) (2 * length cs - 3) = s
        | RY s a => NoLoop Γ (length Γ) /\ length cs mod 6 = 3 /\ vat (evs Γ) (2 * length cs - 5) = s /\
                    vat (evs Γ) (2 * length cs - 1) = a
        | RB s a c => NoLoop Γ (length Γ) /\ length cs mod 6 = 4 /\ vat (evs Γ) (2 * length cs - 7) = s /\
                      vat (evs Γ) (2 * length cs - 3) = a /\ vat (evs Γ) (2 * length cs - 1) = c
        | RT s a c => NoLoop Γ (length Γ) /\ length cs mod 6 = 5 /\ vat (evs Γ) (2 * length cs - 9) = s /\
                      vat (evs Γ) (2 * length cs - 5) = a /\ vat (evs Γ) (2 * length cs - 3) = c
        | RD a c => NoLoop Γ (length Γ - 1) /\ length cs mod 6 = 0 /\ 0 < length cs /\
                    rok (vat (evs Γ) (2 * length cs - 11)) (vat (evs Γ) (2 * length cs - 1)) = true /\
                    vat (evs Γ) (2 * length cs - 7) = a /\ vat (evs Γ) (2 * length cs - 5) = c
        end.

      Lemma rinv_init : rinv RG [] [] empty_store.
      Proof. split; [apply rcalls_nil |]. split; [apply slotsok_nil |]. split; [apply noloop_nil | reflexivity]. Qed.

      (** The context after one call. *)
      Lemma call_facts cs Γ H op hu (v : sar op) :
        RunCtx k Γ H cs -> RCallsR rc i cs -> SlotsOK Γ -> op = rop i (length cs mod 6) ->
        RCallsR rc i (cs ++ [@mkRCall ES hu op []]) /\
        SlotsOK ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v]) /\
        length ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v]) = S (S (length Γ)) /\
        length (cs ++ [@mkRCall ES hu op []]) = S (length cs) /\
        (forall p, p < length Γ -> vat (evs ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v])) p = vat (evs Γ) p) /\
        vat (evs ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v])) (S (length Γ)) = sval op v /\
        (forall N, NoLoop Γ N -> N <= length Γ -> NoLoop ((Γ ++ [rsi Γ H cs op hu]) ++ [rsr Γ H cs op hu v]) N).
      Proof.
        intros Hc Hr Hok Hop.
        split; [rewrite Hop; apply rcalls_snoc; exact Hr |].
        split; [apply slotsok_snoc; apply slotsok_snoc; exact Hok |].
        split; [rewrite !length_app; cbn; lia |].
        split; [rewrite length_app; cbn; lia |].
        split; [intros p Hp; rewrite !evs_app, !vat_app by (rewrite ?length_app, !length_evs; cbn; lia); reflexivity |].
        split.
        - rewrite evs_app. unfold vat. rewrite nth_error_app2 by (rewrite length_evs, length_app; cbn; lia).
          rewrite length_evs, length_app. cbn [length]. replace (S (length Γ) - (length Γ + 1)) with 0 by lia. reflexivity.
        - intros N Hn HN. apply noloop_snoc; [apply noloop_snoc; [exact Hn | exact HN] | rewrite length_app; cbn; lia].
      Qed.

      (** The value of the iteration's first read, as the final read's
          response slot sees it. *)
      Lemma gvat_first cs Γ H op hu p :
        p < length Γ -> gvat (evs (Γ ++ [rsi Γ H cs op hu])) (length (Γ ++ [rsi Γ H cs op hu])) p = vat (evs Γ) p.
      Proof.
        intros Hp. rewrite gvat_lt by (rewrite length_app; cbn; lia). rewrite evs_app, vat_app by (rewrite length_evs; exact Hp).
        reflexivity.
      Qed.

      (** The fins at the return: the four response slots of the
          validating iteration, which starts at [b]. *)
      Definition rfin (L : list (TaggedEvent ES)) (b d : nat) : Assn V VF :=
        if d =? b + 1 then ka (RKR (Sq i) (hat L (b + 1)) (vat L (b + 1)))
        else if d =? b + 5 then ka (RKR (Sx i) (hat L (b + 5)) (vat L (b + 5)))
        else if d =? b + 7 then ka (RKR (Sy i) (hat L (b + 7)) (vat L (b + 7)))
        else if d =? b + 11 then ka (RKFR (hat L b) (hat L (b + 4)) (hat L (b + 6)) (hat L (b + 11)) (vat L (b + 11)))
        else fun _ => True.

      (** The return: [Close] with the B-6 postcondition [QrdV]
          ([sl_read_close_rd]: the logged values of the four reads and the
          package of the linearization point, or the read still owns an
          [rmb]), and the footprint. *)
      Lemma rclose cs Γ H a c :
        RunCtx k Γ H cs -> rinv (RD a c) cs Γ H ->
        Close IV RV GV k Pinit (fun r s => QrdV rc si k i r s /\ True) (a, c) Γ H /\ Osl rc tw t (fR i) h (own_invs Γ).
      Proof.
        intros Hc (Hr & Hok & _ & Hm & Hpos & Hrok & Ha & Hcv).
        pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        destruct (runctx_store k Γ H cs Hc) as (_ & Hall & Hnd).
        assert (Hjn : forall j sj, nth_error Γ j = Some sj -> j < length Γ)
          by (intros j sj Hj; apply nth_error_Some; rewrite Hj; discriminate).
        remember (2 * length cs - 12) as b eqn:Eb.
        split.
        - apply (close_done IV RV GV k Pinit (fun r s => QrdV rc si k i r s /\ True) (a, c) Γ H (rfin (evs Γ) b) (fun _ => True) Hall).
          constructor.
          + (* bw_est *)
            intros d sd Hd s _ Hp. rewrite (Hok d sd Hd) in Hp. cbn [rslot sl_post] in Hp.
            pose proof (hat_evs Γ d sd Hd) as Ehd. pose proof (vat_evs Γ d sd Hd) as Evd. pose proof (Hjn d sd Hd) as Hdl.
            unfold rfin.
            destruct (Nat.eqb_spec d (b + 1)) as [-> | N1].
            { replace ((b + 1) mod 12) with 1 in Hp by dlia. cbn [rpost_k] in Hp. rewrite Ehd, Evd. exact Hp. }
            destruct (Nat.eqb_spec d (b + 5)) as [-> | N5].
            { replace ((b + 5) mod 12) with 5 in Hp by dlia. cbn [rpost_k] in Hp. rewrite Ehd, Evd. exact Hp. }
            destruct (Nat.eqb_spec d (b + 7)) as [-> | N7].
            { replace ((b + 7) mod 12) with 7 in Hp by dlia. cbn [rpost_k] in Hp. rewrite Ehd, Evd. exact Hp. }
            destruct (Nat.eqb_spec d (b + 11)) as [-> | N11]; [| exact Logic.I].
            replace ((b + 11) mod 12) with 11 in Hp by dlia. cbn [rpost_k] in Hp.
            replace (b + 11 - 11) with b in Hp by lia.
            rewrite gvat_lt, !ghat_lt in Hp by lia. rewrite <- Ehd, <- Evd in Hp.
            assert (Hrok' : rok (vat (evs Γ) (b + 1)) (vat (evs Γ) (b + 11)) = true).
            { replace (b + 1) with (2 * length cs - 11) by dlia. replace (b + 11) with (2 * length cs - 1) by dlia. exact Hrok. }
            rewrite Hrok' in Hp. exact Hp.
          + (* bw_est0 *) intros s _ _. exact Logic.I.
          + (* bw_if *)
            intros d g sg Hdl Hg Hnb. rewrite (Hok g sg Hg). cbn [rslot sl_guar]. pose proof (Hjn g sg Hg) as Hgl.
            assert (Hany : forall x, kcls x = 0 -> Stable IV (rguar_q (g mod 12)) (ka x)).
            { intros x Hx. destruct (rguar_pos g) as [(-> & _) | [(-> & _) | (-> & _)]];
                [exact (ka_stable_gv x Hx) | apply ka_stable_gr | apply ka_stable_gn; lia]. }
            unfold rfin.
            destruct (Nat.eqb_spec d (b + 1)); [apply Hany; reflexivity |].
            destruct (Nat.eqb_spec d (b + 5)); [apply Hany; reflexivity |].
            destruct (Nat.eqb_spec d (b + 7)); [apply Hany; reflexivity |].
            destruct (Nat.eqb_spec d (b + 11)) as [-> | _]; [| apply Stable_true].
            destruct (rguar_pos g) as [(-> & Hg28) | [(-> & _) | (-> & Hg2 & _)]]; [| apply ka_stable_gr |];
              exfalso; apply Hnb; apply (bef_pos rc si i k Γ H cs g (b + 11) Hc Hr); dlia.
          + (* bw_if0 *) intros g sg _. apply Stable_true.
          + (* bw_R *)
            intros d. unfold rfin.
            repeat match goal with |- context [if ?x then _ else _] => destruct x end; first [apply ka_stable_r | apply Stable_true].
          + (* bw_R0 *) apply Stable_true.
          + (* bw_sum *)
            intros s HI _ Hfin.
            assert (Hres : forall j, j < length cs ->
                             exists sd, nth_error Γ (S (2 * j)) = Some sd /\ is_response (untag (sl_ev sd))).
            { intros j Hj. destruct (nth_error cs j) as [c0 |] eqn:Ej; [| apply nth_error_None in Ej; lia].
              destruct (runctx_res_at k Γ H cs j c0 Hc Ej) as (sr & v & Hsr & Hev). exists sr. split; [exact Hsr |].
              unfold is_response. rewrite Hev. exact Logic.I. }
            destruct (Hres (length cs - 6)) as (s1 & H1 & R1); [dlia |].
            destruct (Hres (length cs - 4)) as (s5 & H5 & R5); [dlia |].
            destruct (Hres (length cs - 3)) as (s7 & H7 & R7); [dlia |].
            destruct (Hres (length cs - 1)) as (s11 & H11 & R11); [dlia |].
            pose proof (Hfin _ _ H1 R1) as F1. pose proof (Hfin _ _ H5 R5) as F5.
            pose proof (Hfin _ _ H7 R7) as F7. pose proof (Hfin _ _ H11 R11) as F11.
            replace (S (2 * (length cs - 6))) with (b + 1) in F1 by dlia.
            replace (S (2 * (length cs - 4))) with (b + 5) in F5 by dlia.
            replace (S (2 * (length cs - 3))) with (b + 7) in F7 by dlia.
            replace (S (2 * (length cs - 1))) with (b + 11) in F11 by dlia.
            unfold rfin in F1, F5, F7, F11.
            rewrite Nat.eqb_refl in F1.
            rewrite (proj2 (Nat.eqb_neq (b + 5) (b + 1))), Nat.eqb_refl in F5 by lia.
            rewrite (proj2 (Nat.eqb_neq (b + 7) (b + 1))), (proj2 (Nat.eqb_neq (b + 7) (b + 5))), Nat.eqb_refl in F7 by lia.
            rewrite (proj2 (Nat.eqb_neq (b + 11) (b + 1))), (proj2 (Nat.eqb_neq (b + 11) (b + 5))),
              (proj2 (Nat.eqb_neq (b + 11) (b + 7))), Nat.eqb_refl in F11 by lia.
            cbn [ka] in F1, F5, F7, F11. destruct F11 as [Hpk HT].
            assert (P1 : hat (evs Γ) b = hat (evs Γ) (b + 1)).
            { pose proof (hat_pair rc si k Γ H cs (length cs - 6) Hc ltac:(dlia)) as E.
              replace (2 * (length cs - 6)) with b in E by dlia. rewrite E. f_equal. lia. }
            assert (P5 : hat (evs Γ) (b + 4) = hat (evs Γ) (b + 5)).
            { pose proof (hat_pair rc si k Γ H cs (length cs - 4) Hc ltac:(dlia)) as E.
              replace (2 * (length cs - 4)) with (b + 4) in E by dlia. rewrite E. f_equal. lia. }
            assert (P7 : hat (evs Γ) (b + 6) = hat (evs Γ) (b + 7)).
            { pose proof (hat_pair rc si k Γ H cs (length cs - 3) Hc ltac:(dlia)) as E.
              replace (2 * (length cs - 3)) with (b + 6) in E by dlia. rewrite E. f_equal. lia. }
            rewrite <- P1 in F1. rewrite <- P5 in F5. rewrite <- P7 in F7.
            replace (b + 5) with (2 * length cs - 7) in F5 by dlia. rewrite Ha in F5.
            replace (b + 7) with (2 * length cs - 5) in F7 by dlia. rewrite Hcv in F7.
            split; [| exact Logic.I].
            apply (sl_read_close_rd rc si tw k i (t, hat (evs Γ) b) (t, hat (evs Γ) (b + 4)) (t, hat (evs Γ) (b + 6))
                     (t, hat (evs Γ) (b + 11)) s (vat (evs Γ) (b + 1)) a c (vat (evs Γ) (b + 11)) HI); [| exact F1 | exact F5 | exact F7 | exact HT |].
            * destruct Hpk as [Hpk | Hown]; [left; exact Hpk | right; exact (owns_not_noown rc si k isRmb _ Hown)].
            * replace (b + 1) with (2 * length cs - 11) by dlia. replace (b + 11) with (2 * length cs - 1) by dlia. exact Hrok.
        - (* the footprint *)
          cbn [Osl]. rewrite (own_invs_run k Γ H cs Hc). exact (rdshape_calls rc t i cs Hr Hm Hpos Hnd).
      Qed.

      (** Every machine step satisfies [RunStepOK]. *)
      Lemma rstep_ok st cs Γ H :
        RunCtx k Γ H cs -> rinv st cs Γ H ->
        RunStepOK IV RV GV k Pinit rinv
          (fun a Γ' H' => Close IV RV GV k Pinit (fun r s => QrdV rc si k i r s /\ True) a Γ' H' /\
                          Osl rc tw t (fR i) h (own_invs Γ'))
          cs Γ H (rnext i st).
      Proof.
        intros Hc Hi. pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        destruct st as [| s0 | s0 | s0 a0 | s0 a0 c0 | s0 a0 c0 | a0 c0]; cbn [rnext RunStepOK].
        - (* RG: the first [rd Sq_i] of an iteration *)
          destruct Hi as (Hr & Hok & Hnl & Hm).
          exists (rsi Γ H cs (sRd (Sq i))), (rsr Γ H cs (sRd (Sq i))).
          assert (Hop : sRd (Sq i) = rop i (length cs mod 6)) by (rewrite Hm; reflexivity).
          apply (rcall rinv cs Γ H (sRd (Sq i)) (fun s => RA s) Hc Hr Hok Hnl Hop).
          + intros hu. apply (upd_G _ _ _ hu); [rewrite HlΓ; dlia | reflexivity].
          + intros hu v. apply (upd_res_rd _ _ _ hu (Sq i) v); [reflexivity |]. left.
            split; [rewrite length_app; cbn [length]; rewrite HlΓ; dlia | reflexivity].
          + intros hu v H' _ _ Hc'.
            destruct (call_facts cs Γ H _ hu v Hc Hr Hok Hop) as (Hr2 & Hok2 & Hl2 & Hlc & Hold & Hnew & Hnl2).
            split; [exact Hr2 |]. split; [exact Hok2 |]. rewrite Hl2, Hlc.
            split; [apply (noloop_ext _ (length Γ)); [exact (Hnl2 _ Hnl (le_n _)) | intros y Hy; rewrite HlΓ in Hy; dlia] |].
            split; [dlia |]. replace (2 * S (length cs) - 1) with (S (length Γ)) by lia. exact Hnew.
        - (* RA s: [rmb_a] *)
          destruct Hi as (Hr & Hok & Hnl & Hm & Hs).
          exists (rsi Γ H cs sRmb), (rsr Γ H cs sRmb).
          assert (Hop : sRmb = rop i (length cs mod 6)) by (rewrite Hm; reflexivity).
          apply (rcall rinv cs Γ H sRmb (fun _ => RX s0) Hc Hr Hok Hnl Hop).
          + intros hu. apply (upd_A _ _ _ hu); [rewrite HlΓ; dlia | reflexivity].
          + intros hu v. apply (upd_res_rmb _ _ _ hu v); [reflexivity |]. left. rewrite length_app; cbn [length]; rewrite HlΓ; dlia.
          + intros hu v H' _ _ Hc'.
            destruct (call_facts cs Γ H _ hu v Hc Hr Hok Hop) as (Hr2 & Hok2 & Hl2 & Hlc & Hold & Hnew & Hnl2).
            split; [exact Hr2 |]. split; [exact Hok2 |]. rewrite Hl2, Hlc.
            split; [apply (noloop_ext _ (length Γ)); [exact (Hnl2 _ Hnl (le_n _)) | intros y Hy; rewrite HlΓ in Hy; dlia] |].
            split; [dlia |]. rewrite Hold by dlia. rewrite <- Hs. f_equal. lia.
        - (* RX s: [rd Sx_i] *)
          destruct Hi as (Hr & Hok & Hnl & Hm & Hs).
          exists (rsi Γ H cs (sRd (Sx i))), (rsr Γ H cs (sRd (Sx i))).
          assert (Hop : sRd (Sx i) = rop i (length cs mod 6)) by (rewrite Hm; reflexivity).
          apply (rcall rinv cs Γ H (sRd (Sx i)) (fun a => RY s0 a) Hc Hr Hok Hnl Hop).
          + intros hu. apply (upd_X _ _ _ hu); [rewrite HlΓ; dlia | reflexivity].
          + intros hu v. apply (upd_res_rd _ _ _ hu (Sx i) v); [reflexivity |]. right; left.
            split; [rewrite length_app; cbn [length]; rewrite HlΓ; dlia | reflexivity].
          + intros hu v H' _ _ Hc'.
            destruct (call_facts cs Γ H _ hu v Hc Hr Hok Hop) as (Hr2 & Hok2 & Hl2 & Hlc & Hold & Hnew & Hnl2).
            split; [exact Hr2 |]. split; [exact Hok2 |]. rewrite Hl2, Hlc.
            split; [apply (noloop_ext _ (length Γ)); [exact (Hnl2 _ Hnl (le_n _)) | intros y Hy; rewrite HlΓ in Hy; dlia] |].
            split; [dlia |]. split; [rewrite Hold by dlia; rewrite <- Hs; f_equal; lia |].
            replace (2 * S (length cs) - 1) with (S (length Γ)) by lia. exact Hnew.
        - (* RY s a: [rd Sy_i] *)
          destruct Hi as (Hr & Hok & Hnl & Hm & Hs & Ha).
          exists (rsi Γ H cs (sRd (Sy i))), (rsr Γ H cs (sRd (Sy i))).
          assert (Hop : sRd (Sy i) = rop i (length cs mod 6)) by (rewrite Hm; reflexivity).
          apply (rcall rinv cs Γ H (sRd (Sy i)) (fun c => RB s0 a0 c) Hc Hr Hok Hnl Hop).
          + intros hu. apply (upd_Y _ _ _ hu); [rewrite HlΓ; dlia | reflexivity].
          + intros hu v. apply (upd_res_rd _ _ _ hu (Sy i) v); [reflexivity |]. right; right; left.
            split; [rewrite length_app; cbn [length]; rewrite HlΓ; dlia | reflexivity].
          + intros hu v H' _ _ Hc'.
            destruct (call_facts cs Γ H _ hu v Hc Hr Hok Hop) as (Hr2 & Hok2 & Hl2 & Hlc & Hold & Hnew & Hnl2).
            split; [exact Hr2 |]. split; [exact Hok2 |]. rewrite Hl2, Hlc.
            split; [apply (noloop_ext _ (length Γ)); [exact (Hnl2 _ Hnl (le_n _)) | intros y Hy; rewrite HlΓ in Hy; dlia] |].
            split; [dlia |]. split; [rewrite Hold by dlia; rewrite <- Hs; f_equal; lia |].
            split; [rewrite Hold by dlia; rewrite <- Ha; f_equal; lia |].
            replace (2 * S (length cs) - 1) with (S (length Γ)) by lia. exact Hnew.
        - (* RB s a c: [rmb_b] *)
          destruct Hi as (Hr & Hok & Hnl & Hm & Hs & Ha & Hcv).
          exists (rsi Γ H cs sRmb), (rsr Γ H cs sRmb).
          assert (Hop : sRmb = rop i (length cs mod 6)) by (rewrite Hm; reflexivity).
          apply (rcall rinv cs Γ H sRmb (fun _ => RT s0 a0 c0) Hc Hr Hok Hnl Hop).
          + intros hu. apply (upd_B _ _ _ hu); [rewrite HlΓ; dlia | reflexivity].
          + intros hu v. apply (upd_res_rmb _ _ _ hu v); [reflexivity |]. right. rewrite length_app; cbn [length]; rewrite HlΓ; dlia.
          + intros hu v H' _ _ Hc'.
            destruct (call_facts cs Γ H _ hu v Hc Hr Hok Hop) as (Hr2 & Hok2 & Hl2 & Hlc & Hold & Hnew & Hnl2).
            split; [exact Hr2 |]. split; [exact Hok2 |]. rewrite Hl2, Hlc.
            split; [apply (noloop_ext _ (length Γ)); [exact (Hnl2 _ Hnl (le_n _)) | intros y Hy; rewrite HlΓ in Hy; dlia] |].
            split; [dlia |]. split; [rewrite Hold by dlia; rewrite <- Hs; f_equal; lia |].
            split; [rewrite Hold by dlia; rewrite <- Ha; f_equal; lia |].
            rewrite Hold by dlia; rewrite <- Hcv; f_equal; lia.
        - (* RT s a c: the final [rd Sq_i] and the validation *)
          destruct Hi as (Hr & Hok & Hnl & Hm & Hs & Ha & Hcv).
          exists (rsi Γ H cs (sRd (Sq i))), (rsr Γ H cs (sRd (Sq i))).
          assert (Hop : sRd (Sq i) = rop i (length cs mod 6)) by (rewrite Hm; reflexivity).
          apply (rcall rinv cs Γ H (sRd (Sq i)) (fun s' => if rok s0 s' then RD a0 c0 else RG) Hc Hr Hok Hnl Hop).
          + intros hu. apply (upd_T _ _ _ hu); [rewrite HlΓ; dlia | reflexivity].
          + intros hu v.
            assert (Hl1 : length (Γ ++ [rsi Γ H cs (sRd (Sq i)) hu]) = S (length Γ)) by (rewrite length_app; cbn; lia).
            assert (Hq : length (Γ ++ [rsi Γ H cs (sRd (Sq i)) hu]) mod 12 = 11) by (rewrite Hl1, HlΓ; dlia).
            assert (Hg : gvat (evs (Γ ++ [rsi Γ H cs (sRd (Sq i)) hu])) (length (Γ ++ [rsi Γ H cs (sRd (Sq i)) hu]))
                           (length (Γ ++ [rsi Γ H cs (sRd (Sq i)) hu]) - length (Γ ++ [rsi Γ H cs (sRd (Sq i)) hu]) mod 12 + 1) = s0).
            { rewrite Hq, gvat_first by (rewrite Hl1, HlΓ; dlia). rewrite <- Hs. f_equal. rewrite Hl1, HlΓ. dlia. }
            destruct (rok s0 v) eqn:Er.
            * apply (upd_rT _ _ _ hu v Hq); [reflexivity |]. rewrite Hg. exact Er.
            * apply (upd_res_rd _ _ _ hu (Sq i) v); [reflexivity |]. right; right; right.
              split; [exact Hq |]. split; [reflexivity |]. rewrite Hg. exact Er.
          + intros hu v H' _ _ Hc'.
            destruct (call_facts cs Γ H _ hu v Hc Hr Hok Hop) as (Hr2 & Hok2 & Hl2 & Hlc & Hold & Hnew & Hnl2).
            cbn [sval] in Hnew.
            destruct (rok s0 v) eqn:Er.
            * split; [exact Hr2 |]. split; [exact Hok2 |]. rewrite Hl2, Hlc.
              split; [apply (noloop_ext _ (length Γ)); [exact (Hnl2 _ Hnl (le_n _)) | intros y Hy; rewrite HlΓ in Hy; dlia] |].
              split; [dlia |]. split; [lia |].
              split; [rewrite Hold by dlia; replace (2 * S (length cs) - 1) with (S (length Γ)) by lia; rewrite Hnew;
                      replace (2 * S (length cs) - 11) with (2 * length cs - 9) by dlia; rewrite Hs; exact Er |].
              split; [rewrite Hold by dlia; rewrite <- Ha; f_equal; lia |].
              rewrite Hold by dlia; rewrite <- Hcv; f_equal; lia.
            * split; [exact Hr2 |]. split; [exact Hok2 |]. rewrite Hl2, Hlc.
              split; [| dlia].
              apply (noloop_add _ (S (length Γ))).
              -- intros y Hy Hy11. destruct (Nat.eq_dec y (length Γ)) as [-> | Hne].
                 ++ exfalso. rewrite HlΓ in Hy11. dlia.
                 ++ exact (Hnl2 _ Hnl (le_n _) y ltac:(lia) Hy11).
              -- intros y Hy Hy11. assert (y = S (length Γ)) as -> by lia. rewrite Hnew.
                 cbn [sval].
                 rewrite Hold by (rewrite HlΓ; dlia). replace (S (length Γ) - 10) with (2 * length cs - 9) by (rewrite HlΓ; dlia).
                 rewrite Hs. exact Er.
        - (* RD a c: the return *)
          exact (rclose cs Γ H a0 c0 Hc Hi).
      Qed.
    End Call.

    (** ** Part 8. The derivation of the read over [EIhlv] *)

    (** The read [fR i] on thread [t]: a syntactic derivation through
        [RelaxedHoareSL2InvLog.sl2_read_run_provable_v] (hence
        [run_method_provable], [rp_run], [RProvable_coind]) with the
        machine invariant [rinv], every [RunStepOK] discharged
        ([rstep_ok]); postcondition [QrdV ∧ True]. *)
    Theorem read_provable_vti :
      MethodProvable IV RV GV (M2w rc si tw) t (fR i) (fun h => Osl rc tw t (fR i) h)
        (fun h r s => QrdV rc si (t, h) i r s /\ True).
    Proof.
      apply (sl2_read_run_provable_v rc si tw t i (fun _ _ _ => True) rinv).
      - intros h. exact (rinv_init h).
      - intros h st cs Γ H Hc Hi. exact (rstep_ok h st cs Γ H Hc Hi).
    Qed.
  End Read.

  (** [SL2ReadV] (the read premise of the assembly
      [RelaxedHoareSL2InvLog.sl2rd_v_of_methods]) for every [rc], [tw]
      and every [si ⊇ slRA]. *)
  Theorem read_provable_v rc si tw (Hsi : forall o o', slRA o o' -> si o o') : SL2ReadV rc si tw.
  Proof. intros t i. exists (fun _ _ _ => True). exact (read_provable_vti rc si tw Hsi t i). Qed.

  (** ** Part 9. The main theorem and its corollaries *)

  (** The derivation-carrying target over [EIhlv]: both methods are
      syntactic [MethodProvable] derivations over [EIhlv δS] (the read
      here, the write in [RelaxedHoareSL2Write], lifted by
      [methodprovable_lift] inside [RelaxedHoareSL2InvLog.sl2rd_v_of_methods]),
      and [RLHL2Hyps] over [EIhlv δS] from [((((regs0, []), []), []))]
      for [M2w rc si tw], for every [rc], [tw] and every [si ⊇ slRA]. *)
  Theorem sl2_main : sl2rd_prov_target_v.
  Proof.
    apply sl2rd_v_of_methods. intros rc si tw Hsi. split.
    - exact (read_provable_v rc si tw Hsi).
    - intros i vx vy. exact (RelaxedHoareSL2Write.write_provable rc si tw i vx vy).
  Qed.

  (** Copy-cat inclusion over the plain [EI δS], for every overlay trace
      of [M2w rc si tw], complete or not ([RelaxedHoareLog.rlhl_complin_eihlv]). *)
  Corollary sl2_complin : sl2rd_complin_target.
  Proof. exact (sl2rd_complin_of_target_v sl2_main). Qed.

  (** Relaxed linearizability of every complete trace at [si]
      ([RelaxedHoareLog.rlhl_eihlv_rel_lin], hence [cc_rel_lin]). *)
  Corollary sl2_rel_lin : sl2rd_relin_target.
  Proof. exact (sl2rd_relin_of_target_v sl2_main). Qed.

  (** The cross-SeqLock load-buffering trace is not a trace of the WRd
      module, for any [si] ([RelaxedHoareSL2Exec.lb2_not_trace_rd_of_rel_lin]
      with its hypothesis discharged by [sl2_rel_lin] at [slRA]). *)
  Corollary lb2_not_trace_rd rc si tw t1 t2 :
    ~ RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
        (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.lb2_trace si t1 t2).
  Proof.
    apply (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.lb2_not_trace_rd_of_rel_lin rc si tw t1 t2).
    intros s Htr Hc. exact (sl2_rel_lin rc slRA tw s (fun o o' H => H) Htr Hc).
  Qed.

  (** ** Part 10. Further corollaries (reviews m-68, m-69, M-29)

      Added after the final review of RLHL-seqlock.  Each is a short
      consequence of the results above; none changes them. *)

  (** The read derivations discharge the premise of
      [RelaxedHoareSL2Write.rlhl2_v_of_reads]: [RLHL2Hyps] over [EIhlv δS]
      with the lifted [Isl]/[Rsl]/[Gsl], for every [si ⊇ slRA] (m-68).
      [sl2_main] reaches the same conclusion through
      [RelaxedHoareSL2InvLog.sl2rd_v_of_methods]; this instance checks that
      the write-side combination of [RelaxedHoareSL2Write] fits too. *)
  Corollary rlhl2_v_of_reads_inst rc si tw (Hsi : forall o o', slRA o o' -> si o o') :
    RLHL2Hyps (RelaxedHoareLog.liftIV (E := E_S rc) (F := F2 si) δS δF (Isl rc si tw))
      (RelaxedHoareLog.liftGLk (Rsl rc si)) (RelaxedHoareLog.liftGLk (Gsl rc si))
      (M2w rc si tw) ((((regs0, []), []), [])) (A0, []).
  Proof.
    apply RelaxedHoareSL2Write.rlhl2_v_of_reads. intros t i.
    destruct (read_provable_v rc si tw Hsi t i) as (X & HX). exact (ex_intro _ _ (ex_intro _ _ HX)).
  Qed.

  (** The precondition form of P1 (m-69): for the unguarded module [M2]
      (any thread may write any instance), every overlay trace that
      satisfies [P1 tw] (only [tw i] writes instance [i]) is a trace of the
      copy-cat over the sequential specification, for every [si ⊇ slRA].
      By [RelaxedHoareSL2Prog.mtraces_guard] and [sl2_complin]. *)
  Corollary sl2_complin_unguarded rc si tw s :
    (forall o o', slRA o o' -> si o o') ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2 rc si) (regs0, []) s ->
    P1 tw s ->
    RelaxedHoareCompLin.RTraces (RelaxedHoareSpec.EI (F := F2 si) δF) (A0, []) s.
  Proof. intros Hsi Htr HP. apply (sl2_complin rc si tw Hsi). exact (mtraces_guard rc si tw _ _ s Htr HP). Qed.

  (** The same for complete traces and [rel_lin] (from [sl2_rel_lin]). *)
  Corollary sl2_rel_lin_unguarded rc si tw s :
    (forall o o', slRA o o' -> si o o') ->
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2 rc si) (regs0, []) s ->
    P1 tw s -> PrefixView.complete s ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) s si (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
  Proof. intros Hsi Htr HP Hc. exact (sl2_rel_lin rc si tw s Hsi (mtraces_guard rc si tw _ _ s Htr HP) Hc). Qed.

  (** Message passing is excluded at the module level (m-69): no complete
      trace of [M2w rc si tw] over [EI δS] is MP-shaped
      ([RelaxedHoareSL2Exec.mp_shaped]), for every [si] (no hypothesis on
      [si], as for [lb2_not_trace_rd]): the trace is moved to [slRA]
      ([RelaxedHoareResig.mtraces_resig_iff], [complete_resig],
      [rel_lin_resig_seq]), where [sl2_rel_lin] makes it relaxed-
      linearizable under [slRA ⊆ slsi], which
      [RelaxedHoareSL2Exec.mp2_not_rel_lin] refutes. *)
  Corollary sl2_no_mp rc si tw s :
    RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, []) s ->
    PrefixView.complete s -> ~ RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.mp_shaped s.
  Proof.
    intros Htr Hc Hmp.
    apply (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.mp2_not_rel_lin si slRA s slRA_slsi Hmp).
    apply (proj2 (RelaxedHoareResig.RelaxedHoareResig.rel_lin_resig_seq (F := F2 si) slRA δF A0 s slRA)).
    apply (sl2_rel_lin rc slRA tw _ (fun o o' H => H)).
    - exact (proj1 (RelaxedHoareResig.RelaxedHoareResig.mtraces_resig_iff (F := F2 si) slRA
                      (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (M2w rc slRA tw)
                      (fun _ _ => eq_refl) (regs0, []) s) Htr).
    - exact (proj1 (RelaxedHoareResig.RelaxedHoareResig.complete_resig (F := F2 si) slRA s) Hc).
  Qed.

  (** The SeqLock-level SB-with-own-reads trace
      ([RelaxedHoareSL2Exec.sbo]) is not a trace of the WRd module over
      this MCA underlay, for any [si] (M-29): it is complete
      ([RelaxedHoareSL2Exec.sbo_complete]) and not relaxed-linearizable
      under [slRA] ([RelaxedHoareSL2Exec.sbo_not_rel_lin]).  Whether a
      store-forwarding underlay produces it is not addressed here. *)
  Corollary sbo_not_trace_rd rc si tw t1 t2 :
    ~ RelaxedHoareCompLin.MTraces (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (regs0, [])
        (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.sbo si t1 t2).
  Proof.
    intros Hm.
    pose proof (proj1 (RelaxedHoareResig.RelaxedHoareResig.mtraces_resig_iff (F := F2 si) slRA
                         (RelaxedHoareSpec.EI (F := E_S rc) δS) (M2w rc si tw) (M2w rc slRA tw)
                         (fun _ _ => eq_refl) (regs0, []) (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.sbo si t1 t2)) Hm) as Hm'.
    change (map (RelaxedHoareResig.RelaxedHoareResig.ev_resig (F := F2 si) slRA)
                (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.sbo si t1 t2))
      with (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.sbo slRA t1 t2) in Hm'.
    exact (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.sbo_not_rel_lin slRA slRA t1 t2 (fun _ _ H => H)
             (sl2_rel_lin rc slRA tw _ (fun o o' H => H) Hm'
                (RelaxedHoareSL2Exec.RelaxedHoareSL2Exec.sbo_complete slRA t1 t2))).
  Qed.
End RelaxedHoareSL2Read.
