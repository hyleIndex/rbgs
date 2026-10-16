(** * RelaxedHoareSL2Write: the RLHL derivation of the SeqLock writer
      (WRd, cached [v]) — RLHL-seqlock task .6

    Plan: .rocq-review/tasks/RLHL-seqlock.md, task .6, with its Addenda
    (RS-1: WRd only; Addendum 2: "RLHL in full", every method a
    [MethodProvable] derivation through [run_method_provable]/[rp_run];
    Addendum 3: option B, the main theorem over [EIhlv := Log (EIhl δS)]).
    The program and the frozen invariant, rely, guarantee, footprint and
    postcondition are those of [RelaxedHoareSL2Prog] and
    [RelaxedHoareSL2Inv]; nothing there is changed.

    The writer [wnext i vx vy] (call indices 0-6):
    [v <- rd Sq_i; wr Sq_i (v+1) [dix 0]; wmb; wr Sx_i vx; wr Sy_i vy;
     wmb; wr Sq_i (v+2) [dix 0]], run by [M2w rc si tw] on thread [tw i]
    (single writer per instance, P1).  It is "a single-writer seqcount
    whose closing increment reuses the opening read" (author decision on
    M-23, research-intent §8), not the Linux writer.  Its linearization
    point is the emission of [wr Sq_i (v+1)] ([isl_wr_lp]).

    ** Main results
    - [write_provable rc si tw i vx vy]: [MethodProvable Isl Rsl Gsl
      (M2w rc si tw) (tw i) (fW i vx vy) (Osl (tw i) (fW i vx vy))
      (Qsl (tw i, h) (fW i vx vy))], over [VE := EIhl δS],
      [VF := EI δF], for every [rc], [si], [tw], [i], [vx], [vy]; no
      hypothesis on [si].  A syntactic derivation:
      [RelaxedHoareSL2Inv.sl2_write_run_provable] (hence
      [run_method_provable], [rp_run], [RProvable_coind]) with the machine
      invariant [winv] below, every [RunStepOK] discharged ([wstep_ok]).
      For writes the postcondition of Part 9 of [RelaxedHoareSL2Inv] is
      [Qop k (fW ..) = Qsl k (fW ..)], so this is also the [Qop] shape.
    - [write_provable_v]: the same derivation over
      [EIhlv δS = Log (EIhl δS)], by [RelaxedHoareLog.methodprovable_lift]
      with [J := LogOK δS]: invariant [liftIV δS δF Isl]
      (= [liftI (LogOK δS) Isl] by definition), rely and guarantee
      [liftGLk Rsl], [liftGLk Gsl], postcondition [liftA Qsl], footprint
      [Osl].  These are exactly the [I], [R], [G] that the [Hprov]
      premise of [RelaxedHoareLog.rlhl2_eihlv_of_provable] expects for
      [I := Isl], [R := Rsl], [G := Gsl]: no mismatch.
      [write_other_provable_v] (writes on [t <> tw i], [div]) and
      [write_fits_eihlv] (every write, every thread, in [Hprov]'s
      [∃ Ω Q] shape) complete the write half.
    - [rlhl2_v_of_reads]: a type check of the combination of task .7:
      lifted read derivations (its premise) together with
      [write_fits_eihlv] and the side fields of [RelaxedHoareSL2Inv]
      ([gsl_rsl], [invoke_rely], [return_rely], [isl_ok], [isl_init])
      instantiate [rlhl2_eihlv_of_provable]: [RLHL2Hyps] over [EIhlv δS]
      for [M2w rc si tw] from [((((regs0, []), []), []))].  The premise
      was open when this file was written (task .5); it is discharged,
      for every [si ⊇ slRA], by [RelaxedHoareSL2Read.read_provable_v]
      (whose [IslV]/[RslV]/[GslV] are by definition the [liftIV]/[liftGLk]
      combinators of the premise): kernel-checked as
      [RelaxedHoareSL2Read.rlhl2_v_of_reads_inst] (review m-68).  The
      main theorem does not go through
      this lemma: it is [RelaxedHoareSL2Read.sl2_main], through
      [RelaxedHoareSL2InvLog.sl2rd_v_of_methods].

    ** The derivation
    Slots: call [c] has its invocation slot at position [2 c] and its
    response slot at [2 c + 1]; the slot at position [j] is
    [wslot v hu0 j ev] ([v]: the value returned by call 0, [hu0]: its
    handle).  The own dag of a run of the writer ([kin_edge], [wbefore],
    from [RelaxedHoareRun.dprec_run]):
    - (F2) edges: 0→2 and 0→12 (same location [Sq_i]), 2→4 and 2→10
      (DW→Wmb), 2→12 (same location), 4→6, 4→8, 4→12, 10→12 (Wmb→DW),
      6→10, 8→10 (DW→Wmb), 4→10 (Wmb/Wmb); (F3) edges 1→2 and 1→12
      (the tag [dix [0]]); each response after its invocation.
    - So [rd Sq_i] (position 0), its response (1) and the linearization
      point (2) precede every later slot; the two data writes (6, 8) are
      unordered with each other; the responses of calls 1-5 (3, 5, 7, 9,
      11) have no outgoing edge and float past every later slot.  The
      "reads vs writes" entries of the table are not realized inside the
      writer: its only read is call 0, which precedes everything
      (same-location edge to call 1, and transitively).
    Assertions ([wka] of the kinds [kin]/[kpost]): [WStart] (start of
    call 0: [k] at [ls_inv], its ghost entries are its footprint, from
    [pinit_facts]); [A1] (after [rd Sq_i]: the call owns its record of
    value [w = Sq_i] ([read_inv_mine]), holds instance [i] with
    [Sq_i = w], owns two pending writes of [Sq_i], [RecNB] of the read);
    [A2 v] (after the response: [w = v] by [eihl_mine_res]); [AW v bx by]
    (after the linearization point: [KLin] (at [ls_lini] with its
    record), holder with [Sq_i = v+1], [A i = (vx, vy)], [v] even, and
    [Sx_i = vx], [Sy_i = vy] once written); [KLin] (to [Close], hence
    [Qsl]).  Only nine in-edges carry facts (0→1, 1→2, 2→4, 4→6, 4→8,
    6→10, 8→10, 10→12, 12→13); every other in-edge and start is [True].
    Guarantees: [Gsl k] at the linearization point (2) and at the last
    write of [Sq_i] (12); every other slot [GF]: [Gsl k], the abstract
    state unchanged, ghost entries only removed and the pending writes of
    [Sq_i] kept, [Sq_i] unchanged, [Sx_i]/[Sy_i] unchanged or set to
    [vx]/[vy].  Every in-edge and post assertion ([wka]) is
    [Rsl k]-stable (the stability kit of [RelaxedHoareSL2Inv], and
    [klin_stable_r], [ktwo_stable_r]) and [GF]-stable ([wka_stable_f]);
    the start [WStart] is [Rsl k]-stable only ([wstart_stable_r]).
    Updates: [upd0] ([isl_inv_noreg]), [upd1] ([isl_response],
    [eihl_mine_res]), [upd2] ([isl_wr_lp], readiness by [ready_write]),
    [upd_wmb] ([isl_inv_noreg], [coup_lin_write]), [upd_data]
    ([isl_wr_data]), [upd6] ([isl_wr_end]), [upd_res] ([isl_response]).
    One generic lemma [wnew] proves every [NewSlotOK] from its update.
    Machine invariant [winv]: after [n] calls, the calls are the first [n]
    of [wnext] ([WCalls]) and every slot is the canonical one for its
    position ([SlotsOK]), for some [v] and [hu0].

    ** Which own-interference premises ([ns_if_*], [bw_if]) are genuine
    Genuine (an own event that may really occur in between, with an
    effect the assertion must survive):
    - the two data writes, both directions: [ns_if_new_in] at position 8
      ([wr Sy]) for the edge 4→8 against [wr Sx] (6); [ns_if_old_in] at
      8 for the edge 4→6 of [wr Sx] against [wr Sy]; [ns_if_new_in] at
      10 ([wmb_b]) for 6→10 ([Sx_i = vx]) against [wr Sy] and for 8→10
      ([Sy_i = vy]) against [wr Sx].  They hold because [GF] lets
      [Sx_i]/[Sy_i] move only to [vx]/[vy], keeps [Sq_i] and the pending
      [wr Sq_i] (so [Holder]) and the abstract state;
    - the floating responses of calls 1-5 (3, 5, 7, 9, 11) against every
      later fact-carrying edge whose source they do not precede (2→4,
      4→6, 4→8, 6→10, 8→10, 10→12, 12→13), against the edge 4→6 when the
      response of call 4 is added ([ns_if_old_in] at 9), and against the
      final edge of the response of call 6 ([bw_if]); a response changes
      no register, pool entry or ghost entry, so these are frame facts.
    Vacuous by the order ([wbefore]; the hypothesis [~ before] is
    refuted): every premise against the start [WStart] of call 0
    ([ns_if_old_start]: call 0 precedes everything), and every premise
    against the guarantees [Gsl k] of the linearization point and of the
    last write of [Sq_i] ([ns_if_new_in], [ns_if_old_in], [bw_if]).
    Trivial: the premises on [True] assertions (in particular the in-edges
    of the responses of calls 1-5).

    ** [rp_run] beyond one-call bodies: what was awkward
    This is the first multi-call use of [rp_run] (plan §3, "Risks").
    - [RunCallOK] asks [NewSlotOK] of the invocation slot in the half
      context [Γ ++ [si h]], which is not a [RunCtx]; [dprec_run] and the
      order facts are stated for run contexts.  The derivation builds the
      full context [((Γ ++ [si h]) ++ [sr h r0])] with a dummy response
      [r0] ([sar_inh]) and the resolved store, and transfers by
      [dprec_app_iff]/[before_app_iff] ([wnew]).  The response premise
      [NewOK (Γ ++ [si h]) (sr h v)] likewise comes without the store
      [H'], rebuilt by [runctx_snoc]/[resolve_here].
    - [NewSlotOK]'s [ns_if_*] premises read [sl_start], [sl_in],
      [sl_guar] of every earlier slot, so the machine invariant must
      determine the whole context; here every slot is the canonical slot
      of its position ([SlotsOK]), which needs the prophesied [v] and the
      handle [hu0] in the invariant.
    - A slot's guarantee is fixed when the slot is appended, but it must
      keep the in-edges of slots appended later ([ns_if_new_in]); the
      guarantees had to be designed for the whole body ([GF]).
    - The pre of [ns_update] is [pre_of], a quantification over the
      (F1)-(F3) edges; extracting an in-edge needs the positive edge fact
      ([kin_edge]).  At [SDone], [bw_sum] sees only the final assertions
      of response slots, so [Qsl] is routed to the response of the last
      call (position 13).
    - Not awkward: [RunStepOK] is a [match], so [cbn [wnext RunStepOK]]
      exposes each step; [rp_run] itself needed nothing beyond its
      premises.

    ** K / S / P / R
    - K: all 61 [Lemma]/[Theorem] results of this file are closed under
      the global context (Print Assumptions, Rocq 9.3.0), among them
      [write_provable], [write_provable_v], [write_other_provable_v],
      [write_fits_eihlv] and [rlhl2_v_of_reads].  No axiom, no
      [vm_compute]/[native_compute].
    - S: [write_provable] is a derivation for the write on its writer
      thread, for every [rc], [si], [tw], [i], [vx], [vy], with the frozen
      [Isl]/[Rsl]/[Gsl]/[Osl]/[Qsl]; [write_provable_v] is its lift
      (admissibility of the existing rules, no log fact used).  Neither is
      a soundness, copy-cat or relaxed-linearizability statement: those
      follow only with the read derivation (task .5,
      [RelaxedHoareSL2Read.read_provable_v]) through [method_sound] and
      [RelaxedHoareLog.rlhl_complin_eihlv] (task .7,
      [RelaxedHoareSL2Read.sl2_main], [sl2_complin], [sl2_rel_lin]).
      [rlhl2_v_of_reads] has the read derivations as a hypothesis, which
      [read_provable_v] discharges for every [si ⊇ slRA]
      ([RelaxedHoareSL2Read.rlhl2_v_of_reads_inst]).
    - P: no SeqLock text in the main paper (plan §1);
      Appendix/SeqLock.tex is a different, TicketLock-based object.  The
      rules used are the mechanized RLHL of [RelaxedHoare] (the printed
      rules of Appendix/programlogic.tex differ; see the table in its
      header, M-21), in the run-interpreter form of [RelaxedHoareRun]
      (review m-66); the history
      presentation restores the underlay projection of the paper's proof
      state (Appendix/programlogic.tex:530; :579, rule EStep; lines as in
      async-ccal commit 4a2db8e1, 42 higher than in 01484091), not its
      overlay invocations or the reachability clause of :579.
    - R: the writer half of popl2027-reviews.md:215 ("No example verified
      on the COH model"); the reader (.5) and the assembly (.7) are in
      [RelaxedHoareSL2Read], whose header gives the status against that
      concern.

    ** Limitations
    - The underlay is the sequential COH register file with ordering-only
      barriers of [RelaxedHoareSL2Prog] (scope as stated there).
    - The writer is single per instance (P1, the [M2w] guard); writes on
      other threads diverge ([write_other_provable_v] is the [div] case).
    - [write_provable_v] uses no history fact; it is the [EIhl]
      derivation transported by [methodprovable_lift].  The reader
      derivation ([RelaxedHoareSL2Read.read_provable_v]) uses the same
      lifted invariant [liftIV δS δF Isl] and the same lifted rely and
      guarantee, so this lift fits the same [RLHL2Hyps] (as used by
      [RelaxedHoareSL2Read.sl2_main]); no re-derivation was needed. *)

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
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import models.simlin.RelaxedHoareRun.
Require Import models.simlin.RelaxedHoareReady.
Require Import models.simlin.RelaxedHoareLog.
Require Import examples.Relaxed.RelaxedHoareSL2Prog.
Require Import examples.Relaxed.RelaxedHoareSL2Inv.

Import ListNotations.

Module RelaxedHoareSL2Write.
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
  Import RelaxedHoareSL2Prog.
  Import RelaxedHoareSL2Inv.

  (** The kinds of slot assertions (Part 3 of the section below). *)
  Inductive WK : Type := WKT | WK1 | WK2 | WKW (bx by_ : bool) | WKL.

  (** [kin j d]: the kind of the in-edge assertion from position [d] into
      the slot at position [j] (invocation of call [c] at [2 c], its
      response at [2 c + 1]); [WKT] ([True]) except on the nine edges that
      carry facts. *)
  Definition kin (j d : nat) : WK :=
    match j with
    | 1 => match d with 0 => WK1 | _ => WKT end
    | 2 => match d with 1 => WK2 | _ => WKT end
    | 4 => match d with 2 => WKW false false | _ => WKT end
    | 6 => match d with 4 => WKW false false | _ => WKT end
    | 8 => match d with 4 => WKW false false | _ => WKT end
    | 10 => match d with 6 => WKW true false | 8 => WKW false true | _ => WKT end
    | 12 => match d with 10 => WKW true true | _ => WKT end
    | 13 => match d with 12 => WKL | _ => WKT end
    | _ => WKT
    end.

  (** [kpost j]: the kind of the postcondition of the slot at position [j]. *)
  Definition kpost (j : nat) : WK :=
    match j with
    | 0 => WK1
    | 1 => WK2
    | 2 => WKW false false
    | 4 => WKW false false
    | 6 => WKW true false
    | 8 => WKW false true
    | 10 => WKW true true
    | 12 => WKL
    | 13 => WKL
    | _ => WKT
    end.

  Lemma kin_cases n d :
    kin n d = WKT \/ (n = 1 /\ d = 0) \/ (n = 2 /\ d = 1) \/ (n = 4 /\ d = 2) \/ (n = 6 /\ d = 4) \/
    (n = 8 /\ d = 4) \/ (n = 10 /\ d = 6) \/ (n = 10 /\ d = 8) \/ (n = 12 /\ d = 10) \/ (n = 13 /\ d = 12).
  Proof.
    destruct (kin n d) eqn:E; [left; reflexivity | right .. ]; unfold kin in E;
      repeat match type of E with
             | context [match ?x with _ => _ end] => is_var x; destruct x; cbn in E
             end; try discriminate E; lia.
  Qed.

  (** On every edge that carries a fact, the in-edge assertion is the
      postcondition of its source. *)
  Lemma kin_post n d : kin n d = WKT \/ kin n d = kpost d.
  Proof.
    destruct (kin_cases n d) as [E | H]; [left; exact E | right].
    repeat destruct H as [H | H]; destruct H as [-> ->]; reflexivity.
  Qed.

  Section Write.
    Context (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid).

    Local Abbreviation ES := (E_S rc).
    Local Abbreviation FS := (F2 si).
    Local Abbreviation VE := (EIhl (E := E_S rc) δS).
    Local Abbreviation VF := (RelaxedHoareSpec.EI (F := F2 si) δF).
    Local Abbreviation POk v pool := (@PossOk FS VF v pool).
    Local Abbreviation IS := (Isl rc si tw).
    Local Abbreviation RS := (Rsl rc si).
    Local Abbreviation GS := (Gsl rc si).
    Local Abbreviation rg := (regs rc si).

    (** The write [fW i vx vy] by its writer [tw i]. *)
    Context (i vx vy : nat).
    Local Abbreviation wt := (tw i).
    Local Abbreviation wop0 := (fW i vx vy).

    (** ** Part 1. The calls of the writer *)

    (** The operation and the tag indices of the [j]-th call of the writer
        whose [rd Sq_i] returned [v] ([wnext]). *)
    Definition wop (v j : nat) : SOp :=
      match j with
      | 0 => sRd (Sq i)
      | 1 => sWr (Sq i) (v + 1)
      | 2 => sWmb
      | 3 => sWr (Sx i) vx
      | 4 => sWr (Sy i) vy
      | 5 => sWmb
      | _ => sWr (Sq i) (v + 2)
      end.

    Definition wdix (j : nat) : list nat :=
      match j with 1 | 6 => [0] | _ => [] end.

    (** The calls [cs] of a run of the writer are a prefix of its seven
        calls. *)
    Definition WCalls (v : nat) (cs : list (RCall ES)) : Prop :=
      length cs <= 7 /\ forall j c, nth_error cs j = Some c -> rc_op c = wop v j /\ rc_dix c = wdix j.

    Section Call.
      Context (h : nat).
      Local Abbreviation k := (@pair tid (handle FS) wt h).
      Local Abbreviation Pinit := (PostInvoke IS k wop0 (Osl rc tw wt wop0 h)).

      (** ** Part 2. The slot assertions *)

      (** [k]'s ghost entries are exactly the invocations [L]. *)
      Definition KGh (L : list (ThreadEvent ES)) : Assn VE VF := fun s =>
        forall e : ScheduledEvent ES FS, se_owner e = k -> (In e (ps_ghost s) <-> exists ev, In ev L /\ e = Build_ScheduledEvent k ev).

      (** The start of the first call: [k] is at [ls_inv], and its ghost
          entries are its footprint. *)
      Definition WStart : Assn VE VF := fun s =>
        KLook rc si k (@ls_inv FS wop0) s /\ exists evs, Osl rc tw wt wop0 h evs /\ KGh evs s.

      (** [k] owns two distinct pending writes of [Sq_i]. *)
      Definition KTwo : Assn VE VF := fun s =>
        exists e1 e2 : ScheduledEvent ES FS, e1 <> e2 /\ In e1 (ps_ghost s) /\ In e2 (ps_ghost s) /\ se_owner e1 = k /\ se_owner e2 = k /\
          isWrSq i (gop rc si e1) /\ isWrSq i (gop rc si e2).

      (** [k] has linearized (at [ls_lini]) and its record is in the
          abstract history: the second disjunct of [Qsl]. *)
      Definition KLin : Assn VE VF := fun s =>
        exists A Pf P, ps_poss s = POk (A, Pf) P /\ lin_lookup k (@ls_lini FS wop0) P /\
          In (@RelaxedTraceLin.Build_Op FS k wop0 tt) Pf.

      (** After the emission of [rd Sq_i] (handle [hu0]): the call owns its
          record, whose value [w] is [Sq_i], and holds instance [i]. *)
      Definition A1 (hu0 : nat) : Assn VE VF := fun s =>
        exists w, KMine rc si (wt, hu0) (@RelaxedTraceLin.Build_Op ES (wt, hu0) (sRd (Sq i)) w) s /\
          KHeld rc si i k (fun q _ _ _ => q = w) s /\ KLook rc si k (@ls_inv FS wop0) s /\ KTwo s /\
          KRecNB rc si k (IE rc wt hu0 (sRd (Sq i))) s.

      (** After the response [v] of [rd Sq_i]. *)
      Definition A2 (v : nat) : Assn VE VF := fun s =>
        KHeld rc si i k (fun q _ _ _ => q = v) s /\ KLook rc si k (@ls_inv FS wop0) s /\ KTwo s /\
        exists h0, KRecNB rc si k (IE rc wt h0 (sRd (Sq i))) s.

      (** After the linearization point: linearized, holder, [Sq_i = v+1],
          the abstract pair is [(vx, vy)], and (if [bx], [by]) the data
          registers already hold [vx], [vy]. *)
      Definition AW (v : nat) (bx by_ : bool) : Assn VE VF := fun s =>
        KLin s /\
        KHeld rc si i k (fun q x y a => q = v + 1 /\ (bx = true -> x = vx) /\ (by_ = true -> y = vy) /\ a = (vx, vy)) s /\
        Nat.even v = true.

      (** The guarantee of every slot except the linearization point and
          the last write: the abstract state is unchanged, ghost entries
          are only removed and the pending writes of [Sq_i] are kept,
          [Sq_i] is unchanged and [Sx_i], [Sy_i] change only to [vx],
          [vy]. *)
      Definition GF : PRel VE VF := fun s s' =>
        GS k s s' /\ ps_poss s' = ps_poss s /\ incl (ps_ghost s') (ps_ghost s) /\
        (forall e : ScheduledEvent ES FS, In e (ps_ghost s) -> se_owner e = k -> isWrSq i (gop rc si e) -> In e (ps_ghost s')) /\
        rg s' (Sq i) = rg s (Sq i) /\
        (rg s' (Sx i) = rg s (Sx i) \/ rg s' (Sx i) = vx) /\
        (rg s' (Sy i) = rg s (Sy i) \/ rg s' (Sy i) = vy).

      (** *** Stability *)

      Lemma klin_stable_r : Stable IS (RS k) KLin.
      Proof.
        intros s s' (A & Pf & P & Hp & Hl & Hr) (_ & A1' & Pf1 & P1 & A1'' & Pf1' & P1' & Hp1 & Hp1' & Hlk & Hrec & _) _.
        rewrite Hp in Hp1. injection Hp1 as E1 E2 E3. subst A1' Pf1 P1. exists A1'', Pf1', P1'.
        split; [exact Hp1' |]. split; [exact (Hlk _ Hl) | exact (Hrec _ (eq_refl : RelaxedTraceLin.op_key (@RelaxedTraceLin.Build_Op FS k wop0 tt) = k) Hr)].
      Qed.

      Lemma klin_stable_f : Stable IS GF KLin.
      Proof.
        intros s s' (A & Pf & P & Hp & Hl & Hr) (_ & Hp' & _) _. exists A, Pf, P. rewrite Hp', Hp. auto.
      Qed.

      Lemma ktwo_stable_r : Stable IS (RS k) KTwo.
      Proof.
        intros s s' (e1 & e2 & Hne & H1 & H2 & Ho1 & Ho2 & Hq1 & Hq2) (_ & A1' & Pf1 & P1 & A1'' & Pf1' & P1' & _ & _ & _ & _ & Hgh & _) _.
        exists e1, e2. split; [exact Hne |]. split; [apply (Hgh e1 Ho1); exact H1 |]. split; [apply (Hgh e2 Ho2); exact H2 |]. auto.
      Qed.

      Lemma ktwo_stable_f : Stable IS GF KTwo.
      Proof.
        intros s s' (e1 & e2 & Hne & H1 & H2 & Ho1 & Ho2 & Hq1 & Hq2) (_ & _ & _ & Hkeep & _) _.
        exists e1, e2. split; [exact Hne |]. split; [exact (Hkeep e1 H1 Ho1 Hq1) |]. split; [exact (Hkeep e2 H2 Ho2 Hq2) |]. auto.
      Qed.

      Lemma kgh_stable_r L : Stable IS (RS k) (KGh L).
      Proof.
        intros s s' Hg (_ & A1' & Pf1 & P1 & A1'' & Pf1' & P1' & _ & _ & _ & _ & Hgh & _) _ e Ho.
        rewrite <- (Hgh e Ho). exact (Hg e Ho).
      Qed.

      Lemma wstart_stable_r : Stable IS (RS k) WStart.
      Proof.
        intros s s' (Hl & evs & HΩ & Hg) Hr HI. split; [exact (klook_stable rc si tw k _ s s' Hl Hr HI) |].
        exists evs. split; [exact HΩ | exact (kgh_stable_r evs s s' Hg Hr HI)].
      Qed.

      (** [KHeld] under [GF]: the holder is kept (no write of [Sq_i] is
          removed, the pool is unchanged), [Sq_i] and the abstract state
          are unchanged; [φ] must survive the data registers moving to
          [vx], [vy]. *)
      Lemma kheld_stable_f (φ : nat -> nat -> nat -> nat * nat -> Prop) :
        (forall q x y a x' y', φ q x y a -> (x' = x \/ x' = vx) -> (y' = y \/ y' = vy) -> φ q x' y' a) ->
        Stable IS GF (KHeld rc si i k φ).
      Proof.
        intros Hφ s s' (A & Pf & P & Hp & (Hw & Hr & Hs) & Hf) (_ & Hp' & Hincl & Hkeep & Hq & Hx & Hy) _.
        exists A, Pf, P. split; [rewrite Hp'; exact Hp |]. split.
        - split; [exact Hw |]. split.
          + intros Hown. apply Hr. exact (owns_incl rc si k _ _ _ Hincl Hown).
          + destruct Hs as (e & He & Ho & Hq'). exists e. split; [exact (Hkeep e He Ho Hq') |]. auto.
        - rewrite Hq. exact (Hφ _ _ _ _ _ _ Hf Hx Hy).
      Qed.

      Lemma krecnb_stable_f ev : Stable IS GF (KRecNB rc si k ev).
      Proof. intros s s' Hs [Hg _] HI. exact (krecnb_stable_g rc si tw k k ev s s' Hs Hg HI). Qed.

      Lemma kmine_stable_f key x0 : Stable IS GF (KMine rc si key x0).
      Proof. intros s s' Hs [Hg _] HI. exact (kmine_stable_g rc si tw k key x0 s s' Hs Hg HI). Qed.

      Lemma klook_stable_f ls : Stable IS GF (KLook rc si k ls).
      Proof. intros s s' (A & Pf & P & Hp & Hl) (_ & Hp' & _) _. exists A, Pf, P. rewrite Hp', Hp. auto. Qed.

      Lemma a1_stable_r hu0 : Stable IS (RS k) (A1 hu0).
      Proof.
        intros s s' (w & Hm & Hh & Hl & H2 & Hn) Hr HI. exists w.
        split; [exact (kmine_stable_r rc si tw k _ _ s s' Hm Hr HI) |].
        split; [exact (kheld_stable rc si tw k i _ s s' Hh Hr HI) |].
        split; [exact (klook_stable rc si tw k _ s s' Hl Hr HI) |].
        split; [exact (ktwo_stable_r s s' H2 Hr HI) | exact (krecnb_stable_r rc si tw k _ s s' Hn Hr HI)].
      Qed.

      Lemma a1_stable_f hu0 : Stable IS GF (A1 hu0).
      Proof.
        intros s s' (w & Hm & Hh & Hl & H2 & Hn) Hr HI. exists w.
        split; [exact (kmine_stable_f _ _ s s' Hm Hr HI) |].
        split; [apply (kheld_stable_f (fun q _ _ _ => q = w) (fun q x y a x' y' Hq _ _ => Hq) s s' Hh Hr HI) |].
        split; [exact (klook_stable_f _ s s' Hl Hr HI) |].
        split; [exact (ktwo_stable_f s s' H2 Hr HI) | exact (krecnb_stable_f _ s s' Hn Hr HI)].
      Qed.

      Lemma a2_stable_r v : Stable IS (RS k) (A2 v).
      Proof.
        intros s s' (Hh & Hl & H2 & h0 & Hn) Hr HI.
        split; [exact (kheld_stable rc si tw k i _ s s' Hh Hr HI) |].
        split; [exact (klook_stable rc si tw k _ s s' Hl Hr HI) |].
        split; [exact (ktwo_stable_r s s' H2 Hr HI) | exists h0; exact (krecnb_stable_r rc si tw k _ s s' Hn Hr HI)].
      Qed.

      Lemma a2_stable_f v : Stable IS GF (A2 v).
      Proof.
        intros s s' (Hh & Hl & H2 & h0 & Hn) Hr HI.
        split; [apply (kheld_stable_f (fun q _ _ _ => q = v) (fun q x y a x' y' Hq _ _ => Hq) s s' Hh Hr HI) |].
        split; [exact (klook_stable_f _ s s' Hl Hr HI) |].
        split; [exact (ktwo_stable_f s s' H2 Hr HI) | exists h0; exact (krecnb_stable_f _ s s' Hn Hr HI)].
      Qed.

      Lemma aw_stable_r v bx by_ : Stable IS (RS k) (AW v bx by_).
      Proof.
        intros s s' (Hl & Hh & Ev) Hr HI.
        split; [exact (klin_stable_r s s' Hl Hr HI) |]. split; [exact (kheld_stable rc si tw k i _ s s' Hh Hr HI) | exact Ev].
      Qed.

      Lemma aw_stable_f v bx by_ : Stable IS GF (AW v bx by_).
      Proof.
        intros s s' (Hl & Hh & Ev) Hr HI.
        split; [exact (klin_stable_f s s' Hl Hr HI) |]. split; [| exact Ev].
        refine (kheld_stable_f _ _ s s' Hh Hr HI).
        intros q x y a x' y' (Hq & Hx & Hy & Ha) Hx' Hy'. split; [exact Hq |]. split; [| split; [| exact Ha]].
        - intros Hb. destruct Hx' as [-> | ->]; [exact (Hx Hb) | reflexivity].
        - intros Hb. destruct Hy' as [-> | ->]; [exact (Hy Hb) | reflexivity].
      Qed.

      (** ** Part 3. The dependency dag of the writer *)

      Ltac nsi v := cbn [wop];
        first [ apply sindep_same_loc; reflexivity
              | let W := fresh "W" in pose proof (wr_order rc i v vx vy) as W; tauto ].

      (** An (F2) edge between the invocations of calls [a < j]. *)
      Lemma wdp_inv (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) v a j :
        RunCtx k Γ H cs -> WCalls v cs -> j < length cs -> a < j -> ~ sindep rc (wop v a) (wop v j) ->
        dprec (evs Γ) (2 * a) (2 * j).
      Proof.
        intros Hc [_ Hw] Hj Ha Hn.
        destruct (nth_error cs j) as [c |] eqn:Ej; [| apply nth_error_None in Ej; lia].
        destruct (nth_error cs a) as [ca |] eqn:Ea; [| apply nth_error_None in Ea; lia].
        apply (proj2 (dprec_run k Γ H cs (2 * a) (2 * j) Hc)).
        exists j, c. split; [exact Ej |]. left. split; [reflexivity |].
        exists a, ca. split; [exact Ea |]. split; [exact Ha |]. left. split; [reflexivity |].
        rewrite (proj1 (Hw a ca Ea)), (proj1 (Hw j c Ej)). exact Hn.
      Qed.

      (** An (F3) edge: the response of call [a] into the invocation of a
          call [j] whose tag names [a]. *)
      Lemma wdp_dix (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) v a j :
        RunCtx k Γ H cs -> WCalls v cs -> j < length cs -> a < j -> In a (wdix j) ->
        dprec (evs Γ) (S (2 * a)) (2 * j).
      Proof.
        intros Hc [_ Hw] Hj Ha Hn.
        destruct (nth_error cs j) as [c |] eqn:Ej; [| apply nth_error_None in Ej; lia].
        destruct (nth_error cs a) as [ca |] eqn:Ea; [| apply nth_error_None in Ea; lia].
        apply (proj2 (dprec_run k Γ H cs (S (2 * a)) (2 * j) Hc)).
        exists j, c. split; [exact Ej |]. left. split; [reflexivity |].
        exists a, ca. split; [exact Ea |]. split; [exact Ha |]. right. split; [reflexivity |].
        rewrite (proj2 (Hw j c Ej)). exact Hn.
      Qed.

      (** The edge from an invocation to its own response. *)
      Lemma wdp_res (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) j : RunCtx k Γ H cs -> j < length cs -> dprec (evs Γ) (2 * j) (S (2 * j)).
      Proof.
        intros Hc Hj. destruct (nth_error cs j) as [c |] eqn:Ej; [| apply nth_error_None in Ej; lia].
        apply (proj2 (dprec_run k Γ H cs (2 * j) (S (2 * j)) Hc)).
        exists j, c. split; [exact Ej |]. right. split; reflexivity.
      Qed.

      (** The nine edges that carry facts are edges of every run context
          long enough. *)
      Lemma kin_edge (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) v n d :
        RunCtx k Γ H cs -> WCalls v cs -> n < length Γ ->
        (n = 1 /\ d = 0) \/ (n = 2 /\ d = 1) \/ (n = 4 /\ d = 2) \/ (n = 6 /\ d = 4) \/
        (n = 8 /\ d = 4) \/ (n = 10 /\ d = 6) \/ (n = 10 /\ d = 8) \/ (n = 12 /\ d = 10) \/ (n = 13 /\ d = 12) ->
        dprec (evs Γ) d n.
      Proof.
        intros Hc Hw Hn Hnd. pose proof (runctx_len k Γ H cs Hc) as Hl.
        destruct Hnd as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]]]]]].
        - exact (wdp_res Γ H cs 0 Hc ltac:(lia)).
        - exact (wdp_dix Γ H cs v 0 1 Hc Hw ltac:(lia) ltac:(lia) ltac:(cbn; auto)).
        - exact (wdp_inv Γ H cs v 1 2 Hc Hw ltac:(lia) ltac:(lia) ltac:(nsi v)).
        - exact (wdp_inv Γ H cs v 2 3 Hc Hw ltac:(lia) ltac:(lia) ltac:(nsi v)).
        - exact (wdp_inv Γ H cs v 2 4 Hc Hw ltac:(lia) ltac:(lia) ltac:(nsi v)).
        - exact (wdp_inv Γ H cs v 3 5 Hc Hw ltac:(lia) ltac:(lia) ltac:(nsi v)).
        - exact (wdp_inv Γ H cs v 4 5 Hc Hw ltac:(lia) ltac:(lia) ltac:(nsi v)).
        - exact (wdp_inv Γ H cs v 5 6 Hc Hw ltac:(lia) ltac:(lia) ltac:(nsi v)).
        - exact (wdp_res Γ H cs 6 Hc ltac:(lia)).
      Qed.

      (** The order facts the derivation uses: the first call, its
          response and the linearization point precede every later slot;
          the invocations before the last write of [Sq_i] precede it; the
          last write precedes its response. *)
      Lemma wbefore (Γ : list (Slot VE VF)) (H : FutureStore ES) (cs : list (RCall ES)) v b :
        RunCtx k Γ H cs -> WCalls v cs -> b < length Γ ->
        before (evs Γ) 0 b /\ (2 <= b -> before (evs Γ) 1 b /\ before (evs Γ) 2 b) /\
        (b = 12 -> before (evs Γ) 4 b /\ before (evs Γ) 6 b /\ before (evs Γ) 8 b /\ before (evs Γ) 10 b) /\
        (b = 13 -> before (evs Γ) 12 b).
      Proof.
        intros Hc Hw Hb. pose proof (runctx_len k Γ H cs Hc) as Hl. pose proof (proj1 Hw) as H7.
        assert (I0 : forall a j, j < length cs -> a < j -> ~ sindep rc (wop v a) (wop v j) -> dprec (evs Γ) (2 * a) (2 * j))
          by (intros a j; exact (wdp_inv Γ H cs v a j Hc Hw)).
        assert (R0 : forall j, j < length cs -> dprec (evs Γ) (2 * j) (S (2 * j))) by (intros j; exact (wdp_res Γ H cs j Hc)).
        assert (B4 : 4 < length Γ -> before (evs Γ) 2 4) by (intros; apply before_dprec; exact (I0 1 2 ltac:(lia) ltac:(lia) ltac:(nsi v))).
        assert (B10 : 10 < length Γ -> before (evs Γ) 2 10) by (intros; apply before_dprec; exact (I0 1 5 ltac:(lia) ltac:(lia) ltac:(nsi v))).
        assert (B12 : 12 < length Γ -> before (evs Γ) 2 12) by (intros; apply before_dprec; exact (I0 1 6 ltac:(lia) ltac:(lia) ltac:(nsi v))).
        assert (B2 : forall b, 2 <= b -> b < length Γ -> before (evs Γ) 2 b).
        { intros b' H2 Hb'.
          destruct b' as [|[|[|[|[|[|[|[|[|[|[|[|[|[| b']]]]]]]]]]]]]]; try lia.
          - apply before_refl.
          - apply before_dprec. exact (R0 1 ltac:(lia)).
          - exact (B4 ltac:(lia)).
          - apply (before_step _ _ 4); [exact (B4 ltac:(lia)) | exact (R0 2 ltac:(lia))].
          - apply (before_step _ _ 4); [exact (B4 ltac:(lia)) | exact (I0 2 3 ltac:(lia) ltac:(lia) ltac:(nsi v))].
          - apply (before_step _ _ 6); [| exact (R0 3 ltac:(lia))].
            apply (before_step _ _ 4); [exact (B4 ltac:(lia)) | exact (I0 2 3 ltac:(lia) ltac:(lia) ltac:(nsi v))].
          - apply (before_step _ _ 4); [exact (B4 ltac:(lia)) | exact (I0 2 4 ltac:(lia) ltac:(lia) ltac:(nsi v))].
          - apply (before_step _ _ 8); [| exact (R0 4 ltac:(lia))].
            apply (before_step _ _ 4); [exact (B4 ltac:(lia)) | exact (I0 2 4 ltac:(lia) ltac:(lia) ltac:(nsi v))].
          - exact (B10 ltac:(lia)).
          - apply (before_step _ _ 10); [exact (B10 ltac:(lia)) | exact (R0 5 ltac:(lia))].
          - exact (B12 ltac:(lia)).
          - apply (before_step _ _ 12); [exact (B12 ltac:(lia)) | exact (R0 6 ltac:(lia))]. }
        split; [| split; [| split]].
        - destruct b as [| [| b]]; [apply before_refl | apply before_dprec; exact (R0 0 ltac:(lia)) |].
          apply (before_trans _ 0 2); [apply before_dprec; exact (I0 0 1 ltac:(lia) ltac:(lia) ltac:(nsi v)) | apply B2; lia].
        - intros H2. split; [| apply B2; lia].
          apply (before_trans _ 1 2); [apply before_dprec; exact (wdp_dix Γ H cs v 0 1 Hc Hw ltac:(lia) ltac:(lia) ltac:(cbn; auto)) |].
          apply B2; lia.
        - intros ->. split; [| split; [| split]].
          + apply before_dprec. exact (I0 2 6 ltac:(lia) ltac:(lia) ltac:(nsi v)).
          + apply (before_step _ _ 10); [apply before_dprec; exact (I0 3 5 ltac:(lia) ltac:(lia) ltac:(nsi v)) |].
            exact (I0 5 6 ltac:(lia) ltac:(lia) ltac:(nsi v)).
          + apply (before_step _ _ 10); [apply before_dprec; exact (I0 4 5 ltac:(lia) ltac:(lia) ltac:(nsi v)) |].
            exact (I0 5 6 ltac:(lia) ltac:(lia) ltac:(nsi v)).
          + apply before_dprec. exact (I0 5 6 ltac:(lia) ltac:(lia) ltac:(nsi v)).
        - intros ->. apply before_dprec. exact (R0 6 ltac:(lia)).
      Qed.

      (** ** Part 4. The slots, and one lemma for every [NewSlotOK]

          Positions: call [c] (0..6) has its invocation slot at [2 c]
          and its response slot at [2 c + 1].  The slot at position [j]
          is [wslot v hu0 j ev]: start [wstart j], in-edges [win], post
          [wpost], guarantee [wguar j]; [v] is the value read by call 0,
          [hu0] its handle. *)

      Definition wka (v hu0 : nat) (x : WK) : Assn VE VF :=
        match x with
        | WKT => fun _ => True
        | WK1 => A1 hu0
        | WK2 => A2 v
        | WKW bx by_ => AW v bx by_
        | WKL => KLin
        end.

      Definition wstart (j : nat) : Assn VE VF := match j with 0 => WStart | _ => fun _ => True end.
      Definition win (v hu0 j d : nat) : Assn VE VF := wka v hu0 (kin j d).
      Definition wpost (v hu0 j : nat) : Assn VE VF := wka v hu0 (kpost j).

      (** The linearization point (position 2) and the last write of
          [Sq_i] (position 12) guarantee [Gsl k]; every other slot [GF]. *)
      Definition wguar (j : nat) : PRel VE VF := if Nat.eqb j 2 || Nat.eqb j 12 then GS k else GF.

      Definition wslot (v hu0 j : nat) (ev : TaggedEvent ES) : Slot VE VF :=
        mkSlot ev (wstart j) (win v hu0 j) (wpost v hu0 j) (wguar j).

      (** Every slot of [Γ] is the canonical one for its position. *)
      Definition SlotsOK (v hu0 : nat) (Γ : list (Slot VE VF)) : Prop :=
        forall j sj, nth_error Γ j = Some sj -> sj = wslot v hu0 j (sl_ev sj).

      Lemma wka_stable_r v hu0 x : Stable IS (RS k) (wka v hu0 x).
      Proof.
        destruct x; cbn [wka]; [apply Stable_true | apply a1_stable_r | apply a2_stable_r | apply aw_stable_r | apply klin_stable_r].
      Qed.

      Lemma wka_stable_f v hu0 x : Stable IS GF (wka v hu0 x).
      Proof.
        destruct x; cbn [wka]; [apply Stable_true | apply a1_stable_f | apply a2_stable_f | apply aw_stable_f | apply klin_stable_f].
      Qed.

      Lemma wguar_gs j s s' : wguar j s s' -> GS k s s'.
      Proof. unfold wguar. destruct (Nat.eqb j 2 || Nat.eqb j 12); [exact (fun H => H) | exact (fun H => proj1 H)]. Qed.

      Lemma wguar_cases j : wguar j = GF \/ ((j = 2 \/ j = 12) /\ wguar j = GS k).
      Proof.
        unfold wguar. destruct (Nat.eqb_spec j 2) as [-> | H2]; [right; split; [left; reflexivity | reflexivity] |].
        destruct (Nat.eqb_spec j 12) as [-> | H12]; [right; split; [right; reflexivity | reflexivity] | left; reflexivity].
      Qed.

      Lemma wstart_est j : Impl IS Pinit (wstart j).
      Proof.
        destruct j as [| j]; [| intros s _ _; exact Logic.I].
        intros s _ Hp. destruct (pinit_facts rc si tw wt h wop0 s Hp) as [Hl (evs & HΩ & Hg)].
        split; [exact Hl |]. exists evs. split; [exact HΩ | exact Hg].
      Qed.

      Lemma wstart_stable j : Stable IS (RS k) (wstart j).
      Proof. destruct j as [| j]; [exact wstart_stable_r | apply Stable_true]. Qed.

      Lemma kin_shape n d :
        (n = 1 /\ d = 0) \/ (n = 2 /\ d = 1) \/ (n = 4 /\ d = 2) \/ (n = 6 /\ d = 4) \/
        (n = 8 /\ d = 4) \/ (n = 10 /\ d = 6) \/ (n = 10 /\ d = 8) \/ (n = 12 /\ d = 10) \/ (n = 13 /\ d = 12) ->
        (d < 2 /\ n <= 2) \/ (2 <= d /\ d < n /\ (n = 13 -> d = 12)).
      Proof. intros H. repeat destruct H as [H | H]; destruct H as [-> ->]; lia. Qed.

      (** The generic slot lemma: a slot [wslot v hu0 (length Γ) ev]
          appended to a context of canonical slots satisfies [NewSlotOK],
          given its event update from the conjunction of its start and all
          its in-edges.  [Γx] is any run context of the writer that
          extends [Γ ++ [sl]]: the order facts are read off it
          ([wbefore], [kin_edge]).  The own-event interference premises
          ([ns_if_*]) hold because every assertion is [GF]-stable, and the
          two [Gsl] slots (the linearization point and the last write of
          [Sq_i]) and the [WStart] start are separated from every
          assertion they would break by the order ([wbefore]). *)
      Lemma wnew v hu0 (Γ : list (Slot VE VF)) (ev : TaggedEvent ES) (Γx : list (Slot VE VF)) (Hx : FutureStore ES)
          (csx : list (RCall ES)) (rest : list (Slot VE VF)) :
        RunCtx k Γx Hx csx -> WCalls v csx -> Γx = (Γ ++ [wslot v hu0 (length Γ) ev]) ++ rest ->
        SlotsOK v hu0 Γ ->
        EvUpdate IS (wguar (length Γ)) k (untag ev)
          (fun s => wstart (length Γ) s /\ forall d, win v hu0 (length Γ) d s) (wpost v hu0 (length Γ)) ->
        NewSlotOK IS RS GS k Pinit Γ (wslot v hu0 (length Γ) ev).
      Proof.
        intros Hc Hw HΓx Hok Hupd.
        assert (Hlx : length Γ < length Γx) by (rewrite HΓx, !length_app; cbn; lia).
        assert (Hlen : length Γx <= 14) by (rewrite (runctx_len k _ _ _ Hc); pose proof (proj1 Hw); lia).
        assert (Hbx : forall a b, b <= length Γ -> before (evs Γx) a b -> before (evs (Γ ++ [wslot v hu0 (length Γ) ev])) a b).
        { intros a b Hb Hbf. rewrite HΓx, evs_app in Hbf.
          apply (before_app_iff (evs (Γ ++ [wslot v hu0 (length Γ) ev])) (evs rest) a b) in Hbf;
            [exact Hbf | rewrite length_evs, length_app; cbn; lia]. }
        assert (Hbo : forall a b, b < length Γ -> before (evs Γx) a b -> before (evs Γ) a b).
        { intros a b Hb Hbf. apply Hbx in Hbf; [| lia]. rewrite evs_app in Hbf.
          apply (before_app_iff (evs Γ) (evs [wslot v hu0 (length Γ) ev]) a b) in Hbf; [exact Hbf | rewrite length_evs; exact Hb]. }
        assert (Hdx : forall a b, b <= length Γ -> dprec (evs Γx) a b -> dprec (evs (Γ ++ [wslot v hu0 (length Γ) ev])) a b).
        { intros a b Hb Hd. rewrite HΓx, evs_app in Hd.
          apply (dprec_app_iff (evs (Γ ++ [wslot v hu0 (length Γ) ev])) (evs rest) a b) in Hd;
            [exact Hd | rewrite length_evs, length_app; cbn; lia]. }
        assert (Hslot : forall j sj, nth_error Γ j = Some sj ->
                          sl_start sj = wstart j /\ sl_in sj = win v hu0 j /\ sl_post sj = wpost v hu0 j /\
                          sl_guar sj = wguar j).
        { intros j sj Hj. rewrite (Hok j sj Hj). cbn. auto. }
        assert (Hjn : forall j sj, nth_error Γ j = Some sj -> j < length Γ)
          by (intros j sj Hj; apply nth_error_Some; rewrite Hj; discriminate).
        destruct (wbefore Γx Hx csx v (length Γ) Hc Hw Hlx) as (B0 & B12 & B4 & _).
        constructor; cbn [wslot sl_ev sl_start sl_in sl_post sl_guar].
        - intros s s' Hg. exact (wguar_gs _ s s' Hg).
        - intros σ p γ γ' [Hst Hin] HI Hge σ' Hs. apply (Hupd σ p γ γ'); [| exact HI | exact Hge | exact Hs].
          split; [exact Hst |]. intros d. unfold win. destruct (kin_cases (length Γ) d) as [E | Hnd];
            [rewrite E; exact Logic.I |].
          apply Hin. apply Hdx; [lia |]. exact (kin_edge Γx Hx csx v (length Γ) d Hc Hw Hlx Hnd).
        - apply wstart_est.
        - intros d sd _ Hsd s _ Hp. destruct (Hslot d sd Hsd) as (_ & _ & Hpo & _). rewrite Hpo in Hp.
          unfold win, wpost in *. destruct (kin_post (length Γ) d) as [E | E]; rewrite E; [exact Logic.I | exact Hp].
        - apply wstart_stable.
        - intros d _. apply wka_stable_r.
        - intros g sg Hg. destruct Γ as [| x Γ']; [destruct g; discriminate Hg |]. apply Stable_true.
        - intros d g sg Hd Hg Hnb. destruct (Hslot g sg Hg) as (_ & _ & _ & ->). unfold win.
          destruct (kin_cases (length Γ) d) as [E | Hnd]; [rewrite E; apply Stable_true |].
          destruct (wguar_cases g) as [-> | [Hg212 ->]]; [apply wka_stable_f |].
          exfalso. apply Hnb. pose proof (Hjn g sg Hg) as Hgn.
          destruct (kin_shape _ _ Hnd) as [(Hd2 & Hn2) | (Hd2 & Hdn & H13)]; [lia |].
          destruct Hg212 as [-> | ->].
          + apply Hbo; [exact Hdn |]. destruct (wbefore Γx Hx csx v d Hc Hw ltac:(lia)) as (_ & Hb2 & _).
            exact (proj2 (Hb2 Hd2)).
          + rewrite (H13 ltac:(lia)). apply before_refl.
        - intros y sy Hy Hnb. destruct (Hslot y sy Hy) as (-> & _). destruct y as [| y]; [| apply Stable_true].
          exfalso. apply Hnb. apply Hbx; [lia | exact B0].
        - intros y sy d Hy Hnb Hd. destruct (Hslot y sy Hy) as (_ & -> & _). unfold win.
          destruct (kin_cases y d) as [E | Hyd]; [rewrite E; apply Stable_true |].
          destruct (wguar_cases (length Γ)) as [-> | [Hn212 ->]]; [apply wka_stable_f |].
          exfalso. apply Hnb. apply Hbx; [lia |]. pose proof (Hjn y sy Hy) as Hyn.
          destruct Hyd as [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [[-> ->] | [-> ->]]]]]]]]];
            try lia.
          + exact (proj1 (B12 ltac:(lia))).
          + exact (proj2 (B12 ltac:(lia))).
          + exact (proj1 (B4 ltac:(lia))).
          + exact (proj1 (proj2 (B4 ltac:(lia)))).
          + exact (proj1 (proj2 (proj2 (B4 ltac:(lia))))).
          + exact (proj2 (proj2 (proj2 (B4 ltac:(lia))))).
          + exact (proj2 (proj2 (proj2 (B4 ltac:(lia))))).
      Qed.

      (** ** Part 5. The event updates ([ns_update]), one per kind of slot *)

      Lemma IE_inj t1 t2 h1 h2 o1 o2 : IE rc t1 h1 o1 = IE rc t2 h2 o2 -> t1 = t2 /\ h1 = h2 /\ o1 = o2.
      Proof. unfold IE. intros E. injection E as E1 E2 E3. auto. Qed.

      Lemma in_rm (g1 g2 : Ghost ES FS) x e : In e (g1 ++ x :: g2) -> e <> x -> In e (g1 ++ g2).
      Proof.
        intros He Hne. apply in_app_or in He as [He | [He | He]]; apply in_or_app; [left; exact He | | right; exact He].
        exfalso. exact (Hne (eq_sym He)).
      Qed.

      (** [AW], unfolded. *)
      Lemma aw_inv v bx by_ s :
        AW v bx by_ s ->
        exists A Pf P, ps_poss s = POk (A, Pf) P /\ lin_lookup k (@ls_lini FS wop0) P /\
          In (@RelaxedTraceLin.Build_Op FS k wop0 tt) Pf /\ Holder rc si i k P (ps_ghost s) /\
          rg s (Sq i) = v + 1 /\ (bx = true -> rg s (Sx i) = vx) /\ (by_ = true -> rg s (Sy i) = vy) /\
          A i = (vx, vy) /\ Nat.even v = true.
      Proof.
        intros ((A & Pf & P & Hp & Hl & Hr) & (A' & Pf' & P' & Hp' & Hh & Hq & Hx & Hy & Ha) & Ev).
        rewrite Hp in Hp'. injection Hp' as <- <- <-. exists A, Pf, P. auto 10.
      Qed.

      Lemma aw_intro v bx by_ s A Pf P :
        ps_poss s = POk (A, Pf) P -> lin_lookup k (@ls_lini FS wop0) P ->
        In (@RelaxedTraceLin.Build_Op FS k wop0 tt) Pf -> Holder rc si i k P (ps_ghost s) ->
        rg s (Sq i) = v + 1 -> (bx = true -> rg s (Sx i) = vx) -> (by_ = true -> rg s (Sy i) = vy) ->
        A i = (vx, vy) -> Nat.even v = true -> AW v bx by_ s.
      Proof.
        intros Hp Hl Hr Hh Hq Hx Hy Ha Ev. split; [exists A, Pf, P; auto |]. split; [| exact Ev].
        exists A, Pf, P. split; [exact Hp |]. split; [exact Hh |]. auto.
      Qed.

      (** After the linearization point [k] is no longer at [ls_inv]. *)
      Lemma lini_not_inv (P : LinPool FS) :
        lin_pool_well_formed P -> lin_lookup k (@ls_lini FS wop0) P -> ~ lin_lookup k (@ls_inv FS wop0) P.
      Proof.
        intros Hwf Hl Hi. pose proof (RelaxedHoareInherit.lookup_unique_gen P k _ _ Hwf Hl Hi) as E. discriminate E.
      Qed.

      Lemma lini_hasop (P : LinPool FS) : lin_lookup k (@ls_lini FS wop0) P -> HasOp si k wop0 P.
      Proof. intros Hl. exists (@ls_lini FS wop0). split; [exact Hl | reflexivity]. Qed.

      (** The [GF] step of an emission or a response that keeps the
          abstract state and does not remove a write of [Sq_i]. *)
      Lemma gf_intro (σ σ' : State VE) p (γ γ' : Ghost ES FS) :
        GS k (σ, p, γ) (σ', p, γ') -> incl γ' γ ->
        (forall e, In e γ -> se_owner e = k -> isWrSq i (gop rc si e) -> In e γ') ->
        fst (fst σ') (Sq i) = fst (fst σ) (Sq i) ->
        (fst (fst σ') (Sx i) = fst (fst σ) (Sx i) \/ fst (fst σ') (Sx i) = vx) ->
        (fst (fst σ') (Sy i) = fst (fst σ) (Sy i) \/ fst (fst σ') (Sy i) = vy) ->
        GF (σ, p, γ) (σ', p, γ').
      Proof. intros HG Hi Hk Hq Hx Hy. split; [exact HG |]. split; [reflexivity |]. auto. Qed.

      (** The emission keeps every other entry. *)
      Lemma keep_other (g1 g2 : Ghost ES FS) x :
        ~ isWrSq i (gop rc si x) ->
        forall e, In e (g1 ++ x :: g2) -> se_owner e = k -> isWrSq i (gop rc si e) -> In e (g1 ++ g2).
      Proof. intros Hx e He _ Hq. apply (in_rm g1 g2 x e He). intros ->. exact (Hx Hq). Qed.

      (** Of two distinct entries, an emission removes at most one. *)
      Lemma two_rm (g1 g2 : Ghost ES FS) x e1 e2 :
        e1 <> e2 -> In e1 (g1 ++ x :: g2) -> In e2 (g1 ++ x :: g2) -> In e1 (g1 ++ g2) \/ In e2 (g1 ++ g2).
      Proof.
        intros Hne H1 H2. apply in_app_or in H1 as [H1 | [H1 | H1]]; [left; apply in_or_app; left; exact H1 | | left; apply in_or_app; right; exact H1].
        right. apply in_app_or in H2 as [H2 | [H2 | H2]]; [apply in_or_app; left; exact H2 | | apply in_or_app; right; exact H2].
        exfalso. apply Hne. rewrite <- H1, <- H2. reflexivity.
      Qed.

      (** *** Call 0, [rd Sq_i]: the start facts give the holder, the
          value of the record and [RecNB]. *)
      Lemma upd0 hu0 (P : Assn VE VF) :
        (forall s, P s -> WStart s) -> EvUpdate IS GF k (IE rc wt hu0 (sRd (Sq i))) P (A1 hu0).
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hst.
        destruct (HP _ Hpre) as ((A & Pf & P0 & Hp & Hl) & evs & (_ & v0 & h0 & h1 & h2 & h3 & h4 & h5 & h6 & Hnd & ->) & Hgh).
        cbn [ps_poss ps_ghost ps_mem fst snd] in Hp, Hgh. subst p.
        pose proof HI as (A' & Pf' & P' & Hp' & Hru & HC). cbn in Hp'. injection Hp' as <- <- <-.
        cbn [regs ps_mem ps_ghost fst snd] in Hru, HC.
        pose proof Hge as Hge0. destruct (ghost_emit_ie rc si k wt hu0 (sRd (Sq i)) γ γ' Hge0) as (g1 & g2 & Hγ & Hγ' & _).
        subst γ γ'.
        pose proof (ic_gnd _ _ _ _ _ _ _ _ HC) as Hgnd.
        assert (Hx : In (Build_ScheduledEvent k (IE rc wt hu0 (sRd (Sq i)))) (g1 ++ Build_ScheduledEvent k (IE rc wt hu0 (sRd (Sq i))) :: g2))
          by (apply in_or_app; right; left; reflexivity).
        assert (Hxn : ~ In (Build_ScheduledEvent k (IE rc wt hu0 (sRd (Sq i)))) (g1 ++ g2)) by exact (NoDup_remove_2 _ _ _ Hgnd).
        assert (Hin7 : forall hj o, In (IE rc wt hj o) [IE rc wt h0 (sRd (Sq i)); IE rc wt h1 (sWr (Sq i) (v0 + 1)); IE rc wt h2 sWmb;
                                     IE rc wt h3 (sWr (Sx i) vx); IE rc wt h4 (sWr (Sy i) vy); IE rc wt h5 sWmb;
                                     IE rc wt h6 (sWr (Sq i) (v0 + 2))] ->
                          In (Build_ScheduledEvent k (IE rc wt hj o)) (g1 ++ Build_ScheduledEvent k (IE rc wt hu0 (sRd (Sq i))) :: g2)).
        { intros hj o Hin. apply (Hgh (Build_ScheduledEvent k (IE rc wt hj o)) eq_refl). exists (IE rc wt hj o). split; [exact Hin | reflexivity]. }
        (* the handle of the emitted read is h0 *)
        assert (Eh0 : hu0 = h0).
        { destruct (proj1 (Hgh (Build_ScheduledEvent k (IE rc wt hu0 (sRd (Sq i)))) eq_refl) Hx) as (ev' & Hev' & Hxe). injection Hxe as Hxe. subst ev'.
          destruct Hev' as [E | [E | [E | [E | [E | [E | [E | []]]]]]]]; apply IE_inj in E as (_ & E1 & E2);
            first [exact (eq_sym E1) | discriminate E2]. }
        subst hu0.
        (* the read is the only read of [k] *)
        assert (Hrd : forall e, In e (g1 ++ Build_ScheduledEvent k (IE rc wt h0 (sRd (Sq i))) :: g2) -> se_owner e = k ->
                        isRdSq i (gop rc si e) -> e = Build_ScheduledEvent k (IE rc wt h0 (sRd (Sq i)))).
        { intros e He Ho Hq. destruct (proj1 (Hgh e Ho) He) as (ev & Hev & ->). unfold isRdSq, gop in Hq.
          destruct Hev as [<- | [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]]; cbn in Hq; first [reflexivity | discriminate Hq]. }
        assert (Hne : forall hj o, o <> sRd (Sq i) ->
                        Build_ScheduledEvent k (IE rc wt hj o) <> Build_ScheduledEvent k (IE rc wt h0 (sRd (Sq i)))).
        { intros hj o Ho E. apply (f_equal (gop rc si)) in E. cbn in E. exact (Ho E). }
        assert (Hw1 : In (Build_ScheduledEvent k (IE rc wt h1 (sWr (Sq i) (v0 + 1)))) (g1 ++ g2)).
        { apply (in_rm g1 g2 _ _ (Hin7 h1 (sWr (Sq i) (v0 + 1)) ltac:(cbn; tauto))). apply Hne. discriminate. }
        assert (Hw6 : In (Build_ScheduledEvent k (IE rc wt h6 (sWr (Sq i) (v0 + 2)))) (g1 ++ g2)).
        { apply (in_rm g1 g2 _ _ (Hin7 h6 (sWr (Sq i) (v0 + 2)) ltac:(cbn; tauto))). apply Hne. discriminate. }
        assert (Hwm : In (Build_ScheduledEvent k (IE rc wt h2 sWmb)) (g1 ++ g2)).
        { apply (in_rm g1 g2 _ _ (Hin7 h2 sWmb ltac:(cbn; tauto))). apply Hne. discriminate. }
        assert (Hnrd : ~ Owns rc si k (isRdSq i) (g1 ++ g2)).
        { intros (e & He & Ho & Hq). apply Hxn. rewrite <- (Hrd e (incl_remove_mid rc si g1 g2 _ e He) Ho Hq). exact He. }
        assert (Hcoup : forall ls, lin_lookup k ls P0 -> Coup rc si k ls (g1 ++ g2)).
        { intros ls Hls. rewrite (RelaxedHoareInherit.lookup_unique_gen P0 k _ _ (ic_wf _ _ _ _ _ _ _ _ HC) Hls Hl).
          unfold Coup. cbn. intros _. split.
          - exists (Build_ScheduledEvent k (IE rc wt h2 sWmb)). split; [exact Hwm | split; reflexivity].
          - exists (Build_ScheduledEvent k (IE rc wt h1 (sWr (Sq i) (v0 + 1)))). split; [exact Hw1 | split; reflexivity]. }
        destruct (isl_inv_noreg rc si tw k wt h0 (sRd (Sq i)) σ σ' A Pf P0 _ _ HI Hge Hst (fun l w E => ltac:(discriminate E)) Hcoup)
          as [HI' HG].
        destruct (read_inv_mine rc wt h0 (Sq i) σ σ' Hru Hst) as [Hregs Hmine].
        exists (POk (A, Pf) P0). split; [apply rt_refl |]. split; [| split; [exact HI' |]].
        - exists (fst (fst σ) (Sq i)). split; [exact Hmine |]. split; [| split; [| split]].
          + exists A, Pf, P0. split; [reflexivity |]. split.
            * split; [exists vx, vy, (@ls_inv FS wop0); split; [exact Hl | reflexivity] |]. split; [exact Hnrd |].
              exists (Build_ScheduledEvent k (IE rc wt h1 (sWr (Sq i) (v0 + 1)))). split; [exact Hw1 |].
              split; [reflexivity | exists (v0 + 1); reflexivity].
            * unfold regs. cbn [ps_mem fst]. rewrite Hregs. reflexivity.
          + exists A, Pf, P0. split; [reflexivity | exact Hl].
          + exists (Build_ScheduledEvent k (IE rc wt h1 (sWr (Sq i) (v0 + 1)))),
              (Build_ScheduledEvent k (IE rc wt h6 (sWr (Sq i) (v0 + 2)))).
            split; [intros E; apply (f_equal (gop rc si)) in E; cbn in E; injection E as E; lia |].
            split; [exact Hw1 |]. split; [exact Hw6 |]. split; [reflexivity |]. split; [reflexivity |].
            split; [exists (v0 + 1); reflexivity | exists (v0 + 2); reflexivity].
          + exists A, Pf, P0. split; [reflexivity |].
            exact (proj2 (recnb_establish P0 k (IE rc wt h0 (sRd (Sq i))) _ _ (ic_age _ _ _ _ _ _ _ _ HC) Logic.I Hge)).
        - apply gf_intro; [exact HG | apply incl_remove_mid | | rewrite Hregs; reflexivity | left; rewrite Hregs; reflexivity |
                           left; rewrite Hregs; reflexivity].
          apply keep_other. intros (w & Hw). discriminate Hw.
      Qed.

      (** *** Call 0, its response: the record identifies the value [v]
          read with [Sq_i] ([eihl_mine_res]). *)
      Lemma upd1 hu0 v (P : Assn VE VF) :
        (forall s, P s -> A1 hu0 s) ->
        EvUpdate IS GF k (Build_ThreadEvent wt (@ResEv ES hu0 (sRd (Sq i)) v)) P (A2 v).
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hst. cbn in Hge. subst γ'.
        destruct (HP _ Hpre) as (w & Hm & Hh & Hl & H2 & Hn).
        pose proof (eihl_mine_res (E := ES) δS (wt, hu0) _ (sRd (Sq i)) v σ σ' Hm Hst) as E.
        apply rd_rec_inj in E. subst w.
        destruct (isl_response rc si tw k wt hu0 (sRd (Sq i)) v σ σ' p γ HI Hst) as [HI' HG].
        pose proof (step_res rc σ σ' wt hu0 (sRd (Sq i)) v Hst) as Hregs.
        exists p. split; [apply rt_refl |]. split; [| split; [exact HI' |]].
        - split; [| split; [exact Hl | split; [exact H2 | exists hu0; exact Hn]]].
          destruct Hh as (A & Pf & P0 & Hp & Hh & Hq). exists A, Pf, P0. split; [exact Hp |]. split; [exact Hh |].
          unfold regs in *. cbn [ps_mem fst] in *. rewrite Hregs. exact Hq.
        - apply gf_intro; [exact HG | intros x Hx; exact Hx | intros e He _ _; exact He | rewrite Hregs; reflexivity |
                           left; rewrite Hregs; reflexivity | left; rewrite Hregs; reflexivity].
      Qed.

      (** *** Call 1, [wr Sq_i (v+1)]: the linearization point
          ([isl_wr_lp]; readiness by [ready_write]: direct blocks and the
          [RecNB] of call 0). *)
      Lemma upd2 v hu (P : Assn VE VF) :
        (forall s, P s -> A2 v s) ->
        EvUpdate IS (GS k) k (IE rc wt hu (sWr (Sq i) (v + 1))) P (AW v false false).
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hst.
        destruct (HP _ Hpre) as ((A & Pf & P0 & Hp & Hh & Hq) & (A1' & Pf1 & P1 & Hp1 & Hl) & H2 & h0 & (A2' & Pf2 & P2 & Hp2 & Hrec)).
        cbn [ps_poss ps_ghost ps_mem fst snd] in *. subst p.
        injection Hp1 as <- <- <-. injection Hp2 as <- <- <-.
        pose proof HI as (A' & Pf' & P' & Hp' & Hru & HC). cbn in Hp'. injection Hp' as <- <- <-.
        cbn [regs ps_mem ps_ghost fst snd] in Hru, HC, Hq.
        pose proof Hge as Hge0. destruct (ghost_emit_ie rc si k wt hu (sWr (Sq i) (v + 1)) γ γ' Hge0) as (g1 & g2 & Hγ & Hγ' & _).
        assert (Hown : Owns rc si k (isWrSq i) γ').
        { destruct H2 as (e1 & e2 & Hne & He1 & He2 & Ho1 & Ho2 & Hq1 & Hq2). cbn in He1, He2. subst γ γ'.
          destruct (two_rm g1 g2 _ e1 e2 Hne He1 He2) as [E1 | E2]; [exists e1 | exists e2]; auto. }
        destruct (isl_wr_lp rc si tw wt h i vx vy v h0 hu σ σ' A Pf P0 γ γ' HI Hl Hh Hq Hge Hst Hrec Hown)
          as (P' & Hu & Hps & HI' & HG).
        pose proof (lin_invoke_update_is_update _ _ _ _ _ Hu) as Hu2.
        assert (Hev : Nat.even v = true).
        { rewrite <- Hq. exact (holder_inv_even _ _ _ _ _ _ _ _ HC i k vx vy Hh Hl). }
        exists (POk (Aupd A i (vx, vy), @RelaxedTraceLin.Build_Op FS k wop0 tt :: Pf) P').
        split; [exact Hps |]. split; [| split; [exact HI' | exact HG]].
        apply (aw_intro v false false _ (Aupd A i (vx, vy)) (@RelaxedTraceLin.Build_Op FS k wop0 tt :: Pf) P'); cbn [ps_poss ps_ghost ps_mem fst snd];
          [reflexivity | exact (lin_update_target _ _ _ _ _ Hu2) | left; reflexivity | | | discriminate | discriminate |
           apply aupd_same | exact Hev].
        - split; [exists vx, vy, (@ls_lini FS wop0); split; [exact (lin_update_target _ _ _ _ _ Hu2) | reflexivity] |].
          split; [| exact Hown]. subst γ γ'. intros H. apply (proj1 (proj2 Hh)). exact (owns_incl rc si k _ _ _ (incl_remove_mid rc si g1 g2 _) H).
        - unfold regs. cbn [ps_mem fst]. rewrite (step_ie_wr rc σ σ' wt hu (Sq i) (v + 1) Hst). apply upd_sq_same.
      Qed.

      (** *** The responses of calls 1-6: nothing changes but the
          underlay record (memory is unchanged). *)
      Lemma upd_res hu o (r : sar o) (P X : Assn VE VF) :
        (forall σ p γ σ', P (σ, p, γ) -> X (σ', p, γ)) ->
        EvUpdate IS GF k (Build_ThreadEvent wt (@ResEv ES hu o r)) P X.
      Proof.
        intros HX σ p γ γ' Hpre HI Hge σ' Hst. cbn in Hge. subst γ'.
        destruct (isl_response rc si tw k wt hu o r σ σ' p γ HI Hst) as [HI' HG].
        pose proof (step_res rc σ σ' wt hu o r Hst) as Hregs.
        exists p. split; [apply rt_refl |]. split; [exact (HX σ p γ σ' Hpre) |]. split; [exact HI' |].
        apply gf_intro; [exact HG | intros x Hx; exact Hx | intros e He _ _; exact He | rewrite Hregs; reflexivity |
                         left; rewrite Hregs; reflexivity | left; rewrite Hregs; reflexivity].
      Qed.

      (** *** Calls 2 and 5, [wmb] after the linearization point
          ([isl_inv_noreg]; the coupling of a linearized write is free). *)
      Lemma upd_wmb v hu bx by_ (P : Assn VE VF) :
        (forall s, P s -> AW v bx by_ s) -> EvUpdate IS GF k (IE rc wt hu sWmb) P (AW v bx by_).
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hst.
        destruct (aw_inv v bx by_ _ (HP _ Hpre)) as (A & Pf & P0 & Hp & Hl & Hr & Hh & Hq & Hx & Hy & Ha & Ev).
        cbn [ps_poss ps_ghost ps_mem fst snd] in *. subst p.
        pose proof HI as (A' & Pf' & P' & Hp' & Hru & HC). cbn in Hp'. injection Hp' as <- <- <-.
        cbn [regs ps_mem ps_ghost fst snd] in Hru, HC.
        pose proof (ic_wf _ _ _ _ _ _ _ _ HC) as Hwf.
        destruct (isl_inv_noreg rc si tw k wt hu sWmb σ σ' A Pf P0 γ γ' HI Hge Hst (fun l w E => ltac:(discriminate E))
                    (coup_lin_write rc si k i vx vy P0 γ' Hwf (lini_hasop P0 Hl) (lini_not_inv P0 Hwf Hl))) as [HI' HG].
        pose proof (step_ie_regs rc σ σ' wt hu sWmb Hst (fun l w E => ltac:(discriminate E))) as Hregs.
        pose proof Hge as Hge0. destruct (ghost_emit_ie rc si k wt hu sWmb γ γ' Hge0) as (g1 & g2 & Hγ & Hγ' & _). subst γ γ'.
        exists (POk (A, Pf) P0). split; [apply rt_refl |]. split; [| split; [exact HI' |]].
        - apply (aw_intro v bx by_ _ A Pf P0); cbn [ps_poss ps_ghost ps_mem fst snd]; try assumption; [reflexivity | | | |].
          + apply (holder_emit rc si i k P0 g1 g2 _ Hh). intros [_ (w & Hw)]. discriminate Hw.
          + unfold regs in *. cbn [ps_mem fst] in *. rewrite Hregs. exact Hq.
          + unfold regs in *. cbn [ps_mem fst] in *. rewrite Hregs. exact Hx.
          + unfold regs in *. cbn [ps_mem fst] in *. rewrite Hregs. exact Hy.
        - apply gf_intro; [exact HG | apply incl_remove_mid | | rewrite Hregs; reflexivity | left; rewrite Hregs; reflexivity |
                           left; rewrite Hregs; reflexivity].
          apply keep_other. intros (w & Hw). discriminate Hw.
      Qed.

      (** *** Calls 3 and 4, the data writes ([isl_wr_data]; [Sq_i] is odd
          after the linearization point). *)
      Lemma upd_data v hu l w bx by_ bx' by' (P : Assn VE VF) :
        (forall s, P s -> AW v bx by_ s) ->
        (l = Sx i /\ w = vx /\ bx' = true /\ by' = by_) \/ (l = Sy i /\ w = vy /\ bx' = bx /\ by' = true) ->
        EvUpdate IS GF k (IE rc wt hu (sWr l w)) P (AW v bx' by').
      Proof.
        intros HP Hlw σ p γ γ' Hpre HI Hge σ' Hst.
        destruct (aw_inv v bx by_ _ (HP _ Hpre)) as (A & Pf & P0 & Hp & Hl & Hr & Hh & Hq & Hx & Hy & Ha & Ev).
        cbn [ps_poss ps_ghost ps_mem fst snd] in *. subst p.
        pose proof HI as (A' & Pf' & P' & Hp' & Hru & HC). cbn in Hp'. injection Hp' as <- <- <-.
        cbn [regs ps_mem ps_ghost fst snd] in Hru, HC.
        pose proof (ic_wf _ _ _ _ _ _ _ _ HC) as Hwf.
        unfold regs in Hq, Hx, Hy. cbn [ps_mem fst] in Hq, Hx, Hy.
        assert (Hodd : Nat.even (fst (fst σ) (Sq i)) = false).
        { rewrite Hq, Nat.add_1_r, Nat.even_succ, <- Nat.negb_even, Ev. reflexivity. }
        assert (Hl' : l = Sx i \/ l = Sy i) by (destruct Hlw as [(-> & _) | (-> & _)]; auto).
        assert (Hlq : l <> Sq i) by (destruct Hl' as [-> | ->]; discriminate).
        destruct (isl_wr_data rc si tw wt h i vx vy l w hu σ σ' A Pf P0 γ γ' HI (lini_hasop P0 Hl) (lini_not_inv P0 Hwf Hl)
                    Hh Hodd Hl' Hge Hst) as [HI' HG].
        pose proof (step_ie_wr rc σ σ' wt hu l w Hst) as Hregs.
        pose proof Hge as Hge0. destruct (ghost_emit_ie rc si k wt hu (sWr l w) γ γ' Hge0) as (g1 & g2 & Hγ & Hγ' & _). subst γ γ'.
        assert (Hnw : ~ isWrSq i (gop rc si (Build_ScheduledEvent k (IE rc wt hu (sWr l w))))).
        { intros (w' & Hw'). cbn in Hw'. injection Hw' as E _. exact (Hlq E). }
        exists (POk (A, Pf) P0). split; [apply rt_refl |]. split; [| split; [exact HI' |]].
        - apply (aw_intro v bx' by' _ A Pf P0); cbn [ps_poss ps_ghost ps_mem fst snd]; try assumption; [reflexivity | | | |].
          + apply (holder_emit rc si i k P0 g1 g2 _ Hh). intros [_ Hw']. exact (Hnw Hw').
          + unfold regs. cbn [ps_mem fst]. rewrite Hregs. rewrite (upd_neq_q _ _ i w Hlq). exact Hq.
          + unfold regs. cbn [ps_mem fst]. rewrite Hregs. intros Hb.
            destruct Hlw as [(-> & -> & _ & _) | (-> & -> & -> & _)]; [apply upd_eq |].
            rewrite (upd_neq_x (fst (fst σ)) (Sy i) i vy ltac:(discriminate)). exact (Hx Hb).
          + unfold regs. cbn [ps_mem fst]. rewrite Hregs. intros Hb.
            destruct Hlw as [(-> & -> & _ & ->) | (-> & -> & _ & _)]; [| apply upd_eq].
            rewrite (upd_neq_y (fst (fst σ)) (Sx i) i vx ltac:(discriminate)). exact (Hy Hb).
        - apply gf_intro; [exact HG | apply incl_remove_mid | apply keep_other; exact Hnw | | |];
            rewrite Hregs.
          + exact (upd_neq_q _ _ i w Hlq).
          + destruct Hlw as [(-> & -> & _) | (-> & _)]; [right; apply upd_eq | left; apply (upd_neq_x _ (Sy i)); discriminate].
          + destruct Hlw as [(-> & _) | (-> & -> & _)]; [left; apply (upd_neq_y _ (Sx i)); discriminate | right; apply upd_eq].
      Qed.

      (** *** Call 6, [wr Sq_i (v+2)] ([isl_wr_end]). *)
      Lemma upd6 v hu (P : Assn VE VF) :
        (forall s, P s -> AW v true true s) -> EvUpdate IS (GS k) k (IE rc wt hu (sWr (Sq i) (v + 2))) P KLin.
      Proof.
        intros HP σ p γ γ' Hpre HI Hge σ' Hst.
        destruct (aw_inv v true true _ (HP _ Hpre)) as (A & Pf & P0 & Hp & Hl & Hr & Hh & Hq & Hx & Hy & Ha & Ev).
        cbn [ps_poss ps_ghost ps_mem fst snd] in *. subst p.
        pose proof HI as (A' & Pf' & P' & Hp' & Hru & HC). cbn in Hp'. injection Hp' as <- <- <-.
        cbn [regs ps_mem ps_ghost fst snd] in Hru, HC.
        pose proof (ic_wf _ _ _ _ _ _ _ _ HC) as Hwf.
        unfold regs in Hq, Hx, Hy. cbn [ps_mem fst] in Hq, Hx, Hy.
        destruct (isl_wr_end rc si tw wt h i vx vy v hu σ σ' A Pf P0 γ γ' HI (lini_hasop P0 Hl) (lini_not_inv P0 Hwf Hl)
                    Hh Hq Ev (Hx eq_refl) (Hy eq_refl) Ha Hge Hst) as [HI' HG].
        exists (POk (A, Pf) P0). split; [apply rt_refl |]. split; [| split; [exact HI' | exact HG]].
        exists A, Pf, P0. auto.
      Qed.

      (** ** Part 6. The machine invariant and the steps of [rp_run] *)

      (** After [n] calls of the writer whose call 0 returned [v]: the calls
          are the first [n] calls of [wnext], and every slot is canonical. *)
      Definition WInvAt (v n : nat) (cs : list (RCall ES)) (Γ : list (Slot VE VF)) : Prop :=
        length cs = n /\ WCalls v cs /\ exists hu0, SlotsOK v hu0 Γ.

      (** The machine invariant of [rp_run] (for the overlay handle [h]). *)
      Definition winv (st : WSt) (cs : list (RCall ES)) (Γ : list (Slot VE VF)) (H : FutureStore ES) : Prop :=
        match st with
        | W0 => cs = [] /\ Γ = []
        | W1 v => WInvAt v 1 cs Γ
        | W2 v => WInvAt v 2 cs Γ
        | W3 v => WInvAt v 3 cs Γ
        | W4 v => WInvAt v 4 cs Γ
        | W5 v => WInvAt v 5 cs Γ
        | W6 v => WInvAt v 6 cs Γ
        | WD => exists v, WInvAt v 7 cs Γ
        end.

      (** The machine state after call [n] (1..6). *)
      Definition wnxt (v n : nat) : WSt :=
        match n with 1 => W2 v | 2 => W3 v | 3 => W4 v | 4 => W5 v | 5 => W6 v | _ => WD end.

      Lemma winv_next v n cs Γ H : 1 <= n <= 6 -> WInvAt v (S n) cs Γ -> winv (wnxt v n) cs Γ H.
      Proof.
        intros Hn Hi. destruct n as [| [| [| [| [| [| [| n]]]]]]]; try lia; cbn [winv wnxt]; try exact Hi.
        exists v. exact Hi.
      Qed.

      (** The slots of call [n] (invocation and response). *)
      Definition wsi (v hu0 n : nat) (cs : list (RCall ES)) (H : FutureStore ES) (hu : nat) : Slot VE VF :=
        wslot v hu0 (2 * n) (invD_tev (E := ES) k H (dep_of (map rc_h cs) (wdix n)) hu (wop v n)).

      Definition wsr (v hu0 n hu : nat) (r : sar (wop v n)) : Slot VE VF :=
        wslot v hu0 (S (2 * n)) (res_tev (E := ES) k hu (wop v n) r).

      Definition sar_inh (o : SOp) : sar o := match o with sRd _ => 0 | _ => tt end.

      Lemma wnew_at v hu0 (Γ : list (Slot VE VF)) p (ev : TaggedEvent ES) (Γx : list (Slot VE VF)) (Hx : FutureStore ES)
          (csx : list (RCall ES)) (rest : list (Slot VE VF)) :
        p = length Γ ->
        RunCtx k Γx Hx csx -> WCalls v csx -> Γx = (Γ ++ [wslot v hu0 p ev]) ++ rest ->
        SlotsOK v hu0 Γ ->
        EvUpdate IS (wguar p) k (untag ev) (fun s => wstart p s /\ forall d, win v hu0 p d s) (wpost v hu0 p) ->
        NewSlotOK IS RS GS k Pinit Γ (wslot v hu0 p ev).
      Proof. intros ->. apply wnew. Qed.

      Lemma slotsok_snoc v hu0 (Γ : list (Slot VE VF)) p ev :
        SlotsOK v hu0 Γ -> p = length Γ -> SlotsOK v hu0 (Γ ++ [wslot v hu0 p ev]).
      Proof.
        intros Hok -> j sj Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [(_ & Hj') | (-> & ->)];
          [exact (Hok j sj Hj') | reflexivity].
      Qed.

      Lemma wcalls_snoc v n (cs : list (RCall ES)) (hu : nat) :
        length cs = n -> n <= 6 -> WCalls v cs -> WCalls v (cs ++ [@mkRCall ES hu (wop v n) (wdix n)]).
      Proof.
        intros Hl Hn [_ Hw]. split; [rewrite length_app; cbn; lia |].
        intros j c Hj. destruct (nth_error_snoc_cases _ _ _ _ Hj) as [(_ & Hj') | (-> & ->)]; [exact (Hw j c Hj') |].
        rewrite Hl. split; reflexivity.
      Qed.

      Lemma aw_merge v s : AW v true false s -> AW v false true s -> AW v true true s.
      Proof.
        intros H1 H2. destruct (aw_inv v true false s H1) as (A & Pf & P & Hp & Hl & Hr & Hh & Hq & Hx & _ & Ha & Ev).
        destruct (aw_inv v false true s H2) as (A' & Pf' & P' & Hp' & _ & _ & _ & _ & _ & Hy & _ & _).
        apply (aw_intro v true true s A Pf P Hp Hl Hr Hh Hq Hx Hy Ha Ev).
      Qed.

      (** Calls 1-6 ([n]): one lemma, the event update chosen by [n]. *)
      Lemma wcall v hu0 n cs Γ H :
        1 <= n <= 6 -> RunCtx k Γ H cs -> length cs = n -> WCalls v cs -> SlotsOK v hu0 Γ ->
        RunCallOK IS RS GS k Pinit winv cs Γ H (wop v n) (wdix n) (fun _ => wnxt v n) (wsi v hu0 n cs H) (wsr v hu0 n).
      Proof.
        intros Hn Hc Hl Hw Hok. pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        assert (Hctx : forall hu (r : sar (wop v n)), handle_fresh hu H ->
                  RunCtx k ((Γ ++ [wsi v hu0 n cs H hu]) ++ [wsr v hu0 n hu r]) (Build_FutureEntry hu (@Resolved ES (wop v n) r) :: H)
                    (cs ++ [@mkRCall ES hu (wop v n) (wdix n)])).
        { intros hu r Hf. apply (runctx_snoc k Γ H cs _ _ hu (wop v n) (wdix n) r _ Hc Hf); [reflexivity | reflexivity |].
          apply resolve_here. }
        assert (Hok' : forall hu, SlotsOK v hu0 (Γ ++ [wsi v hu0 n cs H hu])) by (intros hu; apply slotsok_snoc; [exact Hok | lia]).
        split; [| split; [| split; [| split]]].
        - intros hu. reflexivity.
        - intros hu Hf. unfold wsi.
          apply (wnew_at v hu0 Γ (2 * n) _ _ _ _ [wsr v hu0 n hu (sar_inh (wop v n))] ltac:(lia) (Hctx hu _ Hf)
                   (wcalls_snoc v n cs hu Hl ltac:(lia) Hw) eq_refl Hok).
          destruct n as [| [| [| [| [| [| [| n]]]]]]]; try lia.
          + apply (upd2 v hu). intros s Hs. exact (proj2 Hs 1).
          + apply (upd_wmb v hu false false). intros s Hs. exact (proj2 Hs 2).
          + apply (upd_data v hu (Sx i) vx false false true false); [intros s Hs; exact (proj2 Hs 4) |].
            left. auto.
          + apply (upd_data v hu (Sy i) vy false false false true); [intros s Hs; exact (proj2 Hs 4) |].
            right. auto.
          + apply (upd_wmb v hu true true). intros s Hs. exact (aw_merge v s (proj2 Hs 6) (proj2 Hs 8)).
          + apply (upd6 v hu). intros s Hs. exact (proj2 Hs 10).
        - intros hu r. reflexivity.
        - intros hu r Hf. unfold wsr.
          apply (wnew_at v hu0 (Γ ++ [wsi v hu0 n cs H hu]) (S (2 * n)) _ _ _ _ [] ltac:(rewrite length_app; cbn; lia)
                   (Hctx hu r Hf) (wcalls_snoc v n cs hu Hl ltac:(lia) Hw) ltac:(rewrite app_nil_r; reflexivity) (Hok' hu)).
          destruct n as [| [| [| [| [| [| [| n]]]]]]]; try lia;
            apply upd_res; [intros; exact Logic.I .. | intros σ p γ σ' Hs; exact (proj2 Hs 12)].
        - intros hu r H' _ _ _. apply winv_next; [exact Hn |].
          split; [rewrite length_app, Hl; cbn; lia |]. split; [exact (wcalls_snoc v n cs hu Hl ltac:(lia) Hw) |].
          exists hu0. apply slotsok_snoc; [exact (Hok' hu) | rewrite length_app; cbn; lia].
      Qed.

      (** Call 0, [rd Sq_i]: the value [r] it returns becomes the [v] of the
          machine state, and its handle the [hu0] of the slots. *)
      Definition wsi0 (H : FutureStore ES) (cs : list (RCall ES)) (hu : nat) : Slot VE VF :=
        wslot 0 hu 0 (invD_tev (E := ES) k H (dep_of (map rc_h cs) []) hu (sRd (Sq i))).

      Definition wsr0 (hu : nat) (r : sar (sRd (Sq i))) : Slot VE VF :=
        wslot r hu 1 (res_tev (E := ES) k hu (sRd (Sq i)) r).

      Lemma wcall0 cs Γ H :
        RunCtx k Γ H cs -> cs = [] -> Γ = [] ->
        RunCallOK IS RS GS k Pinit winv cs Γ H (sRd (Sq i)) [] (fun r => W1 r) (wsi0 H cs) wsr0.
      Proof.
        intros Hc -> ->.
        assert (Hctx : forall hu (r : sar (sRd (Sq i))), handle_fresh hu H ->
                  RunCtx k (([] ++ [wsi0 H [] hu]) ++ [wsr0 hu r]) (Build_FutureEntry hu (@Resolved ES (sRd (Sq i)) r) :: H)
                    ([] ++ [@mkRCall ES hu (sRd (Sq i)) []])).
        { intros hu r Hf. apply (runctx_snoc k [] H [] _ _ hu (sRd (Sq i)) [] r _ Hc Hf); [reflexivity | reflexivity |].
          apply resolve_here. }
        assert (Hw : forall r hu, WCalls r ([] ++ [@mkRCall ES hu (sRd (Sq i)) []]))
          by (intros r hu; apply (wcalls_snoc r 0 [] hu); [reflexivity | lia | split; [cbn; lia | intros j c Hj; destruct j; discriminate Hj]]).
        assert (Hok : forall r hu, SlotsOK r hu [wsi0 H [] hu]).
        { intros r hu j sj Hj. destruct j as [| j]; [| destruct j; discriminate Hj]. injection Hj as <-. reflexivity. }
        split; [| split; [| split; [| split]]].
        - intros hu. reflexivity.
        - intros hu Hf. unfold wsi0.
          apply (wnew_at 0 hu [] 0 _ _ _ _ [wsr0 hu 0] eq_refl (Hctx hu 0 Hf) (Hw 0 hu) eq_refl
                   (fun j sj Hj => ltac:(destruct j; discriminate Hj))).
          apply (upd0 hu). intros s Hs. exact (proj1 Hs).
        - intros hu r. reflexivity.
        - intros hu r Hf. unfold wsr0.
          apply (wnew_at r hu [wsi0 H [] hu] 1 _ _ _ _ [] eq_refl (Hctx hu r Hf) (Hw r hu) eq_refl (Hok r hu)).
          apply (upd1 hu r). intros s Hs. exact (proj2 Hs 0).
        - intros hu r H' _ _ _. cbn [winv]. split; [reflexivity |]. split; [exact (Hw r hu) |].
          exists hu. apply slotsok_snoc; [exact (Hok r hu) | reflexivity].
      Qed.

      (** The return: the response of the last write of [Sq_i] carries
          [KLin], hence [Qsl]; the footprint is the seven invocations. *)
      Lemma wclose v hu0 cs Γ H :
        RunCtx k Γ H cs -> length cs = 7 -> WCalls v cs -> SlotsOK v hu0 Γ ->
        Close IS RS GS k Pinit (fun r => Qsl rc si k wop0 r) tt Γ H /\ Osl rc tw wt wop0 h (own_invs Γ).
      Proof.
        intros Hc Hl Hw Hok. pose proof (runctx_len k Γ H cs Hc) as HlΓ.
        destruct (runctx_store k Γ H cs Hc) as (_ & Hall & Hnd).
        split.
        - apply (close_done IS RS GS k Pinit (fun r => Qsl rc si k wop0 r) tt Γ H
                   (fun d => if Nat.eqb d 13 then KLin else fun _ => True) (fun _ => True) Hall).
          constructor.
          + intros d sd Hd s _ Hp. rewrite (Hok d sd Hd) in Hp. cbn [wslot sl_post] in Hp.
            destruct (Nat.eqb_spec d 13) as [-> | _]; [exact Hp | exact Logic.I].
          + intros s _ _. exact Logic.I.
          + intros d g sg Hd Hg Hnb. destruct (Nat.eqb_spec d 13) as [-> | _]; [| apply Stable_true].
            rewrite (Hok g sg Hg). cbn [wslot sl_guar]. destruct (wguar_cases g) as [-> | [Hg212 ->]]; [exact klin_stable_f |].
            exfalso. apply Hnb. destruct (wbefore Γ H cs v 13 Hc Hw ltac:(lia)) as (_ & B12 & _ & B13).
            destruct Hg212 as [-> | ->]; [exact (proj2 (B12 ltac:(lia))) | exact (B13 eq_refl)].
          + intros g sg _. apply Stable_true.
          + intros d. destruct (Nat.eqb d 13); [exact klin_stable_r | apply Stable_true].
          + apply Stable_true.
          + intros s _ _ Hfin.
            destruct (nth_error cs 6) as [c6 |] eqn:E6; [| apply nth_error_None in E6; lia].
            destruct (runctx_res_at k Γ H cs 6 c6 Hc E6) as (sr & r & Hsr & Hev).
            pose proof (Hfin 13 sr Hsr ltac:(unfold is_response; rewrite Hev; exact Logic.I)) as Hk. cbn in Hk.
            destruct Hk as (A & Pf & P & Hp & Hli & Hr). exists A, Pf, P. split; [exact Hp |]. right. auto.
        - rewrite (own_invs_run k Γ H cs Hc). destruct Hw as [_ Hw].
          destruct cs as [| c0 [| c1 [| c2 [| c3 [| c4 [| c5 [| c6 [| c7 cs]]]]]]]]; cbn in Hl; try lia.
          cbn [map] in Hnd |- *.
          rewrite (proj1 (Hw 0 c0 eq_refl)), (proj1 (Hw 1 c1 eq_refl)), (proj1 (Hw 2 c2 eq_refl)), (proj1 (Hw 3 c3 eq_refl)),
            (proj1 (Hw 4 c4 eq_refl)), (proj1 (Hw 5 c5 eq_refl)), (proj1 (Hw 6 c6 eq_refl)).
          split; [reflexivity |].
          exists v, (rc_h c0), (rc_h c1), (rc_h c2), (rc_h c3), (rc_h c4), (rc_h c5), (rc_h c6). split; [exact Hnd | reflexivity].
      Qed.

      (** Every machine step satisfies [RunStepOK]. *)
      Lemma wstep_ok st cs Γ H :
        RunCtx k Γ H cs -> winv st cs Γ H ->
        RunStepOK IS RS GS k Pinit winv
          (fun a Γ' H' => Close IS RS GS k Pinit (fun r => Qsl rc si k wop0 r) a Γ' H' /\ Osl rc tw wt wop0 h (own_invs Γ'))
          cs Γ H (wnext i vx vy st).
      Proof.
        intros Hc Hi. destruct st as [| v | v | v | v | v | v |]; cbn [winv] in Hi; cbn [wnext RunStepOK].
        - destruct Hi as [-> ->]. exists (wsi0 H []), wsr0. exact (wcall0 [] [] H Hc eq_refl eq_refl).
        - destruct Hi as (Hl & Hw & hu0 & Hok). exists (wsi v hu0 1 cs H), (wsr v hu0 1). exact (wcall v hu0 1 cs Γ H ltac:(lia) Hc Hl Hw Hok).
        - destruct Hi as (Hl & Hw & hu0 & Hok). exists (wsi v hu0 2 cs H), (wsr v hu0 2). exact (wcall v hu0 2 cs Γ H ltac:(lia) Hc Hl Hw Hok).
        - destruct Hi as (Hl & Hw & hu0 & Hok). exists (wsi v hu0 3 cs H), (wsr v hu0 3). exact (wcall v hu0 3 cs Γ H ltac:(lia) Hc Hl Hw Hok).
        - destruct Hi as (Hl & Hw & hu0 & Hok). exists (wsi v hu0 4 cs H), (wsr v hu0 4). exact (wcall v hu0 4 cs Γ H ltac:(lia) Hc Hl Hw Hok).
        - destruct Hi as (Hl & Hw & hu0 & Hok). exists (wsi v hu0 5 cs H), (wsr v hu0 5). exact (wcall v hu0 5 cs Γ H ltac:(lia) Hc Hl Hw Hok).
        - destruct Hi as (Hl & Hw & hu0 & Hok). exists (wsi v hu0 6 cs H), (wsr v hu0 6). exact (wcall v hu0 6 cs Γ H ltac:(lia) Hc Hl Hw Hok).
        - destruct Hi as (v & Hl & Hw & hu0 & Hok). exact (wclose v hu0 cs Γ H Hc Hl Hw Hok).
      Qed.
    End Call.

    (** ** Part 7. The derivation, and its lift to [EIhlv] *)

    (** The write of [fW i vx vy] by its writer [tw i]: a syntactic
        derivation through [sl2_write_run_provable] (hence
        [run_method_provable], [rp_run], [RProvable_coind]), over
        [VE := EIhl δS], with the frozen [Isl], [Rsl], [Gsl], [Osl] and the
        postcondition [Qsl]. *)
    Theorem write_provable :
      MethodProvable IS RS GS (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl rc tw (tw i) (fW i vx vy) h)
        (fun h r => Qsl rc si (tw i, h) (fW i vx vy) r).
    Proof.
      apply (sl2_write_run_provable rc si tw i vx vy winv).
      - intros h. cbn. split; reflexivity.
      - intros h st cs Γ H Hc Hi. exact (wstep_ok h st cs Γ H Hc Hi).
    Qed.

    (** The same derivation over the history presentation
        [EIhlv δS = Log (EIhl δS)] ([RelaxedHoareLog.methodprovable_lift]
        with [J := LogOK δS]): invariant [liftIV δS δF Isl], rely and
        guarantee [liftGLk Rsl], [liftGLk Gsl], postcondition
        [liftA Qsl]; footprint unchanged.  These are the invariant, rely
        and guarantee of the [Hprov] premise of
        [RelaxedHoareLog.rlhl2_eihlv_of_provable] for [I := Isl],
        [R := Rsl], [G := Gsl] ([write_fits_eihlv]). *)
    Theorem write_provable_v :
      MethodProvable (RelaxedHoareLog.liftIV (E := ES) (F := FS) δS δF IS) (RelaxedHoareLog.liftGLk RS) (RelaxedHoareLog.liftGLk GS)
        (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl rc tw (tw i) (fW i vx vy) h)
        (fun h r => RelaxedHoareLog.liftA (Qsl rc si (tw i, h) (fW i vx vy) r)).
    Proof.
      exact (RelaxedHoareLog.methodprovable_lift (RelaxedHoareLog.LogOK (E := ES) δS) (RelaxedHoareLog.logok_mono (E := ES) δS)
               IS RS GS (M2w rc si tw) (tw i) (fW i vx vy) _ _ write_provable).
    Qed.

    (** A write by a thread other than [tw i] ([div]), lifted. *)
    Theorem write_other_provable_v t :
      t <> tw i ->
      MethodProvable (RelaxedHoareLog.liftIV (E := ES) (F := FS) δS δF IS) (RelaxedHoareLog.liftGLk RS) (RelaxedHoareLog.liftGLk GS)
        (M2w rc si tw) t (fW i vx vy) (fun h => Osl rc tw t (fW i vx vy) h)
        (fun h r => RelaxedHoareLog.liftA (Qsl rc si (t, h) (fW i vx vy) r)).
    Proof.
      intros Hne.
      exact (RelaxedHoareLog.methodprovable_lift (RelaxedHoareLog.LogOK (E := ES) δS) (RelaxedHoareLog.logok_mono (E := ES) δS)
               IS RS GS (M2w rc si tw) t (fW i vx vy) _ _ (sl2_write_other_provable rc si tw t i vx vy Hne)).
    Qed.

    (** Every write, on every thread, in the [∃ Ω Q] shape of the [Hprov]
        premise of [RelaxedHoareLog.rlhl2_eihlv_of_provable]. *)
    Theorem write_fits_eihlv t :
      exists Ω Q, MethodProvable (RelaxedHoareLog.liftIV (E := ES) (F := FS) δS δF IS) (RelaxedHoareLog.liftGLk RS)
                    (RelaxedHoareLog.liftGLk GS) (M2w rc si tw) t (fW i vx vy) Ω Q.
    Proof.
      destruct (Pos.eq_dec t (tw i)) as [-> | Hne].
      - exact (ex_intro _ _ (ex_intro _ _ write_provable_v)).
      - exact (ex_intro _ _ (ex_intro _ _ (write_other_provable_v t Hne))).
    Qed.
  End Write.

  (** A type check of the combination step of task .7: given lifted
      derivations of the reads (the premise; open when this was written,
      task .5), the write derivations of this file and the side fields of
      [RelaxedHoareSL2Inv] (over [EIhl δS]) instantiate
      [RelaxedHoareLog.rlhl2_eihlv_of_provable] for the guarded module
      [M2w rc si tw].  No hypothesis on [si].  The premise is discharged
      by [RelaxedHoareSL2Read.read_provable_v] for every [si ⊇ slRA]
      (that file does not use this lemma; its main theorem is
      [RelaxedHoareSL2Read.sl2_main]). *)
  Theorem rlhl2_v_of_reads rc si tw :
    (forall t i, exists Ω Q,
        MethodProvable (RelaxedHoareLog.liftIV (E := E_S rc) (F := F2 si) δS δF (Isl rc si tw)) (RelaxedHoareLog.liftGLk (Rsl rc si))
          (RelaxedHoareLog.liftGLk (Gsl rc si)) (M2w rc si tw) t (fR i) Ω Q) ->
    RLHL2Hyps (RelaxedHoareLog.liftIV (E := E_S rc) (F := F2 si) δS δF (Isl rc si tw)) (RelaxedHoareLog.liftGLk (Rsl rc si))
      (RelaxedHoareLog.liftGLk (Gsl rc si)) (M2w rc si tw) ((((regs0, []), []), [])) (A0, []).
  Proof.
    intros Hrd.
    apply (RelaxedHoareLog.rlhl2_eihlv_of_provable (E := E_S rc) (F := F2 si) δS δF A0 (Isl rc si tw) (Rsl rc si) (Gsl rc si)
             (M2w rc si tw) regs0).
    - intros t [i vx vy | i]; [exact (write_fits_eihlv rc si tw i vx vy t) | exact (Hrd t i)].
    - intros k k' s s' Hne HG. exact (gsl_rsl rc si k k' s s' Hne HG).
    - exact (invoke_rely rc si tw).
    - exact (return_rely rc si tw).
    - exact (isl_ok rc si tw).
    - exact (isl_init rc si tw).
  Qed.
End RelaxedHoareSL2Write.
