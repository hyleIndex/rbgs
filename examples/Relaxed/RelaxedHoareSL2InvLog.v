(** * RelaxedHoareSL2InvLog: the RLHL SeqLock (WRd writer) over the
      history presentation [EIhlv δS] — RLHL-seqlock task .4v

    Plan: [.rocq-review/tasks/RLHL-seqlock.md], Addendum 3 (author
    decision "option B": the underlay presentation of the method
    derivations and of the main theorem is [EIhlv δS := Log (EIhl δS)]),
    Addendum 2 ("RLHL in full": methods by [MethodProvable] derivations,
    soundness only through [method_sound] and [RLHL2Hyps], no route S, no
    [ren_rlhl2] shortcut); reader evaluation
    [.rocq-review/tasks/RLHL-seqlock-reader-eval.md] §1.3 (B-6), §4, and
    [RLHL-seqlock-reader-eval/eval1.md] §3 (the reader sketch).  Built on
    [RelaxedHoareLog] (the lifting kit), [RelaxedHoareSL2Inv] (the frozen
    [Isl]/[Rsl]/[Gsl]/[Osl]/[Qsl], [Qrd]/[Qop], Part 6-7 kits),
    [RelaxedHoareSL2Prog] (program, [M2w]).  No definition of those files
    is changed; this file only adds.  It proves no method derivation of
    the read or of the write by [tw i] (only the [div] case,
    [sl2_write_other_provable_v]); it states the premises (a), (b) of
    the assembly and the targets.  The derivations are in
    [RelaxedHoareSL2Write] ([write_provable], (b)) and
    [RelaxedHoareSL2Read] ([read_provable_v], (a)); the main theorem is
    [RelaxedHoareSL2Read.sl2_main : sl2rd_prov_target_v], with the
    corollaries [RelaxedHoareSL2Read.sl2_complin] and [sl2_rel_lin].

    ** Part 1: the frozen definitions over [EIhlv]
    Proof state [((((m, U), used), log), PossOk (A, Pf) P, γ)].
    - [IslV := liftIV δS δF Isl] ([Isl] on the base part and
      [RelaxedHoareLog.LogOK] on the lifted memory), [RslV := liftGLk Rsl],
      [GslV := liftGLk Gsl] (the base relation on the base parts, and the
      memory moves by [Log] steps), [QslV]/[QrdV]/[QopV := liftA Qsl/Qrd/Qop].
      These are exactly the combinators of
      [RelaxedHoareLog.rlhl2_eihlv_of_provable].
    - The footprint [Osl] is a predicate on lists of underlay invocations,
      independent of the presentation; it is reused unchanged.
    - [islV_base], [islV_logok], [islV_intro].

    ** Part 2: side fields and method premises, transferred
    [gslV_rslV] ([h_guar_rely]), [invoke_rely_v], [return_rely_v],
    [isl_ok_v], [isl_init_v] (by [guar_rely_lift], [invoke_rely_lift],
    [return_rely_lift], [ok_lift], [init_lift] from SL2Inv Part 4);
    [isl_postinvoke_v] ([mp_PI], [postinvoke_lift]); [qsl_ret_v],
    [qrd_ret_v], [qop_ret_v] ([mp_ret], [retcond_lift]).

    ** Part 3: entry points over [EIhlv]
    [sl2_method_provable_op_v]; [sl2_read_run_provable_v] (the read
    through [run_method_provable], hence [rp_run]: a machine invariant
    over [rnext i] with [RunStepOK] steps, postcondition
    [QrdV ∧ X] for any [X]); [sl2_write_run_provable_v] (the write by
    [tw i] directly over [EIhlv], postcondition [QslV ∧ X]);
    [sl2_write_lift] (an [EIhl] derivation of the write, lifted by
    [methodprovable_lift]); [sl2_write_other_provable_v] (the [div] case,
    discharged).

    ** Part 4: the assembly and the target over [EIhlv]
    - [sl2rd_rlhl2_v_of_provable]: [∀ t op, ∃ Ω Q, MethodProvable] over
      [EIhlv] with [IslV]/[RslV]/[GslV] gives [RLHL2Hyps] over [EIhlv]
      from [((((regs0, []), []), [])] ([h_sem] by [method_sound] inside
      [rlhl2_eihlv_of_provable]); no hypothesis on [si].
    - The premises of tasks .5 and .6, with exact types (per [rc], [si],
      [tw]): [SL2ReadV] (∀ t i, ∃ X, the read derivation over [EIhlv]
      with footprint [Osl] and postcondition [QrdV ∧ X]); [SL2WriteB]
      (∀ i vx vy, the write derivation by [tw i] over [EIhl], footprint
      [Osl], postcondition [Qsl], as in SL2Inv's
      [sl2rd_prov_target_of_methods_rd]); [SL2WriteV] (the same directly
      over [EIhlv], postcondition [QslV ∧ X]).
      [sl2_provable_v_of_methods(_v)], [sl2rd_rlhl2_v_of_methods(_v)].
    - [sl2rd_prov_target_v] (the derivation-carrying target over
      [EIhlv]); [sl2rd_complin_target] (copy-cat inclusion over the plain
      [EI δS], every trace, complete or not).
      [sl2rd_complin_of_target_v] (via [rlhl_complin_eihlv]),
      [sl2rd_relin_of_target_v] (target ⇒ [RelaxedHoareSL2Prog.sl2rd_relin_target],
      complete traces, via [rlhl_eihlv_rel_lin]).
      [sl2rd_v_of_methods] ((a) [SL2ReadV] and (b) [SL2WriteB] for every
      [si ⊇ slRA] ⇒ the target), [sl2rd_v_of_methods_v] (with (b')
      [SL2WriteV]), [sl2rd_complin_of_methods], [sl2rd_relin_of_methods].

    ** Part 5: the reader-side value kit (for task .5)
    - [sl_logval_rd]: two logged values of one [sRd] key are equal
      (the one-liner anticipated in [RelaxedHoareLog]'s header).
    - [logvalA_stable_lk]: every [LogVal] fact is stable under every
      [liftGLk] relation.  [KRd κ l v] ("the record of underlay key [κ]
      is (or was) [rd l ↦ v]"): [krd_unique]; stable under every lifted relation
      ([krd_stable], [krd_stable_r], [krd_stable_g]); [krd_step];
      established at the read's invocation ([krd_inv]: value = register),
      pinned at the response ([krd_res]: logged value = response value),
      logged by the response itself ([krd_res_logged]).
    - Value edges (eval1 §3): [EdgeG i κG] (out-edge of the iteration's
      first [rd Sq_i]: [KRd κG r0 ∧ r0 ≤ Sq_i]); [EdgeD i κG κd l pr]
      (out-edge of a data read: [KRd κG r0 ∧ KRd κd ad ∧ KRdVal i r0 pr ad]);
      [PkgAt]/[Pkg] (the package made at the LP: the three logged values
      [r0], [ax], [cy], the overlay record [Op k (fR i) (vx, vy)] with
      [(vx, vy) = A i] of the LP, the [q = Sq_i] seen at the LP with
      [r0 ≤ q ≤ Sq_i], and [q = r0 → even r0 → (vx, vy) = (ax, cy)]);
      [PkgT] (after the final [rd Sq_i] [κT]: [KRd κT r0'] with [q ≤ r0']).
      Establishment: [edgeG_inv], [edgeD_inv]/[edgeX_inv]/[edgeY_inv]
      ([JEven]), [pkg_lp]/[pkg_lp_ex] (at the LP, with the abstract update
      of [isl_read_lp]; the two [r0] agree by [sl_logval_rd]), [pkgT_inv];
      carried by [edgeG_step], [pkgAt_step], [pkg_step], [pkgT_step].
      Stability: [edgeG_stable(_r/_g)], [edgeD_stable(_r/_g)] (every
      [GslV]); [pkg(At/T)_stable], [pkg_stable_r], [pkg_stable_fix],
      [pkgT_stable_r/_fix/_res]; [krecnbV_stable_r/_g], [krecnb_inv].
    - Own-slot guarantees: [GslFix k] ([Gsl k] keeping the possibility),
      [GslRes k] (also keeping the ghost); [gslfixV_gslV],
      [gslresV_gslV] ([ns_guar]); [isl_response_res],
      [isl_inv_noreg_fix] (SL2Inv Part 7 gives them); base stability
      [krec_stable_fix], [klook_stable_fix], [kseqge_stable_fix],
      [krdval_stable_fix], [kowns_stable_res], [notnoown_stable_res],
      [notnoown_stable_r]; lifted [kownsV_stable_r/_res],
      [notnoownV_stable_r/_res]; [Stable_or_v], [stable_res_of_fix],
      [stable_g_of_fix]; [owns_emit_keep].
    - The identification at the return ([bw_sum]/[Close]):
      [pkgT_vals] (the logged values are the returned ones, [q = r0] is
      even, so the LP record [(vx, vy)] is the returned [(a, c)]),
      [read_value_is_lp_value] ([(a, c)] is the [A i] of the LP),
      [qsl_of_krec], [sl_read_close] ([QslV]), [sl_read_close_rd]
      ([QrdV], with the B-6 escape [¬ NoOwn k]), [sl_read_close_owns].

    ** Part 6: the read's own updates (a check that the kit fits)
    [KHas k o] ([k] is in the pool with operation [o]; [khas_stable_r],
    [khas_stable_fix]); [coup_emit_nonrmb]; [EvUpdate]s over [EIhlv] for
    every own event of an iteration, each from SL2Inv Part 7 and the kit:
    [rd_noreg_update] (generic, guarantee [liftGL (GslFix k)]),
    [rd_G_update] ([EdgeG], [RecNB]), [rd_X_update], [rd_Y_update]
    ([EdgeD]); [rd_rmb_update] (generic [rmb], guarantee [GslV k]: the
    LP by [isl_read_lp] if [k] owns no [rmb] afterwards, else no abstract
    step and [k] still owns an [rmb]; an already linearized read cannot
    emit an [rmb], [krec_rmb_contra]), [rd_rmbA_update],
    [rd_rmbB_update] ([Pkg] at the LP); [rd_T_update]
    ([PkgT ∨ owns an rmb]); [rd_res_update] (generic response,
    guarantee [liftGL (GslRes k)]), [rd_res_krd_update],
    [rd_res_logged_update], [rd_resT_update].

    ** Gaps found in the reader sketch (eval1 §3, reader-eval §4), and how
       the kit closes them (for task .5)
    - G1 (B-6 on the final edge).  The sketch covers only paths whose
      validating iteration is the ghost's last one.  On a path that
      validates earlier than the ghost's footprint, no LP happens; the
      [rmb_b] post must be [Pkg ∨ KOwns k isRmb] ([rd_rmb_update]), the
      final read's post and its response's [fin] [PkgT ∨ KOwns k isRmb]
      ([rd_T_update], [rd_resT_update]); [sl_read_close_rd] then gives
      [QrdV] either way.
    - G2 (guarantees).  [Gsl k] leaves [k]'s own pool entry, records and
      ghost entries unconstrained, so [KRec] (in [Pkg]) and [KOwns]
      are not stable under [GslV k].  For the [fin] of [κT]'s response,
      [bw_if] quantifies over the slots not before it, which are exactly
      the read's response slots (no [dix]: no response→invocation edge;
      every invocation precedes [κT] through the [rmb] chain).  So the
      response slots need a guarantee keeping the possibility *and the
      ghost* ([GslRes]; eval1 obligation (a) mentions only the
      possibility).  [isl_response] gives it.
    - G3 (per-value in-edges).  The response slot of an [rd Sq_i] [κT]
      whose value [v] fails [rok s v] (the path loops) must not carry
      [PkgT ∨ KOwns k isRmb] on its in-edge: a response is before no
      slot, so [ns_if_old_in] would ask that edge to be stable under the
      guarantee of every later own invocation, including a later LP
      (which removes the last [rmb]).  Carry the disjunction only when
      [rok s v = true]; [RunCallOK]'s response slot [sr h v] depends on
      [v], so this is expressible.
    - G4 (the read's phase at an [rmb]).  [isl_read_lp] needs [k] at
      [ls_inv (fR i)]; it follows from [Coup] once [k] is known to be in
      the pool with operation [fR i] ([KHas]).  [KHas] is stable under
      [RslV k] and [GslFix] but not under [GslV k], and start assertions
      must be stable under every own guarantee ([ns_if_new_start]), so
      [KHas] must travel on the invocation-chain edges ([G → A],
      [A → X/Y/B], [X/Y → B], [B → T], [B/T → next G]); in particular
      not on [G → B] or [G → T] (the [rmb]s [A], [B] are not before
      [G] and have guarantee [GslV k]).  Part 6 carries it that way.
    - G5.  The LP also needs [RecNB] of an [rd Sq_i] of the read
      (recorded readiness against an older write of the same instance);
      [krecnb_inv] establishes it at [κG] and it is stable under [RslV]
      and every [GslV].
    - G6 (m-53).  [bw_sum] must locate the four response slots of the
      validating iteration (positions [2 j + 1] of [RunCtx]); the machine
      invariant must record that iteration's handles.  [sl_read_close_rd]
      takes the facts by key, not by position.
    None of these needs a change to the logic, to [RelaxedHoareLog], or
    to the frozen definitions.  The derivation itself (slots, all
    [NewSlotOK] fields, the [RunCtx] invariant, [Close]) is not in this
    file; it is [RelaxedHoareSL2Read] (task .5), whose header records how
    each of G1-G6 is closed.

    ** K / S / P / R
    - K (Print Assumptions, Rocq 9.3.0): 112 of the 116
      [Lemma]/[Theorem]/[Corollary] results are closed under the global
      context.  [sl2rd_complin_of_target_v] and [sl2rd_complin_of_methods]
      use [Classical_Prop.classic] (inherited from
      [RelaxedHoareCompLin.rlhl_complin_ei] through
      [RelaxedHoareLog.rlhl_complin_eihlv]);
      [sl2rd_relin_of_target_v] and [sl2rd_relin_of_methods] use
      [classic] and [Eqdep.Eq_rect_eq.eq_rect_eq] (the latter inherited
      from [RelaxedGSim.gsim_rel_lin] through [cc_rel_lin] and
      [RelaxedHoareLog.rlhl_eihlv_rel_lin]).  No proof here uses an axiom
      directly.
    - S: every statement holds for every [rc], [si], [tw]; the LP lemmas
      ([rd_rmb_update], [rd_rmbB_update], [rd_rmbA_update]) and the
      targets for every [si ⊇ slRA].  The assembly theorems have the
      method derivations as hypotheses: (a) the read over [EIhlv]
      (task .5) and (b) the write by [tw i] (task .6); writes by other
      threads and every side field are discharged here.  So nothing in
      this file is an unconditional correctness result for the SeqLock:
      [sl2rd_complin_of_methods]/[sl2rd_relin_of_methods] are
      conditional on (a) and (b).  (a) and (b) are discharged outside
      this file, by [RelaxedHoareSL2Read.read_provable_v] (for every
      [si ⊇ slRA]) and [RelaxedHoareSL2Write.write_provable]; the
      unconditional results are [RelaxedHoareSL2Read.sl2_main],
      [sl2_complin] and [sl2_rel_lin].  The conclusions are over the plain
      [EI δS] (traces over [EI δS], [EIhl δS], [EIhlv δS] coincide,
      [RelaxedHoareLog.loglift_ei]); [sl2rd_prov_target_v] does not imply
      SL2Prog's [sl2rd_target] (over [EIhl]), which is superseded for the
      main theorem by [sl2rd_complin_target] / [sl2rd_relin_target].
    - P: no SeqLock text in the main paper (plan §1); Appendix/SeqLock.tex
      is a different, TicketLock-based object.  The history presentation
      restores the underlay projection of the paper's proof state [s]
      (Appendix/programlogic.tex:530; :579, rule EStep; :549; lines as
      in async-ccal commit 4a2db8e1, 42 higher than in 01484091); the
      overlay invocations of [s] and the reachability clause of :579 are
      not represented.  implex.tex:3 ("RLHL is complete …") is not
      supported by this file.
    - R: groundwork for popl2027-reviews.md:215 ("No example verified on
      the COH model"); by itself it answers nothing.  With (a) and (b)
      discharged in [RelaxedHoareSL2Read] and [RelaxedHoareSL2Write],
      see [RelaxedHoareSL2Read]'s header for the status of the main
      theorem against that concern.

    ** Limitations
    - The value kit and the Part 6 updates are checked lemma by lemma
      here.  Their composition into a [MethodProvable] derivation of the
      read is [RelaxedHoareSL2Read.read_provable_v] (task .5), which uses
      them unchanged.
    - The underlay is SL2Prog's sequential register file (scope as stated
      there); the overlay specification is effect-at-invocation [EI δF]. *)

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
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.RelaxedHoareSL2Prog.
Require Import examples.Relaxed.RelaxedHoareSL2Inv.

Import ListNotations.

Module RelaxedHoareSL2InvLog.
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

  Section SL2V.
    Context (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid).

    Local Abbreviation ES := (E_S rc).
    Local Abbreviation FS := (F2 si).
    Local Abbreviation VB := (EIhl (E := E_S rc) δS).
    Local Abbreviation V := (EIhlv (E := E_S rc) δS).
    Local Abbreviation VF := (RelaxedHoareSpec.EI (F := F2 si) δF).
    Local Abbreviation POk v pool := (@PossOk FS VF v pool).
    Local Abbreviation OpF := (RelaxedTraceLin.Op FS).
    Local Abbreviation okey := (@RelaxedTraceLin.op_key FS).

    (** ** Part 1. The frozen definitions over [EIhlv δS] *)

    Definition IslV : Assn V VF := liftIV (E := ES) (F := FS) δS δF (Isl rc si tw).
    Definition RslV : CallKey FS -> PRel V VF := liftGLk (Rsl rc si).
    Definition GslV : CallKey FS -> PRel V VF := liftGLk (Gsl rc si).
    Definition QslV (k : CallKey FS) (op : FOp) (r : far op) : Assn V VF := liftA (Qsl rc si k op r).
    Definition QrdV (k : CallKey FS) (i : nat) (r : far (fR i)) : Assn V VF := liftA (Qrd rc si k i r).
    Definition QopV (k : CallKey FS) (op : FOp) (r : far op) : Assn V VF := liftA (Qop rc si k op r).

    Lemma islV_base s : IslV s -> Isl rc si tw (dropS s).
    Proof. intros [H _]. exact H. Qed.

    Lemma islV_logok s : IslV s -> LogOK (E := ES) δS (ps_mem s).
    Proof. intros [_ H]. exact H. Qed.

    Lemma islV_intro s : Isl rc si tw (dropS s) -> LogOK (E := ES) δS (ps_mem s) -> IslV s.
    Proof. intros H1 H2. split; assumption. Qed.

    (** ** Part 2. The fields of [RLHL2Hyps] other than [h_sem], and
        [mp_PI], [mp_ret], over [EIhlv δS] *)

    Theorem gslV_rslV k k' s s' : k <> k' -> GslV k s s' -> RslV k' s s'.
    Proof. exact (guar_rely_lift (Rsl rc si) (Gsl rc si) (gsl_rsl rc si) k k' s s'). Qed.

    Theorem invoke_rely_v k k' op tr ret s p' :
      k <> k' -> program_produces_tagged (fst k) (M2w rc si tw op (fst k)) tr ret -> IslV s ->
      poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
      RslV k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr).
    Proof.
      exact (invoke_rely_lift (LogOK (E := ES) δS) (Isl rc si tw) (Rsl rc si) (M2w rc si tw) (invoke_rely rc si tw)
               k k' op tr ret s p').
    Qed.

    Theorem return_rely_v k k' op r s p2 :
      k <> k' -> IslV s -> poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
      RslV k' s (ps_mem s, p2, ps_ghost s).
    Proof.
      exact (return_rely_lift (LogOK (E := ES) δS) (Isl rc si tw) (Rsl rc si) (return_rely rc si tw) k k' op r s p2).
    Qed.

    Theorem isl_ok_v s : IslV s -> exists v pool, ps_poss s = POk v pool /\ lin_pool_well_formed pool.
    Proof. exact (ok_lift (LogOK (E := ES) δS) (Isl rc si tw) (isl_ok rc si tw) s). Qed.

    Theorem isl_init_v : IslV ((((regs0, []), []), []), POk (A0, []) [], []).
    Proof.
      exact (init_lift (LogOK (E := ES) δS) (Isl rc si tw) ((regs0, []), []) (A0, []) (isl_init rc si tw)
               (logok_init (E := ES) δS regs0)).
    Qed.

    (** [mp_PI]. *)
    Theorem isl_postinvoke_v t h op s : PostInvoke IslV (t, h) op (Osl rc tw t op h) s -> IslV s.
    Proof.
      intros Hs. destruct (postinvoke_lift (LogOK (E := ES) δS) (Isl rc si tw) (t, h) op _ s Hs) as [Hs' HJ].
      exact (islV_intro s (isl_postinvoke rc si tw t h op _ Hs') HJ).
    Qed.

    (** [mp_ret], for the three postconditions. *)
    Theorem qsl_ret_v t h op r s : QslV (t, h) op r s -> IslV s -> NoOwn (t, h) (ps_ghost s) -> RetCond IslV GslV (t, h) op r s.
    Proof.
      intros Hq [HI HJ] Hno. apply (retcond_lift (LogOK (E := ES) δS) (Isl rc si tw) (Gsl rc si) (t, h) op r s HJ).
      exact (qsl_ret rc si tw t h op r (dropS s) Hq HI Hno).
    Qed.

    Theorem qrd_ret_v t h i r s : QrdV (t, h) i r s -> IslV s -> NoOwn (t, h) (ps_ghost s) -> RetCond IslV GslV (t, h) (fR i) r s.
    Proof.
      intros Hq [HI HJ] Hno. apply (retcond_lift (LogOK (E := ES) δS) (Isl rc si tw) (Gsl rc si) (t, h) (fR i) r s HJ).
      exact (qrd_ret rc si tw t h i r (dropS s) Hq HI Hno).
    Qed.

    Theorem qop_ret_v t h op r s : QopV (t, h) op r s -> IslV s -> NoOwn (t, h) (ps_ghost s) -> RetCond IslV GslV (t, h) op r s.
    Proof.
      intros Hq [HI HJ] Hno. apply (retcond_lift (LogOK (E := ES) δS) (Isl rc si tw) (Gsl rc si) (t, h) op r s HJ).
      exact (qop_ret rc si tw t h op r (dropS s) Hq HI Hno).
    Qed.

    (** ** Part 3. Entry points for the derivations over [EIhlv δS] *)

    (** [RelaxedHoareSL2Inv.sl2_method_provable_op] over [EIhlv], with an
        extra conjunct [X] in the postcondition. *)
    Theorem sl2_method_provable_op_v t op (X : handle FS -> far op -> Assn V VF) :
      (forall h, RProvable IslV RslV GslV (t, h) (PostInvoke IslV (t, h) op (Osl rc tw t op h))
         (fun a Γ H => Close IslV RslV GslV (t, h) (PostInvoke IslV (t, h) op (Osl rc tw t op h))
                         (fun r s => QopV (t, h) op r s /\ X h r s) a Γ H /\ Osl rc tw t op h (own_invs Γ))
         [] empty_store (M2w rc si tw op t)) ->
      MethodProvable IslV RslV GslV (M2w rc si tw) t op (fun h => Osl rc tw t op h) (fun h r s => QopV (t, h) op r s /\ X h r s).
    Proof.
      intros Ht. constructor.
      - intros h s Hs. exact (isl_postinvoke_v t h op s Hs).
      - intros h r s [Hq _] HI Hno. exact (qop_ret_v t h op r s Hq HI Hno).
      - exact Ht.
    Qed.

    (** The read through [run_method_provable] (hence [rp_run]) over
        [EIhlv]: the postcondition is the lifted [Qrd] strengthened by an
        arbitrary [X] (e.g. history facts, as [RelaxedHoareLog]'s
        [QlogC]); [mp_PI], [mp_ret] are discharged here. *)
    Theorem sl2_read_run_provable_v t i (X : handle FS -> far (fR i) -> Assn V VF)
        (Inv : handle FS -> RSt -> list (RCall ES) -> list (Slot V VF) -> FutureStore ES -> Prop) :
      (forall h, Inv h RG [] [] empty_store) ->
      (forall h st cs Γ H, RunCtx (t, h) Γ H cs -> Inv h st cs Γ H ->
         RunStepOK IslV RslV GslV (t, h) (PostInvoke IslV (t, h) (fR i) (Osl rc tw t (fR i) h)) (Inv h)
           (fun a Γ' H' => Close IslV RslV GslV (t, h) (PostInvoke IslV (t, h) (fR i) (Osl rc tw t (fR i) h))
                             (fun r s => QrdV (t, h) i r s /\ X h r s) a Γ' H' /\ Osl rc tw t (fR i) h (own_invs Γ'))
           cs Γ H (rnext i st)) ->
      MethodProvable IslV RslV GslV (M2w rc si tw) t (fR i) (fun h => Osl rc tw t (fR i) h)
        (fun h r s => QrdV (t, h) i r s /\ X h r s).
    Proof.
      intros Hi0 Hstep. apply (run_method_provable IslV RslV GslV (M2w rc si tw) t (fR i) _ _ (rnext i) RG Inv).
      - reflexivity.
      - intros h s Hs. exact (isl_postinvoke_v t h (fR i) s Hs).
      - intros h r s [Hq _] HI Hno. exact (qrd_ret_v t h i r s Hq HI Hno).
      - exact Hi0.
      - exact Hstep.
    Qed.

    (** The write by [tw i], directly over [EIhlv] (alternative to lifting
        an [EIhl] derivation, [sl2_write_lift]). *)
    Theorem sl2_write_run_provable_v i vx vy (X : handle FS -> far (fW i vx vy) -> Assn V VF)
        (Inv : handle FS -> WSt -> list (RCall ES) -> list (Slot V VF) -> FutureStore ES -> Prop) :
      (forall h, Inv h W0 [] [] empty_store) ->
      (forall h st cs Γ H, RunCtx (tw i, h) Γ H cs -> Inv h st cs Γ H ->
         RunStepOK IslV RslV GslV (tw i, h) (PostInvoke IslV (tw i, h) (fW i vx vy) (Osl rc tw (tw i) (fW i vx vy) h)) (Inv h)
           (fun a Γ' H' => Close IslV RslV GslV (tw i, h) (PostInvoke IslV (tw i, h) (fW i vx vy) (Osl rc tw (tw i) (fW i vx vy) h))
                             (fun r s => QslV (tw i, h) (fW i vx vy) r s /\ X h r s) a Γ' H' /\
                           Osl rc tw (tw i) (fW i vx vy) h (own_invs Γ'))
           cs Γ H (wnext i vx vy st)) ->
      MethodProvable IslV RslV GslV (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl rc tw (tw i) (fW i vx vy) h)
        (fun h r s => QslV (tw i, h) (fW i vx vy) r s /\ X h r s).
    Proof.
      intros Hi0 Hstep. apply (run_method_provable IslV RslV GslV (M2w rc si tw) (tw i) (fW i vx vy) _ _ (wnext i vx vy) W0 Inv).
      - exact (m2w_write_body rc si tw i vx vy).
      - intros h s Hs. exact (isl_postinvoke_v (tw i) h (fW i vx vy) s Hs).
      - intros h r s [Hq _] HI Hno. exact (qsl_ret_v (tw i) h (fW i vx vy) r s Hq HI Hno).
      - exact Hi0.
      - exact Hstep.
    Qed.

    (** An [EIhl] derivation of the write (task .6 over the base
        presentation, e.g. through [sl2_write_run_provable]) is one over
        [EIhlv] ([RelaxedHoareLog.methodprovable_lift]). *)
    Theorem sl2_write_lift i vx vy :
      MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) (tw i) (fW i vx vy)
        (fun h => Osl rc tw (tw i) (fW i vx vy) h) (fun h r => Qsl rc si (tw i, h) (fW i vx vy) r) ->
      MethodProvable IslV RslV GslV (M2w rc si tw) (tw i) (fW i vx vy)
        (fun h => Osl rc tw (tw i) (fW i vx vy) h) (fun h r => QslV (tw i, h) (fW i vx vy) r).
    Proof.
      intros H. exact (methodprovable_lift (LogOK (E := ES) δS) (logok_mono (E := ES) δS) _ _ _ _ _ _ _ _ H).
    Qed.

    (** A write by a thread other than [tw i] ([div]), over [EIhlv]. *)
    Theorem sl2_write_other_provable_v t i vx vy :
      t <> tw i ->
      MethodProvable IslV RslV GslV (M2w rc si tw) t (fW i vx vy)
        (fun h => Osl rc tw t (fW i vx vy) h) (fun h r => QslV (t, h) (fW i vx vy) r).
    Proof.
      intros Hne. exact (methodprovable_lift (LogOK (E := ES) δS) (logok_mono (E := ES) δS) _ _ _ _ _ _ _ _
                           (sl2_write_other_provable rc si tw t i vx vy Hne)).
    Qed.

    (** ** Part 4. The assembly over [EIhlv δS] *)

    (** Derivations over [EIhlv] of every method (any footprint and
        postcondition per operation, the [∃ Ω Q] shape of
        [rlhl_sound_complin]) give [RLHL2Hyps] over [EIhlv] ([h_sem] by
        [RelaxedHoareSound.method_sound] inside
        [RelaxedHoareLog.rlhl2_eihlv_of_provable]); the other fields are
        SL2Inv's, transferred.  No hypothesis on [si]. *)
    Theorem sl2rd_rlhl2_v_of_provable :
      (forall t op, exists Ω Q, MethodProvable IslV RslV GslV (M2w rc si tw) t op Ω Q) ->
      RLHL2Hyps (VE := V) (VF := VF) IslV RslV GslV (M2w rc si tw) ((((regs0, []), []), [])) (A0, []).
    Proof.
      intros Hprov.
      exact (rlhl2_eihlv_of_provable (E := ES) (F := FS) δS δF A0 (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) regs0
               Hprov (gsl_rsl rc si) (invoke_rely rc si tw) (return_rely rc si tw) (isl_ok rc si tw) (isl_init rc si tw)).
    Qed.

    (** The method premises that tasks .5 and .6 are to provide, with
        their exact types.

        (a) The read, over [EIhlv], on every thread: footprint [Osl],
        postcondition the lifted [Qrd] (B-6) strengthened by any [X]
        chosen per thread and instance (the reader may keep history
        facts in its postcondition). *)
    Definition SL2ReadV : Prop :=
      forall t i, exists X : handle FS -> far (fR i) -> Assn V VF,
        MethodProvable IslV RslV GslV (M2w rc si tw) t (fR i) (fun h => Osl rc tw t (fR i) h)
          (fun h r s => QrdV (t, h) i r s /\ X h r s).

    (** (b) The write by [tw i], over [EIhl] (as in
        [RelaxedHoareSL2Inv.sl2rd_prov_target_of_methods_rd]); lifted by
        [sl2_write_lift]. *)
    Definition SL2WriteB : Prop :=
      forall i vx vy,
        MethodProvable (Isl rc si tw) (Rsl rc si) (Gsl rc si) (M2w rc si tw) (tw i) (fW i vx vy)
          (fun h => Osl rc tw (tw i) (fW i vx vy) h) (fun h r => Qsl rc si (tw i, h) (fW i vx vy) r).

    (** (b') The write by [tw i], directly over [EIhlv]: postcondition the
        lifted [Qsl] strengthened by any [X]. *)
    Definition SL2WriteV : Prop :=
      forall i vx vy, exists X : handle FS -> far (fW i vx vy) -> Assn V VF,
        MethodProvable IslV RslV GslV (M2w rc si tw) (tw i) (fW i vx vy) (fun h => Osl rc tw (tw i) (fW i vx vy) h)
          (fun h r s => QslV (tw i, h) (fW i vx vy) r s /\ X h r s).

    (** All methods from (a) and (b'): writes on a thread other than
        [tw i] are the [div] case. *)
    Theorem sl2_provable_v_of_methods_v :
      SL2ReadV -> SL2WriteV -> forall t op, exists Ω Q, MethodProvable IslV RslV GslV (M2w rc si tw) t op Ω Q.
    Proof.
      intros Hrd Hwr t [i vx vy | i].
      - destruct (Pos.eq_dec t (tw i)) as [-> | Hne].
        + destruct (Hwr i vx vy) as (X & Hm). eexists _, _. exact Hm.
        + eexists _, _. exact (sl2_write_other_provable_v t i vx vy Hne).
      - destruct (Hrd t i) as (X & Hm). eexists _, _. exact Hm.
    Qed.

    (** All methods from (a) and (b). *)
    Theorem sl2_provable_v_of_methods :
      SL2ReadV -> SL2WriteB -> forall t op, exists Ω Q, MethodProvable IslV RslV GslV (M2w rc si tw) t op Ω Q.
    Proof.
      intros Hrd Hwr t [i vx vy | i].
      - destruct (Pos.eq_dec t (tw i)) as [-> | Hne].
        + eexists _, _. exact (sl2_write_lift i vx vy (Hwr i vx vy)).
        + eexists _, _. exact (sl2_write_other_provable_v t i vx vy Hne).
      - destruct (Hrd t i) as (X & Hm). eexists _, _. exact Hm.
    Qed.

    Theorem sl2rd_rlhl2_v_of_methods_v :
      SL2ReadV -> SL2WriteV -> RLHL2Hyps (VE := V) (VF := VF) IslV RslV GslV (M2w rc si tw) ((((regs0, []), []), [])) (A0, []).
    Proof. intros Hrd Hwr. exact (sl2rd_rlhl2_v_of_provable (sl2_provable_v_of_methods_v Hrd Hwr)). Qed.

    Theorem sl2rd_rlhl2_v_of_methods :
      SL2ReadV -> SL2WriteB -> RLHL2Hyps (VE := V) (VF := VF) IslV RslV GslV (M2w rc si tw) ((((regs0, []), []), [])) (A0, []).
    Proof. intros Hrd Hwr. exact (sl2rd_rlhl2_v_of_provable (sl2_provable_v_of_methods Hrd Hwr)). Qed.

  End SL2V.

  (** *** The target over [EIhlv], and its consequences *)

  (** The derivation-carrying target ([RelaxedHoareSL2Inv.sl2rd_prov_target])
      over the history presentation [EIhlv δS := Log (EIhl δS)] (author
      decision option B).  It cannot be met by a direct [MethodSem] proof
      (route S): the first conjunct asks for [MethodProvable] derivations. *)
  Definition sl2rd_prov_target_v : Prop :=
    forall rc si tw, (forall o o', slRA o o' -> si o o') ->
      exists I R G,
        (forall t op, exists Ω Q,
           MethodProvable (VE := EIhlv (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
             I R G (M2w rc si tw) t op Ω Q) /\
        RLHL2Hyps (VE := EIhlv (E := E_S rc) δS) (VF := RelaxedHoareSpec.EI (F := F2 si) δF)
          I R G (M2w rc si tw) ((((regs0, []), []), [])) (A0, []).

  (** Copy-cat inclusion over the plain [EI δS], for every overlay trace
      (complete or not): the paper-facing correctness statement of task .7. *)
  Definition sl2rd_complin_target : Prop :=
    forall rc si tw, (forall o o', slRA o o' -> si o o') ->
      RelaxedHoareCompLin.RCompLin (M2w rc si tw) (RelaxedHoareSpec.EI (F := E_S rc) δS) (regs0, [])
        (RelaxedHoareSpec.EI (F := F2 si) δF) (A0, []).

  (** [RCompLin] (every prefix) from the target, through
      [RelaxedHoareLog.rlhl_complin_eihlv] ([classic], inherited). *)
  Theorem sl2rd_complin_of_target_v : sl2rd_prov_target_v -> sl2rd_complin_target.
  Proof.
    intros H rc si tw Hsi. destruct (H rc si tw Hsi) as (I & R & G & _ & HH).
    exact (rlhl_complin_eihlv (E := E_S rc) (F := F2 si) δS δF A0 I R G (M2w rc si tw) (regs0, []) HH).
  Qed.

  (** [rel_lin] of every complete trace ([RelaxedHoareSL2Prog.sl2rd_relin_target])
      from the target, through [RelaxedHoareLog.rlhl_eihlv_rel_lin]
      ([classic], [eq_rect_eq], inherited). *)
  Theorem sl2rd_relin_of_target_v : sl2rd_prov_target_v -> sl2rd_relin_target.
  Proof.
    intros H rc si tw s Hsi Htr Hc. destruct (H rc si tw Hsi) as (I & R & G & _ & HH).
    exact (rlhl_eihlv_rel_lin (E := E_S rc) (F := F2 si) δS δF A0 I R G (M2w rc si tw) (regs0, []) HH s Htr Hc).
  Qed.

  (** The assembly: from (a) the read derivation over [EIhlv] and (b') the
      write derivation over [EIhlv], the target. *)
  Theorem sl2rd_v_of_methods_v :
    (forall rc si tw, (forall o o', slRA o o' -> si o o') -> SL2ReadV rc si tw /\ SL2WriteV rc si tw) ->
    sl2rd_prov_target_v.
  Proof.
    intros H rc si tw Hsi. destruct (H rc si tw Hsi) as [Hrd Hwr].
    exists (IslV rc si tw), (RslV rc si), (GslV rc si). split.
    - exact (sl2_provable_v_of_methods_v rc si tw Hrd Hwr).
    - exact (sl2rd_rlhl2_v_of_methods_v rc si tw Hrd Hwr).
  Qed.

  (** The assembly: from (a) the read derivation over [EIhlv] and (b) the
      write derivation over [EIhl] (lifted by [methodprovable_lift]), the
      target. *)
  Theorem sl2rd_v_of_methods :
    (forall rc si tw, (forall o o', slRA o o' -> si o o') -> SL2ReadV rc si tw /\ SL2WriteB rc si tw) ->
    sl2rd_prov_target_v.
  Proof.
    intros H rc si tw Hsi. destruct (H rc si tw Hsi) as [Hrd Hwr].
    exists (IslV rc si tw), (RslV rc si), (GslV rc si). split.
    - exact (sl2_provable_v_of_methods rc si tw Hrd Hwr).
    - exact (sl2rd_rlhl2_v_of_methods rc si tw Hrd Hwr).
  Qed.

  Corollary sl2rd_complin_of_methods :
    (forall rc si tw, (forall o o', slRA o o' -> si o o') -> SL2ReadV rc si tw /\ SL2WriteB rc si tw) ->
    sl2rd_complin_target.
  Proof. intros H. exact (sl2rd_complin_of_target_v (sl2rd_v_of_methods H)). Qed.

  Corollary sl2rd_relin_of_methods :
    (forall rc si tw, (forall o o', slRA o o' -> si o o') -> SL2ReadV rc si tw /\ SL2WriteB rc si tw) ->
    sl2rd_relin_target.
  Proof. intros H. exact (sl2rd_relin_of_target_v (sl2rd_v_of_methods H)). Qed.

  (** ** Part 5. The reader-side value kit (for task .5)

      Reader evaluation §4 ("Sufficiency for the reader") and eval1.md §3:
      the four record values of the validating iteration and the abstract
      value at the read's linearization point meet in [bw_sum] at the
      return, linked by facts about the logged value of each underlay key
      ([KRd]), not along dag edges.  The lemmas below are the pieces; the
      derivation itself (slots, machine invariant, [RunCtx] bookkeeping)
      is task .5, [RelaxedHoareSL2Read.read_provable_v]. *)

  (** Two logged values of one [sRd] key are equal (the SeqLock instance
      of [RelaxedHoareLog.logval_unique]; no [eq_rect_eq], by
      [RelaxedHoareSL2Prog.rd_rec_inj]). *)
  Lemma sl_logval_rd {rc : bool} (σ : State (EIhlv (E := E_S rc) δS)) key l (v w : nat) :
    LogOK (E := E_S rc) δS σ ->
    LogVal (E := E_S rc) δS (@RelaxedTraceLin.Build_Op (E_S rc) key (sRd l) v) σ ->
    LogVal (E := E_S rc) δS (@RelaxedTraceLin.Build_Op (E_S rc) key (sRd l) w) σ -> v = w.
  Proof. intros Hok Hv Hw. exact (rd_rec_inj key l v w (logval_unique (E := E_S rc) δS σ _ _ Hok Hv Hw eq_refl)). Qed.

  Section Kit.
    Context (rc : bool) (si : FOp -> FOp -> Prop) (tw : nat -> tid).

    Local Abbreviation ES := (E_S rc).
    Local Abbreviation FS := (F2 si).
    Local Abbreviation VB := (EIhl (E := E_S rc) δS).
    Local Abbreviation V := (EIhlv (E := E_S rc) δS).
    Local Abbreviation VF := (RelaxedHoareSpec.EI (F := F2 si) δF).
    Local Abbreviation POk v pool := (@PossOk FS VF v pool).
    Local Abbreviation OpF := (RelaxedTraceLin.Op FS).
    Local Abbreviation IV := (IslV rc si tw).
    Local Abbreviation IB := (Isl rc si tw).

    (** *** Registers and record values of the lifted memory *)

    Definition regsV (σ : State V) : Regs := fst (fst (fst σ)).

    Lemma regs_dropS (s : PState V VF) : regs rc si (dropS s) = regsV (ps_mem s).
    Proof. reflexivity. Qed.

    (** [KRd κ l v]: the underlay record of key [κ] is (or was) [rd l ↦ v]. *)
    Definition KRd (κ : CallKey ES) (l : SLoc) (v : nat) : Assn V VF :=
      fun s => LogVal (E := ES) δS (@RelaxedTraceLin.Build_Op ES κ (sRd l) v) (ps_mem s).

    Lemma krd_unique s κ l v w : IV s -> KRd κ l v s -> KRd κ l w s -> v = w.
    Proof. intros HI Hv Hw. exact (sl_logval_rd (ps_mem s) κ l v w (islV_logok rc si tw s HI) Hv Hw). Qed.

    (** Any [LogVal] fact (any underlay operation) is stable under every
        relation of a [liftGLk] family, whatever the invariant: in
        particular under [RslV k] and [GslV k] for every [k]. *)
    Lemma logvalA_stable_lk (I' : Assn V VF) (R : CallKey FS -> PRel VB VF) k (x : RelaxedTraceLin.Op ES) :
      Stable I' (liftGLk R k) (logA (LogVal (E := ES) δS x)).
    Proof. exact (stable_logA I' (R k) _ (logval_mono (E := ES) δS x)). Qed.

    (** [KRd] is stable under every lifted relation (reader-eval §4:
        "[V(κ, o, v)] facts are monotone"), in particular under every
        [liftGLk] rely and guarantee ([RslV], [GslV]). *)
    Lemma krd_stable (I' : Assn V VF) (r : PRel VB VF) κ l v : Stable I' (liftGL r) (KRd κ l v).
    Proof. exact (stable_logA I' r _ (logval_mono (E := ES) δS _)). Qed.

    Lemma krd_stable_r k κ l v : Stable IV (RslV rc si k) (KRd κ l v).
    Proof. exact (krd_stable IV (Rsl rc si k) κ l v). Qed.

    Lemma krd_stable_g k κ l v : Stable IV (GslV rc si k) (KRd κ l v).
    Proof. exact (krd_stable IV (Gsl rc si k) κ l v). Qed.

    Lemma krd_step ev (σ σ' : State V) p γ p' γ' κ l v :
      Step V ev σ σ' -> KRd κ l v (σ, p, γ) -> KRd κ l v (σ', p', γ').
    Proof. intros Hs H. exact (logval_step (E := ES) δS ev σ σ' _ Hs H). Qed.

    (** *** Underlay steps of [EIhlv δS] *)

    Lemma stepV_base ev (σ σ' : State V) : Step V ev σ σ' -> Step VB ev (fst σ) (fst σ').
    Proof. intros [H _]. exact H. Qed.

    Lemma regsV_inv_noreg t hu o (σ σ' : State V) :
      Step V (IE rc t hu o) σ σ' -> (forall l v, o <> sWr l v) -> regsV σ' = regsV σ.
    Proof. intros Hs Hn. exact (step_ie_regs rc _ _ t hu o (stepV_base _ _ _ Hs) Hn). Qed.

    Lemma regsV_res t hu o (r : sar o) (σ σ' : State V) :
      Step V (Build_ThreadEvent t (@ResEv ES hu o r)) σ σ' -> regsV σ' = regsV σ.
    Proof. intros Hs. exact (step_res rc _ _ t hu o r (stepV_base _ _ _ Hs)). Qed.

    Lemma rd_noreg l : forall l' v, sRd l <> sWr l' v.
    Proof. intros l' v E. discriminate E. Qed.

    Lemma rmb_noreg : forall l v, sRmb <> sWr l v.
    Proof. intros l v E. discriminate E. Qed.

    (** The emission of a read logs its record, whose value is the
        register read; the registers are unchanged. *)
    Lemma krd_inv t hu l (σ σ' : State V) p γ :
      Step V (IE rc t hu (sRd l)) σ σ' -> regsV σ' = regsV σ /\ KRd (t, hu) l (regsV σ l) (σ', p, γ).
    Proof.
      intros Hs. destruct (logval_inv (E := ES) δS t hu (sRd l) σ σ' Hs) as (r & st' & Hd & Hst & Hl).
      destruct Hd as [Hr Hm]. subst r st'. split; [exact Hst | exact Hl].
    Qed.

    (** A response returns the logged value of its key ([logval_res];
        reader-eval §4: "[logval_res] pins response values"). *)
    Lemma krd_res κ l (w v : nat) (σ σ' : State V) p γ :
      IV (σ, p, γ) -> KRd κ l w (σ, p, γ) ->
      Step V (Build_ThreadEvent (fst κ) (@ResEv ES (snd κ) (sRd l) v)) σ σ' -> w = v.
    Proof.
      destruct κ as [t hu]. intros HI Hl Hs.
      pose proof (logval_res (E := ES) δS t hu (sRd l) v _ σ σ' (islV_logok rc si tw _ HI) Hl eq_refl Hs) as E.
      exact (rd_rec_inj _ _ _ _ E).
    Qed.

    (** A response logs its own record: the [fin] of a response slot
        follows from its own event, with no precondition. *)
    Lemma krd_res_logged t hu l (v : nat) (σ σ' : State V) p γ :
      Step V (Build_ThreadEvent t (@ResEv ES hu (sRd l) v)) σ σ' -> KRd (t, hu) l v (σ', p, γ).
    Proof. intros Hs. exact (logval_res_logged (E := ES) δS t hu (sRd l) v σ σ' Hs). Qed.

    (** *** Value edges *)

    (** Out-edge of the iteration's first read [κG] of [Sq_i]: its logged
        value [r0] is at most the current [Sq_i] (eval1 §3, [E_G]). *)
    Definition EdgeG (i : nat) (κG : CallKey ES) : Assn V VF := fun s =>
      exists r0, KRd κG (Sq i) r0 s /\ liftA (KSeqGe rc si i r0) s.

    (** Out-edge of a data read [κd] of [l] ([Sx_i] with [pr := fst],
        [Sy_i] with [pr := snd]): [KRdVal] about the logged values of
        [κG] and [κd] (eval1 §3, [E_x], [E_y]). *)
    Definition EdgeD (i : nat) (κG κd : CallKey ES) (l : SLoc) (pr : nat * nat -> nat) : Assn V VF := fun s =>
      exists r0 ad, KRd κG (Sq i) r0 s /\ KRd κd l ad s /\ liftA (KRdVal rc si i r0 pr ad) s.

    (** The package carried from the read's linearization point to its
        return (eval1 §3, [Pkg]): the logged values [r0], [ax], [cy] of
        [κG], [κx], [κy]; the overlay record of [k] with value
        [(vx, vy)] (the [A i] of the LP); the [Sq_i] value [q] seen at the
        LP, still [≤ Sq_i]; and the [KRdVal] facts evaluated at the LP. *)
    Definition PkgAt (k : CallKey FS) (i : nat) (κG κx κy : CallKey ES) (r0 ax cy q vx vy : nat) : Assn V VF := fun s =>
      KRd κG (Sq i) r0 s /\ KRd κx (Sx i) ax s /\ KRd κy (Sy i) cy s /\
      liftA (KRec rc si (@RelaxedTraceLin.Build_Op FS k (fR i) (vx, vy))) s /\
      r0 <= q /\ liftA (KSeqGe rc si i q) s /\
      (q = r0 -> Nat.even r0 = true -> vx = ax /\ vy = cy).

    Definition Pkg (k : CallKey FS) (i : nat) (κG κx κy : CallKey ES) : Assn V VF := fun s =>
      exists r0 ax cy q vx vy, PkgAt k i κG κx κy r0 ax cy q vx vy s.

    (** The package after the final read [κT] of [Sq_i]: its logged value
        [r0'] is at least [q]. *)
    Definition PkgT (k : CallKey FS) (i : nat) (κG κx κy κT : CallKey ES) : Assn V VF := fun s =>
      exists r0 ax cy q vx vy r0', PkgAt k i κG κx κy r0 ax cy q vx vy s /\ KRd κT (Sq i) r0' s /\ q <= r0'.

    (** *** Own-slot guarantees that keep the abstract state

        [Gsl k] does not constrain [k]'s own pool entry, records or ghost
        entries.  A record fact of [k] ([KRec], in [PkgAt]) on a final
        edge must survive the guarantees of [k]'s own response slots
        ([bw_if]), and an ownership fact ([KOwns k isRmb], the B-6
        escape) as well; reader-eval §4 obligation (a), refined: the
        response slots keep the possibility *and* the ghost. *)
    Definition GslFix (k : CallKey FS) : PRel VB VF := fun s s' => Gsl rc si k s s' /\ ps_poss s' = ps_poss s.

    Definition GslRes (k : CallKey FS) : PRel VB VF := fun s s' => GslFix k s s' /\ ps_ghost s' = ps_ghost s.

    Lemma gslfix_gsl k s s' : GslFix k s s' -> Gsl rc si k s s'.
    Proof. intros [H _]. exact H. Qed.

    Lemma gslres_fix k s s' : GslRes k s s' -> GslFix k s s'.
    Proof. intros [H _]. exact H. Qed.

    (** [ns_guar] for slots with these guarantees. *)
    Lemma gslfixV_gslV k s s' : liftGL (GslFix k) s s' -> GslV rc si k s s'.
    Proof. intros [[Hg _] Hl]. split; [exact Hg | exact Hl]. Qed.

    Lemma gslresV_gslV k s s' : liftGL (GslRes k) s s' -> GslV rc si k s s'.
    Proof. intros [[[Hg _] _] Hl]. split; [exact Hg | exact Hl]. Qed.

    (** The maintenance lemmas of SL2Inv Part 7 give them. *)
    Lemma isl_response_res k t hu o (r : sar o) (σ σ' : State VB) p (γ : Ghost ES FS) :
      IB (σ, p, γ) -> Step VB (Build_ThreadEvent t (@ResEv ES hu o r)) σ σ' ->
      IB (σ', p, γ) /\ GslRes k (σ, p, γ) (σ', p, γ).
    Proof.
      intros HI Hs. destruct (isl_response rc si tw k t hu o r σ σ' p γ HI Hs) as [HI' Hg].
      split; [exact HI' | split; [split; [exact Hg | reflexivity] | reflexivity]].
    Qed.

    Lemma isl_inv_noreg_fix k t hu o (σ σ' : State VB) A Pf P (γ γ' : Ghost ES FS) :
      IB (σ, POk (A, Pf) P, γ) -> ghost_emit k (IE rc t hu o) γ γ' -> Step VB (IE rc t hu o) σ σ' ->
      (forall l v, o <> sWr l v) -> (forall ls, lin_lookup k ls P -> Coup rc si k ls γ') ->
      IB (σ', POk (A, Pf) P, γ') /\ GslFix k (σ, POk (A, Pf) P, γ) (σ', POk (A, Pf) P, γ').
    Proof.
      intros HI Hge Hs Hn Hc. destruct (isl_inv_noreg rc si tw k t hu o σ σ' A Pf P γ γ' HI Hge Hs Hn Hc) as [HI' Hg].
      split; [exact HI' | split; [exact Hg | reflexivity]].
    Qed.

    (** Base stability under the refined guarantees. *)
    Lemma krec_stable_fix k o : Stable IB (GslFix k) (KRec rc si o).
    Proof. intros s s' (A & Pf & P & Hp & Hin) [_ Hpp] _. exists A, Pf, P. rewrite Hpp. split; [exact Hp | exact Hin]. Qed.

    Lemma klook_stable_fix k k' ls : Stable IB (GslFix k) (KLook rc si k' ls).
    Proof. intros s s' (A & Pf & P & Hp & Hl) [_ Hpp] _. exists A, Pf, P. rewrite Hpp. split; [exact Hp | exact Hl]. Qed.

    Lemma kseqge_stable_fix k i v : Stable IB (GslFix k) (KSeqGe rc si i v).
    Proof. apply (Stable_mono IB _ (Gsl rc si k)); [exact (gslfix_gsl k) | apply (kseqge_stable_g rc si tw k)]. Qed.

    Lemma krdval_stable_fix k i v pr x : Stable IB (GslFix k) (KRdVal rc si i v pr x).
    Proof. apply (Stable_mono IB _ (Gsl rc si k)); [exact (gslfix_gsl k) | apply (krdval_stable_g rc si tw k)]. Qed.

    Lemma kowns_stable_res k k' Q : Stable IB (GslRes k) (KOwns rc si k' Q).
    Proof. intros s s' Hs [_ Hg] _. unfold KOwns in *. rewrite Hg. exact Hs. Qed.

    Lemma notnoown_stable_res k k' : Stable IB (GslRes k) (fun s => ~ NoOwn k' (ps_ghost s)).
    Proof. intros s s' Hs [_ Hg] _. rewrite Hg. exact Hs. Qed.

    (** Under the rely of [k], [k]'s ghost entries are kept both ways. *)
    Lemma notnoown_stable_r k : Stable IB (Rsl rc si k) (fun s => ~ NoOwn k (ps_ghost s)).
    Proof.
      intros s s' Hs (_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & _ & _ & _ & _ & Hgh & _) _ Hno.
      apply Hs. intros e He Ho. apply (Hno e); [apply (Hgh e Ho); exact He | exact Ho].
    Qed.

    (** *** Stability of the value edges and packages *)

    Lemma edgeG_stable (r : PRel VB VF) i κG :
      (forall v, Stable IB r (KSeqGe rc si i v)) -> Stable IV (liftGL r) (EdgeG i κG).
    Proof.
      intros Hr s s' (r0 & H1 & H2) Hrel HI. exists r0.
      split; [exact (krd_stable IV r κG (Sq i) r0 s s' H1 Hrel HI) |].
      exact (stable_liftL (LogOK (E := ES) δS) IB r _ (Hr r0) s s' H2 Hrel HI).
    Qed.

    Lemma edgeD_stable (r : PRel VB VF) i κG κd l pr :
      (forall v x, Stable IB r (KRdVal rc si i v pr x)) -> Stable IV (liftGL r) (EdgeD i κG κd l pr).
    Proof.
      intros Hr s s' (r0 & ad & H1 & H2 & H3) Hrel HI. exists r0, ad.
      split; [exact (krd_stable IV r κG (Sq i) r0 s s' H1 Hrel HI) |].
      split; [exact (krd_stable IV r κd l ad s s' H2 Hrel HI) |].
      exact (stable_liftL (LogOK (E := ES) δS) IB r _ (Hr r0 ad) s s' H3 Hrel HI).
    Qed.

    Lemma pkgAt_stable (r : PRel VB VF) k i κG κx κy r0 ax cy q vx vy :
      Stable IB r (KRec rc si (@RelaxedTraceLin.Build_Op FS k (fR i) (vx, vy))) -> Stable IB r (KSeqGe rc si i q) ->
      Stable IV (liftGL r) (PkgAt k i κG κx κy r0 ax cy q vx vy).
    Proof.
      intros Hrec Hq s s' (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hrel HI.
      split; [exact (krd_stable IV r _ _ _ s s' H1 Hrel HI) |].
      split; [exact (krd_stable IV r _ _ _ s s' H2 Hrel HI) |].
      split; [exact (krd_stable IV r _ _ _ s s' H3 Hrel HI) |].
      split; [exact (stable_liftL (LogOK (E := ES) δS) IB r _ Hrec s s' H4 Hrel HI) |].
      split; [exact H5 |].
      split; [exact (stable_liftL (LogOK (E := ES) δS) IB r _ Hq s s' H6 Hrel HI) | exact H7].
    Qed.

    Lemma pkg_stable (r : PRel VB VF) k i κG κx κy :
      (forall vx vy, Stable IB r (KRec rc si (@RelaxedTraceLin.Build_Op FS k (fR i) (vx, vy)))) ->
      (forall q, Stable IB r (KSeqGe rc si i q)) ->
      Stable IV (liftGL r) (Pkg k i κG κx κy).
    Proof.
      intros Hrec Hq s s' (r0 & ax & cy & q & vx & vy & H) Hrel HI. exists r0, ax, cy, q, vx, vy.
      exact (pkgAt_stable r k i κG κx κy r0 ax cy q vx vy (Hrec vx vy) (Hq q) s s' H Hrel HI).
    Qed.

    Lemma pkgT_stable (r : PRel VB VF) k i κG κx κy κT :
      (forall vx vy, Stable IB r (KRec rc si (@RelaxedTraceLin.Build_Op FS k (fR i) (vx, vy)))) ->
      (forall q, Stable IB r (KSeqGe rc si i q)) ->
      Stable IV (liftGL r) (PkgT k i κG κx κy κT).
    Proof.
      intros Hrec Hq s s' (r0 & ax & cy & q & vx & vy & r0' & H & HT & Hle) Hrel HI.
      exists r0, ax, cy, q, vx, vy, r0'.
      split; [exact (pkgAt_stable r k i κG κx κy r0 ax cy q vx vy (Hrec vx vy) (Hq q) s s' H Hrel HI) |].
      split; [exact (krd_stable IV r _ _ _ s s' HT Hrel HI) | exact Hle].
    Qed.

    (** Generic helpers for the final edges. *)
    Lemma Stable_or_v (I' : Assn V VF) (r : PRel V VF) (P Q : Assn V VF) :
      Stable I' r P -> Stable I' r Q -> Stable I' r (fun s => P s \/ Q s).
    Proof. intros HP HQ s s' [H | H] Hr HI; [left; exact (HP s s' H Hr HI) | right; exact (HQ s s' H Hr HI)]. Qed.

    Lemma stable_res_of_fix k' (P : Assn V VF) :
      Stable IV (liftGL (GslFix k')) P -> Stable IV (liftGL (GslRes k')) P.
    Proof.
      apply (Stable_mono IV _ (liftGL (GslFix k'))). intros s s' [Hg Hl]. split; [exact (gslres_fix k' _ _ Hg) | exact Hl].
    Qed.

    Lemma stable_g_of_fix k' (P : Assn V VF) :
      Stable IV (GslV rc si k') P -> Stable IV (liftGL (GslFix k')) P.
    Proof. apply (Stable_mono IV _ (GslV rc si k')). exact (gslfixV_gslV k'). Qed.

    (** Instances: the rely of the reader [k], and the refined guarantees
        of any own slot (for [EdgeG]/[EdgeD], every [GslV]). *)
    Lemma edgeG_stable_r k i κG : Stable IV (RslV rc si k) (EdgeG i κG).
    Proof. apply edgeG_stable. intros v. exact (kseqge_stable_r rc si tw k i v). Qed.

    Lemma edgeG_stable_g k i κG : Stable IV (GslV rc si k) (EdgeG i κG).
    Proof. apply edgeG_stable. intros v. exact (kseqge_stable_g rc si tw k i v). Qed.

    Lemma edgeD_stable_r k i κG κd l pr : Stable IV (RslV rc si k) (EdgeD i κG κd l pr).
    Proof. apply edgeD_stable. intros v x. exact (krdval_stable_r rc si tw k i v pr x). Qed.

    Lemma edgeD_stable_g k i κG κd l pr : Stable IV (GslV rc si k) (EdgeD i κG κd l pr).
    Proof. apply edgeD_stable. intros v x. exact (krdval_stable_g rc si tw k i v pr x). Qed.

    Lemma pkg_stable_r k i κG κx κy : Stable IV (RslV rc si k) (Pkg k i κG κx κy).
    Proof.
      apply pkg_stable; [intros vx vy; exact (krec_stable rc si tw k (@RelaxedTraceLin.Build_Op FS k (fR i) (vx, vy)) eq_refl) | intros q; exact (kseqge_stable_r rc si tw k i q)].
    Qed.

    Lemma pkg_stable_fix k' k i κG κx κy : Stable IV (liftGL (GslFix k')) (Pkg k i κG κx κy).
    Proof. apply pkg_stable; [intros vx vy; apply krec_stable_fix | intros q; apply kseqge_stable_fix]. Qed.

    Lemma pkgT_stable_r k i κG κx κy κT : Stable IV (RslV rc si k) (PkgT k i κG κx κy κT).
    Proof.
      apply pkgT_stable; [intros vx vy; exact (krec_stable rc si tw k (@RelaxedTraceLin.Build_Op FS k (fR i) (vx, vy)) eq_refl) | intros q; exact (kseqge_stable_r rc si tw k i q)].
    Qed.

    Lemma pkgT_stable_fix k' k i κG κx κy κT : Stable IV (liftGL (GslFix k')) (PkgT k i κG κx κy κT).
    Proof. apply pkgT_stable; [intros vx vy; apply krec_stable_fix | intros q; apply kseqge_stable_fix]. Qed.

    Lemma pkgT_stable_res k' k i κG κx κy κT : Stable IV (liftGL (GslRes k')) (PkgT k i κG κx κy κT).
    Proof.
      apply (Stable_mono IV _ (liftGL (GslFix k'))); [| apply pkgT_stable_fix].
      intros s s' [Hg Hl]. split; [exact (gslres_fix k' _ _ Hg) | exact Hl].
    Qed.

    (** The B-6 escape on the final edge: [k] still owns an entry. *)
    Lemma notnoownV_stable_r k : Stable IV (RslV rc si k) (fun s => ~ NoOwn k (ps_ghost s)).
    Proof. exact (stable_liftL (LogOK (E := ES) δS) IB (Rsl rc si k) _ (notnoown_stable_r k)). Qed.

    Lemma notnoownV_stable_res k' k : Stable IV (liftGL (GslRes k')) (fun s => ~ NoOwn k (ps_ghost s)).
    Proof. exact (stable_liftL (LogOK (E := ES) δS) IB (GslRes k') _ (notnoown_stable_res k' k)). Qed.

    Lemma kownsV_stable_r k Q : Stable IV (RslV rc si k) (liftA (KOwns rc si k Q)).
    Proof. exact (stable_liftL (LogOK (E := ES) δS) IB (Rsl rc si k) _ (kowns_stable rc si tw k Q)). Qed.

    Lemma kownsV_stable_res k' k Q : Stable IV (liftGL (GslRes k')) (liftA (KOwns rc si k Q)).
    Proof. exact (stable_liftL (LogOK (E := ES) δS) IB (GslRes k') _ (kowns_stable_res k' k Q)). Qed.

    (** An own emission of a non-[Q] invocation keeps "[k] owns a [Q]
        entry" (the non-final [rmb_b] case: after it, [k] owns a later
        [rmb]; the final [rd Sq_i] does not remove it). *)
    Lemma owns_emit_keep k Q t hu o (γ γ' : Ghost ES FS) :
      Owns rc si k Q γ -> ghost_emit k (IE rc t hu o) γ γ' -> ~ Q o -> Owns rc si k Q γ'.
    Proof.
      intros (e & He & Ho & Hq) Hge Hn. exists e. split; [| split; [exact Ho | exact Hq]].
      apply (ghost_emit_keeps_neq k (IE rc t hu o) γ γ' e Hge); [| exact He].
      intros ->. apply Hn. exact Hq.
    Qed.

    (** *** Establishment at the read's own events *)

    (** [EdgeG] mentions only the memory: it survives any step that does
        not lower [Sq_i] (e.g. the [rmb_a] between [κG] and the data reads;
        there is no direct [κG] → [κx] edge, DR/DR on distinct
        locations). *)
    Lemma edgeG_step i κG ev (σ σ' : State V) p p' γ γ' :
      EdgeG i κG (σ, p, γ) -> Step V ev σ σ' -> regsV σ (Sq i) <= regsV σ' (Sq i) -> EdgeG i κG (σ', p', γ').
    Proof.
      intros (r0 & Hk & Hge) Hs Hle. exists r0. split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs Hk) |].
      unfold liftA, KSeqGe in Hge |- *. rewrite regs_dropS in Hge |- *. cbn [ps_mem fst] in Hge |- *. lia.
    Qed.

    (** The recorded non-blocking fact of an [rd Sq_i] of [k]
        ([RelaxedHoareReady.recnb_establish]), needed by [isl_read_lp] for
        the older-write-of-the-same-instance case; stable under the rely
        of [k] and every guarantee. *)
    Lemma krecnb_inv k t hG i (σ σ' : State V) A Pf P (γ γ' : Ghost ES FS) :
      IV (σ, POk (A, Pf) P, γ) -> ghost_emit k (IE rc t hG (sRd (Sq i))) γ γ' ->
      liftA (KRecNB rc si k (IE rc t hG (sRd (Sq i)))) (σ', POk (A, Pf) P, γ').
    Proof.
      intros [(A1 & Pf1 & P1 & Hp & _ & HC) _] Hge. cbn in Hp. injection Hp as <- <- <-.
      exists A, Pf, P. split; [reflexivity |].
      exact (proj2 (recnb_establish P k (IE rc t hG (sRd (Sq i))) γ γ' (ic_age rc si tw _ _ _ _ _ HC) Logic.I Hge)).
    Qed.

    Lemma krecnbV_stable_r k ev : Stable IV (RslV rc si k) (liftA (KRecNB rc si k ev)).
    Proof. exact (stable_liftL (LogOK (E := ES) δS) IB (Rsl rc si k) _ (krecnb_stable_r rc si tw k ev)). Qed.

    Lemma krecnbV_stable_g k k1 ev : Stable IV (GslV rc si k) (liftA (KRecNB rc si k1 ev)).
    Proof. exact (stable_liftL (LogOK (E := ES) δS) IB (Gsl rc si k) _ (krecnb_stable_g rc si tw k1 k ev)). Qed.

    (** At [κG] (first read of [Sq_i]). *)
    Lemma edgeG_inv t hG i (σ σ' : State V) p γ :
      Step V (IE rc t hG (sRd (Sq i))) σ σ' -> EdgeG i (t, hG) (σ', p, γ).
    Proof.
      intros Hs. destruct (krd_inv t hG (Sq i) σ σ' p γ Hs) as [Hr Hk]. exists (regsV σ (Sq i)).
      split; [exact Hk |]. unfold liftA, KSeqGe. rewrite regs_dropS. cbn [ps_mem fst]. rewrite Hr. apply le_n.
    Qed.

    (** At a data read [κd] of [l] (the abstract state is unchanged by
        this emission): [JEven] gives the [KRdVal] fact. *)
    Lemma edgeD_inv t hG hd i l pr (σ σ' : State V) A Pf P (γ γ' : Ghost ES FS) :
      (forall m : Regs, (m (Sx i), m (Sy i)) = A i -> pr (A i) = m l) ->
      IV (σ, POk (A, Pf) P, γ) -> EdgeG i (t, hG) (σ, POk (A, Pf) P, γ) ->
      Step V (IE rc t hd (sRd l)) σ σ' -> EdgeD i (t, hG) (t, hd) l pr (σ', POk (A, Pf) P, γ').
    Proof.
      intros Hpl [HI _] (r0 & Hg & Hge) Hs.
      destruct (krd_inv t hd l σ σ' (POk (A, Pf) P) γ' Hs) as [Hr Hk].
      exists r0, (regsV σ l). split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs Hg) |]. split; [exact Hk |].
      unfold liftA, KSeqGe in Hge. rewrite regs_dropS in Hge. cbn [ps_mem fst] in Hge.
      exists A, Pf, P. split; [reflexivity |]. rewrite regs_dropS. cbn [ps_mem fst]. rewrite Hr.
      split; [exact Hge |]. intros Hq Ev.
      destruct HI as (A1 & Pf1 & P1 & Hp & _ & HC). cbn in Hp. injection Hp as <- <- <-.
      apply Hpl. apply (ic_jeven rc si tw _ _ _ _ _ HC i). change (Nat.even (regsV σ (Sq i)) = true).
      rewrite Hq. exact Ev.
    Qed.

    Lemma edgeX_inv t hG hX i (σ σ' : State V) A Pf P (γ γ' : Ghost ES FS) :
      IV (σ, POk (A, Pf) P, γ) -> EdgeG i (t, hG) (σ, POk (A, Pf) P, γ) ->
      Step V (IE rc t hX (sRd (Sx i))) σ σ' -> EdgeD i (t, hG) (t, hX) (Sx i) fst (σ', POk (A, Pf) P, γ').
    Proof. apply edgeD_inv. intros m Hm. rewrite <- Hm. reflexivity. Qed.

    Lemma edgeY_inv t hG hY i (σ σ' : State V) A Pf P (γ γ' : Ghost ES FS) :
      IV (σ, POk (A, Pf) P, γ) -> EdgeG i (t, hG) (σ, POk (A, Pf) P, γ) ->
      Step V (IE rc t hY (sRd (Sy i))) σ σ' -> EdgeD i (t, hG) (t, hY) (Sy i) snd (σ', POk (A, Pf) P, γ').
    Proof. apply edgeD_inv. intros m Hm. rewrite <- Hm. reflexivity. Qed.

    (** At the linearization point (the read's last [rmb], with the
        abstract update of [isl_read_lp]): the two [r0] of [EdgeD] agree
        ([sl_logval_rd]), and the package records [q := Sq_i] and
        [(vx, vy) := A i] of the LP. *)
    Lemma pkg_lp k i κG κx κy t hB (σ σ' : State V) A Pf P P' (γ γ' : Ghost ES FS) :
      IV (σ, POk (A, Pf) P, γ) ->
      EdgeD i κG κx (Sx i) fst (σ, POk (A, Pf) P, γ) -> EdgeD i κG κy (Sy i) snd (σ, POk (A, Pf) P, γ) ->
      Step V (IE rc t hB sRmb) σ σ' ->
      exists r0 ax cy, PkgAt k i κG κx κy r0 ax cy (regsV σ (Sq i)) (fst (A i)) (snd (A i))
        (σ', POk (A, @RelaxedTraceLin.Build_Op FS k (fR i) (A i) :: Pf) P', γ').
    Proof.
      intros HI (r0 & ax & Hg & Hx & (A1 & Pf1 & P1 & Hp1 & Hle & Hvx)) (r0' & cy & Hg' & Hy & (A2 & Pf2 & P2 & Hp2 & _ & Hvy)) Hs.
      cbn in Hp1, Hp2. injection Hp1 as <- <- <-. injection Hp2 as <- <- <-.
      assert (E0 : r0' = r0) by exact (krd_unique _ κG (Sq i) r0' r0 HI Hg' Hg). subst r0'.
      pose proof (regsV_inv_noreg t hB sRmb σ σ' Hs rmb_noreg) as Hr.
      rewrite regs_dropS in Hle, Hvx, Hvy. cbn [ps_mem fst] in Hle, Hvx, Hvy.
      exists r0, ax, cy. split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs Hg) |].
      split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs Hx) |].
      split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs Hy) |].
      split; [exists A, (RelaxedTraceLin.Build_Op k (fR i) (A i) :: Pf), P'; split; [reflexivity |];
              left; rewrite <- surjective_pairing; reflexivity |].
      split; [exact Hle |].
      split; [unfold liftA, KSeqGe; rewrite regs_dropS; cbn [ps_mem fst]; rewrite Hr; apply le_n |].
      intros Hq Ev. split; [exact (Hvx Hq Ev) | exact (Hvy Hq Ev)].
    Qed.

    Corollary pkg_lp_ex k i κG κx κy t hB (σ σ' : State V) A Pf P P' (γ γ' : Ghost ES FS) :
      IV (σ, POk (A, Pf) P, γ) ->
      EdgeD i κG κx (Sx i) fst (σ, POk (A, Pf) P, γ) -> EdgeD i κG κy (Sy i) snd (σ, POk (A, Pf) P, γ) ->
      Step V (IE rc t hB sRmb) σ σ' ->
      Pkg k i κG κx κy (σ', POk (A, @RelaxedTraceLin.Build_Op FS k (fR i) (A i) :: Pf) P', γ').
    Proof.
      intros HI Hx Hy Hs. destruct (pkg_lp k i κG κx κy t hB σ σ' A Pf P P' γ γ' HI Hx Hy Hs) as (r0 & ax & cy & H).
      exists r0, ax, cy, (regsV σ (Sq i)), (fst (A i)), (snd (A i)). exact H.
    Qed.

    (** Across any step that keeps the abstract state and does not lower
        [Sq_i] (the reader's own non-LP events, responses). *)
    Lemma pkgAt_step k i κG κx κy r0 ax cy q vx vy ev (σ σ' : State V) p γ γ' :
      PkgAt k i κG κx κy r0 ax cy q vx vy (σ, p, γ) -> Step V ev σ σ' -> regsV σ (Sq i) <= regsV σ' (Sq i) ->
      PkgAt k i κG κx κy r0 ax cy q vx vy (σ', p, γ').
    Proof.
      intros (H1 & H2 & H3 & H4 & H5 & H6 & H7) Hs Hle.
      split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs H1) |].
      split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs H2) |].
      split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs H3) |].
      split; [exact H4 |]. split; [exact H5 |].
      split; [| exact H7]. unfold liftA, KSeqGe in H6 |- *. rewrite regs_dropS in H6 |- *. cbn [ps_mem fst] in H6 |- *. lia.
    Qed.

    Lemma pkg_step k i κG κx κy ev (σ σ' : State V) p γ γ' :
      Pkg k i κG κx κy (σ, p, γ) -> Step V ev σ σ' -> regsV σ (Sq i) <= regsV σ' (Sq i) -> Pkg k i κG κx κy (σ', p, γ').
    Proof.
      intros (r0 & ax & cy & q & vx & vy & H) Hs Hle. exists r0, ax, cy, q, vx, vy.
      exact (pkgAt_step k i κG κx κy r0 ax cy q vx vy ev σ σ' p γ γ' H Hs Hle).
    Qed.

    Lemma pkgT_step k i κG κx κy κT ev (σ σ' : State V) p γ γ' :
      PkgT k i κG κx κy κT (σ, p, γ) -> Step V ev σ σ' -> regsV σ (Sq i) <= regsV σ' (Sq i) ->
      PkgT k i κG κx κy κT (σ', p, γ').
    Proof.
      intros (r0 & ax & cy & q & vx & vy & r0' & H & HT & Hle') Hs Hle. exists r0, ax, cy, q, vx, vy, r0'.
      split; [exact (pkgAt_step k i κG κx κy r0 ax cy q vx vy ev σ σ' p γ γ' H Hs Hle) |].
      split; [exact (krd_step _ σ σ' _ _ _ _ _ _ _ Hs HT) | exact Hle'].
    Qed.

    (** At the final read [κT] of [Sq_i]: its logged value is at least [q]. *)
    Lemma pkgT_inv k i κG κx κy t hT (σ σ' : State V) p γ γ' :
      Pkg k i κG κx κy (σ, p, γ) -> Step V (IE rc t hT (sRd (Sq i))) σ σ' -> PkgT k i κG κx κy (t, hT) (σ', p, γ').
    Proof.
      intros (r0 & ax & cy & q & vx & vy & H) Hs. destruct (krd_inv t hT (Sq i) σ σ' p γ' Hs) as [Hr Hk].
      exists r0, ax, cy, q, vx, vy, (regsV σ (Sq i)).
      split; [apply (pkgAt_step k i κG κx κy r0 ax cy q vx vy _ σ σ' p γ γ' H Hs); rewrite Hr; apply le_n |].
      split; [exact Hk |]. destruct H as (_ & _ & _ & _ & _ & H6 & _).
      unfold liftA, KSeqGe in H6. rewrite regs_dropS in H6. exact H6.
    Qed.

    (** *** The identification at the return ([bw_sum] / [Close])

        The machine returns [(a, c)] after an iteration whose responses
        were [sv] ([κG]), [a] ([κx]), [c] ([κy]), [sv'] ([κT]), with
        [rok sv sv' = true].  The [fin]s of these four response slots give
        the [KRd] facts; the [fin] of [κT]'s response also carries
        [PkgT].  Then the logged values are the returned ones, [q = r0]
        is even, and the record [(vx, vy)] made at the LP (where it was
        [A i]) is [(a, c)]. *)
    Lemma pkgT_vals k i κG κx κy κT r0 ax cy q vx vy r0' (s : PState V VF) (sv a c sv' : nat) :
      IV s -> PkgAt k i κG κx κy r0 ax cy q vx vy s -> KRd κT (Sq i) r0' s -> q <= r0' ->
      KRd κG (Sq i) sv s -> KRd κx (Sx i) a s -> KRd κy (Sy i) c s -> KRd κT (Sq i) sv' s ->
      rok sv sv' = true -> (vx, vy) = (a, c).
    Proof.
      intros HI (H1 & H2 & H3 & _ & H5 & _ & H7) HT Hle HG HX HY HT' Hok.
      pose proof (krd_unique s κG (Sq i) r0 sv HI H1 HG) as E1.
      pose proof (krd_unique s κx (Sx i) ax a HI H2 HX) as E2.
      pose proof (krd_unique s κy (Sy i) cy c HI H3 HY) as E3.
      pose proof (krd_unique s κT (Sq i) r0' sv' HI HT HT') as E4.
      rewrite <- E1, <- E4 in Hok. rewrite <- E2, <- E3. apply rok_spec in Hok as [Ev Heq].
      assert (Hq : q = r0) by lia. destruct (H7 Hq Ev) as [-> ->]. reflexivity.
    Qed.

    (** The returned pair is the abstract value at the LP. *)
    Corollary read_value_is_lp_value k i κG κx κy κT r0 ax cy q (Alp : nat * nat) r0' (s : PState V VF) (sv a c sv' : nat) :
      IV s -> PkgAt k i κG κx κy r0 ax cy q (fst Alp) (snd Alp) s -> KRd κT (Sq i) r0' s -> q <= r0' ->
      KRd κG (Sq i) sv s -> KRd κx (Sx i) a s -> KRd κy (Sy i) c s -> KRd κT (Sq i) sv' s ->
      rok sv sv' = true -> (a, c) = Alp.
    Proof.
      intros HI H HT Hle HG HX HY HT' Hok.
      rewrite <- (pkgT_vals k i κG κx κy κT r0 ax cy q (fst Alp) (snd Alp) r0' s sv a c sv' HI H HT Hle HG HX HY HT' Hok).
      symmetry. apply surjective_pairing.
    Qed.

    (** A record of [k] in a state of the invariant: [k] is at [ls_lini]
        with it, so the read postcondition [Qsl] holds. *)
    Lemma qsl_of_krec k i (r : nat * nat) (s : PState VB VF) :
      IB s -> KRec rc si (@RelaxedTraceLin.Build_Op FS k (fR i) r) s -> Qsl rc si k (fR i) r s.
    Proof.
      intros (A & Pf & P & Hp & _ & HC) (A' & Pf' & P' & Hp' & Hin). rewrite Hp in Hp'. injection Hp' as <- <- <-.
      exists A, Pf, P. split; [exact Hp |]. right. split; [| exact Hin].
      exact (ic_rec rc si tw _ _ _ _ _ HC _ Hin).
    Qed.

    (** The return of the validating path: [Qsl] over [EIhlv]. *)
    Theorem sl_read_close k i κG κx κy κT (s : PState V VF) (sv a c sv' : nat) :
      IV s -> PkgT k i κG κx κy κT s ->
      KRd κG (Sq i) sv s -> KRd κx (Sx i) a s -> KRd κy (Sy i) c s -> KRd κT (Sq i) sv' s ->
      rok sv sv' = true -> QslV rc si k (fR i) (a, c) s.
    Proof.
      intros HI (r0 & ax & cy & q & vx & vy & r0' & H & HT & Hle) HG HX HY HT' Hok.
      pose proof (pkgT_vals k i κG κx κy κT r0 ax cy q vx vy r0' s sv a c sv' HI H HT Hle HG HX HY HT' Hok) as E.
      injection E as -> ->. destruct H as (_ & _ & _ & Hrec & _).
      exact (qsl_of_krec k i (a, c) (dropS s) (islV_base rc si tw s HI) Hrec).
    Qed.

    (** With the B-6 escape: on a path that validates before the ghost's
        last iteration (no LP on this path), the [fin] of [κT]'s response
        carries "[k] still owns an entry" instead of [PkgT]; either way
        the read postcondition [Qrd] holds. *)
    Theorem sl_read_close_rd k i κG κx κy κT (s : PState V VF) (sv a c sv' : nat) :
      IV s -> (PkgT k i κG κx κy κT s \/ ~ NoOwn k (ps_ghost s)) ->
      KRd κG (Sq i) sv s -> KRd κx (Sx i) a s -> KRd κy (Sy i) c s -> KRd κT (Sq i) sv' s ->
      rok sv sv' = true -> QrdV rc si k i (a, c) s.
    Proof.
      intros HI [Hp | Hn] HG HX HY HT Hok.
      - left. exact (sl_read_close k i κG κx κy κT s sv a c sv' HI Hp HG HX HY HT Hok).
      - right. exact Hn.
    Qed.

    Corollary sl_read_close_owns k Q i (s : PState V VF) (r : nat * nat) :
      Owns rc si k Q (ps_ghost s) -> QrdV rc si k i r s.
    Proof. intros H. right. exact (owns_not_noown rc si k Q _ H). Qed.
    (** ** Part 6. The read's own updates over [EIhlv] (a check of the kit)

        [EvUpdate]s for the three kinds of events of the read [k = (t, h)]
        of instance [i], each from the maintenance lemmas of SL2Inv Part 7
        and the kit above.  The read is known to be in the pool with its
        operation ([KHas], carried along the invocation chain). *)

    (** [k] is in the pool with operation [o] (any phase). *)
    Definition KHas (k : CallKey FS) (o : FOp) : Assn V VF := fun s =>
      exists A Pf P, ps_poss s = POk (A, Pf) P /\ HasOp si k o P.

    Lemma khas_stable_r k o : Stable IV (RslV rc si k) (KHas k o).
    Proof.
      intros s s' (A & Pf & P & Hp & (ls & Hl & Ho)) [(_ & A1 & Pf1 & P1 & A1' & Pf1' & P1' & Hp1 & Hp1' & Hlk & _) _] _.
      change (ps_poss (dropS s)) with (ps_poss s) in Hp1. change (ps_poss (dropS s')) with (ps_poss s') in Hp1'.
      rewrite Hp in Hp1. injection Hp1 as <- <- <-. exists A1', Pf1', P1'. split; [exact Hp1' |].
      exists ls. split; [exact (Hlk ls Hl) | exact Ho].
    Qed.

    Lemma khas_stable_fix k' k o : Stable IV (liftGL (GslFix k')) (KHas k o).
    Proof.
      intros s s' H [[_ Hpp] _] _. change (ps_poss s' = ps_poss s) in Hpp. unfold KHas. rewrite Hpp. exact H.
    Qed.

    (** The coupling of a read whose emitted invocation is not an [rmb]
        is unchanged by the emission. *)
    Lemma coup_emit_nonrmb k i t hu o (σ : State VB) A Pf P (γ γ' : Ghost ES FS) :
      IB (σ, POk (A, Pf) P, γ) -> ghost_emit k (IE rc t hu o) γ γ' -> o <> sRmb -> HasOp si k (fR i) P ->
      forall ls, lin_lookup k ls P -> Coup rc si k ls γ'.
    Proof.
      intros HI Hge Hn (ls0 & Hl0 & Ho0) ls Hl.
      destruct HI as (A1 & Pf1 & P1 & Hp & _ & HC). cbn in Hp. injection Hp as <- <- <-.
      pose proof (RelaxedHoareInherit.lookup_unique_gen P k _ _ (ic_wf rc si tw _ _ _ _ _ HC) Hl Hl0) as ->.
      pose proof (ic_coup rc si tw _ _ _ _ _ HC _ Hl0) as Hc. rewrite lin_key_make_lin_entry in Hc.
      unfold Coup in Hc |- *. cbn [lin_state make_lin_entry] in Hc. rewrite Ho0 in Hc |- *.
      rewrite Hc. split.
      - intros Hown. apply (owns_emit_keep k isRmb t hu o γ γ' Hown Hge). exact Hn.
      - apply owns_incl. exact (ghost_emit_incl k (IE rc t hu o) γ γ' Hge).
    Qed.

    (** An invocation of the read that writes no register and is not an
        [rmb] (its [rd Sq_i], [rd Sx_i], [rd Sy_i]): no abstract step, the
        guarantee keeps the abstract state ([GslFix]). *)
    Theorem rd_noreg_update t (h : handle FS) i (hu : nat) o (Pd Qd : Assn V VF) :
      (forall l v, o <> sWr l v) -> o <> sRmb ->
      (forall σ σ' p γ γ', Pd (σ, p, γ) -> IV (σ, p, γ) -> ghost_emit (t, h) (IE rc t hu o) γ γ' ->
         Step V (IE rc t hu o) σ σ' -> Qd (σ', p, γ')) ->
      EvUpdate IV (liftGL (GslFix (t, h))) (t, h) (IE rc t hu o)
        (fun s => Pd s /\ KHas (t, h) (fR i) s) (fun s => Qd s /\ KHas (t, h) (fR i) s).
    Proof.
      intros Hnw Hnr HQ σ p γ γ' [Hd Hhas] HI Hge σ' Hs.
      pose proof HI as [HIb HJ]. pose proof Hhas as (A & Pf & P & Hp & Hop). cbn [ps_poss fst snd] in Hp. subst p.
      destruct (isl_inv_noreg_fix (t, h) t hu o (fst σ) (fst σ') A Pf P γ γ' HIb Hge (stepV_base _ _ _ Hs) Hnw
                  (coup_emit_nonrmb (t, h) i t hu o (fst σ) A Pf P γ γ' HIb Hge Hnr Hop)) as [HI' Hg].
      exists (POk (A, Pf) P). split; [apply rt_refl |].
      split; [split; [exact (HQ σ σ' _ γ γ' Hd HI Hge Hs) | exact Hhas] |].
      split; [split; [exact HI' | exact (logok_step (E := ES) δS _ σ σ' Hs HJ)] |].
      split; [exact Hg | exact (log_steps_step VB _ σ σ' Hs)].
    Qed.

    Lemma ivV_poss (σ : State V) p (γ : Ghost ES FS) : IV (σ, p, γ) -> exists A Pf P, p = POk (A, Pf) P.
    Proof. intros [(A & Pf & P & Hp & _) _]. exists A, Pf, P. exact Hp. Qed.

    (** The first read [κG = (t, hG)] of [Sq_i] of an iteration: its
        out-edge [EdgeG] and the recorded non-blocking fact. *)
    Corollary rd_G_update t (h : handle FS) i (hG : nat) :
      EvUpdate IV (liftGL (GslFix (t, h))) (t, h) (IE rc t hG (sRd (Sq i)))
        (fun s => True /\ KHas (t, h) (fR i) s)
        (fun s => (EdgeG i (t, hG) s /\ liftA (KRecNB rc si (t, h) (IE rc t hG (sRd (Sq i)))) s) /\ KHas (t, h) (fR i) s).
    Proof.
      apply (rd_noreg_update t h i hG (sRd (Sq i))); [exact (rd_noreg (Sq i)) | discriminate |].
      intros σ σ' p γ γ' _ HI Hge Hs. split; [exact (edgeG_inv t hG i σ σ' p γ' Hs) |].
      destruct (ivV_poss σ p γ HI) as (A & Pf & P & ->). exact (krecnb_inv (t, h) t hG i σ σ' A Pf P γ γ' HI Hge).
    Qed.

    (** The data reads [κx = (t, hX)], [κy = (t, hY)]. *)
    Corollary rd_X_update t (h : handle FS) i (hG hX : nat) :
      EvUpdate IV (liftGL (GslFix (t, h))) (t, h) (IE rc t hX (sRd (Sx i)))
        (fun s => EdgeG i (t, hG) s /\ KHas (t, h) (fR i) s)
        (fun s => EdgeD i (t, hG) (t, hX) (Sx i) fst s /\ KHas (t, h) (fR i) s).
    Proof.
      apply (rd_noreg_update t h i hX (sRd (Sx i))); [exact (rd_noreg (Sx i)) | discriminate |].
      intros σ σ' p γ γ' Hg HI _ Hs. destruct (ivV_poss σ p γ HI) as (A & Pf & P & ->).
      exact (edgeX_inv t hG hX i σ σ' A Pf P γ γ' HI Hg Hs).
    Qed.

    Corollary rd_Y_update t (h : handle FS) i (hG hY : nat) :
      EvUpdate IV (liftGL (GslFix (t, h))) (t, h) (IE rc t hY (sRd (Sy i)))
        (fun s => EdgeG i (t, hG) s /\ KHas (t, h) (fR i) s)
        (fun s => EdgeD i (t, hG) (t, hY) (Sy i) snd s /\ KHas (t, h) (fR i) s).
    Proof.
      apply (rd_noreg_update t h i hY (sRd (Sy i))); [exact (rd_noreg (Sy i)) | discriminate |].
      intros σ σ' p γ γ' Hg HI _ Hs. destruct (ivV_poss σ p γ HI) as (A & Pf & P & ->).
      exact (edgeY_inv t hG hY i σ σ' A Pf P γ γ' HI Hg Hs).
    Qed.

    (** An [rmb] of the read: the linearization point when the read owns
        no [rmb] afterwards ([isl_read_lp]; [Qlp] is what the derivation
        concludes from the LP transition, e.g. [Pkg] by [pkg_lp_ex]),
        otherwise no abstract step and the read still owns an [rmb] (the
        B-6 escape).  [k] is at [ls_inv] here because it owns the emitted
        [rmb] ([Coup]). *)
    Theorem rd_rmb_update (Hsi : forall o o', slRA o o' -> si o o') t (h : handle FS) i (hR hB : nat) (Pd Pc Qlp : Assn V VF) :
      (forall (σ σ' : State V) (A : AS) (Pf : list OpF) (P P' : LinPool FS) (γ γ' : Ghost ES FS),
         Pd (σ, POk (A, Pf) P, γ) -> IV (σ, POk (A, Pf) P, γ) ->
         Step V (IE rc t hB sRmb) σ σ' -> lin_invoke_update t h (fR i) P P' ->
         Qlp (σ', POk (A, @RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf) P', γ')) ->
      (forall (σ σ' : State V) p p' (γ γ' : Ghost ES FS), Pc (σ, p, γ) -> Step V (IE rc t hB sRmb) σ σ' -> Pc (σ', p', γ')) ->
      EvUpdate IV (GslV rc si (t, h)) (t, h) (IE rc t hB sRmb)
        (fun s => Pd s /\ Pc s /\ liftA (KRecNB rc si (t, h) (IE rc t hR (sRd (Sq i)))) s /\ KHas (t, h) (fR i) s)
        (fun s => (Qlp s \/ liftA (KOwns rc si (t, h) isRmb) s) /\ Pc s /\ KHas (t, h) (fR i) s).
    Proof.
      intros HQ HPc σ p γ γ' (Hd & Hpc & Hrec & Hhas) HI Hge σ' Hs.
      pose proof HI as [HIb HJ].
      destruct Hhas as (A & Pf & P & Hp & (ls & Hl & Hop)). cbn [ps_poss fst snd] in Hp. subst p.
      destruct Hrec as (A2 & Pf2 & P2 & Hp2 & Hrec). cbn in Hp2. injection Hp2 as <- <- <-.
      pose proof HIb as (A1 & Pf1 & P1 & Hp1 & _ & HC). cbn in Hp1. injection Hp1 as <- <- <-.
      assert (Hown : Owns rc si (t, h) isRmb γ).
      { destruct (ghost_emit_ie rc si (t, h) t hB sRmb γ γ' Hge) as (g1 & g2 & -> & _ & _).
        exists (Build_ScheduledEvent (t, h) (IE rc t hB sRmb)).
        split; [apply in_or_app; right; left; reflexivity | split; reflexivity]. }
      assert (Hls : ls = @ls_inv FS (fR i)).
      { pose proof (ic_coup rc si tw _ _ _ _ _ HC _ Hl) as Hc. rewrite lin_key_make_lin_entry in Hc.
        unfold Coup in Hc. cbn [lin_state make_lin_entry] in Hc. rewrite Hop in Hc. apply Hc in Hown.
        destruct ls as [o | o | o r]; cbn in Hop, Hown |- *; [subst o; reflexivity | discriminate Hown | discriminate Hown]. }
      subst ls.
      destruct (owns_dec rc si (t, h) isRmb γ' isRmb_dec) as [Hown' | Hnown'].
      - (* not the last [rmb] *)
        assert (Hc' : forall ls, lin_lookup (t, h) ls P -> Coup rc si (t, h) ls γ').
        { intros ls Hl'. rewrite (RelaxedHoareInherit.lookup_unique_gen P (t, h) _ _ (ic_wf rc si tw _ _ _ _ _ HC) Hl' Hl).
          unfold Coup. cbn. split; [intros _; exact Hown' | reflexivity]. }
        destruct (isl_inv_noreg rc si tw (t, h) t hB sRmb (fst σ) (fst σ') A Pf P γ γ' HIb Hge (stepV_base _ _ _ Hs) rmb_noreg Hc')
          as [HI' Hg].
        exists (POk (A, Pf) P). split; [apply rt_refl |].
        split; [split; [right; exact Hown' |]; split; [exact (HPc σ σ' _ _ γ γ' Hpc Hs) |];
                exists A, Pf, P; split; [reflexivity | exists (@ls_inv FS (fR i)); split; [exact Hl | reflexivity]] |].
        split; [split; [exact HI' | exact (logok_step (E := ES) δS _ σ σ' Hs HJ)] |].
        split; [exact Hg | exact (log_steps_step VB _ σ σ' Hs)].
      - (* the linearization point *)
        destruct (isl_read_lp rc si tw Hsi t h i hB hR (fst σ) (fst σ') A Pf P γ γ' HIb Hl Hge (stepV_base _ _ _ Hs) Hrec Hnown')
          as (P' & Hu & Hps & HI' & Hg).
        exists (POk (A, @RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf) P'). split; [exact Hps |].
        split.
        + split; [left; exact (HQ σ σ' A Pf P P' γ γ' Hd HI Hs Hu) |]. split; [exact (HPc σ σ' _ _ γ γ' Hpc Hs) |].
          exists A, (@RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf), P'. split; [reflexivity |].
          apply (proj1 (hasop_update si (t, h) _ _ P P' (t, h) (fR i) (ic_wf rc si tw _ _ _ _ _ HC)
                          (lin_invoke_update_is_update _ _ _ _ _ Hu) eq_refl)).
          exists (@ls_inv FS (fR i)). split; [exact Hl | reflexivity].
        + split; [split; [exact HI' | exact (logok_step (E := ES) δS _ σ σ' Hs HJ)] |].
          split; [exact Hg | exact (log_steps_step VB _ σ σ' Hs)].
    Qed.

    (** The [rmb_b] instance: at the LP the package [Pkg] holds. *)
    Corollary rd_rmbB_update (Hsi : forall o o', slRA o o' -> si o o') t (h : handle FS) i (hR hG hB : nat) κx κy :
      EvUpdate IV (GslV rc si (t, h)) (t, h) (IE rc t hB sRmb)
        (fun s => (EdgeD i (t, hG) κx (Sx i) fst s /\ EdgeD i (t, hG) κy (Sy i) snd s) /\ True /\
                  liftA (KRecNB rc si (t, h) (IE rc t hR (sRd (Sq i)))) s /\ KHas (t, h) (fR i) s)
        (fun s => (Pkg (t, h) i (t, hG) κx κy s \/ liftA (KOwns rc si (t, h) isRmb) s) /\ True /\ KHas (t, h) (fR i) s).
    Proof.
      apply (rd_rmb_update Hsi t h i hR hB); [| intros; exact Logic.I]. intros σ σ' A Pf P P' γ γ' [Hx Hy] HI Hs _.
      exact (pkg_lp_ex (t, h) i (t, hG) κx κy t hB σ σ' A Pf P P' γ γ' HI Hx Hy Hs).
    Qed.

    (** The [rmb_a] instance: an LP there (possible only if the ghost
        footprint disagrees with the machine path) records some value. *)
    Corollary rd_rmbA_update (Hsi : forall o o', slRA o o' -> si o o') t (h : handle FS) i (hR hG hA : nat) :
      EvUpdate IV (GslV rc si (t, h)) (t, h) (IE rc t hA sRmb)
        (fun s => True /\ EdgeG i (t, hG) s /\ liftA (KRecNB rc si (t, h) (IE rc t hR (sRd (Sq i)))) s /\ KHas (t, h) (fR i) s)
        (fun s => ((exists r, liftA (KRec rc si (@RelaxedTraceLin.Build_Op FS (t, h) (fR i) r)) s) \/
                   liftA (KOwns rc si (t, h) isRmb) s) /\ EdgeG i (t, hG) s /\ KHas (t, h) (fR i) s).
    Proof.
      apply (rd_rmb_update Hsi t h i hR hA).
      2: { intros σ σ' p p' γ γ' Hg Hs. apply (edgeG_step i (t, hG) _ σ σ' p p' γ γ' Hg Hs).
           rewrite (regsV_inv_noreg t hA sRmb σ σ' Hs rmb_noreg). apply le_n. }
      intros σ σ' A Pf P P' γ γ' _ _ _ _.
      exists (A i), A, (@RelaxedTraceLin.Build_Op FS (t, h) (fR i) (A i) :: Pf), P'. split; [reflexivity | left; reflexivity].
    Qed.

    (** A linearized read emits no [rmb]: its record puts it at [ls_lini]
        ([ic_rec]), where [Coup] excludes owning an [rmb].  So after the
        LP every later [rmb] slot of the read has a vacuous update. *)
    Lemma krec_rmb_contra k i r (σ : State V) p (γ γ' : Ghost ES FS) t hB :
      IV (σ, p, γ) -> liftA (KRec rc si (@RelaxedTraceLin.Build_Op FS k (fR i) r)) (σ, p, γ) ->
      ghost_emit k (IE rc t hB sRmb) γ γ' -> False.
    Proof.
      intros [HIb _] (A & Pf & P & Hp & Hin) Hge.
      destruct HIb as (A1 & Pf1 & P1 & Hp1 & _ & HC). change (ps_poss (dropS (σ, p, γ))) with p in Hp, Hp1.
      rewrite Hp in Hp1. injection Hp1 as <- <- <-.
      pose proof (ic_rec rc si tw _ _ _ _ _ HC _ Hin) as Hl. cbn [RelaxedTraceLin.op_key RelaxedTraceLin.op_op] in Hl.
      pose proof (ic_coup rc si tw _ _ _ _ _ HC _ Hl) as Hc. rewrite lin_key_make_lin_entry in Hc.
      unfold Coup in Hc. cbn in Hc.
      destruct (ghost_emit_ie rc si k t hB sRmb γ γ' Hge) as (g1 & g2 & Hγ & _ & _).
      enough (Hown : Owns rc si k isRmb γ) by (apply (proj2 Hc) in Hown; discriminate Hown).
      rewrite Hγ.
      exists (Build_ScheduledEvent k (IE rc t hB sRmb)). split; [apply in_or_app; right; left; reflexivity | split; reflexivity].
    Qed.

    (** The final [rd Sq_i] ([κT]): [Pkg ∨ owns an rmb] becomes
        [PkgT ∨ owns an rmb]. *)
    Corollary rd_T_update t (h : handle FS) i (hT : nat) κG κx κy :
      EvUpdate IV (liftGL (GslFix (t, h))) (t, h) (IE rc t hT (sRd (Sq i)))
        (fun s => (Pkg (t, h) i κG κx κy s \/ liftA (KOwns rc si (t, h) isRmb) s) /\ KHas (t, h) (fR i) s)
        (fun s => (PkgT (t, h) i κG κx κy (t, hT) s \/ liftA (KOwns rc si (t, h) isRmb) s) /\ KHas (t, h) (fR i) s).
    Proof.
      apply (rd_noreg_update t h i hT (sRd (Sq i))); [exact (rd_noreg (Sq i)) | discriminate |].
      intros σ σ' p γ γ' [Hp | Ho] _ Hge Hs.
      - left. exact (pkgT_inv (t, h) i κG κx κy t hT σ σ' p γ γ' Hp Hs).
      - right. exact (owns_emit_keep (t, h) isRmb t hT (sRd (Sq i)) γ γ' Ho Hge ltac:(discriminate)).
    Qed.

    (** A response of the read: no abstract step, the guarantee keeps
        the abstract state and the ghost ([GslRes]). *)
    Theorem rd_res_update k t hu o (r : sar o) (Pd Qd : Assn V VF) :
      (forall σ σ' p γ, Pd (σ, p, γ) -> IV (σ, p, γ) ->
         Step V (Build_ThreadEvent t (@ResEv ES hu o r)) σ σ' -> Qd (σ', p, γ)) ->
      EvUpdate IV (liftGL (GslRes k)) k (Build_ThreadEvent t (@ResEv ES hu o r)) Pd Qd.
    Proof.
      intros HQ σ p γ γ' Hd HI Hge σ' Hs. cbn in Hge. subst γ'.
      pose proof HI as [HIb HJ].
      destruct (isl_response_res k t hu o r (fst σ) (fst σ') p γ HIb (stepV_base _ _ _ Hs)) as [HI' Hg].
      exists p. split; [apply rt_refl |]. split; [exact (HQ σ σ' p γ Hd HI Hs) |].
      split; [split; [exact HI' | exact (logok_step (E := ES) δS _ σ σ' Hs HJ)] |].
      split; [exact Hg | exact (log_steps_step VB _ σ σ' Hs)].
    Qed.

    (** The response of a read of [l] on [κ = (t, hu)] with value [v]:
        the in-edge's logged value is [v] (a wrong prophecy makes the step
        impossible), and the post logs it. *)
    Corollary rd_res_krd_update k t hu l (v : nat) (Pd : Assn V VF) w :
      (forall s, Pd s -> KRd (t, hu) l w s) ->
      EvUpdate IV (liftGL (GslRes k)) k (Build_ThreadEvent t (@ResEv ES hu (sRd l) v))
        Pd (fun s => w = v /\ KRd (t, hu) l v s).
    Proof.
      intros Hw. apply rd_res_update. intros σ σ' p γ Hd HI Hs. split.
      - exact (krd_res (t, hu) l w v σ σ' p γ HI (Hw _ Hd) Hs).
      - exact (krd_res_logged t hu l v σ σ' p γ Hs).
    Qed.
    (** A response of a read of [l]: whatever the in-edge, the post logs
        the response value (reader-eval §4: "a response's [fin] follows
        from its own logged event"); [Pd] is carried if it survives the
        memory step. *)
    Corollary rd_res_logged_update k t hu l (v : nat) (Pd : Assn V VF) :
      (forall σ σ' p γ, Pd (σ, p, γ) -> Step V (Build_ThreadEvent t (@ResEv ES hu (sRd l) v)) σ σ' -> Pd (σ', p, γ)) ->
      EvUpdate IV (liftGL (GslRes k)) k (Build_ThreadEvent t (@ResEv ES hu (sRd l) v))
        Pd (fun s => Pd s /\ KRd (t, hu) l v s).
    Proof.
      intros Hc. apply rd_res_update. intros σ σ' p γ Hd _ Hs.
      split; [exact (Hc σ σ' p γ Hd Hs) | exact (krd_res_logged t hu l v σ σ' p γ Hs)].
    Qed.

    (** The response of the final [rd Sq_i] ([κT = (t, hu)]): the final
        edge [PkgT ∨ owns an rmb] is carried, and [κT]'s value is logged. *)
    Corollary rd_resT_update k i κG κx κy t hu (v : nat) :
      EvUpdate IV (liftGL (GslRes k)) k (Build_ThreadEvent t (@ResEv ES hu (sRd (Sq i)) v))
        (fun s => PkgT k i κG κx κy (t, hu) s \/ liftA (KOwns rc si k isRmb) s)
        (fun s => (PkgT k i κG κx κy (t, hu) s \/ liftA (KOwns rc si k isRmb) s) /\ KRd (t, hu) (Sq i) v s).
    Proof.
      apply rd_res_logged_update. intros σ σ' p γ [Hp | Ho] Hs; [left | right; exact Ho].
      apply (pkgT_step k i κG κx κy (t, hu) _ σ σ' p γ γ Hp Hs). rewrite (regsV_res t hu (sRd (Sq i)) v σ σ' Hs). apply le_n.
    Qed.
  End Kit.

End RelaxedHoareSL2InvLog.
