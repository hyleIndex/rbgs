(** * RLHL, part 12: a generic interpreter [run] for method bodies, its
      derived rule [rp_run], the age order [GAge] of the ghost, readiness
      by blocking, and [Done] facts over [EIhl] (RLHL-latch L.1)

    Plan: .rocq-review/tasks/RLHL-latch.md §3 row L.1 (written in the
    RLHL-latch wave 1, which was stopped before its Writer reported;
    iteration-log 2026-10-15).  Reused unchanged by RLHL-seqlock
    (.rocq-review/tasks/RLHL-seqlock.md §3, "Dependency on RLHL-latch
    wave 1"; task .0 pinned the names below) and by
    [RelaxedHoareReady] (RLHL-seqlock .1).  This header was written in
    RLHL-seqlock task .0; the code is as the wave-1 Writer left it.

    ** Part 1: the interpreter
    - [SStep S St R]: one step of a state machine over the operations of
      [S]: [SDone r], or [SCall op dix k] (call [op], tagged with the
      indices [dix] of earlier calls of the same run, continue with
      [k v] on the response [v]).
    - [run next hs st]: the body [FutureD op (dep_of hs dix) (fun f =>
      Wait f (fun v => run next (hs ++ [h_f]) (k v)))].  Every call is
      waited immediately, so the local program is sequential (all
      earlier calls are resolved when the next one is issued) and the
      tag of a call is exactly the handles at the positions [dix]
      ([dep_of]).  All reordering is left to the module frontier
      ((F1)--(F3), [must_precede]), as in Appendix/programlogic.tex:291-293
      (remark "Weak sequential composition": "a method body is run to
      completion before its events are scheduled").  Loops and
      data-dependent branches are machine states.  [run_unfold].
    - The interpreter corresponds to the image of the compilation
      [⟦-⟧] (programlogic.tex:70-94) restricted to one future per
      command, each waited before the next command; [dix] plays the role
      of the dependency tags [deps] (programlogic.tex:295,
      lem:wsc-dep).  This correspondence is argued, not mechanized.

    ** Part 2: run contexts and the dependency dag
    - [RunCtx k Γ H cs]: the slot context and lazy store that [rp_run]
      builds after the calls [cs]: invocation slot of call [j] at
      position [2 j] (tagged with the handles of its [dix], all
      resolved), response slot at [2 j + 1]; [H] holds exactly the
      responses.  Facts: [runctx_store], [runctx_resolved],
      [runctx_inv_at], [runctx_res_at], [runctx_slot], [own_invs_run]
      (the own invocations of the context, in program order).
    - [dprec_run]: the (F1)--(F3) edges of a run context, exactly: into
      the invocation of call [j], from the invocation of an earlier call
      [i] iff [~ semi_independent E (op i) (op j)], and from the response
      of [i] iff [i ∈ dix j]; into the response of [j], only from its own
      invocation.  [dprec_run_inv], [dprec_run_res], [dprec_run_into_inv],
      [dprec_run_into_res].

    ** Part 3: the rule [rp_run]
    - [RunCallOK]/[RunStepOK]: the premises of one machine step from a
      machine invariant [Inv st cs Γ H]: at [SDone r], the continuation
      obligation; at [SCall op dix kc], an invocation slot [si h] and a
      response slot [sr h v] for every fresh handle [h] and every
      response [v], their [NewSlotOK] premises, and [Inv] after the call.
    - [rp_run] (via [RelaxedHoare.RProvable_coind]): a machine invariant
      that every step re-establishes gives [RProvable] for
      [run next (map rc_h cs) st]; [rp_run_start] from the empty context.
    - [run_method_provable]: [MethodProvable I R G M t op Ω Q] for a
      method whose body is [run next [] st0], from [mp_PI], [mp_ret], an
      initial [Inv] and the step premises (with [Close] and the footprint
      [Ω] at [SDone]).

    ** Part 4: the age order of the ghost
    - [key_older ks k1 k2]: [k1] is older than [k2] in the newest-first
      key list [ks].
    - [GAge P γ]: every ghost entry is owned by a call of the pool [P],
      and the entries of an older owner precede those of a younger owner.
    - Preservation: abstract updates that keep the domain
      ([gage_domain], [gage_lin_update], [gage_lin_invoke_update],
      [gage_poss_steps]); invocation of a fresh key with its entries
      appended ([gage_invoke], [gage_poss_invoke]); emission
      ([gage_remove], [gage_ghost_emit]); return of a key with no entry
      left ([gage_lin_remove], [gage_poss_return]); [gage_nil].
    - [gage_before]: an entry of an older owner lies before every entry
      of a younger owner.

    ** Part 5: readiness by blocking
    - [emit_ready_block_older]: at the emission of an invocation [ev] of
      the call [(t, h)] with [ghost_emit] (no earlier entry [inv_blocks
      ev]), if every older [ls_inv] call of thread [t] owns a ghost entry
      that [inv_blocks ev], then [lin_invoke_update t h o P P'] exists
      and keeps the pool well formed: by [GAge] such an entry would be
      earlier, so there is no older [ls_inv] call of [t], and the
      overlay relation [semi_independent F] is never consulted.
      [emit_ready_block]: the same with the premise for every other
      [ls_inv] call of [t]; [gage_after_lp].  Readiness through the
      overlay relation is [RelaxedHoareInherit.emit_ready_SI] and
      [RelaxedHoareReady.emit_ready_mixed].

    ** Part 6: [Done] facts over [EIhl δ]
    - [eihl_done_inv key σ]: [key] was invoked; [eihl_done_res key σ]:
      it was invoked and its record has been consumed.  Both are kept by
      every [EIhl] step of any thread and operation
      ([eihl_done_inv_step(s)], [eihl_done_res_step(s)]), so an edge
      assertion "event [κ] is done" is stable under every rely whose
      memory part is [eihl_steps].  Also [eihl_rec_nodup] (pending
      records have distinct keys) and its preservation,
      [eihl_done_inv_of_inv], [eihl_done_res_of_res],
      [eihl_done_inv_disabled], [eihl_done_res_disabled],
      [eihl_done_res_mine].

    ** Part 7: smoke test
    - [Mrun]: the renaming copy-cat of [RelaxedHoareInherit] with each
      body written as the one-call machine [one_next] under [run] (a
      [FutureD] with the empty tag instead of an untagged [Future]).
      [ren_run_provable] derives it through [run_method_provable], hence
      [rp_run]; [ren_run_methodsem], [ren_run_rlhl2] follow with
      [RelaxedHoareInherit]'s invariant and relations.
    - [RunCounter]: the SI = ∅ FAA→Inc counter instance
      ([counter_run_rlhl2], [counter_run_complin]).

    ** K / S / P / R
    - K (Print Assumptions, Rocq 9.3.0, re-checked in RLHL-seqlock .0):
      73 of the 74 [Theorem]/[Lemma]/[Corollary] results of this file
      are closed under the global context, including [rp_run],
      [run_method_provable], [dprec_run], [own_invs_run], every [gage_*]
      lemma, [emit_ready_block_older], [emit_ready_block], every
      [eihl_done_*] lemma, [ren_run_rlhl2] and
      [RunCounter.counter_run_rlhl2].  The exception is
      [RunCounter.counter_run_complin]: [Classical_Prop.classic],
      inherited from [RelaxedHoareCompLinSpec.rlhl_complin_eihl]; no
      proof in this file uses an axiom directly.
    - S: [rp_run] and [run_method_provable] are derived rules of the
      existing judgement [RProvable]/[MethodProvable] (no new
      soundness argument: [RelaxedHoareSound.method_sound] applies).
      [dprec_run] characterises the own-call dag of a run exactly.  The
      [GAge] and [Done] lemmas are facts about the proof state and the
      [EIhl] presentation; [GAge] is not a field of [RLHL2Hyps], a user
      invariant must carry it.
    - P: no paper statement cites this file.  It is proof
      infrastructure for RLHL instances whose bodies are loops or
      multi-call sequences (Appendix/programlogic.tex, the language of
      §app:lang and the rules of §app:program-logic).
    - R: infrastructure for the planned RLHL LatchSet (paused) and the
      RLHL SeqLock (popl2027-reviews.md:215, "No example verified on the
      COH model"; used by [RelaxedHoareSL2Write] and
      [RelaxedHoareSL2Read]); by itself it answers no reviewer concern.

    ** Limitations
    - The smoke test of this file exercises only one-call bodies.  The
      first multi-call and looping uses of [rp_run] are done elsewhere:
      [RelaxedHoareSL2Write.write_provable] (the seven-call
      straight-line SeqLock writer, over [EIhl]) and
      [RelaxedHoareSL2Read.read_provable_v] (the looping SeqLock reader,
      over [EIhlv]), both through [run_method_provable].  This retires
      the risk listed in the RLHL-seqlock plan (§3, "Risks") for these
      two bodies.
    - [run] waits every call immediately; bodies with several
      outstanding local futures are outside its image.  Indices in [dix]
      that do not name an earlier call (out of range) contribute no tag.
    - [emit_ready_block(_older)] needs a blocking ghost entry for every
      older [ls_inv] call of the thread; at a non-empty overlay relation
      use [RelaxedHoareReady.emit_ready_mixed]/[emit_ready_rec].
    - Part 6 is specific to the handle-linear presentation [EIhl δ].

    ** Plan check (RLHL-seqlock .0, against RLHL-latch.md §3 L.1)
    All L.1 items are present: [SStep]/[dep_of]/[run]/[run_unfold];
    [rp_run] via [RProvable_coind]; [dprec_run] (Inv–Inv iff ¬SI,
    Res_i→Inv_j iff [i ∈ dix_j], Inv_j→Res_j); [GAge] and its
    preservation under invoke/emit/return/[lin_update]; [emit_ready_block];
    monotonicity of [Done] under [EIhl]; the smoke test (Part 7, the
    [RelaxedHoareInherit] renaming and a counter, re-derived through
    [run_method_provable]). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Operators.

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
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.

Import ListNotations.


Module RelaxedHoareRun.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.

  (** ** Part 1. The interpreter *)

  (** A step of a state machine over the operations of [S]: done with a
      result, or one call [op] tagged with the indices [dix] (positions
      among the method's earlier calls) of the calls it depends on, whose
      result is passed to [k]. *)
  Inductive SStep (S : Sig.t) (St R : Type) : Type :=
  | SDone (r : R)
  | SCall (op : Sig.op S) (dix : list nat) (k : Sig.ar op -> St).

  (** Bidirectionality hints ([&]): the expected type fixes [S] before
      [op] is typed, so that a machine over a concrete signature (e.g. a
      [match] returning [SStep LSig _ _]) can use its own operation type. *)
  Arguments SDone {S St R} & r.
  Arguments SCall {S St R} & op dix k.

  (** The handles of [dix], read off the handles [hs] of the earlier calls. *)
  Definition dep_of {A : Type} (hs : list A) (dix : list nat) (q : A) : Prop :=
    exists i, In i dix /\ nth_error hs i = Some q.

  Section Run.
    Context {G : RelaxedSig.t}.

    (** The interpreter: every call is a [FutureD] tagged with the handles
        of [dix], immediately waited.  [hs] are the handles of the
        method's calls so far, in program order. *)
    CoFixpoint run {St R : Type} (next : St -> SStep (effect G) St R) (hs : list (handle G)) (st : St) :
        Prog G R :=
      match next st with
      | SDone r => Ret r
      | SCall op dix k =>
          FutureD op (dep_of hs dix) (fun f => Wait f (fun v => run next (hs ++ [future_handle f]) (k v)))
      end.

    Lemma run_unfold {St R} (next : St -> SStep (effect G) St R) hs st :
      run next hs st =
      match next st with
      | SDone r => Ret r
      | SCall op dix k =>
          FutureD op (dep_of hs dix) (fun f => Wait f (fun v => run next (hs ++ [future_handle f]) (k v)))
      end.
    Proof.
      rewrite (PPid (run next hs st)) at 1. cbv beta iota delta [PP run].
      destruct (next st); reflexivity.
    Qed.
  End Run.

  (** ** Part 2. Run contexts and the dependency dag of a run *)

  (** A call of a run: its handle, its operation and its tag indices. *)
  Record RCall (E : RelaxedSig.t) : Type := mkRCall {
    rc_h : handle E;
    rc_op : Sig.op (effect E);
    rc_dix : list nat
  }.

  Arguments mkRCall {E} _ _ _.
  Arguments rc_h {E} _.
  Arguments rc_op {E} _.
  Arguments rc_dix {E} _.

  Lemma resolve_add_pending {E : RelaxedSig.t} (H H' : FutureStore E) h op (v : Sig.ar op) :
    resolve_store h op v (add_pending h op H) H' -> H' = Build_FutureEntry h (Resolved op v) :: H.
  Proof.
    unfold add_pending. intros Hres.
    inversion Hres as [tail | h' cell H0 H0' Hneq Hres0]; subst; [reflexivity |].
    exfalso. apply Hneq. reflexivity.
  Qed.

  Lemma run_nodup_snoc {A : Type} (l : list A) x : NoDup l -> ~ In x l -> NoDup (l ++ [x]).
  Proof.
    induction l as [| a l IH]; cbn; intros Hnd Hx.
    - constructor; [intros [] | constructor].
    - apply NoDup_cons_iff in Hnd as [Ha Hnd]. constructor.
      + intros Hin. apply in_app_or in Hin as [Hin | [<- | []]]; [exact (Ha Hin) | apply Hx; left; reflexivity].
      + apply IH; [exact Hnd |]. intros Hin. apply Hx. right. exact Hin.
  Qed.

  Lemma nodup_nth_inj {A : Type} (l : list A) i j x :
    NoDup l -> nth_error l i = Some x -> nth_error l j = Some x -> i = j.
  Proof.
    intros Hnd Hi Hj. apply (proj1 (NoDup_nth_error l) Hnd i j); [apply nth_error_Some; rewrite Hi; discriminate |].
    rewrite Hi, Hj. reflexivity.
  Qed.

  Section Ctx.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (k : CallKey F).
    Local Abbreviation SlotT := (Slot VE VF).

    (** The contexts built by [rp_run] (Part 3): one pair of slots per call
        of the run, the invocation at position [2 j] (tagged with the
        handles of its [dix], all resolved), the response at [2 j + 1]; the
        lazy store holds exactly the responses of the run's calls. *)
    Inductive RunCtx : list SlotT -> FutureStore E -> list (RCall E) -> Prop :=
    | runctx_nil : RunCtx [] empty_store []
    | runctx_snoc Γ H cs (si sr : SlotT) h op dix (v : Sig.ar op) H' :
        RunCtx Γ H cs ->
        handle_fresh h H ->
        sl_ev si = invD_tev k H (dep_of (map rc_h cs) dix) h op ->
        sl_ev sr = res_tev k h op v ->
        resolve_store h op v (add_pending h op H) H' ->
        RunCtx ((Γ ++ [si]) ++ [sr]) H' (cs ++ [mkRCall h op dix]).

    Lemma runctx_store Γ H cs :
      RunCtx Γ H cs ->
      map (fe_handle E) H = rev (map rc_h cs) /\ all_resolved H /\ NoDup (map rc_h cs).
    Proof.
      induction 1 as [| Γ H cs si sr h op dix v H' Hc IH Hf Hsi Hsr Hres].
      - split; [reflexivity |]. split; constructor.
      - destruct IH as (Hh & Hall & Hnd). rewrite (resolve_add_pending _ _ _ _ _ Hres).
        split; [cbn; rewrite map_app, rev_app_distr, Hh; reflexivity |].
        split; [constructor; [exact Logic.I | exact Hall] |].
        rewrite map_app. apply run_nodup_snoc; [exact Hnd |].
        intros Hin. apply Hf. rewrite Hh. apply in_rev. rewrite rev_involutive. exact Hin.
    Qed.

    Lemma runctx_resolved Γ H cs q :
      RunCtx Γ H cs -> (resolved_in H q <-> In q (map rc_h cs)).
    Proof.
      intros Hc. destruct (runctx_store Γ H cs Hc) as (Hh & Hall & _). split.
      - intros (op & r & Hin). apply in_rev. rewrite <- Hh. exact (in_map (fe_handle E) _ _ Hin).
      - intros Hq. apply in_rev in Hq. rewrite <- Hh in Hq.
        apply in_map_iff in Hq as ([h c] & Eh & Hin). cbn in Eh. subst h.
        unfold all_resolved in Hall. rewrite Forall_forall in Hall. specialize (Hall _ Hin). cbn in Hall.
        destruct c as [o | o r]; [contradiction |]. exists o, r. exact Hin.
    Qed.

    Lemma runctx_fresh Γ H cs h : RunCtx Γ H cs -> handle_fresh h H -> ~ In h (map rc_h cs).
    Proof.
      intros Hc Hf Hin. apply Hf. destruct (runctx_store Γ H cs Hc) as (Hh & _). rewrite Hh.
      apply in_rev. rewrite rev_involutive. exact Hin.
    Qed.

    Lemma runctx_len Γ H cs : RunCtx Γ H cs -> length Γ = 2 * length cs.
    Proof.
      induction 1 as [| Γ H cs si sr h op dix v H' Hc IH]; [reflexivity |].
      rewrite !length_app, IH. cbn. lia.
    Qed.

    Lemma firstn_snoc_le {A : Type} (l : list A) x j : j <= length l -> firstn j (l ++ [x]) = firstn j l.
    Proof.
      intros Hj. rewrite firstn_app. replace (j - length l) with 0 by lia. rewrite firstn_O, app_nil_r. reflexivity.
    Qed.

    (** The invocation slot of the [j]-th call: the event and its tag. *)
    Lemma runctx_inv_at Γ H cs j c :
      RunCtx Γ H cs -> nth_error cs j = Some c ->
      exists si, nth_error Γ (2 * j) = Some si /\
        untag (sl_ev si) = Build_ThreadEvent (fst k) (InvEv (rc_h c) (rc_op c)) /\
        (forall q, tev_deps (sl_ev si) q <-> dep_of (map rc_h (firstn j cs)) (rc_dix c) q).
    Proof.
      intros Hc. revert j c. induction Hc as [| Γ H cs si sr h op dix v H' Hc IH Hf Hsi Hsr Hres]; intros j c Hj.
      - destruct j; discriminate.
      - pose proof (runctx_len _ _ _ Hc) as Hlen.
        destruct (Nat.lt_ge_cases j (length cs)) as [Hlt | Hge].
        + rewrite nth_error_app1 in Hj by exact Hlt.
          destruct (IH j c Hj) as (si0 & Hs0 & Hev & Htag). exists si0.
          split; [rewrite <- app_assoc, nth_error_app1 by lia; exact Hs0 |]. split; [exact Hev |].
          rewrite firstn_snoc_le by lia. exact Htag.
        + assert (Hj' : j = length cs).
          { apply nth_error_lt in Hj. rewrite length_app in Hj. cbn in Hj. lia. }
          subst j. rewrite nth_error_app2 in Hj by lia. rewrite Nat.sub_diag in Hj. cbn in Hj.
          injection Hj as <-. exists si.
          split; [rewrite <- app_assoc, nth_error_app2 by lia; rewrite Hlen, Nat.sub_diag; reflexivity |].
          rewrite Hsi. split; [reflexivity |]. cbn [rc_h rc_op rc_dix tev_deps invD_tev].
          rewrite firstn_snoc_le, firstn_all by lia. intros q. split; [intros [Hq _]; exact Hq |].
          intros Hq. split; [exact Hq |]. apply (runctx_resolved Γ H cs q Hc).
          destruct Hq as (i & _ & Hi). exact (nth_error_In _ _ Hi).
    Qed.

    (** The response slot of the [j]-th call. *)
    Lemma runctx_res_at Γ H cs j c :
      RunCtx Γ H cs -> nth_error cs j = Some c ->
      exists sr (v : Sig.ar (rc_op c)), nth_error Γ (S (2 * j)) = Some sr /\
        untag (sl_ev sr) = Build_ThreadEvent (fst k) (ResEv (rc_h c) (rc_op c) v).
    Proof.
      intros Hc. revert j c. induction Hc as [| Γ H cs si sr h op dix v H' Hc IH Hf Hsi Hsr Hres]; intros j c Hj.
      - destruct j; discriminate.
      - pose proof (runctx_len _ _ _ Hc) as Hlen.
        destruct (Nat.lt_ge_cases j (length cs)) as [Hlt | Hge].
        + rewrite nth_error_app1 in Hj by exact Hlt.
          destruct (IH j c Hj) as (sr0 & v0 & Hs0 & Hev). exists sr0, v0.
          split; [rewrite <- app_assoc, nth_error_app1 by lia; exact Hs0 | exact Hev].
        + assert (Hj' : j = length cs).
          { apply nth_error_lt in Hj. rewrite length_app in Hj. cbn in Hj. lia. }
          subst j. rewrite nth_error_app2 in Hj by lia. rewrite Nat.sub_diag in Hj. cbn in Hj.
          injection Hj as <-. exists sr, v.
          split; [rewrite <- app_assoc, nth_error_app2 by lia; rewrite Hlen; replace (S (2 * length cs) - 2 * length cs) with 1 by lia; reflexivity |].
          rewrite Hsr. reflexivity.
    Qed.

    (** Every slot of a run context is the invocation or the response of
        one of its calls. *)
    Lemma runctx_slot Γ H cs n s :
      RunCtx Γ H cs -> nth_error Γ n = Some s ->
      exists j c, nth_error cs j = Some c /\
        ((n = 2 * j /\ untag (sl_ev s) = Build_ThreadEvent (fst k) (InvEv (rc_h c) (rc_op c)) /\
          (forall q, tev_deps (sl_ev s) q <-> dep_of (map rc_h (firstn j cs)) (rc_dix c) q)) \/
         (n = S (2 * j) /\ exists v : Sig.ar (rc_op c),
            untag (sl_ev s) = Build_ThreadEvent (fst k) (ResEv (rc_h c) (rc_op c) v))).
    Proof.
      intros Hc Hn. pose proof (runctx_len _ _ _ Hc) as Hlen.
      assert (Hnl : n < length Γ) by (apply nth_error_Some; rewrite Hn; discriminate).
      destruct (Nat.Even_or_Odd n) as [[j Hj] | [j Hj]].
      - destruct (nth_error cs j) as [c |] eqn:Hcj; [| apply nth_error_None in Hcj; lia].
        exists j, c. split; [exact Hcj |]. left.
        destruct (runctx_inv_at Γ H cs j c Hc Hcj) as (si & Hsi & Hev & Htag).
        subst n. rewrite Hsi in Hn. injection Hn as <-. auto.
      - destruct (nth_error cs j) as [c |] eqn:Hcj; [| apply nth_error_None in Hcj; lia].
        exists j, c. split; [exact Hcj |]. right.
        destruct (runctx_res_at Γ H cs j c Hc Hcj) as (sr & v & Hsr & Hev).
        replace n with (S (2 * j)) in Hn by lia. rewrite Hsr in Hn. injection Hn as <-.
        split; [lia |]. exists v. exact Hev.
    Qed.

    (** The own invocations of a run context, in program order. *)
    Lemma own_invs_run Γ H cs :
      RunCtx Γ H cs -> own_invs Γ = map (fun c => Build_ThreadEvent (fst k) (InvEv (rc_h c) (rc_op c))) cs.
    Proof.
      induction 1 as [| Γ H cs si sr h op dix v H' Hc IH Hf Hsi Hsr Hres]; [reflexivity |].
      unfold own_invs, evs in *. rewrite !map_app, !inv_events_app, IH. cbn. rewrite Hsi, Hsr. cbn.
      rewrite app_nil_r. reflexivity.
    Qed.

    Lemma nth_error_evs (Γ : list SlotT) n : nth_error (evs Γ) n = option_map (@sl_ev E F VE VF) (nth_error Γ n).
    Proof. unfold evs. apply nth_error_map. Qed.

    Lemma dep_of_run (cs : list (RCall E)) (dix : list nat) i (ci : RCall E) :
      NoDup (map rc_h cs) -> nth_error cs i = Some ci ->
      (dep_of (map rc_h cs) dix (rc_h ci) <-> In i dix).
    Proof.
      intros Hnd Hi. assert (Hi' : nth_error (map rc_h cs) i = Some (rc_h ci)) by (rewrite nth_error_map, Hi; reflexivity).
      split.
      - intros (i' & Hin & Hi''). rewrite (nodup_nth_inj _ _ _ _ Hnd Hi' Hi''). exact Hin.
      - intros Hin. exists i. auto.
    Qed.

    (** (F1)--(F3) edges into a new invocation slot of a run: from an
        earlier invocation iff the two operations are not
        semi-independent; from an earlier response iff its index is in the
        tag [dix]. *)
    Lemma dprec_run_inv Γ H cs (si : SlotT) h op dix d :
      RunCtx Γ H cs -> sl_ev si = invD_tev k H (dep_of (map rc_h cs) dix) h op ->
      (dprec (evs (Γ ++ [si])) d (length Γ) <->
       exists i ci, nth_error cs i = Some ci /\
         ((d = 2 * i /\ ~ semi_independent E (rc_op ci) op) \/ (d = S (2 * i) /\ In i dix))).
    Proof.
      intros Hc Hsi. destruct (runctx_store Γ H cs Hc) as (_ & _ & Hnd).
      assert (Hlast : nth_error (evs (Γ ++ [si])) (length Γ) = Some (sl_ev si)).
      { rewrite evs_app, nth_error_app2 by (rewrite length_evs; lia). rewrite length_evs, Nat.sub_diag. reflexivity. }
      split.
      - intros Hd. inversion Hd as [d0 j0 a b Hlt Ha Hb Hm]; subst d0 j0.
        rewrite Hlast in Hb. injection Hb as <-.
        rewrite evs_app, nth_error_app1 in Ha by (rewrite length_evs; exact Hlt).
        rewrite nth_error_evs in Ha. destruct (nth_error Γ d) as [s |] eqn:Hs; [| discriminate Ha].
        cbn in Ha. injection Ha as <-.
        destruct (runctx_slot Γ H cs d s Hc Hs) as (j & c & Hj & [(-> & Hev & _) | (-> & v & Hev)]);
          exists j, c; split; [exact Hj | | exact Hj |].
        + left. split; [reflexivity |]. unfold must_precede in Hm. rewrite Hev, Hsi in Hm. exact Hm.
        + right. split; [reflexivity |]. unfold must_precede in Hm. rewrite Hev, Hsi in Hm. cbn in Hm.
          destruct Hm as [Hm _]. exact (proj1 (dep_of_run cs dix j c Hnd Hj) Hm).
      - intros (i & ci & Hi & [(-> & Hn) | (-> & Hin)]).
        + destruct (runctx_inv_at Γ H cs i ci Hc Hi) as (s & Hs & Hev & _).
          pose proof (runctx_len _ _ _ Hc) as Hlen. pose proof (nth_error_lt _ _ _ Hi).
          apply (dprec_intro _ _ _ (sl_ev s) (sl_ev si)); [lia | | exact Hlast |].
          * rewrite evs_app, nth_error_app1 by (rewrite length_evs; lia). rewrite nth_error_evs, Hs. reflexivity.
          * unfold must_precede. rewrite Hev, Hsi. exact Hn.
        + destruct (runctx_res_at Γ H cs i ci Hc Hi) as (s & v & Hs & Hev).
          pose proof (runctx_len _ _ _ Hc) as Hlen. pose proof (nth_error_lt _ _ _ Hi).
          apply (dprec_intro _ _ _ (sl_ev s) (sl_ev si)); [lia | | exact Hlast |].
          * rewrite evs_app, nth_error_app1 by (rewrite length_evs; lia). rewrite nth_error_evs, Hs. reflexivity.
          * unfold must_precede. rewrite Hev, Hsi. cbn. split; [exact (proj2 (dep_of_run cs dix i ci Hnd Hi) Hin) |].
            apply (runctx_resolved Γ H cs _ Hc). exact (nth_error_In _ _ (eq_trans (nth_error_map _ _ _) (f_equal (option_map rc_h) Hi))).
    Qed.

    (** The only (F1)--(F3) edge into a new response slot of a run is from
        its own invocation. *)
    Lemma dprec_run_res Γ H cs (si sr : SlotT) h op dix (v : Sig.ar op) d :
      RunCtx Γ H cs -> handle_fresh h H ->
      sl_ev si = invD_tev k H (dep_of (map rc_h cs) dix) h op -> sl_ev sr = res_tev k h op v ->
      (dprec (evs ((Γ ++ [si]) ++ [sr])) d (S (length Γ)) <-> d = length Γ).
    Proof.
      intros Hc Hf Hsi Hsr.
      assert (Hlast : nth_error (evs ((Γ ++ [si]) ++ [sr])) (S (length Γ)) = Some (sl_ev sr)).
      { rewrite evs_app, nth_error_app2 by (rewrite length_evs, length_app; cbn; lia).
        rewrite length_evs, length_app. cbn [length]. replace (S (length Γ) - (length Γ + 1)) with 0 by lia. reflexivity. }
      assert (Hpen : nth_error (evs ((Γ ++ [si]) ++ [sr])) (length Γ) = Some (sl_ev si)).
      { rewrite evs_app, nth_error_app1 by (rewrite length_evs, length_app; cbn; lia).
        rewrite evs_app, nth_error_app2 by (rewrite length_evs; lia). rewrite length_evs, Nat.sub_diag. reflexivity. }
      split.
      - intros Hd. inversion Hd as [d0 j0 a b Hlt Ha Hb Hm]; subst d0 j0.
        rewrite Hlast in Hb. injection Hb as <-.
        destruct (Nat.eq_dec d (length Γ)) as [-> | Hne]; [reflexivity | exfalso].
        rewrite evs_app, nth_error_app1 in Ha by (rewrite length_evs, length_app; cbn; lia).
        rewrite evs_app, nth_error_app1 in Ha by (rewrite length_evs; lia).
        rewrite nth_error_evs in Ha. destruct (nth_error Γ d) as [s |] eqn:Hs; [| discriminate Ha].
        cbn in Ha. injection Ha as <-.
        destruct (runctx_slot Γ H cs d s Hc Hs) as (j & c & Hj & [(_ & Hev & _) | (_ & w & Hev)]);
          unfold must_precede in Hm; rewrite Hev, Hsr in Hm; cbn in Hm; [| exact Hm].
        apply (runctx_fresh Γ H cs h Hc Hf). rewrite <- Hm.
        exact (nth_error_In _ _ (eq_trans (nth_error_map _ _ _) (f_equal (option_map rc_h) Hj))).
      - intros ->. apply (dprec_intro _ _ _ (sl_ev si) (sl_ev sr)); [lia | exact Hpen | exact Hlast |].
        unfold must_precede. rewrite Hsi, Hsr. reflexivity.
    Qed.

    (** The whole dag of a run context ([dprec_run]): into the invocation
        of call [j], the edges of [dprec_run_inv]; into its response, the
        edge from its own invocation. *)
    Theorem dprec_run Γ H cs a b :
      RunCtx Γ H cs ->
      (dprec (evs Γ) a b <->
       exists j c, nth_error cs j = Some c /\
         ((b = 2 * j /\ exists i ci, nth_error cs i = Some ci /\ i < j /\
             ((a = 2 * i /\ ~ semi_independent E (rc_op ci) (rc_op c)) \/ (a = S (2 * i) /\ In i (rc_dix c)))) \/
          (b = S (2 * j) /\ a = 2 * j))).
    Proof.
      intros Hc. revert a b. induction Hc as [| Γ H cs si sr h op dix v H' Hc IH Hf Hsi Hsr Hres]; intros a b.
      - split; [intros Hd; apply dprec_bound in Hd; cbn in Hd; lia |].
        intros (j & c & Hj & _). destruct j; discriminate.
      - pose proof (runctx_len _ _ _ Hc) as Hlen.
        assert (Hev2 : evs ((Γ ++ [si]) ++ [sr]) = evs Γ ++ [sl_ev si; sl_ev sr]) by (rewrite !evs_app, <- app_assoc; reflexivity).
        assert (Hlt_cs : forall j c, nth_error (cs ++ [mkRCall h op dix]) j = Some c -> j < length cs ->
                           nth_error cs j = Some c) by (intros j c Hj Hl; rewrite nth_error_app1 in Hj by exact Hl; exact Hj).
        assert (Hlast_cs : nth_error (cs ++ [mkRCall h op dix]) (length cs) = Some (mkRCall h op dix))
          by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
        destruct (Nat.lt_ge_cases b (length Γ)) as [Hb | Hb].
        + rewrite Hev2, dprec_app_iff by (rewrite length_evs; exact Hb). rewrite IH. split.
          * intros (j & c & Hj & Hcase). exists j, c.
            assert (Hjl : j < length cs) by (apply nth_error_lt in Hj; exact Hj).
            split; [rewrite nth_error_app1 by exact Hjl; exact Hj |].
            destruct Hcase as [(-> & i & ci & Hi & Hij & Hc') | (-> & ->)]; [left | right; auto].
            split; [reflexivity |]. exists i, ci. split; [rewrite nth_error_app1 by lia; exact Hi | auto].
          * intros (j & c & Hj & Hcase).
            assert (Hjl : j < length cs) by (destruct Hcase as [(-> & _) | (-> & _)]; lia).
            exists j, c. split; [exact (Hlt_cs j c Hj Hjl) |].
            destruct Hcase as [(-> & i & ci & Hi & Hij & Hc') | (-> & ->)]; [left | right; auto].
            split; [reflexivity |]. exists i, ci. split; [exact (Hlt_cs i ci Hi ltac:(lia)) | auto].
        + destruct (Nat.eq_dec b (length Γ)) as [-> | Hb2].
          * assert (Hev1 : evs ((Γ ++ [si]) ++ [sr]) = evs (Γ ++ [si]) ++ [sl_ev sr]) by (rewrite evs_app; reflexivity).
            rewrite Hev1, dprec_app_iff by (rewrite length_evs, length_app; cbn; lia).
            rewrite (dprec_run_inv Γ H cs si h op dix a Hc Hsi). split.
            -- intros (i & ci & Hi & Hcase). exists (length cs), (mkRCall h op dix).
               split; [exact Hlast_cs |]. left. split; [lia |].
               exists i, ci. pose proof (nth_error_lt _ _ _ Hi).
               split; [rewrite nth_error_app1 by lia; exact Hi |]. split; [lia | exact Hcase].
            -- intros (j & c & Hj & [(Hbj & i & ci & Hi & Hij & Hcase) | (Hbj & _)]); [| lia].
               assert (j = length cs) by lia. subst j. rewrite Hlast_cs in Hj. injection Hj as <-.
               exists i, ci. split; [exact (Hlt_cs i ci Hi Hij) | exact Hcase].
          * assert (Hb3 : b = S (length Γ) \/ b > S (length Γ)) by lia.
            destruct Hb3 as [-> | Hb3].
            -- rewrite (dprec_run_res Γ H cs si sr h op dix v a Hc Hf Hsi Hsr). split.
               ++ intros ->. exists (length cs), (mkRCall h op dix). split; [exact Hlast_cs |]. right. lia.
               ++ intros (j & c & Hj & [(Hbj & _) | (Hbj & ->)]); lia.
            -- split.
               ++ intros Hd. apply dprec_bound in Hd. rewrite length_evs, !length_app in Hd. cbn in Hd. lia.
               ++ intros (j & c & Hj & Hcase). apply nth_error_lt in Hj. rewrite length_app in Hj. cbn in Hj.
                  destruct Hcase as [(-> & _) | (-> & _)]; lia.
    Qed.

    Corollary dprec_run_into_inv Γ H cs j c a :
      RunCtx Γ H cs -> nth_error cs j = Some c ->
      (dprec (evs Γ) a (2 * j) <->
       exists i ci, nth_error cs i = Some ci /\ i < j /\
         ((a = 2 * i /\ ~ semi_independent E (rc_op ci) (rc_op c)) \/ (a = S (2 * i) /\ In i (rc_dix c)))).
    Proof.
      intros Hc Hj. rewrite (dprec_run Γ H cs a (2 * j) Hc). split.
      - intros (j' & c' & Hj' & [(Hb & Hrest) | (Hb & _)]); [| lia].
        assert (j' = j) by lia. subst j'. rewrite Hj in Hj'. injection Hj' as <-. exact Hrest.
      - intros Hrest. exists j, c. split; [exact Hj |]. left. auto.
    Qed.

    Corollary dprec_run_into_res Γ H cs j c a :
      RunCtx Γ H cs -> nth_error cs j = Some c -> (dprec (evs Γ) a (S (2 * j)) <-> a = 2 * j).
    Proof.
      intros Hc Hj. rewrite (dprec_run Γ H cs a (S (2 * j)) Hc). split.
      - intros (j' & c' & Hj' & [(Hb & _) | (Hb & ->)]); lia.
      - intros ->. exists j, c. split; [exact Hj |]. right. auto.
    Qed.
  End Ctx.

  (** ** Part 3. The rule [rp_run] *)

  Section RunRule.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF).
    Context (k : CallKey F) (Pinit : Assn VE VF).
    Local Abbreviation SlotT := (Slot VE VF).
    Local Abbreviation NewOK := (NewSlotOK I R G k Pinit).
    Context {St A : Type} (next : St -> SStep (effect E) St A).

    (** The premises of one call of the machine, from the context [Γ] and
        lazy store [H] built for the calls [cs]: an invocation slot [si h]
        and a response slot [sr h v] for every fresh handle [h] and every
        response [v], their [NewSlotOK] premises, and the machine invariant
        [Inv] after the call (which may use the run context reached). *)
    Definition RunCallOK (Inv : St -> list (RCall E) -> list SlotT -> FutureStore E -> Prop)
        (cs : list (RCall E)) (Γ : list SlotT) (H : FutureStore E)
        (op : Sig.op (effect E)) (dix : list nat) (kc : Sig.ar op -> St)
        (si : handle E -> SlotT) (sr : handle E -> Sig.ar op -> SlotT) : Prop :=
      (forall h, sl_ev (si h) = invD_tev k H (dep_of (map rc_h cs) dix) h op) /\
      (forall h, handle_fresh h H -> NewOK Γ (si h)) /\
      (forall h v, sl_ev (sr h v) = res_tev k h op v) /\
      (forall h v, handle_fresh h H -> NewOK (Γ ++ [si h]) (sr h v)) /\
      (forall h v H', handle_fresh h H -> resolve_store h op v (add_pending h op H) H' ->
         RunCtx k ((Γ ++ [si h]) ++ [sr h v]) H' (cs ++ [mkRCall h op dix]) ->
         Inv (kc v) (cs ++ [mkRCall h op dix]) ((Γ ++ [si h]) ++ [sr h v]) H').

    (** The premise of one machine step: the continuation obligation at
        [SDone], [RunCallOK] at [SCall].  A [Definition] by [match], so
        that a concrete machine reduces it by computation. *)
    Definition RunStepOK (Inv : St -> list (RCall E) -> list SlotT -> FutureStore E -> Prop)
        (K : A -> list SlotT -> FutureStore E -> Prop)
        (cs : list (RCall E)) (Γ : list SlotT) (H : FutureStore E) (s : SStep (effect E) St A) : Prop :=
      match s with
      | SDone r => K r Γ H
      | SCall op dix kc => exists si sr, RunCallOK Inv cs Γ H op dix kc si sr
      end.

    (** The rule: a machine invariant [Inv] (on the machine state, the run's
        calls, the slot context and the lazy store) that every step
        re-establishes gives a derivation of [run next]. *)
    Theorem rp_run (Inv : St -> list (RCall E) -> list SlotT -> FutureStore E -> Prop)
        (K : A -> list SlotT -> FutureStore E -> Prop) :
      (forall st cs Γ H, RunCtx k Γ H cs -> Inv st cs Γ H -> RunStepOK Inv K cs Γ H (next st)) ->
      forall st cs Γ H, RunCtx k Γ H cs -> Inv st cs Γ H ->
        RProvable I R G k Pinit K Γ H (run next (map rc_h cs) st).
    Proof.
      intros Hstep st0 cs0 Γ0 H0 Hc0 Hi0.
      apply (RProvable_coind I R G k Pinit K
        (fun Γ H p =>
           (exists (st : St) (cs : list (RCall E)), p = run next (map rc_h cs) st /\ RunCtx k Γ H cs /\ Inv st cs Γ H) \/
           (exists (cs : list (RCall E)) (Γ1 : list SlotT) (H1 : FutureStore E) (op : Sig.op (effect E))
              (dix : list nat) (kc : Sig.ar op -> St) (si : handle E -> SlotT) (sr : handle E -> Sig.ar op -> SlotT)
              (h : handle E),
              RunCtx k Γ1 H1 cs /\ RunCallOK Inv cs Γ1 H1 op dix kc si sr /\ handle_fresh h H1 /\
              Γ = Γ1 ++ [si h] /\ H = add_pending h op H1 /\
              p = Wait (MkFutureRef op h) (fun v => run next (map rc_h cs ++ [h]) (kc v)))));
        [| left; exists st0, cs0; auto].
      clear st0 cs0 Γ0 H0 Hc0 Hi0.
      intros Γ H p [(st & cs & -> & Hc & Hi) | (cs & Γ1 & H1 & op & dix & kc & si & sr & h & Hc & Hok & Hf & -> & -> & ->)].
      - pose proof (Hstep st cs Γ H Hc Hi) as Hs. rewrite run_unfold.
        destruct (next st) as [r | op dix kc]; cbn in Hs |- *; [exact Hs |].
        destruct Hs as (si & sr & Hok). pose proof Hok as (Hsi & Hnsi & _).
        exists si. split; [exact Hsi |]. split; [exact Hnsi |].
        intros h Hf. right. exists cs, Γ, H, op, dix, kc, si, sr, h. auto 7.
      - cbn. right. pose proof Hok as (_ & _ & Hsr & Hnsr & Hinv). exists (sr h).
        split; [left; reflexivity |]. split; [intros v; apply Hsr |]. split; [intros v; apply Hnsr; exact Hf |].
        intros v H' Hres. left. exists (kc v), (cs ++ [mkRCall h op dix]).
        split; [rewrite map_app; reflexivity |].
        assert (Hc' : RunCtx k ((Γ1 ++ [si h]) ++ [sr h v]) H' (cs ++ [mkRCall h op dix]))
          by (apply (runctx_snoc k Γ1 H1 cs (si h) (sr h v) h op dix v H' Hc Hf); [apply Hok | apply Hsr | exact Hres]).
        split; [exact Hc' |]. apply Hinv; assumption.
    Qed.

    (** The rule from the start of a method body. *)
    Corollary rp_run_start (Inv : St -> list (RCall E) -> list SlotT -> FutureStore E -> Prop)
        (K : A -> list SlotT -> FutureStore E -> Prop) st0 :
      (forall st cs Γ H, RunCtx k Γ H cs -> Inv st cs Γ H -> RunStepOK Inv K cs Γ H (next st)) ->
      Inv st0 [] [] empty_store ->
      RProvable I R G k Pinit K [] empty_store (run next [] st0).
    Proof. intros Hstep Hi0. exact (rp_run Inv K Hstep st0 [] [] empty_store (runctx_nil k) Hi0). Qed.
  End RunRule.

  (** The method level: a method whose body is a [run] is provable from a
      machine invariant (per overlay handle [h]). *)
  Section RunMethod.
    Context {E F : RelaxedSig.t} {VE : LTS E} {VF : LTS F}.
    Context (I : Assn VE VF) (R G : CallKey F -> PRel VE VF) (M : RelaxedModuleImpl E F).

    Corollary run_method_provable (t : tid) (op : Sig.op (effect F))
        (Ω : handle F -> list (ThreadEvent E) -> Prop) (Q : handle F -> Sig.ar op -> Assn VE VF)
        {St : Type} (next : St -> SStep (effect E) St (Sig.ar op)) (st0 : St)
        (Inv : handle F -> St -> list (RCall E) -> list (Slot VE VF) -> FutureStore E -> Prop) :
      M op t = run next [] st0 ->
      (forall h s, PostInvoke I (t, h) op (Ω h) s -> I s) ->
      (forall h r s, Q h r s -> I s -> NoOwn (t, h) (ps_ghost s) -> RetCond I G (t, h) op r s) ->
      (forall h, Inv h st0 [] [] empty_store) ->
      (forall h st cs Γ H, RunCtx (t, h) Γ H cs -> Inv h st cs Γ H ->
         RunStepOK I R G (t, h) (PostInvoke I (t, h) op (Ω h)) (Inv h)
           (fun a Γ' H' => Close I R G (t, h) (PostInvoke I (t, h) op (Ω h)) (Q h) a Γ' H' /\ Ω h (own_invs Γ'))
           cs Γ H (next st)) ->
      MethodProvable I R G M t op Ω Q.
    Proof.
      intros HM HPI Hret Hi0 Hstep. constructor; [exact HPI | exact Hret |].
      intros h. rewrite HM. apply (rp_run_start I R G (t, h) _ next (Inv h)); [| apply Hi0].
      intros st cs Γ H Hc Hi. apply Hstep; assumption.
    Qed.
  End RunMethod.

  (** ** Part 4. The age order of the ghost ([GAge]) *)

  Section Lists.
    Context {A : Type}.

    Lemma subseq_nil_l (l : list A) : subseq [] l.
    Proof. induction l; constructor; assumption. Qed.

    Lemma subseq_single (x : A) l : In x l -> subseq [x] l.
    Proof.
      induction l as [| y l IH]; intros Hx; [destruct Hx |].
      destruct Hx as [-> | Hx]; [apply subseq_keep, subseq_nil_l | apply subseq_skip, IH, Hx].
    Qed.

    Lemma subseq_pair_split (l1 l2 : list A) a b : In b l2 -> subseq [a; b] (l1 ++ a :: l2).
    Proof.
      intros Hb. induction l1 as [| y l1 IH]; cbn.
      - apply subseq_keep. apply subseq_single. exact Hb.
      - apply subseq_skip. exact IH.
    Qed.

    Lemma subseq_cons_l (x : A) l ks :
      subseq (x :: l) ks -> exists ks1 ks2, ks = ks1 ++ x :: ks2 /\ subseq l ks2.
    Proof.
      induction ks as [| y ks IH]; intros Hs; [inversion Hs |].
      inversion Hs as [| x0 l0 l0' Hs' E1 E2 | x0 l0 l0' Hs' E1 E2]; subst.
      - exists [], ks. auto.
      - destruct (IH Hs') as (ks1 & ks2 & -> & Hs2). exists (y :: ks1), ks2. auto.
    Qed.
  End Lists.

  Section Age.
    Context {E F : RelaxedSig.t}.

    (** [key_older ks k1 k2]: in the newest-first key list [ks] (the
        domain of a pool, [lin_insert] adds at the head), [k1] is older
        than [k2]. *)
    Definition key_older (ks : list (CallKey F)) (k1 k2 : CallKey F) : Prop := subseq [k2; k1] ks.

    (** [GAge P γ]: every ghost entry is owned by a call of the pool, and
        the entries of an older call come before the entries of a younger
        call ("grouped by owner, owners in pool age order", design B,
        I8).  Entries of one owner may be interleaved with nothing else
        of a different-age owner; their own order is unconstrained. *)
    Definition GAge (P : LinPool F) (γ : Ghost E F) : Prop :=
      (forall e, In e γ -> In (se_owner e) (lin_domain P)) /\
      (forall i j e1 e2, nth_error γ i = Some e1 -> nth_error γ j = Some e2 ->
         key_older (lin_domain P) (se_owner e1) (se_owner e2) -> i < j).

    Lemma key_older_mono ks ks' k1 k2 : subseq ks ks' -> key_older ks k1 k2 -> key_older ks' k1 k2.
    Proof. intros Hs Ho. exact (subseq_trans _ _ _ Ho Hs). Qed.

    Lemma key_older_in ks k1 k2 : key_older ks k1 k2 -> In k1 ks /\ In k2 ks.
    Proof.
      intros Ho. split; apply (subseq_in _ _ _ Ho); [right; left | left]; reflexivity.
    Qed.

    Lemma key_older_irrefl ks k : NoDup ks -> ~ key_older ks k k.
    Proof.
      intros Hnd Ho. destruct (subseq_cons_l _ _ _ Ho) as (ks1 & ks2 & -> & Hs).
      apply (NoDup_remove_2 _ _ _ Hnd). apply in_or_app. right. exact (subseq_in _ _ _ Hs (or_introl eq_refl)).
    Qed.

    Lemma key_older_cons k ks k1 k2 : key_older (k :: ks) k1 k2 -> (k2 = k /\ In k1 ks) \/ key_older ks k1 k2.
    Proof.
      intros Ho. inversion Ho as [| x0 l0 l0' Hs E1 E2 | x0 l0 l0' Hs E1 E2]; subst.
      - left. split; [reflexivity |]. exact (subseq_in _ _ _ Hs (or_introl eq_refl)).
      - right. exact Hs.
    Qed.

    Lemma gage_nil (P : LinPool F) : GAge P [].
    Proof. split; [intros e [] | intros i j e1 e2 H1; destruct i; discriminate]. Qed.

    Lemma gage_domain (P P' : LinPool F) (γ : Ghost E F) :
      lin_domain P' = lin_domain P -> GAge P γ -> GAge P' γ.
    Proof. intros Hd. unfold GAge. rewrite Hd. exact (fun H => H). Qed.

    Lemma gage_lin_update key b a (P P' : LinPool F) (γ : Ghost E F) :
      lin_update key b a P P' -> GAge P γ -> GAge P' γ.
    Proof. intros Hu. apply gage_domain. symmetry. exact (lin_update_keys _ _ _ _ _ Hu). Qed.

    Lemma gage_lin_invoke_update t h o (P P' : LinPool F) (γ : Ghost E F) :
      lin_invoke_update t h o P P' -> GAge P γ -> GAge P' γ.
    Proof. intros Hu. apply gage_domain. symmetry. exact (lin_invoke_update_keys _ _ _ _ _ Hu). Qed.

    Lemma gage_poss_steps {VF : LTS F} v (P : LinPool F) v' P' (γ : Ghost E F) :
      poss_steps VF (PossOk v P) (PossOk v' P') -> GAge P γ -> GAge P' γ.
    Proof. intros Hs. apply gage_domain. symmetry. exact (poss_steps_ok_domain VF _ _ _ _ Hs). Qed.

    (** Invocation: the new call is the youngest, its entries are
        appended. *)
    Lemma gage_invoke key st (P : LinPool F) (γ γn : Ghost E F) :
      lin_fresh key P -> (forall e, In e γn -> se_owner e = key) -> GAge P γ ->
      GAge (make_lin_entry key st :: P) (γ ++ γn).
    Proof.
      intros Hfr Hown [Hdom Hord]. unfold lin_fresh in Hfr. split.
      - intros e He. cbn. rewrite lin_key_make_lin_entry. apply in_app_or in He as [He | He].
        + right. exact (Hdom e He).
        + left. symmetry. exact (Hown e He).
      - intros i j e1 e2 H1 H2 Ho. cbn [lin_domain map] in Ho. rewrite lin_key_make_lin_entry in Ho.
        destruct (Nat.lt_ge_cases i (length γ)) as [Hi | Hi].
        + rewrite nth_error_app1 in H1 by exact Hi.
          destruct (Nat.lt_ge_cases j (length γ)) as [Hj | Hj]; [| lia].
          rewrite nth_error_app1 in H2 by exact Hj.
          destruct (key_older_cons _ _ _ _ Ho) as [(Hk & _) | Ho'].
          * exfalso. apply Hfr. rewrite <- Hk. exact (Hdom e2 (nth_error_In _ _ H2)).
          * exact (Hord i j e1 e2 H1 H2 Ho').
        + exfalso. rewrite nth_error_app2 in H1 by exact Hi.
          pose proof (Hown e1 (nth_error_In _ _ H1)) as Hk1. rewrite Hk1 in Ho.
          destruct (key_older_cons _ _ _ _ Ho) as [(_ & Hin) | Ho']; apply Hfr;
            [exact Hin | exact (proj1 (key_older_in _ _ _ Ho'))].
    Qed.

    Lemma gage_poss_invoke {VF : LTS F} t h op v (P : LinPool F) p' (γ γn : Ghost E F) :
      poss_invoke VF t h op (PossOk v P) p' -> (forall e, In e γn -> se_owner e = (t, h)) -> GAge P γ ->
      p' = PossOk v (make_lin_entry (t, h) (ls_inv op) :: P) /\
      GAge (make_lin_entry (t, h) (ls_inv op) :: P) (γ ++ γn).
    Proof.
      intros Hi Hown Hage. destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hi) as [-> Hfr].
      split; [reflexivity | exact (gage_invoke _ _ _ _ _ Hfr Hown Hage)].
    Qed.

    (** Emission: removing an entry keeps the order of the others. *)
    Lemma gage_remove (P : LinPool F) (g1 g2 : Ghost E F) x :
      GAge P (g1 ++ x :: g2) -> GAge P (g1 ++ g2).
    Proof.
      intros [Hdom Hord]. split.
      - intros e He. apply Hdom. apply in_app_or in He as [He | He]; apply in_or_app; [left | right; right]; exact He.
      - set (f := fun i => if i <? length g1 then i else S i).
        assert (Hf : forall i, nth_error (g1 ++ x :: g2) (f i) = nth_error (g1 ++ g2) i).
        { intros i. unfold f. destruct (Nat.ltb_spec i (length g1)) as [Hi | Hi].
          - rewrite !nth_error_app1 by exact Hi. reflexivity.
          - rewrite !nth_error_app2 by lia. replace (S i - length g1) with (S (i - length g1)) by lia. reflexivity. }
        intros i j e1 e2 H1 H2 Ho. rewrite <- Hf in H1, H2. pose proof (Hord _ _ _ _ H1 H2 Ho) as Hlt.
        unfold f in Hlt. destruct (Nat.ltb_spec i (length g1)), (Nat.ltb_spec j (length g1)); lia.
    Qed.

    Lemma gage_ghost_emit (P : LinPool F) key (ev : ThreadEvent E) (γ γ' : Ghost E F) :
      ghost_emit key ev γ γ' -> GAge P γ -> GAge P γ'.
    Proof.
      unfold ghost_emit. destruct (te_ev E ev).
      - intros (g1 & g2 & -> & -> & _). apply gage_remove.
      - intros ->. exact (fun H => H).
    Qed.

    Lemma lin_remove_domain_subseq key st (P P' : LinPool F) :
      lin_remove key st P P' -> subseq (lin_domain P') (lin_domain P).
    Proof.
      induction 1 as [tail | e pool pool' Hne Hr IH]; cbn.
      - apply subseq_skip. apply subseq_refl.
      - apply subseq_keep. exact IH.
    Qed.

    Lemma lin_remove_domain_in key st (P P' : LinPool F) k' :
      lin_remove key st P P' -> In k' (lin_domain P) -> k' <> key -> In k' (lin_domain P').
    Proof.
      induction 1 as [tail | e pool pool' Hne Hr IH]; cbn; intros Hin Hk.
      - rewrite lin_key_make_lin_entry in Hin. destruct Hin as [Heq | Hin]; [contradiction (Hk (eq_sym Heq)) | exact Hin].
      - destruct Hin as [Heq | Hin]; [left; exact Heq | right; exact (IH Hin Hk)].
    Qed.

    (** Return: the returning call has no ghost entry left. *)
    Lemma gage_lin_remove key st (P P' : LinPool F) (γ : Ghost E F) :
      lin_remove key st P P' -> NoOwn key γ -> GAge P γ -> GAge P' γ.
    Proof.
      intros Hr Hno [Hdom Hord]. split.
      - intros e He. exact (lin_remove_domain_in _ _ _ _ _ Hr (Hdom e He) (Hno e He)).
      - intros i j e1 e2 H1 H2 Ho. apply (Hord i j e1 e2 H1 H2).
        exact (key_older_mono _ _ _ _ (lin_remove_domain_subseq _ _ _ _ Hr) Ho).
    Qed.

    Lemma gage_poss_return {VF : LTS F} t h op r v (P : LinPool F) p2 (γ : Ghost E F) :
      poss_return VF t h op r (PossOk v P) p2 -> NoOwn (t, h) γ -> GAge P γ ->
      exists P2, p2 = PossOk v P2 /\ GAge P2 γ.
    Proof.
      intros Hr Hno Hage. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hr) as (P2 & -> & Hrem).
      exists P2. split; [reflexivity | exact (gage_lin_remove _ _ _ _ _ Hrem Hno Hage)].
    Qed.

    (** An entry of an older owner lies before every entry of a younger
        owner. *)
    Lemma gage_before (P : LinPool F) (γ g1 g2 : Ghost E F) x e :
      GAge P γ -> γ = g1 ++ x :: g2 -> In e γ ->
      key_older (lin_domain P) (se_owner e) (se_owner x) -> In e g1.
    Proof.
      intros [_ Hord] -> He Ho. apply In_nth_error in He as (i & Hi).
      assert (Hx : nth_error (g1 ++ x :: g2) (length g1) = Some x)
        by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
      pose proof (Hord i (length g1) e x Hi Hx Ho) as Hlt.
      rewrite nth_error_app1 in Hi by exact Hlt. exact (nth_error_In _ _ Hi).
    Qed.
  End Age.

  (** ** Part 5. Readiness by blocking ([emit_ready_block])

      When the linearizing invocation [ev] of the call [(t, h)] is emitted
      ([ghost_emit]: no older ghost entry [inv_blocks] it), the abstract
      invocation of [(t, h)] is enabled, provided every older [ls_inv]
      call of the same thread owns a ghost entry that blocks [ev].  By
      [GAge] that entry lies before [ev]'s entry, which [ghost_emit]
      excludes; so no older same-thread call is at [ls_inv], and
      [invocation_ready] holds without consulting the overlay relation
      [semi_independent F]. *)

  Section Ready.
    Context {E F : RelaxedSig.t}.

    Theorem emit_ready_block_older (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
      lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
      (forall k1 o1, fst k1 = t -> key_older (lin_domain P) k1 (t, h) -> lin_lookup k1 (ls_inv o1) P ->
         exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) ->
      γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 ->
      Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
      exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
    Proof.
      intros Hwf Hl Hage Hblk Hγ Hnb.
      destruct (in_split _ _ Hl) as (pre & older & HP).
      assert (Hwf0 := Hwf). unfold lin_pool_well_formed, lin_domain in Hwf0.
      rewrite HP, map_app in Hwf0. cbn in Hwf0.
      pose proof (NoDup_remove_2 _ _ _ Hwf0) as Hnin. rewrite lin_key_make_lin_entry in Hnin.
      assert (Hpre : forall y, In y pre -> lin_key y <> (t, h)).
      { intros y Hy Hk. apply Hnin. apply in_or_app. left. rewrite <- Hk. apply in_map. exact Hy. }
      assert (Hready : invocation_ready t o older).
      { unfold invocation_ready. apply Forall_forall. intros e He.
        unfold older_entry_allows_invocation.
        destruct (Pos.eqb_spec (lin_tid F e) t) as [Ht | Ht]; [right | left; exact Ht].
        destruct (lin_state F e) as [o1 | o1 | o1 r1] eqn:Hs; [exfalso | exact Logic.I | exact Logic.I].
        assert (He' : e = make_lin_entry (lin_key e) (ls_inv o1)) by (destruct e; cbn in *; subst; reflexivity).
        assert (Hold : key_older (lin_domain P) (lin_key e) (t, h)).
        { unfold key_older, lin_domain. rewrite HP, map_app. cbn [map]. rewrite lin_key_make_lin_entry.
          apply subseq_pair_split. apply in_map. exact He. }
        assert (Hle : lin_lookup (lin_key e) (ls_inv o1) P).
        { unfold lin_lookup. rewrite <- He', HP. apply in_or_app. right. right. exact He. }
        destruct (Hblk (lin_key e) o1 Ht Hold Hle) as (e' & He'γ & Hown & Hb).
        assert (Hin1 : In e' g1).
        { apply (gage_before P γ g1 g2 (Build_ScheduledEvent (t, h) ev) e' Hage Hγ He'γ). rewrite Hown. exact Hold. }
        rewrite Forall_forall in Hnb. exact (Hnb e' Hin1 Hb). }
      assert (Hu : lin_invoke_update t h o P (pre ++ make_lin_entry (t, h) (ls_lini o) :: older)).
      { rewrite HP. apply RelaxedHoareCompLinSpec.liu_app; [exact Hpre |]. apply lin_invoke_update_here. exact Hready. }
      exists (pre ++ make_lin_entry (t, h) (ls_lini o) :: older). split; [exact Hu |].
      eapply lin_invoke_update_well_formed; [exact Hu | exact Hwf].
    Qed.

    (** The plan's form: the blocking premise for every other [ls_inv]
        call of the thread (the readiness coupling of an invariant usually
        gives it for all of them). *)
    Corollary emit_ready_block (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
      lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
      (forall k1 o1, fst k1 = t -> k1 <> (t, h) -> lin_lookup k1 (ls_inv o1) P ->
         exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) ->
      γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 ->
      Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
      exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
    Proof.
      intros Hwf Hl Hage Hblk. apply (emit_ready_block_older P γ g1 g2 t h o ev Hwf Hl Hage).
      intros k1 o1 Ht Ho Hl1. apply (Hblk k1 o1); [exact Ht | | exact Hl1].
      intros ->. exact (key_older_irrefl _ _ Hwf Ho).
    Qed.

    (** [GAge] after the emission of the linearization point. *)
    Corollary gage_after_lp (P P' : LinPool F) (g1 g2 : Ghost E F) x t h o :
      GAge P (g1 ++ x :: g2) -> lin_invoke_update t h o P P' -> GAge P' (g1 ++ g2).
    Proof. intros Hage Hu. exact (gage_lin_invoke_update _ _ _ _ _ _ Hu (gage_remove _ _ _ _ Hage)). Qed.
  End Ready.

  (** ** Part 6. [Done] facts over [EIhl], and their monotonicity

      [eihl_done_inv key]: the underlay key [key] has been invoked (it is
      in the used list).  [eihl_done_res key]: it has been invoked and its
      record has been consumed (its response emitted).  Both are kept by
      every [EIhl] step, of any thread and operation ([eihl_done_inv_steps],
      [eihl_done_res_steps]), by handle-linearity: a used key is never
      re-invoked.  So an edge assertion "the event [κ] is done" is stable
      under every rely and every guarantee whose memory part is
      [eihl_steps]. *)

  Section Done.
    Import RelaxedHoareCompLinSpec.
    Context {E : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (effect E), Sig.ar o -> St -> Prop).
    Local Abbreviation V := (EIhl δ).

    Definition eihl_done_inv (key : CallKey E) (σ : State V) : Prop := In key (snd σ).

    Definition eihl_done_res (key : CallKey E) (σ : State V) : Prop :=
      In key (snd σ) /\ forall x, In x (snd (fst σ)) -> RelaxedTraceLin.op_key x <> key.

    (** Pending records have distinct keys. *)
    Definition eihl_rec_nodup (σ : State V) : Prop := NoDup (map (@RelaxedTraceLin.op_key E) (snd (fst σ))).

    Lemma eihl_done_inv_step key ev (σ σ' : State V) :
      Step V ev σ σ' -> eihl_done_inv key σ -> eihl_done_inv key σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. unfold eihl_done_inv. cbn.
      destruct ev as [t [h o | h o r]]; cbn.
      - intros (_ & _ & ->) Hk. right. exact Hk.
      - intros (_ & ->) Hk. exact Hk.
    Qed.

    Lemma eihl_done_inv_steps key (σ σ' : State V) :
      eihl_steps δ σ σ' -> eihl_done_inv key σ -> eihl_done_inv key σ'.
    Proof.
      induction 1 as [σ σ' (ev & Hs) | σ | σ σ1 σ' _ IH1 _ IH2]; intros H; auto.
      exact (eihl_done_inv_step key ev σ σ' Hs H).
    Qed.

    Lemma eihl_done_res_step key ev (σ σ' : State V) :
      Step V ev σ σ' -> eihl_done_res key σ -> eihl_done_res key σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. unfold eihl_done_res. cbn.
      destruct ev as [t [h o | h o r]]; cbn.
      - intros (Hnu & (r & st' & _ & Heq) & ->) (Hk & Hx). injection Heq as -> ->.
        split; [right; exact Hk |]. intros x [<- | Hin]; [| exact (Hx x Hin)].
        cbn. intros Heq. apply Hnu. rewrite Heq. exact Hk.
      - intros ((P1 & P2 & HP & Heq) & ->) (Hk & Hx). injection Heq as -> ->.
        split; [exact Hk |]. intros x Hin. apply Hx. rewrite HP.
        apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left | right; right]; exact Hin.
    Qed.

    Lemma eihl_done_res_steps key (σ σ' : State V) :
      eihl_steps δ σ σ' -> eihl_done_res key σ -> eihl_done_res key σ'.
    Proof.
      induction 1 as [σ σ' (ev & Hs) | σ | σ σ1 σ' _ IH1 _ IH2]; intros H; auto.
      exact (eihl_done_res_step key ev σ σ' Hs H).
    Qed.

    Lemma eihl_done_res_inv key (σ : State V) : eihl_done_res key σ -> eihl_done_inv key σ.
    Proof. intros [Hk _]. exact Hk. Qed.

    Lemma eihl_rec_nodup_init (s : St) : eihl_rec_nodup ((s, []), []).
    Proof. constructor. Qed.

    Lemma eihl_rec_nodup_step ev (σ σ' : State V) :
      Step V ev σ σ' -> eihl_rec_used δ σ -> eihl_rec_nodup σ -> eihl_rec_nodup σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. unfold eihl_rec_nodup, eihl_rec_used. cbn.
      destruct ev as [t [h o | h o r]]; cbn.
      - intros (Hnu & (r & st' & _ & Heq) & ->) Hru Hnd. injection Heq as -> ->. cbn.
        constructor; [| exact Hnd]. intros Hin. apply in_map_iff in Hin as (x & Hk & Hx).
        apply Hnu. rewrite <- Hk. exact (Hru x Hx).
      - intros ((P1 & P2 & HP & Heq) & ->) _ Hnd. injection Heq as -> ->.
        rewrite HP, map_app in Hnd. cbn in Hnd. rewrite map_app. exact (NoDup_remove_1 _ _ _ Hnd).
    Qed.

    Lemma eihl_rec_nodup_steps (σ σ' : State V) :
      eihl_steps δ σ σ' -> eihl_rec_used δ σ -> eihl_rec_nodup σ -> eihl_rec_nodup σ'.
    Proof.
      induction 1 as [σ σ' (ev & Hs) | σ | σ σ1 σ' H1 IH1 H2 IH2]; intros Hru Hnd; auto.
      - exact (eihl_rec_nodup_step ev σ σ' Hs Hru Hnd).
      - apply IH2; [exact (eihl_rec_used_steps δ _ _ H1 Hru) |]. apply IH1; assumption.
    Qed.

    (** The invocation of [key] makes it done. *)
    Lemma eihl_done_inv_of_inv t h o (σ σ' : State V) :
      Step V (Build_ThreadEvent t (@InvEv E h o)) σ σ' -> eihl_done_inv (t, h) σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. unfold eihl_done_inv. cbn.
      intros (_ & _ & ->). left. reflexivity.
    Qed.

    (** The response of [key] consumes its (unique) record. *)
    Lemma eihl_done_res_of_res t h o (r : Sig.ar o) (σ σ' : State V) :
      Step V (Build_ThreadEvent t (@ResEv E h o r)) σ σ' -> eihl_rec_used δ σ -> eihl_rec_nodup σ ->
      eihl_done_res (t, h) σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. unfold eihl_done_res, eihl_rec_nodup, eihl_rec_used. cbn.
      intros ((P1 & P2 & HP & Heq) & ->) Hru Hnd. injection Heq as -> ->.
      split.
      - apply (Hru (RelaxedTraceLin.Build_Op (t, h) o r)). rewrite HP. apply in_or_app. right. left. reflexivity.
      - intros x Hx Hk. rewrite HP, map_app in Hnd. cbn in Hnd. apply (NoDup_remove_2 _ _ _ Hnd).
        rewrite <- map_app. apply in_map_iff. exists x. split; [exact Hk | exact Hx].
    Qed.

    (** A done invocation cannot be emitted again, a done response
        neither. *)
    Lemma eihl_done_inv_disabled t h o (σ σ' : State V) :
      eihl_done_inv (t, h) σ -> ~ Step V (Build_ThreadEvent t (@InvEv E h o)) σ σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. unfold eihl_done_inv. cbn.
      intros Hk (Hnu & _). exact (Hnu Hk).
    Qed.

    Lemma eihl_done_res_disabled t h o (r : Sig.ar o) (σ σ' : State V) :
      eihl_done_res (t, h) σ -> ~ Step V (Build_ThreadEvent t (@ResEv E h o r)) σ σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. unfold eihl_done_res. cbn.
      intros (_ & Hx) ((P1 & P2 & HP & _) & _). apply (Hx (RelaxedTraceLin.Build_Op (t, h) o r)); [| reflexivity].
      rewrite HP. apply in_or_app. right. left. reflexivity.
    Qed.

    (** A done response is owned vacuously: no record with its key is left. *)
    Lemma eihl_done_res_mine key x0 (σ : State V) :
      eihl_rec_used δ σ -> eihl_done_res key σ -> eihl_mine δ key x0 σ.
    Proof.
      intros Hru (Hk & Hx). split; [exact Hru |]. split; [exact Hk |].
      intros x Hin Hkx. exfalso. exact (Hx x Hin Hkx).
    Qed.
  End Done.

  (** ** Part 7. Smoke test: [rp_run] re-derives the renaming body

      The one-call machine [one_next op back1]: call [op] (empty tag),
      then return [back1] of its response.  [Mrun] is the renaming
      copy-cat of [RelaxedHoareInherit] with every body written as this
      machine under [run] (a [FutureD] with the empty tag, instead of the
      untagged [Future] of [RelaxedHoareInherit.ren_provable]).  Its
      derivation [ren_run_provable] goes through [run_method_provable],
      i.e. [rp_run], and reuses the per-event updates and stability
      lemmas of [RelaxedHoareInherit]; the dag facts come from
      [dprec_run_res].  [RunCounter] instantiates it with the SI = ∅
      FAA→Inc counter. *)

  Definition one_next {S : Sig.t} {B : Type} (op : Sig.op S) (back1 : Sig.ar op -> B) (st : option B) :
      SStep S (option B) B :=
    match st with
    | None => SCall op [] (fun r => Some (back1 r))
    | Some b => SDone b
    end.

  Section RunRename.
    Import RelaxedHoareCompLinSpec RelaxedHoareInherit.
    Context {E F : RelaxedSig.t} {StE StF : Type}.
    Context (δE : StE -> forall o : Sig.op (effect E), Sig.ar o -> StE -> Prop).
    Context (δF : StF -> forall o : Sig.op (effect F), Sig.ar o -> StF -> Prop).
    Context (π : StE -> StF) (ρ : Sig.op (effect F) -> Sig.op (effect E)) (lz : Sig.op (effect E) -> bool).
    Context (back : forall o : Sig.op (effect F), Sig.ar (ρ o) -> Sig.ar o).
    Context (Hδ : forall s o r s', δE s (ρ o) r s' -> δF (π s) o (back o r) (π s')).
    Context (Hsi : forall o1 o2, ~ ~ semi_independent E (ρ o1) (ρ o2) -> semi_independent F o1 o2).
    Context (Hlz : forall o, lz (ρ o) = true).
    Context (Hinj : forall u o (r1 r2 : Sig.ar (ρ o)),
                @RelaxedTraceLin.Build_Op E u (ρ o) r1 = @RelaxedTraceLin.Build_Op E u (ρ o) r2 ->
                back o r1 = back o r2).

    Local Abbreviation VE := (EIhl δE).
    Local Abbreviation VF := (RelaxedHoareSpec.EI δF).
    Local Abbreviation Ir := (Iren δE δF π ρ lz).
    Local Abbreviation Rr := (Rren δE δF).
    Local Abbreviation Gr := (Gren δE δF).

    Definition Mrun : RelaxedModuleImpl E F := fun o _ => run (one_next (ρ o) (back o)) [] None.

    Section Call.
      Context (t : tid) (h : handle F) (o : Sig.op (effect F)).
      Local Abbreviation k := (@pair tid (handle F) t h).

      (** The invocation slot: [RelaxedHoareInherit.sl_inv] with the tag of
          [FutureD]. *)
      Definition sl_invD (hu : handle E) : Slot VE VF :=
        mkSlot (invD_tev (F := F) k empty_store (dep_of (map (@rc_h E) []) []) hu (ρ o)) (KInv δE δF k o)
          (fun _ _ => True) (KLini δE δF ρ back k o hu) (Gr k).

      (** The machine invariant: before the call, nothing; after it, the
          two slots, and the result is [back] of the response. *)
      Definition ren_run_inv (st : option (Sig.ar o)) (cs : list (RCall E)) (Γ : list (Slot VE VF))
          (H : FutureStore E) : Prop :=
        match st with
        | None => cs = [] /\ Γ = [] /\ H = empty_store
        | Some b => exists hu (r : Sig.ar (ρ o)), b = back o r /\ Γ = [sl_invD hu; sl_res δE δF ρ back t h o hu r]
        end.

      Lemma ren_run_dprec hu (r : Sig.ar (ρ o)) d :
        dprec (evs [sl_invD hu; sl_res δE δF ρ back t h o hu r]) d 1 <-> d = 0.
      Proof.
        pose proof (dprec_run_res k [] empty_store [] (sl_invD hu) (sl_res δE δF ρ back t h o hu r) hu (ρ o) [] r d
                      (runctx_nil k) (fun Hin => Hin) eq_refl eq_refl) as Hd.
        exact Hd.
      Qed.

      Lemma ren_run_newinv hu :
        NewSlotOK Ir Rr Gr k (PostInvoke Ir k o (Ωren ρ t o)) [] (sl_invD hu).
      Proof.
        constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_invD].
        - auto.
        - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_invD].
          intros σ p γ γ' [HK _]. exact (inv_update δE δF π ρ lz back Hδ Hsi Hlz t h o hu σ p γ γ' HK).
        - exact (pinit_KInv δE δF π ρ lz t h o).
        - intros d sd _ Hd. destruct d; discriminate.
        - apply KInv_stable.
        - intros d _. apply Stable_true.
        - intros g sg Hg. destruct g; discriminate.
        - intros d g sg _ Hg. destruct g; discriminate.
        - intros y sy Hy. destruct y; discriminate.
        - intros y sy d Hy. destruct y; discriminate.
      Qed.

      Lemma ren_run_newres hu (r : Sig.ar (ρ o)) :
        NewSlotOK Ir Rr Gr k (PostInvoke Ir k o (Ωren ρ t o)) [sl_invD hu] (sl_res δE δF ρ back t h o hu r).
      Proof.
        pose proof (ren_run_dprec hu r) as Hdp.
        constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar sl_res sl_invD length app].
        - auto.
        - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar sl_res length app].
          intros σ p γ γ' [_ Hin]. apply (res_update δE δF π ρ lz back Hinj t h o hu r σ p γ γ').
          apply (Hin 0). apply Hdp. reflexivity.
        - intros s _ _. exact Logic.I.
        - intros d sd Hd Hsd. apply Hdp in Hd. subst d. cbn in Hsd. injection Hsd as <-.
          cbn. intros s _ Hs. exact Hs.
        - apply Stable_true.
        - intros d _. apply KLini_stable.
        - intros g sg _. apply Stable_true.
        - intros d g sg Hd Hg Hnb. exfalso. apply Hdp in Hd. subst d.
          destruct g as [| g]; [apply Hnb, before_refl | destruct g; discriminate].
        - intros y sy Hy Hnb. exfalso. destruct y as [| y]; [| destruct y; discriminate].
          apply Hnb. apply before_dprec. apply Hdp. reflexivity.
        - intros y sy d Hy _ Hd. exfalso. apply dprec_lt in Hd. destruct y as [| y]; [lia | destruct y; discriminate].
      Qed.

      Lemma ren_run_close hu (r : Sig.ar (ρ o)) H :
        all_resolved H ->
        Close Ir Rr Gr k (PostInvoke Ir k o (Ωren ρ t o)) (KLinr δE δF k o) (back o r)
          [sl_invD hu; sl_res δE δF ρ back t h o hu r] H.
      Proof.
        intros Hall. pose proof (ren_run_dprec hu r 0) as Hd01.
        apply close_done with
          (fin := fun d => match d with 1 => KLinr δE δF k o (back o r) | _ => fun _ => True end)
          (fin0 := fun _ => True); [exact Hall |].
        constructor.
        - intros d sd Hd. destruct d as [| [| d]]; cbn in Hd; try (destruct d; discriminate).
          + intros s _ _. exact Logic.I.
          + injection Hd as <-. intros s _ Hs. exact Hs.
        - intros s _ _. exact Logic.I.
        - intros d g sg Hd Hg Hnb. destruct d as [| [| d]]; [apply Stable_true | | cbn in Hd; lia].
          exfalso. apply Hnb. destruct g as [| [| g]]; [| apply before_refl | destruct g; discriminate].
          apply before_dprec. apply Hd01. reflexivity.
        - intros g sg _. apply Stable_true.
        - intros [| [| d]]; [apply Stable_true | apply KLinr_stable | apply Stable_true].
        - apply Stable_true.
        - intros s _ _ Hfin. exact (Hfin 1 _ eq_refl Logic.I).
      Qed.
    End Call.

    (** The derivation, through [run_method_provable] (hence [rp_run]). *)
    Theorem ren_run_provable t o :
      MethodProvable Ir Rr Gr Mrun t o (fun _ => Ωren ρ t o) (fun h => KLinr δE δF (t, h) o).
    Proof.
      apply (run_method_provable Ir Rr Gr Mrun t o _ _ (one_next (ρ o) (back o)) None (fun h => ren_run_inv t h o)).
      - reflexivity.
      - intros h s Hs. exact (ren_PI δE δF π ρ lz Hlz t h o s Hs).
      - intros h r s HQ HI Hno. exact (ren_ret δE δF π ρ lz t h o r s HQ HI Hno).
      - intros h. cbn. auto.
      - intros h st cs Γ H Hc Hi. destruct st as [b |]; cbn in Hi |- *.
        + destruct Hi as (hu & r & -> & ->). split.
          * apply ren_run_close. exact (proj1 (proj2 (runctx_store _ _ _ _ Hc))).
          * exists hu. reflexivity.
        + destruct Hi as (-> & -> & ->).
          exists (sl_invD t h o), (sl_res δE δF ρ back t h o).
          split; [intros hu; reflexivity |]. split; [intros hu _; apply ren_run_newinv |].
          split; [intros hu v; reflexivity |]. split; [intros hu v _; apply ren_run_newres |].
          intros hu v H' _ _ _. exists hu, v. split; reflexivity.
    Qed.

    Theorem ren_run_methodsem t o : MethodSem Ir Rr Gr Mrun t o.
    Proof. exact (method_sound Ir Rr Gr Mrun t o _ _ (ren_run_provable t o)). Qed.

    Theorem ren_run_rlhl2 (s0 : StE) : RLHL2Hyps Ir Rr Gr Mrun ((s0, []), []) (π s0, []).
    Proof. exact (ren_rlhl2_of_sem δE δF π ρ lz Mrun s0 ren_run_methodsem). Qed.
  End RunRename.

  (** The SI = ∅ FAA→Inc counter (as [RelaxedHoareChecks.Counter]), with
      its body run by the one-call machine. *)
  Module RunCounter.
    Inductive UOp := FAA.
    Definition u_ar (o : UOp) : Type := match o with FAA => nat end.
    Definition UEff : Sig.t := {| Sig.op := UOp; Sig.ar := u_ar |}.
    Definition USig : RelaxedSig.t :=
      {| effect := UEff; handle := nat; semi_independent := fun _ _ => False; mode := fun _ => Local |}.
    Inductive OOp := Inc.
    Definition o_ar (o : OOp) : Type := match o with Inc => nat end.
    Definition OEff : Sig.t := {| Sig.op := OOp; Sig.ar := o_ar |}.
    Definition OSig : RelaxedSig.t :=
      {| effect := OEff; handle := nat; semi_independent := fun _ _ => False; mode := fun _ => Local |}.

    Definition uδ (n : nat) (o : Sig.op (effect USig)) : Sig.ar o -> nat -> Prop :=
      match o as o0 return @Sig.ar UEff o0 -> nat -> Prop with FAA => fun r n' => r = n /\ n' = S n end.
    Definition cδ (n : nat) (o : Sig.op (effect OSig)) : Sig.ar o -> nat -> Prop :=
      match o as o0 return @Sig.ar OEff o0 -> nat -> Prop with Inc => fun r n' => r = n /\ n' = S n end.

    Definition ρc (o : Sig.op (effect OSig)) : Sig.op (effect USig) := FAA.
    Definition backc (o : Sig.op (effect OSig)) : Sig.ar (ρc o) -> Sig.ar o :=
      match o as o0 return @Sig.ar UEff (ρc o0) -> @Sig.ar OEff o0 with Inc => fun r => r end.

    Definition uval (x : RelaxedTraceLin.Op USig) : nat :=
      match RelaxedTraceLin.op_op x as o return u_ar o -> nat with FAA => fun r => r end (RelaxedTraceLin.op_ret x).

    Lemma c_δ : forall s o r s', uδ s (ρc o) r s' -> cδ s o (backc o r) s'.
    Proof. intros s [] r s' H. exact H. Qed.

    Lemma c_si : forall o1 o2, ~ ~ semi_independent USig (ρc o1) (ρc o2) -> semi_independent OSig o1 o2.
    Proof. intros o1 o2 H. apply H. intros []. Qed.

    Lemma c_inj : forall u o (r1 r2 : Sig.ar (ρc o)),
        @RelaxedTraceLin.Build_Op USig u (ρc o) r1 = @RelaxedTraceLin.Build_Op USig u (ρc o) r2 ->
        backc o r1 = backc o r2.
    Proof. intros u [] r1 r2 H. exact (f_equal uval H). Qed.

    Definition Mc : RelaxedModuleImpl USig OSig := Mrun ρc backc.

    (** The body of [Mc] is a [run] (not the untagged [Future] body of
        [RelaxedHoareChecks.Counter.Mc]). *)
    Lemma Mc_body t : Mc Inc t = run (G := USig) (one_next (S := UEff) FAA (fun r : nat => r)) [] None.
    Proof. reflexivity. Qed.

    Theorem counter_run_rlhl2 :
      RLHL2Hyps (RelaxedHoareInherit.Iren uδ cδ (fun n => n) ρc (fun _ => true))
        (RelaxedHoareInherit.Rren uδ cδ) (RelaxedHoareInherit.Gren uδ cδ) Mc ((0, []), []) (0, []).
    Proof.
      exact (ren_run_rlhl2 uδ cδ (fun n => n) ρc (fun _ => true) backc c_δ c_si (fun _ => eq_refl) c_inj 0).
    Qed.

    (** Copy-cat inclusion over the plain [EI uδ] ([classic], through
        [RelaxedHoareCompLinSpec.rlhl_complin_eihl]). *)
    Corollary counter_run_complin :
      RelaxedHoareCompLin.RCompLin Mc (RelaxedHoareSpec.EI uδ) (0, []) (RelaxedHoareSpec.EI cδ) (0, []).
    Proof. exact (RelaxedHoareCompLinSpec.rlhl_complin_eihl uδ cδ 0 _ _ _ Mc (0, []) counter_run_rlhl2). Qed.
  End RunCounter.

End RelaxedHoareRun.
