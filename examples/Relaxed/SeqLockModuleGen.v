(** * SeqLock ⊎ COH[z]: the module bridge over an arbitrary underlay specification

    [SeqLockModule] builds, from a complete instrumented execution of
    [SeqLockProg.M rc K] and an underlay witness [Wu], an execution
    [SeqLockModule.SX] of [SeqLockCOH].  It proves [SeqLockCOH.WF] for it
    ([SeqLockModule.SX_wf]) and transports [seqlock_S1], [z_S1], their
    order lemmas and [lp_inj] to the overlay ([SeqLockModule.positional]).
    There [Wu] is a witness for the register specification
    [BL.nuE_all SL.comp_dec compE (nuEc rc K)] (TicketLock with version
    counter ⊗ x ⊗ y ⊗ barriers, and COH[z]).  This file states the same
    bridge for a witness [HWu] of an arbitrary underlay specification
    [P : list (Op (E rc K)) -> Prop].  The one place where the register
    specification was used is isolated: the field [wf_valid] of
    [SeqLockCOH.WF] for [SX] ([Valid SX]).  Validity is needed only for
    the overlay specifications themselves ([seqlock_S1], [z_S1]); every
    ordering fact holds without it.

    For every [P], with no validity hypothesis:
    - Section [Core] (any [SeqLockCOH.Exec]): [WF_core], the five fields
      of [SeqLockCOH.WF] other than [wf_valid]; [WF_of_core] /
      [core_of_WF] ([WF] is [WF_core] plus [Valid]); [lp_inj_core]
      ([SeqLockCOH.lp_inj] from [WF_core] alone); the order chain
      [Pq_cross_core], [Pq_in_core], [Pq_after_core], [write_order_core],
      [read_order_core], [sl_tl_last_core], [sl_tl_first_core], and
      [seqlock_S1_ord_core] (with [K_ok K]) / [z_S1_ord_core]
      ([SeqLockCOH.seqlock_S1_ord] / [z_S1_ord] from [WF_core]).
    - Section [ExecutionGen]: [wu_src], [wu_call], [toEv_evt], [wit_nodup],
      [idx_pos] (the statements of the [SeqLockModule] lemmas of the same
      names, with [P] in place of the register tensor) and [SX_wf_core]
      ([WF_core] for [SX]).
    - Section [TransportGen]: [X_wf_core], [lpu_src], [phi_lpq], and three
      of the four fields of [WindowLinkTable.Positional] /
      [WindowLinkTableJ.PositionalJ] for the linearization call
      [SeqLockModule.lpu]: [lpu_inj] ([p_lp_inj]), [lpu_window]
      ([p_window]) and [lpu_S1_ord] ([p_S1_ord], with [K_ok K]).  The
      transport of the lp-sorted overlay calls along [SeqLockModule.phi]:
      [S1_transport_gen] (any filters [fA] / [fB] that agree along [phi]),
      its per-component form [S1_transport], and its unfiltered form
      [S1_transport_all], stated on the list of
      [WindowLinkTableJ.p_S1J].  [positionalJ_of_S1J]: for every joint
      overlay specification [nuJ], [p_S1J] alone gives
      [WindowLinkTableJ.PositionalJ ... nuJ ... lpu]; [positionalJ_of_ovl]
      reads [p_S1J] on the overlay events of [SX].
    - Reused unchanged from [SeqLockModule], whose statements never
      mentioned the underlay witness: the definitions [dcs], [blk_of],
      [rth], [recs], [tcs], [tn], [ix], [toEv], [SX], [lpu], [kpos],
      [phi], and the lemmas [rec_shape], [rec_window], [recs_in],
      [rec_keys], [tcs_nodup], [recs_keys_nodup], [recs_nodup],
      [invs_sorted], [recs_sorted], [trace_map_blk], [prog_trace],
      [off_foff], [usrc_inv], [ix_src], [key_index_lindex], [src_order],
      [replay_toEv] (Section [Execution]) and [phi_rec], [phi_all_ops],
      [phi_onto], [phi_inj], [phi_blk], [phi_ovl], [phi_sl], [phi_po],
      [secs_nodup] (Section [Transport]); also, directly or through the
      lemmas above, [window_at], [produced_shape], [catE_wcall],
      [window_bodies], [E_compat], [F_cross], [nuF_nil], [replay_merge],
      [nuE_replay], [replay_pre], [isort_transport] and the list lemmas.
      [SeqLockModule.lpu] is used as the linearization call, so
      [positional_gen] concludes about the same term as
      [SeqLockModule.positional].

    What uses validity.  [Valid X] is the field [wf_valid] of
    [SeqLockCOH.WF]; for [SX] it is equivalent to
    [replay SL.init (map (uev rc K) Wu)], a property of [Wu] alone
    ([SX_valid_iff]; [pre] and [post] ignore the index of an event).
    - [SX_wf_gen : Valid SX -> SeqLockCOH.WF rc K SX].
    - [positional_gen] (hypothesis [Hvalid : replay SL.init (map (uev rc K) Wu)]):
      only its field [p_S1] uses [Hvalid], because [SeqLockCOH.seqlock_S1]
      and [z_S1] take [SeqLockCOH.WF]; its other three fields are
      [lpu_inj], [lpu_window], [lpu_S1_ord].  The hypothesis is stated on
      [Wu], in the vocabulary of the underlay specification, rather than
      on the internal construction [SX]; [SX_valid_iff] converts.
    - [seqlock_module_rel_lin_gen]: the module theorem for every [P] with
      [HP : forall w, P w -> replay SL.init (map (uev rc K) w)].  [HP] says
      that every [P]-witness replays sequentially (SC) on the whole merged
      register state of [SeqLockCOH] (TicketLock [own] / [hold], x, y,
      and z).  No underlay specification that admits a non-SC witness
      (in particular no buffered or TSO one) satisfies it, so this
      theorem gives nothing beyond register cells; it only shows
      that the component structure of the underlay specification plays
      no role.

    Instances (kernel-checked to have literally the statements of the
    originals, through [Example ... : ltac:(let T := type of @... in exact T)]):
    - [SX_wf_of_gen] is [SeqLockModule.SX_wf];
    - [positional_of_gen] is [SeqLockModule.positional];
    - [seqlock_module_rel_lin_K_of_gen] is
      [SeqLockModule.seqlock_module_rel_lin_K].
    Each is the generic lemma at [P := BL.nuE_all SL.comp_dec compE (nuEc rc K)],
    with validity from [SeqLockModule.nuE_replay].  So the register
    specification enters [SeqLockModule]'s bridge only through validity.

    How [P] reaches [BracketedLink] / [WindowLinkTable].  Their lemmas
    ([BL.wu_src], [wu_res_src], [wu_key_inj], [before_pos], [inv_order],
    [WLT.call_at_spec]) are stated for a witness of a tensor
    [BL.nuE_all comp_dec compE nuEc].  A witness for [P] is a witness for
    the one-component tensor [Comp := unit], [compE := fun _ => tt],
    [nuEc := fun _ => P] ([nuE_all_unit], [witness_unit]; from
    [WindowLinkTableJ.nuE_all_const_gen] and
    [WindowLinkTableJ.rel_lin_witness_nu_mono]).  [seqlock_module_rel_lin_gen]
    uses the constant component map [fun _ => SL.CSL] over [SL.CompT]
    instead ([WindowLinkTableJ.nuE_all_const]), because
    [WindowLinkTable.window_link_table] shares [Comp] between the underlay
    and the overlay.

    What is copied, and why.  Sections [Execution] and [Transport] of
    [SeqLockModule] fix the register witness in their context
    (SeqLockModule.v:695-696 and :1018-1019).  After the sections are
    closed, every lemma whose proof uses [HWu] takes that register witness
    as an argument and cannot be applied to a witness for another [P].
    These lemmas are copied here, with the [BL] / [WLT] calls instantiated
    as above:
    - [wu_src], [wu_call], [toEv_evt], [wit_nodup], [idx_pos]
      (SeqLockModule.v:806-807, :839-881, :886-899);
    - [SX_wf] (:947-1000) without its last bullet, as [SX_wf_core];
    - [X_wf] (:1025-1026) as [X_wf_core]; [lpu_src], [phi_lpq]
      (:1083-1105); [S1_transport] (:1148-1169), generalized to
      [S1_transport_gen] and from [WF_core];
    - [positional] (:1171-1224) as [positional_gen]; its first, second and
      last bullets (:1176-1182, :1205-1223) are split off as [lpu_inj],
      [lpu_window] and [lpu_S1_ord] (the last from [WF_core]).
    From [SeqLockCOH] (Section [Layer], under [Hypothesis HW : WF rc K X],
    although these proofs use only [wf_complete] and [wf_pres]), copied as
    [*_core] with [WF_core] in place of [WF]:
    - [Pq_spec], [Pq_inj], [lp_inj] (SeqLockCOH.v:747-755, :813-828,
      :1250-1258);
    - [Pq_cross], [Pq_in], [Pq_after] (:774-810), [write_order]
      (:866-873), [upres_ok] / [read_order] (:950-977), [sl_tl_last],
      [sl_tl_first], [seqlock_S1_ord] (:1317-1353), [z_S1_ord]
      (:1445-1462); the four [Let]s on [K_ok] (:718-725) become
      [K_ok_cats].
    [SeqLockCOH.v] and [SeqLockModule.v] are not changed.

    Intended use (item D-1 of the buffered-cell plan).  For a buffered
    (hybrid) underlay specification, the [SX] built from the witness is
    not valid for the register state machine of [SeqLockCOH].  D-2 is
    meant to obtain [WindowLinkTableJ.PositionalJ] from
    [positionalJ_of_S1J] (or [positionalJ_of_ovl]), so that only the joint
    obligation [p_S1J] remains, and to discharge it by combining
    [SX_wf_core] with the SC-ification of S-1.  (If S-1's buffered
    well-formedness is stated as [WF_core] of an [SeqLockCOH.Exec] call
    part plus a hybrid validity, [SX_wf_core] supplies the first part
    directly.)  Nothing about the buffered case is proved here.

    Only complete executions and safety, as in [SeqLockModule]. *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith micromega.Lia.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedModuleFacts.
Require Import examples.Relaxed.BracketedLink.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.WindowLinkTable.
Require Import examples.Relaxed.WindowTableJ.
Require Import examples.Relaxed.WindowLinkTableJ.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.SeqLockProg.
Require Import examples.Relaxed.SeqLockModule.

Import ListNotations.

Module SeqLockModuleGen.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedModuleFacts.
  Import SeqLockProg.SeqLockProg.

  Module BL := BracketedLink.BracketedLink.
  Module WC := WindowComposition.WindowComposition.
  Module WLT := WindowLinkTable.WindowLinkTable.
  Module WTJ := WindowTableJ.WindowTableJ.
  Module WLTJ := WindowLinkTableJ.WindowLinkTableJ.
  Module SLM := SeqLockModule.SeqLockModule.

  (** ** An arbitrary underlay specification as a one-component tensor *)

  Lemma nuE_all_unit {G : RelaxedSig.t} (P : list (Op G) -> Prop) w :
    BL.nuE_all (E := G) WTJ.unit_dec (fun _ => tt) (fun _ => P) w <-> P w.
  Proof.
    apply WLTJ.nuE_all_const_gen; [intros l; apply iff_refl|].
    intros [] Hn. exfalso. apply Hn. reflexivity.
  Qed.

  Lemma witness_unit {G : RelaxedSig.t} {X : Type} (sel : X -> option (ThreadEvent G)) (L : list X)
      indep (P : list (Op G) -> Prop) W :
    rel_lin_witness sel L indep P W ->
    rel_lin_witness sel L indep (BL.nuE_all (E := G) WTJ.unit_dec (fun _ => tt) (fun _ => P)) W.
  Proof. apply WLTJ.rel_lin_witness_nu_mono. intros w. apply (proj2 (nuE_all_unit P w)). Qed.

  (** ** [SeqLockCOH.WF] without validity *)

  (** The field [wf_valid] of [SeqLockCOH.WF]. *)
  Definition Valid (X : SL.Exec) : Prop :=
    forall p e, nth_error (SL.wit X) p = Some e -> SL.pre (SL.at_ X p) e = true.

  (** The four category conditions of [SeqLockCOH.K_ok]. *)
  Lemma K_ok_cats K : SL.K_ok K = true ->
    WT.isW (SL.k_acq K) = true /\ WT.isW (SL.k_rel K) = true /\
    WT.isR (SL.k_gt K) = true /\ WT.isR (SL.k_tt K) = true.
  Proof.
    unfold SL.K_ok. intros H. repeat (apply andb_true_iff in H as [H ?]).
    repeat split; assumption.
  Qed.

  Section Core.
    Context (rc : bool) (K : SL.TLCats) (X : SL.Exec).

    (** The fields [wf_nodup], [wf_ths], [wf_call], [wf_complete],
        [wf_pres] of [SeqLockCOH.WF], with the same statements. *)
    Record WF_core : Prop := {
      wfc_nodup : NoDup (SL.wit X);
      wfc_ths : NoDup (SL.ths X);
      wfc_call : forall e, In e (SL.wit X) ->
                   In (SL.th e) (SL.ths X) /\
                   nth_error (SL.trace (SL.prog X (SL.th e))) (SL.ix e) = Some (SL.call e);
      wfc_complete : forall t i, In t (SL.ths X) -> i < length (SL.trace (SL.prog X t)) ->
                       In (SL.evt X t i) (SL.wit X);
      wfc_pres : forall e1 e2, In e1 (SL.wit X) -> In e2 (SL.wit X) -> SL.th e1 = SL.th e2 ->
                   SL.ix e1 < SL.ix e2 -> SL.upres rc K (SL.call e1) (SL.call e2) = true ->
                   SL.idx e1 (SL.wit X) < SL.idx e2 (SL.wit X);
    }.

    Lemma WF_of_core : WF_core -> Valid X -> SL.WF rc K X.
    Proof. intros [H1 H2 H3 H4 H5] H6. exact (SL.Build_WF rc K X H1 H2 H3 H4 H5 H6). Qed.

    Lemma core_of_WF : SL.WF rc K X -> WF_core.
    Proof. intros [H1 H2 H3 H4 H5 _]. exact (Build_WF_core H1 H2 H3 H4 H5). Qed.

    Lemma valid_of_WF : SL.WF rc K X -> Valid X.
    Proof. intros HW. exact (SL.wf_valid _ _ _ HW). Qed.

    (** [SeqLockCOH.Pq_spec], [Pq_inj], [lp_inj] (SeqLockCOH.v:747, :813,
        :1250), whose proofs use only [wf_complete]. *)
    Lemma Pq_spec_core (HC : WF_core) q k i c :
      In (fst q) (SL.ths X) -> SL.blk X q = Some k -> nth_error (SL.calls k) i = Some c ->
      nth_error (SL.wit X) (SL.Pq X q i) =
        Some (SL.evt X (fst q) (SL.off (SL.prog X (fst q)) (snd q) + i)) /\
      SL.call (SL.evt X (fst q) (SL.off (SL.prog X (fst q)) (snd q) + i)) = c.
    Proof.
      intros Ht Hb Hi. destruct (SL.blk_evt X _ _ _ _ _ Hb Hi) as [Ec Hlt].
      split; [|exact Ec].
      apply SL.idx_nth. apply (wfc_complete HC); assumption.
    Qed.

    Lemma Pq_inj_core (HC : WF_core) q q' k k' i i' c c' :
      In (fst q) (SL.ths X) -> In (fst q') (SL.ths X) -> SL.blk X q = Some k -> SL.blk X q' = Some k' ->
      nth_error (SL.calls k) i = Some c -> nth_error (SL.calls k') i' = Some c' ->
      SL.Pq X q i = SL.Pq X q' i' -> q = q' /\ i = i'.
    Proof.
      destruct q as [t j], q' as [t' j']. cbn. intros Ht Ht' Hb Hb' Hi Hi' E.
      destruct (Pq_spec_core HC (t, j) k i c Ht Hb Hi) as [Hn _].
      destruct (Pq_spec_core HC (t', j') k' i' c' Ht' Hb' Hi') as [Hn' _].
      cbn [fst snd] in *. rewrite E in Hn. rewrite Hn in Hn'. injection Hn' as Et Ei _. subst t'.
      assert (Li : i < length (SL.calls k)) by (apply nth_error_Some; congruence).
      assert (Li' : i' < length (SL.calls k')) by (apply nth_error_Some; congruence).
      destruct (Nat.lt_trichotomy j j') as [Hlt|[<-|Hlt]].
      - pose proof (SL.off_lt _ _ _ _ _ Hb Li Hlt). lia.
      - split; [reflexivity|]. lia.
      - pose proof (SL.off_lt _ _ _ _ _ Hb' Li' Hlt). lia.
    Qed.

    Lemma lp_inj_core (HC : WF_core) q q' :
      In q (SL.all_ops X) -> In q' (SL.all_ops X) -> SL.lpq X q = SL.lpq X q' -> q = q'.
    Proof.
      intros Hq Hq' E.
      destruct (SL.all_ops_blk X q Hq) as [k Hk]. destruct (SL.all_ops_blk X q' Hq') as [k' Hk'].
      destruct (SL.lpi_call X q k Hk) as [c Hc]. destruct (SL.lpi_call X q' k' Hk') as [c' Hc'].
      rewrite (SL.lpq_Pq X q k Hk), (SL.lpq_Pq X q' k' Hk') in E.
      apply SL.all_ops_In in Hq as [Ht _]. apply SL.all_ops_In in Hq' as [Ht' _].
      exact (proj1 (Pq_inj_core HC q q' k k' _ _ c c' Ht Ht' Hk Hk' Hc Hc' E)).
    Qed.

    (** *** The order chain from [WF_core]

        [SeqLockCOH.Pq_cross], [Pq_in], [Pq_after] (SeqLockCOH.v:774-810),
        [write_order] (:866-873), [upres_ok] / [read_order] (:950-977),
        [sl_tl_last], [sl_tl_first], [seqlock_S1_ord] (:1317-1353) and
        [z_S1_ord] (:1445-1462).  Their proofs use only [wf_complete]
        (through [Pq_spec]) and [wf_pres], plus [K_ok K] for the SeqLock
        blocks; never [wf_valid]. *)
    Lemma Pq_cross_core (HC : WF_core) t j k j' k' i i' c c' :
      In t (SL.ths X) -> nth_error (SL.prog X t) j = Some k -> nth_error (SL.prog X t) j' = Some k' ->
      nth_error (SL.calls k) i = Some c -> nth_error (SL.calls k') i' = Some c' ->
      SL.off (SL.prog X t) j + i < SL.off (SL.prog X t) j' + i' -> SL.upres rc K c c' = true ->
      SL.Pq X (t, j) i < SL.Pq X (t, j') i'.
    Proof.
      intros Ht Hj Hj' Hi Hi' Hlt Hu.
      destruct (Pq_spec_core HC (t, j) k i c Ht Hj Hi) as [Hn Ec].
      destruct (Pq_spec_core HC (t, j') k' i' c' Ht Hj' Hi') as [Hn' Ec'].
      unfold SL.Pq, SL.P in *. cbn [fst snd] in *.
      apply (wfc_pres HC).
      - eapply nth_error_In. exact Hn.
      - eapply nth_error_In. exact Hn'.
      - reflexivity.
      - exact Hlt.
      - rewrite Ec, Ec'. exact Hu.
    Qed.

    Lemma Pq_in_core (HC : WF_core) q k i i' c c' :
      In (fst q) (SL.ths X) -> SL.blk X q = Some k ->
      nth_error (SL.calls k) i = Some c -> nth_error (SL.calls k) i' = Some c' ->
      i < i' -> SL.upres rc K c c' = true -> SL.Pq X q i < SL.Pq X q i'.
    Proof.
      destruct q as [t j]. intros Ht Hb Hi Hi' Hlt Hu.
      apply (Pq_cross_core HC t j k j k i i' c c'); try assumption. lia.
    Qed.

    Lemma Pq_after_core (HC : WF_core) q k j' k' i i' c c' :
      In (fst q) (SL.ths X) -> SL.blk X q = Some k -> nth_error (SL.prog X (fst q)) j' = Some k' ->
      nth_error (SL.calls k) i = Some c -> nth_error (SL.calls k') i' = Some c' ->
      snd q < j' -> SL.upres rc K c c' = true -> SL.Pq X q i < SL.Pq X (fst q, j') i'.
    Proof.
      destruct q as [t j]. cbn. intros Ht Hb Hb' Hi Hi' Hlt Hu.
      apply (Pq_cross_core HC t j k j' k' i i' c c'); try assumption.
      assert (i < length (SL.calls k)) by (apply nth_error_Some; congruence).
      pose proof (SL.off_lt _ _ _ _ _ Hb H Hlt). lia.
    Qed.

    Lemma write_order_core (HC : WF_core) (HK : SL.K_ok K = true) q vx vy :
      In (fst q) (SL.ths X) -> SL.blk X q = Some (SL.BW vx vy) ->
      SL.Pq X q 0 < SL.Pq X q 1 /\ SL.Pq X q 1 < SL.Pq X q 2 /\ SL.Pq X q 1 < SL.Pq X q 3 /\
      SL.Pq X q 2 < SL.Pq X q 4 /\ SL.Pq X q 3 < SL.Pq X q 4 /\ SL.Pq X q 4 < SL.Pq X q 5.
    Proof.
      intros Hq Hb. destruct (K_ok_cats K HK) as (HKa & HKr & HKg & HKt).
      repeat split; eapply (Pq_in_core HC q (SL.BW vx vy)); try eassumption; try reflexivity; try lia;
        unfold SL.upres; cbn [SL.uobj SL.same_obj SL.ucat orb]; cbn;
        first [ apply SL.dto_W_wmb; assumption | apply SL.dto_wmb_W; first [assumption | reflexivity] ].
    Qed.

    Local Ltac upres_ok :=
      unfold SL.upres; cbn [SL.uobj SL.same_obj SL.ucat orb];
      first [ reflexivity
            | apply SL.dto_W_wmb; first [assumption | reflexivity]
            | apply SL.dto_wmb_W; first [assumption | reflexivity]
            | apply SL.dto_R_rmb; first [assumption | reflexivity]
            | apply SL.dto_rmb_R; first [assumption | reflexivity] ].

    Lemma read_order_core (HC : WF_core) (HK : SL.K_ok K = true) r fs s a b :
      In (fst r) (SL.ths X) -> SL.blk X r = Some (SL.BR fs s a b) ->
      SL.Pq X r (SL.base (SL.BR fs s a b)) < SL.Pq X r (SL.base (SL.BR fs s a b) + 1) /\
      SL.Pq X r (SL.base (SL.BR fs s a b) + 1) < SL.Pq X r (SL.base (SL.BR fs s a b) + 2) /\
      SL.Pq X r (SL.base (SL.BR fs s a b) + 1) < SL.Pq X r (SL.base (SL.BR fs s a b) + 3) /\
      SL.Pq X r (SL.base (SL.BR fs s a b) + 2) < SL.Pq X r (SL.base (SL.BR fs s a b) + 4) /\
      SL.Pq X r (SL.base (SL.BR fs s a b) + 3) < SL.Pq X r (SL.base (SL.BR fs s a b) + 4) /\
      SL.Pq X r (SL.base (SL.BR fs s a b) + 4) < SL.Pq X r (SL.base (SL.BR fs s a b) + 5) /\
      SL.Pq X r (SL.base (SL.BR fs s a b)) < SL.Pq X r (SL.base (SL.BR fs s a b) + 5).
    Proof.
      intros Hr Hb. destruct (K_ok_cats K HK) as (HKa & HKr & HKg & HKt).
      pose proof (SL.read_call0 fs s a b) as R0.
      repeat split.
      - eapply (Pq_in_core HC r _ _ _ _ _ Hr Hb R0 (SL.read_call fs s a b 1 SL.RmbC eq_refl));
          [lia|upres_ok].
      - eapply (Pq_in_core HC r _ _ _ _ _ Hr Hb (SL.read_call fs s a b 1 SL.RmbC eq_refl)
                  (SL.read_call fs s a b 2 (SL.RdX a) eq_refl)); [lia|upres_ok].
      - eapply (Pq_in_core HC r _ _ _ _ _ Hr Hb (SL.read_call fs s a b 1 SL.RmbC eq_refl)
                  (SL.read_call fs s a b 3 (SL.RdY b) eq_refl)); [lia|upres_ok].
      - eapply (Pq_in_core HC r _ _ _ _ _ Hr Hb (SL.read_call fs s a b 2 (SL.RdX a) eq_refl)
                  (SL.read_call fs s a b 4 SL.RmbC eq_refl)); [lia|upres_ok].
      - eapply (Pq_in_core HC r _ _ _ _ _ Hr Hb (SL.read_call fs s a b 3 (SL.RdY b) eq_refl)
                  (SL.read_call fs s a b 4 SL.RmbC eq_refl)); [lia|upres_ok].
      - eapply (Pq_in_core HC r _ _ _ _ _ Hr Hb (SL.read_call fs s a b 4 SL.RmbC eq_refl)
                  (SL.read_call fs s a b 5 (SL.TT s false) eq_refl)); [lia|upres_ok].
      - eapply (Pq_in_core HC r _ _ _ _ _ Hr Hb R0 (SL.read_call fs s a b 5 (SL.TT s false) eq_refl));
          [lia|upres_ok].
    Qed.

    Lemma sl_tl_last_core (HC : WF_core) (HK : SL.K_ok K = true) q k :
      In (fst q) (SL.ths X) -> SL.blk X q = Some k -> SL.is_sl k = true ->
      exists i c, nth_error (SL.calls k) i = Some c /\ SL.uobj c = SL.OTL /\ SL.lpq X q < SL.Pq X q i.
    Proof.
      intros Hq Hb Hs. destruct k as [vx vy|fs s a b|v|v]; try discriminate.
      - exists 5, SL.Rel. split; [reflexivity|]. split; [reflexivity|].
        rewrite (SL.lpq_W X q vx vy Hb).
        destruct (write_order_core HC HK q vx vy Hq Hb) as (? & ? & ? & ? & ? & ?). lia.
      - exists (SL.base (SL.BR fs s a b) + 5), (SL.TT s false).
        split; [apply SL.read_call; reflexivity|]. split; [reflexivity|].
        rewrite (SL.lpq_R X q fs s a b Hb).
        destruct (read_order_core HC HK q fs s a b Hq Hb) as (? & ? & ? & ? & ? & ? & ?). lia.
    Qed.

    Lemma sl_tl_first_core (HC : WF_core) (HK : SL.K_ok K = true) q k :
      In (fst q) (SL.ths X) -> SL.blk X q = Some k -> SL.is_sl k = true ->
      exists i c, nth_error (SL.calls k) i = Some c /\ SL.uobj c = SL.OTL /\ SL.Pq X q i < SL.lpq X q.
    Proof.
      intros Hq Hb Hs. destruct k as [vx vy|fs s a b|v|v]; try discriminate.
      - exists 0, SL.Acq. split; [reflexivity|]. split; [reflexivity|].
        rewrite (SL.lpq_W X q vx vy Hb).
        destruct (write_order_core HC HK q vx vy Hq Hb) as (? & ? & ? & ? & ? & ?). lia.
      - exists (SL.base (SL.BR fs s a b)), (SL.GT s).
        split; [apply SL.read_call0|]. split; [reflexivity|].
        rewrite (SL.lpq_R X q fs s a b Hb).
        destruct (read_order_core HC HK q fs s a b Hq Hb) as (? & ? & ? & ? & ? & ? & ?). lia.
    Qed.

    (** [SeqLockCOH.seqlock_S1_ord] from [WF_core]. *)
    Theorem seqlock_S1_ord_core (HC : WF_core) (HK : SL.K_ok K = true) q q' :
      In q (SL.sl_ops X) -> In q' (SL.sl_ops X) -> fst q = fst q' -> snd q < snd q' ->
      SL.lpq X q < SL.lpq X q'.
    Proof.
      intros Hq Hq' Et Hlt.
      destruct (SL.sl_ops_In X q Hq) as [Hqo (k & Hb & Hs)].
      destruct (SL.sl_ops_In X q' Hq') as [Hqo' (k' & Hb' & Hs')].
      assert (Ht : In (fst q) (SL.ths X)) by (apply SL.all_ops_In in Hqo; tauto).
      assert (Ht' : In (fst q') (SL.ths X)) by (apply SL.all_ops_In in Hqo'; tauto).
      destruct (sl_tl_last_core HC HK q k Ht Hb Hs) as (i & c & Hc & Oc & L1).
      destruct (sl_tl_first_core HC HK q' k' Ht' Hb' Hs') as (i' & c' & Hc' & Oc' & L2).
      assert (Hb'' : nth_error (SL.prog X (fst q)) (snd q') = Some k') by (rewrite Et; exact Hb').
      pose proof (Pq_after_core HC q k (snd q') k' i i' c c' Ht Hb Hb'' Hc Hc' Hlt) as H.
      assert (Hu : SL.upres rc K c c' = true) by (unfold SL.upres; rewrite Oc, Oc'; reflexivity).
      specialize (H Hu). destruct q' as [t' j']. cbn in Et, H |- *. subst t'. lia.
    Qed.

    (** [SeqLockCOH.z_S1_ord] from [WF_core]. *)
    Theorem z_S1_ord_core (HC : WF_core) q q' :
      In q (SL.z_ops X) -> In q' (SL.z_ops X) -> fst q = fst q' -> snd q < snd q' ->
      SL.lpq X q < SL.lpq X q'.
    Proof.
      intros Hq Hq' Et Hlt.
      apply filter_In in Hq as [Hqo Hs]. apply filter_In in Hq' as [Hqo' Hs'].
      destruct (SL.all_ops_blk X q Hqo) as [k Hb]. destruct (SL.all_ops_blk X q' Hqo') as [k' Hb'].
      assert (Ht : In (fst q) (SL.ths X)) by (apply SL.all_ops_In in Hqo; tauto).
      unfold SL.is_sl_op in Hs, Hs'. rewrite Hb in Hs. rewrite Hb' in Hs'.
      assert (Hz : forall k, SL.is_sl k = false ->
                     exists c, nth_error (SL.calls k) 0 = Some c /\ SL.uobj c = SL.OZ /\ SL.lpi k = 0).
      { intros [] H; cbn in H; try discriminate; eexists; (split; [reflexivity|split; reflexivity]). }
      destruct (Hz k ltac:(destruct (SL.is_sl k); [discriminate|reflexivity])) as (c & Hc & Oc & L).
      destruct (Hz k' ltac:(destruct (SL.is_sl k'); [discriminate|reflexivity])) as (c' & Hc' & Oc' & L').
      rewrite (SL.lpq_Pq X q k Hb), (SL.lpq_Pq X q' k' Hb'), L, L'.
      assert (Hb'' : nth_error (SL.prog X (fst q)) (snd q') = Some k') by (rewrite Et; exact Hb').
      pose proof (Pq_after_core HC q k (snd q') k' 0 0 c c' Ht Hb Hb'' Hc Hc' Hlt) as H.
      assert (Hu : SL.upres rc K c c' = true) by (unfold SL.upres; rewrite Oc, Oc'; reflexivity).
      specialize (H Hu). destruct q' as [t' j']. cbn in Et, H |- *. subst t'. exact H.
    Qed.
  End Core.

  (** ** Validity of [SX] is a property of [Wu] *)

  Lemma replay_of_pre s l :
    (forall p e, nth_error l p = Some e -> SL.pre (SL.run s (firstn p l)) e = true) -> SLM.replay s l.
  Proof.
    revert s. induction l as [|e l IH]; intros s H; [exact I|].
    split.
    - exact (H 0 e eq_refl).
    - apply IH. intros p e' Hp. exact (H (S p) e' Hp).
  Qed.

  Lemma valid_iff_replay X : Valid X <-> SLM.replay SL.init (SL.wit X).
  Proof.
    split.
    - intros H. apply replay_of_pre. exact H.
    - intros H p e Hn. exact (SLM.replay_pre SL.init _ H p e Hn).
  Qed.

  (** [pre] and [post] ignore the index, so [uev] (index 0) and [toEv]
      (the index in [SX]) replay alike. *)
  Lemma replay_toEv_iff rc K (VE : LTS (E rc K)) (ic : @IConfig (E rc K) (F rc) VE) l s :
    SLM.replay s (map (SLM.uev rc K) l) <-> SLM.replay s (map (SLM.toEv rc K VE ic) l).
  Proof.
    split; [apply SLM.replay_toEv|].
    revert s. induction l as [|u l IH]; intros s H; [exact I|].
    destruct H as [Hp H]. split; [exact Hp|]. exact (IH _ H).
  Qed.

  Lemma SX_valid_iff rc K (VE : LTS (E rc K)) (ic : @IConfig (E rc K) (F rc) VE) Wu :
    Valid (SLM.SX rc K VE ic Wu) <-> SLM.replay SL.init (map (SLM.uev rc K) Wu).
  Proof.
    split.
    - intros H. apply (proj2 (replay_toEv_iff rc K VE ic Wu SL.init)).
      exact (proj1 (valid_iff_replay _) H).
    - intros H. apply (proj2 (valid_iff_replay _)).
      exact (proj1 (replay_toEv_iff rc K VE ic Wu SL.init) H).
  Qed.

  (** ** The underlay witness as an execution of [SeqLockCOH], for any [P] *)

  Section ExecutionGen.
    Context (rc : bool) (K : SL.TLCats).
    Local Abbreviation G := (E rc K).
    Context (VE : LTS G).
    Context (IT : list (@ITraceEvent G (F rc))) (ic : @IConfig G (F rc) VE).
    Context (Hinv : IInv VE (M rc K) IT ic) (Hq : ic_queue VE ic = []).
    Context (Wu : list (Op G)) (P : list (Op G) -> Prop).
    Context (HWu : rel_lin_witness BL.usel IT (semi_independent G) P Wu).
    Context (r0 : @InvRec G (F rc)).

    (** [HWu] as a witness of the one-component tensor. *)
    Local Abbreviation HWu1 := (witness_unit BL.usel IT (semi_independent G) P Wu HWu).

    (** Reused from [SeqLockModule] (no [HWu] in their statements). *)
    Local Abbreviation SX := (SLM.SX rc K VE ic Wu).
    Local Abbreviation dcs := (SLM.dcs rc K).
    Local Abbreviation rth := (SLM.rth rc K).
    Local Abbreviation recs := (SLM.recs rc K VE ic).
    Local Abbreviation tcs := (SLM.tcs rc K VE ic).
    Local Abbreviation tn := (SLM.tn rc K).
    Local Abbreviation ix := (SLM.ix rc K VE ic).
    Local Abbreviation toEv := (SLM.toEv rc K VE ic).
    Local Abbreviation rec_shape := (SLM.rec_shape rc K VE IT ic Hinv).
    Local Abbreviation recs_in := (SLM.recs_in rc K VE ic).
    Local Abbreviation tcs_nodup := (SLM.tcs_nodup rc K VE IT ic Hinv).
    Local Abbreviation prog_trace := (SLM.prog_trace rc K VE IT ic Hinv Wu).
    Local Abbreviation usrc_inv := (SLM.usrc_inv rc K VE IT ic).
    Local Abbreviation ix_src := (SLM.ix_src rc K VE IT ic Hinv).
    Local Abbreviation src_order := (SLM.src_order rc K VE IT ic Hinv).

    (** *** Where the calls of the witness are (copied, SeqLockModule.v:806-881, :886-899) *)

    Lemma wu_src u : In u Wu -> exists r j m p, BL.usrc VE IT ic u r j m p.
    Proof. exact (BL.wu_src VE (M rc K) WTJ.unit_dec (fun _ => tt) (fun _ => P) IT ic Hinv Wu HWu1 u). Qed.

    Lemma wu_call u : In u Wu ->
      In (tn u) (SL.ths SX) /\ nth_error (tcs (tn u)) (ix u) = Some (snd (op_key u), SLM.uc rc K u).
    Proof.
      intros Hu. destruct (wu_src u Hu) as (r & j & m & p & Hs).
      destruct (usrc_inv u r j m p Hs) as [Hr Hj].
      assert (Hin : In r (recs (rth r))) by (apply recs_in; auto).
      destruct (In_nth_error _ _ Hin) as [jr Hjr].
      destruct (ix_src u r j m p jr Hs Hjr) as (Ht & Hix & c & Hc).
      assert (Ec : c = SLM.uc rc K u).
      { destruct (BL.wu_res_src VE (M rc K) (SLM.keyE_dec rc K) WTJ.unit_dec (fun _ => tt) (fun _ => P)
                    IT ic Hinv Wu HWu1 r0 u Hu) as (r' & j' & m' & p' & Hr' & Hj' & Hm' & _ & Ho').
        assert (r' = r).
        { apply (record_key_unique _ _ _ _ Hinv); [exact Hr'|exact Hr|].
          rewrite <- Ho'. exact (BL.usrc_owner VE (M rc K) (SLM.keyE_dec rc K) IT ic Hinv r0 u r j m p Hs). }
        subst r'.
        destruct (rec_shape r Hr) as (_ & _ & Hnd & Hperm & _ & _).
        assert (Hres : In (snd (op_key u), SLM.uc rc K u) (res_list (BL.ltr r))).
        { unfold SLM.uc. apply (SLM.res_list_in rc K (BL.ltr r) j' (untag m') _ (op_op u) (op_ret u)).
          - unfold BL.ltr. rewrite nth_error_map, Hj'. reflexivity.
          - rewrite Hm'. reflexivity. }
        apply (Permutation_in _ Hperm) in Hres.
        exact (SLM.pair_nodup_fst (dcs r) _ _ _ Hnd (nth_error_In _ _ Hc) Hres). }
      subst c. split.
      - rewrite Ht. cbn [SL.ths SLM.SX]. apply nodup_In, in_map, Hr.
      - rewrite Hix, Ht. unfold SLM.tcs. apply (SLM.flat_map_nth dcs _ _ _ _ _ Hjr Hc).
    Qed.

    Lemma toEv_evt u : In u Wu -> toEv u = SL.evt SX (tn u) (ix u).
    Proof.
      intros Hu. destruct (wu_call u Hu) as [_ Hn]. unfold SL.evt, SLM.toEv. f_equal.
      symmetry. apply nth_error_nth. rewrite prog_trace, nth_error_map, Hn. reflexivity.
    Qed.

    Lemma wit_nodup : NoDup (map toEv Wu).
    Proof.
      pose proof HWu as (_ & Hnd & _). apply SLM.NoDup_map_in; [exact (NoDup_map_inv _ _ Hnd)|].
      intros u u' Hu Hu' Eq. unfold SLM.toEv in Eq. injection Eq as Et Ei _.
      apply (BL.wu_key_inj (E := G) WTJ.unit_dec (fun _ => tt) (fun _ => P) IT Wu HWu1 u u' Hu Hu').
      destruct (wu_call u Hu) as [_ Hn]. destruct (wu_call u' Hu') as [_ Hn'].
      rewrite <- Et, <- Ei, Hn in Hn'. injection Hn' as Eh _.
      apply injective_projections; [|exact Eh].
      apply Pos2Nat.inj. exact Et.
    Qed.

    Lemma idx_pos u : In u Wu -> SL.idx (toEv u) (SL.wit SX) = BL.pos (SLM.keyE_dec rc K) Wu u.
    Proof.
      intros Hu. unfold BL.pos. rewrite SLM.key_index_lindex.
      set (i := SLM.lindex (SLM.keyE_dec rc K) (op_key u) (map op_key Wu)).
      assert (Hi : nth_error (map op_key Wu) i = Some (op_key u)) by (apply SLM.lindex_nth, in_map, Hu).
      rewrite nth_error_map in Hi.
      destruct (nth_error Wu i) as [u'|] eqn:Hu'; cbn in Hi; [|discriminate].
      injection Hi as Hk.
      assert (u' = u).
      { apply (BL.wu_key_inj (E := G) WTJ.unit_dec (fun _ => tt) (fun _ => P) IT Wu HWu1);
          [|exact Hu|exact Hk].
        eapply nth_error_In. exact Hu'. }
      subst u'. apply SL.nth_idx; [exact wit_nodup|].
      cbn [SL.wit SLM.SX]. rewrite nth_error_map, Hu'. reflexivity.
    Qed.

    (** *** Well-formedness without validity (SeqLockModule.v:947-998) *)

    Lemma SX_wf_core : WF_core rc K SX.
    Proof.
      constructor.
      - exact wit_nodup.
      - apply NoDup_nodup.
      - intros e He. cbn [SL.wit SLM.SX] in He. apply in_map_iff in He as (u & <- & Hu).
        destruct (wu_call u Hu) as [Ht Hn]. split; [exact Ht|].
        change (nth_error (SL.trace (SL.prog SX (tn u))) (ix u) = Some (SLM.uc rc K u)).
        rewrite prog_trace, nth_error_map, Hn. reflexivity.
      - intros t i _ Hi.
        rewrite prog_trace, length_map in Hi.
        destruct (nth_error (tcs t) i) as [[h c]|] eqn:Hti; [|apply nth_error_None in Hti; lia].
        pose proof Hti as Hti'. unfold SLM.tcs in Hti'.
        destruct (SLM.flat_map_nth_inv dcs _ _ _ Hti') as (jr & r & i' & Hjr & Ei & Hc).
        assert (Hr : In r (recs t)) by (eapply nth_error_In; exact Hjr).
        apply recs_in in Hr as [Hr Hrt].
        destruct (rec_shape r Hr) as (_ & Hinvl & _ & _ & Htid & _).
        assert (Hil : nth_error (inv_list (BL.ltr r)) i' = Some (h, op_of c))
          by (rewrite Hinvl, nth_error_map, Hc; reflexivity).
        destruct (SLM.inv_pos_spec _ _ _ _ Hil) as (ev & Hev & He & _).
        set (jp := SLM.inv_pos i' (BL.ltr r)) in *.
        assert (Hev' := Hev). unfold BL.ltr in Hev'. rewrite nth_error_map in Hev'.
        destruct (nth_error (ir_trace r) jp) as [m|] eqn:Hm; cbn in Hev'; [|discriminate].
        injection Hev' as Hev'.
        destruct (complete_all_emitted _ _ _ _ Hinv r jp m Hq Hr Hm) as (p & Hp).
        pose proof HWu as (_ & _ & _ & Hall & _).
        assert (Htev : te_tid _ ev = fst (ir_key r)).
        { rewrite Forall_forall in Htid. apply Htid. eapply nth_error_In. exact Hev. }
        destruct (Hall p (fst (ir_key r), h) (op_of c)) as (u & Hu & Hk).
        { exists (IUnder (ir_start r + jp, Build_TaggedScheduledEvent (ir_key r) m)).
          split; [exact Hp|].
          change (Some (untag m) = Some (Build_ThreadEvent (fst (ir_key r)) (@InvEv G h (op_of c)))).
          rewrite Hev'. destruct ev as [t' e]. cbn in He, Htev. subst. reflexivity. }
        assert (Htu : tn u = t) by (unfold SLM.tn; rewrite Hk; exact Hrt).
        assert (Hix : ix u = i).
        { unfold SLM.ix. rewrite Htu, Hk. apply SLM.lindex_of_nth; [apply tcs_nodup|].
          rewrite nth_error_map, Hti. reflexivity. }
        rewrite <- Hix, <- Htu, <- (toEv_evt u Hu). cbn [SL.wit SLM.SX]. apply in_map, Hu.
      - intros e1 e2 He1 He2 Ht Hlt Hu.
        cbn [SL.wit SLM.SX] in He1, He2.
        apply in_map_iff in He1 as (u1 & <- & Hu1). apply in_map_iff in He2 as (u2 & <- & Hu2).
        cbn [SLM.toEv SL.th SL.ix SL.call] in Ht, Hlt, Hu.
        rewrite (idx_pos u1 Hu1), (idx_pos u2 Hu2).
        apply (BL.before_pos (SLM.keyE_dec rc K) WTJ.unit_dec (fun _ => tt) (fun _ => P) IT Wu HWu1).
        destruct (wu_src u1 Hu1) as (r1 & j1 & m1 & p1 & Hs1).
        destruct (wu_src u2 Hu2) as (r2 & j2 & m2 & p2 & Hs2).
        apply (BL.inv_order VE (M rc K) WTJ.unit_dec (fun _ => tt) (fun _ => P) IT ic Hinv Wu HWu1
                 u1 u2 r1 j1 m1 p1 r2 j2 m2 p2 Hu1 Hu2 Hs1 Hs2).
        + exact (src_order u1 u2 r1 j1 m1 p1 r2 j2 m2 p2 Hs1 Hs2 Ht Hlt).
        + apply Pos2Nat.inj. exact Ht.
        + intros Hsi. change (sindep rc K (op_op u1) (op_op u2)) in Hsi. unfold sindep in Hsi.
          unfold SLM.uc in Hu. rewrite upres_ret_indep in Hu. congruence.
    Qed.

    (** The only use of validity: [wf_valid]. *)
    Lemma SX_wf_gen : Valid SX -> SL.WF rc K SX.
    Proof. intros Hv. exact (WF_of_core rc K SX SX_wf_core Hv). Qed.
  End ExecutionGen.

  (** ** Transport to the overlay, for any [P] *)

  Section TransportGen.
    Context (rc : bool) (K : SL.TLCats) (HK : SL.K_ok K = true).
    Local Abbreviation G := (E rc K).
    Context (VE : LTS G).
    Context (IT : list (@ITraceEvent G (F rc))) (ic : @IConfig G (F rc) VE).
    Context (Hinv : IInv VE (M rc K) IT ic) (Hq : ic_queue VE ic = []).
    Context (Wu : list (Op G)) (P : list (Op G) -> Prop).
    Context (HWu : rel_lin_witness BL.usel IT (semi_independent G) P Wu).
    Context (r0 : @InvRec G (F rc)) (u0 : Op G).

    Local Abbreviation HWu1 := (witness_unit BL.usel IT (semi_independent G) P Wu HWu).

    (** Reused from [SeqLockModule]. *)
    Local Abbreviation X := (SLM.SX rc K VE ic Wu).
    Local Abbreviation secs := (BL.secs VE ic).
    Local Abbreviation lpu := (SLM.lpu rc K VE ic Wu r0 u0).
    Local Abbreviation phi := (SLM.phi rc K VE ic).
    Local Abbreviation phi_rec := (SLM.phi_rec rc K VE IT ic Hinv).
    Local Abbreviation phi_all_ops := (SLM.phi_all_ops rc K VE IT ic Hinv Wu).
    Local Abbreviation phi_onto := (SLM.phi_onto rc K VE IT ic Hinv Wu).
    Local Abbreviation phi_inj := (SLM.phi_inj rc K VE IT ic Hinv).
    Local Abbreviation phi_blk := (SLM.phi_blk rc K VE IT ic Hinv Wu).
    Local Abbreviation phi_ovl := (SLM.phi_ovl rc K VE IT ic Hinv Wu r0).
    Local Abbreviation phi_sl := (SLM.phi_sl rc K VE IT ic Hinv Wu r0).
    Local Abbreviation phi_po := (SLM.phi_po rc K VE IT ic Hinv).
    Local Abbreviation secs_nodup := (SLM.secs_nodup rc K VE IT ic Hinv).

    Lemma X_wf_core : WF_core rc K X.
    Proof. exact (SX_wf_core rc K VE IT ic Hinv Hq Wu P HWu r0). Qed.

    (** *** Copied, SeqLockModule.v:1083-1105 *)

    Lemma lpu_src r : In r (ic_invs VE ic) ->
      In (lpu (ir_key r)) Wu /\
      exists m p, BL.usrc VE IT ic (lpu (ir_key r)) r (SLM.wsel rc K (ir_op r) (BL.ltr r)) m p.
    Proof.
      intros Hr. destruct (SLM.rec_window rc K VE IT ic Hinv r Hr) as (h & Hin & _).
      destruct (WLT.call_at_spec VE (M rc K) (SLM.keyE_dec rc K) (SLM.keyF_dec rc) WTJ.unit_dec
                  (fun _ => tt) (fun _ => P) IT ic Hinv Hq Wu HWu1 r0 u0 (SLM.wsel rc K) r _ _ _
                  Hr eq_refl Hin)
        as (m & p & Hs & Hu & _).
      split; [exact Hu|]. exists m, p. exact Hs.
    Qed.

    (** The position of the linearization call is [SeqLockCOH.lpq]. *)
    Lemma phi_lpq r : In r (ic_invs VE ic) ->
      SL.lpq X (phi (ir_key r)) = BL.pos (SLM.keyE_dec rc K) Wu (lpu (ir_key r)).
    Proof.
      intros Hr. destruct (lpu_src r Hr) as (Hu & m & p & Hs).
      destruct (phi_rec r Hr) as [Ephi Hn].
      destruct (SLM.ix_src rc K VE IT ic Hinv _ r _ m p _ Hs Hn) as (Ht & Hix & _).
      destruct (SLM.rec_window rc K VE IT ic Hinv r Hr) as (h & _ & Hlen).
      rewrite <- (idx_pos rc K VE IT ic Hinv Wu P HWu r0 _ Hu),
              (toEv_evt rc K VE IT ic Hinv Wu P HWu r0 _ Hu).
      rewrite Ht, Hix, Hlen.
      unfold SL.lpq, SL.lpc, SL.lpi_of. rewrite (phi_blk r Hr), Ephi. cbn [fst snd].
      rewrite (SLM.off_foff rc K VE IT ic Hinv). reflexivity.
    Qed.

    (** *** Without validity: [p_lp_inj], [p_window], [p_S1_ord], and the transport *)

    (** The field [p_lp_inj]: the first bullet of [SeqLockModule.positional]
        (SeqLockModule.v:1176-1181). *)
    Lemma lpu_inj s s' : In s secs -> In s' secs ->
      BL.pos (SLM.keyE_dec rc K) Wu (lpu s) = BL.pos (SLM.keyE_dec rc K) Wu (lpu s') -> s = s'.
    Proof.
      intros Hs Hs' Eq.
      destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->).
      destruct (BL.secs_record VE ic s' Hs') as (r' & Hr' & ->).
      f_equal. apply phi_inj; [exact Hr|exact Hr'|].
      apply (lp_inj_core rc K X X_wf_core); [apply phi_all_ops, Hr|apply phi_all_ops, Hr'|].
      rewrite (phi_lpq r Hr), (phi_lpq r' Hr'). exact Eq.
    Qed.

    (** The field [p_window]: both window ends are the linearization call
        (the second bullet of [SeqLockModule.positional]). *)
    Lemma lpu_window s : In s (WLT.secs VE ic) ->
      WLT.pos (SLM.keyE_dec rc K) Wu
        (WLT.lo VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) (SLM.wsel rc K) ic Wu r0 u0 s)
      <= WLT.pos (SLM.keyE_dec rc K) Wu (lpu s)
      <= WLT.pos (SLM.keyE_dec rc K) Wu
           (WLT.hi VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) (SLM.wsel rc K) ic Wu r0 u0 s).
    Proof. intros _. unfold SLM.lpu, WLT.lo, WLT.hi. lia. Qed.

    (** The field [p_S1_ord], for any [P] and without validity: the last
        bullet of [SeqLockModule.positional] (SeqLockModule.v:1205-1223),
        with [seqlock_S1_ord_core] / [z_S1_ord_core] on [X_wf_core]. *)
    Lemma lpu_S1_ord s s' : In s (WLT.secs VE ic) -> In s' (WLT.secs VE ic) ->
      WLT.comp VE (SLM.keyF_dec rc) fcomp ic r0 s = WLT.comp VE (SLM.keyF_dec rc) fcomp ic r0 s' ->
      WLT.po VE (SLM.keyF_dec rc) ic r0 s s' ->
      ~ semi_independent (F rc) (WLT.opF VE (SLM.keyF_dec rc) ic r0 s)
                                (WLT.opF VE (SLM.keyF_dec rc) ic r0 s') ->
      WLT.pos (SLM.keyE_dec rc K) Wu (lpu s) < WLT.pos (SLM.keyE_dec rc K) Wu (lpu s').
    Proof.
      intros Hs Hs' Hc Hpo _.
      destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->).
      destruct (BL.secs_record VE ic s' Hs') as (r' & Hr' & ->).
      destruct Hpo as [Ht Hpos].
      rewrite (BL.rec_of_spec VE (M rc K) (SLM.keyF_dec rc) IT ic Hinv r0 r Hr),
              (BL.rec_of_spec VE (M rc K) (SLM.keyF_dec rc) IT ic Hinv r0 r' Hr') in Hpos.
      change (BL.pos (SLM.keyE_dec rc K) Wu (lpu (ir_key r)) <
              BL.pos (SLM.keyE_dec rc K) Wu (lpu (ir_key r'))).
      rewrite <- (phi_lpq r Hr), <- (phi_lpq r' Hr').
      destruct (phi_po r r' Hr Hr' Ht Hpos) as [Hfst Hsnd].
      change (fcomp (ir_op (BL.rec_of VE (SLM.keyF_dec rc) ic r0 (ir_key r))) =
              fcomp (ir_op (BL.rec_of VE (SLM.keyF_dec rc) ic r0 (ir_key r')))) in Hc.
      pose proof (phi_sl r Hr) as S1. pose proof (phi_sl r' Hr') as S2. rewrite <- Hc in S2.
      destruct (fcomp (ir_op (BL.rec_of VE (SLM.keyF_dec rc) ic r0 (ir_key r)))).
      - apply (seqlock_S1_ord_core rc K X X_wf_core HK); [| |exact Hfst|exact Hsnd];
          unfold SL.sl_ops; apply filter_In; (split; [apply phi_all_ops; assumption|assumption]).
      - apply (z_S1_ord_core rc K X X_wf_core); [| |exact Hfst|exact Hsnd];
          unfold SL.z_ops; apply filter_In; (split; [apply phi_all_ops; assumption|]).
        + rewrite S1. reflexivity.
        + rewrite S2. reflexivity.
    Qed.

    (** The transport of the lp-sorted overlay calls along [phi], for any
        filters [fA] (overlay calls) and [fB] (operations of [X]) that agree
        along [phi] (SeqLockModule.v:1148-1169, generalized; from
        [WF_core]). *)
    Lemma S1_transport_gen (fA : CallKey (F rc) -> bool) (fB : nat * nat -> bool) :
      (forall s, In s secs -> fB (phi s) = fA s) ->
      map (SLM.ovev rc) (map (BL.ovl VE (SLM.keyF_dec rc) ic r0)
                           (WC.isort (fun s => BL.pos (SLM.keyE_dec rc K) Wu (lpu s)) (filter fA secs))) =
        map (SL.ovl X) (WC.isort (SL.lpq X) (filter fB (SL.all_ops X))).
    Proof.
      intros Hf.
      rewrite <- (SLM.isort_transport phi (fun s => BL.pos (SLM.keyE_dec rc K) Wu (lpu s)) (SL.lpq X)
                    fA fB secs (SL.all_ops X)).
      - rewrite !map_map. apply map_ext_in. intros s Hs.
        apply (Permutation_in _ (WC.isort_perm _ _)) in Hs. apply filter_In in Hs as [Hs _].
        destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). symmetry. exact (phi_ovl r Hr).
      - exact secs_nodup.
      - exact (SL.all_ops_nodup X (wfc_ths _ _ _ X_wf_core)).
      - intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). exact (phi_all_ops r Hr).
      - intros q Hq'. destruct (phi_onto q Hq') as (r & Hr & <-). exists (ir_key r). split; [|reflexivity].
        apply in_map, Hr.
      - intros s s' Hs Hs' Eq. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->).
        destruct (BL.secs_record VE ic s' Hs') as (r' & Hr' & ->). f_equal. exact (phi_inj r r' Hr Hr' Eq).
      - intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). exact (phi_lpq r Hr).
      - intros q q' Hq1 Hq2. exact (lp_inj_core rc K X X_wf_core q q' Hq1 Hq2).
      - exact Hf.
    Qed.

    Local Abbreviation St := (WLT.setting VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) SL.comp_dec fcomp
                         (SLM.nuFc rc) (SLM.catE K) fcat
                         (SLM.wsel rc K) (SLM.wsel rc K) IT ic Wu r0 u0 lpu).

    (** The per-component form (the statement of [SeqLockModule.S1_transport]). *)
    Lemma S1_transport (fB : nat * nat -> bool) (c : SL.CompT) :
      (forall s, In s secs -> fB (phi s) = WT.in_comp St c s) ->
      map (SLM.ovev rc) (map (BL.ovl VE (SLM.keyF_dec rc) ic r0)
                           (WC.isort (WT.lp St) (filter (WT.in_comp St c) secs))) =
        map (SL.ovl X) (WC.isort (SL.lpq X) (filter fB (SL.all_ops X))).
    Proof. intros Hf. exact (S1_transport_gen (WT.in_comp St c) fB Hf). Qed.

    (** The joint setting of [WindowLinkTableJ] for [lpu]. *)
    Local Abbreviation StJ := (WLTJ.settingJ VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) SL.comp_dec fcomp
                          (SLM.catE K) fcat (SLM.wsel rc K) (SLM.wsel rc K) IT ic Wu r0 u0 lpu).

    (** The unfiltered instance, on the list of [WindowLinkTableJ.p_S1J]. *)
    Lemma S1_transport_all :
      map (SLM.ovev rc) (map (WLT.ovl VE (SLM.keyF_dec rc) ic r0)
                           (WC.isort (WT.lp StJ) (WLT.secs VE ic))) =
        map (SL.ovl X) (WC.isort (SL.lpq X) (SL.all_ops X)).
    Proof.
      pose proof (S1_transport_gen (fun _ => true) (fun _ => true) (fun _ _ => eq_refl)) as H.
      rewrite (WTJ.filter_all_true (fun _ => true) secs (fun _ _ => eq_refl)),
              (WTJ.filter_all_true (fun _ => true) (SL.all_ops X) (fun _ _ => eq_refl)) in H.
      exact H.
    Qed.

    (** *** [WindowLinkTableJ.PositionalJ] for any [P], without validity *)

    (** Three of the four fields come from the lemmas above; only the joint
        specification obligation [p_S1J] remains. *)
    Lemma positionalJ_of_S1J (nuJ : list (Op (F rc)) -> Prop) :
      nuJ (map (WLT.ovl VE (SLM.keyF_dec rc) ic r0) (WC.isort (WT.lp StJ) (WLT.secs VE ic))) ->
      WLTJ.PositionalJ VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) SL.comp_dec fcomp nuJ (SLM.catE K) fcat
        (SLM.wsel rc K) (SLM.wsel rc K) IT ic Wu r0 u0 lpu.
    Proof.
      intros HS1J. constructor.
      - intros s s' Hs Hs' Eq. exact (lpu_inj s s' Hs Hs' Eq).
      - exact lpu_window.
      - exact HS1J.
      - exact lpu_S1_ord.
    Qed.

    (** The same, with [p_S1J] read on the operations of [X]: for a joint
        specification of the form [fun h => nuO (map (ovev rc) h)], the
        obligation is [nuO] of the lp-sorted overlay events of [X]. *)
    Lemma positionalJ_of_ovl (nuO : list SL.OvEv -> Prop) :
      nuO (map (SL.ovl X) (WC.isort (SL.lpq X) (SL.all_ops X))) ->
      WLTJ.PositionalJ VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) SL.comp_dec fcomp
        (fun h => nuO (map (SLM.ovev rc) h)) (SLM.catE K) fcat
        (SLM.wsel rc K) (SLM.wsel rc K) IT ic Wu r0 u0 lpu.
    Proof.
      intros H. apply positionalJ_of_S1J. cbv beta. rewrite S1_transport_all. exact H.
    Qed.

    (** *** Positional correctness (SeqLockModule.v:1171-1224); validity only for [p_S1] *)

    Lemma positional_gen (Hvalid : SLM.replay SL.init (map (SLM.uev rc K) Wu)) :
      WLT.Positional VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) SL.comp_dec fcomp (SLM.nuFc rc)
        (SLM.catE K) fcat (SLM.wsel rc K) (SLM.wsel rc K) IT ic Wu r0 u0 lpu.
    Proof.
      constructor.
      - intros s s' Hs Hs' Eq. exact (lpu_inj s s' Hs Hs' Eq).
      - exact lpu_window.
      - (* The only use of [Hvalid]: [seqlock_S1] and [z_S1] take [SeqLockCOH.WF]. *)
        assert (X_wf : SL.WF rc K X).
        { apply (SX_wf_gen rc K VE IT ic Hinv Hq Wu P HWu r0).
          exact (proj2 (SX_valid_iff rc K VE ic Wu) Hvalid). }
        intros c.
        assert (Hsl : forall s, In s secs -> SL.is_sl_op X (phi s) = WT.in_comp St SL.CSL s).
        { intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). rewrite (phi_sl r Hr).
          change (WT.in_comp St SL.CSL (ir_key r)) with
            (if SL.comp_dec (fcomp (ir_op (BL.rec_of VE (SLM.keyF_dec rc) ic r0 (ir_key r)))) SL.CSL
             then true else false).
          destruct (fcomp _); reflexivity. }
        assert (Hz : forall s, In s secs -> negb (SL.is_sl_op X (phi s)) = WT.in_comp St SL.CZ s).
        { intros s Hs. destruct (BL.secs_record VE ic s Hs) as (r & Hr & ->). rewrite (phi_sl r Hr).
          change (WT.in_comp St SL.CZ (ir_key r)) with
            (if SL.comp_dec (fcomp (ir_op (BL.rec_of VE (SLM.keyF_dec rc) ic r0 (ir_key r)))) SL.CZ
             then true else false).
          destruct (fcomp _); reflexivity. }
        destruct c.
        + change (SL.nu_sl (map (SLM.ovev rc) (map (BL.ovl VE (SLM.keyF_dec rc) ic r0)
                     (WC.isort (WT.lp St) (filter (WT.in_comp St SL.CSL) secs))))).
          rewrite (S1_transport (SL.is_sl_op X) SL.CSL Hsl).
          exact (SL.seqlock_S1 rc K X X_wf HK).
        + change (SL.nu_z (map (SLM.ovev rc) (map (BL.ovl VE (SLM.keyF_dec rc) ic r0)
                     (WC.isort (WT.lp St) (filter (WT.in_comp St SL.CZ) secs))))).
          rewrite (S1_transport (fun q => negb (SL.is_sl_op X q)) SL.CZ Hz).
          exact (SL.z_S1 rc K X X_wf).
      - exact lpu_S1_ord.
    Qed.
  End TransportGen.

  (** ** The register specification is an instance *)

  (** [SeqLockModule.SX_wf], from [SX_wf_gen]. *)
  Lemma SX_wf_of_gen rc K (VE : LTS (E rc K)) (IT : list (@ITraceEvent (E rc K) (F rc)))
      (ic : @IConfig (E rc K) (F rc) VE)
      (Hinv : IInv VE (M rc K) IT ic) (Hq : ic_queue VE ic = []) (Wu : list (Op (E rc K)))
      (HWu : rel_lin_witness BL.usel IT (semi_independent (E rc K))
               (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) Wu)
      (r0 : @InvRec (E rc K) (F rc)) :
    SL.WF rc K (SLM.SX rc K VE ic Wu).
  Proof.
    apply (SX_wf_gen rc K VE IT ic Hinv Hq Wu _ HWu r0).
    exact (proj2 (SX_valid_iff rc K VE ic Wu) (SLM.nuE_replay rc K Wu (proj1 HWu))).
  Qed.

  Example SX_wf_of_gen_statement :
    ltac:(let T := type of @SLM.SX_wf in exact T).
  Proof. exact @SX_wf_of_gen. Qed.

  (** [SeqLockModule.positional], from [positional_gen]. *)
  Lemma positional_of_gen rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K))
      (IT : list (@ITraceEvent (E rc K) (F rc))) (ic : @IConfig (E rc K) (F rc) VE)
      (Hinv : IInv VE (M rc K) IT ic) (Hq : ic_queue VE ic = []) (Wu : list (Op (E rc K)))
      (HWu : rel_lin_witness BL.usel IT (semi_independent (E rc K))
               (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) Wu)
      (r0 : @InvRec (E rc K) (F rc)) (u0 : Op (E rc K)) :
    WLT.Positional VE (SLM.keyE_dec rc K) (SLM.keyF_dec rc) SL.comp_dec fcomp (SLM.nuFc rc)
      (SLM.catE K) fcat (SLM.wsel rc K) (SLM.wsel rc K) IT ic Wu r0 u0 (SLM.lpu rc K VE ic Wu r0 u0).
  Proof.
    apply (positional_gen rc K HK VE IT ic Hinv Hq Wu _ HWu r0 u0).
    exact (SLM.nuE_replay rc K Wu (proj1 HWu)).
  Qed.

  Example positional_of_gen_statement :
    ltac:(let T := type of @SLM.positional in exact T).
  Proof. exact @positional_of_gen. Qed.

  (** ** The module theorem for every specification that implies validity *)

  Theorem seqlock_module_rel_lin_gen rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K))
      (P : list (Op (E rc K)) -> Prop)
      (HP : forall w, P w -> SLM.replay SL.init (map (SLM.uev rc K) w)) q0 T c :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K)) P ->
    rel_lin BL.over_sel T (semi_independent (F rc)) (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)).
  Proof.
    intros Hexec Hqc Hdc Hunder.
    refine (WLT.window_link_table VE (M rc K) (SLM.keyE_dec rc K) (SLM.keyF_dec rc) SL.comp_dec
              (fun _ => SL.CSL) fcomp
              (fun cp l => if SL.comp_dec cp SL.CSL then P l else True) (SLM.nuFc rc)
              (WT.dtable rc) (SLM.catE K) fcat (SLM.E_compat rc K) (SLM.F_cross rc) (SLM.nuF_nil rc)
              (SLM.wsel rc K) (SLM.wsel rc K) (SLM.window_bodies rc K) _ q0 T c Hexec Hqc Hdc _).
    - intros IT ic Wu r0 u0 Hinv Hq _ HWu.
      apply (WLTJ.rel_lin_witness_nu_mono _ _ _ _ _ _
               (fun w => proj1 (WLTJ.nuE_all_const SL.comp_dec SL.CSL P w))) in HWu.
      exists (SLM.lpu rc K VE ic Wu r0 u0).
      apply (positional_gen rc K HK VE IT ic Hinv Hq Wu P HWu r0 u0).
      exact (HP Wu (proj1 HWu)).
    - apply (WLTJ.rel_lin_nu_mono _ _ _ _ _
               (fun w => proj2 (WLTJ.nuE_all_const SL.comp_dec SL.CSL P w))).
      exact Hunder.
  Qed.

  (** [SeqLockModule.seqlock_module_rel_lin_K], from
      [seqlock_module_rel_lin_gen]. *)
  Theorem seqlock_module_rel_lin_K_of_gen rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    rel_lin BL.over_sel T (semi_independent (F rc)) (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)).
  Proof. exact (seqlock_module_rel_lin_gen rc K HK VE _ (SLM.nuE_replay rc K) q0 T c). Qed.

  Example seqlock_module_rel_lin_K_of_gen_statement :
    ltac:(let T := type of @SLM.seqlock_module_rel_lin_K in exact T).
  Proof. exact @seqlock_module_rel_lin_K_of_gen. Qed.

End SeqLockModuleGen.
