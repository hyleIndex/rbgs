(** * Lock-protected registers through window composition

    [LockedRegisters] obtains its store-buffering result from
    [BracketedLink.bracketed_link].  Here the same module [M0] is checked
    against [BracketedWindow.lock_window_link], the instance of the
    general window theorem on Lock(O):

    - the premises on the lock operations are their modes (acquire
      [RFence], release [LFence]) and are checked here;
    - the overlay signature [F0] exports mode [RFence] for every
      operation (its linearization call is the acquire).  The previous
      declaration [Fence] does not satisfy mode inheritance
      ([fence_not_inheritable]);
    - [sb_forbidden_window] re-proves store buffering impossible from the
      window theorem, with the same proof as [LockedRegisters.sb_forbidden]
      after the call to the composition theorem;
    - [window_hypotheses_satisfiable]: an actual complete run meets the
      premises and gets the conclusion. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Sorting.Sorted.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedModuleFacts.
Require Import examples.Relaxed.BracketedComposition.
Require Import examples.Relaxed.BracketedLink.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.BracketedWindow.
Require Import examples.Relaxed.LockedRegisters.

Import ListNotations.

Module LockedRegistersWindow.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import LockedRegisters.

  Module WC := WindowComposition.WindowComposition.

  (** ** Premises of [lock_window_link] *)

  Lemma acq_mode a : is_acq a = true -> WC.acq_like (mode E0 a).
  Proof. destruct a; cbn; try discriminate. intros _ H. exact H. Qed.

  Lemma rel_mode r : is_rel r = true -> WC.rel_like (mode E0 r).
  Proof. destruct r; cbn; try discriminate. intros _ H. exact H. Qed.

  Lemma F0_modes o : mode F0 o ≤f RFence.
  Proof. exact I. Qed.

  Lemma F0_cross o o' : floc o <> floc o' -> WC.cross (mode F0 o) (mode F0 o') -> semi_independent F0 o o'.
  Proof. intros _ [H _]. exact H. Qed.

  Lemma nuF_nil c : nuFc c [].
  Proof. exact I. Qed.

  (** Exporting [Fence] instead is not justified: a release-like overlay
      mode must be carried by the first call of the window, here the
      acquire, whose mode is [RFence]. *)
  Lemma fence_not_inheritable : ~ (WC.rel_like Fence -> WC.rel_like RFence).
  Proof. intros H. apply (H (fun f => f)). exact I. Qed.

  (** ** The composition theorem for [M0] *)

  Theorem lock_regs_link (VE : RelaxedLTSSpec.LTS E0) q0 T c :
    module_execution_tagged VE M0 (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell F0 e = DeadCall) ->
    rel_lin BracketedLink.under_sel T (semi_independent E0)
      (BracketedLink.nuE_all (E := E0) BracketedComposition.loc_dec uloc nuEc) ->
    rel_lin BracketedLink.over_sel T (semi_independent F0)
      (BracketedLink.nuF_all (F := F0) BracketedComposition.loc_dec floc nuFc).
  Proof.
    exact (BracketedWindow.lock_window_link E0_well_formed VE M0 keyE0_dec keyF0_dec
             BracketedComposition.loc_dec uloc floc is_acq is_rel acq_mode rel_mode acq_not_rel
             M0_bracketed nuEc nuFc (fun _ _ H => proj1 H) local_correct F0_modes F0_cross nuF_nil q0 T c).
  Qed.

  (** ** Store buffering, from the window theorem *)

  Theorem sb_forbidden_window (VE : RelaxedLTSSpec.LTS E0) q0 T c (k1 k2 k3 k4 : CallKey F0) :
    fst k1 = fst k2 -> fst k3 = fst k4 -> NoDup [k1; k2; k3; k4] ->
    module_execution_tagged VE M0 (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell F0 e = DeadCall) ->
    rel_lin BracketedLink.under_sel T (semi_independent E0)
      (BracketedLink.nuE_all (E := E0) BracketedComposition.loc_dec uloc nuEc) ->
    (forall o, occurs BracketedLink.over_sel T o <->
       In o [put_op k1 LX; get_op k2 LY 0; put_op k3 LY; get_op k4 LX 0]) ->
    (exists i j, inv_at BracketedLink.over_sel T i k1 (FPut LX 1) /\
                 inv_at BracketedLink.over_sel T j k2 (FGet LY) /\ i < j) ->
    (exists i j, inv_at BracketedLink.over_sel T i k3 (FPut LY 1) /\
                 inv_at BracketedLink.over_sel T j k4 (FGet LX) /\ i < j) ->
    False.
  Proof.
    intros Ht12 Ht34 Hkeys Hexec Hq Hdead Hunder Hops (i1 & j1 & Hi1 & Hj1 & Hij1) (i2 & j2 & Hi2 & Hj2 & Hij2).
    destruct (lock_regs_link VE q0 T c Hexec Hq Hdead Hunder)
      as (W & Hnu & Hnd & Hocc & Hall & Hord).
    set (o1 := put_op k1 LX). set (o2 := get_op k2 LY 0).
    set (o3 := put_op k3 LY). set (o4 := get_op k4 LX 0).
    assert (HWsub : forall o, In o W -> In o [o1; o2; o3; o4]) by (intros o Ho; apply Hops, Hocc, Ho).
    assert (HinW : forall o, In o [o1; o2; o3; o4] -> In o W).
    { intros o Ho. pose proof (proj2 (Hops o) Ho) as [(i & Hi) _].
      destruct (Hall i (op_key o) (op_op o) Hi) as (o' & Ho' & Hk).
      assert (E : o' = o).
      { apply (nodup_map_inj_local op_key [o1; o2; o3; o4]); [exact Hkeys | apply HWsub, Ho' | exact Ho | exact Hk]. }
      rewrite <- E. exact Ho'. }
    assert (H1 : In o1 W) by (apply HinW; cbn; tauto).
    assert (H2 : In o2 W) by (apply HinW; cbn; tauto).
    assert (H3 : In o3 W) by (apply HinW; cbn; tauto).
    assert (H4 : In o4 W) by (apply HinW; cbn; tauto).
    assert (Hsort : StronglySorted (fun s s' => kidx W s < kidx W s') W).
    { apply BracketedLink.ss_of_before. intros x y Hxy. apply before_kidx; assumption. }
    (* program order, through the witness *)
    assert (P1 : kidx W o1 < kidx W o2).
    { apply before_kidx; [exact Hnd |]. apply Hord; [exact H1 | exact H2 |].
      right. split; [exact Ht12 |]. exists i1, j1. auto. }
    assert (P2 : kidx W o3 < kidx W o4).
    { apply before_kidx; [exact Hnd |]. apply Hord; [exact H3 | exact H4 |].
      right. split; [exact Ht34 |]. exists i2, j2. auto. }
    (* each location is a register *)
    assert (Hputs : forall l s v', In s (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc l W) ->
                      ovl_reg s = Put v' -> v' = 1).
    { intros l s v' Hs Ho. apply filter_In in Hs as [Hs _]. apply HWsub in Hs.
      destruct Hs as [<- | [<- | [<- | [<- | []]]]]; cbn in Ho; congruence. }
    assert (Hin : forall l s, In s W -> floc (op_op s) = l ->
                    In s (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc l W)).
    { intros l s Hs Hl. apply filter_In. split; [exact Hs |]. rewrite Hl.
      destruct (BracketedComposition.loc_dec l l); [reflexivity | contradiction]. }
    assert (RX : kidx W o4 < kidx W o1).
    { apply (BracketedComposition.read_old_before_write (kidx W) ovl_reg
               (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc LX W) o1 o4 1 0).
      - apply BracketedComposition.ss_filter, Hsort.
      - apply Hputs.
      - exact (Hnu LX).
      - apply Hin; [exact H1 | reflexivity].
      - apply Hin; [exact H4 | reflexivity].
      - reflexivity.
      - reflexivity.
      - discriminate. }
    assert (RY : kidx W o2 < kidx W o3).
    { apply (BracketedComposition.read_old_before_write (kidx W) ovl_reg
               (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc LY W) o3 o2 1 0).
      - apply BracketedComposition.ss_filter, Hsort.
      - apply Hputs.
      - exact (Hnu LY).
      - apply Hin; [exact H3 | reflexivity].
      - apply Hin; [exact H2 | reflexivity].
      - reflexivity.
      - reflexivity.
      - discriminate. }
    lia.
  Qed.

  (** ** Non-vacuity *)

  Theorem window_hypotheses_satisfiable : exists T c,
    module_execution_tagged VE0 M0 (initial_tagged_module VE0 tt) T c /\
    tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell F0 e = DeadCall) /\
    rel_lin BracketedLink.under_sel T (semi_independent E0)
      (BracketedLink.nuE_all (E := E0) BracketedComposition.loc_dec uloc nuEc) /\
    rel_lin BracketedLink.over_sel T (semi_independent F0)
      (BracketedLink.nuF_all (F := F0) BracketedComposition.loc_dec floc nuFc) /\
    inv_at BracketedLink.over_sel T 0 (t1, 0) (FPut LX 1).
  Proof.
    destruct put_execution as (c & Hx & Hq & Hd).
    exists T_put, c. split; [exact Hx |]. split; [exact Hq |]. split; [exact Hd |].
    split; [exact put_underlay_rel_lin |].
    split; [exact (lock_regs_link VE0 tt T_put c Hx Hq Hd put_underlay_rel_lin) |].
    eexists. split; reflexivity.
  Qed.

End LockedRegistersWindow.
