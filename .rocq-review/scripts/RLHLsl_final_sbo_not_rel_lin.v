From Stdlib Require Import List Arith.PeanoNat micromega.Lia.
Require Import models.LinCCAL models.RelaxedSignature models.simlin.RelaxedLTS models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareSpec models.view.PrefixView.
Require Import examples.Relaxed.RelaxedHoareSL2Prog examples.Relaxed.RelaxedHoareSL2Exec.
Import ListNotations. Import LinCCALBase. Import RelaxedSig. Import RelaxedLTSSpec. Import RelaxedHoareSL2Prog. Import RelaxedHoareSL2Exec.
Ltac in_tac := cbn; solve [repeat (first [left; reflexivity | right])].
Ltac nodup_keys := cbn; repeat constructor; cbn; let H := fresh in intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
Ltac inv_here := eexists; split; reflexivity.
Definition sbo (si : FOp -> FOp -> Prop) (t1 t2 : tid) : list (ThreadEvent (F2 si)) :=
  [Build_ThreadEvent t1 (@InvEv (F2 si) 0 (fW 1 1 1)); Build_ThreadEvent t1 (@InvEv (F2 si) 1 (fR 1)); Build_ThreadEvent t1 (@InvEv (F2 si) 2 (fR 2));
   Build_ThreadEvent t2 (@InvEv (F2 si) 3 (fW 2 1 1)); Build_ThreadEvent t2 (@InvEv (F2 si) 4 (fR 2)); Build_ThreadEvent t2 (@InvEv (F2 si) 5 (fR 1));
   Build_ThreadEvent t1 (@ResEv (F2 si) 1 (fR 1) (1, 1)); Build_ThreadEvent t1 (@ResEv (F2 si) 2 (fR 2) (0, 0));
   Build_ThreadEvent t2 (@ResEv (F2 si) 4 (fR 2) (1, 1)); Build_ThreadEvent t2 (@ResEv (F2 si) 5 (fR 1) (0, 0));
   Build_ThreadEvent t1 (@ResEv (F2 si) 0 (fW 1 1 1) tt); Build_ThreadEvent t2 (@ResEv (F2 si) 3 (fW 2 1 1) tt)].
Definition oWi (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 0) (fW 1 1 1) tt.
Definition oRi (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 1) (fR 1) (1, 1).
Definition oRj (si : FOp -> FOp -> Prop) (t1 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t1, 2) (fR 2) (0, 0).
Definition oWj (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 3) (fW 2 1 1) tt.
Definition oRj' (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 4) (fR 2) (1, 1).
Definition oRi' (si : FOp -> FOp -> Prop) (t2 : tid) := @RelaxedTraceLin.Build_Op (F2 si) (t2, 5) (fR 1) (0, 0).
Lemma sbo_sub si t1 t2 : forall e, In e (sbo si t1 t2) -> In e (evs_of [oWi si t1; oRi si t1; oRj si t1; oWj si t2; oRj' si t2; oRi' si t2]).
Proof. intros e He. cbn in He. repeat (destruct He as [<- | He]; [in_tac |]). destruct He. Qed.
Theorem sbo_not_rel_lin si indep t1 t2 : (forall o o', indep o o' -> slRA o o') ->
  ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (F2 si)) (sbo si t1 t2) indep (RelaxedHoareSpec.seq_legal (F := F2 si) δF A0).
Proof.
  intros Hsub Hrl.
  destruct (rel_lin_ops (sbo si t1 t2) indep _ [oWi si t1; oRi si t1; oRj si t1; oWj si t2; oRj' si t2; oRi' si t2] ltac:(nodup_keys) (sbo_sub si t1 t2) Hrl) as (W & (A' & Hrun) & Hnd & HW & Hin & Hord).
  assert (H0 : In (oWi si t1) W) by (apply (Hin _ 0); [in_tac | inv_here]).
  assert (H1 : In (oRi si t1) W) by (apply (Hin _ 1); [in_tac | inv_here]).
  assert (H2 : In (oRj si t1) W) by (apply (Hin _ 2); [in_tac | inv_here]).
  assert (H3 : In (oWj si t2) W) by (apply (Hin _ 3); [in_tac | inv_here]).
  assert (H4 : In (oRj' si t2) W) by (apply (Hin _ 4); [in_tac | inv_here]).
  assert (H5 : In (oRi' si t2) W) by (apply (Hin _ 5); [in_tac | inv_here]).
  assert (B01 : RelaxedTraceLin.before W (oWi si t1) (oRi si t1)).
  { apply Hord; [exact H0 | exact H1 |]. right. split; [reflexivity |]. exists 0, 1. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact (H eq_refl). }
  assert (B12 : RelaxedTraceLin.before W (oRi si t1) (oRj si t1)).
  { apply Hord; [exact H1 | exact H2 |]. right. split; [reflexivity |]. exists 1, 2. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact H. }
  assert (B34 : RelaxedTraceLin.before W (oWj si t2) (oRj' si t2)).
  { apply Hord; [exact H3 | exact H4 |]. right. split; [reflexivity |]. exists 3, 4. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact (H eq_refl). }
  assert (B45 : RelaxedTraceLin.before W (oRj' si t2) (oRi' si t2)).
  { apply Hord; [exact H4 | exact H5 |]. right. split; [reflexivity |]. exists 4, 5. split; [inv_here |]. split; [inv_here |]. split; [lia |]. intros H; apply Hsub in H; exact H. }
  destruct (In_nth_error _ _ H0) as (i0 & E0). destruct (In_nth_error _ _ H1) as (i1 & E1).
  destruct (In_nth_error _ _ H2) as (i2 & E2). destruct (In_nth_error _ _ H3) as (i3 & E3).
  destruct (In_nth_error _ _ H4) as (i4 & E4). destruct (In_nth_error _ _ H5) as (i5 & E5).
  pose proof (before_idx W _ _ _ _ Hnd B01 E0 E1). pose proof (before_idx W _ _ _ _ Hnd B12 E1 E2).
  pose proof (before_idx W _ _ _ _ Hnd B34 E3 E4). pose proof (before_idx W _ _ _ _ Hnd B45 E4 E5).
  assert (i2 < i3).
  { apply (leg_read_before A0 W A' i2 i3 (oRj si t1) (oWj si t2) 2 1 1 Hrun E2 E3 eq_refl eq_refl).
    intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hop; try discriminate Hop; injection Hop; intros; subst; cbn; congruence. }
  assert (i5 < i0).
  { apply (leg_read_before A0 W A' i5 i0 (oRi' si t2) (oWi si t1) 1 1 1 Hrun E5 E0 eq_refl eq_refl).
    intros o ux uy Ho Hop. destruct (HW o Ho) as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; cbn in Hop; try discriminate Hop; injection Hop; intros; subst; cbn; congruence. }
  lia.
Qed.
Print Assumptions sbo_not_rel_lin.
