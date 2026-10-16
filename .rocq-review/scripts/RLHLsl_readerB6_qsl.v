From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL.
Require Import models.simlin.RelaxedLTS models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareDag models.simlin.RelaxedHoareSpec models.simlin.RelaxedHoareCompLinSpec models.simlin.RelaxedHoareRun.
Require Import examples.Relaxed.RelaxedHoareSL2Prog examples.Relaxed.RelaxedHoareSL2Inv.
Import ListNotations LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedModuleSemantics RelaxedPossibility RelaxedHoareCompLinSpec RelaxedHoareBase RelaxedHoareDag RelaxedHoareRun RelaxedHoareSL2Prog RelaxedHoareSL2Inv.
Lemma owns_rmb_not_qsl rc si tw k i r s :
  Isl rc si tw s -> Owns rc si k isRmb (ps_ghost s) -> ~ Qsl rc si k (fR i) r s.
Proof.
  intros (A & Pf & P & Hp & _ & HC) Hown (A' & Pf' & P' & Hp' & Hq).
  rewrite Hp in Hp'. injection Hp' as <- <- <-.
  destruct Hq as [Hl | [Hl _]];
    pose proof (ic_coup _ _ _ _ _ _ _ _ HC _ Hl) as Hc;
    unfold Coup in Hc; rewrite lin_key_make_lin_entry in Hc; cbn in Hc;
    apply Hc in Hown; discriminate Hown.
Qed.
Module Mismatch.
  Definition rc := true.
  Definition si : FOp -> FOp -> Prop := fun _ _ => False.
  Definition tw : nat -> tid := fun _ => 2%positive.
  Definition t : tid := 1%positive.
  Definition k : CallKey (F2 si) := (t, 0).
  Definition hs1 : nat * nat * nat * nat * nat * nat := (0, 1, 2, 3, 4, 5).
  Definition hs2 : nat * nat * nat * nat * nat * nat := (6, 7, 8, 9, 10, 11).
  Definition evs := flat_map (rd_iter rc t 0) [hs1; hs2].
  Definition P : LinPool (F2 si) := [make_lin_entry k (@ls_inv (F2 si) (fR 0))].
  Definition VE := EIhl (E := E_S rc) δS.
  Definition VF := RelaxedHoareSpec.EI (F := F2 si) δF.
  Definition s0 : PState VE VF :=
    (((regs0, []), []), @PossOk (F2 si) VF (A0, []) P, map (Build_ScheduledEvent k) evs).
  Lemma pinit0 : PostInvoke (Isl rc si tw) k (fR 0) (Osl rc tw t (fR 0) 0) s0.
  Proof.
    exists (@PossOk (F2 si) VF (A0, []) []), [], evs. split; [exact (isl_init rc si tw) |].
    split; [constructor; constructor; intros [] |].
    split; [reflexivity |]. split.
    - cbn. exists [hs1; hs2]. split; [discriminate |]. split; [| reflexivity].
      cbn. repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    - cbn. repeat constructor.
  Qed.
  Lemma islc0 : IslC rc si tw regs0 A0 [] P (map (Build_ScheduledEvent k) evs).
  Proof.
    constructor.
    - unfold lin_pool_well_formed, lin_domain. cbn. constructor; [intros [] | constructor].
    - split.
      + intros e He. apply in_map_iff in He as (x & <- & _). cbn. left. reflexivity.
      + intros i j e1 e2 H1 H2 Ho. exfalso. cbn in Ho. unfold key_older in Ho.
        inversion Ho; subst; repeat match goal with H : subseq _ [] |- _ => inversion H; clear H end;
        repeat match goal with H : subseq _ (_ :: _) |- _ => inversion H; clear H; subst end.
    - cbn. repeat constructor.
    - intros o [].
    - constructor.
    - intros e [<- | []]. cbn. split; [intros _ | reflexivity].
      exists (Build_ScheduledEvent k (IE rc t 1 sRmb)). split; [cbn; tauto |]. split; reflexivity.
    - intros e i vx vy [<- | []] H. discriminate.
    - intros i k1 k2 (vx & vy & ls & Hl & Hop). exfalso.
      destruct Hl as [Hl | []]. unfold make_lin_entry in Hl. injection Hl as _ _ Hls. subst ls. discriminate.
    - intros i _. reflexivity.
    - intros i He. discriminate.
    - cbn. repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
  Qed.
  Lemma isl0 : Isl rc si tw s0.
  Proof. exists A0, [], P. split; [reflexivity |]. split; [intros x [] | exact islc0]. Qed.
  Lemma owns_after_iter1 : Owns rc si k isRmb (map (Build_ScheduledEvent k) (rd_iter rc t 0 hs2)).
  Proof. exists (Build_ScheduledEvent k (IE rc t 7 sRmb)). split; [cbn; tauto |]. split; reflexivity. Qed.
  Lemma rok00 : rok 0 0 = true. Proof. reflexivity. Qed.
End Mismatch.
Print Assumptions owns_rmb_not_qsl.
Print Assumptions Mismatch.pinit0.
Print Assumptions Mismatch.isl0.
Print Assumptions Mismatch.owns_after_iter1.
