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
