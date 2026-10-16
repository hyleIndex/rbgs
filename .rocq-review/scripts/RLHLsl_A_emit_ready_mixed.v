Require Import Stdlib.Lists.List Stdlib.PArith.PArith.
Require Import models.EffectSignatures models.RelaxedSignature models.LinCCAL models.simlin.RelaxedLTS models.simlin.RelaxedLang models.simlin.RelaxedSemantics models.simlin.RelaxedModuleSemantics models.simlin.RelaxedPossibility models.simlin.RelaxedHoareBase models.simlin.RelaxedHoareCompLinSpec models.simlin.RelaxedHoareRun.
Import ListNotations LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedModuleSemantics RelaxedPossibility RelaxedHoareBase RelaxedHoareRun.
Section S. Context {E F : RelaxedSig.t}.
Theorem emit_ready_mixed (P : LinPool F) (γ g1 g2 : Ghost E F) t h o (ev : ThreadEvent E) :
  lin_pool_well_formed P -> lin_lookup (t, h) (ls_inv o) P -> GAge P γ ->
  (forall k1 o1, fst k1 = t -> key_older (lin_domain P) k1 (t, h) -> lin_lookup k1 (ls_inv o1) P ->
     semi_independent F o1 o \/ exists e, In e γ /\ se_owner e = k1 /\ inv_blocks (se_event e) ev) ->
  γ = g1 ++ Build_ScheduledEvent (t, h) ev :: g2 -> Forall (fun e => ~ inv_blocks (se_event e) ev) g1 ->
  exists P', lin_invoke_update t h o P P' /\ lin_pool_well_formed P'.
Proof.
  intros Hwf Hl Hage Hblk Hγ Hnb. destruct (in_split _ _ Hl) as (pre & older & HP).
  assert (Hwf0 := Hwf). unfold lin_pool_well_formed, lin_domain in Hwf0. rewrite HP, map_app in Hwf0. cbn in Hwf0.
  pose proof (NoDup_remove_2 _ _ _ Hwf0) as Hnin. rewrite lin_key_make_lin_entry in Hnin.
  assert (Hpre : forall y, In y pre -> lin_key y <> (t, h)).
  { intros y Hy Hk. apply Hnin. apply in_or_app. left. rewrite <- Hk. apply in_map. exact Hy. }
  assert (Hready : invocation_ready t o older).
  { unfold invocation_ready. apply Forall_forall. intros e He. unfold older_entry_allows_invocation.
    destruct (Pos.eqb_spec (lin_tid F e) t) as [Ht | Ht]; [right | left; exact Ht].
    destruct (lin_state F e) as [o1 | o1 | o1 r1] eqn:Hs; [| exact Logic.I | exact Logic.I].
    assert (He' : e = make_lin_entry (lin_key e) (ls_inv o1)) by (destruct e; cbn in *; subst; reflexivity).
    assert (Hold : key_older (lin_domain P) (lin_key e) (t, h)).
    { unfold key_older, lin_domain. rewrite HP, map_app. cbn [map]. rewrite lin_key_make_lin_entry.
      apply subseq_pair_split. apply in_map. exact He. }
    assert (Hle : lin_lookup (lin_key e) (ls_inv o1) P).
    { unfold lin_lookup. rewrite <- He', HP. apply in_or_app. right. right. exact He. }
    destruct (Hblk (lin_key e) o1 Ht Hold Hle) as [Hsi | (e' & He'γ & Hown & Hb)]; [exact Hsi | exfalso].
    assert (Hin1 : In e' g1).
    { apply (gage_before P γ g1 g2 (Build_ScheduledEvent (t, h) ev) e' Hage Hγ He'γ). rewrite Hown. exact Hold. }
    rewrite Forall_forall in Hnb. exact (Hnb e' Hin1 Hb). }
  assert (Hu : lin_invoke_update t h o P (pre ++ make_lin_entry (t, h) (ls_lini o) :: older)).
  { rewrite HP. apply RelaxedHoareCompLinSpec.liu_app; [exact Hpre |]. apply lin_invoke_update_here. exact Hready. }
  exists (pre ++ make_lin_entry (t, h) (ls_lini o) :: older). split; [exact Hu |].
  eapply lin_invoke_update_well_formed; [exact Hu | exact Hwf].
Qed.
End S.

Print Assumptions emit_ready_mixed.