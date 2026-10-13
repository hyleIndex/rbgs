(** * T1: one shared clock refines per-object clocks

    The view of a tensor product [P1 ⊗ P2] is lifted with one clock
    shared by both objects.  Its same-thread order inside each component
    is that of the component, and across components it is given by two
    arbitrary relations [x12] and [x21] (for instance, those induced by
    fence modes).  Theorem [shared_sim_by_tensor] shows that this lifted
    LTS is simulated by the tensor of the two separately lifted LTSs.
    Each component then has its own clock, and the cross-component
    constraints are dropped.

    Consequently ([cal_tensor_to_shared]), an implementation verified
    against the tensor of per-object view specifications is also correct
    against the shared-clock view of the tensor.  Only this direction is
    needed for an underlay.  [EBStackTSOImpl.components_correct] in
    [examples/View/EBStackTSO.v] uses it to run the EB stack components on
    one shared clock.  This replaced a hand-written bridge of about 980
    lines to CSL-Lin's global view [VComboTSO]. *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulation.
Require Import models.simlin.AtomicLTS.
Require Import models.view.UnderlayRefinement.
Require Import models.view.ViewLift.
Import ListNotations.

Module ViewLiftTensor.
  Import Reg LinCCALBase LTSSpec AtomicLTS ViewLift.

  Section Tensor.
    Context {E1 E2 : Op.t}.
    Context (P1 : @Params E1) (P2 : @Params E2).
    Context (x12 : Sig.op E1 -> Sig.op E2 -> bool) (x21 : Sig.op E2 -> Sig.op E1 -> bool).

    Abbreviation E := (Sig.Plus.omap E1 E2).

    Definition tspec (s : vl_state P1 * vl_state P2) (t : tid) (m : Sig.op E) :
        Sig.ar m -> vl_state P1 * vl_state P2 -> Prop :=
      match m as m0 return @Sig.ar (Sig.Plus.omap E1 E2) m0 -> vl_state P1 * vl_state P2 -> Prop with
      | inl m1 => fun r s' => vl_spec P1 (fst s) t m1 r (fst s') /\ snd s' = snd s
      | inr m2 => fun r s' => vl_spec P2 (snd s) t m2 r (snd s') /\ fst s' = fst s
      end.

    Definition terr (t : tid) (m : Sig.op E) (s : vl_state P1 * vl_state P2) : Prop :=
      match m with
      | inl m1 => vl_err P1 t m1 (fst s)
      | inr m2 => vl_err P2 t m2 (snd s)
      end.

    Definition tretro (m : Sig.op E) : bool :=
      match m with inl m1 => vl_retro P1 m1 | inr m2 => vl_retro P2 m2 end.

    Definition tsync (m : Sig.op E) : bool :=
      match m with inl m1 => vl_sync P1 m1 | inr m2 => vl_sync P2 m2 end.

    Definition tdep (o m : Sig.op E) : bool :=
      match o, m with
      | inl a, inl b => vl_dep P1 a b
      | inr a, inr b => vl_dep P2 a b
      | inl a, inr b => x12 a b
      | inr a, inl b => x21 a b
      end.

    Definition PT : @Params E := {|
      vl_state := vl_state P1 * vl_state P2;
      vl_spec := tspec;
      vl_err := terr;
      vl_retro := tretro;
      vl_dep := tdep;
      vl_sync := tsync;
    |}.

    (** ** Collapse conditions are preserved by the shared-clock product *)

    Lemma PT_sync :
      (forall m, vl_retro P1 m = false -> vl_sync P1 m = true) ->
      (forall m, vl_retro P2 m = false -> vl_sync P2 m = true) ->
      forall m, vl_retro PT m = false -> vl_sync PT m = true.
    Proof. intros H1 H2 [m | m]; simpl; auto. Qed.

    Lemma PT_pres :
      (forall s t m r s', vl_retro P1 m = true -> vl_spec P1 s t m r s' -> s' = s) ->
      (forall s t m r s', vl_retro P2 m = true -> vl_spec P2 s t m r s' -> s' = s) ->
      forall s t m r s', vl_retro PT m = true -> vl_spec PT s t m r s' -> s' = s.
    Proof.
      intros H1 H2 [a b] t [m | m] r [a' b'] Hr [Hs He]; simpl in *; subst.
      - rewrite (H1 _ _ _ _ _ Hr Hs). reflexivity.
      - rewrite (H2 _ _ _ _ _ Hr Hs). reflexivity.
    Qed.

    (** ** The simulation relation *)

    Record Proj (s : VState PT) (s1 : VState P1) (s2 : VState P2) : Prop := {
      pj_inv : Inv PT s;
      pj_inv1 : Inv P1 s1;
      pj_inv2 : Inv P2 s2;
      pj_tl1 : forall h, vs_tl P1 s1 h = fst (vs_tl PT s h);
      pj_tl2 : forall h, vs_tl P2 s2 h = snd (vs_tl PT s h);
      pj_past1 : forall t o h, In (o, h) (vs_past P1 s1 t) -> In (inl o, h) (vs_past PT s t);
      pj_past2 : forall t o h, In (o, h) (vs_past P2 s2 t) -> In (inr o, h) (vs_past PT s t);
      pj_floor1 : Pos.le (vs_floor P1 s1) (vs_floor PT s);
      pj_floor2 : Pos.le (vs_floor P2 s2) (vs_floor PT s);
      pj_hor1 : Pos.le (vs_hor P1 s1) (vs_hor PT s);
      pj_hor2 : Pos.le (vs_hor P2 s2) (vs_hor PT s);
    }.

    Definition Rel (x : State (VL PT)) (y : State (tens_lts (VL P1) (VL P2))) : Prop :=
      match x, y with
      | Idle s, (Idle s1, Idle s2) => Proj s s1 s2
      | Pending s t (inl m), (Pending s1 t1 m1, Idle s2) => Proj s s1 s2 /\ t1 = t /\ m1 = m
      | Pending s t (inr m), (Idle s1, Pending s2 t2 m2) => Proj s s1 s2 /\ t2 = t /\ m2 = m
      | _, _ => False
      end.

    Lemma Proj_init s01 s02 :
      Proj (vinit PT (s01, s02)) (vinit P1 s01) (vinit P2 s02).
    Proof.
      constructor; simpl; try apply Inv_init; try reflexivity; try (intros; contradiction);
        apply Pos.le_refl.
    Qed.

    Lemma Rel_init s01 s02 :
      Rel (Idle (vinit PT (s01, s02))) (Idle (vinit P1 s01), Idle (vinit P2 s02)).
    Proof. apply Proj_init. Qed.

    (** Current states project. *)
    Lemma cur_proj1 s s1 s2 : Proj s s1 s2 -> cur P1 s1 = fst (cur PT s).
    Proof.
      intros HP. unfold cur. rewrite <- (inv_const _ _ (pj_inv1 _ _ _ HP) _ (pj_hor1 _ _ _ HP)).
      apply (pj_tl1 _ _ _ HP).
    Qed.

    Lemma cur_proj2 s s1 s2 : Proj s s1 s2 -> cur P2 s2 = snd (cur PT s).
    Proof.
      intros HP. unfold cur. rewrite <- (inv_const _ _ (pj_inv2 _ _ _ HP) _ (pj_hor2 _ _ _ HP)).
      apply (pj_tl2 _ _ _ HP).
    Qed.

    Lemma In_push {Op : Type} (past : tid -> list (Op * Time)) t m h t' o h' :
      In (o, h') (past t') ->
      In (o, h') (if Pos.eqb t t' then (m, h) :: past t' else past t').
    Proof. intros H. destruct (Pos.eqb t t'); [right|]; exact H. Qed.

    Lemma In_push_inv {Op : Type} (past : tid -> list (Op * Time)) t m h t' o h' :
      In (o, h') (if Pos.eqb t t' then (m, h) :: past t' else past t') ->
      (t = t' /\ o = m /\ h' = h) \/ In (o, h') (past t').
    Proof.
      destruct (Pos.eqb t t') eqn:Heqtt; [|auto].
      apply Pos.eqb_eq in Heqtt. intros [H | H]; [left | right; exact H].
      inversion H; subst; auto.
    Qed.


    Ltac res_inv H :=
      let Ht := fresh "Ht" in
      let Hr := fresh "Hr" in
      pose proof (f_equal te_tid H) as Ht; simpl in Ht;
      pose proof (f_equal te_ev H) as Hr; simpl in Hr;
      match type of Hr with
      | ResEv ?m1 _ = ResEv ?m2 _ =>
          let Hm := fresh "Hm" in
          assert (Hm : m1 = m2) by (injection Hr; auto); subst m1
      end;
      apply LTSSpec.ResEvInversion in Hr;
      match type of Ht with ?a = _ => subst a end;
      match type of Hr with ?a = _ => subst a end.

    Lemma le_lt_le a b c : Pos.le a b -> Pos.lt b c -> Pos.le a c.
    Proof. intros H1 H2. apply Pos.lt_le_incl. eapply Pos.le_lt_trans; eassumption. Qed.

    (** A response of component 1 in the shared view is a response of the
        lifted component 1, and preserves the projection. *)
    Lemma resp1 t (m : Sig.op E1) (r : Sig.ar m) (s s' : VState PT) s1 s2 :
      Proj s s1 s2 ->
      VStep PT (Build_ThreadEvent t (@ResEv E (inl m) r)) s s' ->
      exists s1', VStep P1 (Build_ThreadEvent t (ResEv m r)) s1 s1' /\ Proj s' s1' s2.
    Proof.
      intros HP Hs. remember (Build_ThreadEvent t (@ResEv E (inl m) r)) as ev eqn:Hev.
      pose proof (VStep_Inv PT _ _ _ Hs (pj_inv _ _ _ HP)) as HI'.
      destruct Hs as [t0 m0 s0 e He | t0 m0 r0 h s0 s0' e He Hretro Hfloor Hdep Hspec Hupd
                     | t0 m0 r0 h st s0 s0' e He Hretro Hhor Hdep Hspec Hupd]; rewrite He in Hev.
      - discriminate.
      - res_inv Hev. subst s0'. simpl in Hretro, Hspec. destruct Hspec as [Hspec1 _].
        exists (upd_retro P1 s1 t m h). split.
        + eapply vstep_retro; [reflexivity | exact Hretro | | | | reflexivity].
          * eapply Pos.le_lt_trans; [exact (pj_floor1 _ _ _ HP) | exact Hfloor].
          * intros o h' Hin Hd. exact (Hdep (inl o) h' (pj_past1 _ _ _ HP _ _ _ Hin) Hd).
          * rewrite (pj_tl1 _ _ _ HP). exact Hspec1.
        + constructor; simpl.
          * exact HI'.
          * eapply (VStep_Inv P1). 2: exact (pj_inv1 _ _ _ HP).
            eapply vstep_retro; [reflexivity | exact Hretro | | | | reflexivity].
            -- eapply Pos.le_lt_trans; [exact (pj_floor1 _ _ _ HP) | exact Hfloor].
            -- intros o h' Hin Hd. exact (Hdep (inl o) h' (pj_past1 _ _ _ HP _ _ _ Hin) Hd).
            -- rewrite (pj_tl1 _ _ _ HP). exact Hspec1.
          * exact (pj_inv2 _ _ _ HP).
          * exact (pj_tl1 _ _ _ HP).
          * exact (pj_tl2 _ _ _ HP).
          * intros t' o h' Hin. unfold push_past in *.
            apply In_push_inv in Hin as [(-> & -> & ->) | Hin].
            -- rewrite Pos.eqb_refl. left. reflexivity.
            -- apply In_push. exact (pj_past1 _ _ _ HP _ _ _ Hin).
          * intros t' o h' Hin. unfold push_past. apply In_push. exact (pj_past2 _ _ _ HP _ _ _ Hin).
          * pose proof (pj_floor1 _ _ _ HP). destruct (vl_sync P1 m); [|assumption].
            apply Pos.max_le_compat; [assumption | apply Pos.le_refl].
          * pose proof (pj_floor2 _ _ _ HP). destruct (vl_sync P1 m); [|assumption].
            eapply Pos.le_trans; [eassumption | apply Pos.le_max_l].
          * apply Pos.max_le_compat; [exact (pj_hor1 _ _ _ HP) | apply Pos.le_refl].
          * eapply Pos.le_trans; [exact (pj_hor2 _ _ _ HP) | apply Pos.le_max_l].
      - res_inv Hev. subst s0'. simpl in Hretro, Hspec. destruct Hspec as [Hspec1 Hsnd].
        assert (Hstep1 : VStep P1 (Build_ThreadEvent t (ResEv m r)) s1 (upd_app P1 s1 t m h (fst st))).
        { eapply vstep_app; [reflexivity | exact Hretro | | | | reflexivity].
          - eapply Pos.le_lt_trans; [exact (pj_hor1 _ _ _ HP) | exact Hhor].
          - intros o h' Hin Hd. exact (Hdep (inl o) h' (pj_past1 _ _ _ HP _ _ _ Hin) Hd).
          - rewrite (pj_tl1 _ _ _ HP). exact Hspec1. }
        exists (upd_app P1 s1 t m h (fst st)). split; [exact Hstep1|].
        constructor; simpl.
        + exact HI'.
        + exact (VStep_Inv P1 _ _ _ Hstep1 (pj_inv1 _ _ _ HP)).
        + exact (pj_inv2 _ _ _ HP).
        + intros h'. unfold tl_write. destruct (Pos.leb h h'); [reflexivity | apply (pj_tl1 _ _ _ HP)].
        + intros h'. unfold tl_write. destruct (Pos.leb h h') eqn:Hle; [|apply (pj_tl2 _ _ _ HP)].
          apply Pos.leb_le in Hle. rewrite Hsnd, (pj_tl2 _ _ _ HP).
          pose proof (pj_inv _ _ _ HP) as HI.
          rewrite (inv_const _ _ HI h') by (eapply le_lt_le; [apply Pos.le_refl | exact (Pos.lt_le_trans _ _ _ Hhor Hle)]).
          rewrite (inv_const _ _ HI h) by (apply Pos.lt_le_incl; exact Hhor).
          reflexivity.
        + intros t' o h' Hin. unfold push_past in *.
          apply In_push_inv in Hin as [(-> & -> & ->) | Hin].
          * rewrite Pos.eqb_refl. left. reflexivity.
          * apply In_push. exact (pj_past1 _ _ _ HP _ _ _ Hin).
        + intros t' o h' Hin. unfold push_past. apply In_push. exact (pj_past2 _ _ _ HP _ _ _ Hin).
        + pose proof (pj_floor1 _ _ _ HP). destruct (vl_sync P1 m); [apply Pos.le_refl | assumption].
        + pose proof (pj_floor2 _ _ _ HP). pose proof (inv_floor _ _ (pj_inv _ _ _ HP)).
          destruct (vl_sync P1 m); [|assumption].
          eapply le_lt_le; [eapply Pos.le_trans; eassumption | exact Hhor].
        + apply Pos.le_refl.
        + eapply le_lt_le; [exact (pj_hor2 _ _ _ HP) | exact Hhor].
    Qed.

    Lemma resp2 t (m : Sig.op E2) (r : Sig.ar m) (s s' : VState PT) s1 s2 :
      Proj s s1 s2 ->
      VStep PT (Build_ThreadEvent t (@ResEv E (inr m) r)) s s' ->
      exists s2', VStep P2 (Build_ThreadEvent t (ResEv m r)) s2 s2' /\ Proj s' s1 s2'.
    Proof.
      intros HP Hs. remember (Build_ThreadEvent t (@ResEv E (inr m) r)) as ev eqn:Hev.
      pose proof (VStep_Inv PT _ _ _ Hs (pj_inv _ _ _ HP)) as HI'.
      destruct Hs as [t0 m0 s0 e He | t0 m0 r0 h s0 s0' e He Hretro Hfloor Hdep Hspec Hupd
                     | t0 m0 r0 h st s0 s0' e He Hretro Hhor Hdep Hspec Hupd]; rewrite He in Hev.
      - discriminate.
      - res_inv Hev. subst s0'. simpl in Hretro, Hspec. destruct Hspec as [Hspec2 _].
        assert (Hstep2 : VStep P2 (Build_ThreadEvent t (ResEv m r)) s2 (upd_retro P2 s2 t m h)).
        { eapply vstep_retro; [reflexivity | exact Hretro | | | | reflexivity].
          - eapply Pos.le_lt_trans; [exact (pj_floor2 _ _ _ HP) | exact Hfloor].
          - intros o h' Hin Hd. exact (Hdep (inr o) h' (pj_past2 _ _ _ HP _ _ _ Hin) Hd).
          - rewrite (pj_tl2 _ _ _ HP). exact Hspec2. }
        exists (upd_retro P2 s2 t m h). split; [exact Hstep2|].
        constructor; simpl.
        + exact HI'.
        + exact (pj_inv1 _ _ _ HP).
        + exact (VStep_Inv P2 _ _ _ Hstep2 (pj_inv2 _ _ _ HP)).
        + exact (pj_tl1 _ _ _ HP).
        + exact (pj_tl2 _ _ _ HP).
        + intros t' o h' Hin. unfold push_past. apply In_push. exact (pj_past1 _ _ _ HP _ _ _ Hin).
        + intros t' o h' Hin. unfold push_past in *.
          apply In_push_inv in Hin as [(-> & -> & ->) | Hin].
          * rewrite Pos.eqb_refl. left. reflexivity.
          * apply In_push. exact (pj_past2 _ _ _ HP _ _ _ Hin).
        + pose proof (pj_floor1 _ _ _ HP). destruct (vl_sync P2 m); [|assumption].
          eapply Pos.le_trans; [eassumption | apply Pos.le_max_l].
        + pose proof (pj_floor2 _ _ _ HP). destruct (vl_sync P2 m); [|assumption].
          apply Pos.max_le_compat; [assumption | apply Pos.le_refl].
        + eapply Pos.le_trans; [exact (pj_hor1 _ _ _ HP) | apply Pos.le_max_l].
        + apply Pos.max_le_compat; [exact (pj_hor2 _ _ _ HP) | apply Pos.le_refl].
      - res_inv Hev. subst s0'. simpl in Hretro, Hspec. destruct Hspec as [Hspec2 Hfst].
        assert (Hstep2 : VStep P2 (Build_ThreadEvent t (ResEv m r)) s2 (upd_app P2 s2 t m h (snd st))).
        { eapply vstep_app; [reflexivity | exact Hretro | | | | reflexivity].
          - eapply Pos.le_lt_trans; [exact (pj_hor2 _ _ _ HP) | exact Hhor].
          - intros o h' Hin Hd. exact (Hdep (inr o) h' (pj_past2 _ _ _ HP _ _ _ Hin) Hd).
          - rewrite (pj_tl2 _ _ _ HP). exact Hspec2. }
        exists (upd_app P2 s2 t m h (snd st)). split; [exact Hstep2|].
        constructor; simpl.
        + exact HI'.
        + exact (pj_inv1 _ _ _ HP).
        + exact (VStep_Inv P2 _ _ _ Hstep2 (pj_inv2 _ _ _ HP)).
        + intros h'. unfold tl_write. destruct (Pos.leb h h') eqn:Hle; [|apply (pj_tl1 _ _ _ HP)].
          apply Pos.leb_le in Hle. rewrite Hfst, (pj_tl1 _ _ _ HP).
          pose proof (pj_inv _ _ _ HP) as HI.
          rewrite (inv_const _ _ HI h') by (eapply le_lt_le; [apply Pos.le_refl | exact (Pos.lt_le_trans _ _ _ Hhor Hle)]).
          rewrite (inv_const _ _ HI h) by (apply Pos.lt_le_incl; exact Hhor).
          reflexivity.
        + intros h'. unfold tl_write. destruct (Pos.leb h h'); [reflexivity | apply (pj_tl2 _ _ _ HP)].
        + intros t' o h' Hin. unfold push_past. apply In_push. exact (pj_past1 _ _ _ HP _ _ _ Hin).
        + intros t' o h' Hin. unfold push_past in *.
          apply In_push_inv in Hin as [(-> & -> & ->) | Hin].
          * rewrite Pos.eqb_refl. left. reflexivity.
          * apply In_push. exact (pj_past2 _ _ _ HP _ _ _ Hin).
        + pose proof (pj_floor1 _ _ _ HP). pose proof (inv_floor _ _ (pj_inv _ _ _ HP)).
          destruct (vl_sync P2 m); [|assumption].
          eapply le_lt_le; [eapply Pos.le_trans; eassumption | exact Hhor].
        + pose proof (pj_floor2 _ _ _ HP). destruct (vl_sync P2 m); [apply Pos.le_refl | assumption].
        + eapply le_lt_le; [exact (pj_hor1 _ _ _ HP) | exact Hhor].
        + apply Pos.le_refl.
    Qed.

    (** ** T1 *)

    Theorem shared_sim_by_tensor :
      UnderlayRefinement.UnderlaySim (tens_lts (VL P1) (VL P2)) (VL PT) Rel.
    Proof.
      constructor.
      - intros ev x x' y HR Hs.
        destruct Hs as [t op s s' Hs | t op r s s' Hs].
        + apply (vstep_inv_inv PT) in Hs. subst s'.
          destruct y as [[a | a ta ma] [b | b tb mb]]; try contradiction. simpl in HR.
          destruct op as [m | m].
          * exists (Pending a t m, Idle b). split; [|simpl; auto].
            simpl. split; [|reflexivity]. constructor. econstructor. reflexivity.
          * exists (Idle a, Pending b t m). split; [|simpl; auto].
            simpl. split; [|reflexivity]. constructor. econstructor. reflexivity.
        + destruct op as [m | m].
          * destruct y as [[a | a ta ma] [b | b tb mb]]; try contradiction.
            destruct HR as (HP & -> & ->).
            destruct (resp1 _ _ _ _ _ _ _ HP Hs) as (a' & Ha & HP').
            exists (Idle a', Idle b). split; [|exact HP'].
            simpl. split; [|reflexivity]. constructor. exact Ha.
          * destruct y as [[a | a ta ma] [b | b tb mb]]; try contradiction.
            destruct HR as (HP & -> & ->).
            destruct (resp2 _ _ _ _ _ _ _ HP Hs) as (b' & Hb & HP').
            exists (Idle a, Idle b'). split; [|exact HP'].
            simpl. split; [|reflexivity]. constructor. exact Hb.
      - intros ev x y HR He. destruct He as [ev s Herr].
        destruct y as [[a | a ta ma] [b | b tb mb]]; try contradiction.
        destruct ev as [t [op | op r]]; unfold err_at in Herr; simpl in Herr; [|contradiction].
        destruct op as [m | m]; simpl.
        + constructor. unfold err_at. simpl. rewrite (cur_proj1 _ _ _ HR). exact Herr.
        + constructor. unfold err_at. simpl. rewrite (cur_proj2 _ _ _ HR). exact Herr.
    Qed.

    Corollary cal_tensor_to_shared {F : Op.t} (VF : @LTS F) (M : Lang.ModuleImpl E F)
        s01 s02 ρ0 :
      TPSimulation.cal (VE := tens_lts (VL P1) (VL P2)) (VF := VF) M
        (Idle (vinit P1 s01), Idle (vinit P2 s02)) ρ0 ->
      TPSimulation.cal (VE := VL PT) (VF := VF) M (Idle (vinit PT (s01, s02))) ρ0.
    Proof.
      intros Hc.
      refine (UnderlayRefinement.cal_refine (tens_lts (VL P1) (VL P2)) (VL PT) VF Rel _ M _ _ ρ0 _ Hc).
      - exact shared_sim_by_tensor.
      - apply Rel_init.
    Qed.

  End Tensor.
End ViewLiftTensor.
