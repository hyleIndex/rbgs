(** * The CSL-Lin TSO CAS register is an instance of [ViewLift], hence SC

    [CASRegTSOSpec.VCASRegTSO] ([ViewSpecs.v]) was written by hand.  This
    file shows that it is bisimilar to [ViewLift.VL CASP], where [CASP] is
    the SC CAS register with:

    - [get] retroactive and non-synchronizing;
    - [cas] appended and synchronizing;
    - no semi-independence (every same-thread pair is ordered).

    Since every appended operation synchronizes, [ViewLift]'s collapse
    theorem applies.  Hence [cal] proofs over [VCASRegTSO] and over the
    atomic SC CAS register ([ViewLift.SC CASP]) transfer in both
    directions ([cas_tso_to_sc], [cas_sc_to_tso]).  The exchanger of
    [ExchangerTSO.v] therefore runs on an observationally SC
    register. *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Logic.Eqdep.
Require Import Stdlib.Program.Equality.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulation.
Require Import examples.Common.AtomicLTS.
Require Import examples.View.ViewSpecs.
Require Import models.view.UnderlayRefinement.
Require Import models.view.ViewLift.
Import ListNotations.

Module ViewLiftCAS.
  Import Reg LinCCALBase LTSSpec AtomicLTS CASRegTSOSpec ViewLift.

  Section CAS.
    Context {A : Type}.

    Definition cas_spec (s : A) (t : tid) (m : ECASReg_op A) : ECASReg_ar m -> A -> Prop :=
      match m as m0 return ECASReg_ar m0 -> A -> Prop with
      | get => fun r s' => r = s /\ s' = s
      | cas e d => fun r s' => (s = e /\ r = true /\ s' = d) \/ (s <> e /\ r = false /\ s' = s)
      end.

    Definition CASP : @Params (ECASReg A) := {|
      vl_state := A;
      vl_spec := cas_spec;
      vl_err := fun _ _ _ => False;
      vl_retro := fun m => match m with get => true | cas _ _ => false end;
      vl_dep := fun _ _ => true;
      vl_sync := fun m => match m with get => false | cas _ _ => true end;
    |}.

    (** ** Per-thread view of a lifted state *)

    Definition own (v : VState CASP) (t : tid) : Time :=
      fold_right Pos.max (vs_floor CASP v) (map snd (vs_past CASP v t)).

    Lemma fold_max_ge b l : Pos.le b (fold_right Pos.max b l).
    Proof.
      induction l as [|a l IH]; simpl; [apply Pos.le_refl|].
      eapply Pos.le_trans; [exact IH | apply Pos.le_max_r].
    Qed.

    Lemma fold_max_lt b l h :
      Pos.lt (fold_right Pos.max b l) h <-> Pos.lt b h /\ forall x, In x l -> Pos.lt x h.
    Proof.
      induction l as [|a l IH]; simpl.
      - split; [intros; split; [assumption | intros _ []] | intros [H _]; exact H].
      - rewrite Pos.max_lub_lt_iff. rewrite IH. split.
        + intros (Ha & Hb & Hl). split; [exact Hb|]. intros x [<- | Hx]; auto.
        + intros (Hb & Hl). auto.
    Qed.

    Lemma fold_max_le b l h :
      Pos.le b h -> (forall x, In x l -> Pos.le x h) -> Pos.le (fold_right Pos.max b l) h.
    Proof.
      intros Hb Hl. induction l as [|a l IH]; simpl; [exact Hb|].
      apply Pos.max_lub; [apply Hl; left; reflexivity | apply IH; intros; apply Hl; right; assumption].
    Qed.

    Lemma own_lt v t h :
      Pos.lt (own v t) h <->
      Pos.lt (vs_floor CASP v) h /\ forall o h', In (o, h') (vs_past CASP v t) -> Pos.lt h' h.
    Proof.
      unfold own. rewrite fold_max_lt. split.
      - intros [Hf Hl]. split; [exact Hf|]. intros o h' Hin. apply Hl.
        apply in_map_iff. exists (o, h'). auto.
      - intros [Hf Hl]. split; [exact Hf|]. intros x Hx. apply in_map_iff in Hx as ([o h'] & <- & Hin).
        exact (Hl _ _ Hin).
    Qed.

    Lemma own_le_hor v t : Inv CASP v -> Pos.le (own v t) (vs_hor CASP v).
    Proof.
      intros HI. apply fold_max_le; [exact (inv_floor _ _ HI)|].
      intros x Hx. apply in_map_iff in Hx as ([o h'] & <- & Hin). exact (inv_past _ _ HI _ _ _ Hin).
    Qed.

    Lemma own_ge_past v t o h : In (o, h) (vs_past CASP v t) -> Pos.le h (own v t).
    Proof.
      unfold own. generalize (vs_past CASP v t). intros l Hin.
      induction l as [|a l IH]; [destruct Hin|]. destruct Hin as [-> | Hin]; simpl.
      - apply Pos.le_max_l.
      - eapply Pos.le_trans; [exact (IH Hin) | apply Pos.le_max_r].
    Qed.

    (** The horizon is witnessed by the floor or by some past operation. *)
    Definition HorW (v : VState CASP) : Prop :=
      vs_hor CASP v = vs_floor CASP v \/ exists t o, In (o, vs_hor CASP v) (vs_past CASP v t).

    Lemma hor_lt v h :
      Inv CASP v -> HorW v -> ((forall t, Pos.lt (own v t) h) <-> Pos.lt (vs_hor CASP v) h).
    Proof.
      intros HI HW. split.
      - intros Hall. destruct HW as [Heq | (t & o & Hin)].
        + rewrite Heq. eapply Pos.le_lt_trans; [apply fold_max_ge | exact (Hall xH)].
        + eapply Pos.le_lt_trans; [exact (own_ge_past _ _ _ _ Hin) | exact (Hall t)].
      - intros Hh t. eapply Pos.le_lt_trans; [exact (own_le_hor _ _ HI) | exact Hh].
    Qed.

    (** ** The relation *)

    Record K (c : SCASRegTSO A) (v : VState CASP) : Prop := {
      k_inv : Inv CASP v;
      k_hw : HorW v;
      k_mem : forall h, cas_mem c h = vs_tl CASP v h;
      k_view : forall t, cas_view c t = own v t;
    }.

    Definition CR (x : @AState (ECASReg A) (SCASRegTSO A)) (y : @AState (ECASReg A) (VState CASP)) : Prop :=
      match x, y with
      | Idle c, Idle v => K c v
      | Pending c t m, Pending v t' m' => K c v /\ t = t' /\ m = m'
      | _, _ => False
      end.

    Lemma K_init (a : A) :
      K (mkCASRegTSO (fun _ => a) (fun _ => xH)) (vinit CASP a).
    Proof.
      constructor.
      - apply Inv_init.
      - left. reflexivity.
      - reflexivity.
      - reflexivity.
    Qed.

    (** ** Updates *)

    Lemma K_get c v t h :
      K c v -> Pos.lt (own v t) h ->
      K (mkCASRegTSO (cas_mem c) (upd_tid_time (cas_view c) t h)) (upd_retro CASP v t get h).
    Proof.
      intros HK Hlt. pose proof (proj1 (own_lt _ _ _) Hlt) as [Hfl Hpast].
      constructor.
      - eapply (VStep_Inv CASP).
        + refine (vstep_retro CASP t get (vs_tl CASP v h : A) h v _ _ eq_refl eq_refl Hfl _ _ eq_refl).
          * intros o h' Hin _. exact (Hpast _ _ Hin).
          * simpl. auto.
        + exact (k_inv _ _ HK).
      - unfold HorW; simpl. destruct (Pos.max_spec (vs_hor CASP v) h) as [[Hle ->] | [Hle ->]].
        + right. exists t, get. unfold push_past. rewrite Pos.eqb_refl. left. reflexivity.
        + destruct (k_hw _ _ HK) as [Heq | (t' & o & Hin)]; [left; exact Heq|].
          right. exists t', o. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin.
      - simpl. exact (k_mem _ _ HK).
      - intros t'. simpl. unfold upd_tid_time, own; simpl. unfold push_past.
        destruct (Pos.eqb t t') eqn:Htt.
        + apply Pos.eqb_eq in Htt. subst t'. simpl. symmetry. apply Pos.max_l.
          apply Pos.lt_le_incl. exact Hlt.
        + exact (k_view _ _ HK t').
    Qed.

    Lemma fold_max_all b l : (forall x, In x l -> Pos.le x b) -> fold_right Pos.max b l = b.
    Proof.
      intros H. apply Pos.le_antisym; [apply fold_max_le; [apply Pos.le_refl | exact H] | apply fold_max_ge].
    Qed.

    Lemma own_after_cas v t e d h st :
      Inv CASP v -> Pos.lt (vs_hor CASP v) h ->
      forall t', own (upd_app CASP v t (cas e d) h st) t' = h.
    Proof.
      intros HI Hh t'. unfold own, upd_app; simpl.
      apply fold_max_all. intros x Hx. apply in_map_iff in Hx as ([o h'] & <- & Hin). simpl.
      unfold push_past in Hin. destruct (Pos.eqb t t'); [destruct Hin as [Hin | Hin]|].
      - inversion Hin; subst. apply Pos.le_refl.
      - apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact (inv_past _ _ HI _ _ _ Hin) | exact Hh].
      - apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact (inv_past _ _ HI _ _ _ Hin) | exact Hh].
    Qed.

    Lemma K_cas c v t e d st h mem' :
      K c v -> Pos.lt (vs_hor CASP v) h ->
      (forall h', mem' h' = tl_write CASP (vs_tl CASP v) h st h') ->
      K (mkCASRegTSO mem' (view_advance_all h)) (upd_app CASP v t (cas e d) h st).
    Proof.
      intros HK Hh Hmem.
      assert (HI' : Inv CASP (upd_app CASP v t (cas e d) h st)).
      { pose proof (k_inv _ _ HK) as HI. constructor; simpl.
        - apply Pos.le_refl.
        - intros t' o h' Hin. unfold push_past in Hin.
          destruct (Pos.eqb t t'); [destruct Hin as [Hin | Hin]|].
          + inversion Hin; subst. apply Pos.le_refl.
          + apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact (inv_past _ _ HI _ _ _ Hin) | exact Hh].
          + apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact (inv_past _ _ HI _ _ _ Hin) | exact Hh].
        - intros h' Hle. unfold tl_write. rewrite (proj2 (Pos.leb_le h h') Hle), Pos.leb_refl. reflexivity. }
      constructor.
      - exact HI'.
      - right. exists t, (cas e d). simpl. unfold push_past. rewrite Pos.eqb_refl. left. reflexivity.
      - intros h'. exact (Hmem h').
      - intros t'. simpl. rewrite own_after_cas; [reflexivity | exact (k_inv _ _ HK) | exact Hh].
    Qed.

    (** ** Inversion of the hand-written steps *)

    Lemma get_res_inv t (r : A) c1 c2 :
      StepCASRegTSO {| te_tid := t; te_ev := ResEv get r |} c1 c2 ->
      exists h, Pos.lt (cas_view c1 t) h /\ r = cas_mem c1 h /\
        c2 = mkCASRegTSO (cas_mem c1) (upd_tid_time (cas_view c1) t h).
    Proof.
      intros Hs. inversion Hs; subst.
      match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H end.
      subst. eexists; eauto.
    Qed.

    Definition cas_ret (ev : @Event (ECASReg A)) : option bool :=
      match ev with
      | ResEv op b =>
          match op as o return ECASReg_ar o -> option bool with
          | cas _ _ => fun b => Some b
          | get => fun _ => None
          end b
      | InvEv _ => None
      end.

    Lemma cas_res_inv t (e d : A) (r : bool) (c1 c2 : SCASRegTSO A) :
      StepCASRegTSO {| te_tid := t; te_ev := ResEv (cas e d) r |} c1 c2 ->
      exists h, (forall t0, Pos.lt (cas_view c1 t0) h) /\
        ((cas_mem c1 h = e /\ r = true /\
          c2 = mkCASRegTSO (mem_write (cas_mem c1) h d) (view_advance_all h)) \/
         (cas_mem c1 h <> e /\ r = false /\
          c2 = mkCASRegTSO (cas_mem c1) (view_advance_all h))).
    Proof.
      intros Hs. remember (Build_ThreadEvent t (ResEv (cas e d) r)) as ev eqn:Hev.
      destruct Hs; inversion Hev; subst;
        pose proof (f_equal (fun ev => cas_ret (te_ev ev)) Hev) as Hb; simpl in Hb;
        injection Hb as Hb; subst.
      - exists h. split; [assumption|]. left. repeat split; auto.
      - exists h. split; [assumption|]. right. repeat split; auto.
    Qed.

    Lemma inv_step_eq t m (c1 c2 : SCASRegTSO A) :
      StepCASRegTSO {| te_tid := t; te_ev := InvEv m |} c1 c2 -> c2 = c1.
    Proof. intros Hs. inversion Hs; reflexivity. Qed.

    (** ** VCASRegTSO is simulated by the lifted register *)

    Lemma tso_sim_by_vl :
      UnderlayRefinement.UnderlaySim (VL CASP) VCASRegTSO CR.
    Proof.
      constructor.
      - intros ev x x' y HR Hs. destruct Hs as [t op c1 c2 Hs | t op r c1 c2 Hs].
        + apply inv_step_eq in Hs. subst c2.
          destruct y as [v | v t' op']; [|contradiction].
          exists (Pending v t op). split; [|simpl; auto].
          constructor. econstructor. reflexivity.
        + destruct y as [v | v t' op']; [contradiction|].
          destruct HR as (HK & <- & <-).
          destruct op as [|e d].
          * destruct (get_res_inv _ _ _ _ Hs) as (h & Hlt & -> & ->).
            rewrite (k_view _ _ HK) in Hlt.
            pose proof (proj1 (own_lt _ _ _) Hlt) as [Hfl Hpast].
            exists (Idle (upd_retro CASP v t get h)). split.
            -- constructor.
               refine (vstep_retro CASP t get (cas_mem c1 h : A) h v _ _ eq_refl eq_refl Hfl _ _ eq_refl).
               ++ intros o h' Hin _. exact (Hpast _ _ Hin).
               ++ simpl. rewrite (k_mem _ _ HK). auto.
            -- exact (K_get _ _ _ _ HK Hlt).
          * destruct (cas_res_inv _ _ _ _ _ _ Hs) as (h & Hall & Hcase).
            assert (Hall' : forall t0, Pos.lt (own v t0) h)
              by (intros t0; rewrite <- (k_view _ _ HK); apply Hall).
            pose proof (proj1 (hor_lt _ _ (k_inv _ _ HK) (k_hw _ _ HK)) Hall') as Hh.
            assert (Hdep : dep_ok CASP v t (cas e d) h)
              by (intros o h' Hin _; exact (proj2 (proj1 (own_lt _ _ _) (Hall' t)) _ _ Hin)).
            destruct Hcase as [(Heq & -> & ->) | (Hneq & -> & ->)].
            -- exists (Idle (upd_app CASP v t (cas e d) h d)). split.
               ++ constructor.
                  refine (vstep_app CASP t (cas e d) (true : bool) h d v _ _ eq_refl eq_refl Hh Hdep _ eq_refl).
                  simpl. left. rewrite <- (k_mem _ _ HK). auto.
               ++ apply (K_cas c1); [exact HK | exact Hh|].
                  intros h'. unfold mem_write, tl_write. rewrite (k_mem _ _ HK). reflexivity.
            -- exists (Idle (upd_app CASP v t (cas e d) h (vs_tl CASP v h))). split.
               ++ constructor.
                  refine (vstep_app CASP t (cas e d) (false : bool) h (vs_tl CASP v h) v _ _ eq_refl eq_refl Hh Hdep _ eq_refl).
                  simpl. right. rewrite <- (k_mem _ _ HK). auto.
               ++ apply (K_cas c1); [exact HK | exact Hh|].
                  intros h'. unfold tl_write. rewrite (k_mem _ _ HK).
                  destruct (Pos.leb h h') eqn:Hle; [|reflexivity].
                  apply Pos.leb_le in Hle. pose proof (k_inv _ _ HK) as HI.
                  rewrite (inv_const _ _ HI h') by (apply Pos.lt_le_incl; exact (Pos.lt_le_trans _ _ _ Hh Hle)).
                  symmetry. apply (inv_const _ _ HI). apply Pos.lt_le_incl. exact Hh.
      - intros ev x y HR He. destruct He.
    Qed.

    (** ** The lifted register is simulated by VCASRegTSO *)

    Lemma vl_sim_by_tso :
      UnderlayRefinement.UnderlaySim VCASRegTSO (VL CASP) (fun y x => CR x y).
    Proof.
      constructor.
      - intros ev y y' x HR Hs. destruct Hs as [t op v1 v2 Hs | t op r v1 v2 Hs].
        + apply (vstep_inv_inv CASP) in Hs. subst v2.
          destruct x as [c | c t' op']; [|contradiction].
          exists (Pending c t op). split; [|simpl; auto].
          constructor. destruct op; constructor.
        + destruct x as [c | c t' op']; [contradiction|].
          destruct HR as (HK & -> & ->).
          remember (Build_ThreadEvent t (ResEv op r)) as ev eqn:Hev.
          destruct Hs as [t1 m1 s0 ev0 He | t1 m1 r1 h s0 s0' ev0 He Hretro Hfloor Hdep Hspec Hupd
                         | t1 m1 r1 h st s0 s0' ev0 He Hretro Hhor Hdep Hspec Hupd];
            rewrite He in Hev; subst ev0; [discriminate | |].
          * pose proof (f_equal te_tid Hev) as Ht. pose proof (f_equal te_ev Hev) as Hr.
            simpl in Ht, Hr. subst t1 s0'.
            destruct m1 as [|e d]; [|discriminate].
            destruct op as [|e d]; [|discriminate].
            apply ResEvInversion in Hr. subst r1.
            simpl in Hspec. destruct Hspec as [-> _].
            assert (Hlt : Pos.lt (own s0 t) h) by (apply own_lt; split; [exact Hfloor | intros o h' Hin; exact (Hdep o h' Hin eq_refl)]).
            exists (Idle (mkCASRegTSO (cas_mem c) (upd_tid_time (cas_view c) t h))). split.
            -- constructor. econstructor.
               ++ rewrite (k_view _ _ HK). exact Hlt.
               ++ symmetry. apply (k_mem _ _ HK).
               ++ reflexivity.
            -- exact (K_get _ _ _ _ HK Hlt).
          * pose proof (f_equal te_tid Hev) as Ht. pose proof (f_equal te_ev Hev) as Hr.
            simpl in Ht, Hr. subst t1 s0'.
            destruct m1 as [|e d]; [discriminate|].
            destruct op as [|e' d']; [discriminate|].
            pose proof Hr as Hr0. injection Hr0 as He' Hd'. subst e' d'.
            apply ResEvInversion in Hr. subst r1.
            assert (Hall : forall t0, Pos.lt (cas_view c t0) h).
            { intros t0. rewrite (k_view _ _ HK). apply (hor_lt _ _ (k_inv _ _ HK) (k_hw _ _ HK)). exact Hhor. }
            simpl in Hspec. destruct Hspec as [(Heq & -> & ->) | (Hneq & -> & ->)].
            -- exists (Idle (mkCASRegTSO (mem_write (cas_mem c) h d) (view_advance_all h))). split.
               ++ constructor. eapply step_cas_success_res; [exact Hall | rewrite (k_mem _ _ HK); exact Heq | reflexivity].
               ++ apply (K_cas c); [exact HK | exact Hhor|].
                  intros h'. unfold mem_write, tl_write. rewrite (k_mem _ _ HK). reflexivity.
            -- exists (Idle (mkCASRegTSO (cas_mem c) (view_advance_all h))). split.
               ++ constructor. eapply step_cas_fail_res; [exact Hall | rewrite (k_mem _ _ HK); exact Hneq | reflexivity].
               ++ apply (K_cas c); [exact HK | exact Hhor|].
                  intros h'. unfold tl_write. rewrite (k_mem _ _ HK).
                  destruct (Pos.leb h h') eqn:Hle; [|reflexivity].
                  apply Pos.leb_le in Hle. pose proof (k_inv _ _ HK) as HI.
                  rewrite (inv_const _ _ HI h') by (apply Pos.lt_le_incl; exact (Pos.lt_le_trans _ _ _ Hhor Hle)).
                  symmetry. apply (inv_const _ _ HI). apply Pos.lt_le_incl. exact Hhor.
      - intros ev y x HR He. destruct He as [ev v Herr].
        unfold err_at in Herr. destruct (te_ev ev); [destruct Herr | destruct Herr].
    Qed.

    (** ** Transfer of [cal] proofs *)

    Definition tso_init (a : A) : @AState (ECASReg A) (SCASRegTSO A) :=
      Idle (mkCASRegTSO (fun _ => a) (fun _ => xH)).

    Section Transfer.
      Context {F : Op.t} (VF : @LTS F) (M : Lang.ModuleImpl (ECASReg A) F).

      Theorem cas_vl_to_tso a ρ0 :
        TPSimulation.cal (VE := VL CASP) (VF := VF) M (Idle (vinit CASP a)) ρ0 ->
        TPSimulation.cal (VE := VCASRegTSO) (VF := VF) M (tso_init a) ρ0.
      Proof.
        intros Hc. refine (UnderlayRefinement.cal_refine (VL CASP) VCASRegTSO VF CR _ M _ _ ρ0 _ Hc).
        - exact tso_sim_by_vl.
        - apply K_init.
      Qed.

      Theorem cas_tso_to_vl a ρ0 :
        TPSimulation.cal (VE := VCASRegTSO) (VF := VF) M (tso_init a) ρ0 ->
        TPSimulation.cal (VE := VL CASP) (VF := VF) M (Idle (vinit CASP a)) ρ0.
      Proof.
        intros Hc. refine (UnderlayRefinement.cal_refine VCASRegTSO (VL CASP) VF (fun y x => CR x y) _ M _ _ ρ0 _ Hc).
        - exact vl_sim_by_tso.
        - apply K_init.
      Qed.

      Lemma CASP_sync : forall m, vl_retro CASP m = false -> vl_sync CASP m = true.
      Proof. intros [|e d]; simpl; [discriminate | reflexivity]. Qed.

      Lemma CASP_pres : forall s t m r s',
        vl_retro CASP m = true -> vl_spec CASP s t m r s' -> s' = s.
      Proof. intros s t [|e d] r s' Hr Hs; [exact (proj2 Hs) | discriminate]. Qed.

      (** The hand-written TSO register and the atomic SC register admit
          exactly the same [cal] proofs. *)
      Theorem cas_tso_to_sc a ρ0 :
        TPSimulation.cal (VE := VCASRegTSO) (VF := VF) M (tso_init a) ρ0 ->
        TPSimulation.cal (VE := SC CASP) (VF := VF) M (Idle a) ρ0.
      Proof.
        intros Hc. apply (cal_view_to_sc CASP CASP_sync CASP_pres VF M).
        apply cas_tso_to_vl. exact Hc.
      Qed.

      Theorem cas_sc_to_tso a ρ0 :
        TPSimulation.cal (VE := SC CASP) (VF := VF) M (Idle a) ρ0 ->
        TPSimulation.cal (VE := VCASRegTSO) (VF := VF) M (tso_init a) ρ0.
      Proof.
        intros Hc. apply cas_vl_to_tso.
        exact (cal_sc_to_view CASP CASP_sync VF M a ρ0 Hc).
      Qed.
    End Transfer.
  End CAS.
End ViewLiftCAS.
