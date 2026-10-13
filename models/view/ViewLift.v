(** * ViewLift: a view-based LTS derived from a sequential specification

    Given a sequential (SC) specification of an object and three pieces
    of per-operation information, [ViewLift] builds a timestamped LTS of
    the shape that the CSL-Lin view specifications ([examples/View]) wrote
    by hand.  The pieces of information are:

    - [vl_retro m]: may [m] be timestamped in the past?  Such operations
      must leave the state unchanged.  Every other operation is appended
      after all existing timestamps.
    - [vl_dep o m]: must a later [m] of the same thread be timestamped
      after an earlier [o]?  This is the complement of the
      semi-independence relation [I], given as a boolean table so that
      [I] is decidable.
    - [vl_sync m]: is the response of [m] a global visibility point?  If
      so, every later operation of every thread is timestamped after it.

    The state is a timeline [vs_tl : Time -> state], the per-thread list
    of past operations with their timestamps, a global visibility floor
    and the horizon (the largest timestamp used so far).

    Because state-changing operations are only appended, the timeline is
    never modified below an already used timestamp.  So no
    "view-based compatibility" side condition (Def. 6.1 of the paper) is
    needed.

    The theorems [vl_sim_by_sc] and [sc_sim_by_vl] show that when every
    appended operation is synchronizing, the lifted LTS is bisimilar to
    the atomic SC specification.  Hence any [cal] proof transfers in both
    directions ([cal_sc_to_view], [cal_view_to_sc]). *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Program.Equality.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulation.
Require Import models.simlin.AtomicLTS.
Require Import models.view.UnderlayRefinement.
Import ListNotations.

Module ViewLift.
  Import Reg LinCCALBase LTSSpec AtomicLTS.

  Abbreviation Time := positive.

  Section Def.
    Context {E : Op.t}.

    Record Params : Type := {
      vl_state : Type;
      vl_spec : vl_state -> tid -> forall m : Sig.op E, Sig.ar m -> vl_state -> Prop;
      vl_err : tid -> Sig.op E -> vl_state -> Prop;
      vl_retro : Sig.op E -> bool;
      vl_dep : Sig.op E -> Sig.op E -> bool;
      vl_sync : Sig.op E -> bool;
    }.

    Context (P : Params).

    Record VState : Type := mkVS {
      vs_tl : Time -> vl_state P;
      vs_past : tid -> list (Sig.op E * Time);
      vs_floor : Time;
      vs_hor : Time;
    }.

    Definition tl_write (tl : Time -> vl_state P) (h : Time) (s : vl_state P) :
        Time -> vl_state P :=
      fun h' => if Pos.leb h h' then s else tl h'.

    Definition push_past (past : tid -> list (Sig.op E * Time)) (t : tid)
        (m : Sig.op E) (h : Time) : tid -> list (Sig.op E * Time) :=
      fun t' => if Pos.eqb t t' then (m, h) :: past t' else past t'.

    Definition upd_retro (s : VState) (t : tid) (m : Sig.op E) (h : Time) : VState :=
      mkVS (vs_tl s) (push_past (vs_past s) t m h)
           (if vl_sync P m then Pos.max (vs_floor s) h else vs_floor s)
           (Pos.max (vs_hor s) h).

    Definition upd_app (s : VState) (t : tid) (m : Sig.op E) (h : Time)
        (st : vl_state P) : VState :=
      mkVS (tl_write (vs_tl s) h st) (push_past (vs_past s) t m h)
           (if vl_sync P m then h else vs_floor s)
           h.

    (** Same-thread order: [h] is above every earlier operation of [t]
        that [m] depends on. *)
    Definition dep_ok (s : VState) (t : tid) (m : Sig.op E) (h : Time) : Prop :=
      forall o h', In (o, h') (vs_past s t) -> vl_dep P o m = true -> Pos.lt h' h.

    Variant VStep : @ThreadEvent E -> VState -> VState -> Prop :=
    | vstep_inv t m s e
        (He : e = Build_ThreadEvent t (InvEv m)) :
        VStep e s s
    | vstep_retro t m r h s s' e
        (He : e = Build_ThreadEvent t (ResEv m r))
        (Hretro : vl_retro P m = true)
        (Hfloor : Pos.lt (vs_floor s) h)
        (Hdep : dep_ok s t m h)
        (Hspec : vl_spec P (vs_tl s h) t m r (vs_tl s h))
        (Hupd : s' = upd_retro s t m h) :
        VStep e s s'
    | vstep_app t m r h st s s' e
        (He : e = Build_ThreadEvent t (ResEv m r))
        (Hretro : vl_retro P m = false)
        (Hhor : Pos.lt (vs_hor s) h)
        (Hdep : dep_ok s t m h)
        (Hspec : vl_spec P (vs_tl s h) t m r st)
        (Hupd : s' = upd_app s t m h st) :
        VStep e s s'.

    (** The current state is the timeline at the horizon. *)
    Definition cur (s : VState) : vl_state P := vs_tl s (vs_hor s).

    Definition err_at (ev : @ThreadEvent E) (st : vl_state P) : Prop :=
      match te_ev ev with
      | InvEv m => vl_err P (te_tid ev) m st
      | ResEv _ _ => False
      end.

    Definition VError : @ThreadEvent E -> @AState E VState -> Prop :=
      AError (fun ev s => err_at ev (cur s)).

    Definition VL : @LTS E := VAE VStep VError.

    Definition vinit (s0 : vl_state P) : VState :=
      mkVS (fun _ => s0) (fun _ => []) xH xH.

    (** ** Invariants of reachable states *)

    Record Inv (s : VState) : Prop := {
      inv_floor : Pos.le (vs_floor s) (vs_hor s);
      inv_past : forall t o h, In (o, h) (vs_past s t) -> Pos.le h (vs_hor s);
      inv_const : forall h, Pos.le (vs_hor s) h -> vs_tl s h = vs_tl s (vs_hor s);
    }.

    Lemma Inv_init s0 : Inv (vinit s0).
    Proof.
      constructor; simpl.
      - apply Pos.le_refl.
      - intros t o h [].
      - reflexivity.
    Qed.

    Lemma push_past_In past t m h t' o h' :
      In (o, h') (push_past past t m h t') ->
      (t = t' /\ o = m /\ h' = h) \/ In (o, h') (past t').
    Proof.
      unfold push_past. destruct (Pos.eqb t t') eqn:Heqtt; [|auto].
      apply Pos.eqb_eq in Heqtt. intros [H | H]; [left | right; exact H].
      inversion H; subst; auto.
    Qed.

    (** From [{|t; ResEv op r|} = {|t1; ResEv m1 r1|}], substitute [t1],
        [m1] and [r1]. *)
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

    Lemma VStep_Inv ev s s' : VStep ev s s' -> Inv s -> Inv s'.
    Proof.
      intros Hs HI.
      destruct Hs as [t m s0 e He | t m r h s0 s1 e He Hretro Hfloor Hdep Hspec Hupd
                     | t m r h st s0 s1 e He Hretro Hhor Hdep Hspec Hupd]; subst;
        [exact HI | |].
      - destruct HI as [Hf Hp Hc]. constructor; simpl.
        + destruct (vl_sync P m).
          * apply Pos.max_le_compat; [exact Hf | apply Pos.le_refl].
          * eapply Pos.le_trans; [exact Hf | apply Pos.le_max_l].
        + intros t' o h' Hin. apply push_past_In in Hin as [(-> & -> & ->) | Hin].
          * apply Pos.le_max_r.
          * eapply Pos.le_trans; [exact (Hp _ _ _ Hin) | apply Pos.le_max_l].
        + intros h' Hle.
          assert (Hh : Pos.le (vs_hor s0) h') by (eapply Pos.le_trans; [apply Pos.le_max_l | exact Hle]).
          rewrite (Hc _ Hh).
          symmetry. apply Hc. apply Pos.le_max_l.
      - destruct HI as [Hf Hp Hc]. constructor; simpl.
        + destruct (vl_sync P m); [apply Pos.le_refl|].
          apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact Hf | exact Hhor].
        + intros t' o h' Hin. apply push_past_In in Hin as [(-> & -> & ->) | Hin].
          * apply Pos.le_refl.
          * apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact (Hp _ _ _ Hin) | exact Hhor].
        + intros h' Hle. unfold tl_write.
          rewrite (proj2 (Pos.leb_le h h') Hle), Pos.leb_refl. reflexivity.
    Qed.

    Definition AInv (x : @AState E VState) : Prop := Inv (state x).

    Lemma AStep_AInv ev x x' : Step VL ev x x' -> AInv x -> AInv x'.
    Proof.
      intros Hs. destruct Hs as [t op s1 s2 Hstep | t op r s1 s2 Hstep]; unfold AInv; simpl;
        apply VStep_Inv with (1 := Hstep).
    Qed.

    (** ** Collapse to SC when every appended operation synchronizes *)

    Variant SCStep : @ThreadEvent E -> vl_state P -> vl_state P -> Prop :=
    | scstep_inv t m s e
        (He : e = Build_ThreadEvent t (InvEv m)) :
        SCStep e s s
    | scstep_res t m r s s' e
        (He : e = Build_ThreadEvent t (ResEv m r))
        (Hspec : vl_spec P s t m r s') :
        SCStep e s s'.

    Definition SCError : @ThreadEvent E -> @AState E (vl_state P) -> Prop :=
      AError err_at.

    Definition SC : @LTS E := VAE SCStep SCError.

    Section Collapse.
      Hypothesis Hsync : forall m, vl_retro P m = false -> vl_sync P m = true.
      Hypothesis Hpres : forall s t m r s',
        vl_retro P m = true -> vl_spec P s t m r s' -> s' = s.

      (** Above the floor the timeline is constant. *)
      Definition SCInv (s : VState) : Prop :=
        Inv s /\ forall h, Pos.le (vs_floor s) h -> vs_tl s h = vs_tl s (vs_floor s).

      Lemma SCInv_init s0 : SCInv (vinit s0).
      Proof. split; [apply Inv_init | reflexivity]. Qed.

      Lemma SCInv_cur s : SCInv s -> cur s = vs_tl s (vs_floor s).
      Proof. intros [HI Hc]. unfold cur. apply Hc, (inv_floor _ HI). Qed.

      Lemma SCInv_at s h : SCInv s -> Pos.le (vs_floor s) h -> vs_tl s h = cur s.
      Proof. intros HS Hle. rewrite (SCInv_cur _ HS). apply (proj2 HS), Hle. Qed.

      Lemma VStep_SCInv ev s s' : VStep ev s s' -> SCInv s -> SCInv s'.
      Proof.
        intros Hs HS. split; [exact (VStep_Inv _ _ _ Hs (proj1 HS))|].
        destruct HS as [HI Hc].
        destruct Hs as [t m s0 e He | t m r h s0 s1 e He Hretro Hfloor Hdep Hspec Hupd
                       | t m r h st s0 s1 e He Hretro Hhor Hdep Hspec Hupd]; subst;
          [exact Hc | |].
        - simpl. intros h' Hle.
          assert (Hfl : Pos.le (vs_floor s0)
                          (if vl_sync P m then Pos.max (vs_floor s0) h else vs_floor s0))
            by (destruct (vl_sync P m); [apply Pos.le_max_l | apply Pos.le_refl]).
          rewrite (Hc h') by (eapply Pos.le_trans; [exact Hfl | exact Hle]).
          symmetry. apply Hc, Hfl.
        - simpl. rewrite (Hsync _ Hretro). intros h' Hle. unfold tl_write.
          rewrite (proj2 (Pos.leb_le h h') Hle), Pos.leb_refl. reflexivity.
      Qed.

      (** Bisimulation between the lifted LTS and the SC LTS. *)
      Definition SCRel (x : @AState E VState) (y : @AState E (vl_state P)) : Prop :=
        match x, y with
        | Idle s, Idle st => SCInv s /\ st = cur s
        | Pending s t m, Pending st t' m' => SCInv s /\ st = cur s /\ t = t' /\ m = m'
        | _, _ => False
        end.

      Lemma succ_gt h : Pos.lt h (Pos.succ h).
      Proof. apply Pos.lt_succ_diag_r. Qed.

      Lemma dep_ok_succ s t m : Inv s -> dep_ok s t m (Pos.succ (vs_hor s)).
      Proof.
        intros HI o h' Hin _. eapply Pos.le_lt_trans; [exact (inv_past _ HI _ _ _ Hin) | apply succ_gt].
      Qed.

      Lemma vstep_inv_inv t op s s' :
        VStep (Build_ThreadEvent t (InvEv op)) s s' -> s' = s.
      Proof. intros Hs. inversion Hs; subst; [reflexivity | discriminate | discriminate]. Qed.

      Lemma scstep_inv_inv t op s s' :
        SCStep (Build_ThreadEvent t (InvEv op)) s s' -> s' = s.
      Proof. intros Hs. inversion Hs; subst; [reflexivity | discriminate]. Qed.

      (** A response step of the lifted LTS is an SC response step on the
          current states. *)
      Lemma vstep_res_sc t op r s s' :
        SCInv s -> VStep (Build_ThreadEvent t (ResEv op r)) s s' ->
        vl_spec P (cur s) t op r (cur s').
      Proof.
        intros HS Hs. remember (Build_ThreadEvent t (ResEv op r)) as ev eqn:Hev.
        destruct Hs as [t1 m1 s1 e He | t1 m1 r1 h s1 s2 e He Hretro Hfloor Hdep Hspec Hupd
                       | t1 m1 r1 h st s1 s2 e He Hretro Hhor Hdep Hspec Hupd]; rewrite He in Hev.
        - discriminate.
        - res_inv Hev. subst s2.
          assert (Hcur : cur (upd_retro s1 t op h) = cur s1).
          { unfold cur, upd_retro. simpl. apply (SCInv_at s1); [exact HS|].
            eapply Pos.le_trans; [exact (inv_floor _ (proj1 HS)) | apply Pos.le_max_l]. }
          rewrite Hcur. rewrite <- (SCInv_at s1 h HS (Pos.lt_le_incl _ _ Hfloor)). exact Hspec.
        - res_inv Hev. subst s2.
          assert (Hcur : cur (upd_app s1 t op h st) = st).
          { unfold cur, upd_app, tl_write. simpl. rewrite Pos.leb_refl. reflexivity. }
          rewrite Hcur.
          rewrite <- (SCInv_at s1 h HS); [exact Hspec|].
          apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact (inv_floor _ (proj1 HS)) | exact Hhor].
      Qed.

      Lemma scstep_res_spec t op r st st' :
        SCStep (Build_ThreadEvent t (ResEv op r)) st st' -> vl_spec P st t op r st'.
      Proof.
        intros Hs. remember (Build_ThreadEvent t (ResEv op r)) as ev eqn:Hev.
        destruct Hs as [t1 m1 s1 e He | t1 m1 r1 s1 s2 e He Hspec]; rewrite He in Hev.
        - discriminate.
        - res_inv Hev. exact Hspec.
      Qed.

      (** The lifted LTS is simulated by the SC LTS. *)
      Lemma vl_sim_by_sc : UnderlayRefinement.UnderlaySim SC VL SCRel.
      Proof.
        constructor.
        - intros ev x x' y HR Hs. destruct Hs as [t op s1 s2 Hs | t op r s1 s2 Hs].
          + apply vstep_inv_inv in Hs. subst s2.
            destruct y as [st | st t' op']; [|contradiction].
            destruct HR as [HS ->].
            exists (Pending (cur s1) t op). split.
            * constructor. econstructor. reflexivity.
            * simpl. auto.
          + destruct y as [st | st t' op']; [contradiction|].
            destruct HR as (HS & -> & <- & <-).
            exists (Idle (cur s2)). split.
            * constructor. eapply scstep_res; [reflexivity|]. eapply vstep_res_sc; eauto.
            * simpl. split; [eapply VStep_SCInv; eauto | reflexivity].
        - intros ev x y HR He. destruct He as [ev s Herr].
          destruct y as [st | st t' op']; [|contradiction].
          destruct HR as [_ ->]. constructor. exact Herr.
      Qed.

      (** The SC LTS is simulated by the lifted LTS. *)
      Lemma sc_sim_by_vl : UnderlayRefinement.UnderlaySim VL SC (fun y x => SCRel x y).
      Proof.
        constructor.
        - intros ev y y' x HR Hs. destruct Hs as [t op st1 st2 Hs | t op r st1 st2 Hs].
          + apply scstep_inv_inv in Hs. subst st2.
            destruct x as [s | s t' op']; [|contradiction].
            destruct HR as [HS ->].
            exists (Pending s t op). split.
            * constructor. econstructor. reflexivity.
            * simpl. auto.
          + destruct x as [s | s t' op']; [contradiction|].
            destruct HR as (HS & -> & -> & ->).
            assert (Hspec : vl_spec P (cur s) t op r st2) by exact (scstep_res_spec _ _ _ _ _ Hs).
            remember (Pos.succ (vs_hor s)) as h eqn:Hh.
            assert (Hhor : Pos.lt (vs_hor s) h) by (subst h; apply succ_gt).
            assert (Hdepok : dep_ok s t op h) by (subst h; apply dep_ok_succ, (proj1 HS)).
            assert (Hfl : Pos.le (vs_floor s) h)
              by (apply Pos.lt_le_incl; eapply Pos.le_lt_trans; [exact (inv_floor _ (proj1 HS)) | exact Hhor]).
            assert (Htl : vs_tl s h = cur s) by exact (SCInv_at s h HS Hfl).
            destruct (vl_retro P op) eqn:Hr.
            * pose proof (Hpres _ _ _ _ _ Hr Hspec) as ->.
              assert (Hv : VStep (Build_ThreadEvent t (ResEv op r)) s (upd_retro s t op h)).
              { eapply vstep_retro; [reflexivity | exact Hr | | exact Hdepok | | reflexivity].
                - eapply Pos.le_lt_trans; [exact (inv_floor _ (proj1 HS)) | exact Hhor].
                - rewrite Htl. exact Hspec. }
              exists (Idle (upd_retro s t op h)). split; [constructor; exact Hv|].
              simpl. split; [eapply VStep_SCInv; eauto|].
              unfold cur, upd_retro. simpl. symmetry. apply (SCInv_at s); [exact HS|].
              eapply Pos.le_trans; [exact Hfl | apply Pos.le_max_r].
            * assert (Hv : VStep (Build_ThreadEvent t (ResEv op r)) s (upd_app s t op h st2)).
              { eapply vstep_app; [reflexivity | exact Hr | exact Hhor | exact Hdepok | | reflexivity].
                rewrite Htl. exact Hspec. }
              exists (Idle (upd_app s t op h st2)). split; [constructor; exact Hv|].
              simpl. split; [eapply VStep_SCInv; eauto|].
              unfold cur, upd_app, tl_write. simpl. rewrite Pos.leb_refl. reflexivity.
        - intros ev y x HR He. destruct He as [ev st Herr].
          destruct x as [s | s t' op']; [|contradiction].
          destruct HR as [_ ->]. constructor. exact Herr.
      Qed.

      Lemma SCRel_init s0 : SCRel (Idle (vinit s0)) (Idle s0).
      Proof. split; [apply SCInv_init | reflexivity]. Qed.
    End Collapse.

    (** ** Transfer of [cal] proofs *)

    Section Transfer.
      Hypothesis Hsync : forall m, vl_retro P m = false -> vl_sync P m = true.
      Hypothesis Hpres : forall s t m r s',
        vl_retro P m = true -> vl_spec P s t m r s' -> s' = s.
      Context {F : Op.t} (VF : @LTS F) (M : Lang.ModuleImpl E F).

      (** A proof against the SC specification is a proof against the
          lifted (view) specification ... *)
      Theorem cal_sc_to_view s0 ρ0 :
        TPSimulation.cal (VE := SC) (VF := VF) M (Idle s0) ρ0 ->
        TPSimulation.cal (VE := VL) (VF := VF) M (Idle (vinit s0)) ρ0.
      Proof.
        intros Hc.
        refine (UnderlayRefinement.cal_refine SC VL VF SCRel _ M _ (Idle s0) ρ0 _ Hc).
        - apply vl_sim_by_sc; assumption.
        - apply SCRel_init.
      Qed.

      (** ... and conversely. *)
      Theorem cal_view_to_sc s0 ρ0 :
        TPSimulation.cal (VE := VL) (VF := VF) M (Idle (vinit s0)) ρ0 ->
        TPSimulation.cal (VE := SC) (VF := VF) M (Idle s0) ρ0.
      Proof.
        intros Hc.
        refine (UnderlayRefinement.cal_refine VL SC VF (fun y x => SCRel x y) _ M _
                  (Idle (vinit s0)) ρ0 _ Hc).
        - apply sc_sim_by_vl; assumption.
        - apply SCRel_init.
      Qed.
    End Transfer.
  End Def.
End ViewLift.
