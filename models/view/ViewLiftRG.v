(** * Rely-guarantee helpers for [ViewLift] underlays and overlays

    Lemmas used by [RGILogic] proofs in which both the underlay and the
    overlay are lifted LTSs ([VL P]).  Nothing here is specific to an
    object.

    - Inversion of lifted steps ([vstep_res_cases], [vstep_inv_same]) and
      of atomic steps of [VL P] ([astep_inv_cases], [astep_res_cases]).
    - The current state after a step ([cur_retro], [cur_app],
      [vstep_res_cur]).
    - [VLMove t]: a lifted state changed by at most one response of thread
      [t].  Another thread's move leaves [t]'s past and the timeline up to
      the old horizon unchanged ([vlmove_past], [vlmove_tl_old]).
    - Linearization points on an idle overlay: [vl_lp] performs the
      invocation and the response of the abstract operation in one go;
      [vl_lp_error] reaches the error of an erroneous invocation.
    - [dep_ok_transfer]: the dependency condition of an overlay operation
      follows from the condition of the underlay operation at the same
      timestamp, given a correspondence between the two pasts. *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Relations.Relation_Operators.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import models.simlin.AtomicLTS.
Require Import models.view.ViewLift.
Import ListNotations.

Module ViewLiftRG.
  Import Reg LinCCALBase LTSSpec AtomicLTS ViewLift.

  (** ** Steps of a lifted LTS *)

  Section Steps.
    Context {E : Op.t} (Q : @Params E).

    Lemma vstep_res_cases t (m : Sig.op E) (r : Sig.ar m) v v' :
      VStep Q (Build_ThreadEvent t (ResEv m r)) v v' ->
      (vl_retro Q m = true /\ exists h, Pos.lt (vs_floor Q v) h /\ dep_ok Q v t m h /\
         vl_spec Q (vs_tl Q v h) t m r (vs_tl Q v h) /\ v' = upd_retro Q v t m h) \/
      (vl_retro Q m = false /\ exists h st, Pos.lt (vs_hor Q v) h /\ dep_ok Q v t m h /\
         vl_spec Q (vs_tl Q v h) t m r st /\ v' = upd_app Q v t m h st).
    Proof.
      intros Hs. remember (Build_ThreadEvent t (ResEv m r)) as ev eqn:Hev.
      destruct Hs as [t1 m1 s1 e He | t1 m1 r1 h s1 s2 e He Hretro Hfloor Hdep Hspec Hupd
                     | t1 m1 r1 h st s1 s2 e He Hretro Hhor Hdep Hspec Hupd];
        rewrite He in Hev; [discriminate| |].
      - pose proof (f_equal te_tid Hev) as Ht. simpl in Ht. subst t1.
        pose proof (f_equal te_ev Hev) as Hr. simpl in Hr.
        assert (Hm : m1 = m) by (injection Hr; auto). subst m1.
        apply ResEvInversion in Hr. subst r1.
        left. split; [exact Hretro|]. exists h. auto.
      - pose proof (f_equal te_tid Hev) as Ht. simpl in Ht. subst t1.
        pose proof (f_equal te_ev Hev) as Hr. simpl in Hr.
        assert (Hm : m1 = m) by (injection Hr; auto). subst m1.
        apply ResEvInversion in Hr. subst r1.
        right. split; [exact Hretro|]. exists h, st. auto.
    Qed.

    Lemma vstep_inv_same t (m : Sig.op E) v v' :
      VStep Q (Build_ThreadEvent t (InvEv m)) v v' -> v' = v.
    Proof. intros Hs. inversion Hs; subst; [reflexivity | discriminate | discriminate]. Qed.

    Lemma astep_inv_cases t (m : Sig.op E) (x y : State (VL Q)) :
      Step (VL Q) (Build_ThreadEvent t (InvEv m)) x y ->
      exists v, x = Idle v /\ y = Pending v t m.
    Proof.
      intros Hs. remember (Build_ThreadEvent t (InvEv m)) as ev eqn:Hev.
      destruct Hs as [t1 m1 s1 s2 Hs | t1 m1 r1 s1 s2 Hs]; [|discriminate].
      injection Hev as -> ->. apply vstep_inv_same in Hs. subst s2. eauto.
    Qed.

    Lemma astep_res_cases t (m : Sig.op E) (r : Sig.ar m) (x y : State (VL Q)) :
      Step (VL Q) (Build_ThreadEvent t (ResEv m r)) x y ->
      exists v v', x = Pending v t m /\ y = Idle v' /\
        VStep Q (Build_ThreadEvent t (ResEv m r)) v v'.
    Proof.
      intros Hs. remember (Build_ThreadEvent t (ResEv m r)) as ev eqn:Hev.
      destruct Hs as [t1 m1 s1 s2 Hs | t1 m1 r1 s1 s2 Hs]; [discriminate|].
      pose proof (f_equal te_tid Hev) as Ht. simpl in Ht. subst t1.
      pose proof (f_equal te_ev Hev) as Hr. simpl in Hr.
      assert (Hm : m1 = m) by (injection Hr; auto). subst m1.
      apply ResEvInversion in Hr. subst r1.
      exists s1, s2. auto.
    Qed.

    (** *** The timeline *)

    Lemma tl_write_lt tl h (st : vl_state Q) h' :
      Pos.lt h' h -> tl_write Q tl h st h' = tl h'.
    Proof.
      intros Hlt. unfold tl_write.
      destruct (Pos.leb h h') eqn:Hb; [|reflexivity].
      apply Pos.leb_le in Hb. exfalso. eapply Pos.lt_irrefl. eapply Pos.lt_le_trans; eauto.
    Qed.

    Lemma tl_write_ge tl h (st : vl_state Q) h' :
      Pos.le h h' -> tl_write Q tl h st h' = st.
    Proof. intros Hle. unfold tl_write. rewrite (proj2 (Pos.leb_le h h') Hle). reflexivity. Qed.

    Lemma tl_above v h : Inv Q v -> Pos.le (vs_hor Q v) h -> vs_tl Q v h = cur Q v.
    Proof. intros HI Hh. exact (inv_const _ _ HI h Hh). Qed.

    Lemma cur_retro v t m h : Inv Q v -> cur Q (upd_retro Q v t m h) = cur Q v.
    Proof.
      intros HI. unfold cur, upd_retro. simpl.
      apply tl_above; [exact HI | apply Pos.le_max_l].
    Qed.

    Lemma cur_app v t m h st : cur Q (upd_app Q v t m h st) = st.
    Proof. unfold cur, upd_app. simpl. apply tl_write_ge. apply Pos.le_refl. Qed.

    (** An appended operation reads the current state. *)
    Lemma spec_app_cur v t m (r : Sig.ar m) h st :
      Inv Q v -> Pos.lt (vs_hor Q v) h ->
      vl_spec Q (vs_tl Q v h) t m r st -> vl_spec Q (cur Q v) t m r st.
    Proof. intros HI Hh Hs. rewrite <- (tl_above v h HI (Pos.lt_le_incl _ _ Hh)). exact Hs. Qed.

    Lemma vstep_res_cur t m (r : Sig.ar m) v v' :
      Inv Q v -> VStep Q (Build_ThreadEvent t (ResEv m r)) v v' ->
      (vl_retro Q m = true /\ cur Q v' = cur Q v) \/
      (vl_retro Q m = false /\ vl_spec Q (cur Q v) t m r (cur Q v')).
    Proof.
      intros HI Hs.
      destruct (vstep_res_cases t m r v v' Hs)
        as [ (Hretro & h & _ & _ & _ & ->) | (Hretro & h & st & Hhor & _ & Hspec & ->)].
      - left. split; [exact Hretro | apply cur_retro; exact HI].
      - right. split; [exact Hretro|]. rewrite cur_app. exact (spec_app_cur v t m r h st HI Hhor Hspec).
    Qed.

    (** *** Moves of one thread *)

    Definition VLMove (t : tid) (x y : VState Q) : Prop :=
      y = x \/ exists m (r : Sig.ar m), VStep Q (Build_ThreadEvent t (ResEv m r)) x y.

    Lemma vlmove_refl t x : VLMove t x x.
    Proof. left. reflexivity. Qed.

    Lemma vlmove_step t m (r : Sig.ar m) x y :
      VStep Q (Build_ThreadEvent t (ResEv m r)) x y -> VLMove t x y.
    Proof. intros Hs. right. exists m, r. exact Hs. Qed.

    Lemma push_past_other (past : tid -> list (Sig.op E * Time)) t1 m h t :
      t1 <> t -> push_past past t1 m h t = past t.
    Proof.
      intros Hne. unfold push_past. destruct (Pos.eqb t1 t) eqn:Hb; [|reflexivity].
      apply Pos.eqb_eq in Hb. contradiction.
    Qed.

    Lemma push_past_self (past : tid -> list (Sig.op E * Time)) t m h :
      push_past past t m h t = (m, h) :: past t.
    Proof. unfold push_past. rewrite Pos.eqb_refl. reflexivity. Qed.

    Lemma vlmove_past t1 t x y : t1 <> t -> VLMove t1 x y -> vs_past Q y t = vs_past Q x t.
    Proof.
      intros Hne [-> | (m & r & Hs)]; [reflexivity|].
      destruct (vstep_res_cases t1 m r x y Hs)
        as [ (_ & h & _ & _ & _ & ->) | (_ & h & st & _ & _ & _ & ->)];
        simpl; apply push_past_other; exact Hne.
    Qed.

    Lemma vlmove_hor t1 x y : VLMove t1 x y -> Pos.le (vs_hor Q x) (vs_hor Q y).
    Proof.
      intros [-> | (m & r & Hs)]; [apply Pos.le_refl|].
      destruct (vstep_res_cases t1 m r x y Hs)
        as [ (_ & h & _ & _ & _ & ->) | (_ & h & st & Hhor & _ & _ & ->)]; simpl.
      - apply Pos.le_max_l.
      - apply Pos.lt_le_incl. exact Hhor.
    Qed.

    Lemma vlmove_tl_old t1 x y h :
      VLMove t1 x y -> Pos.le h (vs_hor Q x) -> vs_tl Q y h = vs_tl Q x h.
    Proof.
      intros [-> | (m & r & Hs)] Hle; [reflexivity|].
      destruct (vstep_res_cases t1 m r x y Hs)
        as [ (_ & h' & _ & _ & _ & ->) | (_ & h' & st & Hhor & _ & _ & ->)]; simpl; [reflexivity|].
      apply tl_write_lt. eapply Pos.le_lt_trans; eauto.
    Qed.

    Lemma vlmove_floor t1 x y :
      (forall m, vl_sync Q m = false) -> VLMove t1 x y -> vs_floor Q y = vs_floor Q x.
    Proof.
      intros Hns [-> | (m & r & Hs)]; [reflexivity|].
      destruct (vstep_res_cases t1 m r x y Hs)
        as [ (_ & h & _ & _ & _ & ->) | (_ & h & st & _ & _ & _ & ->)]; simpl; rewrite Hns; reflexivity.
    Qed.

    Lemma vlmove_inv t1 x y : VLMove t1 x y -> Inv Q x -> Inv Q y.
    Proof. intros [-> | (m & r & Hs)] HI; [exact HI | exact (VStep_Inv Q _ _ _ Hs HI)]. Qed.

    (** A past entry is below the horizon. *)
    Lemma past_le_hor v t o h : Inv Q v -> In (o, h) (vs_past Q v t) -> Pos.le h (vs_hor Q v).
    Proof. intros HI Hin. exact (inv_past _ _ HI _ _ _ Hin). Qed.

    (** Without synchronizing operations the floor never moves. *)
    Lemma vstep_floor ev x y :
      (forall m, vl_sync Q m = false) -> VStep Q ev x y -> vs_floor Q y = vs_floor Q x.
    Proof.
      intros Hns Hs. destruct Hs as [t m s e He | t m r h s s' e He _ _ _ _ Hupd
                                    | t m r h st s s' e He _ _ _ _ Hupd]; subst; simpl;
        [reflexivity | rewrite Hns; reflexivity | rewrite Hns; reflexivity].
    Qed.
  End Steps.

  (** ** Linearization points on an idle overlay *)

  Section LP.
    Context {F : Op.t} (Q : @Params F).

    Lemma vl_lp (w w' : VState Q) t (f : Sig.op F) (r : Sig.ar f) (pi : tmap (@Semantics.LinState F)) :
      TMap.find t pi = Some (Semantics.ls_inv f) ->
      VStep Q (Build_ThreadEvent t (ResEv f r)) w w' ->
      @Semantics.poss_steps F (VL Q) (@Semantics.PossOk F (VL Q) (Idle w) pi)
        (@Semantics.PossOk F (VL Q) (Idle w') (TMap.add t (Semantics.ls_linr f r) (TMap.add t (Semantics.ls_lini f) pi))).
    Proof.
      intros Hpi Hs.
      eapply rt_trans; apply rt_step.
      - apply Semantics.ps_inv; [| exact Hpi].
        exact (step_inv (VStep Q) t f w w (vstep_inv Q t f w _ eq_refl)).
      - apply Semantics.ps_ret; [| apply TMap.gss].
        exact (step_res (VStep Q) t f r w w' Hs).
    Qed.

    Lemma vl_lp_retro (w : VState Q) t (f : Sig.op F) (r : Sig.ar f) h pi :
      TMap.find t pi = Some (Semantics.ls_inv f) ->
      vl_retro Q f = true -> Pos.lt (vs_floor Q w) h -> dep_ok Q w t f h ->
      vl_spec Q (vs_tl Q w h) t f r (vs_tl Q w h) ->
      @Semantics.poss_steps F (VL Q) (@Semantics.PossOk F (VL Q) (Idle w) pi)
        (@Semantics.PossOk F (VL Q) (Idle (upd_retro Q w t f h)) (TMap.add t (Semantics.ls_linr f r) (TMap.add t (Semantics.ls_lini f) pi))).
    Proof.
      intros Hpi Hr Hf Hd Hs. apply vl_lp; [exact Hpi|].
      eapply vstep_retro; [reflexivity | exact Hr | exact Hf | exact Hd | exact Hs | reflexivity].
    Qed.

    Lemma vl_lp_app (w : VState Q) t (f : Sig.op F) (r : Sig.ar f) h st pi :
      TMap.find t pi = Some (Semantics.ls_inv f) ->
      vl_retro Q f = false -> Pos.lt (vs_hor Q w) h -> dep_ok Q w t f h ->
      vl_spec Q (vs_tl Q w h) t f r st ->
      @Semantics.poss_steps F (VL Q) (@Semantics.PossOk F (VL Q) (Idle w) pi)
        (@Semantics.PossOk F (VL Q) (Idle (upd_app Q w t f h st)) (TMap.add t (Semantics.ls_linr f r) (TMap.add t (Semantics.ls_lini f) pi))).
    Proof.
      intros Hpi Hr Hh Hd Hs. apply vl_lp; [exact Hpi|].
      eapply vstep_app; [reflexivity | exact Hr | exact Hh | exact Hd | exact Hs | reflexivity].
    Qed.

    (** An invocation that is an error of the overlay reaches [Semantics.PossError]. *)
    Lemma vl_lp_error (w : VState Q) t (f : Sig.op F) pi :
      TMap.find t pi = Some (Semantics.ls_inv f) -> vl_err Q t f (cur Q w) ->
      @Semantics.poss_steps F (VL Q) (@Semantics.PossOk F (VL Q) (Idle w) pi) Semantics.PossError.
    Proof.
      intros Hpi He. apply rt_step. eapply Semantics.ps_error; [| exact Hpi].
      constructor. exact He.
    Qed.

    Lemma vl_lp_find (pi : tmap (@Semantics.LinState F)) t (f : Sig.op F) (r : Sig.ar f) :
      TMap.find t (TMap.add t (Semantics.ls_linr f r) (TMap.add t (Semantics.ls_lini f) pi)) = Some (Semantics.ls_linr f r).
    Proof. apply TMap.gss. Qed.

    Lemma vl_lp_find_other (pi : tmap (@Semantics.LinState F)) t t' (f : Sig.op F) (r : Sig.ar f) :
      t' <> t ->
      TMap.find t' (TMap.add t (Semantics.ls_linr f r) (TMap.add t (Semantics.ls_lini f) pi)) = TMap.find t' pi.
    Proof. intros Hne. rewrite !TMap.gso by exact Hne. reflexivity. Qed.
  End LP.

  (** ** Dependencies through a correspondence of pasts *)

  Section DepTransfer.
    Context {E F : Op.t} (P : @Params E) (Q : @Params F).
    Context (acc : Sig.op F -> Sig.op E -> Prop).

    Definition PastRel (u : VState P) (w : VState Q) : Prop :=
      forall t o h, In (o, h) (vs_past Q w t) -> exists o', In (o', h) (vs_past P u t) /\ acc o o'.

    Lemma dep_ok_transfer u w t (m : Sig.op F) (m' : Sig.op E) h :
      PastRel u w ->
      (forall o o', acc o o' -> vl_dep Q o m = true -> vl_dep P o' m' = true) ->
      dep_ok P u t m' h -> dep_ok Q w t m h.
    Proof.
      intros HR Hd Hok o h' Hin Hdep.
      destruct (HR t o h' Hin) as (o' & Hin' & Hacc).
      exact (Hok o' h' Hin' (Hd o o' Hacc Hdep)).
    Qed.

    (** Extending both pasts by corresponding entries. *)
    Lemma PastRel_push u w t (m : Sig.op F) (m' : Sig.op E) h :
      PastRel u w -> acc m m' ->
      forall pu,
        (forall t', vs_past P pu t' = push_past (vs_past P u) t m' h t') ->
      forall pw,
        (forall t', vs_past Q pw t' = push_past (vs_past Q w) t m h t') ->
      PastRel pu pw.
    Proof.
      intros HR Hacc pu Hpu pw Hpw t' o h' Hin. rewrite Hpw in Hin.
      apply push_past_In in Hin as [ (<- & -> & ->) | Hin].
      - exists m'. split; [rewrite Hpu, push_past_self; left; reflexivity | exact Hacc].
      - destruct (HR t' o h' Hin) as (o' & Hin' & Hacc').
        exists o'. split; [|exact Hacc'].
        rewrite Hpu. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin'.
    Qed.

    (** Extending only the underlay past. *)
    Lemma PastRel_push_u u w t (m' : Sig.op E) h :
      PastRel u w ->
      forall pu,
        (forall t', vs_past P pu t' = push_past (vs_past P u) t m' h t') ->
      forall pw, (forall t', vs_past Q pw t' = vs_past Q w t') ->
      PastRel pu pw.
    Proof.
      intros HR pu Hpu pw Hpw t' o h' Hin. rewrite Hpw in Hin.
      destruct (HR t' o h' Hin) as (o' & Hin' & Hacc').
      exists o'. split; [|exact Hacc'].
      rewrite Hpu. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin'.
    Qed.
  End DepTransfer.
End ViewLiftRG.
