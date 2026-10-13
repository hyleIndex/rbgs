(** * The SeqLock underlay is a ViewLift instance, and it is weak

    [SeqLockUnderlaySpec.VSeqLockUL] ([ViewSpecs.v]) was written by hand:
    memory locations [x], [y] and a ticket lock, with per-thread,
    per-location views and a ghost owner.  This file shows that it is
    bisimilar to [ViewLift.VL SLP], where [SLP] is the SC specification
    of the same object ([sl_spec]) with:

    - [rd] retroactive; every other operation appended;
    - only [rel] synchronizing;
    - [dep o (rd l)] true exactly when [o] advances the thread's view of
      [l] ([touches]): [wrt l'] only for [l' = l], [acq] never, the
      others always.  So a read may be timestamped before an earlier
      write of the same thread to another location (TSO's write-read
      reordering) and before an earlier [acq].  Every other pair is
      dependent.

    Two rules of the hand-written specification look different but agree
    on reachable states:

    - [acq] and [rel] read the lock at the thread's own view of the lock,
      not at the current state.  The relation [K] keeps the invariant
      [k_stale]: whenever the thread may take the lock (no owner, or it
      is the owner), the lock is constant from that view on.
    - [get_ticket] and [test_ticket] read at a timestamp above every
      view.  So they are appended operations that leave the state
      unchanged.

    Results:

    - [tso_sim_by_vl], [vl_sim_by_tso]: the bisimulation.
    - [seqlock_tso_to_vl], [seqlock_vl_to_tso]: [cal] proofs transfer in
      both directions; [Mseqlock_vl] is the SeqLock proof of
      [SeqLockTSO.v] over the derived underlay.
    - Not every appended operation synchronizes, so the collapse theorem
      does not apply.  [vl_stale_read], [sc_no_stale_read] and
      [tso_stale_read] show that the object is not SC: after the owner's
      write to [x] has responded, another thread can still read the old
      value.
    - [stale_run], [stale_canon]: the run of that execution and its
      canonical trace ([ViewLiftAdequacy]), in which the overtaken write
      responds last. *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Logic.Eqdep.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import TPSimulation.
Require Import examples.Common.AtomicLTS.
Require Import examples.View.ViewSpecs.
Require Import examples.View.SeqLockTSO.
Require Import models.view.UnderlayRefinement.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftAdequacy.
Require Import models.RelaxedSignature.
Require Import models.simlin.RelaxedTraceLin.
Import ListNotations.

Module ViewLiftSeqLock.
  Import Reg LinCCALBase LTSSpec AtomicLTS SeqLockUnderlaySpec ViewLift.

  (** ** The SC specification *)

  Record SLS : Type := mkSLS { s_x : nat; s_y : nat; s_lk : nat * nat; s_own : option tid }.

  Definition sval (s : SLS) (l : MemLoc) : nat :=
    match l with loc_x => s_x s | loc_y => s_y s end.

  Definition supd (s : SLS) (l : MemLoc) (w : nat) : SLS :=
    match l with
    | loc_x => mkSLS w (s_y s) (s_lk s) (s_own s)
    | loc_y => mkSLS (s_x s) w (s_lk s) (s_own s)
    end.

  Definition slock (s : SLS) (lk : nat * nat) (o : option tid) : SLS :=
    mkSLS (s_x s) (s_y s) lk o.

  Definition sl_spec (s : SLS) (t : tid) (m : ESeqLockUL_op) : ESeqLockUL_ar m -> SLS -> Prop :=
    match m as m0 return ESeqLockUL_ar m0 -> SLS -> Prop with
    | wrt l w => fun _ s' => s_own s = Some t /\ s' = supd s l w
    | rd l => fun r s' => r = sval s l /\ s' = s
    | acq => fun _ s' =>
        exists nxt own, s_lk s = (nxt, own) /\ nxt = own /\ Nat.even nxt = true /\
          s_own s = None /\ s' = slock s ((nxt + 2)%nat, (own + 1)%nat) (Some t)
    | rel => fun _ s' =>
        exists nxt own, s_lk s = (nxt, own) /\ nxt = (own + 1)%nat /\ Nat.even nxt = true /\
          s_own s = Some t /\ s' = slock s (nxt, (own + 1)%nat) None
    | get_ticket => fun k s' => exists nxt, s_lk s = (nxt, k) /\ s' = s
    | test_ticket n => fun b s' =>
        exists k, s_lk s = (n, k) /\ b = orb (Nat.odd n) (negb (Nat.eqb k n)) /\ s' = s
    end.

  (** Does [o] advance its thread's view of location [a]? *)
  Definition touches (o : ESeqLockUL_op) (a : AllLoc) : bool :=
    match o with
    | wrt l _ => AllLoc_eqb (mem_to_all l) a
    | acq => AllLoc_eqb aloc_lk a
    | _ => true
    end.

  Definition SLP : @Params ESeqLockUL := {|
    vl_state := SLS;
    vl_spec := sl_spec;
    vl_err := fun _ _ _ => False;
    vl_retro := fun m => match m with rd _ => true | _ => false end;
    vl_dep := fun o m => match m with rd l => touches o (mem_to_all l) | _ => true end;
    vl_sync := fun m => match m with rel => true | _ => false end;
  |}.

  Definition sl_init : SLS := mkSLS O O (O, O) None.

  (** ** Per-thread, per-location views of a lifted state *)

  Definition own (v : VState SLP) (t : tid) (a : AllLoc) : Time :=
    fold_right Pos.max (vs_floor SLP v)
      (map snd (filter (fun p => touches (fst p) a) (vs_past SLP v t))).

  Lemma fold_max_ge b l : Pos.le b (fold_right Pos.max b l).
  Proof. induction l as [|x l IH]; simpl; lia. Qed.

  Lemma fold_max_lt b l h :
    Pos.lt (fold_right Pos.max b l) h <-> Pos.lt b h /\ forall x, In x l -> Pos.lt x h.
  Proof.
    induction l as [|x l IH]; simpl.
    - split; [intros; split; [assumption | intros _ []] | intros [H _]; exact H].
    - rewrite Pos.max_lub_lt_iff, IH. split.
      + intros (Ha & Hb & Hl). split; [exact Hb|]. intros y [<- | Hy]; auto.
      + intros (Hb & Hl). auto.
  Qed.

  Lemma fold_max_le b l h :
    Pos.le b h -> (forall x, In x l -> Pos.le x h) -> Pos.le (fold_right Pos.max b l) h.
  Proof.
    intros Hb Hl. induction l as [|x l IH]; simpl; [exact Hb|].
    apply Pos.max_lub; [apply Hl; left; reflexivity | apply IH; intros; apply Hl; right; assumption].
  Qed.

  Lemma fold_max_in b l x : In x l -> Pos.le x (fold_right Pos.max b l).
  Proof.
    induction l as [|y l IH]; intros Hin; [destruct Hin|]. simpl.
    destruct Hin as [-> | Hin]; [lia|]. specialize (IH Hin). lia.
  Qed.

  Lemma own_lt v t a h :
    Pos.lt (own v t a) h <->
    Pos.lt (vs_floor SLP v) h /\
    forall o h', In (o, h') (vs_past SLP v t) -> touches o a = true -> Pos.lt h' h.
  Proof.
    unfold own. rewrite fold_max_lt. split.
    - intros [Hf Hl]. split; [exact Hf|]. intros o h' Hin Ht. apply Hl.
      apply in_map_iff. exists (o, h'). split; [reflexivity|]. apply filter_In. auto.
    - intros [Hf Hl]. split; [exact Hf|]. intros x Hx.
      apply in_map_iff in Hx as ([o h'] & <- & Hin). apply filter_In in Hin as [Hin Ht].
      exact (Hl _ _ Hin Ht).
  Qed.

  Lemma own_ge_floor v t a : Pos.le (vs_floor SLP v) (own v t a).
  Proof. apply fold_max_ge. Qed.

  Lemma own_ge_past v t a o h :
    In (o, h) (vs_past SLP v t) -> touches o a = true -> Pos.le h (own v t a).
  Proof.
    intros Hin Ht. unfold own. apply fold_max_in. apply in_map_iff. exists (o, h).
    split; [reflexivity|]. apply filter_In. auto.
  Qed.

  Lemma own_le_hor v t a : Inv SLP v -> Pos.le (own v t a) (vs_hor SLP v).
  Proof.
    intros HI. apply fold_max_le; [exact (inv_floor _ _ HI)|].
    intros x Hx. apply in_map_iff in Hx as ([o h'] & <- & Hin). apply filter_In in Hin as [Hin _].
    exact (inv_past _ _ HI _ _ _ Hin).
  Qed.

  Lemma touches_some o : exists a, touches o a = true.
  Proof.
    destruct o as [l w | l | | | | n].
    - exists (mem_to_all l). destruct l; reflexivity.
    - exists aloc_x. reflexivity.
    - exists aloc_lk. reflexivity.
    - exists aloc_x. reflexivity.
    - exists aloc_x. reflexivity.
    - exists aloc_x. reflexivity.
  Qed.

  Lemma view_bar_lt (w : View) h : Pos.lt (view_bar w) h <-> forall a, Pos.lt (w a) h.
  Proof.
    unfold view_bar. split.
    - intros H [ | | ]; lia.
    - intros H. pose proof (H aloc_x). pose proof (H aloc_y). pose proof (H aloc_lk). lia.
  Qed.

  (** The horizon is witnessed by the floor or by some past operation. *)
  Definition HorW (v : VState SLP) : Prop :=
    vs_hor SLP v = vs_floor SLP v \/ exists t o, In (o, vs_hor SLP v) (vs_past SLP v t).

  Lemma hor_lt v h :
    Inv SLP v -> HorW v -> ((forall t a, Pos.lt (own v t a) h) <-> Pos.lt (vs_hor SLP v) h).
  Proof.
    intros HI HW. split.
    - intros Hall. destruct HW as [Heq | (t & o & Hin)].
      + rewrite Heq. pose proof (own_ge_floor v xH aloc_x). specialize (Hall xH aloc_x). lia.
      + destruct (touches_some o) as (a & Ha).
        pose proof (own_ge_past _ _ _ _ _ Hin Ha). specialize (Hall t a). lia.
    - intros Hh t a. pose proof (own_le_hor v t a HI). lia.
  Qed.

  (** ** The relation *)

  Definition lk_ok (v : VState SLP) (t : tid) : Prop :=
    forall h, Pos.le (own v t aloc_lk) h -> s_lk (vs_tl SLP v h) = s_lk (cur SLP v).

  Record K (c : SSeqLockUL) (v : VState SLP) : Prop := {
    k_inv : Inv SLP v;
    k_hw : HorW v;
    k_mem : forall l h, sl_mem c l h = sval (vs_tl SLP v h) l;
    k_lock : forall h, sl_lock c h = s_lk (vs_tl SLP v h);
    k_owner : sl_owner c = s_own (cur SLP v);
    k_view : forall t a, sl_view c t a = own v t a;
    k_stale : forall t, (s_own (cur SLP v) = None \/ s_own (cur SLP v) = Some t) -> lk_ok v t;
  }.

  Definition CR (x : @AState ESeqLockUL SSeqLockUL) (y : @AState ESeqLockUL (VState SLP)) : Prop :=
    match x, y with
    | Idle c, Idle v => K c v
    | Pending c t m, Pending v t' m' => K c v /\ t = t' /\ m = m'
    | _, _ => False
    end.

  Lemma K_init : K SeqLockImpl.initE (vinit SLP sl_init).
  Proof.
    constructor; simpl.
    - apply Inv_init.
    - left. reflexivity.
    - intros [|] h; reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - intros t _ h _. reflexivity.
  Qed.

  Lemma K_hbar c v h :
    K c v -> ((forall t0, Pos.lt (H_bar c t0) h) <-> Pos.lt (vs_hor SLP v) h).
  Proof.
    intros HK. rewrite <- (hor_lt v h (k_inv _ _ HK) (k_hw _ _ HK)). unfold H_bar. split.
    - intros H t a. rewrite <- (k_view _ _ HK). exact (proj1 (view_bar_lt _ _) (H t) a).
    - intros H t. apply view_bar_lt. intros a. rewrite (k_view _ _ HK). apply H.
  Qed.

  (** Above the horizon the timeline is the current state. *)
  Lemma tl_above v h : Inv SLP v -> Pos.le (vs_hor SLP v) h -> vs_tl SLP v h = cur SLP v.
  Proof. intros HI Hh. exact (inv_const _ _ HI h Hh). Qed.

  (** The lock read by [acq] and [rel] is the current lock. *)
  Lemma K_lock_own c v t :
    K c v -> (s_own (cur SLP v) = None \/ s_own (cur SLP v) = Some t) ->
    sl_lock c (sl_view c t aloc_lk) = s_lk (cur SLP v).
  Proof.
    intros HK Ho. rewrite (k_lock _ _ HK), (k_view _ _ HK).
    apply (k_stale _ _ HK t Ho). apply Pos.le_refl.
  Qed.

  (** ** Inversion of the hand-written steps *)

  Ltac inv_existT :=
    repeat match goal with H : existT _ _ _ = existT _ _ _ |- _ => apply inj_pair2 in H; subst end.

  Definition ret_nat (ev : @Event ESeqLockUL) : option nat :=
    match ev with
    | ResEv op r =>
        match op as o return ESeqLockUL_ar o -> option nat with
        | rd _ | get_ticket => fun r => Some r
        | _ => fun _ => None
        end r
    | InvEv _ => None
    end.

  Definition ret_bool (ev : @Event ESeqLockUL) : option bool :=
    match ev with
    | ResEv op r =>
        match op as o return ESeqLockUL_ar o -> option bool with
        | test_ticket _ => fun r => Some r
        | _ => fun _ => None
        end r
    | InvEv _ => None
    end.

  Lemma inv_step_eq t m c1 c2 :
    StepSeqLockUL {| te_tid := t; te_ev := InvEv m |} c1 c2 -> c2 = c1.
  Proof. intros Hs. inversion Hs; reflexivity. Qed.

  Lemma wrt_res_inv t l w r c1 c2 :
    StepSeqLockUL {| te_tid := t; te_ev := ResEv (wrt l w) r |} c1 c2 ->
    sl_owner c1 = Some t /\
    exists h, (forall t0, Pos.lt (H_bar c1 t0) h) /\
      c2 = mkSLUL (mem_write (sl_mem c1) l h w) (sl_lock c1)
             (upd_tid_view (sl_view c1) t (view_set (sl_view c1 t) (mem_to_all l) h))
             (sl_owner c1).
  Proof. intros Hs. inversion Hs; subst; inv_existT. eauto. Qed.

  Lemma rd_res_inv t l r c1 c2 :
    StepSeqLockUL {| te_tid := t; te_ev := ResEv (rd l) r |} c1 c2 ->
    exists h, Pos.lt (sl_view c1 t (mem_to_all l)) h /\ r = sl_mem c1 l h /\
      c2 = mkSLUL (sl_mem c1) (sl_lock c1)
             (upd_tid_view (sl_view c1) t (view_advance (sl_view c1 t) h)) (sl_owner c1).
  Proof.
    intros Hs. remember (Build_ThreadEvent t (ResEv (rd l) r)) as ev eqn:Hev.
    destruct Hs; inversion Hev; subst;
      pose proof (f_equal (fun e => ret_nat (te_ev e)) Hev) as Hb; simpl in Hb;
      injection Hb as Hb; subst; eauto.
  Qed.

  Lemma acq_res_inv t r c1 c2 :
    StepSeqLockUL {| te_tid := t; te_ev := ResEv acq r |} c1 c2 ->
    exists h nxt own, (forall t0, Pos.lt (H_bar c1 t0) h) /\
      sl_lock c1 (sl_view c1 t aloc_lk) = (nxt, own) /\ nxt = own /\ Nat.even nxt = true /\
      sl_owner c1 = None /\
      c2 = mkSLUL (sl_mem c1) (lock_write (sl_lock c1) h (nxt + 2)%nat (own + 1)%nat)
             (upd_tid_view (sl_view c1) t (view_set (sl_view c1 t) aloc_lk h)) (Some t).
  Proof. intros Hs. inversion Hs; subst; inv_existT. do 3 eexists. eauto 7. Qed.

  Lemma rel_res_inv t r c1 c2 :
    StepSeqLockUL {| te_tid := t; te_ev := ResEv rel r |} c1 c2 ->
    exists h nxt own, (forall t0, Pos.lt (H_bar c1 t0) h) /\
      sl_lock c1 (sl_view c1 t aloc_lk) = (nxt, own) /\ nxt = (own + 1)%nat /\
      Nat.even nxt = true /\ sl_owner c1 = Some t /\
      c2 = mkSLUL (sl_mem c1) (lock_write (sl_lock c1) h nxt (own + 1)%nat)
             (fun t' => view_advance (sl_view c1 t') h) None.
  Proof. intros Hs. inversion Hs; subst; inv_existT. do 3 eexists. eauto 7. Qed.

  Lemma get_res_inv t k c1 c2 :
    StepSeqLockUL {| te_tid := t; te_ev := ResEv get_ticket k |} c1 c2 ->
    exists h nxt, (forall t0, Pos.lt (H_bar c1 t0) h) /\ sl_lock c1 h = (nxt, k) /\
      c2 = mkSLUL (sl_mem c1) (sl_lock c1)
             (upd_tid_view (sl_view c1) t (view_advance (sl_view c1 t) h)) (sl_owner c1).
  Proof.
    intros Hs. remember (Build_ThreadEvent t (ResEv get_ticket k)) as ev eqn:Hev.
    destruct Hs; inversion Hev; subst;
      pose proof (f_equal (fun e => ret_nat (te_ev e)) Hev) as Hb; simpl in Hb;
      injection Hb as Hb; subst; eauto.
  Qed.

  Lemma test_res_inv t n b c1 c2 :
    StepSeqLockUL {| te_tid := t; te_ev := ResEv (test_ticket n) b |} c1 c2 ->
    exists h k, (forall t0, Pos.lt (H_bar c1 t0) h) /\ sl_lock c1 h = (n, k) /\
      b = orb (Nat.odd n) (negb (Nat.eqb k n)) /\
      c2 = mkSLUL (sl_mem c1) (sl_lock c1)
             (upd_tid_view (sl_view c1) t (view_advance (sl_view c1 t) h)) (sl_owner c1).
  Proof.
    intros Hs. remember (Build_ThreadEvent t (ResEv (test_ticket n) b)) as ev eqn:Hev.
    destruct Hs; inversion Hev; subst;
      pose proof (f_equal (fun e => ret_bool (te_ev e)) Hev) as Hb; simpl in Hb;
      injection Hb as Hb; subst; do 2 eexists; repeat split; eauto.
  Qed.

  (** ** Updates of the lifted state *)

  Lemma own_retro v t l h t' a :
    own (upd_retro SLP v t (rd l) h) t' a =
    if Pos.eqb t t' then Pos.max h (own v t' a) else own v t' a.
  Proof.
    unfold own, upd_retro, push_past. simpl. destruct (Pos.eqb t t'); reflexivity.
  Qed.

  Lemma own_app v t m h st t' a :
    vl_sync SLP m = false -> Inv SLP v -> Pos.lt (vs_hor SLP v) h ->
    own (upd_app SLP v t m h st) t' a =
    if Pos.eqb t t' && touches m a then h else own v t' a.
  Proof.
    intros Hy HI Hh. pose proof (own_le_hor v t' a HI) as Hle.
    unfold own, upd_app, push_past in *. simpl in Hy |- *. rewrite Hy.
    destruct (Pos.eqb t t') eqn:Ht; simpl; [|reflexivity].
    destruct (touches m a); simpl; [lia | reflexivity].
  Qed.

  Lemma own_sync v t m h st t' a :
    vl_sync SLP m = true -> Inv SLP v -> Pos.lt (vs_hor SLP v) h ->
    own (upd_app SLP v t m h st) t' a = h.
  Proof.
    intros Hy HI Hh. unfold own, upd_app. simpl in Hy |- *. rewrite Hy.
    apply Pos.le_antisym; [|apply fold_max_ge].
    apply fold_max_le; [apply Pos.le_refl|].
    intros x Hx. apply in_map_iff in Hx as ([o h'] & <- & Hin). apply filter_In in Hin as [Hin _].
    unfold push_past in Hin. simpl.
    destruct (Pos.eqb t t'); [destruct Hin as [Hin | Hin]|].
    - injection Hin as _ <-. apply Pos.le_refl.
    - pose proof (inv_past _ _ HI _ _ _ Hin). lia.
    - pose proof (inv_past _ _ HI _ _ _ Hin). lia.
  Qed.

  Lemma dep_ok_hor v t m h : Inv SLP v -> Pos.lt (vs_hor SLP v) h -> dep_ok SLP v t m h.
  Proof. intros HI Hh o h' Hin _. pose proof (inv_past _ _ HI _ _ _ Hin). lia. Qed.

  Lemma tl_write_same v h h' :
    Inv SLP v -> Pos.lt (vs_hor SLP v) h ->
    tl_write SLP (vs_tl SLP v) h (vs_tl SLP v h) h' = vs_tl SLP v h'.
  Proof.
    intros HI Hh. unfold tl_write. destruct (Pos.leb h h') eqn:Hle; [|reflexivity].
    apply Pos.leb_le in Hle. rewrite !(tl_above v) by (try exact HI; lia). reflexivity.
  Qed.

  Lemma cur_app v t m h st : Pos.lt (vs_hor SLP v) h -> cur SLP (upd_app SLP v t m h st) = st.
  Proof. intros _. unfold cur, upd_app, tl_write. simpl. rewrite Pos.leb_refl. reflexivity. Qed.

  Lemma HorW_app v t m h st : HorW (upd_app SLP v t m h st).
  Proof. right. exists t, m. simpl. unfold push_past. rewrite Pos.eqb_refl. left. reflexivity. Qed.

  (** The lock invariant after an appended operation. *)
  Lemma stale_keep c v t m h st :
    K c v -> Pos.lt (vs_hor SLP v) h ->
    s_lk st = s_lk (cur SLP v) -> s_own st = s_own (cur SLP v) ->
    (forall t', Pos.le (own v t' aloc_lk) (own (upd_app SLP v t m h st) t' aloc_lk)) ->
    forall t', (s_own st = None \/ s_own st = Some t') ->
    lk_ok (upd_app SLP v t m h st) t'.
  Proof.
    intros HK Hh Hlk Hown Hmono t' Ho h' Hle. rewrite (cur_app _ _ _ _ _ Hh).
    simpl. unfold tl_write. destruct (Pos.leb h h'); [reflexivity|].
    rewrite Hlk. rewrite Hown in Ho. apply (k_stale _ _ HK t' Ho). specialize (Hmono t'). lia.
  Qed.

  Lemma stale_top v t m h st t' :
    Pos.lt (vs_hor SLP v) h -> Pos.le h (own (upd_app SLP v t m h st) t' aloc_lk) ->
    lk_ok (upd_app SLP v t m h st) t'.
  Proof.
    intros Hh Hle h' Hle'. rewrite (cur_app _ _ _ _ _ Hh). simpl. unfold tl_write.
    destruct (Pos.leb h h') eqn:Hb; [reflexivity|]. apply Pos.leb_gt in Hb. lia.
  Qed.

  Lemma K_app c v t m r h st c' :
    K c v -> Pos.lt (vs_hor SLP v) h ->
    VStep SLP (Build_ThreadEvent t (ResEv m r)) v (upd_app SLP v t m h st) ->
    (forall l h', sl_mem c' l h' = sval (tl_write SLP (vs_tl SLP v) h st h') l) ->
    (forall h', sl_lock c' h' = s_lk (tl_write SLP (vs_tl SLP v) h st h')) ->
    sl_owner c' = s_own st ->
    (forall t' a, sl_view c' t' a = own (upd_app SLP v t m h st) t' a) ->
    (forall t', (s_own st = None \/ s_own st = Some t') -> lk_ok (upd_app SLP v t m h st) t') ->
    K c' (upd_app SLP v t m h st).
  Proof.
    intros HK Hh Hv Hmem Hlock Hown Hview Hst.
    constructor.
    - exact (VStep_Inv _ _ _ _ Hv (k_inv _ _ HK)).
    - apply HorW_app.
    - exact Hmem.
    - exact Hlock.
    - rewrite (cur_app _ _ _ _ _ Hh). exact Hown.
    - exact Hview.
    - rewrite (cur_app _ _ _ _ _ Hh). exact Hst.
  Qed.

  Lemma K_rd c v t l h :
    K c v -> Pos.lt (own v t (mem_to_all l)) h ->
    K (mkSLUL (sl_mem c) (sl_lock c)
         (upd_tid_view (sl_view c) t (view_advance (sl_view c t) h)) (sl_owner c))
      (upd_retro SLP v t (rd l) h).
  Proof.
    intros HK Hlt. pose proof (proj1 (own_lt _ _ _ _) Hlt) as [Hfl Hpast].
    pose proof (k_inv _ _ HK) as HI.
    assert (Hcur : cur SLP (upd_retro SLP v t (rd l) h) = cur SLP v).
    { unfold cur, upd_retro. simpl. apply (inv_const _ _ HI). lia. }
    assert (Hmono : forall t', Pos.le (own v t' aloc_lk) (own (upd_retro SLP v t (rd l) h) t' aloc_lk)).
    { intros t'. rewrite own_retro. destruct (Pos.eqb t t'); lia. }
    constructor.
    - eapply (VStep_Inv SLP); [|exact HI].
      refine (vstep_retro SLP t (rd l) (sval (vs_tl SLP v h) l : nat) h v _ _ eq_refl eq_refl Hfl _ _ eq_refl).
      + intros o h' Hin Hd. exact (Hpast _ _ Hin Hd).
      + simpl. auto.
    - unfold HorW; simpl. destruct (Pos.max_spec (vs_hor SLP v) h) as [[Hle ->] | [Hle ->]].
      + right. exists t, (rd l). unfold push_past. rewrite Pos.eqb_refl. left. reflexivity.
      + destruct (k_hw _ _ HK) as [Heq | (t' & o & Hin)]; [left; exact Heq|].
        right. exists t', o. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin.
    - exact (k_mem _ _ HK).
    - exact (k_lock _ _ HK).
    - rewrite Hcur. exact (k_owner _ _ HK).
    - intros t' a. simpl. rewrite own_retro. unfold upd_tid_view, view_advance.
      destruct (Pos.eqb t t') eqn:Ht.
      + apply Pos.eqb_eq in Ht. subst t'. rewrite (k_view _ _ HK). lia.
      + exact (k_view _ _ HK t' a).
    - rewrite Hcur. intros t' Ho h' Hle. rewrite Hcur. simpl.
      apply (k_stale _ _ HK t' Ho). specialize (Hmono t'). lia.
  Qed.

  (** ** One lemma per appended operation *)

  Lemma vs_wrt v t l w r h :
    Inv SLP v -> Pos.lt (vs_hor SLP v) h -> s_own (cur SLP v) = Some t ->
    VStep SLP (Build_ThreadEvent t (ResEv (wrt l w) r)) v
      (upd_app SLP v t (wrt l w) h (supd (vs_tl SLP v h) l w)).
  Proof.
    intros HI Hh Ho.
    refine (vstep_app SLP t (wrt l w) r h _ v _ _ eq_refl eq_refl Hh (dep_ok_hor _ _ _ _ HI Hh) _ eq_refl).
    simpl. split; [|reflexivity]. rewrite (tl_above v h HI) by lia. exact Ho.
  Qed.

  Lemma K_wrt c v t l w (r : unit) h :
    K c v -> Pos.lt (vs_hor SLP v) h -> s_own (cur SLP v) = Some t ->
    K (mkSLUL (mem_write (sl_mem c) l h w) (sl_lock c)
         (upd_tid_view (sl_view c) t (view_set (sl_view c t) (mem_to_all l) h)) (sl_owner c))
      (upd_app SLP v t (wrt l w) h (supd (vs_tl SLP v h) l w)).
  Proof.
    intros HK Hh Ho. pose proof (k_inv _ _ HK) as HI.
    assert (Hc : vs_tl SLP v h = cur SLP v) by (apply tl_above; [exact HI | lia]).
    apply (K_app c v t (wrt l w) r h); [exact HK | exact Hh | apply vs_wrt; assumption | | | | |].
    - intros l' h'. cbn [sl_mem]. unfold mem_write, tl_write. rewrite (k_mem _ _ HK).
      destruct (Pos.leb h h') eqn:Hle; [apply Pos.leb_le in Hle | rewrite andb_false_r; reflexivity].
      rewrite (tl_above v h') by (exact HI || lia). rewrite Hc.
      destruct l, l'; reflexivity.
    - intros h'. cbn [sl_lock]. unfold tl_write. rewrite (k_lock _ _ HK).
      destruct (Pos.leb h h') eqn:Hle; [apply Pos.leb_le in Hle | reflexivity].
      rewrite (tl_above v h') by (exact HI || lia). rewrite Hc. destruct l; reflexivity.
    - cbn [sl_owner]. rewrite (k_owner _ _ HK), Hc. destruct l; reflexivity.
    - intros t' a. cbn [sl_view]. rewrite own_app by (reflexivity || exact HI || exact Hh).
      unfold upd_tid_view, view_set. cbn [touches].
      destruct (Pos.eqb t t') eqn:Ht; cbn [andb].
      + apply Pos.eqb_eq in Ht. subst t'.
        destruct (AllLoc_eqb (mem_to_all l) a); [reflexivity | apply (k_view _ _ HK)].
      + apply (k_view _ _ HK).
    - apply (stale_keep c v t (wrt l w) h _ HK Hh).
      + rewrite Hc. destruct l; reflexivity.
      + rewrite Hc. destruct l; reflexivity.
      + intros t'. rewrite own_app by (reflexivity || exact HI || exact Hh).
        pose proof (own_le_hor v t' aloc_lk HI).
        destruct (Pos.eqb t t' && touches (wrt l w) aloc_lk); lia.
  Qed.

  Lemma vs_acq v t r h nxt ow :
    Inv SLP v -> Pos.lt (vs_hor SLP v) h ->
    s_lk (cur SLP v) = (nxt, ow) -> nxt = ow -> Nat.even nxt = true -> s_own (cur SLP v) = None ->
    VStep SLP (Build_ThreadEvent t (ResEv acq r)) v
      (upd_app SLP v t acq h (slock (vs_tl SLP v h) ((nxt + 2)%nat, (ow + 1)%nat) (Some t))).
  Proof.
    intros HI Hh Hl Hn He Ho.
    refine (vstep_app SLP t acq r h _ v _ _ eq_refl eq_refl Hh (dep_ok_hor _ _ _ _ HI Hh) _ eq_refl).
    simpl. rewrite (tl_above v h HI) by lia. exists nxt, ow. auto.
  Qed.

  Lemma K_acq c v t (r : unit) h nxt ow :
    K c v -> Pos.lt (vs_hor SLP v) h ->
    s_lk (cur SLP v) = (nxt, ow) -> nxt = ow -> Nat.even nxt = true -> s_own (cur SLP v) = None ->
    K (mkSLUL (sl_mem c) (lock_write (sl_lock c) h (nxt + 2)%nat (ow + 1)%nat)
         (upd_tid_view (sl_view c) t (view_set (sl_view c t) aloc_lk h)) (Some t))
      (upd_app SLP v t acq h (slock (vs_tl SLP v h) ((nxt + 2)%nat, (ow + 1)%nat) (Some t))).
  Proof.
    intros HK Hh Hl Hn He Ho. pose proof (k_inv _ _ HK) as HI.
    assert (Hc : vs_tl SLP v h = cur SLP v) by (apply tl_above; [exact HI | lia]).
    apply (K_app c v t acq r h); [exact HK | exact Hh | apply vs_acq; assumption | | | | |].
    - intros l h'. cbn [sl_mem]. unfold tl_write. rewrite (k_mem _ _ HK).
      destruct (Pos.leb h h') eqn:Hle; [apply Pos.leb_le in Hle | reflexivity].
      rewrite (tl_above v h') by (exact HI || lia). rewrite Hc. destruct l; reflexivity.
    - intros h'. cbn [sl_lock]. unfold lock_write, tl_write. rewrite (k_lock _ _ HK).
      destruct (Pos.leb h h'); reflexivity.
    - reflexivity.
    - intros t' a. cbn [sl_view]. rewrite own_app by (reflexivity || exact HI || exact Hh).
      unfold upd_tid_view, view_set. cbn [touches].
      destruct (Pos.eqb t t') eqn:Ht; cbn [andb].
      + apply Pos.eqb_eq in Ht. subst t'.
        destruct (AllLoc_eqb aloc_lk a); [reflexivity | apply (k_view _ _ HK)].
      + apply (k_view _ _ HK).
    - intros t' [Hs | Hs]; [discriminate|]. injection Hs as <-.
      apply stale_top; [exact Hh|]. rewrite own_app by (reflexivity || exact HI || exact Hh).
      rewrite Pos.eqb_refl. simpl. lia.
  Qed.

  Lemma vs_rel v t r h nxt ow :
    Inv SLP v -> Pos.lt (vs_hor SLP v) h ->
    s_lk (cur SLP v) = (nxt, ow) -> nxt = (ow + 1)%nat -> Nat.even nxt = true ->
    s_own (cur SLP v) = Some t ->
    VStep SLP (Build_ThreadEvent t (ResEv rel r)) v
      (upd_app SLP v t rel h (slock (vs_tl SLP v h) (nxt, (ow + 1)%nat) None)).
  Proof.
    intros HI Hh Hl Hn He Ho.
    refine (vstep_app SLP t rel r h _ v _ _ eq_refl eq_refl Hh (dep_ok_hor _ _ _ _ HI Hh) _ eq_refl).
    simpl. rewrite (tl_above v h HI) by lia. exists nxt, ow. auto.
  Qed.

  Lemma K_rel c v t (r : unit) h nxt ow :
    K c v -> Pos.lt (vs_hor SLP v) h ->
    s_lk (cur SLP v) = (nxt, ow) -> nxt = (ow + 1)%nat -> Nat.even nxt = true ->
    s_own (cur SLP v) = Some t ->
    K (mkSLUL (sl_mem c) (lock_write (sl_lock c) h nxt (ow + 1)%nat)
         (fun t' => view_advance (sl_view c t') h) None)
      (upd_app SLP v t rel h (slock (vs_tl SLP v h) (nxt, (ow + 1)%nat) None)).
  Proof.
    intros HK Hh Hl Hn He Ho. pose proof (k_inv _ _ HK) as HI.
    assert (Hc : vs_tl SLP v h = cur SLP v) by (apply tl_above; [exact HI | lia]).
    apply (K_app c v t rel r h); [exact HK | exact Hh | apply vs_rel; assumption | | | | |].
    - intros l h'. cbn [sl_mem]. unfold tl_write. rewrite (k_mem _ _ HK).
      destruct (Pos.leb h h') eqn:Hle; [apply Pos.leb_le in Hle | reflexivity].
      rewrite (tl_above v h') by (exact HI || lia). rewrite Hc. destruct l; reflexivity.
    - intros h'. cbn [sl_lock]. unfold lock_write, tl_write. rewrite (k_lock _ _ HK).
      destruct (Pos.leb h h'); reflexivity.
    - reflexivity.
    - intros t' a. cbn [sl_view]. rewrite own_sync by (reflexivity || exact HI || exact Hh).
      unfold view_advance. rewrite (k_view _ _ HK). pose proof (own_le_hor v t' a HI). lia.
    - intros t' _. apply stale_top; [exact Hh|].
      rewrite own_sync by (reflexivity || exact HI || exact Hh). lia.
  Qed.

  (** [get_ticket] and [test_ticket]: appended, state unchanged, every
      location advanced. *)
  Lemma K_look c v t m r h :
    K c v -> Pos.lt (vs_hor SLP v) h ->
    vl_sync SLP m = false -> (forall a, touches m a = true) ->
    VStep SLP (Build_ThreadEvent t (ResEv m r)) v (upd_app SLP v t m h (vs_tl SLP v h)) ->
    K (mkSLUL (sl_mem c) (sl_lock c)
         (upd_tid_view (sl_view c) t (view_advance (sl_view c t) h)) (sl_owner c))
      (upd_app SLP v t m h (vs_tl SLP v h)).
  Proof.
    intros HK Hh Hy Hall Hv. pose proof (k_inv _ _ HK) as HI.
    assert (Hc : vs_tl SLP v h = cur SLP v) by (apply tl_above; [exact HI | lia]).
    apply (K_app c v t m r h); [exact HK | exact Hh | exact Hv | | | | |].
    - intros l h'. cbn [sl_mem]. rewrite tl_write_same by assumption. apply (k_mem _ _ HK).
    - intros h'. cbn [sl_lock]. rewrite tl_write_same by assumption. apply (k_lock _ _ HK).
    - cbn [sl_owner]. rewrite (k_owner _ _ HK), Hc. reflexivity.
    - intros t' a. cbn [sl_view]. rewrite own_app by assumption.
      unfold upd_tid_view, view_advance. rewrite Hall.
      destruct (Pos.eqb t t') eqn:Ht; cbn [andb].
      + apply Pos.eqb_eq in Ht. subst t'. rewrite (k_view _ _ HK).
        pose proof (own_le_hor v t a HI). lia.
      + apply (k_view _ _ HK).
    - apply (stale_keep c v t m h _ HK Hh); [rewrite Hc; reflexivity | rewrite Hc; reflexivity |].
      intros t'. rewrite own_app by assumption. pose proof (own_le_hor v t' aloc_lk HI).
      destruct (Pos.eqb t t' && touches m aloc_lk); lia.
  Qed.

  Lemma vs_get v t k h nxt :
    Inv SLP v -> Pos.lt (vs_hor SLP v) h -> s_lk (cur SLP v) = (nxt, k) ->
    VStep SLP (Build_ThreadEvent t (ResEv get_ticket k)) v
      (upd_app SLP v t get_ticket h (vs_tl SLP v h)).
  Proof.
    intros HI Hh Hl.
    refine (vstep_app SLP t get_ticket k h _ v _ _ eq_refl eq_refl Hh (dep_ok_hor _ _ _ _ HI Hh) _ eq_refl).
    simpl. rewrite (tl_above v h HI) by lia. exists nxt. auto.
  Qed.

  Lemma vs_test v t n b h k :
    Inv SLP v -> Pos.lt (vs_hor SLP v) h -> s_lk (cur SLP v) = (n, k) ->
    b = orb (Nat.odd n) (negb (Nat.eqb k n)) ->
    VStep SLP (Build_ThreadEvent t (ResEv (test_ticket n) b)) v
      (upd_app SLP v t (test_ticket n) h (vs_tl SLP v h)).
  Proof.
    intros HI Hh Hl Hb.
    refine (vstep_app SLP t (test_ticket n) b h _ v _ _ eq_refl eq_refl Hh (dep_ok_hor _ _ _ _ HI Hh) _ eq_refl).
    simpl. rewrite (tl_above v h HI) by lia. exists k. auto.
  Qed.

  Lemma vs_rd v t l h :
    Pos.lt (own v t (mem_to_all l)) h ->
    VStep SLP (Build_ThreadEvent t (ResEv (rd l) (sval (vs_tl SLP v h) l))) v (upd_retro SLP v t (rd l) h).
  Proof.
    intros Hlt. pose proof (proj1 (own_lt _ _ _ _) Hlt) as [Hfl Hpast].
    refine (vstep_retro SLP t (rd l) (sval (vs_tl SLP v h) l : nat) h v _ _ eq_refl eq_refl Hfl _ _ eq_refl).
    - intros o h' Hin Hd. exact (Hpast _ _ Hin Hd).
    - simpl. auto.
  Qed.

  (** ** VSeqLockUL is simulated by the lifted object *)

  Lemma tso_sim_by_vl : UnderlayRefinement.UnderlaySim (VL SLP) VSeqLockUL CR.
  Proof.
    constructor.
    - intros ev x x' y HR Hs. destruct Hs as [t op c1 c2 Hs | t op r c1 c2 Hs].
      + apply inv_step_eq in Hs. subst c2.
        destruct y as [v | v t' op']; [|contradiction].
        exists (Pending v t op). split; [|simpl; auto].
        constructor. econstructor. reflexivity.
      + destruct y as [v | v t' op']; [contradiction|].
        destruct HR as (HK & <- & <-). pose proof (k_inv _ _ HK) as HI.
        destruct op as [l w | l | | | | n].
        * destruct (wrt_res_inv _ _ _ _ _ _ Hs) as (Hown & h & Hall & ->).
          apply (K_hbar _ _ _ HK) in Hall. rewrite (k_owner _ _ HK) in Hown.
          exists (Idle (upd_app SLP v t (wrt l w) h (supd (vs_tl SLP v h) l w))). split.
          -- constructor. apply vs_wrt; assumption.
          -- exact (K_wrt c1 v t l w r h HK Hall Hown).
        * destruct (rd_res_inv _ _ _ _ _ Hs) as (h & Hlt & -> & ->).
          rewrite (k_view _ _ HK) in Hlt.
          exists (Idle (upd_retro SLP v t (rd l) h)). split.
          -- constructor. rewrite (k_mem _ _ HK). apply vs_rd. exact Hlt.
          -- exact (K_rd _ _ _ _ _ HK Hlt).
        * destruct (acq_res_inv _ _ _ _ Hs) as (h & nxt & ow & Hall & Hlk & Hn & He & Hown & ->).
          apply (K_hbar _ _ _ HK) in Hall. rewrite (k_owner _ _ HK) in Hown.
          rewrite (K_lock_own _ _ t HK (or_introl Hown)) in Hlk.
          exists (Idle (upd_app SLP v t acq h (slock (vs_tl SLP v h) ((nxt + 2)%nat, (ow + 1)%nat) (Some t)))).
          split.
          -- constructor. apply vs_acq; assumption.
          -- exact (K_acq c1 v t r h nxt ow HK Hall Hlk Hn He Hown).
        * destruct (rel_res_inv _ _ _ _ Hs) as (h & nxt & ow & Hall & Hlk & Hn & He & Hown & ->).
          apply (K_hbar _ _ _ HK) in Hall. rewrite (k_owner _ _ HK) in Hown.
          rewrite (K_lock_own _ _ t HK (or_intror Hown)) in Hlk.
          exists (Idle (upd_app SLP v t rel h (slock (vs_tl SLP v h) (nxt, (ow + 1)%nat) None))).
          split.
          -- constructor. apply vs_rel; assumption.
          -- exact (K_rel c1 v t r h nxt ow HK Hall Hlk Hn He Hown).
        * destruct (get_res_inv _ _ _ _ Hs) as (h & nxt & Hall & Hlk & ->).
          apply (K_hbar _ _ _ HK) in Hall.
          rewrite (k_lock _ _ HK), (tl_above v h HI) in Hlk by lia.
          exists (Idle (upd_app SLP v t get_ticket h (vs_tl SLP v h))).
          assert (Hv : VStep SLP (Build_ThreadEvent t (ResEv get_ticket r)) v
                         (upd_app SLP v t get_ticket h (vs_tl SLP v h)))
            by (eapply vs_get; eassumption).
          split; [constructor; exact Hv|].
          apply (K_look c1 v t get_ticket r h HK Hall eq_refl (fun _ => eq_refl) Hv).
        * destruct (test_res_inv _ _ _ _ _ Hs) as (h & k & Hall & Hlk & Hb & ->).
          apply (K_hbar _ _ _ HK) in Hall.
          rewrite (k_lock _ _ HK), (tl_above v h HI) in Hlk by lia.
          exists (Idle (upd_app SLP v t (test_ticket n) h (vs_tl SLP v h))).
          assert (Hv : VStep SLP (Build_ThreadEvent t (ResEv (test_ticket n) r)) v
                         (upd_app SLP v t (test_ticket n) h (vs_tl SLP v h)))
            by (eapply vs_test; eassumption).
          split; [constructor; exact Hv|].
          apply (K_look c1 v t (test_ticket n) r h HK Hall eq_refl (fun _ => eq_refl) Hv).
    - intros ev x y HR He. destruct He.
  Qed.

  (** ** The lifted object is simulated by VSeqLockUL *)

  Lemma vl_sim_by_tso : UnderlayRefinement.UnderlaySim VSeqLockUL (VL SLP) (fun y x => CR x y).
  Proof.
    constructor.
    - intros ev y y' x HR Hs. destruct Hs as [t op v1 v2 Hs | t op r v1 v2 Hs].
      + apply (vstep_inv_inv SLP) in Hs. subst v2.
        destruct x as [c | c t' op']; [|contradiction].
        exists (Pending c t op). split; [|simpl; auto].
        constructor. destruct op; constructor.
      + destruct x as [c | c t' op']; [contradiction|].
        destruct HR as (HK & -> & ->). pose proof (k_inv _ _ HK) as HI.
        destruct (ViewLiftAdequacy.vstep_rstep SLP v1 t op r v2 HI Hs) as (h & Hfl & Hdep & Hcase).
        cbn [ViewLiftAdequacy.e_t ViewLiftAdequacy.e_m ViewLiftAdequacy.e_r ViewLiftAdequacy.e_h] in Hfl, Hdep, Hcase.
        destruct Hcase as [(Hr & Hspec & ->) | (Hr & Hh & st & Hspec & ->)].
        * (* retroactive: only [rd] *)
          destruct op as [l w | l | | | | n]; try discriminate.
          destruct Hspec as [-> _].
          assert (Hlt : Pos.lt (own v1 t (mem_to_all l)) h).
          { apply own_lt. split; [exact Hfl|]. intros o h' Hin Ht. exact (Hdep o h' Hin Ht). }
          exists (Idle (mkSLUL (sl_mem c) (sl_lock c)
                          (upd_tid_view (sl_view c) t (view_advance (sl_view c t) h)) (sl_owner c))).
          split.
          -- constructor. eapply step_rd_res; [rewrite (k_view _ _ HK); exact Hlt | | reflexivity].
             rewrite (k_mem _ _ HK). reflexivity.
          -- exact (K_rd _ _ _ _ _ HK Hlt).
        * assert (Hall : forall t0, Pos.lt (H_bar c t0) h) by (apply (K_hbar _ _ _ HK); exact Hh).
          assert (Hc : vs_tl SLP v1 h = cur SLP v1) by (apply tl_above; [exact HI | lia]).
          destruct op as [l w | l | | | | n]; try discriminate; simpl in Hspec.
          -- destruct Hspec as (Hown & ->). destruct r. rewrite Hc in Hown.
             exists (Idle (mkSLUL (mem_write (sl_mem c) l h w) (sl_lock c)
                             (upd_tid_view (sl_view c) t (view_set (sl_view c t) (mem_to_all l) h))
                             (sl_owner c))).
             split.
             ++ constructor. eapply step_wrt_res; [rewrite (k_owner _ _ HK); exact Hown | exact Hall | reflexivity].
             ++ exact (K_wrt c v1 t l w tt h HK Hh Hown).
          -- destruct Hspec as (nxt & ow & Hlk & Hn & He & Hown & ->). destruct r.
             rewrite Hc in Hlk, Hown.
             exists (Idle (mkSLUL (sl_mem c) (lock_write (sl_lock c) h (nxt + 2)%nat (ow + 1)%nat)
                             (upd_tid_view (sl_view c) t (view_set (sl_view c t) aloc_lk h)) (Some t))).
             split.
             ++ constructor. eapply step_acq_res; [exact Hall | | exact Hn | exact He | | reflexivity].
                ** rewrite (K_lock_own _ _ t HK (or_introl Hown)). exact Hlk.
                ** rewrite (k_owner _ _ HK). exact Hown.
             ++ exact (K_acq c v1 t tt h nxt ow HK Hh Hlk Hn He Hown).
          -- destruct Hspec as (nxt & ow & Hlk & Hn & He & Hown & ->). destruct r.
             rewrite Hc in Hlk, Hown.
             exists (Idle (mkSLUL (sl_mem c) (lock_write (sl_lock c) h nxt (ow + 1)%nat)
                             (fun t' => view_advance (sl_view c t') h) None)).
             split.
             ++ constructor. eapply step_rel_res; [exact Hall | | exact Hn | exact He | | reflexivity].
                ** rewrite (K_lock_own _ _ t HK (or_intror Hown)). exact Hlk.
                ** rewrite (k_owner _ _ HK). exact Hown.
             ++ exact (K_rel c v1 t tt h nxt ow HK Hh Hlk Hn He Hown).
          -- destruct Hspec as (nxt & Hlk & ->).
             exists (Idle (mkSLUL (sl_mem c) (sl_lock c)
                             (upd_tid_view (sl_view c) t (view_advance (sl_view c t) h)) (sl_owner c))).
             split.
             ++ constructor. eapply step_get_ticket_res; [exact Hall | | reflexivity].
                rewrite (k_lock _ _ HK). exact Hlk.
             ++ apply (K_look c v1 t get_ticket r h HK Hh eq_refl (fun _ => eq_refl)).
                rewrite Hc in Hlk. eapply vs_get; eassumption.
          -- destruct Hspec as (k & Hlk & Hb & ->).
             exists (Idle (mkSLUL (sl_mem c) (sl_lock c)
                             (upd_tid_view (sl_view c) t (view_advance (sl_view c t) h)) (sl_owner c))).
             split.
             ++ constructor. eapply step_test_ticket_res; [exact Hall | | exact Hb | reflexivity].
                rewrite (k_lock _ _ HK). exact Hlk.
             ++ apply (K_look c v1 t (test_ticket n) r h HK Hh eq_refl (fun _ => eq_refl)).
                rewrite Hc in Hlk. eapply vs_test; eassumption.
    - intros ev y x HR He. destruct He as [ev v Herr].
      unfold err_at in Herr. destruct (te_ev ev); destruct Herr.
  Qed.

  (** ** Transfer of [cal] proofs *)

  Import TPSimulation.

  Definition EVL : layer_interface := {|
    li_sig := ESeqLockUL;
    li_lts := VL SLP;
    li_init := Idle (vinit SLP sl_init);
  |}.

  Section Transfer.
    Context {F : Op.t} (VF : @LTS F) (M : Lang.ModuleImpl ESeqLockUL F).

    Theorem seqlock_tso_to_vl ρ0 :
      cal (VE := VSeqLockUL) (VF := VF) M (Idle SeqLockImpl.initE) ρ0 ->
      cal (VE := VL SLP) (VF := VF) M (Idle (vinit SLP sl_init)) ρ0.
    Proof.
      intros Hc.
      exact (UnderlayRefinement.cal_refine VSeqLockUL (VL SLP) VF _ vl_sim_by_tso M
               (Idle (vinit SLP sl_init)) (Idle SeqLockImpl.initE) ρ0 K_init Hc).
    Qed.

    Theorem seqlock_vl_to_tso ρ0 :
      cal (VE := VL SLP) (VF := VF) M (Idle (vinit SLP sl_init)) ρ0 ->
      cal (VE := VSeqLockUL) (VF := VF) M (Idle SeqLockImpl.initE) ρ0.
    Proof.
      intros Hc.
      exact (UnderlayRefinement.cal_refine (VL SLP) VSeqLockUL VF CR tso_sim_by_vl M
               (Idle SeqLockImpl.initE) (Idle (vinit SLP sl_init)) ρ0 K_init Hc).
    Qed.
  End Transfer.

  (** The SeqLock of [SeqLockTSO.v] over the derived underlay. *)
  Program Definition Mseqlock_vl : layer_implementation EVL SeqLockImpl.F := {|
    li_impl := li_impl SeqLockImpl.Mseqlock
  |}.
  Next Obligation.
    apply seqlock_tso_to_vl. exact (li_correct SeqLockImpl.Mseqlock).
  Qed.

  (** ** The object is not SC: a stale read *)

  Definition t1 : tid := 1%positive.
  Definition t2 : tid := 2%positive.

  (** The owner takes the lock and writes 1 to [x]; afterwards another
      thread reads [x] and gets the initial 0. *)
  Definition stale_trace : list (@ThreadEvent ESeqLockUL) := [
    Build_ThreadEvent t1 (InvEv acq);
    Build_ThreadEvent t1 (ResEv acq tt);
    Build_ThreadEvent t1 (InvEv (wrt loc_x 1));
    Build_ThreadEvent t1 (ResEv (wrt loc_x 1) tt);
    Build_ThreadEvent t2 (InvEv (rd loc_x));
    Build_ThreadEvent t2 (ResEv (rd loc_x) (O : nat))
  ].

  Lemma vl_stale_read :
    exists s', UnderlayRefinement.Reach (VL SLP) (Idle (vinit SLP sl_init)) stale_trace s'.
  Proof.
    set (v0 := vinit SLP sl_init).
    assert (HI0 : Inv SLP v0) by apply Inv_init.
    pose proof (vs_acq v0 t1 tt 2 O O HI0 ltac:(reflexivity) eq_refl eq_refl eq_refl eq_refl) as H1.
    set (v1 := upd_app SLP v0 t1 acq 2 _) in H1.
    pose proof (VStep_Inv _ _ _ _ H1 HI0) as HI1.
    pose proof (vs_wrt v1 t1 loc_x 1 tt 3 HI1 ltac:(reflexivity) eq_refl) as H2.
    set (v2 := upd_app SLP v1 t1 (wrt loc_x 1) 3 _) in H2.
    pose proof (vs_rd v2 t2 loc_x 2 ltac:(reflexivity)) as H3.
    eexists. unfold stale_trace.
    econstructor; [constructor; econstructor; reflexivity|].
    econstructor; [constructor; exact H1|].
    econstructor; [constructor; econstructor; reflexivity|].
    econstructor; [constructor; exact H2|].
    econstructor; [constructor; econstructor; reflexivity|].
    econstructor; [constructor; exact H3|].
    constructor.
  Qed.

  Lemma astep_inv {E : Op.t} {S : Type} (St : @ThreadEvent E -> S -> S -> Prop) ev x x' :
    AStep St ev x x' ->
    match te_ev ev with
    | InvEv op => exists s1 s2, x = Idle s1 /\ x' = Pending s2 (te_tid ev) op /\ St ev s1 s2
    | ResEv op r => exists s1 s2, x = Pending s1 (te_tid ev) op /\ x' = Idle s2 /\ St ev s1 s2
    end.
  Proof. intros H. destruct H; simpl; eauto 6. Qed.

  Lemma sc_no_stale_read :
    ~ exists s', UnderlayRefinement.Reach (SC SLP) (Idle sl_init) stale_trace s'.
  Proof.
    intros (s' & Hr). unfold stale_trace in Hr.
    inversion Hr as [|x0 ev1 x1 evs1 y1 Hs1 Hr1]; subst; clear Hr.
    apply astep_inv in Hs1 as (a1 & b1 & Ha1 & -> & Hs1). injection Ha1 as <-.
    apply (scstep_inv_inv SLP) in Hs1. subst b1.
    inversion Hr1 as [|x0 ev2 x2 evs2 y2 Hs2 Hr2]; subst; clear Hr1.
    apply astep_inv in Hs2 as (a2 & b2 & Ha2 & -> & Hs2). injection Ha2 as <-.
    apply (scstep_res_spec SLP) in Hs2. destruct Hs2 as (nxt & ow & _ & _ & _ & _ & ->).
    inversion Hr2 as [|x0 ev3 x3 evs3 y3 Hs3 Hr3]; subst; clear Hr2.
    apply astep_inv in Hs3 as (a3 & b3 & Ha3 & -> & Hs3). injection Ha3 as <-.
    apply (scstep_inv_inv SLP) in Hs3. subst b3.
    inversion Hr3 as [|x0 ev4 x4 evs4 y4 Hs4 Hr4]; subst; clear Hr3.
    apply astep_inv in Hs4 as (a4 & b4 & Ha4 & -> & Hs4). injection Ha4 as <-.
    apply (scstep_res_spec SLP) in Hs4. destruct Hs4 as (_ & ->).
    inversion Hr4 as [|x0 ev5 x5 evs5 y5 Hs5 Hr5]; subst; clear Hr4.
    apply astep_inv in Hs5 as (a5 & b5 & Ha5 & -> & Hs5). injection Ha5 as <-.
    apply (scstep_inv_inv SLP) in Hs5. subst b5.
    inversion Hr5 as [|x0 ev6 x6 evs6 y6 Hs6 Hr6]; subst; clear Hr5.
    apply astep_inv in Hs6 as (a6 & b6 & Ha6 & -> & Hs6). injection Ha6 as <-.
    apply (scstep_res_spec SLP) in Hs6. destruct Hs6 as (Hv & _).
    discriminate Hv.
  Qed.

  (** By the bisimulation, the hand-written specification has the same
      stale read. *)
  Theorem tso_stale_read :
    exists c', UnderlayRefinement.Reach VSeqLockUL (Idle SeqLockImpl.initE) stale_trace c'.
  Proof.
    destruct vl_stale_read as (s' & Hr).
    destruct (UnderlayRefinement.us_reach _ _ _ vl_sim_by_tso (Idle (vinit SLP sl_init)) (Idle SeqLockImpl.initE) _ _ K_init Hr) as (c' & Hc & _).
    exists c'. exact Hc.
  Qed.

  (** ** The run of the stale read and its canonical trace

      The write is timestamped 3 and the later read 2.  So the canonical
      trace of [ViewLiftAdequacy] delays the write's response to the end,
      after the read, and the trace is relaxed linearizable with the
      witness [acq; rd x = 0; wrt x 1]. *)

  Definition stale_R : list (@ViewLiftAdequacy.Ent ESeqLockUL) := [
    ViewLiftAdequacy.mkEnt t1 acq tt 2;
    ViewLiftAdequacy.mkEnt t1 (wrt loc_x 1) tt 3;
    ViewLiftAdequacy.mkEnt t2 (rd loc_x) (O : nat) 2
  ].

  Lemma stale_run : exists s, ViewLiftAdequacy.Run SLP sl_init stale_R s.
  Proof.
    set (v0 := vinit SLP sl_init).
    assert (HI0 : Inv SLP v0) by apply Inv_init.
    pose proof (vs_acq v0 t1 tt 2 O O HI0 ltac:(reflexivity) eq_refl eq_refl eq_refl eq_refl) as H1.
    set (v1 := upd_app SLP v0 t1 acq 2 _) in H1.
    pose proof (VStep_Inv _ _ _ _ H1 HI0) as HI1.
    pose proof (vs_wrt v1 t1 loc_x 1 tt 3 HI1 ltac:(reflexivity) eq_refl) as H2.
    set (v2 := upd_app SLP v1 t1 (wrt loc_x 1) 3 _) in H2.
    pose proof (vs_rd v2 t2 loc_x 2 ltac:(reflexivity)) as H3.
    pose proof (VStep_Inv _ _ _ _ H2 HI1) as HI2.
    destruct (ViewLiftAdequacy.vstep_rstep SLP _ _ _ _ _ HI0 H1) as (h1 & R1).
    destruct (ViewLiftAdequacy.vstep_rstep SLP _ _ _ _ _ HI1 H2) as (h2 & R2).
    destruct (ViewLiftAdequacy.vstep_rstep SLP _ _ _ _ _ HI2 H3) as (h3 & R3).
    (* The timestamps of the steps are the ones chosen above. *)
    assert (Hh1 : h1 = 2%positive).
    { destruct R1 as (_ & _ & [(Hr & _) | (_ & _ & st & _ & Heq)]); [discriminate|].
      apply (f_equal (vs_hor SLP)) in Heq. simpl in Heq. symmetry. exact Heq. }
    assert (Hh2 : h2 = 3%positive).
    { destruct R2 as (_ & _ & [(Hr & _) | (_ & _ & st & _ & Heq)]); [discriminate|].
      apply (f_equal (vs_hor SLP)) in Heq. simpl in Heq. symmetry. exact Heq. }
    assert (Hh3 : h3 = 2%positive).
    { destruct R3 as (_ & _ & [(_ & _ & Heq) | (Hr & _)]); [|discriminate].
      apply (f_equal (fun s => vs_past SLP s t2)) in Heq. simpl in Heq.
      unfold push_past in Heq. simpl in Heq. injection Heq as Heq. symmetry. exact Heq. }
    subst h1 h2 h3.
    eexists. change stale_R with ((([] ++ [ViewLiftAdequacy.mkEnt t1 acq tt 2])
                                    ++ [ViewLiftAdequacy.mkEnt t1 (wrt loc_x 1) tt 3])
                                    ++ [ViewLiftAdequacy.mkEnt t2 (rd loc_x) (O : nat) 2]).
    eapply ViewLiftAdequacy.run_snoc; [|exact R3].
    eapply ViewLiftAdequacy.run_snoc; [|exact R2].
    eapply ViewLiftAdequacy.run_snoc; [|exact R1].
    constructor.
  Qed.

  Lemma stale_canon :
    ViewLiftAdequacy.canon stale_R =
      [(0%nat, false); (0%nat, true); (1%nat, false); (2%nat, false); (2%nat, true); (1%nat, true)].
  Proof. reflexivity. Qed.

  Theorem stale_rel_lin :
    RelaxedTraceLin.rel_lin (ViewLiftAdequacy.csel SLP stale_R) (ViewLiftAdequacy.canon stale_R)
      (RelaxedSig.semi_independent (ViewLiftAdequacy.RS SLP)) (ViewLiftAdequacy.nu_P SLP sl_init).
  Proof.
    destruct stale_run as (s & HR). exact (ViewLiftAdequacy.canon_rel_lin SLP sl_init stale_R s HR).
  Qed.
End ViewLiftSeqLock.
