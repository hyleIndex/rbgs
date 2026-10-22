(** * The ticket lock on TSO memory, against the plain presentation of the lock

    [M_TL] implements [TLC] (the ticket lock with its data cells) with
    reads, writes and fetch-and-add on [MemHW].

    - [tacq]: [k <- faa(l_nxt, 2)]; read [l_own] until it is [k]; write
      [l_own := k + 1].
    - [trel]: [v <- l_own]; [l_own := v + 1].  A plain read and write,
      not an atomic read-modify-write: while the lock is held, only the
      holder writes [l_own].
    - [tgt]: read [l_own].  [tdr l], [tdw l a]: read or write the cell.

    Every operation of [TLC] is timestamped at its access to [l_own] or to
    the data: the write for [tacq] and [trel], the read for [tgt].  So the
    two timelines agree pointwise ([ti_pt]): the version is [l_own], the
    data are [l_x], [l_y].  Every dependency of [tl_dep] is a dependency
    of [hw_dep] between the corresponding accesses ([acc_dep]).

    A spin read may be stale.  It is still safe: while [k] is waiting,
    [l_own] stays at most [k], and at every timestamp it is at most its
    current value ([ti_mono]).  So a read of [k] at any timestamp means
    the current value is [k].

    The proof works over [MemHWg], the memory with the owner of each
    ticket as a ghost ([TicketTowerSpecs.tk_up]): a thread knows that the
    ticket it drew is its own.  The plain memory records this only
    indirectly, through the fetch-and-add in the thread's past and the
    value of [l_nxt] at its timestamp.
    [M_TL_plain] forgets the ghost with [ViewLiftGhost.cal_ghost_to_plain].

    [trel] and [tdw] by a thread that does not hold the lock are errors of
    [TLC]; the proof reaches the error ([APError]) at the invocation.

    Results: [M_TL_ghost], [M_TL_plain]. *)

Require Import Stdlib.FSets.FMapPositive.
Require Import Stdlib.Relations.Relation_Operators Stdlib.Relations.Operators_Properties.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.micromega.Lia.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGISimulation.
Require Import RGILogic.
Require Import models.simlin.AtomicLTS.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftRG.
Require Import models.view.ViewLiftGhost.
Require Import examples.View.TicketTowerSpecs.

Module TicketTowerLock.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS ViewLift ViewLiftRG TicketTowerSpecs.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Open Scope prog_scope.

  (** ** The implementation *)

  Definition spin_body : Prog EHW nat := Vis (hR l_own) (fun v => Ret v).

  Definition acq_impl : Prog EHW unit :=
    Vis (hFAA l_nxt 2) (fun k =>
      bindProg (doWhile (fun v => negb (Nat.eqb v k)) spin_body)
        (fun _ => Vis (hW l_own (S k)) (fun _ => Ret tt))).

  Definition rel_impl : Prog EHW unit :=
    Vis (hR l_own) (fun v => Vis (hW l_own (S v)) (fun _ => Ret tt)).

  Definition gt_impl : Prog EHW nat := Vis (hR l_own) (fun v => Ret v).

  Definition dr_impl (l : DLoc) : Prog EHW nat := Vis (hR (dloc l)) (fun v => Ret v).

  Definition dw_impl (l : DLoc) (a : nat) : Prog EHW unit := Vis (hW (dloc l) a) (fun _ => Ret tt).

  Definition M_TL : ModuleImpl EHW ETL :=
    fun m _ =>
      match m as m0 return Prog EHW (TAr m0) with
      | tacq => acq_impl
      | trel => rel_impl
      | tgt => gt_impl
      | tdr l => dr_impl l
      | tdw l a => dw_impl l a
      end.

  (** ** Lifted states *)

  Notation VE := (VL MemHWg).
  Notation VF := (VL TLC).

  Definition assertion := @Assertion (@ProofState _ _ VE VF).
  Definition rg_relation := @RGRelation _ _ VE VF.

  Definition hw (u : VState MemHWg) (h : Time) : HS := fst (vs_tl MemHWg u h).
  Definition hwc (u : VState MemHWg) : HS := fst (cur MemHWg u).
  Definition tkc (u : VState MemHWg) : Tk := snd (cur MemHWg u).

  (** The operation of the lock and its access to memory. *)
  Variant acc : TOp -> HOp -> Prop :=
  | acc_acq v : acc tacq (hW l_own v)
  | acc_rel v : acc trel (hW l_own v)
  | acc_gt : acc tgt (hR l_own)
  | acc_dr l : acc (tdr l) (hR (dloc l))
  | acc_dw l v : acc (tdw l v) (hW (dloc l) v).

  (** [tl_dep] is induced by [hw_dep]. *)
  Lemma acc_dep o o' m m' : acc o o' -> acc m m' -> tl_dep o m = true -> hw_dep o' m' = true.
  Proof.
    intros Ho Hm Hd. destruct Hm; try (destruct o'; reflexivity).
    - destruct Ho; simpl in *; try discriminate; reflexivity.
    - destruct Ho; simpl in *; try discriminate; try reflexivity.
      apply dloc_eqb_eq in Hd. subst. destruct l; reflexivity.
  Qed.

  Record TLInv (u : VState MemHWg) (w : VState TLC) : Prop := {
    ti_invu : Inv MemHWg u;
    ti_invw : Inv TLC w;
    ti_flu : vs_floor MemHWg u = xH;
    ti_flw : vs_floor TLC w = xH;
    ti_hor : Pos.le (vs_hor TLC w) (vs_hor MemHWg u);
    ti_pt : forall h, tv (vs_tl TLC w h) = hw u h l_own /\ tx (vs_tl TLC w h) = hw u h l_x /\
                      ty (vs_tl TLC w h) = hw u h l_y;
    ti_par : th (cur TLC w) = None <-> Nat.even (hwc u l_own) = true;
    ti_tk : forall j t', tkc u j = Some t' -> j < hwc u l_nxt /\ Nat.even j = true;
    ti_nxt : Nat.even (hwc u l_nxt) = true;
    ti_own : hwc u l_own <= hwc u l_nxt;
    ti_mono : forall h, hw u h l_own <= hwc u l_own;
    ti_hold : forall t', th (cur TLC w) = Some t' ->
      exists ha v, In (hW l_own v, ha) (vs_past MemHWg u t') /\
        forall h, Pos.le ha h -> hw u h l_own = hwc u l_own;
    ti_past : PastRel MemHWg TLC acc u w;
  }.

  Lemma pos_le_gt (h1 h2 : positive) : Pos.le h1 h2 \/ Pos.lt h2 h1.
  Proof. lia. Qed.

  Lemma even_2 n : Nat.even n = true -> exists q, n = (2 * q)%nat.
  Proof. intros He. apply Nat.even_spec in He. destruct He as [q ->]. exists q. reflexivity. Qed.

  Lemma odd_2 n : Nat.even n = false -> exists q, n = (2 * q + 1)%nat.
  Proof.
    intros He. assert (Ho : Nat.odd n = true) by (rewrite <- Nat.negb_even, He; reflexivity).
    apply Nat.odd_spec in Ho. destruct Ho as [q ->]. exists q. reflexivity.
  Qed.

  Section Facts.
    Context (u : VState MemHWg) (w : VState TLC) (HT : TLInv u w).

    Lemma hw_above h : Pos.le (vs_hor MemHWg u) h -> hw u h = hwc u.
    Proof. intros Hh. unfold hw, hwc. rewrite (tl_above MemHWg u h (ti_invu _ _ HT) Hh). reflexivity. Qed.

    Lemma tlw_above h : Pos.le (vs_hor MemHWg u) h -> vs_tl TLC w h = cur TLC w.
    Proof.
      intros Hh. apply (tl_above TLC w h (ti_invw _ _ HT)).
      eapply Pos.le_trans; [exact (ti_hor _ _ HT) | exact Hh].
    Qed.

    Lemma pt_cur : tv (cur TLC w) = hwc u l_own /\ tx (cur TLC w) = hwc u l_x /\ ty (cur TLC w) = hwc u l_y.
    Proof.
      rewrite <- (tlw_above (vs_hor MemHWg u)) by apply Pos.le_refl.
      rewrite <- (hw_above (vs_hor MemHWg u)) by apply Pos.le_refl.
      apply (ti_pt _ _ HT).
    Qed.

    Lemma holder_odd t' : th (cur TLC w) = Some t' -> Nat.even (hwc u l_own) = false.
    Proof.
      intros Hh. destruct (Nat.even (hwc u l_own)) eqn:He; [|reflexivity].
      apply (ti_par _ _ HT) in He. congruence.
    Qed.

    Lemma free_even : th (cur TLC w) = None -> Nat.even (hwc u l_own) = true.
    Proof. apply (ti_par _ _ HT). Qed.
  End Facts.

  (** ** Preservation of the invariant *)

  (** A read of memory, with or without a retroactive operation of the
      lock at the same timestamp. *)
  Lemma hwc_retro u t m h : Inv MemHWg u -> hwc (upd_retro MemHWg u t m h) = hwc u.
  Proof. intros HI. unfold hwc. rewrite cur_retro by exact HI. reflexivity. Qed.

  Lemma tkc_retro u t m h : Inv MemHWg u -> tkc (upd_retro MemHWg u t m h) = tkc u.
  Proof. intros HI. unfold tkc. rewrite cur_retro by exact HI. reflexivity. Qed.

  Lemma hw_retro u t m h h' : hw (upd_retro MemHWg u t m h) h' = hw u h'.
  Proof. reflexivity. Qed.

  Lemma TLInv_read u w t l h :
    TLInv u w -> Inv MemHWg (upd_retro MemHWg u t (hR l) h) -> TLInv (upd_retro MemHWg u t (hR l) h) w.
  Proof.
    intros HT HI. pose proof (ti_invu _ _ HT) as HI0.
    constructor; try rewrite (hwc_retro u t (hR l) h HI0); try rewrite (tkc_retro u t (hR l) h HI0).
    - exact HI.
    - exact (ti_invw _ _ HT).
    - exact (ti_flu _ _ HT).
    - exact (ti_flw _ _ HT).
    - simpl. eapply Pos.le_trans; [exact (ti_hor _ _ HT) | apply Pos.le_max_l].
    - intros h'. rewrite hw_retro. exact (ti_pt _ _ HT h').
    - exact (ti_par _ _ HT).
    - exact (ti_tk _ _ HT).
    - exact (ti_nxt _ _ HT).
    - exact (ti_own _ _ HT).
    - intros h'. rewrite hw_retro. exact (ti_mono _ _ HT h').
    - intros t' Ht'. destruct (ti_hold _ _ HT t' Ht') as (ha & v & Hin & Hc').
      exists ha, v. split.
      + simpl. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin.
      + intros h' Hh'. rewrite hw_retro. exact (Hc' h' Hh').
    - eapply (PastRel_push_u MemHWg TLC acc u w t (hR l) h (ti_past _ _ HT)); intros; reflexivity.
  Qed.

  Lemma TLInv_read_lp u w t l h m :
    TLInv u w -> acc m (hR l) ->
    Inv MemHWg (upd_retro MemHWg u t (hR l) h) -> Inv TLC (upd_retro TLC w t m h) ->
    TLInv (upd_retro MemHWg u t (hR l) h) (upd_retro TLC w t m h).
  Proof.
    intros HT Hacc HI HIw. pose proof (ti_invu _ _ HT) as HI0.
    assert (Hcw : cur TLC (upd_retro TLC w t m h) = cur TLC w) by (apply cur_retro, (ti_invw _ _ HT)).
    constructor; try rewrite Hcw; try rewrite (hwc_retro u t (hR l) h HI0); try rewrite (tkc_retro u t (hR l) h HI0).
    - exact HI.
    - exact HIw.
    - exact (ti_flu _ _ HT).
    - exact (ti_flw _ _ HT).
    - simpl. apply Pos.max_le_compat; [exact (ti_hor _ _ HT) | apply Pos.le_refl].
    - intros h'. rewrite hw_retro. exact (ti_pt _ _ HT h').
    - exact (ti_par _ _ HT).
    - exact (ti_tk _ _ HT).
    - exact (ti_nxt _ _ HT).
    - exact (ti_own _ _ HT).
    - intros h'. rewrite hw_retro. exact (ti_mono _ _ HT h').
    - intros t' Ht'. destruct (ti_hold _ _ HT t' Ht') as (ha & v & Hin & Hc').
      exists ha, v. split.
      + simpl. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin.
      + intros h' Hh'. rewrite hw_retro. exact (Hc' h' Hh').
    - eapply (PastRel_push MemHWg TLC acc u w t m (hR l) h (ti_past _ _ HT) Hacc); intros; reflexivity.
  Qed.

  (** An appended memory operation at [h] with new current state [st], and
      the new lock state [w'] whose timeline above [h] is [ws]. *)
  Section App.
    Context (u : VState MemHWg) (w : VState TLC) (HT : TLInv u w).
    Context (t : tid) (mh : HOp) (h : Time) (st : vl_state MemHWg).
    Context (Hhor : Pos.lt (vs_hor MemHWg u) h).
    Context (HIu : Inv MemHWg (upd_app MemHWg u t mh h st)).
    Context (w' : VState TLC) (ws : TS).
    Context (Hw'inv : Inv TLC w') (Hw'fl : vs_floor TLC w' = xH) (Hw'hor : Pos.le (vs_hor TLC w') h).
    Context (Hw'tl : forall h', vs_tl TLC w' h' = if Pos.leb h h' then ws else vs_tl TLC w h').
    Context (Hw'past : PastRel MemHWg TLC acc (upd_app MemHWg u t mh h st) w').
    Context (Hpt : tv ws = fst st l_own /\ tx ws = fst st l_x /\ ty ws = fst st l_y).
    Context (Hpar : th ws = None <-> Nat.even (fst st l_own) = true).
    Context (Htk : forall j t', snd st j = Some t' -> j < fst st l_nxt /\ Nat.even j = true).
    Context (Hnxt : Nat.even (fst st l_nxt) = true).
    Context (Hown : fst st l_own <= fst st l_nxt).
    Context (Hmono : hwc u l_own <= fst st l_own).

    Let u' := upd_app MemHWg u t mh h st.

    Lemma hw_app h' : hw u' h' = if Pos.leb h h' then fst st else hw u h'.
    Proof using. unfold hw, u'. simpl. unfold tl_write. destruct (Pos.leb h h'); reflexivity. Qed.

    Lemma hwc_app : hwc u' = fst st.
    Proof using. unfold hwc, u'. rewrite cur_app. reflexivity. Qed.

    Lemma tkc_app : tkc u' = snd st.
    Proof using. unfold tkc, u'. rewrite cur_app. reflexivity. Qed.

    Lemma TLInv_app_gen :
      (forall t', th ws = Some t' ->
         exists ha v, In (hW l_own v, ha) (vs_past MemHWg u' t') /\
           forall h', Pos.le ha h' -> hw u' h' l_own = fst st l_own) ->
      cur TLC w' = ws ->
      TLInv u' w'.
    Proof using HIu HT Hhor Hmono Hnxt Hown Hpar Hpt Htk Hw'fl Hw'hor Hw'inv Hw'past Hw'tl.
      intros Hhold Hcw.
      assert (Hc : forall h', Pos.lt h' h -> hw u' h' = hw u h').
      { intros h' Hlt. rewrite hw_app. destruct (Pos.leb h h') eqn:Hb; [|reflexivity].
        apply Pos.leb_le in Hb. exfalso. exact (Pos.lt_irrefl _ (Pos.lt_le_trans _ _ _ Hlt Hb)). }
      constructor.
      - exact HIu.
      - exact Hw'inv.
      - unfold u'. simpl. exact (ti_flu _ _ HT).
      - exact Hw'fl.
      - unfold u'. simpl. exact Hw'hor.
      - intros h'. rewrite Hw'tl, hw_app. destruct (Pos.leb h h') eqn:Hb; [exact Hpt | exact (ti_pt _ _ HT h')].
      - rewrite Hcw, hwc_app. exact Hpar.
      - rewrite tkc_app, hwc_app. exact Htk.
      - rewrite hwc_app. exact Hnxt.
      - rewrite hwc_app. exact Hown.
      - intros h'. rewrite hw_app, hwc_app. destruct (Pos.leb h h'); [lia|].
        pose proof (ti_mono _ _ HT h'). lia.
      - intros t' Ht'. rewrite hwc_app. apply Hhold. rewrite <- Hcw. exact Ht'.
      - exact Hw'past.
    Qed.
  End App.

  (** ** Steps of the memory *)

  Lemma hwg_spec_faa (s : vl_state MemHWg) t l d r (st : vl_state MemHWg) :
    vl_spec MemHWg s t (hFAA l d) r st ->
    r = fst s l /\ st = (hupd (fst s) l (fst s l + d), tk_up (fst s) t (hFAA l d) (snd s)).
  Proof. destruct st as [st g]. intros ((H1 & H2) & H3). simpl in H2, H3. subst. auto. Qed.

  Lemma hwg_spec_w (s : vl_state MemHWg) t l v r (st : vl_state MemHWg) :
    vl_spec MemHWg s t (hW l v) r st -> st = (hupd (fst s) l v, snd s).
  Proof. destruct st as [st g]. intros (H2 & H3). simpl in H2, H3. subst. reflexivity. Qed.

  Lemma hwg_spec_r (s : vl_state MemHWg) t l (r : nat) (st : vl_state MemHWg) :
    vl_spec MemHWg s t (hR l) r st -> r = fst s l.
  Proof. intros ((H1 & _) & _). exact H1. Qed.

  Lemma hw_write_inv u t l v r u' :
    Inv MemHWg u -> VStep MemHWg (Build_ThreadEvent t (ResEv (hW l v) r)) u u' ->
    exists h, Pos.lt (vs_hor MemHWg u) h /\ dep_ok MemHWg u t (hW l v) h /\
      u' = upd_app MemHWg u t (hW l v) h (hupd (hwc u) l v, tkc u).
  Proof.
    intros HI Hs.
    destruct (vstep_res_cases MemHWg t (hW l v) r u u' Hs)
      as [ (Hr & _) | (_ & h & st & Hhor & Hdep & Hspec & ->) ]; [discriminate|].
    apply (spec_app_cur MemHWg u t _ r h st HI Hhor) in Hspec. apply hwg_spec_w in Hspec. subst st.
    exists h. auto.
  Qed.

  Lemma hw_faa_inv u t l d r u' :
    Inv MemHWg u -> VStep MemHWg (Build_ThreadEvent t (ResEv (hFAA l d) r)) u u' ->
    exists h, Pos.lt (vs_hor MemHWg u) h /\ r = hwc u l /\
      u' = upd_app MemHWg u t (hFAA l d) h (hupd (hwc u) l (hwc u l + d), tk_up (hwc u) t (hFAA l d) (tkc u)).
  Proof.
    intros HI Hs.
    destruct (vstep_res_cases MemHWg t (hFAA l d) r u u' Hs)
      as [ (Hr & _) | (_ & h & st & Hhor & Hdep & Hspec & ->) ]; [discriminate|].
    apply (spec_app_cur MemHWg u t _ r h st HI Hhor) in Hspec.
    apply hwg_spec_faa in Hspec as (-> & ->). exists h. auto.
  Qed.

  Lemma hw_read_inv u t l r u' :
    VStep MemHWg (Build_ThreadEvent t (ResEv (hR l) r)) u u' ->
    exists h, Pos.lt (vs_floor MemHWg u) h /\ dep_ok MemHWg u t (hR l) h /\ r = hw u h l /\
      u' = upd_retro MemHWg u t (hR l) h.
  Proof.
    intros Hs.
    destruct (vstep_res_cases MemHWg t (hR l) r u u' Hs)
      as [ (_ & h & Hfl & Hdep & Hspec & ->) | (Hr & _) ]; [|discriminate].
    apply hwg_spec_r in Hspec. exists h. auto.
  Qed.

  (** ** The four appended steps *)

  Lemma tlw_app w t m h ws h' :
    vs_tl TLC (upd_app TLC w t m h ws) h' = if Pos.leb h h' then ws else vs_tl TLC w h'.
  Proof. simpl. unfold tl_write. destruct (Pos.leb h h'); reflexivity. Qed.

  Lemma TLInv_faa u w t h :
    TLInv u w -> Pos.lt (vs_hor MemHWg u) h ->
    Inv MemHWg (upd_app MemHWg u t (hFAA l_nxt 2) h
                  (hupd (hwc u) l_nxt (hwc u l_nxt + 2), tk_up (hwc u) t (hFAA l_nxt 2) (tkc u))) ->
    TLInv (upd_app MemHWg u t (hFAA l_nxt 2) h
             (hupd (hwc u) l_nxt (hwc u l_nxt + 2), tk_up (hwc u) t (hFAA l_nxt 2) (tkc u))) w.
  Proof.
    intros HT Hhor HI. destruct (pt_cur u w HT) as (Hv & Hx & Hy).
    pose proof (ti_nxt _ _ HT) as Hn.
    apply (TLInv_app_gen u w HT t _ h _ Hhor HI w (cur TLC w)); cbn [fst snd].
    - exact (ti_invw _ _ HT).
    - exact (ti_flw _ _ HT).
    - apply Pos.lt_le_incl. eapply Pos.le_lt_trans; [exact (ti_hor _ _ HT) | exact Hhor].
    - intros h'. destruct (Pos.leb h h') eqn:Hb; [|reflexivity].
      apply Pos.leb_le in Hb. apply (tlw_above u w HT). apply Pos.lt_le_incl. eapply Pos.lt_le_trans; eauto.
    - eapply (PastRel_push_u MemHWg TLC acc u w t (hFAA l_nxt 2) h (ti_past _ _ HT)); intros; reflexivity.
    - rewrite !hupd_other by discriminate. auto.
    - rewrite hupd_other by discriminate. exact (ti_par _ _ HT).
    - intros j t' Hj. rewrite hupd_same. simpl in Hj.
      destruct (Nat.eqb j (hwc u l_nxt)) eqn:Hb.
      + apply Nat.eqb_eq in Hb. subst j. split; [lia | exact Hn].
      + destruct (ti_tk _ _ HT j t' Hj) as (Hlt & He). split; [lia | exact He].
    - rewrite hupd_same. rewrite Nat.even_add. rewrite Hn. reflexivity.
    - rewrite hupd_same, hupd_other by discriminate. pose proof (ti_own _ _ HT). lia.
    - rewrite hupd_other by discriminate. lia.
    - intros t' Ht'. destruct (ti_hold _ _ HT t' Ht') as (ha & v & Hin & Hc).
      exists ha, v. split.
      + simpl. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin.
      + intros h' Hh'. rewrite hw_app. rewrite hupd_other by discriminate.
        destruct (Pos.leb h h'); [reflexivity | exact (Hc h' Hh')].
    - reflexivity.
  Qed.

  Lemma TLInv_acq u w t k h :
    TLInv u w -> hwc u l_own = k -> tkc u k = Some t -> Pos.lt (vs_hor MemHWg u) h ->
    Inv MemHWg (upd_app MemHWg u t (hW l_own (S k)) h (hupd (hwc u) l_own (S k), tkc u)) ->
    Inv TLC (upd_app TLC w t tacq h (mkTS (S (tv (cur TLC w))) (Some t) (tx (cur TLC w)) (ty (cur TLC w)))) ->
    TLInv (upd_app MemHWg u t (hW l_own (S k)) h (hupd (hwc u) l_own (S k), tkc u))
          (upd_app TLC w t tacq h (mkTS (S (tv (cur TLC w))) (Some t) (tx (cur TLC w)) (ty (cur TLC w)))).
  Proof.
    intros HT Hk Htk Hhor HI HIw. destruct (pt_cur u w HT) as (Hv & Hx & Hy).
    destruct (ti_tk _ _ HT k t Htk) as (Hlt & Hke).
    pose proof (ti_nxt _ _ HT) as Hn.
    apply (TLInv_app_gen u w HT t _ h _ Hhor HI _ (mkTS (S (tv (cur TLC w))) (Some t) (tx (cur TLC w)) (ty (cur TLC w))) HIw); cbn [fst snd].
    - simpl. exact (ti_flw _ _ HT).
    - simpl. apply Pos.le_refl.
    - apply tlw_app.
    - eapply (PastRel_push MemHWg TLC acc u w t tacq (hW l_own (S k)) h (ti_past _ _ HT) (acc_acq _));
        intros; reflexivity.
    - cbn [tv tx ty]. rewrite hupd_same, !hupd_other by discriminate. rewrite Hv, Hk. auto.
    - cbn [th]. rewrite hupd_same, even_odd_succ, Hke. split; discriminate.
    - exact (ti_tk _ _ HT).
    - rewrite hupd_other by discriminate. exact Hn.
    - rewrite hupd_same, hupd_other by discriminate.
      destruct (even_2 _ Hke) as (a & ->). destruct (even_2 _ Hn) as (b & Hb). rewrite Hb in *. lia.
    - rewrite hupd_same. lia.
    - intros t' Ht'. cbn [th] in Ht'. injection Ht' as <-.
      exists h, (S k). split.
      + simpl. rewrite push_past_self. left. reflexivity.
      + intros h' Hh'. rewrite hw_app. rewrite (proj2 (Pos.leb_le h h') Hh'). reflexivity.
    - apply cur_app.
  Qed.

  Lemma TLInv_rel u w t h :
    TLInv u w -> th (cur TLC w) = Some t -> Pos.lt (vs_hor MemHWg u) h ->
    Inv MemHWg (upd_app MemHWg u t (hW l_own (S (hwc u l_own))) h
                  (hupd (hwc u) l_own (S (hwc u l_own)), tkc u)) ->
    Inv TLC (upd_app TLC w t trel h (mkTS (S (tv (cur TLC w))) None (tx (cur TLC w)) (ty (cur TLC w)))) ->
    TLInv (upd_app MemHWg u t (hW l_own (S (hwc u l_own))) h (hupd (hwc u) l_own (S (hwc u l_own)), tkc u))
          (upd_app TLC w t trel h (mkTS (S (tv (cur TLC w))) None (tx (cur TLC w)) (ty (cur TLC w)))).
  Proof.
    intros HT Hh Hhor HI HIw. destruct (pt_cur u w HT) as (Hv & Hx & Hy).
    pose proof (holder_odd u w HT t Hh) as Hodd.
    pose proof (ti_nxt _ _ HT) as Hn. pose proof (ti_own _ _ HT) as Ho.
    apply (TLInv_app_gen u w HT t _ h _ Hhor HI _ (mkTS (S (tv (cur TLC w))) None (tx (cur TLC w)) (ty (cur TLC w))) HIw); cbn [fst snd].
    - simpl. exact (ti_flw _ _ HT).
    - simpl. apply Pos.le_refl.
    - apply tlw_app.
    - eapply (PastRel_push MemHWg TLC acc u w t trel (hW l_own _) h (ti_past _ _ HT) (acc_rel _));
        intros; reflexivity.
    - cbn [tv tx ty]. rewrite hupd_same, !hupd_other by discriminate. rewrite Hv. auto.
    - cbn [th]. rewrite hupd_same, even_odd_succ, Hodd. split; reflexivity.
    - exact (ti_tk _ _ HT).
    - rewrite hupd_other by discriminate. exact Hn.
    - rewrite hupd_same, hupd_other by discriminate.
      destruct (odd_2 _ Hodd) as (a & Ha). destruct (even_2 _ Hn) as (b & Hb). lia.
    - rewrite hupd_same. lia.
    - intros t' Ht'. discriminate.
    - apply cur_app.
  Qed.

  Lemma tdat_tset_same (x : TS) l a : tdat (tset x l a) l = a.
  Proof. destruct l; reflexivity. Qed.

  Lemma TLInv_dw u w t l a h :
    TLInv u w -> th (cur TLC w) = Some t -> Pos.lt (vs_hor MemHWg u) h ->
    Inv MemHWg (upd_app MemHWg u t (hW (dloc l) a) h (hupd (hwc u) (dloc l) a, tkc u)) ->
    Inv TLC (upd_app TLC w t (tdw l a) h (tset (cur TLC w) l a)) ->
    TLInv (upd_app MemHWg u t (hW (dloc l) a) h (hupd (hwc u) (dloc l) a, tkc u))
          (upd_app TLC w t (tdw l a) h (tset (cur TLC w) l a)).
  Proof.
    intros HT Hh Hhor HI HIw. destruct (pt_cur u w HT) as (Hv & Hx & Hy).
    assert (Hno : dloc l <> l_own) by (destruct l; discriminate).
    assert (Hnn : dloc l <> l_nxt) by (destruct l; discriminate).
    apply (TLInv_app_gen u w HT t _ h _ Hhor HI _ (tset (cur TLC w) l a) HIw); cbn [fst snd].
    - simpl. exact (ti_flw _ _ HT).
    - simpl. apply Pos.le_refl.
    - apply tlw_app.
    - eapply (PastRel_push MemHWg TLC acc u w t (tdw l a) (hW (dloc l) a) h (ti_past _ _ HT) (acc_dw _ _));
        intros; reflexivity.
    - destruct l; cbn [tset tv tx ty dloc]; rewrite ?hupd_same, !hupd_other by discriminate; auto.
    - rewrite hupd_other by exact Hno. destruct l; exact (ti_par _ _ HT).
    - rewrite hupd_other by exact Hnn. exact (ti_tk _ _ HT).
    - rewrite hupd_other by exact Hnn. exact (ti_nxt _ _ HT).
    - rewrite !hupd_other by assumption. exact (ti_own _ _ HT).
    - rewrite hupd_other by exact Hno. lia.
    - intros t' Ht'. assert (Ht0 : th (cur TLC w) = Some t') by (destruct l; exact Ht').
      destruct (ti_hold _ _ HT t' Ht0) as (ha & v & Hin & Hc).
      exists ha, v. split.
      + simpl. unfold push_past. destruct (Pos.eqb t t'); [right|]; exact Hin.
      + intros h' Hh'. rewrite hw_app. cbn [fst snd].
        destruct (Pos.leb h h'); rewrite hupd_other by exact Hno; [reflexivity | exact (Hc h' Hh')].
    - apply cur_app.
  Qed.

  (** ** Guarantee and rely *)

  Definition U (s : @ProofState _ _ VE VF) : VState MemHWg := state (σ s).
  Definition O (s : @ProofState _ _ VE VF) : VState TLC := state (ρ s).

  Definition I : assertion := fun s => exists w, ρ s = Idle w /\ TLInv (U s) w.

  (** What a thread may do to memory: draw a ticket, write [l_own] when
      it is its turn or when it holds the lock, write the data when it
      holds the lock, and read. *)
  Definition HWOK (t : tid) (m : HOp) (u : VState MemHWg) (w : VState TLC) : Prop :=
    match m with
    | hR _ => True
    | hFAA l_nxt d => d = 2
    | hFAA _ _ => False
    | hW l_own v => (exists k, v = S k /\ hwc u l_own = k /\ tkc u k = Some t) \/
                    (th (cur TLC w) = Some t /\ v = S (hwc u l_own))
    | hW l_x _ | hW l_y _ => th (cur TLC w) = Some t
    | hW l_nxt _ => False
    end.

  Definition HWMove (t : tid) (u u' : VState MemHWg) (w : VState TLC) : Prop :=
    u' = u \/ exists m (r : Sig.ar m), VStep MemHWg (Build_ThreadEvent t (ResEv m r)) u u' /\ HWOK t m u w.

  Definition G (t : tid) : rg_relation :=
    fun s1 s2 =>
      (forall t', t' <> t -> TMap.find t' (π s2) = TMap.find t' (π s1)) /\
      HWMove t (state (σ s1)) (state (σ s2)) (state (ρ s1)) /\
      VLMove TLC t (state (ρ s1)) (state (ρ s2)).

  Definition R (t : tid) : rg_relation :=
    fun s1 s2 =>
      (exists t1, t1 <> t /\ (G t1 s1 s2 \/ GINV t1 s1 s2 \/ GRET t1 s1 s2)) \/ s1 = s2.

  Lemma succ_neq (t : tid) : Pos.succ t <> t.
  Proof. intros H. pose proof (Pos.lt_succ_diag_r t). rewrite H in H0. exact (Pos.lt_irrefl _ H0). Qed.

  Lemma R_cases t s1 s2 :
    R t s1 s2 ->
    TMap.find t (π s2) = TMap.find t (π s1) /\
    exists t1, t1 <> t /\ HWMove t1 (U s1) (U s2) (O s1) /\ VLMove TLC t1 (O s1) (O s2).
  Proof.
    unfold U, O.
    intros [(t1 & Hne & [(Hpi & Hu & Ho) | [(f & Hs & Hr & _ & Hp) | (f & ret & Hs & Hr & _ & Hp)]]) | <-].
    - split; [apply Hpi; congruence|]. exists t1. auto.
    - split; [rewrite Hp, TMap.gso by congruence; reflexivity|].
      exists t1. rewrite Hs, Hr. split; [exact Hne | split; [left; reflexivity | apply vlmove_refl]].
    - split; [rewrite Hp, TMap.gro by congruence; reflexivity|].
      exists t1. rewrite Hs, Hr. split; [exact Hne | split; [left; reflexivity | apply vlmove_refl]].
    - split; [reflexivity|]. exists (Pos.succ t).
      split; [apply succ_neq | split; [left; reflexivity | apply vlmove_refl]].
  Qed.

  Lemma hwmove_vlmove t u u' w : HWMove t u u' w -> VLMove MemHWg t u u'.
  Proof. intros [-> | (m & r & Hs & _)]; [apply vlmove_refl | exact (vlmove_step MemHWg t m r u u' Hs)]. Qed.

  (** *** What another thread's move does *)

  Lemma move_tk t1 u0 u w0 j t' :
    TLInv u0 w0 -> HWMove t1 u0 u w0 -> tkc u0 j = Some t' -> tkc u j = Some t'.
  Proof.
    intros HT [-> | (m & r & Hs & Hok)] Hj; [exact Hj|].
    pose proof (ti_invu _ _ HT) as HI.
    destruct m as [l | l v | l d].
    - destruct (hw_read_inv u0 t1 l r u Hs) as (h & _ & _ & _ & ->). rewrite tkc_retro by exact HI. exact Hj.
    - destruct (hw_write_inv u0 t1 l v r u HI Hs) as (h & _ & _ & ->). unfold tkc. rewrite cur_app. exact Hj.
    - destruct (hw_faa_inv u0 t1 l d r u HI Hs) as (h & _ & _ & ->). unfold tkc at 1. rewrite cur_app. simpl.
      destruct l; simpl in Hok; try contradiction; try exact Hj.
      destruct (Nat.eqb j (hwc u0 l_nxt)) eqn:Hb; [|exact Hj].
      apply Nat.eqb_eq in Hb. destruct (ti_tk _ _ HT j t' Hj) as (Hlt & _). lia.
  Qed.

  Lemma move_own t1 u0 u w0 :
    TLInv u0 w0 -> HWMove t1 u0 u w0 ->
    hwc u l_own = hwc u0 l_own \/
    (exists k, hwc u0 l_own = k /\ tkc u0 k = Some t1 /\ hwc u l_own = S k) \/
    (th (cur TLC w0) = Some t1 /\ hwc u l_own = S (hwc u0 l_own)).
  Proof.
    intros HT [-> | (m & r & Hs & Hok)]; [left; reflexivity|].
    pose proof (ti_invu _ _ HT) as HI.
    destruct m as [l | l v | l d].
    - destruct (hw_read_inv u0 t1 l r u Hs) as (h & _ & _ & _ & ->). left. rewrite (hwc_retro u0 t1 (hR l) h HI). reflexivity.
    - destruct (hw_write_inv u0 t1 l v r u HI Hs) as (h & _ & _ & ->).
      assert (Hc : hwc (upd_app MemHWg u0 t1 (hW l v) h (hupd (hwc u0) l v, tkc u0)) = hupd (hwc u0) l v)
        by (unfold hwc; rewrite cur_app; reflexivity).
      rewrite Hc.
      destruct l; simpl in Hok; try contradiction.
      + destruct Hok as [(k & -> & Hk & Htk) | (Hh & ->)].
        * right; left. exists k. rewrite hupd_same. auto.
        * right; right. rewrite hupd_same. auto.
      + left. rewrite hupd_other by discriminate. reflexivity.
      + left. rewrite hupd_other by discriminate. reflexivity.
    - destruct (hw_faa_inv u0 t1 l d r u HI Hs) as (h & _ & _ & ->).
      left. unfold hwc at 1. rewrite cur_app. cbn [fst].
      destruct l; simpl in Hok; try contradiction.
      rewrite hupd_other by discriminate. reflexivity.
  Qed.

  Lemma move_th t1 t w0 w :
    t1 <> t -> Inv TLC w0 -> VLMove TLC t1 w0 w -> th (cur TLC w0) = Some t -> th (cur TLC w) = Some t.
  Proof.
    intros Hne HI [-> | (m & r & Hs)] Hh; [exact Hh|].
    destruct (vstep_res_cur TLC t1 m r w0 w HI Hs) as [(_ & ->) | (_ & Hspec)]; [exact Hh|].
    destruct m as [ | | | l | l a]; simpl in Hspec.
    - destruct Hspec as (Hn & _). congruence.
    - destruct Hspec as (Hn & _). congruence.
    - destruct Hspec as (_ & ->). exact Hh.
    - destruct Hspec as (_ & ->). exact Hh.
    - destruct Hspec as (Hn & _). congruence.
  Qed.

  Section Rely.
    Context (t : tid) (s0 s : @ProofState _ _ VE VF).
    Context (HR : R t s0 s) (HI0 : I s0).

    Lemma I_TLInv : TLInv (U s0) (O s0).
    Proof using HI0. destruct HI0 as (w & Hw & HT). unfold O. rewrite Hw. exact HT. Qed.

    Lemma rely_past : vs_past MemHWg (U s) t = vs_past MemHWg (U s0) t.
    Proof using HR.
      destruct (R_cases _ _ _ HR) as (_ & t1 & Hne & Hu & _).
      exact (vlmove_past MemHWg t1 t _ _ Hne (hwmove_vlmove _ _ _ _ Hu)).
    Qed.

    Lemma rely_tk j t' : tkc (U s0) j = Some t' -> tkc (U s) j = Some t'.
    Proof using HR HI0.
      destruct (R_cases _ _ _ HR) as (_ & t1 & Hne & Hu & _).
      exact (move_tk t1 _ _ _ j t' I_TLInv Hu).
    Qed.

    Lemma rely_wait k : tkc (U s0) k = Some t -> hwc (U s0) l_own <= k -> hwc (U s) l_own <= k.
    Proof using HR HI0.
      intros Hk Hle. pose proof I_TLInv as HT.
      destruct (R_cases _ _ _ HR) as (_ & t1 & Hne & Hu & _).
      destruct (ti_tk _ _ HT k t Hk) as (_ & Hke).
      destruct (move_own t1 _ _ _ HT Hu) as [-> | [(k1 & Hk1 & Htk1 & ->) | (Hh & ->)]].
      - exact Hle.
      - destruct (ti_tk _ _ HT k1 t1 Htk1) as (_ & Hk1e).
        assert (Hne' : k1 <> k) by (intros ->; congruence).
        destruct (even_2 _ Hke) as (a & ->). destruct (even_2 _ Hk1e) as (b & ->). lia.
      - pose proof (holder_odd _ _ HT t1 Hh) as Hodd.
        destruct (even_2 _ Hke) as (a & ->). destruct (odd_2 _ Hodd) as (b & Hb). lia.
    Qed.

    Lemma rely_turn k : tkc (U s0) k = Some t -> hwc (U s0) l_own = k -> hwc (U s) l_own = k.
    Proof using HR HI0.
      intros Hk Heq. pose proof I_TLInv as HT.
      destruct (R_cases _ _ _ HR) as (_ & t1 & Hne & Hu & _).
      destruct (ti_tk _ _ HT k t Hk) as (_ & Hke).
      destruct (move_own t1 _ _ _ HT Hu) as [-> | [(k1 & Hk1 & Htk1 & ->) | (Hh & ->)]].
      - exact Heq.
      - exfalso. subst. congruence.
      - exfalso. pose proof (holder_odd _ _ HT t1 Hh) as Hodd. subst. congruence.
    Qed.

    Lemma rely_hold : th (cur TLC (O s0)) = Some t ->
      th (cur TLC (O s)) = Some t /\ hwc (U s) l_own = hwc (U s0) l_own.
    Proof using HR HI0.
      intros Hh. pose proof I_TLInv as HT.
      destruct (R_cases _ _ _ HR) as (_ & t1 & Hne & Hu & Ho).
      split; [exact (move_th t1 t _ _ Hne (ti_invw _ _ HT) Ho Hh)|].
      pose proof (holder_odd _ _ HT t Hh) as Hodd.
      destruct (move_own t1 _ _ _ HT Hu) as [-> | [(k1 & Hk1 & Htk1 & ->) | (Hh1 & ->)]].
      - reflexivity.
      - exfalso. destruct (ti_tk _ _ HT k1 t1 Htk1) as (_ & Hk1e). congruence.
      - exfalso. congruence.
    Qed.
  End Rely.

  (** ** Assertions and their stability *)

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition Pre (t : tid) (f : TOp) : assertion := ALin t (Semantics.ls_inv f).

  (** Waiting with ticket [k]. *)
  Definition Wt (t : tid) (k : nat) : assertion :=
    fun s => tkc (U s) k = Some t /\ hwc (U s) l_own <= k.

  (** Waiting, after a read of [v]. *)
  Definition Sp (t : tid) (k v : nat) : assertion :=
    fun s => tkc (U s) k = Some t /\ hwc (U s) l_own <= k /\ (v = k -> hwc (U s) l_own = k).

  (** The turn of ticket [k]. *)
  Definition Tn (t : tid) (k : nat) : assertion :=
    fun s => tkc (U s) k = Some t /\ hwc (U s) l_own = k.

  Definition Ho (t : tid) : assertion := fun s => th (cur TLC (O s)) = Some t.

  Definition Hrd (t : tid) (v : nat) : assertion :=
    fun s => th (cur TLC (O s)) = Some t /\ hwc (U s) l_own = v.

  Definition SI (t : tid) (X : assertion) : Prop :=
    forall s0 s, I s0 -> X s0 -> R t s0 s -> I s -> X s.

  Lemma stable_I t X : SI t X -> Stable (R t) I (I //\\ X).
  Proof. intros HX s [(s0 & (HI0 & HX0) & HR) HI]. split; [exact HI | exact (HX s0 s HI0 HX0 HR HI)]. Qed.

  Lemma SI_conj t X Y : SI t X -> SI t Y -> SI t (X //\\ Y).
  Proof. intros HX HY s0 s HI0 [Hx Hy] HR HI. split; [exact (HX _ _ HI0 Hx HR HI) | exact (HY _ _ HI0 Hy HR HI)]. Qed.

  Lemma SI_ALin t ls : SI t (ALin t ls).
  Proof. intros s0 s _ H HR _. unfold ALin in *. destruct (R_cases _ _ _ HR) as [-> _]. exact H. Qed.

  Lemma SI_Wt t k : SI t (Wt t k).
  Proof.
    intros s0 s HI0 (Hk & Hle) HR _. split; [exact (rely_tk t s0 s HR HI0 k t Hk)|].
    exact (rely_wait t s0 s HR HI0 k Hk Hle).
  Qed.

  Lemma SI_Sp t k v : SI t (Sp t k v).
  Proof.
    intros s0 s HI0 (Hk & Hle & Hv') HR _. split; [exact (rely_tk t s0 s HR HI0 k t Hk)|].
    split; [exact (rely_wait t s0 s HR HI0 k Hk Hle)|].
    intros Hvk. exact (rely_turn t s0 s HR HI0 k Hk (Hv' Hvk)).
  Qed.

  Lemma SI_Tn t k : SI t (Tn t k).
  Proof.
    intros s0 s HI0 (Hk & Heq) HR _. split; [exact (rely_tk t s0 s HR HI0 k t Hk)|].
    exact (rely_turn t s0 s HR HI0 k Hk Heq).
  Qed.

  Lemma SI_Ho t : SI t (Ho t).
  Proof. intros s0 s HI0 Hh HR _. exact (proj1 (rely_hold t s0 s HR HI0 Hh)). Qed.

  Lemma SI_Hrd t v : SI t (Hrd t v).
  Proof.
    intros s0 s HI0 (Hh & Heq) HR _. destruct (rely_hold t s0 s HR HI0 Hh) as (Hh' & Hc).
    split; [exact Hh' | rewrite Hc; exact Heq].
  Qed.

  (** ** Possibility updates *)

  Definition SOnly (X : assertion) : Prop :=
    forall (σ1 σ2 : State VE) (ρ0 : State VF) (π0 : tmap (@Semantics.LinState ETL)),
      state σ2 = state σ1 -> X (σ1, ρ0, π0) -> X (σ2, ρ0, π0).

  Ltac sonly :=
    let Heqs := fresh "Heqs" in let HX := fresh "HX" in
    intros ? ? ? ? Heqs HX;
    unfold Conj, ALin, Pre, Wt, Sp, Tn, Ho, Hrd, U, O in *; cbn [σ ρ π] in *;
    rewrite ?Heqs; exact HX.

  Lemma pupdate_inv t m X :
    SOnly X -> PUpdate (G t) (Build_ThreadEvent t (InvEv m)) (I //\\ X) (I //\\ X).
  Proof.
    intros HX σ0 ρ0 π0 [HI Hx] σ1 Hs.
    destruct (astep_inv_cases MemHWg t m σ0 σ1 Hs) as (v & -> & ->).
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact HI | exact (HX (Idle v) (Pending v t m) ρ0 π0 eq_refl Hx)].
    - split; [intros; reflexivity | split; [left; reflexivity | apply vlmove_refl]].
  Qed.

  Lemma noerror t (m : HOp) (s : @ProofState _ _ VE VF) :
    ANoError (VE := VE) (VF := VF) (Build_ThreadEvent t (InvEv m)) s.
  Proof.
    intros He. destruct s as [σ0 ρ0 π0]. simpl in *.
    inversion He as [ev v Herr]; subst. exact Herr.
  Qed.

  Lemma I_step (ρ0 : State VF) (π0 : tmap (@Semantics.LinState ETL)) w u' :
    ρ0 = Idle w -> TLInv u' w -> I ((Idle u' : State VE), ρ0, π0).
  Proof. intros -> HT. exists w. split; [reflexivity | exact HT]. Qed.

  Lemma I_lp (π0 : tmap (@Semantics.LinState ETL)) w' u' :
    TLInv u' w' -> I ((Idle u' : State VE), (Idle w' : State VF), π0).
  Proof. intros HT. exists w'. split; [reflexivity | exact HT]. Qed.

  Lemma G_mem t (σ0 σ1 : State VE) (ρ0 : State VF) π0 u u' w m (r : Sig.ar m) :
    state σ0 = u -> state σ1 = u' -> state ρ0 = w ->
    VStep MemHWg (Build_ThreadEvent t (ResEv m r)) u u' -> HWOK t m u w ->
    G t (σ0, ρ0, π0) (σ1, ρ0, π0).
  Proof.
    intros H0 H1 Hw Hs Hok. split; [intros; reflexivity|]. simpl. rewrite H0, H1, Hw.
    split; [right; exists m, r; auto | apply vlmove_refl].
  Qed.

  Lemma G_lp t (σ0 σ1 : State VE) w w' π0 u u' m (r : Sig.ar m) f (rf : Sig.ar f) :
    state σ0 = u -> state σ1 = u' ->
    VStep MemHWg (Build_ThreadEvent t (ResEv m r)) u u' -> HWOK t m u w ->
    VStep TLC (Build_ThreadEvent t (ResEv f rf)) w w' ->
    G t (σ0, (Idle w : State VF), π0)
        (σ1, (Idle w' : State VF), TMap.add t (Semantics.ls_linr f rf) (TMap.add t (Semantics.ls_lini f) π0)).
  Proof.
    intros H0 H1 Hs Hok Hw. split; [intros t' Hne; apply vl_lp_find_other; exact Hne|]. simpl. rewrite H0, H1.
    split; [right; exists m, r; auto | exact (vlmove_step TLC t f rf w w' Hw)].
  Qed.

  Lemma lp_dep u w t (m : TOp) (m' : HOp) h :
    TLInv u w -> acc m m' -> dep_ok MemHWg u t m' h -> dep_ok TLC w t m h.
  Proof.
    intros HT Hm Hd. apply (dep_ok_transfer MemHWg TLC acc u w t m m' h (ti_past _ _ HT)); [|exact Hd].
    intros o o' Ho Hdep. exact (acc_dep o o' m m' Ho Hm Hdep).
  Qed.

  (** *** Acquire *)

  Lemma acq_faa t k :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hFAA l_nxt 2) k))
      (I //\\ Pre t tacq) (I //\\ (Pre t tacq //\\ Wt t k)).
  Proof.
    intros σ0 ρ0 π0 [(w & Hρ & HT) Hlin] σ1 Hs.
    destruct (astep_res_cases MemHWg t _ k σ0 σ1 Hs) as (u & u' & -> & -> & Hv).
    unfold U in HT. cbn [σ ρ state] in HT, Hρ.
    destruct (hw_faa_inv u t l_nxt 2 k u' (ti_invu _ _ HT) Hv) as (h & Hhor & Hk & ->).
    pose proof (TLInv_faa u w t h HT Hhor (VStep_Inv MemHWg _ _ _ Hv (ti_invu _ _ HT))) as HT'.
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ w _ Hρ HT') | split; [exact Hlin|]].
      unfold Wt, U, tkc, hwc. cbn [σ state]. rewrite cur_app. cbn [fst snd tk_up].
      rewrite Hk, Nat.eqb_refl, hupd_other by discriminate. split; [reflexivity|].
      exact (ti_own _ _ HT).
    - eapply G_mem; [reflexivity | reflexivity | rewrite Hρ; reflexivity | exact Hv | reflexivity].
  Qed.

  Lemma acq_spin t k v :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hR l_own) v))
      (I //\\ (Pre t tacq //\\ Wt t k)) (I //\\ (Pre t tacq //\\ Sp t k v)).
  Proof.
    intros σ0 ρ0 π0 [(w & Hρ & HT) (Hlin & Hk & Hle)] σ1 Hs.
    destruct (astep_res_cases MemHWg t _ v σ0 σ1 Hs) as (u & u' & -> & -> & Hv).
    unfold U, Wt in *. cbn [σ ρ state] in *.
    destruct (hw_read_inv u t l_own v u' Hv) as (h & _ & _ & Hval & ->).
    pose proof (TLInv_read u w t l_own h HT (VStep_Inv MemHWg _ _ _ Hv (ti_invu _ _ HT))) as HT'.
    pose proof (ti_mono _ _ HT h) as Hm.
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ w _ Hρ HT') | split; [exact Hlin|]].
      unfold Sp, U. cbn [σ state].
      rewrite (tkc_retro u t (hR l_own) h (ti_invu _ _ HT)), (hwc_retro u t (hR l_own) h (ti_invu _ _ HT)).
      split; [exact Hk | split; [exact Hle | intros ->; lia]].
    - eapply G_mem; [reflexivity | reflexivity | rewrite Hρ; reflexivity | exact Hv | exact Logic.I].
  Qed.

  Lemma acq_write t k r :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hW l_own (S k)) r))
      (I //\\ (Pre t tacq //\\ Tn t k)) (I //\\ ALin t (Semantics.ls_linr tacq tt)).
  Proof.
    intros σ0 ρ0 π0 [(w & Hρ & HT) (Hlin & Hk & Heq)] σ1 Hs.
    destruct (astep_res_cases MemHWg t _ r σ0 σ1 Hs) as (u & u' & -> & -> & Hv).
    unfold U, Tn in *. cbn [σ ρ state] in *.
    destruct (hw_write_inv u t l_own (S k) r u' (ti_invu _ _ HT) Hv) as (h & Hhor & Hdep & ->).
    destruct (ti_tk _ _ HT k t Hk) as (_ & Hke).
    assert (Hfree : th (cur TLC w) = None) by (apply (ti_par _ _ HT); rewrite Heq; exact Hke).
    set (ws := mkTS (S (tv (cur TLC w))) (Some t) (tx (cur TLC w)) (ty (cur TLC w))).
    assert (Hhw : Pos.lt (vs_hor TLC w) h) by (eapply Pos.le_lt_trans; [exact (ti_hor _ _ HT) | exact Hhor]).
    assert (Hvw : VStep TLC (Build_ThreadEvent t (ResEv tacq tt)) w (upd_app TLC w t tacq h ws)).
    { refine (vstep_app TLC t tacq tt h ws w _ _ eq_refl eq_refl Hhw
                (lp_dep u w t tacq _ h HT (acc_acq _) Hdep) _ eq_refl).
      rewrite (tl_above TLC w h (ti_invw _ _ HT) (Pos.lt_le_incl _ _ Hhw)). simpl. split; [exact Hfree | reflexivity]. }
    pose proof (TLInv_acq u w t k h HT Heq Hk Hhor (VStep_Inv MemHWg _ _ _ Hv (ti_invu _ _ HT))
                  (VStep_Inv TLC _ _ _ Hvw (ti_invw _ _ HT))) as HT'.
    exists (Idle (upd_app TLC w t tacq h ws)),
      (TMap.add t (Semantics.ls_linr tacq tt) (TMap.add t (Semantics.ls_lini tacq) π0)).
    split; [rewrite Hρ; exact (vl_lp TLC w _ t tacq tt π0 Hlin Hvw)|]. split.
    - split; [exact (I_lp _ _ _ HT') | apply vl_lp_find].
    - rewrite Hρ. eapply G_lp; [reflexivity | reflexivity | exact Hv | | exact Hvw].
      left. exists k. auto.
  Qed.

  (** *** Release *)

  Lemma rel_read t v :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hR l_own) v))
      (I //\\ (Pre t trel //\\ Ho t)) (I //\\ (Pre t trel //\\ Hrd t v)).
  Proof.
    intros σ0 ρ0 π0 [(w & Hρ & HT) (Hlin & Hh)] σ1 Hs.
    destruct (astep_res_cases MemHWg t _ v σ0 σ1 Hs) as (u & u' & -> & -> & Hv).
    unfold U, Ho, O in *. cbn [σ ρ state] in *. rewrite Hρ in Hh. cbn [state] in Hh.
    destruct (hw_read_inv u t l_own v u' Hv) as (h & _ & Hdep & Hval & ->).
    destruct (ti_hold _ _ HT t Hh) as (ha & v0 & Hin & Hc).
    pose proof (Hdep _ _ Hin eq_refl) as Hlt.
    pose proof (TLInv_read u w t l_own h HT (VStep_Inv MemHWg _ _ _ Hv (ti_invu _ _ HT))) as HT'.
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ w _ Hρ HT') | split; [exact Hlin|]].
      unfold Hrd, U, O. cbn [σ ρ state]. rewrite Hρ. cbn [state].
      rewrite (hwc_retro u t (hR l_own) h (ti_invu _ _ HT)).
      split; [exact Hh | rewrite Hval; symmetry; apply Hc; apply Pos.lt_le_incl; exact Hlt].
    - eapply G_mem; [reflexivity | reflexivity | rewrite Hρ; reflexivity | exact Hv | exact Logic.I].
  Qed.

  Lemma rel_write t v r :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hW l_own (S v)) r))
      (I //\\ (Pre t trel //\\ Hrd t v)) (I //\\ ALin t (Semantics.ls_linr trel tt)).
  Proof.
    intros σ0 ρ0 π0 [(w & Hρ & HT) (Hlin & Hh & Heq)] σ1 Hs.
    destruct (astep_res_cases MemHWg t _ r σ0 σ1 Hs) as (u & u' & -> & -> & Hv).
    unfold U, O in *. cbn [σ ρ state] in *. rewrite Hρ in Hh. cbn [state] in Hh.
    destruct (hw_write_inv u t l_own (S v) r u' (ti_invu _ _ HT) Hv) as (h & Hhor & Hdep & ->).
    subst v.
    set (ws := mkTS (S (tv (cur TLC w))) None (tx (cur TLC w)) (ty (cur TLC w))).
    assert (Hhw : Pos.lt (vs_hor TLC w) h) by (eapply Pos.le_lt_trans; [exact (ti_hor _ _ HT) | exact Hhor]).
    assert (Hvw : VStep TLC (Build_ThreadEvent t (ResEv trel tt)) w (upd_app TLC w t trel h ws)).
    { refine (vstep_app TLC t trel tt h ws w _ _ eq_refl eq_refl Hhw
                (lp_dep u w t trel _ h HT (acc_rel _) Hdep) _ eq_refl).
      rewrite (tl_above TLC w h (ti_invw _ _ HT) (Pos.lt_le_incl _ _ Hhw)). simpl. split; [exact Hh | reflexivity]. }
    pose proof (TLInv_rel u w t h HT Hh Hhor (VStep_Inv MemHWg _ _ _ Hv (ti_invu _ _ HT))
                  (VStep_Inv TLC _ _ _ Hvw (ti_invw _ _ HT))) as HT'.
    exists (Idle (upd_app TLC w t trel h ws)),
      (TMap.add t (Semantics.ls_linr trel tt) (TMap.add t (Semantics.ls_lini trel) π0)).
    split; [rewrite Hρ; exact (vl_lp TLC w _ t trel tt π0 Hlin Hvw)|]. split.
    - split; [exact (I_lp _ _ _ HT') | apply vl_lp_find].
    - rewrite Hρ. eapply G_lp; [reflexivity | reflexivity | exact Hv | | exact Hvw].
      right. auto.
  Qed.

  (** *** Reads of the version and of the data *)

  Lemma read_lp t (f : TOp) l (v : nat) (rf : TAr f) :
    acc f (hR l) -> vl_retro TLC f = true ->
    (forall w u h, TLInv u w -> v = hw u h l -> vl_spec TLC (vs_tl TLC w h) t f rf (vs_tl TLC w h)) ->
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hR l) v))
      (I //\\ Pre t f) (I //\\ ALin t (Semantics.ls_linr f rf)).
  Proof.
    intros Hacc Hr Hspec σ0 ρ0 π0 [(w & Hρ & HT) Hlin] σ1 Hs.
    destruct (astep_res_cases MemHWg t (hR l) v σ0 σ1 Hs) as (u & u' & -> & -> & Hv).
    unfold U in *. cbn [σ ρ state] in *.
    destruct (hw_read_inv u t l v u' Hv) as (h & Hfl & Hdep & Hval & ->).
    assert (Hvw : VStep TLC (Build_ThreadEvent t (ResEv f rf)) w (upd_retro TLC w t f h)).
    { refine (vstep_retro TLC t f rf h w _ _ eq_refl Hr _ (lp_dep u w t f _ h HT Hacc Hdep) (Hspec w u h HT Hval) eq_refl).
      rewrite (ti_flw _ _ HT). rewrite (ti_flu _ _ HT) in Hfl. exact Hfl. }
    pose proof (TLInv_read_lp u w t l h f HT Hacc (VStep_Inv MemHWg _ _ _ Hv (ti_invu _ _ HT))
                  (VStep_Inv TLC _ _ _ Hvw (ti_invw _ _ HT))) as HT'.
    exists (Idle (upd_retro TLC w t f h)),
      (TMap.add t (Semantics.ls_linr f rf) (TMap.add t (Semantics.ls_lini f) π0)).
    split; [rewrite Hρ; exact (vl_lp TLC w _ t f rf π0 Hlin Hvw)|]. split.
    - split; [exact (I_lp _ _ _ HT') | apply vl_lp_find].
    - rewrite Hρ. eapply G_lp; [reflexivity | reflexivity | exact Hv | exact Logic.I | exact Hvw].
  Qed.

  Lemma gt_read t v :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hR l_own) v))
      (I //\\ Pre t tgt) (I //\\ ALin t (Semantics.ls_linr tgt v)).
  Proof.
    apply (read_lp t tgt l_own v v); [constructor | reflexivity |].
    intros w u h HT ->. simpl. split; [|reflexivity]. symmetry. exact (proj1 (ti_pt _ _ HT h)).
  Qed.

  Lemma dr_read t l v :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hR (dloc l)) v))
      (I //\\ Pre t (tdr l)) (I //\\ ALin t (Semantics.ls_linr (tdr l) v)).
  Proof.
    apply (read_lp t (tdr l) (dloc l) v v); [constructor | reflexivity |].
    intros w u h HT ->. simpl. split; [|reflexivity].
    destruct (ti_pt _ _ HT h) as (_ & Hx & Hy). destruct l; simpl; symmetry; assumption.
  Qed.

  (** *** Data write *)

  Lemma dw_write t l a r :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (hW (dloc l) a) r))
      (I //\\ (Pre t (tdw l a) //\\ Ho t)) (I //\\ ALin t (Semantics.ls_linr (tdw l a) tt)).
  Proof.
    intros σ0 ρ0 π0 [(w & Hρ & HT) (Hlin & Hh)] σ1 Hs.
    destruct (astep_res_cases MemHWg t _ r σ0 σ1 Hs) as (u & u' & -> & -> & Hv).
    unfold U, Ho, O in *. cbn [σ ρ state] in *. rewrite Hρ in Hh. cbn [state] in Hh.
    destruct (hw_write_inv u t (dloc l) a r u' (ti_invu _ _ HT) Hv) as (h & Hhor & Hdep & ->).
    set (ws := tset (cur TLC w) l a).
    assert (Hhw : Pos.lt (vs_hor TLC w) h) by (eapply Pos.le_lt_trans; [exact (ti_hor _ _ HT) | exact Hhor]).
    assert (Hvw : VStep TLC (Build_ThreadEvent t (ResEv (tdw l a) tt)) w (upd_app TLC w t (tdw l a) h ws)).
    { refine (vstep_app TLC t (tdw l a) tt h ws w _ _ eq_refl eq_refl Hhw
                (lp_dep u w t (tdw l a) _ h HT (acc_dw _ _) Hdep) _ eq_refl).
      rewrite (tl_above TLC w h (ti_invw _ _ HT) (Pos.lt_le_incl _ _ Hhw)). simpl. split; [exact Hh | reflexivity]. }
    pose proof (TLInv_dw u w t l a h HT Hh Hhor (VStep_Inv MemHWg _ _ _ Hv (ti_invu _ _ HT))
                  (VStep_Inv TLC _ _ _ Hvw (ti_invw _ _ HT))) as HT'.
    exists (Idle (upd_app TLC w t (tdw l a) h ws)),
      (TMap.add t (Semantics.ls_linr (tdw l a) tt) (TMap.add t (Semantics.ls_lini (tdw l a)) π0)).
    split; [rewrite Hρ; exact (vl_lp TLC w _ t (tdw l a) tt π0 Hlin Hvw)|]. split.
    - split; [exact (I_lp _ _ _ HT') | apply vl_lp_find].
    - rewrite Hρ. eapply G_lp; [reflexivity | reflexivity | exact Hv | | exact Hvw].
      destruct l; exact Hh.
  Qed.

  (** ** The methods *)

  Lemma Pinv_gen t f : ⊨ Ginv t f ⊚ I ==>> I //\\ Pre t f.
  Proof.
    intros s (s0 & HI0 & (Hσ & Hρ & _ & Hπ)). split.
    - destruct HI0 as (w & Hw & HT). exists w. unfold U in *. rewrite <- Hσ, <- Hρ. auto.
    - unfold Pre, ALin. rewrite Hπ. apply TMap.gss.
  Qed.

  Lemma Qret_gen t f ret (X : assertion) : ⊨ Gret t f ret ⊚ (I //\\ X) ==>> I.
  Proof.
    intros s (s0 & (HI0 & _) & (Hσ & Hρ & _)).
    destruct HI0 as (w & Hw & HT). exists w. unfold U in *. rewrite <- Hσ, <- Hρ. auto.
  Qed.

  Lemma vis_step {A} t (m : HOp) (k : HAr m -> Prog EHW A) (X : assertion) (Y : HAr m -> assertion) Q :
    SOnly X -> SI t X -> (forall ret, SI t (Y ret)) ->
    (forall ret, PUpdate (G t) (Build_ThreadEvent t (ResEv m ret)) (I //\\ X) (I //\\ Y ret)) ->
    (forall ret, [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Y ret }} k ret {{ Q }}) ->
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ X }} Vis m k {{ Q }}.
  Proof.
    intros Hso HsX HsY Hres Hk.
    apply provable_vis_safe with (P' := I //\\ X) (Q' := fun ret => I //\\ Y ret).
    - intros s _. apply noerror.
    - intros s [HI _]. exact HI.
    - intros ret s [HI _]. exact HI.
    - apply stable_I. exact HsX.
    - intros ret. apply stable_I. exact (HsY ret).
    - apply pupdate_inv. exact Hso.
    - exact Hres.
    - exact Hk.
  Qed.

  (** The first step of a method that is an error unless its caller
      holds the lock. *)
  Lemma vis_step_err {A} t (m : HOp) (k : HAr m -> Prog EHW A) (X X' : assertion) (Y : HAr m -> assertion) Q :
    (forall s, (I //\\ X) s -> (I //\\ X') s \/ APError s) ->
    SOnly X' -> SI t X' -> (forall ret, SI t (Y ret)) ->
    (forall ret, PUpdate (G t) (Build_ThreadEvent t (ResEv m ret)) (I //\\ X') (I //\\ Y ret)) ->
    (forall ret, [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Y ret }} k ret {{ Q }}) ->
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ X }} Vis m k {{ Q }}.
  Proof.
    intros Hsplit Hso HsX HsY Hres Hk.
    apply provable_vis with (P := I //\\ X') (P' := I //\\ X') (Q' := fun ret => I //\\ Y ret).
    - exact Hsplit.
    - intros s _. apply noerror.
    - intros s [HI _]. exact HI.
    - intros ret s [HI _]. exact HI.
    - apply stable_I. exact HsX.
    - intros ret. apply stable_I. exact (HsY ret).
    - apply pupdate_inv. exact Hso.
    - exact Hres.
    - exact Hk.
  Qed.

  Lemma holder_split t f :
    (forall x : TS, th x <> Some t -> vl_err TLC t f x) ->
    forall s, (I //\\ Pre t f) s -> (I //\\ (Pre t f //\\ Ho t)) s \/ APError s.
  Proof.
    intros Herr s [HI Hlin]. destruct HI as (w & Hρ & HT).
    destruct (th (cur TLC w)) as [t'|] eqn:Hth.
    - destruct (Pos.eq_dec t' t) as [-> | Hne].
      + left. split; [exists w; split; assumption|]. split; [exact Hlin|].
        unfold Ho, O. rewrite Hρ. exact Hth.
      + right. unfold APError. rewrite Hρ. apply (vl_lp_error TLC w t f); [exact Hlin|].
        apply Herr. rewrite Hth. congruence.
    - right. unfold APError. rewrite Hρ. apply (vl_lp_error TLC w t f); [exact Hlin|].
      apply Herr. rewrite Hth. discriminate.
  Qed.

  Lemma ret_step {A} t (a : A) (X : assertion) (Q : A -> assertion) (Y : assertion) :
    (forall s, X s -> Y s) -> Q a = I //\\ Y -> SI t Y ->
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ X }} Ret a {{ Q }}.
  Proof.
    intros HXY HQ HY. apply provable_ret_safe; rewrite HQ.
    - intros s [HI Hx]. exact (conj HI (HXY s Hx)).
    - intros s [HI _]. exact HI.
    - apply stable_I. exact HY.
  Qed.

  Definition Post (t : tid) (f : TOp) (ret : TAr f) : assertion :=
    I //\\ ALin t (Semantics.ls_linr f ret).

  Lemma acq_triple t :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Pre t tacq }} acq_impl {{ Post t tacq }}.
  Proof.
    unfold acq_impl.
    apply vis_step with (Y := fun k => Pre t tacq //\\ Wt t k).
    { sonly. }
    { apply SI_ALin. }
    { intros k. apply SI_conj; [apply SI_ALin | apply SI_Wt]. }
    { apply acq_faa. }
    intros k.
    apply provable_seq with
      (Q' := fun a => (I //\\ (Pre t tacq //\\ Sp t k a)) //\\ ⌜negb (Nat.eqb a k) = false⌝).
    - apply provable_dowhile.
      + intros a s ((HI & Hlin & Hk & Hle & _) & _). split; [exact HI | split; [exact Hlin | split; assumption]].
      + intros a s [HI _]. exact HI.
      + intros a. apply stable_I, SI_conj; [apply SI_ALin | apply SI_Sp].
      + unfold spin_body. apply vis_step with (Y := fun v => Pre t tacq //\\ Sp t k v).
        { sonly. }
        { apply SI_conj; [apply SI_ALin | apply SI_Wt]. }
        { intros v. apply SI_conj; [apply SI_ALin | apply SI_Sp]. }
        { apply acq_spin. }
        intros v. apply ret_step with (Y := Pre t tacq //\\ Sp t k v).
        * intros s H. exact H.
        * reflexivity.
        * apply SI_conj; [apply SI_ALin | apply SI_Sp].
    - intros a.
      apply provable_conseq_weak_pre with (P' := I //\\ (Pre t tacq //\\ Tn t k)).
      { intros s ((HI & Hlin & Hk & _ & Heq) & Hb). unfold APure in Hb.
        destruct (Nat.eqb a k) eqn:Hak; [|discriminate]. apply Nat.eqb_eq in Hak.
        split; [exact HI | split; [exact Hlin | split; [exact Hk | exact (Heq Hak)]]]. }
      apply vis_step with (Y := fun _ => ALin t (Semantics.ls_linr tacq tt)).
      { sonly. }
      { apply SI_conj; [apply SI_ALin | apply SI_Tn]. }
      { intros _. apply SI_ALin. }
      { apply acq_write. }
      intros _. apply ret_step with (Y := ALin t (Semantics.ls_linr tacq tt)).
      + intros s H. exact H.
      + reflexivity.
      + apply SI_ALin.
  Qed.

  Lemma rel_triple t :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Pre t trel }} rel_impl {{ Post t trel }}.
  Proof.
    unfold rel_impl.
    apply vis_step_err with (X' := Pre t trel //\\ Ho t) (Y := fun v => Pre t trel //\\ Hrd t v).
    { apply holder_split. intros x Hx. exact Hx. }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_Ho]. }
    { intros v. apply SI_conj; [apply SI_ALin | apply SI_Hrd]. }
    { apply rel_read. }
    intros v. apply vis_step with (Y := fun _ => ALin t (Semantics.ls_linr trel tt)).
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_Hrd]. }
    { intros _. apply SI_ALin. }
    { apply rel_write. }
    intros _. apply ret_step with (Y := ALin t (Semantics.ls_linr trel tt)).
    - intros s H. exact H.
    - reflexivity.
    - apply SI_ALin.
  Qed.

  Lemma gt_triple t :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Pre t tgt }} gt_impl {{ Post t tgt }}.
  Proof.
    unfold gt_impl.
    apply vis_step with (Y := fun v => ALin t (Semantics.ls_linr tgt v)).
    { sonly. }
    { apply SI_ALin. }
    { intros v. apply SI_ALin. }
    { apply gt_read. }
    intros v. apply ret_step with (Y := ALin t (Semantics.ls_linr tgt v)).
    - intros s H. exact H.
    - reflexivity.
    - apply SI_ALin.
  Qed.

  Lemma dr_triple t l :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Pre t (tdr l) }} dr_impl l {{ Post t (tdr l) }}.
  Proof.
    unfold dr_impl.
    apply vis_step with (Y := fun v => ALin t (Semantics.ls_linr (tdr l) v)).
    { sonly. }
    { apply SI_ALin. }
    { intros v. apply SI_ALin. }
    { apply dr_read. }
    intros v. apply ret_step with (Y := ALin t (Semantics.ls_linr (tdr l) v)).
    - intros s H. exact H.
    - reflexivity.
    - apply SI_ALin.
  Qed.

  Lemma dw_triple t l a :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Pre t (tdw l a) }} dw_impl l a {{ Post t (tdw l a) }}.
  Proof.
    unfold dw_impl.
    apply vis_step_err with (X' := Pre t (tdw l a) //\\ Ho t) (Y := fun _ => ALin t (Semantics.ls_linr (tdw l a) tt)).
    { apply holder_split. intros x Hx. exact Hx. }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_Ho]. }
    { intros _. apply SI_ALin. }
    { apply dw_write. }
    intros _. apply ret_step with (Y := ALin t (Semantics.ls_linr (tdw l a) tt)).
    - intros s H. exact H.
    - reflexivity.
    - apply SI_ALin.
  Qed.

  (** ** Correctness over the memory with tickets *)

  Lemma ValidRGI_TL t : RGISimulation.ValidRGI (R t) (G t) I t.
  Proof.
    constructor. intros s s' HR _. destruct (R_cases _ _ _ HR) as [Hf _]. rewrite Hf. tauto.
  Qed.

  Lemma RG_compat t1 t2 :
    t1 <> t2 -> (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId) ⊆ R t2)%RGRelation.
  Proof.
    intros Hne s s' [HG | [[Hi | Hr] | Hid]].
    - left. exists t1. auto.
    - left. exists t1. auto.
    - left. exists t1. auto.
    - right. exact Hid.
  Qed.

  Lemma TLInv_init : TLInv (vinit MemHWg (hw_init, tk_init)) (vinit TLC tl_init).
  Proof.
    constructor; simpl.
    - apply Inv_init.
    - apply Inv_init.
    - reflexivity.
    - reflexivity.
    - apply Pos.le_refl.
    - intros h. auto.
    - split; reflexivity.
    - intros j t' H. discriminate.
    - reflexivity.
    - apply le_n.
    - intros h. apply le_n.
    - intros t' H. discriminate.
    - intros t o h [].
  Qed.

  Lemma method_provable t f :
    exists P Q, MethodProvable VE VF M_TL (R t) (G t) I t f P Q.
  Proof.
    exists (I //\\ Pre t f), (Post t f). constructor.
    - apply Pinv_gen.
    - intros s [HI _]. exact HI.
    - apply stable_I, SI_ALin.
    - intros ret. apply Qret_gen.
    - intros ret σ0 ρ0 π0 [_ H]. exact H.
    - destruct f as [ | | | l | l a].
      + exact (acq_triple t).
      + exact (rel_triple t).
      + exact (gt_triple t).
      + exact (dr_triple t l).
      + exact (dw_triple t l a).
  Qed.

  Theorem M_TL_ghost :
    TPSimulation.cal (VE := VL MemHWg) (VF := VL TLC) M_TL
      (Idle (vinit MemHWg (hw_init, tk_init))) (Idle (vinit TLC tl_init)).
  Proof.
    eapply RGILogic.soundness with (R := R) (G := G) (I := I).
    - exact ValidRGI_TL.
    - exact RG_compat.
    - exact method_provable.
    - exists (vinit TLC tl_init). split; [reflexivity | exact TLInv_init].
  Qed.

  (** ** The same proof over the plain memory *)

  Theorem M_TL_plain :
    TPSimulation.cal (VE := VL MemHW) (VF := VL TLC) M_TL
      (Idle (vinit MemHW hw_init)) (Idle (vinit TLC tl_init)).
  Proof.
    exact (ViewLiftGhost.cal_ghost_to_plain MemHW tk_up (VL TLC) M_TL hw_init tk_init
             (Idle (vinit TLC tl_init)) M_TL_ghost).
  Qed.
End TicketTowerLock.
