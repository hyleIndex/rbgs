(** * The SeqLock over the ticket lock, with the lock presented by its releases

    [M_SL] implements the record [RecP] over the ticket lock with data.

    - [rwrite a b]: [tacq; tdw dx a; tdw dy b; trel].
    - [rread]: read the version [s1]; if it is odd, retry; read the two
      data cells; read the version again; if it is still [s1], return the
      data, otherwise retry.

    The proof works over [VL TLCm]: the lock presented with the data
    published by its last release (the ghost [gh]).  The abstraction is
    then a plain equation between timelines, [si_rec]: at every
    timestamp the record holds the last released data.  The ghost is
    redundant here: by [si_rec] it equals the record's timeline, so the
    same proof works over [VL TLC] with [vs_tl RecP r h] in place of
    [gh v h].  It is kept to exhibit the two presentations of the lock.
    The reader's argument is an epoch argument on the version:

    - [si_mono]: the version never decreases along the timeline;
    - [si_epoch]: on an interval with constant version the last release
      is constant;
    - [si_free]: at an even version the data cells hold the last release.

    A successful reader read [s1] (even) at [h1] and again at [h4], and
    the data at [h2] and [h3], with [h1 < h2 < h3 < h4] by the dependency
    table of the lock.  So the version is [s1] on the whole interval, and
    the data it read is the last release at [h4].  Its linearization point
    is a retroactive read of the record at [h4].  The writer's is its
    [trel], appended at the same timestamp.

    Results:

    - [M_SL_ghost]: [cal] of [M_SL] from [VL TLCm] to [VL RecP];
    - [M_SL_plain]: the same over [VL TLC], by
      [ViewLiftGhost.cal_ghost_to_plain].  [TicketTowerLock] proves the
      ticket lock against [VL TLC], without the ghost.

    Underlay errors: [trel] and [tdw] are errors unless the caller holds
    the lock; [M_SL] calls them only while it holds it. *)

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

Module TicketTowerSeqLock.
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

  Definition write_impl (a b : nat) : Prog ETL unit :=
    tacq >= _ => tdw dx a >= _ => tdw dy b >= _ => trel >= _ => Ret tt.

  Definition read_tail (s1 : nat) : Prog ETL (unit + (nat * nat)) :=
    tdr dx >= a => tdr dy >= b => tgt >= s2 =>
    (if Nat.eqb s1 s2 then Ret (inr (a, b)) else Ret (inl tt)).

  Definition read_body : Prog ETL (unit + (nat * nat)) :=
    tgt >= s1 => (if Nat.even s1 then read_tail s1 else Ret (inl tt)).

  Definition read_impl : Prog ETL (nat * nat) := Do { read_body } Loop.

  Definition M_SL : ModuleImpl ETL ERec :=
    fun m _ =>
      match m as m0 return Prog ETL (RAr m0) with
      | rwrite a b => write_impl a b
      | rread => read_impl
      end.

  (** ** Lifted states *)

  Notation VE := (VL TLCm).
  Notation VF := (VL RecP).

  Definition assertion := @Assertion (@ProofState _ _ VE VF).
  Definition rg_relation := @RGRelation _ _ VE VF.

  Definition lk (v : VState TLCm) (h : Time) : TS := fst (vs_tl TLCm v h).
  Definition gh (v : VState TLCm) (h : Time) : nat * nat := snd (vs_tl TLCm v h).
  Definition lkc (v : VState TLCm) : TS := fst (cur TLCm v).
  Definition ghc (v : VState TLCm) : nat * nat := snd (cur TLCm v).

  (** The record operation and the lock operation at the same timestamp. *)
  Variant racc : ROp -> TOp -> Prop :=
  | racc_w a b : racc (rwrite a b) trel
  | racc_r : racc rread tgt.

  Record SLInv (v : VState TLCm) (r : VState RecP) : Prop := {
    si_invv : Inv TLCm v;
    si_invr : Inv RecP r;
    si_flv : vs_floor TLCm v = xH;
    si_flr : vs_floor RecP r = xH;
    si_hor : Pos.le (vs_hor RecP r) (vs_hor TLCm v);
    si_rec : forall h, vs_tl RecP r h = gh v h;
    si_free : forall h, Nat.even (tv (lk v h)) = true -> (tx (lk v h), ty (lk v h)) = gh v h;
    si_mono : forall h h', Pos.le h h' -> tv (lk v h) <= tv (lk v h');
    si_epoch : forall h h', Pos.le h h' -> tv (lk v h) = tv (lk v h') -> gh v h = gh v h';
    si_par : th (lkc v) = None <-> Nat.even (tv (lkc v)) = true;
    si_past : PastRel TLCm RecP racc v r;
  }.

  Definition U (s : @ProofState _ _ VE VF) : VState TLCm := state (σ s).

  Definition I : assertion :=
    fun s => exists r, ρ s = Idle r /\ SLInv (U s) r.

  (** ** Guarantee and rely *)

  Definition G (t : tid) : rg_relation :=
    fun s1 s2 =>
      (forall t', t' <> t -> TMap.find t' (π s2) = TMap.find t' (π s1)) /\
      VLMove TLCm t (state (σ s1)) (state (σ s2)) /\
      VLMove RecP t (state (ρ s1)) (state (ρ s2)).

  Definition R (t : tid) : rg_relation :=
    fun s1 s2 =>
      (exists t1, t1 <> t /\ (G t1 s1 s2 \/ GINV t1 s1 s2 \/ GRET t1 s1 s2)) \/ s1 = s2.

  Lemma succ_neq (t : tid) : Pos.succ t <> t.
  Proof. intros H. pose proof (Pos.lt_succ_diag_r t). rewrite H in H0. exact (Pos.lt_irrefl _ H0). Qed.

  Lemma R_cases t s1 s2 :
    R t s1 s2 ->
    TMap.find t (π s2) = TMap.find t (π s1) /\
    exists t1, t1 <> t /\
      VLMove TLCm t1 (state (σ s1)) (state (σ s2)) /\
      VLMove RecP t1 (state (ρ s1)) (state (ρ s2)).
  Proof.
    intros [(t1 & Hne & [(Hpi & Hu & Ho) | [(f & Hs & Hr & _ & Hp) | (f & ret & Hs & Hr & _ & Hp)]]) | <-].
    - split; [apply Hpi; congruence|]. exists t1. auto.
    - split; [rewrite Hp, TMap.gso by congruence; reflexivity|].
      exists t1. rewrite Hs, Hr. split; [exact Hne | split; apply vlmove_refl].
    - split; [rewrite Hp, TMap.gro by congruence; reflexivity|].
      exists t1. rewrite Hs, Hr. split; [exact Hne | split; apply vlmove_refl].
    - split; [reflexivity|]. exists (Pos.succ t). split; [apply succ_neq | split; apply vlmove_refl].
  Qed.

  (** ** Steps of the lock *)

  Lemma tlcm_spec_acq (s : vl_state TLCm) t r (st : vl_state TLCm) :
    vl_spec TLCm s t tacq r st ->
    th (fst s) = None /\ st = (mkTS (S (tv (fst s))) (Some t) (tx (fst s)) (ty (fst s)), snd s).
  Proof. destruct st as [st g]. intros ((H1 & H2) & H3). simpl in H2, H3. subst. auto. Qed.

  Lemma tlcm_spec_rel (s : vl_state TLCm) t r (st : vl_state TLCm) :
    vl_spec TLCm s t trel r st ->
    th (fst s) = Some t /\ st = (mkTS (S (tv (fst s))) None (tx (fst s)) (ty (fst s)), (tx (fst s), ty (fst s))).
  Proof. destruct st as [st g]. intros ((H1 & H2) & H3). simpl in H2, H3. subst. auto. Qed.

  Lemma tlcm_spec_dw (s : vl_state TLCm) t l a r (st : vl_state TLCm) :
    vl_spec TLCm s t (tdw l a) r st ->
    th (fst s) = Some t /\ st = (tset (fst s) l a, snd s).
  Proof. destruct st as [st g]. intros ((H1 & H2) & H3). simpl in H2, H3. subst. auto. Qed.

  Lemma tlcm_spec_gt (s : vl_state TLCm) t (r : nat) (st : vl_state TLCm) :
    vl_spec TLCm s t tgt r st -> r = tv (fst s).
  Proof. destruct st as [st g]. intros ((H1 & H2) & H3). exact H1. Qed.

  Lemma tlcm_spec_dr (s : vl_state TLCm) t l (r : nat) (st : vl_state TLCm) :
    vl_spec TLCm s t (tdr l) r st -> r = tdat (fst s) l.
  Proof. destruct st as [st g]. intros ((H1 & H2) & H3). exact H1. Qed.

  (** Another thread cannot take, release, or write under a lock held by [t]. *)
  Lemma vlmove_holder t1 t v v' :
    t1 <> t -> Inv TLCm v -> VLMove TLCm t1 v v' -> th (lkc v) = Some t -> cur TLCm v' = cur TLCm v.
  Proof.
    intros Hne HI [-> | (m & r & Hs)] Hh; [reflexivity|].
    destruct (vstep_res_cur TLCm t1 m r v v' HI Hs) as [(_ & Hc) | (Hretro & Hspec)]; [exact Hc|].
    unfold lkc in Hh. destruct m as [ | | | l | l a]; simpl in Hretro; try discriminate.
    - apply tlcm_spec_acq in Hspec as (Hn & _). congruence.
    - apply tlcm_spec_rel in Hspec as (Hn & _). congruence.
    - apply tlcm_spec_dw in Hspec as (Hn & _). congruence.
  Qed.

  (** ** Preservation of the invariant *)

  Lemma pos_le_gt (h1 h2 : positive) : Pos.le h1 h2 \/ Pos.lt h2 h1.
  Proof. lia. Qed.

  Section Facts.
    Context (v : VState TLCm) (r : VState RecP) (HS : SLInv v r).

    Lemma lk_above h : Pos.le (vs_hor TLCm v) h -> lk v h = lkc v.
    Proof. intros Hh. unfold lk, lkc. rewrite (tl_above TLCm v h (si_invv _ _ HS) Hh). reflexivity. Qed.

    Lemma gh_above h : Pos.le (vs_hor TLCm v) h -> gh v h = ghc v.
    Proof. intros Hh. unfold gh, ghc. rewrite (tl_above TLCm v h (si_invv _ _ HS) Hh). reflexivity. Qed.

    Lemma mono_cur h : tv (lk v h) <= tv (lkc v).
    Proof.
      destruct (pos_le_gt h (vs_hor TLCm v)) as [Hle | Hgt].
      - rewrite <- (lk_above (vs_hor TLCm v)) by apply Pos.le_refl. exact (si_mono _ _ HS _ _ Hle).
      - rewrite lk_above by (apply Pos.lt_le_incl; exact Hgt). lia.
    Qed.

    Lemma epoch_cur h : tv (lk v h) = tv (lkc v) -> gh v h = ghc v.
    Proof.
      intros Heq. destruct (pos_le_gt h (vs_hor TLCm v)) as [Hle | Hgt].
      - rewrite <- (gh_above (vs_hor TLCm v)) by apply Pos.le_refl.
        apply (si_epoch _ _ HS _ _ Hle). rewrite (lk_above (vs_hor TLCm v)) by apply Pos.le_refl. exact Heq.
      - apply gh_above. apply Pos.lt_le_incl. exact Hgt.
    Qed.

    Lemma rec_cur : cur RecP r = ghc v.
    Proof.
      rewrite <- (tl_above RecP r (vs_hor TLCm v) (si_invr _ _ HS) (si_hor _ _ HS)).
      rewrite (si_rec _ _ HS). apply gh_above. apply Pos.le_refl.
    Qed.

    Lemma rec_above h : Pos.le (vs_hor TLCm v) h -> vs_tl RecP r h = ghc v.
    Proof. intros Hh. rewrite (si_rec _ _ HS). apply gh_above. exact Hh. Qed.
  End Facts.

  (** A retroactive step of the lock, the record unchanged. *)
  Lemma SLInv_retro v r t m (ret : Sig.ar m) v' :
    SLInv v r -> VStep TLCm (Build_ThreadEvent t (ResEv m ret)) v v' -> vl_retro TLCm m = true ->
    SLInv v' r.
  Proof.
    intros HS Hs Hr.
    destruct (vstep_res_cases TLCm t m ret v v' Hs)
      as [ (_ & h & Hfloor & Hdep & Hspec & ->) | (Hr' & _) ]; [|congruence].
    pose proof (VStep_Inv TLCm _ _ _ Hs (si_invv _ _ HS)) as HI'.
    assert (Hcur : cur TLCm (upd_retro TLCm v t m h) = cur TLCm v) by (apply cur_retro, (si_invv _ _ HS)).
    constructor; simpl; try exact HI'.
    - exact (si_invr _ _ HS).
    - exact (si_flv _ _ HS).
    - exact (si_flr _ _ HS).
    - eapply Pos.le_trans; [exact (si_hor _ _ HS) | apply Pos.le_max_l].
    - exact (si_rec _ _ HS).
    - exact (si_free _ _ HS).
    - exact (si_mono _ _ HS).
    - exact (si_epoch _ _ HS).
    - unfold lkc. rewrite Hcur. exact (si_par _ _ HS).
    - intros t' o h' Hin. destruct (si_past _ _ HS t' o h' Hin) as (o' & Hin' & Hacc).
      exists o'. split; [|exact Hacc]. simpl. unfold push_past.
      destruct (Pos.eqb t t'); [right|]; exact Hin'.
  Qed.

  (** A retroactive [tgt] at [h] with the record read at [h]. *)
  Lemma SLInv_read v r t h :
    SLInv v r -> Inv TLCm (upd_retro TLCm v t tgt h) -> Inv RecP (upd_retro RecP r t rread h) ->
    SLInv (upd_retro TLCm v t tgt h) (upd_retro RecP r t rread h).
  Proof.
    intros HS HI HIr.
    assert (Hcur : cur TLCm (upd_retro TLCm v t tgt h) = cur TLCm v) by (apply cur_retro, (si_invv _ _ HS)).
    constructor; simpl; try exact HI; try exact HIr.
    - exact (si_flv _ _ HS).
    - exact (si_flr _ _ HS).
    - apply Pos.max_le_compat; [exact (si_hor _ _ HS) | apply Pos.le_refl].
    - exact (si_rec _ _ HS).
    - exact (si_free _ _ HS).
    - exact (si_mono _ _ HS).
    - exact (si_epoch _ _ HS).
    - unfold lkc. rewrite Hcur. exact (si_par _ _ HS).
    - eapply (PastRel_push TLCm RecP racc v r t rread tgt h (si_past _ _ HS) racc_r);
        intros; reflexivity.
  Qed.

  (** Appended steps of the lock.  [st] is the new current state. *)
  Section App.
    Context (v : VState TLCm) (r : VState RecP) (HS : SLInv v r).
    Context (t : tid) (m : TOp) (h : Time) (st : vl_state TLCm).
    Context (Hhor : Pos.lt (vs_hor TLCm v) h).
    Context (HI' : Inv TLCm (upd_app TLCm v t m h st)).
    Context (Hmono : tv (lkc v) <= tv (fst st)).
    Context (Hepoch : tv (fst st) = tv (lkc v) -> snd st = ghc v).
    Context (Hfree : Nat.even (tv (fst st)) = true -> (tx (fst st), ty (fst st)) = snd st).
    Context (Hpar : th (fst st) = None <-> Nat.even (tv (fst st)) = true).

    Let v' := upd_app TLCm v t m h st.

    Lemma lk_app h' : lk v' h' = if Pos.leb h h' then fst st else lk v h'.
    Proof using. unfold lk, v'. simpl. unfold tl_write. destruct (Pos.leb h h'); reflexivity. Qed.

    Lemma gh_app h' : gh v' h' = if Pos.leb h h' then snd st else gh v h'.
    Proof using. unfold gh, v'. simpl. unfold tl_write. destruct (Pos.leb h h'); reflexivity. Qed.

    Lemma app_mono : forall h1 h2, Pos.le h1 h2 -> tv (lk v' h1) <= tv (lk v' h2).
    Proof using HS Hmono.
      clear Hepoch Hfree Hpar.
      intros h1 h2 Hle. rewrite !lk_app.
      destruct (Pos.leb h h1) eqn:H1, (Pos.leb h h2) eqn:H2.
      - lia.
      - apply Pos.leb_le in H1. apply Pos.leb_nle in H2. exfalso. apply H2. eapply Pos.le_trans; eauto.
      - pose proof (mono_cur v r HS h1). lia.
      - exact (si_mono _ _ HS _ _ Hle).
    Qed.

    Lemma app_epoch : forall h1 h2, Pos.le h1 h2 -> tv (lk v' h1) = tv (lk v' h2) -> gh v' h1 = gh v' h2.
    Proof using HS Hmono Hepoch.
      clear Hfree Hpar.
      intros h1 h2 Hle Heq. rewrite !lk_app in Heq. rewrite !gh_app.
      destruct (Pos.leb h h1) eqn:H1, (Pos.leb h h2) eqn:H2.
      - reflexivity.
      - apply Pos.leb_le in H1. apply Pos.leb_nle in H2. exfalso. apply H2. eapply Pos.le_trans; eauto.
      - pose proof (mono_cur v r HS h1).
        assert (Hc : tv (fst st) = tv (lkc v)) by lia.
        rewrite (Hepoch Hc). apply (epoch_cur v r HS). lia.
      - exact (si_epoch _ _ HS _ _ Hle Heq).
    Qed.

    Lemma app_free : forall h', Nat.even (tv (lk v' h')) = true -> (tx (lk v' h'), ty (lk v' h')) = gh v' h'.
    Proof using HS Hfree.
      intros h'. rewrite lk_app, gh_app. destruct (Pos.leb h h'); [exact (Hfree) | exact (si_free _ _ HS h')].
    Qed.

    Lemma app_par : th (lkc v') = None <-> Nat.even (tv (lkc v')) = true.
    Proof using Hpar. unfold lkc, v'. rewrite cur_app. exact Hpar. Qed.
  End App.

  (** [tacq] or [tdw]: the record is unchanged. *)
  Lemma SLInv_app_same v r t m h st :
    SLInv v r -> Pos.lt (vs_hor TLCm v) h -> Inv TLCm (upd_app TLCm v t m h st) ->
    tv (lkc v) <= tv (fst st) ->
    snd st = ghc v ->
    (Nat.even (tv (fst st)) = true -> (tx (fst st), ty (fst st)) = snd st) ->
    (th (fst st) = None <-> Nat.even (tv (fst st)) = true) ->
    SLInv (upd_app TLCm v t m h st) r.
  Proof.
    intros HS Hhor HI' Hmono Hg Hfree Hpar.
    constructor.
    - exact HI'.
    - exact (si_invr _ _ HS).
    - simpl. exact (si_flv _ _ HS).
    - exact (si_flr _ _ HS).
    - simpl. eapply Pos.le_trans; [exact (si_hor _ _ HS) | apply Pos.lt_le_incl; exact Hhor].
    - intros h'. rewrite (gh_app v t m h st). destruct (Pos.leb h h') eqn:Hb.
      + apply Pos.leb_le in Hb. rewrite Hg. apply (rec_above v r HS).
        apply Pos.lt_le_incl. eapply Pos.lt_le_trans; eauto.
      + exact (si_rec _ _ HS h').
    - exact (app_free v r HS t m h st Hfree).
    - exact (app_mono v r HS t m h st Hmono).
    - apply (app_epoch v r HS t m h st Hmono). intros _. exact Hg.
    - exact (app_par v t m h st Hpar).
    - intros t' o h' Hin. destruct (si_past _ _ HS t' o h' Hin) as (o' & Hin' & Hacc).
      exists o'. split; [|exact Hacc]. simpl. unfold push_past.
      destruct (Pos.eqb t t'); [right|]; exact Hin'.
  Qed.

  (** [trel] at [h], with the record written at [h]. *)
  Lemma SLInv_app_rel v r t h st a b :
    SLInv v r -> Pos.lt (vs_hor TLCm v) h -> Inv TLCm (upd_app TLCm v t trel h st) ->
    Inv RecP (upd_app RecP r t (rwrite a b) h (a, b)) ->
    tv (lkc v) < tv (fst st) ->
    snd st = (a, b) ->
    (Nat.even (tv (fst st)) = true -> (tx (fst st), ty (fst st)) = snd st) ->
    (th (fst st) = None <-> Nat.even (tv (fst st)) = true) ->
    SLInv (upd_app TLCm v t trel h st) (upd_app RecP r t (rwrite a b) h (a, b)).
  Proof.
    intros HS Hhor HI' HIr Hlt Hg Hfree Hpar.
    assert (Hmono : tv (lkc v) <= tv (fst st)) by lia.
    constructor.
    - exact HI'.
    - exact HIr.
    - simpl. exact (si_flv _ _ HS).
    - simpl. exact (si_flr _ _ HS).
    - simpl. apply Pos.le_refl.
    - intros h'. rewrite (gh_app v t trel h st). simpl. unfold tl_write.
      destruct (Pos.leb h h'); [symmetry; exact Hg | exact (si_rec _ _ HS h')].
    - exact (app_free v r HS t trel h st Hfree).
    - exact (app_mono v r HS t trel h st Hmono).
    - apply (app_epoch v r HS t trel h st Hmono). intros Heq. lia.
    - exact (app_par v t trel h st Hpar).
    - eapply (PastRel_push TLCm RecP racc v r t (rwrite a b) trel h (si_past _ _ HS) (racc_w a b));
        intros; reflexivity.
  Qed.

  (** ** Assertions *)

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition Hold (t : tid) : assertion := fun s => th (lkc (U s)) = Some t.
  Definition WX (a : nat) : assertion := fun s => tx (lkc (U s)) = a.
  Definition WY (b : nat) : assertion := fun s => ty (lkc (U s)) = b.

  (** The reader read the version [s1] at [h1] and the data at [h2], [h3]. *)
  Definition RG1 (t : tid) (s1 : nat) : assertion :=
    fun s => exists h1, In (tgt, h1) (vs_past TLCm (U s) t) /\ tv (lk (U s) h1) = s1.

  Definition RG2 (t : tid) (s1 a : nat) : assertion :=
    fun s => exists h1 h2, In (tdr dx, h2) (vs_past TLCm (U s) t) /\ Pos.lt h1 h2 /\
      tv (lk (U s) h1) = s1 /\ tx (lk (U s) h2) = a.

  Definition RG3 (t : tid) (s1 a b : nat) : assertion :=
    fun s => exists h1 h2 h3, In (tdr dy, h3) (vs_past TLCm (U s) t) /\ Pos.lt h1 h2 /\ Pos.lt h2 h3 /\
      tv (lk (U s) h1) = s1 /\ tx (lk (U s) h2) = a /\ ty (lk (U s) h3) = b.

  (** Stability of a fact in the presence of the invariant. *)
  Definition SI (t : tid) (X : assertion) : Prop :=
    forall s0 s, I s0 -> X s0 -> R t s0 s -> I s -> X s.

  Lemma stable_I t X : SI t X -> Stable (R t) I (I //\\ X).
  Proof. intros HX s [(s0 & (HI0 & HX0) & HR) HI]. split; [exact HI | exact (HX s0 s HI0 HX0 HR HI)]. Qed.

  Lemma SI_conj t X Y : SI t X -> SI t Y -> SI t (X //\\ Y).
  Proof. intros HX HY s0 s HI0 [Hx Hy] HR HI. split; [exact (HX _ _ HI0 Hx HR HI) | exact (HY _ _ HI0 Hy HR HI)]. Qed.

  Lemma SI_ALin t ls : SI t (ALin t ls).
  Proof. intros s0 s _ H HR _. unfold ALin in *. destruct (R_cases _ _ _ HR) as [-> _]. exact H. Qed.

  Lemma I_inv s : I s -> Inv TLCm (U s).
  Proof. intros (r & _ & HS). exact (si_invv _ _ HS). Qed.

  (** The past of [t] and the timeline below the horizon are kept. *)
  Lemma R_keep t s0 s :
    R t s0 s -> I s0 ->
    vs_past TLCm (U s) t = vs_past TLCm (U s0) t /\
    (forall h, Pos.le h (vs_hor TLCm (U s0)) -> vs_tl TLCm (U s) h = vs_tl TLCm (U s0) h).
  Proof.
    intros HR HI0. destruct (R_cases _ _ _ HR) as (_ & t1 & Hne & Hu & _).
    split; [exact (vlmove_past TLCm t1 t _ _ Hne Hu) | intros h Hh; exact (vlmove_tl_old TLCm t1 _ _ h Hu Hh)].
  Qed.

  Lemma R_hold t s0 s : R t s0 s -> I s0 -> Hold t s0 -> cur TLCm (U s) = cur TLCm (U s0).
  Proof.
    intros HR HI0 Hh. destruct (R_cases _ _ _ HR) as (_ & t1 & Hne & Hu & _).
    exact (vlmove_holder t1 t _ _ Hne (I_inv _ HI0) Hu Hh).
  Qed.

  Lemma SI_Hold t : SI t (Hold t).
  Proof. intros s0 s HI0 Hh HR _. unfold Hold, lkc in *. rewrite (R_hold _ _ _ HR HI0 Hh). exact Hh. Qed.

  Lemma SI_HoldXY t a b : SI t (Hold t //\\ WX a //\\ WY b).
  Proof.
    intros s0 s HI0 (Hh & Hx & Hy) HR _. pose proof (R_hold _ _ _ HR HI0 Hh) as Hc.
    unfold Hold, WX, WY, lkc in *. split; [|split]; rewrite Hc; assumption.
  Qed.

  Lemma SI_HoldX t a : SI t (Hold t //\\ WX a).
  Proof.
    intros s0 s HI0 (Hh & Hx) HR _. pose proof (R_hold _ _ _ HR HI0 Hh) as Hc.
    unfold Hold, WX, lkc in *. split; rewrite Hc; assumption.
  Qed.

  Lemma past_hor s t o h : I s -> In (o, h) (vs_past TLCm (U s) t) -> Pos.le h (vs_hor TLCm (U s)).
  Proof. intros HI Hin. exact (past_le_hor TLCm _ _ _ _ (I_inv _ HI) Hin). Qed.

  Lemma SI_RG1 t s1 : SI t (RG1 t s1).
  Proof.
    intros s0 s HI0 (h1 & Hin & Hv) HR _. destruct (R_keep _ _ _ HR HI0) as (Hp & Htl).
    exists h1. rewrite Hp. split; [exact Hin|].
    unfold lk. rewrite Htl by exact (past_hor _ _ _ _ HI0 Hin). exact Hv.
  Qed.

  Lemma SI_RG2 t s1 a : SI t (RG2 t s1 a).
  Proof.
    intros s0 s HI0 (h1 & h2 & Hin & Hlt & Hv & Ha) HR _. destruct (R_keep _ _ _ HR HI0) as (Hp & Htl).
    pose proof (past_hor _ _ _ _ HI0 Hin) as H2.
    exists h1, h2. rewrite Hp. unfold lk in *.
    rewrite !Htl by (try exact H2; apply Pos.lt_le_incl; eapply Pos.lt_le_trans; eauto). auto.
  Qed.

  Lemma SI_RG3 t s1 a b : SI t (RG3 t s1 a b).
  Proof.
    intros s0 s HI0 (h1 & h2 & h3 & Hin & H12 & H23 & Hv & Ha & Hb) HR _.
    destruct (R_keep _ _ _ HR HI0) as (Hp & Htl).
    pose proof (past_hor _ _ _ _ HI0 Hin) as H3.
    assert (H2 : Pos.le h2 (vs_hor TLCm (U s0))) by (apply Pos.lt_le_incl; eapply Pos.lt_le_trans; eauto).
    assert (H1 : Pos.le h1 (vs_hor TLCm (U s0))) by (apply Pos.lt_le_incl; eapply Pos.lt_le_trans; eauto).
    exists h1, h2, h3. rewrite Hp. unfold lk in *. rewrite !Htl by assumption. auto 7.
  Qed.

  (** ** Generic possibility updates *)

  (** An invocation leaves every assertion of this file true. *)
  Definition SOnly (X : assertion) : Prop :=
    forall (σ1 σ2 : State VE) (ρ0 : State VF) (π0 : tmap (@Semantics.LinState ERec)),
      state σ2 = state σ1 -> X (σ1, ρ0, π0) -> X (σ2, ρ0, π0).

  Lemma pupdate_inv t m X :
    SOnly X -> PUpdate (G t) (Build_ThreadEvent t (InvEv m)) (I //\\ X) (I //\\ X).
  Proof.
    intros HX σ0 ρ0 π0 [HI Hx] σ1 Hs.
    destruct (astep_inv_cases TLCm t m σ0 σ1 Hs) as (v & -> & ->).
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact HI | exact (HX (Idle v) (Pending v t m) ρ0 π0 eq_refl Hx)].
    - split; [intros; reflexivity | split; apply vlmove_refl].
  Qed.

  Ltac sonly :=
    let Heqs := fresh "Heqs" in let HX := fresh "HX" in
    intros ? ? ? ? Heqs HX;
    unfold Conj, ALin, Hold, WX, WY, RG1, RG2, RG3, U in *; cbn [σ ρ π] in *;
    rewrite ?Heqs; exact HX.

  Lemma noerror t m s : ~ vl_err TLCm t m (cur TLCm (U s)) -> ANoError (Build_ThreadEvent t (InvEv m)) s.
  Proof.
    intros Hne He. unfold U in Hne. destruct s as [σ0 ρ0 π0]. simpl in *.
    inversion He as [ev v Herr]; subst. simpl in Hne. exact (Hne Herr).
  Qed.

  (** ** The steps of the lock, on the invariant *)

  Lemma tv_tset (x : TS) l c : tv (tset x l c) = tv x.
  Proof. destruct l; reflexivity. Qed.

  Lemma th_tset (x : TS) l c : th (tset x l c) = th x.
  Proof. destruct l; reflexivity. Qed.

  Lemma holder_odd v r t : SLInv v r -> th (lkc v) = Some t -> Nat.even (tv (lkc v)) = false.
  Proof.
    intros HS Hh. destruct (Nat.even (tv (lkc v))) eqn:He; [|reflexivity].
    apply (si_par _ _ HS) in He. congruence.
  Qed.

  Lemma acq_post v r t ret v' :
    SLInv v r -> VStep TLCm (Build_ThreadEvent t (ResEv tacq ret)) v v' ->
    SLInv v' r /\ th (lkc v') = Some t.
  Proof.
    intros HS Hv.
    destruct (vstep_res_cases TLCm t tacq ret v v' Hv)
      as [ (Hr & _) | (_ & h & st & Hhor & Hdep & Hspec & ->) ]; [discriminate|].
    apply (spec_app_cur TLCm v t tacq ret h st (si_invv _ _ HS) Hhor) in Hspec.
    destruct (tlcm_spec_acq _ _ _ _ Hspec) as (Hfree & ->).
    pose proof (proj1 (si_par _ _ HS) Hfree) as Hev.
    split.
    - apply SLInv_app_same; [exact HS | exact Hhor | exact (VStep_Inv TLCm _ _ _ Hv (si_invv _ _ HS))
                            | unfold lkc; cbn [fst snd tv th tx ty]; lia | reflexivity | | ]; cbn [fst snd tv th tx ty].
      + rewrite even_odd_succ. unfold lkc in Hev. rewrite Hev. discriminate.
      + rewrite even_odd_succ. unfold lkc in Hev. rewrite Hev. split; discriminate.
    - unfold lkc. rewrite cur_app. reflexivity.
  Qed.

  Lemma dw_post v r t l c ret v' :
    SLInv v r -> th (lkc v) = Some t -> VStep TLCm (Build_ThreadEvent t (ResEv (tdw l c) ret)) v v' ->
    SLInv v' r /\ lkc v' = tset (lkc v) l c.
  Proof.
    intros HS Hh Hv. pose proof (holder_odd _ _ _ HS Hh) as Hodd.
    destruct (vstep_res_cases TLCm t (tdw l c) ret v v' Hv)
      as [ (Hr & _) | (_ & h & st & Hhor & Hdep & Hspec & ->) ]; [discriminate|].
    apply (spec_app_cur TLCm v t (tdw l c) ret h st (si_invv _ _ HS) Hhor) in Hspec.
    destruct (tlcm_spec_dw _ _ _ _ _ _ Hspec) as (_ & ->).
    split.
    - unfold lkc in Hodd, Hh.
      apply SLInv_app_same; [exact HS | exact Hhor | exact (VStep_Inv TLCm _ _ _ Hv (si_invv _ _ HS))
                            | unfold lkc; cbn [fst snd]; rewrite tv_tset; lia | reflexivity | | ];
        cbn [fst snd]; rewrite tv_tset, Hodd.
      + discriminate.
      + rewrite th_tset, Hh. split; discriminate.
    - unfold lkc. rewrite cur_app. reflexivity.
  Qed.

  Lemma rel_dep r v t (a b : nat) h :
    SLInv v r -> dep_ok TLCm v t trel h -> dep_ok RecP r t (rwrite a b) h.
  Proof.
    intros HS Hd. eapply (dep_ok_transfer TLCm RecP racc v r t (rwrite a b) trel h (si_past _ _ HS)); [|exact Hd].
    intros o o' _ _. destruct o'; reflexivity.
  Qed.

  Lemma read_dep r v t h :
    SLInv v r -> dep_ok TLCm v t tgt h -> dep_ok RecP r t rread h.
  Proof.
    intros HS Hd. eapply (dep_ok_transfer TLCm RecP racc v r t rread tgt h (si_past _ _ HS)); [|exact Hd].
    intros o o' Hacc _. destruct Hacc; reflexivity.
  Qed.

  (** ** Possibility updates of the writer *)

  Definition WPre (t : tid) (a b : nat) : assertion := ALin t (Semantics.ls_inv (rwrite a b)).

  Lemma I_step (ρ0 : State VF) (π0 : tmap (@Semantics.LinState ERec)) r v' :
    ρ0 = Idle r -> SLInv v' r -> I ((Idle v' : State VE), ρ0, π0).
  Proof. intros -> HS. exists r. split; [reflexivity | exact HS]. Qed.

  Lemma G_under t (σ0 σ1 : State VE) (ρ0 : State VF) π0 v v' m (ret : Sig.ar m) :
    state σ0 = v -> state σ1 = v' -> VStep TLCm (Build_ThreadEvent t (ResEv m ret)) v v' ->
    G t (σ0, ρ0, π0) (σ1, ρ0, π0).
  Proof.
    intros H0 H1 Hv. split; [intros; reflexivity|]. simpl. rewrite H0, H1.
    split; [exact (vlmove_step TLCm t m ret v v' Hv) | apply vlmove_refl].
  Qed.

  Lemma wr_acq t a b ret :
    PUpdate (G t) (Build_ThreadEvent t (ResEv tacq ret))
      (I //\\ WPre t a b) (I //\\ (WPre t a b //\\ Hold t)).
  Proof.
    intros σ0 ρ0 π0 [(r & Hρ & HS) Hlin] σ1 Hs.
    destruct (astep_res_cases TLCm t tacq ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold U in HS; simpl in HS.
    destruct (acq_post v r t ret v' HS Hv) as (HS' & Hh).
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ r v' Hρ HS') | split; [exact Hlin | exact Hh]].
    - exact (G_under t (Pending v t tacq) (Idle v') ρ0 π0 v v' tacq ret eq_refl eq_refl Hv).
  Qed.

  Lemma wr_dwx t a b ret :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (tdw dx a) ret))
      (I //\\ (WPre t a b //\\ Hold t)) (I //\\ (WPre t a b //\\ (Hold t //\\ WX a))).
  Proof.
    intros σ0 ρ0 π0 [(r & Hρ & HS) (Hlin & Hh)] σ1 Hs.
    destruct (astep_res_cases TLCm t (tdw dx a) ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold U, Hold in *; simpl in *.
    destruct (dw_post v r t dx a ret v' HS Hh Hv) as (HS' & Hc).
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ r v' Hρ HS') | split; [exact Hlin|]].
      split; unfold Hold, WX, U; cbn [σ state]; rewrite Hc; [rewrite th_tset; exact Hh | reflexivity].
    - exact (G_under t (Pending v t (tdw dx a)) (Idle v') ρ0 π0 v v' (tdw dx a) ret eq_refl eq_refl Hv).
  Qed.

  Lemma wr_dwy t a b ret :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (tdw dy b) ret))
      (I //\\ (WPre t a b //\\ (Hold t //\\ WX a)))
      (I //\\ (WPre t a b //\\ (Hold t //\\ WX a //\\ WY b))).
  Proof.
    intros σ0 ρ0 π0 [(r & Hρ & HS) (Hlin & Hh & Hx)] σ1 Hs.
    destruct (astep_res_cases TLCm t (tdw dy b) ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold U, Hold, WX in *; simpl in *.
    destruct (dw_post v r t dy b ret v' HS Hh Hv) as (HS' & Hc).
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ r v' Hρ HS') | split; [exact Hlin|]].
      split; [|split]; unfold Hold, WX, WY, U; cbn [σ state]; rewrite Hc;
        [rewrite th_tset; exact Hh | exact Hx | reflexivity].
    - exact (G_under t (Pending v t (tdw dy b)) (Idle v') ρ0 π0 v v' (tdw dy b) ret eq_refl eq_refl Hv).
  Qed.

  Lemma wr_rel t a b ret :
    PUpdate (G t) (Build_ThreadEvent t (ResEv trel ret))
      (I //\\ (WPre t a b //\\ (Hold t //\\ WX a //\\ WY b)))
      (I //\\ ALin t (Semantics.ls_linr (rwrite a b) tt)).
  Proof.
    intros σ0 ρ0 π0 [(r & Hρ & HS) (Hlin & Hh & Hx & Hy)] σ1 Hs.
    destruct (astep_res_cases TLCm t trel ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold Hold, WX, WY, U in Hh, Hx, Hy, HS. cbn [σ ρ state] in Hh, Hx, Hy, HS, Hρ.
    pose proof (holder_odd _ _ _ HS Hh) as Hodd.
    unfold lkc in Hh, Hx, Hy, Hodd.
    destruct (vstep_res_cases TLCm t trel ret v v' Hv)
      as [ (Hr & _) | (_ & h & st & Hhor & Hdep & Hspec & ->) ]; [discriminate|].
    apply (spec_app_cur TLCm v t trel ret h st (si_invv _ _ HS) Hhor) in Hspec.
    destruct (tlcm_spec_rel _ _ _ _ Hspec) as (_ & ->).
    assert (Hvr : VStep RecP (Build_ThreadEvent t (ResEv (rwrite a b) tt)) r
                    (upd_app RecP r t (rwrite a b) h (a, b))).
    { refine (vstep_app RecP t (rwrite a b) tt h (a, b) r _ _ eq_refl eq_refl _ (rel_dep r v t a b h HS Hdep) eq_refl eq_refl).
      eapply Pos.le_lt_trans; [exact (si_hor _ _ HS) | exact Hhor]. }
    exists (Idle (upd_app RecP r t (rwrite a b) h (a, b))),
      (TMap.add t (Semantics.ls_linr (rwrite a b) tt) (TMap.add t (Semantics.ls_lini (rwrite a b)) π0)).
    split; [rewrite Hρ; exact (vl_lp RecP r _ t (rwrite a b) tt π0 Hlin Hvr)|]. split.
    - split; [|apply vl_lp_find].
      exists (upd_app RecP r t (rwrite a b) h (a, b)). split; [reflexivity|]. unfold U. cbn [σ state].
      apply SLInv_app_rel; [exact HS | exact Hhor | exact (VStep_Inv TLCm _ _ _ Hv (si_invv _ _ HS))
                           | exact (VStep_Inv RecP _ _ _ Hvr (si_invr _ _ HS))
                           | unfold lkc; cbn [fst snd tv]; lia
                           | cbn [fst snd]; rewrite Hx, Hy; reflexivity | cbn [fst snd tx ty]; reflexivity | ].
      cbn [fst snd tv th]. rewrite even_odd_succ, Hodd. split; reflexivity.
    - split; [intros t' Hne; apply vl_lp_find_other; exact Hne|]. simpl.
      split; [exact (vlmove_step TLCm t trel ret v _ Hv) | rewrite Hρ; exact (vlmove_step RecP t (rwrite a b) tt r _ Hvr)].
  Qed.

  (** ** Possibility updates of the reader *)

  Definition RPre (t : tid) : assertion := ALin t (Semantics.ls_inv rread).

  Lemma retro_post v r t m ret v' :
    SLInv v r -> VStep TLCm (Build_ThreadEvent t (ResEv m ret)) v v' -> vl_retro TLCm m = true ->
    exists h, Pos.lt xH h /\ dep_ok TLCm v t m h /\ vl_spec TLCm (vs_tl TLCm v h) t m ret (vs_tl TLCm v h) /\
      v' = upd_retro TLCm v t m h /\ SLInv v' r.
  Proof.
    intros HS Hv Hr. pose proof (SLInv_retro v r t m ret v' HS Hv Hr) as HS'.
    destruct (vstep_res_cases TLCm t m ret v v' Hv)
      as [ (_ & h & Hfloor & Hdep & Hspec & ->) | (Hr' & _) ]; [|congruence].
    exists h. rewrite (si_flv _ _ HS) in Hfloor. auto.
  Qed.

  Lemma rd_gt1 t ret :
    PUpdate (G t) (Build_ThreadEvent t (ResEv tgt ret))
      (I //\\ RPre t) (I //\\ (RPre t //\\ RG1 t ret)).
  Proof.
    intros σ0 ρ0 π0 [(r & Hρ & HS) Hlin] σ1 Hs.
    destruct (astep_res_cases TLCm t tgt ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold U in HS; simpl in HS.
    destruct (retro_post v r t tgt ret v' HS Hv eq_refl) as (h & _ & _ & Hspec & -> & HS').
    apply tlcm_spec_gt in Hspec.
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ r _ Hρ HS') | split; [exact Hlin|]].
      exists h. unfold U. simpl. split; [rewrite push_past_self; left; reflexivity | symmetry; exact Hspec].
    - exact (G_under t (Pending v t tgt) (Idle _) ρ0 π0 v _ tgt ret eq_refl eq_refl Hv).
  Qed.

  Lemma rd_dx t s1 ret :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (tdr dx) ret))
      (I //\\ (RPre t //\\ RG1 t s1)) (I //\\ (RPre t //\\ RG2 t s1 ret)).
  Proof.
    intros σ0 ρ0 π0 [(r & Hρ & HS) (Hlin & (h1 & Hin & Hv1))] σ1 Hs.
    destruct (astep_res_cases TLCm t (tdr dx) ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold U in *; simpl in *.
    destruct (retro_post v r t (tdr dx) ret v' HS Hv eq_refl) as (h & _ & Hdep & Hspec & -> & HS').
    apply tlcm_spec_dr in Hspec.
    pose proof (Hdep tgt h1 Hin eq_refl) as H12.
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ r _ Hρ HS') | split; [exact Hlin|]].
      exists h1, h. unfold U. simpl. split; [rewrite push_past_self; left; reflexivity|].
      split; [exact H12 | split; [exact Hv1 | symmetry; exact Hspec]].
    - exact (G_under t (Pending v t (tdr dx)) (Idle _) ρ0 π0 v _ (tdr dx) ret eq_refl eq_refl Hv).
  Qed.

  Lemma rd_dy t s1 a ret :
    PUpdate (G t) (Build_ThreadEvent t (ResEv (tdr dy) ret))
      (I //\\ (RPre t //\\ RG2 t s1 a)) (I //\\ (RPre t //\\ RG3 t s1 a ret)).
  Proof.
    intros σ0 ρ0 π0 [(r & Hρ & HS) (Hlin & (h1 & h2 & Hin & H12 & Hv1 & Ha))] σ1 Hs.
    destruct (astep_res_cases TLCm t (tdr dy) ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold U in *; simpl in *.
    destruct (retro_post v r t (tdr dy) ret v' HS Hv eq_refl) as (h & _ & Hdep & Hspec & -> & HS').
    apply tlcm_spec_dr in Hspec.
    pose proof (Hdep (tdr dx) h2 Hin eq_refl) as H23.
    exists ρ0, π0. split; [apply rt_refl|]. split.
    - split; [exact (I_step _ _ r _ Hρ HS') | split; [exact Hlin|]].
      exists h1, h2, h. unfold U. simpl. split; [rewrite push_past_self; left; reflexivity|].
      auto 6.
    - exact (G_under t (Pending v t (tdr dy)) (Idle _) ρ0 π0 v _ (tdr dy) ret eq_refl eq_refl Hv).
  Qed.

  (** The epoch argument. *)
  Lemma epoch v r s1 a b h1 h2 h3 h4 :
    SLInv v r -> Nat.even s1 = true ->
    Pos.lt h1 h2 -> Pos.lt h2 h3 -> Pos.lt h3 h4 ->
    tv (lk v h1) = s1 -> tx (lk v h2) = a -> ty (lk v h3) = b -> tv (lk v h4) = s1 ->
    (a, b) = gh v h4.
  Proof.
    intros HS Hev H12 H23 H34 Hv1 Ha Hb Hv4.
    assert (Hm12 := si_mono _ _ HS h1 h2 (Pos.lt_le_incl _ _ H12)).
    assert (Hm24 := si_mono _ _ HS h2 h4 (Pos.lt_le_incl _ _ (Pos.lt_trans _ _ _ H23 H34))).
    assert (Hm13 := si_mono _ _ HS h1 h3 (Pos.lt_le_incl _ _ (Pos.lt_trans _ _ _ H12 H23))).
    assert (Hm34 := si_mono _ _ HS h3 h4 (Pos.lt_le_incl _ _ H34)).
    assert (Hv2 : tv (lk v h2) = s1) by lia.
    assert (Hv3 : tv (lk v h3) = s1) by lia.
    pose proof (si_free _ _ HS h2 ltac:(rewrite Hv2; exact Hev)) as Hf2.
    pose proof (si_free _ _ HS h3 ltac:(rewrite Hv3; exact Hev)) as Hf3.
    pose proof (si_epoch _ _ HS h2 h4 (Pos.lt_le_incl _ _ (Pos.lt_trans _ _ _ H23 H34)) ltac:(lia)) as He2.
    pose proof (si_epoch _ _ HS h3 h4 (Pos.lt_le_incl _ _ H34) ltac:(lia)) as He3.
    rewrite He2 in Hf2. rewrite He3 in Hf3.
    destruct (gh v h4) as [g1 g2]. injection Hf2 as Hf2 _. injection Hf3 as _ Hf3. congruence.
  Qed.

  Definition RPost (t : tid) (s1 a b s2 : nat) : assertion :=
    if Nat.eqb s1 s2 then ALin t (Semantics.ls_linr rread (a, b)) else RPre t.

  Lemma rd_gt2 t s1 a b ret :
    Nat.even s1 = true ->
    PUpdate (G t) (Build_ThreadEvent t (ResEv tgt ret))
      (I //\\ (RPre t //\\ RG3 t s1 a b)) (I //\\ RPost t s1 a b ret).
  Proof.
    intros Hev σ0 ρ0 π0 [(r & Hρ & HS) (Hlin & (h1 & h2 & h3 & Hin & H12 & H23 & Hv1 & Ha & Hb))] σ1 Hs.
    destruct (astep_res_cases TLCm t tgt ret σ0 σ1 Hs) as (v & v' & -> & -> & Hv).
    unfold U in *. cbn [σ ρ state] in *.
    destruct (retro_post v r t tgt ret v' HS Hv eq_refl) as (h & Hfl & Hdep & Hspec & -> & HS').
    pose proof (tlcm_spec_gt _ _ _ _ Hspec) as Hv4.
    pose proof (Hdep (tdr dy) h3 Hin eq_refl) as H34.
    unfold RPost. destruct (Nat.eqb s1 ret) eqn:Heq.
    - apply Nat.eqb_eq in Heq. rewrite <- Heq in Hv4.
      assert (Hab : (a, b) = vs_tl RecP r h).
      { rewrite (si_rec _ _ HS). apply (epoch v r s1 a b h1 h2 h3 h HS Hev H12 H23 H34 Hv1 Ha Hb).
        unfold lk. symmetry. exact Hv4. }
      assert (Hvr : VStep RecP (Build_ThreadEvent t (ResEv rread (a, b))) r (upd_retro RecP r t rread h)).
      { refine (vstep_retro RecP t rread (a, b) h r _ _ eq_refl eq_refl _ (read_dep r v t h HS Hdep) _ eq_refl).
        - rewrite (si_flr _ _ HS). exact Hfl.
        - simpl. split; [exact Hab | reflexivity]. }
      exists (Idle (upd_retro RecP r t rread h)),
        (TMap.add t (Semantics.ls_linr rread (a, b)) (TMap.add t (Semantics.ls_lini rread) π0)).
      split; [rewrite Hρ; exact (vl_lp RecP r _ t rread (a, b) π0 Hlin Hvr)|]. split.
      + split; [|apply vl_lp_find].
        exists (upd_retro RecP r t rread h). split; [reflexivity|]. unfold U. simpl.
        apply SLInv_read; [exact HS | exact (VStep_Inv TLCm _ _ _ Hv (si_invv _ _ HS))
                          | exact (VStep_Inv RecP _ _ _ Hvr (si_invr _ _ HS))].
      + split; [intros t' Hne; apply vl_lp_find_other; exact Hne|]. simpl.
        split; [exact (vlmove_step TLCm t tgt ret v _ Hv) | rewrite Hρ; exact (vlmove_step RecP t rread (a, b) r _ Hvr)].
    - exists ρ0, π0. split; [apply rt_refl|]. split.
      + split; [exact (I_step _ _ r _ Hρ HS') | exact Hlin].
      + exact (G_under t (Pending v t tgt) (Idle _) ρ0 π0 v _ tgt ret eq_refl eq_refl Hv).
  Qed.

  (** ** The methods *)

  Lemma Pinv_gen t f : ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
  Proof.
    intros s (s0 & HI0 & (Hσ & Hρ & _ & Hπ)). split.
    - destruct HI0 as (r & Hr & HS). exists r. unfold U in *. rewrite <- Hσ, <- Hρ. auto.
    - unfold ALin. rewrite Hπ. apply TMap.gss.
  Qed.

  Lemma Qret_gen t f ret (X : assertion) : ⊨ Gret t f ret ⊚ (I //\\ X) ==>> I.
  Proof.
    intros s (s0 & (HI0 & _) & (Hσ & Hρ & _)).
    destruct HI0 as (r & Hr & HS). exists r. unfold U in *. rewrite <- Hσ, <- Hρ. auto.
  Qed.

  Lemma vis_step {A} t (m : TOp) (k : TAr m -> Prog ETL A) (X : assertion) (Y : TAr m -> assertion) Q :
    (forall s, X s -> ~ vl_err TLCm t m (cur TLCm (U s))) ->
    SOnly X -> SI t X -> (forall ret, SI t (Y ret)) ->
    (forall ret, PUpdate (G t) (Build_ThreadEvent t (ResEv m ret)) (I //\\ X) (I //\\ Y ret)) ->
    (forall ret, [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ Y ret }} k ret {{ Q }}) ->
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ X }} Vis m k {{ Q }}.
  Proof.
    intros Herr Hso HsX HsY Hres Hk.
    apply provable_vis_safe with (P' := I //\\ X) (Q' := fun ret => I //\\ Y ret).
    - intros s [_ Hx]. apply noerror. exact (Herr s Hx).
    - intros s [HI _]. exact HI.
    - intros ret s [HI _]. exact HI.
    - apply stable_I. exact HsX.
    - intros ret. apply stable_I. exact (HsY ret).
    - apply pupdate_inv. exact Hso.
    - exact Hres.
    - exact Hk.
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

  Definition WPost (t : tid) (a b : nat) (ret : unit) : assertion :=
    I //\\ ALin t (Semantics.ls_linr (rwrite a b) ret).

  Lemma write_triple t a b :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ WPre t a b }} write_impl a b {{ WPost t a b }}.
  Proof.
    unfold write_impl.
    apply vis_step with (Y := fun _ => WPre t a b //\\ Hold t).
    { intros s _ H. exact H. }
    { sonly. }
    { apply SI_ALin. }
    { intros _. apply SI_conj; [apply SI_ALin | apply SI_Hold]. }
    { apply wr_acq. }
    intros _. apply vis_step with (Y := fun _ => WPre t a b //\\ (Hold t //\\ WX a)).
    { intros s (_ & Hh) H. exact (H Hh). }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_Hold]. }
    { intros _. apply SI_conj; [apply SI_ALin | apply SI_HoldX]. }
    { apply wr_dwx. }
    intros _. apply vis_step with (Y := fun _ => WPre t a b //\\ (Hold t //\\ WX a //\\ WY b)).
    { intros s (_ & Hh & _) H. exact (H Hh). }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_HoldX]. }
    { intros _. apply SI_conj; [apply SI_ALin | apply SI_HoldXY]. }
    { apply wr_dwy. }
    intros _. apply vis_step with (Y := fun _ => ALin t (Semantics.ls_linr (rwrite a b) tt)).
    { intros s (_ & Hh & _) H. exact (H Hh). }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_HoldXY]. }
    { intros _. apply SI_ALin. }
    { apply wr_rel. }
    intros _. apply ret_step with (Y := ALin t (Semantics.ls_linr (rwrite a b) tt)).
    - intros s H. exact H.
    - reflexivity.
    - apply SI_ALin.
  Qed.

  Definition RLoop (t : tid) (x : unit + (nat * nat)) : assertion :=
    match x with
    | inl _ => I //\\ RPre t
    | inr v => I //\\ ALin t (Semantics.ls_linr rread v)
    end.

  Lemma read_tail_triple t s1 :
    Nat.even s1 = true ->
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ (RPre t //\\ RG1 t s1) }} read_tail s1 {{ RLoop t }}.
  Proof.
    intros Hev. unfold read_tail.
    apply vis_step with (Y := fun a => RPre t //\\ RG2 t s1 a).
    { intros s _ H. exact H. }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_RG1]. }
    { intros a. apply SI_conj; [apply SI_ALin | apply SI_RG2]. }
    { apply rd_dx. }
    intros a. apply vis_step with (Y := fun b => RPre t //\\ RG3 t s1 a b).
    { intros s _ H. exact H. }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_RG2]. }
    { intros b. apply SI_conj; [apply SI_ALin | apply SI_RG3]. }
    { apply rd_dy. }
    intros b. apply vis_step with (Y := fun s2 => RPost t s1 a b s2).
    { intros s _ H. exact H. }
    { sonly. }
    { apply SI_conj; [apply SI_ALin | apply SI_RG3]. }
    { intros s2. unfold RPost. destruct (Nat.eqb s1 s2); apply SI_ALin. }
    { intros ret. apply rd_gt2. exact Hev. }
    intros s2. unfold RPost. destruct (Nat.eqb s1 s2).
    - apply ret_step with (Y := ALin t (Semantics.ls_linr rread (a, b))).
      + intros s H. exact H.
      + reflexivity.
      + apply SI_ALin.
    - apply ret_step with (Y := RPre t).
      + intros s H. exact H.
      + reflexivity.
      + apply SI_ALin.
  Qed.

  Lemma read_body_triple t :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ RPre t }} read_body {{ RLoop t }}.
  Proof.
    unfold read_body.
    apply vis_step with (Y := fun s1 => RPre t //\\ RG1 t s1).
    { intros s _ H. exact H. }
    { sonly. }
    { apply SI_ALin. }
    { intros s1. apply SI_conj; [apply SI_ALin | apply SI_RG1]. }
    { apply rd_gt1. }
    intros s1. destruct (Nat.even s1) eqn:Hev.
    - apply read_tail_triple. exact Hev.
    - apply ret_step with (Y := RPre t).
      + intros s (H & _). exact H.
      + reflexivity.
      + apply SI_ALin.
  Qed.

  Definition RPostM (t : tid) (v : nat * nat) : assertion :=
    I //\\ ALin t (Semantics.ls_linr rread v).

  Lemma read_triple t :
    [VE, VF, R t, G t, I, t] ⊢ {{ I //\\ RPre t }} read_impl {{ RPostM t }}.
  Proof.
    unfold read_impl.
    apply provable_doloop with (Iloop := I //\\ RPre t) (Q := RPostM t) (p := read_body).
    - intros v s [HI _]. exact HI.
    - intros v. apply stable_I, SI_ALin.
    - eapply provable_conseq_weak_post; [| | | exact (read_body_triple t)].
      + intros [x | v] s [HI _]; exact HI.
      + intros [x | v]; apply stable_I, SI_ALin.
      + intros [x | v] s H; exact H.
  Qed.

  (** ** Correctness over the presentation with releases *)

  Lemma ValidRGI_SL t : RGISimulation.ValidRGI (R t) (G t) I t.
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

  Lemma SLInv_init : SLInv (vinit TLCm (tl_init, rel_init)) (vinit RecP rec_init).
  Proof.
    constructor; simpl.
    - apply Inv_init.
    - apply Inv_init.
    - reflexivity.
    - reflexivity.
    - apply Pos.le_refl.
    - intros h. reflexivity.
    - intros h _. reflexivity.
    - intros h h' _. apply le_n.
    - intros h h' _ _. reflexivity.
    - split; reflexivity.
    - intros t o h [].
  Qed.

  Theorem M_SL_ghost :
    TPSimulation.cal (VE := VL TLCm) (VF := VL RecP) M_SL
      (Idle (vinit TLCm (tl_init, rel_init))) (Idle (vinit RecP rec_init)).
  Proof.
    eapply RGILogic.soundness with (R := R) (G := G) (I := I).
    - exact ValidRGI_SL.
    - exact RG_compat.
    - intros t [a b | ].
      + exists (I //\\ WPre t a b), (WPost t a b). constructor.
        * apply Pinv_gen.
        * intros s [HI _]. exact HI.
        * apply stable_I, SI_ALin.
        * intros ret. apply Qret_gen.
        * intros ret σ0 ρ0 π0 [_ H]. exact H.
        * exact (write_triple t a b).
      + exists (I //\\ RPre t), (RPostM t). constructor.
        * apply Pinv_gen.
        * intros s [HI _]. exact HI.
        * apply stable_I, SI_ALin.
        * intros ret. apply Qret_gen.
        * intros ret σ0 ρ0 π0 [_ H]. exact H.
        * exact (read_triple t).
    - exists (vinit RecP rec_init). split; [reflexivity | exact SLInv_init].
  Qed.

  (** ** The same proof over the plain presentation of the lock *)

  Theorem M_SL_plain :
    TPSimulation.cal (VE := VL TLC) (VF := VL RecP) M_SL
      (Idle (vinit TLC tl_init)) (Idle (vinit RecP rec_init)).
  Proof.
    exact (ViewLiftGhost.cal_ghost_to_plain TLC rel_up (VL RecP) M_SL tl_init rel_init
             (Idle (vinit RecP rec_init)) M_SL_ghost).
  Qed.
End TicketTowerSeqLock.
