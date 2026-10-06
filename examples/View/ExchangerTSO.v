(** Ported from CSL-Lin [examples/Exchanger.v] (hyleIndex/CSL-Lin, master 3f7baaa).
    View-based (timestamped) specification / proof, kept as close to the
    original as possible; changes are limited to the Rocq 9.2 / rbgs
    adaptation listed in [examples/View/README.md]. *)

Require Import Stdlib.FSets.FMapPositive.
Require Import Stdlib.Relations.Relation_Operators Stdlib.Relations.Operators_Properties.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Arith.PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import Logics.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGILogic.
Require Import examples.Common.AtomicLTS.
Require Import examples.View.ViewSpecs.
Require Import examples.Exchanger.ExchangerSpec.

Module Type TypeParam.
  Parameter A : Type.
End TypeParam.

Module ExchangerImplF (P : TypeParam).
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS ExchSpec CASRegTSOSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.

  Open Scope prog_scope.

  Definition A : Type := P.A.

  Variant Offer : Type :=
  | Offered (t1 : tid) (v1 : A)
  | Accepted (t1 t2 : tid) (v1 v2 : A)
  | Empty.

  Definition Tail (mem : Time -> Offer) (view : tid -> Time) (o : Offer) : Prop :=
    exists h,
      (forall t, Pos.le h (view t)) /\
      (forall h', Pos.le h h' -> mem h' = o).

  Definition initE : SCASRegTSO Offer :=
    mkCASRegTSO (fun _ => Empty) (fun _ => xH).

  Definition E : layer_interface :=
  {|
    li_sig := ECASReg Offer;
    li_lts := VCASRegTSO;
    li_init := Idle initE;
  |}.

  Definition F : layer_interface :=
  {|
    li_sig := EExch A;
    li_lts := VExch;
    li_init := ExSIdle;
  |}.

  Definition cas_empty_offer (t : tid) (v : A) : ECASReg_op Offer :=
    cas Empty (Offered t v).

  Definition cas_offer_empty (t : tid) (v : A) : ECASReg_op Offer :=
    cas (Offered t v) Empty.

  Definition cas_accept (t : tid) (w : Offer) (v : A) : ECASReg_op Offer :=
    cas w
        (match w with
         | Offered t' v' => Accepted t' t v' v
         | _ => w
         end).

  Definition cas_cleanup (w : Offer) : ECASReg_op Offer :=
    cas w Empty.

  Definition exch_impl (v : A) (t : tid) : Prog (li_sig E) (option A) :=
    cas_empty_offer t v >= offered =>
    if offered then
      cas_offer_empty t v >= revoked =>
      if revoked then
        Ret None
      else
        get >= w =>
        match w with
        | Accepted _ _ _ v' =>
            cas_cleanup w >= _ =>
            Ret (Some v')
        | _ => Ret None
        end
    else
      get >= w =>
      match w with
      | Offered _ v' =>
          cas_accept t w v >= accepted =>
          Ret (if accepted then Some v' else None)
      | _ => Ret None
      end.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition TSOState (o : Offer) (s : SCASRegTSO Offer) : Prop :=
    Tail (cas_mem s) (cas_view s) o.

  Definition ExchRel (s : SCASRegTSO Offer) (es : @EExchState A)
      (π : tmap Semantics.LinState) : Prop :=
    (TSOState Empty s /\ es = ExSIdle) \/
    (exists t v, TSOState (Offered t v) s /\
      es = ExSIdle /\
      TMap.find t π = Some (Semantics.ls_inv (exch v))) \/
    (exists t1 t2 v1 v2, TSOState (Accepted t1 t2 v1 v2) s /\
      es = ExSIdle).

  Definition I : assertion :=
    fun s => ExchRel (state (σ s)) (ρ s) (π s).

  Lemma Tail_fresh_value mem view o h :
    Tail mem view o ->
    (forall t, Pos.lt (view t) h) ->
    mem h = o.
  Proof.
    intros [hc [Hview Htail]] Hfresh.
    apply Htail.
    specialize (Hfresh xH).
    specialize (Hview xH).
    lia.
  Qed.

  Lemma Tail_get_pres mem view o tid0 h :
    Tail mem view o ->
    Pos.lt (view tid0) h ->
    Tail mem (upd_tid_time view tid0 h) o.
  Proof.
    intros [hc [Hview Htail]] Hlt.
    exists hc; split; auto.
    intro t'. unfold upd_tid_time.
    destruct (Pos.eqb_spec tid0 t'); subst.
    - specialize (Hview t'). lia.
    - specialize (Hview t'). lia.
  Qed.

  Lemma Tail_advance_all_pres mem view o h :
    Tail mem view o ->
    (forall t, Pos.lt (view t) h) ->
    Tail mem (view_advance_all h) o.
  Proof.
    intros HT Hfresh.
    exists h; split.
    - intro t. unfold view_advance_all. lia.
    - intros h' Hle.
      eapply Tail_fresh_value; eauto.
      intro t. specialize (Hfresh t). lia.
  Qed.

  Lemma Tail_write_new mem o h :
    Tail (mem_write mem h o) (view_advance_all h) o.
  Proof.
    exists h; split.
    - intro t. unfold view_advance_all. lia.
    - intros h' Hle. unfold mem_write.
      destruct (Pos.leb_spec h h'); [reflexivity|lia].
  Qed.

  Lemma Tail_unique mem view o1 o2 :
    Tail mem view o1 ->
    Tail mem view o2 ->
    o1 = o2.
  Proof.
    intros [h1 [Hview1 Htail1]] [h2 [Hview2 Htail2]].
    pose proof (Htail1 (Pos.max h1 h2) (Pos.le_max_l h1 h2)) as H1.
    pose proof (Htail2 (Pos.max h1 h2) (Pos.le_max_r h1 h2)) as H2.
    exact (eq_trans (eq_sym H1) H2).
  Qed.

  Definition OfferedBy (t : tid) (v : A) : assertion :=
    fun s => TSOState (Offered t v) (state (σ s)) /\
      ρ s = ExSIdle /\
      ALin t (Semantics.ls_inv (exch v)) s.

  Definition AcceptedByFirst (t : tid) (v : A) (other : A) : assertion :=
    fun s => exists t2, TSOState (Accepted t t2 v other) (state (σ s)) /\
      ρ s = ExSIdle /\
      ALin t (Semantics.ls_linr (exch v) (Some other)) s.

  Definition NoOfferBy (t : tid) : assertion :=
    fun s => forall v, ~ TSOState (Offered t v) (state (σ s)).

  Definition FirstLive (t : tid) (v : A) : assertion :=
    (OfferedBy t v //\\ ALin t (Semantics.ls_inv (exch v))) \\//
    (fun s => exists other,
      (AcceptedByFirst t v other //\\
       ALin t (Semantics.ls_linr (exch v) (Some other))) s).

  Definition R_pres (t : tid) : rg_relation :=
    fun s1 s2 =>
      (TMap.find t (π s1) = None <-> TMap.find t (π s2) = None) /\
      (forall v, (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t) s1 ->
        (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t) s2) /\
      (forall v ret, ALin t (Semantics.ls_linr (exch v) ret) s1 ->
        ALin t (Semantics.ls_linr (exch v) ret) s2) /\
      (NoOfferBy t s1 -> NoOfferBy t s2) /\
      (forall v other, AcceptedByFirst t v other s1 ->
        AcceptedByFirst t v other s2) /\
      (forall v, FirstLive t v s1 -> FirstLive t v s2).

  Definition G t : rg_relation :=
    fun s1 s2 => forall t', t <> t' -> R_pres t' s1 s2.

  Definition R t : rg_relation :=
    R_pres t.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma ActiveInvstable {t v}: Stable (R t) I
    (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Halin [_ [Hinv _]]]] HI].
    eauto.
  Qed.

  Lemma ALinRetstable {t v ret}: Stable (R t) I (ALin t (Semantics.ls_linr (exch v) ret)).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Halin [_ [_ [Hret _]]]]] HI].
    eauto.
  Qed.

  Lemma AcceptedByFirststable {t v other}: Stable (R t) I (AcceptedByFirst t v other).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hacc [_ [_ [_ [_ [Hpres _]]]]]]] HI].
    eauto.
  Qed.

  Lemma FirstLivestable {t v}: Stable (R t) I (FirstLive t v).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hfl [_ [_ [_ [_ [_ Hlive]]]]]]] HI].
    eauto.
  Qed.

  Lemma NoOfferBystable {t}: Stable (R t) I (NoOfferBy t).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hno [_ [_ [_ [Hpres _]]]]]] HI].
    eauto.
  Qed.

  Lemma IAcceptedByFirstStable {t v}: Stable (R t) I
    (I //\\ (fun s => exists other, AcceptedByFirst t v other s)).
  Proof.
    unfold Stable.
    intros s [[s' [[HI [other Hacc]] HR]] HI2].
    split.
    - apply (Istable (t:=t)); split; [exists s'; split; [exact HI|exact HR]|exact HI2].
    - exists other.
      apply (AcceptedByFirststable (t:=t) (v:=v) (other:=other)); split;
        [exists s'; split; [exact Hacc|exact HR]|exact HI2].
  Qed.

  Lemma IAcceptedByFirstPureStable {t v} (P : A -> Prop):
    Stable (R t) I
      (I //\\ (fun s => exists other,
        (AcceptedByFirst t v other //\\ (fun _ => P other)) s)).
  Proof.
    unfold Stable.
    intros s [[s' [[HI [other [Hacc Hpure]]] HR]] HI2].
    split.
    - apply (Istable (t:=t)); split; [exists s'; split; [exact HI|exact HR]|exact HI2].
    - exists other; split.
      + apply (AcceptedByFirststable (t:=t) (v:=v) (other:=other)); split;
        [exists s'; split; [exact Hacc|exact HR]|exact HI2].
      + exact Hpure.
  Qed.

  Lemma R_pres_unchanged t (s1 s2 : @ProofState _ _ (li_lts E) (li_lts F)) :
    σ s1 = σ s2 ->
    ρ s1 = ρ s2 ->
    TMap.find t (π s1) = TMap.find t (π s2) ->
    R_pres t s1 s2.
  Proof.
    intros Hσ Hρ Hπ.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *; subst.
    unfold R_pres, ALin; simpl.
    repeat split; intros; simpl in *.
    - rewrite <- Hπ. auto.
    - rewrite Hπ. auto.
    - destruct H as [Hlin Hno].
      unfold ALin in *; simpl in *.
      change (TMap.find t π2 = Some (Semantics.ls_inv (exch v))).
      rewrite <- Hπ.
      exact Hlin.
    - destruct H as [_ Hno]. exact Hno.
    - rewrite <- Hπ. auto.
    - unfold NoOfferBy in *; auto.
    - unfold AcceptedByFirst in *.
      destruct H as [t2 [? [? ?]]].
      exists t2. repeat split; auto.
      unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    - unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj in *.
      destruct H as [[Hoff Hlin] | [other [Hacc Hlin]]].
      + left. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hoff as [? [? ?]]. repeat split; auto.
        unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
      + right. exists other. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hacc as [t2 [? [? ?]]].
        exists t2. repeat split; auto.
        unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    all: unfold ALin in *; simpl in *; try congruence; eauto.
  Qed.

  Lemma R_pres_same_obs t (s1 s2 : @ProofState _ _ (li_lts E) (li_lts F)) :
    state (σ s1) = state (σ s2) ->
    ρ s1 = ρ s2 ->
    TMap.find t (π s1) = TMap.find t (π s2) ->
    R_pres t s1 s2.
  Proof.
    intros Hσ Hρ Hπ.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *; subst.
    unfold R_pres, ALin; simpl.
    repeat split; intros; simpl in *.
    - rewrite <- Hπ. auto.
    - rewrite Hπ. auto.
    - destruct H as [Hlin Hno].
      unfold ALin in *; simpl in *.
      change (TMap.find t π2 = Some (Semantics.ls_inv (exch v))).
      rewrite <- Hπ.
      exact Hlin.
    - destruct H as [_ Hno].
      unfold NoOfferBy in *. intros vx Hbad. apply (Hno vx). simpl in *. rewrite Hσ. auto.
    - rewrite <- Hπ. auto.
    - unfold NoOfferBy in *. intros vx Hbad. apply (H vx). simpl in *. rewrite Hσ. auto.
    - unfold AcceptedByFirst in *.
      destruct H as [t2 [? [? ?]]].
      exists t2. repeat split; auto.
      * simpl in *. rewrite <- Hσ. auto.
      * unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    - unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj in *.
      destruct H as [[Hoff Hlin] | [other [Hacc Hlin]]].
      + left. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hoff as [? [? ?]]. repeat split; auto.
        * simpl in *. rewrite <- Hσ. auto.
        * unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
      + right. exists other. split; [|unfold ALin in *; simpl in *; rewrite <- Hπ; auto].
        destruct Hacc as [t2 [? [? ?]]].
        exists t2. repeat split; auto.
        * simpl in *. rewrite <- Hσ. auto.
        * unfold ALin in *; simpl in *; rewrite <- Hπ; auto.
    all: unfold ALin in *; simpl in *; try congruence; eauto.
  Qed.

  Create HintDb stableDB.
  #[local] Hint Resolve
    Istable
    ActiveInvstable
    ALinRetstable
    AcceptedByFirststable
    FirstLivestable
    NoOfferBystable
  : stableDB.

  Lemma IGinvActive : forall t v,
    ⊨ Ginv t (exch v) ⊚ I ==>>
      I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t).
  Proof.
    unfold I, ALin, NoOfferBy, Ginv, LiftRelation_π.
    intros t v s [s' [HI [? [? [Hnone ?]]]]].
    destruct s as [σ ρ π], s' as [σ' ρ' π']; simpl in *; subst.
    split.
    - unfold ExchRel in *; simpl in *.
      destruct HI as [[HT Hidle] | [[to [vo [HT [Hidle Hπ]]]] |
        [t1 [t2 [v1 [v2 [HT Hidle]]]]]]].
      + left; split; auto.
      + right; left. exists to, vo. repeat split; auto.
        destruct (PositiveMap.E.eq_dec t to); subst.
        * rewrite Hnone in Hπ. discriminate.
        * rewrite PositiveMap.gso; auto.
      + right; right. exists t1, t2, v1, v2. split; auto.
    - split.
      + change (TMap.find t (TMap.add t (Semantics.ls_inv (exch v)) π') =
          Some (Semantics.ls_inv (exch v))).
        rewrite PositiveMap.gss; auto.
      + intros v0 HTbad.
        unfold ExchRel in HI.
        destruct HI as [[HT Hidle] | [[to [vo [HT [Hidle Hπ]]]] |
          [t1 [t2 [v1 [v2 [HT Hidle]]]]]]].
        * pose proof (Tail_unique _ _ _ _ HT HTbad) as Heq.
          discriminate Heq.
        * pose proof (Tail_unique _ _ _ _ HT HTbad) as Heq.
          inversion Heq; subst.
          rewrite Hnone in Hπ. discriminate.
        * pose proof (Tail_unique _ _ _ _ HT HTbad) as Heq.
          discriminate Heq.
  Qed.

  Lemma IGret : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ ALin t (Semantics.ls_linr f ret)) ==>> I.
  Proof.
    unfold I, ALin, Gret, LiftRelation_π.
    intros t f ret s [s' [[HI Hlin] [? [? [? ?]]]]].
    destruct s as [σ ρ π], s' as [σ' ρ' π']; simpl in *; subst.
    unfold ExchRel in *; simpl in *.
    destruct HI as [[HT Hidle] | [[to [vo [HT [Hidle Hπ]]]] |
      [t1 [t2 [v1 [v2 [HT Hidle]]]]]]].
    - left; split; auto.
    - right; left. exists to, vo. repeat split; auto.
      destruct (PositiveMap.E.eq_dec t to); subst.
      + simpl in Hlin. rewrite Hπ in Hlin. discriminate.
      + rewrite PositiveMap.gro; auto.
    - right; right. exists t1, t2, v1, v2. split; auto.
  Qed.

  Lemma step_cas_empty_offer_success_inv tid0 v h s1 s2 :
    StepCASRegTSO
      {| te_tid := tid0; te_ev := ResEv (cas_empty_offer tid0 v) true |} s1 s2 ->
    (forall t0, Pos.lt (cas_view s1 t0) h) ->
    cas_mem s1 h = Empty ->
    s2 = mkCASRegTSO (mem_write (cas_mem s1) h (Offered tid0 v)) (view_advance_all h) ->
    TSOState (Offered tid0 v) s2.
  Proof.
    intros _ _ _ ->. apply Tail_write_new.
  Qed.

  Lemma step_cas_offer_empty_success_inv tid0 v h s1 s2 :
    StepCASRegTSO
      {| te_tid := tid0; te_ev := ResEv (cas_offer_empty tid0 v) true |} s1 s2 ->
    (forall t0, Pos.lt (cas_view s1 t0) h) ->
    cas_mem s1 h = Offered tid0 v ->
    s2 = mkCASRegTSO (mem_write (cas_mem s1) h Empty) (view_advance_all h) ->
    TSOState Empty s2.
  Proof.
    intros _ _ _ ->. apply Tail_write_new.
  Qed.

  Lemma step_cas_fail_tail_pres tid0 expected desired h s1 s2 o :
    StepCASRegTSO
      {| te_tid := tid0; te_ev := ResEv (cas expected desired) false |} s1 s2 ->
    TSOState o s1 ->
    (forall t0, Pos.lt (cas_view s1 t0) h) ->
    s2 = mkCASRegTSO (cas_mem s1) (view_advance_all h) ->
    TSOState o s2.
  Proof.
    intros _ HT Hfresh ->.
    eapply Tail_advance_all_pres; eauto.
  Qed.

  Lemma step_get_tail_pres tid0 oret h s1 s2 o :
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv get oret |} s1 s2 ->
    TSOState o s1 ->
    Pos.lt (cas_view s1 tid0) h ->
    s2 = mkCASRegTSO (cas_mem s1) (upd_tid_time (cas_view s1) tid0 h) ->
    TSOState o s2.
  Proof.
    intros _ HT Hlt ->.
    eapply Tail_get_pres; eauto.
  Qed.

  Definition cas_response (ev : @ThreadEvent (ECASReg Offer)) : bool :=
    match te_ev ev with
    | ResEv (cas _ _) ret => ret
    | _ => false
    end.

  Definition get_response (ev : @ThreadEvent (ECASReg Offer)) : option Offer :=
    match te_ev ev with
    | ResEv get ret => Some ret
    | _ => None
    end.

  Lemma step_cas_res_inv tid0 (expected desired : Offer) ret s1 s2 :
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv (cas expected desired) ret |} s1 s2 ->
    (ret = true /\
      exists h,
        (forall t0, Pos.lt (cas_view s1 t0) h) /\
        cas_mem s1 h = expected /\
        s2 = mkCASRegTSO (mem_write (cas_mem s1) h desired) (view_advance_all h)) \/
    (ret = false /\
      exists h,
        (forall t0, Pos.lt (cas_view s1 t0) h) /\
        cas_mem s1 h <> expected /\
        s2 = mkCASRegTSO (cas_mem s1) (view_advance_all h)).
  Proof.
    intros Hstep.
    remember {| te_tid := tid0; te_ev := ResEv (cas expected desired) ret |} as ev eqn:Hev.
    revert tid0 expected desired ret Hev.
    induction Hstep; intros tidx expected0 desired0 ret Hev; inversion Hev; subst; try discriminate.
    - pose proof (f_equal cas_response Hev) as Hret.
      unfold cas_response in Hret; simpl in Hret; subst ret.
      left. split; [reflexivity|].
      exists h. repeat split; eauto.
    - pose proof (f_equal cas_response Hev) as Hret.
      unfold cas_response in Hret; simpl in Hret; subst ret.
      right. split; [reflexivity|].
      exists h. repeat split; eauto.
  Qed.

  Lemma step_cas_empty_offer_res_inv tid0 v ret s1 s2 :
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv (cas_empty_offer tid0 v) ret |} s1 s2 ->
    (ret = true /\
      exists h,
        (forall t0, Pos.lt (cas_view s1 t0) h) /\
        cas_mem s1 h = Empty /\
        s2 = mkCASRegTSO (mem_write (cas_mem s1) h (Offered tid0 v)) (view_advance_all h)) \/
    (ret = false /\
      exists h,
        (forall t0, Pos.lt (cas_view s1 t0) h) /\
        cas_mem s1 h <> Empty /\
        s2 = mkCASRegTSO (cas_mem s1) (view_advance_all h)).
  Proof.
    apply step_cas_res_inv.
  Qed.

  Lemma step_get_res_inv tid0 (ret : Offer) (s1 s2 : SCASRegTSO Offer) :
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv get ret |} s1 s2 ->
    exists h,
      Pos.lt (cas_view s1 tid0) h /\
      ret = cas_mem s1 h /\
      s2 = mkCASRegTSO (cas_mem s1) (upd_tid_time (cas_view s1) tid0 h).
  Proof.
    intros Hstep.
    remember {| te_tid := tid0; te_ev := ResEv get ret |} as ev eqn:Hev.
    revert tid0 ret Hev.
    induction Hstep; intros tidx ret0 Hev; inversion Hev; subst; try discriminate.
    pose proof (f_equal get_response Hev) as Hret.
    unfold get_response in Hret; simpl in Hret.
    inversion Hret; subst.
    exists h. repeat split; eauto.
  Qed.

  Lemma step_get_tail_inv tid0 ret s1 s2 o :
    TSOState o s1 ->
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv get ret |} s1 s2 ->
    ret = o /\ TSOState o s2.
  Proof.
    intros HT Hstep.
    destruct (step_get_res_inv _ _ _ _ Hstep) as [h [Hlt [Hret Hs2]]].
    split.
    - subst ret.
      destruct HT as [hc [Hview Htail]].
      apply Htail.
      specialize (Hview tid0). lia.
    - eapply step_get_tail_pres; eauto.
  Qed.

  Lemma step_cas_tail_success_inv tid0 expected desired ret s1 s2 :
    TSOState expected s1 ->
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv (cas expected desired) ret |} s1 s2 ->
    ret = true /\ TSOState desired s2.
  Proof.
    intros HT Hstep.
    destruct (step_cas_res_inv _ _ _ _ _ _ Hstep)
      as [[Hret [h [Hfresh [Hmem Hs2]]]] | [Hret [h [Hfresh [Hneq Hs2]]]]].
    - subst ret. split; [reflexivity|].
      subst s2. apply Tail_write_new.
    - exfalso. subst ret.
      apply Hneq. eapply Tail_fresh_value; eauto.
  Qed.

  Lemma step_cas_tail_fail_inv tid0 expected desired ret s1 s2 o :
    TSOState o s1 ->
    o <> expected ->
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv (cas expected desired) ret |} s1 s2 ->
    ret = false /\ TSOState o s2.
  Proof.
    intros HT Hdiff Hstep.
    destruct (step_cas_res_inv _ _ _ _ _ _ Hstep)
      as [[Hret [h [Hfresh [Hmem Hs2]]]] | [Hret [h [Hfresh [Hneq Hs2]]]]].
    - exfalso. apply Hdiff.
      transitivity (cas_mem s1 h).
      + symmetry. eapply Tail_fresh_value; eauto.
      + exact Hmem.
    - subst ret. split; [reflexivity|].
      subst s2. eapply Tail_advance_all_pres; eauto.
  Qed.

  Lemma no_offer_after_unique t0 v0 t1 v1 s :
    TSOState (Offered t0 v0) s ->
    TSOState (Offered t1 v1) s ->
    t0 = t1.
  Proof.
    intros H0 H1.
    pose proof (Tail_unique _ _ _ _ H0 H1) as Heq.
    inversion Heq; auto.
  Qed.

  Lemma R_pres_empty_to_offer_other t t0 v
      (op : Sig.op (ECASReg Offer)) s1 s2
      (ρ0 : EExchState) (π0 : tmap Semantics.LinState) :
    t0 <> t ->
    TSOState Empty s1 ->
    TSOState (Offered t0 v) s2 ->
    R_pres t
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Pending (ECASReg Offer) (SCASRegTSO Offer) s1 t0 op) ρ0 π0)
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Idle (ECASReg Offer) (SCASRegTSO Offer) s2) ρ0 π0).
  Proof.
    intros Hneq HTempty HToffer.
    unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
    simpl.
    repeat split; intros; simpl in *; auto.
    - destruct H as [Hlin _].
      exact Hlin.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HToffer HTbad) as Heq.
      inversion Heq; subst. contradiction.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HToffer HTbad) as Heq.
      inversion Heq; subst. contradiction.
    - destruct H as [t2 [HTbad _]].
      pose proof (Tail_unique _ _ _ _ HTempty HTbad) as Heq.
      discriminate Heq.
    - destruct H as [[[HTbad _] _] | [other [[t2 [HTbad _]] _]]].
      + pose proof (Tail_unique _ _ _ _ HTempty HTbad) as Heq.
        discriminate Heq.
      + pose proof (Tail_unique _ _ _ _ HTempty HTbad) as Heq.
        discriminate Heq.
  Qed.

  Lemma R_pres_tail_preserved t
      (op : Sig.op (ECASReg Offer)) top s1 s2
      (ρ0 : EExchState) (π0 : tmap Semantics.LinState) :
    ExchRel s1 ρ0 π0 ->
    (forall o, TSOState o s1 -> TSOState o s2) ->
    R_pres t
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Pending (ECASReg Offer) (SCASRegTSO Offer) s1 top op) ρ0 π0)
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Idle (ECASReg Offer) (SCASRegTSO Offer) s2) ρ0 π0).
  Proof.
    intros HI Htail_pres.
    unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
    simpl.
    repeat split; intros; simpl in *; auto.
    - destruct H as [Hlin Hno]. exact Hlin.
    - destruct H as [Hlin Hno].
      intro HTbad.
      unfold ExchRel in HI.
      destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπ]]]] |
        [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        pose proof (Hno vo) as Hno_vo.
        inversion Heq; subst. apply Hno_vo. exact HT.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
    - intro HTbad.
      unfold ExchRel in HI.
      destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπ]]]] |
        [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        pose proof (H vo) as Hno_vo.
        inversion Heq; subst. apply Hno_vo. exact HT.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
    - destruct H as [t2 [HT [Hrho Hlin]]].
      exists t2. repeat split; auto.
    - destruct H as [[[HT [Hrho Hlin]] Hlin'] | [other [[t2 [HT [Hrho Hlin]]] Hlin']]].
      + left. repeat split; auto.
      + right. exists other. split; auto.
        exists t2. repeat split; auto.
  Qed.

  Lemma R_pres_tail_preserved_pi t
      (op : Sig.op (ECASReg Offer)) top s1 s2
      (ρ0 : EExchState) (π0 π1 : tmap Semantics.LinState) :
    ExchRel s1 ρ0 π0 ->
    (forall o, TSOState o s1 -> TSOState o s2) ->
    TMap.find t π0 = TMap.find t π1 ->
    R_pres t
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Pending (ECASReg Offer) (SCASRegTSO Offer) s1 top op) ρ0 π0)
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Idle (ECASReg Offer) (SCASRegTSO Offer) s2) ρ0 π1).
  Proof.
    intros HI Htail_pres Hπ.
    unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
    simpl.
    repeat split; intros; simpl in *; auto.
    - rewrite <- Hπ. auto.
    - rewrite Hπ. auto.
    - destruct H as [Hlin Hno]. rewrite <- Hπ. exact Hlin.
    - destruct H as [Hlin Hno].
      intro HTbad.
      unfold ExchRel in HI.
      destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπto]]]] |
        [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        pose proof (Hno vo) as Hno_vo.
        inversion Heq; subst. apply Hno_vo. exact HT.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
    - rewrite <- Hπ. auto.
    - intro HTbad.
      unfold ExchRel in HI.
      destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπto]]]] |
        [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        pose proof (H vo) as Hno_vo.
        inversion Heq; subst. apply Hno_vo. exact HT.
      + pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
        discriminate Heq.
    - destruct H as [t2 [HT [Hrho Hlin]]].
      exists t2. repeat split; auto.
      unfold ALin; simpl. rewrite <- Hπ. exact Hlin.
    - destruct H as [[[HT [Hrho Hlin]] Hlin'] | [other [[t2 [HT [Hrho Hlin]]] Hlin']]].
      + left. repeat split; auto; unfold ALin; simpl; rewrite <- Hπ; auto.
      + right. exists other. split.
        * exists t2. repeat split; auto. unfold ALin; simpl; rewrite <- Hπ; auto.
        * unfold ALin; simpl; rewrite <- Hπ; auto.
  Qed.

  Lemma R_pres_offer_to_empty_other t t0 v
      (op : Sig.op (ECASReg Offer)) s1 s2
      (ρ0 : EExchState) (π0 π1 : tmap Semantics.LinState) :
    t0 <> t ->
    TSOState (Offered t0 v) s1 ->
    TSOState Empty s2 ->
    TMap.find t π0 = TMap.find t π1 ->
    R_pres t
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Pending (ECASReg Offer) (SCASRegTSO Offer) s1 t0 op) ρ0 π0)
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Idle (ECASReg Offer) (SCASRegTSO Offer) s2) ρ0 π1).
  Proof.
    intros Hneq HToffer HTempty Hπ.
    unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
    simpl.
    repeat split; intros; simpl in *; auto.
    - rewrite <- Hπ. auto.
    - rewrite Hπ. auto.
    - destruct H as [Hlin _]. rewrite <- Hπ. exact Hlin.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HTempty HTbad) as Heq.
      discriminate Heq.
    - rewrite <- Hπ. auto.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HTempty HTbad) as Heq.
      discriminate Heq.
    - destruct H as [t2 [HTbad _]].
      pose proof (Tail_unique _ _ _ _ HToffer HTbad) as Heq.
      discriminate Heq.
    - destruct H as [[[HTbad _] _] | [other [[t2 [HTbad _]] _]]].
      + pose proof (Tail_unique _ _ _ _ HToffer HTbad) as Heq.
        inversion Heq; subst. contradiction.
      + pose proof (Tail_unique _ _ _ _ HToffer HTbad) as Heq.
        discriminate Heq.
  Qed.

  Lemma R_pres_accepted_to_empty_other t t0 t2 v other
      (op : Sig.op (ECASReg Offer)) s1 s2
      (ρ0 : EExchState) (π0 : tmap Semantics.LinState) :
    t0 <> t ->
    TSOState (Accepted t0 t2 v other) s1 ->
    TSOState Empty s2 ->
    R_pres t
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Pending (ECASReg Offer) (SCASRegTSO Offer) s1 t0 op) ρ0 π0)
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Idle (ECASReg Offer) (SCASRegTSO Offer) s2) ρ0 π0).
  Proof.
    intros Hneq HTacc HTempty.
    unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
    simpl.
    repeat split; intros; simpl in *; auto.
    - destruct H as [Hlin _]. exact Hlin.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HTempty HTbad) as Heq.
      discriminate Heq.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HTempty HTbad) as Heq.
      discriminate Heq.
    - destruct H as [tx [HTbad _]].
      pose proof (Tail_unique _ _ _ _ HTacc HTbad) as Heq.
      inversion Heq; subst. contradiction.
    - destruct H as [[[HTbad _] _] | [x [[tx [HTbad _]] _]]].
      + pose proof (Tail_unique _ _ _ _ HTacc HTbad) as Heq.
        discriminate Heq.
      + pose proof (Tail_unique _ _ _ _ HTacc HTbad) as Heq.
        inversion Heq; subst. contradiction.
  Qed.

  Lemma R_pres_offer_to_accepted_pair_other current owner ov v t'
      (op : Sig.op (ECASReg Offer)) s1 s2
      (π0 π1 : tmap Semantics.LinState) :
    current <> t' ->
    owner <> current ->
    TSOState (Offered owner ov) s1 ->
    TSOState (Accepted owner current ov v) s2 ->
    TMap.find owner π0 = Some (Semantics.ls_inv (exch ov)) ->
    π1 =
      TMap.add current (Semantics.ls_linr (exch v) (Some ov))
        (TMap.add owner (Semantics.ls_linr (exch ov) (Some v))
          (TMap.add current (Semantics.ls_lini (exch v))
            (TMap.add owner (Semantics.ls_lini (exch ov)) π0))) ->
    R_pres t'
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Pending (ECASReg Offer) (SCASRegTSO Offer) s1 current op) ExSIdle π0)
      (@Build_ProofStateSingle (li_sig E) (li_sig F) (li_lts E) (li_lts F)
        (@Idle (ECASReg Offer) (SCASRegTSO Offer) s2) ExSIdle π1).
  Proof.
    intros Hcur Howncur HToffer HTacc Howner Hπ1.
    subst π1.
    unfold R_pres, ALin, NoOfferBy, AcceptedByFirst, FirstLive, OfferedBy, Disj, Conj.
    simpl.
    repeat split; intros; simpl in *.
    - destruct (PositiveMap.E.eq_dec owner t'); subst.
      + rewrite Howner in H. discriminate.
      + rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        exact H.
    - destruct (PositiveMap.E.eq_dec owner t'); subst.
      + rewrite PositiveMap.gso in H; [|congruence].
        rewrite PositiveMap.gss in H. discriminate.
      + rewrite PositiveMap.gso in H; [|auto].
        rewrite PositiveMap.gso in H; [|auto].
        rewrite PositiveMap.gso in H; [|auto].
        rewrite PositiveMap.gso in H; [|auto].
        exact H.
    - destruct H as [Hlin Hno].
      destruct (PositiveMap.E.eq_dec owner t'); subst.
      + exfalso. apply (Hno ov). exact HToffer.
      + rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        exact Hlin.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HTacc HTbad) as Heq.
      discriminate Heq.
    - destruct (PositiveMap.E.eq_dec owner t'); subst.
      + rewrite Howner in H. discriminate.
      + rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        rewrite PositiveMap.gso; [|auto].
        exact H.
    - intro HTbad.
      pose proof (Tail_unique _ _ _ _ HTacc HTbad) as Heq.
      discriminate Heq.
    - destruct H as [t2 [HTbad _]].
      pose proof (Tail_unique _ _ _ _ HToffer HTbad) as Heq.
      discriminate Heq.
    - destruct H as [[[HTlive [Hrho Hlin]] Hlin'] | [other [[t2 [HTbad _]] _]]].
      + pose proof (Tail_unique _ _ _ _ HToffer HTlive) as Heq.
        inversion Heq; subst.
        right. exists v. split.
        * exists current. repeat split; auto.
          unfold ALin; simpl.
          rewrite PositiveMap.gso; [rewrite PositiveMap.gss; auto|auto].
        * unfold ALin; simpl.
          rewrite PositiveMap.gso; [rewrite PositiveMap.gss; auto|auto].
      + pose proof (Tail_unique _ _ _ _ HToffer HTbad) as Heq.
        discriminate Heq.
  Qed.

  Ltac solve_no_exch_error :=
    unfold ANoError; intros ? ? Herr;
    inversion Herr.

  Ltac solve_exch_obligation :=
    first [
      solve_no_exch_error
    | apply ConjLeftImpl, ImplRefl
    | intros []; apply ConjLeftImpl, ImplRefl
    ].

  Program Definition Mexchanger : layer_implementation E F := {|
    li_impl m t :=
      match m with
      | exch v => exch_impl v t
      end
  |}.
  Next Obligation.
    refine (@RGILogic.soundness
      (li_sig E) (li_sig F) (li_lts E) (li_lts F)
      _ R G I _ _ _ (li_init E) (li_init F)
      ltac:(unfold I, ExchRel, TSOState, initE; simpl;
        left; split;
        [exists xH; split; [intro; lia|intros; reflexivity]|reflexivity])).
    {
      constructor.
      unfold R, R_pres. intros. tauto.
    }
    {
      unfold G, R.
      intros t1 t2 Hneq s1 s2 Hstep.
      destruct Hstep as [HG | [[Hinv | Hret] | Hid]]; eauto.
      - unfold GINV, Ginv, LiftRelation_π in Hinv.
        destruct Hinv as (? & ? & ? & ? & Hπ).
        eapply R_pres_unchanged; [eauto|eauto|].
        rewrite Hπ. rewrite PositiveMap.gso; auto.
      - unfold GRET, Gret, LiftRelation_π in Hret.
        destruct Hret as (? & ? & ? & ? & ? & Hπ).
        eapply R_pres_unchanged; [eauto|eauto|].
        rewrite Hπ. rewrite PositiveMap.gro; auto.
      - unfold GId in Hid. subst. eapply R_pres_unchanged; reflexivity.
    }
    intros t; destruct f as [v].
    exists (I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t)).
    exists (fun ret => I //\\ ALin t (Semantics.ls_linr (exch v) ret)).
    constructor;
    try solve_conj_impl;
    try solve_conj_stable stableDB;
    try apply IGinvActive; try apply IGret.
    {
      intros ret σ0 ρ0 π0 H. exact (proj2 H).
    }
    simpl. unfold exch_impl.
    eapply provable_vis_safe with
      (P':=I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t))
      (Q':=fun offered =>
        I //\\ match offered with
               | true => FirstLive t v
               | false => ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t
               end);
    try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB];
    [intro offered; destruct offered; solve_conj_stable stableDB| | | ].
    {
      unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      inversion Hstep; subst.
      do 2 eexists. split; [apply rt_refl|]. split.
      - inversion Hstep0; subst.
        destruct Hpre as [HI [Hlin Hno]]; split; [exact HI|split; [exact Hlin|exact Hno]].
      - inversion Hstep0; subst.
        unfold G. intros.
        eapply R_pres_same_obs; simpl; auto.
    }
    {
      intro offered.
      unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      inversion Hstep; subst.
      dependent destruction H2.
      destruct Hpre as [HI [Hlin Hno]].
      pose proof (step_cas_empty_offer_res_inv t v offered _ _ Hstep0) as Hcas.
      destruct Hcas as [[Hoffered [h [Hfresh [Hmem Hs2]]]] |
                        [Hoffered [h [Hfresh [Hneq_empty Hs2]]]]]; subst offered.
      - subst s2.
        assert (HTempty_rho : TSOState Empty s1 /\ ρ0 = ExSIdle).
        {
          unfold I, ExchRel in HI; simpl in HI.
          destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπ]]]] |
            [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
          - split; auto.
          - exfalso.
            pose proof (Tail_fresh_value _ _ _ _ HT Hfresh) as Htail.
            rewrite Hmem in Htail. discriminate Htail.
          - exfalso.
            pose proof (Tail_fresh_value _ _ _ _ HT Hfresh) as Htail.
            rewrite Hmem in Htail. discriminate Htail.
        }
        destruct HTempty_rho as [HTempty Hrho].
        exists ρ0, π0. split; [apply rt_refl|]. split.
        + split.
          * unfold I, ExchRel; simpl.
            right; left. exists t, v. repeat split; auto.
            apply Tail_write_new.
          * unfold FirstLive, OfferedBy, ALin, Disj, Conj; simpl.
            left. repeat split; auto.
            apply Tail_write_new.
        + unfold G. intros t' Hneq'.
          eapply R_pres_empty_to_offer_other; eauto.
          apply Tail_write_new.
      - subst s2.
        assert (Htail_pres : forall o, TSOState o s1 ->
          TSOState o (mkCASRegTSO (cas_mem s1) (view_advance_all h))).
        {
          intros o HT.
          eapply Tail_advance_all_pres; eauto.
        }
        assert (HI_source : ExchRel s1 ρ0 π0).
        { unfold I in HI; simpl in HI; exact HI. }
        exists ρ0, π0. split; [apply rt_refl|]. split.
        + split.
          * unfold I; simpl.
            unfold ExchRel in *.
            destruct HI_source as [[HT Hrho] | [[to [vo [HT [Hrho Hπ]]]] |
              [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
            -- exfalso.
               apply Hneq_empty. eapply Tail_fresh_value; eauto.
            -- right; left. exists to, vo. repeat split; auto.
            -- right; right. exists t1, t2, v1, v2. split; auto.
          * split; auto.
            intros vx HTbad.
            unfold ExchRel in HI.
            destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπ]]]] |
              [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
            -- exfalso.
               apply Hneq_empty. eapply Tail_fresh_value; eauto.
            -- pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
               pose proof (Hno vo) as Hno_vo.
               inversion Heq; subst. apply Hno_vo. exact HT.
            -- pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
               discriminate Heq.
        + unfold G. intros t' Hneq'.
          eapply R_pres_tail_preserved; eauto.
    }
    intros offered; destruct offered.
    - eapply provable_vis_safe with
        (P':=I //\\ FirstLive t v)
        (Q':=fun revoked =>
          I //\\ match revoked with
                 | true => ALin t (Semantics.ls_linr (exch v) None)
                 | false => (fun s => exists other, AcceptedByFirst t v other s)
                 end);
      try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
      1: {
        intro revoked; destruct revoked;
        try solve_conj_stable stableDB.
        apply IAcceptedByFirstStable.
      }
      {
        unfold PUpdate.
        intros σ0 ρ0 π0 Hpre σ' Hstep.
        inversion Hstep; subst.
        inversion Hstep0; subst.
        do 2 eexists. split; [apply rt_refl|]. split.
        - destruct Hpre as [HI Hlive]. split; auto.
        - unfold G. intros.
          eapply R_pres_same_obs; simpl; auto.
      }
      {
        intro revoked.
        unfold PUpdate.
        intros σ0 ρ0 π0 Hpre σ' Hstep.
        inversion Hstep; subst.
        dependent destruction H2.
        destruct Hpre as [HI Hlive].
        unfold FirstLive, OfferedBy, AcceptedByFirst, Disj, Conj, ALin in Hlive.
        destruct Hlive as [[[Hoffered_tail [Hrho Hlini]] Hlini'] |
                           [other [[t2 [Haccepted_tail [Hrho Hlinr]]] Hlinr']]].
        + simpl in Hoffered_tail, Hrho, Hlini, Hlini'. subst ρ0.
          destruct (step_cas_tail_success_inv t (Offered t v) Empty revoked _ _ Hoffered_tail Hstep0)
            as [Hrevoked Hempty].
          subst revoked.
          exists ExSIdle,
            (TMap.add t (Semantics.ls_linr (exch v) None)
              (TMap.add t (Semantics.ls_lini (exch v)) π0)).
          split.
          * eapply rt_trans.
            -- eapply rt_step.
               eapply (Semantics.ps_inv t (exch v)).
               ++ eapply step_exch_offer. reflexivity.
               ++ exact Hlini.
            -- eapply rt_step.
               eapply (Semantics.ps_ret t (exch v) None).
               ++ eapply step_exch_revoke. reflexivity.
               ++ rewrite PositiveMap.gss. auto.
          * split.
            -- split.
               ++ unfold I, ExchRel; simpl. left; split; auto.
	               ++ unfold ALin; simpl. rewrite PositiveMap.gss. auto.
            -- unfold G. intros t' Hneq'.
               eapply R_pres_offer_to_empty_other; eauto.
               simpl.
               rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
        + simpl in Haccepted_tail, Hrho, Hlinr, Hlinr'. subst ρ0.
          assert (Hdiff : Accepted t t2 v other <> Offered t v).
          { discriminate. }
          destruct (step_cas_tail_fail_inv t (Offered t v) Empty revoked _ _
            (Accepted t t2 v other) Haccepted_tail Hdiff Hstep0) as [Hrevoked Hacc2].
          subst revoked.
          destruct (step_cas_res_inv t (Offered t v) Empty false _ _ Hstep0)
            as [[Hbad _] | [_ [h [Hfresh [_ Hs2]]]]]; [discriminate|].
          assert (Htail_pres : forall o, TSOState o s1 -> TSOState o s2).
          {
            intros o HT. subst s2.
            eapply Tail_advance_all_pres; eauto.
          }
          exists ExSIdle, π0. split; [apply rt_refl|]. split.
          * split.
            -- unfold I, ExchRel; simpl. right; right.
               exists t, t2, v, other. split; auto.
            -- exists other. exists t2. repeat split; auto.
          * unfold G. intros t' Hneq'.
            eapply R_pres_tail_preserved; eauto.
      }
      intros revoked; destruct revoked.
      + eapply provable_ret_safe;
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try apply ImplRefl.
      + eapply provable_vis_safe with
          (P':=I //\\ (fun s => exists other, AcceptedByFirst t v other s))
          (Q':=fun w =>
            I //\\ (fun s => exists other,
              (AcceptedByFirst t v other //\\
               (fun _ => exists t2, w = Accepted t t2 v other)) s));
        try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
        1: apply IAcceptedByFirstStable.
        1: { intro w. apply IAcceptedByFirstPureStable. }
        {
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          inversion Hstep0; subst.
          do 2 eexists. split; [apply rt_refl|]. split.
          - destruct Hpre as [HI Hacc]. split; auto.
          - unfold G. intros.
            eapply R_pres_same_obs; simpl; auto.
        }
        {
          intro w.
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          dependent destruction H2.
          destruct Hpre as [HI [other Hacc]].
          unfold AcceptedByFirst, ALin in Hacc.
          destruct Hacc as [t2 [Hacc_tail [Hrho Hlinr]]].
          simpl in Hacc_tail, Hrho, Hlinr. subst ρ0.
          destruct (step_get_tail_inv t w _ _ (Accepted t t2 v other) Hacc_tail Hstep0)
            as [Hw Hacc2].
          subst w.
          destruct (step_get_res_inv t (Accepted t t2 v other) _ _ Hstep0)
            as [h [Hlt [_ Hs2]]].
          assert (Htail_pres : forall o, TSOState o s1 -> TSOState o s2).
          {
            intros o HT. subst s2.
            eapply Tail_get_pres; eauto.
          }
          exists ExSIdle, π0. split; [apply rt_refl|]. split.
          - split.
            + unfold I, ExchRel; simpl. right; right.
              exists t, t2, v, other. split; auto.
            + exists other. split.
              * exists t2. repeat split; auto.
              * exists t2. reflexivity.
          - unfold G. intros t' Hneq'.
            eapply R_pres_tail_preserved; eauto.
        }
        intros w.
        destruct w as [ot ov | tw1 tw2 twv1 twv2 |].
        * eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB.
          intros ? [_ [other [_ [t2 Hp]]]]. simpl in Hp. discriminate.
        * eapply provable_vis_safe with
            (P':=I //\\ (fun s => exists other,
              (AcceptedByFirst t v other //\\
               (fun _ => exists t2, Accepted tw1 tw2 twv1 twv2 = Accepted t t2 v other)) s))
            (Q':=fun _ =>
              I //\\ ALin t (Semantics.ls_linr (exch v) (Some twv2)));
          try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
          1: apply IAcceptedByFirstPureStable.
          {
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            inversion Hstep; subst.
            inversion Hstep0; subst.
            do 2 eexists. split; [apply rt_refl|]. split.
            - destruct Hpre as [HI Hacc]. split; auto.
            - unfold G. intros.
              eapply R_pres_same_obs; simpl; auto.
          }
          {
            intro cleanup_ret.
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            inversion Hstep; subst.
            dependent destruction H2.
            destruct Hpre as [HI [other [Hacc [t2eq Hp]]]].
            unfold AcceptedByFirst, ALin in Hacc.
            destruct Hacc as [t2 [Hacc_tail [Hrho Hlinr]]].
            simpl in Hacc_tail, Hrho, Hlinr. subst ρ0.
            simpl in Hp. inversion Hp; subst.
            pose proof (step_cas_res_inv t
              (Accepted t t2eq v other) Empty cleanup_ret _ _ Hstep0) as Hcas.
            destruct Hcas as [[Hret [h [Hfresh [Hmem Hs2]]]] |
                              [Hret [h [Hfresh [Hneq_exp Hs2]]]]].
            - subst s2.
              exists ExSIdle, π0. split; [apply rt_refl|]. split.
              + split.
                * unfold I, ExchRel; simpl. left; split; auto.
                  apply Tail_write_new.
                * unfold ALin; simpl. exact Hlinr.
              + unfold G. intros t' Hneq'.
                eapply R_pres_accepted_to_empty_other; eauto.
                apply Tail_write_new.
            - subst s2.
              assert (Htail_pres : forall o, TSOState o s1 ->
                TSOState o (mkCASRegTSO (cas_mem s1) (view_advance_all h))).
              {
                intros o HT. eapply Tail_advance_all_pres; eauto.
              }
              exists ExSIdle, π0. split; [apply rt_refl|]. split.
              + split.
                * unfold I in HI; simpl in HI.
                  unfold I, ExchRel; simpl.
                  unfold ExchRel in HI.
                  destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπ]]]] |
                    [t1 [t2' [v1 [v2 [HT Hrho]]]]]]].
                  -- left; split; auto.
                  -- right; left. exists to, vo. repeat split; auto.
                  -- right; right. exists t1, t2', v1, v2. split; auto.
                * unfold ALin; simpl. exact Hlinr.
              + unfold G. intros t' Hneq'.
                eapply R_pres_tail_preserved; eauto.
          }
          intros _.
          eapply provable_ret_safe;
          try solve_conj_stable stableDB.
          {
            intros ? [HI Hlinr].
            split; auto.
          }
          { apply ConjLeftImpl, ImplRefl. }
        * eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB.
          intros ? [_ [other [_ [t2 Hp]]]]. simpl in Hp. discriminate.
    - eapply provable_vis_safe with
        (P':=I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t))
        (Q':=fun w =>
          I //\\ match w with
                 | Offered _ _ => ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t
                 | _ => ALin t (Semantics.ls_linr (exch v) None)
                 end);
      try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
      1: { intro w; destruct w; solve_conj_stable stableDB. }
      {
        unfold PUpdate.
        intros σ0 ρ0 π0 Hpre σ' Hstep.
        inversion Hstep; subst.
        inversion Hstep0; subst.
        do 2 eexists. split; [apply rt_refl|]. split.
        - destruct Hpre as [HI [Hlin Hno]]. split; [exact HI|split; [exact Hlin|exact Hno]].
        - unfold G. intros.
          eapply R_pres_same_obs; simpl; auto.
      }
      {
        intro w.
        unfold PUpdate.
        intros σ0 ρ0 π0 Hpre σ' Hstep.
        inversion Hstep; subst.
        dependent destruction H2.
        destruct Hpre as [HI [Hlin Hno]].
        destruct (step_get_res_inv t w _ _ Hstep0) as [h [Hlt [Hw Hs2]]].
        assert (Htail_pres : forall o, TSOState o s1 -> TSOState o s2).
        {
          intros o HT. subst s2.
          eapply Tail_get_pres; eauto.
        }
        unfold I, ExchRel in HI; simpl in HI.
        destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπto]]]] |
          [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
        + assert (HwEmpty : w = Empty).
          {
            subst w. destruct HT as [hc [Hview Htail]].
            apply Htail. specialize (Hview t). lia.
          }
          subst w. subst s2. subst ρ0.
          exists ExSIdle,
            (TMap.add t (Semantics.ls_linr (exch v) None)
              (TMap.add t (Semantics.ls_lini (exch v)) π0)).
          split.
          * eapply rt_trans.
            -- eapply rt_step.
               eapply (Semantics.ps_inv t (exch v)).
               ++ eapply step_exch_offer. reflexivity.
               ++ exact Hlin.
            -- eapply rt_step.
               eapply (Semantics.ps_ret t (exch v) None).
               ++ eapply step_exch_revoke. reflexivity.
               ++ rewrite PositiveMap.gss. auto.
          * split.
            -- split.
               ++ unfold I, ExchRel; simpl. left; split; auto.
               ++ rewrite HwEmpty. unfold ALin; simpl. rewrite PositiveMap.gss. auto.
            -- unfold G. intros t' Hneq'.
               eapply R_pres_tail_preserved_pi.
               ++ unfold ExchRel. left; split; auto.
               ++ exact Htail_pres.
               ++ symmetry. rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
        + assert (HwOffered : w = Offered to vo).
          {
            subst w. destruct HT as [hc [Hview Htail]].
            apply Htail. specialize (Hview t). lia.
          }
          subst w.
          exists ρ0, π0. split; [apply rt_refl|]. split.
          * split.
            -- unfold I, ExchRel; simpl. right; left.
               exists to, vo. repeat split; auto.
            -- rewrite HwOffered. split; auto.
               intros vx HTbad.
               pose proof (Tail_unique _ _ _ _ (Htail_pres _ HT) HTbad) as Heq.
               pose proof (Hno vo) as Hno_vo.
               inversion Heq; subst. apply Hno_vo. exact HT.
          * unfold G. intros t' Hneq'.
            eapply R_pres_tail_preserved; eauto.
            unfold ExchRel. right; left. exists to, vo. repeat split; auto.
        + assert (HwAccepted : w = Accepted t1 t2 v1 v2).
          {
            subst w. destruct HT as [hc [Hview Htail]].
            apply Htail. specialize (Hview t). lia.
          }
          subst w. subst s2. subst ρ0.
          exists ExSIdle,
            (TMap.add t (Semantics.ls_linr (exch v) None)
              (TMap.add t (Semantics.ls_lini (exch v)) π0)).
          split.
          * eapply rt_trans.
            -- eapply rt_step.
               eapply (Semantics.ps_inv t (exch v)).
               ++ eapply step_exch_offer. reflexivity.
               ++ exact Hlin.
            -- eapply rt_step.
               eapply (Semantics.ps_ret t (exch v) None).
               ++ eapply step_exch_revoke. reflexivity.
               ++ rewrite PositiveMap.gss. auto.
          * split.
            -- split.
	               ++ unfold I, ExchRel; simpl. right; right.
	                  exists t1, t2, v1, v2. split; auto.
	               ++ rewrite HwAccepted. unfold ALin; simpl. rewrite PositiveMap.gss. auto.
            -- unfold G. intros t' Hneq'.
               eapply R_pres_tail_preserved_pi.
               ++ unfold ExchRel. right; right. exists t1, t2, v1, v2. split; auto.
               ++ exact Htail_pres.
               ++ symmetry. rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
      }
      intros w; destruct w as [ot ov | at1 at2 av1 av2 |].
      + eapply provable_vis_safe with
          (P':=I //\\ (ALin t (Semantics.ls_inv (exch v)) //\\ NoOfferBy t))
          (Q':=fun accepted : bool =>
            I //\\ (if accepted
                    then ALin t (Semantics.ls_linr (exch v) (Some ov))
                    else ALin t (Semantics.ls_linr (exch v) None)));
        try solve [solve_conj_impl|solve_exch_obligation|solve_conj_stable stableDB].
        1: { intro accepted; destruct accepted; solve_conj_stable stableDB. }
        {
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          inversion Hstep0; subst.
          do 2 eexists. split; [apply rt_refl|]. split.
          - destruct Hpre as [HI [Hlin Hno]]. split; [exact HI|split; [exact Hlin|exact Hno]].
          - unfold G. intros.
            eapply R_pres_same_obs; simpl; auto.
        }
        {
          intro accepted.
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          dependent destruction H2.
          destruct Hpre as [HI [Hlin Hno]].
          pose proof (step_cas_res_inv t (Offered ot ov) (Accepted ot t ov v)
            accepted _ _ Hstep0) as Hcas.
          unfold I, ExchRel in HI; simpl in HI.
          destruct Hcas as [[Haccepted [h [Hfresh [Hmem Hs2]]]] |
                            [Haccepted [h [Hfresh [Hneq_mem Hs2]]]]]; subst accepted.
          - destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπowner]]]] |
              [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
            + exfalso.
              pose proof (Tail_fresh_value _ _ _ _ HT Hfresh) as Htail.
              rewrite Hmem in Htail. discriminate Htail.
            + pose proof (Tail_fresh_value _ _ _ _ HT Hfresh) as Htail.
              rewrite Hmem in Htail. inversion Htail; subst to vo.
              assert (Hot_ne_t : ot <> t).
              {
                intro Heq. subst ot.
                apply (Hno ov). exact HT.
              }
              subst ρ0 s2.
              exists ExSIdle,
                (TMap.add t (Semantics.ls_linr (exch v) (Some ov))
                  (TMap.add ot (Semantics.ls_linr (exch ov) (Some v))
                    (TMap.add t (Semantics.ls_lini (exch v))
                      (TMap.add ot (Semantics.ls_lini (exch ov)) π0)))).
              split.
              * eapply rt_trans.
                -- eapply rt_step.
                   eapply (Semantics.ps_inv ot (exch ov)).
                   ++ eapply step_exch_offer. reflexivity.
                   ++ exact Hπowner.
                -- eapply rt_trans.
                   ++ eapply rt_step.
                      eapply (Semantics.ps_inv t (exch v)).
                      ** eapply step_exch_pair. reflexivity.
                      ** rewrite PositiveMap.gso; auto.
                   ++ eapply rt_trans.
                      ** eapply rt_step.
                         eapply (Semantics.ps_ret ot (exch ov) (Some v)).
                         --- eapply step_exch_accept. reflexivity.
                         --- rewrite PositiveMap.gso; [rewrite PositiveMap.gss; auto|auto].
                      ** eapply rt_step.
                         eapply (Semantics.ps_ret t (exch v) (Some ov)).
                         --- eapply step_exch_finish. reflexivity.
                         --- rewrite PositiveMap.gso; [rewrite PositiveMap.gss; auto|auto].
              * split.
                -- split.
                   ++ unfold I, ExchRel; simpl. right; right.
                      exists ot, t, ov, v. split.
                      ** apply Tail_write_new.
                      ** reflexivity.
                   ++ unfold ALin; simpl. rewrite PositiveMap.gss. auto.
                -- unfold G. intros t' Hneq'.
                   eapply R_pres_offer_to_accepted_pair_other; eauto.
                   apply Tail_write_new.
            + exfalso.
              pose proof (Tail_fresh_value _ _ _ _ HT Hfresh) as Htail.
              rewrite Hmem in Htail. discriminate Htail.
          - subst s2.
            assert (Htail_pres : forall o,
              TSOState o s1 ->
              TSOState o (mkCASRegTSO (cas_mem s1) (view_advance_all h))).
            {
              intros o HT.
              eapply Tail_advance_all_pres; eauto.
            }
            assert (Hrho_idle : ρ0 = ExSIdle).
            {
              destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπowner]]]] |
                [t1 [t2 [v1 [v2 [HT Hrho]]]]]]]; auto.
            }
            assert (HI_pres : ExchRel
              (mkCASRegTSO (cas_mem s1) (view_advance_all h)) ρ0
              (TMap.add t (Semantics.ls_linr (exch v) None)
                (TMap.add t (Semantics.ls_lini (exch v)) π0))).
            {
              destruct HI as [[HT Hrho] | [[to [vo [HT [Hrho Hπowner]]]] |
                [t1 [t2 [v1 [v2 [HT Hrho]]]]]]].
              - left; split; auto.
              - right; left. exists to, vo. repeat split; auto.
                destruct (PositiveMap.E.eq_dec t to); subst.
                + exfalso. apply (Hno vo). exact HT.
                + rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
              - right; right. exists t1, t2, v1, v2. split; auto.
            }
            subst ρ0.
            exists ExSIdle,
              (TMap.add t (Semantics.ls_linr (exch v) None)
                (TMap.add t (Semantics.ls_lini (exch v)) π0)).
            split.
            * eapply rt_trans.
              -- eapply rt_step.
                 eapply (Semantics.ps_inv t (exch v)).
                 ++ eapply step_exch_offer. reflexivity.
                 ++ exact Hlin.
              -- eapply rt_step.
                 eapply (Semantics.ps_ret t (exch v) None).
                 ++ eapply step_exch_revoke. reflexivity.
                 ++ rewrite PositiveMap.gss. auto.
            * split.
              -- split.
                 ++ unfold I; simpl. exact HI_pres.
                 ++ unfold ALin; simpl. rewrite PositiveMap.gss. auto.
	              -- unfold G. intros t' Hneq'.
	                 eapply R_pres_tail_preserved_pi.
	                 ++ exact HI.
	                 ++ exact Htail_pres.
	                 ++ symmetry. rewrite PositiveMap.gso; [rewrite PositiveMap.gso; auto|auto].
        }
        intros accepted; destruct accepted.
        * eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB;
          try apply ImplRefl.
        * eapply provable_ret_safe;
          try solve_conj_impl;
          try solve_conj_stable stableDB;
          try apply ImplRefl.
      + eapply provable_ret_safe;
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try apply ImplRefl.
      + eapply provable_ret_safe;
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try apply ImplRefl.
  Qed.

End ExchangerImplF.

Module ExchangerImplParam <: TypeParam.
  Parameter A : Type.
End ExchangerImplParam.

Module ExchangerImpl := ExchangerImplF(ExchangerImplParam).
