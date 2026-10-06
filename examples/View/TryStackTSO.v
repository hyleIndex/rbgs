(** Ported from CSL-Lin [examples/TryStackTSO.v] (hyleIndex/CSL-Lin, master 3f7baaa).
    View-based (timestamped) specification / proof, kept as close to the
    original as possible; changes are limited to the Rocq 9.2 / rbgs
    adaptation listed in [examples/View/README.md]. *)

Require Import Stdlib.FSets.FMapPositive.
Require Import Stdlib.Relations.Relation_Operators Stdlib.Relations.Operators_Properties.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Lists.List.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import examples.View.LegacyNotations.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGILogic.
Require Import examples.Common.AtomicLTS.
Require Import examples.View.ViewSpecs.

Module HeapSpec.
  Definition Addr := nat.
  Definition Heap (A : Type) : Type := Addr -> option A.

  Definition empty_heap {A : Type} : Heap A := fun _ => None.

  Definition heap_update {A : Type} (l : Addr) (v : A) (h : Heap A) : Heap A :=
    fun l' => if Nat.eqb l l' then Some v else h l'.

  Lemma HeapUpdateSelf {A : Type} (h : Heap A) l v :
    heap_update l v h l = Some v.
  Proof.
    unfold heap_update. rewrite Nat.eqb_refl. reflexivity.
  Qed.
End HeapSpec.

Module OwnedMemTSOSpec.
  Import LinCCALBase.
  Import LTSSpec.
  Import AtomicLTS.
  Import HeapSpec.

  Notation Time := positive.

  Variant LocStat : Type :=
  | LAlloc (t : tid)
  | LWritten.

  Variant EMem_op {A : Type} : Type :=
  | malloc
  | mread (l : Addr)
  | mwrite (l : Addr) (v : A).
  Arguments EMem_op : clear implicits.

  Definition EMem_ar {A : Type} (m : EMem_op A) : Type :=
    match m with
    | malloc => Addr
    | mread _ => A
    | mwrite _ _ => unit
    end.

  Canonical Structure EMem A :=
  {|
    Sig.op := EMem_op A;
    Sig.ar := EMem_ar;
  |}.

  Record OwnedMemState (A : Type) : Type := mkOwnedMemTSO {
    om_heap : Heap A;
    om_loc : Heap LocStat;
    om_view : tid -> Time;
  }.
  Arguments mkOwnedMemTSO {A}.
  Arguments om_heap {A}.
  Arguments om_loc {A}.
  Arguments om_view {A}.

  Definition upd_tid_time (H : tid -> Time) (t : tid) (h : Time) : tid -> Time :=
    fun t' => if Pos.eqb t t' then h else H t'.

  Definition view_advance_all (h : Time) : tid -> Time :=
    fun _ => h.

  Definition initOwnedMem {A : Type} : OwnedMemState A :=
    mkOwnedMemTSO empty_heap empty_heap (fun _ => xH).

  Variant StepMemTSO {A : Type} :
      @ThreadEvent (EMem A) -> OwnedMemState A -> OwnedMemState A -> Prop :=
  | step_malloc_inv t s :
      StepMemTSO {| te_tid := t; te_ev := InvEv malloc |} s s
  | step_malloc_res t ret init h s1 s2 :
      (forall t0, Pos.lt (om_view s1 t0) h) ->
      om_heap s1 ret = None ->
      om_heap s2 = heap_update ret init (om_heap s1) ->
      om_loc s2 = heap_update ret (LAlloc t) (om_loc s1) ->
      om_view s2 = view_advance_all h ->
      StepMemTSO {| te_tid := t; te_ev := ResEv malloc ret |} s1 s2

  | step_mread_inv t l s :
      StepMemTSO {| te_tid := t; te_ev := InvEv (mread l) |} s s
  | step_mread_res t l v h s1 s2 :
      (forall t0, Pos.lt (om_view s1 t0) h) ->
      om_heap s1 l = Some v ->
      om_loc s1 l = Some LWritten ->
      om_heap s2 = om_heap s1 ->
      om_loc s2 = om_loc s1 ->
      om_view s2 = upd_tid_time (om_view s1) t h ->
      StepMemTSO {| te_tid := t; te_ev := ResEv (mread l) v |} s1 s2

  | step_mwrite_inv t l v s :
      StepMemTSO {| te_tid := t; te_ev := InvEv (mwrite l v) |} s s
  | step_mwrite_res t l v h s1 s2 :
      (forall t0, Pos.lt (om_view s1 t0) h) ->
      om_loc s1 l = Some (LAlloc t) ->
      om_heap s2 = heap_update l v (om_heap s1) ->
      om_loc s2 = heap_update l LWritten (om_loc s1) ->
      om_view s2 = view_advance_all h ->
      StepMemTSO {| te_tid := t; te_ev := ResEv (mwrite l v) tt |} s1 s2.

  Variant ErrorMemTSO {A : Type} :
      @ThreadEvent (EMem A) -> @AState (EMem A) (OwnedMemState A) -> Prop :=
  | error_mread_unwritten t l s :
      om_loc s l <> Some LWritten ->
      ErrorMemTSO {| te_tid := t; te_ev := InvEv (mread l) |} (Idle s)
  | error_mwrite_unowned t l v s :
      om_loc s l <> Some (LAlloc t) ->
      ErrorMemTSO {| te_tid := t; te_ev := InvEv (mwrite l v) |} (Idle s)
  | error_mwrite_racy t t' l l' v v' s :
      t <> t' ->
      l = l' ->
      ErrorMemTSO
        {| te_tid := t; te_ev := InvEv (mwrite l v) |}
        (Pending s t' (mwrite l' v')).

  Definition VMemTSO {A : Type} : @LTS (EMem A) :=
    VAE StepMemTSO ErrorMemTSO.

  Definition malloc_response {A : Type} (ev : @ThreadEvent (EMem A)) : option Addr :=
    match te_ev ev with
    | ResEv malloc ret => Some ret
    | _ => None
    end.
End OwnedMemTSOSpec.

Module Type TypeParam.
  Parameter A : Type.
End TypeParam.

Module TryStackTSOImplF (P : TypeParam).
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import LegacyAssertionNotations.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TryStackSpec CASRegTSOSpec HeapSpec OwnedMemTSOSpec.
  Import ListNotations.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  Definition A : Type := P.A.

  Definition initTop : SCASRegTSO (option Addr) :=
    mkCASRegTSO (fun _ => None) (fun _ => xH).

  Definition E : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ECASReg (option Addr)) (EMem (A * option Addr));
    li_lts := tens_lts VCASRegTSO VMemTSO;
    li_init := (Idle initTop, Idle initOwnedMem);
  |}.

  Definition F : layer_interface :=
  {|
    li_sig := ETryStack A;
    li_lts := VTryStack;
    li_init := Idle nil;
  |}.

  Definition cas_op := Sig.op (ECASReg (option Addr)).
  Definition mem_op := Sig.op (EMem (A * option Addr)).
  Definition in_cas := @inl cas_op mem_op.
  Definition in_mem := @inr cas_op mem_op.

  Definition push_impl (v : A) (_ : tid) : Prog (li_sig E) (TryResult unit) :=
    in_cas get >= oldPtr =>
    in_mem malloc >= newLoc =>
    in_mem (mwrite newLoc (v, oldPtr)) >= _ =>
    in_cas (cas oldPtr (Some newLoc)) >= succ =>
    Ret (if succ then OK tt else FAIL).

  Definition pop_impl (_ : tid) : Prog (li_sig E) (TryResult (option A)) :=
    in_cas get >= oldPtr =>
    match oldPtr with
    | Some oldLoc =>
        in_mem (mread oldLoc) >= head =>
        in_cas (cas oldPtr (snd head)) >= succ =>
        Ret (if succ then OK (Some (fst head)) else FAIL)
    | None => Ret (OK None)
    end.

  Definition Tail {B : Type} (mem : Time -> B) (view : tid -> Time) (v : B) : Prop :=
    exists h,
      (forall t, Pos.le h (view t)) /\
      (forall h', Pos.le h h' -> mem h' = v).

  Definition TSOState (top : option Addr) (s : SCASRegTSO (option Addr)) : Prop :=
    Tail (cas_mem s) (cas_view s) top.

  Lemma Tail_fresh_value {B} mem view (v : B) h :
    Tail mem view v ->
    (forall t, Pos.lt (view t) h) ->
    mem h = v.
  Proof.
    intros [hc [Hview Htail]] Hfresh.
    apply Htail.
    specialize (Hfresh xH).
    specialize (Hview xH).
    lia.
  Qed.

  Lemma Tail_read_value {B} mem view (v : B) tid0 h :
    Tail mem view v ->
    Pos.lt (view tid0) h ->
    mem h = v.
  Proof.
    intros [hc [Hview Htail]] Hlt.
    apply Htail.
    specialize (Hview tid0).
    lia.
  Qed.

  Lemma Tail_get_pres {B} mem view (v : B) tid0 h :
    Tail mem view v ->
    Pos.lt (view tid0) h ->
    Tail mem (upd_tid_time view tid0 h) v.
  Proof.
    intros [hc [Hview Htail]] Hlt.
    exists hc; split; auto.
    intro t'. unfold upd_tid_time.
    destruct (Pos.eqb_spec tid0 t'); subst; specialize (Hview t'); lia.
  Qed.

  Lemma Tail_advance_all_pres {B} mem view (v : B) h :
    Tail mem view v ->
    (forall t, Pos.lt (view t) h) ->
    Tail mem (CASRegTSOSpec.view_advance_all h) v.
  Proof.
    intros HT Hfresh.
    exists h; split.
    - intro t. unfold CASRegTSOSpec.view_advance_all. lia.
    - intros h' Hle.
      eapply Tail_fresh_value; eauto.
      intro t. specialize (Hfresh t). lia.
  Qed.

  Lemma Tail_write_new {B} mem (v : B) h :
    Tail (mem_write mem h v) (CASRegTSOSpec.view_advance_all h) v.
  Proof.
    exists h; split.
    - intro t. unfold CASRegTSOSpec.view_advance_all. lia.
    - intros h' Hle. unfold mem_write.
      destruct (Pos.leb_spec h h'); [reflexivity|lia].
  Qed.

  Lemma Tail_unique {B} mem view (v1 v2 : B) :
    Tail mem view v1 ->
    Tail mem view v2 ->
    v1 = v2.
  Proof.
    intros [h1 [Hview1 Htail1]] [h2 [Hview2 Htail2]].
    pose proof (Htail1 (Pos.max h1 h2) (Pos.le_max_l h1 h2)) as H1.
    pose proof (Htail2 (Pos.max h1 h2) (Pos.le_max_r h1 h2)) as H2.
    exact (eq_trans (eq_sym H1) H2).
  Qed.

  Inductive listseg_loc
    (h : Heap (A * option Addr)) (loc : Heap LocStat) :
    option Addr -> list A -> Prop :=
  | listseg_loc_nil :
      listseg_loc h loc None nil
  | listseg_loc_cons l v nxt vs :
      h l = Some (v, nxt) ->
      loc l = Some LWritten ->
      listseg_loc h loc nxt vs ->
      listseg_loc h loc (Some l) (v :: vs).

  Lemma listseg_loc_defined h loc l vs :
    listseg_loc h loc (Some l) vs ->
    exists v nxt vs',
      vs = v :: vs' /\
      h l = Some (v, nxt) /\
      loc l = Some LWritten /\
      listseg_loc h loc nxt vs'.
  Proof.
    remember (Some l) as top eqn:Heq.
    intros Hls. revert l Heq.
    induction Hls; intros; inversion Heq; subst.
    exists v, nxt, vs. auto.
  Qed.

  Lemma listseg_loc_none h loc vs :
    listseg_loc h loc None vs -> vs = nil.
  Proof.
    intros Hls. inversion Hls; auto.
  Qed.

  Lemma listseg_loc_update_alloc h loc top vs l p t :
    listseg_loc h loc top vs ->
    h l = None ->
    listseg_loc
      (heap_update l p h)
      (heap_update l (LAlloc t) loc)
      top vs.
  Proof.
    intros Hls Hfresh.
    induction Hls.
    - constructor.
    - econstructor.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst. congruence.
        * exact H.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst. congruence.
        * exact H0.
      + apply IHHls.
  Qed.

  Lemma listseg_loc_update_unlinked h loc top vs l p t :
    listseg_loc h loc top vs ->
    loc l = Some (LAlloc t) ->
    listseg_loc
      (heap_update l p h)
      (heap_update l LWritten loc)
      top vs.
  Proof.
    intros Hls Hown.
    induction Hls.
    - constructor.
    - econstructor.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst.
          rewrite H0 in Hown. discriminate.
        * exact H.
      + unfold heap_update.
        destruct (Nat.eqb l l0) eqn:Heq.
        * apply Nat.eqb_eq in Heq. subst.
          rewrite H0 in Hown. discriminate.
        * exact H0.
      + apply IHHls.
  Qed.

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  Definition cas_state (s : State (li_lts E)) : SCASRegTSO (option Addr) :=
    state (fst s).

  Definition mem_state (s : State (li_lts E)) : Heap (A * option Addr) :=
    om_heap (state (snd s)).

  Definition loc_state (s : State (li_lts E)) : Heap LocStat :=
    om_loc (state (snd s)).

  Definition pending_write_owned (s : State (li_lts E)) : Prop :=
    match snd s with
    | Pending mem t (mwrite l _) => om_loc mem l = Some (LAlloc t)
    | _ => True
    end.

  Definition loc_defined (s : State (li_lts E)) : Prop :=
    forall l st, loc_state s l = Some st -> exists p, mem_state s l = Some p.

  Definition written_heap_preserved (s1 s2 : State (li_lts E)) : Prop :=
    forall l v,
      loc_state s1 l = Some LWritten ->
      mem_state s1 l = Some v ->
      loc_state s2 l = Some LWritten /\
      mem_state s2 l = Some v.

  Definition owned_preserved_for (t : tid) (s1 s2 : State (li_lts E)) : Prop :=
    forall l v,
      loc_state s1 l = Some (LAlloc t) ->
      mem_state s1 l = Some v ->
      loc_state s2 l = Some (LAlloc t) /\
      mem_state s2 l = Some v.

  Definition TopIs top : assertion :=
    fun s => TSOState top (cas_state (σ s)).

  Definition I : assertion :=
    fun s => exists stk top,
      ρ s = Idle stk /\
      TopIs top s /\
      listseg_loc (mem_state (σ s)) (loc_state (σ s)) top stk /\
      pending_write_owned (σ s) /\
      loc_defined (σ s).

  Definition HCell l p : assertion :=
    fun s =>
      mem_state (σ s) l = Some p /\
      loc_state (σ s) l = Some LWritten.

  Definition HWritten l : assertion :=
    fun s => exists p, HCell l p s.

  Definition HOwned t l : assertion :=
    fun s => exists p,
      mem_state (σ s) l = Some p /\
      loc_state (σ s) l = Some (LAlloc t).

  Definition G t : rg_relation :=
    fun s1 s2 =>
      I s2 /\
      written_heap_preserved (σ s1) (σ s2) /\
      (forall t', t <> t' -> owned_preserved_for t' (σ s1) (σ s2)) /\
      (forall t', t <> t' -> TMap.find t' (π s1) = TMap.find t' (π s2)).

  Definition R t : rg_relation :=
    fun s1 s2 =>
      written_heap_preserved (σ s1) (σ s2) /\
      owned_preserved_for t (σ s1) (σ s2) /\
      TMap.find t (π s1) = TMap.find t (π s2).

  Lemma Istable {t} : Stable (R t) I I.
  Proof.
    unfold Stable. apply ConjRightImpl, ImplRefl.
  Qed.

  Lemma ALinstable {t ls}: Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, ALin, R.
    intros s [[x [Hlin [_ [_ Hpi]]]] _].
    rewrite <- Hpi. auto.
  Qed.

  Lemma HCellStable {t l p}: Stable (R t) I (HCell l p).
  Proof.
    unfold Stable, R, HCell, written_heap_preserved.
    intros s Hstable.
    destruct Hstable as [[x [[Hmem Hloc] [Hwritten [_ _]]]] HI].
    specialize (Hwritten l p Hloc Hmem) as [Hloc' Hmem'].
    split; auto.
  Qed.

  Lemma HOwnedStable {t l}: Stable (R t) I (HOwned t l).
  Proof.
    unfold Stable, R, HOwned, owned_preserved_for.
    intros s Hstable.
    destruct Hstable as [[x [[p [Hmem Hloc]] [_ [Howned _]]]] HI].
    specialize (Howned l p Hloc Hmem) as [Hloc' Hmem'].
    exists p. auto.
  Qed.

  Lemma HWrittenStable {t l}: Stable (R t) I (HWritten l).
  Proof.
    unfold Stable, HWritten.
    intros s [[x [[p Hcell] Hrel]] HI].
    exists p.
    eapply HCellStable.
    split; [exists x; split; eauto|auto].
  Qed.

  Create HintDb stableDB.
  Hint Resolve Istable ALinstable HCellStable HOwnedStable HWrittenStable : stableDB.

  Ltac inversion_thread_event_eq :=
    repeat match goal with
    | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
        inversion H; subst; clear H
    | H : InvEv _ = InvEv _ |- _ =>
        inversion H; subst; clear H
    | H : ResEv _ _ = ResEv _ _ |- _ =>
        inversion H; subst; clear H
    | H : inl _ = inr _ |- _ => discriminate H
    | H : inr _ = inl _ |- _ => discriminate H
    end.

  Lemma IGinv : forall tid0 f0, ⊨ Ginv tid0 f0 ⊚ I ==>> I //\\ ALin tid0 (Semantics.ls_inv f0).
  Proof.
    unfold I, ALin, Ginv, LiftRelation_π.
    intros tid0 f0 s [x [HI [Hσ [Hρ [Hfind Hπ]]]]].
    destruct x as [σx ρx πx].
    destruct s as [σs ρs πs].
    simpl in *.
    destruct HI as [stk [top [Hrho [Htop [Hls [Hpend Hdef]]]]]].
    subst σs ρs.
    split.
    - exists stk, top. split.
      + exact Hrho.
      + split.
        * exact Htop.
        * split.
          -- exact Hls.
          -- split.
             ++ exact Hpend.
             ++ exact Hdef.
    - rewrite Hπ. simpl. rewrite TMap.gss; auto.
  Qed.

  Lemma IGret : forall tid0 f0 ret,
    ⊨ Gret tid0 f0 ret ⊚ (I //\\ ALin tid0 (Semantics.ls_linr f0 ret)) ==>> I.
  Proof.
    unfold I, ALin, Gret, LiftRelation_π.
    intros tid0 f0 ret s [x [[HI Hlin] [Hσ [Hρ [Hfind Hπ]]]]].
    destruct x as [σx ρx πx].
    destruct s as [σs ρs πs].
    simpl in *.
    destruct HI as [stk [top [Hrho [Htop [Hls [Hpend Hdef]]]]]].
    subst σs ρs.
    exists stk, top. split.
    - exact Hrho.
    - split.
      + exact Htop.
      + split.
        * exact Hls.
        * split.
          -- exact Hpend.
          -- exact Hdef.
  Qed.

  Lemma cas_get_no_error t (P : assertion) :
    ⊨ P ==>>
      ANoError {| te_tid := t; te_ev := InvEv (in_cas get) |}.
  Proof.
    unfold ANoError.
    intros [σ0 ρ0 π0] _ Herror.
    destruct σ0 as [cas mem]; simpl in *.
    inversion Herror; subst; inversion_thread_event_eq.
  Qed.

  Lemma cas_cas_no_error t old new (P : assertion) :
    ⊨ P ==>>
      ANoError {| te_tid := t; te_ev := InvEv (in_cas (cas old new)) |}.
  Proof.
    unfold ANoError.
    intros [σ0 ρ0 π0] _ Herror.
    destruct σ0 as [cas0 mem]; simpl in *.
    inversion Herror; subst; inversion_thread_event_eq.
  Qed.

  Lemma malloc_no_error t (P : assertion) :
    ⊨ P ==>>
      ANoError {| te_tid := t; te_ev := InvEv (in_mem malloc) |}.
  Proof.
    unfold ANoError.
    intros [σ0 ρ0 π0] _ Herror.
    destruct σ0 as [cas mem]; simpl in *.
    inversion Herror; subst; inversion_thread_event_eq.
  Qed.

  Lemma mwrite_owned_no_error t l v :
    ⊨ I //\\ HOwned t l ==>>
      ANoError {| te_tid := t; te_ev := InvEv (in_mem (mwrite l v)) |}.
  Proof.
    unfold I, HOwned, ANoError.
    intros [σ0 ρ0 π0] [[stk [top [Hr [Htop [Hls [Hpend Hdef]]]]]] [p [Hheap Hloc]]] Herror.
    destruct σ0 as [cas mem]; simpl in *.
    destruct mem as [ms | ms tp op]; simpl in *.
    - inversion Herror; subst; inversion_thread_event_eq; simpl in *; try congruence.
      match goal with
      | Hneq : om_loc ms l <> Some (LAlloc t) |- _ =>
          apply Hneq; exact Hloc
      end.
    - destruct op as [|rl|wl wv]; simpl in *;
        inversion Herror; subst; inversion_thread_event_eq; simpl in *; try congruence.
      subst.
      unfold loc_state in *; simpl in *.
      congruence.
  Qed.

  Lemma mread_written_no_error t l :
    ⊨ HWritten l ==>>
      ANoError {| te_tid := t; te_ev := InvEv (in_mem (mread l)) |}.
  Proof.
    unfold HWritten, HCell, ANoError.
    intros [σ0 ρ0 π0] [p [Hheap Hloc]] Herror.
    destruct σ0 as [cas mem]; simpl in *.
    inversion Herror; subst; repeat match goal with
      | H : {| te_tid := _; te_ev := _ |} = {| te_tid := _; te_ev := _ |} |- _ =>
          inversion H; subst; clear H
      | H : InvEv _ = InvEv _ |- _ =>
          inversion H; subst; clear H
      end; simpl in *; try congruence.
    match goal with
    | Hneq : om_loc _ l <> Some LWritten |- _ =>
        apply Hneq; exact Hloc
    end.
  Qed.

  Lemma cas_get_inv_pres t f :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_cas get) |}
      (I //\\ ALin t (Semantics.ls_inv f))
      (I //\\ ALin t (Semantics.ls_inv f)).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hcas Hmem]; subst.
    inversion Hcas; subst.
    dependent destruction Hstep.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - exact Hpre.
    - unfold G. split.
      + exact (proj1 Hpre).
      + split.
        * unfold written_heap_preserved. intros; split; auto.
        * split.
          -- unfold owned_preserved_for. intros; split; auto.
          -- intros; auto.
  Qed.

  Lemma cas_get_res_push t v ret :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas get) ret |}
      (I //\\ ALin t (Semantics.ls_inv (push v)))
      (I //\\ ALin t (Semantics.ls_inv (push v))).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hcas Hmem]; subst.
    inversion Hcas; subst.
    dependent destruction Hstep.
    dependent destruction H2.
    unfold I, ALin, TopIs in Hpre; simpl in *.
    destruct Hpre as [[stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]] Hlin].
    assert (HreadTop : cas_mem s1 h = top).
    { eapply Tail_read_value; eauto. }
    assert (HTop' : TSOState top (mkCASRegTSO (cas_mem s1) (CASRegTSOSpec.upd_tid_time (cas_view s1) t h))).
    { eapply Tail_get_pres; eauto. }
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split.
      + exists stk. exists (top : option Addr).
        split; [exact Hr|].
        split; [exact HTop'|].
        split; [exact Hls|].
        split; [exact Hpend|exact Hdef].
      + exact Hlin.
    - unfold G, written_heap_preserved, owned_preserved_for, I, TopIs; simpl.
      split.
      + exists stk. exists (top : option Addr).
        split; [exact Hr|].
        split; [exact HTop'|].
        split; [exact Hls|].
        split; [exact Hpend|exact Hdef].
      + split.
        * intros; split; auto.
        * split.
	          -- intros; split; auto.
	          -- intros; auto.
  Qed.

  Definition cas_response (ev : @ThreadEvent (ECASReg (option Addr))) : bool :=
    match te_ev ev with
    | ResEv (cas _ _) ret => ret
    | _ => false
    end.

  Definition get_response (ev : @ThreadEvent (ECASReg (option Addr))) : option (option Addr) :=
    match te_ev ev with
    | ResEv get ret => Some ret
    | _ => None
    end.

  Lemma step_get_res_inv tid0 (ret : option Addr) (s1 s2 : SCASRegTSO (option Addr)) :
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv get ret |} s1 s2 ->
    exists h,
      Pos.lt (cas_view s1 tid0) h /\
      ret = cas_mem s1 h /\
      s2 = mkCASRegTSO (cas_mem s1) (CASRegTSOSpec.upd_tid_time (cas_view s1) tid0 h).
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
    - subst ret. destruct HT as [hc [Hview Htail]].
      apply Htail. specialize (Hview tid0). lia.
    - subst s2. eapply Tail_get_pres; eauto.
  Qed.

  Lemma step_cas_res_inv tid0 (expected desired : option Addr) ret s1 s2 :
    StepCASRegTSO {| te_tid := tid0; te_ev := ResEv (cas expected desired) ret |} s1 s2 ->
    (ret = true /\
      exists h,
        (forall t0, Pos.lt (cas_view s1 t0) h) /\
        cas_mem s1 h = expected /\
        s2 = mkCASRegTSO (mem_write (cas_mem s1) h desired)
                          (CASRegTSOSpec.view_advance_all h)) \/
    (ret = false /\
      exists h,
        (forall t0, Pos.lt (cas_view s1 t0) h) /\
        cas_mem s1 h <> expected /\
        s2 = mkCASRegTSO (cas_mem s1)
                          (CASRegTSOSpec.view_advance_all h)).
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

  Lemma mem_malloc_inv_push t v :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_mem malloc) |}
      (I //\\ ALin t (Semantics.ls_inv (push v)))
      (I //\\ ALin t (Semantics.ls_inv (push v))).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst.
    dependent destruction Hstep.
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - exact Hpre.
    - unfold G. split.
      + destruct Hpre as [[stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]] Hlin].
        exists stk. exists (top : option Addr). repeat split; auto.
      + split.
        * unfold written_heap_preserved. intros; split; auto.
        * split.
          -- unfold owned_preserved_for. intros; split; auto.
          -- intros; auto.
  Qed.

  Lemma malloc_res_step_inv t ret
      (s1 s2 : OwnedMemState ((A * option Addr)%type)) :
    StepMemTSO {| te_tid := t; te_ev := ResEv malloc ret |} s1 s2 ->
    exists init h,
      (forall t0, Pos.lt (om_view s1 t0) h) /\
      om_heap s1 ret = None /\
      om_heap s2 = heap_update ret init (om_heap s1) /\
      om_loc s2 = heap_update ret (LAlloc t) (om_loc s1) /\
      om_view s2 = view_advance_all h.
  Proof.
    intros Hstep.
    remember {| te_tid := t; te_ev := ResEv malloc ret |} as ev eqn:Hev.
    revert t ret Hev.
    induction Hstep; intros tidx retx Hev; inversion Hev; subst; try discriminate.
    pose proof (f_equal malloc_response Hev) as Hret.
    unfold malloc_response in Hret; simpl in Hret; inversion Hret; subst.
    eexists; eexists; repeat split; eauto.
  Qed.

  Lemma malloc_res_astep_inv t ret
      (s1 s2 : OwnedMemState ((A * option Addr)%type)) :
    AStep StepMemTSO {| te_tid := t; te_ev := ResEv malloc ret |}
      (Pending s1 t malloc) (Idle s2) ->
    exists init h,
      (forall t0, Pos.lt (om_view s1 t0) h) /\
      om_heap s1 ret = None /\
      om_heap s2 = heap_update ret init (om_heap s1) /\
      om_loc s2 = heap_update ret (LAlloc t) (om_loc s1) /\
      om_view s2 = view_advance_all h.
  Proof.
    intros Hstep.
    dependent destruction Hstep.
    eapply malloc_res_step_inv; eauto.
  Qed.

  Lemma mem_malloc_res_push t v newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_mem malloc) newLoc |}
      (I //\\ ALin t (Semantics.ls_inv (push v)))
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst; clear Hmem.
    apply malloc_res_step_inv in Hstep as
      [init [h [Hfresh [HfreshLoc [HheapUpd [HlocUpd HviewUpd]]]]]].
    dependent destruction H2.
    destruct Hpre as [[stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]] Hlin].
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split.
      + split.
        * exists stk. exists (top : option Addr). split; [exact Hr|].
          split; [exact HTop|].
          split.
          -- unfold mem_state, loc_state. simpl.
             rewrite HheapUpd, HlocUpd.
             eapply listseg_loc_update_alloc; eauto.
          -- split; [auto|].
             unfold loc_defined, mem_state, loc_state in *; simpl in *.
             intros l st Hloc.
             rewrite HlocUpd in Hloc.
             rewrite HheapUpd.
             unfold heap_update in *.
             destruct (Nat.eqb newLoc l) eqn:Heq.
             ++ exists init. reflexivity.
             ++ destruct (Hdef l st Hloc) as [p Hp].
                exists p. exact Hp.
        * exact Hlin.
      + unfold HOwned, mem_state, loc_state; simpl.
        exists init. split.
        * rewrite HheapUpd. apply HeapUpdateSelf.
        * rewrite HlocUpd. apply HeapUpdateSelf.
    - unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
      split.
      + exists stk. exists (top : option Addr). split; [exact Hr|].
        split; [exact HTop|].
        split.
        * unfold mem_state, loc_state. simpl.
          rewrite HheapUpd, HlocUpd.
          eapply listseg_loc_update_alloc; eauto.
        * split; [auto|].
          unfold loc_defined, mem_state, loc_state in *; simpl in *.
          intros l st Hloc.
          rewrite HlocUpd in Hloc.
          rewrite HheapUpd.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l) eqn:Heq.
          -- exists init. reflexivity.
          -- destruct (Hdef l st Hloc) as [p Hp].
             exists p. exact Hp.
      + split.
        * intros l0 p HlocW Hmem0.
          unfold loc_state, mem_state; simpl.
          rewrite HlocUpd, HheapUpd.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l0) eqn:Heq.
          -- apply Nat.eqb_eq in Heq. subst.
             specialize (Hdef l0 LWritten HlocW) as [pold Hpold].
             unfold mem_state in Hpold; simpl in Hpold.
             rewrite HfreshLoc in Hpold. discriminate.
          -- split; auto.
        * split.
          -- intros t' Hneq l0 p HlocO Hmem0.
             unfold loc_state, mem_state; simpl.
             rewrite HlocUpd, HheapUpd.
             unfold heap_update in *.
             destruct (Nat.eqb newLoc l0) eqn:Heq.
             ++ apply Nat.eqb_eq in Heq. subst.
                specialize (Hdef l0 (LAlloc t') HlocO) as [pold Hpold].
                unfold mem_state in Hpold; simpl in Hpold.
                rewrite HfreshLoc in Hpold. discriminate.
             ++ split; auto.
          -- intros; auto.
  Qed.

  Lemma mem_mwrite_inv_push t v oldPtr newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_mem (mwrite newLoc (v, oldPtr))) |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc)
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst.
    dependent destruction Hstep.
    destruct Hpre as [HIA HOwned0].
    destruct HIA as [HI Hlin].
    destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
    destruct HOwned0 as [p [Hheap Hloc]].
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split.
      + split.
        * exists stk, top. repeat split; auto.
        * exact Hlin.
      + exists p. split; auto.
    - unfold G, written_heap_preserved, owned_preserved_for, I.
      split.
      + exists stk, top. repeat split; auto.
      + split.
        * intros; split; auto.
        * split.
          -- intros; split; auto.
          -- intros; auto.
  Qed.

  Lemma mwrite_res_step_inv t l v
      (s1 s2 : OwnedMemState ((A * option Addr)%type)) :
    StepMemTSO {| te_tid := t; te_ev := ResEv (mwrite l v) tt |} s1 s2 ->
    exists h,
      (forall t0, Pos.lt (om_view s1 t0) h) /\
      om_loc s1 l = Some (LAlloc t) /\
      om_heap s2 = heap_update l v (om_heap s1) /\
      om_loc s2 = heap_update l LWritten (om_loc s1) /\
      om_view s2 = view_advance_all h.
  Proof.
    intros Hstep.
    dependent destruction Hstep.
    eexists; repeat split; eauto.
  Qed.

  Lemma mem_mwrite_res_push t v oldPtr newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_mem (mwrite newLoc (v, oldPtr))) tt |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc)
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr)).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst; clear Hmem.
    dependent destruction H2.
    apply mwrite_res_step_inv in Hstep as
      [h [Hfresh [HownLoc [HheapUpd [HlocUpd HviewUpd]]]]].
    destruct Hpre as [HIA HOwned0].
    destruct HIA as [HI Hlin].
    destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
    destruct HOwned0 as [p [Hheap Hloc]].
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split.
      + split.
        * exists stk, top. split; [exact Hr|].
          split; [exact HTop|].
          split.
          -- unfold mem_state, loc_state. simpl.
             rewrite HheapUpd, HlocUpd.
             eapply listseg_loc_update_unlinked; eauto.
          -- split.
             ++ exact Logic.I.
             ++ unfold loc_defined, mem_state, loc_state in *; simpl in *.
                intros l0 st Hloc'.
                rewrite HlocUpd in Hloc'.
                rewrite HheapUpd.
                unfold heap_update in *.
                destruct (Nat.eqb newLoc l0) eqn:Heq.
                ** exists (v, oldPtr). reflexivity.
                ** destruct (Hdef l0 st Hloc') as [p' Hp].
                   exists p'. exact Hp.
        * exact Hlin.
      + unfold HCell, mem_state, loc_state; simpl.
        split.
        * rewrite HheapUpd. apply HeapUpdateSelf.
        * rewrite HlocUpd. apply HeapUpdateSelf.
    - unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
      split.
      + exists stk, top. split; [exact Hr|].
        split; [exact HTop|].
        split.
        * unfold mem_state, loc_state. simpl.
          rewrite HheapUpd, HlocUpd.
          eapply listseg_loc_update_unlinked; eauto.
        * split.
          -- exact Logic.I.
          -- unfold loc_defined, mem_state, loc_state in *; simpl in *.
             intros l0 st Hloc'.
             rewrite HlocUpd in Hloc'.
             rewrite HheapUpd.
             unfold heap_update in *.
             destruct (Nat.eqb newLoc l0) eqn:Heq.
             ++ exists (v, oldPtr). reflexivity.
             ++ destruct (Hdef l0 st Hloc') as [p' Hp].
                exists p'. exact Hp.
      + split.
        * intros l1 p' HlocW Hmem0.
          unfold loc_state, mem_state; simpl.
          rewrite HlocUpd, HheapUpd.
          unfold heap_update in *.
          destruct (Nat.eqb newLoc l1) eqn:Heq.
          -- apply Nat.eqb_eq in Heq. subst.
             unfold loc_state in HlocW; simpl in HlocW.
             rewrite HownLoc in HlocW. discriminate.
          -- split; auto.
        * split.
          -- intros t' Hneq l1 p' HlocO Hmem0.
             unfold loc_state, mem_state; simpl.
             rewrite HlocUpd, HheapUpd.
             unfold heap_update in *.
             destruct (Nat.eqb newLoc l1) eqn:Heq.
             ++ apply Nat.eqb_eq in Heq. subst.
                unfold loc_state in HlocO; simpl in HlocO.
                rewrite HownLoc in HlocO. inversion HlocO; subst. tauto.
             ++ split; auto.
          -- intros; auto.
  Qed.

  Lemma cas_push_inv t v oldPtr newLoc :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_cas (cas oldPtr (Some newLoc))) |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr))
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr)).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hcas Hmem]; subst.
    inversion Hcas; subst.
    dependent destruction Hstep.
    destruct Hpre as [HIA Hcell].
    destruct HIA as [HI Hlin].
    destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split.
      + split.
        * exists stk, top. repeat split; auto.
        * exact Hlin.
      + exact Hcell.
    - unfold G, written_heap_preserved, owned_preserved_for, I.
      split.
      + exists stk, top. repeat split; auto.
      + split.
        * intros; split; auto.
        * split.
          -- intros; split; auto.
          -- intros; auto.
  Qed.

  Lemma cas_push_res t v oldPtr newLoc succ :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas (cas oldPtr (Some newLoc))) succ |}
      (I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr))
      (I //\\
        match succ with
        | true => ALin t (Semantics.ls_linr (push v) (OK tt))
        | false => ALin t (Semantics.ls_linr (push v) FAIL)
        end).
  Proof.
    destruct succ.
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; clear Hcas.
      dependent destruction H2.
      destruct Hpre as [HIA Hcell].
      destruct HIA as [HI Hlin].
      destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
      destruct Hcell as [HnewHeap HnewLoc].
      destruct (step_cas_res_inv t oldPtr (Some newLoc) true _ _ Hstep)
        as [[_ [h [Hfresh [HmemAt HcasUpd]]]] | [[=] _]].
      assert (Htop_eq : top = oldPtr).
      { transitivity (cas_mem s1 h).
        - symmetry. eapply Tail_fresh_value; eauto.
        - exact HmemAt. }
      assert (HTopNew : TSOState (Some newLoc) s2).
      { subst s2. apply Tail_write_new. }
      subst top. simpl in Hr. subst ρ0.
      exists (Idle (v :: stk)),
        (TMap.add t (Semantics.ls_linr (push v) (OK tt))
          (TMap.add t (Semantics.ls_lini (push v)) π0)).
      split.
      + eapply rt_trans.
        * eapply rt_step. eapply Semantics.ps_inv.
          -- constructor. constructor.
          -- exact Hlin.
        * eapply rt_step. eapply Semantics.ps_ret.
          -- constructor. econstructor. reflexivity.
          -- rewrite PositiveMap.gss. auto.
      + split.
        * unfold I, ALin; simpl.
          split.
          -- exists (v :: stk), (Some newLoc). split; [reflexivity|].
             split; [exact HTopNew|].
             split.
             ++ econstructor; eauto.
             ++ split; auto.
          -- cbn. rewrite PositiveMap.gss. auto.
        * unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
          split.
          -- exists (v :: stk), (Some newLoc). split; [reflexivity|].
             split; [exact HTopNew|].
             split.
             ++ econstructor; eauto.
             ++ split; auto.
          -- split.
             ++ intros l0 p HlocW Hmem0. split; auto.
             ++ split.
                ** intros t' Hneq l0 p HlocO Hmem0. split; auto.
                ** intros t' Hneq.
                   do 2 (rewrite PositiveMap.gso by congruence).
                   reflexivity.
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; clear Hcas.
      dependent destruction H2.
      destruct Hpre as [HIA Hcell].
      destruct HIA as [HI Hlin].
      destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
      destruct (step_cas_res_inv t oldPtr (Some newLoc) false _ _ Hstep)
        as [[[=] _] | [_ [h [Hfresh [HneqMem HcasUpd]]]]].
      assert (HTop' : TSOState top s2).
      { subst s2. eapply Tail_advance_all_pres; eauto. }
      simpl in Hr. subst ρ0.
      exists (Idle stk),
        (TMap.add t (Semantics.ls_linr (push v) FAIL)
          (TMap.add t (Semantics.ls_lini (push v)) π0)).
      split.
      + eapply rt_trans.
        * eapply rt_step. eapply Semantics.ps_inv.
          -- constructor. constructor.
          -- exact Hlin.
        * eapply rt_step. eapply Semantics.ps_ret.
          -- constructor. eapply step_push_fail. reflexivity.
          -- rewrite PositiveMap.gss. auto.
      + split.
        * unfold I, ALin; simpl.
          split.
          -- exists stk, top. repeat split; auto.
          -- cbn. rewrite PositiveMap.gss. auto.
        * unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
          split.
          -- exists stk, top. repeat split; auto.
          -- split.
             ++ intros l0 p HlocW Hmem0. split; auto.
             ++ split.
                ** intros t' Hneq l0 p HlocO Hmem0. split; auto.
                ** intros t' Hneq.
                   do 2 (rewrite PositiveMap.gso by congruence).
                   reflexivity.
  Qed.

  Lemma cas_get_res_pop t ret :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas get) ret |}
      (I //\\ ALin t (Semantics.ls_inv pop))
      (match ret with
       | None => I //\\ ALin t (Semantics.ls_linr pop (OK None))
       | Some oldLoc => (I //\\ ALin t (Semantics.ls_inv pop)) //\\ HWritten oldLoc
       end).
  Proof.
    destruct ret as [oldLoc|].
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; clear Hcas.
      dependent destruction H2.
      destruct Hpre as [HI Hlin].
      destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
      pose proof (step_get_tail_inv t (Some oldLoc) _ _ top HTop Hstep) as [HretTop HTop'].
      inversion HretTop; subst top.
      exists ρ0, π0. split; [apply rt_refl|].
      split.
      + unfold I, HWritten, HCell; simpl.
        split.
        * split.
          -- exists stk, (Some oldLoc). repeat split; auto.
          -- exact Hlin.
        * 
          apply listseg_loc_defined in Hls as [hv [nxt [vs [Hstk [Hheap [Hloc Htail]]]]]].
          exists (pair hv nxt). split; auto.
      + unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
        split.
        * exists stk, (Some oldLoc). repeat split; auto.
        * split.
          -- intros l0 p HlocW Hmem0. split; auto.
          -- split.
             ++ intros t' Hneq l0 p HlocO Hmem0. split; auto.
             ++ intros; auto.
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; clear Hcas.
      dependent destruction H2.
      destruct Hpre as [HI Hlin].
      destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
      pose proof (step_get_tail_inv t None _ _ top HTop Hstep) as [HretTop HTop'].
      inversion HretTop; subst top.
      apply listseg_loc_none in Hls. subst stk.
      simpl in Hr. subst ρ0.
      exists (Idle nil),
        (TMap.add t (Semantics.ls_linr pop (OK None))
          (TMap.add t (Semantics.ls_lini pop) π0)).
      split.
      + eapply rt_trans.
        * eapply rt_step. eapply Semantics.ps_inv.
          -- constructor. apply step_pop_inv.
          -- exact Hlin.
        * eapply rt_step. eapply Semantics.ps_ret.
          -- constructor. eapply step_pop_emp. reflexivity.
          -- rewrite PositiveMap.gss. auto.
      + split.
        * unfold I, ALin; simpl.
          split.
          -- exists nil, None. repeat split; auto. constructor.
          -- cbn. rewrite PositiveMap.gss. auto.
        * unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
          split.
          -- exists nil, None. repeat split; auto. constructor.
          -- split.
             ++ intros l0 p HlocW Hmem0. split; auto.
             ++ split.
                ** intros t' Hneq l0 p HlocO Hmem0. split; auto.
                ** intros t' Hneq.
                   do 2 (rewrite PositiveMap.gso by congruence).
                   reflexivity.
  Qed.

  Lemma mem_mread_inv_pop t oldLoc :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_mem (mread oldLoc)) |}
      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc)
      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst.
    dependent destruction Hstep.
    destruct Hpre as [HIA Hwritten].
    destruct HIA as [HI Hlin].
    destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split; [split|].
      + exists stk, top. repeat split; auto.
      + exact Hlin.
      + exact Hwritten.
    - unfold G, written_heap_preserved, owned_preserved_for, I.
      split.
      + exists stk, top. repeat split; auto.
      + split.
        * intros; split; auto.
        * split.
          -- intros; split; auto.
          -- intros; auto.
  Qed.

  Lemma mread_res_step_inv t l v
      (s1 s2 : OwnedMemState ((A * option Addr)%type)) :
    StepMemTSO {| te_tid := t; te_ev := ResEv (mread l) v |} s1 s2 ->
    exists h,
      (forall t0, Pos.lt (om_view s1 t0) h) /\
      om_heap s1 l = Some v /\
      om_loc s1 l = Some LWritten /\
      om_heap s2 = om_heap s1 /\
      om_loc s2 = om_loc s1 /\
      om_view s2 = upd_tid_time (om_view s1) t h.
  Proof.
    intros Hstep.
    dependent destruction Hstep.
    eexists; repeat split; eauto.
  Qed.

  Lemma mem_mread_res_pop t oldLoc head :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_mem (mread oldLoc)) head |}
      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HWritten oldLoc)
      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc head).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hmem Hcas]; subst.
    inversion Hmem; subst; clear Hmem.
    dependent destruction H2.
    apply mread_res_step_inv in Hstep as
      [h [Hfresh [HheapRead [HlocRead [HheapUpd [HlocUpd HviewUpd]]]]]].
    destruct Hpre as [HIA Hwritten].
    destruct HIA as [HI Hlin].
    destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split.
      + split.
        * exists stk, top. split; [exact Hr|].
          split; [exact HTop|].
          split.
          -- unfold mem_state, loc_state in *; simpl in *.
             rewrite HheapUpd, HlocUpd. exact Hls.
          -- split.
             ++ exact Hpend.
             ++ unfold loc_defined, mem_state, loc_state in *; simpl in *.
                rewrite HheapUpd, HlocUpd. exact Hdef.
        * exact Hlin.
      + unfold HCell, mem_state, loc_state; simpl.
        rewrite HheapUpd, HlocUpd. split; auto.
    - unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
      split.
      + exists stk, top. split; [exact Hr|].
        split; [exact HTop|].
        split.
        * unfold mem_state, loc_state in *; simpl in *.
          rewrite HheapUpd, HlocUpd. exact Hls.
        * split; auto.
          unfold loc_defined, mem_state, loc_state in *; simpl in *.
          rewrite HheapUpd, HlocUpd. exact Hdef.
      + split.
        * intros l0 p HlocW Hmem0.
          unfold loc_state, mem_state; simpl. rewrite HheapUpd, HlocUpd. split; auto.
        * split.
          -- intros t' Hneq l0 p HlocO Hmem0.
             unfold loc_state, mem_state; simpl. rewrite HheapUpd, HlocUpd. split; auto.
          -- intros; auto.
  Qed.

  Lemma cas_pop_inv t oldLoc head :
    PUpdate (G t) {| te_tid := t; te_ev := InvEv (in_cas (cas (Some oldLoc) (snd head))) |}
      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc head)
      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc head).
  Proof.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
    destruct Hstep as [Hcas Hmem]; subst.
    inversion Hcas; subst.
    dependent destruction Hstep.
    destruct Hpre as [HIA Hcell].
    destruct HIA as [HI Hlin].
    destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
    exists ρ0, π0. split; [apply rt_refl|].
    split.
    - split.
      + split.
        * exists stk, top. repeat split; auto.
        * exact Hlin.
      + exact Hcell.
    - unfold G, written_heap_preserved, owned_preserved_for, I.
      split.
      + exists stk, top. repeat split; auto.
      + split.
        * intros; split; auto.
        * split.
          -- intros; split; auto.
          -- intros; auto.
  Qed.

  Lemma cas_pop_res t oldLoc v nxt succ :
    PUpdate (G t) {| te_tid := t; te_ev := ResEv (in_cas (cas (Some oldLoc) nxt)) succ |}
      (I //\\ ALin t (Semantics.ls_inv pop) //\\ HCell oldLoc (v, nxt))
      (I //\\
        match succ with
        | true => ALin t (Semantics.ls_linr pop (OK (Some v)))
        | false => ALin t (Semantics.ls_linr pop FAIL)
        end).
  Proof.
    destruct succ.
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; clear Hcas.
      dependent destruction H2.
      destruct Hpre as [HIA Hcell].
      destruct HIA as [HI Hlin].
      destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
      destruct Hcell as [HcellHeap HcellLoc].
      destruct (step_cas_res_inv t (Some oldLoc) nxt true _ _ Hstep)
        as [[_ [h [Hfresh [HmemAt HcasUpd]]]] | [[=] _]].
      assert (Htop_eq : top = Some oldLoc).
      { transitivity (cas_mem s1 h).
        - symmetry. eapply Tail_fresh_value; eauto.
        - exact HmemAt. }
      assert (HTopNew : TSOState nxt s2).
      { subst s2. apply Tail_write_new. }
      subst top.
      apply listseg_loc_defined in Hls as [v' [nxt' [vs [Hstk [Hheap [Hloc Htail]]]]]].
      rewrite HcellHeap in Hheap. inversion Hheap; subst v' nxt'. clear Hheap.
      subst stk. simpl in Hr. subst ρ0.
      exists (Idle vs),
        (TMap.add t (Semantics.ls_linr pop (OK (Some v)))
          (TMap.add t (Semantics.ls_lini pop) π0)).
      split.
      + eapply rt_trans.
        * eapply rt_step. eapply Semantics.ps_inv.
          -- constructor. apply step_pop_inv.
          -- exact Hlin.
        * eapply rt_step. eapply Semantics.ps_ret.
          -- constructor. eapply step_pop_ok. reflexivity.
          -- rewrite PositiveMap.gss. auto.
      + split.
        * unfold I, ALin; simpl.
          split.
          -- exists vs, nxt. repeat split; auto.
          -- cbn. rewrite PositiveMap.gss. auto.
        * unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
          split.
          -- exists vs, nxt. repeat split; auto.
          -- split.
             ++ intros l0 p HlocW Hmem0. split; auto.
             ++ split.
                ** intros t' Hneq l0 p HlocO Hmem0. split; auto.
                ** intros t' Hneq.
                   do 2 (rewrite PositiveMap.gso by congruence).
                   reflexivity.
    - unfold PUpdate.
      intros σ0 ρ0 π0 Hpre σ' Hstep.
      destruct σ0 as [cas0 mem0], σ' as [cas' mem']; simpl in *.
      destruct Hstep as [Hcas Hmem]; subst.
      inversion Hcas; subst; clear Hcas.
      dependent destruction H2.
      destruct Hpre as [HIA Hcell].
      destruct HIA as [HI Hlin].
      destruct HI as [stk [top [Hr [HTop [Hls [Hpend Hdef]]]]]].
      destruct (step_cas_res_inv t (Some oldLoc) nxt false _ _ Hstep)
        as [[[=] _] | [_ [h [Hfresh [HneqMem HcasUpd]]]]].
      assert (HTop' : TSOState top s2).
      { subst s2. eapply Tail_advance_all_pres; eauto. }
      simpl in Hr. subst ρ0.
      exists (Idle stk),
        (TMap.add t (Semantics.ls_linr pop FAIL)
          (TMap.add t (Semantics.ls_lini pop) π0)).
      split.
      + eapply rt_trans.
        * eapply rt_step. eapply Semantics.ps_inv.
          -- constructor. apply step_pop_inv.
          -- exact Hlin.
        * eapply rt_step. eapply Semantics.ps_ret.
          -- constructor. eapply step_pop_fail. reflexivity.
          -- rewrite PositiveMap.gss. auto.
      + split.
        * unfold I, ALin; simpl.
          split.
          -- exists stk, top. repeat split; auto.
          -- cbn. rewrite PositiveMap.gss. auto.
        * unfold G, written_heap_preserved, owned_preserved_for, I; simpl.
          split.
          -- exists stk, top. repeat split; auto.
          -- split.
             ++ intros l0 p HlocW Hmem0. split; auto.
             ++ split.
                ** intros t' Hneq l0 p HlocO Hmem0. split; auto.
                ** intros t' Hneq.
                   do 2 (rewrite PositiveMap.gso by congruence).
                   reflexivity.
  Qed.

  Program Definition Mtrystack : layer_implementation E F := {|
    li_impl m tid0 :=
      match m with
      | push v => push_impl v tid0
      | pop => pop_impl tid0
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    {
      constructor.
      unfold R. intros s s' [_ [_ Hpi]] _.
      rewrite Hpi. tauto.
    }
    {
      unfold G, R, written_heap_preserved, owned_preserved_for.
      intros t1 t2 Hneq s1 s2 Hrel.
      destruct Hrel as [HG | Hmeta].
      - destruct HG as [_ [Hwritten [Howned Hpi]]].
        split; [exact Hwritten|].
        split; [apply Howned; auto|apply Hpi; auto].
      - unfold GINV, Ginv, GRET, Gret, GId, LiftRelation_π in Hmeta.
        destruct Hmeta as [[Hinv | Hret] | Hid].
        + destruct Hinv as [f [Hσ [Hρ [Hfind Hπ]]]].
          split.
          * intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
          * split.
            -- intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
            -- rewrite Hπ. rewrite PositiveMap.gso; auto.
        + destruct Hret as [f [ret [Hσ [Hρ [Hfind Hπ]]]]].
          split.
          * intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
          * split.
            -- intros l v Hloc Hmem. rewrite <- Hσ. split; auto.
            -- rewrite Hπ. rewrite PositiveMap.gro; auto.
        + subst. repeat split; intros; auto.
    }
    intros t f. destruct f.
    (* push *)
    {
      exists (I //\\ ALin t (Semantics.ls_inv (push v))).
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr (push v) ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold push_impl.
      eapply provable_vis_safe with
        (P' := I //\\ ALin t (Semantics.ls_inv (push v)))
        (Q' := fun oldPtr => I //\\ ALin t (Semantics.ls_inv (push v)));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
      try apply cas_get_no_error;
      try solve_no_error;
      try apply cas_get_inv_pres;
      try apply cas_get_res_push.
      intros oldPtr.
      eapply provable_vis_safe with
        (P' := I //\\ ALin t (Semantics.ls_inv (push v)))
        (Q' := fun newLoc => I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc);
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
      try apply malloc_no_error;
      try solve_no_error;
      try apply mem_malloc_inv_push;
      try apply mem_malloc_res_push.
      intros newLoc.
      eapply provable_vis_safe with
        (P' := I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HOwned t newLoc)
        (Q' := fun _ => I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr));
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
      try apply mem_mwrite_inv_push;
      try apply mem_mwrite_res_push.
      - eapply ImplTrans; [|apply mwrite_owned_no_error].
        unfold Imply. intros s [[HI _] Hown]. split; auto.
      - intros [].
        apply mem_mwrite_res_push.
      - intros [].
        eapply provable_vis_safe with
          (P' := I //\\ ALin t (Semantics.ls_inv (push v)) //\\ HCell newLoc (v, oldPtr))
          (Q' := fun succ =>
            I //\\ match succ with
                   | true => ALin t (Semantics.ls_linr (push v) (OK tt))
                   | false => ALin t (Semantics.ls_linr (push v) FAIL)
                   end);
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
        try apply cas_cas_no_error;
        try solve_no_error;
        try apply cas_push_inv;
        try apply cas_push_res.
        intros succ.
        eapply provable_ret_safe; destruct succ;
        try solve_conj_impl;
        try solve_conj_stable stableDB;
        try apply ImplRefl.
    }
    (* pop *)
    {
      exists (I //\\ ALin t (Semantics.ls_inv pop)).
      exists (fun ret => I //\\ ALin t (Semantics.ls_linr pop ret)).
      constructor;
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try apply IGinv; try apply IGret.
      {
        unfold ALin. intros.
        destruct H; auto.
      }
      simpl. unfold pop_impl.
      eapply provable_vis_safe with
        (P' := I //\\ ALin t (Semantics.ls_inv pop))
        (Q' := fun oldPtr =>
          match oldPtr with
          | None => I //\\ ALin t (Semantics.ls_linr pop (OK None))
          | Some oldLoc => (I //\\ ALin t (Semantics.ls_inv pop)) //\\ HWritten oldLoc
          end);
      try solve_conj_impl;
      try solve_conj_stable stableDB;
      try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
	      try apply cas_get_no_error;
	      try solve_no_error;
	      try apply cas_get_inv_pres;
	      try apply cas_get_res_pop.
	      - intro oldPtr; destruct oldPtr; solve_conj_impl.
	      - intros oldPtr. destruct oldPtr as [oldLoc|].
	        + eapply provable_vis_safe with
	          (P' := (I //\\ ALin t (Semantics.ls_inv pop)) //\\ HWritten oldLoc)
	          (Q' := fun head : (A * option Addr)%type =>
	            (I //\\ ALin t (Semantics.ls_inv pop)) //\\ HCell oldLoc head);
	        try solve_conj_impl;
	        try solve_conj_stable stableDB;
        try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
        try apply mem_mread_inv_pop;
        try apply mem_mread_res_pop.
	        * eapply ImplTrans; [|apply mread_written_no_error].
	          solve_conj_impl.
	        * intro head.
	          destruct head as [pv nxt].
          eapply provable_vis_safe with
            (P' := (I //\\ ALin t (Semantics.ls_inv pop)) //\\ HCell oldLoc (pv, nxt))
            (Q' := fun succ =>
              I //\\ match succ with
                     | true => ALin t (Semantics.ls_linr pop (OK (Some pv)))
                     | false => ALin t (Semantics.ls_linr pop FAIL)
                     end);
          try solve_conj_impl;
          try solve_conj_stable stableDB;
          try (let ret := fresh "ret" in intro ret; destruct ret; solve_conj_stable stableDB);
          try apply cas_cas_no_error;
          try solve_no_error;
          try apply cas_pop_inv;
          try apply cas_pop_res.
          intros succ.
          eapply provable_ret_safe; destruct succ;
          try solve_conj_impl;
          try solve_conj_stable stableDB;
          try apply ImplRefl.
	        + eapply provable_ret_safe;
	          try solve_conj_impl;
	          try solve_conj_stable stableDB;
	          try apply ImplRefl.
    }
    (* initial *)
    {
      unfold I, TopIs, TSOState, Tail, loc_defined, pending_write_owned.
      simpl.
      exists nil, None. split; [reflexivity|].
      split.
      - exists xH. split.
        + intros ?. lia.
        + intros ?. reflexivity.
      - split; [constructor|].
        split; [auto|].
        intros l st Hloc. discriminate.
    }
  Defined.

End TryStackTSOImplF.

Module TryStackTSOImplParam <: TypeParam.
  Parameter A : Type.
End TryStackTSOImplParam.

Module TryStackTSOImpl := TryStackTSOImplF(TryStackTSOImplParam).
