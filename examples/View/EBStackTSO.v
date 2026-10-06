(** Ported from CSL-Lin [examples/EBStackTSO.v] (hyleIndex/CSL-Lin, master 3f7baaa).
    View-based (timestamped) specification / proof, kept as close to the
    original as possible; changes are limited to the Rocq 9.2 / rbgs
    adaptation listed in [examples/View/README.md]. *)

Require Import Stdlib.FSets.FMapPositive.
Require Import Stdlib.Relations.Relation_Operators Stdlib.Relations.Operators_Properties.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.Logic.Eqdep.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Arith.PeanoNat.

Require Import coqrel.LogicalRelations.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import Lang.
Require Import Semantics.
Require Import examples.View.LegacyNotations.
Require Import Assertion.
Require Import TPSimulation.
Require Import RGISimulation.
Require Import RGILogic.
Require Import examples.Common.AtomicLTS.
Require Import examples.View.ViewSpecs.
Require Import examples.Exchanger.ExchangerSpec.
Require Import examples.View.TryStackTSO.
Require Import examples.View.ExchangerTSO.

Module EBStackTSOImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import LegacyAssertionNotations.
  Import RGISimulation.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS TryStackSpec ExchSpec StackSpec.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Import (canonicals) Sig.Plus.

  Open Scope prog_scope.

  #[local] Parameter A : Type.
  Definition Elem : Type := A.

  Module TSParam <: TryStackTSO.TypeParam.
    Definition A : Type := Elem.
  End TSParam.
  Module TS := TryStackTSOImplF(TSParam).

  Module EXParam <: ExchangerTSO.TypeParam.
    Definition A : Type := option Elem.
  End EXParam.
  Module EX := ExchangerImplF(EXParam).

  (* Projection target for reusing the existing component proofs.  This is
     the ordinary simlin tensor LTS, not a separate EBStack-specific model. *)
  Definition Etensor : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (li_sig TS.E) (li_sig EX.E);
    li_lts := tens_lts (li_lts TS.E) (li_lts EX.E);
    li_init := (li_init TS.E, li_init EX.E);
  |}.

  Definition Fmid : layer_interface :=
  {|
    li_sig := Sig.Plus.omap (ETryStack A) (EExch (option A));
    li_lts := tens_lts VTryStack VExch;
    li_init := (Idle nil, ExSIdle);
  |}.

  Definition F : layer_interface :=
  {|
    li_sig := EStack A;
    li_lts := VStack;
    li_init := Idle nil;
  |}.

  Inductive GlobalLoc : Type :=
  | L_stack_top
  | L_stack_mem
  | L_exchanger_offer.

  Scheme Equality for GlobalLoc.

  Definition combo_view_update
    (v : tid -> GlobalLoc -> positive) (l : GlobalLoc)
    (v' : tid -> positive) : tid -> GlobalLoc -> positive :=
    fun t l' => if GlobalLoc_eq_dec l' l then v' t else v t l'.

  Definition combo_view_update_all
    (v' : tid -> positive) : tid -> GlobalLoc -> positive :=
    fun t _ => v' t.

  Definition combo_view_update_tid_all
    (v : tid -> GlobalLoc -> positive) (t : tid) (h : positive) :
    tid -> GlobalLoc -> positive :=
    fun t' l => if Pos.eqb t t' then h else v t' l.

  Definition combo_view_at
    (v : tid -> GlobalLoc -> positive) (l : GlobalLoc) : tid -> positive :=
    fun t => v t l.

  Definition combo_view_fresh
    (v : tid -> GlobalLoc -> positive) (h : positive) : Prop :=
    forall t l, Pos.lt (v t l) h.

  Definition stack_top_lts :=
    CASRegTSOSpec.VCASRegTSO (A:=option HeapSpec.Addr).
  Definition stack_mem_lts :=
    OwnedMemTSOSpec.VMemTSO (A:=TS.A * option HeapSpec.Addr).
  Definition exchanger_lts :=
    CASRegTSOSpec.VCASRegTSO (A:=EX.Offer).

  Record ComboTSOState : Type := {
    stack_top_hist : positive -> option HeapSpec.Addr;
    stack_top_phase : State stack_top_lts;
    stack_heap : HeapSpec.Heap (TS.A * option HeapSpec.Addr);
    stack_mem_phase : State stack_mem_lts;
    exch_hist : positive -> EX.Offer;
    exch_phase : State exchanger_lts;
    combo_view : tid -> GlobalLoc -> positive;
    loc_status : HeapSpec.Heap OwnedMemTSOSpec.LocStat;
  }.

  Definition combo_stack_top_raw (s : ComboTSOState) :
    CASRegTSOSpec.SCASRegTSO (option HeapSpec.Addr) :=
    CASRegTSOSpec.mkCASRegTSO
      (stack_top_hist s)
      (combo_view_at (combo_view s) L_stack_top).

  Definition combo_stack_top_raw_with_view
    (s : ComboTSOState) (v : tid -> positive) :
    CASRegTSOSpec.SCASRegTSO (option HeapSpec.Addr) :=
    CASRegTSOSpec.mkCASRegTSO (stack_top_hist s) v.

  Definition combo_stack_top_state_with_view
    (s : ComboTSOState) (v : tid -> positive) : State stack_top_lts :=
    match stack_top_phase s with
    | Idle _ => Idle (combo_stack_top_raw_with_view s v)
    | Pending _ t op => Pending (combo_stack_top_raw_with_view s v) t op
    end.

  Definition combo_stack_top_state (s : ComboTSOState) : State stack_top_lts :=
    combo_stack_top_state_with_view s (combo_view_at (combo_view s) L_stack_top).

  Definition combo_owned_mem_raw (s : ComboTSOState) :
    OwnedMemTSOSpec.OwnedMemState (TS.A * option HeapSpec.Addr) :=
    OwnedMemTSOSpec.mkOwnedMemTSO
      (stack_heap s)
      (loc_status s)
      (combo_view_at (combo_view s) L_stack_mem).

  Definition combo_owned_mem_raw_with_view
    (s : ComboTSOState) (v : tid -> positive) :
    OwnedMemTSOSpec.OwnedMemState (TS.A * option HeapSpec.Addr) :=
    OwnedMemTSOSpec.mkOwnedMemTSO (stack_heap s) (loc_status s) v.

  Definition combo_stack_mem_state_with_view
    (s : ComboTSOState) (v : tid -> positive) : State stack_mem_lts :=
    match stack_mem_phase s with
    | Idle _ => Idle (combo_owned_mem_raw_with_view s v)
    | Pending _ t op => Pending (combo_owned_mem_raw_with_view s v) t op
    end.

  Definition combo_stack_mem_state (s : ComboTSOState) : State stack_mem_lts :=
    combo_stack_mem_state_with_view s (combo_view_at (combo_view s) L_stack_mem).

  Definition combo_exchanger_raw (s : ComboTSOState) :
    CASRegTSOSpec.SCASRegTSO EX.Offer :=
    CASRegTSOSpec.mkCASRegTSO
      (exch_hist s)
      (combo_view_at (combo_view s) L_exchanger_offer).

  Definition combo_exchanger_raw_with_view
    (s : ComboTSOState) (v : tid -> positive) :
    CASRegTSOSpec.SCASRegTSO EX.Offer :=
    CASRegTSOSpec.mkCASRegTSO (exch_hist s) v.

  Definition combo_exchanger_state_with_view
    (s : ComboTSOState) (v : tid -> positive) : State exchanger_lts :=
    match exch_phase s with
    | Idle _ => Idle (combo_exchanger_raw_with_view s v)
    | Pending _ t op => Pending (combo_exchanger_raw_with_view s v) t op
    end.

  Definition combo_exchanger_state (s : ComboTSOState) : State exchanger_lts :=
    combo_exchanger_state_with_view s
      (combo_view_at (combo_view s) L_exchanger_offer).

  Definition combo_cas_view_after {X : Type}
    (l : GlobalLoc) (v : tid -> GlobalLoc -> positive)
    (ev : @ThreadEvent (CASRegTSOSpec.ECASReg X))
    (v' : tid -> positive) : tid -> GlobalLoc -> positive :=
    match te_ev ev with
    | ResEv CASRegTSOSpec.get _ =>
        combo_view_update_tid_all v (te_tid ev) (v' (te_tid ev))
    | ResEv (CASRegTSOSpec.cas _ _) _ => combo_view_update_all v'
    | _ => combo_view_update v l v'
    end.

  Definition combo_mem_view_after
    (v : tid -> GlobalLoc -> positive)
    (ev : @ThreadEvent
      (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr)))
    (v' : tid -> positive) : tid -> GlobalLoc -> positive :=
    match te_ev ev with
    (* OwnedMemTSO treats allocation and writes as release/fence-like
       operations by advancing every thread's memory view.  In the combined
       TSO layer we lift those releases to all global locations.  Reads pick a
       global timestamp and advance the reading thread's frontier at every
       global location, while leaving other threads' views unchanged. *)
    | ResEv OwnedMemTSOSpec.malloc _ => combo_view_update_all v'
    | ResEv (OwnedMemTSOSpec.mread _) _ =>
        combo_view_update_tid_all v (te_tid ev) (v' (te_tid ev))
    | ResEv (OwnedMemTSOSpec.mwrite _ _) _ => combo_view_update_all v'
    | _ => combo_view_update v L_stack_mem v'
    end.

  Definition combo_with_stack_top
    (s : ComboTSOState)
    (ev : @ThreadEvent (CASRegTSOSpec.ECASReg (option HeapSpec.Addr)))
    (top : State stack_top_lts) : ComboTSOState :=
    let raw := AtomicLTS.state top in
    {|
      stack_top_hist := CASRegTSOSpec.cas_mem raw;
      stack_top_phase := top;
      stack_heap := stack_heap s;
      stack_mem_phase := stack_mem_phase s;
      exch_hist := exch_hist s;
      exch_phase := exch_phase s;
      combo_view :=
        combo_cas_view_after L_stack_top (combo_view s) ev
          (CASRegTSOSpec.cas_view raw);
      loc_status := loc_status s;
    |}.

  Definition combo_with_stack_mem
    (s : ComboTSOState)
    (ev : @ThreadEvent
      (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr)))
    (mem : State stack_mem_lts) : ComboTSOState :=
    let raw := AtomicLTS.state mem in
    {|
      stack_top_hist := stack_top_hist s;
      stack_top_phase := stack_top_phase s;
      stack_heap := OwnedMemTSOSpec.om_heap raw;
      stack_mem_phase := mem;
      exch_hist := exch_hist s;
      exch_phase := exch_phase s;
      combo_view :=
        combo_mem_view_after (combo_view s) ev
          (OwnedMemTSOSpec.om_view raw);
      loc_status := OwnedMemTSOSpec.om_loc raw;
    |}.

  Definition combo_with_exchanger
    (s : ComboTSOState)
    (ev : @ThreadEvent (CASRegTSOSpec.ECASReg EX.Offer))
    (ex : State exchanger_lts) : ComboTSOState :=
    let raw := AtomicLTS.state ex in
    {|
      stack_top_hist := stack_top_hist s;
      stack_top_phase := stack_top_phase s;
      stack_heap := stack_heap s;
      stack_mem_phase := stack_mem_phase s;
      exch_hist := CASRegTSOSpec.cas_mem raw;
      exch_phase := ex;
      combo_view :=
        combo_cas_view_after L_exchanger_offer (combo_view s) ev
          (CASRegTSOSpec.cas_view raw);
      loc_status := loc_status s;
    |}.

  Definition combo_sig : Sig.t :=
    Sig.Plus.omap (li_sig TS.E) (li_sig EX.E).

  Definition map_stack_top_event
    (ev : @ThreadEvent (CASRegTSOSpec.ECASReg (option HeapSpec.Addr))) :
    @ThreadEvent combo_sig :=
    match te_ev ev with
    | InvEv op => Build_ThreadEvent (te_tid ev) (InvEv (inl (inl op)))
    | ResEv op ret => Build_ThreadEvent (te_tid ev) (ResEv (inl (inl op)) ret)
    end.

  Definition map_stack_mem_event
    (ev : @ThreadEvent
      (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))) :
    @ThreadEvent combo_sig :=
    match te_ev ev with
    | InvEv op => Build_ThreadEvent (te_tid ev) (InvEv (inl (inr op)))
    | ResEv op ret => Build_ThreadEvent (te_tid ev) (ResEv (inl (inr op)) ret)
    end.

  Definition map_exchanger_event
    (ev : @ThreadEvent (CASRegTSOSpec.ECASReg EX.Offer)) :
    @ThreadEvent combo_sig :=
    match te_ev ev with
    | InvEv op => Build_ThreadEvent (te_tid ev) (InvEv (inr op))
    | ResEv op ret => Build_ThreadEvent (te_tid ev) (ResEv (inr op) ret)
    end.

  Definition combo_cas_global_ok {X : Type}
    (l : GlobalLoc) (v : tid -> GlobalLoc -> positive)
    (ev : @ThreadEvent (CASRegTSOSpec.ECASReg X))
    (st : State (CASRegTSOSpec.VCASRegTSO (A:=X))) : Prop :=
    match te_ev ev with
    | InvEv _ => True
    | ResEv CASRegTSOSpec.get _ =>
        exists h,
          combo_view_fresh v h /\
          CASRegTSOSpec.cas_view (AtomicLTS.state st) =
            CASRegTSOSpec.upd_tid_time (combo_view_at v l) (te_tid ev) h
    | ResEv (CASRegTSOSpec.cas _ _) _ =>
        exists h,
          combo_view_fresh v h /\
          CASRegTSOSpec.cas_view (AtomicLTS.state st) =
            CASRegTSOSpec.view_advance_all h
    end.

  Definition combo_mem_global_ok
    (v : tid -> GlobalLoc -> positive)
    (ev : @ThreadEvent
      (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr)))
    (st : State stack_mem_lts) : Prop :=
    match te_ev ev with
    | InvEv _ => True
    | ResEv OwnedMemTSOSpec.malloc _ =>
        exists h,
          combo_view_fresh v h /\
          OwnedMemTSOSpec.om_view (AtomicLTS.state st) =
            OwnedMemTSOSpec.view_advance_all h
    | ResEv (OwnedMemTSOSpec.mread _) _ =>
        exists h,
          combo_view_fresh v h /\
          OwnedMemTSOSpec.om_view (AtomicLTS.state st) =
            OwnedMemTSOSpec.upd_tid_time
              (combo_view_at v L_stack_mem) (te_tid ev) h
    | ResEv (OwnedMemTSOSpec.mwrite _ _) _ =>
        exists h,
          combo_view_fresh v h /\
          OwnedMemTSOSpec.om_view (AtomicLTS.state st) =
            OwnedMemTSOSpec.view_advance_all h
    end.

  Variant StepComboTSO :
    @ThreadEvent combo_sig -> ComboTSOState -> ComboTSOState -> Prop :=
  | step_combo_stack_top ev s top' :
      Step stack_top_lts ev (combo_stack_top_state s) top' ->
      combo_cas_global_ok L_stack_top (combo_view s) ev top' ->
      StepComboTSO
        (map_stack_top_event ev) s (combo_with_stack_top s ev top')
  | step_combo_stack_mem ev s mem' :
      Step stack_mem_lts ev (combo_stack_mem_state s) mem' ->
      combo_mem_global_ok (combo_view s) ev mem' ->
      StepComboTSO
        (map_stack_mem_event ev) s (combo_with_stack_mem s ev mem')
  | step_combo_exchanger ev s ex' :
      Step exchanger_lts ev (combo_exchanger_state s) ex' ->
      combo_cas_global_ok L_exchanger_offer (combo_view s) ev ex' ->
      StepComboTSO
        (map_exchanger_event ev) s (combo_with_exchanger s ev ex').

  Definition ErrorComboTSO :
    @ThreadEvent combo_sig -> ComboTSOState -> Prop :=
    fun ev s =>
      exists ev_mem,
        ev = map_stack_mem_event ev_mem /\
        Error stack_mem_lts ev_mem (combo_stack_mem_state s).

  Definition VComboTSO : @LTS combo_sig :=
    {|
      State := ComboTSOState;
      Step := StepComboTSO;
      Error := ErrorComboTSO;
    |}.

  Definition init_combo_tso : ComboTSOState :=
    {|
      stack_top_hist := fun _ => None;
      stack_top_phase := Idle TS.initTop;
      stack_heap := HeapSpec.empty_heap;
      stack_mem_phase := Idle (OwnedMemTSOSpec.initOwnedMem);
      exch_hist := fun _ => EX.Empty;
      exch_phase := Idle EX.initE;
      combo_view := fun _ _ => xH;
      loc_status := HeapSpec.empty_heap;
    |}.

  Definition ECombo : layer_interface :=
  {|
    li_sig := combo_sig;
    li_lts := VComboTSO;
    li_init := init_combo_tso;
  |}.

  (* Forget the shared global view discipline and expose the ordinary tensor
     state expected by the existing TryStackTSO/Exchanger correctness proofs. *)
  Definition combo_tensor_state (s : ComboTSOState) : State (li_lts Etensor) :=
    ((combo_stack_top_state s, combo_stack_mem_state s),
     combo_exchanger_state s).

  Definition E : layer_interface := ECombo.

  CoFixpoint lift_left {E1 E2 R} (p : Prog E1 R) : Prog (Sig.Plus.omap E1 E2) R :=
    match p with
    | Vis m k => Vis (inl m) (fun r => lift_left (k r))
    | Ret r => Ret r
    | Tau p' => Tau (lift_left p')
    end.

  CoFixpoint lift_right {E1 E2 R} (p : Prog E2 R) : Prog (Sig.Plus.omap E1 E2) R :=
    match p with
    | Vis m k => Vis (inr m) (fun r => lift_right (k r))
    | Ret r => Ret r
    | Tau p' => Tau (lift_right p')
    end.

  Lemma lift_left_ret_inv {E1 E2 R} (p : Prog E1 R) r :
    @lift_left E1 E2 R p = Ret r -> p = Ret r.
  Proof.
    destruct p; intros H; rewrite PPid in H at 1; simpl in H; try discriminate.
    inversion H. reflexivity.
  Qed.

  Lemma lift_right_ret_inv {E1 E2 R} (p : Prog E2 R) r :
    @lift_right E1 E2 R p = Ret r -> p = Ret r.
  Proof.
    destruct p; intros H; rewrite PPid in H at 1; simpl in H; try discriminate.
    inversion H. reflexivity.
  Qed.

  Lemma lift_left_tau_inv {E1 E2 R} (p : Prog E1 R) q :
    @lift_left E1 E2 R p = Tau q ->
    exists p', p = Tau p' /\ q = lift_left p'.
  Proof.
    destruct p; intros H; rewrite PPid in H at 1; simpl in H; try discriminate.
    inversion H; subst. eauto.
  Qed.

	  Lemma lift_right_tau_inv {E1 E2 R} (p : Prog E2 R) q :
	    @lift_right E1 E2 R p = Tau q ->
	    exists p', p = Tau p' /\ q = lift_right p'.
	  Proof.
	    destruct p; intros H; rewrite PPid in H at 1; simpl in H; try discriminate.
	    inversion H; subst. eauto.
	  Qed.

	  Lemma some_eq {X : Type} (x y : X) :
	    Some x = Some y -> x = y.
	  Proof.
	    intro H. inversion H. reflexivity.
	  Qed.

	  Lemma lift_left_vis_inv {E1 E2 R} (p : Prog E1 R) op k :
	    @lift_left E1 E2 R p = Vis (inl op) k ->
	    exists k', p = Vis op k' /\ forall r, k r = lift_left (k' r).
	  Proof.
	    destruct p as [op' k'|r|p']; intros H;
	      rewrite PPid in H at 1; simpl in H; try discriminate.
	    inversion H; subst.
	    pose (vis_sig := fun p : Prog (Sig.Plus.omap E1 E2) R =>
	      match p with
	      | Vis op k =>
	          Some (existT
	            (fun op => SigBase.ar op -> Prog (Sig.Plus.omap E1 E2) R)
	            op k)
	      | _ => None
	      end).
	    pose proof (f_equal vis_sig H) as Hopt.
	    simpl in Hopt.
	    assert (Hsig :
	      existT
	        (fun op => SigBase.ar op -> Prog (Sig.Plus.omap E1 E2) R)
	        (inl op) (fun r => lift_left (k' r)) =
	      existT
	        (fun op => SigBase.ar op -> Prog (Sig.Plus.omap E1 E2) R)
	        (inl op) k).
	    { exact (some_eq _ _ Hopt). }
	    pose proof (inj_pair2 _ _ _ _ _ Hsig) as Hfun.
	    exists k'. split; [reflexivity|].
	    intro r. rewrite <- Hfun. reflexivity.
	  Qed.

	  Lemma lift_right_vis_inv {E1 E2 R} (p : Prog E2 R) op k :
	    @lift_right E1 E2 R p = Vis (inr op) k ->
	    exists k', p = Vis op k' /\ forall r, k r = lift_right (k' r).
	  Proof.
	    destruct p as [op' k'|r|p']; intros H;
	      rewrite PPid in H at 1; simpl in H; try discriminate.
	    inversion H; subst.
	    pose (vis_sig := fun p : Prog (Sig.Plus.omap E1 E2) R =>
	      match p with
	      | Vis op k =>
	          Some (existT
	            (fun op => SigBase.ar op -> Prog (Sig.Plus.omap E1 E2) R)
	            op k)
	      | _ => None
	      end).
	    pose proof (f_equal vis_sig H) as Hopt.
	    simpl in Hopt.
	    assert (Hsig :
	      existT
	        (fun op => SigBase.ar op -> Prog (Sig.Plus.omap E1 E2) R)
	        (inr op) (fun r => lift_right (k' r)) =
	      existT
	        (fun op => SigBase.ar op -> Prog (Sig.Plus.omap E1 E2) R)
	        (inr op) k).
	    { exact (some_eq _ _ Hopt). }
	    pose proof (inj_pair2 _ _ _ _ _ Hsig) as Hfun.
	    exists k'. split; [reflexivity|].
	    intro r. rewrite <- Hfun. reflexivity.
	  Qed.

  Lemma lift_left_vis_right_absurd {E1 E2 R} (p : Prog E1 R) op k :
    @lift_left E1 E2 R p <> Vis (inr op) k.
  Proof.
    destruct p; intro H; rewrite PPid in H at 1; simpl in H; discriminate.
  Qed.

  Lemma lift_right_vis_left_absurd {E1 E2 R} (p : Prog E2 R) op k :
    @lift_right E1 E2 R p <> Vis (inl op) k.
  Proof.
    destruct p; intro H; rewrite PPid in H at 1; simpl in H; discriminate.
  Qed.

  Definition components_impl : ModuleImpl combo_sig (li_sig Fmid) :=
    fun m t =>
      match m with
      | inl m1 => lift_left (li_impl TS.Mtrystack m1 t)
      | inr m2 => lift_right (li_impl EX.Mexchanger m2 t)
      end.

  Definition map_option_left {X Y} (x : option X) : option (X + Y) :=
    match x with
    | Some x => Some (inl x)
    | None => None
    end.

  Definition map_option_right {X Y} (y : option Y) : option (X + Y) :=
    match y with
    | Some y => Some (inr y)
    | None => None
    end.

  Variant tensor_threadstate :
    option (@Semantics.ThreadState (li_sig Etensor) (li_sig Fmid)) ->
    option (@Semantics.ThreadState (li_sig TS.E) (li_sig TS.F)) ->
    option (@Semantics.ThreadState (li_sig EX.E) (li_sig EX.F)) ->
    Prop :=
  | tensor_ts_empty :
      tensor_threadstate None None None
  | tensor_ts_left f p b :
      tensor_threadstate
        (Some (Semantics.Build_ThreadState (inl f) (lift_left p) (map_option_left b)))
        (Some (Semantics.Build_ThreadState f p b))
        None
  | tensor_ts_right f p b :
      tensor_threadstate
        (Some (Semantics.Build_ThreadState (inr f) (lift_right p) (map_option_right b)))
        None
        (Some (Semantics.Build_ThreadState f p b)).

  Definition tensor_threadpool
    (c : @Semantics.ThreadPoolState (li_sig Etensor) (li_sig Fmid))
    (c1 : @Semantics.ThreadPoolState (li_sig TS.E) (li_sig TS.F))
    (c2 : @Semantics.ThreadPoolState (li_sig EX.E) (li_sig EX.F)) : Prop :=
    forall t, tensor_threadstate (TMap.find t c) (TMap.find t c1) (TMap.find t c2).

  Variant tensor_linstate :
    option (@Semantics.LinState (li_sig Fmid)) ->
    option (@Semantics.LinState (li_sig TS.F)) ->
    option (@Semantics.LinState (li_sig EX.F)) ->
    Prop :=
  | tensor_ls_empty :
      tensor_linstate None None None
  | tensor_ls_inv_left f :
      tensor_linstate
        (Some (Semantics.ls_inv (inl f)))
        (Some (Semantics.ls_inv f))
        None
  | tensor_ls_lini_left f :
      tensor_linstate
        (Some (Semantics.ls_lini (inl f)))
        (Some (Semantics.ls_lini f))
        None
  | tensor_ls_linr_left f ret :
      tensor_linstate
        (Some (Semantics.ls_linr (inl f) ret))
        (Some (Semantics.ls_linr f ret))
        None
  | tensor_ls_inv_right f :
      tensor_linstate
        (Some (Semantics.ls_inv (inr f)))
        None
        (Some (Semantics.ls_inv f))
  | tensor_ls_lini_right f :
      tensor_linstate
        (Some (Semantics.ls_lini (inr f)))
        None
        (Some (Semantics.ls_lini f))
  | tensor_ls_linr_right f ret :
      tensor_linstate
        (Some (Semantics.ls_linr (inr f) ret))
        None
        (Some (Semantics.ls_linr f ret)).

  Definition tensor_linmap
    (π : tmap (@Semantics.LinState (li_sig Fmid)))
    (π1 : tmap (@Semantics.LinState (li_sig TS.F)))
    (π2 : tmap (@Semantics.LinState (li_sig EX.F))) : Prop :=
    forall t, tensor_linstate (TMap.find t π) (TMap.find t π1) (TMap.find t π2).

  Lemma tensor_threadpool_empty :
    tensor_threadpool (TMap.empty _) (TMap.empty _) (TMap.empty _).
  Proof.
    intro t. rewrite !PositiveMap.gempty. constructor.
  Qed.

  Lemma tensor_linmap_empty :
    tensor_linmap (TMap.empty _) (TMap.empty _) (TMap.empty _).
  Proof.
    intro t. rewrite !PositiveMap.gempty. constructor.
  Qed.

  Lemma tensor_linmap_add_inv_left t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π2 = None ->
    tensor_linmap
      (TMap.add t (Semantics.ls_inv (inl f)) π)
      (TMap.add t (Semantics.ls_inv f) π1)
      π2.
  Proof.
    intros Hmap Hright t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hright. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hmap.
  Qed.

  Lemma tensor_linmap_add_lini_left t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π2 = None ->
    tensor_linmap
      (TMap.add t (Semantics.ls_lini (inl f)) π)
      (TMap.add t (Semantics.ls_lini f) π1)
      π2.
  Proof.
    intros Hmap Hright t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hright. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hmap.
  Qed.

  Lemma tensor_linmap_add_linr_left t f ret π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π2 = None ->
    tensor_linmap
      (TMap.add t (Semantics.ls_linr (inl f) ret) π)
      (TMap.add t (Semantics.ls_linr f ret) π1)
      π2.
  Proof.
    intros Hmap Hright t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hright. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hmap.
  Qed.

  Lemma tensor_linmap_add_inv_right t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π1 = None ->
    tensor_linmap
      (TMap.add t (Semantics.ls_inv (inr f)) π)
      π1
      (TMap.add t (Semantics.ls_inv f) π2).
  Proof.
    intros Hmap Hleft t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hleft. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hmap.
  Qed.

  Lemma tensor_linmap_add_lini_right t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π1 = None ->
    tensor_linmap
      (TMap.add t (Semantics.ls_lini (inr f)) π)
      π1
      (TMap.add t (Semantics.ls_lini f) π2).
  Proof.
    intros Hmap Hleft t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hleft. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hmap.
  Qed.

  Lemma tensor_linmap_add_linr_right t f ret π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π1 = None ->
    tensor_linmap
      (TMap.add t (Semantics.ls_linr (inr f) ret) π)
      π1
      (TMap.add t (Semantics.ls_linr f ret) π2).
  Proof.
    intros Hmap Hleft t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hleft. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hmap.
  Qed.

  Lemma tensor_linmap_remove_left t π π1 π2 ls :
    tensor_linmap π π1 π2 ->
    TMap.find t π1 = Some ls ->
    tensor_linmap (TMap.remove t π) (TMap.remove t π1) π2.
  Proof.
    intros Hmap Hfind t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.grs.
      specialize (Hmap t). rewrite Hfind in Hmap.
      dependent destruction Hmap;
        match goal with
        | H : None = TMap.find t π2 |- _ => rewrite <- H
        | _ => idtac
        end;
        constructor.
    - rewrite !PositiveMap.gro by auto. apply Hmap.
  Qed.

  Lemma tensor_linmap_remove_right t π π1 π2 ls :
    tensor_linmap π π1 π2 ->
    TMap.find t π2 = Some ls ->
    tensor_linmap (TMap.remove t π) π1 (TMap.remove t π2).
  Proof.
    intros Hmap Hfind t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.grs.
      specialize (Hmap t). rewrite Hfind in Hmap.
      dependent destruction Hmap;
        match goal with
        | H : None = TMap.find t π1 |- _ => rewrite <- H
        | _ => idtac
        end;
        constructor.
    - rewrite !PositiveMap.gro by auto. apply Hmap.
  Qed.

  Lemma tensor_threadpool_none_left t c c1 c2 :
    tensor_threadpool c c1 c2 ->
    TMap.find t c = None ->
    TMap.find t c1 = None /\ TMap.find t c2 = None.
  Proof.
    intros Hpool Hnone.
    specialize (Hpool t). rewrite Hnone in Hpool.
    dependent destruction Hpool. auto.
  Qed.

  Lemma tensor_threadpool_add_left t f p b c c1 c2 :
    tensor_threadpool c c1 c2 ->
    TMap.find t c2 = None ->
    tensor_threadpool
      (TMap.add t
        (Semantics.Build_ThreadState (inl f) (lift_left p) (map_option_left b)) c)
      (TMap.add t (Semantics.Build_ThreadState f p b) c1)
      c2.
  Proof.
    intros Hpool Hright t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hright. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hpool.
  Qed.

  Lemma tensor_threadpool_add_right t f p b c c1 c2 :
    tensor_threadpool c c1 c2 ->
    TMap.find t c1 = None ->
    tensor_threadpool
      (TMap.add t
        (Semantics.Build_ThreadState (inr f) (lift_right p) (map_option_right b)) c)
      c1
      (TMap.add t (Semantics.Build_ThreadState f p b) c2).
  Proof.
    intros Hpool Hleft t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.gss, Hleft. constructor.
    - rewrite !PositiveMap.gso by auto. apply Hpool.
  Qed.

  Lemma tensor_threadpool_remove_left t c c1 c2 ts :
    tensor_threadpool c c1 c2 ->
    TMap.find t c1 = Some ts ->
    tensor_threadpool (TMap.remove t c) (TMap.remove t c1) c2.
  Proof.
    intros Hpool Hfind t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.grs.
      specialize (Hpool t). rewrite Hfind in Hpool.
      dependent destruction Hpool;
        match goal with
        | H : None = TMap.find t c2 |- _ => rewrite <- H
        | _ => idtac
        end;
        constructor.
    - rewrite !PositiveMap.gro by auto. apply Hpool.
  Qed.

  Lemma tensor_threadpool_remove_right t c c1 c2 ts :
    tensor_threadpool c c1 c2 ->
    TMap.find t c2 = Some ts ->
    tensor_threadpool (TMap.remove t c) c1 (TMap.remove t c2).
  Proof.
    intros Hpool Hfind t'.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite !PositiveMap.grs.
      specialize (Hpool t). rewrite Hfind in Hpool.
      dependent destruction Hpool;
        match goal with
        | H : None = TMap.find t c1 |- _ => rewrite <- H
        | _ => idtac
        end;
        constructor.
    - rewrite !PositiveMap.gro by auto. apply Hpool.
  Qed.

  Definition pool_lin_consistent
    {E F : Reg.Op.t} (c : @Semantics.ThreadPoolState E F)
    (π : tmap (@Semantics.LinState F)) : Prop :=
    forall t, TMap.find t c = None -> TMap.find t π = None.

  Lemma pool_lin_consistent_empty {E F : Reg.Op.t} :
    pool_lin_consistent (@TMap.empty (@Semantics.ThreadState E F))
      (@TMap.empty (@Semantics.LinState F)).
  Proof.
    intros t _. rewrite PositiveMap.gempty. reflexivity.
  Qed.

  Lemma pool_lin_consistent_add {E F : Reg.Op.t}
    (c : @Semantics.ThreadPoolState E F) (π : tmap (@Semantics.LinState F))
    t ts ls :
    pool_lin_consistent c π ->
    pool_lin_consistent (TMap.add t ts c) (TMap.add t ls π).
  Proof.
    intros Hcons t' Hfind.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite PositiveMap.gss in Hfind. discriminate.
    - rewrite PositiveMap.gso in Hfind by auto.
      rewrite PositiveMap.gso by auto. apply Hcons; auto.
  Qed.

  Lemma pool_lin_consistent_remove {E F : Reg.Op.t}
    (c : @Semantics.ThreadPoolState E F) (π : tmap (@Semantics.LinState F))
    t :
    pool_lin_consistent c π ->
    pool_lin_consistent (TMap.remove t c) (TMap.remove t π).
  Proof.
    intros Hcons t' Hfind.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite PositiveMap.grs. reflexivity.
    - rewrite PositiveMap.gro in Hfind by auto.
      rewrite PositiveMap.gro by auto. apply Hcons; auto.
  Qed.

  Lemma pool_lin_consistent_update_pool {E F : Reg.Op.t}
    (c : @Semantics.ThreadPoolState E F) (π : tmap (@Semantics.LinState F))
    t ts :
    pool_lin_consistent c π ->
    TMap.find t c <> None ->
    pool_lin_consistent (TMap.add t ts c) π.
  Proof.
    intros Hcons Hsome t' Hfind.
    destruct (PositiveMap.E.eq_dec t' t); subst.
    - rewrite PositiveMap.gss in Hfind. discriminate.
    - rewrite PositiveMap.gso in Hfind by auto. apply Hcons; auto.
  Qed.

  Lemma poss_step_preserve_none {F : Reg.Op.t} {VF : @LTS F}
    t ρ ρ' π π' :
    @Semantics.poss_step F VF
      (@Semantics.PossOk F VF ρ π) (@Semantics.PossOk F VF ρ' π') ->
    TMap.find t π = None ->
    TMap.find t π' = None.
  Proof.
    intros Hstep Hnone.
    inversion Hstep; subst.
    - destruct (PositiveMap.E.eq_dec t t0); subst.
      + rewrite Hlin in Hnone. discriminate.
      + rewrite PositiveMap.gso by auto. exact Hnone.
    - destruct (PositiveMap.E.eq_dec t t0); subst.
      + rewrite Hlin in Hnone. discriminate.
      + rewrite PositiveMap.gso by auto. exact Hnone.
  Qed.

  Lemma poss_steps_pool_lin_consistent {E F : Reg.Op.t} {VF : @LTS F}
    (c : @Semantics.ThreadPoolState E F) ρ ρ' π π' :
    pool_lin_consistent c π ->
    @Semantics.poss_steps F VF
      (@Semantics.PossOk F VF ρ π) (@Semantics.PossOk F VF ρ' π') ->
    pool_lin_consistent c π'.
  Proof.
    intros Hcons Hsteps t Hnonec.
    unfold Semantics.poss_steps in Hsteps.
    apply clos_rt_rtn1_iff in Hsteps.
    remember (@Semantics.PossOk F VF ρ π) as p0.
    remember (@Semantics.PossOk F VF ρ' π') as p1.
    revert ρ π Hcons Heqp0 ρ' π' Heqp1.
    induction Hsteps; intros; subst.
    - inversion Heqp1; subst. apply Hcons; auto.
    - destruct y as [ρm πm|].
      + specialize (IHHsteps _ _ Hcons eq_refl _ _ eq_refl) as Hconsm.
        inversion H; subst.
        * eapply poss_step_preserve_none; eauto.
        * eapply poss_step_preserve_none; eauto.
      + inversion H.
  Qed.

  Lemma tensor_threadpool_ret_left t f ret c c1 c2 :
    tensor_threadpool c c1 c2 ->
    TMap.find t c =
      @Some (@Semantics.ThreadState (li_sig Etensor) (li_sig Fmid))
        {| Semantics.ts_op := inl f;
           Semantics.ts_prog := Ret ret;
           Semantics.ts_pend := None |} ->
    TMap.find t c1 =
      @Some (@Semantics.ThreadState (li_sig TS.E) (li_sig TS.F))
        {| Semantics.ts_op := f;
           Semantics.ts_prog := Ret ret;
           Semantics.ts_pend := None |} /\
    TMap.find t c2 = None.
  Proof.
    intros Hpool Hfind.
    pose proof (Hpool t) as Hpoolt.
    replace (TMap.find t c) with
      (@Some (@Semantics.ThreadState (li_sig Etensor) (li_sig Fmid))
        {| Semantics.ts_op := inl f;
           Semantics.ts_prog := Ret ret;
           Semantics.ts_pend := None |}) in Hpoolt by exact (eq_sym Hfind).
    inversion Hpoolt; subst; try discriminate; try congruence.
    pose proof (inj_pair2 _ _ _ _ _ H1) as Hprog.
    apply lift_left_ret_inv in Hprog. subst.
    destruct b; inversion H2; subst.
    split; symmetry; auto.
  Qed.

  Lemma tensor_threadpool_ret_right t f ret c c1 c2 :
    tensor_threadpool c c1 c2 ->
    TMap.find t c =
      @Some (@Semantics.ThreadState (li_sig Etensor) (li_sig Fmid))
        {| Semantics.ts_op := inr f;
           Semantics.ts_prog := Ret ret;
           Semantics.ts_pend := None |} ->
    TMap.find t c1 = None /\
    TMap.find t c2 =
      @Some (@Semantics.ThreadState (li_sig EX.E) (li_sig EX.F))
        {| Semantics.ts_op := f;
           Semantics.ts_prog := Ret ret;
           Semantics.ts_pend := None |}.
  Proof.
    intros Hpool Hfind.
    pose proof (Hpool t) as Hpoolt.
    replace (TMap.find t c) with
      (@Some (@Semantics.ThreadState (li_sig Etensor) (li_sig Fmid))
        {| Semantics.ts_op := inr f;
           Semantics.ts_prog := Ret ret;
           Semantics.ts_pend := None |}) in Hpoolt by exact (eq_sym Hfind).
    inversion Hpoolt; subst; try discriminate; try congruence.
    pose proof (inj_pair2 _ _ _ _ _ H1) as Hprog.
    apply lift_right_ret_inv in Hprog. subst.
    destruct b; inversion H2; subst.
    split; symmetry; auto.
  Qed.

  Lemma tensor_linmap_inv_left t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π1 = Some (Semantics.ls_inv f) ->
    TMap.find t π = Some (Semantics.ls_inv (inl f)) /\
    TMap.find t π2 = None.
  Proof.
    intros Hmap Hfind.
    specialize (Hmap t). rewrite Hfind in Hmap.
    dependent destruction Hmap; split; symmetry; auto.
  Qed.

  Lemma tensor_linmap_lini_left t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π1 = Some (Semantics.ls_lini f) ->
    TMap.find t π = Some (Semantics.ls_lini (inl f)) /\
    TMap.find t π2 = None.
  Proof.
    intros Hmap Hfind.
    specialize (Hmap t). rewrite Hfind in Hmap.
    dependent destruction Hmap; split; symmetry; auto.
  Qed.

  Lemma tensor_linmap_linr_left t f ret π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π1 = Some (Semantics.ls_linr f ret) ->
    TMap.find t π = Some (Semantics.ls_linr (inl f) ret) /\
    TMap.find t π2 = None.
  Proof.
    intros Hmap Hfind.
    specialize (Hmap t). rewrite Hfind in Hmap.
    dependent destruction Hmap; split; symmetry; auto.
  Qed.

  Lemma tensor_linmap_inv_right t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π2 = Some (Semantics.ls_inv f) ->
    TMap.find t π = Some (Semantics.ls_inv (inr f)) /\
    TMap.find t π1 = None.
  Proof.
    intros Hmap Hfind.
    specialize (Hmap t). rewrite Hfind in Hmap.
    dependent destruction Hmap; split; symmetry; auto.
  Qed.

  Lemma tensor_linmap_lini_right t f π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π2 = Some (Semantics.ls_lini f) ->
    TMap.find t π = Some (Semantics.ls_lini (inr f)) /\
    TMap.find t π1 = None.
  Proof.
    intros Hmap Hfind.
    specialize (Hmap t). rewrite Hfind in Hmap.
    dependent destruction Hmap; split; symmetry; auto.
  Qed.

  Lemma tensor_linmap_linr_right t f ret π π1 π2 :
    tensor_linmap π π1 π2 ->
    TMap.find t π2 = Some (Semantics.ls_linr f ret) ->
    TMap.find t π = Some (Semantics.ls_linr (inr f) ret) /\
    TMap.find t π1 = None.
  Proof.
    intros Hmap Hfind.
    specialize (Hmap t). rewrite Hfind in Hmap.
    dependent destruction Hmap; split; symmetry; auto.
  Qed.

  Lemma tensor_poss_step_left
    (ρ1 ρ1' : State (li_lts TS.F)) (ρ2 : State (li_lts EX.F))
    π π1 π1' π2 :
    tensor_linmap π π1 π2 ->
    @Semantics.poss_step (li_sig TS.F) (li_lts TS.F)
      (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ1 π1)
      (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ1' π1') ->
    exists π',
      @Semantics.poss_step (li_sig Fmid) (li_lts Fmid)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2) π)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1', ρ2) π') /\
      tensor_linmap π' π1' π2.
  Proof.
    intros Hmap Hstep. inversion Hstep; subst.
    - edestruct tensor_linmap_inv_left as [Hπ Hright]; eauto.
      exists (TMap.add t0 (Semantics.ls_lini (inl f)) π).
      split.
      + eapply Semantics.ps_inv.
        * simpl. split; eauto.
        * exact Hπ.
      + eapply tensor_linmap_add_lini_left; eauto.
    - edestruct tensor_linmap_lini_left as [Hπ Hright]; eauto.
      exists (TMap.add t0 (Semantics.ls_linr (inl f) ret) π).
      split.
      + eapply Semantics.ps_ret.
        * simpl. split; eauto.
        * exact Hπ.
      + eapply tensor_linmap_add_linr_left; eauto.
  Qed.

  Lemma tensor_poss_step_right
    (ρ1 : State (li_lts TS.F)) (ρ2 ρ2' : State (li_lts EX.F))
    π π1 π2 π2' :
    tensor_linmap π π1 π2 ->
    @Semantics.poss_step (li_sig EX.F) (li_lts EX.F)
      (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ2 π2)
      (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ2' π2') ->
    exists π',
      @Semantics.poss_step (li_sig Fmid) (li_lts Fmid)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2) π)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2') π') /\
      tensor_linmap π' π1 π2'.
  Proof.
    intros Hmap Hstep. inversion Hstep; subst.
    - edestruct tensor_linmap_inv_right as [Hπ Hleft]; eauto.
      exists (TMap.add t0 (Semantics.ls_lini (inr f)) π).
      split.
      + eapply Semantics.ps_inv.
        * simpl. split; eauto.
        * exact Hπ.
      + eapply tensor_linmap_add_lini_right; eauto.
    - edestruct tensor_linmap_lini_right as [Hπ Hleft]; eauto.
      exists (TMap.add t0 (Semantics.ls_linr (inr f) ret) π).
      split.
      + eapply Semantics.ps_ret.
        * simpl. split; eauto.
        * exact Hπ.
      + eapply tensor_linmap_add_linr_right; eauto.
  Qed.

  Lemma tensor_poss_error_left
    (ρ1 : State (li_lts TS.F)) (ρ2 : State (li_lts EX.F))
    π π1 π2 :
    tensor_linmap π π1 π2 ->
    @Semantics.poss_step (li_sig TS.F) (li_lts TS.F)
      (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ1 π1)
      (@Semantics.PossError (li_sig TS.F) (li_lts TS.F)) ->
    @Semantics.poss_step (li_sig Fmid) (li_lts Fmid)
      (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2) π)
      (@Semantics.PossError (li_sig Fmid) (li_lts Fmid)).
  Proof.
    intros Hmap Hstep. inversion Hstep; subst.
    simpl in Herror. contradiction.
  Qed.

  Lemma tensor_poss_error_right
    (ρ1 : State (li_lts TS.F)) (ρ2 : State (li_lts EX.F))
    π π1 π2 :
    tensor_linmap π π1 π2 ->
    @Semantics.poss_step (li_sig EX.F) (li_lts EX.F)
      (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ2 π2)
      (@Semantics.PossError (li_sig EX.F) (li_lts EX.F)) ->
    @Semantics.poss_step (li_sig Fmid) (li_lts Fmid)
      (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2) π)
      (@Semantics.PossError (li_sig Fmid) (li_lts Fmid)).
  Proof.
    intros Hmap Hstep. inversion Hstep; subst.
    simpl in Herror. contradiction.
  Qed.

  Lemma tensor_poss_steps_left
    (ρ1 ρ1' : State (li_lts TS.F)) (ρ2 : State (li_lts EX.F))
    π π1 π1' π2 :
    tensor_linmap π π1 π2 ->
    @Semantics.poss_steps (li_sig TS.F) (li_lts TS.F)
      (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ1 π1)
      (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ1' π1') ->
    exists π',
      @Semantics.poss_steps (li_sig Fmid) (li_lts Fmid)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2) π)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1', ρ2) π') /\
      tensor_linmap π' π1' π2.
  Proof.
    intros Hmap Hsteps.
    unfold Semantics.poss_steps in Hsteps.
    apply clos_rt_rtn1_iff in Hsteps.
    remember (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ1 π1) as p0.
    remember (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ1' π1') as p1.
    revert ρ1 π1 π Hmap Heqp0 ρ1' π1' Heqp1.
    induction Hsteps; intros; subst.
    - inversion Heqp1; subst.
      exists π0. split; [apply rt_refl|assumption].
    - destruct y as [ρm πm|].
      + specialize (IHHsteps _ _ _ Hmap eq_refl _ _ eq_refl)
          as [πm12 [Hpref Hmapm]].
        inversion H; subst.
        * edestruct tensor_poss_step_left as [π' [Hlast Hmap']]; eauto.
          exists π'. split; [eapply rt_trans; eauto; apply rt_step; exact Hlast|].
          exact Hmap'.
        * edestruct tensor_poss_step_left as [π' [Hlast Hmap']]; eauto.
          exists π'. split; [eapply rt_trans; eauto; apply rt_step; exact Hlast|].
          exact Hmap'.
      + inversion H.
  Qed.

  Lemma tensor_poss_steps_right
    (ρ1 : State (li_lts TS.F)) (ρ2 ρ2' : State (li_lts EX.F))
    π π1 π2 π2' :
    tensor_linmap π π1 π2 ->
    @Semantics.poss_steps (li_sig EX.F) (li_lts EX.F)
      (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ2 π2)
      (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ2' π2') ->
    exists π',
      @Semantics.poss_steps (li_sig Fmid) (li_lts Fmid)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2) π)
        (@Semantics.PossOk (li_sig Fmid) (li_lts Fmid) (ρ1, ρ2') π') /\
      tensor_linmap π' π1 π2'.
  Proof.
    intros Hmap Hsteps.
    unfold Semantics.poss_steps in Hsteps.
    apply clos_rt_rtn1_iff in Hsteps.
    remember (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ2 π2) as p0.
    remember (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ2' π2') as p1.
    revert ρ2 π2 π Hmap Heqp0 ρ2' π2' Heqp1.
    induction Hsteps; intros; subst.
    - inversion Heqp1; subst.
      exists π0. split; [apply rt_refl|assumption].
    - destruct y as [ρm πm|].
      + specialize (IHHsteps _ _ _ Hmap eq_refl _ _ eq_refl)
          as [πm12 [Hpref Hmapm]].
        inversion H; subst.
        * edestruct tensor_poss_step_right as [π' [Hlast Hmap']]; eauto.
          exists π'. split; [eapply rt_trans; eauto; apply rt_step; exact Hlast|].
          exact Hmap'.
        * edestruct tensor_poss_step_right as [π' [Hlast Hmap']]; eauto.
          exists π'. split; [eapply rt_trans; eauto; apply rt_step; exact Hlast|].
          exact Hmap'.
      + inversion H.
  Qed.

  Lemma trystack_poss_steps_noerror ρ π :
    ~ @Semantics.poss_steps (li_sig TS.F) (li_lts TS.F)
        (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ π)
        (@Semantics.PossError (li_sig TS.F) (li_lts TS.F)).
  Proof.
    intro Hsteps.
    unfold Semantics.poss_steps in Hsteps.
    apply clos_rt_rtn1_iff in Hsteps.
    remember (@Semantics.PossOk (li_sig TS.F) (li_lts TS.F) ρ π) as p0.
    remember (@Semantics.PossError (li_sig TS.F) (li_lts TS.F)) as p1.
    induction Hsteps; subst.
    - discriminate.
    - destruct y as [ρm πm|].
      + inversion H; subst; simpl in Herror; contradiction.
      + inversion H.
  Qed.

  Lemma exchanger_poss_steps_noerror ρ π :
    ~ @Semantics.poss_steps (li_sig EX.F) (li_lts EX.F)
        (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ π)
        (@Semantics.PossError (li_sig EX.F) (li_lts EX.F)).
  Proof.
    intro Hsteps.
    unfold Semantics.poss_steps in Hsteps.
    apply clos_rt_rtn1_iff in Hsteps.
    remember (@Semantics.PossOk (li_sig EX.F) (li_lts EX.F) ρ π) as p0.
    remember (@Semantics.PossError (li_sig EX.F) (li_lts EX.F)) as p1.
    induction Hsteps; subst.
    - discriminate.
    - destruct y as [ρm πm|].
      + inversion H; subst; simpl in Herror; contradiction.
      + inversion H.
  Qed.

  (* simlin currently provides [tens_lts], but not a packaged horizontal
     composition theorem for [TPSimulation.cal].  This is the specialization
     of that missing theorem to TryStackTSO tensor Exchanger. *)
  Lemma tensor_components_sim
    (σ1 : State (li_lts TS.E)) (σ2 : State (li_lts EX.E))
    c c1 c2
    (ρ1 : State (li_lts TS.F)) (ρ2 : State (li_lts EX.F))
    π π1 π2 :
    tensor_threadpool c c1 c2 ->
    tensor_linmap π π1 π2 ->
    @TPSimulation (li_sig TS.E) (li_sig TS.F) (li_lts TS.E) (li_lts TS.F)
      (li_impl TS.Mtrystack) σ1 c1 ρ1 π1 ->
    pool_lin_consistent c1 π1 ->
    @TPSimulation (li_sig EX.E) (li_sig EX.F) (li_lts EX.E) (li_lts EX.F)
      (li_impl EX.Mexchanger) σ2 c2 ρ2 π2 ->
    pool_lin_consistent c2 π2 ->
    @TPSimulation (li_sig Etensor) (li_sig Fmid) (li_lts Etensor) (li_lts Fmid)
      components_impl (σ1, σ2) c (ρ1, ρ2) π.
  Proof.
    revert σ1 σ2 c c1 c2 ρ1 ρ2 π π1 π2.
    cofix IH.
    intros σ1 σ2 c c1 c2 ρ1 ρ2 π π1 π2 Hpool Hlin Hsim1 Hcons1 Hsim2 Hcons2.
    inversion Hsim1 as [Herr1|Hinv1 Hret1 Hustep1 Hlinstep1 Htau1 Hnoerr1]; subst.
    { exfalso. eapply trystack_poss_steps_noerror; eauto. }
    inversion Hsim2 as [Herr2|Hinv2 Hret2 Hustep2 Hlinstep2 Htau2 Hnoerr2]; subst.
    { exfalso. eapply exchanger_poss_steps_noerror; eauto. }
    constructor 2.
    - intros t f c' Hstep.
      inversion Hstep; subst; simpl in *.
      destruct f as [f1|f2].
      + destruct (tensor_threadpool_none_left _ _ _ _ Hpool Hfind) as [Hnone1 Hnone2].
        specialize (Hinv1 t f1 (TMap.add t
          (Semantics.Build_ThreadState f1 (li_impl TS.Mtrystack f1 t) None) c1)).
        assert (@Semantics.invstep (li_sig TS.E) (li_sig TS.F)
          (li_impl TS.Mtrystack) t f1 c1
          (TMap.add t
            (Semantics.Build_ThreadState f1 (li_impl TS.Mtrystack f1 t) None) c1)) as Hinvstep1.
        { constructor; auto. }
        specialize (Hinv1 Hinvstep1).
        cbn [components_impl map_option_left].
        change (TMap.add t
          (Semantics.Build_ThreadState (inl f1)
            (lift_left (li_impl TS.Mtrystack f1 t)) None) c) with
          (TMap.add t
            (Semantics.Build_ThreadState (inl f1)
              (lift_left (li_impl TS.Mtrystack f1 t)) (map_option_left None)) c).
        eapply IH.
        * eapply tensor_threadpool_add_left; [exact Hpool|exact Hnone2].
        * eapply tensor_linmap_add_inv_left; [exact Hlin|].
          apply Hcons2. exact Hnone2.
        * exact Hinv1.
        * apply pool_lin_consistent_add; auto.
        * assumption.
        * assumption.
      + destruct (tensor_threadpool_none_left _ _ _ _ Hpool Hfind) as [Hnone1 Hnone2].
        specialize (Hinv2 t f2 (TMap.add t
          (Semantics.Build_ThreadState f2 (li_impl EX.Mexchanger f2 t) None) c2)).
        assert (@Semantics.invstep (li_sig EX.E) (li_sig EX.F)
          (li_impl EX.Mexchanger) t f2 c2
          (TMap.add t
            (Semantics.Build_ThreadState f2 (li_impl EX.Mexchanger f2 t) None) c2)) as Hinvstep2.
        { constructor; auto. }
        specialize (Hinv2 Hinvstep2).
        cbn [components_impl map_option_right].
        change (TMap.add t
          (Semantics.Build_ThreadState (inr f2)
            (lift_right (li_impl EX.Mexchanger f2 t)) None) c) with
          (TMap.add t
            (Semantics.Build_ThreadState (inr f2)
              (lift_right (li_impl EX.Mexchanger f2 t)) (map_option_right None)) c).
        eapply IH.
        * eapply tensor_threadpool_add_right; [exact Hpool|exact Hnone1].
        * eapply tensor_linmap_add_inv_right; [exact Hlin|].
          apply Hcons1. exact Hnone1.
        * assumption.
        * assumption.
        * exact Hinv2.
        * apply pool_lin_consistent_add; auto.
    - intros t f ret c' Hstep.
      destruct f as [f1|f2].
      + destruct Hstep as [Hfindc Hupd]; subst; simpl in *.
        destruct (tensor_threadpool_ret_left _ _ _ _ _ _ Hpool Hfindc)
          as [Hfind1 Hnone2].
        specialize (Hret1 t f1 ret (TMap.remove t c1)).
        assert (@Semantics.retstep (li_sig TS.E) (li_sig TS.F)
          t f1 ret c1 (TMap.remove t c1)) as Hretstep1
          by (eapply Semantics.RetStep; [exact Hfind1|reflexivity]).
        specialize (Hret1 Hretstep1) as [Hπ1 Hsim1'].
        edestruct tensor_linmap_linr_left as [Hπ Hright]; eauto.
        split; auto.
        eapply IH.
        * eapply tensor_threadpool_remove_left; eauto.
        * eapply tensor_linmap_remove_left; eauto.
        * exact Hsim1'.
        * apply pool_lin_consistent_remove; auto.
        * assumption.
        * assumption.
      + destruct Hstep as [Hfindc Hupd]; subst; simpl in *.
        destruct (tensor_threadpool_ret_right _ _ _ _ _ _ Hpool Hfindc)
          as [Hnone1 Hfind2].
        specialize (Hret2 t f2 ret (TMap.remove t c2)).
        assert (@Semantics.retstep (li_sig EX.E) (li_sig EX.F)
          t f2 ret c2 (TMap.remove t c2)) as Hretstep2
          by (eapply Semantics.RetStep; [exact Hfind2|reflexivity]).
        specialize (Hret2 Hretstep2) as [Hπ2 Hsim2'].
        edestruct tensor_linmap_linr_right as [Hπ Hleft]; eauto.
        split; auto.
        eapply IH.
        * eapply tensor_threadpool_remove_right; eauto.
        * eapply tensor_linmap_remove_right; eauto.
        * assumption.
        * assumption.
        * exact Hsim2'.
        * apply pool_lin_consistent_remove; auto.
	    - intros ev σ' c' Hstep.
	      inversion Hstep; subst.
	      pose proof (Hpool (te_tid ev)) as Hpoolt.
	      rewrite Hfind in Hpoolt.
	      inversion Hpoolt; subst; try discriminate; try congruence.
	      + inversion Hstep0; subst; [
	          pose proof (inj_pair2 _ _ _ _ _ H5) as Hprog;
	          destruct op as [op1|op2]
	          | pose proof (inj_pair2 _ _ _ _ _ H5) as Hprog;
	            destruct op as [op1|op2] ].
	        * edestruct (@lift_left_vis_inv (li_sig TS.E) (li_sig EX.E)
	            _ p op1 k0) as [k' [Hp Hk]]; [symmetry; exact Hprog|].
	          subst p.
	          destruct b as [b'|]; simpl in H6; try discriminate.
	          simpl in H.
	          simpl in H2.
	          simpl in Hstep1.
	          destruct σ' as [σ1' σ2']; destruct Hstep1 as [Hstep1 Hσ2]; subst σ2'.
	          assert (@Semantics.ustep (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)
	            (Build_ThreadEvent t0 (InvEv op1)) σ1 c1 σ1'
	            (TMap.add t0
	              (Semantics.Build_ThreadState f0 (Vis op1 k') (Some op1)) c1)) as Huistep1.
	          { eapply (@Semantics.UStep (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)).
	            - symmetry. exact H.
	            - eapply (@Semantics.ts_inv (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)).
	              exact Hstep1.
	            - reflexivity.
	          }
	          destruct (Hustep1 _ _ _ Huistep1) as [ρ1' [π1' [Hsteps1 Hsim1']]].
	          edestruct (tensor_poss_steps_left ρ1 ρ1' ρ2 π π1 π1' π2)
	            as [π' [Hsteps' Hlin']]; eauto.
	          pose proof (poss_steps_pool_lin_consistent c1 ρ1 ρ1' π1 π1'
	            Hcons1 Hsteps1) as Hcons1'.
	          assert (TMap.find t0 c1 <>
	            @None (@Semantics.ThreadState (li_sig TS.E) (li_sig TS.F))) as Hc1some.
	          { intro Hnone. simpl in Hnone. congruence. }
	          simpl in Hc1some.
	          exists (ρ1', ρ2), π'. split; [exact Hsteps'|].
	          eapply (IH σ1' σ2
	            (TMap.add t0
	              {|
	                Semantics.ts_op := inl f0;
	                Semantics.ts_prog := inl op1 >= x => k0 x;
	                Semantics.ts_pend := Some (inl op1)
	              |} c)
	            (TMap.add t0
	              {|
	                Semantics.ts_op := f0;
	                Semantics.ts_prog := op1 >= x => k' x;
	                Semantics.ts_pend := Some op1
	              |} c1)
	            c2 ρ1' ρ2 π' π1' π2).
	          -- intro t.
	             destruct (PositiveMap.E.eq_dec t t0); subst.
	             ++ rewrite !PositiveMap.gss.
	                simpl.
	                rewrite <- H2.
		                refine (eq_ind_r
		                  (fun q =>
		                    tensor_threadstate
		                      (Some
		                        {|
		                          Semantics.ts_op := inl f0;
		                          Semantics.ts_prog := q;
		                          Semantics.ts_pend := Some (inl op1)
		                        |})
		                      (Some
		                        {|
		                          Semantics.ts_op := f0;
		                          Semantics.ts_prog := op1 >= x => k' x;
		                          Semantics.ts_pend := Some op1
		                        |})
		                      None)
		                  _ Hprog).
		                change (Some (inl op1)) with
		                  (@map_option_left (Sig.op (li_sig TS.E)) (Sig.op (li_sig EX.E)) (Some op1)).
		                constructor.
	             ++ rewrite !PositiveMap.gso by auto. apply Hpool.
	          -- exact Hlin'.
	          -- exact Hsim1'.
	          -- eapply pool_lin_consistent_update_pool; [exact Hcons1'|exact Hc1some].
	          -- exact Hsim2.
	          -- exact Hcons2.
	        * exfalso.
	          symmetry in Hprog. exact (lift_left_vis_right_absurd p op2 k0 Hprog).
	        * edestruct (@lift_left_vis_inv (li_sig TS.E) (li_sig EX.E)
	            _ p op1 k0) as [k' [Hp Hk]]; [symmetry; exact Hprog|].
	          subst p.
	          destruct b as [b'|]; simpl in H6; try discriminate.
	          inversion H6; subst b'. clear H6.
	          simpl in H.
	          simpl in H2.
	          simpl in Hstep1.
	          destruct σ' as [σ1' σ2']; destruct Hstep1 as [Hstep1 Hσ2]; subst σ2'.
	          assert (@Semantics.ustep (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)
	            (Build_ThreadEvent t0 (ResEv op1 ret)) σ1 c1 σ1'
	            (TMap.add t0
	              (Semantics.Build_ThreadState f0 (k' ret) None) c1)) as Huistep1.
	          { eapply (@Semantics.UStep (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)).
	            - symmetry. exact H.
	            - eapply (@Semantics.ts_res (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)).
	              exact Hstep1.
	            - reflexivity.
	          }
	          destruct (Hustep1 _ _ _ Huistep1) as [ρ1' [π1' [Hsteps1 Hsim1']]].
	          edestruct (tensor_poss_steps_left ρ1 ρ1' ρ2 π π1 π1' π2)
	            as [π' [Hsteps' Hlin']]; eauto.
	          pose proof (poss_steps_pool_lin_consistent c1 ρ1 ρ1' π1 π1'
	            Hcons1 Hsteps1) as Hcons1'.
	          assert (TMap.find t0 c1 <>
	            @None (@Semantics.ThreadState (li_sig TS.E) (li_sig TS.F))) as Hc1some.
	          { intro Hnone. simpl in Hnone. congruence. }
	          simpl in Hc1some.
	          exists (ρ1', ρ2), π'. split; [exact Hsteps'|].
	          eapply (IH σ1' σ2
	            (TMap.add t0
	              {|
	                Semantics.ts_op := inl f0;
	                Semantics.ts_prog := k0 ret;
	                Semantics.ts_pend := None
	              |} c)
	            (TMap.add t0
	              {|
	                Semantics.ts_op := f0;
	                Semantics.ts_prog := k' ret;
	                Semantics.ts_pend := None
	              |} c1)
	            c2 ρ1' ρ2 π' π1' π2).
	          -- intro t.
	             destruct (PositiveMap.E.eq_dec t t0); subst.
	             ++ rewrite !PositiveMap.gss.
	                simpl.
	                rewrite <- H2.
	                refine (eq_ind_r
	                  (fun q =>
	                    tensor_threadstate
	                      (Some
	                        {|
	                          Semantics.ts_op := inl f0;
	                          Semantics.ts_prog := q;
	                          Semantics.ts_pend := None
	                        |})
	                      (Some
	                        {|
	                          Semantics.ts_op := f0;
	                          Semantics.ts_prog := k' ret;
	                          Semantics.ts_pend := None
	                        |})
	                      None)
	                  _ (Hk ret)).
	                change (tensor_threadstate
	                  (Some
	                    {|
	                      Semantics.ts_op := inl f0;
	                      Semantics.ts_prog := lift_left (k' ret);
	                      Semantics.ts_pend :=
	                        map_option_left (@None (Sig.op (li_sig TS.E)))
	                    |})
	                  (Some
	                    {|
	                      Semantics.ts_op := f0;
	                      Semantics.ts_prog := k' ret;
	                      Semantics.ts_pend := @None (Sig.op (li_sig TS.E))
	                    |})
	                  None).
	                constructor.
	             ++ rewrite !PositiveMap.gso by auto. apply Hpool.
	          -- exact Hlin'.
	          -- exact Hsim1'.
	          -- eapply pool_lin_consistent_update_pool; [exact Hcons1'|exact Hc1some].
	          -- exact Hsim2.
	          -- exact Hcons2.
	        * exfalso.
	          symmetry in Hprog. exact (lift_left_vis_right_absurd p op2 k0 Hprog).
		      + inversion Hstep0; subst; [
		          pose proof (inj_pair2 _ _ _ _ _ H5) as Hprog;
		          destruct op as [op1|op2]
		          | pose proof (inj_pair2 _ _ _ _ _ H5) as Hprog;
		            destruct op as [op1|op2] ].
		        * exfalso.
		          symmetry in Hprog. exact (lift_right_vis_left_absurd p op1 k0 Hprog).
		        * edestruct (@lift_right_vis_inv (li_sig TS.E) (li_sig EX.E)
		            _ p op2 k0) as [k' [Hp Hk]]; [symmetry; exact Hprog|].
		          subst p.
		          destruct b as [b'|]; simpl in H6; try discriminate.
		          simpl in H.
		          simpl in H2.
		          simpl in Hstep1.
		          destruct σ' as [σ1' σ2']; destruct Hstep1 as [Hstep2 Hσ1]; subst σ1'.
		          assert (@Semantics.ustep (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)
		            (Build_ThreadEvent t0 (InvEv op2)) σ2 c2 σ2'
		            (TMap.add t0
		              (Semantics.Build_ThreadState f0 (Vis op2 k') (Some op2)) c2)) as Huistep2.
		          { eapply (@Semantics.UStep (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)).
		            - symmetry. exact H2.
		            - eapply (@Semantics.ts_inv (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)).
		              exact Hstep2.
		            - reflexivity.
		          }
		          destruct (Hustep2 _ _ _ Huistep2) as [ρ2' [π2' [Hsteps2 Hsim2']]].
		          edestruct (tensor_poss_steps_right ρ1 ρ2 ρ2' π π1 π2 π2')
		            as [π' [Hsteps' Hlin']]; eauto.
		          pose proof (poss_steps_pool_lin_consistent c2 ρ2 ρ2' π2 π2'
		            Hcons2 Hsteps2) as Hcons2'.
		          assert (TMap.find t0 c2 <>
		            @None (@Semantics.ThreadState (li_sig EX.E) (li_sig EX.F))) as Hc2some.
		          { intro Hnone. simpl in Hnone. congruence. }
		          simpl in Hc2some.
		          exists (ρ1, ρ2'), π'. split; [exact Hsteps'|].
		          eapply (IH σ1 σ2'
		            (TMap.add t0
		              {|
		                Semantics.ts_op := inr f0;
		                Semantics.ts_prog := inr op2 >= x => k0 x;
		                Semantics.ts_pend := Some (inr op2)
		              |} c)
		            c1
		            (TMap.add t0
		              {|
		                Semantics.ts_op := f0;
		                Semantics.ts_prog := op2 >= x => k' x;
		                Semantics.ts_pend := Some op2
		              |} c2)
		            ρ1 ρ2' π' π1 π2').
		          -- intro t.
		             destruct (PositiveMap.E.eq_dec t t0); subst.
		             ++ rewrite !PositiveMap.gss.
		                simpl.
		                rewrite <- H.
		                refine (eq_ind_r
		                  (fun q =>
		                    tensor_threadstate
		                      (Some
		                        {|
		                          Semantics.ts_op := inr f0;
		                          Semantics.ts_prog := q;
		                          Semantics.ts_pend := Some (inr op2)
		                        |})
		                      None
		                      (Some
		                        {|
		                          Semantics.ts_op := f0;
		                          Semantics.ts_prog := op2 >= x => k' x;
		                          Semantics.ts_pend := Some op2
		                        |}))
		                  _ Hprog).
		                change (Some (inr op2)) with
		                  (@map_option_right (Sig.op (li_sig TS.E)) (Sig.op (li_sig EX.E)) (Some op2)).
		                constructor.
		             ++ rewrite !PositiveMap.gso by auto. apply Hpool.
		          -- exact Hlin'.
		          -- exact Hsim1.
		          -- exact Hcons1.
		          -- exact Hsim2'.
		          -- eapply pool_lin_consistent_update_pool; [exact Hcons2'|exact Hc2some].
		        * exfalso.
		          symmetry in Hprog. exact (lift_right_vis_left_absurd p op1 k0 Hprog).
		        * edestruct (@lift_right_vis_inv (li_sig TS.E) (li_sig EX.E)
		            _ p op2 k0) as [k' [Hp Hk]]; [symmetry; exact Hprog|].
		          subst p.
		          destruct b as [b'|]; simpl in H6; try discriminate.
		          inversion H6; subst b'. clear H6.
		          simpl in H.
		          simpl in H2.
		          simpl in Hstep1.
		          destruct σ' as [σ1' σ2']; destruct Hstep1 as [Hstep2 Hσ1]; subst σ1'.
		          assert (@Semantics.ustep (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)
		            (Build_ThreadEvent t0 (ResEv op2 ret)) σ2 c2 σ2'
		            (TMap.add t0
		              (Semantics.Build_ThreadState f0 (k' ret) None) c2)) as Huistep2.
		          { eapply (@Semantics.UStep (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)).
		            - symmetry. exact H2.
		            - eapply (@Semantics.ts_res (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)).
		              exact Hstep2.
		            - reflexivity.
		          }
		          destruct (Hustep2 _ _ _ Huistep2) as [ρ2' [π2' [Hsteps2 Hsim2']]].
		          edestruct (tensor_poss_steps_right ρ1 ρ2 ρ2' π π1 π2 π2')
		            as [π' [Hsteps' Hlin']]; eauto.
		          pose proof (poss_steps_pool_lin_consistent c2 ρ2 ρ2' π2 π2'
		            Hcons2 Hsteps2) as Hcons2'.
		          assert (TMap.find t0 c2 <>
		            @None (@Semantics.ThreadState (li_sig EX.E) (li_sig EX.F))) as Hc2some.
		          { intro Hnone. simpl in Hnone. congruence. }
		          simpl in Hc2some.
		          exists (ρ1, ρ2'), π'. split; [exact Hsteps'|].
		          eapply (IH σ1 σ2'
		            (TMap.add t0
		              {|
		                Semantics.ts_op := inr f0;
		                Semantics.ts_prog := k0 ret;
		                Semantics.ts_pend := None
		              |} c)
		            c1
		            (TMap.add t0
		              {|
		                Semantics.ts_op := f0;
		                Semantics.ts_prog := k' ret;
		                Semantics.ts_pend := None
		              |} c2)
		            ρ1 ρ2' π' π1 π2').
		          -- intro t.
		             destruct (PositiveMap.E.eq_dec t t0); subst.
		             ++ rewrite !PositiveMap.gss.
		                simpl.
		                rewrite <- H.
		                refine (eq_ind_r
		                  (fun q =>
		                    tensor_threadstate
		                      (Some
		                        {|
		                          Semantics.ts_op := inr f0;
		                          Semantics.ts_prog := q;
		                          Semantics.ts_pend := None
		                        |})
		                      None
		                      (Some
		                        {|
		                          Semantics.ts_op := f0;
		                          Semantics.ts_prog := k' ret;
		                          Semantics.ts_pend := None
		                        |}))
		                  _ (Hk ret)).
		                change (tensor_threadstate
		                  (Some
		                    {|
		                      Semantics.ts_op := inr f0;
		                      Semantics.ts_prog := lift_right (k' ret);
		                      Semantics.ts_pend :=
		                        map_option_right (@None (Sig.op (li_sig EX.E)))
		                    |})
		                  None
		                  (Some
		                    {|
		                      Semantics.ts_op := f0;
		                      Semantics.ts_prog := k' ret;
		                      Semantics.ts_pend := @None (Sig.op (li_sig EX.E))
		                    |})).
		                constructor.
		             ++ rewrite !PositiveMap.gso by auto. apply Hpool.
		          -- exact Hlin'.
		          -- exact Hsim1.
		          -- exact Hcons1.
		          -- exact Hsim2'.
		          -- eapply pool_lin_consistent_update_pool; [exact Hcons2'|exact Hc2some].
    - destruct Hlinstep1 as [ρ1' [π1' [Hsteps Hsim1']]].
      edestruct tensor_poss_steps_left as [π' [Hsteps' Hlin']]; eauto.
      pose proof (poss_steps_pool_lin_consistent c1 ρ1 ρ1' π1 π1'
        Hcons1 Hsteps) as Hcons1'.
      exists (ρ1', ρ2), π'. split; [exact Hsteps'|].
      eapply IH.
      + exact Hpool.
      + exact Hlin'.
      + exact Hsim1'.
      + exact Hcons1'.
      + exact Hsim2.
      + exact Hcons2.
    - intros t c' Hstep.
      inversion Hstep; subst.
      pose proof (Hpool t) as Hpoolt.
      rewrite Hfind in Hpoolt.
      inversion Hpoolt; subst; try discriminate; try congruence.
      + inversion Hstep0; subst.
        pose proof (inj_pair2 _ _ _ _ _ H3) as Hprog.
        symmetry in Hprog.
        edestruct (@lift_left_tau_inv (li_sig TS.E) (li_sig EX.E) _ p p1)
          as [p' [Hp Heq]]; [exact Hprog|].
        subst.
        assert (@Semantics.taustep (li_sig TS.E) (li_sig TS.F)
          t c1 (TMap.add t (Semantics.Build_ThreadState f p' b) c1)) as Htau_step1.
        { eapply (@Semantics.TauStep (li_sig TS.E) (li_sig TS.F)
            t c1 (TMap.add t (Semantics.Build_ThreadState f p' b) c1)
            (Semantics.Build_ThreadState f (Tau p') b)
            (Semantics.Build_ThreadState f p' b)).
          - symmetry. eassumption.
          - exact (@Semantics.ts_tau (li_sig TS.E) (li_sig TS.F) f p' b).
          - reflexivity.
        }
        specialize (Htau1 _ _ Htau_step1).
        eapply IH.
        * eapply tensor_threadpool_add_left; [exact Hpool|symmetry; eassumption].
        * exact Hlin.
        * exact Htau1.
        * intros t' Hnone.
          destruct (PositiveMap.E.eq_dec t' t); subst.
          -- rewrite PositiveMap.gss in Hnone. discriminate.
          -- rewrite PositiveMap.gso in Hnone by auto.
             apply Hcons1. exact Hnone.
        * exact Hsim2.
        * exact Hcons2.
      + inversion Hstep0; subst.
        pose proof (inj_pair2 _ _ _ _ _ H3) as Hprog.
        symmetry in Hprog.
        edestruct (@lift_right_tau_inv (li_sig TS.E) (li_sig EX.E) _ p p1)
          as [p' [Hp Heq]]; [exact Hprog|].
        subst.
        assert (@Semantics.taustep (li_sig EX.E) (li_sig EX.F)
          t c2 (TMap.add t (Semantics.Build_ThreadState f p' b) c2)) as Htau_step2.
        { eapply (@Semantics.TauStep (li_sig EX.E) (li_sig EX.F)
            t c2 (TMap.add t (Semantics.Build_ThreadState f p' b) c2)
            (Semantics.Build_ThreadState f (Tau p') b)
            (Semantics.Build_ThreadState f p' b)).
          - symmetry. eassumption.
          - exact (@Semantics.ts_tau (li_sig EX.E) (li_sig EX.F) f p' b).
          - reflexivity.
        }
        specialize (Htau2 _ _ Htau_step2).
        eapply IH.
        * eapply tensor_threadpool_add_right; [exact Hpool|symmetry; eassumption].
        * exact Hlin.
        * exact Hsim1.
        * exact Hcons1.
        * exact Htau2.
        * intros t' Hnone.
          destruct (PositiveMap.E.eq_dec t' t); subst.
          -- rewrite PositiveMap.gss in Hnone. discriminate.
          -- rewrite PositiveMap.gso in Hnone by auto.
             apply Hcons2. exact Hnone.
    - intros ev Herr.
      inversion Herr; subst.
      pose proof (Hpool (te_tid ev)) as Hpoolt.
      rewrite Hfind in Hpoolt.
      inversion Hpoolt; subst; try discriminate; try congruence.
      + inversion Herror; subst.
        pose proof (inj_pair2 _ _ _ _ _ H5) as Hprog.
        destruct op as [op1|op2].
	        * edestruct (@lift_left_vis_inv (li_sig TS.E) (li_sig EX.E)
	            _ p op1 k0) as [k' [Hp Hk]]; [symmetry; exact Hprog|].
	          subst.
	          destruct b as [b'|]; simpl in H6; try discriminate.
	          apply (Hnoerr1 (Build_ThreadEvent t0 (InvEv op1))).
	          eapply (@Semantics.UError (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)).
	          -- symmetry. eassumption.
	          -- eapply (@Semantics.ts_err (li_sig TS.E) (li_sig TS.F) (li_lts TS.E)).
	             simpl in Herror0. exact Herror0.
        * exfalso.
          symmetry in Hprog. exact (lift_left_vis_right_absurd p op2 k0 Hprog).
      + inversion Herror; subst.
        pose proof (inj_pair2 _ _ _ _ _ H5) as Hprog.
        destruct op as [op1|op2].
        * exfalso.
          symmetry in Hprog. exact (lift_right_vis_left_absurd p op1 k0 Hprog).
	        * edestruct (@lift_right_vis_inv (li_sig TS.E) (li_sig EX.E)
	            _ p op2 k0) as [k' [Hp Hk]]; [symmetry; exact Hprog|].
	          subst.
	          destruct b as [b'|]; simpl in H6; try discriminate.
	          apply (Hnoerr2 (Build_ThreadEvent t0 (InvEv op2))).
	          eapply (@Semantics.UError (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)).
	          -- symmetry. eassumption.
	          -- eapply (@Semantics.ts_err (li_sig EX.E) (li_sig EX.F) (li_lts EX.E)).
	             simpl in Herror0. exact Herror0.
	  Qed.

  Definition push_impl (v : A) (t : tid) : Prog (li_sig Fmid) unit :=
    Do {
      inr (ExchSpec.exch (Some v)) >= other =>
      match other with
      | Some None => Ret (inr tt)
      | _ =>
        inl (TryStackSpec.push v) >= succ =>
        Ret (match succ with | FAIL => inl tt | _ => inr tt end)
      end
    } Loop.

  Definition pop_impl (t : tid) : Prog (li_sig Fmid) (option A) :=
    Do {
      inr (ExchSpec.exch None) >= other =>
      match other with
      | Some (Some v) => Ret (inr (Some v))
      | _ =>
        inl TryStackSpec.pop >= succ =>
        Ret (match succ with | FAIL => inl tt | OK v => inr v end)
      end
    } Loop.

  Definition ebstack_impl : ModuleImpl (li_sig Fmid) (li_sig F) :=
    fun m t =>
      match m with
      | StackSpec.push v => push_impl v t
      | StackSpec.pop => pop_impl t
      end.

  Definition mid_assertion :=
    @Assertion (@ProofState (li_sig Fmid) (li_sig F) (li_lts Fmid) (li_lts F)).
  Definition mid_rg_relation :=
    @RGRelation (li_sig Fmid) (li_sig F) (li_lts Fmid) (li_lts F).

  Definition mid_stack_state (s : State (li_lts Fmid)) : list A :=
    state (fst s).

  Definition mid_exch_state (s : State (li_lts Fmid)) :
    @EExchState (option A) :=
    snd s.

  Definition wait_lin (t : tid) (v : option A)
    (π : tmap Semantics.LinState) : Prop :=
    match v with
    | Some x => TMap.find t π = Some (Semantics.Semantics.ls_inv (StackSpec.push x))
    | None => TMap.find t π = Some (Semantics.Semantics.ls_inv StackSpec.pop)
    end.

  Definition done_lin (t : tid) (v other : option A)
    (π : tmap Semantics.LinState) : Prop :=
    match v, other with
    | Some x, None =>
        TMap.find t π = Some (Semantics.Semantics.ls_linr (StackSpec.push x) tt)
    | None, Some x =>
        TMap.find t π = Some (Semantics.Semantics.ls_linr StackSpec.pop (Some x))
    | _, _ => False
    end.

  Definition paired_lin
    (t1 : tid) (v1 : option A) (t2 : tid) (v2 : option A)
    (π : tmap Semantics.LinState) : Prop :=
    match v1, v2 with
    | Some _, None | None, Some _ =>
        done_lin t1 v1 v2 π /\ done_lin t2 v2 v1 π
    | Some _, Some _ | None, None =>
        wait_lin t1 v1 π /\ wait_lin t2 v2 π
    end.

  Definition accepted_lin
    (t1 : tid) (v1 : option A) (t2 : tid) (v2 : option A)
    (π : tmap Semantics.LinState) : Prop :=
    match v1, v2 with
    | Some _, None | None, Some _ => done_lin t2 v2 v1 π
    | Some _, Some _ | None, None => wait_lin t2 v2 π
    end.

  Definition exch_ok (xs : @EExchState (option A))
    (π : tmap Semantics.LinState) : Prop :=
    match xs with
    | ExSIdle => True
    | ExSOffered t v => wait_lin t v π
    | ExSPaired t1 v1 t2 v2 => paired_lin t1 v1 t2 v2 π
    | ExSAccepted t1 v1 t2 v2 => accepted_lin t1 v1 t2 v2 π
    end.

  Definition exch_distinct (xs : @EExchState (option A)) : Prop :=
    match xs with
    | ExSPaired t1 _ t2 _ | ExSAccepted t1 _ t2 _ => t1 <> t2
    | _ => True
    end.

  Definition I : mid_assertion :=
    fun s =>
      ρ s = Idle (mid_stack_state (σ s)) /\
      exch_ok (mid_exch_state (σ s)) (π s) /\
      exch_distinct (mid_exch_state (σ s)).

  Definition no_exch_by (t : tid) (xs : @EExchState (option A)) : Prop :=
    match xs with
    | ExSIdle => True
    | ExSOffered t1 _ => t <> t1
    | ExSPaired t1 _ t2 _ => t <> t1 /\ t <> t2
    | ExSAccepted _ _ t2 _ => t <> t2
    end.

  Definition NoExchBy (t : tid) : mid_assertion :=
    fun s => no_exch_by t (mid_exch_state (σ s)).

  Definition Active (t : tid) (m : Sig.op (li_sig F)) : mid_assertion :=
    ALin t (Semantics.Semantics.ls_inv m) //\\ NoExchBy t.

  Definition Done (t : tid) (m : Sig.op (li_sig F)) : mid_assertion :=
    fun s => exists ret, ALin t (Semantics.Semantics.ls_linr m ret) s.

  Definition Live (t : tid) (m : Sig.op (li_sig F)) : mid_assertion :=
    ALin t (Semantics.Semantics.ls_inv m) \\// Done t m.

  Definition R_pres t : mid_rg_relation :=
    fun s1 s2 =>
      (TMap.find t (π s1) = None <-> TMap.find t (π s2) = None) /\
      (forall m, Active t m s1 -> Active t m s2) /\
      (forall m ret, ALin t (Semantics.Semantics.ls_linr m ret) s1 ->
        ALin t (Semantics.Semantics.ls_linr m ret) s2) /\
      (forall m, Live t m s1 -> Live t m s2) /\
      (NoExchBy t s1 -> NoExchBy t s2).

  Definition G t : mid_rg_relation :=
    fun s1 s2 =>
      I s2 /\
      (forall t', t <> t' -> R_pres t' s1 s2).

  Definition R t : mid_rg_relation :=
    R_pres t.

  Lemma Istable {t} : Stable (R t) I I.
  Proof. unfold Stable. apply ConjRightImpl, ImplRefl. Qed.

  Lemma Activestable {t m}: Stable (R t) I (Active t m).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hact [_ [Hpres _]]]] ?].
    eauto.
  Qed.

  Lemma Donestable {t m}: Stable (R t) I (Done t m).
  Proof.
    unfold Stable, R, R_pres, Done.
    intros ? [[? [[ret Hdone] [_ [_ [Hpres _]]]]] ?].
    exists ret. eauto.
  Qed.

  Lemma ALinRetstable {t m ret}:
    Stable (R t) I (ALin t (Semantics.Semantics.ls_linr m ret)).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hdone [_ [_ [Hpres _]]]]] ?].
    eauto.
  Qed.

  Lemma Livestable {t m}: Stable (R t) I (Live t m).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hlive [_ [_ [_ [Hpres _]]]]]] ?].
    eauto.
  Qed.

  Lemma NoExchBystable {t}: Stable (R t) I (NoExchBy t).
  Proof.
    unfold Stable, R, R_pres.
    intros ? [[? [Hno [_ [_ [_ [_ Hpres]]]]]] ?].
    eauto.
  Qed.

  Create HintDb ebstack_mid_stable.
  #[local] Hint Resolve Istable Activestable Donestable ALinRetstable
    Livestable NoExchBystable : ebstack_mid_stable.

  Lemma wait_lin_add_fresh t t' v f π :
    TMap.find t π = None ->
    wait_lin t' v π ->
    wait_lin t' v (TMap.add t (Semantics.Semantics.ls_inv f) π).
  Proof.
    intros Hnone Hwait.
    destruct v; simpl in *;
    destruct (PositiveMap.E.eq_dec t t'); subst.
    - rewrite Hnone in Hwait. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hwait.
    - rewrite Hnone in Hwait. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hwait.
  Qed.

  Lemma done_lin_add_fresh t t' v other f π :
    TMap.find t π = None ->
    done_lin t' v other π ->
    done_lin t' v other (TMap.add t (Semantics.Semantics.ls_inv f) π).
  Proof.
    intros Hnone Hdone.
    destruct v as [v|], other as [other|]; simpl in *; try contradiction;
    destruct (PositiveMap.E.eq_dec t t'); subst.
    - rewrite Hnone in Hdone. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hdone.
    - rewrite Hnone in Hdone. discriminate.
    - rewrite PositiveMap.gso by auto. exact Hdone.
  Qed.

  Lemma paired_lin_add_fresh t t1 v1 t2 v2 f π :
    TMap.find t π = None ->
    paired_lin t1 v1 t2 v2 π ->
    paired_lin t1 v1 t2 v2 (TMap.add t (Semantics.Semantics.ls_inv f) π).
  Proof.
    destruct v1 as [a|], v2 as [b|]; simpl in *; intros Hnone [H1 H2]; split.
    - change (wait_lin t1 (Some a) (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (wait_lin t2 (Some b) (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (done_lin t1 (Some a) None (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t2 None (Some a) (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t1 None (Some b) (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t2 (Some b) None (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (wait_lin t1 None (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (wait_lin t2 None (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
  Qed.

  Lemma accepted_lin_add_fresh t t1 v1 t2 v2 f π :
    TMap.find t π = None ->
    accepted_lin t1 v1 t2 v2 π ->
    accepted_lin t1 v1 t2 v2 (TMap.add t (Semantics.Semantics.ls_inv f) π).
  Proof.
    destruct v1 as [a|], v2 as [b|]; simpl in *; intros Hnone H.
    - change (wait_lin t2 (Some b) (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
    - change (done_lin t2 None (Some a) (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (done_lin t2 (Some b) None (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply done_lin_add_fresh; eauto.
    - change (wait_lin t2 None (TMap.add t (Semantics.Semantics.ls_inv f) π)).
      eapply wait_lin_add_fresh; eauto.
  Qed.

  Lemma IGinv : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.Semantics.ls_inv f).
  Proof.
    unfold I, mid_stack_state, mid_exch_state, ALin, Ginv, LiftRelation_π.
    intros t f s [s' [HI [? [? [Hnone Hπ]]]]].
    destruct s, s'; simpl in *; subst.
    split.
    - destruct HI as [Hr [Hex Hdist]]. split; [exact Hr|].
      split.
      2:{ destruct σ0 as [ts xs]; simpl in *; exact Hdist. }
      destruct σ0 as [ts xs]; simpl in *.
      destruct xs as [ot ov|pt1 pv1 pt2 pv2|at1 av1 at2 av2|]; simpl in *; auto.
      + eapply wait_lin_add_fresh; eauto.
      + eapply paired_lin_add_fresh; eauto.
      + eapply accepted_lin_add_fresh; eauto.
    - simpl. rewrite PositiveMap.gss. auto.
  Qed.

  Lemma exch_ok_no_exch_add_fresh t xs π :
    TMap.find t π = None ->
    exch_ok xs π ->
    no_exch_by t xs.
  Proof.
    intros Hnone Hex.
    destruct xs as [t1 v1|t1 v1 t2 v2|t1 v1 t2 v2|]; simpl in *; auto.
    - destruct v1; simpl in *; intros Heq; subst; rewrite Hnone in Hex; discriminate.
    - destruct v1 as [a|], v2 as [b|]; simpl in *; destruct Hex as [H1 H2]; split;
      intros Heq; subst; rewrite Hnone in *; discriminate.
    - destruct v1 as [a|], v2 as [b|]; simpl in *;
      intros Heq; subst; rewrite Hnone in Hex; discriminate.
  Qed.

  Lemma IGinvActive : forall t f, ⊨ Ginv t f ⊚ I ==>> I //\\ Active t f.
  Proof.
    unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy, Ginv, LiftRelation_π.
    intros t f s [s' [HI [? [? [Hnone Hπ]]]]].
    destruct s, s'; simpl in *; subst.
    destruct HI as [Hr [Hex Hdist]].
    split.
    - split; [exact Hr|].
      split.
      2:{ destruct σ0 as [ts xs]; simpl in *; exact Hdist. }
      destruct σ0 as [ts xs]; simpl in *.
      destruct xs as [ot ov|pt1 pv1 pt2 pv2|at1 av1 at2 av2|]; simpl in *; auto.
      + eapply wait_lin_add_fresh; eauto.
      + eapply paired_lin_add_fresh; eauto.
      + eapply accepted_lin_add_fresh; eauto.
    - split.
      + simpl. rewrite PositiveMap.gss. auto.
      + simpl. eapply exch_ok_no_exch_add_fresh; eauto.
  Qed.

  Lemma exch_ok_remove_no_exch t xs π :
    no_exch_by t xs ->
    exch_ok xs π ->
    exch_ok xs (TMap.remove t π).
  Proof.
    intros Hno Hex.
    destruct xs as [t1 v1|t1 v1 t2 v2|t1 v1 t2 v2|]; simpl in *; auto.
    - destruct v1; simpl in *; rewrite PositiveMap.gro by auto; exact Hex.
    - destruct v1 as [a|], v2 as [b|]; simpl in *; destruct Hex as [H1 H2]; destruct Hno as [Hn1 Hn2]; split;
      rewrite PositiveMap.gro by auto; assumption.
    - destruct v1 as [a|], v2 as [b|]; simpl in *;
      rewrite PositiveMap.gro by auto; assumption.
  Qed.

  Lemma exch_ok_add_add_no_exch t xs π ls1 ls2 :
    no_exch_by t xs ->
    exch_ok xs π ->
    exch_ok xs (TMap.add t ls2 (TMap.add t ls1 π)).
  Proof.
    intros Hno Hex.
    destruct xs as [t1 v1|t1 v1 t2 v2|t1 v1 t2 v2|]; simpl in *; auto.
    - destruct v1; simpl in *; repeat (rewrite PositiveMap.gso by auto); exact Hex.
    - destruct v1 as [a|], v2 as [b|]; simpl in *; destruct Hex as [H1 H2]; destruct Hno as [Hn1 Hn2]; split;
      repeat (rewrite PositiveMap.gso by auto); assumption.
    - destruct v1 as [a|], v2 as [b|]; simpl in *;
      repeat (rewrite PositiveMap.gso by auto); assumption.
  Qed.

  Lemma IGretNoExch : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ (ALin t (Semantics.Semantics.ls_linr f ret) //\\ NoExchBy t)) ==>> I.
  Proof.
    unfold Gret, LiftRelation_π.
    intros t f ret s [s' [Hpre [? [? [Hfind Hπ]]]]].
    destruct Hpre as [HI [Hlin Hno]].
    unfold I, mid_stack_state, mid_exch_state, ALin, NoExchBy in *.
    destruct s, s'; simpl in *; subst.
    destruct HI as [Hr [Hex Hdist]]. split; [exact Hr|].
    destruct σ0 as [ts xs]; simpl in *.
    split.
    - eapply exch_ok_remove_no_exch; eauto.
    - exact Hdist.
  Qed.

  Lemma no_error t (m : Sig.op (li_sig Fmid)) (P : mid_assertion) :
    ⊨ P ==>> ANoError {| te_tid := t; te_ev := InvEv m |}.
  Proof.
    unfold ANoError.
    intros [σ0 ρ0 π0] _ Herr.
    destruct σ0 as [ts xs], m as [m|m]; simpl in *; contradiction.
  Qed.

  Lemma R_pres_ginv_other t t' f s1 s2 :
    t <> t' ->
    Ginv t f s1 s2 ->
    R_pres t' s1 s2.
  Proof.
    intros Hneq Hinv.
    assert (Hneq' : t' <> t) by congruence.
    unfold Ginv, LiftRelation_π in Hinv.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *.
    destruct Hinv as [Hσ [Hρ [Hfind Hπ]]]. subst.
    unfold R_pres, Active, NoExchBy, Live, Done, ALin; simpl.
    split.
    - split; intro H.
      + rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.Semantics.ls_inv f) π1 Hneq'). exact H.
      + rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.Semantics.ls_inv f) π1 Hneq') in H. exact H.
    - split.
      + intros m [Hlin Hno]. simpl in *. split.
        * change (TMap.find t' (TMap.add t (Semantics.Semantics.ls_inv f) π1) =
            Some (Semantics.Semantics.ls_inv m)).
          rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.Semantics.ls_inv f) π1 Hneq').
          exact Hlin.
        * exact Hno.
      + split.
        * intros m ret H. simpl in *.
          change (TMap.find t' (TMap.add t (Semantics.Semantics.ls_inv f) π1) =
            Some (Semantics.Semantics.ls_linr m ret)).
          rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.Semantics.ls_inv f) π1 Hneq').
          exact H.
        * split.
          -- intros m [Hlin | [ret Hret]]; simpl in *; simpl.
             ++ left.
                change (TMap.find t' (TMap.add t (Semantics.Semantics.ls_inv f) π1) =
                  Some (Semantics.Semantics.ls_inv m)).
                rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.Semantics.ls_inv f) π1 Hneq').
                exact Hlin.
             ++ right. exists ret.
                change (TMap.find t' (TMap.add t (Semantics.Semantics.ls_inv f) π1) =
                  Some (Semantics.Semantics.ls_linr m ret)).
                rewrite (@PositiveMap.gso Semantics.LinState t' t (Semantics.Semantics.ls_inv f) π1 Hneq').
                exact Hret.
          -- intros H. exact H.
  Qed.

  Lemma R_pres_gret_other t t' f ret s1 s2 :
    t <> t' ->
    Gret t f ret s1 s2 ->
    R_pres t' s1 s2.
  Proof.
    intros Hneq Hret.
    assert (Hneq' : t' <> t) by congruence.
    unfold Gret, LiftRelation_π in Hret.
    destruct s1 as [σ1 ρ1 π1], s2 as [σ2 ρ2 π2]; simpl in *.
    destruct Hret as [Hσ [Hρ [Hfind Hπ]]]. subst.
    unfold R_pres, Active, NoExchBy, Live, Done, ALin; simpl.
    split.
    - split; intro H.
      + rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq'). exact H.
      + rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq') in H. exact H.
    - split.
      + intros m [Hlin Hno]. simpl in *. split.
        * change (TMap.find t' (TMap.remove t π1) =
            Some (Semantics.Semantics.ls_inv m)).
          rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
          exact Hlin.
        * exact Hno.
      + split.
        * intros m r H. simpl in *.
          change (TMap.find t' (TMap.remove t π1) =
            Some (Semantics.Semantics.ls_linr m r)).
          rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
          exact H.
        * split.
          -- intros m [Hlin | [r Hr]]; simpl in *; simpl.
             ++ left.
                change (TMap.find t' (TMap.remove t π1) =
                  Some (Semantics.Semantics.ls_inv m)).
                rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
                exact Hlin.
             ++ right. exists r.
                change (TMap.find t' (TMap.remove t π1) =
                  Some (Semantics.Semantics.ls_linr m r)).
                rewrite (@PositiveMap.gro Semantics.LinState t' t π1 Hneq').
                exact Hr.
          -- intros H. exact H.
  Qed.

  Lemma R_pres_refl t s : R_pres t s s.
  Proof.
    unfold R_pres. firstorder.
  Qed.

  Lemma R_pres_same_π t' σ1 σ2 ρ0 π0 :
    (no_exch_by t' (mid_exch_state σ1) -> no_exch_by t' (mid_exch_state σ2)) ->
    R_pres t' (σ1, ρ0, π0) (σ2, ρ0, π0).
  Proof.
    unfold R_pres, Active, Live, Done, ALin, NoExchBy.
    simpl. intros Hno.
    split; [tauto|].
    split.
    - intros m [Hlin Hnx]. split; [exact Hlin|auto].
    - split.
      + intros m ret Hlin. exact Hlin.
      + split.
        * intros m Hlive. exact Hlive.
        * intros Hnx. auto.
  Qed.

  Lemma R_pres_add_add_other t t' ls1 ls2 σ1 σ2 ρ1 ρ2 π0 :
    t <> t' ->
    (no_exch_by t' (mid_exch_state σ1) -> no_exch_by t' (mid_exch_state σ2)) ->
    R_pres t' (σ1, ρ1, π0) (σ2, ρ2, TMap.add t ls2 (TMap.add t ls1 π0)).
  Proof.
    intros Hneq Hno.
    assert (Hneq' : t' <> t) by congruence.
    unfold R_pres, Active, Live, Done, ALin, NoExchBy.
    simpl.
    split.
    - split; intro Hnone.
      + rewrite PositiveMap.gso by exact Hneq'.
        rewrite PositiveMap.gso by exact Hneq'.
        exact Hnone.
      + rewrite PositiveMap.gso in Hnone by exact Hneq'.
        rewrite PositiveMap.gso in Hnone by exact Hneq'.
        exact Hnone.
    - split.
      + intros m [Hlin Hnx]. simpl in *. split.
        * simpl. rewrite PositiveMap.gso by exact Hneq'.
          rewrite PositiveMap.gso by exact Hneq'.
          exact Hlin.
        * auto.
      + split.
        * intros m ret Hlin. simpl in *.
          simpl. rewrite PositiveMap.gso by exact Hneq'.
          rewrite PositiveMap.gso by exact Hneq'.
          exact Hlin.
        * split.
          -- intros m [Hlin | [ret Hlin]]; simpl in *.
             ++ left. simpl.
                rewrite PositiveMap.gso by exact Hneq'.
                rewrite PositiveMap.gso by exact Hneq'.
                exact Hlin.
             ++ right. exists ret. simpl.
                rewrite PositiveMap.gso by exact Hneq'.
                rewrite PositiveMap.gso by exact Hneq'.
                exact Hlin.
          -- intros Hnx. auto.
  Qed.

  Lemma mid_valid_rgi : forall t, ValidRGI (R t) (G t) I t.
  Proof.
    constructor.
    unfold R. intros s s' Hrel _.
    exact (proj1 Hrel).
  Qed.

  Lemma mid_cross_rely :
    forall t1 t2 : tid,
      t1 <> t2 ->
      (G t1 ∪ (GINV t1 ∪ GRET t1 ∪ GId) ⊆ R t2)%RGRelation.
  Proof.
    unfold G, R.
    intros t1 t2 Hneq s1 s2 Hrel.
    destruct Hrel as [HG | Hmeta].
    - exact (proj2 HG t2 Hneq).
    - unfold GINV, GRET, GId in Hmeta.
      destruct Hmeta as [[Hinv | Hret] | Hid].
      + destruct Hinv as [f Hinv].
        eapply R_pres_ginv_other; eauto.
      + destruct Hret as [f [ret Hret]].
        eapply R_pres_gret_other; eauto.
      + subst. apply R_pres_refl.
  Qed.

  Lemma mid_init : I (li_init Fmid, li_init F, (@TMap.empty _)).
  Proof.
    unfold I, mid_stack_state, mid_exch_state.
    simpl. repeat split.
  Qed.

  Definition push_tso_impl (v : A) (t : tid) : Prog (li_sig E) unit :=
    Do {
      bindProg (components_impl (inr (ExchSpec.exch (Some v))) t) (fun other =>
      match other with
      | Some None => Ret (inr tt)
      | _ =>
        bindProg (components_impl (inl (TryStackSpec.push v)) t) (fun succ =>
        Ret (match succ with | FAIL => inl tt | _ => inr tt end))
      end
      )
    } Loop.

  Definition pop_tso_impl (t : tid) : Prog (li_sig E) (option A) :=
    Do {
      bindProg (components_impl (inr (ExchSpec.exch None)) t) (fun other =>
      match other with
      | Some (Some v) => Ret (inr (Some v))
      | _ =>
        bindProg (components_impl (inl TryStackSpec.pop) t) (fun succ =>
        Ret (match succ with | FAIL => inl tt | OK v => inr v end))
      end
      )
    } Loop.

  Definition ebstack_tso_impl : ModuleImpl (li_sig E) (li_sig F) :=
    fun m t =>
      match m with
      | StackSpec.push v => push_tso_impl v t
      | StackSpec.pop => pop_tso_impl t
      end.

  Definition ebstack_tso_impl_modular : ModuleImpl (li_sig E) (li_sig F) :=
    ebstack_tso_impl.

  Lemma components_correct_tensor :
    cal components_impl (li_init Etensor) (li_init Fmid).
  Proof.
    unfold cal. simpl.
    eapply tensor_components_sim.
    - apply tensor_threadpool_empty.
    - apply tensor_linmap_empty.
    - exact (li_correct TS.Mtrystack).
    - apply pool_lin_consistent_empty.
    - exact (li_correct EX.Mexchanger).
    - apply pool_lin_consistent_empty.
  Qed.

  Definition view_le (v1 v2 : tid -> positive) : Prop :=
    forall t, Pos.le (v1 t) (v2 t).

  Definition tensor_view_le
    (τ : State (li_lts Etensor)) (σ : ComboTSOState) : Prop :=
    exists vtop vmem vex,
      τ =
        ((combo_stack_top_state_with_view σ vtop,
          combo_stack_mem_state_with_view σ vmem),
         combo_exchanger_state_with_view σ vex) /\
      view_le vtop (combo_view_at (combo_view σ) L_stack_top) /\
      view_le vmem (combo_view_at (combo_view σ) L_stack_mem) /\
      view_le vex (combo_view_at (combo_view σ) L_exchanger_offer).

  Lemma combo_init_tensor_view_le :
    tensor_view_le (li_init Etensor) init_combo_tso.
  Proof.
    repeat eexists; repeat split; cbn; intros ?; lia.
  Qed.

  Lemma cas_view_advance_all_inj h h' :
    CASRegTSOSpec.view_advance_all h =
      CASRegTSOSpec.view_advance_all h' ->
    h = h'.
  Proof.
    intro H.
    pose proof (f_equal (fun f => f xH) H) as Hx.
    exact Hx.
  Qed.

  Lemma mem_view_advance_all_inj h h' :
    OwnedMemTSOSpec.view_advance_all h =
      OwnedMemTSOSpec.view_advance_all h' ->
    h = h'.
  Proof.
    intro H.
    pose proof (f_equal (fun f => f xH) H) as Hx.
    exact Hx.
  Qed.

  Lemma view_le_update_same v l vlow vloc :
    view_le vlow vloc ->
    view_le vlow (combo_view_at (combo_view_update v l vloc) l).
  Proof.
    unfold view_le, combo_view_at, combo_view_update.
    intros Hle t0. destruct GlobalLoc_eq_dec; congruence.
  Qed.

  Lemma view_le_update_other v l l' vlow vloc :
    l <> l' ->
    view_le vlow (combo_view_at v l') ->
    view_le vlow (combo_view_at (combo_view_update v l vloc) l').
  Proof.
    unfold view_le, combo_view_at, combo_view_update.
    intros Hneq Hle t0. destruct GlobalLoc_eq_dec; congruence.
  Qed.

  Lemma cas_upd_tid_time_le_update_tid_all v l vlow tid0 h :
    view_le vlow (combo_view_at v l) ->
    view_le (CASRegTSOSpec.upd_tid_time vlow tid0 h)
      (combo_view_at (combo_view_update_tid_all v tid0 h) l).
  Proof.
    unfold view_le, combo_view_at, combo_view_update_tid_all,
      CASRegTSOSpec.upd_tid_time.
    intros Hle t0.
    destruct (Pos.eqb tid0 t0); [apply Pos.le_refl|apply Hle].
  Qed.

  Lemma mem_upd_tid_time_le_update_tid_all v l vlow tid0 h :
    view_le vlow (combo_view_at v l) ->
    view_le (OwnedMemTSOSpec.upd_tid_time vlow tid0 h)
      (combo_view_at (combo_view_update_tid_all v tid0 h) l).
  Proof.
    unfold view_le, combo_view_at, combo_view_update_tid_all,
      OwnedMemTSOSpec.upd_tid_time.
    intros Hle t0.
    destruct (Pos.eqb tid0 t0); [apply Pos.le_refl|apply Hle].
  Qed.

  Lemma view_le_update_tid_all_fresh v l vlow tid0 h :
    view_le vlow (combo_view_at v l) ->
    combo_view_fresh v h ->
    view_le vlow (combo_view_at (combo_view_update_tid_all v tid0 h) l).
  Proof.
    unfold view_le, combo_view_at, combo_view_update_tid_all.
    intros Hle Hfresh t0.
    destruct (Pos.eqb tid0 t0) eqn:Heq.
    - apply Pos.eqb_eq in Heq. subst t0.
      specialize (Hle tid0).
      specialize (Hfresh tid0 l).
      apply Pos.lt_le_incl.
      eapply Pos.le_lt_trans; eauto.
    - apply Hle.
  Qed.

  Lemma stack_top_replay
    ev σ top' vtop :
    Step stack_top_lts ev (combo_stack_top_state σ) top' ->
    combo_cas_global_ok L_stack_top (combo_view σ) ev top' ->
    view_le vtop (combo_view_at (combo_view σ) L_stack_top) ->
    exists top_low',
      Step stack_top_lts ev
        (combo_stack_top_state_with_view σ vtop) top_low' /\
      forall vmem vex,
        view_le vmem (combo_view_at (combo_view σ) L_stack_mem) ->
        view_le vex (combo_view_at (combo_view σ) L_exchanger_offer) ->
        tensor_view_le
          ((top_low',
            combo_stack_mem_state_with_view σ vmem),
           combo_exchanger_state_with_view σ vex)
          (combo_with_stack_top σ ev top').
  Proof.
    intros Hstep Hglobal Hle_top.
    inversion Hstep; subst; clear Hstep.
    - destruct (stack_top_phase σ) as [phase|phase pt pop] eqn:Hphase;
        unfold combo_stack_top_state, combo_stack_top_state_with_view in *;
        rewrite Hphase in *;
        cbn in *;
        repeat match goal with
        | H : Idle _ = Idle _ |- _ => inversion H; subst; clear H
        | H : Idle _ = Pending _ _ _ |- _ => inversion H
        | H : Pending _ _ _ = Idle _ |- _ => inversion H
        | H : Pending _ _ _ = Pending _ _ _ |- _ => inversion H; subst; clear H
        end.
      dependent destruction Hstep0.
      + exists (@Pending (CASRegTSOSpec.ECASReg (option HeapSpec.Addr))
          (CASRegTSOSpec.SCASRegTSO (option HeapSpec.Addr))
          (combo_stack_top_raw_with_view σ vtop) t0
          (@CASRegTSOSpec.get (option HeapSpec.Addr))).
        split.
        * econstructor 1. constructor.
        * intros vmem vex Hle_mem Hle_ex.
          exists vtop, vmem, vex.
          split.
          { unfold combo_with_stack_top, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { apply view_le_update_same. exact Hle_top. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_mem]. }
          { apply view_le_update_other; [discriminate|exact Hle_ex]. }
      + exists (@Pending (CASRegTSOSpec.ECASReg (option HeapSpec.Addr))
          (CASRegTSOSpec.SCASRegTSO (option HeapSpec.Addr))
          (combo_stack_top_raw_with_view σ vtop) t0
          (@CASRegTSOSpec.cas (option HeapSpec.Addr) expected desired)).
        split.
        * econstructor 1. constructor.
        * intros vmem vex Hle_mem Hle_ex.
          exists vtop, vmem, vex.
          split.
          { unfold combo_with_stack_top, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { apply view_le_update_same. exact Hle_top. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_mem]. }
          { apply view_le_update_other; [discriminate|exact Hle_ex]. }
    - destruct (stack_top_phase σ) as [phase|phase pt pop] eqn:Hphase;
        unfold combo_stack_top_state, combo_stack_top_state_with_view in *;
        rewrite Hphase in *;
        cbn in *;
        repeat match goal with
        | H : Idle _ = Idle _ |- _ => inversion H; subst; clear H
        | H : Idle _ = Pending _ _ _ |- _ => inversion H
        | H : Pending _ _ _ = Idle _ |- _ => inversion H
        | H : Pending _ _ _ = Pending _ _ _ |- _ => inversion H; subst; clear H
        end.
      pose proof Hstep0 as Horig.
      dependent destruction Hstep0.
      + let tid0 := match type of H with
          | Pos.lt (_ ?tid) _ => constr:(tid)
          end in
        exists (Idle (CASRegTSOSpec.mkCASRegTSO
          (CASRegTSOSpec.cas_mem (combo_stack_top_raw σ))
          (CASRegTSOSpec.upd_tid_time vtop tid0 h))).
        split.
        * econstructor 2. econstructor 2.
          -- let tid0 := match type of H with
             | Pos.lt (_ ?tid) _ => constr:(tid)
             end in
             specialize (Hle_top tid0); cbn in *;
             eapply Pos.le_lt_trans; eauto.
          -- reflexivity.
          -- reflexivity.
        * intros vmem vex Hle_mem Hle_ex.
          destruct Hglobal as [hg [Hfresh Hgview]].
          let tid0 := match type of H with
            | Pos.lt (_ ?tid) _ => constr:(tid)
            end in
          set (tid_read := tid0) in *;
          assert (h = hg) as ->.
          { pose proof (f_equal (fun f => f tid_read) Hgview) as Heq.
            cbn in Heq.
            unfold CASRegTSOSpec.upd_tid_time in Heq.
            rewrite Pos.eqb_refl in Heq. exact Heq. }
          exists (CASRegTSOSpec.upd_tid_time vtop tid_read hg), vmem, vex.
          split.
          { unfold combo_with_stack_top, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { unfold view_le, combo_view_at, combo_view_update_tid_all,
              CASRegTSOSpec.upd_tid_time in *.
            intros tx. destruct (Pos.eqb tid_read tx) eqn:Heq.
            - apply Pos.eqb_eq in Heq. subst tx.
              rewrite Pos.eqb_refl. apply Pos.le_refl.
            - apply Hle_top. }
          split; cbn.
          { unfold view_le, combo_view_at, combo_view_update_tid_all,
              CASRegTSOSpec.upd_tid_time in *.
            intros tx. destruct (Pos.eqb tid_read tx) eqn:Heq.
            - apply Pos.eqb_eq in Heq. subst tx.
              rewrite Pos.eqb_refl. apply Pos.lt_le_incl.
              specialize (Hle_mem tid_read).
              specialize (Hfresh tid_read L_stack_mem).
              eapply Pos.le_lt_trans; eauto.
            - apply Hle_mem. }
          { unfold view_le, combo_view_at, combo_view_update_tid_all,
              CASRegTSOSpec.upd_tid_time in *.
            intros tx. destruct (Pos.eqb tid_read tx) eqn:Heq.
            - apply Pos.eqb_eq in Heq. subst tx.
              rewrite Pos.eqb_refl. apply Pos.lt_le_incl.
              specialize (Hle_ex tid_read).
              specialize (Hfresh tid_read L_exchanger_offer).
              eapply Pos.le_lt_trans; eauto.
            - apply Hle_ex. }
      + destruct Hglobal as [hg [Hfresh Hgview]].
        assert (h = hg).
        { apply cas_view_advance_all_inj. exact Hgview. }
        subst hg.
        exists (Idle (CASRegTSOSpec.mkCASRegTSO
          (CASRegTSOSpec.mem_write
            (CASRegTSOSpec.cas_mem (combo_stack_top_raw σ)) h desired)
          (CASRegTSOSpec.view_advance_all h))).
        split.
        * destruct r.
          -- econstructor 2. econstructor 4.
             ++ intro t0. specialize (H t0). specialize (Hle_top t0). cbn in *.
                eapply Pos.le_lt_trans; eauto.
             ++ reflexivity.
             ++ reflexivity.
          -- exfalso.
             destruct (TS.step_cas_res_inv _ _ _ _ _ _ Horig)
               as [[Hr _]|[Hr [hf [_ [Hneq Hs2]]]]]; [discriminate|].
             inversion Hs2; subst; clear Hs2.
             assert (hf = h) as ->.
             { symmetry. apply cas_view_advance_all_inj. exact H2. }
             apply Hneq. reflexivity.
        * intros vmem vex Hle_mem Hle_ex.
          repeat eexists; repeat split; cbn; try reflexivity;
            unfold view_le, combo_view_at, combo_view_update_all,
              CASRegTSOSpec.view_advance_all in *;
            cbn in *; intros t0; try lia;
            try (specialize (Hle_top t0); lia);
            try (specialize (Hle_mem t0); specialize (Hfresh t0 L_stack_mem); lia);
            try (specialize (Hle_ex t0); specialize (Hfresh t0 L_exchanger_offer); lia).
      + destruct Hglobal as [hg [Hfresh Hgview]].
        assert (h = hg).
        { apply cas_view_advance_all_inj. exact Hgview. }
        subst hg.
        exists (Idle (CASRegTSOSpec.mkCASRegTSO
          (CASRegTSOSpec.cas_mem (combo_stack_top_raw σ))
          (CASRegTSOSpec.view_advance_all h))).
        split.
        * destruct r.
          -- exfalso.
             destruct (TS.step_cas_res_inv _ _ _ _ _ _ Horig)
               as [[Hr [hs [_ [Hmem Hs2]]]]|[Hr _]]; [|discriminate].
             inversion Hs2; subst; clear Hs2.
             assert (hs = h) as ->.
             { symmetry. apply cas_view_advance_all_inj. exact H3. }
             match goal with
             | Hneq : ?x <> ?x |- _ => apply Hneq; reflexivity
             end.
          -- econstructor 2. econstructor 5; eauto.
             intro t0. specialize (H t0). specialize (Hle_top t0). cbn in *.
             eapply Pos.le_lt_trans; eauto.
        * intros vmem vex Hle_mem Hle_ex.
          repeat eexists; repeat split; cbn; try reflexivity;
            unfold view_le, combo_view_at, combo_view_update_all,
              CASRegTSOSpec.view_advance_all in *;
            cbn in *; intros t0; try lia;
            try (specialize (Hle_top t0); lia);
            try (specialize (Hle_mem t0); specialize (Hfresh t0 L_stack_mem); lia);
            try (specialize (Hle_ex t0); specialize (Hfresh t0 L_exchanger_offer); lia).
  Qed.

  Lemma exchanger_replay
    ev σ ex' vex :
    Step exchanger_lts ev (combo_exchanger_state σ) ex' ->
    combo_cas_global_ok L_exchanger_offer (combo_view σ) ev ex' ->
    view_le vex (combo_view_at (combo_view σ) L_exchanger_offer) ->
    exists ex_low',
      Step exchanger_lts ev
        (combo_exchanger_state_with_view σ vex) ex_low' /\
      forall vtop vmem,
        view_le vtop (combo_view_at (combo_view σ) L_stack_top) ->
        view_le vmem (combo_view_at (combo_view σ) L_stack_mem) ->
        tensor_view_le
          ((combo_stack_top_state_with_view σ vtop,
            combo_stack_mem_state_with_view σ vmem),
           ex_low')
          (combo_with_exchanger σ ev ex').
  Proof.
    intros Hstep Hglobal Hle_ex.
    inversion Hstep; subst; clear Hstep.
    - destruct (exch_phase σ) as [phase|phase pt pop] eqn:Hphase;
        unfold combo_exchanger_state, combo_exchanger_state_with_view in *;
        rewrite Hphase in *;
        cbn in *;
        repeat match goal with
        | H : Idle _ = Idle _ |- _ => inversion H; subst; clear H
        | H : Idle _ = Pending _ _ _ |- _ => inversion H
        | H : Pending _ _ _ = Idle _ |- _ => inversion H
        | H : Pending _ _ _ = Pending _ _ _ |- _ => inversion H; subst; clear H
        end.
      dependent destruction Hstep0; try discriminate; try congruence.
      + exists (@Pending (CASRegTSOSpec.ECASReg EX.Offer)
          (CASRegTSOSpec.SCASRegTSO EX.Offer)
          (combo_exchanger_raw_with_view σ vex) t0
          (@CASRegTSOSpec.get EX.Offer)).
        split.
        * econstructor 1. constructor.
        * intros vtop vmem Hle_top Hle_mem.
          exists vtop, vmem, vex.
          split.
          { unfold combo_with_exchanger, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_top]. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_mem]. }
          { apply view_le_update_same. exact Hle_ex. }
      + exists (@Pending (CASRegTSOSpec.ECASReg EX.Offer)
          (CASRegTSOSpec.SCASRegTSO EX.Offer)
          (combo_exchanger_raw_with_view σ vex) t0
          (@CASRegTSOSpec.cas EX.Offer expected desired)).
        split.
        * econstructor 1. constructor.
        * intros vtop vmem Hle_top Hle_mem.
          exists vtop, vmem, vex.
          split.
          { unfold combo_with_exchanger, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_top]. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_mem]. }
          { apply view_le_update_same. exact Hle_ex. }
    - destruct (exch_phase σ) as [phase|phase pt pop] eqn:Hphase;
        unfold combo_exchanger_state, combo_exchanger_state_with_view in *;
        rewrite Hphase in *;
        cbn in *;
        repeat match goal with
        | H : Idle _ = Idle _ |- _ => inversion H; subst; clear H
        | H : Idle _ = Pending _ _ _ |- _ => inversion H
        | H : Pending _ _ _ = Idle _ |- _ => inversion H
        | H : Pending _ _ _ = Pending _ _ _ |- _ => inversion H; subst; clear H
        end.
      pose proof Hstep0 as Horig.
      dependent destruction Hstep0; try discriminate; try congruence.
      + exists (Idle (CASRegTSOSpec.mkCASRegTSO
          (CASRegTSOSpec.cas_mem (combo_exchanger_raw σ))
          (CASRegTSOSpec.upd_tid_time vex pt h))).
        split.
        * econstructor 2. econstructor 2.
          -- specialize (Hle_ex pt). cbn in *.
             eapply Pos.le_lt_trans; eauto.
          -- reflexivity.
          -- reflexivity.
        * intros vtop vmem Hle_top Hle_mem.
          destruct Hglobal as [hg [Hfresh Hgview]].
          assert (h = hg) as ->.
          { pose proof (f_equal (fun f => f pt) Hgview) as Heq.
            cbn in Heq.
            unfold CASRegTSOSpec.upd_tid_time in Heq.
            rewrite Pos.eqb_refl in Heq. exact Heq. }
          exists vtop, vmem, (CASRegTSOSpec.upd_tid_time vex pt hg).
          split.
          { unfold combo_with_exchanger, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          replace (CASRegTSOSpec.upd_tid_time
            (combo_view_at (combo_view σ) L_exchanger_offer) pt hg pt)
            with hg by (unfold CASRegTSOSpec.upd_tid_time;
              rewrite Pos.eqb_refl; reflexivity).
          assert (Hfresh_read :
            combo_view_fresh (combo_view σ)
              (CASRegTSOSpec.upd_tid_time
                (combo_view_at (combo_view σ) L_exchanger_offer) pt hg pt)).
          { unfold CASRegTSOSpec.upd_tid_time.
            rewrite Pos.eqb_refl. exact Hfresh. }
          split; cbn.
          { eapply view_le_update_tid_all_fresh; [exact Hle_top|exact Hfresh_read]. }
          split; cbn.
          { eapply view_le_update_tid_all_fresh; [exact Hle_mem|exact Hfresh_read]. }
          { unfold view_le, combo_view_at, combo_view_update_tid_all,
              CASRegTSOSpec.upd_tid_time in *.
            intros tx. destruct (Pos.eqb pt tx) eqn:Heq.
            - apply Pos.eqb_eq in Heq. subst tx.
              rewrite Pos.eqb_refl. apply Pos.le_refl.
            - apply Hle_ex. }
      + destruct Hglobal as [hg [Hfresh Hgview]].
        assert (h = hg).
        { apply cas_view_advance_all_inj. exact Hgview. }
        subst hg.
        exists (Idle (CASRegTSOSpec.mkCASRegTSO
          (CASRegTSOSpec.mem_write
            (CASRegTSOSpec.cas_mem (combo_exchanger_raw σ)) h desired)
          (CASRegTSOSpec.view_advance_all h))).
        split.
        * destruct r.
          -- econstructor 2. econstructor 4.
             ++ intro t0.
                match goal with
                | Hfresh_loc : forall t, Pos.lt (_ t) h |- _ =>
                    specialize (Hfresh_loc t0)
                end.
                specialize (Hle_ex t0). cbn in *.
                eapply Pos.le_lt_trans; eauto.
             ++ reflexivity.
             ++ reflexivity.
          -- exfalso.
             destruct (EX.step_cas_res_inv _ _ _ _ _ _ Horig)
               as [[Hr _]|[Hr [hf [_ [Hneq Hs2]]]]]; [discriminate|].
             inversion Hs2; subst; clear Hs2.
             assert (hf = h) as ->.
             { symmetry. apply cas_view_advance_all_inj. exact H2. }
             apply Hneq. reflexivity.
        * intros vtop vmem Hle_top Hle_mem.
          repeat eexists; repeat split; cbn; try reflexivity;
            unfold view_le, combo_view_at, combo_view_update_all,
              CASRegTSOSpec.view_advance_all in *;
            cbn in *; intros t0; try lia;
            try (specialize (Hle_ex t0); lia);
            try (specialize (Hle_top t0); specialize (Hfresh t0 L_stack_top); lia);
            try (specialize (Hle_mem t0); specialize (Hfresh t0 L_stack_mem); lia).
      + destruct Hglobal as [hg [Hfresh Hgview]].
        assert (h = hg).
        { apply cas_view_advance_all_inj. exact Hgview. }
        subst hg.
        exists (Idle (CASRegTSOSpec.mkCASRegTSO
          (CASRegTSOSpec.cas_mem (combo_exchanger_raw σ))
          (CASRegTSOSpec.view_advance_all h))).
        split.
        * destruct r.
          -- exfalso.
             destruct (EX.step_cas_res_inv _ _ _ _ _ _ Horig)
               as [[Hr [hs [_ [Hmem Hs2]]]]|[Hr _]]; [|discriminate].
             inversion Hs2; subst; clear Hs2.
             assert (hs = h) as ->.
             { symmetry. apply cas_view_advance_all_inj. exact H3. }
             match goal with
             | Hneq : ?x <> ?x |- _ => apply Hneq; reflexivity
             end.
          -- econstructor 2. econstructor 5; eauto.
             intro t0.
             match goal with
             | Hfresh_loc : forall t, Pos.lt (_ t) h |- _ =>
                 specialize (Hfresh_loc t0)
             end.
             specialize (Hle_ex t0). cbn in *.
             eapply Pos.le_lt_trans; eauto.
        * intros vtop vmem Hle_top Hle_mem.
          repeat eexists; repeat split; cbn; try reflexivity;
            unfold view_le, combo_view_at, combo_view_update_all,
              CASRegTSOSpec.view_advance_all in *;
            cbn in *; intros t0; try lia;
            try (specialize (Hle_ex t0); lia);
            try (specialize (Hle_top t0); specialize (Hfresh t0 L_stack_top); lia);
            try (specialize (Hle_mem t0); specialize (Hfresh t0 L_stack_mem); lia).
  Qed.

  Lemma mem_malloc_res_inv t (ret : HeapSpec.Addr)
      (s1 s2 : OwnedMemTSOSpec.OwnedMemState
        (TS.A * option HeapSpec.Addr)) :
    OwnedMemTSOSpec.StepMemTSO
      {| te_tid := t;
         te_ev := @ResEv
           (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))
           (@OwnedMemTSOSpec.malloc (TS.A * option HeapSpec.Addr)) ret |}
      s1 s2 ->
    exists init h,
      (forall t0, Pos.lt (OwnedMemTSOSpec.om_view s1 t0) h) /\
      OwnedMemTSOSpec.om_heap s1 ret = None /\
      OwnedMemTSOSpec.om_heap s2 =
        HeapSpec.heap_update ret init (OwnedMemTSOSpec.om_heap s1) /\
      OwnedMemTSOSpec.om_loc s2 =
        HeapSpec.heap_update ret (OwnedMemTSOSpec.LAlloc t)
          (OwnedMemTSOSpec.om_loc s1) /\
      OwnedMemTSOSpec.om_view s2 = OwnedMemTSOSpec.view_advance_all h.
  Proof.
    intros Hstep.
    remember {| te_tid := t;
                te_ev := @ResEv
                  (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))
                  (@OwnedMemTSOSpec.malloc
                    (TS.A * option HeapSpec.Addr)) ret |}
      as ev eqn:Hev.
    revert t ret Hev.
    induction Hstep; intros tidx retx Hev; inversion Hev; subst;
      try discriminate.
    pose proof (f_equal OwnedMemTSOSpec.malloc_response Hev) as Hret.
    unfold OwnedMemTSOSpec.malloc_response in Hret.
    cbn in Hret. inversion Hret; subst.
    eexists; eexists; repeat split; eauto.
  Qed.

  Lemma mem_mread_res_inv t l (ret : TS.A * option HeapSpec.Addr)
      (s1 s2 : OwnedMemTSOSpec.OwnedMemState
        (TS.A * option HeapSpec.Addr)) :
    OwnedMemTSOSpec.StepMemTSO
      {| te_tid := t;
         te_ev := @ResEv
           (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))
           (@OwnedMemTSOSpec.mread (TS.A * option HeapSpec.Addr) l) ret |}
      s1 s2 ->
    exists h,
      (forall t0, Pos.lt (OwnedMemTSOSpec.om_view s1 t0) h) /\
      OwnedMemTSOSpec.om_heap s1 l = Some ret /\
      OwnedMemTSOSpec.om_loc s1 l = Some OwnedMemTSOSpec.LWritten /\
      OwnedMemTSOSpec.om_heap s2 = OwnedMemTSOSpec.om_heap s1 /\
      OwnedMemTSOSpec.om_loc s2 = OwnedMemTSOSpec.om_loc s1 /\
      OwnedMemTSOSpec.om_view s2 =
        OwnedMemTSOSpec.upd_tid_time (OwnedMemTSOSpec.om_view s1) t h.
  Proof.
    intros Hstep.
    dependent destruction Hstep.
    eexists; repeat split; eauto.
  Qed.

  Lemma mem_mwrite_res_inv t l v
      (s1 s2 : OwnedMemTSOSpec.OwnedMemState
        (TS.A * option HeapSpec.Addr)) :
    OwnedMemTSOSpec.StepMemTSO
      {| te_tid := t;
         te_ev := @ResEv
           (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))
           (@OwnedMemTSOSpec.mwrite (TS.A * option HeapSpec.Addr) l v) tt |}
      s1 s2 ->
    exists h,
      (forall t0, Pos.lt (OwnedMemTSOSpec.om_view s1 t0) h) /\
      OwnedMemTSOSpec.om_loc s1 l = Some (OwnedMemTSOSpec.LAlloc t) /\
      OwnedMemTSOSpec.om_heap s2 =
        HeapSpec.heap_update l v (OwnedMemTSOSpec.om_heap s1) /\
      OwnedMemTSOSpec.om_loc s2 =
        HeapSpec.heap_update l OwnedMemTSOSpec.LWritten
          (OwnedMemTSOSpec.om_loc s1) /\
      OwnedMemTSOSpec.om_view s2 = OwnedMemTSOSpec.view_advance_all h.
  Proof.
    intros Hstep.
    dependent destruction Hstep.
    eexists; repeat split; eauto.
  Qed.

  Lemma stack_mem_replay
    ev σ mem' vmem :
    Step stack_mem_lts ev (combo_stack_mem_state σ) mem' ->
    combo_mem_global_ok (combo_view σ) ev mem' ->
    view_le vmem (combo_view_at (combo_view σ) L_stack_mem) ->
    exists mem_low',
      Step stack_mem_lts ev
        (combo_stack_mem_state_with_view σ vmem) mem_low' /\
      forall vtop vex,
        view_le vtop (combo_view_at (combo_view σ) L_stack_top) ->
        view_le vex (combo_view_at (combo_view σ) L_exchanger_offer) ->
        tensor_view_le
          ((combo_stack_top_state_with_view σ vtop, mem_low'),
           combo_exchanger_state_with_view σ vex)
          (combo_with_stack_mem σ ev mem').
  Proof.
    intros Hstep Hglobal Hle_mem.
    inversion Hstep; subst; clear Hstep.
    - destruct (stack_mem_phase σ) as [phase|phase pt pop] eqn:Hphase;
        unfold combo_stack_mem_state, combo_stack_mem_state_with_view in *;
        rewrite Hphase in *;
        cbn in *;
        repeat match goal with
        | H : Idle _ = Idle _ |- _ => inversion H; subst; clear H
        | H : Idle _ = Pending _ _ _ |- _ => inversion H
        | H : Pending _ _ _ = Idle _ |- _ => inversion H
        | H : Pending _ _ _ = Pending _ _ _ |- _ => inversion H; subst; clear H
        end.
      dependent destruction Hstep0; try discriminate; try congruence.
      + exists (@Pending
          (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))
          (OwnedMemTSOSpec.OwnedMemState (TS.A * option HeapSpec.Addr))
          (combo_owned_mem_raw_with_view σ vmem) t0
          (@OwnedMemTSOSpec.malloc (TS.A * option HeapSpec.Addr))).
        split.
        * econstructor 1. constructor.
        * intros vtop vex Hle_top Hle_ex.
          exists vtop, vmem, vex.
          split.
          { unfold combo_with_stack_mem, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_top]. }
          split; cbn.
          { apply view_le_update_same. exact Hle_mem. }
          { apply view_le_update_other; [discriminate|exact Hle_ex]. }
      + exists (@Pending
          (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))
          (OwnedMemTSOSpec.OwnedMemState (TS.A * option HeapSpec.Addr))
          (combo_owned_mem_raw_with_view σ vmem) t0
          (@OwnedMemTSOSpec.mread (TS.A * option HeapSpec.Addr) l)).
        split.
        * econstructor 1. constructor.
        * intros vtop vex Hle_top Hle_ex.
          exists vtop, vmem, vex.
          split.
          { unfold combo_with_stack_mem, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_top]. }
          split; cbn.
          { apply view_le_update_same. exact Hle_mem. }
          { apply view_le_update_other; [discriminate|exact Hle_ex]. }
      + exists (@Pending
          (OwnedMemTSOSpec.EMem (TS.A * option HeapSpec.Addr))
          (OwnedMemTSOSpec.OwnedMemState (TS.A * option HeapSpec.Addr))
          (combo_owned_mem_raw_with_view σ vmem) t0
          (@OwnedMemTSOSpec.mwrite (TS.A * option HeapSpec.Addr) l v)).
        split.
        * econstructor 1. constructor.
        * intros vtop vex Hle_top Hle_ex.
          exists vtop, vmem, vex.
          split.
          { unfold combo_with_stack_mem, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. reflexivity. }
          split; cbn.
          { apply view_le_update_other; [discriminate|exact Hle_top]. }
          split; cbn.
          { apply view_le_update_same. exact Hle_mem. }
          { apply view_le_update_other; [discriminate|exact Hle_ex]. }
    - destruct (stack_mem_phase σ) as [phase|phase pt pop] eqn:Hphase;
        unfold combo_stack_mem_state, combo_stack_mem_state_with_view in *;
        rewrite Hphase in *;
        cbn in *;
        repeat match goal with
        | H : Idle _ = Idle _ |- _ => inversion H; subst; clear H
        | H : Idle _ = Pending _ _ _ |- _ => inversion H
        | H : Pending _ _ _ = Idle _ |- _ => inversion H
        | H : Pending _ _ _ = Pending _ _ _ |- _ => inversion H; subst; clear H
        end.
      destruct pop as [|l|l v].
      + destruct (mem_malloc_res_inv _ _ _ _ Hstep0) as
          [init [h [Hfresh_mem [Hnone [Hheap [Hloc Hview]]]]]].
        destruct Hglobal as [hg [Hfresh Hgview]].
        assert (h = hg).
        { apply mem_view_advance_all_inj. rewrite <- Hview. exact Hgview. }
        subst hg.
        exists (Idle (OwnedMemTSOSpec.mkOwnedMemTSO
          (HeapSpec.heap_update r init (stack_heap σ))
          (HeapSpec.heap_update r (OwnedMemTSOSpec.LAlloc pt) (loc_status σ))
          (OwnedMemTSOSpec.view_advance_all h))).
        split.
        * econstructor 2.
          econstructor 2 with (h:=h); cbn.
          -- intro t0.
             specialize (Hfresh_mem t0).
             specialize (Hle_mem t0). cbn in *.
             eapply Pos.le_lt_trans; eauto.
          -- exact Hnone.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
        * intros vtop vex Hle_top Hle_ex.
          exists vtop, (OwnedMemTSOSpec.view_advance_all h), vex.
          split.
          { unfold combo_with_stack_mem, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. rewrite Hheap, Hloc. reflexivity. }
          split; cbn.
          { unfold view_le, combo_view_at, combo_mem_view_after,
              combo_view_update_all, OwnedMemTSOSpec.view_advance_all in *.
            cbn. intros t0. rewrite Hview. cbn.
            specialize (Hle_top t0). specialize (Hfresh t0 L_stack_top).
            apply Pos.lt_le_incl.
            eapply Pos.le_lt_trans; [exact Hle_top|exact Hfresh]. }
          split; cbn.
          { unfold view_le, combo_view_at, combo_mem_view_after,
              combo_view_update_all, OwnedMemTSOSpec.view_advance_all in *.
            cbn. intros t0. rewrite Hview. cbn. apply Pos.le_refl. }
          { unfold view_le, combo_view_at, combo_mem_view_after,
              combo_view_update_all, OwnedMemTSOSpec.view_advance_all in *.
            cbn. intros t0. rewrite Hview. cbn.
            specialize (Hle_ex t0). specialize (Hfresh t0 L_exchanger_offer).
            apply Pos.lt_le_incl.
            eapply Pos.le_lt_trans; [exact Hle_ex|exact Hfresh]. }
      + destruct (mem_mread_res_inv _ _ _ _ _ Hstep0) as
          [h [Hfresh_mem [Hheap_read [Hloc_read [Hheap [Hloc Hview]]]]]].
        destruct Hglobal as [hg [Hfresh Hgview]].
        assert (h = hg) as ->.
        { pose proof (f_equal (fun f => f pt)
            (eq_trans (eq_sym Hview) Hgview)) as Heq.
          cbn in Heq.
          unfold OwnedMemTSOSpec.upd_tid_time in Heq.
          rewrite Pos.eqb_refl in Heq. exact Heq. }
        assert (Hread_view : OwnedMemTSOSpec.om_view s2 pt = hg).
        { rewrite Hview. unfold OwnedMemTSOSpec.upd_tid_time.
          rewrite Pos.eqb_refl. reflexivity. }
        exists (Idle (OwnedMemTSOSpec.mkOwnedMemTSO
          (stack_heap σ) (loc_status σ)
          (OwnedMemTSOSpec.upd_tid_time vmem pt hg))).
        split.
        * econstructor 2. econstructor 4 with (h:=hg); cbn.
          -- intro t0.
             specialize (Hfresh_mem t0).
             specialize (Hle_mem t0). cbn in *.
             eapply Pos.le_lt_trans; eauto.
          -- exact Hheap_read.
          -- exact Hloc_read.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
        * intros vtop vex Hle_top Hle_ex.
          exists vtop, (OwnedMemTSOSpec.upd_tid_time vmem pt hg), vex.
          split.
          { unfold combo_with_stack_mem, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. rewrite Hheap, Hloc. reflexivity. }
          split; cbn.
          { unfold combo_view_at, combo_mem_view_after. cbn.
            rewrite Hread_view.
            apply view_le_update_tid_all_fresh; assumption. }
          split; cbn.
          { unfold combo_view_at, combo_mem_view_after. cbn.
            rewrite Hread_view.
            apply mem_upd_tid_time_le_update_tid_all. exact Hle_mem. }
          { unfold combo_view_at, combo_mem_view_after. cbn.
            rewrite Hread_view.
            apply view_le_update_tid_all_fresh; assumption. }
      + destruct r.
        destruct (mem_mwrite_res_inv _ _ _ _ _ Hstep0) as
          [h [Hfresh_mem [Hloc_alloc [Hheap [Hloc Hview]]]]].
        destruct Hglobal as [hg [Hfresh Hgview]].
        assert (h = hg).
        { apply mem_view_advance_all_inj. rewrite <- Hview. exact Hgview. }
        subst hg.
        exists (Idle (OwnedMemTSOSpec.mkOwnedMemTSO
          (HeapSpec.heap_update l v (stack_heap σ))
          (HeapSpec.heap_update l OwnedMemTSOSpec.LWritten (loc_status σ))
          (OwnedMemTSOSpec.view_advance_all h))).
        split.
        * econstructor 2.
          econstructor 6 with (h:=h); cbn.
          -- intro t0.
             specialize (Hfresh_mem t0).
             specialize (Hle_mem t0). cbn in *.
             eapply Pos.le_lt_trans; eauto.
          -- exact Hloc_alloc.
          -- reflexivity.
          -- reflexivity.
          -- reflexivity.
        * intros vtop vex Hle_top Hle_ex.
          exists vtop, (OwnedMemTSOSpec.view_advance_all h), vex.
          split.
          { unfold combo_with_stack_mem, combo_stack_top_state_with_view,
              combo_stack_mem_state_with_view, combo_exchanger_state_with_view,
              combo_stack_top_raw_with_view, combo_owned_mem_raw_with_view,
              combo_exchanger_raw_with_view.
            cbn. rewrite Hheap, Hloc. reflexivity. }
          split; cbn.
          { unfold view_le, combo_view_at, combo_mem_view_after,
              combo_view_update_all, OwnedMemTSOSpec.view_advance_all in *.
            cbn. intros t0. rewrite Hview. cbn.
            specialize (Hle_top t0). specialize (Hfresh t0 L_stack_top).
            apply Pos.lt_le_incl.
            eapply Pos.le_lt_trans; [exact Hle_top|exact Hfresh]. }
          split; cbn.
          { unfold view_le, combo_view_at, combo_mem_view_after,
              combo_view_update_all, OwnedMemTSOSpec.view_advance_all in *.
            cbn. intros t0. rewrite Hview. cbn. apply Pos.le_refl. }
          { unfold view_le, combo_view_at, combo_mem_view_after,
              combo_view_update_all, OwnedMemTSOSpec.view_advance_all in *.
            cbn. intros t0. rewrite Hview. cbn.
            specialize (Hle_ex t0). specialize (Hfresh t0 L_exchanger_offer).
            apply Pos.lt_le_incl.
            eapply Pos.le_lt_trans; [exact Hle_ex|exact Hfresh]. }
  Qed.

  Lemma combo_step_tensor_view_le ev σ σ' τ :
    tensor_view_le τ σ ->
    Step VComboTSO ev σ σ' ->
    exists τ',
      Step (li_lts Etensor) ev τ τ' /\
      tensor_view_le τ' σ'.
  Proof.
    intros Hrel Hstep.
    destruct Hrel as [vtop [vmem [vex [-> [Hle_top [Hle_mem Hle_ex]]]]]].
    destruct Hstep.
    - destruct (stack_top_replay ev s top' vtop H H0 Hle_top)
        as [top_low' [Hlow Hrel']].
      exists ((top_low', combo_stack_mem_state_with_view s vmem),
        combo_exchanger_state_with_view s vex).
      split; [destruct ev as [t ev0]; destruct ev0; cbn; repeat split; eauto|].
      apply Hrel'; assumption.
    - destruct (stack_mem_replay ev s mem' vmem H H0 Hle_mem)
        as [mem_low' [Hlow Hrel']].
      exists ((combo_stack_top_state_with_view s vtop, mem_low'),
        combo_exchanger_state_with_view s vex).
      split; [destruct ev as [t ev0]; destruct ev0; cbn; repeat split; eauto|].
      apply Hrel'; assumption.
    - destruct (exchanger_replay ev s ex' vex H H0 Hle_ex)
        as [ex_low' [Hlow Hrel']].
      exists ((combo_stack_top_state_with_view s vtop,
        combo_stack_mem_state_with_view s vmem), ex_low').
      split; [destruct ev as [t ev0]; destruct ev0; cbn; repeat split; eauto|].
      apply Hrel'; assumption.
  Qed.

  Lemma combo_error_tensor_view_le ev σ τ :
    tensor_view_le τ σ ->
    Error VComboTSO ev σ ->
    Error (li_lts Etensor) ev τ.
  Proof.
    intros [vtop [vmem [vex [-> [_ [Hle_mem _]]]]]]
      [ev_mem [-> Herr]].
    destruct ev_mem as [t ev0]; destruct ev0; cbn in *.
    - inversion Herr; subst.
      + destruct (stack_mem_phase σ) as [phase|phase pt op] eqn:Hphase;
          unfold combo_stack_mem_state, combo_stack_mem_state_with_view in *;
          rewrite Hphase in *; cbn in *; try discriminate.
        match goal with
        | Hidle : Idle _ = Idle _ |- _ => inversion Hidle; subst; clear Hidle
        end.
        econstructor 1. cbn in *. exact H0.
      + destruct (stack_mem_phase σ) as [phase|phase pt op] eqn:Hphase;
          unfold combo_stack_mem_state, combo_stack_mem_state_with_view in *;
          rewrite Hphase in *; cbn in *; try discriminate.
        match goal with
        | Hidle : Idle _ = Idle _ |- _ => inversion Hidle; subst; clear Hidle
        end.
        econstructor 2. cbn in *. exact H0.
      + destruct (stack_mem_phase σ) as [phase|phase pt op] eqn:Hphase;
          unfold combo_stack_mem_state, combo_stack_mem_state_with_view in *;
          rewrite Hphase in *; cbn in *; try discriminate.
        match goal with
        | Hpend : Pending _ _ _ = Pending _ _ _ |- _ =>
            inversion Hpend; subst; clear Hpend
        end.
        econstructor 3; cbn in *; eauto.
    - inversion Herr.
  Qed.

  Lemma ts_step_combo_tensor_view_le f ev σ τ ts σ' ts' :
    tensor_view_le τ σ ->
    @Semantics.ts_step (li_sig E) (li_sig Fmid) (li_lts E)
      f ev σ ts σ' ts' ->
    exists τ',
      @Semantics.ts_step (li_sig Etensor) (li_sig Fmid) (li_lts Etensor)
        f ev τ ts τ' ts' /\
      tensor_view_le τ' σ'.
  Proof.
    intros Hrel Hstep.
    inversion Hstep; subst.
    - destruct (combo_step_tensor_view_le _ _ _ _ Hrel Hstep0)
        as [τ' [Htstep Hrel']].
      exists τ'. split; [eapply Semantics.ts_inv; exact Htstep|exact Hrel'].
    - destruct (combo_step_tensor_view_le _ _ _ _ Hrel Hstep0)
        as [τ' [Htstep Hrel']].
      exists τ'. split; [eapply Semantics.ts_res; exact Htstep|exact Hrel'].
  Qed.

  Lemma ustep_combo_tensor_view_le ev σ τ c σ' c' :
    tensor_view_le τ σ ->
    @Semantics.ustep (li_sig E) (li_sig Fmid) (li_lts E)
      ev σ c σ' c' ->
    exists τ',
      @Semantics.ustep (li_sig Etensor) (li_sig Fmid) (li_lts Etensor)
        ev τ c τ' c' /\
      tensor_view_le τ' σ'.
  Proof.
    intros Hrel Hstep.
    inversion Hstep; subst.
    destruct (ts_step_combo_tensor_view_le _ _ _ _ _ _ _ Hrel Hstep0)
      as [τ' [Htstep Hrel']].
    exists τ'. split; [|exact Hrel'].
    eapply Semantics.UStep.
    - exact Hfind.
    - exact Htstep.
    - reflexivity.
  Qed.

  Lemma ts_error_combo_tensor_view_le f ev σ τ ts :
    tensor_view_le τ σ ->
    @Semantics.ts_error (li_sig E) (li_sig Fmid) (li_lts E)
      f ev σ ts ->
    @Semantics.ts_error (li_sig Etensor) (li_sig Fmid) (li_lts Etensor)
      f ev τ ts.
  Proof.
    intros Hrel Herr.
    inversion Herr; subst.
    eapply Semantics.ts_err.
    eapply combo_error_tensor_view_le; eauto.
  Qed.

  Lemma uerror_combo_tensor_view_le ev σ τ c :
    tensor_view_le τ σ ->
    @Semantics.uerror (li_sig E) (li_sig Fmid) (li_lts E)
      ev σ c ->
    @Semantics.uerror (li_sig Etensor) (li_sig Fmid) (li_lts Etensor)
      ev τ c.
  Proof.
    intros Hrel Herr.
    inversion Herr; subst.
    eapply Semantics.UError.
    - exact Hfind.
    - eapply ts_error_combo_tensor_view_le; eauto.
  Qed.

  Lemma tpsim_combo_of_tensor σ τ c ρ π :
    tensor_view_le τ σ ->
    @TPSimulation (li_sig Etensor) (li_sig Fmid) (li_lts Etensor) (li_lts Fmid)
      components_impl τ c ρ π ->
    @TPSimulation (li_sig E) (li_sig Fmid) (li_lts E) (li_lts Fmid)
      components_impl σ c ρ π.
  Proof.
    revert σ τ c ρ π.
    cofix IH.
    intros σ τ c ρ π Hrel Hsim.
    inversion Hsim as [Herror|Hinv Hret Hustep Hlin Htau Hnoerr]; subst.
    - constructor. exact Herror.
    - constructor 2.
      + intros t f c' Hstep.
        eapply IH; [exact Hrel|].
        apply Hinv. exact Hstep.
      + intros t f ret c' Hstep.
        specialize (Hret t f ret c' Hstep) as [Hπ Hsim'].
        split; [exact Hπ|].
        eapply IH; [exact Hrel|exact Hsim'].
      + intros ev σ' c' Hstep.
        destruct (ustep_combo_tensor_view_le ev σ τ c σ' c' Hrel Hstep)
          as [τ' [Htstep Hrel']].
        specialize (Hustep ev τ' c' Htstep)
          as [ρ' [π' [Hsteps Hsim']]].
        exists ρ', π'. split; [exact Hsteps|].
        eapply IH; [exact Hrel'|exact Hsim'].
      + destruct Hlin as [ρ' [π' [Hsteps Hsim']]].
        exists ρ', π'. split; [exact Hsteps|].
        eapply IH; [exact Hrel|exact Hsim'].
      + intros t c' Hstep.
        exact (IH σ τ c' ρ π Hrel (Htau t c' Hstep)).
      + intros ev Herr.
        apply (Hnoerr ev).
        eapply uerror_combo_tensor_view_le; eauto.
  Qed.

  Lemma components_correct :
    cal components_impl (li_init E) (li_init Fmid).
  Proof.
    unfold E, ECombo, cal. simpl.
    eapply tpsim_combo_of_tensor.
    - apply combo_init_tensor_view_le.
    - exact components_correct_tensor.
  Qed.

  Program Definition Mcomponents : layer_implementation E Fmid := {|
    li_impl := components_impl
  |}.
  Next Obligation.
    apply components_correct.
  Qed.

  Definition try_push_ret_obs (ev : @Event (ETryStack A)) : option (TryResult unit) :=
    match ev with
    | ResEv (TryStackSpec.push _) ret => Some ret
    | _ => None
    end.

  Lemma step_try_push_ok_not_same t (x : A) stk :
    ~ StepTryStack {| te_tid := t; te_ev := ResEv (TryStackSpec.push x) (OK tt) |} stk stk.
  Proof.
    intros Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    - match goal with
      | H : cons _ ?xs = ?xs |- _ =>
          apply (f_equal (@length _)) in H; simpl in H; lia
      end.
    - match goal with
      | H : ResEv _ (OK tt) = ResEv _ FAIL |- _ =>
          apply (f_equal try_push_ret_obs) in H; simpl in H; discriminate
      end.
  Qed.
  Lemma ebstack_push_triple t v :
    [li_lts Fmid, li_lts F, R t, G t, I, t] ⊢
      {{ I //\\ Active t (StackSpec.push v) }}
      push_impl v t
      {{ fun _ =>
           I //\\ (ALin t (Semantics.Semantics.ls_linr (StackSpec.push v) tt) //\\
             NoExchBy t) }}.
Proof.

    Ltac solve_idle_eq :=
      first [ reflexivity
            | match goal with H : ?x = ?y |- ?x = ?y => exact H end
            | match goal with H : ?x = ?y |- ?y = ?x => symmetry; exact H end
            | congruence ].
    Ltac pupdate_intros_atomic_mid :=
      red; intros σ1 ρ1 π1 Hpre σ2 Hstep;
      destruct σ1 as [σl1 σr1]; destruct σ2 as [σl2 σr2];
      simpl in Hstep;
      repeat match type of Hstep with
      | _ /\ _ => destruct Hstep as [Hstep ?]; subst
      end;
      inversion Hstep; subst; clear Hstep;
      repeat match goal with
      | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
      | H : _ = _ |- _ => try discriminate H; try dependent destruction H
      end;
      repeat match goal with
      | H : StepTryStack {| te_tid := _; te_ev := ResEv (TryStackSpec.push _) (OK tt) |} ?xs ?xs |- _ =>
          exfalso; eapply step_try_push_ok_not_same; exact H
      | H : StepTryStack _ _ _ |- _ => inversion H; subst; clear H; try congruence
      | H : StepExch _ _ _ |- _ => inversion H; subst; clear H; try congruence
      end;
      repeat match goal with
      | H : @ResEv (ETryStack _) (TryStackSpec.push _) (OK tt) = @ResEv (ETryStack _) (TryStackSpec.push _) FAIL |- _ =>
          exfalso; apply (f_equal try_push_ret_obs) in H; simpl in H; discriminate
      | H : @ResEv (ETryStack _) (TryStackSpec.push _) FAIL = @ResEv (ETryStack _) (TryStackSpec.push _) (OK tt) |- _ =>
          exfalso; apply (f_equal try_push_ret_obs) in H; simpl in H; discriminate
      | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
      | H : _ = _ |- _ => try discriminate H; try dependent destruction H
      end;
      repeat match goal with
      | H : cons _ ?xs = ?xs |- _ => exfalso; apply (f_equal (@length _)) in H; simpl in H; lia
      | H : ?xs = cons _ ?xs |- _ => exfalso; apply (f_equal (@length _)) in H; simpl in H; lia
      end;
      simpl in *.
    Ltac pupdate_finish_mid :=
      try solve [apply rt_refl];
      try (eexists; eexists; split; [apply rt_refl|]).
    Ltac pupdate_start_mid := eexists; eexists; split.
    Tactic Notation "pupdate_forward_mid" constr(tid0) constr(ev) :=
      eapply rt_trans;
      [ eapply rt_step;
        lazymatch ev with
        | InvEv ?f => eapply (Semantics.ps_inv tid0 f)
        | ResEv ?f ?ret => eapply (Semantics.ps_ret tid0 f ret)
        end; [cbn; constructor; constructor
             | simpl; try rewrite PositiveMap.gss;
               try (rewrite PositiveMap.gso by congruence);
               try (rewrite PositiveMap.gso by congruence); eauto]
      | ].

    simpl. unfold push_impl.
    eapply provable_doloop;
    try solve_conj_impl;
    try solve_conj_stable ebstack_mid_stable.
    eapply provable_vis_safe with
      (P' := I //\\ Live t (push v))
      (Q' := fun other =>
        match other with
        | Some None => I //\\ ALin t (Semantics.Semantics.ls_linr (push v) tt) //\\ NoExchBy t
        | _ => I //\\ Active t (push v)
        end);
    try solve_conj_impl;
    try solve_conj_stable ebstack_mid_stable;
    try (intro other; destruct other as [[ov|]|]; try destruct ov; solve_conj_stable ebstack_mid_stable);
    try solve [apply no_error].
    * intros [[ov|]|]; try destruct ov; solve_conj_impl.
    * pupdate_intros_atomic_mid.
      {
        pupdate_finish_mid; split.
        - destruct Hpre as [HI [Hlin Hno]].
          unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
          split.
          + destruct HI as [Hr _]. split; [solve_idle_eq|split; [exact Hlin|auto]].
          + left. exact Hlin.
        - unfold G, R_pres, Active, Live, Done, ALin, NoExchBy, Conj.
          split.
          + destruct Hpre as [HI [Hlin Hno]].
            unfold I in *; simpl in *.
            destruct HI as [Hr _]. split; [solve_idle_eq|split; [exact Hlin|auto]].
          + intros t' Hneq; simpl.
            split.
            -- split; intro H; exact H.
            -- split.
               ++ intros m [Hlin Hno]. split; [exact Hlin|congruence].
               ++ split.
                  ** intros m ret Hlin. exact Hlin.
                  ** split.
                     --- intros m [Hlin | [ret Hlin]]; [left | right; exists ret]; exact Hlin.
                     --- intros _. congruence.
      }
      {
        destruct v1 as [w|].
        - pupdate_finish_mid; split.
          + destruct Hpre as [HI [Hlin Hno]].
    	                unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
    		                destruct HI as [Hr [Hex Hdist]].
    		                split; [split; [solve_idle_eq|split; [split; [exact Hex|exact Hlin]|congruence]]|left; exact Hlin].
          + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy, Conj.
            split.
            * destruct Hpre as [HI [Hlin Hno]].
              unfold I, mid_stack_state, mid_exch_state, Active, ALin in *; simpl in *.
    		                  destruct HI as [Hr [Hex Hdist]].
    		                  split; [solve_idle_eq|split; [split; [exact Hex|exact Hlin]|congruence]].
    	                * intros t' Hneq; simpl.
              destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
              -- split.
                 ++ split; intro Hnone.
                    ** destruct Hpre as [HI [Hlin Hno]].
                       unfold I in HI; simpl in HI.
    	                           destruct HI as [_ [Hex _]].
                       rewrite Hex in Hnone. discriminate.
                    ** destruct Hpre as [HI [Hlin Hno]].
                       unfold I in HI; simpl in HI.
    	                           destruct HI as [_ [Hex _]].
                       rewrite Hex in Hnone. discriminate.
                 ++ split.
                    ** intros m [Hlin Hno]. contradiction.
                    ** split.
                       --- intros m ret Hret.
                           destruct Hpre as [HI _].
                           unfold I in HI; simpl in HI.
    	                               destruct HI as [_ [Hex _]].
                           rewrite Hex in Hret. discriminate.
                       --- split.
    	                               +++ intros m [Hlin | [ret Hret]].
                               { left; exact Hlin. }
                               { destruct Hpre as [HI _].
                                 unfold I in HI; simpl in HI.
    	                                     destruct HI as [_ [Hex _]].
                                 simpl in Hret.
                                 rewrite Hex in Hret. discriminate. }
                           +++ intros Hno. contradiction.
              -- split.
                 ++ split; intro Hnone; exact Hnone.
                 ++ split.
                    ** intros m [Hlin Hno]. split; [exact Hlin|split; [exact Hno|congruence]].
                    ** split.
                       --- intros m ret Hret. exact Hret.
                       --- split.
                           +++ intros m [Hlin | [ret Hret]]; [left | right; exists ret]; exact Hlin || exact Hret.
                           +++ intros Hno. split; [exact Hno|congruence].
    	            - destruct Hpre as [HI [Hlin Hno]].
            unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            pupdate_start_mid.
            pupdate_forward_mid t2 (InvEv (push v)).
            pupdate_forward_mid t2 (ResEv (push v) tt).
            pupdate_forward_mid t1 (@InvEv (EStack A) (@pop A));
              try (rewrite PositiveMap.gso by congruence;
                   rewrite PositiveMap.gso by congruence;
                   exact Hex).
            pupdate_forward_mid t1 (@ResEv (EStack A) (@pop A) (Some v)).
            pupdate_finish_mid.
            split.
    	                + split.
    	                  * split; [reflexivity|].
    	                    simpl. split.
    	                    -- split.
                     ++ rewrite PositiveMap.gss. reflexivity.
                     ++ rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gss. reflexivity.
    	                    -- congruence.
    	                  * right. exists tt.
    	                    unfold ALin; simpl.
                rewrite PositiveMap.gso by congruence.
                rewrite PositiveMap.gso by congruence.
                rewrite PositiveMap.gss. reflexivity.
            + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy, Conj.
              split.
    	                  * split; [reflexivity|].
    	                    simpl. split.
    	                    -- split.
                     ++ rewrite PositiveMap.gss. reflexivity.
                     ++ rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gso by congruence.
                        rewrite PositiveMap.gss. reflexivity.
    	                    -- congruence.
              * intros t' Hneq.
                simpl.
                destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
                -- split.
                   ++ split; intro Hnone.
                      ** rewrite Hex in Hnone. discriminate.
                      ** rewrite PositiveMap.gss in Hnone. discriminate.
                   ++ split.
                      ** intros m [Hinv Hno']. contradiction.
                      ** split.
                         --- intros m ret Hret.
                             rewrite Hex in Hret. discriminate.
                         --- split.
    	                                 +++ intros m [Hinv | [ret Hret]].
    	                                     { destruct m as [x|].
                                     - simpl in Hinv. rewrite Hex in Hinv. discriminate.
                                     - right. exists (Some v).
                                       simpl. rewrite PositiveMap.gss. reflexivity. }
    	                                     { simpl in Hret. rewrite Hex in Hret. discriminate. }
                             +++ intros Hno'. contradiction.
    	                    -- assert (Hne2 : t' <> t2) by congruence.
                   simpl in *.
    	                       split.
                   ++ split; intro Hnone.
                      ** repeat (rewrite PositiveMap.gso by congruence). exact Hnone.
                      ** repeat (rewrite PositiveMap.gso in Hnone by congruence). exact Hnone.
                   ++ split.
    	                          ** intros m [Hinv Hno']. simpl in Hinv. split.
    	                             --- simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv.
                         --- split; [exact Hno'|exact Hne2].
                      ** split.
    	                             --- intros m ret Hret. simpl in Hret.
    	                                 simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret.
                         --- split.
    	                                 +++ intros m [Hinv | [ret Hret]].
    	                                     { simpl in Hinv. left. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv. }
    	                                     { simpl in Hret. right. exists ret. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret. }
    	                                 +++ intros Hno'. split; [exact Hno'|exact Hne2].
    	          }
    * intros ret.
      pupdate_intros_atomic_mid.
    	          { 
    	            pupdate_finish_mid; split.
        + destruct Hpre as [HI Hlive].
          unfold I, mid_stack_state, mid_exch_state, Live, Done, ALin in *; simpl in *.
          destruct HI as [Hr [Hex Hdist]]. subst ρ1.
          split; [split; [reflexivity|split; auto]|].
          split; [exact Hex|auto].
        + unfold G. split.
          * destruct Hpre as [HI Hlive].
            unfold I in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            split; [reflexivity|split; auto].
          * intros t' Hneq.
    	                eapply R_pres_same_π. simpl. intros Hno'. constructor.
        }
    	          { 
    	            destruct v2 as [rv|].
        + pupdate_finish_mid; split.
          * destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            destruct Hex as [Hcur Hother].
            split.
            -- repeat split; auto.
    	                -- first [ exact Hdist | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          * unfold G. split.
            -- destruct Hpre as [HI Hlive].
               unfold I in *; simpl in *.
               destruct HI as [Hr [Hex Hdist]]. subst ρ1.
               destruct Hex as [Hcur Hother].
               repeat split; auto.
            -- intros t' Hneq.
               eapply R_pres_same_π. simpl.
               intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
        + pupdate_finish_mid; split.
          * destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            destruct Hex as [Hcur Hother].
            split.
            -- repeat split; auto.
            -- first [ exact Hdist | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          * unfold G. split.
            -- destruct Hpre as [HI Hlive].
               unfold I in *; simpl in *.
               destruct HI as [Hr [Hex Hdist]]. subst ρ1.
               destruct Hex as [Hcur Hother].
               repeat split; auto.
            -- intros t' Hneq.
               eapply R_pres_same_π. simpl.
               intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
        }
    	          { 
    	            destruct v1 as [rv|].
        + pupdate_finish_mid; split.
          * destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            split.
    	                -- repeat split; auto.
    		                -- first [ exact Logic.I | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          * unfold G. split.
            -- destruct Hpre as [HI Hlive].
               unfold I in *; simpl in *.
               destruct HI as [Hr [Hex Hdist]]. subst ρ1.
    	                   repeat split; auto.
            -- intros t' Hneq.
    	                   eapply R_pres_same_π. simpl. intros Hno'. constructor.
        + pupdate_finish_mid; split.
          * destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            split.
    	                -- repeat split; auto.
    	                -- first [ exact Logic.I | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          * unfold G. split.
            -- destruct Hpre as [HI Hlive].
               unfold I in *; simpl in *.
               destruct HI as [Hr [Hex Hdist]]. subst ρ1.
    	                   repeat split; auto.
            -- intros t' Hneq.
    	                   eapply R_pres_same_π. simpl. intros Hno'. constructor.
        }
    * intros [[ov|]|].
      { eapply provable_vis_safe with
          (P' := I //\\ Active t (push v))
          (Q' := fun succ =>
            match succ with
            | OK _ => I //\\ ALin t (Semantics.Semantics.ls_linr (push v) tt) //\\ NoExchBy t
            | FAIL => I //\\ Active t (push v)
            end);
        try solve_conj_impl;
        try solve_conj_stable ebstack_mid_stable;
        try (intro succ; destruct succ; solve_conj_stable ebstack_mid_stable);
        try solve [apply no_error].
        + intros succ; destruct succ; solve_conj_impl.
        + pupdate_intros_atomic_mid.
          pupdate_finish_mid; split.
          * destruct Hpre as [HI Hact].
            unfold I in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]].
            split; [split; [solve_idle_eq|split; [exact Hex|exact Hdist]]|exact Hact].
          * unfold G. split.
    	                -- destruct Hpre as [HI Hact].
    	                   unfold I in *; simpl in *.
    	                   destruct HI as [Hr [Hex Hdist]].
    	                   split; [solve_idle_eq|split; [exact Hex|exact Hdist]].
    	                -- intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno; exact Hno.
            + intros [[]|].
    	              * pupdate_intros_atomic_mid.
              {
    	                  destruct Hpre as [HI [Hlin Hno]].
                unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                pupdate_start_mid.
                pupdate_forward_mid t (InvEv (push v0)).
                pupdate_forward_mid t (ResEv (push v0) tt).
                pupdate_finish_mid.
                split.
                - repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto;
                  try (unfold ALin; simpl; rewrite PositiveMap.gss; reflexivity).
                - unfold G. split.
                  { repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto. }
                  { intros t' Hneq.
                    eapply R_pres_add_add_other; [exact Hneq|].
                    simpl. intros Hno'; exact Hno'. }
              }
            * pupdate_intros_atomic_mid.
              {
                pupdate_finish_mid; split.
                - destruct Hpre as [HI Hact].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]].
                  split; [split; [solve_idle_eq|split; [exact Hex|exact Hdist]]|exact Hact].
                - unfold G. split.
                  + destruct Hpre as [HI Hact].
                    unfold I in *; simpl in *.
                    destruct HI as [Hr [Hex Hdist]].
                    split; [solve_idle_eq|split; [exact Hex|exact Hdist]].
                  + intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno; exact Hno.
              }
    	            + { intros [[]|]; eapply provable_ret_safe;
                try solve_conj_impl;
                try (unfold Conj; intros s [[HI0 Hlin0] Hno0]; split; [exact HI0|split; [exact Hlin0|exact Hno0]]);
                try exact ImplRefl;
                try solve_conj_stable ebstack_mid_stable. }
      }
      { eapply provable_ret_safe;
        try solve_conj_impl;
        try (unfold Conj; intros s [HI0 [Hlin0 Hno0]]; split; [split; [exact HI0|exact Hlin0]|exact Hno0]);
        try (unfold Conj; intros s [[HI0 Hlin0] Hno0]; split; [exact HI0|split; [exact Hlin0|exact Hno0]]);
        try exact ImplRefl;
        try solve_conj_stable ebstack_mid_stable.
      }
      { eapply provable_vis_safe with
          (P' := I //\\ Active t (push v))
          (Q' := fun succ =>
            match succ with
            | OK _ => I //\\ ALin t (Semantics.Semantics.ls_linr (push v) tt) //\\ NoExchBy t
            | FAIL => I //\\ Active t (push v)
            end);
        try solve_conj_impl;
        try solve_conj_stable ebstack_mid_stable;
        try (intro succ; destruct succ; solve_conj_stable ebstack_mid_stable);
        try solve [apply no_error].
        + intros succ; destruct succ; solve_conj_impl.
        + pupdate_intros_atomic_mid.
          pupdate_finish_mid; split.
          * destruct Hpre as [HI Hact].
            unfold I in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]].
            split; [split; [solve_idle_eq|split; [exact Hex|exact Hdist]]|exact Hact].
          * unfold G. split.
    	                -- destruct Hpre as [HI Hact].
    	                   unfold I in *; simpl in *.
    	                   destruct HI as [Hr [Hex Hdist]].
    	                   split; [solve_idle_eq|split; [exact Hex|exact Hdist]].
    	                -- intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno; exact Hno.
    	            + intros [[]|].
            * pupdate_intros_atomic_mid.
              {
                destruct Hpre as [HI [Hlin Hno]].
                unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]]. subst ρ1.
                pupdate_start_mid.
                pupdate_forward_mid t (InvEv (push v0)).
                pupdate_forward_mid t (ResEv (push v0) tt).
                pupdate_finish_mid.
                split.
                - repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto;
                  try (unfold ALin; simpl; rewrite PositiveMap.gss; reflexivity).
                - unfold G. split.
                  { repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto. }
                  { intros t' Hneq.
                    eapply R_pres_add_add_other; [exact Hneq|].
                    simpl. intros Hno'; exact Hno'. }
              }
            * pupdate_intros_atomic_mid.
              {
                pupdate_finish_mid; split.
                - destruct Hpre as [HI Hact].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]].
                  split; [split; [solve_idle_eq|split; [exact Hex|exact Hdist]]|exact Hact].
                - unfold G. split.
                  + destruct Hpre as [HI Hact].
                    unfold I in *; simpl in *.
                    destruct HI as [Hr [Hex Hdist]].
                    split; [solve_idle_eq|split; [exact Hex|exact Hdist]].
                  + intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno; exact Hno.
              }
    	            + { intros [[]|]; eapply provable_ret_safe;
                try solve_conj_impl;
                try (unfold Conj; intros s [[HI0 Hlin0] Hno0]; split; [exact HI0|split; [exact Hlin0|exact Hno0]]);
                try exact ImplRefl;
                try solve_conj_stable ebstack_mid_stable. }
      }
  Qed.

  Definition try_pop_ret_obs (ev : @Event (ETryStack A)) : option (TryResult (option A)) :=
    match ev with
    | ResEv TryStackSpec.pop ret => Some ret
    | _ => None
    end.

  Lemma step_try_pop_some_not_same t (x : A) stk :
    ~ StepTryStack {| te_tid := t; te_ev := ResEv TryStackSpec.pop (OK (Some x)) |} stk stk.
  Proof.
    intros Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    all: try match goal with
    | H : cons _ _ = _ |- _ =>
        apply (f_equal (@length _)) in H; simpl in H; lia
    | H : _ = cons _ _ |- _ =>
        apply (f_equal (@length _)) in H; simpl in H; lia
    end.
    all: try match goal with
    | H : ResEv _ (OK (Some _)) = ResEv _ FAIL |- _ =>
        apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
    | H : ResEv _ (OK (Some _)) = ResEv _ (OK None) |- _ =>
        apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
    end.
  Qed.

  Lemma step_try_pop_none_not_cons t (x : A) stk stk' :
    ~ StepTryStack {| te_tid := t; te_ev := ResEv TryStackSpec.pop (OK None) |} (x :: stk) stk'.
  Proof.
    intros Hstep.
    inversion Hstep; subst; try discriminate; try congruence.
    all: try match goal with
    | H : ResEv _ (OK None) = ResEv _ FAIL |- _ =>
        apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
    | H : ResEv _ (OK None) = ResEv _ (OK (Some _)) |- _ =>
        apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
    end.
  Qed.
  Lemma ebstack_pop_triple t :
    [li_lts Fmid, li_lts F, R t, G t, I, t] ⊢
      {{ I //\\ Active t StackSpec.pop }}
      pop_impl t
      {{ fun ret =>
           I //\\ (ALin t (Semantics.Semantics.ls_linr StackSpec.pop ret) //\\
             NoExchBy t) }}.
Proof.

    Ltac solve_idle_eq_pop :=
      first [ reflexivity
            | match goal with H : ?x = ?y |- ?x = ?y => exact H end
            | match goal with H : ?x = ?y |- ?y = ?x => symmetry; exact H end
            | congruence ].
    Ltac pupdate_intros_atomic_pop_mid :=
      red; intros σ1 ρ1 π1 Hpre σ2 Hstep;
      destruct σ1 as [σl1 σr1]; destruct σ2 as [σl2 σr2];
      simpl in Hstep;
      repeat match type of Hstep with
      | _ /\ _ => destruct Hstep as [Hstep ?]; subst
      end;
      inversion Hstep; subst; clear Hstep;
      repeat match goal with
      | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
      | H : _ = _ |- _ => try discriminate H; try dependent destruction H
      end;
      repeat match goal with
      | H : StepTryStack {| te_tid := _; te_ev := ResEv TryStackSpec.pop (OK (Some _)) |} ?xs ?xs |- _ =>
          exfalso; eapply step_try_pop_some_not_same; exact H
      | H : StepTryStack {| te_tid := _; te_ev := ResEv TryStackSpec.pop (OK None) |} (cons _ _) _ |- _ =>
          exfalso; eapply step_try_pop_none_not_cons; exact H
      | H : StepTryStack _ _ _ |- _ => inversion H; subst; clear H; try congruence
      | H : StepExch _ _ _ |- _ => inversion H; subst; clear H; try congruence
      end;
      repeat match goal with
      | H : @ResEv (ETryStack _) TryStackSpec.pop (OK _) = @ResEv (ETryStack _) TryStackSpec.pop (OK _) |- _ =>
          apply (f_equal try_pop_ret_obs) in H; simpl in H; inversion H; subst; clear H
      | H : @ResEv (ETryStack _) TryStackSpec.pop (OK _) = @ResEv (ETryStack _) TryStackSpec.pop FAIL |- _ =>
          exfalso; apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
      | H : @ResEv (ETryStack _) TryStackSpec.pop FAIL = @ResEv (ETryStack _) TryStackSpec.pop (OK _) |- _ =>
          exfalso; apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
      | H : @ResEv (ETryStack _) TryStackSpec.pop (OK (Some _)) = @ResEv (ETryStack _) TryStackSpec.pop FAIL |- _ =>
          exfalso; apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
      | H : @ResEv (ETryStack _) TryStackSpec.pop FAIL = @ResEv (ETryStack _) TryStackSpec.pop (OK (Some _)) |- _ =>
          exfalso; apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
      | H : @ResEv (ETryStack _) TryStackSpec.pop (OK None) = @ResEv (ETryStack _) TryStackSpec.pop FAIL |- _ =>
          exfalso; apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
      | H : @ResEv (ETryStack _) TryStackSpec.pop FAIL = @ResEv (ETryStack _) TryStackSpec.pop (OK None) |- _ =>
          exfalso; apply (f_equal try_pop_ret_obs) in H; simpl in H; discriminate
      | H : existT _ _ _ = existT _ _ _ |- _ => dependent destruction H
      | H : _ = _ |- _ => try discriminate H; try dependent destruction H
      end;
      repeat match goal with
      | H : cons _ _ = _ |- _ => exfalso; apply (f_equal (@length _)) in H; simpl in H; lia
      | H : _ = cons _ _ |- _ => exfalso; apply (f_equal (@length _)) in H; simpl in H; lia
      end;
      simpl in *.
    Ltac pupdate_finish_pop_mid :=
      try solve [apply rt_refl];
      try (eexists; eexists; split; [apply rt_refl|]).
    Ltac pupdate_start_pop_mid := eexists; eexists; split.
    Tactic Notation "pupdate_forward_pop_mid" constr(tid0) constr(ev) :=
      eapply rt_trans;
      [ eapply rt_step;
        lazymatch ev with
        | InvEv ?f => eapply (Semantics.ps_inv tid0 f)
        | ResEv ?f ?ret => eapply (Semantics.ps_ret tid0 f ret)
        end; [cbn; constructor; constructor
             | simpl; try rewrite PositiveMap.gss;
               try (rewrite PositiveMap.gso by congruence);
               try (rewrite PositiveMap.gso by congruence); eauto]
      | ].

    simpl. unfold pop_impl.
    eapply provable_doloop;
    try solve_conj_impl;
    try solve_conj_stable ebstack_mid_stable.
    eapply provable_vis_safe with
      (P' := I //\\ Live t pop)
      (Q' := fun other =>
        match other with
        | Some (Some x) => I //\\ ALin t (Semantics.Semantics.ls_linr pop (Some x)) //\\ NoExchBy t
        | _ => I //\\ Active t pop
        end);
    try solve_conj_impl;
    try solve_conj_stable ebstack_mid_stable;
    try (intro other; destruct other as [[ov|]|]; try destruct ov; solve_conj_stable ebstack_mid_stable);
    try solve [apply no_error].
    * intros [[ov|]|]; try destruct ov; solve_conj_impl.
    * pupdate_intros_atomic_pop_mid.
      {
        pupdate_finish_pop_mid; split.
        - destruct Hpre as [HI [Hlin Hno]].
          unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
          split.
          + destruct HI as [Hr _]. split; [solve_idle_eq_pop|split; [exact Hlin|auto]].
          + left. exact Hlin.
        - unfold G, R_pres, Active, Live, Done, ALin, NoExchBy, Conj.
          split.
          + destruct Hpre as [HI [Hlin Hno]].
            unfold I in *; simpl in *.
            destruct HI as [Hr _]. split; [solve_idle_eq_pop|split; [exact Hlin|auto]].
          + intros t' Hneq; simpl.
            split.
            -- split; intro H; exact H.
            -- split.
               ++ intros m [Hlin Hno]. split; [exact Hlin|congruence].
               ++ split.
                  ** intros m ret Hlin. exact Hlin.
                  ** split.
                     --- intros m [Hlin | [ret Hlin]]; [left | right; exists ret]; exact Hlin.
                     --- intros _. congruence.
      }
      {
        destruct v1 as [w|].
        - destruct Hpre as [HI [Hlin Hno]].
          unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
          destruct HI as [Hr [Hex Hdist]]. subst ρ1.
          pupdate_start_pop_mid.
          pupdate_forward_pop_mid t1 (InvEv (push w)).
          pupdate_forward_pop_mid t1 (ResEv (push w) tt).
          pupdate_forward_pop_mid t2 (@InvEv (EStack A) (@pop A));
            try (rewrite PositiveMap.gso by congruence;
                 rewrite PositiveMap.gso by congruence;
                 exact Hlin).
          pupdate_forward_pop_mid t2 (@ResEv (EStack A) (@pop A) (Some w)).
          pupdate_finish_pop_mid.
          split.
          + split.
            * split; [reflexivity|].
              simpl. split.
              -- split.
                 ++ rewrite PositiveMap.gso by congruence.
                    rewrite PositiveMap.gso by congruence.
                    rewrite PositiveMap.gss. reflexivity.
                 ++ rewrite PositiveMap.gss. reflexivity.
              -- congruence.
            * right. exists (Some w).
              unfold ALin; simpl. rewrite PositiveMap.gss. reflexivity.
          + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy, Conj.
            split.
            * split; [reflexivity|].
              simpl. split.
              -- split.
                 ++ rewrite PositiveMap.gso by congruence.
                    rewrite PositiveMap.gso by congruence.
                    rewrite PositiveMap.gss. reflexivity.
                 ++ rewrite PositiveMap.gss. reflexivity.
              -- congruence.
            * intros t' Hneq.
              simpl.
              destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
              -- split.
                 ++ split; intro Hnone.
                    ** rewrite Hex in Hnone. discriminate.
                    ** simpl in Hnone.
                       rewrite PositiveMap.gso in Hnone by congruence.
                       rewrite PositiveMap.gso in Hnone by congruence.
                       rewrite PositiveMap.gss in Hnone. discriminate.
                 ++ split.
                    ** intros m [Hinv Hno']. contradiction.
                    ** split.
                       --- intros m ret Hret.
                           simpl in Hret. rewrite Hex in Hret. discriminate.
                       --- split.
                           +++ intros m [Hinv | [ret Hret]].
    	                                   { destruct m as [x|].
    	                                     - right. exists tt. simpl.
                                   simpl in Hinv. rewrite Hex in Hinv.
                                   inversion Hinv; subst.
    	                                       rewrite PositiveMap.gso by congruence.
    	                                       rewrite PositiveMap.gso by congruence.
    	                                       rewrite PositiveMap.gss. reflexivity.
                                 - simpl in Hinv. rewrite Hex in Hinv. discriminate. }
                               { simpl in Hret. rewrite Hex in Hret. discriminate. }
                           +++ intros Hno'. contradiction.
              -- assert (Hne2 : t' <> t2) by congruence.
                 simpl in *.
                 split.
                 ++ split; intro Hnone.
                    ** repeat (rewrite PositiveMap.gso by congruence). exact Hnone.
                    ** repeat (rewrite PositiveMap.gso in Hnone by congruence). exact Hnone.
                 ++ split.
                    ** intros m [Hinv Hno']. simpl in Hinv. split.
                       --- simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv.
                       --- split; [exact Hno'|exact Hne2].
                    ** split.
                       --- intros m ret Hret. simpl in Hret.
                           simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret.
                       --- split.
                           +++ intros m [Hinv | [ret Hret]].
                               { simpl in Hinv. left. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hinv. }
                               { simpl in Hret. right. exists ret. simpl. repeat (rewrite PositiveMap.gso by congruence). exact Hret. }
                           +++ intros Hno'. split; [exact Hno'|exact Hne2].
        - pupdate_finish_pop_mid; split.
          + destruct Hpre as [HI [Hlin Hno]].
            unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]].
            split; [split; [solve_idle_eq_pop|split; [split; [exact Hex|exact Hlin]|congruence]]|left; exact Hlin].
          + unfold G, R_pres, Active, Live, Done, ALin, NoExchBy, Conj.
            split.
            * destruct Hpre as [HI [Hlin Hno]].
              unfold I, mid_stack_state, mid_exch_state, Active, ALin in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]].
              split; [solve_idle_eq_pop|split; [split; [exact Hex|exact Hlin]|congruence]].
            * intros t' Hneq; simpl.
              destruct (PositiveMap.E.eq_dec t' t1) as [Heq|Hne1]; subst.
              -- split.
                 ++ split; intro Hnone.
                    ** destruct Hpre as [HI [Hlin Hno]].
                       unfold I in HI; simpl in HI.
                       destruct HI as [_ [Hex _]].
                       rewrite Hex in Hnone. discriminate.
                    ** destruct Hpre as [HI [Hlin Hno]].
                       unfold I in HI; simpl in HI.
                       destruct HI as [_ [Hex _]].
                       rewrite Hex in Hnone. discriminate.
                 ++ split.
                    ** intros m [Hlin Hno]. contradiction.
                    ** split.
                       --- intros m ret Hret.
                           destruct Hpre as [HI _].
                           unfold I in HI; simpl in HI.
                           destruct HI as [_ [Hex _]].
                           simpl in Hret. rewrite Hex in Hret. discriminate.
                       --- split.
                           +++ intros m [Hlin | [ret Hret]].
                               { left; exact Hlin. }
                               { destruct Hpre as [HI _].
                                 unfold I in HI; simpl in HI.
                                 destruct HI as [_ [Hex _]].
                                 simpl in Hret.
                                 rewrite Hex in Hret. discriminate. }
                           +++ intros Hno. contradiction.
              -- split.
                 ++ split; intro Hnone; exact Hnone.
                 ++ split.
                    ** intros m [Hlin Hno]. split; [exact Hlin|split; [exact Hno|congruence]].
                    ** split.
                       --- intros m ret Hret. exact Hret.
                       --- split.
                           +++ intros m [Hlin | [ret Hret]]; [left | right; exists ret]; exact Hlin || exact Hret.
                           +++ intros Hno. split; [exact Hno|congruence].
      }
    * intros ret.
      pupdate_intros_atomic_pop_mid.
      {
        
        pupdate_finish_pop_mid; split.
        - destruct Hpre as [HI Hlive].
          unfold I, mid_stack_state, mid_exch_state, Live, Done, ALin in *; simpl in *.
          destruct HI as [Hr [Hex Hdist]]. subst ρ1.
          split; [repeat split; auto|].
          first [ exact Logic.I | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
        - unfold G. split.
          + destruct Hpre as [HI Hlive].
            unfold I in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            repeat split; auto.
          + intros t' Hneq.
            eapply R_pres_same_π. simpl. intros Hno'. constructor.
      }
      {
        
        destruct v2 as [w|].
        - pupdate_finish_pop_mid; split.
          + destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            destruct Hex as [Hcur Hother].
            split.
            * repeat split; auto.
            * first [ exact Hdist | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          + unfold G. split.
            * destruct Hpre as [HI Hlive].
              unfold I in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              destruct Hex as [Hcur Hother].
              repeat split; auto.
            * intros t' Hneq.
              eapply R_pres_same_π. simpl.
              intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
        - pupdate_finish_pop_mid; split.
          + destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            destruct Hex as [Hcur Hother].
            split.
            * repeat split; auto.
            * first [ exact Hdist | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          + unfold G. split.
            * destruct Hpre as [HI Hlive].
              unfold I in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              destruct Hex as [Hcur Hother].
              repeat split; auto.
            * intros t' Hneq.
              eapply R_pres_same_π. simpl.
              intros Hno'. destruct Hno' as [_ Hneq2]. exact Hneq2.
      }
      {
        
        destruct v1 as [w|].
        - pupdate_finish_pop_mid; split.
          + destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Active, Live, Done, ALin, NoExchBy, Conj in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            split.
            * repeat split; auto.
            * first [ exact Logic.I | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          + unfold G. split.
            * destruct Hpre as [HI Hlive].
              unfold I in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              repeat split; auto.
            * intros t' Hneq.
              eapply R_pres_same_π. simpl. intros Hno'. constructor.
        - pupdate_finish_pop_mid; split.
          + destruct Hpre as [HI Hlive].
            unfold I, mid_stack_state, mid_exch_state, Live, Done, Active, ALin, NoExchBy in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]]. subst ρ1.
            split.
            * repeat split; auto.
            * first [ exact Logic.I | cbv beta delta [Logics.Conj]; simpl; refine (conj _ _); eauto ].
          + unfold G. split.
            * destruct Hpre as [HI Hlive].
              unfold I in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              repeat split; auto.
    	                * intros t' Hneq.
    	                  eapply R_pres_same_π. simpl. intros Hno'. constructor.
    	          }
    * intros [[ov|]|].
      { eapply provable_ret_safe;
        try solve_conj_impl;
        try (unfold Conj; intros s [[HI0 Hlin0] Hno0]; split; [exact HI0|split; [exact Hlin0|exact Hno0]]);
        try (unfold Conj; intros s [HI0 [Hlin0 Hno0]]; split; [split; [exact HI0|exact Hlin0]|exact Hno0]);
        try exact ImplRefl;
        try solve_conj_stable ebstack_mid_stable.
      }
      { eapply provable_vis_safe with
          (P' := I //\\ Active t pop)
          (Q' := fun succ =>
            match succ with
            | OK v => I //\\ ALin t (Semantics.Semantics.ls_linr pop v) //\\ NoExchBy t
            | FAIL => I //\\ Active t pop
            end);
        try solve_conj_impl;
        try solve_conj_stable ebstack_mid_stable;
        try (intro succ; destruct succ; solve_conj_stable ebstack_mid_stable);
        try solve [apply no_error].
        + intros succ; destruct succ; solve_conj_impl.
        + pupdate_intros_atomic_pop_mid.
          pupdate_finish_pop_mid; split.
          * destruct Hpre as [HI Hact].
            unfold I in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]].
            split; [split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]]|exact Hact].
          * unfold G. split.
            -- destruct Hpre as [HI Hact].
               unfold I in *; simpl in *.
               destruct HI as [Hr [Hex Hdist]].
               split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]].
            -- intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno'; exact Hno'.
    	            + intros [retv|].
    	              * pupdate_intros_atomic_pop_mid.
            {
              destruct Hpre as [HI [Hlin Hno]].
              unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              pupdate_start_pop_mid.
              pupdate_forward_pop_mid t (@InvEv (EStack A) (@pop A)).
    		                  pupdate_forward_pop_mid t (@ResEv (EStack A) (@pop A) None);
                try rewrite PositiveMap.gss; auto.
              pupdate_finish_pop_mid.
              split.
              - repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto;
                try (unfold ALin; simpl; rewrite PositiveMap.gss; reflexivity).
              - unfold G. split.
                { repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto. }
                { intros t' Hneq.
                  eapply R_pres_add_add_other; [exact Hneq|].
                  simpl. intros Hno'; exact Hno'. }
            }
          {
              destruct Hpre as [HI [Hlin Hno]].
              unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              pupdate_start_pop_mid.
              pupdate_forward_pop_mid t (@InvEv (EStack A) (@pop A)).
    	                  pupdate_forward_pop_mid t (@ResEv (EStack A) (@pop A) (Some v));
                try rewrite PositiveMap.gss; auto.
              pupdate_finish_pop_mid.
              split.
              - repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto;
                try (unfold ALin; simpl; rewrite PositiveMap.gss; reflexivity).
              - unfold G. split.
                { repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto. }
                { intros t' Hneq.
                  eapply R_pres_add_add_other; [exact Hneq|].
                  simpl. intros Hno'; exact Hno'. }
    	                }
    	              * pupdate_intros_atomic_pop_mid.
            {
    	                  pupdate_finish_pop_mid; split.
              - destruct Hpre as [HI Hact].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]].
                split; [split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]]|exact Hact].
              - unfold G. split.
                + destruct Hpre as [HI Hact].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]].
                  split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]].
                + intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno'; exact Hno'.
            }
        + { intros [retv|]; eapply provable_ret_safe;
            try solve_conj_impl;
            try (unfold Conj; intros s [[HI0 Hlin0] Hno0]; split; [exact HI0|split; [exact Hlin0|exact Hno0]]);
            try exact ImplRefl;
            try solve_conj_stable ebstack_mid_stable. }
      }
      { eapply provable_vis_safe with
          (P' := I //\\ Active t pop)
          (Q' := fun succ =>
            match succ with
            | OK v => I //\\ ALin t (Semantics.Semantics.ls_linr pop v) //\\ NoExchBy t
            | FAIL => I //\\ Active t pop
            end);
        try solve_conj_impl;
        try solve_conj_stable ebstack_mid_stable;
        try (intro succ; destruct succ; solve_conj_stable ebstack_mid_stable);
        try solve [apply no_error].
        + intros succ; destruct succ; solve_conj_impl.
        + pupdate_intros_atomic_pop_mid.
          pupdate_finish_pop_mid; split.
          * destruct Hpre as [HI Hact].
            unfold I in *; simpl in *.
            destruct HI as [Hr [Hex Hdist]].
            split; [split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]]|exact Hact].
          * unfold G. split.
            -- destruct Hpre as [HI Hact].
               unfold I in *; simpl in *.
               destruct HI as [Hr [Hex Hdist]].
               split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]].
            -- intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno'; exact Hno'.
        + intros [retv|].
          * pupdate_intros_atomic_pop_mid.
            {
              destruct Hpre as [HI [Hlin Hno]].
              unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              pupdate_start_pop_mid.
              pupdate_forward_pop_mid t (@InvEv (EStack A) (@pop A)).
    	                  pupdate_forward_pop_mid t (@ResEv (EStack A) (@pop A) None);
                try rewrite PositiveMap.gss; auto.
              pupdate_finish_pop_mid.
              split.
              - repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto;
                try (unfold ALin; simpl; rewrite PositiveMap.gss; reflexivity).
              - unfold G. split.
                { repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto. }
                { intros t' Hneq.
                  eapply R_pres_add_add_other; [exact Hneq|].
                  simpl. intros Hno'; exact Hno'. }
    	                }
    	              {
    	                  destruct Hpre as [HI [Hlin Hno]].
              unfold I, mid_stack_state, mid_exch_state, Active, ALin, NoExchBy in *; simpl in *.
              destruct HI as [Hr [Hex Hdist]]. subst ρ1.
              pupdate_start_pop_mid.
              pupdate_forward_pop_mid t (@InvEv (EStack A) (@pop A)).
    	                  pupdate_forward_pop_mid t (@ResEv (EStack A) (@pop A) (Some v));
                try rewrite PositiveMap.gss; auto.
              pupdate_finish_pop_mid.
              split.
              - repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto;
                try (unfold ALin; simpl; rewrite PositiveMap.gss; reflexivity).
              - unfold G. split.
                { repeat split; try reflexivity; try eapply exch_ok_add_add_no_exch; eauto. }
                { intros t' Hneq.
                  eapply R_pres_add_add_other; [exact Hneq|].
                  simpl. intros Hno'; exact Hno'. }
            }
          * pupdate_intros_atomic_pop_mid.
            {
              pupdate_finish_pop_mid; split.
              - destruct Hpre as [HI Hact].
                unfold I in *; simpl in *.
                destruct HI as [Hr [Hex Hdist]].
                split; [split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]]|exact Hact].
              - unfold G. split.
                + destruct Hpre as [HI Hact].
                  unfold I in *; simpl in *.
                  destruct HI as [Hr [Hex Hdist]].
                  split; [solve_idle_eq_pop|split; [exact Hex|exact Hdist]].
                + intros t' Hneq. eapply R_pres_same_π. simpl. intros Hno'; exact Hno'.
            }
        + { intros [retv|]; eapply provable_ret_safe;
            try solve_conj_impl;
            try (unfold Conj; intros s [[HI0 Hlin0] Hno0]; split; [exact HI0|split; [exact Hlin0|exact Hno0]]);
            try exact ImplRefl;
            try solve_conj_stable ebstack_mid_stable. }
      }
  Qed.

  Lemma ebstack_push_method t v :
    MethodProvable (li_lts Fmid) (li_lts F) ebstack_impl
      (R t) (G t) I t (StackSpec.push v)
      (I //\\ Active t (StackSpec.push v))
      (fun _ =>
         I //\\ (ALin t (Semantics.Semantics.ls_linr (StackSpec.push v) tt) //\\
           NoExchBy t)).
  Proof.
    constructor.
    - apply IGinvActive.
    - solve_conj_impl.
    - solve_conj_stable ebstack_mid_stable.
    - intros [].
      apply IGretNoExch.
    - unfold ALin. intros [] σ0 ρ0 π0 [HI [Hlin Hno]].
      exact Hlin.
    - simpl. apply ebstack_push_triple.
  Qed.

  Lemma ebstack_pop_method t :
    MethodProvable (li_lts Fmid) (li_lts F) ebstack_impl
      (R t) (G t) I t StackSpec.pop
      (I //\\ Active t StackSpec.pop)
      (fun ret =>
         I //\\ (ALin t (Semantics.Semantics.ls_linr StackSpec.pop ret) //\\
           NoExchBy t)).
  Proof.
    constructor.
    - apply IGinvActive.
    - solve_conj_impl.
    - solve_conj_stable ebstack_mid_stable.
    - intros ret.
      apply IGretNoExch.
    - unfold ALin. intros ret σ0 ρ0 π0 [HI [Hlin Hno]].
      exact Hlin.
    - simpl. apply ebstack_pop_triple.
  Qed.

  Lemma ebstack_mid_methods :
    forall t f,
      exists P Q,
        MethodProvable (li_lts Fmid) (li_lts F) ebstack_impl
          (R t) (G t) I t f P Q.
  Proof.
    intros t [v|].
    - eexists. eexists. apply ebstack_push_method.
    - eexists. eexists. apply ebstack_pop_method.
  Qed.

  Lemma ebstack_mid_correct :
    cal ebstack_impl (li_init Fmid) (li_init F).
  Proof.
    eapply RGILogic.soundness with (R:=R) (G:=G) (I:=I).
    - apply mid_valid_rgi.
    - apply mid_cross_rely.
    - apply ebstack_mid_methods.
    - apply mid_init.
  Qed.

  Program Definition MebstackMid : layer_implementation Fmid F := {|
    li_impl := ebstack_impl
  |}.
  Next Obligation.
    apply ebstack_mid_correct.
  Qed.

End EBStackTSOImpl.
