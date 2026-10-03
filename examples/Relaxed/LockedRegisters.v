(** * Two lock-protected registers, end to end

    A concrete instance of [BracketedLink.bracketed_link].  The underlay
    [E0] offers, for each location [x] and [y], a lock ([acq]: mode
    [RFence], [rel]: mode [LFence]) and a register ([rd], [wr]: mode
    [Local]); two calls on different locations are semi-independent when
    the modes allow it, so the underlay is genuinely relaxed: a later
    [acq y] or [rd y] may overtake an earlier [wr x] or [rel x] of the same
    thread.  The module [M0] implements [put(l, v) = acq l; wr l v; rel l]
    and [get(l) = acq l; v <- rd l; rel l; ret v].

    [sb_forbidden]: in every complete execution of [M0], over any underlay
    implementation [VE] whose trace is relaxed linearizable w.r.t. the
    tensor of the lock and register specifications, the store-buffering
    outcome [T1: put(x,1); get(y) = 0 || T2: put(y,1); get(x) = 0] does not
    occur, however the overlay client interleaves its calls. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.BinPos.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Sorting.Sorted.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedModuleFacts.
Require Import examples.Relaxed.BracketedComposition.
Require Import examples.Relaxed.BracketedLink.

Import ListNotations.

Module LockedRegisters.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.

  Abbreviation Loc := BracketedComposition.Loc.
  Abbreviation LX := BracketedComposition.LX.
  Abbreviation LY := BracketedComposition.LY.
  Abbreviation RegOp := BracketedComposition.RegOp.
  Abbreviation Put := BracketedComposition.Put.
  Abbreviation Get := BracketedComposition.Get.
  Abbreviation reg_ok := BracketedComposition.reg_ok.

  (** ** Signatures *)

  Inductive UOp := UAcq (l : Loc) | URel (l : Loc) | URd (l : Loc) | UWr (l : Loc) (v : nat).

  Definition uloc (o : UOp) : Loc := match o with UAcq l | URel l | URd l | UWr l _ => l end.

  Definition umode (o : UOp) : FenceMode :=
    match o with UAcq _ => RFence | URel _ => LFence | _ => Local end.

  Definition USig : Sig.t :=
    {| Sig.op := UOp; Sig.ar := fun o => match o with URd _ => nat | _ => unit end |}.

  Definition E0 : RelaxedSig.t :=
    {| effect := USig;
       handle := nat;
       semi_independent := fun o1 o2 => umode o1 ≤f LFence /\ umode o2 ≤f RFence /\ uloc o1 <> uloc o2;
       mode := umode |}.

  Lemma E0_well_formed : RelaxedSig.well_formed E0.
  Proof.
    constructor.
    - intros o (_ & _ & H). apply H. reflexivity.
    - intros e1 e2 (H & _ & _). exact H.
    - intros e1 e2 (_ & H & _). exact H.
  Qed.

  Inductive FOp := FPut (l : Loc) (v : nat) | FGet (l : Loc).

  Definition floc (o : FOp) : Loc := match o with FPut l _ | FGet l => l end.

  Definition FSig : Sig.t :=
    {| Sig.op := FOp; Sig.ar := fun o => match o with FGet _ => nat | FPut _ _ => unit end |}.

  (** No overlay semi-independence: the conclusion is the strongest one.

      Every operation has mode [RFence].  Its linearization call is its
      acquire (mode [RFence]), and by mode inheritance
      ([WindowComposition], [BracketedWindow]) an operation linearized at
      an acquire can be exported with a mode of at most [RFence].  [Fence]
      would additionally promise that earlier operations of other objects
      are never linearized after the acquire, which the implementation
      does not guarantee (a release may be overtaken by a later acquire of
      another lock).  [BracketedLink.bracketed_link] does not read the
      overlay modes; [BracketedWindow.lock_window_link] does. *)
  Definition F0 : RelaxedSig.t :=
    {| effect := FSig; handle := nat; semi_independent := fun _ _ => False; mode := fun _ => RFence |}.

  Definition is_acq (o : UOp) : bool := match o with UAcq _ => true | _ => false end.
  Definition is_rel (o : UOp) : bool := match o with URel _ => true | _ => false end.

  (** ** The module *)

  Definition bprog (a d r : UOp) : Prog E0 (@Sig.ar USig d) :=
    Future (E := E0) a (fun f => Wait f (fun _ =>
      Future (E := E0) d (fun g => Wait g (fun y =>
        Future (E := E0) r (fun h => Wait h (fun _ => Ret y)))))).

  Definition M0 : RelaxedModuleImpl E0 F0 := fun op t =>
    match op as o return Prog E0 (@Sig.ar (effect F0) o) with
    | FPut l v => bprog (UAcq l) (UWr l v) (URel l)
    | FGet l => bprog (UAcq l) (URd l) (URel l)
    end.

  (** ** The traces of a method *)

  Definition of_nat (o : UOp) : nat -> @Sig.ar USig o :=
    match o as o0 return nat -> @Sig.ar USig o0 with
    | URd _ => fun n => n
    | UAcq _ => fun _ => tt
    | URel _ => fun _ => tt
    | UWr _ _ => fun _ => tt
    end.

  Definition val_of (o : UOp) : @Sig.ar USig o -> nat :=
    match o as o0 return @Sig.ar USig o0 -> nat with
    | URd _ => fun v => v
    | _ => fun _ => 0
    end.

  Lemma of_val : forall o (v : @Sig.ar USig o), of_nat o (val_of o v) = v.
  Proof. intros [l | l | l | l n] v; cbn in *; try destruct v; reflexivity. Qed.

  Section Views.
    Context {R : Type}.

    Definition pshape (p : Prog E0 R) : nat :=
      match p with Future _ _ => 0 | FutureD _ _ _ => 1 | Wait _ _ => 2 | Ret _ => 3 | Tau _ => 4 end.

    Definition fview (p : Prog E0 R) : option (UOp * (nat -> Prog E0 R)) :=
      match p with Future op k => Some (op, fun h => k (MkFutureRef op h)) | _ => None end.

    Definition wview (p : Prog E0 R) : option (UOp * nat * (nat -> Prog E0 R)) :=
      match p with
      | Wait f k =>
          (match f in FutureRef _ A return (A -> Prog E0 R) -> option (UOp * nat * (nat -> Prog E0 R)) with
           | MkFutureRef op h => fun k' => Some (op, h, fun n => k' (of_nat op n))
           end) k
      | _ => None
      end.
  End Views.

  Lemma no_pending_resolved (H : FutureStore E0) h o : all_resolved H -> ~ pending_at h o H.
  Proof.
    intros Hall Hp. unfold all_resolved in Hall. rewrite Forall_forall in Hall. exact (Hall _ Hp).
  Qed.

  Lemma resolve_pending_head (H H' : FutureStore E0) h o h' o' v :
    all_resolved H -> resolve_store h' o' v (Build_FutureEntry h (Pending o) :: H) H' ->
    h' = h /\ o' = o.
  Proof.
    intros Hall Hres. remember (Build_FutureEntry h (Pending o) :: H) as L eqn:HL.
    destruct Hres as [tail | h'' cell H0 H0' Hneq Hres'].
    - injection HL as E1 E2 _. split; assumption.
    - injection HL as _ _ ->. exfalso. apply (no_pending_resolved H h' o' Hall).
      eapply resolve_store_pending; exact Hres'.
  Qed.

  Lemma resolve_pending_result (H H' : FutureStore E0) h o v :
    all_resolved H -> resolve_store h o v (Build_FutureEntry h (Pending o) :: H) H' ->
    H' = Build_FutureEntry h (Resolved o v) :: H.
  Proof.
    intros Hall Hres. remember (Build_FutureEntry h (Pending o) :: H) as L eqn:HL.
    destruct Hres as [tail | h'' cell H0 H0' Hneq Hres'].
    - injection HL as ->. reflexivity.
    - injection HL as _ _ ->. exfalso. apply (no_pending_resolved H h o Hall).
      eapply resolve_store_pending; exact Hres'.
  Qed.

  Lemma not_resolved_pending (H : FutureStore E0) h o o' v :
    ~ In h (map (fe_handle E0) H) -> ~ resolved_at h o' v (Build_FutureEntry h (Pending o) :: H).
  Proof.
    intros Hh [He | He]; [discriminate |]. apply Hh. apply (in_map (fe_handle E0)) in He. exact He.
  Qed.

  Lemma resolved_value (H : FutureStore E0) h o v v' :
    ~ In h (map (fe_handle E0) H) -> resolved_at h o v' (Build_FutureEntry h (Resolved o v) :: H) -> v' = v.
  Proof.
    intros Hh [He | He].
    - apply (f_equal (fun e => match fe_cell E0 e with Resolved o0 x => val_of o0 x | Pending _ => 0 end)) in He.
      cbn in He. rewrite <- (of_val o v), He, of_val. reflexivity.
    - exfalso. apply Hh. apply (in_map (fe_handle E0)) in He. exact He.
  Qed.

  Lemma no_pending_after (H : FutureStore E0) h o v h' o' :
    all_resolved H -> ~ pending_at h' o' (Build_FutureEntry h (Resolved o v) :: H).
  Proof.
    intros Hall [He | He]; [discriminate |]. exact (no_pending_resolved H h' o' Hall He).
  Qed.

  Lemma all_resolved_cons (H : FutureStore E0) h o v :
    all_resolved H -> all_resolved (Build_FutureEntry h (Resolved o v) :: H).
  Proof. intros Hall. constructor; [exact I | exact Hall]. Qed.

  Section Exec.
    Context {R : Type} (t : tid).

    Lemma step_future (o : UOp) (kk : FutureRef E0 (@Sig.ar USig o) -> Prog E0 R) (H : FutureStore E0) (a : TAction E0) (c : ProgramConfig E0 R) :
      program_step_tagged t a (Build_ProgramConfig (Future (E := E0) o kk) H) c -> all_resolved H ->
      exists h : handle E0, a = TEmit (Build_TaggedEvent (Build_ThreadEvent t (@InvEv E0 h o)) (resolved_in H)) /\
        c = Build_ProgramConfig (kk (MkFutureRef (E := E0) o h)) (add_pending h o H) /\ handle_fresh h H.
    Proof.
      intros Hstep Hall. remember (Build_ProgramConfig (Future (E := E0) o kk) H) as c0 eqn:Hc0.
      destruct Hstep.
      - pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H0.
        apply (f_equal (fun c => fview (pc_prog c))) in Hc0. cbn in Hc0.
        injection Hc0 as Hop Hk. subst op.
        exists h. split; [reflexivity |]. split; [| exact Hfresh].
        apply (f_equal (fun F => F h)) in Hk. cbn in Hk. rewrite Hk. reflexivity.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
      - exfalso. apply (f_equal (fun c => pc_futures c)) in Hc0. cbn in Hc0. subst H0.
        apply (no_pending_resolved H h op Hall). eapply resolve_store_pending; exact Hresolve.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
    Qed.

    Lemma step_wait_pending (o : UOp) (k : @Sig.ar USig o -> Prog E0 R) (h : handle E0) (H : FutureStore E0) (a : TAction E0) (c : ProgramConfig E0 R) :
      program_step_tagged t a
        (Build_ProgramConfig (Wait (MkFutureRef (E := E0) o h) k) (Build_FutureEntry h (Pending (E := E0) o) :: H)) c ->
      all_resolved H -> ~ In h (map (fe_handle E0) H) ->
      exists v : @Sig.ar USig o, a = TEmit (Build_TaggedEvent (Build_ThreadEvent t (@ResEv E0 h o v)) no_deps) /\
        (c = Build_ProgramConfig (k v) (Build_FutureEntry h (Resolved (E := E0) o v) :: H) \/
         c = Build_ProgramConfig (Wait (MkFutureRef (E := E0) o h) k) (Build_FutureEntry h (Resolved (E := E0) o v) :: H)).
    Proof.
      intros Hstep Hall Hh.
      remember (Build_ProgramConfig (Wait (MkFutureRef (E := E0) o h) k) (Build_FutureEntry h (Pending (E := E0) o) :: H))
        as c0 eqn:Hc0.
      destruct Hstep.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
      - exfalso. pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H0.
        apply (f_equal (fun c => wview (pc_prog c))) in Hc0. cbn in Hc0.
        injection Hc0 as Hop Hh0 _. subst op h0.
        exact (not_resolved_pending H h o o ret Hh Hresolved).
      - pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H0.
        apply (f_equal (fun c => wview (pc_prog c))) in Hc0. cbn in Hc0.
        injection Hc0 as Hop Hh0 Hk. subst op h0.
        rewrite (resolve_pending_result H H' h o ret Hall Hresolve).
        exists ret. split; [reflexivity |]. left.
        apply (f_equal (fun F => F (val_of o ret))) in Hk. cbn in Hk. rewrite !of_val in Hk.
        rewrite Hk. reflexivity.
      - pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H0.
        apply (f_equal (fun c => pc_prog c)) in Hc0. cbn in Hc0. subst p.
        destruct (resolve_pending_head H H' h o h0 op ret Hall Hresolve) as [-> ->].
        rewrite (resolve_pending_result H H' h o ret Hall Hresolve).
        exists ret. split; [reflexivity |]. right. reflexivity.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
    Qed.

    Lemma step_wait_resolved (o : UOp) (k : @Sig.ar USig o -> Prog E0 R) (h : handle E0) (v : @Sig.ar USig o) (H : FutureStore E0) (a : TAction E0) (c : ProgramConfig E0 R) :
      program_step_tagged t a
        (Build_ProgramConfig (Wait (MkFutureRef (E := E0) o h) k) (Build_FutureEntry h (Resolved (E := E0) o v) :: H)) c ->
      all_resolved H -> ~ In h (map (fe_handle E0) H) ->
      a = TSilent /\ c = Build_ProgramConfig (k v) (Build_FutureEntry h (Resolved (E := E0) o v) :: H).
    Proof.
      intros Hstep Hall Hh.
      remember (Build_ProgramConfig (Wait (MkFutureRef (E := E0) o h) k) (Build_FutureEntry h (Resolved (E := E0) o v) :: H))
        as c0 eqn:Hc0.
      destruct Hstep.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
      - pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H0.
        apply (f_equal (fun c => wview (pc_prog c))) in Hc0. cbn in Hc0.
        injection Hc0 as Hop Hh0 Hk. subst op h0.
        rewrite (resolved_value H h o v ret Hh Hresolved).
        split; [reflexivity |].
        apply (f_equal (fun F => F (val_of o v))) in Hk. cbn in Hk. rewrite !of_val in Hk.
        rewrite Hk. reflexivity.
      - exfalso. pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H0.
        apply (no_pending_after H h o v h0 op Hall). eapply resolve_store_pending; exact Hresolve.
      - exfalso. pose proof (f_equal (fun c => pc_futures c) Hc0) as HH. cbn in HH. subst H0.
        apply (no_pending_after H h o v h0 op Hall). eapply resolve_store_pending; exact Hresolve.
      - apply (f_equal (fun c => pshape (pc_prog c))) in Hc0. discriminate.
    Qed.

    Lemma step_ret (r : R) (H : FutureStore E0) (a : TAction E0) (c : ProgramConfig E0 R) :
      program_step_tagged t a (Build_ProgramConfig (Ret (E := E0) r) H) c -> all_resolved H -> False.
    Proof.
      intros Hstep Hall. remember (Build_ProgramConfig (Ret (E := E0) r) H) as c0 eqn:Hc0.
      destruct Hstep; try (apply (f_equal (fun c => pshape (pc_prog c))) in Hc0; discriminate).
      apply (f_equal (fun c => pc_futures c)) in Hc0. cbn in Hc0. subst H0.
      apply (no_pending_resolved H h op Hall). eapply resolve_store_pending; exact Hresolve.
    Qed.

    Lemma exec_wait_resolved (o : UOp) (k : @Sig.ar USig o -> Prog E0 R) (h : handle E0) (v : @Sig.ar USig o) (H : FutureStore E0) tr (c' : ProgramConfig E0 R) rv :
      program_execution_tagged t
        (Build_ProgramConfig (Wait (MkFutureRef (E := E0) o h) k) (Build_FutureEntry h (Resolved (E := E0) o v) :: H)) tr c' ->
      program_terminal c' rv -> all_resolved H -> ~ In h (map (fe_handle E0) H) ->
      program_execution_tagged t (Build_ProgramConfig (k v) (Build_FutureEntry h (Resolved (E := E0) o v) :: H)) tr c'.
    Proof.
      intros Hexec Hterm Hall Hh. inversion Hexec as [c0 | c1 c2 c3 tr0 Hstep Hexec' | c1 c2 c3 m0 tr0 Hstep Hexec']; subst.
      - inversion Hterm.
      - destruct (step_wait_resolved o k h v H _ _ Hstep Hall Hh) as [_ ->]. exact Hexec'.
      - destruct (step_wait_resolved o k h v H _ _ Hstep Hall Hh) as [Ha _]. discriminate.
    Qed.

    Lemma exec_future_wait (o : UOp) (k : @Sig.ar USig o -> Prog E0 R) (H : FutureStore E0) tr (c' : ProgramConfig E0 R) rv :
      program_execution_tagged t (Build_ProgramConfig (Future (E := E0) o (fun f => Wait f k)) H) tr c' ->
      program_terminal c' rv -> all_resolved H ->
      exists (h : handle E0) (v : @Sig.ar USig o) m1 m2 tr', tr = m1 :: m2 :: tr' /\
        untag m1 = BracketedLink.inv_ev (t, h) o /\ untag m2 = BracketedLink.res_ev (t, h) o v /\
        ~ In h (map (fe_handle E0) H) /\
        program_execution_tagged t (Build_ProgramConfig (k v) (Build_FutureEntry h (Resolved (E := E0) o v) :: H)) tr' c'.
    Proof.
      intros Hexec Hterm Hall.
      inversion Hexec as [c0 | c1 c2 c3 tr0 Hstep Hexec' | c1 c2 c3 m1 tr1 Hstep Hexec']; subst.
      - inversion Hterm.
      - destruct (step_future o _ H _ _ Hstep Hall) as (h & Ha & _). discriminate.
      - destruct (step_future o _ H _ _ Hstep Hall) as (h & Ha & -> & Hfresh).
        injection Ha as ->. cbn in Hexec'. unfold add_pending in Hexec'.
        inversion Hexec' as [c0 | c1 c2 c4 tr0 Hstep' Hexec'' | c1 c2 c4 m2 tr2 Hstep' Hexec'']; subst.
        + inversion Hterm.
        + destruct (step_wait_pending o k h H _ _ Hstep' Hall Hfresh) as (v & Ha & _). discriminate.
        + destruct (step_wait_pending o k h H _ _ Hstep' Hall Hfresh) as (v & Ha & [-> | ->]);
            injection Ha as ->.
          * exists h, v. eexists. eexists. exists tr2. split; [reflexivity |]. split; [reflexivity |].
            split; [reflexivity |]. split; [exact Hfresh | exact Hexec''].
          * exists h, v. eexists. eexists. exists tr2. split; [reflexivity |]. split; [reflexivity |].
            split; [reflexivity |]. split; [exact Hfresh |].
            exact (exec_wait_resolved o k h v H _ _ _ Hexec'' Hterm Hall Hfresh).
    Qed.
  End Exec.

  Lemma bprog_shape t a d r tr (rv : @Sig.ar USig d) :
    program_produces_tagged t (bprog a d r) tr rv ->
    exists (h1 h2 h3 : handle E0) (m1 m2 m3 m4 m5 m6 : TaggedEvent E0) (va : @Sig.ar USig a) (vr : @Sig.ar USig r),
      tr = [m1; m2; m3; m4; m5; m6] /\
      untag m1 = BracketedLink.inv_ev (t, h1) a /\ untag m2 = BracketedLink.res_ev (t, h1) a va /\
      untag m3 = BracketedLink.inv_ev (t, h2) d /\ untag m4 = BracketedLink.res_ev (t, h2) d rv /\
      untag m5 = BracketedLink.inv_ev (t, h3) r /\ untag m6 = BracketedLink.res_ev (t, h3) r vr /\
      h1 <> h2 /\ h1 <> h3 /\ h2 <> h3.
  Proof.
    intros (c' & Hexec & Hterm). unfold initial_program, bprog in Hexec.
    destruct (exec_future_wait t a _ [] _ _ _ Hexec Hterm (Forall_nil _))
      as (h1 & va & m1 & m2 & tr1 & -> & Hm1 & Hm2 & _ & Hexec1).
    cbn beta in Hexec1.
    destruct (exec_future_wait t d _ _ _ _ _ Hexec1 Hterm (all_resolved_cons _ _ _ _ (Forall_nil _)))
      as (h2 & v2 & m3 & m4 & tr2 & -> & Hm3 & Hm4 & Hf2 & Hexec2).
    cbn beta in Hexec2.
    destruct (exec_future_wait t r _ _ _ _ _ Hexec2 Hterm
                (all_resolved_cons _ _ _ _ (all_resolved_cons _ _ _ _ (Forall_nil _))))
      as (h3 & vr & m5 & m6 & tr3 & -> & Hm5 & Hm6 & Hf3 & Hexec3).
    cbn beta in Hexec3.
    inversion Hexec3 as [c0 | c1 c2 c3 tr0 Hstep _ | c1 c2 c3 m0 tr0 Hstep _]; subst.
    - inversion Hterm; subst.
      exists h1, h2, h3, m1, m2, m3, m4, m5, m6, va, vr.
      cbn in Hf2, Hf3.
      repeat split; try assumption; intros ->; tauto.
    - exfalso. eapply step_ret; [exact Hstep |]. repeat apply all_resolved_cons. constructor.
    - exfalso. eapply step_ret; [exact Hstep |]. repeat apply all_resolved_cons. constructor.
  Qed.

  (** ** Instantiating the link *)

  Definition keyE0_dec (k k' : CallKey E0) : {k = k'} + {k <> k'}.
  Proof.
    destruct k as [t h], k' as [t' h'].
    destruct (Pos.eq_dec t t') as [-> | Ht]; [| right; congruence].
    destruct (Nat.eq_dec h h') as [-> | Hh]; [left; reflexivity | right; congruence].
  Defined.

  Definition keyF0_dec (k k' : CallKey F0) : {k = k'} + {k <> k'}.
  Proof.
    destruct k as [t h], k' as [t' h'].
    destruct (Pos.eq_dec t t') as [-> | Ht]; [| right; congruence].
    destruct (Nat.eq_dec h h') as [-> | Hh]; [left; reflexivity | right; congruence].
  Defined.

  Lemma acq_rfence (a x : UOp) : is_acq a = true -> ~ semi_independent E0 a x.
  Proof. destruct a; cbn; try discriminate. intros _ (H & _). exact H. Qed.

  Lemma rel_lfence (x r : UOp) : is_rel r = true -> ~ semi_independent E0 x r.
  Proof. destruct r; cbn; try discriminate. intros _ (_ & H & _). exact H. Qed.

  Lemma acq_not_rel (o : UOp) : is_acq o = true -> is_rel o = false.
  Proof. destruct o; cbn; congruence. Qed.

  Lemma M0_bracketed t op tr ret :
    program_produces_tagged t (M0 op t) tr ret ->
    BracketedLink.bracketed (E := E0) uloc is_acq is_rel (floc op) (map untag tr).
  Proof.
    destruct op as [l v | l]; cbn; intros Hp;
      [apply (bprog_shape t (UAcq l) (UWr l v) (URel l)) in Hp |
       apply (bprog_shape t (UAcq l) (URd l) (URel l)) in Hp];
      destruct Hp as
      (h1 & h2 & h3 & m1 & m2 & m3 & m4 & m5 & m6 & va & vr & -> & Hm1 & Hm2 & Hm3 & Hm4 & Hm5 & Hm6 & _);
      cbn [map];
      exists 0, (t, h1), (UAcq l), 4, (t, h3), (URel l);
      unfold BracketedLink.inv_in; cbn [nth_error];
      rewrite Hm1, Hm2, Hm3, Hm4, Hm5, Hm6;
      (split; [reflexivity |]); (split; [reflexivity |]); (split; [reflexivity |]);
      (split; [reflexivity |]); (split; [reflexivity |]); (split; [reflexivity |]);
      (split; [lia |]);
      intros [| [| [| [| [| [| i]]]]]] k o Hi Hi0 Hi4; cbn in Hi;
      try discriminate; try lia.
    all: first [ (destruct i; discriminate)
               | (injection Hi as _ _ <-; split; [lia | split; reflexivity]) ].
  Qed.

  (** Component specifications: the lock alternates, and the register
      is a sequential register. *)
  Definition data_reg (o : Op E0) : option RegOp :=
    match o with
    | Build_Op k op ret =>
        (match op as o0 return @Sig.ar USig o0 -> option RegOp with
         | URd _ => fun v => Some (Get v)
         | UWr _ v => fun _ => Some (Put v)
         | _ => fun _ => None
         end) ret
    end.

  Definition data_regs (w : list (Op E0)) : list RegOp :=
    flat_map (fun o => match data_reg o with Some x => [x] | None => [] end) w.

  Definition nuEc (c : Loc) (w : list (Op E0)) : Prop :=
    BracketedLink.lock_alternates (E := E0) is_acq is_rel w /\ reg_ok 0 (data_regs w).

  Definition ovl_reg (s : Op F0) : RegOp :=
    match s with
    | Build_Op k op ret =>
        (match op as o0 return @Sig.ar FSig o0 -> RegOp with
         | FPut _ v => fun _ => Put v
         | FGet _ => fun v => Get v
         end) ret
    end.

  Definition nuFc (c : Loc) (G : list (Op F0)) : Prop := reg_ok 0 (map ovl_reg G).

  Lemma flat_map_single {A B : Type} (f : A -> list B) l a x :
    NoDup l -> In a l -> f a = [x] -> (forall b, In b l -> b <> a -> f b = []) -> flat_map f l = [x].
  Proof.
    induction l as [| c l IH]; cbn; intros Hnd Ha Hfa Hother; [contradiction |].
    inversion Hnd as [| ? ? Hnc Hnd']; subst.
    destruct Ha as [<- | Ha].
    - rewrite Hfa. cbn. f_equal.
      assert (Hnil : forall l', (forall b, In b l' -> f b = []) -> flat_map f l' = []).
      { induction l' as [| b l' IHl]; cbn; intros Hb; [reflexivity |].
        rewrite Hb by (left; reflexivity). apply IHl. intros b' Hb'. apply Hb. right. exact Hb'. }
      apply Hnil. intros b Hb. apply Hother; [right; exact Hb |]. intros ->. contradiction.
    - rewrite (Hother c (or_introl eq_refl)) by (intros ->; contradiction). cbn.
      apply IH; [exact Hnd' | exact Ha | exact Hfa |].
      intros b Hb Hne. apply Hother; [right; exact Hb | exact Hne].
  Qed.

  Lemma nodup_map_inj_local {A B : Type} (f : A -> B) l a b :
    NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
  Proof.
    induction l as [|c l IH]; cbn; intros Hnd Ha Hb Hf; [contradiction |].
    inversion Hnd as [|? ? Hnin Hnd']; subst.
    destruct Ha as [<- | Ha], Hb as [<- | Hb]; auto.
    - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hb.
    - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Ha.
  Qed.

  Section BodyData.
    Context (t : tid) (a d r : UOp) (h1 h2 h3 : handle E0).
    Context (m1 m2 m3 m4 m5 m6 : TaggedEvent E0).
    Context (va : @Sig.ar USig a) (rv : @Sig.ar USig d) (vr : @Sig.ar USig r).
    Context (Hm1 : untag m1 = BracketedLink.inv_ev (t, h1) a).
    Context (Hm2 : untag m2 = BracketedLink.res_ev (t, h1) a va).
    Context (Hm3 : untag m3 = BracketedLink.inv_ev (t, h2) d).
    Context (Hm4 : untag m4 = BracketedLink.res_ev (t, h2) d rv).
    Context (Hm5 : untag m5 = BracketedLink.inv_ev (t, h3) r).
    Context (Hm6 : untag m6 = BracketedLink.res_ev (t, h3) r vr).
    Context (Hd12 : h1 <> h2) (Hd13 : h1 <> h3) (Hd23 : h2 <> h3).

    Definition tr6 : list (TaggedEvent E0) := [m1; m2; m3; m4; m5; m6].

    Lemma inv_classify i k o :
      inv_at BracketedLink.tsel tr6 i k o ->
      (k = (t, h1) /\ o = a) \/ (k = (t, h2) /\ o = d) \/ (k = (t, h3) /\ o = r).
    Proof.
      intros (m & Hi & Hs). unfold BracketedLink.tsel in Hs.
      destruct i as [| [| [| [| [| [| i]]]]]]; cbn in Hi; try (destruct i; discriminate);
        injection Hi as <-;
        [rewrite Hm1 in Hs | rewrite Hm2 in Hs | rewrite Hm3 in Hs
        | rewrite Hm4 in Hs | rewrite Hm5 in Hs | rewrite Hm6 in Hs];
        unfold BracketedLink.inv_ev, BracketedLink.res_ev in Hs; try discriminate;
        injection Hs as Ht Hh Ho; subst o;
        destruct k as [tk hk]; cbn in Ht, Hh; subst tk hk;
        first [ left; split; reflexivity
              | right; left; split; reflexivity
              | right; right; split; reflexivity ].
    Qed.

    Lemma res_classify j (v' : @Sig.ar USig d) :
      res_at BracketedLink.tsel tr6 j (t, h2) d v' -> v' = rv.
    Proof.
      intros (m & Hj & Hs). unfold BracketedLink.tsel in Hs.
      destruct j as [| [| [| [| [| [| j]]]]]]; cbn in Hj; try (destruct j; discriminate);
        injection Hj as <-;
        [rewrite Hm1 in Hs | rewrite Hm2 in Hs | rewrite Hm3 in Hs
        | rewrite Hm4 in Hs | rewrite Hm5 in Hs | rewrite Hm6 in Hs];
        unfold BracketedLink.inv_ev, BracketedLink.res_ev in Hs; try discriminate.
      - apply (f_equal (option_map (fun ev => event_handle (te_ev E0 ev)))) in Hs.
        cbn in Hs. injection Hs as Hs. contradiction.
      - apply (f_equal (option_map (fun ev => match te_ev E0 ev with
                                              | ResEv _ o0 x => val_of o0 x | InvEv _ _ => 0 end))) in Hs.
        cbn in Hs. injection Hs as Hs. rewrite <- (of_val d rv), Hs, of_val. reflexivity.
      - apply (f_equal (option_map (fun ev => event_handle (te_ev E0 ev)))) in Hs.
        cbn in Hs. injection Hs as Hs. symmetry in Hs. contradiction.
    Qed.

    Lemma body_data_gen (l : list (Op E0)) (x : RegOp) :
      (forall (k' : CallKey E0) (va' : @Sig.ar USig a), data_reg (Build_Op (E := E0) k' a va') = None) ->
      (forall (k' : CallKey E0) (vr' : @Sig.ar USig r), data_reg (Build_Op (E := E0) k' r vr') = None) ->
      data_reg (Build_Op (E := E0) (t, h2) d rv) = Some x ->
      BracketedLink.body_matches (E := E0) tr6 l ->
      data_regs l = [x].
    Proof.
      intros Ha Hr Hd (Hnd & Hocc & Hall & _).
      assert (Hkey : forall (hh hh' : handle E0), (t, hh) = (t, hh') -> hh = hh') by congruence.
      destruct (Hall 2 (t, h2) d) as (od & Hod & Hkd).
      { exists m3. split; [reflexivity |]. unfold BracketedLink.tsel. rewrite Hm3. reflexivity. }
      assert (Hop : op_op od = d).
      { destruct (Hocc od Hod) as [(i & Hi) _]. rewrite Hkd in Hi.
        destruct (inv_classify _ _ _ Hi) as [[E _] | [[_ E] | [E _]]];
          [apply Hkey in E; congruence | exact E | apply Hkey in E; congruence]. }
      destruct od as [kd opd rd]. cbn in Hkd, Hop. subst kd opd.
      assert (Hrd : rd = rv).
      { destruct (Hocc _ Hod) as [_ (j & Hj)]. exact (res_classify j rd Hj). }
      subst rd.
      unfold data_regs. apply (flat_map_single _ l (Build_Op (E := E0) (t, h2) d rv) x).
      - exact (NoDup_map_inv _ _ Hnd).
      - exact Hod.
      - rewrite Hd. reflexivity.
      - intros b Hb Hne. destruct (Hocc b Hb) as [(i & Hi) _].
        destruct b as [kb opb rb]. cbn in Hi.
        destruct (inv_classify _ _ _ Hi) as [[E1 E2] | [[E1 E2] | [E1 E2]]]; subst kb opb.
        + rewrite Ha. reflexivity.
        + exfalso. apply Hne. apply (nodup_map_inj_local _ _ _ _ Hnd Hb Hod). reflexivity.
        + rewrite Hr. reflexivity.
    Qed.
  End BodyData.

  (** The body of each method: exactly one data call, carrying the
      register event of the overlay call. *)
  Lemma body_data (s : Op F0) (l : list (Op E0)) :
    BracketedLink.local_ok M0 s l -> data_regs l = [ovl_reg s].
  Proof.
    intros (tr & Hprod & Hbm).
    destruct s as [k op ret]. cbn [op_key op_op op_ret] in Hprod.
    destruct op as [lc v | lc]; cbn in Hprod.
    - apply (bprog_shape (fst k) (UAcq lc) (UWr lc v) (URel lc)) in Hprod
        as (h1 & h2 & h3 & m1 & m2 & m3 & m4 & m5 & m6 & va & vr & -> & H1 & H2 & H3 & H4 & H5 & H6 & D12 & D13 & D23).
      eapply body_data_gen with (t := fst k) (a := UAcq lc) (d := UWr lc v) (r := URel lc) (rv := ret);
        try eassumption; try (intros; reflexivity).
    - apply (bprog_shape (fst k) (UAcq lc) (URd lc) (URel lc)) in Hprod
        as (h1 & h2 & h3 & m1 & m2 & m3 & m4 & m5 & m6 & va & vr & -> & H1 & H2 & H3 & H4 & H5 & H6 & D12 & D13 & D23).
      eapply body_data_gen with (t := fst k) (a := UAcq lc) (d := URd lc) (r := URel lc) (rv := ret);
        try eassumption; try (intros; reflexivity).
  Qed.

  Lemma data_regs_app l1 l2 : data_regs (l1 ++ l2) = data_regs l1 ++ data_regs l2.
  Proof. unfold data_regs. apply flat_map_app. Qed.

  Lemma data_regs_concat (G : list (Op F0)) (b : Op F0 -> list (Op E0)) :
    (forall s, In s G -> BracketedLink.local_ok M0 s (b s)) ->
    data_regs (concat (map b G)) = map ovl_reg G.
  Proof.
    induction G as [| s G IH]; intros Hb; [reflexivity |].
    cbn [concat map]. rewrite data_regs_app, (body_data s (b s) (Hb s (or_introl eq_refl))), IH.
    - reflexivity.
    - intros s' Hs'. apply Hb. right. exact Hs'.
  Qed.

  (** The local obligation of a lock-protected register. *)
  Lemma local_correct (c : Loc) (G : list (Op F0)) (b : Op F0 -> list (Op E0)) :
    NoDup (map op_key G) ->
    (forall s, In s G -> floc (op_op s) = c /\ BracketedLink.local_ok M0 s (b s)) ->
    nuEc c (concat (map b G)) -> nuFc c G.
  Proof.
    intros _ Hb (_ & Hreg). unfold nuFc. rewrite <- (data_regs_concat G b); [exact Hreg |].
    intros s Hs. apply (Hb s Hs).
  Qed.

  (** ** Store buffering *)

  Definition put_op (k : CallKey F0) (l : Loc) : Op F0 := Build_Op (E := F0) k (FPut l 1) tt.
  Definition get_op (k : CallKey F0) (l : Loc) (v : nat) : Op F0 := Build_Op (E := F0) k (FGet l) v.

  Definition kidx (W : list (Op F0)) (o : Op F0) : nat :=
    BracketedLink.key_index keyF0_dec (op_key o) (map op_key W).

  Lemma before_kidx (W : list (Op F0)) a b :
    NoDup (map op_key W) -> before W a b -> kidx W a < kidx W b.
  Proof.
    intros Hnd (l1 & l2 & HW & Hin). unfold kidx. rewrite HW in *. rewrite map_app in *. cbn in *.
    assert (Hn1 : ~ In (op_key a) (map op_key l1)).
    { intros H. apply (RelaxedModuleFacts.nodup_app_disj _ _ _ Hnd H). left. reflexivity. }
    assert (Hn2 : ~ In (op_key b) (map op_key l1)).
    { intros H. apply (RelaxedModuleFacts.nodup_app_disj _ _ _ Hnd H). right. apply in_map, Hin. }
    assert (Hne : op_key a <> op_key b).
    { intros Heq. apply NoDup_app_remove_l in Hnd. inversion Hnd as [| ? ? Hn _].
      apply Hn. rewrite Heq. apply in_map, Hin. }
    rewrite !(BracketedLink.key_index_app keyF0_dec) by assumption.
    rewrite (BracketedLink.key_index_head keyF0_dec). cbn.
    destruct (keyF0_dec (op_key a) (op_key b)); [contradiction | lia].
  Qed.

  (** [T1: put(x,1); get(y) || T2: put(y,1); get(x)] with both reads
      returning [0] is impossible.  The outcome is described by the set
      of complete overlay operations and by the program order of the
      invocations; the overlay client may invoke [get] before [put]
      returns. *)
  Theorem sb_forbidden (VE : RelaxedLTSSpec.LTS E0) q0 T c (k1 k2 k3 k4 : CallKey F0) :
    fst k1 = fst k2 -> fst k3 = fst k4 -> NoDup [k1; k2; k3; k4] ->
    module_execution_tagged VE M0 (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell F0 e = DeadCall) ->
    rel_lin BracketedLink.under_sel T (semi_independent E0)
      (BracketedLink.nuE_all (E := E0) BracketedComposition.loc_dec uloc nuEc) ->
    (forall o, occurs BracketedLink.over_sel T o <->
       In o [put_op k1 LX; get_op k2 LY 0; put_op k3 LY; get_op k4 LX 0]) ->
    (exists i j, inv_at BracketedLink.over_sel T i k1 (FPut LX 1) /\
                 inv_at BracketedLink.over_sel T j k2 (FGet LY) /\ i < j) ->
    (exists i j, inv_at BracketedLink.over_sel T i k3 (FPut LY 1) /\
                 inv_at BracketedLink.over_sel T j k4 (FGet LX) /\ i < j) ->
    False.
  Proof.
    intros Ht12 Ht34 Hkeys Hexec Hq Hdead Hunder Hops (i1 & j1 & Hi1 & Hj1 & Hij1) (i2 & j2 & Hi2 & Hj2 & Hij2).
    destruct (BracketedLink.bracketed_link VE M0 keyE0_dec keyF0_dec BracketedComposition.loc_dec
                uloc floc is_acq is_rel acq_rfence rel_lfence acq_not_rel M0_bracketed nuEc nuFc
                (fun _ _ H => proj1 H) local_correct q0 T c Hexec Hq Hdead Hunder)
      as (W & Hnu & Hnd & Hocc & Hall & Hord).
    set (o1 := put_op k1 LX). set (o2 := get_op k2 LY 0).
    set (o3 := put_op k3 LY). set (o4 := get_op k4 LX 0).
    assert (HWsub : forall o, In o W -> In o [o1; o2; o3; o4]) by (intros o Ho; apply Hops, Hocc, Ho).
    assert (HinW : forall o, In o [o1; o2; o3; o4] -> In o W).
    { intros o Ho. pose proof (proj2 (Hops o) Ho) as [(i & Hi) _].
      destruct (Hall i (op_key o) (op_op o) Hi) as (o' & Ho' & Hk).
      assert (E : o' = o).
      { apply (nodup_map_inj_local op_key [o1; o2; o3; o4]); [exact Hkeys | apply HWsub, Ho' | exact Ho | exact Hk]. }
      rewrite <- E. exact Ho'. }
    assert (H1 : In o1 W) by (apply HinW; cbn; tauto).
    assert (H2 : In o2 W) by (apply HinW; cbn; tauto).
    assert (H3 : In o3 W) by (apply HinW; cbn; tauto).
    assert (H4 : In o4 W) by (apply HinW; cbn; tauto).
    assert (Hsort : StronglySorted (fun s s' => kidx W s < kidx W s') W).
    { apply BracketedLink.ss_of_before. intros x y Hxy. apply before_kidx; assumption. }
    (* program order, through the witness *)
    assert (P1 : kidx W o1 < kidx W o2).
    { apply before_kidx; [exact Hnd |]. apply Hord; [exact H1 | exact H2 |].
      right. split; [exact Ht12 |]. exists i1, j1. auto. }
    assert (P2 : kidx W o3 < kidx W o4).
    { apply before_kidx; [exact Hnd |]. apply Hord; [exact H3 | exact H4 |].
      right. split; [exact Ht34 |]. exists i2, j2. auto. }
    (* each location is a register *)
    assert (Hputs : forall l s v', In s (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc l W) ->
                      ovl_reg s = Put v' -> v' = 1).
    { intros l s v' Hs Ho. apply filter_In in Hs as [Hs _]. apply HWsub in Hs.
      destruct Hs as [<- | [<- | [<- | [<- | []]]]]; cbn in Ho; congruence. }
    assert (Hin : forall l s, In s W -> floc (op_op s) = l ->
                    In s (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc l W)).
    { intros l s Hs Hl. apply filter_In. split; [exact Hs |]. rewrite Hl.
      destruct (BracketedComposition.loc_dec l l); [reflexivity | contradiction]. }
    assert (RX : kidx W o4 < kidx W o1).
    { apply (BracketedComposition.read_old_before_write (kidx W) ovl_reg
               (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc LX W) o1 o4 1 0).
      - apply BracketedComposition.ss_filter, Hsort.
      - apply Hputs.
      - exact (Hnu LX).
      - apply Hin; [exact H1 | reflexivity].
      - apply Hin; [exact H4 | reflexivity].
      - reflexivity.
      - reflexivity.
      - discriminate. }
    assert (RY : kidx W o2 < kidx W o3).
    { apply (BracketedComposition.read_old_before_write (kidx W) ovl_reg
               (BracketedLink.proj_F (F := F0) BracketedComposition.loc_dec floc LY W) o3 o2 1 0).
      - apply BracketedComposition.ss_filter, Hsort.
      - apply Hputs.
      - exact (Hnu LY).
      - apply Hin; [exact H3 | reflexivity].
      - apply Hin; [exact H2 | reflexivity].
      - reflexivity.
      - reflexivity.
      - discriminate. }
    lia.
  Qed.

  (** ** The hypotheses are met by an actual execution

      One thread calls [put(x, 1)]; the underlay is an LTS that accepts
      every event.  The run is complete and its underlay part is
      relaxed linearizable, so the premises of [bracketed_link] (and of
      [sb_forbidden], apart from the outcome) are not contradictory. *)

  Definition VE0 : RelaxedLTSSpec.LTS E0 :=
    {| State := unit; Step := fun _ _ _ => True; Error := fun _ _ => False |}.

  Definition t1 : tid := 1%positive.

  Definition st1 : FutureStore E0 := [Build_FutureEntry (E := E0) 0 (Resolved (E := E0) (UAcq LX) tt)].
  Definition st2 : FutureStore E0 := Build_FutureEntry (E := E0) 1 (Resolved (E := E0) (UWr LX 1) tt) :: st1.

  Definition ev1 : TaggedEvent E0 := Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv E0 0 (UAcq LX))) (resolved_in empty_store).
  Definition ev2 : TaggedEvent E0 := Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv E0 0 (UAcq LX) tt)) no_deps.
  Definition ev3 : TaggedEvent E0 := Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv E0 1 (UWr LX 1))) (resolved_in st1).
  Definition ev4 : TaggedEvent E0 := Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv E0 1 (UWr LX 1) tt)) no_deps.
  Definition ev5 : TaggedEvent E0 := Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv E0 2 (URel LX))) (resolved_in st2).
  Definition ev6 : TaggedEvent E0 := Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv E0 2 (URel LX) tt)) no_deps.

  Definition put_trace : list (TaggedEvent E0) := [ev1; ev2; ev3; ev4; ev5; ev6].

  Lemma put_produces : program_produces_tagged t1 (M0 (FPut LX 1) t1) put_trace tt.
  Proof.
    eexists. split.
    - unfold put_trace. cbn [M0]. unfold bprog, initial_program.
      eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; tauto |]. cbn beta.
      eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
      eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; intuition discriminate |]. cbn beta.
      eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
      eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; intuition discriminate |]. cbn beta.
      eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
      apply tagged_execution_refl.
    - constructor. repeat constructor.
  Qed.

  Definition T_put : list (ModuleEvent E0 F0) :=
    [OverlayEvent (Build_ThreadEvent t1 (@InvEv F0 0 (FPut LX 1)));
     UnderlayEvent (untag ev1); UnderlayEvent (untag ev2); UnderlayEvent (untag ev3);
     UnderlayEvent (untag ev4); UnderlayEvent (untag ev5); UnderlayEvent (untag ev6);
     OverlayEvent (Build_ThreadEvent t1 (@ResEv F0 0 (FPut LX 1) tt))].

  Lemma put_execution : exists c,
    module_execution_tagged VE0 M0 (initial_tagged_module VE0 tt) T_put c /\
    tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell F0 e = DeadCall).
  Proof.
    eexists. split; [| split].
    - unfold T_put.
      eapply tagged_module_execution_cons.
      { apply tagged_invoke; [unfold call_fresh; cbn; tauto | exact put_produces |].
        split.
        - cbn. repeat constructor; cbn; intuition discriminate.
        - intros key _ []. }
      eapply tagged_module_execution_cons.
      { eapply tagged_underlay with (candidate := Build_TaggedScheduledEvent (F := F0) (t1, 0) ev1) (q' := tt);
          [cbn; apply tagged_select_here | exact I]. }
      eapply tagged_module_execution_cons.
      { eapply tagged_underlay with (candidate := Build_TaggedScheduledEvent (F := F0) (t1, 0) ev2) (q' := tt);
          [cbn; apply tagged_select_here | exact I]. }
      eapply tagged_module_execution_cons.
      { eapply tagged_underlay with (candidate := Build_TaggedScheduledEvent (F := F0) (t1, 0) ev3) (q' := tt);
          [cbn; apply tagged_select_here | exact I]. }
      eapply tagged_module_execution_cons.
      { eapply tagged_underlay with (candidate := Build_TaggedScheduledEvent (F := F0) (t1, 0) ev4) (q' := tt);
          [cbn; apply tagged_select_here | exact I]. }
      eapply tagged_module_execution_cons.
      { eapply tagged_underlay with (candidate := Build_TaggedScheduledEvent (F := F0) (t1, 0) ev5) (q' := tt);
          [cbn; apply tagged_select_here | exact I]. }
      eapply tagged_module_execution_cons.
      { eapply tagged_underlay with (candidate := Build_TaggedScheduledEvent (F := F0) (t1, 0) ev6) (q' := tt);
          [cbn; apply tagged_select_here | exact I]. }
      eapply tagged_module_execution_cons.
      { eapply tagged_return; [apply finish_here | intros []]. }
      apply tagged_module_execution_refl.
    - reflexivity.
    - intros e [<- | []]. reflexivity.
  Qed.

  Definition W_put : list (Op E0) :=
    [Build_Op (E := E0) (t1, 0) (UAcq LX) tt;
     Build_Op (E := E0) (t1, 1) (UWr LX 1) tt;
     Build_Op (E := E0) (t1, 2) (URel LX) tt].

  Lemma put_inv_pos i k op :
    inv_at BracketedLink.under_sel T_put i k op -> exists h, h < 3 /\ k = (t1, h) /\ i = 2 * h + 1.
  Proof.
    intros (x & Hx & Hs).
    destruct i as [| [| [| [| [| [| [| [| i]]]]]]]]; cbn in Hx; try (destruct i; discriminate);
      injection Hx as <-; cbn in Hs; try discriminate;
      injection Hs as Ht Hh _; destruct k as [tk hk]; cbn in Ht, Hh; subst tk hk;
      (eexists; split; [| split; reflexivity]); lia.
  Qed.

  Lemma put_res_pos i k op v :
    res_at BracketedLink.under_sel T_put i k op v -> exists h, h < 3 /\ k = (t1, h) /\ i = 2 * h + 2.
  Proof.
    intros (x & Hx & Hs).
    destruct i as [| [| [| [| [| [| [| [| i]]]]]]]]; cbn in Hx; try (destruct i; discriminate);
      injection Hx as <-; cbn in Hs; try discriminate;
      apply (f_equal (option_map (fun ev => (te_tid E0 ev, event_handle (te_ev E0 ev))))) in Hs;
      cbn in Hs; injection Hs as Ht Hh; destruct k as [tk hk]; cbn in Ht, Hh; subst tk hk;
      (eexists; split; [| split; reflexivity]); lia.
  Qed.

  Lemma put_underlay_rel_lin :
    rel_lin BracketedLink.under_sel T_put (semi_independent E0)
      (BracketedLink.nuE_all (E := E0) BracketedComposition.loc_dec uloc nuEc).
  Proof.
    exists W_put. split; [| split; [| split; [| split]]].
    - intros [|]; cbn; (split; [repeat constructor | exact I]).
    - cbn. repeat constructor; cbn; intuition congruence.
    - intros o Ho. destruct Ho as [<- | [<- | [<- | []]]]; split.
      + exists 1. eexists. split; reflexivity.
      + exists 2. eexists. split; reflexivity.
      + exists 3. eexists. split; reflexivity.
      + exists 4. eexists. split; reflexivity.
      + exists 5. eexists. split; reflexivity.
      + exists 6. eexists. split; reflexivity.
    - intros i k op Hi. destruct (put_inv_pos i k op Hi) as (h & Hh & -> & _).
      destruct h as [| [| [| h]]]; [| | | lia].
      + eexists. split; [left; reflexivity | reflexivity].
      + eexists. split; [right; left; reflexivity | reflexivity].
      + eexists. split; [right; right; left; reflexivity | reflexivity].
    - intros o o' Ho Ho' Hr.
      assert (Hlt : snd (op_key o) < snd (op_key o')).
      { destruct Hr as [(i & j & Hi & Hj & Hij) | (_ & i & j & Hi & Hj & Hij & _)].
        - destruct (put_res_pos _ _ _ _ Hi) as (h & _ & Hk & ->).
          destruct (put_inv_pos _ _ _ Hj) as (h' & _ & Hk' & ->).
          rewrite Hk, Hk'. cbn. lia.
        - destruct (put_inv_pos _ _ _ Hi) as (h & _ & Hk & ->).
          destruct (put_inv_pos _ _ _ Hj) as (h' & _ & Hk' & ->).
          rewrite Hk, Hk'. cbn. lia. }
      destruct Ho as [<- | [<- | [<- | []]]]; destruct Ho' as [<- | [<- | [<- | []]]];
        cbn in Hlt; try lia;
        first [ (eexists [], _; split; [reflexivity | cbn; tauto])
              | (eexists [_], _; split; [reflexivity | cbn; tauto]) ].
  Qed.

  Theorem link_hypotheses_satisfiable : exists T c,
    module_execution_tagged VE0 M0 (initial_tagged_module VE0 tt) T c /\
    tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell F0 e = DeadCall) /\
    rel_lin BracketedLink.under_sel T (semi_independent E0)
      (BracketedLink.nuE_all (E := E0) BracketedComposition.loc_dec uloc nuEc) /\
    inv_at BracketedLink.over_sel T 0 (t1, 0) (FPut LX 1).
  Proof.
    destruct put_execution as (c & Hx & Hq & Hd).
    exists T_put, c. split; [exact Hx |]. split; [exact Hq |]. split; [exact Hd |].
    split; [exact put_underlay_rel_lin |].
    eexists. split; reflexivity.
  Qed.

End LockedRegisters.
