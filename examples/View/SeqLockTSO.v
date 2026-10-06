(** Ported from CSL-Lin [examples/seqlock.v] (hyleIndex/CSL-Lin, master 3f7baaa).
    View-based (timestamped) specification / proof, kept as close to the
    original as possible; changes are limited to the Rocq 9.2 / rbgs
    adaptation listed in [examples/View/README.md]. *)

Require Import Stdlib.FSets.FMapPositive.
Require Import Stdlib.Relations.Relation_Operators Stdlib.Relations.Operators_Properties.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Program.Equality.
Require Import Stdlib.micromega.Lia.

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

Module SeqLockImpl.
  Import LinCCALBase.
  Import LTSSpec.
  Import Lang.
  Import AssertionsSingle.
  Import LegacyAssertionNotations.
  Import RGILogic.
  Import TPSimulation.
  Import AtomicLTS SeqLockUnderlaySpec SeqLock.
  Import (coercions, canonicals, notations) Sig.
  Import (notations) LinCCAL.
  Open Scope prog_scope.

(* Seqlock:
import l : ticketLock
import x, y : TSO
write (vx, vy) {
    l.acq();
    x.wrt(vx);
    y.wrt(vy);
    l.rel();
}

read () {
    do {
        now $\gets$ l.get_ticket();
        vx $\gets$ x.rd();
        vy $\gets$ y.rd();
    } while (l.test_ticket(now));
    ret (vx, vy);
} *)

  (* ------------------------------------------------------------------ *)
  (** ** Layer interfaces *)

  (** Underlay [E]: the six TSO+lock primitives *)
  Definition initE : SSeqLockUL :=
    mkSLUL (fun _ _ => O) (fun _ => (O, O)) (fun _ _ => xH) None.

  Definition E : layer_interface :=
  {|
    li_sig := ESeqLockUL;
    li_lts := VSeqLockUL;
    li_init := Idle initE;
  |}.

  (** Overlay [F]: atomic write/read seqlock *)
  Definition initF : SSeqLock :=
    mkSL O O (fun _ => xH).

  Definition F : layer_interface :=
  {|
    li_sig := ESeqLock;
    li_lts := VSeqLock;
    li_init := Idle initF;
  |}.

  (* ------------------------------------------------------------------ *)
  (** ** Implementation programs *)

  (** [write(vx', vy')]: acquire lock, write x, write y, release *)
  Definition write_impl (vx' vy' : nat) : Prog (li_sig E) unit :=
    acq >= _ =>
    wrt loc_x vx' >= _ =>
    wrt loc_y vy' >= _ =>
    rel >= _ =>
    Ret tt.

  (** One iteration of the reader loop:
      read the ticket, snapshot x and y, then test if the lock is busy.
      Returns [(busy, (vx, vy))] so the do-while can check [busy].
      We use [Vis] with explicit type annotations for [get_ticket] and
      [test_ticket] because [test_ticket now] is a dependent constructor
      whose arity ([bool]) must be given explicitly so that the unifier
      does not try to place [now] outside its scope in the return type. *)
  Definition read_body : Prog (li_sig E) (bool * (nat * nat)) :=
    Vis get_ticket (fun (now : nat) =>
    rd loc_x >= vx =>
    rd loc_y >= vy =>
    Vis (test_ticket now) (fun (busy : bool) =>
    Ret (busy, (vx, vy)))).

  (** [read()]: loop until the lock is not busy, then return [(vx, vy)] *)
  Definition read_impl : Prog (li_sig E) (nat * nat) :=
    Do { read_body } While (fst res) >= res =>
    Ret (snd res).

  Definition pack_res (e : Event) :
    option (sigT (fun op : Sig.op ESeqLockUL => Sig.ar op)) :=
    match e with
    | InvEv _ => None
    | ResEv op ret => Some (existT _ op ret)
    end.

  Lemma step_get_ticket_res_inv {t k s1 s2} :
    StepSeqLockUL (Build_ThreadEvent t (ResEv get_ticket k)) s1 s2 ->
    exists h nxt,
      (forall t0, Pos.lt (SeqLockUnderlaySpec.H_bar s1 t0) h) /\
      SeqLockUnderlaySpec.sl_lock s1 h = (nxt, k) /\
      s2 =
        SeqLockUnderlaySpec.mkSLUL
          (SeqLockUnderlaySpec.sl_mem s1)
          (SeqLockUnderlaySpec.sl_lock s1)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
             (view_advance (SeqLockUnderlaySpec.sl_view s1 t) h))
          (SeqLockUnderlaySpec.sl_owner s1).
  Proof.
    intro Hstep.
    remember (Build_ThreadEvent t (ResEv get_ticket k)) as ev eqn:Hev.
    change (StepSeqLockUL ev s1 s2) in Hstep.
    dependent destruction Hstep; try (inversion Hev).
    (* step_get_ticket_res *)
    inversion Hev; subst.
    (* recover the return equality [k0 = k] from the event equality *)
    pose proof (f_equal te_ev Hev) as Hev_ev.
    simpl in Hev_ev.
    pose proof (f_equal pack_res Hev_ev) as Hpack.
    simpl in Hpack.
    apply (f_equal (fun ox =>
      match ox with
      | Some x => x
      | None => existT _ get_ticket k (* impossible here *)
      end)) in Hpack.
    (* now Hpack is an equality of [existT] pairs *)
    apply Eqdep_dec.inj_pair2_eq_dec in Hpack;
      [|repeat decide equality].
    subst.
    eexists h, nxt; repeat split; eauto.
	  Qed.

  Lemma step_test_ticket_res_inv {t n b s1 s2} :
    StepSeqLockUL (Build_ThreadEvent t (ResEv (test_ticket n) b)) s1 s2 ->
    exists h k,
      (forall t0, Pos.lt (SeqLockUnderlaySpec.H_bar s1 t0) h) /\
      SeqLockUnderlaySpec.sl_lock s1 h = (n, k) /\
      b = orb (Nat.odd n) (negb (Nat.eqb k n)) /\
      s2 =
        SeqLockUnderlaySpec.mkSLUL
          (SeqLockUnderlaySpec.sl_mem s1)
          (SeqLockUnderlaySpec.sl_lock s1)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
             (view_advance (SeqLockUnderlaySpec.sl_view s1 t) h))
          (SeqLockUnderlaySpec.sl_owner s1).
  Proof.
    intro Hstep.
    remember (Build_ThreadEvent t (ResEv (test_ticket n) b)) as ev eqn:Hev.
    change (StepSeqLockUL ev s1 s2) in Hstep.
    dependent destruction Hstep; try (inversion Hev).
    inversion Hev; subst.
    pose proof (f_equal te_ev Hev) as Hev_ev.
    simpl in Hev_ev.
    pose proof (f_equal pack_res Hev_ev) as Hpack.
    simpl in Hpack.
    apply (f_equal (fun ox =>
      match ox with
      | Some x => x
      | None => existT _ (test_ticket n) b
      end)) in Hpack.
    apply Eqdep_dec.inj_pair2_eq_dec in Hpack;
      [|repeat decide equality].
    subst.
    eexists h, k; repeat split; eauto.
  Qed.

  Lemma step_rd_res_inv {t l w s1 s2} :
    StepSeqLockUL (Build_ThreadEvent t (ResEv (rd l) w)) s1 s2 ->
    exists h,
      Pos.lt (SeqLockUnderlaySpec.sl_view s1 t (SeqLockUnderlaySpec.mem_to_all l)) h /\
      w = SeqLockUnderlaySpec.sl_mem s1 l h /\
      s2 =
        SeqLockUnderlaySpec.mkSLUL
          (SeqLockUnderlaySpec.sl_mem s1)
          (SeqLockUnderlaySpec.sl_lock s1)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
             (view_advance (SeqLockUnderlaySpec.sl_view s1 t) h))
          (SeqLockUnderlaySpec.sl_owner s1).
  Proof.
    intro Hstep.
    remember (Build_ThreadEvent t (ResEv (rd l) w)) as ev eqn:Hev.
    change (StepSeqLockUL ev s1 s2) in Hstep.
    dependent destruction Hstep; try (inversion Hev).
    (* step_rd_res *)
    inversion Hev; subst.
    pose proof (f_equal te_ev Hev) as Hev_ev.
    simpl in Hev_ev.
    pose proof (f_equal pack_res Hev_ev) as Hpack.
    simpl in Hpack.
    apply (f_equal (fun ox =>
      match ox with
      | Some x => x
      | None => existT _ (rd l) w
      end)) in Hpack.
    apply Eqdep_dec.inj_pair2_eq_dec in Hpack;
      [|repeat decide equality].
    subst.
    eexists h; repeat split; eauto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** ** Correctness proof *)

  Definition assertion := @Assertion (@ProofState _ _ (li_lts E) (li_lts F)).
  Definition rg_relation := @RGRelation _ _ (li_lts E) (li_lts F).

  Open Scope rg_relation_scope.
  Open Scope assertion_scope.

  (* ------------------------------------------------------------------ *)
  (** *** Helper predicates *)

  (** The lock is free at timestamp [h]: [nxt = own] and [nxt] is even. *)
  Definition LockFreeAt (σs : SSeqLockUL) (h : Time) : Prop :=
    let '(nxt, own) := sl_lock σs h in
    nxt = own /\ Nat.even nxt = true.

  (** No release fires in the interval [(lo, hi)]: the lock history is
      constant on that interval (no transition from odd owner to even). *)
  Definition NoRelIn (σs : SSeqLockUL) (lo hi : Time) : Prop :=
    forall h, Pos.lt lo h -> Pos.lt h hi ->
      sl_lock σs h = sl_lock σs lo.

  (** [laststate σ h = (vx, vy)]: memory values at the latest release
      timestamp at or before [h].  Since [mem_write] overwrites all
      timestamps [>= h_write], when no release fires in an interval,
      the memory values are constant there. *)
  Definition LastState (σs : SSeqLockUL) (h : Time) (vx vy : nat) : Prop :=
    sl_mem σs loc_x h = vx /\ sl_mem σs loc_y h = vy.

  (** Writer holds the lock: [own] is odd at thread [t]'s lock view. *)
  Definition WriterActive (t : tid) : assertion :=
    fun s =>
      let σs := state (σ s) in
      let '(_, own) := sl_lock σs (sl_view (state (ρ s)) t) in
      Nat.odd own = true.

  (* ------------------------------------------------------------------ *)
  (** *** Invariant
      [I]: the overlay values [(sl_vx, sl_vy)] agree with the underlay
      memory at some "consistent timestamp" [h_c] where the lock is
      free.  This captures the trace-based invariant
        [(sl_vx, sl_vy) = laststate(σ, h_c)]
      in a purely state-based way.

      NOTE: for the multi-writer scenario where a reader observes stale
      values while the overlay has already been updated by a later writer,
      this invariant may need ghost state (overlay history).  The current
      formulation works when readers always see the latest release — which
      is guaranteed by the seqlock protocol: if test_ticket succeeds at
      [h_test], no acq/rel straddled the observation window, so the reader
      sees the same values as the current overlay. *)

  Definition ReadWindowConsistent (σs : SSeqLockUL) (ols : SSeqLock) (h_tail : Time) : Prop :=
    forall (t : tid) now h_get hx hy h_test,
      Pos.le h_tail h_get ->
      Pos.le h_get hx ->
      Pos.le h_get hy ->
      Pos.lt hx h_test ->
      Pos.lt hy h_test ->
      (forall t0, Pos.lt (H_bar σs t0) h_test) ->
      snd (sl_lock σs h_get) = now ->
      sl_lock σs h_test = (now, now) ->
      Nat.even now = true ->
      sl_mem σs loc_x hx = sl_vx ols /\
      sl_mem σs loc_y hy = sl_vy ols.

  Definition SuccessfulReadWindowAfterTail (σs : SSeqLockUL) (h_tail : Time) : Prop :=
    forall (t : tid) now h_get hx hy h_test,
      Pos.le h_get hx ->
      Pos.le h_get hy ->
      Pos.lt hx h_test ->
      Pos.lt hy h_test ->
      (forall t0, Pos.lt (H_bar σs t0) h_test) ->
      snd (sl_lock σs h_get) = now ->
      sl_lock σs h_test = (now, now) ->
      Nat.even now = true ->
      Pos.le h_tail h_get.

  Definition LockHistoryBounded (σs : SSeqLockUL) (h_tail : Time) (n_tail : nat) : Prop :=
    (forall h, Pos.lt h h_tail -> snd (sl_lock σs h) < n_tail) /\
    (forall h, Pos.le h_tail h -> snd (sl_lock σs h) = n_tail \/
      snd (sl_lock σs h) = S n_tail).

  Definition I : assertion :=
    fun s =>
      (exists ls, ρ s = Idle ls) /\
      exists h_c n,
        (* [h_c] is the last released ticket [n] (even), and the overlay values
           agree with underlay memory at [h_c]. *)
        sl_lock (state (σ s)) h_c = (n, n) /\
        Nat.even n = true /\
        sl_vx (state (ρ s)) = sl_mem (state (σ s)) loc_x h_c /\
        sl_vy (state (ρ s)) = sl_mem (state (σ s)) loc_y h_c /\
        (forall t, Pos.le h_c (H_bar (state (σ s)) t)) /\
        (forall t, Pos.le h_c (SeqLockUnderlaySpec.sl_view (state (σ s)) t aloc_lk)) /\
        LockHistoryBounded (state (σ s)) h_c n /\
        SuccessfulReadWindowAfterTail (state (σ s)) h_c /\
        ReadWindowConsistent (state (σ s)) (state (ρ s)) h_c.

  (* ------------------------------------------------------------------ *)
  (** *** Rely / Guarantee *)

  (** Underlay components that should be preserved when some *other* thread
      owns the lock (i.e. only the unique owner may change them). *)
  Definition PreserveUL : rg_relation :=
    fun s1 s2 =>
      sl_mem (state (σ s1)) = sl_mem (state (σ s2)) /\
      sl_lock (state (σ s1)) = sl_lock (state (σ s2)).

  (** Helper: [mem_write] at a fresh timestamp doesn't affect older timestamps. *)
  Lemma mem_write_old : forall mem l h w l' h',
    Pos.lt h' h -> mem_write mem l h w l' h' = mem l' h'.
  Proof.
    intros. unfold mem_write.
    assert (Pos.leb h h' = false) as Hleb.
    { apply Pos.leb_nle. intro. eapply Pos.lt_irrefl.
      eapply Pos.lt_le_trans; eauto. }
    rewrite Hleb, Bool.andb_false_r. reflexivity.
  Qed.

  (** Helper: [lock_write] at a fresh timestamp doesn't affect older timestamps. *)
  Lemma lock_write_old : forall lk h nxt own h',
    Pos.lt h' h -> lock_write lk h nxt own h' = lk h'.
  Proof.
    intros. unfold lock_write.
    destruct (Pos.leb h h') eqn:Hleb; [|reflexivity].
    exfalso. apply Pos.leb_le in Hleb.
    eapply Pos.lt_irrefl. eapply Pos.lt_le_trans; eauto.
  Qed.

  Lemma Nat_odd_add_1_even : forall n,
    Nat.odd (n + 1) = Nat.even n.
  Proof.
    intro n. replace (n + 1)%nat with (S n) by lia.
    apply PeanoNat.Nat.odd_succ.
  Qed.

  (** Helper: [view_advance] is monotone on [H_bar]. *)
  Lemma Hbar_view_advance_le : forall s t h,
    Pos.le (H_bar s t) (H_bar (mkSLUL (sl_mem s) (sl_lock s)
      (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
        (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
      (sl_owner s)) t).
  Proof.
    intros. unfold H_bar; simpl. unfold upd_tid_view.
    rewrite Pos.eqb_refl. unfold view_bar, view_advance.
    apply Pos.max_lub.
    - apply Pos.max_lub.
      + eapply Pos.le_trans; [apply Pos.le_max_l|].
        eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_l.
      + eapply Pos.le_trans; [apply Pos.le_max_l|].
        eapply Pos.le_trans; [apply Pos.le_max_r|]. apply Pos.le_max_l.
    - eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_r.
  Qed.

  (** Helper: [H_bar] is unchanged for other threads under [upd_tid_view]. *)
  Lemma Hbar_upd_tid_view_neq : forall m l v t1 new_v o t2,
    t1 <> t2 ->
    H_bar (mkSLUL m l (upd_tid_view v t1 new_v) o) t2 = view_bar (v t2).
  Proof.
    intros. unfold H_bar; simpl. unfold upd_tid_view.
    destruct (Pos.eqb_spec t1 t2); [congruence | reflexivity].
  Qed.

  (** [G t]: thread [t]'s guarantee.
      - preserves other threads' [π] entries;
      - if some other thread owns the lock, this step does not change the
        underlay memory/lock histories nor the owner. *)
  Definition G (t : tid) : rg_relation :=
    fun s1 s2 =>
      (forall t', t <> t' ->
        TMap.find t' (π s1) = TMap.find t' (π s2))
      /\
	      (forall t', t <> t' ->
	        Pos.le (H_bar (state (σ s1)) t') (H_bar (state (σ s2)) t'))
	      /\
	      (forall t', t <> t' ->
	        forall l, Pos.le (SeqLockUnderlaySpec.sl_view (state (σ s1)) t' l)
	                         (SeqLockUnderlaySpec.sl_view (state (σ s2)) t' l))
	      /\
	      (forall owner,
	        sl_owner (state (σ s1)) = Some owner -> owner <> t ->
	          sl_owner (state (σ s2)) = Some owner /\
          PreserveUL s1 s2 /\
          SeqLockUnderlaySpec.sl_view (state (σ s1)) owner =
            SeqLockUnderlaySpec.sl_view (state (σ s2)) owner)
      /\
      (* reverse: environment can't give ownership to a non-stepping thread *)
      (forall t', t <> t' ->
        sl_owner (state (σ s2)) = Some t' -> sl_owner (state (σ s1)) = Some t')
      /\
      (forall t', t <> t' ->
        forall l h, Pos.le h (H_bar (state (σ s1)) t') ->
          sl_mem (state (σ s1)) l h = sl_mem (state (σ s2)) l h)
      /\
      (forall t', t <> t' ->
        forall h, Pos.le h (H_bar (state (σ s1)) t') ->
          sl_lock (state (σ s1)) h = sl_lock (state (σ s2)) h).

  Lemma G_refl : forall t s, G t s s.
  Proof.
    unfold G, PreserveUL.
    intros t s.
    repeat split; intros; try reflexivity; try assumption; apply Pos.le_refl.
  Qed.

  Lemma G_same_state : forall t (σ1 σ2 : State (li_lts E)) (ρ : State (li_lts F)) π,
    state σ1 = state σ2 ->
    G t (σ1, ρ, π) (σ2, ρ, π).
  Proof.
    unfold G, PreserveUL.
    intros t σ1 σ2 ρ π Hstate; simpl in *.
    rewrite Hstate.
    repeat split; intros; try reflexivity; try assumption; apply Pos.le_refl.
  Qed.

  Lemma G_view_advance_current :
    forall t (σ0 : State (li_lts E)) ρ0 π0 (s : SSeqLockUL) h,
      state σ0 = s ->
      G t (σ0, ρ0, π0)
        ((Idle (mkSLUL (sl_mem s) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
            (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
          (sl_owner s)) : State (li_lts E)), ρ0, π0).
  Proof.
    unfold G, PreserveUL.
    intros t σ0 ρ0 π0 s h Hstate. simpl. rewrite Hstate. simpl.
    split; [intros t' Hneq; reflexivity|].
    split; [intros t' Hneq; rewrite Hbar_upd_tid_view_neq by auto; apply Pos.le_refl|].
    split; [intros t' Hneq l; unfold upd_tid_view; destruct (Pos.eqb_spec t t'); [congruence|apply Pos.le_refl]|].
    split.
    - intros owner Hown Hneq.
      split; [exact Hown|].
      split; [split; reflexivity|].
      unfold upd_tid_view.
      destruct (Pos.eqb_spec t owner); [congruence|reflexivity].
    - split; [intros t' Hneq Hown; exact Hown|].
      split; [intros t' Hneq l h' Hle; reflexivity|].
      intros t' Hneq h' Hle; reflexivity.
  Qed.

  (** [R t]: thread [t]'s rely.
      - own [π] entry is preserved;
      - while [t] owns the lock, the environment cannot change the underlay
        memory/lock histories nor the owner. *)
  Definition R (t : tid) : rg_relation :=
    fun s1 s2 =>
      TMap.find t (π s1) = TMap.find t (π s2)
      /\
	      Pos.le (H_bar (state (σ s1)) t) (H_bar (state (σ s2)) t)
	      /\
	      (forall l, Pos.le (SeqLockUnderlaySpec.sl_view (state (σ s1)) t l)
	                       (SeqLockUnderlaySpec.sl_view (state (σ s2)) t l))
	      /\
	      (sl_owner (state (σ s1)) = Some t ->
	        sl_owner (state (σ s2)) = Some t /\
        PreserveUL s1 s2 /\
        SeqLockUnderlaySpec.sl_view (state (σ s1)) t =
          SeqLockUnderlaySpec.sl_view (state (σ s2)) t)
      /\
      (* reverse: environment can't give t ownership *)
      (sl_owner (state (σ s2)) = Some t -> sl_owner (state (σ s1)) = Some t)
      /\
      (forall l h, Pos.le h (H_bar (state (σ s1)) t) ->
        sl_mem (state (σ s1)) l h = sl_mem (state (σ s2)) l h)
      /\
      (forall h, Pos.le h (H_bar (state (σ s1)) t) ->
        sl_lock (state (σ s1)) h = sl_lock (state (σ s2)) h).

  (* ------------------------------------------------------------------ *)
  (** *** Stability lemmas *)

  (* helper: ALin transfers along π-equality *)
  Lemma ALin_transfer {t ls} {x s : @ProofState _ _ (li_lts E) (li_lts F)} :
    ALin t ls x ->
    TMap.find t (π x) = TMap.find t (π s) ->
    ALin t ls s.
  Proof.
    unfold ALin. intros. congruence.
  Qed.

  Lemma Istable {t} : Stable (R t) I I.
  Proof.
    unfold Stable.
    apply ConjRightImpl, ImplRefl.
  Qed.

  Lemma ALinstable {t ls} : Stable (R t) I (ALin t ls).
  Proof.
    unfold Stable, R.
    intros s [[x [Hlinx Hrely]] _].
    destruct Hrely as [Hπeq _].
    exact (ALin_transfer Hlinx Hπeq).
  Qed.

  Create HintDb slStableDB.
  Hint Resolve Istable ALinstable : slStableDB.

  (* ------------------------------------------------------------------ *)
  (** *** Ginv / Gret interaction with I *)

  Lemma IGinv : forall t f,
    ⊨ Ginv t f ⊚ I ==>> I //\\ ALin t (Semantics.ls_inv f).
  Proof.
    unfold I, ALin, Ginv, LiftRelation_π.
    intros t f s [x [HI (Hσeq & Hρeq & Hfind & Hπeq)]].
    destruct s, x; simpl in *; subst.
    split; [exact HI|].
    simpl. rewrite TMap.gss. reflexivity.
  Qed.

  Lemma IGret : forall t f ret,
    ⊨ Gret t f ret ⊚ (I //\\ ALin t (Semantics.ls_linr f ret)) ==>> I.
  Proof.
    unfold I, ALin, Gret, LiftRelation_π.
    intros. intros [? [[? ?] ?]].
    destruct H1 as [? [? [? ?]]].
    destruct s, x; simpl in *; subst. auto.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** Writer-specific predicates *)

  (** After [acq]: the writer holds the lock, [I] still holds for the
      overlay, and the thread's linearization state is [ls_inv]. *)
  Definition WriterAcquired (t : tid) (vx' vy' : nat) : assertion :=
    fun s =>
      I s /\ ALin t (Semantics.ls_inv (write vx' vy')) s.

  (** The writer has acquired ownership of the lock in the underlay. *)
  Definition WriterHolding (t : tid) (vx' vy' : nat) : assertion :=
    fun s =>
      I s /\ ALin t (Semantics.ls_inv (write vx' vy')) s /\
      sl_owner (state (σ s)) = Some t /\
      (forall h,
        Pos.le (SeqLockUnderlaySpec.sl_view (state (σ s)) t aloc_lk) h ->
        Nat.odd (snd (sl_lock (state (σ s)) h)) = true).

  Lemma WriterAcquiredStable {t vx' vy'} :
    Stable (R t) I (WriterAcquired t vx' vy').
  Proof. 
    unfold WriterAcquired.
    apply ConjStable; eauto with slStableDB.
    
    Qed.
  Lemma WriterHoldingStable {t vx' vy'} :
    Stable (R t) I (WriterHolding t vx' vy').
  Proof.
    unfold Stable, WriterHolding, R.
    intros s [[x [HxHold Hrely]] HI].
    destruct HxHold as [HIx [Hlinx [Hownerx Hbusyx]]].
	    destruct Hrely as [Hπeq [_ [_ [Hguard _]]]].
    specialize (Hguard Hownerx) as [Howners [Hpres Hvieweq]].
    destruct Hpres as [_ Hlockeq].
    split; [exact HI|].
    split.
    - exact (ALin_transfer Hlinx Hπeq).
    - split; [exact Howners|].
      intros h Hle.
      rewrite <- Hlockeq.
      pose proof (f_equal (fun v => v aloc_lk) Hvieweq) as Hviewlk.
      apply Hbusyx.
      rewrite Hviewlk. exact Hle.
  Qed.


  (** After [wrt x]: x has been updated in memory. *)
  Definition WriterWroteX (t : tid) (vx' vy' : nat) : assertion :=
    fun s =>
      WriterHolding t vx' vy' s /\
      (forall h, Pos.le (SeqLockUnderlaySpec.sl_view (state (σ s)) t aloc_x) h ->
        sl_mem (state (σ s)) loc_x h = vx').

  Lemma WriterWroteXStable {t vx' vy'} :
    Stable (R t) I (WriterWroteX t vx' vy').
  Proof.
    unfold Stable, WriterWroteX, R.
    intros s [[x [[HxHold HxMemX] Hrely]] HI].
	    destruct Hrely as [Hπeq [_ [_ [Hguard _]]]].
    unfold WriterHolding in HxHold.
    destruct HxHold as [HIx [Hlinx [Hownerx Hbusyx]]].
    specialize (Hguard Hownerx) as [Howners [Hpres Hvieweq]].
    destruct Hpres as [Hmem_eq Hlock_eq].
    split.
    - (* WriterHolding preserved *)
      unfold WriterHolding.
      split; [exact HI|].
      split.
      + exact (ALin_transfer Hlinx Hπeq).
      + split; [exact Howners|].
        intros h Hle.
        rewrite <- Hlock_eq.
        pose proof (f_equal (fun v => v aloc_lk) Hvieweq) as Hviewlk.
        apply Hbusyx.
        rewrite Hviewlk. exact Hle.
    - (* memory fact preserved *)
      intros h Hle.
      rewrite <- Hmem_eq.
      pose proof (f_equal (fun v => v aloc_x) Hvieweq) as Hviewx.
      apply HxMemX.
      rewrite Hviewx. exact Hle.
  Qed.

  (** After [wrt y]: both x and y have been updated. *)
  Definition WriterWroteXY (t : tid) (vx' vy' : nat) : assertion :=
    fun s =>
      WriterWroteX t vx' vy' s /\
      (forall h, Pos.le (SeqLockUnderlaySpec.sl_view (state (σ s)) t aloc_y) h ->
        sl_mem (state (σ s)) loc_y h = vy').

  Lemma WriterWroteXYStable {t vx' vy'} :
    Stable (R t) I (WriterWroteXY t vx' vy').
  Proof.
    unfold Stable, WriterWroteXY, WriterWroteX, R.
    intros s [[x [[HxWroteX HxMemY] Hrely]] HI].
	    destruct Hrely as [Hπeq [_ [_ [Hguard _]]]].

    (* unpack the source facts *)
    destruct HxWroteX as [HxHold HxMemX].
    unfold WriterHolding in HxHold.
    destruct HxHold as [HIx [Hlinx [Hownerx Hbusyx]]].
    specialize (Hguard Hownerx) as [Howners [Hpres Hvieweq]].
    destruct Hpres as [Hmem_eq Hlock_eq].

    split.
    - (* WriterWroteX preserved *)
      split.
      + (* WriterHolding *)
        unfold WriterHolding.
        split; [exact HI|].
        split.
        * exact (ALin_transfer Hlinx Hπeq).
        * split; [exact Howners|].
          intros h Hle.
          rewrite <- Hlock_eq.
          pose proof (f_equal (fun v => v aloc_lk) Hvieweq) as Hviewlk.
          apply Hbusyx.
          rewrite Hviewlk. exact Hle.
      + (* X memory *)
        intros h Hle.
        rewrite <- Hmem_eq.
        pose proof (f_equal (fun v => v aloc_x) Hvieweq) as Hviewx.
        apply HxMemX.
        rewrite Hviewx. exact Hle.
    - (* Y memory preserved *)
      intros h Hle.
      rewrite <- Hmem_eq.
      pose proof (f_equal (fun v => v aloc_y) Hvieweq) as Hviewy.
      apply HxMemY.
      rewrite Hviewy. exact Hle.
  Qed.

  (* ------------------------------------------------------------------ *)
  (** *** Reader-specific predicates *)

  (** Loop invariant for the reader: [I] holds and the thread's lin
      state is [ls_inv read]. *)
  Definition ReaderLoop (t : tid) : assertion :=
    fun s => I s /\ ALin t (Semantics.ls_inv read) s.

  Lemma ReaderLoopStable {t} : Stable (R t) I (ReaderLoop t).
  Proof.
    unfold Stable, ReaderLoop, R.
    intros s [[x [[HIx Hlinx] Hrely]] HI].
    destruct Hrely as [Hπeq _].
    split; [exact HI|].
    exact (ALin_transfer Hlinx Hπeq).
  Qed.

  (** After [get_ticket]: records the ticket value [now] and the
      timestamp [h_get] at which it was read.  After view_advance,
      [h_get <= H_bar(t)], so lock/mem at [h_get] is stable under R. *)
  Definition ReaderGotTicket (t : tid) (now : nat) : assertion :=
    fun s =>
      I s /\ ALin t (Semantics.ls_inv read) s /\
	      exists h_get,
	        Pos.le h_get (H_bar (state (σ s)) t) /\
	        (forall l, Pos.le h_get (SeqLockUnderlaySpec.sl_view (state (σ s)) t l)) /\
	        snd (sl_lock (state (σ s)) h_get) = now.

  Lemma ReaderGotTicketStable {t now} :
    Stable (R t) I (ReaderGotTicket t now).
  Proof.
    unfold Stable, ReaderGotTicket, R.
    intros s [[x [Hpre Hrely]] HI].
	    destruct Hpre as [HIx [Hlinx [h_get [Hle_hget [Hview_hget Hlock_hget]]]]].
	    destruct Hrely as [Hπeq [Hbar_mono [Hview_mono [_ [_ [Hmem_pres Hlock_pres]]]]]].
    split; [exact HI|].
    split; [exact (ALin_transfer Hlinx Hπeq)|].
    exists h_get.
	    repeat split.
	    - eapply Pos.le_trans; [exact Hle_hget | exact Hbar_mono].
	    - intro l. eapply Pos.le_trans; [exact (Hview_hget l) | exact (Hview_mono l)].
	    - rewrite <- Hlock_pres; [exact Hlock_hget | exact Hle_hget].
  Qed.

  (** After reading x and y: carries the timestamps [h_get], [hx], [hy]
      and witnesses [vx = mem x hx], [vy = mem y hy].  All timestamps
      are [<= H_bar(t)], so the equalities are stable under the new R. *)
  Definition ReaderSnapped (t : tid) (now : nat) (vx vy : nat) : assertion :=
    fun s =>
      I s /\ ALin t (Semantics.ls_inv read) s /\
      exists h_get hx hy,
	        Pos.le h_get (H_bar (state (σ s)) t) /\
	        Pos.le hx (H_bar (state (σ s)) t) /\
	        Pos.le hy (H_bar (state (σ s)) t) /\
	        Pos.le h_get hx /\
	        Pos.le h_get hy /\
	        snd (sl_lock (state (σ s)) h_get) = now /\
        sl_mem (state (σ s)) loc_x hx = vx /\
        sl_mem (state (σ s)) loc_y hy = vy.

  Lemma ReaderSnappedStable {t now vx vy} :
    Stable (R t) I (ReaderSnapped t now vx vy).
  Proof.
    unfold Stable, ReaderSnapped, R.
    intros s [[x [Hpre Hrely]] HI].
	    destruct Hpre as (HIx & Hlinx & h_get & hx & hy & Hle_hget & Hle_hx & Hle_hy & Hget_le_hx & Hget_le_hy & Hlock_hget & Hmem_hx & Hmem_hy).
	    destruct Hrely as [Hπeq [Hbar_mono [_ [_ [_ [Hmem_pres Hlock_pres]]]]]].
    split; [exact HI|].
    split; [exact (ALin_transfer Hlinx Hπeq)|].
    exists h_get, hx, hy.
    repeat split.
	    - eapply Pos.le_trans; [exact Hle_hget | exact Hbar_mono].
	    - eapply Pos.le_trans; [exact Hle_hx | exact Hbar_mono].
	    - eapply Pos.le_trans; [exact Hle_hy | exact Hbar_mono].
	    - exact Hget_le_hx.
	    - exact Hget_le_hy.
	    - rewrite <- Hlock_pres; [exact Hlock_hget | exact Hle_hget].
    - rewrite <- Hmem_pres; [exact Hmem_hx | exact Hle_hx].
    - rewrite <- Hmem_pres; [exact Hmem_hy | exact Hle_hy].
  Qed.

  (** After reading x (but not yet y): carries [h_get] and [hx]
      witnesses.  No [hy] yet — that comes from [rd loc_y]. *)
  Definition ReaderReadX (t : tid) (now : nat) (vx : nat) : assertion :=
    fun s =>
      I s /\ ALin t (Semantics.ls_inv read) s /\
      exists h_get hx,
	        Pos.le h_get (H_bar (state (σ s)) t) /\
	        Pos.le hx (H_bar (state (σ s)) t) /\
	        (forall l, Pos.le h_get (SeqLockUnderlaySpec.sl_view (state (σ s)) t l)) /\
	        Pos.le h_get hx /\
	        snd (sl_lock (state (σ s)) h_get) = now /\
        sl_mem (state (σ s)) loc_x hx = vx.

  Lemma ReaderReadXStable {t now vx} :
    Stable (R t) I (ReaderReadX t now vx).
  Proof.
    unfold Stable, ReaderReadX, R.
    intros s [[x [Hpre Hrely]] HI].
	    destruct Hpre as (HIx & Hlinx & h_get & hx & Hle_hget & Hle_hx & Hview_hget & Hget_le_hx & Hlock_hget & Hmem_hx).
	    destruct Hrely as [Hπeq [Hbar_mono [Hview_mono [_ [_ [Hmem_pres Hlock_pres]]]]]].
    split; [exact HI|].
    split; [exact (ALin_transfer Hlinx Hπeq)|].
    exists h_get, hx.
    repeat split.
	    - eapply Pos.le_trans; [exact Hle_hget | exact Hbar_mono].
	    - eapply Pos.le_trans; [exact Hle_hx | exact Hbar_mono].
	    - intro l. eapply Pos.le_trans; [exact (Hview_hget l) | exact (Hview_mono l)].
	    - exact Hget_le_hx.
    - rewrite <- Hlock_pres; [exact Hlock_hget | exact Hle_hget].
    - rewrite <- Hmem_pres; [exact Hmem_hx | exact Hle_hx].
  Qed.

  (** Key step: linearization at [test_ticket].
      The [busy=true] case is a stutter on the overlay side.
      The [busy=false] case is the remaining proof obligation (the
      actual linearization of the overlay [read] with return [(vx,vy)]). *)

  (* H_bar monotonicity: view_advance only increases H_bar *)
  Lemma Hbar_view_advance_mono :
    forall s t h h_c,
      (forall t0, Pos.le h_c (H_bar s t0)) ->
      Pos.le h_c
        (H_bar (mkSLUL (sl_mem s) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
          (sl_owner s)) t).
  Proof.
    intros s t h h_c Hybar.
    unfold H_bar; simpl. unfold upd_tid_view.
    rewrite Pos.eqb_refl.
    specialize (Hybar t).
    eapply Pos.le_trans; [exact Hybar|].
    unfold view_bar, view_advance.
    apply Pos.max_lub.
    - apply Pos.max_lub.
      + eapply Pos.le_trans; [apply Pos.le_max_l|].
        eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_l.
      + eapply Pos.le_trans; [apply Pos.le_max_l|].
        eapply Pos.le_trans; [apply Pos.le_max_r|]. apply Pos.le_max_l.
    - eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_r.
  Qed.

  Lemma Hbar_view_advance_other :
    forall s t h h_c t',
      t <> t' ->
      (forall t0, Pos.le h_c (H_bar s t0)) ->
      Pos.le h_c
        (H_bar (mkSLUL (sl_mem s) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
          (sl_owner s)) t').
  Proof.
    intros s t h h_c t' Hneq Hybar.
    unfold H_bar; simpl. unfold upd_tid_view.
    destruct (Pos.eqb_spec t t'); [congruence|].
    exact (Hybar t').
  Qed.

  Lemma Hbar_view_advance_all :
    forall (s : SSeqLockUL) (t : tid) (h h_c : Time),
      (forall t0, Pos.le h_c (H_bar s t0)) ->
      forall t0, Pos.le h_c
        (H_bar (mkSLUL (sl_mem s) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
          (sl_owner s)) t0).
  Proof.
    intros s t h h_c Hybar t0.
    unfold H_bar; simpl. unfold upd_tid_view.
    destruct (Pos.eqb_spec t t0) as [Heq|Hneq].
    - subst t0.
      specialize (Hybar t).
      eapply Pos.le_trans; [exact Hybar|].
      unfold view_bar, view_advance.
      apply Pos.max_lub.
      + apply Pos.max_lub.
        * eapply Pos.le_trans; [apply Pos.le_max_l|].
          eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_l.
        * eapply Pos.le_trans; [apply Pos.le_max_l|].
          eapply Pos.le_trans; [apply Pos.le_max_r|]. apply Pos.le_max_l.
      + eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_r.
    - exact (Hybar t0).
	  Qed.

  Lemma ReadWindowConsistent_view_advance :
    forall (s : SSeqLockUL) (ols : SSeqLock) (h_tail : Time) (t : tid) (h : Time),
      ReadWindowConsistent s ols h_tail ->
      ReadWindowConsistent
        (mkSLUL (sl_mem s) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
            (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
          (sl_owner s))
        ols h_tail.
  Proof.
    unfold ReadWindowConsistent.
    intros s ols h_tail t h Hrwc tr now h_get hx hy h_test
      Htailget Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven.
    eapply Hrwc; eauto.
    intro t0.
    specialize (Hfresh t0).
    destruct (Pos.eqb_spec t t0) as [Heq|Hneq].
    - subst t0.
      eapply Pos.le_lt_trans; [|exact Hfresh].
      apply Hbar_view_advance_le.
    - rewrite Hbar_upd_tid_view_neq in Hfresh by auto.
      exact Hfresh.
  Qed.

  Lemma SuccessfulReadWindowAfterTail_view_advance :
    forall (s : SSeqLockUL) (h_tail : Time) (t : tid) (h : Time),
      SuccessfulReadWindowAfterTail s h_tail ->
      SuccessfulReadWindowAfterTail
        (mkSLUL (sl_mem s) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
            (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
          (sl_owner s))
        h_tail.
  Proof.
    unfold SuccessfulReadWindowAfterTail.
    intros s h_tail t h Hafter tr now h_get hx hy h_test
      Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven.
    eapply Hafter; eauto.
    intro t0.
    specialize (Hfresh t0).
    destruct (Pos.eqb_spec t t0) as [Heq|Hneq].
    - subst t0.
      eapply Pos.le_lt_trans; [|exact Hfresh].
      apply Hbar_view_advance_le.
    - rewrite Hbar_upd_tid_view_neq in Hfresh by auto.
      exact Hfresh.
  Qed.

  Lemma LockHistoryBounded_view_advance :
    forall (s : SSeqLockUL) (h_tail : Time) (n_tail : nat) (t : tid) (h : Time),
      LockHistoryBounded s h_tail n_tail ->
      LockHistoryBounded
        (mkSLUL (sl_mem s) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
            (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
          (sl_owner s))
        h_tail n_tail.
  Proof.
    unfold LockHistoryBounded. simpl. auto.
  Qed.

  Lemma LockViewsAfterTail_view_advance :
    forall (s : SSeqLockUL) (h_tail : Time) (t : tid) (h : Time),
      (forall t0, Pos.le h_tail (SeqLockUnderlaySpec.sl_view s t0 aloc_lk)) ->
      forall t0,
        Pos.le h_tail
          (SeqLockUnderlaySpec.sl_view
            (mkSLUL (sl_mem s) (sl_lock s)
              (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
                (view_advance (SeqLockUnderlaySpec.sl_view s t) h))
              (sl_owner s)) t0 aloc_lk).
  Proof.
    intros s h_tail t h Hlk t0. simpl.
    unfold upd_tid_view.
    destruct (Pos.eqb_spec t t0) as [->|Hneq].
    - unfold view_advance. eapply Pos.le_trans; [apply Hlk|apply Pos.le_max_l].
    - apply Hlk.
  Qed.

  Lemma LockViewsAfterTail_wrt :
    forall (s : SSeqLockUL) (h_tail : Time) (t : tid) (l : MemLoc) (h : Time) (w : nat),
      (forall t0, Pos.le h_tail (SeqLockUnderlaySpec.sl_view s t0 aloc_lk)) ->
      forall t0,
        Pos.le h_tail
          (SeqLockUnderlaySpec.sl_view
            (mkSLUL (mem_write (sl_mem s) l h w) (sl_lock s)
              (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
                (view_set (SeqLockUnderlaySpec.sl_view s t) (mem_to_all l) h))
              (sl_owner s)) t0 aloc_lk).
  Proof.
    intros s h_tail t l h w Hlk t0. simpl.
    unfold upd_tid_view.
    destruct (Pos.eqb_spec t t0) as [->|Hneq].
    - destruct l; simpl; apply Hlk.
    - apply Hlk.
  Qed.

  Lemma LockViewsAfterTail_acq :
    forall (s : SSeqLockUL) (h_tail hp : Time) (t : tid) (own : nat),
      (forall t0, Pos.le h_tail (SeqLockUnderlaySpec.sl_view s t0 aloc_lk)) ->
      Pos.lt h_tail hp ->
      forall t0,
        Pos.le h_tail
          (SeqLockUnderlaySpec.sl_view
            (mkSLUL (sl_mem s)
              (lock_write (sl_lock s) hp (own + 2) (own + 1))
              (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
                (view_set (SeqLockUnderlaySpec.sl_view s t) aloc_lk hp))
              (Some t)) t0 aloc_lk).
  Proof.
    intros s h_tail hp t own Hlk Htail_hp t0. simpl.
    unfold upd_tid_view.
    destruct (Pos.eqb_spec t t0) as [->|Hneq].
    - unfold view_set. simpl. apply Pos.lt_le_incl. exact Htail_hp.
    - apply Hlk.
  Qed.

  Lemma LockViewsAfterTail_release :
    forall (s : SSeqLockUL) (hp : Time) (nxt own : nat),
      forall t0,
        Pos.le hp
          (SeqLockUnderlaySpec.sl_view
            (mkSLUL (sl_mem s)
              (lock_write (sl_lock s) hp nxt (own + 1)%nat)
              (fun t' => view_advance (SeqLockUnderlaySpec.sl_view s t') hp)
              None) t0 aloc_lk).
  Proof.
    intros s hp nxt own t0. simpl.
    unfold view_advance. apply Pos.le_max_r.
  Qed.

  Lemma LockHistoryBounded_wrt :
    forall (s : SSeqLockUL) (h_tail : Time) (n_tail : nat) (t : tid) (l : MemLoc) (h : Time) (w : nat),
      LockHistoryBounded s h_tail n_tail ->
      LockHistoryBounded
        (mkSLUL (mem_write (sl_mem s) l h w) (sl_lock s)
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
            (view_set (SeqLockUnderlaySpec.sl_view s t) (mem_to_all l) h))
          (sl_owner s))
        h_tail n_tail.
  Proof.
    unfold LockHistoryBounded. simpl. auto.
  Qed.

  Lemma LockHistoryBounded_acq :
    forall (s : SSeqLockUL) (h_tail : Time) (n_tail own : nat) (hp : Time) (t : tid),
      Nat.even n_tail = true ->
      LockHistoryBounded s h_tail n_tail ->
      Pos.lt h_tail hp ->
      Pos.le h_tail (SeqLockUnderlaySpec.sl_view s t aloc_lk) ->
      sl_lock s (SeqLockUnderlaySpec.sl_view s t aloc_lk) = (own, own) ->
      Nat.even own = true ->
      LockHistoryBounded
        (mkSLUL (sl_mem s)
          (lock_write (sl_lock s) hp (own + 2) (own + 1))
          (upd_tid_view (SeqLockUnderlaySpec.sl_view s) t
            (view_set (SeqLockUnderlaySpec.sl_view s t) aloc_lk hp))
          (Some t))
        h_tail n_tail.
  Proof.
    intros s h_tail n_tail own hp t Heven_tail [Hbelow Habove] Htail_hp Htail_view Hlock_view Heven_own.
    specialize (Habove _ Htail_view) as Hown_cases.
    rewrite Hlock_view in Hown_cases. simpl in Hown_cases.
    assert (Hown_tail : own = n_tail).
    { destruct Hown_cases as [->|Hsucc]; [reflexivity|].
      exfalso.
      rewrite Hsucc in Heven_own.
      rewrite <- PeanoNat.Nat.negb_odd in Heven_own.
      rewrite PeanoNat.Nat.odd_succ in Heven_own.
      rewrite Heven_tail in Heven_own. discriminate. }
    subst own.
    unfold LockHistoryBounded. simpl.
    split.
    - intros q Hq. unfold lock_write.
      destruct (Pos.leb hp q) eqn:Hle.
      + apply Pos.leb_le in Hle.
        exfalso. eapply Pos.lt_irrefl.
        eapply Pos.lt_le_trans; [exact Hq|].
        eapply Pos.le_trans; [|exact Hle].
        apply Pos.lt_le_incl. exact Htail_hp.
      + apply Hbelow. exact Hq.
    - intros q Hq. unfold lock_write.
      destruct (Pos.leb hp q) eqn:Hle.
      + simpl. right. lia.
      + apply Habove. exact Hq.
  Qed.

  Lemma LockHistoryBounded_release :
    forall (s : SSeqLockUL) (h_tail hp : Time) (n_tail nxt own : nat) (t : tid),
      Nat.even n_tail = true ->
      LockHistoryBounded s h_tail n_tail ->
      Pos.le h_tail (SeqLockUnderlaySpec.sl_view s t aloc_lk) ->
      sl_lock s (SeqLockUnderlaySpec.sl_view s t aloc_lk) = (nxt, own) ->
      nxt = (own + 1)%nat ->
      Nat.even nxt = true ->
      LockHistoryBounded
        (mkSLUL (sl_mem s)
          (lock_write (sl_lock s) hp nxt (own + 1)%nat)
          (fun t' => view_advance (SeqLockUnderlaySpec.sl_view s t') hp)
          None)
        hp nxt.
  Proof.
    intros s h_tail hp n_tail nxt own t Heven_tail [Hbelow Habove] Htail_view Hlock_view Hnxt Heven_nxt.
    specialize (Habove _ Htail_view) as Hown_cases.
    rewrite Hlock_view in Hown_cases. simpl in Hown_cases.
    assert (Hown_succ : own = S n_tail).
    { destruct Hown_cases as [Hown|Hown].
      - subst own. subst nxt.
        rewrite PeanoNat.Nat.add_1_r in Heven_nxt.
        rewrite <- PeanoNat.Nat.negb_odd in Heven_nxt.
        rewrite PeanoNat.Nat.odd_succ in Heven_nxt.
        rewrite Heven_tail in Heven_nxt. discriminate.
      - exact Hown. }
    subst own. rewrite PeanoNat.Nat.add_1_r in Hnxt. subst nxt.
    unfold LockHistoryBounded. simpl.
    split.
    - intros q Hq. unfold lock_write.
      destruct (Pos.leb hp q) eqn:Hle.
      + apply Pos.leb_le in Hle.
        exfalso. eapply Pos.lt_irrefl. eapply Pos.lt_le_trans; eauto.
      + destruct (Pos.ltb q h_tail) eqn:Hlt_tail.
        * apply Pos.ltb_lt in Hlt_tail.
          specialize (Hbelow _ Hlt_tail). lia.
        * apply Pos.ltb_ge in Hlt_tail.
          specialize (Habove _ Hlt_tail) as [Hsame|Hsucc]; lia.
    - intros q Hq. unfold lock_write.
      rewrite (proj2 (Pos.leb_le hp q)) by exact Hq.
      simpl. left. lia.
  Qed.

  Lemma WriterHolding_read_window_contradiction :
    forall (σs : SSeqLockUL) (now : nat) (h_test : Time),
      Nat.odd (snd (sl_lock σs h_test)) = true ->
      sl_lock σs h_test = (now, now) ->
      Nat.even now = true ->
      False.
  Proof.
    intros σs now h_test Hodd Hlock Heven.
    rewrite Hlock in Hodd. simpl in Hodd.
    rewrite <- PeanoNat.Nat.negb_odd in Heven.
    rewrite Hodd in Heven. discriminate.
  Qed.

  Lemma ReadWindowConsistent_release :
    forall (σs : SSeqLockUL) (ols : SSeqLock) (h : Time) (nxt own : nat),
      (forall hx, Pos.le h hx -> sl_mem σs loc_x hx = sl_vx ols) ->
      (forall hy, Pos.le h hy -> sl_mem σs loc_y hy = sl_vy ols) ->
      ReadWindowConsistent
        (mkSLUL (sl_mem σs)
          (lock_write (sl_lock σs) h nxt (own + 1))
          (fun t' => view_advance (SeqLockUnderlaySpec.sl_view σs t') h)
          None)
        ols h.
  Proof.
    unfold ReadWindowConsistent.
    intros σs ols h nxt own HmemX HmemY tr now h_get hx hy h_test
      Htailget Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven.
    simpl.
    split.
    - apply HmemX. eapply Pos.le_trans; eauto.
    - apply HmemY. eapply Pos.le_trans; eauto.
  Qed.

  Lemma SuccessfulReadWindowAfterTail_release :
    forall (σs : SSeqLockUL) (h : Time) (nxt own : nat),
      LockHistoryBounded
        (mkSLUL (sl_mem σs)
          (lock_write (sl_lock σs) h nxt (own + 1))
          (fun t' => view_advance (SeqLockUnderlaySpec.sl_view σs t') h)
          None)
        h nxt ->
      SuccessfulReadWindowAfterTail
        (mkSLUL (sl_mem σs)
          (lock_write (sl_lock σs) h nxt (own + 1))
          (fun t' => view_advance (SeqLockUnderlaySpec.sl_view σs t') h)
          None)
        h.
  Proof.
    unfold SuccessfulReadWindowAfterTail, LockHistoryBounded.
    intros σs h nxt own Hbound tr now h_get hx hy h_test
      Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven.
    destruct Hbound as [Hbelow _].
    simpl in *.
    assert (Hh_test : Pos.le h h_test).
    { specialize (Hfresh tr).
      eapply Pos.le_trans; [|apply Pos.lt_le_incl; exact Hfresh].
      unfold H_bar; simpl. unfold view_bar, view_advance.
      eapply Pos.le_trans; [|apply Pos.le_max_r].
      apply Pos.le_max_r. }
    unfold lock_write in Hlocktest.
    rewrite (proj2 (Pos.leb_le h h_test)) in Hlocktest by exact Hh_test.
    pose proof Hlockget as Hlockget_copy.
    inversion Hlocktest; subst.
    destruct (Pos.leb h h_get) eqn:Hle.
    - apply Pos.leb_le in Hle. exact Hle.
    - apply Pos.leb_gt in Hle.
      specialize (Hbelow h_get Hle). lia.
  Qed.


  Lemma ReaderTestTicketPUpdateRes_busy_true :
    forall (t : tid) (now vx vy : nat),
      PUpdate (G t)
        (Build_ThreadEvent t (ResEv (test_ticket now) true))
        (ReaderSnapped t now vx vy)
        (ReaderLoop t).
  Proof.
    intros t now vx vy.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.

    exists ρ0, π0.
    split; [apply rt_refl|].
	    destruct Hpre as (HI & Hlin & h_get & hx & hy & Hle_hget & Hle_hx & Hle_hy & Hget_le_hx & Hget_le_hy & Hlock_hget & Hmem_hx & Hmem_hy).
    inversion Hstep; subst. inversion Hstep0; subst.
    rewrite <- H3 in *; simpl in *; clear H3.
    split.
    - (* ReaderLoop preserved *)
      unfold ReaderLoop.
      split.
      + (* I preserved *)
        unfold I in *.
		        destruct HI as [[ls Hρ] [h_c [n [Hlock_hc [Heven [Hvx [Hvy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
	        simpl in *.
		        split; [exists ls; exact Hρ|].
		        exists h_c, n.
            split; [exact Hlock_hc|].
            split; [exact Heven|].
            split; [exact Hvx|].
	            split; [exact Hvy|].
		            split.
		            * apply Hbar_view_advance_all. exact Hybar.
		            * split.
		              -- apply LockViewsAfterTail_view_advance. exact Hlk.
		              -- split.
                     ++ apply LockHistoryBounded_view_advance. exact Hbound.
		                 ++ split.
	                    ** apply SuccessfulReadWindowAfterTail_view_advance. exact Hafter.
	                    ** apply ReadWindowConsistent_view_advance. exact Hrwc.
      + simpl. exact Hlin.
    - (* G *)
	      unfold G. simpl.
	      split; [intros t' Hneq; reflexivity|].
	      split; [intros t' Hneq; rewrite Hbar_upd_tid_view_neq by auto; apply Pos.le_refl|].
	      split; [intros t' Hneq l; unfold upd_tid_view; destruct (Pos.eqb_spec t t'); [congruence|apply Pos.le_refl]|].
	      split.
      + intros owner Hown Hneq.
        split; [assumption|].
        split; [unfold PreserveUL; split; reflexivity|].
        unfold upd_tid_view.
        destruct (Pos.eqb_spec t owner); [congruence|reflexivity].
      + split; [intros t' Hneq; auto|].
        split; [intros t' Hneq l h' Hle; reflexivity|].
        intros t' Hneq h' Hle; reflexivity.
  Qed.

  (* The lock is constant on [lo, hi] when lock(lo) = lock(hi) and the
     lock history is a step function overwritten only at globally fresh
     timestamps. When no lock_write fires in (lo, hi], the lock is constant. *)
  (* Key helper: if lock(h_c) = (n,n) with n even, lock is constant from
     h_c to h_test (both are <= all relevant timestamps), and
     lock(h_test) = (now, now) with now even, then n = now and
     memory is constant from h_c through all timestamps in the window. *)

  Lemma ReaderTestTicketPUpdateRes_busy_false :
    forall (t : tid) (now vx vy : nat),
      PUpdate (G t)
        (Build_ThreadEvent t (ResEv (test_ticket now) false))
        (ReaderSnapped t now vx vy)
        (I //\\ ALin t (Semantics.ls_linr read (vx, vy))).
  Proof.
    intros t now vx_read vy_read.
    unfold PUpdate.
    intros σ0 ρ0 π0 Hpre σ' Hstep.
    set (nowr := now) in *.

    (* Unpack ReaderSnapped *)
    destruct Hpre as (HI & Hlin & h_get & hx & hy & Hle_hget & Hle_hx & Hle_hy & Hget_le_hx & Hget_le_hy & Hlock_hget & Hmem_hx & Hmem_hy).
    unfold I in HI.
    destruct HI as [[ols Hρ] [h_c [n [Hlock_hc [Heven [Hvx [Hvy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
    rewrite Hρ in *. simpl in *.
    set (vxr := vx_read) in *.
    set (vyr := vy_read) in *.

    inversion Hstep; subst. inversion Hstep0; subst.
    simpl in *.
    apply Eqdep_dec.inj_pair2_eq_dec in H2; [subst r0 | repeat decide equality].
    apply step_test_ticket_res_inv in Hstep0.
    destruct Hstep0 as [h_test [ktest [Hfresh [Hlock_test [Hbusy Hσ']]]]].
    inversion Hσ'; subst; clear Hσ'.
    assert (sl_lock s1 h_test = (nowr, nowr) /\ Nat.even nowr = true) as [Hlock_h Hnow_even].
    {
      try rewrite Hlock_hget in Hbusy.
      try rewrite Hlock_hget in Hlock_test.
      symmetry in Hbusy.
      apply Bool.orb_false_iff in Hbusy.
      destruct Hbusy as [Hodd Hneqb].
      apply Bool.negb_false_iff in Hneqb.
      apply PeanoNat.Nat.eqb_eq in Hneqb. subst ktest.
      split; [exact Hlock_test|].
      rewrite <- PeanoNat.Nat.negb_odd. rewrite Hodd. reflexivity.
    }
    pose proof (Hrwc t nowr h_get hx hy h_test
      (Hafter t nowr h_get hx hy h_test
        Hget_le_hx Hget_le_hy
        (Pos.le_lt_trans _ _ _ Hle_hx (Hfresh t))
        (Pos.le_lt_trans _ _ _ Hle_hy (Hfresh t))
        Hfresh Hlock_hget Hlock_h Hnow_even)
      Hget_le_hx Hget_le_hy
      (Pos.le_lt_trans _ _ _ Hle_hx (Hfresh t))
      (Pos.le_lt_trans _ _ _ Hle_hy (Hfresh t))
      Hfresh Hlock_hget Hlock_h Hnow_even) as [Hmemx_ols Hmemy_ols].
    assert (Hvx_snap : SeqLock.sl_vx ols = vxr).
    { rewrite <- Hmem_hx. symmetry. exact Hmemx_ols. }
    assert (Hvy_snap : SeqLock.sl_vy ols = vyr).
    { rewrite <- Hmem_hy. symmetry. exact Hmemy_ols. }

    set (h_o := Pos.succ (SeqLock.sl_view ols t)).
    set (ols' := SeqLock.mkSL vxr vyr (SeqLock.upd_tid_time (SeqLock.sl_view ols) t h_o)).
    set (ρ' := (Idle ols' : State (li_lts F))).
    set (π1 := TMap.add t (Semantics.ls_lini read) π0).
    set (π' := TMap.add t (Semantics.ls_linr read (vxr, vyr)) π1).

    exists ρ', π'.
    split.
    - eapply rt_trans.
      + apply rt_step.
        eapply Semantics.ps_inv with (t := t) (f := read).
        * apply step_inv. apply step_read_inv.
        * exact Hlin.
      + apply rt_step.
        eapply Semantics.ps_ret with (t := t) (f := read) (ret := (vxr, vyr)).
        * apply step_res.
          replace (vxr, vyr) with (SeqLock.sl_vx ols, SeqLock.sl_vy ols)
            by (rewrite Hvx_snap, Hvy_snap; reflexivity).
          apply step_read_res with (h := h_o).
          -- apply Pos.lt_succ_diag_r.
          -- subst ols'. simpl. rewrite Hvx_snap, Hvy_snap. reflexivity.
        * subst π1. rewrite TMap.gss. reflexivity.
    - split.
      + split.
        * unfold I.
	          split; [exists ols'; reflexivity|].
	          exists h_c, n.
            split; [exact Hlock_hc|].
            split; [exact Heven|].
            split; [subst ols'; simpl; rewrite <- Hvx_snap; exact Hvx|].
	            split; [subst ols'; simpl; rewrite <- Hvy_snap; exact Hvy|].
		            split; [apply Hbar_view_advance_all; exact Hybar|].
		            split.
		            -- apply LockViewsAfterTail_view_advance. exact Hlk.
		            -- split.
                 ++ apply LockHistoryBounded_view_advance. exact Hbound.
                 ++ split.
	              ** apply SuccessfulReadWindowAfterTail_view_advance. exact Hafter.
		            ** unfold ReadWindowConsistent.
	               intros t0 now0 h_get0 hx0 hy0 h_test0 Htailget0 Hgetx0 Hgety0 Hxlt0 Hylt0 Hfresh0 Hlockget0 Hlocktest0 Heven0.
               pose proof (ReadWindowConsistent_view_advance s1 ols h_c t h Hrwc
                 t0 now0 h_get0 hx0 hy0 h_test0 Htailget0 Hgetx0 Hgety0 Hxlt0 Hylt0 Hfresh0 Hlockget0 Hlocktest0 Heven0)
                 as [Hrwc_x Hrwc_y].
	               subst ols'. simpl.
                 split; [rewrite <- Hvx_snap; exact Hrwc_x|rewrite <- Hvy_snap; exact Hrwc_y].
        * unfold ALin. subst π' π1. simpl. rewrite TMap.gss. reflexivity.
      + unfold G. simpl.
        split.
        { intros t' Hneq.
          subst π' π1. rewrite !TMap.gso by congruence. reflexivity. }
	        split.
	        { intros t' Hneq. rewrite Hbar_upd_tid_view_neq by auto. apply Pos.le_refl. }
	        split.
	        { intros t' Hneq l. unfold upd_tid_view.
	          destruct (Pos.eqb_spec t t'); [congruence|apply Pos.le_refl]. }
	        split.
	        { intros owner Hown Hneq.
          split; [assumption|].
          split; [unfold PreserveUL; split; reflexivity|].
          unfold upd_tid_view.
          destruct (Pos.eqb_spec t owner); [congruence|reflexivity]. }
        split; [intros t' Hneq; auto|].
        split; [intros t' Hneq l h' Hle; reflexivity|].
        intros t' Hneq h' Hle; reflexivity.
  Qed.
  (* ------------------------------------------------------------------ *)
  (** ** Layer implementation and proof *)

  Program Definition Mseqlock : layer_implementation E F :=
  {|
    li_impl m _ :=
      match m with
      | write vx' vy' => write_impl vx' vy'
      | read           => read_impl
      end
  |}.
  Next Obligation.
    eapply RGILogic.soundness with (R := R) (G := G) (I := I).

    (* ---- ValidRGI ---- *)
    {
      constructor.
      unfold R. intros s s' Hrely _.
      destruct Hrely as [Hfind _].
      split; intro Hnone; rewrite <- Hfind in *; exact Hnone.
    }

    (* ---- G t1 ∪ ... ⊆ R t2 ---- *)
    {
      unfold G, R.
      intros t1 t2 H.
      unfold Subset, Union.
      intros s1 s2 Hstep.
      destruct Hstep as [HG | Hstep].
      - (* G(t1) → R(t2) *)
	        destruct HG as [Gπ [Ghbar [Gview [Gguard [Grev [Gmem Glock]]]]]].
	        split; [apply Gπ; auto|].
	        split; [apply Ghbar; auto|].
	        split; [intro l; apply Gview; auto|].
	        split; [intro Howner;
	          specialize (Gguard t2 Howner (fun Heq => H (eq_sym Heq)));
          exact Gguard|].
        split; [intro Howner; exact (Grev t2 H Howner)|].
        split; [intros l h' Hle; exact (Gmem t2 H l h' Hle)|].
        intros h' Hle; exact (Glock t2 H h' Hle).
      - destruct Hstep as [HInv | Hid].
        + destruct HInv as [Hginv | Hrinv].
          * (* GINV: only π changes, σ/ρ unchanged *)
            destruct Hginv as [f Hginv].
            unfold Ginv, LiftRelation_π in Hginv.
            destruct Hginv as (Hσ & Hρ & (Hπ1 & Hπ2)).
            destruct s1 as [σ1 ρ1 π1']; destruct s2 as [σ2 ρ2 π2']; simpl in *.
	            subst.
	            split; [cbn; rewrite TMap.gso by auto; reflexivity|].
	            split; [apply Pos.le_refl|].
	            split; [intro l; apply Pos.le_refl|].
	            split; [intro Howner;
               split; [exact Howner|];
               split; [unfold PreserveUL; split; reflexivity|];
               reflexivity|].
            split; [auto|].
            split; [intros l h' Hle; reflexivity|].
            intros h' Hle; reflexivity.
          * (* GRET: only π changes, σ/ρ unchanged *)
            destruct Hrinv as [f [ret Hrinv]].
            unfold Gret, LiftRelation_π in Hrinv.
            destruct Hrinv as (Hσ & Hρ & (Hπ1 & Hπ2)).
            destruct s1 as [σ1 ρ1 π1']; destruct s2 as [σ2 ρ2 π2']; simpl in *.
	            subst.
	            split; [cbn; rewrite TMap.gro by auto; reflexivity|].
	            split; [apply Pos.le_refl|].
	            split; [intro l; apply Pos.le_refl|].
	            split; [intro Howner;
               split; [exact Howner|];
               split; [unfold PreserveUL; split; reflexivity|];
               reflexivity|].
            split; [auto|].
            split; [intros l h' Hle; reflexivity|].
            intros h' Hle; reflexivity.
        + (* GId *)
          unfold GId in Hid. subst.
	          split; [reflexivity|].
	          split; [apply Pos.le_refl|].
	          split; [intro l; apply Pos.le_refl|].
	          split; [intro Howner;
            split; [exact Howner|];
            split; [unfold PreserveUL; split; reflexivity|];
            reflexivity|].
          split; [auto|].
          split; [intros l h' Hle; reflexivity|].
          intros h' Hle; reflexivity.
    }

    (* ---- MethodProvable ---- *)
    {
      intros t. destruct f.

      (* ================================================================ *)
      (* METHOD: write vx' vy'                                            *)
      (* ================================================================ *)
      {
        (* pre/post conditions *)
        exists (I //\\ ALin t (Semantics.ls_inv (write vx' vy'))).
        exists (fun ret => I //\\ ALin t (Semantics.ls_linr (write vx' vy') ret)).
        constructor;
        try solve_conj_impl;
        try solve_conj_stable slStableDB;
        try apply IGinv; try apply IGret.
        { unfold ALin. intros. destruct H; auto. }

        simpl. unfold write_impl.

        (* -- step 1: acq -- *)
        eapply provable_vis_safe with
          (P' := WriterAcquired t vx' vy')
          (Q' := fun _ => WriterHolding t vx' vy').
        (* Herror: safe *)
        { intros ? _. unfold ANoError. intro Herr.
          destruct (σ s); inversion Herr; subst; inversion Herror. }
        { unfold WriterAcquired. intros ? [? _]; auto. }
        { intros _. unfold WriterHolding. intros ? [? _]; auto. }
        { apply WriterAcquiredStable. }
        { intros _. apply WriterHoldingStable. }
        (* PUpdate inv *)
        {
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          do 2 eexists. split; [apply rt_refl|]. split.
          - destruct Hpre as [HI Hlin].
            inversion Hstep0; subst.
            unfold WriterAcquired.
            split; simpl; assumption.
          - inversion Hstep0; subst.
	            unfold G. simpl.
	            split; [intros t' Hneq; reflexivity|].
	            split; [intros t' Hneq; apply Pos.le_refl|].
	            split; [intros t' Hneq l; apply Pos.le_refl|].
	            split; [intros owner Hown Hneq;
              split; [assumption|];
              split; [unfold PreserveUL; split; reflexivity|];
              reflexivity|].
            split; [intros t' Hneq; auto|].
            split; [intros t' Hneq l h' Hle; reflexivity|].
            intros t' Hneq h' Hle; reflexivity.
        }
        (* PUpdate res *)
        {
          intro ret.
          destruct ret.
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          exists ρ0, π0.
          split; [apply rt_refl|]. split.
          - destruct Hpre as [HI Hlin].
            unfold WriterHolding; split.
            + destruct HI as [[ls Hρ] [h_c [n [Hlock_hc [Heven [Hx [Hy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
              inversion Hstep; subst.
              split.
	              * exists ls; exact Hρ.
	              * exists h_c, n.
	                inversion Hstep0; subst; simpl.
	                split.
	                -- (* LockFreeAt preserved: h_c < h, so lock_write doesn't touch h_c *)
	                   assert (Pos.lt h_c h) as Hhc.
	                   { eapply Pos.le_lt_trans; [exact (Hybar t)|exact (H0 t)]. }
	                   simpl in *.
                   unfold lock_write.
                   destruct (Pos.leb h h_c) eqn:Hleb.
                   { apply Pos.leb_le in Hleb.
                     exfalso. eapply Pos.lt_irrefl.
	                     eapply Pos.le_lt_trans; eauto. }
	                   exact Hlock_hc.
	                -- split; [exact Heven|].
	                   split; [exact Hx|].
	                   split; [exact Hy|].
		                   split.
		                   ++ intro t0. unfold H_bar; simpl.
		                   unfold upd_tid_view.
	                   destruct (Pos.eqb_spec t t0) as [->|Hneq].
	                   { assert (Pos.lt h_c h) as Hhc.
                     { eapply Pos.le_lt_trans; [exact (Hybar t0)|exact (H0 t0)]. }
                     apply Pos.lt_le_incl in Hhc.
                     eapply Pos.le_trans; [exact Hhc|].
                     unfold view_bar, view_set; simpl.
	                     apply Pos.le_max_r. }
				                   { exact (Hybar t0). }
				                   ++ split.
                         ** apply (LockViewsAfterTail_acq s1 h_c h t own).
                            --- exact Hlk.
                            --- eapply Pos.le_lt_trans; [exact (Hybar t)|exact (H0 t)].
                         ** split.
	                            --- eapply LockHistoryBounded_acq.
	                                { exact Heven. }
	                                { exact Hbound. }
	                                { eapply Pos.le_lt_trans; [exact (Hybar t)|exact (H0 t)]. }
	                                { exact (Hlk t). }
	                                { exact H1. }
	                                { exact H4. }
	                            --- split.
                              { unfold SuccessfulReadWindowAfterTail.
		                       intros tr now2 hget2 hx2 hy2 htest2 Hgetx Hgety Hxlt Hylt Hfresh2 Hlockget2 Hlocktest2 Heven2.
		                       exfalso.
			                       eapply WriterHolding_read_window_contradiction
			                         with (σs := {|
			                           sl_mem := SeqLockUnderlaySpec.sl_mem s1;
		                           sl_lock := lock_write (sl_lock s1) h (own + 2) (own + 1);
		                           SeqLockUnderlaySpec.sl_view :=
		                             upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
		                               (view_set (SeqLockUnderlaySpec.sl_view s1 t) aloc_lk h);
			                           sl_owner := Some t |})
			                         (now := now2) (h_test := htest2).
				                       { simpl. unfold lock_write.
				                           assert (Pos.lt h htest2) as Hh_htest.
				                           { specialize (Hfresh2 t).
			                             unfold H_bar in Hfresh2; simpl in Hfresh2.
			                             unfold upd_tid_view in Hfresh2.
			                             rewrite Pos.eqb_refl in Hfresh2.
			                             eapply Pos.le_lt_trans; [|exact Hfresh2].
			                             unfold view_bar, view_set; simpl.
			                             apply Pos.le_max_r. }
			                           rewrite (proj2 (Pos.leb_le h htest2)).
				                           2:{ apply Pos.lt_le_incl. exact Hh_htest. }
				                           change (Nat.odd (own + 1) = true).
				                           rewrite Nat_odd_add_1_even. exact H4. }
					                       { exact Hlocktest2. }
					                       { exact Heven2. } }
                              { unfold ReadWindowConsistent.
		                       intros tr now2 hget2 hx2 hy2 htest2 Htailget2 Hgetx Hgety Hxlt Hylt Hfresh2 Hlockget2 Hlocktest2 Heven2.
		                       exfalso.
			                       eapply WriterHolding_read_window_contradiction
			                         with (σs := {|
			                           sl_mem := SeqLockUnderlaySpec.sl_mem s1;
		                           sl_lock := lock_write (sl_lock s1) h (own + 2) (own + 1);
		                           SeqLockUnderlaySpec.sl_view :=
		                             upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
		                               (view_set (SeqLockUnderlaySpec.sl_view s1 t) aloc_lk h);
			                           sl_owner := Some t |})
			                         (now := now2) (h_test := htest2).
				                       { simpl. unfold lock_write.
				                           assert (Pos.lt h htest2) as Hh_htest.
				                           { specialize (Hfresh2 t).
			                             unfold H_bar in Hfresh2; simpl in Hfresh2.
			                             unfold upd_tid_view in Hfresh2.
			                             rewrite Pos.eqb_refl in Hfresh2.
			                             eapply Pos.le_lt_trans; [|exact Hfresh2].
			                             unfold view_bar, view_set; simpl.
			                             apply Pos.le_max_r. }
			                           rewrite (proj2 (Pos.leb_le h htest2)).
				                           2:{ apply Pos.lt_le_incl. exact Hh_htest. }
				                           change (Nat.odd (own + 1) = true).
				                           rewrite Nat_odd_add_1_even. exact H4. }
					                       { exact Hlocktest2. }
					                       { exact Heven2. } }
	            + split.
              * exact Hlin.
	              * (* owner becomes Some t after acq_res *)
	                inversion Hstep; subst.
	                inversion Hstep0; subst; simpl.
	                split; [auto|].
	                intros h' Hle.
	                unfold lock_write.
	                unfold upd_tid_view in Hle. rewrite Pos.eqb_refl in Hle.
	                unfold view_set in Hle; simpl in Hle.
	                rewrite (proj2 (Pos.leb_le h h')) by exact Hle.
	                change (Nat.odd (own + 1) = true).
	                rewrite Nat_odd_add_1_even. exact H4.
          - unfold G.
            inversion Hstep; subst. inversion Hstep0; subst. cbn.
            repeat split.
		            + intros t' Hneq. unfold H_bar; cbn; unfold upd_tid_view.
		              destruct (Pos.eqb_spec t t'); [congruence | apply Pos.le_refl].
		            + intros t' Hneq l. cbn; unfold upd_tid_view.
		              destruct (Pos.eqb_spec t t'); [congruence | apply Pos.le_refl].
		            + cbn in *. congruence.
	            + congruence.
	            + congruence.
	            + congruence.
		            + intros t' Hneq h' Hle.
		              unfold lock_write.
		              match goal with
		              | [Hfr : forall t0, Pos.lt (H_bar _ t0) ?hh |- _] =>
		                destruct (Pos.leb hh h') eqn:Hleb; [|reflexivity];
		                exfalso; apply Pos.leb_le in Hleb;
		                eapply Pos.lt_irrefl;
		                eapply Pos.lt_le_trans; [|exact Hleb];
		                eapply Pos.le_lt_trans; [exact Hle|exact (Hfr t')]
		              end.
        }

        intros _.

        (* -- step 2: wrt loc_x vx' -- *)
        eapply provable_vis_safe with
          (P' := WriterHolding t vx' vy')
          (Q' := fun _ => WriterWroteX t vx' vy').
        { intros ? [? _]. unfold ANoError. intro Herr.
          destruct (σ s); inversion Herr; subst; inversion Herror. }
        { unfold WriterHolding. intros ? [? _]; tauto. }
        { intros _. unfold WriterWroteX. intros ? [? _]; unfold WriterHolding in H. tauto. }
        { apply WriterHoldingStable. }
        { intros _. apply WriterWroteXStable. }
        (* PUpdate inv: wrt inv is identity on state *)
        {
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          do 2 eexists. split; [apply rt_refl|]. split.
	          - destruct Hpre as [HI [Hlin [Howner_t Hbusy_t]]].
            inversion Hstep0; subst.
            unfold WriterHolding.
            split; [simpl; exact HI|].
            split; [simpl; exact Hlin|].
            simpl; split; [exact Howner_t|exact Hbusy_t].
	          - inversion Hstep0; subst.
		            unfold G. cbn. repeat split; intros; try reflexivity; try congruence.
        }
        (* PUpdate res: memory updated, I preserved since h_c < h_wx *)
        {
          intro ret.
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          exists ρ0, π0.
          split; [apply rt_refl|]. split.
          - unfold WriterHolding in Hpre.
	            destruct Hpre as [HI [Hlin [Howner_t Hbusy_t]]].
	            unfold I in HI.
		            destruct HI as [[ls Hρ] [h_c [n [Hlock_hc [Heven [Hx [Hy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
            unfold WriterWroteX; split.
            + (* WriterHolding in post-state *)
              unfold WriterHolding.
              inversion Hstep; subst.
              split.
              * (* I *)
                unfold I.
                split; [exists ls; exact Hρ|].
	                exists h_c, n.
                inversion Hstep0; subst; simpl.
                match goal with
                | [ Hlt : forall t0, Pos.lt (H_bar _ t0) ?hh |- _ ] =>
                  pose proof (Hlt t) as Hbar_lt
                end.
	                split; [exact Hlock_hc|].
                  split; [exact Heven|].
	                split.
                  -- (* sl_mem loc_x at h_c preserved: mem_write at h > h_c *)
	                   assert (Pos.lt h_c h) as Hhc.
	                   { eapply Pos.le_lt_trans; [exact (Hybar t)|exact Hbar_lt]. }
	                   unfold mem_write; simpl.
                   destruct (Pos.leb h h_c) eqn:Hleb.
                   { apply Pos.leb_le in Hleb.
                     exfalso. eapply Pos.lt_irrefl.
	                     eapply Pos.le_lt_trans; eauto. }
		                   exact Hx.
	                -- split.
                    ++ (* sl_mem loc_y at h_c preserved: different location *)
	                   unfold mem_write; simpl.
		                   exact Hy.
                    ++ split.
		                ** (* H_bar: view_set at aloc_x *)
	                   intro t0. unfold H_bar; simpl.
                   unfold upd_tid_view.
	                   destruct (Pos.eqb_spec t t0) as [->|Hneq].
	                   { assert (Pos.lt h_c h) as Hhc.
	                     { eapply Pos.le_lt_trans; [exact (Hybar t0)|exact Hbar_lt]. }
	                     apply Pos.lt_le_incl in Hhc.
	                     eapply Pos.le_trans; [exact Hhc|].
	                     unfold view_bar, view_set; simpl.
		                     eapply Pos.le_trans; [apply Pos.le_max_l|apply Pos.le_max_l]. }
			                   { exact (Hybar t0). }
		                    ** split.
			                       --- intro t0. exact (LockViewsAfterTail_wrt s1 h_c t loc_x h vx' Hlk t0).
			                       --- split.
                                { exact (LockHistoryBounded_wrt s1 h_c n t loc_x h vx' Hbound). }
                                split.
	                         { (* SuccessfulReadWindowAfterTail: writer still owns the busy tail. *)
                         unfold SuccessfulReadWindowAfterTail.
                         intros tr now hget hx0 hy0 htest Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven_now.
			                   exfalso.
			                   eapply WriterHolding_read_window_contradiction
			                     with (σs := {|
		                       sl_mem := mem_write (SeqLockUnderlaySpec.sl_mem s1) loc_x h vx';
		                       sl_lock := sl_lock s1;
		                       SeqLockUnderlaySpec.sl_view :=
			                         upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
			                           (view_set (SeqLockUnderlaySpec.sl_view s1 t) aloc_x h);
			                       sl_owner := sl_owner s1 |})
					                       (now := now) (h_test := htest).
				                   { apply Hbusy_t.
					                     apply Pos.lt_le_incl.
					                     eapply Pos.le_lt_trans; [|exact (Hfresh t)].
					                     unfold H_bar; simpl. unfold upd_tid_view.
					                     rewrite Pos.eqb_refl. unfold view_bar, view_set; simpl.
					                     apply Pos.le_max_r. }
					                   { exact Hlocktest. }
					                   { exact Heven_now. } }
                         { (* ReadWindowConsistent: writer still owns the busy tail. *)
                         unfold ReadWindowConsistent.
                         intros tr now hget hx0 hy0 htest Htailget Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven_now.
                         exfalso.
			                   eapply WriterHolding_read_window_contradiction
			                     with (σs := {|
		                       sl_mem := mem_write (SeqLockUnderlaySpec.sl_mem s1) loc_x h vx';
		                       sl_lock := sl_lock s1;
		                       SeqLockUnderlaySpec.sl_view :=
			                         upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
			                           (view_set (SeqLockUnderlaySpec.sl_view s1 t) aloc_x h);
			                       sl_owner := sl_owner s1 |})
				                       (now := now) (h_test := htest).
				                   { apply Hbusy_t.
				                     apply Pos.lt_le_incl.
				                     eapply Pos.le_lt_trans; [|exact (Hfresh t)].
				                     unfold H_bar; simpl. unfold upd_tid_view.
				                     rewrite Pos.eqb_refl. unfold view_bar, view_set; simpl.
				                     apply Pos.le_max_r. }
					                   { exact Hlocktest. }
					                   { exact Heven_now. } }
		              * split; [exact Hlin|].
	                inversion Hstep0; subst; simpl.
	                split; [exact Howner_t|].
	                intros h' Hle.
	                apply Hbusy_t.
	                unfold upd_tid_view in Hle. rewrite Pos.eqb_refl in Hle.
	                unfold view_set in Hle; simpl in Hle.
	                exact Hle.
            + (* sl_mem loc_x h = vx' for all h >= view(t, aloc_x) *)
              inversion Hstep; subst.
              inversion Hstep0; subst; simpl.
              match goal with
              | [ Hlt : forall t0, Pos.lt (H_bar _ t0) ?hh |- _ ] =>
                pose proof (Hlt t) as Hbar_lt; rename hh into hwx
              end.
              intros h' Hview.
              unfold mem_write; simpl.
              destruct (Pos.leb hwx h') eqn:Hleb.
              * reflexivity.
              * (* hwx > h' contradicts h' >= new_view(t, aloc_x) = hwx *)
                apply Pos.leb_nle in Hleb.
                exfalso. apply Hleb.
                unfold upd_tid_view in Hview.
                rewrite Pos.eqb_refl in Hview.
                unfold view_set in Hview; simpl in Hview.
                exact Hview.
	          - unfold G.
	            inversion Hstep; subst. inversion Hstep0; subst. cbn.
	            split; [intros t' Hneq; reflexivity|].
	            split; [intros t' Hneq; rewrite Hbar_upd_tid_view_neq by auto; apply Pos.le_refl|].
	            split; [intros t' Hneq l; cbn; unfold upd_tid_view;
	              destruct (Pos.eqb_spec t t'); [congruence | apply Pos.le_refl]|].
	            split; [intros owner0 Hown Hneq; rewrite H3 in Hown; inversion Hown; subst; congruence|].
	            split; [intros t' Hneq Hown; exact Hown|].
	            split.
	            + intros t' Hneq l h' Hle.
	              unfold mem_write.
	              destruct (andb (MemLoc_eqb loc_x l) (Pos.leb h h')) eqn:Hwrite;
	                [|reflexivity].
	              apply Bool.andb_true_iff in Hwrite as [_ Hleh'].
	              apply Pos.leb_le in Hleh'.
	              exfalso. eapply Pos.lt_irrefl.
	              eapply Pos.lt_le_trans; [|exact Hleh'].
	              eapply Pos.le_lt_trans; [exact Hle|exact (H6 t')].
	            + intros t' Hneq h' Hle; reflexivity.
        }

        intros _.

        (* -- step 3: wrt loc_y vy' -- *)
        eapply provable_vis_safe with
          (P' := WriterWroteX t vx' vy')
          (Q' := fun _ => WriterWroteXY t vx' vy').
        { intros ? [? _]. unfold ANoError. intro Herr.
          destruct (σ s); inversion Herr; subst; inversion Herror. }
        { unfold WriterWroteX. intros ? [? _]. unfold WriterHolding in H. tauto. }
        { intros _. unfold WriterWroteXY. intros ? [? _]. unfold WriterWroteX in H. destruct H as [[? _] _]; auto. }
        { apply WriterWroteXStable. }
        { intros _. apply WriterWroteXYStable. }
        (* PUpdate inv: wrt inv is identity on state *)
        {
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          do 2 eexists. split; [apply rt_refl|]. split.
          - destruct Hpre as [Hhold HmemX].
            inversion Hstep0; subst.
            unfold WriterWroteX.
            split; [simpl; exact Hhold|].
            simpl; exact HmemX.
	          - inversion Hstep0; subst.
	            unfold G. cbn. repeat split; intros; try reflexivity; try assumption.
        }
        (* PUpdate res: memory updated, I preserved since h_c < h_wy *)
        {
          intro ret.
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          exists ρ0, π0.
          split; [apply rt_refl|]. split.
          - destruct Hpre as [Hhold HmemX].
            unfold WriterHolding in Hhold.
            destruct Hhold as [HI [HAlin [Howner_t Hbusy_t]]].
	            unfold I in HI.
		            destruct HI as [[ols Hρ] [h_c [n [Hlock_hc [Heven [Hx [Hy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
            unfold WriterWroteXY; split.
            + (* WriterWroteX in post-state *)
              unfold WriterWroteX.
              inversion Hstep; subst.
              split.
              * (* WriterHolding *)
                split.
                { (* I *)
                  split.
                  { eexists. exact Hρ. }
	                  exists h_c, n.
                  inversion Hstep0; subst; simpl.
                  match goal with
                  | [ Hlt : forall t0, Pos.lt (H_bar _ t0) ?hh |- _ ] =>
                    pose proof (Hlt t) as Hbar_lt
                  end.
	                  split; [exact Hlock_hc|].
                    split; [exact Heven|].
	                  split.
                    -- (* sl_mem loc_x at h_c preserved: different location *)
	                     unfold mem_write; simpl.
	                     exact Hx.
	                  -- split.
                    ++ (* sl_mem loc_y at h_c preserved: mem_write at h > h_c *)
	                     assert (Pos.lt h_c h) as Hhc.
	                     { eapply Pos.le_lt_trans; [exact (Hybar t)|exact Hbar_lt]. }
                     unfold mem_write; simpl.
                     destruct (Pos.leb h h_c) eqn:Hleb.
                     { apply Pos.leb_le in Hleb.
                       exfalso. eapply Pos.lt_irrefl.
	                       eapply Pos.le_lt_trans; eauto. }
	                     exact Hy.
                    ++ split.
	                  ** (* H_bar: view_set at aloc_y *)
	                     intro t0. unfold H_bar; simpl.
                     unfold upd_tid_view.
	                     destruct (Pos.eqb_spec t t0) as [->|Hneq].
                     { assert (Pos.lt h_c h) as Hhc.
                       { eapply Pos.le_lt_trans; [exact (Hybar t0)|exact Hbar_lt]. }
                       apply Pos.lt_le_incl in Hhc.
                       eapply Pos.le_trans; [exact Hhc|].
	                       unfold view_bar, view_set; simpl.
		                       eapply Pos.le_trans; [apply Pos.le_max_r|apply Pos.le_max_l]. }
			                     { exact (Hybar t0). }
		                    ** split.
		                       --- intro t0. exact (LockViewsAfterTail_wrt s1 h_c t loc_y h vy' Hlk t0).
		                       --- split.
                              { exact (LockHistoryBounded_wrt s1 h_c n t loc_y h vy' Hbound). }
                              split.
                         { (* SuccessfulReadWindowAfterTail: writer still owns the busy tail. *)
                         unfold SuccessfulReadWindowAfterTail.
                         intros tr now hget hx0 hy0 htest Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven_now.
		                     exfalso.
		                     eapply WriterHolding_read_window_contradiction
	                       with (σs := {|
	                         sl_mem := mem_write (SeqLockUnderlaySpec.sl_mem s1) loc_y h vy';
	                         sl_lock := sl_lock s1;
	                         SeqLockUnderlaySpec.sl_view :=
		                           upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
		                             (view_set (SeqLockUnderlaySpec.sl_view s1 t) aloc_y h);
		                         sl_owner := sl_owner s1 |})
				                         (now := now) (h_test := htest).
			                     { apply Hbusy_t.
				                       apply Pos.lt_le_incl.
				                       eapply Pos.le_lt_trans; [|exact (Hfresh t)].
				                       unfold H_bar; simpl. unfold upd_tid_view.
				                       rewrite Pos.eqb_refl. unfold view_bar, view_set; simpl.
				                       apply Pos.le_max_r. }
				                     { exact Hlocktest. }
				                     { exact Heven_now. } }
                         { (* ReadWindowConsistent: writer still owns the busy tail. *)
                         unfold ReadWindowConsistent.
                         intros tr now hget hx0 hy0 htest Htailget Hgetx Hgety Hxlt Hylt Hfresh Hlockget Hlocktest Heven_now.
                         exfalso.
		                     eapply WriterHolding_read_window_contradiction
	                       with (σs := {|
	                         sl_mem := mem_write (SeqLockUnderlaySpec.sl_mem s1) loc_y h vy';
	                         sl_lock := sl_lock s1;
	                         SeqLockUnderlaySpec.sl_view :=
		                           upd_tid_view (SeqLockUnderlaySpec.sl_view s1) t
		                             (view_set (SeqLockUnderlaySpec.sl_view s1 t) aloc_y h);
		                         sl_owner := sl_owner s1 |})
				                         (now := now) (h_test := htest).
			                     { apply Hbusy_t.
				                       apply Pos.lt_le_incl.
				                       eapply Pos.le_lt_trans; [|exact (Hfresh t)].
				                       unfold H_bar; simpl. unfold upd_tid_view.
				                       rewrite Pos.eqb_refl. unfold view_bar, view_set; simpl.
				                       apply Pos.le_max_r. }
				                     { exact Hlocktest. }
				                     { exact Heven_now. } }
                }
                split; [exact HAlin|].
                inversion Hstep0; subst; simpl.
                split; [exact Howner_t|].
                intros h' Hle.
                apply Hbusy_t.
                unfold upd_tid_view in Hle. rewrite Pos.eqb_refl in Hle.
                unfold view_set in Hle; simpl in Hle.
                exact Hle.
              * (* mem_x fact preserved *)
                inversion Hstep0; subst; simpl.
                match goal with
                | [ Hlt : forall t0, Pos.lt (H_bar _ t0) ?hh |- _ ] =>
                  pose proof (Hlt t) as Hbar_lt; rename hh into hwy
                end.
                intros h' Hview.
                unfold mem_write; simpl.
                apply HmemX.
                unfold upd_tid_view in Hview.
                rewrite Pos.eqb_refl in Hview.
                unfold view_set in Hview; simpl in Hview.
                exact Hview.
            + (* mem_y fact *)
              inversion Hstep; subst.
              inversion Hstep0; subst; simpl.
              match goal with
              | [ Hlt : forall t0, Pos.lt (H_bar _ t0) ?hh |- _ ] =>
                pose proof (Hlt t) as Hbar_lt; rename hh into hwy
              end.
              intros h' Hview.
              unfold mem_write; simpl.
              destruct (Pos.leb hwy h') eqn:Hleb.
              * reflexivity.
              * apply Pos.leb_nle in Hleb.
                exfalso. apply Hleb.
                unfold upd_tid_view in Hview.
                rewrite Pos.eqb_refl in Hview.
                unfold view_set in Hview; simpl in Hview.
                exact Hview.
	          - unfold G.
	            inversion Hstep; subst. inversion Hstep0; subst. cbn.
	            split; [intros t' Hneq; reflexivity|].
	            split; [intros t' Hneq; rewrite Hbar_upd_tid_view_neq by auto; apply Pos.le_refl|].
	            split; [intros t' Hneq l; cbn; unfold upd_tid_view;
	              destruct (Pos.eqb_spec t t'); [congruence | apply Pos.le_refl]|].
	            split; [intros owner0 Hown Hneq; rewrite H3 in Hown; inversion Hown; subst; congruence|].
	            split; [intros t' Hneq Hown; exact Hown|].
	            split.
	            + intros t' Hneq l h' Hle.
	              unfold mem_write.
	              destruct (andb (MemLoc_eqb loc_y l) (Pos.leb h h')) eqn:Hwrite;
	                [|reflexivity].
	              apply Bool.andb_true_iff in Hwrite as [_ Hleh'].
	              apply Pos.leb_le in Hleh'.
	              exfalso. eapply Pos.lt_irrefl.
	              eapply Pos.lt_le_trans; [|exact Hleh'].
	              eapply Pos.le_lt_trans; [exact Hle|exact (H6 t')].
	            + intros t' Hneq h' Hle; reflexivity.
        }

        intros _.

        (* -- step 4: rel -- *)
        (* At release, linearize the overlay write:
           poss_steps: ps_inv(write vx' vy') · ps_ret(write vx' vy', tt)
           Overlay becomes (vx', vy'), which matches the newly-released memory. *)
        eapply provable_vis_safe with
          (P' := WriterWroteXY t vx' vy')
          (Q' := fun _ => I //\\ ALin t (Semantics.ls_linr (write vx' vy') tt)).
        { intros ? [? _]. unfold ANoError. intro Herr.
          destruct (σ s); inversion Herr; subst; inversion Herror. }
        { unfold WriterWroteXY, WriterWroteX, WriterHolding.
          intros ? [[[? _] _] _]; auto. }
        { intros _. solve_conj_impl. }
        { apply WriterWroteXYStable. }
        { intros _. apply ConjStable; eauto with slStableDB. }
        (* PUpdate inv: rel inv is identity *)
        {
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.
          inversion Hstep; subst.
          inversion Hstep0; subst s2.
          unfold WriterWroteXY, WriterWroteX, WriterHolding in Hpre.
          destruct Hpre as [[Hhold HmemX] HmemY].
          destruct Hhold as [HI [HAlin [Howner_t Hbusy_t]]].
          exists ρ0, π0. split; [apply rt_refl|]. split.
          - unfold WriterWroteXY, WriterWroteX, WriterHolding.
            split.
            + split.
              * split; [simpl; exact HI|].
                split; [simpl; exact HAlin|].
                simpl; split; [exact Howner_t|exact Hbusy_t].
              * simpl; exact HmemX.
            + simpl; exact HmemY.
	          - unfold G. cbn. repeat split; intros; try reflexivity; try assumption.
        }
        (* PUpdate res: the key linearization step for writer.
           At rel_res, we fire poss_steps (ps_inv + ps_ret) to linearize
           the overlay write(vx', vy').
           After lock_write at fresh h, the lock becomes free at h with
           (nxt, own+1) where nxt = own+1, Nat.even nxt = true.
           Memory has vx' at all timestamps >= view(t,aloc_x), vy' >= view(t,aloc_y).
           Since h > H_bar(t) >= view(t,l) for every l, the memory at h equals
           (vx', vy'), matching the new overlay state.
           I is restored with h_c := h. *)
        {
          intro ret.
          unfold PUpdate.
          intros σ0 ρ0 π0 Hpre σ' Hstep.

          (* Unpack WriterWroteXY *)
          unfold WriterWroteXY, WriterWroteX, WriterHolding in Hpre.
          destruct Hpre as [[Hhold HmemX] HmemY].
          destruct Hhold as [HI [HAlin [Howner_t Hbusy_t]]].
          unfold I in HI.
	          destruct HI as [[ols Hρ] [h_c_old [n_old [Hlock_old [Heven_old [Hx_old [Hy_old [Hybar_old [Hlk_old [Hbound_old [Hafter_old Hrwc_old]]]]]]]]]]].

          (* Invert the Step to get step_rel_res *)
          inversion Hstep; subst.
          (* normalize the (unit) return value so [Hstep0] becomes [ResEv _ tt] *)
          repeat match goal with
          | [ r : unit |- _ ] => destruct r
          end.
          inversion Hstep0; subst s2.

          (* --- Construct poss_steps: ps_inv then ps_ret --- *)
          (* ρ0 = Idle ols *)
          set (h_o := Pos.succ (SeqLock.sl_view ols t)).
          set (ols' := SeqLock.mkSL vx' vy' (SeqLock.upd_tid_time (SeqLock.sl_view ols) t h_o)).
          set (ρ' := (Idle ols' : State (li_lts F))).
          set (π1 := TMap.add t (Semantics.ls_lini (write vx' vy')) π0).
          set (π' := TMap.add t (Semantics.ls_linr (write vx' vy') tt) π1).

          exists ρ', π'.
          split.
          { (* poss_steps *)
            eapply rt_trans.
            - apply rt_step.
              (* ps_inv *)
              simpl in Hρ. rewrite Hρ.
              eapply Semantics.ps_inv with (t := t) (f := write vx' vy').
              + apply step_inv. apply step_write_inv.
              + exact HAlin.
            - apply rt_step.
              (* ps_ret *)
              eapply Semantics.ps_ret with (t := t) (f := write vx' vy') (ret := tt).
              + apply step_res.
                apply step_write_res with (h := h_o).
                * apply Pos.lt_succ_diag_r.
                * reflexivity.
              + subst π1. rewrite TMap.gss. reflexivity.
          }
          split.
          { (* I //\\ ALin t (ls_linr (write vx' vy') tt) *)
            split.
            - (* I *)
              unfold I. split.
              + exists ols'. reflexivity.
		              + exists h, (own + 1)%nat.
		                split.
		                * (* lock is free at h *)
		                  simpl. unfold lock_write. rewrite Pos.leb_refl.
		                  rewrite H3. reflexivity.
		                * split.
		                  { rewrite <- H3. exact H4. }
		                  split.
		                  { (* sl_vx = sl_mem loc_x h *)
	                  simpl.
	                  symmetry. apply HmemX.
	                  apply Pos.lt_le_incl.
	                  eapply Pos.le_lt_trans; [ | exact (H0 t) ].
	                  unfold H_bar, view_bar.
	                  eapply Pos.le_trans; [apply Pos.le_max_l|apply Pos.le_max_l].
		                  }
		                  split.
		                  { (* sl_vy = sl_mem loc_y h *)
	                  simpl.
	                  symmetry. apply HmemY.
	                  apply Pos.lt_le_incl.
	                  eapply Pos.le_lt_trans; [ | exact (H0 t) ].
	                  unfold H_bar, view_bar.
	                  eapply Pos.le_trans; [apply Pos.le_max_r|apply Pos.le_max_l].
		                  }
		                  split.
			                  { (* H_bar bound: h <= H_bar s2 t0 for all t0 *)
			                  intro t'. unfold H_bar; simpl.
			                  unfold view_bar, view_advance.
			                  eapply Pos.le_trans; [|apply Pos.le_max_r].
			                  apply Pos.le_max_r.
			                  }
                        assert (Hbound_new :
                          LockHistoryBounded
                            {|
                              sl_mem := sl_mem s1;
                              sl_lock := lock_write (sl_lock s1) h nxt (own + 1);
                              SeqLockUnderlaySpec.sl_view :=
                                fun t' : tid => view_advance (SeqLockUnderlaySpec.sl_view s1 t') h;
                              sl_owner := None
                            |} h nxt).
                        { eapply LockHistoryBounded_release; try exact Heven_old; try exact Hbound_old; eauto. }
			                        split.
                        { intro t'. rewrite <- H3. exact (LockViewsAfterTail_release s1 h nxt own t'). }
                        split.
                        { rewrite <- H3. rewrite <- H3 in Hbound_new. exact Hbound_new. }
                        split.
				                { apply SuccessfulReadWindowAfterTail_release.
                          rewrite <- H3. rewrite <- H3 in Hbound_new. exact Hbound_new. }
				                { (* ReadWindowConsistent after release. *)
                          apply ReadWindowConsistent_release.
                          - intros hx Hh_hx. simpl.
                            apply HmemX.
                            eapply Pos.le_trans; [|exact Hh_hx].
                            apply Pos.lt_le_incl.
                            eapply Pos.le_lt_trans; [|exact (H0 t)].
                            unfold H_bar, view_bar.
                            eapply Pos.le_trans; [apply Pos.le_max_l|apply Pos.le_max_l].
                          - intros hy Hh_hy. simpl.
                            apply HmemY.
                            eapply Pos.le_trans; [|exact Hh_hy].
                            apply Pos.lt_le_incl.
                            eapply Pos.le_lt_trans; [|exact (H0 t)].
                            unfold H_bar, view_bar.
                            eapply Pos.le_trans; [apply Pos.le_max_r|apply Pos.le_max_l].
                        }
	            - (* ALin *)
              unfold ALin. simpl. unfold π', π1.
              rewrite TMap.gss. reflexivity.
          }
	          { (* G *)
	            unfold G. cbn.
	            split.
	            - intros t' Hneq.
	              subst π' π1. simpl.
	              rewrite TMap.gso by auto.
	              rewrite TMap.gso by auto.
	              reflexivity.
	            - split.
	              + intros t' Hneq. unfold H_bar; cbn.
	                unfold view_bar, view_advance.
	                apply Pos.max_lub.
	                * eapply Pos.le_trans; [|apply Pos.le_max_l].
	                  apply Pos.max_lub.
	                  -- eapply Pos.le_trans; [apply Pos.le_max_l|].
	                     apply Pos.le_max_l.
	                  -- eapply Pos.le_trans; [apply Pos.le_max_l|].
	                     apply Pos.le_max_r.
	                * eapply Pos.le_trans; [apply Pos.le_max_l|].
	                  apply Pos.le_max_r.
	              + split.
	                * intros t' Hneq l. cbn.
	                  unfold view_advance. apply Pos.le_max_l.
	                * split.
	                  -- intros owner0 Hown Hneq.
	                     rewrite H5 in Hown. inversion Hown; subst. congruence.
	                  -- split.
	                     ++ intros t' Hneq Hown. discriminate.
	                     ++ split.
	                        ** intros t' Hneq l h' Hle. reflexivity.
	                        ** intros t' Hneq h' Hle.
	                           simpl. unfold lock_write.
	                           destruct (Pos.leb h h') eqn:Hleb; [|reflexivity].
	                           apply Pos.leb_le in Hleb.
	                           exfalso. eapply Pos.lt_irrefl.
	                           eapply Pos.lt_le_trans; [|exact Hleb].
	                           eapply Pos.le_lt_trans; [exact Hle|exact (H0 t')].
	          }
        }

        (* -- Ret tt -- *)
        intros _.
        eapply provable_ret_safe;
        try solve_conj_impl;
        try solve_conj_stable slStableDB.
        all: apply ImplRefl.
      }

      (* ================================================================ *)
      (* METHOD: read                                                      *)
      (* ================================================================ *)
      {
        (* pre/post conditions *)
        exists (I //\\ ALin t (Semantics.ls_inv read)).
        exists (fun ret => I //\\ ALin t (Semantics.ls_linr read ret)).
        constructor;
        try solve_conj_impl;
        try solve_conj_stable slStableDB;
        try apply IGinv; try apply IGret.
        { unfold ALin. intros. destruct H; auto. }

        simpl. unfold read_impl.
        eapply provable_seq.

        (* ---- do-while loop ---- *)
        {
          eapply provable_dowhile with
            (Iloop := ReaderLoop t)
            (Q := fun res : bool * (nat * nat) =>
              let '(busy, (vx, vy)) := res in
              if busy
              then ReaderLoop t
              else I //\\ ALin t (Semantics.ls_linr read (vx, vy)));
          try solve_conj_stable slStableDB.
          (* Hpost: Q res //\\ fst res = true ==>> Iloop *)
          {
            intros [[|] [vx vy]]; simpl.
            - (* busy = true *) intros ? [? ?]; auto.
            - (* busy = false: vacuous *) intros ? [? ?]. discriminate.
          }
          (* HQinv *)
          {
            intros [[|] [vx vy]]; simpl.
            - unfold ReaderLoop. intros ? [? _]; auto.
            - intros ? [? _]; auto.
          }
          (* HQstable *)
          {
            intros [[|] [vx vy]]; simpl.
            - apply ReaderLoopStable.
            - apply ConjStable; eauto with slStableDB.
          }

          (* ---- loop body: read_body ---- *)
          unfold read_body.

          (* step 1: get_ticket *)
          eapply provable_vis_safe with
            (P' := ReaderLoop t)
            (Q' := fun now => ReaderGotTicket t now).
          { intros ? [? _]. unfold ANoError. intro Herr.
            destruct (σ s); inversion Herr; subst; inversion Herror. }
          { unfold ReaderLoop. intros ? [? _]; auto. }
          { intros now0. unfold ReaderGotTicket. intros ? [? _]; auto. }
          { apply ReaderLoopStable. }
          { intros now0. apply ReaderGotTicketStable. }
          (* PUpdate inv *)
          {
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            inversion Hstep; subst.
            exists ρ0, π0.
            split; [apply rt_refl|].
            split.
            - destruct Hpre as [HI Hlin].
              inversion Hstep0; subst.
              unfold ReaderLoop.
              split; simpl; assumption.
	            - inversion Hstep0; subst.
	              unfold G. cbn. repeat split; intros; try reflexivity; try assumption.
          }
          (* PUpdate res *)
          {
            	intro now0.
	            unfold PUpdate.
	            intros σ0 ρ0 π0 Hpre σ' Hstep.
              inversion Hstep; subst.
	            dependent destruction H2.
	            exists ρ0, π0.
	            split; [apply rt_refl|].
	            split.
	            - destruct Hpre as [HI Hlin].
	            apply step_get_ticket_res_inv in Hstep0.
	              destruct Hstep0 as [h0 [nxt0 [Hfresh [Hlock ->]]]].
	              simpl in Hlock.
	              simpl.
              unfold ReaderGotTicket.
              split.
              + (* I preserved: only thread [t]'s view advances *)
                unfold I in *.
		                destruct HI as [[ls Hρ] [h_c [n [Hlock_hc [Heven [Hx [Hy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
                unfold I.
                split; [exists ls; exact Hρ|].
		                exists h_c, n.
		                split; [exact Hlock_hc|].
		                split; [exact Heven|].
		                split; [exact Hx|].
		                split; [exact Hy|].
		                split.
		                * intro t'.
	                  unfold H_bar; simpl.
	                  match goal with
	                  | [ |- context[upd_tid_view _ ?t_id _ t'] ] =>
                      unfold upd_tid_view;
                      destruct (Pos.eqb_spec t_id t') as [->|Hneq]
                  end.
                  -- (* t' is the updated thread: view_bar increases under view_advance *)
                     specialize (Hybar t') as Hybart.
                     eapply Pos.le_trans; [exact Hybart|].
                     unfold view_bar, view_advance.
                     (* old_bar <= new_bar *)
                     apply Pos.max_lub.
                     ++ (* max(vx,vy) <= new_bar *)
                        apply Pos.max_lub.
                        ** (* vx <= new_bar *)
                           eapply Pos.le_trans; [apply Pos.le_max_l|].
                           eapply Pos.le_trans; [apply Pos.le_max_l|].
                           apply Pos.le_max_l.
                        ** (* vy <= new_bar *)
                           eapply Pos.le_trans; [apply Pos.le_max_l|].
                           eapply Pos.le_trans; [apply Pos.le_max_r|].
                           apply Pos.le_max_l.
                     ++ (* vlk <= new_bar *)
	                        eapply Pos.le_trans; [apply Pos.le_max_l|].
	                        apply Pos.le_max_r.
	                  -- (* t0 <> t: other threads' views unchanged *)
	                    exact (Hybar t').
					                * split.
		                        -- apply LockViewsAfterTail_view_advance. exact Hlk.
		                        -- split.
	                          ++ apply LockHistoryBounded_view_advance. exact Hbound.
		                          ++ split.
                                ** apply SuccessfulReadWindowAfterTail_view_advance. exact Hafter.
                                ** apply ReadWindowConsistent_view_advance. exact Hrwc.
	              + split; [exact Hlin|].
		                exists h0. repeat split.
		                * unfold H_bar; simpl.
		                  unfold upd_tid_view. rewrite Pos.eqb_refl.
		                  unfold view_bar, view_advance.
		                  eapply Pos.le_trans; [|apply Pos.le_max_r].
		                  apply Pos.le_max_r.
		                * intro l. simpl.
		                  unfold upd_tid_view. rewrite Pos.eqb_refl.
		                  unfold view_advance. apply Pos.le_max_r.
		                * simpl. rewrite Hlock. reflexivity.
			            - apply step_get_ticket_res_inv in Hstep0.
			              destruct Hstep0 as [h0 [nxt0 [Hfresh [Hlock ->]]]].
			              eapply G_view_advance_current. reflexivity.
          }

          intros now.

          (* step 2: rd loc_x *)
          eapply provable_vis_safe with
            (P' := ReaderGotTicket t now)
            (Q' := fun vx => ReaderReadX t now vx).
          { intros ? [? _]. unfold ANoError. intro Herr.
            destruct (σ s); inversion Herr; subst; inversion Herror. }
          { unfold ReaderGotTicket. intros ? [? _]; auto. }
          { intros vx0. unfold ReaderReadX. intros ? [? _]; auto. }
          { apply ReaderGotTicketStable. }
          { intros vx0. apply ReaderReadXStable. }
          (* PUpdate inv *)
          {
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            inversion Hstep; subst.
            exists ρ0, π0.
            split; [apply rt_refl|].
            split.
	            - destruct Hpre as [HI [Hlin [h_get [Hle_hget [Hview_hget Hlock_hget]]]]].
	              inversion Hstep0; subst.
		              unfold ReaderGotTicket.
		              simpl.
		              split; [exact HI|].
		              split; [exact Hlin|].
		              exists h_get.
                repeat split; auto.
			            - inversion Hstep0; subst. apply G_same_state. reflexivity.
          }
          (* PUpdate res *)
          {
            intro vx0.
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            exists ρ0, π0.
            split; [apply rt_refl|].
            split.
	            - destruct Hpre as [HI [Hlin [h_get [Hle_hget [Hview_hget Hlock_hget]]]]].
              inversion Hstep; subst.
              apply step_rd_res_inv in Hstep0.
              destruct Hstep0 as [h [Hview_lt [Hmem_eq H3]]].
              subst; simpl.
              unfold ReaderReadX.
              split.
              + (* I preserved: rd only advances thread view *)
                unfold I in *.
	                destruct HI as [[ls Hρ] [h_c [n [Hlock_hc [Heven [Hvx [Hvy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
                split; [exists ls; exact Hρ|].
	                exists h_c, n.
	                split; [exact Hlock_hc|].
	                split; [exact Heven|].
	                split; [exact Hvx|].
	                split; [exact Hvy|].
	                split.
			                * apply Hbar_view_advance_all. exact Hybar.
				                * split.
		                      -- apply LockViewsAfterTail_view_advance. exact Hlk.
		                      -- split.
	                         ++ apply LockHistoryBounded_view_advance. exact Hbound.
		                         ++ split.
                              ** apply SuccessfulReadWindowAfterTail_view_advance. exact Hafter.
                              ** apply ReadWindowConsistent_view_advance. exact Hrwc.
              + (* ReaderReadX conjuncts: ALin, timestamps for h_get and hx *)
                simpl. split.
                * exact (ALin_transfer Hlin eq_refl).
                * exists h_get, h.
                  repeat split.
                  -- eapply Pos.le_trans; [exact Hle_hget|].
                     apply Hbar_view_advance_le.
		                  -- unfold H_bar; simpl.
		                     unfold upd_tid_view. rewrite Pos.eqb_refl.
		                     unfold view_bar, view_advance.
		                     eapply Pos.le_trans; [apply Pos.le_max_r|].
		                     eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_l.
		                  -- intro l.
		                     eapply Pos.le_trans; [exact (Hview_hget l)|].
		                     unfold upd_tid_view. rewrite Pos.eqb_refl.
		                     unfold view_advance. apply Pos.le_max_l.
		                  -- assert (Hhgx : Pos.le h_get (SeqLockUnderlaySpec.sl_view s1 t (mem_to_all loc_x))).
		                     { apply Hview_hget. }
		                     eapply Pos.le_trans; [exact Hhgx|].
		                     apply Pos.lt_le_incl. exact Hview_lt.
			                  -- apply Eqdep_dec.inj_pair2_eq_dec in H2; [exact H2 | repeat decide equality]. 
        - inversion Hstep; subst.
          apply step_rd_res_inv in Hstep0.
          destruct Hstep0 as [h [Hview_lt [Hmem_eq ->]]].
          eapply G_view_advance_current. reflexivity.
          }

          intros vx.

          (* step 3: rd loc_y *)
          eapply provable_vis_safe with
            (P' := ReaderReadX t now vx)
            (Q' := fun vy => ReaderSnapped t now vx vy).
          { intros ? [? _]. unfold ANoError. intro Herr.
            destruct (σ s); inversion Herr; subst; inversion Herror. }
          { unfold ReaderReadX. intros ? [? _]; auto. }
          { intros vy0. unfold ReaderSnapped. intros ? [? _]; auto. }
          { apply ReaderReadXStable. }
          { intros vy0. apply ReaderSnappedStable. }
          (* PUpdate inv *)
          {
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            inversion Hstep; subst.
            exists ρ0, π0.
            split; [apply rt_refl|].
            split.
		            - destruct Hpre as [HI [Hlin [h_get [hx [Hle_hget [Hle_hx [Hview_hget [Hget_le_hx [Hlock_hget Hmem_hx]]]]]]]]].
	              inversion Hstep0; subst.
	              unfold ReaderReadX.
	              simpl.
	              split; [exact HI|].
	              split; [exact Hlin|].
	              exists h_get, hx.
                repeat split; assumption.
		            - inversion Hstep0; subst. apply G_same_state. reflexivity.
          }
          (* PUpdate res *)
          {
            intro vy0.
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            exists ρ0, π0.
            split; [apply rt_refl|].
            split.
		            - destruct Hpre as [HI [Hlin [h_get [hx [Hle_hget [Hle_hx [Hview_hget [Hget_le_hx [Hlock_hget Hmem_hx]]]]]]]]].
	              pose proof Hmem_hx as Hmem_hx_keep.
              inversion Hstep; subst.
              apply step_rd_res_inv in Hstep0.
              destruct Hstep0 as [h [Hview_lt [Hmem_eq H3]]].
              subst; simpl.
              unfold ReaderSnapped.
              split.
              + (* I preserved: rd only advances thread view *)
                unfold I in *.
	                destruct HI as [[ls Hρ] [h_c [n [Hlock_hc [Heven [Hvx [Hvy [Hybar [Hlk [Hbound [Hafter Hrwc]]]]]]]]]]].
                split; [exists ls; exact Hρ|].
	                exists h_c, n.
	                split; [exact Hlock_hc|].
	                split; [exact Heven|].
	                split; [exact Hvx|].
	                split; [exact Hvy|].
	                split.
			                * apply Hbar_view_advance_all. exact Hybar.
				                * split.
		                      -- apply LockViewsAfterTail_view_advance. exact Hlk.
		                      -- split.
	                         ++ apply LockHistoryBounded_view_advance. exact Hbound.
		                         ++ split.
                              ** apply SuccessfulReadWindowAfterTail_view_advance. exact Hafter.
                              ** apply ReadWindowConsistent_view_advance. exact Hrwc.
              + (* ReaderSnapped conjuncts: ALin, timestamps for h_get, hx, and hy *)
                simpl. split.
                * exact (ALin_transfer Hlin eq_refl).
                * exists h_get, hx, h.
                  repeat split.
                  -- eapply Pos.le_trans; [exact Hle_hget|].
                     apply Hbar_view_advance_le.
                  -- eapply Pos.le_trans; [exact Hle_hx|].
                     apply Hbar_view_advance_le.
	                  -- unfold H_bar; simpl.
	                     unfold upd_tid_view. rewrite Pos.eqb_refl.
	                     unfold view_bar, view_advance.
	                     eapply Pos.le_trans; [apply Pos.le_max_r|].
	                     eapply Pos.le_trans; [apply Pos.le_max_l|]. apply Pos.le_max_l.
	                  -- exact Hget_le_hx.
	                  -- eapply Pos.le_trans; [apply Hview_hget|].
	                     apply Pos.lt_le_incl. exact Hview_lt.
		                  -- apply Eqdep_dec.inj_pair2_eq_dec in H2; [exact H2 | repeat decide equality].
        - inversion Hstep; subst.
          apply step_rd_res_inv in Hstep0.
          destruct Hstep0 as [h [Hview_lt [Hmem_eq ->]]].
          eapply G_view_advance_current. reflexivity.
          }

          intros vy.

          (* step 4: test_ticket now *)
          (* This is the critical step for the reader.
             When [busy = false]: test_ticket succeeds, meaning
               - lock(h_test) = (now, now) with [now] even
               - no acq fired in (h_get, h_test) => no rel in [h_get, h_test]
               - laststate constant on [h_get, h_test]
               - (vx, vy) = laststate = overlay values
             We linearize the read:
               poss_steps: ps_inv(read) · ps_ret(read, (vx,vy))
             When [busy = true]: loop continues. *)
          eapply provable_vis_safe with
            (P' := ReaderSnapped t now vx vy)
            (Q' := fun busy : bool =>
              if busy
              then ReaderLoop t
              else I //\\ ALin t (Semantics.ls_linr read (vx, vy))).
          { intros ? [? _]. unfold ANoError. intro Herr.
            destruct (σ s); inversion Herr; subst; inversion Herror. }
          { unfold ReaderSnapped. intros ? [? _]; auto. }
          { intros [|]; simpl.
            - unfold ReaderLoop. intros ? [? _]; auto.
            - intros ? [? _]; auto. }
          { apply ReaderSnappedStable. }
          { intros [|]; simpl.
            - apply ReaderLoopStable.
            - apply ConjStable; eauto with slStableDB. }
          (* PUpdate inv *)
          {
            unfold PUpdate.
            intros σ0 ρ0 π0 Hpre σ' Hstep.
            inversion Hstep; subst.
            exists ρ0, π0.
            split; [apply rt_refl|].
            split.
            - destruct Hpre as [HI Hlin].
              inversion Hstep0; subst.
              unfold ReaderSnapped.
              split; simpl; assumption.
		            - inversion Hstep0; subst. apply G_same_state. reflexivity.
          }
          (* PUpdate res: the key linearization step for reader.
             When busy = false (test_ticket succeeds):
               lock(h_test) = (now, now), now is even, k = now.
               => No acq in (h_get, h_test).
               => mem(x)(h_x) and mem(y)(h_y) equal laststate
                  because no release fires in [h_get, h_test].
               => By I, overlay (sl_vx, sl_vy) = laststate = (vx, vy).
               => Construct poss_steps:
                    ps_inv read · ps_ret read (vx, vy)
                  Overlay read returns (sl_vx, sl_vy) = (vx, vy). ✓
             When busy = true: no linearization, just maintain I. *)
          {
            intro busy0.
            destruct busy0.
            - exact (ReaderTestTicketPUpdateRes_busy_true t now vx vy).
            - exact (ReaderTestTicketPUpdateRes_busy_false t now vx vy).
          }

          (* After test_ticket, return (busy, (vx, vy)) *)
          intros busy.
          destruct busy.
          - (* busy = true: loop continues *)
            eapply provable_ret_safe; try apply ImplRefl.
            + unfold ReaderLoop. intros ? [? _]; auto.
            + apply ReaderLoopStable.
          - (* busy = false: exit loop *)
            eapply provable_ret_safe; try apply ImplRefl.
            + intros ? [? _]; auto.
            + apply ConjStable; eauto with slStableDB.
        }

        (* ---- after loop: Ret (snd res) ---- *)
        {
          intros [[|] [vx vy]]; simpl.
          - (* busy = true: contradicts loop exit condition *)
            eapply provable_ret_safe.
            + (* precondition is inconsistent: fst (true,_) = false *)
              intros ? [_ Hfalse]. discriminate.
            + (* postcondition implies I *)
              intros ? [? _]. exact H.
            + (* stability *)
              apply ConjStable; eauto with slStableDB.
          - (* busy = false: return (vx, vy) *)
            eapply provable_ret_safe;
            try solve_conj_impl;
            try solve_conj_stable slStableDB.
        }
      }
    }

    (* ---- Initial state satisfies I ---- *)
	    {
	      unfold I. simpl.
	      split.
	      - eexists; eauto.
	      - exists xH, 0%nat.
          simpl.
          split; [reflexivity|].
          split; [reflexivity|].
          split; [reflexivity|].
          split; [reflexivity|].
		          split.
		          + intro. apply Pos.le_refl.
		          + split.
		            * intro. apply Pos.le_refl.
                * split.
                  -- unfold LockHistoryBounded. split.
                     ++ intros h Hlt. exfalso.
                        apply (Pos.nlt_1_r h). exact Hlt.
                     ++ intros h Hle. left. reflexivity.
                  -- split.
		                 ++ unfold SuccessfulReadWindowAfterTail.
		                    intros. apply Pos.le_1_l.
		                 ++ unfold ReadWindowConsistent.
		                    intros. split; reflexivity.
	    }
  Qed.

End SeqLockImpl.
