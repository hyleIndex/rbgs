(** * WHWQInv: invariant, rely, guarantee, footprints and the side fields of
      the RLHL proof of the weak Herlihy–Wing queue

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P6.  The program is
    [WHWQProg.Mwhw]; the underlay presentation is the handle-linear
    [VE := EIhl δRC]; the overlay presentation is [VF := POQueueRD positive]
    (decision C7: [POQueueR] with abandoned dequeues).  This file states
    the invariant [Iq], the rely [Rq], the guarantee [Gq], the footprints
    [Oq] and the postcondition [Qq], proves the fields of [RLHL2Hyps] other
    than [h_sem], and the per-event maintenance and stability lemmas that
    the method derivations of [WHWQProof] (the enqueue) and [WHWQDeq]
    (the dequeue) use.  It proves no method derivation.

    ** Proof state

    [(((m, U), used), PossOk (POQReady st) P, γ)]: the memory [m]
    (location 0 the counter, location [S n] slot [n]), the pending
    underlay records [U], the used underlay keys, the partial-order queue
    state [st] (never [POQAtomic] between steps: a dequeue's [AInv] and
    [ARet] are taken in one [poss_steps]), the pool [P], the ghost [γ].

    ** The invariant [Iq] ([IqC])

    - bookkeeping: [iq_wf] (pool), [iq_age] ([GAge]), [iq_gwf] (every
      ghost entry is an invocation of its owner's thread), [iq_gnd] (no
      duplicate ghost entry), [iq_pwf] ([poq_wf], (W1)–(W8));
    - [iq_ctr]: the counter is the number of vertices;
    - [iq_cells] ([CellOK]): slot [n] is [0] when [n] is not a vertex,
      when its vertex is pending, or when it is garbage; it holds the
      value of its vertex when the vertex is complete and live;
    - [iq_coup] ([Coup]): an enqueue at [ls_inv] owns its [FAA]; an
      enqueue at [ls_lini] (after its [FAA], before its store) is the
      pending enqueue of its thread, with its value, and owns a store; a
      dequeue at [ls_inv] owns an [xchg];
    - [iq_pend], [iq_uniq]: every pending vertex belongs to an enqueue at
      [ls_lini] of its thread, and a thread has at most one;
    - [iq_ord] ([Ord]): once an enqueue has done its [FAA], the older calls
      of its thread own no pending invocation.  Every operation of the
      code is ordered before a younger [FAA] (the [FAA] releases,
      [rc_si_not_before_rel]), so this is the cross-call (F2) order; it
      gives the per-thread condition of [POQueueR] ([pending t = None]) at
      an enqueue's [FAA] ([no_pending_at_faa]).

    ** Linearization points (the derivations of [WHWQProof] and [WHWQDeq])

    - enqueue: the emission of its [FAA] takes [AInv] ([poq_start_enq],
      the new vertex is the slot the [FAA] returns); the emission of its
      store takes [ARet] ([poq_finish_enq]);
    - dequeue: the emission of an [xchg] whose record (the slot it swaps
      out, fixed by [EI] at the invocation) is non-zero takes [AInv] and
      [ARet] ([poq_mark_garbage] of that slot's vertex), whatever result
      the call committed; the emission of the last [xchg] of the call's
      ghost entries with a zero record takes [poqrd_dead] (decision C7).

    ** Rely and guarantee

    [Rq k]: memory moves by [EIhl δRC] steps; [k]'s pool entry and its
    pending invocations (as a list, [kg]) are kept ([KFrame]); the queue
    state only grows ([AMono]: more vertices with the same values, edges
    only out of new vertices, more garbage, more complete vertices); the
    pending vertex of a thread is kept while its owner stays at
    [ls_lini] ([PFreeze]).  [Gq k]: the same with [KFrame] for every other
    call.  [h_guar_rely] is immediate ([gq_rq]).

    ** Footprints and postconditions

    [Oq t (enq v)]: [[FAA; store i v]] for some [i], distinct handles.
    [Oq t deq]: invocations of [ld] or [xchg] of thread [t], distinct
    handles, the last one an [xchg] (a dequeue returns after an
    [xchg]).  [Qq k op r]: [k] is at [ls_linr op r].

    ** Scope (review gate 4, WHWQ-g4-3)

    - Over the handle-linear [EIhl δRC].  The underlay word is a run of
      the sequential register file, with effects at invocation.  Every
      weak behaviour comes from the module frontier: the semi-independence
      of [ERC], decisions D2′ and D3′ (review gate 3, WHWQ-g3-1).
    - The overlay presentation is [POQueueRD], which also accepts dead
      dequeues (decision C7).  A dead step occurs only on traces that are
      not complete ([POQueueRD.poqrd_complete_path]).  That no proof over
      the atomic [POQueueR] exists is argued in the task file (C7), not
      proved.
    - [I(enq, deq)] enters the proof in two places only.  One is the
      readiness of a dequeue's [AInv] ([deq_ready], through
      [emit_ready_mixed], which crosses an older enqueue of the thread at
      [ls_inv] by [I(enq, deq)]).  That use is a convenience: the older
      enqueue's [FAA] precedes the dequeue's [ld], at the same location,
      so no such enqueue is left.  The other is the soundness of the
      presentation ([POQueueRD.poqrd_sound], from
      [POQueueRSound.poqr_sound]).  The paper places it at the TInvoke
      step (Appendix/WHWQueue.tex:63, :148).

    No axiom is used: every result is closed under the global context
    ([Print Assumptions]; task log). *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia Relations.Relation_Operators.
Require Import Stdlib.FSets.FMapPositive.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import models.simlin.RelaxedHoareRun.
Require Import models.simlin.RelaxedHoareReady.
Require Import examples.Relaxed.WHWQ.WHWQSpec.
Require Import examples.Relaxed.WHWQ.POQueueR.
Require Import examples.Relaxed.WHWQ.POQueueRD.
Require Import examples.Relaxed.WHWQ.WHWQProg.

Import ListNotations.

Module WHWQInv.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareCompLinSpec.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.
  Import RelaxedHoareRun.
  Import RelaxedHoareReady.
  Import WHWQSpec.
  Import POQueueR.
  Import POQueueRD.
  Import WHWQProg.

  Local Abbreviation ES := ERC.
  Local Abbreviation FP := (FQ positive).
  Local Abbreviation VE := (EIhl (E := ERC) δRC).
  Local Abbreviation VF := (POQueueRD.POQueueRD positive).
  Local Abbreviation POk c P := (@PossOk FP VF c P).
  Local Abbreviation QSt := (@POQueueState positive).
  Local Abbreviation QOpP := (QOp positive).

  (** ** Part 1. Vocabulary *)

  Definition gop (e : ScheduledEvent ES FP) : RCOp := event_op (te_ev ES (se_event e)).

  Definition IE (t : tid) (h : nat) (o : RCOp) : ThreadEvent ES := Build_ThreadEvent t (@InvEv ES h o).

  Definition isFaa (o : RCOp) : Prop := o = op_faa.
  Definition isSt (o : RCOp) : Prop := exists s v, o = op_store s v.
  Definition isLd (o : RCOp) : Prop := o = op_ld.
  Definition isX (o : RCOp) : Prop := exists s, o = op_xchg s.
  Definition DeqOp (o : RCOp) : Prop := isLd o \/ isX o.

  (** [k] owns a pending invocation whose operation satisfies [Q]. *)
  Definition Owns (k : CallKey FP) (Q : RCOp -> Prop) (γ : Ghost ES FP) : Prop :=
    exists e, In e γ /\ se_owner e = k /\ Q (gop e).

  Definition key_eqb (k1 k2 : CallKey FP) : bool := Pos.eqb (fst k1) (fst k2) && Nat.eqb (snd k1) (snd k2).

  (** The pending invocations of [k], in ghost order (= queue order). *)
  Definition kg (k : CallKey FP) (γ : Ghost ES FP) : list (ThreadEvent ES) :=
    map (@se_event ES FP) (filter (fun e => key_eqb (se_owner e) k) γ).

  Definition ie_handle (ev : ThreadEvent ES) : nat := event_handle (te_ev ES ev).

  (** *** Footprints *)

  Definition EnqShape (t : tid) (v : positive) (evs : list (ThreadEvent ES)) : Prop :=
    exists h0 h1 i, h0 <> h1 /\ evs = [IE t h0 op_faa; IE t h1 (op_store i (Pos.to_nat v))].

  Definition DeqEv (t : tid) (ev : ThreadEvent ES) : Prop := exists h o, ev = IE t h o /\ DeqOp o.

  Definition DeqShape (t : tid) (evs : list (ThreadEvent ES)) : Prop :=
    NoDup (map ie_handle evs) /\ Forall (DeqEv t) evs /\ exists evs0 h s, evs = evs0 ++ [IE t h (op_xchg s)].

  Definition Oq (t : tid) (op : QOpP) (h : nat) (evs : list (ThreadEvent ES)) : Prop :=
    match op with
    | enq v => EnqShape t v evs
    | deq => DeqShape t evs
    end.

  (** *** The coupling of a call's phase with its pending invocations *)

  Definition Coup (k : CallKey FP) (ls : LinState FP) (st : QSt) (γ : Ghost ES FP) : Prop :=
    match ls with
    | ls_inv o =>
        match o with
        | enq _ => Owns k isFaa γ
        | deq => Owns k isX γ
        end
    | ls_lini o =>
        match o with
        | enq v => exists n, TMap.find (fst k) (poq_pending st) = Some n /\ poq_vertices st n = Some v /\ Owns k isSt γ
        | deq => True
        end
    | ls_linr _ _ => True
    end.

  (** *** The cells *)

  Definition CellOK (st : QSt) (m : Mem) (n : nat) : Prop :=
    (poq_next st <= n -> m (S n) = 0) /\
    (n < poq_next st ->
       (poq_pending_vertex st n /\ m (S n) = 0) \/
       (poq_garbage st n /\ m (S n) = 0) \/
       (poq_complete st n /\ ~ poq_garbage st n /\ exists v, poq_vertices st n = Some v /\ m (S n) = Pos.to_nat v)).

  (** *** The cross-call order *)

  (** [k] is an enqueue that has done its [FAA]. *)
  Definition EnqPast (k : CallKey FP) (P : LinPool FP) : Prop :=
    exists v, lin_lookup k (@ls_lini FP (enq v)) P \/ lin_lookup k (@ls_linr FP (enq v) tt) P.

  Definition Ord (P : LinPool FP) (γ : Ghost ES FP) : Prop :=
    forall k1 k2, fst k1 = fst k2 -> key_older (lin_domain P) k1 k2 -> EnqPast k2 P ->
      forall e, In e γ -> se_owner e <> k1.

  (** *** The scan of a dequeue (master's [scan_clause]) *)

  (** The dequeue read the counter [r] and found the slots below [i]
      empty: every live, complete vertex below [i] has only successors
      created after the read. *)
  Definition ScanC (st : QSt) (r i : nat) : Prop :=
    r <= poq_next st /\
    forall j, j < i -> poq_live st j -> poq_complete st j -> forall n, poq_edges st n j -> r <= n.

  (** ** Part 2. The invariant, the rely, the guarantee, the postcondition *)

  Record IqC (m : Mem) (st : QSt) (P : LinPool FP) (γ : Ghost ES FP) : Prop := {
    iq_wf : lin_pool_well_formed P;
    iq_age : GAge P γ;
    iq_gwf : Forall RelaxedHoareInherit.gwf γ;
    iq_gnd : NoDup γ;
    iq_pwf : poq_wf st;
    iq_ctr : m 0 = poq_next st;
    iq_cells : forall n, CellOK st m n;
    iq_coup : forall e, In e P -> Coup (lin_key e) (lin_state FP e) st γ;
    iq_pend : forall t n, TMap.find t (poq_pending st) = Some n ->
                exists h v, lin_lookup (t, h) (@ls_lini FP (enq v)) P;
    iq_uniq : forall t h1 h2 v1 v2, lin_lookup (t, h1) (@ls_lini FP (enq v1)) P ->
                lin_lookup (t, h2) (@ls_lini FP (enq v2)) P -> h1 = h2;
    iq_ord : Ord P γ
  }.

  Definition regs (s : PState VE VF) : Mem := fst (fst (ps_mem s)).

  Definition Iq : Assn VE VF := fun s =>
    exists st P, ps_poss s = POk (POQReady st) P /\ eihl_rec_used (E := ES) δRC (ps_mem s) /\
      IqC (regs s) st P (ps_ghost s).

  Definition AMono (st st' : QSt) : Prop :=
    poq_next st <= poq_next st' /\
    (forall n v, poq_vertices st n = Some v -> poq_vertices st' n = Some v) /\
    (forall n j, poq_edges st n j -> poq_edges st' n j) /\
    (forall n j, poq_edges st' n j -> poq_edges st n j \/ poq_next st <= n) /\
    (forall n, poq_garbage st n -> poq_garbage st' n) /\
    (forall n, poq_complete st n -> poq_complete st' n).

  Definition PFreeze (st : QSt) (P : LinPool FP) (st' : QSt) (P' : LinPool FP) : Prop :=
    forall t h v n, lin_lookup (t, h) (@ls_lini FP (enq v)) P -> lin_lookup (t, h) (@ls_lini FP (enq v)) P' ->
      TMap.find t (poq_pending st) = Some n -> TMap.find t (poq_pending st') = Some n.

  Definition KFrame (k : CallKey FP) (P : LinPool FP) (γ : Ghost ES FP) (P' : LinPool FP) (γ' : Ghost ES FP) : Prop :=
    (forall ls, lin_lookup k ls P -> lin_lookup k ls P') /\ kg k γ' = kg k γ.

  Definition Rq (k : CallKey FP) : PRel VE VF := fun s s' =>
    eihl_steps (E := ES) δRC (ps_mem s) (ps_mem s') /\
    exists st P st' P', ps_poss s = POk (POQReady st) P /\ ps_poss s' = POk (POQReady st') P' /\
      KFrame k P (ps_ghost s) P' (ps_ghost s') /\ AMono st st' /\ PFreeze st P st' P'.

  Definition Gq (k : CallKey FP) : PRel VE VF := fun s s' =>
    eihl_steps (E := ES) δRC (ps_mem s) (ps_mem s') /\
    exists st P st' P', ps_poss s = POk (POQReady st) P /\ ps_poss s' = POk (POQReady st') P' /\
      (forall k', k' <> k -> KFrame k' P (ps_ghost s) P' (ps_ghost s')) /\ AMono st st' /\ PFreeze st P st' P'.

  Definition Qq (k : CallKey FP) (op : QOpP) (r : q_ar positive op) : Assn VE VF := fun s =>
    exists st P, ps_poss s = POk (POQReady st) P /\ lin_lookup k (@ls_linr FP op r) P.

  (** ** Part 3. Basic facts *)

  (** *** Keys, entries, the pool *)

  Lemma callkey_eq_dec (k1 k2 : CallKey FP) : {k1 = k2} + {k1 <> k2}.
  Proof.
    destruct k1 as [t1 h1], k2 as [t2 h2].
    destruct (Pos.eq_dec t1 t2) as [-> | Ht]; [| right; congruence].
    destruct (Nat.eq_dec h1 h2) as [-> | Hh]; [left; reflexivity | right; congruence].
  Defined.

  Lemma key_eqb_spec k1 k2 : key_eqb k1 k2 = true <-> k1 = k2.
  Proof.
    destruct k1 as [t1 h1], k2 as [t2 h2]. unfold key_eqb. cbn [fst snd].
    rewrite andb_true_iff, Pos.eqb_eq, Nat.eqb_eq. split; [intros [-> ->]; reflexivity | intros E; injection E as -> ->; auto].
  Qed.

  Lemma key_eqb_false k1 k2 : k1 <> k2 -> key_eqb k1 k2 = false.
  Proof. intros Hne. destruct (key_eqb k1 k2) eqn:E; [exfalso; apply Hne; apply key_eqb_spec; exact E | reflexivity]. Qed.

  Lemma make_entry_inj k1 k2 (ls1 ls2 : LinState FP) :
    make_lin_entry k1 ls1 = make_lin_entry k2 ls2 -> k1 = k2 /\ ls1 = ls2.
  Proof.
    destruct k1 as [t1 h1], k2 as [t2 h2]. unfold make_lin_entry. cbn. intros E. injection E as -> -> ->. auto.
  Qed.

  Lemma lookup_in_dom k ls (P : LinPool FP) : lin_lookup k ls P -> In k (lin_domain P).
  Proof. intros H. unfold lin_domain. apply in_map_iff. exists (make_lin_entry k ls). split; [apply lin_key_make_lin_entry | exact H]. Qed.

  Lemma lookup_unique k ls1 ls2 (P : LinPool FP) :
    lin_pool_well_formed P -> lin_lookup k ls1 P -> lin_lookup k ls2 P -> ls1 = ls2.
  Proof. apply RelaxedHoareInherit.lookup_unique_gen. Qed.

  Lemma entry_eta (e : LinEntry FP) : e = make_lin_entry (lin_key e) (lin_state FP e).
  Proof. destruct e. reflexivity. Qed.

  Lemma entry_lookup (e : LinEntry FP) (P : LinPool FP) : In e P -> lin_lookup (lin_key e) (lin_state FP e) P.
  Proof. intros H. unfold lin_lookup. rewrite <- entry_eta. exact H. Qed.

  Lemma lin_update_incl k b a (P P' : LinPool FP) e :
    lin_update k b a P P' -> In e P' -> In e P \/ e = make_lin_entry k a.
  Proof.
    induction 1 as [tail | e0 pool pool' Hne Hu IH]; cbn.
    - intros [<- | He]; [right; reflexivity | left; right; exact He].
    - intros [<- | He]; [left; left; reflexivity |]. destruct (IH He) as [H | H]; [left; right; exact H | right; exact H].
  Qed.

  Lemma lin_update_back k b a (P P' : LinPool FP) k' ls :
    lin_update k b a P P' -> lin_lookup k' ls P' -> k' <> k -> lin_lookup k' ls P.
  Proof.
    intros Hu Hl Hne. destruct (lin_update_incl _ _ _ _ _ _ Hu Hl) as [H | H]; [exact H |].
    exfalso. apply Hne. exact (proj1 (make_entry_inj _ _ _ _ H)).
  Qed.

  Lemma lin_update_self k b a (P P' : LinPool FP) ls :
    lin_pool_well_formed P -> lin_update k b a P P' -> lin_lookup k ls P' -> ls = a.
  Proof.
    intros Hwf Hu Hl. apply (lookup_unique k ls a P' (lin_update_well_formed _ _ _ _ _ Hu Hwf) Hl).
    exact (lin_update_target _ _ _ _ _ Hu).
  Qed.

  Lemma lin_remove_incl k st (P P' : LinPool FP) : lin_remove k st P P' -> incl P' P.
  Proof.
    induction 1 as [tail | e pool pool' Hne Hr IH]; intros x Hx; [right; exact Hx |].
    destruct Hx as [<- | Hx]; [left; reflexivity | right; exact (IH x Hx)].
  Qed.

  Lemma key_older_total (ks : list (CallKey FP)) k1 k2 :
    In k1 ks -> In k2 ks -> k1 <> k2 -> key_older ks k1 k2 \/ key_older ks k2 k1.
  Proof.
    unfold key_older. induction ks as [| k ks IH]; intros H1 H2 Hne; [destruct H1 |].
    destruct H1 as [<- | H1], H2 as [<- | H2].
    - contradiction.
    - right. apply subseq_keep. exact (RelaxedHoareRun.subseq_single _ _ H2).
    - left. apply subseq_keep. exact (RelaxedHoareRun.subseq_single _ _ H1).
    - destruct (IH H1 H2 Hne) as [H | H]; [left | right]; apply subseq_skip; exact H.
  Qed.

  (** *** [kg]: the pending invocations of one call *)

  Lemma kg_app k (g1 g2 : Ghost ES FP) : kg k (g1 ++ g2) = kg k g1 ++ kg k g2.
  Proof. unfold kg. rewrite filter_app, map_app. reflexivity. Qed.

  Lemma kg_cons_own k (e : ScheduledEvent ES FP) g : se_owner e = k -> kg k (e :: g) = se_event e :: kg k g.
  Proof. intros Ho. unfold kg. cbn. rewrite Ho. assert (key_eqb k k = true) as -> by (apply key_eqb_spec; reflexivity). reflexivity. Qed.

  Lemma kg_cons_other k (e : ScheduledEvent ES FP) g : se_owner e <> k -> kg k (e :: g) = kg k g.
  Proof. intros Ho. unfold kg. cbn. rewrite (key_eqb_false _ _ Ho). reflexivity. Qed.

  Lemma kg_nil k : kg k [] = [].
  Proof. reflexivity. Qed.

  Lemma kg_in k (γ : Ghost ES FP) ev : In ev (kg k γ) <-> In (Build_ScheduledEvent k ev) γ.
  Proof.
    unfold kg. rewrite in_map_iff. split.
    - intros (e & <- & He). apply filter_In in He as [He Hk]. apply key_eqb_spec in Hk.
      destruct e as [o ev]. cbn in *. subst o. exact He.
    - intros He. exists (Build_ScheduledEvent k ev). split; [reflexivity |].
      apply filter_In. split; [exact He | apply key_eqb_spec; reflexivity].
  Qed.

  Lemma kg_in_owner k (γ : Ghost ES FP) e : In e γ -> se_owner e = k -> In (se_event e) (kg k γ).
  Proof. intros He Ho. apply kg_in. destruct e as [o ev]. cbn in *. subst o. exact He. Qed.

  Lemma kg_new k (evs : list (ThreadEvent ES)) : kg k (map (Build_ScheduledEvent k) evs) = evs.
  Proof.
    induction evs as [| ev evs IH]; [reflexivity |]. cbn [map]. rewrite kg_cons_own by reflexivity. cbn. rewrite IH. reflexivity.
  Qed.

  Lemma kg_new_other k k' (evs : list (ThreadEvent ES)) : k' <> k -> kg k (map (Build_ScheduledEvent k') evs) = [].
  Proof.
    intros Hne. induction evs as [| ev evs IH]; [reflexivity |]. cbn [map]. rewrite kg_cons_other by exact Hne. exact IH.
  Qed.

  Lemma kg_none k (γ : Ghost ES FP) : (forall e, In e γ -> se_owner e <> k) -> kg k γ = [].
  Proof.
    induction γ as [| e γ IH]; intros H; [reflexivity |].
    rewrite kg_cons_other by (apply H; left; reflexivity). apply IH. intros x Hx. apply H. right. exact Hx.
  Qed.

  Lemma kg_nil_noown k (γ : Ghost ES FP) : kg k γ = [] -> forall e, In e γ -> se_owner e <> k.
  Proof. intros H e He Ho. pose proof (kg_in_owner k γ e He Ho) as Hin. rewrite H in Hin. destruct Hin. Qed.

  Lemma kg_emit_other k (g1 g2 : Ghost ES FP) x : se_owner x <> k -> kg k (g1 ++ g2) = kg k (g1 ++ x :: g2).
  Proof. intros Hx. rewrite !kg_app. rewrite kg_cons_other by exact Hx. reflexivity. Qed.

  Lemma owns_kg k Q (γ : Ghost ES FP) : Owns k Q γ <-> exists ev, In ev (kg k γ) /\ Q (event_op (te_ev ES ev)).
  Proof.
    split.
    - intros (e & He & Ho & Hq). exists (se_event e). split; [exact (kg_in_owner _ _ _ He Ho) | exact Hq].
    - intros (ev & Hin & Hq). apply kg_in in Hin. exists (Build_ScheduledEvent k ev). auto.
  Qed.

  Lemma owns_kg_eq k Q (γ γ' : Ghost ES FP) : kg k γ' = kg k γ -> Owns k Q γ -> Owns k Q γ'.
  Proof. intros E H. apply owns_kg in H. apply owns_kg. rewrite E. exact H. Qed.

  Lemma owns_app_other k k0 Q (γ γn : Ghost ES FP) :
    (forall e, In e γn -> se_owner e = k0) -> k <> k0 -> (Owns k Q (γ ++ γn) <-> Owns k Q γ).
  Proof.
    intros Hown Hne. split.
    - intros (e & He & Ho & Hq). apply in_app_or in He as [He | He]; [exists e; auto |].
      exfalso. apply Hne. rewrite <- Ho. exact (Hown e He).
    - intros (e & He & Ho & Hq). exists e. split; [apply in_or_app; left; exact He | auto].
  Qed.

  Lemma owns_dec k Q (γ : Ghost ES FP) : (forall o, {Q o} + {~ Q o}) -> {Owns k Q γ} + {~ Owns k Q γ}.
  Proof.
    intros HQ. induction γ as [| e γ IH].
    - right. intros (e & [] & _).
    - destruct (callkey_eq_dec (se_owner e) k) as [Ho | Ho]; [destruct (HQ (gop e)) as [Hq | Hq] |].
      + left. exists e. split; [left; reflexivity | auto].
      + destruct IH as [IH | IH]; [left; destruct IH as (x & Hx & Hxo & Hxq); exists x; split; [right; exact Hx | auto] |].
        right. intros (x & [<- | Hx] & Hxo & Hxq); [exact (Hq Hxq) | apply IH; exists x; auto].
      + destruct IH as [IH | IH]; [left; destruct IH as (x & Hx & Hxo & Hxq); exists x; split; [right; exact Hx | auto] |].
        right. intros (x & [<- | Hx] & Hxo & Hxq); [exact (Ho Hxo) | apply IH; exists x; auto].
  Qed.

  Lemma isX_dec o : {isX o} + {~ isX o}.
  Proof.
    destruct o as [l mr | l v mw | l n mr mw | l v mr mw | l e n mr mw];
      try (right; intros (s & E); discriminate E).
    destruct l as [| s]; [right; intros (s & E); discriminate E |].
    destruct v as [| v]; [| right; intros (s' & E); discriminate E].
    destruct mr; [right; intros (s' & E); discriminate E |].
    destruct mw; [left; exists s; reflexivity | right; intros (s' & E); discriminate E].
  Defined.

  (** *** Blocking: which own events an older pending invocation orders *)

  (** Every operation is ordered before a younger [FAA] or store of its
      thread (both release). *)
  Lemma blocks_faa (e : ScheduledEvent ES FP) t hu :
    RelaxedHoareInherit.gwf e -> fst (se_owner e) = t -> inv_blocks (se_event e) (IE t hu op_faa).
  Proof.
    intros (Ht & Hi) Ho. destruct e as [o [t' ev]]. cbn in *. unfold is_invocation in Hi. cbn in Hi.
    split; [cbn; congruence |]. cbn. destruct ev as [h op | h op r]; [| contradiction].
    exact (proj1 (rc_si_not_before_rel op)).
  Qed.

  Lemma blocks_store (e : ScheduledEvent ES FP) t hu s w :
    RelaxedHoareInherit.gwf e -> fst (se_owner e) = t -> inv_blocks (se_event e) (IE t hu (op_store s w)).
  Proof.
    intros (Ht & Hi) Ho. destruct e as [o [t' ev]]. cbn in *. unfold is_invocation in Hi. cbn in Hi.
    split; [cbn; congruence |]. cbn. destruct ev as [h op | h op r]; [| contradiction].
    exact (proj2 (rc_si_not_before_rel op) s w).
  Qed.

  (** An acquire ([ld], [xchg]) is ordered before every younger operation of
      its thread. *)
  Lemma deq_blocks (e : ScheduledEvent ES FP) t hu o :
    RelaxedHoareInherit.gwf e -> fst (se_owner e) = t -> DeqOp (gop e) -> inv_blocks (se_event e) (IE t hu o).
  Proof.
    intros (Ht & Hi) Ho Hd. destruct e as [ow [t' ev]]. cbn in *. unfold is_invocation in Hi. cbn in Hi.
    split; [cbn; congruence |]. cbn. destruct ev as [h op | h op r]; [| contradiction].
    unfold gop in Hd. cbn in Hd. destruct Hd as [-> | (s & ->)].
    - exact (proj1 (rc_si_not_after_acq o)).
    - exact (proj2 (rc_si_not_after_acq o) s).
  Qed.

  (** The emitted invocation of [k] is the first of [k]'s pending
      invocations, provided that first one would order it. *)
  Lemma kg_head k (γ γ' : Ghost ES FP) y l ev :
    NoDup γ -> kg k γ = y :: l -> ghost_emit k ev γ γ' -> is_invocation ev -> (y = ev \/ inv_blocks y ev) ->
    ev = y /\ kg k γ' = l.
  Proof.
    intros Hnd Hk Hge Hinv Hyb. unfold ghost_emit in Hge. unfold is_invocation in Hinv.
    destruct (te_ev ES ev) as [h0 o0 | h0 o0 r0] eqn:Ev; [| contradiction].
    destruct Hge as (g1 & g2 & -> & -> & Hnb).
    rewrite kg_app, kg_cons_own in Hk by reflexivity. cbn [se_event] in Hk. rewrite kg_app.
    destruct (kg k g1) as [| y1 l1] eqn:Hg1.
    - cbn in Hk. injection Hk as -> ->. split; reflexivity.
    - exfalso. cbn in Hk. injection Hk as -> Hl.
      assert (Hy1 : In (Build_ScheduledEvent k y) g1) by (apply kg_in; rewrite Hg1; left; reflexivity).
      destruct Hyb as [-> | Hb].
      + apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. left. exact Hy1.
      + rewrite Forall_forall in Hnb. exact (Hnb _ Hy1 Hb).
  Qed.

  (** *** Ghost bookkeeping *)

  Lemma gwf_emit (g1 g2 : Ghost ES FP) x :
    Forall RelaxedHoareInherit.gwf (g1 ++ x :: g2) -> Forall RelaxedHoareInherit.gwf (g1 ++ g2).
  Proof. intros H. apply Forall_app in H as [H1 H2]. apply Forall_app. split; [exact H1 | exact (Forall_inv_tail H2)]. Qed.

  Lemma nodup_emit (g1 g2 : Ghost ES FP) x : NoDup (g1 ++ x :: g2) -> NoDup (g1 ++ g2).
  Proof. apply NoDup_remove_1. Qed.

  Lemma incl_remove_mid (g1 g2 : Ghost ES FP) x : incl (g1 ++ g2) (g1 ++ x :: g2).
  Proof. intros y Hy. apply in_app_or in Hy as [Hy | Hy]; apply in_or_app; [left | right; right]; exact Hy. Qed.

  Lemma owns_emit_other k Q (g1 g2 : Ghost ES FP) x :
    se_owner x <> k -> Owns k Q (g1 ++ x :: g2) -> Owns k Q (g1 ++ g2).
  Proof.
    intros Hx (e & He & Ho & Hq). exists e. split; [| auto].
    apply in_app_or in He as [He | [<- | He]]; [apply in_or_app; left; exact He | contradiction | apply in_or_app; right; exact He].
  Qed.

  Lemma kg_emit_eq_other k k0 (g1 g2 : Ghost ES FP) x :
    se_owner x = k0 -> k <> k0 -> kg k (g1 ++ g2) = kg k (g1 ++ x :: g2).
  Proof. intros Hx Hne. apply kg_emit_other. rewrite Hx. intros E. apply Hne. symmetry. exact E. Qed.

  Lemma ghost_emit_shape k ev (γ γ' : Ghost ES FP) :
    ghost_emit k ev γ γ' -> is_invocation ev ->
    exists g1 g2, γ = g1 ++ Build_ScheduledEvent k ev :: g2 /\ γ' = g1 ++ g2 /\
      Forall (fun e => ~ inv_blocks (se_event e) ev) g1.
  Proof.
    unfold ghost_emit, is_invocation. destruct (te_ev ES ev); [exact (fun H _ => H) | intros _ []].
  Qed.

  (** An emission keeps the pending invocations of every other call. *)
  Lemma kg_ghost_emit_other k k' ev (γ γ' : Ghost ES FP) :
    ghost_emit k ev γ γ' -> k' <> k -> kg k' γ' = kg k' γ.
  Proof.
    unfold ghost_emit. destruct (te_ev ES ev).
    - intros (g1 & g2 & -> & -> & _) Hne. apply kg_emit_other. cbn. intros E. apply Hne. symmetry. exact E.
    - intros -> _. reflexivity.
  Qed.

  (** ** Part 4. The fields of [RLHL2Hyps] other than [h_sem] *)

  Lemma amono_refl st : AMono st st.
  Proof.
    split; [lia |]. split; [auto |]. split; [auto |]. split; [intros n j H; left; exact H |]. split; auto.
  Qed.

  Lemma pfreeze_same st (P P' : LinPool FP) : PFreeze st P st P'.
  Proof. intros t h v n _ _ H. exact H. Qed.

  (** [h_guar_rely]. *)
  Theorem gq_rq k k' s s' : k <> k' -> Gq k s s' -> Rq k' s s'.
  Proof.
    intros Hne (Hm & st & P & st' & P' & Hp & Hp' & Hfr & Hmono & Hpf).
    split; [exact Hm |]. exists st, P, st', P'. split; [exact Hp |]. split; [exact Hp' |].
    split; [apply Hfr; intros E; apply Hne; symmetry; exact E |]. split; [exact Hmono | exact Hpf].
  Qed.

  (** [h_invoke_rely]. *)
  Theorem invoke_rely k k' op tr ret s p' :
    k <> k' -> program_produces_tagged (fst k) (Mwhw op (fst k)) tr ret -> Iq s ->
    poss_invoke VF (fst k) (snd k) op (ps_poss s) p' ->
    Rq k' s (ps_mem s, p', ps_ghost s ++ ghost_new k tr).
  Proof.
    intros Hne _ (st & P & Hp & _ & HI) Hinv. destruct k as [t h].
    rewrite Hp in Hinv. destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hinv) as [-> Hfr].
    split; [apply rt_refl |]. exists st, P, st, (make_lin_entry (t, h) (ls_inv op) :: P).
    cbn [ps_poss ps_mem ps_ghost fst snd]. split; [exact Hp |]. split; [reflexivity |].
    split; [split |].
    - intros ls Hl. right. exact Hl.
    - rewrite kg_app. unfold ghost_new. rewrite kg_new_other by exact Hne. apply app_nil_r.
    - split; [apply amono_refl | apply pfreeze_same].
  Qed.

  (** [h_return_rely]. *)
  Theorem return_rely k k' op r s p2 :
    k <> k' -> Iq s -> poss_return VF (fst k) (snd k) op r (ps_poss s) p2 -> NoOwn k (ps_ghost s) ->
    Rq k' s (ps_mem s, p2, ps_ghost s).
  Proof.
    intros Hne (st & P & Hp & _ & HI) Hret _. destruct k as [t h].
    rewrite Hp in Hret. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hret) as (P2 & -> & Hrem).
    split; [apply rt_refl |]. exists st, P, st, P2.
    cbn [ps_poss ps_mem ps_ghost fst snd]. split; [exact Hp |]. split; [reflexivity |].
    split; [split; [| reflexivity] |].
    - intros ls Hl. apply (lin_remove_other_lookup _ _ _ _ _ _ Hrem); [intros E; apply Hne; symmetry; exact E | exact Hl].
    - split; [apply amono_refl | apply pfreeze_same].
  Qed.

  (** [h_ok]. *)
  Theorem iq_ok s : Iq s -> exists v pool, ps_poss s = POk v pool /\ lin_pool_well_formed pool.
  Proof. intros (st & P & Hp & _ & HI). exists (POQReady st), P. split; [exact Hp | exact (iq_wf _ _ _ _ HI)]. Qed.

  (** [h_init]. *)
  Theorem iq_init : Iq (((mem0, []), []), POk (POQReady empty_poqueue_state) [], []).
  Proof.
    exists empty_poqueue_state, []. split; [reflexivity |].
    split; [exact (eihl_rec_used_init (E := ES) δRC mem0) |].
    constructor; cbn [regs ps_mem ps_poss ps_ghost fst snd].
    - constructor.
    - apply gage_nil.
    - constructor.
    - constructor.
    - apply empty_poqueue_state_wf.
    - reflexivity.
    - intros n. split; [intros _; reflexivity | cbn; lia].
    - intros e [].
    - intros t n Hf. cbn in Hf. rewrite TMap.gempty in Hf. discriminate.
    - intros t h1 h2 v1 v2 [].
    - intros k1 k2 _ Ho. destruct (key_older_in _ _ _ Ho) as [[] _].
  Qed.

  (** *** [mp_PI]: the state right after an overlay invocation *)

  Lemma owns_app_r k Q (γ γn : Ghost ES FP) : Owns k Q γ -> Owns k Q (γ ++ γn).
  Proof. intros (e & He & Ho & Hq). exists e. split; [apply in_or_app; left; exact He | auto]. Qed.

  Lemma owns_new k Q (evs : list (ThreadEvent ES)) ev :
    In ev evs -> Q (event_op (te_ev ES ev)) -> Owns k Q (map (Build_ScheduledEvent k) evs).
  Proof. intros Hin Hq. exists (Build_ScheduledEvent k ev). split; [apply in_map; exact Hin | auto]. Qed.

  Lemma coup_app k ls st (γ γn : Ghost ES FP) : Coup k ls st γ -> Coup k ls st (γ ++ γn).
  Proof.
    destruct ls as [o | o | o r]; cbn; [destruct o as [v |] | destruct o as [v |] | exact (fun H => H)].
    - apply owns_app_r.
    - apply owns_app_r.
    - intros (n & Hn & Hv & Ho). exists n. split; [exact Hn |]. split; [exact Hv | exact (owns_app_r _ _ _ _ Ho)].
    - exact (fun H => H).
  Qed.

  Lemma nodup_app_disj {X : Type} (l1 l2 : list X) :
    NoDup l1 -> NoDup l2 -> (forall a, In a l1 -> ~ In a l2) -> NoDup (l1 ++ l2).
  Proof.
    induction l1 as [| a l1 IH]; intros H1 H2 Hd; [exact H2 |]. cbn. apply NoDup_cons_iff in H1 as [Ha H1].
    constructor.
    - intros Hin. apply in_app_or in Hin as [Hin | Hin]; [exact (Ha Hin) | exact (Hd a (or_introl eq_refl) Hin)].
    - apply IH; [exact H1 | exact H2 | intros b Hb; apply Hd; right; exact Hb].
  Qed.

  Lemma nodup_map_inj {X Y : Type} (f : X -> Y) (l : list X) :
    (forall a b, f a = f b -> a = b) -> NoDup l -> NoDup (map f l).
  Proof.
    intros Hf. induction 1 as [| a l Ha Hl IH]; cbn; constructor; [| exact IH].
    intros Hin. apply in_map_iff in Hin as (b & Hb & Hin). rewrite (Hf b a Hb) in Hin. exact (Ha Hin).
  Qed.

  Lemma oq_nodup t op h evs : Oq t op h evs -> NoDup evs.
  Proof.
    destruct op as [v |]; cbn.
    - intros (h0 & h1 & i & Hne & ->). constructor; [| constructor; [intros [] | constructor]].
      intros [E | []]. injection E as E. exact (Hne (eq_sym E)).
    - intros (Hnd & _ & _). exact (NoDup_map_inv ie_handle _ Hnd).
  Qed.

  Lemma lookup_cons_other k k' ls ls' (P : LinPool FP) :
    lin_lookup k' ls' (make_lin_entry k ls :: P) -> (k' = k /\ ls' = ls) \/ lin_lookup k' ls' P.
  Proof.
    intros [E | H]; [left | right; exact H].
    destruct (make_entry_inj _ _ _ _ E) as [-> ->]. auto.
  Qed.

  Lemma owns_app_r_alt (γ : Ghost ES FP) k Q (γn : Ghost ES FP) : Owns k Q γn -> Owns k Q (γ ++ γn).
  Proof. intros (e & He & Ho & Hq). exists e. split; [apply in_or_app; right; exact He | auto]. Qed.

  Theorem iq_postinvoke t h (op : QOpP) s : PostInvoke Iq (t, h) op (Oq t op h) s -> Iq s.
  Proof.
    intros (p0 & γ0 & evs & (st & P0 & Hp0 & Hru & HC) & Hinv & Hg & HΩ & Htid).
    cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, Hru, Hinv, HC. subst p0.
    destruct (RelaxedHoareInherit.pinv_inv_gen _ _ _ _ _ _ Hinv) as [Hp Hfr].
    set (k := (t, h)) in *. set (γn := map (Build_ScheduledEvent k) evs) in *.
    assert (Hown : forall e, In e γn -> se_owner e = k).
    { intros e He. apply in_map_iff in He as (ev & <- & _). reflexivity. }
    assert (Hdom : forall k', In k' (lin_domain P0) -> k' <> k) by (intros k' Hk E; subst k'; exact (Hfr Hk)).
    exists st, (make_lin_entry k (@ls_inv FP op) :: P0). split; [exact Hp |]. split; [exact Hru |].
    rewrite Hg. change (regs s) with (fst (fst (ps_mem s))). cbn [regs ps_mem fst snd] in HC.
    destruct HC as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
    assert (Hnot_lini : forall o, lin_lookup k (ls_lini o) (make_lin_entry k (@ls_inv FP op) :: P0) -> False).
    { intros o Hl. destruct (lookup_cons_other _ _ _ _ _ Hl) as [(_ & E) | Hl']; [discriminate E | exact (Hfr (lookup_in_dom _ _ _ Hl'))]. }
    assert (Hnot_linr : forall o r, lin_lookup k (@ls_linr FP o r) (make_lin_entry k (@ls_inv FP op) :: P0) -> False).
    { intros o r Hl. destruct (lookup_cons_other _ _ _ _ _ Hl) as [(_ & E) | Hl']; [discriminate E | exact (Hfr (lookup_in_dom _ _ _ Hl'))]. }
    constructor.
    - eapply lin_insert_well_formed; [constructor; exact Hfr | exact Hwf].
    - exact (gage_invoke k _ P0 γ0 γn Hfr Hown Hage).
    - apply Forall_app. split; [exact Hgwf |]. subst γn. apply Forall_map.
      eapply Forall_impl; [| exact Htid]. intros ev [Ht Hi]. split; [exact Ht | exact Hi].
    - apply nodup_app_disj; [exact Hgnd | |].
      + subst γn. apply nodup_map_inj; [intros a b E; injection E as E; exact E | exact (oq_nodup t op h evs HΩ)].
      + intros e He Hn. pose proof (Hown e Hn) as Ho. exact (Hfr (eq_ind _ (fun x => In x (lin_domain P0)) (proj1 Hage e He) _ Ho)).
    - exact Hpwf.
    - exact Hctr.
    - exact Hcells.
    - intros e [<- | He].
      + cbn [lin_state lin_key make_lin_entry]. change (lin_key (make_lin_entry k (@ls_inv FP op))) with k.
        cbn [Coup]. destruct op as [v |]; cbn in HΩ.
        * destruct HΩ as (h0 & h1 & i & _ & Hevs). apply (owns_app_r_alt γ0).
          apply (owns_new k _ evs (IE t h0 op_faa)); [rewrite Hevs; left; reflexivity | reflexivity].
        * destruct HΩ as (_ & _ & evs0 & hx & sx & Hevs). apply (owns_app_r_alt γ0).
          apply (owns_new k _ evs (IE t hx (op_xchg sx))); [rewrite Hevs; apply in_or_app; right; left; reflexivity | exists sx; reflexivity].
      + apply coup_app. exact (Hcoup e He).
    - intros t' n Hf. destruct (Hpend t' n Hf) as (h' & v & Hl). exists h', v. right. exact Hl.
    - intros t' h1 h2 v1 v2 H1 H2.
      destruct (lookup_cons_other _ _ _ _ _ H1) as [(_ & E) | H1']; [discriminate E |].
      destruct (lookup_cons_other _ _ _ _ _ H2) as [(_ & E) | H2']; [discriminate E |].
      exact (Huniq t' h1 h2 v1 v2 H1' H2').
    - intros k1 k2 Ht Ho Hpast e He. cbn [lin_domain map] in Ho. rewrite lin_key_make_lin_entry in Ho.
      destruct (key_older_cons _ _ _ _ Ho) as [(-> & Hk1) | Ho'].
      + exfalso. destruct Hpast as (v & [Hl | Hl]); [exact (Hnot_lini _ Hl) | exact (Hnot_linr _ _ Hl)].
      + destruct (key_older_in _ _ _ Ho') as [Hk1 Hk2].
        assert (Hpast' : EnqPast k2 P0).
        { destruct Hpast as (v & [Hl | Hl]); exists v; [left | right];
            (destruct (lookup_cons_other _ _ _ _ _ Hl) as [(E & _) | Hl']; [exfalso; exact (Hdom _ Hk2 E) | exact Hl']). }
        apply in_app_or in He as [He | He]; [exact (Hord k1 k2 Ht Ho' Hpast' e He) |].
        rewrite (Hown e He). intros E. exact (Hdom _ Hk1 (eq_sym E)).
  Qed.

  (** *** [mp_ret]: from [Qq] to [RetCond] *)

  Lemma iq_return σ c (P P2 : LinPool FP) (γ : Ghost ES FP) k op (r : Sig.ar op) :
    Iq (σ, POk c P, γ) -> lin_lookup k (@ls_linr FP op r) P -> lin_remove k (@ls_linr FP op r) P P2 -> NoOwn k γ ->
    Iq (σ, POk c P2, γ).
  Proof.
    intros (st & P' & Hp & Hru & HC) Hl Hrem Hno. cbn in Hp. injection Hp as -> <-.
    exists st, P2. split; [reflexivity |]. split; [exact Hru |]. cbn [regs ps_mem ps_ghost ps_poss fst snd] in HC |- *.
    destruct HC as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
    pose proof (lin_remove_incl _ _ _ _ Hrem) as Hincl.
    assert (Hk_lini : forall o, lin_lookup k (ls_lini o) P -> False).
    { intros o Hl'. pose proof (lookup_unique _ _ _ _ Hwf Hl Hl') as E. discriminate E. }
    constructor.
    - exact (lin_remove_well_formed _ _ _ _ Hrem Hwf).
    - exact (gage_lin_remove _ _ _ _ _ Hrem Hno Hage).
    - exact Hgwf.
    - exact Hgnd.
    - exact Hpwf.
    - exact Hctr.
    - exact Hcells.
    - intros e He. exact (Hcoup e (Hincl e He)).
    - intros t n Hf. destruct (Hpend t n Hf) as (h & v & Hl'). exists h, v.
      apply (lin_remove_other_lookup _ _ _ _ _ _ Hrem); [| exact Hl'].
      intros E. rewrite E in Hl'. exact (Hk_lini _ Hl').
    - intros t h1 h2 v1 v2 H1 H2. exact (Huniq t h1 h2 v1 v2 (Hincl _ H1) (Hincl _ H2)).
    - intros k1 k2 Ht Ho Hpast e He.
      apply (Hord k1 k2 Ht (key_older_mono _ _ _ _ (lin_remove_domain_subseq _ _ _ _ Hrem) Ho)); [| exact He].
      destruct Hpast as (v & [H | H]); exists v; [left | right]; exact (Hincl _ H).
  Qed.

  Theorem qq_ret t h (op : QOpP) r s :
    Qq (t, h) op r s -> Iq s -> NoOwn (t, h) (ps_ghost s) -> RetCond Iq Gq (t, h) op r s.
  Proof.
    destruct s as [[σ p] γ]. intros (st & P & Hp & Hl) HI Hno. cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst p.
    exists (POk (POQReady st) P). split; [apply rt_refl |].
    split; [exists (POQReady st), P; split; [reflexivity | exact Hl] |].
    split; [exact HI |]. split; [apply r_refl |].
    intros p2 Hret. destruct (RelaxedHoareInherit.pret_inv_gen _ _ _ _ _ _ _ Hret) as (P2 & -> & Hrem).
    exact (iq_return σ (POQReady st) P P2 γ (t, h) op r HI Hl Hrem Hno).
  Qed.

  (** *** Assembly *)

  (** Derivations of every method ([MethodProvable], with the footprint
      [Oq] and the postcondition [Qq]) give every field of [RLHL2Hyps]
      ([h_sem] through [RelaxedHoareSound.method_sound]). *)
  Theorem whw_rlhl2_of_provable :
    (forall t (op : QOpP), MethodProvable Iq Rq Gq Mwhw t op (fun h => Oq t op h) (fun h r => Qq (t, h) op r)) ->
    RLHL2Hyps (VE := VE) (VF := VF) Iq Rq Gq Mwhw ((mem0, []), []) poqr_init.
  Proof.
    intros Hmp. constructor.
    - intros t op. exact (method_sound Iq Rq Gq Mwhw t op _ _ (Hmp t op)).
    - intros k k' s s' Hne HG. exact (gq_rq k k' s s' Hne HG).
    - exact invoke_rely.
    - exact return_rely.
    - exact iq_ok.
    - exact iq_init.
  Qed.

  (** The method-level obligations [mp_PI] and [mp_ret] are [iq_postinvoke]
      and [qq_ret]: a derivation of the body suffices. *)
  Theorem whw_method_provable t (op : QOpP) :
    (forall h, RProvable Iq Rq Gq (t, h) (PostInvoke Iq (t, h) op (Oq t op h))
       (fun a Γ H => Close Iq Rq Gq (t, h) (PostInvoke Iq (t, h) op (Oq t op h)) (fun r => Qq (t, h) op r) a Γ H /\
                     Oq t op h (own_invs Γ))
       [] empty_store (Mwhw op t)) ->
    MethodProvable Iq Rq Gq Mwhw t op (fun h => Oq t op h) (fun h r => Qq (t, h) op r).
  Proof.
    intros Ht. constructor.
    - intros h s Hs. exact (iq_postinvoke t h op s Hs).
    - intros h r s Hq HI Hno. exact (qq_ret t h op r s Hq HI Hno).
    - exact Ht.
  Qed.

  (** ** Part 5. Underlay steps of [EIhl δRC] *)

  Lemma step_ie (σ σ' : State VE) t hu o :
    Step VE (IE t hu o) σ σ' ->
    ~ In (t, hu) (snd σ) /\ exists r m', δRC (fst (fst σ)) o r m' /\
      σ' = ((m', @RelaxedTraceLin.Build_Op ES (t, hu) o r :: snd (fst σ)), (t, hu) :: snd σ).
  Proof.
    destruct σ as [[m U] u], σ' as [[m' U'] u']. cbn. intros (Hnu & (r & st' & Hd & Heq) & Hu).
    injection Heq as -> ->. subst u'. split; [exact Hnu |]. exists r, st'. split; [exact Hd | reflexivity].
  Qed.

  Lemma step_res (σ σ' : State VE) t hu o (r : Sig.ar o) :
    Step VE (Build_ThreadEvent t (@ResEv ES hu o r)) σ σ' -> fst (fst σ') = fst (fst σ).
  Proof.
    destruct σ as [[m U] u], σ' as [[m' U'] u']. cbn. intros ((Q1 & Q2 & _ & Heq) & _). injection Heq as -> _. reflexivity.
  Qed.

  Lemma eihl_step1 ev (σ σ' : State VE) : Step VE ev σ σ' -> eihl_steps (E := ES) δRC σ σ'.
  Proof. intros H. apply rt_step. exists ev. exact H. Qed.

  (** The effect of each operation of the code on the memory, and its
      record. *)
  Lemma step_faa (σ σ' : State VE) t hu :
    Step VE (IE t hu op_faa) σ σ' ->
    fst (fst σ') = mem_upd (fst (fst σ)) 0 (fst (fst σ) 0 + 1) /\
    snd (fst σ') = @RelaxedTraceLin.Build_Op ES (t, hu) op_faa (fst (fst σ) 0) :: snd (fst σ).
  Proof. intros Hs. destruct (step_ie _ _ _ _ _ Hs) as (_ & r & m' & [-> ->] & ->). cbn. auto. Qed.

  Lemma step_store (σ σ' : State VE) t hu s w :
    Step VE (IE t hu (op_store s w)) σ σ' -> fst (fst σ') = mem_upd (fst (fst σ)) (S s) w.
  Proof. intros Hs. destruct (step_ie _ _ _ _ _ Hs) as (_ & r & m' & Hd & ->). exact Hd. Qed.

  Lemma step_ld (σ σ' : State VE) t hu :
    Step VE (IE t hu op_ld) σ σ' ->
    fst (fst σ') = fst (fst σ) /\
    snd (fst σ') = @RelaxedTraceLin.Build_Op ES (t, hu) op_ld (fst (fst σ) 0) :: snd (fst σ).
  Proof. intros Hs. destruct (step_ie _ _ _ _ _ Hs) as (_ & r & m' & [-> ->] & ->). cbn. auto. Qed.

  Lemma step_xchg (σ σ' : State VE) t hu s :
    Step VE (IE t hu (op_xchg s)) σ σ' ->
    fst (fst σ') = mem_upd (fst (fst σ)) (S s) 0 /\
    snd (fst σ') = @RelaxedTraceLin.Build_Op ES (t, hu) (op_xchg s) (fst (fst σ) (S s)) :: snd (fst σ).
  Proof. intros Hs. destruct (step_ie _ _ _ _ _ Hs) as (_ & r & m' & [-> ->] & ->). cbn. auto. Qed.

  (** The emission of an invocation leaves the call owning its new
      record. *)
  Lemma inv_mine (σ σ' : State VE) t hu o :
    eihl_rec_used (E := ES) δRC σ -> Step VE (IE t hu o) σ σ' ->
    exists r, eihl_mine (E := ES) δRC (t, hu) (@RelaxedTraceLin.Build_Op ES (t, hu) o r) σ' /\
      snd (fst σ') = @RelaxedTraceLin.Build_Op ES (t, hu) o r :: snd (fst σ).
  Proof.
    intros Hru Hs. destruct (eihl_mine_inv (E := ES) δRC t hu o σ σ' Hs Hru) as (r & st' & _ & Hσ' & Hm).
    exists r. split; [exact Hm | rewrite Hσ'; reflexivity].
  Qed.

  (** The value of a record of an operation with a [nat] result, read
      without dependent equality. *)
  Definition rec_nat (x : RelaxedTraceLin.Op ES) : nat :=
    match RelaxedTraceLin.op_op x as o return Sig.ar o -> nat with
    | RCRd _ _ => fun r => r
    | RCFaa _ _ _ _ => fun r => r
    | RCXchg _ _ _ _ => fun r => r
    | _ => fun _ => 0
    end (RelaxedTraceLin.op_ret x).

  Lemma faa_rec_inj key (a b : nat) :
    @RelaxedTraceLin.Build_Op ES key op_faa a = @RelaxedTraceLin.Build_Op ES key op_faa b -> a = b.
  Proof. intros E. exact (f_equal rec_nat E). Qed.

  Lemma ld_rec_inj key (a b : nat) :
    @RelaxedTraceLin.Build_Op ES key op_ld a = @RelaxedTraceLin.Build_Op ES key op_ld b -> a = b.
  Proof. intros E. exact (f_equal rec_nat E). Qed.

  Lemma xchg_rec_inj key s (a b : nat) :
    @RelaxedTraceLin.Build_Op ES key (op_xchg s) a = @RelaxedTraceLin.Build_Op ES key (op_xchg s) b -> a = b.
  Proof. intros E. exact (f_equal rec_nat E). Qed.

  (** ** Part 6. Maintenance of the invariant, event by event *)

  (** *** Generic pieces *)

  Lemma cellok_ext st (m m' : Mem) n : (forall j, m' (S j) = m (S j)) -> CellOK st m n -> CellOK st m' n.
  Proof. intros Hx [H1 H2]. split; [intros H; rewrite Hx; exact (H1 H) | intros H; rewrite !Hx; exact (H2 H)]. Qed.

  Lemma gq_intro k (σ σ' : State VE) st P st' P' (γ γ' : Ghost ES FP) :
    eihl_steps (E := ES) δRC σ σ' ->
    (forall k', k' <> k -> KFrame k' P γ P' γ') -> AMono st st' -> PFreeze st P st' P' ->
    Gq k (σ, POk (POQReady st) P, γ) (σ', POk (POQReady st') P', γ').
  Proof.
    intros Hm Hfr Hmono Hpf. split; [exact Hm |]. exists st, P, st', P'.
    split; [reflexivity |]. split; [reflexivity |]. split; [exact Hfr |]. split; [exact Hmono | exact Hpf].
  Qed.

  Lemma kframe_emit_other k k' (P : LinPool FP) ev (γ γ' : Ghost ES FP) :
    ghost_emit k ev γ γ' -> k' <> k -> KFrame k' P γ P γ'.
  Proof. intros Hge Hne. split; [auto | exact (kg_ghost_emit_other _ _ _ _ _ Hge Hne)]. Qed.

  (** Any response: nothing but the record changes. *)
  Theorem iq_response k t hu o (r : Sig.ar o) (σ σ' : State VE) p (γ : Ghost ES FP) :
    Iq (σ, p, γ) -> Step VE (Build_ThreadEvent t (@ResEv ES hu o r)) σ σ' ->
    Iq (σ', p, γ) /\ Gq k (σ, p, γ) (σ', p, γ).
  Proof.
    intros (st & P & Hp & Hru & HC) Hs. cbn [ps_poss ps_mem ps_ghost fst snd] in Hp, Hru, HC. subst p.
    pose proof (step_res _ _ _ _ _ _ Hs) as Hm.
    split.
    - exists st, P. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δRC _ _ _ Hs Hru) |].
      unfold regs. cbn [ps_mem fst]. rewrite Hm. exact HC.
    - apply gq_intro; [exact (eihl_step1 _ _ _ Hs) | intros k' _; split; auto | apply amono_refl | apply pfreeze_same].
  Qed.

  (** An emission of [k] that changes no queue state and leaves the
      memory pointwise unchanged, given [k]'s coupling afterwards. *)
  Lemma iqc_emit m st (P : LinPool FP) (g1 g2 : Ghost ES FP) x k :
    IqC m st P (g1 ++ x :: g2) -> se_owner x = k ->
    (forall ls, lin_lookup k ls P -> Coup k ls st (g1 ++ g2)) ->
    IqC m st P (g1 ++ g2).
  Proof.
    intros HC Hx Hck. destruct HC as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
    constructor; try assumption.
    - exact (gage_remove _ _ _ _ Hage).
    - exact (gwf_emit _ _ _ Hgwf).
    - exact (nodup_emit _ _ _ Hgnd).
    - intros e He. destruct (callkey_eq_dec (lin_key e) k) as [Ek | Ek].
      + rewrite Ek. apply Hck. rewrite <- Ek. exact (entry_lookup e P He).
      + pose proof (Hcoup e He) as Hc. destruct (lin_state FP e) as [o | o | o r]; cbn in Hc |- *;
          [destruct o as [v |] | destruct o as [v |] | exact Logic.I].
        * apply (owns_emit_other _ _ g1 g2 x); [rewrite Hx; intros E; exact (Ek (eq_sym E)) | exact Hc].
        * apply (owns_emit_other _ _ g1 g2 x); [rewrite Hx; intros E; exact (Ek (eq_sym E)) | exact Hc].
        * destruct Hc as (n & Hn & Hv & Ho). exists n. split; [exact Hn |]. split; [exact Hv |].
          apply (owns_emit_other _ _ g1 g2 x); [rewrite Hx; intros E; exact (Ek (eq_sym E)) | exact Ho].
        * exact Logic.I.
    - intros k1 k2 Ht Ho Hpast e He. exact (Hord k1 k2 Ht Ho Hpast e (incl_remove_mid _ _ _ e He)).
  Qed.

  Theorem iq_emit_plain k t hu o (σ σ' : State VE) st (P : LinPool FP) (γ γ' : Ghost ES FP) :
    Iq (σ, POk (POQReady st) P, γ) -> Step VE (IE t hu o) σ σ' ->
    (forall l, fst (fst σ') l = fst (fst σ) l) ->
    ghost_emit k (IE t hu o) γ γ' ->
    (forall ls, lin_lookup k ls P -> Coup k ls st γ') ->
    Iq (σ', POk (POQReady st) P, γ') /\ Gq k (σ, POk (POQReady st) P, γ) (σ', POk (POQReady st) P, γ').
  Proof.
    intros (st0 & P0 & Hp & Hru & HC) Hs Hm Hge Hck. cbn in Hp. injection Hp as <- <-.
    cbn [regs ps_mem ps_ghost fst] in HC.
    destruct (ghost_emit_shape _ _ _ _ Hge I) as (g1 & g2 & Hγ & Hγ' & _). subst γ γ'.
    split.
    - exists st, P. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δRC _ _ _ Hs Hru) |].
      cbn [regs ps_mem ps_ghost fst].
      pose proof (iqc_emit _ _ _ _ _ _ k HC eq_refl Hck) as HC'.
      destruct HC' as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
      constructor; try assumption.
      + unfold regs, ps_mem. cbn [fst]. rewrite Hm. exact Hctr.
      + intros n. apply (cellok_ext st (fst (fst σ))); [intros j; apply Hm | exact (Hcells n)].
    - apply gq_intro; [exact (eihl_step1 _ _ _ Hs) | | apply amono_refl | apply pfreeze_same].
      intros k' Hne. split; [auto |]. apply kg_emit_other. cbn. intros E. exact (Hne (eq_sym E)).
  Qed.

  (** *** Queue-state facts *)

  Lemma coup_of_lookup m st (P : LinPool FP) (γ : Ghost ES FP) k ls :
    IqC m st P γ -> lin_lookup k ls P -> Coup k ls st γ.
  Proof.
    intros HC Hl. pose proof (iq_coup _ _ _ _ HC _ Hl) as Hc.
    rewrite lin_key_make_lin_entry in Hc. destruct k. exact Hc.
  Qed.

  Lemma gwf_of_in m st (P : LinPool FP) (γ : Ghost ES FP) e :
    IqC m st P γ -> In e γ -> RelaxedHoareInherit.gwf e.
  Proof. intros HC He. pose proof (iq_gwf _ _ _ _ HC) as H. rewrite Forall_forall in H. exact (H e He). Qed.

  Lemma vertex_lt_next (st : QSt) n v : poq_wf st -> poq_vertices st n = Some v -> n < poq_next st.
  Proof. intros Hwf Hv. apply (poq_vertex_lt st n Hwf). unfold poq_is_vertex. rewrite Hv. discriminate. Qed.

  Lemma pending_lt_next (st : QSt) n : poq_wf st -> poq_pending_vertex st n -> n < poq_next st.
  Proof. intros Hwf Hp. exact (poq_vertex_lt st n Hwf (wf_pending_vertex st Hwf n Hp)). Qed.

  Lemma complete_lt_next (st : QSt) n : poq_wf st -> poq_complete st n -> n < poq_next st.
  Proof. intros Hwf [Hv _]. exact (poq_vertex_lt st n Hwf Hv). Qed.

  Lemma amono_start_enq t (v : positive) (st : QSt) :
    poq_wf st -> TMap.find t (poq_pending st) = None -> AMono st (poq_start_enq t v st).
  Proof.
    intros Hwf Hidle. split; [cbn; lia |]. split; [| split; [| split; [| split]]].
    - intros n w Hv. rewrite poq_start_enq_vertices; [exact Hv |]. pose proof (vertex_lt_next _ _ _ Hwf Hv). lia.
    - intros n j H. apply poq_start_enq_edges. left. exact H.
    - intros n j H. apply poq_start_enq_edges in H as [H | [-> _]]; [left; exact H | right; lia].
    - intros n H. exact H.
    - intros n H. assert (Hn : n <> poq_next st) by (pose proof (complete_lt_next _ _ Hwf H); lia).
      exact (proj2 (poq_start_enq_complete t v st n Hidle Hn) H).
  Qed.

  Lemma amono_finish_enq t (st : QSt) n :
    poq_wf st -> TMap.find t (poq_pending st) = Some n -> AMono st (poq_finish_enq t st).
  Proof.
    intros Hwf Hf. split; [cbn; lia |]. split; [| split; [| split; [| split]]].
    - intros j w Hv. exact Hv.
    - intros a j H. exact H.
    - intros a j H. left. exact H.
    - intros j H. exact H.
    - intros j H. apply (poq_finish_enq_complete t st n j Hwf Hf). left. exact H.
  Qed.

  Lemma amono_mark_garbage n (st : QSt) : AMono st (poq_mark_garbage n st).
  Proof.
    split; [cbn; lia |]. split; [| split; [| split; [| split]]].
    - intros j w Hv. exact Hv.
    - intros a j H. exact H.
    - intros a j H. left. exact H.
    - intros j H. right. exact H.
    - intros j H. apply poq_mark_garbage_complete. exact H.
  Qed.

  (** Before an enqueue's [FAA], its thread has no pending vertex: a
      pending vertex belongs to an enqueue at [ls_lini] of the thread,
      which owns a store; if that enqueue is older, the store precedes
      the [FAA] in the ghost and orders it; if it is younger, [Ord]
      leaves the emitting call no pending invocation. *)
  Theorem no_pending_at_faa m st (P : LinPool FP) (γ γ' : Ghost ES FP) t h v hu :
    IqC m st P γ -> lin_lookup (t, h) (@ls_inv FP (enq v)) P ->
    ghost_emit (t, h) (IE t hu op_faa) γ γ' ->
    TMap.find t (poq_pending st) = None.
  Proof.
    intros HC Hl Hge.
    destruct (TMap.find t (poq_pending st)) as [n |] eqn:Hf; [exfalso | reflexivity].
    destruct (iq_pend _ _ _ _ HC t n Hf) as (h' & v' & Hl').
    destruct (ghost_emit_shape _ _ _ _ Hge I) as (g1 & g2 & Hγ & _ & Hnb).
    assert (Hne : (t, h') <> (t, h)).
    { intros E. rewrite E in Hl'. pose proof (lookup_unique _ _ _ _ (iq_wf _ _ _ _ HC) Hl Hl') as E2. discriminate E2. }
    destruct (key_older_total (lin_domain P) (t, h') (t, h) (lookup_in_dom _ _ _ Hl') (lookup_in_dom _ _ _ Hl) Hne) as [Ho | Ho].
    - pose proof (coup_of_lookup _ _ _ _ _ _ HC Hl') as Hc. cbn in Hc. destruct Hc as (n0 & _ & _ & e & He & Hoe & _).
      assert (He1 : In e g1).
      { apply (gage_before P γ g1 g2 (Build_ScheduledEvent (t, h) (IE t hu op_faa)) e (iq_age _ _ _ _ HC) Hγ He).
        rewrite Hoe. exact Ho. }
      rewrite Forall_forall in Hnb. apply (Hnb e He1). apply blocks_faa; [exact (gwf_of_in _ _ _ _ _ HC He) | rewrite Hoe; reflexivity].
    - apply (iq_ord _ _ _ _ HC (t, h) (t, h') eq_refl Ho (ex_intro _ v' (or_introl Hl'))
               (Build_ScheduledEvent (t, h) (IE t hu op_faa))); [| reflexivity].
      rewrite Hγ. apply in_or_app. right. left. reflexivity.
  Qed.

  (** *** The enqueue's [FAA]: [AInv] *)

  Lemma vf_ie t h (v : positive) (st : QSt) :
    TMap.find t (poq_pending st) = None ->
    Step VF (Build_ThreadEvent t (@InvEv FP h (enq v))) (POQReady st) (POQReady (poq_start_enq t v st)).
  Proof. intros Hidle. left. cbn. exists st. split; [reflexivity |]. split; [exact Hidle | reflexivity]. Qed.

  Theorem iq_faa_lp t h v hu (σ σ' : State VE) st (P : LinPool FP) (γ γ' : Ghost ES FP) :
    Iq (σ, POk (POQReady st) P, γ) -> lin_lookup (t, h) (@ls_inv FP (enq v)) P ->
    Step VE (IE t hu op_faa) σ σ' -> ghost_emit (t, h) (IE t hu op_faa) γ γ' ->
    Owns (t, h) isSt γ' ->
    exists P',
      lin_invoke_update t h (enq v) P P' /\ lin_lookup (t, h) (@ls_lini FP (enq v)) P' /\
      poss_steps VF (POk (POQReady st) P) (POk (POQReady (poq_start_enq t v st)) P') /\
      Iq (σ', POk (POQReady (poq_start_enq t v st)) P', γ') /\
      Gq (t, h) (σ, POk (POQReady st) P, γ) (σ', POk (POQReady (poq_start_enq t v st)) P', γ') /\
      poq_next st = fst (fst σ) 0.
  Proof.
    intros HI Hl Hs Hge Hst.
    pose proof HI as (st0 & P0 & Hp & Hru & HC). cbn in Hp. injection Hp as <- <-.
    unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
    pose proof (no_pending_at_faa _ _ _ _ _ _ _ _ _ HC Hl Hge) as Hidle.
    destruct (ghost_emit_shape _ _ _ _ Hge I) as (g1 & g2 & Hγ & Hγ' & Hnb).
    destruct (emit_ready_block_older P γ g1 g2 t h (enq v) (IE t hu op_faa) (iq_wf _ _ _ _ HC) Hl (iq_age _ _ _ _ HC))
      as (P' & Hinv & Hwf'); [| exact Hγ | exact Hnb |].
    { intros k1 o1 Ht Ho Hl1. pose proof (coup_of_lookup _ _ _ _ _ _ HC Hl1) as Hc.
      assert (Hown : exists e, In e γ /\ se_owner e = k1) by (destruct o1 as [v1 |]; cbn in Hc; destruct Hc as (e & He & Hoe & _); eauto).
      destruct Hown as (e & He & Hoe). exists e. split; [exact He |]. split; [exact Hoe |].
      apply blocks_faa; [exact (gwf_of_in _ _ _ _ _ HC He) | rewrite Hoe; exact Ht]. }
    pose proof (lin_invoke_update_is_update _ _ _ _ _ Hinv) as Hu.
    assert (Hk' : lin_lookup (t, h) (@ls_lini FP (enq v)) P') by exact (lin_update_target _ _ _ _ _ Hu).
    destruct HC as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
    set (n := poq_next st). set (st' := poq_start_enq t v st).
    destruct (step_faa _ _ _ _ Hs) as [Hm' _].
    set (m := fst (fst σ)) in *.
    assert (Hmx : forall j, fst (fst σ') (S j) = m (S j)) by (intros j; rewrite Hm'; apply mem_upd_other; discriminate).
    assert (Hold_lini : forall t' h' v', (t', h') <> (t, h) -> lin_lookup (t', h') (@ls_lini FP (enq v')) P' ->
                          lin_lookup (t', h') (@ls_lini FP (enq v')) P).
    { intros t' h' v' Hne Hl'. exact (lin_update_back _ _ _ _ _ _ _ Hu Hl' Hne). }
    assert (Hlini_t : forall h' v', lin_lookup (t, h') (@ls_lini FP (enq v')) P -> False).
    { intros h' v' Hl'. pose proof (coup_of_lookup _ _ _ _ _ _ (Build_IqC _ _ _ _ Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord) Hl') as Hc.
      cbn in Hc. destruct Hc as (n0 & Hn0 & _). rewrite Hidle in Hn0. discriminate. }
    exists P'. split; [exact Hinv |]. split; [exact Hk' |]. split.
    { apply rt_step. exists (t, h). apply (psa_inv VF t h (enq v) (POQReady st) (POQReady st') P P' Hinv). exact (vf_ie t h v st Hidle). }
    split; [| split].
    - exists st', P'. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δRC _ _ _ Hs Hru) |].
      unfold regs, ps_mem, ps_ghost. cbn [fst snd]. rewrite Hγ'. constructor.
      + exact Hwf'.
      + apply (gage_lin_invoke_update _ _ _ _ _ _ Hinv). rewrite Hγ in Hage. exact (gage_remove _ _ _ _ Hage).
      + rewrite Hγ in Hgwf. exact (gwf_emit _ _ _ Hgwf).
      + rewrite Hγ in Hgnd. exact (nodup_emit _ _ _ Hgnd).
      + exact (poq_start_enq_wf t v st Hpwf Hidle).
      + rewrite Hm', mem_upd_same. unfold st'. cbn [poq_next poq_start_enq]. rewrite Hctr. lia.
      + intros j. unfold st'. apply (cellok_ext _ m); [exact Hmx |]. destruct (Hcells j) as [C1 C2]. split.
        * intros Hj. apply C1. cbn in Hj. fold n. lia.
        * intros Hj. cbn in Hj. fold n in Hj.
          destruct (Nat.eq_dec j n) as [-> | Hjn].
          -- left. split; [exact (poq_start_enq_new_pending t v st Hidle) | apply C1; unfold n; lia].
          -- assert (Hjlt : j < poq_next st) by (unfold n in *; lia).
             destruct (C2 Hjlt) as [(Hpv & Hz) | [(Hg & Hz) | (Hc & Hng & w & Hw & Hz)]].
             ++ left. split; [apply (poq_start_enq_pending_vertex t v st j Hidle); right; exact Hpv | exact Hz].
             ++ right. left. split; [exact Hg | exact Hz].
             ++ right. right. split; [apply (proj2 (poq_start_enq_complete t v st j Hidle Hjn)); exact Hc |].
                split; [exact Hng |]. exists w. split; [rewrite poq_start_enq_vertices by exact Hjn; exact Hw | exact Hz].
      + intros e He. unfold st'. destruct (callkey_eq_dec (lin_key e) (t, h)) as [Ek | Ek].
        * assert (Hes : lin_state FP e = @ls_lini FP (enq v)).
          { apply (lookup_unique (t, h) _ _ P' Hwf'); [rewrite <- Ek; exact (entry_lookup e P' He) | exact Hk']. }
          rewrite Ek, Hes. cbn. exists n. split; [cbn; apply TMap.gss |].
          split; [exact (poq_start_enq_vertex_new t v st) |]. rewrite <- Hγ'. exact Hst.
        * destruct (lin_update_incl _ _ _ _ _ _ Hu He) as [He0 | He0]; [| exfalso; apply Ek; rewrite He0; reflexivity].
          pose proof (Hcoup e He0) as Hc. rewrite Hγ in Hc.
          assert (Hx : se_owner (Build_ScheduledEvent (t, h) (IE t hu op_faa)) <> lin_key e) by (cbn; intros E; exact (Ek (eq_sym E))).
          destruct (lin_state FP e) as [o | o | o r]; cbn in Hc |- *; [destruct o as [v1 |] | destruct o as [v1 |] | exact Logic.I].
          -- exact (owns_emit_other _ _ _ _ _ Hx Hc).
          -- exact (owns_emit_other _ _ _ _ _ Hx Hc).
          -- destruct Hc as (n1 & Hn1 & Hv1 & Ho1). exists n1.
             assert (Ht1 : lin_tid FP e <> t) by (intros E; rewrite E in Hn1; rewrite Hidle in Hn1; discriminate).
             split; [cbn; rewrite TMap.gso by exact Ht1; exact Hn1 |].
             split; [| exact (owns_emit_other _ _ _ _ _ Hx Ho1)].
             rewrite vertex_update_other; [exact Hv1 |]. pose proof (vertex_lt_next _ _ _ Hpwf Hv1). lia.
          -- exact Logic.I.
      + intros t' n' Hf. unfold st' in Hf. cbn in Hf. destruct (Pos.eq_dec t' t) as [-> | Ht'].
        * exists h, v. exact Hk'.
        * rewrite TMap.gso in Hf by exact Ht'. destruct (Hpend t' n' Hf) as (h' & v' & Hl'). exists h', v'.
          apply (lin_update_other_lookup _ _ _ _ _ _ _ Hu); [intros E; injection E as E _; exact (Ht' E) | exact Hl'].
      + intros t' h1 h2 v1 v2 H1 H2.
        destruct (callkey_eq_dec (t', h1) (t, h)) as [E1 | E1]; destruct (callkey_eq_dec (t', h2) (t, h)) as [E2 | E2].
        * injection E1 as -> ->. injection E2 as ->. reflexivity.
        * injection E1 as -> ->. exfalso. exact (Hlini_t h2 v2 (Hold_lini _ _ _ E2 H2)).
        * injection E2 as -> ->. exfalso. exact (Hlini_t h1 v1 (Hold_lini _ _ _ E1 H1)).
        * exact (Huniq t' h1 h2 v1 v2 (Hold_lini _ _ _ E1 H1) (Hold_lini _ _ _ E2 H2)).
      + intros k1 k2 Ht Ho Hpast e He.
        rewrite <- (lin_invoke_update_keys _ _ _ _ _ Hinv) in Ho. rewrite <- Hγ' in He.
        assert (He0 : In e γ) by (rewrite Hγ; rewrite Hγ' in He; exact (incl_remove_mid _ _ _ e He)).
        destruct (callkey_eq_dec k2 (t, h)) as [-> | Ek2].
        * intros Hoe. assert (He1 : In e g1).
          { apply (gage_before P γ g1 g2 (Build_ScheduledEvent (t, h) (IE t hu op_faa)) e Hage Hγ He0). rewrite Hoe. exact Ho. }
          rewrite Forall_forall in Hnb. apply (Hnb e He1). apply blocks_faa; [exact (gwf_of_in _ _ _ _ _ (Build_IqC _ _ _ _ Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord) He0) |].
          rewrite Hoe. exact Ht.
        * apply (Hord k1 k2 Ht Ho); [| exact He0].
          destruct Hpast as (v2 & [H2 | H2]); exists v2; [left | right]; exact (lin_update_back _ _ _ _ _ _ _ Hu H2 Ek2).
    - apply gq_intro; [exact (eihl_step1 _ _ _ Hs) | | exact (amono_start_enq t v st Hpwf Hidle) |].
      + intros k' Hne. split; [intros ls Hl'; exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu Hne Hl') |].
        exact (kg_ghost_emit_other _ _ _ _ _ Hge Hne).
      + intros t' h' v' n' H1 H2 Hf. destruct (Pos.eq_dec t' t) as [-> | Ht'].
        * exfalso. rewrite Hidle in Hf. discriminate.
        * unfold st'. cbn. rewrite TMap.gso by exact Ht'. exact Hf.
    - unfold n. rewrite <- Hctr. reflexivity.
  Qed.

  (** *** The enqueue's store: [ARet] *)

  Lemma vf_re t h (v : positive) (st : QSt) n :
    TMap.find t (poq_pending st) = Some n ->
    Step VF (Build_ThreadEvent t (@ResEv FP h (enq v) tt)) (POQReady st) (POQReady (poq_finish_enq t st)).
  Proof. intros Hf. left. cbn. exists st, n. split; [reflexivity |]. split; [exact Hf | reflexivity]. Qed.

  Theorem iq_store_lp t h v hu n (σ σ' : State VE) st (P : LinPool FP) (γ γ' : Ghost ES FP) :
    Iq (σ, POk (POQReady st) P, γ) -> lin_lookup (t, h) (@ls_lini FP (enq v)) P ->
    TMap.find t (poq_pending st) = Some n ->
    Step VE (IE t hu (op_store n (Pos.to_nat v))) σ σ' ->
    ghost_emit (t, h) (IE t hu (op_store n (Pos.to_nat v))) γ γ' ->
    exists P',
      lin_update (t, h) (@ls_lini FP (enq v)) (@ls_linr FP (enq v) tt) P P' /\
      poss_steps VF (POk (POQReady st) P) (POk (POQReady (poq_finish_enq t st)) P') /\
      Iq (σ', POk (POQReady (poq_finish_enq t st)) P', γ') /\
      Gq (t, h) (σ, POk (POQReady st) P, γ) (σ', POk (POQReady (poq_finish_enq t st)) P', γ').
  Proof.
    intros HI Hl Hf Hs Hge.
    pose proof HI as (st0 & P0 & Hp & Hru & HC). cbn in Hp. injection Hp as <- <-.
    unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
    pose proof (coup_of_lookup _ _ _ _ _ _ HC Hl) as Hck. cbn in Hck. destruct Hck as (n0 & Hn0 & Hv0 & _).
    rewrite Hf in Hn0. injection Hn0 as <-.
    destruct (ghost_emit_shape _ _ _ _ Hge I) as (g1 & g2 & Hγ & Hγ' & Hnb).
    destruct HC as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
    destruct (RelaxedHoareInherit.lin_update_exists_gen (t, h) (@ls_lini FP (enq v)) (@ls_linr FP (enq v) tt) P Hwf Hl)
      as (P' & Hu).
    set (st' := poq_finish_enq t st).
    pose proof (step_store _ _ _ _ _ _ Hs) as Hm'. set (m := fst (fst σ)) in *.
    assert (Hnlt : n < poq_next st) by (apply (pending_lt_next _ _ Hpwf); exists t; exact Hf).
    assert (Hnot_lini : forall ls, lin_lookup (t, h) ls P' -> ls = @ls_linr FP (enq v) tt)
      by (intros ls Hl'; exact (lin_update_self _ _ _ _ _ _ Hwf Hu Hl')).
    assert (Hlini_back : forall t' h' v', lin_lookup (t', h') (@ls_lini FP (enq v')) P' -> lin_lookup (t', h') (@ls_lini FP (enq v')) P).
    { intros t' h' v' Hl'. apply (lin_update_back _ _ _ _ _ _ _ Hu Hl'). intros E. rewrite E in Hl'.
      pose proof (Hnot_lini _ Hl') as E2. discriminate E2. }
    assert (Hlini_other_t : forall t' h' v', lin_lookup (t', h') (@ls_lini FP (enq v')) P -> (t', h') <> (t, h) -> t' <> t).
    { intros t' h' v' Hl' Hne Ht. subst t'. apply Hne. rewrite (Huniq t h' h v' v Hl' Hl). reflexivity. }
    exists P'. split; [exact Hu |]. split.
    { apply rt_step. exists (t, h). apply (psa_ret VF t h (enq v) tt (POQReady st) (POQReady st') P P' Hu). exact (vf_re t h v st n Hf). }
    split.
    - exists st', P'. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δRC _ _ _ Hs Hru) |].
      unfold regs, ps_mem, ps_ghost. cbn [fst snd]. rewrite Hγ'. constructor.
      + exact (lin_update_well_formed _ _ _ _ _ Hu Hwf).
      + apply (gage_lin_update _ _ _ _ _ _ Hu). rewrite Hγ in Hage. exact (gage_remove _ _ _ _ Hage).
      + rewrite Hγ in Hgwf. exact (gwf_emit _ _ _ Hgwf).
      + rewrite Hγ in Hgnd. exact (nodup_emit _ _ _ Hgnd).
      + exact (poq_finish_enq_wf t st Hpwf).
      + rewrite Hm'. rewrite mem_upd_other by discriminate. exact Hctr.
      + intros j. unfold st', CellOK. rewrite Hm'. destruct (Nat.eq_dec j n) as [-> | Hjn].
        * split; [cbn; lia |]. intros _. right. right.
          split; [apply (poq_finish_enq_complete t st n n Hpwf Hf); right; reflexivity |].
          split; [cbn; intros Hg; exact (wf_pending_not_garbage st Hpwf n (ex_intro _ t Hf) Hg) |].
          exists v. split; [exact Hv0 | apply mem_upd_same].
        * rewrite mem_upd_other by (intros E; injection E as E; exact (Hjn (eq_sym E))).
          destruct (Hcells j) as [C1 C2]. split; [exact C1 |]. intros Hj. destruct (C2 Hj) as [(Hpv & Hz) | [(Hg & Hz) | (Hc & Hng & w & Hw & Hz)]].
          -- left. split; [apply (poq_finish_enq_pending_vertex_iff t st n j Hpwf Hf); split; [exact Hpv | exact Hjn] | exact Hz].
          -- right. left. split; [exact Hg | exact Hz].
          -- right. right. split; [apply (poq_finish_enq_complete t st n j Hpwf Hf); left; exact Hc |].
             split; [exact Hng |]. exists w. auto.
      + intros e He. destruct (callkey_eq_dec (lin_key e) (t, h)) as [Ek | Ek].
        * assert (Hes : lin_state FP e = @ls_linr FP (enq v) tt) by (apply Hnot_lini; rewrite <- Ek; exact (entry_lookup e P' He)).
          rewrite Hes. exact Logic.I.
        * destruct (lin_update_incl _ _ _ _ _ _ Hu He) as [He0 | He0]; [| exfalso; apply Ek; rewrite He0; reflexivity].
          pose proof (Hcoup e He0) as Hc. rewrite Hγ in Hc.
          assert (Hx : se_owner (Build_ScheduledEvent (t, h) (IE t hu (op_store n (Pos.to_nat v)))) <> lin_key e)
            by (cbn; intros E; exact (Ek (eq_sym E))).
          pose proof (entry_lookup e P He0) as Hle.
          destruct (lin_state FP e) as [o | o | o r]; cbn in Hc |- *; [destruct o as [v1 |] | destruct o as [v1 |] | exact Logic.I].
          -- exact (owns_emit_other _ _ _ _ _ Hx Hc).
          -- exact (owns_emit_other _ _ _ _ _ Hx Hc).
          -- destruct Hc as (n1 & Hn1 & Hv1 & Ho1). exists n1.
             assert (Ht1 : lin_tid FP e <> t).
             { destruct e as [te he se]. cbn in *. exact (Hlini_other_t te he v1 Hle Ek). }
             split; [cbn; rewrite TMap.gro by exact Ht1; exact Hn1 |].
             split; [exact Hv1 | exact (owns_emit_other _ _ _ _ _ Hx Ho1)].
          -- exact Logic.I.
      + intros t' n' Hf'. unfold st' in Hf'. cbn in Hf'. destruct (Pos.eq_dec t' t) as [-> | Ht'].
        * rewrite TMap.grs in Hf'. discriminate.
        * rewrite TMap.gro in Hf' by exact Ht'. destruct (Hpend t' n' Hf') as (h' & v' & Hl'). exists h', v'.
          apply (lin_update_other_lookup _ _ _ _ _ _ _ Hu); [intros E; injection E as E _; exact (Ht' E) | exact Hl'].
      + intros t' h1 h2 v1 v2 H1 H2. exact (Huniq t' h1 h2 v1 v2 (Hlini_back _ _ _ H1) (Hlini_back _ _ _ H2)).
      + intros k1 k2 Ht Ho Hpast e He.
        rewrite <- (lin_update_keys _ _ _ _ _ Hu) in Ho.
        assert (He0 : In e γ) by (rewrite Hγ; exact (incl_remove_mid _ _ _ e He)).
        apply (Hord k1 k2 Ht Ho); [| exact He0].
        destruct (callkey_eq_dec k2 (t, h)) as [-> | Ek2]; [exists v; left; exact Hl |].
        destruct Hpast as (v2 & [H2 | H2]); exists v2; [left | right]; exact (lin_update_back _ _ _ _ _ _ _ Hu H2 Ek2).
    - apply gq_intro; [exact (eihl_step1 _ _ _ Hs) | | exact (amono_finish_enq t st n Hpwf Hf) |].
      + intros k' Hne. split; [intros ls Hl'; exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu Hne Hl') |].
        exact (kg_ghost_emit_other _ _ _ _ _ Hge Hne).
      + intros t' h' v' n' H1 H2 Hf'. assert (Hne : (t', h') <> (t, h)).
        { intros E. rewrite E in H2. pose proof (Hnot_lini _ H2) as E2. discriminate E2. }
        pose proof (Hlini_other_t _ _ _ H1 Hne) as Ht'. unfold st'. cbn. rewrite TMap.gro by exact Ht'. exact Hf'.
  Qed.

  (** *** The dequeue's [xchg]: [AInv] and [ARet], or [poqrd_dead] *)

  Lemma vf_idq t h (st : QSt) :
    Step VF (Build_ThreadEvent t (@InvEv FP h deq)) (POQReady st) (POQAtomic st t).
  Proof. left. cbn. exists st. split; reflexivity. Qed.

  Lemma vf_rdq t h (st : QSt) n (r : positive) :
    poq_minimal st n -> poq_complete st n -> poq_vertices st n = Some r ->
    Step VF (Build_ThreadEvent t (@ResEv FP h deq r)) (POQAtomic st t) (POQReady (poq_mark_garbage n st)).
  Proof. intros Hm Hc Hv. left. cbn. exists st, n. auto. Qed.

  Lemma vf_dead t h (st : QSt) :
    Step VF (Build_ThreadEvent t (@InvEv FP h deq)) (POQReady st) (POQReady st).
  Proof. right. cbn. exists st. split; reflexivity. Qed.

  (** Readiness of a dequeue's [AInv] at one of its [xchg]s: an older
      enqueue of the thread is crossed by [I(enq, deq)]; an older dequeue
      at [ls_inv] owns an [xchg], which orders the emitted one. *)
  Theorem deq_ready m st (P : LinPool FP) (γ γ' : Ghost ES FP) t h hu s :
    IqC m st P γ -> lin_lookup (t, h) (@ls_inv FP deq) P ->
    ghost_emit (t, h) (IE t hu (op_xchg s)) γ γ' ->
    exists P1, lin_invoke_update t h deq P P1 /\ lin_pool_well_formed P1.
  Proof.
    intros HC Hl Hge. destruct (ghost_emit_shape _ _ _ _ Hge I) as (g1 & g2 & Hγ & _ & Hnb).
    apply (emit_ready_mixed P γ g1 g2 t h deq (IE t hu (op_xchg s)) (iq_wf _ _ _ _ HC) Hl (iq_age _ _ _ _ HC)); [| exact Hγ | exact Hnb].
    intros k1 o1 Ht Ho Hl1. destruct o1 as [v1 |].
    - left. cbn. exact Logic.I.
    - right. pose proof (coup_of_lookup _ _ _ _ _ _ HC Hl1) as Hc. cbn in Hc. destruct Hc as (e & He & Hoe & Hx).
      exists e. split; [exact He |]. split; [exact Hoe |].
      apply deq_blocks; [exact (gwf_of_in _ _ _ _ _ HC He) | rewrite Hoe; exact Ht | right; exact Hx].
  Qed.

  (** The vertex at a non-empty slot below the dequeue's bound is
      removable: complete, live, and minimal by the scan. *)
  Lemma take_minimal m st (P : LinPool FP) (γ : Ghost ES FP) s r :
    IqC m st P γ -> m (S s) <> 0 -> ScanC st r s -> s < r ->
    exists v, poq_vertices st s = Some v /\ Pos.to_nat v = m (S s) /\
      poq_complete st s /\ ~ poq_garbage st s /\ poq_minimal st s.
  Proof.
    intros HC Hnz (Hr & Hscan) Hsr. pose proof (iq_pwf _ _ _ _ HC) as Hpwf.
    destruct (iq_cells _ _ _ _ HC s) as [C1 C2].
    assert (Hs : s < poq_next st) by (destruct (Nat.lt_ge_cases s (poq_next st)) as [H | H]; [exact H | exfalso; exact (Hnz (C1 H))]).
    destruct (C2 Hs) as [(_ & Hz) | [(_ & Hz) | (Hc & Hng & v & Hv & Hval)]]; [exfalso; exact (Hnz Hz) | exfalso; exact (Hnz Hz) |].
    exists v. split; [exact Hv |]. split; [symmetry; exact Hval |]. split; [exact Hc |]. split; [exact Hng |].
    split; [split; [exact (proj1 Hc) | exact Hng] |].
    intros j Hedge Hlive.
    assert (Hjs : j < s) by exact (wf_edge_lt st Hpwf s j Hedge).
    assert (Hcj : poq_complete st j).
    { split; [apply (proj2 (wf_vertex_iff_lt st Hpwf j)); lia |].
      intros Hpj. exact (wf_pending_no_incoming st Hpwf s j Hpj Hedge). }
    pose proof (Hscan j Hjs Hlive Hcj s Hedge). lia.
  Qed.

  Theorem iq_xchg_take t h hu s r (σ σ' : State VE) st (P : LinPool FP) (γ γ' : Ghost ES FP) :
    Iq (σ, POk (POQReady st) P, γ) -> lin_lookup (t, h) (@ls_inv FP deq) P ->
    Step VE (IE t hu (op_xchg s)) σ σ' -> ghost_emit (t, h) (IE t hu (op_xchg s)) γ γ' ->
    fst (fst σ) (S s) <> 0 -> ScanC st r s -> s < r ->
    exists v P1 P2,
      poq_vertices st s = Some v /\ Pos.to_nat v = fst (fst σ) (S s) /\
      lin_invoke_update t h deq P P1 /\ lin_update (t, h) (@ls_lini FP deq) (@ls_linr FP deq v) P1 P2 /\
      poss_steps VF (POk (POQReady st) P) (POk (POQReady (poq_mark_garbage s st)) P2) /\
      Iq (σ', POk (POQReady (poq_mark_garbage s st)) P2, γ') /\
      Gq (t, h) (σ, POk (POQReady st) P, γ) (σ', POk (POQReady (poq_mark_garbage s st)) P2, γ').
  Proof.
    intros HI Hl Hs Hge Hnz Hscan Hsr.
    pose proof HI as (st0 & P0 & Hp & Hru & HC). cbn in Hp. injection Hp as <- <-.
    unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
    destruct (take_minimal _ _ _ _ _ _ HC Hnz Hscan Hsr) as (v & Hv & Hval & Hc & Hng & Hmin).
    destruct (deq_ready _ _ _ _ _ _ _ _ _ HC Hl Hge) as (P1 & Hinv & Hwf1).
    pose proof (lin_invoke_update_is_update _ _ _ _ _ Hinv) as Hu1.
    destruct (RelaxedHoareInherit.lin_update_exists_gen (t, h) (@ls_lini FP deq) (@ls_linr FP deq v) P1 Hwf1
                (lin_update_target _ _ _ _ _ Hu1)) as (P2 & Hu2).
    destruct (ghost_emit_shape _ _ _ _ Hge I) as (g1 & g2 & Hγ & Hγ' & Hnb).
    destruct HC as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
    set (st' := poq_mark_garbage s st).
    destruct (step_xchg _ _ _ _ _ Hs) as [Hm' _]. set (m := fst (fst σ)) in *.
    assert (Hk2 : forall ls, lin_lookup (t, h) ls P2 -> ls = @ls_linr FP deq v)
      by (intros ls Hl'; exact (lin_update_self _ _ _ _ _ _ Hwf1 Hu2 Hl')).
    assert (Hback : forall k' ls, k' <> (t, h) -> lin_lookup k' ls P2 -> lin_lookup k' ls P).
    { intros k' ls Hne Hl'. exact (lin_update_back _ _ _ _ _ _ _ Hu1 (lin_update_back _ _ _ _ _ _ _ Hu2 Hl' Hne) Hne). }
    assert (Hfwd : forall k' ls, k' <> (t, h) -> lin_lookup k' ls P -> lin_lookup k' ls P2).
    { intros k' ls Hne Hl'. exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu2 Hne (lin_update_other_lookup _ _ _ _ _ _ _ Hu1 Hne Hl')). }
    assert (Hk_enq : forall o ls, lin_lookup (t, h) ls P -> ls = @ls_inv FP o \/ ls = @ls_lini FP o \/ (exists r0, ls = @ls_linr FP o r0) -> o = deq).
    { intros o ls Hl' Hls. pose proof (lookup_unique _ _ _ _ Hwf Hl Hl') as E.
      destruct Hls as [-> | [-> | (r0 & ->)]]; [injection E as E; exact (eq_sym E) | discriminate E | discriminate E]. }
    exists v, P1, P2. split; [exact Hv |]. split; [exact Hval |]. split; [exact Hinv |]. split; [exact Hu2 |].
    split.
    { apply (rt_trans _ _ _ (POk (POQAtomic st t) P1)).
      - apply rt_step. exists (t, h). exact (psa_inv VF t h deq (POQReady st) (POQAtomic st t) P P1 Hinv (vf_idq t h st)).
      - apply rt_step. exists (t, h). exact (psa_ret VF t h deq v (POQAtomic st t) (POQReady st') P1 P2 Hu2 (vf_rdq t h st s v Hmin Hc Hv)). }
    split.
    - exists st', P2. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δRC _ _ _ Hs Hru) |].
      unfold regs, ps_mem, ps_ghost. cbn [fst snd]. rewrite Hγ'. constructor.
      + exact (lin_update_well_formed _ _ _ _ _ Hu2 Hwf1).
      + apply (gage_lin_update _ _ _ _ _ _ Hu2). apply (gage_lin_invoke_update _ _ _ _ _ _ Hinv).
        rewrite Hγ in Hage. exact (gage_remove _ _ _ _ Hage).
      + rewrite Hγ in Hgwf. exact (gwf_emit _ _ _ Hgwf).
      + rewrite Hγ in Hgnd. exact (nodup_emit _ _ _ Hgnd).
      + exact (poq_mark_garbage_wf s st Hpwf Hc).
      + rewrite Hm'. rewrite mem_upd_other by discriminate. exact Hctr.
      + intros j. unfold st', CellOK. rewrite Hm'. destruct (Nat.eq_dec j s) as [-> | Hjs].
        * rewrite mem_upd_same. split; [intros _; reflexivity |]. intros _. right. left.
          split; [cbn; left; reflexivity | reflexivity].
        * rewrite mem_upd_other by (intros E; injection E as E; exact (Hjs (eq_sym E))).
          destruct (Hcells j) as [C1 C2]. split; [exact C1 |]. intros Hj.
          destruct (C2 Hj) as [(Hpv & Hz) | [(Hg & Hz) | (Hcj & Hngj & w & Hw & Hz)]].
          -- left. split; [exact Hpv | exact Hz].
          -- right. left. split; [cbn; right; exact Hg | exact Hz].
          -- right. right. split; [apply poq_mark_garbage_complete; exact Hcj |].
             split; [cbn; intros [E | Hg]; [exact (Hjs E) | exact (Hngj Hg)] |]. exists w. auto.
      + intros e He. destruct (callkey_eq_dec (lin_key e) (t, h)) as [Ek | Ek].
        * assert (Hes : lin_state FP e = @ls_linr FP deq v) by (apply Hk2; rewrite <- Ek; exact (entry_lookup e P2 He)).
          rewrite Hes. exact Logic.I.
        * pose proof (Hback _ _ Ek (entry_lookup e P2 He)) as He0. unfold lin_lookup in He0. rewrite <- entry_eta in He0.
          pose proof (Hcoup e He0) as Hcp. rewrite Hγ in Hcp.
          assert (Hx : se_owner (Build_ScheduledEvent (t, h) (IE t hu (op_xchg s))) <> lin_key e)
            by (cbn; intros E; exact (Ek (eq_sym E))).
          destruct (lin_state FP e) as [o | o | o r0]; cbn in Hcp |- *; [destruct o as [v1 |] | destruct o as [v1 |] | exact Logic.I].
          -- exact (owns_emit_other _ _ _ _ _ Hx Hcp).
          -- exact (owns_emit_other _ _ _ _ _ Hx Hcp).
          -- destruct Hcp as (n1 & Hn1 & Hv1 & Ho1). exists n1. split; [exact Hn1 |]. split; [exact Hv1 |].
             exact (owns_emit_other _ _ _ _ _ Hx Ho1).
          -- exact Logic.I.
      + intros t' n' Hf'. destruct (Hpend t' n' Hf') as (h' & v' & Hl'). exists h', v'.
        apply Hfwd; [| exact Hl']. intros E. rewrite E in Hl'. pose proof (lookup_unique _ _ _ _ Hwf Hl Hl') as E2. discriminate E2.
      + intros t' h1 h2 v1 v2 H1 H2.
        assert (Hn : forall h' v', lin_lookup (t', h') (@ls_lini FP (enq v')) P2 -> (t', h') <> (t, h))
          by (intros h' v' Hl' E; rewrite E in Hl'; pose proof (Hk2 _ Hl') as E2; discriminate E2).
        exact (Huniq t' h1 h2 v1 v2 (Hback _ _ (Hn _ _ H1) H1) (Hback _ _ (Hn _ _ H2) H2)).
      + intros k1 k2 Ht Ho Hpast e He.
        rewrite <- (lin_update_keys _ _ _ _ _ Hu2), <- (lin_invoke_update_keys _ _ _ _ _ Hinv) in Ho.
        assert (He0 : In e γ) by (rewrite Hγ; exact (incl_remove_mid _ _ _ e He)).
        apply (Hord k1 k2 Ht Ho); [| exact He0].
        assert (Hk2ne : k2 <> (t, h)).
        { intros ->. destruct Hpast as (v2 & [H2 | H2]); pose proof (Hk2 _ H2) as E2; discriminate E2. }
        destruct Hpast as (v2 & [H2 | H2]); exists v2; [left | right]; exact (Hback _ _ Hk2ne H2).
    - apply gq_intro; [exact (eihl_step1 _ _ _ Hs) | | exact (amono_mark_garbage s st) |].
      + intros k' Hne. split; [intros ls Hl'; exact (Hfwd k' ls Hne Hl') |]. exact (kg_ghost_emit_other _ _ _ _ _ Hge Hne).
      + intros t' h' v' n' _ _ Hf'. exact Hf'.
  Qed.

  Theorem iq_xchg_dead t h hu s (σ σ' : State VE) st (P : LinPool FP) (γ γ' : Ghost ES FP) :
    Iq (σ, POk (POQReady st) P, γ) -> lin_lookup (t, h) (@ls_inv FP deq) P ->
    Step VE (IE t hu (op_xchg s)) σ σ' -> ghost_emit (t, h) (IE t hu (op_xchg s)) γ γ' ->
    fst (fst σ) (S s) = 0 ->
    exists P1,
      lin_invoke_update t h deq P P1 /\
      poss_steps VF (POk (POQReady st) P) (POk (POQReady st) P1) /\
      Iq (σ', POk (POQReady st) P1, γ') /\
      Gq (t, h) (σ, POk (POQReady st) P, γ) (σ', POk (POQReady st) P1, γ').
  Proof.
    intros HI Hl Hs Hge Hz.
    pose proof HI as (st0 & P0 & Hp & Hru & HC). cbn in Hp. injection Hp as <- <-.
    unfold regs, ps_mem, ps_ghost in HC. cbn [fst snd] in HC.
    destruct (deq_ready _ _ _ _ _ _ _ _ _ HC Hl Hge) as (P1 & Hinv & Hwf1).
    pose proof (lin_invoke_update_is_update _ _ _ _ _ Hinv) as Hu1.
    destruct (ghost_emit_shape _ _ _ _ Hge I) as (g1 & g2 & Hγ & Hγ' & Hnb).
    destruct HC as [Hwf Hage Hgwf Hgnd Hpwf Hctr Hcells Hcoup Hpend Huniq Hord].
    destruct (step_xchg _ _ _ _ _ Hs) as [Hm' _].
    assert (Hmx : forall l, fst (fst σ') l = fst (fst σ) l).
    { intros l. rewrite Hm'. unfold mem_upd. destruct (Nat.eqb_spec (S s) l) as [<- | _]; [exact (eq_sym Hz) | reflexivity]. }
    assert (Hk1 : forall ls, lin_lookup (t, h) ls P1 -> ls = @ls_lini FP deq)
      by (intros ls Hl'; exact (lin_update_self _ _ _ _ _ _ Hwf Hu1 Hl')).
    assert (Hback : forall k' ls, k' <> (t, h) -> lin_lookup k' ls P1 -> lin_lookup k' ls P)
      by (intros k' ls Hne Hl'; exact (lin_update_back _ _ _ _ _ _ _ Hu1 Hl' Hne)).
    exists P1. split; [exact Hinv |]. split.
    { apply rt_step. exists (t, h). exact (psa_inv VF t h deq (POQReady st) (POQReady st) P P1 Hinv (vf_dead t h st)). }
    split.
    - exists st, P1. split; [reflexivity |]. split; [exact (eihl_rec_used_step (E := ES) δRC _ _ _ Hs Hru) |].
      unfold regs, ps_mem, ps_ghost. cbn [fst snd]. rewrite Hγ'. constructor.
      + exact Hwf1.
      + apply (gage_lin_invoke_update _ _ _ _ _ _ Hinv). rewrite Hγ in Hage. exact (gage_remove _ _ _ _ Hage).
      + rewrite Hγ in Hgwf. exact (gwf_emit _ _ _ Hgwf).
      + rewrite Hγ in Hgnd. exact (nodup_emit _ _ _ Hgnd).
      + exact Hpwf.
      + rewrite Hmx. exact Hctr.
      + intros j. apply (cellok_ext st (fst (fst σ))); [intros j'; apply Hmx | exact (Hcells j)].
      + intros e He. destruct (callkey_eq_dec (lin_key e) (t, h)) as [Ek | Ek].
        * assert (Hes : lin_state FP e = @ls_lini FP deq) by (apply Hk1; rewrite <- Ek; exact (entry_lookup e P1 He)).
          rewrite Hes. exact Logic.I.
        * pose proof (Hback _ _ Ek (entry_lookup e P1 He)) as He0. unfold lin_lookup in He0. rewrite <- entry_eta in He0.
          pose proof (Hcoup e He0) as Hcp. rewrite Hγ in Hcp.
          assert (Hx : se_owner (Build_ScheduledEvent (t, h) (IE t hu (op_xchg s))) <> lin_key e)
            by (cbn; intros E; exact (Ek (eq_sym E))).
          destruct (lin_state FP e) as [o | o | o r0]; cbn in Hcp |- *; [destruct o as [v1 |] | destruct o as [v1 |] | exact Logic.I].
          -- exact (owns_emit_other _ _ _ _ _ Hx Hcp).
          -- exact (owns_emit_other _ _ _ _ _ Hx Hcp).
          -- destruct Hcp as (n1 & Hn1 & Hv1 & Ho1). exists n1. split; [exact Hn1 |]. split; [exact Hv1 |].
             exact (owns_emit_other _ _ _ _ _ Hx Ho1).
          -- exact Logic.I.
      + intros t' n' Hf'. destruct (Hpend t' n' Hf') as (h' & v' & Hl'). exists h', v'.
        apply (lin_update_other_lookup _ _ _ _ _ _ _ Hu1); [| exact Hl'].
        intros E. rewrite E in Hl'. pose proof (lookup_unique _ _ _ _ Hwf Hl Hl') as E2. discriminate E2.
      + intros t' h1 h2 v1 v2 H1 H2.
        assert (Hn : forall h' v', lin_lookup (t', h') (@ls_lini FP (enq v')) P1 -> (t', h') <> (t, h))
          by (intros h' v' Hl' E; rewrite E in Hl'; pose proof (Hk1 _ Hl') as E2; discriminate E2).
        exact (Huniq t' h1 h2 v1 v2 (Hback _ _ (Hn _ _ H1) H1) (Hback _ _ (Hn _ _ H2) H2)).
      + intros k1 k2 Ht Ho Hpast e He.
        rewrite <- (lin_invoke_update_keys _ _ _ _ _ Hinv) in Ho.
        assert (He0 : In e γ) by (rewrite Hγ; exact (incl_remove_mid _ _ _ e He)).
        apply (Hord k1 k2 Ht Ho); [| exact He0].
        assert (Hk2ne : k2 <> (t, h)).
        { intros ->. destruct Hpast as (v2 & [H2 | H2]); pose proof (Hk1 _ H2) as E2; discriminate E2. }
        destruct Hpast as (v2 & [H2 | H2]); exists v2; [left | right]; exact (Hback _ _ Hk2ne H2).
    - apply gq_intro; [exact (eihl_step1 _ _ _ Hs) | | apply amono_refl | apply pfreeze_same].
      intros k' Hne. split; [intros ls Hl'; exact (lin_update_other_lookup _ _ _ _ _ _ _ Hu1 Hne Hl') |].
      exact (kg_ghost_emit_other _ _ _ _ _ Hge Hne).
  Qed.

  (** ** Part 7. The stability kit *)

  (** [k] is at phase [ls]. *)
  Definition KLk (k : CallKey FP) (ls : LinState FP) : Assn VE VF := fun s =>
    exists st P, ps_poss s = POk (POQReady st) P /\ lin_lookup k ls P.

  (** [k]'s pending invocations are exactly [l], in ghost order. *)
  Definition KG (k : CallKey FP) (l : list (ThreadEvent ES)) : Assn VE VF := fun s => kg k (ps_ghost s) = l.

  Definition KMine (key : CallKey ES) (x0 : RelaxedTraceLin.Op ES) : Assn VE VF := fun s =>
    eihl_mine (E := ES) δRC key x0 (ps_mem s).

  (** [k] is the pending enqueue of its thread, with vertex [n] of value
      [v]. *)
  Definition KPend (k : CallKey FP) (n : nat) (v : positive) : Assn VE VF := fun s =>
    exists st P, ps_poss s = POk (POQReady st) P /\ lin_lookup k (@ls_lini FP (enq v)) P /\
      TMap.find (fst k) (poq_pending st) = Some n /\ poq_vertices st n = Some v.

  (** The scan facts of a dequeue that read the counter [r] and found the
      slots below [i] empty. *)
  Definition KScan (r i : nat) : Assn VE VF := fun s =>
    exists st P, ps_poss s = POk (POQReady st) P /\ poq_wf st /\ ScanC st r i.

  (** The guarantees of the slots of a derivation: [GRes] (a response:
      the possibility and the ghost are kept), [GPl] (an invocation that
      is not a linearization point: the possibility is kept), and [Gq] at
      a linearization point. *)
  Definition GRes (k : CallKey FP) : PRel VE VF := fun s s' =>
    Gq k s s' /\ ps_poss s' = ps_poss s /\ ps_ghost s' = ps_ghost s.

  Definition GPl (k : CallKey FP) : PRel VE VF := fun s s' =>
    Gq k s s' /\ ps_poss s' = ps_poss s.

  (** *** Stability under the rely *)

  Lemma klk_stable_r k ls : Stable Iq (Rq k) (KLk k ls).
  Proof.
    intros s s' (st & P & Hp & Hl) (_ & st1 & P1 & st1' & P1' & Hp1 & Hp1' & (Hlk & _) & _) _.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists st1', P1'. split; [exact Hp1' | exact (Hlk ls Hl)].
  Qed.

  Lemma kg_stable_r k l : Stable Iq (Rq k) (KG k l).
  Proof. intros s s' Hg (_ & st1 & P1 & st1' & P1' & _ & _ & (_ & Hkg) & _) _. unfold KG in *. rewrite Hkg. exact Hg. Qed.

  Lemma kmine_stable_r k key x0 : Stable Iq (Rq k) (KMine key x0).
  Proof. intros s s' Hm (Hs & _) _. exact (eihl_mine_steps (E := ES) δRC _ _ _ _ Hs Hm). Qed.

  Lemma kmine_stable_g k key x0 : Stable Iq (Gq k) (KMine key x0).
  Proof. intros s s' Hm (Hs & _) _. exact (eihl_mine_steps (E := ES) δRC _ _ _ _ Hs Hm). Qed.

  Lemma kpend_stable_r k n v : Stable Iq (Rq k) (KPend k n v).
  Proof.
    intros s s' (st & P & Hp & Hl & Hf & Hv) (_ & st1 & P1 & st1' & P1' & Hp1 & Hp1' & (Hlk & _) & Hmono & Hpf) _.
    rewrite Hp in Hp1. injection Hp1 as <- <-. exists st1', P1'. split; [exact Hp1' |].
    pose proof (Hlk _ Hl) as Hl'. split; [exact Hl' |].
    destruct k as [t h]. split; [exact (Hpf t h v n Hl Hl' Hf) |].
    exact (proj1 (proj2 Hmono) n v Hv).
  Qed.

  (** [ScanC] only needs the queue state to grow. *)
  Lemma scanc_mono (st st' : QSt) r i : poq_wf st -> AMono st st' -> ScanC st r i -> ScanC st' r i.
  Proof.
    intros Hwf (Hn & Hv & He & He' & Hg & Hc) (Hr & Hscan). split; [lia |].
    intros j Hj Hlive Hcomp n Hedge. destruct (He' n j Hedge) as [Hold | Hnew]; [| lia].
    assert (Hjn : j < n) by exact (wf_edge_lt st Hwf n j Hold).
    assert (Hnv : n < poq_next st) by exact (poq_vertex_lt st n Hwf (wf_edge_source st Hwf n j Hold)).
    apply (Hscan j Hj); [| | exact Hold].
    - split; [apply (proj2 (wf_vertex_iff_lt st Hwf j)); lia |]. intros Hgj. exact (proj2 Hlive (Hg j Hgj)).
    - split; [apply (proj2 (wf_vertex_iff_lt st Hwf j)); lia |]. intros Hpj. exact (wf_pending_no_incoming st Hwf n j Hpj Hold).
  Qed.

  Lemma kscan_stable_r k r i : Stable Iq (Rq k) (KScan r i).
  Proof.
    intros s s' (st & P & Hp & Hwf & Hsc) (_ & st1 & P1 & st1' & P1' & Hp1 & Hp1' & _ & Hmono & _) (st2 & P2 & Hp2 & _ & HC).
    rewrite Hp in Hp1. injection Hp1 as <- <-. rewrite Hp1' in Hp2. injection Hp2 as <- <-.
    exists st1', P1'. split; [exact Hp1' |]. split; [exact (iq_pwf _ _ _ _ HC) | exact (scanc_mono st st1' r i Hwf Hmono Hsc)].
  Qed.

  Lemma kscan_stable_g k r i : Stable Iq (Gq k) (KScan r i).
  Proof.
    intros s s' (st & P & Hp & Hwf & Hsc) (_ & st1 & P1 & st1' & P1' & Hp1 & Hp1' & _ & Hmono & _) (st2 & P2 & Hp2 & _ & HC).
    rewrite Hp in Hp1. injection Hp1 as <- <-. rewrite Hp1' in Hp2. injection Hp2 as <- <-.
    exists st1', P1'. split; [exact Hp1' |]. split; [exact (iq_pwf _ _ _ _ HC) | exact (scanc_mono st st1' r i Hwf Hmono Hsc)].
  Qed.

  (** *** Stability under the own guarantees *)

  Lemma klk_stable_pl k k' ls : Stable Iq (GPl k') (KLk k ls).
  Proof. intros s s' (st & P & Hp & Hl) (_ & Hp') _. exists st, P. rewrite Hp', Hp. auto. Qed.

  Lemma klk_stable_res k k' ls : Stable Iq (GRes k') (KLk k ls).
  Proof. intros s s' (st & P & Hp & Hl) (_ & Hp' & _) _. exists st, P. rewrite Hp', Hp. auto. Qed.

  Lemma kg_stable_res k k' l : Stable Iq (GRes k') (KG k l).
  Proof. intros s s' Hg (_ & _ & Hg') _. unfold KG in *. rewrite Hg'. exact Hg. Qed.

  Lemma kmine_stable_pl k key x0 : Stable Iq (GPl k) (KMine key x0).
  Proof. intros s s' Hm (HG & _) HI. exact (kmine_stable_g k key x0 s s' Hm HG HI). Qed.

  Lemma kmine_stable_res k key x0 : Stable Iq (GRes k) (KMine key x0).
  Proof. intros s s' Hm (HG & _) HI. exact (kmine_stable_g k key x0 s s' Hm HG HI). Qed.

  Lemma kpend_stable_pl k k' n v : Stable Iq (GPl k') (KPend k n v).
  Proof. intros s s' (st & P & Hp & H) (_ & Hp') _. exists st, P. rewrite Hp', Hp. auto. Qed.

  Lemma kpend_stable_res k k' n v : Stable Iq (GRes k') (KPend k n v).
  Proof. intros s s' (st & P & Hp & H) (_ & Hp' & _) _. exists st, P. rewrite Hp', Hp. auto. Qed.

  Lemma kscan_stable_pl k r i : Stable Iq (GPl k) (KScan r i).
  Proof. intros s s' H (HG & _) HI. exact (kscan_stable_g k r i s s' H HG HI). Qed.

  Lemma kscan_stable_res k r i : Stable Iq (GRes k) (KScan r i).
  Proof. intros s s' H (HG & _) HI. exact (kscan_stable_g k r i s s' H HG HI). Qed.

  (** *** Facts read off the invariant *)

  Lemma klk_unique k ls1 ls2 s : Iq s -> KLk k ls1 s -> KLk k ls2 s -> ls1 = ls2.
  Proof.
    intros (st & P & Hp & _ & HC) (st1 & P1 & Hp1 & H1) (st2 & P2 & Hp2 & H2).
    rewrite Hp in Hp1, Hp2. injection Hp1 as <- <-. injection Hp2 as <- <-.
    exact (lookup_unique _ _ _ _ (iq_wf _ _ _ _ HC) H1 H2).
  Qed.

  (** A response returns the owned record. *)
  Lemma mine_res_val key o (r : Sig.ar o) x0 (σ σ' : State VE) :
    eihl_mine (E := ES) δRC key x0 σ ->
    Step VE (Build_ThreadEvent (fst key) (@ResEv ES (snd key) o r)) σ σ' ->
    x0 = @RelaxedTraceLin.Build_Op ES key o r.
  Proof. intros Hm Hs. exact (eihl_mine_res (E := ES) δRC key x0 o r σ σ' Hm Hs). Qed.

End WHWQInv.
