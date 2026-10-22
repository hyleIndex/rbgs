(** * WHWQProg: the weak Herlihy–Wing queue module over RCMem

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P5.  The module [Mwhw],
    its method executions, and tactics for concrete module executions.
    It proves no RLHL triple and no relaxed-linearizability result; the
    concrete executions of T7 are in [WHWQExec].

    ** The code (Appendix/WHWQueue.tex:14–17, with decision D3′)

    - [enq v]: [i := FAA(q, 1, rel); store(q + i + 1, v, rel)], i.e.
      [op_faa], then [op_store i v] (slot [i], location [i + 1]; see the
      slot convention of [WHWQSpec]).
    - [deq]: [while (true) { t := ld(q, acq); for i := 1 to t do
      { x := xchg(q + i, null, (acq, rlx)); if (x != null) return x } }],
      i.e. [op_ld], then [op_xchg s] for the slots [s = 0 .. t - 1]
      (the paper's index [i] is slot [i - 1]); [null] is [0].  A run that
      reads [t = 0], or finds every slot empty, reads the counter again.
    - Values (decision D4): [enq v] stores [Pos.to_nat v]; a successful
      [deq] returns [Pos.of_nat x] for the non-zero [x] it swapped out.
    - Both methods are state machines under [RelaxedHoareRun.run]: every
      call is waited before the next one is issued, so all reordering
      comes from the module frontier ((F1)–(F3), [must_precede]).

    ** Dependency tags

    The shallow embedding cannot compute tags, so they are written by
    hand ([dix] of each [SCall]).  They follow the paper's dependency
    policy for memory cells (Appendix/programlogic.tex:106–112, and the
    invocation rule at :163–172): the tag of a call is the set of handles
    its arguments depend on, plus, for a control-ordered operation (every
    operation except a plain read), the handles the enclosing branches
    depend on (κ).  Hence:
    - the [FAA] and every [ld] are untagged (constant arguments; a plain
      read is not control-ordered);
    - the store is tagged with the [FAA] (its address is computed from the
      returned index);
    - each [xchg] is tagged with every earlier call of its dequeue (κ: the
      loop bound read by each [ld], and every earlier null test, across
      iterations; its own arguments are constants).
    A tag only orders the responses it names before the tagged
    invocation.  Every call of a dequeue acquires, so (F2) already keeps
    every later invocation of the thread after it
    ([WHWQSpec.rc_si_not_after_acq]), and in the enqueue (F2) keeps the
    store after the [FAA] (the store releases).  So on complete
    executions the tags decide only how late a response event may be
    emitted, not which effects may be reordered.  Over [EI δRC], where the
    result of a call is fixed at its invocation, no other choice of tags
    is expected to change the complete overlay traces (argued, review
    gate 3, not proved).  On executions that are not complete the tags do
    matter (review gate 4, WHWQ-g4-2).  A call whose committed response
    differs from its record never receives that response.  The tags keep
    its later tagged invocations from being emitted: without the address
    tag, such an enqueue could store into a slot it was not given;
    without κ, such a dequeue could go on exchanging.  The RLHL
    derivations ([WHWQProof], [WHWQDeq]) use the tag edges.

    ** Results

    - [enq_prod], [deq_prod]: the method executions used by the
      concrete module executions, for every handle base, with the exact
      untagged events and a bound on the tags.  A dequeue's scan is
      [scan_exec] (induction on the number of empty slots it passes).
    - Frontier facts that explain the crossings in [WHWQExec] (the
      tactic [cross_ok] re-proves each crossing directly and does not use
      them).  Within one thread: a dequeue's [ld] and its [xchg]s at
      other slots may be emitted before both the [store] invocation and
      the [store] response of an older enqueue ([deq_inv_crosses_store],
      [deq_res_crosses_store]: none of (F1)–(F3) holds); a dequeue's
      [xchg] at the slot of that store must wait for the store's
      invocation ([xchg_same_slot_blocked]), but may still be emitted
      before the store's response ([inv_crosses_store_res]: a store's
      response orders no later invocation that is not tagged with it); a
      [FAA] waits for the invocation of every older call of its thread
      ([faa_after_older_inv]).
    - The pair a dequeue's exchange uses to overtake an older store needs
      both decisions D2′ and D3′: with a release write part in the
      exchange, as printed in the paper, the pair is ordered
      ([store_xchg_rel_ordered]), and so it is under the plain-only
      relation of decision D2 ([rc_si_D2], [store_xchg_D2_ordered]).
    - Not covered: production lemmas for a dequeue that retries (reads the
      counter again after an empty scan); the machine has these runs, and
      no execution of [WHWQExec] needs them.
    - Tactics for module executions over [EI δRC] (ports of
      [RelaxedHoareSL2Prog] Part 5, with [cross_ok] for [rc_si]).

    No axiom is used ([Print Assumptions]; task log). *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith.PArith micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareRun.
Require Import examples.Relaxed.WHWQ.WHWQSpec.

Import ListNotations.

Module WHWQProg.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedHoareRun.
  Import WHWQSpec.

  Local Abbreviation FP := (FQ positive).

  (** ** Part 1. The methods and the module *)

  (** The enqueue: [E0] before the [FAA]; [E1 i] before the store into
      slot [i]; [ED] done. *)
  Inductive ESt : Type := E0 | E1 (i : nat) | ED.

  Definition enext (v : positive) (st : ESt) : SStep RCEff ESt unit :=
    match st with
    | E0 => SCall op_faa [] (fun i => E1 i)
    | E1 i => SCall (op_store i (Pos.to_nat v)) [0] (fun _ => ED)
    | ED => SDone tt
    end.

  (** The dequeue.  [n] counts the calls made so far (the positions in the
      tag of an [xchg]).  [DLd n] reads the counter (untagged); [DXchg n
      tl s] exchanges slot [s] of a scan over the [tl] slots read, tagged
      with every earlier call; [DRet x] returns. *)
  Inductive DSt : Type :=
  | DLd (n : nat)
  | DXchg (n tl s : nat)
  | DRet (x : nat).

  Definition dnext (st : DSt) : SStep RCEff DSt positive :=
    match st with
    | DLd n =>
        SCall op_ld [] (fun tl => if Nat.eqb tl 0 then DLd (S n) else DXchg (S n) tl 0)
    | DXchg n tl s =>
        SCall (op_xchg s) (seq 0 n)
          (fun x => if Nat.eqb x 0
                    then (if Nat.ltb (S s) tl then DXchg (S n) tl (S s) else DLd (S n))
                    else DRet x)
    | DRet x => SDone (Pos.of_nat x)
    end.

  Definition Mwhw : RelaxedModuleImpl ERC FP :=
    fun op _ =>
      match op as o return Prog ERC (q_ar positive o) with
      | enq v => run (G := ERC) (enext v) [] E0
      | deq => run (G := ERC) dnext [] (DLd 0)
      end.

  (** ** Part 2. Method executions *)

  Definition uinv (t : tid) (h : nat) (o : RCOp) : ThreadEvent ERC :=
    Build_ThreadEvent t (@InvEv ERC h o).

  Definition ures (t : tid) (h : nat) (o : RCOp) (r : rc_ar o) : ThreadEvent ERC :=
    Build_ThreadEvent t (@ResEv ERC h o r).

  (** The untagged events of an enqueue of [v] whose [FAA] returns [i],
      on handles [h] and [S h]. *)
  Definition enq_evs (t : tid) (h i : nat) (v : positive) : list (ThreadEvent ERC) :=
    [uinv t h op_faa; ures t h op_faa i;
     uinv t (S h) (op_store i (Pos.to_nat v)); ures t (S h) (op_store i (Pos.to_nat v)) tt].

  (** A scan from slot [s] that passes [k] empty slots and swaps [x] out of
      slot [s + k], on handles [h], [S h], ... *)
  Fixpoint scan_evs (t : tid) (h s k x : nat) : list (ThreadEvent ERC) :=
    match k with
    | 0 => [uinv t h (op_xchg s); ures t h (op_xchg s) x]
    | S k' => uinv t h (op_xchg s) :: ures t h (op_xchg s) 0 :: scan_evs t (S h) (S s) k' x
    end.

  (** A dequeue that reads [tl] and succeeds in its first iteration at slot
      [k], on handles [h .. h + k + 1]. *)
  Definition deq_evs (t : tid) (h tl k x : nat) : list (ThreadEvent ERC) :=
    uinv t h op_ld :: ures t h op_ld tl :: scan_evs t (S h) 0 k x.

  Lemma pet_app {E : RelaxedSig.t} {R : Type} t (c1 c2 c3 : ProgramConfig E R) tr1 tr2 :
    program_execution_tagged t c1 tr1 c2 -> program_execution_tagged t c2 tr2 c3 ->
    program_execution_tagged t c1 (tr1 ++ tr2) c3.
  Proof.
    induction 1 as [c | c1 c2 c3' tr Hs Hx IH | c1 c2 c3' m tr Hs Hx IH]; intros H2; cbn.
    - exact H2.
    - eapply tagged_execution_silent; [exact Hs | exact (IH H2)].
    - eapply tagged_execution_emit; [exact Hs | exact (IH H2)].
  Qed.

  (** One call of a [run]: its invocation on a fresh handle [hh], tagged
      with [dix], and its response [v]. *)
  Lemma run_call_exec {St R : Type} t (next : St -> SStep RCEff St R) hs st
      (op : RCOp) dix (k : rc_ar op -> St) hh (v : rc_ar op) H :
    next st = SCall op dix k ->
    handle_fresh hh H ->
    program_execution_tagged t (Build_ProgramConfig (run (G := ERC) next hs st) H)
      [Build_TaggedEvent (Build_ThreadEvent t (@InvEv ERC hh op)) (fun q => dep_of hs dix q /\ resolved_in H q);
       Build_TaggedEvent (Build_ThreadEvent t (@ResEv ERC hh op v)) no_deps]
      (Build_ProgramConfig (run (G := ERC) next (hs ++ [hh]) (k v))
         (@Build_FutureEntry ERC hh (Resolved (E := ERC) op v) :: H)).
  Proof.
    intros Hn Hf. rewrite run_unfold, Hn.
    eapply tagged_execution_emit; [apply tagged_futureD; exact Hf |]. cbn beta.
    eapply tagged_execution_emit; [apply tagged_wait_pending; apply resolve_here |]. cbn beta.
    apply tagged_execution_refl.
  Qed.

  Lemma run_done {St R : Type} (next : St -> SStep RCEff St R) hs st r :
    next st = SDone r -> run (G := ERC) next hs st = Ret r.
  Proof. intros Hn. rewrite run_unfold, Hn. reflexivity. Qed.

  Lemma all_resolved_cons_resolved h (op : RCOp) (v : rc_ar op) (H : FutureStore ERC) :
    all_resolved H -> all_resolved (@Build_FutureEntry ERC h (Resolved (E := ERC) op v) :: H).
  Proof. intros HH. constructor; [exact Logic.I | exact HH]. Qed.

  Lemma dep_of_in {A : Type} (hs : list A) dix q : dep_of hs dix q -> In q hs.
  Proof. intros (i & _ & Hi). exact (nth_error_In _ _ Hi). Qed.

  (** The scan of a dequeue. *)
  Lemma scan_exec t tl x (Hx : x <> 0) :
    forall k s n hs H h0 hb,
      s + k < tl -> length hs = n ->
      (forall q, In q (map (fe_handle ERC) H) -> q < h0) ->
      all_resolved H ->
      (forall q, In q hs -> hb <= q) -> hb <= h0 ->
      exists tr H',
        program_execution_tagged t (Build_ProgramConfig (run (G := ERC) dnext hs (DXchg n tl s)) H) tr
          (Build_ProgramConfig (Ret (Pos.of_nat x)) H') /\
        all_resolved H' /\
        map untag tr = scan_evs t h0 s k x /\
        Forall (fun m : TaggedEvent ERC => forall q, tev_deps m q -> hb <= q) tr.
  Proof.
    induction k as [| k IH]; intros s n hs H h0 hb Hk Hn HH Hres Hhs Hb.
    - pose proof (run_call_exec t dnext hs (DXchg n tl s) (op_xchg s) (seq 0 n)
        (fun x => if Nat.eqb x 0
                  then (if Nat.ltb (S s) tl then DXchg (S n) tl (S s) else DLd (S n))
                  else DRet x) h0 x H eq_refl) as Hc.
      assert (Hf : @handle_fresh ERC h0 H) by (intros Hin; specialize (HH _ Hin); lia).
      specialize (Hc Hf). cbn beta in Hc.
      apply Nat.eqb_neq in Hx. rewrite Hx in Hc. rewrite (run_done dnext _ (DRet x) (Pos.of_nat x) eq_refl) in Hc.
      eexists _, _. split; [exact Hc |]. split; [apply all_resolved_cons_resolved; exact Hres |].
      split; [reflexivity |].
      constructor; [| constructor; [intros q [] | constructor]].
      intros q [Hq _]. apply Hhs. exact (dep_of_in _ _ _ Hq).
    - pose proof (run_call_exec t dnext hs (DXchg n tl s) (op_xchg s) (seq 0 n)
        (fun x => if Nat.eqb x 0
                  then (if Nat.ltb (S s) tl then DXchg (S n) tl (S s) else DLd (S n))
                  else DRet x) h0 0 H eq_refl) as Hc.
      assert (Hf : @handle_fresh ERC h0 H) by (intros Hin; specialize (HH _ Hin); lia).
      specialize (Hc Hf). cbn beta in Hc.
      assert (Hlt : Nat.ltb (S s) tl = true) by (apply Nat.ltb_lt; lia).
      rewrite Nat.eqb_refl, Hlt in Hc.
      destruct (IH (S s) (S n) (hs ++ [h0]) (@Build_FutureEntry ERC h0 (Resolved (E := ERC) (op_xchg s) 0) :: H) (S h0) hb)
        as (tr & H' & Hx' & Hres' & Hm & Hd).
      + lia.
      + rewrite length_app, Hn. cbn. lia.
      + intros q [Hq | Hq]; [cbn in Hq; lia | specialize (HH _ Hq); lia].
      + apply all_resolved_cons_resolved. exact Hres.
      + intros q Hq. apply in_app_or in Hq as [Hq | [Hq | []]]; [exact (Hhs _ Hq) | lia].
      + lia.
      + eexists _, H'. split; [exact (pet_app _ _ _ _ _ _ Hc Hx') |].
        split; [exact Hres' |]. split; [cbn; rewrite Hm; reflexivity |].
        constructor; [| constructor; [intros q [] | exact Hd]].
        intros q [Hq _]. apply Hhs. exact (dep_of_in _ _ _ Hq).
  Qed.

  (** A dequeue that reads [tl] and swaps [x <> 0] out of slot [k < tl],
      passing [k] empty slots; its tags are within its own handles. *)
  Lemma deq_prod t h tl k x :
    k < tl -> x <> 0 ->
    exists tr, program_produces_tagged t (Mwhw deq t) tr (Pos.of_nat x) /\
      map untag tr = deq_evs t h tl k x /\
      Forall (fun m : TaggedEvent ERC => forall q, tev_deps m q -> h <= q) tr.
  Proof.
    intros Hk Hx.
    pose proof (run_call_exec t dnext [] (DLd 0) op_ld []
      (fun tl => if Nat.eqb tl 0 then DLd 1 else DXchg 1 tl 0) h tl empty_store eq_refl) as Hc.
    specialize (Hc ltac:(intros [])). cbn beta in Hc.
    assert (Htl : Nat.eqb tl 0 = false) by (apply Nat.eqb_neq; lia).
    rewrite Htl in Hc.
    destruct (scan_exec t tl x Hx k 0 1 [h] [@Build_FutureEntry ERC h (Resolved (E := ERC) op_ld tl)] (S h) h)
      as (tr & H' & Hx' & Hres' & Hm & Hd).
    - lia.
    - reflexivity.
    - intros q [Hq | []]. cbn in Hq. lia.
    - apply all_resolved_cons_resolved. constructor.
    - intros q [Hq | []]. lia.
    - lia.
    - eexists. split; [| split].
      + exists (Build_ProgramConfig (Ret (Pos.of_nat x)) H'). split.
        * exact (pet_app _ _ _ _ _ _ Hc Hx').
        * constructor. exact Hres'.
      + cbn. rewrite Hm. reflexivity.
      + constructor; [| constructor; [intros q [] | exact Hd]].
        intros q [Hq _]. destruct (dep_of_in _ _ _ Hq).
  Qed.

  (** An enqueue of [v] whose [FAA] returns [i]; its store is tagged with
      the [FAA]. *)
  Lemma enq_prod t v h i :
    exists tr, program_produces_tagged t (Mwhw (enq v) t) tr tt /\
      map untag tr = enq_evs t h i v /\
      Forall (fun m : TaggedEvent ERC => forall q, tev_deps m q -> q = h) tr.
  Proof.
    pose proof (run_call_exec t (enext v) [] E0 op_faa [] (fun i => E1 i) h i empty_store eq_refl) as Hc1.
    specialize (Hc1 ltac:(intros [])). cbn beta in Hc1.
    pose proof (run_call_exec t (enext v) [h] (E1 i) (op_store i (Pos.to_nat v)) [0] (fun _ => ED) (S h) tt
      [@Build_FutureEntry ERC h (Resolved (E := ERC) op_faa i)] eq_refl) as Hc2.
    specialize (Hc2 ltac:(intros [Hq | []]; cbn in Hq; lia)). cbn beta in Hc2.
    rewrite (run_done (enext v) _ ED tt eq_refl) in Hc2.
    eexists. split; [| split].
    - eexists. split; [exact (pet_app _ _ _ _ _ _ Hc1 Hc2) |].
      constructor. repeat constructor.
    - reflexivity.
    - repeat constructor.
      + intros q [Hq _]. destruct (dep_of_in _ _ _ Hq).
      + intros q [].
      + intros q [Hq _]. destruct (dep_of_in _ _ _ Hq) as [<- | []]. reflexivity.
      + intros q [].
  Qed.

  (** ** Part 3. What the frontier lets a dequeue overtake

      The (F1)–(F3) constraints ([RelaxedModuleSemantics.must_precede])
      between an older enqueue's [store] and a younger dequeue of the same
      thread.  The dequeue's tags only name its own handles ([deq_prod]),
      so the premise [~ dd hs] holds whenever the dequeue is a later call. *)

  Lemma deq_inv_crosses_store t hs hd s v o (ds dd : handle ERC -> Prop) :
    (o = op_ld \/ exists s', o = op_xchg s' /\ s' <> s) -> ~ dd hs ->
    ~ RelaxedModuleSemantics.must_precede (Build_TaggedEvent (uinv t hs (op_store s v)) ds)
        (Build_TaggedEvent (uinv t hd o) dd) /\
    ~ RelaxedModuleSemantics.must_precede (Build_TaggedEvent (ures t hs (op_store s v) tt) ds)
        (Build_TaggedEvent (uinv t hd o) dd).
  Proof.
    intros Ho Hd. unfold RelaxedModuleSemantics.must_precede; cbn. split; [| exact Hd].
    intros Hn. apply Hn. destruct Ho as [-> | (s' & -> & Hs)]; [apply rc_si_store_ld | apply rc_si_store_xchg; exact Hs].
  Qed.

  Lemma deq_res_crosses_store t hs hd s v o (r : rc_ar o) (ds dd : handle ERC -> Prop) :
    hs <> hd ->
    ~ RelaxedModuleSemantics.must_precede (Build_TaggedEvent (uinv t hs (op_store s v)) ds)
        (Build_TaggedEvent (ures t hd o r) dd) /\
    ~ RelaxedModuleSemantics.must_precede (Build_TaggedEvent (ures t hs (op_store s v) tt) ds)
        (Build_TaggedEvent (ures t hd o r) dd).
  Proof. intros Hne. unfold RelaxedModuleSemantics.must_precede; cbn. split; [exact Hne | intros []]. Qed.

  (** A dequeue's exchange at the slot of an older pending store waits for
      the store's invocation. *)
  Lemma xchg_same_slot_blocked t hs hd s v (ds dd : handle ERC -> Prop) :
    RelaxedModuleSemantics.must_precede (Build_TaggedEvent (uinv t hs (op_store s v)) ds)
      (Build_TaggedEvent (uinv t hd (op_xchg s)) dd).
  Proof. unfold RelaxedModuleSemantics.must_precede; cbn. intros (Hl & _). apply Hl. reflexivity. Qed.

  (** A store's response orders no later invocation of the thread that is
      not tagged with it, whatever its operation (in particular an
      exchange at the store's slot). *)
  Lemma inv_crosses_store_res t hs hd s v o (ds dd : handle ERC -> Prop) :
    ~ dd hs ->
    ~ RelaxedModuleSemantics.must_precede (Build_TaggedEvent (ures t hs (op_store s v) tt) ds)
        (Build_TaggedEvent (uinv t hd o) dd).
  Proof. intros Hd. unfold RelaxedModuleSemantics.must_precede; cbn. exact Hd. Qed.

  (** With a release write part in the exchange (the paper prints
      [atomic-xchg(q + i, null, rel)]), a younger exchange cannot overtake
      an older store. *)
  Lemma store_xchg_rel_ordered s v l x mr : ~ rc_si (op_store s v) (RCXchg l x mr WRel).
  Proof. intros (_ & _ & H). destruct mr; exact H. Qed.

  (** The relation of decision D2 (before D2′): [rc_si] restricted to plain
      reads and writes, so that no RMW takes part. *)
  Definition rc_si_D2 (o1 o2 : RCOp) : Prop := rc_plain o1 /\ rc_plain o2 /\ rc_si o1 o2.

  Lemma store_xchg_D2_ordered s v s' : ~ rc_si_D2 (op_store s v) (op_xchg s').
  Proof. intros (_ & H & _). exact H. Qed.

  (** A [FAA] waits for the invocation of every older call of its thread
      (the per-thread condition of [POQueueR]). *)
  Lemma faa_after_older_inv t h h' o (d d' : handle ERC -> Prop) :
    RelaxedModuleSemantics.must_precede (Build_TaggedEvent (uinv t h o) d) (Build_TaggedEvent (uinv t h' op_faa) d').
  Proof. unfold RelaxedModuleSemantics.must_precede; cbn. apply (proj1 (rc_si_not_before_rel o)). Qed.

  (** ** Part 4. Tactics for module executions over [EI δRC]

      Ports of [RelaxedHoareSL2Prog] Part 5.  [m_here] emits the head of
      the queue; [m_next] crosses one earlier queue event, which [cross_ok]
      justifies: a different thread, or for the same thread none of
      (F1)–(F3).  Hypotheses [untag m = ...] (from [map untag tr = ...])
      compute the tagged events ([untag_rw]); tag facts come from the
      hypotheses [forall q, tev_deps m q -> h <= q] or [... -> q = h] of
      the production lemmas ([unpack_forall]). *)

  Ltac untag_rw := repeat match goal with H : untag ?m = _ |- context [untag ?m] => rewrite H end.

  Ltac untag_rw_in Hx :=
    repeat match goal with H : untag ?m = _ |- _ => match type of Hx with context [untag m] => rewrite H in Hx end end.

  Ltac unpack_forall Hx :=
    repeat match type of Hx with
           | Forall _ (_ :: _) => let D := fresh "D" in apply Forall_cons_iff in Hx as [D Hx]; cbv beta in D
           end.

  (** A WHW pair of [rc_si], after [cbn] has unfolded it. *)
  Ltac si_ok :=
    repeat split; first [ exact Logic.I | discriminate | (let H := fresh in intros H; discriminate H) | lia ].

  Ltac cross_ok :=
    first
      [ left; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn; first [discriminate | assumption | congruence]
      | right; split; [cbn [RelaxedModuleSemantics.ts_event]; untag_rw; reflexivity |];
        unfold RelaxedModuleSemantics.must_precede; cbn [RelaxedModuleSemantics.ts_event]; untag_rw; cbn;
        first
          [ solve [discriminate]
          | solve [let H := fresh in intros H; exact H]
          | solve [let H := fresh in intros H; apply H; si_ok]
          | solve [match goal with Hd : forall q, tev_deps ?m q -> _ <= q |- ~ tev_deps ?m _ =>
                     let H := fresh in intros H; apply Hd in H; lia end]
          | solve [match goal with Hd : forall q, tev_deps ?m q -> q = _ |- ~ tev_deps ?m _ =>
                     let H := fresh in intros H; apply Hd in H; discriminate H end] ] ].

  Ltac m_next := apply RelaxedModuleSemantics.tagged_select_next; [cross_ok |].
  Ltac m_here := apply RelaxedModuleSemantics.tagged_select_here.

  (** [ei_inv]: an [EI δRC] invocation step (writes first, then reads and
      RMWs); [ei_res pre]: a response step whose record is after the
      records [pre]. *)
  Ltac ei_inv :=
    cbn; untag_rw; cbn;
    first [ exists tt; eexists; split; reflexivity
          | eexists _, _; split; [split; reflexivity | reflexivity] ].
  Ltac ei_res pre := cbn; untag_rw; cbn; exists pre; eexists; split; reflexivity.

  Ltac m_step k m sel lts :=
    eapply RelaxedModuleSemantics.tagged_module_execution_cons;
    [ apply RelaxedModuleSemantics.tagged_underlay with
        (candidate := @RelaxedModuleSemantics.Build_TaggedScheduledEvent _ _ k m);
      [ cbn; sel | lts ]
    | ].

  Ltac m_finish :=
    first [ apply RelaxedModuleSemantics.finish_here
          | eapply RelaxedModuleSemantics.finish_next; [ | m_finish ]; discriminate ].

  Ltac m_return o :=
    eapply RelaxedModuleSemantics.tagged_module_execution_cons;
    [ eapply RelaxedModuleSemantics.tagged_return with (op := o);
      [ m_finish
      | cbn; intros Hin; repeat (destruct Hin as [Hin | Hin]; [discriminate Hin |]); exact Hin ]
    | ].

  (** Freshness side conditions of an overlay invocation. *)
  Ltac call_fresh_ok :=
    cbn; let Hin := fresh "Hin" in intros Hin; repeat (destruct Hin as [Hin | Hin]; [discriminate Hin |]); exact Hin.

  Ltac trace_fresh_ok Hm :=
    rewrite Hm; split;
    [ cbn; repeat constructor; cbn; intuition discriminate
    | let key := fresh "key" in let Hk := fresh "Hk" in let Hu := fresh "Hu" in
      intros key Hk Hu; untag_rw_in Hu; cbn in Hk, Hu;
      repeat (destruct Hk as [<- | Hk]; [repeat (destruct Hu as [Hu | Hu]; [discriminate Hu |]); exact Hu |]);
      exact Hk ].

End WHWQProg.
