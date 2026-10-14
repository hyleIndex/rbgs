(** * SeqLockLB: concurrent module executions of SeqLock ⊎ COH[z]

    So far [SeqLockModule.seqlock_module_rel_lin] and the module-level
    client theorems of [SeqLockClients] were instantiated only on one
    [write] by one thread over an underlay whose [Step] is [True]
    ([SeqLockModuleExample]).  This file builds two concrete complete
    executions of the module [SeqLockProg.M rc plainTL], for every [rc].
    Each has two threads, overlapping calls inside each thread, and a
    [read()] response.  The file instantiates those theorems on them.
    These instances show that the hypotheses are jointly satisfiable;
    their client conclusions are sanity instances, true by construction
    of the executions.  The discriminating counterpart is a third
    execution, [T_bad] (Part 9): the underlay LTS [VEa] used here admits
    it, its underlay part is not relaxed linearizable, and over it the
    SeqLock violates message passing.  So the underlay hypothesis of the
    module theorem is load-bearing, and [VEa] does not discharge it.

    [T_lb] (Part 7): load buffering through SeqLock ⊎ COH[z].
<<
      A (thread 1):  zr() = 1        ;  write(1,1)
      B (thread 2):  read() = (1,1)  ;  zw(1)
>>
    - Overlay events, by position.  A invokes [zr()] (0) and
      [write(1,1)] (2).  B invokes [read()] (15) and [zw(1)] (28).  Then
      [write], [read] and [zw] respond (31, 32, 33), and [zr] responds last
      (35).  All four invocations precede all four responses.  In each
      thread the second call is invoked before the first one responds.
      A's [write(1,1)] and B's [read()] overlap: B's read is invoked (15)
      while the write is pending, and the write responds (31) just before
      the read responds (1,1) (32).  The overlap is at the overlay only:
      all twelve underlay events of the write precede those of the read.
    - Underlay events.  A's [z.rd()] is invoked first (1).  Its response,
      1, is the last underlay event (34).  In between come A's six write
      calls, B's six read calls (ticket 2, x = y = 1, no retry) and B's
      [z := 1].
    - Results.
      - [lb_execution]: the execution is complete ([tm_queue c = []],
        every call [DeadCall]), over [VEa] from [SeqLockCOH.init].
      - [lb_underlay_rel_lin]: the underlay part is relaxed linearizable
        w.r.t. [BL.nuE_all ... (SeqLockModule.nuEc rc plainTL)], with the
        explicit witness [W_lb] adapted from [SeqLockCOH.lb_wit]: A's
        write calls, B's read calls, B's [z := 1], A's [z.rd() = 1].
      - [seqlock_lb_module]: the overlay part is relaxed linearizable
        under [findep rc], by [seqlock_module_rel_lin].
      - [lb_refuted]: every semi-independence that keeps the pairs
        ([zr()], [write(1,1)]) and ([read()], [zw(1)]) rejects the overlay
        part.  Instances:
        - [seqlock_lb_not_classical]: the empty relation, i.e. rejection
          under I = ∅, where [rhb] is real time ∪ per-thread invocation
          order.  [T_lb] has two pending calls per thread, so it is not a
          Herlihy--Wing history, and no identity with Herlihy--Wing
          linearizability is claimed (prop:sanity-check is not
          mechanized);
        - [seqlock_lb_refutes]: the relation [cf_indep rc cf] induced by
          any category assignment [cf] of blocks whose [dto] orders both
          pairs;
        - [seqlock_lb_paper_signature], [seqlock_lb_paper_modes]: in
          particular [SeqLockCOH.paper_cf] and [paper_cf_modes];
        - [seqlock_lb_paper_tensor]: the paper's own rule
          [RelaxedSig.Tens.tensor_semi_independent] for a SeqLock
          signature with [[rd ↦ rfence][wrt ↦ lfence]] (trace.tex:395) and
          a COH[z] signature with any modes and semi-independence.
        [findep_sl_cf] shows that [findep] is [cf_indep sl_cf].  These
        are [SeqLockCOH.lb_allowed], [lb_refutes] and
        [paper_signature_fails] at module level.
      - The client theorems hold on [T_lb]: [lb_client_same_epoch],
        [lb_client_equal_pairs] (every [write] invocation is diagonal,
        [lb_writes_diag]) and [lb_client_read_not_future_po].  These are
        sanity instances; their conclusions can also be read off the
        execution directly.
      - [seqlock_lb_nonvacuous] packages these facts in one statement.
      - Part 10, [lb_underlay_not_classical]: the underlay part of [T_lb]
        is memory-level load buffering on the registers z and x
        (A: [z.rd() = 1] … [x.wrt(1)]; B: [x.rd() = 1] … [z.wrt(1)]).  It
        is rejected under the empty underlay semi-independence, while
        [lb_underlay_rel_lin] accepts it under the underlay one.  So the
        same execution shows load buffering at both levels, and the
        overtaking of intro.tex:74 ("a later invocation may be issued
        while the read is still pending") is what makes it possible.

    [T_mp] (Part 8): message passing, with the allowed outcome.
<<
      A:  zw(1)           ;  write(1,1)    (write invoked before zw responds)
      B:  read() = (1,1)  ;  zr() = 1      (zr invoked before read responds)
>>
    - The overlay projection of [T_mp] is exactly
      [SeqLockClients.mp_trace rc 1] (SeqLockClients Part 5), with the
      same keys and order ([mp_overlay_projection]).
    - At the underlay, the response of A's [z := 1] is emitted after the
      twelve underlay events of [write(1,1)].
    - Results: [mp_execution], [mp_underlay_rel_lin] (witness [W_mp]),
      [seqlock_mp_module], [mp_client_order] (from
      [seqlock_client_mp_order]), [mp_client_zr_value] (from
      [seqlock_client_mp_zr_value]), and the package
      [seqlock_mp_nonvacuous].  As for [T_lb], the client conclusions
      are sanity instances ([zr()] returns 1 by construction).

    [T_bad] (Part 9): [T_mp] with [zr() = 0].  The response of A's
    [z := 1] is delayed past every other underlay event, so in [VEa] B's
    [z.rd()] returns 0.
    - [bad_execution]: a complete execution over [VEa] from
      [SeqLockCOH.init]; every underlay return value passes [VEa].
    - [bad_underlay_not_rel_lin]: its underlay part is not relaxed
      linearizable (contraposition of [seqlock_client_mp_zr_value]), so
      the module theorem does not apply to it.
    - [bad_overlay_not_rel_lin]: its overlay part is not relaxed
      linearizable under [findep] either (from the interface rule
      [client_rule_mp_zr_value]).  Over [VEa], SeqLock ⊎ COH[z] violates
      message passing.

    How the overlaps arise in [RelaxedModuleSemantics]:
    - [tagged_invoke] (:581) needs only [call_fresh] of the overlay key,
      so a thread may invoke a call while an earlier call of the thread is
      active.  It runs the whole method body when the call is invoked
      ([program_produces_tagged]), so the underlay return values and the
      overlay return value are chosen then.  [VE] checks each underlay
      event only when the event is emitted ([tagged_underlay], :594).
      [trace_fresh] (:201) makes underlay keys globally fresh, so the two
      calls of one thread use disjoint underlay handles (A: 0 and 1..6;
      B: 0..5 and 6).
    - Underlay events are emitted from the dependency frontier
      ([must_precede], [tagged_can_cross], F1--F3, :207--265).  For two
      events of one thread, (F3) orders a response before a later
      invocation only if the invocation's tag contains the response's
      handle.  In [SeqLockProg] every invocation is an untagged [Future],
      whose tag is the set of handles resolved in its own method's future
      store.  The stores are per method.  So A's write invocations are
      tagged with handles among 1..6 only and may overtake the pending
      response of A's [z.rd()] (handle 0).  (F1) and (F2) do not apply to
      these crossings ([cross] checks each one).  In [T_mp] the same holds
      for [write(1,1)] and the pending response of A's [z := 1].
    - [tagged_return] (:603) needs only [owner_done_tagged] for the
      returning call.  So an overlay response may be delayed past later
      invocations of its thread.
    - [rhb] does not keep the overlapping overlay pairs ([zr()],
      [write]) and ([read()], [zw]), because they are semi-independent
      ([SeqLockClients.zr_write_independent], [read_zw_independent]).  At
      the underlay, A's [z.rd()] is semi-independent of A's write calls:
      [SeqLockCOH.upres rc plainTL (RdZ _) c = false] for [c] among
      [Acq], [WmbC], [WrX], [WrY], [Rel] (checked inside [rhb_check]).  So
      [W_lb] may place it last.

    Underlay LTS.  [VEa] (Part 2) runs the abstract underlay
    [TL ⊗ X ⊗ Y ⊗ B ⊗ Z] of [SeqLockCOH] with each call taking effect
    atomically at its response: a response is enabled iff
    [SeqLockCOH.pre] accepts it in the current state, and
    [SeqLockCOH.post] is then applied, from [SeqLockCOH.init].
    - What it does: it checks every underlay return value, in response
      order, against the specification that [SeqLockModule.nuEc] uses.
      So none of the executions relies on [Step := True] ([VE0] is not
      used).
    - What it does not do: it does not implement ν_E.  Barrier calls
      ([wmb]/[rmb]) are no-ops in it.  Nothing orders the effect of a call
      before a later call of the same thread made by another method call:
      the frontier keeps the order of same-thread invocations that are not
      semi-independent (F2), but it lets a response be delayed past later
      invocations of other calls of its thread (per-method future stores,
      so (F3) never applies across calls), and [VEa] applies a call only
      at its response.  It therefore admits executions to which the module
      theorem does not apply, and over it the SeqLock violates message
      passing ([T_bad], Part 9: A's [z := 1] is invoked before A's first
      [wmb], but takes effect after B has read z).
    - Consequently [VEa] adds no logical strength.  The module theorem is
      uniform in [VE]; its substantive underlay hypothesis, [rel_lin] of
      the underlay part, is discharged per execution, by an explicit
      witness: [W_lb] for [T_lb], [W_mp] for [T_mp].  [W_lb] is the order
      of the underlay responses of [T_lb].  [W_mp] is not the response
      order of [T_mp]: it must put A's [z := 1] before A's first [wmb]
      (same-thread clause of [rhb], [dto DW Wmb]), although that response
      comes later.  For [T_bad] no witness exists.
    - Which operational underlay should stand for COH (a [VE] that
      implements ν_E, or a memory model of [memory/]) is open.

    Checking.  The conditions of an underlay witness other than the
    specification are decided by three boolean checks ([nodup_check],
    [all_check], [rhb_check], Part 4).  Each has a soundness lemma, and
    each is closed by [reflexivity], i.e. kernel conversion.  [upres_rc]:
    for [plainTL] the underlay order does not depend on [rc].  No
    [vm_compute] or [native_compute] is used.

    Not shown here.
    - Generality.  These are two executions.  There is no general theorem
      that the module admits load buffering, for instance for every
      execution of that shape or over every [VE].
    - Complete executions only, as in the module theorem.
    - The memory.  The underlay is the abstract specification executed
      at the responses ([VEa]), not a memory model of [memory/] (task
      SL-mem).  [VEa] checks return values in response order only; its
      barriers are no-ops and it does not order the effect of a call
      before later calls of the same thread, so it is neither ν_E nor
      COH, and over it the SeqLock is incorrect ([T_bad]).
      Every positive result here is relative to the abstract
      specification ν_E, through the per-execution witnesses; none is a
      statement about an operational memory.  The weak behaviour of [T_lb]
      comes from the order in which the module semantics emits
      invocations and responses, together with the underlay and overlay
      semi-independence.
    - Return values are chosen when a call is invoked, by the module
      semantics, and [VEa] checks them only when they are emitted.
    - Optional item (c) of the task is not built: a thread that invokes
      [read()] and then [write(a,b)] before the read responds.  In such an
      execution the read cannot return the thread's own later write, so
      the same-thread clause of [seqlock_client_read_not_future_po] would
      hold only vacuously there.  On [T_lb] that clause is vacuous too,
      because the write that B's read observes belongs to A.
    - For [T_mp], only the equality of the overlay projection with
      [mp_trace 1] is shown.  No general lemma transfers [rel_lin] between
      the overlay part of a module trace and its projection.
    - Out-of-thin-air.  [SeqLockProg] issues only untagged futures, so no
      execution here involves a dependency.  The second half of
      intro.tex:110 ("dependency-forced OOTA behaviors remain rejected")
      is not addressed.
    - The SeqLock is the COH barrier variant of [SeqLockCOH] (rmb/wmb),
      not the paper's SeqLock over TSO cells. *)
From Stdlib Require Import List Bool Arith.PeanoNat PArith micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedModuleFacts.
Require Import examples.Relaxed.BracketedLink.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.SeqLockProg.
Require Import examples.Relaxed.SeqLockModule.
Require Import examples.Relaxed.SeqLockClients.

Import ListNotations.

Module SeqLockLB.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import SeqLockProg.SeqLockProg.

  Module BL := BracketedLink.BracketedLink.
  Module SLM := SeqLockModule.SeqLockModule.
  Module SLC := SeqLockClients.SeqLockClients.

  (** ** Part 1: positions of invocations and responses in a trace *)

  Section Positions.
    Context {G : RelaxedSig.t} {X : Type} (sel : X -> option (ThreadEvent G)).

    (** The invocations of [L] with their positions, keys and operations,
        and the responses with their positions and keys. *)
    Fixpoint invs_from (n : nat) (L : list X) : list (nat * CallKey G * Sig.op (effect G)) :=
      match L with
      | [] => []
      | x :: L' =>
          match sel x with
          | Some ev =>
              match te_ev G ev with
              | InvEv h op => (n, (te_tid G ev, h), op) :: invs_from (S n) L'
              | ResEv _ _ _ => invs_from (S n) L'
              end
          | None => invs_from (S n) L'
          end
      end.

    Fixpoint ress_from (n : nat) (L : list X) : list (nat * CallKey G) :=
      match L with
      | [] => []
      | x :: L' =>
          match sel x with
          | Some ev =>
              match te_ev G ev with
              | ResEv h _ _ => (n, (te_tid G ev, h)) :: ress_from (S n) L'
              | InvEv _ _ => ress_from (S n) L'
              end
          | None => ress_from (S n) L'
          end
      end.

    Lemma invs_from_tail n x L p : In p (invs_from (S n) L) -> In p (invs_from n (x :: L)).
    Proof.
      intros Hp. cbn. destruct (sel x) as [ev |]; [| exact Hp].
      destruct (te_ev G ev); [right |]; exact Hp.
    Qed.

    Lemma ress_from_tail n x L p : In p (ress_from (S n) L) -> In p (ress_from n (x :: L)).
    Proof.
      intros Hp. cbn. destruct (sel x) as [ev |]; [| exact Hp].
      destruct (te_ev G ev); [| right]; exact Hp.
    Qed.

    Lemma inv_at_invs L : forall n i k op, inv_at sel L i k op -> In (n + i, k, op) (invs_from n L).
    Proof.
      induction L as [| x L IH]; intros n i k op (y & Hy & Hs); [destruct i; discriminate |].
      destruct i as [| i].
      - cbn in Hy. injection Hy as <-. cbn. rewrite Hs. cbn. left.
        destruct k as [t h]. rewrite Nat.add_0_r. reflexivity.
      - apply invs_from_tail. replace (n + S i) with (S n + i) by lia.
        apply IH. exists y. split; [exact Hy | exact Hs].
    Qed.

    Lemma res_at_ress L : forall n j k op ret, res_at sel L j k op ret -> In (n + j, k) (ress_from n L).
    Proof.
      induction L as [| x L IH]; intros n j k op ret (y & Hy & Hs); [destruct j; discriminate |].
      destruct j as [| j].
      - cbn in Hy. injection Hy as <-. cbn. rewrite Hs. cbn. left.
        destruct k as [t h]. rewrite Nat.add_0_r. reflexivity.
      - apply ress_from_tail. replace (n + S j) with (S n + j) by lia.
        apply (IH (S n) j k op ret). exists y. split; [exact Hy | exact Hs].
    Qed.

    (** Responses with a function [f] of their operation and value. *)
    Fixpoint ressv_from {B : Type} (f : forall op : Sig.op (effect G), Sig.ar op -> B) (n : nat) (L : list X) :
        list (nat * CallKey G * B) :=
      match L with
      | [] => []
      | x :: L' =>
          match sel x with
          | Some ev =>
              match te_ev G ev with
              | ResEv h op ret => (n, (te_tid G ev, h), f op ret) :: ressv_from f (S n) L'
              | InvEv _ _ => ressv_from f (S n) L'
              end
          | None => ressv_from f (S n) L'
          end
      end.

    Lemma res_at_ressv {B : Type} (f : forall op : Sig.op (effect G), Sig.ar op -> B) L :
      forall n j k op ret, res_at sel L j k op ret -> In (n + j, k, f op ret) (ressv_from f n L).
    Proof.
      induction L as [| x L IH]; intros n j k op ret (y & Hy & Hs); [destruct j; discriminate |].
      destruct j as [| j].
      - cbn in Hy. injection Hy as <-. cbn. rewrite Hs. cbn. left.
        destruct k as [t h]. rewrite Nat.add_0_r. reflexivity.
      - cbn. replace (n + S j) with (S n + j) by lia.
        assert (H : In (S n + j, k, f op ret) (ressv_from f (S n) L)).
        { apply (IH (S n) j k op ret). exists y. split; [exact Hy | exact Hs]. }
        destruct (sel x) as [ev |]; [destruct (te_ev G ev); [| right] |]; exact H.
    Qed.

    Lemma inv_at_pos L i k op : inv_at sel L i k op -> In (i, k, op) (invs_from 0 L).
    Proof. exact (inv_at_invs L 0 i k op). Qed.

    Lemma res_at_pos L j k op ret : res_at sel L j k op ret -> In (j, k) (ress_from 0 L).
    Proof. exact (res_at_ress L 0 j k op ret). Qed.
  End Positions.

  (** ** Part 2: the underlay LTS

      [VEa]: the abstract underlay [TL ⊗ X ⊗ Y ⊗ B ⊗ Z] of [SeqLockCOH]
      executed atomically at the responses.  An invocation does not change
      the state; a response [r] of call [c] by thread [t] is enabled iff
      [SeqLockCOH.pre] accepts [c] with return value [r] in the current
      state, and then applies [SeqLockCOH.post].  So [VEa] checks every
      underlay return value, in response order, against the sequential
      specification that [SeqLockModule.nuEc] uses.  It does not
      implement ν_E: barriers are no-ops, a call takes effect only at its
      response (which the module semantics may delay past later calls of
      the same thread), and it admits executions whose underlay part is
      not relaxed linearizable ([T_bad], Part 9). *)

  Section Underlay.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).

    Definition aev (ev : ThreadEvent G) : option SL.Ev :=
      match te_ev G ev with
      | InvEv _ _ => None
      | ResEv _ o v => Some (SL.mkEv (Pos.to_nat (te_tid G ev)) 0 (uc_of o v))
      end.

    Definition astep (ev : ThreadEvent G) (s s' : SL.State) : Prop :=
      match aev ev with
      | None => s' = s
      | Some e => SL.pre s e = true /\ s' = SL.post s e
      end.

    Definition VEa : LTS G := {| State := SL.State; Step := astep; Error := fun _ _ => False |}.
  End Underlay.

  (** ** Part 3: method runs *)

  (** The two threads. *)
  Local Abbreviation tA := 1%positive (only parsing).
  Local Abbreviation tB := 2%positive (only parsing).

  Section Runs.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).

    Definition ivt (t : tid) (h : nat) (o : SOp) (H : FutureStore G) : TaggedEvent G :=
      Build_TaggedEvent (Build_ThreadEvent t (@InvEv G h o)) (resolved_in H).
    Definition rst (t : tid) (h : nat) (o : SOp) (v : @Sig.ar (effect G) o) : TaggedEvent G :=
      Build_TaggedEvent (Build_ThreadEvent t (@ResEv G h o v)) no_deps.
    Definition rv (h : nat) (o : SOp) (v : @Sig.ar (effect G) o) : FutureEntry G :=
      Build_FutureEntry (E := G) h (Resolved (E := G) o v).

    (** A one-call method on handle [h] ([zr()] or [zw(v)]). *)
    Definition one_tr (t : tid) (h : nat) (o : SOp) (v : @Sig.ar (effect G) o) : list (TaggedEvent G) :=
      [ivt t h o []; rst t h o v].

    (** [write(vx,vy)] on handles [b+1 .. b+6].  In the method's own
        trace each call is answered right after it is issued; the module
        semantics may still emit these events later and interleaved with
        other calls' events. *)
    Definition wst (b : nat) (vx vy : nat) (n : nat) : FutureStore G :=
      skipn (5 - n)
        [rv (b + 5) sWmb tt; rv (b + 4) (sWrY vy) tt; rv (b + 3) (sWrX vx) tt;
         rv (b + 2) sWmb tt; rv (b + 1) sAcq tt].

    Definition wr_tr (t : tid) (b vx vy : nat) : list (TaggedEvent G) :=
      [ivt t (b + 1) sAcq []; rst t (b + 1) sAcq tt;
       ivt t (b + 2) sWmb (wst b vx vy 1); rst t (b + 2) sWmb tt;
       ivt t (b + 3) (sWrX vx) (wst b vx vy 2); rst t (b + 3) (sWrX vx) tt;
       ivt t (b + 4) (sWrY vy) (wst b vx vy 3); rst t (b + 4) (sWrY vy) tt;
       ivt t (b + 5) sWmb (wst b vx vy 4); rst t (b + 5) sWmb tt;
       ivt t (b + 6) sRel (wst b vx vy 5); rst t (b + 6) sRel tt].

    (** One successful iteration of [read()] on handles [0 .. 5], with
        ticket [s] and values [a], [b]. *)
    Definition rst_ (s a b : nat) (n : nat) : FutureStore G :=
      skipn (5 - n)
        [rv 4 sRmb tt; rv 3 sRdY b; rv 2 sRdX a; rv 1 sRmb tt; rv 0 sGt s].

    Definition rd_tr (t : tid) (s a b : nat) : list (TaggedEvent G) :=
      [ivt t 0 sGt []; rst t 0 sGt s;
       ivt t 1 sRmb (rst_ s a b 1); rst t 1 sRmb tt;
       ivt t 2 sRdX (rst_ s a b 2); rst t 2 sRdX a;
       ivt t 3 sRdY (rst_ s a b 3); rst t 3 sRdY b;
       ivt t 4 sRmb (rst_ s a b 4); rst t 4 sRmb tt;
       ivt t 5 (sTt s) (rst_ s a b 5); rst t 5 (sTt s) false].

    Lemma zr_produces t h v : program_produces_tagged t (M rc SL.plainTL fZr t) (one_tr t h sRdZ v) v.
    Proof.
      eexists. split.
      - cbn [M]. unfold zread, initial_program, one_tr.
        eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; tauto |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
        apply tagged_execution_refl.
      - constructor. repeat constructor.
    Qed.

    Lemma zw_produces t h v : program_produces_tagged t (M rc SL.plainTL (fZw v) t) (one_tr t h (sWrZ v) tt) tt.
    Proof.
      eexists. split.
      - cbn [M]. unfold zwrite, initial_program, one_tr.
        eapply tagged_execution_emit; [apply tagged_future; unfold handle_fresh; cbn; tauto |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
        apply tagged_execution_refl.
      - constructor. repeat constructor.
    Qed.

    Ltac fresh_h := unfold handle_fresh; cbn; intros Hin; repeat (destruct Hin as [Hin | Hin]); try lia; exact Hin.

    Lemma wr_produces t b vx vy :
      program_produces_tagged t (M rc SL.plainTL (fWrite vx vy) t) (wr_tr t b vx vy) tt.
    Proof.
      eexists. split.
      - cbn [M]. unfold write, initial_program, wr_tr.
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        do 5 (eapply tagged_execution_silent; [apply tagged_wait_resolved; cbn; tauto | cbn beta]).
        apply tagged_execution_refl.
      - constructor. repeat constructor.
    Qed.

    Lemma rd_produces t s a b :
      program_produces_tagged t (M rc SL.plainTL fRead t) (rd_tr t s a b) (a, b).
    Proof.
      eexists. split.
      - cbn [M]. unfold initial_program. rewrite (read_unfold rc SL.plainTL). unfold read_body, rd_tr.
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_resolve; apply resolve_here |].
        eapply tagged_execution_emit; [apply tagged_future; fresh_h |]. cbn beta.
        eapply tagged_execution_emit; [eapply tagged_wait_pending; apply resolve_here |]. cbn beta.
        do 4 (eapply tagged_execution_silent;
              [eapply tagged_wait_resolved; cbn; repeat first [left; reflexivity | right] | cbn beta]).
        cbn iota. apply tagged_execution_refl.
      - constructor. repeat constructor.
    Qed.
  End Runs.

  (** ** Part 4: deciding the conditions of an underlay witness

      For the underlay [E rc plainTL], the conditions of
      [rel_lin_witness] other than the specification are decided by
      boolean checks over the positions computed by [invs_from] and
      [ress_from].  [rhb_check W] says: for every two operations at
      positions [p], [p'] of [W], if the trace orders them by [rhb] (a
      response before an invocation, or two invocations of one thread
      whose calls [SeqLockCOH.upres] orders), then [p < p']. *)

  (** For [plainTL] the underlay order [upres] does not depend on [rc]:
      no TicketLock, cell or barrier category has the release flag. *)
  Lemma upres_rc rc o o' :
    SL.upres rc SL.plainTL (uc_of o (dflt o)) (uc_of o' (dflt o')) =
    SL.upres false SL.plainTL (uc_of o (dflt o)) (uc_of o' (dflt o')).
  Proof. destruct rc; [| reflexivity]. destruct o, o'; reflexivity. Qed.

  Section Checks.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).

    Definition keqb (k k' : CallKey G) : bool := if SLM.keyE_dec rc SL.plainTL k k' then true else false.

    Lemma keqb_eq k k' : keqb k k' = true -> k = k'.
    Proof. unfold keqb. destruct (SLM.keyE_dec rc SL.plainTL k k'); congruence. Qed.

    Lemma keqb_refl k : keqb k k = true.
    Proof. unfold keqb. destruct (SLM.keyE_dec rc SL.plainTL k k); congruence. Qed.

    Definition upb (o o' : SOp) : bool := SL.upres false SL.plainTL (uc_of o (dflt o)) (uc_of o' (dflt o')).

    (** Some invocation (resp. response) of [k] precedes some invocation
        of [k']. *)
    Definition ii_lt (il : list (nat * CallKey G * SOp)) (k k' : CallKey G) : bool :=
      existsb (fun a => keqb (snd (fst a)) k &&
        existsb (fun b => keqb (snd (fst b)) k' && Nat.ltb (fst (fst a)) (fst (fst b))) il) il.
    Definition ri_lt (il : list (nat * CallKey G * SOp)) (rl : list (nat * CallKey G)) (k k' : CallKey G) : bool :=
      existsb (fun a => keqb (snd a) k &&
        existsb (fun b => keqb (snd (fst b)) k' && Nat.ltb (fst a) (fst (fst b))) il) rl.

    Definition rhb_check (il : list (nat * CallKey G * SOp)) (rl : list (nat * CallKey G)) (W : list (Op G)) : bool :=
      forallb (fun p => forallb (fun p' =>
        match nth_error W p, nth_error W p' with
        | Some o, Some o' =>
            implb (ri_lt il rl (op_key o) (op_key o') ||
                   (Pos.eqb (fst (op_key o)) (fst (op_key o')) && upb (op_op o) (op_op o') &&
                    ii_lt il (op_key o) (op_key o')))
                  (Nat.ltb p p')
        | _, _ => true
        end) (seq 0 (length W))) (seq 0 (length W)).

    Definition all_check (il : list (nat * CallKey G * SOp)) (W : list (Op G)) : bool :=
      forallb (fun a => existsb (fun o => keqb (op_key o) (snd (fst a))) W) il.

    Lemma nth_error_seq {A} (W : list A) p a : nth_error W p = Some a -> In p (seq 0 (length W)).
    Proof.
      intros Hp. apply in_seq. split; [lia |]. cbn. apply nth_error_Some. congruence.
    Qed.

    Section Sound.
      Context {X : Type} (sel : X -> option (ThreadEvent G)) (L : list X).

      Lemma rhb_check_sound W :
        rhb_check (invs_from sel 0 L) (ress_from sel 0 L) W = true ->
        forall o o', In o W -> In o' W -> rhb sel L (semi_independent G) o o' -> before W o o'.
      Proof.
        intros Hc o o' Ho Ho' Hr.
        destruct (In_nth_error W o Ho) as (p & Hp).
        destruct (In_nth_error W o' Ho') as (p' & Hp').
        unfold rhb_check in Hc. rewrite forallb_forall in Hc.
        specialize (Hc p (nth_error_seq W p o Hp)). rewrite forallb_forall in Hc.
        specialize (Hc p' (nth_error_seq W p' o' Hp')). rewrite Hp, Hp' in Hc.
        apply (BL.nth_before W p p' o o' Hp Hp'). apply Nat.ltb_lt.
        destruct (Nat.ltb p p'); [reflexivity |]. exfalso.
        rewrite implb_false_r, negb_true_iff, orb_false_iff in Hc. destruct Hc as [Hc1 Hc2].
        destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        - apply res_at_pos in Hi. apply inv_at_pos in Hj.
          assert (H : ri_lt (invs_from sel 0 L) (ress_from sel 0 L) (op_key o) (op_key o') = true).
          { apply existsb_exists. exists (i, op_key o). split; [exact Hi |].
            rewrite keqb_refl. cbn. apply existsb_exists. exists (j, op_key o', op_op o'). split; [exact Hj |].
            rewrite keqb_refl. cbn. apply Nat.ltb_lt. exact Hij. }
          congruence.
        - apply inv_at_pos in Hi. apply inv_at_pos in Hj.
          assert (Hu : upb (op_op o) (op_op o') = true).
          { unfold upb. rewrite <- (upres_rc rc). apply not_false_iff_true. exact Hn. }
          assert (H : ii_lt (invs_from sel 0 L) (op_key o) (op_key o') = true).
          { apply existsb_exists. exists (i, op_key o, op_op o). split; [exact Hi |].
            rewrite keqb_refl. cbn. apply existsb_exists. exists (j, op_key o', op_op o'). split; [exact Hj |].
            rewrite keqb_refl. cbn. apply Nat.ltb_lt. exact Hij. }
          rewrite Ht, Pos.eqb_refl, Hu, H in Hc2. discriminate Hc2.
      Qed.

      Lemma all_check_sound W :
        all_check (invs_from sel 0 L) W = true ->
        forall i k op, inv_at sel L i k op -> exists o, In o W /\ op_key o = k.
      Proof.
        intros Hc i k op Hi. apply inv_at_pos in Hi.
        unfold all_check in Hc. rewrite forallb_forall in Hc.
        apply Hc, existsb_exists in Hi as (o & Ho & E). cbn in E.
        exists o. split; [exact Ho | exact (keqb_eq _ _ E)].
      Qed.
    End Sound.

    Lemma nodup_check (W : list (Op G)) : SL.nodupb keqb (map op_key W) = true -> NoDup (map op_key W).
    Proof. apply (SL.nodupb_spec keqb keqb_eq). exact keqb_refl. Qed.
  End Checks.

  (** Register facts for the underlay specification [SeqLockModule.nuEc]:
      a read of [x] (resp. [z]) that does not return the current value
      follows a write of the value it returns. *)
  Lemma replay_rdx_src l1 : forall s e l2 v,
    SLM.replay s (l1 ++ e :: l2) -> SL.call e = SL.RdX v ->
    v = SL.sx s \/ exists e', In e' l1 /\ SL.call e' = SL.WrX v.
  Proof.
    induction l1 as [| e0 l1 IH]; intros s e l2 v H He; cbn in H.
    - destruct H as [Hp _]. unfold SL.pre in Hp. rewrite He in Hp. left. symmetry. apply Nat.eqb_eq, Hp.
    - destruct H as [_ H]. destruct (IH _ _ _ _ H He) as [E | (e' & Hin & Ee)].
      + rewrite SL.sx_post in E. destruct (SL.call e0) eqn:Ec; cbn in E; try (left; exact E).
        subst v. right. exists e0. split; [left; reflexivity | exact Ec].
      + right. exists e'. split; [right; exact Hin | exact Ee].
  Qed.

  Lemma zreg_rd_src l1 : forall cur c l2 v,
    SLM.zreg cur (l1 ++ c :: l2) -> c = SL.RdZ v -> v = cur \/ In (SL.WrZ v) l1.
  Proof.
    induction l1 as [| c0 l1 IH]; intros cur c l2 v H Hc; cbn in H.
    - subst c. left. exact (proj1 H).
    - destruct c0; try (destruct (IH _ _ _ _ H Hc) as [E | Hin]; [left; exact E | right; right; exact Hin]).
      + destruct (IH _ _ _ _ H Hc) as [E | Hin]; [subst; right; left; reflexivity | right; right; exact Hin].
      + destruct (IH _ _ _ _ (proj2 H) Hc) as [E | Hin]; [left; exact E | right; right; exact Hin].
  Qed.

  (** Find the position of an event: the goal is [exists i, inv_at ...]
      or [exists j, res_at ...] on a concrete trace. *)
  Ltac find_pos :=
    let rec go n :=
      first [ exists n; eexists; split; reflexivity
            | lazymatch n with 60 => fail 1 | _ => go (S n) end ] in
    go 0.

  (** ** Part 5: scheduling tactics for module executions *)

  (** Freshness side conditions of [tagged_invoke]. *)
  Ltac cfresh := unfold call_fresh; cbn; solve [intuition discriminate].
  Ltac tfresh :=
    split; [cbn; repeat constructor; cbn; solve [intuition discriminate]
           | intros key Hk Hu; cbn in Hk, Hu; solve [intuition congruence]].

  (** Overlay invocation of a method whose run is [prod]. *)
  Ltac oinv prod :=
    eapply tagged_module_execution_cons;
    [ eapply tagged_invoke; [cfresh | exact prod | tfresh] | ];
    cbn [app schedule_trace_tagged map one_tr wr_tr rd_tr].

  (** Overlay return. *)
  Ltac fin := repeat first [ apply finish_here | apply finish_next; [intros Efin; discriminate Efin |] ].
  Ltac oret :=
    eapply tagged_module_execution_cons;
    [ eapply tagged_return; [fin | unfold owner_done_tagged; cbn; solve [intuition discriminate]] | ].

  (** A step of [VEa]: an invocation keeps the state, a response is
      checked by [SeqLockCOH.pre]. *)
  Ltac astep_tac := cbn [VEa Step]; unfold astep, aev; cbn;
    first [reflexivity | split; [reflexivity | reflexivity]].

  (** Crossing an earlier queued event (F1--F3 do not apply). *)
  Ltac cross :=
    first [ left; cbn; discriminate
          | right; split; [reflexivity |];
            cbn; unfold resolved_in, resolved_at;
            first [ solve [intros (op0 & ret0 & Hin0); cbn in Hin0; intuition discriminate]
                  | solve [intros []] ] ].

  (** Emit the first, resp. second, queued underlay event. *)
  Ltac uhere :=
    lazymatch goal with
    | |- module_execution_tagged _ _ (Build_TaggedModuleConfig _ _ (?m :: _) _) _ _ =>
        eapply tagged_module_execution_cons;
        [ eapply tagged_underlay with (candidate := m); [apply tagged_select_here | astep_tac] | ]
    end.
  Ltac usecond :=
    lazymatch goal with
    | |- module_execution_tagged _ _ (Build_TaggedModuleConfig _ _ (_ :: ?m :: _) _) _ _ =>
        eapply tagged_module_execution_cons;
        [ eapply tagged_underlay with (candidate := m);
          [apply tagged_select_next; [cross | apply tagged_select_here] | astep_tac] | ]
    end.

  (** ** Part 6: overlay facts *)

  Section OverlayFacts.
    Context (rc : bool) {X : Type} (sel : X -> option (ThreadEvent (F rc))).

    (** The return value of a witness operation is the one in the trace. *)
    Lemma witness_ret T indep nu W o j op ret :
      SLC.trace_wf sel T -> rel_lin_witness sel T indep nu W -> In o W ->
      res_at sel T j (op_key o) op ret -> SLM.ovev rc o = SLM.ovev_of op ret.
    Proof.
      intros (_ & Hru & _) (_ & _ & Hocc & _) Ho Hj.
      destruct (Hocc o Ho) as [_ (j' & Hj')].
      pose proof (Hru _ _ _ _ _ _ _ Hj Hj') as <-.
      symmetry. exact (SLC.res_at_ovev rc sel T j (op_key o) (op_key o) op (op_op o) ret (op_ret o) Hj Hj').
    Qed.
  End OverlayFacts.

  (** The z analogue of [SeqLockClients.nuF_all_read_src]: a [zr()] that
      returns [v] returns the initial 0 or follows a [zw(v)]. *)
  Lemma nuF_all_zread_src rc (W : list (Op (F rc))) :
    BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W ->
    forall o v, In o W -> SLM.ovev rc o = SL.OZR v ->
      v = 0 \/ exists w, In w W /\ op_op w = fZw v /\ before W w o.
  Proof.
    intros Hnu o v Ho Hov.
    set (fZ := fun o : Op (F rc) => if SL.comp_dec (fcomp (op_op o)) SL.CZ then true else false).
    assert (HoZ : In o (filter fZ W)).
    { apply filter_In. split; [exact Ho |]. unfold fZ. rewrite (SLC.ovev_OZR rc o v Hov). reflexivity. }
    destruct (in_split _ _ HoZ) as (P1 & P2 & EP).
    pose proof (Hnu SL.CZ) as HZ. change (SL.nu_z (map (SLM.ovev rc) (filter fZ W))) in HZ.
    unfold SL.nu_z in HZ. rewrite EP, map_app in HZ. cbn [map] in HZ. rewrite Hov in HZ.
    destruct (SLC.reg_ok_read_src SL.z_wr SL.z_rd _ _ _ _ v HZ eq_refl eq_refl) as [E | (e & He & Ee)];
      [left; exact E | right].
    apply in_map_iff in He as (w & <- & Hw).
    exists w. split; [| split].
    - assert (HwZ : In w (filter fZ W)) by (rewrite EP; apply in_or_app; left; exact Hw).
      apply filter_In in HwZ. exact (proj1 HwZ).
    - apply SLC.ovev_OZW, SLC.z_wr_OZW, Ee.
    - apply (BL.before_filter_inv fZ). rewrite EP.
      destruct (in_split _ _ Hw) as (P11 & P12 & ->).
      exists P11, (P12 ++ o :: P2). split; [rewrite <- app_assoc; reflexivity |].
      apply in_or_app. right. left. reflexivity.
  Qed.

  (** Overlay semi-independence induced by a category assignment of
      blocks, by the same rule as [SeqLockProg.findep]: different
      components, and [WindowTable.dto] does not order the categories. *)
  Definition fblk (o : FOp) : SL.Blk :=
    match o with
    | fWrite vx vy => SL.BW vx vy
    | fRead => SL.BR [] 0 0 0
    | fZw v => SL.BZw v
    | fZr => SL.BZr 0
    end.

  Definition cf_indep (rc : bool) (cf : SL.Blk -> WT.DCat) (o o' : FOp) : Prop :=
    fcomp o <> fcomp o' /\ WT.dto rc (cf (fblk o)) (cf (fblk o')) = false.

  (** [findep] is the instance for [SeqLockCOH.sl_cf] (read ↦ rmb,
      write ↦ wmb). *)
  Lemma findep_sl_cf rc o o' : findep rc o o' <-> cf_indep rc SL.sl_cf o o'.
  Proof. destruct o, o'; split; intros H; exact H. Qed.

  (** The paper's own rule: the tensor [RelaxedSig.Tens.tensor_semi_independent]
      of a SeqLock signature with the printed fence modes
      [[rd ↦ rfence][wrt ↦ lfence]] (trace.tex:395) and a COH[z]
      signature with arbitrary modes and semi-independence.  [femb] sends
      an operation of [F] to its component. *)
  Inductive SLOp := slWrite (vx vy : nat) | slRead.
  Inductive ZOp := zWrite (v : nat) | zRead.

  Definition SLS : Sig.t :=
    {| Sig.op := SLOp; Sig.ar := fun o => match o with slWrite _ _ => unit | slRead => (nat * nat)%type end |}.
  Definition ZS : Sig.t :=
    {| Sig.op := ZOp; Sig.ar := fun o => match o with zWrite _ => unit | zRead => nat end |}.

  Definition paper_sl (Isl : SLOp -> SLOp -> Prop) : RelaxedSig.t :=
    {| effect := SLS; handle := nat; semi_independent := Isl;
       mode := fun o => match o with slWrite _ _ => LFence | slRead => RFence end |}.
  Definition coh_z (Iz : ZOp -> ZOp -> Prop) (mz : ZOp -> FenceMode) : RelaxedSig.t :=
    {| effect := ZS; handle := nat; semi_independent := Iz; mode := mz |}.

  Definition femb (o : FOp) : SLOp + ZOp :=
    match o with
    | fWrite vx vy => inl (slWrite vx vy)
    | fRead => inl slRead
    | fZw v => inr (zWrite v)
    | fZr => inr zRead
    end.

  Definition paper_tens_indep Isl Iz mz (o o' : FOp) : Prop :=
    Tens.tensor_semi_independent (paper_sl Isl) (coh_z Iz mz) (femb o) (femb o').

  (** ** Part 7: the load-buffering execution [T_lb] *)

  Section LB.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).
    Local Abbreviation FF := (F rc).

    Definition U (m : TaggedEvent G) : ModuleEvent G FF := UnderlayEvent (untag m).
    Definition oi (t : tid) (h : nat) (o : FOp) : ModuleEvent G FF :=
      OverlayEvent (Build_ThreadEvent t (@InvEv FF h o)).
    Definition orr (t : tid) (h : nat) (o : FOp) (v : @Sig.ar (effect FF) o) : ModuleEvent G FF :=
      OverlayEvent (Build_ThreadEvent t (@ResEv FF h o v)).

    (** Method runs: A's [zr()] on handle 0 returning 1, A's
        [write(1,1)] on handles 1..6, B's [read()] on handles 0..5 with
        ticket 2 returning (1,1), B's [zw(1)] on handle 6. *)
    Definition zrA : list (TaggedEvent G) := one_tr rc tA 0 sRdZ 1.
    Definition wrA : list (TaggedEvent G) := wr_tr rc tA 0 1 1.
    Definition rdB : list (TaggedEvent G) := rd_tr rc tB 2 1 1.
    Definition zwB : list (TaggedEvent G) := one_tr rc tB 6 (sWrZ 1) tt.

    Definition T_lb : list (ModuleEvent G FF) :=
      [oi tA 0 fZr] ++ map U (firstn 1 zrA) ++
      [oi tA 1 (fWrite 1 1)] ++ map U wrA ++
      [oi tB 0 fRead] ++ map U rdB ++
      [oi tB 1 (fZw 1)] ++ map U zwB ++
      [orr tA 1 (fWrite 1 1) tt; orr tB 0 fRead (1, 1); orr tB 1 (fZw 1) tt] ++
      map U (skipn 1 zrA) ++ [orr tA 0 fZr 1].

    Lemma lb_execution : exists c,
      module_execution_tagged (VEa rc) (M rc SL.plainTL) (initial_tagged_module (VEa rc) SL.init) T_lb c /\
      tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell FF e = DeadCall).
    Proof.
      eexists. split; [| split].
      - unfold T_lb, zrA, wrA, rdB, zwB. cbn [app map firstn skipn one_tr wr_tr rd_tr U oi orr].
        oinv (zr_produces rc tA 0 1). uhere.
        oinv (wr_produces rc tA 0 1 1). do 12 usecond.
        oinv (rd_produces rc tB 2 1 1). do 12 usecond.
        oinv (zw_produces rc tB 6 1). do 2 usecond.
        oret. oret. oret. uhere. oret.
        apply tagged_module_execution_refl.
      - reflexivity.
      - intros e He. cbn in He. repeat (destruct He as [<- | He]; [reflexivity |]). destruct He.
    Qed.

    (** The underlay witness, adapted from [SeqLockCOH.lb_wit]: A's write
        calls, B's read calls, B's [z := 1], and last A's [z.rd() = 1]. *)
    Definition W_lb : list (Op G) :=
      [Build_Op (E := G) (tA, 1) sAcq tt; Build_Op (E := G) (tA, 2) sWmb tt;
       Build_Op (E := G) (tA, 3) (sWrX 1) tt; Build_Op (E := G) (tA, 4) (sWrY 1) tt;
       Build_Op (E := G) (tA, 5) sWmb tt; Build_Op (E := G) (tA, 6) sRel tt;
       Build_Op (E := G) (tB, 0) sGt 2; Build_Op (E := G) (tB, 1) sRmb tt;
       Build_Op (E := G) (tB, 2) sRdX 1; Build_Op (E := G) (tB, 3) sRdY 1;
       Build_Op (E := G) (tB, 4) sRmb tt; Build_Op (E := G) (tB, 5) (sTt 2) false;
       Build_Op (E := G) (tB, 6) (sWrZ 1) tt; Build_Op (E := G) (tA, 0) sRdZ 1].

    Lemma lb_underlay_witness :
      rel_lin_witness BL.under_sel T_lb (semi_independent G)
        (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) W_lb.
    Proof.
      split; [| split; [| split; [| split]]].
      - intros []; cbn; repeat split.
      - apply nodup_check. reflexivity.
      - intros o Ho. unfold W_lb in Ho.
        repeat (destruct Ho as [<- | Ho]; [split; find_pos |]). destruct Ho.
      - apply all_check_sound. reflexivity.
      - apply rhb_check_sound. reflexivity.
    Qed.

    Lemma lb_underlay_rel_lin :
      rel_lin BL.under_sel T_lb (semi_independent G)
        (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)).
    Proof. exists W_lb. exact lb_underlay_witness. Qed.

    (** *** The overlay part *)

    Local Abbreviation nuF := (BL.nuF_all (F := FF) SL.comp_dec fcomp (SLM.nuFc rc)).

    (** The overlay invocations of [T_lb]. *)
    Lemma lb_over_inv i k op :
      inv_at BL.over_sel T_lb i k op ->
      In (i, k, op) [(0, (tA, 0), fZr); (2, (tA, 1), fWrite 1 1); (15, (tB, 0), fRead); (28, (tB, 1), fZw 1)].
    Proof. intros H. apply inv_at_pos in H. exact H. Qed.

    Lemma lb_write_inv i k vx vy : inv_at BL.over_sel T_lb i k (fWrite vx vy) -> k = (tA, 1) /\ vx = 1 /\ vy = 1.
    Proof.
      intros H. apply lb_over_inv in H. cbn in H.
      repeat (destruct H as [H | H]; [inversion H; subst; repeat split |]). destruct H.
    Qed.

    Lemma lb_zw_inv i k v : inv_at BL.over_sel T_lb i k (fZw v) -> k = (tB, 1) /\ v = 1.
    Proof.
      intros H. apply lb_over_inv in H. cbn in H.
      repeat (destruct H as [H | H]; [inversion H; subst; repeat split |]). destruct H.
    Qed.

    (** The client hypothesis of [seqlock_client_equal_pairs]: every
        [write] invocation is diagonal. *)
    Lemma lb_writes_diag i k vx vy : inv_at BL.over_sel T_lb i k (fWrite vx vy) -> vx = vy.
    Proof. intros H. destruct (lb_write_inv i k vx vy H) as (_ & -> & ->). reflexivity. Qed.

    (** [seqlock_module_rel_lin] applies: the overlay part is relaxed
        linearizable under F's semi-independence. *)
    Theorem seqlock_lb_module : rel_lin BL.over_sel T_lb (semi_independent FF) nuF.
    Proof.
      destruct lb_execution as (c & Hx & Hq & Hd).
      exact (SLM.seqlock_module_rel_lin rc (VEa rc) SL.init T_lb c Hx Hq Hd lb_underlay_rel_lin).
    Qed.

    (** Any semi-independence that keeps the two program-order edges
        [zr(); write(1,1)] and [read(); zw(1)] rejects [T_lb]: the edges,
        ν_SeqLock ([read() = (1,1)] after [write(1,1)]) and ν_COH[z]
        ([zr() = 1] after [zw(1)]) form a cycle. *)
    Lemma lb_refuted indep :
      ~ indep fZr (fWrite 1 1) -> ~ indep fRead (fZw 1) -> ~ rel_lin BL.over_sel T_lb indep nuF.
    Proof.
      intros Hzw Hrz (W & HW).
      destruct lb_execution as (c & Hx & _ & _).
      pose proof (SLC.over_trace_wf (VEa rc) (M rc SL.plainTL) SL.init T_lb c Hx) as Hwf.
      pose proof HW as (Hnu & Hnd & Hocc & _ & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      destruct (SLC.witness_inv rc BL.over_sel T_lb indep nuF W Hwf HW 0 (tA, 0) fZr
                  ltac:(eexists; split; reflexivity)) as (ozr & Hozr & Kzr & Ozr & Izr).
      destruct (SLC.witness_inv rc BL.over_sel T_lb indep nuF W Hwf HW 2 (tA, 1) (fWrite 1 1)
                  ltac:(eexists; split; reflexivity)) as (owr & Howr & Kwr & Owr & Iwr).
      destruct (SLC.witness_inv rc BL.over_sel T_lb indep nuF W Hwf HW 15 (tB, 0) fRead
                  ltac:(eexists; split; reflexivity)) as (ord & Hord' & Krd & Ord & Ird).
      destruct (SLC.witness_inv rc BL.over_sel T_lb indep nuF W Hwf HW 28 (tB, 1) (fZw 1)
                  ltac:(eexists; split; reflexivity)) as (ozw & Hozw & Kzw & Ozw & Izw).
      assert (Vzr : SLM.ovev rc ozr = SL.OZR 1).
      { apply (witness_ret rc BL.over_sel T_lb indep nuF W ozr 35 fZr 1 Hwf HW Hozr).
        rewrite Kzr. eexists. split; reflexivity. }
      assert (Vrd : SLM.ovev rc ord = SL.OR 1 1).
      { apply (witness_ret rc BL.over_sel T_lb indep nuF W ord 32 fRead (1, 1) Hwf HW Hord').
        rewrite Krd. eexists. split; reflexivity. }
      (* program order, kept by [indep] *)
      assert (B1 : before W ozr owr).
      { apply (Hord ozr owr Hozr Howr). right. split; [rewrite Kzr, Kwr; reflexivity |].
        exists 0, 2. split; [exact Izr |]. split; [exact Iwr |]. split; [lia |].
        rewrite Ozr, Owr. exact Hzw. }
      assert (B3 : before W ord ozw).
      { apply (Hord ord ozw Hord' Hozw). right. split; [rewrite Krd, Kzw; reflexivity |].
        exists 15, 28. split; [exact Ird |]. split; [exact Izw |]. split; [lia |].
        rewrite Ord, Ozw. exact Hrz. }
      (* the specifications *)
      assert (B2 : before W owr ord).
      { destruct (SLC.nuF_all_read_src rc W Hnu ord 1 1 Hord' Vrd) as [E | (w & Hw & Ew & Hb)];
          [discriminate E |].
        destruct (Hocc w Hw) as [(i & Hi) _]. rewrite Ew in Hi.
        destruct (lb_write_inv _ _ _ _ Hi) as (Hk & _).
        assert (Ew' : w = owr).
        { apply (SLC.witness_key_unique rc BL.over_sel T_lb indep nuF W w owr HW Hw Howr). congruence. }
        subst w. exact Hb. }
      assert (B4 : before W ozw ozr).
      { destruct (nuF_all_zread_src rc W Hnu ozr 1 Hozr Vzr) as [E | (w & Hw & Ew & Hb)];
          [discriminate E |].
        destruct (Hocc w Hw) as [(i & Hi) _]. rewrite Ew in Hi.
        destruct (lb_zw_inv _ _ _ Hi) as (Hk & _).
        assert (Ew' : w = ozw).
        { apply (SLC.witness_key_unique rc BL.over_sel T_lb indep nuF W w ozw HW Hw Hozw). congruence. }
        subst w. exact Hb. }
      exact (SLC.before_asym W ozr ozw HndW
               (SLC.before_trans W _ _ _ HndW (SLC.before_trans W _ _ _ HndW B1 B2) B3) B4).
    Qed.

    (** Rejection under I = ∅: [rhb] is real time ∪ per-thread invocation
        order.  ([T_lb] is not a Herlihy--Wing history: each thread has
        two pending calls.) *)
    Theorem seqlock_lb_not_classical : ~ rel_lin BL.over_sel T_lb (fun _ _ => False) nuF.
    Proof. apply lb_refuted; intros []. Qed.

    (** So does every category assignment that orders a client read
        before a later SeqLock write and a SeqLock read before a later
        client write (cf. [SeqLockCOH.lb_refutes], at witness level). *)
    Theorem seqlock_lb_refutes cf :
      WT.dto rc (cf (SL.BZr 0)) (cf (SL.BW 1 1)) = true ->
      WT.dto rc (cf (SL.BR [] 0 0 0)) (cf (SL.BZw 1)) = true ->
      ~ rel_lin BL.over_sel T_lb (cf_indep rc cf) nuF.
    Proof.
      intros D1 D2. apply lb_refuted; intros [_ H]; cbn [fblk] in H; congruence.
    Qed.

    (** In particular the paper's printed signature, as categories
        (read ↦ acquire, write ↦ release: [SeqLockCOH.paper_cf]) and as
        fence modes (read ↦ rfence, write ↦ lfence:
        [SeqLockCOH.paper_cf_modes]). *)
    Corollary seqlock_lb_paper_signature : ~ rel_lin BL.over_sel T_lb (cf_indep rc SL.paper_cf) nuF.
    Proof. apply seqlock_lb_refutes; destruct rc; reflexivity. Qed.

    Corollary seqlock_lb_paper_modes : ~ rel_lin BL.over_sel T_lb (cf_indep rc SL.paper_cf_modes) nuF.
    Proof. apply seqlock_lb_refutes; destruct rc; reflexivity. Qed.

    (** The same in the paper's vocabulary: under the tensor rule with
        [[rd ↦ rfence][wrt ↦ lfence]], a cross pair (e, f) is
        semi-independent only if [mode e ≤f LFence] and
        [mode f ≤f RFence]; [LFence ≤f RFence] and [RFence ≤f LFence] are
        both false, so both pairs are ordered whatever the modes and the
        semi-independence of z. *)
    Corollary seqlock_lb_paper_tensor Isl Iz mz :
      ~ rel_lin BL.over_sel T_lb (paper_tens_indep Isl Iz mz) nuF.
    Proof. apply lb_refuted; intros H; inversion H; subst; cbn in *; tauto. Qed.

    (** *** The client theorems of [SeqLockClients] on [T_lb]

        The read of thread B responds (1,1) at position 32.  The
        hypotheses of the module-level client theorems hold, so they
        apply. *)

    Lemma lb_read_response : res_at BL.over_sel T_lb 32 (tB, 0) fRead (1, 1).
    Proof. eexists. split; reflexivity. Qed.

    Corollary lb_client_same_epoch :
      forall j k a b, res_at BL.over_sel T_lb j k fRead (a, b) ->
        (a, b) = (0, 0) \/ exists i k', inv_at BL.over_sel T_lb i k' (fWrite a b).
    Proof.
      destruct lb_execution as (c & Hx & Hq & Hd).
      exact (SLC.seqlock_client_same_epoch rc (VEa rc) SL.init T_lb c Hx Hq Hd lb_underlay_rel_lin).
    Qed.

    Corollary lb_client_equal_pairs :
      forall j k a b, res_at BL.over_sel T_lb j k fRead (a, b) -> a = b.
    Proof.
      destruct lb_execution as (c & Hx & Hq & Hd).
      exact (SLC.seqlock_client_equal_pairs rc (VEa rc) SL.init T_lb c Hx Hq Hd lb_underlay_rel_lin
               lb_writes_diag).
    Qed.

    Corollary lb_client_read_not_future_po :
      forall j k a b, res_at BL.over_sel T_lb j k fRead (a, b) -> (a, b) <> (0, 0) ->
        exists i k', inv_at BL.over_sel T_lb i k' (fWrite a b) /\ i < j /\
          (fst k' = fst k -> forall i0 op0, inv_at BL.over_sel T_lb i0 k op0 -> i < i0).
    Proof.
      destruct lb_execution as (c & Hx & Hq & Hd).
      exact (SLC.seqlock_client_read_not_future_po rc (VEa rc) SL.init T_lb c Hx Hq Hd lb_underlay_rel_lin).
    Qed.
  End LB.

  (** *** Joint satisfiability

      The hypotheses of [seqlock_module_rel_lin] and of
      [seqlock_client_equal_pairs] hold together on a complete
      execution over [VEa] in which
      - thread B's [read()] responds (1,1), and its interval overlaps that
        of thread A's [write(1,1)]: the read is invoked while the write is
        pending (at the overlay; the write's underlay events all precede
        the read's);
      - in each thread the second call is invoked before the first one
        responds;
      and the overlay part is relaxed linearizable under F's
      semi-independence but not under the empty one. *)
  Theorem seqlock_lb_nonvacuous rc :
    exists T c,
      module_execution_tagged (VEa rc) (M rc SL.plainTL) (initial_tagged_module (VEa rc) SL.init) T c /\
      tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) /\
      rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
        (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) /\
      (forall i k vx vy, inv_at BL.over_sel T i k (fWrite vx vy) -> vx = vy) /\
      (* a read response (1,1), concurrent with a write(1,1) of the other thread *)
      (exists ir jr iw jw,
         inv_at BL.over_sel T ir (tB, 0) fRead /\ res_at BL.over_sel T jr (tB, 0) fRead (1, 1) /\
         inv_at BL.over_sel T iw (tA, 1) (fWrite 1 1) /\ res_at BL.over_sel T jw (tA, 1) (fWrite 1 1) tt /\
         iw < jr /\ ir < jw) /\
      (* overlapping same-thread calls: A's write(1,1) is invoked before A's zr() responds,
         B's zw(1) before B's read() responds *)
      (exists i0 j0 i1,
         inv_at BL.over_sel T i0 (tA, 0) fZr /\ res_at BL.over_sel T j0 (tA, 0) fZr 1 /\
         inv_at BL.over_sel T i1 (tA, 1) (fWrite 1 1) /\ i0 < i1 < j0) /\
      (exists i0 j0 i1,
         inv_at BL.over_sel T i0 (tB, 0) fRead /\ res_at BL.over_sel T j0 (tB, 0) fRead (1, 1) /\
         inv_at BL.over_sel T i1 (tB, 1) (fZw 1) /\ i0 < i1 < j0) /\
      rel_lin BL.over_sel T (semi_independent (F rc)) (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)) /\
      ~ rel_lin BL.over_sel T (fun _ _ => False) (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)).
  Proof.
    destruct (lb_execution rc) as (c & Hx & Hq & Hd).
    exists (T_lb rc), c. split; [exact Hx |]. split; [exact Hq |]. split; [exact Hd |].
    split; [exact (lb_underlay_rel_lin rc) |]. split; [exact (lb_writes_diag rc) |].
    split.
    { exists 15, 32, 2, 31. repeat split; try lia; eexists; split; reflexivity. }
    split.
    { exists 0, 35, 2. repeat split; try lia; eexists; split; reflexivity. }
    split.
    { exists 15, 32, 28. repeat split; try lia; eexists; split; reflexivity. }
    split; [exact (seqlock_lb_module rc) | exact (seqlock_lb_not_classical rc)].
  Qed.
  (** ** Part 8: the message-passing execution [T_mp] *)

  (** The overlay events of a module trace, in order. *)
  Definition over_proj {E F : RelaxedSig.t} (T : list (ModuleEvent E F)) : list (ThreadEvent F) :=
    flat_map (fun e => match BL.over_sel e with Some ev => [ev] | None => [] end) T.

  Section MP.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).
    Local Abbreviation FF := (F rc).
    Local Abbreviation nuF := (BL.nuF_all (F := FF) SL.comp_dec fcomp (SLM.nuFc rc)).

    (** Method runs: A's [zw(1)] on handle 0, A's [write(1,1)] on
        handles 1..6, B's [read()] on handles 0..5 with ticket 2
        returning (1,1), B's [zr()] on handle 6 returning 1. *)
    Definition zwA : list (TaggedEvent G) := one_tr rc tA 0 (sWrZ 1) tt.
    Definition zrB : list (TaggedEvent G) := one_tr rc tB 6 sRdZ 1.

    (** [zw(1)]'s underlay response is emitted after the twelve events of
        [write(1,1)]; the four overlay invocations precede the four
        overlay responses. *)
    Definition T_mp : list (ModuleEvent G FF) :=
      [oi rc tA 0 (fZw 1)] ++ map (U rc) (firstn 1 zwA) ++
      [oi rc tA 1 (fWrite 1 1)] ++ map (U rc) (wrA rc) ++ map (U rc) (skipn 1 zwA) ++
      [oi rc tB 0 fRead] ++ map (U rc) (rdB rc) ++
      [oi rc tB 1 fZr] ++ map (U rc) zrB ++
      [orr rc tA 0 (fZw 1) tt; orr rc tA 1 (fWrite 1 1) tt; orr rc tB 0 fRead (1, 1); orr rc tB 1 fZr 1].

    Lemma mp_execution : exists c,
      module_execution_tagged (VEa rc) (M rc SL.plainTL) (initial_tagged_module (VEa rc) SL.init) T_mp c /\
      tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell FF e = DeadCall).
    Proof.
      eexists. split; [| split].
      - unfold T_mp, zwA, wrA, rdB, zrB. cbn [app map firstn skipn one_tr wr_tr rd_tr U oi orr].
        oinv (zw_produces rc tA 0 1). uhere.
        oinv (wr_produces rc tA 0 1 1). do 12 usecond. uhere.
        oinv (rd_produces rc tB 2 1 1). do 12 uhere.
        oinv (zr_produces rc tB 6 1). do 2 uhere.
        oret. oret. oret. oret.
        apply tagged_module_execution_refl.
      - reflexivity.
      - intros e He. cbn in He. repeat (destruct He as [<- | He]; [reflexivity |]). destruct He.
    Qed.

    (** The underlay witness: A's [z := 1], A's write calls, B's read
        calls, B's [z.rd() = 1]. *)
    Definition W_mp : list (Op G) :=
      [Build_Op (E := G) (tA, 0) (sWrZ 1) tt;
       Build_Op (E := G) (tA, 1) sAcq tt; Build_Op (E := G) (tA, 2) sWmb tt;
       Build_Op (E := G) (tA, 3) (sWrX 1) tt; Build_Op (E := G) (tA, 4) (sWrY 1) tt;
       Build_Op (E := G) (tA, 5) sWmb tt; Build_Op (E := G) (tA, 6) sRel tt;
       Build_Op (E := G) (tB, 0) sGt 2; Build_Op (E := G) (tB, 1) sRmb tt;
       Build_Op (E := G) (tB, 2) sRdX 1; Build_Op (E := G) (tB, 3) sRdY 1;
       Build_Op (E := G) (tB, 4) sRmb tt; Build_Op (E := G) (tB, 5) (sTt 2) false;
       Build_Op (E := G) (tB, 6) sRdZ 1].

    Lemma mp_underlay_witness :
      rel_lin_witness BL.under_sel T_mp (semi_independent G)
        (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) W_mp.
    Proof.
      split; [| split; [| split; [| split]]].
      - intros []; cbn; repeat split.
      - apply nodup_check. reflexivity.
      - intros o Ho. unfold W_mp in Ho.
        repeat (destruct Ho as [<- | Ho]; [split; find_pos |]). destruct Ho.
      - apply all_check_sound. reflexivity.
      - apply rhb_check_sound. reflexivity.
    Qed.

    Lemma mp_underlay_rel_lin :
      rel_lin BL.under_sel T_mp (semi_independent G)
        (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)).
    Proof. exists W_mp. exact mp_underlay_witness. Qed.

    (** The overlay part of [T_mp] is the interface-level trace
        [SeqLockClients.mp_trace 1] of [SeqLockClients] Part 5, with the
        same keys and the same order. *)
    Lemma mp_overlay_projection : over_proj T_mp = SLC.mp_trace rc 1.
    Proof. reflexivity. Qed.

    Lemma mp_over_inv i k op :
      inv_at BL.over_sel T_mp i k op ->
      In (i, k, op) [(0, (tA, 0), fZw 1); (2, (tA, 1), fWrite 1 1); (16, (tB, 0), fRead); (29, (tB, 1), fZr)].
    Proof. intros H. apply inv_at_pos in H. exact H. Qed.

    Lemma mp_only_write i k : inv_at BL.over_sel T_mp i k (fWrite 1 1) -> k = (tA, 1).
    Proof.
      intros H. apply mp_over_inv in H. cbn in H.
      repeat (destruct H as [H | H]; [inversion H; subst; reflexivity |]). destruct H.
    Qed.

    Lemma mp_only_zw i k v : inv_at BL.over_sel T_mp i k (fZw v) -> k = (tA, 0).
    Proof.
      intros H. apply mp_over_inv in H. cbn in H.
      repeat (destruct H as [H | H]; [inversion H; subst; reflexivity |]). destruct H.
    Qed.

    (** The client shape of the message-passing theorems, with both
        same-thread overlaps. *)
    Lemma mp_zw_write : exists i i', inv_at BL.over_sel T_mp i (tA, 0) (fZw 1) /\
                                     inv_at BL.over_sel T_mp i' (tA, 1) (fWrite 1 1) /\ i < i'.
    Proof. exists 0, 2. repeat split; try lia; eexists; split; reflexivity. Qed.

    Lemma mp_read_zr : exists i i', inv_at BL.over_sel T_mp i (tB, 0) fRead /\
                                    inv_at BL.over_sel T_mp i' (tB, 1) fZr /\ i < i'.
    Proof. exists 16, 29. repeat split; try lia; eexists; split; reflexivity. Qed.

    Lemma mp_read_response : res_at BL.over_sel T_mp 34 (tB, 0) fRead (1, 1).
    Proof. eexists. split; reflexivity. Qed.

    Lemma mp_zr_response : res_at BL.over_sel T_mp 35 (tB, 1) fZr 1.
    Proof. eexists. split; reflexivity. Qed.

    Lemma mp_overlaps :
      (exists j, res_at BL.over_sel T_mp j (tA, 0) (fZw 1) tt /\ 2 < j) /\
      (exists j, res_at BL.over_sel T_mp j (tB, 0) fRead (1, 1) /\ 29 < j).
    Proof. split; [exists 32 | exists 34]; (split; [eexists; split; reflexivity | lia]). Qed.

    (** [seqlock_module_rel_lin] and the message-passing client theorems
        on [T_mp]. *)
    Theorem seqlock_mp_module : rel_lin BL.over_sel T_mp (semi_independent FF) nuF.
    Proof.
      destruct mp_execution as (c & Hx & Hq & Hd).
      exact (SLM.seqlock_module_rel_lin rc (VEa rc) SL.init T_mp c Hx Hq Hd mp_underlay_rel_lin).
    Qed.

    Corollary mp_client_order :
      rel_lin BL.over_sel T_mp (semi_independent FF) nuF /\
      (forall W, rel_lin_witness BL.over_sel T_mp (semi_independent FF) nuF W ->
         forall oz oq, In oz W -> op_key oz = (tA, 0) -> In oq W -> op_key oq = (tB, 1) -> before W oz oq).
    Proof.
      destruct mp_execution as (c & Hx & Hq & Hd).
      exact (SLC.seqlock_client_mp_order rc (VEa rc) SL.init T_mp c (tA, 0) (tA, 1) (tB, 0) (tB, 1) 1 1 1 34
               Hx Hq Hd mp_underlay_rel_lin eq_refl mp_zw_write eq_refl mp_read_zr mp_read_response
               ltac:(discriminate) mp_only_write).
    Qed.

    Corollary mp_client_zr_value : forall jq r, res_at BL.over_sel T_mp jq (tB, 1) fZr r -> r = 1.
    Proof.
      destruct mp_execution as (c & Hx & Hq & Hd).
      exact (SLC.seqlock_client_mp_zr_value rc (VEa rc) SL.init T_mp c (tA, 0) (tA, 1) (tB, 0) (tB, 1) 1 1 1 34
               Hx Hq Hd mp_underlay_rel_lin eq_refl mp_zw_write eq_refl mp_read_zr mp_read_response
               ltac:(discriminate) mp_only_write mp_only_zw).
    Qed.
  End MP.

  (** *** Joint satisfiability for message passing

      Every hypothesis of [SeqLockClients.seqlock_client_mp_zr_value]
      holds on one complete execution over [VEa] in which [write(1,1)]
      is invoked before [zw(1)] responds and [zr()] before [read()]
      responds; its conclusion is not vacuous ([zr()] does respond, with
      1). *)
  Theorem seqlock_mp_nonvacuous rc :
    exists T c,
      module_execution_tagged (VEa rc) (M rc SL.plainTL) (initial_tagged_module (VEa rc) SL.init) T c /\
      tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) /\
      rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
        (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) /\
      (exists i i' j, inv_at BL.over_sel T i (tA, 0) (fZw 1) /\ inv_at BL.over_sel T i' (tA, 1) (fWrite 1 1) /\
                      res_at BL.over_sel T j (tA, 0) (fZw 1) tt /\ i < i' < j) /\
      (exists i i' j, inv_at BL.over_sel T i (tB, 0) fRead /\ inv_at BL.over_sel T i' (tB, 1) fZr /\
                      res_at BL.over_sel T j (tB, 0) fRead (1, 1) /\ i < i' < j) /\
      (forall i k, inv_at BL.over_sel T i k (fWrite 1 1) -> k = (tA, 1)) /\
      (forall i k v, inv_at BL.over_sel T i k (fZw v) -> k = (tA, 0)) /\
      (exists jq, res_at BL.over_sel T jq (tB, 1) fZr 1) /\
      (forall jq r, res_at BL.over_sel T jq (tB, 1) fZr r -> r = 1) /\
      over_proj T = SLC.mp_trace rc 1.
  Proof.
    destruct (mp_execution rc) as (c & Hx & Hq & Hd).
    exists (T_mp rc), c. split; [exact Hx |]. split; [exact Hq |]. split; [exact Hd |].
    split; [exact (mp_underlay_rel_lin rc) |].
    split; [exists 0, 2, 32; repeat split; try lia; eexists; split; reflexivity |].
    split; [exists 16, 29, 34; repeat split; try lia; eexists; split; reflexivity |].
    split; [exact (mp_only_write rc) |]. split; [exact (mp_only_zw rc) |].
    split; [exists 35; exact (mp_zr_response rc) |].
    split; [exact (mp_client_zr_value rc) | exact (mp_overlay_projection rc)].
  Qed.
  (** ** Part 9: [VEa] does not implement ν_E ([T_bad])

      [T_bad] is [T_mp] with [zr() = 0].  The response of A's [z := 1]
      is delayed past every other underlay event, so B's [z.rd()] is
      answered 0 in [VEa].  The execution is complete and every return
      value passes [VEa].  Its underlay part is not relaxed linearizable
      (so the module theorem does not apply), and its overlay part is not
      relaxed linearizable either: over [VEa], SeqLock ⊎ COH[z] violates
      message passing.  This is the discriminating counterpart of [T_mp]:
      the underlay hypothesis of [seqlock_module_rel_lin] is
      load-bearing, and [VEa] does not discharge it. *)

  Section Bad.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).
    Local Abbreviation FF := (F rc).
    Local Abbreviation nuF := (BL.nuF_all (F := FF) SL.comp_dec fcomp (SLM.nuFc rc)).

    Definition zrB0 : list (TaggedEvent G) := one_tr rc tB 6 sRdZ 0.

    Definition T_bad : list (ModuleEvent G FF) :=
      [oi rc tA 0 (fZw 1)] ++ map (U rc) (firstn 1 (zwA rc)) ++
      [oi rc tA 1 (fWrite 1 1)] ++ map (U rc) (wrA rc) ++
      [oi rc tB 0 fRead] ++ map (U rc) (rdB rc) ++
      [oi rc tB 1 fZr] ++ map (U rc) zrB0 ++
      map (U rc) (skipn 1 (zwA rc)) ++
      [orr rc tA 0 (fZw 1) tt; orr rc tA 1 (fWrite 1 1) tt; orr rc tB 0 fRead (1, 1); orr rc tB 1 fZr 0].

    Lemma bad_execution : exists c,
      module_execution_tagged (VEa rc) (M rc SL.plainTL) (initial_tagged_module (VEa rc) SL.init) T_bad c /\
      tm_queue c = [] /\ (forall e, In e (tm_calls c) -> ce_cell FF e = DeadCall).
    Proof.
      eexists. split; [| split].
      - unfold T_bad, zwA, wrA, rdB, zrB0. cbn [app map firstn skipn one_tr wr_tr rd_tr U oi orr].
        oinv (zw_produces rc tA 0 1). uhere.
        oinv (wr_produces rc tA 0 1 1). do 12 usecond.
        oinv (rd_produces rc tB 2 1 1). do 12 usecond.
        oinv (zr_produces rc tB 6 0). do 2 usecond. uhere.
        oret. oret. oret. oret.
        apply tagged_module_execution_refl.
      - reflexivity.
      - intros e He. cbn in He. repeat (destruct He as [<- | He]; [reflexivity |]). destruct He.
    Qed.

    Lemma bad_only_write i k : inv_at BL.over_sel T_bad i k (fWrite 1 1) -> k = (tA, 1).
    Proof.
      intros H. apply inv_at_pos in H. cbn in H.
      repeat (destruct H as [H | H]; [inversion H; subst; reflexivity |]). destruct H.
    Qed.

    Lemma bad_only_zw i k v : inv_at BL.over_sel T_bad i k (fZw v) -> k = (tA, 0).
    Proof.
      intros H. apply inv_at_pos in H. cbn in H.
      repeat (destruct H as [H | H]; [inversion H; subst; reflexivity |]). destruct H.
    Qed.

    (** By contraposition of [seqlock_client_mp_zr_value]. *)
    Theorem bad_underlay_not_rel_lin :
      ~ rel_lin BL.under_sel T_bad (semi_independent G)
          (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)).
    Proof.
      intros Hu. destruct bad_execution as (c & Hx & Hq & Hd).
      pose proof (SLC.seqlock_client_mp_zr_value rc (VEa rc) SL.init T_bad c (tA, 0) (tA, 1) (tB, 0) (tB, 1)
                    1 1 1 34 Hx Hq Hd Hu eq_refl
                    ltac:(exists 0, 2; repeat split; try lia; eexists; split; reflexivity) eq_refl
                    ltac:(exists 15, 28; repeat split; try lia; eexists; split; reflexivity)
                    ltac:(eexists; split; reflexivity) ltac:(discriminate) bad_only_write bad_only_zw
                    35 0 ltac:(eexists; split; reflexivity)) as H.
      discriminate H.
    Qed.

    (** From the interface rule [client_rule_mp_zr_value]; the module
        theorem is not used. *)
    Theorem bad_overlay_not_rel_lin : ~ rel_lin BL.over_sel T_bad (semi_independent FF) nuF.
    Proof.
      intros (W & HW). destruct bad_execution as (c & Hx & _ & _).
      pose proof (SLC.over_trace_wf (VEa rc) (M rc SL.plainTL) SL.init T_bad c Hx) as Hwf.
      pose proof (SLC.client_rule_mp_zr_value rc BL.over_sel T_bad W (tA, 0) (tA, 1) (tB, 0) (tB, 1)
                    1 1 1 34 Hwf HW eq_refl
                    ltac:(exists 0, 2; repeat split; try lia; eexists; split; reflexivity) eq_refl
                    ltac:(exists 15, 28; repeat split; try lia; eexists; split; reflexivity)
                    ltac:(eexists; split; reflexivity) ltac:(discriminate) bad_only_write bad_only_zw
                    35 0 ltac:(eexists; split; reflexivity)) as H.
      discriminate H.
    Qed.
  End Bad.

  (** ** Part 10: load buffering at the underlay of [T_lb]

      The underlay part of [T_lb] contains memory-level load buffering on
      the registers z and x:
<<
      A:  z.rd() = 1 ;  ... x.wrt(1) ...
      B:  ... x.rd() = 1 ... ;  z.wrt(1)
>>
      It is relaxed linearizable under the underlay semi-independence
      ([lb_underlay_rel_lin]), but not under the empty one: with every
      per-thread invocation order kept, z.rd() → x.wrt(1) → x.rd() = 1 →
      z.wrt(1) → z.rd() = 1 is a cycle ([lb_underlay_not_classical]).  So
      the same execution exhibits load buffering at both levels. *)

  Section UnderlayLB.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).

    (** Every underlay call of [T_lb] with its key. *)
    Definition lb_table : list (CallKey G * SL.UC) :=
      [((tA, 1), SL.Acq); ((tA, 2), SL.WmbC); ((tA, 3), SL.WrX 1); ((tA, 4), SL.WrY 1);
       ((tA, 5), SL.WmbC); ((tA, 6), SL.Rel);
       ((tB, 0), SL.GT 2); ((tB, 1), SL.RmbC); ((tB, 2), SL.RdX 1); ((tB, 3), SL.RdY 1);
       ((tB, 4), SL.RmbC); ((tB, 5), SL.TT 2 false); ((tB, 6), SL.WrZ 1); ((tA, 0), SL.RdZ 1)].

    Lemma lb_ucall o : occurs BL.under_sel (T_lb rc) o -> In (op_key o, SLM.uc rc SL.plainTL o) lb_table.
    Proof.
      intros [_ (j & Hj)].
      apply (res_at_ressv (G := G) BL.under_sel (B := SL.UC) uc_of (T_lb rc) 0) in Hj.
      change (In (op_key o, SLM.uc rc SL.plainTL o)
                (map (fun p => (snd (fst p), snd p))
                   (ressv_from (G := G) BL.under_sel (B := SL.UC) uc_of 0 (T_lb rc)))).
      apply (in_map (fun p => (snd (fst p), snd p))) in Hj. exact Hj.
    Qed.

    Lemma lb_table_keys k c : In (k, c) lb_table ->
      (c = SL.WrX 1 -> k = (tA, 3)) /\ (c = SL.WrZ 1 -> k = (tB, 6)).
    Proof.
      intros H. cbn in H.
      repeat (destruct H as [H | H]; [inversion H; subst; split; intros E; first [discriminate E | reflexivity] |]).
      destruct H.
    Qed.

    Lemma lb_table_vals k c : In (k, c) lb_table ->
      (k = (tA, 0) -> c = SL.RdZ 1) /\ (k = (tA, 3) -> c = SL.WrX 1) /\
      (k = (tB, 2) -> c = SL.RdX 1) /\ (k = (tB, 6) -> c = SL.WrZ 1).
    Proof.
      intros H. cbn in H.
      repeat (destruct H as [H | H];
              [inversion H; subst; repeat split; intros E; first [discriminate E | reflexivity] |]).
      destruct H.
    Qed.

    Theorem lb_underlay_not_classical :
      ~ rel_lin BL.under_sel (T_lb rc) (fun _ _ => False)
          (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)).
    Proof.
      intros (W & Hnu & Hnd & Hocc & Hall & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      assert (Huniq : forall u u', In u W -> In u' W -> op_key u = op_key u' -> u = u')
        by (intros u u' Hu Hu' E; exact (RelaxedModuleFacts.nodup_map_inj op_key W u u' Hnd Hu Hu' E)).
      (* the four calls of the cycle, with their calls and operations *)
      assert (Get : forall i k op, inv_at BL.under_sel (T_lb rc) i k op ->
                exists o, In o W /\ op_key o = k /\
                  op_op o = op_of (SLM.uc rc SL.plainTL o) /\
                  In (k, SLM.uc rc SL.plainTL o) lb_table).
      { intros i k op Hi. destruct (Hall i k op Hi) as (o & Ho & Hk). exists o.
        split; [exact Ho |]. split; [exact Hk |]. split.
        - unfold SLM.uc. symmetry. apply op_of_uc.
        - rewrite <- Hk. apply lb_ucall, Hocc, Ho. }
      destruct (Get 1 (tA, 0) sRdZ ltac:(eexists; split; reflexivity)) as (ozr & Hozr & Kzr & Ozr & Tzr).
      destruct (Get 7 (tA, 3) (sWrX 1) ltac:(eexists; split; reflexivity)) as (owx & Howx & Kwx & Owx & Twx).
      destruct (Get 20 (tB, 2) sRdX ltac:(eexists; split; reflexivity)) as (orx & Horx & Krx & Orx & Trx).
      destruct (Get 29 (tB, 6) (sWrZ 1) ltac:(eexists; split; reflexivity)) as (owz & Howz & Kwz & Owz & Twz).
      pose proof (proj1 (lb_table_vals _ _ Tzr) eq_refl) as Czr.
      pose proof (proj1 (proj2 (lb_table_vals _ _ Twx)) eq_refl) as Cwx.
      pose proof (proj1 (proj2 (proj2 (lb_table_vals _ _ Trx))) eq_refl) as Crx.
      pose proof (proj2 (proj2 (proj2 (lb_table_vals _ _ Twz))) eq_refl) as Cwz.
      rewrite Czr in Ozr. rewrite Cwx in Owx. rewrite Crx in Orx. rewrite Cwz in Owz. cbn in Ozr, Owx, Orx, Owz.
      (* program order, all kept *)
      assert (B1 : before W ozr owx).
      { apply (Hord ozr owx Hozr Howx). right. split; [rewrite Kzr, Kwx; reflexivity |].
        exists 1, 7. rewrite Kzr, Kwx, Ozr, Owx.
        split; [eexists; split; reflexivity |]. split; [eexists; split; reflexivity |]. split; [lia | tauto]. }
      assert (B3 : before W orx owz).
      { apply (Hord orx owz Horx Howz). right. split; [rewrite Krx, Kwz; reflexivity |].
        exists 20, 29. rewrite Krx, Kwz, Orx, Owz.
        split; [eexists; split; reflexivity |]. split; [eexists; split; reflexivity |]. split; [lia | tauto]. }
      (* x: the read of 1 follows the only write of 1 *)
      assert (B2 : before W owx orx).
      { set (fS := fun o : Op G => if SL.comp_dec (SLM.compE (op_op o)) SL.CSL then true else false).
        assert (HS : In orx (filter fS W)) by (apply filter_In; split; [exact Horx | unfold fS; rewrite Orx; reflexivity]).
        destruct (in_split _ _ HS) as (P1 & P2 & EP).
        pose proof (Hnu SL.CSL) as Hx. change (SLM.replay SL.init (map (SLM.uev rc SL.plainTL) (filter fS W))) in Hx.
        rewrite EP, map_app in Hx. cbn [map] in Hx.
        destruct (replay_rdx_src _ _ _ _ 1 Hx ltac:(exact Crx)) as [E | (e' & He' & Ee')]; [discriminate E |].
        apply in_map_iff in He' as (u & <- & Hu).
        assert (HuW : In u W) by (assert (In u (filter fS W)) as Hf by (rewrite EP; apply in_or_app; left; exact Hu);
                                  apply filter_In in Hf; exact (proj1 Hf)).
        assert (Ku : op_key u = (tA, 3)) by exact (proj1 (lb_table_keys _ _ (lb_ucall u (Hocc u HuW))) Ee').
        rewrite (Huniq u owx HuW Howx (eq_trans Ku (eq_sym Kwx))) in Hu.
        apply (BL.before_filter_inv fS). rewrite EP.
        destruct (in_split _ _ Hu) as (P11 & P12 & ->).
        exists P11, (P12 ++ orx :: P2). split; [rewrite <- app_assoc; reflexivity |].
        apply in_or_app. right. left. reflexivity. }
      (* z: the read of 1 follows the only write of 1 *)
      assert (B4 : before W owz ozr).
      { set (fZ := fun o : Op G => if SL.comp_dec (SLM.compE (op_op o)) SL.CZ then true else false).
        assert (HZ : In ozr (filter fZ W)) by (apply filter_In; split; [exact Hozr | unfold fZ; rewrite Ozr; reflexivity]).
        destruct (in_split _ _ HZ) as (P1 & P2 & EP).
        pose proof (Hnu SL.CZ) as Hz. change (SLM.zreg 0 (map (SLM.uc rc SL.plainTL) (filter fZ W))) in Hz.
        rewrite EP, map_app in Hz. cbn [map] in Hz.
        destruct (zreg_rd_src _ _ _ _ 1 Hz Czr) as [E | Hin]; [discriminate E |].
        apply in_map_iff in Hin as (u & Eu & Hu).
        assert (HuW : In u W) by (assert (In u (filter fZ W)) as Hf by (rewrite EP; apply in_or_app; left; exact Hu);
                                  apply filter_In in Hf; exact (proj1 Hf)).
        assert (Ku : op_key u = (tB, 6)) by exact (proj2 (lb_table_keys _ _ (lb_ucall u (Hocc u HuW))) Eu).
        rewrite (Huniq u owz HuW Howz (eq_trans Ku (eq_sym Kwz))) in Hu.
        apply (BL.before_filter_inv fZ). rewrite EP.
        destruct (in_split _ _ Hu) as (P11 & P12 & ->).
        exists P11, (P12 ++ ozr :: P2). split; [rewrite <- app_assoc; reflexivity |].
        apply in_or_app. right. left. reflexivity. }
      exact (SLC.before_asym W ozr owz HndW
               (SLC.before_trans W _ _ _ HndW (SLC.before_trans W _ _ _ HndW B1 B2) B3) B4).
    Qed.
  End UnderlayLB.
End SeqLockLB.
