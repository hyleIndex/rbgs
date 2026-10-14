(** * SeqLockClients: client theorems for SeqLock ⊎ COH[z] at module level

    [SeqLockModule.seqlock_module_rel_lin] says that every complete
    execution of the module [SeqLockProg.M rc plainTL] whose underlay part
    is relaxed linearizable w.r.t. the abstract component specifications
    has an overlay part that is relaxed linearizable w.r.t. ν_SeqLock ⊗
    ν_COH[z], for the overlay semi-independence [SeqLockProg.findep rc].
    This file derives client theorems from that statement.  The SeqLock
    implementation is not looked at again.

    Structure.  The client facts are proved as rules about the interface
    (Part 3, [client_rule_*]).  A rule holds for any trace in which each
    key is invoked at most once and responds at most once, and every key
    that responds was invoked ([trace_wf]), and for every sequential
    witness of that trace's relaxed linearizability w.r.t. ν_SeqLock ⊗
    ν_COH[z] and [findep rc].  The rules do not mention the
    implementation.  The module-level theorems (Part 4) instantiate them
    with the witness that the module theorem provides; every overlay trace
    of the module semantics satisfies [trace_wf] ([over_trace_wf]).
    [seqlock_client_equal_pairs] and [seqlock_client_mp_forbidden] are
    then derived from the module-level same-epoch and z-value theorems.
    Part 5 instantiates the message-passing rules on a concrete trace of
    overlay events ([mp_trace]).  That trace is not a module execution.
    In it both same-thread pairs overlap, and no response precedes an
    invocation.  Part 5 also shows that the same rules, stated for a
    semi-independence that also contains the pairs ([zw], [write]), would
    be false.

    Client theorems (Part 4).  Each has a [_K] variant for every
    TicketLock signature [K] with [SeqLockCOH.K_ok K] (from
    [seqlock_module_rel_lin_K]); the plain theorem is its instance at
    [SeqLockCOH.plainTL].
    - [seqlock_client_same_epoch] (overview.tex:276: "every successful
      read observes values from the same update epoch").  Every overlay
      [read] response event of the trace returns the initial pair (0,0) or
      a pair [(a,b)] that some [write(a,b)] invocation of the trace
      writes.  There is no hypothesis on the writes.  Specification level:
      [reg_epoch], [nu_sl_epoch], [nuF_all_epoch].  "Epoch" is identified
      by value.  Caveats:
        - the returned pair is (0,0) or the argument pair of *some*
          [write] invocation of the trace; the statement does not say
          which one;
        - so this is "no torn read up to value coincidence": a torn read
          whose two components happen to equal the argument pair of
          another [write] is not excluded;
        - there is no freshness claim: the statement does not say that the
          write is the last one before the read, so a stale pair is not
          excluded.  The only timing bound is the [i < j] of
          [seqlock_client_read_not_future];
        - the (0,0) disjunct carries no information when the trace
          contains some [write(0,0)].
      Any paper sentence that cites this theorem must carry the same
      qualifier.
    - [seqlock_client_equal_pairs] (the client of author response B4),
      derived from [seqlock_client_same_epoch].  If every overlay [write]
      invocation in the trace is [write(v,v)], every overlay [read]
      response event returns a pair [(a,a)].  Concurrent writers and any
      number of threads are not excluded by the hypotheses; that such
      executions satisfy them is not shown (see "Not shown here").
      [nu_sl_nondiag] shows that the hypothesis on the writes is needed.
    - [seqlock_client_read_not_future].  A [read] that returns [(a,b)] ≠
      (0,0) returns the pair of a [write(a,b)] invoked before the read's
      response.  This uses the real-time clause of [rhb]: in the witness
      the read follows a [write(a,b)], and a write invoked after the read
      responded would have to follow the read.
      [seqlock_client_read_not_future_po] adds that if this write belongs
      to the reader's thread, it was invoked before the read.  This uses
      the same-thread clause of [rhb]: two SeqLock operations are never
      semi-independent ([read_write_dependent]), so the order holds even
      if the two calls overlap.
    - Message passing.  [seqlock_client_mp_order] (rule
      [client_rule_mp_order]): suppose that in one thread [zw(v)] (key kz)
      is invoked before [write(x,y)] (key kw), that in one thread [read()]
      (key kr) is invoked before [zr()] (key kq) and returns (x,y) ≠
      (0,0), and that kw is the only key that invokes [write(x,y)].  Then
      the witness places kz before kq; the rule holds for every witness.
      At module level, [seqlock_client_mp_order] states that the overlay
      part is relaxed linearizable and that every witness places kz before
      kq.  The universal part is [client_rule_mp_order] with
      [over_trace_wf]; the module theorem adds only the existence of a
      witness.  This is a fact about witnesses, which a client does not
      observe.  Its observable consequence is the next theorem.
      [seqlock_client_mp_zr_value]: if moreover kz is the only key that
      writes z, then [zr()] at kq returns v.  [seqlock_client_mp_forbidden]
      follows, with z initially 0:
<<
        t1: zw(1); write(1,1)      ||      t2: read() = (1,1); zr() = 0
>>
      None of these hypotheses says that the first call of a thread
      returns before its second call is invoked, so the calls may overlap.
      The order comes from F's semi-independence: [zw]/[write] and
      [read]/[zr] belong to different components, and the table
      [WindowTable.dto] orders a write before a [wmb] and an [rmb] before
      a read, for both profiles [rc] ([fcat_cross_table]).  So neither
      pair is semi-independent ([zw_write_dependent],
      [read_zr_dependent]), and [rhb] keeps both same-thread edges.  The
      witness-level form of the litmus test is [mp_no_witness];
      [mp_witness_zr_sees_1] shows that the same shape with [zr() = 1] has
      a witness.
    - The two pairs of load buffering ([zr; write ‖ read; zw]) are
      semi-independent ([zr_write_independent], [read_zw_independent]), so
      [rhb] does not keep those edges.  This matches
      [SeqLockCOH.lb_allowed], and it shows that the overlay
      semi-independence is not empty.  Like every statement about all
      witnesses, the rules also hold for the empty semi-independence
      ([RelaxedTraceLin.rel_lin_mono]; by [rhb_mono], a witness for the
      empty relation is a witness for [findep rc]); what they depend on is
      that the two MP pairs are *not* semi-independent (Part 5 shows that
      the rules would be false if [zw]/[write] were semi-independent).  A
      client fact that depends on the nonempty part says that a behaviour
      is allowed (LB).  That the interface allows LB can be stated on a
      concrete overlay trace with a witness; this file does not state it.
      That the implementation exhibits LB needs a module execution (task
      SL-nonvac).

    Module semantics.  Three facts are proved here for any [VE] and [M];
    they would belong in [RelaxedModuleFacts].  In an execution from the
    initial configuration, a key is invoked at most once
    ([over_inv_unique]: each invocation leaves the record of its call, and
    records have distinct keys), a key responds at most once
    ([over_res_unique]: a finished call stays in the pool as [DeadCall],
    and the pool keeps one entry per key), and a key that responds was
    invoked ([over_res_invoked]).  Together: [over_trace_wf].

    Assumptions.  The hypotheses of every module-level theorem are exactly
    those of [seqlock_module_rel_lin] (or [_K]), plus client-shape
    hypotheses on the trace where the statement needs them:
    - only complete executions: [tm_queue c = []] and every overlay call
      is [DeadCall];
    - the underlay part of this execution is assumed relaxed linearizable
      w.r.t. the abstract specifications [SeqLockModule.nuEc]: the
      TicketLock with version counter ⊗ x ⊗ y ⊗ barriers, through
      [SeqLockCOH.pre]/[post] from [SeqLockCOH.init] (x = y = z = 0), and
      z as a register from 0.  The TicketLock is the abstract signature
      [plainTL] (or any [K] with [K_ok]);
    - initial values are fixed by the specifications: (0,0) for the
      SeqLock (ν_SeqLock) and 0 for z (ν_COH[z]);
    - client shapes: diagonal write invocations (equal pairs); invocation
      orders, the read's response and unique writers (message passing);
      for [seqlock_client_mp_forbidden], the overlay operations that occur
      are exactly the four listed ones, with pairwise distinct keys, as in
      [LockedRegistersWindow.sb_forbidden_window].

    Not shown here.
    - Joint satisfiability.  No module execution containing a [read], and
      no concurrent execution (for instance, a writer in parallel with a
      reader), is shown to meet the hypotheses.  The only non-vacuity
      witness of [seqlock_module_rel_lin] is a single write by a single
      thread over an underlay whose [Step] is [True]
      ([SeqLockModuleExample]).  This is task SL-nonvac.  The sanity
      checks above are at the level of specifications and witnesses only.
      Part 5 shows that the hypotheses of [client_rule_mp_order] and
      [client_rule_mp_zr_value] can all hold on an overlay trace with
      both same-thread overlaps.  This is at the interface level only:
      [mp_trace] is not shown to be the overlay part of a module
      execution.
    - The memory models.  The underlay is the abstract
      register/barrier/TicketLock specification, not a memory model of
      [memory/] (task SL-mem).  Response B4's "actual underlay semantics"
      is therefore not reached.  The theorems hold for every underlay LTS
      [VE] whose part of the execution is relaxed linearizable w.r.t.
      [nuEc], and no memory model is shown to have that property.
    - Incomplete executions.  An execution in which a [read] has returned
      while other calls are still pending is covered only if it extends to
      a complete execution whose underlay part is relaxed linearizable
      w.r.t. [nuEc].
    - A client program, a program logic, or a refinement theorem.  The
      client is described by hypotheses on the trace (which overlay
      operations are invoked, with which arguments and return values, and
      in which order inside each thread), not by a client program composed
      with the module.  Each client fact is derived directly from the
      sequential witness, not by an RLHL derivation and not through a
      contextual or observational refinement theorem (the development has
      none).  The module theorem comes from
      [WindowLinkTable.window_link_table], not from the program logic.
    - The SeqLock is the COH barrier variant of [SeqLockCOH] (rmb/wmb over
      abstract per-location registers, overlay categories write ↦ [Wmb],
      read ↦ [Rmb]).  It is not the paper's SeqLock over TSO cells, whose
      printed release/acquire signature [SeqLockCOH.paper_signature_fails]
      refutes. *)

From Stdlib Require Import List Bool Arith.PeanoNat PArith micromega.Lia.
From Stdlib Require Import Sorting.Permutation.
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
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.SeqLockProg.
Require Import examples.Relaxed.SeqLockModule.

Import ListNotations.

Module SeqLockClients.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedModuleFacts.
  Import SeqLockProg.SeqLockProg.

  Module BL := BracketedLink.BracketedLink.
  Module WC := WindowComposition.WindowComposition.
  Module SLM := SeqLockModule.SeqLockModule.

  (** ** Part 1: traces and the module semantics *)

  (** *** Positions in a trace *)

  Section TraceFacts.
    Context {G : RelaxedSig.t} {X : Type} (sel : X -> option (ThreadEvent G)).

    (** Each key is invoked at most once and responds at most once, and a
        key that responds was invoked.  Every overlay trace of the module
        semantics has these properties ([over_trace_wf]). *)
    Definition trace_wf (T : list X) : Prop :=
      (forall i i' k op op', inv_at sel T i k op -> inv_at sel T i' k op' -> i = i') /\
      (forall j j' k op op' ret ret', res_at sel T j k op ret -> res_at sel T j' k op' ret' -> j = j') /\
      (forall j k op ret, res_at sel T j k op ret -> exists i op', inv_at sel T i k op').

    Lemma inv_at_det T i k k' op op' :
      inv_at sel T i k op -> inv_at sel T i k' op' -> k = k' /\ op = op'.
    Proof.
      destruct k as [t h], k' as [t' h'].
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-. rewrite Hs in Hs'.
      apply (f_equal (option_map (fun ev => (te_key ev, event_op (te_ev G ev))))) in Hs'.
      cbn in Hs'. injection Hs' as -> -> ->. split; reflexivity.
    Qed.

    Lemma inv_res_distinct T i k k' op op' ret :
      inv_at sel T i k op -> res_at sel T i k' op' ret -> False.
    Proof.
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-.
      rewrite Hs in Hs'. discriminate Hs'.
    Qed.
  End TraceFacts.

  Lemma before_trans {A : Type} (l : list A) a b c :
    NoDup l -> before l a b -> before l b c -> before l a c.
  Proof.
    intros Hnd H1 H2.
    destruct (WC.before_i_trans l a b c Hnd (WC.before_to_i l a b H1) (WC.before_to_i l b c H2))
      as (i & j & Hij & Hi & Hj).
    exact (BL.nth_before l i j a c Hi Hj Hij).
  Qed.

  Lemma before_asym {A : Type} (l : list A) a b : NoDup l -> before l a b -> before l b a -> False.
  Proof.
    intros Hnd H1 H2.
    exact (WC.before_i_irrefl l a Hnd
             (WC.before_i_trans l a b a Hnd (WC.before_to_i l a b H1) (WC.before_to_i l b a H2))).
  Qed.

  (** *** Overlay events in the module semantics

      Generic in the underlay LTS and the module.  The proofs go through
      the instrumented semantics of [RelaxedModuleFacts]. *)

  Section ModuleFacts.
    Context {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F).

    Lemma finish_call_dead t h op ret (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' -> In (Build_CallEntry t h DeadCall) pool'.
    Proof. induction 1; cbn; auto. Qed.

    Definition over_key (e : @ITraceEvent E F) : option (CallKey F) :=
      match e with IOver ev => Some (te_key ev) | IUnder _ => None end.

    (** A key that has responded has a [DeadCall] entry in the pool. *)
    Lemma iexec_res_dead q0 IT ic :
      iexec VE M (iinitial VE q0) IT ic ->
      forall p t h op ret,
        nth_error IT p = Some (IOver (Build_ThreadEvent t (@ResEv F h op ret))) ->
        In (Build_CallEntry t h DeadCall) (ic_calls VE ic).
    Proof.
      induction 1 as [| tr c ev c' Hexec IH Hstep]; intros p t h op ret Hp.
      - destruct p; discriminate.
      - destruct Hstep as [t' h' op' q pool queue used log invs trace ret' Hfc Hm Hft
                          | cand q q' pool queue queue' used log invs Hsel Hlts
                          | t' h' op' ret' q pool pool' queue used log invs Hfin Hdone];
          cbn [ic_calls] in IH |- *;
          apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]].
        + right. exact (IH _ _ _ _ _ Hp).
        + discriminate He.
        + exact (IH _ _ _ _ _ Hp).
        + discriminate He.
        + destruct (finish_call_cases _ _ _ _ _ _ Hfin _ (IH _ _ _ _ _ Hp)) as [H | H];
            [exact H | discriminate H].
        + apply (f_equal over_key) in He. cbn in He. injection He as -> ->.
          exact (finish_call_dead _ _ _ _ _ _ Hfin).
    Qed.

    (** So no step after it is a second response with the same key: a
        return needs an [ActiveCall] entry, and the pool has one entry per
        key. *)
    Lemma istep_res_fresh q0 tr c n ev c' p t h op ret :
      iexec VE M (iinitial VE q0) tr c -> istep VE M n ev c c' ->
      nth_error tr p = Some (IOver (Build_ThreadEvent t (@ResEv F h op ret))) ->
      forall op' ret', ev <> IOver (Build_ThreadEvent t (@ResEv F h op' ret')).
    Proof.
      intros Hexec Hstep Hp op' ret' He.
      pose proof (iexec_res_dead q0 tr c Hexec p t h op ret Hp) as Hd.
      pose proof (ii_pool_nodup _ _ _ _ (iinv_reach VE M q0 tr c Hexec)) as Hwf.
      clear Hexec Hp. revert Hd Hwf He.
      destruct Hstep as [t' h' op'' q pool queue used log invs trace ret'' Hfc Hm Hft
                        | cand q q' pool queue queue' used log invs Hsel Hlts
                        | t' h' op'' ret'' q pool pool' queue used log invs Hfin Hdone];
        intros Hd Hwf He; cbn [ic_calls] in Hd, Hwf.
      - discriminate He.
      - discriminate He.
      - apply (f_equal over_key) in He. cbn in He. injection He as -> ->.
        pose proof (pool_entry_unique _ _ _ Hwf (finish_call_source _ _ _ _ _ _ Hfin) Hd eq_refl) as Heq.
        discriminate Heq.
    Qed.

    Lemma iexec_res_unique q0 IT ic :
      iexec VE M (iinitial VE q0) IT ic ->
      forall p p' t h op ret op' ret',
        nth_error IT p = Some (IOver (Build_ThreadEvent t (@ResEv F h op ret))) ->
        nth_error IT p' = Some (IOver (Build_ThreadEvent t (@ResEv F h op' ret'))) ->
        p = p'.
    Proof.
      induction 1 as [| tr c ev c' Hexec IH Hstep]; intros p p' t h op ret op' ret' Hp Hp'.
      - destruct p; discriminate.
      - apply nth_error_snoc_cases in Hp as [[_ Hp] | [-> He]];
          apply nth_error_snoc_cases in Hp' as [[_ Hp'] | [-> He']].
        + exact (IH _ _ _ _ _ _ _ _ Hp Hp').
        + exfalso. exact (istep_res_fresh q0 tr c _ ev c' p t h op ret Hexec Hstep Hp op' ret' (eq_sym He')).
        + exfalso. exact (istep_res_fresh q0 tr c _ ev c' p' t h op' ret' Hexec Hstep Hp' op ret (eq_sym He)).
        + reflexivity.
    Qed.

    (** In the trace of a module execution, a key responds at most once. *)
    Lemma over_res_unique q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      forall j j' k op op' ret ret',
        res_at BL.over_sel T j k op ret -> res_at BL.over_sel T j' k op' ret' -> j = j'.
    Proof.
      intros Hexec j j' k op op' ret ret' Hj Hj'.
      destruct (instrument VE M q0 T c Hexec) as (IT & ic & Hix & HT & _). subst T.
      apply (res_at_map ierase BL.over_sel IT) in Hj. apply (res_at_map ierase BL.over_sel IT) in Hj'.
      destruct Hj as (x & Hx & Hs). destruct Hj' as (x' & Hx' & Hs').
      destruct x as [y | ev]; cbn in Hs; [discriminate |].
      destruct x' as [y' | ev']; cbn in Hs'; [discriminate |].
      injection Hs as ->. injection Hs' as ->.
      exact (iexec_res_unique q0 IT ic Hix j j' (fst k) (snd k) op ret op' ret' Hx Hx').
    Qed.

    (** A key that responds was invoked. *)
    Lemma over_res_invoked q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      forall j k op ret, res_at BL.over_sel T j k op ret ->
        exists i op', inv_at BL.over_sel T i k op'.
    Proof.
      intros Hexec j k op ret Hj.
      destruct (instrument VE M q0 T c Hexec) as (IT & ic & Hix & HT & _). subst T.
      pose proof (iinv_reach VE M q0 IT ic Hix) as Hinv.
      apply (res_at_map ierase BL.over_sel IT) in Hj. destruct Hj as (x & Hx & Hs).
      destruct x as [y | ev]; cbn in Hs; [discriminate |]. injection Hs as ->.
      destruct (ii_over_res _ _ _ _ Hinv _ _ _ _ _ Hx) as (r & Hr & Hk).
      destruct (in_split _ _ Hr) as (pre & post & Hs).
      destruct (ii_pos _ _ _ _ Hinv pre r post Hs) as [Hpos _].
      exists (ir_pos r), (ir_op r). apply (inv_at_map ierase BL.over_sel IT).
      exists (IOver (Build_ThreadEvent (fst (ir_key r)) (@InvEv F (snd (ir_key r)) (ir_op r)))).
      split; [exact Hpos |]. cbn. rewrite Hk. reflexivity.
    Qed.

    (** A key is invoked at most once: each invocation leaves the record
        of its call, and records have distinct keys. *)
    Lemma over_inv_unique q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      forall i i' k op op', inv_at BL.over_sel T i k op -> inv_at BL.over_sel T i' k op' -> i = i'.
    Proof.
      intros Hexec i i' k op op' Hi Hi'.
      destruct (instrument VE M q0 T c Hexec) as (IT & ic & Hix & HT & _). subst T.
      pose proof (iinv_reach VE M q0 IT ic Hix) as Hinv.
      apply (inv_at_map ierase BL.over_sel IT) in Hi. apply (inv_at_map ierase BL.over_sel IT) in Hi'.
      destruct Hi as (x & Hx & Hs). destruct Hi' as (x' & Hx' & Hs').
      destruct x as [y | ev]; cbn in Hs; [discriminate |].
      destruct x' as [y' | ev']; cbn in Hs'; [discriminate |].
      injection Hs as ->. injection Hs' as ->.
      destruct (ii_over_inv _ _ _ _ Hinv _ _ _ _ Hx) as (r & Hr & Hk & _ & Hp).
      destruct (ii_over_inv _ _ _ _ Hinv _ _ _ _ Hx') as (r' & Hr' & Hk' & _ & Hp').
      rewrite <- Hp, <- Hp'. f_equal.
      apply (record_key_unique _ _ _ _ Hinv); [exact Hr | exact Hr' | congruence].
    Qed.

    Lemma over_trace_wf q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c -> trace_wf BL.over_sel T.
    Proof.
      intros Hexec. split; [| split].
      - exact (over_inv_unique q0 T c Hexec).
      - exact (over_res_unique q0 T c Hexec).
      - exact (over_res_invoked q0 T c Hexec).
    Qed.
  End ModuleFacts.

  (** ** Part 2: specification level *)

  (** *** Registers *)

  Section RegFacts.
    Context {V : Type} (owr ord : SL.OvEv -> option V).

    (** A read returns the value current when it is reached: the initial
        value, or the value of a write before it. *)
    Lemma reg_ok_read_src h1 h2 : forall cur rd vr,
      SL.reg_ok owr ord cur (h1 ++ rd :: h2) -> owr rd = None -> ord rd = Some vr ->
      vr = cur \/ exists w, In w h1 /\ owr w = Some vr.
    Proof.
      induction h1 as [| e h1 IH]; intros cur rd vr H Hw Hr; cbn in H.
      - rewrite Hw, Hr in H. left. exact (proj1 H).
      - revert H. destruct (owr e) as [u |] eqn:Ee; [| destruct (ord e) as [v' |]]; intros H.
        + destruct (IH u rd vr H Hw Hr) as [-> | (w & Hin & Hwv)].
          * right. exists e. split; [left; reflexivity | exact Ee].
          * right. exists w. split; [right; exact Hin | exact Hwv].
        + destruct (IH cur rd vr (proj2 H) Hw Hr) as [E | (w & Hin & Hwv)]; [left; exact E |].
          right. exists w. split; [right; exact Hin | exact Hwv].
        + destruct (IH cur rd vr H Hw Hr) as [E | (w & Hin & Hwv)]; [left; exact E |].
          right. exists w. split; [right; exact Hin | exact Hwv].
    Qed.

    Lemma reg_ok_suffix h1 h2 : forall cur,
      SL.reg_ok owr ord cur (h1 ++ h2) -> exists cur', SL.reg_ok owr ord cur' h2.
    Proof.
      induction h1 as [| e h1 IH]; intros cur H; [exists cur; exact H |]. cbn in H. revert H.
      destruct (owr e) as [u |]; [| destruct (ord e) as [v' |]]; intros H.
      - exact (IH u H).
      - exact (IH cur (proj2 H)).
      - exact (IH cur H).
    Qed.

    (** If every remaining write writes [u], every remaining read returns
        [u]. *)
    Lemma reg_ok_stable h : forall u, SL.reg_ok owr ord u h ->
      (forall e u', In e h -> owr e = Some u' -> u' = u) ->
      forall rd vr, In rd h -> owr rd = None -> ord rd = Some vr -> vr = u.
    Proof.
      induction h as [| e h IH]; intros u H Hw rd vr Hin Hr Hv; [destruct Hin |].
      assert (Hw' : forall e' u', In e' h -> owr e' = Some u' -> u' = u)
        by (intros e' u' He; apply Hw; right; exact He).
      cbn in H. destruct Hin as [<- | Hin].
      - rewrite Hr, Hv in H. exact (proj1 H).
      - revert H. destruct (owr e) as [u' |] eqn:Ee; [| destruct (ord e) as [v' |]]; intros H.
        + rewrite (Hw e u' (or_introl eq_refl) Ee) in H. exact (IH u H Hw' rd vr Hin Hr Hv).
        + exact (IH u (proj2 H) Hw' rd vr Hin Hr Hv).
        + exact (IH u H Hw' rd vr Hin Hr Hv).
    Qed.
  End RegFacts.

  Lemma sl_wr_OW e a b : SL.sl_wr e = Some (a, b) -> e = SL.OW a b.
  Proof. destruct e; cbn; intros H; try discriminate. injection H as -> ->. reflexivity. Qed.

  Lemma z_wr_OZW e u : SL.z_wr e = Some u -> e = SL.OZW u.
  Proof. destruct e; cbn; intros H; try discriminate. injection H as ->. reflexivity. Qed.

  (** *** The register of pairs

      Same epoch: a read of [SeqLockCOH.nu_sl] returns the current pair,
      i.e. the initial one or the pair of some write. *)

  Lemma reg_epoch (h : list SL.OvEv) cur a b :
    SL.reg_ok SL.sl_wr SL.sl_rd cur h -> In (SL.OR a b) h -> (a, b) = cur \/ In (SL.OW a b) h.
  Proof.
    intros H Hin. destruct (in_split _ _ Hin) as (h1 & h2 & ->).
    destruct (reg_ok_read_src SL.sl_wr SL.sl_rd h1 h2 cur (SL.OR a b) (a, b) H eq_refl eq_refl)
      as [E | (w & Hw & Ew)]; [left; exact E | right].
    apply in_or_app. left. rewrite <- (sl_wr_OW w a b Ew). exact Hw.
  Qed.

  Lemma nu_sl_epoch (h : list SL.OvEv) a b :
    SL.nu_sl h -> In (SL.OR a b) h -> (a, b) = (0, 0) \/ In (SL.OW a b) h.
  Proof. exact (reg_epoch h (0, 0) a b). Qed.

  (** (a) If every write is diagonal, so is every read. *)
  Lemma reg_diag (h : list SL.OvEv) : forall cur,
    fst cur = snd cur -> SL.reg_ok SL.sl_wr SL.sl_rd cur h ->
    (forall vx vy, In (SL.OW vx vy) h -> vx = vy) ->
    forall a b, In (SL.OR a b) h -> a = b.
  Proof.
    intros cur Hcur Hreg Hw a b Hin.
    destruct (reg_epoch h cur a b Hreg Hin) as [E | Hwr]; [| exact (Hw a b Hwr)].
    rewrite <- E in Hcur. exact Hcur.
  Qed.

  Lemma nu_sl_diag (h : list SL.OvEv) :
    SL.nu_sl h -> (forall vx vy, In (SL.OW vx vy) h -> vx = vy) ->
    forall a b, In (SL.OR a b) h -> a = b.
  Proof. intros Hnu. exact (reg_diag h (0, 0) eq_refl Hnu). Qed.

  (** The hypothesis on the writes is needed. *)
  Lemma nu_sl_nondiag : SL.nu_sl [SL.OW 1 2; SL.OR 1 2].
  Proof. cbn. tauto. Qed.

  (** *** Overlay histories *)

  Section Overlay.
    Context (rc : bool).

    Lemma ovev_OW (o : Op (F rc)) vx vy : SLM.ovev rc o = SL.OW vx vy -> op_op o = fWrite vx vy.
    Proof.
      destruct o as [k op ret]. destruct op; cbn; intros H; try discriminate.
      injection H as -> ->. reflexivity.
    Qed.

    Lemma ovev_OR (o : Op (F rc)) a b : SLM.ovev rc o = SL.OR a b -> op_op o = fRead.
    Proof. destruct o as [k op ret]. destruct op; cbn; intros H; try discriminate. reflexivity. Qed.

    Lemma ovev_OZW (o : Op (F rc)) v : SLM.ovev rc o = SL.OZW v -> op_op o = fZw v.
    Proof. destruct o as [k op ret]. destruct op; cbn; intros H; try discriminate. injection H as ->. reflexivity. Qed.

    Lemma ovev_OZR (o : Op (F rc)) v : SLM.ovev rc o = SL.OZR v -> op_op o = fZr.
    Proof. destruct o as [k op ret]. destruct op; cbn; intros H; try discriminate. reflexivity. Qed.

    Lemma ovev_zw (o : Op (F rc)) v : op_op o = fZw v -> SLM.ovev rc o = SL.OZW v.
    Proof. destruct o as [k op ret]. cbn. intros ->. reflexivity. Qed.

    (** Same epoch, on overlay histories, with the position of the write:
        a [read] that returns [(a,b)] returns the initial pair or follows a
        [write(a,b)]. *)
    Lemma nuF_all_read_src (W : list (Op (F rc))) :
      BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W ->
      forall o a b, In o W -> SLM.ovev rc o = SL.OR a b ->
        (a, b) = (0, 0) \/ exists w, In w W /\ op_op w = fWrite a b /\ before W w o.
    Proof.
      intros Hnu o a b Ho Hov.
      set (fS := fun o : Op (F rc) => if SL.comp_dec (fcomp (op_op o)) SL.CSL then true else false).
      assert (HoS : In o (filter fS W)).
      { apply filter_In. split; [exact Ho |]. unfold fS. rewrite (ovev_OR o a b Hov). reflexivity. }
      destruct (in_split _ _ HoS) as (P1 & P2 & EP).
      pose proof (Hnu SL.CSL) as HS. change (SL.nu_sl (map (SLM.ovev rc) (filter fS W))) in HS.
      unfold SL.nu_sl in HS. rewrite EP, map_app in HS. cbn [map] in HS. rewrite Hov in HS.
      destruct (reg_ok_read_src SL.sl_wr SL.sl_rd _ _ _ _ (a, b) HS eq_refl eq_refl) as [E | (e & He & Ee)];
        [left; exact E | right].
      apply in_map_iff in He as (w & <- & Hw).
      exists w. split; [| split].
      - assert (HwS : In w (filter fS W)) by (rewrite EP; apply in_or_app; left; exact Hw).
        apply filter_In in HwS. exact (proj1 HwS).
      - apply ovev_OW, sl_wr_OW, Ee.
      - apply (BL.before_filter_inv fS). rewrite EP.
        destruct (in_split _ _ Hw) as (P11 & P12 & ->).
        exists P11, (P12 ++ o :: P2). split; [rewrite <- app_assoc; reflexivity |].
        apply in_or_app. right. left. reflexivity.
    Qed.

    (** Same epoch on overlay histories. *)
    Lemma nuF_all_epoch (W : list (Op (F rc))) :
      BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W ->
      forall o a b, In o W -> SLM.ovev rc o = SL.OR a b ->
        (a, b) = (0, 0) \/ exists w, In w W /\ op_op w = fWrite a b.
    Proof.
      intros Hnu o a b Ho Hov.
      destruct (nuF_all_read_src W Hnu o a b Ho Hov) as [E | (w & Hw & Ew & _)];
        [left; exact E | right; exists w; split; assumption].
    Qed.

    (** (a) on overlay histories: a history legal for [nuF_all] whose
        [write] operations are diagonal has only diagonal [read]s. *)
    Lemma nuF_all_diag (W : list (Op (F rc))) :
      BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W ->
      (forall o vx vy, In o W -> op_op o = fWrite vx vy -> vx = vy) ->
      forall o a b, In o W -> SLM.ovev rc o = SL.OR a b -> a = b.
    Proof.
      intros Hnu Hw o a b Ho Hov.
      destruct (nuF_all_epoch W Hnu o a b Ho Hov) as [E | (w & Hw' & Ew)].
      - injection E as -> ->. reflexivity.
      - exact (Hw w a b Hw' Ew).
    Qed.

    (** z: a read placed after a write, when every z write writes [v],
        returns [v]. *)
    Lemma nuF_all_z_after (W : list (Op (F rc))) oz oq v r :
      BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W ->
      In oz W -> SLM.ovev rc oz = SL.OZW v -> In oq W -> SLM.ovev rc oq = SL.OZR r ->
      before W oz oq ->
      (forall w u, In w W -> SLM.ovev rc w = SL.OZW u -> u = v) ->
      r = v.
    Proof.
      intros Hnu Hoz Ez Hoq Eq Hb Hall.
      set (fZ := fun o : Op (F rc) => if SL.comp_dec (fcomp (op_op o)) SL.CZ then true else false).
      assert (Hb' : before (filter fZ W) oz oq).
      { apply BL.before_filter; [exact Hb | |]; unfold fZ;
          [rewrite (ovev_OZW oz v Ez) | rewrite (ovev_OZR oq r Eq)]; reflexivity. }
      destruct Hb' as (l1 & l2 & EP & Hl2).
      pose proof (Hnu SL.CZ) as HZ. change (SL.nu_z (map (SLM.ovev rc) (filter fZ W))) in HZ.
      unfold SL.nu_z in HZ. rewrite EP, map_app in HZ. cbn [map] in HZ.
      destruct (reg_ok_suffix SL.z_wr SL.z_rd _ _ _ HZ) as (cur & Hc).
      rewrite Ez in Hc. cbn in Hc.
      apply (reg_ok_stable SL.z_wr SL.z_rd (map (SLM.ovev rc) l2) v Hc) with (rd := SL.OZR r).
      - intros e u He Hu. apply in_map_iff in He as (w & <- & Hw).
        apply (Hall w u); [| apply z_wr_OZW, Hu].
        assert (HwZ : In w (filter fZ W)) by (rewrite EP; apply in_or_app; right; right; exact Hw).
        apply filter_In in HwZ. exact (proj1 HwZ).
      - rewrite <- Eq. apply in_map, Hl2.
      - reflexivity.
      - reflexivity.
    Qed.

    (** *** Which same-thread pairs across the two components are ordered

        [findep rc o o'] holds iff [o] and [o'] are in different
        components and [WT.dto rc (fcat o) (fcat o') = false].  Overlay
        categories: write ↦ [Wmb], read ↦ [Rmb], zw ↦ [DW], zr ↦ [DR].  The
        first two lines list the ordered cross pairs (earlier, later), the
        last two the unordered ones; the table is the same for both
        profiles. *)
    Lemma fcat_cross_table :
      WT.dto rc WT.DW WT.Wmb = true /\ WT.dto rc WT.Wmb WT.DW = true /\
      WT.dto rc WT.Rmb WT.DR = true /\ WT.dto rc WT.DR WT.Rmb = true /\
      WT.dto rc WT.DR WT.Wmb = false /\ WT.dto rc WT.Wmb WT.DR = false /\
      WT.dto rc WT.DW WT.Rmb = false /\ WT.dto rc WT.Rmb WT.DW = false.
    Proof. destruct rc; repeat split; reflexivity. Qed.

    Lemma zw_write_dependent v vx vy : ~ semi_independent (F rc) (fZw v) (fWrite vx vy).
    Proof.
      intros [_ H]. change (WT.dto rc WT.DW WT.Wmb = false) in H.
      rewrite (proj1 fcat_cross_table) in H. discriminate H.
    Qed.

    Lemma read_zr_dependent : ~ semi_independent (F rc) fRead fZr.
    Proof.
      intros [_ H]. change (WT.dto rc WT.Rmb WT.DR = false) in H.
      rewrite (proj1 (proj2 (proj2 fcat_cross_table))) in H. discriminate H.
    Qed.

    (** The two pairs of load buffering are semi-independent, so the
        overlay semi-independence is not empty. *)
    Lemma zr_write_independent vx vy : semi_independent (F rc) fZr (fWrite vx vy).
    Proof.
      destruct fcat_cross_table as (_ & _ & _ & _ & H & _).
      split; [intros E; discriminate E | exact H].
    Qed.

    Lemma read_zw_independent v : semi_independent (F rc) fRead (fZw v).
    Proof.
      destruct fcat_cross_table as (_ & _ & _ & _ & _ & _ & _ & H).
      split; [intros E; discriminate E | exact H].
    Qed.

    (** Two SeqLock operations are in the same component, hence never
        semi-independent. *)
    Lemma read_write_dependent vx vy : ~ semi_independent (F rc) fRead (fWrite vx vy).
    Proof. intros [H _]. apply H. reflexivity. Qed.

    (** *** (b) Message passing has no witness *)

    Definition mp_zw (k : CallKey (F rc)) : Op (F rc) := Build_Op (E := F rc) k (fZw 1) tt.
    Definition mp_wr (k : CallKey (F rc)) : Op (F rc) := Build_Op (E := F rc) k (fWrite 1 1) tt.
    Definition mp_rd (k : CallKey (F rc)) : Op (F rc) := Build_Op (E := F rc) k fRead (1, 1).
    Definition mp_zr (k : CallKey (F rc)) (v : nat) : Op (F rc) := Build_Op (E := F rc) k fZr v.

    (** A witness of the four operations that is legal for [nuF_all] and
        keeps the two same-thread edges does not exist: ν_SeqLock orders
        [write(1,1)] before [read() = (1,1)], ν_COH[z] orders [zr() = 0]
        before [zw(1)], and the four edges form a cycle. *)
    Lemma mp_no_witness (W : list (Op (F rc))) k1 k2 k3 k4 :
      NoDup [k1; k2; k3; k4] -> NoDup (map op_key W) ->
      (forall o, In o W <-> In o [mp_zw k1; mp_wr k2; mp_rd k3; mp_zr k4 0]) ->
      BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W ->
      before W (mp_zw k1) (mp_wr k2) -> before W (mp_rd k3) (mp_zr k4 0) -> False.
    Proof.
      intros Hk Hnd Hin Hnu B1 B3.
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      assert (Hperm : Permutation W [mp_zw k1; mp_wr k2; mp_rd k3; mp_zr k4 0]).
      { apply NoDup_Permutation; [exact HndW | apply (NoDup_map_inv op_key); exact Hk | exact Hin]. }
      assert (B2 : WC.before W (mp_wr k2) (mp_rd k3)).
      { apply (SL.two_order (SLM.ovev rc) SL.nu_sl
                 (fun o => if SL.comp_dec (fcomp (op_op o)) SL.CSL then true else false) W).
        - apply (Permutation_trans (WC.perm_filter _ _ _ Hperm)). apply Permutation_refl.
        - exact (Hnu SL.CSL).
        - cbn. intros [E _]. discriminate E. }
      assert (B4 : WC.before W (mp_zr k4 0) (mp_zw k1)).
      { apply (SL.two_order (SLM.ovev rc) SL.nu_z
                 (fun o => if SL.comp_dec (fcomp (op_op o)) SL.CZ then true else false) W).
        - apply (Permutation_trans (WC.perm_filter _ _ _ Hperm)). apply perm_swap.
        - exact (Hnu SL.CZ).
        - cbn. intros [E _]. discriminate E. }
      exact (SL.before_cycle W _ _ _ _ HndW B1 B2 B3 B4).
    Qed.

    (** The same shape with [zr() = 1] has such a witness: [mp_no_witness]
        depends on the value read from z. *)
    Lemma mp_witness_zr_sees_1 k1 k2 k3 k4 :
      NoDup [k1; k2; k3; k4] ->
      exists W : list (Op (F rc)),
        NoDup (map op_key W) /\
        (forall o, In o W <-> In o [mp_zw k1; mp_wr k2; mp_rd k3; mp_zr k4 1]) /\
        BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W /\
        before W (mp_zw k1) (mp_wr k2) /\ before W (mp_rd k3) (mp_zr k4 1).
    Proof.
      intros Hk. exists [mp_zw k1; mp_wr k2; mp_rd k3; mp_zr k4 1].
      split; [exact Hk |]. split; [intros o; reflexivity |]. split.
      - intros []; cbn; tauto.
      - split.
        + exists [], [mp_wr k2; mp_rd k3; mp_zr k4 1]. split; [reflexivity | left; reflexivity].
        + exists [mp_zw k1; mp_wr k2], [mp_zr k4 1]. split; [reflexivity | left; reflexivity].
    Qed.
  End Overlay.

  (** ** Part 3: client rules for the interface

      Each rule holds for any trace [T] with [trace_wf] and for every
      sequential witness [W] of [T]'s relaxed linearizability w.r.t.
      ν_SeqLock ⊗ ν_COH[z] (and, where [rhb] is used, [findep rc]).  None
      of them mentions the implementation of the SeqLock. *)

  (** The overlay event of a response. *)
  Definition res_ovev {rc} (ev : ThreadEvent (F rc)) : option SL.OvEv :=
    match te_ev _ ev with ResEv _ op v => Some (SLM.ovev_of op v) | InvEv _ _ => None end.

  Section Rules.
    Context (rc : bool) {X : Type} (sel : X -> option (ThreadEvent (F rc))).
    Local Abbreviation nuF := (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)).

    Lemma res_at_ovev T j k k' op op' ret ret' :
      res_at sel T j k op ret -> res_at sel T j k' op' ret' -> SLM.ovev_of op ret = SLM.ovev_of op' ret'.
    Proof.
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-. rewrite Hs in Hs'.
      apply (f_equal (fun oe => match oe with Some ev => res_ovev ev | None => None end)) in Hs'.
      cbn in Hs'. injection Hs' as Hs'. exact Hs'.
    Qed.

    Lemma witness_key_unique T indep nu W o o' :
      rel_lin_witness sel T indep nu W -> In o W -> In o' W -> op_key o = op_key o' -> o = o'.
    Proof. intros (_ & Hnd & _). apply (nodup_map_inj op_key W); assumption. Qed.

    (** The witness operation of an invocation. *)
    Lemma witness_inv T indep nu W :
      trace_wf sel T -> rel_lin_witness sel T indep nu W ->
      forall i k op, inv_at sel T i k op ->
        exists o, In o W /\ op_key o = k /\ op_op o = op /\ inv_at sel T i (op_key o) (op_op o).
    Proof.
      intros (Hiu & _ & _) (_ & _ & Hocc & Hall & _) i k op Hi.
      destruct (Hall i k op Hi) as (o & Ho & Hk).
      destruct (Hocc o Ho) as [(i' & Hi') _]. rewrite Hk in Hi'.
      pose proof (Hiu _ _ _ _ _ Hi Hi') as <-.
      destruct (inv_at_det sel T i k k op (op_op o) Hi Hi') as [_ Eop].
      exists o. split; [exact Ho |]. split; [exact Hk |]. split; [symmetry; exact Eop |].
      rewrite Hk. exact Hi'.
    Qed.

    (** The witness operation of a [read] response. *)
    Lemma witness_read T indep nu W :
      trace_wf sel T -> rel_lin_witness sel T indep nu W ->
      forall j k a b, res_at sel T j k fRead (a, b) ->
        exists o, In o W /\ op_key o = k /\ SLM.ovev rc o = SL.OR a b /\
          res_at sel T j (op_key o) (op_op o) (op_ret o).
    Proof.
      intros Hwf HW j k a b Hj. pose proof Hwf as (_ & Hru & Hri). pose proof HW as (_ & _ & Hocc & Hall & _).
      destruct (Hri j k fRead (a, b) Hj) as (i & op & Hi).
      destruct (Hall i k op Hi) as (o & Ho & Hk).
      destruct (Hocc o Ho) as [_ (j' & Hj')]. rewrite Hk in Hj'.
      pose proof (Hru _ _ _ _ _ _ _ Hj Hj') as <-.
      exists o. split; [exact Ho |]. split; [exact Hk |]. split.
      - symmetry. exact (res_at_ovev T j k k fRead (op_op o) (a, b) (op_ret o) Hj Hj').
      - rewrite Hk. exact Hj'.
    Qed.

    (** Same epoch.  It uses only the legality of the witness, not [rhb]. *)
    Lemma client_rule_same_epoch T indep W :
      trace_wf sel T -> rel_lin_witness sel T indep nuF W ->
      forall j k a b, res_at sel T j k fRead (a, b) ->
        (a, b) = (0, 0) \/ exists i k', inv_at sel T i k' (fWrite a b).
    Proof.
      intros Hwf HW j k a b Hj. pose proof HW as (Hnu & _ & Hocc & _ & _).
      destruct (witness_read T indep nuF W Hwf HW j k a b Hj) as (o & Ho & _ & Hov & _).
      destruct (nuF_all_epoch rc W Hnu o a b Ho Hov) as [E | (w & Hw & Ew)]; [left; exact E | right].
      destruct (Hocc w Hw) as [(i & Hi) _]. rewrite Ew in Hi. exists i, (op_key w). exact Hi.
    Qed.

    (** No read from the future.  The write that a [read] observes was
        invoked before the read responded (real-time clause of [rhb]), and,
        if it belongs to the reader's thread, before the read was invoked
        (same-thread clause of [rhb]; SeqLock operations are never
        semi-independent, so this holds even if the two calls overlap). *)
    Lemma client_rule_read_not_future T W :
      trace_wf sel T -> rel_lin_witness sel T (semi_independent (F rc)) nuF W ->
      forall j k a b, res_at sel T j k fRead (a, b) -> (a, b) <> (0, 0) ->
        exists i k', inv_at sel T i k' (fWrite a b) /\ i < j /\
          (fst k' = fst k -> forall i0 op0, inv_at sel T i0 k op0 -> i < i0).
    Proof.
      intros Hwf HW j k a b Hj Hab. pose proof Hwf as (Hiu & _ & _).
      pose proof HW as (Hnu & Hnd & Hocc & _ & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      destruct (witness_read T _ _ W Hwf HW j k a b Hj) as (o & Ho & Hk & Hov & Hro).
      destruct (nuF_all_read_src rc W Hnu o a b Ho Hov) as [E | (w & Hw & Ew & Hwo)]; [contradiction |].
      destruct (Hocc w Hw) as [(iw & Hiw) _].
      exists iw, (op_key w). split; [rewrite <- Ew; exact Hiw |]. split.
      - (* real-time clause: a write invoked after the read's response follows the read in [W] *)
        destruct (Nat.lt_trichotomy iw j) as [Hlt | [Heq | Hgt]]; [exact Hlt | |].
        + subst iw. exfalso. exact (inv_res_distinct sel T j _ _ _ _ _ Hiw Hro).
        + exfalso. apply (before_asym W w o HndW Hwo). apply (Hord o w Ho Hw).
          left. exists j, iw. split; [exact Hro |]. split; [exact Hiw | exact Hgt].
      - (* same-thread clause: a later write of the reader's thread follows the read in [W] *)
        intros Ht i0 op0 Hi0.
        destruct (Hocc o Ho) as [(io & Hio) _]. rewrite Hk in Hio.
        pose proof (Hiu _ _ _ _ _ Hi0 Hio) as <-. rewrite <- Hk in Hio.
        destruct (Nat.lt_trichotomy iw i0) as [Hlt | [Heq | Hgt]]; [exact Hlt | |].
        + subst iw. exfalso.
          destruct (inv_at_det sel T i0 _ _ _ _ Hiw Hio) as [Ekey _].
          rewrite (witness_key_unique T _ _ W w o HW Hw Ho Ekey) in Ew.
          rewrite (ovev_OR rc o a b Hov) in Ew. discriminate Ew.
        + exfalso. apply (before_asym W w o HndW Hwo). apply (Hord o w Ho Hw).
          right. split; [rewrite Hk; symmetry; exact Ht |].
          exists i0, iw. split; [exact Hio |]. split; [exact Hiw |]. split; [exact Hgt |].
          rewrite (ovev_OR rc o a b Hov), Ew. apply read_write_dependent.
    Qed.

    (** Message passing as an order on every witness.  Hypotheses on [T]
        only: [zw(v)]@kz is invoked before [write(x,y)]@kw in one thread,
        [read()]@kr is invoked before [zr()]@kq in one thread and returns
        [(x,y)] ≠ (0,0), and kw is the only key that invokes [write(x,y)].
        Nothing says that a call returns before the next one of its thread
        is invoked. *)
    Lemma client_rule_mp_order T W kz kw kr kq v x y jr :
      trace_wf sel T -> rel_lin_witness sel T (semi_independent (F rc)) nuF W ->
      fst kz = fst kw ->
      (exists i i', inv_at sel T i kz (fZw v) /\ inv_at sel T i' kw (fWrite x y) /\ i < i') ->
      fst kr = fst kq ->
      (exists i i', inv_at sel T i kr fRead /\ inv_at sel T i' kq fZr /\ i < i') ->
      res_at sel T jr kr fRead (x, y) -> (x, y) <> (0, 0) ->
      (forall i k, inv_at sel T i k (fWrite x y) -> k = kw) ->
      forall oz oq, In oz W -> op_key oz = kz -> In oq W -> op_key oq = kq -> before W oz oq.
    Proof.
      intros Hwf HW Hzw (iz & iw & Hiz & Hiw & Hlt1) Hrq (ir & iq & Hir & Hiq & Hlt2) Hjr Hxy Honly
             oz oq Hoz Ekz Hoq Ekq.
      pose proof HW as (Hnu & Hnd & Hocc & _ & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      (* the witness operations of the four keys *)
      destruct (witness_inv T _ _ W Hwf HW iz kz (fZw v) Hiz) as (oz' & Hoz' & Ekz' & Eoz & Hiz').
      assert (oz' = oz) as -> by (apply (witness_key_unique T _ _ W oz' oz HW Hoz' Hoz); congruence).
      destruct (witness_inv T _ _ W Hwf HW iw kw (fWrite x y) Hiw) as (ow & How & Ekw & Eow & Hiw').
      destruct (witness_read T _ _ W Hwf HW jr kr x y Hjr) as (or & Hor & Ekr & Eor & _).
      destruct (witness_inv T _ _ W Hwf HW iq kq fZr Hiq) as (oq' & Hoq' & Ekq' & Eoq & Hiq').
      assert (oq' = oq) as -> by (apply (witness_key_unique T _ _ W oq' oq HW Hoq' Hoq); congruence).
      (* zw before write: same thread, invocation order, not semi-independent *)
      assert (B1 : before W oz ow).
      { apply (Hord oz ow Hoz How). right. split; [rewrite Ekz', Ekw; exact Hzw |].
        exists iz, iw. split; [exact Hiz' |]. split; [exact Hiw' |]. split; [exact Hlt1 |].
        rewrite Eoz, Eow. apply zw_write_dependent. }
      (* read before zr: same thread, invocation order, not semi-independent *)
      assert (B3 : before W or oq).
      { apply (Hord or oq Hor Hoq). right. split; [rewrite Ekr, Ekq'; exact Hrq |].
        exists ir, iq. split.
        - rewrite Ekr, (ovev_OR rc or x y Eor). exact Hir.
        - split; [exact Hiq' |]. split; [exact Hlt2 |].
          rewrite (ovev_OR rc or x y Eor), Eoq. apply read_zr_dependent. }
      (* write before read: the read returns (x,y) ≠ (0,0), so it follows a
         write(x,y), and kw is the only one *)
      assert (B2 : before W ow or).
      { destruct (nuF_all_read_src rc W Hnu or x y Hor Eor) as [E | (w & Hw & Ew & Hwr)]; [contradiction |].
        destruct (Hocc w Hw) as [(i & Hi) _]. rewrite Ew in Hi.
        assert (Ewo : w = ow).
        { apply (witness_key_unique T _ _ W w ow HW Hw How). rewrite Ekw. exact (Honly _ _ Hi). }
        subst w. exact Hwr. }
      exact (before_trans W oz or oq HndW (before_trans W oz ow or HndW B1 B2) B3).
    Qed.

    (** If moreover kz is the only key that writes z, [zr()]@kq returns
        [v]. *)
    Lemma client_rule_mp_zr_value T W kz kw kr kq v x y jr :
      trace_wf sel T -> rel_lin_witness sel T (semi_independent (F rc)) nuF W ->
      fst kz = fst kw ->
      (exists i i', inv_at sel T i kz (fZw v) /\ inv_at sel T i' kw (fWrite x y) /\ i < i') ->
      fst kr = fst kq ->
      (exists i i', inv_at sel T i kr fRead /\ inv_at sel T i' kq fZr /\ i < i') ->
      res_at sel T jr kr fRead (x, y) -> (x, y) <> (0, 0) ->
      (forall i k, inv_at sel T i k (fWrite x y) -> k = kw) ->
      (forall i k v', inv_at sel T i k (fZw v') -> k = kz) ->
      forall jq r, res_at sel T jq kq fZr r -> r = v.
    Proof.
      intros Hwf HW Hzw Hzw' Hrq Hrq' Hjr Hxy Honly Hzonly jq r Hjq.
      pose proof Hwf as (_ & Hru & _). pose proof HW as (Hnu & _ & Hocc & _ & _).
      pose proof Hzw' as (iz & _ & Hiz & _ & _). pose proof Hrq' as (_ & iq & _ & Hiq & _).
      destruct (witness_inv T _ _ W Hwf HW iz kz (fZw v) Hiz) as (oz & Hoz & Ekz & Eoz & _).
      destruct (witness_inv T _ _ W Hwf HW iq kq fZr Hiq) as (oq & Hoq & Ekq & _ & _).
      pose proof (client_rule_mp_order T W kz kw kr kq v x y jr Hwf HW Hzw Hzw' Hrq Hrq' Hjr Hxy Honly
                    oz oq Hoz Ekz Hoq Ekq) as Hb.
      (* the response at [jq] is the response of [oq] *)
      destruct (Hocc oq Hoq) as [_ (jq' & Hjq')]. rewrite Ekq in Hjq'.
      pose proof (Hru _ _ _ _ _ _ _ Hjq Hjq') as <-.
      assert (Eq : SLM.ovev rc oq = SL.OZR r)
        by (symmetry; exact (res_at_ovev T jq kq kq fZr (op_op oq) r (op_ret oq) Hjq Hjq')).
      apply (nuF_all_z_after rc W oz oq v r Hnu Hoz (ovev_zw rc oz v Eoz) Hoq Eq Hb).
      (* every z write of the witness is the one at kz *)
      intros w u Hw Hwu. pose proof (ovev_OZW rc w u Hwu) as Ew.
      destruct (Hocc w Hw) as [(i & Hi) _]. rewrite Ew in Hi.
      assert (Ewz : w = oz).
      { apply (witness_key_unique T _ _ W w oz HW Hw Hoz). rewrite Ekz. exact (Hzonly _ _ _ Hi). }
      subst w. rewrite Eoz in Ew. injection Ew as ->. reflexivity.
    Qed.
  End Rules.

  (** ** Part 4: module-level client theorems *)

  (** *** Same epoch (overview.tex:276) *)

  Theorem seqlock_client_same_epoch_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) ->
      (a, b) = (0, 0) \/ exists i k', inv_at BL.over_sel T i k' (fWrite a b).
  Proof.
    intros Hexec Hq Hd Hunder.
    destruct (SLM.seqlock_module_rel_lin_K rc K HK VE q0 T c Hexec Hq Hd Hunder) as (W & HW).
    exact (client_rule_same_epoch rc BL.over_sel T _ W (over_trace_wf VE (M rc K) q0 T c Hexec) HW).
  Qed.

  Theorem seqlock_client_same_epoch rc (VE : LTS (E rc SL.plainTL)) q0 T c :
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) ->
      (a, b) = (0, 0) \/ exists i k', inv_at BL.over_sel T i k' (fWrite a b).
  Proof. exact (seqlock_client_same_epoch_K rc SL.plainTL SL.plainTL_ok VE q0 T c). Qed.

  (** *** Equal pairs (response B4) *)

  Theorem seqlock_client_equal_pairs_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    (forall i k vx vy, inv_at BL.over_sel T i k (fWrite vx vy) -> vx = vy) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) -> a = b.
  Proof.
    intros Hexec Hq Hd Hunder Hw j k a b Hj.
    destruct (seqlock_client_same_epoch_K rc K HK VE q0 T c Hexec Hq Hd Hunder j k a b Hj)
      as [E | (i & k' & Hi)].
    - injection E as -> ->. reflexivity.
    - exact (Hw i k' a b Hi).
  Qed.

  Theorem seqlock_client_equal_pairs rc (VE : LTS (E rc SL.plainTL)) q0 T c :
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) ->
    (forall i k vx vy, inv_at BL.over_sel T i k (fWrite vx vy) -> vx = vy) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) -> a = b.
  Proof. exact (seqlock_client_equal_pairs_K rc SL.plainTL SL.plainTL_ok VE q0 T c). Qed.

  (** *** No read from the future *)

  Theorem seqlock_client_read_not_future_po_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) -> (a, b) <> (0, 0) ->
      exists i k', inv_at BL.over_sel T i k' (fWrite a b) /\ i < j /\
        (fst k' = fst k -> forall i0 op0, inv_at BL.over_sel T i0 k op0 -> i < i0).
  Proof.
    intros Hexec Hq Hd Hunder.
    destruct (SLM.seqlock_module_rel_lin_K rc K HK VE q0 T c Hexec Hq Hd Hunder) as (W & HW).
    exact (client_rule_read_not_future rc BL.over_sel T W (over_trace_wf VE (M rc K) q0 T c Hexec) HW).
  Qed.

  Theorem seqlock_client_read_not_future_po rc (VE : LTS (E rc SL.plainTL)) q0 T c :
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) -> (a, b) <> (0, 0) ->
      exists i k', inv_at BL.over_sel T i k' (fWrite a b) /\ i < j /\
        (fst k' = fst k -> forall i0 op0, inv_at BL.over_sel T i0 k op0 -> i < i0).
  Proof. exact (seqlock_client_read_not_future_po_K rc SL.plainTL SL.plainTL_ok VE q0 T c). Qed.

  (** Real-time clause only. *)
  Theorem seqlock_client_read_not_future_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) -> (a, b) <> (0, 0) ->
      exists i k', inv_at BL.over_sel T i k' (fWrite a b) /\ i < j.
  Proof.
    intros Hexec Hq Hd Hunder j k a b Hj Hab.
    destruct (seqlock_client_read_not_future_po_K rc K HK VE q0 T c Hexec Hq Hd Hunder j k a b Hj Hab)
      as (i & k' & Hi & Hlt & _).
    exists i, k'. split; assumption.
  Qed.

  Theorem seqlock_client_read_not_future rc (VE : LTS (E rc SL.plainTL)) q0 T c :
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) ->
    forall j k a b, res_at BL.over_sel T j k fRead (a, b) -> (a, b) <> (0, 0) ->
      exists i k', inv_at BL.over_sel T i k' (fWrite a b) /\ i < j.
  Proof. exact (seqlock_client_read_not_future_K rc SL.plainTL SL.plainTL_ok VE q0 T c). Qed.

  (** *** Message passing *)

  (** The overlay part is relaxed linearizable, and every witness places
      the z write at kz before the z read at kq.  The universal part is
      [client_rule_mp_order] with [over_trace_wf] and does not use the
      module theorem; the module theorem gives only the existence of a
      witness.  Every witness contains an operation with key kz and one
      with key kq ([witness_inv]), so the universal part is not vacuous.
      This is a fact about witnesses; the observable consequence is
      [seqlock_client_mp_zr_value]. *)
  Theorem seqlock_client_mp_order_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c
      (kz kw kr kq : CallKey (F rc)) v x y jr :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    fst kz = fst kw ->
    (exists i i', inv_at BL.over_sel T i kz (fZw v) /\ inv_at BL.over_sel T i' kw (fWrite x y) /\ i < i') ->
    fst kr = fst kq ->
    (exists i i', inv_at BL.over_sel T i kr fRead /\ inv_at BL.over_sel T i' kq fZr /\ i < i') ->
    res_at BL.over_sel T jr kr fRead (x, y) -> (x, y) <> (0, 0) ->
    (forall i k, inv_at BL.over_sel T i k (fWrite x y) -> k = kw) ->
    rel_lin BL.over_sel T (semi_independent (F rc))
      (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)) /\
    (forall W, rel_lin_witness BL.over_sel T (semi_independent (F rc))
                 (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)) W ->
       forall oz oq, In oz W -> op_key oz = kz -> In oq W -> op_key oq = kq -> before W oz oq).
  Proof.
    intros Hexec Hq Hd Hunder Hzw Hzw' Hrq Hrq' Hjr Hxy Honly. split.
    - exact (SLM.seqlock_module_rel_lin_K rc K HK VE q0 T c Hexec Hq Hd Hunder).
    - intros W HW.
      exact (client_rule_mp_order rc BL.over_sel T W kz kw kr kq v x y jr
               (over_trace_wf VE (M rc K) q0 T c Hexec) HW Hzw Hzw' Hrq Hrq' Hjr Hxy Honly).
  Qed.

  Theorem seqlock_client_mp_order rc (VE : LTS (E rc SL.plainTL)) q0 T c
      (kz kw kr kq : CallKey (F rc)) v x y jr :
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) ->
    fst kz = fst kw ->
    (exists i i', inv_at BL.over_sel T i kz (fZw v) /\ inv_at BL.over_sel T i' kw (fWrite x y) /\ i < i') ->
    fst kr = fst kq ->
    (exists i i', inv_at BL.over_sel T i kr fRead /\ inv_at BL.over_sel T i' kq fZr /\ i < i') ->
    res_at BL.over_sel T jr kr fRead (x, y) -> (x, y) <> (0, 0) ->
    (forall i k, inv_at BL.over_sel T i k (fWrite x y) -> k = kw) ->
    rel_lin BL.over_sel T (semi_independent (F rc))
      (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)) /\
    (forall W, rel_lin_witness BL.over_sel T (semi_independent (F rc))
                 (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)) W ->
       forall oz oq, In oz W -> op_key oz = kz -> In oq W -> op_key oq = kq -> before W oz oq).
  Proof. exact (seqlock_client_mp_order_K rc SL.plainTL SL.plainTL_ok VE q0 T c kz kw kr kq v x y jr). Qed.

  (** The z read returns the value of the z write. *)
  Theorem seqlock_client_mp_zr_value_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c
      (kz kw kr kq : CallKey (F rc)) v x y jr :
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    fst kz = fst kw ->
    (exists i i', inv_at BL.over_sel T i kz (fZw v) /\ inv_at BL.over_sel T i' kw (fWrite x y) /\ i < i') ->
    fst kr = fst kq ->
    (exists i i', inv_at BL.over_sel T i kr fRead /\ inv_at BL.over_sel T i' kq fZr /\ i < i') ->
    res_at BL.over_sel T jr kr fRead (x, y) -> (x, y) <> (0, 0) ->
    (forall i k, inv_at BL.over_sel T i k (fWrite x y) -> k = kw) ->
    (forall i k v', inv_at BL.over_sel T i k (fZw v') -> k = kz) ->
    forall jq r, res_at BL.over_sel T jq kq fZr r -> r = v.
  Proof.
    intros Hexec Hq Hd Hunder.
    destruct (SLM.seqlock_module_rel_lin_K rc K HK VE q0 T c Hexec Hq Hd Hunder) as (W & HW).
    exact (client_rule_mp_zr_value rc BL.over_sel T W kz kw kr kq v x y jr
             (over_trace_wf VE (M rc K) q0 T c Hexec) HW).
  Qed.

  Theorem seqlock_client_mp_zr_value rc (VE : LTS (E rc SL.plainTL)) q0 T c
      (kz kw kr kq : CallKey (F rc)) v x y jr :
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) ->
    fst kz = fst kw ->
    (exists i i', inv_at BL.over_sel T i kz (fZw v) /\ inv_at BL.over_sel T i' kw (fWrite x y) /\ i < i') ->
    fst kr = fst kq ->
    (exists i i', inv_at BL.over_sel T i kr fRead /\ inv_at BL.over_sel T i' kq fZr /\ i < i') ->
    res_at BL.over_sel T jr kr fRead (x, y) -> (x, y) <> (0, 0) ->
    (forall i k, inv_at BL.over_sel T i k (fWrite x y) -> k = kw) ->
    (forall i k v', inv_at BL.over_sel T i k (fZw v') -> k = kz) ->
    forall jq r, res_at BL.over_sel T jq kq fZr r -> r = v.
  Proof. exact (seqlock_client_mp_zr_value_K rc SL.plainTL SL.plainTL_ok VE q0 T c kz kw kr kq v x y jr). Qed.

  (** The litmus test, from [seqlock_client_mp_zr_value_K]: the four
      operations give the unique writers, and [zr()] would have to return
      1. *)
  Theorem seqlock_client_mp_forbidden_K rc K (HK : SL.K_ok K = true) (VE : LTS (E rc K)) q0 T c
      (k1 k2 k3 k4 : CallKey (F rc)) :
    fst k1 = fst k2 -> fst k3 = fst k4 -> NoDup [k1; k2; k3; k4] ->
    module_execution_tagged VE (M rc K) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc K))
      (BL.nuE_all (E := E rc K) SL.comp_dec SLM.compE (SLM.nuEc rc K)) ->
    (forall o, occurs BL.over_sel T o <-> In o [mp_zw rc k1; mp_wr rc k2; mp_rd rc k3; mp_zr rc k4 0]) ->
    (exists i j, inv_at BL.over_sel T i k1 (fZw 1) /\ inv_at BL.over_sel T j k2 (fWrite 1 1) /\ i < j) ->
    (exists i j, inv_at BL.over_sel T i k3 fRead /\ inv_at BL.over_sel T j k4 fZr /\ i < j) ->
    False.
  Proof.
    intros Ht12 Ht34 Hkeys Hexec Hq Hd Hunder Hops H12 H34.
    pose proof (over_trace_wf VE (M rc K) q0 T c Hexec) as Hwf.
    (* every invocation of [T] is the invocation of one of the four operations *)
    assert (Hop : forall i k op, inv_at BL.over_sel T i k op ->
                    exists o, In o [mp_zw rc k1; mp_wr rc k2; mp_rd rc k3; mp_zr rc k4 0] /\
                              op_key o = k /\ op_op o = op).
    { intros i k op Hi.
      destruct (SLM.seqlock_module_rel_lin_K rc K HK VE q0 T c Hexec Hq Hd Hunder) as (W & HW).
      destruct (witness_inv rc BL.over_sel T _ _ W Hwf HW i k op Hi) as (o & Ho & Ek & Eop & _).
      pose proof HW as (_ & _ & Hocc & _ & _).
      exists o. split; [apply Hops, Hocc, Ho | split; assumption]. }
    assert (Honly_w : forall i k, inv_at BL.over_sel T i k (fWrite 1 1) -> k = k2).
    { intros i k Hi. destruct (Hop i k _ Hi) as (o & Ho & Ek & Eop).
      destruct Ho as [<- | [<- | [<- | [<- | []]]]]; cbn in Ek, Eop; try discriminate Eop.
      symmetry. exact Ek. }
    assert (Honly_z : forall i k v', inv_at BL.over_sel T i k (fZw v') -> k = k1).
    { intros i k v' Hi. destruct (Hop i k _ Hi) as (o & Ho & Ek & Eop).
      destruct Ho as [<- | [<- | [<- | [<- | []]]]]; cbn in Ek, Eop; try discriminate Eop.
      symmetry. exact Ek. }
    destruct (proj2 (Hops (mp_rd rc k3)) ltac:(cbn; tauto)) as [_ (jr & Hjr)].
    destruct (proj2 (Hops (mp_zr rc k4 0)) ltac:(cbn; tauto)) as [_ (jq & Hjq)].
    pose proof (seqlock_client_mp_zr_value_K rc K HK VE q0 T c k1 k2 k3 k4 1 1 1 jr Hexec Hq Hd Hunder
                  Ht12 H12 Ht34 H34 Hjr ltac:(discriminate) Honly_w Honly_z jq 0 Hjq) as E.
    discriminate E.
  Qed.

  Theorem seqlock_client_mp_forbidden rc (VE : LTS (E rc SL.plainTL)) q0 T c (k1 k2 k3 k4 : CallKey (F rc)) :
    fst k1 = fst k2 -> fst k3 = fst k4 -> NoDup [k1; k2; k3; k4] ->
    module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
    tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
    rel_lin BL.under_sel T (semi_independent (E rc SL.plainTL))
      (BL.nuE_all (E := E rc SL.plainTL) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)) ->
    (forall o, occurs BL.over_sel T o <-> In o [mp_zw rc k1; mp_wr rc k2; mp_rd rc k3; mp_zr rc k4 0]) ->
    (exists i j, inv_at BL.over_sel T i k1 (fZw 1) /\ inv_at BL.over_sel T j k2 (fWrite 1 1) /\ i < j) ->
    (exists i j, inv_at BL.over_sel T i k3 fRead /\ inv_at BL.over_sel T j k4 fZr /\ i < j) ->
    False.
  Proof. exact (seqlock_client_mp_forbidden_K rc SL.plainTL SL.plainTL_ok VE q0 T c k1 k2 k3 k4). Qed.

  (** ** Part 5: the message-passing rules on a concrete overlay trace

      A list of overlay events with selector [Some], not a module
      execution.  Thread 1 invokes [zw(1)] and then [write(1,1)] before
      [zw(1)] responds; thread 2 invokes [read()] and then [zr()] before
      [read()] responds.  All four invocations come before all four
      responses, so the real-time clause of [rhb] orders nothing.  The
      order that the rules derive comes from the same-thread clause of
      [rhb] with the table (zw before write, read before zr) and from
      ν_SeqLock (write before read). *)

  Section MPInstance.
    Context (rc : bool).
    Local Abbreviation nuF := (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)).

    Definition mp_k1 : CallKey (F rc) := (1%positive, 0).
    Definition mp_k2 : CallKey (F rc) := (1%positive, 1).
    Definition mp_k3 : CallKey (F rc) := (2%positive, 0).
    Definition mp_k4 : CallKey (F rc) := (2%positive, 1).

    (** [read()] returns (1,1) and [zr()] returns [r]. *)
    Definition mp_trace (r : nat) : list (ThreadEvent (F rc)) :=
      [ Build_ThreadEvent 1%positive (InvEv (E := F rc) 0 (fZw 1));
        Build_ThreadEvent 1%positive (InvEv (E := F rc) 1 (fWrite 1 1));
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 0 fRead);
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 1 fZr);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 0 (fZw 1) tt);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 1 (fWrite 1 1) tt);
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 0 fRead (1, 1));
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 1 fZr r) ].

    Lemma mp_inv_at r i k op :
      inv_at Some (mp_trace r) i k op ->
      (i = 0 /\ k = mp_k1 /\ op = fZw 1) \/ (i = 1 /\ k = mp_k2 /\ op = fWrite 1 1) \/
      (i = 2 /\ k = mp_k3 /\ op = fRead) \/ (i = 3 /\ k = mp_k4 /\ op = fZr).
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x. cbn [fst snd] in Hx.
      do 8 (destruct i as [| i]; cbn in Hx;
            [ first [ discriminate Hx
                    | injection Hx as Hx; intros; subst;
                      repeat first [left; repeat split; reflexivity | right]; repeat split ] |]).
      destruct i; discriminate Hx.
    Qed.

    Lemma mp_res_at r j k op ret :
      res_at Some (mp_trace r) j k op ret ->
      (j = 4 /\ k = mp_k1) \/ (j = 5 /\ k = mp_k2) \/ (j = 6 /\ k = mp_k3) \/ (j = 7 /\ k = mp_k4).
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x. cbn [fst snd] in Hx.
      do 8 (destruct j as [| j]; cbn in Hx;
            [ first [ discriminate Hx
                    | apply (f_equal (option_map te_key)) in Hx; cbn in Hx; injection Hx as Hx; intros; subst;
                      repeat first [left; repeat split; reflexivity | right]; repeat split ] |]).
      destruct j; discriminate Hx.
    Qed.

    Lemma mp_trace_wf r : trace_wf Some (mp_trace r).
    Proof.
      split; [| split].
      - intros i i' k op op' Hi Hi'.
        apply mp_inv_at in Hi, Hi'.
        destruct Hi as [(-> & -> & _) | [(-> & -> & _) | [(-> & -> & _) | (-> & -> & _)]]];
        destruct Hi' as [(-> & Hk & _) | [(-> & Hk & _) | [(-> & Hk & _) | (-> & Hk & _)]]];
        try reflexivity; discriminate Hk.
      - intros j j' k op op' ret ret' Hj Hj'.
        apply mp_res_at in Hj, Hj'.
        destruct Hj as [(-> & ->) | [(-> & ->) | [(-> & ->) | (-> & ->)]]];
        destruct Hj' as [(-> & Hk) | [(-> & Hk) | [(-> & Hk) | (-> & Hk)]]];
        try reflexivity; discriminate Hk.
      - intros j k op ret Hj. apply mp_res_at in Hj.
        destruct Hj as [(_ & ->) | [(_ & ->) | [(_ & ->) | (_ & ->)]]].
        + exists 0, (fZw 1). eexists. split; reflexivity.
        + exists 1, (fWrite 1 1). eexists. split; reflexivity.
        + exists 2, fRead. eexists. split; reflexivity.
        + exists 3, fZr. eexists. split; reflexivity.
    Qed.

    (** Both same-thread pairs overlap: [write(1,1)] is invoked before
        [zw(1)] responds, and [zr()] before [read()] responds. *)
    Lemma mp_trace_overlap r :
      (exists i j, inv_at Some (mp_trace r) i mp_k2 (fWrite 1 1) /\
                   res_at Some (mp_trace r) j mp_k1 (fZw 1) tt /\ i < j) /\
      (exists i j, inv_at Some (mp_trace r) i mp_k4 fZr /\
                   res_at Some (mp_trace r) j mp_k3 fRead (1, 1) /\ i < j).
    Proof.
      split.
      - exists 1, 4. split; [eexists; split; reflexivity |]. split; [eexists; split; reflexivity | lia].
      - exists 3, 6. split; [eexists; split; reflexivity |]. split; [eexists; split; reflexivity | lia].
    Qed.

    (** Every invocation precedes every response, so the real-time clause
        of [rhb] orders no pair. *)
    Lemma mp_trace_no_realtime r i k op ret j k' op' :
      res_at Some (mp_trace r) i k op ret -> inv_at Some (mp_trace r) j k' op' -> j < i.
    Proof.
      intros Hi Hj. apply mp_res_at in Hi. apply mp_inv_at in Hj.
      destruct Hi as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]];
      destruct Hj as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]]; lia.
    Qed.

    (** So, for any [indep], [rhb] keeps at most the two same-thread
        edges, each only if its pair is not in [indep]. *)
    Lemma mp_rhb r indep o o' :
      rhb Some (mp_trace r) indep o o' ->
      (op_key o = mp_k1 /\ op_key o' = mp_k2 /\ ~ indep (op_op o) (op_op o')) \/
      (op_key o = mp_k3 /\ op_key o' = mp_k4 /\ ~ indep (op_op o) (op_op o')).
    Proof.
      intros [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
      - exfalso. pose proof (mp_trace_no_realtime _ _ _ _ _ _ _ _ Hi Hj). lia.
      - apply mp_inv_at in Hi, Hj.
        destruct Hi as [(-> & Hk & _) | [(-> & Hk & _) | [(-> & Hk & _) | (-> & Hk & _)]]];
        destruct Hj as [(-> & Hk' & _) | [(-> & Hk' & _) | [(-> & Hk' & _) | (-> & Hk' & _)]]];
        try lia; rewrite Hk, Hk' in Ht; cbv [mp_k1 mp_k2 mp_k3 mp_k4 fst] in Ht; try discriminate Ht;
        [left | right]; repeat split; assumption.
    Qed.

    (** A witness: program order in each thread, the write before the
        read. *)
    Definition mp_lin (r : nat) : list (Op (F rc)) :=
      [mp_zw rc mp_k1; mp_wr rc mp_k2; mp_rd rc mp_k3; mp_zr rc mp_k4 r].

    Lemma mp_trace_witness :
      rel_lin_witness Some (mp_trace 1) (semi_independent (F rc)) nuF (mp_lin 1).
    Proof.
      split; [| split; [| split; [| split]]].
      - intros []; cbn; tauto.
      - cbn. repeat constructor; cbn; intuition discriminate.
      - intros o Ho. destruct Ho as [<- | [<- | [<- | [<- | []]]]]; split.
        + exists 0. eexists. split; reflexivity.
        + exists 4. eexists. split; reflexivity.
        + exists 1. eexists. split; reflexivity.
        + exists 5. eexists. split; reflexivity.
        + exists 2. eexists. split; reflexivity.
        + exists 6. eexists. split; reflexivity.
        + exists 3. eexists. split; reflexivity.
        + exists 7. eexists. split; reflexivity.
      - intros i k op Hi. apply mp_inv_at in Hi.
        destruct Hi as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]].
        + exists (mp_zw rc mp_k1). split; [left | ]; reflexivity.
        + exists (mp_wr rc mp_k2). split; [right; left | ]; reflexivity.
        + exists (mp_rd rc mp_k3). split; [right; right; left | ]; reflexivity.
        + exists (mp_zr rc mp_k4 1). split; [right; right; right; left | ]; reflexivity.
      - intros o o' Ho Ho' Hr. apply mp_rhb in Hr.
        destruct Hr as [(Hk & Hk' & _) | (Hk & Hk' & _)];
        destruct Ho as [<- | [<- | [<- | [<- | []]]]]; try discriminate Hk;
        destruct Ho' as [<- | [<- | [<- | [<- | []]]]]; try discriminate Hk'.
        + apply (BL.nth_before _ 0 1); [reflexivity | reflexivity | lia].
        + apply (BL.nth_before _ 2 3); [reflexivity | reflexivity | lia].
    Qed.

    (** Every hypothesis of [client_rule_mp_order] and
        [client_rule_mp_zr_value] other than the witness holds on
        [mp_trace r], for every [r] (kz, kw, kr, kq = [mp_k1] .. [mp_k4],
        v = x = y = 1, jr = 6). *)
    Lemma mp_trace_rule_hyps r :
      trace_wf Some (mp_trace r) /\
      fst mp_k1 = fst mp_k2 /\
      (exists i i', inv_at Some (mp_trace r) i mp_k1 (fZw 1) /\
                    inv_at Some (mp_trace r) i' mp_k2 (fWrite 1 1) /\ i < i') /\
      fst mp_k3 = fst mp_k4 /\
      (exists i i', inv_at Some (mp_trace r) i mp_k3 fRead /\ inv_at Some (mp_trace r) i' mp_k4 fZr /\ i < i') /\
      res_at Some (mp_trace r) 6 mp_k3 fRead (1, 1) /\ (1, 1) <> (0, 0) /\
      (forall i k, inv_at Some (mp_trace r) i k (fWrite 1 1) -> k = mp_k2) /\
      (forall i k v', inv_at Some (mp_trace r) i k (fZw v') -> k = mp_k1).
    Proof.
      split; [exact (mp_trace_wf r) |]. split; [reflexivity |]. split.
      { exists 0, 1. split; [eexists; split; reflexivity |]. split; [eexists; split; reflexivity | lia]. }
      split; [reflexivity |]. split.
      { exists 2, 3. split; [eexists; split; reflexivity |]. split; [eexists; split; reflexivity | lia]. }
      split; [eexists; split; reflexivity |]. split; [discriminate |]. split.
      - intros i k Hi. apply mp_inv_at in Hi.
        destruct Hi as [(_ & _ & E) | [(_ & -> & _) | [(_ & _ & E) | (_ & _ & E)]]];
          [discriminate E | reflexivity | discriminate E | discriminate E].
      - intros i k v' Hi. apply mp_inv_at in Hi.
        destruct Hi as [(_ & -> & _) | [(_ & _ & E) | [(_ & _ & E) | (_ & _ & E)]]];
          [reflexivity | discriminate E | discriminate E | discriminate E].
    Qed.

    (** The rules on [mp_trace 1]: it is relaxed linearizable, and every
        witness places [zw(1)] before [zr()] and has [zr()] return 1. *)
    Lemma mp_trace_rule_instance :
      rel_lin Some (mp_trace 1) (semi_independent (F rc)) nuF /\
      (forall W, rel_lin_witness Some (mp_trace 1) (semi_independent (F rc)) nuF W ->
         (forall oz oq, In oz W -> op_key oz = mp_k1 -> In oq W -> op_key oq = mp_k4 -> before W oz oq) /\
         (forall jq r, res_at Some (mp_trace 1) jq mp_k4 fZr r -> r = 1)).
    Proof.
      destruct (mp_trace_rule_hyps 1) as (Hwf & H12 & H12' & H34 & H34' & Hjr & Hxy & Hw & Hz).
      split; [exists (mp_lin 1); exact mp_trace_witness |]. intros W HW. split.
      - exact (client_rule_mp_order rc Some (mp_trace 1) W mp_k1 mp_k2 mp_k3 mp_k4 1 1 1 6
                 Hwf HW H12 H12' H34 H34' Hjr Hxy Hw).
      - exact (client_rule_mp_zr_value rc Some (mp_trace 1) W mp_k1 mp_k2 mp_k3 mp_k4 1 1 1 6
                 Hwf HW H12 H12' H34 H34' Hjr Hxy Hw Hz).
    Qed.

    (** The forbidden outcome: with [zr() = 0] the trace has no witness. *)
    Lemma mp_trace_zr0_not_rel_lin : ~ rel_lin Some (mp_trace 0) (semi_independent (F rc)) nuF.
    Proof.
      intros (W & HW).
      destruct (mp_trace_rule_hyps 0) as (Hwf & H12 & H12' & H34 & H34' & Hjr & Hxy & Hw & Hz).
      assert (Hq : res_at Some (mp_trace 0) 7 mp_k4 fZr 0) by (eexists; split; reflexivity).
      pose proof (client_rule_mp_zr_value rc Some (mp_trace 0) W mp_k1 mp_k2 mp_k3 mp_k4 1 1 1 6
                    Hwf HW H12 H12' H34 H34' Hjr Hxy Hw Hz 7 0 Hq) as E.
      discriminate E.
    Qed.

    (** The rules depend on the table.  Add the pairs ([zw], [write]) to
        the semi-independence of [F rc], as if [WT.dto rc WT.DW WT.Wmb]
        were false.  Then [mp_trace 0], which meets every hypothesis of the
        rules other than the witness ([mp_trace_rule_hyps 0]), has a
        witness for the larger relation in which [zr() = 0] precedes
        [zw(1)].  So the two rules, stated for that relation, would be
        false: kz is not before kq, and [zr()] returns 0, not 1. *)
    Definition zw_write_indep (o o' : FOp) : Prop :=
      semi_independent (F rc) o o' \/ exists v x y, o = fZw v /\ o' = fWrite x y.

    Definition mp_lin_zw_last : list (Op (F rc)) :=
      [mp_wr rc mp_k2; mp_rd rc mp_k3; mp_zr rc mp_k4 0; mp_zw rc mp_k1].

    Lemma mp_trace_zr0_zw_write_indep :
      rel_lin_witness Some (mp_trace 0) zw_write_indep nuF mp_lin_zw_last /\
      before mp_lin_zw_last (mp_zr rc mp_k4 0) (mp_zw rc mp_k1) /\
      ~ before mp_lin_zw_last (mp_zw rc mp_k1) (mp_zr rc mp_k4 0).
    Proof.
      assert (Hnd : NoDup (map op_key mp_lin_zw_last)) by (cbn; repeat constructor; cbn; intuition discriminate).
      assert (Hb : before mp_lin_zw_last (mp_zr rc mp_k4 0) (mp_zw rc mp_k1))
        by (apply (BL.nth_before _ 2 3); [reflexivity | reflexivity | lia]).
      split; [| split; [exact Hb |]].
      - split; [| split; [exact Hnd | split; [| split]]].
        + intros []; cbn; tauto.
        + intros o Ho. destruct Ho as [<- | [<- | [<- | [<- | []]]]]; split.
          * exists 1. eexists. split; reflexivity.
          * exists 5. eexists. split; reflexivity.
          * exists 2. eexists. split; reflexivity.
          * exists 6. eexists. split; reflexivity.
          * exists 3. eexists. split; reflexivity.
          * exists 7. eexists. split; reflexivity.
          * exists 0. eexists. split; reflexivity.
          * exists 4. eexists. split; reflexivity.
        + intros i k op Hi. apply mp_inv_at in Hi.
          destruct Hi as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]].
          * exists (mp_zw rc mp_k1). split; [right; right; right; left | ]; reflexivity.
          * exists (mp_wr rc mp_k2). split; [left | ]; reflexivity.
          * exists (mp_rd rc mp_k3). split; [right; left | ]; reflexivity.
          * exists (mp_zr rc mp_k4 0). split; [right; right; left | ]; reflexivity.
        + intros o o' Ho Ho' Hr. apply mp_rhb in Hr.
          destruct Hr as [(Hk & Hk' & Hn) | (Hk & Hk' & Hn)];
          destruct Ho as [<- | [<- | [<- | [<- | []]]]]; try discriminate Hk;
          destruct Ho' as [<- | [<- | [<- | [<- | []]]]]; try discriminate Hk'.
          * exfalso. apply Hn. right. exists 1, 1, 1. split; reflexivity.
          * apply (BL.nth_before _ 1 2); [reflexivity | reflexivity | lia].
      - intros Hb'. apply (before_asym mp_lin_zw_last _ _ (NoDup_map_inv _ _ Hnd) Hb Hb').
    Qed.
  End MPInstance.

End SeqLockClients.
