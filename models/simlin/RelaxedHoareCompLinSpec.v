(** * RLHL, part 8: the meaning of copy-cat inclusion, and handle-linear underlays (RLHL-3a, iteration 2)

    [RelaxedHoareCompLin] states RLHL soundness as copy-cat trace
    inclusion, [RCompLin M VE σ0 VF v0], for every execution (author
    decision M-20, research-intent §8).  This file answers two findings
    of the RLHL-3a iteration-1 review: what [RTraces (EI δ)] means
    (latest-review M-20, "item 5"), and which underlay presentation the
    layering uses (latest-review m-20).

    ** Part 1: traces of executions with a global simulation

    Generic in [VE], [VF], [M] and a relation [S] with [GSimRel VE VF M S]
    and [S (initial_tagged_module VE σ0) (PossOk v0 [])]:
    - [gsim_trace_wf]: every overlay trace in [MTraces VE M σ0] is well
      formed ([PrefixView.wf]).
    - [gsim_complete_dead], [gsim_dead_complete]: the overlay trace of an
      execution is complete iff every call of its final configuration has
      returned.
    - [gsim_rel_lin_traces]: [RelaxedGSim.gsim_rel_lin] on the trace set:
      under [HVF], every complete trace in [MTraces VE M σ0] is
      relaxed-linearizable.

    ** Part 2: the identity simulation of the copy-cat over [EI δ]

    [cc_gsim : GSimRel (EI δ) (EI δ) idF SCC] and [cc_init]: the relaxed
    copy-cat [RelaxedHoareCompLin.idF], run over the effect-at-invocation
    LTS [RelaxedHoareSpec.EI δ], is simulated by the possibilities over
    [EI δ] itself.  Each call's underlay invocation is matched by the
    abstract invocation of the call (same [δ] step, same result, the
    record rekeyed from the underlay key to the overlay key, [rekey]),
    its underlay response by the abstract response, its overlay return by
    the abstract return.  The invariant [CCInv] lists the active calls
    with their phase ([ph0]: nothing emitted, [ph1 x]: the invocation
    emitted with concrete record [x], [ph2]: both emitted); the abstract
    pool is [map a_lin G]; the order of the queue's pending invocations
    agrees with the age of the calls ([sc_ord]).  The [invocation_ready]
    check of an abstract invocation is discharged by the frontier: an
    older pending invocation of the same thread is before it in the
    queue, and the emitted one crosses it, so (F2) gives [~ ~
    semi_independent], hence [semi_independent] by [Classical_Prop.NNPP]
    (the only classical step; [semi_independent] is not decidable).
    The simulation also sees the module's key freshness ([trace_fresh]),
    which the RLHL triple does not.  What it is *not* (latest-review
    M-22): [cc_gsim] is an identity [GSimRel (EI δ) (EI δ) idF].  Through
    [RelaxedHoareCompLin.gsim_complin] it yields only [RTraces (EI δ) ⊆
    RTraces (EI δ)], and through [RelaxedGSim.gsim_rel_lin] it yields
    [cc_rel_lin].  It is not the absorption lemma [MTraces (Lift idF V)
    N ⊆ MTraces V N] that layering needs, and no composition theorem for
    [GSimRel] or [RCompLin] exists yet, so its role as a unit for
    composition is hypothetical.

    Results:
    - [cc_rel_lin] (M-20 (a), item 5): every *complete* overlay trace in
      [RTraces (EI δ) (s0, [])] is relaxed-linearizable to [seq_legal δ
      s0] under the signature's [semi_independent].  No well-formedness
      hypothesis ([cc_trace_wf]).  This is ν;cc ⊆ rel_lin, the soundness
      direction.  In the orientation of Appendix/relaxedlin.tex:47-50
      (rlx(ν) = ν;seqcopy) it is the ⊇ half (ν;cc ⊆ rlx(ν)), restricted
      to concurrent complete traces and to an effect-at-invocation
      presentation of ν.  The paper's corollary is about *sequential*
      relaxed games, and its rlx is defined by rewriting (REW,
      relaxedlin.tex:29), not by [rel_lin].
    - Open: the converse, rel_lin ⊆ ν;cc (every complete [rel_lin] trace
      is a copy-cat trace).  It is needed only for "every underlay
      relaxed-linearizable" (verimpl, relaxedlin.tex:74; latest-review
      M-22), not for the soundness direction.
    - Not proved either: anything about traces with pending calls.  That
      [RTraces (EI δ)] coincides with the paper's REW prefixes
      (relaxedlin.tex:29-30) is argued, not proved (latest-review M-20);
      the mechanized data points are
      [RelaxedHoareChecks.CounterCompLin.junkF_not_rtrace] (REW rejects
      it, so does the copy-cat) and [RelaxedHoareChecks.WRCopyCat]
      ([si_overtake_rtrace]: a younger read of a thread overtakes the
      thread's pending write when they are semi-independent;
      [si_overtake_not_rtrace0]: not under the empty relation).  The
      paper's prop:rhb-equiv ("for all s, s'", relaxedlin.tex:39-40) is
      likewise not mechanized for prefixes.

    ** Part 3: consequences for [RCompLin] and for the RLHL route

    - [complin_ei_rel_lin], [rlhl_complin_ei_rel_lin]: [RCompLin] into
      [EI δ], hence the RLHL hypotheses via
      [RelaxedHoareCompLin.rlhl_complin_ei], give relaxed linearizability
      of every complete overlay trace.  So the relaxed-linearizability
      conclusion of the RLHL route follows from its copy-cat form.
    - [rlhl_rel_lin_ei_via_cc] re-derives [RelaxedHoareGSim.rlhl_rel_lin_ei]
      in its exact form through the copy-cat (the conversion of
      [Hcomplete] into completeness of the trace uses the RLHL simulation,
      [gsim_dead_complete]).

    ** Part 4: handle-linear presentations and [HLift] (m-20)

    - [HL VE]: [VE] with the list of invoked underlay keys; an invocation
      step is enabled only on a key not in the list
      ([HL_handle_linear : HandleLinear (HL VE) hl_used]).
    - [hlift] (the review's HLift): for every module [M] and initial
      state, [MTraces VE M σ0 s <-> MTraces (HL VE) M (σ0, []) s].  The
      inclusion [⊆] uses the module's underlay-key freshness
      ([trace_fresh] against [tm_used_underlay]; invariant [LiftOK]);
      [⊇] forgets the list.  Corollaries: [rtraces_hlift] ([M := idF]:
      [RTraces VF v = RTraces (HL VF) (v, [])]), [complin_hlift_under] and
      [complin_hlift_over] ([RCompLin] is unchanged when either side is
      replaced by its handle-linear presentation).
    - [EIhl δ := HL (EI δ)], state [((s, P), used)];
      [EIhl_handle_linear]; [hlift_ei].
    - [rlhl_complin_eihl]: the decided layering interface (research-intent
      §8, M-20 as corrected by m-20): RLHL hypotheses over [VE := EIhl
      δE] from [(σ0, [])] give [RCompLin M (EI δE) σ0 (EI δF) (s0, [])].
      Why [EIhl] and not [EI]: [EI] is not handle-linear and admits no
      [RLHL2Hyps] for overlapping same-thread calls
      ([RelaxedHoareChecks.CounterEI], review T1).  Instances:
      [RelaxedHoareChecks.CounterEIhl] ([counter_eihl_rlhl2],
      [counter_complin_ei]) and [RelaxedHoareChecks.CounterEIhlFrame]
      ([counter_frame_rlhl2], [counter_frame_complin_ei]).
    - A specification-independent frame for [EIhl] (latest-review m-34;
      the review's scratch [FrameCheck], adapted).  [eihl_rec_used σ]:
      every pending record of [σ] has a used key.  [eihl_mine key x0 σ]:
      [eihl_rec_used σ], [key] is used, and every pending record with key
      [key] is [x0] (the call owns its record; [x0] need not be present
      any more).  [eihl_steps]: the reflexive-transitive closure of all
      [EIhl δ] steps, of any thread and operation.
      - [eihl_rec_used_init], [eihl_rec_used_step], [eihl_rec_used_steps]:
        [eihl_rec_used] holds from [((s, []), [])] and is kept by every
        step.
      - [eihl_mine_step], [eihl_mine_steps]: [eihl_mine key x0] is kept by
        every step, so an assertion "my record is [x0]" is stable under
        the rely "any [EIhl δ] steps", which mentions no value.  The
        reason is handle-linearity: an invocation step needs an unused
        key, and [key] is used.
      - [eihl_mine_inv] (own invocation establishes ownership): from an
        [eihl_rec_used] state, the invocation step of [(t, h)] with
        result [r] gives [eihl_mine (t, h) (Build_Op (t, h) o r)]; key
        freshness is the step's handle-linearity premise.
      - [eihl_mine_res]: a response step on [key] returns [x0].
      [RelaxedHoareChecks.CounterEIhlFrame] uses the kit for a counter
      instance whose rely and guarantee constrain memory only by
      [eihl_steps].

    Limitations.  Nothing here composes two layers: whether [EIhl]
    layering replaces [ViewLHL.presentation_choice] depends on absorption,
    linking and monotonicity (RLHL-3c, latest-review M-22).  The
    [RLHL2Hyps] instances over [EIhl]: three proofs for the I=∅ counter
    ([RelaxedHoareChecks.CounterEIhl.counter_eihl_rlhl2],
    [RelaxedHoareChecks.CounterEIhlFrame.counter_frame_rlhl2], and
    [RelaxedHoareCounterXY.CounterAsRename.counter_ren_rlhl2] from the
    generic [RelaxedHoareInherit.ren_rlhl2]; the module-derived
    overlapping execution [inc_ooo_exec_ei] is a non-vacuity witness);
    and Counter_xy over the SC two-location cell
    (examples/Relaxed/RelaxedHoareCounterXY.v; every instance but the
    two-future variant is from [ren_rlhl2]): with empty semi-independence on both signatures,
    [RelaxedHoareCounterXY.cxy00_rlhl2]; with nonempty semi-independence
    on both signatures (RLHL-3b), [RelaxedHoareCounterXY.cxy_rlhl2]
    (choice (a), by location / by counter; module-derived SB and LB
    executions [sb_exec], [lb_exec]) and [cxyb_rlhl2] (choice (b),
    [si_mb] / [si_cb]; module-derived SB execution [sb_exec_gen] at
    [si_mb], as the trace [sb_mtraces_b]; LB is not a trace of this
    module, [lb_not_trace_b]); the remaining positive cells of the
    semi-independence table ([cxy0cb_rlhl2], [cxy0cnt_rlhl2],
    [cxybcnt_rlhl2], instances of [mgen_rlhl2], latest-review m-49); and
    the two-future variant of [cxy_rlhl2]
    ([RelaxedHoareCounterXY.CounterXYZ.cxyz_rlhl2]).  All of them are
    renamings or frame-level variants of one (latest-review B-1 (4')).
    The first counter rely uses that the counter's values are unique;
    this is a proof artifact, not a limitation of [EIhl]: the second
    proof replaces it by the value-free frame above (latest-review
    m-34).  [cc_rel_lin] needs the initial pending list
    to be empty.  [EI]'s [Error] is [False], so a partial [δ] blocks (see
    [RelaxedHoareCompLin], latest-review m-8).

    Assumptions: [gsim_trace_wf], [gsim_complete_dead],
    [gsim_dead_complete], [cc_init], every lemma of Part 4 ([hlift],
    [HL_handle_linear], [EIhl_handle_linear], [complin_hlift_*], and the
    frame lemmas [eihl_rec_used_*], [eihl_mine_*]) are
    closed; [cc_gsim] and [cc_trace_wf] use [Classical_Prop.classic]
    (through [NNPP] in [scc_underlay]), [rlhl_complin_eihl] uses it
    through [RelaxedHoareCompLin.rinv_val]; [gsim_rel_lin_traces] uses
    [Eqdep.Eq_rect_eq.eq_rect_eq] (from [RelaxedGSim.gsim_rel_lin]);
    [cc_rel_lin], [complin_ei_rel_lin], [rlhl_complin_ei_rel_lin],
    [rlhl_rel_lin_ei_via_cc] use both. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Logic.Classical_Prop.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedPossibility.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.view.ViewPossibility.
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareGSim.
Require Import models.simlin.RelaxedHoareCompLin.

Import ListNotations.


Module RelaxedHoareCompLinSpec.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedTraceLin.
  Import ViewPossibility.
  Import RelaxedGSim.
  Import RelaxedHoareCompLin.

  (** ** Part 1: traces of executions with a global simulation *)

  Section GSimTraces.
    Context {E F : RelaxedSig.t} (VE : LTS E) (VF : LTS F) (M : RelaxedModuleImpl E F).
    Context (S : @TaggedModuleConfig E F VE -> Poss VF -> Prop) (σ0 : State VE) (v0 : State VF).
    Context (HS : GSimRel VE VF M S) (H0 : S (initial_tagged_module VE σ0) (PossOk v0 [])).

    Lemma gsim_run evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
      exists run v pool, RInv VF v0 run (tm_calls c) v pool /\ conc run = overlay_events evs.
    Proof.
      intros Hex.
      destruct (rinv_exec VE VF M v0 S _ _ _ HS Hex [] v0 [] H0 (RInv_init VF v0)) as (run & v & pool & _ & HI & Hc).
      cbn [app] in HI. exists run, v, pool. split; [exact HI | exact Hc].
    Qed.

    (** The overlay trace of a simulated execution is well formed. *)
    Lemma gsim_trace_wf s : MTraces VE M σ0 s -> PrefixView.wf s.
    Proof.
      intros (evs & c & Hex & <-). destruct (gsim_run evs c Hex) as (run & v & pool & HI & Hc).
      rewrite <- Hc. exact (ri_lwf _ _ _ _ _ _ HI).
    Qed.

    (** A complete overlay trace leaves every call returned. *)
    Lemma gsim_complete_dead evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
      PrefixView.complete (overlay_events evs) ->
      forall e, In e (tm_calls c) -> ce_cell F e = DeadCall.
    Proof.
      intros Hex Hcomp e He. destruct (gsim_run evs c Hex) as (run & v & pool & HI & Hc).
      destruct e as [t h [op ret |]]; [exfalso | reflexivity].
      destruct (ri_cact _ _ _ _ _ _ HI t h op ret He) as ((i & Hi) & Hno).
      rewrite Hc in Hi, Hno. destruct (Hcomp _ _ _ Hi) as (j & r & Hj). exact (Hno _ _ _ Hj).
    Qed.

    (** Conversely, an execution that ends with every call returned has a
        complete overlay trace (the argument inside [gsim_rel_lin]). *)
    Lemma gsim_dead_complete evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
      (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) ->
      PrefixView.complete (overlay_events evs).
    Proof.
      intros Hex Hdead. destruct (gsim_run evs c Hex) as (run & v & pool & HI & Hc). rewrite <- Hc.
      assert (Hwf := ri_lwf _ _ _ _ _ _ HI).
      intros i k m Hi. pose proof (ri_cin _ _ _ _ _ _ HI _ _ _ Hi) as Hk.
      apply in_map_iff in Hk as (e & Hke & He). pose proof (Hdead _ He) as Hd.
      destruct e as [t' h' cell]. cbn in Hd, Hke. subst cell k.
      destruct (ri_cdead _ _ _ _ _ _ HI _ _ He) as (j & m' & r' & Hj).
      pose proof (res_op_inv _ _ _ _ _ _ _ Hwf Hj Hi) as Heq. subst m'.
      exists j, r'. exact Hj.
    Qed.

    (** [RelaxedGSim.gsim_rel_lin] stated on the trace set [MTraces]: every
        complete overlay trace of [M] over [VE] is relaxed-linearizable,
        under [HVF]. *)
    Theorem gsim_rel_lin_traces (nu : list (Op F) -> Prop) :
      (forall T v, vf_path VF v0 T v -> PrefixView.wf T -> PrefixView.complete T ->
         rel_lin (@PrefixView.sel F) T (semi_independent F) nu) ->
      forall s, MTraces VE M σ0 s -> PrefixView.complete s ->
        rel_lin (@PrefixView.sel F) s (semi_independent F) nu.
    Proof.
      intros HVF s (evs & c & Hex & <-) Hcomp.
      exact (gsim_rel_lin VE VF M v0 nu S σ0 evs c HS H0 Hex (gsim_complete_dead evs c Hex Hcomp) HVF).
    Qed.
  End GSimTraces.

  (** ** Generic list facts *)

  Lemma before_in {A : Type} (l : list A) a b : before l a b -> In a l /\ In b l.
  Proof.
    intros (l1 & l2 & -> & Hb). split; apply in_or_app; right; [left; reflexivity | right; exact Hb].
  Qed.

  Lemma before_app_r {A : Type} (l l' : list A) a b : before l a b -> before (l ++ l') a b.
  Proof.
    intros (l1 & l2 & -> & Hb). exists l1, (l2 ++ l'). rewrite <- app_assoc. cbn.
    split; [reflexivity | apply in_or_app; left; exact Hb].
  Qed.

  Lemma before_cons_inv {A : Type} (x : A) l a b : before (x :: l) a b -> (a = x /\ In b l) \/ before l a b.
  Proof.
    intros (l1 & l2 & Heq & Hb). destruct l1 as [| y l1]; cbn in Heq; injection Heq as -> Heq.
    - left. subst l. auto.
    - right. exists l1, l2. auto.
  Qed.

  Lemma before_insert {A : Type} (l1 l2 : list A) x a b : before (l1 ++ l2) a b -> before (l1 ++ x :: l2) a b.
  Proof.
    revert l2. induction l1 as [| y l1 IH]; intros l2 Hb; cbn in *.
    - destruct Hb as (p1 & p2 & -> & Hb). exists (x :: p1), p2. split; [reflexivity | exact Hb].
    - destruct (before_cons_inv _ _ _ _ Hb) as [(-> & Hin) | Hb'].
      + exists [], (l1 ++ x :: l2). split; [reflexivity |].
        apply in_app_or in Hin as [Hin | Hin]; apply in_or_app; [left | right; right]; exact Hin.
      + destruct (IH l2 Hb') as (p1 & p2 & Heq & Hp). exists (y :: p1), p2. rewrite Heq. split; [reflexivity | exact Hp].
  Qed.

  (** In a duplicate-free list, an element before [c] is to the left of [c]. *)
  Lemma before_nodup_pre {A : Type} (l pre post : list A) c y :
    NoDup l -> l = pre ++ c :: post -> before l y c -> In y pre.
  Proof.
    intros Hnd Hl (l1 & l2 & Hl' & Hc). apply in_split in Hc as (m1 & m2 & ->).
    assert (Hnd' : NoDup (map (fun x : A => x) l)) by (rewrite map_id; exact Hnd).
    assert (Heq : l = (l1 ++ y :: m1) ++ c :: m2) by (rewrite Hl', <- app_assoc; reflexivity).
    destruct (key_position (fun x : A => x) l pre post (l1 ++ y :: m1) m2 c c Hnd' Hl Heq eq_refl) as (-> & _ & _).
    apply in_or_app. right. left. reflexivity.
  Qed.

  Section PoolUpdate.
    Context {F : RelaxedSig.t}.

    Lemma liu_app t h op (pre post : LinPool F) e e' :
      (forall y, In y pre -> lin_key y <> (t, h)) ->
      lin_invoke_update t h op (e :: post) (e' :: post) ->
      lin_invoke_update t h op (pre ++ e :: post) (pre ++ e' :: post).
    Proof.
      induction pre as [| y pre IH]; intros Hk Hu; [exact Hu |].
      cbn. apply lin_invoke_update_next; [apply Hk; left; reflexivity |].
      apply IH; [intros z Hz; apply Hk; right; exact Hz | exact Hu].
    Qed.

    Lemma lu_app k b a (pre post : LinPool F) :
      (forall y, In y pre -> lin_key y <> k) ->
      lin_update k b a (pre ++ make_lin_entry k b :: post) (pre ++ make_lin_entry k a :: post).
    Proof.
      induction pre as [| y pre IH]; intros Hk; [apply lin_update_here |].
      cbn. apply lin_update_next; [apply Hk; left; reflexivity |].
      apply IH. intros z Hz. apply Hk. right. exact Hz.
    Qed.

    Lemma lr_app k st (pre post : LinPool F) :
      (forall y, In y pre -> lin_key y <> k) ->
      lin_remove k st (pre ++ make_lin_entry k st :: post) (pre ++ post).
    Proof.
      induction pre as [| y pre IH]; intros Hk; [apply lin_remove_here |].
      cbn. apply lin_remove_next; [apply Hk; left; reflexivity |].
      apply IH. intros z Hz. apply Hk. right. exact Hz.
    Qed.
  End PoolUpdate.

  (** ** Part 2: the identity simulation of the copy-cat over [EI δ] *)

  Section CopyCat.
    Context {F : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop).

    Abbreviation V := (RelaxedHoareSpec.EI δ).
    Abbreviation Cfg := (@TaggedModuleConfig F F V).
    Abbreviation TSE := (TaggedScheduledEvent F F).
    Abbreviation POk s Pa pool := (@PossOk F V (s, Pa) pool).

    (** An active copy-cat call: its overlay key, the underlay handle it
        chose, its operation and the result it committed at invocation. *)
    Record ACall : Type := mkACall {
      ac_key : CallKey F;
      ac_uh : RelaxedSig.handle F;
      ac_op : Sig.op (RelaxedSig.effect F);
      ac_ret : Sig.ar ac_op
    }.

    Definition ac_ukey (a : ACall) : CallKey F := (fst (ac_key a), ac_uh a).

    Definition a_inv (a : ACall) : TSE :=
      Build_TaggedScheduledEvent (ac_key a) (cc_inv_ev (fst (ac_key a)) (ac_uh a) (ac_op a)).

    Definition a_res (a : ACall) : TSE :=
      Build_TaggedScheduledEvent (ac_key a) (cc_res_ev (fst (ac_key a)) (ac_uh a) (ac_op a) (ac_ret a)).

    Definition a_entry (a : ACall) : CallEntry F :=
      Build_CallEntry (fst (ac_key a)) (snd (ac_key a)) (ActiveCall (ac_op a) (ac_ret a)).

    (** The phase of a call: nothing emitted; the underlay invocation
        emitted, with the concrete pending record [x]; both emitted. *)
    Inductive APhase : Type := ph0 | ph1 (x : Op F) | ph2.

    Definition gkey (g : ACall * APhase) : CallKey F := ac_key (fst g).
    Definition gukey (g : ACall * APhase) : CallKey F := ac_ukey (fst g).

    Definition a_ls (g : ACall * APhase) : LinState F :=
      match snd g with
      | ph0 => ls_inv (ac_op (fst g))
      | ph1 _ => ls_lini (ac_op (fst g))
      | ph2 => ls_linr (ac_op (fst g)) (ac_ret (fst g))
      end.

    Definition a_lin (g : ACall * APhase) : LinEntry F := make_lin_entry (gkey g) (a_ls g).

    (** The abstract record of a concrete one: the same operation and
        result under the overlay key. *)
    Definition rekey (k : CallKey F) (x : Op F) : Op F := Build_Op k (op_op x) (op_ret x).

    Definition PhaseOK (c : Cfg) (Pa : list (Op F)) (g : ACall * APhase) : Prop :=
      match snd g with
      | ph0 => before (tm_queue c) (a_inv (fst g)) (a_res (fst g))
      | ph1 x => ~ In (a_inv (fst g)) (tm_queue c) /\ In (a_res (fst g)) (tm_queue c) /\
                 In x (snd (tm_lts_state c)) /\ op_key x = gukey g /\ In (rekey (gkey g) x) Pa
      | ph2 => ~ In (a_inv (fst g)) (tm_queue c) /\ ~ In (a_res (fst g)) (tm_queue c)
      end.

    (** The invariant: [G] lists the active calls, newest first, with
        their phases; the abstract pool is [map a_lin G]; the abstract
        sequential state is the concrete one; [Pa] holds the abstract
        records of the calls in phase [ph1]. *)
    Record CCInv (c : Cfg) (Pa : list (Op F)) (G : list (ACall * APhase)) : Prop := {
      sc_ndk : NoDup (map gkey G);
      sc_ndu : NoDup (map gukey G);
      sc_used : forall g, In g G -> In (gukey g) (tm_used_underlay c);
      sc_calls : forall g, In g G -> In (a_entry (fst g)) (tm_calls c);
      sc_act : forall t h op (ret : Sig.ar op), In (Build_CallEntry t h (ActiveCall op ret)) (tm_calls c) ->
                 exists g, In g G /\ gkey g = (t, h);
      sc_cwf : NoDup (map call_key (tm_calls c));
      sc_ph : forall g, In g G -> PhaseOK c Pa g;
      sc_q : forall y, In y (tm_queue c) -> exists g, In g G /\ (y = a_inv (fst g) \/ y = a_res (fst g));
      sc_ndq : NoDup (tm_queue c);
      sc_pc : forall x, In x (snd (tm_lts_state c)) -> exists g, In g G /\ snd g = ph1 x;
      sc_ndpc : NoDup (map op_key (snd (tm_lts_state c)));
      sc_ord : forall a a', before (map fst G) a a' -> In (a_inv a') (tm_queue c) -> In (a_inv a) (tm_queue c) ->
                 before (tm_queue c) (a_inv a') (a_inv a)
    }.

    Definition SCC (c : Cfg) (p : Poss V) : Prop :=
      exists (Pa : list (Op F)) (G : list (ACall * APhase)),
        p = @PossOk F V (fst (tm_lts_state c), Pa) (map a_lin G) /\ CCInv c Pa G.

    (** *** Small facts *)

    Lemma a_entry_key a : call_key (a_entry a) = ac_key a.
    Proof. unfold call_key, a_entry. cbn. symmetry. apply surjective_pairing. Qed.

    Lemma a_lin_key g : lin_key (a_lin g) = gkey g.
    Proof. apply lin_key_make_lin_entry. Qed.

    Lemma a_inv_ne_res a a' : a_inv a <> a_res a'.
    Proof. intros H. apply (f_equal (fun x => te_ev F (untag (ts_event x)))) in H. discriminate H. Qed.

    Lemma a_inv_owner a a' : a_inv a = a_inv a' -> ac_key a = ac_key a'.
    Proof. intros H. exact (f_equal ts_owner H). Qed.

    Lemma a_res_owner a a' : a_res a = a_res a' -> ac_key a = ac_key a'.
    Proof. intros H. exact (f_equal ts_owner H). Qed.

    Lemma gkey_in G g : In g G -> In (gkey g) (map gkey G).
    Proof. apply in_map. Qed.

    Lemma g_eq_of_key G g g' : NoDup (map gkey G) -> In g G -> In g' G -> gkey g = gkey g' -> g = g'.
    Proof. apply NoDup_key_eq. Qed.

    Lemma g_eq_of_ukey G g g' : NoDup (map gukey G) -> In g G -> In g' G -> gukey g = gukey g' -> g = g'.
    Proof. apply NoDup_key_eq. Qed.

    (** Keys of the other entries around a split point differ. *)
    Lemma split_key_ne (G1 G2 : list (ACall * APhase)) g0 g :
      NoDup (map gkey (G1 ++ g0 :: G2)) -> In g (G1 ++ G2) -> gkey g <> gkey g0.
    Proof.
      intros Hnd Hg Hk. rewrite map_app in Hnd. cbn in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd.
      rewrite <- map_app, <- Hk. apply in_map. exact Hg.
    Qed.

    Lemma split_ukey_ne (G1 G2 : list (ACall * APhase)) g0 g :
      NoDup (map gukey (G1 ++ g0 :: G2)) -> In g (G1 ++ G2) -> gukey g <> gukey g0.
    Proof.
      intros Hnd Hg Hk. rewrite map_app in Hnd. cbn in Hnd. apply NoDup_remove_2 in Hnd. apply Hnd.
      rewrite <- map_app, <- Hk. apply in_map. exact Hg.
    Qed.

    Lemma map_upd {B : Type} (f : ACall * APhase -> B) (G1 G2 : list (ACall * APhase)) a p p' :
      (forall p0, f (a, p0) = f (a, p)) ->
      map f (G1 ++ (a, p') :: G2) = map f (G1 ++ (a, p) :: G2).
    Proof. intros Hf. rewrite !map_app. cbn. rewrite Hf. reflexivity. Qed.

    Lemma in_upd (G1 G2 : list (ACall * APhase)) g0' g :
      In g (G1 ++ g0' :: G2) -> g = g0' \/ In g (G1 ++ G2).
    Proof.
      intros Hg. apply in_app_or in Hg as [Hg | [<- | Hg]];
        [right; apply in_or_app; left; exact Hg | left; reflexivity | right; apply in_or_app; right; exact Hg].
    Qed.

    Lemma in_rest (G1 G2 : list (ACall * APhase)) g0 g : In g (G1 ++ G2) -> In g (G1 ++ g0 :: G2).
    Proof. intros Hg. apply in_app_or in Hg as [Hg | Hg]; apply in_or_app; [left | right; right]; exact Hg. Qed.

    Lemma map_fst_split (G1 G2 : list (ACall * APhase)) a p :
      map fst (G1 ++ (a, p) :: G2) = map fst G1 ++ a :: map fst G2.
    Proof. rewrite map_app. reflexivity. Qed.

    (** *** Preservation: an overlay invocation *)

    Lemma scc_invoke t h op q calls Q used trace (ret : Sig.ar op) Pa G :
      CCInv (Build_TaggedModuleConfig q calls Q used) Pa G ->
      call_fresh (t, h) calls ->
      program_produces_tagged t (@idF F op t) trace ret ->
      trace_fresh used (map untag trace) ->
      exists G' : list (ACall * APhase), poss_invoke V t h op (POk (fst q) Pa (map a_lin G)) (POk (fst q) Pa (map a_lin G')) /\
        CCInv (Build_TaggedModuleConfig q (Build_CallEntry t h (ActiveCall op ret) :: calls)
                 (Q ++ schedule_trace_tagged (t, h) trace) (used ++ invocation_keys (map untag trace))) Pa G'.
    Proof.
      intros HC Hcf Hprod Hft.
      destruct (cc_trace t op trace ret Hprod) as (u & ->).
      set (a := mkACall (t, h) u op ret).
      destruct Hft as [_ Hfu].
      assert (Hu : ~ In (t, u) used) by (apply Hfu; left; reflexivity).
      change (schedule_trace_tagged (t, h) [cc_inv_ev t u op; cc_res_ev t u op ret]) with [a_inv a; a_res a].
      change (invocation_keys (map untag [@cc_inv_ev F t u op; @cc_res_ev F t u op ret])) with [ac_ukey a].
      destruct HC as [Hndk Hndu Hused Hcalls Hact Hcwf Hph Hq Hndq Hpc Hndpc Hord];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      assert (Hko : forall g, In g G -> gkey g <> (t, h)).
      { intros g Hg Hk. apply Hcf. rewrite <- Hk. unfold gkey. rewrite <- a_entry_key.
        apply in_map. exact (Hcalls g Hg). }
      assert (Huo : forall g, In g G -> gukey g <> (t, u)).
      { intros g Hg Hk. apply Hu. rewrite <- Hk. exact (Hused g Hg). }
      assert (Hqo : forall y, In y Q -> ts_owner y <> (t, h)).
      { intros y Hy Hk. destruct (Hq y Hy) as (g & Hg & [-> | ->]); exact (Hko g Hg Hk). }
      assert (Hnew_i : forall y, In y Q -> y <> a_inv a).
      { intros y Hy ->. exact (Hqo _ Hy eq_refl). }
      assert (Hnew_r : forall y, In y Q -> y <> a_res a).
      { intros y Hy ->. exact (Hqo _ Hy eq_refl). }
      assert (HinQ' : forall y, In y (Q ++ [a_inv a; a_res a]) -> In y Q \/ y = a_inv a \/ y = a_res a).
      { intros y Hy. apply in_app_or in Hy as [Hy | [<- | [<- | []]]]; auto. }
      exists ((a, ph0) :: G). split.
      - apply (poss_invoke_ok V t h op (fst q, Pa) (map a_lin G) (map a_lin ((a, ph0) :: G))).
        apply (lin_insert_fresh (t, h) (ls_inv op) (map a_lin G)).
        intros Hin. unfold lin_domain in Hin. rewrite map_map in Hin.
        apply in_map_iff in Hin as (g & Hk & Hg). rewrite a_lin_key in Hk. exact (Hko g Hg Hk).
      - constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay].
        + cbn [map]. constructor; [| exact Hndk].
          intros Hin. apply in_map_iff in Hin as (g & Hk & Hg). exact (Hko g Hg Hk).
        + cbn [map]. constructor; [| exact Hndu].
          intros Hin. apply in_map_iff in Hin as (g & Hk & Hg). exact (Huo g Hg Hk).
        + intros g [<- | Hg]; apply in_or_app; [right; left; reflexivity | left; exact (Hused g Hg)].
        + intros g [<- | Hg]; [left; reflexivity | right; exact (Hcalls g Hg)].
        + intros t' h' op' ret' [Heq | Hin].
          * exists (a, ph0). split; [left; reflexivity |].
            exact (f_equal call_key Heq).
          * destruct (Hact t' h' op' ret' Hin) as (g & Hg & Hk). exists g. split; [right; exact Hg | exact Hk].
        + cbn [map]. constructor; [exact Hcf | exact Hcwf].
        + intros g [<- | Hg].
          * cbn. exists Q, [a_res a]. split; [reflexivity | left; reflexivity].
          * pose proof (Hph g Hg) as Hp. unfold PhaseOK in Hp |- *. cbn [tm_queue tm_lts_state] in Hp |- *.
            assert (Hgi : a_inv (fst g) <> a_inv a /\ a_inv (fst g) <> a_res a).
            { split; [intros Heq; exact (Hko g Hg (a_inv_owner _ _ Heq)) | apply a_inv_ne_res]. }
            assert (Hgr : a_res (fst g) <> a_inv a /\ a_res (fst g) <> a_res a).
            { split; [intros Heq; exact (a_inv_ne_res _ _ (eq_sym Heq)) |].
              intros Heq. exact (Hko g Hg (a_res_owner _ _ Heq)). }
            destruct (snd g) as [| x |].
            -- exact (before_app_r _ _ _ _ Hp).
            -- destruct Hp as (Hni & Hr & Hx & Hkx & Hrk). split; [| split; [| auto]].
               ++ intros Hin. destruct (HinQ' _ Hin) as [Hin' | [Heq | Heq]]; [exact (Hni Hin') | exact (proj1 Hgi Heq) | exact (proj2 Hgi Heq)].
               ++ apply in_or_app. left. exact Hr.
            -- destruct Hp as (Hni & Hnr). split.
               ++ intros Hin. destruct (HinQ' _ Hin) as [Hin' | [Heq | Heq]]; [exact (Hni Hin') | exact (proj1 Hgi Heq) | exact (proj2 Hgi Heq)].
               ++ intros Hin. destruct (HinQ' _ Hin) as [Hin' | [Heq | Heq]]; [exact (Hnr Hin') | exact (proj1 Hgr Heq) | exact (proj2 Hgr Heq)].
        + intros y Hy. destruct (HinQ' _ Hy) as [Hy' | [-> | ->]].
          * destruct (Hq y Hy') as (g & Hg & Hform). exists g. split; [right; exact Hg | exact Hform].
          * exists (a, ph0). split; [left; reflexivity | left; reflexivity].
          * exists (a, ph0). split; [left; reflexivity | right; reflexivity].
        + apply NoDup_app; [exact Hndq | |].
          * constructor; [intros [H | []]; exact (a_inv_ne_res _ _ (eq_sym H)) | constructor; [intros [] | constructor]].
          * intros y Hy [Heq | [Heq | []]]; [exact (Hnew_i y Hy (eq_sym Heq)) | exact (Hnew_r y Hy (eq_sym Heq))].
        + intros x Hx. destruct (Hpc x Hx) as (g & Hg & Hs). exists g. split; [right; exact Hg | exact Hs].
        + exact Hndpc.
        + intros a1 a2 Hb Hi2 Hi1. cbn [map] in Hb.
          destruct (before_cons_inv _ _ _ _ Hb) as [(-> & Hin) | Hb'].
          * apply in_map_iff in Hin as (g2 & <- & Hg2).
            destruct (HinQ' _ Hi2) as [Hi2' | [Heq | Heq]].
            -- destruct (in_split _ _ Hi2') as (l1 & l2 & ->). exists l1, (l2 ++ [a_inv a; a_res a]).
               rewrite <- app_assoc. split; [reflexivity | apply in_or_app; right; left; reflexivity].
            -- exfalso. exact (Hko g2 Hg2 (a_inv_owner _ _ Heq)).
            -- exfalso. exact (a_inv_ne_res _ _ Heq).
          * destruct (before_in _ _ _ Hb') as (Ha1 & Ha2).
            apply in_map_iff in Ha1 as (g1 & <- & Hg1). apply in_map_iff in Ha2 as (g2 & <- & Hg2).
            assert (Hi1' : In (a_inv (fst g1)) Q).
            { destruct (HinQ' _ Hi1) as [H | [Heq | Heq]]; [exact H | | exfalso; exact (a_inv_ne_res _ _ Heq)].
              exfalso. exact (Hko g1 Hg1 (a_inv_owner _ _ Heq)). }
            assert (Hi2' : In (a_inv (fst g2)) Q).
            { destruct (HinQ' _ Hi2) as [H | [Heq | Heq]]; [exact H | | exfalso; exact (a_inv_ne_res _ _ Heq)].
              exfalso. exact (Hko g2 Hg2 (a_inv_owner _ _ Heq)). }
            exact (before_app_r _ _ _ _ (Hord _ _ Hb' Hi2' Hi1')).
    Qed.
    (** *** Preservation: an underlay emission *)

    Lemma scc_underlay cand q q' calls Q Q' used Pa G :
      CCInv (Build_TaggedModuleConfig q calls Q used) Pa G ->
      select_frontier_tagged cand Q Q' ->
      Step V (untag (ts_event cand)) q q' ->
      exists (Pa' : list (Op F)) (G' : list (ACall * APhase)),
        poss_steps V (POk (fst q) Pa (map a_lin G)) (POk (fst q') Pa' (map a_lin G')) /\
        CCInv (Build_TaggedModuleConfig q' calls Q' used) Pa' G'.
    Proof.
      intros HC Hsel Hst.
      destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & HQ & -> & Hcross).
      rewrite Forall_forall in Hcross.
      destruct HC as [Hndk Hndu Hused Hcalls Hact Hcwf Hph Hq Hndq Hpc Hndpc Hord];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      assert (Hcand : In cand Q) by (rewrite HQ; apply in_or_app; right; left; reflexivity).
      assert (Hndq' : NoDup (pre ++ post)) by (rewrite HQ in Hndq; exact (NoDup_remove_1 _ _ _ Hndq)).
      assert (Hnc : ~ In cand (pre ++ post)) by (rewrite HQ in Hndq; exact (NoDup_remove_2 _ _ _ Hndq)).
      assert (Hsub : forall y, In y (pre ++ post) -> In y Q)
        by (intros y Hy; rewrite HQ; exact (in_remove_in _ _ _ _ Hy)).
      assert (Hkeep : forall y, In y Q -> y <> cand -> In y (pre ++ post))
        by (intros y Hy Hne; rewrite HQ in Hy; exact (in_remove_ne _ _ _ _ Hy Hne)).
      assert (Hbef : forall y z, before Q y z -> y <> cand -> z <> cand -> before (pre ++ post) y z)
        by (intros y z Hb Hy Hz; rewrite HQ in Hb; exact (before_remove _ _ _ _ _ Hb Hy Hz)).
      destruct (Hq cand Hcand) as (g & Hg & Hform).
      destruct g as [a p]. cbn [fst] in Hform.
      destruct (in_split _ _ Hg) as (G1 & G2 & HG). subst G.
      pose proof (Hph (a, p) Hg) as Hph_a. unfold PhaseOK in Hph_a. cbn [snd fst tm_queue tm_lts_state] in Hph_a.
      assert (Hoth : forall g', In g' (G1 ++ G2) -> gkey g' <> ac_key a)
        by (intros g' Hg'; exact (split_key_ne G1 G2 (a, p) g' Hndk Hg')).
      assert (Hothu : forall g', In g' (G1 ++ G2) -> gukey g' <> ac_ukey a)
        by (intros g' Hg'; exact (split_ukey_ne G1 G2 (a, p) g' Hndu Hg')).
      assert (Hord' : forall a1 a2, before (map fst (G1 ++ (a, p) :: G2)) a1 a2 ->
                In (a_inv a2) (pre ++ post) -> In (a_inv a1) (pre ++ post) ->
                before (pre ++ post) (a_inv a2) (a_inv a1)).
      { intros a1 a2 Hb Hi2 Hi1. apply Hbef; [exact (Hord _ _ Hb (Hsub _ Hi2) (Hsub _ Hi1)) | |];
          intros Heq; rewrite Heq in *; contradiction. }
      destruct Hform as [-> | ->].
      - (* the emission of the underlay invocation of [a] *)
        destruct p as [| x0 |];
          [| destruct Hph_a as (Hni & _); exfalso; exact (Hni Hcand)
           | destruct Hph_a as (Hni & _); exfalso; exact (Hni Hcand)].
        destruct a as [[t h] u op ret]. cbn in Hst. destruct Hst as (r & st' & Hd & ->).
        set (a := mkACall (t, h) u op ret) in *.
        set (x := Build_Op (t, u) op r).
        assert (Hxnew : ~ In (op_key x) (map op_key (snd q))).
        { intros Hin. apply in_map_iff in Hin as (y & Hyk & Hy). destruct (Hpc y Hy) as (g' & Hg' & Hs).
          pose proof (Hph g' Hg') as Hp'. unfold PhaseOK in Hp'. rewrite Hs in Hp'.
          destruct Hp' as (_ & _ & _ & Hky & _).
          assert (Heq : g' = (a, ph0)).
          { apply (g_eq_of_ukey _ _ _ Hndu Hg' (in_elt _ _ _)). rewrite <- Hky, Hyk. reflexivity. }
          rewrite Heq in Hs. discriminate Hs. }
        exists (Build_Op (t, h) op r :: Pa), (G1 ++ (a, ph1 x) :: G2). split.
        + apply rt_step. rewrite !map_app. cbn [map].
          apply (ps_inv V t h op (fst q, Pa) (st', Build_Op (t, h) op r :: Pa)).
          * apply liu_app.
            -- intros y Hy. apply in_map_iff in Hy as (g' & <- & Hg'). rewrite a_lin_key.
               apply (Hoth g'). apply in_or_app. left. exact Hg'.
            -- apply lin_invoke_update_here. unfold invocation_ready. rewrite Forall_forall. intros y Hy.
               apply in_map_iff in Hy as (g2 & <- & Hg2). destruct g2 as [a2 p2].
               unfold older_entry_allows_invocation.
               destruct p2 as [| x2 |]; cbn; [| right; exact Logic.I | right; exact Logic.I].
               destruct (Pos.eq_dec (fst (ac_key a2)) t) as [Ht | Ht]; [right | left; exact Ht].
               apply NNPP. intros Hn.
               assert (Hg2G : In (a2, ph0) (G1 ++ (a, ph0) :: G2)) by (apply in_or_app; right; right; exact Hg2).
               pose proof (Hph _ Hg2G) as Hp2. unfold PhaseOK in Hp2. cbn in Hp2.
               destruct (before_in _ _ _ Hp2) as (Hi2 & _).
               assert (Hb : before (map fst (G1 ++ (a, ph0) :: G2)) a a2).
               { rewrite map_fst_split. exists (map fst G1), (map fst G2). split; [reflexivity |].
                 apply in_map_iff. exists (a2, ph0). split; [reflexivity | exact Hg2]. }
               pose proof (Hord _ _ Hb Hi2 Hcand) as Hb2.
               pose proof (before_nodup_pre Q pre post _ _ Hndq HQ Hb2) as Hpre.
               pose proof (Hcross _ Hpre) as Hc. unfold tagged_can_cross, must_precede in Hc. cbn in Hc.
               destruct Hc as [Hc | (_ & Hc)]; [exact (Hc Ht) | exact (Hc Hn)].
          * cbn. exists r, st'. split; [exact Hd | reflexivity].
        + assert (Hres_a : In (a_res a) (pre ++ post)).
          { apply Hkeep; [exact (proj2 (before_in _ _ _ Hph_a)) |]. intros Heq. exact (a_inv_ne_res _ _ (eq_sym Heq)). }
          constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay snd fst].
          * rewrite (map_upd gkey G1 G2 a ph0 (ph1 x) (fun _ => eq_refl)). exact Hndk.
          * rewrite (map_upd gukey G1 G2 a ph0 (ph1 x) (fun _ => eq_refl)). exact Hndu.
          * intros g' Hg'. destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''];
              [exact (Hused _ (in_elt _ _ _)) | exact (Hused _ (in_rest _ _ _ _ Hg''))].
          * intros g' Hg'. destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''];
              [exact (Hcalls _ (in_elt _ _ _)) | exact (Hcalls _ (in_rest _ _ _ _ Hg''))].
          * intros t' h' op' ret' Hin. destruct (Hact t' h' op' ret' Hin) as (g' & Hg' & Hk).
            destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
            -- exists (a, ph1 x). split; [apply in_elt | exact Hk].
            -- exists g'. split; [exact (in_rest _ _ _ _ Hg'') | exact Hk].
          * exact Hcwf.
          * intros g' Hg'. destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
            -- unfold PhaseOK. cbn [snd fst tm_queue tm_lts_state].
               split; [exact Hnc |]. split; [exact Hres_a |]. split; [left; reflexivity |].
               split; [reflexivity | left; reflexivity].
            -- pose proof (Hph g' (in_rest _ _ _ _ Hg'')) as Hp'. pose proof (Hoth g' Hg'') as Hgk.
               destruct g' as [a' p']. unfold PhaseOK in Hp' |- *. cbn [snd fst tm_queue tm_lts_state] in Hp' |- *.
               assert (Hia : a_inv a' <> a_inv a) by (intros Heq; exact (Hgk (a_inv_owner _ _ Heq))).
               assert (Hra : a_res a' <> a_inv a) by (intros Heq; exact (a_inv_ne_res _ _ (eq_sym Heq))).
               destruct p' as [| y |].
               ++ exact (Hbef _ _ Hp' Hia Hra).
               ++ destruct Hp' as (Hni & Hr & Hy & Hky & Hrk).
                  split; [intros Hin; exact (Hni (Hsub _ Hin)) |]. split; [exact (Hkeep _ Hr Hra) |].
                  split; [right; exact Hy |]. split; [exact Hky | right; exact Hrk].
               ++ destruct Hp' as (Hni & Hnr). split; intros Hin; [exact (Hni (Hsub _ Hin)) | exact (Hnr (Hsub _ Hin))].
          * intros y Hy. destruct (Hq y (Hsub y Hy)) as (g' & Hg' & Hf).
            destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
            -- exists (a, ph1 x). split; [apply in_elt | exact Hf].
            -- exists g'. split; [exact (in_rest _ _ _ _ Hg'') | exact Hf].
          * exact Hndq'.
          * intros y [<- | Hy].
            -- exists (a, ph1 x). split; [apply in_elt | reflexivity].
            -- destruct (Hpc y Hy) as (g' & Hg' & Hs). destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
               ++ discriminate Hs.
               ++ exists g'. split; [exact (in_rest _ _ _ _ Hg'') | exact Hs].
          * cbn [map]. constructor; [exact Hxnew | exact Hndpc].
          * rewrite (map_upd fst G1 G2 a ph0 (ph1 x) (fun _ => eq_refl)). exact Hord'.
      - (* the emission of the underlay response of [a] *)
        destruct p as [| x0 |].
        + exfalso. pose proof (before_nodup_pre Q pre post _ _ Hndq HQ Hph_a) as Hpre.
          pose proof (Hcross _ Hpre) as Hc. unfold tagged_can_cross, must_precede in Hc. cbn in Hc.
          destruct Hc as [Hc | (_ & Hc)]; exact (Hc eq_refl).
        + destruct Hph_a as (Hni & _ & Hx0 & Hkx0 & Hrk).
          destruct a as [[t h] u op ret]. cbn in Hst. destruct Hst as (P1 & P2 & HP & ->).
          set (a := mkACall (t, h) u op ret) in *.
          assert (Hx0eq : x0 = Build_Op (t, u) op ret).
          { apply (NoDup_key_eq op_key (snd q) _ _ Hndpc Hx0); [rewrite HP; apply in_elt | exact Hkx0]. }
          rewrite Hx0eq in Hrk. cbn in Hrk.
          destruct (in_split _ _ Hrk) as (Pa1 & Pa2 & HPa).
          exists (Pa1 ++ Pa2), (G1 ++ (a, ph2) :: G2). split.
          * apply rt_step. rewrite !map_app. cbn [map].
            apply (ps_ret V t h op ret (fst q, Pa) (fst q, Pa1 ++ Pa2)).
            -- apply lu_app. intros y Hy. apply in_map_iff in Hy as (g' & <- & Hg'). rewrite a_lin_key.
               apply (Hoth g'). apply in_or_app. left. exact Hg'.
            -- cbn. exists Pa1, Pa2. split; [exact HPa | reflexivity].
          * assert (Hnd_P : NoDup (map op_key (P1 ++ Build_Op (t, u) op ret :: P2))) by (rewrite <- HP; exact Hndpc).
            constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay snd fst].
            -- rewrite (map_upd gkey G1 G2 a (ph1 x0) ph2 (fun _ => eq_refl)). exact Hndk.
            -- rewrite (map_upd gukey G1 G2 a (ph1 x0) ph2 (fun _ => eq_refl)). exact Hndu.
            -- intros g' Hg'. destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''];
                 [exact (Hused _ (in_elt _ _ _)) | exact (Hused _ (in_rest _ _ _ _ Hg''))].
            -- intros g' Hg'. destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''];
                 [exact (Hcalls _ (in_elt _ _ _)) | exact (Hcalls _ (in_rest _ _ _ _ Hg''))].
            -- intros t' h' op' ret' Hin. destruct (Hact t' h' op' ret' Hin) as (g' & Hg' & Hk).
               destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
               ++ exists (a, ph2). split; [apply in_elt | exact Hk].
               ++ exists g'. split; [exact (in_rest _ _ _ _ Hg'') | exact Hk].
            -- exact Hcwf.
            -- intros g' Hg'. destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
               ++ unfold PhaseOK. cbn [snd fst tm_queue tm_lts_state].
                  split; [intros Hin; exact (Hni (Hsub _ Hin)) | exact Hnc].
               ++ pose proof (Hph g' (in_rest _ _ _ _ Hg'')) as Hp'. pose proof (Hoth g' Hg'') as Hgk.
                  pose proof (Hothu g' Hg'') as Hgu.
                  destruct g' as [a' p']. unfold PhaseOK in Hp' |- *. cbn [snd fst tm_queue tm_lts_state] in Hp' |- *.
                  assert (Hia : a_inv a' <> a_res a) by (apply a_inv_ne_res).
                  assert (Hra : a_res a' <> a_res a) by (intros Heq; exact (Hgk (a_res_owner _ _ Heq))).
                  destruct p' as [| y |].
                  ** exact (Hbef _ _ Hp' Hia Hra).
                  ** destruct Hp' as (Hni' & Hr & Hy & Hky & Hrk').
                     split; [intros Hin; exact (Hni' (Hsub _ Hin)) |]. split; [exact (Hkeep _ Hr Hra) |].
                     split; [| split; [exact Hky |]].
                     --- rewrite HP in Hy. apply (in_remove_ne _ _ _ _ Hy). intros Heq. apply Hgu.
                         rewrite <- Hky, Heq. reflexivity.
                     --- rewrite HPa in Hrk'. apply (in_remove_ne _ _ _ _ Hrk'). intros Heq. apply Hgk.
                         exact (f_equal op_key Heq).
                  ** destruct Hp' as (Hni' & Hnr). split; intros Hin; [exact (Hni' (Hsub _ Hin)) | exact (Hnr (Hsub _ Hin))].
            -- intros y Hy. destruct (Hq y (Hsub y Hy)) as (g' & Hg' & Hf).
               destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
               ++ exists (a, ph2). split; [apply in_elt | exact Hf].
               ++ exists g'. split; [exact (in_rest _ _ _ _ Hg'') | exact Hf].
            -- exact Hndq'.
            -- intros y Hy. assert (Hy' : In y (snd q)) by (rewrite HP; exact (in_remove_in _ _ _ _ Hy)).
               destruct (Hpc y Hy') as (g' & Hg' & Hs). destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
               ++ exfalso. cbn in Hs. injection Hs as Hs. rewrite Hx0eq in Hs. subst y.
                  rewrite map_app in Hnd_P. cbn in Hnd_P. apply (NoDup_remove_2 _ _ _ Hnd_P).
                  rewrite <- map_app. apply in_map_iff. exists (Build_Op (t, u) op ret). split; [reflexivity | exact Hy].
               ++ exists g'. split; [exact (in_rest _ _ _ _ Hg'') | exact Hs].
            -- rewrite map_app in Hnd_P |- *. cbn in Hnd_P. exact (NoDup_remove_1 _ _ _ Hnd_P).
            -- rewrite (map_upd fst G1 G2 a (ph1 x0) ph2 (fun _ => eq_refl)). exact Hord'.
        + exfalso. destruct Hph_a as (_ & Hnr). exact (Hnr Hcand).
    Qed.

    (** *** Preservation: an overlay return *)

    Lemma scc_return t h op (ret : Sig.ar op) q calls calls' Q used Pa G :
      CCInv (Build_TaggedModuleConfig q calls Q used) Pa G ->
      finish_call t h op ret calls calls' -> owner_done_tagged (t, h) Q ->
      exists G' : list (ACall * APhase),
        lin_remove (t, h) (ls_linr op ret) (map a_lin G) (map a_lin G') /\
        CCInv (Build_TaggedModuleConfig q calls' Q used) Pa G'.
    Proof.
      intros HC Hfin Hdone.
      destruct HC as [Hndk Hndu Hused Hcalls Hact Hcwf Hph Hq Hndq Hpc Hndpc Hord];
        cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
      pose proof (finish_src _ _ _ _ _ _ Hfin) as Hsrc.
      destruct (Hact t h op ret Hsrc) as (g & Hg & Hk).
      destruct g as [a p].
      assert (Hres_out : ~ In (a_res a) Q).
      { intros Hin. apply Hdone. rewrite <- Hk. change (gkey (a, p)) with (ts_owner (a_res a)). apply in_map. exact Hin. }
      assert (Hp2 : p = ph2).
      { pose proof (Hph _ Hg) as Hp. unfold PhaseOK in Hp. cbn [snd fst tm_queue] in Hp.
        destruct p as [| x |]; [| | reflexivity]; exfalso.
        - exact (Hres_out (proj2 (before_in _ _ _ Hp))).
        - exact (Hres_out (proj1 (proj2 Hp))). }
      subst p.
      assert (Hls : ls_linr (ac_op a) (ac_ret a) = ls_linr op ret).
      { assert (Hke : call_key (a_entry a) = call_key (Build_CallEntry t h (ActiveCall op ret)))
          by (rewrite a_entry_key; exact Hk).
        pose proof (NoDup_key_eq call_key _ _ _ Hcwf (Hcalls _ Hg) Hsrc Hke) as He.
        exact (f_equal (fun e => match ce_cell F e with ActiveCall o r => ls_linr o r | DeadCall => ls_linr op ret end) He). }
      destruct (in_split _ _ Hg) as (G1 & G2 & HG). subst G.
      assert (Hoth : forall g', In g' (G1 ++ G2) -> gkey g' <> (t, h))
        by (intros g' Hg'; rewrite <- Hk; exact (split_key_ne G1 G2 (a, ph2) g' Hndk Hg')).
      exists (G1 ++ G2). split.
      - rewrite !map_app. cbn [map].
        change (a_lin (a, ph2)) with (make_lin_entry (gkey (a, ph2)) (ls_linr (ac_op a) (ac_ret a))).
        rewrite Hk, Hls. apply lr_app.
        intros y Hy. apply in_map_iff in Hy as (g' & <- & Hg'). rewrite a_lin_key.
        apply Hoth. apply in_or_app. left. exact Hg'.
      - constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay].
        + rewrite map_app in Hndk |- *. cbn [map] in Hndk. exact (NoDup_remove_1 _ _ _ Hndk).
        + rewrite map_app in Hndu |- *. cbn [map] in Hndu. exact (NoDup_remove_1 _ _ _ Hndu).
        + intros g' Hg'. exact (Hused g' (in_rest _ _ _ _ Hg')).
        + intros g' Hg'. apply (finish_keep t h op ret calls calls' _ Hfin (Hcalls _ (in_rest _ _ _ _ Hg'))).
          rewrite a_entry_key. exact (Hoth g' Hg').
        + intros t' h' op' ret' Hin. destruct (finish_back _ _ _ _ _ _ _ Hfin Hin) as [Hin' | Heq]; [| discriminate Heq].
          destruct (Hact t' h' op' ret' Hin') as (g' & Hg' & Hk').
          destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
          * exfalso. pose proof (finish_call_well_formed _ _ _ _ _ _ Hfin Hcwf) as Hcwf'.
            assert (Hke : call_key (Build_CallEntry t' h' (ActiveCall op' ret')) = call_key (@Build_CallEntry F t h DeadCall)).
            { change ((t', h') = (t, h)). rewrite <- Hk', Hk. reflexivity. }
            pose proof (NoDup_key_eq call_key _ _ _ Hcwf' Hin (finish_tgt _ _ _ _ _ _ Hfin) Hke) as He.
            discriminate He.
          * exists g'. split; [exact Hg'' | exact Hk'].
        + exact (finish_call_well_formed _ _ _ _ _ _ Hfin Hcwf).
        + intros g' Hg'. exact (Hph g' (in_rest _ _ _ _ Hg')).
        + intros y Hy. destruct (Hq y Hy) as (g' & Hg' & Hf).
          destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
          * exfalso. apply Hdone. rewrite <- Hk. apply in_map_iff. exists y.
            split; [destruct Hf as [-> | ->]; reflexivity | exact Hy].
          * exists g'. split; [exact Hg'' | exact Hf].
        + exact Hndq.
        + intros x Hx. destruct (Hpc x Hx) as (g' & Hg' & Hs). destruct (in_upd G1 G2 _ g' Hg') as [-> | Hg''].
          * discriminate Hs.
          * exists g'. split; [exact Hg'' | exact Hs].
        + exact Hndpc.
        + intros a1 a2 Hb Hi2 Hi1. apply Hord; [| exact Hi2 | exact Hi1].
          rewrite map_fst_split. rewrite map_app in Hb. exact (before_insert _ _ _ _ _ Hb).
    Qed.

    (** *** The identity simulation *)

    Theorem cc_gsim : GSimRel V V (@idF F) SCC.
    Proof.
      intros c p (Pa & G & -> & HC). split; [| split; [| split]].
      - eexists _, _. reflexivity.
      - intros t h op c' Hst. remember (OverlayEvent (Build_ThreadEvent t (@InvEv F h op))) as ev eqn:Hev.
        revert HC.
        destruct Hst as [t0 h0 op0 q calls Q used trace ret Hcf Hprod Hft
                        | cand q q' calls Q Q' used Hsel Hlts
                        | t0 h0 op0 ret q calls calls' Q used Hfin Hdone]; intros HC.
        + injection Hev as -> -> ->.
          destruct (scc_invoke t h op q calls Q used trace ret Pa G HC Hcf Hprod Hft) as (G' & Hpi & HC').
          eexists. split; [exact Hpi |]. exists Pa, G'. split; [reflexivity | exact HC'].
        + discriminate Hev.
        + discriminate Hev.
      - intros ev c' Hst. remember (@UnderlayEvent F F ev) as e eqn:Hev.
        revert HC.
        destruct Hst as [t0 h0 op0 q calls Q used trace ret Hcf Hprod Hft
                        | cand q q' calls Q Q' used Hsel Hlts
                        | t0 h0 op0 ret q calls calls' Q used Hfin Hdone]; intros HC;
          [discriminate Hev | | discriminate Hev].
        destruct (scc_underlay cand q q' calls Q Q' used Pa G HC Hsel Hlts) as (Pa' & G' & Hps & HC').
        exists (POk (fst q') Pa' (map a_lin G')). split; [exact Hps |]. exists Pa', G'. split; [reflexivity | exact HC'].
      - intros t h op ret c' Hst. remember (OverlayEvent (Build_ThreadEvent t (@ResEv F h op ret))) as ev eqn:Hev.
        revert HC.
        destruct Hst as [t0 h0 op0 q calls Q used trace ret0 Hcf Hprod Hft
                        | cand q q' calls Q Q' used Hsel Hlts
                        | t0 h0 op0 ret0 q calls calls' Q used Hfin Hdone]; intros HC;
          [discriminate Hev | discriminate Hev |].
        assert (Ht : t0 = t)
          by exact (f_equal (fun e => match e with OverlayEvent x => te_tid F x | UnderlayEvent _ => t0 end) Hev).
        assert (Hh : h0 = h)
          by exact (f_equal (fun e => match e with OverlayEvent x => event_handle (te_ev F x) | UnderlayEvent _ => h0 end) Hev).
        assert (Hls : ls_linr op0 ret0 = ls_linr op ret)
          by exact (f_equal (fun e => match e with
                                      | OverlayEvent x => match te_ev F x with ResEv _ o r => ls_linr o r | InvEv _ o => ls_inv o end
                                      | UnderlayEvent _ => ls_linr op0 ret0 end) Hev).
        subst t0 h0.
        destruct (scc_return t h op0 ret0 q calls calls' Q used Pa G HC Hfin Hdone) as (G' & Hrem & HC').
        rewrite Hls in Hrem.
        exists (POk (fst q) Pa (map a_lin G)), (POk (fst q) Pa (map a_lin G')).
        split; [apply rt_refl |]. split; [exact (poss_return_ok V t h op ret (fst q, Pa) _ _ Hrem) |].
        exists Pa, G'. split; [reflexivity | exact HC'].
    Qed.

    Lemma cc_init (s0 : St) : SCC (initial_tagged_module V (s0, [])) (POk s0 [] []).
    Proof.
      exists [], []. split; [reflexivity |].
      constructor; cbn.
      - constructor.
      - constructor.
      - intros g [].
      - intros g [].
      - intros t h op ret [].
      - constructor.
      - intros g [].
      - intros y [].
      - constructor.
      - intros x [].
      - constructor.
      - intros a a' Hb. destruct (before_in _ _ _ Hb) as [[] _].
    Qed.

    (** *** What the copy-cat over [EI δ] means *)

    (** M-20 (a): every complete overlay trace of the relaxed copy-cat run
        over the effect-at-invocation LTS [EI δ] from [(s0, [])] is
        relaxed-linearizable to the sequential specification [seq_legal δ
        s0].  No well-formedness hypothesis: the copy-cat's traces are well
        formed ([cc_trace_wf]). *)
    Theorem cc_rel_lin (s0 : St) (s : list (ThreadEvent F)) :
      RTraces V (s0, []) s -> PrefixView.complete s ->
      rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δ s0).
    Proof.
      exact (gsim_rel_lin_traces V V idF SCC (s0, []) (s0, []) cc_gsim (cc_init s0) _
               (RelaxedHoareSpec.ei_hvf δ s0) s).
    Qed.

    Lemma cc_trace_wf (s0 : St) (s : list (ThreadEvent F)) : RTraces V (s0, []) s -> PrefixView.wf s.
    Proof. exact (gsim_trace_wf V V idF SCC (s0, []) (s0, []) cc_gsim (cc_init s0) s). Qed.
  End CopyCat.

  (** ** Part 3: consequences for [RCompLin] and for the RLHL route *)

  Section Meaning.
    Context {E F : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) (s0 : St).

    (** Copy-cat trace inclusion into [EI δ] implies relaxed
        linearizability of every complete overlay trace. *)
    Corollary complin_ei_rel_lin (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE) :
      RCompLin M VE σ0 (RelaxedHoareSpec.EI δ) (s0, []) ->
      forall s, MTraces VE M σ0 s -> PrefixView.complete s ->
        rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δ s0).
    Proof. intros HC s Hs Hc. exact (cc_rel_lin δ s0 s (HC s Hs) Hc). Qed.

    Section RLHL.
      Import RelaxedHoareBase RelaxedHoareGSim.
      Context {VE : LTS E} (I : Assn VE (RelaxedHoareSpec.EI δ))
              (R G : CallKey F -> PRel VE (RelaxedHoareSpec.EI δ)) (M : RelaxedModuleImpl E F) (σ0 : State VE).

      (** M-20: [rlhl_complin_ei] followed by [cc_rel_lin].  The
          relaxed-linearizability conclusion of the RLHL route is obtained
          from the copy-cat form. *)
      Corollary rlhl_complin_ei_rel_lin :
        RLHL2Hyps I R G M σ0 (s0, []) ->
        forall s, MTraces VE M σ0 s -> PrefixView.complete s ->
          rel_lin (@PrefixView.sel F) s (semi_independent F) (RelaxedHoareSpec.seq_legal δ s0).
      Proof. intros HH. exact (complin_ei_rel_lin M VE σ0 (rlhl_complin_ei δ s0 I R G M σ0 HH)). Qed.

      (** The statement of [RelaxedHoareGSim.rlhl_rel_lin_ei] (complete
          executions, every call returned), re-derived through the copy-cat
          form.  [gsim_dead_complete] turns [Hcomplete] into completeness
          of the overlay trace. *)
      Corollary rlhl_rel_lin_ei_via_cc (HH : RLHL2Hyps I R G M σ0 (s0, [])) evs c
          (Hexec : module_execution_tagged VE M (initial_tagged_module VE σ0) evs c)
          (Hcomplete : forall e, In e (tm_calls c) -> ce_cell F e = DeadCall) :
        rel_lin (@PrefixView.sel F) (overlay_events evs) (semi_independent F) (RelaxedHoareSpec.seq_legal δ s0).
      Proof.
        destruct (rlhl_gsim I R G M σ0 (s0, []) HH) as (S & HS & H0).
        apply (rlhl_complin_ei_rel_lin HH).
        - exists evs, c. split; [exact Hexec | reflexivity].
        - exact (gsim_dead_complete VE _ M S σ0 (s0, []) HS H0 evs c Hexec Hcomplete).
      Qed.
    End RLHL.
  End Meaning.

  (** ** Part 4: handle-linear presentations and [HLift] (m-20) *)

  Section HL.
    Context {E : RelaxedSig.t} (VE : LTS E).

    (** [HL VE]: [VE] with the list of invoked underlay keys; an
        invocation is enabled only on a key that is not in the list. *)
    Definition hlx_step (ev : ThreadEvent E) (σ σ' : State VE * list (CallKey E)) : Prop :=
      match te_ev E ev with
      | InvEv h _ => ~ In (te_tid E ev, h) (snd σ) /\ Step VE ev (fst σ) (fst σ') /\
                     snd σ' = (te_tid E ev, h) :: snd σ
      | ResEv _ _ _ => Step VE ev (fst σ) (fst σ') /\ snd σ' = snd σ
      end.

    Definition HL : LTS E :=
      {| State := (State VE * list (CallKey E))%type; Step := hlx_step; Error := fun ev σ => Error VE ev (fst σ) |}.

    Definition hl_used (σ : State HL) (k : CallKey E) : Prop := In k (snd σ).

    Theorem HL_handle_linear : RelaxedHoareBase.HandleLinear HL hl_used.
    Proof.
      constructor.
      - intros t h op σ σ' (_ & _ & Hu). unfold hl_used. cbn in Hu. rewrite Hu. left. reflexivity.
      - intros [t [h op | h op r]] σ σ' k Hs Hu; cbn in Hs; unfold hl_used in *.
        + destruct Hs as (_ & _ & ->). right. exact Hu.
        + destruct Hs as (_ & ->). exact Hu.
      - intros t h op σ σ' (Hn & _ & _). exact Hn.
    Qed.

    Lemma hl_step_base ev σ σ' : Step HL ev σ σ' -> Step VE ev (fst σ) (fst σ').
    Proof. cbn. unfold hlx_step. destruct (te_ev E ev); tauto. Qed.

    Context {G : RelaxedSig.t} (M : RelaxedModuleImpl E G).

    Definition lift_cfg (c : @TaggedModuleConfig E G VE) (u : list (CallKey E)) : @TaggedModuleConfig E G HL :=
      @Build_TaggedModuleConfig E G HL (tm_lts_state c, u) (tm_calls c) (tm_queue c) (tm_used_underlay c).

    Definition drop_cfg (c : @TaggedModuleConfig E G HL) : @TaggedModuleConfig E G VE :=
      @Build_TaggedModuleConfig E G VE (fst (tm_lts_state c)) (tm_calls c) (tm_queue c) (tm_used_underlay c).

    (** The underlay keys of the pending invocations of a queue. *)
    Definition qkeys (Q : TaggedQueue E G) : list (CallKey E) :=
      invocation_keys (map (fun x => untag (ts_event x)) Q).

    Lemma invocation_keys_app (l l' : list (ThreadEvent E)) :
      invocation_keys (l ++ l') = invocation_keys l ++ invocation_keys l'.
    Proof. induction l as [| e l IH]; [reflexivity |]. cbn. destruct (te_ev E e); cbn; rewrite IH; reflexivity. Qed.

    Lemma qkeys_app Q Q' : qkeys (Q ++ Q') = qkeys Q ++ qkeys Q'.
    Proof. unfold qkeys. rewrite map_app. apply invocation_keys_app. Qed.

    Lemma qkeys_schedule (k : CallKey G) (trace : list (TaggedEvent E)) :
      qkeys (schedule_trace_tagged k trace) = invocation_keys (map untag trace).
    Proof. unfold qkeys, schedule_trace_tagged. rewrite map_map. reflexivity. Qed.

    (** The invariant of the lifting: the pending invocations of the queue
        have distinct keys, none of them is in the list [u] of emitted
        invocations, and [u] and these keys are among the module's used
        underlay keys. *)
    Definition LiftOK (c : @TaggedModuleConfig E G VE) (u : list (CallKey E)) : Prop :=
      NoDup (qkeys (tm_queue c)) /\
      (forall k, In k (qkeys (tm_queue c)) -> ~ In k u /\ In k (tm_used_underlay c)) /\
      (forall k, In k u -> In k (tm_used_underlay c)).

    Lemma lift_step ev c c' u :
      module_step_tagged VE M ev c c' -> LiftOK c u ->
      exists u', module_step_tagged HL M ev (lift_cfg c u) (lift_cfg c' u') /\ LiftOK c' u'.
    Proof.
      intros Hst. destruct Hst as [t h op q calls Q used trace ret Hcf Hprod Hft
                                  | cand q q' calls Q Q' used Hsel Hlts
                                  | t h op ret q calls calls' Q used Hfin Hdone]; intros (Hnd & Hq & Hu);
        cbn [tm_queue tm_used_underlay tm_lts_state tm_calls] in *.
      - exists u. split; [exact (tagged_invoke HL M t h op (q, u) calls Q used trace ret Hcf Hprod Hft) |].
        destruct Hft as [Hftnd Hftu]. unfold LiftOK. cbn [tm_queue tm_used_underlay].
        rewrite qkeys_app, qkeys_schedule. split; [| split].
        + apply NoDup_app; [exact Hnd | exact Hftnd |]. intros k Hk1 Hk2. exact (Hftu k Hk2 (proj2 (Hq k Hk1))).
        + intros k Hk. apply in_app_or in Hk as [Hk | Hk].
          * destruct (Hq k Hk) as (Hn & Hin). split; [exact Hn | apply in_or_app; left; exact Hin].
          * split; [intros Hin; exact (Hftu k Hk (Hu k Hin)) | apply in_or_app; right; exact Hk].
        + intros k Hk. apply in_or_app. left. exact (Hu k Hk).
      - destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & HQ & HQ' & _).
        assert (Hqc : forall l, qkeys (cand :: l) = invocation_keys [untag (ts_event cand)] ++ qkeys l).
        { intros l. unfold qkeys. cbn [map]. destruct (untag (ts_event cand)) as [t0 [h0 op0 | h0 op0 r0]]; reflexivity. }
        assert (Hqk : qkeys Q = qkeys pre ++ invocation_keys [untag (ts_event cand)] ++ qkeys post)
          by (rewrite HQ, qkeys_app, Hqc; reflexivity).
        assert (Hqk' : qkeys Q' = qkeys pre ++ qkeys post) by (rewrite HQ', qkeys_app; reflexivity).
        destruct (untag (ts_event cand)) as [t [h op | h op r]] eqn:Hev.
        + cbn in Hqk. rewrite Hqk in Hnd, Hq.
          assert (Hk : In (t, h) (qkeys pre ++ (t, h) :: qkeys post)) by (apply in_elt).
          destruct (Hq _ Hk) as (Hnu & Hused).
          exists ((t, h) :: u). split.
          * cbn. rewrite <- Hev. apply (tagged_underlay HL M cand (q, u) (q', (t, h) :: u) calls Q Q' used Hsel).
            cbn. unfold hlx_step. rewrite Hev. cbn. split; [exact Hnu |]. split; [exact Hlts | reflexivity].
          * unfold LiftOK. cbn [tm_queue tm_used_underlay]. rewrite Hqk'. split; [| split].
            -- exact (NoDup_remove_1 _ _ _ Hnd).
            -- intros k Hk'. pose proof (NoDup_remove_2 _ _ _ Hnd) as Hn.
               assert (Hkin : In k (qkeys pre ++ (t, h) :: qkeys post)) by (exact (in_remove_in _ _ _ _ Hk')).
               destruct (Hq k Hkin) as (Hku & Hkused). split; [| exact Hkused].
               intros [Heq | Hin]; [subst k; exact (Hn Hk') | exact (Hku Hin)].
            -- intros k [<- | Hk']; [exact Hused | exact (Hu k Hk')].
        + cbn in Hqk. exists u. split.
          * cbn. rewrite <- Hev. apply (tagged_underlay HL M cand (q, u) (q', u) calls Q Q' used Hsel).
            cbn. unfold hlx_step. rewrite Hev. cbn. split; [exact Hlts | reflexivity].
          * unfold LiftOK. cbn [tm_queue tm_used_underlay]. rewrite Hqk'. rewrite Hqk in Hnd, Hq. split; [exact Hnd |].
            split; [exact Hq | exact Hu].
      - exists u. split; [exact (tagged_return HL M t h op ret (q, u) calls calls' Q used Hfin Hdone) |].
        split; [exact Hnd | split; [exact Hq | exact Hu]].
    Qed.

    Lemma lift_exec c evs c' :
      module_execution_tagged VE M c evs c' ->
      forall u, LiftOK c u -> exists u', module_execution_tagged HL M (lift_cfg c u) evs (lift_cfg c' u').
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros u Hok.
      - exists u. constructor.
      - destruct (lift_step ev c1 c2 u Hst Hok) as (u2 & Hst' & Hok2).
        destruct (IH u2 Hok2) as (u3 & Hex'). exists u3. econstructor; [exact Hst' | exact Hex'].
    Qed.

    Lemma drop_step ev c c' : module_step_tagged HL M ev c c' -> module_step_tagged VE M ev (drop_cfg c) (drop_cfg c').
    Proof.
      destruct 1 as [t h op q calls Q used trace ret Hcf Hprod Hft
                    | cand q q' calls Q Q' used Hsel Hlts
                    | t h op ret q calls calls' Q used Hfin Hdone]; cbn.
      - exact (tagged_invoke VE M t h op (fst q) calls Q used trace ret Hcf Hprod Hft).
      - exact (tagged_underlay VE M cand (fst q) (fst q') calls Q Q' used Hsel (hl_step_base _ _ _ Hlts)).
      - exact (tagged_return VE M t h op ret (fst q) calls calls' Q used Hfin Hdone).
    Qed.

    Lemma drop_exec c evs c' :
      module_execution_tagged HL M c evs c' -> module_execution_tagged VE M (drop_cfg c) evs (drop_cfg c').
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; [constructor |].
      econstructor; [exact (drop_step _ _ _ Hst) | exact IH].
    Qed.

    (** [HLift]: the overlay traces of [M] over [VE] and over its
        handle-linear presentation [HL VE] (from the empty key list)
        coincide.  The inclusion [⊆] uses the module's freshness of
        underlay keys ([trace_fresh] against [tm_used_underlay]); [⊇]
        forgets the key list. *)
    Theorem hlift (σ0 : State VE) (s : list (ThreadEvent G)) :
      MTraces VE M σ0 s <-> MTraces HL M (σ0, []) s.
    Proof.
      split.
      - intros (evs & c & Hex & Hov).
        destruct (lift_exec _ _ _ Hex [] ltac:(split; [constructor | split; [intros k [] | intros k []]])) as (u & Hex').
        exists evs, (lift_cfg c u). split; [exact Hex' | exact Hov].
      - intros (evs & c & Hex & Hov). exists evs, (drop_cfg c). split; [exact (drop_exec _ _ _ Hex) | exact Hov].
    Qed.
  End HL.

  Section HLCor.
    (** Copy-cat traces over [VF] and over [HL VF] coincide (the instance
        [M := idF] of [hlift]). *)
    Corollary rtraces_hlift {F : RelaxedSig.t} (VF : LTS F) (v : State VF) s :
      RTraces VF v s <-> RTraces (HL VF) (v, []) s.
    Proof. exact (hlift VF idF v s). Qed.

    (** Verifying [M] over [HL VE] or over [VE] gives the same copy-cat
        inclusion; the same on the overlay side. *)
    Corollary complin_hlift_under {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
        (VF : LTS F) (v0 : State VF) :
      RCompLin M VE σ0 VF v0 <-> RCompLin M (HL VE) (σ0, []) VF v0.
    Proof.
      split; intros HC s Hs; apply HC; apply (hlift VE M σ0 s); exact Hs.
    Qed.

    Corollary complin_hlift_over {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
        (VF : LTS F) (v0 : State VF) :
      RCompLin M VE σ0 VF v0 <-> RCompLin M VE σ0 (HL VF) (v0, []).
    Proof.
      split; intros HC s Hs; apply (rtraces_hlift VF v0 s); exact (HC s Hs).
    Qed.
  End HLCor.

  (** *** [EIhl]: the handle-linear sequential-specification LTS *)

  Section EIhl.
    Context {E : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect E), Sig.ar o -> St -> Prop).

    (** State [((s, P), used)]: [EI δ] with the list of invoked keys. *)
    Definition EIhl : LTS E := HL (RelaxedHoareSpec.EI δ).

    Theorem EIhl_handle_linear : RelaxedHoareBase.HandleLinear EIhl (hl_used (RelaxedHoareSpec.EI δ)).
    Proof. exact (HL_handle_linear (RelaxedHoareSpec.EI δ)). Qed.

    Corollary hlift_ei {F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (σ0 : State (RelaxedHoareSpec.EI δ)) s :
      MTraces (RelaxedHoareSpec.EI δ) M σ0 s <-> MTraces EIhl M (σ0, []) s.
    Proof. exact (hlift (RelaxedHoareSpec.EI δ) M σ0 s). Qed.

    (** *** A specification-independent frame (latest-review m-34)

        Adapted from the review's scratch session [FrameCheck] ([RecUsed],
        [Mine], [mine_step], [mine_res]).  Nothing below mentions [δ]'s
        values: the lemmas hold for every [δ]. *)

    (** Every pending record has a used key. *)
    Definition eihl_rec_used (σ : State EIhl) : Prop :=
      forall x, In x (snd (fst σ)) -> In (op_key x) (snd σ).

    (** The call [key] owns its record [x0]: [key] is used and every
        pending record with key [key] is [x0] ([x0] may have been
        consumed). *)
    Definition eihl_mine (key : CallKey E) (x0 : Op E) (σ : State EIhl) : Prop :=
      eihl_rec_used σ /\ In key (snd σ) /\ forall x, In x (snd (fst σ)) -> op_key x = key -> x = x0.

    (** Any number of [EIhl] steps, of any thread and operation. *)
    Definition eihl_steps : State EIhl -> State EIhl -> Prop :=
      clos_refl_trans _ (fun σ σ' => exists ev, Step EIhl ev σ σ').

    Lemma eihl_rec_used_init (s : St) : eihl_rec_used ((s, []), []).
    Proof. intros x []. Qed.

    Lemma eihl_rec_used_step ev σ σ' : Step EIhl ev σ σ' -> eihl_rec_used σ -> eihl_rec_used σ'.
    Proof.
      destruct σ as [[s P] u], σ' as [[s' P'] u'].
      destruct ev as [t [h o | h o r]]; cbn.
      - intros (_ & (r & st' & _ & Heq) & ->) Hru. injection Heq as -> ->.
        intros x [<- | Hx]; [left; reflexivity | right; exact (Hru x Hx)].
      - intros ((P1 & P2 & HP & Heq) & ->) Hru. injection Heq as -> ->.
        intros x Hx. apply Hru. rewrite HP.
        apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left | right; right]; exact Hx.
    Qed.

    Lemma eihl_rec_used_steps σ σ' : eihl_steps σ σ' -> eihl_rec_used σ -> eihl_rec_used σ'.
    Proof.
      induction 1 as [σ σ' (ev & Hs) | σ | σ σ1 σ' _ IH1 _ IH2]; intros H; auto.
      exact (eihl_rec_used_step ev σ σ' Hs H).
    Qed.

    (** Ownership is kept by every step: an invocation step needs an
        unused key (handle-linearity), and [key] is used. *)
    Lemma eihl_mine_step key x0 ev σ σ' : Step EIhl ev σ σ' -> eihl_mine key x0 σ -> eihl_mine key x0 σ'.
    Proof.
      intros Hs Hm. pose proof (eihl_rec_used_step ev σ σ' Hs (proj1 Hm)) as Hru'.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. destruct Hm as (_ & Hk & Hx).
      destruct ev as [t [h o | h o r]]; cbn in Hs, Hk, Hx |- *.
      - destruct Hs as (Hnu & (r & st' & _ & Heq) & ->). injection Heq as -> ->.
        split; [exact Hru' |]. split; [right; exact Hk |].
        intros x [<- | Hx'] Hkx; [exfalso; apply Hnu; cbn in Hkx; rewrite Hkx; exact Hk | exact (Hx x Hx' Hkx)].
      - destruct Hs as ((P1 & P2 & HP & Heq) & ->). injection Heq as -> ->.
        split; [exact Hru' |]. split; [exact Hk |].
        intros x Hx' Hkx. apply (Hx x); [| exact Hkx]. rewrite HP.
        apply in_app_or in Hx' as [Hx' | Hx']; apply in_or_app; [left | right; right]; exact Hx'.
    Qed.

    Lemma eihl_mine_steps key x0 σ σ' : eihl_steps σ σ' -> eihl_mine key x0 σ -> eihl_mine key x0 σ'.
    Proof.
      induction 1 as [σ σ' (ev & Hs) | σ | σ σ1 σ' _ IH1 _ IH2]; intros H; auto.
      exact (eihl_mine_step key x0 ev σ σ' Hs H).
    Qed.

    (** A response on [key] returns the owned record. *)
    Lemma eihl_mine_res key x0 o (r : Sig.ar o) σ σ' :
      eihl_mine key x0 σ ->
      Step EIhl (Build_ThreadEvent (fst key) (@ResEv E (snd key) o r)) σ σ' -> x0 = Build_Op key o r.
    Proof.
      destruct key as [k h]. destruct σ as [[s P] u], σ' as [[s' P'] u']. intros (_ & _ & Hx). cbn.
      intros ((P1 & P2 & HP & _) & _). cbn in HP, Hx. symmetry. apply Hx; [| reflexivity].
      rewrite HP. apply in_or_app. right. left. reflexivity.
    Qed.

    (** The own invocation establishes ownership: from a state whose
        records have used keys, the invocation step of [(t, h)] creates a
        record that [(t, h)] owns.  Key freshness is the step's own
        premise (the key is not in the used list). *)
    Lemma eihl_mine_inv t h o σ σ' :
      Step EIhl (Build_ThreadEvent t (@InvEv E h o)) σ σ' -> eihl_rec_used σ ->
      exists r st', δ (fst (fst σ)) o r st' /\
        σ' = ((st', Build_Op (t, h) o r :: snd (fst σ)), (t, h) :: snd σ) /\
        eihl_mine (t, h) (Build_Op (t, h) o r) σ'.
    Proof.
      intros Hs Hru. pose proof (eihl_rec_used_step _ σ σ' Hs Hru) as Hru'.
      destruct σ as [[s P] u], σ' as [[s' P'] u']. cbn in Hs |- *.
      destruct Hs as (Hnu & (r & st' & Hd & Heq) & ->). injection Heq as -> ->.
      exists r, st'. split; [exact Hd |]. split; [reflexivity |].
      split; [exact Hru' |]. split; [left; reflexivity |].
      intros x [<- | Hx] Hkx; [reflexivity |].
      exfalso. apply Hnu. rewrite <- Hkx. exact (Hru x Hx).
    Qed.

    Section RLHL.
      Import RelaxedHoareBase.
      Context {F : RelaxedSig.t} {StF : Type}.
      Context (δF : StF -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> StF -> Prop) (s0 : StF).

      (** The layering interface of research-intent §8 (M-20, corrected by
          m-20): a layer verified by RLHL over the handle-linear
          specification LTS [EIhl δ] of the layer below satisfies copy-cat
          inclusion over the plain [EI δ] of the layer below. *)
      Corollary rlhl_complin_eihl (I : Assn EIhl (RelaxedHoareSpec.EI δF))
          (R G : CallKey F -> PRel EIhl (RelaxedHoareSpec.EI δF)) (M : RelaxedModuleImpl E F)
          (σ0 : State (RelaxedHoareSpec.EI δ)) :
        RLHL2Hyps I R G M (σ0, []) (s0, []) ->
        RCompLin M (RelaxedHoareSpec.EI δ) σ0 (RelaxedHoareSpec.EI δF) (s0, []).
      Proof.
        intros HH. apply (proj2 (complin_hlift_under M (RelaxedHoareSpec.EI δ) σ0 _ _)).
        exact (rlhl_complin_ei δF s0 I R G M (σ0, []) HH).
      Qed.
    End RLHL.
  End EIhl.
End RelaxedHoareCompLinSpec.
