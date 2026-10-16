(** * Re-signature transport: overlay traces across overlay relations
      (task RLHL-latch L.8)

    Plan: .rocq-review/tasks/RLHL-latch.md, §3 row L.8, §5 item 4, §7
    check 5; used by the [lbw] datum of §2.6 (task L.9) and by the
    [si := ∅] corollaries of §2.5 (RD-4).

    ** Provenance and reuse
    Written in the RLHL-latch wave 1, which was stopped before its
    Writer reported (iteration-log 2026-10-15); RLHL-latch L.9 and the
    LatchSet corollaries are paused.  Reused unchanged by RLHL-seqlock
    (.rocq-review/tasks/RLHL-seqlock.md §3, "Dependency on RLHL-latch
    wave 1"; Addendum, [lb2_not_trace_rd]: "via [mtraces_rel_lin_resig]
    if needed"), where it moves trace-level results of the SeqLock
    module between overlay relations ([slRA], ∅, ...).  Task .0 of
    RLHL-seqlock re-checked this header and the Print Assumptions below
    (Rocq 9.3.0: 66 of the 70 results closed; the 4 others are listed
    under K); the code is as the wave-1 Writer left it.

    ** Plan check (RLHL-seqlock .0, against RLHL-latch.md §3 L.8)
    All L.8 items are present: [resig F si]; [ev_resig] (with the
    [event_]/[op_]/[mev_] versions and inverses); the configuration
    transport ([cfg_resig]/[cfg_unresig], [step_resig_iff],
    [exec_resig_iff]); [mtraces_resig] in both directions
    ([mtraces_resig_iff], [mtraces_unresig_iff]); [rel_lin_resig]
    (and [rel_lin_resig_seq], [mtraces_rel_lin_resig]); a test instance
    (Part 6, [CounterXYResig]).

    ** Why this file exists

    [RelaxedLTSSpec.ThreadEvent F] (and [CallEntry F], [CallKey F],
    [TaggedScheduledEvent E F], [TaggedModuleConfig], [Op F]) is indexed
    by the whole relaxed signature [F], including its
    [semi_independent] and [mode] fields.  So a trace
    [s : list (ThreadEvent (F_Lsi si1))] is not a trace at [F_Lsi si2]:
    the conversion fails (plan §7 check 5).  Comparing the traces of one
    module body under two overlay relations needs an explicit transport.

    ** What the module semantics reads of the overlay signature

    Nothing beyond its operations, arities and handles.  The only use of
    a semi-independence relation in [module_step_tagged]
    ([RelaxedModuleSemantics.v:578-610]) is [must_precede]
    ([RelaxedModuleSemantics.v:252-259]) inside
    [select_frontier_tagged], and it is instantiated at the *underlay*
    [E] (it compares [TaggedEvent E]s).  The overlay [F] enters only
    through the call pool ([CallEntry F]: key and [ActiveCall op ret]),
    the queue owners ([CallKey F]) and the overlay events.  The modes
    are not read either.  The kernel evidence is [step_resig_iff]
    below: for every [si], the transport is a bijection on
    configurations and module events that preserves and reflects every
    [module_step_tagged] step.  This is the mechanized counterpart of
    the paper's notation [⟦M⟧_E] (impl.tex:357: the denotation is
    parameterized by the underlay relation [E.I] only; impl.tex:81 and
    :213 name [E.I] as the only relation the Step rule reads).

    ** Definitions
    - [resig F si]: [F] with [semi_independent := si]; same [effect],
      [handle], [mode].  [resig (resig F si1) si2] is [resig F si2] by
      conversion; for a signature built with the record constructor
      ([CxySig si], [F_Lsi si]) [resig (CxySig si) si'] *is* [CxySig si']
      by conversion, so the generic results apply to concrete pairs
      directly ([CounterXYResig.F0_is_resig]).
    - [ev_resig]/[ev_unresig] (and [event_], [op_], [mev_] versions):
      the identity on the data, re-typed; mutually inverse
      ([ev_unresig_resig], [ev_resig_unresig], ...).
    - [cell_], [entry_], [tse_], [cfg_resig]/[cfg_unresig]: the
      configuration transport for [TaggedModuleConfig]; mutually inverse
      ([cfg_unresig_resig], [cfg_resig_unresig]); the initial
      configuration is fixed ([cfg_resig_initial]).
    - [resig_impl si M := fun op t => M op t]: the re-typed copy of [M]
      (bodies [Prog E (Sig.ar op)] do not mention [F]).
    - [sel_resig]: a selector re-typed through [ev_resig].

    ** Results (all closed)
    - [step_resig], [step_unresig], [step_resig_iff]; [exec_resig],
      [exec_unresig], [exec_resig_iff].  Stated for any [M'] with
      [HM : forall op t, M' op t = M op t] (a hypothesis only in the sense
      of identifying the copy; [resig_impl] discharges it by [eq_refl],
      and so does every concrete pair whose bodies do not use the
      relation, e.g. [M_cxy]/[M_cxy0]).
    - [mtraces_resig_iff]: [MTraces VE M σ0 s <-> MTraces VE M' σ0
      (map (ev_resig si) s)], every execution (complete or not), every
      underlay [VE], every [si]; [mtraces_unresig_iff] the same from the
      re-signed side; [mtraces_resig_impl] for [M' := resig_impl si M].
    - [in_ev_resig]: membership is reflected (for trace predicates such
      as the plan's [P1]/[P2]); [complete_resig]: [PrefixView.complete]
      is invariant.
    - [rel_lin_resig_sel] (any selector) and [rel_lin_resig] (overlay
      traces): [rel_lin sel s indep nu <-> rel_lin sel' (map ev_resig s)
      indep (fun W => nu (map op_unresig W))], *the same* [indep].
      [rel_lin] takes [indep] as an argument and never reads the
      signature's [semi_independent] field, so only the record type
      changes.  [rel_lin_resig_seq]: for [nu := seq_legal δ s0] no
      pull-back is needed ([seq_legal_resig]).
    - [mtraces_rel_lin_resig], [mtraces_rel_lin_seq_resig]: "every
      complete trace of [M] is relaxed-linearizable under [indep]"
      transfers to the re-typed copy at any overlay relation.

    ** Test instance (Part 6, [CounterXYResig]; Counter_xy of
       [examples/Relaxed/RelaxedHoareCounterXY.v])
    - [sb_mtraces0_by_resig] (closed): the SB trace of [M_cxy] at [FC]
      transports to [M_cxy0] at [F0], re-deriving [sb_mtraces ∅].
    - [lb_not_trace_mgen] ([eq_rect_eq], [classic]), new: the LB trace is
      a trace of [Mgen si_mb si] for *no* overlay relation [si]
      (CounterXY has it only at [si_cb], [lb_not_trace_b]).
    - [lb_admitted_not_exhibited] ([eq_rect_eq], [classic]): the pattern
      of the planned LatchSet [lbw] datum (RD-4): [Mgen si_mb
      by_counter] is verified with contract [by_counter]
      ([cxybcnt_rlhl2]), the contract admits LB ([lb_rel_lin_direct]),
      the module does not exhibit it.
    - [sb_rel_lin0_by_resig], [sb_not_rel_lin0_by_resig] (closed):
      [rel_lin_resig_seq] in both directions, re-deriving
      [sb_rel_lin_gen ∅ by_counter] and [sb_not_rel_lin0 ∅].
    - [cxy0_rel_lin_by_counter] ([eq_rect_eq], [classic]): every complete
      trace of [M_cxy0] (overlay [F0]) is relaxed-linearizable under
      [by_counter], from [cxy_rel_lin] at [FC].
    - [rtraces_not_resig_invariant] ([eq_rect_eq], [classic]): the scope
      limit below, on an instance.

    ** K / S / P / R
    - K: everything in Parts 1-5 is closed under the global context.
      Part 6: [lb_not_trace_mgen], [lb_admitted_not_exhibited],
      [rtraces_not_resig_invariant] and [cxy0_rel_lin_by_counter] use
      [Eqdep.Eq_rect_eq.eq_rect_eq] and [Classical_Prop.classic], both
      inherited from [RelaxedHoareCompLinSpec.cc_rel_lin] (and
      [rlhl_complin_eihl], [classic]) through
      [RelaxedHoareCounterXY.lb_not_trace_b], [cxy_complin_ei] and
      [cxy_rel_lin]; no proof in this file uses an axiom directly.  The
      rest of Part 6 is closed.
    - S: an exact bisimulation of the module semantics across overlay
      relations, for every execution (prefixes included), every
      underlay, every [M]; [rel_lin] transport for complete traces
      (as [rel_lin] itself).
    - P: no paper statement cites this file.  It mechanizes the fact
      implicit in impl.tex:357 ([⟦M⟧_E] depends on [E.I] only); the
      overlay relation [F.I] enters only the correctness criterion
      (relaxed linearizability / the copy-cat over [ν_F]).
    - R: infrastructure; no reviewer concern asks for it directly.  It
      supports the LatchSet claims of plan §1 ("the proof is uniform in
      [si], including ∅", RD-4) at the level of traces.

    ** Limitations and scope
    - Overlay only.  The underlay relation is read by the frontier, so
      nothing here transports across *underlay* relations.  In
      particular the copy-cat [idF : RelaxedModuleImpl F F] has [F] as
      its underlay, so [RTraces]/[RCompLin] over [VF : LTS F] are not
      invariant: [rtraces_not_resig_invariant] (the SB trace is a
      copy-cat trace of [EI δcxy] at [FC], not at [F0]).
    - The RLHL judgement does not transfer.  The abstract possibility
      semantics reads the overlay relation
      ([RelaxedPossibility.older_entry_allows_invocation], :111-120,
      through [invocation_ready]/[lin_invoke_update]), so [GSimRel] and
      [RLHL2Hyps] depend on it ([RelaxedHoareCounterXY.cxy_discriminates_rlhl2]:
      same bodies, [RLHL2Hyps] at [FC], none at [F0]).  What transfers
      is every trace-level consequence (Parts 4-5).
    - Only [semi_independent] is replaced; [mode] is kept, as the task
      asks, although the module semantics does not read it either.
    - For an abstract [F], [F] and [resig F (semi_independent F)] are not
      convertible ([RelaxedSig.t] has no definitional eta), hence the
      separate [unresig] direction.
    - Part 6 makes this [models/] file import
      [examples.Relaxed.RelaxedHoareCounterXY] (allowed by the task
      brief, which asked for the test to stay in this file).  This
      inverts the usual models/examples layering, and [_CoqProject]
      lists this file before [RelaxedHoareCounterXY.v] (coqdep orders
      the build correctly).  Moving Part 6 to an [examples/] file at the
      next [_CoqProject] edit would restore the layering; nothing in
      Parts 1-5 depends on it.

    ** Provisional decisions relied on
    None is needed for Parts 1-5.  The file serves RD-4 (export I_L and
    state the ∅ corollary; the [lbw] datum) and the plan's §5 item 4
    correction; Part 6's [lb_admitted_not_exhibited] shows the RD-4
    pattern on Counter_xy, not on LatchSet. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Relations.Relation_Definitions.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
(* Only for the test instance, Part 6. *)
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import examples.Relaxed.RelaxedHoareCounterXY.

Import ListNotations.


Module RelaxedHoareResig.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import RelaxedHoareCompLin.

  (** ** Part 1: the re-signature *)

  (** [resig F si]: the operations, arities, handles and modes of [F],
      with the semi-independence relation replaced by [si]. *)
  Definition resig (F : RelaxedSig.t) (si : relation (Sig.op (RelaxedSig.effect F))) : RelaxedSig.t :=
    {| RelaxedSig.effect := RelaxedSig.effect F;
       RelaxedSig.handle := RelaxedSig.handle F;
       RelaxedSig.semi_independent := si;
       RelaxedSig.mode := RelaxedSig.mode F |}.

  Lemma resig_effect F si : RelaxedSig.effect (resig F si) = RelaxedSig.effect F.
  Proof. reflexivity. Qed.

  Lemma resig_handle F si : RelaxedSig.handle (resig F si) = RelaxedSig.handle F.
  Proof. reflexivity. Qed.

  Lemma resig_semi_independent F si : RelaxedSig.semi_independent (resig F si) = si.
  Proof. reflexivity. Qed.

  (** Re-signing twice is re-signing once, by conversion. *)
  Lemma resig_resig F si1 si2 : resig (resig F si1) si2 = resig F si2.
  Proof. reflexivity. Qed.

  (** Shrinking the relation keeps the signature well-formed (irreflexive
      and mode-compatible); in particular [resig F (fun _ _ => False)]. *)
  Lemma resig_well_formed_sub F (si : relation (Sig.op (RelaxedSig.effect F))) :
    RelaxedSig.well_formed F -> (forall a b, si a b -> RelaxedSig.semi_independent F a b) ->
    RelaxedSig.well_formed (resig F si).
  Proof.
    intros [Hirr Hl Hr] Hsub. constructor.
    - intros a Ha. exact (Hirr a (Hsub a a Ha)).
    - intros a b Hab. exact (Hl a b (Hsub a b Hab)).
    - intros a b Hab. exact (Hr a b (Hsub a b Hab)).
  Qed.

  (** ** Part 2: events, operation records and module events *)

  Section Events.
    Context {F : RelaxedSig.t} (si : relation (Sig.op (RelaxedSig.effect F))).
    Local Abbreviation F' := (resig F si).

    Definition event_resig (e : Event F) : Event F' :=
      match e with
      | InvEv h op => @InvEv F' h op
      | ResEv h op r => @ResEv F' h op r
      end.

    Definition event_unresig (e : Event F') : Event F :=
      match e with
      | InvEv h op => @InvEv F h op
      | ResEv h op r => @ResEv F h op r
      end.

    Definition ev_resig (e : ThreadEvent F) : ThreadEvent F' :=
      Build_ThreadEvent (te_tid F e) (event_resig (te_ev F e)).

    Definition ev_unresig (e : ThreadEvent F') : ThreadEvent F :=
      Build_ThreadEvent (te_tid F' e) (event_unresig (te_ev F' e)).

    Lemma ev_unresig_resig e : ev_unresig (ev_resig e) = e.
    Proof. destruct e as [t [h op | h op r]]; reflexivity. Qed.

    Lemma ev_resig_unresig e : ev_resig (ev_unresig e) = e.
    Proof. destruct e as [t [h op | h op r]]; reflexivity. Qed.

    Lemma map_ev_unresig_resig s : map ev_unresig (map ev_resig s) = s.
    Proof. induction s as [| e s IH]; cbn; [reflexivity | rewrite ev_unresig_resig, IH; reflexivity]. Qed.

    Lemma map_ev_resig_unresig s : map ev_resig (map ev_unresig s) = s.
    Proof. induction s as [| e s IH]; cbn; [reflexivity | rewrite ev_resig_unresig, IH; reflexivity]. Qed.

    Definition op_resig (o : Op F) : Op F' := @Build_Op F' (op_key o) (op_op o) (op_ret o).
    Definition op_unresig (o : Op F') : Op F := @Build_Op F (op_key o) (op_op o) (op_ret o).

    Lemma op_unresig_resig o : op_unresig (op_resig o) = o.
    Proof. destruct o; reflexivity. Qed.

    Lemma op_resig_unresig o : op_resig (op_unresig o) = o.
    Proof. destruct o; reflexivity. Qed.

    Lemma map_op_unresig_resig W : map op_unresig (map op_resig W) = W.
    Proof. induction W as [| o W IH]; cbn; [reflexivity | rewrite op_unresig_resig, IH; reflexivity]. Qed.

    Lemma map_op_resig_unresig W : map op_resig (map op_unresig W) = W.
    Proof. induction W as [| o W IH]; cbn; [reflexivity | rewrite op_resig_unresig, IH; reflexivity]. Qed.

    Definition mev_resig {E : RelaxedSig.t} (ev : ModuleEvent E F) : ModuleEvent E F' :=
      match ev with
      | UnderlayEvent e => UnderlayEvent e
      | OverlayEvent e => OverlayEvent (ev_resig e)
      end.

    Definition mev_unresig {E : RelaxedSig.t} (ev : ModuleEvent E F') : ModuleEvent E F :=
      match ev with
      | UnderlayEvent e => UnderlayEvent e
      | OverlayEvent e => OverlayEvent (ev_unresig e)
      end.

    Lemma mev_unresig_resig {E : RelaxedSig.t} (ev : ModuleEvent E F) : mev_unresig (mev_resig ev) = ev.
    Proof. destruct ev as [e | e]; cbn; [reflexivity | rewrite ev_unresig_resig; reflexivity]. Qed.

    Lemma mev_resig_unresig {E : RelaxedSig.t} (ev : ModuleEvent E F') : mev_resig (mev_unresig ev) = ev.
    Proof. destruct ev as [e | e]; cbn; [reflexivity | rewrite ev_resig_unresig; reflexivity]. Qed.

    Lemma overlay_events_resig {E : RelaxedSig.t} (evs : list (ModuleEvent E F)) :
      RelaxedGSim.overlay_events (map mev_resig evs) = map ev_resig (RelaxedGSim.overlay_events evs).
    Proof. induction evs as [| [e | e] evs IH]; [reflexivity | exact IH | cbn; f_equal; exact IH]. Qed.

    Lemma overlay_events_unresig {E : RelaxedSig.t} (evs : list (ModuleEvent E F')) :
      RelaxedGSim.overlay_events (map mev_unresig evs) = map ev_unresig (RelaxedGSim.overlay_events evs).
    Proof. induction evs as [| [e | e] evs IH]; [reflexivity | exact IH | cbn; f_equal; exact IH]. Qed.
  End Events.

  (** ** Part 3: configurations and module steps *)

  Section Config.
    Context {E F : RelaxedSig.t} (si : relation (Sig.op (RelaxedSig.effect F))).
    Context (VE : LTS E).
    Local Abbreviation F' := (resig F si).

    Definition cell_resig (c : CallCell F) : CallCell F' :=
      match c with ActiveCall op ret => @ActiveCall F' op ret | DeadCall => @DeadCall F' end.
    Definition cell_unresig (c : CallCell F') : CallCell F :=
      match c with ActiveCall op ret => @ActiveCall F op ret | DeadCall => @DeadCall F end.

    Definition entry_resig (e : CallEntry F) : CallEntry F' :=
      @Build_CallEntry F' (ce_tid F e) (ce_handle F e) (cell_resig (ce_cell F e)).
    Definition entry_unresig (e : CallEntry F') : CallEntry F :=
      @Build_CallEntry F (ce_tid F' e) (ce_handle F' e) (cell_unresig (ce_cell F' e)).

    Definition tse_resig (m : TaggedScheduledEvent E F) : TaggedScheduledEvent E F' :=
      @Build_TaggedScheduledEvent E F' (ts_owner m) (ts_event m).
    Definition tse_unresig (m : TaggedScheduledEvent E F') : TaggedScheduledEvent E F :=
      @Build_TaggedScheduledEvent E F (ts_owner m) (ts_event m).

    Definition cfg_resig (c : @TaggedModuleConfig E F VE) : @TaggedModuleConfig E F' VE :=
      @Build_TaggedModuleConfig E F' VE (tm_lts_state c) (map entry_resig (tm_calls c))
        (map tse_resig (tm_queue c)) (tm_used_underlay c).
    Definition cfg_unresig (c : @TaggedModuleConfig E F' VE) : @TaggedModuleConfig E F VE :=
      @Build_TaggedModuleConfig E F VE (tm_lts_state c) (map entry_unresig (tm_calls c))
        (map tse_unresig (tm_queue c)) (tm_used_underlay c).

    Lemma cfg_unresig_resig c : cfg_unresig (cfg_resig c) = c.
    Proof.
      destruct c as [q pool queue used]. unfold cfg_unresig, cfg_resig. cbn. rewrite !map_map. f_equal.
      - rewrite <- (map_id pool) at 2. apply map_ext. intros [t h [op ret |]]; reflexivity.
      - rewrite <- (map_id queue) at 2. apply map_ext. intros [k m]; reflexivity.
    Qed.

    Lemma cfg_resig_unresig c : cfg_resig (cfg_unresig c) = c.
    Proof.
      destruct c as [q pool queue used]. unfold cfg_unresig, cfg_resig. cbn. rewrite !map_map. f_equal.
      - rewrite <- (map_id pool) at 2. apply map_ext. intros [t h [op ret |]]; reflexivity.
      - rewrite <- (map_id queue) at 2. apply map_ext. intros [k m]; reflexivity.
    Qed.

    Lemma cfg_resig_initial σ0 : cfg_resig (initial_tagged_module VE σ0) = initial_tagged_module VE σ0.
    Proof. reflexivity. Qed.

    Lemma cfg_unresig_initial σ0 : cfg_unresig (initial_tagged_module VE σ0) = initial_tagged_module VE σ0.
    Proof. reflexivity. Qed.

    (** The overlay keys of the pool and the owners of the queue are
        unchanged. *)
    Lemma keys_resig (pool : CallPool F) : map call_key (map entry_resig pool) = map call_key pool.
    Proof. induction pool as [| e pool IH]; [reflexivity | cbn; f_equal; exact IH]. Qed.

    Lemma keys_unresig (pool : CallPool F') : map call_key (map entry_unresig pool) = map call_key pool.
    Proof. induction pool as [| e pool IH]; [reflexivity | cbn; f_equal; exact IH]. Qed.

    Lemma owners_resig (queue : TaggedQueue E F) : map ts_owner (map tse_resig queue) = map ts_owner queue.
    Proof. induction queue as [| m queue IH]; [reflexivity | cbn; f_equal; exact IH]. Qed.

    Lemma owners_unresig (queue : TaggedQueue E F') : map ts_owner (map tse_unresig queue) = map ts_owner queue.
    Proof. induction queue as [| m queue IH]; [reflexivity | cbn; f_equal; exact IH]. Qed.

    Lemma schedule_resig (k : CallKey F) (trace : list (TaggedEvent E)) :
      map tse_resig (schedule_trace_tagged k trace) = @schedule_trace_tagged E F' k trace.
    Proof. induction trace as [| m trace IH]; [reflexivity | cbn; f_equal; exact IH]. Qed.

    Lemma schedule_unresig (k : CallKey F') (trace : list (TaggedEvent E)) :
      map tse_unresig (schedule_trace_tagged k trace) = @schedule_trace_tagged E F k trace.
    Proof. induction trace as [| m trace IH]; [reflexivity | cbn; f_equal; exact IH]. Qed.

    Lemma finish_call_resig t h op ret (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' ->
      @finish_call F' t h op ret (map entry_resig pool) (map entry_resig pool').
    Proof.
      induction 1 as [tail | t' h' cell pool pool' Hneq Hfin IH]; cbn.
      - apply finish_here.
      - apply finish_next; [exact Hneq | exact IH].
    Qed.

    Lemma finish_call_unresig t h op ret (pool pool' : CallPool F') :
      finish_call t h op ret pool pool' ->
      @finish_call F t h op ret (map entry_unresig pool) (map entry_unresig pool').
    Proof.
      induction 1 as [tail | t' h' cell pool pool' Hneq Hfin IH]; cbn.
      - apply finish_here.
      - apply finish_next; [exact Hneq | exact IH].
    Qed.

    (** The frontier: [tagged_can_cross] reads only the tagged underlay
        events, which the transport does not touch. *)
    Lemma select_resig (cand : TaggedScheduledEvent E F) queue queue' :
      select_frontier_tagged cand queue queue' ->
      select_frontier_tagged (tse_resig cand) (map tse_resig queue) (map tse_resig queue').
    Proof.
      induction 1 as [suffix | earlier queue queue' Hcross Hsel IH]; cbn.
      - apply tagged_select_here.
      - apply tagged_select_next; [exact Hcross | exact IH].
    Qed.

    Lemma select_unresig (cand : TaggedScheduledEvent E F') queue queue' :
      select_frontier_tagged cand queue queue' ->
      select_frontier_tagged (tse_unresig cand) (map tse_unresig queue) (map tse_unresig queue').
    Proof.
      induction 1 as [suffix | earlier queue queue' Hcross Hsel IH]; cbn.
      - apply tagged_select_here.
      - apply tagged_select_next; [exact Hcross | exact IH].
    Qed.

    Section Impl.
      Context (M : RelaxedModuleImpl E F) (M' : RelaxedModuleImpl E F').
      (** The two modules have the same bodies.  [Prog E _] does not
          mention [F], so [M] itself has type [RelaxedModuleImpl E F']
          and [M' := M] satisfies this by [eq_refl] ([resig_impl]). *)
      Context (HM : forall op t, M' op t = M op t).

      Lemma step_resig ev c c' :
        module_step_tagged VE M ev c c' ->
        module_step_tagged VE M' (mev_resig si ev) (cfg_resig c) (cfg_resig c').
      Proof.
        destruct 1 as [t h op q pool queue used trace ret Hfresh Hmeth Htr
                      | cand q q' pool queue queue' used Hsel Hlts
                      | t h op ret q pool pool' queue used Hfin Hdone]; unfold cfg_resig; cbn.
        - rewrite map_app, schedule_resig.
          apply (tagged_invoke VE M' t h op q (map entry_resig pool) (map tse_resig queue) used trace ret).
          + unfold call_fresh. rewrite keys_resig. exact Hfresh.
          + rewrite HM. exact Hmeth.
          + exact Htr.
        - exact (tagged_underlay VE M' (tse_resig cand) q q' (map entry_resig pool) (map tse_resig queue)
                   (map tse_resig queue') used (select_resig _ _ _ Hsel) Hlts).
        - apply tagged_return.
          + apply finish_call_resig. exact Hfin.
          + unfold owner_done_tagged. rewrite owners_resig. exact Hdone.
      Qed.

      Lemma step_unresig ev c c' :
        module_step_tagged VE M' ev c c' ->
        module_step_tagged VE M (mev_unresig si ev) (cfg_unresig c) (cfg_unresig c').
      Proof.
        destruct 1 as [t h op q pool queue used trace ret Hfresh Hmeth Htr
                      | cand q q' pool queue queue' used Hsel Hlts
                      | t h op ret q pool pool' queue used Hfin Hdone]; unfold cfg_unresig; cbn.
        - rewrite map_app, schedule_unresig.
          apply (tagged_invoke VE M t h op q (map entry_unresig pool) (map tse_unresig queue) used trace ret).
          + unfold call_fresh. rewrite keys_unresig. exact Hfresh.
          + rewrite <- HM. exact Hmeth.
          + exact Htr.
        - exact (tagged_underlay VE M (tse_unresig cand) q q' (map entry_unresig pool) (map tse_unresig queue)
                   (map tse_unresig queue') used (select_unresig _ _ _ Hsel) Hlts).
        - apply tagged_return.
          + apply finish_call_unresig. exact Hfin.
          + unfold owner_done_tagged. rewrite owners_unresig. exact Hdone.
      Qed.

      (** The transport is a bijection on configurations and events that
          preserves and reflects every module step. *)
      Theorem step_resig_iff ev c c' :
        module_step_tagged VE M ev c c' <->
        module_step_tagged VE M' (mev_resig si ev) (cfg_resig c) (cfg_resig c').
      Proof.
        split; [apply step_resig |]. intros H.
        pose proof (step_unresig _ _ _ H) as H'.
        rewrite mev_unresig_resig, !cfg_unresig_resig in H'. exact H'.
      Qed.

      Lemma exec_resig c evs c' :
        module_execution_tagged VE M c evs c' ->
        module_execution_tagged VE M' (cfg_resig c) (map (mev_resig si) evs) (cfg_resig c').
      Proof.
        induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; cbn.
        - apply tagged_module_execution_refl.
        - eapply tagged_module_execution_cons; [apply step_resig; exact Hst | exact IH].
      Qed.

      Lemma exec_unresig c evs c' :
        module_execution_tagged VE M' c evs c' ->
        module_execution_tagged VE M (cfg_unresig c) (map (mev_unresig si) evs) (cfg_unresig c').
      Proof.
        induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; cbn.
        - apply tagged_module_execution_refl.
        - eapply tagged_module_execution_cons; [apply step_unresig; exact Hst | exact IH].
      Qed.

      Theorem exec_resig_iff c evs c' :
        module_execution_tagged VE M c evs c' <->
        module_execution_tagged VE M' (cfg_resig c) (map (mev_resig si) evs) (cfg_resig c').
      Proof.
        split; [apply exec_resig |]. intros H.
        pose proof (exec_unresig _ _ _ H) as H'.
        rewrite map_map, !cfg_unresig_resig in H'.
        rewrite (map_ext _ (fun x => x) (@mev_unresig_resig F si E)), map_id in H'. exact H'.
      Qed.
    End Impl.
  End Config.

  (** ** Part 4: module traces *)

  (** The re-typed copy of a module: the same bodies. *)
  Definition resig_impl {E F : RelaxedSig.t} (si : relation (Sig.op (RelaxedSig.effect F)))
      (M : RelaxedModuleImpl E F) : RelaxedModuleImpl E (resig F si) :=
    fun op t => M op t.

  Section Traces.
    Context {E F : RelaxedSig.t} (si : relation (Sig.op (RelaxedSig.effect F))).
    Context (VE : LTS E) (M : RelaxedModuleImpl E F) (M' : RelaxedModuleImpl E (resig F si)).
    Context (HM : forall op t, M' op t = M op t).

    Lemma mtraces_resig σ0 s :
      MTraces VE M σ0 s -> MTraces VE M' σ0 (map (ev_resig si) s).
    Proof.
      intros (evs & c & Hex & Hov).
      exists (map (mev_resig si) evs), (cfg_resig si VE c). split.
      - exact (exec_resig si VE M M' HM _ _ _ Hex).
      - rewrite overlay_events_resig, Hov. reflexivity.
    Qed.

    Lemma mtraces_unresig σ0 s' :
      MTraces VE M' σ0 s' -> MTraces VE M σ0 (map (ev_unresig si) s').
    Proof.
      intros (evs & c & Hex & Hov).
      exists (map (mev_unresig si) evs), (cfg_unresig si VE c). split.
      - exact (exec_unresig si VE M M' HM _ _ _ Hex).
      - rewrite overlay_events_unresig, Hov. reflexivity.
    Qed.

    (** L.8 target: the overlay traces of a module are the same for every
        overlay relation, up to the re-typing [ev_resig]. *)
    Theorem mtraces_resig_iff σ0 s :
      MTraces VE M σ0 s <-> MTraces VE M' σ0 (map (ev_resig si) s).
    Proof.
      split; [apply mtraces_resig |]. intros H.
      pose proof (mtraces_unresig _ _ H) as H'. rewrite map_ev_unresig_resig in H'. exact H'.
    Qed.

    Theorem mtraces_unresig_iff σ0 s' :
      MTraces VE M' σ0 s' <-> MTraces VE M σ0 (map (ev_unresig si) s').
    Proof.
      split; [apply mtraces_unresig |]. intros H.
      pose proof (mtraces_resig _ _ H) as H'. rewrite map_ev_resig_unresig in H'. exact H'.
    Qed.
  End Traces.

  Corollary mtraces_resig_impl {E F : RelaxedSig.t} si (VE : LTS E) (M : RelaxedModuleImpl E F) σ0 s :
    MTraces VE M σ0 s <-> MTraces VE (resig_impl si M) σ0 (map (ev_resig si) s).
  Proof. exact (mtraces_resig_iff si VE M (resig_impl si M) (fun _ _ => eq_refl) σ0 s). Qed.

  (** Membership is reflected, so trace predicates such as the plan's
      [P1]/[P2] (stated with [In (Build_ThreadEvent t (InvEv h op)) s])
      transfer. *)
  Lemma in_ev_resig {F : RelaxedSig.t} si (s : list (ThreadEvent F)) e :
    In (ev_resig si e) (map (ev_resig si) s) <-> In e s.
  Proof.
    split; [| apply in_map]. intros H. apply in_map_iff in H. destruct H as (e' & He & Hin).
    apply (f_equal (ev_unresig si)) in He. rewrite !ev_unresig_resig in He. subst e'. exact Hin.
  Qed.

  (** ** Part 5: relaxed linearizability

      [rel_lin] takes the semi-independence relation [indep] as an
      argument and never reads the signature's [semi_independent] field,
      so the only thing to transport is the type of the operation records
      ([Op F] vs [Op (resig F si)]): the specification [nu] is pulled back
      along [op_unresig]. *)

  Lemma before_map {A B : Type} (f : A -> B) (W : list A) a b :
    before W a b -> before (map f W) (f a) (f b).
  Proof.
    intros (l1 & l2 & -> & Hin). exists (map f l1), (map f l2).
    split; [rewrite map_app; reflexivity | apply in_map; exact Hin].
  Qed.

  Lemma rel_lin_nu_iff {E : RelaxedSig.t} {X : Type} (sel : X -> option (ThreadEvent E)) (L : list X) indep
      (nu1 nu2 : list (Op E) -> Prop) :
    (forall W, nu1 W <-> nu2 W) -> (rel_lin sel L indep nu1 <-> rel_lin sel L indep nu2).
  Proof.
    intros Hnu. split; intros (W & H1 & Hrest); exists W; split; [apply Hnu; exact H1 | exact Hrest | apply Hnu; exact H1 | exact Hrest].
  Qed.

  Section RelLinSel.
    Context {F : RelaxedSig.t} (si : relation (Sig.op (RelaxedSig.effect F))).
    Context {X : Type} (sel : X -> option (ThreadEvent F)) (L : list X).
    Local Abbreviation F' := (resig F si).

    Definition sel_resig (x : X) : option (ThreadEvent F') := option_map (ev_resig si) (sel x).

    Lemma inv_at_resig i (k : CallKey F) (op : Sig.op (RelaxedSig.effect F)) :
      inv_at sel_resig L i k op <-> inv_at sel L i k op.
    Proof.
      unfold inv_at, sel_resig. split; intros (x & Hx & Hs); exists x; split; try exact Hx.
      - destruct (sel x) as [e |]; cbn [option_map] in Hs; [| discriminate Hs].
        apply (f_equal (option_map (ev_unresig si))) in Hs. cbn [option_map] in Hs.
        rewrite ev_unresig_resig in Hs. rewrite Hs. reflexivity.
      - rewrite Hs. reflexivity.
    Qed.

    Lemma res_at_resig j (k : CallKey F) (op : Sig.op (RelaxedSig.effect F)) (r : Sig.ar op) :
      res_at sel_resig L j k op r <-> res_at sel L j k op r.
    Proof.
      unfold res_at, sel_resig. split; intros (x & Hx & Hs); exists x; split; try exact Hx.
      - destruct (sel x) as [e |]; cbn [option_map] in Hs; [| discriminate Hs].
        apply (f_equal (option_map (ev_unresig si))) in Hs. cbn [option_map] in Hs.
        rewrite ev_unresig_resig in Hs. rewrite Hs. reflexivity.
      - rewrite Hs. reflexivity.
    Qed.

    Lemma occurs_resig (o : Op F') : occurs sel_resig L o <-> occurs sel L (op_unresig si o).
    Proof.
      unfold occurs. split; intros [(i & Hi) (j & Hj)]; split.
      - exists i. exact (proj1 (inv_at_resig i _ _) Hi).
      - exists j. exact (proj1 (res_at_resig j _ _ _) Hj).
      - exists i. exact (proj2 (inv_at_resig i _ _) Hi).
      - exists j. exact (proj2 (res_at_resig j _ _ _) Hj).
    Qed.

    Lemma rhb_resig indep (o o' : Op F') :
      rhb sel_resig L indep o o' <-> rhb sel L indep (op_unresig si o) (op_unresig si o').
    Proof.
      unfold rhb. split.
      - intros [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + left. exists i, j. split; [exact (proj1 (res_at_resig i _ _ _) Hi) |].
          split; [exact (proj1 (inv_at_resig j _ _) Hj) | exact Hij].
        + right. split; [exact Ht |]. exists i, j.
          split; [exact (proj1 (inv_at_resig i _ _) Hi) |].
          split; [exact (proj1 (inv_at_resig j _ _) Hj) |]. split; [exact Hij | exact Hn].
      - intros [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + left. exists i, j. split; [exact (proj2 (res_at_resig i _ _ _) Hi) |].
          split; [exact (proj2 (inv_at_resig j _ _) Hj) | exact Hij].
        + right. split; [exact Ht |]. exists i, j.
          split; [exact (proj2 (inv_at_resig i _ _) Hi) |].
          split; [exact (proj2 (inv_at_resig j _ _) Hj) |]. split; [exact Hij | exact Hn].
    Qed.

    (** For a general selector: the same [indep], the specification
        pulled back along [op_unresig]. *)
    Theorem rel_lin_resig_sel indep (nu : list (Op F) -> Prop) :
      rel_lin sel L indep nu <-> rel_lin sel_resig L indep (fun W => nu (map (op_unresig si) W)).
    Proof.
      split.
      - intros (W & Hnu & Hnd & Hocc & Hall & Hord). exists (map (op_resig si) W).
        split; [| split; [| split; [| split]]].
        + rewrite map_op_unresig_resig. exact Hnu.
        + rewrite map_map. exact Hnd.
        + intros o' Ho'. apply in_map_iff in Ho'. destruct Ho' as (o & <- & Ho).
          apply occurs_resig. rewrite op_unresig_resig. exact (Hocc o Ho).
        + intros i k op Hi. destruct (Hall i k op (proj1 (inv_at_resig i k op) Hi)) as (o & Ho & Hk).
          exists (op_resig si o). split; [apply in_map; exact Ho | exact Hk].
        + intros o1' o2' H1 H2 Hr. apply in_map_iff in H1, H2.
          destruct H1 as (o1 & <- & H1). destruct H2 as (o2 & <- & H2).
          apply before_map. apply Hord; [exact H1 | exact H2 |].
          apply rhb_resig in Hr. rewrite !op_unresig_resig in Hr. exact Hr.
      - intros (W' & Hnu & Hnd & Hocc & Hall & Hord). exists (map (op_unresig si) W').
        split; [| split; [| split; [| split]]].
        + exact Hnu.
        + rewrite map_map. exact Hnd.
        + intros o Ho. apply in_map_iff in Ho. destruct Ho as (o' & <- & Ho').
          apply occurs_resig. exact (Hocc o' Ho').
        + intros i k op Hi. destruct (Hall i k op (proj2 (inv_at_resig i k op) Hi)) as (o' & Ho' & Hk).
          exists (op_unresig si o'). split; [apply in_map; exact Ho' | exact Hk].
        + intros o1 o2 H1 H2 Hr. apply in_map_iff in H1, H2.
          destruct H1 as (o1' & <- & H1). destruct H2 as (o2' & <- & H2).
          apply before_map. apply Hord; [exact H1 | exact H2 |]. apply rhb_resig. exact Hr.
    Qed.
  End RelLinSel.

  (** L.8 target, for overlay traces: [rel_lin] of [map ev_resig s] is
      [rel_lin] of [s], with the same [indep]. *)
  Theorem rel_lin_resig {F : RelaxedSig.t} si (s : list (ThreadEvent F)) indep (nu : list (Op F) -> Prop) :
    rel_lin (@PrefixView.sel F) s indep nu <->
    rel_lin (@PrefixView.sel (resig F si)) (map (ev_resig si) s) indep (fun W => nu (map (op_unresig si) W)).
  Proof.
    pose proof (rel_lin_map (ev_resig si) (@PrefixView.sel (resig F si)) s indep (fun W => nu (map (op_unresig si) W))) as Hm.
    pose proof (rel_lin_resig_sel si (@PrefixView.sel F) s indep nu) as Hr.
    split; intros H.
    - apply (proj2 Hm). exact (proj1 Hr H).
    - apply (proj2 Hr). exact (proj1 Hm H).
  Qed.

  (** The sequential specification of an effect-at-invocation spec is
      the same predicate at both signatures. *)
  Lemma seq_run_resig {F : RelaxedSig.t} si {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) s0 W s1 :
    RelaxedHoareSpec.seq_run (F := F) δ s0 (map (op_unresig si) W) s1 <->
    RelaxedHoareSpec.seq_run (F := resig F si) δ s0 W s1.
  Proof.
    revert s0. induction W as [| o W IH]; intros s0; cbn [map]; split; intros H.
    - inversion H; subst. constructor.
    - inversion H; subst. constructor.
    - inversion H as [| s o0 s' W0 s2 Hd Hr]; subst.
      econstructor; [exact Hd | apply IH; exact Hr].
    - inversion H as [| s o0 s' W0 s2 Hd Hr]; subst.
      econstructor; [exact Hd | apply IH; exact Hr].
  Qed.

  Lemma seq_legal_resig {F : RelaxedSig.t} si {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) s0 W :
    RelaxedHoareSpec.seq_legal (F := F) δ s0 (map (op_unresig si) W) <->
    RelaxedHoareSpec.seq_legal (F := resig F si) δ s0 W.
  Proof.
    split; intros (s1 & H); exists s1; [apply (proj1 (seq_run_resig si δ s0 W s1)) | apply (proj2 (seq_run_resig si δ s0 W s1))];
      exact H.
  Qed.

  Corollary rel_lin_resig_seq {F : RelaxedSig.t} si {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) s0 (s : list (ThreadEvent F)) indep :
    rel_lin (@PrefixView.sel F) s indep (RelaxedHoareSpec.seq_legal (F := F) δ s0) <->
    rel_lin (@PrefixView.sel (resig F si)) (map (ev_resig si) s) indep (RelaxedHoareSpec.seq_legal (F := resig F si) δ s0).
  Proof.
    pose proof (rel_lin_resig si s indep (RelaxedHoareSpec.seq_legal (F := F) δ s0)) as H1.
    pose proof (rel_lin_nu_iff (@PrefixView.sel (resig F si)) (map (ev_resig si) s) indep
                  (fun W => RelaxedHoareSpec.seq_legal (F := F) δ s0 (map (op_unresig si) W))
                  (RelaxedHoareSpec.seq_legal (F := resig F si) δ s0) (seq_legal_resig si δ s0)) as H2.
    split; intros H.
    - exact (proj1 H2 (proj1 H1 H)).
    - exact (proj2 H1 (proj2 H2 H)).
  Qed.

  Lemma inv_at_map_resig {F : RelaxedSig.t} si (s : list (ThreadEvent F)) i (k : CallKey F) op :
    inv_at (@PrefixView.sel (resig F si)) (map (ev_resig si) s) i k op <-> inv_at (@PrefixView.sel F) s i k op.
  Proof.
    pose proof (inv_at_map (ev_resig si) (@PrefixView.sel (resig F si)) s i k op) as Hm.
    pose proof (inv_at_resig si (@PrefixView.sel F) s i k op) as Hr.
    split; intros H; [exact (proj1 Hr (proj1 Hm H)) | exact (proj2 Hm (proj2 Hr H))].
  Qed.

  Lemma res_at_map_resig {F : RelaxedSig.t} si (s : list (ThreadEvent F)) j (k : CallKey F) op (r : Sig.ar op) :
    res_at (@PrefixView.sel (resig F si)) (map (ev_resig si) s) j k op r <-> res_at (@PrefixView.sel F) s j k op r.
  Proof.
    pose proof (res_at_map (ev_resig si) (@PrefixView.sel (resig F si)) s j k op r) as Hm.
    pose proof (res_at_resig si (@PrefixView.sel F) s j k op r) as Hr.
    split; intros H; [exact (proj1 Hr (proj1 Hm H)) | exact (proj2 Hm (proj2 Hr H))].
  Qed.

  (** Completeness of a trace is invariant too. *)
  Lemma complete_resig {F : RelaxedSig.t} si (s : list (ThreadEvent F)) :
    PrefixView.complete s <-> PrefixView.complete (map (ev_resig si) s).
  Proof.
    split; intros Hc i k op Hi.
    - destruct (Hc i k op (proj1 (inv_at_map_resig si s i k op) Hi)) as (j & r & Hj).
      exists j, r. exact (proj2 (res_at_map_resig si s j k op r) Hj).
    - destruct (Hc i k op (proj2 (inv_at_map_resig si s i k op) Hi)) as (j & r & Hj).
      exists j, r. exact (proj1 (res_at_map_resig si s j k op r) Hj).
  Qed.

  (** Trace-level results transfer between overlay relations: if every
      complete overlay trace of [M] is relaxed-linearizable under [indep],
      so is every complete overlay trace of its re-typed copy [M'] (same
      bodies, overlay relation [si]), under the same [indep].  The RLHL
      judgement itself does not transfer (the abstract possibility
      semantics reads the overlay relation; see the header). *)
  Corollary mtraces_rel_lin_resig {E F : RelaxedSig.t} si (VE : LTS E) (M : RelaxedModuleImpl E F)
      (M' : RelaxedModuleImpl E (resig F si)) (HM : forall op t, M' op t = M op t) σ0 indep (nu : list (Op F) -> Prop) :
    (forall s, MTraces VE M σ0 s -> PrefixView.complete s -> rel_lin (@PrefixView.sel F) s indep nu) ->
    forall s', MTraces VE M' σ0 s' -> PrefixView.complete s' ->
      rel_lin (@PrefixView.sel (resig F si)) s' indep (fun W => nu (map (op_unresig si) W)).
  Proof.
    intros Hall s' Hs' Hc'.
    rewrite <- (map_ev_resig_unresig si s') in Hc' |- *.
    apply (proj1 (rel_lin_resig si _ indep nu)). apply Hall.
    - exact (mtraces_unresig si VE M M' HM σ0 s' Hs').
    - exact (proj2 (complete_resig si _) Hc').
  Qed.

  Corollary mtraces_rel_lin_seq_resig {E F : RelaxedSig.t} si (VE : LTS E) (M : RelaxedModuleImpl E F)
      (M' : RelaxedModuleImpl E (resig F si)) (HM : forall op t, M' op t = M op t) σ0 indep {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) s0 :
    (forall s, MTraces VE M σ0 s -> PrefixView.complete s ->
       rel_lin (@PrefixView.sel F) s indep (RelaxedHoareSpec.seq_legal (F := F) δ s0)) ->
    forall s', MTraces VE M' σ0 s' -> PrefixView.complete s' ->
      rel_lin (@PrefixView.sel (resig F si)) s' indep (RelaxedHoareSpec.seq_legal (F := resig F si) δ s0).
  Proof.
    intros Hall s' Hs' Hc'.
    rewrite <- (map_ev_resig_unresig si s') in Hc' |- *.
    apply (proj1 (rel_lin_resig_seq si δ s0 _ indep)). apply Hall.
    - exact (mtraces_unresig si VE M M' HM σ0 s' Hs').
    - exact (proj2 (complete_resig si _) Hc').
  Qed.

  (** ** Part 6: test instance, Counter_xy ([RelaxedHoareCounterXY])

      [FC = CxySig by_counter] and [F0 = CxySig ∅] are re-signatures of
      each other by conversion, and so are [CxySig si] and [CxySig si']
      for all [si], [si']; the transported traces are the original
      [sb_trace]/[lb_trace] by conversion. *)
  Module CounterXYResig.
    Import RelaxedHoareCounterXY.
    Import RelaxedHoareCompLinSpec.
    Import RelaxedHoareBase.
    Import RelaxedHoareInherit.

    Local Abbreviation empty := (fun _ _ : COp => False).
    Local Abbreviation V := (@RelaxedHoareSpec.EI EM MSt δmem).
    Local Abbreviation Vb := (@RelaxedHoareSpec.EI EMb MSt δmem).

    Lemma F0_is_resig : resig FC empty = F0.
    Proof. reflexivity. Qed.

    Lemma FC_is_resig : resig F0 by_counter = FC.
    Proof. reflexivity. Qed.

    Lemma sb_trace_resig si si' : map (ev_resig (F := CxySig si) si') (sb_trace si) = sb_trace si'.
    Proof. reflexivity. Qed.

    Lemma lb_trace_resig si si' : map (ev_resig (F := CxySig si) si') (lb_trace si) = lb_trace si'.
    Proof. reflexivity. Qed.

    (** (1) Positive transport ([mtraces_resig_iff], left to right):
        the SB trace of [M_cxy] (overlay [FC]) gives the SB trace of
        [M_cxy0] (overlay [F0]).  This re-derives
        [sb_mtraces (fun _ _ => False)], which [RelaxedHoareCounterXY]
        proves by a second, separate execution proof. *)
    Theorem sb_mtraces0_by_resig : MTraces V M_cxy0 (s00, []) (sb_trace empty).
    Proof.
      rewrite <- (sb_trace_resig by_counter empty).
      exact (proj1 (mtraces_resig_iff (F := FC) empty V M_cxy M_cxy0 (fun _ _ => eq_refl) (s00, []) (sb_trace by_counter))
               (sb_mtraces by_counter)).
    Qed.

    (** (2) Negative transport ([mtraces_resig_iff], right to left), a
        new fact: the load-buffering trace is a trace of the module
        [Mgen si_mb si] (underlay relation [si_mb]) for *no* overlay
        relation [si].  [RelaxedHoareCounterXY.lb_not_trace_b] proves it
        only at [si := si_cb], through [cxyb_rel_lin]. *)
    Theorem lb_not_trace_mgen si : ~ MTraces Vb (Mgen si_mb si) (s00, []) (lb_trace si).
    Proof.
      intros H. apply lb_not_trace_b. rewrite <- (lb_trace_resig si si_cb).
      exact (proj1 (mtraces_resig_iff (F := CxySig si) si_cb Vb (Mgen si_mb si) Mb (fun _ _ => eq_refl) (s00, [])
                      (lb_trace si)) H).
    Qed.

    (** (3) The pattern of the planned LatchSet datum [lbw] (plan §2.6,
        RD-4), on Counter_xy: the module [Mgen si_mb by_counter] is
        verified with the exported relation [by_counter]
        ([cxybcnt_rlhl2]); that contract admits the load-buffering trace
        ([lb_rel_lin_direct]); the module does not exhibit it (2). *)
    Corollary lb_admitted_not_exhibited :
      RLHL2Hyps (@Iren EMb FC MSt MSt δmem δcxy (fun s => s) RelaxedHoareCounterXY.ρ (fun _ => true))
        (@Rren EMb FC MSt MSt δmem δcxy) (@Gren EMb FC MSt MSt δmem δcxy) (Mgen si_mb by_counter) cxyb_σ0 cxy_v0 /\
      rel_lin (@PrefixView.sel FC) (lb_trace by_counter) by_counter (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00) /\
      ~ MTraces Vb (Mgen si_mb by_counter) (s00, []) (lb_trace by_counter).
    Proof. exact (conj cxybcnt_rlhl2 (conj lb_rel_lin_direct (lb_not_trace_mgen by_counter))). Qed.

    (** (4) [rel_lin_resig_seq], both directions, re-deriving known facts
        at [F0] from the [FC] versions: the SB trace is
        relaxed-linearizable under [by_counter] ([sb_rel_lin_gen] at
        [si := ∅]) and not under ∅ ([sb_not_rel_lin0] at [si := ∅]). *)
    Corollary sb_rel_lin0_by_resig :
      rel_lin (@PrefixView.sel F0) (sb_trace empty) by_counter (@RelaxedHoareSpec.seq_legal F0 MSt δcxy s00).
    Proof.
      rewrite <- (sb_trace_resig by_counter empty).
      exact (proj1 (rel_lin_resig_seq (F := FC) empty δcxy s00 (sb_trace by_counter) by_counter) sb_rel_lin_direct).
    Qed.

    Corollary sb_not_rel_lin0_by_resig :
      ~ rel_lin (@PrefixView.sel F0) (sb_trace empty) empty (@RelaxedHoareSpec.seq_legal F0 MSt δcxy s00).
    Proof.
      intros H. apply (sb_not_rel_lin0 by_counter).
      apply (proj2 (rel_lin_resig_seq (F := FC) empty δcxy s00 (sb_trace by_counter) empty)).
      exact H.
    Qed.

    (** (4') [mtraces_rel_lin_seq_resig] on the module [M_cxy0]
        (overlay [F0]): every complete trace of it is relaxed-linearizable
        under [by_counter], from [cxy_rel_lin] (overlay [FC]).  So
        [cxy0_no_rlhl2] (no [RLHL2Hyps] at [F0]) is a failure of the
        contract ∅ that [F0] exports, not of the bodies. *)
    Corollary cxy0_rel_lin_by_counter s :
      MTraces V M_cxy0 (s00, []) s -> PrefixView.complete s ->
      rel_lin (@PrefixView.sel F0) s by_counter (@RelaxedHoareSpec.seq_legal F0 MSt δcxy s00).
    Proof.
      exact (mtraces_rel_lin_seq_resig (F := FC) empty V M_cxy M_cxy0 (fun _ _ => eq_refl) (s00, []) by_counter
               δcxy s00 cxy_rel_lin s).
    Qed.

    (** (5) Scope of the transport: it is about the *overlay* signature
        of a module.  The copy-cat [idF : RelaxedModuleImpl F F] has [F]
        as its underlay too, where the frontier reads the relation
        ([must_precede], (F2)).  So the copy-cat's traces [RTraces] (and
        [RCompLin]) are not invariant under re-signature: the SB trace is
        a copy-cat trace of [EI δcxy] at [FC] (through [cxy_complin_ei])
        but not at [F0] (through [cc_rel_lin] and [sb_not_rel_lin0]). *)
    Theorem rtraces_not_resig_invariant :
      RTraces (@RelaxedHoareSpec.EI FC MSt δcxy) (s00, []) (sb_trace by_counter) /\
      ~ RTraces (@RelaxedHoareSpec.EI F0 MSt δcxy) (s00, []) (sb_trace empty).
    Proof.
      split.
      - exact (cxy_complin_ei _ (sb_mtraces by_counter)).
      - intros H. exact (sb_not_rel_lin0 empty (cc_rel_lin (F := F0) δcxy s00 _ H (sb_complete empty))).
    Qed.
  End CounterXYResig.

End RelaxedHoareResig.
