(** * ARMBar: an ARMv8 check for the buffered-cell redesign (task G-3)

    Task G-3 of the buffered-cell redesign of the SeqLock running example
    (.rocq-review/buffered-cell-plan.md, Phase 6; moved before F-2 by the
    author).  Report only: nothing else depends on this file.  It
    - extends a copy of the axiomatic ARMv8 model of memory/ARM.v with the
      fences DMB SY, DMB LD, DMB ST, with single-copy-atomic RMWs (SWP and
      LDADD with the A, L and AL flavours) and with LDAR/STLR (Parts 1-3);
    - proves litmus verdicts in that model, each as a named theorem
      (Part 6);
    - checks the cell-level counterpart of the RSW verdict in the buffered
      memory of memory/TableBarrier.v (Part 7).
    memory/ARM.v, memory/Litmus.v and every other file are unchanged.  This
    file imports only memory/ (and, through it, models/RelaxedSignature.v).

    What the verdicts are relative to.  Every verdict is a theorem about
    the model defined here, which is this file's reading of aarch64.cat
    (herdtools7).  The model has not been validated against herd7, which is
    not installed on the machine where this file was written.  The herd7
    tests for the author are in memory/herd/ (README.md there).  Nothing
    here is a claim about ARMv8 hardware.

    The model (Part 3).  Events are reads (acquire bit [A]: LDAR, or the
    read of SWPA/SWPAL/LDADDA/LDADDAL), writes (release bit [L]: STLR, or
    the write of SWPL/SWPAL/LDADDL/LDADDAL) and fences.  An RMW is a read
    and a write of one instruction, paired by [rmw]; the two are not
    [po]-related.  Initial writes are implicit, as in memory/Declarative.v.
    Clauses, as read from aarch64.cat:
<<
    obs = rfe | fre | coe
    dob = addr | data | ctrl; [W] | addr; po; [W] | (addr | data); rfi
          [| (ctrl | data); coi                  POPL18 only]
    aob = rmw | [range(rmw)]; rfi; [A]
    bob = po; [dmb.full]; po | po; ([A]; amo; [L]); po | [L]; po; [A]
        | [R]; po; [dmb.ld]; po | [A]; po | [W]; po; [dmb.st]; po; [W]
        | po; [L]
          [| po; [L]; coi                        POPL18 only]
    lws = po-loc; [W]                            Cur and CurSI only
    ob  = (obs | dob | aob | bob | lws [| si-edges, CurSI only])+
    internal: acyclic (po-loc | fr | co | rf)
    external: irreflexive ob
    atomic:   empty rmw & (fre; coe)
>>
    Omitted, because no test uses them: the ISB clause of [dob], pick
    dependencies, LDAPR ([Q]), load/store exclusives (LDXR/STXR), DSB
    (as read here, aarch64.cat treats DSB like DMB), shareability domains,
    mixed-size accesses, tags.

    Three variants ([variant]).
    - [POPL18]: the shape of memory/ARM.v, which as read here is the model
      of Pulte et al. (POPL 2018): [(ctrl | data); coi] and
      [po; [L]; coi], no [lws].  The name refers to those clauses only:
      this variant also has this file's fence and RMW clauses, including
      the AL clause, which postdates POPL 2018.  Read it as "ARM.v's shape,
      extended", not as the POPL 2018 model itself.
    - [Cur]: the current herdtools7 aarch64.cat as read here: [lws] in
      [lob], no [coi] clauses (they are subsumed by [lws]), and [si] (same
      instruction) the identity on these tests.
    - [CurSI]: hypothetical.  [Cur], plus [si] relating the write of an
      RMW to its read, so that [obs; si] and [lws; si] continue from an
      RMW's write to its read.  It exists to bracket flag F2.

    Flags (clauses this file is unsure of).
    - F1, the AL clause [po; ([A]; amo; [L]); po].  Read here as relating
      accesses strictly before an AL atomic to accesses strictly after it,
      so it does not order the atomic's own write before later accesses.
      This is the literal reading of the clause (strict [po] on both
      sides), and the G-3.1 review agrees with it.  F1 is therefore not
      the open question; F2 is.
    - F2, [si] and RMWs.  It is not settled here whether aarch64.cat's
      [si] relates the read and the write of an RMW.  [Cur] assumes not,
      [CurSI] assumes it does.  Three outcomes flip between the two
      ([vw_acq_flip], [vw_data_flip], [vw_seqlock_acq_flip]); all other
      verdicts hold in all three variants.  If herd7 shows CurSI-like
      behaviour, VW+ldadda and VW+ldaddal are Forbidden (as the G-3.1
      reviewer predicts for VW+ldaddal); under Cur they are Allowed.
    - F3, [lws] against the [coi] clauses.  No verdict here depends on it.

    Locations.  Five: x, y, z, s (the version word [own]) and [ln] (the
    TicketLock's [nxt]); [ln] was added in G-3.2 and only [MPObj] uses it.

    Results.  "Forbidden" theorems quantify over every well-formed witness.
    Where a theorem has parameters, it also quantifies over the values the
    outcome leaves open (RMW flavours, values read or written by RMWs and
    by get_ticket/test_ticket) and, for [RSWObj] and [RSWObjCore], over
    every dependency relation.  Non-vacuity (some well-formed witness
    satisfies INTERNAL and ATOMIC, so EXTERNAL alone excludes the outcome)
    is proved for the main forbidden outcomes: [rsw_obj_only_external_fails],
    [RSWObjCore.rsw_obj_core_not_vacuous], [mp_only_external_fails],
    [ac_only_external_fails], [sb_relacq_only_external_fails],
    [VW.vw_dmbst_only_external_fails],
    [VW.vw_seqlock_dmbst_only_external_fails], and the [_flip] corollaries.
    The remaining forbidden outcomes differ from one of these by a barrier
    or an annotation; their non-vacuity is not stated.  The [nonvacuous]
    lemmas (G-3.2, finding m-42) add [wf_cand] to these and cover the
    G-3.2 outcomes ([rt_get_dmbld_nonvacuous], [mp_obj_nonvacuous],
    [mp_obj_prologue_stale_get_nonvacuous]).
    - Sanity (module [Sanity]).  MP and LB allowed; MP+dmb.st+ctrl and
      SB+dmb.ld allowed; MP+dmb.st+addr, SB+dmb.sy, LB+data, IRIW+dmb.ld
      and CoRR forbidden.  These are the standard ARMv8 verdicts; they test
      this file's reading, they do not validate it.
    - Cross-checks with memory/Litmus.v ([CrossCheck]).  Litmus.RSW (Δ2,
      Mem.tex Ex. mem:ex:rsw) is allowed ([rsw_allowed]) and Litmus.SB with
      release/acquire (Δ1) is forbidden ([sb_relacq_forbidden]), as in
      ARM.v ([RSW.arm_allow], [SB.arm_forbid]), in all three variants.  No
      general theorem relates this model to ARM.v.
    - G-3 (c), RSW through the object ([RSWObj], [RSWObjCore]).  Under the
      SeqLock mapping (rmb = DMB LD, wmb = DMB ST, acq/rel = SWP or LDADD of
      any flavour, get_ticket/test_ticket = LDR), the outcome
      T1: zr()=1; zw(2); zr()=2; read()=(0,_) ‖ T2: write(1,1); zw(1)
      is forbidden ([rsw_obj_forbidden]).  The cycle is
      W x 1 →bob(DMB ST) W z 1 →rfe R z = 1 →bob(DMB LD) R x = 0 →fre W x 1.
      It does not use the same-location chain zr()=1, zw(2), zr()=2: DMB LD
      orders every earlier read.  Positive control: the same program with
      read() = (1,1) (relaxed RMWs, s read as 2) is allowed
      ([rsw_obj_control_allowed]).  The minimal
      core is forbidden as well ([rsw_obj_core_forbidden]).  If instead
      the order were carried by an acquire on the last read of z (LDAR, no
      DMB LD), the core would be allowed ([rsw_obj_core_ldar_allowed]):
      that is the Δ2 shape of Litmus.RSW.  Part 7: the redesign's
      cell-level specification forbids the core too
      ([CellTab.rsw_obj_core_tab_forbidden]).  Both forbid the core, so this
      shape shows no gap between that specification and the model.
    - G-3 (a), (b), SeqLockZ+rfi (the Q6 outcome) ([SeqLockZ]).  The
      minimal core ([core_allowed]) and the full test of the plan, for
      every flavour of acq and rel ([full_allowed]), are allowed.  Reviewer
      A's SB+rfi is allowed, plain and with DMB LD between the reads
      ([SBrfi]).  MP+dmb.st+dmb.ld is forbidden ([MPBar]).
    - G-3 (d), the atomic clause of the planned hybrid specification
      ([AtomicClause]).  W x 1; DMB ST; RMW s ‖ get s = 1; DMB LD; R x = 0
      is forbidden for every RMW flavour, relaxed LDADD included, with a
      plain LDR get ([ac_ldadd_ldr_forbidden]), and with an RMW observer
      ([ac_rmw_observer_forbidden]).  Without the DMB ST it is allowed for
      a relaxed or acquire RMW ([ac_nodmbst_allowed]; dto(DW, DRMW) =
      false) and forbidden for a release RMW ([ac_nodmbst_rel_forbidden]).
      Without the DMB LD it is allowed with LDR ([ac_ldr_nodmbld_allowed])
      and forbidden with LDAR ([ac_ldar_nodmbld_forbidden]).
    - G-3 item 3, the version word ([VW]).  RMW s 0 -> 1; STR z 1 ‖
      R z = 1; DMB LD; R s = 0: the RMW's write is not yet visible to a
      thread that has seen a later write of the same thread.
      Allowed for SWP/SWPL/LDADD/LDADDL in all variants, and for the
      acquire flavours in POPL18 and Cur ([vw_allowed]).  With the store
      of z data-dependent on the RMW's result: allowed in POPL18 and Cur
      ([vw_data_allowed]), forbidden in CurSI ([vw_data_si_forbidden]).
      A DMB ST or DMB SY after the RMW, or STLR for z, forbids it for every
      flavour ([vw_dmbst_forbidden], [vw_dmbsy_forbidden],
      [vw_stlr_forbidden]).  SeqLock variant: write(1,1) (acq; DMB ST;
      x; y; DMB ST; rel); zw(1) ‖ zr() = 1; DMB LD; get_ticket = 1 (the
      odd value): allowed for every flavour in POPL18 and Cur, and for a
      rel without acquire bit in CurSI ([vw_seqlock_allowed]); forbidden
      with a DMB ST between rel and zw ([vw_seqlock_dmbst_forbidden]).
      How much of this matters for the hybrid underlay Hν (finding M-16;
      a module-trace argument, not a theorem): a VW outcome refutes an
      atomic TicketLock only if the module semantics orders the later
      store's invocation after the RMW's response, that is, a Wait on the
      RMW or a data dependency on its result ([must_precede], F3).
      Otherwise the later store may be invoked before the RMW responds
      (Rel and WrZ are semi-independent, dto(DRMW, DW) = false), and a Hν
      witness can place Rel after the observer's get_ticket.  In the
      SeqLock as coded (SeqLockProg.write) the only such Wait is [Wait fa]
      on acq, and the DMB ST that follows already orders acq's write before
      every later store.  So VW-SeqLock does not by itself refute the
      atomic TicketLock.  The genuine writer-side violation is VW+data
      under Cur ([vw_data_allowed]): F3 forces the dependent store after
      the RMW's response, and the store becomes visible first.  A
      publication point for RMWs (option R1 of the G-3.1 report) may
      therefore be unnecessary for the SeqLock.
    - G-3.2, the reader side (finding M-15; [RTGet], [MPObj]).  A client
      [while (zr() != 1) {}; read()] waits on zr, so the module semantics
      invokes get_ticket after zr's response.  ARMv8 does not order the two
      loads: after zr() = 1, get_ticket can return the value from before
      acq, with an LDR get ([rt_get_ldr_allowed]), an LDAR get
      ([rt_get_ldar_allowed]) or a control dependency without ISB
      ([rt_get_ctrl_allowed]); a DMB LD between them forbids it
      ([rt_get_dmbld_forbidden]).  ctrl+ISB is not modelled (this model
      has no ISB); by aarch64.cat's ISB clause it would be forbidden
      (derivation).  In a full run with the TicketLock inlined (LDADD nxt,
      spin, LDADD own; ...; LDADD own; STR z), the stale get_ticket is
      allowed and the read retries ([mp_obj_stale_get_allowed]).  The
      client-visible outcome is not affected: read() cannot return x = 0
      after zr() = 1, with or without a prologue, for every flavour and
      value ([mp_obj_forbidden]), because the DMB LD after get_ticket also
      orders the z load.  A DMB LD at the start of read() removes the stale
      get_ticket ([mp_obj_prologue_stale_get_forbidden]).
      Derivation (not kernel-checked; F-2 is to check it once Hν exists):
      the hybrid underlay Hν rejects the underlay trace of that run.  In
      any Hν witness, Acq < wmb1 (dto(DRMW, Wmb) = true), wmb1 < wmb2 <
      WrZ (dto(Wmb, Wmb), dto(Wmb, DW)), WrZ is published before RdZ = 1
      (the only write of 1 to z), and RdZ < GT by real time (the client's
      Wait).  So Acq < GT, and the atomic TicketLock answers GT ≥ 1;
      GT = 0 has no witness.  This is a failure of the underlay
      hypothesis on a correct SeqLock run, as for the registers x and y in
      Q6-2, not a client-visible violation.

    What this file does not give.
    - No validation against herd7 and no soundness claim for ARMv8.
    - Known gap (finding M-15): the hybrid underlay Hν is not sound for
      ARMv8 executions of clients that wait on a load before calling
      read(), unless such Waits compile to a barrier (DMB LD, or ctrl+ISB)
      before get_ticket.  The tests above show the hardware side; the Hν
      side is the derivation above.  Whether ARMv8 is claimed (x86 only,
      or ARMv8 under a stated compilation scheme for Waits) is the
      author's decision.
    - No theorem that ARMBar restricted to the common fragment equals
      memory/ARM.v (only the two cross-checks).
    - No link from ARMBar executions to [V_{I_tab}] or to rel_lin (that is
      the declarative route of task G-1; it still needs the "mo at the
      shared Bw adds no constraint" lemma, m-35, and a "ghost dmb ↦ ghost
      access" candidate lemma).
    - No operational model, hence nothing about when an operation responds.
      The version-word tests are axiomatic proxies for the question of
      task G-3 item 3; how they bear on response times is an argument, not
      a theorem (see the G-3 report).

    Trusted computation.  "Allowed" theorems go through the boolean checker
    of Part 4 ([allowed_of_checkb], proved sound) and are closed by
    [exact eq_refl], i.e. by the kernel's conversion; there is no
    [vm_compute] or [native_compute].  Proofs by [lia] carry a VM cast, as
    elsewhere in the development.

    Assumptions.  The "forbidden" theorems whose cycle needs the source of
    a read use [classic] (a read with a nonzero value has a source,
    [read_source]); so do the [_flip] corollaries.
    [CellTab.rsw_obj_core_tab_forbidden] uses it through
    [TableBarrier.declarative_tab].  Every other result, including all
    "allowed" theorems, the [only_external_fails] lemmas,
    [CrossCheck.sb_relacq_forbidden] and [Sanity.sb_dmbsy_forbidden], is
    closed under the global context. *)

From Stdlib Require Import List Arith Bool micromega.Lia.
From Stdlib Require Import Relations.Relation_Definitions Relations.Relation_Operators.
From Stdlib Require Import Logic.Classical.
From Stdlib Require Import PArith.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.TableBarrier.

Import ListNotations.

Module ARMBar.

  (** ** Part 1. Events

      Five locations suffice for every test here.  An event is a read
      (with its acquire bit [A]), a write (with its release bit [L]) or a
      fence, with a thread and an instruction index.  The read and the
      write of one RMW instruction share thread and index. *)

  (** [ln] (the TicketLock's [nxt]) was added in G-3.2 for [MPObj]; no
      earlier test uses it. *)
  Inductive loc : Type := lx | ly | lz | ls | ln.

  Definition loc_eqb (a b : loc) : bool :=
    match a, b with
    | lx, lx | ly, ly | lz, lz | ls, ls | ln, ln => true
    | _, _ => false
    end.

  Lemma loc_eqb_spec a b : loc_eqb a b = true <-> a = b.
  Proof. destruct a, b; cbn; split; intros H; congruence. Qed.

  Inductive fence : Type := FSY | FLD | FST.

  Definition fence_eqb (a b : fence) : bool :=
    match a, b with FSY, FSY | FLD, FLD | FST, FST => true | _, _ => false end.

  Lemma fence_eqb_spec a b : fence_eqb a b = true <-> a = b.
  Proof. destruct a, b; cbn; split; intros H; congruence. Qed.

  Inductive kind : Type :=
  | KR (x : loc) (v : nat) (acq : bool)
  | KW (x : loc) (v : nat) (rel : bool)
  | KF (f : fence).

  Record event : Type := Ev { tid : nat; ins : nat; knd : kind }.

  Definition kind_eqb (a b : kind) : bool :=
    match a, b with
    | KR x v q, KR x' v' q' => loc_eqb x x' && Nat.eqb v v' && Bool.eqb q q'
    | KW x v q, KW x' v' q' => loc_eqb x x' && Nat.eqb v v' && Bool.eqb q q'
    | KF f, KF f' => fence_eqb f f'
    | _, _ => false
    end.

  Lemma kind_eqb_spec a b : kind_eqb a b = true <-> a = b.
  Proof.
    destruct a as [x v q | x v q | f], b as [x' v' q' | x' v' q' | f']; cbn;
      split; intros H; try discriminate.
    - apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
      apply loc_eqb_spec in H1. apply Nat.eqb_eq in H2. apply eqb_prop in H3. congruence.
    - injection H as -> -> ->. rewrite (proj2 (loc_eqb_spec x' x') eq_refl), Nat.eqb_refl, eqb_reflx. reflexivity.
    - apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
      apply loc_eqb_spec in H1. apply Nat.eqb_eq in H2. apply eqb_prop in H3. congruence.
    - injection H as -> -> ->. rewrite (proj2 (loc_eqb_spec x' x') eq_refl), Nat.eqb_refl, eqb_reflx. reflexivity.
    - apply fence_eqb_spec in H. congruence.
    - injection H as ->. apply fence_eqb_spec. reflexivity.
  Qed.

  Definition ev_eqb (a b : event) : bool :=
    Nat.eqb (tid a) (tid b) && Nat.eqb (ins a) (ins b) && kind_eqb (knd a) (knd b).

  Lemma ev_eqb_spec a b : ev_eqb a b = true <-> a = b.
  Proof.
    destruct a as [t i k], b as [t' i' k']. unfold ev_eqb; cbn. split.
    - intros H. apply andb_true_iff in H as [H H3]. apply andb_true_iff in H as [H1 H2].
      apply Nat.eqb_eq in H1, H2. apply kind_eqb_spec in H3. congruence.
    - intros H. injection H as -> -> ->. rewrite !Nat.eqb_refl. apply kind_eqb_spec. reflexivity.
  Qed.

  Definition isR (e : event) : bool := match knd e with KR _ _ _ => true | _ => false end.
  Definition isW (e : event) : bool := match knd e with KW _ _ _ => true | _ => false end.
  (** [A]: a read with acquire semantics (LDAR, or the read of SWPA/SWPAL,
      LDADDA/LDADDAL). *)
  Definition isA (e : event) : bool := match knd e with KR _ _ q => q | _ => false end.
  (** [L]: a write with release semantics (STLR, or the write of SWPL/SWPAL,
      LDADDL/LDADDAL). *)
  Definition isL (e : event) : bool := match knd e with KW _ _ q => q | _ => false end.
  Definition isF (k : fence) (e : event) : bool :=
    match knd e with KF f => fence_eqb f k | _ => false end.
  Definition eloc (e : event) : option loc :=
    match knd e with KR x _ _ | KW x _ _ => Some x | KF _ => None end.
  Definition eval (e : event) : nat :=
    match knd e with KR _ v _ | KW _ v _ => v | KF _ => 0 end.
  Definition sloc (a b : event) : bool :=
    match eloc a, eloc b with Some x, Some y => loc_eqb x y | _, _ => false end.

  (** ** Part 2. Candidates and witnesses

      As in memory/Declarative.v: the initial writes are implicit (value
      0, [co]-first), [co] is a strict total order on the writes of each
      location, [rf] is functional and a read without source reads 0.
      Program order is the instruction order of a thread; the two events
      of an RMW are not [po]-related (in herd7 they are related by
      [iico]).  [rmw] pairs the read and the write of each RMW; the
      dependency relations [addr], [data], [ctrl] are data of the
      candidate. *)

  Record cand : Type := {
    evs : list event;
    rmw : list (event * event);
    addr : list (event * event);
    data : list (event * event);
    ctrl : list (event * event);
  }.

  Definition inp (l : list (event * event)) : relation event := fun a b => In (a, b) l.

  Definition po (X : cand) : relation event :=
    fun a b => In a (evs X) /\ In b (evs X) /\ tid a = tid b /\ ins a < ins b.

  Definition po_loc (X : cand) : relation event := fun a b => po X a b /\ sloc a b = true.

  Record wf_cand (X : cand) : Prop := {
    evs_nodup : NoDup (evs X);
    ins_unique : forall a b, In a (evs X) -> In b (evs X) -> tid a = tid b -> ins a = ins b ->
      a = b \/ inp (rmw X) a b \/ inp (rmw X) b a;
    rmw_wf : forall r u, inp (rmw X) r u ->
      In r (evs X) /\ In u (evs X) /\ isR r = true /\ isW u = true /\
      tid r = tid u /\ ins r = ins u /\ sloc r u = true;
    dep_wf : forall a b, inp (addr X) a b \/ inp (data X) a b \/ inp (ctrl X) a b ->
      isR a = true /\ po X a b;
    ctrl_po : forall a b c, inp (ctrl X) a b -> po X b c -> inp (ctrl X) a c;
  }.

  Record witness : Type := { co : relation event; rf : relation event }.

  Record wf_witness (X : cand) (w : witness) : Prop := {
    co_dom : forall a b, co w a b ->
      In a (evs X) /\ In b (evs X) /\ isW a = true /\ isW b = true /\ sloc a b = true;
    co_irrefl : forall a, ~ co w a a;
    co_trans : forall a b c, co w a b -> co w b c -> co w a c;
    co_total : forall a b, In a (evs X) -> In b (evs X) -> isW a = true -> isW b = true ->
      sloc a b = true -> a <> b -> co w a b \/ co w b a;
    rf_dom : forall u r, rf w u r ->
      In u (evs X) /\ In r (evs X) /\ isW u = true /\ isR r = true /\
      sloc u r = true /\ eval u = eval r;
    rf_func : forall u u' r, rf w u r -> rf w u' r -> u = u';
    rf_init : forall r, In r (evs X) -> isR r = true -> (forall u, ~ rf w u r) -> eval r = 0;
  }.

  Arguments evs_nodup {X}. Arguments ins_unique {X}. Arguments rmw_wf {X}.
  Arguments dep_wf {X}. Arguments ctrl_po {X}.
  Arguments co_dom {X w}. Arguments co_irrefl {X w}. Arguments co_trans {X w}.
  Arguments co_total {X w}. Arguments rf_dom {X w}. Arguments rf_func {X w}. Arguments rf_init {X w}.

  Definition fr (X : cand) (w : witness) : relation event :=
    fun r u => In r (evs X) /\ In u (evs X) /\ isR r = true /\ isW u = true /\
            sloc r u = true /\ (forall u0, rf w u0 r -> co w u0 u).

  (** ** Part 3. The axiomatic model

      Each definition below cites the clause of aarch64.cat it encodes,
      as this file reads it.  See the header for the three variants and
      for the clauses that are flagged as uncertain. *)

  (** [POPL18]: the shape of memory/ARM.v (dob has [(ctrl | data); coi],
      bob has [po; [L]; coi], no [lws]), extended with fences and RMWs.
      [Cur]: the current herdtools7 aarch64.cat as read here ([lws] in
      [lob], no [coi] clauses, [si] the identity on these tests).
      [CurSI]: hypothetical; [Cur] plus [si] relating the write of an RMW
      to its read (header, flag F2). *)
  Inductive variant : Type := POPL18 | Cur | CurSI.

  Definition is18 (v : variant) : bool := match v with POPL18 => true | _ => false end.
  Definition has_lws (v : variant) : bool := match v with POPL18 => false | _ => true end.
  Definition has_si (v : variant) : bool := match v with CurSI => true | _ => false end.

  (** [let obs = rfe | fre | coe] *)
  Definition obs (X : cand) (w : witness) : relation event :=
    fun a b => (rf w a b \/ fr X w a b \/ co w a b) /\ tid a <> tid b.

  (** [let dob = addr | data | ctrl; [W] | addr; po; [W] | (addr | data); rfi],
      and in [POPL18] also [(ctrl | data); coi].  The ISB clause
      [(ctrl | (addr; po)); [ISB]; po; [R]] is omitted: no test has an ISB.
      Pick dependencies are omitted. *)
  Definition dob (v : variant) (X : cand) (w : witness) : relation event :=
    fun a b =>
      inp (addr X) a b
      \/ inp (data X) a b
      \/ (inp (ctrl X) a b /\ isW b = true)
      \/ (exists c, inp (addr X) a c /\ po X c b /\ isW b = true)
      \/ (exists c, (inp (addr X) a c \/ inp (data X) a c) /\ rf w c b /\ tid c = tid b)
      \/ (is18 v = true /\ exists c, (inp (ctrl X) a c \/ inp (data X) a c) /\ co w c b /\ tid c = tid b).

  (** [let aob = rmw | [range(rmw)]; rfi; [A | Q]]; [Q] (LDAPR) is
      omitted. *)
  Definition aob (X : cand) (w : witness) : relation event :=
    fun a b =>
      inp (rmw X) a b
      \/ ((exists r0, inp (rmw X) r0 a) /\ rf w a b /\ tid a = tid b /\ isA b = true).

  Definition fenced (k : fence) (X : cand) : relation event :=
    fun a b => exists f, po X a f /\ isF k f = true /\ po X f b.

  (** [let bob = po; [dmb.full]; po            (DMB SY)
                | po; ([A]; amo; [L]); po    (an AL atomic; flag F1)
                | [L]; po; [A]
                | [R]; po; [dmb.ld]; po      (DMB LD)
                | [A | Q]; po
                | [W]; po; [dmb.st]; po; [W] (DMB ST)
                | po; [L]],
      and in [POPL18] also [po; [L]; coi]. *)
  Definition bob (v : variant) (X : cand) (w : witness) : relation event :=
    fun a b =>
      fenced FSY X a b
      \/ (exists r1 w1, po X a r1 /\ inp (rmw X) r1 w1 /\ isA r1 = true /\ isL w1 = true /\ po X w1 b)
      \/ (isL a = true /\ po X a b /\ isA b = true)
      \/ (isR a = true /\ fenced FLD X a b)
      \/ (isA a = true /\ po X a b)
      \/ (isW a = true /\ fenced FST X a b /\ isW b = true)
      \/ (po X a b /\ isL b = true)
      \/ (is18 v = true /\ exists c, po X a c /\ isL c = true /\ co w c b /\ tid c = tid b).

  (** [let lws = po-loc; [W]] (local write successor), in [Cur] and
      [CurSI]. *)
  Definition lws (v : variant) (X : cand) : relation event :=
    fun a b => has_lws v = true /\ po X a b /\ sloc a b = true /\ isW b = true.

  (** [obs; si] and [lws; si] beyond the identity, in [CurSI] only: an
      edge into the write of an RMW continues to its read. *)
  Definition sie (v : variant) (X : cand) (w : witness) : relation event :=
    fun a b => has_si v = true /\
      exists u, (obs X w a u \/ (po X a u /\ sloc a u = true /\ isW u = true)) /\ inp (rmw X) b u.

  Definition obgen (v : variant) (X : cand) (w : witness) : relation event :=
    fun a b => obs X w a b \/ dob v X w a b \/ aob X w a b \/ bob v X w a b \/ lws v X a b
               \/ sie v X w a b.

  (** [ob] is the transitive closure of the generators.  aarch64.cat
      writes it as [ob = (obs; si) | lob] with [lob] the closure of
      [lws; si | dob | aob | bob]; on these tests the two agree (with the
      [si] of the chosen variant). *)
  Definition ob (v : variant) (X : cand) (w : witness) : relation event := tc (obgen v X w).

  (** [acyclic po-loc | ca | rf as internal], with [ca = fr | co]. *)
  Definition internal (X : cand) (w : witness) : Prop :=
    acyclic (fun a b => po_loc X a b \/ fr X w a b \/ co w a b \/ rf w a b).

  (** [irreflexive ob as external], i.e. the generators are acyclic. *)
  Definition external (v : variant) (X : cand) (w : witness) : Prop := acyclic (obgen v X w).

  (** [empty rmw & (fre; coe) as atomic]. *)
  Definition atomic (X : cand) (w : witness) : Prop :=
    forall r u, inp (rmw X) r u ->
      ~ exists u', fr X w r u' /\ tid r <> tid u' /\ co w u' u /\ tid u' <> tid u.

  Definition consistent (v : variant) (X : cand) (w : witness) : Prop :=
    internal X w /\ external v X w /\ atomic X w.

  (** A litmus outcome is a candidate whose read events carry the values of
      the outcome.  [allowed]: the candidate is well formed and some
      well-formed witness is consistent.  [forbidden]: no well-formed
      witness is consistent. *)
  Definition allowed (v : variant) (X : cand) : Prop :=
    wf_cand X /\ exists w, wf_witness X w /\ consistent v X w.

  Definition forbidden (v : variant) (X : cand) : Prop :=
    forall w, wf_witness X w -> ~ consistent v X w.

  (** ** Part 4. A boolean checker for "allowed" *)

  Definition memb (e : event) (l : list event) : bool := existsb (ev_eqb e) l.

  Lemma memb_spec e l : memb e l = true <-> In e l.
  Proof.
    unfold memb. rewrite existsb_exists. split.
    - intros (x & Hx & Hq). apply ev_eqb_spec in Hq. subst. exact Hx.
    - intros H. exists e. split; [exact H | apply ev_eqb_spec; reflexivity].
  Qed.

  Definition inpb (l : list (event * event)) (a b : event) : bool :=
    existsb (fun p => ev_eqb (fst p) a && ev_eqb (snd p) b) l.

  Lemma inpb_spec l a b : inpb l a b = true <-> In (a, b) l.
  Proof.
    unfold inpb. rewrite existsb_exists. split.
    - intros ([x y] & Hx & Hq). apply andb_true_iff in Hq as [H1 H2].
      apply ev_eqb_spec in H1, H2. cbn in *. subst. exact Hx.
    - intros H. exists (a, b). split; [exact H |]. cbn.
      rewrite (proj2 (ev_eqb_spec a a) eq_refl), (proj2 (ev_eqb_spec b b) eq_refl). reflexivity.
  Qed.

  Definition pob (a b : event) : bool := Nat.eqb (tid a) (tid b) && Nat.ltb (ins a) (ins b).

  Lemma pob_of X a b : po X a b -> pob a b = true.
  Proof.
    intros (_ & _ & Ht & Hi). unfold pob. rewrite Ht, Nat.eqb_refl. apply Nat.ltb_lt. exact Hi.
  Qed.

  Definition extb (a b : event) : bool := negb (Nat.eqb (tid a) (tid b)).
  Definition intb (a b : event) : bool := Nat.eqb (tid a) (tid b).

  Lemma extb_of a b : tid a <> tid b -> extb a b = true.
  Proof. intros H. unfold extb. apply negb_true_iff, Nat.eqb_neq. exact H. Qed.

  Lemma intb_of a b : tid a = tid b -> intb a b = true.
  Proof. intros H. unfold intb. apply Nat.eqb_eq. exact H. Qed.

  Section Check.
    Variable v : variant.
    Variable X : cand.
    Variables co_l rf_l : list (event * event).

    Definition wit : witness := {| co := inp co_l; rf := inp rf_l |}.

    Definition frb (r u : event) : bool :=
      isR r && isW u && sloc r u &&
      forallb (fun p => implb (ev_eqb (snd p) r) (inpb co_l (fst p) u)) rf_l.

    Lemma frb_of r u : fr X wit r u -> frb r u = true.
    Proof.
      intros (_ & _ & Hr & Hu & Hl & Hs). unfold frb. rewrite Hr, Hu, Hl. cbn.
      apply forallb_forall. intros [u0 r0] Hin. cbn.
      destruct (ev_eqb r0 r) eqn:E; [| reflexivity]. cbn.
      apply ev_eqb_spec in E. subst r0. apply inpb_spec. apply Hs. exact Hin.
    Qed.

    Definition fencedb (k : fence) (a b : event) : bool :=
      existsb (fun f => pob a f && isF k f && pob f b) (evs X).

    Lemma fencedb_of k a b : fenced k X a b -> fencedb k a b = true.
    Proof.
      intros (f & H1 & Hf & H2). unfold fencedb. apply existsb_exists.
      exists f. split; [exact (proj1 H2) |].
      rewrite (pob_of _ _ _ H1), Hf, (pob_of _ _ _ H2). reflexivity.
    Qed.

    Definition obsb (a b : event) : bool :=
      (inpb rf_l a b || frb a b || inpb co_l a b) && extb a b.

    Definition dobb (a b : event) : bool :=
      inpb (addr X) a b
      || inpb (data X) a b
      || (inpb (ctrl X) a b && isW b)
      || (existsb (fun p => ev_eqb (fst p) a && pob (snd p) b) (addr X) && isW b)
      || existsb (fun p => ev_eqb (fst p) a && inpb rf_l (snd p) b && intb (snd p) b)
                 (addr X ++ data X)
      || (is18 v &&
          existsb (fun p => ev_eqb (fst p) a && inpb co_l (snd p) b && intb (snd p) b)
                  (ctrl X ++ data X)).

    Definition aobb (a b : event) : bool :=
      inpb (rmw X) a b
      || (existsb (fun p => ev_eqb (snd p) a) (rmw X) && inpb rf_l a b && intb a b && isA b).

    Definition bobb (a b : event) : bool :=
      fencedb FSY a b
      || existsb (fun p => pob a (fst p) && isA (fst p) && isL (snd p) && pob (snd p) b) (rmw X)
      || (isL a && pob a b && isA b)
      || (isR a && fencedb FLD a b)
      || (isA a && pob a b)
      || (isW a && fencedb FST a b && isW b)
      || (pob a b && isL b)
      || (is18 v &&
          existsb (fun p => pob a (fst p) && isL (fst p) && ev_eqb (snd p) b && intb (fst p) b) co_l).

    Definition lwsb (a b : event) : bool :=
      has_lws v && pob a b && sloc a b && isW b.

    Definition sieb (a b : event) : bool :=
      has_si v &&
      existsb (fun p => ev_eqb (fst p) b &&
                        (obsb a (snd p) || (pob a (snd p) && sloc a (snd p) && isW (snd p)))) (rmw X).

    Definition obgenb (a b : event) : bool :=
      obsb a b || dobb a b || aobb a b || bobb a b || lwsb a b || sieb a b.

    Ltac bt := repeat (first [ rewrite orb_true_iff | rewrite andb_true_iff ]).

    Lemma obgenb_of a b : obgen v X wit a b -> obgenb a b = true.
    Proof.
      unfold obgenb. intros H.
      destruct H as [Ho | [Hd | [Ha | [Hb | [Hl | Hs]]]]].
      - (* obs *)
        do 5 (apply orb_true_iff; left). destruct Ho as [Ho He]. unfold obsb. rewrite (extb_of _ _ He).
        rewrite andb_true_r. destruct Ho as [Hrf | [Hfr | Hco]].
        + apply orb_true_iff. left. apply orb_true_iff. left. apply inpb_spec. exact Hrf.
        + apply orb_true_iff. left. apply orb_true_iff. right. apply frb_of. exact Hfr.
        + apply orb_true_iff. right. apply inpb_spec. exact Hco.
      - (* dob *)
        do 4 (apply orb_true_iff; left). apply orb_true_iff; right. unfold dobb.
        destruct Hd as [H | [H | [[H Hw] | [(c & Hc & Hpo & Hw) | [(c & Hc & Hrf & Ht) | (Hv & c & Hc & Hco & Ht)]]]]].
        + do 5 (apply orb_true_iff; left). apply inpb_spec. exact H.
        + do 4 (apply orb_true_iff; left). apply orb_true_iff; right. apply inpb_spec. exact H.
        + do 3 (apply orb_true_iff; left). apply orb_true_iff; right.
          rewrite Hw, andb_true_r. apply inpb_spec. exact H.
        + do 2 (apply orb_true_iff; left). apply orb_true_iff; right. rewrite Hw, andb_true_r.
          apply existsb_exists. exists (a, c). split; [exact Hc |]. cbn.
          rewrite (proj2 (ev_eqb_spec a a) eq_refl), (pob_of _ _ _ Hpo). reflexivity.
        + apply orb_true_iff; left. apply orb_true_iff; right.
          apply existsb_exists. exists (a, c). split.
          * apply in_or_app. destruct Hc as [Hc | Hc]; [left | right]; exact Hc.
          * cbn. rewrite (proj2 (ev_eqb_spec a a) eq_refl), (intb_of _ _ Ht).
            rewrite (proj2 (inpb_spec rf_l c b) Hrf). reflexivity.
        + apply orb_true_iff; right. rewrite Hv. cbn.
          apply existsb_exists. exists (a, c). split.
          * apply in_or_app. destruct Hc as [Hc | Hc]; [left | right]; exact Hc.
          * cbn. rewrite (proj2 (ev_eqb_spec a a) eq_refl), (intb_of _ _ Ht).
            rewrite (proj2 (inpb_spec co_l c b) Hco). reflexivity.
      - (* aob *)
        do 3 (apply orb_true_iff; left). apply orb_true_iff; right. unfold aobb. destruct Ha as [H | ((r0 & Hr0) & Hrf & Ht & HA)].
        + apply orb_true_iff; left. apply inpb_spec. exact H.
        + apply orb_true_iff; right. rewrite HA, (intb_of _ _ Ht), (proj2 (inpb_spec rf_l a b) Hrf).
          rewrite !andb_true_r. apply existsb_exists. exists (r0, a). split; [exact Hr0 |].
          cbn. apply ev_eqb_spec. reflexivity.
      - (* bob *)
        do 2 (apply orb_true_iff; left). apply orb_true_iff; right. unfold bobb.
        destruct Hb as [H | [(r1 & w1 & H1 & Hm & HA & HL & H2) | [(HL & Hpo & HA) | [(HR & H) |
                       [(HA & Hpo) | [(HW & H & HW') | [(Hpo & HL) | (Hv & c & Hpo & HL & Hco & Ht)]]]]]]].
        + do 7 (apply orb_true_iff; left). apply fencedb_of. exact H.
        + do 6 (apply orb_true_iff; left). apply orb_true_iff; right.
          apply existsb_exists. exists (r1, w1). split; [exact Hm |]. cbn.
          rewrite (pob_of _ _ _ H1), HA, HL, (pob_of _ _ _ H2). reflexivity.
        + do 5 (apply orb_true_iff; left). apply orb_true_iff; right.
          rewrite HL, (pob_of _ _ _ Hpo), HA. reflexivity.
        + do 4 (apply orb_true_iff; left). apply orb_true_iff; right.
          rewrite HR, (fencedb_of _ _ _ H). reflexivity.
        + do 3 (apply orb_true_iff; left). apply orb_true_iff; right.
          rewrite HA, (pob_of _ _ _ Hpo). reflexivity.
        + do 2 (apply orb_true_iff; left). apply orb_true_iff; right.
          rewrite HW, (fencedb_of _ _ _ H), HW'. reflexivity.
        + apply orb_true_iff; left. apply orb_true_iff; right.
          rewrite (pob_of _ _ _ Hpo), HL. reflexivity.
        + apply orb_true_iff; right. rewrite Hv. cbn.
          apply existsb_exists. exists (c, b). split; [exact Hco |]. cbn.
          rewrite (pob_of _ _ _ Hpo), HL, (intb_of _ _ Ht), (proj2 (ev_eqb_spec b b) eq_refl).
          reflexivity.
      - (* lws *)
        apply orb_true_iff; left. apply orb_true_iff; right.
        destruct Hl as (Hv & Hpo & Hs & HW). unfold lwsb. rewrite Hv. cbn.
        rewrite (pob_of _ _ _ Hpo), Hs, HW. reflexivity.
      - (* si *)
        apply orb_true_iff; right. destruct Hs as (Hv & u & Hu & Hm). unfold sieb. rewrite Hv. cbn.
        apply existsb_exists. exists (b, u). split; [exact Hm |]. cbn.
        rewrite (proj2 (ev_eqb_spec b b) eq_refl). cbn.
        destruct Hu as [Ho | (Hpo & Hsl & HW)].
        + apply orb_true_iff. left. destruct Ho as [Ho He]. unfold obsb. rewrite (extb_of _ _ He).
          rewrite andb_true_r. destruct Ho as [Hrf | [Hfr | Hco]].
          * apply orb_true_iff. left. apply orb_true_iff. left. apply inpb_spec. exact Hrf.
          * apply orb_true_iff. left. apply orb_true_iff. right. apply frb_of. exact Hfr.
          * apply orb_true_iff. right. apply inpb_spec. exact Hco.
        + apply orb_true_iff. right. rewrite (pob_of _ _ _ Hpo), Hsl, HW. reflexivity.
    Qed.

    Definition intgenb (a b : event) : bool :=
      (pob a b && sloc a b) || frb a b || inpb co_l a b || inpb rf_l a b.

    Lemma intgenb_of a b :
      (po_loc X a b \/ fr X wit a b \/ co wit a b \/ rf wit a b) -> intgenb a b = true.
    Proof.
      unfold intgenb. intros [[Hpo Hs] | [Hfr | [Hco | Hrf]]].
      - do 3 (apply orb_true_iff; left). rewrite (pob_of _ _ _ Hpo), Hs. reflexivity.
      - do 2 (apply orb_true_iff; left). apply orb_true_iff; right. apply frb_of. exact Hfr.
      - apply orb_true_iff; left. apply orb_true_iff; right. apply inpb_spec. exact Hco.
      - apply orb_true_iff; right. apply inpb_spec. exact Hrf.
    Qed.

    Definition atomicb : bool :=
      forallb (fun p => negb (existsb (fun q => frb (fst p) (fst q) && extb (fst p) (fst q)
                                              && ev_eqb (snd q) (snd p) && extb (fst q) (snd p)) co_l))
              (rmw X).

    Lemma atomic_of_atomicb : atomicb = true -> atomic X wit.
    Proof.
      intros H r u Hru (u' & Hfr & He1 & Hco & He2).
      unfold atomicb in H. rewrite forallb_forall in H. specialize (H (r, u) Hru). cbn in H.
      apply negb_true_iff in H. rewrite <- not_true_iff_false in H. apply H.
      apply existsb_exists. exists (u', u). split; [exact Hco |]. cbn.
      rewrite (frb_of _ _ Hfr), (extb_of _ _ He1), (extb_of _ _ He2), (proj2 (ev_eqb_spec u u) eq_refl).
      reflexivity.
    Qed.

    Fixpoint nodupb (l : list event) : bool :=
      match l with [] => true | e :: t => negb (memb e t) && nodupb t end.

    Lemma nodupb_sound l : nodupb l = true -> NoDup l.
    Proof.
      induction l as [| e t IH]; cbn; intros H; [constructor |].
      apply andb_true_iff in H as [H1 H2]. constructor; [| apply IH, H2].
      intros Hin. apply memb_spec in Hin. rewrite Hin in H1. discriminate.
    Qed.

    Definition wfcb : bool :=
      nodupb (evs X)
      && forallb (fun a => forallb (fun b =>
           implb (Nat.eqb (tid a) (tid b) && Nat.eqb (ins a) (ins b))
                 (ev_eqb a b || inpb (rmw X) a b || inpb (rmw X) b a)) (evs X)) (evs X)
      && forallb (fun p => memb (fst p) (evs X) && memb (snd p) (evs X) && isR (fst p) && isW (snd p)
                          && Nat.eqb (tid (fst p)) (tid (snd p)) && Nat.eqb (ins (fst p)) (ins (snd p))
                          && sloc (fst p) (snd p)) (rmw X)
      && forallb (fun p => isR (fst p) && memb (fst p) (evs X) && memb (snd p) (evs X) && pob (fst p) (snd p))
                 (addr X ++ data X ++ ctrl X)
      && forallb (fun p => forallb (fun c => implb (pob (snd p) c) (inpb (ctrl X) (fst p) c)) (evs X))
                 (ctrl X).

    Lemma po_of_pob a b : In a (evs X) -> In b (evs X) -> pob a b = true -> po X a b.
    Proof.
      intros Ha Hb H. apply andb_true_iff in H as [H1 H2].
      apply Nat.eqb_eq in H1. apply Nat.ltb_lt in H2. repeat split; auto.
    Qed.

    Lemma wf_cand_of_wfcb : wfcb = true -> wf_cand X.
    Proof.
      unfold wfcb. intros H. repeat rewrite andb_true_iff in H.
      destruct H as [[[[H1 H2] H3] H4] H5].
      constructor.
      - apply nodupb_sound. exact H1.
      - intros a b Ha Hb Ht Hi. rewrite forallb_forall in H2. specialize (H2 a Ha).
        rewrite forallb_forall in H2. specialize (H2 b Hb). rewrite Ht, Hi, !Nat.eqb_refl in H2. cbn in H2.
        repeat rewrite orb_true_iff in H2. destruct H2 as [[H | H] | H].
        + left. apply ev_eqb_spec. exact H.
        + right; left. apply inpb_spec. exact H.
        + right; right. apply inpb_spec. exact H.
      - intros r u Hru. rewrite forallb_forall in H3. specialize (H3 (r, u) Hru). cbn in H3.
        repeat rewrite andb_true_iff in H3.
        destruct H3 as [[[[[[Hr Hu] HR] HW] Ht] Hi] Hs].
        apply memb_spec in Hr, Hu. apply Nat.eqb_eq in Ht, Hi. repeat split; auto.
      - intros a b Hab. rewrite forallb_forall in H4.
        assert (Hin : In (a, b) (addr X ++ data X ++ ctrl X)).
        { destruct Hab as [Hab | [Hab | Hab]]; apply in_or_app; [left | right; apply in_or_app; left
                                                                 | right; apply in_or_app; right]; exact Hab. }
        specialize (H4 _ Hin). cbn in H4. repeat rewrite andb_true_iff in H4.
        destruct H4 as [[[HR Ha] Hb] Hp]. apply memb_spec in Ha, Hb.
        split; [exact HR | apply po_of_pob; auto].
      - intros a b c Hab Hbc. rewrite forallb_forall in H5. specialize (H5 _ Hab). cbn in H5.
        rewrite forallb_forall in H5. specialize (H5 c (proj1 (proj2 Hbc))).
        rewrite (pob_of _ _ _ Hbc) in H5. cbn in H5. apply inpb_spec. exact H5.
    Qed.

    Definition wfwb : bool :=
      forallb (fun p => memb (fst p) (evs X) && memb (snd p) (evs X) && isW (fst p) && isW (snd p)
                        && sloc (fst p) (snd p) && negb (ev_eqb (fst p) (snd p))) co_l
      && forallb (fun p => forallb (fun q => implb (ev_eqb (snd p) (fst q)) (inpb co_l (fst p) (snd q))) co_l) co_l
      && forallb (fun a => forallb (fun b =>
           implb (isW a && isW b && sloc a b && negb (ev_eqb a b)) (inpb co_l a b || inpb co_l b a))
           (evs X)) (evs X)
      && forallb (fun p => memb (fst p) (evs X) && memb (snd p) (evs X) && isW (fst p) && isR (snd p)
                          && sloc (fst p) (snd p) && Nat.eqb (eval (fst p)) (eval (snd p))) rf_l
      && forallb (fun p => forallb (fun q => implb (ev_eqb (snd p) (snd q)) (ev_eqb (fst p) (fst q))) rf_l) rf_l
      && forallb (fun r => implb (isR r && negb (existsb (fun p => ev_eqb (snd p) r) rf_l))
                                 (Nat.eqb (eval r) 0)) (evs X).

    Lemma wf_witness_of_wfwb : wfwb = true -> wf_witness X wit.
    Proof.
      unfold wfwb. intros H. repeat rewrite andb_true_iff in H.
      destruct H as [[[[[H1 H2] H3] H4] H5] H6].
      rewrite forallb_forall in H1, H2, H3, H4, H5, H6.
      constructor; cbn.
      - intros a b Hab. specialize (H1 _ Hab). cbn in H1. repeat rewrite andb_true_iff in H1.
        destruct H1 as [[[[[Ha Hb] Hwa] Hwb] Hs] _]. apply memb_spec in Ha, Hb. repeat split; auto.
      - intros a Ha. specialize (H1 _ Ha). cbn in H1. repeat rewrite andb_true_iff in H1.
        destruct H1 as [_ Hne]. rewrite (proj2 (ev_eqb_spec a a) eq_refl) in Hne. discriminate.
      - intros a b c Hab Hbc. specialize (H2 _ Hab). rewrite forallb_forall in H2.
        specialize (H2 _ Hbc). cbn in H2. rewrite (proj2 (ev_eqb_spec b b) eq_refl) in H2.
        apply inpb_spec. exact H2.
      - intros a b Ha Hb Hwa Hwb Hs Hne. specialize (H3 _ Ha). rewrite forallb_forall in H3.
        specialize (H3 _ Hb). rewrite Hwa, Hwb, Hs in H3.
        destruct (ev_eqb a b) eqn:E; [apply ev_eqb_spec in E; contradiction |].
        cbn in H3. apply orb_true_iff in H3 as [H | H]; [left | right]; apply inpb_spec; exact H.
      - intros u r Hur. specialize (H4 _ Hur). cbn in H4. repeat rewrite andb_true_iff in H4.
        destruct H4 as [[[[[Hu Hr] Hwu] Hrr] Hs] Hv]. apply memb_spec in Hu, Hr.
        apply Nat.eqb_eq in Hv. repeat split; auto.
      - intros u u' r H H'. specialize (H5 _ H). rewrite forallb_forall in H5.
        specialize (H5 _ H'). cbn in H5. rewrite (proj2 (ev_eqb_spec r r) eq_refl) in H5.
        cbn in H5. apply ev_eqb_spec. exact H5.
      - intros r Hr HR Hno. specialize (H6 _ Hr). rewrite HR in H6.
        assert (Hn : existsb (fun p => ev_eqb (snd p) r) rf_l = false).
        { apply not_true_iff_false. intros Hex. apply existsb_exists in Hex as ([u r'] & Hin & Hq).
          cbn in Hq. apply ev_eqb_spec in Hq. subst r'. exact (Hno u Hin). }
        rewrite Hn in H6. cbn in H6. apply Nat.eqb_eq. exact H6.
    Qed.

    Fixpoint idx (e : event) (l : list event) : nat :=
      match l with [] => 0 | h :: t => if ev_eqb e h then 0 else S (idx e t) end.

    Definition acycb (Rb : event -> event -> bool) (ord : list event) : bool :=
      forallb (fun a => forallb (fun b => implb (Rb a b) (Nat.ltb (idx a ord) (idx b ord))) (evs X)) (evs X).

    Lemma acycb_sound (R : relation event) (Rb : event -> event -> bool) ord :
      (forall a b, R a b -> In a (evs X) /\ In b (evs X) /\ Rb a b = true) ->
      acycb Rb ord = true -> acyclic R.
    Proof.
      intros HR H. apply (acyclic_by_nat_potential (fun e => idx e ord)).
      intros a b Hab. destruct (HR a b Hab) as (Ha & Hb & Hr).
      unfold acycb in H. rewrite forallb_forall in H. specialize (H a Ha).
      rewrite forallb_forall in H. specialize (H b Hb). rewrite Hr in H. cbn in H.
      apply Nat.ltb_lt. exact H.
    Qed.

    (** Every generator edge of [ob] and of INTERNAL relates events of the
        candidate. *)
    Lemma obgen_in (HX : wf_cand X) (Hw : wf_witness X wit) a b :
      obgen v X wit a b -> In a (evs X) /\ In b (evs X).
    Proof.
      intros [Ho | [Hd | [Ha | [Hb | [Hl | Hs]]]]].
      - destruct Ho as [[H | [H | H]] _].
        + destruct (rf_dom Hw _ _ H) as (? & ? & _). auto.
        + destruct H as (? & ? & _). auto.
        + destruct (co_dom Hw _ _ H) as (? & ? & _). auto.
      - destruct Hd as [H | [H | [[H _] | [(c & Hc & Hpo & _) | [(c & Hc & Hrf & _) | (_ & c & Hc & Hco & _)]]]]].
        + destruct (dep_wf HX a b (or_introl H)) as [_ (? & ? & _)]. auto.
        + destruct (dep_wf HX a b (or_intror (or_introl H))) as [_ (? & ? & _)]. auto.
        + destruct (dep_wf HX a b (or_intror (or_intror H))) as [_ (? & ? & _)]. auto.
        + destruct (dep_wf HX a c (or_introl Hc)) as [_ (? & _)]. destruct Hpo as (_ & ? & _). auto.
        + split.
          * destruct Hc as [Hc | Hc].
            -- destruct (dep_wf HX a c (or_introl Hc)) as [_ (? & _)]. auto.
            -- destruct (dep_wf HX a c (or_intror (or_introl Hc))) as [_ (? & _)]. auto.
          * destruct (rf_dom Hw _ _ Hrf) as (_ & ? & _). auto.
        + split.
          * destruct Hc as [Hc | Hc].
            -- destruct (dep_wf HX a c (or_intror (or_intror Hc))) as [_ (? & _)]. auto.
            -- destruct (dep_wf HX a c (or_intror (or_introl Hc))) as [_ (? & _)]. auto.
          * destruct (co_dom Hw _ _ Hco) as (_ & ? & _). auto.
      - destruct Ha as [H | (_ & Hrf & _)].
        + destruct (rmw_wf HX a b H) as (? & ? & _). auto.
        + destruct (rf_dom Hw _ _ Hrf) as (? & ? & _). auto.
      - destruct Hb as [(f & (? & _) & _ & (_ & ? & _)) | [(r1 & w1 & (? & _) & _ & _ & _ & (_ & ? & _)) |
                       [(_ & (? & ? & _) & _) | [(_ & f & (? & _) & _ & (_ & ? & _)) | [(_ & (? & ? & _)) |
                       [(_ & (f & (? & _) & _ & (_ & ? & _)) & _) | [((? & ? & _) & _) |
                       (_ & c & (? & _) & _ & Hco & _)]]]]]]]; auto.
        destruct (co_dom Hw _ _ Hco) as (_ & ? & _). auto.
      - destruct Hl as (_ & (? & ? & _) & _). auto.
      - destruct Hs as (_ & u & Hu & Hm). destruct (rmw_wf HX b u Hm) as (Hb & _).
        split; [| exact Hb].
        destruct Hu as [[[H | [H | H]] _] | ((? & _) & _)]; auto.
        + destruct (rf_dom Hw _ _ H) as (? & _). auto.
        + destruct H as (? & _). auto.
        + destruct (co_dom Hw _ _ H) as (? & _). auto.
    Qed.

    Lemma intgen_in (Hw : wf_witness X wit) a b :
      (po_loc X a b \/ fr X wit a b \/ co wit a b \/ rf wit a b) -> In a (evs X) /\ In b (evs X).
    Proof.
      intros [[(? & ? & _) _] | [(? & ? & _) | [H | H]]]; auto.
      - destruct (co_dom Hw _ _ H) as (? & ? & _). auto.
      - destruct (rf_dom Hw _ _ H) as (? & ? & _). auto.
    Qed.

    Definition checkb (ord_int ord_ext : list event) : bool :=
      wfcb && wfwb && acycb intgenb ord_int && acycb obgenb ord_ext && atomicb.

    (** The checker is sound: if it succeeds, the outcome is allowed. *)
    Theorem allowed_of_checkb ord_int ord_ext :
      checkb ord_int ord_ext = true -> allowed v X.
    Proof.
      unfold checkb. intros H. repeat rewrite andb_true_iff in H.
      destruct H as [[[[Hc Hw] Hi] He] Ha].
      pose proof (wf_cand_of_wfcb Hc) as HX. pose proof (wf_witness_of_wfwb Hw) as HW.
      split; [exact HX |]. exists wit. split; [exact HW |]. split; [| split].
      - eapply acycb_sound; [| exact Hi]. intros a b Hab.
        destruct (intgen_in HW a b Hab) as [Ha' Hb']. repeat split; auto. apply intgenb_of. exact Hab.
      - eapply acycb_sound; [| exact He]. intros a b Hab.
        destruct (obgen_in HX HW a b Hab) as [Ha' Hb']. repeat split; auto. apply obgenb_of. exact Hab.
      - apply atomic_of_atomicb. exact Ha.
    Qed.

    (** The same checker without EXTERNAL: a well-formed witness that
        satisfies INTERNAL and ATOMIC.  Used to show that a forbidden
        outcome is excluded by EXTERNAL and not by a value mismatch. *)
    Theorem wit_of_checkb_noext ord_int :
      wfwb && acycb intgenb ord_int && atomicb = true ->
      wf_witness X wit /\ internal X wit /\ atomic X wit.
    Proof.
      intros H. repeat rewrite andb_true_iff in H. destruct H as [[Hw Hi] Ha].
      pose proof (wf_witness_of_wfwb Hw) as HW.
      split; [exact HW | split].
      - eapply acycb_sound; [| exact Hi]. intros a b Hab.
        destruct (intgen_in HW a b Hab) as [Ha' Hb']. repeat split; auto. apply intgenb_of. exact Hab.
      - apply atomic_of_atomicb. exact Ha.
    Qed.
  End Check.

  (** A forbidden outcome is not vacuous if some well-formed witness
      satisfies INTERNAL and ATOMIC: EXTERNAL alone excludes it. *)
  Definition only_external_fails (X : cand) : Prop :=
    exists w, wf_witness X w /\ internal X w /\ atomic X w.

  (** ** Part 5. Tools for "forbidden" *)

  Section Forbid.
    Variable v : variant.
    Variable X : cand.
    Variable w : witness.

    Lemma ob_rfe a b : rf w a b -> tid a <> tid b -> obgen v X w a b.
    Proof. intros H Ht. left. split; [left; exact H | exact Ht]. Qed.

    Lemma ob_fre a b : fr X w a b -> tid a <> tid b -> obgen v X w a b.
    Proof. intros H Ht. left. split; [right; left; exact H | exact Ht]. Qed.

    Lemma ob_coe a b : co w a b -> tid a <> tid b -> obgen v X w a b.
    Proof. intros H Ht. left. split; [right; right; exact H | exact Ht]. Qed.

    Lemma ob_data a b : inp (data X) a b -> obgen v X w a b.
    Proof. intros H. right; left. right; left. exact H. Qed.

    Lemma ob_dmbsy a f b : po X a f -> isF FSY f = true -> po X f b -> obgen v X w a b.
    Proof. intros H1 Hf H2. right; right; right; left. left. exists f. auto. Qed.

    Lemma ob_relacq a b : isL a = true -> po X a b -> isA b = true -> obgen v X w a b.
    Proof. intros H1 H2 H3. right; right; right; left. right; right; left. auto. Qed.

    Lemma ob_dmbld a f b : isR a = true -> po X a f -> isF FLD f = true -> po X f b -> obgen v X w a b.
    Proof. intros H0 H1 Hf H2. right; right; right; left. right; right; right; left. split; [exact H0 |]. exists f. auto. Qed.

    Lemma ob_acq a b : isA a = true -> po X a b -> obgen v X w a b.
    Proof. intros H1 H2. right; right; right; left. right; right; right; right; left. auto. Qed.

    Lemma ob_dmbst a f b :
      isW a = true -> po X a f -> isF FST f = true -> po X f b -> isW b = true -> obgen v X w a b.
    Proof.
      intros H0 H1 Hf H2 H3. right; right; right; left. right; right; right; right; right; left.
      split; [exact H0 | split; [exists f; auto | exact H3]].
    Qed.

    Lemma ob_rel a b : po X a b -> isL b = true -> obgen v X w a b.
    Proof. intros H1 H2. right; right; right; left. right; right; right; right; right; right; left. auto. Qed.

    Lemma ob_si_fre a u b :
      has_si v = true -> fr X w a u -> tid a <> tid u -> inp (rmw X) b u -> obgen v X w a b.
    Proof.
      intros Hv Hfr Ht Hm. right; right; right; right; right.
      split; [exact Hv |]. exists u. split; [left; split; [right; left; exact Hfr | exact Ht] | exact Hm].
    Qed.

    Lemma cycle4 a b c d :
      external v X w -> obgen v X w a b -> obgen v X w b c -> obgen v X w c d -> obgen v X w d a -> False.
    Proof.
      intros Hext H1 H2 H3 H4. apply (Hext a).
      eapply t_trans; [apply t_step; exact H1 |].
      eapply t_trans; [apply t_step; exact H2 |].
      eapply t_trans; [apply t_step; exact H3 |].
      apply t_step. exact H4.
    Qed.

    Lemma cycle6 a b c d e f :
      external v X w -> obgen v X w a b -> obgen v X w b c -> obgen v X w c d ->
      obgen v X w d e -> obgen v X w e f -> obgen v X w f a -> False.
    Proof.
      intros Hext H1 H2 H3 H4 H5 H6. apply (Hext a).
      eapply t_trans; [apply t_step; exact H1 |].
      eapply t_trans; [apply t_step; exact H2 |].
      eapply t_trans; [apply t_step; exact H3 |].
      eapply t_trans; [apply t_step; exact H4 |].
      eapply t_trans; [apply t_step; exact H5 |].
      apply t_step. exact H6.
    Qed.

    Lemma ob_addr a b : inp (addr X) a b -> obgen v X w a b.
    Proof. intros H. right; left. left. exact H. Qed.

    Hypothesis Hw : wf_witness X w.

    (** A read with a nonzero value has a source.  This uses [classic]. *)
    Lemma read_source r : In r (evs X) -> isR r = true -> eval r <> 0 -> exists u, rf w u r.
    Proof.
      intros Hr HR Hv. destruct (classic (exists u, rf w u r)) as [H | Hno]; [exact H |].
      exfalso. apply Hv. apply (rf_init Hw r Hr HR). intros u Hu. apply Hno. eauto.
    Qed.

    (** A read with no source reads before every write at its location. *)
    Lemma fr_no_source r u :
      In r (evs X) -> In u (evs X) -> isR r = true -> isW u = true -> sloc r u = true ->
      (forall u0, rf w u0 r -> False) -> fr X w r u.
    Proof. intros H1 H2 H3 H4 H5 H6. repeat split; auto. intros u0 Hu0. exfalso. eauto. Qed.

    Lemma fr_of_rf_co r u0 u :
      In u (evs X) -> rf w u0 r -> co w u0 u -> fr X w r u.
    Proof.
      intros Hu Hrf Hco. destruct (rf_dom Hw _ _ Hrf) as (_ & Hr & _ & HR & Hl & _).
      destruct (co_dom Hw _ _ Hco) as (_ & _ & _ & HW & Hl').
      repeat split; auto.
      - unfold sloc in *. destruct (eloc u0), (eloc r), (eloc u); try discriminate.
        apply loc_eqb_spec in Hl, Hl'. subst. apply loc_eqb_spec. reflexivity.
      - intros u1 Hu1. rewrite (rf_func Hw _ _ _ Hu1 Hrf). exact Hco.
    Qed.
  End Forbid.

  (** Membership in a concrete list of events, program order between two
      concrete events, and elimination of the impossible sources of a
      read. *)
  Ltac in_tac := cbn; repeat (first [left; reflexivity | right]).
  Ltac po_tac := split; [in_tac | split; [in_tac | split; [reflexivity | cbn; lia]]].
  Ltac kill H := cbn in H; discriminate H.
  Ltac pin_src Hin Hwu Hl Hv :=
    cbn in Hin; repeat (destruct Hin as [<- | Hin]; [first [kill Hwu | kill Hl | kill Hv | (cbn in Hv; lia) | idtac] |]);
    try contradiction.
  Ltac no_src Hw :=
    let u0 := fresh "u0" in let Hu0 := fresh "Hu0" in
    let Hin := fresh "Hin" in let Hwu := fresh "Hwu" in let Hl := fresh "Hl" in let Hv := fresh "Hv" in
    intros u0 Hu0; destruct (rf_dom Hw _ _ Hu0) as (Hin & _ & Hwu & _ & Hl & Hv);
    pin_src Hin Hwu Hl Hv.

  Definition Rd (t i : nat) (x : loc) (v : nat) (a : bool) : event := Ev t i (KR x v a).
  Definition Wr (t i : nat) (x : loc) (v : nat) (l : bool) : event := Ev t i (KW x v l).
  Definition Fn (t i : nat) (k : fence) : event := Ev t i (KF k).

  (** ** Part 6. Litmus verdicts *)


  (** *** Sanity checks: classic tests with well-known ARMv8 verdicts

      These check the clauses against verdicts that are standard for
      ARMv8 (MP, SB, LB, IRIW, CoRR with and without barriers or
      dependencies).  They are a consistency check of this file's reading
      of aarch64.cat, not a validation of the model. *)

  Module Sanity.
    Definition nodeps (l : list event) : cand := {| evs := l; rmw := []; addr := []; data := []; ctrl := [] |}.

    (** MP, no barrier: allowed. *)
    Theorem mp_allowed v :
      allowed v (nodeps [Wr 1 0 lx 1 false; Wr 1 1 ly 1 false; Rd 2 0 ly 1 false; Rd 2 1 lx 0 false]).
    Proof.
      apply (allowed_of_checkb v _ [] [(Wr 1 1 ly 1 false, Rd 2 0 ly 1 false)]
        [Rd 2 1 lx 0 false; Wr 1 0 lx 1 false; Wr 1 1 ly 1 false; Rd 2 0 ly 1 false]
        [Rd 2 1 lx 0 false; Wr 1 0 lx 1 false; Wr 1 1 ly 1 false; Rd 2 0 ly 1 false]).
      destruct v; exact eq_refl.
    Qed.

    (** MP+dmb.st+ctrl (control dependency to a read, no ISB): allowed. *)
    Definition mpctrl : cand := {|
      evs := [Wr 1 0 lx 1 false; Fn 1 1 FST; Wr 1 2 ly 1 false; Rd 2 0 ly 1 false; Rd 2 1 lx 0 false];
      rmw := []; addr := []; data := []; ctrl := [(Rd 2 0 ly 1 false, Rd 2 1 lx 0 false)] |}.

    Theorem mp_dmbst_ctrl_allowed v : allowed v mpctrl.
    Proof.
      apply (allowed_of_checkb v _ [] [(Wr 1 2 ly 1 false, Rd 2 0 ly 1 false)]
        [Rd 2 1 lx 0 false; Wr 1 0 lx 1 false; Fn 1 1 FST; Wr 1 2 ly 1 false; Rd 2 0 ly 1 false]
        [Rd 2 1 lx 0 false; Wr 1 0 lx 1 false; Fn 1 1 FST; Wr 1 2 ly 1 false; Rd 2 0 ly 1 false]).
      destruct v; exact eq_refl.
    Qed.

    (** MP+dmb.st+addr: forbidden. *)
    Definition mpaddr : cand := {|
      evs := [Wr 1 0 lx 1 false; Fn 1 1 FST; Wr 1 2 ly 1 false; Rd 2 0 ly 1 false; Rd 2 1 lx 0 false];
      rmw := []; addr := [(Rd 2 0 ly 1 false, Rd 2 1 lx 0 false)]; data := []; ctrl := [] |}.

    Theorem mp_dmbst_addr_forbidden v : forbidden v mpaddr.
    Proof.
      intros w Hw (_ & Hext & _).
      destruct (read_source _ w Hw (Rd 2 0 ly 1 false)) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv). pin_src Hin Hwu Hl Hv.
      apply (cycle4 v _ w (Wr 1 0 lx 1 false) (Wr 1 2 ly 1 false) (Rd 2 0 ly 1 false) (Rd 2 1 lx 0 false) Hext).
      - apply (ob_dmbst v _ w _ (Fn 1 1 FST)); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
      - apply ob_rfe; [exact Hu | discriminate].
      - apply ob_addr. left. reflexivity.
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
    Qed.

    (** SB+dmb.ld+dmb.ld: allowed (DMB LD does not order W→R). *)
    Theorem sb_dmbld_allowed v :
      allowed v (nodeps [Wr 1 0 lx 1 false; Fn 1 1 FLD; Rd 1 2 ly 0 false;
                         Wr 2 0 ly 1 false; Fn 2 1 FLD; Rd 2 2 lx 0 false]).
    Proof.
      apply (allowed_of_checkb v _ [] []
        [Rd 1 2 ly 0 false; Rd 2 2 lx 0 false; Wr 1 0 lx 1 false; Fn 1 1 FLD; Wr 2 0 ly 1 false; Fn 2 1 FLD]
        [Rd 1 2 ly 0 false; Rd 2 2 lx 0 false; Wr 1 0 lx 1 false; Fn 1 1 FLD; Wr 2 0 ly 1 false; Fn 2 1 FLD]).
      destruct v; exact eq_refl.
    Qed.

    (** SB+dmb.sy+dmb.sy: forbidden. *)
    Theorem sb_dmbsy_forbidden v :
      forbidden v (nodeps [Wr 1 0 lx 1 false; Fn 1 1 FSY; Rd 1 2 ly 0 false;
                           Wr 2 0 ly 1 false; Fn 2 1 FSY; Rd 2 2 lx 0 false]).
    Proof.
      intros w Hw (_ & Hext & _).
      apply (cycle4 v _ w (Wr 1 0 lx 1 false) (Rd 1 2 ly 0 false) (Wr 2 0 ly 1 false) (Rd 2 2 lx 0 false) Hext).
      - apply (ob_dmbsy v _ w _ (Fn 1 1 FSY)); [po_tac | reflexivity | po_tac].
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
      - apply (ob_dmbsy v _ w _ (Fn 2 1 FSY)); [po_tac | reflexivity | po_tac].
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
    Qed.

    (** LB, no dependency: allowed. *)
    Theorem lb_allowed v :
      allowed v (nodeps [Rd 1 0 lx 1 false; Wr 1 1 ly 1 false; Rd 2 0 ly 1 false; Wr 2 1 lx 1 false]).
    Proof.
      apply (allowed_of_checkb v _ [] [(Wr 1 1 ly 1 false, Rd 2 0 ly 1 false); (Wr 2 1 lx 1 false, Rd 1 0 lx 1 false)]
        [Wr 1 1 ly 1 false; Wr 2 1 lx 1 false; Rd 1 0 lx 1 false; Rd 2 0 ly 1 false]
        [Wr 1 1 ly 1 false; Wr 2 1 lx 1 false; Rd 1 0 lx 1 false; Rd 2 0 ly 1 false]).
      destruct v; exact eq_refl.
    Qed.

    (** LB+data+data: forbidden. *)
    Definition lbdata : cand := {|
      evs := [Rd 1 0 lx 1 false; Wr 1 1 ly 1 false; Rd 2 0 ly 1 false; Wr 2 1 lx 1 false];
      rmw := []; addr := [];
      data := [(Rd 1 0 lx 1 false, Wr 1 1 ly 1 false); (Rd 2 0 ly 1 false, Wr 2 1 lx 1 false)]; ctrl := [] |}.

    Theorem lb_data_forbidden v : forbidden v lbdata.
    Proof.
      intros w Hw (_ & Hext & _).
      destruct (read_source _ w Hw (Rd 1 0 lx 1 false)) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv). pin_src Hin Hwu Hl Hv.
      destruct (read_source _ w Hw (Rd 2 0 ly 1 false)) as (u' & Hu'); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu') as (Hin' & _ & Hwu' & _ & Hl' & Hv'). pin_src Hin' Hwu' Hl' Hv'.
      apply (cycle4 v _ w (Rd 1 0 lx 1 false) (Wr 1 1 ly 1 false) (Rd 2 0 ly 1 false) (Wr 2 1 lx 1 false) Hext).
      - apply ob_data. left. reflexivity.
      - apply ob_rfe; [exact Hu' | discriminate].
      - apply ob_data. right; left. reflexivity.
      - apply ob_rfe; [exact Hu | discriminate].
    Qed.

    (** IRIW+dmb.ld+dmb.ld: forbidden (multicopy atomicity). *)
    Definition iriw : cand := nodeps
      [Wr 1 0 lx 1 false; Wr 2 0 ly 1 false;
       Rd 3 0 lx 1 false; Fn 3 1 FLD; Rd 3 2 ly 0 false;
       Rd 4 0 ly 1 false; Fn 4 1 FLD; Rd 4 2 lx 0 false].

    Theorem iriw_dmbld_forbidden v : forbidden v iriw.
    Proof.
      intros w Hw (_ & Hext & _).
      destruct (read_source _ w Hw (Rd 3 0 lx 1 false)) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv). pin_src Hin Hwu Hl Hv.
      destruct (read_source _ w Hw (Rd 4 0 ly 1 false)) as (u' & Hu'); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu') as (Hin' & _ & Hwu' & _ & Hl' & Hv'). pin_src Hin' Hwu' Hl' Hv'.
      apply (cycle6 v _ w (Wr 1 0 lx 1 false) (Rd 3 0 lx 1 false) (Rd 3 2 ly 0 false)
                         (Wr 2 0 ly 1 false) (Rd 4 0 ly 1 false) (Rd 4 2 lx 0 false) Hext).
      - apply ob_rfe; [exact Hu | discriminate].
      - apply (ob_dmbld v _ w _ (Fn 3 1 FLD)); [reflexivity | po_tac | reflexivity | po_tac].
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
      - apply ob_rfe; [exact Hu' | discriminate].
      - apply (ob_dmbld v _ w _ (Fn 4 1 FLD)); [reflexivity | po_tac | reflexivity | po_tac].
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
    Qed.

    (** CoRR: forbidden by INTERNAL. *)
    Theorem corr_forbidden v :
      forbidden v (nodeps [Wr 1 0 lx 1 false; Rd 2 0 lx 1 false; Rd 2 1 lx 0 false]).
    Proof.
      intros w Hw (Hint & _ & _).
      destruct (read_source _ w Hw (Rd 2 0 lx 1 false)) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv). pin_src Hin Hwu Hl Hv.
      apply (Hint (Wr 1 0 lx 1 false)).
      apply t_trans with (y := Rd 2 0 lx 1 false); [apply t_step; right; right; right; exact Hu |].
      apply t_trans with (y := Rd 2 1 lx 0 false); [apply t_step; left; split; [po_tac | reflexivity] |].
      apply t_step. right; left. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
      no_src Hw.
    Qed.
  End Sanity.

  (** *** RSW through the object, SeqLock mapping (task G-3 (c)) *)

  Module RSWObj.
    Section Prog.
      Variables (a1 l1 a2 l2 : bool) (gt tt ra wa rr wr vx vy : nat) (ad da ct : list (event * event)).

      (** T1: zr()=1; zw(2); zr()=2; read()=(vx,vy) *)
      Definition rz1 := Rd 1 0 lz 1 false.
      Definition wz2 := Wr 1 1 lz 2 false.
      Definition rz2 := Rd 1 2 lz 2 false.
      Definition gts := Rd 1 3 ls gt false.
      Definition f1 := Fn 1 4 FLD.
      Definition rx := Rd 1 5 lx vx false.
      Definition ry := Rd 1 6 ly vy false.
      Definition f2 := Fn 1 7 FLD.
      Definition tts := Rd 1 8 ls tt false.
      (** T2: write(1,1); zw(1) *)
      Definition aR := Rd 2 0 ls ra a1.
      Definition aW := Wr 2 0 ls wa l1.
      Definition f3 := Fn 2 1 FST.
      Definition wx := Wr 2 2 lx 1 false.
      Definition wy := Wr 2 3 ly 1 false.
      Definition f4 := Fn 2 4 FST.
      Definition rR := Rd 2 5 ls rr a2.
      Definition rW := Wr 2 5 ls wr l2.
      Definition wz1 := Wr 2 6 lz 1 false.

      Definition X : cand := {|
        evs := [rz1; wz2; rz2; gts; f1; rx; ry; f2; tts; aR; aW; f3; wx; wy; f4; rR; rW; wz1];
        rmw := [(aR, aW); (rR, rW)];
        addr := ad; data := da; ctrl := ct |}.

      Lemma forb v : vx = 0 -> forbidden v X.
      Proof.
        intros Hvx w Hw (_ & Hext & _).
        destruct (read_source X w Hw rz1) as (u & Hu); [in_tac | reflexivity | discriminate |].
        destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
        pin_src Hin Hwu Hl Hv.
        apply (cycle4 v X w wx wz1 rz1 rx Hext).
        - apply (ob_dmbst v X w wx f4 wz1); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v X w rz1 f1 rx); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.
    End Prog.

    (** The outcome zr()=1, zw(2), zr()=2, read() returning x = 0 is
        forbidden, for every RMW flavour of acq and rel, every value read
        or written by the RMWs and by get_ticket/test_ticket, every y, and
        every dependency relation. *)
    Theorem rsw_obj_forbidden v a1 l1 a2 l2 gt tt ra wa rr wr vy ad da ct :
      forbidden v (X a1 l1 a2 l2 gt tt ra wa rr wr 0 vy ad da ct).
    Proof. apply forb. reflexivity. Qed.

    (** Positive control: the same program with read() = (1,1) (s read as
        2 twice) is allowed; its witness is the sequential run T2; T1. *)
    Definition Xc := X false false false false 2 2 0 1 1 2 1 1 [] [] [].

    Theorem rsw_obj_control_allowed v : allowed v Xc.
    Proof.
      apply (allowed_of_checkb v Xc
        [(aW false 1, rW false 2); (wz1, wz2)]
        [(aW false 1, rR false 1); (wz1, rz1); (wz2, rz2); (rW false 2, gts 2); (wx, rx 1);
         (wy, ry 1); (rW false 2, tts 2)]
        [aR false 0; aW false 1; f3; wx; wy; f4; rR false 1; rW false 2; wz1;
         rz1; wz2; rz2; gts 2; f1; rx 1; ry 1; f2; tts 2]
        [aR false 0; aW false 1; f3; wx; wy; f4; rR false 1; rW false 2; wz1;
         rz1; wz2; rz2; gts 2; f1; rx 1; ry 1; f2; tts 2]).
      destruct v; exact eq_refl.
    Qed.
  End RSWObj.


  (** *** RSW through the object, minimal core, and the Δ2 contrast *)

  Module RSWObjCore.
    Section Prog.
      Variables (vx : nat) (acq : bool) (ad da ct : list (event * event)).

      (** T1: R z = 1; W z 2; R z = 2 (acquire iff [acq]); [DMB LD]; R x = vx
          T2: W x 1; DMB ST; W z 1 *)
      Definition rz1 := Rd 1 0 lz 1 false.
      Definition wz2 := Wr 1 1 lz 2 false.
      Definition rz2 := Rd 1 2 lz 2 acq.
      Definition f1 := Fn 1 3 FLD.
      Definition rx := Rd 1 4 lx vx false.
      Definition wx := Wr 2 0 lx 1 false.
      Definition f2 := Fn 2 1 FST.
      Definition wz1 := Wr 2 2 lz 1 false.

      (** With the DMB LD (the SeqLock mapping of rmb). *)
      Definition X : cand := {|
        evs := [rz1; wz2; rz2; f1; rx; wx; f2; wz1];
        rmw := []; addr := ad; data := da; ctrl := ct |}.

      (** Without it: the order is carried by the acquire on the last read
          of z only ([acq = true]), the shape of Litmus.RSW. *)
      Definition Xa : cand := {|
        evs := [rz1; wz2; rz2; rx; wx; f2; wz1];
        rmw := []; addr := ad; data := da; ctrl := ct |}.

      Lemma forb v : vx = 0 -> forbidden v X.
      Proof.
        intros Hvx w Hw (_ & Hext & _).
        destruct (read_source X w Hw rz1) as (u & Hu); [in_tac | reflexivity | discriminate |].
        destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
        pin_src Hin Hwu Hl Hv.
        apply (cycle4 v X w wx wz1 rz1 rx Hext).
        - apply (ob_dmbst v X w wx f2 wz1); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v X w rz1 f1 rx); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.
    End Prog.

    Theorem rsw_obj_core_forbidden v acq ad da ct : forbidden v (X 0 acq ad da ct).
    Proof. apply forb. reflexivity. Qed.

    (** The outcome is excluded by EXTERNAL alone: a well-formed witness
        satisfies INTERNAL and ATOMIC. *)
    Theorem rsw_obj_core_not_vacuous :
      exists w, wf_witness (X 0 false [] [] []) w /\ internal (X 0 false [] [] []) w /\
                atomic (X 0 false [] [] []) w.
    Proof.
      assert (H : wfwb (X 0 false [] [] []) [(wz1, wz2)] [(wz1, rz1); (wz2, rz2 false)] = true /\
                  acycb (X 0 false [] [] []) (intgenb [(wz1, wz2)] [(wz1, rz1); (wz2, rz2 false)])
                        [wz1; rz1; wz2; rz2 false; f1; rx 0; wx; f2] = true /\
                  atomicb (X 0 false [] [] []) [(wz1, wz2)] [(wz1, rz1); (wz2, rz2 false)] = true)
        by (split; [| split]; exact eq_refl).
      destruct H as (H1 & H2 & H3).
      exists (wit [(wz1, wz2)] [(wz1, rz1); (wz2, rz2 false)]).
      pose proof (wf_witness_of_wfwb _ _ _ H1) as Hw.
      split; [exact Hw | split].
      - eapply acycb_sound; [| exact H2]. intros a b Hab.
        destruct (intgen_in _ _ _ Hw a b Hab). repeat split; auto. eapply intgenb_of. exact Hab.
      - apply atomic_of_atomicb. exact H3.
    Qed.

    (** Positive control: with x = 1 the same program is allowed. *)
    Theorem rsw_obj_core_control_allowed v : allowed v (X 1 false [] [] []).
    Proof.
      apply (allowed_of_checkb v (X 1 false [] [] []) [(wz1, wz2)] [(wx, rx 1); (wz1, rz1); (wz2, rz2 false)]
        [wx; f2; wz1; rz1; wz2; rz2 false; f1; rx 1]
        [wx; f2; wz1; rz1; wz2; rz2 false; f1; rx 1]).
      destruct v; exact eq_refl.
    Qed.

    (** The Δ2 contrast: if the order is carried by an acquire on the
        last read of z instead of by DMB LD, the outcome is allowed. *)
    Theorem rsw_obj_core_ldar_allowed v : allowed v (Xa 0 true [] [] []).
    Proof.
      apply (allowed_of_checkb v (Xa 0 true [] [] []) [(wz1, wz2)] [(wz1, rz1); (wz2, rz2 true)]
        [wz1; rz1; wz2; rz2 true; rx 0; wx; f2]
        [rz2 true; rx 0; wx; f2; wz1; rz1; wz2]).
      destruct v; exact eq_refl.
    Qed.
  End RSWObjCore.

  (** *** Cross-checks against memory/Litmus.v (the ARM verdicts of Δ1, Δ2) *)

  Module CrossCheck.
    (** Litmus.RSW (Δ2): T1: R x = 1; W x 2; R(acq) x = 2; R z = 0
        ‖ T2: W z 1; W(rel) x 1.  ARM.v allows it ([RSW.arm_allow]). *)
    Definition rx1 := Rd 1 0 lx 1 false.
    Definition wx2 := Wr 1 1 lx 2 false.
    Definition rxa := Rd 1 2 lx 2 true.
    Definition rz := Rd 1 3 lz 0 false.
    Definition wz := Wr 2 0 lz 1 false.
    Definition wx1 := Wr 2 1 lx 1 true.

    Definition rsw : cand := {|
      evs := [rx1; wx2; rxa; rz; wz; wx1]; rmw := []; addr := []; data := []; ctrl := [] |}.

    Theorem rsw_allowed v : allowed v rsw.
    Proof.
      apply (allowed_of_checkb v rsw [(wx1, wx2)] [(wx1, rx1); (wx2, rxa)]
        [wx1; rx1; wx2; rxa; rz; wz] [rxa; rz; wz; wx1; rx1; wx2]).
      destruct v; exact eq_refl.
    Qed.

    (** Litmus.SB (Δ1): T1: W(rel) x 1; R(acq) y = 0 ‖ T2: W(rel) y 1;
        R(acq) x = 0.  ARM.v forbids it ([SB.arm_forbid]). *)
    Definition sx := Wr 1 0 lx 1 true.
    Definition sy0 := Rd 1 1 ly 0 true.
    Definition sy := Wr 2 0 ly 1 true.
    Definition sx0 := Rd 2 1 lx 0 true.

    Definition sb : cand := {|
      evs := [sx; sy0; sy; sx0]; rmw := []; addr := []; data := []; ctrl := [] |}.

    Theorem sb_relacq_forbidden v : forbidden v sb.
    Proof.
      intros w Hw (_ & Hext & _).
      apply (cycle4 v sb w sx sy0 sy sx0 Hext).
      - apply ob_relacq; [reflexivity | po_tac | reflexivity].
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
      - apply ob_relacq; [reflexivity | po_tac | reflexivity].
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
    Qed.
  End CrossCheck.

  (** *** SeqLockZ+rfi (the Q6 outcome), task G-3 (a) and (b) *)

  Module SeqLockZ.
    (** Minimal core.  P0: W z 1; R z = 1; DMB LD; R x = 0
        ‖ P1: W x 1; DMB SY; R z = 0. *)
    Definition wz := Wr 1 0 lz 1 false.
    Definition rz := Rd 1 1 lz 1 false.
    Definition f1 := Fn 1 2 FLD.
    Definition rx := Rd 1 3 lx 0 false.
    Definition wx := Wr 2 0 lx 1 false.
    Definition f2 := Fn 2 1 FSY.
    Definition rz0 := Rd 2 2 lz 0 false.

    Definition core : cand := {|
      evs := [wz; rz; f1; rx; wx; f2; rz0]; rmw := []; addr := []; data := []; ctrl := [] |}.

    Theorem core_allowed v : allowed v core.
    Proof.
      apply (allowed_of_checkb v core [] [(wz, rz)]
        [rz0; wz; rz; f1; rx; wx; f2] [rz; f1; rx; wx; f2; rz0; wz]).
      destruct v; exact eq_refl.
    Qed.

    (** The full test of the redesign plan (SeqLockQ6.v header).  P0 (T1):
        zw(1); zr() = 1; read() = (0,0) with get_ticket/test_ticket = LDR s.
        P1 (T2): write(1,1) with acq = SWP(a1,l1) s 0 -> 1 and rel =
        SWP(a2,l2) s 1 -> 2; read() = (1,1); zr() = 0.  [a] and [l] are the
        acquire and release bits of each RMW: (true, false) is SWPA,
        (false, true) SWPL, (true, true) SWPAL.  LDADD gives the same
        events. *)
    Section Full.
      Variables a1 l1 a2 l2 : bool.
      Definition p0 := [Wr 1 0 lz 1 false; Rd 1 1 lz 1 false; Rd 1 2 ls 0 false; Fn 1 3 FLD;
                        Rd 1 4 lx 0 false; Rd 1 5 ly 0 false; Fn 1 6 FLD; Rd 1 7 ls 0 false].
      Definition aR := Rd 2 0 ls 0 a1.
      Definition aW := Wr 2 0 ls 1 l1.
      Definition rR := Rd 2 5 ls 1 a2.
      Definition rW := Wr 2 5 ls 2 l2.
      Definition p1 := [aR; aW; Fn 2 1 FST; Wr 2 2 lx 1 false; Wr 2 3 ly 1 false; Fn 2 4 FST;
                        rR; rW; Rd 2 6 ls 2 false; Fn 2 7 FLD; Rd 2 8 lx 1 false;
                        Rd 2 9 ly 1 false; Fn 2 10 FLD; Rd 2 11 ls 2 false; Rd 2 12 lz 0 false].
      Definition full : cand := {|
        evs := p0 ++ p1; rmw := [(aR, aW); (rR, rW)]; addr := []; data := []; ctrl := [] |}.

      Definition full_co := [(aW, rW)].
      Definition full_rf := [(Wr 1 0 lz 1 false, Rd 1 1 lz 1 false); (aW, rR); (rW, Rd 2 6 ls 2 false);
                             (Wr 2 2 lx 1 false, Rd 2 8 lx 1 false); (Wr 2 3 ly 1 false, Rd 2 9 ly 1 false);
                             (rW, Rd 2 11 ls 2 false)].
      Definition full_int := [Rd 1 2 ls 0 false; Rd 1 7 ls 0 false; Rd 1 4 lx 0 false; Rd 1 5 ly 0 false;
                              Fn 1 3 FLD; Fn 1 6 FLD] ++ p1 ++ [Wr 1 0 lz 1 false; Rd 1 1 lz 1 false].
      Definition full_ext := tl p0 ++ p1 ++ [Wr 1 0 lz 1 false].
    End Full.

    (** Allowed for every flavour of the two RMWs. *)
    Theorem full_allowed v a1 l1 a2 l2 : allowed v (full a1 l1 a2 l2).
    Proof.
      apply (allowed_of_checkb v (full a1 l1 a2 l2) (full_co l1 l2) (full_rf l1 a2 l2)
        (full_int a1 l1 a2 l2) (full_ext a1 l1 a2 l2)).
      destruct v, a1, l1, a2, l2; exact eq_refl.
    Qed.
  End SeqLockZ.

  (** *** MP with DMB ST / DMB LD (the SeqLock's wmb/rmb), and SB+rfi *)

  Module MPBar.
    (** P0: W x 1; DMB ST; W y 1 ‖ P1: R y = 1; DMB LD; R x = 0 *)
    Definition wx := Wr 1 0 lx 1 false.
    Definition f1 := Fn 1 1 FST.
    Definition wy := Wr 1 2 ly 1 false.
    Definition ry := Rd 2 0 ly 1 false.
    Definition f2 := Fn 2 1 FLD.
    Definition rx := Rd 2 2 lx 0 false.

    Definition mp : cand := {|
      evs := [wx; f1; wy; ry; f2; rx]; rmw := []; addr := []; data := []; ctrl := [] |}.

    Theorem mp_dmbst_dmbld_forbidden v : forbidden v mp.
    Proof.
      intros w Hw (_ & Hext & _).
      destruct (read_source mp w Hw ry) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
      pin_src Hin Hwu Hl Hv.
      apply (cycle4 v mp w wx wy ry rx Hext).
      - apply (ob_dmbst v mp w wx f1 wy); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
      - apply ob_rfe; [exact Hu | discriminate].
      - apply (ob_dmbld v mp w ry f2 rx); [reflexivity | po_tac | reflexivity | po_tac].
      - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
        no_src Hw.
    Qed.
  End MPBar.

  Module SBrfi.
    (** Reviewer A's test (popl2027-reviews.md:69-81):
        P0: W x 1; R x = 1; R y = 0 ‖ P1: W y 1; R y = 1; R x = 0,
        plain, and with a DMB LD between the two reads of each thread. *)
    Definition wx := Wr 1 0 lx 1 false.
    Definition rx1 := Rd 1 1 lx 1 false.
    Definition wy := Wr 2 0 ly 1 false.
    Definition ry1 := Rd 2 1 ly 1 false.

    Definition plain : cand := {|
      evs := [wx; rx1; Rd 1 2 ly 0 false; wy; ry1; Rd 2 2 lx 0 false];
      rmw := []; addr := []; data := []; ctrl := [] |}.

    Theorem sbrfi_allowed v : allowed v plain.
    Proof.
      apply (allowed_of_checkb v plain [] [(wx, rx1); (wy, ry1)]
        [Rd 1 2 ly 0 false; Rd 2 2 lx 0 false; wx; wy; rx1; ry1]
        [Rd 1 2 ly 0 false; Rd 2 2 lx 0 false; wx; wy; rx1; ry1]).
      destruct v; exact eq_refl.
    Qed.

    Definition dmbld : cand := {|
      evs := [wx; rx1; Fn 1 2 FLD; Rd 1 3 ly 0 false; wy; ry1; Fn 2 2 FLD; Rd 2 3 lx 0 false];
      rmw := []; addr := []; data := []; ctrl := [] |}.

    Theorem sbrfi_dmbld_allowed v : allowed v dmbld.
    Proof.
      apply (allowed_of_checkb v dmbld [] [(wx, rx1); (wy, ry1)]
        [Rd 1 3 ly 0 false; Rd 2 3 lx 0 false; wx; wy; rx1; ry1; Fn 1 2 FLD; Fn 2 2 FLD]
        [rx1; Fn 1 2 FLD; Rd 1 3 ly 0 false; ry1; Fn 2 2 FLD; Rd 2 3 lx 0 false; wx; wy]).
      destruct v; exact eq_refl.
    Qed.
  End SBrfi.

  (** *** The atomic clause of the planned hybrid specification, task G-3 (d) *)

  Module AtomicClause.
    (** P0: W x 1; [DMB ST]; RMW s (read [ra], write 1, flavour [a], [l])
        ‖ P1: get s = 1 (LDR or LDAR); [DMB LD]; R x = 0.
        The atomic clause asks that the pending own write W x 1, ordered
        before the RMW by the wmb (dto(Wmb, DRMW) = true), be published at
        the RMW: a thread that sees the RMW's value and then, after an rmb,
        reads x must see W x 1. *)
    Section Prog.
      Variables (a l : bool) (ra : nat).
      Definition wx := Wr 1 0 lx 1 false.
      Definition f1 := Fn 1 1 FST.
      Definition sR := Rd 1 2 ls ra a.
      Definition sW := Wr 1 2 ls 1 l.
      Definition gs (acq : bool) := Rd 2 0 ls 1 acq.
      Definition f2 := Fn 2 1 FLD.
      Definition rx := Rd 2 2 lx 0 false.

      (** With DMB ST and DMB LD (the SeqLock mapping). *)
      Definition mp : cand := {|
        evs := [wx; f1; sR; sW; gs false; f2; rx]; rmw := [(sR, sW)];
        addr := []; data := []; ctrl := [] |}.
      (** Without DMB ST (a plain DW write is not covered by the clause,
          dto(DW, DRMW) = false). *)
      Definition nodmbst : cand := {|
        evs := [wx; sR; sW; gs false; f2; rx]; rmw := [(sR, sW)];
        addr := []; data := []; ctrl := [] |}.
      (** Without DMB LD on the reader side, with get = LDR or LDAR. *)
      Definition nodmbld (acq : bool) : cand := {|
        evs := [wx; f1; sR; sW; gs acq; Rd 2 1 lx 0 false]; rmw := [(sR, sW)];
        addr := []; data := []; ctrl := [] |}.
      (** The observer is itself an RMW of s (read 1, write 2; flavour
          [a'], [l']), followed by DMB LD. *)
      Definition rmwobs (a' l' : bool) : cand := {|
        evs := [wx; f1; sR; sW; Rd 2 0 ls 1 a'; Wr 2 0 ls 2 l'; f2; rx];
        rmw := [(sR, sW); (Rd 2 0 ls 1 a', Wr 2 0 ls 2 l')];
        addr := []; data := []; ctrl := [] |}.

      Lemma src_sW (X : cand) w r :
        wf_witness X w -> In r (evs X) -> isR r = true -> sloc r sW = true -> eval r = 1 ->
        (forall u, In u (evs X) -> isW u = true -> sloc u r = true -> eval u = 1 -> u = sW) ->
        rf w sW r.
      Proof.
        intros Hw Hr HR Hl Hv Huniq.
        destruct (read_source X w Hw r Hr HR) as (u & Hu); [rewrite Hv; discriminate |].
        destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hlu & Hvu).
        rewrite (Huniq u Hin Hwu Hlu (eq_trans Hvu Hv)) in Hu. exact Hu.
      Qed.

      Lemma mp_forb v : forbidden v mp.
      Proof.
        intros w Hw (_ & Hext & _).
        assert (Hu : rf w sW (gs false)).
        { apply (src_sW mp); auto; [in_tac |].
          intros u Hin Hwu Hl Hv. pin_src Hin Hwu Hl Hv; reflexivity. }
        apply (cycle4 v mp w wx sW (gs false) rx Hext).
        - apply (ob_dmbst v mp w wx f1 sW); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v mp w (gs false) f2 rx); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.

      Lemma rel_forb v : l = true -> forbidden v nodmbst.
      Proof.
        intros Hl0 w Hw (_ & Hext & _).
        assert (Hu : rf w sW (gs false)).
        { apply (src_sW nodmbst); auto; [in_tac |].
          intros u Hin Hwu Hl Hv. pin_src Hin Hwu Hl Hv; reflexivity. }
        apply (cycle4 v nodmbst w wx sW (gs false) rx Hext).
        - apply ob_rel; [po_tac | exact Hl0].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v nodmbst w (gs false) f2 rx); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.

      Lemma ldar_forb v : forbidden v (nodmbld true).
      Proof.
        intros w Hw (_ & Hext & _).
        assert (Hu : rf w sW (gs true)).
        { apply (src_sW (nodmbld true)); auto; [in_tac |].
          intros u Hin Hwu Hl Hv. pin_src Hin Hwu Hl Hv; reflexivity. }
        apply (cycle4 v (nodmbld true) w wx sW (gs true) (Rd 2 1 lx 0 false) Hext).
        - apply (ob_dmbst v (nodmbld true) w wx f1 sW); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply ob_acq; [reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.

      Lemma rmwobs_forb v a' l' : forbidden v (rmwobs a' l').
      Proof.
        intros w Hw (_ & Hext & _).
        assert (Hu : rf w sW (Rd 2 0 ls 1 a')).
        { apply (src_sW (rmwobs a' l')); auto; [in_tac |].
          intros u Hin Hwu Hl Hv. pin_src Hin Hwu Hl Hv; reflexivity. }
        apply (cycle4 v (rmwobs a' l') w wx sW (Rd 2 0 ls 1 a') rx Hext).
        - apply (ob_dmbst v _ w wx f1 sW); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v _ w (Rd 2 0 ls 1 a') f2 rx); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.
    End Prog.

    (** The SeqLock mapping realizes the clause with any RMW flavour,
        relaxed LDADD/SWP included, and a plain LDR get. *)
    Theorem ac_ldadd_ldr_forbidden v a l ra : forbidden v (mp a l ra).
    Proof. apply mp_forb. Qed.

    (** An RMW observer behaves like the plain get. *)
    Theorem ac_rmw_observer_forbidden v a l ra a' l' : forbidden v (rmwobs a l ra a' l').
    Proof. apply rmwobs_forb. Qed.

    (** Without DMB ST, a release RMW still orders W x 1 (po;[L]). *)
    Theorem ac_nodmbst_rel_forbidden v a ra : forbidden v (nodmbst a true ra).
    Proof. apply rel_forb. reflexivity. Qed.

    (** Without DMB ST and with a relaxed or acquire RMW the outcome is
        allowed.  This matches dto(DW, DRMW) = false. *)
    Theorem ac_nodmbst_allowed v a : allowed v (nodmbst a false 0).
    Proof.
      apply (allowed_of_checkb v (nodmbst a false 0) [] [(sW false, gs false)]
        [sR a 0; sW false; gs false; rx; wx; f2] [sR a 0; sW false; gs false; f2; rx; wx]).
      destruct v, a; exact eq_refl.
    Qed.

    (** The get alone, without DMB LD: allowed with LDR (matches
        dto(DR, DR) = false), forbidden with LDAR ([A];po). *)
    Theorem ac_ldr_nodmbld_allowed v : allowed v (nodmbld false false 0 false).
    Proof.
      apply (allowed_of_checkb v (nodmbld false false 0 false) [] [(sW false, gs false)]
        [sR false 0; sW false; gs false; Rd 2 1 lx 0 false; wx; f1]
        [Rd 2 1 lx 0 false; wx; f1; sR false 0; sW false; gs false]).
      destruct v; exact eq_refl.
    Qed.

    Theorem ac_ldar_nodmbld_forbidden v a l ra : forbidden v (nodmbld a l ra true).
    Proof. apply ldar_forb. Qed.
  End AtomicClause.


  (** *** The version word (task G-3, item 3) *)

  Module VW.
    (** Writer (thread 1): RMW s (read [ra], write 1, flavour [a], [l]);
        optional barrier; W z 1 (STR, or STLR in [vw_stlr]).
        Observer (thread 2): R z = 1; DMB LD; R s = 0.
        The outcome says that the RMW's write to s is not yet visible to a
        thread that has seen a later write of the writer. *)
    Section Prog.
      Variables (a l : bool) (ra : nat).
      Definition sR := Rd 1 0 ls ra a.
      Definition sW := Wr 1 0 ls 1 l.
      Definition rz := Rd 2 0 lz 1 false.
      Definition f2 := Fn 2 1 FLD.
      Definition rs := Rd 2 2 ls 0 false.

      Definition base (mid : list event) (wz : event) (deps : list (event * event)) : cand := {|
        evs := [sR; sW] ++ mid ++ [wz; rz; f2; rs]; rmw := [(sR, sW)];
        addr := []; data := deps; ctrl := [] |}.

      Definition wz1 := Wr 1 1 lz 1 false.
      Definition wz2 := Wr 1 2 lz 1 false.
      Definition vw := base [] wz1 [].
      (** The store of z is data-dependent on the value the RMW returns
          (z := old + 1). *)
      Definition vw_data := base [] wz1 [(sR, wz1)].
      Definition vw_dmbst := base [Fn 1 1 FST] wz2 [].
      Definition vw_dmbsy := base [Fn 1 1 FSY] wz2 [].
      Definition vw_stlr := base [] (Wr 1 1 lz 1 true) [].

      Lemma forb_mid v k : (k = FST \/ k = FSY) -> forbidden v (base [Fn 1 1 k] wz2 []).
      Proof.
        intros Hk w Hw (_ & Hext & _).
        destruct (read_source _ w Hw rz) as (u & Hu); [in_tac | reflexivity | discriminate |].
        destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
        pin_src Hin Hwu Hl Hv.
        apply (cycle4 v _ w sW wz2 rz rs Hext).
        - destruct Hk as [-> | ->].
          + apply (ob_dmbst v _ w sW (Fn 1 1 FST) wz2); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
          + apply (ob_dmbsy v _ w sW (Fn 1 1 FSY) wz2); [po_tac | reflexivity | po_tac].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v _ w rz f2 rs); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.

      Lemma forb_stlr v : forbidden v vw_stlr.
      Proof.
        intros w Hw (_ & Hext & _).
        destruct (read_source _ w Hw rz) as (u & Hu); [in_tac | reflexivity | discriminate |].
        destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
        pin_src Hin Hwu Hl Hv.
        apply (cycle4 v _ w sW (Wr 1 1 lz 1 true) rz rs Hext).
        - apply ob_rel; [po_tac | reflexivity].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v _ w rz f2 rs); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |].
          no_src Hw.
      Qed.
    End Prog.

    (** With a plain STR z after the RMW: allowed for every flavour in
        POPL18 and Cur, SWPAL/LDADDAL included (see the header on the AL
        clause).  In the hypothetical CurSI it stays allowed for the
        relaxed and release flavours (SWP, SWPL, LDADD, LDADDL) and becomes
        forbidden for the acquire flavours ([vw_acq_si_forbidden]). *)
    Theorem vw_allowed v a l : a = false \/ v <> CurSI -> allowed v (vw a l 0).
    Proof.
      intros H.
      apply (allowed_of_checkb v (vw a l 0) [] [(wz1, rz)]
        [sR a 0; rs; sW l; wz1; rz; f2]
        (if a then [sR a 0; wz1; rz; f2; rs; sW l] else [wz1; rz; f2; rs; sR a 0; sW l])).
      destruct v, a, l;
        first [exact eq_refl | exfalso; destruct H as [H | H]; [discriminate H | apply H; reflexivity]].
    Qed.

    (** Even when the store of z depends on the value the RMW returned
        (POPL18 and Cur; forbidden in CurSI, [vw_data_si_forbidden]). *)
    Theorem vw_data_allowed v a l : v <> CurSI -> allowed v (vw_data a l 0).
    Proof.
      intros H.
      apply (allowed_of_checkb v (vw_data a l 0) [] [(wz1, rz)]
        [sR a 0; rs; sW l; wz1; rz; f2] [sR a 0; wz1; rz; f2; rs; sW l]).
      destruct v, a, l; first [exact eq_refl | exfalso; apply H; reflexivity].
    Qed.

    Lemma rz_src (X : cand) w :
      wf_witness X w -> In rz (evs X) ->
      (forall u, In u (evs X) -> isW u = true -> sloc u rz = true -> eval u = 1 -> u = wz1) ->
      rf w wz1 rz.
    Proof.
      intros Hw Hr Huniq.
      destruct (read_source X w Hw rz Hr eq_refl) as (u & Hu); [discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hlu & Hvu).
      rewrite (Huniq u Hin Hwu Hlu Hvu) in Hu. exact Hu.
    Qed.

    (** In CurSI, an acquire RMW (SWPA, SWPAL, LDADDA, LDADDAL) forbids
        the outcome: R s = 0 →fre W s →si R s →[A];po W z 1 →rfe R z = 1
        →dmb.ld R s = 0. *)
    Theorem vw_acq_si_forbidden l ra : forbidden CurSI (vw true l ra).
    Proof.
      intros w Hw (_ & Hext & _).
      assert (Hu : rf w wz1 rz).
      { apply (rz_src (vw true l ra)); auto; [in_tac |]. intros u Hin Hwu Hl Hv. pin_src Hin Hwu Hl Hv; reflexivity. }
      apply (cycle4 CurSI _ w (sR true ra) wz1 rz rs Hext).
      - apply ob_acq; [reflexivity | po_tac].
      - apply ob_rfe; [exact Hu | discriminate].
      - apply (ob_dmbld CurSI _ w rz f2 rs); [reflexivity | po_tac | reflexivity | po_tac].
      - apply (ob_si_fre CurSI _ w rs (sW l)); [reflexivity | | discriminate | left; reflexivity].
        apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |]. no_src Hw.
    Qed.

    (** In CurSI, a data dependency on the RMW's result forbids it for
        every flavour. *)
    Theorem vw_data_si_forbidden a l ra : forbidden CurSI (vw_data a l ra).
    Proof.
      intros w Hw (_ & Hext & _).
      assert (Hu : rf w wz1 rz).
      { apply (rz_src (vw_data a l ra)); auto; [in_tac |]. intros u Hin Hwu Hl Hv. pin_src Hin Hwu Hl Hv; reflexivity. }
      apply (cycle4 CurSI _ w (sR a ra) wz1 rz rs Hext).
      - apply ob_data. left. reflexivity.
      - apply ob_rfe; [exact Hu | discriminate].
      - apply (ob_dmbld CurSI _ w rz f2 rs); [reflexivity | po_tac | reflexivity | po_tac].
      - apply (ob_si_fre CurSI _ w rs (sW l)); [reflexivity | | discriminate | left; reflexivity].
        apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |]. no_src Hw.
    Qed.

    (** A DMB ST (or DMB SY) after the RMW, or a release store of z,
        forbids it, for every flavour. *)
    Theorem vw_dmbst_forbidden v a l ra : forbidden v (vw_dmbst a l ra).
    Proof. apply forb_mid. left. reflexivity. Qed.

    Theorem vw_dmbsy_forbidden v a l ra : forbidden v (vw_dmbsy a l ra).
    Proof. apply forb_mid. right. reflexivity. Qed.

    Theorem vw_stlr_forbidden v a l ra : forbidden v (vw_stlr a l ra).
    Proof. apply forb_stlr. Qed.

    Theorem vw_dmbst_only_external_fails : only_external_fails (vw_dmbst false false 0).
    Proof.
      exists (wit [] [(wz2, rz)]).
      apply (wit_of_checkb_noext (vw_dmbst false false 0) [] [(wz2, rz)]
               [sR false 0; rs; sW false; Fn 1 1 FST; wz2; rz; f2]).
      exact eq_refl.
    Qed.

    (** The SeqLock variant.  Writer (thread 1): write(1,1) = acq (RMW s
        [ra] -> 1, flavour [a1] [l1]); DMB ST; W x 1; W y 1; DMB ST; rel
        (RMW s [rr] -> 2, flavour [a2] [l2]); then zw(1) = W z 1, with or
        without a DMB ST before it.  Reader (thread 2): zr() = 1; DMB LD;
        get_ticket = R s = 1, the odd value written by acq: the reader
        retries.  The DMB LD is stronger than the SeqLock code, which has
        no barrier between zr() and get_ticket. *)
    Section SL.
      Variables (a1 l1 a2 l2 : bool) (ra rr : nat).
      Definition aR := Rd 1 0 ls ra a1.
      Definition aW := Wr 1 0 ls 1 l1.
      Definition g1 := Fn 1 1 FST.
      Definition wx := Wr 1 2 lx 1 false.
      Definition wy := Wr 1 3 ly 1 false.
      Definition g2 := Fn 1 4 FST.
      Definition rR := Rd 1 5 ls rr a2.
      Definition rW := Wr 1 5 ls 2 l2.
      Definition szr := Rd 2 0 lz 1 false.
      Definition g3 := Fn 2 1 FLD.
      Definition sgt := Rd 2 2 ls 1 false.

      Definition sl : cand := {|
        evs := [aR; aW; g1; wx; wy; g2; rR; rW; Wr 1 6 lz 1 false; szr; g3; sgt];
        rmw := [(aR, aW); (rR, rW)]; addr := []; data := []; ctrl := [] |}.

      Definition sl_dmbst : cand := {|
        evs := [aR; aW; g1; wx; wy; g2; rR; rW; Fn 1 6 FST; Wr 1 7 lz 1 false; szr; g3; sgt];
        rmw := [(aR, aW); (rR, rW)]; addr := []; data := []; ctrl := [] |}.

      Lemma sl_forb v : forbidden v sl_dmbst.
      Proof.
        intros w Hw (Hint & Hext & _).
        destruct (read_source _ w Hw szr) as (u & Hu); [in_tac | reflexivity | discriminate |].
        destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
        pin_src Hin Hwu Hl Hv.
        destruct (read_source _ w Hw sgt) as (u' & Hu'); [in_tac | reflexivity | discriminate |].
        destruct (rf_dom Hw _ _ Hu') as (Hin' & _ & Hwu' & _ & Hl' & Hv').
        pin_src Hin' Hwu' Hl' Hv'.
        assert (Hco : co w aW rW).
        { destruct (co_total Hw aW rW) as [H | H];
            [in_tac | in_tac | reflexivity | reflexivity | reflexivity | discriminate | exact H |].
          exfalso. apply (Hint aW).
          apply t_trans with (y := rW); [apply t_step; left; split; [po_tac | reflexivity] |].
          apply t_step. right; right; left. exact H. }
        apply (cycle4 v _ w rW (Wr 1 7 lz 1 false) szr sgt Hext).
        - apply (ob_dmbst v _ w rW (Fn 1 6 FST) (Wr 1 7 lz 1 false));
            [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
        - apply ob_rfe; [exact Hu | discriminate].
        - apply (ob_dmbld v _ w szr g3 sgt); [reflexivity | po_tac | reflexivity | po_tac].
        - apply ob_fre; [| discriminate]. eapply fr_of_rf_co; [exact Hw | in_tac | exact Hu' | exact Hco].
      Qed.
    End SL.

    (** Allowed for every flavour of acq and rel in POPL18 and Cur; in
        CurSI for every rel without acquire semantics (SWPL, LDADDL, SWP,
        LDADD), and forbidden for an acquire rel
        ([vw_seqlock_acq_si_forbidden]). *)
    Theorem vw_seqlock_allowed v a1 l1 a2 l2 : a2 = false \/ v <> CurSI -> allowed v (sl a1 l1 a2 l2 0 1).
    Proof.
      intros H.
      apply (allowed_of_checkb v (sl a1 l1 a2 l2 0 1) [(aW l1, rW l2)]
        [(aW l1, rR a2 1); (aW l1, sgt); (Wr 1 6 lz 1 false, szr)]
        [aR a1 0; aW l1; rR a2 1; sgt; rW l2; g1; wx; wy; g2; Wr 1 6 lz 1 false; szr; g3]
        (if a2 then [aR a1 0; aW l1; g1; wx; wy; g2; rR a2 1; Wr 1 6 lz 1 false; szr; g3; sgt; rW l2]
         else [aR a1 0; aW l1; g1; wx; wy; g2; Wr 1 6 lz 1 false; szr; g3; sgt; rR a2 1; rW l2])).
      destruct v, a1, l1, a2, l2;
        first [exact eq_refl | exfalso; destruct H as [H | H]; [discriminate H | apply H; reflexivity]].
    Qed.

    Theorem vw_seqlock_acq_si_forbidden a1 l1 l2 ra rr : forbidden CurSI (sl a1 l1 true l2 ra rr).
    Proof.
      intros w Hw (Hint & Hext & _).
      destruct (read_source _ w Hw szr) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
      pin_src Hin Hwu Hl Hv.
      destruct (read_source _ w Hw sgt) as (u' & Hu'); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu') as (Hin' & _ & Hwu' & _ & Hl' & Hv').
      pin_src Hin' Hwu' Hl' Hv'.
      assert (Hco : co w (aW l1) (rW l2)).
      { destruct (co_total Hw (aW l1) (rW l2)) as [H | H];
          [in_tac | in_tac | reflexivity | reflexivity | reflexivity | discriminate | exact H |].
        exfalso. apply (Hint (aW l1)).
        apply t_trans with (y := rW l2); [apply t_step; left; split; [po_tac | reflexivity] |].
        apply t_step. right; right; left. exact H. }
      apply (cycle4 CurSI _ w (rR true rr) (Wr 1 6 lz 1 false) szr sgt Hext).
      - apply ob_acq; [reflexivity | po_tac].
      - apply ob_rfe; [exact Hu | discriminate].
      - apply (ob_dmbld CurSI _ w szr g3 sgt); [reflexivity | po_tac | reflexivity | po_tac].
      - apply (ob_si_fre CurSI _ w sgt (rW l2)); [reflexivity | | discriminate | right; left; reflexivity].
        eapply fr_of_rf_co; [exact Hw | in_tac | exact Hu' | exact Hco].
    Qed.

    (** A DMB ST between rel and zw forbids it, for every flavour. *)
    Theorem vw_seqlock_dmbst_forbidden v a1 l1 a2 l2 ra rr : forbidden v (sl_dmbst a1 l1 a2 l2 ra rr).
    Proof. apply sl_forb. Qed.

    Theorem vw_seqlock_dmbst_only_external_fails : only_external_fails (sl_dmbst false false false false 0 1).
    Proof.
      exists (wit [(aW false, rW false)] [(aW false, rR false 1); (aW false, sgt); (Wr 1 7 lz 1 false, szr)]).
      apply (wit_of_checkb_noext (sl_dmbst false false false false 0 1) [(aW false, rW false)]
               [(aW false, rR false 1); (aW false, sgt); (Wr 1 7 lz 1 false, szr)]
               [aR false 0; aW false; rR false 1; sgt; rW false; g1; wx; wy; g2; Fn 1 6 FST;
                Wr 1 7 lz 1 false; szr; g3]).
      exact eq_refl.
    Qed.

    (** The three outcomes whose verdict depends on flag F2: allowed in
        [Cur], forbidden in [CurSI].  (So the [CurSI] refutations are not
        vacuous.) *)
    Corollary vw_acq_flip l : allowed Cur (vw true l 0) /\ forbidden CurSI (vw true l 0).
    Proof. split; [apply vw_allowed; right; discriminate | apply vw_acq_si_forbidden]. Qed.

    Corollary vw_data_flip a l : allowed Cur (vw_data a l 0) /\ forbidden CurSI (vw_data a l 0).
    Proof. split; [apply vw_data_allowed; discriminate | apply vw_data_si_forbidden]. Qed.

    Corollary vw_seqlock_acq_flip a1 l1 l2 :
      allowed Cur (sl a1 l1 true l2 0 1) /\ forbidden CurSI (sl a1 l1 true l2 0 1).
    Proof. split; [apply vw_seqlock_allowed; right; discriminate | apply vw_seqlock_acq_si_forbidden]. Qed.
  End VW.

  (** *** Non-vacuity of the other forbidden outcomes *)

  Theorem rsw_obj_only_external_fails :
    only_external_fails (RSWObj.X false false false false 0 0 0 1 1 2 0 0 [] [] []).
  Proof.
    exists (wit [(RSWObj.aW false 1, RSWObj.rW false 2); (RSWObj.wz1, RSWObj.wz2)]
                [(RSWObj.aW false 1, RSWObj.rR false 1); (RSWObj.wz1, RSWObj.rz1); (RSWObj.wz2, RSWObj.rz2)]).
    apply (wit_of_checkb_noext _ [(RSWObj.aW false 1, RSWObj.rW false 2); (RSWObj.wz1, RSWObj.wz2)]
             [(RSWObj.aW false 1, RSWObj.rR false 1); (RSWObj.wz1, RSWObj.rz1); (RSWObj.wz2, RSWObj.rz2)]
             [RSWObj.gts 0; RSWObj.tts 0; RSWObj.rx 0; RSWObj.ry 0; RSWObj.f1; RSWObj.f2;
              RSWObj.aR false 0; RSWObj.aW false 1; RSWObj.f3; RSWObj.wx; RSWObj.wy; RSWObj.f4;
              RSWObj.rR false 1; RSWObj.rW false 2; RSWObj.wz1; RSWObj.rz1; RSWObj.wz2; RSWObj.rz2]).
    exact eq_refl.
  Qed.

  Theorem mp_only_external_fails : only_external_fails MPBar.mp.
  Proof.
    exists (wit [] [(MPBar.wy, MPBar.ry)]).
    apply (wit_of_checkb_noext MPBar.mp [] [(MPBar.wy, MPBar.ry)]
             [MPBar.rx; MPBar.wx; MPBar.f1; MPBar.wy; MPBar.ry; MPBar.f2]).
    exact eq_refl.
  Qed.

  Theorem ac_only_external_fails : only_external_fails (AtomicClause.mp false false 0).
  Proof.
    exists (wit [] [(AtomicClause.sW false, AtomicClause.gs false)]).
    apply (wit_of_checkb_noext (AtomicClause.mp false false 0) [] [(AtomicClause.sW false, AtomicClause.gs false)]
             [AtomicClause.sR false 0; AtomicClause.sW false; AtomicClause.gs false; AtomicClause.rx;
              AtomicClause.wx; AtomicClause.f1; AtomicClause.f2]).
    exact eq_refl.
  Qed.

  Theorem sb_relacq_only_external_fails : only_external_fails CrossCheck.sb.
  Proof.
    exists (wit [] []).
    apply (wit_of_checkb_noext CrossCheck.sb [] []
             [CrossCheck.sy0; CrossCheck.sx0; CrossCheck.sx; CrossCheck.sy]).
    exact eq_refl.
  Qed.



  (** *** The reader side: real time on a Wait (task G-3.2, finding M-15)

      A client [while (zr() != 1) {}; read()] waits on zr's value, so the
      module semantics invokes read, hence its first underlay call
      get_ticket, after zr's response ([must_precede], F3).  On ARMv8 the
      read's first load (get_ticket's LDR of the version word) is not
      ordered after the load of z: there is no barrier between them, and a
      control dependency orders only later writes ([ctrl; [W]]), not later
      reads (the ISB clause is not in this model; see the header). *)

  Module RTGet.
    (** Writer (thread 1): write(1,1) with acq = SWPA s 0 -> 1, rel = SWPL
        s 1 -> 2, then DMB ST (the R2 mapping of G-3.1), then zw(1).
        Reader (thread 2): zr() = 1, then get_ticket = 0 (LDR, or LDAR if
        [q]).  These are the reviewer's scratch tests. *)
    Definition rt_aR := Rd 1 0 ls 0 true.
    Definition rt_aW := Wr 1 0 ls 1 false.
    Definition rt_rR := Rd 1 5 ls 1 false.
    Definition rt_rW := Wr 1 5 ls 2 true.
    Definition rt_wz := Wr 1 7 lz 1 false.
    Definition rt_zr := Rd 2 0 lz 1 false.
    Definition writer := [rt_aR; rt_aW; Fn 1 1 FST; Wr 1 2 lx 1 false; Wr 1 3 ly 1 false; Fn 1 4 FST;
                          rt_rR; rt_rW; Fn 1 6 FST; rt_wz].

    Definition rt_get (q : bool) : cand := {|
      evs := writer ++ [rt_zr; Rd 2 1 ls 0 q];
      rmw := [(rt_aR, rt_aW); (rt_rR, rt_rW)]; addr := []; data := []; ctrl := [] |}.

    (** A control dependency from the z load to get_ticket (the loop's
        branch, no ISB). *)
    Definition rt_get_ctrl : cand := {|
      evs := writer ++ [rt_zr; Rd 2 1 ls 0 false];
      rmw := [(rt_aR, rt_aW); (rt_rR, rt_rW)]; addr := []; data := [];
      ctrl := [(rt_zr, Rd 2 1 ls 0 false)] |}.

    (** A DMB LD between the z load and get_ticket. *)
    Definition rt_get_dmbld : cand := {|
      evs := writer ++ [rt_zr; Fn 2 1 FLD; Rd 2 2 ls 0 false];
      rmw := [(rt_aR, rt_aW); (rt_rR, rt_rW)]; addr := []; data := []; ctrl := [] |}.

    Definition ord (q : bool) :=
      [Rd 2 1 ls 0 q; rt_aR; rt_aW; Fn 1 1 FST; Wr 1 2 lx 1 false; Wr 1 3 ly 1 false; Fn 1 4 FST;
       rt_rR; rt_rW; Fn 1 6 FST; rt_wz; rt_zr].

    Theorem rt_get_allowed v q : allowed v (rt_get q).
    Proof.
      apply (allowed_of_checkb v (rt_get q) [(rt_aW, rt_rW)] [(rt_aW, rt_rR); (rt_wz, rt_zr)]
        (ord q) (ord q)).
      destruct v, q; exact eq_refl.
    Qed.

    Corollary rt_get_ldr_allowed v : allowed v (rt_get false).
    Proof. apply rt_get_allowed. Qed.

    Corollary rt_get_ldar_allowed v : allowed v (rt_get true).
    Proof. apply rt_get_allowed. Qed.

    Theorem rt_get_ctrl_allowed v : allowed v rt_get_ctrl.
    Proof.
      apply (allowed_of_checkb v rt_get_ctrl [(rt_aW, rt_rW)] [(rt_aW, rt_rR); (rt_wz, rt_zr)]
        (ord false) (ord false)).
      destruct v; exact eq_refl.
    Qed.

    Theorem rt_get_dmbld_forbidden v : forbidden v rt_get_dmbld.
    Proof.
      intros w Hw (_ & Hext & _).
      destruct (read_source _ w Hw rt_zr) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv). pin_src Hin Hwu Hl Hv.
      apply (cycle4 v _ w rt_aW rt_wz rt_zr (Rd 2 2 ls 0 false) Hext).
      - apply (ob_dmbst v _ w rt_aW (Fn 1 1 FST) rt_wz); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
      - apply ob_rfe; [exact Hu | discriminate].
      - apply (ob_dmbld v _ w rt_zr (Fn 2 1 FLD) (Rd 2 2 ls 0 false)); [reflexivity | po_tac | reflexivity | po_tac].
      - apply ob_fre; [| discriminate].
        apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |]. no_src Hw.
    Qed.
  End RTGet.

  (** *** The full SeqLock run behind M-15: MP through the object

      Writer (thread 1), write(1,1); zw(1), with the TicketLock inlined:
      acq = LDADD nxt (+2, read [rn]); spin LDR own (= [rsp]; the loop
      exit is control-dependent on both loads); LDADD own (+1, read [ra]);
      then DMB ST; STR x 1; STR y 1; DMB ST; rel = LDADD own (+1, read
      [rr]); STR z 1.  RMW flavours: [a0 l0] for nxt, [a1 l1] for acq's
      inc, [a2 l2] for rel.
      Reader (thread 2), zr(); read() with one iteration: LDR z = 1;
      [DMB LD] (iff [pro], an rmb at the start of read()); get_ticket =
      LDR own ([gt]); DMB LD; LDR x ([vx]); LDR y ([vy]); DMB LD;
      test_ticket = LDR own ([tt]). *)

  Module MPObj.
    Section Prog.
      Variables (a0 l0 a1 l1 a2 l2 : bool) (rn rsp ra rr : nat) (pro : bool) (gt vx vy tt : nat)
                (ad da ct : list (event * event)).

      Definition nR := Rd 1 0 ln rn a0.
      Definition nW := Wr 1 0 ln (rn + 2) l0.
      Definition sp := Rd 1 1 ls rsp false.
      Definition aR := Rd 1 2 ls ra a1.
      Definition aW := Wr 1 2 ls (S ra) l1.
      Definition g1 := Fn 1 3 FST.
      Definition wx := Wr 1 4 lx 1 false.
      Definition wy := Wr 1 5 ly 1 false.
      Definition g2 := Fn 1 6 FST.
      Definition rR := Rd 1 7 ls rr a2.
      Definition rW := Wr 1 7 ls (S rr) l2.
      Definition wz := Wr 1 8 lz 1 false.
      Definition zr := Rd 2 0 lz 1 false.
      Definition pf := Fn 2 1 FLD.
      Definition gts := Rd 2 2 ls gt false.
      Definition h1 := Fn 2 3 FLD.
      Definition rx := Rd 2 4 lx vx false.
      Definition ry := Rd 2 5 ly vy false.
      Definition h2 := Fn 2 6 FLD.
      Definition tts := Rd 2 7 ls tt false.

      (** The prologue fence, if any, is listed last; [po] is by
          instruction index, so the position in the list is irrelevant. *)
      Definition X : cand := {|
        evs := [nR; nW; sp; aR; aW; g1; wx; wy; g2; rR; rW; wz; zr; gts; h1; rx; ry; h2; tts]
               ++ (if pro then [pf] else []);
        rmw := [(nR, nW); (aR, aW); (rR, rW)];
        addr := ad; data := da; ctrl := ct |}.
    End Prog.

    (** Whatever get_ticket, y and test_ticket return, and with or without
        the prologue: once the reader has seen z = 1, its read of x
        returns 1.  The cycle is W x 1 →bob(DMB ST) W z 1 →rfe R z = 1
        →bob(the DMB LD after get_ticket) R x = 0 →fre W x 1.  This is the
        client-visible outcome of MP through the object (the SeqLock as
        data, z as flag), which the interface also forbids. *)
    Theorem mp_obj_forbidden v a0 l0 a1 l1 a2 l2 rn rsp ra rr pro gt vy tt ad da ct :
      forbidden v (X a0 l0 a1 l1 a2 l2 rn rsp ra rr pro gt 0 vy tt ad da ct).
    Proof.
      intros w Hw (_ & Hext & _).
      destruct (read_source _ w Hw zr) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv).
      destruct pro; pin_src Hin Hwu Hl Hv;
      (apply (cycle4 v _ w wx wz zr (rx 0) Hext);
       [ apply (ob_dmbst v _ w wx g2 wz); [reflexivity | po_tac | reflexivity | po_tac | reflexivity]
       | apply ob_rfe; [exact Hu | discriminate]
       | apply (ob_dmbld v _ w zr h1 (rx 0)); [reflexivity | po_tac | reflexivity | po_tac]
       | apply ob_fre; [| discriminate];
         apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |];
         no_src Hw ]).
    Qed.

    (** With the prologue DMB LD (an rmb at the start of read()), the
        stale get_ticket = 0 is forbidden, for every flavour and value:
        W own (acq) →bob(DMB ST) W z 1 →rfe R z = 1 →bob(prologue DMB LD)
        get_ticket = 0 →fre W own (acq). *)
    Theorem mp_obj_prologue_stale_get_forbidden v a0 l0 a1 l1 a2 l2 rn rsp ra rr vx vy tt ad da ct :
      forbidden v (X a0 l0 a1 l1 a2 l2 rn rsp ra rr true 0 vx vy tt ad da ct).
    Proof.
      intros w Hw (_ & Hext & _).
      destruct (read_source _ w Hw zr) as (u & Hu); [in_tac | reflexivity | discriminate |].
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hv). pin_src Hin Hwu Hl Hv.
      apply (cycle4 v _ w (aW l1 ra) wz zr (gts 0) Hext).
      - apply (ob_dmbst v _ w (aW l1 ra) g1 wz); [reflexivity | po_tac | reflexivity | po_tac | reflexivity].
      - apply ob_rfe; [exact Hu | discriminate].
      - apply (ob_dmbld v _ w zr pf (gts 0)); [reflexivity | po_tac | reflexivity | po_tac].
      - apply ob_fre; [| discriminate].
        apply fr_no_source; [in_tac | in_tac | reflexivity | reflexivity | reflexivity |]. no_src Hw.
    Qed.

    (** The loop exit is control-dependent on the nxt and spin loads; so
        is everything after it. *)
    Definition spin_ctrl (a1 l1 a2 l2 : bool) : list (event * event) :=
      flat_map (fun e => [(nR false 0, e); (sp 0, e)])
        [aR a1 0; aW l1 0; g1; wx; wy; g2; rR a2 1; rW l2 1; wz].

    (** The run: acq reads own = 0, rel reads own = 1, relaxed LDADD on
        nxt; after zr() = 1, get_ticket = 0 (the value before acq), the data
        reads return (1,1), test_ticket = 2, so the read retries. *)
    Definition Xs (a1 l1 a2 l2 : bool) : cand :=
      X false false a1 l1 a2 l2 0 0 0 1 false 0 1 1 2 [] [] (spin_ctrl a1 l1 a2 l2).

    (** The M-15 outcome inside a full run, without the prologue: allowed
        for every flavour of acq's inc and of rel. *)
    Theorem mp_obj_stale_get_allowed v a1 l1 a2 l2 : allowed v (Xs a1 l1 a2 l2).
    Proof.
      apply (allowed_of_checkb v (Xs a1 l1 a2 l2) [(aW l1 0, rW l2 1)]
        [(aW l1 0, rR a2 1); (rW l2 1, tts 2); (wz, zr); (wx, rx 1); (wy, ry 1)]
        [nR false 0; nW false 0; sp 0; gts 0; aR a1 0; aW l1 0; rR a2 1; rW l2 1; tts 2;
         g1; wx; wy; g2; wz; zr; h1; rx 1; ry 1; h2]
        [gts 0; nR false 0; nW false 0; sp 0; aR a1 0; aW l1 0; g1; wx; wy; g2;
         rR a2 1; rW l2 1; wz; zr; h1; rx 1; ry 1; h2; tts 2]).
      destruct v, a1, l1, a2, l2; exact eq_refl.
    Qed.
  End MPObj.

  (** *** Non-vacuity with well-formed candidates (finding m-42)

      [nonvacuous X]: the candidate is well formed and some well-formed
      witness satisfies INTERNAL and ATOMIC, so EXTERNAL alone excludes the
      outcome.  The earlier [only_external_fails] lemmas are unchanged; the
      lemmas below add [wf_cand]. *)

  Definition nonvacuous (X : cand) : Prop := wf_cand X /\ only_external_fails X.

  Theorem rsw_obj_nonvacuous :
    nonvacuous (RSWObj.X false false false false 0 0 0 1 1 2 0 0 [] [] []).
  Proof. split; [apply wf_cand_of_wfcb; exact eq_refl | exact rsw_obj_only_external_fails]. Qed.

  Theorem rsw_obj_core_nonvacuous : nonvacuous (RSWObjCore.X 0 false [] [] []).
  Proof. split; [apply wf_cand_of_wfcb; exact eq_refl | exact RSWObjCore.rsw_obj_core_not_vacuous]. Qed.

  Theorem mp_nonvacuous : nonvacuous MPBar.mp.
  Proof. split; [apply wf_cand_of_wfcb; exact eq_refl | exact mp_only_external_fails]. Qed.

  Theorem ac_nonvacuous : nonvacuous (AtomicClause.mp false false 0).
  Proof. split; [apply wf_cand_of_wfcb; exact eq_refl | exact ac_only_external_fails]. Qed.

  Theorem sb_relacq_nonvacuous : nonvacuous CrossCheck.sb.
  Proof. split; [apply wf_cand_of_wfcb; exact eq_refl | exact sb_relacq_only_external_fails]. Qed.

  Theorem vw_dmbst_nonvacuous : nonvacuous (VW.vw_dmbst false false 0).
  Proof. split; [apply wf_cand_of_wfcb; exact eq_refl | exact VW.vw_dmbst_only_external_fails]. Qed.

  Theorem vw_seqlock_dmbst_nonvacuous : nonvacuous (VW.sl_dmbst false false false false 0 1).
  Proof. split; [apply wf_cand_of_wfcb; exact eq_refl | exact VW.vw_seqlock_dmbst_only_external_fails]. Qed.

  Theorem rt_get_dmbld_nonvacuous : nonvacuous RTGet.rt_get_dmbld.
  Proof.
    split; [apply wf_cand_of_wfcb; exact eq_refl |].
    exists (wit [(RTGet.rt_aW, RTGet.rt_rW)] [(RTGet.rt_aW, RTGet.rt_rR); (RTGet.rt_wz, RTGet.rt_zr)]).
    apply (wit_of_checkb_noext RTGet.rt_get_dmbld [(RTGet.rt_aW, RTGet.rt_rW)]
             [(RTGet.rt_aW, RTGet.rt_rR); (RTGet.rt_wz, RTGet.rt_zr)]
             [Rd 2 2 ls 0 false; RTGet.rt_aR; RTGet.rt_aW; RTGet.rt_rR; RTGet.rt_rW; RTGet.rt_wz;
              RTGet.rt_zr; Fn 1 1 FST; Wr 1 2 lx 1 false; Wr 1 3 ly 1 false; Fn 1 4 FST; Fn 1 6 FST;
              Fn 2 1 FLD]).
    exact eq_refl.
  Qed.

  (** The client-visible MP outcome (read() = (0,0) after zr() = 1), plain
      flavours, no prologue, the loop's control dependencies. *)
  Theorem mp_obj_nonvacuous :
    nonvacuous (MPObj.X false false false false false false 0 0 0 1 false 0 0 0 0 [] [] (MPObj.spin_ctrl false false false false)).
  Proof.
    split; [apply wf_cand_of_wfcb; exact eq_refl |].
    exists (wit [(MPObj.aW false 0, MPObj.rW false 1)]
                [(MPObj.aW false 0, MPObj.rR false 1); (MPObj.wz, MPObj.zr)]).
    apply (wit_of_checkb_noext _ [(MPObj.aW false 0, MPObj.rW false 1)]
             [(MPObj.aW false 0, MPObj.rR false 1); (MPObj.wz, MPObj.zr)]
             [MPObj.nR false 0; MPObj.nW false 0; MPObj.sp 0; MPObj.gts 0; MPObj.tts 0;
              MPObj.aR false 0; MPObj.aW false 0; MPObj.rR false 1; MPObj.rW false 1;
              MPObj.rx 0; MPObj.ry 0; MPObj.g1; MPObj.wx; MPObj.wy; MPObj.g2; MPObj.wz; MPObj.zr;
              MPObj.h1; MPObj.h2]).
    exact eq_refl.
  Qed.

  (** The prologue variant of the stale get_ticket. *)
  Theorem mp_obj_prologue_stale_get_nonvacuous :
    nonvacuous (MPObj.X false false false false false false 0 0 0 1 true 0 1 1 2 [] [] (MPObj.spin_ctrl false false false false)).
  Proof.
    split; [apply wf_cand_of_wfcb; exact eq_refl |].
    exists (wit [(MPObj.aW false 0, MPObj.rW false 1)]
                [(MPObj.aW false 0, MPObj.rR false 1); (MPObj.rW false 1, MPObj.tts 2);
                 (MPObj.wz, MPObj.zr); (MPObj.wx, MPObj.rx 1); (MPObj.wy, MPObj.ry 1)]).
    apply (wit_of_checkb_noext _ [(MPObj.aW false 0, MPObj.rW false 1)]
             [(MPObj.aW false 0, MPObj.rR false 1); (MPObj.rW false 1, MPObj.tts 2);
              (MPObj.wz, MPObj.zr); (MPObj.wx, MPObj.rx 1); (MPObj.wy, MPObj.ry 1)]
             [MPObj.nR false 0; MPObj.nW false 0; MPObj.sp 0; MPObj.gts 0; MPObj.aR false 0;
              MPObj.aW false 0; MPObj.rR false 1; MPObj.rW false 1; MPObj.tts 2;
              MPObj.g1; MPObj.wx; MPObj.wy; MPObj.g2; MPObj.wz; MPObj.zr; MPObj.pf; MPObj.h1;
              MPObj.rx 1; MPObj.ry 1; MPObj.h2]).
    exact eq_refl.
  Qed.

  (** ** Part 7. The same shape in the redesign's buffered memory

      The core of RSW through the object, as a candidate of the buffered
      memory under the table-induced semi-independence of
      [memory/TableBarrier.v], on its abstract table [NonVacuity.ato]
      (W→Wmb, Wmb→W, Wmb→Wmb, R→Rmb, Rmb→R, Rmb→Rmb; this is
      [WindowTable.dto] restricted to DR, DW, Rmb, Wmb).  rmb and wmb are the
      ghost accesses of that file. *)

  Module CellTab.
    Import Cell Decl TableBarrier TableBarrier.NonVacuity.

    (** T1: R z = 1; W z 2; R z = 2; rmb; R x = 0 ‖ T2: W x 1; wmb; W z 1,
        with x = Dat 0 and z = Dat 2; handles follow program order. *)
    Definition ops : list (block AC) :=
      [ @BR AC 1%positive 0 (Dat 2) tt 1;   (* T1: R z = 1 *)
        @BW AC 1%positive 1 (Dat 2) 2 tt;   (* T1: W z 2 *)
        @BR AC 1%positive 2 (Dat 2) tt 2;   (* T1: R z = 2 *)
        @BR AC 1%positive 3 GBr tt 0;       (* T1: rmb *)
        @BR AC 1%positive 4 (Dat 0) tt 0;   (* T1: R x = 0 *)
        @BW AC 2%positive 0 (Dat 0) 1 tt;   (* T2: W x 1 *)
        @BW AC 2%positive 1 GBw 0 tt;       (* T2: wmb *)
        @BW AC 2%positive 2 (Dat 2) 1 tt ]. (* T2: W z 1 *)

    Definition Xt : cand AC := cand_of ops.

    Lemma Xt_wf : wf_cand Xt.
    Proof.
      constructor; cbn.
      - intros b Hb. repeat (destruct Hb as [<- | Hb]; [cbn; tauto |]). destruct Hb.
      - repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
      - intros a b (Ha & Hb & Ht & _). auto.
      - intros a (_ & _ & _ & H). lia.
      - intros a b c (Ha & Hb & Ht1 & H1) (_ & Hc & Ht2 & H2). repeat split; auto; [congruence | lia].
      - intros a b Ha Hb Ht Hne.
        assert (Hh : b_handle a <> b_handle b)
          by (intros Heq; repeat (destruct Ha as [<- | Ha]; [ repeat (destruct Hb as [<- | Hb];
                [ cbn in Ht, Heq; first [discriminate Ht | discriminate Heq | apply Hne; reflexivity] |]);
                destruct Hb |]); destruct Ha).
        destruct (lt_dec (b_handle a) (b_handle b)) as [Hlt | Hge];
          [left; repeat split; auto | right; repeat split; auto; lia].
      - intros a b (_ & _ & _ & H) _ _. exact H.
    Qed.

    Local Ltac cpo_tac := split; [cbn; tauto | split; [cbn; tauto | split; [reflexivity | cbn; lia]]].

    (** For every admissible [pre] and every well-formed witness, (D2)
        fails: W x 1 →ppo⁺ W z 1 (through wmb) →rfe R z = 1 →ppo R x = 0
        (through rmb) →rb W x 1.  The same-location chain R z = 1 → W z 2 →
        R z = 2 is not used. *)
    Theorem rsw_obj_core_tab_inconsistent (pre : relation (block AC)) (w : witness AC) :
      admissible Xt AI pre -> wf_witness Xt w -> ~ D2 Xt AI w pre.
    Proof.
      intros Hadm Hw HD2.
      assert (Hsrc : ~ ~ exists u, rf w u (@BR AC 1%positive 0 (Dat 2) tt 1)).
      { intros Hn.
        assert (H0 : b_val (@BR AC 1%positive 0 (Dat 2) tt 1) = 0).
        { apply (rf_init Hw); [cbn; tauto | exact I |]. intros u Hu. apply Hn. eauto. }
        discriminate H0. }
      apply Hsrc. intros (u & Hu).
      destruct (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hloc & Hval).
      assert (Hu1 : u = @BW AC 2%positive 2 (Dat 2) 1 tt).
      { cbn in Hin. repeat (destruct Hin as [<- | Hin];
          [cbn in Hwu, Hloc, Hval; first [reflexivity | discriminate Hloc | discriminate Hval | contradiction Hwu] |]).
        destruct Hin. }
      subst u.
      destruct (ppo_wmb_WW Nat.eq_dec umodes ato adata cWmb cRmb Xt pre
                  (@BW AC 2%positive 0 (Dat 0) 1 tt) (@BW AC 2%positive 2 (Dat 2) 1 tt) 2%positive 1 0 tt)
        as (_ & _ & Hww); [cpo_tac | cpo_tac | exact I | exact I | reflexivity | reflexivity |].
      destruct (ppo_rmb_RR Nat.eq_dec umodes ato adata cWmb cRmb Xt pre
                  (@BR AC 1%positive 0 (Dat 2) tt 1) (@BR AC 1%positive 4 (Dat 0) tt 0) 1%positive 3 tt 0)
        as (_ & _ & Hrr); [exact (proj1 Hadm) | cpo_tac | cpo_tac | exact I | reflexivity | reflexivity |].
      apply (HD2 (@BW AC 2%positive 0 (Dat 0) 1 tt)).
      eapply t_trans; [exact (Hww w) |].
      eapply t_trans; [apply t_step; left; left; right; split; [exact Hu | discriminate] |].
      eapply t_trans; [apply t_step; left; left; left; exact Hrr |].
      apply t_step. right.
      split; [cbn; tauto | split; [cbn; tauto | split; [exact I | split; [exact I | split; [reflexivity |]]]]].
      intros u0 Hu0. exfalso.
      destruct (rf_dom Hw _ _ Hu0) as (Hin0 & _ & Hw0 & _ & Hl0 & Hv0).
      cbn in Hin0. repeat (destruct Hin0 as [<- | Hin0];
        [cbn in Hw0, Hl0, Hv0; first [discriminate Hl0 | discriminate Hv0 | contradiction Hw0] |]).
      destruct Hin0.
    Qed.

    (** Hence no history of [ν_{I_tab}] presents the candidate and respects
        an admissible [pre] (through [declarative_tab]; uses [classic]). *)
    Theorem rsw_obj_core_tab_forbidden (pre : relation (block AC)) :
      admissible Xt AI pre -> ~ exists s, nu AI s /\ presents s Xt /\ respects s pre.
    Proof.
      intros Hadm Hs.
      apply (declarative_tab ato acat Xt Xt_wf pre Hadm) in Hs.
      destruct Hs as (w & Hw & _ & HD2).
      exact (rsw_obj_core_tab_inconsistent pre w Hadm Hw HD2).
    Qed.
  End CellTab.
End ARMBar.
