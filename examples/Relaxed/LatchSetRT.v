(** * LatchSetRT: LatchSet over buffered cells refutes an atomic set specification (CE1, CE2)

    Task LS-0a.1 of the LatchSet plan (.rocq-review/latchset-plan.md §5,
    phase LS-0a), after the design review
    (.rocq-review/latchset-design-review.md, B-5).  This is an evidence
    file.  It records in the kernel why the LatchSet of the paper cannot
    export an atomic set specification when it is built on the buffered
    cells of memory/.  It does not define the buffered set ν_BS that the
    author chose on 2026-10-13 (task LS-1), and nothing here depends on
    that choice.  No existing file is changed.

    The object.  The sorted-array latch set of
    async-ccal/drafts/relaxed-lin/Claude outputs/litmus-check/
    tests_latch_set.py (base model tests_latch.py), at capacity 1.
    Locations: seq; copy 0 = n0 (size), a00; copy 1 = n1, a10.  The
    barriers are the ghost locations of memory/TableBarrier.v: a wmb is a
    write of [GBw], an rmb a read of [GBr].  [insert(k)] has a single
    writer and uses the form LD-0 (a′) adopted in plan §5: the writer reads
    seq and copy 0 only, then writes both copies from the computed array.
<<
    insert(k):   wmb; s <- seq; seq := s+1; wmb;
                 m <- n0; (reads of a0_i, i < m); writes of a0_i; n0 := m+1;
                 wmb; seq := s+2; wmb;
                 writes of a1_i; n1 := m+1
    contains(k): s <- seq; m <- n_(s&1); reads of a_(s&1)_i, i < m; rmb;
                 retry if seq <> s; return (k found)
>>
    [insert] ends with plain stores, and nothing drains them.  In memory/
    a plain write responds when it is issued (it enters the buffer); this
    is the convention of Cell.v and of the buffered-cell redesign
    (research-intent §8).  So a returned insert can still be unpublished.
    The address dependency of the scan on [s] is not modelled at this
    level.  At the cell level a dependency only constrains the issue
    order, and every history below is issued in full program order
    ([ce1_underlay_allowed], [ce2_underlay_allowed]).

    Part 0, generic checkers (any configuration).
    - [fifochk]: [tchk] at the full table, i.e. at every flush no pending
      write of the thread has a smaller handle.  [contract_of_fifochk],
      [V_of_fifochk]: a trace that passes it satisfies the contract of
      every relation, and is in [V Ir] for every [Ir] if it also passes
      [vchk].
    - [vchk_complete]: [vchk] is complete for the [VBuf] part of [V].
      [not_V_of_vchk]: [vchk s = false] refutes [V Ir s] for every [Ir].
    - [wochk], [wr_order_of_chk]: each thread issues its writes in
      increasing handle order (the side condition of [TSO.V_up]).

    Part 1, configuration and table.
    - [LC = tab_cfg ldec TSO_modes]: data locations [Dat ℓ], with ℓ in
      [LLoc], and the ghosts [GBw], [GBr].  The modes are [TSO_modes] so that
      the same traces are traces of [TSO_cfg] (Part 3).  [I_tab] does not
      consult modes.
    - Categories [lcat] ([TableBarrier.bcat]): data reads DR, data writes
      DW, a write of Bw Wmb, a read of Br Rmb.  These are the cell kinds of
      plan §5.  On them the checker's LKMem agrees with [dto] up to the
      Wmb–Wmb and Rmb–Rmb entries (design review M-22).
    - [LI rc := I_tab (WindowTable.dto rc) lcat], for both profiles [rc].
      This is the table [dto] itself, not the abstract table [ato] of
      [TableBarrier.NonVacuity].  [latch_table] evaluates [dto rc] on all
      sixteen pairs of {DR, DW, Wmb, Rmb} for both [rc].  Exactly W→Wmb,
      Wmb→W, Wmb→Wmb, R→Rmb, Rmb→R and Rmb→Rmb are ordered.  This is [ato],
      which TableBarrier checked only in a scratch session.

    Part 2, the cell traces.  Writer T1 = thread 1, reader T3 = thread 3.
    Handles follow program order; flush handles (100..109) are arbitrary.
    - [ins2]: T1's insert(2) into the empty set, 12 blocks:
      wmb; R seq 0; W seq 1; wmb; R n0 0; W a00 2; W n0 1; wmb; W seq 2;
      wmb; W a10 2; W n1 1.
    - [own_contains]: T1's contains(2): R seq 2; R n0 1; R a00 2; rmb;
      R seq 2, so it returns true.  The data reads are forwarded
      ([ce2_T1_reads_forwarded]).
    - [other_contains]: T3's contains(2): R seq 0; R n0 0; rmb; R seq 0, so
      it returns false.  The reads come from memory ([ce1_T3_reads_memory]).
    - [flushes]: T1's ten flushes, in program order, at the end.
    - CE1 = [ce1_cells] = ins2 ++ other_contains ++ flushes.
      CE2 = [ce2_cells] = ins2 ++ own_contains ++ other_contains ++ flushes.
    Results.
    - [ce1_cells_V], [ce2_cells_V]: in [V (LI rc)] for every [rc].
      [ce1_cells_V_any], [ce2_cells_V_any]: in [V Ir] for every relation
      [Ir], because the flushes are FIFO.  So no table, and no other
      choice of semi-independence relation, excludes CE1 or CE2 from this
      memory.  This agrees with TableBarrier's scope note (a): the memory
      has no draining fence.
    - [ce1_underlay_allowed], [ce2_underlay_allowed]: the flush-free
      histories are in [ν (LI rc)], present their own candidate, and
      respect all of program order.  [ce1_hist_nu_any], [ce2_hist_nu_any]:
      in [ν Ir] for every [Ir].
    - [ce1_hist_separated], [ce2_hist_separated]: in the history every
      block of the insert (and, in CE2, of T1's own contains) precedes
      every block of T3's contains.
    - [ins2_all_pending]: when T3 starts, all ten writes of the insert are
      still pending.
    - Controls.  [ce1_flushed_first_not_V]: with the flushes before T3's
      contains, the trace is in [V Ir] for no [Ir]; T3 cannot read seq = 0.
      [ce1_flushed_true_V]: after the flushes, T3's contains(2) = true is
      in [V Ir] for every [Ir].  [ce2_writer_must_forward]: directly after
      [ins2], T1's read of seq cannot return the old value 0, for any [Ir]
      (one prefix only; no general statement about the writer).

    Part 3, the x86-TSO machine (memory/TSO.v: the machine of Owens, Sarkar
    and Sewell, read/write fragment).
    - [ce1_x86]: [ce1_x86_run], the erasure of CE1 without the ghost
      accesses ([ce1_x86_run_eq]), is a trace of the machine.  On x86, rmb
      and wmb are compiler barriers, and LatchSet has no locked
      instruction, so the read/write fragment covers the code.
      [ce2_x86]: the same for CE2.  [ce1_cells_x86]: the trace with the
      ghost accesses is a machine trace as well.  There the ghosts are
      plain accesses: stores to Bw, which nothing reads, and loads of Br,
      which nothing writes.
    - In [ce1_x86_run], T3's three loads come after all of T1's stores in
      the machine's step order, and they read 0.  This is the real-time
      content of CE1.  A litmus test cannot express it: the final outcome
      alone (T3 reads all zeros) is allowed even under SC, by running T3
      first.  So no herd7 test is given.

    Part 4, the overlay.  The set signature [SetE indep] (operations
    [Ins k : unit] and [Mem k : bool], handles [nat], mode [Local]) for any
    semi-independence relation [indep].  The spec is the atomic grow-only
    set [nuset_from S0] from an initial set [S0], with [nuset = nuset_from
    []]: [Ins k] adds [k], and [Mem k] answers whether [k] is in the set.
    - [rt_ins_mem_false_not_rel_lin]: for any trace and selector, if an
      [Ins x] responds before a [Mem x] that returns false is invoked, the
      trace is not relaxed linearizable w.r.t. [nuset_from S0], for every
      [indep] and every [S0].  Only the real-time clause of [rhb] is used.
      The mechanism is the one of Q6-2 ([SeqLockQ6.rt_iteration_not_rel_lin]):
      a store buffer whose writes respond at issue is not linearizable to
      an atomic object.  What is specific to LatchSet is the cell-level
      run of Part 2: the latch protocol does not detect the stale state,
      because T3 reads seq = 0 on both sides of its rmb and accepts.
    - [ce1_ov b]: T1 inv/res insert(2), then T3 inv/res contains(2) = b.
      [ce1_overlay_not_rel_lin]: [forall indep, ~ rel_lin Some (ce1_ov indep
      false) indep (nuset indep)]; [ce1_overlay_not_rel_lin_from]: the same
      for every initial set.
    - [ce2_ov b]: T1 inv/res insert(2), T1 inv/res contains(2) = true, then
      T3 inv/res contains(2) = b.  [ce2_overlay_not_rel_lin(_from)]: the
      same refutation.  Against an atomic set CE2 adds nothing to CE1.  Its
      refutation uses the same real-time edge (T1's insert before T3's
      contains), and T1's own contains = true is consistent with [nuset].
      CE2 matters for the replacement spec instead.  It is the object-level
      SB+rfi: the writer sees its insert by forwarding, while another
      thread does not.  A buffered set in which every thread, the writer
      included, sees only published inserts would reject CE2.  T1's
      contains = true forces the insert's publication point before it, and
      T3's later contains = false forces it after.  This is why ν_BS lets
      the writer see its own issued inserts.  That argument is a
      derivation; no such spec is defined here (task LS-1).
    - Controls: [ce1_ctl_rel_lin], [ce2_ctl_rel_lin]: with T3's
      contains(2) = true, both overlay traces are relaxed linearizable
      w.r.t. [nuset], for every [indep].

    K / S / P / R.
    - K (kernel-checked; Print Assumptions: closed for every result).
      - Cell level: CE1 and CE2 are in [V] of the table-induced buffered
        memory at [dto rc], for both [rc], and in fact for every
        semi-independence relation.  Their histories are in [ν] and
        respect all of program order.  T3's reads are served from memory
        while all of the insert's writes are pending; T1's own reads are
        forwarded.  The negative and positive controls above hold.
      - x86: the ghost-free erasures of CE1 and CE2 are traces of the
        x86-TSO machine of memory/TSO.v.
      - Overlay: the CE1 and CE2 overlay traces are not relaxed
        linearizable w.r.t. the atomic grow-only set, for every
        semi-independence relation and every initial set.  With T3's
        answer true, both are.
    - Derivation (not kernel-checked).
      - Module realizability.  A futures module M_L for this code, over a
        memory whose plain writes respond at issue, can produce the
        overlay trace [ce1_ov false] (resp. [ce2_ov false]) from an
        underlay whose history is [ce1_hist] (resp. [ce2_hist]).  The
        insert responds after its last cell call responds
        ([ce1_hist_separated]), and T3 then invokes contains.  M_L does
        not exist yet (plan LS-2); the module-level CE1/CE2 are task LS-6.
        The link from [ν_{I_tab}] to [rel_lin] of a module's underlay
        trace (task G-1 in the buffered-cell plan) is not available either.
      - That [ce1_x86_run] is an execution of the compiled LatchSet code:
        program points are not formalized (as in TableBarrierTSO, "What
        this does not give").
    - S (scope of the statements).  One small instance: capacity 1, key 2,
      one insert into the empty set (memory/ starts at 0, so the
      checker's initial set {1,3} would need a setup prefix, m-69), one
      writer.  The flushes come last.  The overlay traces are complete and
      sequential; [rel_lin] is for complete traces.  The cell-level
      results are for every [rc] and every relation, the overlay
      refutations for every [indep] and every initial set.
    - P (paper).  intro.tex:106: "We verify LatchSet, a latched set based on
      the Linux kernel's latch technique".  overview.tex:316 (the LatchSet
      proof box of fig:latch-set): "Atomic set behavior + relaxed
      ordering".  overview.tex:333: each component "must supply the atomic
      update and observation interface required by the collect loop".
      overview.tex:335: "Each LatchSet component exports an atomic set
      specification".  Line numbers are those of the working copy of
      2026-10-13.  Consequence: for this code over buffered cells, with
      issue-time write responses, an atomic set specification is not
      reachable.  CE1 is admitted by the buffered memory (for every table)
      and by the x86-TSO machine, and its overlay is not relaxed
      linearizable to the atomic grow-only set under any semi-independence
      relation; the module step in between is the derivation above.  So
      the exported spec must change, and the author decided on 2026-10-13
      (research-intent §8) that it becomes the buffered set ν_BS.  The
      paper's "atomic set" wording has to change accordingly.  The other
      repairs listed in B-5 are a draining operation at the end of insert
      (a code and memory/ change) and register cells (not x86-grounded,
      Q6-2).
    - R (reviewers).  Reviewer A, popl2027-reviews.md:69-81: SB with own
      reads ("whose annotated weak behavior is allowed by TSO").  CE2 is
      its object-level form through LatchSet.  The response's revision
      plan, popl2027-reviews.md:385: "Distinguish strict MCA, oMCA, and
      store forwarding".  Response A1, popl2027-reviews.md:401: oMCA
      "permits the issuing thread to observe its own write before that
      write is published to other threads", which is CE2's writer-local
      view.  Response A2 (:437) restricted the scope to MCA; the author's
      2026-10-13 decision puts oMCA in scope instead.  Together with the
      module step (a derivation), CE1 shows what that decision costs at
      the object level: LatchSet over this memory is not relaxed
      linearizable to an atomic set, so its exported spec must expose
      buffering.
    - Not claimed.  Nothing here is about ARMv8; the ARM track is LS-A.
      Nothing here is about the broken variants of the checker or about
      the address dependency (tasks LS-2, LS-4).

    Trusted computation.  The finite checks ([tchk], [fifochk], [vchk],
    [pochk], [wochk], [latch_table], the state and pending-list facts) are
    closed by [exact eq_refl], [reflexivity] or [repeat split], i.e. by
    the kernel's conversion.  This file calls no [vm_compute] and no
    [lia]; lemmas reused from memory/ were proved with [lia], whose proof
    terms carry a VM cast, as elsewhere in the development.  The
    [WindowTable.latch_*] lemmas (proved with [vm_compute]) are not used.

    Assumptions.  Every result is closed under the global context. *)

From Stdlib Require Import List Arith PArith Bool.
From Stdlib Require Import Relations.Relation_Definitions.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.TSO.
Require Import memory.TableBarrier.
Require Import memory.TableBarrierTSO.
Require Import examples.Relaxed.WindowTable.

Import ListNotations.

Module LatchSetRT.
  Import Cell Cell.Instances Decl TableBarrier.
  Module WT := WindowTable.WindowTable.

  (** ** Part 0. Generic checkers, for any configuration *)

  Section Generic.
    Context {C : Cfg}.

    (** The full table orders everything, so [I_tab fto ucat] is empty. *)
    Definition fto (c d : unit) : bool := true.
    Definition ucat (m : cell_op C) : unit := tt.

    Lemma I_tab_full_empty (m m' : cell_op C) : ~ I_tab fto ucat m m'.
    Proof. intros [_ H]. discriminate H. Qed.

    (** FIFO publication: at every flush, no pending write of the thread
        has a smaller handle than the published one. *)
    Definition fifochk (s : trace C) : bool := forallb (tchk fto ucat s) (seq 0 (length s)).

    (** A FIFO trace satisfies the contract of every relation. *)
    Lemma contract_of_fifochk (s : trace C) : fifochk s = true -> forall Ir, contract Ir s.
    Proof.
      intros H Ir. apply (TableBarrierTSO.contract_mono (I_tab fto ucat)).
      - intros m m' Hm. exfalso. exact (I_tab_full_empty m m' Hm).
      - apply contract_of_tchk, H.
    Qed.

    Lemma V_of_fifochk (s : trace C) : fifochk s = true -> vchk s = true -> forall Ir, V Ir s.
    Proof. intros H1 H2 Ir. split; [apply contract_of_fifochk, H1 | apply VBuf_of_vchk, H2]. Qed.

    (** Each thread issues its writes in increasing handle order. *)
    Definition wochk (s : trace C) : bool := idxchk fto ucat s (fun k => k).

    Lemma wr_order_of_chk (s : trace C) : wochk s = true ->
      forall i j a b, i < j -> nth_error s i = Some a -> nth_error s j = Some b ->
        is_write a -> is_write b -> b_tid a = b_tid b -> b_handle a < b_handle b.
    Proof.
      intros H i j a b Hij Ha Hb Wa Wb Ht.
      apply (idx_of_chk fto ucat s (fun k => k) H i j a b Hij Ha Hb Wa Wb Ht (I_tab_full_empty _ _)).
    Qed.

    (** [vchk] is complete: a trace whose cell projections are all paths
        of [Buf_x] passes it.  So [vchk s = false] refutes [V] for every
        relation. *)
    Lemma enabledb_complete (b : block C) st : enabled b st -> enabledb b st = true.
    Proof.
      destruct b as [t h x v a | t h x a v | t h x]; cbn; [reflexivity | |].
      - intros [[Hne Hv] | [Hnil Hv]]; subst v.
        + destruct (cP st t) as [| n l] eqn:E; [congruence |]. apply Nat.eqb_refl.
        + rewrite Hnil. apply Nat.eqb_refl.
      - destruct (cP st t); [congruence | reflexivity].
    Qed.

    Lemma vchk_complete (s : trace C) : (forall x, VBuf x (proj x s)) -> vchk s = true.
    Proof.
      intros H. unfold vchk. apply forallb_forall. intros i _.
      destruct (nth_error s i) as [b |] eqn:E; [| reflexivity].
      apply enabledb_complete. exact (proj1 (VBuf_proj_iff (b_loc b) s) (H (b_loc b)) i b E eq_refl).
    Qed.

    Lemma not_V_of_vchk (s : trace C) : vchk s = false -> forall Ir, ~ V Ir s.
    Proof. intros H Ir [_ Hb]. rewrite (vchk_complete s Hb) in H. discriminate H. Qed.
  End Generic.

  (** ** Part 1. Locations, categories, and the table *)

  Inductive LLoc : Type := Lseq | Ln0 | La00 | Ln1 | La10.

  Definition ldec (x y : LLoc) : {x = y} + {x <> y}.
  Proof. decide equality. Defined.

  Abbreviation LC := (tab_cfg ldec TSO_modes).

  (** Data reads are [DR], data writes [DW]; a write of the ghost [Bw] is
      a [Wmb], a read of the ghost [Br] an [Rmb]. *)
  Definition ldata (m : cell_op LC) : WT.DCat :=
    match m with rd _ _ => WT.DR | _ => WT.DW end.

  Definition lcat : cell_op LC -> WT.DCat := bcat ldec TSO_modes ldata WT.Wmb WT.Rmb.

  (** The table-induced relation of [WindowTable.dto rc]. *)
  Definition LI (rc : bool) : cell_op LC -> cell_op LC -> Prop := I_tab (WT.dto rc) lcat.

  (** [dto] on the four categories that occur, for both profiles. *)
  Lemma latch_table rc :
    WT.dto rc WT.DW WT.Wmb = true /\ WT.dto rc WT.Wmb WT.DW = true /\ WT.dto rc WT.Wmb WT.Wmb = true /\
    WT.dto rc WT.DR WT.Rmb = true /\ WT.dto rc WT.Rmb WT.DR = true /\ WT.dto rc WT.Rmb WT.Rmb = true /\
    WT.dto rc WT.DR WT.DR = false /\ WT.dto rc WT.DR WT.DW = false /\
    WT.dto rc WT.DW WT.DR = false /\ WT.dto rc WT.DW WT.DW = false /\
    WT.dto rc WT.DR WT.Wmb = false /\ WT.dto rc WT.Wmb WT.DR = false /\
    WT.dto rc WT.DW WT.Rmb = false /\ WT.dto rc WT.Rmb WT.DW = false /\
    WT.dto rc WT.Rmb WT.Wmb = false /\ WT.dto rc WT.Wmb WT.Rmb = false.
  Proof. destruct rc; repeat split. Qed.

  (** ** Part 2. The CE1 and CE2 cell traces *)

  Abbreviation T1 := 1%positive.
  Abbreviation T3 := 3%positive.

  Definition bW (t : tid) (h : nat) (x : LLoc) (v : nat) : block LC := @BW LC t h (Dat x) v tt.
  Definition bR (t : tid) (h : nat) (x : LLoc) (v : nat) : block LC := @BR LC t h (Dat x) tt v.
  Definition bWmb (t : tid) (h : nat) : block LC := @BW LC t h GBw 0 tt.
  Definition bRmb (t : tid) (h : nat) : block LC := @BR LC t h GBr tt 0.
  Definition bF (t : tid) (h : nat) (x : gloc LLoc) : block LC := @BF LC t h x.

  Definition ins2 : trace LC :=
    [ bWmb T1 0;             (* wmb0 *)
      bR T1 1 Lseq 0;        (* s <- seq = 0 *)
      bW T1 2 Lseq 1;        (* seq := s+1 = 1 *)
      bWmb T1 3;             (* wmb1 *)
      bR T1 4 Ln0 0;         (* m <- n0 = 0 *)
      bW T1 5 La00 2;        (* a00 := 2 *)
      bW T1 6 Ln0 1;         (* n0 := 1 *)
      bWmb T1 7;             (* wmb2 *)
      bW T1 8 Lseq 2;        (* seq := s+2 = 2 *)
      bWmb T1 9;             (* wmb3 *)
      bW T1 10 La10 2;       (* a10 := 2 *)
      bW T1 11 Ln1 1 ].      (* n1 := 1 *)

  Definition own_contains : trace LC :=
    [ bR T1 12 Lseq 2;       (* s <- seq = 2, forwarded *)
      bR T1 13 Ln0 1;        (* m <- n0 = 1, forwarded *)
      bR T1 14 La00 2;       (* a00 = 2: found, forwarded *)
      bRmb T1 15;            (* rmb *)
      bR T1 16 Lseq 2 ].     (* seq = 2 = s: return true *)

  Definition other_contains : trace LC :=
    [ bR T3 0 Lseq 0;        (* s <- seq = 0, from memory *)
      bR T3 1 Ln0 0;         (* m <- n0 = 0, from memory *)
      bRmb T3 2;             (* rmb *)
      bR T3 3 Lseq 0 ].      (* seq = 0 = s: return false *)

  Definition flushes : trace LC :=
    [ bF T1 100 GBw; bF T1 101 (Dat Lseq); bF T1 102 GBw; bF T1 103 (Dat La00); bF T1 104 (Dat Ln0);
      bF T1 105 GBw; bF T1 106 (Dat Lseq); bF T1 107 GBw; bF T1 108 (Dat La10); bF T1 109 (Dat Ln1) ].

  Definition ce1_cells : trace LC := ins2 ++ other_contains ++ flushes.
  Definition ce2_cells : trace LC := ins2 ++ own_contains ++ other_contains ++ flushes.

  Definition ce1_hist : list (block LC) := hide ce1_cells.
  Definition ce2_hist : list (block LC) := hide ce2_cells.

  Lemma ce1_hist_eq : ce1_hist = ins2 ++ other_contains.
  Proof. reflexivity. Qed.

  Lemma ce2_hist_eq : ce2_hist = ins2 ++ own_contains ++ other_contains.
  Proof. reflexivity. Qed.

  Theorem ce1_cells_V rc : V (LI rc) ce1_cells.
  Proof. apply V_of_tchk; destruct rc; exact eq_refl. Qed.

  Theorem ce2_cells_V rc : V (LI rc) ce2_cells.
  Proof. apply V_of_tchk; destruct rc; exact eq_refl. Qed.

  Theorem ce1_cells_V_any : forall Ir, V Ir ce1_cells.
  Proof. apply V_of_fifochk; exact eq_refl. Qed.

  Theorem ce2_cells_V_any : forall Ir, V Ir ce2_cells.
  Proof. apply V_of_fifochk; exact eq_refl. Qed.

  Theorem ce1_underlay_allowed rc :
    nu (LI rc) ce1_hist /\ presents ce1_hist (cand_of ce1_hist) /\ respects ce1_hist (po (cand_of ce1_hist)).
  Proof.
    split; [| split].
    - exists ce1_cells. split; [apply ce1_cells_V | reflexivity].
    - apply Permutation.Permutation_refl.
    - apply respects_po_of_chk. exact eq_refl.
  Qed.

  Theorem ce2_underlay_allowed rc :
    nu (LI rc) ce2_hist /\ presents ce2_hist (cand_of ce2_hist) /\ respects ce2_hist (po (cand_of ce2_hist)).
  Proof.
    split; [| split].
    - exists ce2_cells. split; [apply ce2_cells_V | reflexivity].
    - apply Permutation.Permutation_refl.
    - apply respects_po_of_chk. exact eq_refl.
  Qed.

  (** No relation excludes the two histories: both traces are FIFO. *)
  Theorem ce1_hist_nu_any : forall Ir, nu Ir ce1_hist.
  Proof. intros Ir. exists ce1_cells. split; [apply ce1_cells_V_any | reflexivity]. Qed.

  Theorem ce2_hist_nu_any : forall Ir, nu Ir ce2_hist.
  Proof. intros Ir. exists ce2_cells. split; [apply ce2_cells_V_any | reflexivity]. Qed.

  (** In both histories every block of the insert precedes every block of
      T3's contains (and, in CE2, every block of T1's own contains precedes
      them too).  Blocks are atomic, so every cell call of the insert has
      responded before T3 invokes its first cell call. *)
  Lemma ce1_hist_separated : forall a b, In a ins2 -> In b other_contains -> before ce1_hist a b.
  Proof. intros a b Ha Hb. rewrite ce1_hist_eq. apply before_app_lr; assumption. Qed.

  Lemma ce2_hist_separated :
    forall a b, In a (ins2 ++ own_contains) -> In b other_contains -> before ce2_hist a b.
  Proof. intros a b Ha Hb. rewrite ce2_hist_eq, app_assoc. apply before_app_lr; assumption. Qed.

  (** When T3 starts, the insert has issued all its blocks and none of its
      ten writes (six data writes, four wmb) is published. *)
  Lemma ins2_all_pending : pend T1 ins2 = filter is_writeb ins2.
  Proof. reflexivity. Qed.

  (** T3's contains runs in the state left by [ins2] (in CE2, [own_contains]
      writes nothing).  T3 has no pending write, so its reads of seq and n0
      are served from memory (rule RdM), which still holds 0. *)
  Lemma ce1_T3_reads_memory :
    cP (state_after (C := LC) (Dat Lseq) ins2) T3 = [] /\ cg (state_after (C := LC) (Dat Lseq) ins2) = 0 /\
    cP (state_after (C := LC) (Dat Ln0) ins2) T3 = [] /\ cg (state_after (C := LC) (Dat Ln0) ins2) = 0.
  Proof. repeat split. Qed.

  (** T1's own data reads in CE2 run in the same state.  T1's buffer holds
      writes of seq, n0 and a00, so the reads are forwarded (rule RdF) and
      return the last pending values 2, 1, 2. *)
  Lemma ce2_T1_reads_forwarded :
    cP (state_after (C := LC) (Dat Lseq) ins2) T1 = [1; 2] /\
    cP (state_after (C := LC) (Dat Ln0) ins2) T1 = [1] /\
    cP (state_after (C := LC) (Dat La00) ins2) T1 = [2].
  Proof. repeat split. Qed.

  (** *** Controls *)

  (** Negative control: with T1's flushes before T3's contains, T3 cannot
      read seq = 0; the trace is in [V] for no relation. *)
  Definition ce1_flushed_first : trace LC := ins2 ++ flushes ++ other_contains.

  Theorem ce1_flushed_first_not_V : forall Ir, ~ V Ir ce1_flushed_first.
  Proof. apply not_V_of_vchk. exact eq_refl. Qed.

  (** Positive control: after the flushes, T3's contains(2) returns true. *)
  Definition other_contains_true : trace LC :=
    [ bR T3 0 Lseq 2; bR T3 1 Ln0 1; bR T3 2 La00 2; bRmb T3 3; bR T3 4 Lseq 2 ].

  Theorem ce1_flushed_true_V : forall Ir, V Ir (ins2 ++ flushes ++ other_contains_true).
  Proof. apply V_of_fifochk; exact eq_refl. Qed.

  (** The writer cannot miss its own insert: after [ins2], T1's read of
      seq cannot return the old value 0. *)
  Theorem ce2_writer_must_forward : forall Ir, ~ V Ir (ins2 ++ [bR T1 12 Lseq 0]).
  Proof. apply not_V_of_vchk. exact eq_refl. Qed.

  (** ** Part 3. The x86-TSO machine *)

  Abbreviation GL := (gloc LLoc).
  Abbreviation gdec := (gloc_eq_dec ldec).

  (** Deleting the ghost barrier accesses: on x86, rmb and wmb are
      compiler barriers. *)
  Definition is_datab (b : block LC) : bool := match b_loc b with Dat _ => true | _ => false end.
  Definition strip (s : trace LC) : trace LC := filter is_datab s.

  Lemma V_up_of_chk (s : trace LC) :
    fifochk s = true -> vchk s = true -> wochk s = true -> TSO.V_up GL gdec s.
  Proof.
    intros H1 H2 H3. split.
    - exact (V_of_fifochk s H1 H2 _).
    - exact (wr_order_of_chk s H3).
  Qed.

  Definition ce1_x86_run : list (TSO.elabel GL) :=
    [ TSO.ER GL T1 (Dat Lseq) 0; TSO.EW GL T1 (Dat Lseq) 1; TSO.ER GL T1 (Dat Ln0) 0;
      TSO.EW GL T1 (Dat La00) 2; TSO.EW GL T1 (Dat Ln0) 1; TSO.EW GL T1 (Dat Lseq) 2;
      TSO.EW GL T1 (Dat La10) 2; TSO.EW GL T1 (Dat Ln1) 1;
      TSO.ER GL T3 (Dat Lseq) 0; TSO.ER GL T3 (Dat Ln0) 0; TSO.ER GL T3 (Dat Lseq) 0;
      TSO.EF GL T1 (Dat Lseq); TSO.EF GL T1 (Dat La00); TSO.EF GL T1 (Dat Ln0);
      TSO.EF GL T1 (Dat Lseq); TSO.EF GL T1 (Dat La10); TSO.EF GL T1 (Dat Ln1) ].

  Lemma ce1_x86_run_eq : TSO.erase GL gdec (strip ce1_cells) = ce1_x86_run.
  Proof. reflexivity. Qed.

  Theorem ce1_x86 : TSO.Tr GL gdec ce1_x86_run.
  Proof.
    apply (proj1 (TSO.tso_traces GL gdec _)). exists (strip ce1_cells).
    split; [apply V_up_of_chk; exact eq_refl | reflexivity].
  Qed.

  Theorem ce2_x86 : TSO.Tr GL gdec (TSO.erase GL gdec (strip ce2_cells)).
  Proof.
    apply (proj1 (TSO.tso_traces GL gdec _)). exists (strip ce2_cells).
    split; [apply V_up_of_chk; exact eq_refl | reflexivity].
  Qed.

  (** The trace with the ghost accesses is a machine trace as well. *)
  Theorem ce1_cells_x86 : TSO.Tr GL gdec (TSO.erase GL gdec ce1_cells).
  Proof.
    apply (proj1 (TSO.tso_traces GL gdec _)). exists ce1_cells.
    split; [apply V_up_of_chk; exact eq_refl | reflexivity].
  Qed.

  (** ** Part 4. The overlay: an atomic set refutes CE1 and CE2 *)

  Import LinCCALBase RelaxedSig RelaxedLTSSpec RelaxedTraceLin.

  Inductive SetOp : Type := Ins (k : nat) | Mem (k : nat).

  Definition set_ar (o : SetOp) : Type := match o with Ins _ => unit | Mem _ => bool end.

  Definition SetSig : Sig.t := {| Sig.op := SetOp; Sig.ar := set_ar |}.

  (** The set signature, for any semi-independence relation. *)
  Definition SetE (indep : relation SetOp) : RelaxedSig.t :=
    {| effect := SetSig; handle := nat; semi_independent := indep; mode := fun _ => Local |}.

  (** Non-dependent summaries of completed operations. *)
  Inductive SEv : Type := EIns (k : nat) | EMem (k : nat) (b : bool).

  Definition sev_of (o : SetOp) : set_ar o -> SEv :=
    match o return set_ar o -> SEv with
    | Ins k => fun _ => EIns k
    | Mem k => fun b => EMem k b
    end.

  (** The atomic grow-only set: [Ins k] adds [k]; [Mem k] answers whether
      [k] is in the set.  [S] is the current set. *)
  Definition memb (k : nat) (S : list nat) : bool := existsb (Nat.eqb k) S.

  Fixpoint set_ok (S : list nat) (l : list SEv) : Prop :=
    match l with
    | [] => True
    | EIns k :: l' => set_ok (k :: S) l'
    | EMem k b :: l' => b = memb k S /\ set_ok S l'
    end.

  Lemma memb_In k S : In k S -> memb k S = true.
  Proof.
    intros H. unfold memb. apply existsb_exists. exists k. split; [exact H | apply Nat.eqb_refl].
  Qed.

  (** Once [k] is in the set, every later [Mem k] answers [true]. *)
  Lemma set_ok_member S l k b : set_ok S l -> In k S -> In (EMem k b) l -> b = true.
  Proof.
    revert S. induction l as [| e l IH]; intros S H Hk Hin; [destruct Hin |].
    destruct e as [k' | k' b']; cbn in H, Hin.
    - destruct Hin as [Hc | Hin]; [discriminate Hc |].
      apply (IH (k' :: S) H); [right; exact Hk | exact Hin].
    - destruct H as [Hb H]. destruct Hin as [Hc | Hin].
      + injection Hc as -> ->. rewrite Hb. apply memb_In, Hk.
      + exact (IH S H Hk Hin).
  Qed.

  Lemma set_ok_app S l1 l2 : set_ok S (l1 ++ l2) -> exists S', set_ok S' l2.
  Proof.
    revert S. induction l1 as [| e l1 IH]; intros S H; [exists S; exact H |].
    destruct e as [k | k b]; cbn in H; [exact (IH _ H) | exact (IH _ (proj2 H))].
  Qed.

  Lemma set_ok_ins_mem S l1 l2 k b : set_ok S (l1 ++ EIns k :: l2) -> In (EMem k b) l2 -> b = true.
  Proof.
    intros H Hin. destruct (set_ok_app S l1 _ H) as (S' & H').
    cbn in H'. exact (set_ok_member _ _ _ _ H' (or_introl eq_refl) Hin).
  Qed.

  Section Overlay.
    Context (indep : relation SetOp).
    Local Abbreviation E := (SetE indep).

    Definition sev (o : Op E) : SEv := sev_of (op_op o) (op_ret o).

    (** The atomic grow-only set specification, from the initial set [S0]. *)
    Definition nuset_from (S0 : list nat) (W : list (Op E)) : Prop := set_ok S0 (map sev W).
    Definition nuset : list (Op E) -> Prop := nuset_from [].

    (** The real-time refutation, for any trace and selector.  If an
        [Ins x] responds before a [Mem x] is invoked and that [Mem x]
        returns [false], the trace is not relaxed linearizable w.r.t. the
        atomic set, for every semi-independence relation and every initial
        set.  Only the real-time clause of [rhb] is used. *)
    Theorem rt_ins_mem_false_not_rel_lin {X : Type} (sel : X -> option (ThreadEvent E)) (L : list X)
        (S0 : list nat) (k1 k2 : CallKey E) (x : nat) :
      (forall j op ret, res_at sel L j k1 op ret -> sev_of op ret = EIns x) ->
      (forall j op ret, res_at sel L j k2 op ret -> sev_of op ret = EMem x false) ->
      (exists i, inv_at sel L i k1 (Ins x)) ->
      (exists i j, res_at sel L i k1 (Ins x) tt /\ inv_at sel L j k2 (Mem x) /\ i < j) ->
      ~ rel_lin sel L indep (nuset_from S0).
    Proof.
      intros H1 H2 [i0 Hi0] (i & j & Hres & Hinv & Hij) (W & Hnu & Hnd & Hocc & Hall & Hord).
      destruct (Hall _ _ _ Hi0) as (o1 & Ho1 & K1).
      destruct (Hall _ _ _ Hinv) as (o2 & Ho2 & K2).
      destruct (Hocc o1 Ho1) as [_ (j1 & Hj1)]. rewrite K1 in Hj1. pose proof (H1 _ _ _ Hj1) as E1.
      destruct (Hocc o2 Ho2) as [_ (j2 & Hj2)]. rewrite K2 in Hj2. pose proof (H2 _ _ _ Hj2) as E2.
      destruct o1 as [key1 op1 r1]; cbn in K1, E1; subst key1.
      destruct op1 as [y | y]; cbn in E1; [injection E1 as -> | discriminate E1].
      destruct r1.
      destruct o2 as [key2 op2 r2]; cbn in K2, E2; subst key2.
      destruct op2 as [y | y]; cbn in E2; [discriminate E2 | injection E2 as -> ->].
      assert (Hb : before W (Build_Op (E := E) k1 (Ins x) tt) (Build_Op (E := E) k2 (Mem x) false)).
      { apply Hord; [exact Ho1 | exact Ho2 |]. left. exists i, j. auto. }
      destruct Hb as (l1 & l2 & EW & Hin).
      unfold nuset_from in Hnu. rewrite EW, map_app in Hnu. cbn [map] in Hnu.
      assert (Hin' : In (EMem x false) (map sev l2)).
      { change (EMem x false) with (sev (Build_Op (E := E) k2 (Mem x) false)). apply in_map, Hin. }
      discriminate (set_ok_ins_mem _ _ _ _ _ Hnu Hin').
    Qed.

    (** *** Reading concrete traces without dependent equalities *)

    Definition res_info (ev : ThreadEvent E) : option (CallKey E * SEv) :=
      match te_ev E ev with
      | ResEv h op r => Some ((te_tid E ev, h), sev_of op r)
      | InvEv _ _ => None
      end.

    Definition ev_info (ev : ThreadEvent E) : bool * CallKey E :=
      match te_ev E ev with
      | InvEv h _ => (false, (te_tid E ev, h))
      | ResEv h _ _ => (true, (te_tid E ev, h))
      end.

    Lemma res_at_info (L : list (ThreadEvent E)) j k op ret :
      res_at Some L j k op ret -> In (Some (k, sev_of op ret)) (map res_info L).
    Proof.
      destruct k as [t h]. intros (ev & Hx & Hs). injection Hs as ->.
      apply (nth_error_In _ j). rewrite nth_error_map, Hx. reflexivity.
    Qed.

    Lemma res_at_pos (L : list (ThreadEvent E)) j k op ret :
      res_at Some L j k op ret -> nth_error (map ev_info L) j = Some (true, k).
    Proof.
      destruct k as [t h]. intros (ev & Hx & Hs). injection Hs as ->.
      rewrite nth_error_map, Hx. reflexivity.
    Qed.

    Lemma inv_at_pos (L : list (ThreadEvent E)) i k op :
      inv_at Some L i k op -> nth_error (map ev_info L) i = Some (false, k).
    Proof.
      destruct k as [t h]. intros (ev & Hx & Hs). injection Hs as ->.
      rewrite nth_error_map, Hx. reflexivity.
    Qed.

    Lemma before_nth {A : Type} (W : list A) i j a b :
      nth_error W i = Some a -> nth_error W j = Some b -> i < j -> before W a b.
    Proof.
      revert i j. induction W as [| c W IH]; intros i j Hi Hj Hij; [destruct i; discriminate Hi |].
      destruct i as [| i]; destruct j as [| j]; cbn in Hi, Hj.
      - exfalso. exact (Nat.lt_irrefl 0 Hij).
      - injection Hi as <-. exists [], W. split; [reflexivity | eapply nth_error_In; exact Hj].
      - exfalso. exact (Nat.nlt_0_r _ Hij).
      - destruct (IH i j Hi Hj (proj2 (Nat.succ_lt_mono i j) Hij)) as (l1 & l2 & -> & Hl2).
        exists (c :: l1), l2. split; [reflexivity | exact Hl2].
    Qed.

    (** *** CE1: T1 inserts 2; then T3's contains(2) returns [b] *)

    Definition ce1_ov (b : bool) : list (ThreadEvent E) :=
      [ Build_ThreadEvent T1 (InvEv (E := E) 0 (Ins 2));
        Build_ThreadEvent T1 (ResEv (E := E) 0 (Ins 2) tt);
        Build_ThreadEvent T3 (InvEv (E := E) 0 (Mem 2));
        Build_ThreadEvent T3 (ResEv (E := E) 0 (Mem 2) b) ].

    Local Ltac pick H :=
      cbn in H; repeat (destruct H as [H | H]; [first [discriminate H | injection H as ->; reflexivity] |]);
      destruct H.

    Theorem ce1_overlay_not_rel_lin_from S0 : ~ rel_lin Some (ce1_ov false) indep (nuset_from S0).
    Proof.
      apply (rt_ins_mem_false_not_rel_lin Some (ce1_ov false) S0 (T1, 0) (T3, 0) 2).
      - intros j op ret H. apply res_at_info in H. revert H. generalize (sev_of op ret) as v. intros v H.
        pick H.
      - intros j op ret H. apply res_at_info in H. revert H. generalize (sev_of op ret) as v. intros v H.
        pick H.
      - exists 0. eexists. split; reflexivity.
      - exists 1, 2. split; [eexists; split; reflexivity | split; [eexists; split; reflexivity | auto]].
    Qed.

    Theorem ce1_overlay_not_rel_lin : ~ rel_lin Some (ce1_ov false) indep nuset.
    Proof. exact (ce1_overlay_not_rel_lin_from []). Qed.

    (** *** CE2: T1 inserts 2 and its own contains(2) returns [true]; then
        T3's contains(2) returns [b] *)

    Definition ce2_ov (b : bool) : list (ThreadEvent E) :=
      [ Build_ThreadEvent T1 (InvEv (E := E) 0 (Ins 2));
        Build_ThreadEvent T1 (ResEv (E := E) 0 (Ins 2) tt);
        Build_ThreadEvent T1 (InvEv (E := E) 1 (Mem 2));
        Build_ThreadEvent T1 (ResEv (E := E) 1 (Mem 2) true);
        Build_ThreadEvent T3 (InvEv (E := E) 0 (Mem 2));
        Build_ThreadEvent T3 (ResEv (E := E) 0 (Mem 2) b) ].

    Theorem ce2_overlay_not_rel_lin_from S0 : ~ rel_lin Some (ce2_ov false) indep (nuset_from S0).
    Proof.
      apply (rt_ins_mem_false_not_rel_lin Some (ce2_ov false) S0 (T1, 0) (T3, 0) 2).
      - intros j op ret H. apply res_at_info in H. revert H. generalize (sev_of op ret) as v. intros v H.
        pick H.
      - intros j op ret H. apply res_at_info in H. revert H. generalize (sev_of op ret) as v. intros v H.
        pick H.
      - exists 0. eexists. split; reflexivity.
      - exists 1, 4. split; [eexists; split; reflexivity | split; [eexists; split; reflexivity | auto]].
    Qed.

    Theorem ce2_overlay_not_rel_lin : ~ rel_lin Some (ce2_ov false) indep nuset.
    Proof. exact (ce2_overlay_not_rel_lin_from []). Qed.

    (** *** Controls: with T3's contains(2) = true, both traces are relaxed
        linearizable, for every semi-independence relation. *)

    Definition o_ins : Op E := Build_Op (E := E) (T1, 0) (Ins 2) tt.
    Definition o_mem1 : Op E := Build_Op (E := E) (T1, 1) (Mem 2) true.
    Definition o_mem3 : Op E := Build_Op (E := E) (T3, 0) (Mem 2) true.

    (** Determine the position [n] in [H : nth_error l n = Some p] for a
        concrete list [l]. *)
    Local Ltac posn H :=
      cbn in H;
      repeat match type of H with
             | nth_error _ ?n = Some _ => is_var n; let m := fresh "m" in destruct n as [| m]; cbn in H
             end;
      try discriminate H.

    Local Ltac ltc := apply (proj1 (Nat.ltb_lt _ _)); reflexivity.
    Local Ltac nltc H := apply (proj2 (Nat.ltb_lt _ _)) in H; cbn in H; discriminate H.

    (** [rhb] implies [before] in a witness that lists the operations in
        invocation order, for a trace in which each operation responds
        before the next one is invoked. *)
    Local Ltac rhb_seq :=
      intros o o' Ho Ho' Hr;
      repeat (destruct Ho as [<- | Ho]; [| ]); try destruct Ho;
      repeat (destruct Ho' as [<- | Ho']; [| ]); try destruct Ho';
      destruct Hr as [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & _)];
      first
        [ apply (before_nth _ 0 1); [reflexivity | reflexivity | ltc]
        | apply (before_nth _ 0 2); [reflexivity | reflexivity | ltc]
        | apply (before_nth _ 1 2); [reflexivity | reflexivity | ltc]
        | exfalso; cbn in Ht; discriminate Ht
        | exfalso; apply res_at_pos in Hi; apply inv_at_pos in Hj; posn Hi; posn Hj; nltc Hij
        | exfalso; apply inv_at_pos in Hi; apply inv_at_pos in Hj; posn Hi; posn Hj; nltc Hij ].

    Theorem ce1_ctl_rel_lin : rel_lin Some (ce1_ov true) indep nuset.
    Proof.
      exists [o_ins; o_mem3]. split; [| split; [| split; [| split]]].
      - cbn. repeat split.
      - repeat constructor; cbn; intuition discriminate.
      - intros o [<- | [<- | []]]; split.
        + exists 0. eexists. split; reflexivity.
        + exists 1. eexists. split; reflexivity.
        + exists 2. eexists. split; reflexivity.
        + exists 3. eexists. split; reflexivity.
      - intros i k op Hi. apply inv_at_pos in Hi. posn Hi; injection Hi as <-;
          first [ exists o_ins; split; [cbn; tauto | reflexivity]
                | exists o_mem3; split; [cbn; tauto | reflexivity] ].
      - rhb_seq.
    Qed.

    Theorem ce2_ctl_rel_lin : rel_lin Some (ce2_ov true) indep nuset.
    Proof.
      exists [o_ins; o_mem1; o_mem3]. split; [| split; [| split; [| split]]].
      - cbn. repeat split.
      - repeat constructor; cbn; intuition discriminate.
      - intros o [<- | [<- | [<- | []]]]; split.
        + exists 0. eexists. split; reflexivity.
        + exists 1. eexists. split; reflexivity.
        + exists 2. eexists. split; reflexivity.
        + exists 3. eexists. split; reflexivity.
        + exists 4. eexists. split; reflexivity.
        + exists 5. eexists. split; reflexivity.
      - intros i k op Hi. apply inv_at_pos in Hi. posn Hi; injection Hi as <-;
          first [ exists o_ins; split; [cbn; tauto | reflexivity]
                | exists o_mem1; split; [cbn; tauto | reflexivity]
                | exists o_mem3; split; [cbn; tauto | reflexivity] ].
      - rhb_seq.
    Qed.

  End Overlay.

End LatchSetRT.
