(** * SeqLockQ6Mem: the Q6 runs, and Reviewer A's test, in the buffered memory of memory/

    Cell-level evidence for question Q6 (see [SeqLockQ6]).  It uses the TSO
    instance of the buffered cell (memory/Cell.v: [TSO_cfg Nat.eq_dec];
    I = [mode_indep]: only a write followed by a read of another location
    is semi-independent, [TSO_indep_iff]).  Locations: z = 0, x = 1,
    y = 2, s = 3 (the TicketLock / version word).  T1 = thread 1, T2 =
    thread 2.  This file depends only on memory/ (and
    models/RelaxedSignature.v) and changes no file there.

    The traces [sq] and [rt_cells] are hand-mapped cell images of the
    SeqLock runs of [SeqLockQ6]: GT and TT ↦ R s; Acq and Rel ↦ a locked
    R s; W s; F s; Wmb and Rmb ↦ nothing; RdX/WrX etc. ↦ R/W of the
    location.  No theorem relates them to the underlay histories of
    [SeqLockQ6]; memory/ has no link to [RelaxedLTS] yet.

    The Q6 run.
    - [sq_V], [sq_nu]: the trace [sq] (22 blocks, flushes included) is in
      V_TSO, and its flush-free history [hide sq] is in ν_TSO.
      T1: W z 1; R z = 1, forwarded from T1's own buffer (rule RdF,
      Cell.v); R s 0, R x 0, R y 0, R s 0, so read() = (0,0).
      T2: acq = R s 0; W s 1; F s.  Then W x 1; W y 1; F x; F y.  Then
      rel = R s 1; W s 2; F s.  Then R s 2, R x 1, R y 1, R s 2, so
      read() = (1,1).  Then R z = 0, from memory (rule RdM).  T1's flush
      of z comes last.
    - [sq_locked]: both RMWs of T2 are [locked_rmw] triples (see below).
    - [q6_cells_x86_trace]: [sq], with handles erased and flushes
      visible, is a trace of the x86-TSO machine of Owens, Sarkar and
      Sewell, read/write fragment ([TSO.tso_traces]).  This is the
      independent x86 evidence.
    - [q6_cells_TSO_consistent]: let the candidate consist of the 17
      visible accesses, with program order = thread order by handle and
      [pre] = the whole program order (the largest admissible relation
      contained in po; [admissible] also allows cross-thread edges).  It
      has a witness satisfying (D1) and (D2) of the TSO instance.  This
      follows from [sq_nu] through the paper's own equivalence
      ([Equivalence.declarative_TSO], Theorem mem:thm:decl; uses
      [classic]), so it is not independent evidence about x86.
      Explanation, not a lemma: T1's W z has no outgoing edge of (D2)'s
      relation [Dc] in any well-formed witness.  [Dc] uses rfe, not rf,
      and the only read of W z is T1's own; W z is the only write to z,
      so it has no mo edge; [ppo] leaves a write only towards a later
      write of the same thread, and T1 has none.
    - [sq_z_history]: the z part of the history is
      [W₁ z 1; R₁ z 1; R₂ z 0].  As a sequence it is not a register
      history: the register [SeqLockModule.zreg] of the SeqLock underlay
      specification rejects it, because the last read returns 0 after a
      write of 1.  This is a fact about one sequential order, not about
      relaxed linearizability.  Without real-time order the z accesses
      alone can be ordered as a register history (R₂ z 0 first; not
      stated here).  What Q6 needs is the cross-location cycle through
      the SeqLock, see [SeqLockQ6].

    The real-time iteration (Q6-2; [SeqLockQ6] Part 4).
    - [rt_cells_V], [rt_cells_nu], [rt_cells_x86_trace]: T2's acq (a
      locked R s 0; W s 1; F s) and W x 1.  T1 reads s = 1, x = 0, y = 0,
      s = 1 (odd: retry).  T2 writes y := 1, drains x and y, and does its
      rel (a locked R s 1; W s 2; F s).  T1 reads s = 2, x = 1, y = 1,
      s = 2.  [rt_cells_locked]: both RMWs are [locked_rmw] triples.
    - In the history, T2's W x 1 precedes T1's R x = 0
      ([rt_cells_write_before_read]).  A block is atomic, so the write has
      responded before the read is invoked.  At that point the write is
      still pending in T2's buffer ([rt_cells_pending]).
    - The run is forwarding-free: T1 does not write, and T2 reads only
      with its buffer empty.

    Reviewer A's test (popl2027-reviews.md:69-81; the plain-cell example
    of Appendix/Mem.tex:5-14):
    W x 1; R x = 1; R y = 0 ‖ W y 1; R y = 1; R x = 0.
    - [sbrfi_V], [sbrfi_nu], [sbrfi_x86_trace]: the outcome is in V_TSO and
      ν_TSO, and it is a trace of the x86-TSO machine.  Both own reads are
      forwarded.
    - That no register specification produces it, for any semi-independence
      that keeps same-location and read-read order, is in [RegisterSB].

    The locked RMWs (acq and rel are XCHG on x86).  memory/ has no RMW
    and no locked instruction.  Each RMW is a [locked_rmw] triple: a read
    of s, a write of s and the flush of that write.  The three blocks are
    contiguous, so no other thread acts in between.  T2's buffer is
    empty before the read, so the read returns the memory value
    (the old value the XCHG returns: 0 for acq, 1 for rel).  It is empty
    again after the flush.  For rel, T2's earlier writes of x and y are
    flushed, in order, just before the triple.  Everything about these
    triples is kernel-checked ([sq_locked], [rt_cells_locked], and the
    [V]/[nu]/[TSO.Tr] theorems).  One step remains a derivation: that a
    contiguous R; W; F of one location, from an empty buffer to an empty
    buffer, is a locked-RMW step of x86-TSO.  The machine of TSO.v has no
    locked instructions.

    What else memory/ cannot express.
    - rmb and wmb.  Cell has only wrt, rd and flush, so there are no
      fences.  On the TSO instance every write has mode LFence and every
      read RFence, so R→R and W→W order is already kept.  rmb and wmb would
      be no-ops, as on x86 where they are compiler barriers.  They are
      omitted.
    - ARMv8 fences and RMWs.  memory/ARM.v covers only "reads and writes
      with modes rlx/rel and rlx/acq, no RMWs, no fences" (ARM.v:3-4).
      The ARMv8 verdict of [SeqLockQ6] is therefore not covered here.
    - The read's retry loop.  The traces list the accesses of the
      iterations that happen; control flow is not modelled.
    - Handles of flush blocks (100..104) are arbitrary; nothing depends on
      them.

    Trusted computation.  The finite checks ([chk], [vchk], [whchk],
    [pochk], [locked_rmw] instances) are closed by [reflexivity] or
    [exact eq_refl], i.e. by the kernel's ordinary conversion; this file
    calls no [vm_compute].  Proof terms built by [lia] contain a VM cast,
    as everywhere in the development.  None of the results depends on
    [Tensor.s_in_product] or the [Litmus] facts proved with [vm_compute]
    ([Print All Dependencies]).

    Assumptions.  [q6_cells_TSO_consistent] uses [classic], through
    memory/Prelude.v and the declarative characterization.  Every other
    result is closed under the global context. *)

From Stdlib Require Import List Arith PArith Bool micromega.Lia.
From Stdlib Require Import Relations.Relation_Definitions Relations.Relation_Operators Sorting.Permutation.
Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Equivalence.
Require Import memory.TSO.

Import ListNotations.

Module SeqLockQ6Mem.
  Import Cell Cell.Instances Decl.

  (** Locations: z = 0, x = 1, y = 2, s = 3 (the lock / version word). *)
  Abbreviation C := (TSO_cfg Nat.eq_dec).
  Abbreviation I := (mode_indep (C := C)).

  (** ** Checkers for the flush contract, [VBuf], and handle order *)

  (** At every flush, the published write has the least handle among the
      pending writes of its thread.  Under TSO no two writes are
      semi-independent ([TSO_indep_iff]), so this is what the contract
      requires. *)
  Definition chk (s : trace C) (k : nat) : bool :=
    match nth_error s k with
    | Some (BF t _ x) =>
        match hd_error (proj x (pend t (firstn k s))) with
        | Some m => forallb (fun m' => Nat.leb (b_handle m) (b_handle m')) (pend t (firstn k s))
        | None => true
        end
    | _ => true
    end.

  Lemma contract_of_chk s : forallb (chk s) (seq 0 (length s)) = true -> contract I s.
  Proof.
    intros H s1 t h x s2 m Hs Hm m' Hm' Hlt. exfalso.
    assert (Hk : In (length s1) (seq 0 (length s))) by (apply in_seq; rewrite Hs, length_app; cbn; lia).
    rewrite forallb_forall in H. specialize (H _ Hk). unfold chk in H.
    assert (E1 : nth_error s (length s1) = Some (BF t h x))
      by (rewrite Hs, nth_error_app2, Nat.sub_diag by lia; reflexivity).
    assert (E2 : firstn (length s1) s = s1)
      by (rewrite Hs, firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r; reflexivity).
    rewrite E1, E2 in H.
    change (match hd_error (proj x (pend t s1)) with
            | Some m => forallb (fun m' => Nat.leb (b_handle m) (b_handle m')) (pend t s1)
            | None => true end = true) in H.
    rewrite Hm in H. rewrite forallb_forall in H. specialize (H m' Hm'). apply Nat.leb_le in H. lia.
  Qed.

  Definition enabledb (b : block C) (st : cstate) : bool :=
    match b with
    | BW _ _ _ _ _ => true
    | BR t _ _ _ v => match cP st t with [] => Nat.eqb v (cg st) | l => Nat.eqb v (last l 0) end
    | BF t _ _ => match cP st t with [] => false | _ => true end
    end.

  Lemma enabledb_sound b st : enabledb b st = true -> enabled b st.
  Proof.
    destruct b as [t h x v a | t h x a v | t h x]; cbn; [auto | |].
    - destruct (cP st t) as [| n l] eqn:E; intros H; apply Nat.eqb_eq in H.
      + right. split; [reflexivity | exact H].
      + left. split; [discriminate | exact H].
    - destruct (cP st t); [discriminate | intros _; discriminate].
  Qed.

  Definition vchk (s : trace C) : bool :=
    forallb (fun i => match nth_error s i with
                      | Some b => enabledb b (state_after (b_loc b) (firstn i s))
                      | None => true
                      end) (seq 0 (length s)).

  Lemma VBuf_of_vchk s : vchk s = true -> forall x, VBuf x (proj x s).
  Proof.
    intros H x. apply VBuf_proj_iff. intros i b Hi Hloc. subst x. apply enabledb_sound.
    unfold vchk in H. rewrite forallb_forall in H.
    assert (Hin : In i (seq 0 (length s))) by (apply in_seq; split; [lia | apply nth_error_Some; congruence]).
    specialize (H i Hin). rewrite Hi in H. exact H.
  Qed.

  Lemma V_of_chk s : forallb (chk s) (seq 0 (length s)) = true -> vchk s = true -> V I s.
  Proof. intros H1 H2. split; [apply contract_of_chk, H1 | apply VBuf_of_vchk, H2]. Qed.

  (** Writes of each thread are issued in increasing handle order, so the
      trace is in [TSO.V_up]. *)
  Definition whchk (s : trace C) : bool :=
    forallb (fun i => forallb (fun j => implb (Nat.ltb i j)
      (match nth_error s i, nth_error s j with
       | Some a, Some b =>
           implb (is_writeb a && is_writeb b && Pos.eqb (b_tid a) (b_tid b)) (Nat.ltb (b_handle a) (b_handle b))
       | _, _ => true
       end)) (seq 0 (length s))) (seq 0 (length s)).

  Lemma wr_handle_order_of_chk s : whchk s = true -> TSO.wr_handle_order nat Nat.eq_dec s.
  Proof.
    intros H i j a b Hij Ha Hb Wa Wb Ht.
    assert (Hi : In i (seq 0 (length s))) by (apply in_seq; split; [lia | apply nth_error_Some; congruence]).
    assert (Hj : In j (seq 0 (length s))) by (apply in_seq; split; [lia | apply nth_error_Some; congruence]).
    unfold whchk in H. rewrite forallb_forall in H. specialize (H i Hi).
    rewrite forallb_forall in H. specialize (H j Hj). rewrite Ha, Hb in H.
    apply Nat.ltb_lt in Hij. rewrite Hij in H. cbn [implb] in H.
    apply is_writeb_true in Wa. apply is_writeb_true in Wb.
    rewrite Wa, Wb, Ht, Pos.eqb_refl in H. cbn in H. apply Nat.ltb_lt, H.
  Qed.

  (** ** Locked read-modify-writes *)

  (** [locked_rmw s k t x]: positions [k], [k+1], [k+2] of [s] are a read,
      a write and a flush of [x] by thread [t]; [t]'s buffer is empty
      before the read (so the read returns the memory value [cg], rule
      RdM) and empty again after the flush.  Contiguity means no other
      thread acts in between.  This is how the TicketLock's acq and rel
      (XCHG on x86) appear in the traces below. *)
  Definition locked_rmw (s : trace C) (k : nat) (t : tid) (x : nat) : Prop :=
    pend t (firstn k s) = [] /\
    (exists h v, nth_error s k = Some (@BR C t h x tt v) /\ v = cg (state_after (C := C) x (firstn k s))) /\
    (exists h v, nth_error s (S k) = Some (@BW C t h x v tt)) /\
    (exists h, nth_error s (S (S k)) = Some (@BF C t h x)) /\
    pend t (firstn (3 + k) s) = [].

  Local Ltac locked :=
    split; [reflexivity |]; split; [do 2 eexists; split; reflexivity |];
    split; [do 2 eexists; reflexivity |]; split; [eexists; reflexivity | reflexivity].

  (** ** The Q6 cells *)

  (** T1 = thread 1, T2 = thread 2.  Flush handles (100..104) are
      arbitrary; nothing depends on them. *)
  Definition sq : trace C :=
    [ @BW C 1%positive 0 0 1 tt;   (* T1: z := 1 (buffered) *)
      @BR C 1%positive 1 0 tt 1;   (* T1: z = 1, forwarded from T1's buffer *)
      @BR C 1%positive 2 3 tt 0;   (* T1: s = 0 *)
      @BR C 1%positive 3 1 tt 0;   (* T1: x = 0 *)
      @BR C 1%positive 4 2 tt 0;   (* T1: y = 0 *)
      @BR C 1%positive 5 3 tt 0;   (* T1: s = 0: read() = (0,0) *)
      @BR C 2%positive 0 3 tt 0;   (* T2: acq = XCHG s: reads 0 from memory (empty buffer) ... *)
      @BW C 2%positive 1 3 1 tt;   (* ... writes s := 1 ... *)
      @BF C 2%positive 100 3;      (* ... flushed at once *)
      @BW C 2%positive 2 1 1 tt;   (* T2: x := 1 *)
      @BW C 2%positive 3 2 1 tt;   (* T2: y := 1 *)
      @BF C 2%positive 101 1; @BF C 2%positive 102 2;  (* the drain before rel *)
      @BR C 2%positive 4 3 tt 1;   (* T2: rel = XCHG s: reads 1 from memory (empty buffer) ... *)
      @BW C 2%positive 5 3 2 tt;   (* ... writes s := 2 ... *)
      @BF C 2%positive 103 3;      (* ... flushed at once *)
      @BR C 2%positive 6 3 tt 2;   (* T2: s = 2 *)
      @BR C 2%positive 7 1 tt 1;   (* T2: x = 1 *)
      @BR C 2%positive 8 2 tt 1;   (* T2: y = 1 *)
      @BR C 2%positive 9 3 tt 2;   (* T2: s = 2: read() = (1,1) *)
      @BR C 2%positive 10 0 tt 0;  (* T2: z = 0, from memory *)
      @BF C 1%positive 104 0 ].    (* T1's z := 1 reaches memory last *)

  Lemma sq_locked : locked_rmw sq 6 2%positive 3 /\ locked_rmw sq 13 2%positive 3.
  Proof. split; locked. Qed.

  Theorem sq_V : V I sq.
  Proof. apply V_of_chk; exact eq_refl. Qed.

  Theorem sq_nu : nu I (hide sq).
  Proof. exists sq. split; [exact sq_V | reflexivity]. Qed.

  (** The z part of the history: [W₁ z 1; R₁ z 1; R₂ z 0]. *)
  Lemma sq_z_history :
    proj (C := C) 0 (hide sq) = [@BW C 1%positive 0 0 1 tt; @BR C 1%positive 1 0 tt 1; @BR C 2%positive 10 0 tt 0].
  Proof. reflexivity. Qed.

  (** The same trace, with the flushes visible, is a trace of the x86-TSO
      machine of Owens, Sarkar and Sewell (read/write fragment;
      [TSO.tso_traces]). *)
  Theorem q6_cells_x86_trace : TSO.Tr nat Nat.eq_dec (TSO.erase nat Nat.eq_dec sq).
  Proof.
    apply (proj1 (TSO.tso_traces nat Nat.eq_dec _)). exists sq.
    split; [split; [exact sq_V | apply wr_handle_order_of_chk; exact eq_refl] | reflexivity].
  Qed.

  (** *** Declarative form *)

  Definition sq_hist : list (block C) := hide sq.

  Definition po_of (l : list (block C)) : relation (block C) :=
    fun a b => In a l /\ In b l /\ b_tid a = b_tid b /\ b_handle a < b_handle b.

  (** The candidate of the 17 visible accesses; program order is thread
      order by handle. *)
  Definition sq_cand : cand C := {| ops := sq_hist; po := po_of sq_hist |}.

  Lemma sq_cand_wf : wf_cand sq_cand.
  Proof.
    constructor; cbn.
    - intros b Hb. repeat (destruct Hb as [<- | Hb]; [cbn; tauto |]). destruct Hb.
    - repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    - intros a b (Ha & Hb & Ht & _). auto.
    - intros a (_ & _ & _ & H). lia.
    - intros a b c (Ha & Hb & Ht1 & H1) (_ & Hc & Ht2 & H2). repeat split; auto; [congruence | lia].
    - intros a b Ha Hb Ht Hne.
      assert (Hh : b_handle a <> b_handle b).
      { intros Heq. repeat (destruct Ha as [<- | Ha]; [ repeat (destruct Hb as [<- | Hb];
              [ cbn in Ht, Heq; first [discriminate Ht | discriminate Heq | apply Hne; reflexivity] |]);
              destruct Hb |]). destruct Ha. }
      destruct (lt_dec (b_handle a) (b_handle b)) as [Hlt | Hge];
        [left; repeat split; auto | right; repeat split; auto; lia].
    - intros a b (_ & _ & _ & H) _ _. exact H.
  Qed.

  (** [pre = po]: the largest admissible relation contained in [po]
      ([admissible] also allows cross-thread edges). *)
  Lemma sq_admissible_po : admissible sq_cand I (po sq_cand).
  Proof.
    split; [| split].
    - intros a b [H _]. exact H.
    - intros x Hx. apply (po_irrefl sq_cand_wf x).
      assert (Htc : forall a b, tc (po sq_cand) a b -> po sq_cand a b)
        by (intros a b H; induction H as [a b H | a b c H1 IH1 H2 IH2];
            [exact H | eapply (po_trans sq_cand_wf); eauto]).
      apply Htc. exact Hx.
    - intros a b H. apply (po_dom sq_cand_wf) in H. tauto.
  Qed.

  Definition pochk (l : list (block C)) : bool :=
    forallb (fun i => forallb (fun j => implb (Nat.leb j i)
       (match nth_error l i, nth_error l j with
        | Some a, Some b => negb (Pos.eqb (b_tid a) (b_tid b)) || Nat.leb (b_handle b) (b_handle a)
        | _, _ => true
        end))
       (seq 0 (length l))) (seq 0 (length l)).

  Lemma sq_respects_po : respects sq_hist (po sq_cand).
  Proof.
    intros a b (Ha & Hb & Ht & Hh). apply In_nth_error in Ha as [i Hi]. apply In_nth_error in Hb as [j Hj].
    destruct (Nat.lt_ge_cases i j) as [Hij | Hji]; [exists i, j; auto |].
    exfalso. assert (Hc : pochk sq_hist = true) by exact eq_refl. unfold pochk in Hc. rewrite forallb_forall in Hc.
    assert (Hli : i < length sq_hist) by (apply nth_error_Some; congruence).
    assert (Hlj : j < length sq_hist) by (apply nth_error_Some; congruence).
    specialize (Hc i ltac:(apply in_seq; lia)). rewrite forallb_forall in Hc.
    specialize (Hc j ltac:(apply in_seq; lia)). rewrite Hi, Hj in Hc.
    apply Nat.leb_le in Hji. rewrite Hji in Hc. cbn in Hc. rewrite Ht, Pos.eqb_refl in Hc. cbn in Hc.
    apply Nat.leb_le in Hc. lia.
  Qed.

  (** D1 ∧ D2 (OMCA consistency for the TSO instance), with [pre] the
      whole program order.  This is [sq_nu] transported through the
      paper's own equivalence ([Equivalence.declarative_TSO], Theorem
      mem:thm:decl); it is not independent evidence about x86.  The
      independent x86 evidence is [q6_cells_x86_trace]. *)
  Theorem q6_cells_TSO_consistent : exists w, wf_witness sq_cand w /\ consistent sq_cand I w (po sq_cand).
  Proof.
    apply (proj2 (Equivalence.declarative_TSO nat Nat.eq_dec sq_cand sq_cand_wf (po sq_cand) sq_admissible_po)).
    exists sq_hist. split; [exact sq_nu |]. split; [apply Permutation_refl | exact sq_respects_po].
  Qed.

  (** ** The real-time iteration (Q6-2 at the cell level) *)

  (** Writer T2 = thread 2, reader T1 = thread 1.  T2's [x := 1] is
      issued (position 3) and still pending when T1 reads [x = 0]
      (position 5); T1 then sees an odd version and retries, and its
      second iteration reads (1,1) after the drain.  The run is
      forwarding-free: T1 does not write, and every read of T2 is served
      from memory with T2's buffer empty. *)
  Definition rt_cells : trace C :=
    [ @BR C 2%positive 0 3 tt 0;   (* T2: acq = XCHG s: reads 0 ... *)
      @BW C 2%positive 1 3 1 tt;   (* ... writes s := 1 ... *)
      @BF C 2%positive 100 3;      (* ... flushed at once *)
      @BW C 2%positive 2 1 1 tt;   (* T2: x := 1, pending *)
      @BR C 1%positive 0 3 tt 1;   (* T1: s = 1 (odd) *)
      @BR C 1%positive 1 1 tt 0;   (* T1: x = 0, from memory: T2's x := 1 is still pending *)
      @BR C 1%positive 2 2 tt 0;   (* T1: y = 0 *)
      @BR C 1%positive 3 3 tt 1;   (* T1: s = 1: retry *)
      @BW C 2%positive 3 2 1 tt;   (* T2: y := 1 *)
      @BF C 2%positive 101 1; @BF C 2%positive 102 2;  (* the drain before rel *)
      @BR C 2%positive 4 3 tt 1;   (* T2: rel = XCHG s: reads 1 ... *)
      @BW C 2%positive 5 3 2 tt;   (* ... writes s := 2 ... *)
      @BF C 2%positive 103 3;      (* ... flushed at once *)
      @BR C 1%positive 4 3 tt 2;   (* T1: s = 2 *)
      @BR C 1%positive 5 1 tt 1;   (* T1: x = 1 *)
      @BR C 1%positive 6 2 tt 1;   (* T1: y = 1 *)
      @BR C 1%positive 7 3 tt 2 ]. (* T1: s = 2: read() = (1,1) *)

  Lemma rt_cells_locked : locked_rmw rt_cells 0 2%positive 3 /\ locked_rmw rt_cells 11 2%positive 3.
  Proof. split; locked. Qed.

  (** In the history, T2's write of [x] precedes T1's read of [x], which
      returns 0. *)
  Lemma rt_cells_write_before_read :
    nth_error (hide rt_cells) 2 = Some (@BW C 2%positive 2 1 1 tt) /\
    nth_error (hide rt_cells) 4 = Some (@BR C 1%positive 1 1 tt 0).
  Proof. split; reflexivity. Qed.

  (** ... and T2's [x := 1] is still pending at that point. *)
  Lemma rt_cells_pending :
    In (@BW C 2%positive 2 1 1 tt) (pend 2%positive (firstn 5 rt_cells)).
  Proof. cbn. tauto. Qed.

  Theorem rt_cells_V : V I rt_cells.
  Proof. apply V_of_chk; exact eq_refl. Qed.

  Theorem rt_cells_nu : nu I (hide rt_cells).
  Proof. exists rt_cells. split; [exact rt_cells_V | reflexivity]. Qed.

  Theorem rt_cells_x86_trace : TSO.Tr nat Nat.eq_dec (TSO.erase nat Nat.eq_dec rt_cells).
  Proof.
    apply (proj1 (TSO.tso_traces nat Nat.eq_dec _)). exists rt_cells.
    split; [split; [exact rt_cells_V | apply wr_handle_order_of_chk; exact eq_refl] | reflexivity].
  Qed.

  (** ** Reviewer A's test: store buffering with own reads, on plain cells *)

  (** popl2027-reviews.md:69-81 and Appendix/Mem.tex:5-14:
<<
      W x 1; R x = 1; R y = 0   ||   W y 1; R y = 1; R x = 0
>>
      with x = 1, y = 2.  Each thread's own read is forwarded from its
      buffer; each other read is served from memory before the other
      thread's write is flushed. *)
  Definition sbrfi : trace C :=
    [ @BW C 1%positive 0 1 1 tt;   (* T1: x := 1 *)
      @BR C 1%positive 1 1 tt 1;   (* T1: x = 1, forwarded *)
      @BR C 1%positive 2 2 tt 0;   (* T1: y = 0, from memory *)
      @BW C 2%positive 0 2 1 tt;   (* T2: y := 1 *)
      @BR C 2%positive 1 2 tt 1;   (* T2: y = 1, forwarded *)
      @BR C 2%positive 2 1 tt 0;   (* T2: x = 0, from memory *)
      @BF C 1%positive 100 1; @BF C 2%positive 101 2 ].

  Theorem sbrfi_V : V I sbrfi.
  Proof. apply V_of_chk; exact eq_refl. Qed.

  Theorem sbrfi_nu : nu I (hide sbrfi).
  Proof. exists sbrfi. split; [exact sbrfi_V | reflexivity]. Qed.

  Theorem sbrfi_x86_trace : TSO.Tr nat Nat.eq_dec (TSO.erase nat Nat.eq_dec sbrfi).
  Proof.
    apply (proj1 (TSO.tso_traces nat Nat.eq_dec _)). exists sbrfi.
    split; [split; [exact sbrfi_V | apply wr_handle_order_of_chk; exact eq_refl] | reflexivity].
  Qed.

End SeqLockQ6Mem.
