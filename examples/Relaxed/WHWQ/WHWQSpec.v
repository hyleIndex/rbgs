(** * WHWQSpec: the signatures of the weak Herlihy–Wing queue case study

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P1.  Two relaxed
    signatures with their sequential specifications.  Nothing here is
    specific to the implementation.

    ** Overlay: the queue [FQ A]

    - Operations [enq (v : A) : unit] and [deq : A].  The case study uses
      [A := positive] (author decision D4), so that the implementation can
      use [0] as null; the queue itself is generic in [A].
    - Semi-independence [qsi]: [qsi o1 o2] holds exactly when [o1] is an
      enqueue and [o2] is a dequeue.  So a dequeue may be linearized before
      an older, still pending enqueue of its own thread; every other
      same-thread pair keeps its invocation order.  This is
      I_WkQueue = {(enq, deq)} of Appendix/WHWQueue.tex:63.
    - Modes: [enq ↦ LFence], [deq ↦ RFence].  These are the largest modes
      that [RelaxedSig.well_formed] allows together with [qsi] (the left
      operation of a semi-independent pair must be at most [LFence], the
      right one at most [RFence]).  The current draft fixes no modes for
      the queue (its definition in spec.tex is not input); Example 3.11
      of the anonymized submission's TR used these same modes (that PDF
      is not in this repository or in the current .tex sources).
      They only matter when the queue is tensored with another object, and
      no result of this case study depends on them.  Under the tensor rule
      they would promise clients message-passing order through the queue
      (a write before an [enq] is ordered before a read after the matching
      [deq]); nothing here validates that promise (review WHWQ-m-4).
    - [δQ]: the FIFO queue with a blocking dequeue.  [deq] has no
      transition on the empty queue, so no completed dequeue returns
      "empty"; this is the blocking specification of the author response
      to Review B, B6 (popl2027-reviews.md:541–545).  It deliberately
      changes the meaning of the submitted specification: there
      (Example 3.11 of the submission, and the commented-out spec.tex:87)
      [deq] returns [N + {⊥}] and returns [⊥] on the empty queue; here
      [deq] returns a value and has no step on the empty queue.
      [νQ := seq_legal δQ []] is the set of legal sequential traces.
      [POQueueRExample.b6_enq_deq] proves the consequence for the
      reviewer's single-thread example [enq(v); deq()].

    ** Underlay: RCMem [ERC] (Appendix/2Counter.tex:6–13)

    - Locations and values are [nat].  The operations are those of
      [Mem_Access[Locs]] extended with the RMWs: [RCRd l mR], [RCWr l v mW],
      [RCFaa l n mR mW], [RCXchg l v mR mW], [RCCas l e n mR mW], with read
      modes [RRlx | RAcq] and write modes [WRlx | WRel].
    - Modes: a read is [Local] ([rlx]) or [RFence] ([acq]); a write is
      [Local] ([rlx]) or [LFence] ([rel]); an RMW gets the join of its read
      and write modes ("The exported mode of an RMW is the join of its read
      and write modes", 2Counter.tex:13).
    - Semi-independence [rc_si] (author decision D2′, 2026-10-21; option
      (b) of review WHWQ-M-1): [ERC] is read as the tensor of per-location
      cells, each with empty internal I, so [rc_si] is the cross-component
      rule of Def. tensor-sig (trace.tex:196–205) applied to every
      operation with its exported mode: the two operations are at
      different locations, the older one has mode at most [LFence] and
      the younger one at most [RFence].  RMWs take part with their join
      modes.  Equivalently ([rc_si_iff]): different locations, the older
      operation has no acquire read part and the younger one no release
      write part.  On plain reads and writes this is the relation of
      Ex. rc-cell, whose preserved order is [po_loc ∪ [acq];po ∪ po;[rel]]
      (trace.tex:297–301; [rc_si_plain_iff]).
    - This deliberately departs from the paper's RCMem, whose internal
      relation has "no RMW pairs" (2Counter.tex:13).  The paper's RCMem,
      and the Counter_xy appendix that uses it, must be updated to match
      (the Coq Counter_xy development uses its own signature and is not
      affected).  The new pairs are C11-style reorderings (an acquire
      prevents later operations from moving before it, a release prevents
      earlier ones from moving after it); x86-TSO, where an exchange is a
      locked full barrier, does not exhibit them, and ARMv8, whose
      release/acquire accesses are RCsc, may not exhibit the WHW pair
      (store rel, xchg acq) either.  Open check for the authors, against
      primary sources: the Arm ARM and the ARMv8 axiomatic model (Pulte et
      al., POPL 2018) for the hardware, RC11 (Lahav et al., PLDI 2017) for
      C11; it decides whether the queue's weak behaviour is presented as
      hardware-level or C11-level.
    - Consequence for the WHW code ([whw_rc_si] and the lemmas after it).
      Pairwise, a younger [xchg] may overtake an older [faa], and a
      younger [ld] or [xchg] may overtake an older [store] to another
      location; nothing overtakes an older [ld] or [xchg] (acquire), and a
      [faa] or [store] overtakes nothing (release).  In an execution, a
      dequeue starts with [ld] at the counter's location, which keeps every
      older [faa] of its thread first, so what a dequeue's [xchg] may
      overtake is the [store] of an older enqueue of its thread (at another
      slot).  So a dequeue's successful [xchg] (its linearization point)
      may precede the store of an older pending enqueue of its thread,
      which is the case [I(enq, deq)] is for, while a thread's [faa] still
      waits for all of its older operations (the per-thread condition of
      [POQueueR]).
    - Decision D3′ (same date): the exchange is [(acq, rlx)], as asked in
      Review B's minor comment (popl2027-reviews.md:301), replacing the
      appendix's [rel]; its mode is [RFence].
    - [δRC]: the sequential register file ("globally atomic register
      executions", 2Counter.tex:13).  [RCRd] returns the value; [RCWr]
      writes; [RCFaa] returns the old value and adds; [RCXchg] returns the
      old value and replaces it; [RCCas] reports whether the expected
      value matched and updates on success.  Memory is a function
      [nat -> nat]; nothing below needs functional extensionality.

    ** Limitations

    - The paper's RCMem is a target that the concrete underlay is assumed
      to refine (2Counter.tex:13).  As there, no memory model from
      [memory/] is connected to [ERC] here.
    - Handles are [nat] on both signatures, as in the other RLHL case
      studies. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedHoareSpec.

Import ListNotations.

Module WHWQSpec.
  Import RelaxedSig.
  Import RelaxedTraceLin.

  (** ** The overlay queue *)

  Section Queue.
    Context (A : Type).

    Inductive QOp : Type :=
    | enq (v : A)
    | deq.

    Definition q_ar (o : QOp) : Type :=
      match o with
      | enq _ => unit
      | deq => A
      end.

    Canonical Structure QEff : Sig.t := {| Sig.op := QOp; Sig.ar := q_ar |}.

    (** I_WkQueue = {(enq, deq)}: an older enqueue and a younger dequeue of
        the same thread may be reordered. *)
    Definition qsi (o1 o2 : QOp) : Prop :=
      match o1, o2 with
      | enq _, deq => True
      | _, _ => False
      end.

    Definition q_mode (o : QOp) : FenceMode :=
      match o with
      | enq _ => LFence
      | deq => RFence
      end.

    Definition FQ : RelaxedSig.t :=
      {|
        RelaxedSig.effect := QEff;
        RelaxedSig.handle := nat;
        RelaxedSig.semi_independent := qsi;
        RelaxedSig.mode := q_mode;
      |}.

    Lemma FQ_wf : RelaxedSig.well_formed FQ.
    Proof.
      constructor.
      - intros [v |] H; exact H.
      - intros [v1 |] [v2 |] H; cbn in H |- *; try contradiction; exact Logic.I.
      - intros [v1 |] [v2 |] H; cbn in H |- *; try contradiction; exact Logic.I.
    Qed.

    Lemma qsi_iff o1 o2 : qsi o1 o2 <-> (exists v, o1 = enq v) /\ o2 = deq.
    Proof.
      destruct o1 as [v1 |], o2 as [v2 |]; cbn; split.
      - contradiction.
      - intros (_ & H). discriminate.
      - intros _. split; [exists v1; reflexivity | reflexivity].
      - intros _. exact Logic.I.
      - contradiction.
      - intros ((v & H) & _). discriminate.
      - contradiction.
      - intros ((v & H) & _). discriminate.
    Qed.

    (** The FIFO queue with a blocking dequeue. *)
    Definition δQ : list A -> forall o : Sig.op (RelaxedSig.effect FQ), Sig.ar o -> list A -> Prop :=
      fun q o =>
        match o as o0 return Sig.ar o0 -> list A -> Prop with
        | enq v => fun _ q' => q' = q ++ [v]
        | deq => fun r q' => q = r :: q'
        end.

    Lemma δQ_deq_nonempty q (r : A) q' : δQ q deq r q' -> q <> [].
    Proof. cbn. intros -> H. discriminate. Qed.

    (** The legal sequential traces. *)
    Definition νQ : list (Op FQ) -> Prop := @RelaxedHoareSpec.seq_legal FQ (list A) δQ [].

  End Queue.

  Arguments enq {A} v.
  Arguments deq {A}.

  (** ** The underlay RCMem *)

  Variant RMode : Type := RRlx | RAcq.
  Variant WMode : Type := WRlx | WRel.

  Inductive RCOp : Type :=
  | RCRd (l : nat) (mr : RMode)
  | RCWr (l : nat) (v : nat) (mw : WMode)
  | RCFaa (l : nat) (n : nat) (mr : RMode) (mw : WMode)
  | RCXchg (l : nat) (v : nat) (mr : RMode) (mw : WMode)
  | RCCas (l : nat) (e n : nat) (mr : RMode) (mw : WMode).

  Definition rc_ar (o : RCOp) : Type :=
    match o with
    | RCWr _ _ _ => unit
    | RCCas _ _ _ _ _ => bool
    | _ => nat
    end.

  Canonical Structure RCEff : Sig.t := {| Sig.op := RCOp; Sig.ar := rc_ar |}.

  Definition rc_loc (o : RCOp) : nat :=
    match o with
    | RCRd l _ | RCWr l _ _ | RCFaa l _ _ _ | RCXchg l _ _ _ | RCCas l _ _ _ _ => l
    end.

  Definition rmode (m : RMode) : FenceMode :=
    match m with RRlx => Local | RAcq => RFence end.

  Definition wmode (m : WMode) : FenceMode :=
    match m with WRlx => Local | WRel => LFence end.

  (** The join in the lattice [Local < LFence, RFence < Fence]. *)
  Definition fjoin (a b : FenceMode) : FenceMode :=
    match a, b with
    | Local, x | x, Local => x
    | LFence, LFence => LFence
    | RFence, RFence => RFence
    | _, _ => Fence
    end.

  Lemma fjoin_upper_l a b : a ≤f fjoin a b.
  Proof. destruct a, b; exact Logic.I. Qed.

  Lemma fjoin_upper_r a b : b ≤f fjoin a b.
  Proof. destruct a, b; exact Logic.I. Qed.

  Lemma fjoin_least a b c : a ≤f c -> b ≤f c -> fjoin a b ≤f c.
  Proof. destruct a, b, c; cbn; tauto. Qed.

  Definition rc_mode (o : RCOp) : FenceMode :=
    match o with
    | RCRd _ mr => rmode mr
    | RCWr _ _ mw => wmode mw
    | RCFaa _ _ mr mw | RCXchg _ _ mr mw | RCCas _ _ _ mr mw => fjoin (rmode mr) (wmode mw)
    end.

  (** Plain reads and writes; RMWs are not plain. *)
  Definition rc_plain (o : RCOp) : Prop :=
    match o with
    | RCRd _ _ | RCWr _ _ _ => True
    | _ => False
    end.

  (** The tensor rule over per-location cells with empty internal I
      (decision D2′; see the header). *)
  Definition rc_si (o1 o2 : RCOp) : Prop :=
    rc_loc o1 <> rc_loc o2 /\ rc_mode o1 ≤f LFence /\ rc_mode o2 ≤f RFence.

  Definition ERC : RelaxedSig.t :=
    {|
      RelaxedSig.effect := RCEff;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := rc_si;
      RelaxedSig.mode := rc_mode;
    |}.

  Lemma ERC_wf : RelaxedSig.well_formed ERC.
  Proof.
    constructor.
    - intros o (Hl & _). exact (Hl eq_refl).
    - intros o1 o2 (_ & H & _). exact H.
    - intros o1 o2 (_ & _ & H). exact H.
  Qed.

  (** The acquire part (a read with mode acq) and the release part (a
      write with mode rel) of an operation, RMWs included. *)
  Definition rc_acq (o : RCOp) : Prop :=
    match o with
    | RCRd _ RAcq | RCFaa _ _ RAcq _ | RCXchg _ _ RAcq _ | RCCas _ _ _ RAcq _ => True
    | _ => False
    end.

  Definition rc_rel (o : RCOp) : Prop :=
    match o with
    | RCWr _ _ WRel | RCFaa _ _ _ WRel | RCXchg _ _ _ WRel | RCCas _ _ _ _ WRel => True
    | _ => False
    end.

  Lemma rc_mode_le_lfence o : rc_mode o ≤f LFence <-> ~ rc_acq o.
  Proof.
    destruct o as [l [|] | l v [|] | l n [|] [|] | l v [|] [|] | l e n [|] [|]]; cbn; intuition.
  Qed.

  Lemma rc_mode_le_rfence o : rc_mode o ≤f RFence <-> ~ rc_rel o.
  Proof.
    destruct o as [l [|] | l v [|] | l n [|] [|] | l v [|] [|] | l e n [|] [|]]; cbn; intuition.
  Qed.

  (** A younger operation may overtake an older one exactly when they are
      at different locations, the older one does not acquire and the
      younger one does not release. *)
  Lemma rc_si_iff o1 o2 :
    rc_si o1 o2 <-> rc_loc o1 <> rc_loc o2 /\ ~ rc_acq o1 /\ ~ rc_rel o2.
  Proof. unfold rc_si. rewrite rc_mode_le_lfence, rc_mode_le_rfence. reflexivity. Qed.

  (** Ex. rc-cell (trace.tex:297–301): on plain reads and writes the
      preserved order [po \ I_RC] is [po_loc ∪ [acq];po ∪ po;[rel]], i.e. a
      pair may be reordered exactly when the locations differ, the older
      operation is not an acquire read and the younger one is not a release
      write.  This part is unchanged by decision D2′. *)
  Definition rc_acq_read (o : RCOp) : Prop :=
    match o with RCRd _ RAcq => True | _ => False end.

  Definition rc_rel_write (o : RCOp) : Prop :=
    match o with RCWr _ _ WRel => True | _ => False end.

  Lemma rc_si_plain_iff o1 o2 :
    rc_plain o1 -> rc_plain o2 ->
    (rc_si o1 o2 <-> rc_loc o1 <> rc_loc o2 /\ ~ rc_acq_read o1 /\ ~ rc_rel_write o2).
  Proof.
    intros H1 H2. rewrite rc_si_iff.
    destruct o1 as [l1 [|] | l1 v1 [|] | | |], o2 as [l2 [|] | l2 v2 [|] | | |];
      cbn in H1, H2 |- *; try contradiction; tauto.
  Qed.

  (** The register file. *)
  Definition Mem : Type := nat -> nat.

  Definition mem_upd (m : Mem) (l v : nat) : Mem :=
    fun l' => if Nat.eqb l l' then v else m l'.

  Lemma mem_upd_same m l v : mem_upd m l v l = v.
  Proof. unfold mem_upd. rewrite Nat.eqb_refl. reflexivity. Qed.

  Lemma mem_upd_other m l v l' : l <> l' -> mem_upd m l v l' = m l'.
  Proof. intros H. unfold mem_upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

  Definition mem0 : Mem := fun _ => 0.

  Definition δRC : Mem -> forall o : Sig.op (RelaxedSig.effect ERC), Sig.ar o -> Mem -> Prop :=
    fun m o =>
      match o as o0 return Sig.ar o0 -> Mem -> Prop with
      | RCRd l _ => fun r m' => r = m l /\ m' = m
      | RCWr l v _ => fun _ m' => m' = mem_upd m l v
      | RCFaa l n _ _ => fun r m' => r = m l /\ m' = mem_upd m l (m l + n)
      | RCXchg l v _ _ => fun r m' => r = m l /\ m' = mem_upd m l v
      | RCCas l e n _ _ => fun b m' =>
          (m l = e /\ b = true /\ m' = mem_upd m l n) \/
          (m l <> e /\ b = false /\ m' = m)
      end.

  Lemma δRC_total m (o : RCOp) : exists r m', δRC m o r m'.
  Proof.
    destruct o as [l mr | l v mw | l n mr mw | l v mr mw | l e n mr mw]; cbn.
    - exists (m l), m. split; reflexivity.
    - exists tt, (mem_upd m l v). reflexivity.
    - exists (m l), (mem_upd m l (m l + n)). split; reflexivity.
    - exists (m l), (mem_upd m l v). split; reflexivity.
    - destruct (Nat.eq_dec (m l) e) as [He | He].
      + exists true, (mem_upd m l n). left. auto.
      + exists false, m. right. auto.
  Qed.

  Lemma δRC_det m (o : RCOp) r1 m1 r2 m2 : δRC m o r1 m1 -> δRC m o r2 m2 -> r1 = r2 /\ m1 = m2.
  Proof.
    destruct o as [l mr | l v mw | l n mr mw | l v mr mw | l e n mr mw]; cbn.
    - intros [-> ->] [-> ->]. auto.
    - destruct r1, r2. intros -> ->. auto.
    - intros [-> ->] [-> ->]. auto.
    - intros [-> ->] [-> ->]. auto.
    - intros [(He & -> & ->) | (He & -> & ->)] [(He' & -> & ->) | (He' & -> & ->)]; auto; contradiction.
  Qed.

  (** ** The operations of the WHW code (Appendix/WHWQueue.tex:14–17, Fig.
      "WHW Queue implementation"), with author decision D3′ for the
      exchange: [FAA(q, 1, rel)], [store(q + i + 1, v, rel)],
      [ld(q, acq)], [atomic-xchg(q + i, null, (acq, rlx))] (the appendix
      prints [rel] for the exchange).

      Slot convention: location 0 is the counter [q]; slot [s] is location
      [S s].  An enqueue whose [FAA] returns [i] owns slot [i] and stores
      at location [i + 1], as in the paper.  The paper's dequeue loop index
      [i ∈ 1..t] is location [i], i.e. slot [i - 1]: [op_xchg s] is the
      paper's exchange at [q + (s + 1)].  The FAA's single mode "rel" is
      read as (rlx, rel). *)

  Definition op_faa : RCOp := RCFaa 0 1 RRlx WRel.
  Definition op_store (slot v : nat) : RCOp := RCWr (S slot) v WRel.
  Definition op_ld : RCOp := RCRd 0 RAcq.
  Definition op_xchg (slot : nat) : RCOp := RCXchg (S slot) 0 RAcq WRlx.

  Definition whw_op (o : RCOp) : Prop :=
    o = op_faa \/ (exists s v, o = op_store s v) \/ o = op_ld \/ exists s, o = op_xchg s.

  (** The reorderable same-thread pairs among the WHW operations: a
      younger [xchg] may overtake an older [faa], and a younger [ld] or
      [xchg] may overtake an older [store] to another slot. *)
  Lemma whw_rc_si o1 o2 : whw_op o1 -> whw_op o2 -> rc_si o1 o2 ->
    (o1 = op_faa /\ exists s, o2 = op_xchg s) \/
    (exists s v, o1 = op_store s v /\ (o2 = op_ld \/ exists s', o2 = op_xchg s' /\ s' <> s)).
  Proof.
    intros H1 H2 Hsi.
    destruct H1 as [-> | [(s1 & v1 & ->) | [-> | (s1 & ->)]]];
      destruct H2 as [-> | [(s2 & v2 & ->) | [-> | (s2 & ->)]]];
      destruct Hsi as (Hl & Hm1 & Hm2); cbn in *; try contradiction;
      try (exfalso; apply Hl; reflexivity).
    - left. split; [reflexivity | exists s2; reflexivity].
    - right. exists s1, v1. split; [reflexivity | left; reflexivity].
    - right. exists s1, v1. split; [reflexivity |]. right. exists s2. split; [reflexivity | congruence].
  Qed.

  (** Each of these pairs is semi-independent. *)
  Lemma rc_si_faa_xchg s : rc_si op_faa (op_xchg s).
  Proof. split; [discriminate | split; exact Logic.I]. Qed.

  Lemma rc_si_store_ld s v : rc_si (op_store s v) op_ld.
  Proof. split; [discriminate | split; exact Logic.I]. Qed.

  Lemma rc_si_store_xchg s v s' : s' <> s -> rc_si (op_store s v) (op_xchg s').
  Proof. intros H. split; [cbn; congruence | split; exact Logic.I]. Qed.

  (** Nothing overtakes an older [ld] or [xchg], and a [faa] or [store]
      overtakes nothing.  In particular a thread's [faa] is issued after
      all of its older operations (the per-thread condition of
      [POQueueR]), and a dequeue's scan keeps its order. *)
  Lemma rc_si_not_after_acq o : ~ rc_si op_ld o /\ forall s, ~ rc_si (op_xchg s) o.
  Proof. split; [intros (_ & H & _); exact H | intros s (_ & H & _); exact H]. Qed.

  Lemma rc_si_not_before_rel o : ~ rc_si o op_faa /\ forall s v, ~ rc_si o (op_store s v).
  Proof. split; [intros (_ & _ & H); exact H | intros s v (_ & _ & H); exact H]. Qed.

End WHWQSpec.
