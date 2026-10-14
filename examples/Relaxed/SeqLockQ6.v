(** * SeqLockQ6: store forwarding against the SeqLock ⊎ COH[z] interface

    Question Q6 (.rocq-review/research-intent.md §7): is the interface of
    the COH SeqLock example, ν_SeqLock ⊗ ν_COH[z] with the overlay
    semi-independence [SeqLockProg.findep], sound for a memory with store
    forwarding?  The outcome in question is
<<
    T1: zw(1); zr() = 1; read() = (0,0)   ||   T2: write(1,1); read() = (1,1); zr() = 0
>>
    It is store buffering with own reads ("SB+rfi"), the test of
    Reviewer A (popl2027-reviews.md:69-81), lifted through the SeqLock
    object.  The plain-cell version of the same test is Appendix/Mem.tex:5-14
    of the TR, which introduces the buffered cell for this reason.  This
    file contains what is kernel-checked about Q6 at the object and
    underlay levels.  The memory/ (cell-level) evidence is in
    [SeqLockQ6Mem]; Reviewer A's own two-location test, against register
    cells, is in [RegisterSB].  Every result is for both table profiles
    [rc] and over the plain TicketLock signature [SeqLockCOH.plainTL].
    This confirms Reviewer A's objection for the running example; it does
    not answer it (the answer is the buffered redesign).

    All results are about complete traces ([RelaxedTraceLin.rel_lin]
    requires every invoked operation to respond).  The [_any] negative
    theorems hold trivially on incomplete traces, which are never relaxed
    linearizable in this sense (M-1).

    Part 1, overlay (the exported interface).
    - [q6_not_rel_lin]: the trace [q6_trace 0] of the outcome, in which all
      six invocations precede all six responses, is not relaxed
      linearizable w.r.t. ν_SeqLock ⊗ ν_COH[z] and [findep rc].  [rhb]
      keeps four same-thread edges: zw<zr (same component), zr<read
      ([dto DR Rmb] = true), write<read (same component), and read<zr
      ([read_zr_dependent]).  Either read()=(0,0) precedes write(1,1) in the
      witness, and then zw(1) precedes zr()=0, which ν_COH[z] forbids; or
      write(1,1) precedes read()=(0,0), which ν_SeqLock forbids
      ([nuF_all_sl_after]).
      [q6_not_rel_lin_any] states the same for every complete trace, with
      any selector, whose responses are those of the outcome and which has
      the four invocation orders ([q6_shape]).  It is that general because
      the proof uses only the four same-thread edges and the values, never
      a real-time edge.  [q6_trace] has no response before an invocation,
      so only the same-thread clause of [rhb] applies to it.
    - Controls, all relaxed linearizable.  [q6_zr1_rel_lin]: the same
      trace with T2's zr() = 1.  [sb_rel_lin]: plain store buffering on
      the object (T1: zw(1); read()=(0,0) ‖ T2: write(1,1); zr()=0, with
      neither own read).  [d1_rel_lin]: only T1's zr() dropped (T1:
      zw(1); read()=(0,0) ‖ T2: write(1,1); read()=(1,1); zr()=0).
      [d2_rel_lin]: only T2's read() dropped (T1: zw(1); zr()=1;
      read()=(0,0) ‖ T2: write(1,1); zr()=0).
      So the refutation needs both same-thread chains.  T1's chain
      zw(1) < zr()=1 < read() goes through the forwarded read and orders
      T1's write before its later read of another object; x86 does not
      enforce that order (the store may still be buffered).  T2's chain
      write(1,1) < read()=(1,1) < zr() goes through T2's own read after
      the XCHG drain; that order x86 does enforce.  The transitivity of
      Reviewer A's sentence happens in T1's chain.

    Part 2, underlay at witness level ([SeqLockCOH.WF]).
    - [q6_underlay_no_WF]: for every witness [w], the programs [q6p0] =
      [BZw 1; BZr 1; BR [] 0 0 0] (T1) and [q6p1] = [BW 1 1; BR [] 2 1 1;
      BZr 0] (T2) have no [WF] execution.  The cycle is
      WrZ1 <obj RdZ1 <tab rmb <tab RdX0 <val WrX1 <obj RdX1 <tab rmb <tab RdZ0 <val WrZ1
      (obj: same object; tab: [WindowTable.dto]; val: register values,
      [field_const]).
    - Control [ctl_wf]: with T2's zr() = 1 ([q6p1z1]) a [WF] execution
      exists.

    Part 3, underlay at trace level (the hypothesis of
    [SeqLockModule.seqlock_module_rel_lin]).
    - [q6_underlay_not_rel_lin]: the 42-event history [U] of the two
      programs (the 21 invocations, T1's then T2's, then the 21 responses)
      is not relaxed linearizable w.r.t. [sindep] and
      [BL.nuE_all SL.comp_dec SLM.compE (SLM.nuEc rc plainTL)].  This is
      the form of the underlay hypothesis of [seqlock_module_rel_lin].
      The cycle is the one of Part 2, with [nuEc] in place of [WF]
      ([nuE_x_after], [nuE_z_after]).
    - [q6_underlay_not_rel_lin_any]: the same for every complete trace
      with these 21 responses and the six same-thread invocation orders
      that the proof uses ([q6u_shape]).  It is that general because the
      proof uses only same-thread edges and the values.  [U] is not a
      trace of the module [SeqLockProg.M]: the module waits for the
      responses of [Acq] and [GT] before its next invocation.  The [_any]
      form also covers the underlay part of any module trace that has
      these responses and invocation orders
      ([q6_module_underlay_not_rel_lin]; similarly
      [rt_module_underlay_not_rel_lin] for Part 4).

    Part 4, the real-time obstruction for the registers x and y (task
    Q6-2).  A call of the module semantics responds when its response
    event is emitted.  Suppose an operational buffered memory emits the
    response of a plain write when the write is issued, i.e. when it
    enters the store buffer ("writes respond at issue").  Then a write's
    response can precede a read of the same location by another thread,
    and that read can still return the old value.
    - [rt_iteration_not_rel_lin]: the underlay history [rt_trace] of one
      write(1,1) (thread 2, [rtp_w]) and one read() (thread 1, [rtp_r] =
      [BR [(1,0,0)] 2 1 1]).  The read has one failed iteration (GT = 1,
      odd; x = 0, y = 0; TT 1 = retry) and one successful iteration
      (GT = 2, (1,1)).  Every call responds before the next call of any
      thread is invoked.  The writer's WrX(1) responds (event 5) before
      the reader invokes RdX of the failed iteration (event 10), which
      returns 0.  The history is not relaxed linearizable w.r.t. [sindep]
      and the same [nuEc].  The real-time clause of [rhb] puts WrX(1)
      before RdX in the witness, and x is a register written only by
      WrX(1).
      [rt_iteration_not_rel_lin_any] proves the same for every complete
      trace with these 18 responses in which the WrX(1) response precedes
      the RdX invocation ([rt_shape]).  Only that real-time edge and the
      values are used: the failed iteration and the later success make
      the execution realistic but are not needed for the refutation.
      Only x is kernel-checked.  y follows by symmetry (a WrY(1) response
      before an RdY = 0 invocation); it is not stated here.
    - Control [rt_iteration_overlap_rel_lin]: the same 36 events, with the
      WrX(1) response moved after the RdX invocation ([rt_overlap_trace];
      the two calls now overlap), are relaxed linearizable.  The witness
      is [rt_W], which places RdX = 0 before WrX(1).
    - The SeqLock behaves correctly on [rt_trace], informally: the failed
      iteration retries, and the read returns (1,1).  No module execution
      with this underlay is constructed (m-27).  The hand-mapped cell image
      of the run is in ν_TSO ([SeqLockQ6Mem.rt_cells_nu]) and is a trace of
      the x86-TSO machine ([SeqLockQ6Mem.rt_cells_x86_trace]).
    - The run is forwarding-free: in its cell image the reader never
      writes, and the writer reads (in its locked RMWs) only with an empty
      buffer.  The refutation is the general fact
      that a store buffer whose writes respond at issue is not
      linearizable to a register; nothing in it is specific to the
      SeqLock.
    - Outcome: the obstruction holds.  Under "writes respond at issue",
      the register specifications of x and y, not only that of z, are
      refuted by an execution that a store-buffer memory produces and on
      which the SeqLock is correct.  So x and y must be buffered as well;
      a z-only buffering variant does not suffice under this convention.
      The obstruction does not apply if a write responds only once it is
      published.  This file does not examine that convention.
    - Consequence for the register-cell results ([seqlock_module_rel_lin]
      and the files built on the same underlay specification): with
      issue-time responses their hypothesis can fail even on
      forwarding-free runs ([rt_iteration_not_rel_lin_any]).  They cover
      underlays in which each write is visible to all
      threads when it responds and no read is forwarded.  How the paper
      names that class is the author's decision.

    Part 5, module traces.
    - [q6_module_hypothesis_fails]: by contraposition of
      [seqlock_module_rel_lin], every complete execution of [M rc plainTL],
      over any underlay [VE], whose overlay part has the Q6 shape has an
      underlay part that is not relaxed linearizable w.r.t. [nuEc].
    - So [seqlock_module_rel_lin] is not contradicted by Q6: on such an
      execution its hypothesis fails, and the theorem says nothing about
      it.  What Q6 shows is that the interface and the register underlay
      specification exclude a behaviour that x86-TSO allows by the
      derivation below; the proof of the module theorem is not affected.
    - This file does not show that such a module execution exists over an
      operational underlay; no [VE] is constructed here.

    Not kernel-checked (derivations).
    - Hardware verdicts: x86-TSO allows the Q6 outcome, and ARMv8 allows
      it.  Both are hand derivations (.rocq-review/buffered-cell-plan.md,
      "Q6 status").  herd7 is not installed, and the litmus tests below
      have never been run.
      x86: rmb/wmb are compiler barriers; acq/rel are XCHG; get_ticket and
      test_ticket are plain loads of s.  T1's store to z stays in its
      buffer: its load of z is forwarded (1), and its loads of s, x, y, s
      read memory (0).  T2's XCHGs drain its buffer, it reads (1,1), and
      its load of z reads memory (0).  T1's buffer drains last.  In the
      axiomatic x86tso model, T1's store to z has no outgoing ghb edge, so
      no cycle can pass through it.
      ARMv8 (rmb = DMB LD, wmb = DMB ST, acq = SWPA, rel = SWPL): T1's STR z
      is a sink of ob.  Its only reader is rfi, DMB LD orders only earlier
      loads, and T1 has no later store, release or DMB SY.
<<
    X86 SeqLockZ+rfi
    { x=0; y=0; z=0; s=0; }
     P0          | P1           ;
     MOV [z],$1  | MOV EAX,$1   ;
     MOV EAX,[z] | XCHG [s],EAX ;
     MOV EBX,[s] | MOV [x],$1   ;
     MOV ECX,[x] | MOV [y],$1   ;
     MOV EDX,[y] | MOV EBX,$2   ;
     MOV ESI,[s] | XCHG [s],EBX ;
                 | MOV ECX,[s]  ;
                 | MOV EDX,[x]  ;
                 | MOV ESI,[y]  ;
                 | MOV EDI,[s]  ;
                 | MOV EAX,[z]  ;
    exists (0:EAX=1 /\ 0:EBX=0 /\ 0:ECX=0 /\ 0:EDX=0 /\ 0:ESI=0 /\
            1:ECX=2 /\ 1:EDX=1 /\ 1:ESI=1 /\ 1:EDI=2 /\ 1:EAX=0)
    (expected with herd7 -model x86tso.cat: Allowed)

    AArch64 SeqLockZ+rfi
    { 0:X1=z; 0:X3=s; 0:X4=x; 0:X5=y; 1:X1=z; 1:X3=s; 1:X4=x; 1:X5=y; }
     P0          | P1               ;
     MOV W0,#1   | MOV W0,#1        ;
     STR W0,[X1] | SWPA W0,W2,[X3]  ;
     LDR W2,[X1] | DMB ST           ;
     LDR W6,[X3] | STR W0,[X4]      ;
     DMB LD      | STR W0,[X5]      ;
     LDR W7,[X4] | DMB ST           ;
     LDR W8,[X5] | MOV W6,#2        ;
     DMB LD      | SWPL W6,W9,[X3]  ;
     LDR W9,[X3] | LDR W10,[X3]     ;
                 | DMB LD           ;
                 | LDR W11,[X4]     ;
                 | LDR W12,[X5]     ;
                 | DMB LD           ;
                 | LDR W13,[X3]     ;
                 | LDR W14,[X1]     ;
    exists (0:X2=1 /\ 0:X6=0 /\ 0:X7=0 /\ 0:X8=0 /\ 0:X9=0 /\
            1:X10=2 /\ 1:X11=1 /\ 1:X12=1 /\ 1:X13=2 /\ 1:X14=0)
    (expected with herd7 -model aarch64.cat: Allowed)
>>
      Minimal cores (expected Allowed).  x86: P0: MOV [z],$1; MOV EAX,[z];
      MOV EBX,[x] ‖ P1: MOV [x],$1; MFENCE; MOV EAX,[z], with exists
      (0:EAX=1 /\ 0:EBX=0 /\ 1:EAX=0).  AArch64: P0: STR z; LDR z; DMB LD;
      LDR x ‖ P1: STR x; DMB SY; LDR z, with the same condition.
    - memory/ has no locked RMWs, fences or retry loop (see
      [SeqLockQ6Mem]).  There each XCHG is a contiguous read, write and
      flush of s from an empty buffer ([SeqLockQ6Mem.locked_rmw]); that
      such a triple is a locked-RMW step of x86-TSO is a derivation.  The
      cell-level runs are kernel-checked; that the full litmus tests are
      allowed is not.
    - "Writes respond at issue" is a convention about a future
      operational underlay.  No such [VE] exists in the development yet.
    - Open risk for ARMv8 (not examined here): under issue-time responses,
      the argument of Part 4 may also apply to the version word s written
      by the TicketLock's rel (SWPL).  rel responds, and another thread's
      GT may still read the old odd value; a correct SeqLock retries.  If
      so, the TicketLock specification would also need a publication
      point on ARM, and "buffer x, y and z" would be x86-specific.

    Trusted computation.  This file calls no [vm_compute] or
    [native_compute].  The finite checks ([ctl_wf], [res_incl_of_check],
    [cover_of_check], [rhb_by_check], [nodup_keys_of_check]) are closed by
    [exact eq_refl], i.e. by the kernel's ordinary conversion.  The proof
    terms built by [lia] contain a VM cast ([<:]), which the kernel checks
    with its VM; this holds wherever [lia] is used in the development.
    [Print All Dependencies] shows that none of the results of Parts 1-5
    depends on the lemmas that other files prove with [vm_compute]
    ([WindowTable.lock_not_fence] and the [latch_*] facts,
    [SeqLockCOH.four_modes_force_local], [lb_wf], [retry_wf],
    [torn_with_local_tl]).

    Assumptions.  Every result is closed under the global context. *)

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
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.SeqLockProg.
Require Import examples.Relaxed.SeqLockModule.
Require Import examples.Relaxed.SeqLockClients.

Import ListNotations.

Module SeqLockQ6.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedModuleSemantics.
  Import RelaxedTraceLin.
  Import SeqLockProg.SeqLockProg.
  Import SeqLockClients.SeqLockClients.
  Module BL := BracketedLink.BracketedLink.
  Module SLM := SeqLockModule.SeqLockModule.

  (** ** Part 0: generic helpers *)

  Lemma before_total {A} (l : list A) a b :
    In a l -> In b l -> a <> b -> before l a b \/ before l b a.
  Proof.
    intros Ha Hb Hne. destruct (in_split _ _ Ha) as (l1 & l2 & ->).
    apply in_app_or in Hb as [Hb | [Hb | Hb]].
    - right. destruct (in_split _ _ Hb) as (m1 & m2 & ->). exists m1, (m2 ++ a :: l2).
      split; [rewrite <- app_assoc; reflexivity | apply in_or_app; right; left; reflexivity].
    - congruence.
    - left. exists l1, l2. split; [reflexivity | exact Hb].
  Qed.

  (** [inv_before sel L k op k' op']: the trace has an invocation of [op]
      at key [k] before an invocation of [op'] at key [k']. *)
  Definition inv_before {G : RelaxedSig.t} {X : Type} (sel : X -> option (ThreadEvent G)) (L : list X)
      (k : CallKey G) (op : Sig.op (effect G)) (k' : CallKey G) (op' : Sig.op (effect G)) : Prop :=
    exists i j, inv_at sel L i k op /\ inv_at sel L j k' op' /\ i < j.

  (** Position of a key in a witness. *)
  Section KeyPos.
    Context {G : RelaxedSig.t} (keq : forall k k' : CallKey G, {k = k'} + {k <> k'}).

    Fixpoint kpos (k : CallKey G) (W : list (Op G)) : nat :=
      match W with
      | [] => 0
      | o :: W' => if keq (op_key o) k then 0 else S (kpos k W')
      end.

    Lemma kpos_nth W o : NoDup (map op_key W) -> In o W -> nth_error W (kpos (op_key o) W) = Some o.
    Proof.
      induction W as [| o0 W IH]; intros Hnd Ho; [destruct Ho |].
      cbn in Hnd |- *. inversion Hnd as [| ? ? Hn Hnd']; subst.
      destruct Ho as [<- | Ho].
      - destruct (keq (op_key o0) (op_key o0)) as [_ | Hne]; [reflexivity | congruence].
      - destruct (keq (op_key o0) (op_key o)) as [Heq | _].
        + exfalso. apply Hn. rewrite Heq. apply in_map, Ho.
        + apply IH; assumption.
    Qed.

    Lemma before_kpos W o o' :
      NoDup (map op_key W) -> In o W -> In o' W -> kpos (op_key o) W < kpos (op_key o') W ->
      before W o o'.
    Proof.
      intros Hnd Ho Ho' Hlt.
      exact (BL.nth_before W _ _ o o' (kpos_nth W o Hnd Ho) (kpos_nth W o' Hnd Ho') Hlt).
    Qed.
  End KeyPos.

  (** Indexing the [Some] entries of a list. *)
  Fixpoint idx_some {A} (l : list (option A)) (n : nat) : list (nat * A) :=
    match l with
    | [] => []
    | None :: l' => idx_some l' (S n)
    | Some a :: l' => (n, a) :: idx_some l' (S n)
    end.

  Lemma idx_some_spec {A} (l : list (option A)) : forall n j a,
    nth_error l j = Some (Some a) -> In (n + j, a) (idx_some l n).
  Proof.
    induction l as [| x l IH]; intros n j a H; [destruct j; discriminate H |].
    destruct j as [| j]; cbn in H.
    - injection H as ->. cbn. left. f_equal. lia.
    - replace (n + S j) with (S n + j) by lia.
      destruct x as [b |]; cbn [idx_some]; [right |]; apply IH, H.
  Qed.

  Lemma forallb2 {A B} (P : A -> B -> bool) (l1 : list A) (l2 : list B) :
    forallb (fun a => forallb (fun b => P a b) l2) l1 = true ->
    forall a b, In a l1 -> In b l2 -> P a b = true.
  Proof.
    intros H a b Ha Hb. rewrite forallb_forall in H. specialize (H a Ha).
    rewrite forallb_forall in H. exact (H b Hb).
  Qed.

  (** Invocation and response keys of a trace of thread events, as plain
      data (no dependent return values). *)
  Section EventInfo.
    Context {G : RelaxedSig.t}.

    Definition ikey (ev : ThreadEvent G) : option (CallKey G) :=
      match te_ev G ev with InvEv h _ => Some (te_tid G ev, h) | ResEv _ _ _ => None end.
    Definition rkey (ev : ThreadEvent G) : option (CallKey G) :=
      match te_ev G ev with ResEv h _ _ => Some (te_tid G ev, h) | InvEv _ _ => None end.

    Lemma inv_at_ikey L i k op : inv_at Some L i k op -> In (i, k) (idx_some (map ikey L) 0).
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
      apply (idx_some_spec _ 0 i). rewrite nth_error_map, Hx. reflexivity.
    Qed.

    Lemma res_at_rkey L j k op ret : res_at Some L j k op ret -> In (j, k) (idx_some (map rkey L) 0).
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
      apply (idx_some_spec _ 0 j). rewrite nth_error_map, Hx. reflexivity.
    Qed.

    (** If [W] orders every (response, later invocation) pair and every
        pair of same-thread invocations of [L] as [L] does (two boolean
        checks on positions), then [W] preserves [rhb] for every
        semi-independence relation. *)
    Lemma rhb_by_check (keq : forall k k' : CallKey G, {k = k'} + {k <> k'})
        (L : list (ThreadEvent G)) indep (W : list (Op G)) :
      NoDup (map op_key W) ->
      forallb (fun a => forallb (fun b =>
          implb (Nat.ltb (fst a) (fst b)) (Nat.ltb (kpos keq (snd a) W) (kpos keq (snd b) W)))
        (idx_some (map ikey L) 0)) (idx_some (map rkey L) 0) = true ->
      forallb (fun a => forallb (fun b =>
          implb (Pos.eqb (fst (snd a)) (fst (snd b)) && Nat.ltb (fst a) (fst b))
                (Nat.ltb (kpos keq (snd a) W) (kpos keq (snd b) W)))
        (idx_some (map ikey L) 0)) (idx_some (map ikey L) 0) = true ->
      forall o o', In o W -> In o' W -> rhb Some L indep o o' -> before W o o'.
    Proof.
      intros Hnd Hrt Hpo o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & _)];
        apply (before_kpos keq W o o' Hnd Ho Ho').
      - apply res_at_rkey in Hi. apply inv_at_ikey in Hj.
        pose proof (forallb2 _ _ _ Hrt _ _ Hi Hj) as H. cbn [fst snd] in H.
        apply Nat.ltb_lt in Hij. rewrite Hij in H. apply Nat.ltb_lt, H.
      - apply inv_at_ikey in Hi. apply inv_at_ikey in Hj.
        pose proof (forallb2 _ _ _ Hpo _ _ Hi Hj) as H. cbn [fst snd] in H.
        change (@fst positive (handle G) (op_key o) = @fst positive (handle G) (op_key o')) in Ht.
        apply Nat.ltb_lt in Hij. rewrite Hij, Ht, Pos.eqb_refl in H. apply Nat.ltb_lt, H.
    Qed.

    Definition keqb (keq : forall k k' : CallKey G, {k = k'} + {k <> k'}) (k k' : CallKey G) : bool :=
      if keq k k' then true else false.

    Lemma keqb_eq keq k k' : keqb keq k k' = true -> k = k'.
    Proof. unfold keqb. destruct (keq k k'); [auto | discriminate]. Qed.

    Lemma keqb_refl keq k : keqb keq k k = true.
    Proof. unfold keqb. destruct (keq k k); [reflexivity | congruence]. Qed.

    (** Every invoked key is the key of an operation of [W]: a boolean
        check. *)
    Lemma cover_of_check keq (L : list (ThreadEvent G)) (W : list (Op G)) :
      forallb (fun a => existsb (keqb keq (snd a)) (map op_key W)) (idx_some (map ikey L) 0) = true ->
      forall i k op, inv_at Some L i k op -> exists o, In o W /\ op_key o = k.
    Proof.
      intros H i k op Hi. apply inv_at_ikey in Hi. rewrite forallb_forall in H.
      specialize (H _ Hi). cbn [snd] in H. apply existsb_exists in H as (k' & Hk' & E).
      apply keqb_eq in E. subst k'. apply in_map_iff in Hk' as (o & Ek & Ho). exists o. auto.
    Qed.

    Lemma nodup_keys_of_check keq (W : list (Op G)) :
      SL.nodupb (keqb keq) (map op_key W) = true -> NoDup (map op_key W).
    Proof. apply SL.nodupb_spec; [apply keqb_eq | apply keqb_refl]. Qed.

    (** Position of the first event of a key, to name positions in proofs. *)
    Fixpoint find_key (f : ThreadEvent G -> option (CallKey G)) keq (k : CallKey G)
        (L : list (ThreadEvent G)) : nat :=
      match L with
      | [] => 0
      | ev :: L' =>
          match f ev with
          | Some k' => if keqb keq k' k then 0 else S (find_key f keq k L')
          | None => S (find_key f keq k L')
          end
      end.
  End EventInfo.

  (** ** Part 1: overlay *)

  Lemma nuF_all_sl_after rc (W : list (Op (F rc))) ow orr x y a b :
    BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc) W ->
    In ow W -> SLM.ovev rc ow = SL.OW x y -> In orr W -> SLM.ovev rc orr = SL.OR a b ->
    before W ow orr ->
    (forall w a' b', In w W -> SLM.ovev rc w = SL.OW a' b' -> (a', b') = (x, y)) -> (a, b) = (x, y).
  Proof.
    intros Hnu How Ew Hor Er Hb Hall.
    set (fS := fun o : Op (F rc) => if SL.comp_dec (fcomp (op_op o)) SL.CSL then true else false).
    assert (Hb' : before (filter fS W) ow orr).
    { apply BL.before_filter; [exact Hb | |]; unfold fS;
        [rewrite (ovev_OW rc ow x y Ew) | rewrite (ovev_OR rc orr a b Er)]; reflexivity. }
    destruct Hb' as (l1 & l2 & EP & Hl2).
    pose proof (Hnu SL.CSL) as HS. change (SL.nu_sl (map (SLM.ovev rc) (filter fS W))) in HS.
    unfold SL.nu_sl in HS. rewrite EP, map_app in HS. cbn [map] in HS.
    destruct (reg_ok_suffix SL.sl_wr SL.sl_rd _ _ _ HS) as (cur & Hc).
    rewrite Ew in Hc. cbn in Hc.
    apply (reg_ok_stable SL.sl_wr SL.sl_rd (map (SLM.ovev rc) l2) (x, y) Hc) with (rd := SL.OR a b).
    - intros e u He Hu. apply in_map_iff in He as (w & <- & Hw).
      destruct u as [a' b']. apply (Hall w a' b'); [| apply sl_wr_OW, Hu].
      assert (HwS : In w (filter fS W)) by (rewrite EP; apply in_or_app; right; right; exact Hw).
      apply filter_In in HwS. exact (proj1 HwS).
    - rewrite <- Er. apply in_map, Hl2.
    - reflexivity.
    - reflexivity.
  Qed.

  Section Overlay.
    Context (rc : bool).
    Local Abbreviation nuF := (BL.nuF_all (F := F rc) SL.comp_dec fcomp (SLM.nuFc rc)).

    Definition q6_trace (r2 : nat) : list (ThreadEvent (F rc)) :=
      [ Build_ThreadEvent 1%positive (InvEv (E := F rc) 0 (fZw 1));
        Build_ThreadEvent 1%positive (InvEv (E := F rc) 1 fZr);
        Build_ThreadEvent 1%positive (InvEv (E := F rc) 2 fRead);
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 0 (fWrite 1 1));
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 1 fRead);
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 2 fZr);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 0 (fZw 1) tt);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 1 fZr 1);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 2 fRead (0, 0));
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 0 (fWrite 1 1) tt);
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 1 fRead (1, 1));
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 2 fZr r2) ].

    Definition q6_info (r2 : nat) : list (CallKey (F rc) * SL.OvEv) :=
      [((1%positive, 0), SL.OZW 1); ((1%positive, 1), SL.OZR 1); ((1%positive, 2), SL.OR 0 0);
       ((2%positive, 0), SL.OW 1 1); ((2%positive, 1), SL.OR 1 1); ((2%positive, 2), SL.OZR r2)].

    (** The shape of a trace that the overlay refutation uses: every
        response is one of [q6_info r2], and the four same-thread
        invocation orders of the litmus test. *)
    Definition q6_shape {X : Type} (sel : X -> option (ThreadEvent (F rc))) (L : list X) (r2 : nat) : Prop :=
      (forall j k op ret, res_at sel L j k op ret -> In (k, SLM.ovev_of op ret) (q6_info r2)) /\
      inv_before sel L (1%positive, 0) (fZw 1) (1%positive, 1) fZr /\
      inv_before sel L (1%positive, 1) fZr (1%positive, 2) fRead /\
      inv_before sel L (2%positive, 0) (fWrite 1 1) (2%positive, 1) fRead /\
      inv_before sel L (2%positive, 1) fRead (2%positive, 2) fZr.

    Definition res_info (ev : ThreadEvent (F rc)) : option (CallKey (F rc) * SL.OvEv) :=
      match te_ev _ ev with ResEv h op v => Some ((te_tid _ ev, h), SLM.ovev_of op v) | InvEv _ _ => None end.

    Lemma q6_res_info r2 j k op ret :
      res_at Some (q6_trace r2) j k op ret -> In (k, SLM.ovev_of op ret) (q6_info r2).
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
      assert (H : In (Some ((t, h), SLM.ovev_of op ret)) (map res_info (q6_trace r2))).
      { apply (nth_error_In _ j). rewrite nth_error_map, Hx. reflexivity. }
      revert H. generalize (SLM.ovev_of op ret) as ov. intros ov H. cbn in H.
      repeat (destruct H as [H | H]; [first [discriminate H | injection H; intros; subst; cbn; auto 10] |]).
      destruct H.
    Qed.

    Lemma q6_trace_shape r2 : q6_shape Some (q6_trace r2) r2.
    Proof.
      split; [exact (q6_res_info r2) |].
      split; [| split; [| split]];
        [exists 0, 1 | exists 1, 2 | exists 3, 4 | exists 4, 5];
        (split; [eexists; split; reflexivity | split; [eexists; split; reflexivity | lia]]).
    Qed.

    Ltac pick I := cbn in I;
      destruct I as [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | []]]]]]]; first [discriminate Hc | congruence].

    Lemma q6_val {X : Type} (sel : X -> option (ThreadEvent (F rc))) L r2 W :
      (forall j k op ret, res_at sel L j k op ret -> In (k, SLM.ovev_of op ret) (q6_info r2)) ->
      rel_lin_witness sel L (semi_independent (F rc)) nuF W ->
      forall o, In o W -> In (op_key o, SLM.ovev rc o) (q6_info r2).
    Proof.
      intros Hres (_ & _ & Hocc & _ & _) o Ho.
      destruct (Hocc o Ho) as [_ (j & Hj)]. exact (Hres _ _ _ _ Hj).
    Qed.

    (** The overlay outcome is not relaxed linearizable, for every trace of
        this shape. *)
    Theorem q6_not_rel_lin_any {X : Type} (sel : X -> option (ThreadEvent (F rc))) (L : list X) :
      q6_shape sel L 0 -> ~ rel_lin sel L (semi_independent (F rc)) nuF.
    Proof.
      intros (Hres & (i1 & i2 & Hi1 & Hi2 & H12) & (i2' & i3 & Hi2' & Hi3 & H23)
                   & (i4 & i5 & Hi4 & Hi5 & H45) & (i5' & i6 & Hi5' & Hi6 & H56)) (W & HW).
      pose proof (q6_val sel L 0 W Hres HW) as Hv.
      pose proof HW as (Hnu & Hnd & Hocc & Hall & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      destruct (Hall _ _ _ Hi1) as (o1 & Ho1 & K1). destruct (Hall _ _ _ Hi2) as (o2 & Ho2 & K2).
      destruct (Hall _ _ _ Hi3) as (o3 & Ho3 & K3). destruct (Hall _ _ _ Hi4) as (o4 & Ho4 & K4).
      destruct (Hall _ _ _ Hi5) as (o5 & Ho5 & K5). destruct (Hall _ _ _ Hi6) as (o6 & Ho6 & K6).
      assert (E1 : SLM.ovev rc o1 = SL.OZW 1) by (pose proof (Hv o1 Ho1) as I; rewrite K1 in I; pick I).
      assert (E2 : SLM.ovev rc o2 = SL.OZR 1) by (pose proof (Hv o2 Ho2) as I; rewrite K2 in I; pick I).
      assert (E3 : SLM.ovev rc o3 = SL.OR 0 0) by (pose proof (Hv o3 Ho3) as I; rewrite K3 in I; pick I).
      assert (E4 : SLM.ovev rc o4 = SL.OW 1 1) by (pose proof (Hv o4 Ho4) as I; rewrite K4 in I; pick I).
      assert (E5 : SLM.ovev rc o5 = SL.OR 1 1) by (pose proof (Hv o5 Ho5) as I; rewrite K5 in I; pick I).
      assert (E6 : SLM.ovev rc o6 = SL.OZR 0) by (pose proof (Hv o6 Ho6) as I; rewrite K6 in I; pick I).
      pose proof (ovev_OZW rc o1 1 E1) as P1. pose proof (ovev_OZR rc o2 1 E2) as P2.
      pose proof (ovev_OR rc o3 0 0 E3) as P3. pose proof (ovev_OW rc o4 1 1 E4) as P4.
      pose proof (ovev_OR rc o5 1 1 E5) as P5. pose proof (ovev_OZR rc o6 0 E6) as P6.
      assert (B12 : before W o1 o2).
      { apply (Hord o1 o2 Ho1 Ho2). right. rewrite K1, K2, P1, P2. split; [reflexivity |].
        exists i1, i2. split; [exact Hi1 |]. split; [exact Hi2 |]. split; [exact H12 |].
        intros [Hc _]. apply Hc. reflexivity. }
      assert (B23 : before W o2 o3).
      { apply (Hord o2 o3 Ho2 Ho3). right. rewrite K2, K3, P2, P3. split; [reflexivity |].
        exists i2', i3. split; [exact Hi2' |]. split; [exact Hi3 |]. split; [exact H23 |].
        intros [_ H]. change (WT.dto rc WT.DR WT.Rmb = false) in H.
        rewrite (proj1 (proj2 (proj2 (proj2 (fcat_cross_table rc))))) in H. discriminate H. }
      assert (B45 : before W o4 o5).
      { apply (Hord o4 o5 Ho4 Ho5). right. rewrite K4, K5, P4, P5. split; [reflexivity |].
        exists i4, i5. split; [exact Hi4 |]. split; [exact Hi5 |]. split; [exact H45 |].
        intros [Hc _]. apply Hc. reflexivity. }
      assert (B56 : before W o5 o6).
      { apply (Hord o5 o6 Ho5 Ho6). right. rewrite K5, K6, P5, P6. split; [reflexivity |].
        exists i5', i6. split; [exact Hi5' |]. split; [exact Hi6 |]. split; [exact H56 |].
        apply read_zr_dependent. }
      assert (Hz : forall w u, In w W -> SLM.ovev rc w = SL.OZW u -> u = 1).
      { intros w u Hw Ew. pose proof (Hv w Hw) as I. rewrite Ew in I. pick I. }
      assert (Hs : forall w a' b', In w W -> SLM.ovev rc w = SL.OW a' b' -> (a', b') = (1, 1)).
      { intros w a' b' Hw Ew. pose proof (Hv w Hw) as I. rewrite Ew in I. pick I. }
      assert (N34 : o3 <> o4) by (intros ->; rewrite K3 in K4; discriminate K4).
      destruct (before_total W o3 o4 Ho3 Ho4 N34) as [B34 | B43].
      - pose proof (before_trans W _ _ _ HndW B12 B23) as B13.
        pose proof (before_trans W _ _ _ HndW B13 B34) as B14.
        pose proof (before_trans W _ _ _ HndW B14 B45) as B15.
        pose proof (before_trans W _ _ _ HndW B15 B56) as B16.
        pose proof (nuF_all_z_after rc W o1 o6 1 0 Hnu Ho1 E1 Ho6 E6 B16 Hz) as Ev. discriminate Ev.
      - pose proof (nuF_all_sl_after rc W o4 o3 1 1 0 0 Hnu Ho4 E4 Ho3 E3 B43 Hs) as Ev. discriminate Ev.
    Qed.

    Theorem q6_not_rel_lin : ~ rel_lin Some (q6_trace 0) (semi_independent (F rc)) nuF.
    Proof. exact (q6_not_rel_lin_any Some (q6_trace 0) (q6_trace_shape 0)). Qed.

    (** *** Controls *)

    Ltac getpos Hq := cbn in Hq;
      repeat (destruct Hq as [Hq | Hq]; [first [discriminate Hq | injection Hq; clear Hq; intros; subst] |]);
      try (destruct Hq).
    Ltac occpos := first [ exists 0; eexists; split; reflexivity | exists 1; eexists; split; reflexivity
      | exists 2; eexists; split; reflexivity | exists 3; eexists; split; reflexivity
      | exists 4; eexists; split; reflexivity | exists 5; eexists; split; reflexivity
      | exists 6; eexists; split; reflexivity | exists 7; eexists; split; reflexivity
      | exists 8; eexists; split; reflexivity | exists 9; eexists; split; reflexivity
      | exists 10; eexists; split; reflexivity | exists 11; eexists; split; reflexivity ].
    Ltac nthb := first [ apply (BL.nth_before _ 0 1); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 0 2); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 0 3); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 1 2); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 1 3); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 2 3); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 3 4); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 3 5); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 4 5); [reflexivity | reflexivity | lia] ].

    Lemma q6_inv_at r2 i k op : inv_at Some (q6_trace r2) i k op ->
      In (i, k, op) [(0, (1%positive, 0), fZw 1); (1, (1%positive, 1), fZr); (2, (1%positive, 2), fRead);
                     (3, (2%positive, 0), fWrite 1 1); (4, (2%positive, 1), fRead); (5, (2%positive, 2), fZr)].
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 12 (destruct i as [| i]; [cbn in Hx; first [discriminate Hx | injection Hx; intros; subst; cbn; auto 10] |]).
      destruct i; discriminate Hx.
    Qed.

    Lemma q6_res_pos r2 j k op ret : res_at Some (q6_trace r2) j k op ret -> 6 <= j.
    Proof.
      intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 6 (destruct j as [| j]; [cbn in Hx; discriminate Hx |]). lia.
    Qed.

    Definition o_zw1 : Op (F rc) := Build_Op (E := F rc) (1%positive, 0) (fZw 1) tt.
    Definition o_zr1 : Op (F rc) := Build_Op (E := F rc) (1%positive, 1) fZr 1.
    Definition o_rd1 : Op (F rc) := Build_Op (E := F rc) (1%positive, 2) fRead (0, 0).
    Definition o_wr2 : Op (F rc) := Build_Op (E := F rc) (2%positive, 0) (fWrite 1 1) tt.
    Definition o_rd2 : Op (F rc) := Build_Op (E := F rc) (2%positive, 1) fRead (1, 1).
    Definition o_zr2 (r2 : nat) : Op (F rc) := Build_Op (E := F rc) (2%positive, 2) fZr r2.

    (** Control 1: the same trace with T2's [zr()] returning 1 is relaxed
        linearizable. *)
    Lemma q6_zr1_rel_lin : rel_lin Some (q6_trace 1) (semi_independent (F rc)) nuF.
    Proof.
      exists [o_zw1; o_zr1; o_rd1; o_wr2; o_rd2; o_zr2 1].
      split; [| split; [| split; [| split]]].
      - intros []; cbn; tauto.
      - cbn. repeat constructor; cbn; intuition discriminate.
      - intros o Ho. destruct Ho as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]]; split; occpos.
      - intros i k op Hi. apply q6_inv_at in Hi. getpos Hi;
          first [ exists o_zw1; split; [cbn; tauto | reflexivity] | exists o_zr1; split; [cbn; tauto | reflexivity]
                | exists o_rd1; split; [cbn; tauto | reflexivity] | exists o_wr2; split; [cbn; tauto | reflexivity]
                | exists o_rd2; split; [cbn; tauto | reflexivity] | exists (o_zr2 1); split; [cbn; tauto | reflexivity]].
      - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + exfalso. apply q6_res_pos in Hi. apply q6_inv_at in Hj. getpos Hj; lia.
        + apply q6_inv_at in Hi. apply q6_inv_at in Hj.
          destruct Ho as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
          destruct Ho' as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
          cbn in Ht; try discriminate Ht; getpos Hi; getpos Hj; try lia; nthb.
    Qed.

    (** Control 2: plain store buffering on the object, without the
        forwarded [zr()], is relaxed linearizable. *)
    Definition sb_trace : list (ThreadEvent (F rc)) :=
      [ Build_ThreadEvent 1%positive (InvEv (E := F rc) 0 (fZw 1));
        Build_ThreadEvent 1%positive (InvEv (E := F rc) 2 fRead);
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 0 (fWrite 1 1));
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 2 fZr);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 0 (fZw 1) tt);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 2 fRead (0, 0));
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 0 (fWrite 1 1) tt);
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 2 fZr 0) ].

    Lemma sb_inv_at i k op : inv_at Some sb_trace i k op ->
      In (i, k, op) [(0, (1%positive, 0), fZw 1); (1, (1%positive, 2), fRead);
                     (2, (2%positive, 0), fWrite 1 1); (3, (2%positive, 2), fZr)].
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 8 (destruct i as [| i]; [cbn in Hx; first [discriminate Hx | injection Hx; intros; subst; cbn; auto 10] |]).
      destruct i; discriminate Hx.
    Qed.

    Lemma sb_res_pos j k op ret : res_at Some sb_trace j k op ret -> 4 <= j.
    Proof.
      intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 4 (destruct j as [| j]; [cbn in Hx; discriminate Hx |]). lia.
    Qed.

    Lemma sb_rel_lin : rel_lin Some sb_trace (semi_independent (F rc)) nuF.
    Proof.
      destruct (fcat_cross_table rc) as (_ & _ & _ & _ & _ & HWmbDR & HDWRmb & _).
      exists [o_rd1; o_zr2 0; o_zw1; o_wr2].
      split; [| split; [| split; [| split]]].
      - intros []; cbn; tauto.
      - cbn. repeat constructor; cbn; intuition discriminate.
      - intros o Ho. destruct Ho as [<- | [<- | [<- | [<- | []]]]]; split; occpos.
      - intros i k op Hi. apply sb_inv_at in Hi. getpos Hi;
          first [ exists o_zw1; split; [cbn; tauto | reflexivity] | exists o_rd1; split; [cbn; tauto | reflexivity]
                | exists o_wr2; split; [cbn; tauto | reflexivity] | exists (o_zr2 0); split; [cbn; tauto | reflexivity]].
      - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + exfalso. apply sb_res_pos in Hi. apply sb_inv_at in Hj. getpos Hj; lia.
        + apply sb_inv_at in Hi. apply sb_inv_at in Hj.
          destruct Ho as [<- | [<- | [<- | [<- | []]]]];
          destruct Ho' as [<- | [<- | [<- | [<- | []]]]];
          cbn in Ht; try discriminate Ht; getpos Hi; getpos Hj; try lia;
          first [ nthb | exfalso; apply Hn; split; [discriminate | assumption] ].
    Qed.

    (** Controls 3 and 4: dropping either own read alone.  The refutation
        needs both same-thread chains.  [d1]: T1's zr() dropped,
<<
        T1: zw(1); read() = (0,0)   ||   T2: write(1,1); read() = (1,1); zr() = 0
>>
        [d2]: T2's read() dropped,
<<
        T1: zw(1); zr() = 1; read() = (0,0)   ||   T2: write(1,1); zr() = 0
>>
        Handles as in [q6_trace]; all invocations before all responses. *)
    Ltac nthb5 := first
      [ apply (BL.nth_before _ 0 1); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 0 2); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 0 3); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 0 4); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 1 2); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 1 3); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 1 4); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 2 3); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 2 4); [reflexivity | reflexivity | lia]
      | apply (BL.nth_before _ 3 4); [reflexivity | reflexivity | lia] ].

    Definition d1_trace : list (ThreadEvent (F rc)) :=
      [ Build_ThreadEvent 1%positive (InvEv (E := F rc) 0 (fZw 1));
        Build_ThreadEvent 1%positive (InvEv (E := F rc) 2 fRead);
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 0 (fWrite 1 1));
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 1 fRead);
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 2 fZr);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 0 (fZw 1) tt);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 2 fRead (0, 0));
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 0 (fWrite 1 1) tt);
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 1 fRead (1, 1));
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 2 fZr 0) ].

    Definition d2_trace : list (ThreadEvent (F rc)) :=
      [ Build_ThreadEvent 1%positive (InvEv (E := F rc) 0 (fZw 1));
        Build_ThreadEvent 1%positive (InvEv (E := F rc) 1 fZr);
        Build_ThreadEvent 1%positive (InvEv (E := F rc) 2 fRead);
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 0 (fWrite 1 1));
        Build_ThreadEvent 2%positive (InvEv (E := F rc) 2 fZr);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 0 (fZw 1) tt);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 1 fZr 1);
        Build_ThreadEvent 1%positive (ResEv (E := F rc) 2 fRead (0, 0));
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 0 (fWrite 1 1) tt);
        Build_ThreadEvent 2%positive (ResEv (E := F rc) 2 fZr 0) ].

    Lemma d1_inv_at i k op : inv_at Some d1_trace i k op ->
      In (i, k, op) [(0, (1%positive, 0), fZw 1); (1, (1%positive, 2), fRead);
                     (2, (2%positive, 0), fWrite 1 1); (3, (2%positive, 1), fRead); (4, (2%positive, 2), fZr)].
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 10 (destruct i as [| i]; [cbn in Hx; first [discriminate Hx | injection Hx; intros; subst; cbn; auto 10] |]).
      destruct i; discriminate Hx.
    Qed.

    Lemma d2_inv_at i k op : inv_at Some d2_trace i k op ->
      In (i, k, op) [(0, (1%positive, 0), fZw 1); (1, (1%positive, 1), fZr); (2, (1%positive, 2), fRead);
                     (3, (2%positive, 0), fWrite 1 1); (4, (2%positive, 2), fZr)].
    Proof.
      destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 10 (destruct i as [| i]; [cbn in Hx; first [discriminate Hx | injection Hx; intros; subst; cbn; auto 10] |]).
      destruct i; discriminate Hx.
    Qed.

    Lemma d1_res_pos j k op ret : res_at Some d1_trace j k op ret -> 5 <= j.
    Proof.
      intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 5 (destruct j as [| j]; [cbn in Hx; discriminate Hx |]). lia.
    Qed.

    Lemma d2_res_pos j k op ret : res_at Some d2_trace j k op ret -> 5 <= j.
    Proof.
      intros (x & Hx & Hs). injection Hs as Hs. subst x.
      do 5 (destruct j as [| j]; [cbn in Hx; discriminate Hx |]). lia.
    Qed.

    Lemma d1_rel_lin : rel_lin Some d1_trace (semi_independent (F rc)) nuF.
    Proof.
      destruct (fcat_cross_table rc) as (_ & _ & _ & _ & _ & HWmbDR & HDWRmb & _).
      exists [o_rd1; o_wr2; o_rd2; o_zr2 0; o_zw1].
      split; [| split; [| split; [| split]]].
      - intros []; cbn; tauto.
      - cbn. repeat constructor; cbn; intuition discriminate.
      - intros o Ho. destruct Ho as [<- | [<- | [<- | [<- | [<- | []]]]]]; split; occpos.
      - intros i k op Hi. apply d1_inv_at in Hi. getpos Hi;
          first [ exists o_zw1; split; [cbn; tauto | reflexivity] | exists o_rd1; split; [cbn; tauto | reflexivity]
                | exists o_wr2; split; [cbn; tauto | reflexivity] | exists o_rd2; split; [cbn; tauto | reflexivity]
                | exists (o_zr2 0); split; [cbn; tauto | reflexivity]].
      - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + exfalso. apply d1_res_pos in Hi. apply d1_inv_at in Hj. getpos Hj; lia.
        + apply d1_inv_at in Hi. apply d1_inv_at in Hj.
          destruct Ho as [<- | [<- | [<- | [<- | [<- | []]]]]];
          destruct Ho' as [<- | [<- | [<- | [<- | [<- | []]]]]];
          cbn in Ht; try discriminate Ht; getpos Hi; getpos Hj; try lia;
          first [ nthb5 | exfalso; apply Hn; split; [discriminate | assumption] ].
    Qed.

    Lemma d2_rel_lin : rel_lin Some d2_trace (semi_independent (F rc)) nuF.
    Proof.
      destruct (fcat_cross_table rc) as (_ & _ & _ & _ & _ & HWmbDR & HDWRmb & _).
      exists [o_zr2 0; o_zw1; o_zr1; o_rd1; o_wr2].
      split; [| split; [| split; [| split]]].
      - intros []; cbn; tauto.
      - cbn. repeat constructor; cbn; intuition discriminate.
      - intros o Ho. destruct Ho as [<- | [<- | [<- | [<- | [<- | []]]]]]; split; occpos.
      - intros i k op Hi. apply d2_inv_at in Hi. getpos Hi;
          first [ exists o_zw1; split; [cbn; tauto | reflexivity] | exists o_zr1; split; [cbn; tauto | reflexivity]
                | exists o_rd1; split; [cbn; tauto | reflexivity] | exists o_wr2; split; [cbn; tauto | reflexivity]
                | exists (o_zr2 0); split; [cbn; tauto | reflexivity]].
      - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + exfalso. apply d2_res_pos in Hi. apply d2_inv_at in Hj. getpos Hj; lia.
        + apply d2_inv_at in Hi. apply d2_inv_at in Hj.
          destruct Ho as [<- | [<- | [<- | [<- | [<- | []]]]]];
          destruct Ho' as [<- | [<- | [<- | [<- | [<- | []]]]]];
          cbn in Ht; try discriminate Ht; getpos Hi; getpos Hj; try lia;
          first [ nthb5 | exfalso; apply Hn; split; [discriminate | assumption] ].
    Qed.
  End Overlay.

  (** ** Part 2: underlay, witness level ([SeqLockCOH.WF]) *)

  Lemma field_const (f : SL.State -> nat) (wr : SL.UC -> option nat)
    (f_post : forall s e, f (SL.post s e) = match wr (SL.call e) with Some v => v | None => f s end)
    X v p0 e0 k :
    (forall p e, nth_error (SL.wit X) p = Some e -> wr (SL.call e) = None \/ wr (SL.call e) = Some v) ->
    nth_error (SL.wit X) p0 = Some e0 -> wr (SL.call e0) = Some v -> p0 < k -> f (SL.at_ X k) = v.
  Proof.
    intros Hall H0 Hw. induction k as [| k IH]; intros Hlt; [lia |].
    rewrite (SL.field_S f wr f_post X k). destruct (Nat.eq_dec k p0) as [-> | Hne].
    - rewrite H0, Hw. reflexivity.
    - destruct (nth_error (SL.wit X) k) as [e |] eqn:E.
      + destruct (Hall k e E) as [N | N]; rewrite N; [apply IH; lia | reflexivity].
      + apply IH; lia.
  Qed.

  Definition q6p0 : list SL.Blk := [SL.BZw 1; SL.BZr 1; SL.BR [] 0 0 0].
  Definition q6p1 : list SL.Blk := [SL.BW 1 1; SL.BR [] 2 1 1; SL.BZr 0].

  Theorem q6_underlay_no_WF rc w : ~ SL.WF rc SL.plainTL (SL.mkX q6p0 q6p1 w).
  Proof.
    intros HW.
    assert (Hin : forall t i, In t [0; 1] -> i < length (SL.trace (SL.prog (SL.mkX q6p0 q6p1 w) t)) ->
                    In (SL.evt (SL.mkX q6p0 q6p1 w) t i) (SL.wit (SL.mkX q6p0 q6p1 w)))
      by (intros t i Ht Hi; exact (SL.wf_complete _ _ _ HW t i Ht Hi)).
    assert (Hpres : forall t i i', In t [0; 1] -> i < i' -> i' < length (SL.trace (SL.prog (SL.mkX q6p0 q6p1 w) t)) ->
              SL.upres rc SL.plainTL (SL.call (SL.evt (SL.mkX q6p0 q6p1 w) t i))
                (SL.call (SL.evt (SL.mkX q6p0 q6p1 w) t i')) = true ->
              SL.P (SL.mkX q6p0 q6p1 w) t i < SL.P (SL.mkX q6p0 q6p1 w) t i').
    { intros t i i' Ht Hii' Hi' Hu. unfold SL.P.
      apply (SL.wf_pres _ _ _ HW); [apply Hin; [exact Ht | lia] | apply Hin; [exact Ht | exact Hi'] | reflexivity
                                   | exact Hii' | exact Hu]. }
    assert (A1 : SL.P (SL.mkX q6p0 q6p1 w) 0 0 < SL.P (SL.mkX q6p0 q6p1 w) 0 1)
      by (apply Hpres; [cbn; tauto | lia | cbn; lia | destruct rc; reflexivity]).
    assert (A2 : SL.P (SL.mkX q6p0 q6p1 w) 0 1 < SL.P (SL.mkX q6p0 q6p1 w) 0 3)
      by (apply Hpres; [cbn; tauto | lia | cbn; lia | destruct rc; reflexivity]).
    assert (A3 : SL.P (SL.mkX q6p0 q6p1 w) 0 3 < SL.P (SL.mkX q6p0 q6p1 w) 0 4)
      by (apply Hpres; [cbn; tauto | lia | cbn; lia | destruct rc; reflexivity]).
    assert (B1 : SL.P (SL.mkX q6p0 q6p1 w) 1 2 < SL.P (SL.mkX q6p0 q6p1 w) 1 8)
      by (apply Hpres; [cbn; tauto | lia | cbn; lia | destruct rc; reflexivity]).
    assert (B2 : SL.P (SL.mkX q6p0 q6p1 w) 1 8 < SL.P (SL.mkX q6p0 q6p1 w) 1 10)
      by (apply Hpres; [cbn; tauto | lia | cbn; lia | destruct rc; reflexivity]).
    assert (B3 : SL.P (SL.mkX q6p0 q6p1 w) 1 10 < SL.P (SL.mkX q6p0 q6p1 w) 1 12)
      by (apply Hpres; [cbn; tauto | lia | cbn; lia | destruct rc; reflexivity]).
    assert (Hval : forall t i, In t [0; 1] -> i < length (SL.trace (SL.prog (SL.mkX q6p0 q6p1 w) t)) ->
              nth_error (SL.wit (SL.mkX q6p0 q6p1 w)) (SL.P (SL.mkX q6p0 q6p1 w) t i)
              = Some (SL.evt (SL.mkX q6p0 q6p1 w) t i))
      by (intros t i Ht Hi; unfold SL.P; apply SL.idx_nth, Hin; assumption).
    pose proof (SL.wf_valid _ _ _ HW _ _ (Hval 0 4 ltac:(cbn; tauto) ltac:(cbn; lia))) as V1.
    change (Nat.eqb (SL.sx (SL.at_ (SL.mkX q6p0 q6p1 w) (SL.P (SL.mkX q6p0 q6p1 w) 0 4))) 0 = true) in V1.
    pose proof (SL.wf_valid _ _ _ HW _ _ (Hval 1 12 ltac:(cbn; tauto) ltac:(cbn; lia))) as V2.
    change (Nat.eqb (SL.sz (SL.at_ (SL.mkX q6p0 q6p1 w) (SL.P (SL.mkX q6p0 q6p1 w) 1 12))) 0 = true) in V2.
    assert (Hcall : forall p e, nth_error (SL.wit (SL.mkX q6p0 q6p1 w)) p = Some e ->
                      In (SL.call e) (SL.trace q6p0 ++ SL.trace q6p1)).
    { intros p e Hp. destruct (SL.wf_call _ _ _ HW e (nth_error_In _ _ Hp)) as [Ht Hc].
      apply nth_error_In in Hc. apply in_or_app. cbn in Ht.
      destruct Ht as [Ht | [Ht | []]]; rewrite <- Ht in Hc; [left | right]; exact Hc. }
    assert (Hx1 : forall p e, nth_error (SL.wit (SL.mkX q6p0 q6p1 w)) p = Some e ->
                    SL.wrx (SL.call e) = None \/ SL.wrx (SL.call e) = Some 1).
    { intros p e Hp. pose proof (Hcall p e Hp) as Hc. cbn in Hc.
      repeat (destruct Hc as [Hc | Hc]; [rewrite <- Hc; cbn; auto |]). destruct Hc. }
    assert (Hz1 : forall p e, nth_error (SL.wit (SL.mkX q6p0 q6p1 w)) p = Some e ->
                    SL.wrz (SL.call e) = None \/ SL.wrz (SL.call e) = Some 1).
    { intros p e Hp. pose proof (Hcall p e Hp) as Hc. cbn in Hc.
      repeat (destruct Hc as [Hc | Hc]; [rewrite <- Hc; cbn; auto |]). destruct Hc. }
    destruct (Nat.lt_ge_cases (SL.P (SL.mkX q6p0 q6p1 w) 1 2) (SL.P (SL.mkX q6p0 q6p1 w) 0 4)) as [Hlt | Hge].
    - rewrite (field_const SL.sx SL.wrx SL.sx_post _ 1 _ _ _ Hx1 (Hval 1 2 ltac:(cbn; tauto) ltac:(cbn; lia))
                 eq_refl Hlt) in V1. discriminate V1.
    - assert (Hz : SL.P (SL.mkX q6p0 q6p1 w) 0 0 < SL.P (SL.mkX q6p0 q6p1 w) 1 12) by lia.
      rewrite (field_const SL.sz SL.wrz SL.sz_post _ 1 _ _ _ Hz1 (Hval 0 0 ltac:(cbn; tauto) ltac:(cbn; lia))
                 eq_refl Hz) in V2. discriminate V2.
  Qed.

  (** Control: with T2's [zr()] returning 1 the programs have a [WF]
      execution. *)
  Definition q6p1z1 : list SL.Blk := [SL.BW 1 1; SL.BR [] 2 1 1; SL.BZr 1].
  Definition ctl_wit : list SL.Ev :=
    map (fun '(i, c) => SL.mkEv 0 i c) (combine (seq 0 8) (SL.trace q6p0)) ++
    map (fun '(i, c) => SL.mkEv 1 i c) (combine (seq 0 13) (SL.trace q6p1z1)).

  Lemma ctl_wf rc : SL.WF rc SL.plainTL (SL.mkX q6p0 q6p1z1 ctl_wit).
  Proof. apply SL.wfb_sound. destruct rc; exact eq_refl. Qed.

  (** ** Part 3: underlay, trace level *)

  Lemma replay_app s l1 l2 : SLM.replay s (l1 ++ l2) -> exists s', SLM.replay s' l2.
  Proof.
    revert s. induction l1 as [| e l1 IH]; intros s H; [exists s; exact H | exact (IH _ (proj2 H))].
  Qed.

  Lemma zreg_app cur l1 l2 : SLM.zreg cur (l1 ++ l2) -> exists cur', SLM.zreg cur' l2.
  Proof.
    revert cur. induction l1 as [| c l1 IH]; intros cur H; [exists cur; exact H |].
    cbn in H. destruct c; try exact (IH _ H). exact (IH _ (proj2 H)).
  Qed.

  (** In a replay of the [CSL] component from a state with [x = 1], if
      every call writes nothing to [x] or writes 1, every [x] read
      returns 1. *)
  Lemma replay_x1 l : forall s, SLM.replay s l -> SL.sx s = 1 ->
    (forall e, In e l -> SL.wrx (SL.call e) = None \/ SL.wrx (SL.call e) = Some 1) ->
    forall e v, In e l -> SL.call e = SL.RdX v -> v = 1.
  Proof.
    induction l as [| a l IH]; intros s H Hs Hall e v Hin Hc; [destruct Hin |].
    destruct Hin as [<- | Hin].
    - destruct H as [Hp _]. unfold SL.pre in Hp. rewrite Hc in Hp. apply Nat.eqb_eq in Hp. congruence.
    - refine (IH (SL.post s a) (proj2 H) _ _ e v Hin Hc).
      + rewrite SL.sx_post. destruct (Hall a (or_introl eq_refl)) as [N | N]; rewrite N; [exact Hs | reflexivity].
      + intros e' He'. apply Hall. right. exact He'.
  Qed.

  (** The same for the register [z]. *)
  Lemma zreg_1 l : forall cur, SLM.zreg cur l -> cur = 1 -> (forall v, In (SL.WrZ v) l -> v = 1) ->
    forall v, In (SL.RdZ v) l -> v = 1.
  Proof.
    induction l as [| c l IH]; intros cur H Hc Hall v Hin; [destruct Hin |].
    assert (Hall' : forall v, In (SL.WrZ v) l -> v = 1) by (intros v' H'; apply Hall; right; exact H').
    cbn in H. destruct Hin as [Hcv | Hin].
    - subst c. destruct H as [-> _]. exact Hc.
    - destruct c; first [ exact (IH _ H Hc Hall' v Hin)
                        | exact (IH _ H (Hall _ (or_introl eq_refl)) Hall' v Hin)
                        | exact (IH _ (proj2 H) Hc Hall' v Hin) ].
  Qed.

  Section Underlay.
    Context (rc : bool).
    Local Abbreviation K := SL.plainTL.
    Local Abbreviation G := (E rc K).
    Local Abbreviation nuE := (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc K)).

    (** Calls of a program, numbered by handle. *)
    Definition ucs (p : list SL.Blk) : list (nat * SL.UC) :=
      combine (seq 0 (length (SL.trace p))) (SL.trace p).

    Definition mk_inv (t : positive) (hc : nat * SL.UC) : ThreadEvent G :=
      Build_ThreadEvent t (InvEv (E := G) (fst hc) (op_of (snd hc))).
    Definition mk_res (t : positive) (hc : nat * SL.UC) : ThreadEvent G :=
      Build_ThreadEvent t (ResEv (E := G) (fst hc) (op_of (snd hc)) (of_uc (op_of (snd hc)) (snd hc))).

    (** The (key, call) pairs of a thread running a program. *)
    Definition info_of (t : positive) (p : list SL.Blk) : list (CallKey G * SL.UC) :=
      map (fun hc => ((t, fst hc), snd hc)) (ucs p).

    Definition ures_info (ev : ThreadEvent G) : option (CallKey G * SL.UC) :=
      match te_ev _ ev with ResEv h op v => Some ((te_tid _ ev, h), uc_of op v) | InvEv _ _ => None end.

    Definition kc_eqb (a b : CallKey G * SL.UC) : bool :=
      if SLM.keyE_dec rc K (fst a) (fst b) then (if SL.UC_eq_dec (snd a) (snd b) then true else false)
      else false.

    Lemma kc_eqb_eq a b : kc_eqb a b = true -> a = b.
    Proof.
      destruct a as [ka ca], b as [kb cb]. unfold kc_eqb. cbn [fst snd].
      destruct (SLM.keyE_dec rc K ka kb) as [-> |]; [| discriminate].
      destruct (SL.UC_eq_dec ca cb) as [-> |]; [reflexivity | discriminate].
    Qed.

    (** Every response of a concrete trace is listed in [info]: a
        boolean check. *)
    Lemma res_incl_of_check (L : list (ThreadEvent G)) info :
      forallb (fun x => match x with Some a => existsb (kc_eqb a) info | None => true end)
              (map ures_info L) = true ->
      forall j k op ret, res_at Some L j k op ret -> In (k, uc_of op ret) info.
    Proof.
      intros H j k op ret (x & Hx & Hs). injection Hs as ->.
      assert (Hin : In (Some (k, uc_of op ret)) (map ures_info L)).
      { destruct k as [t h]. apply (nth_error_In _ j). rewrite nth_error_map, Hx. reflexivity. }
      rewrite forallb_forall in H. specialize (H _ Hin). cbn beta iota in H.
      apply existsb_exists in H as (b & Hb & Eb). apply kc_eqb_eq in Eb. subst b. exact Hb.
    Qed.

    Lemma op_from_uc (o : Op G) c : SLM.uc rc K o = c -> op_op o = op_of c.
    Proof. intros <-. symmetry. apply op_of_uc. Qed.

    Lemma sdep a b : SL.upres rc K (uc_of a (dflt a)) (uc_of b (dflt b)) = true -> ~ semi_independent G a b.
    Proof. intros H Hn. change (SL.upres rc K (uc_of a (dflt a)) (uc_of b (dflt b)) = false) in Hn. congruence. Qed.

    (** Values of the operations of a witness, from the responses. *)
    Lemma uvals {X : Type} (sel : X -> option (ThreadEvent G)) L info W :
      (forall j k op ret, res_at sel L j k op ret -> In (k, uc_of op ret) info) ->
      rel_lin_witness sel L (semi_independent G) nuE W ->
      forall o, In o W -> In (op_key o, SLM.uc rc K o) info.
    Proof.
      intros Hres (_ & _ & Hocc & _ & _) o Ho.
      destruct (Hocc o Ho) as [_ (j & Hj)]. exact (Hres _ _ _ _ Hj).
    Qed.

    (** The [CSL] part of a legal witness: once [x] is written 1, and no
        other value is ever written to [x], no later [x] read returns 0. *)
    Lemma nuE_x_after W ow orr :
      nuE W -> In ow W -> SLM.uc rc K ow = SL.WrX 1 -> In orr W -> SLM.uc rc K orr = SL.RdX 0 ->
      (forall w, In w W -> SL.wrx (SLM.uc rc K w) = None \/ SL.wrx (SLM.uc rc K w) = Some 1) ->
      ~ before W ow orr.
    Proof.
      intros Hnu How Uw Hor Ur Hx Hb.
      set (fS := fun o : Op G => if SL.comp_dec (SLM.compE (op_op o)) SL.CSL then true else false).
      assert (Hb' : before (filter fS W) ow orr).
      { apply BL.before_filter; [exact Hb | |]; unfold fS;
          [rewrite (op_from_uc ow _ Uw) | rewrite (op_from_uc orr _ Ur)]; reflexivity. }
      destruct Hb' as (l1 & l2 & EP & Hl2).
      pose proof (Hnu SL.CSL) as HS. change (SLM.replay SL.init (map (SLM.uev rc K) (filter fS W))) in HS.
      rewrite EP, map_app in HS. cbn [map] in HS.
      destruct (replay_app _ _ _ HS) as (s & [_ Hs]).
      assert (E0 : 0 = 1).
      { apply (replay_x1 (map (SLM.uev rc K) l2) (SL.post s (SLM.uev rc K ow)) Hs)
          with (e := SLM.uev rc K orr).
        - rewrite SL.sx_post. change (SL.wrx (SLM.uc rc K ow)) with (SL.wrx (SL.call (SLM.uev rc K ow))).
          cbn [SL.call SLM.uev]. rewrite Uw. reflexivity.
        - intros e He. apply in_map_iff in He as (w & <- & Hw). apply Hx.
          assert (HwS : In w (filter fS W)) by (rewrite EP; apply in_or_app; right; right; exact Hw).
          apply filter_In in HwS. exact (proj1 HwS).
        - apply in_map, Hl2.
        - exact Ur. }
      discriminate E0.
    Qed.

    (** The [CZ] part: once [z] is written 1, and no other value is ever
        written to [z], no later [z] read returns 0. *)
    Lemma nuE_z_after W ow orr :
      nuE W -> In ow W -> SLM.uc rc K ow = SL.WrZ 1 -> In orr W -> SLM.uc rc K orr = SL.RdZ 0 ->
      (forall w v, In w W -> SLM.uc rc K w = SL.WrZ v -> v = 1) ->
      ~ before W ow orr.
    Proof.
      intros Hnu How Uw Hor Ur Hz Hb.
      set (fZ := fun o : Op G => if SL.comp_dec (SLM.compE (op_op o)) SL.CZ then true else false).
      assert (Hb' : before (filter fZ W) ow orr).
      { apply BL.before_filter; [exact Hb | |]; unfold fZ;
          [rewrite (op_from_uc ow _ Uw) | rewrite (op_from_uc orr _ Ur)]; reflexivity. }
      destruct Hb' as (l1 & l2 & EP & Hl2).
      pose proof (Hnu SL.CZ) as HZ. change (SLM.zreg 0 (map (SLM.uc rc K) (filter fZ W))) in HZ.
      rewrite EP, map_app in HZ. cbn [map] in HZ.
      destruct (zreg_app _ _ _ HZ) as (cur & Hc). rewrite Uw in Hc. cbn in Hc.
      assert (E0 : 0 = 1).
      { apply (zreg_1 (map (SLM.uc rc K) l2) 1 Hc eq_refl).
        - intros v Hv. apply in_map_iff in Hv as (w & Ew & Hw). apply (Hz w v); [| exact Ew].
          assert (HwZ : In w (filter fZ W)) by (rewrite EP; apply in_or_app; right; right; exact Hw).
          apply filter_In in HwZ. exact (proj1 HwZ).
        - rewrite <- Ur. apply in_map, Hl2. }
      discriminate E0.
    Qed.

    Ltac pick I := cbn in I;
      repeat (destruct I as [Hc | I]; [first [discriminate Hc | congruence] |]); destruct I.

    (** *** The Q6 underlay history *)

    Definition q6u_info : list (CallKey G * SL.UC) := info_of 1 q6p0 ++ info_of 2 q6p1.

    Lemma q6u_info_x k c : In (k, c) q6u_info -> SL.wrx c = None \/ SL.wrx c = Some 1.
    Proof.
      intros H. cbn in H.
      repeat (destruct H as [H | H]; [injection H; intros; subst; cbn; auto |]). destruct H.
    Qed.

    Lemma q6u_info_z k v : In (k, SL.WrZ v) q6u_info -> v = 1.
    Proof.
      intros H. cbn in H.
      repeat (destruct H as [H | H]; [first [discriminate H | injection H; intros; subst; reflexivity] |]).
      destruct H.
    Qed.

    (** The shape of a trace that the underlay refutation uses: every
        response is one of the 21 calls of [q6u_info] (T1 = thread 1 runs
        [q6p0], T2 = thread 2 runs [q6p1]), and six same-thread invocation
        orders. *)
    Definition q6u_shape {X : Type} (sel : X -> option (ThreadEvent G)) (L : list X) : Prop :=
      (forall j k op ret, res_at sel L j k op ret -> In (k, uc_of op ret) q6u_info) /\
      inv_before sel L (1%positive, 0) (sWrZ 1) (1%positive, 1) sRdZ /\
      inv_before sel L (1%positive, 1) sRdZ (1%positive, 3) sRmb /\
      inv_before sel L (1%positive, 3) sRmb (1%positive, 4) sRdX /\
      inv_before sel L (2%positive, 2) (sWrX 1) (2%positive, 8) sRdX /\
      inv_before sel L (2%positive, 8) sRdX (2%positive, 10) sRmb /\
      inv_before sel L (2%positive, 10) sRmb (2%positive, 12) sRdZ.

    Theorem q6_underlay_not_rel_lin_any {X : Type} (sel : X -> option (ThreadEvent G)) (L : list X) :
      q6u_shape sel L -> ~ rel_lin sel L (semi_independent G) nuE.
    Proof.
      intros (Hres & (ia0 & ia1 & Ha0 & Ha1 & H01) & (ia1' & ia3 & Ha1' & Ha3 & H13)
                   & (ia3' & ia4 & Ha3' & Ha4 & H34) & (ib2 & ib8 & Hb2 & Hb8 & H28)
                   & (ib8' & ib10 & Hb8' & Hb10 & H810) & (ib10' & ib12 & Hb10' & Hb12 & H1012)) (W & HW).
      pose proof (uvals sel L q6u_info W Hres HW) as Hv.
      pose proof HW as (Hnu & Hnd & Hocc & Hall & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      destruct (Hall _ _ _ Ha0) as (a0 & Ia0 & Ka0). destruct (Hall _ _ _ Ha1) as (a1 & Ia1 & Ka1).
      destruct (Hall _ _ _ Ha3) as (a3 & Ia3 & Ka3). destruct (Hall _ _ _ Ha4) as (a4 & Ia4 & Ka4).
      destruct (Hall _ _ _ Hb2) as (b2 & Ib2 & Kb2). destruct (Hall _ _ _ Hb8) as (b8 & Ib8 & Kb8).
      destruct (Hall _ _ _ Hb10) as (b10 & Ib10 & Kb10). destruct (Hall _ _ _ Hb12) as (b12 & Ib12 & Kb12).
      assert (Ua0 : SLM.uc rc K a0 = SL.WrZ 1) by (pose proof (Hv a0 Ia0) as I; rewrite Ka0 in I; pick I).
      assert (Ua1 : SLM.uc rc K a1 = SL.RdZ 1) by (pose proof (Hv a1 Ia1) as I; rewrite Ka1 in I; pick I).
      assert (Ua3 : SLM.uc rc K a3 = SL.RmbC) by (pose proof (Hv a3 Ia3) as I; rewrite Ka3 in I; pick I).
      assert (Ua4 : SLM.uc rc K a4 = SL.RdX 0) by (pose proof (Hv a4 Ia4) as I; rewrite Ka4 in I; pick I).
      assert (Ub2 : SLM.uc rc K b2 = SL.WrX 1) by (pose proof (Hv b2 Ib2) as I; rewrite Kb2 in I; pick I).
      assert (Ub8 : SLM.uc rc K b8 = SL.RdX 1) by (pose proof (Hv b8 Ib8) as I; rewrite Kb8 in I; pick I).
      assert (Ub10 : SLM.uc rc K b10 = SL.RmbC) by (pose proof (Hv b10 Ib10) as I; rewrite Kb10 in I; pick I).
      assert (Ub12 : SLM.uc rc K b12 = SL.RdZ 0) by (pose proof (Hv b12 Ib12) as I; rewrite Kb12 in I; pick I).
      pose proof (op_from_uc a0 _ Ua0) as Pa0. pose proof (op_from_uc a1 _ Ua1) as Pa1.
      pose proof (op_from_uc a3 _ Ua3) as Pa3. pose proof (op_from_uc a4 _ Ua4) as Pa4.
      pose proof (op_from_uc b2 _ Ub2) as Pb2. pose proof (op_from_uc b8 _ Ub8) as Pb8.
      pose proof (op_from_uc b10 _ Ub10) as Pb10. pose proof (op_from_uc b12 _ Ub12) as Pb12.
      cbn [op_of] in Pa0, Pa1, Pa3, Pa4, Pb2, Pb8, Pb10, Pb12.
      Local Ltac edge Hord o o' Io Io' Ko Ko' Po Po' i j Hi Hj Hij :=
        apply (Hord o o' Io Io'); right; rewrite Ko, Ko', Po, Po'; split; [reflexivity |];
        exists i, j; split; [exact Hi |]; split; [exact Hj |]; split; [exact Hij |];
        apply sdep; destruct rc; reflexivity.
      assert (A01 : before W a0 a1) by (edge Hord a0 a1 Ia0 Ia1 Ka0 Ka1 Pa0 Pa1 ia0 ia1 Ha0 Ha1 H01).
      assert (A13 : before W a1 a3) by (edge Hord a1 a3 Ia1 Ia3 Ka1 Ka3 Pa1 Pa3 ia1' ia3 Ha1' Ha3 H13).
      assert (A34 : before W a3 a4) by (edge Hord a3 a4 Ia3 Ia4 Ka3 Ka4 Pa3 Pa4 ia3' ia4 Ha3' Ha4 H34).
      assert (B28 : before W b2 b8) by (edge Hord b2 b8 Ib2 Ib8 Kb2 Kb8 Pb2 Pb8 ib2 ib8 Hb2 Hb8 H28).
      assert (B810 : before W b8 b10) by (edge Hord b8 b10 Ib8 Ib10 Kb8 Kb10 Pb8 Pb10 ib8' ib10 Hb8' Hb10 H810).
      assert (B1012 : before W b10 b12)
        by (edge Hord b10 b12 Ib10 Ib12 Kb10 Kb12 Pb10 Pb12 ib10' ib12 Hb10' Hb12 H1012).
      assert (Hx : forall w, In w W -> SL.wrx (SLM.uc rc K w) = None \/ SL.wrx (SLM.uc rc K w) = Some 1)
        by (intros w Hw; exact (q6u_info_x _ _ (Hv w Hw))).
      assert (Hz : forall w v, In w W -> SLM.uc rc K w = SL.WrZ v -> v = 1)
        by (intros w v Hw Ew; pose proof (Hv w Hw) as I; rewrite Ew in I; exact (q6u_info_z _ _ I)).
      assert (N : a4 <> b2) by (intros ->; rewrite Ka4 in Kb2; discriminate Kb2).
      destruct (before_total W a4 b2 Ia4 Ib2 N) as [Bab | Bba].
      - (* T1's x read precedes T2's x write: then T1's z write precedes
           T2's z read, which returns 0 *)
        pose proof (before_trans W _ _ _ HndW A01 A13) as C.
        pose proof (before_trans W _ _ _ HndW C A34) as C'.
        pose proof (before_trans W _ _ _ HndW C' Bab) as C1.
        pose proof (before_trans W _ _ _ HndW C1 B28) as C2.
        pose proof (before_trans W _ _ _ HndW C2 B810) as C3.
        pose proof (before_trans W _ _ _ HndW C3 B1012) as C4.
        exact (nuE_z_after W a0 b12 Hnu Ia0 Ua0 Ib12 Ub12 Hz C4).
      - (* T2's x write precedes T1's x read, which returns 0 *)
        exact (nuE_x_after W b2 a4 Hnu Ib2 Ub2 Ia4 Ua4 Hx Bba).
    Qed.

    (** The 42-event history: all 21 invocations (T1's, then T2's), then
        all 21 responses.  No response precedes an invocation, so only the
        same-thread clause of [rhb] applies. *)
    Definition U : list (ThreadEvent G) :=
      map (mk_inv 1) (ucs q6p0) ++ map (mk_inv 2) (ucs q6p1) ++
      map (mk_res 1) (ucs q6p0) ++ map (mk_res 2) (ucs q6p1).

    Local Ltac invb i j :=
      exists i, j; split; [eexists; split; reflexivity | split; [eexists; split; reflexivity | lia]].

    Lemma U_shape : q6u_shape Some U.
    Proof.
      split; [apply res_incl_of_check; exact eq_refl |].
      split; [invb 0 1 |]. split; [invb 1 3 |]. split; [invb 3 4 |].
      split; [invb 10 16 |]. split; [invb 16 18 |]. invb 18 20.
    Qed.

    Theorem q6_underlay_not_rel_lin : ~ rel_lin Some U (semi_independent G) nuE.
    Proof. exact (q6_underlay_not_rel_lin_any Some U U_shape). Qed.

    (** ** Part 4: real-time obstruction for the registers [x], [y] (Q6-2) *)

    (** Reader (thread 1): one [read()] with one failed iteration (ticket
        1, odd: the writer holds the lock; it reads (0,0) and retries),
        then a successful iteration (ticket 2, (1,1)).  Writer (thread 2):
        one [write(1,1)]. *)
    Definition rtp_r : list SL.Blk := [SL.BR [(1, 0, 0)] 2 1 1].
    Definition rtp_w : list SL.Blk := [SL.BW 1 1].

    Definition rt_info : list (CallKey G * SL.UC) := info_of 1 rtp_r ++ info_of 2 rtp_w.

    Lemma rt_info_x k c : In (k, c) rt_info -> SL.wrx c = None \/ SL.wrx c = Some 1.
    Proof.
      intros H. cbn in H.
      repeat (destruct H as [H | H]; [injection H; intros; subst; cbn; auto |]). destruct H.
    Qed.

    (** The shape the refutation uses: every response is one of the 18
        calls of [rt_info], the writer's [WrX(1)] (key (2,2)) is invoked,
        and its response precedes the invocation of the reader's [RdX] of
        the failed iteration (key (1,2)). *)
    Definition rt_shape {X : Type} (sel : X -> option (ThreadEvent G)) (L : list X) : Prop :=
      (forall j k op ret, res_at sel L j k op ret -> In (k, uc_of op ret) rt_info) /\
      (exists i, inv_at sel L i (2%positive, 2) (sWrX 1)) /\
      (exists i j, res_at sel L i (2%positive, 2) (sWrX 1) tt /\ inv_at sel L j (1%positive, 2) sRdX /\ i < j).

    Theorem rt_iteration_not_rel_lin_any {X : Type} (sel : X -> option (ThreadEvent G)) (L : list X) :
      rt_shape sel L -> ~ rel_lin sel L (semi_independent G) nuE.
    Proof.
      intros (Hres & (i0 & Hi0) & (i & j & Hri & Hj & Hij)) (W & HW).
      pose proof (uvals sel L rt_info W Hres HW) as Hv.
      pose proof HW as (Hnu & Hnd & Hocc & Hall & Hord).
      destruct (Hall _ _ _ Hi0) as (ow & Iw & Kw). destruct (Hall _ _ _ Hj) as (orr & Ir & Kr).
      assert (Uw : SLM.uc rc K ow = SL.WrX 1) by (pose proof (Hv ow Iw) as I; rewrite Kw in I; pick I).
      assert (Ur : SLM.uc rc K orr = SL.RdX 0) by (pose proof (Hv orr Ir) as I; rewrite Kr in I; pick I).
      pose proof (op_from_uc ow _ Uw) as Pw. pose proof (op_from_uc orr _ Ur) as Pr. cbn [op_of] in Pw, Pr.
      assert (Hri' : res_at sel L i (op_key ow) (op_op ow) (op_ret ow)).
      { clear - Hri Kw Pw. destruct ow as [kw opw retw]. cbn [op_key op_op op_ret] in Kw, Pw |- *.
        subst kw opw. destruct retw. exact Hri. }
      assert (B : before W ow orr).
      { apply (Hord ow orr Iw Ir). left. exists i, j.
        split; [exact Hri' |]. split; [rewrite Kr, Pr; exact Hj | exact Hij]. }
      exact (nuE_x_after W ow orr Hnu Iw Uw Ir Ur (fun w Hw => rt_info_x _ _ (Hv w Hw)) B).
    Qed.

    Definition iv (t : positive) (h : nat) (c : SL.UC) : ThreadEvent G := mk_inv t (h, c).
    Definition rs (t : positive) (h : nat) (c : SL.UC) : ThreadEvent G := mk_res t (h, c).

    (** The writer's last three calls and the reader's successful
        iteration, each call responding before the next is invoked. *)
    Definition rt_tail : list (ThreadEvent G) :=
      [ iv 2 3 (SL.WrY 1); rs 2 3 (SL.WrY 1); iv 2 4 SL.WmbC; rs 2 4 SL.WmbC; iv 2 5 SL.Rel; rs 2 5 SL.Rel;
        iv 1 6 (SL.GT 2); rs 1 6 (SL.GT 2); iv 1 7 SL.RmbC; rs 1 7 SL.RmbC;
        iv 1 8 (SL.RdX 1); rs 1 8 (SL.RdX 1); iv 1 9 (SL.RdY 1); rs 1 9 (SL.RdY 1);
        iv 1 10 SL.RmbC; rs 1 10 SL.RmbC; iv 1 11 (SL.TT 2 false); rs 1 11 (SL.TT 2 false) ].

    (** Every call responds before the next call of any thread is
        invoked.  The writer's [WrX(1)] responds (position 5) before the
        reader invokes [RdX] (position 10), which returns 0. *)
    Definition rt_trace : list (ThreadEvent G) :=
      [ iv 2 0 SL.Acq; rs 2 0 SL.Acq; iv 2 1 SL.WmbC; rs 2 1 SL.WmbC;
        iv 2 2 (SL.WrX 1); rs 2 2 (SL.WrX 1);
        iv 1 0 (SL.GT 1); rs 1 0 (SL.GT 1); iv 1 1 SL.RmbC; rs 1 1 SL.RmbC;
        iv 1 2 (SL.RdX 0); rs 1 2 (SL.RdX 0);
        iv 1 3 (SL.RdY 0); rs 1 3 (SL.RdY 0); iv 1 4 SL.RmbC; rs 1 4 SL.RmbC;
        iv 1 5 (SL.TT 1 true); rs 1 5 (SL.TT 1 true) ] ++ rt_tail.

    (** The same events, with the [WrX(1)] response moved after the
        invocation of the reader's [RdX] (equivalently: the reader's
        [GT], first [rmb] and the [RdX] invocation moved before the
        [WrX(1)] response).  The two calls now overlap. *)
    Definition rt_overlap_trace : list (ThreadEvent G) :=
      [ iv 2 0 SL.Acq; rs 2 0 SL.Acq; iv 2 1 SL.WmbC; rs 2 1 SL.WmbC;
        iv 2 2 (SL.WrX 1);
        iv 1 0 (SL.GT 1); rs 1 0 (SL.GT 1); iv 1 1 SL.RmbC; rs 1 1 SL.RmbC;
        iv 1 2 (SL.RdX 0); rs 2 2 (SL.WrX 1); rs 1 2 (SL.RdX 0);
        iv 1 3 (SL.RdY 0); rs 1 3 (SL.RdY 0); iv 1 4 SL.RmbC; rs 1 4 SL.RmbC;
        iv 1 5 (SL.TT 1 true); rs 1 5 (SL.TT 1 true) ] ++ rt_tail.

    Lemma rt_trace_shape : rt_shape Some rt_trace.
    Proof.
      split; [apply res_incl_of_check; exact eq_refl |].
      split; [exists 4; eexists; split; reflexivity |].
      exists 5, 10. split; [eexists; split; reflexivity |]. split; [eexists; split; reflexivity | lia].
    Qed.

    Theorem rt_iteration_not_rel_lin : ~ rel_lin Some rt_trace (semi_independent G) nuE.
    Proof. exact (rt_iteration_not_rel_lin_any Some rt_trace rt_trace_shape). Qed.

    (** *** Control *)

    Definition mkop (t : positive) (h : nat) (c : SL.UC) : Op G :=
      Build_Op (E := G) (t, h) (op_of c) (of_uc (op_of c) c).

    (** The witness: the reader's [RdX] = 0 is placed before the writer's
        [WrX(1)]; everything else in real-time order. *)
    Definition rt_W : list (Op G) :=
      [ mkop 2 0 SL.Acq; mkop 2 1 SL.WmbC; mkop 1 0 (SL.GT 1); mkop 1 1 SL.RmbC; mkop 1 2 (SL.RdX 0);
        mkop 2 2 (SL.WrX 1); mkop 1 3 (SL.RdY 0); mkop 1 4 SL.RmbC; mkop 1 5 (SL.TT 1 true);
        mkop 2 3 (SL.WrY 1); mkop 2 4 SL.WmbC; mkop 2 5 SL.Rel;
        mkop 1 6 (SL.GT 2); mkop 1 7 SL.RmbC; mkop 1 8 (SL.RdX 1); mkop 1 9 (SL.RdY 1); mkop 1 10 SL.RmbC;
        mkop 1 11 (SL.TT 2 false) ].

    Local Ltac occ keq L :=
      match goal with
      | |- occurs _ _ ?o =>
          split; [exists (find_key ikey keq (op_key o) L) | exists (find_key rkey keq (op_key o) L)];
          eexists; split; reflexivity
      end.

    Theorem rt_iteration_overlap_rel_lin : rel_lin Some rt_overlap_trace (semi_independent G) nuE.
    Proof.
      exists rt_W.
      assert (Hnd : NoDup (map op_key rt_W)) by (apply (nodup_keys_of_check (SLM.keyE_dec rc K)); exact eq_refl).
      split; [| split; [exact Hnd | split; [| split]]].
      - intros c. destruct c; cbn; repeat split.
      - intros o Ho. cbn [rt_W In] in Ho.
        repeat (destruct Ho as [<- | Ho]; [occ (SLM.keyE_dec rc K) rt_overlap_trace |]). destruct Ho.
      - apply (cover_of_check (SLM.keyE_dec rc K)). exact eq_refl.
      - apply (rhb_by_check (SLM.keyE_dec rc K)); [exact Hnd | exact eq_refl | exact eq_refl].
    Qed.
  End Underlay.

  (** ** Part 5: module traces *)

  Section Module.
    Context (rc : bool).
    Local Abbreviation G := (E rc SL.plainTL).
    Local Abbreviation nuE := (BL.nuE_all (E := G) SL.comp_dec SLM.compE (SLM.nuEc rc SL.plainTL)).

    (** The underlay hypothesis of [SeqLockModule.seqlock_module_rel_lin]
        fails on every module trace whose underlay part has the shape of
        the Q6 underlay history, or of the real-time iteration. *)
    Corollary q6_module_underlay_not_rel_lin (T : list (ModuleEvent G (F rc))) :
      q6u_shape rc BL.under_sel T -> ~ rel_lin BL.under_sel T (semi_independent G) nuE.
    Proof. apply q6_underlay_not_rel_lin_any. Qed.

    Corollary rt_module_underlay_not_rel_lin (T : list (ModuleEvent G (F rc))) :
      rt_shape rc BL.under_sel T -> ~ rel_lin BL.under_sel T (semi_independent G) nuE.
    Proof. apply rt_iteration_not_rel_lin_any. Qed.

    (** [seqlock_module_rel_lin] is not contradicted by Q6.  By
        contraposition, every complete execution of the module whose
        overlay part shows the Q6 outcome has an underlay part that is not
        relaxed linearizable w.r.t. the register specifications, whatever
        the underlay [VE] is. *)
    Corollary q6_module_hypothesis_fails (VE : LTS G) q0 T c :
      module_execution_tagged VE (M rc SL.plainTL) (initial_tagged_module VE q0) T c ->
      tm_queue c = [] -> (forall e, In e (tm_calls c) -> ce_cell (F rc) e = DeadCall) ->
      q6_shape rc BL.over_sel T 0 ->
      ~ rel_lin BL.under_sel T (semi_independent G) nuE.
    Proof.
      intros Hex Hq Hd Hs Hu.
      exact (q6_not_rel_lin_any rc BL.over_sel T Hs (SLM.seqlock_module_rel_lin rc VE q0 T c Hex Hq Hd Hu)).
    Qed.
  End Module.

End SeqLockQ6.
