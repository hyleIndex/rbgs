(** * Counter_xy by RLHL: nonempty semi-independence with a specification
      meaning (task RLHL-3b, latest-review M-19; the semi-independence
      table and the load-buffering twin, latest-review m-46)

    The first RLHL instances with nonempty semi-independence on both
    signatures whose conclusions have a specification meaning.  Route:
    the decided layering interface (research-intent §8, M-20): the
    underlay presentation is [VE := RelaxedHoareCompLinSpec.EIhl δmem],
    the overlay specification [VF := RelaxedHoareSpec.EI δcxy];
    [rlhl_complin_eihl] turns [RLHL2Hyps] into copy-cat inclusion over
    the plain [EI δmem], and [cc_rel_lin] turns that into relaxed
    linearizability of complete traces.

    ** Objects
    - Underlay [EM]: a two-location memory (locations [CX], [CY]) with
      [Rd l] and [Faa l]; semi-independence [by_location] (two accesses
      are semi-independent iff their locations differ, every pair; the
      COH relation of trace.tex:205); [δmem], the sequential SC cell
      ([Rd l] returns the value of [l], [Faa l] returns it and
      increments it).  [EM_wf].
    - Overlay [FC := CxySig by_counter]: [Inc c], [Get c] for the
      counters [c ∈ {CX, CY}]; [by_counter] (semi-independent iff they
      act on different counters, every pair); [δcxy], the sequential
      two-counter specification ([Inc c] returns the old value of [c]
      and increments it, [Get c] returns it).  [FC_wf].  [F0 := CxySig
      ∅]: the same operations with the empty relation.  [F0_wf].
    - Module [Mcxy si]: [Inc c ↦ call (Faa c)], [Get c ↦ call (Rd c)]
      ([Future op (fun f => Wait f (fun r => Ret r))]), for every overlay
      relation [si]; [M_cxy := Mcxy by_counter], [M_cxy0 := Mcxy ∅].
      The module semantics reads only the underlay relation
      ([RelaxedModuleSemantics.must_precede]), so [M_cxy] and [M_cxy0]
      have the same executions.
    - Inheritance, pair by pair ([cxy_si]): [~ ~ by_location (ρ o1) (ρ
      o2) -> by_counter o1 o2] (in fact the two relations coincide under
      [ρ]); no classical step.

    ** Results (M-19 items 1-7)
    - [cxy_rlhl2] (closed): every field of [RLHL2Hyps Icxy Rcxy Gcxy
      M_cxy cxy_σ0 cxy_v0], derived through [method_sound], as an
      instance of the generic [RelaxedHoareInherit.ren_rlhl2] (the
      review's "Stronger approach 1").  [Icxy]: the coupling of memory
      and counters (one state type, equal states), [eihl_rec_used], and
      the per-thread, age-ordered correspondence between the [ls_inv]
      calls and the pending ghost invocations carrying [ρ o];
      [Rcxy]/[Gcxy]: frame style, memory part "any [EIhl δmem] steps";
      results read through [eihl_mine_*].  Readiness is
      [RelaxedHoareInherit.emit_ready_SI], which replaces the SI = ∅
      [RelaxedHoareChecks.Counter.emit_ready].
    - [cxy_complin_ei] ([classic]) and [cxy_rel_lin] ([classic],
      [eq_rect_eq]): copy-cat inclusion over [EI δmem], and relaxed
      linearizability under [by_counter] of every complete overlay trace
      of [M_cxy] over [EI δmem].
    - The SB witness (item 5).  [sb_exec si] (closed): a complete
      execution of [Mcxy si] over [EI δmem], built from [tagged_invoke],
      [tagged_underlay] and [tagged_return]: thread [t1] invokes [inc_x],
      then [get_y] while [inc_x] is pending, and [get_y] returns 0;
      thread [t2] symmetrically; each [Rd] is emitted before its own
      thread's pending [Faa] (they are semi-independent by location);
      all calls return ([sb_complete]).
      - [sb_rel_lin] (through [cxy_rel_lin]) and [sb_rel_lin_direct]
        (closed, explicit witness [get_y 0; get_x 0; inc_x 0; inc_y 0]):
        relaxed-linearizable under [by_counter].
      - [sb_not_rel_lin0] (closed): not relaxed-linearizable under ∅.
        The argument goes through legality, not an rhb cycle (review
        wording correction): only [inc_x → get_y] and [inc_y → get_x]
        are rhb edges under ∅; [get_y] before [inc_y] and [get_x] before
        [inc_x] come from [seq_legal], since each [get] returns 0
        ([seq_inc_get]).
      - [sb_si_decides] (closed): both, on the same trace.
    - The universal negative (item 6): [cxy0_no_rlhl2]: for every [I],
      [R], [G], [~ RLHL2Hyps I R G M_cxy0 cxy_σ0 cxy0_v0] (same bodies
      and underlay, overlay relation ∅): [rlhl_complin_eihl], then
      [cc_rel_lin], then [sb_not_rel_lin0].  [cxy_discriminates_rlhl2]
      pairs it with [cxy_rlhl2].
    - [CounterAsRename.counter_ren_rlhl2] (closed): the SI = ∅ FAA→Inc
      counter of [RelaxedHoareChecks.CounterEIhl] is an instance of the
      same generic theorem.
    - Item 7: option (a) delivered, [CounterXYZ].  Every operation also
      increments a private statistics location [z] (no overlay operation
      reads it): the body issues the linearizing access and [Faa z],
      then waits for both before [Ret].  The two invocations are
      semi-independent by location, so the module may emit them in
      either order ([z_reorder_exec], closed: the own [Faa z] of an
      [inc_x] is emitted before its [Faa x]).  [cxyz_rlhl2] (closed,
      through [method_sound]) is derived with own-event premises
      discharged by genuine stability arguments (not vacuous, not
      [Stable_true], not refuted by [before]): [Gzz_keeps_KInv]
      ([ns_if_old_start], slots 1 and 3), [Gzz_keeps_KLini]
      ([ns_if_new_in] at slot 2 and [ns_if_old_in] at slot 3: the
      ownership of the linearizing record survives the own [z] steps, by
      [eihl_mine_steps]; the coupling is untouched by a [z] access),
      [Gz_keeps_KZ] ([ns_if_new_in] at slot 3), [Gzz_keeps_KLinr]
      ([bw_if]).  The [z] events get the finer guarantee [Gzz] (memory
      moves, the possibility does not); [Gz k ⊄ Rz k], so
      [newslot_guar_in_rely] does not apply.  Limitation: [z] is
      invisible to the overlay, so these are frame facts (ownership and
      an unchanged possibility), not facts about interfering values.
      [CounterXYZ.Gz_breaks_KInv] (closed): with the method-level
      guarantee [Gz k] at slot 1, the [ns_if_old_start] premise there
      would be false, so the finer [Gzz] is needed in this derivation.
    - The semi-independence table (m-46; the two sections at the end of
      the file).  The same bodies over the same cell, for
      underlay/overlay relations (SI_E, SI_F) ∈ {∅, [si_mb],
      [by_location]} × {∅, [si_cb], [by_counter]}, where choice (b) is
      [si_mb] (a [Faa l] may be passed by a later [Rd l'], [l ≠ l']) and
      [si_cb] (an [Inc c] by a later [Get c'], [c ≠ c']); "free" marks
      the four cells of the final section (m-49):

      | SI_E \ SI_F    | ∅        | si_cb (b) | by_counter (a) |
      |----------------|----------|-----------|----------------|
      | ∅              | ✓        | ✓ free    | ✓ free         |
      | si_mb (b)      | ✗ free   | ✓         | ✓ free         |
      | by_location    | ✗        | ✗ (mixed) | ✓              |

      ✓ is an [RLHL2Hyps] instance (closed, from [ren_rlhl2]):
      [cxy00_rlhl2], [cxyb_rlhl2], [cxy_rlhl2]; ✗ is a universal
      negative (∀ [I] [R] [G]): [cxy0_no_rlhl2] (through SB) and
      [cxy_mixed_no_rlhl2] (through LB); [cxy_si_table] collects them.
      The free cells: ✓ [cxy0cb_rlhl2], [cxy0cnt_rlhl2],
      [cxybcnt_rlhl2] (instances of [mgen_rlhl2], i.e. [ren_rlhl2];
      inheritance trivial or by inclusion), ✗ [cxyb0_no_rlhl2] (through
      SB, [sb_exec_gen] at [si_mb]).  [cxy_si_char]: on these nine pairs
      (and only these), [RLHL2Hyps] has a model iff SI_E ∘ ρ ⊆ SI_F; the
      statement for arbitrary relations is not proved (its ⇒ half needs
      a non-relaxed-linearizable witness for every crossing pair).
      [EMb_wf], [FCb_wf], [E00_wf]: the new signatures are well-formed
      ([RelaxedSig.well_formed] allows asymmetric relations).
      - SB: [sb_exec_gen] (closed): the SB execution exists for every
        underlay relation containing [(Faa x, Rd y)] and [(Faa y, Rd x)]
        ([sb_exec_gen_loc] is [sb_exec]'s statement as its instance);
        [sb_rel_lin_gen] (closed): accepted under every overlay relation
        containing [(Inc x, Get y)] and [(Inc y, Get x)]; under (b):
        [sb_rel_lin_cb] (closed) and [sb_rel_lin_b] (through
        [cxyb_rel_lin] and the execution [sb_mtraces_b] of the (b)
        module).
      - LB: [lb_exec] (closed): a complete, module-derived execution of
        [Mcxy si] over [EI δmem] in which [t1] invokes [get_x] then
        [inc_y], [t2] invokes [get_y] then [inc_x], each [Faa] is
        emitted before its own thread's pending [Rd], both [inc]s
        return 0 and both [get]s return 1.  Accepted under (a)
        ([lb_rel_lin_direct], closed; [lb_rel_lin] through
        [cxy_rel_lin]); rejected under every overlay relation without
        [(Get x, Inc y)] and [(Get y, Inc x)] ([lb_not_rel_lin_gen],
        closed: the two rhb edges plus [seq_legal], since each [get]
        reading 1 needs the other thread's [inc] before it), in
        particular under [si_cb] and ∅ ([lb_si_decides]).
        [lb_not_trace_b]: LB is not a trace of the (b) module.
      - So SB is accepted under (a) and (b), LB only under (a).  On the
        same LB trace the overlay relation alone decides acceptance
        ([lb_si_decides]); for the same by-location module it alone
        decides RLHL provability ((a) ✓, mixed ✗).  The module verified
        against [si_cb] needs the narrower underlay relation [si_mb],
        and then the LB trace is not among its traces
        ([lb_not_trace_b]; about this trace only, not a general
        LB-freedom theorem).

    ** Scope and recorded simplifications
    - Choice (a) of M-19 item 3 (semi-independence by location for the
      memory and by counter for the overlay, every pair) is a
      simplification of the paper's RC version; choice (b) ([si_mb],
      [si_cb]; [cxyb_rlhl2]) matches the readiness of 2Counter.tex:41
      and :53 exactly (see difference (2)), so the Coq carries either
      reading of I_Counter_xy.  Appendix/2Counter.tex builds Counter_xy
      on RCMem with [faa(x, 1, rel)] and [rd(x, acq)] (:3, :26, :51);
      the printed I_RC (trace.tex:388-396) lists only wrt/rd pairs, no
      RMW rows, and I_Counter_xy is printed nowhere (latest-review m-40,
      escalated to the author).  [si_mb] is I_RC (trace.tex:393)
      restricted to [faa(·, rel)] and [rd(·, acq)]; I_RC prints no RMW
      row, so treating [faa] as a write (or as a componentwise RMW, a
      read plus a write) is an interpretation; both readings give
      [si_mb] (latest-review m-48; a hand derivation, not mechanized,
      since the signatures do not carry the modes).  Release/acquire
      modes are compiled into [si_mb]; the mode field is [Local] on
      every signature and unused (neither [rel_lin] nor
      [module_step_tagged] reads it).
      Choice (a) uses the COH relation [by_location], which has no
      modes.
    - The underlay is ν;cc of the SC cell under [by_location] (the
      copy-cat over [EI δmem]), not RCMem, not the buffered memory of
      [memory/] (nothing here imports [memory/]), and not RC11.  Only
      ν;cc ⊆ rel_lin is proved ([cc_rel_lin]); its converse is open
      (M-20), and identifying [M_cxy] over [EI δmem] with
      ν_E;cc_E;⟦M⟧ needs the unproved absorption lemma (M-22).
    - [rel_lin] conclusions are for complete traces; the copy-cat
      inclusions are for every trace.  One possibility, no error clause
      (m-8), run-to-completion module semantics (m-33).

    ** K / S / P / R against Appendix/2Counter.tex
    - K: as listed above.  The [RLHL2Hyps] proofs ([cxy_rlhl2],
      [cxyb_rlhl2], [cxy00_rlhl2], [cxyz_rlhl2], [counter_ren_rlhl2],
      and, in the final section, [mgen_rlhl2], [cxy0cb_rlhl2],
      [cxy0cnt_rlhl2], [cxybcnt_rlhl2]),
      the executions ([sb_exec], [sb_exec_gen], [lb_exec],
      [z_reorder_exec]) and the trace-level facts ([sb_rel_lin_direct],
      [sb_rel_lin_gen], [sb_rel_lin_cb], [sb_not_rel_lin0],
      [sb_si_decides], [lb_rel_lin_direct], [lb_not_rel_lin_gen],
      [lb_si_decides]) are closed; the corollaries through
      [rlhl_complin_eihl] use [classic], those through [cc_rel_lin]
      (including [sb_rel_lin], [sb_rel_lin_b], [lb_rel_lin],
      [lb_not_trace_b], [cxy_si_table], [cxy_si_char] and the universal
      negatives [cxy0_no_rlhl2], [cxy_mixed_no_rlhl2], [cxyb0_no_rlhl2])
      use [classic] and [eq_rect_eq].
    - S: Counter_xy over the SC two-location cell with SI by location,
      overlay SI by counter, [Inc] returning the old value; the SB trace
      is accepted under [by_counter] and rejected under ∅, and the same
      module bodies have no RLHL proof at all under ∅; with choice (b)
      the bodies have an RLHL proof and SB is accepted; the LB trace of
      the by-location module is accepted under [by_counter] only, and
      the by-location module has no RLHL proof against [si_cb]; on the
      nine pairs of relations of the table, RLHL provability of the
      bodies is exactly SI_E ∘ ρ ⊆ SI_F ([cxy_si_char]).
    - P: 2Counter.tex is in the TR only (main-tr.tex:262; main.tex:261
      is commented out).  :5: ν_RCMem "is exactly the same as the memory
      cell specification under sequential consistency"; :12: an
      invariant counting [#inc_l = #faa_l]; :41: when [rd(x)] executes,
      "the only pending operations in this thread can be unfinished
      [inc_y] operations"; :53: [inc_x] has no older pending operation
      ([s_O' = ε]); :57: [inc_x] returns [ok].  intro.tex:99 ("pending,
      independent operations within the verifying thread") and
      implex.tex:3 (the rely admits "the verifying thread's own
      independent futures"; RLHL "can specify patterns such as load
      buffering").  trace.tex:205: the COH signature, with I_COH by
      location; trace.tex:388-396: I_RC, whose rows are
      (wrt, wrt), (rd, rd), (rd, wrt) and (wrt, rd) on different
      locations with mode conditions, and no RMW row.
    - Differences between S and P:
      (1) memory: the SC cell plus [by_location] (or [si_mb], ∅)
          instead of RCMem with I_RC and modes.  The underlay is
          replaced by, not derived from, the paper's premise at :5
          (RCMem traces are relaxed-linearizable to the SC cell under
          I_RC): nothing here assumes or proves :5.  Even granting :5, a
          link from it to this file needs the converse of [cc_rel_lin]
          (rel_lin ⊆ ν;cc, open, M-20) and [mtraces_mono] plus
          absorption (M-22); RCMem itself is not mechanized (m-37);
      (2) readiness: [emit_ready_SI] admits as older pending same-thread
          calls every call on the other counter ([inc_y] and [get_y]
          for [get_x]; [inc_y] and [get_y] for [inc_x]), whereas :41
          admits only [inc_y] for [get_x] and :53 nothing for [inc_x];
          with modes (a release FAA, acquire reads, I_RC) only
          [(inc_l, get_l')] pairs would be semi-independent.  That is
          choice (b) of M-19 item 3, now also an instance
          ([cxyb_rlhl2]: [si_cb] admits exactly [inc_y] for [get_x] and
          nothing for [inc_x], as :41 and :53); which one is the paper's
          I_Counter_xy is the author's decision (m-40).  The two choices
          differ observably: LB is accepted under (a) and not under (b)
          ([lb_si_decides]);
      (3) [Inc c] returns the old value (the [Faa] result); the paper's
          [inc_x] returns [ok];
      (4) the invariant equates states instead of counting operations
          (:12), and the possibility is a single [Poss], not a set;
      (5) the derivation is Coq's [RProvable] judgement with slots and
          the ghost thread frontier, checked by [method_sound], not the
          printed EStep outlines (latest-review M-21);
      (6) own-thread interference, two readings (m-43).  The sentences
          App. relaxedlin.tex:626 (R_π is the rely "when the same thread
          is executing some other independent operation"), implex.tex:3
          and intro.tex:99 fit either reading, so attributing them to
          one is an interpretation.  Inter-call (one reading of :626):
          [R k] ⊇ [G k'] for every other call [k'], same-thread ones
          included ([RLHL2Hyps.h_guar_rely]).  This is necessarily
          larger than an R_π restricted to independent operations: the
          module semantics runs an older non-independent same-thread
          call's events while [k] is pending ([tagged_invoke] checks
          only [call_fresh]; F2, [must_precede], then forces e.g. an
          older [inc_x]'s [Faa CX] before a younger same-thread
          [get_x]'s [Rd CX]).  Exercised here by [cxy_rlhl2], where
          [sb_exec] and [lb_exec] have same-thread pending calls that
          are crossed, and by [cxyb_rlhl2], with the SB execution
          [sb_exec_gen] at [si_mb] ([sb_mtraces_b]; LB is not a trace of
          [Mb], [lb_not_trace_b]).  Intra-call (programlogic.tex:308:
          "treat the events a method emits out of program order as
          interference by the thread's own independent operations"; its
          closest printed counterpart is the commented-out EStep
          premise, programlogic.tex:558; lines as in async-ccal commit
          4a2db8e1, where :308 is unchanged and :558 was :516 in
          01484091): the own events of one call are
          checked pairwise ([ns_if_*]) against a finer per-event
          guarantee, never put into [R k]; exercised only as frame facts
          ([CounterXYZ], m-45).
    - R: Reviewer B (popl2027-reviews.md:309-311): "skeptical that
      specifying a concurrent object solely in terms of instruction
      reordering yields a useful abstraction or workable reasoning
      principles".  This file is one data point at the logic level: the
      overlay relation alone decides whether the SB behaviour is
      accepted, and decides RLHL provability of the same code; and the
      overlay relation alone separates SB-only ((b)) from SB+LB ((a))
      on the traces ([lb_si_decides]), with RLHL proofs on both sides,
      the (b) side over the narrower underlay relation [si_mb]
      ([cxyb_rlhl2]).  The mixed negative
      [cxy_mixed_no_rlhl2] answers the remark of the RLHL-3b iteration-1
      review (Redesign assessment, citing m-36) that a by-location
      underlay with a narrower overlay relation may need prophecy: for
      [si_cb] it is not a limitation of the proof method; the module has
      a trace (LB) that is not relaxed-linearizable under [si_cb], so no
      proof in any logic sound for [rel_lin] can exist, with or without
      prophecy.  It does not answer the rest of Reviewer B's chain
      (:313-316: soundness "against a weak memory model such as RC11",
      a client; B-1). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
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
Require Import models.simlin.RelaxedHoareBase.
Require Import models.simlin.RelaxedHoareDag.
Require Import models.simlin.RelaxedHoare.
Require Import models.simlin.RelaxedHoareSound.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareGSim.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareInherit.
Require Import examples.Relaxed.RelaxedHoareChecks.

Import ListNotations.


Module RelaxedHoareCounterXY.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedPossibility.
  Import RelaxedHoareCompLin.
  Import RelaxedHoareCompLinSpec.
  Import RelaxedHoareBase.
  Import RelaxedHoareDag.
  Import RelaxedHoare.
  Import RelaxedHoareSound.
  Import RelaxedHoareInherit.

  (** ** Locations, counters and the two signatures *)

  Inductive CLoc : Type := CX | CY.

  (** *** Underlay: a two-location memory with [Rd] and [Faa] *)

  Inductive MOp : Type :=
  | Rd (l : CLoc)
  | Faa (l : CLoc).

  Definition m_ar (_ : MOp) : Type := nat.

  Canonical Structure MEff : Sig.t := {| Sig.op := MOp; Sig.ar := m_ar |}.

  Definition mloc (o : MOp) : CLoc := match o with Rd l | Faa l => l end.

  (** Semi-independence by location, every pair (COH-style, trace.tex:205;
      a simplification of the paper's RC version, see the header). *)
  Definition by_location (o1 o2 : MOp) : Prop := mloc o1 <> mloc o2.

  Definition EM : RelaxedSig.t :=
    {|
      RelaxedSig.effect := MEff;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := by_location;
      RelaxedSig.mode := fun _ => Local;
    |}.

  Lemma EM_wf : RelaxedSig.well_formed EM.
  Proof. constructor; [intros o H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

  (** The memory state: the values of [x] and [y]. *)
  Definition MSt : Type := (nat * nat)%type.

  Definition get (s : MSt) (l : CLoc) : nat := match l with CX => fst s | CY => snd s end.
  Definition put (s : MSt) (l : CLoc) (v : nat) : MSt :=
    match l with CX => (v, snd s) | CY => (fst s, v) end.

  (** The sequential SC cell (2Counter.tex:5: ν_RCMem "is exactly the
      same as the memory cell specification under sequential
      consistency"): [Rd l] returns the value of [l]; [Faa l] returns it
      and increments it. *)
  Definition δmem : MSt -> forall o : Sig.op (RelaxedSig.effect EM), Sig.ar o -> MSt -> Prop :=
    fun s o =>
      match o as o0 return Sig.ar o0 -> MSt -> Prop with
      | Rd l => fun r s' => r = get s l /\ s' = s
      | Faa l => fun r s' => r = get s l /\ s' = put s l (S (get s l))
      end.

  (** *** Overlay: two counters *)

  Inductive COp : Type :=
  | Inc (c : CLoc)
  | Get (c : CLoc).

  Definition c_ar (_ : COp) : Type := nat.

  Canonical Structure CEff : Sig.t := {| Sig.op := COp; Sig.ar := c_ar |}.

  Definition cloc (o : COp) : CLoc := match o with Inc c | Get c => c end.

  (** The overlay signature, for a given semi-independence relation. *)
  Definition CxySig (si : COp -> COp -> Prop) : RelaxedSig.t :=
    {|
      RelaxedSig.effect := CEff;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := si;
      RelaxedSig.mode := fun _ => Local;
    |}.

  (** Semi-independence by counter, every pair. *)
  Definition by_counter (o1 o2 : COp) : Prop := cloc o1 <> cloc o2.

  Definition FC : RelaxedSig.t := CxySig by_counter.

  (** The same operations with the empty relation (SI = ∅). *)
  Definition F0 : RelaxedSig.t := CxySig (fun _ _ => False).

  Lemma FC_wf : RelaxedSig.well_formed FC.
  Proof. constructor; [intros o H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

  Lemma F0_wf : RelaxedSig.well_formed F0.
  Proof. constructor; [intros o H; exact H | intros _ _ [] | intros _ _ []]. Qed.

  (** The sequential two-counter specification: [Inc c] returns the old
      value of [c] and increments it, [Get c] returns it. *)
  Definition δcxy : MSt -> forall o : Sig.op CEff, Sig.ar o -> MSt -> Prop :=
    fun s o =>
      match o as o0 return Sig.ar o0 -> MSt -> Prop with
      | Inc c => fun r s' => r = get s c /\ s' = put s c (S (get s c))
      | Get c => fun r s' => r = get s c /\ s' = s
      end.

  (** *** The module: [inc_c ↦ call (Faa c)], [get_c ↦ call (Rd c)] *)

  Definition ρ (o : COp) : MOp := match o with Inc c => Faa c | Get c => Rd c end.

  Lemma mloc_ρ o : mloc (ρ o) = cloc o.
  Proof. destruct o; reflexivity. Qed.

  Definition Mcxy (si : COp -> COp -> Prop) : RelaxedModuleImpl EM (CxySig si) :=
    fun o _ => @Future EM (Sig.ar o) (ρ o) (fun f => Wait f (fun r => Ret r)).

  Definition M_cxy : RelaxedModuleImpl EM FC := Mcxy by_counter.
  Definition M_cxy0 : RelaxedModuleImpl EM F0 := Mcxy (fun _ _ => False).

  (** Initial states: memory [(0, 0)], counters [(0, 0)], nothing
      pending, no key used. *)
  Definition s00 : MSt := (0, 0).
  Definition cxy_σ0 : State (EIhl δmem) := ((s00, []), []).
  Definition cxy_v0 : State (@RelaxedHoareSpec.EI FC MSt δcxy) := (s00, []).

  (** ** The instance (M-19 items 1-4) *)

  Definition backc (o : Sig.op (RelaxedSig.effect FC)) (r : Sig.ar (ρ o)) : Sig.ar o := r.

  Lemma cxy_δ : forall s o r s', δmem s (ρ o) r s' -> δcxy s o (backc o r) s'.
  Proof. intros s [c | c] r s' H; exact H. Qed.

  (** Inheritance: semi-independent memory operations come from
      semi-independent counter operations; constructive, since both
      relations are negations. *)
  Lemma cxy_si : forall o1 o2 : COp, ~ ~ by_location (ρ o1) (ρ o2) -> by_counter o1 o2.
  Proof.
    intros o1 o2 Hnn Heq. apply Hnn. unfold by_location. rewrite !mloc_ρ. intros Hne. exact (Hne Heq).
  Qed.

  Lemma cxy_inj : forall u o (r1 r2 : Sig.ar (ρ o)),
      @RelaxedTraceLin.Build_Op EM u (ρ o) r1 = @RelaxedTraceLin.Build_Op EM u (ρ o) r2 -> backc o r1 = backc o r2.
  Proof. intros u o r1 r2 H. exact (f_equal (fun x : RelaxedTraceLin.Op EM => (RelaxedTraceLin.op_ret x : nat)) H). Qed.

  Lemma cxy_M : forall o t, M_cxy o t = @Future EM (Sig.ar o) (ρ o) (fun f => Wait f (fun r => Ret (backc o r))).
  Proof. reflexivity. Qed.

  Definition Icxy : Assn (EIhl δmem) (@RelaxedHoareSpec.EI FC MSt δcxy) :=
    @Iren EM FC MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true).
  Definition Rcxy : CallKey FC -> PRel (EIhl δmem) (@RelaxedHoareSpec.EI FC MSt δcxy) :=
    @Rren EM FC MSt MSt δmem δcxy.
  Definition Gcxy : CallKey FC -> PRel (EIhl δmem) (@RelaxedHoareSpec.EI FC MSt δcxy) :=
    @Gren EM FC MSt MSt δmem δcxy.

  (** M-19: every field of [RLHL2Hyps] holds for Counter_xy over
      [EIhl δmem] into [EI δcxy], with nonempty semi-independence on
      both signatures; derived through [method_sound]
      ([RelaxedHoareInherit.ren_rlhl2]; abstraction [fun s => s], every
      underlay invocation linearizing). *)
  Theorem cxy_rlhl2 : RLHL2Hyps Icxy Rcxy Gcxy M_cxy cxy_σ0 cxy_v0.
  Proof.
    exact (@ren_rlhl2 EM FC MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true) backc cxy_δ cxy_si
             (fun _ => eq_refl) cxy_inj M_cxy cxy_M s00).
  Qed.

  (** Copy-cat inclusion over the plain [EI δmem] ([classic]). *)
  Theorem cxy_complin_ei :
    RCompLin M_cxy (RelaxedHoareSpec.EI δmem) (s00, []) (@RelaxedHoareSpec.EI FC MSt δcxy) (s00, []).
  Proof. exact (rlhl_complin_eihl δmem (F := FC) δcxy s00 Icxy Rcxy Gcxy M_cxy (s00, []) cxy_rlhl2). Qed.

  (** Every complete overlay trace of Counter_xy over [EI δmem] is
      relaxed-linearizable under semi-independence by counter
      ([classic], [eq_rect_eq]). *)
  Corollary cxy_rel_lin s :
    MTraces (RelaxedHoareSpec.EI δmem) M_cxy (s00, []) s -> PrefixView.complete s ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel FC) s by_counter (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
  Proof. exact (complin_ei_rel_lin (F := FC) δcxy s00 M_cxy (RelaxedHoareSpec.EI δmem) (s00, []) cxy_complin_ei s). Qed.

  (** ** The store-buffering execution (M-19 item 5)

      Generic in the overlay relation [si]: the module semantics reads
      only the underlay relation ([RelaxedModuleSemantics.must_precede]),
      so the same execution exists for [FC] and for [F0]. *)

  Definition t1 : tid := 1%positive.
  Definition t2 : tid := 2%positive.

  Definition ui (t : tid) (hu : nat) (o : MOp) : TaggedEvent EM :=
    Build_TaggedEvent (Build_ThreadEvent t (@InvEv EM hu o)) (resolved_in (@empty_store EM)).
  Definition ur (t : tid) (hu : nat) (o : MOp) (r : nat) : TaggedEvent EM :=
    Build_TaggedEvent (Build_ThreadEvent t (@ResEv EM hu o r)) no_deps.

  (** Frontier facts for one thread. *)
  Lemma cross_inv_inv t h1 o1 d1 h2 o2 d2 :
    mloc o1 <> mloc o2 ->
    tagged_can_cross (Build_TaggedEvent (Build_ThreadEvent t (@InvEv EM h1 o1)) d1)
                     (Build_TaggedEvent (Build_ThreadEvent t (@InvEv EM h2 o2)) d2).
  Proof. intros Hne. right. split; [reflexivity |]. unfold must_precede. cbn. intros H. exact (H Hne). Qed.

  Lemma cross_res_inv t h1 o1 r1 h2 o2 : tagged_can_cross (ur t h1 o1 r1) (ui t h2 o2).
  Proof. right. split; [reflexivity |]. unfold must_precede. cbn. apply resolved_in_empty. Qed.

  Lemma cross_inv_res t h1 o1 d h2 o2 r :
    h1 <> h2 -> tagged_can_cross (Build_TaggedEvent (Build_ThreadEvent t (@InvEv EM h1 o1)) d) (ur t h2 o2 r).
  Proof. intros Hne. right. split; [reflexivity |]. unfold must_precede. cbn. exact Hne. Qed.

  Lemma cross_res_res t h1 o1 r1 h2 o2 r2 : tagged_can_cross (ur t h1 o1 r1) (ur t h2 o2 r2).
  Proof. right. split; [reflexivity |]. unfold must_precede. cbn. intros []. Qed.

  Lemma cross_thread (a b : TaggedEvent EM) :
    te_tid EM (untag a) <> te_tid EM (untag b) -> tagged_can_cross a b.
  Proof. intros H. left. exact H. Qed.

  Section SB.
    Context (si : COp -> COp -> Prop).
    Local Abbreviation F := (CxySig si).
    Local Abbreviation V := (@RelaxedHoareSpec.EI EM MSt δmem).

    Lemma call_produces t (o : COp) (hu r : nat) :
      program_produces_tagged t (Mcxy si o t) [ui t hu (ρ o); ur t hu (ρ o) r] r.
    Proof.
      exists (Build_ProgramConfig (Ret r) [@Build_FutureEntry EM hu (@Resolved EM (ρ o) r)]). split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future EM (Sig.ar o) t (ρ o) (fun f => Wait f (fun (x : nat) => Ret x)) hu (@empty_store EM)).
          intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending EM (Sig.ar o) t (ρ o) hu r (fun (x : nat) => Ret x)). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. constructor; [exact Logic.I | constructor].
    Qed.

    Definition oi (t : tid) (h : nat) (o : COp) : ThreadEvent F := Build_ThreadEvent t (@InvEv F h o).
    Definition orr (t : tid) (h : nat) (o : COp) (r : nat) : ThreadEvent F := Build_ThreadEvent t (@ResEv F h o r).

    (** Thread [t1]: [inc_x] (handle 0), then [get_y] (handle 1) while
        [inc_x] is pending; thread [t2] symmetrically.  Each [Rd] is
        emitted before its own thread's pending [Faa] (the two are
        semi-independent by location), and returns 0. *)
    Definition sb_evs : list (ModuleEvent EM F) :=
      [OverlayEvent (oi t1 0 (Inc CX)); OverlayEvent (oi t1 1 (Get CY));
       OverlayEvent (oi t2 0 (Inc CY)); OverlayEvent (oi t2 1 (Get CX));
       UnderlayEvent (untag (ui t1 1 (Rd CY))); UnderlayEvent (untag (ur t1 1 (Rd CY) 0));
       OverlayEvent (orr t1 1 (Get CY) 0);
       UnderlayEvent (untag (ui t2 1 (Rd CX))); UnderlayEvent (untag (ur t2 1 (Rd CX) 0));
       OverlayEvent (orr t2 1 (Get CX) 0);
       UnderlayEvent (untag (ui t1 0 (Faa CX))); UnderlayEvent (untag (ur t1 0 (Faa CX) 0));
       OverlayEvent (orr t1 0 (Inc CX) 0);
       UnderlayEvent (untag (ui t2 0 (Faa CY))); UnderlayEvent (untag (ur t2 0 (Faa CY) 0));
       OverlayEvent (orr t2 0 (Inc CY) 0)].

    Definition sb_trace : list (ThreadEvent F) :=
      [oi t1 0 (Inc CX); oi t1 1 (Get CY); oi t2 0 (Inc CY); oi t2 1 (Get CX);
       orr t1 1 (Get CY) 0; orr t2 1 (Get CX) 0; orr t1 0 (Inc CX) 0; orr t2 0 (Inc CY) 0].

    Lemma sb_overlay : RelaxedGSim.overlay_events sb_evs = sb_trace.
    Proof. reflexivity. Qed.

    Local Ltac nin := cbn; let H := fresh in intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.

    (** The execution, from module steps ([tagged_invoke],
        [tagged_underlay], [tagged_return]) over the plain [EI δmem];
        every call returns. *)
    Theorem sb_exec :
      exists c, module_execution_tagged V (Mcxy si) (initial_tagged_module V (s00, [])) sb_evs c /\
        (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall).
    Proof.
      eexists. split.
      - unfold sb_evs.
        (* the four invocations *)
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t1 0 (Inc CX) (s00, []) [] [] [] [ui t1 0 (Faa CX); ur t1 0 (Faa CX) 0] 0).
          - intros [].
          - apply call_produces.
          - split; [repeat constructor; intros [] | intros key Hk []]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t1 1 (Get CY) (s00, []) _ _ _ [ui t1 1 (Rd CY); ur t1 1 (Rd CY) 0] 0).
          - nin.
          - apply call_produces.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t2 0 (Inc CY) (s00, []) _ _ _ [ui t2 0 (Faa CY); ur t2 0 (Faa CY) 0] 0).
          - nin.
          - apply call_produces.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t2 1 (Get CX) (s00, []) _ _ _ [ui t2 1 (Rd CX); ur t2 1 (Rd CX) 0] 0).
          - nin.
          - apply call_produces.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        (* t1's read of y overtakes t1's pending FAA on x *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 1) (ui t1 1 (Rd CY)))).
          - cbn. apply tagged_select_next; [apply cross_inv_inv; discriminate |].
            apply tagged_select_next; [apply cross_res_inv |]. apply tagged_select_here.
          - cbn. exists 0, s00. split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 1) (ur t1 1 (Rd CY) 0))).
          - cbn. apply tagged_select_next; [apply cross_inv_res; discriminate |].
            apply tagged_select_next; [apply cross_res_res |]. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        (* t2's read of x overtakes t2's pending FAA on y *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 1) (ui t2 1 (Rd CX)))).
          - cbn. apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_inv_inv; discriminate |].
            apply tagged_select_next; [apply cross_res_inv |]. apply tagged_select_here.
          - cbn. exists 0, s00. split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 1) (ur t2 1 (Rd CX) 0))).
          - cbn. apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_inv_res; discriminate |].
            apply tagged_select_next; [apply cross_res_res |]. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_here.
          - nin. }
        (* the two FAAs *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 0) (ui t1 0 (Faa CX)))).
          - cbn. apply tagged_select_here.
          - cbn. exists 0, (1, 0). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 0) (ur t1 0 (Faa CX) 0))).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 0) (ui t2 0 (Faa CY)))).
          - cbn. apply tagged_select_here.
          - cbn. exists 0, (1, 1). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 0) (ur t2 0 (Faa CY) 0))).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        apply tagged_module_execution_refl.
      - intros e He. cbn in He. repeat (destruct He as [<- | He]; [reflexivity |]). destruct He.
    Qed.

    Corollary sb_mtraces : MTraces V (Mcxy si) (s00, []) sb_trace.
    Proof. destruct sb_exec as (c & Hex & _). exists sb_evs, c. split; [exact Hex | reflexivity]. Qed.

    (** *** The events of the trace *)

    Abbreviation sel := (@PrefixView.sel F).

    Definition ev_val (e : ThreadEvent F) : nat :=
      match te_ev F e with ResEv _ _ r => r | InvEv _ _ => 0 end.
    Definition ev_op (e : ThreadEvent F) : COp := event_op (te_ev F e).
    Definition ev_h (e : ThreadEvent F) : nat := event_handle (te_ev F e).
    Definition ev_isres (e : ThreadEvent F) : bool :=
      match te_ev F e with ResEv _ _ _ => true | InvEv _ _ => false end.

    Lemma sb_inv_cases i k (op : COp) :
      RelaxedTraceLin.inv_at sel sb_trace i k op ->
      (i = 0 /\ k = (t1, 0) /\ op = Inc CX) \/ (i = 1 /\ k = (t1, 1) /\ op = Get CY) \/
      (i = 2 /\ k = (t2, 0) /\ op = Inc CY) \/ (i = 3 /\ k = (t2, 1) /\ op = Get CX).
    Proof.
      intros (x & Hx & Hs). destruct k as [t h]. cbn [fst snd] in Hs.
      do 8 (destruct i as [| i]; [cbn in Hx; injection Hx as <-; cbn in Hs;
             first [discriminate Hs | injection Hs as Ht Hh Ho; subst; tauto] |]).
      destruct i; cbn in Hx; discriminate Hx.
    Qed.

    Lemma sb_res_cases j k (op : COp) (r : Sig.ar op) :
      RelaxedTraceLin.res_at sel sb_trace j k op r ->
      (j = 4 /\ k = (t1, 1) /\ op = Get CY /\ r = 0) \/ (j = 5 /\ k = (t2, 1) /\ op = Get CX /\ r = 0) \/
      (j = 6 /\ k = (t1, 0) /\ op = Inc CX /\ r = 0) \/ (j = 7 /\ k = (t2, 0) /\ op = Inc CY /\ r = 0).
    Proof.
      intros (x & Hx & Hs). destruct k as [t h]. cbn [fst snd] in Hs.
      pose proof (f_equal (option_map (te_tid F)) Hs) as Ht.
      pose proof (f_equal (option_map ev_h) Hs) as Hh.
      pose proof (f_equal (option_map ev_op) Hs) as Ho.
      pose proof (f_equal (option_map ev_val) Hs) as Hr.
      pose proof (f_equal (option_map ev_isres) Hs) as Hk.
      clear Hs. cbn in Ht, Hh, Ho, Hr, Hk.
      do 8 (destruct j as [| j]; [cbn in Hx; injection Hx as <-; cbn in Ht, Hh, Ho, Hr, Hk;
             first [discriminate Hk |
                    injection Ht as Ht; injection Hh as Hh; injection Ho as Ho; injection Hr as Hr;
                    subst; tauto] |]).
      destruct j; cbn in Hx; discriminate Hx.
    Qed.

    (** Every invocation has a response. *)
    Lemma sb_complete : PrefixView.complete sb_trace.
    Proof.
      intros i k op Hi.
      destruct (sb_inv_cases i k op Hi) as [(-> & -> & ->) | [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]]].
      - exists 6, 0. eexists. split; reflexivity.
      - exists 4, 0. eexists. split; reflexivity.
      - exists 7, 0. eexists. split; reflexivity.
      - exists 5, 0. eexists. split; reflexivity.
    Qed.

    (** *** Legality: a counter never decreases *)

    Abbreviation OpF := (RelaxedTraceLin.Op F).

    Lemma δcxy_mono s (o : COp) (r : nat) s' c : δcxy s o r s' -> get s c <= get s' c.
    Proof.
      destruct o as [c' | c']; cbn; intros [_ ->]; [| lia].
      destruct c', c; cbn; lia.
    Qed.

    (** A [Get c] in a legal run returns at least the initial value of
        [c]. *)
    Lemma seq_get_ge s (W : list OpF) s' j (oj : OpF) c :
      @RelaxedHoareSpec.seq_run F MSt δcxy s W s' -> nth_error W j = Some oj ->
      RelaxedTraceLin.op_op oj = Get c -> get s c <= RelaxedTraceLin.op_ret oj.
    Proof.
      intros Hrun. revert j. induction Hrun as [s | s o s1 W s2 Hd Hrun IH]; intros j Hj Hop;
        [destruct j; discriminate Hj |].
      destruct j as [| j]; cbn in Hj.
      - injection Hj as ->. destruct oj as [k op r]. cbn in Hop, Hd |- *. subst op. cbn in Hd.
        destruct Hd as [-> _]. lia.
      - pose proof (δcxy_mono _ _ _ _ c Hd). pose proof (IH j Hj Hop). lia.
    Qed.

    (** A [Get c] after an [Inc c] in a legal run returns more than the
        initial value of [c]. *)
    Lemma seq_inc_get s (W : list OpF) s' i j (oi oj : OpF) c :
      @RelaxedHoareSpec.seq_run F MSt δcxy s W s' ->
      nth_error W i = Some oi -> RelaxedTraceLin.op_op oi = Inc c ->
      nth_error W j = Some oj -> RelaxedTraceLin.op_op oj = Get c -> i < j ->
      get s c < RelaxedTraceLin.op_ret oj.
    Proof.
      intros Hrun. revert i j. induction Hrun as [s | s o s1 W s2 Hd Hrun IH]; intros i j Hi Hopi Hj Hopj Hlt;
        [destruct i; discriminate Hi |].
      destruct j as [| j]; [lia |]. cbn in Hj.
      destruct i as [| i]; cbn in Hi.
      - injection Hi as ->. destruct oi as [k op r]. cbn in Hopi, Hd. subst op. cbn in Hd.
        destruct Hd as [_ ->]. pose proof (seq_get_ge _ _ _ j oj c Hrun Hj Hopj) as Hge.
        destruct c; cbn in Hge |- *; lia.
      - pose proof (δcxy_mono _ _ _ _ c Hd). pose proof (IH i j Hi Hopi Hj Hopj ltac:(lia)). lia.
    Qed.

    Lemma before_idx (W : list OpF) a b i j :
      NoDup W -> RelaxedTraceLin.before W a b -> nth_error W i = Some a -> nth_error W j = Some b -> i < j.
    Proof.
      intros Hnd (l1 & l2 & -> & Hb) Hi Hj.
      pose proof (proj1 (NoDup_nth_error _) Hnd) as Hinj.
      assert (Ha : nth_error (l1 ++ a :: l2) (length l1) = Some a)
        by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
      assert (Hil : i = length l1).
      { apply Hinj; [apply nth_error_Some; rewrite Hi; discriminate | rewrite Hi, Ha; reflexivity]. }
      destruct (In_nth_error _ _ Hb) as (j' & Hj').
      assert (Hb' : nth_error (l1 ++ a :: l2) (length l1 + S j') = Some b).
      { rewrite nth_error_app2 by lia. replace (length l1 + S j' - length l1) with (S j') by lia. exact Hj'. }
      assert (Hjl : j = length l1 + S j').
      { apply Hinj; [apply nth_error_Some; rewrite Hj; discriminate | rewrite Hj, Hb'; reflexivity]. }
      lia.
    Qed.

    (** The operations of a witness, from the trace. *)
    Lemma sb_witness_op (W : list OpF) (o : OpF) k op :
      (forall o, In o W -> RelaxedTraceLin.occurs sel sb_trace o) -> In o W ->
      RelaxedTraceLin.op_key o = k -> (exists i, RelaxedTraceLin.inv_at sel sb_trace i k op) ->
      RelaxedTraceLin.op_op o = op.
    Proof.
      intros Hocc Ho Hk (i & Hi). destruct (Hocc o Ho) as [(i' & Hi') _]. rewrite Hk in Hi'.
      destruct (sb_inv_cases _ _ _ Hi) as [(-> & -> & ->) | [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]]];
      destruct (sb_inv_cases _ _ _ Hi') as [(_ & Hk' & ->) | [(_ & Hk' & ->) | [(_ & Hk' & ->) | (_ & Hk' & ->)]]];
      solve [reflexivity | discriminate Hk'].
    Qed.

    Lemma sb_witness_ret (W : list OpF) (o : OpF) :
      (forall o, In o W -> RelaxedTraceLin.occurs sel sb_trace o) -> In o W ->
      RelaxedTraceLin.op_ret o = 0.
    Proof.
      intros Hocc Ho. destruct (Hocc o Ho) as [_ (j & Hj)].
      destruct (sb_res_cases _ _ _ _ Hj) as [(_ & _ & _ & Hr) | [(_ & _ & _ & Hr) | [(_ & _ & _ & Hr) | (_ & _ & _ & Hr)]]];
        exact Hr.
    Qed.

    Lemma inv_at_sb i k op : nth_error sb_trace i = Some (Build_ThreadEvent (fst k) (@InvEv F (snd k) op)) ->
      RelaxedTraceLin.inv_at sel sb_trace i k op.
    Proof. intros H. eexists. split; [exact H | reflexivity]. Qed.

    (** M-19 item 5, the negative half: under the empty relation the SB
        trace is not relaxed-linearizable.  Not a pure rhb cycle (review
        wording correction): only [inc_x → get_y] and [inc_y → get_x]
        are rhb edges; [get_y] before [inc_y] and [get_x] before [inc_x]
        come from legality, because each [get] returns 0 ([seq_inc_get]). *)
    Theorem sb_not_rel_lin0 :
      ~ RelaxedTraceLin.rel_lin sel sb_trace (fun _ _ => False) (@RelaxedHoareSpec.seq_legal F MSt δcxy s00).
    Proof.
      intros (W & (s & Hrun) & Hnd & Hocc & Hall & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      assert (I0 : RelaxedTraceLin.inv_at sel sb_trace 0 (t1, 0) (Inc CX)) by (apply inv_at_sb; reflexivity).
      assert (I1 : RelaxedTraceLin.inv_at sel sb_trace 1 (t1, 1) (Get CY)) by (apply inv_at_sb; reflexivity).
      assert (I2 : RelaxedTraceLin.inv_at sel sb_trace 2 (t2, 0) (Inc CY)) by (apply inv_at_sb; reflexivity).
      assert (I3 : RelaxedTraceLin.inv_at sel sb_trace 3 (t2, 1) (Get CX)) by (apply inv_at_sb; reflexivity).
      destruct (Hall _ _ _ I0) as (o1 & Ho1 & Hk1).
      destruct (Hall _ _ _ I1) as (o2 & Ho2 & Hk2).
      destruct (Hall _ _ _ I2) as (o3 & Ho3 & Hk3).
      destruct (Hall _ _ _ I3) as (o4 & Ho4 & Hk4).
      pose proof (sb_witness_op W o1 _ _ Hocc Ho1 Hk1 (ex_intro _ 0 I0)) as Hop1.
      pose proof (sb_witness_op W o2 _ _ Hocc Ho2 Hk2 (ex_intro _ 1 I1)) as Hop2.
      pose proof (sb_witness_op W o3 _ _ Hocc Ho3 Hk3 (ex_intro _ 2 I2)) as Hop3.
      pose proof (sb_witness_op W o4 _ _ Hocc Ho4 Hk4 (ex_intro _ 3 I3)) as Hop4.
      pose proof (sb_witness_ret W o2 Hocc Ho2) as Hr2.
      pose proof (sb_witness_ret W o4 Hocc Ho4) as Hr4.
      (* the two program-order edges of rhb under the empty relation *)
      assert (Hb12 : RelaxedTraceLin.before W o1 o2).
      { apply Hord; [exact Ho1 | exact Ho2 |]. right. split; [rewrite Hk1, Hk2; reflexivity |].
        exists 0, 1. rewrite Hk1, Hk2, Hop1, Hop2. split; [exact I0 |]. split; [exact I1 |]. split; [lia | intros []]. }
      assert (Hb34 : RelaxedTraceLin.before W o3 o4).
      { apply Hord; [exact Ho3 | exact Ho4 |]. right. split; [rewrite Hk3, Hk4; reflexivity |].
        exists 2, 3. rewrite Hk3, Hk4, Hop3, Hop4. split; [exact I2 |]. split; [exact I3 |]. split; [lia | intros []]. }
      destruct (In_nth_error _ _ Ho1) as (i1 & Hi1).
      destruct (In_nth_error _ _ Ho2) as (i2 & Hi2).
      destruct (In_nth_error _ _ Ho3) as (i3 & Hi3).
      destruct (In_nth_error _ _ Ho4) as (i4 & Hi4).
      pose proof (before_idx W _ _ _ _ HndW Hb12 Hi1 Hi2) as H12.
      pose proof (before_idx W _ _ _ _ HndW Hb34 Hi3 Hi4) as H34.
      (* legality: get_y reads 0, so inc_y is not before it; likewise for x *)
      assert (H23 : i2 < i3).
      { destruct (Nat.lt_trichotomy i2 i3) as [H | [H | H]]; [exact H | exfalso | exfalso].
        - subst i3. rewrite Hi2 in Hi3. injection Hi3 as <-. rewrite Hop2 in Hop3. discriminate Hop3.
        - pose proof (seq_inc_get _ _ _ _ _ _ _ CY Hrun Hi3 Hop3 Hi2 Hop2 H) as Hlt.
          rewrite Hr2 in Hlt. cbn in Hlt. lia. }
      assert (H41 : i4 < i1).
      { destruct (Nat.lt_trichotomy i4 i1) as [H | [H | H]]; [exact H | exfalso | exfalso].
        - subst i1. rewrite Hi4 in Hi1. injection Hi1 as <-. rewrite Hop4 in Hop1. discriminate Hop1.
        - pose proof (seq_inc_get _ _ _ _ _ _ _ CX Hrun Hi1 Hop1 Hi4 Hop4 H) as Hlt.
          rewrite Hr4 in Hlt. cbn in Hlt. lia. }
      lia.
    Qed.
  End SB.

  (** *** The SB execution under semi-independence by counter *)

  (** M-19 item 5, the positive half, through the instance: the SB trace
      of Counter_xy is relaxed-linearizable under [by_counter]
      ([cxy_rel_lin]: [cxy_rlhl2], [rlhl_complin_eihl], [cc_rel_lin];
      [classic], [eq_rect_eq]). *)
  Corollary sb_rel_lin :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (sb_trace by_counter) by_counter
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
  Proof. exact (cxy_rel_lin _ (sb_mtraces by_counter) (sb_complete by_counter)). Qed.

  (** The same, directly and without axioms: the witness
      [get_y 0; get_x 0; inc_x 0; inc_y 0] is legal, and under
      [by_counter] the trace has no [rhb] edge (all invocations precede
      all responses, and the two same-thread pairs act on different
      counters). *)
  Definition sb_W : list (RelaxedTraceLin.Op FC) :=
    [@RelaxedTraceLin.Build_Op FC (t1, 1) (Get CY) 0; @RelaxedTraceLin.Build_Op FC (t2, 1) (Get CX) 0;
     @RelaxedTraceLin.Build_Op FC (t1, 0) (Inc CX) 0; @RelaxedTraceLin.Build_Op FC (t2, 0) (Inc CY) 0].

  Lemma sb_no_rhb (o o' : RelaxedTraceLin.Op FC) :
    ~ RelaxedTraceLin.rhb (@PrefixView.sel FC) (sb_trace by_counter) by_counter o o'.
  Proof.
    intros [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
    - destruct (sb_res_cases by_counter _ _ _ _ Hi) as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]];
      destruct (sb_inv_cases by_counter _ _ _ Hj) as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]]; lia.
    - apply Hn.
      destruct (sb_inv_cases by_counter _ _ _ Hi) as [(-> & Hk & ->) | [(-> & Hk & ->) | [(-> & Hk & ->) | (-> & Hk & ->)]]];
      destruct (sb_inv_cases by_counter _ _ _ Hj) as [(-> & Hk' & ->) | [(-> & Hk' & ->) | [(-> & Hk' & ->) | (-> & Hk' & ->)]]];
      try lia; rewrite Hk, Hk' in Ht; try discriminate Ht; intros Heq; discriminate Heq.
  Qed.

  Theorem sb_rel_lin_direct :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (sb_trace by_counter) by_counter
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
  Proof.
    exists sb_W. split; [| split; [| split; [| split]]].
    - exists (1, 1). repeat (econstructor; [split; reflexivity |]). constructor.
    - cbn. repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    - intros o Ho. cbn in Ho. split.
      + repeat (destruct Ho as [<- | Ho];
          [solve [exists 0; eexists; split; reflexivity | exists 1; eexists; split; reflexivity
                 | exists 2; eexists; split; reflexivity | exists 3; eexists; split; reflexivity] |]).
        destruct Ho.
      + repeat (destruct Ho as [<- | Ho];
          [solve [exists 4; eexists; split; reflexivity | exists 5; eexists; split; reflexivity
                 | exists 6; eexists; split; reflexivity | exists 7; eexists; split; reflexivity] |]).
        destruct Ho.
    - intros i k op Hi.
      destruct (sb_inv_cases by_counter _ _ _ Hi) as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]].
      + eexists. split; [right; right; left; reflexivity | reflexivity].
      + eexists. split; [left; reflexivity | reflexivity].
      + eexists. split; [right; right; right; left; reflexivity | reflexivity].
      + eexists. split; [right; left; reflexivity | reflexivity].
    - intros o o' _ _ Hr. exfalso. exact (sb_no_rhb o o' Hr).
  Qed.

  (** ** The universal negative under SI = ∅ (M-19 item 6) *)

  Definition cxy0_v0 : State (@RelaxedHoareSpec.EI F0 MSt δcxy) := (s00, []).

  (** With the empty overlay relation, no invariant, rely and guarantee
      verify the same module bodies over the same underlay: through
      [rlhl_complin_eihl] and [cc_rel_lin], [RLHL2Hyps] would make the SB
      trace of [sb_exec] relaxed-linearizable under ∅, which
      [sb_not_rel_lin0] refutes.  [classic] and [eq_rect_eq] enter
      through [rlhl_complin_eihl] and [cc_rel_lin]. *)
  Theorem cxy0_no_rlhl2 :
    forall (I : Assn (EIhl δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy))
           (R G : CallKey F0 -> PRel (EIhl δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy)),
      ~ RLHL2Hyps I R G M_cxy0 cxy_σ0 cxy0_v0.
  Proof.
    intros I R G HH.
    pose proof (rlhl_complin_eihl δmem (F := F0) δcxy s00 I R G M_cxy0 (s00, []) HH) as Hcc.
    pose proof (Hcc _ (sb_mtraces (fun _ _ => False))) as Hrt.
    exact (sb_not_rel_lin0 _ (cc_rel_lin (F := F0) δcxy s00 _ Hrt (sb_complete _))).
  Qed.

  (** The pairing (in the style of
      [RelaxedHoareChecks.ReadPairUniversal.pair_discriminates_rlhl2]):
      the same module bodies over the same underlay are verified under
      semi-independence by counter, and under the empty relation no
      [I], [R], [G] verify them. *)
  Corollary cxy_discriminates_rlhl2 :
    RLHL2Hyps Icxy Rcxy Gcxy M_cxy cxy_σ0 cxy_v0 /\
    forall (I : Assn (EIhl δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy))
           (R G : CallKey F0 -> PRel (EIhl δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy)),
      ~ RLHL2Hyps I R G M_cxy0 cxy_σ0 cxy0_v0.
  Proof. exact (conj cxy_rlhl2 cxy0_no_rlhl2). Qed.

  (** At the level of traces: the same trace is relaxed-linearizable
      under [by_counter] and not under the empty relation. *)
  Corollary sb_si_decides :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (sb_trace by_counter) by_counter
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00) /\
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (sb_trace by_counter) (fun _ _ => False)
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
  Proof. exact (conj sb_rel_lin_direct (sb_not_rel_lin0 by_counter)). Qed.

  (** ** The SI = ∅ counter is an instance too (the review's "Stronger
      approach 1")

      The FAA→Inc counter of [RelaxedHoareChecks.CounterEIhl] and
      [CounterEIhlFrame] (module [Counter.Mc] over [EIhl uδ] into
      [CounterHL.CVFe], semi-independence ∅ on both signatures) is the
      renaming copy-cat for [ρ Inc := FAA]; [counter_ren_rlhl2] is a
      third [RLHL2Hyps] proof for it, from the generic theorem. *)

  Module CounterAsRename.
    Import RelaxedHoareChecks.Counter RelaxedHoareChecks.CounterHL.

    Definition ρc (o : Sig.op (RelaxedSig.effect OSig)) : Sig.op (RelaxedSig.effect USig) := FAA.

    Definition backc0 (o : Sig.op (RelaxedSig.effect OSig)) : Sig.ar (ρc o) -> Sig.ar o :=
      match o as o0 return Sig.ar (ρc o0) -> Sig.ar o0 with Inc => fun r => r end.

    Lemma c_δ : forall s o r s', RelaxedHoareChecks.CounterRelLin.uδ s (ρc o) r s' -> cδ s o (backc0 o r) s'.
    Proof. intros s [] r s' H. exact H. Qed.

    Lemma c_si : forall o1 o2, ~ ~ RelaxedSig.semi_independent USig (ρc o1) (ρc o2) ->
                               RelaxedSig.semi_independent OSig o1 o2.
    Proof. intros o1 o2 H. apply H. intros []. Qed.

    Lemma c_inj : forall u o (r1 r2 : Sig.ar (ρc o)),
        @RelaxedTraceLin.Build_Op USig u (ρc o) r1 = @RelaxedTraceLin.Build_Op USig u (ρc o) r2 ->
        backc0 o r1 = backc0 o r2.
    Proof. intros u [] r1 r2 H. exact (f_equal RelaxedHoareChecks.CounterEIhl.uval H). Qed.

    Lemma c_M : forall o t, Mc o t = @Future USig (Sig.ar o) (ρc o) (fun f => Wait f (fun r => Ret (backc0 o r))).
    Proof. intros [] t. reflexivity. Qed.

    Theorem counter_ren_rlhl2 :
      RLHL2Hyps (@Iren USig OSig nat nat RelaxedHoareChecks.CounterRelLin.uδ cδ (fun n => n) ρc (fun _ => true))
        (@Rren USig OSig nat nat RelaxedHoareChecks.CounterRelLin.uδ cδ)
        (@Gren USig OSig nat nat RelaxedHoareChecks.CounterRelLin.uδ cδ)
        Mc RelaxedHoareChecks.CounterEIhl.ehσ0 (0, []).
    Proof.
      exact (@ren_rlhl2 USig OSig nat nat RelaxedHoareChecks.CounterRelLin.uδ cδ (fun n => n) ρc (fun _ => true)
               backc0 c_δ c_si (fun _ => eq_refl) c_inj Mc c_M 0).
    Qed.
  End CounterAsRename.

  (** ** Item 7a: a two-future variant whose derivation discharges
      own-event interference premises by stability

      Every operation of Counter_xy also increments a private statistics
      location [z] that no overlay operation reads: the body issues the
      linearizing access [ρ o] and [Faa z], then waits for both (both
      futures are waited before [Ret]).  The two invocations are
      semi-independent by location, so neither (F2) nor a tag orders
      them: the call's own [Faa z] may be emitted before or after its
      linearizing access, and the derivation must show that each edge
      assertion survives the other own event.  Slots, in program order:
      0 = the linearizing invocation, 1 = [Faa z], 2 = the linearizing
      response, 3 = the [z] response; the dag is [0 → 2], [1 → 3]
      ([dprec4]).  The non-trivial own-event premises (not vacuous, not
      [Stable_true], not refuted by [before]) are discharged by:
      - [Gzz_keeps_KInv]: [ns_if_old_start] at slot 1 and at slot 3 (the
        start edge of the linearizing invocation survives the own [z]
        steps);
      - [Gzz_keeps_KLini]: [ns_if_new_in] at slot 2 and [ns_if_old_in] at
        slot 3 (the ownership of the linearizing record, the abstract
        record and the [ls_lini] phase survive the own [z] steps, by
        [eihl_mine_steps] and because the possibility does not move; that
        a [z] access keeps the coupling of the invariant is
        [zinv_update]);
      - [Gz_keeps_KZ]: [ns_if_new_in] at slot 3 (the ownership of the [z]
        record survives the own linearizing events);
      - [Gzz_keeps_KLinr]: [bw_if] of the final edge of slot 2.
      The guarantee of the [z] events is finer than the method-level
      one ([Gzz k]: memory moves by [EIhl] steps, the possibility does
      not), which is how the pairwise premises are discharged although
      [Gz k ⊄ Rz k] ([newslot_guar_in_rely] does not apply).

      The underlay [EZ] is the two-location memory plus [z] ([ZM o] for
      the operations of [EM], [ZFaa] for [Faa z]), with semi-independence
      by location; [δz] is the SC cell on [x, y, z].  The overlay is [FC]
      with [δcxy]; the abstraction forgets [z] ([π := fst]).  Results:
      [cxyz_rlhl2] (through [method_sound] and
      [RelaxedHoareInherit.ren_rlhl2_of_sem]; the linearization and
      response updates are [RelaxedHoareInherit.inv_update] and
      [res_update]), [cxyz_complin_ei], [cxyz_rel_lin]; [z_reorder_exec]
      is a module-derived execution in which the own [Faa z] of an
      [inc_x] call is emitted before its [Faa x]. *)

  Module CounterXYZ.

    Inductive ZOp : Type :=
    | ZM (o : MOp)
    | ZFaa.

    Definition z_ar (_ : ZOp) : Type := nat.

    Canonical Structure ZEff : Sig.t := {| Sig.op := ZOp; Sig.ar := z_ar |}.

    Definition zloc (o : ZOp) : option CLoc := match o with ZM o' => Some (mloc o') | ZFaa => None end.

    Definition EZ : RelaxedSig.t :=
      {|
        RelaxedSig.effect := ZEff;
        RelaxedSig.handle := nat;
        RelaxedSig.semi_independent := fun o1 o2 => zloc o1 <> zloc o2;
        RelaxedSig.mode := fun _ => Local;
      |}.

    Lemma EZ_wf : RelaxedSig.well_formed EZ.
    Proof. constructor; [intros o H; apply H; reflexivity | intros; exact Logic.I | intros; exact Logic.I]. Qed.

    (** The state: [x, y] and [z]. *)
    Definition ZSt : Type := (MSt * nat)%type.

    Definition δz : ZSt -> forall o : Sig.op (RelaxedSig.effect EZ), Sig.ar o -> ZSt -> Prop :=
      fun s o =>
        match o as o0 return Sig.ar o0 -> ZSt -> Prop with
        | ZM o' => fun r s' => δmem (fst s) o' r (fst s') /\ snd s' = snd s
        | ZFaa => fun r s' => r = snd s /\ s' = (fst s, S (snd s))
        end.

    Definition ρz (o : COp) : ZOp := ZM (ρ o).
    Definition lzz (o : ZOp) : bool := match o with ZM _ => true | ZFaa => false end.

    Definition Mz : RelaxedModuleImpl EZ FC :=
      fun o _ => @Future EZ (Sig.ar o) (ρz o) (fun f => @Future EZ (Sig.ar o) ZFaa (fun g =>
                   Wait f (fun r => Wait g (fun _ => Ret r)))).

    Definition z_σ0 : State (EIhl δz) := (((s00, 0), []), []).
    Definition z_v0 : State (@RelaxedHoareSpec.EI FC MSt δcxy) := (s00, []).

    Local Abbreviation VZ := (EIhl δz).
    Local Abbreviation VF := (@RelaxedHoareSpec.EI FC MSt δcxy).
    Local Abbreviation A := (Assn VZ VF).
    Local Abbreviation POk v pool := (@PossOk FC VF v pool).

    Definition backz (o : Sig.op (RelaxedSig.effect FC)) (r : Sig.ar (ρz o)) : Sig.ar o := r.

    Lemma z_δ : forall s o r s', δz s (ρz o) r s' -> δcxy (fst s) o (backz o r) (fst s').
    Proof. intros s o r s' [H _]. exact (cxy_δ _ _ _ _ H). Qed.

    Lemma z_si : forall o1 o2 : COp, ~ ~ (zloc (ρz o1) <> zloc (ρz o2)) -> by_counter o1 o2.
    Proof.
      intros o1 o2 Hnn Heq. apply Hnn. cbn. rewrite !mloc_ρ, Heq. intros H. apply H. reflexivity.
    Qed.

    Lemma z_lz : forall o, lzz (ρz o) = true.
    Proof. reflexivity. Qed.

    Lemma z_inj : forall u o (r1 r2 : Sig.ar (ρz o)),
        @RelaxedTraceLin.Build_Op EZ u (ρz o) r1 = @RelaxedTraceLin.Build_Op EZ u (ρz o) r2 -> backz o r1 = backz o r2.
    Proof. intros u o r1 r2 H. exact (f_equal (fun x : RelaxedTraceLin.Op EZ => (RelaxedTraceLin.op_ret x : nat)) H). Qed.

    Definition Iz : A := @Iren EZ FC ZSt MSt δz δcxy fst ρz lzz.
    Definition Rz : CallKey FC -> PRel VZ VF := @Rren EZ FC ZSt MSt δz δcxy.
    Definition Gz : CallKey FC -> PRel VZ VF := @Gren EZ FC ZSt MSt δz δcxy.

    (** The guarantee of the [z] events: memory moves by [EIhl δz]
        steps, the possibility does not. *)
    Definition Gzz (k : CallKey FC) : PRel VZ VF := fun s s' =>
      eihl_steps δz (ps_mem s) (ps_mem s') /\ ps_poss s' = ps_poss s /\
      exists v pool, ps_poss s = POk v pool.

    Lemma Gzz_in_Gz k s s' : Gzz k s s' -> Gz k s s'.
    Proof.
      intros (Hm & Hp & v & pool & Hv). split; [exact Hm |].
      exists v, pool, v, pool. split; [exact Hv |]. split; [rewrite Hp; exact Hv |]. auto.
    Qed.

    (** The call owns its [z] record. *)
    Definition KZ (k : CallKey FC) (hg : nat) : A := fun s =>
      exists c, eihl_mine δz (fst k, hg) (@RelaxedTraceLin.Build_Op EZ (fst k, hg) ZFaa c) (ps_mem s).

    Local Abbreviation KInvz := (@KInv EZ FC ZSt MSt δz δcxy).
    Local Abbreviation KLinrz := (@KLinr EZ FC ZSt MSt δz δcxy).
    Local Abbreviation KLiniz := (@KLini EZ FC ZSt MSt δz δcxy ρz backz).

    (** *** The own-event stability facts *)

    Lemma Gzz_keeps_KInv k k' o : Stable Iz (Gzz k') (KInvz k o).
    Proof. intros s s' (v & pool & Hp & Hl) (_ & Hp' & _) _. exists v, pool. rewrite Hp'. auto. Qed.

    Lemma Gzz_keeps_KLini k k' o hu : Stable Iz (Gzz k') (KLiniz k o hu).
    Proof.
      intros s s' (c & v & pool & Hp & Hm & HP & Hl) (Hs & Hp' & _) _.
      exists c, v, pool. rewrite Hp'. split; [exact Hp |]. split; [exact (eihl_mine_steps δz _ _ _ _ Hs Hm) |]. auto.
    Qed.

    Lemma Gzz_keeps_KLinr k k' o r : Stable Iz (Gzz k') (KLinrz k o r).
    Proof. intros s s' (v & pool & Hp & Hl) (_ & Hp' & _) _. exists v, pool. rewrite Hp'. auto. Qed.

    Lemma Gz_keeps_KZ k k' hg : Stable Iz (Gz k') (KZ k hg).
    Proof. intros s s' (c & Hm) (Hs & _) _. exists c. exact (eihl_mine_steps δz _ _ _ _ Hs Hm). Qed.

    Lemma Rz_keeps_KZ k hg : Stable Iz (Rz k) (KZ k hg).
    Proof. intros s s' (c & Hm) (Hs & _) _. exists c. exact (eihl_mine_steps δz _ _ _ _ Hs Hm). Qed.

    (** The finer guarantee [Gzz] of the [z] events is needed in this
        derivation (latest-review m-44): with the method-level guarantee
        [Gz k] at slot 1, the premise [ns_if_old_start] there would be
        [Stable Iz (Gz k) (KInvz k o)], which is false.  [Gz k] lets [k]
        itself move its own pool entry (here: drop it), so "[k] is at
        [ls_inv o]" is not stable under it.  Witness: a state with only
        [k]'s [ls_inv o] entry, and the step to the initial state (which
        satisfies [Iz], [ren_init]), with memory unchanged.  This is
        about the slot assignment of [z_derivation], not a claim that no
        other derivation exists. *)
    Lemma Gz_breaks_KInv k o : ~ Stable Iz (Gz k) (KInvz k o).
    Proof.
      intros Hst.
      pose (σ0 := (((s00, 0), []), []) : State VZ).
      pose (s := (σ0, @PossOk FC VF (s00, []) [make_lin_entry k (ls_inv o)], []) : PState VZ VF).
      pose (s' := (σ0, @PossOk FC VF (s00, []) [], []) : PState VZ VF).
      assert (HK : KInvz k o s) by (exists (s00, []), [make_lin_entry k (ls_inv o)]; split; [reflexivity | left; reflexivity]).
      assert (HG : Gz k s s').
      { split; [apply rt_refl |]. exists (s00, []), [make_lin_entry k (ls_inv o)], (s00, []), [].
        split; [reflexivity |]. split; [reflexivity |]. split.
        - intros k' ls Hne [Heq | []]. exfalso. apply Hne.
          apply (f_equal (@lin_key FC)) in Heq. rewrite !lin_key_make_lin_entry in Heq. symmetry. exact Heq.
        - intros x _ []. }
      assert (HI : Iz s') by exact (ren_init (F := FC) δz δcxy fst ρz lzz (s00, 0)).
      destruct (Hst s s' HK HG HI) as (v & pool & Hp & Hl). cbn in Hp. injection Hp as _ <-. exact Hl.
    Qed.

    (** *** The updates of the [z] events *)

    Lemma zinv_update t h hg (P : A) :
      EvUpdate Iz (Gzz (t, h)) (t, h) (Build_ThreadEvent t (@InvEv EZ hg ZFaa)) P (KZ (t, h) hg).
    Proof.
      intros σ p γ γ' _ (st & P0 & pool & Hp & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) Hge σ' Hstep.
      cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hge. destruct Hge as (g1 & g2 & -> & -> & _).
      pose proof (eihl_rec_used_step δz _ σ σ' Hstep Hru) as Hru'.
      destruct (eihl_mine_inv δz t hg ZFaa σ σ' Hstep Hru) as (r & st' & Hd & Hσ' & Hm).
      exists p. split; [apply rt_refl |]. split; [| split].
      - exists r. exact Hm.
      - exists st, P0, pool. cbn [ps_poss ps_mem ps_ghost fst snd]. split; [exact Hp |].
        split; [rewrite Hσ'; cbn in Hd; destruct Hd as [_ ->]; exact Hc |]. split; [exact Hwf |].
        split; [intros t'; rewrite (HJ t'); apply gkops_drop; reflexivity |].
        split; [apply Forall_app in HJwf as [H1 H2]; apply Forall_app; split; [exact H1 | exact (Forall_inv_tail H2)] |].
        split; [exact HPl |]. split; [exact HPnd | exact Hru'].
      - split; [apply rt_step; exists (Build_ThreadEvent t (@InvEv EZ hg ZFaa)); exact Hstep |].
        split; [reflexivity |]. exists (st, P0), pool. exact Hp.
    Qed.

    Lemma zres_update t h hg rz (P : A) :
      EvUpdate Iz (Gzz (t, h)) (t, h) (Build_ThreadEvent t (@ResEv EZ hg ZFaa rz)) P (fun _ => True).
    Proof.
      intros σ p γ γ' _ (st & P0 & pool & Hp & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) Hge σ' Hstep.
      cbn [ps_poss ps_mem ps_ghost fst snd] in *. cbn in Hge. subst γ'.
      pose proof (eihl_rec_used_step δz _ σ σ' Hstep Hru) as Hru'.
      assert (Hcnt : fst (fst σ') = fst (fst σ)).
      { destruct σ as [[n Pc] u], σ' as [[n' Pc'] u']. cbn in Hstep. destruct Hstep as ((P1 & P2 & _ & Hq') & _).
        injection Hq' as -> _. reflexivity. }
      exists p. split; [apply rt_refl |]. split; [exact Logic.I | split].
      - exists st, P0, pool. cbn [ps_poss ps_mem ps_ghost fst snd]. rewrite Hcnt. auto 10.
      - split; [apply rt_step; exists (Build_ThreadEvent t (@ResEv EZ hg ZFaa rz)); exact Hstep |].
        split; [reflexivity |]. exists (st, P0), pool. exact Hp.
    Qed.

    (** *** The derivation *)

    Section ZCall.
      Context (t : tid) (h : nat) (o : COp).
      Local Abbreviation k := (@pair tid (RelaxedSig.handle FC) t h).

      Definition Ωz (evs : list (ThreadEvent EZ)) : Prop :=
        exists hf hg, evs = [Build_ThreadEvent t (@InvEv EZ hf (ρz o)); Build_ThreadEvent t (@InvEv EZ hg ZFaa)].

      Local Abbreviation Pz := (PostInvoke Iz k o Ωz).

      Definition e0 (hf : nat) := inv_tev (E := EZ) (F := FC) k empty_store hf (ρz o).
      Definition e1 (hf hg : nat) := inv_tev (E := EZ) (F := FC) k (@add_pending EZ hf (ρz o) empty_store) hg ZFaa.
      Definition e2 (hf r : nat) := res_tev (E := EZ) (F := FC) k hf (ρz o) r.
      Definition e3 (hg rz : nat) := res_tev (E := EZ) (F := FC) k hg ZFaa rz.

      (** The own events' dependency dag: [0 → 2] and [1 → 3] (F1)
          only; [0] and [1] are semi-independent by location, so the two
          invocations are unordered. *)
      Lemma dprec4 hf hg r rz i j : hg <> hf -> dprec [e0 hf; e1 hf hg; e2 hf r; e3 hg rz] i j ->
        (i = 0 /\ j = 2) \/ (i = 1 /\ j = 3).
      Proof.
        intros Hne [i0 j0 a b Hlt Ha Hb Hm].
        destruct i0 as [| [| [| [| i0]]]]; cbn in Ha; [| | | | destruct i0; discriminate Ha];
          injection Ha as <-;
          (destruct j0 as [| [| [| [| j0]]]]; cbn in Hb; [| | | | destruct j0; discriminate Hb]);
          injection Hb as <-; try lia; unfold must_precede in Hm; cbn in Hm.
        (* the edges (0, 2) and (1, 3) are closed by [lia]; the other pairs are not edges *)
        - exfalso. apply Hm. discriminate.
        - exfalso. exact (Hne (eq_sym Hm)).
        - exfalso. exact (Hne Hm).
        - destruct Hm.
      Qed.

      Lemma before4 hf hg r rz i j : hg <> hf -> before [e0 hf; e1 hf hg; e2 hf r; e3 hg rz] i j ->
        i = j \/ (i = 0 /\ j = 2) \/ (i = 1 /\ j = 3).
      Proof.
        intros Hne Hb. induction Hb as [| y z Hyz Hb IH]; [left; reflexivity |].
        destruct (dprec4 hf hg r rz y z Hne Hyz) as [[-> ->] | [-> ->]];
          destruct IH as [-> | [[-> H] | [-> H]]]; try discriminate; auto.
      Qed.

      Lemma dprec_02 hf hg r L : dprec ([e0 hf; e1 hf hg; e2 hf r] ++ L) 0 2.
      Proof. econstructor; [lia | reflexivity | reflexivity |]. unfold must_precede. cbn. reflexivity. Qed.

      Lemma dprec_13 hf hg r rz : dprec [e0 hf; e1 hf hg; e2 hf r; e3 hg rz] 1 3.
      Proof. econstructor; [lia | reflexivity | reflexivity |]. unfold must_precede. cbn. reflexivity. Qed.

      Definition s0 (hf : nat) : Slot VZ VF :=
        mkSlot (e0 hf) (KInvz k o) (fun _ _ => True) (KLiniz k o hf) (Gz k).
      Definition s1 (hf hg : nat) : Slot VZ VF :=
        mkSlot (e1 hf hg) (fun _ => True) (fun _ _ => True) (KZ k hg) (Gzz k).
      Definition s2 (hf r : nat) : Slot VZ VF :=
        mkSlot (e2 hf r) (fun _ => True) (fun d => if Nat.eqb d 0 then KLiniz k o hf else fun _ => True)
          (KLinrz k o (backz o r)) (Gz k).
      Definition s3 (hg rz : nat) : Slot VZ VF :=
        mkSlot (e3 hg rz) (fun _ => True) (fun d => if Nat.eqb d 1 then KZ k hg else fun _ => True)
          (fun _ => True) (Gzz k).

      Lemma pinit_KInvz : Impl Iz Pz (KInvz k o).
      Proof.
        intros [[σ p] γ] _ (p0 & γ0 & evs & (st & P & pool0 & Hp0 & _) & Hinv & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in Hp0, Hinv. rewrite Hp0 in Hinv.
        destruct (pinv_inv_gen _ _ _ _ _ _ Hinv) as [-> _].
        exists (st, P), (make_lin_entry k (@ls_inv FC o) :: pool0). split; [reflexivity | left; reflexivity].
      Qed.

      Lemma z_derivation :
        RProvable Iz Rz Gz k Pz
          (fun a Γ H => Close Iz Rz Gz k Pz (KLinrz k o) a Γ H /\ Ωz (own_invs Γ)) [] empty_store (Mz o t).
      Proof.
        unfold Mz.
        (* slot 0: the linearizing invocation *)
        apply rp_future with (sl := s0); [intros; reflexivity | |].
        { intros hf _. constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar s0].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar s0].
            intros σ p γ γ' [HK _].
            exact (inv_update (F := FC) δz δcxy fst ρz lzz backz z_δ z_si z_lz t h o hf σ p γ γ' HK).
          - exact pinit_KInvz.
          - intros d sd _ Hd. destruct d; discriminate.
          - exact (KInv_stable (F := FC) δz δcxy fst ρz lzz k o).
          - intros d _. apply Stable_true.
          - intros g sg Hg. destruct g; discriminate.
          - intros d g sg _ Hg. destruct g; discriminate.
          - intros y sy Hy. destruct y; discriminate.
          - intros y sy d Hy. destruct y; discriminate. }
        intros hf _. cbv beta.
        (* slot 1: the own [Faa z], unordered with slot 0 *)
        apply rp_future with (sl := s1 hf); [intros; reflexivity | |].
        { intros hg Hfg. assert (Hne : hg <> hf) by (intros ->; apply Hfg; left; reflexivity).
          constructor; cbn [sl_ev sl_start sl_in sl_post sl_guar s1 s0].
          - apply Gzz_in_Gz.
          - intros σ p γ γ' Hpre. exact (zinv_update t h hg _ σ p γ γ' Hpre).
          - intros s _ _. exact Logic.I.
          - intros d sd _ _ s _ _. exact Logic.I.
          - apply Stable_true.
          - intros d _. apply Stable_true.
          - intros g sg _. apply Stable_true.
          - intros d g sg _ _ _. apply Stable_true.
          - (* ns_if_old_start: slot 0's start edge against the own [z] step *)
            intros y sy Hy Hnb. destruct y as [| y]; [| destruct y; discriminate Hy].
            cbn in Hy. injection Hy as <-. cbn [sl_start s0]. apply Gzz_keeps_KInv.
          - intros y sy d Hy _ Hd. exfalso. destruct y as [| y]; [| destruct y; discriminate Hy].
            apply dprec_lt in Hd. lia. }
        intros hg Hfg. assert (Hne : hg <> hf) by (intros ->; apply Hfg; left; reflexivity). cbv beta.
        (* slot 2: the response of the linearizing access *)
        apply rp_wait_pending with (sl := s2 hf); [right; left; reflexivity | intros; reflexivity | |].
        { intros r. constructor; cbn [evs map app length sl_ev sl_start sl_in sl_post sl_guar s2 s1 s0].
          - auto.
          - unfold pre_of. cbn [sl_ev sl_start sl_in sl_post sl_guar s2].
            intros σ p γ γ' [_ Hin]. refine (res_update (F := FC) δz δcxy fst ρz lzz backz z_inj t h o hf r σ p γ γ' _).
            apply (Hin 0). exact (dprec_02 hf hg r []).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [| d]]; cbn in Hd.
            + injection Hd as <-. cbn. intros s _ Hs. exact Hs.
            + intros s _ _. exact Logic.I.
            + destruct d; discriminate Hd.
          - apply Stable_true.
          - intros d _. destruct (Nat.eqb d 0); [exact (KLini_stable (F := FC) δz δcxy fst ρz lzz backz k o hf) | apply Stable_true].
          - intros g sg _. apply Stable_true.
          - (* ns_if_new_in: the in-edge 0 → 2 against the own [z] step *)
            intros d g sg Hd Hg Hnb.
            destruct (dprec4 hf hg r 0 d 2 Hne (proj2 (dprec_app_iff [e0 hf; e1 hf hg; e2 hf r] [e3 hg 0] d 2 ltac:(cbn; lia)) Hd))
              as [[-> _] | [_ H]]; [| discriminate H].
            cbn. destruct g as [| [| g]]; [exfalso; apply Hnb; apply before_refl | | destruct g; discriminate Hg].
            cbn in Hg. injection Hg as <-. cbn [sl_guar s1]. apply Gzz_keeps_KLini.
          - intros y sy Hy Hnb. destruct y as [| [| y]]; cbn in Hy.
            + exfalso. apply Hnb. apply before_dprec. exact (dprec_02 hf hg r []).
            + injection Hy as <-. apply Stable_true.
            + destruct y; discriminate Hy.
          - intros y sy d Hy Hnb Hd. exfalso. destruct y as [| [| y]].
            + apply dprec_lt in Hd. lia.
            + apply (dprec_app_iff [e0 hf; e1 hf hg] [e2 hf 0; e3 hg 0] d 1 ltac:(cbn; lia)) in Hd.
              destruct (dprec4 hf hg 0 0 d 1 Hne Hd) as [[_ H] | [_ H]]; discriminate H.
            + destruct y; discriminate Hy. }
        intros r H' Hres. cbv beta.
        (* slot 3: the response of the own [Faa z] *)
        assert (Hpg : pending_at hg ZFaa H').
        { apply (RelaxedHoareChecks.resolve_store_keep_pending hf (ρz o) r _ H' _ Hres); [left; reflexivity |].
          cbn. exact Hne. }
        apply rp_wait_pending with (sl := s3 hg); [exact Hpg | intros; reflexivity | |].
        { intros rz. constructor; cbn [evs map app length sl_ev sl_start sl_in sl_post sl_guar s3 s2 s1 s0].
          - apply Gzz_in_Gz.
          - intros σ p γ γ' Hpre. exact (zres_update t h hg rz _ σ p γ γ' Hpre).
          - intros s _ _. exact Logic.I.
          - intros d sd _ Hd. destruct d as [| [| [| d]]]; cbn in Hd.
            + intros s _ _. exact Logic.I.
            + injection Hd as <-. cbn. intros s _ Hs. exact Hs.
            + intros s _ _. exact Logic.I.
            + destruct d; discriminate Hd.
          - apply Stable_true.
          - intros d _. destruct (Nat.eqb d 1); [apply Rz_keeps_KZ | apply Stable_true].
          - intros g sg _. apply Stable_true.
          - (* ns_if_new_in: the in-edge 1 → 3 against the own linearizing events *)
            intros d g sg Hd Hg Hnb.
            destruct (dprec4 hf hg r rz d 3 Hne Hd) as [[_ H] | [-> _]]; [discriminate H |].
            cbn. destruct g as [| [| [| g]]]; cbn in Hg.
            + injection Hg as <-. cbn [sl_guar s0]. apply Gz_keeps_KZ.
            + exfalso. apply Hnb. apply before_refl.
            + injection Hg as <-. cbn [sl_guar s2]. apply Gz_keeps_KZ.
            + destruct g; discriminate Hg.
          - (* ns_if_old_start: slot 0's start edge against the own [z] response *)
            intros y sy Hy Hnb. destruct y as [| [| [| y]]]; cbn in Hy.
            + injection Hy as <-. cbn [sl_start s0]. apply Gzz_keeps_KInv.
            + exfalso. apply Hnb. apply before_dprec. exact (dprec_13 hf hg r rz).
            + injection Hy as <-. apply Stable_true.
            + destruct y; discriminate Hy.
          - (* ns_if_old_in: slot 2's in-edge 0 → 2 against the own [z] response *)
            intros y sy d Hy Hnb Hd. destruct y as [| [| [| y]]]; cbn in Hy.
            + exfalso. apply dprec_lt in Hd. lia.
            + exfalso. apply Hnb. apply before_dprec. exact (dprec_13 hf hg r rz).
            + injection Hy as <-. cbn [sl_in s2].
              destruct (dprec4 hf hg r 0 d 2 Hne (proj2 (dprec_app_iff [e0 hf; e1 hf hg; e2 hf r] [e3 hg 0] d 2 ltac:(cbn; lia)) Hd))
                as [[-> _] | [_ H]]; [| discriminate H].
              apply Gzz_keeps_KLini.
            + destruct y; discriminate Hy. }
        intros rz H'' Hres'. cbv beta. apply rp_ret. split.
        - apply close_done with
            (fin := fun d => match d with 2 => KLinrz k o (backz o r) | _ => fun _ => True end)
            (fin0 := fun _ => True).
          + exact (RelaxedHoareChecks.resolve_two hf (ρz o) r hg ZFaa rz H' H'' Hne Hres Hres').
          + constructor.
            * intros d sd Hd. destruct d as [| [| [| [| d]]]]; cbn in Hd;
                [intros s _ _; exact Logic.I | intros s _ _; exact Logic.I | | intros s _ _; exact Logic.I |
                 destruct d; discriminate Hd].
              injection Hd as <-. intros s _ Hs. exact Hs.
            * intros s _ _. exact Logic.I.
            * (* bw_if: the final edge of slot 2 against the own [z] events *)
              intros d g sg Hd Hg Hnb. destruct d as [| [| [| d]]]; [apply Stable_true | apply Stable_true | | apply Stable_true].
              destruct g as [| [| [| [| g]]]]; cbn in Hg.
              -- exfalso. apply Hnb. apply before_dprec. exact (dprec_02 hf hg r [e3 hg rz]).
              -- injection Hg as <-. apply Gzz_keeps_KLinr.
              -- exfalso. apply Hnb. apply before_refl.
              -- injection Hg as <-. apply Gzz_keeps_KLinr.
              -- destruct g; discriminate Hg.
            * intros g sg _. apply Stable_true.
            * intros [| [| [| d]]]; [apply Stable_true | apply Stable_true | exact (KLinr_stable (F := FC) δz δcxy fst ρz lzz k o (backz o r)) | apply Stable_true].
            * apply Stable_true.
            * intros s _ _ Hfin. exact (Hfin 2 _ eq_refl Logic.I).
        - exists hf, hg. reflexivity.
      Qed.

      Lemma z_PI : forall s, Pz s -> Iz s.
      Proof.
        intros [[σ p] γ] (p0 & γ0 & evs & (st & P & pool0 & Hp0 & Hc & Hwf & HJ & HJwf & HPl & HPnd & Hru) & Hinv & Hg & (hf & hg & ->) & _).
        cbn [ps_poss ps_mem ps_ghost fst snd] in *. subst γ. rewrite Hp0 in Hinv.
        destruct (pinv_inv_gen _ _ _ _ _ _ Hinv) as [-> Hfresh].
        exists st, P, (make_lin_entry k (@ls_inv FC o) :: pool0). split; [reflexivity |]. split; [exact Hc |].
        split; [eapply lin_insert_well_formed; [constructor; exact Hfresh | exact Hwf] |]. split.
        - intros t'. cbn [inv_kops ps_ghost snd]. rewrite HJ, gkops_app. f_equal.
          cbn [map]. rewrite gkops_cons. change [Build_ScheduledEvent k (Build_ThreadEvent t (@InvEv EZ hg ZFaa))]
            with ([] ++ Build_ScheduledEvent k (Build_ThreadEvent t (@InvEv EZ hg ZFaa)) :: []).
          rewrite gkops_drop by reflexivity. unfold ikop, gsel. cbn.
          destruct (Pos.eqb t t'); reflexivity.
        - split; [apply Forall_app; split; [exact HJwf |] |].
          + repeat constructor.
          + split; [intros x Hx; right; exact (HPl x Hx) |]. split; [exact HPnd | exact Hru].
      Qed.
    End ZCall.

    Theorem z_provable t o :
      MethodProvable Iz Rz Gz Mz t o (fun h => Ωz t o) (fun h => KLinrz (t, h) o).
    Proof.
      constructor.
      - intros h s Hs. exact (z_PI t h o s Hs).
      - intros h r s HQ HI Hno. exact (ren_ret (F := FC) δz δcxy fst ρz lzz t h o r s HQ HI Hno).
      - intros h. exact (z_derivation t h o).
    Qed.

    Theorem z_methodsem t o : MethodSem Iz Rz Gz Mz t o.
    Proof. eapply method_sound. exact (z_provable t o). Qed.

    (** Item 7a: every field of [RLHL2Hyps] for the two-future variant,
        through [method_sound]. *)
    Theorem cxyz_rlhl2 : RLHL2Hyps Iz Rz Gz Mz z_σ0 z_v0.
    Proof. exact (ren_rlhl2_of_sem (F := FC) δz δcxy fst ρz lzz Mz (s00, 0) z_methodsem). Qed.

    Theorem cxyz_complin_ei :
      RCompLin Mz (RelaxedHoareSpec.EI δz) ((s00, 0), []) (@RelaxedHoareSpec.EI FC MSt δcxy) (s00, []).
    Proof. exact (rlhl_complin_eihl δz (F := FC) δcxy s00 Iz Rz Gz Mz ((s00, 0), []) cxyz_rlhl2). Qed.

    Corollary cxyz_rel_lin s :
      MTraces (RelaxedHoareSpec.EI δz) Mz ((s00, 0), []) s -> PrefixView.complete s ->
      RelaxedTraceLin.rel_lin (@PrefixView.sel FC) s by_counter (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
    Proof. exact (complin_ei_rel_lin (F := FC) δcxy s00 Mz (RelaxedHoareSpec.EI δz) ((s00, 0), []) cxyz_complin_ei s). Qed.

    (** The reordering that the own-event premises cover happens: in this
        module-derived execution over [EI δz], the own [Faa z] of an
        [inc_x] call is emitted before its [Faa x], and the call
        returns. *)
    Definition zi0 : TaggedEvent EZ :=
      Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv EZ 0 (ZM (Faa CX)))) (resolved_in (@empty_store EZ)).
    Definition zi1 : TaggedEvent EZ :=
      Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv EZ 1 ZFaa))
        (resolved_in (@add_pending EZ 0 (ZM (Faa CX)) empty_store)).
    Definition zr0 : TaggedEvent EZ := Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv EZ 0 (ZM (Faa CX)) 0)) no_deps.
    Definition zr1 : TaggedEvent EZ := Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv EZ 1 ZFaa 0)) no_deps.

    Lemma z_produces : program_produces_tagged t1 (Mz (Inc CX) t1) [zi0; zi1; zr0; zr1] 0.
    Proof.
      eexists. split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future EZ nat t1 (ZM (Faa CX))). intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_future EZ nat t1 ZFaa). intros [H | []]. discriminate H. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending EZ nat t1 (ZM (Faa CX)) 0 0). apply resolve_next; [discriminate |]. apply resolve_here. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending EZ nat t1 ZFaa 1 0). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. repeat constructor.
    Qed.

    Definition z_evs : list (ModuleEvent EZ FC) :=
      [OverlayEvent (Build_ThreadEvent t1 (@InvEv FC 0 (Inc CX)));
       UnderlayEvent (untag zi1); UnderlayEvent (untag zi0);
       UnderlayEvent (untag zr0); UnderlayEvent (untag zr1);
       OverlayEvent (Build_ThreadEvent t1 (@ResEv FC 0 (Inc CX) 0))].

    Theorem z_reorder_exec :
      exists c, module_execution_tagged (RelaxedHoareSpec.EI δz) Mz
                  (initial_tagged_module (RelaxedHoareSpec.EI δz) ((s00, 0), [])) z_evs c /\
        (forall e, In e (tm_calls c) -> ce_cell FC e = DeadCall).
    Proof.
      set (V := @RelaxedHoareSpec.EI EZ ZSt δz).
      eexists. split.
      - unfold z_evs.
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V Mz t1 0 (Inc CX) ((s00, 0), []) [] [] [] [zi0; zi1; zr0; zr1] 0).
          - intros [].
          - exact z_produces.
          - split; [| intros key _ []]. cbn. constructor; [| constructor; [intros [] | constructor]].
            intros [H | []]. discriminate H. }
        (* the own [Faa z] overtakes the call's pending [Faa x] *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mz (@Build_TaggedScheduledEvent EZ FC (t1, 0) zi1)).
          - cbn. apply tagged_select_next; [| apply tagged_select_here].
            right. split; [reflexivity |]. unfold must_precede. cbn. intros H. apply H. discriminate.
          - cbn. exists 0, ((0, 0), 1). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mz (@Build_TaggedScheduledEvent EZ FC (t1, 0) zi0)).
          - cbn. apply tagged_select_here.
          - cbn. exists 0, ((1, 0), 1). split; [split; [split; reflexivity | reflexivity] | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mz (@Build_TaggedScheduledEvent EZ FC (t1, 0) zr0)).
          - cbn. apply tagged_select_here.
          - cbn. eexists [], _. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V Mz (@Build_TaggedScheduledEvent EZ FC (t1, 0) zr1)).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return; [apply finish_here | intros []]. }
        apply tagged_module_execution_refl.
      - intros e [<- | []]. reflexivity.
    Qed.
  End CounterXYZ.


  (** ** The semi-independence table (latest-review m-46)

      The same bodies ([Inc c ↦ call (Faa c)], [Get c ↦ call (Rd c)])
      over the same SC cell [δmem], for several pairs (SI_E, SI_F) of
      underlay and overlay relations.  [EMsi siE] is [EM] with the
      relation [siE] ([EMsi by_location] is [EM], [EMsi_loc]); [Mgen siE
      si] is the module ([Mgen by_location si] is [Mcxy si], [Mgen_loc]).
      Choice (b) of M-19 item 3: [si_mb] ([Faa l] may be passed by a
      later [Rd l'], [l ≠ l']) and [si_cb] ([Inc c] by a later [Get c'],
      [c ≠ c']); both are asymmetric, which [RelaxedSig.well_formed]
      allows (it asks irreflexivity and mode compatibility only;
      [EMb_wf], [FCb_wf]).

      Positive cells ([RLHL2Hyps] instances, each from
      [RelaxedHoareInherit.ren_rlhl2], closed):
      - (∅, ∅): [cxy00_rlhl2] ([E00 := EMsi ∅], overlay [F0]);
      - (a) = (by_location, by_counter): [cxy_rlhl2] (above);
      - (b) = (si_mb, si_cb): [cxyb_rlhl2], with [cxyb_complin_ei] and
        [cxyb_rel_lin] (every complete trace of [Mb] over [EI δmem] is
        relaxed-linearizable under [si_cb]).
      Negative cells (∀ [I] [R] [G], [~ RLHL2Hyps]):
      - (by_location, ∅): [cxy0_no_rlhl2] (above, through the SB trace);
      - (by_location, si_cb), "mixed": [cxy_mixed_no_rlhl2], through the
        LB trace below.
      [cxy_si_table] collects the five cells.

      Witnesses.
      - SB, generic in the underlay relation: [sb_exec_gen siE si] is a
        complete execution of [Mgen siE si] over [EI δmem] for every
        [siE] containing the two crossing pairs [(Faa x, Rd y)] and
        [(Faa y, Rd x)] (each [Rd] passes its own thread's pending
        [Faa]); [sb_exec_gen_loc] is [sb_exec]'s statement as its
        instance.  [sb_rel_lin_gen]: the SB trace is relaxed-linearizable
        under every overlay relation containing [(Inc x, Get y)] and
        [(Inc y, Get x)]; so it is accepted under (a) ([sb_rel_lin]) and
        (b) ([sb_rel_lin_cb], closed; [sb_rel_lin_b], through
        [cxyb_rel_lin] and the execution [sb_mtraces_b] of [Mb]).
      - LB: [lb_exec si] is a complete execution of [Mcxy si] (underlay
        [EM], by location) over [EI δmem]: [t1] invokes [get_x], then
        [inc_y] while [get_x] is pending, and [t1]'s [Faa y] is emitted
        before its own pending [Rd x]; [t2] symmetrically ([get_y], then
        [inc_x]); both [inc]s return 0, both [get]s return 1.
        [lb_rel_lin_direct] (closed) and [lb_rel_lin] (through
        [cxy_rel_lin]): accepted under (a).  [lb_not_rel_lin_gen]: not
        relaxed-linearizable under any overlay relation that lacks
        [(Get x, Inc y)] and [(Get y, Inc x)]; in particular not under
        [si_cb] ([lb_not_rel_lin_cb]) nor under ∅ ([lb_not_rel_lin0]).
        The argument goes through [seq_legal], not an rhb cycle alone:
        [get_x → inc_y] and [get_y → inc_x] are rhb edges (same thread,
        not semi-independent), and [get_x] returning 1 needs [inc_x]
        before it, [get_y] returning 1 needs [inc_y] before it
        ([seq_get_gt_inc]), which closes the cycle.  [lb_si_decides]
        collects the three facts on one trace.
      - [lb_not_trace_b]: the LB trace is not a trace of the choice-(b)
        module [Mb] over [EI δmem], by [cxyb_rel_lin]; RLHL proves a
        negative fact about the executions of [Mb].

      Resulting table (✓ = an [RLHL2Hyps] instance; ✗ = no [I], [R],
      [G] at all; the blank cells are filled in the final section,
      m-49):

      | SI_E \ SI_F    | ∅   | si_cb (b) | by_counter (a) |
      |----------------|-----|-----------|----------------|
      | ∅              | ✓   |           |                |
      | si_mb (b)      |     | ✓         |                |
      | by_location    | ✗   | ✗ (mixed) | ✓              |

      SB is a trace of the (a) and (b) modules and is accepted under (a)
      and (b), rejected under ∅; LB is a trace of the by-location module
      and not of the (b) module ([lb_not_trace_b]), and is accepted only
      under (a).  With the bodies and the cell fixed, the overlay
      relation alone decides acceptance of each trace, and, for the
      by-location module, RLHL provability ((a) versus mixed).

      The mixed cell.  The RLHL-3b iteration-1 review (Redesign
      assessment, citing m-36) remarked that a by-location underlay with
      an overlay relation narrower than the inherited one may need
      prophecy (possibility sets) in RLHL.  For
      (by_location, si_cb) the obstacle is not the proof method:
      [cxy_mixed_no_rlhl2] is a universal negative because the module
      really has a trace (LB) that is not relaxed-linearizable under
      [si_cb], and [RLHL2Hyps] implies relaxed linearizability of every
      complete trace ([rlhl_complin_eihl], [cc_rel_lin]).  No extension
      of the logic (prophecy included) can verify this module against
      [si_cb], since that would contradict soundness.  The prophecy
      question of m-36 remains open for specifications that are narrower
      than the inherited relation but still satisfied by every trace.

      Scope: the same as the rest of this file (SC cell; modes compiled
      into [si_mb], the mode field is [Local] and unused; [Inc] returns
      the old value; complete traces for [rel_lin]).  The nonempty
      underlay relations are COH-style ([by_location], trace.tex:205) or I_RC
      (trace.tex:393) restricted to [faa(·, rel)] and [rd(·, acq)]
      ([si_mb]); I_RC prints no RMW row (trace.tex:388-396), so treating
      [faa] as a write (or as a componentwise RMW) is an interpretation
      (m-48; which relation is I_Counter_xy stays m-40). *)

  Definition EMsi (siE : MOp -> MOp -> Prop) : RelaxedSig.t :=
    {|
      RelaxedSig.effect := MEff;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := siE;
      RelaxedSig.mode := fun _ => Local;
    |}.

  Definition Mgen (siE : MOp -> MOp -> Prop) (si : COp -> COp -> Prop) : RelaxedModuleImpl (EMsi siE) (CxySig si) :=
    fun o _ => @Future (EMsi siE) (Sig.ar o) (ρ o) (fun f => Wait f (fun r => Ret r)).

  Lemma EMsi_loc : EMsi by_location = EM.
  Proof. reflexivity. Qed.

  Lemma Mgen_loc si : Mgen by_location si = Mcxy si.
  Proof. reflexivity. Qed.

  (** *** Choice (b) *)

  (** [Faa l] may be passed by a later [Rd l'] on a different location
      (a write may be delayed past a later read, as in the
      [(wrt, rd)] row of I_RC, trace.tex:393). *)
  Definition si_mb (o1 o2 : MOp) : Prop :=
    match o1, o2 with Faa l, Rd l2 => l <> l2 | _, _ => False end.

  (** [Inc c] may be passed by a later [Get c'] on a different counter
      (2Counter.tex:41: when [get_x] executes, only unfinished [inc_y]
      may be pending; :53: nothing passes into [inc_x]). *)
  Definition si_cb (o1 o2 : COp) : Prop :=
    match o1, o2 with Inc c, Get c2 => c <> c2 | _, _ => False end.

  Definition EMb : RelaxedSig.t := EMsi si_mb.
  Definition FCb : RelaxedSig.t := CxySig si_cb.
  Definition Mb : RelaxedModuleImpl EMb FCb := Mgen si_mb si_cb.

  Lemma EMb_wf : RelaxedSig.well_formed EMb.
  Proof. constructor; [intros [l | l] H; exact H | intros; exact Logic.I | intros; exact Logic.I]. Qed.

  Lemma FCb_wf : RelaxedSig.well_formed FCb.
  Proof. constructor; [intros [c | c] H; exact H | intros; exact Logic.I | intros; exact Logic.I]. Qed.

  (** Inheritance, constructively (both relations are negations on the
      pairs where they are not [False]). *)
  Lemma cxyb_si : forall o1 o2 : COp, ~ ~ si_mb (ρ o1) (ρ o2) -> si_cb o1 o2.
  Proof.
    intros [c1 | c1] [c2 | c2] H; cbn in *;
      first [intros Heq; apply H; intros Hne; exact (Hne Heq) | exfalso; apply H; intros []].
  Qed.

  Lemma cxyb_inj : forall u o (r1 r2 : Sig.ar (ρ o)),
      @RelaxedTraceLin.Build_Op EMb u (ρ o) r1 = @RelaxedTraceLin.Build_Op EMb u (ρ o) r2 -> backc o r1 = backc o r2.
  Proof. intros u o r1 r2 H. exact (f_equal (fun x : RelaxedTraceLin.Op EMb => (RelaxedTraceLin.op_ret x : nat)) H). Qed.

  Lemma cxyb_M : forall o t, Mb o t = @Future EMb (Sig.ar o) (ρ o) (fun f => Wait f (fun r => Ret (backc o r))).
  Proof. reflexivity. Qed.

  Definition cxyb_σ0 : State (EIhl (E := EMb) δmem) := ((s00, []), []).
  Definition cxyb_v0 : State (@RelaxedHoareSpec.EI FCb MSt δcxy) := (s00, []).

  Definition Icxyb : Assn (EIhl (E := EMb) δmem) (@RelaxedHoareSpec.EI FCb MSt δcxy) :=
    @Iren EMb FCb MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true).
  Definition Rcxyb : CallKey FCb -> PRel (EIhl (E := EMb) δmem) (@RelaxedHoareSpec.EI FCb MSt δcxy) :=
    @Rren EMb FCb MSt MSt δmem δcxy.
  Definition Gcxyb : CallKey FCb -> PRel (EIhl (E := EMb) δmem) (@RelaxedHoareSpec.EI FCb MSt δcxy) :=
    @Gren EMb FCb MSt MSt δmem δcxy.

  (** Choice (b): every field of [RLHL2Hyps] (the review's scratch
      instance, .rocq-review/scripts/RLHL3b1_m46_cxyb_rlhl2.v). *)
  Theorem cxyb_rlhl2 : RLHL2Hyps Icxyb Rcxyb Gcxyb Mb cxyb_σ0 cxyb_v0.
  Proof.
    exact (@ren_rlhl2 EMb FCb MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true) backc cxy_δ cxyb_si
             (fun _ => eq_refl) cxyb_inj Mb cxyb_M s00).
  Qed.

  (** Copy-cat inclusion over the plain [EI δmem] ([classic], through
      [rlhl_complin_eihl] and [RelaxedHoareCompLin.rinv_val]). *)
  Theorem cxyb_complin_ei :
    RCompLin Mb (@RelaxedHoareSpec.EI EMb MSt δmem) (s00, []) (@RelaxedHoareSpec.EI FCb MSt δcxy) (s00, []).
  Proof. exact (rlhl_complin_eihl (E := EMb) δmem (F := FCb) δcxy s00 Icxyb Rcxyb Gcxyb Mb (s00, []) cxyb_rlhl2). Qed.

  (** Every complete trace of the choice-(b) module over [EI δmem] is
      relaxed-linearizable under [si_cb] ([classic], [eq_rect_eq]). *)
  Corollary cxyb_rel_lin s :
    MTraces (@RelaxedHoareSpec.EI EMb MSt δmem) Mb (s00, []) s -> PrefixView.complete s ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel FCb) s si_cb (@RelaxedHoareSpec.seq_legal FCb MSt δcxy s00).
  Proof. exact (complin_ei_rel_lin (F := FCb) δcxy s00 Mb (@RelaxedHoareSpec.EI EMb MSt δmem) (s00, []) cxyb_complin_ei s). Qed.

  (** *** The (∅, ∅) cell *)

  Definition E00 : RelaxedSig.t := EMsi (fun _ _ => False).
  Definition M00 : RelaxedModuleImpl E00 F0 := Mgen (fun _ _ => False) (fun _ _ => False).

  Lemma E00_wf : RelaxedSig.well_formed E00.
  Proof. constructor; [intros o H; exact H | intros _ _ [] | intros _ _ []]. Qed.

  Lemma cxy00_inj : forall u o (r1 r2 : Sig.ar (ρ o)),
      @RelaxedTraceLin.Build_Op E00 u (ρ o) r1 = @RelaxedTraceLin.Build_Op E00 u (ρ o) r2 -> backc o r1 = backc o r2.
  Proof. intros u o r1 r2 H. exact (f_equal (fun x : RelaxedTraceLin.Op E00 => (RelaxedTraceLin.op_ret x : nat)) H). Qed.

  Definition cxy00_σ0 : State (EIhl (E := E00) δmem) := ((s00, []), []).

  Theorem cxy00_rlhl2 :
    RLHL2Hyps (@Iren E00 F0 MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true)) (@Rren E00 F0 MSt MSt δmem δcxy)
      (@Gren E00 F0 MSt MSt δmem δcxy) M00 cxy00_σ0 cxy0_v0.
  Proof.
    exact (@ren_rlhl2 E00 F0 MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true) backc cxy_δ
             (fun _ _ Hnn => Hnn (fun x => x)) (fun _ => eq_refl) cxy00_inj M00 (fun _ _ => eq_refl) s00).
  Qed.

  (** *** The SB execution, generic in the underlay relation *)

  (** [sb_exec] for every underlay relation [siE] that lets each [Rd]
      pass its own thread's pending [Faa] on the other location; the
      overlay relation [si] is arbitrary (the module semantics reads only
      the underlay relation). *)
  Section SBGen.
    Context (siE : MOp -> MOp -> Prop) (si : COp -> COp -> Prop).
    Context (Hx : siE (Faa CX) (Rd CY)) (Hy : siE (Faa CY) (Rd CX)).
    Local Abbreviation EG := (EMsi siE).
    Local Abbreviation F := (CxySig si).
    Local Abbreviation V := (@RelaxedHoareSpec.EI EG MSt δmem).

    Definition uig (t : tid) (hu : nat) (o : MOp) : TaggedEvent EG :=
      Build_TaggedEvent (Build_ThreadEvent t (@InvEv EG hu o)) (resolved_in (@empty_store EG)).
    Definition urg (t : tid) (hu : nat) (o : MOp) (r : nat) : TaggedEvent EG :=
      Build_TaggedEvent (Build_ThreadEvent t (@ResEv EG hu o r)) no_deps.

    Lemma call_produces_gen t (o : COp) (hu r : nat) :
      program_produces_tagged t (Mgen siE si o t) [uig t hu (ρ o); urg t hu (ρ o) r] r.
    Proof.
      exists (Build_ProgramConfig (Ret r) [@Build_FutureEntry EG hu (@Resolved EG (ρ o) r)]). split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future EG (Sig.ar o) t (ρ o) (fun f => Wait f (fun (x : nat) => Ret x)) hu (@empty_store EG)).
          intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending EG (Sig.ar o) t (ρ o) hu r (fun (x : nat) => Ret x)). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. constructor; [exact Logic.I | constructor].
    Qed.

    Lemma crossg_inv_inv t h1 o1 d1 h2 o2 d2 :
      siE o1 o2 ->
      tagged_can_cross (Build_TaggedEvent (Build_ThreadEvent t (@InvEv EG h1 o1)) d1)
                       (Build_TaggedEvent (Build_ThreadEvent t (@InvEv EG h2 o2)) d2).
    Proof. intros Hs. right. split; [reflexivity |]. unfold must_precede. cbn. intros H. exact (H Hs). Qed.

    Lemma crossg_res_inv t h1 o1 r1 h2 o2 : tagged_can_cross (urg t h1 o1 r1) (uig t h2 o2).
    Proof. right. split; [reflexivity |]. unfold must_precede. cbn. apply resolved_in_empty. Qed.

    Lemma crossg_inv_res t h1 o1 d h2 o2 r :
      h1 <> h2 -> tagged_can_cross (Build_TaggedEvent (Build_ThreadEvent t (@InvEv EG h1 o1)) d) (urg t h2 o2 r).
    Proof. intros Hne. right. split; [reflexivity |]. unfold must_precede. cbn. exact Hne. Qed.

    Lemma crossg_res_res t h1 o1 r1 h2 o2 r2 : tagged_can_cross (urg t h1 o1 r1) (urg t h2 o2 r2).
    Proof. right. split; [reflexivity |]. unfold must_precede. cbn. intros []. Qed.

    Lemma crossg_thread (a b : TaggedEvent EG) :
      te_tid EG (untag a) <> te_tid EG (untag b) -> tagged_can_cross a b.
    Proof. intros H. left. exact H. Qed.

    Definition sb_evs_gen : list (ModuleEvent EG F) :=
      [OverlayEvent (oi si t1 0 (Inc CX)); OverlayEvent (oi si t1 1 (Get CY));
       OverlayEvent (oi si t2 0 (Inc CY)); OverlayEvent (oi si t2 1 (Get CX));
       UnderlayEvent (untag (uig t1 1 (Rd CY))); UnderlayEvent (untag (urg t1 1 (Rd CY) 0));
       OverlayEvent (orr si t1 1 (Get CY) 0);
       UnderlayEvent (untag (uig t2 1 (Rd CX))); UnderlayEvent (untag (urg t2 1 (Rd CX) 0));
       OverlayEvent (orr si t2 1 (Get CX) 0);
       UnderlayEvent (untag (uig t1 0 (Faa CX))); UnderlayEvent (untag (urg t1 0 (Faa CX) 0));
       OverlayEvent (orr si t1 0 (Inc CX) 0);
       UnderlayEvent (untag (uig t2 0 (Faa CY))); UnderlayEvent (untag (urg t2 0 (Faa CY) 0));
       OverlayEvent (orr si t2 0 (Inc CY) 0)].

    Lemma sb_overlay_gen : RelaxedGSim.overlay_events sb_evs_gen = sb_trace si.
    Proof. reflexivity. Qed.

    Local Ltac nin := cbn; let H := fresh in intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.

    (** The execution of [sb_exec], from module steps, over [EI δmem]
        with the underlay relation [siE]; every call returns.  The only
        use of [siE] is the two crossings [Hx], [Hy]. *)
    Theorem sb_exec_gen :
      exists c, module_execution_tagged V (Mgen siE si) (initial_tagged_module V (s00, [])) sb_evs_gen c /\
        (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall).
    Proof.
      eexists. split.
      - unfold sb_evs_gen.
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mgen siE si) t1 0 (Inc CX) (s00, []) [] [] [] [uig t1 0 (Faa CX); urg t1 0 (Faa CX) 0] 0).
          - intros [].
          - apply call_produces_gen.
          - split; [repeat constructor; intros [] | intros key Hk []]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mgen siE si) t1 1 (Get CY) (s00, []) _ _ _ [uig t1 1 (Rd CY); urg t1 1 (Rd CY) 0] 0).
          - nin.
          - apply call_produces_gen.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mgen siE si) t2 0 (Inc CY) (s00, []) _ _ _ [uig t2 0 (Faa CY); urg t2 0 (Faa CY) 0] 0).
          - nin.
          - apply call_produces_gen.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mgen siE si) t2 1 (Get CX) (s00, []) _ _ _ [uig t2 1 (Rd CX); urg t2 1 (Rd CX) 0] 0).
          - nin.
          - apply call_produces_gen.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t1, 1) (uig t1 1 (Rd CY)))).
          - cbn. apply tagged_select_next; [apply crossg_inv_inv; exact Hx |].
            apply tagged_select_next; [apply crossg_res_inv |]. apply tagged_select_here.
          - cbn. exists 0, s00. split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t1, 1) (urg t1 1 (Rd CY) 0))).
          - cbn. apply tagged_select_next; [apply crossg_inv_res; discriminate |].
            apply tagged_select_next; [apply crossg_res_res |]. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t2, 1) (uig t2 1 (Rd CX)))).
          - cbn. apply tagged_select_next; [apply crossg_thread; discriminate |].
            apply tagged_select_next; [apply crossg_thread; discriminate |].
            apply tagged_select_next; [apply crossg_inv_inv; exact Hy |].
            apply tagged_select_next; [apply crossg_res_inv |]. apply tagged_select_here.
          - cbn. exists 0, s00. split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t2, 1) (urg t2 1 (Rd CX) 0))).
          - cbn. apply tagged_select_next; [apply crossg_thread; discriminate |].
            apply tagged_select_next; [apply crossg_thread; discriminate |].
            apply tagged_select_next; [apply crossg_inv_res; discriminate |].
            apply tagged_select_next; [apply crossg_res_res |]. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_here.
          - nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t1, 0) (uig t1 0 (Faa CX)))).
          - cbn. apply tagged_select_here.
          - cbn. exists 0, (1, 0). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t1, 0) (urg t1 0 (Faa CX) 0))).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t2, 0) (uig t2 0 (Faa CY)))).
          - cbn. apply tagged_select_here.
          - cbn. exists 0, (1, 1). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mgen siE si) (@Build_TaggedScheduledEvent EG F (t2, 0) (urg t2 0 (Faa CY) 0))).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        apply tagged_module_execution_refl.
      - intros e He. cbn in He. repeat (destruct He as [<- | He]; [reflexivity |]). destruct He.
    Qed.

    Corollary sb_mtraces_gen : MTraces V (Mgen siE si) (s00, []) (sb_trace si).
    Proof. destruct sb_exec_gen as (c & Hex & _). exists sb_evs_gen, c. split; [exact Hex | reflexivity]. Qed.
  End SBGen.

  (** [sb_exec]'s statement, as the instance [siE := by_location] of
      [sb_exec_gen] ([sb_exec] itself is unchanged). *)
  Lemma sb_exec_gen_loc si :
    exists c, module_execution_tagged (@RelaxedHoareSpec.EI EM MSt δmem) (Mcxy si)
                (initial_tagged_module (@RelaxedHoareSpec.EI EM MSt δmem) (s00, [])) (sb_evs si) c /\
      (forall e, In e (tm_calls c) -> ce_cell (CxySig si) e = DeadCall).
  Proof. exact (sb_exec_gen by_location si ltac:(discriminate) ltac:(discriminate)). Qed.

  (** *** SB under choice (b)

      The SB trace is relaxed-linearizable under every overlay relation
      that contains [(Inc x, Get y)] and [(Inc y, Get x)]: then it has
      no rhb edge, and [get_y 0; get_x 0; inc_x 0; inc_y 0] is a legal
      witness ([sb_rel_lin_direct] for [by_counter], generalised). *)
  Definition sb_Wg (si : COp -> COp -> Prop) : list (RelaxedTraceLin.Op (CxySig si)) :=
    [@RelaxedTraceLin.Build_Op (CxySig si) (t1, 1) (Get CY) 0; @RelaxedTraceLin.Build_Op (CxySig si) (t2, 1) (Get CX) 0;
     @RelaxedTraceLin.Build_Op (CxySig si) (t1, 0) (Inc CX) 0; @RelaxedTraceLin.Build_Op (CxySig si) (t2, 0) (Inc CY) 0].

  Lemma sb_no_rhb_gen si (indep : COp -> COp -> Prop) (o o' : RelaxedTraceLin.Op (CxySig si)) :
    indep (Inc CX) (Get CY) -> indep (Inc CY) (Get CX) ->
    ~ RelaxedTraceLin.rhb (@PrefixView.sel (CxySig si)) (sb_trace si) indep o o'.
  Proof.
    intros Hx Hy [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
    - destruct (sb_res_cases si _ _ _ _ Hi) as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]];
      destruct (sb_inv_cases si _ _ _ Hj) as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]]; lia.
    - apply Hn.
      destruct (sb_inv_cases si _ _ _ Hi) as [(-> & Hk & ->) | [(-> & Hk & ->) | [(-> & Hk & ->) | (-> & Hk & ->)]]];
      destruct (sb_inv_cases si _ _ _ Hj) as [(-> & Hk' & ->) | [(-> & Hk' & ->) | [(-> & Hk' & ->) | (-> & Hk' & ->)]]];
      try lia; rewrite Hk, Hk' in Ht; try discriminate Ht; first [exact Hx | exact Hy].
  Qed.

  Theorem sb_rel_lin_gen si (indep : COp -> COp -> Prop) :
    indep (Inc CX) (Get CY) -> indep (Inc CY) (Get CX) ->
    RelaxedTraceLin.rel_lin (@PrefixView.sel (CxySig si)) (sb_trace si) indep
      (@RelaxedHoareSpec.seq_legal (CxySig si) MSt δcxy s00).
  Proof.
    intros Hx Hy. exists (sb_Wg si). split; [| split; [| split; [| split]]].
    - exists (1, 1). repeat (econstructor; [split; reflexivity |]). constructor.
    - cbn. repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    - intros o Ho. cbn in Ho. split.
      + repeat (destruct Ho as [<- | Ho];
          [solve [exists 0; eexists; split; reflexivity | exists 1; eexists; split; reflexivity
                 | exists 2; eexists; split; reflexivity | exists 3; eexists; split; reflexivity] |]).
        destruct Ho.
      + repeat (destruct Ho as [<- | Ho];
          [solve [exists 4; eexists; split; reflexivity | exists 5; eexists; split; reflexivity
                 | exists 6; eexists; split; reflexivity | exists 7; eexists; split; reflexivity] |]).
        destruct Ho.
    - intros i k op Hi.
      destruct (sb_inv_cases si _ _ _ Hi) as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]].
      + eexists. split; [right; right; left; reflexivity | reflexivity].
      + eexists. split; [left; reflexivity | reflexivity].
      + eexists. split; [right; right; right; left; reflexivity | reflexivity].
      + eexists. split; [right; left; reflexivity | reflexivity].
    - intros o o' _ _ Hr. exfalso. exact (sb_no_rhb_gen si indep o o' Hx Hy Hr).
  Qed.

  (** Under choice (b), directly (closed). *)
  Corollary sb_rel_lin_cb :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FCb) (sb_trace si_cb) si_cb (@RelaxedHoareSpec.seq_legal FCb MSt δcxy s00).
  Proof. apply sb_rel_lin_gen; discriminate. Qed.

  (** The SB trace is a trace of the choice-(b) module: [si_mb] contains
      the two crossing pairs [(Faa x, Rd y)], [(Faa y, Rd x)]. *)
  Corollary sb_mtraces_b : MTraces (@RelaxedHoareSpec.EI EMb MSt δmem) Mb (s00, []) (sb_trace si_cb).
  Proof. apply sb_mtraces_gen; discriminate. Qed.

  (** Under choice (b), through the instance ([cxyb_rel_lin];
      [classic], [eq_rect_eq]). *)
  Corollary sb_rel_lin_b :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FCb) (sb_trace si_cb) si_cb (@RelaxedHoareSpec.seq_legal FCb MSt δcxy s00).
  Proof. exact (cxyb_rel_lin _ sb_mtraces_b (sb_complete si_cb)). Qed.

  (** *** The load-buffering execution (m-46 (d)) *)

  Lemma CLoc_eq_dec (a b : CLoc) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (** Over the by-location underlay [EM], for every overlay relation
      [si]: thread [t1] invokes [get_x] (handle 0), then [inc_y] (handle
      1) while [get_x] is pending; thread [t2] invokes [get_y], then
      [inc_x].  Each [Faa] is emitted before its own thread's pending
      [Rd] (semi-independent by location), so both [Faa]s return 0 and
      both [Rd]s then return 1. *)
  Section LB.
    Context (si : COp -> COp -> Prop).
    Local Abbreviation F := (CxySig si).
    Local Abbreviation V := (@RelaxedHoareSpec.EI EM MSt δmem).

    Definition lb_evs : list (ModuleEvent EM F) :=
      [OverlayEvent (oi si t1 0 (Get CX)); OverlayEvent (oi si t1 1 (Inc CY));
       OverlayEvent (oi si t2 0 (Get CY)); OverlayEvent (oi si t2 1 (Inc CX));
       UnderlayEvent (untag (ui t1 1 (Faa CY))); UnderlayEvent (untag (ur t1 1 (Faa CY) 0));
       OverlayEvent (orr si t1 1 (Inc CY) 0);
       UnderlayEvent (untag (ui t2 1 (Faa CX))); UnderlayEvent (untag (ur t2 1 (Faa CX) 0));
       OverlayEvent (orr si t2 1 (Inc CX) 0);
       UnderlayEvent (untag (ui t1 0 (Rd CX))); UnderlayEvent (untag (ur t1 0 (Rd CX) 1));
       OverlayEvent (orr si t1 0 (Get CX) 1);
       UnderlayEvent (untag (ui t2 0 (Rd CY))); UnderlayEvent (untag (ur t2 0 (Rd CY) 1));
       OverlayEvent (orr si t2 0 (Get CY) 1)].

    Definition lb_trace : list (ThreadEvent F) :=
      [oi si t1 0 (Get CX); oi si t1 1 (Inc CY); oi si t2 0 (Get CY); oi si t2 1 (Inc CX);
       orr si t1 1 (Inc CY) 0; orr si t2 1 (Inc CX) 0; orr si t1 0 (Get CX) 1; orr si t2 0 (Get CY) 1].

    Lemma lb_overlay : RelaxedGSim.overlay_events lb_evs = lb_trace.
    Proof. reflexivity. Qed.

    Local Ltac nin := cbn; let H := fresh in intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.

    (** The execution, from module steps ([tagged_invoke],
        [tagged_underlay], [tagged_return]) over the plain [EI δmem];
        every call returns. *)
    Theorem lb_exec :
      exists c, module_execution_tagged V (Mcxy si) (initial_tagged_module V (s00, [])) lb_evs c /\
        (forall e, In e (tm_calls c) -> ce_cell F e = DeadCall).
    Proof.
      eexists. split.
      - unfold lb_evs.
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t1 0 (Get CX) (s00, []) [] [] [] [ui t1 0 (Rd CX); ur t1 0 (Rd CX) 1] 1).
          - intros [].
          - apply call_produces.
          - split; [repeat constructor; intros [] | intros key Hk []]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t1 1 (Inc CY) (s00, []) _ _ _ [ui t1 1 (Faa CY); ur t1 1 (Faa CY) 0] 0).
          - nin.
          - apply call_produces.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t2 0 (Get CY) (s00, []) _ _ _ [ui t2 0 (Rd CY); ur t2 0 (Rd CY) 1] 1).
          - nin.
          - apply call_produces.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_invoke V (Mcxy si) t2 1 (Inc CX) (s00, []) _ _ _ [ui t2 1 (Faa CX); ur t2 1 (Faa CX) 0] 0).
          - nin.
          - apply call_produces.
          - split; [repeat constructor; intros [] |]. intros key [<- | []]. nin. }
        (* t1's FAA on y overtakes t1's pending read of x *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 1) (ui t1 1 (Faa CY)))).
          - cbn. apply tagged_select_next; [apply cross_inv_inv; discriminate |].
            apply tagged_select_next; [apply cross_res_inv |]. apply tagged_select_here.
          - cbn. exists 0, (0, 1). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 1) (ur t1 1 (Faa CY) 0))).
          - cbn. apply tagged_select_next; [apply cross_inv_res; discriminate |].
            apply tagged_select_next; [apply cross_res_res |]. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        (* t2's FAA on x overtakes t2's pending read of y *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 1) (ui t2 1 (Faa CX)))).
          - cbn. apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_inv_inv; discriminate |].
            apply tagged_select_next; [apply cross_res_inv |]. apply tagged_select_here.
          - cbn. exists 0, (1, 1). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 1) (ur t2 1 (Faa CX) 0))).
          - cbn. apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_thread; discriminate |].
            apply tagged_select_next; [apply cross_inv_res; discriminate |].
            apply tagged_select_next; [apply cross_res_res |]. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_here.
          - nin. }
        (* the two reads, each returning 1 *)
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 0) (ui t1 0 (Rd CX)))).
          - cbn. apply tagged_select_here.
          - cbn. exists 1, (1, 1). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t1, 0) (ur t1 0 (Rd CX) 1))).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |].
            apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 0) (ui t2 0 (Rd CY)))).
          - cbn. apply tagged_select_here.
          - cbn. exists 1, (1, 1). split; [split; reflexivity | reflexivity]. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay V (Mcxy si) (@Build_TaggedScheduledEvent EM F (t2, 0) (ur t2 0 (Rd CY) 1))).
          - cbn. apply tagged_select_here.
          - cbn. exists [], []. split; reflexivity. }
        eapply tagged_module_execution_cons.
        { apply tagged_return.
          - apply finish_next; [intros H; discriminate H |]. apply finish_here.
          - nin. }
        apply tagged_module_execution_refl.
      - intros e He. cbn in He. repeat (destruct He as [<- | He]; [reflexivity |]). destruct He.
    Qed.

    Corollary lb_mtraces : MTraces V (Mcxy si) (s00, []) lb_trace.
    Proof. destruct lb_exec as (c & Hex & _). exists lb_evs, c. split; [exact Hex | reflexivity]. Qed.

    Local Abbreviation sel := (@PrefixView.sel F).
    Local Abbreviation OpF := (RelaxedTraceLin.Op F).

    Lemma lb_inv_cases i k (op : COp) :
      RelaxedTraceLin.inv_at sel lb_trace i k op ->
      (i = 0 /\ k = (t1, 0) /\ op = Get CX) \/ (i = 1 /\ k = (t1, 1) /\ op = Inc CY) \/
      (i = 2 /\ k = (t2, 0) /\ op = Get CY) \/ (i = 3 /\ k = (t2, 1) /\ op = Inc CX).
    Proof.
      intros (x & Hx & Hs). destruct k as [t h]. cbn [fst snd] in Hs.
      do 8 (destruct i as [| i]; [cbn in Hx; injection Hx as <-; cbn in Hs;
             first [discriminate Hs | injection Hs as Ht Hh Ho; subst; tauto] |]).
      destruct i; cbn in Hx; discriminate Hx.
    Qed.

    Lemma lb_res_cases j k (op : COp) (r : Sig.ar op) :
      RelaxedTraceLin.res_at sel lb_trace j k op r ->
      (j = 4 /\ k = (t1, 1) /\ op = Inc CY /\ r = 0) \/ (j = 5 /\ k = (t2, 1) /\ op = Inc CX /\ r = 0) \/
      (j = 6 /\ k = (t1, 0) /\ op = Get CX /\ r = 1) \/ (j = 7 /\ k = (t2, 0) /\ op = Get CY /\ r = 1).
    Proof.
      intros (x & Hx & Hs). destruct k as [t h]. cbn [fst snd] in Hs.
      pose proof (f_equal (option_map (te_tid F)) Hs) as Ht.
      pose proof (f_equal (option_map (ev_h si)) Hs) as Hh.
      pose proof (f_equal (option_map (ev_op si)) Hs) as Ho.
      pose proof (f_equal (option_map (ev_val si)) Hs) as Hr.
      pose proof (f_equal (option_map (ev_isres si)) Hs) as Hk.
      clear Hs. cbn in Ht, Hh, Ho, Hr, Hk.
      do 8 (destruct j as [| j]; [cbn in Hx; injection Hx as <-; cbn in Ht, Hh, Ho, Hr, Hk;
             first [discriminate Hk |
                    injection Ht as Ht; injection Hh as Hh; injection Ho as Ho; injection Hr as Hr;
                    subst; tauto] |]).
      destruct j; cbn in Hx; discriminate Hx.
    Qed.

    (** Every invocation has a response. *)
    Lemma lb_complete : PrefixView.complete lb_trace.
    Proof.
      intros i k op Hi.
      destruct (lb_inv_cases i k op Hi) as [(-> & -> & ->) | [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]]].
      - exists 6, 1. eexists. split; reflexivity.
      - exists 4, 0. eexists. split; reflexivity.
      - exists 7, 1. eexists. split; reflexivity.
      - exists 5, 0. eexists. split; reflexivity.
    Qed.

    (** Legality: a [Get c] that returns more than the initial value of
        [c] has an [Inc c] before it. *)
    Lemma δcxy_other s (o : COp) (r : nat) s' c :
      δcxy s o r s' -> o <> Inc c -> get s' c = get s c.
    Proof.
      destruct o as [c' | c']; cbn; intros [_ ->] Hne; [| reflexivity].
      destruct c', c; cbn; try reflexivity; exfalso; apply Hne; reflexivity.
    Qed.

    Lemma seq_get_gt_inc s (W : list OpF) s' j (oj : OpF) c :
      @RelaxedHoareSpec.seq_run F MSt δcxy s W s' -> nth_error W j = Some oj ->
      RelaxedTraceLin.op_op oj = Get c -> get s c < RelaxedTraceLin.op_ret oj ->
      exists i oi, i < j /\ nth_error W i = Some oi /\ RelaxedTraceLin.op_op oi = Inc c.
    Proof.
      intros Hrun. revert j. induction Hrun as [s | s o s1 W s2 Hd Hrun IH]; intros j Hj Hop Hlt;
        [destruct j; discriminate Hj |].
      destruct j as [| j]; cbn in Hj.
      - injection Hj as ->. destruct oj as [k op r]. cbn in Hop, Hd, Hlt. subst op. cbn in Hd.
        destruct Hd as [-> _]. lia.
      - destruct o as [ko op ro]. cbn [RelaxedTraceLin.op_op RelaxedTraceLin.op_ret] in Hd.
        destruct op as [c' | c'].
        + destruct (CLoc_eq_dec c' c) as [-> | Hne].
          * exists 0, (@RelaxedTraceLin.Build_Op F ko (Inc c) ro). split; [lia |]. split; reflexivity.
          * rewrite <- (δcxy_other _ _ _ _ c Hd) in Hlt by (intros H; injection H as H; exact (Hne H)).
            destruct (IH j Hj Hop Hlt) as (i & oi & Hij & Hi & Hoi). exists (S i), oi. split; [lia | auto].
        + rewrite <- (δcxy_other _ _ _ _ c Hd) in Hlt by discriminate.
          destruct (IH j Hj Hop Hlt) as (i & oi & Hij & Hi & Hoi). exists (S i), oi. split; [lia | auto].
    Qed.
  End LB.

  (** *** LB is accepted only under choice (a) *)

  Section LBLin.
    Context (si : COp -> COp -> Prop).
    Local Abbreviation F := (CxySig si).
    Local Abbreviation OpF := (RelaxedTraceLin.Op F).
    Local Abbreviation sel := (@PrefixView.sel F).

    Lemma lb_witness_op (W : list OpF) (o : OpF) k op :
      (forall o, In o W -> RelaxedTraceLin.occurs sel (lb_trace si) o) -> In o W ->
      RelaxedTraceLin.op_key o = k -> (exists i, RelaxedTraceLin.inv_at sel (lb_trace si) i k op) ->
      RelaxedTraceLin.op_op o = op.
    Proof.
      intros Hocc Ho Hk (i & Hi). destruct (Hocc o Ho) as [(i' & Hi') _]. rewrite Hk in Hi'.
      destruct (lb_inv_cases si _ _ _ Hi) as [(-> & -> & ->) | [(-> & -> & ->) | [(-> & -> & ->) | (-> & -> & ->)]]];
      destruct (lb_inv_cases si _ _ _ Hi') as [(_ & Hk' & ->) | [(_ & Hk' & ->) | [(_ & Hk' & ->) | (_ & Hk' & ->)]]];
      solve [reflexivity | discriminate Hk'].
    Qed.

    Lemma lb_witness_get (W : list OpF) (o : OpF) c :
      (forall o, In o W -> RelaxedTraceLin.occurs sel (lb_trace si) o) -> In o W ->
      RelaxedTraceLin.op_op o = Get c -> RelaxedTraceLin.op_ret o = 1.
    Proof.
      intros Hocc Ho Hop. destruct (Hocc o Ho) as [_ (j & Hj)]. rewrite Hop in Hj.
      destruct (lb_res_cases si _ _ _ _ Hj) as [(_ & _ & Ho' & _) | [(_ & _ & Ho' & _) | [(_ & _ & _ & Hr) | (_ & _ & _ & Hr)]]];
        [discriminate Ho' | discriminate Ho' | exact Hr | exact Hr].
    Qed.

    (** Every [Inc c] of a witness is the trace's (single) [inc_c]. *)
    Lemma lb_witness_inc (W : list OpF) (o : OpF) c :
      (forall o, In o W -> RelaxedTraceLin.occurs sel (lb_trace si) o) -> In o W ->
      RelaxedTraceLin.op_op o = Inc c -> RelaxedTraceLin.op_key o = (match c with CX => t2 | CY => t1 end, 1).
    Proof.
      intros Hocc Ho Hop. destruct (Hocc o Ho) as [(i & Hi) _]. rewrite Hop in Hi.
      destruct (lb_inv_cases si _ _ _ Hi) as [(_ & Hk & Hc) | [(_ & Hk & Hc) | [(_ & Hk & Hc) | (_ & Hk & Hc)]]];
        try discriminate Hc; injection Hc as Hc; subst c; exact Hk.
    Qed.

    Lemma nth_in_inj (W : list OpF) i j a :
      NoDup W -> nth_error W i = Some a -> nth_error W j = Some a -> i = j.
    Proof.
      intros Hnd Hi Hj. apply (proj1 (NoDup_nth_error W) Hnd); [apply nth_error_Some; rewrite Hi; discriminate |].
      rewrite Hi, Hj. reflexivity.
    Qed.

    Lemma inv_at_lb i k op : nth_error (lb_trace si) i = Some (Build_ThreadEvent (fst k) (@InvEv F (snd k) op)) ->
      RelaxedTraceLin.inv_at sel (lb_trace si) i k op.
    Proof. intros H. eexists. split; [exact H | reflexivity]. Qed.

    (** Under any overlay relation without [(Get x, Inc y)] and
        [(Get y, Inc x)], the LB trace is not relaxed-linearizable: the
        program-order edges [get_x → inc_y] and [get_y → inc_x] are rhb
        edges, and legality puts [inc_x] before [get_x] and [inc_y]
        before [get_y] (each [get] returns 1, [seq_get_gt_inc]); the four
        positions form a cycle. *)
    Theorem lb_not_rel_lin_gen (indep : COp -> COp -> Prop) :
      ~ indep (Get CX) (Inc CY) -> ~ indep (Get CY) (Inc CX) ->
      ~ RelaxedTraceLin.rel_lin sel (lb_trace si) indep (@RelaxedHoareSpec.seq_legal F MSt δcxy s00).
    Proof.
      intros Hn1 Hn2 (W & (s & Hrun) & Hnd & Hocc & Hall & Hord).
      assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
      assert (I0 : RelaxedTraceLin.inv_at sel (lb_trace si) 0 (t1, 0) (Get CX)) by (apply inv_at_lb; reflexivity).
      assert (I1 : RelaxedTraceLin.inv_at sel (lb_trace si) 1 (t1, 1) (Inc CY)) by (apply inv_at_lb; reflexivity).
      assert (I2 : RelaxedTraceLin.inv_at sel (lb_trace si) 2 (t2, 0) (Get CY)) by (apply inv_at_lb; reflexivity).
      assert (I3 : RelaxedTraceLin.inv_at sel (lb_trace si) 3 (t2, 1) (Inc CX)) by (apply inv_at_lb; reflexivity).
      destruct (Hall _ _ _ I0) as (o1 & Ho1 & Hk1).
      destruct (Hall _ _ _ I1) as (o2 & Ho2 & Hk2).
      destruct (Hall _ _ _ I2) as (o3 & Ho3 & Hk3).
      destruct (Hall _ _ _ I3) as (o4 & Ho4 & Hk4).
      pose proof (lb_witness_op W o1 _ _ Hocc Ho1 Hk1 (ex_intro _ 0 I0)) as Hop1.
      pose proof (lb_witness_op W o2 _ _ Hocc Ho2 Hk2 (ex_intro _ 1 I1)) as Hop2.
      pose proof (lb_witness_op W o3 _ _ Hocc Ho3 Hk3 (ex_intro _ 2 I2)) as Hop3.
      pose proof (lb_witness_op W o4 _ _ Hocc Ho4 Hk4 (ex_intro _ 3 I3)) as Hop4.
      pose proof (lb_witness_get W o1 CX Hocc Ho1 Hop1) as Hr1.
      pose proof (lb_witness_get W o3 CY Hocc Ho3 Hop3) as Hr3.
      (* the two program-order edges get_x → inc_y and get_y → inc_x *)
      assert (Hb12 : RelaxedTraceLin.before W o1 o2).
      { apply Hord; [exact Ho1 | exact Ho2 |]. right. split; [rewrite Hk1, Hk2; reflexivity |].
        exists 0, 1. rewrite Hk1, Hk2, Hop1, Hop2. split; [exact I0 |]. split; [exact I1 |]. split; [lia | exact Hn1]. }
      assert (Hb34 : RelaxedTraceLin.before W o3 o4).
      { apply Hord; [exact Ho3 | exact Ho4 |]. right. split; [rewrite Hk3, Hk4; reflexivity |].
        exists 2, 3. rewrite Hk3, Hk4, Hop3, Hop4. split; [exact I2 |]. split; [exact I3 |]. split; [lia | exact Hn2]. }
      destruct (In_nth_error _ _ Ho1) as (i1 & Hi1).
      destruct (In_nth_error _ _ Ho2) as (i2 & Hi2).
      destruct (In_nth_error _ _ Ho3) as (i3 & Hi3).
      destruct (In_nth_error _ _ Ho4) as (i4 & Hi4).
      pose proof (before_idx si W _ _ _ _ HndW Hb12 Hi1 Hi2) as H12.
      pose proof (before_idx si W _ _ _ _ HndW Hb34 Hi3 Hi4) as H34.
      (* legality: get_x reads 1, so some inc_x, i.e. o4, precedes it; likewise o2 precedes o3 *)
      assert (H41 : i4 < i1).
      { destruct (seq_get_gt_inc si _ _ _ _ _ CX Hrun Hi1 Hop1 ltac:(rewrite Hr1; cbn; lia)) as (i & oi & Hlt & Hi & Hoi).
        pose proof (lb_witness_inc W oi CX Hocc (nth_error_In _ _ Hi) Hoi) as Hki.
        assert (oi = o4) as ->.
        { apply (nodup_map_in_inj (@RelaxedTraceLin.op_key F) W); [exact Hnd | exact (nth_error_In _ _ Hi) | exact Ho4 |].
          rewrite Hki, Hk4. reflexivity. }
        rewrite (nth_in_inj W i4 i o4 HndW Hi4 Hi). exact Hlt. }
      assert (H23 : i2 < i3).
      { destruct (seq_get_gt_inc si _ _ _ _ _ CY Hrun Hi3 Hop3 ltac:(rewrite Hr3; cbn; lia)) as (i & oi & Hlt & Hi & Hoi).
        pose proof (lb_witness_inc W oi CY Hocc (nth_error_In _ _ Hi) Hoi) as Hki.
        assert (oi = o2) as ->.
        { apply (nodup_map_in_inj (@RelaxedTraceLin.op_key F) W); [exact Hnd | exact (nth_error_In _ _ Hi) | exact Ho2 |].
          rewrite Hki, Hk2. reflexivity. }
        rewrite (nth_in_inj W i2 i o2 HndW Hi2 Hi). exact Hlt. }
      lia.
    Qed.
  End LBLin.

  (** Under choice (a), directly (closed): under [by_counter] the LB
      trace has no rhb edge, and [inc_y 0; inc_x 0; get_x 1; get_y 1] is
      a legal witness. *)
  Definition lb_W : list (RelaxedTraceLin.Op FC) :=
    [@RelaxedTraceLin.Build_Op FC (t1, 1) (Inc CY) 0; @RelaxedTraceLin.Build_Op FC (t2, 1) (Inc CX) 0;
     @RelaxedTraceLin.Build_Op FC (t1, 0) (Get CX) 1; @RelaxedTraceLin.Build_Op FC (t2, 0) (Get CY) 1].

  Lemma lb_no_rhb (o o' : RelaxedTraceLin.Op FC) :
    ~ RelaxedTraceLin.rhb (@PrefixView.sel FC) (lb_trace by_counter) by_counter o o'.
  Proof.
    intros [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
    - destruct (lb_res_cases by_counter _ _ _ _ Hi) as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]];
      destruct (lb_inv_cases by_counter _ _ _ Hj) as [(-> & _) | [(-> & _) | [(-> & _) | (-> & _)]]]; lia.
    - apply Hn.
      destruct (lb_inv_cases by_counter _ _ _ Hi) as [(-> & Hk & ->) | [(-> & Hk & ->) | [(-> & Hk & ->) | (-> & Hk & ->)]]];
      destruct (lb_inv_cases by_counter _ _ _ Hj) as [(-> & Hk' & ->) | [(-> & Hk' & ->) | [(-> & Hk' & ->) | (-> & Hk' & ->)]]];
      try lia; rewrite Hk, Hk' in Ht; try discriminate Ht; intros Heq; discriminate Heq.
  Qed.

  Theorem lb_rel_lin_direct :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (lb_trace by_counter) by_counter
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
  Proof.
    exists lb_W. split; [| split; [| split; [| split]]].
    - exists (1, 1). repeat (econstructor; [split; reflexivity |]). constructor.
    - cbn. repeat constructor; cbn; intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    - intros o Ho. cbn in Ho. split.
      + repeat (destruct Ho as [<- | Ho];
          [solve [exists 0; eexists; split; reflexivity | exists 1; eexists; split; reflexivity
                 | exists 2; eexists; split; reflexivity | exists 3; eexists; split; reflexivity] |]).
        destruct Ho.
      + repeat (destruct Ho as [<- | Ho];
          [solve [exists 4; eexists; split; reflexivity | exists 5; eexists; split; reflexivity
                 | exists 6; eexists; split; reflexivity | exists 7; eexists; split; reflexivity] |]).
        destruct Ho.
    - intros i k op Hi.
      destruct (lb_inv_cases by_counter _ _ _ Hi) as [(_ & -> & _) | [(_ & -> & _) | [(_ & -> & _) | (_ & -> & _)]]].
      + eexists. split; [right; right; left; reflexivity | reflexivity].
      + eexists. split; [left; reflexivity | reflexivity].
      + eexists. split; [right; right; right; left; reflexivity | reflexivity].
      + eexists. split; [right; left; reflexivity | reflexivity].
    - intros o o' _ _ Hr. exfalso. exact (lb_no_rhb o o' Hr).
  Qed.

  (** Under choice (a), through the instance ([cxy_rel_lin]; [classic],
      [eq_rect_eq]): the LB trace is a complete trace of [M_cxy]. *)
  Corollary lb_rel_lin :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (lb_trace by_counter) by_counter
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
  Proof. exact (cxy_rel_lin _ (lb_mtraces by_counter) (lb_complete by_counter)). Qed.

  Corollary lb_not_rel_lin_cb si :
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (CxySig si)) (lb_trace si) si_cb
      (@RelaxedHoareSpec.seq_legal (CxySig si) MSt δcxy s00).
  Proof. apply lb_not_rel_lin_gen; intros []. Qed.

  Corollary lb_not_rel_lin0 si :
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel (CxySig si)) (lb_trace si) (fun _ _ => False)
      (@RelaxedHoareSpec.seq_legal (CxySig si) MSt δcxy s00).
  Proof. apply lb_not_rel_lin_gen; intros []. Qed.

  (** One trace, three relations: accepted under [by_counter], rejected
      under [si_cb] and under ∅. *)
  Corollary lb_si_decides :
    RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (lb_trace by_counter) by_counter
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00) /\
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (lb_trace by_counter) si_cb
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00) /\
    ~ RelaxedTraceLin.rel_lin (@PrefixView.sel FC) (lb_trace by_counter) (fun _ _ => False)
      (@RelaxedHoareSpec.seq_legal FC MSt δcxy s00).
  Proof. exact (conj lb_rel_lin_direct (conj (lb_not_rel_lin_cb by_counter) (lb_not_rel_lin0 by_counter))). Qed.

  (** *** The mixed cell (by_location, si_cb) (m-46 (e))

      With the by-location underlay and the choice-(b) overlay relation,
      no [I], [R], [G] verify the bodies: [rlhl_complin_eihl] and
      [cc_rel_lin] would make the LB trace (a complete trace of this
      module, [lb_exec si_cb]) relaxed-linearizable under [si_cb], which
      [lb_not_rel_lin_cb] refutes.  This is a property of the module,
      not of the proof method (see the section header).  [classic] and
      [eq_rect_eq] enter through [rlhl_complin_eihl] and [cc_rel_lin]. *)
  Definition M_mixed : RelaxedModuleImpl EM FCb := Mcxy si_cb.

  Theorem cxy_mixed_no_rlhl2 :
    forall (I : Assn (EIhl δmem) (@RelaxedHoareSpec.EI FCb MSt δcxy))
           (R G : CallKey FCb -> PRel (EIhl δmem) (@RelaxedHoareSpec.EI FCb MSt δcxy)),
      ~ RLHL2Hyps I R G M_mixed cxy_σ0 cxyb_v0.
  Proof.
    intros I R G HH.
    pose proof (rlhl_complin_eihl δmem (F := FCb) δcxy s00 I R G M_mixed (s00, []) HH) as Hcc.
    pose proof (Hcc _ (lb_mtraces si_cb)) as Hrt.
    exact (lb_not_rel_lin_cb si_cb (cc_rel_lin (F := FCb) δcxy s00 _ Hrt (lb_complete _))).
  Qed.

  (** The LB trace is not a trace of the choice-(b) module (m-46 (f)):
      by [cxyb_rel_lin], every complete trace of [Mb] is
      relaxed-linearizable under [si_cb], and LB is not
      ([classic], [eq_rect_eq]). *)
  Corollary lb_not_trace_b : ~ MTraces (@RelaxedHoareSpec.EI EMb MSt δmem) Mb (s00, []) (lb_trace si_cb).
  Proof. intros H. exact (lb_not_rel_lin_cb si_cb (cxyb_rel_lin _ H (lb_complete si_cb))). Qed.

  (** The table (m-46 (g)): the positive cells (∅, ∅), (a), (b) and
      the universal negatives (by_location, ∅) and (by_location, si_cb)
      ([classic] and [eq_rect_eq], from the two negatives, through
      [rlhl_complin_eihl] and [cc_rel_lin]). *)
  Theorem cxy_si_table :
    RLHL2Hyps (@Iren E00 F0 MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true)) (@Rren E00 F0 MSt MSt δmem δcxy)
      (@Gren E00 F0 MSt MSt δmem δcxy) M00 cxy00_σ0 cxy0_v0 /\
    RLHL2Hyps Icxy Rcxy Gcxy M_cxy cxy_σ0 cxy_v0 /\
    RLHL2Hyps Icxyb Rcxyb Gcxyb Mb cxyb_σ0 cxyb_v0 /\
    (forall (I : Assn (EIhl δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy))
            (R G : CallKey F0 -> PRel (EIhl δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy)),
        ~ RLHL2Hyps I R G M_cxy0 cxy_σ0 cxy0_v0) /\
    (forall (I : Assn (EIhl δmem) (@RelaxedHoareSpec.EI FCb MSt δcxy))
            (R G : CallKey FCb -> PRel (EIhl δmem) (@RelaxedHoareSpec.EI FCb MSt δcxy)),
        ~ RLHL2Hyps I R G M_mixed cxy_σ0 cxyb_v0).
  Proof. exact (conj cxy00_rlhl2 (conj cxy_rlhl2 (conj cxyb_rlhl2 (conj cxy0_no_rlhl2 cxy_mixed_no_rlhl2)))). Qed.


  (* ==================================================================== *)
  (** ** The free cells and the characterisation on the 3 × 3 family
      (latest-review m-49; RLHL-3b iteration 3)

      No declaration above this section is changed.  This section fills
      the four blank cells of the table, for (SI_E, SI_F) in {∅, [si_mb],
      [by_location]} × {∅, [si_cb], [by_counter]}, and proves the
      characterisation on these nine pairs.
      - (∅, [si_cb]) and (∅, [by_counter]): ✓, [cxy0cb_rlhl2] and
        [cxy0cnt_rlhl2], from [ren_rlhl2]; inheritance holds trivially
        (the double negation of the empty relation implies [False],
        [cxy0_si]).
      - ([si_mb], [by_counter]): ✓, [cxybcnt_rlhl2], from [ren_rlhl2];
        inheritance holds by inclusion ([si_mb] ∘ ρ is [si_cb], which is
        included in [by_counter]; [cxybcnt_si], constructive).
      - ([si_mb], ∅): ✗ for every [I], [R], [G], [cxyb0_no_rlhl2]: the SB
        execution [sb_exec_gen] at [si_mb] (its trace [sb_mtraces_gen],
        as for [sb_mtraces_b]) is a complete trace of the module, and
        under ∅ it is not relaxed-linearizable ([sb_not_rel_lin0]);
        through [rlhl_complin_eihl] and [cc_rel_lin], as for
        [cxy0_no_rlhl2].
      [mgen_rlhl2] (closed) is [ren_rlhl2] for [Mgen siE siF] at every
      pair of relations with the double-negated inheritance; the three
      new positive cells are its instances.

      The characterisation ([cxy_si_char]): for each of the nine pairs,
      [RLHL2Hyps] has a model ([cxy_cell]: some [I], [R], [G], from the
      initial states [((s00, []), [])] and [(s00, [])]) for [Mgen SI_E
      SI_F] iff SI_E ∘ ρ ⊆ SI_F.  Scope: these nine pairs only (an
      enumeration [SIRowE] × [SIColF]).  The proof is cell by cell: in
      the six ✓ cells both sides hold (the inclusion is checked
      directly, not derived from the model), in the three ✗ cells both
      fail (a universal negative, and a crossing pair outside SI_F); so
      [cxy_si_char] is a compact restatement of the full table, not a
      generic argument.  Not proved: the same statement
      for every pair of relations.  Its ⇐ half is [mgen_rlhl2] (with
      [RelaxedHoareInherit.ren_si_of_plain] to remove the double
      negation, [classic]); its ⇒ half needs, for every crossing pair
      [(o1, o2)] with [SI_E (ρ o1) (ρ o2)] and [~ SI_F o1 o2], a
      module-derived complete trace that is not relaxed-linearizable
      under SI_F.  Here only two such witness families exist, each for
      both cross pairs at once: [sb_exec_gen] with [sb_not_rel_lin0]
      (SI_E contains both [(Faa x, Rd y)] and [(Faa y, Rd x)]; SI_F
      empty) and [lb_exec] with [lb_not_rel_lin_gen] (SI_E =
      [by_location]; SI_F lacks both [(Get x, Inc y)] and [(Get y, Inc
      x)]).  Witnesses for a single crossing pair, for the (Inc, Inc)
      and (Get, Get) crossings and for same-counter crossings are not
      constructed (DEFERRED).

      The full table (✓ = [RLHL2Hyps] instance; ✗ = no [I], [R], [G];
      "new" = this section):

      | SI_E \ SI_F    | ∅         | si_cb (b) | by_counter (a) |
      |----------------|-----------|-----------|----------------|
      | ∅              | ✓         | ✓ new     | ✓ new          |
      | si_mb (b)      | ✗ new     | ✓         | ✓ new          |
      | by_location    | ✗         | ✗ (mixed) | ✓              |

      Assumptions: [cxy0_si], [cxybcnt_si], [mgen_inj], [mgen_rlhl2],
      [cxy0cb_rlhl2], [cxy0cnt_rlhl2], [cxybcnt_rlhl2] are closed;
      [cxyb0_no_rlhl2] and [cxy_si_char] use [classic] and [eq_rect_eq]
      (through [rlhl_complin_eihl] and [cc_rel_lin], and the existing
      negatives).  The scope is that of the table above (SC cell,
      renaming bodies, complete traces for [rel_lin]). *)

  (** Inheritance from the empty underlay relation, to any overlay
      relation (trivially). *)
  Lemma cxy0_si (siF : COp -> COp -> Prop) :
    forall o1 o2 : COp, ~ ~ (fun _ _ : MOp => False) (ρ o1) (ρ o2) -> siF o1 o2.
  Proof. intros o1 o2 Hnn. exfalso. exact (Hnn (fun x => x)). Qed.

  (** Inheritance from [si_mb] to [by_counter] (by inclusion:
      [si_mb] ∘ ρ = [si_cb] ⊆ [by_counter]); constructive. *)
  Lemma cxybcnt_si : forall o1 o2 : COp, ~ ~ si_mb (ρ o1) (ρ o2) -> by_counter o1 o2.
  Proof.
    intros [c1 | c1] [c2 | c2] Hnn; cbn in *;
      first [intros Heq; apply Hnn; intros Hne; exact (Hne Heq) | exfalso; apply Hnn; intros []].
  Qed.

  Lemma mgen_inj (siE : MOp -> MOp -> Prop) : forall u o (r1 r2 : Sig.ar (ρ o)),
      @RelaxedTraceLin.Build_Op (EMsi siE) u (ρ o) r1 = @RelaxedTraceLin.Build_Op (EMsi siE) u (ρ o) r2 ->
      backc o r1 = backc o r2.
  Proof.
    intros u o r1 r2 H. exact (f_equal (fun x : RelaxedTraceLin.Op (EMsi siE) => (RelaxedTraceLin.op_ret x : nat)) H).
  Qed.

  (** [ren_rlhl2] for [Mgen siE siF], at every pair of relations with
      the double-negated inheritance (closed). *)
  Theorem mgen_rlhl2 (siE : MOp -> MOp -> Prop) (siF : COp -> COp -> Prop) :
    (forall o1 o2 : COp, ~ ~ siE (ρ o1) (ρ o2) -> siF o1 o2) ->
    RLHL2Hyps (@Iren (EMsi siE) (CxySig siF) MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true))
      (@Rren (EMsi siE) (CxySig siF) MSt MSt δmem δcxy) (@Gren (EMsi siE) (CxySig siF) MSt MSt δmem δcxy)
      (Mgen siE siF) ((s00, []), []) (s00, []).
  Proof.
    intros Hsi.
    exact (@ren_rlhl2 (EMsi siE) (CxySig siF) MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true) backc cxy_δ Hsi
             (fun _ => eq_refl) (mgen_inj siE) (Mgen siE siF) (fun _ _ => eq_refl) s00).
  Qed.

  (** (∅, [si_cb]): ✓. *)
  Theorem cxy0cb_rlhl2 :
    RLHL2Hyps (@Iren E00 FCb MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true)) (@Rren E00 FCb MSt MSt δmem δcxy)
      (@Gren E00 FCb MSt MSt δmem δcxy) (Mgen (fun _ _ => False) si_cb) cxy00_σ0 cxyb_v0.
  Proof. exact (mgen_rlhl2 (fun _ _ => False) si_cb (cxy0_si si_cb)). Qed.

  (** (∅, [by_counter]): ✓. *)
  Theorem cxy0cnt_rlhl2 :
    RLHL2Hyps (@Iren E00 FC MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true)) (@Rren E00 FC MSt MSt δmem δcxy)
      (@Gren E00 FC MSt MSt δmem δcxy) (Mgen (fun _ _ => False) by_counter) cxy00_σ0 cxy_v0.
  Proof. exact (mgen_rlhl2 (fun _ _ => False) by_counter (cxy0_si by_counter)). Qed.

  (** ([si_mb], [by_counter]): ✓. *)
  Theorem cxybcnt_rlhl2 :
    RLHL2Hyps (@Iren EMb FC MSt MSt δmem δcxy (fun s => s) ρ (fun _ => true)) (@Rren EMb FC MSt MSt δmem δcxy)
      (@Gren EMb FC MSt MSt δmem δcxy) (Mgen si_mb by_counter) cxyb_σ0 cxy_v0.
  Proof. exact (mgen_rlhl2 si_mb by_counter cxybcnt_si). Qed.

  (** ([si_mb], ∅): ✗ for every [I], [R], [G].  The SB trace is a
      complete trace of [Mb0] ([sb_mtraces_gen] at [si_mb]: [si_mb]
      contains [(Faa x, Rd y)] and [(Faa y, Rd x)]); under ∅ it is not
      relaxed-linearizable ([sb_not_rel_lin0]).  [classic] and
      [eq_rect_eq] enter through [rlhl_complin_eihl] and [cc_rel_lin]. *)
  Definition Mb0 : RelaxedModuleImpl EMb F0 := Mgen si_mb (fun _ _ => False).

  Theorem cxyb0_no_rlhl2 :
    forall (I : Assn (EIhl (E := EMb) δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy))
           (R G : CallKey F0 -> PRel (EIhl (E := EMb) δmem) (@RelaxedHoareSpec.EI F0 MSt δcxy)),
      ~ RLHL2Hyps I R G Mb0 cxyb_σ0 cxy0_v0.
  Proof.
    intros I R G HH.
    pose proof (rlhl_complin_eihl (E := EMb) δmem (F := F0) δcxy s00 I R G Mb0 (s00, []) HH) as Hcc.
    pose proof (Hcc _ (sb_mtraces_gen si_mb (fun _ _ => False) ltac:(discriminate) ltac:(discriminate))) as Hrt.
    exact (sb_not_rel_lin0 _ (cc_rel_lin (F := F0) δcxy s00 _ Hrt (sb_complete _))).
  Qed.

  (** *** The characterisation on the nine pairs *)

  Inductive SIRowE : Type := RowE0 | RowEmb | RowEloc.
  Inductive SIColF : Type := ColF0 | ColFcb | ColFcnt.

  Definition siE_of (r : SIRowE) : MOp -> MOp -> Prop :=
    match r with RowE0 => fun _ _ => False | RowEmb => si_mb | RowEloc => by_location end.

  Definition siF_of (c : SIColF) : COp -> COp -> Prop :=
    match c with ColF0 => fun _ _ => False | ColFcb => si_cb | ColFcnt => by_counter end.

  (** [RLHL2Hyps] has a model for [Mgen siE siF] from the initial
      states of the table. *)
  Definition cxy_cell (siE : MOp -> MOp -> Prop) (siF : COp -> COp -> Prop) : Prop :=
    exists (I : Assn (EIhl (E := EMsi siE) δmem) (@RelaxedHoareSpec.EI (CxySig siF) MSt δcxy))
           (R G : CallKey (CxySig siF) -> PRel (EIhl (E := EMsi siE) δmem) (@RelaxedHoareSpec.EI (CxySig siF) MSt δcxy)),
      RLHL2Hyps I R G (Mgen siE siF) ((s00, []), []) (s00, []).

  (** On the nine pairs: a model exists iff SI_E ∘ ρ ⊆ SI_F
      ([classic], [eq_rect_eq], from the three negatives). *)
  Theorem cxy_si_char (r : SIRowE) (c : SIColF) :
    cxy_cell (siE_of r) (siF_of c) <-> (forall o1 o2 : COp, siE_of r (ρ o1) (ρ o2) -> siF_of c o1 o2).
  Proof.
    destruct r, c; cbn [siE_of siF_of]; split.
    (* (∅, ∅) *)
    - intros _ o1 o2 [].
    - intros _. do 3 eexists. exact (mgen_rlhl2 (fun _ _ => False) (fun _ _ => False) (cxy0_si _)).
    (* (∅, si_cb) *)
    - intros _ o1 o2 [].
    - intros _. do 3 eexists. exact (mgen_rlhl2 (fun _ _ => False) si_cb (cxy0_si si_cb)).
    (* (∅, by_counter) *)
    - intros _ o1 o2 [].
    - intros _. do 3 eexists. exact (mgen_rlhl2 (fun _ _ => False) by_counter (cxy0_si by_counter)).
    (* (si_mb, ∅) *)
    - intros (I & R & G & HH). exfalso. exact (cxyb0_no_rlhl2 I R G HH).
    - intros Hincl. exfalso. exact (Hincl (Inc CX) (Get CY) ltac:(cbn; discriminate)).
    (* (si_mb, si_cb) *)
    - intros _ [c1 | c1] [c2 | c2] H; cbn in H |- *; first [exact H | destruct H].
    - intros _. do 3 eexists. exact (mgen_rlhl2 si_mb si_cb cxyb_si).
    (* (si_mb, by_counter) *)
    - intros _ [c1 | c1] [c2 | c2] H; cbn in H |- *; first [exact H | destruct H].
    - intros _. do 3 eexists. exact (mgen_rlhl2 si_mb by_counter cxybcnt_si).
    (* (by_location, ∅) *)
    - intros (I & R & G & HH). exfalso. exact (cxy0_no_rlhl2 I R G HH).
    - intros Hincl. exfalso. exact (Hincl (Inc CX) (Get CY) ltac:(cbn; discriminate)).
    (* (by_location, si_cb) *)
    - intros (I & R & G & HH). exfalso. exact (cxy_mixed_no_rlhl2 I R G HH).
    - intros Hincl. exfalso. exact (Hincl (Get CX) (Inc CY) ltac:(cbn; discriminate)).
    (* (by_location, by_counter) *)
    - intros _ o1 o2 H. unfold by_location in H. rewrite !mloc_ρ in H. exact H.
    - intros _. do 3 eexists. exact (mgen_rlhl2 by_location by_counter cxy_si).
  Qed.

End RelaxedHoareCounterXY.
