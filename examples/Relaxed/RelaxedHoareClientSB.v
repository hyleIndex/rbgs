(** * A client of Counter_xy, verified from the counters' specification:
      store buffering with and without a [Wait] (task RLHL-3c.2; part 1
      of the client of the RLHL-3c plan)

    ** What this file is, and what it is not

    This is a *specification-level* client theorem.  The client runs over
    the plain effect-at-invocation specification LTS of the two counters,
    [RelaxedHoareSpec.EI δcxy] from [(s00, [])], with the overlay
    signature of Counter_xy as its underlay signature; the counters'
    implementation [M_cxy] and the memory cell [δmem] do not occur.  The
    transfer to the Counter_xy implementation over [EI δmem] is part 2
    (RLHL-3c.7, not in this file): it needs absorption ([absorb_ei],
    [RelaxedHoareAbsorb]) and linking ([RelaxedHoareLink]) of
    latest-review M-22, which do not exist yet.  Until part 2 exists,
    nothing here is a statement about the implementation.  This file
    imports neither [RelaxedHoareLayer] nor [RelaxedHoareAbsorb].

    ** Objects

    - [GS]: the client's signature: one operation [SB c] (arity [nat]),
      handles [nat], semi-independence ∅, every mode [Local]
      ([GS_wf]).  [other CX = CY], [other CY = CX].
    - [Mcl_si si : RelaxedModuleImpl (CxySig si) GS], the waiting
      client ([Mcl_si_unfold]):
      [SB c ↦ Future (Inc c) (λf. Wait f (λ_. Future (Get (other c))
      (λg. Wait g (λr. Ret r))))].  The untagged [Future] after the
      [Wait] carries the tag "every handle resolved so far", which
      contains the [Inc]'s handle, so (F3) orders [res(inc)] before
      [inv(get)].
    - [Mnw_si si], the no-wait client ([Mnw_si_unfold]):
      [SB c ↦ Future (Inc c) (λf. Future (Get (other c)) (λg. Wait g
      (λr. Wait f (λ_. Ret r))))].  Both futures are issued before
      either is awaited; the [Get]'s tag is empty unless the [Inc] was
      resolved early, so it is ordered after the [Inc] only by (F2),
      i.e. only when [~ si (Inc c) (Get (other c))].
    Both are defined for every relation [si] of the counters' signature
    [CxySig si]; [FC = CxySig by_counter], [F0 = CxySig ∅]
    ([RelaxedHoareCounterXY]).

    ** Results (Rocq 9.3.0; every lemma, theorem and corollary of this
       file, 77 in total, is "Closed under the global context": no
       [classic], no [eq_rect_eq])

    - Method traces, by first-order views computed by [match] ([fut_op],
      [fut_next], [wait_hop], [wait_next], [is_ret]), in the style of
      [RelaxedHoareCompLin.cc_trace]: a step is destructed while its
      source configuration is a variable, so no dependent equality on
      [Wait (MkFutureRef op h) k] is inverted; all arities are [nat], so
      results are compared as [nat]s ([cell_val], projections).
      - [mcl_trace] (the planned statement): a trace of [Mcl_si si (SB c)]
        with result [r] is exactly [inv h1 (Inc c) D1; res h1 (Inc c) r1;
        inv h2 (Get (other c)) D2; res h2 (Get (other c)) r] with
        [h1 ≠ h2] and [D2 h1].
      - [mnw_trace]: a trace of [Mnw_si si (SB c)] is [I1; I2; R2; R1],
        [I1; I2; R1; R2] or [I1; R1; I2; R2] (the [Inc]'s response may
        come early), with the [Get]'s response carrying [r].
      - [mcl_produces], [mnw_produces]: the forward direction for
        concrete handles.
    - Generic module-execution facts (any [VE], any [M]):
      [exec_underlay_nodup] (underlay invocation keys of an execution
      from an initial configuration are pairwise distinct, from
      [trace_fresh]); [ucount], [ucount_nth], [ucount_lt] (module
      positions to underlay positions); [in_overlay_ierase];
      [iexec_over_res] (a returned call's result is the one its body
      committed to, compared through [ResEv] equalities);
      [returned_emitted] (a returned call has emitted every event of its
      body: [ii_returned_done], [ii_partition]); [forced] (a chain of
      (F1)--(F3) edges inside one method trace) and [forced_order] (such
      events are emitted in that order: [ii_order]).
    - The EI path ([EIInv], [ei_res_source], [get0_before_inc]): along a
      path of [EI δcxy] from [(s00, [])], counter [c] equals the number
      of [Inc c] invocations so far, and a [Get c'] that returns 0
      precedes every [Inc c'] invocation (with unique invocation keys).
      [ei_sb_cycle_gen] (any [si]) and [ei_sb_cycle] (the planned
      statement, [FC]): [inc_x < get_y < inc_y < get_x < inc_x] is
      impossible.  Pure specification reasoning.
    - [SBShape M]: each call [SB c] invokes [Inc c] and [Get (other c)],
      the [Get] answers the call's result, and the [Inc] invocation is
      [forced] before the [Get] invocation.  [sb_cycle_of_shape]: then
      no trace of [M] over [EI δcxy] has an [SB CX] and an [SB CY] that
      both return 0.  [mcl_shape] (every [si]; chain inv(inc) →(F1)
      res(inc) →(F3) inv(get); no (F2), so the same-thread case needs no
      separate argument); [mnw_shape] (when [forall c, ~ si (Inc c)
      (Get (other c))]; the single (F2) edge).
    - [sb_client_spec] (the planned statement) and [sb_client_spec_gen]
      (every [si]); [sb_nowait_safe_gen].
    - Executions built from [tagged_invoke], [tagged_underlay] and
      [tagged_return] over the plain [EI δcxy]: [sb_nowait_00_gen] (if
      both pairs [(Inc CX, Get CY)], [(Inc CY, Get CX)] are
      semi-independent, the no-wait client reaches (0, 0): each [Get]
      invocation overtakes its own thread's pending [Inc] invocation);
      [sb_spec_live_gen], [sb_spec_live] (non-vacuity: the waiting
      client's two calls both return, with (0, 1)).
    - [sb_nowait_si_decides] (the planned statement): under [by_counter]
      the no-wait client reaches (0, 0); under SI = ∅ ([F0]) no trace
      does.  [sb_wait_decides]: under the same [by_counter]
      specification, the waiting client never reaches (0, 0) and the
      no-wait client can.

    ** K / S / P / R

    - K: the kernel checked every statement above; all closed.
    - S: [sb_client_spec s k1 k2]: for every overlay trace [s] of every
      execution of [Mcl_si by_counter] over [EI δcxy] from [(s00, [])]
      ([MTraces]: any finite execution, complete or not, any number of
      calls on any threads, overlapping calls of one thread allowed),
      and for all keys [k1], [k2] (possibly of the same thread), [s]
      does not contain both [res (SB CX) 0] at [k1] and [res (SB CY) 0]
      at [k2].  The underlay is the counters' specification, not an
      implementation and not a memory model.  The property is one
      outcome excluded, not a full specification of the client (the
      client's own signature carries no specification here).
    - P: the paper prints no client theorem (RLHL-3c plan, row T7).
      Closest printed text: intro.tex:28 ("a data or control dependency
      forces the dependent operation to wait") and intro.tex:70 ("The
      client can then use the resulting abstraction in the next
      verification layer").  Author response B4
      (popl2027-reviews.md:531-533): "reason from an object's contract
      and use a contextual refinement result to transfer the property to
      an implementation"; this file is the "reason from the contract"
      half, for Counter_xy; the transfer is part 2.
    - R: Reviewer B (popl2027-reviews.md:313-316): "the program logic,
      its soundness proof against a weak memory model such as RC11, and
      the verification of a concurrent object alongside the verification
      of its client program"; :214: "No demonstration that the proposed
      relaxed linearizability and program logic are useful for
      nontrivial client verification"; meta-review :615: "the lack of a
      demonstration of client verification"; latest-review B-1 (client
      missing) and M-22 (plan item 5, iteration-log:461: "an
      SB-with-Wait client of Counter_xy").
    - Gaps K/S vs P/R:
      - not linked to the implementation yet (part 2, M-22);
      - no RC11: Counter_xy is a renaming object (each counter operation
        is one memory operation; latest-review B-1 (4′)) over the SC
        cell [δmem] with COH-style semi-independence ([by_location]),
        not RC11; and this file does not even use that cell;
      - this is not the SeqLock a=b client promised in author response
        B4 (popl2027-reviews.md:531-533), and not Reviewer B's
        "nontrivial client" (:214);
      - the client is verified by a direct argument on the module
        semantics (decision D4 (a) of the RLHL-3c plan: a semantic
        theorem), not by an RLHL derivation for the client.

    ** Provisional research-level choices (research-intent §7, RLHL-3c
       plan "Research-level decisions"; not yet decided by the author)

    - D1 (semantic layering, [ModLTS]): not used here; the spec-level
      theorem does not depend on it.  Part 2 will compose through
      [ModLTS].
    - D2 (saturation only on the E-side, over [CCClosed] presentations):
      the theorem is stated over the plain [EI δcxy] from an empty
      pending list, the presentation for which E-side absorption is
      planned ([ei_ccclosed]); part 2 depends on it.
    - D3 (verimpl in copy-cat form): part 2 is to transfer through
      copy-cat inclusion ([cxy_complin_ei], [CCRefines]), not through
      [rel_lin]; nothing here uses [rel_lin].
    Also D4 (a) (semantic client theorem now, SeqLock later) and D6 (all
    executions): this file holds for every execution, complete or not.

    ** Deviations from the plan's statements

    - [mcl_trace], [ei_sb_cycle], [sb_client_spec],
      [sb_nowait_si_decides]: the planned statements, unchanged; each is
      derived from a stronger generic version ([si] arbitrary, or a
      generic [SBShape] client).
    - [mnw_trace]: the plan gives no statement; the three shapes above.
    - The "ucount position lemmas" are stated over module event lists
      ([map ierase IT]) rather than over the instrumented trace.
    - Additions beyond the plan: [SBShape]/[sb_cycle_of_shape],
      [sb_nowait_safe_gen], [sb_spec_live], [sb_wait_decides].

    ** Known limitations

    - [sb_nowait_si_decides] compares two underlay signatures ([FC],
      [F0]) under one program text, one [δcxy] and one [EI]: the module
      semantics reads only the underlay relation
      ([RelaxedModuleSemantics.must_precede]).
    - [sb_nowait_00_gen] assumes both cross pairs are semi-independent
      and [sb_nowait_safe_gen] assumes neither is; the mixed case (by
      hand: (0, 0) is still reachable) is not mechanized.
    - The [Get]'s value is taken at its invocation (EI); this is the
      specification of [RelaxedHoareCounterXY], not a weak-memory read. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Sorting.Permutation.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedModuleFacts.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.ViewLHL.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import examples.Relaxed.RelaxedHoareCounterXY.

Import ListNotations.


Module RelaxedHoareClientSB.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedModuleFacts.
  Import RelaxedGSim.
  Import RelaxedHoareCompLin.
  Import RelaxedHoareCounterXY.

  (** ** The client signature and the two clients *)

  Definition other (c : CLoc) : CLoc := match c with CX => CY | CY => CX end.

  Lemma other_ne c : other c <> c.
  Proof. destruct c; discriminate. Qed.

  (** [SB c]: increment counter [c], then read the other counter. *)
  Inductive SBOp : Type := SB (c : CLoc).

  Definition sb_ar (_ : SBOp) : Type := nat.

  Canonical Structure SBEff : Sig.t := {| Sig.op := SBOp; Sig.ar := sb_ar |}.

  (** The client's own signature: handles [nat], no semi-independence,
      every mode [Local]. *)
  Definition GS : RelaxedSig.t :=
    {|
      RelaxedSig.effect := SBEff;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := fun _ _ => False;
      RelaxedSig.mode := fun _ => Local;
    |}.

  Lemma GS_wf : RelaxedSig.well_formed GS.
  Proof. constructor; [intros o H; exact H | intros _ _ [] | intros _ _ []]. Qed.

  Section Clients.
    Context (si : COp -> COp -> Prop).
    Local Abbreviation F := (CxySig si).

    (** The waiting client: the [Get] is issued after the [Inc] has
        returned (the untagged [Future] after the [Wait] is tagged with
        the [Inc]'s handle, so (F3) orders them). *)
    Definition cl_get (c : CLoc) : Prog F nat :=
      @Future F nat (Get (other c)) (fun g => Wait g (fun r => Ret r)).

    Definition sbw (c : CLoc) : Prog F nat :=
      @Future F nat (Inc c) (fun f => Wait f (fun _ => cl_get c)).

    Definition Mcl_si : RelaxedModuleImpl F GS :=
      fun o _ => match o as o0 return Prog F (Sig.ar o0) with SB c => sbw c end.

    Lemma Mcl_si_unfold c t :
      Mcl_si (SB c) t =
      @Future F nat (Inc c) (fun f => Wait f (fun _ => @Future F nat (Get (other c)) (fun g => Wait g (fun r => Ret r)))).
    Proof. reflexivity. Qed.

    (** The no-wait client: both futures are issued before either is
        awaited; the [Get] is untagged, but at its invocation nothing has
        been awaited, so it is ordered after the [Inc] only by (F2). *)
    Definition nw_get (c : CLoc) (f : FutureRef F nat) : Prog F nat :=
      @Future F nat (Get (other c)) (fun g => Wait g (fun r => Wait f (fun _ => Ret r))).

    Definition snw (c : CLoc) : Prog F nat :=
      @Future F nat (Inc c) (fun f => nw_get c f).

    Definition Mnw_si : RelaxedModuleImpl F GS :=
      fun o _ => match o as o0 return Prog F (Sig.ar o0) with SB c => snw c end.

    Lemma Mnw_si_unfold c t :
      Mnw_si (SB c) t =
      @Future F nat (Inc c) (fun f => @Future F nat (Get (other c)) (fun g => Wait g (fun r => Wait f (fun _ => Ret r)))).
    Proof. reflexivity. Qed.
  End Clients.

  (** ** Every method trace of the two clients

      The programs are read through first-order views computed by
      [match] ([fut_op], [fut_next], [wait_hop], [wait_next], [is_ret]),
      as in [RelaxedHoareCompLin.cc_trace]: a step is destructed while
      its source configuration is a variable, so no dependent equality
      on [Wait (MkFutureRef op h) k] is ever inverted (no [eq_rect_eq]).
      All arities of [CxySig si] are [nat], so results are compared as
      [nat]s. *)

  Section Traces.
    Context (si : COp -> COp -> Prop) (t : tid).
    Local Abbreviation F := (CxySig si).
    Local Abbreviation PC := (ProgramConfig F nat).

    Definition fut_op (p : Prog F nat) : option COp :=
      match p with Future o _ => Some o | _ => None end.

    Definition fut_next (p : Prog F nat) (h : nat) : option (Prog F nat) :=
      match p with Future o k => Some (k (MkFutureRef o h)) | _ => None end.

    Definition wait_hop (p : Prog F nat) : option (nat * COp) :=
      match p with Wait f _ => Some (future_handle f, future_op f) | _ => None end.

    Definition wait_next (p : Prog F nat) (x : nat) : option (Prog F nat) :=
      match p with
      | Wait f k =>
          match f in FutureRef _ A return (A -> Prog F nat) -> option (Prog F nat) with
          | MkFutureRef o h => fun k => Some (k x)
          end k
      | _ => None
      end.

    Definition is_ret (p : Prog F nat) : option nat :=
      match p with Ret y => Some y | _ => None end.

    Definition cell_val (c : FutureCell F) : nat :=
      match c with Resolved _ v => v | Pending _ => 0 end.

    Definition cell_pending (c : FutureCell F) : bool :=
      match c with Pending _ => true | Resolved _ _ => false end.

    (** The tagged events of a method trace. *)
    Definition ti (h : nat) (o : COp) (D : nat -> Prop) : TaggedEvent F :=
      Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h o)) D.
    Definition tr_ (h : nat) (o : COp) (r : nat) : TaggedEvent F :=
      Build_TaggedEvent (Build_ThreadEvent t (@ResEv F h o r)) no_deps.

    (** *** One step from each kind of program *)

    Lemma step_future a (c c' : PC) :
      program_step_tagged t a c c' -> fut_op (pc_prog c) <> None ->
      (exists o h, fut_op (pc_prog c) = Some o /\ @handle_fresh F h (pc_futures c) /\
         a = TEmit (ti h o (resolved_in (pc_futures c))) /\
         fut_next (pc_prog c) h = Some (pc_prog c') /\ pc_futures c' = @add_pending F h o (pc_futures c)) \/
      (exists o h (ret : nat), a = TEmit (tr_ h o ret) /\
         @resolve_store F h o ret (pc_futures c) (pc_futures c') /\ pc_prog c' = pc_prog c).
    Proof.
      intros Hs Hf.
      destruct Hs as [o k h H Hfr | o d k h H Hfr | o h ret k H Hr | o h ret k H H' Hr | o h ret p H H' Hr | p H];
        cbn in Hf |- *; try (exfalso; apply Hf; reflexivity).
      - left. exists o, h. repeat split; auto.
      - right. exists o, h, ret. repeat split; auto.
    Qed.

    Lemma step_wait a (c c' : PC) h0 o0 :
      program_step_tagged t a c c' -> wait_hop (pc_prog c) = Some (h0, o0) ->
      (exists ret : nat, a = TSilent /\ @resolved_at F h0 o0 ret (pc_futures c) /\
         wait_next (pc_prog c) ret = Some (pc_prog c') /\ pc_futures c' = pc_futures c) \/
      (exists ret : nat, a = TEmit (tr_ h0 o0 ret) /\ @resolve_store F h0 o0 ret (pc_futures c) (pc_futures c') /\
         wait_next (pc_prog c) ret = Some (pc_prog c')) \/
      (exists o h (ret : nat), a = TEmit (tr_ h o ret) /\
         @resolve_store F h o ret (pc_futures c) (pc_futures c') /\ pc_prog c' = pc_prog c).
    Proof.
      intros Hs Hw.
      destruct Hs as [o k h H Hfr | o d k h H Hfr | o h ret k H Hr | o h ret k H H' Hr | o h ret p H H' Hr | p H];
        cbn in Hw |- *; try discriminate Hw.
      - injection Hw as <- <-. left. exists ret. auto.
      - injection Hw as <- <-. right; left. exists ret. auto.
      - right; right. exists o, h, ret. auto.
    Qed.

    Lemma step_ret a (c c' : PC) :
      program_step_tagged t a c c' -> is_ret (pc_prog c) <> None ->
      exists o h (ret : nat), a = TEmit (tr_ h o ret) /\
        @resolve_store F h o ret (pc_futures c) (pc_futures c') /\ pc_prog c' = pc_prog c.
    Proof.
      intros Hs Hr0.
      destruct Hs as [o k h H Hfr | o d k h H Hfr | o h ret k H Hr | o h ret k H H' Hr | o h ret p H H' Hr | p H];
        cbn in Hr0 |- *; try (exfalso; apply Hr0; reflexivity).
      exists o, h, ret. auto.
    Qed.

    Lemma exec_first (c c' : PC) tr :
      program_execution_tagged t c tr c' ->
      (c' = c /\ tr = []) \/
      (exists c2, program_step_tagged t TSilent c c2 /\ program_execution_tagged t c2 tr c') \/
      (exists m c2 tr', tr = m :: tr' /\ program_step_tagged t (TEmit m) c c2 /\
                        program_execution_tagged t c2 tr' c').
    Proof.
      intros Hex. destruct Hex as [c | c1 c2 c3 tr Hstep Hex | c1 c2 c3 m tr Hstep Hex].
      - left. auto.
      - right; left. exists c2. auto.
      - right; right. exists m, c2, tr. auto.
    Qed.

    Lemma terminal_prog (c : PC) r : program_terminal c r -> pc_prog c = Ret r.
    Proof. intros Ht. destruct Ht. reflexivity. Qed.

    (** *** Stores *)

    Lemma resolve_store_cons h o (ret : nat) e (H H' : FutureStore F) :
      @resolve_store F h o ret (e :: H) H' ->
      (e = @Build_FutureEntry F h (@Pending F o) /\ H' = @Build_FutureEntry F h (@Resolved F o ret) :: H) \/
      (exists H'', fe_handle F e <> h /\ @resolve_store F h o ret H H'' /\ H' = e :: H'').
    Proof.
      intros Hr. inversion Hr as [tail | h' cell H1 H1' Hneq Hres]; subst.
      - left. auto.
      - right. exists H1'. auto.
    Qed.

    Lemma resolve_store_nil h o (ret : nat) (H' : FutureStore F) : ~ @resolve_store F h o ret [] H'.
    Proof. intros Hr. inversion Hr. Qed.

    Lemma pend_eq (h h' : nat) (o o' : COp) :
      @Build_FutureEntry F h (@Pending F o) = @Build_FutureEntry F h' (@Pending F o') -> h = h' /\ o = o'.
    Proof. intros Heq. injection Heq. auto. Qed.

    Lemma pend_res (h h' : nat) (o o' : COp) (x : nat) : @Build_FutureEntry F h (@Pending F o) <> @Build_FutureEntry F h' (@Resolved F o' x).
    Proof. intros Heq. apply (f_equal (fun e => cell_pending (fe_cell F e))) in Heq. discriminate Heq. Qed.

    Lemma res_eq (h h' : nat) (o o' : COp) (x x' : nat) :
      @Build_FutureEntry F h (@Resolved F o x) = @Build_FutureEntry F h' (@Resolved F o' x') -> h = h' /\ x = x'.
    Proof.
      intros Heq. split; [exact (f_equal (fe_handle F) Heq) | exact (f_equal (fun e => cell_val (fe_cell F e)) Heq)].
    Qed.

    (** A store with no pending entry admits no [resolve_store]. *)
    Definition no_pending (H : FutureStore F) : Prop :=
      forall e, In e H -> cell_pending (fe_cell F e) = false.

    Lemma resolve_no_pending h o (ret : nat) (H H' : FutureStore F) :
      no_pending H -> ~ @resolve_store F h o ret H H'.
    Proof.
      intros Hn Hr. pose proof (Hn _ (resolve_store_in _ _ _ _ _ Hr)) as Hc. discriminate Hc.
    Qed.

    Lemma no_pending_2 h1 o1 (x1 : nat) h2 o2 (x2 : nat) :
      no_pending [@Build_FutureEntry F h1 (@Resolved F o1 x1); @Build_FutureEntry F h2 (@Resolved F o2 x2)].
    Proof. intros e [<- | [<- | []]]; reflexivity. Qed.

    Lemma no_pending_1 h1 o1 (x1 : nat) : no_pending [@Build_FutureEntry F h1 (@Resolved F o1 x1)].
    Proof. intros e [<- | []]; reflexivity. Qed.

    (** The [Ret] stage: nothing more happens. *)
    Lemma stage_ret (c c' : PC) tr r x :
      program_execution_tagged t c tr c' -> program_terminal c' r ->
      pc_prog c = Ret x -> no_pending (pc_futures c) -> tr = [] /\ r = x.
    Proof.
      intros Hex Hterm Hp Hn.
      destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & _) | (m & c2 & tr' & -> & Hs & _)]].
      - rewrite (terminal_prog _ _ Hterm) in Hp. injection Hp as ->. auto.
      - exfalso. destruct (step_ret _ _ _ Hs) as (o & h & ret & Ha & _); [rewrite Hp; discriminate | discriminate Ha].
      - exfalso. destruct (step_ret _ _ _ Hs) as (o & h & ret & _ & Hr & _); [rewrite Hp; discriminate |].
        exact (resolve_no_pending _ _ _ _ _ Hn Hr).
    Qed.

    (** *** The waiting client *)

    Section McL.
      Context (c : CLoc).
      Local Abbreviation oc := (other c).

      Definition Sget (h2 : nat) : Prog F nat := Wait (@MkFutureRef F (Get oc) h2) (fun r : nat => Ret r).
      Definition Sinc (h1 : nat) : Prog F nat := Wait (@MkFutureRef F (Inc c) h1) (fun _ : nat => cl_get si c).

      (** The [Get] has been awaited and resolved early. *)
      Lemma mcl_s3r (c0 c' : PC) tr r h1 h2 (r1 x : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r -> h2 <> h1 ->
        pc_prog c0 = Sget h2 ->
        pc_futures c0 = [@Build_FutureEntry F h2 (@Resolved F (Get oc) x); @Build_FutureEntry F h1 (@Resolved F (Inc c) r1)] ->
        tr = [] /\ r = x.
      Proof.
        intros Hex Hterm Hne Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & _ & Hres & Hn & Hst2) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | [Heq | []]].
          + destruct (res_eq _ _ _ _ _ _ Heq) as (_ & Hx). subst x.
            rewrite Hp in Hn. cbn in Hn. apply some_inj in Hn.
            refine (stage_ret _ _ _ _ _ Hex2 Hterm (eq_sym Hn) _). rewrite Hst2, Hst. apply no_pending_2.
          + destruct (res_eq _ _ _ _ _ _ Heq) as (Hh & _). congruence.
        - exfalso.
          destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & Ha & _) | [(ret & _ & Hr & _) | (o & h & ret & _ & Hr & _)]];
            [rewrite Hp; reflexivity | discriminate Ha | |]; rewrite Hst in Hr;
            exact (resolve_no_pending _ _ _ _ _ (no_pending_2 _ _ _ _ _ _) Hr).
      Qed.

      (** The [Get] is pending. *)
      Lemma mcl_s3 (c0 c' : PC) tr r h1 h2 (r1 : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r -> h2 <> h1 ->
        pc_prog c0 = Sget h2 ->
        pc_futures c0 = [@Build_FutureEntry F h2 (@Pending F (Get oc)); @Build_FutureEntry F h1 (@Resolved F (Inc c) r1)] ->
        tr = [tr_ h2 (Get oc) r].
      Proof.
        intros Hex Hterm Hne Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso.
          destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & _ & Hres & _) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | [Heq | []]];
            [exact (pend_res _ _ _ _ _ Heq) | destruct (res_eq _ _ _ _ _ _ Heq) as (Hh & _); congruence].
        - destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & Ha & _) | [(ret & Ha & Hr & Hn) | (o & h & ret & Ha & Hr & Hp2)]];
            [rewrite Hp; reflexivity | discriminate Ha | |].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(_ & Hst2) | (H'' & _ & Hr' & _)].
            * rewrite Hp in Hn. cbn in Hn. apply some_inj in Hn.
              destruct (stage_ret _ _ _ _ _ Hex2 Hterm (eq_sym Hn)) as (-> & ->);
                [rewrite Hst2; apply no_pending_2 | reflexivity].
            * exfalso. destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(Heq & _) | (H3 & _ & Hr3 & _)];
                [exact (pend_res _ _ _ _ _ (eq_sym Heq)) | exact (resolve_store_nil _ _ _ _ Hr3)].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & Hst2) | (H'' & _ & Hr' & _)].
            * apply pend_eq in Heq as (<- & <-).
              destruct (mcl_s3r _ _ _ _ h1 h2 r1 ret Hex2 Hterm Hne) as (-> & ->);
                [rewrite Hp2; exact Hp | exact Hst2 | reflexivity].
            * exfalso. destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(Heq & _) | (H3 & _ & Hr3 & _)];
                [exact (pend_res _ _ _ _ _ (eq_sym Heq)) | exact (resolve_store_nil _ _ _ _ Hr3)].
      Qed.

      (** The [Get] is about to be issued, after the [Inc] resolved. *)
      Lemma mcl_s2 (c0 c' : PC) tr r h1 (r1 : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r ->
        pc_prog c0 = cl_get si c -> pc_futures c0 = [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)] ->
        exists h2, h2 <> h1 /\
          tr = [ti h2 (Get oc) (resolved_in [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]); tr_ h2 (Get oc) r].
      Proof.
        intros Hex Hterm Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso. destruct (step_future _ _ _ Hs) as [(o & h & _ & _ & Ha & _) | (o & h & ret & Ha & _)];
            [rewrite Hp; discriminate | discriminate Ha | discriminate Ha].
        - destruct (step_future _ _ _ Hs) as [(o & h2 & Ho & Hfr & Ha & Hn & Hst2) | (o & h & ret & _ & Hr & _)];
            [rewrite Hp; discriminate | |].
          + rewrite Hp in Ho, Hn. cbn in Ho, Hn. injection Ho as <-. apply some_inj in Hn.
            assert (Hne : h2 <> h1).
            { intros ->. apply Hfr. rewrite Hst. left. reflexivity. }
            exists h2. split; [exact Hne |]. injection Ha as ->. rewrite Hst.
            rewrite (mcl_s3 _ _ _ _ h1 h2 r1 Hex2 Hterm Hne (eq_sym Hn)); [reflexivity |].
            rewrite Hst2, Hst. reflexivity.
          + exfalso. rewrite Hst in Hr. exact (resolve_no_pending _ _ _ _ _ (no_pending_1 _ _ _) Hr).
      Qed.

      (** The [Inc] has been awaited and resolved early. *)
      Lemma mcl_s1r (c0 c' : PC) tr r h1 (r1 : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r ->
        pc_prog c0 = Sinc h1 -> pc_futures c0 = [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)] ->
        exists h2, h2 <> h1 /\
          tr = [ti h2 (Get oc) (resolved_in [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]); tr_ h2 (Get oc) r].
      Proof.
        intros Hex Hterm Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & _ & _ & Hn & Hst2) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hp in Hn. cbn in Hn. apply some_inj in Hn.
          refine (mcl_s2 _ _ _ _ _ _ Hex2 Hterm (eq_sym Hn) _). rewrite Hst2. exact Hst.
        - exfalso.
          destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & Ha & _) | [(ret & _ & Hr & _) | (o & h & ret & _ & Hr & _)]];
            [rewrite Hp; reflexivity | discriminate Ha | |]; rewrite Hst in Hr;
            exact (resolve_no_pending _ _ _ _ _ (no_pending_1 _ _ _) Hr).
      Qed.

      (** The [Inc] is pending. *)
      Lemma mcl_s1 (c0 c' : PC) tr r h1 :
        program_execution_tagged t c0 tr c' -> program_terminal c' r ->
        pc_prog c0 = Sinc h1 -> pc_futures c0 = [@Build_FutureEntry F h1 (@Pending F (Inc c))] ->
        exists (r1 : nat) h2, h2 <> h1 /\
          tr = [tr_ h1 (Inc c) r1; ti h2 (Get oc) (resolved_in [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]);
                tr_ h2 (Get oc) r].
      Proof.
        intros Hex Hterm Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso.
          destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & _ & Hres & _) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | []]. exact (pend_res _ _ _ _ _ Heq).
        - destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & Ha & _) | [(ret & Ha & Hr & Hn) | (o & h & ret & Ha & Hr & Hp2)]];
            [rewrite Hp; reflexivity | discriminate Ha | |].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(_ & Hst2) | (H'' & _ & Hr' & _)];
              [| exfalso; exact (resolve_store_nil _ _ _ _ Hr')].
            rewrite Hp in Hn. cbn in Hn. apply some_inj in Hn.
            destruct (mcl_s2 _ _ _ _ h1 ret Hex2 Hterm (eq_sym Hn) Hst2) as (h2 & Hne & ->).
            exists ret, h2. auto.
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & Hst2) | (H'' & _ & Hr' & _)];
              [| exfalso; exact (resolve_store_nil _ _ _ _ Hr')].
            apply pend_eq in Heq as (<- & <-).
            destruct (mcl_s1r _ _ _ _ h1 ret Hex2 Hterm) as (h2 & Hne & ->); [rewrite Hp2; exact Hp | exact Hst2 |].
            exists ret, h2. auto.
      Qed.
    End McL.

    (** [mcl_trace]: a trace of the waiting client is [inv(inc_c)],
        [res(inc_c)], [inv(get_{other c})] tagged with the [Inc]'s handle,
        [res(get)] with the call's result. *)
    Theorem mcl_trace c tr (r : nat) :
      program_produces_tagged t (Mcl_si si (SB c) t) tr r ->
      exists h1 h2 (r1 : nat) D1 D2, h1 <> h2 /\ D2 h1 /\
        tr = [Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h1 (Inc c))) D1;
              Build_TaggedEvent (Build_ThreadEvent t (@ResEv F h1 (Inc c) r1)) no_deps;
              Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h2 (Get (other c)))) D2;
              Build_TaggedEvent (Build_ThreadEvent t (@ResEv F h2 (Get (other c)) r)) no_deps].
    Proof.
      intros (c' & Hex & Hterm). unfold initial_program in Hex.
      destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
      - pose proof (terminal_prog _ _ Hterm) as Hp. discriminate Hp.
      - exfalso. destruct (step_future _ _ _ Hs) as [(o & h & _ & _ & Ha & _) | (o & h & ret & Ha & _)];
          [cbn; discriminate | discriminate Ha | discriminate Ha].
      - destruct (step_future _ _ _ Hs) as [(o & h1 & Ho & _ & Ha & Hn & Hst) | (o & h & ret & _ & Hr & _)];
          [cbn; discriminate | |].
        + cbn in Ho, Hn, Hst. injection Ho as <-. apply some_inj in Hn.
          destruct (mcl_s1 c _ _ _ _ h1 Hex2 Hterm (eq_sym Hn) Hst) as (r1 & h2 & Hne & ->).
          injection Ha as ->.
          exists h1, h2, r1, (resolved_in (@empty_store F)),
            (resolved_in [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]).
          split; [intros ->; exact (Hne eq_refl) |]. split; [| reflexivity].
          exists (Inc c), r1. left. reflexivity.
        + exfalso. exact (resolve_store_nil _ _ _ _ Hr).
    Qed.

    (** *** The no-wait client *)

    Section MnW.
      Context (c : CLoc).
      Local Abbreviation oc := (other c).

      Definition N2 (h1 h2 : nat) : Prog F nat :=
        Wait (@MkFutureRef F (Get oc) h2) (fun r : nat => Wait (@MkFutureRef F (Inc c) h1) (fun _ : nat => Ret r)).
      Definition N3 (h1 : nat) (x : nat) : Prog F nat :=
        Wait (@MkFutureRef F (Inc c) h1) (fun _ : nat => Ret x).

      (** The [Inc] is awaited last, after the [Get] has returned. *)
      Lemma nw_s3r (c0 c' : PC) tr r h1 (x : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r ->
        pc_prog c0 = N3 h1 x -> no_pending (pc_futures c0) -> tr = [] /\ r = x.
      Proof.
        intros Hex Hterm Hp Hn.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & _ & _ & Hw & Hst2) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hp in Hw. cbn in Hw. apply some_inj in Hw.
          refine (stage_ret _ _ _ _ _ Hex2 Hterm (eq_sym Hw) _). rewrite Hst2. exact Hn.
        - exfalso.
          destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & Ha & _) | [(ret & _ & Hr & _) | (o & h & ret & _ & Hr & _)]];
            [rewrite Hp; reflexivity | discriminate Ha | |]; exact (resolve_no_pending _ _ _ _ _ Hn Hr).
      Qed.

      Lemma nw_s3p (c0 c' : PC) tr r h1 h2 (x x' : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r -> h2 <> h1 ->
        pc_prog c0 = N3 h1 x ->
        pc_futures c0 = [@Build_FutureEntry F h2 (@Resolved F (Get oc) x'); @Build_FutureEntry F h1 (@Pending F (Inc c))] ->
        exists r1 : nat, tr = [tr_ h1 (Inc c) r1] /\ r = x.
      Proof.
        intros Hex Hterm Hne Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso.
          destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & _ & Hres & _) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | [Heq | []]];
            [destruct (res_eq _ _ _ _ _ _ Heq) as (Hh & _); congruence | exact (pend_res _ _ _ _ _ Heq)].
        - destruct (step_wait _ _ _ h1 (Inc c) Hs) as [(ret & Ha & _) | [(ret & Ha & Hr & Hw) | (o & h & ret & Ha & Hr & Hp2)]];
            [rewrite Hp; reflexivity | discriminate Ha | |].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & _) | (H'' & _ & Hr' & Hst2)];
              [exfalso; exact (pend_res _ _ _ _ _ (eq_sym Heq)) |].
            destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(_ & ->) | (H3 & _ & Hr3 & _)];
              [| exfalso; exact (resolve_store_nil _ _ _ _ Hr3)].
            rewrite Hp in Hw. cbn in Hw. apply some_inj in Hw.
            destruct (stage_ret _ _ _ _ _ Hex2 Hterm (eq_sym Hw)) as (-> & ->);
              [rewrite Hst2; apply no_pending_2 | exists ret; auto].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & _) | (H'' & _ & Hr' & Hst2)];
              [exfalso; exact (pend_res _ _ _ _ _ (eq_sym Heq)) |].
            destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(Heq & ->) | (H3 & _ & Hr3 & _)];
              [| exfalso; exact (resolve_store_nil _ _ _ _ Hr3)].
            apply pend_eq in Heq as (<- & <-).
            destruct (nw_s3r _ _ _ _ h1 x Hex2 Hterm) as (-> & ->);
              [rewrite Hp2; exact Hp | rewrite Hst2; apply no_pending_2 | exists ret; auto].
      Qed.

      (** Both futures issued; the four store situations at the [Wait] on
          the [Get]. *)
      Lemma nw_s2rr (c0 c' : PC) tr r h1 h2 (x r1 : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r -> h2 <> h1 ->
        pc_prog c0 = N2 h1 h2 ->
        pc_futures c0 = [@Build_FutureEntry F h2 (@Resolved F (Get oc) x); @Build_FutureEntry F h1 (@Resolved F (Inc c) r1)] ->
        tr = [] /\ r = x.
      Proof.
        intros Hex Hterm Hne Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & _ & Hres & Hw & Hst2) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | [Heq | []]];
            [| destruct (res_eq _ _ _ _ _ _ Heq) as (Hh & _); congruence].
          destruct (res_eq _ _ _ _ _ _ Heq) as (_ & Hx). subst x.
          rewrite Hp in Hw. cbn in Hw. apply some_inj in Hw.
          refine (nw_s3r _ _ _ _ h1 ret Hex2 Hterm (eq_sym Hw) _). rewrite Hst2, Hst. apply no_pending_2.
        - exfalso.
          destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & Ha & _) | [(ret & _ & Hr & _) | (o & h & ret & _ & Hr & _)]];
            [rewrite Hp; reflexivity | discriminate Ha | |]; rewrite Hst in Hr;
            exact (resolve_no_pending _ _ _ _ _ (no_pending_2 _ _ _ _ _ _) Hr).
      Qed.

      Lemma nw_s2pr (c0 c' : PC) tr r h1 h2 (r1 : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r -> h2 <> h1 ->
        pc_prog c0 = N2 h1 h2 ->
        pc_futures c0 = [@Build_FutureEntry F h2 (@Pending F (Get oc)); @Build_FutureEntry F h1 (@Resolved F (Inc c) r1)] ->
        tr = [tr_ h2 (Get oc) r].
      Proof.
        intros Hex Hterm Hne Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso.
          destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & _ & Hres & _) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | [Heq | []]];
            [exact (pend_res _ _ _ _ _ Heq) | destruct (res_eq _ _ _ _ _ _ Heq) as (Hh & _); congruence].
        - destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & Ha & _) | [(ret & Ha & Hr & Hw) | (o & h & ret & Ha & Hr & Hp2)]];
            [rewrite Hp; reflexivity | discriminate Ha | |].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(_ & Hst2) | (H'' & _ & Hr' & _)];
              [| exfalso; destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(Heq & _) | (H3 & _ & Hr3 & _)];
                 [exact (pend_res _ _ _ _ _ (eq_sym Heq)) | exact (resolve_store_nil _ _ _ _ Hr3)]].
            rewrite Hp in Hw. cbn in Hw. apply some_inj in Hw.
            destruct (nw_s3r _ _ _ _ h1 ret Hex2 Hterm (eq_sym Hw)) as (-> & ->);
              [rewrite Hst2; apply no_pending_2 | reflexivity].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & Hst2) | (H'' & _ & Hr' & _)];
              [| exfalso; destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(Heq & _) | (H3 & _ & Hr3 & _)];
                 [exact (pend_res _ _ _ _ _ (eq_sym Heq)) | exact (resolve_store_nil _ _ _ _ Hr3)]].
            apply pend_eq in Heq as (<- & <-).
            destruct (nw_s2rr _ _ _ _ h1 h2 ret r1 Hex2 Hterm Hne) as (-> & ->);
              [rewrite Hp2; exact Hp | exact Hst2 | reflexivity].
      Qed.

      Lemma nw_s2rp (c0 c' : PC) tr r h1 h2 (x : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r -> h2 <> h1 ->
        pc_prog c0 = N2 h1 h2 ->
        pc_futures c0 = [@Build_FutureEntry F h2 (@Resolved F (Get oc) x); @Build_FutureEntry F h1 (@Pending F (Inc c))] ->
        exists r1 : nat, tr = [tr_ h1 (Inc c) r1] /\ r = x.
      Proof.
        intros Hex Hterm Hne Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & _ & Hres & Hw & Hst2) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | [Heq | []]];
            [| exfalso; exact (pend_res _ _ _ _ _ Heq)].
          destruct (res_eq _ _ _ _ _ _ Heq) as (_ & Hx). subst x.
          rewrite Hp in Hw. cbn in Hw. apply some_inj in Hw.
          exact (nw_s3p _ _ _ _ h1 h2 ret ret Hex2 Hterm Hne (eq_sym Hw) (eq_trans Hst2 Hst)).
        - destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & Ha & _) | [(ret & Ha & Hr & Hw) | (o & h & ret & Ha & Hr & Hp2)]];
            [rewrite Hp; reflexivity | discriminate Ha | |].
          + exfalso. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & _) | (H'' & Hh & _ & _)];
              [exact (pend_res _ _ _ _ _ (eq_sym Heq)) | exact (Hh eq_refl)].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & _) | (H'' & _ & Hr' & Hst2)];
              [exfalso; exact (pend_res _ _ _ _ _ (eq_sym Heq)) |].
            destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(Heq & ->) | (H3 & _ & Hr3 & _)];
              [| exfalso; exact (resolve_store_nil _ _ _ _ Hr3)].
            apply pend_eq in Heq as (<- & <-).
            destruct (nw_s2rr _ _ _ _ h1 h2 x ret Hex2 Hterm Hne) as (-> & ->);
              [rewrite Hp2; exact Hp | exact Hst2 | exists ret; auto].
      Qed.

      Lemma nw_s2pp (c0 c' : PC) tr r h1 h2 :
        program_execution_tagged t c0 tr c' -> program_terminal c' r -> h2 <> h1 ->
        pc_prog c0 = N2 h1 h2 ->
        pc_futures c0 = [@Build_FutureEntry F h2 (@Pending F (Get oc)); @Build_FutureEntry F h1 (@Pending F (Inc c))] ->
        exists r1 : nat, tr = [tr_ h2 (Get oc) r; tr_ h1 (Inc c) r1] \/ tr = [tr_ h1 (Inc c) r1; tr_ h2 (Get oc) r].
      Proof.
        intros Hex Hterm Hne Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso.
          destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & _ & Hres & _) | [(ret & Ha & _) | (o & h & ret & Ha & _)]];
            [rewrite Hp; reflexivity | | discriminate Ha | discriminate Ha].
          rewrite Hst in Hres. destruct Hres as [Heq | [Heq | []]]; exact (pend_res _ _ _ _ _ Heq).
        - destruct (step_wait _ _ _ h2 (Get oc) Hs) as [(ret & Ha & _) | [(ret & Ha & Hr & Hw) | (o & h & ret & Ha & Hr & Hp2)]];
            [rewrite Hp; reflexivity | discriminate Ha | |].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(_ & Hst2) | (H'' & Hh & _ & _)];
              [| exfalso; exact (Hh eq_refl)].
            rewrite Hp in Hw. cbn in Hw. apply some_inj in Hw.
            destruct (nw_s3p _ _ _ _ h1 h2 ret ret Hex2 Hterm Hne (eq_sym Hw) Hst2) as (r1 & -> & ->).
            exists r1. left. reflexivity.
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & Hst2) | (H'' & _ & Hr' & Hst2)].
            * apply pend_eq in Heq as (<- & <-).
              destruct (nw_s2rp _ _ _ _ h1 h2 ret Hex2 Hterm Hne) as (r1 & -> & ->);
                [rewrite Hp2; exact Hp | exact Hst2 |].
              exists r1. left. reflexivity.
            * destruct (resolve_store_cons _ _ _ _ _ _ Hr') as [(Heq & ->) | (H3 & _ & Hr3 & _)];
                [| exfalso; exact (resolve_store_nil _ _ _ _ Hr3)].
              apply pend_eq in Heq as (<- & <-).
              rewrite (nw_s2pr _ _ _ _ h1 h2 ret Hex2 Hterm Hne); [| rewrite Hp2; exact Hp | exact Hst2].
              exists ret. right. reflexivity.
      Qed.

      (** The [Get] is about to be issued. *)
      Lemma nw_s1r (c0 c' : PC) tr r h1 (r1 : nat) :
        program_execution_tagged t c0 tr c' -> program_terminal c' r ->
        pc_prog c0 = nw_get si c (@MkFutureRef F (Inc c) h1) ->
        pc_futures c0 = [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)] ->
        exists h2, h2 <> h1 /\
          tr = [ti h2 (Get oc) (resolved_in [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]); tr_ h2 (Get oc) r].
      Proof.
        intros Hex Hterm Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso. destruct (step_future _ _ _ Hs) as [(o & h & _ & _ & Ha & _) | (o & h & ret & Ha & _)];
            [rewrite Hp; discriminate | discriminate Ha | discriminate Ha].
        - destruct (step_future _ _ _ Hs) as [(o & h2 & Ho & Hfr & Ha & Hn & Hst2) | (o & h & ret & _ & Hr & _)];
            [rewrite Hp; discriminate | |].
          + rewrite Hp in Ho, Hn. cbn in Ho, Hn. injection Ho as <-. apply some_inj in Hn.
            assert (Hne : h2 <> h1) by (intros ->; apply Hfr; rewrite Hst; left; reflexivity).
            exists h2. split; [exact Hne |]. injection Ha as ->. rewrite Hst.
            rewrite (nw_s2pr _ _ _ _ h1 h2 r1 Hex2 Hterm Hne (eq_sym Hn)); [reflexivity |].
            rewrite Hst2, Hst. reflexivity.
          + exfalso. rewrite Hst in Hr. exact (resolve_no_pending _ _ _ _ _ (no_pending_1 _ _ _) Hr).
      Qed.

      Lemma nw_s1p (c0 c' : PC) tr r h1 :
        program_execution_tagged t c0 tr c' -> program_terminal c' r ->
        pc_prog c0 = nw_get si c (@MkFutureRef F (Inc c) h1) ->
        pc_futures c0 = [@Build_FutureEntry F h1 (@Pending F (Inc c))] ->
        exists h2 (r1 : nat) D2, h2 <> h1 /\
          (tr = [ti h2 (Get oc) D2; tr_ h2 (Get oc) r; tr_ h1 (Inc c) r1] \/
           tr = [ti h2 (Get oc) D2; tr_ h1 (Inc c) r1; tr_ h2 (Get oc) r] \/
           tr = [tr_ h1 (Inc c) r1; ti h2 (Get oc) D2; tr_ h2 (Get oc) r]).
      Proof.
        intros Hex Hterm Hp Hst.
        destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
        - rewrite (terminal_prog _ _ Hterm) in Hp. discriminate Hp.
        - exfalso. destruct (step_future _ _ _ Hs) as [(o & h & _ & _ & Ha & _) | (o & h & ret & Ha & _)];
            [rewrite Hp; discriminate | discriminate Ha | discriminate Ha].
        - destruct (step_future _ _ _ Hs) as [(o & h2 & Ho & Hfr & Ha & Hn & Hst2) | (o & h & ret & Ha & Hr & Hp2)];
            [rewrite Hp; discriminate | |].
          + rewrite Hp in Ho, Hn. cbn in Ho, Hn. injection Ho as <-. apply some_inj in Hn.
            assert (Hne : h2 <> h1) by (intros ->; apply Hfr; rewrite Hst; left; reflexivity).
            injection Ha as ->.
            assert (Hst3 : pc_futures c2 =
                             [@Build_FutureEntry F h2 (@Pending F (Get oc)); @Build_FutureEntry F h1 (@Pending F (Inc c))])
              by (rewrite Hst2, Hst; reflexivity).
            destruct (nw_s2pp _ _ _ _ h1 h2 Hex2 Hterm Hne (eq_sym Hn) Hst3) as (r1 & [-> | ->]).
            * exists h2, r1, (resolved_in (pc_futures c0)). split; [exact Hne | left; reflexivity].
            * exists h2, r1, (resolved_in (pc_futures c0)). split; [exact Hne | right; left; reflexivity].
          + injection Ha as ->. rewrite Hst in Hr.
            destruct (resolve_store_cons _ _ _ _ _ _ Hr) as [(Heq & Hst2) | (H'' & _ & Hr' & _)];
              [| exfalso; exact (resolve_store_nil _ _ _ _ Hr')].
            apply pend_eq in Heq as (<- & <-).
            destruct (nw_s1r _ _ _ _ h1 ret Hex2 Hterm) as (h2 & Hne & ->); [rewrite Hp2; exact Hp | exact Hst2 |].
            exists h2, ret, (resolved_in [@Build_FutureEntry F h1 (@Resolved F (Inc c) ret)]).
            split; [exact Hne | right; right; reflexivity].
      Qed.
    End MnW.

    (** [mnw_trace]: a trace of the no-wait client invokes the [Inc]
        first; the [Get] is invoked second, or third after an early
        response of the [Inc]; the [Get]'s response carries the call's
        result. *)
    Theorem mnw_trace c tr (r : nat) :
      program_produces_tagged t (Mnw_si si (SB c) t) tr r ->
      exists h1 h2 (r1 : nat) D1 D2, h1 <> h2 /\
        let I1 := Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h1 (Inc c))) D1 in
        let I2 := Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h2 (Get (other c)))) D2 in
        let R1 := Build_TaggedEvent (Build_ThreadEvent t (@ResEv F h1 (Inc c) r1)) no_deps in
        let R2 := Build_TaggedEvent (Build_ThreadEvent t (@ResEv F h2 (Get (other c)) r)) no_deps in
        tr = [I1; I2; R2; R1] \/ tr = [I1; I2; R1; R2] \/ tr = [I1; R1; I2; R2].
    Proof.
      intros (c' & Hex & Hterm). unfold initial_program in Hex.
      destruct (exec_first _ _ _ Hex) as [(-> & ->) | [(c2 & Hs & Hex2) | (m & c2 & tr' & -> & Hs & Hex2)]].
      - pose proof (terminal_prog _ _ Hterm) as Hp. discriminate Hp.
      - exfalso. destruct (step_future _ _ _ Hs) as [(o & h & _ & _ & Ha & _) | (o & h & ret & Ha & _)];
          [cbn; discriminate | discriminate Ha | discriminate Ha].
      - destruct (step_future _ _ _ Hs) as [(o & h1 & Ho & _ & Ha & Hn & Hst) | (o & h & ret & _ & Hr & _)];
          [cbn; discriminate | |].
        + cbn in Ho, Hn, Hst. injection Ho as <-. apply some_inj in Hn.
          destruct (nw_s1p c _ _ _ _ h1 Hex2 Hterm (eq_sym Hn) Hst) as (h2 & r1 & D2 & Hne & Htr).
          injection Ha as ->.
          exists h1, h2, r1, (resolved_in (@empty_store F)), D2.
          split; [intros ->; exact (Hne eq_refl) |]. cbv zeta.
          destruct Htr as [-> | [-> | ->]]; auto.
        + exfalso. exact (resolve_store_nil _ _ _ _ Hr).
    Qed.

    (** *** Forward: the clients produce the traces above *)

    Lemma mcl_produces c h1 h2 (r1 r : nat) :
      h1 <> h2 ->
      program_produces_tagged t (Mcl_si si (SB c) t)
        [ti h1 (Inc c) (resolved_in (@empty_store F)); tr_ h1 (Inc c) r1;
         ti h2 (Get (other c)) (resolved_in [@Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]);
         tr_ h2 (Get (other c)) r] r.
    Proof.
      intros Hne.
      exists (Build_ProgramConfig (Ret r)
                [@Build_FutureEntry F h2 (@Resolved F (Get (other c)) r); @Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]).
      split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future F nat t (Inc c) (fun f => Wait f (fun _ => cl_get si c)) h1 (@empty_store F)). intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending F nat t (Inc c) h1 r1 (fun _ => cl_get si c)). apply resolve_here. }
        eapply tagged_execution_emit.
        { apply (@tagged_future F nat t (Get (other c)) (fun g => Wait g (fun x => Ret x)) h2).
          intros [Heq | []]. exact (Hne Heq). }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending F nat t (Get (other c)) h2 r (fun x => Ret x)). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. repeat constructor.
    Qed.

    Lemma mnw_produces c h1 h2 (r1 r : nat) :
      h1 <> h2 ->
      program_produces_tagged t (Mnw_si si (SB c) t)
        [ti h1 (Inc c) (resolved_in (@empty_store F));
         ti h2 (Get (other c)) (resolved_in [@Build_FutureEntry F h1 (@Pending F (Inc c))]);
         tr_ h2 (Get (other c)) r; tr_ h1 (Inc c) r1] r.
    Proof.
      intros Hne.
      exists (Build_ProgramConfig (Ret r)
                [@Build_FutureEntry F h2 (@Resolved F (Get (other c)) r); @Build_FutureEntry F h1 (@Resolved F (Inc c) r1)]).
      split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future F nat t (Inc c) (fun f => nw_get si c f) h1 (@empty_store F)). intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_future F nat t (Get (other c))
                   (fun g => Wait g (fun x => Wait (@MkFutureRef F (Inc c) h1) (fun _ => Ret x))) h2).
          intros [Heq | []]. exact (Hne Heq). }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending F nat t (Get (other c)) h2 r
                   (fun x => Wait (@MkFutureRef F (Inc c) h1) (fun _ => Ret x))). apply resolve_here. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending F nat t (Inc c) h1 r1 (fun _ => Ret r)).
          apply resolve_next; [exact (fun H => Hne (eq_sym H)) | apply resolve_here]. }
        apply tagged_execution_refl.
      - constructor. repeat constructor.
    Qed.

  End Traces.

  (** ** Generic facts about module executions

      Not specific to the clients: the underlay invocation keys of an
      execution are unique ([exec_underlay_nodup]); module positions map
      to underlay positions ([ucount]); a returned overlay call has the
      result its body committed to ([iexec_over_res]) and has emitted
      all its events ([returned_emitted]); events of a call that are
      ordered by a chain of (F1)--(F3) edges ([forced]) are emitted in
      that order ([forced_order]). *)

  Section ExecGeneric.
    Context {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F).

    Lemma ikeys_app (l1 l2 : list (ThreadEvent E)) :
      invocation_keys (l1 ++ l2) = invocation_keys l1 ++ invocation_keys l2.
    Proof.
      induction l1 as [| a l1 IH]; [reflexivity |]. cbn. destruct (te_ev E a); rewrite IH; reflexivity.
    Qed.

    Definition sb_qkeys (queue : TaggedQueue E F) : list (CallKey E) :=
      invocation_keys (map (fun x => untag (ts_event x)) queue).

    Lemma sb_qkeys_app q1 q2 : sb_qkeys (q1 ++ q2) = sb_qkeys q1 ++ sb_qkeys q2.
    Proof. unfold sb_qkeys. rewrite map_app. apply ikeys_app. Qed.

    Lemma sb_qkeys_schedule owner (trace : list (TaggedEvent E)) :
      sb_qkeys (schedule_trace_tagged owner trace) = invocation_keys (map untag trace).
    Proof. unfold sb_qkeys, schedule_trace_tagged. rewrite map_map. reflexivity. Qed.

    Lemma ue_app (l1 l2 : list (ModuleEvent E F)) :
      ViewLHL.underlay_events (l1 ++ l2) = ViewLHL.underlay_events l1 ++ ViewLHL.underlay_events l2.
    Proof. unfold ViewLHL.underlay_events. apply flat_map_app. Qed.

    Lemma ue_cons (ev : ModuleEvent E F) l :
      ViewLHL.underlay_events (ev :: l) = ViewLHL.underlay_events [ev] ++ ViewLHL.underlay_events l.
    Proof. change (ev :: l) with ([ev] ++ l). apply ue_app. Qed.

    (** The invariant: the invocation keys emitted so far and those still
        queued are pairwise distinct, and all are recorded as used. *)
    Definition KeysOK (em : list (ThreadEvent E)) (c : @TaggedModuleConfig E F VE) : Prop :=
      NoDup (invocation_keys em ++ sb_qkeys (tm_queue c)) /\
      forall k, In k (invocation_keys em ++ sb_qkeys (tm_queue c)) -> In k (tm_used_underlay c).

    Lemma keys_step ev c c' em :
      module_step_tagged VE M ev c c' -> KeysOK em c -> KeysOK (em ++ ViewLHL.underlay_events [ev]) c'.
    Proof.
      intros Hs (Hnd & Hu).
      destruct Hs as [t h op q pool queue used trace ret Hfresh Hmeth (Hnd2 & Hfr)
                     | cand q q' pool queue queue' used Hsel Hlts
                     | t h op ret q pool pool' queue used Hfin Hdone];
        unfold KeysOK; cbn [tm_queue tm_used_underlay] in Hnd, Hu |- *.
      - change (ViewLHL.underlay_events [@OverlayEvent E F (Build_ThreadEvent t (@InvEv F h op))]) with (@nil (ThreadEvent E)).
        rewrite app_nil_r. rewrite sb_qkeys_app, sb_qkeys_schedule. split.
        + rewrite app_assoc. apply NoDup_app; [exact Hnd | exact Hnd2 |].
          intros k Hk Hk'. exact (Hfr k Hk' (Hu k Hk)).
        + intros k Hk. rewrite app_assoc in Hk. apply in_app_or in Hk as [Hk | Hk]; apply in_or_app; [left | right];
            [exact (Hu k Hk) | exact Hk].
      - change (ViewLHL.underlay_events [@UnderlayEvent E F (untag (ts_event cand))]) with [untag (ts_event cand)].
        destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & -> & -> & _).
        assert (Hp : Permutation (invocation_keys em ++ sb_qkeys (pre ++ cand :: post))
                                 (invocation_keys (em ++ [untag (ts_event cand)]) ++ sb_qkeys (pre ++ post))).
        { change (pre ++ cand :: post) with (pre ++ [cand] ++ post).
          rewrite !sb_qkeys_app, ikeys_app, <- app_assoc. apply Permutation_app_head.
          change (sb_qkeys [cand]) with (invocation_keys [untag (ts_event cand)]).
          rewrite !app_assoc. apply Permutation_app_tail. apply Permutation_app_comm. }
        split; [exact (Permutation_NoDup Hp Hnd) |].
        intros k Hk. apply Hu. exact (Permutation_in _ (Permutation_sym Hp) Hk).
      - change (ViewLHL.underlay_events [@OverlayEvent E F (Build_ThreadEvent t (@ResEv F h op ret))]) with (@nil (ThreadEvent E)).
        rewrite app_nil_r. split; assumption.
    Qed.

    Lemma keys_exec c evs c' em :
      module_execution_tagged VE M c evs c' -> KeysOK em c -> KeysOK (em ++ ViewLHL.underlay_events evs) c'.
    Proof.
      intros Hex. revert em. induction Hex as [c | c1 c2 c3 ev evs Hs Hex IH]; intros em Hk.
      - rewrite app_nil_r. exact Hk.
      - rewrite ue_cons, app_assoc. apply IH. exact (keys_step _ _ _ _ Hs Hk).
    Qed.

    (** Every underlay invocation key occurs at most once in an execution
        from an initial configuration. *)
    Theorem exec_underlay_nodup σ0 evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
      NoDup (invocation_keys (ViewLHL.underlay_events evs)).
    Proof.
      intros Hex. assert (H0 : KeysOK [] (initial_tagged_module VE σ0)).
      { split; [constructor | intros k []]. }
      destruct (keys_exec _ _ _ _ Hex H0) as (Hnd & _). exact (NoDup_app_remove_r _ _ Hnd).
    Qed.

    (** *** Module positions and underlay positions *)

    Definition ucount (evs : list (ModuleEvent E F)) (p : nat) : nat :=
      length (ViewLHL.underlay_events (firstn p evs)).

    Lemma ucount_nth evs p e :
      nth_error evs p = Some (UnderlayEvent e) -> nth_error (ViewLHL.underlay_events evs) (ucount evs p) = Some e.
    Proof.
      unfold ucount. revert p. induction evs as [| a evs IH]; intros p Hp; [destruct p; discriminate |].
      destruct p as [| p]; cbn in Hp.
      - injection Hp as ->. reflexivity.
      - change (firstn (S p) (a :: evs)) with ([a] ++ firstn p evs).
        rewrite ue_cons, ue_app, length_app, nth_error_app2 by lia.
        rewrite Nat.add_comm, Nat.add_sub. exact (IH p Hp).
    Qed.

    Lemma ucount_lt evs p q e :
      p < q -> nth_error evs p = Some (UnderlayEvent e) -> ucount evs p < ucount evs q.
    Proof.
      unfold ucount. revert p q. induction evs as [| a evs IH]; intros p q Hlt Hp; [destruct p; discriminate |].
      destruct q as [| q]; [lia |].
      change (firstn (S q) (a :: evs)) with ([a] ++ firstn q evs). rewrite ue_app, length_app.
      destruct p as [| p]; cbn in Hp.
      - injection Hp as ->. cbn. lia.
      - change (firstn (S p) (a :: evs)) with ([a] ++ firstn p evs). rewrite ue_app, length_app.
        pose proof (IH p q ltac:(lia) Hp). lia.
    Qed.

    Lemma in_overlay_ierase (IT : list (@ITraceEvent E F)) e :
      In e (overlay_events (map ierase IT)) -> exists p, nth_error IT p = Some (IOver e).
    Proof.
      induction IT as [| a IT IH]; intros Hin; [destruct Hin |].
      destruct a as [x | ev]; cbn in Hin.
      - destruct (IH Hin) as (p & Hp). exists (S p). exact Hp.
      - destruct Hin as [<- | Hin]; [exists 0; reflexivity |].
        destruct (IH Hin) as (p & Hp). exists (S p). exact Hp.
    Qed.

    (** *** Returned calls *)

    Lemma istep_invs_incl n ev (c c' : IConfig VE) :
      istep VE M n ev c c' -> forall r, In r (ic_invs VE c) -> In r (ic_invs VE c').
    Proof. intros Hs r Hr. destruct Hs; cbn in *; auto. apply in_or_app. left. exact Hr. Qed.

    (** The result of a returned call is the result its body committed to
        at the invocation.  Results are compared through [ResEv]
        equalities, never decomposed. *)
    Lemma iexec_over_res q0 IT ic :
      iexec VE M (iinitial VE q0) IT ic ->
      forall p t h op ret, nth_error IT p = Some (IOver (Build_ThreadEvent t (@ResEv F h op ret))) ->
      exists r, In r (ic_invs VE ic) /\ ir_key r = (t, h) /\ @ResEv F h op ret = @ResEv F h (ir_op r) (ir_ret r).
    Proof.
      induction 1 as [| tr c ev c' Hexec IH Hstep]; intros p t h op ret Hp; [destruct p; discriminate |].
      destruct (nth_app_cases _ _ _ _ Hp) as [(_ & Hp') | (Hge & Hp')].
      - destruct (IH _ _ _ _ _ Hp') as (r & Hr & Hk & Hev). exists r. split; [| auto].
        exact (istep_invs_incl _ _ _ _ Hstep r Hr).
      - destruct (p - length tr) as [| k] eqn:Hk; [| destruct k; discriminate Hp'].
        cbn in Hp'. injection Hp' as Hev0.
        pose proof (iinv_reach _ _ _ _ _ Hexec) as Hinv.
        destruct Hstep as [t' h' op' q pool queue used log invs trace ret' Hfresh Hmeth Hft
                          | cand q q' pool queue queue' used log invs Hsel Hlts
                          | t' h' op' ret' q pool pool' queue used log invs Hfin Hdone]; [| discriminate Hev0 |].
        + apply (f_equal (fun x => match x with IOver e => match te_ev F e with InvEv _ _ => true | ResEv _ _ _ => false end
                                            | IUnder _ => true end)) in Hev0.
          discriminate Hev0.
        + assert (Ht : t' = t) by exact (f_equal (fun x => match x with IOver e => te_tid F e | IUnder _ => t end) Hev0).
          assert (He : @ResEv F h' op' ret' = @ResEv F h op ret)
            by exact (f_equal (fun x => match x with IOver e => te_ev F e | IUnder _ => @ResEv F h op ret end) Hev0).
          assert (Hh : h' = h) by exact (f_equal event_handle He).
          subst t' h'. clear Hev0.
          destruct (ii_pool_active _ _ _ _ Hinv t h op' ret' (finish_call_source _ _ _ _ _ _ Hfin))
            as (r & Hr & Hkey & Hac).
          exists r. split; [exact Hr | split; [exact Hkey |]].
          rewrite <- He.
          exact (f_equal (fun cc => match cc with ActiveCall o x => @ResEv F h o x | DeadCall => @ResEv F h op' ret' end) Hac).
    Qed.

    Section Returned.
      Context (IT : list (@ITraceEvent E F)) (ic : IConfig VE) (Hinv : IInv VE M IT ic).

      Definition returned (r : @InvRec E F) : Prop :=
        exists p op ret, nth_error IT p = Some (IOver (Build_ThreadEvent (fst (ir_key r)) (@ResEv F (snd (ir_key r)) op ret))).

      (** A returned call has emitted every event of its body. *)
      Lemma returned_emitted r : In r (ic_invs VE ic) -> returned r ->
        forall j m, nth_error (ir_trace r) j = Some m ->
          exists q, nth_error IT q = Some (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
      Proof.
        intros Hr (p & op & ret & Hp) j m Hj.
        pose proof (block_of_trace r j m Hj) as Hb.
        assert (Hl : In (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m) (ic_log VE ic)).
        { rewrite (ii_blocks _ _ _ _ Hinv). apply in_flat_map. exists r. auto. }
        destruct (ii_partition _ _ _ _ Hinv _ Hl) as [Hq | Hq].
        - exfalso. apply (ii_returned_done _ _ _ _ Hinv _ _ _ _ _ Hp).
          rewrite <- surjective_pairing. rewrite map_map.
          exact (in_map (fun x => ts_owner (snd x)) _ _ Hq).
        - apply In_nth_error. exact Hq.
      Qed.

      (** Ordered by a chain of (F1)--(F3) edges inside one method trace. *)
      Inductive forced (tr : list (TaggedEvent E)) : nat -> nat -> Prop :=
      | forced_one i j a b :
          i < j -> nth_error tr i = Some a -> nth_error tr j = Some b -> ~ tagged_can_cross a b -> forced tr i j
      | forced_trans i j k : forced tr i j -> forced tr j k -> forced tr i k.

      Lemma forced_valid tr i j : forced tr i j -> (exists a, nth_error tr i = Some a) /\ (exists b, nth_error tr j = Some b).
      Proof.
        induction 1 as [i j a b _ Ha Hb _ | i j k _ [IH1 _] _ [_ IH2]]; [split; eauto | split; assumption].
      Qed.

      Lemma forced_order r : In r (ic_invs VE ic) -> returned r ->
        forall i j, forced (ir_trace r) i j ->
        forall pi pj a b, nth_error (ir_trace r) i = Some a -> nth_error (ir_trace r) j = Some b ->
          nth_error IT pi = Some (IUnder (ir_start r + i, Build_TaggedScheduledEvent (ir_key r) a)) ->
          nth_error IT pj = Some (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) b)) ->
          pi < pj.
      Proof.
        intros Hr Hret i j Hf. induction Hf as [i j a0 b0 Hlt Ha0 Hb0 Hnc | i j k Hf1 IH1 Hf2 IH2];
          intros pi pj a b Ha Hb Hpi Hpj.
        - rewrite Ha in Ha0. rewrite Hb in Hb0. injection Ha0 as <-. injection Hb0 as <-.
          apply (ii_order _ _ _ _ Hinv _ _ _ _ Hpi Hpj); cbn; [lia | exact Hnc].
        - destruct (forced_valid _ _ _ Hf2) as ((m & Hm) & _).
          destruct (returned_emitted r Hr Hret j m Hm) as (pm & Hpm).
          pose proof (IH1 pi pm a m Ha Hm Hpi Hpm). pose proof (IH2 pm pj m b Hm Hb Hpm Hpj). lia.
      Qed.
    End Returned.
  End ExecGeneric.

  (** ** The effect-at-invocation path of the two counters

      Along a path of [EI δcxy] from [(s00, [])]: the value of counter [c]
      is the number of [Inc c] invocations so far, and a pending record
      for a [Get c'] carries the number of [Inc c'] invocations before
      its own invocation ([EIInv]).  Hence a [Get c'] that returns 0
      precedes every [Inc c'] invocation, and the store-buffering cycle
      [inc_x < get_y < inc_y < get_x < inc_x] is impossible
      ([ei_sb_cycle_gen]). *)

  Section EIPath.
    Context (si : COp -> COp -> Prop).
    Local Abbreviation F := (CxySig si).
    Local Abbreviation V := (@RelaxedHoareSpec.EI F MSt δcxy).

    Definition cloc_eqb (a b : CLoc) : bool :=
      match a, b with CX, CX | CY, CY => true | _, _ => false end.

    Lemma cloc_eqb_spec a b : cloc_eqb a b = true <-> a = b.
    Proof. destruct a, b; cbn; split; congruence. Qed.

    Definition is_inc (c : CLoc) (e : ThreadEvent F) : bool :=
      match te_ev F e with InvEv _ (Inc c') => cloc_eqb c c' | _ => false end.

    Definition cnt (c : CLoc) (l : list (ThreadEvent F)) : nat := length (filter (is_inc c) l).

    Lemma cnt_app c l1 l2 : cnt c (l1 ++ l2) = cnt c l1 + cnt c l2.
    Proof. unfold cnt. rewrite filter_app, length_app. reflexivity. Qed.

    Lemma get_put s c c' v : get (put s c' v) c = if cloc_eqb c c' then v else get s c.
    Proof. destruct s, c, c'; reflexivity. Qed.

    Definition EIInv (l : list (ThreadEvent F)) (σ : MSt * list (RelaxedTraceLin.Op F)) : Prop :=
      (forall c, get (fst σ) c = cnt c l) /\
      (forall o, In o (snd σ) -> exists i,
         nth_error l i = Some (Build_ThreadEvent (fst (RelaxedTraceLin.op_key o))
                                 (@InvEv F (snd (RelaxedTraceLin.op_key o)) (RelaxedTraceLin.op_op o))) /\
         forall c', RelaxedTraceLin.op_op o = Get c' -> (RelaxedTraceLin.op_ret o : nat) = cnt c' (firstn i l)).

    Lemma eiinv_extend {A : Type} (l : list A) (x : A) i ev :
      nth_error l i = Some ev -> nth_error (l ++ [x]) i = Some ev /\ firstn i (l ++ [x]) = firstn i l.
    Proof.
      intros Hi. assert (Hlt : i < length l) by (apply nth_error_Some; rewrite Hi; discriminate).
      split; [rewrite nth_error_app1 by exact Hlt; exact Hi |].
      rewrite firstn_app. replace (i - length l) with 0 by lia. rewrite app_nil_r. reflexivity.
    Qed.

    Lemma cnt_snoc c l e : cnt c (l ++ [e]) = cnt c l + (if is_inc c e then 1 else 0).
    Proof. unfold cnt. rewrite filter_app, length_app. cbn. destruct (is_inc c e); reflexivity. Qed.

    Lemma ei_inv_step l σ ev σ' : EIInv l σ -> @RelaxedHoareSpec.ei_step F MSt δcxy ev σ σ' -> EIInv (l ++ [ev]) σ'.
    Proof.
      intros (Hc & Ho) Hs. destruct ev as [t [h o | h o r]]; cbn in Hs.
      - destruct Hs as (r & st' & Hd & ->). split.
        + intros c. cbn [fst]. rewrite cnt_snoc. unfold is_inc. cbn [te_ev].
          destruct o as [c' | c']; cbn in Hd; destruct Hd as [-> ->].
          * rewrite get_put. destruct (cloc_eqb c c') eqn:He.
            -- apply cloc_eqb_spec in He. subst c'. rewrite Hc. lia.
            -- rewrite Hc. lia.
          * rewrite Hc. lia.
        + intros o0 [<- | Hin]; cbn [snd fst RelaxedTraceLin.op_key RelaxedTraceLin.op_op RelaxedTraceLin.op_ret].
          * exists (length l). split; [rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity |].
            intros c' Hop. subst o. cbn in Hd. destruct Hd as [-> _].
            rewrite firstn_app, Nat.sub_diag, firstn_all2 by lia. cbn. rewrite app_nil_r. apply Hc.
          * destruct (Ho o0 Hin) as (i & Hi & Hv).
            destruct (eiinv_extend l (Build_ThreadEvent t (@InvEv F h o)) i _ Hi) as (Hi' & Hf).
            exists i. split; [exact Hi' |]. intros c' Hop. rewrite Hf. exact (Hv c' Hop).
      - destruct Hs as (P1 & P2 & Hsnd & ->). split.
        + intros c. cbn [fst]. rewrite cnt_snoc. cbn. rewrite Hc. lia.
        + intros o0 Hin. cbn [snd] in Hin.
          assert (Hin' : In o0 (snd σ))
            by (rewrite Hsnd; apply in_app_or in Hin as [H | H]; apply in_or_app; [left | right; right]; exact H).
          destruct (Ho o0 Hin') as (i & Hi & Hv).
          destruct (eiinv_extend l (Build_ThreadEvent t (@ResEv F h o r)) i _ Hi) as (Hi' & Hf).
          exists i. split; [exact Hi' |]. intros c' Hop. rewrite Hf. exact (Hv c' Hop).
    Qed.

    Lemma ei_inv_path σ l σ' : vf_path V σ l σ' -> forall pre, EIInv pre σ -> EIInv (pre ++ l) σ'.
    Proof.
      induction 1 as [σ | σ ev σ1 l σ2 Hs Hp IH]; intros pre Hi; [rewrite app_nil_r; exact Hi |].
      replace (pre ++ ev :: l) with ((pre ++ [ev]) ++ l) by (rewrite <- app_assoc; reflexivity).
      apply IH. exact (ei_inv_step _ _ _ _ Hi Hs).
    Qed.

    Lemma ei_inv_init : EIInv [] (s00, []).
    Proof. split; [intros []; reflexivity | intros o []]. Qed.

    (** A response with result [r] answers an earlier invocation with the
        same key and operation; for a [Get c'], [r] is the number of
        [Inc c'] invocations before that invocation. *)
    Lemma ei_res_source u v j (k : CallKey F) o (r : nat) :
      vf_path V (s00, []) u v ->
      nth_error u j = Some (Build_ThreadEvent (fst k) (@ResEv F (snd k) o r)) ->
      exists i, i < j /\ nth_error u i = Some (Build_ThreadEvent (fst k) (@InvEv F (snd k) o)) /\
        forall c', o = Get c' -> r = cnt c' (firstn i u).
    Proof.
      intros Hp Hj. destruct (nth_error_split _ _ Hj) as (l1 & l2 & -> & Hl1).
      destruct (RelaxedHoareSpec.vf_path_app_inv _ _ _ _ _ Hp) as (σ & Hp1 & Hp2).
      inversion Hp2 as [| ? ? σ' ? ? Hs _]; subst.
      pose proof (ei_inv_path _ _ _ Hp1 [] ei_inv_init) as (_ & Ho). cbn in Hs.
      destruct Hs as (P1 & P2 & Hsnd & _).
      assert (Hin : In (@RelaxedTraceLin.Build_Op F (fst k, snd k) o r) (snd σ))
        by (rewrite Hsnd; apply in_or_app; right; left; reflexivity).
      destruct (Ho _ Hin) as (i & Hi & Hv). cbn in Hi, Hv.
      assert (Hlt : i < length l1) by (apply nth_error_Some; rewrite Hi; discriminate).
      exists i. split; [lia |]. split; [rewrite nth_error_app1 by exact Hlt; exact Hi |].
      intros c' Hop. rewrite (Hv c' Hop). rewrite firstn_app. replace (i - length l1) with 0 by lia.
      rewrite app_nil_r. reflexivity.
    Qed.

    Lemma cnt_pos l i n (k : CallKey F) c :
      nth_error l i = Some (Build_ThreadEvent (fst k) (@InvEv F (snd k) (Inc c))) -> i < n -> 1 <= cnt c (firstn n l).
    Proof.
      intros Hi Hlt. destruct (nth_error_split _ _ Hi) as (l1 & l2 & -> & Hl1).
      assert (Hone : cnt c [Build_ThreadEvent (fst k) (@InvEv F (snd k) (Inc c))] = 1)
        by (unfold cnt; cbn; destruct c; reflexivity).
      rewrite firstn_app, cnt_app. replace (n - length l1) with (S (n - S (length l1))) by lia.
      change (firstn (S (n - S (length l1))) (Build_ThreadEvent (fst k) (@InvEv F (snd k) (Inc c)) :: l2))
        with ([Build_ThreadEvent (fst k) (@InvEv F (snd k) (Inc c))] ++ firstn (n - S (length l1)) l2).
      rewrite cnt_app, Hone. lia.
    Qed.

    (** A [Get c'] invocation whose response is 0 precedes every [Inc c']
        invocation. *)
    Lemma get0_before_inc u v (kb kc : CallKey F) ib jb ic c' :
      vf_path V (s00, []) u v -> NoDup (invocation_keys u) ->
      nth_error u ib = Some (Build_ThreadEvent (fst kb) (@InvEv F (snd kb) (Get c'))) ->
      nth_error u jb = Some (Build_ThreadEvent (fst kb) (@ResEv F (snd kb) (Get c') 0)) ->
      nth_error u ic = Some (Build_ThreadEvent (fst kc) (@InvEv F (snd kc) (Inc c'))) ->
      ib < ic.
    Proof.
      intros Hp Hnd Hib Hjb Hic.
      destruct (ei_res_source _ _ _ _ _ _ Hp Hjb) as (i & _ & Hi & Hv).
      assert (Hii : i = ib) by exact (local_inv_unique _ _ _ _ _ _ _ _ Hnd Hi Hib eq_refl eq_refl eq_refl).
      subst i. specialize (Hv c' eq_refl).
      destruct (Nat.lt_trichotomy ib ic) as [H | [H | H]]; [exact H | exfalso | exfalso].
      - subst ic. rewrite Hib in Hic.
        apply (f_equal (fun x => match x with Some e => event_op (te_ev F e) | None => Inc CX end)) in Hic.
        discriminate Hic.
      - pose proof (cnt_pos _ _ _ _ _ Hic H). lia.
    Qed.

    Theorem ei_sb_cycle_gen (u : list (ThreadEvent F)) v (ka kb kc kd : CallKey F) ia ib jb ic id jd :
      vf_path V (s00, []) u v -> NoDup (invocation_keys u) ->
      nth_error u ia = Some (Build_ThreadEvent (fst ka) (@InvEv F (snd ka) (Inc CX))) ->
      nth_error u ib = Some (Build_ThreadEvent (fst kb) (@InvEv F (snd kb) (Get CY))) ->
      nth_error u jb = Some (Build_ThreadEvent (fst kb) (@ResEv F (snd kb) (Get CY) 0)) ->
      nth_error u ic = Some (Build_ThreadEvent (fst kc) (@InvEv F (snd kc) (Inc CY))) ->
      nth_error u id = Some (Build_ThreadEvent (fst kd) (@InvEv F (snd kd) (Get CX))) ->
      nth_error u jd = Some (Build_ThreadEvent (fst kd) (@ResEv F (snd kd) (Get CX) 0)) ->
      ia < ib -> ic < id -> False.
    Proof.
      intros Hp Hnd Ha Hb Hjb Hc Hd Hjd H1 H2.
      pose proof (get0_before_inc _ _ _ _ _ _ _ _ Hp Hnd Hb Hjb Hc).
      pose proof (get0_before_inc _ _ _ _ _ _ _ _ Hp Hnd Hd Hjd Ha).
      lia.
    Qed.
  End EIPath.

  (** The planned statement, over [FC] ([by_counter]). *)
  Theorem ei_sb_cycle (u : list (ThreadEvent FC)) v (ka kb kc kd : CallKey FC) ia ib jb ic id jd :
    vf_path (@RelaxedHoareSpec.EI FC MSt δcxy) (s00, []) u v -> NoDup (invocation_keys u) ->
    nth_error u ia = Some (Build_ThreadEvent (fst ka) (InvEv (snd ka) (Inc CX))) ->
    nth_error u ib = Some (Build_ThreadEvent (fst kb) (InvEv (snd kb) (Get CY))) ->
    nth_error u jb = Some (Build_ThreadEvent (fst kb) (@ResEv FC (snd kb) (Get CY) 0)) ->
    nth_error u ic = Some (Build_ThreadEvent (fst kc) (InvEv (snd kc) (Inc CY))) ->
    nth_error u id = Some (Build_ThreadEvent (fst kd) (InvEv (snd kd) (Get CX))) ->
    nth_error u jd = Some (Build_ThreadEvent (fst kd) (@ResEv FC (snd kd) (Get CX) 0)) -> ia < ib -> ic < id -> False.
  Proof. exact (ei_sb_cycle_gen by_counter u v ka kb kc kd ia ib jb ic id jd). Qed.

  (** ** The client theorems

      [SBShape M]: every call [SB c] of [M] invokes [Inc c] and
      [Get (other c)], the [Get] answers with the call's result, and the
      [Inc] invocation is forced before the [Get] invocation by a chain
      of (F1)--(F3) edges of the call's own trace.  [sb_cycle_of_shape]:
      then no trace of [M] over [EI δcxy], complete or not, has an
      [SB CX] and an [SB CY] that both return 0.  The proof uses the
      specification only ([EI δcxy]); it never mentions the
      implementation of the counters. *)

  Lemma not_cross_same {E : RelaxedSig.t} (a b : TaggedEvent E) :
    te_tid E (untag a) = te_tid E (untag b) -> must_precede a b -> ~ tagged_can_cross a b.
  Proof. intros Ht Hm [Hd | (_ & Hn)]; [exact (Hd Ht) | exact (Hn Hm)]. Qed.

  Section ClientGeneric.
    Context (si : COp -> COp -> Prop).
    Local Abbreviation F := (CxySig si).

    Definition SBShape (M : RelaxedModuleImpl F GS) : Prop :=
      forall t c tr (r : nat), program_produces_tagged t (M (SB c) t) tr r ->
      exists h1 h2 i1 i2 i3 D1 D2 D3,
        nth_error tr i1 = Some (Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h1 (Inc c))) D1) /\
        nth_error tr i2 = Some (Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h2 (Get (other c)))) D2) /\
        nth_error tr i3 = Some (Build_TaggedEvent (Build_ThreadEvent t (@ResEv F h2 (Get (other c)) r)) D3) /\
        forced tr i1 i2.

    Section Calls.
      Context (M : RelaxedModuleImpl F GS) (Hsh : SBShape M) (VE : LTS F).

      (** A returned call [SB c0] with result [r]: in the underlay trace,
          its [Inc c0] invocation precedes its [Get (other c0)]
          invocation, and the [Get] answers [r]. *)
      Lemma sb_call_events q0 IT ic t h c0 (r : nat) p :
        iexec VE M (iinitial VE q0) IT ic ->
        nth_error IT p = Some (IOver (Build_ThreadEvent t (@ResEv GS h (SB c0) r))) ->
        exists (ka kb : CallKey F) ia ib jb, ia < ib /\
          nth_error (ViewLHL.underlay_events (map ierase IT)) ia =
            Some (Build_ThreadEvent (fst ka) (@InvEv F (snd ka) (Inc c0))) /\
          nth_error (ViewLHL.underlay_events (map ierase IT)) ib =
            Some (Build_ThreadEvent (fst kb) (@InvEv F (snd kb) (Get (other c0)))) /\
          nth_error (ViewLHL.underlay_events (map ierase IT)) jb =
            Some (Build_ThreadEvent (fst kb) (@ResEv F (snd kb) (Get (other c0)) r)).
      Proof.
        intros Hix Hp. pose proof (iinv_reach _ _ _ _ _ Hix) as Hinv.
        destruct (iexec_over_res VE M q0 IT ic Hix p t h (SB c0) r Hp) as (rec & Hin & Hkey & Hev).
        destruct rec as [key op ret st pos trc]. cbn in Hkey, Hev. subst key.
        destruct op as [c1].
        assert (Hc : c1 = c0).
        { apply (f_equal event_op) in Hev. cbn in Hev. injection Hev as ->. reflexivity. }
        subst c1.
        assert (Hr : (ret : nat) = r)
          by exact (eq_sym (f_equal (fun e : Event GS => match e with ResEv _ _ v => (v : nat) | InvEv _ _ => 0 end) Hev)).
        rewrite Hr in Hin. clear Hev Hr ret.
        pose proof (ii_produced _ _ _ _ Hinv _ Hin) as Hprod. cbn in Hprod.
        destruct (Hsh _ _ _ _ Hprod) as (h1 & h2 & i1 & i2 & i3 & D1 & D2 & D3 & Hi1 & Hi2 & Hi3 & Hf).
        assert (Hret : returned IT (Build_InvRec (t, h) (SB c0) r st pos trc)) by (exists p, (SB c0), r; exact Hp).
        destruct (returned_emitted VE M IT ic Hinv _ Hin Hret i1 _ Hi1) as (q1 & Hq1).
        destruct (returned_emitted VE M IT ic Hinv _ Hin Hret i2 _ Hi2) as (q2 & Hq2).
        destruct (returned_emitted VE M IT ic Hinv _ Hin Hret i3 _ Hi3) as (q3 & Hq3).
        pose proof (forced_order VE M IT ic Hinv _ Hin Hret i1 i2 Hf q1 q2 _ _ Hi1 Hi2 Hq1 Hq2) as Hlt.
        assert (He1 : nth_error (map ierase IT) q1 =
                        Some (UnderlayEvent (Build_ThreadEvent t (@InvEv F h1 (Inc c0)))))
          by (rewrite nth_error_map, Hq1; reflexivity).
        assert (He2 : nth_error (map ierase IT) q2 =
                        Some (UnderlayEvent (Build_ThreadEvent t (@InvEv F h2 (Get (other c0))))))
          by (rewrite nth_error_map, Hq2; reflexivity).
        assert (He3 : nth_error (map ierase IT) q3 =
                        Some (UnderlayEvent (Build_ThreadEvent t (@ResEv F h2 (Get (other c0)) r))))
          by (rewrite nth_error_map, Hq3; reflexivity).
        exists (t, h1), (t, h2), (ucount (map ierase IT) q1), (ucount (map ierase IT) q2), (ucount (map ierase IT) q3).
        split; [exact (ucount_lt _ _ _ _ Hlt He1) |].
        split; [exact (ucount_nth _ _ _ He1) |]. split; [exact (ucount_nth _ _ _ He2) | exact (ucount_nth _ _ _ He3)].
      Qed.
    End Calls.

    (** The client theorem, generic in the client and in [si]. *)
    Theorem sb_cycle_of_shape (M : RelaxedModuleImpl F GS) :
      SBShape M ->
      forall s (k1 k2 : CallKey GS),
        MTraces (@RelaxedHoareSpec.EI F MSt δcxy) M (s00, []) s ->
        In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s ->
        In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False.
    Proof.
      intros Hsh s k1 k2 (evs & c & Hex & Hov) H1 H2.
      destruct (instrument _ _ _ _ _ Hex) as (IT & ic & Hix & Herase & _). subst evs.
      pose proof (ViewLHL.exec_underlay_path M _ _ _ _ Hex) as Hpath. cbn in Hpath.
      pose proof (exec_underlay_nodup _ _ _ _ _ Hex) as Hnd.
      rewrite <- Hov in H1, H2.
      destruct (in_overlay_ierase _ _ H1) as (p1 & Hp1). destruct (in_overlay_ierase _ _ H2) as (p2 & Hp2).
      destruct (sb_call_events M Hsh _ _ _ _ _ _ _ _ _ Hix Hp1) as (ka & kb & ia & ib & jb & Hab & Ha & Hb & Hjb).
      destruct (sb_call_events M Hsh _ _ _ _ _ _ _ _ _ Hix Hp2) as (kc & kd & ic' & id & jd & Hcd & Hc & Hd & Hjd).
      exact (ei_sb_cycle_gen si _ _ ka kb kc kd ia ib jb ic' id jd Hpath Hnd Ha Hb Hjb Hc Hd Hjd Hab Hcd).
    Qed.

    (** The waiting client has the shape for every [si]: the chain is
        [inv(inc)] →(F1) [res(inc)] →(F3) [inv(get)]. *)
    Lemma mcl_shape : SBShape (Mcl_si si).
    Proof.
      intros t c tr r Hp. destruct (mcl_trace si t c tr r Hp) as (h1 & h2 & r1 & D1 & D2 & Hne & HD & ->).
      exists h1, h2, 0, 2, 3, D1, D2, no_deps. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
      apply (forced_trans _ 0 1 2).
      - eapply (forced_one _ 0 1); [lia | reflexivity | reflexivity |]. apply not_cross_same; reflexivity.
      - eapply (forced_one _ 1 2); [lia | reflexivity | reflexivity |]. apply not_cross_same; [reflexivity | exact HD].
    Qed.

    (** The no-wait client has the shape when [(Inc c, Get (other c))] is
        never semi-independent: the chain is the single (F2) edge
        [inv(inc)] → [inv(get)]. *)
    Lemma mnw_shape : (forall c, ~ si (Inc c) (Get (other c))) -> SBShape (Mnw_si si).
    Proof.
      intros Hsi t c tr r Hp. destruct (mnw_trace si t c tr r Hp) as (h1 & h2 & r1 & D1 & D2 & Hne & Htr).
      cbv zeta in Htr.
      assert (Hnc : forall D D', ~ tagged_can_cross (Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h1 (Inc c))) D)
                                                   (Build_TaggedEvent (Build_ThreadEvent t (@InvEv F h2 (Get (other c)))) D'))
        by (intros D D'; apply not_cross_same; [reflexivity | exact (Hsi c)]).
      destruct Htr as [-> | [-> | ->]].
      - exists h1, h2, 0, 1, 2, D1, D2, no_deps. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
        eapply (forced_one _ 0 1); [lia | reflexivity | reflexivity | apply Hnc].
      - exists h1, h2, 0, 1, 3, D1, D2, no_deps. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
        eapply (forced_one _ 0 1); [lia | reflexivity | reflexivity | apply Hnc].
      - exists h1, h2, 0, 2, 3, D1, D2, no_deps. split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
        eapply (forced_one _ 0 2); [lia | reflexivity | reflexivity | apply Hnc].
    Qed.

    Corollary sb_client_spec_gen s (k1 k2 : CallKey GS) :
      MTraces (@RelaxedHoareSpec.EI F MSt δcxy) (Mcl_si si) (s00, []) s ->
      In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s ->
      In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False.
    Proof. exact (sb_cycle_of_shape _ mcl_shape s k1 k2). Qed.

    Corollary sb_nowait_safe_gen :
      (forall c, ~ si (Inc c) (Get (other c))) ->
      forall s (k1 k2 : CallKey GS),
        MTraces (@RelaxedHoareSpec.EI F MSt δcxy) (Mnw_si si) (s00, []) s ->
        In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s ->
        In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False.
    Proof. intros Hsi. exact (sb_cycle_of_shape _ (mnw_shape Hsi)). Qed.
  End ClientGeneric.

  (** [sb_client_spec] (the planned statement): over the plain
      specification [EI δcxy] with [SI_F = by_counter], no trace of the
      waiting client, complete or not, for any keys (possibly of the
      same thread), has an [SB CX] and an [SB CY] that both return 0. *)
  Theorem sb_client_spec s (k1 k2 : CallKey GS) :
    MTraces (@RelaxedHoareSpec.EI FC MSt δcxy) (Mcl_si by_counter) (s00, []) s ->
    In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s ->
    In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False.
  Proof. exact (sb_client_spec_gen by_counter s k1 k2). Qed.

  (** ** Executions built from module steps

      Over the plain specification [EI δcxy], from [tagged_invoke],
      [tagged_underlay] and [tagged_return] only.
      - [sb_nowait_00_gen]: when both pairs [(Inc CX, Get CY)] and
        [(Inc CY, Get CX)] are semi-independent, the no-wait client
        reaches (0, 0): each thread's [Get] invocation overtakes its own
        pending [Inc] invocation at the client's dependency frontier
        (their (F2) edge is absent), and both [Get]s read 0.
      - [sb_spec_live_gen]: the waiting client is not vacuous: both calls
        return, with results (0, 1). *)

  Section Witness.
    Context (si : COp -> COp -> Prop).
    Local Abbreviation F := (CxySig si).
    Local Abbreviation V := (@RelaxedHoareSpec.EI F MSt δcxy).

    Local Ltac nin := cbn; let H := fresh in intros H; repeat (destruct H as [H | H]; [discriminate H |]); exact H.
    Local Ltac fresh_tr :=
      split; [cbn; repeat constructor; cbn; intuition discriminate
             | intros key Hk Hu; cbn in Hk, Hu; destruct Hk as [<- | [<- | []]];
               repeat (destruct Hu as [Hu | Hu]; [discriminate Hu |]); exact Hu].
    Local Ltac same_ok := right; split; [reflexivity |]; unfold must_precede; cbn.
    Local Ltac diff_tid := left; cbn; discriminate.

    Definition gi (t : tid) (h : nat) (o : SBOp) : ThreadEvent GS := Build_ThreadEvent t (@InvEv GS h o).
    Definition gr (t : tid) (h : nat) (o : SBOp) (r : nat) : ThreadEvent GS := Build_ThreadEvent t (@ResEv GS h o r).

    Definition nwtr (t : tid) (c : CLoc) : list (TaggedEvent F) :=
      [ti si t 0 (Inc c) (resolved_in (@empty_store F));
       ti si t 1 (Get (other c)) (resolved_in [@Build_FutureEntry F 0 (@Pending F (Inc c))]);
       tr_ si t 1 (Get (other c)) 0; tr_ si t 0 (Inc c) 0].

    Theorem sb_nowait_00_gen :
      si (Inc CX) (Get CY) -> si (Inc CY) (Get CX) ->
      exists s (k1 k2 : CallKey GS),
        MTraces V (Mnw_si si) (s00, []) s /\
        In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s /\
        In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s.
    Proof.
      intros H1 H2.
      exists [gi t1 0 (SB CX); gi t2 0 (SB CY); gr t1 0 (SB CX) 0; gr t2 0 (SB CY) 0], (t1, 0), (t2, 0).
      split; [| split; cbn; tauto].
      do 2 eexists. split.
      (* the two invocations *)
      eapply tagged_module_execution_cons.
      { apply (tagged_invoke V (Mnw_si si) t1 0 (SB CX) (s00, []) [] [] [] (nwtr t1 CX) 0).
        - intros [].
        - apply mnw_produces. discriminate.
        - fresh_tr. }
      eapply tagged_module_execution_cons.
      { apply (tagged_invoke V (Mnw_si si) t2 0 (SB CY) (s00, []) _ _ _ (nwtr t2 CY) 0).
        - nin.
        - apply mnw_produces. discriminate.
        - fresh_tr. }
      (* t1's [Get CY] overtakes t1's pending [Inc CX] *)
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t1, 0)
                 (ti si t1 1 (Get CY) (resolved_in [@Build_FutureEntry F 0 (@Pending F (Inc CX))])))).
        - cbn. apply tagged_select_next; [same_ok; intros Hm; exact (Hm H1) |]. apply tagged_select_here.
        - cbn. exists 0, s00. split; [split; reflexivity | reflexivity]. }
      (* t2's [Get CX] overtakes t2's pending [Inc CY] *)
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t2, 0)
                 (ti si t2 1 (Get CX) (resolved_in [@Build_FutureEntry F 0 (@Pending F (Inc CY))])))).
        - cbn. apply tagged_select_next; [diff_tid |]. apply tagged_select_next; [diff_tid |].
          apply tagged_select_next; [diff_tid |].
          apply tagged_select_next; [same_ok; intros Hm; exact (Hm H2) |]. apply tagged_select_here.
        - cbn. exists 0, s00. split; [split; reflexivity | reflexivity]. }
      (* both [Get]s return 0 *)
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t1, 0) (tr_ si t1 1 (Get CY) 0))).
        - cbn. apply tagged_select_next; [same_ok; discriminate |]. apply tagged_select_here.
        - cbn. exists [@RelaxedTraceLin.Build_Op F (t2, 1) (Get CX) 0], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t2, 0) (tr_ si t2 1 (Get CX) 0))).
        - cbn. apply tagged_select_next; [diff_tid |]. apply tagged_select_next; [diff_tid |].
          apply tagged_select_next; [same_ok; discriminate |]. apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      (* t1's [Inc CX], and t1 returns 0 *)
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t1, 0)
                 (ti si t1 0 (Inc CX) (resolved_in (@empty_store F))))).
        - cbn. apply tagged_select_here.
        - cbn. exists 0, (1, 0). split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t1, 0) (tr_ si t1 0 (Inc CX) 0))).
        - cbn. apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_return V (Mnw_si si) t1 0 (SB CX) 0).
        - apply finish_next; [intros H; discriminate H |]. apply finish_here.
        - nin. }
      (* t2's [Inc CY], and t2 returns 0 *)
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t2, 0)
                 (ti si t2 0 (Inc CY) (resolved_in (@empty_store F))))).
        - cbn. apply tagged_select_here.
        - cbn. exists 0, (1, 1). split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mnw_si si) (@Build_TaggedScheduledEvent F GS (t2, 0) (tr_ si t2 0 (Inc CY) 0))).
        - cbn. apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_return V (Mnw_si si) t2 0 (SB CY) 0); [apply finish_here | intros []]. }
      apply tagged_module_execution_refl.
      reflexivity.
    Qed.

    Definition cltr (t : tid) (c : CLoc) (r : nat) : list (TaggedEvent F) :=
      [ti si t 0 (Inc c) (resolved_in (@empty_store F)); tr_ si t 0 (Inc c) 0;
       ti si t 1 (Get (other c)) (resolved_in [@Build_FutureEntry F 0 (@Resolved F (Inc c) 0)]);
       tr_ si t 1 (Get (other c)) r].

    Theorem sb_spec_live_gen :
      exists s (k1 k2 : CallKey GS),
        MTraces V (Mcl_si si) (s00, []) s /\
        In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s /\
        In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 1)) s.
    Proof.
      exists [gi t1 0 (SB CX); gr t1 0 (SB CX) 0; gi t2 0 (SB CY); gr t2 0 (SB CY) 1], (t1, 0), (t2, 0).
      split; [| split; cbn; tauto].
      do 2 eexists. split.
      (* t1: inc_x returns 0, then get_y returns 0 *)
      eapply tagged_module_execution_cons.
      { apply (tagged_invoke V (Mcl_si si) t1 0 (SB CX) (s00, []) [] [] [] (cltr t1 CX 0) 0).
        - intros [].
        - apply mcl_produces. discriminate.
        - fresh_tr. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t1, 0)
                 (ti si t1 0 (Inc CX) (resolved_in (@empty_store F))))).
        - cbn. apply tagged_select_here.
        - cbn. exists 0, (1, 0). split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t1, 0) (tr_ si t1 0 (Inc CX) 0))).
        - cbn. apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t1, 0)
                 (ti si t1 1 (Get CY) (resolved_in [@Build_FutureEntry F 0 (@Resolved F (Inc CX) 0)])))).
        - cbn. apply tagged_select_here.
        - cbn. exists 0, (1, 0). split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t1, 0) (tr_ si t1 1 (Get CY) 0))).
        - cbn. apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_return V (Mcl_si si) t1 0 (SB CX) 0); [apply finish_here | intros []]. }
      (* t2: inc_y returns 0, then get_x returns 1 *)
      eapply tagged_module_execution_cons.
      { apply (tagged_invoke V (Mcl_si si) t2 0 (SB CY) _ _ _ _ (cltr t2 CY 1) 1).
        - nin.
        - apply mcl_produces. discriminate.
        - fresh_tr. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t2, 0)
                 (ti si t2 0 (Inc CY) (resolved_in (@empty_store F))))).
        - cbn. apply tagged_select_here.
        - cbn. exists 0, (1, 1). split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t2, 0) (tr_ si t2 0 (Inc CY) 0))).
        - cbn. apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t2, 0)
                 (ti si t2 1 (Get CX) (resolved_in [@Build_FutureEntry F 0 (@Resolved F (Inc CY) 0)])))).
        - cbn. apply tagged_select_here.
        - cbn. exists 1, (1, 1). split; [split; reflexivity | reflexivity]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay V (Mcl_si si) (@Build_TaggedScheduledEvent F GS (t2, 0) (tr_ si t2 1 (Get CX) 1))).
        - cbn. apply tagged_select_here.
        - cbn. exists [], []. split; reflexivity. }
      eapply tagged_module_execution_cons.
      { apply (tagged_return V (Mcl_si si) t2 0 (SB CY) 1); [apply finish_here | intros []]. }
      apply tagged_module_execution_refl.
      reflexivity.
    Qed.
  End Witness.

  (** The waiting client over [EI δcxy] with [by_counter] is not vacuous:
      both calls can return, one of them with 0. *)
  Corollary sb_spec_live :
    exists s (k1 k2 : CallKey GS),
      MTraces (@RelaxedHoareSpec.EI FC MSt δcxy) (Mcl_si by_counter) (s00, []) s /\
      In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s /\
      In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 1)) s.
  Proof. exact (sb_spec_live_gen by_counter). Qed.

  (** [sb_nowait_si_decides] (the planned statement): under [by_counter]
      the no-wait client reaches (0, 0) over [EI δcxy]; under SI = ∅
      ([F0]) it does not, for any trace. *)
  Theorem sb_nowait_si_decides :
    (exists s (k1 k2 : CallKey GS),
       MTraces (@RelaxedHoareSpec.EI FC MSt δcxy) (Mnw_si by_counter) (s00, []) s /\
       In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s /\
       In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s) /\
    (forall s (k1 k2 : CallKey GS),
       MTraces (@RelaxedHoareSpec.EI F0 MSt δcxy) (Mnw_si (fun _ _ => False)) (s00, []) s ->
       In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s ->
       In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False).
  Proof.
    split.
    - apply sb_nowait_00_gen; cbn; discriminate.
    - apply sb_nowait_safe_gen. intros c [].
  Qed.

  (** Under the same [by_counter] specification, the [Wait] decides: the
      waiting client never sees (0, 0), the no-wait client can. *)
  Corollary sb_wait_decides :
    (forall s (k1 k2 : CallKey GS),
       MTraces (@RelaxedHoareSpec.EI FC MSt δcxy) (Mcl_si by_counter) (s00, []) s ->
       In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s ->
       In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s -> False) /\
    (exists s (k1 k2 : CallKey GS),
       MTraces (@RelaxedHoareSpec.EI FC MSt δcxy) (Mnw_si by_counter) (s00, []) s /\
       In (Build_ThreadEvent (fst k1) (@ResEv GS (snd k1) (SB CX) 0)) s /\
       In (Build_ThreadEvent (fst k2) (@ResEv GS (snd k2) (SB CY) 0)) s).
  Proof. exact (conj sb_client_spec (proj1 sb_nowait_si_decides)). Qed.

End RelaxedHoareClientSB.
