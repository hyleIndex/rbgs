(** * The inlined SeqLock tower module as a futures program

    [SeqLockProg] writes the SeqLock ⊎ client-cell module [M rc K] in the
    futures language over an atomic TicketLock ⊗ COH[x] ⊗ COH[y] ⊗ Barrier
    ⊗ COH[z], and proves that every method trace is the trace of one block
    of [SeqLockCOH] ([SeqLockProg.M_shape]).  [SeqLockTower] links the two
    layers at the level of underlay witnesses: the SeqLock code with the
    TicketLock code inlined, on

<<
    Counter[own] ⊗ COH[nxt] ⊗ COH[x] ⊗ COH[y] ⊗ Barrier ⊗ COH[z]
>>

    This file is the program half one level down: the inlined module [M0]
    written in the futures language over these low-level objects, and its
    shape lemma [M0_shape].  It is part 1 (task T-1) of the tower at module
    level; it contains no link theorem, no [rel_lin] statement, and nothing
    about buffered cells.

    Scope of the tower.  T-1..T-3 cover the TicketLock and SeqLock layers
    only.  The Counter is not inlined: [own] stays an object with
    categories [C] (as in [SeqLockTower]); of "Counter → TicketLock →
    SeqLock", the Counter layer itself (its implementation over a cell)
    is not part of this tower.

    Differences from the paper's printed code (Appendix/SeqLock.tex:5-45
    of ../async-ccal/drafts/relaxed-lin, TR only).  There [x], [y] and
    [next_ticket] are TSO cells (:8, :29), there is no [rmb]/[wmb] and no
    client cell [z]; the Counter is an imported object
    ([import owner : Counter], :7), implemented by [faa]/[rd] on a cell
    in a separate layer (figures/SeqLock.tex:29-56, [M_Counter^TSO] and
    [M_Counter^RC], a figure the current overview.tex no longer inputs).
    [M0] has COH cells [x], [y], [nxt], a Barrier object with
    [rmb]/[wmb] and the client cell [z] (the code of the [SeqLockCOH] /
    [TicketLockCOH] headers), and, like the paper's listing, keeps the
    Counter as an object.  The "⊗" above is the table-induced preserved
    order [SeqLockTower.lpres] (over [WindowTable.dto]), not
    [RelaxedSig]'s fence-mode tensor; the fence modes printed for the
    SeqLock are refuted for this COH variant with barriers, on the
    load-buffering execution [SeqLockCOH.X_lb]
    ([SeqLockCOH.paper_modes_fail]).

    - Underlay [E0 rc C]: the low-level calls of [SeqLockTower.LC] without
      their return values ([L0Op]): [nxt.faa(2)] ([oFaa], returns the old
      value), [own.get()] ([oGet]), [own.inc()] ([oInc]) and the data and
      barrier calls.  Two calls are semi-independent when the preserved
      order [SeqLockTower.lpres rc C] does not order them; it does not
      depend on return values ([lpres_ret_indep]).  [C] gives the
      categories of the Counter and of [nxt], as in [SeqLockTower].
    - Overlay: [SeqLockProg.F rc] (write, read, zw, zr), reused unchanged.
    - The module [M0 rc C]: the literal inlining of [SeqLockProg.M] with
      the TicketLock code of the headers of [SeqLockCOH] / [TicketLockCOH]
      ([acq = t <- nxt.faa(2); while (own.get() <> t) {}; own.inc()],
      [rel = own.inc()], [get_ticket = own.get()],
      [test_ticket(s) = (s & 1) || own.get() <> s]):
<<
    write(vx,vy) = fn <- ?nxt.faa(2); t <- wait fn;
                   do { fg <- ?own.get(); v <- wait fg } while (v <> t);
                   fa <- ?own.inc(); wait fa;
                   f1 <- ?wmb; f2 <- ?x.wrt(vx); f3 <- ?y.wrt(vy);
                   f4 <- ?wmb; f5 <- ?own.inc(); wait f1..f5
    read()       = fg <- ?own.get(); s <- wait fg; f1 <- ?rmb; fx <- ?x.rd(); fy <- ?y.rd();
                   f2 <- ?rmb;
                   r <- (if s odd then ret true
                         else ft <- ?own.get(); v <- wait ft; ret (v <> s));
                   wait f1; a <- wait fx; b <- wait fy; wait f2;
                   if r then read() else ret (a, b)
    zw(v)        = z.wrt(v)            zr() = z.rd()
>>
      Where [SeqLockProg.M] waits for a TicketLock operation, [M0] waits
      for the corresponding low-level calls: the ticket of [nxt.faa],
      every spin [own.get()], the final [own.inc()] of [acq] (the
      [wait fa] of [SeqLockProg.write]), the [own.get()] of [get_ticket],
      and the [own.get()] of a non-silent [test_ticket].  [rel]'s
      [own.inc()] is the future [f5], waited at the end as in
      [SeqLockProg.write].  [test_ticket(s)] with odd [s] makes no call
      at all (it is silent) and answers retry.  The spin of [acq] and the
      [read] loop are [CoFixpoint]s ([spin], [read], with [spin_unfold],
      [read_unfold]); [acq] and [test_ticket] are written with an explicit
      continuation, which is how their inlining reads in the shallow
      embedding.  Every invocation is an untagged [Future], as in
      [SeqLockProg].
    - Why the hand-inlining is literal.  In [SeqLockProg.M] every
      multi-call TicketLock operation ([acq], an even-[s] [test_ticket])
      is waited immediately, and the only TicketLock future that is not
      waited immediately ([f5 <- ?l.rel()]) is a single call, so it
      inlines as one [Future].  A multi-call method that is not waited
      immediately could not be inlined in this futures language without a
      fork construct.  [RelaxedLang] has no inlining or substitution
      operator, so no theorem relates [M0] to [SeqLockProg.M] composed
      with a TicketLock module: [M0] is one hand-inlined module, and its
      continuation-passing [acq k] equals a [bindProg] composition only up
      to bisimulation (not proved here).
    - [read()] follows the current SeqLock code: there is no prologue
      [rmb] before the first [get_ticket].  (Adding one is one of the ARM
      options the author has not decided; nothing here depends on that
      choice beyond the program text.)

    Main result: [M0_shape].  For [program_produces_tagged t (M0 rc C op t)
    tr ret] (a complete trace of a single method, from the empty store)
    there are a low-level block [k : SeqLockTower.LBlk] and a list [cs] of
    (handle, call) pairs such that
    - [SeqLockTower.lcalls k = map snd cs];
    - the invocations of [tr], in order, are
      [map (fun c => (fst c, op0_of (snd c))) cs], on pairwise distinct
      handles, and the responses are a permutation of [cs] (as calls,
      [res_list0]); every event is on thread [t];
    - [SeqLockTower.blk_ok k = true]: the failed iterations of a read
      answered retry and its last ticket [s] is even (that the last
      [test_ticket] read [s] is the form [liter s a b s] of [lcalls]);
    - [spin_ok k = true]: every spin value of a write's [acq] differs from
      its ticket.  This is a program fact that [blk_ok] does not record
      (it is [true] on every write block), so it is a separate conjunct;
    - [silent_r0 k = true]: a silent failed iteration is recorded with
      [r = 0], the choice of [SeqLockTower.X0_ex].  A silent [test_ticket]
      returns no value, so [r] is not determined by the trace;
      [lcalls], [blk_ok] and [abs] do not depend on it ([liter_silent],
      [iter_ok_silent]).  The conjunct fixes a canonical block, and it is
      needed: [lcalls] identifies blocks that differ only in the [r] of a
      silent iteration, so a decoder with [parse0 (lcalls k) = k] can hold
      only on [silent_r0] blocks ([parse0_lcalls]; T-3's analogue of
      [SeqLockModule.parse_calls]);
    - [SeqLockProg.blk_matches op (SeqLockTower.abs k) ret]: the
      SeqLock-layer block of [k] is that of the overlay operation and its
      return value.
    Corollaries: [M0_inv_fresh], [M0_shape_read], [M0_shape_write], and
    [M0_shape_decoded] ([M0_shape] with [k := parse0 (map snd cs)] and
    [cs := decode0 (map untag tr)], the analogue of
    [SeqLockModule.produced_shape]).

    Decoding, for T-3 (on [SeqLockTower]'s model only): [parse0] with
    [parse0_lcalls] ([silent_r0 k = true -> parse0 (lcalls k) = k]);
    [decode0] with [decode0_spec] (the (handle, call) list of a trace,
    as [SeqLockModule.decode]); the window call [wcall0 k] at index
    [lpi0 k] of [lcalls k] ([M0_window_index]): a write's first [wmb], at
    [length sp + 3] ([M0_window_first_wmb]: no earlier [wmb]), a read's
    first [rmb] of its last iteration, at
    [length (flat_map literq its) + 1] ([M0_window_last_iter]: the
    [get_ticket] of the last iteration is just before it).

    The junk clause of [op0_of].  [op0_of] sends the [LD] forms of
    SeqLock-layer TicketLock calls to [oInc]; they are not in the image
    of [uc0_of] and never occur in [M0_shape] ([cs] comes from [uc0_of];
    [lcalls_lc_ok]).  Bridges between [E0] and [SeqLockTower] must be
    stated on that image, the calls with [lc_ok c = true]: e.g.
    [sindep0_lpres] ([sindep0 (op0_of c) (op0_of c')] iff
    [lpres c c' = false] for [lc_ok] calls).  Stated for all calls it is
    false: [sindep0_lpres_junk] ([c = LD (SL.GT 0)], [c' = LD SL.WmbC],
    plain counter; [lcat C (LD (SL.GT v))] is [TL.k_get C], not
    [TL.k_inc C]).

    Proof machinery: [FuturesShape] (generic in the underlay signature;
    SeqLockProg.v is not modified).  The program-specific part is Section
    [Methods]: [spin_calls] (the spin loop, by induction on the trace
    length, ending in the continuation), [read_calls_gen], [write_calls],
    [zwrite_calls], [zread_calls], [M0_calls].

    Non-vacuity.  [M0_write_produces] (a [write(1,1)] whose [acq] takes
    ticket 2 and spins once, reading [own = 0]) and [M0_read_produces] (a
    [read()] whose first iteration has a silent [test_ticket(1)]: five
    invocations and no [own.get()] for the test; its second iteration
    succeeds with ticket 2) are concrete [program_produces_tagged]
    derivations.  Each states its invocation list and its response list
    [res_list0] with all values.  [M0_read_block] / [M0_write_block] pin
    the block: every [k] with the conjuncts of [M0_shape] on that trace
    is [LBR [(1, 0, 0, 0)] 2 1 1] (the reader's block of
    [SeqLockTower.X0_ex]) / [LBW 1 1 2 [0]], and so is the block of
    [M0_shape_decoded].  So the hypothesis of [M0_shape] is satisfiable
    for a looping write and a looping read with a silent [test_ticket];
    [M0_shape_nonvacuous] applies [M0_shape] to both.  These are
    single-thread, single-method traces: they say nothing about
    module-level executions.

    Sanity check: [M_shape_via_FS] has exactly the type of
    [SeqLockProg.M_shape] and is proved from [FuturesShape.exec_shape],
    [SeqLockProg.M_calls] and the bridge [res_list_SLP].

    For T-3: [inv_list_SLP] identifies [FuturesShape.inv_list] with
    [SeqLockProg.inv_list].

    Scope: complete traces of single methods, from the empty store; no
    module-level execution, no underlay specification. *)

From Stdlib Require Import List Bool Arith.PeanoNat micromega.Lia.
From Stdlib Require Import Sorting.Permutation.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.TicketLockCOH.
Require Import examples.Relaxed.SeqLockProg.
Require Import examples.Relaxed.SeqLockTower.
Require Import examples.Relaxed.FuturesShape.

Import ListNotations.

Module SeqLockTowerProg.
  Module SL := SeqLockCOH.
  Module TL := TicketLockCOH.
  Module ST := SeqLockTower.
  Module SLP := SeqLockProg.
  Module FS := FuturesShape.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import FS.

  (** ** Underlay signature *)

  Inductive L0Op : Type :=
  | oFaa                                 (* nxt.faa(2), returns the old value *)
  | oGet                                 (* own.get() *)
  | oInc                                 (* own.inc() *)
  | oWrX (v : nat) | oWrY (v : nat) | oRdX | oRdY
  | oWmb | oRmb
  | oWrZ (v : nat) | oRdZ.

  Definition L0Op_eq_dec (a b : L0Op) : {a = b} + {a <> b}.
  Proof. decide equality; apply Nat.eq_dec. Defined.

  Definition l0ar (o : L0Op) : Type :=
    match o with
    | oFaa | oGet | oRdX | oRdY | oRdZ => nat
    | _ => unit
    end.

  Definition L0Sig : Sig.t := {| Sig.op := L0Op; Sig.ar := l0ar |}.

  (** The call of [SeqLockTower] made by an operation with a given return
      value, and back. *)
  Definition uc0_of (o : L0Op) : @Sig.ar L0Sig o -> ST.LC :=
    match o as o0 return @Sig.ar L0Sig o0 -> ST.LC with
    | oFaa => fun r => ST.LT (TL.FaaN r)
    | oGet => fun v => ST.LT (TL.GetO v)
    | oInc => fun _ => ST.LT TL.IncO
    | oWrX v => fun _ => ST.LD (SL.WrX v)
    | oWrY v => fun _ => ST.LD (SL.WrY v)
    | oRdX => fun v => ST.LD (SL.RdX v)
    | oRdY => fun v => ST.LD (SL.RdY v)
    | oWmb => fun _ => ST.LD SL.WmbC
    | oRmb => fun _ => ST.LD SL.RmbC
    | oWrZ v => fun _ => ST.LD (SL.WrZ v)
    | oRdZ => fun v => ST.LD (SL.RdZ v)
    end.

  (** The [LD] forms of SeqLock-layer TicketLock calls ([SL.Acq], [SL.Rel],
      [SL.GT], [SL.TT]) are not low-level calls ([uc0_of] never produces
      them); they are sent to [oInc] arbitrarily. *)
  Definition op0_of (c : ST.LC) : L0Op :=
    match c with
    | ST.LT (TL.FaaN _) => oFaa
    | ST.LT (TL.GetO _) => oGet
    | ST.LT TL.IncO => oInc
    | ST.LD (SL.WrX v) => oWrX v
    | ST.LD (SL.WrY v) => oWrY v
    | ST.LD (SL.RdX _) => oRdX
    | ST.LD (SL.RdY _) => oRdY
    | ST.LD SL.WmbC => oWmb
    | ST.LD SL.RmbC => oRmb
    | ST.LD (SL.WrZ v) => oWrZ v
    | ST.LD (SL.RdZ _) => oRdZ
    | ST.LD (SL.Acq | SL.Rel | SL.GT _ | SL.TT _ _) => oInc
    end.

  Lemma op0_of_uc o v : op0_of (uc0_of o v) = o.
  Proof. destruct o; reflexivity. Qed.

  Definition dflt0 (o : L0Op) : @Sig.ar L0Sig o :=
    match o as o0 return @Sig.ar L0Sig o0 with
    | oFaa | oGet | oRdX | oRdY | oRdZ => 0
    | oInc | oWrX _ | oWrY _ | oWmb | oRmb | oWrZ _ => tt
    end.

  Lemma lobj_ret_indep o v : ST.lobj (uc0_of o v) = ST.lobj (uc0_of o (dflt0 o)).
  Proof. destruct o; reflexivity. Qed.

  Lemma lcat_ret_indep C o v : ST.lcat C (uc0_of o v) = ST.lcat C (uc0_of o (dflt0 o)).
  Proof. destruct o; reflexivity. Qed.

  (** The preserved order does not depend on return values. *)
  Lemma lpres_ret_indep rc C o o' v v' :
    ST.lpres rc C (uc0_of o v) (uc0_of o' v') =
    ST.lpres rc C (uc0_of o (dflt0 o)) (uc0_of o' (dflt0 o')).
  Proof.
    unfold ST.lpres.
    rewrite (lobj_ret_indep o v), (lobj_ret_indep o' v'), (lcat_ret_indep C o v), (lcat_ret_indep C o' v').
    reflexivity.
  Qed.

  Definition sindep0 (rc : bool) (C : TL.CCats) (o o' : L0Op) : Prop :=
    ST.lpres rc C (uc0_of o (dflt0 o)) (uc0_of o' (dflt0 o')) = false.

  Definition E0 (rc : bool) (C : TL.CCats) : RelaxedSig.t :=
    {| effect := L0Sig; handle := nat; semi_independent := sindep0 rc C; mode := fun _ => Local |}.

  (** [FuturesShape.inv_list] is [SeqLockProg.inv_list]. *)
  Lemma inv_list_SLP {G : RelaxedSig.t} (l : list (ThreadEvent G)) : inv_list l = SLP.inv_list l.
  Proof. induction l as [|[? []] l IH]; cbn; [reflexivity | rewrite IH; reflexivity | exact IH]. Qed.

  (** Responses, in order, as calls of [SeqLockTower]. *)
  Definition res_list0 {rc C} (l : list (ThreadEvent (E0 rc C))) : list (nat * ST.LC) :=
    @FS.res_list (E0 rc C) ST.LC uc0_of l.

  (** The image of [uc0_of]: [LT] calls and the data and barrier [LD]
      calls.  [op0_of] is meaningful only there (its junk clause sends
      [LD SL.Acq], [LD SL.Rel], [LD (SL.GT _)], [LD (SL.TT _ _)] to [oInc],
      although e.g. [ST.lcat C (ST.LD (SL.GT v))] is not [TL.k_inc C]);
      bridges between [E0] and [SeqLockTower] are stated on [lc_ok] calls
      ([sindep0_lpres]), and every call of a block is one
      ([lcalls_lc_ok]). *)
  Definition lc_ok (c : ST.LC) : bool :=
    match c with ST.LD (SL.Acq | SL.Rel | SL.GT _ | SL.TT _ _) => false | _ => true end.

  Lemma lc_ok_uc0 o v : lc_ok (uc0_of o v) = true.
  Proof. destruct o; reflexivity. Qed.

  Lemma lc_ok_inv c : lc_ok c = true -> exists v : @Sig.ar L0Sig (op0_of c), c = uc0_of (op0_of c) v.
  Proof.
    destruct c as [[r | v |] | [| | s | s r | v | v | v | v | | | v | v]]; cbn; try discriminate; intros _;
      first [exists tt; reflexivity | eexists; reflexivity].
  Qed.

  (** On [lc_ok] calls, [sindep0] of their operations is exactly the
      complement of [SeqLockTower.lpres]. *)
  Lemma sindep0_lpres rc C c c' : lc_ok c = true -> lc_ok c' = true ->
    (sindep0 rc C (op0_of c) (op0_of c') <-> ST.lpres rc C c c' = false).
  Proof.
    intros H H'. destruct (lc_ok_inv c H) as (v & Ev). destruct (lc_ok_inv c' H') as (v' & Ev').
    unfold sindep0. rewrite <- (lpres_ret_indep rc C _ _ v v'), <- Ev, <- Ev'. reflexivity.
  Qed.

  (** Off the image of [uc0_of] the bridge fails. *)
  Example sindep0_lpres_junk :
    ~ (sindep0 false TL.plainC (op0_of (ST.LD (SL.GT 0))) (op0_of (ST.LD SL.WmbC)) <->
       ST.lpres false TL.plainC (ST.LD (SL.GT 0)) (ST.LD SL.WmbC) = false).
  Proof. intros [_ H]. specialize (H eq_refl). unfold sindep0 in H. cbn in H. discriminate H. Qed.

  (** ** The module *)

  Section Programs.
    Context (rc : bool) (C : TL.CCats).
    Local Abbreviation G := (E0 rc C).

    (** [while (own.get() <> t) {}], then [k]. *)
    Definition spin_body {R} (t : nat) (k loop : Prog G R) : Prog G R :=
      Future (E := G) oGet (fun fg => Wait fg (fun v =>
      if Nat.eqb v t then k else Tau loop)).

    CoFixpoint spin {R} (t : nat) (k : Prog G R) : Prog G R := spin_body t k (spin t k).

    Lemma spin_unfold {R} t (k : Prog G R) : spin t k = spin_body t k (spin t k).
    Proof. exact (PPid (spin t k)). Qed.

    (** [acq() = t <- nxt.faa(2); while (own.get() <> t) {}; own.inc()],
        waited, then [k]. *)
    Definition acq {R} (k : Prog G R) : Prog G R :=
      Future (E := G) oFaa (fun fn => Wait fn (fun t =>
      spin t (Future (E := G) oInc (fun fa => Wait fa (fun _ => k))))).

    Definition write (vx vy : nat) : Prog G unit :=
      acq (
      Future (E := G) oWmb (fun f1 =>
      Future (E := G) (oWrX vx) (fun f2 =>
      Future (E := G) (oWrY vy) (fun f3 =>
      Future (E := G) oWmb (fun f4 =>
      Future (E := G) oInc (fun f5 =>
      Wait f1 (fun _ => Wait f2 (fun _ => Wait f3 (fun _ => Wait f4 (fun _ => Wait f5 (fun _ =>
      Ret tt))))))))))).

    (** [test_ticket(s) = (s & 1) || own.get() <> s], then [k]: silent
        (no call, answer retry) for odd [s]. *)
    Definition test_ticket {R} (s : nat) (k : bool -> Prog G R) : Prog G R :=
      if Nat.odd s then k true
      else Future (E := G) oGet (fun ft => Wait ft (fun v => k (negb (Nat.eqb v s)))).

    (** One iteration of [read], parameterised by the loop. *)
    Definition read_body (loop : Prog G (nat * nat)) : Prog G (nat * nat) :=
      Future (E := G) oGet (fun fg => Wait fg (fun s =>
      Future (E := G) oRmb (fun f1 =>
      Future (E := G) oRdX (fun fx =>
      Future (E := G) oRdY (fun fy =>
      Future (E := G) oRmb (fun f2 =>
      test_ticket s (fun r =>
      Wait f1 (fun _ => Wait fx (fun a => Wait fy (fun b => Wait f2 (fun _ =>
      if r then Tau loop else Ret ((a : nat), (b : nat))))))))))))).

    CoFixpoint read : Prog G (nat * nat) := read_body read.

    Lemma read_unfold : read = read_body read.
    Proof. exact (PPid read). Qed.

    Definition zwrite (v : nat) : Prog G unit :=
      Future (E := G) (oWrZ v) (fun f => Wait f (fun _ => Ret tt)).

    Definition zread : Prog G nat :=
      Future (E := G) oRdZ (fun f => Wait f (fun v => Ret v)).

    Definition M0 : RelaxedModuleImpl G (SLP.F rc) := fun op _ =>
      match op as o return Prog G (@Sig.ar (effect (SLP.F rc)) o) with
      | SLP.fWrite vx vy => write vx vy
      | SLP.fRead => read
      | SLP.fZw v => zwrite v
      | SLP.fZr => zread
      end.
  End Programs.

  (** ** Program facts on low-level blocks *)

  (** Every spin value of a write's [acq] differs from its ticket. *)
  Definition spin_ok (k : ST.LBlk) : bool :=
    match k with ST.LBW _ _ tk sp => forallb (fun v => negb (Nat.eqb v tk)) sp | _ => true end.

  (** A silent failed iteration (odd [s]) is recorded with [r = 0]. *)
  Definition silent_r0 (k : ST.LBlk) : bool :=
    match k with
    | ST.LBR its _ _ _ => forallb (fun it => let '(s, _, _, r) := it in implb (Nat.odd s) (Nat.eqb r 0)) its
    | _ => true
    end.

  (** The value [r] of a silent iteration is irrelevant to its calls and
      to [iter_ok] ([ST.abs] drops it). *)
  Lemma liter_silent s a b r r' : Nat.odd s = true -> ST.liter s a b r = ST.liter s a b r'.
  Proof. intros H. unfold ST.liter. cbn [TL.tcalls]. rewrite H. reflexivity. Qed.

  Lemma iter_ok_silent s a b r : Nat.odd s = true -> ST.iter_ok (s, a, b, r) = true.
  Proof. intros H. cbn. rewrite H. reflexivity. Qed.

  Lemma tcalls_tt_odd s r : Nat.odd s = true -> TL.tcalls (TL.TTt s r) = [].
  Proof. intros H. cbn. rewrite H. reflexivity. Qed.

  Lemma tcalls_tt_even s r : Nat.odd s = false -> TL.tcalls (TL.TTt s r) = [TL.GetO r].
  Proof. intros H. cbn. rewrite H. reflexivity. Qed.

  Lemma liter_odd s a b r : Nat.odd s = true ->
    ST.liter s a b r = [ST.LT (TL.GetO s); ST.LD SL.RmbC; ST.LD (SL.RdX a); ST.LD (SL.RdY b); ST.LD SL.RmbC].
  Proof. intros H. unfold ST.liter. rewrite (tcalls_tt_odd _ _ H). reflexivity. Qed.

  Lemma liter_even s a b r : Nat.odd s = false ->
    ST.liter s a b r =
    [ST.LT (TL.GetO s); ST.LD SL.RmbC; ST.LD (SL.RdX a); ST.LD (SL.RdY b); ST.LD SL.RmbC; ST.LT (TL.GetO r)].
  Proof. intros H. unfold ST.liter. rewrite (tcalls_tt_even _ _ H). reflexivity. Qed.

  Lemma blk_ok_cons it its s a b :
    ST.iter_ok it = true -> ST.blk_ok (ST.LBR its s a b) = true -> ST.blk_ok (ST.LBR (it :: its) s a b) = true.
  Proof.
    cbn [ST.blk_ok forallb]. intros H1 H2. apply andb_true_iff in H2 as [H2 H3].
    rewrite H1, H2, H3. reflexivity.
  Qed.

  Lemma silent_r0_cons s0 a0 b0 r0 its s a b :
    implb (Nat.odd s0) (Nat.eqb r0 0) = true -> silent_r0 (ST.LBR its s a b) = true ->
    silent_r0 (ST.LBR ((s0, a0, b0, r0) :: its) s a b) = true.
  Proof. cbn [silent_r0 forallb]. intros H1 H2. rewrite H1, H2. reflexivity. Qed.

  Lemma spin_ok_of tk sp vx vy : Forall (fun v => v <> tk) sp -> spin_ok (ST.LBW vx vy tk sp) = true.
  Proof.
    intros H. cbn [spin_ok]. apply forallb_forall. intros v Hv.
    rewrite Forall_forall in H. apply negb_true_iff, Nat.eqb_neq, H, Hv.
  Qed.

  Lemma lcalls_LBW vx vy tk sp :
    ST.lcalls (ST.LBW vx vy tk sp) =
    [ST.LT (TL.FaaN tk)] ++ map ST.LT (map TL.GetO sp ++ [TL.GetO tk]) ++
    [ST.LT TL.IncO; ST.LD SL.WmbC; ST.LD (SL.WrX vx); ST.LD (SL.WrY vy); ST.LD SL.WmbC; ST.LT TL.IncO].
  Proof.
    cbn [ST.lcalls TL.tcalls]. cbn [map app]. rewrite map_app, map_app. cbn [map app].
    rewrite <- !app_assoc. reflexivity.
  Qed.

  (** ** Decoding low-level blocks (for T-3)

      These concern [SeqLockTower]'s model only. *)

  (** Every call of a block is in the image of [uc0_of]. *)
  Lemma forallb_lc_ok_LT l : forallb lc_ok (map ST.LT l) = true.
  Proof. induction l; cbn; auto. Qed.

  Lemma liter_lc_ok s a b r : forallb lc_ok (ST.liter s a b r) = true.
  Proof. unfold ST.liter. rewrite !forallb_app, !forallb_lc_ok_LT. reflexivity. Qed.

  Lemma lcalls_lc_ok k : forallb lc_ok (ST.lcalls k) = true.
  Proof.
    destruct k as [vx vy tk sp | its s a b | v | v]; cbn [ST.lcalls]; [| | reflexivity | reflexivity].
    - rewrite !forallb_app, !forallb_lc_ok_LT. reflexivity.
    - rewrite forallb_app, liter_lc_ok, andb_true_r.
      induction its as [|[[[s0 a0] b0] r0] its IH]; [reflexivity |].
      cbn [flat_map ST.literq]. rewrite forallb_app, IH, andb_true_r. apply liter_lc_ok.
  Qed.

  (** The gets at the head of a list, and the rest. *)
  Fixpoint pw (l : list ST.LC) : list nat * list ST.LC :=
    match l with
    | ST.LT (TL.GetO v) :: l' => let '(g, r) := pw l' in (v :: g, r)
    | _ => ([], l)
    end.

  (** The iterations of a read: a silent one (odd [s]) is recorded with
      [r = 0]; the last iteration is the one that ends the list. *)
  Fixpoint pr (l : list ST.LC) : list (nat * nat * nat * nat) * (nat * nat * nat) :=
    match l with
    | ST.LT (TL.GetO s) :: ST.LD SL.RmbC :: ST.LD (SL.RdX a) :: ST.LD (SL.RdY b) :: ST.LD SL.RmbC :: rest =>
        if Nat.odd s then
          match rest with
          | [] => ([], (s, a, b))
          | _ :: _ => let '(its, f) := pr rest in ((s, a, b, 0) :: its, f)
          end
        else
          match rest with
          | ST.LT (TL.GetO r) :: rest' =>
              match rest' with
              | [] => ([], (s, a, b))
              | _ :: _ => let '(its, f) := pr rest' in ((s, a, b, r) :: its, f)
              end
          | _ => ([], (s, a, b))
          end
    | _ => ([], (0, 0, 0))
    end.

  (** The block of a list of calls ([ST.LBZr 0] on lists that are no
      block's calls). *)
  Definition parse0 (l : list ST.LC) : ST.LBlk :=
    match l with
    | ST.LT (TL.FaaN tk) :: rest =>
        match pw rest with
        | (g, ST.LT TL.IncO :: ST.LD SL.WmbC :: ST.LD (SL.WrX vx) :: ST.LD (SL.WrY vy) :: _) =>
            ST.LBW vx vy tk (removelast g)
        | _ => ST.LBZr 0
        end
    | ST.LT (TL.GetO _) :: _ => let '(its, (s, a, b)) := pr l in ST.LBR its s a b
    | ST.LD (SL.WrZ v) :: _ => ST.LBZw v
    | ST.LD (SL.RdZ v) :: _ => ST.LBZr v
    | _ => ST.LBZr 0
    end.

  Lemma pw_spin sp tk rest :
    pw (map ST.LT (map TL.GetO sp) ++ ST.LT (TL.GetO tk) :: ST.LT TL.IncO :: rest) =
    (sp ++ [tk], ST.LT TL.IncO :: rest).
  Proof. induction sp as [|v sp IH]; cbn; [reflexivity | rewrite IH; reflexivity]. Qed.

  Lemma pr_step_odd s a b y rest : Nat.odd s = true ->
    pr (ST.LT (TL.GetO s) :: ST.LD SL.RmbC :: ST.LD (SL.RdX a) :: ST.LD (SL.RdY b) :: ST.LD SL.RmbC :: y :: rest) =
    let '(its, f) := pr (y :: rest) in ((s, a, b, 0) :: its, f).
  Proof. intros H. simpl pr at 1. rewrite H. reflexivity. Qed.

  Lemma pr_step_even s a b r y rest : Nat.odd s = false ->
    pr (ST.LT (TL.GetO s) :: ST.LD SL.RmbC :: ST.LD (SL.RdX a) :: ST.LD (SL.RdY b) :: ST.LD SL.RmbC
          :: ST.LT (TL.GetO r) :: y :: rest) =
    let '(its, f) := pr (y :: rest) in ((s, a, b, r) :: its, f).
  Proof. intros H. simpl pr at 1. rewrite H. reflexivity. Qed.

  Lemma pr_lcalls its s a b :
    silent_r0 (ST.LBR its s a b) = true -> pr (flat_map ST.literq its ++ ST.liter s a b s) = (its, (s, a, b)).
  Proof.
    induction its as [|[[[s0 a0] b0] r0] its IH]; intros Hr0.
    - cbn [flat_map app]. destruct (Nat.odd s) eqn:Hodd.
      + rewrite (liter_odd s a b s Hodd). cbn [app pr]. rewrite Hodd. reflexivity.
      + rewrite (liter_even s a b s Hodd). cbn [app pr]. rewrite Hodd. reflexivity.
    - cbn [silent_r0 forallb] in Hr0. apply andb_true_iff in Hr0 as [H0 Hr0].
      specialize (IH Hr0).
      cbn [flat_map ST.literq]. rewrite <- app_assoc.
      destruct (flat_map ST.literq its ++ ST.liter s a b s) as [|x T] eqn:ET.
      + exfalso. apply (f_equal (@length _)) in ET. rewrite length_app in ET.
        unfold ST.liter in ET. rewrite !length_app in ET. cbn in ET. lia.
      + destruct (Nat.odd s0) eqn:Hodd.
        * cbn [implb] in H0. apply Nat.eqb_eq in H0. subst r0.
          rewrite (liter_odd s0 a0 b0 0 Hodd). cbn [app]. rewrite (pr_step_odd _ _ _ _ _ Hodd), IH. reflexivity.
        * rewrite (liter_even s0 a0 b0 r0 Hodd). cbn [app]. rewrite (pr_step_even _ _ _ _ _ _ Hodd), IH. reflexivity.
  Qed.

  (** [lcalls] identifies blocks that differ only in the [r] of a silent
      iteration; on [silent_r0] blocks [parse0] inverts it. *)
  Lemma parse0_lcalls k : silent_r0 k = true -> parse0 (ST.lcalls k) = k.
  Proof.
    destruct k as [vx vy tk sp | its s a b | v | v]; intros Hr0; [| | reflexivity | reflexivity].
    - rewrite lcalls_LBW, map_app, <- app_assoc. cbn [app map parse0].
      rewrite pw_spin. cbn beta iota. rewrite removelast_last. reflexivity.
    - assert (Hh : exists x l', ST.lcalls (ST.LBR its s a b) = ST.LT (TL.GetO x) :: l').
      { destruct its as [|[[[s0 a0] b0] r0] its']; cbn [ST.lcalls flat_map ST.literq app];
          [| rewrite <- app_assoc]; unfold ST.liter at 1; cbn [TL.tcalls map app]; eauto. }
      destruct Hh as (x & l' & E).
      transitivity (let '(its0, (s0, a0, b0)) := pr (ST.lcalls (ST.LBR its s a b)) in ST.LBR its0 s0 a0 b0).
      + rewrite E. reflexivity.
      + cbn [ST.lcalls]. rewrite (pr_lcalls its s a b Hr0). reflexivity.
  Qed.

  (** The window call of a block ([wcall0]) and its index in [lcalls]
      ([lpi0]): a write's first [wmb], a read's first [rmb] of its last
      iteration, a client call itself. *)
  Definition lpi0 (k : ST.LBlk) : nat :=
    match k with
    | ST.LBW _ _ _ sp => length sp + 3
    | ST.LBR its _ _ _ => length (flat_map ST.literq its) + 1
    | ST.LBZw _ | ST.LBZr _ => 0
    end.

  Definition wcall0 (k : ST.LBlk) : ST.LC :=
    match k with
    | ST.LBW _ _ _ _ => ST.LD SL.WmbC
    | ST.LBR _ _ _ _ => ST.LD SL.RmbC
    | ST.LBZw v => ST.LD (SL.WrZ v)
    | ST.LBZr v => ST.LD (SL.RdZ v)
    end.

  Lemma length_sp1 sp tk : length (map ST.LT (map TL.GetO sp ++ [TL.GetO tk])) = length sp + 1.
  Proof. rewrite length_map, length_app, length_map. reflexivity. Qed.

  Lemma M0_window_index k : nth_error (ST.lcalls k) (lpi0 k) = Some (wcall0 k).
  Proof.
    destruct k as [vx vy tk sp | its s a b | v | v]; [| | reflexivity | reflexivity]; cbn [lpi0 wcall0].
    - rewrite lcalls_LBW, nth_error_app2 by (cbn; lia). cbn [length].
      rewrite nth_error_app2 by (rewrite length_sp1; lia). rewrite length_sp1.
      replace (length sp + 3 - 1 - (length sp + 1)) with 1 by lia. reflexivity.
    - cbn [ST.lcalls]. rewrite nth_error_app2 by lia.
      replace (length (flat_map ST.literq its) + 1 - length (flat_map ST.literq its)) with 1 by lia.
      reflexivity.
  Qed.

  (** The window of a write is its first [wmb]. *)
  Lemma M0_window_first_wmb vx vy tk sp i :
    i < length sp + 3 -> nth_error (ST.lcalls (ST.LBW vx vy tk sp)) i <> Some (ST.LD SL.WmbC).
  Proof.
    intros Hi. rewrite lcalls_LBW. destruct i as [|i]; [cbn; discriminate |].
    cbn [app nth_error].
    destruct (Nat.lt_ge_cases i (length sp + 1)) as [Hl | Hge].
    - rewrite nth_error_app1 by (rewrite length_sp1; lia).
      rewrite nth_error_map. destruct (nth_error _ i); cbn; congruence.
    - rewrite nth_error_app2 by (rewrite length_sp1; lia). rewrite length_sp1.
      replace (i - (length sp + 1)) with 0 by lia. cbn. discriminate.
  Qed.

  (** The window of a read is in its last iteration, right after its
      [get_ticket]. *)
  Lemma M0_window_last_iter its s a b :
    nth_error (ST.lcalls (ST.LBR its s a b)) (length (flat_map ST.literq its)) = Some (ST.LT (TL.GetO s)).
  Proof.
    cbn [ST.lcalls]. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
  Qed.

  (** The (handle, call) list of a method trace: the invocations in
      order, each with the response to its handle (the analogue of
      [SeqLockModule.decode]). *)
  Fixpoint res_find0 (h : nat) (l : list (nat * ST.LC)) : option ST.LC :=
    match l with
    | [] => None
    | (h', c) :: l' => if Nat.eqb h h' then Some c else res_find0 h l'
    end.

  Lemma res_find0_in h c l : NoDup (map fst l) -> In (h, c) l -> res_find0 h l = Some c.
  Proof.
    induction l as [|[h' c'] l IH]; cbn; [intros _ [] |].
    intros Hnd Hin. inversion Hnd as [|? ? Hni Hnd']; subst.
    destruct Hin as [E | Hin].
    - injection E as -> ->. rewrite Nat.eqb_refl. reflexivity.
    - destruct (Nat.eqb_spec h h') as [-> | Hne].
      + exfalso. apply Hni. apply (in_map fst) in Hin. exact Hin.
      + apply IH; assumption.
  Qed.

  Definition decode0 {rc C} (l : list (ThreadEvent (E0 rc C))) : list (nat * ST.LC) :=
    map (fun ho => (fst ho, match res_find0 (fst ho) (res_list0 l) with Some c => c | None => ST.LT TL.IncO end))
        (inv_list l).

  Lemma decode0_spec {rc C} (l : list (ThreadEvent (E0 rc C))) (cs : list (nat * ST.LC)) :
    inv_list l = map (fun c => (fst c, op0_of (snd c))) cs -> NoDup (map fst cs) ->
    Permutation (res_list0 l) cs -> decode0 l = cs.
  Proof.
    intros Hinv Hnd Hp. unfold decode0. rewrite Hinv, map_map.
    transitivity (map (fun c => c) cs); [| apply map_id].
    apply map_ext_in. intros [h c] Hin. cbn.
    rewrite (res_find0_in h c (res_list0 l)); [reflexivity | |].
    - apply (Permutation_NoDup (Permutation_map fst (Permutation_sym Hp))). exact Hnd.
    - apply (Permutation_in _ (Permutation_sym Hp)). exact Hin.
  Qed.

  (** ** The calls of each method *)

  Section Methods.
    Context (rc : bool) (C : TL.CCats) (t : tid).
    Local Abbreviation G := (E0 rc C).
    Local Abbreviation eu := (@entry_uc G ST.LC uc0_of dflt0).

    (** The spin of [acq]: some gets [sp], all different from [t0], then
        a get of [t0], then the continuation [k]. *)
    Lemma spin_calls_gen {R} t0 (k : Prog G R) n : forall S H tr (c' : ProgramConfig G R) r,
      length tr < n -> store_well_formed H -> refines S H ->
      program_execution_tagged t (Build_ProgramConfig (spin rc C t0 k) H) tr c' -> program_terminal c' r ->
      exists N sp H' tr', all_resolved N /\ store_well_formed H' /\ refines (N ++ S) H' /\
        program_execution_tagged t (Build_ProgramConfig k H') tr' c' /\
        map snd (rev (map eu N)) = map ST.LT (map TL.GetO sp ++ [TL.GetO t0]) /\
        Forall (fun v => v <> t0) sp.
    Proof.
      induction n as [|n IH]; intros S H tr c' r Hlt Hw Hr Hx Hterm; [lia |].
      rewrite spin_unfold in Hx. unfold spin_body in Hx.
      fut hg. wt (@nil (FutureEntry G)) v.
      grab. destruct (Nat.eqb v t0) eqn:Ev; cbn beta iota in Hx_.
      - (* exit *)
        apply Nat.eqb_eq in Ev. subst v.
        eexists [Build_FutureEntry hg (Resolved (E := G) oGet t0)], [], _, _.
        split; [repeat constructor |]. split; [exact Hw_ |]. split; [exact Hr_ |].
        split; [exact Hx_ |]. split; [reflexivity | constructor].
      - (* spin again *)
        apply Nat.eqb_neq in Ev.
        destruct (exec_tau Hx_ Hterm Hw_ Hr_) as (H' & tr' & Hw' & Hr' & Hx' & Hl').
        destruct (IH _ _ tr' _ _ ltac:(lia) Hw' Hr' Hx' Hterm)
          as (N & sp & H'' & tr'' & Hall & Hw'' & Hf & Hx'' & Hc & Hsp).
        exists (N ++ [Build_FutureEntry hg (Resolved (E := G) oGet v)]), (v :: sp), H'', tr''.
        split; [apply Forall_app; split; [exact Hall | repeat constructor] |].
        split; [exact Hw'' |]. split; [rewrite <- app_assoc; exact Hf |].
        split; [exact Hx'' |]. split; [| constructor; assumption].
        rewrite map_app, rev_app_distr, map_app, Hc. reflexivity.
    Qed.

    Lemma spin_calls {R} t0 (k : Prog G R) S H tr (c' : ProgramConfig G R) r :
      store_well_formed H -> refines S H ->
      program_execution_tagged t (Build_ProgramConfig (spin rc C t0 k) H) tr c' -> program_terminal c' r ->
      exists N sp H' tr', all_resolved N /\ store_well_formed H' /\ refines (N ++ S) H' /\
        program_execution_tagged t (Build_ProgramConfig k H') tr' c' /\
        map snd (rev (map eu N)) = map ST.LT (map TL.GetO sp ++ [TL.GetO t0]) /\
        Forall (fun v => v <> t0) sp.
    Proof. intros Hw Hr Hx Hterm. exact (spin_calls_gen t0 k (Datatypes.S (length tr)) S H tr c' r ltac:(lia) Hw Hr Hx Hterm). Qed.

    Lemma write_calls vx vy tr (c' : ProgramConfig G unit) r :
      program_execution_tagged t (initial_program (write rc C vx vy)) tr c' -> program_terminal c' r ->
      exists tk sp, map snd (rev (map eu (pc_futures c'))) = ST.lcalls (ST.LBW vx vy tk sp) /\
        Forall (fun v => v <> tk) sp.
    Proof.
      intros Hx Hterm. unfold initial_program, write, acq in Hx.
      assert (Hw : store_well_formed (@empty_store G)) by constructor.
      assert (Hr : refines [] (@empty_store G)) by constructor.
      fut hn. wt (@nil (FutureEntry G)) tk.
      grab. destruct (spin_calls tk _ _ _ _ _ _ Hw_ Hr_ Hx_ Hterm)
        as (N & sp & H' & tr' & Hall & Hw & Hr & Hx & Hc & Hsp).
      clear Hx_ Hw_ Hr_. cbn beta in Hx.
      fut ha. wt (@nil (FutureEntry G)) u0.
      fut h1. fut h2. fut h3. fut h4. fut h5.
      wt [_; _; _; _] u1. wt [_; _; _] u2. wt [_; _] u3. wt [_] u4. wt (@nil (FutureEntry G)) u5.
      grab. destruct (exec_ret Hx_ Hterm Hr_) as (_ & Hf & _).
      apply refines_resolved_eq in Hf;
        [| repeat (apply Forall_cons; [exact I |]); apply Forall_app; split; [exact Hall | repeat constructor]].
      exists tk, sp. split; [| exact Hsp]. rewrite Hf.
      match goal with |- context [map eu (?a1 :: ?a2 :: ?a3 :: ?a4 :: ?a5 :: ?a6 :: N ++ ?l)] =>
        change (a1 :: a2 :: a3 :: a4 :: a5 :: a6 :: N ++ l) with ([a1; a2; a3; a4; a5; a6] ++ N ++ l) end.
      rewrite !map_app, !rev_app_distr, !map_app, Hc, lcalls_LBW, <- app_assoc. reflexivity.
    Qed.

    Lemma read_calls_gen n : forall S H tr (c' : ProgramConfig G (nat * nat)) r,
      length tr < n -> store_well_formed H -> refines S H ->
      program_execution_tagged t (Build_ProgramConfig (read rc C) H) tr c' -> program_terminal c' r ->
      exists N its s a b, all_resolved N /\ refines (N ++ S) (pc_futures c') /\
        map snd (rev (map eu N)) = ST.lcalls (ST.LBR its s a b) /\
        ST.blk_ok (ST.LBR its s a b) = true /\ silent_r0 (ST.LBR its s a b) = true /\ r = (a, b).
    Proof.
      induction n as [|n IH]; intros S H tr c' r Hlt Hw Hr Hx Hterm; [lia |].
      rewrite read_unfold in Hx. unfold read_body in Hx.
      fut hg. wt (@nil (FutureEntry G)) s.
      fut hm1. fut hx. fut hy. fut hm2.
      grab. unfold test_ticket in Hx_. destruct (Nat.odd s) eqn:Hodd; cbn beta iota in Hx_.
      - (* silent test_ticket: retry *)
        wt [_; _; _] u1. wt [_; _] a. wt [_] b. wt (@nil (FutureEntry G)) u2.
        grab. cbn iota in Hx_.
        destruct (exec_tau Hx_ Hterm Hw_ Hr_) as (H' & tr' & Hw' & Hr' & Hx' & Hl').
        destruct (IH _ _ tr' _ _ ltac:(lia) Hw' Hr' Hx' Hterm)
          as (N & its & s' & a' & b' & Hall & Hf & Hc & Hok & Hr0 & ->).
        eexists (N ++ [_; _; _; _; _]), ((s, a, b, 0) :: its), s', a', b'.
        split; [| split; [rewrite <- app_assoc; exact Hf |]].
        { apply Forall_app. split; [exact Hall | repeat constructor]. }
        split; [| split; [| split; [| reflexivity]]].
        + rewrite map_app, rev_app_distr, map_app, Hc.
          cbn [ST.lcalls flat_map ST.literq]. rewrite (liter_odd s a b 0 Hodd). reflexivity.
        + apply blk_ok_cons; [apply iter_ok_silent, Hodd | exact Hok].
        + apply silent_r0_cons; [rewrite Hodd; reflexivity | exact Hr0].
      - (* test_ticket calls own.get() *)
        fut ht. wt (@nil (FutureEntry G)) v.
        wt [_; _; _; _] u1. wt [_; _; _] a. wt [_; _] b. wt [_] u2.
        grab. destruct (negb (Nat.eqb v s)) eqn:Hv; cbn beta iota in Hx_.
        + (* retry *)
          destruct (exec_tau Hx_ Hterm Hw_ Hr_) as (H' & tr' & Hw' & Hr' & Hx' & Hl').
          destruct (IH _ _ tr' _ _ ltac:(lia) Hw' Hr' Hx' Hterm)
            as (N & its & s' & a' & b' & Hall & Hf & Hc & Hok & Hr0 & ->).
          eexists (N ++ [_; _; _; _; _; _]), ((s, a, b, v) :: its), s', a', b'.
          split; [| split; [rewrite <- app_assoc; exact Hf |]].
          { apply Forall_app. split; [exact Hall | repeat constructor]. }
          split; [| split; [| split; [| reflexivity]]].
          * rewrite map_app, rev_app_distr, map_app, Hc.
            cbn [ST.lcalls flat_map ST.literq]. rewrite (liter_even s a b v Hodd). reflexivity.
          * apply blk_ok_cons; [cbn; rewrite Hodd, Hv; reflexivity | exact Hok].
          * apply silent_r0_cons; [rewrite Hodd; reflexivity | exact Hr0].
        + (* success *)
          apply negb_false_iff, Nat.eqb_eq in Hv. subst v.
          destruct (exec_ret Hx_ Hterm Hr_) as (-> & Hf & _).
          eexists [_; _; _; _; _; _], [], s, a, b.
          split; [| split; [exact Hf |]]; [repeat constructor |].
          split; [| split; [| split; reflexivity]].
          * cbn [ST.lcalls flat_map app]. rewrite (liter_even s a b s Hodd). reflexivity.
          * cbn [ST.blk_ok forallb]. unfold Nat.odd in Hodd. apply negb_false_iff in Hodd.
            rewrite Hodd. reflexivity.
    Qed.

    Lemma read_calls tr (c' : ProgramConfig G (nat * nat)) r :
      program_execution_tagged t (initial_program (read rc C)) tr c' -> program_terminal c' r ->
      exists its s a b,
        map snd (rev (map eu (pc_futures c'))) = ST.lcalls (ST.LBR its s a b) /\
        ST.blk_ok (ST.LBR its s a b) = true /\ silent_r0 (ST.LBR its s a b) = true /\ r = (a, b).
    Proof.
      intros Hx Hterm.
      destruct (read_calls_gen (S (length tr)) [] empty_store tr c' r ltac:(lia)
                  ltac:(constructor) ltac:(constructor) Hx Hterm)
        as (N & its & s & a & b & Hall & Hf & Hc & Hok & Hr0 & ->).
      rewrite app_nil_r in Hf. rewrite (refines_resolved_eq _ _ Hall Hf).
      exists its, s, a, b. auto.
    Qed.

    Lemma zwrite_calls v tr (c' : ProgramConfig G unit) r :
      program_execution_tagged t (initial_program (zwrite rc C v)) tr c' -> program_terminal c' r ->
      map snd (rev (map eu (pc_futures c'))) = ST.lcalls (ST.LBZw v).
    Proof.
      intros Hx Hterm. unfold initial_program, zwrite in Hx.
      assert (Hw : store_well_formed (@empty_store G)) by constructor.
      assert (Hr : refines [] (@empty_store G)) by constructor.
      fut h1. wt (@nil (FutureEntry G)) v1.
      grab. destruct (exec_ret Hx_ Hterm Hr_) as (_ & Hf & _).
      apply refines_resolved_eq in Hf; [| repeat constructor]. rewrite Hf. reflexivity.
    Qed.

    Lemma zread_calls tr (c' : ProgramConfig G nat) r :
      program_execution_tagged t (initial_program (zread rc C)) tr c' -> program_terminal c' r ->
      map snd (rev (map eu (pc_futures c'))) = ST.lcalls (ST.LBZr r).
    Proof.
      intros Hx Hterm. unfold initial_program, zread in Hx.
      assert (Hw : store_well_formed (@empty_store G)) by constructor.
      assert (Hr : refines [] (@empty_store G)) by constructor.
      fut h1. wt (@nil (FutureEntry G)) v1.
      grab. destruct (exec_ret Hx_ Hterm Hr_) as (-> & Hf & _).
      apply refines_resolved_eq in Hf; [| repeat constructor]. rewrite Hf. reflexivity.
    Qed.

    Lemma M0_calls op tr (c' : ProgramConfig G (@Sig.ar SLP.FSig op)) ret :
      program_execution_tagged t (initial_program (M0 rc C op t)) tr c' -> program_terminal c' ret ->
      exists k, map snd (rev (map eu (pc_futures c'))) = ST.lcalls k /\
        ST.blk_ok k = true /\ spin_ok k = true /\ silent_r0 k = true /\
        SLP.blk_matches op (ST.abs k) ret.
    Proof.
      destruct op as [vx vy | | v |]; cbn [M0]; intros Hx Hterm.
      - destruct (write_calls vx vy tr c' ret Hx Hterm) as (tk & sp & Hc & Hsp).
        exists (ST.LBW vx vy tk sp). split; [exact Hc |].
        split; [reflexivity |]. split; [apply spin_ok_of, Hsp |]. split; reflexivity.
      - destruct (read_calls tr c' ret Hx Hterm) as (its & s & a & b & Hc & Hok & Hr0 & ->).
        exists (ST.LBR its s a b). split; [exact Hc |]. split; [exact Hok |].
        split; [reflexivity |]. split; [exact Hr0 |].
        exists (map ST.drop4 its), s, a, b. split; reflexivity.
      - exists (ST.LBZw v). split; [exact (zwrite_calls v tr c' ret Hx Hterm) |].
        split; [reflexivity |]. split; [reflexivity |]. split; reflexivity.
      - exists (ST.LBZr ret). split; [exact (zread_calls tr c' ret Hx Hterm) |].
        split; [reflexivity |]. split; [reflexivity |]. split; [reflexivity |].
        exists ret. split; reflexivity.
    Qed.
  End Methods.

  (** ** The shape of a method's trace *)

  Theorem M0_shape rc C op t tr ret :
    program_produces_tagged t (M0 rc C op t) tr ret ->
    exists (k : ST.LBlk) (cs : list (nat * ST.LC)),
      ST.lcalls k = map snd cs /\
      inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) cs /\
      NoDup (map fst cs) /\
      Permutation (res_list0 (map untag tr)) cs /\
      Forall (fun ev => te_tid _ ev = t) (map untag tr) /\
      ST.blk_ok k = true /\
      spin_ok k = true /\
      silent_r0 k = true /\
      SLP.blk_matches op (ST.abs k) ret.
  Proof.
    intros (c' & Hx & Hterm).
    destruct (M0_calls rc C t op tr c' ret Hx Hterm) as (k & Hk & Hok & Hsp & Hr0 & Hm).
    destruct (@exec_shape (E0 rc C) ST.LC uc0_of dflt0 op0_of op0_of_uc _ t _ tr c' ret Hx Hterm)
      as (Hinv & Hnd & Hperm & Htid).
    exists k, (rev (map (@entry_uc (E0 rc C) ST.LC uc0_of dflt0) (pc_futures c'))).
    split; [symmetry; exact Hk |]. split; [exact Hinv |]. split; [exact Hnd |].
    split; [exact Hperm |]. split; [exact Htid |]. auto.
  Qed.

  (** Invocations of a method use pairwise distinct handles. *)
  Corollary M0_inv_fresh rc C op t tr ret :
    program_produces_tagged t (M0 rc C op t) tr ret ->
    NoDup (map fst (inv_list (map untag tr))).
  Proof.
    intros Hp. destruct (M0_shape rc C op t tr ret Hp) as (k & cs & _ & Hinv & Hnd & _).
    rewrite Hinv, map_map. exact Hnd.
  Qed.

  (** The read case, with the return value unfolded. *)
  Corollary M0_shape_read rc C t tr a b :
    program_produces_tagged t (M0 rc C SLP.fRead t) tr (a, b) ->
    exists its s cs,
      ST.lcalls (ST.LBR its s a b) = map snd cs /\
      inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) cs /\
      NoDup (map fst cs) /\
      Permutation (res_list0 (map untag tr)) cs /\
      Forall (fun ev => te_tid _ ev = t) (map untag tr) /\
      ST.blk_ok (ST.LBR its s a b) = true /\
      silent_r0 (ST.LBR its s a b) = true.
  Proof.
    intros Hp.
    destruct (M0_shape rc C SLP.fRead t tr (a, b) Hp)
      as (k & cs & Hk & Hinv & Hnd & Hperm & Htid & Hok & _ & Hr0 & fs & s & a' & b' & Habs & Hab).
    injection Hab as <- <-.
    destruct k as [| its s0 a0 b0 | |]; cbn in Habs; try discriminate.
    injection Habs as _ <- <- <-. exists its, s0, cs. auto 8.
  Qed.

  (** The write case: the ticket, the spin values (all different from
      the ticket), and the trace. *)
  Corollary M0_shape_write rc C t vx vy tr ret :
    program_produces_tagged t (M0 rc C (SLP.fWrite vx vy) t) tr ret ->
    exists tk sp cs,
      ST.lcalls (ST.LBW vx vy tk sp) = map snd cs /\
      inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) cs /\
      NoDup (map fst cs) /\
      Permutation (res_list0 (map untag tr)) cs /\
      Forall (fun ev => te_tid _ ev = t) (map untag tr) /\
      Forall (fun v => v <> tk) sp.
  Proof.
    intros Hp.
    destruct (M0_shape rc C (SLP.fWrite vx vy) t tr ret Hp)
      as (k & cs & Hk & Hinv & Hnd & Hperm & Htid & _ & Hsp & _ & Hm).
    destruct k as [vx0 vy0 tk sp | | |]; cbn in Hm; try discriminate.
    injection Hm as <- <-. exists tk, sp, cs.
    split; [exact Hk |]. split; [exact Hinv |]. split; [exact Hnd |].
    split; [exact Hperm |]. split; [exact Htid |].
    cbn [spin_ok] in Hsp. apply Forall_forall. intros v Hv.
    rewrite forallb_forall in Hsp. specialize (Hsp v Hv).
    apply negb_true_iff, Nat.eqb_neq in Hsp. exact Hsp.
  Qed.

  (** [M0_shape] with the block decoded from the trace ([decode0],
      [parse0]): the analogue of [SeqLockModule.produced_shape]. *)
  Corollary M0_shape_decoded rc C op t tr ret :
    program_produces_tagged t (M0 rc C op t) tr ret ->
    ST.lcalls (parse0 (map snd (decode0 (map untag tr)))) = map snd (decode0 (map untag tr)) /\
    inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) (decode0 (map untag tr)) /\
    NoDup (map fst (decode0 (map untag tr))) /\
    Permutation (res_list0 (map untag tr)) (decode0 (map untag tr)) /\
    Forall (fun ev => te_tid _ ev = t) (map untag tr) /\
    ST.blk_ok (parse0 (map snd (decode0 (map untag tr)))) = true /\
    spin_ok (parse0 (map snd (decode0 (map untag tr)))) = true /\
    silent_r0 (parse0 (map snd (decode0 (map untag tr)))) = true /\
    SLP.blk_matches op (ST.abs (parse0 (map snd (decode0 (map untag tr))))) ret.
  Proof.
    intros Hp.
    destruct (M0_shape rc C op t tr ret Hp) as (k & cs & Hk & Hinv & Hnd & Hperm & Htid & Hok & Hsp & Hr0 & Hm).
    rewrite (decode0_spec _ cs Hinv Hnd Hperm), <- Hk, (parse0_lcalls k Hr0). auto 10.
  Qed.

  (** ** Non-vacuity: concrete method traces *)

  Ltac ex_fut h :=
    match goal with
    | |- program_execution_tagged ?t (Build_ProgramConfig (@Future ?E ?R ?o ?k) ?H) _ _ =>
        eapply tagged_execution_emit;
        [ apply (@tagged_future E R t o k h H); unfold handle_fresh; cbn; intuition discriminate
        | cbn beta ]
    end.

  Ltac ex_resolve :=
    repeat first [ apply resolve_here | apply resolve_next; [discriminate |] ].

  Ltac ex_wait v :=
    match goal with
    | |- program_execution_tagged ?t
           (Build_ProgramConfig (@Wait ?E ?R _ (@MkFutureRef _ ?o ?h) ?k) ?H) _ _ =>
        eapply tagged_execution_emit;
        [ eapply (@tagged_wait_pending E R t o h v k H); ex_resolve
        | cbn beta ]
    end.

  Ltac ex_tau := eapply tagged_execution_silent; [apply tagged_tau |].

  Ltac ex_norm := cbn [Nat.eqb Nat.odd Nat.even negb test_ticket].

  (** A [write(1,1)] whose [acq] takes ticket 2, reads [own = 0] once
      (one spin iteration), then [own = 2]. *)
  Example M0_write_produces rc C t :
    exists tr, program_produces_tagged t (M0 rc C (SLP.fWrite 1 1) t) tr tt /\
      inv_list (map untag tr) =
        [(0, oFaa); (1, oGet); (2, oGet); (3, oInc); (4, oWmb); (5, oWrX 1); (6, oWrY 1); (7, oWmb); (8, oInc)] /\
      map snd (inv_list (map untag tr)) = map op0_of (ST.lcalls (ST.LBW 1 1 2 [0])) /\
      res_list0 (map untag tr) =
        [(0, ST.LT (TL.FaaN 2)); (1, ST.LT (TL.GetO 0)); (2, ST.LT (TL.GetO 2)); (3, ST.LT TL.IncO);
         (4, ST.LD SL.WmbC); (5, ST.LD (SL.WrX 1)); (6, ST.LD (SL.WrY 1)); (7, ST.LD SL.WmbC);
         (8, ST.LT TL.IncO)].
  Proof.
    eexists. split; [eexists; split |].
    - unfold initial_program. cbv beta iota delta [M0]. unfold write, acq.
      ex_fut 0. ex_wait 2.
      rewrite spin_unfold. unfold spin_body.
      ex_fut 1. ex_wait 0. ex_norm. ex_tau.
      rewrite spin_unfold. unfold spin_body.
      ex_fut 2. ex_wait 2. ex_norm.
      ex_fut 3. ex_wait tt.
      ex_fut 4. ex_fut 5. ex_fut 6. ex_fut 7. ex_fut 8.
      ex_wait tt. ex_wait tt. ex_wait tt. ex_wait tt. ex_wait tt.
      apply tagged_execution_refl.
    - constructor. repeat constructor.
    - split; [reflexivity | split; reflexivity].
  Qed.

  (** The reader of [SeqLockTower.X0_ex]: the first [get_ticket] returns
      1, so [test_ticket(1)] is silent and the read retries; the second
      iteration reads (1, 1) under ticket 2 and succeeds. *)
  Example M0_read_produces rc C t :
    exists tr, program_produces_tagged t (M0 rc C SLP.fRead t) tr (1, 1) /\
      inv_list (map untag tr) =
        [(0, oGet); (1, oRmb); (2, oRdX); (3, oRdY); (4, oRmb);
         (5, oGet); (6, oRmb); (7, oRdX); (8, oRdY); (9, oRmb); (10, oGet)] /\
      map snd (inv_list (map untag tr)) = map op0_of (ST.lcalls (ST.LBR [(1, 0, 0, 0)] 2 1 1)) /\
      res_list0 (map untag tr) =
        [(0, ST.LT (TL.GetO 1)); (1, ST.LD SL.RmbC); (2, ST.LD (SL.RdX 0)); (3, ST.LD (SL.RdY 0));
         (4, ST.LD SL.RmbC); (5, ST.LT (TL.GetO 2)); (10, ST.LT (TL.GetO 2)); (6, ST.LD SL.RmbC);
         (7, ST.LD (SL.RdX 1)); (8, ST.LD (SL.RdY 1)); (9, ST.LD SL.RmbC)].
  Proof.
    eexists. split; [eexists; split |].
    - unfold initial_program. cbv beta iota delta [M0].
      rewrite read_unfold. unfold read_body.
      ex_fut 0. ex_wait 1.
      ex_fut 1. ex_fut 2. ex_fut 3. ex_fut 4. ex_norm.
      ex_wait tt. ex_wait 0. ex_wait 0. ex_wait tt. ex_tau.
      rewrite read_unfold. unfold read_body.
      ex_fut 5. ex_wait 2.
      ex_fut 6. ex_fut 7. ex_fut 8. ex_fut 9. ex_norm.
      ex_fut 10. ex_wait 2.
      ex_wait tt. ex_wait 1. ex_wait 1. ex_wait tt. ex_norm.
      apply tagged_execution_refl.
    - constructor. repeat constructor.
    - split; [reflexivity | split; reflexivity].
  Qed.

  (** [M0_shape] applies to both. *)
  Example M0_shape_nonvacuous rc C t :
    (exists tr k cs, program_produces_tagged t (M0 rc C SLP.fRead t) tr (1, 1) /\
       ST.lcalls k = map snd cs /\ inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) cs /\
       ST.blk_ok k = true /\ SLP.blk_matches SLP.fRead (ST.abs k) (1, 1)) /\
    (exists tr k cs, program_produces_tagged t (M0 rc C (SLP.fWrite 1 1) t) tr tt /\
       ST.lcalls k = map snd cs /\ inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) cs /\
       spin_ok k = true /\ SLP.blk_matches (SLP.fWrite 1 1) (ST.abs k) tt).
  Proof.
    split.
    - destruct (M0_read_produces rc C t) as (tr & Hp & _).
      destruct (M0_shape rc C SLP.fRead t tr (1, 1) Hp) as (k & cs & Hk & Hinv & _ & _ & _ & Hok & _ & _ & Hm).
      exists tr, k, cs. auto.
    - destruct (M0_write_produces rc C t) as (tr & Hp & _).
      destruct (M0_shape rc C (SLP.fWrite 1 1) t tr tt Hp) as (k & cs & Hk & Hinv & _ & _ & _ & _ & Hsp & _ & Hm).
      exists tr, k, cs. auto.
  Qed.
  (** The block of the read trace above is the reader's block
      [LBR [(1, 0, 0, 0)] 2 1 1] of [SeqLockTower.X0_ex]: every block [k]
      with the conjuncts of [M0_shape] is it, and it is the decoded block
      of [M0_shape_decoded]. *)
  Example M0_read_block rc C t :
    exists tr, program_produces_tagged t (M0 rc C SLP.fRead t) tr (1, 1) /\
      (forall k cs,
         ST.lcalls k = map snd cs ->
         inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) cs ->
         NoDup (map fst cs) -> Permutation (res_list0 (map untag tr)) cs ->
         silent_r0 k = true -> k = ST.LBR [(1, 0, 0, 0)] 2 1 1) /\
      parse0 (map snd (decode0 (map untag tr))) = ST.LBR [(1, 0, 0, 0)] 2 1 1.
  Proof.
    destruct (M0_read_produces rc C t) as (tr & Hp & Hinv0 & _ & Hres0).
    exists tr. split; [exact Hp |]. split.
    - intros k cs Hk Hinv Hnd Hperm Hr0.
      rewrite <- (decode0_spec _ cs Hinv Hnd Hperm) in Hk. unfold decode0 in Hk. rewrite Hinv0, Hres0 in Hk.
      rewrite <- (parse0_lcalls k Hr0), Hk. reflexivity.
    - unfold decode0. rewrite Hinv0, Hres0. reflexivity.
  Qed.

  (** Likewise, the block of the write trace above is [LBW 1 1 2 [0]]. *)
  Example M0_write_block rc C t :
    exists tr, program_produces_tagged t (M0 rc C (SLP.fWrite 1 1) t) tr tt /\
      (forall k cs,
         ST.lcalls k = map snd cs ->
         inv_list (map untag tr) = map (fun c => (fst c, op0_of (snd c))) cs ->
         NoDup (map fst cs) -> Permutation (res_list0 (map untag tr)) cs ->
         silent_r0 k = true -> k = ST.LBW 1 1 2 [0]) /\
      parse0 (map snd (decode0 (map untag tr))) = ST.LBW 1 1 2 [0].
  Proof.
    destruct (M0_write_produces rc C t) as (tr & Hp & Hinv0 & _ & Hres0).
    exists tr. split; [exact Hp |]. split.
    - intros k cs Hk Hinv Hnd Hperm Hr0.
      rewrite <- (decode0_spec _ cs Hinv Hnd Hperm) in Hk. unfold decode0 in Hk. rewrite Hinv0, Hres0 in Hk.
      rewrite <- (parse0_lcalls k Hr0), Hk. reflexivity.
    - unfold decode0. rewrite Hinv0, Hres0. reflexivity.
  Qed.

  (** ** Sanity check: [FuturesShape] re-derives [SeqLockProg.M_shape]

      [M_shape_via_FS] has exactly the type of [SeqLockProg.M_shape] and
      is proved from [FuturesShape.exec_shape] and [SeqLockProg.M_calls]
      alone, so [exec_shape] is the program-independent part of
      [M_shape]. *)
  Lemma res_list_SLP rc K (l : list (ThreadEvent (SLP.E rc K))) :
    @FS.res_list (SLP.E rc K) _ SLP.uc_of l = SLP.res_list l.
  Proof. induction l as [|[? []] l IH]; cbn; [reflexivity | exact IH | rewrite IH; reflexivity]. Qed.

  Example M_shape_via_FS : ltac:(let T := type of @SLP.M_shape in exact T).
  Proof.
    intros rc K op t tr ret (c' & Hx & Hterm).
    destruct (SLP.M_calls rc K t op tr c' ret Hx Hterm) as (k & Hk & Hm).
    pose proof (@FS.exec_shape (SLP.E rc K) _ SLP.uc_of SLP.dflt SLP.op_of SLP.op_of_uc _ t _ tr c' ret Hx Hterm)
      as (Hinv & Hnd & Hperm & Htid).
    rewrite res_list_SLP in Hperm. exists k.
    exists (rev (map (@FS.entry_uc (SLP.E rc K) _ SLP.uc_of SLP.dflt) (pc_futures c'))).
    split; [symmetry; exact Hk |]. split; [rewrite <- inv_list_SLP; exact Hinv |]. split; [exact Hnd |].
    split; [exact Hperm |]. split; [exact Htid | exact Hm].
  Qed.
End SeqLockTowerProg.
