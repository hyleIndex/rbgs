(** * The SeqLock tower: the vertical link at the level of underlay witnesses

    [SeqLockCOH] Part B verifies the SeqLock over an atomic TicketLock
    (with the abstract lock-with-version specification) ⊗ COH[x] ⊗ COH[y]
    ⊗ Barrier ⊗ COH[z]; [TicketLockCOH] verifies the TicketLock over
    Counter[own] ⊗ COH[nxt].  Here the two layers are composed vertically:
    the SeqLock code runs with the TicketLock code inlined, on

<<
    Counter[own] ⊗ COH[nxt] ⊗ COH[x] ⊗ COH[y] ⊗ Barrier ⊗ COH[z]
>>

    and every complete low-level execution of it ([WF0]) yields a
    SeqLock-layer execution ([SeqLockCOH.WF], the TicketLock now atomic)
    with the same threads, the abstracted programs ([abs]) and a witness
    that keeps the witness order of operations of the low level ([rt0]:
    every low-level call of [q] before every low-level call of [q'] in
    the low-level witness; [tower_link]).  Hence the SeqLock-layer
    theorems apply to the low-level execution, in particular
    [SeqLockCOH.seqlock_z_composition] ([tower_composition];
    [tower_composition_plain] for the plain counter, whose categories are
    [plainTL]; [tower_composition_rc] for the RC counter).  With a
    timing of the low-level execution ([RT_ok0], as [SeqLockRT.RT_ok]),
    real-time order implies witness order ([rt_of0_rt0]), so the
    linearization respects the real-time order of the low-level execution
    ([tower_composition_rt], [tower_composition_rt_plain]).

    - The model.  A SeqLock block calls the TicketLock code: [acq] is
      [nxt.faa(2)], the spins [own.get()] and [own.inc()]; [rel] is
      [own.inc()]; [get_ticket] is [own.get()]; [test_ticket(s)] is
      [own.get()] for even [s] and silent (no call) for odd [s]
      ([TicketLockCOH.tcalls]).  Preserved order: same object ([own],
      [nxt], [x], [y], [z], each with [I = ∅]) or the table [WT.dto] on
      categories, those of the Counter and of [nxt] being a parameter
      [C : CCats] (as in [TicketLockCOH]).  Reads must be well formed
      ([blk_ok]): a failed iteration returned retry, the final one is
      [(s, a, b, s)] with even [s].
    - Segments.  Every SeqLock-layer call is one segment: a TicketLock
      operation [ST k] (its calls [map LT (tcalls k)]) or a data call
      [SD c] (the call [LD c]).  So SeqLock indices are segment indices,
      and the projection to TicketLock operations keeps the [ST] segments.
    - The TicketLock projection [XT]: the [LT] calls of the low-level
      witness form a [TicketLockCOH.WF] execution ([XT_wf]; [bracketed]
      holds as a write contributes [acq; rel] and a read no lock op).
    - The SeqLock-layer witness [W1]: each low-level call emits the
      SeqLock calls it represents ([emits]): a data call itself, the
      window call of a TicketLock operation ([own.inc] of [acq]/[rel],
      [own.get] of [get_ticket]/[test_ticket]) that operation, and the
      second [rmb] of an iteration whose [test_ticket] is silent emits
      that [test_ticket] right after itself.  [W1] is the concatenation
      along the low-level witness, i.e. the SeqLock calls sorted by
      [2 · pos] of their representative, [2 · pos(rmb) + 1] for a silent
      [test_ticket].
    - [SeqLockCOH.WF] ([X1_wf]).  Preserved order transfers since a call
      and its representative have the same object and category
      ([rep_obj], [rep_cat]); a silent [test_ticket] is ordered through
      the next iteration's [get_ticket] and through its own iteration's
      [get_ticket] and [rmb]s ([core_order]; the only use of [K_ok]: the
      Counter's [get] is a read).  Validity: data calls see the low-level
      cell values ([W1_dsim]); the TicketLock calls of [W1], in order,
      are a placement of the silent [test_ticket]s into the TicketLock
      linearization of [XT] ([W1_tl_ok], by
      [TicketLockCOH.ticketlock_S1_any_placement]), hence valid
      ([tl_valid], by [TicketLockCOH.spec_match]).
    - Witness order of operations ([X1_rt]): every SeqLock call of an
      operation is emitted by a low-level call of the same operation, so
      an operation whose low-level calls all precede those of another in
      the low-level witness ([rt0]) has all its SeqLock calls before the
      other's in [W1] ([rt1], the [rt] of [SeqLockCOH.setting], which is
      likewise a witness order, not a real-time one).
    - Real time.  [Timing0] gives invocation and response times to
      low-level operations and calls and [RT_ok0] links them as
      [SeqLockRT.RT_ok] does (a call is invoked after its operation, a
      responded operation has its calls responded, a call responds after
      its invocation, the witness extends the real-time order of calls).
      The standard real-time order [rt_of0] (q responded before q' was
      invoked) implies [rt0] ([rt_of0_rt0]).  [setting_rt0] is
      [SeqLockCOH.setting] with [rt_of0] as real-time order, and
      [tower_composition_rt] gives its [Conclusion].  [RT_ok0] holds of
      every execution for some timing ([canon0_ok]).
    - Non-vacuity: a concrete execution with a silent [test_ticket]
      satisfies [WF0] ([ex_wf0]); its [W1] is computed ([ex_W1]) and
      checked by [SeqLockCOH]'s own decision procedure ([ex_X1_wf]).

    Scope: as the two layer files, everything is at the level of underlay
    witnesses of complete executions; the Counter is kept as an object
    with categories [C] (its implementation over COH[own] is not
    inlined). *)

From Stdlib Require Import List Bool Arith.PeanoNat micromega.Lia.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.SeqLockCOH.
Require Import examples.Relaxed.TicketLockCOH.

Import ListNotations.

Module SeqLockTower.
  Module WC := WindowComposition.
  Module WT := WindowTable.
  Module SL := SeqLockCOH.
  Module TL := TicketLockCOH.
  Import WT.

  (** ** The low-level model *)

  (** Calls of [Counter[own] ⊗ COH[nxt]] ([LT]) and of the cells and
      barriers ([LD], used only for [WrX], [WrY], [RdX], [RdY], [WmbC],
      [RmbC], [WrZ], [RdZ]). *)
  Inductive LC : Type := LT (c : TL.TC) | LD (c : SL.UC).

  Definition LC_eq_dec (a b : LC) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply TL.TC_eq_dec | apply SL.UC_eq_dec]. Defined.

  Inductive LObj := LOwn | LNxt | LX | LY | LB | LZ.

  Definition oimg (o : SL.UObj) : LObj :=
    match o with SL.OTL => LOwn | SL.OX => LX | SL.OY => LY | SL.OB => LB | SL.OZ => LZ end.

  Definition lobj (c : LC) : LObj :=
    match c with
    | LT c => match TL.tobj c with TL.ONxt => LNxt | TL.OOwn => LOwn end
    | LD c => oimg (SL.uobj c)
    end.

  (** [own], [nxt] and the cells have [I = ∅]; barriers are ordered by the
      table only. *)
  Definition same_lobj (a b : LObj) : bool :=
    match a, b with
    | LOwn, LOwn | LNxt, LNxt | LX, LX | LY, LY | LZ, LZ => true
    | _, _ => false
    end.

  Definition lcat (C : TL.CCats) (c : LC) : DCat :=
    match c with LT c => TL.tcat C c | LD c => SL.ucat (TL.tl_cats C) c end.

  Definition lpres (rc : bool) (C : TL.CCats) (c1 c2 : LC) : bool :=
    same_lobj (lobj c1) (lobj c2) || dto rc (lcat C c1) (lcat C c2).

  (** Blocks: a write with its ticket and spin values, a read with its
      failed iterations [(s, a, b, r)] and its final ticket and values, and
      the client cell. *)
  Inductive LBlk : Type :=
  | LBW (vx vy tk : nat) (sp : list nat)
  | LBR (its : list (nat * nat * nat * nat)) (s a b : nat)
  | LBZw (v : nat)
  | LBZr (v : nat).

  Definition liter (s a b r : nat) : list LC :=
    map LT (TL.tcalls (TL.TGt s)) ++ map LD [SL.RmbC; SL.RdX a; SL.RdY b; SL.RmbC]
    ++ map LT (TL.tcalls (TL.TTt s r)).

  Definition literq (it : nat * nat * nat * nat) : list LC := let '(s, a, b, r) := it in liter s a b r.

  Definition lcalls (k : LBlk) : list LC :=
    match k with
    | LBW vx vy tk sp =>
        map LT (TL.tcalls (TL.TAcq tk sp)) ++ map LD [SL.WmbC; SL.WrX vx; SL.WrY vy; SL.WmbC]
        ++ map LT (TL.tcalls TL.TRel)
    | LBR its s a b => flat_map literq its ++ liter s a b s
    | LBZw v => [LD (SL.WrZ v)]
    | LBZr v => [LD (SL.RdZ v)]
    end.

  (** A read loops while [test_ticket] says retry: failed iterations
      returned retry, the final one returned [false] (even [s], [r = s]). *)
  Definition iter_ok (it : nat * nat * nat * nat) : bool :=
    let '(s, _, _, r) := it in Nat.odd s || negb (Nat.eqb r s).

  Definition blk_ok (k : LBlk) : bool :=
    match k with LBR its s _ _ => Nat.even s && forallb iter_ok its | _ => true end.

  (** The SeqLock-layer block. *)
  Definition drop4 (it : nat * nat * nat * nat) : nat * nat * nat := let '(s, a, b, _) := it in (s, a, b).

  Definition abs (k : LBlk) : SL.Blk :=
    match k with
    | LBW vx vy _ _ => SL.BW vx vy
    | LBR its s a b => SL.BR (map drop4 its) s a b
    | LBZw v => SL.BZw v
    | LBZr v => SL.BZr v
    end.

  Record LState : Type := mkL { lown : nat; lnxt : nat; lx : nat; ly : nat; lz : nat }.

  Definition linit : LState := mkL 0 0 0 0 0.

  Record LEv : Type := mkLE { lth : nat; lix : nat; lcall : LC }.

  Definition LEv_eq_dec (a b : LEv) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply LC_eq_dec | apply Nat.eq_dec]. Defined.

  Definition lpre (s : LState) (e : LEv) : bool :=
    match lcall e with
    | LT (TL.FaaN r) => Nat.eqb (lnxt s) r
    | LT (TL.GetO v) => Nat.eqb (lown s) v
    | LT TL.IncO => true
    | LD (SL.RdX v) => Nat.eqb (lx s) v
    | LD (SL.RdY v) => Nat.eqb (ly s) v
    | LD (SL.RdZ v) => Nat.eqb (lz s) v
    | LD _ => true
    end.

  Definition lpost (s : LState) (e : LEv) : LState :=
    match lcall e with
    | LT (TL.FaaN _) => mkL (lown s) (S (S (lnxt s))) (lx s) (ly s) (lz s)
    | LT (TL.GetO _) => s
    | LT TL.IncO => mkL (S (lown s)) (lnxt s) (lx s) (ly s) (lz s)
    | LD (SL.WrX v) => mkL (lown s) (lnxt s) v (ly s) (lz s)
    | LD (SL.WrY v) => mkL (lown s) (lnxt s) (lx s) v (lz s)
    | LD (SL.WrZ v) => mkL (lown s) (lnxt s) (lx s) (ly s) v
    | LD _ => s
    end.

  Fixpoint lrun (s : LState) (l : list LEv) : LState :=
    match l with [] => s | e :: l' => lrun (lpost s e) l' end.

  Fixpoint lidx (e : LEv) (l : list LEv) : nat :=
    match l with
    | [] => 0
    | e' :: l' => if LEv_eq_dec e e' then 0 else S (lidx e l')
    end.

  Record Exec0 : Type := { ths0 : list nat; prog0 : nat -> list LBlk; wit0 : list LEv }.

  Definition ltrace (p : list LBlk) : list LC := flat_map lcalls p.
  Definition loff (p : list LBlk) (j : nat) : nat := length (ltrace (firstn j p)).

  Section WithExec0.
    Context (rc : bool) (C : TL.CCats) (X0 : Exec0).

    Definition at0 (p : nat) : LState := lrun linit (firstn p (wit0 X0)).
    Definition evt0 (t i : nat) : LEv := mkLE t i (nth i (ltrace (prog0 X0 t)) (LT TL.IncO)).
    Definition P0 (t i : nat) : nat := lidx (evt0 t i) (wit0 X0).

    (** A complete low-level execution. *)
    Record WF0 : Prop := {
      wf0_nodup : NoDup (wit0 X0);
      wf0_ths : NoDup (ths0 X0);
      wf0_call : forall e, In e (wit0 X0) ->
                   In (lth e) (ths0 X0) /\ nth_error (ltrace (prog0 X0 (lth e))) (lix e) = Some (lcall e);
      wf0_complete : forall t i, In t (ths0 X0) -> i < length (ltrace (prog0 X0 t)) ->
                       In (evt0 t i) (wit0 X0);
      wf0_pres : forall e1 e2, In e1 (wit0 X0) -> In e2 (wit0 X0) -> lth e1 = lth e2 ->
                   lix e1 < lix e2 -> lpres rc C (lcall e1) (lcall e2) = true ->
                   lidx e1 (wit0 X0) < lidx e2 (wit0 X0);
      wf0_valid : forall p e, nth_error (wit0 X0) p = Some e -> lpre (at0 p) e = true;
      wf0_blk : forall t, In t (ths0 X0) -> forallb blk_ok (prog0 X0 t) = true;
    }.

    Definition blk0 (q : nat * nat) : option LBlk := nth_error (prog0 X0 (fst q)) (snd q).

    Definition all_ops0 : list (nat * nat) :=
      flat_map (fun t => map (pair t) (seq 0 (length (prog0 X0 t)))) (ths0 X0).

    Definition Pq0 (q : nat * nat) (i : nat) : nat := P0 (fst q) (loff (prog0 X0 (fst q)) (snd q) + i).

    (** Witness order of operations at the low level: every call of [q]
        before every call of [q'] in the low-level witness.  This is not
        real time ([WF0] has no timing); real time implies it under
        [RT_ok0] ([rt_of0_rt0]). *)
    Definition rt0 (q q' : nat * nat) : Prop :=
      forall k k' i i', blk0 q = Some k -> blk0 q' = Some k' ->
        i < length (lcalls k) -> i' < length (lcalls k') -> Pq0 q i < Pq0 q' i'.

    Definition ovl0 (q : nat * nat) : SL.OvEv :=
      match blk0 q with
      | Some (LBW vx vy _ _) => SL.OW vx vy
      | Some (LBR _ _ a b) => SL.OR a b
      | Some (LBZw v) => SL.OZW v
      | Some (LBZr v) => SL.OZR v
      | None => SL.OZR 0
      end.
  End WithExec0.

  (** ** Segments *)

  (** One SeqLock-layer call each: a TicketLock operation or a data call. *)
  Inductive Seg : Type := ST (k : TL.TBlk) | SD (c : SL.UC).

  Definition segcalls (s : Seg) : list LC :=
    match s with ST k => map LT (TL.tcalls k) | SD c => [LD c] end.

  Definition segtl (s : Seg) : list TL.TBlk := match s with ST k => [k] | SD _ => [] end.

  (** The SeqLock-layer call of a TicketLock operation. *)
  Definition tlcall (k : TL.TBlk) : SL.UC :=
    match k with
    | TL.TAcq _ _ => SL.Acq
    | TL.TRel => SL.Rel
    | TL.TGt s => SL.GT s
    | TL.TTt s r => SL.TT s (Nat.odd s || negb (Nat.eqb r s))
    end.

  Definition segsl (s : Seg) : SL.UC := match s with ST k => tlcall k | SD c => c end.

  Definition silent (s : Seg) : bool := match s with ST k => negb (TL.has_call k) | SD _ => false end.

  Definition iseg (s a b r : nat) : list Seg :=
    [ST (TL.TGt s); SD SL.RmbC; SD (SL.RdX a); SD (SL.RdY b); SD SL.RmbC; ST (TL.TTt s r)].

  Definition isegq (it : nat * nat * nat * nat) : list Seg := let '(s, a, b, r) := it in iseg s a b r.

  Definition segs (k : LBlk) : list Seg :=
    match k with
    | LBW vx vy tk sp =>
        [ST (TL.TAcq tk sp); SD SL.WmbC; SD (SL.WrX vx); SD (SL.WrY vy); SD SL.WmbC; ST TL.TRel]
    | LBR its s a b => flat_map isegq its ++ iseg s a b s
    | LBZw v => [SD (SL.WrZ v)]
    | LBZr v => [SD (SL.RdZ v)]
    end.

  Definition sg (p : list LBlk) : list Seg := flat_map segs p.

  (** The TicketLock program of a thread. *)
  Definition tblks (k : LBlk) : list TL.TBlk := flat_map segtl (segs k).
  Definition tprog (p : list LBlk) : list TL.TBlk := flat_map tblks p.

  (** The window call of a call-ful TicketLock operation, and the
      representative low-level call of a segment. *)
  Definition wcall (k : TL.TBlk) : TL.TC :=
    match k with TL.TAcq _ _ | TL.TRel => TL.IncO | TL.TGt s => TL.GetO s | TL.TTt _ r => TL.GetO r end.

  Definition repc (s : Seg) : LC := match s with ST k => LT (wcall k) | SD c => LD c end.

  (** The [LT] calls of a low-level trace: the TicketLock trace. *)
  Definition ltp (c : LC) : list TL.TC := match c with LT c => [c] | LD _ => [] end.

  Definition is_tlc (c : SL.UC) : bool :=
    match c with SL.Acq | SL.Rel | SL.GT _ | SL.TT _ _ => true | _ => false end.

  (** ** Generic lemmas on [flat_map] *)

  Section FM.
    Context {A B : Type} (f : A -> list B).

    (** Offset of the [p]-th element's image. *)
    Definition fo (l : list A) (p : nat) : nat := length (flat_map f (firstn p l)).

    Lemma fo_0 l : fo l 0 = 0.
    Proof. reflexivity. Qed.

    Lemma fo_cons a l p : fo (a :: l) (S p) = length (f a) + fo l p.
    Proof. unfold fo. cbn [firstn flat_map]. apply length_app. Qed.

    Lemma fo_S l p x : nth_error l p = Some x -> fo l (S p) = fo l p + length (f x).
    Proof.
      revert p. induction l as [|a l IH]; intros [|p] H; cbn in H; try discriminate.
      - injection H as <-. rewrite fo_cons, !fo_0. lia.
      - rewrite !fo_cons. specialize (IH p H). lia.
    Qed.

    Lemma fo_mono l p p' : p <= p' -> fo l p <= fo l p'.
    Proof.
      revert p p'. induction l as [|a l IH]; intros p p' Hle.
      - unfold fo. rewrite !firstn_nil. lia.
      - destruct p as [|p]; [rewrite fo_0; lia|].
        destruct p' as [|p']; [lia|].
        rewrite !fo_cons. specialize (IH p p' ltac:(lia)). lia.
    Qed.

    Lemma fo_lt l p p' x k :
      nth_error l p = Some x -> k < length (f x) -> p < p' -> fo l p + k < fo l p'.
    Proof.
      intros Hp Hk Hlt. pose proof (fo_S l p x Hp). pose proof (fo_mono l (S p) p' Hlt). lia.
    Qed.

    Lemma fo_le_len l p : fo l p <= length (flat_map f l).
    Proof.
      unfold fo. rewrite <- (firstn_skipn p l) at 2. rewrite flat_map_app, length_app. lia.
    Qed.

    Lemma fm_nth l p x k :
      nth_error l p = Some x -> k < length (f x) ->
      nth_error (flat_map f l) (fo l p + k) = nth_error (f x) k.
    Proof.
      intros Hp Hk.
      destruct (nth_error_split l p Hp) as (l1 & l2 & -> & Hl1). subst p.
      unfold fo. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite flat_map_app. cbn [flat_map]. rewrite nth_error_app2 by lia.
      replace (length (flat_map f l1) + k - length (flat_map f l1)) with k by lia.
      rewrite nth_error_app1 by exact Hk. reflexivity.
    Qed.

    Lemma fm_inv l i b :
      nth_error (flat_map f l) i = Some b ->
      exists p x k, nth_error l p = Some x /\ i = fo l p + k /\ nth_error (f x) k = Some b.
    Proof.
      revert i. induction l as [|a l IH]; intros i H; [destruct i; discriminate|].
      cbn [flat_map] in H.
      destruct (Nat.lt_ge_cases i (length (f a))) as [Hi|Hi].
      - rewrite nth_error_app1 in H by exact Hi. exists 0, a, i. rewrite fo_0. auto.
      - rewrite nth_error_app2 in H by exact Hi.
        destruct (IH _ H) as (p & x & k & Hp & Ei & Hk).
        exists (S p), x, k. split; [exact Hp|]. split; [|exact Hk]. rewrite fo_cons. lia.
    Qed.

    Lemma fm_firstn l p x k :
      nth_error l p = Some x -> k <= length (f x) ->
      firstn (fo l p + k) (flat_map f l) = flat_map f (firstn p l) ++ firstn k (f x).
    Proof.
      intros Hp Hk.
      destruct (nth_error_split l p Hp) as (l1 & l2 & -> & Hl1). subst p.
      unfold fo. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
      rewrite flat_map_app. cbn [flat_map].
      rewrite firstn_app, firstn_all2 by lia.
      replace (length (flat_map f l1) + k - length (flat_map f l1)) with k by lia.
      rewrite firstn_app. replace (k - length (f x)) with 0 by lia. rewrite firstn_O, app_nil_r.
      reflexivity.
    Qed.

    Lemma fm_firstn0 l p : firstn (fo l p) (flat_map f l) = flat_map f (firstn p l).
    Proof.
      unfold fo. rewrite <- (firstn_skipn p l) at 2. rewrite flat_map_app.
      rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r. reflexivity.
    Qed.

    Lemma fo_inj l p x k p' x' k' :
      nth_error l p = Some x -> k < length (f x) -> nth_error l p' = Some x' -> k' < length (f x') ->
      fo l p + k = fo l p' + k' -> p = p' /\ k = k'.
    Proof.
      intros Hp Hk Hp' Hk' E.
      destruct (Nat.lt_trichotomy p p') as [Hlt|[<-|Hlt]].
      - pose proof (fo_lt l p p' x k Hp Hk Hlt). lia.
      - split; [reflexivity|lia].
      - pose proof (fo_lt l p' p x' k' Hp' Hk' Hlt). lia.
    Qed.

    (** Locating a position of [flat_map f l]. *)
    Fixpoint loc (l : list A) (i : nat) : nat * nat :=
      match l with
      | [] => (0, i)
      | a :: l' => if i <? length (f a) then (0, i)
                   else let '(p, k) := loc l' (i - length (f a)) in (S p, k)
      end.

    Lemma loc_fo l p x k : nth_error l p = Some x -> k < length (f x) -> loc l (fo l p + k) = (p, k).
    Proof.
      revert p. induction l as [|a l IH]; intros [|p] Hp Hk; cbn in Hp; try discriminate.
      - injection Hp as <-. rewrite fo_0. cbn [loc Nat.add].
        destruct (k <? length (f a)) eqn:E; [reflexivity|apply Nat.ltb_ge in E; lia].
      - rewrite fo_cons. cbn [loc].
        destruct (length (f a) + fo l p + k <? length (f a)) eqn:E; [apply Nat.ltb_lt in E; lia|].
        replace (length (f a) + fo l p + k - length (f a)) with (fo l p + k) by lia.
        rewrite (IH p Hp Hk). reflexivity.
    Qed.

    Lemma NoDup_fm l :
      NoDup l -> (forall x, In x l -> NoDup (f x)) ->
      (forall x y b, In x l -> In y l -> In b (f x) -> In b (f y) -> x = y) ->
      NoDup (flat_map f l).
    Proof.
      induction 1 as [|a l Ha Hnd IH]; intros Hf Hdis; cbn [flat_map]; [constructor|].
      apply NoDup_app.
      - apply Hf. left; reflexivity.
      - apply IH; [intros x Hx; apply Hf; right; exact Hx|].
        intros x y b Hx Hy. apply Hdis; right; assumption.
      - intros b Hb Hb'. apply in_flat_map in Hb' as (y & Hy & Hby).
        assert (a = y) by (apply (Hdis a y b); [left; reflexivity|right; exact Hy|exact Hb|exact Hby]).
        subst y. contradiction.
    Qed.
  End FM.

  Lemma fm_fm {A B D} (f : A -> list B) (g : B -> list D) l :
    flat_map g (flat_map f l) = flat_map (fun x => flat_map g (f x)) l.
  Proof. induction l as [|a l IH]; cbn; [reflexivity|]. rewrite flat_map_app, IH. reflexivity. Qed.

  Lemma NoDup_map_in {A B} (f : A -> B) l :
    NoDup l -> (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup (map f l).
  Proof.
    induction 1 as [|a l Ha Hnd IH]; intros Hinj; cbn; constructor.
    - intros Hin. apply in_map_iff in Hin as (y & E & Hy).
      assert (y = a) by (apply Hinj; [right|left|]; auto). subst. contradiction.
    - apply IH. intros x y Hx Hy. apply Hinj; right; assumption.
  Qed.

  (** A list whose elements, taken in their order, are related. *)
  Lemma ss_of_nth {A B} (R : B -> B -> Prop) (f : A -> B) (g : A -> bool) l :
    (forall p p' x y, p < p' -> nth_error l p = Some x -> nth_error l p' = Some y ->
       g x = true -> g y = true -> R (f x) (f y)) ->
    StronglySorted R (map f (filter g l)).
  Proof.
    induction l as [|a l IH]; intros H; cbn; [constructor|].
    assert (IH' : StronglySorted R (map f (filter g l))).
    { apply IH. intros p p' x y Hlt Hx Hy. apply (H (S p) (S p')); [lia|exact Hx|exact Hy]. }
    destruct (g a) eqn:Ga; [|exact IH'].
    cbn. constructor; [exact IH'|].
    apply Forall_forall. intros b Hb. apply in_map_iff in Hb as (y & <- & Hy).
    apply filter_In in Hy as [Hy Gy]. destruct (In_nth_error _ _ Hy) as [p' Hp'].
    apply (H 0 (S p')); [lia|reflexivity|exact Hp'|exact Ga|exact Gy].
  Qed.

  Lemma lidx_nth e l : In e l -> nth_error l (lidx e l) = Some e.
  Proof.
    induction l as [|e' l IH]; cbn; [contradiction|].
    destruct (LEv_eq_dec e e') as [->|Hne]; [reflexivity|].
    intros [->|H]; [contradiction|]. apply IH, H.
  Qed.

  Lemma nth_lidx l p e : NoDup l -> nth_error l p = Some e -> lidx e l = p.
  Proof.
    revert p. induction l as [|e' l IH]; intros p Hnd H; [destruct p; discriminate|].
    inversion Hnd as [|? ? Hni Hnd']; subst.
    destruct p as [|p]; cbn in H |- *.
    - injection H as ->. destruct (LEv_eq_dec e e); [reflexivity|contradiction].
    - destruct (LEv_eq_dec e e') as [->|Hne].
      + exfalso. apply Hni. eapply nth_error_In. exact H.
      + f_equal. apply IH; assumption.
  Qed.

  (** ** Structure of the segments *)

  Lemma lcalls_segs k : lcalls k = flat_map segcalls (segs k).
  Proof.
    destruct k as [vx vy tk sp|its s a b|v|v]; cbn [lcalls segs]; try reflexivity.
    rewrite flat_map_app. f_equal.
    - rewrite fm_fm. apply flat_map_ext. intros [[[s' a'] b'] r].
      cbn [literq isegq liter iseg flat_map segcalls]. rewrite app_nil_r. reflexivity.
    - cbn [liter iseg flat_map segcalls]. rewrite app_nil_r. reflexivity.
  Qed.

  Lemma ltrace_sg p : ltrace p = flat_map segcalls (sg p).
  Proof. unfold ltrace, sg. rewrite fm_fm. apply flat_map_ext, lcalls_segs. Qed.

  Lemma tprog_sg p : tprog p = flat_map segtl (sg p).
  Proof. unfold tprog, sg, tblks. rewrite fm_fm. reflexivity. Qed.

  (** The TicketLock trace is the [LT] part of the low-level trace. *)
  Lemma tl_ltp l : flat_map TL.tcalls (flat_map segtl l) = flat_map ltp (flat_map segcalls l).
  Proof.
    rewrite !fm_fm. apply flat_map_ext. intros [k|c]; cbn [segtl segcalls flat_map]; [|reflexivity].
    rewrite app_nil_r. induction (TL.tcalls k) as [|c l' IH]; cbn; [reflexivity|]. f_equal. exact IH.
  Qed.

  Lemma tprog_trace p : TL.trace (tprog p) = flat_map ltp (ltrace p).
  Proof. unfold TL.trace. rewrite tprog_sg, ltrace_sg. apply tl_ltp. Qed.

  Lemma calls_abs k : blk_ok k = true -> SL.calls (abs k) = map segsl (segs k).
  Proof.
    destruct k as [vx vy tk sp|its s a b|v|v]; cbn [blk_ok]; intros H; try reflexivity.
    apply andb_true_iff in H as [Hs Hits]. cbn [abs segs SL.calls]. rewrite map_app. f_equal.
    - induction its as [|[[[s' a'] b'] r] its IH]; [reflexivity|].
      cbn [forallb] in Hits. apply andb_true_iff in Hits as [H1 H2].
      cbn [map drop4 SL.fail_calls flat_map isegq iseg]. rewrite map_app. f_equal; [|apply IH, H2].
      cbn [iter_ok] in H1. cbn. rewrite H1. reflexivity.
    - cbn. rewrite <- Nat.negb_even, Hs, Nat.eqb_refl. reflexivity.
  Qed.

  Lemma trace_abs p : forallb blk_ok p = true -> SL.trace (map abs p) = map segsl (sg p).
  Proof.
    induction p as [|k p IH]; cbn [forallb]; intros H; [reflexivity|].
    apply andb_true_iff in H as [H1 H2]. unfold SL.trace, sg in *. cbn [map flat_map].
    rewrite map_app, calls_abs by exact H1. f_equal. apply IH, H2.
  Qed.

  Lemma forallb_firstn {A} (g : A -> bool) l j : forallb g l = true -> forallb g (firstn j l) = true.
  Proof.
    intros H. apply forallb_forall. intros x Hx. rewrite forallb_forall in H.
    apply H. rewrite <- (firstn_skipn j l). apply in_or_app. left. exact Hx.
  Qed.

  Lemma off_abs p j : forallb blk_ok p = true -> SL.off (map abs p) j = fo segs p j.
  Proof.
    intros H. unfold SL.off, fo. rewrite firstn_map, trace_abs by (apply forallb_firstn, H).
    rewrite length_map. reflexivity.
  Qed.

  Lemma loff_fo p j : loff p j = fo segcalls (sg p) (fo segs p j).
  Proof.
    change (fo segcalls (sg p) (fo segs p j))
      with (length (flat_map segcalls (firstn (fo segs p j) (flat_map segs p)))).
    rewrite fm_firstn0. unfold loff. rewrite ltrace_sg. reflexivity.
  Qed.

  (** SD segments carry data calls. *)
  Ltac in_lit H :=
    cbn in H; repeat (destruct H as [H|H]; [first [discriminate H | injection H as <-; reflexivity]|]);
    contradiction.

  Lemma segs_SD k c : In (SD c) (segs k) -> is_tlc c = false.
  Proof.
    destruct k as [vx vy tk sp|its s a b|v|v]; cbn [segs]; intros H.
    - in_lit H.
    - apply in_app_or in H as [H|H].
      + apply in_flat_map in H as ([[[s' a'] b'] r] & _ & H). in_lit H.
      + in_lit H.
    - in_lit H.
    - in_lit H.
  Qed.

  Lemma sg_SD p i c : nth_error (sg p) i = Some (SD c) -> is_tlc c = false.
  Proof.
    intros H. apply nth_error_In in H. unfold sg in H. apply in_flat_map in H as (k & _ & H).
    exact (segs_SD k c H).
  Qed.

  (** A TicketLock call of the SeqLock layer is an [ST] segment. *)
  Lemma sg_tl p i s : nth_error (sg p) i = Some s -> is_tlc (segsl s) = true -> exists k, s = ST k.
  Proof.
    intros H Ht. destruct s as [k|c]; [eauto|].
    cbn in Ht. rewrite (sg_SD p i c H) in Ht. discriminate.
  Qed.

  (** *** Silent [test_ticket]s *)

  (** A silent segment is the last of a failed iteration: before it the
      iteration's [get_ticket], [rmb], [x.rd], [y.rd], [rmb]; after it the
      next iteration's [get_ticket]. *)
  Definition sil_facts (l : list Seg) (i : nat) : Prop :=
    5 <= i /\ S i < length l /\
    (exists s, nth_error l (i - 5) = Some (ST (TL.TGt s))) /\
    nth_error l (i - 4) = Some (SD SL.RmbC) /\
    (exists a, nth_error l (i - 3) = Some (SD (SL.RdX a))) /\
    (exists b, nth_error l (i - 2) = Some (SD (SL.RdY b))) /\
    nth_error l (i - 1) = Some (SD SL.RmbC) /\
    (exists s', nth_error l (S i) = Some (ST (TL.TGt s'))).

  Lemma sil_transfer l1 l2 d i :
    (forall n, n < length l1 -> nth_error l2 (d + n) = nth_error l1 n) ->
    d + length l1 <= length l2 ->
    sil_facts l1 i -> sil_facts l2 (d + i).
  Proof.
    intros Hn Hl (H5 & HS & (s & E5) & E4 & (a & E3) & (b & E2) & E1 & (s' & ES)).
    assert (R : forall n, n <= 5 -> d + i - n = d + (i - n)) by (intros; lia).
    split; [lia|]. split; [lia|].
    rewrite !R by lia. rewrite <- Nat.add_succ_r.
    rewrite !Hn by lia.
    repeat split; eauto.
  Qed.

  Definition starts_gt (l : list Seg) : Prop := exists s, nth_error l 0 = Some (ST (TL.TGt s)).

  Lemma iters_silent its F i x :
    starts_gt F -> (forall j y, nth_error F j = Some y -> silent y = false) ->
    nth_error (flat_map isegq its ++ F) i = Some x -> silent x = true ->
    sil_facts (flat_map isegq its ++ F) i.
  Proof.
    intros HF HnF. revert i. induction its as [|[[[s' a'] b'] r] its IH]; intros i Hx Hs.
    - cbn in Hx. rewrite (HnF i x Hx) in Hs. discriminate.
    - cbn [flat_map isegq]. rewrite <- app_assoc.
      cbn [flat_map isegq] in Hx. rewrite <- app_assoc in Hx.
      set (R := flat_map isegq its ++ F) in *.
      assert (HR : starts_gt R).
      { unfold R. destruct its as [|[[[s'' a''] b''] r''] its']; [exact HF|].
        exists s''. reflexivity. }
      assert (HRl : 0 < length R) by (destruct HR as [s0 H0]; destruct R; [discriminate|cbn; lia]).
      destruct (Nat.lt_ge_cases i 6) as [Hi|Hi].
      + rewrite nth_error_app1 in Hx by (cbn; lia).
        destruct i as [|[|[|[|[|[|i]]]]]]; try lia; cbn in Hx; injection Hx as <-; cbn in Hs;
          try discriminate.
        destruct HR as [s0 H0].
        split; [lia|]. split; [rewrite length_app; cbn; lia|].
        cbn. repeat split; eauto.
      + rewrite nth_error_app2 in Hx by (cbn; lia).
        pose proof (IH (i - 6) Hx Hs) as Hf.
        replace i with (length (iseg s' a' b' r) + (i - 6)) by (cbn; lia).
        apply (sil_transfer R); [| rewrite length_app; lia | exact Hf].
        intros n Hn. rewrite nth_error_app2 by lia. f_equal. lia.
  Qed.

  Lemma blk_silent k i x :
    blk_ok k = true -> nth_error (segs k) i = Some x -> silent x = true -> sil_facts (segs k) i.
  Proof.
    destruct k as [vx vy tk sp|its s a b|v|v]; cbn [blk_ok segs]; intros Hok Hx Hs.
    - destruct i as [|[|[|[|[|[|i]]]]]]; cbn in Hx; try (destruct i; discriminate);
        injection Hx as <-; cbn in Hs; discriminate.
    - apply andb_true_iff in Hok as [He _]. apply (iters_silent its _ i x); try assumption.
      + exists s. reflexivity.
      + intros j y Hy. destruct j as [|[|[|[|[|[|j]]]]]]; cbn in Hy; try (destruct j; discriminate);
          injection Hy as <-; try reflexivity.
        cbn. rewrite <- Nat.negb_even, He. reflexivity.
    - destruct i as [|i]; cbn in Hx; [|destruct i; discriminate]. injection Hx as <-. discriminate.
    - destruct i as [|i]; cbn in Hx; [|destruct i; discriminate]. injection Hx as <-. discriminate.
  Qed.

  (** The same, in the thread's segment list, with the block it lies in. *)
  Lemma sg_silent p i x :
    forallb blk_ok p = true -> nth_error (sg p) i = Some x -> silent x = true ->
    exists j k i', nth_error p j = Some k /\ i = fo segs p j + i' /\
      sil_facts (segs k) i' /\ sil_facts (sg p) i.
  Proof.
    intros Hok Hx Hs. unfold sg in Hx. destruct (fm_inv segs p i x Hx) as (j & k & i' & Hj & -> & Hi').
    assert (Hk : blk_ok k = true).
    { rewrite forallb_forall in Hok. apply Hok. eapply nth_error_In. exact Hj. }
    pose proof (blk_silent k i' x Hk Hi' Hs) as Hf.
    exists j, k, i'. split; [exact Hj|]. split; [reflexivity|]. split; [exact Hf|].
    apply (sil_transfer (segs k)); [| | exact Hf].
    - intros n Hn. apply fm_nth; assumption.
    - pose proof (fo_S segs p j k Hj). pose proof (fo_le_len segs p (S j)). unfold sg. lia.
  Qed.

  (** *** The TicketLock projection is bracketed *)

  Lemma tblks_LBR_norel its s a b : ~ In TL.TRel (tblks (LBR its s a b)).
  Proof.
    unfold tblks. cbn [segs]. intros H. apply in_flat_map in H as (x & Hx & H).
    apply in_app_or in Hx as [Hx|Hx].
    - apply in_flat_map in Hx as ([[[s' a'] b'] r] & _ & Hx). cbn in Hx.
      intuition (subst; cbn in H; intuition discriminate).
    - cbn in Hx. intuition (subst; cbn in H; intuition discriminate).
  Qed.

  Lemma rel_prev p j :
    nth_error (tprog p) j = Some TL.TRel ->
    0 < j /\ exists tk sp, nth_error (tprog p) (pred j) = Some (TL.TAcq tk sp).
  Proof.
    revert j. induction p as [|k p IH]; intros j H; [destruct j; discriminate|].
    unfold tprog in *. cbn [flat_map] in *.
    destruct (Nat.lt_ge_cases j (length (tblks k))) as [Hj|Hj].
    - rewrite nth_error_app1 in H by exact Hj.
      destruct k as [vx vy tk sp|its s a b|v|v].
      + destruct j as [|[|j]]; cbn in H; try discriminate; [|destruct j; discriminate].
        split; [lia|]. exists tk, sp. reflexivity.
      + exfalso. apply (tblks_LBR_norel its s a b). eapply nth_error_In. exact H.
      + cbn in Hj. lia.
      + cbn in Hj. lia.
    - rewrite nth_error_app2 in H by exact Hj.
      destruct (IH _ H) as [Hpos (tk & sp & Ha)]. split; [lia|]. exists tk, sp.
      rewrite nth_error_app2 by lia. rewrite <- Ha. f_equal. lia.
  Qed.

  Lemma tprog_bracketed p : TL.bracketed (tprog p).
  Proof.
    intros j Hj. destruct (rel_prev p j Hj) as [Hpos (tk & sp & Ha)].
    exists (pred j). split; [lia|]. split; [eauto|].
    intros m k Hm1 Hm2. lia.
  Qed.

  (** *** Representatives *)

  Lemma wcall_nth k : TL.has_call k = true -> nth_error (TL.tcalls k) (TL.lpi k) = Some (wcall k).
  Proof.
    destruct k as [tk sp| |s|s r]; intros Hc.
    - exact (proj2 (proj2 (TL.acq_calls tk sp))).
    - reflexivity.
    - reflexivity.
    - cbn [TL.has_call] in Hc. apply negb_true_iff in Hc. cbn [TL.tcalls TL.lpi wcall]. rewrite Hc. reflexivity.
  Qed.

  Lemma same_lobj_oimg o1 o2 : same_lobj (oimg o1) (oimg o2) = SL.same_obj o1 o2.
  Proof. destruct o1, o2; reflexivity. Qed.

  (** A segment's SeqLock-layer call and its representative low-level call
      have the same object and the same category. *)
  Lemma rep_obj s : lobj (repc s) = oimg (SL.uobj (segsl s)).
  Proof. destruct s as [[]|c]; reflexivity. Qed.

  Lemma rep_cat C s : lcat C (repc s) = SL.ucat (TL.tl_cats C) (segsl s).
  Proof. destruct s as [[]|c]; reflexivity. Qed.

  Lemma lpres_rep rc C s1 s2 :
    lpres rc C (repc s1) (repc s2) = SL.upres rc (TL.tl_cats C) (segsl s1) (segsl s2).
  Proof. unfold lpres, SL.upres. rewrite !rep_obj, !rep_cat, same_lobj_oimg. reflexivity. Qed.

  (** ** The SeqLock-layer witness *)

  (** The low-level index of the call representing the [i]-th SeqLock
      call of a thread (for a silent [test_ticket], the [rmb] before it),
      and its rank among the calls that low-level call represents. *)
  Definition rho (G : list Seg) (i : nat) : nat :=
    match nth_error G i with
    | Some (ST k) => if TL.has_call k then fo segcalls G i + TL.lpi k else fo segcalls G (pred i)
    | _ => fo segcalls G i
    end.

  Definition kappa (G : list Seg) (i : nat) : nat :=
    match nth_error G i with Some (ST k) => if TL.has_call k then 0 else 1 | _ => 0 end.

  (** The SeqLock calls represented by the low-level call at offset [o] of
      segment [m]. *)
  Definition emits (G : list Seg) (t : nat) (mo : nat * nat) : list SL.Ev :=
    let '(m, o) := mo in
    match nth_error G m with
    | Some (ST k) => if Nat.eqb o (TL.lpi k) then [SL.mkEv t m (tlcall k)] else []
    | Some (SD c) =>
        SL.mkEv t m c ::
        match nth_error G (S m) with
        | Some (ST k') => if TL.has_call k' then [] else [SL.mkEv t (S m) (tlcall k')]
        | _ => []
        end
    | None => []
    end.

  Definition emit0 (X0 : Exec0) (e : LEv) : list SL.Ev :=
    emits (sg (prog0 X0 (lth e))) (lth e) (loc segcalls (sg (prog0 X0 (lth e))) (lix e)).

  Definition W1 (X0 : Exec0) : list SL.Ev := flat_map (emit0 X0) (wit0 X0).

  (** The SeqLock-layer execution. *)
  Definition X1 (X0 : Exec0) : SL.Exec :=
    {| SL.ths := ths0 X0; SL.prog := fun t => map abs (prog0 X0 t); SL.wit := W1 X0 |}.

  Lemma rho_ns G i s :
    nth_error G i = Some s -> silent s = false ->
    nth_error (flat_map segcalls G) (rho G i) = Some (repc s) /\
    exists o, rho G i = fo segcalls G i + o /\ o < length (segcalls s) /\ kappa G i = 0.
  Proof.
    intros Hi Hs. unfold rho, kappa. rewrite Hi. destruct s as [k|c].
    - cbn [silent] in Hs. apply negb_false_iff in Hs. rewrite Hs.
      pose proof (wcall_nth k Hs) as Hw.
      assert (Hl : TL.lpi k < length (segcalls (ST k)))
        by (cbn [segcalls]; rewrite length_map; apply nth_error_Some; congruence).
      split; [|exists (TL.lpi k); auto].
      rewrite (fm_nth segcalls G i (ST k) _ Hi Hl). cbn [segcalls repc]. rewrite nth_error_map, Hw.
      reflexivity.
    - split; [|exists 0; cbn; repeat split; lia].
      rewrite <- (Nat.add_0_r (fo segcalls G i)), (fm_nth segcalls G i (SD c) 0 Hi) by (cbn; lia).
      reflexivity.
  Qed.

  Lemma rho_s G i s :
    nth_error G i = Some s -> silent s = true -> rho G i = fo segcalls G (pred i) /\ kappa G i = 1.
  Proof.
    intros Hi Hs. unfold rho, kappa. rewrite Hi. destruct s as [k|c]; [|discriminate].
    cbn [silent] in Hs. apply negb_true_iff in Hs. rewrite Hs. split; reflexivity.
  Qed.

  Lemma emits_spec G t m o s k e :
    nth_error G m = Some s -> o < length (segcalls s) -> nth_error (emits G t (m, o)) k = Some e ->
    SL.th e = t /\ fo segcalls G m + o = rho G (SL.ix e) /\ k = kappa G (SL.ix e) /\
    exists s', nth_error G (SL.ix e) = Some s' /\ SL.call e = segsl s'.
  Proof.
    intros Hm Ho He. unfold emits in He. rewrite Hm in He. destruct s as [kb|c].
    - destruct (Nat.eqb o (TL.lpi kb)) eqn:Eo; [|destruct k; discriminate].
      apply Nat.eqb_eq in Eo. subst o.
      destruct k as [|k]; [|destruct k; discriminate]. injection He as <-. cbn [SL.th SL.ix SL.call].
      assert (Hc : TL.has_call kb = true).
      { destruct (TL.has_call kb) eqn:E; [reflexivity|].
        cbn [segcalls] in Ho. rewrite length_map, TL.tcalls_silent in Ho by exact E. cbn in Ho. lia. }
      unfold rho, kappa. rewrite Hm, Hc.
      split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
      exists (ST kb). split; reflexivity.
    - cbn [segcalls length] in Ho. assert (o = 0) by lia. subst o.
      destruct k as [|k].
      + injection He as <-. cbn [SL.th SL.ix SL.call]. unfold rho, kappa. rewrite Hm.
        split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
        exists (SD c). split; reflexivity.
      + destruct (nth_error G (S m)) as [[kb'|c']|] eqn:Hm'; try (destruct k; discriminate).
        destruct (TL.has_call kb') eqn:Hc; [destruct k; discriminate|].
        destruct k as [|k]; [|destruct k; discriminate]. cbn in He. injection He as <-.
        cbn [SL.th SL.ix SL.call]. unfold rho, kappa. rewrite Hm', Hc. cbn [pred].
        split; [reflexivity|]. split; [lia|]. split; [reflexivity|].
        exists (ST kb'). split; reflexivity.
  Qed.

  Lemma emits_complete G t i s :
    nth_error G i = Some s ->
    (silent s = true -> 0 < i /\ exists c, nth_error G (pred i) = Some (SD c)) ->
    exists m o s0 k, nth_error G m = Some s0 /\ o < length (segcalls s0) /\
      nth_error (emits G t (m, o)) k = Some (SL.mkEv t i (segsl s)).
  Proof.
    intros Hi Hsil. destruct (silent s) eqn:Hs.
    - destruct (Hsil eq_refl) as [Hpos [c Hc]].
      destruct s as [kb|c']; [|discriminate]. cbn [silent] in Hs. apply negb_true_iff in Hs.
      exists (pred i), 0, (SD c), 1. split; [exact Hc|]. split; [cbn; lia|].
      unfold emits. rewrite Hc. replace (S (pred i)) with i by lia. rewrite Hi, Hs. reflexivity.
    - destruct s as [kb|c].
      + cbn [silent] in Hs. apply negb_false_iff in Hs.
        exists i, (TL.lpi kb), (ST kb), 0. split; [exact Hi|]. split.
        * cbn [segcalls]. rewrite length_map. apply nth_error_Some. rewrite (wcall_nth kb Hs). discriminate.
        * unfold emits. rewrite Hi, Nat.eqb_refl. reflexivity.
      + exists i, 0, (SD c), 0. split; [exact Hi|]. split; [cbn; lia|].
        unfold emits. rewrite Hi. reflexivity.
  Qed.

  Lemma emits_nodup G t mo : NoDup (emits G t mo).
  Proof.
    destruct mo as [m o]. unfold emits.
    destruct (nth_error G m) as [[kb|c]|]; [| |constructor].
    - destruct (Nat.eqb o (TL.lpi kb)); repeat constructor. intros [].
    - destruct (nth_error G (S m)) as [[kb'|c']|]; [destruct (TL.has_call kb')| |];
        repeat constructor; cbn; try tauto.
      intros [E|[]]. injection E. lia.
  Qed.

  (** ** The TicketLock projection *)

  (** Index of a low-level [LT] call in the thread's TicketLock trace. *)
  Definition tix (p : list LBlk) (i : nat) : nat := fo ltp (ltrace p) i.

  Definition toT (X0 : Exec0) (e : LEv) : list TL.Ev :=
    match lcall e with
    | LT c => [TL.mkEv (lth e) (tix (prog0 X0 (lth e)) (lix e)) c]
    | LD _ => []
    end.

  Definition XT (X0 : Exec0) : TL.Exec :=
    {| TL.ths := ths0 X0; TL.prog := fun t => tprog (prog0 X0 t); TL.wit := flat_map (toT X0) (wit0 X0) |}.

  (** The TicketLock operation of the [ST] segment [i]. *)
  Definition tnum (G : list Seg) (i : nat) : nat := fo segtl G i.

  Lemma ltp_map_LT l : flat_map ltp (map LT l) = l.
  Proof. induction l as [|c l IH]; cbn; [reflexivity|]. f_equal. exact IH. Qed.

  Lemma toT_run X0 l s s0 :
    TL.own s = lown s0 -> TL.nxt s = lnxt s0 ->
    TL.own (TL.run s (flat_map (toT X0) l)) = lown (lrun s0 l) /\
    TL.nxt (TL.run s (flat_map (toT X0) l)) = lnxt (lrun s0 l).
  Proof.
    revert s s0. induction l as [|e l IH]; intros s s0 Ho Hn; [split; assumption|].
    cbn [flat_map lrun]. rewrite TL.run_app. apply IH.
    - unfold toT, lpost. destruct (lcall e) as [[r|v|]|c]; cbn; try rewrite Ho; try reflexivity.
      destruct c; reflexivity.
    - unfold toT, lpost. destruct (lcall e) as [[r|v|]|c]; cbn; try rewrite Hn; try reflexivity.
      destruct c; reflexivity.
  Qed.

  (** The low-level index of a TicketLock op's call, in TicketLock terms. *)
  Lemma tix_seg p i kb o :
    nth_error (sg p) i = Some (ST kb) -> o <= length (TL.tcalls kb) ->
    tix p (fo segcalls (sg p) i + o) = TL.off (tprog p) (tnum (sg p) i) + o.
  Proof.
    intros Hi Ho. unfold tix, TL.off, tnum. unfold fo at 1.
    rewrite ltrace_sg, (fm_firstn segcalls _ i (ST kb) o Hi) by (cbn [segcalls]; rewrite length_map; exact Ho).
    rewrite flat_map_app. cbn [segcalls]. rewrite firstn_map, ltp_map_LT, length_app, length_firstn.
    rewrite tprog_sg. unfold TL.trace. rewrite fm_firstn0, tl_ltp. lia.
  Qed.

  Lemma blk_tnum X0 t i kb :
    nth_error (sg (prog0 X0 t)) i = Some (ST kb) -> TL.blk (XT X0) (t, tnum (sg (prog0 X0 t)) i) = Some kb.
  Proof.
    intros Hi. unfold TL.blk. cbn [fst snd XT TL.prog]. rewrite tprog_sg. unfold tnum.
    rewrite <- (Nat.add_0_r (fo segtl _ i)), (fm_nth segtl _ i (ST kb) 0 Hi) by (cbn; lia). reflexivity.
  Qed.

  (** The abstract TicketLock operation of a SeqLock-layer call. *)
  Definition absop (c : SL.UC) : TL.TOp :=
    match c with
    | SL.Acq => TL.OAcq | SL.Rel => TL.ORel | SL.GT s => TL.OGt s | SL.TT s r => TL.OTt s r
    | _ => TL.OGt 0
    end.

  Definition absev (e : SL.Ev) : nat * TL.TOp := (SL.th e, absop (SL.call e)).

  Definition tlop_of (X0 : Exec0) (e : SL.Ev) : nat * nat :=
    (SL.th e, tnum (sg (prog0 X0 (SL.th e))) (SL.ix e)).

  Lemma tlop_absop c : is_tlc c = true -> TL.tlop c = Some (absop c).
  Proof. destruct c; cbn; congruence. Qed.

  Lemma post_ntl s e : is_tlc (SL.call e) = false ->
    SL.own (SL.post s e) = SL.own s /\ SL.hold (SL.post s e) = SL.hold s.
  Proof. unfold SL.post. destruct (SL.call e); cbn; try discriminate; auto. Qed.

  (** If the TicketLock calls of a SeqLock-layer witness, in order, are
      accepted by the abstract TicketLock specification, they are valid
      ([spec_match]). *)
  Lemma tl_valid l s :
    TL.tl_ok (SL.own s, SL.hold s) (map absev (filter (fun e => is_tlc (SL.call e)) l)) ->
    forall p e, nth_error l p = Some e -> is_tlc (SL.call e) = true ->
    SL.pre (SL.run s (firstn p l)) e = true.
  Proof.
    revert s. induction l as [|e' l IH]; intros s Hok p e Hp Ht; [destruct p; discriminate|].
    cbn [filter] in Hok. destruct (is_tlc (SL.call e')) eqn:Te'.
    - cbn [map TL.tl_ok] in Hok.
      change (TL.tl_step (SL.own s, SL.hold s) (absev e'))
        with (TL.tl_step (SL.own s, SL.hold s) (SL.th e', absop (SL.call e'))) in Hok.
      pose proof (TL.spec_match s e' (absop (SL.call e')) (tlop_absop _ Te')) as Hm.
      destruct (TL.tl_step (SL.own s, SL.hold s) (SL.th e', absop (SL.call e'))) as [[v h]|];
        [|contradiction].
      destruct Hm as (Hpre & Ho & Hh).
      destruct p as [|p].
      + cbn in Hp. injection Hp as <-. exact Hpre.
      + cbn [firstn SL.run]. apply IH; [|exact Hp|exact Ht]. rewrite Ho, Hh. exact Hok.
    - destruct p as [|p].
      + cbn in Hp. injection Hp as <-. congruence.
      + cbn [firstn SL.run]. apply IH; [|exact Hp|exact Ht].
        destruct (post_ntl s e' Te') as [-> ->]. exact Hok.
  Qed.

  Lemma filter_filter' {A} (f g : A -> bool) l : filter g (filter f l) = filter (fun x => f x && g x) l.
  Proof. induction l as [|a l IH]; cbn; [reflexivity|]. destruct (f a); cbn; [destruct (g a)|]; rewrite IH; reflexivity. Qed.

  (** Values of the cells. *)
  Definition dsim (s : SL.State) (s0 : LState) : Prop :=
    SL.sx s = lx s0 /\ SL.sy s = ly s0 /\ SL.sz s = lz s0.

  Lemma dsim_post_tl s s0 e : is_tlc (SL.call e) = true -> dsim s s0 -> dsim (SL.post s e) s0.
  Proof. unfold dsim, SL.post. destruct (SL.call e); cbn; try discriminate; auto. Qed.

  Lemma dsim_post_LD s s0 e x c : lcall x = LD c -> SL.call e = c -> dsim s s0 -> dsim (SL.post s e) (lpost s0 x).
  Proof.
    unfold dsim, SL.post, lpost. intros Hx He. rewrite Hx, He. intros (H1 & H2 & H3).
    destruct c; cbn; auto.
  Qed.

  Lemma dsim_lpost_LT s s0 x c : lcall x = LT c -> dsim s s0 -> dsim s (lpost s0 x).
  Proof. unfold dsim, lpost. intros Hx. rewrite Hx. destruct c; cbn; auto. Qed.

  Lemma dsim_run_tl s s0 l : Forall (fun e => is_tlc (SL.call e) = true) l -> dsim s s0 -> dsim (SL.run s l) s0.
  Proof.
    revert s. induction l as [|e l IH]; intros s Hf Hd; [exact Hd|].
    inversion Hf as [|? ? He Hl]; subst. cbn. apply IH; [exact Hl|]. apply dsim_post_tl; assumption.
  Qed.

  Lemma tlcall_tl k : is_tlc (tlcall k) = true.
  Proof. destruct k; reflexivity. Qed.

  Lemma fo_nested p j k i :
    nth_error p j = Some k -> i <= length (segs k) ->
    fo segcalls (sg p) (fo segs p j + i) = fo segcalls (sg p) (fo segs p j) + fo segcalls (segs k) i.
  Proof.
    intros Hj Hi.
    change (fo segcalls (sg p) (fo segs p j + i))
      with (length (flat_map segcalls (firstn (fo segs p j + i) (flat_map segs p)))).
    change (fo segcalls (sg p) (fo segs p j))
      with (length (flat_map segcalls (firstn (fo segs p j) (flat_map segs p)))).
    rewrite (fm_firstn segs p j k i Hj Hi), fm_firstn0, flat_map_app, length_app. reflexivity.
  Qed.

  Lemma kappa_SD G i c : nth_error G i = Some (SD c) -> kappa G i = 0.
  Proof. intros H. unfold kappa. rewrite H. reflexivity. Qed.

  (** Witness order of operations at the SeqLock layer: every call of [q]
      before every call of [q'] in the witness (the [rt] of
      [SeqLockCOH.setting]). *)
  Definition rt1 (X : SL.Exec) (q q' : nat * nat) : Prop :=
    forall k k' i i', SL.blk X q = Some k -> SL.blk X q' = Some k' ->
      i < length (SL.calls k) -> i' < length (SL.calls k') -> SL.Pq X q i < SL.Pq X q' i'.

  (** ** The link *)

  Section Link.
    Context (rc : bool) (C : TL.CCats) (X0 : Exec0).
    Hypothesis HW0 : WF0 rc C X0.
    Hypothesis HK : SL.K_ok (TL.tl_cats C) = true.

    Let HKg : isR (TL.k_get C) = true.
    Proof. unfold SL.K_ok in HK. cbn in HK. repeat (apply andb_true_iff in HK as [HK ?]). assumption. Qed.

    (** *** Low-level facts *)

    Lemma ev_evt0 e : In e (wit0 X0) -> e = evt0 X0 (lth e) (lix e).
    Proof.
      intros H. destruct (wf0_call _ _ _ HW0 e H) as [_ Hn].
      destruct e as [t i c]. unfold evt0. cbn in *. f_equal. symmetry. apply nth_error_nth. exact Hn.
    Qed.

    Lemma lidx_P0 e : In e (wit0 X0) -> lidx e (wit0 X0) = P0 X0 (lth e) (lix e).
    Proof. intros H. unfold P0. rewrite <- (ev_evt0 e H). reflexivity. Qed.

    Lemma evt0_spec t i c :
      In t (ths0 X0) -> nth_error (ltrace (prog0 X0 t)) i = Some c ->
      In (evt0 X0 t i) (wit0 X0) /\ lcall (evt0 X0 t i) = c /\
      nth_error (wit0 X0) (P0 X0 t i) = Some (evt0 X0 t i).
    Proof.
      intros Ht Hi. assert (Hin : In (evt0 X0 t i) (wit0 X0)).
      { apply (wf0_complete _ _ _ HW0 t i Ht). apply nth_error_Some. congruence. }
      split; [exact Hin|]. split.
      - unfold evt0. cbn. apply nth_error_nth. exact Hi.
      - apply lidx_nth, Hin.
    Qed.

    Lemma P0_cross t i i' c c' :
      In t (ths0 X0) -> nth_error (ltrace (prog0 X0 t)) i = Some c ->
      nth_error (ltrace (prog0 X0 t)) i' = Some c' -> i < i' -> lpres rc C c c' = true ->
      P0 X0 t i < P0 X0 t i'.
    Proof.
      intros Ht Hi Hi' Hlt Hp.
      destruct (evt0_spec t i c Ht Hi) as (In1 & E1 & _).
      destruct (evt0_spec t i' c' Ht Hi') as (In2 & E2 & _).
      unfold P0. apply (wf0_pres _ _ _ HW0); [exact In1|exact In2|reflexivity|exact Hlt|].
      rewrite E1, E2. exact Hp.
    Qed.

    Lemma ths_ok t : In t (ths0 X0) -> forallb blk_ok (prog0 X0 t) = true.
    Proof. apply (wf0_blk _ _ _ HW0). Qed.

    (** Every low-level event, located in its thread's segments. *)
    Lemma emit0_loc e :
      In e (wit0 X0) ->
      exists m o s, nth_error (sg (prog0 X0 (lth e))) m = Some s /\ o < length (segcalls s) /\
        lix e = fo segcalls (sg (prog0 X0 (lth e))) m + o /\
        nth_error (segcalls s) o = Some (lcall e) /\
        emit0 X0 e = emits (sg (prog0 X0 (lth e))) (lth e) (m, o).
    Proof.
      intros He. destruct (wf0_call _ _ _ HW0 e He) as [_ Hn]. rewrite ltrace_sg in Hn.
      destruct (fm_inv segcalls _ _ _ Hn) as (m & s & o & Hm & Ei & Ho).
      assert (Hlt : o < length (segcalls s)) by (apply nth_error_Some; congruence).
      exists m, o, s. split; [exact Hm|]. split; [exact Hlt|]. split; [exact Ei|]. split; [exact Ho|].
      unfold emit0. rewrite Ei, (loc_fo segcalls _ m s o Hm Hlt). reflexivity.
    Qed.

    Lemma emit0_spec e0 k e :
      In e0 (wit0 X0) -> nth_error (emit0 X0 e0) k = Some e ->
      SL.th e = lth e0 /\ lix e0 = rho (sg (prog0 X0 (lth e0))) (SL.ix e) /\
      k = kappa (sg (prog0 X0 (lth e0))) (SL.ix e) /\
      exists s', nth_error (sg (prog0 X0 (lth e0))) (SL.ix e) = Some s' /\ SL.call e = segsl s'.
    Proof.
      intros He0 Hk. destruct (emit0_loc e0 He0) as (m & o & s & Hm & Ho & Ei & _ & Ee).
      rewrite Ee in Hk. destruct (emits_spec _ _ _ _ _ _ _ Hm Ho Hk) as (Et & Er & Ek & Hs).
      split; [exact Et|]. split; [rewrite Ei; exact Er|]. split; [exact Ek|exact Hs].
    Qed.

    Lemma W1_elem e :
      In e (W1 X0) ->
      exists p0 e0 k, nth_error (wit0 X0) p0 = Some e0 /\ nth_error (emit0 X0 e0) k = Some e /\
        In (SL.th e) (ths0 X0) /\ lth e0 = SL.th e /\
        lix e0 = rho (sg (prog0 X0 (SL.th e))) (SL.ix e) /\
        k = kappa (sg (prog0 X0 (SL.th e))) (SL.ix e) /\
        p0 = P0 X0 (SL.th e) (rho (sg (prog0 X0 (SL.th e))) (SL.ix e)) /\
        exists s', nth_error (sg (prog0 X0 (SL.th e))) (SL.ix e) = Some s' /\ SL.call e = segsl s'.
    Proof.
      intros He. unfold W1 in He. apply in_flat_map in He as (e0 & He0 & Hin).
      destruct (In_nth_error _ _ He0) as [p0 Hp0]. destruct (In_nth_error _ _ Hin) as [k Hk].
      destruct (emit0_spec e0 k e He0 Hk) as (Et & Ei & Ek & Hs).
      rewrite <- Et in Ei, Ek, Hs.
      exists p0, e0, k. split; [exact Hp0|]. split; [exact Hk|].
      split; [rewrite Et; exact (proj1 (wf0_call _ _ _ HW0 e0 He0))|]. split; [symmetry; exact Et|].
      split; [exact Ei|]. split; [exact Ek|]. split; [|exact Hs].
      rewrite <- Ei, Et. rewrite <- (nth_lidx _ _ _ (wf0_nodup _ _ _ HW0) Hp0). rewrite lidx_P0 by exact He0.
      rewrite <- Et. reflexivity.
    Qed.

    (** *** [SeqLockCOH.WF] for [X1]: the shape of the witness *)

    Lemma W1_nodup : NoDup (W1 X0).
    Proof.
      apply NoDup_fm; [exact (wf0_nodup _ _ _ HW0)| |].
      - intros x _. unfold emit0. apply emits_nodup.
      - intros x y b Hx Hy Hbx Hby.
        destruct (In_nth_error _ _ Hbx) as [k Hk]. destruct (In_nth_error _ _ Hby) as [k' Hk'].
        destruct (emit0_spec x k b Hx Hk) as (Tx & Ix & _).
        destruct (emit0_spec y k' b Hy Hk') as (Ty & Iy & _).
        assert (Et : lth x = lth y) by congruence.
        assert (Ei : lix x = lix y) by (rewrite Ix, Iy, Et; reflexivity).
        rewrite (ev_evt0 x Hx), (ev_evt0 y Hy), Et, Ei. reflexivity.
    Qed.

    Lemma X1_trace t : In t (ths0 X0) -> SL.trace (SL.prog (X1 X0) t) = map segsl (sg (prog0 X0 t)).
    Proof. intros Ht. apply trace_abs, ths_ok, Ht. Qed.

    Lemma W1_call e :
      In e (W1 X0) ->
      In (SL.th e) (ths0 X0) /\ nth_error (SL.trace (SL.prog (X1 X0) (SL.th e))) (SL.ix e) = Some (SL.call e).
    Proof.
      intros He. destruct (W1_elem e He) as (p0 & e0 & k & _ & _ & Ht & _ & _ & _ & _ & s' & Hs & Ec).
      split; [exact Ht|]. rewrite X1_trace by exact Ht. rewrite nth_error_map, Hs, Ec. reflexivity.
    Qed.

    Lemma X1_evt t i s :
      In t (ths0 X0) -> nth_error (sg (prog0 X0 t)) i = Some s -> SL.evt (X1 X0) t i = SL.mkEv t i (segsl s).
    Proof.
      intros Ht Hi. unfold SL.evt. f_equal. apply nth_error_nth.
      rewrite X1_trace by exact Ht. rewrite nth_error_map, Hi. reflexivity.
    Qed.

    Lemma W1_complete t i :
      In t (ths0 X0) -> i < length (SL.trace (SL.prog (X1 X0) t)) -> In (SL.evt (X1 X0) t i) (W1 X0).
    Proof.
      intros Ht Hi. rewrite X1_trace, length_map in Hi by exact Ht.
      destruct (nth_error (sg (prog0 X0 t)) i) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
      rewrite (X1_evt t i s Ht Hs).
      assert (Hsil : silent s = true -> 0 < i /\ exists c, nth_error (sg (prog0 X0 t)) (pred i) = Some (SD c)).
      { intros Hsl. destruct (sg_silent _ i s (ths_ok t Ht) Hs Hsl) as (_ & _ & _ & _ & _ & _ & (H5 & _ & _ & _ & _ & _ & E1 & _)).
        split; [lia|]. exists SL.RmbC. rewrite <- E1. f_equal. lia. }
      destruct (emits_complete _ t i s Hs Hsil) as (m & o & s0 & k & Hm & Ho & Hk).
      assert (Hn : nth_error (ltrace (prog0 X0 t)) (fo segcalls (sg (prog0 X0 t)) m + o) <> None).
      { rewrite ltrace_sg, (fm_nth segcalls _ m s0 o Hm Ho). apply nth_error_Some, Ho. }
      destruct (nth_error (ltrace (prog0 X0 t)) (fo segcalls (sg (prog0 X0 t)) m + o)) as [c|] eqn:Hc;
        [|contradiction].
      destruct (evt0_spec t _ c Ht Hc) as (Hin & _ & _).
      unfold W1. apply in_flat_map. exists (evt0 X0 t (fo segcalls (sg (prog0 X0 t)) m + o)).
      split; [exact Hin|]. unfold emit0. cbn [lth lix evt0].
      rewrite (loc_fo segcalls _ m s0 o Hm Ho). eapply nth_error_In. exact Hk.
    Qed.

    (** *** Preserved order *)

    Lemma lp_rmb_get s : lpres rc C (LD SL.RmbC) (LT (TL.GetO s)) = true.
    Proof. unfold lpres. cbn [lobj lcat same_lobj orb]. apply SL.dto_rmb_R, HKg. Qed.

    Lemma lp_get_rmb s : lpres rc C (LT (TL.GetO s)) (LD SL.RmbC) = true.
    Proof. unfold lpres. cbn [lobj lcat same_lobj orb]. apply SL.dto_R_rmb, HKg. Qed.

    Lemma lp_rmb_rmb : lpres rc C (LD SL.RmbC) (LD SL.RmbC) = true.
    Proof. destruct rc; reflexivity. Qed.

    Lemma lp_rdx_rmb a : lpres rc C (LD (SL.RdX a)) (LD SL.RmbC) = true.
    Proof. destruct rc; reflexivity. Qed.

    Lemma lp_rdy_rmb b : lpres rc C (LD (SL.RdY b)) (LD SL.RmbC) = true.
    Proof. destruct rc; reflexivity. Qed.

    Section Thread.
      Context (t : nat).
      Hypothesis Ht : In t (ths0 X0).

      Local Abbreviation G := (sg (prog0 X0 t)).
      Local Abbreviation LTr := (ltrace (prog0 X0 t)).

      Lemma low_SD i c : nth_error G i = Some (SD c) -> nth_error LTr (fo segcalls G i) = Some (LD c).
      Proof.
        intros H. rewrite ltrace_sg, <- (Nat.add_0_r (fo segcalls G i)).
        rewrite (fm_nth segcalls G i (SD c) 0 H) by (cbn; lia). reflexivity.
      Qed.

      Lemma low_GT i s : nth_error G i = Some (ST (TL.TGt s)) ->
        nth_error LTr (fo segcalls G i) = Some (LT (TL.GetO s)).
      Proof.
        intros H. rewrite ltrace_sg, <- (Nat.add_0_r (fo segcalls G i)).
        rewrite (fm_nth segcalls G i _ 0 H) by (cbn; lia). reflexivity.
      Qed.

      Lemma rho_SD i c : nth_error G i = Some (SD c) -> rho G i = fo segcalls G i.
      Proof. intros H. unfold rho. rewrite H. reflexivity. Qed.

      Lemma rho_GT i s : nth_error G i = Some (ST (TL.TGt s)) -> rho G i = fo segcalls G i.
      Proof. intros H. unfold rho. rewrite H. cbn. lia. Qed.

      Lemma low_ns i s : nth_error G i = Some s -> silent s = false ->
        nth_error LTr (rho G i) = Some (repc s).
      Proof. intros H Hs. rewrite ltrace_sg. exact (proj1 (rho_ns G i s H Hs)). Qed.

      Lemma rho_ns_lt i i' s : nth_error G i = Some s -> silent s = false -> i < i' ->
        rho G i < fo segcalls G i'.
      Proof.
        intros H Hs Hlt. destruct (proj2 (rho_ns G i s H Hs)) as (o & -> & Ho & _).
        apply (fo_lt segcalls G i i' s o H Ho Hlt).
      Qed.

      Lemma fo_le_rho i s : nth_error G i = Some s -> silent s = false -> fo segcalls G i <= rho G i.
      Proof. intros H Hs. destruct (proj2 (rho_ns G i s H Hs)) as (o & -> & _). lia. Qed.

      Lemma fo_seg_lt i i' s : nth_error G i = Some s -> 0 < length (segcalls s) -> i < i' ->
        fo segcalls G i < fo segcalls G i'.
      Proof. intros H Hl Hlt. pose proof (fo_lt segcalls G i i' s 0 H Hl Hlt). lia. Qed.

      Lemma silent_TT s : silent s = true -> exists s0 r, s = ST (TL.TTt s0 r).
      Proof. destruct s as [[| | |s0 r]|c]; cbn; try discriminate. intros _. eauto. Qed.

      (** The heart of the link: two SeqLock calls of one thread ordered by
          the SeqLock layer's preserved order have their representatives in
          that order in the low-level witness (or share it, ranked). *)
      Lemma core_order i1 i2 s1 s2 :
        nth_error G i1 = Some s1 -> nth_error G i2 = Some s2 -> i1 < i2 ->
        SL.upres rc (TL.tl_cats C) (segsl s1) (segsl s2) = true ->
        P0 X0 t (rho G i1) < P0 X0 t (rho G i2) \/
        (rho G i1 = rho G i2 /\ kappa G i1 < kappa G i2).
      Proof.
        intros H1 H2 Hlt Hu. pose proof (ths_ok t Ht) as Hok.
        destruct (silent s1) eqn:S1, (silent s2) eqn:S2.
        - (* both silent: through their [rmb]s *)
          left.
          destruct (sg_silent _ i1 s1 Hok H1 S1) as (_ & _ & _ & _ & _ & _ & (F1 & _ & _ & _ & _ & _ & E1 & _)).
          destruct (sg_silent _ i2 s2 Hok H2 S2) as (_ & _ & _ & _ & _ & _ & (F2 & _ & _ & _ & _ & _ & E2 & _)).
          rewrite (proj1 (rho_s G i1 s1 H1 S1)), (proj1 (rho_s G i2 s2 H2 S2)).
          replace (pred i1) with (i1 - 1) by lia. replace (pred i2) with (i2 - 1) by lia.
          apply (P0_cross t _ _ _ _ Ht (low_SD _ _ E1) (low_SD _ _ E2)); [|exact lp_rmb_rmb].
          apply (fo_seg_lt _ _ _ E1); cbn; lia.
        - (* a silent [test_ticket] before: through the next [get_ticket] *)
          left. destruct (silent_TT s1 S1) as (s0 & r & ->).
          destruct (sg_silent _ i1 _ Hok H1 S1)
            as (_ & _ & _ & _ & _ & _ & (F1 & L1 & _ & _ & _ & _ & E1 & (s' & ES))).
          rewrite (proj1 (rho_s G i1 _ H1 S1)). replace (pred i1) with (i1 - 1) by lia.
          assert (Ha : P0 X0 t (fo segcalls G (i1 - 1)) < P0 X0 t (fo segcalls G (S i1))).
          { apply (P0_cross t _ _ _ _ Ht (low_SD _ _ E1) (low_GT _ _ ES)); [|apply lp_rmb_get].
            apply (fo_seg_lt _ _ _ E1); cbn; lia. }
          destruct (Nat.eq_dec i2 (S i1)) as [->|Hne].
          + rewrite (rho_GT _ _ ES). exact Ha.
          + eapply Nat.lt_trans; [exact Ha|].
            apply (P0_cross t _ _ _ _ Ht (low_GT _ _ ES) (low_ns _ _ H2 S2)).
            * apply (Nat.lt_le_trans _ (fo segcalls G i2)); [|apply (fo_le_rho _ _ H2 S2)].
              apply (fo_seg_lt _ _ _ ES); cbn; lia.
            * change (LT (TL.GetO s')) with (repc (ST (TL.TGt s'))). rewrite lpres_rep. exact Hu.
        - (* a silent [test_ticket] after: through its iteration *)
          destruct (silent_TT s2 S2) as (s0 & r & ->).
          destruct (sg_silent _ i2 _ Hok H2 S2)
            as (_ & _ & _ & _ & _ & _ & (F2 & _ & (g & E5) & E4 & (a & E3) & (b & E2') & E1 & _)).
          rewrite (proj1 (rho_s G i2 _ H2 S2)), (proj2 (rho_s G i2 _ H2 S2)).
          replace (pred i2) with (i2 - 1) by lia.
          destruct (proj2 (rho_ns G i1 s1 H1 S1)) as (_ & _ & _ & Hk1). rewrite Hk1.
          assert (Hg : P0 X0 t (fo segcalls G (i2 - 5)) < P0 X0 t (fo segcalls G (i2 - 1))).
          { apply (P0_cross t _ _ _ _ Ht (low_GT _ _ E5) (low_SD _ _ E1)); [|apply lp_get_rmb].
            apply (fo_seg_lt _ _ _ E5); cbn; lia. }
          destruct (Nat.lt_trichotomy i1 (i2 - 5)) as [Hl5|[E15|Hg5]].
          + left. eapply Nat.lt_trans; [|exact Hg].
            apply (P0_cross t _ _ _ _ Ht (low_ns _ _ H1 S1) (low_GT _ _ E5)).
            * apply (rho_ns_lt _ _ _ H1 S1 Hl5).
            * change (LT (TL.GetO g)) with (repc (ST (TL.TGt g))). rewrite lpres_rep. exact Hu.
          + left. subst i1. rewrite (rho_GT _ _ E5). exact Hg.
          + assert (Hcase : i1 = i2 - 4 \/ i1 = i2 - 3 \/ i1 = i2 - 2 \/ i1 = i2 - 1) by lia.
            destruct Hcase as [-> | [-> | [-> | ->]]].
            * left. rewrite H1 in E4. injection E4 as ->. rewrite (rho_SD _ _ H1).
              apply (P0_cross t _ _ _ _ Ht (low_SD _ _ H1) (low_SD _ _ E1)); [|exact lp_rmb_rmb].
              apply (fo_seg_lt _ _ _ H1); cbn; lia.
            * left. rewrite H1 in E3. injection E3 as ->. rewrite (rho_SD _ _ H1).
              apply (P0_cross t _ _ _ _ Ht (low_SD _ _ H1) (low_SD _ _ E1)); [|apply lp_rdx_rmb].
              apply (fo_seg_lt _ _ _ H1); cbn; lia.
            * left. rewrite H1 in E2'. injection E2' as ->. rewrite (rho_SD _ _ H1).
              apply (P0_cross t _ _ _ _ Ht (low_SD _ _ H1) (low_SD _ _ E1)); [|apply lp_rdy_rmb].
              apply (fo_seg_lt _ _ _ H1); cbn; lia.
            * right. rewrite H1 in E1. injection E1 as ->. rewrite (rho_SD _ _ H1). split; [reflexivity|lia].
        - (* neither silent: the representatives are ordered as the calls *)
          left. apply (P0_cross t _ _ _ _ Ht (low_ns _ _ H1 S1) (low_ns _ _ H2 S2)).
          + apply (Nat.lt_le_trans _ (fo segcalls G i2)); [apply (rho_ns_lt _ _ _ H1 S1 Hlt)|].
            apply (fo_le_rho _ _ H2 S2).
          + rewrite lpres_rep. exact Hu.
      Qed.
    End Thread.

    Lemma W1_idx e :
      In e (W1 X0) ->
      exists e0, nth_error (wit0 X0) (P0 X0 (SL.th e) (rho (sg (prog0 X0 (SL.th e))) (SL.ix e))) = Some e0 /\
        kappa (sg (prog0 X0 (SL.th e))) (SL.ix e) < length (emit0 X0 e0) /\
        SL.idx e (W1 X0) =
          fo (emit0 X0) (wit0 X0) (P0 X0 (SL.th e) (rho (sg (prog0 X0 (SL.th e))) (SL.ix e)))
          + kappa (sg (prog0 X0 (SL.th e))) (SL.ix e).
    Proof.
      intros He. destruct (W1_elem e He) as (p0 & e0 & k & Hp0 & Hk & _ & _ & _ & Ek & Ep & _).
      rewrite <- Ep, <- Ek. exists e0. split; [exact Hp0|].
      assert (Hl : k < length (emit0 X0 e0)) by (apply nth_error_Some; congruence).
      split; [exact Hl|].
      apply SL.nth_idx; [exact W1_nodup|]. unfold W1. rewrite (fm_nth _ _ _ _ _ Hp0 Hl). exact Hk.
    Qed.

    Lemma W1_pres e1 e2 :
      In e1 (W1 X0) -> In e2 (W1 X0) -> SL.th e1 = SL.th e2 -> SL.ix e1 < SL.ix e2 ->
      SL.upres rc (TL.tl_cats C) (SL.call e1) (SL.call e2) = true ->
      SL.idx e1 (W1 X0) < SL.idx e2 (W1 X0).
    Proof.
      intros He1 He2 Et Hlt Hu.
      destruct (W1_elem e1 He1) as (_ & _ & _ & _ & _ & Ht & _ & _ & _ & _ & s1 & H1 & E1).
      destruct (W1_elem e2 He2) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & s2 & H2 & E2).
      destruct (W1_idx e1 He1) as (e01 & N1 & L1 & I1).
      destruct (W1_idx e2 He2) as (e02 & N2 & L2 & I2).
      rewrite <- Et in H2, N2, L2, I2. rewrite I1, I2.
      rewrite E1, E2 in Hu.
      destruct (core_order (SL.th e1) Ht _ _ _ _ H1 H2 Hlt Hu) as [Hp|[Hr Hk]].
      - pose proof (fo_lt (emit0 X0) (wit0 X0) _ _ _ _ N1 L1 Hp). lia.
      - rewrite Hr. lia.
    Qed.

    (** *** The TicketLock projection is a complete TicketLock execution *)

    Lemma toT_in e :
      In e (TL.wit (XT X0)) ->
      exists e0 c, In e0 (wit0 X0) /\ lcall e0 = LT c /\
        e = TL.mkEv (lth e0) (tix (prog0 X0 (lth e0)) (lix e0)) c.
    Proof.
      intros He. cbn [XT TL.wit] in He. apply in_flat_map in He as (e0 & He0 & Hin).
      unfold toT in Hin. destruct (lcall e0) as [c|c] eqn:Ec; [|destruct Hin].
      destruct Hin as [<-|[]]. exists e0, c. auto.
    Qed.

    Lemma tix_nth t i c :
      nth_error (ltrace (prog0 X0 t)) i = Some (LT c) ->
      nth_error (TL.trace (tprog (prog0 X0 t))) (tix (prog0 X0 t) i) = Some c.
    Proof.
      intros H. rewrite tprog_trace. unfold tix.
      rewrite <- (Nat.add_0_r (fo ltp _ i)), (fm_nth ltp _ i (LT c) 0 H) by (cbn; lia). reflexivity.
    Qed.

    Lemma XT_nodup : NoDup (TL.wit (XT X0)).
    Proof.
      cbn [XT TL.wit]. apply NoDup_fm; [exact (wf0_nodup _ _ _ HW0)| |].
      - intros x _. unfold toT. destruct (lcall x); repeat constructor. intros [].
      - intros x y b Hx Hy Hbx Hby. unfold toT in Hbx, Hby.
        destruct (lcall x) as [c|c] eqn:Ex; [|destruct Hbx].
        destruct (lcall y) as [c'|c'] eqn:Ey; [|destruct Hby].
        destruct Hbx as [<-|[]]. destruct Hby as [E|[]]. injection E as Et Ei Ec. subst c'.
        destruct (wf0_call _ _ _ HW0 x Hx) as [_ Nx]. destruct (wf0_call _ _ _ HW0 y Hy) as [_ Ny].
        rewrite Ex in Nx. rewrite Ey in Ny. rewrite Et in Ny, Ei. unfold tix in Ei.
        destruct (fo_inj ltp _ _ _ 0 _ _ 0 Ny ltac:(cbn; lia) Nx ltac:(cbn; lia) ltac:(lia))
          as [Ei' _].
        rewrite (ev_evt0 x Hx), (ev_evt0 y Hy), Et, Ei'. reflexivity.
    Qed.

    Lemma XT_idx e0 c :
      In e0 (wit0 X0) -> lcall e0 = LT c ->
      TL.idx (TL.mkEv (lth e0) (tix (prog0 X0 (lth e0)) (lix e0)) c) (TL.wit (XT X0)) =
      fo (toT X0) (wit0 X0) (lidx e0 (wit0 X0)).
    Proof.
      intros He Hc. apply TL.nth_idx; [exact XT_nodup|].
      rewrite <- (Nat.add_0_r (fo (toT X0) _ _)). cbn [XT TL.wit].
      rewrite (fm_nth (toT X0) _ _ e0 0 (lidx_nth e0 _ He)) by (unfold toT; rewrite Hc; cbn; lia).
      unfold toT. rewrite Hc. reflexivity.
    Qed.

    Lemma XT_wf : TL.WF rc C (XT X0).
    Proof.
      constructor.
      - exact XT_nodup.
      - exact (wf0_ths _ _ _ HW0).
      - intros e He. destruct (toT_in e He) as (e0 & c & He0 & Hc & ->).
        destruct (wf0_call _ _ _ HW0 e0 He0) as [Ht Hn]. rewrite Hc in Hn.
        split; [exact Ht|]. exact (tix_nth _ _ _ Hn).
      - intros t i Ht Hi. cbn [XT TL.prog TL.ths] in Hi, Ht |- *. rewrite tprog_trace in Hi.
        destruct (nth_error (flat_map ltp (ltrace (prog0 X0 t))) i) as [c|] eqn:Hc;
          [|apply nth_error_None in Hc; lia].
        destruct (fm_inv ltp _ _ _ Hc) as (i0 & x & k & Hx & -> & Hk).
        destruct x as [c'|c']; cbn in Hk; [|destruct k; discriminate].
        destruct k as [|k]; [|destruct k; discriminate]. injection Hk as ->.
        destruct (evt0_spec t i0 (LT c) Ht Hx) as (Hin & Ec & _).
        assert (Ev : TL.evt (XT X0) t (fo ltp (ltrace (prog0 X0 t)) i0 + 0) =
                     TL.mkEv t (tix (prog0 X0 t) i0) c).
        { unfold TL.evt. rewrite Nat.add_0_r. f_equal. apply nth_error_nth. exact (tix_nth _ _ _ Hx). }
        rewrite Ev. apply in_flat_map. exists (evt0 X0 t i0). split; [exact Hin|].
        unfold toT. rewrite Ec. left. reflexivity.
      - intros e1 e2 He1 He2 Et Hlt Hp.
        destruct (toT_in e1 He1) as (x & c & Hx & Hc & ->).
        destruct (toT_in e2 He2) as (y & c' & Hy & Hc' & ->).
        cbn [TL.th TL.ix TL.call] in Et, Hlt, Hp. subst.
        rewrite (XT_idx x c Hx Hc), (XT_idx y c' Hy Hc').
        assert (Hl : lix x < lix y).
        { destruct (Nat.lt_ge_cases (lix x) (lix y)) as [H|H]; [exact H|].
          rewrite Et in Hlt. unfold tix in Hlt. pose proof (fo_mono ltp (ltrace (prog0 X0 (lth y))) _ _ H). lia. }
        assert (Hlx : lidx x (wit0 X0) < lidx y (wit0 X0)).
        { apply (wf0_pres _ _ _ HW0); try assumption. rewrite Hc, Hc'. destruct c, c'; exact Hp. }
        pose proof (fo_lt (toT X0) _ _ _ x 0 (lidx_nth x _ Hx) ltac:(unfold toT; rewrite Hc; cbn; lia) Hlx).
        lia.
      - intros p e Hn.
        assert (He : In e (TL.wit (XT X0))) by (eapply nth_error_In; exact Hn).
        cbn [XT TL.wit] in Hn. destruct (fm_inv (toT X0) _ _ _ Hn) as (p0 & e0 & k & Hp0 & -> & Hk).
        unfold toT in Hk. destruct (lcall e0) as [c|c] eqn:Ec; [|destruct k; discriminate].
        destruct k as [|k]; [|destruct k; discriminate]. injection Hk as <-.
        unfold TL.at_. cbn [XT TL.wit].
        rewrite (fm_firstn (toT X0) _ _ e0 0 Hp0) by lia. rewrite firstn_O, app_nil_r.
        destruct (toT_run X0 (firstn p0 (wit0 X0)) TL.init linit eq_refl eq_refl) as [Ho Hn'].
        pose proof (wf0_valid _ _ _ HW0 p0 e0 Hp0) as V. unfold lpre, at0 in V. rewrite Ec in V.
        unfold TL.pre. cbn [TL.call]. rewrite Ho, Hn'. destruct c; exact V.
      - intros t _. apply tprog_bracketed.
    Qed.

    (** *** The TicketLock calls of [W1] *)

    Lemma W1_tl e :
      In e (W1 X0) -> is_tlc (SL.call e) = true ->
      In (SL.th e) (ths0 X0) /\
      exists kb, nth_error (sg (prog0 X0 (SL.th e))) (SL.ix e) = Some (ST kb) /\ SL.call e = tlcall kb.
    Proof.
      intros He Ht. destruct (W1_elem e He) as (_ & _ & _ & _ & _ & Hth & _ & _ & _ & _ & s' & Hs & Ec).
      split; [exact Hth|].
      rewrite Ec in Ht. destruct (sg_tl _ _ _ Hs Ht) as [kb ->]. exists kb. split; [exact Hs|exact Ec].
    Qed.

    Lemma ovl_tlop e :
      In e (W1 X0) -> is_tlc (SL.call e) = true -> TL.ovl (XT X0) (tlop_of X0 e) = absev e.
    Proof.
      intros He Ht. destruct (W1_tl e He Ht) as (_ & kb & Hs & Ec).
      unfold TL.ovl, tlop_of, absev. cbn [fst]. rewrite (blk_tnum X0 _ _ kb Hs), Ec.
      destruct kb; reflexivity.
    Qed.

    Lemma tlop_all_ops e :
      In e (W1 X0) -> is_tlc (SL.call e) = true -> In (tlop_of X0 e) (TL.all_ops (XT X0)).
    Proof.
      intros He Ht. destruct (W1_tl e He Ht) as (Hth & kb & Hs & _).
      unfold tlop_of. apply (TL.all_ops_of (XT X0) _ _ kb Hth). exact (blk_tnum X0 _ _ kb Hs).
    Qed.

    (** The window of a call-ful TicketLock op in [XT] is its
        representative low-level call. *)
    Lemma lpq_XT t i kb :
      In t (ths0 X0) -> nth_error (sg (prog0 X0 t)) i = Some (ST kb) -> TL.has_call kb = true ->
      TL.lpq (XT X0) (t, tnum (sg (prog0 X0 t)) i) =
      fo (toT X0) (wit0 X0) (P0 X0 t (rho (sg (prog0 X0 t)) i)).
    Proof.
      intros Ht Hi Hc.
      assert (Hns : silent (ST kb) = false) by (cbn; rewrite Hc; reflexivity).
      pose proof (low_ns t i (ST kb) Hi Hns) as Hlow. cbn [repc] in Hlow.
      destruct (evt0_spec t _ _ Ht Hlow) as (Hin & Ec & _).
      assert (Hr : rho (sg (prog0 X0 t)) i = fo segcalls (sg (prog0 X0 t)) i + TL.lpi kb)
        by (unfold rho; rewrite Hi, Hc; reflexivity).
      assert (Hlpi : TL.lpi kb <= length (TL.tcalls kb)).
      { pose proof (wcall_nth kb Hc) as W.
        assert (TL.lpi kb < length (TL.tcalls kb)) by (apply nth_error_Some; congruence). lia. }
      assert (Hn : nth_error (TL.trace (tprog (prog0 X0 t)))
                     (TL.off (tprog (prog0 X0 t)) (tnum (sg (prog0 X0 t)) i) + TL.lpi kb) = Some (wcall kb)).
      { rewrite <- (tix_seg _ i kb _ Hi Hlpi), <- Hr. apply tix_nth. exact Hlow. }
      unfold P0. rewrite <- (XT_idx _ (wcall kb) Hin Ec). cbn [lth lix evt0].
      unfold TL.lpq, TL.lpc, TL.lpi_of. rewrite (blk_tnum X0 t i kb Hi). cbn [fst snd XT TL.prog].
      rewrite Hr, (tix_seg _ i kb _ Hi Hlpi).
      unfold TL.evt. cbn [XT TL.prog]. rewrite (nth_error_nth _ _ _ Hn). reflexivity.
    Qed.

    Lemma tl_pos x :
      In x (W1 X0) -> is_tlc (SL.call x) = true -> TL.callful (XT X0) (tlop_of X0 x) = true ->
      exists px e0, SL.idx x (W1 X0) = fo (emit0 X0) (wit0 X0) px /\
        TL.lpq (XT X0) (tlop_of X0 x) = fo (toT X0) (wit0 X0) px /\
        nth_error (wit0 X0) px = Some e0 /\ length (toT X0 e0) = 1.
    Proof.
      intros Hx Ht Hcf. destruct (W1_tl x Hx Ht) as (Hth & kb & Hs & _).
      assert (Hc : TL.has_call kb = true).
      { unfold TL.callful, tlop_of in Hcf. rewrite (blk_tnum X0 _ _ kb Hs) in Hcf. exact Hcf. }
      assert (Hns : silent (ST kb) = false) by (cbn; rewrite Hc; reflexivity).
      pose proof (low_ns _ _ (ST kb) Hs Hns) as Hlow. cbn [repc] in Hlow.
      destruct (evt0_spec _ _ _ Hth Hlow) as (_ & Ec & N).
      exists (P0 X0 (SL.th x) (rho (sg (prog0 X0 (SL.th x))) (SL.ix x))), (evt0 X0 (SL.th x) (rho (sg (prog0 X0 (SL.th x))) (SL.ix x))).
      split; [|split; [apply (lpq_XT _ _ kb Hth Hs Hc)|split; [exact N|unfold toT; rewrite Ec; reflexivity]]].
      destruct (W1_idx x Hx) as (_ & _ & _ & ->).
      destruct (proj2 (rho_ns _ _ _ Hs Hns)) as (_ & _ & _ & ->). lia.
    Qed.

    (** The TicketLock calls of [W1], in order, are a placement of the
        silent [test_ticket]s into the TicketLock linearization. *)
    Lemma W1_tl_ok : TL.tl_ok (0, None) (map absev (filter (fun e => is_tlc (SL.call e)) (W1 X0))).
    Proof.
      set (Lw := filter (fun e => is_tlc (SL.call e)) (W1 X0)).
      assert (HLw : forall e, In e Lw -> In e (W1 X0) /\ is_tlc (SL.call e) = true)
        by (intros e He; apply filter_In in He; exact He).
      assert (Hov : map (TL.ovl (XT X0)) (map (tlop_of X0) Lw) = map absev Lw).
      { rewrite map_map. apply map_ext_in. intros e He. destruct (HLw e He). apply ovl_tlop; assumption. }
      rewrite <- Hov. apply (TL.ticketlock_S1_any_placement rc C (XT X0) XT_wf).
      { intros q Hq. apply in_map_iff in Hq as (e & <- & He). destruct (HLw e He) as [He1 Ht].
        apply tlop_all_ops; assumption. }
      apply (WC.ss_perm_eq (TL.lpq (XT X0))).
      - rewrite filter_map_swap. unfold Lw. rewrite filter_filter'.
        apply ss_of_nth. intros p p' x y Hlt Hx Hy Gx Gy.
        apply andb_true_iff in Gx as [Tx Cx]. apply andb_true_iff in Gy as [Ty Cy].
        assert (Inx : In x (W1 X0)) by (eapply nth_error_In; exact Hx).
        assert (Iny : In y (W1 X0)) by (eapply nth_error_In; exact Hy).
        destruct (tl_pos x Inx Tx Cx) as (px & e0 & Ix & Lx & Nx & Lex).
        destruct (tl_pos y Iny Ty Cy) as (py & e0' & Iy & Ly & Ny & Ley).
        rewrite (SL.nth_idx _ _ _ W1_nodup Hx) in Ix. rewrite (SL.nth_idx _ _ _ W1_nodup Hy) in Iy.
        rewrite Lx, Ly.
        assert (Hp : px < py).
        { destruct (Nat.lt_ge_cases px py) as [H|H]; [exact H|].
          pose proof (fo_mono (emit0 X0) (wit0 X0) _ _ H). lia. }
        pose proof (fo_lt (toT X0) _ _ _ e0 0 Nx ltac:(lia) Hp). lia.
      - apply WC.isort_sorted; [exact (TL.lp_inj rc C (XT X0) XT_wf)|].
        exact (TL.callful_ops_nodup (XT X0) (wf0_ths _ _ _ HW0)).
      - apply NoDup_Permutation.
        + apply NoDup_filter, NoDup_map_in; [apply NoDup_filter, W1_nodup|].
          intros x y Hx Hy E. destruct (HLw x Hx) as [Inx Tx]. destruct (HLw y Hy) as [Iny Ty].
          destruct (W1_tl x Inx Tx) as (_ & kb & Hs & Ec). destruct (W1_tl y Iny Ty) as (_ & kb' & Hs' & Ec').
          unfold tlop_of in E. injection E as Et Ei. rewrite Et in Hs, Ei. unfold tnum in Ei.
          destruct (fo_inj segtl _ _ _ 0 _ _ 0 Hs ltac:(cbn; lia) Hs' ltac:(cbn; lia) ltac:(lia)) as [Ei' _].
          rewrite Ei' in Hs. rewrite Hs in Hs'. injection Hs' as <-.
          destruct x as [tx ix cx], y as [ty iy cy]. cbn in *. subst. reflexivity.
        + apply (Permutation_NoDup (Permutation_sym (WC.isort_perm _ _))).
          exact (TL.callful_ops_nodup (XT X0) (wf0_ths _ _ _ HW0)).
        + intros q. split; intros Hq.
          * apply (Permutation_in _ (Permutation_sym (WC.isort_perm _ _))).
            apply filter_In in Hq as [Hq Hc]. unfold TL.callful_ops. apply filter_In. split; [|exact Hc].
            apply in_map_iff in Hq as (e & <- & He). destruct (HLw e He). apply tlop_all_ops; assumption.
          * apply (Permutation_in _ (WC.isort_perm _ _)) in Hq.
            apply TL.callful_ops_In in Hq as [Hq (kb & Hb & Hc)].
            destruct q as [t n]. apply TL.all_ops_In in Hq as [Ht _]. cbn [fst XT TL.ths] in Ht.
            unfold TL.blk in Hb. cbn [fst snd XT TL.prog] in Hb. rewrite tprog_sg in Hb.
            destruct (fm_inv segtl _ _ _ Hb) as (i & s0 & k & Hi & -> & Hk).
            destruct s0 as [kb'|c]; cbn in Hk; [|destruct k; discriminate].
            destruct k as [|k]; [|destruct k; discriminate]. injection Hk as ->.
            assert (Hin : In (SL.evt (X1 X0) t i) (W1 X0)).
            { apply W1_complete; [exact Ht|]. rewrite X1_trace, length_map by exact Ht.
              apply nth_error_Some. congruence. }
            rewrite (X1_evt t i _ Ht Hi) in Hin.
            apply filter_In. split.
            -- apply in_map_iff. exists (SL.mkEv t i (segsl (ST kb))). split.
               ++ unfold tlop_of, tnum. cbn [SL.th SL.ix]. f_equal. lia.
               ++ apply filter_In. split; [exact Hin|apply tlcall_tl].
            -- unfold TL.callful. cbn [fst snd]. replace (fo segtl (sg (prog0 X0 t)) i + 0)
                 with (tnum (sg (prog0 X0 t)) i) by (unfold tnum; lia).
               rewrite (blk_tnum X0 t i kb Hi). exact Hc.
    Qed.

    (** *** Validity *)

    Lemma W1_dsim l s s0 :
      (forall x, In x l -> In x (wit0 X0)) -> dsim s s0 ->
      dsim (SL.run s (flat_map (emit0 X0) l)) (lrun s0 l).
    Proof.
      revert s s0. induction l as [|x l IH]; intros s s0 Hl Hd; [exact Hd|].
      cbn [flat_map lrun]. rewrite SL.run_app. apply IH; [intros y Hy; apply Hl; right; exact Hy|].
      assert (Hx : In x (wit0 X0)) by (apply Hl; left; reflexivity).
      destruct (emit0_loc x Hx) as (m & o & sgm & Hm & Ho & _ & Hc & Ee). rewrite Ee.
      unfold emits. rewrite Hm. destruct sgm as [kb|c].
      - cbn [segcalls] in Hc. rewrite nth_error_map in Hc.
        destruct (nth_error (TL.tcalls kb) o) as [c|] eqn:Hco; [|discriminate]. injection Hc as Hc.
        apply (dsim_lpost_LT _ _ x c (eq_sym Hc)).
        apply dsim_run_tl; [|exact Hd].
        destruct (Nat.eqb o (TL.lpi kb)); repeat constructor. apply tlcall_tl.
      - cbn [segcalls] in Hc. destruct o as [|o]; [|destruct o; discriminate]. injection Hc as Hc.
        cbn [SL.run]. apply dsim_run_tl.
        + destruct (nth_error _ (S m)) as [[kb'|c']|]; [destruct (TL.has_call kb')| |];
            repeat constructor. apply tlcall_tl.
        + apply (dsim_post_LD _ _ (SL.mkEv (lth x) m c) x c (eq_sym Hc) eq_refl Hd).
    Qed.

    Lemma W1_valid p e : nth_error (W1 X0) p = Some e -> SL.pre (SL.at_ (X1 X0) p) e = true.
    Proof.
      intros Hp. unfold SL.at_. cbn [X1 SL.wit].
      destruct (is_tlc (SL.call e)) eqn:Ht.
      - exact (tl_valid (W1 X0) SL.init W1_tl_ok p e Hp Ht).
      - assert (He : In e (W1 X0)) by (eapply nth_error_In; exact Hp).
        destruct (W1_elem e He) as (p0 & e0 & k & Hp0 & Hk & Hth & Et & Ei & Ek & Ep & s' & Hs & Ec).
        destruct s' as [kb|c]; [exfalso; rewrite Ec in Ht; cbn [segsl] in Ht; rewrite tlcall_tl in Ht; discriminate|].
        assert (Hpos : p = fo (emit0 X0) (wit0 X0) p0).
        { rewrite <- (SL.nth_idx _ _ _ W1_nodup Hp). destruct (W1_idx e He) as (_ & _ & _ & ->).
          rewrite <- Ep, (kappa_SD _ _ _ Hs). lia. }
        rewrite Hpos. unfold W1. rewrite fm_firstn0.
        assert (Hd : dsim (SL.run SL.init (flat_map (emit0 X0) (firstn p0 (wit0 X0))))
                          (lrun linit (firstn p0 (wit0 X0)))).
        { apply W1_dsim; [|split; [reflexivity|split; reflexivity]].
          intros x Hx. rewrite <- (firstn_skipn p0 (wit0 X0)). apply in_or_app. left. exact Hx. }
        assert (Hc0 : lcall e0 = LD c).
        { destruct (wf0_call _ _ _ HW0 e0 (nth_error_In _ _ Hp0)) as [_ N].
          rewrite Et, Ei, (rho_SD _ _ _ Hs), (low_SD _ _ _ Hs) in N. congruence. }
        pose proof (wf0_valid _ _ _ HW0 p0 e0 Hp0) as V. unfold lpre, at0 in V. rewrite Hc0 in V.
        destruct Hd as (Dx & Dy & Dz).
        unfold SL.pre. rewrite Ec in Ht |- *. cbn [segsl] in Ht |- *.
        destruct c; cbn in Ht; try discriminate; try reflexivity.
        + rewrite Dx. exact V.
        + rewrite Dy. exact V.
        + rewrite Dz. exact V.
    Qed.

    Theorem X1_wf : SL.WF rc (TL.tl_cats C) (X1 X0).
    Proof.
      constructor.
      - exact W1_nodup.
      - exact (wf0_ths _ _ _ HW0).
      - exact W1_call.
      - exact W1_complete.
      - exact W1_pres.
      - exact W1_valid.
    Qed.

    (** *** Witness order of operations *)

    Lemma rho_block t j k i :
      In t (ths0 X0) -> nth_error (prog0 X0 t) j = Some k -> i < length (segs k) ->
      exists i', i' < length (lcalls k) /\
        rho (sg (prog0 X0 t)) (fo segs (prog0 X0 t) j + i) = loff (prog0 X0 t) j + i'.
    Proof.
      intros Ht Hj Hi.
      assert (Hk : blk_ok k = true).
      { pose proof (ths_ok t Ht) as Hok. rewrite forallb_forall in Hok. apply Hok. eapply nth_error_In. exact Hj. }
      destruct (nth_error (segs k) i) as [s|] eqn:Hs; [|apply nth_error_None in Hs; lia].
      pose proof (fm_nth segs _ _ _ _ Hj Hi) as Hm. rewrite Hs in Hm. fold (sg (prog0 X0 t)) in Hm.
      assert (Hlen : length (lcalls k) = length (flat_map segcalls (segs k))) by (rewrite lcalls_segs; reflexivity).
      rewrite loff_fo.
      destruct (silent s) eqn:Hsl.
      - destruct (blk_silent k i s Hk Hs Hsl) as (H5 & _ & _ & _ & _ & _ & E1 & _).
        rewrite (proj1 (rho_s _ _ _ Hm Hsl)).
        replace (pred (fo segs (prog0 X0 t) j + i)) with (fo segs (prog0 X0 t) j + (i - 1)) by lia.
        rewrite (fo_nested _ j k (i - 1) Hj) by lia.
        exists (fo segcalls (segs k) (i - 1)). split; [|reflexivity].
        pose proof (fo_lt segcalls (segs k) (i - 1) i _ 0 E1 ltac:(cbn; lia) ltac:(lia)).
        pose proof (fo_le_len segcalls (segs k) i). lia.
      - destruct (proj2 (rho_ns _ _ _ Hm Hsl)) as (o & -> & Ho & _).
        rewrite (fo_nested _ j k i Hj) by lia.
        exists (fo segcalls (segs k) i + o). split; [|lia].
        pose proof (fo_S segcalls (segs k) i s Hs). pose proof (fo_le_len segcalls (segs k) (S i)). lia.
    Qed.

    Lemma X1_Pq t j k i :
      In t (ths0 X0) -> nth_error (prog0 X0 t) j = Some k -> i < length (SL.calls (abs k)) ->
      exists i' e0 kp, i' < length (lcalls k) /\ nth_error (wit0 X0) (Pq0 X0 (t, j) i') = Some e0 /\
        kp < length (emit0 X0 e0) /\
        SL.Pq (X1 X0) (t, j) i = fo (emit0 X0) (wit0 X0) (Pq0 X0 (t, j) i') + kp.
    Proof.
      intros Ht Hj Hi.
      assert (Hk : blk_ok k = true).
      { pose proof (ths_ok t Ht) as Hok. rewrite forallb_forall in Hok. apply Hok. eapply nth_error_In. exact Hj. }
      rewrite calls_abs, length_map in Hi by exact Hk.
      destruct (rho_block t j k i Ht Hj Hi) as (i' & Hi' & Hr).
      assert (Hin : In (SL.evt (X1 X0) t (fo segs (prog0 X0 t) j + i)) (W1 X0)).
      { apply W1_complete; [exact Ht|]. rewrite X1_trace, length_map by exact Ht.
        apply nth_error_Some. unfold sg. rewrite (fm_nth segs _ _ _ _ Hj Hi).
        apply nth_error_Some, Hi. }
      destruct (W1_idx _ Hin) as (e0 & N & L & I). cbn [SL.evt SL.th SL.ix] in N, L, I.
      rewrite Hr in N, I. exists i', e0, (kappa (sg (prog0 X0 t)) (fo segs (prog0 X0 t) j + i)).
      split; [exact Hi'|]. split; [exact N|]. split; [exact L|].
      unfold SL.Pq, SL.P. cbn [fst snd X1 SL.prog SL.wit]. rewrite off_abs by exact (ths_ok t Ht). exact I.
    Qed.

    Lemma X1_rt q q' :
      In q (SL.all_ops (X1 X0)) -> In q' (SL.all_ops (X1 X0)) -> rt0 X0 q q' -> rt1 (X1 X0) q q'.
    Proof.
      intros Hq Hq' Hrt k k' i i' Hk Hk' Hi Hi'.
      destruct q as [t j], q' as [t' j'].
      apply SL.all_ops_In in Hq, Hq'. cbn [fst snd X1 SL.ths] in Hq, Hq'. destruct Hq as [Ht _], Hq' as [Ht' _].
      unfold SL.blk in Hk, Hk'. cbn [SL.prog X1 fst snd] in Hk, Hk'. rewrite nth_error_map in Hk, Hk'.
      destruct (nth_error (prog0 X0 t) j) as [k0|] eqn:Hj; [|discriminate]. injection Hk as <-.
      destruct (nth_error (prog0 X0 t') j') as [k0'|] eqn:Hj'; [|discriminate]. injection Hk' as <-.
      destruct (X1_Pq t j k0 i Ht Hj Hi) as (n & e0 & kp & Hn & N & L & ->).
      destruct (X1_Pq t' j' k0' i' Ht' Hj' Hi') as (n' & e0' & kp' & Hn' & N' & L' & ->).
      assert (H : Pq0 X0 (t, j) n < Pq0 X0 (t', j') n') by (apply (Hrt k0 k0'); assumption).
      pose proof (fo_lt (emit0 X0) _ _ _ _ _ N L H). lia.
    Qed.
  End Link.

  (** ** The vertical link *)

  (** Every complete low-level execution of the SeqLock with the
      TicketLock inlined gives a complete SeqLock-layer execution (the
      TicketLock atomic, with its abstract specification) with the same
      threads, the abstracted programs, and a witness that keeps the
      witness order of operations of the low level ([rt0] to [rt1]). *)
  Theorem tower_link rc C X0 :
    SL.K_ok (TL.tl_cats C) = true -> WF0 rc C X0 ->
    exists X : SL.Exec,
      SL.WF rc (TL.tl_cats C) X /\
      SL.ths X = ths0 X0 /\
      (forall t, SL.prog X t = map abs (prog0 X0 t)) /\
      (forall q q', In q (SL.all_ops X) -> In q' (SL.all_ops X) -> rt0 X0 q q' -> rt1 X q q').
  Proof.
    intros HK HW0. exists (X1 X0).
    split; [exact (X1_wf rc C X0 HW0 HK)|].
    split; [reflexivity|]. split; [reflexivity|].
    exact (X1_rt rc C X0 HW0).
  Qed.

  (** The overlay operations of the two executions are the same. *)
  Lemma abs_all_ops X X0 :
    SL.ths X = ths0 X0 -> (forall t, SL.prog X t = map abs (prog0 X0 t)) -> SL.all_ops X = all_ops0 X0.
  Proof.
    intros Et Ep. unfold SL.all_ops, all_ops0. rewrite Et. apply flat_map_ext. intros t.
    rewrite Ep, length_map. reflexivity.
  Qed.

  Lemma abs_ovl X X0 q : (forall t, SL.prog X t = map abs (prog0 X0 t)) -> SL.ovl X q = ovl0 X0 q.
  Proof.
    intros Ep. unfold SL.ovl, SL.blk, ovl0, blk0. rewrite Ep, nth_error_map.
    destruct (nth_error (prog0 X0 (fst q)) (snd q)) as [[]|]; reflexivity.
  Qed.

  (** Hence the composition theorem of the SeqLock layer applies to the
      low-level execution: SeqLock ⊗ COH[z], with read ↦ rmb and write ↦
      wmb, is relaxed linearizable on it, every pair of operations in
      low-level witness order ([rt0]) being kept.  For real time, see
      [tower_composition_rt]. *)
  Corollary tower_composition rc C X0 :
    SL.K_ok (TL.tl_cats C) = true -> WF0 rc C X0 ->
    exists X : SL.Exec,
      SL.ths X = ths0 X0 /\ (forall t, SL.prog X t = map abs (prog0 X0 t)) /\
      SL.all_ops X = all_ops0 X0 /\ (forall q, SL.ovl X q = ovl0 X0 q) /\
      (forall q q', In q (all_ops0 X0) -> In q' (all_ops0 X0) -> rt0 X0 q q' ->
         WT.rt (SL.setting SL.sl_cf rc (TL.tl_cats C) X) q q') /\
      WT.Conclusion (dtable rc) (SL.setting SL.sl_cf rc (TL.tl_cats C) X).
  Proof.
    intros HK HW0. destruct (tower_link rc C X0 HK HW0) as (X & HW & Et & Ep & Hrt).
    pose proof (abs_all_ops X X0 Et Ep) as Eo.
    exists X. split; [exact Et|]. split; [exact Ep|]. split; [exact Eo|].
    split; [intros q; apply abs_ovl, Ep|]. split.
    - intros q q' Hq Hq'. rewrite <- Eo in Hq, Hq'. exact (Hrt q q' Hq Hq').
    - exact (SL.seqlock_z_composition rc (TL.tl_cats C) X HW HK).
  Qed.

  (** With the plain counter, the categories are [plainTL]. *)
  Corollary tower_composition_plain rc X0 :
    WF0 rc TL.plainC X0 ->
    exists X : SL.Exec,
      SL.ths X = ths0 X0 /\ (forall t, SL.prog X t = map abs (prog0 X0 t)) /\
      SL.all_ops X = all_ops0 X0 /\ (forall q, SL.ovl X q = ovl0 X0 q) /\
      (forall q q', In q (all_ops0 X0) -> In q' (all_ops0 X0) -> rt0 X0 q q' ->
         WT.rt (SL.setting SL.sl_cf rc SL.plainTL X) q q') /\
      WT.Conclusion (dtable rc) (SL.setting SL.sl_cf rc SL.plainTL X).
  Proof. rewrite <- TL.exports_plainTL. apply tower_composition. reflexivity. Qed.

  (** An RC counter works as well. *)
  Corollary tower_composition_rc rc X0 :
    WF0 rc TL.rcC X0 ->
    exists X : SL.Exec,
      SL.ths X = ths0 X0 /\ (forall t, SL.prog X t = map abs (prog0 X0 t)) /\
      WT.Conclusion (dtable rc) (SL.setting SL.sl_cf rc (TL.tl_cats TL.rcC) X).
  Proof.
    intros HW0. destruct (tower_composition rc TL.rcC X0 TL.exports_rc_ok HW0)
      as (X & Et & Ep & _ & _ & _ & Hc).
    exists X. auto.
  Qed.

  (** ** Real time *)

  (** The [i]-th low-level call of block [j] of thread [t]. *)
  Definition ce0 (X0 : Exec0) (t j i : nat) : LEv := evt0 X0 t (loff (prog0 X0 t) j + i).

  (** Invocation and response times of low-level operations and calls
      ([None]: no response yet), as [SeqLockRT.Timing]. *)
  Record Timing0 : Type := {
    oinv0 : nat * nat -> nat;
    ores0 : nat * nat -> option nat;
    cinv0 : LEv -> nat;
    cres0 : LEv -> option nat;
  }.

  (** The links between them, as [SeqLockRT.RT_ok]. *)
  Record RT_ok0 (X0 : Exec0) (T : Timing0) : Prop := {
    (** a call is issued after its operation is invoked *)
    rt0_inv : forall q k i, blk0 X0 q = Some k -> i < length (lcalls k) ->
                In (ce0 X0 (fst q) (snd q) i) (wit0 X0) ->
                oinv0 T q <= cinv0 T (ce0 X0 (fst q) (snd q) i);
    (** an operation responds after all its issued calls have responded *)
    rt0_res : forall q k i r, blk0 X0 q = Some k -> i < length (lcalls k) ->
                In (ce0 X0 (fst q) (snd q) i) (wit0 X0) -> ores0 T q = Some r ->
                exists r', cres0 T (ce0 X0 (fst q) (snd q) i) = Some r' /\ r' <= r;
    (** a call responds after its invocation *)
    rt0_call : forall e r, In e (wit0 X0) -> cres0 T e = Some r -> cinv0 T e <= r;
    (** the witness extends the real-time order of low-level calls *)
    rt0_wit : forall e e' r, In e (wit0 X0) -> In e' (wit0 X0) -> cres0 T e = Some r ->
                r < cinv0 T e' -> lidx e (wit0 X0) < lidx e' (wit0 X0);
  }.

  (** The standard real-time order of low-level operations. *)
  Definition rt_of0 (T : Timing0) (q q' : nat * nat) : Prop :=
    exists r, ores0 T q = Some r /\ r < oinv0 T q'.

  Lemma all_ops0_ths X0 q : In q (all_ops0 X0) -> In (fst q) (ths0 X0).
  Proof.
    unfold all_ops0. intros H. apply in_flat_map in H as (t & Ht & Hin).
    apply in_map_iff in Hin as (j & <- & _). exact Ht.
  Qed.

  (** Real time implies the witness order of operations. *)
  Lemma rt_of0_rt0 rc C X0 T q q' :
    WF0 rc C X0 -> RT_ok0 X0 T -> In q (all_ops0 X0) -> In q' (all_ops0 X0) ->
    rt_of0 T q q' -> rt0 X0 q q'.
  Proof.
    intros HW0 HT Hq Hq' (r & Hr & Hlt) k k' i i' Hk Hk' Hi Hi'.
    assert (Hce : forall q k i, In q (all_ops0 X0) -> blk0 X0 q = Some k -> i < length (lcalls k) ->
                    In (ce0 X0 (fst q) (snd q) i) (wit0 X0)).
    { intros q0 k0 i0 Hq0 Hk0 Hi0. apply (wf0_complete _ _ _ HW0 _ _ (all_ops0_ths X0 q0 Hq0)).
      unfold blk0 in Hk0. apply nth_error_Some.
      change (loff (prog0 X0 (fst q0)) (snd q0)) with (fo lcalls (prog0 X0 (fst q0)) (snd q0)).
      unfold ltrace. rewrite (fm_nth lcalls _ _ _ _ Hk0 Hi0). apply nth_error_Some, Hi0. }
    pose proof (Hce q k i Hq Hk Hi) as Hin. pose proof (Hce q' k' i' Hq' Hk' Hi') as Hin'.
    destruct (rt0_res _ _ HT q k i r Hk Hi Hin Hr) as (r' & Hr' & Hle).
    pose proof (rt0_inv _ _ HT q' k' i' Hk' Hi' Hin') as Hinv.
    exact (rt0_wit _ _ HT _ _ r' Hin Hin' Hr' ltac:(lia)).
  Qed.

  (** [RT_ok0] is satisfiable on every execution: each call is the point
      interval [[2p, 2p+1]] at its witness position [p], each operation
      spans from its first to its last call (as [SeqLockRT.canon]). *)
  Definition ncalls0 (X0 : Exec0) (q : nat * nat) : nat :=
    match blk0 X0 q with Some k => length (lcalls k) | None => 0 end.

  Definition cpos0 (X0 : Exec0) (q : nat * nat) : list nat :=
    map (fun i => lidx (ce0 X0 (fst q) (snd q) i) (wit0 X0)) (seq 0 (ncalls0 X0 q)).

  Definition canon0 (X0 : Exec0) : Timing0 := {|
    oinv0 := fun q => 2 * fold_right Nat.min (length (wit0 X0)) (cpos0 X0 q);
    ores0 := fun q => Some (S (2 * list_max (cpos0 X0 q)));
    cinv0 := fun e => 2 * lidx e (wit0 X0);
    cres0 := fun e => Some (S (2 * lidx e (wit0 X0)));
  |}.

  Lemma fold_min_le d l x : In x l -> fold_right Nat.min d l <= x.
  Proof.
    induction l as [|y l IH]; cbn; [contradiction|].
    intros [->|H]; [lia|]. specialize (IH H). lia.
  Qed.

  Lemma le_list_max x l : In x l -> x <= list_max l.
  Proof.
    intros H. assert (Hf : Forall (fun k => k <= list_max l) l) by (apply list_max_le; lia).
    rewrite Forall_forall in Hf. exact (Hf x H).
  Qed.

  Lemma cpos0_In X0 q k i : blk0 X0 q = Some k -> i < length (lcalls k) ->
    In (lidx (ce0 X0 (fst q) (snd q) i) (wit0 X0)) (cpos0 X0 q).
  Proof.
    intros Hb Hi. unfold cpos0, ncalls0. rewrite Hb. apply in_map_iff. exists i.
    split; [reflexivity|]. apply in_seq. lia.
  Qed.

  Lemma canon0_ok X0 : RT_ok0 X0 (canon0 X0).
  Proof.
    constructor; cbn [oinv0 ores0 cinv0 cres0 canon0].
    - intros q k i Hb Hi _. pose proof (fold_min_le (length (wit0 X0)) _ _ (cpos0_In X0 q k i Hb Hi)). lia.
    - intros q k i r Hb Hi _ Hr. injection Hr as <-. eexists. split; [reflexivity|].
      pose proof (le_list_max _ _ (cpos0_In X0 q k i Hb Hi)). lia.
    - intros e r _ Hr. injection Hr as <-. lia.
    - intros e e' r _ _ Hr Hlt. injection Hr as <-. lia.
  Qed.

  (** [SeqLockCOH.setting] with the real-time order of a low-level timing. *)
  Definition setting_rt0 (cf : SL.Blk -> DCat) (rc : bool) (K : SL.TLCats) (X : SL.Exec) (T : Timing0)
    : WT.Setting DCat := {|
    WT.Op := nat * nat;
    WT.Call := SL.Ev;
    WT.OvOp := SL.OvEv;
    WT.Comp := SL.CompT;
    WT.comp_dec := SL.comp_dec;
    WT.comp := fun q => if SL.is_sl_op X q then SL.CSL else SL.CZ;
    WT.ovl := SL.ovl X;
    WT.cF := fun q => match SL.blk X q with Some k => cf k | None => DLocal end;
    WT.IFc := fun _ _ => False;
    WT.ucomp := fun e => match SL.uobj (SL.call e) with SL.OZ => SL.CZ | _ => SL.CSL end;
    WT.cE := fun e => SL.ucat K (SL.call e);
    WT.IEc := fun u u' => SL.upres rc K (SL.call u) (SL.call u') = false;
    WT.lo := SL.lpc X;
    WT.hi := SL.lpc X;
    WT.lpc := SL.lpc X;
    WT.pos := fun e => SL.idx e (SL.wit X);
    WT.ops := SL.all_ops X;
    WT.po := fun q q' => fst q = fst q' /\ snd q < snd q';
    WT.rt := rt_of0 T;
    WT.nuF := fun c => match c with SL.CSL => SL.nu_sl | SL.CZ => SL.nu_z end;
  |}.

  (** A [Conclusion] for the witness order [rt1] is one for any real-time
      order contained in it. *)
  Lemma conclusion_rt0 cf rc K X T :
    (forall q q', In q (SL.all_ops X) -> In q' (SL.all_ops X) -> rt_of0 T q q' -> rt1 X q q') ->
    WT.Conclusion (dtable rc) (SL.setting cf rc K X) ->
    WT.Conclusion (dtable rc) (setting_rt0 cf rc K X T).
  Proof.
    intros Hrt (ow & Hp & Hord & Hspec). exists ow. split; [exact Hp|]. split; [|exact Hspec].
    intros q q' Hq Hq' [Hpo|Hr].
    - apply Hord; [exact Hq|exact Hq'|left; exact Hpo].
    - apply Hord; [exact Hq|exact Hq'|right; exact (Hrt q q' Hq Hq' Hr)].
  Qed.

  (** The real-time statement: every complete low-level execution with a
      timing has a linearization of SeqLock ⊗ COH[z] (read ↦ rmb, write ↦
      wmb) on its abstraction that respects the real-time order of the
      low-level execution. *)
  Corollary tower_composition_rt rc C X0 T :
    SL.K_ok (TL.tl_cats C) = true -> WF0 rc C X0 -> RT_ok0 X0 T ->
    exists X : SL.Exec,
      SL.ths X = ths0 X0 /\ (forall t, SL.prog X t = map abs (prog0 X0 t)) /\
      SL.all_ops X = all_ops0 X0 /\ (forall q, SL.ovl X q = ovl0 X0 q) /\
      WT.Conclusion (dtable rc) (setting_rt0 SL.sl_cf rc (TL.tl_cats C) X T).
  Proof.
    intros HK HW0 HT. destruct (tower_link rc C X0 HK HW0) as (X & HW & Et & Ep & Hrt).
    pose proof (abs_all_ops X X0 Et Ep) as Eo.
    exists X. split; [exact Et|]. split; [exact Ep|]. split; [exact Eo|].
    split; [intros q; apply abs_ovl, Ep|].
    apply conclusion_rt0; [|exact (SL.seqlock_z_composition rc (TL.tl_cats C) X HW HK)].
    intros q q' Hq Hq' Hr. apply Hrt; [exact Hq|exact Hq'|].
    rewrite Eo in Hq, Hq'. exact (rt_of0_rt0 rc C X0 T q q' HW0 HT Hq Hq' Hr).
  Qed.

  Corollary tower_composition_rt_plain rc X0 T :
    WF0 rc TL.plainC X0 -> RT_ok0 X0 T ->
    exists X : SL.Exec,
      SL.ths X = ths0 X0 /\ (forall t, SL.prog X t = map abs (prog0 X0 t)) /\
      SL.all_ops X = all_ops0 X0 /\ (forall q, SL.ovl X q = ovl0 X0 q) /\
      WT.Conclusion (dtable rc) (setting_rt0 SL.sl_cf rc SL.plainTL X T).
  Proof. rewrite <- TL.exports_plainTL. apply tower_composition_rt. reflexivity. Qed.

  (** ** Non-vacuity: a concrete low-level execution with a silent [test_ticket] *)

  Definition LEv_eqb (a b : LEv) : bool := if LEv_eq_dec a b then true else false.

  Lemma LEv_eqb_eq a b : LEv_eqb a b = true -> a = b.
  Proof. unfold LEv_eqb. destruct (LEv_eq_dec a b); congruence. Qed.

  Definition optLC_eqb (a b : option LC) : bool :=
    match a, b with
    | Some x, Some y => if LC_eq_dec x y then true else false
    | None, None => true
    | _, _ => false
    end.

  Definition wfb0 (rc : bool) (C : TL.CCats) (X0 : Exec0) : bool :=
    SL.nodupb LEv_eqb (wit0 X0) && SL.nodupb Nat.eqb (ths0 X0)
    && forallb (fun e => existsb (Nat.eqb (lth e)) (ths0 X0)
                         && optLC_eqb (nth_error (ltrace (prog0 X0 (lth e))) (lix e)) (Some (lcall e)))
               (wit0 X0)
    && forallb (fun t => forallb (fun i => existsb (LEv_eqb (evt0 X0 t i)) (wit0 X0))
                                 (seq 0 (length (ltrace (prog0 X0 t))))) (ths0 X0)
    && forallb (fun e1 => forallb (fun e2 =>
          implb (Nat.eqb (lth e1) (lth e2) && Nat.ltb (lix e1) (lix e2) && lpres rc C (lcall e1) (lcall e2))
                (Nat.ltb (lidx e1 (wit0 X0)) (lidx e2 (wit0 X0)))) (wit0 X0)) (wit0 X0)
    && forallb (fun p => match nth_error (wit0 X0) p with Some e => lpre (at0 X0 p) e | None => true end)
               (seq 0 (length (wit0 X0)))
    && forallb (fun t => forallb blk_ok (prog0 X0 t)) (ths0 X0).

  Lemma wfb0_sound rc C X0 : wfb0 rc C X0 = true -> WF0 rc C X0.
  Proof.
    unfold wfb0. intros H.
    apply andb_true_iff in H as [H Hblk]. apply andb_true_iff in H as [H Hval].
    apply andb_true_iff in H as [H Hpres]. apply andb_true_iff in H as [H Hcomp].
    apply andb_true_iff in H as [H Hcall]. apply andb_true_iff in H as [Hnd Hth].
    constructor.
    - apply (SL.nodupb_spec LEv_eqb LEv_eqb_eq); [|exact Hnd].
      intros a. unfold LEv_eqb. destruct (LEv_eq_dec a a); congruence.
    - apply (SL.nodupb_spec Nat.eqb (fun a b => proj1 (Nat.eqb_eq a b))); [|exact Hth].
      intros a. apply Nat.eqb_refl.
    - intros e He. rewrite forallb_forall in Hcall. specialize (Hcall e He).
      apply andb_true_iff in Hcall as [H1 H2]. split.
      + apply existsb_exists in H1 as (t & Ht & E). apply Nat.eqb_eq in E. congruence.
      + destruct (nth_error (ltrace (prog0 X0 (lth e))) (lix e)); cbn in H2; [|discriminate].
        destruct (LC_eq_dec l (lcall e)); congruence.
    - intros t i Ht Hi. rewrite forallb_forall in Hcomp. specialize (Hcomp t Ht).
      rewrite forallb_forall in Hcomp. specialize (Hcomp i ltac:(apply in_seq; lia)).
      apply existsb_exists in Hcomp as (e & He & E). apply LEv_eqb_eq in E. congruence.
    - intros e1 e2 He1 He2 Et Hi Hu. rewrite forallb_forall in Hpres. specialize (Hpres e1 He1).
      rewrite forallb_forall in Hpres. specialize (Hpres e2 He2).
      rewrite Et, Nat.eqb_refl, Hu in Hpres. apply Nat.ltb_lt in Hi. rewrite Hi in Hpres.
      cbn in Hpres. apply Nat.ltb_lt, Hpres.
    - intros p e Hn. rewrite forallb_forall in Hval.
      assert (Hp : In p (seq 0 (length (wit0 X0))))
        by (apply in_seq; split; [lia|]; apply nth_error_Some; congruence).
      specialize (Hval p Hp). rewrite Hn in Hval. exact Hval.
    - intros t Ht. rewrite forallb_forall in Hblk. apply Hblk, Ht.
  Qed.

  (** The writer takes ticket 0 and writes (1, 1); the reader's first
      [get_ticket] returns 1 (the writer holds the lock), so its
      [test_ticket(1)] is silent; the second iteration succeeds with
      ticket 2. *)
  Definition ex_wit : list LEv :=
    [ mkLE 0 0 (LT (TL.FaaN 0)); mkLE 0 1 (LT (TL.GetO 0)); mkLE 0 2 (LT TL.IncO);
      mkLE 1 0 (LT (TL.GetO 1)); mkLE 1 1 (LD SL.RmbC); mkLE 1 2 (LD (SL.RdX 0));
      mkLE 1 3 (LD (SL.RdY 0)); mkLE 1 4 (LD SL.RmbC);
      mkLE 0 3 (LD SL.WmbC); mkLE 0 4 (LD (SL.WrX 1)); mkLE 0 5 (LD (SL.WrY 1));
      mkLE 0 6 (LD SL.WmbC); mkLE 0 7 (LT TL.IncO);
      mkLE 1 5 (LT (TL.GetO 2)); mkLE 1 6 (LD SL.RmbC); mkLE 1 7 (LD (SL.RdX 1));
      mkLE 1 8 (LD (SL.RdY 1)); mkLE 1 9 (LD SL.RmbC); mkLE 1 10 (LT (TL.GetO 2)) ].

  Definition X0_ex : Exec0 :=
    {| ths0 := [0; 1];
       prog0 := fun t => match t with 0 => [LBW 1 1 0 []] | _ => [LBR [(1, 0, 0, 0)] 2 1 1] end;
       wit0 := ex_wit |}.

  Lemma ex_wf0 rc : WF0 rc TL.plainC X0_ex.
  Proof. apply wfb0_sound. destruct rc; vm_compute; reflexivity. Qed.

  (** The constructed SeqLock-layer witness: the silent [test_ticket] is
      placed right after the [rmb] before it. *)
  Example ex_W1 :
    SL.wit (X1 X0_ex) =
    [ SL.mkEv 0 0 SL.Acq; SL.mkEv 1 0 (SL.GT 1); SL.mkEv 1 1 SL.RmbC; SL.mkEv 1 2 (SL.RdX 0);
      SL.mkEv 1 3 (SL.RdY 0); SL.mkEv 1 4 SL.RmbC; SL.mkEv 1 5 (SL.TT 1 true);
      SL.mkEv 0 1 SL.WmbC; SL.mkEv 0 2 (SL.WrX 1); SL.mkEv 0 3 (SL.WrY 1); SL.mkEv 0 4 SL.WmbC;
      SL.mkEv 0 5 SL.Rel;
      SL.mkEv 1 6 (SL.GT 2); SL.mkEv 1 7 SL.RmbC; SL.mkEv 1 8 (SL.RdX 1); SL.mkEv 1 9 (SL.RdY 1);
      SL.mkEv 1 10 SL.RmbC; SL.mkEv 1 11 (SL.TT 2 false) ].
  Proof. vm_compute. reflexivity. Qed.

  (** Checked independently by [SeqLockCOH]'s decision procedure. *)
  Example ex_X1_wf rc : SL.WF rc SL.plainTL (X1 X0_ex).
  Proof. apply SL.wfb_sound. destruct rc; vm_compute; reflexivity. Qed.

  Example ex_composition rc :
    exists X, SL.prog X 1 = [SL.BR [(1, 0, 0)] 2 1 1] /\
      WT.Conclusion (dtable rc) (SL.setting SL.sl_cf rc SL.plainTL X).
  Proof.
    destruct (tower_composition_plain rc X0_ex (ex_wf0 rc)) as (X & _ & Ep & _ & _ & _ & Hc).
    exists X. split; [rewrite Ep; reflexivity|exact Hc].
  Qed.

  (** The real-time statement on the example, with the canonical timing. *)
  Example ex_composition_rt rc :
    exists X, SL.prog X 1 = [SL.BR [(1, 0, 0)] 2 1 1] /\
      WT.Conclusion (dtable rc) (setting_rt0 SL.sl_cf rc SL.plainTL X (canon0 X0_ex)).
  Proof.
    destruct (tower_composition_rt_plain rc X0_ex (canon0 X0_ex) (ex_wf0 rc) (canon0_ok X0_ex))
      as (X & _ & Ep & _ & _ & Hc).
    exists X. split; [rewrite Ep; reflexivity|exact Hc].
  Qed.
End SeqLockTower.
