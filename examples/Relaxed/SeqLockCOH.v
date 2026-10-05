(** * The SeqLock tower on COH

    Counter (over COH[own]) -> TicketLock (over Counter ⊗ COH[nxt]) ->
    SeqLock (over TicketLock ⊗ COH[x] ⊗ COH[y] ⊗ Barrier), with every
    barrier issued by the SeqLock layer:

<<
    write(vx,vy) = l.acq(); wmb; x.wrt(vx); y.wrt(vy); wmb; l.rel()
    read()       = do { s <- l.get_ticket(); rmb; a <- x.rd(); b <- y.rd(); rmb }
                   while (l.test_ticket(s))
>>

    Cross-object order is given by the default category table
    [WindowTable.dto]; barriers are the categories [Rmb] and [Wmb].

    - Part A: the categories each layer exports and the interface facts
      (decided over [dto]).
    - Part B: the SeqLock layer at the level of underlay witnesses.  For
      every complete execution whose witness respects the table-induced
      preserved order and the sequential specifications of TicketLock, the
      cells and the barriers, the SeqLock operations linearize at their
      barrier calls ([seqlock_S1], [seqlock_S1_ord]).  The only facts used
      about the TicketLock are [K_ok] (acq and rel are writes, get_ticket
      and test_ticket are reads) and [I = ∅] (its calls of one thread stay
      in order, [same_obj OTL OTL]); [TicketLockCOH] provides both.
    - Part C: composition with a client cell z through [WindowTable]: every
      such execution of SeqLock ⊎ COH[z] gives [Hyps0] and [Inherit] with
      read ↦ rmb, write ↦ wmb, hence [Conclusion] ([seqlock_z_composition]).
    - Part D: clients.  MP through the SeqLock is excluded by the overlay
      specification alone ([mp_forbidden]).  A concrete LB execution
      satisfies every hypothesis ([lb_wf], [lb_allowed]); any signature
      that orders a client read before a SeqLock write and a SeqLock read
      before a client write has no [Conclusion] on it ([lb_refutes]), in
      particular the paper's [read ↦ rfence][write ↦ lfence]
      ([paper_signature_fails], [paper_modes_fail]).
    - Part E: if TicketLock exports [Local] (the only choice under the four
      fence modes, Part A), the selective barriers do not order its calls:
      a torn read has a valid witness and no linearization
      ([torn_with_local_tl]); with the plain categories no witness
      produces it ([torn_impossible_with_plain_tl]).

    Scope: everything is stated at the level of underlay witnesses of
    complete executions (as [WindowTable]); the link from [dto] to the
    module semantics is not done ([WindowLink] covers the four modes).

    The layer below, TicketLock over Counter ⊗ COH[nxt] with no barrier,
    is [TicketLockCOH]; it exports exactly [plainTL]. *)

From Stdlib Require Import List Bool Arith.PeanoNat micromega.Lia.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.

Import ListNotations.

Module SeqLockCOH.
  Module WC := WindowComposition.
  Module WT := WindowTable.
  Import WT.
  Import RelaxedSig.

  (** ** Part A: categories and interface facts *)

  Definition DRMW : DCat := Acc KRW false false.

  (** Counter over COH[own]: [inc = faa], [get = rd]. *)
  Definition cnt_inc : DCat := DRMW.
  Definition cnt_get : DCat := DR.
  (** TicketLock over Counter ⊗ COH[nxt]: every window is the one call on
      [own] ([acq] uses its [own.inc]). *)
  Definition tl_acq : DCat := DRMW.
  Definition tl_rel : DCat := DRMW.
  Definition tl_gt : DCat := DR.
  Definition tl_tt : DCat := DR.
  (** SeqLock: the window of [read] is its first [rmb], of [write] its first
      [wmb]. *)
  Definition sl_read : DCat := Rmb.
  Definition sl_write : DCat := Wmb.

  (** [c] may be exported by an operation whose window is one call of
      category [cw]. *)
  Definition exportable rc (c cw : DCat) : Prop :=
    out_le (dtable rc) c cw /\ in_le (dtable rc) c cw.

  Lemma exportable_b rc c cw :
    out_leb rc c cw && in_leb rc c cw = true -> exportable rc c cw.
  Proof.
    intros H. apply andb_true_iff in H as [H1 H2].
    split; [apply out_leb_spec | apply in_leb_spec]; assumption.
  Qed.

  Lemma not_out_le rc c c' : out_leb rc c c' = false -> ~ out_le (dtable rc) c c'.
  Proof. intros H Ho. apply out_leb_spec in Ho. congruence. Qed.

  Lemma not_in_le rc c c' : in_leb rc c c' = false -> ~ in_le (dtable rc) c c'.
  Proof. intros H Hi. apply in_leb_spec in Hi. congruence. Qed.

  Lemma exportable_refl rc c : exportable rc c c.
  Proof. apply single_window_inherits. Qed.

  (** A1. Every window is a single call of the exported category, so
      inheritance holds at every layer boundary. *)
  Lemma tower_inherits rc :
    exportable rc cnt_inc DRMW /\ exportable rc cnt_get DR /\
    exportable rc tl_acq cnt_inc /\ exportable rc tl_rel cnt_inc /\
    exportable rc tl_gt cnt_get /\ exportable rc tl_tt cnt_get /\
    exportable rc sl_read Rmb /\ exportable rc sl_write Wmb.
  Proof. repeat split; apply exportable_refl. Qed.

  (** A2. Under the four fence modes ([emb]), a plain counter call exports
      only [Local]; so does a TicketLock operation whose window is one. *)
  Lemma four_modes_force_local rc m :
    exportable rc (emb m) DRMW \/ exportable rc (emb m) DR -> m = Local.
  Proof.
    intros [[Ho Hi]|[Ho Hi]];
      apply out_leb_spec in Ho; apply in_leb_spec in Hi;
      destruct m, rc; try reflexivity; vm_compute in Ho, Hi; congruence.
  Qed.

  (** A3. The current signature of the paper, [read ↦ rfence],
      [write ↦ lfence] (or [Racq]/[Wrel]), cannot be inherited from the
      barrier windows. *)
  Lemma paper_signature_not_inheritable rc :
    ~ out_le (dtable rc) DRFence Rmb /\ ~ out_le (dtable rc) DRacq Rmb /\
    ~ in_le (dtable rc) DLFence Wmb /\ ~ in_le (dtable rc) DWrel Wmb.
  Proof.
    repeat split; first [apply not_out_le | apply not_in_le]; destruct rc; reflexivity.
  Qed.

  (** A4. [rmb]/[wmb] promise strictly more than plain [R]/[W] (what a
      window on the [seq] access would give), and strictly less than the
      acquire/release categories. *)
  Lemma barrier_exports_strictly_between rc :
    exportable rc DR Rmb /\ ~ out_le (dtable rc) Rmb DR /\ ~ in_le (dtable rc) Rmb DR /\
    exportable rc DW Wmb /\ ~ out_le (dtable rc) Wmb DW /\ ~ in_le (dtable rc) Wmb DW.
  Proof.
    repeat split;
      first [ apply out_leb_spec | apply in_leb_spec | apply not_out_le | apply not_in_le ];
      destruct rc; reflexivity.
  Qed.

  (** A5. Swapping the Counter implementation.  An RC counter
      ([faa rel], [rd acq]) and a TSO counter (locked [faa] is a full
      barrier, reads are acquire) can export the plain signature
      [(RMW, R)], so the TicketLock and SeqLock layers are reused verbatim. *)
  Lemma rc_counter_exports_plain rc :
    exportable rc DRMW (Acc KRW false true) /\ exportable rc DR DRacq.
  Proof. split; apply exportable_b; destruct rc; reflexivity. Qed.

  Lemma tso_counter_exports_plain rc :
    exportable rc DRMW DFence /\ exportable rc DR DRacq.
  Proof. split; apply exportable_b; destruct rc; reflexivity. Qed.

  (** ** Part B: the SeqLock layer *)

  (** Underlay calls: TicketLock, cells [x], [y], barriers, and a client
      cell [z] (used from Part C on; the SeqLock never touches it). *)
  Inductive UC : Type :=
  | Acq | Rel | GT (s : nat) | TT (s : nat) (retry : bool)
  | WrX (v : nat) | WrY (v : nat) | RdX (v : nat) | RdY (v : nat)
  | WmbC | RmbC
  | WrZ (v : nat) | RdZ (v : nat).

  Definition UC_eq_dec (a b : UC) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply Nat.eq_dec | apply bool_dec]. Defined.

  Inductive UObj := OTL | OX | OY | OB | OZ.

  Definition uobj (c : UC) : UObj :=
    match c with
    | Acq | Rel | GT _ | TT _ _ => OTL
    | WrX _ | RdX _ => OX
    | WrY _ | RdY _ => OY
    | WmbC | RmbC => OB
    | WrZ _ | RdZ _ => OZ
    end.

  (** TicketLock and the cells have [I = ∅]; barriers are ordered among
      themselves by the table only. *)
  Definition same_obj (a b : UObj) : bool :=
    match a, b with
    | OTL, OTL | OX, OX | OY, OY | OZ, OZ => true
    | _, _ => false
    end.

  (** The categories exported by the TicketLock below. *)
  Record TLCats := { k_acq : DCat; k_rel : DCat; k_gt : DCat; k_tt : DCat }.

  Definition plainTL : TLCats := {| k_acq := DRMW; k_rel := DRMW; k_gt := DR; k_tt := DR |}.
  Definition localTL : TLCats :=
    {| k_acq := DLocal; k_rel := DLocal; k_gt := DLocal; k_tt := DLocal |}.

  (** The only assumption the SeqLock proof makes about them. *)
  Definition K_ok (K : TLCats) : bool :=
    isW (k_acq K) && isW (k_rel K) && isR (k_gt K) && isR (k_tt K).

  Lemma plainTL_ok : K_ok plainTL = true.
  Proof. reflexivity. Qed.

  Definition ucat (K : TLCats) (c : UC) : DCat :=
    match c with
    | Acq => k_acq K | Rel => k_rel K | GT _ => k_gt K | TT _ _ => k_tt K
    | WrX _ | WrY _ | WrZ _ => DW
    | RdX _ | RdY _ | RdZ _ => DR
    | WmbC => Wmb
    | RmbC => Rmb
    end.

  (** Preserved order of the underlay [TL ⊗ X ⊗ Y ⊗ B ⊗ Z]. *)
  Definition upres (rc : bool) (K : TLCats) (c1 c2 : UC) : bool :=
    same_obj (uobj c1) (uobj c2) || dto rc (ucat K c1) (ucat K c2).

  Lemma dto_W_wmb rc c : isW c = true -> dto rc c Wmb = true.
  Proof. destruct c as [[] [] []| |], rc; cbn; congruence. Qed.
  Lemma dto_wmb_W rc c : isW c = true -> dto rc Wmb c = true.
  Proof. destruct c as [[] [] []| |], rc; cbn; congruence. Qed.
  Lemma dto_R_rmb rc c : isR c = true -> dto rc c Rmb = true.
  Proof. destruct c as [[] [] []| |], rc; cbn; congruence. Qed.
  Lemma dto_rmb_R rc c : isR c = true -> dto rc Rmb c = true.
  Proof. destruct c as [[] [] []| |], rc; cbn; congruence. Qed.

  (** *** Programs *)

  (** A block is one overlay operation: a SeqLock write, a SeqLock read
      with its failed iterations, or an access to the client cell. *)
  Inductive Blk : Type :=
  | BW (vx vy : nat)
  | BR (fails : list (nat * nat * nat)) (s a b : nat)
  | BZw (v : nat)
  | BZr (v : nat).

  Definition iter (s a b : nat) (retry : bool) : list UC :=
    [GT s; RmbC; RdX a; RdY b; RmbC; TT s retry].

  Definition fail_calls (fs : list (nat * nat * nat)) : list UC :=
    flat_map (fun '(s, a, b) => iter s a b true) fs.

  Definition wcalls (vx vy : nat) : list UC := [Acq; WmbC; WrX vx; WrY vy; WmbC; Rel].

  Definition calls (k : Blk) : list UC :=
    match k with
    | BW vx vy => wcalls vx vy
    | BR fs s a b => fail_calls fs ++ iter s a b false
    | BZw v => [WrZ v]
    | BZr v => [RdZ v]
    end.

  Definition trace (p : list Blk) : list UC := flat_map calls p.
  Definition off (p : list Blk) (j : nat) : nat := length (trace (firstn j p)).

  (** Start of the final iteration of a read. *)
  Definition base (k : Blk) : nat :=
    match k with BR fs _ _ _ => length (fail_calls fs) | _ => 0 end.

  (** Index of the window call inside the block. *)
  Definition lpi (k : Blk) : nat :=
    match k with BW _ _ | BR _ _ _ _ => base k + 1 | _ => 0 end.

  Definition is_sl (k : Blk) : bool :=
    match k with BW _ _ | BR _ _ _ _ => true | _ => false end.

  (** *** Executions *)

  Record Ev : Type := mkEv { th : nat; ix : nat; call : UC }.

  Definition Ev_eq_dec (a b : Ev) : {a = b} + {a <> b}.
  Proof. decide equality; first [apply UC_eq_dec | apply Nat.eq_dec]. Defined.

  (** Sequential state of [TL ⊗ X ⊗ Y ⊗ B ⊗ Z].  The TicketLock
      specification is an abstract lock with a version counter: [acq]
      needs the lock free and makes the counter odd, [rel] is done by the
      holder and makes it even. *)
  Record State : Type := mkSt { own : nat; hold : option nat; sx : nat; sy : nat; sz : nat }.

  Definition init : State := mkSt 0 None 0 0 0.

  Definition opt_eqb (a b : option nat) : bool :=
    match a, b with
    | None, None => true
    | Some x, Some y => Nat.eqb x y
    | _, _ => false
    end.

  Lemma opt_eqb_eq a b : opt_eqb a b = true -> a = b.
  Proof. destruct a, b; cbn; try congruence. intros H. apply Nat.eqb_eq in H. congruence. Qed.

  (** Enabledness and return-value check of one call. *)
  Definition pre (s : State) (e : Ev) : bool :=
    match call e with
    | Acq => Nat.even (own s) && opt_eqb (hold s) None
    | Rel => opt_eqb (hold s) (Some (th e))
    | GT v => Nat.eqb (own s) v
    | TT v r => Bool.eqb r (Nat.odd v || negb (Nat.eqb (own s) v))
    | RdX v => Nat.eqb (sx s) v
    | RdY v => Nat.eqb (sy s) v
    | RdZ v => Nat.eqb (sz s) v
    | _ => true
    end.

  Definition post (s : State) (e : Ev) : State :=
    match call e with
    | Acq => mkSt (S (own s)) (Some (th e)) (sx s) (sy s) (sz s)
    | Rel => mkSt (S (own s)) None (sx s) (sy s) (sz s)
    | WrX v => mkSt (own s) (hold s) v (sy s) (sz s)
    | WrY v => mkSt (own s) (hold s) (sx s) v (sz s)
    | WrZ v => mkSt (own s) (hold s) (sx s) (sy s) v
    | _ => s
    end.

  Fixpoint run (s : State) (l : list Ev) : State :=
    match l with
    | [] => s
    | e :: l' => run (post s e) l'
    end.

  Record Exec : Type := { ths : list nat; prog : nat -> list Blk; wit : list Ev }.

  Fixpoint idx (e : Ev) (l : list Ev) : nat :=
    match l with
    | [] => 0
    | e' :: l' => if Ev_eq_dec e e' then 0 else S (idx e l')
    end.

  Section WithExec.
    Context (rc : bool) (K : TLCats) (X : Exec).

    Definition at_ (p : nat) : State := run init (firstn p (wit X)).

    (** The [i]-th call of thread [t], and its position in the witness. *)
    Definition evt (t i : nat) : Ev := mkEv t i (nth i (trace (prog X t)) WmbC).
    Definition P (t i : nat) : nat := idx (evt t i) (wit X).

    (** A complete execution: the witness lists every call of every thread
        exactly once, respects the preserved order, and is valid for the
        sequential specification. *)
    Record WF : Prop := {
      wf_nodup : NoDup (wit X);
      wf_ths : NoDup (ths X);
      wf_call : forall e, In e (wit X) ->
                  In (th e) (ths X) /\ nth_error (trace (prog X (th e))) (ix e) = Some (call e);
      wf_complete : forall t i, In t (ths X) -> i < length (trace (prog X t)) ->
                      In (evt t i) (wit X);
      wf_pres : forall e1 e2, In e1 (wit X) -> In e2 (wit X) -> th e1 = th e2 ->
                  ix e1 < ix e2 -> upres rc K (call e1) (call e2) = true ->
                  idx e1 (wit X) < idx e2 (wit X);
      wf_valid : forall p e, nth_error (wit X) p = Some e -> pre (at_ p) e = true;
    }.

    (** Overlay operations: (thread, block index). *)
    Definition blk (q : nat * nat) : option Blk := nth_error (prog X (fst q)) (snd q).

    Definition all_ops : list (nat * nat) :=
      flat_map (fun t => map (pair t) (seq 0 (length (prog X t)))) (ths X).

    Definition is_sl_op (q : nat * nat) : bool :=
      match blk q with Some k => is_sl k | None => false end.

    Definition sl_ops : list (nat * nat) := filter is_sl_op all_ops.

    (** Position of the [i]-th call of block [q]. *)
    Definition Pq (q : nat * nat) (i : nat) : nat :=
      P (fst q) (off (prog X (fst q)) (snd q) + i).

    Definition lpi_of (q : nat * nat) : nat :=
      match blk q with Some k => lpi k | None => 0 end.

    (** The window (= linearization) call of [q], and its position. *)
    Definition lpc (q : nat * nat) : Ev :=
      evt (fst q) (off (prog X (fst q)) (snd q) + lpi_of q).

    Definition lpq (q : nat * nat) : nat := idx (lpc q) (wit X).
  End WithExec.

  (** *** Lemmas on traces, offsets and positions *)

  Lemma trace_app l1 l2 : trace (l1 ++ l2) = trace l1 ++ trace l2.
  Proof. unfold trace. apply flat_map_app. Qed.

  Lemma off_0 p : off p 0 = 0.
  Proof. reflexivity. Qed.

  Lemma off_cons a p j : off (a :: p) (S j) = length (calls a) + off p j.
  Proof. unfold off. cbn [firstn]. unfold trace. cbn [flat_map]. apply length_app. Qed.

  Lemma off_S p j k : nth_error p j = Some k -> off p (S j) = off p j + length (calls k).
  Proof.
    revert j. induction p as [|a p IH]; intros [|j] H; cbn in H; try discriminate.
    - injection H as <-. rewrite off_cons, !off_0. lia.
    - rewrite !off_cons. specialize (IH j H). lia.
  Qed.

  Lemma off_mono p j j' : j <= j' -> off p j <= off p j'.
  Proof.
    revert j j'. induction p as [|a p IH]; intros j j' Hle.
    - unfold off. rewrite !firstn_nil. lia.
    - destruct j as [|j]; [rewrite off_0; lia|].
      destruct j' as [|j']; [lia|].
      rewrite !off_cons. specialize (IH j j' ltac:(lia)). lia.
  Qed.

  Lemma off_lt p j j' k i :
    nth_error p j = Some k -> i < length (calls k) -> j < j' -> off p j + i < off p j'.
  Proof.
    intros Hj Hi Hlt. pose proof (off_S p j k Hj). pose proof (off_mono p (S j) j' Hlt). lia.
  Qed.

  Lemma trace_off p j k i :
    nth_error p j = Some k -> nth_error (trace p) (off p j + i) = nth_error (calls k) i \/ length (calls k) <= i.
  Proof.
    intros Hj. destruct (Nat.lt_ge_cases i (length (calls k))) as [Hi|Hi]; [left|right; exact Hi].
    destruct (nth_error_split p j Hj) as (l1 & l2 & -> & Hl1). subst j.
    unfold off. rewrite firstn_app, firstn_all, Nat.sub_diag, firstn_O, app_nil_r.
    rewrite trace_app. cbn [trace flat_map]. rewrite nth_error_app2 by (unfold trace; lia).
    replace (length (trace l1) + i - length (trace l1)) with i by lia.
    rewrite nth_error_app1 by exact Hi. reflexivity.
  Qed.

  Lemma trace_off' p j k i :
    nth_error p j = Some k -> i < length (calls k) ->
    nth_error (trace p) (off p j + i) = nth_error (calls k) i.
  Proof. intros Hj Hi. destruct (trace_off p j k i Hj) as [H|H]; [exact H|lia]. Qed.

  Lemma trace_inv p i c :
    nth_error (trace p) i = Some c ->
    exists j k i', nth_error p j = Some k /\ i = off p j + i' /\ nth_error (calls k) i' = Some c.
  Proof.
    revert i. induction p as [|a p IH]; intros i H; [destruct i; discriminate|].
    cbn [trace flat_map] in H. fold (trace p) in H.
    destruct (Nat.lt_ge_cases i (length (calls a))) as [Hi|Hi].
    - rewrite nth_error_app1 in H by exact Hi.
      exists 0, a, i. rewrite off_0. auto.
    - rewrite nth_error_app2 in H by exact Hi.
      destruct (IH _ H) as (j & k & i' & Hj & Ei & Hk).
      exists (S j), k, i'. split; [exact Hj|]. split; [|exact Hk].
      rewrite off_cons. lia.
  Qed.

  Lemma calls_BR_kind fs s a b c :
    In c (calls (BR fs s a b)) ->
    match c with GT _ | RmbC | RdX _ | RdY _ | TT _ _ => True | _ => False end.
  Proof.
    cbn. intros H. apply in_app_or in H as [H|H].
    - unfold fail_calls in H. apply in_flat_map in H as ([[s' a'] b'] & _ & H).
      cbn in H. intuition (subst; exact I).
    - cbn in H. intuition (subst; exact I).
  Qed.

  Lemma calls_BR_final fs s a b i :
    i < 6 -> nth_error (calls (BR fs s a b)) (base (BR fs s a b) + i) = nth_error (iter s a b false) i.
  Proof.
    intros Hi. cbn. rewrite nth_error_app2 by lia.
    f_equal. lia.
  Qed.

  Lemma length_calls_BR fs s a b : length (calls (BR fs s a b)) = base (BR fs s a b) + 6.
  Proof. cbn. rewrite length_app. reflexivity. Qed.

  Lemma idx_nth e l : In e l -> nth_error l (idx e l) = Some e.
  Proof.
    induction l as [|e' l IH]; cbn; [contradiction|].
    destruct (Ev_eq_dec e e') as [->|Hne]; [reflexivity|].
    intros [->|H]; [contradiction|]. apply IH, H.
  Qed.

  Lemma nth_idx l p e : NoDup l -> nth_error l p = Some e -> idx e l = p.
  Proof.
    revert p. induction l as [|e' l IH]; intros p Hnd H; [destruct p; discriminate|].
    inversion Hnd as [|? ? Hni Hnd']; subst.
    destruct p as [|p]; cbn in H |- *.
    - injection H as ->. destruct (Ev_eq_dec e e); [reflexivity|contradiction].
    - destruct (Ev_eq_dec e e') as [->|Hne].
      + exfalso. apply Hni. eapply nth_error_In. exact H.
      + f_equal. apply IH; assumption.
  Qed.

  Lemma idx_lt e l : In e l -> idx e l < length l.
  Proof. intros H. apply nth_error_Some. rewrite idx_nth by exact H. discriminate. Qed.

  Lemma idx_inj e e' l : In e l -> In e' l -> idx e l = idx e' l -> e = e'.
  Proof.
    intros H H' E. pose proof (idx_nth e l H) as A. pose proof (idx_nth e' l H') as B.
    rewrite E in A. congruence.
  Qed.

  Lemma firstn_S_nth {A} (l : list A) p :
    firstn (S p) l = firstn p l ++ match nth_error l p with Some e => [e] | None => [] end.
  Proof.
    revert p. induction l as [|a l IH]; intros [|p]; try reflexivity.
    change (firstn (S (S p)) (a :: l)) with (a :: firstn (S p) l).
    rewrite IH. reflexivity.
  Qed.

  Lemma run_app s l1 l2 : run s (l1 ++ l2) = run (run s l1) l2.
  Proof. revert s. induction l1; intros s; cbn; auto. Qed.

  Lemma at_S X p :
    at_ X (S p) = match nth_error (wit X) p with Some e => post (at_ X p) e | None => at_ X p end.
  Proof.
    unfold at_. rewrite firstn_S_nth, run_app.
    destruct (nth_error (wit X) p); reflexivity.
  Qed.

  Definition incr (c : UC) : nat := match c with Acq | Rel => 1 | _ => 0 end.

  Lemma own_post s e : own (post s e) = own s + incr (call e).
  Proof. unfold post, incr. destruct (call e); cbn; lia. Qed.

  Lemma own_S X p :
    own (at_ X (S p)) = own (at_ X p) +
      match nth_error (wit X) p with Some e => incr (call e) | None => 0 end.
  Proof. rewrite at_S. destruct (nth_error (wit X) p); [apply own_post | lia]. Qed.

  Lemma own_mono X p p' : p <= p' -> own (at_ X p) <= own (at_ X p').
  Proof.
    induction 1 as [|p' Hle IH]; [lia|].
    rewrite own_S. lia.
  Qed.

  (** A field of the state that only one kind of call writes holds the
      value of the last such call before the position. *)
  Section Field.
    Context (f : State -> nat) (wr : UC -> option nat).
    Hypothesis f_post : forall s e,
      f (post s e) = match wr (call e) with Some v => v | None => f s end.

    Lemma field_S X p :
      f (at_ X (S p)) =
        match nth_error (wit X) p with
        | Some e => match wr (call e) with Some v => v | None => f (at_ X p) end
        | None => f (at_ X p)
        end.
    Proof. rewrite at_S. destruct (nth_error (wit X) p); [apply f_post | reflexivity]. Qed.

    Lemma field_none X k :
      (forall p e, p < k -> nth_error (wit X) p = Some e -> wr (call e) = None) ->
      f (at_ X k) = f init.
    Proof.
      induction k as [|k IH]; intros H; [reflexivity|].
      rewrite field_S. destruct (nth_error (wit X) k) as [e|] eqn:E.
      - rewrite (H k e ltac:(lia) E). apply IH. intros p e' Hp. apply H. lia.
      - apply IH. intros p e' Hp. apply H. lia.
    Qed.

    Lemma field_last X p0 e0 v k :
      nth_error (wit X) p0 = Some e0 -> wr (call e0) = Some v -> p0 < k ->
      (forall p e, p0 < p -> p < k -> nth_error (wit X) p = Some e -> wr (call e) = None) ->
      f (at_ X k) = v.
    Proof.
      intros H0 Hw. induction k as [|k IH]; intros Hlt H; [lia|].
      rewrite field_S. destruct (Nat.eq_dec k p0) as [->|Hne].
      - rewrite H0, Hw. reflexivity.
      - destruct (nth_error (wit X) k) as [e|] eqn:E.
        + rewrite (H k e ltac:(lia) ltac:(lia) E). apply IH; [lia|].
          intros p e' Hp1 Hp2. apply H; lia.
        + apply IH; [lia|]. intros p e' Hp1 Hp2. apply H; lia.
    Qed.
  End Field.

  Definition wrx (c : UC) : option nat := match c with WrX v => Some v | _ => None end.
  Definition wry (c : UC) : option nat := match c with WrY v => Some v | _ => None end.
  Definition wrz (c : UC) : option nat := match c with WrZ v => Some v | _ => None end.

  Lemma sx_post s e : sx (post s e) = match wrx (call e) with Some v => v | None => sx s end.
  Proof. unfold post, wrx. destruct (call e); reflexivity. Qed.
  Lemma sy_post s e : sy (post s e) = match wry (call e) with Some v => v | None => sy s end.
  Proof. unfold post, wry. destruct (call e); reflexivity. Qed.
  Lemma sz_post s e : sz (post s e) = match wrz (call e) with Some v => v | None => sz s end.
  Proof. unfold post, wrz. destruct (call e); reflexivity. Qed.

  Lemma hold_post s e :
    hold (post s e) = match call e with Acq => Some (th e) | Rel => None | _ => hold s end.
  Proof. unfold post. destruct (call e); reflexivity. Qed.

  Lemma all_ops_In X q : In q (all_ops X) <-> In (fst q) (ths X) /\ snd q < length (prog X (fst q)).
  Proof.
    destruct q as [t j]. unfold all_ops. rewrite in_flat_map. split.
    - intros (t' & Ht' & Hin). apply in_map_iff in Hin as (j' & E & Hj). injection E as <- <-.
      apply in_seq in Hj. cbn. split; [exact Ht'|lia].
    - cbn. intros [Ht Hj]. exists t. split; [exact Ht|]. apply in_map_iff. exists j.
      split; [reflexivity|]. apply in_seq. lia.
  Qed.

  Lemma all_ops_blk X q : In q (all_ops X) -> exists k, blk X q = Some k.
  Proof.
    intros H. apply all_ops_In in H as [_ H]. unfold blk.
    destruct (nth_error (prog X (fst q)) (snd q)) eqn:E; [eauto|].
    apply nth_error_None in E. lia.
  Qed.

  Lemma all_ops_of X t j k : In t (ths X) -> nth_error (prog X t) j = Some k -> In (t, j) (all_ops X).
  Proof.
    intros Ht Hj. apply all_ops_In. split; [exact Ht|]. cbn.
    apply nth_error_Some. congruence.
  Qed.

  Lemma all_ops_nodup X : NoDup (ths X) -> NoDup (all_ops X).
  Proof.
    unfold all_ops. induction 1 as [|t l Hni Hnd IH]; cbn; [constructor|].
    apply NoDup_app; [| exact IH |].
    - assert (Hm : forall m : list nat, NoDup m -> NoDup (map (@pair nat nat t) m)).
      { induction 1 as [|x m Hx _ IHm]; cbn; constructor; [|exact IHm].
        intros Hin. apply in_map_iff in Hin as (y & E & Hy). injection E as ->. contradiction. }
      apply Hm, seq_NoDup.
    - intros q Hq Hq'. apply in_map_iff in Hq as (j & <- & _).
      apply in_flat_map in Hq' as (t' & Ht' & Hin). apply in_map_iff in Hin as (j' & E & _).
      injection E as -> _. contradiction.
  Qed.

  (** Overlay events and the sequential specifications of the overlay
      objects: the SeqLock is a register of pairs, z a register. *)
  Inductive OvEv := OW (vx vy : nat) | OR (a b : nat) | OZW (v : nat) | OZR (v : nat).

  Section Reg.
    Context {V : Type} (owr ord : OvEv -> option V).

    Fixpoint reg_ok (cur : V) (h : list OvEv) : Prop :=
      match h with
      | [] => True
      | o :: h' =>
          match owr o with
          | Some v => reg_ok v h'
          | None => match ord o with Some v => v = cur /\ reg_ok cur h' | None => reg_ok cur h' end
          end
      end.

    Context {A : Type} (key : A -> nat) (ov : A -> OvEv).

    (** The value [v] returned by [r] is that of the last write before it,
        or the initial value. *)
    Definition last_ok (init : V) (L : list A) (r : A) (v : V) : Prop :=
      (exists w u, In w L /\ owr (ov w) = Some u /\ key w < key r /\ v = u /\
         forall w' u', In w' L -> owr (ov w') = Some u' -> key w' < key r -> key w' <= key w)
      \/ ((forall w' u', In w' L -> owr (ov w') = Some u' -> ~ key w' < key r) /\ v = init).

    Lemma reg_ok_of_last L : forall init,
      StronglySorted (fun a b => key a < key b) L ->
      (forall r v, In r L -> owr (ov r) = None -> ord (ov r) = Some v -> last_ok init L r v) ->
      reg_ok init (map ov L).
    Proof.
      induction L as [|a L IH]; intros init Hs Hl; cbn; [exact I|].
      inversion Hs as [|? ? Hs' Hf]; subst. rewrite Forall_forall in Hf.
      destruct (owr (ov a)) as [u|] eqn:Ea.
      - apply IH; [exact Hs'|]. intros r v Hr Hw Hrd.
        destruct (Hl r v (or_intror Hr) Hw Hrd) as [(w & u' & Hw' & Ew & Hk & -> & Hmax)|(Hnone & ->)].
        + destruct Hw' as [<-|Hw'].
          * right. split; [|congruence].
            intros w' u'' Hw'' Ew'' Hk'. specialize (Hmax w' u'' (or_intror Hw'') Ew'' Hk').
            specialize (Hf w' Hw''). lia.
          * left. exists w, u'. repeat split; try assumption.
            intros w' u'' Hw'' Ew''. apply (Hmax w' u''); [right|]; assumption.
        + exfalso. apply (Hnone a u (or_introl eq_refl) Ea). apply Hf, Hr.
      - assert (Hrest : forall r v, In r L -> owr (ov r) = None -> ord (ov r) = Some v ->
                          last_ok init L r v).
        { intros r v Hr Hw Hrd.
          destruct (Hl r v (or_intror Hr) Hw Hrd) as [(w & u' & Hw' & Ew & Hk & -> & Hmax)|(Hnone & ->)].
          - destruct Hw' as [<-|Hw']; [congruence|].
            left. exists w, u'. repeat split; try assumption.
            intros w' u'' Hw'' Ew''. apply (Hmax w' u''); [right|]; assumption.
          - right. split; [|reflexivity]. intros w' u'' Hw''. apply Hnone. right; exact Hw''. }
        destruct (ord (ov a)) as [v|] eqn:Er.
        + split.
          * destruct (Hl a v (or_introl eq_refl) Ea Er) as [(w & u' & Hw' & Ew & Hk & _ & _)|(_ & ->)];
              [|reflexivity].
            exfalso. destruct Hw' as [<-|Hw']; [lia|]. specialize (Hf w Hw'). lia.
          * apply IH; assumption.
        + apply IH; assumption.
    Qed.
  End Reg.

  Definition sl_wr (o : OvEv) : option (nat * nat) := match o with OW x y => Some (x, y) | _ => None end.
  Definition sl_rd (o : OvEv) : option (nat * nat) := match o with OR a b => Some (a, b) | _ => None end.
  Definition z_wr (o : OvEv) : option nat := match o with OZW v => Some v | _ => None end.
  Definition z_rd (o : OvEv) : option nat := match o with OZR v => Some v | _ => None end.

  (** ν_SeqLock and ν_COH[z]. *)
  Definition nu_sl (h : list OvEv) : Prop := reg_ok sl_wr sl_rd (0, 0) h.
  Definition nu_z (h : list OvEv) : Prop := reg_ok z_wr z_rd 0 h.

  Definition ovl (X : Exec) (q : nat * nat) : OvEv :=
    match blk X q with
    | Some (BW x y) => OW x y
    | Some (BR _ _ a b) => OR a b
    | Some (BZw v) => OZW v
    | Some (BZr v) => OZR v
    | None => OZR 0
    end.

  (** A maximum of a key over the elements satisfying a test. *)
  Lemma max_or_none {A} (key : A -> nat) (f : A -> bool) (l : list A) :
    (exists x, In x l /\ f x = true /\ forall y, In y l -> f y = true -> key y <= key x)
    \/ (forall y, In y l -> f y = false).
  Proof.
    induction l as [|a l IH]; [right; intros y []|].
    destruct (f a) eqn:Fa.
    - left. destruct IH as [(x & Hx & Fx & Hmax)|Hnone].
      + destruct (Nat.le_gt_cases (key a) (key x)).
        * exists x. split; [right; exact Hx|]. split; [exact Fx|].
          intros y [<-|Hy] Fy; [assumption|]. apply Hmax; assumption.
        * exists a. split; [left; reflexivity|]. split; [exact Fa|].
          intros y [<-|Hy] Fy; [lia|]. specialize (Hmax y Hy Fy). lia.
      + exists a. split; [left; reflexivity|]. split; [exact Fa|].
        intros y [<-|Hy] Fy; [lia|]. rewrite (Hnone y Hy) in Fy. discriminate.
    - destruct IH as [(x & Hx & Fx & Hmax)|Hnone].
      + left. exists x. split; [right; exact Hx|]. split; [exact Fx|].
        intros y [<-|Hy] Fy; [congruence|]. apply Hmax; assumption.
      + right. intros y [<-|Hy]; [exact Fa|]. apply Hnone, Hy.
  Qed.

  (** *** The SeqLock layer: proof *)

  Section Layer.
    Context (rc : bool) (K : TLCats) (X : Exec).
    Hypothesis HW : WF rc K X.
    Hypothesis HK : K_ok K = true.

    Let HKa : isW (k_acq K) = true.
    Proof. unfold K_ok in HK. repeat (apply andb_true_iff in HK as [HK ?]). assumption. Qed.
    Let HKr : isW (k_rel K) = true.
    Proof. unfold K_ok in HK. repeat (apply andb_true_iff in HK as [HK ?]). assumption. Qed.
    Let HKg : isR (k_gt K) = true.
    Proof. unfold K_ok in HK. repeat (apply andb_true_iff in HK as [HK ?]). assumption. Qed.
    Let HKt : isR (k_tt K) = true.
    Proof. unfold K_ok in HK. repeat (apply andb_true_iff in HK as [HK ?]). assumption. Qed.

    Lemma ev_evt e : In e (wit X) -> e = evt X (th e) (ix e).
    Proof.
      intros H. destruct (wf_call _ _ _ HW e H) as [_ Hn].
      destruct e as [t i c]. unfold evt. cbn in *. f_equal.
      symmetry. apply nth_error_nth. exact Hn.
    Qed.

    Lemma blk_evt t j k i c :
      nth_error (prog X t) j = Some k -> nth_error (calls k) i = Some c ->
      call (evt X t (off (prog X t) j + i)) = c /\
      off (prog X t) j + i < length (trace (prog X t)).
    Proof.
      intros Hj Hi. assert (Hlt : i < length (calls k)) by (apply nth_error_Some; congruence).
      pose proof (trace_off' _ _ _ _ Hj Hlt) as E. rewrite Hi in E.
      split.
      - unfold evt. cbn. apply nth_error_nth. exact E.
      - apply nth_error_Some. congruence.
    Qed.

    (** The [i]-th call of block [q], as an element of the witness. *)
    Lemma Pq_spec q k i c :
      In (fst q) (ths X) -> blk X q = Some k -> nth_error (calls k) i = Some c ->
      nth_error (wit X) (Pq X q i) = Some (evt X (fst q) (off (prog X (fst q)) (snd q) + i)) /\
      call (evt X (fst q) (off (prog X (fst q)) (snd q) + i)) = c.
    Proof.
      intros Ht Hb Hi. destruct (blk_evt _ _ _ _ _ Hb Hi) as [Ec Hlt].
      split; [|exact Ec].
      apply idx_nth. apply (wf_complete _ _ _ HW); assumption.
    Qed.

    Lemma Pq_valid q k i c :
      In (fst q) (ths X) -> blk X q = Some k -> nth_error (calls k) i = Some c ->
      pre (at_ X (Pq X q i)) (evt X (fst q) (off (prog X (fst q)) (snd q) + i)) = true.
    Proof.
      intros Ht Hb Hi. destruct (Pq_spec q k i c Ht Hb Hi) as [Hn _].
      exact (wf_valid _ _ _ HW _ _ Hn).
    Qed.

    Lemma Pq_lt_len q k i c :
      In (fst q) (ths X) -> blk X q = Some k -> nth_error (calls k) i = Some c ->
      Pq X q i < length (wit X).
    Proof.
      intros Ht Hb Hi. destruct (Pq_spec q k i c Ht Hb Hi) as [Hn _].
      apply nth_error_Some. congruence.
    Qed.

    (** Preserved program order between two calls of one thread. *)
    Lemma Pq_cross t j k j' k' i i' c c' :
      In t (ths X) -> nth_error (prog X t) j = Some k -> nth_error (prog X t) j' = Some k' ->
      nth_error (calls k) i = Some c -> nth_error (calls k') i' = Some c' ->
      off (prog X t) j + i < off (prog X t) j' + i' -> upres rc K c c' = true ->
      Pq X (t, j) i < Pq X (t, j') i'.
    Proof.
      intros Ht Hj Hj' Hi Hi' Hlt Hu.
      destruct (Pq_spec (t, j) k i c Ht Hj Hi) as [Hn Ec].
      destruct (Pq_spec (t, j') k' i' c' Ht Hj' Hi') as [Hn' Ec'].
      unfold Pq, P in *. cbn [fst snd] in *.
      apply (wf_pres _ _ _ HW).
      - eapply nth_error_In. exact Hn.
      - eapply nth_error_In. exact Hn'.
      - reflexivity.
      - exact Hlt.
      - rewrite Ec, Ec'. exact Hu.
    Qed.

    Lemma Pq_in q k i i' c c' :
      In (fst q) (ths X) -> blk X q = Some k ->
      nth_error (calls k) i = Some c -> nth_error (calls k) i' = Some c' ->
      i < i' -> upres rc K c c' = true -> Pq X q i < Pq X q i'.
    Proof.
      destruct q as [t j]. intros Ht Hb Hi Hi' Hlt Hu.
      apply (Pq_cross t j k j k i i' c c'); try assumption. lia.
    Qed.

    Lemma Pq_after q k j' k' i i' c c' :
      In (fst q) (ths X) -> blk X q = Some k -> nth_error (prog X (fst q)) j' = Some k' ->
      nth_error (calls k) i = Some c -> nth_error (calls k') i' = Some c' ->
      snd q < j' -> upres rc K c c' = true -> Pq X q i < Pq X (fst q, j') i'.
    Proof.
      destruct q as [t j]. cbn. intros Ht Hb Hb' Hi Hi' Hlt Hu.
      apply (Pq_cross t j k j' k' i i' c c'); try assumption.
      assert (i < length (calls k)) by (apply nth_error_Some; congruence).
      pose proof (off_lt _ _ _ _ _ Hb H Hlt). lia.
    Qed.

    (** Distinct calls have distinct positions. *)
    Lemma Pq_inj q q' k k' i i' c c' :
      In (fst q) (ths X) -> In (fst q') (ths X) -> blk X q = Some k -> blk X q' = Some k' ->
      nth_error (calls k) i = Some c -> nth_error (calls k') i' = Some c' ->
      Pq X q i = Pq X q' i' -> q = q' /\ i = i'.
    Proof.
      destruct q as [t j], q' as [t' j']. cbn. intros Ht Ht' Hb Hb' Hi Hi' E.
      destruct (Pq_spec (t, j) k i c Ht Hb Hi) as [Hn _].
      destruct (Pq_spec (t', j') k' i' c' Ht' Hb' Hi') as [Hn' _].
      cbn [fst snd] in *. rewrite E in Hn. rewrite Hn in Hn'. injection Hn' as Et Ei _. subst t'.
      assert (Li : i < length (calls k)) by (apply nth_error_Some; congruence).
      assert (Li' : i' < length (calls k')) by (apply nth_error_Some; congruence).
      destruct (Nat.lt_trichotomy j j') as [Hlt|[<-|Hlt]].
      - pose proof (off_lt _ _ _ _ _ Hb Li Hlt). lia.
      - split; [reflexivity|]. lia.
      - pose proof (off_lt _ _ _ _ _ Hb' Li' Hlt). lia.
    Qed.

    (** Which block a writing call comes from. *)
    Lemma writer_inv e :
      In e (wit X) ->
      (call e = Acq \/ call e = Rel \/ wrx (call e) <> None \/ wry (call e) <> None) ->
      exists j vx vy i,
        nth_error (prog X (th e)) j = Some (BW vx vy) /\
        nth_error (wcalls vx vy) i = Some (call e) /\
        e = evt X (th e) (off (prog X (th e)) j + i).
    Proof.
      intros He Hc. destruct (wf_call _ _ _ HW e He) as [_ Hn].
      destruct (trace_inv _ _ _ Hn) as (j & k & i & Hj & Ei & Hi).
      destruct k as [vx vy|fs s a b|v|v].
      - exists j, vx, vy, i. split; [exact Hj|]. split; [exact Hi|].
        rewrite <- Ei. apply ev_evt, He.
      - exfalso. pose proof (calls_BR_kind fs s a b (call e) (nth_error_In _ _ Hi)) as Hk.
        destruct Hc as [E|[E|[E|E]]]; rewrite ?E in Hk; try exact Hk;
          destruct (call e); cbn in *; try contradiction; congruence.
      - exfalso. cbn in Hi. destruct i as [|[]]; cbn in Hi; try discriminate.
        injection Hi as E'. destruct Hc as [E|[E|[E|E]]]; rewrite <- E' in E; cbn in E; congruence.
      - exfalso. cbn in Hi. destruct i as [|[]]; cbn in Hi; try discriminate.
        injection Hi as E'. destruct Hc as [E|[E|[E|E]]]; rewrite <- E' in E; cbn in E; congruence.
    Qed.

    Lemma idx_Pq e j vx vy i :
      In e (wit X) -> nth_error (prog X (th e)) j = Some (BW vx vy) ->
      e = evt X (th e) (off (prog X (th e)) j + i) ->
      idx e (wit X) = Pq X (th e, j) i.
    Proof. intros _ _ E. unfold Pq, P. cbn. rewrite E at 1. reflexivity. Qed.

    (** **** Writes *)

    Section Write.
      Context (q : nat * nat) (vx vy : nat).
      Hypothesis Hq : In (fst q) (ths X).
      Hypothesis Hb : blk X q = Some (BW vx vy).

      Lemma write_order :
        Pq X q 0 < Pq X q 1 /\ Pq X q 1 < Pq X q 2 /\ Pq X q 1 < Pq X q 3 /\
        Pq X q 2 < Pq X q 4 /\ Pq X q 3 < Pq X q 4 /\ Pq X q 4 < Pq X q 5.
      Proof.
        repeat split; eapply (Pq_in q (BW vx vy)); try eassumption; try reflexivity; try lia;
          unfold upres; cbn [uobj same_obj ucat orb]; cbn;
          first [ apply dto_W_wmb; assumption | apply dto_wmb_W; first [assumption | reflexivity] ].
      Qed.

      Lemma write_held k :
        Pq X q 0 < k -> k <= Pq X q 5 ->
        own (at_ X k) = S (own (at_ X (Pq X q 0))) /\ hold (at_ X k) = Some (fst q).
      Proof.
        induction k as [|k IH]; intros H1 H2; [lia|].
        destruct (Pq_spec q (BW vx vy) 0 Acq Hq Hb eq_refl) as [Hn0 Ec0].
        rewrite at_S.
        destruct (Nat.eq_dec k (Pq X q 0)) as [->|Hne].
        - rewrite Hn0. rewrite own_post, hold_post, Ec0. cbn. split; [lia|reflexivity].
        - destruct IH as [IHo IHh]; [lia|lia|].
          destruct (nth_error (wit X) k) as [e|] eqn:Ek.
          2:{ exfalso. apply nth_error_None in Ek.
              pose proof (Pq_lt_len q (BW vx vy) 5 Rel Hq Hb eq_refl). lia. }
          pose proof (wf_valid _ _ _ HW _ _ Ek) as Hpre.
          assert (He : In e (wit X)) by (eapply nth_error_In; exact Ek).
          destruct (call e) eqn:Ec.
          + exfalso. unfold pre in Hpre. rewrite Ec, IHh in Hpre. cbn in Hpre.
            rewrite andb_false_r in Hpre. discriminate.
          + exfalso. unfold pre in Hpre. rewrite Ec, IHh in Hpre. cbn in Hpre.
            apply Nat.eqb_eq in Hpre.
            destruct (writer_inv e He (or_intror (or_introl Ec))) as (j' & vx' & vy' & i & Hj' & Hi & Ee).
            rewrite Ec in Hi.
            destruct i as [|[|[|[|[|[|i]]]]]]; cbn in Hi; try discriminate;
              [|destruct i; discriminate].
            pose proof (nth_idx _ _ _ (wf_nodup _ _ _ HW) Ek) as Ik.
            rewrite (idx_Pq e j' vx' vy' 5 He Hj' Ee) in Ik.
            rewrite <- Hpre in Ik, Hj'. destruct q as [t j]. cbn in *.
            destruct (Nat.lt_trichotomy j' j) as [Hlt|[->|Hlt]].
            * pose proof (Pq_after (t, j') (BW vx' vy') j (BW vx vy) 5 0 Rel Acq Hq Hj' Hb
                            eq_refl eq_refl Hlt eq_refl). cbn in H. lia.
            * lia.
            * pose proof (Pq_after (t, j) (BW vx vy) j' (BW vx' vy') 5 5 Rel Rel Hq Hb Hj'
                            eq_refl eq_refl Hlt eq_refl). cbn in H. lia.
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
          + rewrite own_post, hold_post, Ec. cbn. split; [lia|exact IHh].
      Qed.

      Lemma write_odd k :
        Pq X q 0 < k -> k <= Pq X q 5 -> Nat.odd (own (at_ X k)) = true.
      Proof.
        intros H1 H2. destruct (write_held k H1 H2) as [Ho _]. rewrite Ho.
        pose proof (Pq_valid q (BW vx vy) 0 Acq Hq Hb eq_refl) as Hpre.
        destruct (Pq_spec q (BW vx vy) 0 Acq Hq Hb eq_refl) as [_ Ec].
        unfold pre in Hpre. rewrite Ec in Hpre. apply andb_true_iff in Hpre as [Hev _].
        rewrite Nat.odd_succ. exact Hev.
      Qed.
    End Write.

    (** **** Reads: the final iteration *)

    Section Read.
      Context (r : nat * nat) (fs : list (nat * nat * nat)) (s a b : nat).
      Hypothesis Hr : In (fst r) (ths X).
      Hypothesis Hb : blk X r = Some (BR fs s a b).

      Let f := base (BR fs s a b).

      Lemma read_call i c : nth_error (iter s a b false) i = Some c ->
        nth_error (calls (BR fs s a b)) (f + i) = Some c.
      Proof.
        intros H. assert (Hlt : i < length (iter s a b false)) by (apply nth_error_Some; congruence).
        cbn in Hlt. unfold f. rewrite calls_BR_final by lia. exact H.
      Qed.

      Lemma read_call0 : nth_error (calls (BR fs s a b)) f = Some (GT s).
      Proof. rewrite <- (Nat.add_0_r f). apply read_call. reflexivity. Qed.

      Ltac upres_ok :=
        unfold upres; cbn [uobj same_obj ucat orb];
        first [ reflexivity
              | apply dto_W_wmb; first [assumption | reflexivity]
              | apply dto_wmb_W; first [assumption | reflexivity]
              | apply dto_R_rmb; first [assumption | reflexivity]
              | apply dto_rmb_R; first [assumption | reflexivity] ].

      Lemma read_order :
        Pq X r f < Pq X r (f + 1) /\ Pq X r (f + 1) < Pq X r (f + 2) /\
        Pq X r (f + 1) < Pq X r (f + 3) /\ Pq X r (f + 2) < Pq X r (f + 4) /\
        Pq X r (f + 3) < Pq X r (f + 4) /\ Pq X r (f + 4) < Pq X r (f + 5) /\
        Pq X r f < Pq X r (f + 5).
      Proof.
        repeat split.
        - eapply (Pq_in r _ _ _ _ _ Hr Hb read_call0 (read_call 1 RmbC eq_refl)); [lia|upres_ok].
        - eapply (Pq_in r _ _ _ _ _ Hr Hb (read_call 1 RmbC eq_refl) (read_call 2 (RdX a) eq_refl));
            [lia|upres_ok].
        - eapply (Pq_in r _ _ _ _ _ Hr Hb (read_call 1 RmbC eq_refl) (read_call 3 (RdY b) eq_refl));
            [lia|upres_ok].
        - eapply (Pq_in r _ _ _ _ _ Hr Hb (read_call 2 (RdX a) eq_refl) (read_call 4 RmbC eq_refl));
            [lia|upres_ok].
        - eapply (Pq_in r _ _ _ _ _ Hr Hb (read_call 3 (RdY b) eq_refl) (read_call 4 RmbC eq_refl));
            [lia|upres_ok].
        - eapply (Pq_in r _ _ _ _ _ Hr Hb (read_call 4 RmbC eq_refl) (read_call 5 (TT s false) eq_refl));
            [lia|upres_ok].
        - eapply (Pq_in r _ _ _ _ _ Hr Hb read_call0 (read_call 5 (TT s false) eq_refl)); [lia|upres_ok].
      Qed.

      Lemma read_window :
        Nat.even s = true /\
        forall k, Pq X r f <= k -> k <= Pq X r (f + 5) -> own (at_ X k) = s.
      Proof.
        pose proof read_call0 as Hg.
        assert (Ht : nth_error (calls (BR fs s a b)) (f + 5) = Some (TT s false)) by (apply read_call; reflexivity).
        pose proof (Pq_valid r _ _ _ Hr Hb Hg) as Pg.
        destruct (Pq_spec r _ _ _ Hr Hb Hg) as [_ Eg].
        pose proof (Pq_valid r _ _ _ Hr Hb Ht) as Pt.
        destruct (Pq_spec r _ _ _ Hr Hb Ht) as [_ Et].
        unfold pre in Pg, Pt. rewrite Eg in Pg. rewrite Et in Pt.
        apply Nat.eqb_eq in Pg.
        destruct (Nat.odd s) eqn:Os; [cbn in Pt; discriminate|].
        destruct (Nat.eqb (own (at_ X (Pq X r (f + 5)))) s) eqn:Es; [|cbn in Pt; discriminate].
        apply Nat.eqb_eq in Es.
        split.
        - rewrite <- Nat.negb_odd, Os. reflexivity.
        - intros k H1 H2. pose proof (own_mono X _ _ H1). pose proof (own_mono X _ _ H2). lia.
      Qed.

      Lemma read_no_incr p e :
        Pq X r f <= p -> p < Pq X r (f + 5) -> nth_error (wit X) p = Some e -> incr (call e) = 0.
      Proof.
        intros H1 H2 He. destruct read_window as [_ Hw].
        pose proof (own_S X p) as E. rewrite He in E.
        rewrite (Hw p) in E by lia. rewrite (Hw (S p)) in E by lia. lia.
      Qed.
    End Read.

    Definition op_eq_dec (q q' : nat * nat) : {q = q'} + {q <> q'}.
    Proof. decide equality; apply Nat.eq_dec. Defined.

    (** **** Disjointness of critical sections and read windows *)

    Lemma wr_disjoint w vx vy r fs s a b :
      In (fst w) (ths X) -> blk X w = Some (BW vx vy) ->
      In (fst r) (ths X) -> blk X r = Some (BR fs s a b) ->
      Pq X w 5 < Pq X r (base (BR fs s a b)) \/ Pq X r (base (BR fs s a b) + 5) < Pq X w 0.
    Proof.
      intros Hw Hbw Hr Hbr.
      destruct (write_order w vx vy Hw Hbw) as (O1 & O2 & O3 & O4 & O5 & O6).
      destruct (read_order r fs s a b Hr Hbr) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      destruct (read_window r fs s a b Hr Hbr) as [Hev Hwin].
      destruct (Pq_spec w _ 0 Acq Hw Hbw eq_refl) as [Na Ea].
      destruct (Pq_spec w _ 5 Rel Hw Hbw eq_refl) as [Nl El].
      assert (Ha : ~ (Pq X r (base (BR fs s a b)) <= Pq X w 0 /\
                      Pq X w 0 < Pq X r (base (BR fs s a b) + 5))).
      { intros [H1 H2]. pose proof (read_no_incr r fs s a b Hr Hbr _ _ H1 H2 Na) as Z.
        rewrite Ea in Z. discriminate. }
      assert (Hl : ~ (Pq X r (base (BR fs s a b)) <= Pq X w 5 /\
                      Pq X w 5 < Pq X r (base (BR fs s a b) + 5))).
      { intros [H1 H2]. pose proof (read_no_incr r fs s a b Hr Hbr _ _ H1 H2 Nl) as Z.
        rewrite El in Z. discriminate. }
      assert (Hm : ~ (Pq X w 0 < Pq X r (base (BR fs s a b)) /\
                      Pq X r (base (BR fs s a b)) <= Pq X w 5)).
      { intros [H1 H2]. pose proof (write_odd w vx vy Hw Hbw _ H1 H2) as Odd.
        rewrite (Hwin (Pq X r (base (BR fs s a b)))) in Odd by lia.
        rewrite <- Nat.negb_even, Hev in Odd. discriminate. }
      assert (Hne : Pq X w 0 <> Pq X r (base (BR fs s a b) + 5)).
      { intros E.
        destruct (Pq_inj w r _ _ 0 (base (BR fs s a b) + 5) Acq (TT s false) Hw Hr Hbw Hbr eq_refl
                    (read_call fs s a b 5 (TT s false) eq_refl) E) as [-> _].
        congruence. }
      lia.
    Qed.

    Lemma ww_disjoint w vx vy w' vx' vy' :
      In (fst w) (ths X) -> blk X w = Some (BW vx vy) ->
      In (fst w') (ths X) -> blk X w' = Some (BW vx' vy') -> w <> w' ->
      Pq X w 5 < Pq X w' 0 \/ Pq X w' 5 < Pq X w 0.
    Proof.
      intros Hw Hb Hw' Hb' Hne.
      destruct (write_order w vx vy Hw Hb) as (O1 & O2 & O3 & O4 & O5 & O6).
      destruct (write_order w' vx' vy' Hw' Hb') as (P1 & P2 & P3 & P4 & P5 & P6).
      assert (Hacq : forall u ux uy u' ux' uy',
                 In (fst u) (ths X) -> blk X u = Some (BW ux uy) ->
                 In (fst u') (ths X) -> blk X u' = Some (BW ux' uy') ->
                 ~ (Pq X u 0 < Pq X u' 0 /\ Pq X u' 0 <= Pq X u 5)).
      { intros u ux uy u' ux' uy' Hu Hbu Hu' Hbu' [H1 H2].
        pose proof (write_odd u ux uy Hu Hbu _ H1 H2) as Odd.
        pose proof (Pq_valid u' _ 0 Acq Hu' Hbu' eq_refl) as Pre.
        destruct (Pq_spec u' _ 0 Acq Hu' Hbu' eq_refl) as [_ Ec].
        unfold pre in Pre. rewrite Ec in Pre. apply andb_true_iff in Pre as [Hev _].
        rewrite <- Nat.negb_even, Hev in Odd. discriminate. }
      assert (H0 : Pq X w 0 <> Pq X w' 0).
      { intros E. destruct (Pq_inj w w' _ _ 0 0 Acq Acq Hw Hw' Hb Hb' eq_refl eq_refl E) as [? _].
        contradiction. }
      pose proof (Hacq w vx vy w' vx' vy' Hw Hb Hw' Hb').
      pose proof (Hacq w' vx' vy' w vx vy Hw' Hb' Hw Hb).
      lia.
    Qed.

    (** **** What a read observes *)

    Section Field2.
      Context (fld : State -> nat) (wrf : UC -> option nat) (i : nat) (sel : nat -> nat -> nat).
      Hypothesis Hfp : forall s e, fld (post s e) = match wrf (call e) with Some v => v | None => fld s end.
      Hypothesis Hinit : fld init = 0.
      Hypothesis Hcall : forall vx vy, nth_error (wcalls vx vy) i = Some
                           (match i with 2 => WrX (sel vx vy) | _ => WrY (sel vx vy) end).
      Hypothesis Hwr : forall vx vy, wrf (match i with 2 => WrX (sel vx vy) | _ => WrY (sel vx vy) end)
                                     = Some (sel vx vy).
      Hypothesis Hord : forall w vx vy, In (fst w) (ths X) -> blk X w = Some (BW vx vy) ->
                          Pq X w 0 < Pq X w i /\ Pq X w i < Pq X w 5.
      Hypothesis Hinv : forall e, In e (wit X) -> wrf (call e) <> None ->
        exists j vx vy, nth_error (prog X (th e)) j = Some (BW vx vy) /\
                        e = evt X (th e) (off (prog X (th e)) j + i).

      (** A write of the field strictly inside a read window comes from a
          write operation that ends before the window. *)
      Lemma writer_before r fs s a b p e :
        In (fst r) (ths X) -> blk X r = Some (BR fs s a b) ->
        p < Pq X r (base (BR fs s a b) + 5) -> nth_error (wit X) p = Some e -> wrf (call e) <> None ->
        exists w vx vy, In w (all_ops X) /\ blk X w = Some (BW vx vy) /\
          Pq X w 5 < Pq X r (base (BR fs s a b)) /\ p = Pq X w i.
      Proof.
        intros Hr Hbr Hp Hn Hw.
        assert (He : In e (wit X)) by (eapply nth_error_In; exact Hn).
        destruct (Hinv e He Hw) as (j & vx & vy & Hj & Ee).
        destruct (wf_call _ _ _ HW e He) as [Ht _].
        assert (Hb : blk X (th e, j) = Some (BW vx vy)) by exact Hj.
        exists (th e, j), vx, vy. split; [eapply all_ops_of; eassumption|]. split; [exact Hb|].
        assert (Ep : p = Pq X (th e, j) i).
        { rewrite <- (nth_idx _ _ _ (wf_nodup _ _ _ HW) Hn). apply (idx_Pq e j vx vy i He Hj Ee). }
        split; [|exact Ep].
        destruct (wr_disjoint (th e, j) vx vy r fs s a b Ht Hb Hr Hbr) as [H|H]; [exact H|].
        exfalso. destruct (Hord (th e, j) vx vy Ht Hb). lia.
      Qed.

      Lemma field_max r fs s a b w vx vy p :
        In (fst r) (ths X) -> blk X r = Some (BR fs s a b) ->
        In w (all_ops X) -> blk X w = Some (BW vx vy) ->
        Pq X w 5 < Pq X r (base (BR fs s a b)) ->
        (forall w' vx' vy', In w' (all_ops X) -> blk X w' = Some (BW vx' vy') ->
           Pq X w' 5 < Pq X r (base (BR fs s a b)) -> Pq X w' 0 <= Pq X w 0) ->
        Pq X r (base (BR fs s a b)) < p -> p < Pq X r (base (BR fs s a b) + 5) ->
        fld (at_ X p) = sel vx vy.
      Proof.
        intros Hr Hbr Hwo Hbw Hbef Hmax Hp1 Hp2.
        assert (Hw : In (fst w) (ths X)) by (apply all_ops_In in Hwo; tauto).
        destruct (Hord w vx vy Hw Hbw) as [Hw1 Hw2].
        destruct (Pq_spec w _ i _ Hw Hbw (Hcall vx vy)) as [Nw Ew].
        apply (field_last fld wrf Hfp X _ _ _ p Nw); [rewrite Ew; apply Hwr | lia |].
        intros p' e Hp1' Hp2' Hn.
        destruct (wrf (call e)) eqn:Ef; [exfalso|reflexivity].
        destruct (writer_before r fs s a b p' e Hr Hbr ltac:(lia) Hn ltac:(congruence))
          as (w' & vx' & vy' & Hwo' & Hbw' & Hbef' & ->).
        assert (Hw' : In (fst w') (ths X)) by (apply all_ops_In in Hwo'; tauto).
        pose proof (Hmax w' vx' vy' Hwo' Hbw' Hbef') as Hle.
        destruct (Hord w' vx' vy' Hw' Hbw').
        destruct (op_eq_dec w w') as [<-|Hne]; [lia|].
        destruct (ww_disjoint w vx vy w' vx' vy' Hw Hbw Hw' Hbw' Hne); lia.
      Qed.

      Lemma field_none_before r fs s a b p :
        In (fst r) (ths X) -> blk X r = Some (BR fs s a b) ->
        (forall w' vx' vy', In w' (all_ops X) -> blk X w' = Some (BW vx' vy') ->
           ~ Pq X w' 5 < Pq X r (base (BR fs s a b))) ->
        p < Pq X r (base (BR fs s a b) + 5) ->
        fld (at_ X p) = 0.
      Proof.
        intros Hr Hbr Hnone Hp. rewrite <- Hinit.
        apply (field_none fld wrf Hfp X p).
        intros p' e Hp' Hn.
        destruct (wrf (call e)) eqn:Ef; [exfalso|reflexivity].
        destruct (writer_before r fs s a b p' e Hr Hbr ltac:(lia) Hn ltac:(congruence))
          as (w' & vx' & vy' & Hwo' & Hbw' & Hbef' & _).
        exact (Hnone w' vx' vy' Hwo' Hbw' Hbef').
      Qed.
    End Field2.

    Lemma read_value r fs s a b :
      In (fst r) (ths X) -> blk X r = Some (BR fs s a b) ->
      (exists w vx vy, In w (all_ops X) /\ blk X w = Some (BW vx vy) /\
         Pq X w 5 < Pq X r (base (BR fs s a b)) /\ a = vx /\ b = vy /\
         forall w' vx' vy', In w' (all_ops X) -> blk X w' = Some (BW vx' vy') ->
           Pq X w' 5 < Pq X r (base (BR fs s a b)) -> Pq X w' 0 <= Pq X w 0)
      \/ ((forall w' vx' vy', In w' (all_ops X) -> blk X w' = Some (BW vx' vy') ->
            ~ Pq X w' 5 < Pq X r (base (BR fs s a b))) /\ a = 0 /\ b = 0).
    Proof.
      intros Hr Hbr.
      destruct (read_order r fs s a b Hr Hbr) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      assert (Hx : nth_error (calls (BR fs s a b)) (base (BR fs s a b) + 2) = Some (RdX a))
        by (apply read_call; reflexivity).
      assert (Hy : nth_error (calls (BR fs s a b)) (base (BR fs s a b) + 3) = Some (RdY b))
        by (apply read_call; reflexivity).
      pose proof (Pq_valid r _ _ _ Hr Hbr Hx) as Px. destruct (Pq_spec r _ _ _ Hr Hbr Hx) as [_ Ex].
      pose proof (Pq_valid r _ _ _ Hr Hbr Hy) as Py. destruct (Pq_spec r _ _ _ Hr Hbr Hy) as [_ Ey].
      unfold pre in Px, Py. rewrite Ex in Px. rewrite Ey in Py.
      apply Nat.eqb_eq in Px, Py.
      assert (OrdX : forall w vx vy, In (fst w) (ths X) -> blk X w = Some (BW vx vy) ->
                       Pq X w 0 < Pq X w 2 /\ Pq X w 2 < Pq X w 5).
      { intros w vx vy Hw Hb. destruct (write_order w vx vy Hw Hb) as (? & ? & ? & ? & ? & ?). lia. }
      assert (OrdY : forall w vx vy, In (fst w) (ths X) -> blk X w = Some (BW vx vy) ->
                       Pq X w 0 < Pq X w 3 /\ Pq X w 3 < Pq X w 5).
      { intros w vx vy Hw Hb. destruct (write_order w vx vy Hw Hb) as (? & ? & ? & ? & ? & ?). lia. }
      assert (InvX : forall e, In e (wit X) -> wrx (call e) <> None ->
                exists j vx vy, nth_error (prog X (th e)) j = Some (BW vx vy) /\
                                e = evt X (th e) (off (prog X (th e)) j + 2)).
      { intros e He Hw. destruct (writer_inv e He (or_intror (or_intror (or_introl Hw))))
          as (j & vx & vy & i & Hj & Hi & Ee).
        destruct i as [|[|[|[|[|[|i]]]]]]; cbn in Hi; try (destruct i; discriminate);
          injection Hi as Hi; rewrite <- Hi in Hw; cbn in Hw; try congruence.
        exists j, vx, vy. split; assumption. }
      assert (InvY : forall e, In e (wit X) -> wry (call e) <> None ->
                exists j vx vy, nth_error (prog X (th e)) j = Some (BW vx vy) /\
                                e = evt X (th e) (off (prog X (th e)) j + 3)).
      { intros e He Hw. destruct (writer_inv e He (or_intror (or_intror (or_intror Hw))))
          as (j & vx & vy & i & Hj & Hi & Ee).
        destruct i as [|[|[|[|[|[|i]]]]]]; cbn in Hi; try (destruct i; discriminate);
          injection Hi as Hi; rewrite <- Hi in Hw; cbn in Hw; try congruence.
        exists j, vx, vy. split; assumption. }
      set (isbef := fun w => match blk X w with
                             | Some (BW _ _) => Nat.ltb (Pq X w 5) (Pq X r (base (BR fs s a b)))
                             | _ => false end).
      destruct (max_or_none (fun w => Pq X w 0) isbef (all_ops X)) as [(w & Hwo & Hbef & Hmax)|Hnone].
      - unfold isbef in Hbef. destruct (blk X w) as [[vx vy| | |]|] eqn:Hbw; try discriminate.
        apply Nat.ltb_lt in Hbef.
        assert (Hmax' : forall w' vx' vy', In w' (all_ops X) -> blk X w' = Some (BW vx' vy') ->
                  Pq X w' 5 < Pq X r (base (BR fs s a b)) -> Pq X w' 0 <= Pq X w 0).
        { intros w' vx' vy' Hw' Hb' Hl. apply Hmax; [exact Hw'|]. unfold isbef. rewrite Hb'.
          apply Nat.ltb_lt, Hl. }
        left. exists w, vx, vy. repeat split; try assumption.
        + rewrite <- Px.
          apply (field_max sx wrx 2 (fun vx vy => vx) sx_post eq_refl (fun _ _ => eq_refl)
                   (fun _ _ => eq_refl) OrdX InvX r fs s a b w vx vy); try assumption; lia.
        + rewrite <- Py.
          apply (field_max sy wry 3 (fun vx vy => vy) sy_post eq_refl (fun _ _ => eq_refl)
                   (fun _ _ => eq_refl) OrdY InvY r fs s a b w vx vy); try assumption; lia.
      - assert (Hn : forall w' vx' vy', In w' (all_ops X) -> blk X w' = Some (BW vx' vy') ->
                  ~ Pq X w' 5 < Pq X r (base (BR fs s a b))).
        { intros w' vx' vy' Hw' Hb' Hl. specialize (Hnone w' Hw'). unfold isbef in Hnone.
          rewrite Hb' in Hnone. apply Nat.ltb_ge in Hnone. lia. }
        right. split; [exact Hn|]. split.
        + rewrite <- Px.
          apply (field_none_before sx wrx 2 sx_post eq_refl OrdX InvX r fs s a b); try assumption; lia.
        + rewrite <- Py.
          apply (field_none_before sy wry 3 sy_post eq_refl OrdY InvY r fs s a b); try assumption; lia.
    Qed.

    (** **** Linearization points *)

    Lemma lpq_Pq q k : blk X q = Some k -> lpq X q = Pq X q (lpi k).
    Proof. intros Hb. unfold lpq, lpc, lpi_of, Pq, P. rewrite Hb. reflexivity. Qed.

    Lemma lpq_W w vx vy : blk X w = Some (BW vx vy) -> lpq X w = Pq X w 1.
    Proof. apply lpq_Pq. Qed.

    Lemma lpq_R r fs s a b : blk X r = Some (BR fs s a b) -> lpq X r = Pq X r (base (BR fs s a b) + 1).
    Proof. apply lpq_Pq. Qed.

    Lemma before_iff w vx vy r fs s a b :
      In (fst w) (ths X) -> blk X w = Some (BW vx vy) ->
      In (fst r) (ths X) -> blk X r = Some (BR fs s a b) ->
      lpq X w < lpq X r <-> Pq X w 5 < Pq X r (base (BR fs s a b)).
    Proof.
      intros Hw Hbw Hr Hbr. rewrite (lpq_W w vx vy Hbw), (lpq_R r fs s a b Hbr).
      destruct (write_order w vx vy Hw Hbw) as (O1 & O2 & O3 & O4 & O5 & O6).
      destruct (read_order r fs s a b Hr Hbr) as (R1 & R2 & R3 & R4 & R5 & R6 & R7).
      destruct (wr_disjoint w vx vy r fs s a b Hw Hbw Hr Hbr); lia.
    Qed.

    Lemma lpi_call q k : blk X q = Some k -> exists c, nth_error (calls k) (lpi k) = Some c.
    Proof.
      intros _. destruct k as [vx vy|fs s a b|v|v].
      - exists WmbC. reflexivity.
      - exists RmbC. apply read_call. reflexivity.
      - exists (WrZ v). reflexivity.
      - exists (RdZ v). reflexivity.
    Qed.

    Lemma lp_inj q q' : In q (all_ops X) -> In q' (all_ops X) -> lpq X q = lpq X q' -> q = q'.
    Proof.
      intros Hq Hq' E.
      destruct (all_ops_blk X q Hq) as [k Hk]. destruct (all_ops_blk X q' Hq') as [k' Hk'].
      destruct (lpi_call q k Hk) as [c Hc]. destruct (lpi_call q' k' Hk') as [c' Hc'].
      rewrite (lpq_Pq q k Hk), (lpq_Pq q' k' Hk') in E.
      apply all_ops_In in Hq as [Ht _]. apply all_ops_In in Hq' as [Ht' _].
      exact (proj1 (Pq_inj q q' k k' _ _ c c' Ht Ht' Hk Hk' Hc Hc' E)).
    Qed.

    Lemma sl_ops_In q : In q (sl_ops X) -> In q (all_ops X) /\
      exists k, blk X q = Some k /\ is_sl k = true.
    Proof.
      unfold sl_ops. intros H. apply filter_In in H as [H Hs]. split; [exact H|].
      unfold is_sl_op in Hs. destruct (blk X q) as [k|]; [eauto|discriminate].
    Qed.

    Theorem seqlock_S1 : nu_sl (map (ovl X) (WC.isort (lpq X) (sl_ops X))).
    Proof.
      unfold nu_sl. apply (reg_ok_of_last sl_wr sl_rd (lpq X) (ovl X)).
      - apply WC.isort_sorted.
        + intros x y Hx Hy. apply lp_inj; [apply sl_ops_In in Hx | apply sl_ops_In in Hy]; tauto.
        + apply NoDup_filter, all_ops_nodup, (wf_ths _ _ _ HW).
      - intros r v Hr Hw Hrd.
        assert (HrL : In r (sl_ops X)) by exact (Permutation_in _ (WC.isort_perm _ _) Hr).
        destruct (sl_ops_In r HrL) as [Hro (k & Hbr & _)].
        assert (Hrt : In (fst r) (ths X)) by (apply all_ops_In in Hro; tauto).
        unfold ovl in Hw, Hrd. rewrite Hbr in Hw, Hrd.
        destruct k as [vx vy|fs s a b|u|u]; cbn in Hw, Hrd; try discriminate.
        injection Hrd as <-.
        assert (HinL : forall w, In w (sl_ops X) -> In w (WC.isort (lpq X) (sl_ops X)))
          by (intros w Hw'; exact (Permutation_in _ (Permutation_sym (WC.isort_perm _ _)) Hw')).
        assert (Hwr : forall w u, In w (WC.isort (lpq X) (sl_ops X)) -> sl_wr (ovl X w) = Some u ->
                   exists vx vy, In w (all_ops X) /\ blk X w = Some (BW vx vy) /\ u = (vx, vy)).
        { intros w u Hw' Hu. apply (Permutation_in _ (WC.isort_perm _ _)) in Hw'.
          destruct (sl_ops_In w Hw') as [Hwo (k & Hbk & _)].
          unfold ovl in Hu. rewrite Hbk in Hu. destruct k; cbn in Hu; try discriminate.
          injection Hu as <-. eauto. }
        destruct (read_value r fs s a b Hrt Hbr)
          as [(w & vx & vy & Hwo & Hbw & Hbef & -> & -> & Hmax)|(Hnone & -> & ->)].
        + assert (Hwt : In (fst w) (ths X)) by (apply all_ops_In in Hwo; tauto).
          left. exists w, (vx, vy). split.
          { apply HinL. unfold sl_ops. apply filter_In. split; [exact Hwo|].
            unfold is_sl_op. rewrite Hbw. reflexivity. }
          split; [unfold ovl; rewrite Hbw; reflexivity|].
          split; [apply (before_iff w vx vy r fs s _ _ Hwt Hbw Hrt Hbr), Hbef|].
          split; [reflexivity|].
          intros w' u' Hw' Hu' Hlt.
          destruct (Hwr w' u' Hw' Hu') as (vx' & vy' & Hwo' & Hbw' & _).
          assert (Hwt' : In (fst w') (ths X)) by (apply all_ops_In in Hwo'; tauto).
          apply (before_iff w' vx' vy' r fs s _ _ Hwt' Hbw' Hrt Hbr) in Hlt.
          pose proof (Hmax w' vx' vy' Hwo' Hbw' Hlt) as Hle.
          rewrite (lpq_W w vx vy Hbw), (lpq_W w' vx' vy' Hbw').
          destruct (op_eq_dec w w') as [<-|Hne]; [lia|].
          destruct (write_order w vx vy Hwt Hbw) as (O1 & O2 & O3 & O4 & O5 & O6).
          destruct (write_order w' vx' vy' Hwt' Hbw') as (P1 & P2 & P3 & P4 & P5 & P6).
          destruct (ww_disjoint w vx vy w' vx' vy' Hwt Hbw Hwt' Hbw' Hne); lia.
        + right. split; [|reflexivity].
          intros w' u' Hw' Hu' Hlt.
          destruct (Hwr w' u' Hw' Hu') as (vx' & vy' & Hwo' & Hbw' & _).
          assert (Hwt' : In (fst w') (ths X)) by (apply all_ops_In in Hwo'; tauto).
          apply (before_iff w' vx' vy' r fs s _ _ Hwt' Hbw' Hrt Hbr) in Hlt.
          exact (Hnone w' vx' vy' Hwo' Hbw' Hlt).
    Qed.

    (** Same-thread SeqLock operations: [I = ∅], so every pair is ordered.
        The chain goes through the TicketLock, an object with [I = ∅]. *)
    Lemma sl_tl_last q k : In (fst q) (ths X) -> blk X q = Some k -> is_sl k = true ->
      exists i c, nth_error (calls k) i = Some c /\ uobj c = OTL /\ lpq X q < Pq X q i.
    Proof.
      intros Hq Hb Hs. destruct k as [vx vy|fs s a b|v|v]; try discriminate.
      - exists 5, Rel. split; [reflexivity|]. split; [reflexivity|].
        rewrite (lpq_W q vx vy Hb). destruct (write_order q vx vy Hq Hb) as (? & ? & ? & ? & ? & ?). lia.
      - exists (base (BR fs s a b) + 5), (TT s false).
        split; [apply read_call; reflexivity|]. split; [reflexivity|].
        rewrite (lpq_R q fs s a b Hb). destruct (read_order q fs s a b Hq Hb) as (? & ? & ? & ? & ? & ? & ?). lia.
    Qed.

    Lemma sl_tl_first q k : In (fst q) (ths X) -> blk X q = Some k -> is_sl k = true ->
      exists i c, nth_error (calls k) i = Some c /\ uobj c = OTL /\ Pq X q i < lpq X q.
    Proof.
      intros Hq Hb Hs. destruct k as [vx vy|fs s a b|v|v]; try discriminate.
      - exists 0, Acq. split; [reflexivity|]. split; [reflexivity|].
        rewrite (lpq_W q vx vy Hb). destruct (write_order q vx vy Hq Hb) as (? & ? & ? & ? & ? & ?). lia.
      - exists (base (BR fs s a b)), (GT s).
        split; [apply read_call0|]. split; [reflexivity|].
        rewrite (lpq_R q fs s a b Hb). destruct (read_order q fs s a b Hq Hb) as (? & ? & ? & ? & ? & ? & ?). lia.
    Qed.

    Theorem seqlock_S1_ord q q' :
      In q (sl_ops X) -> In q' (sl_ops X) -> fst q = fst q' -> snd q < snd q' -> lpq X q < lpq X q'.
    Proof.
      intros Hq Hq' Et Hlt.
      destruct (sl_ops_In q Hq) as [Hqo (k & Hb & Hs)].
      destruct (sl_ops_In q' Hq') as [Hqo' (k' & Hb' & Hs')].
      assert (Ht : In (fst q) (ths X)) by (apply all_ops_In in Hqo; tauto).
      assert (Ht' : In (fst q') (ths X)) by (apply all_ops_In in Hqo'; tauto).
      destruct (sl_tl_last q k Ht Hb Hs) as (i & c & Hc & Oc & L1).
      destruct (sl_tl_first q' k' Ht' Hb' Hs') as (i' & c' & Hc' & Oc' & L2).
      assert (Hb'' : nth_error (prog X (fst q)) (snd q') = Some k') by (rewrite Et; exact Hb').
      pose proof (Pq_after q k (snd q') k' i i' c c' Ht Hb Hb'' Hc Hc' Hlt) as H.
      assert (Hu : upres rc K c c' = true) by (unfold upres; rewrite Oc, Oc'; reflexivity).
      specialize (H Hu). destruct q' as [t' j']. cbn in Et, H |- *. subst t'. lia.
    Qed.

    (** **** The client cell z *)

    Lemma z_writer_inv e :
      In e (wit X) -> wrz (call e) <> None ->
      exists j v, nth_error (prog X (th e)) j = Some (BZw v) /\
                  e = evt X (th e) (off (prog X (th e)) j + 0).
    Proof.
      intros He Hw. destruct (wf_call _ _ _ HW e He) as [_ Hn].
      destruct (trace_inv _ _ _ Hn) as (j & k & i & Hj & Ei & Hi).
      destruct k as [vx vy|fs s a b|v|v].
      - exfalso. destruct i as [|[|[|[|[|[|i]]]]]]; cbn in Hi; try (destruct i; discriminate);
          injection Hi as Hi; rewrite <- Hi in Hw; cbn in Hw; congruence.
      - exfalso. pose proof (calls_BR_kind fs s a b (call e) (nth_error_In _ _ Hi)) as Hk.
        destruct (call e); cbn in *; try contradiction; congruence.
      - destruct i as [|i]; [|destruct i; discriminate].
        exists j, v. split; [exact Hj|]. rewrite <- Ei. apply ev_evt, He.
      - exfalso. destruct i as [|i]; [|destruct i; discriminate].
        injection Hi as Hi. rewrite <- Hi in Hw. cbn in Hw. congruence.
    Qed.

    Definition z_ops : list (nat * nat) := filter (fun q => negb (is_sl_op X q)) (all_ops X).

    Theorem z_S1 : nu_z (map (ovl X) (WC.isort (lpq X) z_ops)).
    Proof.
      unfold nu_z. apply (reg_ok_of_last z_wr z_rd (lpq X) (ovl X)).
      - apply WC.isort_sorted.
        + intros x y Hx Hy. apply lp_inj; [apply filter_In in Hx | apply filter_In in Hy]; tauto.
        + apply NoDup_filter, all_ops_nodup, (wf_ths _ _ _ HW).
      - intros r v Hr Hw Hrd.
        apply (Permutation_in _ (WC.isort_perm _ _)) in Hr.
        apply filter_In in Hr as [Hro _].
        assert (Hrt : In (fst r) (ths X)) by (apply all_ops_In in Hro; tauto).
        destruct (all_ops_blk X r Hro) as [k Hbr].
        unfold ovl in Hw, Hrd. rewrite Hbr in Hw, Hrd.
        destruct k as [vx vy|fs s a b|u|u]; cbn in Hw, Hrd; try discriminate.
        injection Hrd as <-.
        pose proof (Pq_valid r _ 0 (RdZ u) Hrt Hbr eq_refl) as Pr.
        destruct (Pq_spec r _ 0 (RdZ u) Hrt Hbr eq_refl) as [_ Er].
        unfold pre in Pr. rewrite Er in Pr. apply Nat.eqb_eq in Pr.
        assert (HinL : forall w, In w z_ops -> In w (WC.isort (lpq X) z_ops))
          by (intros w Hw'; exact (Permutation_in _ (Permutation_sym (WC.isort_perm _ _)) Hw')).
        assert (Hzw : forall w u', In w (WC.isort (lpq X) z_ops) -> z_wr (ovl X w) = Some u' ->
                   In w (all_ops X) /\ blk X w = Some (BZw u')).
        { intros w u' Hw' Hu. apply (Permutation_in _ (WC.isort_perm _ _)) in Hw'.
          apply filter_In in Hw' as [Hwo _]. destruct (all_ops_blk X w Hwo) as [k Hbk].
          unfold ovl in Hu. rewrite Hbk in Hu. destruct k; cbn in Hu; try discriminate.
          injection Hu as <-. split; assumption. }
        (* a z write strictly before the read in the witness *)
        assert (Hwb : forall p e, p < Pq X r 0 -> nth_error (wit X) p = Some e -> wrz (call e) <> None ->
                   exists w u', In w (all_ops X) /\ blk X w = Some (BZw u') /\ p = Pq X w 0).
        { intros p e Hp Hn Hwz.
          assert (He : In e (wit X)) by (eapply nth_error_In; exact Hn).
          destruct (z_writer_inv e He Hwz) as (j & u' & Hj & Ee).
          destruct (wf_call _ _ _ HW e He) as [Ht _].
          exists (th e, j), u'. split; [eapply all_ops_of; eassumption|]. split; [exact Hj|].
          rewrite <- (nth_idx _ _ _ (wf_nodup _ _ _ HW) Hn). unfold Pq, P. cbn. rewrite Ee at 1. reflexivity. }
        set (isb := fun w => match blk X w with
                             | Some (BZw _) => Nat.ltb (Pq X w 0) (Pq X r 0)
                             | _ => false end).
        destruct (max_or_none (fun w => Pq X w 0) isb (all_ops X)) as [(w & Hwo & Hb & Hmax)|Hnone].
        + unfold isb in Hb. destruct (blk X w) as [[| | u'|]|] eqn:Hbw; try discriminate.
          apply Nat.ltb_lt in Hb.
          assert (Hwt : In (fst w) (ths X)) by (apply all_ops_In in Hwo; tauto).
          destruct (Pq_spec w _ 0 (WrZ u') Hwt Hbw eq_refl) as [Nw Ew].
          assert (Hval : u = u').
          { rewrite <- Pr. apply (field_last sz wrz sz_post X _ _ _ _ Nw); [rewrite Ew; reflexivity | exact Hb |].
            intros p' e Hp1 Hp2 Hn. destruct (wrz (call e)) eqn:Ez; [exfalso|reflexivity].
            destruct (Hwb p' e Hp2 Hn ltac:(congruence)) as (w' & u'' & Hwo' & Hbw' & ->).
            assert (isb w' = true) by (unfold isb; rewrite Hbw'; apply Nat.ltb_lt; exact Hp2).
            specialize (Hmax w' Hwo' H). lia. }
          left. exists w, u'. split.
          { apply HinL. apply filter_In. split; [exact Hwo|]. unfold is_sl_op. rewrite Hbw. reflexivity. }
          split; [unfold ovl; rewrite Hbw; reflexivity|].
          split; [rewrite (lpq_Pq w _ Hbw), (lpq_Pq r _ Hbr); exact Hb|].
          split; [exact Hval|].
          intros w' u'' Hw' Hu Hlt. destruct (Hzw w' u'' Hw' Hu) as [Hwo' Hbw'].
          rewrite (lpq_Pq w _ Hbw), (lpq_Pq w' _ Hbw'). rewrite (lpq_Pq w' _ Hbw'), (lpq_Pq r _ Hbr) in Hlt.
          apply Hmax; [exact Hwo'|]. unfold isb. rewrite Hbw'. apply Nat.ltb_lt. exact Hlt.
        + right. split.
          * intros w' u'' Hw' Hu Hlt. destruct (Hzw w' u'' Hw' Hu) as [Hwo' Hbw'].
            rewrite (lpq_Pq w' _ Hbw'), (lpq_Pq r _ Hbr) in Hlt.
            specialize (Hnone w' Hwo'). unfold isb in Hnone. rewrite Hbw' in Hnone.
            apply Nat.ltb_ge in Hnone. cbn in Hlt. lia.
          * rewrite <- Pr. apply (field_none sz wrz sz_post X).
            intros p e Hp Hn. destruct (wrz (call e)) eqn:Ez; [exfalso|reflexivity].
            destruct (Hwb p e Hp Hn ltac:(congruence)) as (w' & u'' & Hwo' & Hbw' & ->).
            specialize (Hnone w' Hwo'). unfold isb in Hnone. rewrite Hbw' in Hnone.
            apply Nat.ltb_ge in Hnone. lia.
    Qed.

    Theorem z_S1_ord q q' :
      In q z_ops -> In q' z_ops -> fst q = fst q' -> snd q < snd q' -> lpq X q < lpq X q'.
    Proof.
      intros Hq Hq' Et Hlt.
      apply filter_In in Hq as [Hqo Hs]. apply filter_In in Hq' as [Hqo' Hs'].
      destruct (all_ops_blk X q Hqo) as [k Hb]. destruct (all_ops_blk X q' Hqo') as [k' Hb'].
      assert (Ht : In (fst q) (ths X)) by (apply all_ops_In in Hqo; tauto).
      unfold is_sl_op in Hs, Hs'. rewrite Hb in Hs. rewrite Hb' in Hs'.
      assert (Hz : forall k, is_sl k = false -> exists c, nth_error (calls k) 0 = Some c /\ uobj c = OZ /\ lpi k = 0).
      { intros [] H; cbn in H; try discriminate; eexists; (split; [reflexivity|split; reflexivity]). }
      destruct (Hz k ltac:(destruct (is_sl k); [discriminate|reflexivity])) as (c & Hc & Oc & L).
      destruct (Hz k' ltac:(destruct (is_sl k'); [discriminate|reflexivity])) as (c' & Hc' & Oc' & L').
      rewrite (lpq_Pq q k Hb), (lpq_Pq q' k' Hb'), L, L'.
      assert (Hb'' : nth_error (prog X (fst q)) (snd q') = Some k') by (rewrite Et; exact Hb').
      pose proof (Pq_after q k (snd q') k' 0 0 c c' Ht Hb Hb'' Hc Hc' Hlt) as H.
      assert (Hu : upres rc K c c' = true) by (unfold upres; rewrite Oc, Oc'; reflexivity).
      specialize (H Hu). destruct q' as [t' j']. cbn in Et, H |- *. subst t'. exact H.
    Qed.
  End Layer.

  (** ** Part C: SeqLock ⊎ COH[z] through [WindowTable] *)

  Inductive CompT := CSL | CZ.

  Definition comp_dec (c c' : CompT) : {c = c'} + {c <> c'}.
  Proof. decide equality. Defined.

  (** Overlay categories: [sl_cf] is the proposed signature
      (read ↦ rmb, write ↦ wmb); [paper_cf] the current one
      (read ↦ acquire, write ↦ release). *)
  Definition sl_cf (k : Blk) : DCat :=
    match k with BW _ _ => Wmb | BR _ _ _ _ => Rmb | BZw _ => DW | BZr _ => DR end.
  Definition paper_cf (k : Blk) : DCat :=
    match k with BW _ _ => DWrel | BR _ _ _ _ => DRacq | BZw _ => DW | BZr _ => DR end.

  (** One execution of SeqLock ⊎ COH[z], as a [WindowTable] setting: two
      components, every window a single call ([lpc]), real-time order
      taken as "every call before every call" in the witness (implied by
      real time). *)
  Definition setting (cf : Blk -> DCat) (rc : bool) (K : TLCats) (X : Exec) : WT.Setting DCat := {|
    WT.Op := nat * nat;
    WT.Call := Ev;
    WT.OvOp := OvEv;
    WT.Comp := CompT;
    WT.comp_dec := comp_dec;
    WT.comp := fun q => if is_sl_op X q then CSL else CZ;
    WT.ovl := ovl X;
    WT.cF := fun q => match blk X q with Some k => cf k | None => DLocal end;
    WT.IFc := fun _ _ => False;
    WT.ucomp := fun e => match uobj (call e) with OZ => CZ | _ => CSL end;
    WT.cE := fun e => ucat K (call e);
    WT.IEc := fun u u' => upres rc K (call u) (call u') = false;
    WT.lo := lpc X;
    WT.hi := lpc X;
    WT.lpc := lpc X;
    WT.pos := fun e => idx e (wit X);
    WT.ops := all_ops X;
    WT.po := fun q q' => fst q = fst q' /\ snd q < snd q';
    WT.rt := fun q q' => forall k k' i i', blk X q = Some k -> blk X q' = Some k' ->
               i < length (calls k) -> i' < length (calls k') -> Pq X q i < Pq X q' i';
    WT.nuF := fun c => match c with CSL => nu_sl | CZ => nu_z end;
  |}.

  Lemma lpc_call X q k :
    blk X q = Some k ->
    call (lpc X q) = match k with BW _ _ => WmbC | BR _ _ _ _ => RmbC | BZw v => WrZ v | BZr v => RdZ v end.
  Proof.
    intros Hb. unfold lpc, lpi_of. rewrite Hb.
    assert (Hc : nth_error (calls k) (lpi k) =
                 Some match k with BW _ _ => WmbC | BR _ _ _ _ => RmbC | BZw v => WrZ v | BZr v => RdZ v end).
    { destruct k as [vx vy|fs s a b|v|v]; try reflexivity. apply read_call. reflexivity. }
    exact (proj1 (blk_evt X _ _ _ _ _ Hb Hc)).
  Qed.

  Section Composition.
    Context (rc : bool) (K : TLCats) (X : Exec).
    Hypothesis HW : WF rc K X.
    Hypothesis HK : K_ok K = true.

    Lemma IE_upres cf u u' :
      ~ WT.IE (dtable rc) (setting cf rc K X) u u' -> upres rc K (call u) (call u') = true.
    Proof.
      unfold WT.IE. cbn [WT.comp_dec WT.ucomp WT.IEc WT.cE setting].
      destruct (comp_dec _ _) as [E|NE]; intros H.
      - destruct (upres rc K (call u) (call u')) eqn:U; [reflexivity|]. exfalso. apply H. reflexivity.
      - unfold upres. destruct (dto rc (ucat K (call u)) (ucat K (call u'))) eqn:D; [apply orb_true_r|].
        exfalso. apply H. unfold dtable. rewrite D. discriminate.
    Qed.

    Lemma in_comp_CSL cf q : WT.in_comp (setting cf rc K X) CSL q = is_sl_op X q.
    Proof. unfold WT.in_comp. cbn. destruct (is_sl_op X q); reflexivity. Qed.

    Lemma in_comp_CZ cf q : WT.in_comp (setting cf rc K X) CZ q = negb (is_sl_op X q).
    Proof. unfold WT.in_comp. cbn. destruct (is_sl_op X q); reflexivity. Qed.

    Lemma ops_ths q : In q (all_ops X) -> In (fst q) (ths X).
    Proof. intros H. apply all_ops_In in H. tauto. Qed.

    (** [Hyps0] holds whatever overlay categories are claimed. *)
    Theorem setting_hyps0 cf : WT.Hyps0 (dtable rc) (setting cf rc K X).
    Proof.
      constructor.
      - exact (all_ops_nodup X (wf_ths _ _ _ HW)).
      - intros q q' Hq Hq'. exact (lp_inj rc K X HW q q' Hq Hq').
      - intros q Hq. cbn [setting WT.ucomp WT.lo WT.comp]. destruct (all_ops_blk X q Hq) as [k Hb].
        rewrite (lpc_call X q k Hb). unfold is_sl_op. rewrite Hb. destruct k; reflexivity.
      - intros q Hq. cbn [setting WT.ucomp WT.hi WT.comp]. destruct (all_ops_blk X q Hq) as [k Hb].
        rewrite (lpc_call X q k Hb). unfold is_sl_op. rewrite Hb. destruct k; reflexivity.
      - intros q Hq. unfold WT.lp. cbn. lia.
      - intros q q' Hq Hq' [Et Hlt] HnIE. cbn [setting WT.pos WT.hi WT.lo] in *.
        pose proof (IE_upres cf _ _ HnIE) as Hu.
        destruct (all_ops_blk X q Hq) as [k Hb]. destruct (all_ops_blk X q' Hq') as [k' Hb'].
        destruct (lpi_call X q k Hb) as [c Hc]. destruct (lpi_call X q' k' Hb') as [c' Hc'].
        assert (Ec : call (lpc X q) = c).
        { unfold lpc, lpi_of. rewrite Hb. exact (proj1 (blk_evt X _ _ _ _ _ Hb Hc)). }
        assert (Ec' : call (lpc X q') = c').
        { unfold lpc, lpi_of. rewrite Hb'. exact (proj1 (blk_evt X _ _ _ _ _ Hb' Hc')). }
        rewrite Ec, Ec' in Hu.
        change (lpq X q < lpq X q'). rewrite (lpq_Pq X q k Hb), (lpq_Pq X q' k' Hb').
        assert (Hb'' : nth_error (prog X (fst q)) (snd q') = Some k') by (rewrite Et; exact Hb').
        pose proof (Pq_after rc K X HW q k (snd q') k' _ _ c c' (ops_ths q Hq) Hb Hb'' Hc Hc' Hlt Hu) as H.
        destruct q' as [t' j']. cbn in Et, H |- *. subst t'. exact H.
      - intros q q' Hq Hq' Hrt. cbn [setting WT.rt WT.pos WT.hi WT.lo] in *.
        destruct (all_ops_blk X q Hq) as [k Hb]. destruct (all_ops_blk X q' Hq') as [k' Hb'].
        destruct (lpi_call X q k Hb) as [c Hc]. destruct (lpi_call X q' k' Hb') as [c' Hc'].
        change (lpq X q < lpq X q'). rewrite (lpq_Pq X q k Hb), (lpq_Pq X q' k' Hb').
        apply (Hrt k k'); try assumption; apply nth_error_Some; congruence.
      - intros [|].
        + cbn [setting WT.nuF WT.ovl WT.ops].
          change (WT.lp (setting cf rc K X)) with (lpq X).
          rewrite (filter_ext _ _ (in_comp_CSL cf)). exact (seqlock_S1 rc K X HW HK).
        + cbn [setting WT.nuF WT.ovl WT.ops].
          change (WT.lp (setting cf rc K X)) with (lpq X).
          rewrite (filter_ext _ _ (in_comp_CZ cf)). exact (z_S1 rc K X HW).
      - intros q q' Hq Hq' Ecomp [Et Hlt] _. cbn [setting WT.comp] in Ecomp.
        change (lpq X q < lpq X q').
        destruct (is_sl_op X q) eqn:Sq, (is_sl_op X q') eqn:Sq'; try discriminate.
        + apply (seqlock_S1_ord rc K X HW HK); try assumption;
            unfold sl_ops; apply filter_In; split; assumption.
        + apply (z_S1_ord rc K X HW); try assumption.
          * unfold z_ops. apply filter_In. split; [assumption|]. rewrite Sq. reflexivity.
          * unfold z_ops. apply filter_In. split; [assumption|]. rewrite Sq'. reflexivity.
    Qed.

    (** Inheritance: every overlay operation exports the category of its
        own window call. *)
    Theorem setting_inherit : WT.Inherit (dtable rc) (setting sl_cf rc K X).
    Proof.
      split; intros q Hq; cbn [setting WT.cF WT.cE WT.hi WT.lo];
        destruct (all_ops_blk X q Hq) as [k Hb]; rewrite Hb, (lpc_call X q k Hb).
      - destruct k; apply out_le_refl.
      - destruct k; apply in_le_refl.
    Qed.

    (** The tensor SeqLock ⊗ COH[z], with read ↦ rmb and write ↦ wmb, is
        relaxed linearizable on every such execution. *)
    Theorem seqlock_z_composition : WT.Conclusion (dtable rc) (setting sl_cf rc K X).
    Proof. exact (WT.window_composition _ _ (setting_hyps0 sl_cf) setting_inherit). Qed.
  End Composition.

  (** ** Deciding [WF] on concrete executions *)

  Definition Ev_eqb (a b : Ev) : bool := if Ev_eq_dec a b then true else false.
  Definition UC_eqb (a b : UC) : bool := if UC_eq_dec a b then true else false.

  Lemma Ev_eqb_eq a b : Ev_eqb a b = true -> a = b.
  Proof. unfold Ev_eqb. destruct (Ev_eq_dec a b); congruence. Qed.

  Fixpoint nodupb {A} (eqb : A -> A -> bool) (l : list A) : bool :=
    match l with
    | [] => true
    | x :: l' => negb (existsb (eqb x) l') && nodupb eqb l'
    end.

  Lemma nodupb_spec {A} (eqb : A -> A -> bool) (Heq : forall a b, eqb a b = true -> a = b) l :
    (forall a, eqb a a = true) -> nodupb eqb l = true -> NoDup l.
  Proof.
    intros Hrefl. induction l as [|x l IH]; cbn; intros H; [constructor|].
    apply andb_true_iff in H as [H1 H2]. constructor; [|apply IH, H2].
    intros Hin. apply negb_true_iff in H1. assert (existsb (eqb x) l = true) by (apply existsb_exists; eauto).
    congruence.
  Qed.

  Definition optUC_eqb (a b : option UC) : bool :=
    match a, b with Some x, Some y => UC_eqb x y | None, None => true | _, _ => false end.

  Definition wfb (rc : bool) (K : TLCats) (X : Exec) : bool :=
    nodupb Ev_eqb (wit X) && nodupb Nat.eqb (ths X)
    && forallb (fun e => existsb (Nat.eqb (th e)) (ths X)
                         && optUC_eqb (nth_error (trace (prog X (th e))) (ix e)) (Some (call e))) (wit X)
    && forallb (fun t => forallb (fun i => existsb (Ev_eqb (evt X t i)) (wit X))
                                 (seq 0 (length (trace (prog X t))))) (ths X)
    && forallb (fun e1 => forallb (fun e2 =>
          implb (Nat.eqb (th e1) (th e2) && Nat.ltb (ix e1) (ix e2) && upres rc K (call e1) (call e2))
                (Nat.ltb (idx e1 (wit X)) (idx e2 (wit X)))) (wit X)) (wit X)
    && forallb (fun p => match nth_error (wit X) p with Some e => pre (at_ X p) e | None => true end)
               (seq 0 (length (wit X))).

  Lemma wfb_sound rc K X : wfb rc K X = true -> WF rc K X.
  Proof.
    unfold wfb. intros H.
    apply andb_true_iff in H as [H Hval]. apply andb_true_iff in H as [H Hpres].
    apply andb_true_iff in H as [H Hcomp]. apply andb_true_iff in H as [H Hcall].
    apply andb_true_iff in H as [Hnd Hth].
    constructor.
    - apply (nodupb_spec Ev_eqb Ev_eqb_eq); [|exact Hnd].
      intros a. unfold Ev_eqb. destruct (Ev_eq_dec a a); congruence.
    - apply (nodupb_spec Nat.eqb (fun a b => proj1 (Nat.eqb_eq a b))); [|exact Hth].
      intros a. apply Nat.eqb_refl.
    - intros e He. rewrite forallb_forall in Hcall. specialize (Hcall e He).
      apply andb_true_iff in Hcall as [H1 H2]. split.
      + apply existsb_exists in H1 as (t & Ht & E). apply Nat.eqb_eq in E. congruence.
      + destruct (nth_error (trace (prog X (th e))) (ix e)); cbn in H2; [|discriminate].
        unfold UC_eqb in H2. destruct (UC_eq_dec u (call e)); congruence.
    - intros t i Ht Hi. rewrite forallb_forall in Hcomp. specialize (Hcomp t Ht).
      rewrite forallb_forall in Hcomp. specialize (Hcomp i ltac:(apply in_seq; lia)).
      apply existsb_exists in Hcomp as (e & He & E). apply Ev_eqb_eq in E. congruence.
    - intros e1 e2 He1 He2 Et Hi Hu. rewrite forallb_forall in Hpres. specialize (Hpres e1 He1).
      rewrite forallb_forall in Hpres. specialize (Hpres e2 He2).
      rewrite Et, Nat.eqb_refl, Hu in Hpres. apply Nat.ltb_lt in Hi. rewrite Hi in Hpres.
      cbn in Hpres. apply Nat.ltb_lt, Hpres.
    - intros p e Hn. rewrite forallb_forall in Hval.
      assert (Hp : In p (seq 0 (length (wit X)))) by (apply in_seq; split; [lia|]; apply nth_error_Some; congruence).
      specialize (Hval p Hp). rewrite Hn in Hval. exact Hval.
  Qed.

  (** ** Part D: clients *)

  Definition mkX (p0 p1 : list Blk) (w : list Ev) : Exec :=
    {| ths := [0; 1]; prog := fun t => match t with 0 => p0 | _ => p1 end; wit := w |}.

  Lemma before_cycle {A} (l : list A) a b c d :
    NoDup l -> WC.before l a b -> WC.before l b c -> WC.before l c d -> WC.before l d a -> False.
  Proof.
    intros Hnd H1 H2 H3 H4.
    apply WC.before_to_i in H1, H2, H3, H4.
    pose proof (WC.before_i_trans l a b c Hnd H1 H2) as H.
    pose proof (WC.before_i_trans l a c d Hnd H H3) as H'.
    exact (WC.before_i_irrefl l a Hnd (WC.before_i_trans l a d a Hnd H' H4)).
  Qed.

  (** In a component with two operations, the specification fixes their
      order. *)
  Lemma two_order {A B} (ov : A -> B) (nu : list B -> Prop) (f : A -> bool) ow a b :
    Permutation (filter f ow) [a; b] -> nu (map ov (filter f ow)) -> ~ nu [ov b; ov a] ->
    WC.before ow a b.
  Proof.
    intros Hp Hnu Hbad. apply Permutation_sym, Permutation_length_2_inv in Hp as [E|E];
      rewrite E in Hnu; [|contradiction].
    apply (WC.before_filter f). rewrite E. exists [], [b]. split; [reflexivity|left; reflexivity].
  Qed.

  (** Same-thread order the overlay specification keeps. *)
  Lemma kept rc cf K X q q' ow :
    (forall q q', In q (WT.ops (setting cf rc K X)) -> In q' (WT.ops (setting cf rc K X)) ->
       (WT.po (setting cf rc K X) q q' /\ ~ WT.IF (dtable rc) (setting cf rc K X) q q') \/
       WT.rt (setting cf rc K X) q q' ->
       exists l1 l2, ow = l1 ++ q :: l2 /\ In q' l2) ->
    In q (all_ops X) -> In q' (all_ops X) -> fst q = fst q' -> snd q < snd q' ->
    ~ WT.IF (dtable rc) (setting cf rc K X) q q' -> WC.before ow q q'.
  Proof. intros Hord Hq Hq' Et Hlt HnIF. apply Hord; [exact Hq|exact Hq'|]. left. split; [split|]; assumption. Qed.

  (** MP through the SeqLock: [z := 1; write(1,1) ‖ read() = (1,1); z = 0].
      Forbidden for every witness, every number of retries and every
      ticket, using only the overlay specification [seqlock_z_composition]. *)
  Theorem mp_forbidden rc K fs s w :
    K_ok K = true -> ~ WF rc K (mkX [BZw 1; BW 1 1] [BR fs s 1 1; BZr 0] w).
  Proof.
    intros HK HW.
    destruct (seqlock_z_composition rc K _ HW HK) as (ow & Hp & Hord & Hspec).
    set (X := mkX [BZw 1; BW 1 1] [BR fs s 1 1; BZr 0] w) in *.
    assert (Hops : all_ops X = [(0, 0); (0, 1); (1, 0); (1, 1)]) by reflexivity.
    assert (Hnd : NoDup ow).
    { apply (Permutation_NoDup (Permutation_sym Hp)). cbn [setting WT.ops]. rewrite Hops.
      repeat constructor; cbn; intuition congruence. }
    assert (In0 : forall q, In q [(0, 0); (0, 1); (1, 0); (1, 1)] -> In q (all_ops X))
      by (intros q Hq; rewrite Hops; exact Hq).
    assert (B1 : WC.before ow (0, 0) (0, 1)).
    { apply (kept rc sl_cf K X _ _ ow Hord); try (apply In0; cbn; tauto); try reflexivity; try (cbn; lia).
      unfold WT.IF. cbn. intros H. apply H. unfold dtable. destruct rc; reflexivity. }
    assert (B3 : WC.before ow (1, 0) (1, 1)).
    { apply (kept rc sl_cf K X _ _ ow Hord); try (apply In0; cbn; tauto); try reflexivity; try (cbn; lia).
      unfold WT.IF. cbn. intros H. apply H. unfold dtable. destruct rc; reflexivity. }
    assert (B2 : WC.before ow (0, 1) (1, 0)).
    { apply (two_order (ovl X) nu_sl (WT.in_comp (setting sl_cf rc K X) CSL) ow).
      - apply (Permutation_trans (WC.perm_filter _ _ _ Hp)). cbn [setting WT.ops]. rewrite Hops. reflexivity.
      - exact (Hspec CSL).
      - cbn. intros [E _]. discriminate. }
    assert (B4 : WC.before ow (1, 1) (0, 0)).
    { apply (two_order (ovl X) nu_z (WT.in_comp (setting sl_cf rc K X) CZ) ow).
      - apply (Permutation_trans (WC.perm_filter _ _ _ Hp)). cbn [setting WT.ops]. rewrite Hops. apply perm_swap.
      - exact (Hspec CZ).
      - cbn. intros [E _]. discriminate. }
    exact (before_cycle ow _ _ _ _ Hnd B1 B2 B3 B4).
  Qed.

  (** LB through the SeqLock: [z = 1; write(1,1) ‖ read() = (1,1); z := 1].
      A concrete complete execution produces it. *)
  Definition lb_wit : list Ev :=
    [ mkEv 0 1 Acq; mkEv 0 2 WmbC; mkEv 0 3 (WrX 1); mkEv 0 4 (WrY 1); mkEv 0 5 WmbC; mkEv 0 6 Rel;
      mkEv 1 0 (GT 2); mkEv 1 1 RmbC; mkEv 1 2 (RdX 1); mkEv 1 3 (RdY 1); mkEv 1 4 RmbC;
      mkEv 1 5 (TT 2 false); mkEv 1 6 (WrZ 1);
      mkEv 0 0 (RdZ 1) ].

  Definition X_lb : Exec := mkX [BZr 1; BW 1 1] [BR [] 2 1 1; BZw 1] lb_wit.

  Lemma lb_wf rc : WF rc plainTL X_lb.
  Proof. apply wfb_sound. destruct rc; vm_compute; reflexivity. Qed.

  (** Non-vacuity with retries and reordering inside blocks: the writer
      writes [y] before [x], the reader's failed iteration reads a torn
      (0, 1) and its reads are performed [y] first. *)
  Definition retry_wit : list Ev :=
    [ mkEv 1 0 (GT 0);
      mkEv 0 0 Acq; mkEv 0 1 WmbC; mkEv 0 3 (WrY 1);
      mkEv 1 1 RmbC; mkEv 1 3 (RdY 1); mkEv 1 2 (RdX 0); mkEv 1 4 RmbC; mkEv 1 5 (TT 0 true);
      mkEv 0 2 (WrX 1); mkEv 0 4 WmbC; mkEv 0 5 Rel;
      mkEv 1 6 (GT 2); mkEv 1 7 RmbC; mkEv 1 9 (RdY 1); mkEv 1 8 (RdX 1); mkEv 1 10 RmbC;
      mkEv 1 11 (TT 2 false) ].

  Definition X_retry : Exec := mkX [BW 1 1] [BR [(0, 0, 1)] 2 1 1] retry_wit.

  Lemma retry_wf rc : WF rc plainTL X_retry.
  Proof. apply wfb_sound. destruct rc; vm_compute; reflexivity. Qed.

  (** The proposed signature accepts it. *)
  Corollary lb_allowed rc : WT.Conclusion (dtable rc) (setting sl_cf rc plainTL X_lb).
  Proof. exact (seqlock_z_composition rc plainTL X_lb (lb_wf rc) plainTL_ok). Qed.

  (** Any signature that orders a client read before a later SeqLock
      write, and a SeqLock read before a later client write, excludes this
      execution: it has no [Conclusion], although [Hyps0] holds. *)
  Theorem lb_refutes rc cf :
    dto rc (cf (BZr 1)) (cf (BW 1 1)) = true -> dto rc (cf (BR [] 2 1 1)) (cf (BZw 1)) = true ->
    WT.Hyps0 (dtable rc) (setting cf rc plainTL X_lb) /\
    ~ WT.Conclusion (dtable rc) (setting cf rc plainTL X_lb).
  Proof.
    intros D1 D2. set (X := X_lb). set (S := setting cf rc plainTL X).
    assert (Hops : all_ops X = [(0, 0); (0, 1); (1, 0); (1, 1)]) by reflexivity.
    split; [exact (setting_hyps0 rc plainTL X (lb_wf rc) plainTL_ok cf)|].
    intros (ow & Hp & Hord & Hspec).
    assert (Hnd : NoDup ow).
    { apply (Permutation_NoDup (Permutation_sym Hp)). cbn [S setting WT.ops]. rewrite Hops.
      repeat constructor; cbn; intuition congruence. }
    assert (In0 : forall q, In q [(0, 0); (0, 1); (1, 0); (1, 1)] -> In q (all_ops X))
      by (intros q Hq; rewrite Hops; exact Hq).
    assert (B1 : WC.before ow (0, 0) (0, 1)).
    { apply (kept rc cf plainTL X _ _ ow Hord); try (apply In0; cbn; tauto); try reflexivity; try (cbn; lia).
      unfold WT.IF. cbn. intros H. apply H. exact D1. }
    assert (B3 : WC.before ow (1, 0) (1, 1)).
    { apply (kept rc cf plainTL X _ _ ow Hord); try (apply In0; cbn; tauto); try reflexivity; try (cbn; lia).
      unfold WT.IF. cbn. intros H. apply H. exact D2. }
    assert (B2 : WC.before ow (0, 1) (1, 0)).
    { apply (two_order (ovl X) nu_sl (WT.in_comp S CSL) ow).
      - apply (Permutation_trans (WC.perm_filter _ _ _ Hp)). cbn [S setting WT.ops]. rewrite Hops. reflexivity.
      - exact (Hspec CSL).
      - cbn. intros [E _]. discriminate. }
    assert (B4 : WC.before ow (1, 1) (0, 0)).
    { apply (two_order (ovl X) nu_z (WT.in_comp S CZ) ow).
      - apply (Permutation_trans (WC.perm_filter _ _ _ Hp)). cbn [S setting WT.ops]. rewrite Hops. apply perm_swap.
      - exact (Hspec CZ).
      - cbn. intros [E _]. discriminate. }
    exact (before_cycle ow _ _ _ _ Hnd B1 B2 B3 B4).
  Qed.

  (** The paper's signature: all hypotheses but inheritance hold, and the
      conclusion fails.  The signature is refuted, not only unprovable. *)
  Theorem paper_signature_fails rc :
    WT.Hyps0 (dtable rc) (setting paper_cf rc plainTL X_lb) /\
    ~ WT.Inherit (dtable rc) (setting paper_cf rc plainTL X_lb) /\
    ~ WT.Conclusion (dtable rc) (setting paper_cf rc plainTL X_lb).
  Proof.
    destruct (lb_refutes rc paper_cf ltac:(destruct rc; reflexivity) ltac:(destruct rc; reflexivity))
      as [H0 Hc].
    split; [exact H0|]. split; [|exact Hc].
    intros [Ho _]. specialize (Ho (1, 0)). cbn [setting WT.cF WT.cE WT.hi WT.ops] in Ho.
    specialize (Ho ltac:(cbn; tauto)).
    cbn in Ho. apply (proj1 (proj2 (paper_signature_not_inheritable rc))). exact Ho.
  Qed.

  (** The same with the kind-less modes [rfence]/[lfence] of the four-mode
      lattice. *)
  Definition paper_cf_modes (k : Blk) : DCat :=
    match k with BW _ _ => emb LFence | BR _ _ _ _ => emb RFence | BZw _ => DW | BZr _ => DR end.

  Corollary paper_modes_fail rc : ~ WT.Conclusion (dtable rc) (setting paper_cf_modes rc plainTL X_lb).
  Proof. apply (lb_refutes rc paper_cf_modes); destruct rc; reflexivity. Qed.

  (** The proposed signature does not order these pairs (and accepts the
      execution, [lb_allowed]). *)
  Lemma sl_cf_unordered rc :
    dto rc (sl_cf (BZr 1)) (sl_cf (BW 1 1)) = false /\ dto rc (sl_cf (BR [] 2 1 1)) (sl_cf (BZw 1)) = false.
  Proof. destruct rc; split; reflexivity. Qed.

  (** ** Part E: selective barriers do not order a TicketLock exporting [Local] *)

  (** Under the four fence modes a plain counter call can only export
      [Local] (Part A).  Selective barriers ([Rmb], [Wmb]) do not order
      [Local] calls, so the writer's first barrier and [x := 1] can be
      performed before its [acq], and the reader's [get_ticket] and
      [test_ticket] are not ordered with its barriers: the read returns
      (1, 0).  (Full barriers would order [Local] calls; the SeqLock then
      exports [fence] and hides everything.) *)
  Definition torn_wit : list Ev :=
    [ mkEv 0 1 WmbC; mkEv 0 2 (WrX 1);
      mkEv 1 0 (GT 0); mkEv 1 1 RmbC; mkEv 1 2 (RdX 1); mkEv 1 3 (RdY 0); mkEv 1 4 RmbC;
      mkEv 1 5 (TT 0 false);
      mkEv 0 0 Acq; mkEv 0 3 (WrY 1); mkEv 0 4 WmbC; mkEv 0 5 Rel ].

  Definition torn_p0 : list Blk := [BW 1 1].
  Definition torn_p1 : list Blk := [BR [] 0 1 0].
  Definition X_torn : Exec := mkX torn_p0 torn_p1 torn_wit.

  (** Whatever the number of retries and the ticket, a read returning
      (1, 0) has no linearization: the only writes are (1, 1). *)
  Lemma torn_no_linearization X fs s :
    prog X 0 = torn_p0 -> prog X 1 = [BR fs s 1 0] -> ths X = [0; 1] ->
    forall l, Permutation l (sl_ops X) -> ~ nu_sl (map (ovl X) l).
  Proof.
    intros H0 H1 Ht l Hp.
    assert (Hs : sl_ops X = [(0, 0); (1, 0)]).
    { unfold sl_ops, all_ops. rewrite Ht. cbn [flat_map]. rewrite H0, H1.
      cbn [length seq map app filter torn_p0]. unfold is_sl_op, blk. cbn [fst snd].
      rewrite H0, H1. reflexivity. }
    rewrite Hs in Hp. apply Permutation_sym, Permutation_length_2_inv in Hp as [->| ->];
      unfold ovl, blk; cbn; rewrite H0, H1; cbn; intros [E _]; discriminate.
  Qed.

  Theorem torn_with_local_tl rc :
    WF rc localTL X_torn /\ forall l, Permutation l (sl_ops X_torn) -> ~ nu_sl (map (ovl X_torn) l).
  Proof.
    split.
    - apply wfb_sound. destruct rc; vm_compute; reflexivity.
    - apply (torn_no_linearization X_torn [] 0); reflexivity.
  Qed.

  (** With the plain categories no witness at all, with any number of
      retries and any ticket, produces the torn read. *)
  Corollary torn_impossible_with_plain_tl rc fs s w : ~ WF rc plainTL (mkX torn_p0 [BR fs s 1 0] w).
  Proof.
    intros HW. pose proof (seqlock_S1 rc plainTL _ HW plainTL_ok) as H.
    exact (torn_no_linearization (mkX torn_p0 [BR fs s 1 0] w) fs s eq_refl eq_refl eq_refl _
             (WC.isort_perm _ _) H).
  Qed.
End SeqLockCOH.
