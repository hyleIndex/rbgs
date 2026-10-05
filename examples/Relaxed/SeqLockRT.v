(** * SeqLock ⊗ COH[z]: explicit real time and incomplete executions

    Extends the witness-level development of [SeqLockCOH] (unchanged) in
    two directions.

    - Part 1: real time.  [SeqLockCOH.setting] takes as overlay real-time
      order "every call of [q] precedes every call of [q'] in the
      witness", so [h_rt] holds by definition and the claim that the
      witness respects real time is built into the setting.  Here a
      [Timing] gives invocation and response times to overlay operations
      and to underlay calls ([None]: no response yet), and [RT_ok] states
      the only links needed between them:
      - a call is invoked after its operation ([rt_inv]);
      - an operation that has responded at [r] has every call in the
        witness responded by [r] ([rt_res]);
      - a call responds after it is invoked ([rt_call]);
      - the witness extends the real-time order of calls: the underlay is
        linearizable in the usual sense ([rt_wit]).
      The overlay order is the standard one, [rt_of]: [q] responded
      before [q'] was invoked.  [seqlock_z_composition_rt] gives the
      [WindowTable] conclusion for it.  Every field of [Hyps0] but [h_rt]
      is that of [SeqLockCOH.setting]; [h_rt] holds at the window call,
      which is one of the operation's own calls ([rt_lp]).  Nothing is
      assumed of overlay intervals alone (invocation before response,
      same-thread invocations in program order): the proof does not use
      it, and a thread may invoke an operation before its previous one
      returns.  Conservativity: every complete execution has a timing
      [canon] with [RT_ok] whose real-time order is exactly the witness
      order of [SeqLockCOH.setting] ([canon_ok], [canon_rt]).

    - Part 2: incomplete executions.  An incomplete execution is an
      [Exec] with a set [pend] of pending operations, meant to be the
      operations without a response ([incomplete_seqlock_z_rt] requires
      exactly that of the timing).  Its witness lists the underlay calls
      that the completion keeps, called present: those that have
      responded and those completed by an appended response; the others
      are not yet emitted, or are pending invocations that the completion
      drops.  [WF_inc] is [WF] with completeness asked of completed
      operations only, plus closure ([wfi_closed]): if a call is present,
      so is every earlier call of its thread, across operations, that has
      a preserved edge to it.

      The justification is the append/drop completion of relaxed
      linearizability (Def. 5.3, [s ⋅ s_P ⇝rhb s' ⋅ s_O]): a dropped
      pending invocation goes to [s_O], so it must commute to the end of
      the trace, and within a thread [⇝E] lets an invocation pass a later
      one only when the two are semi-independent; the pairs that are not
      semi-independent are exactly the preserved ones ([upres]).  So a
      pending call followed, in its thread's call order, by a present call
      that is not semi-independent of it cannot be dropped (the Step rule
      of the module semantics only orders the emission of the two,
      earlier first; it does not say which calls a completion may drop).
      [RelaxedTraceLin] formalizes complete traces only, so this is a
      modelling assumption, not linked to the trace semantics in Rocq.
      It is needed: without it a write could have [x := v] absent and
      [rel] present, and a read after the [rel] would return a torn pair
      that no completion explains.  For a complete execution it follows
      from completeness ([WF_WF_inc], [WF_inc_WF]); [wfi_pres] orders
      present calls only and says nothing about absent ones.

      The completion uses closure four times:
      - a pending write with no [acq] present has no call present: every
        call of a write reaches its [acq] by preserved edges
        ([acq_needed]);
      - a pending write with [rel] present has every call present
        ([rel_all]);
      - a write with [acq] present and [rel] absent (open) holds the lock
        to the end, since a later [rel] of its thread would need its own
        ([held_forever]); hence there is at most one ([open_unique]);
      - no present call has a preserved edge from an absent call of the
        open write, so these can be appended at the end ([L_pres]).
      [completion] drops pending reads and pending z-reads (their calls do
      not change the state), and pending writes and z-writes with no call
      present; it completes the open write by appending its absent calls
      in program order, and keeps as completed the pending writes with
      every call present and the pending z-writes whose call is present.
      It is a complete execution ([completion_wf]), and its operations map
      injectively into those of the incomplete one, preserving thread,
      program order and block (so overlay label), and covering every
      completed operation ([Psi_ok], [complete_execution]).  Headline
      theorems: [incomplete_seqlock_z_rt], with [pend] the operations
      without response and the real-time order of the incomplete
      execution transported along the map (appended calls never respond),
      and its instance [incomplete_seqlock_z_timed] with [pend] read off
      the timing; [incomplete_seqlock_z], without timing.  [X_inc] is a concrete
      instance: a writer holding the lock followed, in its thread, by a
      completed z-read; a completed read; and a pending read that saw a
      torn state.

    Scope: as in [SeqLockCOH], everything is at the level of underlay
    witnesses. *)

From Stdlib Require Import List Bool Arith.PeanoNat micromega.Lia.
From Stdlib Require Import Sorting.Sorted Sorting.Permutation.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.
Require Import examples.Relaxed.SeqLockCOH.

Import ListNotations.

Module SeqLockRT.
  Module WC := WindowComposition.
  Module WT := WindowTable.
  Import WT.
  Import RelaxedSig.
  Import SeqLockCOH.

  (** The [i]-th call of block [j] of thread [t]. *)
  Definition ce (X : Exec) (t j i : nat) : Ev := evt X t (off (prog X t) j + i).

  Lemma ce_call X t j k i c :
    nth_error (prog X t) j = Some k -> nth_error (calls k) i = Some c -> call (ce X t j i) = c.
  Proof. intros Hj Hi. exact (proj1 (blk_evt X t j k i c Hj Hi)). Qed.

  (** ** Part 1: real time *)

  (** Invocation and response times of overlay operations and underlay
      calls; [None] is "no response yet". *)
  Record Timing : Type := {
    oinv : nat * nat -> nat;
    ores : nat * nat -> option nat;
    cinv : Ev -> nat;
    cres : Ev -> option nat;
  }.

  Record RT_ok (X : Exec) (T : Timing) : Prop := {
    (** a call is invoked after its operation *)
    rt_inv : forall q k i, blk X q = Some k -> i < length (calls k) ->
               In (ce X (fst q) (snd q) i) (wit X) ->
               oinv T q <= cinv T (ce X (fst q) (snd q) i);
    (** an operation responds after its calls in the witness have responded *)
    rt_res : forall q k i r, blk X q = Some k -> i < length (calls k) ->
               In (ce X (fst q) (snd q) i) (wit X) -> ores T q = Some r ->
               exists r', cres T (ce X (fst q) (snd q) i) = Some r' /\ r' <= r;
    (** a call responds after its invocation *)
    rt_call : forall e r, In e (wit X) -> cres T e = Some r -> cinv T e <= r;
    (** the witness extends the real-time order of underlay calls *)
    rt_wit : forall e e' r, In e (wit X) -> In e' (wit X) -> cres T e = Some r -> r < cinv T e' ->
               idx e (wit X) < idx e' (wit X);
  }.

  (** The standard overlay real-time order. *)
  Definition rt_of (T : Timing) (q q' : nat * nat) : Prop :=
    exists r, ores T q = Some r /\ r < oinv T q'.

  (** [SeqLockCOH.setting] with the real-time order of a timing. *)
  Definition setting_rt (cf : Blk -> DCat) (rc : bool) (K : TLCats) (X : Exec) (T : Timing)
    : WT.Setting DCat := {|
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
    WT.rt := rt_of T;
    WT.nuF := fun c => match c with CSL => nu_sl | CZ => nu_z end;
  |}.

  Section RT.
    Context (rc : bool) (K : TLCats) (X : Exec) (T : Timing).
    Hypothesis HW : WF rc K X.
    Hypothesis HK : K_ok K = true.
    Hypothesis HT : RT_ok X T.

    (** The window call is one of the operation's calls, and is in the
        witness. *)
    Lemma lpc_ce q k : blk X q = Some k -> lpc X q = ce X (fst q) (snd q) (lpi k).
    Proof. intros Hb. unfold lpc, lpi_of, ce. rewrite Hb. reflexivity. Qed.

    Lemma lpc_in q k :
      In (fst q) (ths X) -> blk X q = Some k -> In (lpc X q) (wit X) /\ lpi k < length (calls k).
    Proof.
      intros Ht Hb. destruct (lpi_call X q k Hb) as [c Hc].
      split; [|apply nth_error_Some; congruence].
      rewrite (lpc_ce q k Hb). apply (wf_complete _ _ _ HW); [exact Ht|].
      exact (proj2 (blk_evt X _ _ _ _ _ Hb Hc)).
    Qed.

    (** Real-time order is respected at the window calls. *)
    Lemma rt_lp q q' : In q (all_ops X) -> In q' (all_ops X) -> rt_of T q q' -> lpq X q < lpq X q'.
    Proof.
      intros Hq Hq' (r & Hr & Hlt).
      destruct (all_ops_blk X q Hq) as [k Hb]. destruct (all_ops_blk X q' Hq') as [k' Hb'].
      destruct (lpc_in q k (ops_ths X q Hq) Hb) as [Hin Hl].
      destruct (lpc_in q' k' (ops_ths X q' Hq') Hb') as [Hin' Hl'].
      unfold lpq. rewrite (lpc_ce q k Hb) in Hin |- *. rewrite (lpc_ce q' k' Hb') in Hin' |- *.
      destruct (rt_res _ _ HT q k (lpi k) r Hb Hl Hin Hr) as (r' & Hr' & Hle).
      pose proof (rt_inv _ _ HT q' k' (lpi k') Hb' Hl' Hin') as Hinv.
      apply (rt_wit _ _ HT _ _ r' Hin Hin' Hr'). lia.
    Qed.

    (** Every field but [h_rt] is that of [SeqLockCOH.setting]. *)
    Theorem setting_rt_hyps0 cf : WT.Hyps0 (dtable rc) (setting_rt cf rc K X T).
    Proof.
      destruct (setting_hyps0 rc K X HW HK cf) as [H1 H2 H3 H4 H5 H6 _ H8 H9].
      constructor; [exact H1|exact H2|exact H3|exact H4|exact H5|exact H6| |exact H8|exact H9].
      exact rt_lp.
    Qed.

    Theorem setting_rt_inherit : WT.Inherit (dtable rc) (setting_rt sl_cf rc K X T).
    Proof. exact (setting_inherit rc K X). Qed.

    (** SeqLock ⊗ COH[z], read ↦ rmb, write ↦ wmb, with the standard
        real-time order. *)
    Theorem seqlock_z_composition_rt : WT.Conclusion (dtable rc) (setting_rt sl_cf rc K X T).
    Proof. exact (WT.window_composition _ _ (setting_rt_hyps0 sl_cf) setting_rt_inherit). Qed.
  End RT.

  (** *** Conservativity

      Every complete execution has a timing satisfying [RT_ok]: each call
      is the point interval [[2p, 2p+1]] at its witness position [p], each
      operation spans from its first to its last call.  Its real-time
      order is exactly the witness order of [SeqLockCOH.setting], so
      [seqlock_z_composition] is the instance [canon] of
      [seqlock_z_composition_rt]. *)

  Definition ncalls (X : Exec) (q : nat * nat) : nat :=
    match blk X q with Some k => length (calls k) | None => 0 end.

  Definition cpos (X : Exec) (q : nat * nat) : list nat :=
    map (fun i => idx (ce X (fst q) (snd q) i) (wit X)) (seq 0 (ncalls X q)).

  Definition canon (X : Exec) : Timing := {|
    oinv := fun q => 2 * fold_right Nat.min (length (wit X)) (cpos X q);
    ores := fun q => Some (S (2 * list_max (cpos X q)));
    cinv := fun e => 2 * idx e (wit X);
    cres := fun e => Some (S (2 * idx e (wit X)));
  |}.

  Lemma fold_min_le d l x : In x l -> fold_right Nat.min d l <= x.
  Proof.
    induction l as [|y l IH]; cbn; [contradiction|].
    intros [->|H]; [lia|]. specialize (IH H). lia.
  Qed.

  Lemma lt_fold_min n d l : n < d -> (forall x, In x l -> n < x) -> n < fold_right Nat.min d l.
  Proof.
    induction l as [|y l IH]; cbn; intros Hd Hl; [exact Hd|].
    specialize (IH Hd (fun x Hx => Hl x (or_intror Hx))). specialize (Hl y (or_introl eq_refl)). lia.
  Qed.

  Lemma le_list_max x l : In x l -> x <= list_max l.
  Proof.
    intros H. assert (Hf : Forall (fun k => k <= list_max l) l) by (apply list_max_le; lia).
    rewrite Forall_forall in Hf. exact (Hf x H).
  Qed.

  Lemma calls_nonempty k : 0 < length (calls k).
  Proof. destruct k; cbn; try lia. rewrite length_app. cbn. lia. Qed.

  Lemma cpos_In X q k i : blk X q = Some k -> i < length (calls k) ->
    In (idx (ce X (fst q) (snd q) i) (wit X)) (cpos X q).
  Proof.
    intros Hb Hi. unfold cpos, ncalls. rewrite Hb. apply in_map_iff. exists i.
    split; [reflexivity|]. apply in_seq. lia.
  Qed.

  Lemma cpos_inv X q y : In y (cpos X q) ->
    exists k i, blk X q = Some k /\ i < length (calls k) /\ y = idx (ce X (fst q) (snd q) i) (wit X).
  Proof.
    unfold cpos, ncalls. destruct (blk X q) as [k|]; intros H; [|contradiction].
    apply in_map_iff in H as (i & <- & Hi). apply in_seq in Hi. exists k, i.
    split; [reflexivity|]. split; [lia|reflexivity].
  Qed.

  Section Canon.
    Context (rc : bool) (K : TLCats) (X : Exec).
    Hypothesis HW : WF rc K X.

    Lemma ce_in q k i : In (fst q) (ths X) -> blk X q = Some k -> i < length (calls k) ->
      In (ce X (fst q) (snd q) i) (wit X).
    Proof.
      intros Ht Hb Hi. destruct (nth_error (calls k) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
      apply (wf_complete _ _ _ HW); [exact Ht|]. exact (proj2 (blk_evt X _ _ _ _ _ Hb Hc)).
    Qed.

    Theorem canon_ok : RT_ok X (canon X).
    Proof.
      constructor; cbn [oinv ores cinv cres canon].
      - intros q k i Hb Hi _. pose proof (fold_min_le (length (wit X)) _ _ (cpos_In X q k i Hb Hi)). lia.
      - intros q k i r Hb Hi _ Hr. injection Hr as <-. eexists. split; [reflexivity|].
        pose proof (le_list_max _ _ (cpos_In X q k i Hb Hi)). lia.
      - intros e r _ Hr. injection Hr as <-. lia.
      - intros e e' r _ _ Hr Hlt. injection Hr as <-. lia.
    Qed.

    Theorem canon_rt cf q q' : In q (all_ops X) -> In q' (all_ops X) ->
      WT.rt (setting cf rc K X) q q' <-> rt_of (canon X) q q'.
    Proof.
      intros Hq Hq'. cbn [WT.rt setting]. unfold rt_of. cbn [oinv ores canon].
      destruct (all_ops_blk X q Hq) as [k Hb]. destruct (all_ops_blk X q' Hq') as [k' Hb'].
      assert (Hne : cpos X q <> []).
      { intros E. pose proof (cpos_In X q k 0 Hb (calls_nonempty k)) as H. rewrite E in H. exact H. }
      split.
      - intros Hrt. eexists. split; [reflexivity|].
        enough (list_max (cpos X q) < fold_right Nat.min (length (wit X)) (cpos X q')) by lia.
        apply lt_fold_min.
        + apply list_max_lt; [exact Hne|]. apply Forall_forall. intros y Hy.
          destruct (cpos_inv X q y Hy) as (k0 & i & Hb0 & Hi & ->).
          apply idx_lt, (ce_in q k0 i (ops_ths X q Hq) Hb0 Hi).
        + intros x Hx. destruct (cpos_inv X q' x Hx) as (k1 & i' & Hb1 & Hi' & ->).
          apply list_max_lt; [exact Hne|]. apply Forall_forall. intros y Hy.
          destruct (cpos_inv X q y Hy) as (k0 & i & Hb0 & Hi & ->).
          exact (Hrt k0 k1 i i' Hb0 Hb1 Hi Hi').
      - intros (r & Hr & Hlt) k0 k1 i i' Hb0 Hb1 Hi Hi'. injection Hr as <-.
        pose proof (le_list_max _ _ (cpos_In X q k0 i Hb0 Hi)).
        pose proof (fold_min_le (length (wit X)) _ _ (cpos_In X q' k1 i' Hb1 Hi')).
        unfold Pq, P. change (idx (ce X (fst q) (snd q) i) (wit X) < idx (ce X (fst q') (snd q') i') (wit X)).
        lia.
    Qed.

    Corollary seqlock_z_composition_canon :
      K_ok K = true -> WT.Conclusion (dtable rc) (setting_rt sl_cf rc K X (canon X)).
    Proof. intros HK. exact (seqlock_z_composition_rt rc K X (canon X) HW HK canon_ok). Qed.
  End Canon.

  (** ** Part 2: incomplete executions *)

  (** *** Filtering a program

      [fprog kp p] keeps the blocks of [p] whose index satisfies [kp];
      block [j] of [p] becomes block [cnt kp j]; [unc] is the inverse. *)

  Fixpoint cnt (kp : nat -> bool) (j : nat) : nat :=
    match j with 0 => 0 | S j' => (if kp 0 then 1 else 0) + cnt (fun x => kp (S x)) j' end.

  Fixpoint fprog (kp : nat -> bool) (p : list Blk) : list Blk :=
    match p with
    | [] => []
    | k :: p' => if kp 0 then k :: fprog (fun x => kp (S x)) p' else fprog (fun x => kp (S x)) p'
    end.

  Fixpoint unc (kp : nat -> bool) (p : list Blk) (j' : nat) : nat :=
    match p with
    | [] => 0
    | _ :: p' =>
        if kp 0 then match j' with 0 => 0 | S j'' => S (unc (fun x => kp (S x)) p' j'') end
        else S (unc (fun x => kp (S x)) p' j')
    end.

  (** Block and offset of a trace index. *)
  Fixpoint loc (p : list Blk) (i : nat) : nat * nat :=
    match p with
    | [] => (0, i)
    | k :: p' => if Nat.ltb i (length (calls k)) then (0, i)
                 else (S (fst (loc p' (i - length (calls k)))), snd (loc p' (i - length (calls k))))
    end.

  Lemma cnt_le kp j j' : j <= j' -> cnt kp j <= cnt kp j'.
  Proof.
    revert kp j'. induction j as [|j IH]; intros kp j' Hle; [cbn; lia|].
    destruct j' as [|j']; [lia|]. cbn.
    specialize (IH (fun x => kp (S x)) j' ltac:(lia)). destruct (kp 0); lia.
  Qed.

  Lemma cnt_lt kp j j' : kp j = true -> j < j' -> cnt kp j < cnt kp j'.
  Proof.
    revert kp j'. induction j as [|j IH]; intros kp j' Hk Hlt.
    - destruct j' as [|j']; [lia|]. cbn. rewrite Hk. lia.
    - destruct j' as [|j']; [lia|]. cbn.
      specialize (IH (fun x => kp (S x)) j' Hk ltac:(lia)). destruct (kp 0); lia.
  Qed.

  Lemma cnt_inj kp j j' : kp j = true -> kp j' = true -> cnt kp j = cnt kp j' -> j = j'.
  Proof.
    intros H H' E. destruct (Nat.lt_trichotomy j j') as [Hlt|[?|Hlt]]; [|assumption|].
    - pose proof (cnt_lt kp j j' H Hlt). lia.
    - pose proof (cnt_lt kp j' j H' Hlt). lia.
  Qed.

  Lemma cnt_lt_iff kp j j' : kp j = true -> kp j' = true -> (cnt kp j < cnt kp j' <-> j < j').
  Proof.
    intros H H'. split; [|apply cnt_lt; assumption].
    intros Hlt. destruct (Nat.lt_ge_cases j j') as [?|Hge]; [assumption|].
    pose proof (cnt_le kp j' j Hge). lia.
  Qed.

  Lemma fprog_nth kp p j k :
    kp j = true -> nth_error p j = Some k -> nth_error (fprog kp p) (cnt kp j) = Some k.
  Proof.
    revert kp j. induction p as [|k0 p IH]; intros kp j Hk Hj; [destruct j; discriminate|].
    destruct j as [|j]; cbn in Hj |- *.
    - injection Hj as <-. rewrite Hk. reflexivity.
    - destruct (kp 0); cbn; apply IH; assumption.
  Qed.

  Lemma unc_spec kp p j' : j' < length (fprog kp p) ->
    kp (unc kp p j') = true /\ cnt kp (unc kp p j') = j' /\
    nth_error p (unc kp p j') = nth_error (fprog kp p) j'.
  Proof.
    revert kp j'. induction p as [|k0 p IH]; intros kp j' Hl; cbn in Hl |- *; [lia|].
    destruct (kp 0) eqn:E.
    - destruct j' as [|j'].
      + cbn. rewrite E. auto.
      + cbn in Hl. destruct (IH (fun x => kp (S x)) j' ltac:(lia)) as (H1 & H2 & H3).
        cbn. rewrite E. auto.
    - destruct (IH (fun x => kp (S x)) j' Hl) as (H1 & H2 & H3). cbn. rewrite E. auto.
  Qed.

  Lemma unc_lt kp p j' : j' < length (fprog kp p) -> unc kp p j' < length p.
  Proof.
    intros Hl. destruct (unc_spec kp p j' Hl) as (_ & _ & E). apply nth_error_Some.
    rewrite E. apply nth_error_Some. exact Hl.
  Qed.

  Lemma cnt_lt_length kp p j : kp j = true -> j < length p -> cnt kp j < length (fprog kp p).
  Proof.
    intros Hk Hj. destruct (nth_error p j) as [k|] eqn:E; [|apply nth_error_None in E; lia].
    apply nth_error_Some. rewrite (fprog_nth kp p j k Hk E). discriminate.
  Qed.

  Lemma unc_cnt kp p j : kp j = true -> j < length p -> unc kp p (cnt kp j) = j.
  Proof.
    intros Hk Hj. destruct (unc_spec kp p (cnt kp j) (cnt_lt_length kp p j Hk Hj)) as (H1 & H2 & _).
    exact (cnt_inj kp _ _ H1 Hk H2).
  Qed.

  Lemma loc_off p j k i : nth_error p j = Some k -> i < length (calls k) -> loc p (off p j + i) = (j, i).
  Proof.
    revert j. induction p as [|k0 p IH]; intros j Hj Hi; [destruct j; discriminate|].
    destruct j as [|j]; cbn in Hj.
    - injection Hj as ->. rewrite off_0, Nat.add_0_l. cbn [loc].
      apply Nat.ltb_lt in Hi. rewrite Hi. reflexivity.
    - rewrite off_cons. cbn [loc].
      destruct (Nat.ltb_spec (length (calls k0) + off p j + i) (length (calls k0))); [lia|].
      replace (length (calls k0) + off p j + i - length (calls k0)) with (off p j + i) by lia.
      rewrite (IH j Hj Hi). reflexivity.
  Qed.

  Lemma off_cmp p j1 k1 i1 j2 k2 i2 :
    nth_error p j1 = Some k1 -> i1 < length (calls k1) ->
    nth_error p j2 = Some k2 -> i2 < length (calls k2) ->
    (off p j1 + i1 < off p j2 + i2 <-> j1 < j2 \/ (j1 = j2 /\ i1 < i2)).
  Proof.
    intros H1 L1 H2 L2. split.
    - intros Hlt. destruct (Nat.lt_trichotomy j1 j2) as [?|[->|Hgt]]; [left; assumption|right; lia|].
      pose proof (off_lt p j2 j1 k2 i2 H2 L2 Hgt). lia.
    - intros [Hlt|[-> Hlt]]; [pose proof (off_lt p j1 j2 k1 i1 H1 L1 Hlt); lia | lia].
  Qed.

  Lemma off_inj p j1 k1 i1 j2 k2 i2 :
    nth_error p j1 = Some k1 -> i1 < length (calls k1) ->
    nth_error p j2 = Some k2 -> i2 < length (calls k2) ->
    off p j1 + i1 = off p j2 + i2 -> j1 = j2 /\ i1 = i2.
  Proof.
    intros H1 L1 H2 L2 E.
    destruct (Nat.lt_trichotomy j1 j2) as [Hlt|[->|Hlt]].
    - pose proof (off_lt p j1 j2 k1 i1 H1 L1 Hlt). lia.
    - lia.
    - pose proof (off_lt p j2 j1 k2 i2 H2 L2 Hlt). lia.
  Qed.

  (** *** Positions in lists *)

  Lemma idx_app_l e l1 l2 : In e l1 -> idx e (l1 ++ l2) = idx e l1.
  Proof.
    induction l1 as [|x l1 IH]; cbn; [contradiction|].
    destruct (Ev_eq_dec e x); [reflexivity|]. intros [->|H]; [contradiction|]. f_equal. apply IH, H.
  Qed.

  Lemma idx_app_r e l1 l2 : ~ In e l1 -> idx e (l1 ++ l2) = length l1 + idx e l2.
  Proof.
    induction l1 as [|x l1 IH]; cbn; [reflexivity|].
    destruct (Ev_eq_dec e x) as [->|Hne]; [intros H; exfalso; apply H; left; reflexivity|].
    intros H. f_equal. apply IH. intros H'. apply H. right. exact H'.
  Qed.

  Lemma idx_filter_lt (f : Ev -> bool) l a b :
    In a l -> In b l -> f a = true -> f b = true -> idx a l < idx b l ->
    idx a (filter f l) < idx b (filter f l).
  Proof.
    induction l as [|x l IH]; cbn; [contradiction|]. intros Ha Hb Fa Fb.
    destruct (Ev_eq_dec a x) as [->|Hax]; destruct (Ev_eq_dec b x) as [->|Hbx]; try lia.
    - intros _. rewrite Fa. cbn. destruct (Ev_eq_dec x x); [|contradiction].
      destruct (Ev_eq_dec b x); [contradiction|]. lia.
    - intros Hlt. destruct Ha as [->|Ha]; [contradiction|]. destruct Hb as [->|Hb]; [contradiction|].
      destruct (f x); cbn; [destruct (Ev_eq_dec a x); [contradiction|];
                              destruct (Ev_eq_dec b x); [contradiction|] |];
        specialize (IH Ha Hb Fa Fb ltac:(lia)); lia.
  Qed.

  Lemma idx_map (f : Ev -> Ev) l a :
    (forall x y, In x l -> In y l -> f x = f y -> x = y) -> In a l -> idx (f a) (map f l) = idx a l.
  Proof.
    induction l as [|x l IH]; cbn; [contradiction|]. intros Hinj Ha.
    destruct (Ev_eq_dec a x) as [->|Hne].
    - destruct (Ev_eq_dec (f x) (f x)); [reflexivity|contradiction].
    - destruct (Ev_eq_dec (f a) (f x)) as [E|_].
      + exfalso. apply Hne. apply Hinj; [|left; reflexivity|exact E].
        destruct Ha as [->|Ha]; [left; reflexivity|right; exact Ha].
      + destruct Ha as [->|Ha]; [contradiction|]. f_equal.
        apply IH; [|exact Ha]. intros y z Hy Hz. apply Hinj; right; assumption.
  Qed.

  Lemma NoDup_map_inj {A B} (f : A -> B) l :
    (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
  Proof.
    induction l as [|x l IH]; cbn; intros Hinj Hnd; [constructor|].
    inversion Hnd as [|? ? Hni Hnd']; subst. constructor.
    - intros Hin. apply in_map_iff in Hin as (y & E & Hy).
      assert (y = x) by (apply Hinj; [right|left|]; auto). subst. contradiction.
    - apply IH; [|exact Hnd']. intros y z Hy Hz. apply Hinj; right; assumption.
  Qed.

  Lemma nodup_firstn_neq {A} (l : list A) m e x :
    NoDup l -> nth_error l m = Some e -> In x (firstn m l) -> x <> e.
  Proof.
    revert m. induction l as [|a l IH]; intros m Hnd Hm Hx; [destruct m; discriminate|].
    inversion Hnd as [|? ? Hni Hnd']; subst.
    destruct m as [|m]; cbn in Hx, Hm; [contradiction|].
    destruct Hx as [<-|Hx].
    - intros ->. apply Hni. eapply nth_error_In. exact Hm.
    - exact (IH m Hnd' Hm Hx).
  Qed.

  (** Dropping calls that do not change the state. *)
  Definition neutral (c : UC) : bool :=
    match c with Acq | Rel | WrX _ | WrY _ | WrZ _ => false | _ => true end.

  Lemma post_neutral s e : neutral (call e) = true -> post s e = s.
  Proof. unfold post, neutral. destruct (call e); cbn; congruence. Qed.

  Lemma run_filter (g : Ev -> bool) l s :
    (forall x, In x l -> g x = false -> neutral (call x) = true) -> run s (filter g l) = run s l.
  Proof.
    revert s. induction l as [|x l IH]; intros s Hn; cbn; [reflexivity|].
    destruct (g x) eqn:G; cbn.
    - apply IH. intros y Hy. apply Hn. right. exact Hy.
    - rewrite (post_neutral s x (Hn x (or_introl eq_refl) G)).
      apply IH. intros y Hy. apply Hn. right. exact Hy.
  Qed.

  Lemma run_filter_nth (g : Ev -> bool) l s p e :
    (forall x, In x l -> g x = false -> neutral (call x) = true) ->
    nth_error (filter g l) p = Some e ->
    exists P, nth_error l P = Some e /\ run s (firstn p (filter g l)) = run s (firstn P l).
  Proof.
    revert s p. induction l as [|x l IH]; intros s p Hn Hp; [destruct p; discriminate|].
    assert (Hn' : forall y, In y l -> g y = false -> neutral (call y) = true)
      by (intros y Hy; apply Hn; right; exact Hy).
    cbn in Hp |- *. destruct (g x) eqn:G.
    - destruct p as [|p]; cbn in Hp.
      + injection Hp as <-. exists 0. split; reflexivity.
      + destruct (IH (post s x) p Hn' Hp) as (P & HP & E). exists (S P). split; [exact HP|].
        cbn. exact E.
    - destruct (IH s p Hn' Hp) as (P & HP & E). exists (S P). split; [exact HP|].
      cbn. rewrite (post_neutral s x (Hn x (or_introl eq_refl) G)). exact E.
  Qed.

  Lemma pre_post_ext e e' : th e = th e' -> call e = call e' ->
    (forall s, pre s e = pre s e') /\ (forall s, post s e = post s e').
  Proof. destruct e, e'; cbn; intros -> ->; split; reflexivity. Qed.

  Lemma hold_run s l : (forall x, In x l -> call x <> Acq /\ call x <> Rel) -> hold (run s l) = hold s.
  Proof.
    revert s. induction l as [|x l IH]; intros s H; cbn; [reflexivity|].
    rewrite IH by (intros y Hy; apply H; right; exact Hy).
    rewrite hold_post. destruct (H x (or_introl eq_refl)) as [H1 H2].
    destruct (call x); congruence.
  Qed.

  (** *** Incomplete executions

      [pend q] holds of the operations still pending.  The witness lists
      the present calls (those the completion keeps); completed operations
      have all their calls present; and the present calls of a thread are
      closed under earlier calls of the thread with a preserved edge to
      them ([wfi_closed]; see the header for the justification). *)

  Section WithExecInc.
    Context (rc : bool) (K : TLCats) (X : Exec) (pend : nat * nat -> bool).

    Record WF_inc : Prop := {
      wfi_nodup : NoDup (wit X);
      wfi_ths : NoDup (ths X);
      wfi_call : forall e, In e (wit X) ->
                   In (th e) (ths X) /\ nth_error (trace (prog X (th e))) (ix e) = Some (call e);
      wfi_complete : forall t j k i, In t (ths X) -> nth_error (prog X t) j = Some k ->
                       pend (t, j) = false -> i < length (calls k) -> In (ce X t j i) (wit X);
      wfi_closed : forall e i, In e (wit X) -> i < ix e ->
                     upres rc K (call (evt X (th e) i)) (call e) = true -> In (evt X (th e) i) (wit X);
      wfi_pres : forall e1 e2, In e1 (wit X) -> In e2 (wit X) -> th e1 = th e2 ->
                   ix e1 < ix e2 -> upres rc K (call e1) (call e2) = true ->
                   idx e1 (wit X) < idx e2 (wit X);
      wfi_valid : forall p e, nth_error (wit X) p = Some e -> pre (at_ X p) e = true;
    }.
  End WithExecInc.

  (** Complete executions are the incomplete ones with nothing pending. *)
  Lemma WF_WF_inc rc K X pend : WF rc K X -> WF_inc rc K X pend.
  Proof.
    intros HW. constructor.
    - exact (wf_nodup _ _ _ HW).
    - exact (wf_ths _ _ _ HW).
    - exact (wf_call _ _ _ HW).
    - intros t j k i Ht Hj _ Hi.
      destruct (nth_error (calls k) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
      apply (wf_complete _ _ _ HW); [exact Ht|]. exact (proj2 (blk_evt X _ _ _ _ _ Hj Hc)).
    - intros e i He Hi _. destruct (wf_call _ _ _ HW e He) as [Ht Hn].
      apply (wf_complete _ _ _ HW); [exact Ht|].
      assert (ix e < length (trace (prog X (th e)))) by (apply nth_error_Some; congruence). lia.
    - exact (wf_pres _ _ _ HW).
    - exact (wf_valid _ _ _ HW).
  Qed.

  Lemma WF_inc_WF rc K X pend :
    WF_inc rc K X pend -> (forall q, In q (all_ops X) -> pend q = false) -> WF rc K X.
  Proof.
    intros HI Hp. constructor.
    - exact (wfi_nodup _ _ _ _ HI).
    - exact (wfi_ths _ _ _ _ HI).
    - exact (wfi_call _ _ _ _ HI).
    - intros t i Ht Hi.
      destruct (nth_error (trace (prog X t)) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
      destruct (trace_inv _ _ _ Hc) as (j & k & i' & Hj & -> & Hk).
      apply (wfi_complete _ _ _ _ HI t j k); try assumption.
      + apply Hp. exact (all_ops_of X t j k Ht Hj).
      + apply nth_error_Some. congruence.
    - exact (wfi_pres _ _ _ _ HI).
    - exact (wfi_valid _ _ _ _ HI).
  Qed.

  (** *** The completion *)

  Definition present (X : Exec) (e : Ev) : bool := existsb (Ev_eqb e) (wit X).

  Lemma present_iff X e : present X e = true <-> In e (wit X).
  Proof.
    unfold present. rewrite existsb_exists. split.
    - intros (x & Hx & E). apply Ev_eqb_eq in E. subst. exact Hx.
    - intros H. exists e. split; [exact H|]. unfold Ev_eqb. destruct (Ev_eq_dec e e); congruence.
  Qed.

  (** The operations kept: the completed ones, the writes whose [acq] is
      present and the z-writes whose call is present.  Pending reads,
      pending z-reads, and pending writes or z-writes with no call present
      are dropped. *)
  Definition keep (X : Exec) (pend : nat * nat -> bool) (q : nat * nat) : bool :=
    negb (pend q) ||
    match blk X q with
    | Some (BW _ _) | Some (BZw _) => present X (ce X (fst q) (snd q) 0)
    | _ => false
    end.

  (** A write that holds the lock: [acq] present, [rel] absent. *)
  Definition is_open (X : Exec) (q : nat * nat) : bool :=
    match blk X q with
    | Some (BW _ _) => present X (ce X (fst q) (snd q) 0) && negb (present X (ce X (fst q) (snd q) 5))
    | _ => false
    end.

  (** Its absent calls, appended in program order. *)
  Definition missing (X : Exec) : list Ev :=
    match find (is_open X) (all_ops X) with
    | Some w => filter (fun e => negb (present X e)) (map (ce X (fst w) (snd w)) (seq 0 6))
    | None => []
    end.

  Definition kp (X : Exec) (pend : nat * nat -> bool) (t : nat) : nat -> bool :=
    fun j => keep X pend (t, j).

  Definition cprog (X : Exec) (pend : nat * nat -> bool) (t : nat) : list Blk :=
    fprog (kp X pend t) (prog X t).

  Definition keepev (X : Exec) (pend : nat * nat -> bool) (e : Ev) : bool :=
    keep X pend (th e, fst (loc (prog X (th e)) (ix e))).

  (** Re-indexing a call of a kept operation. *)
  Definition emap (X : Exec) (pend : nat * nat -> bool) (e : Ev) : Ev :=
    mkEv (th e)
         (off (cprog X pend (th e)) (cnt (kp X pend (th e)) (fst (loc (prog X (th e)) (ix e))))
          + snd (loc (prog X (th e)) (ix e)))
         (call e).

  Definition Fk (X : Exec) (pend : nat * nat -> bool) : list Ev := filter (keepev X pend) (wit X).
  Definition Lc (X : Exec) (pend : nat * nat -> bool) : list Ev := Fk X pend ++ missing X.

  Definition completion (X : Exec) (pend : nat * nat -> bool) : Exec :=
    {| ths := ths X; prog := cprog X pend; wit := map (emap X pend) (Lc X pend) |}.

  (** Operation [q'] of the completion is operation [psi X pend q'] of
      [X]. *)
  Definition psi (X : Exec) (pend : nat * nat -> bool) (q : nat * nat) : nat * nat :=
    (fst q, unc (kp X pend (fst q)) (prog X (fst q)) (snd q)).

  Lemma is_open_spec X q : is_open X q = true <->
    exists vx vy, blk X q = Some (BW vx vy) /\ In (ce X (fst q) (snd q) 0) (wit X) /\
                  ~ In (ce X (fst q) (snd q) 5) (wit X).
  Proof.
    unfold is_open. destruct (blk X q) as [[vx vy| | |]|]; split; try discriminate;
      try (intros (? & ? & ? & _); discriminate).
    - intros H. apply andb_true_iff in H as [H1 H2]. apply negb_true_iff in H2.
      exists vx, vy. split; [reflexivity|]. split; [apply present_iff, H1|].
      intros H. apply present_iff in H. congruence.
    - intros (vx' & vy' & _ & H1 & H2). apply present_iff in H1. rewrite H1. cbn.
      destruct (present X (ce X (fst q) (snd q) 5)) eqn:E; [|reflexivity].
      apply present_iff in E. contradiction.
  Qed.

  Lemma calls_Rel k i : nth_error (calls k) i = Some Rel -> exists vx vy, k = BW vx vy /\ i = 5.
  Proof.
    intros H. destruct k as [vx vy|fs s a b|v|v].
    - exists vx, vy. split; [reflexivity|].
      destruct i as [|[|[|[|[|[|i]]]]]]; cbn in H; try discriminate; [reflexivity|destruct i; discriminate].
    - exfalso. exact (calls_BR_kind fs s a b Rel (nth_error_In _ _ H)).
    - destruct i as [|[|i]]; cbn in H; discriminate.
    - destruct i as [|[|i]]; cbn in H; discriminate.
  Qed.

  Lemma evt_nth X t i :
    i < length (trace (prog X t)) -> nth_error (trace (prog X t)) (ix (evt X t i)) = Some (call (evt X t i)).
  Proof. intros H. cbn. apply nth_error_nth'. exact H. Qed.

  (** How the operations of a completion [X'] correspond to those of [X]. *)
  Record Psi_ok (X X' : Exec) (pend : nat * nat -> bool) (f : nat * nat -> nat * nat) : Prop := {
    ps_ths : ths X' = ths X;
    ps_ops : forall q', In q' (all_ops X') -> In (f q') (all_ops X);
    ps_inj : forall q1 q2, In q1 (all_ops X') -> In q2 (all_ops X') -> f q1 = f q2 -> q1 = q2;
    ps_blk : forall q', In q' (all_ops X') -> blk X' q' = blk X (f q');
    ps_ovl : forall q', In q' (all_ops X') -> ovl X' q' = ovl X (f q');
    ps_th : forall q', fst (f q') = fst q';
    ps_po : forall q1 q2, In q1 (all_ops X') -> In q2 (all_ops X') -> fst q1 = fst q2 ->
              (snd q1 < snd q2 <-> snd (f q1) < snd (f q2));
    ps_complete : forall q, In q (all_ops X) -> pend q = false ->
                    exists q', In q' (all_ops X') /\ f q' = q;
    ps_pending : forall q, In q (all_ops X) -> (forall q', In q' (all_ops X') -> f q' <> q) ->
                   pend q = true;
  }.

  (** The completion's timing: operations keep their times, present calls
      keep theirs, appended calls are invoked no earlier than any
      operation and never respond. *)
  Definition ctiming (X : Exec) (pend : nat * nat -> bool) (T : Timing) : Timing := {|
    oinv := fun q => oinv T (psi X pend q);
    ores := fun q => ores T (psi X pend q);
    cinv := fun e' => match find (fun e => Ev_eqb (emap X pend e) e') (Fk X pend) with
                      | Some e => cinv T e
                      | None => list_max (map (oinv T) (all_ops X))
                      end;
    cres := fun e' => match find (fun e => Ev_eqb (emap X pend e) e') (Fk X pend) with
                      | Some e => cres T e
                      | None => None
                      end;
  |}.

  Section Inc.
    Context (rc : bool) (K : TLCats) (X : Exec) (pend : nat * nat -> bool).
    Hypothesis HI : WF_inc rc K X pend.
    Hypothesis HK : K_ok K = true.

    Let HKa : isW (k_acq K) = true.
    Proof. unfold K_ok in HK. repeat (apply andb_true_iff in HK as [HK ?]). assumption. Qed.
    Let HKr : isW (k_rel K) = true.
    Proof. unfold K_ok in HK. repeat (apply andb_true_iff in HK as [HK ?]). assumption. Qed.

    Ltac upres_ok :=
      unfold upres; cbn [uobj same_obj ucat orb];
      first [ reflexivity
            | apply dto_W_wmb; first [assumption | reflexivity]
            | apply dto_wmb_W; first [assumption | reflexivity] ].

    Lemma inc_decomp e : In e (wit X) ->
      exists t j k i, In t (ths X) /\ nth_error (prog X t) j = Some k /\
                      nth_error (calls k) i = Some (call e) /\ e = ce X t j i.
    Proof.
      intros He. destruct (wfi_call _ _ _ _ HI e He) as [Ht Hn].
      destruct (trace_inv _ _ _ Hn) as (j & k & i & Hj & Ei & Hi).
      exists (th e), j, k, i. split; [exact Ht|]. split; [exact Hj|]. split; [exact Hi|].
      destruct e as [t i' c]. cbn in *. unfold ce, evt. rewrite <- Ei. f_equal.
      symmetry. apply nth_error_nth. exact Hn.
    Qed.

    (** Closure, across operations of one thread. *)
    Lemma closed_cross t j k i j' k' i' c c' :
      nth_error (prog X t) j = Some k -> nth_error (calls k) i = Some c ->
      nth_error (prog X t) j' = Some k' -> nth_error (calls k') i' = Some c' ->
      off (prog X t) j + i < off (prog X t) j' + i' -> upres rc K c c' = true ->
      In (ce X t j' i') (wit X) -> In (ce X t j i) (wit X).
    Proof.
      intros Hj Hc Hj' Hc' Hlt Hu Hin.
      assert (Hu' : upres rc K (call (evt X (th (ce X t j' i')) (off (prog X t) j + i))) (call (ce X t j' i'))
                    = true).
      { change (upres rc K (call (ce X t j i)) (call (ce X t j' i')) = true).
        rewrite (ce_call X t j k i c Hj Hc), (ce_call X t j' k' i' c' Hj' Hc'). exact Hu. }
      exact (wfi_closed _ _ _ _ HI (ce X t j' i') (off (prog X t) j + i) Hin Hlt Hu').
    Qed.

    Lemma pres_cross t j k i j' k' i' c c' :
      nth_error (prog X t) j = Some k -> nth_error (calls k) i = Some c ->
      nth_error (prog X t) j' = Some k' -> nth_error (calls k') i' = Some c' ->
      off (prog X t) j + i < off (prog X t) j' + i' -> upres rc K c c' = true ->
      In (ce X t j i) (wit X) -> In (ce X t j' i') (wit X) ->
      idx (ce X t j i) (wit X) < idx (ce X t j' i') (wit X).
    Proof.
      intros Hj Hc Hj' Hc' Hlt Hu Hin Hin'.
      apply (wfi_pres _ _ _ _ HI); [exact Hin|exact Hin'|reflexivity|exact Hlt|].
      rewrite (ce_call X t j k i c Hj Hc), (ce_call X t j' k' i' c' Hj' Hc'). exact Hu.
    Qed.

    (** A write with a call present has its [acq] present. *)
    Lemma acq_needed t j vx vy i : nth_error (prog X t) j = Some (BW vx vy) -> i < 6 ->
      In (ce X t j i) (wit X) -> In (ce X t j 0) (wit X).
    Proof.
      intros Hj Hi Hin.
      assert (S1 : In (ce X t j 1) (wit X) -> In (ce X t j 0) (wit X)).
      { apply (closed_cross t j _ 0 j _ 1 Acq WmbC Hj eq_refl Hj eq_refl); [lia|upres_ok]. }
      destruct i as [|[|[|[|[|[|i]]]]]]; try lia; try exact Hin.
      - exact (S1 Hin).
      - apply S1.
        apply (closed_cross t j _ 1 j _ 2 WmbC (WrX vx) Hj eq_refl Hj eq_refl); [lia|upres_ok|exact Hin].
      - apply S1.
        apply (closed_cross t j _ 1 j _ 3 WmbC (WrY vy) Hj eq_refl Hj eq_refl); [lia|upres_ok|exact Hin].
      - apply (closed_cross t j _ 0 j _ 4 Acq WmbC Hj eq_refl Hj eq_refl); [lia|upres_ok|exact Hin].
      - apply (closed_cross t j _ 0 j _ 5 Acq Rel Hj eq_refl Hj eq_refl); [lia|upres_ok|exact Hin].
    Qed.

    (** A write with its [rel] present has every call present. *)
    Lemma rel_all t j vx vy i : nth_error (prog X t) j = Some (BW vx vy) -> i < 6 ->
      In (ce X t j 5) (wit X) -> In (ce X t j i) (wit X).
    Proof.
      intros Hj Hi H5.
      assert (H4 : In (ce X t j 4) (wit X))
        by (apply (closed_cross t j _ 4 j _ 5 WmbC Rel Hj eq_refl Hj eq_refl); [lia|upres_ok|exact H5]).
      assert (H2 : In (ce X t j 2) (wit X))
        by (apply (closed_cross t j _ 2 j _ 4 (WrX vx) WmbC Hj eq_refl Hj eq_refl); [lia|upres_ok|exact H4]).
      assert (H3 : In (ce X t j 3) (wit X))
        by (apply (closed_cross t j _ 3 j _ 4 (WrY vy) WmbC Hj eq_refl Hj eq_refl); [lia|upres_ok|exact H4]).
      assert (H1 : In (ce X t j 1) (wit X))
        by (apply (closed_cross t j _ 1 j _ 2 WmbC (WrX vx) Hj eq_refl Hj eq_refl); [lia|upres_ok|exact H2]).
      assert (H0 : In (ce X t j 0) (wit X))
        by (apply (closed_cross t j _ 0 j _ 5 Acq Rel Hj eq_refl Hj eq_refl); [lia|upres_ok|exact H5]).
      destruct i as [|[|[|[|[|[|i]]]]]]; first [assumption | lia].
    Qed.

    (** **** The open write holds the lock to the end *)

    Section Open.
      Context (tw jw vx vy : nat).
      Hypothesis Hbw : nth_error (prog X tw) jw = Some (BW vx vy).
      Hypothesis Hacq : In (ce X tw jw 0) (wit X).
      Hypothesis Hrel : ~ In (ce X tw jw 5) (wit X).

      Lemma held_forever p :
        idx (ce X tw jw 0) (wit X) < p -> p <= length (wit X) -> hold (at_ X p) = Some tw.
      Proof.
        induction p as [|p IH]; intros H1 H2; [lia|].
        rewrite at_S.
        destruct (nth_error (wit X) p) as [e|] eqn:Ep; [|apply nth_error_None in Ep; lia].
        destruct (Nat.eq_dec p (idx (ce X tw jw 0) (wit X))) as [Ep0|Hne].
        - rewrite Ep0, (idx_nth _ _ Hacq) in Ep. injection Ep as <-.
          rewrite hold_post, (ce_call X tw jw _ 0 Acq Hbw eq_refl). reflexivity.
        - specialize (IH ltac:(lia) ltac:(lia)).
          pose proof (wfi_valid _ _ _ _ HI _ _ Ep) as Hpre.
          assert (He : In e (wit X)) by (eapply nth_error_In; exact Ep).
          rewrite hold_post. destruct (call e) eqn:Ec; try exact IH.
          + exfalso. unfold pre in Hpre. rewrite Ec, IH in Hpre. cbn in Hpre.
            rewrite andb_false_r in Hpre. discriminate.
          + exfalso. unfold pre in Hpre. rewrite Ec, IH in Hpre. cbn in Hpre.
            apply Nat.eqb_eq in Hpre.
            destruct (inc_decomp e He) as (t & j & k & i & Ht & Hj & Hi & ->).
            rewrite Ec in Hi. destruct (calls_Rel k i Hi) as (vx' & vy' & -> & ->).
            change (tw = t) in Hpre. subst t.
            destruct (Nat.lt_trichotomy j jw) as [Hlt|[->|Hlt]].
            * assert (Ho : off (prog X tw) j + 5 < off (prog X tw) jw + 0)
                by (pose proof (off_lt _ j jw _ 5 Hj ltac:(cbn; lia) Hlt); lia).
              pose proof (pres_cross tw j _ 5 jw _ 0 Rel Acq Hj eq_refl Hbw eq_refl Ho
                            ltac:(upres_ok) He Hacq) as Hp.
              rewrite (nth_idx _ _ _ (wfi_nodup _ _ _ _ HI) Ep) in Hp. lia.
            * exact (Hrel He).
            * apply Hrel. apply (closed_cross tw jw _ 5 j _ 5 Rel Rel Hbw eq_refl Hj eq_refl);
                [|upres_ok|exact He].
              pose proof (off_lt _ jw j _ 5 Hbw ltac:(cbn; lia) Hlt). lia.
      Qed.

      Lemma final_hold : hold (run init (wit X)) = Some tw.
      Proof.
        assert (E : run init (wit X) = at_ X (length (wit X)))
          by (unfold at_; rewrite firstn_all; reflexivity).
        rewrite E. apply held_forever; [apply idx_lt, Hacq | lia].
      Qed.
    End Open.

    (** At most one write holds the lock forever. *)
    Lemma open_unique tw jw vx vy tw' jw' vx' vy' :
      nth_error (prog X tw) jw = Some (BW vx vy) -> In (ce X tw jw 0) (wit X) -> ~ In (ce X tw jw 5) (wit X) ->
      nth_error (prog X tw') jw' = Some (BW vx' vy') -> In (ce X tw' jw' 0) (wit X) ->
      ~ In (ce X tw' jw' 5) (wit X) ->
      (tw, jw) = (tw', jw').
    Proof.
      intros Hb Ha Hr Hb' Ha' Hr'.
      assert (Hno : forall a b ax ay a' b' ax' ay',
                 nth_error (prog X a) b = Some (BW ax ay) -> In (ce X a b 0) (wit X) ->
                 ~ In (ce X a b 5) (wit X) ->
                 nth_error (prog X a') b' = Some (BW ax' ay') -> In (ce X a' b' 0) (wit X) ->
                 ~ idx (ce X a b 0) (wit X) < idx (ce X a' b' 0) (wit X)).
      { intros a b ax ay a' b' ax' ay' Hb0 Ha0 Hr0 Hb0' Ha0' Hlt.
        pose proof (held_forever a b ax ay Hb0 Ha0 Hr0 (idx (ce X a' b' 0) (wit X)) Hlt
                      (Nat.lt_le_incl _ _ (idx_lt _ _ Ha0'))) as Hh.
        pose proof (wfi_valid _ _ _ _ HI _ _ (idx_nth _ _ Ha0')) as Hpre.
        unfold pre in Hpre. rewrite (ce_call X a' b' _ 0 Acq Hb0' eq_refl), Hh in Hpre. cbn in Hpre.
        rewrite andb_false_r in Hpre. discriminate. }
      destruct (Nat.lt_trichotomy (idx (ce X tw jw 0) (wit X)) (idx (ce X tw' jw' 0) (wit X)))
        as [Hlt|[E|Hlt]].
      - exfalso. exact (Hno _ _ _ _ _ _ _ _ Hb Ha Hr Hb' Ha' Hlt).
      - pose proof (idx_inj _ _ _ Ha Ha' E) as E'. unfold ce, evt in E'. injection E' as Et Ei _. subst tw'.
        destruct (off_inj (prog X tw) jw _ 0 jw' _ 0 Hb ltac:(cbn; lia) Hb' ltac:(cbn; lia) Ei) as [-> _].
        reflexivity.
      - exfalso. exact (Hno _ _ _ _ _ _ _ _ Hb' Ha' Hr' Hb Ha Hlt).
    Qed.

    Lemma missing_cases :
      (missing X = [] /\ forall q, In q (all_ops X) -> is_open X q = false) \/
      (exists tw jw vx vy, In (tw, jw) (all_ops X) /\ nth_error (prog X tw) jw = Some (BW vx vy) /\
         In (ce X tw jw 0) (wit X) /\ ~ In (ce X tw jw 5) (wit X) /\
         missing X = filter (fun e => negb (present X e)) (map (ce X tw jw) (seq 0 6))).
    Proof.
      unfold missing. destruct (find (is_open X) (all_ops X)) as [[tw jw]|] eqn:F.
      - right. apply find_some in F as [Hw Ho]. apply is_open_spec in Ho as (vx & vy & Hb & Ha & Hr).
        exists tw, jw, vx, vy. auto.
      - left. split; [reflexivity|]. intros q Hq. exact (find_none _ _ F q Hq).
    Qed.

    (** **** Kept and dropped calls *)

    (** Every call of a kept operation is present, or is a missing call of
        the open write. *)
    Lemma kept_cases t j k i : In t (ths X) -> nth_error (prog X t) j = Some k -> i < length (calls k) ->
      keep X pend (t, j) = true -> In (ce X t j i) (wit X) \/ In (ce X t j i) (missing X).
    Proof.
      intros Ht Hj Hi Hk. unfold keep in Hk. unfold blk in Hk. cbn [fst snd] in Hk. rewrite Hj in Hk.
      destruct (pend (t, j)) eqn:Hp; cbn in Hk.
      2:{ left. exact (wfi_complete _ _ _ _ HI t j k i Ht Hj Hp Hi). }
      destruct (In_dec Ev_eq_dec (ce X t j i) (wit X)) as [Hin|Hout]; [left; exact Hin|right].
      destruct k as [vx vy|fs s a b|v|v]; try discriminate.
      - apply present_iff in Hk.
        assert (Hr : ~ In (ce X t j 5) (wit X)) by (intros H5; exact (Hout (rel_all t j vx vy i Hj Hi H5))).
        assert (Ho : is_open X (t, j) = true) by (apply is_open_spec; exists vx, vy; auto).
        destruct missing_cases as [[_ Hn]|(tw & jw & vx' & vy' & Hw & Hbw & Ha & Hr' & ->)].
        + rewrite (Hn (t, j) (all_ops_of X t j _ Ht Hj)) in Ho. discriminate.
        + pose proof (open_unique t j vx vy tw jw vx' vy' Hj Hk Hr Hbw Ha Hr') as E. injection E as <- <-.
          apply filter_In. split.
          * apply in_map. apply in_seq. cbn in Hi. lia.
          * apply negb_true_iff. destruct (present X (ce X t j i)) eqn:E; [|reflexivity].
            apply present_iff in E. contradiction.
      - apply present_iff in Hk. cbn in Hi. replace i with 0 in Hout by lia. contradiction.
    Qed.

    Lemma keepev_ce t j k i : nth_error (prog X t) j = Some k -> i < length (calls k) ->
      keepev X pend (ce X t j i) = keep X pend (t, j).
    Proof.
      intros Hj Hi. unfold keepev. change (th (ce X t j i)) with t.
      change (ix (ce X t j i)) with (off (prog X t) j + i).
      rewrite (loc_off _ _ _ _ Hj Hi). reflexivity.
    Qed.

    (** The present calls of dropped operations do not change the state. *)
    Lemma dropped_neutral e : In e (wit X) -> keepev X pend e = false -> neutral (call e) = true.
    Proof.
      intros He Hk. destruct (inc_decomp e He) as (t & j & k & i & Ht & Hj & Hi & E).
      assert (Hl : i < length (calls k)) by (apply nth_error_Some; congruence).
      rewrite E in Hk, He. rewrite (keepev_ce t j k i Hj Hl) in Hk.
      unfold keep in Hk. unfold blk in Hk. cbn [fst snd] in Hk. rewrite Hj in Hk.
      apply orb_false_iff in Hk as [_ Hm].
      destruct k as [vx vy|fs s a b|v|v].
      - exfalso. pose proof (acq_needed t j vx vy i Hj Hl He) as H0. apply present_iff in H0. congruence.
      - pose proof (calls_BR_kind fs s a b (call e) (nth_error_In _ _ Hi)) as Hc.
        destruct (call e); cbn in Hc |- *; first [reflexivity | contradiction].
      - exfalso. cbn in Hl. replace i with 0 in He by lia. apply present_iff in He. congruence.
      - destruct i as [|[|i]]; cbn in Hi; try discriminate. injection Hi as <-. reflexivity.
    Qed.

    (** A call of a kept operation. *)
    Definition kcall (e : Ev) : Prop :=
      exists t j k i, In t (ths X) /\ nth_error (prog X t) j = Some k /\ i < length (calls k) /\
                      keep X pend (t, j) = true /\ e = ce X t j i.

    Lemma Fk_kcall e : In e (Fk X pend) -> kcall e.
    Proof.
      unfold Fk. intros H. apply filter_In in H as [He Hk].
      destruct (inc_decomp e He) as (t & j & k & i & Ht & Hj & Hi & E).
      assert (Hl : i < length (calls k)) by (apply nth_error_Some; congruence).
      exists t, j, k, i. split; [exact Ht|]. split; [exact Hj|]. split; [exact Hl|]. split; [|exact E].
      rewrite E in Hk. rewrite (keepev_ce t j k i Hj Hl) in Hk. exact Hk.
    Qed.

    Lemma Fk_wit e : In e (Fk X pend) -> In e (wit X).
    Proof. unfold Fk. intros H. apply filter_In in H. tauto. Qed.

    Lemma missing_kcall e : In e (missing X) -> kcall e /\ ~ In e (wit X).
    Proof.
      intros H.
      destruct missing_cases as [[E _]|(tw & jw & vx & vy & Hw & Hbw & Ha & Hr & E)];
        rewrite E in H; [contradiction|].
      apply filter_In in H as [H Hp]. apply in_map_iff in H as (i & <- & Hi). apply in_seq in Hi.
      split.
      - exists tw, jw, (BW vx vy), i. split; [exact (ops_ths X _ Hw)|]. split; [exact Hbw|].
        split; [cbn; lia|]. split; [|reflexivity].
        unfold keep, blk. cbn [fst snd]. rewrite Hbw. apply orb_true_iff. right. apply present_iff, Ha.
      - intros H. apply present_iff in H. rewrite H in Hp. discriminate.
    Qed.

    Lemma kcall_L e : kcall e -> In e (Lc X pend).
    Proof.
      intros (t & j & k & i & Ht & Hj & Hi & Hk & ->). unfold Lc. apply in_or_app.
      destruct (kept_cases t j k i Ht Hj Hi Hk) as [H|H]; [left|right; exact H].
      unfold Fk. apply filter_In. split; [exact H|]. rewrite (keepev_ce t j k i Hj Hi). exact Hk.
    Qed.

    Lemma L_kcall e : In e (Lc X pend) -> kcall e.
    Proof.
      unfold Lc. intros H.
      apply in_app_or in H as [H|H]; [apply Fk_kcall, H | exact (proj1 (missing_kcall e H))].
    Qed.

    Lemma missing_nodup : NoDup (missing X).
    Proof.
      destruct missing_cases as [[E _]|(tw & jw & vx & vy & _ & _ & _ & _ & E)]; rewrite E; [constructor|].
      apply NoDup_filter. apply NoDup_map_inj; [|apply seq_NoDup].
      intros x y _ _ Exy. unfold ce, evt in Exy. injection Exy as Ei _. lia.
    Qed.

    Lemma L_nodup : NoDup (Lc X pend).
    Proof.
      unfold Lc. apply NoDup_app.
      - apply NoDup_filter, (wfi_nodup _ _ _ _ HI).
      - apply missing_nodup.
      - intros e H1 H2. exact (proj2 (missing_kcall e H2) (Fk_wit e H1)).
    Qed.

    Lemma idx_map_ce t j a n i : a <= i < a + n -> idx (ce X t j i) (map (ce X t j) (seq a n)) = i - a.
    Proof.
      revert a. induction n as [|n IH]; intros a Hi; [lia|]. cbn [seq map idx].
      destruct (Ev_eq_dec (ce X t j i) (ce X t j a)) as [E|Hne].
      - unfold ce, evt in E. injection E as Ei _. lia.
      - destruct (Nat.eq_dec i a) as [->|Hia]; [contradiction|]. rewrite (IH (S a)) by lia. lia.
    Qed.

    (** The new witness respects the preserved order: the missing calls
        come last, and nothing present depends on them ([wfi_closed]). *)
    Lemma L_pres e1 e2 : In e1 (Lc X pend) -> In e2 (Lc X pend) -> th e1 = th e2 -> ix e1 < ix e2 ->
      upres rc K (call e1) (call e2) = true -> idx e1 (Lc X pend) < idx e2 (Lc X pend).
    Proof.
      intros H1 H2 Et Hlt Hu. unfold Lc in *.
      apply in_app_or in H1 as [H1|H1]; apply in_app_or in H2 as [H2|H2].
      - rewrite !idx_app_l by assumption. unfold Fk in *.
        apply filter_In in H1 as [W1 K1]. apply filter_In in H2 as [W2 K2].
        apply idx_filter_lt; try assumption. exact (wfi_pres _ _ _ _ HI e1 e2 W1 W2 Et Hlt Hu).
      - rewrite idx_app_l by assumption.
        rewrite idx_app_r by (intros H; exact (proj2 (missing_kcall e2 H2) (Fk_wit e2 H))).
        pose proof (idx_lt e1 _ H1). lia.
      - exfalso. destruct (missing_kcall e1 H1) as [(t & j & k & i & _ & _ & _ & _ & E1) Habs].
        apply Habs. pose proof (Fk_wit e2 H2) as W2.
        assert (E : evt X (th e2) (ix e1) = e1) by (rewrite <- Et, E1; reflexivity).
        pose proof (wfi_closed _ _ _ _ HI e2 (ix e1) W2 Hlt) as Hc. rewrite E in Hc. exact (Hc Hu).
      - pose proof (proj2 (missing_kcall e1 H1)) as N1. pose proof (proj2 (missing_kcall e2 H2)) as N2.
        rewrite !idx_app_r by (intros H; apply Fk_wit in H; contradiction).
        apply Nat.add_lt_mono_l.
        destruct missing_cases as [[E _]|(tw & jw & vx & vy & _ & _ & _ & _ & E)];
          rewrite E in *; [contradiction|].
        pose proof H1 as H1'. pose proof H2 as H2'.
        apply filter_In in H1 as [H1 G1]. apply filter_In in H2 as [H2 G2].
        apply idx_filter_lt; try assumption.
        apply in_map_iff in H1 as (i1 & <- & I1). apply in_map_iff in H2 as (i2 & <- & I2).
        apply in_seq in I1. apply in_seq in I2.
        rewrite !idx_map_ce by lia. cbn [ce evt ix] in Hlt. lia.
    Qed.

    (** The new witness is valid: dropped calls are neutral, and the open
        write still holds the lock when its missing calls are appended. *)
    Lemma L_valid p e : nth_error (Lc X pend) p = Some e -> pre (run init (firstn p (Lc X pend))) e = true.
    Proof.
      unfold Lc. intros Hp.
      assert (Hneu : forall x, In x (wit X) -> keepev X pend x = false -> neutral (call x) = true)
        by exact dropped_neutral.
      destruct (Nat.lt_ge_cases p (length (Fk X pend))) as [Hlt|Hge].
      - rewrite nth_error_app1 in Hp by exact Hlt.
        rewrite firstn_app. replace (p - length (Fk X pend)) with 0 by lia. rewrite firstn_O, app_nil_r.
        unfold Fk in Hp |- *. destruct (run_filter_nth _ _ init p e Hneu Hp) as (P & HP & E).
        rewrite E. exact (wfi_valid _ _ _ _ HI P e HP).
      - rewrite nth_error_app2 in Hp by exact Hge.
        rewrite firstn_app, firstn_all2 by lia. rewrite run_app.
        unfold Fk at 1. rewrite (run_filter _ _ init Hneu).
        pose proof missing_nodup as Hnd.
        set (m := p - length (Fk X pend)) in *.
        destruct missing_cases as [[E _]|(tw & jw & vx & vy & Hw & Hbw & Ha & Hr & E)];
          rewrite E in Hp, Hnd |- *; [destruct m; discriminate|].
        assert (Hin : In e (filter (fun e => negb (present X e)) (map (ce X tw jw) (seq 0 6))))
          by (eapply nth_error_In; exact Hp).
        apply filter_In in Hin as [Hin Habs]. apply in_map_iff in Hin as (i & <- & Hi). apply in_seq in Hi.
        destruct i as [|[|[|[|[|[|i]]]]]]; try lia.
        + exfalso. apply present_iff in Ha. rewrite Ha in Habs. discriminate.
        + unfold pre. rewrite (ce_call X tw jw _ 1 WmbC Hbw eq_refl). reflexivity.
        + unfold pre. rewrite (ce_call X tw jw _ 2 (WrX vx) Hbw eq_refl). reflexivity.
        + unfold pre. rewrite (ce_call X tw jw _ 3 (WrY vy) Hbw eq_refl). reflexivity.
        + unfold pre. rewrite (ce_call X tw jw _ 4 WmbC Hbw eq_refl). reflexivity.
        + unfold pre. rewrite (ce_call X tw jw _ 5 Rel Hbw eq_refl).
          rewrite hold_run, (final_hold tw jw vx vy Hbw Ha Hr); [apply Nat.eqb_refl|].
          intros x Hx.
          pose proof (nodup_firstn_neq _ _ _ _ Hnd Hp Hx) as Hne.
          assert (Hx' : In x (filter (fun e => negb (present X e)) (map (ce X tw jw) (seq 0 6))))
            by (rewrite <- (firstn_skipn m (filter _ _)); apply in_or_app; left; exact Hx).
          apply filter_In in Hx' as [Hx' Hxa]. apply in_map_iff in Hx' as (i' & <- & Hi'). apply in_seq in Hi'.
          destruct i' as [|[|[|[|[|[|i']]]]]]; try lia.
          * exfalso. apply present_iff in Ha. rewrite Ha in Hxa. discriminate.
          * rewrite (ce_call X tw jw _ 1 WmbC Hbw eq_refl). split; discriminate.
          * rewrite (ce_call X tw jw _ 2 (WrX vx) Hbw eq_refl). split; discriminate.
          * rewrite (ce_call X tw jw _ 3 (WrY vy) Hbw eq_refl). split; discriminate.
          * rewrite (ce_call X tw jw _ 4 WmbC Hbw eq_refl). split; discriminate.
          * contradiction.
    Qed.

    (** **** Re-indexing *)

    Lemma emap_ce t j k i : nth_error (prog X t) j = Some k -> i < length (calls k) ->
      emap X pend (ce X t j i) = mkEv t (off (cprog X pend t) (cnt (kp X pend t) j) + i) (call (ce X t j i)).
    Proof.
      intros Hj Hi. unfold emap. change (th (ce X t j i)) with t.
      change (ix (ce X t j i)) with (off (prog X t) j + i).
      rewrite (loc_off _ _ _ _ Hj Hi). reflexivity.
    Qed.

    Lemma cprog_nth t j k : nth_error (prog X t) j = Some k -> keep X pend (t, j) = true ->
      nth_error (cprog X pend t) (cnt (kp X pend t) j) = Some k.
    Proof. intros Hj Hk. apply fprog_nth; assumption. Qed.

    Lemma emap_evt t j k i : nth_error (prog X t) j = Some k -> i < length (calls k) ->
      keep X pend (t, j) = true ->
      emap X pend (ce X t j i) = ce (completion X pend) t (cnt (kp X pend t) j) i.
    Proof.
      intros Hj Hi Hk. rewrite (emap_ce t j k i Hj Hi).
      destruct (nth_error (calls k) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
      rewrite (ce_call X t j k i c Hj Hc). unfold ce, evt. cbn [prog completion]. f_equal.
      symmetry. apply nth_error_nth.
      rewrite (trace_off' _ _ _ _ (cprog_nth t j k Hj Hk) Hi). exact Hc.
    Qed.

    Lemma emap_inj e1 e2 : kcall e1 -> kcall e2 -> emap X pend e1 = emap X pend e2 -> e1 = e2.
    Proof.
      intros (t1 & j1 & k1 & i1 & Ht1 & Hj1 & Hi1 & Hk1 & ->)
             (t2 & j2 & k2 & i2 & Ht2 & Hj2 & Hi2 & Hk2 & ->) E.
      rewrite (emap_ce _ _ _ _ Hj1 Hi1), (emap_ce _ _ _ _ Hj2 Hi2) in E.
      injection E as Et Ei _. subst t2.
      destruct (off_inj _ _ _ _ _ _ _ (cprog_nth t1 j1 k1 Hj1 Hk1) Hi1 (cprog_nth t1 j2 k2 Hj2 Hk2) Hi2 Ei)
        as [Ej ->].
      rewrite (cnt_inj (kp X pend t1) j1 j2 Hk1 Hk2 Ej). reflexivity.
    Qed.

    Lemma emap_lt t j1 k1 i1 j2 k2 i2 :
      nth_error (prog X t) j1 = Some k1 -> i1 < length (calls k1) -> keep X pend (t, j1) = true ->
      nth_error (prog X t) j2 = Some k2 -> i2 < length (calls k2) -> keep X pend (t, j2) = true ->
      off (cprog X pend t) (cnt (kp X pend t) j1) + i1 < off (cprog X pend t) (cnt (kp X pend t) j2) + i2 ->
      off (prog X t) j1 + i1 < off (prog X t) j2 + i2.
    Proof.
      intros Hj1 Hi1 Hk1 Hj2 Hi2 Hk2 Hlt.
      apply (off_cmp _ _ _ _ _ _ _ Hj1 Hi1 Hj2 Hi2).
      apply (off_cmp _ _ _ _ _ _ _ (cprog_nth t j1 k1 Hj1 Hk1) Hi1 (cprog_nth t j2 k2 Hj2 Hk2) Hi2) in Hlt.
      destruct Hlt as [Hlt|[Ej Hlt]].
      - left. apply (cnt_lt_iff (kp X pend t) j1 j2 Hk1 Hk2). exact Hlt.
      - right. split; [exact (cnt_inj (kp X pend t) j1 j2 Hk1 Hk2 Ej)|exact Hlt].
    Qed.

    Lemma run_emap s l : run s (map (emap X pend) l) = run s l.
    Proof.
      revert s. induction l as [|x l IH]; intros s; cbn; [reflexivity|].
      rewrite (proj2 (pre_post_ext (emap X pend x) x eq_refl eq_refl)). apply IH.
    Qed.

    Lemma L_inj x y : In x (Lc X pend) -> In y (Lc X pend) -> emap X pend x = emap X pend y -> x = y.
    Proof. intros Hx Hy. apply emap_inj; apply L_kcall; assumption. Qed.

    (** **** The completion is a complete execution *)

    Theorem completion_wf : WF rc K (completion X pend).
    Proof.
      constructor; cbn [wit ths prog completion].
      - apply NoDup_map_inj; [exact L_inj | exact L_nodup].
      - exact (wfi_ths _ _ _ _ HI).
      - intros e' He'. apply in_map_iff in He' as (e & <- & He).
        destruct (L_kcall e He) as (t & j & k & i & Ht & Hj & Hi & Hk & ->).
        rewrite (emap_evt t j k i Hj Hi Hk). split; [exact Ht|].
        destruct (nth_error (calls k) i) as [c|] eqn:Hc; [|apply nth_error_None in Hc; lia].
        exact (evt_nth _ _ _ (proj2 (blk_evt (completion X pend) t _ k i c (cprog_nth t j k Hj Hk) Hc))).
      - intros t i' Ht Hi'.
        destruct (nth_error (trace (cprog X pend t)) i') as [c|] eqn:Hc;
          [|apply nth_error_None in Hc; cbn in Hi'; lia].
        destruct (trace_inv _ _ _ Hc) as (j' & k & i & Hj' & -> & Hk).
        assert (Hl' : j' < length (cprog X pend t)) by (apply nth_error_Some; congruence).
        destruct (unc_spec (kp X pend t) (prog X t) j' Hl') as (Hkp & Hcnt & Hnth).
        assert (Hj : nth_error (prog X t) (unc (kp X pend t) (prog X t) j') = Some k)
          by (rewrite Hnth; exact Hj').
        assert (Hi : i < length (calls k)) by (apply nth_error_Some; congruence).
        apply in_map_iff. exists (ce X t (unc (kp X pend t) (prog X t) j') i). split.
        + rewrite (emap_evt t _ k i Hj Hi Hkp), Hcnt. reflexivity.
        + apply kcall_L. exists t, (unc (kp X pend t) (prog X t) j'), k, i.
          split; [exact Ht|]. split; [exact Hj|]. split; [exact Hi|]. split; [exact Hkp|reflexivity].
      - intros e1' e2' He1 He2 Et Hlt Hu.
        apply in_map_iff in He1 as (e1 & <- & He1). apply in_map_iff in He2 as (e2 & <- & He2).
        rewrite (idx_map _ _ _ L_inj He1), (idx_map _ _ _ L_inj He2).
        apply L_pres; [exact He1|exact He2|exact Et| |exact Hu].
        destruct (L_kcall e1 He1) as (t1 & j1 & k1 & i1 & Ht1 & Hj1 & Hi1 & Hk1 & E1).
        destruct (L_kcall e2 He2) as (t2 & j2 & k2 & i2 & Ht2 & Hj2 & Hi2 & Hk2 & E2).
        subst e1 e2. change (t1 = t2) in Et. subst t2.
        rewrite (emap_ce _ _ _ _ Hj1 Hi1), (emap_ce _ _ _ _ Hj2 Hi2) in Hlt. cbn [ix] in Hlt.
        exact (emap_lt t1 j1 k1 i1 j2 k2 i2 Hj1 Hi1 Hk1 Hj2 Hi2 Hk2 Hlt).
      - intros p e' Hp. rewrite nth_error_map in Hp.
        destruct (nth_error (Lc X pend) p) as [e|] eqn:He; cbn in Hp; [|discriminate]. injection Hp as <-.
        unfold at_. cbn [wit completion]. rewrite firstn_map, run_emap.
        rewrite (proj1 (pre_post_ext (emap X pend e) e eq_refl eq_refl)).
        exact (L_valid p e He).
    Qed.

    (** **** Operations of the completion *)

    Lemma psi_spec q' : In q' (all_ops (completion X pend)) ->
      keep X pend (psi X pend q') = true /\ cnt (kp X pend (fst q')) (snd (psi X pend q')) = snd q' /\
      blk X (psi X pend q') = blk (completion X pend) q' /\ In (psi X pend q') (all_ops X).
    Proof.
      intros H. apply all_ops_In in H as [Ht Hl]. cbn in Hl.
      destruct (unc_spec (kp X pend (fst q')) (prog X (fst q')) (snd q') Hl) as (H1 & H2 & H3).
      split; [exact H1|]. split; [exact H2|]. split; [exact H3|].
      apply all_ops_In. split; [exact Ht|]. exact (unc_lt _ _ _ Hl).
    Qed.

    Theorem completion_psi : Psi_ok X (completion X pend) pend (psi X pend).
    Proof.
      constructor.
      - reflexivity.
      - intros q' H. exact (proj2 (proj2 (proj2 (psi_spec q' H)))).
      - intros q1 q2 H1 H2 E.
        destruct (psi_spec q1 H1) as (_ & C1 & _). destruct (psi_spec q2 H2) as (_ & C2 & _).
        destruct q1 as [t1 j1], q2 as [t2 j2]. unfold psi in E, C1, C2. cbn [fst snd] in *.
        injection E as <- Ej. rewrite Ej in C1. congruence.
      - intros q' H. symmetry. exact (proj1 (proj2 (proj2 (psi_spec q' H)))).
      - intros q' H. unfold ovl. rewrite (proj1 (proj2 (proj2 (psi_spec q' H)))). reflexivity.
      - reflexivity.
      - intros q1 q2 H1 H2 Et.
        destruct (psi_spec q1 H1) as (K1 & C1 & _). destruct (psi_spec q2 H2) as (K2 & C2 & _).
        destruct q1 as [t j1], q2 as [t2 j2]. cbn [fst] in Et. subst t2.
        unfold psi in *. cbn [fst snd] in *.
        rewrite <- C1, <- C2 at 1. apply cnt_lt_iff; assumption.
      - intros [t j] Hq Hp.
        assert (Hk : keep X pend (t, j) = true) by (unfold keep; rewrite Hp; reflexivity).
        apply all_ops_In in Hq as [Ht Hj]. cbn [fst snd] in Ht, Hj.
        exists (t, cnt (kp X pend t) j). split.
        + apply all_ops_In. split; [exact Ht|]. exact (cnt_lt_length (kp X pend t) (prog X t) j Hk Hj).
        + unfold psi. cbn [fst snd]. rewrite (unc_cnt (kp X pend t) (prog X t) j Hk Hj). reflexivity.
      - intros q Hq Hn. destruct (pend q) eqn:Hp; [reflexivity|]. exfalso.
        (* the completed operation is in the image *)
        destruct q as [t j].
        assert (Hk : keep X pend (t, j) = true) by (unfold keep; rewrite Hp; reflexivity).
        apply all_ops_In in Hq as [Ht Hj]. cbn [fst snd] in Ht, Hj.
        apply (Hn (t, cnt (kp X pend t) j)).
        + apply all_ops_In. split; [exact Ht|]. exact (cnt_lt_length (kp X pend t) (prog X t) j Hk Hj).
        + unfold psi. cbn [fst snd]. rewrite (unc_cnt (kp X pend t) (prog X t) j Hk Hj). reflexivity.
    Qed.

    (** Only writes and z-writes survive while pending. *)
    Lemma completion_pending_kind q' : In q' (all_ops (completion X pend)) -> pend (psi X pend q') = true ->
      match blk X (psi X pend q') with Some (BW _ _) | Some (BZw _) => True | _ => False end.
    Proof.
      intros H Hp. destruct (psi_spec q' H) as (Hk & _).
      unfold keep in Hk. rewrite Hp in Hk. cbn [negb orb] in Hk.
      destruct (blk X (psi X pend q')) as [[]|]; first [exact I | discriminate].
    Qed.

    (** **** Real time of the completion *)

    Section CompRT.
      Context (T : Timing).
      Hypothesis HT : RT_ok X T.
      Hypothesis Hpend : forall q, In q (all_ops X) -> (pend q = true <-> ores T q = None).

      Lemma find_Fk e :
        In e (Fk X pend) -> find (fun x => Ev_eqb (emap X pend x) (emap X pend e)) (Fk X pend) = Some e.
      Proof.
        intros He. destruct (find (fun x => Ev_eqb (emap X pend x) (emap X pend e)) (Fk X pend)) as [x|] eqn:F.
        - apply find_some in F as [Hx Ex]. apply Ev_eqb_eq in Ex. f_equal.
          exact (emap_inj x e (Fk_kcall x Hx) (Fk_kcall e He) Ex).
        - exfalso. pose proof (find_none _ _ F e He) as H. cbn in H.
          unfold Ev_eqb in H. destruct (Ev_eq_dec _ _); congruence.
      Qed.

      Lemma find_out e : kcall e -> ~ In e (Fk X pend) ->
        find (fun x => Ev_eqb (emap X pend x) (emap X pend e)) (Fk X pend) = None.
      Proof.
        intros Hk Hn.
        destruct (find (fun x => Ev_eqb (emap X pend x) (emap X pend e)) (Fk X pend)) as [x|] eqn:F;
          [|reflexivity].
        exfalso. apply find_some in F as [Hx Ex]. apply Ev_eqb_eq in Ex.
        apply Hn. rewrite <- (emap_inj x e (Fk_kcall x Hx) Hk Ex). exact Hx.
      Qed.

      Lemma cop_call t j' k i : nth_error (cprog X pend t) j' = Some k -> i < length (calls k) ->
        nth_error (prog X t) (unc (kp X pend t) (prog X t) j') = Some k /\
        keep X pend (t, unc (kp X pend t) (prog X t) j') = true /\
        ce (completion X pend) t j' i = emap X pend (ce X t (unc (kp X pend t) (prog X t) j') i).
      Proof.
        intros Hj' Hi. assert (Hl : j' < length (cprog X pend t)) by (apply nth_error_Some; congruence).
        destruct (unc_spec (kp X pend t) (prog X t) j' Hl) as (Hk & Hc & Hn).
        assert (Hj : nth_error (prog X t) (unc (kp X pend t) (prog X t) j') = Some k)
          by (rewrite Hn; exact Hj').
        split; [exact Hj|]. split; [exact Hk|].
        rewrite (emap_evt t _ k i Hj Hi Hk), Hc. reflexivity.
      Qed.

      Lemma Fk_ce t j k i : nth_error (prog X t) j = Some k -> i < length (calls k) ->
        keep X pend (t, j) = true -> In (ce X t j i) (wit X) -> In (ce X t j i) (Fk X pend).
      Proof.
        intros Hj Hi Hk Hin. unfold Fk. apply filter_In. split; [exact Hin|].
        rewrite (keepev_ce t j k i Hj Hi). exact Hk.
      Qed.

      Theorem ctiming_ok : RT_ok (completion X pend) (ctiming X pend T).
      Proof.
        pose proof (completion_wf) as HW'.
        constructor; cbn [oinv ores cinv cres ctiming].
        - intros [t j'] k i Hb Hi Hin. cbn [fst snd] in *.
          destruct (wf_call _ _ _ HW' _ Hin) as [Ht _]. change (In t (ths X)) in Ht.
          destruct (cop_call t j' k i Hb Hi) as (Hj & Hk & E). rewrite E.
          set (j := unc (kp X pend t) (prog X t) j') in *.
          change (psi X pend (t, j')) with (t, j).
          destruct (In_dec Ev_eq_dec (ce X t j i) (Fk X pend)) as [HF|HF].
          + rewrite (find_Fk _ HF).
            exact (rt_inv _ _ HT (t, j) k i Hj Hi (Fk_wit _ HF)).
          + assert (Hkc : kcall (ce X t j i)) by (exists t, j, k, i; auto).
            rewrite (find_out _ Hkc HF).
            apply le_list_max. apply in_map. apply all_ops_In. split; [exact Ht|].
            apply nth_error_Some. cbn [snd fst]. congruence.
        - intros [t j'] k i r Hb Hi Hin Hr. cbn [fst snd] in *.
          destruct (wf_call _ _ _ HW' _ Hin) as [Ht _]. change (In t (ths X)) in Ht.
          destruct (cop_call t j' k i Hb Hi) as (Hj & Hk & E). rewrite E.
          set (j := unc (kp X pend t) (prog X t) j') in *.
          change (psi X pend (t, j')) with (t, j) in Hr.
          assert (Hp : pend (t, j) = false).
          { destruct (pend (t, j)) eqn:P; [|reflexivity].
            rewrite (proj1 (Hpend (t, j) (all_ops_of X t j k Ht Hj)) P) in Hr. discriminate. }
          pose proof (wfi_complete _ _ _ _ HI t j k i Ht Hj Hp Hi) as Hin0.
          rewrite (find_Fk _ (Fk_ce t j k i Hj Hi Hk Hin0)).
          exact (rt_res _ _ HT (t, j) k i r Hj Hi Hin0 Hr).
        - intros e' r He' Hr.
          destruct (find (fun e => Ev_eqb (emap X pend e) e') (Fk X pend)) as [e|] eqn:F; [|discriminate].
          apply find_some in F as [HF _]. exact (rt_call _ _ HT e r (Fk_wit _ HF) Hr).
        - intros e1' e2' r He1 He2 Hr Hlt. cbn [wit completion] in He1, He2 |- *.
          destruct (find (fun e => Ev_eqb (emap X pend e) e1') (Fk X pend)) as [e1|] eqn:F1; [|discriminate].
          apply find_some in F1 as [HF1 E1]. apply Ev_eqb_eq in E1. subst e1'.
          assert (HL1 : In e1 (Lc X pend)) by (apply in_or_app; left; exact HF1).
          apply in_map_iff in He2 as (e2 & <- & HL2).
          rewrite (idx_map _ _ _ L_inj HL1), (idx_map _ _ _ L_inj HL2). unfold Lc.
          rewrite (idx_app_l e1 _ _ HF1).
          destruct (In_dec Ev_eq_dec e2 (Fk X pend)) as [HF2|HF2].
          + rewrite (find_Fk _ HF2) in Hlt. rewrite (idx_app_l e2 _ _ HF2).
            pose proof (rt_wit _ _ HT e1 e2 r (Fk_wit _ HF1) (Fk_wit _ HF2) Hr Hlt) as H.
            unfold Fk in *. apply filter_In in HF1 as [W1 G1]. apply filter_In in HF2 as [W2 G2].
            apply idx_filter_lt; assumption.
          + rewrite (idx_app_r e2 _ _ HF2). pose proof (idx_lt e1 _ HF1). lia.
      Qed.
    End CompRT.

  End Inc.

  (** *** Completion and the headline theorems *)

  Theorem complete_execution rc K X pend :
    WF_inc rc K X pend -> K_ok K = true ->
    exists X' f, WF rc K X' /\ Psi_ok X X' pend f.
  Proof.
    intros HI HK. exists (completion X pend), (psi X pend).
    split; [exact (completion_wf rc K X pend HI HK) | exact (completion_psi X pend)].
  Qed.

  (** Every incomplete execution of SeqLock ⊗ COH[z]: its completed
      operations, together with possibly the pending write that holds the
      lock and the pending z-writes already performed, satisfy the
      conclusion of [WindowTable] with read ↦ rmb, write ↦ wmb.  For the
      statement to be meaningful, [pend] must be the set of operations
      without a response: [pend] is a parameter here, and with
      [pend ≡ true] completeness is vacuous and every read is dropped.
      [incomplete_seqlock_z_rt] ties it to the timing. *)
  Theorem incomplete_seqlock_z rc K X pend :
    WF_inc rc K X pend -> K_ok K = true ->
    exists X' f, Psi_ok X X' pend f /\ WT.Conclusion (dtable rc) (setting sl_cf rc K X').
  Proof.
    intros HI HK. destruct (complete_execution rc K X pend HI HK) as (X' & f & HW & Hp).
    exists X', f. split; [exact Hp|]. exact (seqlock_z_composition rc K X' HW HK).
  Qed.

  (** The headline theorem: the same, with [pend] the operations without
      response in the timing, and with the real-time order of the
      incomplete execution, transported along the map. *)
  Theorem incomplete_seqlock_z_rt rc K X pend T :
    WF_inc rc K X pend -> K_ok K = true -> RT_ok X T ->
    (forall q, In q (all_ops X) -> (pend q = true <-> ores T q = None)) ->
    exists X' f T', Psi_ok X X' pend f /\ RT_ok X' T' /\
      (forall q', oinv T' q' = oinv T (f q') /\ ores T' q' = ores T (f q')) /\
      WT.Conclusion (dtable rc) (setting_rt sl_cf rc K X' T').
  Proof.
    intros HI HK HT Hpend. exists (completion X pend), (psi X pend), (ctiming X pend T).
    pose proof (ctiming_ok rc K X pend HI HK T HT Hpend) as HT'.
    split; [exact (completion_psi X pend)|]. split; [exact HT'|].
    split; [intros q'; split; reflexivity|].
    exact (seqlock_z_composition_rt rc K _ _ (completion_wf rc K X pend HI HK) HK HT').
  Qed.

  (** Real time on the completion is real time on [X]. *)
  Lemma rt_of_transport (T T' : Timing) (f : nat * nat -> nat * nat) q1 q2 :
    (forall q', oinv T' q' = oinv T (f q') /\ ores T' q' = ores T (f q')) ->
    rt_of T' q1 q2 <-> rt_of T (f q1) (f q2).
  Proof.
    intros H. unfold rt_of. destruct (H q1) as [_ E1]. destruct (H q2) as [E2 _]. rewrite E1, E2. reflexivity.
  Qed.

  (** With [pend] read off the timing. *)
  Definition pending (T : Timing) (q : nat * nat) : bool :=
    match ores T q with None => true | Some _ => false end.

  Corollary incomplete_seqlock_z_timed rc K X T :
    WF_inc rc K X (pending T) -> K_ok K = true -> RT_ok X T ->
    exists X' f T', Psi_ok X X' (pending T) f /\ RT_ok X' T' /\
      (forall q', oinv T' q' = oinv T (f q') /\ ores T' q' = ores T (f q')) /\
      WT.Conclusion (dtable rc) (setting_rt sl_cf rc K X' T').
  Proof.
    intros HI HK HT. apply (incomplete_seqlock_z_rt rc K X (pending T) T HI HK HT).
    intros q _. unfold pending. destruct (ores T q); split; congruence.
  Qed.

  (** *** Example: a writer holding the lock, a torn pending read *)

  Definition wfib (rc : bool) (K : TLCats) (X : Exec) (pend : nat * nat -> bool) : bool :=
    nodupb Ev_eqb (wit X) && nodupb Nat.eqb (ths X)
    && forallb (fun e => existsb (Nat.eqb (th e)) (ths X)
                         && optUC_eqb (nth_error (trace (prog X (th e))) (ix e)) (Some (call e))) (wit X)
    && forallb (fun q => implb (negb (pend q))
                           (forallb (fun i => present X (ce X (fst q) (snd q) i)) (seq 0 (ncalls X q))))
               (all_ops X)
    && forallb (fun e => forallb (fun i => implb (upres rc K (call (evt X (th e) i)) (call e))
                                                 (present X (evt X (th e) i))) (seq 0 (ix e))) (wit X)
    && forallb (fun e1 => forallb (fun e2 =>
          implb (Nat.eqb (th e1) (th e2) && Nat.ltb (ix e1) (ix e2) && upres rc K (call e1) (call e2))
                (Nat.ltb (idx e1 (wit X)) (idx e2 (wit X)))) (wit X)) (wit X)
    && forallb (fun p => match nth_error (wit X) p with Some e => pre (at_ X p) e | None => true end)
               (seq 0 (length (wit X))).

  Lemma wfib_sound rc K X pend : wfib rc K X pend = true -> WF_inc rc K X pend.
  Proof.
    unfold wfib. intros H.
    apply andb_true_iff in H as [H Hval]. apply andb_true_iff in H as [H Hpres].
    apply andb_true_iff in H as [H Hclo]. apply andb_true_iff in H as [H Hcomp].
    apply andb_true_iff in H as [H Hcall]. apply andb_true_iff in H as [Hnd Hth].
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
    - intros t j k i Ht Hj Hp Hi. rewrite forallb_forall in Hcomp.
      specialize (Hcomp (t, j) (all_ops_of X t j k Ht Hj)). rewrite Hp in Hcomp. cbn [negb implb] in Hcomp.
      rewrite forallb_forall in Hcomp. apply present_iff. apply Hcomp. apply in_seq.
      unfold ncalls, blk. cbn [fst snd]. rewrite Hj. lia.
    - intros e i He Hi Hu. rewrite forallb_forall in Hclo. specialize (Hclo e He).
      rewrite forallb_forall in Hclo. specialize (Hclo i ltac:(apply in_seq; lia)).
      rewrite Hu in Hclo. cbn [implb] in Hclo. apply present_iff, Hclo.
    - intros e1 e2 He1 He2 Et Hi Hu. rewrite forallb_forall in Hpres. specialize (Hpres e1 He1).
      rewrite forallb_forall in Hpres. specialize (Hpres e2 He2).
      rewrite Et, Nat.eqb_refl, Hu in Hpres. apply Nat.ltb_lt in Hi. rewrite Hi in Hpres.
      cbn in Hpres. apply Nat.ltb_lt, Hpres.
    - intros p e Hn. rewrite forallb_forall in Hval.
      assert (Hp : In p (seq 0 (length (wit X))))
        by (apply in_seq; split; [lia|]; apply nth_error_Some; congruence).
      specialize (Hval p Hp). rewrite Hn in Hval. exact Hval.
  Qed.

  (** Thread 0: [write(1,1)], pending with [acq], the first [wmb] and
      [x := 1] present, followed by a completed z-read returning 0
      ([BZr 0]), which is present although the write is pending: no
      preserved edge leads from the write's absent calls to its [RdZ].
      A thread with a pending operation followed by a completed one is
      allowed by the futures semantics (a thread may invoke while its
      earlier invocations are still active).  Thread 1: a completed
      [read() = (0,0)].  Thread 2: a pending read whose first iteration
      saw the torn (1,0) and failed, and whose retry has only
      [get_ticket] present. *)
  Definition inc_wit : list Ev :=
    [ mkEv 1 0 (GT 0); mkEv 1 1 RmbC; mkEv 1 2 (RdX 0); mkEv 1 3 (RdY 0); mkEv 1 4 RmbC;
      mkEv 1 5 (TT 0 false);
      mkEv 0 0 Acq; mkEv 0 1 WmbC; mkEv 0 2 (WrX 1);
      mkEv 2 0 (GT 1); mkEv 2 1 RmbC; mkEv 2 2 (RdX 1); mkEv 2 3 (RdY 0); mkEv 2 4 RmbC;
      mkEv 2 5 (TT 1 true); mkEv 2 6 (GT 1);
      mkEv 0 6 (RdZ 0) ].

  Definition X_inc : Exec := {|
    ths := [0; 1; 2];
    prog := fun t => match t with
                     | 0 => [BW 1 1; BZr 0]
                     | 1 => [BR [] 0 0 0]
                     | _ => [BR [(1, 1, 0)] 1 1 1]
                     end;
    wit := inc_wit |}.

  Definition pend_inc (q : nat * nat) : bool :=
    match q with (0, 0) | (2, 0) => true | _ => false end.

  Lemma inc_wf rc : WF_inc rc plainTL X_inc pend_inc.
  Proof. apply wfib_sound. destruct rc; vm_compute; reflexivity. Qed.

  (** The completion drops the pending read and appends [y := 1], [wmb],
      [rel] of the writer. *)
  Example inc_completion :
    prog (completion X_inc pend_inc) 2 = [] /\
    wit (completion X_inc pend_inc) =
      [ mkEv 1 0 (GT 0); mkEv 1 1 RmbC; mkEv 1 2 (RdX 0); mkEv 1 3 (RdY 0); mkEv 1 4 RmbC;
        mkEv 1 5 (TT 0 false);
        mkEv 0 0 Acq; mkEv 0 1 WmbC; mkEv 0 2 (WrX 1); mkEv 0 6 (RdZ 0);
        mkEv 0 3 (WrY 1); mkEv 0 4 WmbC; mkEv 0 5 Rel ].
  Proof. vm_compute. split; reflexivity. Qed.

  Corollary inc_allowed rc :
    exists X' f, Psi_ok X_inc X' pend_inc f /\ WT.Conclusion (dtable rc) (setting sl_cf rc plainTL X').
  Proof. exact (incomplete_seqlock_z rc plainTL X_inc pend_inc (inc_wf rc) plainTL_ok). Qed.
End SeqLockRT.
