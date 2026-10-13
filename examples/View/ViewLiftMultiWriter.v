(** * Two writers under TSO: what a blocking timeline presentation loses

    Memory with two locations [x] ([true]) and [y] ([false]), lifted with
    [ViewLift] and the TSO dependency table: a read need not follow an
    earlier write of its thread to the other location; every other pair
    is ordered.  Writes are appended and not synchronizing, reads may be
    timestamped in the past.

    The behaviour: thread 1 writes [x := 1], thread 2 writes [y := 1],
    thread 3 reads [y = 1] and then [x = 0].  On x86-TSO this happens even
    when thread 1's store is issued before thread 2's: thread 2's store
    buffer drains first.

    - [no_issue_order_run]: [VL TP] has no run in issue order (thread 1's
      write, thread 2's write, then the two reads), whatever the
      timestamps.  An appended write takes the position of its response,
      so the order of the writes on the timeline is their response order,
      and a blocking presentation responds when the store is issued.
    - [reorder_run]: the run in which thread 2's write responds first
      exists.  The two runs differ only in the order of steps of different
      threads.  (That a blocking client cannot tell the two orders apart is
      not formalized here.)
    - [reorder_canon], [reorder_rel_lin]: the canonical relaxed trace of
      that run delays thread 1's response past thread 3's read of [x]:
      thread 1's write overlaps the read.  This trace is relaxed
      linearizable.
    - [issue_trace_not_rel_lin]: the trace in which thread 1's write
      responds before thread 2's write is invoked is not relaxed
      linearizable.  So relaxed linearizability expresses the behaviour by
      overlap, not by the issue order either.
    - [poss_run_rel_lin]: the same overlapping trace, verified with a
      futures-style possibility run in [ViewPossibility] whose abstract
      responses form the run of [reorder_run].  This shows that the
      hypotheses of [ViewPossibility.timeline_rel_lin] are satisfiable by
      a non-SC behaviour. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import models.RelaxedSignature.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftAdequacy.
Require Import models.view.PrefixView.
Require Import models.view.ViewPossibility.
Import ListNotations.

Module ViewLiftMultiWriter.
  Import Reg LinCCALBase ViewLift.

  (** ** The object *)

  Variant TOp : Type := TW (l : bool) (v : nat) | TR (l : bool).

  Definition TAr (m : TOp) : Type := match m with TW _ _ => unit | TR _ => nat end.

  Canonical Structure ETSO := {| Sig.op := TOp; Sig.ar := TAr |}.

  Definition get (s : nat * nat) (l : bool) : nat := if l then fst s else snd s.

  Definition put (s : nat * nat) (l : bool) (v : nat) : nat * nat :=
    if l then (v, snd s) else (fst s, v).

  Definition tspec (s : nat * nat) (t : tid) (m : TOp) : TAr m -> nat * nat -> Prop :=
    match m as m0 return TAr m0 -> nat * nat -> Prop with
    | TW l v => fun _ s' => s' = put s l v
    | TR l => fun r s' => r = get s l /\ s' = s
    end.

  (** TSO: only a write followed by a read of the other location is
      unordered. *)
  Definition tdep (o m : TOp) : bool :=
    match o, m with TW l _, TR l' => Bool.eqb l l' | _, _ => true end.

  Definition TP : @Params ETSO := {|
    vl_state := nat * nat;
    vl_spec := tspec;
    vl_err := fun _ _ _ => False;
    vl_retro := fun m => match m with TR _ => true | TW _ _ => false end;
    vl_dep := tdep;
    vl_sync := fun _ => false;
  |}.

  Definition s00 : nat * nat := (O, O).

  Abbreviation Ent := (@ViewLiftAdequacy.Ent ETSO).
  Abbreviation mkEnt := (@ViewLiftAdequacy.mkEnt ETSO).

  Definition t1 : tid := 1%positive.
  Definition t2 : tid := 2%positive.
  Definition t3 : tid := 3%positive.

  Definition wx (h : positive) : Ent := mkEnt t1 (TW true 1) (tt : TAr (TW true 1)) h.
  Definition wy (h : positive) : Ent := mkEnt t2 (TW false 1) (tt : TAr (TW false 1)) h.
  Definition ry (h : positive) : Ent := mkEnt t3 (TR false) (1%nat : TAr (TR false)) h.
  Definition rx (h : positive) : Ent := mkEnt t3 (TR true) (0%nat : TAr (TR true)) h.

  (** ** Inverting runs *)

  Lemma run_snoc_inv R e s :
    ViewLiftAdequacy.Run TP s00 (R ++ [e]) s ->
    exists s1, ViewLiftAdequacy.Run TP s00 R s1 /\ ViewLiftAdequacy.RStep TP s1 e s.
  Proof.
    intros HR. remember (R ++ [e]) as l eqn:Hl. destruct HR as [|R' s1 e' s2 HR Hst].
    - destruct R; discriminate.
    - apply app_inj_tail in Hl as [-> ->]. eauto.
  Qed.

  Lemma run_nil_inv s : ViewLiftAdequacy.Run TP s00 [] s -> s = vinit TP s00.
  Proof.
    intros HR. remember [] as l eqn:Hl. destruct HR as [|R' s1 e' s2 HR Hst]; [reflexivity|].
    destruct R'; discriminate.
  Qed.

  (** ** Issue order is not a run *)

  Theorem no_issue_order_run h1 h2 h3 h4 s :
    ~ ViewLiftAdequacy.Run TP s00 [wx h1; wy h2; ry h3; rx h4] s.
  Proof.
    intros HR.
    apply (run_snoc_inv [wx h1; wy h2; ry h3]) in HR as (s3 & HR & R4).
    apply (run_snoc_inv [wx h1; wy h2]) in HR as (s2 & HR & R3).
    apply (run_snoc_inv [wx h1]) in HR as (s1 & HR & R2).
    apply (run_snoc_inv []) in HR as (s0' & HR & R1).
    apply run_nil_inv in HR. subst s0'.
    destruct R1 as (_ & _ & [(Hr & _) | (_ & Hh1 & st1 & Hsp1 & ->)]); [discriminate|].
    simpl in Hh1, Hsp1. subst st1.
    destruct R2 as (_ & _ & [(Hr & _) | (_ & Hh2 & st2 & Hsp2 & ->)]); [discriminate|].
    simpl in Hh2, Hsp2. subst st2.
    destruct R3 as (_ & _ & [(_ & Hsp3 & ->) | (Hr & _)]); [|discriminate].
    destruct R4 as (_ & Hdep4 & [(_ & Hsp4 & ->) | (Hr & _)]); [|discriminate].
    (* The read of [y] sees thread 2's write, so [h2 <= h3]. *)
    simpl in Hsp3. destruct Hsp3 as [Hy _]. unfold tl_write in Hy.
    destruct (Pos.leb h2 h3) eqn:E23; [apply Pos.leb_le in E23|];
      [|destruct (Pos.leb h1 h3); simpl in Hy; discriminate].
    (* The read of [x] is after the read of [y]. *)
    assert (H34 : Pos.lt h3 h4).
    { apply (Hdep4 (TR false) h3); [|reflexivity]. simpl. unfold push_past. simpl. left. reflexivity. }
    (* So it sees both writes. *)
    simpl in Hsp4. destruct Hsp4 as [Hx _]. unfold tl_write in Hx.
    rewrite (proj2 (Pos.leb_le h2 h4) ltac:(lia)), (proj2 (Pos.leb_le h1 h2) ltac:(lia)) in Hx.
    discriminate.
  Qed.

  (** ** The reordered run *)

  Definition reorder_R : list Ent := [wy 2; ry 3; wx 5; rx 4].

  Lemma reorder_run : exists s, ViewLiftAdequacy.Run TP s00 reorder_R s.
  Proof.
    eexists. change reorder_R with (((([] ++ [wy 2]) ++ [ry 3]) ++ [wx 5]) ++ [rx 4]).
    eapply ViewLiftAdequacy.run_snoc; [eapply ViewLiftAdequacy.run_snoc;
      [eapply ViewLiftAdequacy.run_snoc; [eapply ViewLiftAdequacy.run_snoc; [constructor|]|]|]|].
    - split; [reflexivity|]. split; [intros o h' []|]. right.
      split; [reflexivity|]. split; [reflexivity|]. eexists. split; reflexivity.
    - split; [reflexivity|]. split; [intros o h' Hin; destruct Hin|]. left.
      split; [reflexivity|]. split; [split; reflexivity | reflexivity].
    - split; [reflexivity|]. split; [intros o h' Hin; destruct Hin|]. right.
      split; [reflexivity|]. split; [reflexivity|]. eexists. split; reflexivity.
    - split; [reflexivity|]. split.
      + intros o h' Hin _. simpl in Hin. destruct Hin as [Heq | []]. injection Heq as _ <-. reflexivity.
      + left. split; [reflexivity|]. split; [split; reflexivity | reflexivity].
  Qed.

  (** Thread 1's write (operation 2) responds last, after thread 3's read
      of [x] (operation 3). *)
  Lemma reorder_canon :
    ViewLiftAdequacy.canon reorder_R =
      [(0%nat, false); (0%nat, true); (1%nat, false); (1%nat, true);
       (2%nat, false); (3%nat, false); (3%nat, true); (2%nat, true)].
  Proof. reflexivity. Qed.

  Theorem reorder_rel_lin :
    RelaxedTraceLin.rel_lin (ViewLiftAdequacy.csel TP reorder_R) (ViewLiftAdequacy.canon reorder_R)
      (RelaxedSig.semi_independent (ViewLiftAdequacy.RS TP)) (ViewLiftAdequacy.nu_P TP s00).
  Proof.
    destruct reorder_run as (s & HR). exact (ViewLiftAdequacy.canon_rel_lin TP s00 reorder_R s HR).
  Qed.

  (** ** Relaxed traces over [TP] *)

  Import RelaxedTraceLin.

  Abbreviation RS := (ViewLiftAdequacy.RS TP).
  Abbreviation selR := (@PrefixView.sel RS).
  Abbreviation indepT := (RelaxedSig.semi_independent RS).
  Abbreviation nuT := (ViewLiftAdequacy.nu_P TP s00).
  Abbreviation TE := (RelaxedLTSSpec.ThreadEvent RS).

  Definition iv (t : tid) (h : nat) (m : TOp) : TE :=
    RelaxedLTSSpec.Build_ThreadEvent t (RelaxedLTSSpec.InvEv (E := RS) h m).
  Definition rv (t : tid) (h : nat) (m : TOp) (r : TAr m) : TE :=
    RelaxedLTSSpec.Build_ThreadEvent t (RelaxedLTSSpec.ResEv (E := RS) h m r).

  Lemma inv_nth (L : list TE) i k m :
    inv_at selR L i k m ->
    nth_error L i = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.InvEv (snd k) m)).
  Proof. intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->. exact Hx. Qed.

  Lemma res_nth (L : list TE) j k m r :
    res_at selR L j k m r ->
    nth_error L j = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.ResEv (snd k) m r)).
  Proof. intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->. exact Hx. Qed.

  Lemma nth_inv (L : list TE) i k m :
    nth_error L i = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.InvEv (snd k) m)) ->
    inv_at selR L i k m.
  Proof. intros Hx. eexists. split; [exact Hx | reflexivity]. Qed.

  Lemma nth_res (L : list TE) j k m r :
    nth_error L j = Some (RelaxedLTSSpec.Build_ThreadEvent (fst k) (RelaxedLTSSpec.ResEv (snd k) m r)) ->
    res_at selR L j k m r.
  Proof. intros Hx. eexists. split; [exact Hx | reflexivity]. Qed.

  (** Case analysis on the index of an event in a concrete list. *)
  Ltac enum_nth H :=
    match type of H with
    | nth_error (_ :: _) ?i = _ => destruct i as [|i]; simpl in H; [|enum_nth H]
    | nth_error [] ?i = _ => destruct i; discriminate H
    | _ => idtac
    end.

  (** From [Some e = Some e'] with [e'] mentioning the key [k]: either the
      events differ, or [k] and the operation are determined. *)
  Ltac ev_case H k :=
    first [ discriminate H
          | (destruct k as [?kt ?kh]; injection H; intros; subst) ].

  (** *** The issue-order trace is not relaxed linearizable *)

  Definition issue_trace : list TE := [
    iv t1 0%nat (TW true 1); rv t1 0%nat (TW true 1) tt;
    iv t2 1%nat (TW false 1); rv t2 1%nat (TW false 1) tt;
    iv t3 2%nat (TR false); rv t3 2%nat (TR false) 1%nat;
    iv t3 3%nat (TR true); rv t3 3%nat (TR true) 0%nat].

  Definition wx_op : Op RS := Build_Op (E := RS) (t1, 0%nat) (TW true 1) (tt : TAr (TW true 1)).
  Definition rx_op : Op RS := Build_Op (E := RS) (t3, 3%nat) (TR true) (0%nat : TAr (TR true)).

  Lemma inv_issue i k m :
    inv_at selR issue_trace i k m ->
    (k = (t1, 0%nat) /\ m = TW true 1) \/ (k = (t2, 1%nat) /\ m = TW false 1) \/
    (k = (t3, 2%nat) /\ m = TR false) \/ (i = 6%nat /\ k = (t3, 3%nat) /\ m = TR true).
  Proof.
    intros Hi. apply inv_nth in Hi. unfold issue_trace in Hi. enum_nth Hi; ev_case Hi k; simpl; auto 10.
  Qed.

  Lemma res_issue_rx j m r : res_at selR issue_trace j (t3, 3%nat) m r -> j = 7%nat.
  Proof.
    intros Hj. apply res_nth in Hj. unfold issue_trace in Hj. simpl in Hj.
    enum_nth Hj; try discriminate Hj. reflexivity.
  Qed.

  Lemma chain_cons_inv s o s' Ws :
    ViewLiftAdequacy.Chain TP s ((o, s') :: Ws) ->
    vl_spec TP s (fst (op_key o)) (op_op o) (op_ret o) s' /\ ViewLiftAdequacy.Chain TP s' Ws.
  Proof. intros Hc. inversion Hc; subst. auto. Qed.

  Lemma chain_no_stale s Ws :
    ViewLiftAdequacy.Chain TP s Ws -> fst s = 1%nat ->
    (forall o, In o (map fst Ws) -> forall v, op_op o <> TW true v) ->
    ~ In rx_op (map fst Ws).
  Proof.
    induction 1 as [s | s o s' Ws Hsp Hc IH]; intros Hx Hnw Hin; [destruct Hin|].
    simpl in Hin. destruct Hin as [Ho | Hin].
    - subst o. simpl in Hsp. destruct Hsp as [H0 _]. unfold get in H0. rewrite Hx in H0. discriminate.
    - apply IH; [| intros o' Ho' v; apply Hnw; right; exact Ho' | exact Hin].
      destruct o as [k m r]. destruct m as [l v | l].
      + destruct l; [exfalso; exact (Hnw _ (or_introl eq_refl) v eq_refl)|].
        simpl in Hsp. subst s'. exact Hx.
      + simpl in Hsp. destruct Hsp as [_ ->]. exact Hx.
  Qed.

  Theorem issue_trace_not_rel_lin : ~ RelaxedTraceLin.rel_lin selR issue_trace indepT nuT.
  Proof.
    intros (W & (Ws & Hc & HWs) & Hnd & Hocc & Hcov & Hord).
    (* The write of [x] and the read of [x] are in the witness. *)
    assert (Hwx : In wx_op W).
    { destruct (Hcov 0%nat (t1, 0%nat) (TW true 1) (nth_inv issue_trace 0%nat (t1, 0%nat) (TW true 1) eq_refl)) as (o & Ho & Hk).
      destruct (Hocc o Ho) as [(i & Hi) _]. destruct o as [k m r]. simpl in Hk, Hi. subst k.
      destruct (inv_issue _ _ _ Hi) as [(_ & ->) | [(Hk & _) | [(Hk & _) | (_ & Hk & _)]]];
        try discriminate Hk.
      destruct r. exact Ho. }
    assert (Hrx : In rx_op W).
    { destruct (Hcov 6%nat (t3, 3%nat) (TR true) (nth_inv issue_trace 6%nat (t3, 3%nat) (TR true) eq_refl)) as (o & Ho & Hk).
      destruct (Hocc o Ho) as [(i & Hi) (j & Hj)]. destruct o as [k m r]. simpl in Hk, Hi, Hj. subst k.
      destruct (inv_issue _ _ _ Hi) as [(Hk & _) | [(Hk & _) | [(Hk & _) | (_ & _ & ->)]]];
        try discriminate Hk.
      pose proof (res_issue_rx _ _ _ Hj) as ->.
      assert (Hj7 : res_at selR issue_trace 7%nat (t3, 3%nat) (TR true) (0%nat : TAr (TR true)))
        by (apply nth_res; reflexivity).
      pose proof (PrefixView.res_ret _ _ _ _ _ _ Hj Hj7) as ->. exact Ho. }
    (* Real time orders them. *)
    assert (Hb : before W wx_op rx_op).
    { apply Hord; [exact Hwx | exact Hrx|]. left. exists 1%nat, 6%nat.
      split; [apply nth_res; reflexivity|]. split; [apply nth_inv; reflexivity | lia]. }
    destruct Hb as (l1 & l2 & HW & Hin).
    rewrite HW in HWs. apply map_eq_app in HWs as (Ws1 & Ws2 & -> & _ & HWs2).
    apply map_eq_cons in HWs2 as (p & Ws3 & -> & Hp & HWs3). subst l2.
    apply ViewLiftAdequacy.chain_app in Hc as [_ Hc]. destruct p as [o' s'].
    simpl in Hp. subst o'.
    apply chain_cons_inv in Hc as [Hsp Hc2].
    simpl in Hsp. subst s'.
    apply (chain_no_stale _ _ Hc2); [reflexivity| |exact Hin].
    (* Every other operation after the write of [x] is not a write of [x]:
       only key [(t1, 0)] writes [x], and keys are unique. *)
    intros o Ho v Hv.
    destruct (Hocc o (ltac:(rewrite HW; apply in_or_app; right; right; exact Ho))) as [(i & Hi) _].
    rewrite Hv in Hi.
    destruct (inv_issue _ _ _ Hi) as [(Hk & _) | [(_ & Hm) | [(_ & Hm) | (_ & _ & Hm)]]];
      [|discriminate Hm..].
    rewrite HW, map_app in Hnd. simpl in Hnd. apply NoDup_app_remove_l in Hnd.
    apply NoDup_cons_iff in Hnd as [Hn _]. apply Hn. rewrite <- Hk. apply in_map. exact Ho.
  Qed.

  (** *** The overlapping trace, verified by a possibility run *)

  (** Thread 1's write [x := 1] is invoked after thread 2's write and
      thread 3's read of [y], and responds last, after thread 3's read of
      [x] returns 0.  Keys are [(thread, run index)] as in [canon]. *)
  Definition overlap_trace : list TE := [
    iv t2 0%nat (TW false 1); rv t2 0%nat (TW false 1) tt;
    iv t3 1%nat (TR false); rv t3 1%nat (TR false) 1%nat;
    iv t1 2%nat (TW true 1);
    iv t3 3%nat (TR true); rv t3 3%nat (TR true) 0%nat;
    rv t1 2%nat (TW true 1) tt].

  (** It is the canonical trace of [reorder_R]. *)
  Lemma overlap_is_canon :
    map (ViewLiftAdequacy.csel TP reorder_R) (ViewLiftAdequacy.canon reorder_R) = map Some overlap_trace.
  Proof. reflexivity. Qed.

  (** The stamps of the possibility: those of [reorder_R]. *)
  Definition hkT (k : RelaxedLTSSpec.CallKey RS) : positive :=
    match snd k with O => 2 | S O => 3 | S (S O) => 5 | _ => 4 end%positive.

  (** VT-Invoke and VT-Return of each operation immediately follow its
      concrete invocation.  Thread 1's concrete response comes last. *)
  Definition trun : list (ViewPossibility.PStep RS) := [
    ViewPossibility.CEv (iv t2 0%nat (TW false 1));
    ViewPossibility.AInv (E := RS) (t2, 0%nat) (TW false 1);
    ViewPossibility.ARet (E := RS) (t2, 0%nat) (TW false 1) (tt : TAr (TW false 1));
    ViewPossibility.CEv (rv t2 0%nat (TW false 1) tt);
    ViewPossibility.CEv (iv t3 1%nat (TR false));
    ViewPossibility.AInv (E := RS) (t3, 1%nat) (TR false);
    ViewPossibility.ARet (E := RS) (t3, 1%nat) (TR false) (1%nat : TAr (TR false));
    ViewPossibility.CEv (rv t3 1%nat (TR false) 1%nat);
    ViewPossibility.CEv (iv t1 2%nat (TW true 1));
    ViewPossibility.AInv (E := RS) (t1, 2%nat) (TW true 1);
    ViewPossibility.ARet (E := RS) (t1, 2%nat) (TW true 1) (tt : TAr (TW true 1));
    ViewPossibility.CEv (iv t3 3%nat (TR true));
    ViewPossibility.AInv (E := RS) (t3, 3%nat) (TR true);
    ViewPossibility.ARet (E := RS) (t3, 3%nat) (TR true) (0%nat : TAr (TR true));
    ViewPossibility.CEv (rv t3 3%nat (TR true) 0%nat);
    ViewPossibility.CEv (rv t1 2%nat (TW true 1) tt)].

  Lemma conc_trun : ViewPossibility.conc trun = overlap_trace.
  Proof. reflexivity. Qed.

  Lemma ents_trun : ViewPossibility.ents TP hkT trun = reorder_R.
  Proof. reflexivity. Qed.

  Ltac in_list := simpl; repeat (first [left; reflexivity | right]).

  Ltac split_or H :=
    match type of H with
    | _ \/ _ => destruct H as [H | H]; [| split_or H]
    | False => destruct H
    | _ => idtac
    end.

  (** One component of the local conditions of a step. *)
  Ltac solve_part :=
    first
      [ exact I
      | (* the concrete or abstract invocation is in the trace *)
        solve [apply ViewPossibility.In_inv; in_list]
      | (* a concrete event: if a response, the abstract response precedes it *)
        solve [let Heq := fresh "Heq" in
               intros ? ? ? Heq;
               first [ discriminate Heq
                     | (apply ViewPossibility.In_res;
                        match type of Heq with ?a = _ => match goal with |- In _ ?L =>
                          let Hin := fresh in assert (Hin : In a L) by in_list; rewrite Heq in Hin; exact Hin
                        end end) ]]
      | (* VT-Invoke, real time: every earlier response has a smaller stamp *)
        solve [let k' := fresh "k'" in let Hj := fresh "Hj" in
               intros ? ? k' ? ? _ Hj _; apply ViewPossibility.res_In in Hj; simpl in Hj; split_or Hj;
               first [discriminate Hj | (destruct k' as [? ?]; injection Hj; intros; subst;
                                         unfold ViewPossibility.HT, hkT; simpl; lia)]]
      | (* VT-Invoke, Def. I.2(3): earlier dependent same-thread invocations *)
        solve [let k' := fresh "k'" in let Hi := fresh "Hi" in let Hj := fresh "Hj" in
               let Hth := fresh "Hth" in let Hn := fresh "Hn" in
               intros ? ? k' ? Hi Hj ? Hth Hn; apply inv_nth in Hi; apply inv_nth in Hj;
               simpl in Hi, Hj; enum_nth Hi; try discriminate Hi; enum_nth Hj; try discriminate Hj;
               destruct k' as [? ?]; injection Hj; intros; subst;
               first [ lia | (simpl in Hth; discriminate Hth) | (exfalso; apply Hn; reflexivity)
                     | (split; [apply ViewPossibility.In_inv; in_list | unfold ViewPossibility.HT, hkT; simpl; lia]) ]]
      | (* VT-Return: no earlier abstract response with the same key *)
        solve [let Hb := fresh "Hb" in
               intros ? ? ? Hb; apply ViewPossibility.res_In in Hb; simpl in Hb; split_or Hb; discriminate Hb] ].

  Lemma trun_lvalid : ViewPossibility.LValid indepT (ViewPossibility.HT TP hkT) trun.
  Proof.
    apply (ViewPossibility.okall_LValid _ _ [] trun (ViewPossibility.LValid_nil _ _)).
    simpl. repeat match goal with |- _ /\ _ => split end.
    all: hnf.
    all: solve_part.
  Qed.

  Ltac find_inv :=
    first [ exists 0%nat; split; [lia | apply nth_inv; reflexivity]
          | exists 1%nat; split; [lia | apply nth_inv; reflexivity]
          | exists 2%nat; split; [lia | apply nth_inv; reflexivity]
          | exists 3%nat; split; [lia | apply nth_inv; reflexivity]
          | exists 4%nat; split; [lia | apply nth_inv; reflexivity]
          | exists 5%nat; split; [lia | apply nth_inv; reflexivity]
          | exists 6%nat; split; [lia | apply nth_inv; reflexivity] ].

  Ltac find_res :=
    first [ exists 1%nat; eexists; apply nth_res; reflexivity
          | exists 3%nat; eexists; apply nth_res; reflexivity
          | exists 6%nat; eexists; apply nth_res; reflexivity
          | exists 7%nat; eexists; apply nth_res; reflexivity ].

  Lemma wf_overlap : PrefixView.wf overlap_trace.
  Proof.
    split; [|split].
    - intros i j k m m' Hi Hj. apply inv_nth in Hi. apply inv_nth in Hj. unfold overlap_trace in Hi, Hj.
      enum_nth Hi; ev_case Hi k; enum_nth Hj; first [discriminate Hj | reflexivity].
    - intros i j k m m' r r' Hi Hj. apply res_nth in Hi. apply res_nth in Hj. unfold overlap_trace in Hi, Hj.
      enum_nth Hi; ev_case Hi k; enum_nth Hj; first [discriminate Hj | reflexivity].
    - intros j k m r Hj. apply res_nth in Hj. unfold overlap_trace in Hj.
      enum_nth Hj; ev_case Hj k; find_inv.
  Qed.

  Lemma complete_overlap : PrefixView.complete overlap_trace.
  Proof.
    intros i k m Hi. apply inv_nth in Hi. unfold overlap_trace in Hi.
    enum_nth Hi; ev_case Hi k; find_res.
  Qed.

  Theorem poss_run_rel_lin : RelaxedTraceLin.rel_lin selR overlap_trace indepT nuT.
  Proof.
    rewrite <- conc_trun. apply (ViewPossibility.timeline_rel_lin TP s00 hkT trun).
    - split; [exact trun_lvalid|]. rewrite ents_trun. exact reorder_run.
    - rewrite conc_trun. exact wf_overlap.
    - rewrite conc_trun. exact complete_overlap.
  Qed.
End ViewLiftMultiWriter.
