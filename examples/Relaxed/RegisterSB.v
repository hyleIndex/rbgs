(** * RegisterSB: Reviewer A's store-buffering test against register cells

    Reviewer A (popl2027-reviews.md:69-81) asks whether the
    semi-independence relation can encode the TSO outcome
<<
    W x 1; R x = 1; R y = 0   ||   W y 1; R y = 1; R x = 0
>>
    (store buffering with own reads, "SB+rfi"), and suspects it is
    forbidden "because the adjacent operations of each thread are ordered
    (and so, by transitivity, also the first and third operation in each
    thread)".  Appendix/Mem.tex:5-14 of the TR gives the same argument for
    the register cells and states "No choice of semi-independence relation
    repairs this".  This file checks both statements in the kernel and
    makes the second one precise.  That TSO allows the outcome is in
    [SeqLockQ6Mem] ([sbrfi_nu]: ν_TSO of the buffered cell;
    [sbrfi_x86_trace]: a trace of the x86-TSO machine).

    What is used.
    - Signature: [Cell.CellRSig] (memory/Cell.v) at [TSO_cfg Nat.eq_dec].
      Its operations are [wrt x v tt], [rd x tt], [flush x]; its
      semi-independence is [Cell.mode_indep] (only a write followed by a
      read of another location, [TSO_indep_iff]).  Locations x = 1, y = 2.
    - Relaxed linearizability: [RelaxedTraceLin.rel_lin] (Def. 3.14,
      complete traces), with the semi-independence passed explicitly, so
      any relation I on [cell_op] can be tested.
    - Specification [nu_regs]: every location is a register initialised to
      0.  The projection of the sequential witness to each location is a
      register history ([reg_hist], the same shape as
      [PrefixView.reg_ok]); [flush] is not a register operation.  This is
      the tensor of per-location registers, as [BracketedLink.nuE_all] is
      for components.  These are the register cells of the main text:
      "The memory cells of \S\ref{sec:trace} share one linearized
      specification, the register" (Appendix/Mem.tex:5).

    Results.
    - (b′) [sbrfi_not_rel_lin_any]: for every I that keeps the four pairs
      (W x 1, R x), (R x, R y), (W y 1, R y), (R y, R x), and for every
      complete trace whose responses are those of the outcome and whose
      invocations have the four same-thread orders ([sb_shape]), the
      trace is not relaxed linearizable w.r.t. [nu_regs].  The proof uses
      only these same-thread edges and the values: either T1's R y = 0
      follows T2's W y 1, or T1's chain W x 1 < R x < R y < W y 1 < R y <
      R x puts T2's R x = 0 after W x 1.
    - (b) [sbrfi_not_rel_lin_TSO]: in particular for I = [mode_indep], on
      the trace [sbrfi_events] (all invocations before all responses,
      the least constrained schedule).
    - The four pairs cannot be reduced to the two same-location pairs.
      [sbrfi_rel_lin_loc]: under [I_loc] (every two operations of
      different locations are semi-independent, the cross-location
      relation of a COH cell), which keeps both same-location pairs, the
      outcome is relaxed linearizable w.r.t. [nu_regs].
    - [sbrfi_needs_rr_reordering]: the precise form of Mem.tex:14.  Take
      any I that keeps each thread's write before its own read of the same
      location.  If neither message-passing outcome ([mp_events]:
      W x 1; W y 1 ‖ R y = 1; R x = 0, and its mirror [mp_rev_events]) is
      relaxed linearizable under I, then the SB+rfi outcome is not either.
      [mp_rel_lin_if] and [mp_rev_rel_lin_if] show the step: dropping a
      reader's read-read pair admits message passing.  TSO forbids both
      message-passing outcomes; that is the standard x86-TSO fact and is
      not kernel-checked here.  So, over register cells, no I both keeps
      TSO's guarantees and admits this TSO behaviour.  The remedy of
      Mem.tex is to change the specification (the buffered cell), not I.
    - Real-time order is not used: [sbrfi_events] has no response before
      an invocation.  Consider instead a schedule in which T1's three
      operations complete before T2's begin; x86 can produce the outcome
      that way if writes respond at issue.  There, real time alone orders
      T1's W x 1 before T2's R x = 0 and refutes the outcome for every I
      (the argument of [SeqLockQ6] Part 4).  That variant is not stated
      here.

    This confirms Reviewer A's objection for the register cells of the main
    text; it does not answer it (the answer is the buffered cell of
    Mem.tex).

    Assumptions.  Every result is closed under the global context.  No
    [vm_compute]; [lia] terms carry a VM cast, as everywhere in the
    development. *)

From Stdlib Require Import List Bool Arith PArith micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import memory.Cell.

Import ListNotations.

Module RegisterSB.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedTraceLin.
  Import Cell Cell.Instances.

  (** The TSO cell signature over locations [nat] (memory/Cell.v): its
      operations are [wrt x v tt], [rd x tt] and [flush x]; its
      semi-independence is [mode_indep]. *)
  Abbreviation C := (TSO_cfg Nat.eq_dec).
  Abbreviation E := (CellRSig C).

  (** ** List facts *)

  Lemma before_split {A} (l : list A) a b :
    before l a b -> exists i j, i < j /\ nth_error l i = Some a /\ nth_error l j = Some b.
  Proof.
    intros (l1 & l2 & -> & Hb). apply In_nth_error in Hb as [j Hj].
    exists (length l1), (length l1 + S j). split; [lia |]. split.
    - rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity.
    - rewrite nth_error_app2 by lia. replace (length l1 + S j - length l1) with (S j) by lia. exact Hj.
  Qed.

  Lemma nth_before {A} (l : list A) i j a b :
    nth_error l i = Some a -> nth_error l j = Some b -> i < j -> before l a b.
  Proof.
    intros Hi Hj Hij. destruct (nth_error_split _ _ Hi) as (l1 & l2 & -> & Hlen).
    exists l1, l2. split; [reflexivity |].
    rewrite nth_error_app2 in Hj by lia.
    destruct (j - length l1) as [| d] eqn:Hd; [lia |]. cbn in Hj.
    apply nth_error_In in Hj. exact Hj.
  Qed.

  Lemma before_trans {A} (l : list A) a b c : NoDup l -> before l a b -> before l b c -> before l a c.
  Proof.
    intros Hnd H1 H2.
    apply before_split in H1 as (i & j & Hij & Ha & Hb). apply before_split in H2 as (j' & k & Hjk & Hb' & Hc).
    assert (j = j').
    { apply (proj1 (NoDup_nth_error l) Hnd); [apply nth_error_Some; congruence | congruence]. }
    subst j'. exact (nth_before l i k a c Ha Hc ltac:(lia)).
  Qed.

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

  Lemma before_filter {A} (f : A -> bool) l a b :
    before l a b -> f a = true -> f b = true -> before (filter f l) a b.
  Proof.
    intros (l1 & l2 & -> & Hb) Ha Hfb. rewrite filter_app. cbn. rewrite Ha.
    exists (filter f l1), (filter f l2). split; [reflexivity | apply filter_In; auto].
  Qed.

  Definition inv_before {X : Type} (sel : X -> option (ThreadEvent E)) (L : list X)
      (k : CallKey E) (m : cell_op C) (k' : CallKey E) (m' : cell_op C) : Prop :=
    exists i j, inv_at sel L i k m /\ inv_at sel L j k' m' /\ i < j.

  (** ** The register specification *)

  (** Operations with their results, as plain data. *)
  Inductive CEv := CW (x v : nat) | CR (x r : nat) | CF (x : nat).

  Definition cev (m : cell_op C) : cell_ar m -> CEv :=
    match m as m0 return cell_ar m0 -> CEv with
    | wrt x v _ => fun _ => CW x v
    | rd x _ => fun r => CR x r
    | flush x => fun _ => CF x
    end.

  Definition ev (o : Op E) : CEv := cev (op_op o) (op_ret o).

  (** One register, from value [cur]: a read returns the last value
      written; [flush] is not a register operation. *)
  Fixpoint reg_hist (cur : nat) (l : list (Op E)) : Prop :=
    match l with
    | [] => True
    | o :: l' =>
        match ev o with
        | CW _ v => reg_hist v l'
        | CR _ r => r = cur /\ reg_hist cur l'
        | CF _ => False
        end
    end.

  Definition at_loc_op (x : nat) (o : Op E) : bool := Nat.eqb (op_loc (op_op o)) x.

  (** The register cells: every location is a register initialised to 0,
      i.e. the projection of the sequential witness to each location is a
      register history (the tensor of per-location registers, as
      [BracketedLink.nuE_all] for components). *)
  Definition nu_regs (l : list (Op E)) : Prop := forall x, reg_hist 0 (filter (at_loc_op x) l).

  Lemma ev_CW (o : Op E) x v : ev o = CW x v -> op_op o = @wrt C x v tt.
  Proof.
    destruct o as [k m r]. destruct m as [x' v' a | x' a | x']; cbn; intros H; try discriminate H.
    injection H as -> ->. destruct a. reflexivity.
  Qed.

  Lemma ev_CR (o : Op E) x r : ev o = CR x r -> op_op o = @rd C x tt.
  Proof.
    destruct o as [k m r']. destruct m as [x' v' a | x' a | x']; cbn; intros H; try discriminate H.
    injection H as -> ->. destruct a. reflexivity.
  Qed.

  Lemma reg_hist_app cur l1 l2 : reg_hist cur (l1 ++ l2) -> exists cur', reg_hist cur' l2.
  Proof.
    revert cur. induction l1 as [| o l1 IH]; intros cur H; [exists cur; exact H |].
    cbn in H. destruct (ev o); [exact (IH _ H) | exact (IH _ (proj2 H)) | destruct H].
  Qed.

  Lemma reg_hist_const l : forall cur, reg_hist cur l ->
    (forall o x v, In o l -> ev o = CW x v -> v = cur) ->
    forall o x r, In o l -> ev o = CR x r -> r = cur.
  Proof.
    induction l as [| o l IH]; intros cur H Hw o' x r Hin Ho'; [destruct Hin |].
    cbn in H. destruct Hin as [<- | Hin].
    - rewrite Ho' in H. exact (proj1 H).
    - assert (Hw' : forall o x v, In o l -> ev o = CW x v -> v = cur) by (intros; eapply Hw; [right |]; eauto).
      destruct (ev o) as [x' v | x' r' | x'] eqn:Eo.
      + rewrite (Hw o x' v (or_introl eq_refl) Eo) in H. exact (IH cur H Hw' o' x r Hin Ho').
      + exact (IH cur (proj2 H) Hw' o' x r Hin Ho').
      + destruct H.
  Qed.

  (** In a legal witness, a read of [x] placed after a write of [v] to [x]
      returns [v], if every write to [x] writes [v]. *)
  Lemma regs_after W ow orr x v r :
    nu_regs W -> In ow W -> ev ow = CW x v -> In orr W -> ev orr = CR x r -> before W ow orr ->
    (forall w v', In w W -> ev w = CW x v' -> v' = v) -> r = v.
  Proof.
    intros Hnu How Ew Hor Er Hb Hall.
    assert (Hb' : before (filter (at_loc_op x) W) ow orr).
    { apply before_filter; [exact Hb | |]; unfold at_loc_op;
        [rewrite (ev_CW ow x v Ew) | rewrite (ev_CR orr x r Er)]; apply Nat.eqb_refl. }
    destruct Hb' as (l1 & l2 & EP & Hl2).
    pose proof (Hnu x) as Hx. rewrite EP in Hx.
    destruct (reg_hist_app _ _ _ Hx) as (cur & Hc). cbn in Hc. rewrite Ew in Hc.
    apply (reg_hist_const l2 v Hc) with (o := orr) (x := x); [| exact Hl2 | exact Er].
    intros w x' v' Hw Ew'.
    assert (HwW : In w (filter (at_loc_op x) W)) by (rewrite EP; apply in_or_app; right; right; exact Hw).
    apply filter_In in HwW as [HwW Hloc]. unfold at_loc_op in Hloc. rewrite (ev_CW w x' v' Ew') in Hloc.
    apply Nat.eqb_eq in Hloc. cbn in Hloc. subst x'. exact (Hall w v' HwW Ew').
  Qed.

  (** ** The test, for every semi-independence that keeps four pairs *)

  (** x = 1, y = 2.  T1 = thread 1: W x 1 (handle 0); R x = 1 (1);
      R y = 0 (2).  T2 = thread 2: W y 1 (0); R y = 1 (1); R x = 0 (2). *)
  Definition sb_info : list (CallKey E * CEv) :=
    [((1%positive, 0), CW 1 1); ((1%positive, 1), CR 1 1); ((1%positive, 2), CR 2 0);
     ((2%positive, 0), CW 2 1); ((2%positive, 1), CR 2 1); ((2%positive, 2), CR 1 0)].

  (** The shape the refutation uses: every response is one of [sb_info],
      and each thread invokes its write before its own read, and its own
      read before its other read. *)
  Definition sb_shape {X : Type} (sel : X -> option (ThreadEvent E)) (L : list X) : Prop :=
    (forall j k m r, res_at sel L j k m r -> In (k, cev m r) sb_info) /\
    inv_before sel L (1%positive, 0) (@wrt C 1 1 tt) (1%positive, 1) (@rd C 1 tt) /\
    inv_before sel L (1%positive, 1) (@rd C 1 tt) (1%positive, 2) (@rd C 2 tt) /\
    inv_before sel L (2%positive, 0) (@wrt C 2 1 tt) (2%positive, 1) (@rd C 2 tt) /\
    inv_before sel L (2%positive, 1) (@rd C 2 tt) (2%positive, 2) (@rd C 1 tt).

  Ltac pick I := cbn in I;
    destruct I as [Hc | [Hc | [Hc | [Hc | [Hc | [Hc | []]]]]]]; first [discriminate Hc | congruence].

  (** (b′) If the semi-independence keeps each thread's write before its
      own read of the same location, and each thread's two reads in
      order, the outcome is not relaxed linearizable w.r.t. the register
      cells, for every complete trace of this shape. *)
  Theorem sbrfi_not_rel_lin_any (I : cell_op C -> cell_op C -> Prop) :
    ~ I (@wrt C 1 1 tt) (@rd C 1 tt) -> ~ I (@rd C 1 tt) (@rd C 2 tt) ->
    ~ I (@wrt C 2 1 tt) (@rd C 2 tt) -> ~ I (@rd C 2 tt) (@rd C 1 tt) ->
    forall {X : Type} (sel : X -> option (ThreadEvent E)) (L : list X),
      sb_shape sel L -> ~ rel_lin sel L I nu_regs.
  Proof.
    intros N1 N2 N3 N4 X sel L
      (Hres & (i1 & i2 & Hi1 & Hi2 & H12) & (i2' & i3 & Hi2' & Hi3 & H23)
             & (i4 & i5 & Hi4 & Hi5 & H45) & (i5' & i6 & Hi5' & Hi6 & H56)) (W & HW).
    pose proof HW as (Hnu & Hnd & Hocc & Hall & Hord).
    assert (Hv : forall o, In o W -> In (op_key o, ev o) sb_info).
    { intros o Ho. destruct (Hocc o Ho) as [_ (j & Hj)]. exact (Hres _ _ _ _ Hj). }
    assert (HndW : NoDup W) by exact (NoDup_map_inv _ _ Hnd).
    destruct (Hall _ _ _ Hi1) as (o1 & Ho1 & K1). destruct (Hall _ _ _ Hi2) as (o2 & Ho2 & K2).
    destruct (Hall _ _ _ Hi3) as (o3 & Ho3 & K3). destruct (Hall _ _ _ Hi4) as (o4 & Ho4 & K4).
    destruct (Hall _ _ _ Hi5) as (o5 & Ho5 & K5). destruct (Hall _ _ _ Hi6) as (o6 & Ho6 & K6).
    assert (E1 : ev o1 = CW 1 1) by (pose proof (Hv o1 Ho1) as I'; rewrite K1 in I'; pick I').
    assert (E2 : ev o2 = CR 1 1) by (pose proof (Hv o2 Ho2) as I'; rewrite K2 in I'; pick I').
    assert (E3 : ev o3 = CR 2 0) by (pose proof (Hv o3 Ho3) as I'; rewrite K3 in I'; pick I').
    assert (E4 : ev o4 = CW 2 1) by (pose proof (Hv o4 Ho4) as I'; rewrite K4 in I'; pick I').
    assert (E5 : ev o5 = CR 2 1) by (pose proof (Hv o5 Ho5) as I'; rewrite K5 in I'; pick I').
    assert (E6 : ev o6 = CR 1 0) by (pose proof (Hv o6 Ho6) as I'; rewrite K6 in I'; pick I').
    pose proof (ev_CW o1 _ _ E1) as P1. pose proof (ev_CR o2 _ _ E2) as P2.
    pose proof (ev_CR o3 _ _ E3) as P3. pose proof (ev_CW o4 _ _ E4) as P4.
    pose proof (ev_CR o5 _ _ E5) as P5. pose proof (ev_CR o6 _ _ E6) as P6.
    Local Ltac edge Hord o o' Ho Ho' K K' P P' i j Hi Hj Hij N :=
      apply (Hord o o' Ho Ho'); right; rewrite K, K', P, P'; split; [reflexivity |];
      exists i, j; split; [exact Hi |]; split; [exact Hj |]; split; [exact Hij | exact N].
    assert (B12 : before W o1 o2) by (edge Hord o1 o2 Ho1 Ho2 K1 K2 P1 P2 i1 i2 Hi1 Hi2 H12 N1).
    assert (B23 : before W o2 o3) by (edge Hord o2 o3 Ho2 Ho3 K2 K3 P2 P3 i2' i3 Hi2' Hi3 H23 N2).
    assert (B45 : before W o4 o5) by (edge Hord o4 o5 Ho4 Ho5 K4 K5 P4 P5 i4 i5 Hi4 Hi5 H45 N3).
    assert (B56 : before W o5 o6) by (edge Hord o5 o6 Ho5 Ho6 K5 K6 P5 P6 i5' i6 Hi5' Hi6 H56 N4).
    assert (Hw : forall w x v, In w W -> ev w = CW x v -> v = 1).
    { intros w x v Hw' Ew. pose proof (Hv w Hw') as I'. rewrite Ew in I'. pick I'. }
    assert (N34 : o3 <> o4) by (intros ->; rewrite K3 in K4; discriminate K4).
    destruct (before_total W o3 o4 Ho3 Ho4 N34) as [B34 | B43].
    - (* T1's read of y precedes T2's write of y: then T1's write of x
         precedes T2's read of x, which returns 0 *)
      pose proof (before_trans W _ _ _ HndW B12 B23) as B13.
      pose proof (before_trans W _ _ _ HndW B13 B34) as B14.
      pose proof (before_trans W _ _ _ HndW B14 B45) as B15.
      pose proof (before_trans W _ _ _ HndW B15 B56) as B16.
      assert (Ev : 0 = 1) by (apply (regs_after W o1 o6 1 1 0 Hnu Ho1 E1 Ho6 E6 B16);
                              intros w v' Hw' Ew; exact (Hw w 1 v' Hw' Ew)).
      discriminate Ev.
    - (* T2's write of y precedes T1's read of y, which returns 0 *)
      assert (Ev : 0 = 1) by (apply (regs_after W o4 o3 2 1 0 Hnu Ho4 E4 Ho3 E3 B43);
                              intros w v' Hw' Ew; exact (Hw w 2 v' Hw' Ew)).
      discriminate Ev.
  Qed.

  (** ** Concrete traces *)

  Definition iv (t : positive) (h : nat) (m : cell_op C) : ThreadEvent E :=
    Build_ThreadEvent t (InvEv (E := E) h m).
  Definition rw (t : positive) (h : nat) (x v : nat) : ThreadEvent E :=
    Build_ThreadEvent t (ResEv (E := E) h (@wrt C x v tt) tt).
  Definition rr (t : positive) (h : nat) (x r : nat) : ThreadEvent E :=
    Build_ThreadEvent t (ResEv (E := E) h (@rd C x tt) r).

  (** The outcome with all six invocations before all six responses: no
      response precedes an invocation, so only the same-thread clause of
      [rhb] applies (the least constrained schedule). *)
  Definition sbrfi_events : list (ThreadEvent E) :=
    [ iv 1 0 (@wrt C 1 1 tt); iv 1 1 (@rd C 1 tt); iv 1 2 (@rd C 2 tt);
      iv 2 0 (@wrt C 2 1 tt); iv 2 1 (@rd C 2 tt); iv 2 2 (@rd C 1 tt);
      rw 1 0 1 1; rr 1 1 1 1; rr 1 2 2 0; rw 2 0 2 1; rr 2 1 2 1; rr 2 2 1 0 ].

  Definition cres_info (e : ThreadEvent E) : option (CallKey E * CEv) :=
    match te_ev _ e with ResEv h m r => Some ((te_tid _ e, h), cev m r) | InvEv _ _ => None end.

  Lemma sbrfi_res j k m r : res_at Some sbrfi_events j k m r -> In (k, cev m r) sb_info.
  Proof.
    destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
    assert (H : In (Some ((t, h), cev m r)) (map cres_info sbrfi_events)).
    { apply (nth_error_In _ j). rewrite nth_error_map, Hx. reflexivity. }
    revert H. generalize (cev m r) as c. intros c H. cbn in H.
    repeat (destruct H as [H | H]; [first [discriminate H | injection H; intros; subst; cbn; auto 10] |]).
    destruct H.
  Qed.

  Lemma sbrfi_events_shape : sb_shape Some sbrfi_events.
  Proof.
    split; [exact sbrfi_res |].
    split; [| split; [| split]];
      [exists 0, 1 | exists 1, 2 | exists 3, 4 | exists 4, 5];
      (split; [eexists; split; reflexivity | split; [eexists; split; reflexivity | lia]]).
  Qed.

  (** (b) The TSO cell semi-independence keeps the four pairs: same
      location, and read-read ([TSO_indep_iff]). *)
  Theorem sbrfi_not_rel_lin_TSO : ~ rel_lin Some sbrfi_events (semi_independent E) nu_regs.
  Proof.
    apply (sbrfi_not_rel_lin_any (semi_independent E));
      [intros (H & _); apply H; reflexivity | intros (_ & H & _); exact H
      | intros (H & _); apply H; reflexivity | intros (_ & H & _); exact H
      | exact sbrfi_events_shape].
  Qed.

  (** ** Which pairs are needed *)

  Ltac getpos Hq := cbn in Hq;
    repeat (destruct Hq as [Hq | Hq]; [first [discriminate Hq | injection Hq; clear Hq; intros; subst] |]);
    try (destruct Hq).
  Ltac occpos := first [ exists 0; eexists; split; reflexivity | exists 1; eexists; split; reflexivity
    | exists 2; eexists; split; reflexivity | exists 3; eexists; split; reflexivity
    | exists 4; eexists; split; reflexivity | exists 5; eexists; split; reflexivity
    | exists 6; eexists; split; reflexivity | exists 7; eexists; split; reflexivity
    | exists 8; eexists; split; reflexivity | exists 9; eexists; split; reflexivity
    | exists 10; eexists; split; reflexivity | exists 11; eexists; split; reflexivity ].
  Ltac nthb := first
    [ apply (nth_before _ 0 1); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 0 2); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 0 3); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 0 4); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 0 5); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 1 2); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 1 3); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 1 4); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 1 5); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 2 3); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 2 4); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 2 5); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 3 4); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 3 5); [reflexivity | reflexivity | lia]
    | apply (nth_before _ 4 5); [reflexivity | reflexivity | lia] ].

  Definition mk (t : positive) (h : nat) (m : cell_op C) (r : cell_ar m) : Op E :=
    Build_Op (E := E) (t, h) m r.

  Lemma sbrfi_inv_at i k m : inv_at Some sbrfi_events i k m ->
    In (i, k, m) [(0, (1%positive, 0), @wrt C 1 1 tt); (1, (1%positive, 1), @rd C 1 tt);
                  (2, (1%positive, 2), @rd C 2 tt); (3, (2%positive, 0), @wrt C 2 1 tt);
                  (4, (2%positive, 1), @rd C 2 tt); (5, (2%positive, 2), @rd C 1 tt)].
  Proof.
    destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
    do 12 (destruct i as [| i]; [cbn in Hx; first [discriminate Hx | injection Hx; intros; subst; cbn; auto 10] |]).
    destruct i; discriminate Hx.
  Qed.

  Lemma sbrfi_res_pos j k m r : res_at Some sbrfi_events j k m r -> 6 <= j.
  Proof.
    intros (x & Hx & Hs). injection Hs as Hs. subst x.
    do 6 (destruct j as [| j]; [cbn in Hx; discriminate Hx |]). lia.
  Qed.

  (** The four pairs of (b′) cannot be reduced to the two same-location
      pairs.  [I_loc] relates every two operations of different locations
      (the cross-location relation of a COH cell): it keeps both
      same-location pairs and drops both read-read pairs, and under it the
      outcome is relaxed linearizable w.r.t. the register cells. *)
  Definition I_loc (m m' : cell_op C) : Prop := op_loc m <> op_loc m'.

  Lemma sbrfi_rel_lin_loc : rel_lin Some sbrfi_events I_loc nu_regs.
  Proof.
    exists [mk 1 2 (@rd C 2 tt) 0; mk 2 2 (@rd C 1 tt) 0; mk 1 0 (@wrt C 1 1 tt) tt;
            mk 1 1 (@rd C 1 tt) 1; mk 2 0 (@wrt C 2 1 tt) tt; mk 2 1 (@rd C 2 tt) 1].
    split; [| split; [| split; [| split]]].
    - intros x. destruct x as [| [| [| x]]]; cbn; tauto.
    - cbn. repeat constructor; cbn; intuition discriminate.
    - intros o Ho. cbn in Ho.
      repeat (destruct Ho as [<- | Ho]; [split; occpos |]). destruct Ho.
    - intros i k m Hi. apply sbrfi_inv_at in Hi. getpos Hi;
        first [ exists (mk 1 0 (@wrt C 1 1 tt) tt); split; [cbn; tauto | reflexivity]
              | exists (mk 1 1 (@rd C 1 tt) 1); split; [cbn; tauto | reflexivity]
              | exists (mk 1 2 (@rd C 2 tt) 0); split; [cbn; tauto | reflexivity]
              | exists (mk 2 0 (@wrt C 2 1 tt) tt); split; [cbn; tauto | reflexivity]
              | exists (mk 2 1 (@rd C 2 tt) 1); split; [cbn; tauto | reflexivity]
              | exists (mk 2 2 (@rd C 1 tt) 0); split; [cbn; tauto | reflexivity] ].
    - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
      + exfalso. apply sbrfi_res_pos in Hi. apply sbrfi_inv_at in Hj. getpos Hj; lia.
      + apply sbrfi_inv_at in Hi. apply sbrfi_inv_at in Hj.
        cbn in Ho, Ho'.
        destruct Ho as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
        destruct Ho' as [<- | [<- | [<- | [<- | [<- | [<- | []]]]]]];
        cbn in Ht; try discriminate Ht; getpos Hi; getpos Hj; try lia;
        first [ nthb | exfalso; apply Hn; unfold I_loc; cbn; discriminate ].
  Qed.

  (** Message passing over the register cells, with all invocations
      before all responses.
<<
      mp_events:     W x 1; W y 1   ||   R y = 1; R x = 0
      mp_rev_events: W y 1; W x 1   ||   R x = 1; R y = 0
>>
      If the semi-independence drops the read-read pair of the reader,
      the outcome is relaxed linearizable. *)
  Definition mp_events : list (ThreadEvent E) :=
    [ iv 1 0 (@wrt C 1 1 tt); iv 1 1 (@wrt C 2 1 tt); iv 2 0 (@rd C 2 tt); iv 2 1 (@rd C 1 tt);
      rw 1 0 1 1; rw 1 1 2 1; rr 2 0 2 1; rr 2 1 1 0 ].

  Definition mp_rev_events : list (ThreadEvent E) :=
    [ iv 1 0 (@wrt C 2 1 tt); iv 1 1 (@wrt C 1 1 tt); iv 2 0 (@rd C 1 tt); iv 2 1 (@rd C 2 tt);
      rw 1 0 2 1; rw 1 1 1 1; rr 2 0 1 1; rr 2 1 2 0 ].

  Lemma mp_inv_at i k m : inv_at Some mp_events i k m ->
    In (i, k, m) [(0, (1%positive, 0), @wrt C 1 1 tt); (1, (1%positive, 1), @wrt C 2 1 tt);
                  (2, (2%positive, 0), @rd C 2 tt); (3, (2%positive, 1), @rd C 1 tt)].
  Proof.
    destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
    do 8 (destruct i as [| i]; [cbn in Hx; first [discriminate Hx | injection Hx; intros; subst; cbn; auto 10] |]).
    destruct i; discriminate Hx.
  Qed.

  Lemma mp_rev_inv_at i k m : inv_at Some mp_rev_events i k m ->
    In (i, k, m) [(0, (1%positive, 0), @wrt C 2 1 tt); (1, (1%positive, 1), @wrt C 1 1 tt);
                  (2, (2%positive, 0), @rd C 1 tt); (3, (2%positive, 1), @rd C 2 tt)].
  Proof.
    destruct k as [t h]. intros (x & Hx & Hs). injection Hs as Hs. subst x.
    do 8 (destruct i as [| i]; [cbn in Hx; first [discriminate Hx | injection Hx; intros; subst; cbn; auto 10] |]).
    destruct i; discriminate Hx.
  Qed.

  Lemma mp_res_pos j k m r : res_at Some mp_events j k m r -> 4 <= j.
  Proof.
    intros (x & Hx & Hs). injection Hs as Hs. subst x.
    do 4 (destruct j as [| j]; [cbn in Hx; discriminate Hx |]). lia.
  Qed.

  Lemma mp_rev_res_pos j k m r : res_at Some mp_rev_events j k m r -> 4 <= j.
  Proof.
    intros (x & Hx & Hs). injection Hs as Hs. subst x.
    do 4 (destruct j as [| j]; [cbn in Hx; discriminate Hx |]). lia.
  Qed.

  Lemma mp_rel_lin_if (I : cell_op C -> cell_op C -> Prop) :
    I (@rd C 2 tt) (@rd C 1 tt) -> rel_lin Some mp_events I nu_regs.
  Proof.
    intros HI.
    exists [mk 2 1 (@rd C 1 tt) 0; mk 1 0 (@wrt C 1 1 tt) tt; mk 1 1 (@wrt C 2 1 tt) tt; mk 2 0 (@rd C 2 tt) 1].
    split; [| split; [| split; [| split]]].
    - intros x. destruct x as [| [| [| x]]]; cbn; tauto.
    - cbn. repeat constructor; cbn; intuition discriminate.
    - intros o Ho. cbn in Ho.
      repeat (destruct Ho as [<- | Ho]; [split; occpos |]). destruct Ho.
    - intros i k m Hi. apply mp_inv_at in Hi. getpos Hi;
        first [ exists (mk 1 0 (@wrt C 1 1 tt) tt); split; [cbn; tauto | reflexivity]
              | exists (mk 1 1 (@wrt C 2 1 tt) tt); split; [cbn; tauto | reflexivity]
              | exists (mk 2 0 (@rd C 2 tt) 1); split; [cbn; tauto | reflexivity]
              | exists (mk 2 1 (@rd C 1 tt) 0); split; [cbn; tauto | reflexivity] ].
    - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
      + exfalso. apply mp_res_pos in Hi. apply mp_inv_at in Hj. getpos Hj; lia.
      + apply mp_inv_at in Hi. apply mp_inv_at in Hj.
        cbn in Ho, Ho'.
        destruct Ho as [<- | [<- | [<- | [<- | []]]]]; destruct Ho' as [<- | [<- | [<- | [<- | []]]]];
        cbn in Ht; try discriminate Ht; getpos Hi; getpos Hj; try lia;
        first [ nthb | exfalso; exact (Hn HI) ].
  Qed.

  Lemma mp_rev_rel_lin_if (I : cell_op C -> cell_op C -> Prop) :
    I (@rd C 1 tt) (@rd C 2 tt) -> rel_lin Some mp_rev_events I nu_regs.
  Proof.
    intros HI.
    exists [mk 2 1 (@rd C 2 tt) 0; mk 1 0 (@wrt C 2 1 tt) tt; mk 1 1 (@wrt C 1 1 tt) tt; mk 2 0 (@rd C 1 tt) 1].
    split; [| split; [| split; [| split]]].
    - intros x. destruct x as [| [| [| x]]]; cbn; tauto.
    - cbn. repeat constructor; cbn; intuition discriminate.
    - intros o Ho. cbn in Ho.
      repeat (destruct Ho as [<- | Ho]; [split; occpos |]). destruct Ho.
    - intros i k m Hi. apply mp_rev_inv_at in Hi. getpos Hi;
        first [ exists (mk 1 0 (@wrt C 2 1 tt) tt); split; [cbn; tauto | reflexivity]
              | exists (mk 1 1 (@wrt C 1 1 tt) tt); split; [cbn; tauto | reflexivity]
              | exists (mk 2 0 (@rd C 1 tt) 1); split; [cbn; tauto | reflexivity]
              | exists (mk 2 1 (@rd C 2 tt) 0); split; [cbn; tauto | reflexivity] ].
    - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
      + exfalso. apply mp_rev_res_pos in Hi. apply mp_rev_inv_at in Hj. getpos Hj; lia.
      + apply mp_rev_inv_at in Hi. apply mp_rev_inv_at in Hj.
        cbn in Ho, Ho'.
        destruct Ho as [<- | [<- | [<- | [<- | []]]]]; destruct Ho' as [<- | [<- | [<- | [<- | []]]]];
        cbn in Ht; try discriminate Ht; getpos Hi; getpos Hj; try lia;
        first [ nthb | exfalso; exact (Hn HI) ].
  Qed.

  (** The precise form of Appendix/Mem.tex:14 ("No choice of
      semi-independence relation repairs this").  Take any I that keeps
      each thread's write before its own later read of the same location
      (dropping that pair lets the read miss the thread's own write).
      If neither message-passing outcome is relaxed linearizable under
      I, then neither is the SB-with-own-reads outcome. *)
  Theorem sbrfi_needs_rr_reordering (I : cell_op C -> cell_op C -> Prop) :
    ~ I (@wrt C 1 1 tt) (@rd C 1 tt) -> ~ I (@wrt C 2 1 tt) (@rd C 2 tt) ->
    ~ rel_lin Some mp_events I nu_regs -> ~ rel_lin Some mp_rev_events I nu_regs ->
    ~ rel_lin Some sbrfi_events I nu_regs.
  Proof.
    intros N1 N3 Nmp Nrev.
    apply (sbrfi_not_rel_lin_any I N1); [| exact N3 | | exact sbrfi_events_shape].
    - intros H. exact (Nrev (mp_rev_rel_lin_if I H)).
    - intros H. exact (Nmp (mp_rel_lin_if I H)).
  Qed.

End RegisterSB.
