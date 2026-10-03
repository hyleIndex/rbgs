(** * Horizontal composition via windows and mode inheritance

    Replaces the compatibility condition of the paper (Def. 5.8), which
    [BracketedComposition.bracketed_not_compatible] shows can never hold
    for methods that call both an acquire-like and a release-like
    operation.

    Every complete overlay operation [q] designates two of its own
    underlay calls, [lo q] and [hi q] (its window), and a linearization
    position [lp q] in the underlay sequential witness (possibly a call of
    another thread, so helping is allowed).

    - (S1) positional correctness, per component: ordering the
      component's operations by [lp] gives a history of its overlay
      specification, and [lp q] lies inside the window of [q].
      The component's own relaxed happens-before (same component, same
      thread, not semi-independent) must be respected by [lp] too; this
      is part of the component's own proof.
    - (S2) mode inheritance, across components: an acquire-like overlay
      mode must be carried by the last call of the window, a
      release-like one by the first call.  It gives order reflection:
      for same-thread [q] before [q'] of different components with
      [(q, q')] not overlay semi-independent, [(hi q, lo q')] is not
      underlay semi-independent.

    Part 1: the theorem, at the level of sequential witnesses (in the
    style of [BracketedComposition], Part 2).  Part 2: mode inheritance
    for single-call windows is [mF ≤f mode of the call]; checks for
    Lock(O) and LatchSet.  Part 3: necessity: with an overlay mode that
    is not inherited, every other hypothesis holds and the conclusion is
    false (store buffering).  Part 4: positive control.  Part 5: vertical
    closure of windows, positional correctness and mode inheritance. *)

From Stdlib Require Import List Sorting.Sorted Sorting.Permutation.
From Stdlib Require Import Arith.PeanoNat Bool.Bool micromega.Lia.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.

Import ListNotations.

Module WindowComposition.
  Import RelaxedSig.

  (** ** Fence-mode facts *)

  Lemma fence_le_dec (m1 m2 : FenceMode) : {m1 ≤f m2} + {~ m1 ≤f m2}.
  Proof.
    destruct m1, m2; cbn;
      first [left; exact I | right; intro Hf; exact Hf].
  Qed.

  (** The cross-component semi-independence of the tensor
      ([Tens.tsi_cross_lr] / [tsi_cross_rl]). *)
  Definition cross (m1 m2 : FenceMode) : Prop := m1 ≤f LFence /\ m2 ≤f RFence.

  (** Later operations of other objects may not overtake [q]. *)
  Definition acq_like (m : FenceMode) : Prop := ~ m ≤f LFence.
  (** Earlier operations of other objects may not be overtaken by [q]. *)
  Definition rel_like (m : FenceMode) : Prop := ~ m ≤f RFence.

  Lemma not_cross m1 m2 : ~ cross m1 m2 -> acq_like m1 \/ rel_like m2.
  Proof.
    unfold cross, acq_like, rel_like. intros Hn.
    destruct (fence_le_dec m1 LFence) as [H1|H1]; [|left; exact H1].
    destruct (fence_le_dec m2 RFence) as [H2|H2]; [|right; exact H2].
    exfalso. apply Hn. split; assumption.
  Qed.

  (** ** Lists *)

  Section Lists.
    Context {A : Type}.

    Lemma ss_filter (R : A -> A -> Prop) (f : A -> bool) l :
      StronglySorted R l -> StronglySorted R (filter f l).
    Proof.
      induction 1 as [|a l Hs IH Hf]; cbn; [constructor|].
      destruct (f a); [|exact IH].
      constructor; [exact IH|].
      rewrite Forall_forall in *. intros x Hx.
      apply filter_In in Hx as [Hx _]. apply Hf, Hx.
    Qed.

    Lemma ss_app_cons (R : A -> A -> Prop) l1 a l2 b :
      StronglySorted R (l1 ++ a :: l2) -> In b l1 -> R b a.
    Proof.
      induction l1 as [|c l1 IH]; cbn; intros Hs Hb; [contradiction|].
      inversion Hs as [|? ? Hs' Hf]; subst.
      destruct Hb as [<-|Hb].
      - rewrite Forall_forall in Hf. apply Hf. apply in_or_app. right; left; reflexivity.
      - apply IH; assumption.
    Qed.

    Lemma ss_impl_in (R R' : A -> A -> Prop) l :
      (forall x y, In x l -> In y l -> R x y -> R' x y) ->
      StronglySorted R l -> StronglySorted R' l.
    Proof.
      induction l as [|a l IH]; intros Himp Hs; [constructor|].
      inversion Hs as [|? ? Hs' Hf]; subst.
      constructor.
      - apply IH; [|exact Hs']. intros x y Hx Hy. apply Himp; right; assumption.
      - rewrite Forall_forall in *. intros x Hx.
        apply Himp; [left; reflexivity | right; exact Hx | apply Hf, Hx].
    Qed.

    Lemma perm_filter (f : A -> bool) l l' :
      Permutation l l' -> Permutation (filter f l) (filter f l').
    Proof.
      induction 1 as [|x l l' _ IH|x y l|l l' l'' _ IH1 _ IH2]; cbn.
      - constructor.
      - destruct (f x); [apply perm_skip|]; exact IH.
      - destruct (f x), (f y); first [apply perm_swap | reflexivity].
      - eapply perm_trans; eassumption.
    Qed.

    Context (key : A -> nat).

    (** Two lists sorted by a strict key order that are permutations of
        each other are equal. *)
    Lemma ss_perm_eq : forall l1 l2,
      StronglySorted (fun a b => key a < key b) l1 ->
      StronglySorted (fun a b => key a < key b) l2 ->
      Permutation l1 l2 -> l1 = l2.
    Proof.
      induction l1 as [|a l1 IH]; intros l2 H1 H2 P.
      - symmetry. apply Permutation_nil, P.
      - destruct l2 as [|b l2].
        + apply Permutation_sym, Permutation_nil in P. discriminate.
        + inversion H1 as [|? ? H1' F1]; subst.
          inversion H2 as [|? ? H2' F2]; subst.
          rewrite Forall_forall in F1, F2.
          assert (Ha : In a (b :: l2)) by (apply (Permutation_in _ P); left; reflexivity).
          assert (Hb : In b (a :: l1))
            by (apply (Permutation_in _ (Permutation_sym P)); left; reflexivity).
          destruct Ha as [Eab|Ha].
          * subst b. f_equal. apply IH; [assumption|assumption|].
            eapply Permutation_cons_inv; exact P.
          * exfalso. specialize (F2 a Ha).
            destruct Hb as [Eba|Hb].
            -- subst b. lia.
            -- specialize (F1 b Hb). lia.
    Qed.

    (** Insertion sort by [key] (as in [BracketedComposition]). *)
    Fixpoint ins (x : A) (l : list A) : list A :=
      match l with
      | [] => [x]
      | y :: l' => if key x <? key y then x :: y :: l' else y :: ins x l'
      end.

    Fixpoint isort (l : list A) : list A :=
      match l with
      | [] => []
      | x :: l' => ins x (isort l')
      end.

    Lemma ins_perm x l : Permutation (ins x l) (x :: l).
    Proof.
      induction l as [|y l IH]; cbn [ins]; [reflexivity|].
      destruct (key x <? key y); [reflexivity|].
      eapply perm_trans; [apply perm_skip; exact IH | apply perm_swap].
    Qed.

    Lemma isort_perm l : Permutation (isort l) l.
    Proof.
      induction l as [|x l IH]; cbn; [reflexivity|].
      eapply perm_trans; [apply ins_perm|]. apply perm_skip, IH.
    Qed.

    Lemma ins_sorted x l :
      StronglySorted (fun a b => key a < key b) l ->
      (forall y, In y l -> key x <> key y) ->
      StronglySorted (fun a b => key a < key b) (ins x l).
    Proof.
      induction 1 as [|y l Hs IH Hf]; intros Hne; cbn [ins].
      - repeat constructor.
      - destruct (key x <? key y) eqn:Hlt.
        + apply Nat.ltb_lt in Hlt.
          constructor; [constructor; assumption|].
          constructor; [exact Hlt|].
          rewrite Forall_forall in *. intros z Hz.
          specialize (Hf z Hz). cbn in *. lia.
        + apply Nat.ltb_ge in Hlt.
          assert (key y < key x) by (specialize (Hne y (or_introl eq_refl)); lia).
          constructor.
          * apply IH. intros z Hz. apply Hne. right; exact Hz.
          * rewrite Forall_forall in *. intros z Hz.
            apply (Permutation_in _ (ins_perm x l)) in Hz.
            destruct Hz as [<-|Hz]; [assumption|]. apply Hf, Hz.
    Qed.

    Lemma isort_sorted l :
      (forall x y, In x l -> In y l -> key x = key y -> x = y) ->
      NoDup l ->
      StronglySorted (fun a b => key a < key b) (isort l).
    Proof.
      induction l as [|x l IH]; intros Hinj Hnd; cbn; [constructor|].
      inversion Hnd as [|? ? Hx Hnd']; subst.
      apply ins_sorted.
      - apply IH; [|exact Hnd'].
        intros a b Ha Hb E. apply Hinj; [right|right|]; assumption.
      - intros y Hy E. apply (Permutation_in _ (isort_perm l)) in Hy.
        apply Hx. rewrite (Hinj x y (or_introl eq_refl) (or_intror Hy) E). exact Hy.
    Qed.

    (** Filtering commutes with sorting. *)
    Lemma filter_isort (f : A -> bool) l :
      (forall x y, In x l -> In y l -> key x = key y -> x = y) -> NoDup l ->
      filter f (isort l) = isort (filter f l).
    Proof.
      intros Hinj Hnd. apply ss_perm_eq.
      - apply ss_filter. apply isort_sorted; assumption.
      - apply isort_sorted.
        + intros x y Hx Hy. apply filter_In in Hx as [Hx _]. apply filter_In in Hy as [Hy _].
          apply Hinj; assumption.
        + apply NoDup_filter; assumption.
      - eapply perm_trans; [apply perm_filter, isort_perm|].
        apply Permutation_sym, isort_perm.
    Qed.
  End Lists.

  (** Sorting by two keys that order the elements the same way gives the
      same list. *)
  Lemma isort_key_equiv {A} (k1 k2 : A -> nat) l :
    (forall x y, In x l -> In y l -> k1 x < k1 y <-> k2 x < k2 y) ->
    (forall x y, In x l -> In y l -> k1 x = k1 y -> x = y) ->
    (forall x y, In x l -> In y l -> k2 x = k2 y -> x = y) ->
    NoDup l ->
    isort k1 l = isort k2 l.
  Proof.
    intros Hiff Hinj1 Hinj2 Hnd. apply (ss_perm_eq k2).
    - apply (ss_impl_in (fun a b => k1 a < k1 b)).
      + intros x y Hx Hy. apply Hiff.
        * apply (Permutation_in _ (isort_perm k1 l)), Hx.
        * apply (Permutation_in _ (isort_perm k1 l)), Hy.
      + apply isort_sorted; assumption.
    - apply isort_sorted; assumption.
    - eapply perm_trans; [apply isort_perm|]. apply Permutation_sym, isort_perm.
  Qed.

  (** ** Part 1: the theorem *)

  (** All data of one composed execution, as seen through its sequential
      underlay witness. *)
  Record Setting : Type := {
    Op : Type;               (* complete overlay operations *)
    Call : Type;             (* underlay calls *)
    OvOp : Type;             (* overlay events (call and result) *)
    Comp : Type;             (* components *)
    comp_dec : forall c c' : Comp, {c = c'} + {c <> c'};
    comp : Op -> Comp;
    ovl : Op -> OvOp;
    mF : Op -> FenceMode;            (* overlay fence modes *)
    IFc : Op -> Op -> Prop;          (* overlay semi-independence inside a component *)
    ucomp : Call -> Comp;
    mE : Call -> FenceMode;          (* underlay fence modes *)
    IEc : Call -> Call -> Prop;      (* underlay semi-independence inside a component *)
    lo : Op -> Call;                 (* first call of the window *)
    hi : Op -> Call;                 (* last call of the window *)
    lpc : Op -> Call;                (* linearization call (any thread) *)
    pos : Call -> nat;               (* position in the underlay witness *)
    ops : list Op;
    po : Op -> Op -> Prop;           (* same thread, invoked before *)
    rt : Op -> Op -> Prop;           (* response before invocation *)
    nuF : Comp -> list OvOp -> Prop; (* overlay specifications *)
  }.

  Section Window.
    Context (S : Setting).

    (** Semi-independence of the tensors (Def. 3.22 / [Tens.omap]). *)
    Definition IF (q q' : Op S) : Prop :=
      if comp_dec S (comp S q) (comp S q') then IFc S q q' else cross (mF S q) (mF S q').
    Definition IE (u u' : Call S) : Prop :=
      if comp_dec S (ucomp S u) (ucomp S u') then IEc S u u' else cross (mE S u) (mE S u').

    Definition lp (q : Op S) : nat := pos S (lpc S q).

    Definition in_comp (c : Comp S) (q : Op S) : bool :=
      if comp_dec S (comp S q) c then true else false.

    (** Everything except mode inheritance.  In a linked execution:
        - [h_ord]: the module semantics does not let [lo q'] overtake the
          earlier-enqueued [hi q] unless they are semi-independent
          (cross-continuation clause, [ii_order] in RelaxedModuleFacts),
          and relaxed happens-before (ii) of the underlay trace then
          orders them in every witness;
        - [h_rt]: [ret] waits for all handles, so [hi q] responds before
          [q] returns, and [lo q'] is issued after [q'] is invoked;
          relaxed happens-before (i);
        - [h_window], [h_S1], [h_S1_ord]: positional correctness of each
          component: its operations ordered by [lp] form a history of its
          specification that respects its own relaxed happens-before
          ([h_S1_ord]; the real-time part follows from [h_rt] and the
          window).  [intra_from_reflection] shows that order reflection
          [(hi q, lo q')] inside the component is one way to get
          [h_S1_ord]. *)
    Record Hyps0 : Prop := {
      h_nodup : NoDup (ops S);
      h_lp_inj : forall q q', In q (ops S) -> In q' (ops S) -> lp q = lp q' -> q = q';
      h_lo_comp : forall q, In q (ops S) -> ucomp S (lo S q) = comp S q;
      h_hi_comp : forall q, In q (ops S) -> ucomp S (hi S q) = comp S q;
      h_window : forall q, In q (ops S) -> pos S (lo S q) <= lp q <= pos S (hi S q);
      h_ord : forall q q', In q (ops S) -> In q' (ops S) -> po S q q' ->
                           ~ IE (hi S q) (lo S q') -> pos S (hi S q) < pos S (lo S q');
      h_rt : forall q q', In q (ops S) -> In q' (ops S) -> rt S q q' ->
                          pos S (hi S q) < pos S (lo S q');
      h_S1 : forall c, nuF S c (map (ovl S) (isort lp (filter (in_comp c) (ops S))));
      h_S1_ord : forall q q', In q (ops S) -> In q' (ops S) -> comp S q = comp S q' ->
                              po S q q' -> ~ IFc S q q' -> lp q < lp q';
    }.

    (** Mode inheritance (the cross-component part of (S2)). *)
    Definition Inherit : Prop :=
      (forall q, In q (ops S) -> acq_like (mF S q) -> acq_like (mE S (hi S q))) /\
      (forall q, In q (ops S) -> rel_like (mF S q) -> rel_like (mE S (lo S q))).

    (** The conclusion: an overlay witness that respects relaxed
        happens-before of the overlay (per-thread order not discharged by
        the overlay tensor's semi-independence, and real-time order) and
        projects onto every component as a history of its specification,
        i.e. a history of the tensor specification. *)
    Definition Conclusion : Prop :=
      exists ow : list (Op S),
        Permutation ow (ops S) /\
        (forall q q', In q (ops S) -> In q' (ops S) ->
           (po S q q' /\ ~ IF q q') \/ rt S q q' ->
           exists l1 l2, ow = l1 ++ q :: l2 /\ In q' l2) /\
        (forall c, nuF S c (map (ovl S) (filter (in_comp c) ow))).

    (** Order reflection inside a component suffices for [h_S1_ord]. *)
    Lemma intra_from_reflection :
      (forall q q', In q (ops S) -> In q' (ops S) -> po S q q' ->
                    ~ IE (hi S q) (lo S q') -> pos S (hi S q) < pos S (lo S q')) ->
      (forall q, In q (ops S) -> pos S (lo S q) <= lp q <= pos S (hi S q)) ->
      (forall q, In q (ops S) -> ucomp S (lo S q) = comp S q) ->
      (forall q, In q (ops S) -> ucomp S (hi S q) = comp S q) ->
      (forall q q', In q (ops S) -> In q' (ops S) -> comp S q = comp S q' ->
                    po S q q' -> ~ IFc S q q' -> ~ IEc S (hi S q) (lo S q')) ->
      forall q q', In q (ops S) -> In q' (ops S) -> comp S q = comp S q' ->
                   po S q q' -> ~ IFc S q q' -> lp q < lp q'.
    Proof.
      intros Hord Hwin Hlo Hhi Hrefl q q' Hq Hq' Hc Hpo HnI.
      pose proof (Hwin q Hq) as [_ W1]. pose proof (Hwin q' Hq') as [W2 _].
      assert (pos S (hi S q) < pos S (lo S q')); [|lia].
      apply Hord; try assumption. unfold IE. rewrite (Hhi q Hq), (Hlo q' Hq').
      destruct (comp_dec S (comp S q) (comp S q')) as [_|NE]; [|contradiction].
      apply Hrefl; assumption.
    Qed.

    Section WithHyps.
      Context (H : Hyps0) (Hinh : Inherit).

      Lemma cross_reflect q q' :
        In q (ops S) -> In q' (ops S) -> comp S q <> comp S q' ->
        ~ IF q q' -> ~ IE (hi S q) (lo S q').
      Proof.
        intros Hq Hq' Hne. unfold IE, IF.
        rewrite (h_hi_comp H q Hq), (h_lo_comp H q' Hq').
        destruct (comp_dec S (comp S q) (comp S q')) as [E|NE]; [contradiction|].
        intros HnIF [Hl Hr]. destruct (not_cross _ _ HnIF) as [Ha|Hr'].
        - exact (proj1 Hinh q Hq Ha Hl).
        - exact (proj2 Hinh q' Hq' Hr' Hr).
      Qed.

      Lemma lp_before q q' :
        In q (ops S) -> In q' (ops S) -> (po S q q' /\ ~ IF q q') \/ rt S q q' -> lp q < lp q'.
      Proof.
        intros Hq Hq' Hord.
        pose proof (h_window H q Hq) as [_ W1].
        pose proof (h_window H q' Hq') as [W2 _].
        destruct Hord as [[Hpo HnIF]|Hrt].
        - destruct (comp_dec S (comp S q) (comp S q')) as [E|NE].
          + apply (h_S1_ord H); try assumption.
            unfold IF in HnIF. destruct (comp_dec S (comp S q) (comp S q')); [exact HnIF|contradiction].
          + assert (pos S (hi S q) < pos S (lo S q'))
              by (apply (h_ord H); try assumption; apply cross_reflect; assumption).
            lia.
        - assert (pos S (hi S q) < pos S (lo S q')) by (apply (h_rt H); assumption).
          lia.
      Qed.

      Theorem window_composition : Conclusion.
      Proof.
        exists (isort lp (ops S)).
        assert (Hperm : Permutation (isort lp (ops S)) (ops S)) by apply isort_perm.
        pose proof (h_lp_inj H) as Hinj.
        assert (Hsort : StronglySorted (fun q q' => lp q < lp q') (isort lp (ops S)))
          by (apply isort_sorted; [exact Hinj | exact (h_nodup H)]).
        split; [exact Hperm|]. split.
        - intros q q' Hq Hq' Hord.
          assert (Hlt : lp q < lp q') by (apply lp_before; assumption).
          assert (Hin : In q (isort lp (ops S)))
            by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hq).
          assert (Hin' : In q' (isort lp (ops S)))
            by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hq').
          destruct (in_split _ _ Hin) as (l1 & l2 & E).
          exists l1, l2. split; [exact E|].
          rewrite E in Hin'. apply in_app_or in Hin' as [H1|[<-|H2]].
          + exfalso. rewrite E in Hsort.
            pose proof (ss_app_cons _ _ _ _ _ Hsort H1) as Hc. cbn in Hc. lia.
          + lia.
          + exact H2.
        - intros c. rewrite filter_isort by (exact Hinj || exact (h_nodup H)).
          apply (h_S1 H).
      Qed.
    End WithHyps.
  End Window.

  Arguments Hyps0 : clear implicits.
  Arguments Inherit : clear implicits.
  Arguments Conclusion : clear implicits.


  (** ** Part 2: mode inheritance for single-call windows *)

  Definition inherits (mF mlo mhi : FenceMode) : Prop :=
    (acq_like mF -> acq_like mhi) /\ (rel_like mF -> rel_like mlo).

  (** With [lo = hi = lp], mode inheritance is exactly: the overlay mode
      is at most the mode of the linearization call. *)
  Lemma inherits_single mF m : inherits mF m m <-> mF ≤f m.
  Proof.
    unfold inherits, acq_like, rel_like.
    destruct mF, m; cbn; tauto.
  Qed.

  (** Lock(O): window = the [acq] call (RFence).  RFence may be exported,
      Fence may not (agrees with [BracketedComposition]: LP = acq and the
      right overlay mode is RFence). *)
  Example lock_rfence_ok : inherits RFence RFence RFence.
  Proof. apply inherits_single; exact I. Qed.
  Example lock_fence_bad : ~ inherits Fence RFence RFence.
  Proof. rewrite inherits_single; cbn; tauto. Qed.

  (** LatchSet: window = the LP call on [seq], a plain (Local) access.
      Only Local may be exported (agrees with the litmus checks: update
      is neither lfence nor rfence). *)
  Example latch_local_ok : inherits Local Local Local.
  Proof. apply inherits_single; exact I. Qed.
  Example latch_rfence_bad : ~ inherits RFence Local Local.
  Proof. rewrite inherits_single; cbn; tauto. Qed.
  Example latch_lfence_bad : ~ inherits LFence Local Local.
  Proof. rewrite inherits_single; cbn; tauto. Qed.

  (** A two-call window whose first call is a release and last call an
      acquire can export Fence, although neither call alone could. *)
  Example release_then_acquire_fence : inherits Fence LFence RFence.
  Proof. unfold inherits, acq_like, rel_like; cbn; tauto. Qed.

  (** ** Before, as positions *)

  Section Before.
    Context {A : Type}.

    Definition before (l : list A) (a b : A) : Prop :=
      exists l1 l2, l = l1 ++ a :: l2 /\ In b l2.

    Lemma before_cons x l a b : before l a b -> before (x :: l) a b.
    Proof.
      intros (l1 & l2 & -> & Hb). exists (x :: l1), l2. split; [reflexivity|exact Hb].
    Qed.

    Lemma before_filter (f : A -> bool) l a b : before (filter f l) a b -> before l a b.
    Proof.
      induction l as [|x l IH]; cbn; intros Hb.
      - destruct Hb as (l1 & l2 & E & _). destruct l1; discriminate.
      - destruct (f x).
        + destruct Hb as (l1 & l2 & E & Hb2). destruct l1 as [|y l1]; cbn in E.
          * injection E as <- <-. exists [], l. split; [reflexivity|].
            apply filter_In in Hb2 as [Hb2 _]. exact Hb2.
          * injection E as <- E. apply before_cons, IH. exists l1, l2. split; assumption.
        + apply before_cons, IH, Hb.
    Qed.

    Definition before_i (l : list A) (a b : A) : Prop :=
      exists i j, i < j /\ nth_error l i = Some a /\ nth_error l j = Some b.

    Lemma before_to_i l a b : before l a b -> before_i l a b.
    Proof.
      intros (l1 & l2 & -> & Hb). apply In_nth_error in Hb as [k Hk].
      exists (length l1), (length l1 + S k). split; [lia|]. split.
      - rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity.
      - rewrite nth_error_app2 by lia.
        replace (length l1 + S k - length l1) with (S k) by lia. exact Hk.
    Qed.

    Lemma nth_error_inj (l : list A) i j (a : A) :
      NoDup l -> nth_error l i = Some a -> nth_error l j = Some a -> i = j.
    Proof.
      intros Hnd Hi Hj. apply (proj1 (NoDup_nth_error l) Hnd).
      - apply nth_error_Some. rewrite Hi. discriminate.
      - rewrite Hi, Hj. reflexivity.
    Qed.

    Lemma before_i_trans l a b c : NoDup l -> before_i l a b -> before_i l b c -> before_i l a c.
    Proof.
      intros Hnd (i & j & Hij & Hi & Hj) (j' & k & Hjk & Hj' & Hk).
      pose proof (nth_error_inj l j j' b Hnd Hj Hj'). subst j'.
      exists i, k. split; [lia|]. split; assumption.
    Qed.

    Lemma before_i_irrefl l a : NoDup l -> ~ before_i l a a.
    Proof.
      intros Hnd (i & j & Hij & Hi & Hj).
      pose proof (nth_error_inj l i j a Hnd Hi Hj). lia.
    Qed.
  End Before.

  (** ** Part 3: mode inheritance is necessary *)

  (** Two registers A and B over one plain cell each (every underlay call
      Local), store buffering:
      [T1: A.put(1); B.get() = 0 ‖ T2: B.put(1); A.get() = 0],
      with underlay witness [B.get, A.get, A.put, B.put].  Each operation
      is its own window and linearization call.  If the overlay claims
      Fence for every operation, all hypotheses except mode inheritance
      hold, and the conclusion fails: the claimed tensor specification
      forbids store buffering, the implementation produces it. *)
  Module Necessity.
    Inductive Q := Q1 | Q2 | Q3 | Q4.
    Inductive Obj := OA | OB.
    Definition obj_dec (a b : Obj) : {a = b} + {a <> b}.
    Proof. decide equality. Defined.

    Inductive RegOp := Put (v : nat) | Get (v : nat).
    Fixpoint reg_ok (cur : nat) (l : list RegOp) : Prop :=
      match l with
      | [] => True
      | Put v :: l' => reg_ok v l'
      | Get v :: l' => v = cur /\ reg_ok cur l'
      end.

    Definition compQ (q : Q) : Obj := match q with Q1 | Q4 => OA | Q2 | Q3 => OB end.
    Definition ovlQ (q : Q) : RegOp :=
      match q with Q1 => Put 1 | Q2 => Get 0 | Q3 => Put 1 | Q4 => Get 0 end.
    Definition poQ (q q' : Q) : Prop := (q = Q1 /\ q' = Q2) \/ (q = Q3 /\ q' = Q4).
    Definition posQ (q : Q) : nat := match q with Q2 => 0 | Q4 => 1 | Q1 => 2 | Q3 => 3 end.

    Definition setting (m : FenceMode) : Setting := {|
      Op := Q; Call := Q; OvOp := RegOp; Comp := Obj;
      comp_dec := obj_dec; comp := compQ; ovl := ovlQ;
      mF := fun _ => m; IFc := fun _ _ => False;
      ucomp := compQ; mE := fun _ => Local; IEc := fun _ _ => False;
      lo := fun q => q; hi := fun q => q; lpc := fun q => q; pos := posQ;
      ops := [Q1; Q2; Q3; Q4]; po := poQ; rt := fun _ _ => False;
      nuF := fun _ l => reg_ok 0 l;
    |}.

    Lemma hyps0 m : Hyps0 (setting m).
    Proof.
      constructor; cbn.
      - repeat constructor; cbn; intuition discriminate.
      - unfold lp; cbn. intros [] [] _ _ E; cbn in E; try reflexivity; discriminate.
      - intros; reflexivity.
      - intros; reflexivity.
      - unfold lp; cbn. intros; lia.
      - unfold IE, cross; cbn.
        intros q q' _ _ [[-> ->]|[-> ->]] Hn; exfalso; apply Hn; cbn; auto.
      - intros ? ? ? ? [].
      - intros []; cbn; auto.
      - intros q q' _ _ Hc [[-> ->]|[-> ->]]; cbn in Hc; discriminate.
    Qed.

    Lemma fence_not_inherited : ~ Inherit (setting Fence).
    Proof.
      intros [Ha _]. apply (Ha Q1); unfold acq_like; cbn; auto.
    Qed.

    Theorem fence_claim_fails : ~ Conclusion (setting Fence).
    Proof.
      intros (ow & Hperm & Hord & Hspec).
      assert (Hnd : NoDup ow)
        by (apply (Permutation_NoDup (Permutation_sym Hperm));
            exact (@h_nodup _ (hyps0 Fence))).
      set (S := setting Fence) in *.
      (* the register specification forces the order of each pair *)
      assert (Hreg : forall c a b,
                 filter (in_comp S c) ow = [a; b] \/ filter (in_comp S c) ow = [b; a] ->
                 ~ reg_ok 0 [ovlQ a; ovlQ b] -> before_i ow b a).
      { intros c a b Hin Hbad. pose proof (Hspec c) as Hc.
        destruct Hin as [E|E]; rewrite E in Hc.
        - exfalso. apply Hbad. exact Hc.
        - apply before_to_i, (before_filter (in_comp S c)). rewrite E.
          exists [], [a]. split; [reflexivity|left; reflexivity]. }
      assert (HA : filter (in_comp S OA) ow = [Q1; Q4] \/ filter (in_comp S OA) ow = [Q4; Q1]).
      { apply Permutation_length_2_inv. apply Permutation_sym.
        exact (perm_filter (in_comp S OA) _ _ Hperm). }
      assert (HB : filter (in_comp S OB) ow = [Q3; Q2] \/ filter (in_comp S OB) ow = [Q2; Q3]).
      { assert (P : Permutation (filter (in_comp S OB) ow) [Q2; Q3])
          by exact (perm_filter (in_comp S OB) _ _ Hperm).
        apply Permutation_sym, Permutation_length_2_inv in P as [E|E]; [right|left]; exact E. }
      pose proof (Hreg OA Q1 Q4 HA ltac:(cbn; intros [E _]; discriminate)) as B41.
      pose proof (Hreg OB Q3 Q2 HB ltac:(cbn; intros [E _]; discriminate)) as B23.
      (* the claimed Fence modes keep program order across the two registers *)
      assert (B12 : before_i ow Q1 Q2).
      { apply before_to_i. apply (Hord Q1 Q2); [cbn; auto 6 | cbn; auto 6 |].
        left. split; [cbn; left; split; reflexivity|]. unfold IF, cross; cbn; tauto. }
      assert (B34 : before_i ow Q3 Q4).
      { apply before_to_i. apply (Hord Q3 Q4); [cbn; auto 6 | cbn; auto 6 |].
        left. split; [cbn; right; split; reflexivity|]. unfold IF, cross; cbn; tauto. }
      (* Q1 < Q2 < Q3 < Q4 < Q1 *)
      apply (before_i_irrefl ow Q1 Hnd).
      eapply before_i_trans; [exact Hnd | exact B12 |].
      eapply before_i_trans; [exact Hnd | exact B23 |].
      eapply before_i_trans; [exact Hnd | exact B34 | exact B41].
    Qed.

    (** ** Part 4: positive control *)

    (** With the honest mode Local (inherited from the Local cell calls),
        all hypotheses hold, and the theorem gives an overlay witness for
        the store-buffering execution: the tensor of two Local registers
        allows it, as it should. *)
    Lemma local_inherited : Inherit (setting Local).
    Proof.
      split; intros q _ Hq; exfalso; apply Hq; exact I.
    Qed.

    Corollary sb_allowed_with_local_modes : Conclusion (setting Local).
    Proof. apply window_composition; [apply hyps0 | apply local_inherited]. Qed.
  End Necessity.

  (** ** Part 5: vertical closure *)

  Lemma sorted_before {A} (key : A -> nat) l a b :
    StronglySorted (fun x y => key x < key y) l -> In a l -> In b l ->
    key a < key b -> before l a b.
  Proof.
    intros Hs Ha Hb Hlt.
    destruct (in_split _ _ Ha) as (l1 & l2 & E).
    exists l1, l2. split; [exact E|].
    rewrite E in Hb. apply in_app_or in Hb as [H1|[<-|H2]].
    - exfalso. rewrite E in Hs. pose proof (ss_app_cons _ _ _ _ _ Hs H1) as Hc. cbn in Hc. lia.
    - lia.
    - exact H2.
  Qed.

  Section Vertical.
    (** Three levels: [Gop] (top overlay operations, implemented by N over
        F), [Fop] (middle operations, implemented by M over E), [Ecall]
        (bottom calls).  The middle witness [V] is M's linearization: the
        F operations ordered by the E-position of their linearization
        call. *)
    Context {Gop Fop Ecall GEv : Type}.
    Context (Gs : list Gop) (Fs : list Fop).
    Context (loN hiN lpN : Gop -> Fop) (loM hiM lpcM : Fop -> Ecall) (posE : Ecall -> nat).
    Context (ovlG : Gop -> GEv) (nuG : list GEv -> Prop).
    Context (mG : Gop -> FenceMode) (mFv : Fop -> FenceMode) (mEv : Ecall -> FenceMode).

    Definition keyM (f : Fop) : nat := posE (lpcM f).
    Definition V : list Fop := isort keyM Fs.

    Hypothesis keyM_inj : forall f f', In f Fs -> In f' Fs -> keyM f = keyM f' -> f = f'.
    Hypothesis Fs_nodup : NoDup Fs.
    (** M's windows (S1 for M). *)
    Hypothesis winM : forall f, In f Fs -> posE (loM f) <= keyM f <= posE (hiM f).
    (** N's window calls are complete F operations. *)
    Hypothesis N_calls : forall g, In g Gs -> In (loN g) Fs /\ In (hiN g) Fs /\ In (lpN g) Fs.
    (** N's windows, stated in the F witness [V]: [lo ≤ lp ≤ hi]. *)
    Hypothesis winN : forall g, In g Gs ->
      ~ before V (lpN g) (loN g) /\ ~ before V (hiN g) (lpN g).
    (** N's positional correctness depends only on the order of [V]: any
        key that sorts [V] strictly may be used to order the G operations
        by their linearization F operation ([isort_key_equiv] shows that
        all such keys give the same list). *)
    Hypothesis S1N : forall kV : Fop -> nat,
      StronglySorted (fun a b => kV a < kV b) V ->
      (forall f f', In f Fs -> In f' Fs -> kV f = kV f' -> f = f') ->
      nuG (map ovlG (isort (fun g => kV (lpN g)) Gs)).

    Lemma V_sorted : StronglySorted (fun a b => keyM a < keyM b) V.
    Proof. apply isort_sorted; assumption. Qed.

    Lemma in_V f : In f Fs -> In f V.
    Proof. intros Hf. apply (Permutation_in _ (Permutation_sym (isort_perm keyM Fs))), Hf. Qed.

    Lemma key_le a b : In a Fs -> In b Fs -> ~ before V b a -> keyM a <= keyM b.
    Proof.
      intros Ha Hb Hn. destruct (Nat.le_gt_cases (keyM a) (keyM b)) as [Hle|Hgt]; [exact Hle|].
      exfalso. apply Hn. apply (sorted_before keyM); [apply V_sorted | apply in_V; assumption ..|].
      exact Hgt.
    Qed.

    (** The composed window [lo := loM ∘ loN], [hi := hiM ∘ hiN] contains
        the composed linearization call [lpcM ∘ lpN]. *)
    Theorem vertical_window g : In g Gs ->
      posE (loM (loN g)) <= posE (lpcM (lpN g)) <= posE (hiM (hiN g)).
    Proof.
      intros Hg. destruct (N_calls g Hg) as (Hlo & Hhi & Hlp).
      destruct (winN g Hg) as [W1 W2].
      pose proof (key_le _ _ Hlo Hlp W1). pose proof (key_le _ _ Hlp Hhi W2).
      pose proof (winM _ Hlo). pose proof (winM _ Hhi).
      unfold keyM in *. lia.
    Qed.

    (** Positional correctness of the composite: ordering the G operations
        by the E-position of the composed linearization call gives a
        history of N's specification. *)
    Theorem vertical_S1 : nuG (map ovlG (isort (fun g => posE (lpcM (lpN g))) Gs)).
    Proof. apply (S1N keyM); [apply V_sorted | exact keyM_inj]. Qed.

    (** Mode inheritance composes. *)
    Theorem vertical_inherit g :
      (acq_like (mG g) -> acq_like (mFv (hiN g))) ->
      (rel_like (mG g) -> rel_like (mFv (loN g))) ->
      (forall f, acq_like (mFv f) -> acq_like (mEv (hiM f))) ->
      (forall f, rel_like (mFv f) -> rel_like (mEv (loM f))) ->
      inherits (mG g) (mEv (loM (loN g))) (mEv (hiM (hiN g))).
    Proof. intros HaN HrN HaM HrM. split; auto. Qed.
  End Vertical.

  (** The statement in one line. *)
  Corollary window_composition' (S : Setting) : Hyps0 S -> Inherit S -> Conclusion S.
  Proof. intros H Hinh. exact (window_composition S H Hinh). Qed.

End WindowComposition.
