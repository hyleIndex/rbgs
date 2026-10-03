(** * Horizontal composition of lock-bracketed components

    This file studies two lock-protected objects placed side by side,
    [Lock(O1) ⊎ Lock(O2)], where every overlay method has the shape
    [acq; body; rel] over [Lock ⊗ Data].

    - Part 1 shows that the compatibility condition of the paper
      (Def. 5.8: for every pair of underlay calls issued by two overlay
      methods, underlay semi-independence iff overlay semi-independence)
      can never hold for such components, whatever overlay
      semi-independence relation and fence modes are chosen, because
      [(acq1, acq2)] is not semi-independent while [(rel1, acq2)] is.
      It then shows that a variant which compares only a designated
      linearization-point call ([acq]) does hold, with every overlay
      operation given mode [RFence] (an overlay operation behaves like
      an acquire: later operations of other objects cannot be
      linearized before it, earlier ones can be linearized after it).

    - Part 2 proves the composition theorem that replaces Def. 5.8 in
      this situation, at the level of sequential witnesses: ordering the
      overlay operations by the witness position of their [acq] call
      yields an overlay witness that (a) respects per-thread overlay
      order with an empty overlay semi-independence relation and the
      real-time order, and (b) projects onto each component as a trace
      of that component's overlay specification, provided each component
      is correct when its critical sections run one after the other (a
      purely local obligation).

    - Part 3 instantiates Part 2 on two lock-protected registers and
      machine-checks that the store-buffering (SB) and IRIW weak
      outcomes are impossible ([SB.sb_forbidden], [IRIW.iriw_forbidden]);
      [SB.sb_hypotheses_satisfiable] checks that the hypotheses are met
      by a sequential run with a different outcome, so the theorems are
      not vacuous.

    The abstract hypotheses of Part 2 are the facts that the relaxed
    trace semantics provides about a linked execution (see the comment
    on [Hyps]).  [BracketedLink] derives all of them from complete
    executions of [RelaxedModuleSemantics.module_step_tagged], and
    [LockedRegisters] redoes the SB example against the semantics. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.

Import ListNotations.

Module BracketedComposition.
  Import RelaxedSig.

  (** ** Part 1: the compatibility condition of Def. 5.8 *)

  Lemma tsi_lr_iff (E F : RelaxedSig.t) (e : Sig.op (effect E)) (f : Sig.op (effect F)) :
    Tens.tensor_semi_independent E F (inl e) (inr f) <->
    mode E e ≤f LFence /\ mode F f ≤f RFence.
  Proof.
    split.
    - intros H. inversion H; subst. split; assumption.
    - intros [H1 H2]. apply Tens.tsi_cross_lr; assumption.
  Qed.

  Lemma tsi_rl_iff (E F : RelaxedSig.t) (e : Sig.op (effect E)) (f : Sig.op (effect F)) :
    Tens.tensor_semi_independent E F (inr f) (inl e) <->
    mode F f ≤f LFence /\ mode E e ≤f RFence.
  Proof.
    split.
    - intros H. inversion H; subst. split; assumption.
    - intros [H1 H2]. apply Tens.tsi_cross_rl; assumption.
  Qed.

  Section Compatibility.
    Context (E1 E2 F1 F2 : RelaxedSig.t).
    Context (HE : handle E1 = handle E2) (HF : handle F1 = handle F2).

    (** [calls1 q m]: the body of the overlay operation [q] of the first
        component contains a call to the underlay operation [m]
        (the relation [q -invoke->_M m] of Def. 5.8). *)
    Context (calls1 : Sig.op (effect F1) -> Sig.op (effect E1) -> Prop).
    Context (calls2 : Sig.op (effect F2) -> Sig.op (effect E2) -> Prop).

    Definition Iu : relation (Sig.op (effect (Tens.omap E1 E2 HE))) :=
      semi_independent (Tens.omap E1 E2 HE).

    Definition Io : relation (Sig.op (effect (Tens.omap F1 F2 HF))) :=
      semi_independent (Tens.omap F1 F2 HF).

    (** Def. 5.8, as printed. *)
    Definition compatible : Prop :=
      (forall q1 m1 q2 m2, calls1 q1 m1 -> calls2 q2 m2 ->
         (Iu (@Tens.op_i1 E1 E2 HE m1) (@Tens.op_i2 E1 E2 HE m2) <->
          Io (@Tens.op_i1 F1 F2 HF q1) (@Tens.op_i2 F1 F2 HF q2))) /\
      (forall q1 m1 q2 m2, calls1 q1 m1 -> calls2 q2 m2 ->
         (Iu (@Tens.op_i2 E1 E2 HE m2) (@Tens.op_i1 E1 E2 HE m1) <->
          Io (@Tens.op_i2 F1 F2 HF q2) (@Tens.op_i1 F1 F2 HF q1))).

    Lemma cross_blocked (e : Sig.op (effect E1)) (f : Sig.op (effect E2)) :
      mode E1 e = RFence ->
      ~ Iu (@Tens.op_i1 E1 E2 HE e) (@Tens.op_i2 E1 E2 HE f).
    Proof.
      intros Hm H. unfold Iu, Tens.op_i1, Tens.op_i2 in H. cbn in H.
      apply tsi_lr_iff in H as [H _]. rewrite Hm in H. exact H.
    Qed.

    Lemma cross_open (e : Sig.op (effect E1)) (f : Sig.op (effect E2)) :
      mode E1 e ≤f LFence -> mode E2 f ≤f RFence ->
      Iu (@Tens.op_i1 E1 E2 HE e) (@Tens.op_i2 E1 E2 HE f).
    Proof.
      intros H1 H2. unfold Iu, Tens.op_i1, Tens.op_i2. cbn.
      apply tsi_lr_iff. split; assumption.
    Qed.

    (** If a method of the first component calls both an [RFence]
        operation (an acquire) and an operation of mode at most
        [LFence] (a release), and a method of the second component calls
        an [RFence] operation, then Def. 5.8 fails, for every choice of
        overlay signatures [F1], [F2]. *)
    Theorem bracketed_not_compatible q1 a1 r1 q2 a2 :
      calls1 q1 a1 -> calls1 q1 r1 -> calls2 q2 a2 ->
      mode E1 a1 = RFence -> mode E1 r1 ≤f LFence -> mode E2 a2 ≤f RFence ->
      ~ compatible.
    Proof.
      intros Ha1 Hr1 Ha2 Hma1 Hmr1 Hma2 [Hc _].
      apply (cross_blocked a1 a2 Hma1).
      apply (proj2 (Hc q1 a1 q2 a2 Ha1 Ha2)).
      apply (proj1 (Hc q1 r1 q2 a2 Hr1 Ha2)).
      apply cross_open; assumption.
    Qed.

  End Compatibility.

  Section LPCompatibility.
    Context (E1 E2 F1 F2 : RelaxedSig.t).
    Context (HE : handle E1 = handle E2) (HF : handle F1 = handle F2).

    (** A variant that compares only one designated call per overlay
        operation, its linearization-point call. *)
    Context (lp1 : Sig.op (effect F1) -> Sig.op (effect E1)) (lp2 : Sig.op (effect F2) -> Sig.op (effect E2)).

    Definition lp_compatible : Prop :=
      (forall q1 q2,
         Iu E1 E2 HE (@Tens.op_i1 E1 E2 HE (lp1 q1)) (@Tens.op_i2 E1 E2 HE (lp2 q2)) <->
         Io F1 F2 HF (@Tens.op_i1 F1 F2 HF q1) (@Tens.op_i2 F1 F2 HF q2)) /\
      (forall q1 q2,
         Iu E1 E2 HE (@Tens.op_i2 E1 E2 HE (lp2 q2)) (@Tens.op_i1 E1 E2 HE (lp1 q1)) <->
         Io F1 F2 HF (@Tens.op_i2 F1 F2 HF q2) (@Tens.op_i1 F1 F2 HF q1)).

    Lemma rfence_lp_compatible :
      (forall q, mode E1 (lp1 q) = RFence) ->
      (forall q, mode E2 (lp2 q) = RFence) ->
      (forall q, mode F1 q = RFence) ->
      (forall q, mode F2 q = RFence) ->
      lp_compatible.
    Proof.
      intros H1 H2 H3 H4.
      unfold lp_compatible, Iu, Io, Tens.op_i1, Tens.op_i2; cbn.
      split; intros q1 q2;
        rewrite ?tsi_lr_iff, ?tsi_rl_iff;
        rewrite ?H1, ?H2, ?H3, ?H4; cbn; tauto.
    Qed.

  End LPCompatibility.

  (** *** A concrete instance: two lock-protected registers *)

  Inductive LockOp := Acq | Rel.
  Inductive CellOp := Rd | Wr (v : nat).
  Inductive RegCall := PutC (v : nat) | GetC.

  Definition LockE : Sig.t := {| Sig.op := LockOp; Sig.ar := fun _ => unit |}.
  Definition CellE : Sig.t :=
    {| Sig.op := CellOp;
       Sig.ar := fun o => match o with Rd => nat | Wr _ => unit end |}.
  Definition RegE : Sig.t :=
    {| Sig.op := RegCall;
       Sig.ar := fun o => match o with GetC => nat | PutC _ => unit end |}.

  Definition Lock : RelaxedSig.t :=
    {| effect := LockE;
       handle := nat;
       semi_independent := fun _ _ => False;
       mode := fun o : LockOp => match o with Acq => RFence | Rel => LFence end |}.

  Definition Cell : RelaxedSig.t :=
    {| effect := CellE;
       handle := nat;
       semi_independent := fun _ _ => False;
       mode := fun _ => Local |}.

  Definition LockCell : RelaxedSig.t := Tens.omap Lock Cell eq_refl.

  (** Any overlay signature on register calls. *)
  Definition RegSig (I : relation RegCall) (m : RegCall -> FenceMode) : RelaxedSig.t :=
    {| effect := RegE; handle := nat; semi_independent := I; mode := m |}.

  Definition acq_call : Sig.op (effect LockCell) := @Tens.op_i1 Lock Cell eq_refl Acq.
  Definition rel_call : Sig.op (effect LockCell) := @Tens.op_i1 Lock Cell eq_refl Rel.
  Definition cell_call (q : RegCall) : Sig.op (effect LockCell) :=
    @Tens.op_i2 Lock Cell eq_refl (match q with PutC v => Wr v | GetC => Rd end).

  (** [put(v) = acq; wrt(v); rel] and [get() = acq; rd; rel]. *)
  Definition lock_reg_calls (q : RegCall) (m : Sig.op (effect LockCell)) : Prop :=
    m = acq_call \/ m = cell_call q \/ m = rel_call.

  Corollary lock_registers_not_compatible
      (I1 I2 : relation RegCall) (m1 m2 : RegCall -> FenceMode) :
    ~ compatible LockCell LockCell (RegSig I1 m1) (RegSig I2 m2)
        eq_refl eq_refl lock_reg_calls lock_reg_calls.
  Proof.
    apply (bracketed_not_compatible LockCell LockCell (RegSig I1 m1) (RegSig I2 m2)
             eq_refl eq_refl lock_reg_calls lock_reg_calls
             (PutC 1) acq_call rel_call GetC acq_call).
    - left; reflexivity.
    - right; right; reflexivity.
    - left; reflexivity.
    - reflexivity.
    - exact I.
    - exact I.
  Qed.

  Corollary lock_registers_lp_compatible (I1 I2 : relation RegCall) :
    lp_compatible LockCell LockCell
      (RegSig I1 (fun _ => RFence)) (RegSig I2 (fun _ => RFence))
      eq_refl eq_refl (fun _ => acq_call) (fun _ => acq_call).
  Proof.
    apply rfence_lp_compatible; intros; reflexivity.
  Qed.

  (** ** Part 2: the composition theorem *)

  (** *** List lemmas *)

  Section Lists.
    Context {A : Type}.

    Lemma filter_all (f : A -> bool) (l : list A) :
      (forall x, In x l -> f x = true) -> filter f l = l.
    Proof.
      induction l as [|a l IH]; cbn; intros H; [reflexivity|].
      rewrite (H a (or_introl eq_refl)). f_equal.
      apply IH. intros x Hx. apply H. right; exact Hx.
    Qed.

    Lemma filter_none (f : A -> bool) (l : list A) :
      (forall x, In x l -> f x = false) -> filter f l = [].
    Proof.
      induction l as [|a l IH]; cbn; intros H; [reflexivity|].
      rewrite (H a (or_introl eq_refl)).
      apply IH. intros x Hx. apply H. right; exact Hx.
    Qed.

    Lemma filter_filter_sub (f g : A -> bool) (l : list A) :
      (forall x, f x = true -> g x = true) -> filter f (filter g l) = filter f l.
    Proof.
      induction l as [|a l IH]; cbn; intros H; [reflexivity|].
      destruct (g a) eqn:Hg; cbn.
      - destruct (f a); [f_equal|]; apply IH; exact H.
      - destruct (f a) eqn:Hf.
        + rewrite (H a Hf) in Hg. discriminate.
        + apply IH; exact H.
    Qed.

    Lemma filter_filter_and (f g : A -> bool) (l : list A) :
      filter f (filter g l) = filter (fun x => g x && f x) l.
    Proof.
      induction l as [|a l IH]; cbn; [reflexivity|].
      destruct (g a); cbn; [destruct (f a); cbn; [f_equal|]|]; exact IH.
    Qed.

    Lemma filter_single (f : A -> bool) (l : list A) (x : A) :
      NoDup l -> In x l -> (forall y, In y l -> f y = true <-> y = x) ->
      filter f l = [x].
    Proof.
      induction l as [|a l IH]; intros Hnd Hx Hf; [contradiction|].
      inversion Hnd as [|? ? Ha Hnd']; subst. cbn.
      destruct (f a) eqn:Hfa.
      - pose proof (proj1 (Hf a (or_introl eq_refl)) Hfa) as ->.
        f_equal. apply filter_none. intros y Hy.
        destruct (f y) eqn:Hfy; [|reflexivity]. exfalso.
        pose proof (proj1 (Hf y (or_intror Hy)) Hfy) as ->. contradiction.
      - destruct Hx as [<-|Hx].
        + pose proof (proj2 (Hf a (or_introl eq_refl)) eq_refl). congruence.
        + apply IH; [exact Hnd' | exact Hx |].
          intros y Hy. apply Hf. right; exact Hy.
    Qed.

    Lemma ss_filter (R : A -> A -> Prop) (f : A -> bool) (l : list A) :
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
      - rewrite Forall_forall in Hf. apply Hf.
        apply in_or_app. right; left; reflexivity.
      - apply IH; assumption.
    Qed.

    Lemma ss_tail (R : A -> A -> Prop) l1 l2 :
      StronglySorted R (l1 ++ l2) -> StronglySorted R l2.
    Proof.
      induction l1 as [|a l1 IH]; cbn; intros H; [exact H|].
      apply IH. inversion H; assumption.
    Qed.

    Context (key : A -> nat).

    Lemma ss_nodup l :
      StronglySorted (fun x y => key x < key y) l -> NoDup l.
    Proof.
      induction 1 as [|a l Hs IH Hf]; constructor; [|exact IH].
      intro Ha. rewrite Forall_forall in Hf. specialize (Hf a Ha). cbn in Hf. lia.
    Qed.

    Lemma ss_key_inj l x y :
      StronglySorted (fun x y => key x < key y) l ->
      In x l -> In y l -> key x = key y -> x = y.
    Proof.
      induction 1 as [|a l Hs IH Hf]; intros Hx Hy Hk; [contradiction|].
      rewrite Forall_forall in Hf.
      destruct Hx as [<-|Hx], Hy as [<-|Hy].
      - reflexivity.
      - specialize (Hf y Hy). cbn in Hf. lia.
      - specialize (Hf x Hx). cbn in Hf. lia.
      - apply IH; assumption.
    Qed.

    Lemma split_before l a g :
      StronglySorted (fun x y => key x < key y) l ->
      In a l -> In g l -> key a < key g ->
      exists l1 l2, l = l1 ++ g :: l2 /\ In a l1.
    Proof.
      intros Hs Ha Hg Hlt.
      destruct (in_split _ _ Hg) as (l1 & l2 & E).
      exists l1, l2. split; [exact E|].
      rewrite E in Ha, Hs.
      apply in_app_or in Ha as [Ha|[<-|Ha]]; [exact Ha | lia |].
      exfalso. apply ss_tail in Hs.
      inversion Hs as [|? ? _ Hf]; subst.
      rewrite Forall_forall in Hf. specialize (Hf a Ha). cbn in Hf. lia.
    Qed.

    (** Splitting a key-sorted list whose [P]-elements all precede its
        [Q]-elements. *)
    Lemma group_split (P Q : A -> bool) (l : list A) :
      StronglySorted (fun x y => key x < key y) l ->
      (forall x, In x l -> P x = true \/ Q x = true) ->
      (forall x, In x l -> P x = true -> Q x = false) ->
      (forall x y, In x l -> In y l -> P x = true -> Q y = true -> key x < key y) ->
      l = filter P l ++ filter Q l.
    Proof.
      induction 1 as [|a l Hs IH Hf]; intros Hcov Hexcl Hord; [reflexivity|].
      rewrite Forall_forall in Hf. cbn.
      destruct (P a) eqn:HPa.
      - rewrite (Hexcl a (or_introl eq_refl) HPa). cbn. f_equal.
        apply IH.
        + intros x Hx. apply Hcov. right; exact Hx.
        + intros x Hx. apply Hexcl. right; exact Hx.
        + intros x y Hx Hy. apply Hord; right; assumption.
      - assert (HQa : Q a = true).
        { destruct (Hcov a (or_introl eq_refl)) as [H|H]; [congruence|exact H]. }
        rewrite HQa. rewrite (filter_none P l). cbn. f_equal. symmetry. apply filter_all.
        + intros x Hx. destruct (Hcov x (or_intror Hx)) as [H|H]; [|exact H].
          exfalso. specialize (Hord x a (or_intror Hx) (or_introl eq_refl) H HQa).
          specialize (Hf x Hx). cbn in Hf. lia.
        + intros x Hx. destruct (P x) eqn:HPx; [|reflexivity]. exfalso.
          specialize (Hord x a (or_intror Hx) (or_introl eq_refl) HPx HQa).
          specialize (Hf x Hx). cbn in Hf. lia.
    Qed.

    Context {B : Type} (grp : A -> B).
    Context (dec : forall b b' : B, {b = b'} + {b <> b'}) (lk : B -> nat).

    Definition in_grp (g : B) (x : A) : bool :=
      if dec (grp x) g then true else false.

    (** A key-sorted list in which elements of earlier groups precede
        elements of later groups is the concatenation of its groups. *)
    Lemma group_concat (G : list B) : forall l,
      StronglySorted (fun x y => key x < key y) l ->
      NoDup G ->
      StronglySorted (fun g g' => lk g < lk g') G ->
      (forall x, In x l -> In (grp x) G) ->
      (forall x y, In x l -> In y l -> lk (grp x) < lk (grp y) -> key x < key y) ->
      l = concat (map (fun g => filter (in_grp g) l) G).
    Proof.
      induction G as [|g G IH]; intros l Hl Hnd HG Hcov Hord.
      - destruct l as [|x l]; [reflexivity|].
        exfalso. exact (Hcov x (or_introl eq_refl)).
      - inversion Hnd as [|? ? Hg Hnd']; subst.
        inversion HG as [|? ? HG' HGf]; subst.
        rewrite Forall_forall in HGf.
        set (Q := fun x => if in_dec dec (grp x) G then true else false).
        rewrite (group_split (in_grp g) Q l Hl) at 1.
        + cbn [map concat]. f_equal.
          rewrite (IH (filter Q l)).
          * apply f_equal. apply map_ext_in. intros g' Hg'.
            apply filter_filter_sub. intros x Hx.
            unfold in_grp, Q in *.
            destruct (dec (grp x) g') as [E|E]; [|discriminate].
            destruct (in_dec dec (grp x) G) as [_|N]; [reflexivity|].
            rewrite E in N. contradiction.
          * apply ss_filter; exact Hl.
          * exact Hnd'.
          * exact HG'.
          * intros x Hx. apply filter_In in Hx as [_ Hx]. unfold Q in Hx.
            destruct (in_dec dec (grp x) G); [assumption|discriminate].
          * intros x y Hx Hy. apply filter_In in Hx as [Hx _].
            apply filter_In in Hy as [Hy _]. apply Hord; assumption.
        + intros x Hx. unfold in_grp, Q.
          destruct (Hcov x Hx) as [E|Hin].
          * left. destruct (dec (grp x) g) as [_|N]; [reflexivity|]. congruence.
          * right. destruct (in_dec dec (grp x) G); [reflexivity|contradiction].
        + intros x Hx HP. unfold in_grp, Q in *.
          destruct (dec (grp x) g) as [E|_]; [|discriminate].
          destruct (in_dec dec (grp x) G) as [Hin|]; [|reflexivity].
          rewrite E in Hin. contradiction.
        + intros x y Hx Hy HP HQ. apply Hord; [assumption|assumption|].
          unfold in_grp, Q in *.
          destruct (dec (grp x) g) as [E|_]; [|discriminate].
          destruct (in_dec dec (grp y) G) as [Hin|]; [|discriminate].
          rewrite E. specialize (HGf _ Hin). cbn in HGf. exact HGf.
    Qed.

  End Lists.

  (** *** Insertion sort by a key *)

  Section Sort.
    Context {A : Type} (key : A -> nat).

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

  End Sort.

  (** *** The theorem *)

  Section Composition.
    Context {Sec UOp OvOp Comp : Type}.
    Context (sec_dec : forall s s' : Sec, {s = s'} + {s <> s'}).
    Context (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).

    (** [comp s]: the component (object) that overlay operation [s]
        belongs to.  [owner u]: the overlay operation whose body issued
        underlay call [u].  [acq s], [rel s]: the lock calls that open and
        close the body of [s].  [ovl s]: the overlay event of [s] (call
        and result).  [pos u]: the position of [u] in the underlay
        sequential witness. *)
    Context (comp : Sec -> Comp) (owner : UOp -> Sec).
    Context (acq rel : Sec -> UOp) (ovl : Sec -> OvOp) (pos : UOp -> nat).

    (** [secs]: the complete overlay operations; [W]: the underlay
        witness (a sequential trace of underlay operations); [po s s']:
        same thread, [s] invoked before [s']; [rt s s']: the response of
        [s] precedes the invocation of [s']. *)
    Context (secs : list Sec) (W : list UOp) (po rt : Sec -> Sec -> Prop).

    (** Per-component underlay and overlay specifications, and a
        per-operation predicate on the witness order of its own calls. *)
    Context (nuE : Comp -> list UOp -> Prop) (nuF : Comp -> list OvOp -> Prop).
    Context (body_ok : Sec -> list UOp -> Prop).

    Definition lp (s : Sec) : nat := pos (acq s).

    Definition owned_by (s : Sec) (u : UOp) : bool :=
      if sec_dec (owner u) s then true else false.

    Definition in_comp (c : Comp) (s : Sec) : bool :=
      if comp_dec (comp s) c then true else false.

    Definition uop_in_comp (c : Comp) (u : UOp) : bool := in_comp c (owner u).

    Definition body (s : Sec) : list UOp := filter (owned_by s) W.

    (** The hypotheses.  In a linked execution they come from:
        - [hyp_rfence]: relaxed happens-before (ii) of the underlay trace,
          because [acq] has mode [RFence], so no later call of the same
          thread is semi-independent of it, and the module semantics
          issues the later call after [acq] (cross-continuation clause);
        - [hyp_rt]: relaxed happens-before (i), because an overlay
          response is emitted only after all the calls of its body have
          responded ([ret] waits for all handles);
        - [hyp_in]: the same two facts inside one body ([acq] first,
          [rel] last, [rel] has mode [LFence]);
        - [hyp_mutex] and [hyp_nuE]: the underlay witness belongs to the
          tensor of the lock and data specifications (Def. 3.22), and
          the lock specification forbids overlapping critical sections
          of the same lock;
        - [hyp_local]: correctness of each component in isolation, when
          its critical sections run one after the other.  It mentions
          only that component's specifications. *)
    Record Hyps : Prop := {
      hyp_acq_owner : forall s, In s secs -> owner (acq s) = s;
      hyp_secs_nodup : NoDup secs;
      hyp_W_sorted : StronglySorted (fun u v => pos u < pos v) W;
      hyp_W_owner : forall u, In u W -> In (owner u) secs;
      hyp_W_acq : forall s, In s secs -> In (acq s) W;
      hyp_rfence : forall s u, In s secs -> In u W -> po s (owner u) ->
                               pos (acq s) < pos u;
      hyp_rt : forall u u', In u W -> In u' W -> rt (owner u) (owner u') ->
                            pos u < pos u';
      hyp_in : forall u, In u W ->
                         pos (acq (owner u)) <= pos u <= pos (rel (owner u));
      hyp_mutex : forall s s', In s secs -> In s' secs -> s <> s' ->
                               comp s = comp s' ->
                               pos (rel s) < pos (acq s') \/
                               pos (rel s') < pos (acq s);
      hyp_nuE : forall c, nuE c (filter (uop_in_comp c) W);
      hyp_body_ok : forall s, In s secs -> body_ok s (body s);
      hyp_local : forall c (G : list Sec) (b : Sec -> list UOp),
          NoDup G ->
          (forall s, In s G -> comp s = c /\ body_ok s (b s)) ->
          nuE c (concat (map b G)) -> nuF c (map ovl G);
    }.

    Section WithHyps.
      Context (H : Hyps).

      Lemma lp_inj s s' : In s secs -> In s' secs -> lp s = lp s' -> s = s'.
      Proof.
        intros Hs Hs' E. unfold lp in E.
        rewrite <- (hyp_acq_owner H s Hs), <- (hyp_acq_owner H s' Hs').
        f_equal. eapply (ss_key_inj pos W).
        - exact (hyp_W_sorted H).
        - apply (hyp_W_acq H); exact Hs.
        - apply (hyp_W_acq H); exact Hs'.
        - exact E.
      Qed.

      Lemma lp_po s s' : In s secs -> In s' secs -> po s s' -> lp s < lp s'.
      Proof.
        intros Hs Hs' Hpo. unfold lp.
        apply (hyp_rfence H); [exact Hs | apply (hyp_W_acq H); exact Hs' |].
        rewrite (hyp_acq_owner H s' Hs'). exact Hpo.
      Qed.

      Lemma lp_rt s s' : In s secs -> In s' secs -> rt s s' -> lp s < lp s'.
      Proof.
        intros Hs Hs' Hrt. unfold lp.
        apply (hyp_rt H); [apply (hyp_W_acq H); exact Hs | apply (hyp_W_acq H); exact Hs' |].
        rewrite (hyp_acq_owner H s Hs), (hyp_acq_owner H s' Hs'). exact Hrt.
      Qed.

      (** Calls of an earlier critical section of a component precede all
          calls of a later one. *)
      Lemma sections_grouped u u' :
        In u W -> In u' W -> comp (owner u) = comp (owner u') ->
        lp (owner u) < lp (owner u') -> pos u < pos u'.
      Proof.
        intros Hu Hu' Hc Hlt.
        pose proof (hyp_in H u Hu) as [Hu1 Hu2].
        pose proof (hyp_in H u' Hu') as [Hu1' Hu2'].
        assert (Hne : owner u <> owner u') by (intro E; rewrite E in Hlt; lia).
        pose proof (hyp_in H (acq (owner u'))
                      (hyp_W_acq H _ (hyp_W_owner H _ Hu'))) as [_ Ha'].
        rewrite (hyp_acq_owner H _ (hyp_W_owner H _ Hu')) in Ha'.
        destruct (hyp_mutex H (owner u) (owner u')
                    (hyp_W_owner H _ Hu) (hyp_W_owner H _ Hu') Hne Hc) as [Hm|Hm];
          unfold lp in Hlt; lia.
      Qed.

      (** The overlay witness: all complete overlay operations ordered by
          the witness position of their [acq] call.  It respects the
          per-thread overlay order (with no overlay semi-independence) and
          the real-time order, and each component's projection belongs to
          that component's overlay specification. *)
      Theorem bracketed_composition :
        exists ow : list Sec,
          Permutation ow secs /\
          StronglySorted (fun s s' => lp s < lp s') ow /\
          (forall s s', In s secs -> In s' secs -> po s s' \/ rt s s' ->
             exists l1 l2, ow = l1 ++ s :: l2 /\ In s' l2) /\
          (forall c, nuF c (map ovl (filter (in_comp c) ow))).
      Proof.
        exists (isort lp secs).
        assert (Hperm : Permutation (isort lp secs) secs) by apply isort_perm.
        assert (Hsort : StronglySorted (fun s s' => lp s < lp s') (isort lp secs)).
        { apply isort_sorted; [intros; apply lp_inj; assumption | exact (hyp_secs_nodup H)]. }
        set (ow := isort lp secs) in *.
        assert (Hnd : NoDup ow)
          by exact (Permutation_NoDup (Permutation_sym Hperm) (hyp_secs_nodup H)).
        split; [exact Hperm|]. split; [exact Hsort|]. split.
        - intros s s' Hs Hs' Hord.
          assert (Hlt : lp s < lp s')
            by (destruct Hord; [apply lp_po | apply lp_rt]; assumption).
          assert (Hin : In s ow)
            by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hs).
          assert (Hin' : In s' ow)
            by (apply (Permutation_in _ (Permutation_sym Hperm)); exact Hs').
          destruct (in_split _ _ Hin) as (l1 & l2 & E).
          exists l1, l2. split; [exact E|].
          rewrite E in Hin'. apply in_app_or in Hin' as [H1|[<-|H2]].
          + exfalso. rewrite E in Hsort.
            pose proof (ss_app_cons _ _ _ _ _ Hsort H1) as Hc. cbn in Hc. lia.
          + lia.
          + exact H2.
        - intros c.
          set (G := filter (in_comp c) ow).
          assert (Hgroup : filter (uop_in_comp c) W = concat (map body G)).
          { rewrite (group_concat pos owner sec_dec lp G (filter (uop_in_comp c) W)).
            - apply f_equal. apply map_ext_in. intros s Hs. unfold body.
              apply filter_filter_sub. intros u Hu.
              unfold in_grp, owned_by, uop_in_comp in *.
              destruct (sec_dec (owner u) s) as [E|]; [|discriminate].
              rewrite E. unfold G in Hs. apply filter_In in Hs as [_ Hs]. exact Hs.
            - apply ss_filter; exact (hyp_W_sorted H).
            - apply NoDup_filter; exact Hnd.
            - apply ss_filter; exact Hsort.
            - intros u Hu. apply filter_In in Hu as [Hu Hc].
              unfold G. apply filter_In. split; [|exact Hc].
              apply (Permutation_in _ (Permutation_sym Hperm)).
              apply (hyp_W_owner H); exact Hu.
            - intros u u' Hu Hu' Hlt.
              apply filter_In in Hu as [Hu Hc]. apply filter_In in Hu' as [Hu' Hc'].
              apply sections_grouped; try assumption.
              unfold uop_in_comp, in_comp in *.
              destruct (comp_dec (comp (owner u)) c), (comp_dec (comp (owner u')) c);
                try discriminate. congruence. }
          apply ((hyp_local H) c G body).
          + apply NoDup_filter; exact Hnd.
          + intros s Hs. unfold G in Hs. apply filter_In in Hs as [Hs Hc].
            assert (Hs0 : In s secs) by (apply (Permutation_in _ Hperm); exact Hs).
            split.
            * unfold in_comp in Hc. destruct (comp_dec (comp s) c); [assumption|discriminate].
            * apply (hyp_body_ok H); exact Hs0.
          + rewrite <- Hgroup. apply (hyp_nuE H).
      Qed.

    End WithHyps.
  End Composition.

  (** ** Part 3: two lock-protected registers, SB and IRIW *)

  Inductive Loc := LX | LY.

  Definition loc_dec (a b : Loc) : {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  (** Overlay register events: [Put v] and [Get v] (a read returning [v]). *)
  Inductive RegOp := Put (v : nat) | Get (v : nat).

  (** Sequential specification of a register. *)
  Fixpoint reg_ok (cur : nat) (l : list RegOp) : Prop :=
    match l with
    | [] => True
    | Put v :: l' => reg_ok v l'
    | Get v :: l' => v = cur /\ reg_ok cur l'
    end.

  Lemma reg_const v l :
    (forall v', In (Put v') l -> v' = v) -> reg_ok v l ->
    forall w, In (Get w) l -> w = v.
  Proof.
    induction l as [|x l IH]; cbn; intros Hp Hr w Hw; [contradiction|].
    destruct x as [u|u]; destruct Hw as [Hw|Hw]; try discriminate.
    - assert (u = v) by (apply Hp; left; reflexivity). subst u.
      apply IH; [intros v' Hv'; apply Hp; right; exact Hv' | exact Hr | exact Hw].
    - injection Hw as ->. destruct Hr as [-> _]. reflexivity.
    - destruct Hr as [_ Hr].
      apply IH; [intros v' Hv'; apply Hp; right; exact Hv' | exact Hr | exact Hw].
  Qed.

  Lemma reg_get_after_put v l1 l2 cur w :
    (forall v', In (Put v') (l1 ++ Get w :: l2) -> v' = v) ->
    In (Put v) l1 -> reg_ok cur (l1 ++ Get w :: l2) -> w = v.
  Proof.
    revert cur. induction l1 as [|x l1 IH]; cbn; intros cur Hp Hin Hr; [contradiction|].
    destruct x as [u|u].
    - assert (u = v) by (apply Hp; left; reflexivity). subst u.
      destruct Hin as [_|Hin].
      + apply (reg_const v (l1 ++ Get w :: l2));
          [intros v' Hv'; apply Hp; right; exact Hv' | exact Hr |].
        apply in_or_app. right; left; reflexivity.
      + apply (IH v); [intros v' Hv'; apply Hp; right; exact Hv' | exact Hin | exact Hr].
    - destruct Hin as [Hin|Hin]; [discriminate|]. destruct Hr as [_ Hr].
      apply (IH cur); [intros v' Hv'; apply Hp; right; exact Hv' | exact Hin | exact Hr].
  Qed.

  Lemma reg_get_before_put l1 l2 w :
    (forall v', ~ In (Put v') l1) -> reg_ok 0 (l1 ++ Get w :: l2) -> w = 0.
  Proof.
    induction l1 as [|x l1 IH]; cbn; intros Hp Hr.
    - destruct Hr as [-> _]; reflexivity.
    - destruct x as [u|u]; [exfalso; apply (Hp u); left; reflexivity|].
      destruct Hr as [_ Hr].
      apply IH; [intros v' Hv'; apply (Hp v'); right; exact Hv' | exact Hr].
  Qed.

  Section RegOrder.
    Context {S : Type} (key : S -> nat) (ovl : S -> RegOp).

    (** In a key-sorted register history in which every write writes
        [v], a read of [w <> v] precedes every write. *)
    Lemma read_old_before_write ox a g v w :
      StronglySorted (fun s s' => key s < key s') ox ->
      (forall s v', In s ox -> ovl s = Put v' -> v' = v) ->
      reg_ok 0 (map ovl ox) ->
      In a ox -> In g ox -> ovl a = Put v -> ovl g = Get w -> w <> v ->
      key g < key a.
    Proof.
      intros Hs Hputs Hr Ha Hg Hoa Hog Hwv.
      destruct (Nat.lt_trichotomy (key a) (key g)) as [Hlt|[Heq|Hgt]]; [exfalso|exfalso|exact Hgt].
      - destruct (split_before key ox a g Hs Ha Hg Hlt) as (l1 & l2 & E & Hin1).
        assert (Hmap : map ovl ox = map ovl l1 ++ Get w :: map ovl l2)
          by (rewrite E, map_app; cbn; rewrite Hog; reflexivity).
        apply Hwv. rewrite Hmap in Hr.
        eapply reg_get_after_put; [| |exact Hr].
        + intros v' Hv'. rewrite <- Hmap in Hv'.
          apply in_map_iff in Hv' as (s & Hs1 & Hs2). exact (Hputs s v' Hs2 Hs1).
        + apply in_map_iff. exists a. split; [exact Hoa | exact Hin1].
      - pose proof (ss_key_inj key ox a g Hs Ha Hg Heq) as ->. congruence.
    Qed.

    (** If [a] is the only write, a read of [w <> 0] follows it. *)
    Lemma read_new_after_write ox a g v w :
      StronglySorted (fun s s' => key s < key s') ox ->
      (forall s v', In s ox -> ovl s = Put v' -> s = a) ->
      reg_ok 0 (map ovl ox) ->
      In a ox -> In g ox -> ovl a = Put v -> ovl g = Get w -> w <> 0 ->
      key a < key g.
    Proof.
      intros Hs Hwr Hr Ha Hg Hoa Hog Hw0.
      destruct (Nat.lt_trichotomy (key a) (key g)) as [Hlt|[Heq|Hgt]]; [exact Hlt|exfalso|exfalso].
      - pose proof (ss_key_inj key ox a g Hs Ha Hg Heq) as ->. congruence.
      - destruct (in_split _ _ Hg) as (l1 & l2 & E).
        assert (Hmap : map ovl ox = map ovl l1 ++ Get w :: map ovl l2)
          by (rewrite E, map_app; cbn; rewrite Hog; reflexivity).
        apply Hw0. rewrite Hmap in Hr. eapply reg_get_before_put; [|exact Hr].
        intros v' Hv'. apply in_map_iff in Hv' as (s & Hs1 & Hs2).
        assert (Hso : In s ox) by (rewrite E; apply in_or_app; left; exact Hs2).
        pose proof (Hwr s v' Hso Hs1) as ->.
        rewrite E in Hs. pose proof (ss_app_cons _ _ _ _ _ Hs Hs2) as Hc. cbn in Hc. lia.
    Qed.
  End RegOrder.

  (** Each overlay operation issues three underlay calls. *)
  Inductive Kind := KAcq | KData | KRel.

  Section RegComponent.
    Context {S : Type} (ovl : S -> RegOp).

    Definition is_data (u : S * Kind) : bool :=
      match snd u with KData => true | _ => false end.

    (** The data cell of a component is a register; its data calls carry
        the same register event as the overlay operation that issued
        them ([put(v) = acq; wrt(v); rel], [get() = acq; r <- rd; rel; ret r]). *)
    Definition reg_nuE (w : list (S * Kind)) : Prop :=
      reg_ok 0 (map (fun u => ovl (fst u)) (filter is_data w)).

    Definition reg_body_ok (s : S) (b : list (S * Kind)) : Prop :=
      filter is_data b = [(s, KData)].

    (** The local obligation of a lock-protected register: when the
        critical sections run one after the other, the overlay history
        is a register history. *)
    Lemma reg_local (G : list S) (b : S -> list (S * Kind)) :
      (forall s, In s G -> reg_body_ok s (b s)) ->
      reg_nuE (concat (map b G)) -> reg_ok 0 (map ovl G).
    Proof.
      intros Hb Hr. unfold reg_nuE in Hr.
      assert (E : filter is_data (concat (map b G)) = map (fun s => (s, KData)) G).
      { clear Hr. induction G as [|s G IH]; cbn; [reflexivity|].
        rewrite filter_app. pose proof (Hb s (or_introl eq_refl)) as Hs.
        unfold reg_body_ok in Hs. rewrite Hs. cbn. f_equal.
        apply IH. intros s' Hs'. apply Hb. right; exact Hs'. }
      rewrite E, map_map in Hr. exact Hr.
    Qed.

    Context (sec_dec : forall s s' : S, {s = s'} + {s <> s'}).

    Lemma reg_body_of_witness (W : list (S * Kind)) (pos : S * Kind -> nat) s :
      StronglySorted (fun u v => pos u < pos v) W -> In (s, KData) W ->
      reg_body_ok s (filter (fun u => if sec_dec (fst u) s then true else false) W).
    Proof.
      intros Hs Hin. unfold reg_body_ok. rewrite filter_filter_and.
      apply filter_single; [exact (ss_nodup pos W Hs) | exact Hin |].
      intros [s' k] _. cbn.
      destruct (sec_dec s' s) as [->|Hne]; destruct k; cbn;
        split; intros Hy; first [reflexivity | congruence].
    Qed.
  End RegComponent.

  (** *** Store buffering

      [T1: x.put(1); r1 <- y.get()]  and  [T2: y.put(1); r2 <- x.get()],
      each method being [acq; data; rel] on the lock of its register.
      The outcome [r1 = r2 = 0] is impossible. *)
  Module SB.
    Inductive Sec := S1 | S2 | S3 | S4.

    Definition sec_dec (a b : Sec) : {a = b} + {a <> b}.
    Proof. decide equality. Defined.

    Definition comp (s : Sec) : Loc :=
      match s with S1 | S4 => LX | S2 | S3 => LY end.
    Definition ovl (s : Sec) : RegOp :=
      match s with S1 | S3 => Put 1 | S2 | S4 => Get 0 end.
    Definition po (s s' : Sec) : Prop :=
      (s = S1 /\ s' = S2) \/ (s = S3 /\ s' = S4).
    Definition secs : list Sec := [S1; S2; S3; S4].
    Definition acq (s : Sec) : Sec * Kind := (s, KAcq).
    Definition rel (s : Sec) : Sec * Kind := (s, KRel).

    Theorem sb_forbidden (W : list (Sec * Kind)) (pos : Sec * Kind -> nat) :
      (* the underlay witness is a sequential trace containing every call *)
      StronglySorted (fun u v => pos u < pos v) W ->
      (forall s k, In (s, k) W) ->
      (* acq has mode RFence: later calls of the same thread come after it *)
      (forall s u, In u W -> po s (fst u) -> pos (acq s) < pos u) ->
      (* each body is bracketed by its acq and rel *)
      (forall u, In u W -> pos (acq (fst u)) <= pos u <= pos (rel (fst u))) ->
      (* lock specification: critical sections of one lock do not overlap *)
      (forall s s', s <> s' -> comp s = comp s' ->
         pos (rel s) < pos (acq s') \/ pos (rel s') < pos (acq s)) ->
      (* register specification, per location *)
      (forall c, reg_nuE ovl (filter (fun u => if loc_dec (comp (fst u)) c then true else false) W)) ->
      False.
    Proof.
      intros Hsort Hall Hrf Hin Hmx Hcell.
      assert (Hsecs : forall s, In s secs) by (intros []; cbn; tauto).
      assert (Hnd : NoDup secs).
      { repeat constructor; cbn; intuition discriminate. }
      assert (HH : Hyps sec_dec loc_dec comp fst acq rel ovl pos secs W
                     po (fun _ _ => False) (fun _ => reg_nuE ovl) (fun _ => reg_ok 0)
                     reg_body_ok).
      { constructor.
        - intros s _; reflexivity.
        - exact Hnd.
        - exact Hsort.
        - intros u _; apply Hsecs.
        - intros s _; apply Hall.
        - intros s u _ Hu Hpo; apply Hrf; assumption.
        - intros u u' _ _ [].
        - exact Hin.
        - intros s s' _ _ Hne Hc; apply Hmx; assumption.
        - exact Hcell.
        - intros s _. apply (reg_body_of_witness sec_dec W pos s Hsort (Hall s KData)).
        - intros c G b _ Hb Hr. apply (reg_local ovl G b); [|exact Hr].
          intros s Hs'. apply (proj2 (Hb s Hs')). }
      destruct (bracketed_composition sec_dec loc_dec comp fst acq rel ovl pos secs W
                  po (fun _ _ => False) (fun _ => reg_nuE ovl) (fun _ => reg_ok 0)
                  reg_body_ok HH)
        as (ow & Hperm & Hs & _ & Hspec).
      assert (Hinow : forall s, In s ow)
        by (intros s; apply (Permutation_in _ (Permutation_sym Hperm)), Hsecs).
      set (key := lp acq pos).
      (* location x: the read of 0 (S4) precedes the write (S1) *)
      assert (HX : key S4 < key S1).
      { apply (read_old_before_write key ovl (filter (in_comp loc_dec comp LX) ow) S1 S4 1 0).
        - apply ss_filter; exact Hs.
        - intros [] v' _ Ho; cbn in Ho; congruence.
        - exact (Hspec LX).
        - apply filter_In; split; [apply Hinow | reflexivity].
        - apply filter_In; split; [apply Hinow | reflexivity].
        - reflexivity.
        - reflexivity.
        - discriminate. }
      (* location y: the read of 0 (S2) precedes the write (S3) *)
      assert (HY : key S2 < key S3).
      { apply (read_old_before_write key ovl (filter (in_comp loc_dec comp LY) ow) S3 S2 1 0).
        - apply ss_filter; exact Hs.
        - intros [] v' _ Ho; cbn in Ho; congruence.
        - exact (Hspec LY).
        - apply filter_In; split; [apply Hinow | reflexivity].
        - apply filter_In; split; [apply Hinow | reflexivity].
        - reflexivity.
        - reflexivity.
        - discriminate. }
      (* program order, through the acquires *)
      pose proof (Hrf S1 (acq S2) (Hall S2 KAcq) (or_introl (conj eq_refl eq_refl))) as P1.
      pose proof (Hrf S3 (acq S4) (Hall S4 KAcq) (or_intror (conj eq_refl eq_refl))) as P2.
      unfold key, lp in HX, HY. lia.
    Qed.
    (** Sanity check that the hypotheses of [sb_forbidden] are not
        contradictory by themselves: with the outcome changed to
        [r1 = 0, r2 = 1] they are met by the sequential run
        [T1; T2]. *)
    Definition ovl_seq (s : Sec) : RegOp :=
      match s with S1 | S3 => Put 1 | S2 => Get 0 | S4 => Get 1 end.

    Definition W_seq : list (Sec * Kind) :=
      [(S1, KAcq); (S1, KData); (S1, KRel); (S2, KAcq); (S2, KData); (S2, KRel);
       (S3, KAcq); (S3, KData); (S3, KRel); (S4, KAcq); (S4, KData); (S4, KRel)].

    Definition pos_seq (u : Sec * Kind) : nat :=
      let '(s, k) := u in
      3 * (match s with S1 => 0 | S2 => 1 | S3 => 2 | S4 => 3 end) +
      (match k with KAcq => 0 | KData => 1 | KRel => 2 end).

    Lemma sb_hypotheses_satisfiable :
      StronglySorted (fun u v => pos_seq u < pos_seq v) W_seq /\
      (forall s k, In (s, k) W_seq) /\
      (forall s u, In u W_seq -> po s (fst u) -> pos_seq (acq s) < pos_seq u) /\
      (forall u, In u W_seq -> pos_seq (acq (fst u)) <= pos_seq u <= pos_seq (rel (fst u))) /\
      (forall s s', s <> s' -> comp s = comp s' ->
         pos_seq (rel s) < pos_seq (acq s') \/ pos_seq (rel s') < pos_seq (acq s)) /\
      (forall c, reg_nuE ovl_seq
                   (filter (fun u => if loc_dec (comp (fst u)) c then true else false) W_seq)).
    Proof.
      split; [|split; [|split; [|split; [|split]]]].
      - apply Sorted_StronglySorted.
        + intros x y z H1 H2; cbn in *; lia.
        + unfold W_seq.
          repeat first [ apply Sorted_nil | apply Sorted_cons | apply HdRel_nil
                       | apply HdRel_cons | (cbn; lia) ].
      - intros [] []; cbn; tauto.
      - intros s [s' k] _ Hpo. cbn in Hpo.
        destruct Hpo as [[-> ->]|[-> ->]]; destruct k; cbn; lia.
      - intros [[] []] _; cbn; lia.
      - intros [] [] Hne Hc; cbn in *; try congruence; lia.
      - intros []; cbn; intuition.
    Qed.
  End SB.

  (** *** IRIW

      [T1: x.put(1)], [T2: y.put(1)], [T3: a <- x.get(); b <- y.get()],
      [T4: c <- y.get(); d <- x.get()].  The outcome [a = 1, b = 0,
      c = 1, d = 0] is impossible. *)
  Module IRIW.
    Inductive Sec := A | B | C | D | E | F.

    Definition sec_dec (a b : Sec) : {a = b} + {a <> b}.
    Proof. decide equality. Defined.

    Definition comp (s : Sec) : Loc :=
      match s with A | C | F => LX | B | D | E => LY end.
    Definition ovl (s : Sec) : RegOp :=
      match s with
      | A | B => Put 1
      | C | E => Get 1
      | D | F => Get 0
      end.
    Definition po (s s' : Sec) : Prop :=
      (s = C /\ s' = D) \/ (s = E /\ s' = F).
    Definition secs : list Sec := [A; B; C; D; E; F].
    Definition acq (s : Sec) : Sec * Kind := (s, KAcq).
    Definition rel (s : Sec) : Sec * Kind := (s, KRel).

    Theorem iriw_forbidden (W : list (Sec * Kind)) (pos : Sec * Kind -> nat) :
      StronglySorted (fun u v => pos u < pos v) W ->
      (forall s k, In (s, k) W) ->
      (forall s u, In u W -> po s (fst u) -> pos (acq s) < pos u) ->
      (forall u, In u W -> pos (acq (fst u)) <= pos u <= pos (rel (fst u))) ->
      (forall s s', s <> s' -> comp s = comp s' ->
         pos (rel s) < pos (acq s') \/ pos (rel s') < pos (acq s)) ->
      (forall c, reg_nuE ovl (filter (fun u => if loc_dec (comp (fst u)) c then true else false) W)) ->
      False.
    Proof.
      intros Hsort Hall Hrf Hin Hmx Hcell.
      assert (Hsecs : forall s, In s secs) by (intros []; cbn; tauto).
      assert (Hnd : NoDup secs).
      { repeat constructor; cbn; intuition discriminate. }
      assert (HH : Hyps sec_dec loc_dec comp fst acq rel ovl pos secs W
                     po (fun _ _ => False) (fun _ => reg_nuE ovl) (fun _ => reg_ok 0)
                     reg_body_ok).
      { constructor.
        - intros s _; reflexivity.
        - exact Hnd.
        - exact Hsort.
        - intros u _; apply Hsecs.
        - intros s _; apply Hall.
        - intros s u _ Hu Hpo; apply Hrf; assumption.
        - intros u u' _ _ [].
        - exact Hin.
        - intros s s' _ _ Hne Hc; apply Hmx; assumption.
        - exact Hcell.
        - intros s _. apply (reg_body_of_witness sec_dec W pos s Hsort (Hall s KData)).
        - intros c G b _ Hb Hr. apply (reg_local ovl G b); [|exact Hr].
          intros s Hs'. apply (proj2 (Hb s Hs')). }
      destruct (bracketed_composition sec_dec loc_dec comp fst acq rel ovl pos secs W
                  po (fun _ _ => False) (fun _ => reg_nuE ovl) (fun _ => reg_ok 0)
                  reg_body_ok HH)
        as (ow & Hperm & Hs & _ & Hspec).
      assert (Hinow : forall s, In s ow)
        by (intros s; apply (Permutation_in _ (Permutation_sym Hperm)), Hsecs).
      set (key := lp acq pos).
      set (ox := filter (in_comp loc_dec comp LX) ow).
      set (oy := filter (in_comp loc_dec comp LY) ow).
      assert (Hox : StronglySorted (fun s s' => key s < key s') ox) by (apply ss_filter; exact Hs).
      assert (Hoy : StronglySorted (fun s s' => key s < key s') oy) by (apply ss_filter; exact Hs).
      assert (Hinx : forall s, comp s = LX -> In s ox).
      { intros s Hc. apply filter_In. split; [apply Hinow|].
        unfold in_comp. rewrite Hc. reflexivity. }
      assert (Hiny : forall s, comp s = LY -> In s oy).
      { intros s Hc. apply filter_In. split; [apply Hinow|].
        unfold in_comp. rewrite Hc. reflexivity. }
      assert (Hwx : forall s v', In s ox -> ovl s = Put v' -> s = A).
      { intros s v' Hs' Ho. apply filter_In in Hs' as [_ Hc].
        destruct s; cbn in Ho, Hc; first [reflexivity | discriminate]. }
      assert (Hwy : forall s v', In s oy -> ovl s = Put v' -> s = B).
      { intros s v' Hs' Ho. apply filter_In in Hs' as [_ Hc].
        destruct s; cbn in Ho, Hc; first [reflexivity | discriminate]. }
      assert (H1 : key F < key A).
      { apply (read_old_before_write key ovl ox A F 1 0 Hox);
          [intros s v' Hs' Ho; rewrite (Hwx s v' Hs' Ho) in Ho; cbn in Ho; congruence
          | exact (Hspec LX) | apply Hinx; reflexivity | apply Hinx; reflexivity
          | reflexivity | reflexivity | discriminate]. }
      assert (H2 : key A < key C).
      { apply (read_new_after_write key ovl ox A C 1 1 Hox Hwx (Hspec LX));
          [apply Hinx; reflexivity | apply Hinx; reflexivity
          | reflexivity | reflexivity | discriminate]. }
      assert (H3 : key D < key B).
      { apply (read_old_before_write key ovl oy B D 1 0 Hoy);
          [intros s v' Hs' Ho; rewrite (Hwy s v' Hs' Ho) in Ho; cbn in Ho; congruence
          | exact (Hspec LY) | apply Hiny; reflexivity | apply Hiny; reflexivity
          | reflexivity | reflexivity | discriminate]. }
      assert (H4 : key B < key E).
      { apply (read_new_after_write key ovl oy B E 1 1 Hoy Hwy (Hspec LY));
          [apply Hiny; reflexivity | apply Hiny; reflexivity
          | reflexivity | reflexivity | discriminate]. }
      pose proof (Hrf C (acq D) (Hall D KAcq) (or_introl (conj eq_refl eq_refl))) as P1.
      pose proof (Hrf E (acq F) (Hall F KAcq) (or_intror (conj eq_refl eq_refl))) as P2.
      unfold key, lp in H1, H2, H3, H4. lia.
    Qed.
  End IRIW.

End BracketedComposition.
