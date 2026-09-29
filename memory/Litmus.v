(** * Litmus witnesses for the comparison (Section L.7)

    The containments of [RC11.v] and [ARM.v] are strict, and the reverse
    containments fail; the paper establishes the incomparabilities by
    explicit witnesses.  This file checks the four decisive ones:

      LB   (all rlx)             ours allow   RC11 forbid   Δ5
      ISA2 + rel + acq           ours forbid  RC11 allow    Δ4
      SB + rel + acq             ours allow   ARM  forbid   Δ1
      RSW + rel                  ours forbid  ARM  allow    Δ2

    "Ours allow" means: for the program-level choice [pre = pre_0] there is
    a well-formed witness satisfying (D1) and (D2).  "Ours forbid" means:
    no well-formed witness satisfies (D1) and (D2) for any admissible
    [pre].  The reference-model verdicts quantify over all well-formed
    witnesses (forbid) or exhibit one (allow).

    Candidates are lists of blocks with program order given by handles
    within a thread; witnesses are given by lists of pairs.  Acyclicity is
    shown by potentials, RC11's COHERENCE by the normal form of [eco]. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.PArith.PArith.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.Logic.Classical.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Consequences.
Require Import memory.RC11.
Require Import memory.ARM.
Require Import Coq.Sorting.Permutation.
Require Import memory.Equivalence.
Require Import memory.Tensor.

Import ListNotations.

Module Litmus.

  Import Cell Cell.Instances Decl Consequences.

  (** ** Locations *)

  Inductive Loc4 : Type := lx | ly | lz | lw.

  Definition Loc4_dec : forall a b : Loc4, {a = b} + {a <> b}.
  Proof. decide equality. Defined.

  Notation C := (RC_cfg Loc4_dec).
  Notation block := (block C).
  Notation I := (mode_indep (C := C)).
  Notation pre0_iff := (pre0_iff Loc4 Loc4_dec).

  (** ** Candidates from lists, witnesses from pair lists *)

  (** Program order: same thread, increasing handle. *)
  Definition po_of (l : list block) : relation block :=
    fun a b => In a l /\ In b l /\ b_tid a = b_tid b /\ b_handle a < b_handle b.

  Definition cand_of (l : list block) : cand C := {| ops := l; po := po_of l |}.

  Lemma wf_cand_of (l : list block) :
    (forall b, In b l -> ~ is_flush b) ->
    NoDup l ->
    (forall a b, In a l -> In b l -> b_tid a = b_tid b -> a <> b -> b_handle a <> b_handle b) ->
    wf_cand (cand_of l).
  Proof.
    intros Hnf Hnd Hh. constructor; cbn.
    - exact Hnf.
    - exact Hnd.
    - intros a b (Ha & Hb & Ht & _). auto.
    - intros a (_ & _ & _ & H). lia.
    - intros a b c (Ha & Hb & Ht1 & H1) (_ & Hc & Ht2 & H2). repeat split; auto; [congruence | lia].
    - intros a b Ha Hb Ht Hne.
      destruct (lt_dec (b_handle a) (b_handle b)) as [Hlt | Hge].
      + left. repeat split; auto.
      + right. repeat split; auto. specialize (Hh a b Ha Hb Ht Hne). lia.
    - intros a b (_ & _ & _ & H) _ _. exact H.
  Qed.

  (** The program-level choice [pre_0] is admissible. *)
  Lemma admissible_pre0 (X : cand C) (HX : wf_cand X) : admissible X I (pre0 X I).
  Proof.
    split; [| split].
    - intros a b H. exact H.
    - eapply acyclic_incl with (S := po X).
      + intros a b [H _]. exact H.
      + assert (Htc : forall a b, (po X)⁺ a b -> po X a b).
        { intros a b H. induction H as [a b H | a b c H1 IH1 H2 IH2]; [exact H | eapply (po_trans HX); eauto]. }
        intros x Hx. apply (po_irrefl HX x). apply Htc. exact Hx.
    - intros a b [H _]. apply (po_dom HX) in H. tauto.
  Qed.

  Definition rel_of (l : list (block * block)) : relation block := fun a b => In (a, b) l.

  Definition witness_of (mo_l rf_l : list (block * block)) : witness C :=
    {| mo := rel_of mo_l; rf := rel_of rf_l |}.

  (** A read with a nonzero value has a value-matching source. *)
  Lemma read_source (X : cand C) (w : witness C) (Hw : wf_witness X w) (r : block) :
    In r (ops X) -> is_read r -> b_val r <> 0 ->
    exists u, rf w u r /\ In u (ops X) /\ is_write u /\ b_loc u = b_loc r /\ b_val u = b_val r.
  Proof.
    intros Hr Hrd Hv.
    destruct (classic (exists u, rf w u r)) as [(u & Hu) | Hno].
    - exists u. pose proof (rf_dom Hw _ _ Hu) as (Hin & _ & Hwu & _ & Hl & Hval). auto.
    - exfalso. apply Hv. apply (rf_init Hw r Hr Hrd). intros u Hu. apply Hno. eauto.
  Qed.

  (** Monotone and strict potentials along a transitive closure. *)
  Lemma tc_monotone (h : block -> nat) (R : relation block) :
    (forall x y, R x y -> h x <= h y) -> forall x y, R⁺ x y -> h x <= h y.
  Proof.
    intros H x y Hxy. induction Hxy as [x y Hxy | x y z _ IH1 _ IH2]; [auto | lia].
  Qed.

  Lemma tc_strict (f : block -> nat) (R : relation block) :
    (forall x y, R x y -> f x < f y) -> forall x y, R⁺ x y -> f x < f y.
  Proof.
    intros H x y Hxy. induction Hxy as [x y Hxy | x y z _ IH1 _ IH2]; [auto | lia].
  Qed.

  (** ** Tactics *)

  (** Case analysis on membership in a concrete list of blocks, and on
      membership of a pair in a concrete list of pairs. *)
  Ltac in_ops H := cbn in H; repeat (destruct H as [<- | H]); try contradiction.
  Ltac in_pairs H :=
    cbn in H; repeat (destruct H as [H | H]; [injection H; intros; subst |]); try contradiction.

  (** A program-order edge between two concrete blocks. *)
  Ltac po_edge := repeat split; cbn; intuition (auto; try lia).

  Ltac fin :=
    cbn in *;
    repeat match goal with
           | H : _ /\ _ |- _ => destruct H
           end;
    try discriminate; try contradiction; try congruence; try lia;
    try (intuition (auto; try discriminate; try lia)).

  (** ** LB: load buffering, all relaxed (Δ5)

        T1: rd(x) // 1; wrt(y, 1)        T2: rd(y) // 1; wrt(x, 1)  *)

  Module LB.
    Definition rx : block := @BR C 1%positive 1 lx rrlx 1.
    Definition wy : block := @BW C 1%positive 2 ly 1 wrlx.
    Definition ry : block := @BR C 2%positive 1 ly rrlx 1.
    Definition wx : block := @BW C 2%positive 2 lx 1 wrlx.

    Definition ops : list block := [rx; wy; ry; wx].
    Definition X : cand C := cand_of ops.

    Lemma wf : wf_cand X.
    Proof.
      apply wf_cand_of.
      - intros b H. in_ops H; fin.
      - repeat constructor; cbn; intuition discriminate.
      - intros a b Ha Hb. in_ops Ha; in_ops Hb; fin.
    Qed.

    (** The witness: each read reads the other thread's write. *)
    Definition w : witness C := witness_of [] [(wy, ry); (wx, rx)].

    Lemma wf_w : wf_witness X w.
    Proof.
      constructor.
      - intros a b H. in_pairs H.
      - intros a H. in_pairs H.
      - intros a b c H. in_pairs H.
      - intros a b Ha Hb Hwa Hwb Hl Hne. in_ops Ha; in_ops Hb; fin.
      - intros u r H. in_pairs H; fin.
      - intros u u' r H H'. in_pairs H; in_pairs H'; fin.
      - intros r Hr Hrd Hno. in_ops Hr; fin.
        + exfalso. apply (Hno wx). cbn. right. left. reflexivity.
        + exfalso. apply (Hno wy). cbn. left. reflexivity.
    Qed.

    (** No read-before edges: every read reads the last write at its
        location. *)
    Lemma no_rb r u : ~ rb X w r u.
    Proof.
      intros (Hr & Hu & Hrd & Hwu & Hl & Hsrc). in_ops Hr; in_ops Hu; fin.
      - specialize (Hsrc wx). cbn in Hsrc. apply Hsrc. auto.
      - specialize (Hsrc wy). cbn in Hsrc. apply Hsrc. auto.
    Qed.

    (** [pre_0 = ∅]: the only program-order pairs are relaxed read–write
        pairs across locations. *)
    Lemma pre0_empty a b : ~ pre0 X I a b.
    Proof.
      intros H. apply pre0_iff in H; [| exact wf].
      destruct H as [(Ha & Hb & Ht & Hh) Hshape]. in_ops Ha; in_ops Hb; fin.
    Qed.

    Definition pot (b : block) : nat := if is_writeb b then 0 else 1.

    Theorem ours_allow :
      exists w pre, wf_witness X w /\ admissible X I pre /\ consistent X I w pre.
    Proof.
      exists w, (pre0 X I). split; [exact wf_w |]. split; [apply admissible_pre0; exact wf |].
      split.
      - (* D1 *)
        apply (acyclic_by_nat_potential pot). intros x y [[[Hpo | Hrf] | Hmo] | Hrb].
        + destruct Hpo as [(Hx & Hy & Ht & Hh) Hl]. in_ops Hx; in_ops Hy; fin.
        + in_pairs Hrf; cbn; lia.
        + in_pairs Hmo.
        + exfalso. eapply no_rb; eauto.
      - (* D2 *)
        apply (acyclic_by_nat_potential pot). intros x y [[[Hppo | Hrfe] | Hmo] | Hrb].
        + exfalso. destruct Hppo as [[_ Hpre] | [Hpre _]].
          * induction Hpre as [a b H | a b c H1 IH1 H2 IH2]; [eapply pre0_empty; eauto | auto].
          * eapply pre0_empty; eauto.
        + destruct Hrfe as [Hrf _]. in_pairs Hrf; cbn; lia.
        + in_pairs Hmo.
        + exfalso. eapply no_rb; eauto.
    Qed.

    (** RC11 forbids it: [po ∪ rf] has the cycle
        [rx → wy → ry → wx → rx], whichever the witness. *)
    Theorem rc11_forbid : forall w, wf_witness X w -> ~ RC11.rc11_consistent Loc4 Loc4_dec X w.
    Proof.
      intros w Hw [_ Hnta].
      assert (Hrx : rf w wx rx).
      { destruct (read_source X w Hw rx) as (u & Hu & Hin & Hwu & Hl & Hv); cbn; auto.
        in_ops Hin; fin. }
      assert (Hry : rf w wy ry).
      { destruct (read_source X w Hw ry) as (u & Hu & Hin & Hwu & Hl & Hv); cbn; auto.
        in_ops Hin; fin. }
      apply (Hnta rx).
      eapply t_trans with (y := wy); [apply t_step; left; po_edge |].
      eapply t_trans with (y := ry); [apply t_step; right; exact Hry |].
      eapply t_trans with (y := wx); [apply t_step; left; po_edge |].
      apply t_step. right. exact Hrx.
    Qed.
  End LB.

  (** ** ISA2 with release/acquire (Δ4)

        T1: rd(w) // 1; wrt(x, 1, rel)
        T2: rd(x, acq) // 1; rd(y) // 0
        T3: wrt(y, 1); wrt(w, 1, rel)

      Every intra-thread edge comes from a clause all models have; we and
      ARM forbid the outcome, RC11 allows it because its COHERENCE tests
      one [hb] path followed by one [eco] path, and this cycle needs two
      alternations. *)

  Module ISA2.
    Definition rw : block := @BR C 1%positive 1 lw rrlx 1.
    Definition wx : block := @BW C 1%positive 2 lx 1 rel.
    Definition rx : block := @BR C 2%positive 1 lx acq 1.
    Definition ry : block := @BR C 2%positive 2 ly rrlx 0.
    Definition wy : block := @BW C 3%positive 1 ly 1 wrlx.
    Definition ww : block := @BW C 3%positive 2 lw 1 rel.

    Definition ops : list block := [rw; wx; rx; ry; wy; ww].
    Definition X : cand C := cand_of ops.

    Lemma wf : wf_cand X.
    Proof.
      apply wf_cand_of.
      - intros b H. in_ops H; fin.
      - repeat constructor; cbn; intuition discriminate.
      - intros a b Ha Hb. in_ops Ha; in_ops Hb; fin.
    Qed.

    (** ours forbid: for every witness and every admissible [pre], [Dc]
        cycles through [rw → wx → rx → ry → wy → ww → rw]. *)
    Theorem ours_forbid :
      forall w pre, wf_witness X w -> admissible X I pre -> ~ consistent X I w pre.
    Proof.
      intros w pre Hw Hadm [HD1 HD2].
      destruct Hadm as (Hpre0 & _ & _).
      assert (Hrw : rf w ww rw).
      { destruct (read_source X w Hw rw) as (u & Hu & Hin & Hwu & Hl & Hv); cbn; auto.
        in_ops Hin; fin. }
      assert (Hrx : rf w wx rx).
      { destruct (read_source X w Hw rx) as (u & Hu & Hin & Hwu & Hl & Hv); cbn; auto.
        in_ops Hin; fin. }
      assert (Hrb : rb X w ry wy).
      { split; [cbn; intuition auto |]. split; [cbn; intuition auto |].
        split; [exact Logic.I |]. split; [exact Logic.I |]. split; [reflexivity |].
        intros u0 Hu0. pose proof (rf_dom Hw _ _ Hu0) as (Hin & _ & Hwu & _ & Hl & Hv).
        in_ops Hin; fin. }
      apply (HD2 rw).
      eapply t_trans with (y := wx).
      { apply t_step. left. left. left. left. split; [exact Logic.I |].
        apply t_step. apply Hpre0. apply pre0_iff; [exact wf |]. split; [po_edge | right; right; exact Logic.I]. }
      eapply t_trans with (y := rx).
      { apply t_step. left. left. right. split; [exact Hrx | cbn; discriminate]. }
      eapply t_trans with (y := ry).
      { apply t_step. left. left. left. left. split; [exact Logic.I |].
        apply t_step. apply Hpre0. apply pre0_iff; [exact wf |]. split; [po_edge | right; left; exact Logic.I]. }
      eapply t_trans with (y := wy).
      { apply t_step. right. exact Hrb. }
      eapply t_trans with (y := ww).
      { apply t_step. left. left. left. right. split; [| split; exact Logic.I].
        apply pre0_iff; [exact wf |]. split; [po_edge | right; right; exact Logic.I]. }
      apply t_step. left. left. right. split; [exact Hrw | cbn; discriminate].
    Qed.

    (** RC11 allow: the witness reading as annotated. *)
    Definition w : witness C := witness_of [] [(ww, rw); (wx, rx)].

    Lemma wf_w : wf_witness X w.
    Proof.
      constructor.
      - intros a b H. in_pairs H.
      - intros a H. in_pairs H.
      - intros a b c H. in_pairs H.
      - intros a b Ha Hb Hwa Hwb Hl Hne. in_ops Ha; in_ops Hb; fin.
      - intros u r H. in_pairs H; fin.
      - intros u u' r H H'. in_pairs H; in_pairs H'; fin.
      - intros r Hr Hrd Hno. in_ops Hr; fin.
        + exfalso. apply (Hno ww). cbn. left. reflexivity.
        + exfalso. apply (Hno wx). cbn. right. left. reflexivity.
    Qed.

    (** The only read-before edge is [ry → wy]. *)
    Lemma rb_char r u : rb X w r u -> r = ry /\ u = wy.
    Proof.
      intros (Hr & Hu & Hrd & Hwu & Hl & Hsrc). in_ops Hr; in_ops Hu; cbn in Hrd, Hwu, Hl;
        try contradiction; try (discriminate Hl); try (split; reflexivity).
      - exfalso. apply (Hsrc ww). cbn. left. reflexivity.
      - exfalso. apply (Hsrc wx). cbn. right. left. reflexivity.
    Qed.

    (** The only synchronizes-with edge is [wx → rx]. *)
    Lemma sw_char a r : RC11.sw Loc4 Loc4_dec X w a r -> a = wx /\ r = rx.
    Proof.
      intros (Hrel & Hacq & u & (Hwa & Hwu & Hau) & Hrf).
      (* the pair [(ww, rw)] is excluded since [rw] is not an acquire *)
      in_pairs Hrf.
      destruct Hau as [-> | [(Ha & _ & Ht & Hh) Hl]]; [auto |]. in_ops Ha; fin.
    Qed.

    (** Potentials: [f] increases along [po ∪ sw ∪ rf]; [h] separates
        thread 3 from threads 1 and 2, which no [hb] edge connects. *)
    Definition f (b : block) : nat :=
      match b_tid b, b_handle b with
      | 1%positive, 1 => 2 | 1%positive, 2 => 3
      | 2%positive, 1 => 4 | 2%positive, 2 => 5
      | 3%positive, 1 => 0 | 3%positive, 2 => 1
      | _, _ => 0
      end.

    Definition h (b : block) : nat := match b_tid b with 3%positive => 1 | _ => 0 end.

    Lemma hb_gen_f x y : (po X ∪ RC11.sw Loc4 Loc4_dec X w) x y -> f x < f y.
    Proof.
      intros [(Hx & Hy & Ht & Hh) | Hsw].
      - in_ops Hx; in_ops Hy; fin.
      - apply sw_char in Hsw. destruct Hsw as [-> ->]. cbn. lia.
    Qed.

    Lemma hb_gen_h x y : (po X ∪ RC11.sw Loc4 Loc4_dec X w) x y -> h x <= h y.
    Proof.
      intros [(Hx & Hy & Ht & Hh) | Hsw].
      - unfold h. rewrite Ht. lia.
      - apply sw_char in Hsw. destruct Hsw as [-> ->]. cbn. lia.
    Qed.

    Theorem rc11_allow : exists w, wf_witness X w /\ RC11.rc11_consistent Loc4 Loc4_dec X w.
    Proof.
      exists w. split; [exact wf_w |]. split.
      - (* COHERENCE *)
        intros a b Hhb Hcase. unfold RC11.rchb in Hhb.
        assert (Hf : f a < f b) by (eapply tc_strict; [apply hb_gen_f | exact Hhb]).
        assert (Hh : h a <= h b) by (eapply tc_monotone; [apply hb_gen_h | exact Hhb]).
        destruct Hcase as [-> | Heco]; [lia |].
        apply (RC11.eco_normal_form Loc4 Loc4_dec X w wf_w) in Heco.
        destruct Heco as [Hmo | [Hrb | [Hrf | (u & [Hmo | Hrb] & Hrf)]]].
        + in_pairs Hmo.
        + apply rb_char in Hrb. destruct Hrb as [-> ->]. cbn in Hh. lia.
        + in_pairs Hrf; cbn in Hf; lia.
        + in_pairs Hmo.
        + apply rb_char in Hrb. destruct Hrb as [-> ->]. in_pairs Hrf; fin.
      - (* NO-THIN-AIR *)
        apply (acyclic_by_nat_potential f). intros x y [(Hx & Hy & Ht & Hh) | Hrf].
        + in_ops Hx; in_ops Hy; fin.
        + in_pairs Hrf; cbn; lia.
    Qed.
  End ISA2.

  (** ** The ARM witnesses

      Both programs have no dependencies: the dependency relations are
      empty. *)

  Definition nodep : relation block := fun _ _ => False.

  (** ** SB with release/acquire (Δ1)

        T1: wrt(x, 1, rel); rd(y, acq) // 0
        T2: wrt(y, 1, rel); rd(x, acq) // 0

      The needed edge is [W_rel → R_acq] across locations, which [pre_0]
      does not have: ours allow.  ARM has [[rel];po;[acq]] twice and [rbe]
      twice: forbid. *)

  Module SB.
    Definition wx : block := @BW C 1%positive 1 lx 1 rel.
    Definition ry : block := @BR C 1%positive 2 ly acq 0.
    Definition wy : block := @BW C 2%positive 1 ly 1 rel.
    Definition rx : block := @BR C 2%positive 2 lx acq 0.

    Definition ops : list block := [wx; ry; wy; rx].
    Definition X : cand C := cand_of ops.

    Lemma wf : wf_cand X.
    Proof.
      apply wf_cand_of.
      - intros b H. in_ops H; fin.
      - repeat constructor; cbn; intuition discriminate.
      - intros a b Ha Hb. in_ops Ha; in_ops Hb; fin.
    Qed.

    (** Both reads read the initial value. *)
    Definition w : witness C := witness_of [] [].

    Lemma wf_w : wf_witness X w.
    Proof.
      constructor.
      - intros a b H. in_pairs H.
      - intros a H. in_pairs H.
      - intros a b c H. in_pairs H.
      - intros a b Ha Hb Hwa Hwb Hl Hne. in_ops Ha; in_ops Hb; fin.
      - intros u r H. in_pairs H.
      - intros u u' r H H'. in_pairs H.
      - intros r Hr Hrd Hno. in_ops Hr; fin.
    Qed.

    Lemma rb_char r u : rb X w r u -> (r = ry /\ u = wy) \/ (r = rx /\ u = wx).
    Proof.
      intros (Hr & Hu & Hrd & Hwu & Hl & Hsrc). in_ops Hr; in_ops Hu; cbn in Hrd, Hwu, Hl;
        try contradiction; try (discriminate Hl); auto.
    Qed.

    Lemma pre0_empty a b : ~ pre0 X I a b.
    Proof.
      intros H. apply pre0_iff in H; [| exact wf].
      destruct H as [(Ha & Hb & Ht & Hh) Hshape]. in_ops Ha; in_ops Hb; fin.
    Qed.

    Definition pot (b : block) : nat := if is_writeb b then 1 else 0.

    Theorem ours_allow :
      exists w pre, wf_witness X w /\ admissible X I pre /\ consistent X I w pre.
    Proof.
      exists w, (pre0 X I). split; [exact wf_w |]. split; [apply admissible_pre0; exact wf |].
      split.
      - apply (acyclic_by_nat_potential pot). intros x y [[[Hpo | Hrf] | Hmo] | Hrb].
        + destruct Hpo as [(Hx & Hy & Ht & Hh) Hl]. in_ops Hx; in_ops Hy; fin.
        + in_pairs Hrf.
        + in_pairs Hmo.
        + apply rb_char in Hrb. destruct Hrb as [[-> ->] | [-> ->]]; cbn; lia.
      - apply (acyclic_by_nat_potential pot). intros x y [[[Hppo | Hrfe] | Hmo] | Hrb].
        + exfalso. destruct Hppo as [[_ Hpre] | [Hpre _]].
          * induction Hpre as [a b H | a b c H1 IH1 H2 IH2]; [eapply pre0_empty; eauto | auto].
          * eapply pre0_empty; eauto.
        + destruct Hrfe as [Hrf _]. in_pairs Hrf.
        + in_pairs Hmo.
        + apply rb_char in Hrb. destruct Hrb as [[-> ->] | [-> ->]]; cbn; lia.
    Qed.

    (** ARM forbids it: [ob] has the cycle [wx → ry → wy → rx → wx]. *)
    Theorem arm_forbid :
      forall w, wf_witness X w -> ~ ARM.arm_consistent Loc4 Loc4_dec X w nodep nodep nodep.
    Proof.
      intros w Hw [_ Hext].
      assert (Hrb : forall r u, In r ops -> In u ops -> is_read r -> is_write u -> b_loc r = b_loc u ->
                                rb X w r u).
      { intros r u Hr Hu Hrd Hwu Hl. repeat split; auto.
        intros u0 Hu0. pose proof (rf_dom Hw _ _ Hu0) as (Hin & _ & Hwu0 & _ & Hl0 & Hv).
        in_ops Hr; in_ops Hin; fin. }
      apply (Hext wx). apply t_step. unfold ARM.ob.
      eapply t_trans with (y := ry).
      { apply t_step. right. left. split; [exact Logic.I | split; [po_edge | exact Logic.I]]. }
      eapply t_trans with (y := wy).
      { apply t_step. left. left. left. right. split; [apply Hrb; cbn; auto | cbn; discriminate]. }
      eapply t_trans with (y := rx).
      { apply t_step. right. left. split; [exact Logic.I | split; [po_edge | exact Logic.I]]. }
      apply t_step. left. left. left. right. split; [apply Hrb; cbn; auto | cbn; discriminate].
    Qed.
  End SB.

  (** ** RSW with a release (Δ2)

        T1: rd(x) // 1; wrt(x, 2); rd(x, acq) // 2; rd(z) // 0
        T2: wrt(z, 1); wrt(x, 1, rel)

      Our [ppo] chains [rd(x) → wrt(x,2) → rd(x,acq) → rd(z)] through
      same-location program order and [[acq];po], and with [rb], [po;[rel]]
      and [rfe] the relation cycles: forbid.  In ARM, [rd(x,acq)] has no
      incoming [ob] edge: allow. *)

  Module RSW.
    Definition rx1 : block := @BR C 1%positive 1 lx rrlx 1.
    Definition wx2 : block := @BW C 1%positive 2 lx 2 wrlx.
    Definition rxa : block := @BR C 1%positive 3 lx acq 2.
    Definition rz : block := @BR C 1%positive 4 lz rrlx 0.
    Definition wz : block := @BW C 2%positive 1 lz 1 wrlx.
    Definition wx1 : block := @BW C 2%positive 2 lx 1 rel.

    Definition ops : list block := [rx1; wx2; rxa; rz; wz; wx1].
    Definition X : cand C := cand_of ops.

    Lemma wf : wf_cand X.
    Proof.
      apply wf_cand_of.
      - intros b H. in_ops H; fin.
      - repeat constructor; cbn; intuition discriminate.
      - intros a b Ha Hb. in_ops Ha; in_ops Hb; fin.
    Qed.

    Theorem ours_forbid :
      forall w pre, wf_witness X w -> admissible X I pre -> ~ consistent X I w pre.
    Proof.
      intros w pre Hw Hadm [HD1 HD2].
      destruct Hadm as (Hpre0 & _ & _).
      assert (Hrx1 : rf w wx1 rx1).
      { destruct (read_source X w Hw rx1) as (u & Hu & Hin & Hwu & Hl & Hv); cbn; auto.
        in_ops Hin; fin. }
      assert (Hrxa : rf w wx2 rxa).
      { destruct (read_source X w Hw rxa) as (u & Hu & Hin & Hwu & Hl & Hv); cbn; auto.
        in_ops Hin; fin. }
      assert (Hrb : rb X w rz wz).
      { split; [cbn; intuition auto |]. split; [cbn; intuition auto |].
        split; [exact Logic.I |]. split; [exact Logic.I |]. split; [reflexivity |].
        intros u0 Hu0. pose proof (rf_dom Hw _ _ Hu0) as (Hin & _ & Hwu & _ & Hl & Hv).
        in_ops Hin; fin. }
      assert (Hmot : mo w wx1 wx2 \/ mo w wx2 wx1).
      { apply (mo_total Hw); cbn; try (intuition auto); try exact Logic.I; try reflexivity; discriminate. }
      destruct Hmot as [Hmo | Hmo].
      - (* [mo] agrees with the values: the (D2) cycle of the paper *)
        apply (HD2 rx1).
        eapply t_trans with (y := rz).
        { apply t_step. left. left. left. left. split; [exact Logic.I |].
          eapply t_trans with (y := wx2).
          { apply t_step. apply Hpre0. apply pre0_iff; [exact wf |]. split; [po_edge | left; reflexivity]. }
          eapply t_trans with (y := rxa).
          { apply t_step. apply Hpre0. apply pre0_iff; [exact wf |]. split; [po_edge | left; reflexivity]. }
          apply t_step. apply Hpre0. apply pre0_iff; [exact wf |]. split; [po_edge | right; left; exact Logic.I]. }
        eapply t_trans with (y := wz).
        { apply t_step. right. exact Hrb. }
        eapply t_trans with (y := wx1).
        { apply t_step. left. left. left. right. split; [| split; exact Logic.I].
          apply pre0_iff; [exact wf |]. split; [po_edge | right; right; exact Logic.I]. }
        apply t_step. left. left. right. split; [exact Hrx1 | cbn; discriminate].
      - (* [mo] against the values: a (D1) cycle [wx2 → wx1 → rx1 → wx2] *)
        apply (HD1 wx2).
        eapply t_trans with (y := wx1).
        { apply t_step. left. right. exact Hmo. }
        eapply t_trans with (y := rx1).
        { apply t_step. left. left. right. exact Hrx1. }
        apply t_step. left. left. left. split; [po_edge | reflexivity].
    Qed.

    (** ARM allows it. *)
    Definition w : witness C := witness_of [(wx1, wx2)] [(wx1, rx1); (wx2, rxa)].

    Lemma wf_w : wf_witness X w.
    Proof.
      constructor.
      - intros a b H. in_pairs H; fin.
      - intros a H. in_pairs H; fin.
      - intros a b c H H'. in_pairs H; in_pairs H'; fin.
      - intros a b Ha Hb Hwa Hwb Hl Hne. in_ops Ha; in_ops Hb; fin.
      - intros u r H. in_pairs H; fin.
      - intros u u' r H H'. in_pairs H; in_pairs H'; fin.
      - intros r Hr Hrd Hno. in_ops Hr; fin.
        + exfalso. apply (Hno wx1). cbn. left. reflexivity.
        + exfalso. apply (Hno wx2). cbn. right. left. reflexivity.
    Qed.

    Ltac mo_contra Hsrc u :=
      let Hm := fresh in
      exfalso; assert (Hm := Hsrc u ltac:(cbn; intuition auto)); cbn in Hm;
      destruct Hm as [Hm | Hm]; [injection Hm; intros; discriminate | contradiction].

    Lemma rb_char r u : rb X w r u -> (r = rx1 /\ u = wx2) \/ (r = rz /\ u = wz).
    Proof.
      intros (Hr & Hu & Hrd & Hwu & Hl & Hsrc). in_ops Hr; in_ops Hu; cbn in Hrd, Hwu, Hl;
        try contradiction; try (discriminate Hl);
        try (left; split; reflexivity); try (right; split; reflexivity).
      - mo_contra Hsrc wx1.
      - mo_contra Hsrc wx2.
      - mo_contra Hsrc wx2.
    Qed.

    (** Potentials for INTERNAL and for EXTERNAL. *)
    Definition g (b : block) : nat :=
      match b_tid b, b_handle b with
      | 1%positive, 1 => 2 | 1%positive, 2 => 3 | 1%positive, 3 => 4 | 1%positive, 4 => 5
      | 2%positive, 1 => 100 | 2%positive, 2 => 1
      | _, _ => 0
      end.

    Definition p (b : block) : nat :=
      match b_tid b, b_handle b with
      | 1%positive, 1 => 4 | 1%positive, 2 => 4 | 1%positive, 3 => 0 | 1%positive, 4 => 1
      | 2%positive, 1 => 2 | 2%positive, 2 => 3
      | _, _ => 0
      end.

    Theorem arm_allow :
      exists w, wf_witness X w /\ ARM.arm_consistent Loc4 Loc4_dec X w nodep nodep nodep.
    Proof.
      exists w. split; [exact wf_w |]. split.
      - (* INTERNAL *)
        apply (acyclic_by_nat_potential g). intros x y [[[Hpo | Hrf] | Hrb] | Hmo].
        + destruct Hpo as [(Hx & Hy & Ht & Hh) Hl]. in_ops Hx; in_ops Hy; fin.
        + in_pairs Hrf; cbn; lia.
        + apply rb_char in Hrb. destruct Hrb as [[-> ->] | [-> ->]]; cbn; lia.
        + in_pairs Hmo; cbn; lia.
      - (* EXTERNAL *)
        apply acyclic_tc. apply (acyclic_by_nat_potential p). intros x y H.
        unfold ARM.obs, ARM.dob, ARM.bob, ARM.bob0, ARM.S in H.
        destruct H as [[[[Hrfe | Hrbe] | Hmoe] | Hdob] | [HS | [[Hacq | Hrel] | Hrelmoi]]].
        + destruct Hrfe as [Hrf Ht]. in_pairs Hrf; cbn in Ht; try (exfalso; apply Ht; reflexivity); cbn; lia.
        + destruct Hrbe as [Hrb Ht]. apply rb_char in Hrb.
          destruct Hrb as [[-> ->] | [-> ->]]; cbn in Ht; try (exfalso; apply Ht; reflexivity); cbn; lia.
        + destruct Hmoe as [Hmo Ht]. in_pairs Hmo; cbn; lia.
        + exfalso.
          destruct Hdob as [[[[[H | H] | [H _]] | (z & H & _)] | (z & [H | H] & _)] | (z & [H | H] & _)];
            exact H.
        + destruct HS as (Hrel & (Hx & Hy & Ht & Hh) & Hacq). in_ops Hx; in_ops Hy; fin.
        + destruct Hacq as [Hacq (Hx & Hy & Ht & Hh)]. in_ops Hx; in_ops Hy; fin.
        + destruct Hrel as [(Hx & Hy & Ht & Hh) Hrel]. in_ops Hx; in_ops Hy; fin.
        + destruct Hrelmoi as (z & [(Hx & Hz & Ht & Hh) Hrel] & [Hmo Ht']).
          in_pairs Hmo. cbn in Ht'. discriminate.
    Qed.
  End RSW.


  (** ** MP with release/acquire: the hidden tensor is not a product

        T1: wrt(y, 1); wrt(x, 1, rel)        T2: rd(x, acq) // 1; rd(y) // 0

      The outcome is forbidden by (D2): [wy → wx] (write--write in
      [po \ I], the later write is a release), [wx → rx] ([rfe]),
      [rx → ry] (an acquire read followed in program order by any read),
      [ry → wy] ([rb]: [ry] reads the initial value, [wy] is [mo]-later).
      By Thm. decl the trace [wy · wx · rx · ry], which presents the
      candidate and respects [pre_0], is therefore not in [ν_RC].  Its
      projections onto [{x}] and [{y}] are, however, in the hidden
      specifications of the single cells [ν_RC[{x}]] and [ν_RC[{y}]]:
      the hidden memory [ν_RC[{x,y}]] is strictly smaller than the
      specification tensor of Def. def:spec-tensor of the hidden cells.
      The composite memory is a tensor of its cells only with the flush
      contract of Def. mem:def:tensor ([Tensor.memory_tensor]), and the
      contract does not survive hiding: what it forbids here is that the
      acquire read [rx] of thread 2 reads the release write after the
      relaxed write [wy] has been published, while [ry] still reads the
      initial value. *)
  Module MP.
    Definition wy : block := @BW C 1%positive 1 ly 1 wrlx.
    Definition wx : block := @BW C 1%positive 2 lx 1 rel.
    Definition rx : block := @BR C 2%positive 1 lx acq 1.
    Definition ry : block := @BR C 2%positive 2 ly rrlx 0.

    Definition ops : list block := [wy; wx; rx; ry].
    Definition X : cand C := cand_of ops.

    Lemma wf : wf_cand X.
    Proof.
      apply wf_cand_of.
      - intros b H. in_ops H; fin.
      - repeat constructor; cbn; intuition discriminate.
      - intros a b Ha Hb. in_ops Ha; in_ops Hb; fin.
    Qed.

    (** ours forbid: [Dc] cycles through [wy → wx → rx → ry → wy]. *)
    Theorem ours_forbid :
      forall w pre, wf_witness X w -> admissible X I pre -> ~ consistent X I w pre.
    Proof.
      intros w pre Hw Hadm [HD1 HD2].
      destruct Hadm as (Hpre0 & _ & _).
      assert (Hrx : rf w wx rx).
      { destruct (read_source X w Hw rx) as (u & Hu & Hin & Hwu & Hl & Hv); cbn; auto.
        in_ops Hin; fin. }
      assert (Hrb : rb X w ry wy).
      { split; [cbn; intuition auto |]. split; [cbn; intuition auto |].
        split; [exact Logic.I |]. split; [exact Logic.I |]. split; [reflexivity |].
        intros u0 Hu0. pose proof (rf_dom Hw _ _ Hu0) as (Hin & _ & Hwu & _ & Hl & Hv).
        in_ops Hin; fin. }
      apply (HD2 wy).
      eapply t_trans with (y := wx).
      { apply t_step. left. left. left. right. split; [| split; exact Logic.I].
        apply pre0_iff; [exact wf |]. split; [po_edge | right; right; exact Logic.I]. }
      eapply t_trans with (y := rx).
      { apply t_step. left. left. right. split; [exact Hrx | cbn; discriminate]. }
      eapply t_trans with (y := ry).
      { apply t_step. left. left. left. left. split; [exact Logic.I |].
        apply t_step. apply Hpre0. apply pre0_iff; [exact wf |]. split; [po_edge | right; left; exact Logic.I]. }
      apply t_step. right. exact Hrb.
    Qed.

    (** *** The trace [wy · wx · rx · ry] *)

    Definition l : trace C := ops.

    Lemma l_respects : respects l (pre0 X I).
    Proof.
      intros a b Hab. apply pre0_iff in Hab; [| exact wf].
      destruct Hab as [(Ha & Hb & Ht & Hh) _].
      in_ops Ha; in_ops Hb; cbn in Ht, Hh; try discriminate; try lia.
      - exists 0, 1. repeat split; lia.
      - exists 2, 3. repeat split; lia.
    Qed.

    (** By Thm. decl the trace is not in the hidden memory over [Loc4]. *)
    Theorem nu_forbid : ~ nu I l.
    Proof.
      intros Hnu.
      assert (H : exists s, nu I s /\ presents s X /\ respects s (pre0 X I)).
      { exists l. split; [exact Hnu |]. split; [apply Permutation.Permutation_refl | apply l_respects]. }
      apply (Equivalence.declarative_RC Loc4 Loc4_dec X wf (pre0 X I) (admissible_pre0 X wf)) in H.
      destruct H as (w & Hw & Hcons).
      exact (ours_forbid w (pre0 X I) Hw (admissible_pre0 X wf) Hcons).
    Qed.

    (** *** Its projections are behaviours of the hidden single cells *)

    Import Tensor.

    Notation lsx := (lsingle (C := C) lx).
    Notation lsy := (lsingle (C := C) ly).

    Lemma proj_lx : proj_set lsx l = [wx; rx].
    Proof. reflexivity. Qed.

    Lemma proj_ly : proj_set lsy l = [wy; ry].
    Proof. reflexivity. Qed.

    (** [wx · rx] is hidden from [wx · flush(x) · rx]. *)
    Lemma cell_x : nu_on I lsx [wx; rx].
    Proof.
      exists [wx; @BF C 1%positive 0 lx; rx]. split; [| reflexivity].
      split; [| split].
      - intros b Hb. in_ops Hb; reflexivity.
      - intros s1 t h x s2 m Hs Hm m' Hm' Hlt.
        destruct s1 as [| b1 [| b2 [| b3 s1]]]; unfold wx, rx in Hs; cbn in Hs.
        + discriminate.
        + injection Hs; intros; subst.
          unfold wx in Hm; cbn in Hm. injection Hm; intros; subst.
          unfold wx in Hm'; cbn in Hm'. destruct Hm' as [<- | []]. cbn in Hlt. lia.
        + discriminate.
        + injection Hs; intros H4 _ _ _. destruct s1; discriminate H4.
      - intros x Hx. apply lsingle_true in Hx. subst x.
        exists (next rx (next (@BF C 1%positive 0 lx) (next wx init_state))).
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [exact Logic.I | reflexivity]]. }
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [| reflexivity]].
          vm_compute. discriminate. }
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [| reflexivity]].
          right. split; vm_compute; reflexivity. }
        constructor.
    Qed.

    (** [wy · ry] is hidden from itself. *)
    Lemma cell_y : nu_on I lsy [wy; ry].
    Proof.
      exists [wy; ry]. split; [| reflexivity].
      split; [| split].
      - intros b Hb. in_ops Hb; reflexivity.
      - intros s1 t h x s2 m Hs Hm m' Hm' Hlt.
        destruct s1 as [| b1 [| b2 s1]]; unfold wy, ry in Hs; cbn in Hs.
        + discriminate.
        + discriminate.
        + injection Hs; intros H3 _ _. destruct s1; discriminate H3.
      - intros x Hx. apply lsingle_true in Hx. subst x.
        exists (next ry (next wy init_state)).
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [exact Logic.I | reflexivity]]. }
        econstructor.
        { apply cell_step_iff. split; [reflexivity | split; [| reflexivity]].
          right. split; vm_compute; reflexivity. }
        constructor.
    Qed.

    (** The hidden memory over [{x, y}] is not the specification tensor
        of the hidden cells: [ν_RC[{x,y}] ⊊ ν_RC[{x}] ⊗ ν_RC[{y}]]. *)
    Theorem hidden_tensor_is_not_a_product :
      spec_tens lsx lsy (nu_on I lsx) (nu_on I lsy) l /\
      ~ nu_on I (lunion lsx lsy) l.
    Proof.
      split.
      - split; [| split].
        + intros b Hb. in_ops Hb; reflexivity.
        + rewrite proj_lx. apply cell_x.
        + rewrite proj_ly. apply cell_y.
      - intros (s' & HV & Hh). apply nu_forbid. exists s'. split; [| exact Hh].
        apply V_on_iff in HV. tauto.
    Qed.

  End MP.

End Litmus.
