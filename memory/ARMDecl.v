(** * The ARMv8 declarative model in the shape of (D1)/(D2)

    Prop. mem:prop:arm shows [ob ⊆ (Dc_pre ∪ S)⁺]: our global axiom, with
    [S = [rel];po;[acq]] adjoined, is at least as strong as ARM's EXTERNAL.
    The converse fails (Ex. mem:ex:rsw, Ex. mem:ex:mpctrl): [ppo_pre] is
    [[rd];pre⁺], a transitive closure that chains through same-location
    program order and through every wait-induced edge, whereas [ob]'s
    intra-thread generators are single [po] pairs.

    This file gives the version of (D2) that is *exactly* ARM.  Replace
    [ppo_pre] by ARM's own intra-thread generators,

      ppo_ARM = dob ∪ bob
              = addr ∪ data ∪ ctrl;[W] ∪ addr;po;[W] ∪ (ctrl ∪ data);moi
                ∪ (addr ∪ data);rfi ∪ [rel];po;[acq] ∪ [acq];po ∪ po;[rel]
                ∪ po;[rel];moi,

    and keep the communication part of (D2) unchanged:

      Dc_ARM = ppo_ARM ∪ rfe ∪ mo ∪ rb.

    Then (D1) ∧ acyclic(Dc_ARM) ⟺ INTERNAL ∧ EXTERNAL.  The only
    difference between [Dc_ARM] and [ob]'s generators is that [Dc_ARM]
    contains the internal communication edges [moi] and [rbi] while [obs]
    has only [moe] and [rbe]; the content of the theorem is that, under
    INTERNAL, every [ob] edge into the source of an internal edge can be
    redirected to its target ([gen_rbi], [gen_moi]), so adjoining [moi] and
    [rbi] creates no new cycles.

    The dependency relations are parameters, as in [ARM.v]; the proof uses
    only that [data] targets writes, true of ARM's syntactic dependencies. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.PArith.PArith.
Require Import Coq.Logic.Classical.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Consequences.
Require Import memory.ARM.

Import ListNotations.

Module ARMDecl.

  Import Cell Cell.Instances Decl Consequences.

  Section ARMDecl.
    Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).
    Notation C := (RC_cfg dec).
    Notation block := (block C).
    Notation I := (mode_indep (C := C)).
    Notation is_rel := (Consequences.is_rel Loc dec).
    Notation is_acq := (Consequences.is_acq Loc dec).

    Variable X : cand C.
    Hypothesis HX : wf_cand X.
    Variable w : witness C.
    Hypothesis Hw : wf_witness X w.
    Hypothesis HD1 : D1 X w.

    Variables addr data ctrl : relation block.

    (** The one well-formedness fact about the dependency relations that
        the redirection needs: a data dependency targets a write (an
        [ob] edge [data;[R]] would have nothing to be redirected to). *)
    Hypothesis Hdata_write : forall a b, data a b -> is_write b.

    Notation obs := (ARM.obs Loc dec X w).
    Notation dob := (ARM.dob Loc dec X w addr data ctrl).
    Notation S := (ARM.S Loc dec X).
    Notation bob0 := (ARM.bob0 Loc dec X w).
    Notation bob := (ARM.bob Loc dec X w).
    Notation ob := (ARM.ob Loc dec X w addr data ctrl).
    Notation internal := (ARM.internal Loc dec X w).
    Notation external := (ARM.external Loc dec X w addr data ctrl).
    Notation arm_consistent := (ARM.arm_consistent Loc dec X w addr data ctrl).

    (** ** The ARM-shaped global axiom *)

    Definition ppo_ARM : relation block := dob ∪ bob.

    Definition Dc_ARM : relation block := ppo_ARM ∪ rfe X w ∪ mo w ∪ rb X w.

    Definition consistent_ARM : Prop := D1 X w /\ acyclic Dc_ARM.

    (** ** The generators of [ob], as an inductive relation *)

    Inductive gen : block -> block -> Prop :=
    | g_rfe u r : rfe X w u r -> gen u r
    | g_rbe r u : rbe X w r u -> gen r u
    | g_moe a b : moe w a b -> gen a b
    | g_addr a b : addr a b -> gen a b
    | g_data a b : data a b -> gen a b
    | g_ctrl_W a b : ctrl a b -> is_write b -> gen a b
    | g_addr_po_W a y b : addr a y -> po X y b -> is_write b -> gen a b
    | g_ctrl_moi a y b : ctrl a y -> moi w y b -> gen a b
    | g_data_moi a y b : data a y -> moi w y b -> gen a b
    | g_addr_rfi a y b : addr a y -> rfi X w y b -> gen a b
    | g_data_rfi a y b : data a y -> rfi X w y b -> gen a b
    | g_S a b : is_rel a -> po X a b -> is_acq b -> gen a b
    | g_acq_po a b : is_acq a -> po X a b -> gen a b
    | g_po_rel a b : po X a b -> is_rel b -> gen a b
    | g_po_rel_moi a y b : po X a y -> is_rel y -> moi w y b -> gen a b.

    Lemma gen_iff a b : gen a b <-> (obs ∪ dob ∪ bob) a b.
    Proof.
      unfold ARM.obs, ARM.dob, ARM.bob, ARM.bob0, ARM.S. split.
      - intros H. inversion H; subst.
        + left. left. left. left. assumption.
        + left. left. left. right. assumption.
        + left. left. right. assumption.
        + left. right. left. left. left. left. left. assumption.
        + left. right. left. left. left. left. right. assumption.
        + left. right. left. left. left. right. split; assumption.
        + left. right. left. left. right. exists y. split; [assumption | split; assumption].
        + left. right. left. right. exists y. split; [left; assumption | assumption].
        + left. right. left. right. exists y. split; [right; assumption | assumption].
        + left. right. right. exists y. split; [left; assumption | assumption].
        + left. right. right. exists y. split; [right; assumption | assumption].
        + right. left. split; [assumption | split; assumption].
        + right. right. left. left. split; assumption.
        + right. right. left. right. split; assumption.
        + right. right. right. exists y. split; [split; assumption | assumption].
      - intros [[[[Hrfe | Hrbe] | Hmoe] | Hdob] | [HS | [[Hacq | Hrel] | Hrelmoi]]].
        + apply g_rfe; assumption.
        + apply g_rbe; assumption.
        + apply g_moe; assumption.
        + destruct Hdob as [[[[[Haddr | Hdata] | [Hctrl HW]] | (y & Haddr & Hpo & HW)]
                             | (y & [Hc | Hd] & Hmoi)] | (y & [Ha | Hd] & Hrfi)].
          * apply g_addr; assumption.
          * apply g_data; assumption.
          * apply g_ctrl_W; assumption.
          * eapply g_addr_po_W; eassumption.
          * eapply g_ctrl_moi; eassumption.
          * eapply g_data_moi; eassumption.
          * eapply g_addr_rfi; eassumption.
          * eapply g_data_rfi; eassumption.
        + destruct HS as (Hrel & Hpo & Hacq). apply g_S; assumption.
        + destruct Hacq as [Hacq Hpo]. apply g_acq_po; assumption.
        + destruct Hrel as [Hpo Hrel]. apply g_po_rel; assumption.
        + destruct Hrelmoi as (y & [Hpo Hrel] & Hmoi). eapply g_po_rel_moi; eassumption.
    Qed.

    Notation rf_tgt_read := (Consequences.rf_tgt_read C X w Hw).
    Notation mo_src_write := (Consequences.mo_src_write C X w Hw).
    Notation mo_tgt_write := (Consequences.mo_tgt_write C X w Hw).
    Notation rb_src_read := (Consequences.rb_src_read C X w).
    Notation rb_tgt_write := (Consequences.rb_tgt_write C X w).

    (** ** Internal communication edges *)

    Definition int : relation block := moi w ∪ rbi X w.

    Lemma moi_po a b : moi w a b -> po X a b.
    Proof. intros [Hmo Ht]. apply (moi_po_loc C X HX w Hw HD1); auto. Qed.

    Lemma rbi_po r u : rbi X w r u -> po X r u.
    Proof. intros [Hrb Ht]. apply (rbi_po_loc C X HX w Hw HD1); auto. Qed.

    Lemma rfi_po u r : rfi X w u r -> po X u r.
    Proof. intros [Hrf Ht]. apply (rfi_po_loc C X HX w Hw HD1); auto. Qed.

    Lemma moi_trans a b c : moi w a b -> moi w b c -> moi w a c.
    Proof.
      intros [H1 T1] [H2 T2]. split; [eapply (mo_trans Hw); eauto | congruence].
    Qed.

    Lemma rbi_moi r u u' : rbi X w r u -> moi w u u' -> rbi X w r u'.
    Proof.
      intros [H1 T1] [H2 T2]. split; [eapply (rb_mo_rb C X w Hw); eauto | congruence].
    Qed.

    Lemma int_trans a b c : int a b -> int b c -> int a c.
    Proof.
      intros [H1 | H1] [H2 | H2].
      - left. eapply moi_trans; eauto.
      - exfalso. destruct H1 as [H1 _]. destruct H2 as [H2 _].
        eapply (write_read_excl C b); [eapply mo_tgt_write | eapply rb_src_read]; eauto.
      - right. eapply rbi_moi; eauto.
      - exfalso. destruct H1 as [H1 _]. destruct H2 as [H2 _].
        eapply (write_read_excl C b); [eapply rb_tgt_write | eapply rb_src_read]; eauto.
    Qed.

    Lemma int_irrefl a : ~ int a a.
    Proof.
      intros [[H _] | [H _]].
      - eapply (mo_irrefl Hw); eauto.
      - eapply (write_read_excl C a); [eapply rb_tgt_write | eapply rb_src_read]; eauto.
    Qed.

    (** ** Redirection: an [ob] edge into the source of an internal edge
        extends to its target *)

    Ltac wr_contra :=
      match goal with
      | H1 : is_write ?x, H2 : is_read ?x |- _ => exfalso; exact (write_read_excl C x H1 H2)
      end.

    Lemma gen_rbi x r u : gen x r -> rbi X w r u -> gen⁺ x u.
    Proof.
      intros Hg Hrbi.
      assert (Hpo : po X r u) by (apply rbi_po; auto).
      destruct Hrbi as [Hrb Ht].
      assert (Hrb' := Hrb). destruct Hrb' as (_ & _ & Hrd & Hwu & _ & Hsrc).
      inversion Hg; subst.
      - (* rfe: the source write is [mo]-before [u], on another thread *)
        destruct H as [Hrf Htid]. apply t_step. apply g_moe. split; [apply Hsrc; auto | congruence].
      - pose proof (rb_tgt_write _ _ (proj1 H)). wr_contra.
      - pose proof (mo_tgt_write _ _ (proj1 H)). wr_contra.
      - apply t_step. eapply g_addr_po_W; eauto.
      - pose proof (Hdata_write _ _ H). wr_contra.
      - wr_contra.
      - wr_contra.
      - destruct H0 as [H0 _]. pose proof (mo_tgt_write _ _ H0). wr_contra.
      - destruct H0 as [H0 _]. pose proof (mo_tgt_write _ _ H0). wr_contra.
      - (* addr ; rfi : [addr ; po ; [W]] *)
        apply t_step. eapply g_addr_po_W; [eassumption | | exact Hwu].
        eapply (po_trans HX); [apply rfi_po; eassumption | exact Hpo].
      - (* data ; rfi : [data ; moi] *)
        destruct H0 as [Hrf Htid]. apply t_step. eapply g_data_moi; [eassumption |].
        split; [apply Hsrc; auto | congruence].
      - (* [rel];po;[acq] followed by [acq];po *)
        eapply t_trans with (y := r); apply t_step; [apply g_S; assumption | apply g_acq_po; assumption].
      - apply t_step. apply g_acq_po; [assumption | eapply (po_trans HX); eauto].
      - pose proof (is_rel_write Loc dec _ H0). wr_contra.
      - destruct H1 as [H1 _]. pose proof (mo_tgt_write _ _ H1). wr_contra.
    Qed.

    Lemma gen_moi x a b : gen x a -> moi w a b -> gen⁺ x b.
    Proof.
      intros Hg Hmoi.
      assert (Hpo : po X a b) by (apply moi_po; auto).
      assert (Hmoi' := Hmoi). destruct Hmoi' as [Hmo Ht].
      pose proof (mo_src_write _ _ Hmo) as Hwa.
      pose proof (mo_tgt_write _ _ Hmo) as Hwb.
      inversion Hg; subst.
      - destruct H as [Hrf _]. pose proof (rf_tgt_read _ _ Hrf). wr_contra.
      - destruct H as [Hrb Htid]. apply t_step. apply g_rbe.
        split; [eapply (rb_mo_rb C X w Hw); eauto | congruence].
      - destruct H as [Hmo' Htid]. apply t_step. apply g_moe.
        split; [eapply (mo_trans Hw); eauto | congruence].
      - apply t_step. eapply g_addr_po_W; eauto.
      - apply t_step. eapply g_data_moi; eauto.
      - apply t_step. eapply g_ctrl_moi; eauto.
      - apply t_step. eapply g_addr_po_W; [eassumption | eapply (po_trans HX); eauto | assumption].
      - apply t_step. eapply g_ctrl_moi; [eassumption | eapply moi_trans; eauto].
      - apply t_step. eapply g_data_moi; [eassumption | eapply moi_trans; eauto].
      - destruct H0 as [Hrf _]. pose proof (rf_tgt_read _ _ Hrf). wr_contra.
      - destruct H0 as [Hrf _]. pose proof (rf_tgt_read _ _ Hrf). wr_contra.
      - pose proof (is_acq_read Loc dec _ H1). wr_contra.
      - apply t_step. apply g_acq_po; [assumption | eapply (po_trans HX); eauto].
      - apply t_step. eapply g_po_rel_moi; eauto.
      - apply t_step. eapply g_po_rel_moi; [eassumption | eassumption | eapply moi_trans; eauto].
    Qed.

    Lemma gen_int x a b : gen x a -> int a b -> gen⁺ x b.
    Proof. intros Hg [H | H]; [eapply gen_moi | eapply gen_rbi]; eauto. Qed.

    Lemma tc_gen_int x a : gen⁺ x a -> forall b, int a b -> gen⁺ x b.
    Proof.
      intros H. induction H as [x a Hxa | x y a Hxy IH1 Hya IH2]; intros b Hab.
      - eapply gen_int; eauto.
      - eapply t_trans; [exact Hxy | apply IH2; exact Hab].
    Qed.

    (** ** Normal form of a path in [gen ∪ int] *)

    Lemma gen_int_nf x y :
      (gen ∪ int)⁺ x y ->
      gen⁺ x y \/ int x y \/ (exists z, int x z /\ gen⁺ z y).
    Proof.
      intros H. induction H as [x y [Hg | Hi] | x y z Hxy IH1 Hyz IH2].
      - left. apply t_step. exact Hg.
      - right. left. exact Hi.
      - destruct IH1 as [H1 | [H1 | (z1 & H1 & H1')]];
          destruct IH2 as [H2 | [H2 | (z2 & H2 & H2')]].
        + left. eapply t_trans; eauto.
        + left. eapply tc_gen_int; eauto.
        + left. eapply t_trans; [eapply tc_gen_int; eauto | exact H2'].
        + right. right. exists y. auto.
        + right. left. eapply int_trans; eauto.
        + right. right. exists z2. split; [eapply int_trans; eauto | exact H2'].
        + right. right. exists z1. split; [exact H1 | eapply t_trans; eauto].
        + right. right. exists z1. split; [exact H1 | eapply tc_gen_int; eauto].
        + right. right. exists z1. split; [exact H1 |].
          eapply t_trans; [eapply tc_gen_int; eauto | exact H2'].
    Qed.

    Theorem gen_int_acyclic : acyclic gen -> acyclic (gen ∪ int).
    Proof.
      intros Hac x Hx. apply gen_int_nf in Hx.
      destruct Hx as [H | [H | (z & Hxz & Hzx)]].
      - eapply Hac; eauto.
      - eapply int_irrefl; eauto.
      - apply (Hac z). eapply tc_gen_int; eauto.
    Qed.

    (** ** [Dc_ARM] is [gen ∪ int] *)

    Lemma mo_split a b : mo w a b -> moe w a b \/ moi w a b.
    Proof.
      intros H. destruct (Pos.eq_dec (b_tid a) (b_tid b)) as [Ht | Ht];
        [right | left]; split; auto.
    Qed.

    Lemma rb_split r u : rb X w r u -> rbe X w r u \/ rbi X w r u.
    Proof.
      intros H. destruct (Pos.eq_dec (b_tid r) (b_tid u)) as [Ht | Ht];
        [right | left]; split; auto.
    Qed.

    Lemma Dc_ARM_gen_int : Dc_ARM ⊆ gen ∪ int.
    Proof.
      intros a b [[[Hppo | Hrfe] | Hmo] | Hrb].
      - left. apply gen_iff. destruct Hppo as [Hdob | Hbob]; [left; right | right]; assumption.
      - left. apply g_rfe. exact Hrfe.
      - destruct (mo_split _ _ Hmo) as [H | H]; [left; apply g_moe; exact H | right; left; exact H].
      - destruct (rb_split _ _ Hrb) as [H | H]; [left; apply g_rbe; exact H | right; right; exact H].
    Qed.

    Lemma gen_Dc_ARM : (obs ∪ dob ∪ bob) ⊆ Dc_ARM.
    Proof.
      intros a b [[[[Hrfe | Hrbe] | Hmoe] | Hdob] | Hbob].
      - left. left. right. exact Hrfe.
      - right. apply Hrbe.
      - left. right. apply Hmoe.
      - left. left. left. left. exact Hdob.
      - left. left. left. right. exact Hbob.
    Qed.

    (** ** The theorem *)

    Lemma internal_iff_D1 : internal <-> D1 X w.
    Proof.
      split; intros H x Hx; apply (H x); refine (tc_incl _ Hx);
        intros a b [[[H1 | H1] | H1] | H1].
      - left. left. left. exact H1.
      - left. left. right. exact H1.
      - right. exact H1.
      - left. right. exact H1.
      - left. left. left. exact H1.
      - left. left. right. exact H1.
      - right. exact H1.
      - left. right. exact H1.
    Qed.

    Theorem arm_declarative_D1 : consistent_ARM <-> arm_consistent.
    Proof.
      split.
      - intros [HD1' Hac]. split.
        + apply internal_iff_D1. exact HD1'.
        + apply acyclic_tc. eapply acyclic_incl; [apply gen_Dc_ARM | exact Hac].
      - intros [Hint Hext]. split.
        + apply internal_iff_D1. exact Hint.
        + eapply acyclic_incl; [apply Dc_ARM_gen_int |].
          apply gen_int_acyclic. intros x Hx. apply (Hext x).
          refine (tc_incl _ Hx). intros a b H. apply t_step. apply gen_iff. exact H.
    Qed.

  End ARMDecl.

  (** (D1) is part of both sides, so the section hypothesis [HD1] can be
      discharged from either. *)
  Theorem arm_declarative (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y})
      (X : cand (RC_cfg dec)) (HX : wf_cand X) (w : witness (RC_cfg dec)) (Hw : wf_witness X w)
      (addr data ctrl : relation (block (RC_cfg dec)))
      (Hdata_write : forall a b, data a b -> is_write b) :
    consistent_ARM Loc dec X w addr data ctrl <-> ARM.arm_consistent Loc dec X w addr data ctrl.
  Proof.
    split.
    - intros H. apply (arm_declarative_D1 Loc dec X HX w Hw (proj1 H) addr data ctrl Hdata_write). exact H.
    - intros H. assert (HD1 : D1 X w) by (apply (internal_iff_D1 Loc dec X w); apply H).
      apply (arm_declarative_D1 Loc dec X HX w Hw HD1 addr data ctrl Hdata_write). exact H.
  Qed.

  (** ** Relation to (D2): [Dc_ARM ⊆ (Dc_pre ∪ S)⁺] under (W) *)

  Section Containment.
    Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).
    Notation C := (RC_cfg dec).
    Notation block := (block C).
    Notation I := (mode_indep (C := C)).

    Variable X : cand C.
    Hypothesis HX : wf_cand X.
    Variable w : witness C.
    Hypothesis Hw : wf_witness X w.
    Hypothesis HD1 : D1 X w.
    Variables addr data ctrl : relation block.
    Hypothesis Hdep_read : forall a b, ARM.dep Loc dec addr data ctrl a b -> is_read a.
    Variable pre : relation block.
    Hypothesis Hadm : admissible X I pre.
    Hypothesis HW_dep : forall a b, ARM.dep Loc dec addr data ctrl a b -> pre a b.
    Hypothesis HW_dep_po : forall a b c, ARM.dep Loc dec addr data ctrl a b -> po X b c -> pre a c.

    Notation Dc := (Dc X I w pre).
    Notation S := (ARM.S Loc dec X).
    Notation Dc_ARM := (Dc_ARM Loc dec X w addr data ctrl).

    Theorem Dc_ARM_Dc_S : Dc_ARM ⊆ (Dc ∪ S)⁺.
    Proof.
      intros a b [[[Hppo | Hrfe] | Hmo] | Hrb].
      - destruct Hppo as [Hdob | [HS | Hbob0]].
        + eapply tc_incl; [apply rel_union_incl_l |].
          apply (ARM.obs_dob_bob0_Dc Loc dec X HX w Hw HD1 addr data ctrl Hdep_read pre Hadm HW_dep HW_dep_po).
          left. right. exact Hdob.
        + apply t_step. right. exact HS.
        + eapply tc_incl; [apply rel_union_incl_l |].
          apply (ARM.obs_dob_bob0_Dc Loc dec X HX w Hw HD1 addr data ctrl Hdep_read pre Hadm HW_dep HW_dep_po).
          right. exact Hbob0.
      - apply t_step. left. left. left. right. exact Hrfe.
      - apply t_step. left. left. right. exact Hmo.
      - apply t_step. left. right. exact Hrb.
    Qed.

    Corollary Dc_S_consistent_ARM :
      acyclic (Dc ∪ S) -> consistent_ARM Loc dec X w addr data ctrl.
    Proof.
      intros Hac. split; [exact HD1 |].
      eapply acyclic_incl; [apply Dc_ARM_Dc_S | apply acyclic_tc; exact Hac].
    Qed.

  End Containment.

End ARMDecl.
