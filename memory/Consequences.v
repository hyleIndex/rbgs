(** * Consequences of (D1), and the shape of the RC instance

    Facts used by the comparison with the reference models
    (Section L.7 of the paper):

    - under (D1) the internal communication relations lie in program
      order: [rfi ∪ moi ∪ rbi ⊆ po_loc], and program order between two
      same-location writes is [mo] (the consequences (C1)--(C3) used in
      Lemma mem:lem:realize);
    - for the release/acquire instance, Cor. mem:cor:pre:
      [po \ RC.I = po_loc ∪ [acq];po ∪ po;[rel]]. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import Stdlib.Relations.Relation_Operators.
Require Import Stdlib.Logic.Classical.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.

Import ListNotations.

Module Consequences.

  Import Cell Decl.

  Section D1Consequences.
    Context (C : Cfg).
    Abbreviation block := (block C).

    Variable X : cand C.
    Hypothesis HX : wf_cand X.
    Variable w : witness C.
    Hypothesis Hw : wf_witness X w.
    Hypothesis HD1 : D1 X w.

    Abbreviation ops := (ops X).

    Lemma write_read_excl (b : block) : is_write b -> is_read b -> False.
    Proof. destruct b; cbn; tauto. Qed.

    Lemma ops_write_or_read b : In b ops -> is_write b \/ is_read b.
    Proof.
      intros Hb. pose proof (ops_noflush HX b Hb). destruct b; cbn in *; tauto.
    Qed.

    Lemma coh_step a b : coh X w a b -> (coh X w)⁺ a b.
    Proof. apply t_step. Qed.

    (** (C1) Same-location program order between writes is [mo]. *)
    Lemma po_loc_mo a b :
      po_loc X a b -> is_write a -> is_write b -> mo w a b.
    Proof.
      intros Hpo Ha Hb.
      assert (Hin := po_dom HX _ _ (proj1 Hpo)). destruct Hin as (Hina & Hinb & _).
      assert (Hne : a <> b) by (intros ->; eapply (po_irrefl HX); apply Hpo).
      destruct (mo_total Hw Hina Hinb Ha Hb (proj2 Hpo) Hne) as [H | H]; auto.
      exfalso. apply (HD1 a). eapply t_trans; apply t_step.
      - left. left. left. exact Hpo.
      - left. right. exact H.
    Qed.

    (** Internal modification order is program order. *)
    Lemma moi_po_loc a b :
      mo w a b -> b_tid a = b_tid b -> po_loc X a b.
    Proof.
      intros Hmo Ht.
      assert (Hd := mo_dom Hw _ _ Hmo). destruct Hd as (Hina & Hinb & Hwa & Hwb & Hl).
      assert (Hne : a <> b) by (intros ->; eapply (mo_irrefl Hw); eauto).
      destruct (po_total HX Hina Hinb Ht Hne) as [Hpo | Hpo]; [split; auto |].
      exfalso. assert (Hmo' : mo w b a) by (apply po_loc_mo; auto; split; auto).
      eapply (mo_irrefl Hw). eapply (mo_trans Hw); eauto.
    Qed.

    (** (C3) An internal reads-from edge is program order. *)
    Lemma rfi_po_loc u r :
      rf w u r -> b_tid u = b_tid r -> po_loc X u r.
    Proof.
      intros Hrf Ht.
      assert (H := rf_dom Hw _ _ Hrf). destruct H as (Hinu & Hinr & Hwu & Hrd & Hl & _).
      assert (Hne : u <> r) by (intros ->; eapply write_read_excl; eauto).
      destruct (po_total HX Hinu Hinr Ht Hne) as [Hpo | Hpo]; [split; auto |].
      exfalso. apply (HD1 r). eapply t_trans with (y := u); apply t_step.
      - left. left. left. exact (conj Hpo (eq_sym Hl)).
      - left. left. right. exact Hrf.
    Qed.

    (** (C2) A read never sees a version older than an earlier write of
        its own thread. *)
    Lemma po_loc_read_src w0 r :
      po_loc X w0 r -> is_write w0 -> is_read r ->
      rf w w0 r \/ (forall u, rf w u r -> mo w w0 u).
    Proof.
      intros Hpo Hw0 Hr.
      destruct (classic (rf w w0 r)) as [H | H]; [left; auto | right].
      intros u Hu.
      assert (Hin := po_dom HX _ _ (proj1 Hpo)). destruct Hin as (Hin0 & Hinr & _).
      assert (Hu' := rf_dom Hw _ _ Hu). destruct Hu' as (Hinu & _ & Hwu & _ & Hlu & _).
      assert (Hne : w0 <> u) by (intros ->; contradiction).
      destruct (mo_total Hw Hin0 Hinu Hw0 Hwu ltac:(rewrite Hlu; apply Hpo) Hne) as [Hm | Hm]; auto.
      exfalso. apply (HD1 w0). eapply t_trans; [apply t_step; left; left; left; exact Hpo |].
      apply t_step. right. repeat split; auto; [symmetry; apply Hpo |].
      intros u0 Hu0. assert (u0 = u) by (eapply (rf_func Hw); eauto). subst u0. exact Hm.
    Qed.

    Lemma po_loc_read_init w0 r :
      po_loc X w0 r -> is_write w0 -> is_read r -> (forall u, ~ rf w u r) -> False.
    Proof.
      intros Hpo Hw0 Hr Hno.
      assert (Hin := po_dom HX _ _ (proj1 Hpo)). destruct Hin as (Hin0 & Hinr & _).
      apply (HD1 w0). eapply t_trans; [apply t_step; left; left; left; exact Hpo |].
      apply t_step. right. repeat split; auto; [symmetry; apply Hpo |].
      intros u Hu. exfalso. eapply Hno. eauto.
    Qed.

    (** An internal reads-before edge is program order. *)
    Lemma rbi_po_loc r u :
      rb X w r u -> b_tid r = b_tid u -> po_loc X r u.
    Proof.
      intros Hrb Ht.
      assert (Hrb' := Hrb). destruct Hrb' as (Hinr & Hinu & Hrd & Hwu & Hl & Hsrc).
      assert (Hne : r <> u) by (intros ->; eapply write_read_excl; eauto).
      destruct (po_total HX Hinr Hinu Ht Hne) as [Hpo | Hpo]; [split; auto |].
      exfalso.
      assert (Hpo' : po_loc X u r) by (split; auto).
      destruct (classic (exists u0, rf w u0 r)) as [[u0 Hu0] | Hno].
      - destruct (po_loc_read_src u r Hpo' Hwu Hrd) as [Hrf | Hmo].
        + specialize (Hsrc u Hrf). eapply (mo_irrefl Hw); eauto.
        + specialize (Hmo u0 Hu0). specialize (Hsrc u0 Hu0).
          eapply (mo_irrefl Hw). eapply (mo_trans Hw); eauto.
      - eapply (po_loc_read_init u r); eauto.
    Qed.

    (** Endpoints of the communication edges. *)
    Lemma rf_src_write u r : rf w u r -> is_write u.
    Proof. intros H. apply (rf_dom Hw) in H. tauto. Qed.
    Lemma rf_tgt_read u r : rf w u r -> is_read r.
    Proof. intros H. apply (rf_dom Hw) in H. tauto. Qed.
    Lemma mo_src_write a b : mo w a b -> is_write a.
    Proof. intros H. apply (mo_dom Hw) in H. tauto. Qed.
    Lemma mo_tgt_write a b : mo w a b -> is_write b.
    Proof. intros H. apply (mo_dom Hw) in H. tauto. Qed.
    Lemma rb_src_read r u : rb X w r u -> is_read r.
    Proof. intros H. destruct H as (_ & _ & H & _). exact H. Qed.
    Lemma rb_tgt_write r u : rb X w r u -> is_write u.
    Proof. intros H. destruct H as (_ & _ & _ & H & _). exact H. Qed.

    (** Communication edges preserve location. *)
    Lemma rf_same_loc u r : rf w u r -> b_loc u = b_loc r.
    Proof. intros H. apply (rf_dom Hw) in H. tauto. Qed.

    Lemma mo_same_loc a b : mo w a b -> b_loc a = b_loc b.
    Proof. intros H. apply (mo_dom Hw) in H. tauto. Qed.

    Lemma rb_same_loc r u : rb X w r u -> b_loc r = b_loc u.
    Proof. intros H. destruct H as (_ & _ & _ & _ & H & _). exact H. Qed.

    (** [rf ; rb ⊆ mo] and [rb ; mo ⊆ rb]. *)
    Lemma rf_rb_mo u r u' : rf w u r -> rb X w r u' -> mo w u u'.
    Proof. intros Hrf (_ & _ & _ & _ & _ & H). apply H. exact Hrf. Qed.

    Lemma rb_mo_rb r u u' : rb X w r u -> mo w u u' -> rb X w r u'.
    Proof.
      intros (Hr & Hu & Hrd & Hwu & Hl & H) Hmo.
      assert (Hd := mo_dom Hw _ _ Hmo). destruct Hd as (_ & Hu' & _ & Hwu' & Hl').
      repeat split; auto; [congruence |]. intros u0 Hu0. eapply (mo_trans Hw); eauto.
    Qed.

  End D1Consequences.

  (** ** The release/acquire instance: Cor. mem:cor:pre *)

  Section RC.
    Import Cell.Instances.
    Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).
    Abbreviation C := (RC_cfg dec).
    Abbreviation block := (block C).

    Definition is_rel (b : block) : Prop :=
      match b with BW _ _ _ _ rel => True | _ => False end.
    Definition is_acq (b : block) : Prop :=
      match b with BR _ _ _ acq _ => True | _ => False end.

    Lemma is_rel_write b : is_rel b -> is_write b.
    Proof. destruct b as [t h x v [|] | |]; cbn; tauto. Qed.
    Lemma is_acq_read b : is_acq b -> is_read b.
    Proof. destruct b as [| t h x [|] v |]; cbn; tauto. Qed.

    (** [access m ≤ LFence] iff [m] is not an acquire read; [access m ≤ RFence]
        iff [m] is not a release write (for reads and writes). *)
    Lemma mode_indep_iff (a b : block) :
      ~ is_flush a -> ~ is_flush b ->
      (mode_indep (C := C) (b_inv a) (b_inv b) <->
       (b_loc a <> b_loc b /\ ~ is_acq a /\ ~ is_rel b)).
    Proof.
      intros Ha Hb. unfold mode_indep.
      destruct a as [ta ha xa va [|] | ta ha xa [|] va | ta ha xa];
        destruct b as [tb hb xb vb [|] | tb hb xb [|] vb | tb hb xb];
        cbn in *; try contradiction; cbn; intuition.
    Qed.

    (** Cor. mem:cor:pre: [po \ RC.I = po_loc ∪ [acq];po ∪ po;[rel]]. *)
    Lemma pre0_iff (X : cand C) (HX : wf_cand X) a b :
      pre0 X (mode_indep (C := C)) a b <->
      po X a b /\ (b_loc a = b_loc b \/ is_acq a \/ is_rel b).
    Proof.
      split.
      - intros [Hpo HnI]. split; auto.
        assert (Hin := po_dom HX _ _ Hpo). destruct Hin as (Hina & Hinb & _).
        pose proof (ops_noflush HX a Hina). pose proof (ops_noflush HX b Hinb).
        apply NNPP. intros Hno. apply HnI. unfold I_blk. apply mode_indep_iff; auto.
        split; [| split]; intros Hc; apply Hno; auto.
      - intros [Hpo Hshape]. split; auto.
        assert (Hin := po_dom HX _ _ Hpo). destruct Hin as (Hina & Hinb & _).
        pose proof (ops_noflush HX a Hina). pose proof (ops_noflush HX b Hinb).
        intros HI. unfold I_blk in HI. apply mode_indep_iff in HI; auto. tauto.
    Qed.

  End RC.

  (** ** Program-order edges that (D2) sees, in the release/acquire instance

      By Cor. mem:cor:pre, [[acq];po] and [po;[rel]] lie in [pre_0 ⊆ pre]; a
      pair starting at a read is then in [[rd];pre ⊆ ppo], and a pair of
      writes ending at a release is in [(po \ I) ∩ (W × W) ⊆ ppo].  Together
      with the communication edges these are the generators of [Dc] used by
      both comparisons (Props. mem:prop:rc11 and mem:prop:arm).

      Every lemma of this section abstracts over all of its variables
      ([Proof using All]), so that a user can instantiate them uniformly as
      [lemma Loc dec X HX pre Hadm w]. *)

  Section RCDc.
    Import Cell.Instances.
    Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).
    Abbreviation C := (RC_cfg dec).
    Abbreviation block := (block C).
    Abbreviation I := (mode_indep (C := C)).
    Abbreviation is_rel := (is_rel Loc dec).
    Abbreviation is_acq := (is_acq Loc dec).

    Variable X : cand C.
    Hypothesis HX : wf_cand X.
    Variable pre : relation block.
    Hypothesis Hadm : admissible X I pre.
    Variable w : witness C.

    Abbreviation Dc := (Dc X I w pre).

    Lemma pre0_pre a b : pre0 X I a b -> pre a b.
    Proof using All. destruct Hadm as (H & _ & _). apply H. Qed.

    Lemma acq_po_Dc r x : is_acq r -> po X r x -> Dc r x.
    Proof using All.
      intros Hr Hpo. left. left. left. left. split; [apply is_acq_read; auto |].
      apply t_step. apply pre0_pre. apply pre0_iff; auto.
    Qed.

    Lemma po_rel_Dc a b : po X a b -> is_rel b -> Dc a b.
    Proof using All.
      intros Hpo Hb.
      assert (Hin := po_dom HX _ _ Hpo). destruct Hin as (Hina & _ & _).
      assert (Hpre0 : pre0 X I a b) by (apply pre0_iff; auto).
      destruct (ops_write_or_read C X HX a Hina) as [Hwa | Hra].
      - left. left. left. right. split; auto. split; auto. apply is_rel_write; auto.
      - left. left. left. left. split; auto. apply t_step. apply pre0_pre. exact Hpre0.
    Qed.

    Lemma rfe_Dc u r : rf w u r -> b_tid u <> b_tid r -> Dc u r.
    Proof using All. intros H Ht. left. left. right. split; auto. Qed.

    Lemma mo_Dc a b : mo w a b -> Dc a b.
    Proof using All. intros H. left. right. exact H. Qed.

    Lemma rb_Dc a b : rb X w a b -> Dc a b.
    Proof using All. intros H. right. exact H. Qed.

    (** A read that [pre]-precedes something is [Dc]-before it. *)
    Lemma read_pre_Dc r x : is_read r -> pre r x -> Dc r x.
    Proof using All. intros Hr Hpre. left. left. left. left. split; auto. apply t_step. exact Hpre. Qed.

  End RCDc.

End Consequences.
