(** * Containment in ARMv8 (Prop. mem:prop:arm)

    On the common fragment (reads and writes with modes rlx/rel and
    rlx/acq, no RMWs, no fences), the ARMv8 axiomatic model is

      obs = rfe ∪ rbe ∪ moe
      dob = addr ∪ data ∪ ctrl;[W] ∪ addr;po;[W] ∪ (ctrl ∪ data);moi ∪ (addr ∪ data);rfi
      bob = [rel];po;[acq] ∪ [acq];po ∪ po;[rel] ∪ po;[rel];moi
      ob  = (obs ∪ dob ∪ bob)⁺

    subject to INTERNAL: acyclic(po_loc ∪ rf ∪ rb ∪ mo) and EXTERNAL:
    acyclic(ob).

    The dependency relations [addr], [data], [ctrl] are data of the
    candidate; each relates a read to a [po]-later operation, and [ctrl] is
    already closed under [po] to the right.  The only assumption about the
    relaxed happens-before [pre] is the wait placement (W),

      dep ; po? ⊆ pre,

    i.e. the source read of a dependency precedes the dependent operation
    and everything [po]-after it.  With [S = [rel];po;[acq]] and
    [bob_0 = bob \ S] we show

      obs ∪ dob ∪ bob_0 ⊆ Dc⁺   and hence   ob ⊆ (Dc ∪ S)⁺,

    so (D1) together with acyclic(Dc ∪ S) implies ARM consistency. *)

Require Import Coq.Lists.List.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Logic.Classical.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Consequences.

Import ListNotations.

Module ARM.

  Import Cell Cell.Instances Decl Consequences.

  Section ARM.
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

    (** ** Dependencies of the candidate *)

    Variables addr data ctrl : relation block.

    Definition dep : relation block := addr ∪ data ∪ ctrl.

    (** Each dependency relates a read to a [po]-later operation.  Only the
        first half is used below: the theorems do not depend on [Hdep_po]
        and are stated without it. *)
    Hypothesis Hdep_read : forall a b, dep a b -> is_read a.
    Hypothesis Hdep_po : forall a b, dep a b -> po X a b.

    (** ** The relaxed happens-before and the wait placement (W) *)

    Variable pre : relation block.
    Hypothesis Hadm : admissible X I pre.

    (** (W): [dep ; po? ⊆ pre]. *)
    Hypothesis HW_dep : forall a b, dep a b -> pre a b.
    Hypothesis HW_dep_po : forall a b c, dep a b -> po X b c -> pre a c.

    Notation Dc := (Dc X I w pre).

    Notation pre0_pre := (Consequences.pre0_pre Loc dec X HX pre Hadm w).
    Notation acq_po_Dc := (Consequences.acq_po_Dc Loc dec X HX pre Hadm w).
    Notation po_rel_Dc := (Consequences.po_rel_Dc Loc dec X HX pre Hadm w).
    Notation rfe_Dc := (Consequences.rfe_Dc Loc dec X HX pre Hadm w).
    Notation mo_Dc := (Consequences.mo_Dc Loc dec X HX pre Hadm w).
    Notation rb_Dc := (Consequences.rb_Dc Loc dec X HX pre Hadm w).
    Notation read_pre_Dc := (Consequences.read_pre_Dc Loc dec X HX pre Hadm w).

    (** ** The ARMv8 relations on the fragment *)

    Definition obs : relation block := rfe X w ∪ rbe X w ∪ moe w.

    Definition dob : relation block :=
      addr ∪ data ∪ (ctrl ;; ⦗ is_write ⦘) ∪ (addr ;; po X ;; ⦗ is_write ⦘)
      ∪ ((ctrl ∪ data) ;; moi w) ∪ ((addr ∪ data) ;; rfi X w).

    (** [S = [rel];po;[acq]], the one barrier-ordered pair that (D2) does
        not see. *)
    Definition S : relation block := ⦗ is_rel ⦘ ;; po X ;; ⦗ is_acq ⦘.

    (** [bob_0 = bob \ S]: the remaining three clauses. *)
    Definition bob0 : relation block :=
      (⦗ is_acq ⦘ ;; po X) ∪ (po X ;; ⦗ is_rel ⦘) ∪ (po X ;; ⦗ is_rel ⦘ ;; moi w).

    Definition bob : relation block := S ∪ bob0.

    Definition ob : relation block := (obs ∪ dob ∪ bob)⁺.

    Definition internal : Prop := acyclic (po_loc X ∪ rf w ∪ rb X w ∪ mo w).
    Definition external : Prop := acyclic ob.
    Definition arm_consistent : Prop := internal /\ external.

    (** ** Dependencies are [Dc] edges

        Every source of [dep] is a read, so by (W)
        [dep ; po? ⊆ [rd];pre ⊆ ppo ⊆ Dc]. *)

    Lemma dep_Dc a b : dep a b -> Dc a b.
    Proof.
      intros H. apply read_pre_Dc; eauto.
    Qed.

    Lemma dep_po_Dc a b c : dep a b -> po X b c -> Dc a c.
    Proof.
      intros H Hpo. apply read_pre_Dc; eauto.
    Qed.

    (** ** The generators *)

    Lemma obs_Dc : obs ⊆ Dc.
    Proof.
      intros a b [[[Hrf Ht] | [Hrb _]] | [Hmo _]].
      - apply rfe_Dc; auto.
      - apply rb_Dc; auto.
      - apply mo_Dc; auto.
    Qed.

    Lemma dob_Dc : dob ⊆ Dc⁺.
    Proof.
      intros a b H.
      destruct H as [[[[[Haddr | Hdata] | [Hctrl Hwb]] | (y & Haddr & Hpo & Hwb)]
                     | (y & Hcd & Hmoi)] | (y & Had & Hrfi)].
      - apply t_step. apply dep_Dc. left. left. exact Haddr.
      - apply t_step. apply dep_Dc. left. right. exact Hdata.
      - apply t_step. apply dep_Dc. right. exact Hctrl.
      - apply t_step. eapply dep_po_Dc; [left; left; exact Haddr | exact Hpo].
      - (* [(ctrl ∪ data) ; moi]: a path of length two *)
        assert (Hd : dep a y) by (destruct Hcd as [H | H]; [right | left; right]; exact H).
        eapply t_trans with (y := y); apply t_step; [apply dep_Dc; exact Hd | apply mo_Dc; apply Hmoi].
      - (* [(addr ∪ data) ; rfi]: internal [rf] is [po_loc], a single edge *)
        assert (Hd : dep a y) by (destruct Had as [H | H]; [left; left | left; right]; exact H).
        destruct Hrfi as [Hrf Ht].
        assert (Hpo : po_loc X y b) by (eapply rfi_po_loc; eauto).
        apply t_step. eapply dep_po_Dc; [exact Hd | apply Hpo].
    Qed.

    Lemma bob0_Dc : bob0 ⊆ Dc⁺.
    Proof.
      intros a b H.
      destruct H as [[[Hacq Hpo] | [Hpo Hrel]] | (y & [Hpo Hrel] & [Hmo Ht])].
      - apply t_step. apply acq_po_Dc; auto.
      - apply t_step. apply po_rel_Dc; auto.
      - eapply t_trans with (y := y); apply t_step; [apply po_rel_Dc; auto | apply mo_Dc; exact Hmo].
    Qed.

    (** ** Prop. mem:prop:arm *)

    Theorem obs_dob_bob0_Dc : obs ∪ dob ∪ bob0 ⊆ Dc⁺.
    Proof.
      intros a b [[H | H] | H].
      - apply t_step. apply obs_Dc. exact H.
      - apply dob_Dc. exact H.
      - apply bob0_Dc. exact H.
    Qed.

    Theorem ob_Dc_S : ob ⊆ (Dc ∪ S)⁺.
    Proof.
      intros a b H.
      apply tc_idem.
      revert a b H. apply tc_incl.
      intros a b H.
      destruct H as [[H | H] | [H | H]].
      - eapply tc_incl; [apply rel_union_incl_l |]. apply obs_dob_bob0_Dc. left. left. exact H.
      - eapply tc_incl; [apply rel_union_incl_l |]. apply obs_dob_bob0_Dc. left. right. exact H.
      - apply t_step. right. exact H.
      - eapply tc_incl; [apply rel_union_incl_l |]. apply obs_dob_bob0_Dc. right. exact H.
    Qed.

    (** (D1) is INTERNAL verbatim, and acyclicity of [Dc ∪ S] gives
        EXTERNAL. *)
    Theorem arm_containment : acyclic (Dc ∪ S) -> arm_consistent.
    Proof.
      intros Hac. split.
      - intros a Ha. apply (HD1 a). refine (tc_incl _ Ha).
        intros x y [[[H | H] | H] | H].
        + left. left. left. exact H.
        + left. left. right. exact H.
        + right. exact H.
        + left. right. exact H.
      - eapply acyclic_incl; [apply ob_Dc_S |]. apply acyclic_tc. exact Hac.
    Qed.

  End ARM.

End ARM.
