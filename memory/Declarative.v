(** * Declarative form under OMCA (Appendix L, Section L.6)

    Execution candidates, witnesses, preserved program order and the two
    consistency axioms (D1), (D2) of Def. mem:def:cand -- Def. mem:def:cons,
    together with the presentation relation of Def. mem:def:present.

    Operations of a candidate are represented by the (flush-free) blocks
    of [memory/Cell.v]: a block already carries thread, location, access
    mode, value and handle, so "presents" (Def. mem:def:present) becomes a
    permutation, and the bijection of the paper is the identity. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Logic.Classical.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import Stdlib.Relations.Relation_Operators.

Require Import models.RelaxedSignature.
Require Import memory.Prelude.
Require Import memory.Cell.

Import ListNotations.

Set Implicit Arguments.

Module Decl.

  Import Cell.

  Section Decl.
    Context (C : Cfg).

    Abbreviation block := (block C).
    Abbreviation cell_op := (cell_op C).
    Abbreviation trace := (trace C).

    (** ** Execution candidates (Def. mem:def:cand) *)

    (** A candidate is a finite set of read and write operations together
        with a program order.  Handles are part of the operations. *)
    Record cand : Type := {
      ops : list block;
      po : relation block;
    }.

    Record wf_cand (X : cand) : Prop := {
      ops_noflush : forall b, In b (ops X) -> ~ is_flush b;
      ops_nodup : NoDup (ops X);
      po_dom : forall a b, po X a b -> In a (ops X) /\ In b (ops X) /\ b_tid a = b_tid b;
      po_irrefl : irreflexive (po X);
      po_trans : forall a b c, po X a b -> po X b c -> po X a c;
      po_total : forall a b,
        In a (ops X) -> In b (ops X) -> b_tid a = b_tid b -> a <> b ->
        po X a b \/ po X b a;
      (** Assumption mem:ass:handles: write handles increase in program order. *)
      po_handles : forall a b, po X a b -> is_write a -> is_write b -> b_handle a < b_handle b;
    }.

    Definition po_loc (X : cand) : relation block :=
      fun a b => po X a b /\ b_loc a = b_loc b.

    Definition WW : relation block :=
      fun a b => is_write a /\ is_write b.

    Definition same_loc : relation block :=
      fun a b => b_loc a = b_loc b.

    (** ** Witnesses *)

    (** A witness is a pair of relations: [mo], a strict total order on the
        writes of each location (the initial write is implicit, least, and
        never mentioned), and [rf], relating a read to the write it reads
        from; a read with no [rf]-source reads the initial value [0]. *)
    Record witness : Type := {
      mo : relation block;
      rf : relation block;
    }.

    Record wf_witness (X : cand) (w : witness) : Prop := {
      mo_dom : forall a b, mo w a b ->
        In a (ops X) /\ In b (ops X) /\ is_write a /\ is_write b /\ b_loc a = b_loc b;
      mo_irrefl : irreflexive (mo w);
      mo_trans : forall a b c, mo w a b -> mo w b c -> mo w a c;
      mo_total : forall a b,
        In a (ops X) -> In b (ops X) -> is_write a -> is_write b ->
        b_loc a = b_loc b -> a <> b -> mo w a b \/ mo w b a;
      rf_dom : forall u r, rf w u r ->
        In u (ops X) /\ In r (ops X) /\ is_write u /\ is_read r /\
        b_loc u = b_loc r /\ b_val u = b_val r;
      rf_func : forall u u' r, rf w u r -> rf w u' r -> u = u';
      rf_init : forall r, In r (ops X) -> is_read r -> (forall u, ~ rf w u r) -> b_val r = 0;
    }.

    Definition rfe (X : cand) (w : witness) : relation block :=
      fun u r => rf w u r /\ b_tid u <> b_tid r.

    Definition rfi (X : cand) (w : witness) : relation block :=
      fun u r => rf w u r /\ b_tid u = b_tid r.

    (** Reads-before: [rb = {(r, w) | (rf(r), w) ∈ mo}], where a read
        without source reads the initial write, which is [mo]-below every
        write at its location. *)
    Definition rb (X : cand) (w : witness) : relation block :=
      fun r u =>
        In r (ops X) /\ In u (ops X) /\ is_read r /\ is_write u /\
        b_loc r = b_loc u /\ (forall u0, rf w u0 r -> mo w u0 u).

    Definition moe (w : witness) : relation block := fun a b => mo w a b /\ b_tid a <> b_tid b.
    Definition moi (w : witness) : relation block := fun a b => mo w a b /\ b_tid a = b_tid b.
    Definition rbe (X : cand) (w : witness) : relation block := fun a b => rb X w a b /\ b_tid a <> b_tid b.
    Definition rbi (X : cand) (w : witness) : relation block := fun a b => rb X w a b /\ b_tid a = b_tid b.

    (** ** Preserved program order (Def. mem:def:ppo) *)

    (** A semi-independence relation on invocations, lifted to blocks. *)
    Definition I_blk (I : cell_op -> cell_op -> Prop) : relation block :=
      fun a b => I (b_inv a) (b_inv b).

    (** The program-level choice [pre_0 = po \ I]. *)
    Definition pre0 (X : cand) (I : cell_op -> cell_op -> Prop) : relation block :=
      po X \ I_blk I.

    (** [pre] is admissible if it contains [po \ I], is acyclic, and only
        relates operations of the candidate. *)
    Definition admissible (X : cand) (I : cell_op -> cell_op -> Prop) (pre : relation block) : Prop :=
      (pre0 X I ⊆ pre) /\ acyclic pre /\
      (forall a b, pre a b -> In a (ops X) /\ In b (ops X)).

    (** [ppo_pre = [rd];pre⁺ ∪ ((po \ I) ∩ (W × W))]. *)
    Definition ppo (X : cand) (I : cell_op -> cell_op -> Prop) (pre : relation block) : relation block :=
      (⦗is_read⦘ ;; pre⁺) ∪ (pre0 X I ∩ WW).

    (** ** OMCA consistency (Def. mem:def:cons) *)

    (** (D1): per-location coherence.  All four relations are
        location-preserving, so a single acyclicity condition is the same
        as one condition per location ([D1_per_loc] below). *)
    Definition coh (X : cand) (w : witness) : relation block :=
      po_loc X ∪ rf w ∪ mo w ∪ rb X w.

    Definition D1 (X : cand) (w : witness) : Prop := acyclic (coh X w).

    (** (D2): the global axiom, with [rfe] rather than [rf]. *)
    Definition Dc (X : cand) (I : cell_op -> cell_op -> Prop) (w : witness) (pre : relation block) : relation block :=
      ppo X I pre ∪ rfe X w ∪ mo w ∪ rb X w.

    Definition D2 (X : cand) (I : cell_op -> cell_op -> Prop) (w : witness) (pre : relation block) : Prop :=
      acyclic (Dc X I w pre).

    Definition consistent (X : cand) (I : cell_op -> cell_op -> Prop) (w : witness) (pre : relation block) : Prop :=
      D1 X w /\ D2 X I w pre.

    (** ** Presentation (Def. mem:def:present) *)

    Definition presents (s : trace) (X : cand) : Prop := Permutation s (ops X).

    Definition respects (s : trace) (pre : relation block) : Prop :=
      forall a b, pre a b -> before s a b.

    (** ** Elementary facts *)

    Lemma coh_same_loc X w (Hw : wf_witness X w) a b : coh X w a b -> b_loc a = b_loc b.
    Proof.
      intros [[[H | H] | H] | H].
      - destruct H. auto.
      - destruct (rf_dom Hw _ _ H) as (_ & _ & _ & _ & Hloc & _). auto.
      - destruct (mo_dom Hw _ _ H) as (_ & _ & _ & _ & Hloc). auto.
      - destruct H as (_ & _ & _ & _ & H & _). auto.
    Qed.

    Lemma tc_same_loc (X : cand) w (Hw : wf_witness X w) a b :
      (coh X w)⁺ a b -> b_loc a = b_loc b.
    Proof.
      intros H. induction H.
      - eapply coh_same_loc; eauto.
      - congruence.
    Qed.

    (** The per-location statement of (D1), as in Def. mem:def:cons. *)
    Definition coh_at (X : cand) (w : witness) (x : Loc C) : relation block :=
      fun a b => coh X w a b /\ b_loc a = x.

    Lemma D1_per_loc X w (Hw : wf_witness X w) :
      D1 X w <-> forall x, acyclic (coh_at X w x).
    Proof.
      split.
      - intros H x. eapply acyclic_incl; [| exact H]. intros a b [Hab _]. exact Hab.
      - intros H a Ha.
        assert (Hin : forall a b, (coh X w)⁺ a b -> (coh_at X w (b_loc a))⁺ a b).
        { intros a' b' Hab. induction Hab as [a' b' Hab | a' b' c' Hab IH1 Hbc IH2].
          - apply t_step. split; auto.
          - eapply t_trans; [exact IH1 |].
            replace (b_loc a') with (b_loc b'); [exact IH2 |].
            symmetry. eapply tc_same_loc; eauto. }
        apply (H (b_loc a) a). apply Hin. exact Ha.
    Qed.

    Lemma pre0_same_loc_po (X : cand) I
      (HI : forall m m', I m m' -> op_loc m <> op_loc m') :
      po_loc X ⊆ pre0 X I.
    Proof.
      intros a b [Hpo Hloc]. split; auto.
      intros Hind. apply (HI _ _ Hind). rewrite !b_loc_inv. auto.
    Qed.

  End Decl.

End Decl.
