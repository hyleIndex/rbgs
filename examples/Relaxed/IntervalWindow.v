(** * Cross-component order for interval components

    For a component specified by interval-linearizability (Castañeda,
    Rajsbaum, Raynal, DISC 2015), an operation occupies an interval of the
    underlay witness rather than a point.  Here the interval of [q] is
    spanned by a designated set [D q] of its own calls (its
    interval-defining calls); nothing requires those calls to be ordered
    among themselves.

    Inheritance becomes: every interval-defining call dominates the
    exported category ([InheritAll]).  Then a same-thread overlay pair of
    different components that the table orders has disjoint, correctly
    ordered intervals ([interval_order]), and likewise for a real-time pair.
    This is the only step of window composition that uses categories; the
    rest (each component's own interval-sequential correctness) is local.

    Part 2: for the latch's racy layer under the default table, the
    update exports [W] only if its interval is spanned by its writes (its
    reads would break it), and a query spanned by its reads exports [R]. *)

From Stdlib Require Import List.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import examples.Relaxed.WindowComposition.
Require Import examples.Relaxed.WindowTable.

Import ListNotations.

Module IntervalWindow.
  Import WindowTable.

  Section Interval.
    Context {Cat : Type} (to : Cat -> Cat -> Prop).
    Context {Op Call Comp : Type}.
    Context (comp_dec : forall c c' : Comp, {c = c'} + {c <> c'}).
    Context (comp : Op -> Comp) (ucomp : Call -> Comp).
    Context (cF : Op -> Cat) (cE : Call -> Cat).
    Context (IFc : Op -> Op -> Prop) (IEc : Call -> Call -> Prop).
    Context (D : Op -> list Call) (pos : Call -> nat).
    Context (ops : list Op) (po rt : Op -> Op -> Prop).

    Definition IF (q q' : Op) : Prop :=
      if comp_dec (comp q) (comp q') then IFc q q' else ~ to (cF q) (cF q').
    Definition IE (u u' : Call) : Prop :=
      if comp_dec (ucomp u) (ucomp u') then IEc u u' else ~ to (cE u) (cE u').

    (** The interval of [q] lies entirely before that of [q']. *)
    Definition before_int (q q' : Op) : Prop :=
      forall u u', In u (D q) -> In u' (D q') -> pos u < pos u'.

    Record Hyps : Prop := {
      h_D_comp : forall q u, In q ops -> In u (D q) -> ucomp u = comp q;
      (* module semantics + relaxed happens-before (ii) of the underlay *)
      h_ord_all : forall q q' u u', In q ops -> In q' ops -> po q q' ->
                    In u (D q) -> In u' (D q') -> ~ IE u u' -> pos u < pos u';
      (* [ret] waits for all handles; relaxed happens-before (i) *)
      h_rt_all : forall q q' u u', In q ops -> In q' ops -> rt q q' ->
                   In u (D q) -> In u' (D q') -> pos u < pos u';
    }.

    Definition InheritAll : Prop :=
      forall q u, In q ops -> In u (D q) ->
        out_le to (cF q) (cE u) /\ in_le to (cF q) (cE u).

    Section WithHyps.
      Context (H : Hyps) (Hinh : InheritAll).

      Lemma cross_reflect_all q q' u u' :
        In q ops -> In q' ops -> comp q <> comp q' ->
        In u (D q) -> In u' (D q') ->
        ~ IF q q' -> ~ IE u u'.
      Proof.
        intros Hq Hq' Hne Hu Hu'. unfold IE, IF.
        rewrite (h_D_comp H q u Hq Hu), (h_D_comp H q' u' Hq' Hu').
        destruct (comp_dec (comp q) (comp q')) as [E|NE]; [contradiction|].
        intros HnnF HnE. apply HnnF. intros HF. apply HnE.
        exact (transfer to _ _ _ _ (proj1 (Hinh q u Hq Hu)) (proj2 (Hinh q' u' Hq' Hu')) HF).
      Qed.

      Theorem interval_order q q' :
        In q ops -> In q' ops -> comp q <> comp q' ->
        (po q q' /\ ~ IF q q') \/ rt q q' -> before_int q q'.
      Proof.
        intros Hq Hq' Hne Hord u u' Hu Hu'.
        destruct Hord as [[Hpo HnIF]|Hrt].
        - apply (h_ord_all H q q' u u'); try assumption.
          apply (cross_reflect_all q q'); assumption.
        - apply (h_rt_all H q q' u u'); assumption.
      Qed.
    End WithHyps.
  End Interval.

  (** ** Part 2: the racy layer of the latch, default table *)

  (** Update spanned by its writes: exports [W]. *)
  Lemma upd_writes_export_W rcsc :
    out_le (dtable rcsc) DW DW /\ in_le (dtable rcsc) DW DW.
  Proof. apply single_window_inherits. Qed.

  (** If the writer's own reads were interval-defining, [W] could not be
      exported: a preceding [wmb] does not order a read. *)
  Lemma upd_reads_break_W rcsc : ~ in_le (dtable rcsc) DW DR.
  Proof. rewrite <- in_leb_spec. destruct rcsc; vm_compute; discriminate. Qed.

  (** Query spanned by its reads: exports [R]. *)
  Lemma query_reads_export_R rcsc :
    out_le (dtable rcsc) DR DR /\ in_le (dtable rcsc) DR DR.
  Proof. apply single_window_inherits. Qed.

  (** The latch's facts on intervals: [wmb] before every write of an
      update, every write before the next [wmb], every read of a query
      before [rmb]. *)
  Lemma latch_interval_facts rcsc :
    dtable rcsc Wmb DW /\ dtable rcsc DW Wmb /\ dtable rcsc DR Rmb.
  Proof. unfold dtable. destruct rcsc; vm_compute; repeat split. Qed.
End IntervalWindow.
