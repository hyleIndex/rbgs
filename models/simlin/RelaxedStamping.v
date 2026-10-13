(** * Relaxed linearizability as an rhb-monotone stamping

    A stamping of a complete relaxed trace assigns a natural number to
    each operation.  It must admit a witness that lists the operations in
    strictly increasing stamp order, is legal for the specification, and
    increases the stamp along every relaxed-happens-before edge
    (Def. 2.1).  [rel_lin_iff_rhb_stamping] shows that such a stamping
    exists exactly when the trace is relaxed linearizable in the sense of
    [RelaxedTraceLin.rel_lin].

    The equivalence is close to a restatement of [rel_lin]: from a
    witness, take the stamp of an operation to be its position in the
    witness.  The stamps are chosen after the whole trace is known.  So
    this is not a view in the sense of view-based models, and not the
    incremental view of [models/view/ViewLift.v], whose stamps are fixed
    when an operation responds and whose reads can only look at the
    past.  For example, load buffering on COH has an rhb-monotone stamping
    (its relaxed trace overlaps the late read with the other thread's
    write), but no run of an incremental view produces it.

    What the file does contribute: only the order of stamps matters
    ([stamped_witness_retime], P2), and monotonicity along rhb edges is
    all that is needed.  The overlay order of [WindowLink.Positional]
    (stamp = position of the linearizing call in the underlay witness) is
    such a stamping. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Import ListNotations.

Module RelaxedStamping.
  Import RelaxedSig RelaxedLTSSpec RelaxedTraceLin.

  Section Stamping.
    Context {E : RelaxedSig.t} {X : Type} (sel : X -> option (ThreadEvent E)) (L : list X).
    Context (indep : relation (Sig.op (RelaxedSig.effect E))) (nu : list (Op E) -> Prop).
    Context (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).

    Definition stamped_witness (H : Op E -> nat) (W : list (Op E)) : Prop :=
      nu W /\
      NoDup (map op_key W) /\
      (forall o, In o W -> occurs sel L o) /\
      (forall i k op, inv_at sel L i k op -> exists o, In o W /\ op_key o = k) /\
      StronglySorted (fun o o' => H o < H o') W /\
      (forall o o', In o W -> In o' W -> rhb sel L indep o o' -> H o < H o').

    Definition rhb_stamping : Prop := exists H W, stamped_witness H W.

    (** ** From a stamping to a witness *)

    Lemma sorted_before (H : Op E -> nat) W o o' :
      StronglySorted (fun a b => H a < H b) W -> In o W -> In o' W -> H o < H o' -> before W o o'.
    Proof.
      induction W as [|a W IH]; intros HS Ho Ho' Hlt; [destruct Ho|].
      apply StronglySorted_inv in HS as [HS HF].
      destruct Ho as [Ha | Ho].
      - subst a. destruct Ho' as [Ha' | Ho']; [subst o'; lia|].
        exists [], W. split; [reflexivity | exact Ho'].
      - destruct Ho' as [Ha' | Ho'].
        + subst a. rewrite Forall_forall in HF. specialize (HF o Ho). lia.
        + destruct (IH HS Ho Ho' Hlt) as (l1 & l2 & HW & Hin). rewrite HW.
          exists (a :: l1), l2. split; [reflexivity | exact Hin].
    Qed.

    Lemma rhb_stamping_rel_lin : rhb_stamping -> rel_lin sel L indep nu.
    Proof.
      intros (H & W & Hnu & Hnd & Hocc & Hall & HS & Hrhb).
      exists W. refine (conj Hnu (conj Hnd (conj Hocc (conj Hall _)))).
      intros x y Hx Hy Hr. apply (sorted_before H); auto.
    Qed.

    (** ** From a witness to a stamping: the stamp is the position of the key *)

    Fixpoint index (k : CallKey E) (l : list (CallKey E)) : nat :=
      match l with
      | [] => 0
      | k' :: l' => if key_dec k k' then 0 else S (index k l')
      end.

    Lemma index_app_cons k l1 l2 :
      ~ In k l1 -> index k (l1 ++ k :: l2) = length l1.
    Proof.
      induction l1 as [|a l1 IH]; simpl; intros Hn.
      - destruct (key_dec k k); [reflexivity | congruence].
      - destruct (key_dec k a) as [-> | Hne]; [exfalso; apply Hn; left; reflexivity|].
        f_equal. apply IH. intros Hin. apply Hn. right. exact Hin.
    Qed.

    Definition pos (W : list (Op E)) (o : Op E) : nat := index (op_key o) (map op_key W).

    Lemma pos_split W l1 o l2 :
      NoDup (map op_key W) -> W = l1 ++ o :: l2 -> pos W o = length l1.
    Proof.
      intros Hnd ->. unfold pos. rewrite map_app. simpl.
      rewrite map_app in Hnd. simpl in Hnd.
      apply NoDup_remove_2 in Hnd.
      rewrite index_app_cons; [apply length_map|].
      intros Hin. apply Hnd. apply in_or_app. left. exact Hin.
    Qed.

    Lemma before_pos W o o' :
      NoDup (map op_key W) -> before W o o' -> pos W o < pos W o'.
    Proof.
      intros Hnd (l1 & l2 & HW & Hin).
      rewrite (pos_split W l1 o l2 Hnd HW).
      apply in_split in Hin as (m1 & m2 & ->).
      assert (HW' : W = (l1 ++ o :: m1) ++ o' :: m2) by (rewrite HW, <- app_assoc; reflexivity).
      rewrite (pos_split W (l1 ++ o :: m1) o' m2 Hnd HW').
      rewrite length_app. simpl. lia.
    Qed.

    Lemma sorted_pos W :
      NoDup (map op_key W) -> StronglySorted (fun a b => pos W a < pos W b) W.
    Proof.
      intros Hnd.
      assert (Hgen : forall l1 l2, W = l1 ++ l2 -> StronglySorted (fun a b => pos W a < pos W b) l2).
      { intros l1 l2. revert l1. induction l2 as [|a l2 IH]; intros l1 HW; [constructor|].
        constructor.
        - apply (IH (l1 ++ [a])). rewrite HW, <- app_assoc. reflexivity.
        - apply Forall_forall. intros b Hb. apply before_pos; [exact Hnd|].
          exists l1, l2. split; [exact HW | exact Hb]. }
      exact (Hgen [] W eq_refl).
    Qed.

    Lemma rel_lin_rhb_stamping : rel_lin sel L indep nu -> rhb_stamping.
    Proof.
      intros (W & Hnu & Hnd & Hocc & Hall & Hord).
      exists (pos W), W.
      refine (conj Hnu (conj Hnd (conj Hocc (conj Hall (conj (sorted_pos W Hnd) _))))).
      intros x y Hx Hy Hr. apply before_pos; [exact Hnd|]. apply Hord; assumption.
    Qed.

    Theorem rel_lin_iff_rhb_stamping : rel_lin sel L indep nu <-> rhb_stamping.
    Proof. split; [apply rel_lin_rhb_stamping | apply rhb_stamping_rel_lin]. Qed.

    (** Only the order of timestamps matters: a strictly monotone
        re-timestamping preserves a stamping (P2). *)
    Lemma stamped_witness_retime (H : Op E -> nat) (phi : nat -> nat) W :
      (forall a b, a < b -> phi a < phi b) ->
      stamped_witness H W -> stamped_witness (fun o => phi (H o)) W.
    Proof.
      intros Hphi (Hnu & Hnd & Hocc & Hall & HS & Hrhb).
      refine (conj Hnu (conj Hnd (conj Hocc (conj Hall (conj _ _))))).
      - clear -HS Hphi. induction HS as [|a l HS IH HF]; constructor; [exact IH|].
        eapply Forall_impl; [|exact HF]. intros b Hab. apply Hphi. exact Hab.
      - intros x y Hx Hy Hr. apply Hphi. apply Hrhb; assumption.
    Qed.
  End Stamping.
End RelaxedStamping.
