(** Relaxed linearizability of complete traces (Def. 2.1 and Def. 3.14).

    A trace is any list whose elements may carry an event of the relaxed
    signature (selected by [sel]); this lets the same definition be used
    for a plain underlay trace, for the underlay part of a module trace,
    and for its overlay part.  Operations are identified by their call key
    [(thread, handle)].  Only complete traces are treated: every invoked
    operation is required to appear in the witness, and the append/drop
    convention for pending operations is not needed. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Relations.Relation_Definitions.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.

Import ListNotations.


Module RelaxedTraceLin.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.

  (** A complete operation: its key, its operation and its result. *)
  Record Op (E : RelaxedSig.t) : Type := {
    op_key : CallKey E;
    op_op : Sig.op (RelaxedSig.effect E);
    op_ret : Sig.ar op_op;
  }.

  Arguments Op _ : clear implicits.
  Arguments Build_Op {E} _ _ _.
  Arguments op_key {E} _.
  Arguments op_op {E} _.
  Arguments op_ret {E} _.

  (** [before W o o']: [o] occurs strictly before [o'] in the sequential
      witness [W]. *)
  Definition before {A : Type} (W : list A) (a b : A) : Prop :=
    exists l1 l2, W = l1 ++ a :: l2 /\ In b l2.

  Section Trace.
    Context {E : RelaxedSig.t}.
    Context {X : Type} (sel : X -> option (ThreadEvent E)) (L : list X).

    Definition inv_at (i : nat) (k : CallKey E) (op : Sig.op (RelaxedSig.effect E)) : Prop :=
      exists x, nth_error L i = Some x /\
        sel x = Some (Build_ThreadEvent (fst k) (InvEv (snd k) op)).

    Definition res_at (i : nat) (k : CallKey E) (op : Sig.op (RelaxedSig.effect E))
        (ret : Sig.ar op) : Prop :=
      exists x, nth_error L i = Some x /\
        sel x = Some (Build_ThreadEvent (fst k) (ResEv (snd k) op ret)).

    (** Def. 2.1: relaxed happens-before, relative to a semi-independence
        relation [indep] on invocations. *)
    Definition rhb (indep : relation (Sig.op (RelaxedSig.effect E))) (o o' : Op E) : Prop :=
      (exists i j, res_at i (op_key o) (op_op o) (op_ret o) /\
                   inv_at j (op_key o') (op_op o') /\ i < j) \/
      (fst (op_key o) = fst (op_key o') /\
       exists i j, inv_at i (op_key o) (op_op o) /\ inv_at j (op_key o') (op_op o') /\
                   i < j /\ ~ indep (op_op o) (op_op o')).

    Definition occurs (o : Op E) : Prop :=
      (exists i, inv_at i (op_key o) (op_op o)) /\
      (exists j, res_at j (op_key o) (op_op o) (op_ret o)).

    (** Def. 3.14 for complete traces: a sequential witness in [nu] that
        contains exactly the operations of the trace, once each, and
        preserves relaxed happens-before. *)
    Definition rel_lin_witness (indep : relation (Sig.op (RelaxedSig.effect E)))
        (nu : list (Op E) -> Prop) (W : list (Op E)) : Prop :=
      nu W /\
      NoDup (map op_key W) /\
      (forall o, In o W -> occurs o) /\
      (forall i k op, inv_at i k op -> exists o, In o W /\ op_key o = k) /\
      (forall o o', In o W -> In o' W -> rhb indep o o' -> before W o o').

    Definition rel_lin (indep : relation (Sig.op (RelaxedSig.effect E)))
        (nu : list (Op E) -> Prop) : Prop :=
      exists W, rel_lin_witness indep nu W.

    Lemma rhb_mono (indep1 indep2 : relation (Sig.op (RelaxedSig.effect E))) o o' :
      (forall a b, indep1 a b -> indep2 a b) ->
      rhb indep2 o o' -> rhb indep1 o o'.
    Proof.
      intros Hsub [H | (Ht & i & j & Hi & Hj & Hij & Hn)]; [left; exact H |].
      right. split; [exact Ht |]. exists i, j. split; [exact Hi |]. split; [exact Hj |].
      split; [exact Hij |]. intro H1. apply Hn. apply Hsub. exact H1.
    Qed.

    (** A witness for the empty semi-independence relation (the strongest
        order constraints) is a witness for every relation. *)
    Lemma rel_lin_mono (indep1 indep2 : relation (Sig.op (RelaxedSig.effect E))) nu :
      (forall a b, indep1 a b -> indep2 a b) ->
      rel_lin indep1 nu -> rel_lin indep2 nu.
    Proof.
      intros Hsub (W & Hnu & Hnd & Hocc & Hall & Hord).
      exists W. split; [exact Hnu |]. split; [exact Hnd |]. split; [exact Hocc |].
      split; [exact Hall |].
      intros o o' Ho Ho' Hr. apply Hord; auto. eapply rhb_mono; eauto.
    Qed.

    Lemma rel_lin_empty_indep indep nu :
      rel_lin (fun _ _ => False) nu -> rel_lin indep nu.
    Proof. apply rel_lin_mono. intros a b []. Qed.

  End Trace.

  (** Relaxed linearizability is invariant under relabelling the trace
      elements, as long as the selector is adjusted. *)
  Section Map.
    Context {E : RelaxedSig.t} {X Y : Type} (f : X -> Y).
    Context (sel : Y -> option (ThreadEvent E)) (L : list X).

    Lemma inv_at_map i k op :
      inv_at sel (map f L) i k op <-> inv_at (fun x => sel (f x)) L i k op.
    Proof.
      unfold inv_at. rewrite nth_error_map. split.
      - intros (y & Hy & Hs). destruct (nth_error L i) as [x |]; cbn in Hy; [| discriminate].
        injection Hy as <-. exists x. split; [reflexivity | exact Hs].
      - intros (x & Hx & Hs). rewrite Hx. exists (f x). split; [reflexivity | exact Hs].
    Qed.

    Lemma res_at_map i k op ret :
      res_at sel (map f L) i k op ret <-> res_at (fun x => sel (f x)) L i k op ret.
    Proof.
      unfold res_at. rewrite nth_error_map. split.
      - intros (y & Hy & Hs). destruct (nth_error L i) as [x |]; cbn in Hy; [| discriminate].
        injection Hy as <-. exists x. split; [reflexivity | exact Hs].
      - intros (x & Hx & Hs). rewrite Hx. exists (f x). split; [reflexivity | exact Hs].
    Qed.

    Lemma occurs_map o : occurs sel (map f L) o <-> occurs (fun x => sel (f x)) L o.
    Proof.
      unfold occurs. split; intros [(i & Hi) (j & Hj)]; split.
      - exists i. apply inv_at_map. exact Hi.
      - exists j. apply res_at_map. exact Hj.
      - exists i. apply inv_at_map. exact Hi.
      - exists j. apply res_at_map. exact Hj.
    Qed.

    Lemma rhb_map indep o o' :
      rhb sel (map f L) indep o o' <-> rhb (fun x => sel (f x)) L indep o o'.
    Proof.
      unfold rhb. split.
      - intros [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + left. exists i, j. rewrite <- res_at_map, <- inv_at_map. auto.
        + right. split; [exact Ht |]. exists i, j. rewrite <- !inv_at_map. auto.
      - intros [(i & j & Hi & Hj & Hij) | (Ht & i & j & Hi & Hj & Hij & Hn)].
        + left. exists i, j. rewrite res_at_map, inv_at_map. auto.
        + right. split; [exact Ht |]. exists i, j. rewrite !inv_at_map. auto.
    Qed.

    Lemma rel_lin_witness_map indep nu W :
      rel_lin_witness sel (map f L) indep nu W <->
      rel_lin_witness (fun x => sel (f x)) L indep nu W.
    Proof.
      unfold rel_lin_witness. split; intros (Hnu & Hnd & Hocc & Hall & Hord).
      - split; [exact Hnu |]. split; [exact Hnd |]. split; [| split].
        + intros o Ho. apply occurs_map, Hocc, Ho.
        + intros i k op Hi. apply (Hall i k op). apply inv_at_map, Hi.
        + intros o o' Ho Ho' Hr. apply Hord; [exact Ho | exact Ho' | apply rhb_map, Hr].
      - split; [exact Hnu |]. split; [exact Hnd |]. split; [| split].
        + intros o Ho. apply occurs_map, Hocc, Ho.
        + intros i k op Hi. apply (Hall i k op). apply inv_at_map, Hi.
        + intros o o' Ho Ho' Hr. apply Hord; [exact Ho | exact Ho' | apply rhb_map, Hr].
    Qed.

    Lemma rel_lin_map indep nu :
      rel_lin sel (map f L) indep nu <-> rel_lin (fun x => sel (f x)) L indep nu.
    Proof.
      unfold rel_lin. split; intros (W & HW); exists W; apply rel_lin_witness_map; exact HW.
    Qed.
  End Map.

End RelaxedTraceLin.
