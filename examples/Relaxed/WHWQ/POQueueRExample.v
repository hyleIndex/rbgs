(** * POQueueRExample: concrete traces of [POQueueR], and the single-thread B6 example

    Task WHWQ (.rocq-review/tasks/WHWQ.md), review gate 1, findings
    WHWQ-m-5, WHWQ-m-6 (iteration 1) and WHWQ-m-8 (iteration 2)
    (.rocq-review/latest-review.md).  The theorem
    [POQueueRSound.poqr_sound] is universal; this file shows that it is not
    vacuous, that it needs [I(enq, deq)], and that the per-thread condition
    of [POQueueR] is needed.  It also proves the reviewer's single-thread
    example (Review B, B6) for the blocking queue specification.

    ** Results (all over [FQ positive], except the generic B6 theorem)

    - Future-dependent order ([future_dependent]).  Two complete traces
      [Tf 1] and [Tf 2] share the prefix "t1 invokes enq 1; t2 invokes
      enq 2; t2 returns; t1 returns" and differ only in the value returned
      by a later dequeue of t3.  Both are paths of [POQueueR], hence
      relaxed-linearizable ([poqr_sound]).  Every witness of [Tf 1] orders
      enq 1 before enq 2, every witness of [Tf 2] orders enq 2 before
      enq 1: the order of the two overlapping enqueues is decided by the
      future dequeue.
    - [I(enq, deq)] is needed ([T0_needs_qsi]).  The 10-event trace [T0]
      (thread 1 dequeues while its own enqueue is pending) is a complete,
      well-formed path of [POQueueR]; it is relaxed-linearizable under
      [I(enq, deq)] (by [poqr_sound]) and not under the empty relation.
      So [POQueueR] is not a sound presentation for [(νQ, ∅)].
    - The per-thread condition [Hidle] of [POQueueR] is needed ([Tk_*]).
      The trace [Tk] (thread 1 overlaps two of its own enqueues; a
      dequeue returns the younger value) is complete and well-formed, is
      not relaxed-linearizable under [I(enq, deq)], and is not a path of
      [POQueueR].  A call-keyed variant of [POQueueR] without the
      per-thread condition would accept it; that variant is not defined
      here (the claim is by inspection of its rules, cf. the bounded check
      of the background note).
    - B6 ([b6_enq_deq], [b6_returns]; generic in the value type).  For any
      trace whose only calls are [enq v] (key [(t, h1)]) and [deq] (key
      [(t, h2)]) of one thread [t], every relaxed-linearization witness
      under [I(enq, deq)] is exactly [enq v; deq -> v], and on a
      well-formed trace the dequeue returns [v].  Dropping the
      (enq, deq) program-order edge does not let the dequeue fail or
      return anything else, because the dequeue of [δQ] blocks.  These
      are statements about the specification [(νQ, I(enq, deq))]; the
      implementation-level corollary (the WHW code returns [v]) is
      [WHWQTop.whw_b6], from T6 ([WHWQTop.whw_rel_lin]).  [b6_enq_deq]
      does not use the [rhb] part of the witness, so it holds for every
      relation (review WHWQ-g5-2).
      Instances: [Tb6] (sequential; a path of [POQueueR]; real time
      already orders the two calls) and [Tb6ov] ([Tb6ov_b6]: the
      dequeue is invoked while the enqueue is pending and returns first,
      so no [rhb] edge relates the two calls ([Tb6ov_no_rhb]) and only
      the blocking [δQ] forces the enqueue first; [Tb6ov] is not a path
      of [POQueueR], and its witness is given directly).
    - [POQueueR] is not a complete presentation ([POQueueR_incomplete],
      [POQueueR_not_complete_pres]): the trace [Tinc] (two overlapping
      enqueues of one thread) is complete, well-formed and
      relaxed-linearizable, and [POQueueR] rejects it.

    No axiom is used ([Print Assumptions]; task log). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.FSets.FMapPositive.
Require Import Stdlib.micromega.Lia.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.view.ViewLHL.
Require Import models.simlin.RelaxedHoareSpec.
Require Import examples.Relaxed.WHWQ.WHWQSpec.
Require Import examples.Relaxed.WHWQ.POQueueR.
Require Import examples.Relaxed.WHWQ.POQueueRWitness.
Require Import examples.Relaxed.WHWQ.POQueueRSound.

Import ListNotations.

Module POQueueRExample.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import WHWQSpec.
  Import POQueueR.

  (** ** List facts *)

  Section Lists.
    Context {B : Type}.

    Lemma pivot_suffix (p1 p2 q1 q2 : list B) b :
      NoDup (p1 ++ b :: p2) -> p1 ++ b :: p2 = q1 ++ b :: q2 -> p2 = q2.
    Proof.
      revert q1. induction p1 as [| c p1 IH]; intros q1 Hnd Heq; destruct q1 as [| d q1]; cbn in Hnd, Heq.
      - injection Heq as Heq. exact Heq.
      - injection Heq as Hbd Heq. subst d. apply NoDup_cons_iff in Hnd as [Hb _].
        exfalso. apply Hb. rewrite Heq. apply in_or_app. right. left. reflexivity.
      - injection Heq as Hcb Heq. subst c. apply NoDup_cons_iff in Hnd as [Hb _].
        exfalso. apply Hb. apply in_or_app. right. left. reflexivity.
      - injection Heq as Hcd Heq. subst d. apply NoDup_cons_iff in Hnd as [_ Hnd]. exact (IH q1 Hnd Heq).
    Qed.

    Lemma before_trans (l : list B) a b c : NoDup l -> before l a b -> before l b c -> before l a c.
    Proof.
      intros Hnd (l1 & l2 & Hl & Hb) (m1 & m2 & Hm & Hc).
      apply in_split in Hb as (n1 & n2 & ->). subst l.
      exists l1, (n1 ++ b :: n2). split; [reflexivity |].
      assert (H2 : m2 = n2).
      { apply (pivot_suffix m1 m2 (l1 ++ a :: n1) n2 b); [rewrite <- Hm; exact Hnd |].
        rewrite <- Hm, <- app_assoc. reflexivity. }
      subst m2. apply in_or_app. right. right. exact Hc.
    Qed.

    Lemma before_total (l : list B) a b : In a l -> In b l -> a <> b -> before l a b \/ before l b a.
    Proof.
      induction l as [| x l IH]; intros Ha Hb Hab; [destruct Ha |].
      destruct Ha as [Ha | Ha], Hb as [Hb | Hb].
      - subst. contradiction.
      - subst x. left. apply POQueueRWitness.before_cons_hd. exact Hb.
      - subst x. right. apply POQueueRWitness.before_cons_hd. exact Ha.
      - destruct (IH Ha Hb Hab) as [H | H]; [left | right]; apply POQueueRWitness.before_cons_tl; exact H.
    Qed.

    Lemma nodup_app_disj (l1 l2 : list B) a : NoDup (l1 ++ l2) -> In a l1 -> In a l2 -> False.
    Proof.
      intros Hnd H1 H2. apply in_split in H1 as (p1 & p2 & ->). rewrite <- app_assoc in Hnd. cbn in Hnd.
      apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. right. apply in_or_app. right. exact H2.
    Qed.

    Lemma all_eq_singleton (l : list B) a : NoDup l -> In a l -> (forall x, In x l -> x = a) -> l = [a].
    Proof.
      intros Hnd Ha Hall. destruct l as [| x l]; [destruct Ha |].
      assert (x = a) as -> by (apply Hall; left; reflexivity).
      destruct l as [| y l]; [reflexivity |].
      exfalso. assert (y = a) as -> by (apply Hall; right; left; reflexivity).
      apply NoDup_cons_iff in Hnd as [Hn _]. apply Hn. left. reflexivity.
    Qed.

    Lemma none_nil (l : list B) : (forall x, In x l -> False) -> l = [].
    Proof. destruct l as [| x l]; [reflexivity |]. intros H. exfalso. apply (H x). left. reflexivity. Qed.

    Lemma nodup_map_eq {C : Type} (f : B -> C) (l : list B) x y :
      NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
    Proof.
      induction l as [| z l IH]; cbn; intros Hnd Hx Hy Hf; [destruct Hx |].
      apply NoDup_cons_iff in Hnd as [Hz Hnd].
      destruct Hx as [Hx | Hx], Hy as [Hy | Hy].
      - subst. reflexivity.
      - subst z. exfalso. apply Hz. rewrite Hf. apply in_map. exact Hy.
      - subst z. exfalso. apply Hz. rewrite <- Hf. apply in_map. exact Hx.
      - exact (IH Hnd Hx Hy Hf).
    Qed.
  End Lists.

  (** ** FIFO facts and trace inspection (generic in the value type) *)

  Section Fifo.
    Context {A : Type}.

    Local Abbreviation F := (FQ A).
    Local Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Local Abbreviation res L := (res_at (@PrefixView.sel F) L).
    Local Abbreviation run := (@RelaxedHoareSpec.seq_run F (list A) (δQ A)).

    Definition enq_val (o : Op F) : option A :=
      match op_op o with enq v => Some v | deq => None end.

    Definition deq_ret (o : Op F) : option A :=
      match o with
      | Build_Op _ op r =>
          match op as op0 return Sig.ar op0 -> option A with
          | enq _ => fun _ => None
          | deq => fun r => Some r
          end r
      end.

    Lemma run_cons_inv q o W q' :
      run q (o :: W) q' -> exists q1, δQ A q (op_op o) (op_ret o) q1 /\ run q1 W q'.
    Proof. intros H. inversion H; subst. eexists. split; eassumption. Qed.

    Lemma run_app_inv q W1 W2 q' : run q (W1 ++ W2) q' -> exists m, run q W1 m /\ run m W2 q'.
    Proof.
      revert q. induction W1 as [| o W1 IH]; intros q H; cbn in H.
      - exists q. split; [constructor | exact H].
      - destruct (run_cons_inv _ _ _ _ H) as (q1 & Hd & Hr). destruct (IH q1 Hr) as (m & H1 & H2).
        exists m. split; [econstructor; [exact Hd | exact H1] | exact H2].
    Qed.

    Lemma run_enq q (k : CallKey F) v (r : unit) W q' :
      run q (Build_Op k (enq v) r :: W) q' -> run (q ++ [v]) W q'.
    Proof. intros H. destruct (run_cons_inv _ _ _ _ H) as (q1 & Hd & Hr). cbn in Hd. subst q1. exact Hr. Qed.

    (** A value in the final queue was in the initial queue or enqueued. *)
    Lemma fifo_src q W q' y : run q W q' -> In y q' -> In y q \/ exists o, In o W /\ enq_val o = Some y.
    Proof.
      induction 1 as [q | q o q1 W q2 Hd Hr IH]; intros Hy; [left; exact Hy |].
      destruct (IH Hy) as [H1 | (o' & Ho' & Hv)]; [| right; exists o'; split; [right; exact Ho' | exact Hv]].
      destruct o as [k op r]. destruct op as [v |]; cbn in Hd.
      - subst q1. apply in_app_or in H1 as [H1 | [Hvy | []]]; [left; exact H1 |].
        right. eexists. split; [left; reflexivity | cbn; rewrite Hvy; reflexivity].
      - subst q. left. right. exact H1.
    Qed.

    (** A value that is never enqueued and not initially present is never
        dequeued. *)
    Lemma fifo_absent q W q' y :
      run q W q' -> ~ In y q -> (forall o, In o W -> enq_val o <> Some y) ->
      forall o, In o W -> deq_ret o <> Some y.
    Proof.
      induction 1 as [q | q o q1 W q2 Hd Hr IH]; intros Hy Hne o' Ho'; [destruct Ho' |].
      destruct o as [k op r]. destruct op as [v |]; cbn in Hd.
      - subst q1. destruct Ho' as [<- | Ho']; [cbn; discriminate |].
        apply IH; [| intros o'' Ho''; apply Hne; right; exact Ho'' | exact Ho'].
        intros Hin. apply in_app_or in Hin as [Hin | [Hv | []]]; [exact (Hy Hin) |].
        apply (Hne (Build_Op k (enq v) r)); [left; reflexivity | cbn; rewrite Hv; reflexivity].
      - subst q. destruct Ho' as [<- | Ho'].
        + cbn. intros Hr'. injection Hr' as ->. apply Hy. left. reflexivity.
        + apply IH; [intros Hin; apply Hy; right; exact Hin | intros o'' Ho''; apply Hne; right; exact Ho'' | exact Ho'].
    Qed.

    (** FIFO: while [x] is in the queue ahead of every [y], and [x] is not
        dequeued, no [y] is dequeued. *)
    Lemma fifo_ahead q W q' x y :
      run q W q' -> (exists l1 l2, q = l1 ++ x :: l2 /\ ~ In y l1) ->
      (forall o, In o W -> deq_ret o <> Some x) ->
      forall o, In o W -> deq_ret o <> Some y.
    Proof.
      induction 1 as [q | q o q1 W q2 Hd Hr IH]; intros (l1 & l2 & Hq & Hy) Hnd o' Ho'; [destruct Ho' |].
      destruct o as [k op r]. destruct op as [v |]; cbn in Hd.
      - subst q1. destruct Ho' as [<- | Ho']; [cbn; discriminate |].
        apply IH; [| intros o'' Ho''; apply Hnd; right; exact Ho'' | exact Ho'].
        exists l1, (l2 ++ [v]). split; [rewrite Hq, <- app_assoc; reflexivity | exact Hy].
      - subst q. destruct l1 as [| z l1]; cbn in Hq.
        + injection Hq as -> _. exfalso. apply (Hnd (Build_Op k deq x)); [left; reflexivity | reflexivity].
        + injection Hq as -> Hq. destruct Ho' as [<- | Ho'].
          * cbn. intros Hz. injection Hz as ->. apply Hy. left. reflexivity.
          * apply IH; [| intros o'' Ho''; apply Hnd; right; exact Ho'' | exact Ho'].
            exists l1, l2. split; [exact Hq | intros H; apply Hy; right; exact H].
    Qed.

    (** If [oX] enqueues [x] before [oY], the only enqueue of [y], and [x]
        is never dequeued, then [y] is never dequeued. *)
    Lemma fifo_order W (oX oY : Op F) x y :
      νQ A W -> NoDup W -> before W oX oY -> enq_val oX = Some x -> x <> y ->
      (forall o, In o W -> enq_val o = Some y -> o = oY) ->
      (forall o, In o W -> deq_ret o <> Some x) ->
      forall o, In o W -> deq_ret o <> Some y.
    Proof.
      intros (s & Hs) Hnd (W1 & W2 & HW & HY) HX Hxy Huniq Hnx. subst W.
      apply run_app_inv in Hs as (q1 & H1 & H2).
      destruct oX as [kX opX rX]. destruct opX as [vX |]; cbn in HX; [| discriminate HX].
      injection HX as ->. apply run_enq in H2.
      assert (HY1 : ~ In oY W1) by (intros Hin; exact (nodup_app_disj W1 _ oY Hnd Hin (or_intror HY))).
      assert (Hy1 : ~ In y q1).
      { intros Hin. destruct (fifo_src _ _ _ _ H1 Hin) as [[] | (o & Ho & Hv)].
        apply HY1. rewrite <- (Huniq o (in_or_app _ _ _ (or_introl Ho)) Hv). exact Ho. }
      intros o Ho. apply in_app_or in Ho as [Ho | [<- | Ho]].
      - apply (fifo_absent _ _ _ _ H1); [intros [] | | exact Ho].
        intros o' Ho' Hv. apply HY1. rewrite <- (Huniq o' (in_or_app _ _ _ (or_introl Ho')) Hv). exact Ho'.
      - cbn. discriminate.
      - apply (fifo_ahead _ _ _ x y H2); [| intros o' Ho'; apply Hnx; apply in_or_app; right; right; exact Ho' | exact Ho].
        exists q1, []. split; [reflexivity | exact Hy1].
    Qed.

    (** Trace inspection: the invocations and responses of a trace, by
        position, key and operation. *)
    Fixpoint invs_from (n : nat) (L : list (ThreadEvent F)) : list (nat * CallKey F * QOp A) :=
      match L with
      | [] => []
      | e :: L' =>
          match te_ev F e with
          | InvEv h o => (n, (te_tid F e, h), o) :: invs_from (S n) L'
          | ResEv _ _ _ => invs_from (S n) L'
          end
      end.

    Fixpoint ress_from (n : nat) (L : list (ThreadEvent F)) : list (nat * CallKey F * QOp A) :=
      match L with
      | [] => []
      | e :: L' =>
          match te_ev F e with
          | InvEv _ _ => ress_from (S n) L'
          | ResEv h o _ => (n, (te_tid F e, h), o) :: ress_from (S n) L'
          end
      end.

    Lemma invs_from_spec n L i k op : inv L i k op -> In (n + i, k, op) (invs_from n L).
    Proof.
      revert n i. induction L as [| e L IH]; intros n i (x & Hx & Hs); [destruct i; discriminate |].
      unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct i as [| i]; cbn in Hx.
      - injection Hx as ->. cbn. left. rewrite Nat.add_0_r. destruct k. reflexivity.
      - rewrite Nat.add_succ_r. cbn. destruct (te_ev F e).
        + right. apply (IH (S n) i). eexists. split; [exact Hx | reflexivity].
        + apply (IH (S n) i). eexists. split; [exact Hx | reflexivity].
    Qed.

    Lemma ress_from_spec n L j k op (r : Sig.ar op) : res L j k op r -> In (n + j, k, op) (ress_from n L).
    Proof.
      revert n j. induction L as [| e L IH]; intros n j (x & Hx & Hs); [destruct j; discriminate |].
      unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct j as [| j]; cbn in Hx.
      - injection Hx as ->. cbn. left. rewrite Nat.add_0_r. destruct k. reflexivity.
      - rewrite Nat.add_succ_r. cbn. destruct (te_ev F e).
        + apply (IH (S n) j). eexists. split; [exact Hx | reflexivity].
        + right. apply (IH (S n) j). eexists. split; [exact Hx | reflexivity].
    Qed.

    Lemma inv_entry L i k op : inv L i k op -> In (i, k, op) (invs_from 0 L).
    Proof. exact (invs_from_spec 0 L i k op). Qed.

    Lemma res_entry L j k op (r : Sig.ar op) : res L j k op r -> In (j, k, op) (ress_from 0 L).
    Proof. exact (ress_from_spec 0 L j k op r). Qed.

    Definition deq_ret_at (L : list (ThreadEvent F)) (j : nat) : option A :=
      match nth_error L j with
      | Some e =>
          match te_ev F e with
          | ResEv _ o r =>
              match o as o0 return Sig.ar o0 -> option A with
              | enq _ => fun _ => None
              | deq => fun r => Some r
              end r
          | InvEv _ _ => None
          end
      | None => None
      end.

    Lemma res_deq_ret L j k (r : A) : res L j k deq r -> deq_ret_at L j = Some r.
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      unfold deq_ret_at. rewrite Hx. reflexivity.
    Qed.

    Lemma wf_of_entries L :
      NoDup (map (fun e => snd (fst e)) (invs_from 0 L)) ->
      NoDup (map (fun e => snd (fst e)) (ress_from 0 L)) ->
      Forall (fun e => exists i, i < fst (fst e) /\ inv L i (snd (fst e)) (snd e)) (ress_from 0 L) ->
      PrefixView.wf L.
    Proof.
      intros H1 H2 H3. split; [| split].
      - intros i j k op op' Hi Hj. apply inv_entry in Hi, Hj.
        pose proof (nodup_map_eq _ _ _ _ H1 Hi Hj eq_refl) as He. injection He as He _. exact He.
      - intros i j k op op' r r' Hi Hj. apply res_entry in Hi, Hj.
        pose proof (nodup_map_eq _ _ _ _ H2 Hi Hj eq_refl) as He. injection He as He _. exact He.
      - intros j k op r Hj. rewrite Forall_forall in H3. exact (H3 _ (res_entry _ _ _ _ _ Hj)).
    Qed.

    Lemma complete_of_entries L :
      Forall (fun e => exists j (r : Sig.ar (snd e)), res L j (snd (fst e)) (snd e) r) (invs_from 0 L) ->
      PrefixView.complete L.
    Proof.
      intros H i k op Hi. rewrite Forall_forall in H. exact (H _ (inv_entry _ _ _ _ Hi)).
    Qed.

    Lemma vf_path_cons_inv {G : RelaxedSig.t} (V : LTS G) v ev evs v'' :
      vf_path V v (ev :: evs) v'' -> exists v', Step V ev v v' /\ vf_path V v' evs v''.
    Proof. intros Hp. inversion Hp; subst. eexists. split; eassumption. Qed.

    (** *** B6: one thread, [enq v; deq] *)

    Theorem b6_enq_deq (v : A) (T : list (ThreadEvent F)) t h1 h2 W :
      h1 <> h2 ->
      (forall i k op, inv T i k op -> (k = (t, h1) /\ op = enq v) \/ (k = (t, h2) /\ op = deq)) ->
      (exists i, inv T i (t, h1) (enq v)) -> (exists i, inv T i (t, h2) deq) ->
      rel_lin_witness (@PrefixView.sel F) T (semi_independent F) (νQ A) W ->
      W = [Build_Op (t, h1) (enq v) tt; Build_Op (t, h2) deq v].
    Proof.
      intros Hh Hinv (i1 & Hi1) (i2 & Hi2) (Hnu & Hnd & Hocc & Hcov & _).
      pose proof (NoDup_map_inv _ _ Hnd) as HndW.
      assert (Hops : forall o, In o W ->
                 (op_key o = (t, h1) /\ op_op o = enq v) \/ (op_key o = (t, h2) /\ op_op o = deq)).
      { intros o Ho. destruct (Hocc o Ho) as [(i & Hi) _]. exact (Hinv _ _ _ Hi). }
      destruct (Hcov _ _ _ Hi1) as (oE & HoE & HkE).
      destruct (Hcov _ _ _ Hi2) as (oD & HoD & HkD).
      assert (HE : oE = Build_Op (t, h1) (enq v) tt).
      { destruct (Hops oE HoE) as [[_ Hop] | [Hk _]].
        - destruct oE as [k op r]. cbn in HkE, Hop. subst k op. destruct r. reflexivity.
        - exfalso. rewrite HkE in Hk. injection Hk as Hk. exact (Hh Hk). }
      subst oE.
      destruct oD as [kD opD rD]. cbn in HkD. subst kD.
      assert (HopD : opD = deq).
      { destruct (Hops _ HoD) as [[Hk _] | [_ Hop]]; [| exact Hop].
        exfalso. cbn in Hk. injection Hk as Hk. exact (Hh (eq_sym Hk)). }
      subst opD.
      assert (HW2 : forall o, In o W -> o = Build_Op (t, h1) (enq v) tt \/ o = Build_Op (t, h2) deq rD).
      { intros o Ho. destruct (Hops o Ho) as [[Hk _] | [Hk _]].
        - left. exact (RelaxedHoareSpec.nodup_key_eq W o _ Hnd Ho HoE Hk).
        - right. exact (RelaxedHoareSpec.nodup_key_eq W o _ Hnd Ho HoD Hk). }
      assert (HED : Build_Op (t, h1) (enq v) tt <> Build_Op (t, h2) deq rD) by (intros H; discriminate H).
      (* the enqueue comes first: a dequeue needs an earlier enqueue *)
      assert (HbED : before W (Build_Op (t, h1) (enq v) tt) (Build_Op (t, h2) deq rD)).
      { destruct (before_total W _ _ HoE HoD HED) as [H | (l1 & l2 & HW & HE2)]; [exact H | exfalso].
        destruct Hnu as (s & Hs). rewrite HW in Hs. apply run_app_inv in Hs as (q1 & H1 & H2).
        apply run_cons_inv in H2 as (q2 & Hd & _). cbn in Hd.
        destruct (fifo_src _ _ _ rD H1 ltac:(rewrite Hd; left; reflexivity)) as [[] | (o & Ho & Hv)].
        assert (HoW : In o W) by (rewrite HW; apply in_or_app; left; exact Ho).
        destruct (HW2 o HoW) as [-> | ->]; [| discriminate Hv].
        rewrite HW in HndW. exact (nodup_app_disj l1 _ _ HndW Ho (or_intror HE2)). }
      destruct HbED as (l1 & l2 & HW & HD2).
      assert (Hl1 : l1 = []).
      { apply none_nil. intros x Hx. assert (HxW : In x W) by (rewrite HW; apply in_or_app; left; exact Hx).
        rewrite HW in HndW. destruct (HW2 x HxW) as [-> | ->].
        - exact (nodup_app_disj l1 _ _ HndW Hx (or_introl eq_refl)).
        - exact (nodup_app_disj l1 _ _ HndW Hx (or_intror HD2)). }
      subst l1. cbn in HW.
      assert (Hl2 : l2 = [Build_Op (t, h2) deq rD]).
      { apply all_eq_singleton; [rewrite HW in HndW; apply NoDup_cons_iff in HndW as [_ H]; exact H | exact HD2 |].
        intros x Hx. assert (HxW : In x W) by (rewrite HW; right; exact Hx).
        destruct (HW2 x HxW) as [-> | ->]; [| reflexivity].
        exfalso. rewrite HW in HndW. apply NoDup_cons_iff in HndW as [H _]. exact (H Hx). }
      subst l2.
      destruct Hnu as (s & Hs). rewrite HW in Hs. apply run_enq in Hs. apply run_cons_inv in Hs as (q & Hd & _).
      cbn in Hd. injection Hd as <- _. exact HW.
    Qed.

    Corollary b6_returns (v : A) (T : list (ThreadEvent F)) t h1 h2 :
      h1 <> h2 -> PrefixView.wf T ->
      (forall i k op, inv T i k op -> (k = (t, h1) /\ op = enq v) \/ (k = (t, h2) /\ op = deq)) ->
      (exists i, inv T i (t, h1) (enq v)) -> (exists i, inv T i (t, h2) deq) ->
      rel_lin (@PrefixView.sel F) T (semi_independent F) (νQ A) ->
      forall j (r : A), res T j (t, h2) deq r -> r = v.
    Proof.
      intros Hh Hwf Hinv Hi1 Hi2 (W & HW) j r Hj.
      pose proof (b6_enq_deq v T t h1 h2 W Hh Hinv Hi1 Hi2 HW) as HWeq.
      destruct HW as (_ & _ & Hocc & _ & _).
      assert (HD : In (Build_Op (t, h2) deq v) W) by (rewrite HWeq; right; left; reflexivity).
      destruct (Hocc _ HD) as [_ (j' & Hj')]. cbn in Hj'.
      pose proof (POQueueRSound.wf_res_uniq _ _ _ _ _ _ _ _ Hwf Hj Hj') as <-.
      apply res_deq_ret in Hj, Hj'. rewrite Hj in Hj'. injection Hj' as ->. reflexivity.
    Qed.
  End Fifo.

  (** ** Concrete traces over [positive] values *)

  Local Abbreviation FP := (FQ positive).
  Local Abbreviation inv L := (inv_at (@PrefixView.sel FP) L).
  Local Abbreviation res L := (res_at (@PrefixView.sel FP) L).
  Local Abbreviation t1 := 1%positive.
  Local Abbreviation t2 := 2%positive.
  Local Abbreviation t3 := 3%positive.

  Definition ie (t : tid) (h : nat) (v : positive) : ThreadEvent FP := Build_ThreadEvent t (@InvEv FP h (enq v)).
  Definition idq (t : tid) (h : nat) : ThreadEvent FP := Build_ThreadEvent t (@InvEv FP h deq).
  Definition re (t : tid) (h : nat) (v : positive) : ThreadEvent FP := Build_ThreadEvent t (@ResEv FP h (enq v) tt).
  Definition rdq (t : tid) (h : nat) (r : positive) : ThreadEvent FP := Build_ThreadEvent t (@ResEv FP h deq r).

  Lemma st_ei (s : @POQueueState positive) t h v :
    TMap.find t (poq_pending s) = None ->
    Step (POQueueR positive) (ie t h v) (POQReady s) (POQReady (poq_start_enq t v s)).
  Proof. intros H. cbn. exists s. auto. Qed.

  Lemma st_er (s : @POQueueState positive) t h v n :
    TMap.find t (poq_pending s) = Some n ->
    Step (POQueueR positive) (re t h v) (POQReady s) (POQReady (poq_finish_enq t s)).
  Proof. intros H. cbn. exists s, n. auto. Qed.

  Lemma st_di (s : @POQueueState positive) t h : Step (POQueueR positive) (idq t h) (POQReady s) (POQAtomic s t).
  Proof. cbn. exists s. auto. Qed.

  Lemma st_dr (s : @POQueueState positive) t h n r :
    poq_minimal s n -> poq_complete s n -> poq_vertices s n = Some r ->
    Step (POQueueR positive) (rdq t h r) (POQAtomic s t) (POQReady (poq_mark_garbage n s)).
  Proof. intros H1 H2 H3. cbn. exists s, n. auto 6. Qed.

  Lemma inv_at_pos L i e t h o : nth_error L i = Some e -> e = Build_ThreadEvent t (@InvEv FP h o) -> inv L i (t, h) o.
  Proof. intros Hi ->. exists (Build_ThreadEvent t (InvEv h o)). split; [exact Hi | reflexivity]. Qed.

  (** Tactics for the concrete traces. *)
  Ltac lookup H :=
    cbn in H;
    repeat match type of H with _ \/ _ => destruct H as [H | H] end;
    try contradiction; try discriminate H; injection H; intros; subst.

  Ltac nodup_keys :=
    cbn; repeat constructor; cbn; intros Hin;
    repeat match type of Hin with _ \/ _ => destruct Hin as [Hin | Hin] end;
    try contradiction; discriminate Hin.

  Ltac inv_here := eexists; split; reflexivity.

  (** *** 1. The order of overlapping enqueues is decided by the future *)

  Definition Tf (r : positive) : list (ThreadEvent FP) :=
    [ie t1 0 1; ie t2 0 2; re t2 0 2; re t1 0 1; idq t3 0; rdq t3 0 r].

  Definition Fs1 := poq_start_enq t1 1%positive empty_poqueue_state.
  Definition Fs2 := poq_start_enq t2 2%positive Fs1.
  Definition Fs4 := poq_finish_enq t1 (poq_finish_enq t2 Fs2).

  Lemma Fs4_not_pending n : ~ poq_pending_vertex Fs4 n.
  Proof.
    intros (a & Ha).
    change (TMap.find a (TMap.remove t1 (TMap.remove t2 (TMap.add t2 1 (TMap.add t1 0 (TMap.empty nat))))) = Some n) in Ha.
    apply find_remove_inv in Ha as [Hne1 Ha]. apply find_remove_inv in Ha as [Hne2 Ha].
    apply find_add_inv in Ha as [[Ha _] | [_ Ha]]; [contradiction |].
    apply find_add_inv in Ha as [[Ha _] | [_ Ha]]; [contradiction |].
    rewrite TMap.gempty in Ha. discriminate Ha.
  Qed.

  Lemma Fs4_live n : n < 2 -> poq_live Fs4 n.
  Proof.
    intros Hn. split.
    - unfold poq_is_vertex. destruct n as [| [| n]]; [cbn; discriminate | cbn; discriminate | lia].
    - cbn. intros [].
  Qed.

  (** No edge leaves either vertex: each was invoked while the other was
      pending (or absent). *)
  Lemma Fs4_no_edge n m : ~ poq_edges Fs4 n m.
  Proof.
    intros He. change (poq_edges Fs2 n m) in He. unfold Fs2 in He. rewrite poq_start_enq_edges in He.
    destruct He as [He | [-> [Hv Hnp]]].
    - unfold Fs1 in He. rewrite poq_start_enq_edges in He.
      destruct He as [[] | [_ [Hv _]]]. apply Hv. reflexivity.
    - (* [m] is a complete vertex of [Fs1]: impossible *)
      destruct (Nat.eq_dec m 0) as [-> | Hm0].
      + apply Hnp. exists t1. reflexivity.
      + apply Hv. unfold Fs1. rewrite poq_start_enq_vertices by (cbn; exact Hm0). reflexivity.
  Qed.

  Ltac tf_prefix :=
    eapply vf_cons; [apply st_ei; reflexivity |];
    eapply vf_cons; [apply st_ei; reflexivity |];
    eapply vf_cons; [eapply st_er; reflexivity |];
    eapply vf_cons; [eapply st_er; reflexivity |];
    eapply vf_cons; [apply st_di |];
    eapply vf_cons; [| apply vf_nil].

  Lemma Tf_path r : r = 1%positive \/ r = 2%positive ->
    exists c, vf_path (POQueueR positive) poqr_init (Tf r) c.
  Proof.
    intros Hr. destruct Hr as [-> | ->]; eexists; unfold Tf.
    - tf_prefix. apply (st_dr Fs4 t3 0 0 1).
      + split; [exact (Fs4_live 0 ltac:(lia)) | intros m He; exfalso; exact (Fs4_no_edge 0 m He)].
      + split; [exact (proj1 (Fs4_live 0 ltac:(lia))) | apply Fs4_not_pending].
      + reflexivity.
    - tf_prefix. apply (st_dr Fs4 t3 0 1 2).
      + split; [exact (Fs4_live 1 ltac:(lia)) | intros m He; exfalso; exact (Fs4_no_edge 1 m He)].
      + split; [exact (proj1 (Fs4_live 1 ltac:(lia))) | apply Fs4_not_pending].
      + reflexivity.
  Qed.

  Lemma Tf_wf r : PrefixView.wf (Tf r).
  Proof.
    apply wf_of_entries; [nodup_keys | nodup_keys |].
    cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 1. split; [cbn; lia | inv_here].
    - exists 0. split; [cbn; lia | inv_here].
    - exists 4. split; [cbn; lia | inv_here].
  Qed.

  Lemma Tf_complete r : PrefixView.complete (Tf r).
  Proof.
    apply complete_of_entries. cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 3, tt. inv_here.
    - exists 2, tt. inv_here.
    - exists 5, r. inv_here.
  Qed.

  Lemma Tf_rel_lin r : r = 1%positive \/ r = 2%positive ->
    rel_lin (@PrefixView.sel FP) (Tf r) (semi_independent FP) (νQ positive).
  Proof.
    intros Hr. destruct (Tf_path r Hr) as (c & Hp).
    exact (POQueueRSound.poqr_sound _ _ Hp (Tf_wf r) (Tf_complete r)).
  Qed.

  Definition Ea : Op FP := @Build_Op FP (t1, 0) (enq 1%positive) tt.
  Definition Eb : Op FP := @Build_Op FP (t2, 0) (enq 2%positive) tt.

  (** Facts about any witness of [Tf r]. *)
  Section TfWitness.
    Variable r : positive.
    Variable W : list (Op FP).
    Hypothesis HW : rel_lin_witness (@PrefixView.sel FP) (Tf r) (semi_independent FP) (νQ positive) W.

    Lemma Tf_W_Ea : In Ea W.
    Proof.
      destruct HW as (_ & _ & Hocc & Hcov & _).
      destruct (Hcov 0 (t1, 0) (enq 1%positive) ltac:(inv_here)) as (o & Ho & Hk).
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      destruct x. exact Ho.
    Qed.

    Lemma Tf_W_Eb : In Eb W.
    Proof.
      destruct HW as (_ & _ & Hocc & Hcov & _).
      destruct (Hcov 1 (t2, 0) (enq 2%positive) ltac:(inv_here)) as (o & Ho & Hk).
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      destruct x. exact Ho.
    Qed.

    (** Every dequeue in [W] returns [r]. *)
    Lemma Tf_W_deq o x : In o W -> deq_ret o = Some x -> x = r.
    Proof.
      destruct HW as (_ & _ & Hocc & _ & _). intros Ho Hx.
      destruct o as [k op y]. destruct op as [v |]; cbn in Hx; [discriminate Hx |]. injection Hx as ->.
      destruct (Hocc _ Ho) as [_ (j & Hj)]. cbn in Hj.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj.
      cbn in Hret. injection Hret as ->. reflexivity.
    Qed.

    Lemma Tf_W_uniq o v : In o W -> enq_val o = Some v ->
      (v = 1%positive -> o = Ea) /\ (v = 2%positive -> o = Eb).
    Proof.
      destruct HW as (_ & Hnd & Hocc & _ & _). intros Ho Hv.
      destruct o as [k op y]. destruct op as [w |]; cbn in Hv; [| discriminate Hv]. injection Hv as ->.
      destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      - split; [intros _ | intros Habs; discriminate Habs].
        apply (RelaxedHoareSpec.nodup_key_eq W _ Ea Hnd Ho Tf_W_Ea). reflexivity.
      - split; [intros Habs; discriminate Habs | intros _].
        apply (RelaxedHoareSpec.nodup_key_eq W _ Eb Hnd Ho Tf_W_Eb). reflexivity.
    Qed.

    Lemma Tf_W_has_deq : exists o, In o W /\ deq_ret o = Some r.
    Proof.
      destruct HW as (_ & _ & Hocc & Hcov & _).
      destruct (Hcov 4 (t3, 0) deq ltac:(inv_here)) as (o & Ho & Hk).
      exists o. split; [exact Ho |].
      destruct o as [k op y]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) (j & Hj)]. cbn in Hi, Hj. apply inv_entry in Hi. lookup Hi.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj.
      cbn in Hret. injection Hret as ->. reflexivity.
    Qed.
  End TfWitness.

  Theorem future_dependent :
    firstn 4 (Tf 1%positive) = firstn 4 (Tf 2%positive) /\
    (forall r, r = 1%positive \/ r = 2%positive ->
       (exists c, vf_path (POQueueR positive) poqr_init (Tf r) c) /\
       PrefixView.wf (Tf r) /\ PrefixView.complete (Tf r) /\
       rel_lin (@PrefixView.sel FP) (Tf r) (semi_independent FP) (νQ positive)) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) (Tf 1%positive) (semi_independent FP) (νQ positive) W ->
       before W Ea Eb) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) (Tf 2%positive) (semi_independent FP) (νQ positive) W ->
       before W Eb Ea).
  Proof.
    split; [reflexivity |]. split.
    { intros r Hr. split; [exact (Tf_path r Hr) |]. split; [apply Tf_wf |]. split; [apply Tf_complete |].
      exact (Tf_rel_lin r Hr). }
    split.
    - intros W HW. pose proof HW as (Hnu & Hnd & _).
      pose proof (NoDup_map_inv _ _ Hnd) as HndW.
      destruct (before_total W Ea Eb (Tf_W_Ea _ _ HW) (Tf_W_Eb _ _ HW) ltac:(discriminate)) as [H | H]; [exact H |].
      exfalso. destruct (Tf_W_has_deq _ _ HW) as (o & Ho & Hr).
      apply (fifo_order W Eb Ea 2%positive 1%positive Hnu HndW H eq_refl ltac:(discriminate)) with (o := o);
        [| | exact Ho | exact Hr].
      + intros o' Ho' Hv. exact (proj1 (Tf_W_uniq _ _ HW o' _ Ho' Hv) eq_refl).
      + intros o' Ho' Hv. pose proof (Tf_W_deq _ _ HW o' _ Ho' Hv) as Habs. discriminate Habs.
    - intros W HW. pose proof HW as (Hnu & Hnd & _).
      pose proof (NoDup_map_inv _ _ Hnd) as HndW.
      destruct (before_total W Ea Eb (Tf_W_Ea _ _ HW) (Tf_W_Eb _ _ HW) ltac:(discriminate)) as [H | H]; [| exact H].
      exfalso. destruct (Tf_W_has_deq _ _ HW) as (o & Ho & Hr).
      apply (fifo_order W Ea Eb 1%positive 2%positive Hnu HndW H eq_refl ltac:(discriminate)) with (o := o);
        [| | exact Ho | exact Hr].
      + intros o' Ho' Hv. exact (proj2 (Tf_W_uniq _ _ HW o' _ Ho' Hv) eq_refl).
      + intros o' Ho' Hv. pose proof (Tf_W_deq _ _ HW o' _ Ho' Hv) as Habs. discriminate Habs.
  Qed.

  (** *** 2. [I(enq, deq)] is needed: a trace of [POQueueR] that is not
          relaxed-linearizable under the empty relation *)

  Definition T0 : list (ThreadEvent FP) :=
    [ie t1 0 1; re t1 0 1; ie t1 1 2; idq t1 2; rdq t1 2 1;
     ie t2 0 3; re t1 1 2; re t2 0 3; idq t1 3; rdq t1 3 3].

  Definition S1 := poq_start_enq t1 1%positive empty_poqueue_state.
  Definition S2 := poq_finish_enq t1 S1.
  Definition S3 := poq_start_enq t1 2%positive S2.
  Definition S5 := poq_mark_garbage 0 S3.
  Definition S6 := poq_start_enq t2 3%positive S5.
  Definition S8 := poq_finish_enq t2 (poq_finish_enq t1 S6).

  Lemma S3_complete0 : poq_complete S3 0.
  Proof.
    split; [unfold poq_is_vertex; cbn; discriminate |].
    intros (a & Ha).
    change (TMap.find a (TMap.add t1 1 (TMap.remove t1 (TMap.add t1 0 (TMap.empty nat)))) = Some 0) in Ha.
    apply find_add_inv in Ha as [[_ H] | [_ Ha]]; [discriminate H |].
    apply find_remove_inv in Ha as [Hne Ha].
    apply find_add_inv in Ha as [[H _] | [_ Ha]]; [contradiction |].
    rewrite TMap.gempty in Ha. discriminate Ha.
  Qed.

  Lemma S3_minimal0 : poq_minimal S3 0.
  Proof.
    split; [split; [unfold poq_is_vertex; cbn; discriminate | cbn; intros []] |].
    intros m He. unfold S3 in He. rewrite poq_start_enq_edges in He.
    destruct He as [He | [Habs _]]; [| cbn in Habs; discriminate Habs].
    change (poq_edges S1 0 m) in He. unfold S1 in He. rewrite poq_start_enq_edges in He.
    destruct He as [[] | [_ [Hv _]]]. exfalso. apply Hv. reflexivity.
  Qed.

  Lemma S8_complete2 : poq_complete S8 2.
  Proof.
    split; [unfold poq_is_vertex; cbn; discriminate |].
    intros (a & Ha).
    change (TMap.find a (TMap.remove t2 (TMap.remove t1 (TMap.add t2 2 (TMap.add t1 1
              (TMap.remove t1 (TMap.add t1 0 (TMap.empty nat))))))) = Some 2) in Ha.
    apply find_remove_inv in Ha as [Hne2 Ha]. apply find_remove_inv in Ha as [Hne1 Ha].
    apply find_add_inv in Ha as [[Ha _] | [_ Ha]]; [contradiction |].
    apply find_add_inv in Ha as [[Ha _] | [_ Ha]]; [contradiction |].
    apply find_remove_inv in Ha as [_ Ha].
    apply find_add_inv in Ha as [[Ha _] | [_ Ha]]; [contradiction |].
    rewrite TMap.gempty in Ha. discriminate Ha.
  Qed.

  Lemma S8_minimal2 : poq_minimal S8 2.
  Proof.
    split; [split; [unfold poq_is_vertex; cbn; discriminate | cbn; intros [H | []]; discriminate H] |].
    intros m He. change (poq_edges S6 2 m) in He. unfold S6 in He. rewrite poq_start_enq_edges in He.
    destruct He as [He | [_ [Hv Hnp]]].
    - exfalso. change (poq_edges S3 2 m) in He. unfold S3 in He. rewrite poq_start_enq_edges in He.
      destruct He as [He | [Habs _]]; [| cbn in Habs; discriminate Habs].
      change (poq_edges S1 2 m) in He. unfold S1 in He. rewrite poq_start_enq_edges in He.
      destruct He as [[] | [Habs _]]. cbn in Habs. discriminate Habs.
    - (* [m] was complete when vertex 2 was created: only vertex 0, now removed *)
      intros [_ Hg]. destruct (Nat.eq_dec m 0) as [-> | Hm0].
      + apply Hg. cbn. left. reflexivity.
      + destruct (Nat.eq_dec m 1) as [-> | Hm1].
        * apply Hnp. exists t1. reflexivity.
        * apply Hv. change (@vertex_update positive 1 2%positive (vertex_update 0 1%positive empty_vertex_map) m = None).
          rewrite !vertex_update_other by lia. reflexivity.
  Qed.

  Lemma T0_path : vf_path (POQueueR positive) poqr_init T0 (POQReady (poq_mark_garbage 2 S8)).
  Proof.
    unfold T0.
    eapply vf_cons; [apply st_ei; reflexivity |].
    eapply vf_cons; [eapply st_er; reflexivity |].
    eapply vf_cons; [apply st_ei; reflexivity |].
    eapply vf_cons; [apply st_di |].
    eapply vf_cons; [apply (st_dr S3 t1 2 0 1); [exact S3_minimal0 | exact S3_complete0 | reflexivity] |].
    eapply vf_cons; [apply st_ei; reflexivity |].
    eapply vf_cons; [eapply st_er; reflexivity |].
    eapply vf_cons; [eapply st_er; reflexivity |].
    eapply vf_cons; [apply st_di |].
    eapply vf_cons; [apply (st_dr S8 t1 3 2 3); [exact S8_minimal2 | exact S8_complete2 | reflexivity] |].
    apply vf_nil.
  Qed.

  Lemma T0_wf : PrefixView.wf T0.
  Proof.
    apply wf_of_entries; [nodup_keys | nodup_keys |].
    cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 0. split; [cbn; lia | inv_here].
    - exists 3. split; [cbn; lia | inv_here].
    - exists 2. split; [cbn; lia | inv_here].
    - exists 5. split; [cbn; lia | inv_here].
    - exists 8. split; [cbn; lia | inv_here].
  Qed.

  Lemma T0_complete : PrefixView.complete T0.
  Proof.
    apply complete_of_entries. cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 1, tt. inv_here.
    - exists 6, tt. inv_here.
    - exists 4, 1%positive. inv_here.
    - exists 7, tt. inv_here.
    - exists 9, 3%positive. inv_here.
  Qed.

  Lemma T0_rel_lin : rel_lin (@PrefixView.sel FP) T0 (semi_independent FP) (νQ positive).
  Proof. exact (POQueueRSound.poqr_sound _ _ T0_path T0_wf T0_complete). Qed.

  Lemma T0_not_rel_lin_empty : ~ rel_lin (@PrefixView.sel FP) T0 (fun _ _ => False) (νQ positive).
  Proof.
    intros (W & Hnu & Hnd & Hocc & Hcov & Hord).
    pose proof (NoDup_map_inv _ _ Hnd) as HndW.
    set (E1 := @Build_Op FP (t1, 1) (enq 2%positive) tt : Op FP).
    set (D2 := @Build_Op FP (t1, 2) deq 1%positive : Op FP).
    set (E3 := @Build_Op FP (t2, 0) (enq 3%positive) tt : Op FP).
    assert (HE1 : In E1 W).
    { destruct (Hcov 2 (t1, 1) (enq 2%positive) ltac:(inv_here)) as (o & Ho & Hk).
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      destruct x. exact Ho. }
    assert (HE3 : In E3 W).
    { destruct (Hcov 5 (t2, 0) (enq 3%positive) ltac:(inv_here)) as (o & Ho & Hk).
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      destruct x. exact Ho. }
    assert (HD2 : In D2 W).
    { destruct (Hcov 3 (t1, 2) deq ltac:(inv_here)) as (o & Ho & Hk).
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) (j & Hj)]. cbn in Hi, Hj. apply inv_entry in Hi. lookup Hi.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj.
      cbn in Hret. injection Hret as <-. exact Ho. }
    assert (HD3 : exists o, In o W /\ deq_ret o = Some 3%positive).
    { destruct (Hcov 8 (t1, 3) deq ltac:(inv_here)) as (o & Ho & Hk).
      exists o. split; [exact Ho |].
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) (j & Hj)]. cbn in Hi, Hj. apply inv_entry in Hi. lookup Hi.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj.
      cbn in Hret. injection Hret as <-. reflexivity. }
    (* program order (not relaxed under ∅) and real time *)
    assert (H12 : before W E1 D2).
    { apply Hord; [exact HE1 | exact HD2 |]. right. split; [reflexivity |].
      exists 2, 3. split; [inv_here |]. split; [inv_here |]. split; [lia | intros []]. }
    assert (H23 : before W D2 E3).
    { apply Hord; [exact HD2 | exact HE3 |]. left. exists 4, 5. split; [inv_here |]. split; [inv_here | lia]. }
    pose proof (before_trans W E1 D2 E3 HndW H12 H23) as H13.
    destruct HD3 as (o3 & Ho3 & Hr3).
    apply (fifo_order W E1 E3 2%positive 3%positive Hnu HndW H13 eq_refl ltac:(discriminate)) with (o := o3);
      [| | exact Ho3 | exact Hr3].
    - (* E3 is the only enqueue of 3 *)
      intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [| discriminate Hv].
      injection Hv as ->. destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      apply (RelaxedHoareSpec.nodup_key_eq W _ E3 Hnd Ho HE3). reflexivity.
    - (* no dequeue returns 2 *)
      intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [discriminate Hv |].
      injection Hv as ->. destruct (Hocc _ Ho) as [_ (j & Hj)]. cbn in Hj.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj;
        cbn in Hret; discriminate Hret.
  Qed.

  Theorem T0_needs_qsi :
    vf_path (POQueueR positive) poqr_init T0 (POQReady (poq_mark_garbage 2 S8)) /\
    PrefixView.wf T0 /\ PrefixView.complete T0 /\
    rel_lin (@PrefixView.sel FP) T0 (semi_independent FP) (νQ positive) /\
    ~ rel_lin (@PrefixView.sel FP) T0 (fun _ _ => False) (νQ positive).
  Proof.
    split; [exact T0_path |]. split; [exact T0_wf |]. split; [exact T0_complete |].
    split; [exact T0_rel_lin | exact T0_not_rel_lin_empty].
  Qed.

  (** *** 3. The per-thread condition of [POQueueR] is needed *)

  Definition Tk : list (ThreadEvent FP) :=
    [ie t1 0 1; ie t1 1 2; re t1 1 2; idq t2 0; rdq t2 0 2; re t1 0 1].

  Lemma Tk_wf : PrefixView.wf Tk.
  Proof.
    apply wf_of_entries; [nodup_keys | nodup_keys |].
    cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 1. split; [cbn; lia | inv_here].
    - exists 3. split; [cbn; lia | inv_here].
    - exists 0. split; [cbn; lia | inv_here].
  Qed.

  Lemma Tk_complete : PrefixView.complete Tk.
  Proof.
    apply complete_of_entries. cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 5, tt. inv_here.
    - exists 2, tt. inv_here.
    - exists 4, 2%positive. inv_here.
  Qed.

  Lemma Tk_not_rel_lin : ~ rel_lin (@PrefixView.sel FP) Tk (semi_independent FP) (νQ positive).
  Proof.
    intros (W & Hnu & Hnd & Hocc & Hcov & Hord).
    pose proof (NoDup_map_inv _ _ Hnd) as HndW.
    set (Ka := @Build_Op FP (t1, 0) (enq 1%positive) tt : Op FP).
    set (Kb := @Build_Op FP (t1, 1) (enq 2%positive) tt : Op FP).
    assert (HKa : In Ka W).
    { destruct (Hcov 0 (t1, 0) (enq 1%positive) ltac:(inv_here)) as (o & Ho & Hk).
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      destruct x. exact Ho. }
    assert (HKb : In Kb W).
    { destruct (Hcov 1 (t1, 1) (enq 2%positive) ltac:(inv_here)) as (o & Ho & Hk).
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      destruct x. exact Ho. }
    assert (HD : exists o, In o W /\ deq_ret o = Some 2%positive).
    { destruct (Hcov 3 (t2, 0) deq ltac:(inv_here)) as (o & Ho & Hk).
      exists o. split; [exact Ho |].
      destruct o as [k op x]. cbn in Hk. subst k.
      destruct (Hocc _ Ho) as [(i & Hi) (j & Hj)]. cbn in Hi, Hj. apply inv_entry in Hi. lookup Hi.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj.
      cbn in Hret. injection Hret as <-. reflexivity. }
    (* the two enqueues of thread 1 stay ordered: (enq, enq) is not semi-independent *)
    assert (Hab : before W Ka Kb).
    { apply Hord; [exact HKa | exact HKb |]. right. split; [reflexivity |].
      exists 0, 1. split; [inv_here |]. split; [inv_here |]. split; [lia | cbn; intros []]. }
    destruct HD as (o2 & Ho2 & Hr2).
    apply (fifo_order W Ka Kb 1%positive 2%positive Hnu HndW Hab eq_refl ltac:(discriminate)) with (o := o2);
      [| | exact Ho2 | exact Hr2].
    - intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [| discriminate Hv].
      injection Hv as ->. destruct (Hocc _ Ho) as [(i & Hi) _]. cbn in Hi. apply inv_entry in Hi. lookup Hi.
      apply (RelaxedHoareSpec.nodup_key_eq W _ Kb Hnd Ho HKb). reflexivity.
    - intros o Ho Hv. destruct o as [k op x]. destruct op as [w |]; cbn in Hv; [discriminate Hv |].
      injection Hv as ->. destruct (Hocc _ Ho) as [_ (j & Hj)]. cbn in Hj.
      pose proof (res_deq_ret _ _ _ _ Hj) as Hret. apply res_entry in Hj. lookup Hj.
      cbn in Hret. discriminate Hret.
  Qed.

  (** [POQueueR] rejects [Tk]: thread 1 starts its second enqueue while
      the first is pending. *)
  Lemma Tk_no_path c : ~ vf_path (POQueueR positive) poqr_init Tk c.
  Proof.
    intros Hp. unfold Tk in Hp.
    apply vf_path_cons_inv in Hp as (c1 & Hs1 & Hp).
    apply vf_path_cons_inv in Hp as (c2 & Hs2 & _).
    cbn in Hs1, Hs2. destruct Hs1 as (s & Hs & _ & ->). destruct Hs2 as (s' & Hs' & Hf & _).
    unfold poqr_init in Hs. injection Hs as <-. injection Hs' as <-. cbn in Hf. discriminate Hf.
  Qed.

  (** *** 4. B6: a non-vacuity instance *)

  Definition Tb6 : list (ThreadEvent FP) := [ie t1 0 1; re t1 0 1; idq t1 1; rdq t1 1 1].

  Definition B2 := poq_finish_enq t1 (poq_start_enq t1 1%positive empty_poqueue_state).

  Lemma Tb6_path : exists c, vf_path (POQueueR positive) poqr_init Tb6 c.
  Proof.
    eexists. unfold Tb6.
    eapply vf_cons; [apply st_ei; reflexivity |].
    eapply vf_cons; [eapply st_er; reflexivity |].
    eapply vf_cons; [apply st_di |].
    eapply vf_cons; [apply (st_dr B2 t1 1 0 1) | apply vf_nil].
    - split; [split; [unfold poq_is_vertex; cbn; discriminate | cbn; intros []] |].
      intros m He. change (poq_edges (poq_start_enq t1 1%positive empty_poqueue_state) 0 m) in He.
      rewrite poq_start_enq_edges in He. destruct He as [[] | [_ [Hv _]]]. exfalso. apply Hv. reflexivity.
    - split; [unfold poq_is_vertex; cbn; discriminate |].
      intros (a & Ha). change (TMap.find a (TMap.remove t1 (TMap.add t1 0 (TMap.empty nat))) = Some 0) in Ha.
      apply find_remove_inv in Ha as [Hne Ha]. apply find_add_inv in Ha as [[Ha _] | [_ Ha]]; [contradiction |].
      rewrite TMap.gempty in Ha. discriminate Ha.
    - reflexivity.
  Qed.

  Lemma Tb6_wf : PrefixView.wf Tb6.
  Proof.
    apply wf_of_entries; [nodup_keys | nodup_keys |].
    cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 0. split; [cbn; lia | inv_here].
    - exists 2. split; [cbn; lia | inv_here].
  Qed.

  Lemma Tb6_complete : PrefixView.complete Tb6.
  Proof.
    apply complete_of_entries. cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 1, tt. inv_here.
    - exists 3, 1%positive. inv_here.
  Qed.

  Theorem Tb6_b6 :
    rel_lin (@PrefixView.sel FP) Tb6 (semi_independent FP) (νQ positive) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) Tb6 (semi_independent FP) (νQ positive) W ->
       W = [@Build_Op FP (t1, 0) (enq 1%positive) tt; @Build_Op FP (t1, 1) deq 1%positive]).
  Proof.
    split.
    - destruct Tb6_path as (c & Hp). exact (POQueueRSound.poqr_sound _ _ Hp Tb6_wf Tb6_complete).
    - intros W HW. apply (b6_enq_deq 1%positive Tb6 t1 0 1 W); [discriminate | | exists 0; inv_here | exists 2; inv_here | exact HW].
      intros i k op Hi. apply inv_entry in Hi. lookup Hi; [left | right]; split; reflexivity.
  Qed.

  (** A relaxed-happens-before edge that a concrete trace cannot have:
      the positions contradict it. *)
  Ltac rhb_absurd Hr :=
    destruct Hr as [(a & b & Ha & Hb & Hab) | (_ & a & b & Ha & Hb & Hab & _)];
    cbn [op_key op_op op_ret] in Ha, Hb;
    [ apply res_entry in Ha; apply inv_entry in Hb | apply inv_entry in Ha; apply inv_entry in Hb ];
    lookup Ha; lookup Hb; lia.

  (** *** 5. B6 with the program-order edge dropped

      In [Tb6] the enqueue responds before the dequeue is invoked, so real
      time already orders them.  In [Tb6ov] thread 1 invokes [deq] while
      its [enq 1] is pending, and the dequeue returns first: [I(enq, deq)]
      drops the program-order edge and real time gives no edge either, so
      no [rhb] edge relates the two calls.  Only the blocking [δQ] forces
      the enqueue first ([b6_enq_deq]).  [Tb6ov] is not a path of
      [POQueueR] (a dequeue needs a complete vertex), so its witness is
      given directly. *)

  Definition Tb6ov : list (ThreadEvent FP) := [ie t1 0 1; idq t1 1; rdq t1 1 1; re t1 0 1].

  Lemma Tb6ov_wf : PrefixView.wf Tb6ov.
  Proof.
    apply wf_of_entries; [nodup_keys | nodup_keys |].
    cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 1. split; [cbn; lia | inv_here].
    - exists 0. split; [cbn; lia | inv_here].
  Qed.

  Lemma Tb6ov_complete : PrefixView.complete Tb6ov.
  Proof.
    apply complete_of_entries. cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 3, tt. inv_here.
    - exists 2, 1%positive. inv_here.
  Qed.

  Lemma Tb6ov_no_rhb :
    ~ rhb (@PrefixView.sel FP) Tb6ov (semi_independent FP)
        (@Build_Op FP (t1, 0) (enq 1%positive) tt) (@Build_Op FP (t1, 1) deq 1%positive) /\
    ~ rhb (@PrefixView.sel FP) Tb6ov (semi_independent FP)
        (@Build_Op FP (t1, 1) deq 1%positive) (@Build_Op FP (t1, 0) (enq 1%positive) tt).
  Proof.
    split; intros Hr.
    - destruct Hr as [(a & b & Ha & Hb & Hab) | (_ & a & b & Ha & Hb & Hab & Hn)].
      + cbn [op_key op_op op_ret] in Ha, Hb. apply res_entry in Ha. apply inv_entry in Hb.
        lookup Ha; lookup Hb; lia.
      + apply Hn. exact Logic.I.
    - rhb_absurd Hr.
  Qed.

  Lemma Tb6ov_rel_lin : rel_lin (@PrefixView.sel FP) Tb6ov (semi_independent FP) (νQ positive).
  Proof.
    exists [@Build_Op FP (t1, 0) (enq 1%positive) tt; @Build_Op FP (t1, 1) deq 1%positive].
    split; [| split; [| split; [| split]]].
    - eexists. econstructor; [cbn; reflexivity |]. econstructor; [cbn; reflexivity |]. constructor.
    - cbn. constructor; [intros [H | []]; discriminate H | constructor; [intros [] | constructor]].
    - intros o [<- | [<- | []]]; split.
      + exists 0. inv_here.
      + exists 3. inv_here.
      + exists 1. inv_here.
      + exists 2. inv_here.
    - intros i k op Hi. apply inv_entry in Hi. lookup Hi.
      + eexists. split; [left; reflexivity | reflexivity].
      + eexists. split; [right; left; reflexivity | reflexivity].
    - intros o o' Ho Ho' Hr. destruct Ho as [<- | [<- | []]], Ho' as [<- | [<- | []]].
      + exfalso. rhb_absurd Hr.
      + apply POQueueRWitness.before_cons_hd. left. reflexivity.
      + exfalso. rhb_absurd Hr.
      + exfalso. rhb_absurd Hr.
  Qed.

  Lemma Tb6ov_no_path c : ~ vf_path (POQueueR positive) poqr_init Tb6ov c.
  Proof.
    intros Hp. unfold Tb6ov in Hp.
    apply vf_path_cons_inv in Hp as (c1 & Hs1 & Hp).
    apply vf_path_cons_inv in Hp as (c2 & Hs2 & Hp).
    apply vf_path_cons_inv in Hp as (c3 & Hs3 & _).
    cbn in Hs1, Hs2, Hs3. destruct Hs1 as (s & Hs & _ & ->). unfold poqr_init in Hs. injection Hs as <-.
    destruct Hs2 as (s' & Hs' & ->). injection Hs' as <-.
    destruct Hs3 as (s'' & n & Hs'' & _ & [Hv Hnp] & _). injection Hs'' as <-.
    destruct (Nat.eq_dec n 0) as [-> | Hn].
    - apply Hnp. exists t1. reflexivity.
    - apply Hv. change (@vertex_update positive 0 1%positive empty_vertex_map n = None).
      rewrite vertex_update_other by lia. reflexivity.
  Qed.

  Theorem Tb6ov_b6 :
    PrefixView.wf Tb6ov /\ PrefixView.complete Tb6ov /\
    rel_lin (@PrefixView.sel FP) Tb6ov (semi_independent FP) (νQ positive) /\
    (forall W, rel_lin_witness (@PrefixView.sel FP) Tb6ov (semi_independent FP) (νQ positive) W ->
       W = [@Build_Op FP (t1, 0) (enq 1%positive) tt; @Build_Op FP (t1, 1) deq 1%positive]) /\
    (forall c, ~ vf_path (POQueueR positive) poqr_init Tb6ov c).
  Proof.
    split; [exact Tb6ov_wf |]. split; [exact Tb6ov_complete |]. split; [exact Tb6ov_rel_lin |].
    split; [| exact Tb6ov_no_path].
    intros W HW. apply (b6_enq_deq 1%positive Tb6ov t1 0 1 W); [discriminate | | exists 0; inv_here | exists 1; inv_here | exact HW].
    intros i k op Hi. apply inv_entry in Hi. lookup Hi; [left | right]; split; reflexivity.
  Qed.

  (** *** 6. [POQueueR] is not a complete presentation

      [Tinc]: thread 1 overlaps two of its own enqueues and nothing is
      dequeued.  It is relaxed-linearizable (witness [enq 1; enq 2]), but
      [POQueueR] rejects it, as it rejects [Tk]. *)

  Definition Tinc : list (ThreadEvent FP) := [ie t1 0 1; ie t1 1 2; re t1 0 1; re t1 1 2].

  Lemma Tinc_wf : PrefixView.wf Tinc.
  Proof.
    apply wf_of_entries; [nodup_keys | nodup_keys |].
    cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 0. split; [cbn; lia | inv_here].
    - exists 1. split; [cbn; lia | inv_here].
  Qed.

  Lemma Tinc_complete : PrefixView.complete Tinc.
  Proof.
    apply complete_of_entries. cbn. repeat apply Forall_cons; [.. | apply Forall_nil].
    - exists 2, tt. inv_here.
    - exists 3, tt. inv_here.
  Qed.

  Lemma Tinc_rel_lin : rel_lin (@PrefixView.sel FP) Tinc (semi_independent FP) (νQ positive).
  Proof.
    exists [@Build_Op FP (t1, 0) (enq 1%positive) tt; @Build_Op FP (t1, 1) (enq 2%positive) tt].
    split; [| split; [| split; [| split]]].
    - eexists. econstructor; [cbn; reflexivity |]. econstructor; [cbn; reflexivity |]. constructor.
    - cbn. constructor; [intros [H | []]; discriminate H | constructor; [intros [] | constructor]].
    - intros o [<- | [<- | []]]; split.
      + exists 0. inv_here.
      + exists 2. inv_here.
      + exists 1. inv_here.
      + exists 3. inv_here.
    - intros i k op Hi. apply inv_entry in Hi. lookup Hi.
      + eexists. split; [left; reflexivity | reflexivity].
      + eexists. split; [right; left; reflexivity | reflexivity].
    - intros o o' Ho Ho' Hr. destruct Ho as [<- | [<- | []]], Ho' as [<- | [<- | []]].
      + exfalso. rhb_absurd Hr.
      + apply POQueueRWitness.before_cons_hd. left. reflexivity.
      + exfalso. rhb_absurd Hr.
      + exfalso. rhb_absurd Hr.
  Qed.

  Lemma Tinc_no_path c : ~ vf_path (POQueueR positive) poqr_init Tinc c.
  Proof.
    intros Hp. unfold Tinc in Hp.
    apply vf_path_cons_inv in Hp as (c1 & Hs1 & Hp).
    apply vf_path_cons_inv in Hp as (c2 & Hs2 & _).
    cbn in Hs1, Hs2. destruct Hs1 as (s & Hs & _ & ->). destruct Hs2 as (s' & Hs' & Hf & _).
    unfold poqr_init in Hs. injection Hs as <-. injection Hs' as <-. cbn in Hf. discriminate Hf.
  Qed.

  Theorem POQueueR_incomplete :
    PrefixView.wf Tinc /\ PrefixView.complete Tinc /\
    rel_lin (@PrefixView.sel FP) Tinc (semi_independent FP) (νQ positive) /\
    (forall c, ~ vf_path (POQueueR positive) poqr_init Tinc c).
  Proof.
    split; [exact Tinc_wf |]. split; [exact Tinc_complete |]. split; [exact Tinc_rel_lin | exact Tinc_no_path].
  Qed.

  (** In the vocabulary of [ViewLHL]: [POQueueR] is sound
      ([POQueueRSound.poqr_sound]) but not a complete presentation. *)
  Corollary POQueueR_not_complete_pres :
    ~ ViewLHL.complete_pres (νQ positive) (POQueueR positive) poqr_init.
  Proof.
    intros Hc. destruct (Hc Tinc) as (c & Hp).
    - exists []. rewrite app_nil_r. split; [exact Tinc_wf |]. split; [exact Tinc_complete | exact Tinc_rel_lin].
    - exact (Tinc_no_path c Hp).
  Qed.

End POQueueRExample.
