(** * POQueueRSound: [POQueueR] is a sound overlay presentation of the FIFO queue

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P3.  Main result:

    [poqr_sound : ViewLHL.sound_pres (νQ A) (POQueueR A) poqr_init]

    i.e. every complete, well-formed trace that [POQueueR] produces is
    relaxed-linearizable to the FIFO queue with a blocking dequeue, under
    the semi-independence relation of [FQ A], [I(enq, deq)].  This is the
    hypothesis [HVF] of [RelaxedGSim.gsim_rel_lin] for [VF := POQueueR A];
    the future-dependent choice of the Herlihy–Wing queue (the order of two
    overlapping enqueues, decided by a later dequeue) is entirely here.  The
    proof sees the whole complete trace, so it needs neither prophecy
    variables nor sets of possibilities.

    ** Proof

    - Part 1 ([PInv], [pinv_path]): an invariant along every path of
      [POQueueR] relates the state to the trace so far, with ghost data: the
      key [vk n] and the invocation position [vp n] of the enqueue of vertex
      [n], and the list [rems] of the dequeues (invocation position,
      removed vertex).  It records, in trace terms: vertices are the
      enqueue invocations in order; a vertex is pending iff its enqueue has
      not responded; an edge [n -> m] iff [m]'s enqueue responded before
      [n]'s invocation; a dequeue's response follows its invocation
      immediately; at its response the removed vertex had responded, and
      every DAG predecessor had been removed by an earlier dequeue; two
      enqueues of one thread do not overlap.  One lemma per event kind
      ([pinv_enq_inv], [pinv_enq_res], [pinv_deq_inv], [pinv_deq_res]).
      The thread-keyed matching of [POQueueR] is identified with the
      key-keyed matching of the trace using well-formedness of the trace
      and the per-thread clause [pi_idle] ([pinv_enq_res], [pinv_deq_res]).
    - Part 2 ([pinv_rel_lin], [poqr_sound]): on a complete trace these facts
      are the hypotheses of [POQueueRWitness.Witness]; its list [W] is
      mapped to operations ([toOp]) and checked against
      [rel_lin_witness].  On a trace of [POQueueR] every [rhb] edge under
      [I(enq, deq)] is a real-time edge ([rhb_before]): same-thread
      enqueues do not overlap, a dequeue's two events are adjacent, and an
      older enqueue with a younger dequeue is the semi-independent pair.

    Assumptions: the proof uses no axiom ([Print Assumptions poqr_sound]
    reports none; task log). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Sorting.Sorted.
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

Import ListNotations.

Module POQueueRSound.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import WHWQSpec.
  Import POQueueR.
  Import POQueueRWitness.

  (** [lia] after reducing [poq_payload] of a known control state. *)
  Ltac plia := cbn [poq_payload] in *; lia.

  Section Sound.
    Context {A : Type}.

    Local Abbreviation F := (FQ A).
    Local Abbreviation inv L := (inv_at (@PrefixView.sel F) L).
    Local Abbreviation res L := (res_at (@PrefixView.sel F) L).

    (** ** Trace helpers *)

    Definition responded (L : list (ThreadEvent F)) (k : CallKey F) : Prop :=
      exists j op (r : Sig.ar op), res L j k op r.

    Definition resp_before (L : list (ThreadEvent F)) (k : CallKey F) (x : nat) : Prop :=
      exists j op (r : Sig.ar op), res L j k op r /\ j < x.

    Lemma resp_before_app L L' k x : resp_before L k x -> resp_before (L ++ L') k x.
    Proof. intros (j & op & r & Hj & Hlt). exists j, op, r. split; [apply RelaxedHoareSpec.res_app_l; exact Hj | exact Hlt]. Qed.

    Lemma resp_before_snoc_le L ev k x : x <= length L -> resp_before (L ++ [ev]) k x -> resp_before L k x.
    Proof.
      intros Hx (j & op & r & Hj & Hlt). exists j, op, r. split; [| exact Hlt].
      apply (RelaxedHoareSpec.res_app_lt _ [ev]); [lia | exact Hj].
    Qed.

    Lemma resp_before_mono L k x y : resp_before L k x -> x <= y -> resp_before L k y.
    Proof. intros (j & op & r & Hj & Hlt) Hxy. exists j, op, r. split; [exact Hj | lia]. Qed.

    Lemma resp_before_responded L k x : resp_before L k x -> responded L k.
    Proof. intros (j & op & r & Hj & _). exists j, op, r. exact Hj. Qed.

    Lemma responded_app L L' k : responded L k -> responded (L ++ L') k.
    Proof. intros (j & op & r & Hj). exists j, op, r. apply RelaxedHoareSpec.res_app_l. exact Hj. Qed.

    Lemma responded_snoc_inv L t h o k : responded (L ++ [Build_ThreadEvent t (@InvEv F h o)]) k <-> responded L k.
    Proof.
      split; [| apply responded_app].
      intros (j & op & r & Hj). exists j, op, r. exact (RelaxedHoareSpec.res_not_inv_ev _ _ _ _ _ _ _ _ Hj).
    Qed.

    Lemma responded_resp_before L k : responded L k -> resp_before L k (length L).
    Proof.
      intros (j & op & r & Hj). exists j, op, r. split; [exact Hj | exact (RelaxedHoareSpec.res_lt _ _ _ _ _ Hj)].
    Qed.

    Lemma inv_res_same_pos L i k op k' op' (r : Sig.ar op') : inv L i k op -> res L i k' op' r -> False.
    Proof.
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-.
      unfold PrefixView.sel in Hs, Hs'. rewrite Hs in Hs'. discriminate Hs'.
    Qed.

    Lemma inv_same_pos L i k op k' op' : inv L i k op -> inv L i k' op' -> k = k' /\ op = op'.
    Proof.
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-.
      unfold PrefixView.sel in Hs, Hs'. rewrite Hs in Hs'. injection Hs' as Ht Hh Ho.
      destruct k as [t h], k' as [t' h']. cbn in Ht, Hh. subst. auto.
    Qed.

    Lemma ev_inv_eq t h o k o' :
      @Build_ThreadEvent F t (InvEv h o) = Build_ThreadEvent (fst k) (InvEv (snd k) o') -> k = (t, h) /\ o' = o.
    Proof. intros H. injection H as Ht Hh Ho. destruct k as [tk hk]; cbn in *. subst. auto. Qed.

    Lemma ev_res_eq t h o (r : Sig.ar o) k o' (r' : Sig.ar o') :
      @Build_ThreadEvent F t (ResEv h o r) = Build_ThreadEvent (fst k) (ResEv (snd k) o' r') -> k = (t, h) /\ o' = o.
    Proof.
      intros H. pose proof (f_equal (te_tid F) H) as Ht. pose proof (f_equal (te_ev F) H) as Hv.
      pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Ho. cbn in *.
      destruct k as [tk hk]; cbn in *. subst. auto.
    Qed.

    Lemma responded_snoc_res L t h o (r : Sig.ar o) k :
      responded (L ++ [Build_ThreadEvent t (@ResEv F h o r)]) k -> responded L k \/ k = (t, h).
    Proof.
      intros (j & op & r' & Hj). destruct (RelaxedHoareSpec.res_snoc_inv _ _ _ _ _ _ Hj) as [H | [_ Hev]].
      - left. exists j, op, r'. exact H.
      - right. exact (proj1 (ev_res_eq _ _ _ _ _ _ _ Hev)).
    Qed.

    Lemma wf_inv_uniq L i j k op op' : PrefixView.wf L -> inv L i k op -> inv L j k op' -> i = j.
    Proof. intros (H1 & _ & _). exact (H1 i j k op op'). Qed.

    Lemma wf_res_uniq L i j k op op' (r : Sig.ar op) (r' : Sig.ar op') :
      PrefixView.wf L -> res L i k op r -> res L j k op' r' -> i = j.
    Proof. intros (_ & H2 & _). exact (H2 i j k op op' r r'). Qed.

    Lemma wf_res_inv L j k op (r : Sig.ar op) :
      PrefixView.wf L -> res L j k op r -> exists i, i < j /\ inv L i k op.
    Proof. intros (_ & _ & H3). exact (H3 j k op r). Qed.

    (** A key invoked by the last event has not responded before it. *)
    Lemma fresh_inv_not_responded L t h o :
      PrefixView.wf (L ++ [Build_ThreadEvent t (@InvEv F h o)]) -> ~ responded L (t, h).
    Proof.
      intros Hwf (j & op & r & Hj).
      pose proof (RelaxedHoareSpec.res_lt _ _ _ _ _ Hj) as Hjl.
      destruct (wf_res_inv _ _ _ _ _ Hwf (RelaxedHoareSpec.res_app_l _ [Build_ThreadEvent t (@InvEv F h o)] _ _ _ _ Hj))
        as (i & Hij & Hi).
      pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hi (RelaxedHoareSpec.inv_snoc_last L t h o)). lia.
    Qed.

    (** The key of the event at position [i]. *)
    Definition dkey (L : list (ThreadEvent F)) (i : nat) : CallKey F :=
      match nth_error L i with Some ev => te_key ev | None => (1%positive, 0) end.

    Lemma dkey_inv L i k op : inv L i k op -> dkey L i = k.
    Proof.
      intros (x & Hx & Hs). unfold dkey. rewrite Hx. unfold PrefixView.sel in Hs. injection Hs as ->.
      destruct k as [t h]. reflexivity.
    Qed.

    Definition upd {B : Type} (f : nat -> B) (k : nat) (b : B) : nat -> B :=
      fun m => if Nat.eqb m k then b else f m.

    Lemma upd_same {B : Type} (f : nat -> B) k b : upd f k b k = b.
    Proof. unfold upd. rewrite Nat.eqb_refl. reflexivity. Qed.

    Lemma upd_other {B : Type} (f : nat -> B) k b m : m <> k -> upd f k b m = f m.
    Proof. intros H. unfold upd. apply Nat.eqb_neq in H. rewrite H. reflexivity. Qed.

    Lemma StronglySorted_snoc {B : Type} (R : B -> B -> Prop) l x :
      StronglySorted R l -> (forall y, In y l -> R y x) -> StronglySorted R (l ++ [x]).
    Proof.
      induction 1 as [| y l Hs IH Hall]; intros Hx; cbn.
      - repeat constructor.
      - constructor.
        + apply IH. intros z Hz. apply Hx. right. exact Hz.
        + rewrite Forall_forall in Hall |- *. intros z Hz. apply in_app_or in Hz as [Hz | [<- | []]].
          * exact (Hall z Hz).
          * apply Hx. left. reflexivity.
    Qed.

    Lemma nodup_map_inj_in {B C : Type} (f : B -> C) (l : list B) :
      (forall x y, In x l -> In y l -> f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
    Proof.
      intros Hf Hnd. induction Hnd as [| x l Hx Hnd IH]; cbn; constructor.
      - intros Hin. apply in_map_iff in Hin as (y & Hy & Hin).
        assert (y = x) as -> by (apply Hf; [right; exact Hin | left; reflexivity | exact Hy]).
        exact (Hx Hin).
      - apply IH. intros a b Ha Hb. apply Hf; right; assumption.
    Qed.

    Lemma sorted_fst_uniq (l : list (nat * nat)) i n n' :
      StronglySorted (fun a b => fst a < fst b) l -> In (i, n) l -> In (i, n') l -> n = n'.
    Proof.
      intros Hs. induction Hs as [| x l Hs IH Hall]; [intros [] |]. rewrite Forall_forall in Hall.
      intros H1 H2. destruct H1 as [H1 | H1], H2 as [H2 | H2].
      - subst x. injection H2 as H2. congruence.
      - subst x. specialize (Hall _ H2). cbn in Hall. lia.
      - subst x. specialize (Hall _ H1). cbn in Hall. lia.
      - exact (IH H1 H2).
    Qed.

    (** ** Part 1: the path invariant *)

    Record PInv (L : list (ThreadEvent F)) (c : POQueueControl A)
        (vk : nat -> CallKey F) (vp : nat -> nat) (rems : list (nat * nat)) : Prop := {
      pi_wf : poq_wf (poq_payload c);
      (* vertices are the enqueue invocations, in order *)
      pi_val : forall n v, poq_vertices (poq_payload c) n = Some v -> inv L (vp n) (vk n) (enq v);
      pi_enq : forall i k v, inv L i k (enq v) ->
        exists n, n < poq_next (poq_payload c) /\ vp n = i /\ vk n = k;
      pi_mono : forall n m, n < m -> m < poq_next (poq_payload c) -> vp n < vp m;
      (* pending iff not responded *)
      pi_pend : forall n, n < poq_next (poq_payload c) ->
        (responded L (vk n) <-> ~ poq_pending_vertex (poq_payload c) n);
      pi_ptid : forall t n, TMap.find t (poq_pending (poq_payload c)) = Some n -> fst (vk n) = t;
      (* the DAG is the real-time order of the enqueues *)
      pi_edge : forall n m, poq_edges (poq_payload c) n m <->
        (n < poq_next (poq_payload c) /\ m < poq_next (poq_payload c) /\ resp_before L (vk m) (vp n));
      (* the removed vertices and the completed dequeues *)
      pi_garb : forall n, poq_garbage (poq_payload c) n <-> exists i, In (i, n) rems;
      pi_rem : forall i n, In (i, n) rems -> exists k (r : A),
        inv L i k deq /\ res L (S i) k deq r /\ poq_vertices (poq_payload c) n = Some r /\
        resp_before L (vk n) i /\
        (forall m, m < poq_next (poq_payload c) -> resp_before L (vk m) (vp n) ->
           exists i', i' < i /\ In (i', m) rems);
      pi_sorted : StronglySorted (fun a b => fst a < fst b) rems;
      pi_rnd : NoDup (map snd rems);
      (* every dequeue invocation is completed or is the last event *)
      pi_deq : forall i k, inv L i k deq ->
        (exists n, In (i, n) rems) \/ (S i = length L /\ exists s, c = POQAtomic s (fst k));
      (* two enqueues of one thread do not overlap *)
      pi_idle : forall n m, n < m -> m < poq_next (poq_payload c) -> fst (vk n) = fst (vk m) ->
        resp_before L (vk n) (vp m)
    }.

    Arguments pi_wf {L c vk vp rems} _.
    Arguments pi_val {L c vk vp rems} _.
    Arguments pi_enq {L c vk vp rems} _.
    Arguments pi_mono {L c vk vp rems} _.
    Arguments pi_pend {L c vk vp rems} _.
    Arguments pi_ptid {L c vk vp rems} _.
    Arguments pi_edge {L c vk vp rems} _.
    Arguments pi_garb {L c vk vp rems} _.
    Arguments pi_rem {L c vk vp rems} _.
    Arguments pi_sorted {L c vk vp rems} _.
    Arguments pi_rnd {L c vk vp rems} _.
    Arguments pi_deq {L c vk vp rems} _.
    Arguments pi_idle {L c vk vp rems} _.

    Lemma pinv_init : PInv [] poqr_init (fun _ => (1%positive, 0)) (fun _ => 0) [].
    Proof.
      assert (Hinv : forall i k op, ~ inv [] i k op) by (intros i k op (x & Hx & _); destruct i; discriminate).
      constructor; cbn.
      - exact empty_poqueue_state_wf.
      - intros n v H. discriminate.
      - intros i k v Hi. exfalso. exact (Hinv _ _ _ Hi).
      - intros n m _ Hm. lia.
      - intros n Hn. lia.
      - intros t n H. rewrite ?TMap.gempty in H. discriminate H.
      - intros n m. split; [intros [] | intros (Hn & _); lia].
      - intros n. split; [intros [] | intros (i & [])].
      - intros i n [].
      - constructor.
      - constructor.
      - intros i k Hi. exfalso. exact (Hinv _ _ _ Hi).
      - intros n m _ Hm. lia.
    Qed.

    (** Facts derived from the invariant. *)

    Lemma pi_vertex {L c vk vp rems} (HI : PInv L c vk vp rems) n :
      n < poq_next (poq_payload c) <-> poq_vertices (poq_payload c) n <> None.
    Proof. symmetry. exact (wf_vertex_iff_lt _ (pi_wf HI) n). Qed.

    Lemma pi_vertex_lt {L c vk vp rems} (HI : PInv L c vk vp rems) n :
      poq_is_vertex (poq_payload c) n -> n < poq_next (poq_payload c).
    Proof. intros Hv. apply (pi_vertex HI). exact Hv. Qed.

    Lemma pi_inv_vertex {L c vk vp rems} (HI : PInv L c vk vp rems) n :
      n < poq_next (poq_payload c) ->
      exists v, poq_vertices (poq_payload c) n = Some v /\ inv L (vp n) (vk n) (enq v).
    Proof.
      intros Hn. apply (pi_vertex HI) in Hn. destruct (poq_vertices (poq_payload c) n) as [v |] eqn:Hv; [| congruence].
      exists v. split; [reflexivity | exact (pi_val HI n v Hv)].
    Qed.

    Lemma pi_vp_lt {L c vk vp rems} (HI : PInv L c vk vp rems) n :
      n < poq_next (poq_payload c) -> vp n < length L.
    Proof. intros Hn. destruct (pi_inv_vertex HI n Hn) as (v & _ & Hi). exact (RelaxedHoareSpec.inv_lt _ _ _ _ Hi). Qed.

    Lemma pi_vk_inj {L c vk vp rems} (HI : PInv L c vk vp rems) n m :
      PrefixView.wf L -> n < poq_next (poq_payload c) -> m < poq_next (poq_payload c) -> vk n = vk m -> n = m.
    Proof.
      intros Hwf Hn Hm Hk. destruct (pi_inv_vertex HI n Hn) as (v & _ & Hvn). destruct (pi_inv_vertex HI m Hm) as (w & _ & Hwm).
      rewrite Hk in Hvn. pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hvn Hwm) as Hp.
      destruct (Nat.lt_trichotomy n m) as [Hlt | [Heq | Hgt]]; [| exact Heq |].
      - pose proof (pi_mono HI n m Hlt Hm). lia.
      - pose proof (pi_mono HI m n Hgt Hn). lia.
    Qed.

    Lemma pi_pend_vertex {L c vk vp rems} (HI : PInv L c vk vp rems) n :
      poq_pending_vertex (poq_payload c) n -> n < poq_next (poq_payload c).
    Proof. intros Hp. apply (pi_vertex HI). exact (wf_pending_vertex _ (pi_wf HI) n Hp). Qed.

    Lemma pi_rem_lt {L c vk vp rems} (HI : PInv L c vk vp rems) i n : In (i, n) rems -> S i < length L.
    Proof.
      intros Hin. destruct (pi_rem HI i n Hin) as (k & r & _ & Hr & _).
      exact (RelaxedHoareSpec.res_lt _ _ _ _ _ Hr).
    Qed.

    Lemma pi_rem_vertex {L c vk vp rems} (HI : PInv L c vk vp rems) i n :
      In (i, n) rems -> n < poq_next (poq_payload c).
    Proof.
      intros Hin. destruct (pi_rem HI i n Hin) as (k & r & _ & _ & Hv & _).
      apply (pi_vertex HI). rewrite Hv. discriminate.
    Qed.

    (** *** Enqueue invocation: a fresh pending vertex after every complete one *)

    Lemma poq_start_enq_next (a : tid) (v : A) (s : POQueueState) :
      poq_next (poq_start_enq a v s) = S (poq_next s).
    Proof. reflexivity. Qed.

    Lemma pinv_enq_inv L s vk vp rems t h v :
      PInv L (POQReady s) vk vp rems ->
      PrefixView.wf (L ++ [Build_ThreadEvent t (@InvEv F h (enq v))]) ->
      TMap.find t (poq_pending s) = None ->
      PInv (L ++ [Build_ThreadEvent t (@InvEv F h (enq v))]) (POQReady (poq_start_enq t v s))
        (upd vk (poq_next s) (t, h)) (upd vp (poq_next s) (length L)) rems.
    Proof.
      intros HI Hwf Hidle.
      pose proof (fresh_inv_not_responded L t h (enq v) Hwf) as Hfresh.
      assert (Hfresh' : forall x, ~ resp_before (L ++ [Build_ThreadEvent t (@InvEv F h (enq v))]) (t, h) x).
      { intros x Hrb. apply Hfresh. apply (proj1 (responded_snoc_inv L t h (enq v) (t, h))).
        exact (resp_before_responded _ _ _ Hrb). }
      constructor; cbn [poq_payload].
      - exact (poq_start_enq_wf t v s (pi_wf HI) Hidle).
      - intros n w Hw. destruct (Nat.eq_dec n (poq_next s)) as [-> | Hne].
        + rewrite poq_start_enq_vertex_new in Hw. injection Hw as <-. rewrite !upd_same.
          apply RelaxedHoareSpec.inv_snoc_last.
        + rewrite poq_start_enq_vertices in Hw by exact Hne. rewrite !upd_other by exact Hne.
          apply RelaxedHoareSpec.inv_app_l. exact (pi_val HI n w Hw).
      - intros i k w Hi. rewrite poq_start_enq_next.
        apply RelaxedHoareSpec.inv_snoc_inv in Hi as [Hi | [-> Hev]].
        + destruct (pi_enq HI i k w Hi) as (n & Hn & <- & <-). exists n.
          rewrite !upd_other by plia. split; [plia | auto].
        + apply ev_inv_eq in Hev as [-> _]. exists (poq_next s). rewrite !upd_same. auto.
      - intros n m Hnm Hm. rewrite poq_start_enq_next in Hm.
        destruct (Nat.eq_dec m (poq_next s)) as [-> | Hne].
        + rewrite upd_same, upd_other by lia. exact (pi_vp_lt HI n Hnm).
        + rewrite !upd_other by lia. apply (pi_mono HI); plia.
      - intros n Hn. rewrite poq_start_enq_next in Hn. rewrite responded_snoc_inv.
        rewrite (poq_start_enq_pending_vertex t v s n Hidle).
        destruct (Nat.eq_dec n (poq_next s)) as [-> | Hne].
        + rewrite upd_same. split.
          * intros Hr. exfalso. exact (Hfresh Hr).
          * intros Hnp. exfalso. apply Hnp. left. reflexivity.
        + rewrite upd_other by exact Hne. rewrite (pi_pend HI n ltac:(plia)). split.
          * intros Hnp [Heq | Hp]; [exact (Hne Heq) | exact (Hnp Hp)].
          * intros Hnp Hp. apply Hnp. right. exact Hp.
      - intros t' n Hf. change (TMap.find t' (TMap.add t (poq_next s) (poq_pending s)) = Some n) in Hf.
        apply find_add_inv in Hf as [[-> ->] | [_ Hf]].
        + rewrite upd_same. reflexivity.
        + pose proof (pi_pend_vertex HI n (ex_intro _ t' Hf)) as Hn.
          rewrite upd_other by plia. exact (pi_ptid HI t' n Hf).
      - intros n m. rewrite poq_start_enq_edges, poq_start_enq_next. split.
        + intros [He | [-> [Hv Hnp]]].
          * destruct (proj1 (pi_edge HI n m) He) as (Hn & Hm & Hrb). rewrite !upd_other by plia.
            split; [plia |]. split; [plia |]. apply resp_before_app. exact Hrb.
          * pose proof (pi_vertex_lt HI m Hv) as Hm. rewrite upd_same, upd_other by plia.
            split; [lia |]. split; [plia |]. apply resp_before_app. apply responded_resp_before.
            apply (pi_pend HI m Hm). exact Hnp.
        + intros (Hn & Hm & Hrb). destruct (Nat.eq_dec m (poq_next s)) as [-> | Hmne].
          * exfalso. rewrite upd_same in Hrb. exact (Hfresh' _ Hrb).
          * rewrite (upd_other vk) in Hrb by exact Hmne.
            destruct (Nat.eq_dec n (poq_next s)) as [-> | Hne].
            -- right. split; [reflexivity |]. rewrite upd_same in Hrb.
               apply resp_before_snoc_le in Hrb; [| lia].
               split; [exact (proj1 (pi_vertex HI m) ltac:(plia)) |].
               apply (pi_pend HI m ltac:(plia)). exact (resp_before_responded _ _ _ Hrb).
            -- left. rewrite upd_other in Hrb by exact Hne. apply (proj2 (pi_edge HI n m)).
               pose proof (pi_vp_lt HI n ltac:(plia)). split; [plia |]. split; [plia |].
               apply resp_before_snoc_le in Hrb; [exact Hrb | lia].
      - exact (pi_garb HI).
      - intros i n Hin. destruct (pi_rem HI i n Hin) as (k & r & Hi & Hr & Hv & Hd & Hmin).
        pose proof (pi_rem_vertex HI i n Hin) as Hn. pose proof (pi_vp_lt HI n Hn) as Hvpn.
        exists k, r. split; [apply RelaxedHoareSpec.inv_app_l; exact Hi |].
        split; [apply RelaxedHoareSpec.res_app_l; exact Hr |].
        split; [rewrite poq_start_enq_vertices by plia; exact Hv |].
        split; [rewrite (upd_other vk) by plia; apply resp_before_app; exact Hd |].
        intros m Hm Hrb. rewrite poq_start_enq_next in Hm. rewrite (upd_other vp) in Hrb by plia.
        destruct (Nat.eq_dec m (poq_next s)) as [-> | Hmne].
        + exfalso. rewrite upd_same in Hrb. exact (Hfresh' _ Hrb).
        + rewrite upd_other in Hrb by exact Hmne. apply resp_before_snoc_le in Hrb; [| lia].
          exact (Hmin m ltac:(plia) Hrb).
      - exact (pi_sorted HI).
      - exact (pi_rnd HI).
      - intros i k Hi. apply RelaxedHoareSpec.inv_snoc_inv in Hi as [Hi | [_ Hev]].
        + destruct (pi_deq HI i k Hi) as [H | (_ & s0 & Hs0)]; [left; exact H | discriminate Hs0].
        + exfalso. apply ev_inv_eq in Hev as [_ Ho]. discriminate Ho.
      - intros n m Hnm Hm Ht. rewrite poq_start_enq_next in Hm.
        destruct (Nat.eq_dec m (poq_next s)) as [-> | Hmne].
        + rewrite (upd_other vk (poq_next s) (t, h) n) in Ht |- * by lia.
          rewrite upd_same in Ht. rewrite upd_same.
          apply resp_before_app. apply responded_resp_before. apply (pi_pend HI n Hnm).
          intros (a & Ha). pose proof (pi_ptid HI a n Ha) as Hta. rewrite Ht in Hta. cbn in Hta. subst a.
          cbn [poq_payload] in Ha. congruence.
        + rewrite (upd_other vk _ _ n), (upd_other vk _ _ m) in Ht by lia.
          rewrite (upd_other vk _ _ n), (upd_other vp _ _ m) by lia. apply resp_before_app.
          exact (pi_idle HI n m Hnm ltac:(plia) Ht).
    Qed.

    (** *** Enqueue response: the thread's pending vertex completes *)

    Lemma pinv_enq_res L s vk vp rems t h v (r : unit) n0 :
      PInv L (POQReady s) vk vp rems ->
      PrefixView.wf (L ++ [Build_ThreadEvent t (@ResEv F h (enq v) r)]) ->
      TMap.find t (poq_pending s) = Some n0 ->
      PInv (L ++ [Build_ThreadEvent t (@ResEv F h (enq v) r)]) (POQReady (poq_finish_enq t s)) vk vp rems.
    Proof.
      intros HI Hwf Hf.
      assert (HwfL : PrefixView.wf L) by exact (RelaxedHoareSpec.wf_app_l _ _ Hwf).
      (* the responding key [(t, h)] is the key of the thread's pending vertex [n0] *)
      destruct (wf_res_inv _ _ _ _ _ Hwf (RelaxedHoareSpec.res_snoc_last L t h (enq v) r)) as (i & Hil & Hi).
      apply (RelaxedHoareSpec.inv_app_lt _ _ _ _ _ Hil) in Hi.
      destruct (pi_enq HI i (t, h) v Hi) as (n & Hn & _ & Hvk).
      assert (Hnr : ~ responded L (t, h)).
      { intros (j & op & r' & Hj). pose proof (RelaxedHoareSpec.res_lt _ _ _ _ _ Hj).
        pose proof (wf_res_uniq _ _ _ _ _ _ _ _ Hwf (RelaxedHoareSpec.res_app_l _ _ _ _ _ _ Hj)
                      (RelaxedHoareSpec.res_snoc_last L t h (enq v) r)). lia. }
      assert (Hp0 : poq_pending_vertex s n0) by (exists t; exact Hf).
      pose proof (pi_pend_vertex HI n0 Hp0) as Hn0.
      pose proof (pi_ptid HI t n0 Hf) as Ht0.
      assert (Hnr0 : ~ responded L (vk n0)) by (intros Hr; exact (proj1 (pi_pend HI n0 Hn0) Hr Hp0)).
      assert (Hvk0 : vk n0 = (t, h)).
      { destruct (Nat.lt_trichotomy n n0) as [Hlt | [<- | Hgt]].
        - exfalso. apply Hnr. rewrite <- Hvk. apply (resp_before_responded _ _ (vp n0)).
          apply (pi_idle HI n n0 Hlt Hn0). rewrite Hvk, Ht0. reflexivity.
        - exact Hvk.
        - exfalso. apply Hnr0. apply (resp_before_responded _ _ (vp n)).
          apply (pi_idle HI n0 n Hgt Hn). rewrite Hvk, Ht0. reflexivity. }
      clear Hvk Hn n Hi Hil i.
      assert (Hresp : forall k, responded (L ++ [Build_ThreadEvent t (@ResEv F h (enq v) r)]) k <->
                                responded L k \/ k = (t, h)).
      { intros k. split; [apply responded_snoc_res |].
        intros [Hk | ->]; [apply responded_app; exact Hk |].
        exists (length L), (enq v), r. apply RelaxedHoareSpec.res_snoc_last. }
      constructor; cbn [poq_payload].
      - exact (poq_finish_enq_wf t s (pi_wf HI)).
      - intros m w Hw. apply RelaxedHoareSpec.inv_app_l. exact (pi_val HI m w Hw).
      - intros i k w Hi. apply RelaxedHoareSpec.inv_not_res_ev in Hi. exact (pi_enq HI i k w Hi).
      - exact (pi_mono HI).
      - intros m Hm. rewrite Hresp. rewrite (poq_finish_enq_pending_vertex_iff t s n0 m (pi_wf HI) Hf).
        destruct (Nat.eq_dec m n0) as [-> | Hne].
        + rewrite Hvk0. split.
          * intros _ [_ Hne]. exact (Hne eq_refl).
          * intros _. right. reflexivity.
        + assert (Hk : vk m <> (t, h)).
          { rewrite <- Hvk0. intros Hk. exact (Hne (pi_vk_inj HI m n0 HwfL Hm Hn0 Hk)). }
          rewrite (pi_pend HI m Hm). split.
          * intros [Hnp | Hk']; [intros [Hp _]; exact (Hnp Hp) | contradiction].
          * intros Hnp. left. intros Hp. apply Hnp. split; [exact Hp | exact Hne].
      - intros t' m Hf'. change (TMap.find t' (TMap.remove t (poq_pending s)) = Some m) in Hf'.
        apply find_remove_inv in Hf' as [_ Hf']. exact (pi_ptid HI t' m Hf').
      - intros n m. split.
        + intros He. destruct (proj1 (pi_edge HI n m) He) as (Hn & Hm & Hrb).
          split; [exact Hn |]. split; [exact Hm |]. apply resp_before_app. exact Hrb.
        + intros (Hn & Hm & Hrb). apply (proj2 (pi_edge HI n m)). split; [exact Hn |]. split; [exact Hm |].
          apply resp_before_snoc_le in Hrb; [exact Hrb |]. pose proof (pi_vp_lt HI n Hn). lia.
      - exact (pi_garb HI).
      - intros i m Hin. destruct (pi_rem HI i m Hin) as (k & r' & Hi & Hr' & Hv & Hd & Hmin).
        exists k, r'. split; [apply RelaxedHoareSpec.inv_app_l; exact Hi |].
        split; [apply RelaxedHoareSpec.res_app_l; exact Hr' |]. split; [exact Hv |].
        split; [apply resp_before_app; exact Hd |].
        intros m' Hm' Hrb. apply Hmin; [exact Hm' |]. apply resp_before_snoc_le in Hrb; [exact Hrb |].
        pose proof (pi_vp_lt HI m (pi_rem_vertex HI i m Hin)). lia.
      - exact (pi_sorted HI).
      - exact (pi_rnd HI).
      - intros i k Hi. apply RelaxedHoareSpec.inv_not_res_ev in Hi.
        destruct (pi_deq HI i k Hi) as [H | (_ & s0 & Hs0)]; [left; exact H | discriminate Hs0].
      - intros n m Hnm Hm Ht. apply resp_before_app. exact (pi_idle HI n m Hnm Hm Ht).
    Qed.

    (** *** Dequeue invocation: the control state becomes atomic *)

    Lemma pinv_deq_inv L s vk vp rems t h :
      PInv L (POQReady s) vk vp rems ->
      PInv (L ++ [Build_ThreadEvent t (@InvEv F h deq)]) (POQAtomic s t) vk vp rems.
    Proof.
      intros HI. constructor; cbn [poq_payload].
      - exact (pi_wf HI).
      - intros n w Hw. apply RelaxedHoareSpec.inv_app_l. exact (pi_val HI n w Hw).
      - intros i k w Hi. apply RelaxedHoareSpec.inv_snoc_inv in Hi as [Hi | [_ Hev]].
        + exact (pi_enq HI i k w Hi).
        + exfalso. apply ev_inv_eq in Hev as [_ Ho]. discriminate Ho.
      - exact (pi_mono HI).
      - intros n Hn. rewrite responded_snoc_inv. exact (pi_pend HI n Hn).
      - exact (pi_ptid HI).
      - intros n m. split.
        + intros He. destruct (proj1 (pi_edge HI n m) He) as (Hn & Hm & Hrb).
          split; [exact Hn |]. split; [exact Hm |]. apply resp_before_app. exact Hrb.
        + intros (Hn & Hm & Hrb). apply (proj2 (pi_edge HI n m)). split; [exact Hn |]. split; [exact Hm |].
          apply resp_before_snoc_le in Hrb; [exact Hrb |]. pose proof (pi_vp_lt HI n Hn). lia.
      - exact (pi_garb HI).
      - intros i n Hin. destruct (pi_rem HI i n Hin) as (k & r & Hi & Hr & Hv & Hd & Hm).
        exists k, r. split; [apply RelaxedHoareSpec.inv_app_l; exact Hi |].
        split; [apply RelaxedHoareSpec.res_app_l; exact Hr |]. split; [exact Hv |].
        split; [apply resp_before_app; exact Hd |].
        intros m Hm' Hrb. apply Hm; [exact Hm' |]. apply resp_before_snoc_le in Hrb; [exact Hrb |].
        pose proof (pi_vp_lt HI n (pi_rem_vertex HI i n Hin)). lia.
      - exact (pi_sorted HI).
      - exact (pi_rnd HI).
      - intros i k Hi. apply RelaxedHoareSpec.inv_snoc_inv in Hi as [Hi | [-> Hev]].
        + destruct (pi_deq HI i k Hi) as [H | (_ & s0 & Hs0)]; [left; exact H | discriminate Hs0].
        + right. apply ev_inv_eq in Hev as [-> _].
          split; [rewrite length_app; cbn; lia | exists s; reflexivity].
      - intros n m Hnm Hm Ht. apply resp_before_app. exact (pi_idle HI n m Hnm Hm Ht).
    Qed.

    (** *** Dequeue response: a minimal complete live vertex is removed *)

    Lemma pinv_deq_res L s vk vp rems t h (r : A) n0 :
      PInv L (POQAtomic s t) vk vp rems ->
      PrefixView.wf (L ++ [Build_ThreadEvent t (@ResEv F h deq r)]) ->
      poq_minimal s n0 -> poq_complete s n0 -> poq_vertices s n0 = Some r ->
      PInv (L ++ [Build_ThreadEvent t (@ResEv F h deq r)]) (POQReady (poq_mark_garbage n0 s)) vk vp
        (rems ++ [(pred (length L), n0)]).
    Proof.
      intros HI Hwf Hmin Hc Hv0.
      assert (HwfL : PrefixView.wf L) by exact (RelaxedHoareSpec.wf_app_l _ _ Hwf).
      (* the responding dequeue was invoked by the last event of [L] *)
      destruct (wf_res_inv _ _ _ _ _ Hwf (RelaxedHoareSpec.res_snoc_last L t h deq r)) as (i0 & Hil & Hi0).
      apply (RelaxedHoareSpec.inv_app_lt _ _ _ _ _ Hil) in Hi0.
      assert (Hi0e : S i0 = length L).
      { destruct (pi_deq HI i0 (t, h) Hi0) as [(n & Hin) | (H & _)]; [exfalso | exact H].
        destruct (pi_rem HI i0 n Hin) as (k & r' & Hk & Hr' & _).
        destruct (inv_same_pos _ _ _ _ _ _ Hk Hi0) as [-> _].
        pose proof (RelaxedHoareSpec.res_lt _ _ _ _ _ Hr').
        pose proof (wf_res_uniq _ _ _ _ _ _ _ _ Hwf (RelaxedHoareSpec.res_app_l _ _ _ _ _ _ Hr')
                      (RelaxedHoareSpec.res_snoc_last L t h deq r)). lia. }
      replace (pred (length L)) with i0 by lia.
      pose proof (pi_vertex_lt HI n0 (proj1 Hc)) as Hn0.
      assert (Hdone : resp_before L (vk n0) i0).
      { destruct (proj2 (pi_pend HI n0 Hn0) (proj2 Hc)) as (j & op & r' & Hj).
        exists j, op, r'. split; [exact Hj |].
        pose proof (RelaxedHoareSpec.res_lt _ _ _ _ _ Hj).
        destruct (Nat.eq_dec j i0) as [-> | Hne]; [exfalso; exact (inv_res_same_pos _ _ _ _ _ _ _ Hi0 Hj) | lia]. }
      assert (Hkey : forall m, m < poq_next s -> vk m <> (t, h)).
      { intros m Hm Hk. destruct (pi_inv_vertex HI m Hm) as (w & _ & Hw). rewrite Hk in Hw.
        pose proof (wf_inv_uniq _ _ _ _ _ _ HwfL Hw Hi0) as Hp. rewrite Hp in Hw.
        destruct (inv_same_pos _ _ _ _ _ _ Hw Hi0) as [_ Ho]. discriminate Ho. }
      assert (Hnotin : ~ In n0 (map snd rems)).
      { intros Hin. apply in_map_iff in Hin as ([i n] & Heq & Hin). cbn in Heq. subst n.
        apply (proj2 (proj1 Hmin)). apply (proj2 (pi_garb HI n0)). exists i. exact Hin. }
      assert (Hresp : forall m, m < poq_next s ->
                 (responded (L ++ [Build_ThreadEvent t (@ResEv F h deq r)]) (vk m) <-> responded L (vk m))).
      { intros m Hm. split; [| apply responded_app].
        intros Hr. destruct (responded_snoc_res _ _ _ _ _ _ Hr) as [H | H]; [exact H | exfalso; exact (Hkey m Hm H)]. }
      constructor; cbn [poq_payload].
      - exact (poq_mark_garbage_wf n0 s (pi_wf HI) Hc).
      - intros n w Hw. apply RelaxedHoareSpec.inv_app_l. exact (pi_val HI n w Hw).
      - intros i k w Hi. apply RelaxedHoareSpec.inv_not_res_ev in Hi. exact (pi_enq HI i k w Hi).
      - exact (pi_mono HI).
      - intros m Hm. rewrite (Hresp m Hm). exact (pi_pend HI m Hm).
      - exact (pi_ptid HI).
      - intros n m. split.
        + intros He. destruct (proj1 (pi_edge HI n m) He) as (Hn & Hm & Hrb).
          split; [exact Hn |]. split; [exact Hm |]. apply resp_before_app. exact Hrb.
        + intros (Hn & Hm & Hrb). apply (proj2 (pi_edge HI n m)). split; [exact Hn |]. split; [exact Hm |].
          apply resp_before_snoc_le in Hrb; [exact Hrb |]. pose proof (pi_vp_lt HI n Hn). lia.
      - intros n. change (poq_garbage (poq_mark_garbage n0 s) n) with (n = n0 \/ poq_garbage s n). split.
        + intros [-> | Hg].
          * exists i0. apply in_or_app. right. left. reflexivity.
          * destruct (proj1 (pi_garb HI n) Hg) as (i & Hin). exists i. apply in_or_app. left. exact Hin.
        + intros (i & Hin). apply in_app_or in Hin as [Hin | [Heq | []]].
          * right. apply (proj2 (pi_garb HI n)). exists i. exact Hin.
          * injection Heq as _ <-. left. reflexivity.
      - intros i n Hin. apply in_app_or in Hin as [Hin | [Heq | []]].
        + destruct (pi_rem HI i n Hin) as (k & r' & Hi & Hr' & Hv & Hd & Hm).
          exists k, r'. split; [apply RelaxedHoareSpec.inv_app_l; exact Hi |].
          split; [apply RelaxedHoareSpec.res_app_l; exact Hr' |]. split; [exact Hv |].
          split; [apply resp_before_app; exact Hd |].
          intros m Hm' Hrb. apply resp_before_snoc_le in Hrb;
            [| pose proof (pi_vp_lt HI n (pi_rem_vertex HI i n Hin)); lia].
          destruct (Hm m Hm' Hrb) as (i' & Hlt & Hin').
          exists i'. split; [exact Hlt | apply in_or_app; left; exact Hin'].
        + injection Heq as <- <-. exists (t, h), r. split; [apply RelaxedHoareSpec.inv_app_l; exact Hi0 |].
          split; [rewrite Hi0e; apply RelaxedHoareSpec.res_snoc_last |]. split; [exact Hv0 |].
          split; [apply resp_before_app; exact Hdone |].
          intros m Hm Hrb. apply resp_before_snoc_le in Hrb; [| pose proof (pi_vp_lt HI n0 Hn0); lia].
          assert (He : poq_edges s n0 m).
          { apply (proj2 (pi_edge HI n0 m)). split; [exact Hn0 | split; [exact Hm | exact Hrb]]. }
          destruct (in_dec Nat.eq_dec m (map snd rems)) as [Hmr | Hmr].
          * apply in_map_iff in Hmr as ([i' m'] & Heq & Hin'). cbn in Heq. subst m'.
            exists i'. split; [pose proof (pi_rem_lt HI i' m Hin'); lia | apply in_or_app; left; exact Hin'].
          * exfalso. apply (proj2 Hmin m He). split.
            -- exact (proj1 (pi_vertex HI m) Hm).
            -- intros Hg. apply Hmr. destruct (proj1 (pi_garb HI m) Hg) as (i' & Hin').
               apply in_map_iff. exists (i', m). split; [reflexivity | exact Hin'].
      - apply StronglySorted_snoc; [exact (pi_sorted HI) |]. intros [i n] Hin. cbn.
        pose proof (pi_rem_lt HI i n Hin). lia.
      - rewrite map_app. cbn [map snd]. apply NoDup_app; [exact (pi_rnd HI) | constructor; [intros [] | constructor] |].
        intros x Hx [<- | []]. exact (Hnotin Hx).
      - intros i k Hi. apply RelaxedHoareSpec.inv_not_res_ev in Hi.
        destruct (pi_deq HI i k Hi) as [(n & Hin) | (Hi' & _)].
        + left. exists n. apply in_or_app. left. exact Hin.
        + left. exists n0. replace i with i0 by lia. apply in_or_app. right. left. reflexivity.
      - intros n m Hnm Hm Ht. apply resp_before_app. exact (pi_idle HI n m Hnm Hm Ht).
    Qed.

    (** *** Paths *)

    Lemma pinv_step L c vk vp rems ev c' :
      PInv L c vk vp rems -> PrefixView.wf (L ++ [ev]) -> poqr_step ev c c' ->
      exists vk' vp' rems', PInv (L ++ [ev]) c' vk' vp' rems'.
    Proof.
      intros HI Hwf Hs. destruct ev as [t [h o | h o r]]; destruct o as [v |];
        unfold poqr_step in Hs; cbn [te_ev te_tid] in Hs.
      - destruct Hs as (s & -> & Hidle & ->). eexists _, _, _.
        exact (pinv_enq_inv L s vk vp rems t h v HI Hwf Hidle).
      - destruct Hs as (s & -> & ->). exists vk, vp, rems. exact (pinv_deq_inv L s vk vp rems t h HI).
      - destruct Hs as (s & n & -> & Hf & ->). exists vk, vp, rems.
        exact (pinv_enq_res L s vk vp rems t h v r n HI Hwf Hf).
      - destruct Hs as (s & n & -> & Hmin & Hc & Hv & ->). eexists _, _, _.
        exact (pinv_deq_res L s vk vp rems t h r n HI Hwf Hmin Hc Hv).
    Qed.

    Lemma vf_path_one (v : POQueueControl A) ev v' : vf_path (POQueueR A) v [ev] v' -> poqr_step ev v v'.
    Proof.
      intros Hp. inversion Hp; subst.
      match goal with H : vf_path _ _ [] _ |- _ => inversion H; subst end.
      match goal with H : RelaxedLTSSpec.Step _ _ _ _ |- _ => exact H end.
    Qed.

    Lemma pinv_path T (c : POQueueControl A) :
      vf_path (POQueueR A) poqr_init T c -> PrefixView.wf T -> exists vk vp rems, PInv T c vk vp rems.
    Proof.
      revert c. induction T as [| ev T IH] using rev_ind; intros c Hp Hwf.
      - inversion Hp; subst. exists (fun _ => (1%positive, 0)), (fun _ => 0), []. exact pinv_init.
      - destruct (RelaxedHoareSpec.vf_path_app_inv _ _ _ _ _ Hp) as (c0 & Hp0 & Hp1).
        destruct (IH c0 Hp0 (RelaxedHoareSpec.wf_app_l _ _ Hwf)) as (vk & vp & rems & HI).
        exact (pinv_step T c0 vk vp rems ev c HI Hwf (vf_path_one c0 ev c Hp1)).
    Qed.

    (** ** Part 2: the linearization of a complete trace *)

    Section Complete.
      Context (T : list (ThreadEvent F)) (c : POQueueControl A) (vk : nat -> CallKey F) (vp : nat -> nat)
              (rems : list (nat * nat)) (HI : PInv T c vk vp rems)
              (Hwf : PrefixView.wf T) (Hc : PrefixView.complete T).
      Local Abbreviation s := (poq_payload c).
      Local Abbreviation nE := (poq_next (poq_payload c)).

      (** On a complete trace every dequeue has completed. *)
      Lemma deq_in_rems i k : inv T i k deq -> exists n, In (i, n) rems.
      Proof.
        intros Hi. destruct (pi_deq HI i k Hi) as [H | (Hl & _)]; [exact H | exfalso].
        destruct (Hc i k deq Hi) as (j & r & Hj).
        destruct (wf_res_inv _ _ _ _ _ Hwf Hj) as (i' & Hij & Hi').
        pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hi Hi'). pose proof (RelaxedHoareSpec.res_lt _ _ _ _ _ Hj). lia.
      Qed.

      (** The hypotheses of [POQueueRWitness.Witness]. *)
      Definition db (n x : nat) : Prop := resp_before T (vk n) x.

      Lemma H_resp n x : n < nE -> db n x -> vp n < x.
      Proof.
        intros Hn (j & op & r & Hj & Hjx).
        destruct (wf_res_inv _ _ _ _ _ Hwf Hj) as (i & Hij & Hi).
        destruct (pi_inv_vertex HI n Hn) as (v & _ & Hv).
        pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hi Hv). lia.
      Qed.

      Lemma H_done i n : In (i, n) rems -> db n i.
      Proof. intros Hin. destruct (pi_rem HI i n Hin) as (k & r & _ & _ & _ & Hd & _). exact Hd. Qed.

      Lemma H_min i n m : In (i, n) rems -> m < nE -> db m (vp n) -> exists i', i' < i /\ In (i', m) rems.
      Proof. intros Hin. destruct (pi_rem HI i n Hin) as (k & r & _ & _ & _ & _ & Hm). exact (Hm m). Qed.

      Lemma H_mon n x y : db n x -> x <= y -> db n y.
      Proof. apply resp_before_mono. Qed.

      Lemma H_pos i n m : In (i, n) rems -> m < nE -> vp m <> i.
      Proof.
        intros Hin Hm Heq. destruct (pi_rem HI i n Hin) as (k & r & Hi & _).
        destruct (pi_inv_vertex HI m Hm) as (v & _ & Hv). rewrite Heq in Hv.
        destruct (inv_same_pos _ _ _ _ _ _ Hv Hi) as [_ Ho]. discriminate Ho.
      Qed.

      Local Abbreviation W0 := (W nE vp rems).

      Lemma W0_in_enq n : In (inl n) W0 <-> n < nE.
      Proof. exact (W_in_enq nE vp rems (pi_rem_vertex HI) n). Qed.

      Section WithDefault.
        (** A value for the (unused) case of a missing vertex. *)
        Context (a0 : A).

        Definition val (n : nat) : A := match poq_vertices s n with Some v => v | None => a0 end.

        Definition toOp (x : nat + nat * nat) : Op F :=
          match x with
          | inl n => Build_Op (vk n) (enq (val n)) tt
          | inr (i, n) => Build_Op (dkey T i) deq (val n)
          end.

        Definition Wq : list (Op F) := map toOp W0.

        Lemma enq_inv n : n < nE -> inv T (vp n) (vk n) (enq (val n)).
        Proof.
          intros Hn. destruct (pi_inv_vertex HI n Hn) as (v & Hv & Hi). unfold val. rewrite Hv. exact Hi.
        Qed.

        Lemma rem_inv i n : In (i, n) rems -> inv T i (dkey T i) deq /\ res T (S i) (dkey T i) deq (val n).
        Proof.
          intros Hin. destruct (pi_rem HI i n Hin) as (k & r & Hi & Hr & Hv & _).
          rewrite (dkey_inv _ _ _ _ Hi). unfold val. rewrite Hv. split; [exact Hi | exact Hr].
        Qed.

        (** A run of the vertex queue is a run of the FIFO queue. *)
        Lemma vq_seq q W' q' : vq_run q W' q' ->
          RelaxedHoareSpec.seq_run (δQ A) (map val q) (map toOp W') (map val q').
        Proof.
          induction 1 as [q | q n W' q' H IH | q i n W' q' H IH].
          - constructor.
          - cbn [map]. eapply RelaxedHoareSpec.seq_cons; [| exact IH]. cbn. rewrite map_app. reflexivity.
          - cbn [map]. eapply RelaxedHoareSpec.seq_cons; [| exact IH]. cbn. reflexivity.
        Qed.

        (** Every [rhb] edge of the trace is an edge of the witness. *)
        Lemma rhb_before x y : In x W0 -> In y W0 ->
          rhb (@PrefixView.sel F) T (semi_independent F) (toOp x) (toOp y) -> before W0 x y.
        Proof.
          intros Hx Hy [(a & b & Ha & Hb & Hab) | (Ht & a & b & Ha & Hb & Hab & Hni)];
            destruct x as [n | [i n]], y as [m | [i' m]]; cbn [toOp op_key op_op op_ret] in *.
          - (* real time, enq / enq *)
            apply W0_in_enq in Hx, Hy.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hb (enq_inv m Hy)) as ->.
            apply (W_rt_ee nE vp db rems (pi_mono HI) H_resp (pi_sorted HI) H_min n m Hx Hy).
            exists a, (enq (val n)), tt. split; [exact Ha | exact Hab].
          - (* real time, enq / deq *)
            apply W0_in_enq in Hx. apply W_in_deq in Hy.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hb (proj1 (rem_inv i' m Hy))) as ->.
            apply (W_rt_ed nE vp db rems (pi_mono HI) H_resp (pi_sorted HI) (pi_rnd HI) (pi_rem_vertex HI)
                     H_done H_min H_mon H_pos n i' m Hx Hy).
            exists a, (enq (val n)), tt. split; [exact Ha | exact Hab].
          - (* real time, deq / enq *)
            apply W_in_deq in Hx. apply W0_in_enq in Hy.
            pose proof (wf_res_uniq _ _ _ _ _ _ _ _ Hwf Ha (proj2 (rem_inv i n Hx))) as ->.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hb (enq_inv m Hy)) as ->.
            exact (W_rt_de nE vp rems (pi_sorted HI) (pi_rem_vertex HI) i n m Hx Hy Hab).
          - (* real time, deq / deq *)
            apply W_in_deq in Hx, Hy.
            pose proof (wf_res_uniq _ _ _ _ _ _ _ _ Hwf Ha (proj2 (rem_inv i n Hx))) as ->.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hb (proj1 (rem_inv i' m Hy))) as ->.
            exact (W_rt_dd nE vp rems (pi_sorted HI) i n i' m Hx Hy Hab).
          - (* program order, enq / enq: the older enqueue has responded *)
            apply W0_in_enq in Hx, Hy.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Ha (enq_inv n Hx)) as ->.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hb (enq_inv m Hy)) as ->.
            assert (Hnm : n < m).
            { destruct (Nat.lt_trichotomy n m) as [H | [-> | H]]; [exact H | lia |].
              pose proof (pi_mono HI m n H Hx). lia. }
            exact (W_rt_ee nE vp db rems (pi_mono HI) H_resp (pi_sorted HI) H_min n m Hx Hy
                     (pi_idle HI n m Hnm Hy Ht)).
          - (* program order, enq / deq: the semi-independent pair *)
            exfalso. apply Hni. exact Logic.I.
          - (* program order, deq / enq: the dequeue has responded *)
            apply W_in_deq in Hx. apply W0_in_enq in Hy.
            destruct (rem_inv i n Hx) as [Hi Hr].
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Ha Hi) as ->.
            pose proof (enq_inv m Hy) as Hm.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hb Hm) as ->.
            apply (W_rt_de nE vp rems (pi_sorted HI) (pi_rem_vertex HI) i n m Hx Hy).
            destruct (Nat.eq_dec (vp m) (S i)) as [Heq | Hne]; [exfalso | lia].
            rewrite Heq in Hm. exact (inv_res_same_pos _ _ _ _ _ _ _ Hm Hr).
          - (* program order, deq / deq *)
            apply W_in_deq in Hx, Hy.
            destruct (rem_inv i n Hx) as [Hi Hr].
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Ha Hi) as ->.
            pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hb (proj1 (rem_inv i' m Hy))) as ->.
            apply (W_rt_dd nE vp rems (pi_sorted HI) i n i' m Hx Hy).
            destruct (Nat.eq_dec i' (S i)) as [-> | Hne]; [exfalso | lia].
            exact (inv_res_same_pos _ _ _ _ _ _ _ (proj1 (rem_inv (S i) m Hy)) Hr).
        Qed.

        Lemma Wq_witness : rel_lin_witness (@PrefixView.sel F) T (semi_independent F) (νQ A) Wq.
        Proof.
          split; [| split; [| split; [| split]]].
          - (* legal *)
            destruct (W_vq nE vp db rems H_resp (pi_sorted HI) (pi_rnd HI) (pi_rem_vertex HI) H_done) as (q & Hq).
            exists (map val q). exact (vq_seq [] W0 q Hq).
          - (* distinct keys *)
            unfold Wq. rewrite map_map. apply nodup_map_inj_in; [| exact (W_nodup nE vp rems (pi_rnd HI))].
            intros x y Hx Hy Hk. destruct x as [n | [i n]], y as [m | [i' m]]; cbn in Hk.
            + apply W0_in_enq in Hx, Hy. f_equal. exact (pi_vk_inj HI n m Hwf Hx Hy Hk).
            + exfalso. apply W0_in_enq in Hx. apply W_in_deq in Hy.
              destruct (rem_inv i' m Hy) as [Hi' _]. pose proof (enq_inv n Hx) as Hn. rewrite Hk in Hn.
              pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hn Hi') as Hp. rewrite Hp in Hn.
              destruct (inv_same_pos _ _ _ _ _ _ Hn Hi') as [_ Ho]. discriminate Ho.
            + exfalso. apply W_in_deq in Hx. apply W0_in_enq in Hy.
              destruct (rem_inv i n Hx) as [Hi _]. pose proof (enq_inv m Hy) as Hm. rewrite <- Hk in Hm.
              pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hm Hi) as Hp. rewrite Hp in Hm.
              destruct (inv_same_pos _ _ _ _ _ _ Hm Hi) as [_ Ho]. discriminate Ho.
            + apply W_in_deq in Hx, Hy. destruct (rem_inv i n Hx) as [Hi _]. destruct (rem_inv i' m Hy) as [Hi' _].
              rewrite Hk in Hi. pose proof (wf_inv_uniq _ _ _ _ _ _ Hwf Hi Hi') as <-.
              rewrite (sorted_fst_uniq rems i n m (pi_sorted HI) Hx Hy). reflexivity.
          - (* every operation of the witness occurs, completed, in the trace *)
            intros o Ho. unfold Wq in Ho. apply in_map_iff in Ho as (x & <- & Hx).
            destruct x as [n | [i n]]; unfold occurs; cbn [toOp op_key op_op op_ret].
            + apply W0_in_enq in Hx. pose proof (enq_inv n Hx) as Hi.
              split; [exists (vp n); exact Hi |]. destruct (Hc _ _ _ Hi) as (j & r & Hj). exists j. destruct r. exact Hj.
            + apply W_in_deq in Hx. destruct (rem_inv i n Hx) as [Hi Hr].
              split; [exists i; exact Hi | exists (S i); exact Hr].
          - (* every invocation is in the witness *)
            intros i k op Hi. destruct op as [v |].
            + destruct (pi_enq HI i k v Hi) as (n & Hn & <- & <-). exists (toOp (inl n)). split; [| reflexivity].
              apply in_map. apply W0_in_enq. exact Hn.
            + destruct (deq_in_rems i k Hi) as (n & Hin). exists (toOp (inr (i, n))). split.
              * apply in_map. apply W_in_deq. exact Hin.
              * cbn. exact (dkey_inv _ _ _ _ Hi).
          - (* relaxed happens-before is respected *)
            intros o o' Ho Ho' Hrhb. unfold Wq in Ho, Ho' |- *.
            apply in_map_iff in Ho as (x & <- & Hx). apply in_map_iff in Ho' as (y & <- & Hy).
            apply before_map. exact (rhb_before x y Hx Hy Hrhb).
        Qed.
      End WithDefault.

      Lemma pinv_rel_lin : rel_lin (@PrefixView.sel F) T (semi_independent F) (νQ A).
      Proof.
        destruct (poq_vertices s 0) as [a0 |] eqn:H0.
        - exists (Wq a0). exact (Wq_witness a0).
        - (* no vertex, hence no operation at all *)
          assert (HnE : ~ 0 < nE) by (intros H; exact (proj1 (pi_vertex HI 0) H H0)).
          exists []. split; [| split; [| split; [| split]]].
          + exists []. constructor.
          + constructor.
          + intros o [].
          + intros i k op Hi. exfalso. destruct op as [v |].
            * destruct (pi_enq HI i k v Hi) as (n & Hn & _). apply HnE. lia.
            * destruct (deq_in_rems i k Hi) as (n & Hin). apply HnE.
              pose proof (pi_rem_vertex HI i n Hin). lia.
          + intros o o' [].
      Qed.
    End Complete.

    (** ** The theorem *)

    Theorem poqr_sound : ViewLHL.sound_pres (νQ A) (POQueueR A) poqr_init.
    Proof.
      intros T c Hp Hwf Hc. destruct (pinv_path T c Hp Hwf) as (vk & vp & rems & HI).
      exact (pinv_rel_lin T c vk vp rems HI Hwf Hc).
    Qed.

  End Sound.
End POQueueRSound.
