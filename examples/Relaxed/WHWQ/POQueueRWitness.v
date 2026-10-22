(** * POQueueRWitness: the linearization witness of a partial-order queue history

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P3, combinatorial core.
    Nothing here mentions traces or LTSs.  [POQueueRSound] instantiates
    the section [Witness] with the facts it reads off a complete trace of
    [POQueueR].

    ** Data

    - [nE] enqueues, numbered [0 .. nE - 1] in invocation order; [vp n] is
      the trace position of the invocation of enqueue [n].
    - [db n x]: "the enqueue [n] has responded before position [x]".
    - [rems]: the dequeues, as pairs [(i, n)] of the position [i] of the
      invocation (the response is at [S i]) and the vertex [n] removed, in
      trace order.

    ** Hypotheses (read off [POQueueR] in [POQueueRSound])

    - [B_mono]: invocation positions increase with the vertex number.
    - [B_resp]: a response of an existing enqueue comes after its invocation.
    - [B_sorted], [B_nd], [B_lt]: the dequeues are in increasing position,
      remove distinct vertices, and only existing ones.
    - [B_done]: a removed vertex had responded before its dequeue.
    - [B_min]: minimality at removal: every vertex that had responded before
      the removed vertex was invoked (a DAG predecessor) was removed by an
      earlier dequeue.
    - [B_mon]: [db] is monotone in the position.
    - [B_pos]: no enqueue is invoked at a dequeue's position.

    ** The witness (task brief, choice C4)

    - [Es]: the vertices removed by dequeues, in dequeue order, then the
      never-removed vertices in increasing order.
    - Each enqueue [n] gets the key [max {vp m | m at or before n in Es}]
      ([keyed]); each dequeue [(i, n)] the key [i].
    - [W := merge ek rems]: the two key-sorted lists merged.

    ** Results

    - [W_in_enq], [W_in_deq], [W_nodup]: [W] lists each enqueue and each
      dequeue exactly once.
    - [W_vq]: [W] is a run of the vertex queue: each dequeue removes the head
      of the queue, and the head is its own vertex.
    - [W_rt_ee], [W_rt_ed], [W_rt_de], [W_rt_dd]: [W] respects real time:
      an operation that responded before another was invoked comes first.

    Values and keys are attached in [POQueueRSound]. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.micromega.Lia.

Require Import models.simlin.RelaxedTraceLin.

Import ListNotations.

Module POQueueRWitness.
  Import RelaxedTraceLin.

  (** ** Generic list facts *)

  Lemma before_app_l {A : Type} (l l' : list A) a b : before l a b -> before (l ++ l') a b.
  Proof.
    intros (l1 & l2 & -> & Hb). exists l1, (l2 ++ l'). split.
    - rewrite <- app_assoc. reflexivity.
    - apply in_or_app. left. exact Hb.
  Qed.

  Lemma before_app_r {A : Type} (l l' : list A) a b : before l' a b -> before (l ++ l') a b.
  Proof.
    intros (l1 & l2 & -> & Hb). exists (l ++ l1), l2. split; [| exact Hb].
    rewrite <- app_assoc. reflexivity.
  Qed.

  Lemma before_app_lr {A : Type} (l l' : list A) a b : In a l -> In b l' -> before (l ++ l') a b.
  Proof.
    intros Ha Hb. apply in_split in Ha as (l1 & l2 & ->). exists l1, (l2 ++ l'). split.
    - rewrite <- app_assoc. reflexivity.
    - apply in_or_app. right. exact Hb.
  Qed.

  Lemma before_cons_hd {A : Type} (a b : A) l : In b l -> before (a :: l) a b.
  Proof. intros Hb. exists [], l. split; [reflexivity | exact Hb]. Qed.

  Lemma before_cons_tl {A : Type} (x a b : A) l : before l a b -> before (x :: l) a b.
  Proof. intros (l1 & l2 & -> & Hb). exists (x :: l1), l2. split; [reflexivity | exact Hb]. Qed.

  Lemma before_cons_inv {A : Type} (x a b : A) l :
    before (x :: l) a b -> (a = x /\ In b l) \/ before l a b.
  Proof.
    intros (l1 & l2 & Heq & Hb). destruct l1 as [| y l1]; cbn in Heq; injection Heq as -> Ht.
    - left. subst l. split; [reflexivity | exact Hb].
    - right. exists l1, l2. split; [exact Ht | exact Hb].
  Qed.

  Lemma before_in_l {A : Type} (l : list A) a b : before l a b -> In a l.
  Proof. intros (l1 & l2 & -> & _). apply in_or_app. right. left. reflexivity. Qed.

  Lemma before_in_r {A : Type} (l : list A) a b : before l a b -> In b l.
  Proof. intros (l1 & l2 & -> & Hb). apply in_or_app. right. right. exact Hb. Qed.

  Lemma before_map {A B : Type} (f : A -> B) (l : list A) a b : before l a b -> before (map f l) (f a) (f b).
  Proof.
    intros (l1 & l2 & -> & Hb). exists (map f l1), (map f l2). split.
    - rewrite map_app. reflexivity.
    - apply in_map. exact Hb.
  Qed.

  (** [before] in a duplicate-free list is irreflexive and asymmetric. *)
  Lemma before_irrefl {A : Type} (l : list A) a : NoDup l -> ~ before l a a.
  Proof.
    intros Hnd (l1 & l2 & -> & Ha). apply NoDup_remove_2 in Hnd. apply Hnd.
    apply in_or_app. right. exact Ha.
  Qed.

  Lemma before_asym {A : Type} (l : list A) a b : NoDup l -> before l a b -> ~ before l b a.
  Proof.
    intros Hnd. induction l as [| x l IH]; intros Hab Hba.
    - destruct Hab as (l1 & l2 & Heq & _). destruct l1; discriminate.
    - apply NoDup_cons_iff in Hnd as [Hx Hnd].
      apply before_cons_inv in Hab as [[-> Hb] | Hab]; apply before_cons_inv in Hba as [[Hbx Ha] | Hba].
      + subst b. exact (Hx Hb).
      + exact (Hx (before_in_r _ _ _ Hba)).
      + subst b. exact (Hx (before_in_r _ _ _ Hab)).
      + exact (IH Hnd Hab Hba).
  Qed.

  (** In a list sorted by a strict order on keys, a smaller key comes first. *)
  Lemma sorted_before {A : Type} (key : A -> nat) (l : list A) a b :
    StronglySorted (fun x y => key x < key y) l -> In a l -> In b l -> key a < key b -> before l a b.
  Proof.
    intros Hs. induction Hs as [| x l Hs IH Hall]; intros Ha Hb Hab; [destruct Ha |].
    rewrite Forall_forall in Hall.
    destruct Ha as [<- | Ha], Hb as [<- | Hb].
    - lia.
    - apply before_cons_hd. exact Hb.
    - specialize (Hall a Ha). lia.
    - apply before_cons_tl. exact (IH Ha Hb Hab).
  Qed.

  Lemma before_filter {A : Type} (f : A -> bool) (l : list A) a b :
    before l a b -> f a = true -> f b = true -> before (filter f l) a b.
  Proof.
    intros (l1 & l2 & -> & Hb) Ha Hfb. rewrite filter_app. cbn. rewrite Ha.
    apply before_app_r. apply before_cons_hd. apply filter_In. split; assumption.
  Qed.

  Lemma before_seq start len a b :
    In a (seq start len) -> In b (seq start len) -> a < b -> before (seq start len) a b.
  Proof.
    intros Ha Hb Hab. apply (sorted_before (fun x => x)); [| exact Ha | exact Hb | exact Hab].
    clear. revert start. induction len as [| len IH]; intros start; cbn; constructor; [apply IH |].
    apply Forall_forall. intros x Hx. apply in_seq in Hx. lia.
  Qed.

  Lemma StronglySorted_app_inv {A : Type} (R : A -> A -> Prop) l1 l2 :
    StronglySorted R (l1 ++ l2) -> StronglySorted R l1 /\ StronglySorted R l2.
  Proof.
    induction l1 as [| x l1 IH]; cbn; intros Hs; [split; [constructor | exact Hs] |].
    apply StronglySorted_inv in Hs as [Hs Hall]. destruct (IH Hs) as [H1 H2].
    split; [| exact H2]. constructor; [exact H1 |].
    rewrite Forall_forall in Hall |- *. intros y Hy. apply Hall. apply in_or_app. left. exact Hy.
  Qed.

  Lemma StronglySorted_app_rel {A : Type} (R : A -> A -> Prop) l1 l2 x y :
    StronglySorted R (l1 ++ l2) -> In x l1 -> In y l2 -> R x y.
  Proof.
    induction l1 as [| z l1 IH]; cbn; intros Hs Hx Hy; [destruct Hx |].
    apply StronglySorted_inv in Hs as [Hs Hall]. destruct Hx as [<- | Hx].
    - rewrite Forall_forall in Hall. apply Hall. apply in_or_app. right. exact Hy.
    - exact (IH Hs Hx Hy).
  Qed.

  (** The position of an element in a duplicate-free list is unique. *)
  Lemma nodup_split_len {A : Type} (l l1 l2 : list A) x j :
    NoDup l -> l = l1 ++ x :: l2 -> nth_error l j = Some x -> length l1 = j.
  Proof.
    intros Hnd -> Hj. assert (Hl1 : nth_error (l1 ++ x :: l2) (length l1) = Some x).
    { rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
    apply (proj1 (NoDup_nth_error _) Hnd); [rewrite length_app; cbn; lia | rewrite Hl1, Hj; reflexivity].
  Qed.

  (** ** Splitting a list at a bound *)

  Fixpoint span_lt (p : nat) (ds : list (nat * nat)) : list (nat * nat) * list (nat * nat) :=
    match ds with
    | [] => ([], [])
    | d :: ds' =>
        if fst d <? p then (d :: fst (span_lt p ds'), snd (span_lt p ds')) else ([], ds)
    end.

  Lemma span_lt_app p ds : fst (span_lt p ds) ++ snd (span_lt p ds) = ds.
  Proof.
    induction ds as [| d ds IH]; [reflexivity |]. cbn [span_lt].
    destruct (fst d <? p); cbn [fst snd app]; [rewrite IH |]; reflexivity.
  Qed.

  Lemma span_lt_fst p ds d : In d (fst (span_lt p ds)) -> fst d < p.
  Proof.
    induction ds as [| d0 ds IH]; [intros [] |]. cbn [span_lt].
    destruct (fst d0 <? p) eqn:Hlt; cbn [fst snd]; [| intros []].
    intros [<- | Hd]; [apply Nat.ltb_lt; exact Hlt | exact (IH Hd)].
  Qed.

  Lemma span_lt_snd p ds d :
    StronglySorted (fun a b => fst a < fst b) ds -> In d (snd (span_lt p ds)) -> p <= fst d.
  Proof.
    intros Hs. induction Hs as [| d0 ds Hs IH Hall]; [intros [] |]. cbn [span_lt].
    destruct (fst d0 <? p) eqn:Hlt; cbn [fst snd].
    - exact IH.
    - apply Nat.ltb_ge in Hlt. intros [<- | Hd]; [exact Hlt |].
      rewrite Forall_forall in Hall. specialize (Hall d Hd). lia.
  Qed.

  Lemma span_lt_in p ds d : In d ds <-> In d (fst (span_lt p ds)) \/ In d (snd (span_lt p ds)).
  Proof.
    split; intros H.
    - rewrite <- (span_lt_app p ds) in H. apply in_app_iff in H. exact H.
    - rewrite <- (span_lt_app p ds). apply in_app_iff. exact H.
  Qed.

  Lemma span_lt_sorted p ds :
    StronglySorted (fun a b => fst a < fst b) ds ->
    StronglySorted (fun a b => fst a < fst b) (fst (span_lt p ds)) /\
    StronglySorted (fun a b => fst a < fst b) (snd (span_lt p ds)).
  Proof. intros Hs. apply StronglySorted_app_inv. rewrite span_lt_app. exact Hs. Qed.

  (** ** Merging two key-sorted lists *)

  Fixpoint merge (ek : list (nat * nat)) (ds : list (nat * nat)) : list (nat + nat * nat) :=
    match ek with
    | [] => map inr ds
    | (n, p) :: ek' => map inr (fst (span_lt p ds)) ++ inl n :: merge ek' (snd (span_lt p ds))
    end.

  Lemma merge_in_inl ek ds n : In (inl n) (merge ek ds) <-> In n (map fst ek).
  Proof.
    revert ds. induction ek as [| [n0 p0] ek IH]; intros ds; cbn.
    - split; [intros H; apply in_map_iff in H as (d & Hd & _); discriminate | intros []].
    - rewrite in_app_iff. cbn. rewrite IH. split.
      + intros [H | [H | H]].
        * apply in_map_iff in H as (d & Hd & _). discriminate.
        * injection H as ->. left. reflexivity.
        * right. exact H.
      + intros [-> | H]; [right; left; reflexivity | right; right; exact H].
  Qed.

  Lemma merge_in_inr ek ds d : In (inr d) (merge ek ds) <-> In d ds.
  Proof.
    revert ds. induction ek as [| [n0 p0] ek IH]; intros ds; cbn.
    - rewrite in_map_iff. split.
      + intros (d' & Hd & H). injection Hd as ->. exact H.
      + intros H. exists d. split; [reflexivity | exact H].
    - rewrite in_app_iff. cbn. rewrite IH. rewrite (span_lt_in p0 ds d). rewrite in_map_iff. split.
      + intros [(d' & Hd & H) | [H | H]].
        * injection Hd as ->. left. exact H.
        * discriminate.
        * right. exact H.
      + intros [H | H]; [left; exists d; split; [reflexivity | exact H] | right; right; exact H].
  Qed.

  Lemma nodup_map_inj {A B : Type} (f : A -> B) (l : list A) :
    (forall x y, f x = f y -> x = y) -> NoDup l -> NoDup (map f l).
  Proof.
    intros Hf. induction 1 as [| x l Hx Hnd IH]; cbn; constructor; [| exact IH].
    intros Hin. apply in_map_iff in Hin as (y & Hy & Hin). apply Hf in Hy. subst y. contradiction.
  Qed.

  Lemma inr_inj {A B : Type} (x y : B) : @inr A B x = inr y -> x = y.
  Proof. intros H. injection H. auto. Qed.

  Lemma merge_nodup ek ds :
    NoDup (map fst ek) -> NoDup ds -> NoDup (merge ek ds).
  Proof.
    revert ds. induction ek as [| [n0 p0] ek IH]; intros ds Hne Hnd; cbn.
    - exact (nodup_map_inj inr _ (@inr_inj nat _) Hnd).
    - cbn in Hne. apply NoDup_cons_iff in Hne as [Hn0 Hne].
      rewrite <- (span_lt_app p0 ds) in Hnd.
      pose proof (NoDup_app_remove_r _ _ Hnd) as Hnd1.
      pose proof (NoDup_app_remove_l _ _ Hnd) as Hnd2.
      apply NoDup_app.
      + exact (nodup_map_inj inr _ (@inr_inj nat _) Hnd1).
      + constructor; [| exact (IH _ Hne Hnd2)].
        intros H. apply merge_in_inl in H. exact (Hn0 H).
      + intros x Hx [<- | Hx'].
        * apply in_map_iff in Hx as (d & Hd & _). discriminate.
        * apply in_map_iff in Hx as (d & <- & Hd). apply merge_in_inr in Hx'.
          apply in_split in Hd as (a1 & a2 & Ha).
          rewrite Ha, <- app_assoc in Hnd. cbn in Hnd. apply NoDup_remove_2 in Hnd.
          apply Hnd. apply in_or_app. right. apply in_or_app. right. exact Hx'.
  Qed.

  Section MergeOrder.
    Context (ek : list (nat * nat)) (ds : list (nat * nat)).

    Lemma merge_ee_gen n m :
      before (map fst ek) n m -> before (merge ek ds) (inl n) (inl m).
    Proof.
      clear. revert ds. induction ek as [| [n0 p0] ek' IH]; intros ds Hb.
      - destruct Hb as (l1 & l2 & Heq & _). destruct l1; discriminate.
      - cbn in Hb |- *. apply before_app_r.
        apply before_cons_inv in Hb as [[-> Hm] | Hb].
        + apply before_cons_hd. apply merge_in_inl. exact Hm.
        + apply before_cons_tl. apply IH. exact Hb.
    Qed.
  End MergeOrder.

  Lemma merge_ee ek ds n m :
    before (map fst ek) n m -> before (merge ek ds) (inl n) (inl m).
  Proof. apply merge_ee_gen. Qed.

  Lemma merge_ed ek ds n p d :
    StronglySorted (fun a b => snd a <= snd b) ek ->
    StronglySorted (fun a b => fst a < fst b) ds ->
    In (n, p) ek -> In d ds -> p < fst d -> before (merge ek ds) (inl n) (inr d).
  Proof.
    revert ds. induction ek as [| [n0 p0] ek' IH]; intros ds Hk Hs Hn Hd Hlt; [destruct Hn |].
    cbn. apply StronglySorted_inv in Hk as [Hk Hall]. rewrite Forall_forall in Hall.
    assert (Hdb : In d (snd (span_lt p0 ds))).
    { apply (span_lt_in p0) in Hd as [Hd | Hd]; [| exact Hd].
      exfalso. apply span_lt_fst in Hd.
      destruct Hn as [Hn | Hn]; [injection Hn as <- <-; lia |].
      specialize (Hall _ Hn). cbn in Hall. lia. }
    apply before_app_r. destruct Hn as [Hn | Hn].
    - injection Hn as <- <-. apply before_cons_hd. apply merge_in_inr. exact Hdb.
    - apply before_cons_tl. apply IH; [exact Hk | exact (proj2 (span_lt_sorted p0 ds Hs)) | exact Hn | exact Hdb | exact Hlt].
  Qed.

  Lemma merge_de ek ds n p d :
    StronglySorted (fun a b => snd a <= snd b) ek ->
    StronglySorted (fun a b => fst a < fst b) ds ->
    In (n, p) ek -> In d ds -> fst d < p -> before (merge ek ds) (inr d) (inl n).
  Proof.
    revert ds. induction ek as [| [n0 p0] ek' IH]; intros ds Hk Hs Hn Hd Hlt; [destruct Hn |].
    cbn. apply StronglySorted_inv in Hk as [Hk Hall].
    apply (span_lt_in p0) in Hd as [Hd | Hd].
    - apply before_app_lr; [apply in_map; exact Hd |].
      destruct Hn as [Hn | Hn]; [injection Hn as <- <-; left; reflexivity |].
      right. apply merge_in_inl. apply in_map_iff. exists (n, p). split; [reflexivity | exact Hn].
    - pose proof (span_lt_snd p0 ds d Hs Hd) as Hge.
      destruct Hn as [Hn | Hn]; [injection Hn as <- <-; lia |].
      apply before_app_r. apply before_cons_tl.
      apply IH; [exact Hk | exact (proj2 (span_lt_sorted p0 ds Hs)) | exact Hn | exact Hd | exact Hlt].
  Qed.

  Lemma merge_dd ek ds d d' :
    StronglySorted (fun a b => fst a < fst b) ds ->
    In d ds -> In d' ds -> fst d < fst d' -> before (merge ek ds) (inr d) (inr d').
  Proof.
    revert ds. induction ek as [| [n0 p0] ek' IH]; intros ds Hs Hd Hd' Hlt; cbn.
    - apply before_map. exact (sorted_before fst ds d d' Hs Hd Hd' Hlt).
    - destruct (span_lt_sorted p0 ds Hs) as [Hsa Hsb].
      apply (span_lt_in p0) in Hd as [Hd | Hd]; apply (span_lt_in p0) in Hd' as [Hd' | Hd'].
      + apply before_app_l. apply before_map. exact (sorted_before fst _ d d' Hsa Hd Hd' Hlt).
      + apply before_app_lr; [apply in_map; exact Hd |]. right. apply merge_in_inr. exact Hd'.
      + exfalso. pose proof (span_lt_snd p0 ds d Hs Hd). pose proof (span_lt_fst p0 ds d' Hd'). lia.
      + apply before_app_r. apply before_cons_tl. exact (IH _ Hsb Hd Hd' Hlt).
  Qed.

  (** ** The vertex queue *)

  Inductive vq_run : list nat -> list (nat + nat * nat) -> list nat -> Prop :=
  | vq_nil q : vq_run q [] q
  | vq_enq q n W q' : vq_run (q ++ [n]) W q' -> vq_run q (inl n :: W) q'
  | vq_deq q i n W q' : vq_run q W q' -> vq_run (n :: q) (inr (i, n) :: W) q'.

  Lemma vq_run_app q W1 q1 W2 q2 : vq_run q W1 q1 -> vq_run q1 W2 q2 -> vq_run q (W1 ++ W2) q2.
  Proof.
    induction 1 as [q | q n W q' H IH | q i n W q' H IH]; intros H2; cbn.
    - exact H2.
    - apply vq_enq. exact (IH H2).
    - apply vq_deq. exact (IH H2).
  Qed.

  Lemma vq_deqs (ds : list (nat * nat)) q :
    map snd ds = firstn (length ds) q ->
    vq_run q (map inr ds) (skipn (length ds) q).
  Proof.
    revert q. induction ds as [| [i n] ds IH]; intros q Hq; cbn.
    - apply vq_nil.
    - destruct q as [| x q]; cbn in Hq; [discriminate |].
      injection Hq as -> Hq. apply vq_deq. exact (IH q Hq).
  Qed.

  Lemma sorted_nth_lt {A : Type} (R : A -> A -> Prop) (l : list A) i j x y :
    StronglySorted R l -> i < j -> nth_error l i = Some x -> nth_error l j = Some y -> R x y.
  Proof.
    intros Hs. revert i j. induction Hs as [| z l Hs IH Hall]; intros i j Hij Hi Hj; [destruct i; discriminate |].
    destruct i as [| i]; destruct j as [| j]; cbn in Hi, Hj; try lia.
    - injection Hi as <-. rewrite Forall_forall in Hall. apply Hall. exact (nth_error_In _ _ Hj).
    - apply (IH i j); [lia | exact Hi | exact Hj].
  Qed.

  Lemma in_firstn_nth {A : Type} (l : list A) n x :
    In x (firstn n l) -> exists k, k < n /\ nth_error l k = Some x.
  Proof.
    intros Hx. apply In_nth_error in Hx as (k & Hk). rewrite nth_error_firstn in Hk.
    destruct (k <? n) eqn:Hlt; [| discriminate]. apply Nat.ltb_lt in Hlt. exists k. auto.
  Qed.

  Lemma nth_error_map_fst {A B : Type} (l : list (A * B)) j x :
    nth_error (map fst l) j = Some x -> exists y, nth_error l j = Some (x, y).
  Proof.
    rewrite nth_error_map. destruct (nth_error l j) as [[a b] |]; cbn; [| discriminate].
    intros H. injection H as ->. exists b. reflexivity.
  Qed.

  (** A merge is a run of the vertex queue when the dequeues, in order,
      remove the vertices in the order [Erem ++ map fst ek] (the queue
      content [Erem] followed by the enqueues still to come), and every
      dequeue that removes a vertex still to come gets a larger key than
      that vertex. *)
  Lemma merge_vq ek ds Erem :
    StronglySorted (fun a b => snd a <= snd b) ek ->
    StronglySorted (fun a b => fst a < fst b) ds ->
    map snd ds = firstn (length ds) (Erem ++ map fst ek) ->
    (forall j d, nth_error ds j = Some d -> length Erem <= j ->
       exists p, nth_error ek (j - length Erem) = Some (snd d, p) /\ p < fst d) ->
    exists q, vq_run Erem (merge ek ds) q.
  Proof.
    revert ds Erem. induction ek as [| [n0 p0] ek' IH]; intros ds Erem Hk Hs Hm Hb.
    - cbn in Hm |- *. rewrite app_nil_r in Hm. exists (skipn (length ds) Erem). exact (vq_deqs ds Erem Hm).
    - cbn [merge].
      set (a := fst (span_lt p0 ds)). set (b := snd (span_lt p0 ds)).
      assert (Hab : a ++ b = ds) by apply span_lt_app.
      apply StronglySorted_inv in Hk as [Hk Hall]. rewrite Forall_forall in Hall.
      set (L' := map fst ((n0, p0) :: ek')) in Hm.
      (* the dequeues of [a] remove elements of [Erem] *)
      assert (Hla : length a <= length Erem).
      { destruct (Nat.le_gt_cases (length a) (length Erem)) as [H | H]; [exact H | exfalso].
        destruct (nth_error a (length Erem)) as [d |] eqn:Hd; [| apply nth_error_None in Hd; lia].
        pose proof (span_lt_fst p0 ds d (nth_error_In _ _ Hd)) as Hdlt.
        assert (Hdds : nth_error ds (length Erem) = Some d).
        { rewrite <- Hab. rewrite nth_error_app1 by lia. exact Hd. }
        destruct (Hb _ _ Hdds (le_n _)) as (p & Hp & Hplt).
        rewrite Nat.sub_diag in Hp. cbn in Hp. injection Hp as _ Hp'. lia. }
      assert (Hlds : length ds = length a + length b) by (rewrite <- Hab, length_app; reflexivity).
      assert (Hma : map snd a = firstn (length a) Erem).
      { assert (H1 : map snd a = firstn (length a) (map snd ds)).
        { rewrite <- Hab, map_app, firstn_app, length_map, Nat.sub_diag, firstn_0, app_nil_r.
          rewrite firstn_all2 by (rewrite length_map; lia). reflexivity. }
        rewrite H1, Hm, firstn_firstn. replace (Nat.min (length a) (length ds)) with (length a) by lia.
        rewrite firstn_app. replace (length a - length Erem) with 0 by lia. rewrite firstn_0, app_nil_r.
        reflexivity. }
      pose proof (vq_deqs a Erem Hma) as Hra.
      set (Erem' := skipn (length a) Erem ++ [n0]).
      assert (HL : Erem' ++ map fst ek' = skipn (length a) (Erem ++ L')).
      { unfold Erem', L'. rewrite skipn_app. replace (length a - length Erem) with 0 by lia.
        cbn [map fst skipn]. rewrite <- app_assoc. reflexivity. }
      assert (Hmb : map snd b = firstn (length b) (Erem' ++ map fst ek')).
      { rewrite HL. assert (H1 : map snd b = skipn (length a) (map snd ds)).
        { rewrite <- Hab, map_app, skipn_app, length_map, Nat.sub_diag.
          rewrite skipn_all2 by (rewrite length_map; lia). reflexivity. }
        rewrite H1, Hm, skipn_firstn_comm. f_equal. lia. }
      assert (HlE' : length Erem' = length Erem - length a + 1)
        by (unfold Erem'; rewrite length_app, length_skipn; reflexivity).
      assert (Hbb : forall j d, nth_error b j = Some d -> length Erem' <= j ->
                 exists p, nth_error ek' (j - length Erem') = Some (snd d, p) /\ p < fst d).
      { intros j d Hj Hle.
        assert (Hjds : nth_error ds (length a + j) = Some d).
        { rewrite <- Hab, nth_error_app2 by lia. replace (length a + j - length a) with j by lia. exact Hj. }
        destruct (Hb _ _ Hjds) as (p & Hp & Hlt); [lia |].
        exists p. split; [| exact Hlt].
        replace (length a + j - length Erem) with (S (j - length Erem')) in Hp by lia.
        cbn in Hp. exact Hp. }
      destruct (IH b Erem' Hk (proj2 (span_lt_sorted p0 ds Hs)) Hmb Hbb) as (q & Hq).
      exists q. apply (vq_run_app _ _ _ _ _ Hra). apply vq_enq. exact Hq.
  Qed.

  (** ** The witness *)

  Section Witness.
    Variable nE : nat.
    Variable vp : nat -> nat.
    Variable db : nat -> nat -> Prop.
    Variable rems : list (nat * nat).

    Hypothesis B_mono : forall n m, n < m -> m < nE -> vp n < vp m.
    Hypothesis B_resp : forall n x, n < nE -> db n x -> vp n < x.
    Hypothesis B_sorted : StronglySorted (fun a b => fst a < fst b) rems.
    Hypothesis B_nd : NoDup (map snd rems).
    Hypothesis B_lt : forall i n, In (i, n) rems -> n < nE.
    Hypothesis B_done : forall i n, In (i, n) rems -> db n i.
    Hypothesis B_min : forall i n m, In (i, n) rems -> m < nE -> db m (vp n) ->
      exists i', i' < i /\ In (i', m) rems.
    Hypothesis B_mon : forall n x y, db n x -> x <= y -> db n y.
    Hypothesis B_pos : forall i n m, In (i, n) rems -> m < nE -> vp m <> i.

    Definition remv : list nat := map snd rems.
    Definition removed (n : nat) : bool := existsb (Nat.eqb n) remv.
    Definition undeq : list nat := filter (fun n => negb (removed n)) (seq 0 nE).
    Definition Es : list nat := remv ++ undeq.

    Fixpoint keyed (l : list nat) (acc : nat) : list (nat * nat) :=
      match l with
      | [] => []
      | n :: l' => (n, Nat.max acc (vp n)) :: keyed l' (Nat.max acc (vp n))
      end.

    Definition ek : list (nat * nat) := keyed Es 0.
    Definition W : list (nat + nat * nat) := merge ek rems.

    Lemma removed_spec n : removed n = true <-> In n remv.
    Proof.
      unfold removed. rewrite existsb_exists. split.
      - intros (x & Hx & Heq). apply Nat.eqb_eq in Heq. subst x. exact Hx.
      - intros Hn. exists n. split; [exact Hn | apply Nat.eqb_refl].
    Qed.

    Lemma remv_lt n : In n remv -> n < nE.
    Proof. unfold remv. intros Hn. apply in_map_iff in Hn as ([i m] & <- & Hin). exact (B_lt i m Hin). Qed.

    Lemma not_removed n : ~ In n remv -> negb (removed n) = true.
    Proof.
      intros Hn. apply negb_true_iff. destruct (removed n) eqn:Hr; [| reflexivity].
      apply removed_spec in Hr. contradiction.
    Qed.

    Lemma undeq_spec n : In n undeq <-> n < nE /\ ~ In n remv.
    Proof.
      unfold undeq. rewrite filter_In, in_seq, negb_true_iff. split.
      - intros [[_ Hlt] Hr]. split; [lia |]. intros Hn. apply removed_spec in Hn. congruence.
      - intros [Hlt Hn]. split; [lia |]. apply negb_true_iff. exact (not_removed n Hn).
    Qed.

    Lemma Es_in n : In n Es <-> n < nE.
    Proof.
      unfold Es. rewrite in_app_iff, undeq_spec. split.
      - intros [Hn | [Hn _]]; [exact (remv_lt n Hn) | exact Hn].
      - intros Hn. destruct (in_dec Nat.eq_dec n remv) as [H | H]; [left; exact H | right; split; assumption].
    Qed.

    Lemma Es_nodup : NoDup Es.
    Proof.
      unfold Es. apply NoDup_app.
      - exact B_nd.
      - apply NoDup_filter. apply seq_NoDup.
      - intros n Hr Hu. apply undeq_spec in Hu as [_ Hn]. exact (Hn Hr).
    Qed.

    Lemma keyed_fst l a : map fst (keyed l a) = l.
    Proof. revert a. induction l as [| n l IH]; intros a; cbn; [reflexivity | f_equal; apply IH]. Qed.

    Lemma keyed_ge l a n p : In (n, p) (keyed l a) -> vp n <= p /\ a <= p.
    Proof.
      revert a. induction l as [| m l IH]; intros a; cbn; [intros [] |].
      pose proof (Nat.le_max_l a (vp m)). pose proof (Nat.le_max_r a (vp m)).
      intros [Heq | Hin].
      - injection Heq as <- <-. lia.
      - destruct (IH _ Hin). lia.
    Qed.

    Lemma keyed_sorted l a : StronglySorted (fun x y => snd x <= snd y) (keyed l a).
    Proof.
      revert a. induction l as [| m l IH]; intros a; cbn; constructor; [apply IH |].
      apply Forall_forall. intros [n p] Hin. cbn. exact (proj2 (keyed_ge _ _ _ _ Hin)).
    Qed.

    Lemma keyed_lt l a x n p :
      NoDup l -> a < x ->
      (forall l1 l2, l = l1 ++ n :: l2 -> forall m, In m (l1 ++ [n]) -> vp m < x) ->
      In (n, p) (keyed l a) -> p < x.
    Proof.
      revert a. induction l as [| m l IH]; intros a Hnd Ha Hpre; cbn; [intros [] |].
      apply NoDup_cons_iff in Hnd as [Hm Hnd].
      intros [Heq | Hin].
      - injection Heq as <- <-.
        assert (Hv : vp m < x) by (apply (Hpre [] l eq_refl); left; reflexivity).
        apply Nat.max_lub_lt; assumption.
      - assert (Hnl : In n l).
        { rewrite <- (keyed_fst l (Nat.max a (vp m))). apply in_map_iff. exists (n, p). auto. }
        apply in_split in Hnl as (l1 & l2 & Hl).
        assert (Hvm : vp m < x).
        { apply (Hpre (m :: l1) l2); [rewrite Hl; reflexivity | left; reflexivity]. }
        apply (IH (Nat.max a (vp m)) Hnd); [apply Nat.max_lub_lt; assumption | | exact Hin].
        intros l1' l2' Hl' m' Hm'. apply (Hpre (m :: l1') l2'); [rewrite Hl'; reflexivity | right; exact Hm'].
    Qed.

    Lemma ek_in n : In n Es -> exists p, In (n, p) ek.
    Proof.
      intros Hn. unfold ek. rewrite <- (keyed_fst Es 0) in Hn. apply in_map_iff in Hn as ([n' p] & Heq & Hin).
      cbn in Heq. subst n'. exists p. exact Hin.
    Qed.

    Lemma rems_before i n i' m : In (i, n) rems -> In (i', m) rems -> i < i' -> before Es n m.
    Proof.
      intros H1 H2 Hlt. apply before_app_l. unfold remv.
      exact (before_map snd rems (i, n) (i', m) (sorted_before fst rems (i, n) (i', m) B_sorted H1 H2 Hlt)).
    Qed.

    Lemma vp_lt_inv n m : n < nE -> m < nE -> vp n < vp m -> n < m.
    Proof.
      intros Hn Hm H. destruct (Nat.lt_trichotomy n m) as [Hlt | [-> | Hgt]]; [exact Hlt | lia |].
      pose proof (B_mono m n Hgt Hn). lia.
    Qed.

    (** Real-time order between enqueues is respected by [Es]. *)
    Lemma Es_before_db n m : n < nE -> m < nE -> db n (vp m) -> before Es n m.
    Proof.
      intros Hn Hm Hdb.
      destruct (in_dec Nat.eq_dec m remv) as [Hmr | Hmr].
      - unfold remv in Hmr. apply in_map_iff in Hmr as ([i m'] & Heq & Hin). cbn in Heq. subst m'.
        destruct (B_min i m n Hin Hn Hdb) as (i' & Hlt & Hin').
        exact (rems_before i' n i m Hin' Hin Hlt).
      - assert (Hmu : In m undeq) by (apply undeq_spec; split; assumption).
        destruct (in_dec Nat.eq_dec n remv) as [Hnr | Hnr].
        + apply before_app_lr; assumption.
        + apply before_app_r. unfold undeq. apply before_filter.
          * apply before_seq; [apply in_seq; lia | apply in_seq; lia |].
            exact (vp_lt_inv n m Hn Hm (B_resp n (vp m) Hn Hdb)).
          * exact (not_removed n Hnr).
          * exact (not_removed m Hmr).
    Qed.

    Lemma W_in_enq n : In (inl n) W <-> n < nE.
    Proof. unfold W. rewrite merge_in_inl. unfold ek. rewrite keyed_fst. apply Es_in. Qed.

    Lemma W_in_deq d : In (inr d) W <-> In d rems.
    Proof. unfold W. apply merge_in_inr. Qed.

    Lemma W_nodup : NoDup W.
    Proof.
      unfold W. apply merge_nodup.
      - unfold ek. rewrite keyed_fst. exact Es_nodup.
      - exact (NoDup_map_inv snd rems B_nd).
    Qed.

    Lemma W_rt_ee n m : n < nE -> m < nE -> db n (vp m) -> before W (inl n) (inl m).
    Proof.
      intros Hn Hm Hdb. unfold W. apply merge_ee. unfold ek. rewrite keyed_fst.
      exact (Es_before_db n m Hn Hm Hdb).
    Qed.

    (** The key of an enqueue is below every dequeue position at which it
        has responded. *)
    Lemma key_lt_resp n p i r : n < nE -> In (n, p) ek -> In (i, r) rems -> db n i -> p < i.
    Proof.
      intros Hn Hp Hir Hdb. unfold ek in Hp.
      apply (keyed_lt Es 0 i n p Es_nodup); [| | exact Hp].
      - pose proof (B_resp _ _ (B_lt _ _ Hir) (B_done _ _ Hir)). lia.
      - intros l1 l2 Hl m Hm.
        assert (HmE : m < nE).
        { apply Es_in. rewrite Hl. apply in_app_or in Hm as [H | [<- | []]];
            apply in_or_app; [left; exact H | right; left; reflexivity]. }
        destruct (Nat.lt_ge_cases (vp m) i) as [Hlt | Hge]; [exact Hlt | exfalso].
        pose proof (B_pos i r m Hir HmE) as Hne.
        assert (Hdbm : db n (vp m)) by (apply (B_mon n i); [exact Hdb | lia]).
        pose proof (Es_before_db n m Hn HmE Hdbm) as Hbef.
        apply in_app_or in Hm as [Hm | [Hm | []]].
        + apply (before_asym Es n m Es_nodup Hbef). rewrite Hl. apply before_app_lr; [exact Hm | left; reflexivity].
        + subst m. pose proof (B_resp n (vp n) Hn Hdbm). lia.
    Qed.

    Lemma W_rt_ed n i r : n < nE -> In (i, r) rems -> db n i -> before W (inl n) (inr (i, r)).
    Proof.
      intros Hn Hir Hdb. destruct (ek_in n (proj2 (Es_in n) Hn)) as (p & Hp).
      unfold W. apply (merge_ed ek rems n p (i, r)); [apply keyed_sorted | exact B_sorted | exact Hp | exact Hir |].
      cbn. exact (key_lt_resp n p i r Hn Hp Hir Hdb).
    Qed.

    Lemma W_rt_de i r m : In (i, r) rems -> m < nE -> S i < vp m -> before W (inr (i, r)) (inl m).
    Proof.
      intros Hir Hm Hlt. destruct (ek_in m (proj2 (Es_in m) Hm)) as (p & Hp).
      unfold W. apply (merge_de ek rems m p (i, r)); [apply keyed_sorted | exact B_sorted | exact Hp | exact Hir |].
      cbn. pose proof (proj1 (keyed_ge _ _ _ _ Hp)). lia.
    Qed.

    Lemma W_rt_dd i r i' r' :
      In (i, r) rems -> In (i', r') rems -> S i < i' -> before W (inr (i, r)) (inr (i', r')).
    Proof. intros H1 H2 Hlt. unfold W. apply merge_dd; [exact B_sorted | exact H1 | exact H2 | cbn; lia]. Qed.

    (** The removed vertex of the [j]-th dequeue is the [j]-th element of
        [Es], and its key is below the dequeue's position. *)
    Lemma ek_rem j d : nth_error rems j = Some d -> exists p, nth_error ek j = Some (snd d, p) /\ p < fst d.
    Proof.
      intros Hj.
      assert (HjE : nth_error Es j = Some (snd d)).
      { unfold Es, remv. rewrite nth_error_app1 by (rewrite length_map; apply nth_error_Some; congruence).
        rewrite nth_error_map, Hj. reflexivity. }
      assert (Hek : nth_error (map fst ek) j = Some (snd d)) by (unfold ek; rewrite keyed_fst; exact HjE).
      destruct (nth_error_map_fst ek j (snd d) Hek) as (p & Hp).
      exists p. split; [exact Hp |].
      assert (Hd : In d rems) by exact (nth_error_In _ _ Hj).
      destruct d as [i n]. cbn in *.
      apply (keyed_lt Es 0 i n p Es_nodup); [| | exact (nth_error_In _ _ Hp)].
      - pose proof (B_resp _ _ (B_lt _ _ Hd) (B_done _ _ Hd)). lia.
      - intros l1 l2 Hl m Hm.
        pose proof (nodup_split_len Es l1 l2 n j Es_nodup Hl HjE) as Hlen.
        assert (Hl1 : l1 = firstn j Es).
        { rewrite Hl, <- Hlen, firstn_app, Nat.sub_diag, firstn_0, app_nil_r, firstn_all. reflexivity. }
        apply in_app_or in Hm as [Hm | [Hm | []]].
        + rewrite Hl1 in Hm. apply in_firstn_nth in Hm as (k & Hk & Hkm).
          assert (Hkr : nth_error remv k = Some m).
          { unfold Es in Hkm. rewrite nth_error_app1 in Hkm; [exact Hkm |].
            unfold remv. rewrite length_map.
            assert (Hjl : j < length rems) by (apply nth_error_Some; rewrite Hj; discriminate). lia. }
          unfold remv in Hkr. rewrite nth_error_map in Hkr.
          destruct (nth_error rems k) as [[i' m'] |] eqn:Hk'; cbn in Hkr; [| discriminate].
          injection Hkr as ->.
          pose proof (sorted_nth_lt _ rems k j (i', m) (i, n) B_sorted Hk Hk' Hj) as Hii. cbn in Hii.
          pose proof (B_resp _ _ (B_lt _ _ (nth_error_In _ _ Hk')) (B_done _ _ (nth_error_In _ _ Hk'))). lia.
        + subst m. exact (B_resp _ _ (B_lt _ _ Hd) (B_done _ _ Hd)).
    Qed.

    Lemma W_vq : exists q, vq_run [] W q.
    Proof.
      unfold W. apply merge_vq; [apply keyed_sorted | exact B_sorted | |].
      - cbn [app]. unfold ek. rewrite keyed_fst. unfold Es. rewrite firstn_app.
        replace (length rems - length remv) with 0 by (unfold remv; rewrite length_map; lia).
        rewrite firstn_0, app_nil_r. unfold remv. rewrite firstn_all2 by (rewrite length_map; lia).
        reflexivity.
      - intros j d Hj _. cbn [length]. rewrite Nat.sub_0_r. exact (ek_rem j d Hj).
    Qed.
  End Witness.

End POQueueRWitness.
