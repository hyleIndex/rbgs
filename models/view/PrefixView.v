(** * The paper's prefix views (App. I), and what they need to be sound

    This file states Defs. I.2–I.4 of the paper for complete relaxed
    traces, in the representation of [RelaxedTraceLin]:

    - a stamp [H k] for every call key (Def. I.2(2): invocation and
      response share the stamp);
    - [po_ok]: same-thread invocations that are not semi-independent get
      increasing stamps (Def. I.2(3));
    - [lin_h]: the timestamp-ordered prefix witnesses of Def. I.3, where
      the completion appends responses to some pending invocations and
      drops the others;
    - [view]: Def. I.4, every prefix of the trace has such a witness.

    Def. I.2 places no constraint between operations of different threads.
    [view_rt] adds one: if [o] responds before [o'] is invoked, then
    [H o < H o'] ([rt_ok]).

    Results:

    - [view_rt_rel_lin], [rel_lin_view_rt], [rel_lin_iff_view_rt]: on
      complete well-formed traces, relaxed linearizability holds iff there
      is a real-time-respecting prefix view.  The direction from [rel_lin]
      (Prop. I.10) needs no view-based compatibility: the stamp of an
      operation is its position in the witness, and the witness for a
      prefix is the shortest prefix of the witness that contains every
      operation completed so far.
    - [thm_I11_rt]: Thm. I.11 with [view_rt] in place of [view], for
      complete executions.  It follows from the two directions above.
    - [rel_lin_view_rt_chain]: moreover the prefix witnesses form a chain
      of prefixes of one witness.  No operation is ever inserted below an
      operation already justified, which is the only situation in which
      view-based compatibility (Def. I.1) is used.
    - Part 2 ([Counterexample]): without [rt_ok], Thm. I.11 fails.  The
      implementation [write(v) = E.wrt(v); read() = return 0] of a register
      whose reads may overtake earlier writes of the same thread has a
      prefix view for every overlay trace ([zero_reads_view]), so the
      premise of Thm. I.11 holds.  But the execution "thread 1 writes 1
      and returns; then thread 2 reads 0" has a relaxed linearizable
      underlay and an overlay that is not relaxed linearizable
      ([counterexample_I11]).
    - Part 3 ([Compat]): Def. I.1 as printed fails for the register
      ([reg_not_compat_printed]); with the hypothesis that the inserted
      operation overtakes a later operation of its own thread, it holds
      ([reg_compat_fixed]). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Relations.Relation_Definitions.
Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedStamping.
Import ListNotations.

Module PrefixView.
  Import RelaxedSig RelaxedLTSSpec RelaxedTraceLin.

  (** ** Generic list facts *)

  Lemma nth_firstn {A : Type} (l : list A) n i x :
    nth_error (firstn n l) i = Some x <-> i < n /\ nth_error l i = Some x.
  Proof.
    rewrite nth_error_firstn. destruct (Nat.ltb i n) eqn:Hb.
    - apply Nat.ltb_lt in Hb. tauto.
    - apply Nat.ltb_ge in Hb. split; [discriminate | intros [H _]; lia].
  Qed.

  Lemma NoDup_firstn {A : Type} (l : list A) n : NoDup l -> NoDup (firstn n l).
  Proof.
    intros H. rewrite <- (firstn_skipn n l) in H. exact (NoDup_app_remove_r _ _ H).
  Qed.

  Lemma In_firstn {A : Type} (l : list A) n x : In x (firstn n l) -> In x l.
  Proof. intros H. rewrite <- (firstn_skipn n l). apply in_or_app. left. exact H. Qed.

  Lemma StronglySorted_firstn {A : Type} (R : A -> A -> Prop) l n :
    StronglySorted R l -> StronglySorted R (firstn n l).
  Proof.
    revert n. induction l as [|a l IH]; intros n HS; destruct n; simpl; try constructor.
    - apply StronglySorted_inv in HS as [HS HF]. exact (IH n HS).
    - apply StronglySorted_inv in HS as [HS HF]. rewrite Forall_forall in *.
      intros x Hx. apply HF. exact (In_firstn _ _ _ Hx).
  Qed.

  Section Def.
    Context {E : RelaxedSig.t}.
    Context (indep : relation (Sig.op (RelaxedSig.effect E))).
    Context (nu : list (Op E) -> Prop).

    Definition sel (e : ThreadEvent E) : option (ThreadEvent E) := Some e.

    Abbreviation inv L := (inv_at sel L).
    Abbreviation res L := (res_at sel L).

    (** Concurrent plays (Def. I.2(1)): each key is invoked at most once
        and responds at most once, after its invocation. *)
    Definition wf (L : list (ThreadEvent E)) : Prop :=
      (forall i j k op op', inv L i k op -> inv L j k op' -> i = j) /\
      (forall i j k op op' (r : Sig.ar op) (r' : Sig.ar op'),
          res L i k op r -> res L j k op' r' -> i = j) /\
      (forall j k op (r : Sig.ar op), res L j k op r -> exists i, i < j /\ inv L i k op).

    Definition complete (L : list (ThreadEvent E)) : Prop :=
      forall i k op, inv L i k op -> exists j (r : Sig.ar op), res L j k op r.

    (** Def. I.2(3). *)
    Definition po_ok (H : CallKey E -> nat) (L : list (ThreadEvent E)) : Prop :=
      forall i j k k' op op', inv L i k op -> inv L j k' op' -> i < j ->
        fst k = fst k' -> ~ indep op op' -> H k < H k'.

    (** Real time: not part of Def. I.2. *)
    Definition rt_ok (H : CallKey E -> nat) (L : list (ThreadEvent E)) : Prop :=
      forall i j k k' op op' (r : Sig.ar op), res L i k op r -> inv L j k' op' -> i < j -> H k < H k'.

    (** Def. I.3: [t] is a legal sequential witness of some completion of
        [p], and it orders operations by stamp. *)
    Definition lin_h (H : CallKey E -> nat) (p : list (ThreadEvent E)) (t : list (Op E)) : Prop :=
      nu t /\ NoDup (map op_key t) /\
      (forall o, In o t ->
         (exists i, inv p i (op_key o) (op_op o)) /\
         (forall j r, res p j (op_key o) (op_op o) r -> r = op_ret o)) /\
      (forall j k op (r : Sig.ar op), res p j k op r -> In (Build_Op k op r) t) /\
      (forall o o', In o t -> In o' t -> H (op_key o) < H (op_key o') -> before t o o').

    (** Def. I.4. *)
    Definition view (H : CallKey E -> nat) (L : list (ThreadEvent E)) : Prop :=
      wf L /\ po_ok H L /\ forall n, n <= length L -> exists t, lin_h H (firstn n L) t.

    Definition view_rt (H : CallKey E -> nat) (L : list (ThreadEvent E)) : Prop :=
      view H L /\ rt_ok H L.

    (** ** Events at an index *)

    Lemma inv_det L i k k' op op' : inv L i k op -> inv L i k' op' -> k = k' /\ op = op'.
    Proof.
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-.
      unfold sel in *.
      assert (Hev : Build_ThreadEvent (fst k) (InvEv (snd k) op) =
                    Build_ThreadEvent (fst k') (InvEv (snd k') op')) by congruence.
      pose proof (f_equal (te_tid E) Hev) as Ht. pose proof (f_equal (te_ev E) Hev) as Hv.
      pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Ho.
      simpl in Ht, Hh, Ho. split; [|exact Ho]. destruct k, k'; simpl in *; congruence.
    Qed.

    Lemma res_det L i k k' op op' (r : Sig.ar op) (r' : Sig.ar op') :
      res L i k op r -> res L i k' op' r' -> k = k' /\ op = op'.
    Proof.
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-.
      unfold sel in *.
      assert (Hev : Build_ThreadEvent (fst k) (ResEv (snd k) op r) =
                    Build_ThreadEvent (fst k') (ResEv (snd k') op' r')) by congruence.
      pose proof (f_equal (te_tid E) Hev) as Ht. pose proof (f_equal (te_ev E) Hev) as Hv.
      pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Ho.
      simpl in Ht, Hh, Ho. split; [|exact Ho]. destruct k, k'; simpl in *; congruence.
    Qed.

    Lemma res_ret L i k op (r r' : Sig.ar op) : res L i k op r -> res L i k op r' -> r = r'.
    Proof.
      intros (x & Hx & Hs) (x' & Hx' & Hs'). rewrite Hx in Hx'. injection Hx' as <-.
      unfold sel in *.
      assert (Hev : Build_ThreadEvent (fst k) (ResEv (snd k) op r) =
                    Build_ThreadEvent (fst k) (ResEv (snd k) op r')) by congruence.
      pose proof (f_equal (te_ev E) Hev) as Hv. simpl in Hv.
      exact (ResEvInversion _ _ _ _ Hv).
    Qed.

    Lemma inv_firstn L n i k op : inv (firstn n L) i k op <-> i < n /\ inv L i k op.
    Proof.
      unfold inv_at. split.
      - intros (x & Hx & Hs). apply nth_firstn in Hx as [Hi Hx]. eauto.
      - intros [Hi (x & Hx & Hs)]. exists x. split; [apply nth_firstn; auto | exact Hs].
    Qed.

    Lemma res_firstn L n i k op r : res (firstn n L) i k op r <-> i < n /\ res L i k op r.
    Proof.
      unfold res_at. split.
      - intros (x & Hx & Hs). apply nth_firstn in Hx as [Hi Hx]. eauto.
      - intros [Hi (x & Hx & Hs)]. exists x. split; [apply nth_firstn; auto | exact Hs].
    Qed.

    (** ** From a real-time-respecting view to relaxed linearizability *)

    Theorem view_rt_rel_lin H L : complete L -> view_rt H L -> rel_lin sel L indep nu.
    Proof.
      intros Hc ((Hwf & Hpo & Hpre) & Hrt).
      destruct (Hpre (length L) (le_n _)) as (t & Ht). rewrite firstn_all in Ht.
      destruct Ht as (Hnu & Hnd & Hin & Hres & Hord).
      exists t. split; [exact Hnu|]. split; [exact Hnd|]. split; [|split].
      - intros o Ho. destruct (Hin o Ho) as [Hi Hr]. split; [exact Hi|].
        destruct Hi as (i & Hi). destruct (Hc _ _ _ Hi) as (j & r & Hj).
        exists j. rewrite <- (Hr j r Hj). exact Hj.
      - intros i k op Hi. destruct (Hc _ _ _ Hi) as (j & r & Hj).
        exists (Build_Op k op r). split; [exact (Hres _ _ _ _ Hj) | reflexivity].
      - intros o o' Ho Ho' [(i & j & Hi & Hj & Hij) | (Hth & i & j & Hi & Hj & Hij & Hn)].
        + apply Hord; [exact Ho | exact Ho' | exact (Hrt _ _ _ _ _ _ _ Hi Hj Hij)].
        + apply Hord; [exact Ho | exact Ho' | exact (Hpo _ _ _ _ _ _ Hi Hj Hij Hth Hn)].
    Qed.

    (** ** From relaxed linearizability to a real-time-respecting view *)

    Section FromRelLin.
      Context (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'}).
      Context (nu_prefix : forall l1 l2, nu (l1 ++ l2) -> nu l1).
      Context (L : list (ThreadEvent E)) (Hwf : wf L) (Hc : complete L).
      Context (W : list (Op E)) (HW : rel_lin_witness sel L indep nu W).

      Definition Hpos (k : CallKey E) : nat := RelaxedStamping.index key_dec k (map op_key W).

      Lemma W_nd : NoDup (map op_key W). Proof. exact (proj1 (proj2 HW)). Qed.
      Lemma W_occ o : In o W -> occurs sel L o. Proof. exact (proj1 (proj2 (proj2 HW)) o). Qed.
      Lemma W_cov i k op : inv L i k op -> exists o, In o W /\ op_key o = k.
      Proof. exact (proj1 (proj2 (proj2 (proj2 HW))) i k op). Qed.
      Lemma W_ord o o' : In o W -> In o' W -> rhb sel L indep o o' -> before W o o'.
      Proof. exact (proj2 (proj2 (proj2 (proj2 HW))) o o'). Qed.

      Lemma Hpos_rhb o o' :
        In o W -> In o' W -> rhb sel L indep o o' -> Hpos (op_key o) < Hpos (op_key o').
      Proof.
        intros Ho Ho' Hr. exact (RelaxedStamping.before_pos key_dec W o o' W_nd (W_ord o o' Ho Ho' Hr)).
      Qed.

      (** The witness operation of an invocation. *)
      Lemma find_op i k op :
        inv L i k op -> exists o, In o W /\ op_key o = k /\ op_op o = op /\ inv L i k (op_op o).
      Proof.
        intros Hi. destruct (W_cov _ _ _ Hi) as (o & Ho & Hk).
        destruct (W_occ o Ho) as [(i0 & Hi0) _]. rewrite Hk in Hi0.
        pose proof (proj1 Hwf _ _ _ _ _ Hi Hi0) as ->.
        destruct (inv_det _ _ _ _ _ _ Hi Hi0) as [_ Hop].
        exists o. rewrite <- Hop. auto.
      Qed.

      (** Its response index. *)
      Lemma op_res o j k op (r : Sig.ar op) :
        In o W -> op_key o = k -> res L j k op r -> res L j k (op_op o) (op_ret o).
      Proof.
        intros Ho Hk Hj. destruct (W_occ o Ho) as [_ (j0 & Hj0)]. rewrite Hk in Hj0.
        pose proof (proj1 (proj2 Hwf) _ _ _ _ _ _ _ Hj Hj0) as ->. exact Hj0.
      Qed.

      Lemma W_unique o o' : In o W -> In o' W -> op_key o = op_key o' -> o = o'.
      Proof.
        intros Ho Ho' Hk. pose proof W_nd as Hnd.
        apply in_split in Ho as (l1 & l2 & HW1).
        pose proof (RelaxedStamping.pos_split key_dec W l1 o l2 Hnd HW1) as Hp.
        apply in_split in Ho' as (m1 & m2 & HW2).
        pose proof (RelaxedStamping.pos_split key_dec W m1 o' m2 Hnd HW2) as Hp'.
        unfold RelaxedStamping.pos in Hp, Hp'. rewrite Hk in Hp. rewrite Hp in Hp'.
        rewrite HW1 in HW2. clear -HW2 Hp'.
        revert m1 HW2 Hp'. induction l1 as [|a l1 IH]; intros [|b m1] HW2 Hp'; simpl in *; try lia.
        - injection HW2; auto.
        - injection HW2 as _ HW2. apply (IH m1 HW2). lia.
      Qed.

      Lemma Hpos_inj o o' : In o W -> In o' W -> Hpos (op_key o) = Hpos (op_key o') -> o = o'.
      Proof.
        intros Ho Ho' Hp. pose proof W_nd as Hnd.
        apply in_split in Ho as (l1 & l2 & HW1).
        pose proof (RelaxedStamping.pos_split key_dec W l1 o l2 Hnd HW1) as P1.
        apply in_split in Ho' as (m1 & m2 & HW2).
        pose proof (RelaxedStamping.pos_split key_dec W m1 o' m2 Hnd HW2) as P2.
        unfold RelaxedStamping.pos, Hpos in *. rewrite P1, P2 in Hp.
        rewrite HW1 in HW2. clear -HW2 Hp.
        revert m1 HW2 Hp. induction l1 as [|a l1 IH]; intros [|b m1] HW2 Hp; simpl in *; try lia.
        - injection HW2; auto.
        - injection HW2 as _ HW2. apply (IH m1 HW2). lia.
      Qed.

      Lemma In_firstn_pos o K : In o W -> (In o (firstn K W) <-> Hpos (op_key o) < K).
      Proof.
        intros Ho. pose proof W_nd as Hnd.
        apply in_split in Ho as (l1 & l2 & HW1).
        pose proof (RelaxedStamping.pos_split key_dec W l1 o l2 Hnd HW1) as P.
        unfold RelaxedStamping.pos, Hpos in *. rewrite P. rewrite HW1.
        assert (Hn1 : ~ In o l1).
        { intros Hin. rewrite HW1, map_app in Hnd. simpl in Hnd.
          apply NoDup_remove_2 in Hnd. apply Hnd. apply in_or_app. left. apply in_map. exact Hin. }
        rewrite firstn_app. split.
        - intros Hin. destruct (Nat.lt_ge_cases (length l1) K) as [Hl | Hl]; [exact Hl|].
          exfalso. replace (K - length l1) with 0 in Hin by lia. rewrite app_nil_r in Hin.
          apply Hn1. exact (In_firstn _ _ _ Hin).
        - intros Hl. apply in_or_app. right.
          destruct (K - length l1) eqn:Hk; [lia|]. left. reflexivity.
      Qed.

      (** The keys that respond within a list of events. *)
      Definition resp_keys (p : list (ThreadEvent E)) : list (CallKey E) :=
        flat_map (fun e => match te_ev E e with
                           | ResEv h _ _ => [(te_tid E e, h)]
                           | InvEv _ _ => []
                           end) p.

      Lemma resp_keys_in p j k op (r : Sig.ar op) : res p j k op r -> In k (resp_keys p).
      Proof.
        intros (x & Hx & Hs). unfold sel in Hs. injection Hs as ->.
        apply in_flat_map. exists (Build_ThreadEvent (fst k) (ResEv (snd k) op r)).
        split; [exact (nth_error_In _ _ Hx)|]. simpl. left. destruct k. reflexivity.
      Qed.

      Lemma resp_keys_res p k : In k (resp_keys p) -> exists j op (r : Sig.ar op), res p j k op r.
      Proof.
        intros Hin. apply in_flat_map in Hin as (e & He & Hk).
        destruct e as [t [h op | h op r]]; simpl in Hk; [destruct Hk|].
        destruct Hk as [<- | []]. apply In_nth_error in He as (j & Hj).
        exists j, op, r, (Build_ThreadEvent t (ResEv h op r)). split; [exact Hj | reflexivity].
      Qed.

      Definition bound (ks : list (CallKey E)) : nat :=
        fold_right (fun k acc => Nat.max (S (Hpos k)) acc) 0 ks.

      Lemma bound_ge ks k : In k ks -> Hpos k < bound ks.
      Proof.
        unfold bound. induction ks as [|a ks IH]; cbn [fold_right In]; intros Hin; [destruct Hin|].
        destruct Hin as [-> | Hin]; [lia|]. specialize (IH Hin). lia.
      Qed.

      Lemma bound_lt ks x : x < bound ks -> exists k, In k ks /\ x <= Hpos k.
      Proof.
        unfold bound. induction ks as [|a ks IH]; cbn [fold_right In]; intros Hx; [lia|].
        destruct (Nat.le_gt_cases x (Hpos a)) as [Ha | Ha].
        - exists a. auto.
        - destruct IH as (k & Hk & Hle); [lia|]. exists k. auto.
      Qed.

      Lemma prefix_witness n : n <= length L -> lin_h Hpos (firstn n L) (firstn (bound (resp_keys (firstn n L))) W).
      Proof.
        intros Hn. set (p := firstn n L). set (K := bound (resp_keys p)). set (t := firstn K W).
        destruct HW as (Hnu & Hnd & _ & _ & _).
        assert (Hsub : forall o, In o t -> In o W) by (intros o Ho; exact (In_firstn _ _ _ Ho)).
        split; [|split; [|split; [|split]]].
        - apply (nu_prefix t (skipn K W)). unfold t. rewrite firstn_skipn. exact Hnu.
        - unfold t. rewrite <- firstn_map. apply NoDup_firstn. exact Hnd.
        - intros o Ho. pose proof (Hsub o Ho) as HoW.
          pose proof (proj1 (In_firstn_pos o K HoW) Ho) as Hlt.
          destruct (bound_lt _ _ Hlt) as (k & Hk & Hle).
          destruct (resp_keys_res _ _ Hk) as (j & op & r & Hj).
          apply res_firstn in Hj as [Hjn Hj].
          destruct (proj2 (proj2 Hwf) _ _ _ _ Hj) as (i & Hij & Hi).
          destruct (find_op _ _ _ Hi) as (ok & Hok & Hkk & Hop & _).
          pose proof (op_res ok _ _ _ _ Hok Hkk Hj) as Hjk. split.
          + destruct (W_occ o HoW) as [(i' & Hi') _].
            destruct (Nat.lt_ge_cases i' n) as [Hi'n | Hi'n].
            * exists i'. apply inv_firstn. auto.
            * exfalso.
              assert (Hne : o <> ok).
              { intros ->. rewrite Hkk in Hi'. pose proof (proj1 Hwf _ _ _ _ _ Hi Hi'). lia. }
              assert (Hlt' : Hpos (op_key o) < Hpos k).
              { destruct (Nat.eq_dec (Hpos (op_key o)) (Hpos k)) as [Heq | Hneq]; [|lia].
                exfalso. apply Hne. apply Hpos_inj; [exact HoW | exact Hok | rewrite Hkk; exact Heq]. }
              assert (Hr : rhb sel L indep ok o).
              { left. exists j, i'. split; [rewrite Hkk; exact Hjk|]. split; [exact Hi' | lia]. }
              pose proof (Hpos_rhb ok o Hok HoW Hr) as Hc'. rewrite Hkk in Hc'. lia.
          + intros j' r' Hj'. apply res_firstn in Hj' as [_ Hj'].
            pose proof (op_res o _ _ _ _ HoW eq_refl Hj') as Hjo.
            exact (res_ret _ _ _ _ _ _ Hj' Hjo).
        - intros j k op r Hj. pose proof Hj as Hjp. apply res_firstn in Hj as [Hjn Hj].
          destruct (proj2 (proj2 Hwf) _ _ _ _ Hj) as (i & Hij & Hi).
          destruct (find_op _ _ _ Hi) as (o & Ho & Hk & Hop & _).
          pose proof (op_res o _ _ _ _ Ho Hk Hj) as Hjo.
          destruct o as [ko oo ro]. simpl in Hk, Hop, Hjo. subst ko oo.
          pose proof (res_ret _ _ _ _ _ _ Hj Hjo) as ->.
          apply (In_firstn_pos _ K Ho). simpl. apply bound_ge. exact (resp_keys_in _ _ _ _ _ Hjp).
        - intros o o' Ho Ho' Hlt.
          apply (RelaxedStamping.sorted_before (fun o => Hpos (op_key o))); [|exact Ho | exact Ho' | exact Hlt].
          apply StronglySorted_firstn. exact (RelaxedStamping.sorted_pos key_dec W Hnd).
      Qed.

      Lemma bound_le ks B : (forall k, In k ks -> S (Hpos k) <= B) -> bound ks <= B.
      Proof.
        unfold bound. induction ks as [|a ks IH]; cbn [fold_right]; intros H; [lia|].
        apply Nat.max_lub; [apply H; left; reflexivity | apply IH; intros k Hk; apply H; right; exact Hk].
      Qed.

      Lemma firstn_prefix {A : Type} (l : list A) a b : a <= b -> exists t, firstn b l = firstn a l ++ t.
      Proof.
        revert a b. induction l as [|x l IH]; intros a b Hab.
        - exists []. rewrite !firstn_nil. reflexivity.
        - destruct a as [|a]; [exists (firstn b (x :: l)); reflexivity|].
          destruct b as [|b]; [lia|]. simpl. destruct (IH a b ltac:(lia)) as (t & Ht).
          exists t. rewrite Ht. reflexivity.
      Qed.

      (** The prefix witnesses only grow at the end: no operation is ever
          inserted below an operation already in a witness. *)
      Lemma prefix_witness_chain n m : n <= m ->
        exists t', firstn (bound (resp_keys (firstn m L))) W = firstn (bound (resp_keys (firstn n L))) W ++ t'.
      Proof.
        intros Hnm. apply firstn_prefix. apply bound_le. intros k Hk.
        apply bound_ge. destruct (resp_keys_res _ _ Hk) as (j & op & r & Hj).
        apply res_firstn in Hj as [Hjn Hj]. apply (resp_keys_in _ j k op r).
        apply res_firstn. split; [lia | exact Hj].
      Qed.

      Lemma W_view_rt : view_rt Hpos L.
      Proof.
        split; [split; [exact Hwf|split]|].
        - intros i j k k' op op' Hi Hj Hij Hth Hn.
          destruct (find_op _ _ _ Hi) as (o & Ho & Hk & Hop & Hio).
          destruct (find_op _ _ _ Hj) as (o' & Ho' & Hk' & Hop' & Hjo).
          rewrite <- Hk, <- Hk'. apply Hpos_rhb; [exact Ho | exact Ho'|].
          right. split; [rewrite Hk, Hk'; exact Hth|].
          exists i, j. rewrite Hk, Hk', Hop, Hop'. auto.
        - intros n Hn. eexists. exact (prefix_witness n Hn).
        - intros i j k k' op op' r Hi Hj Hij.
          destruct (proj2 (proj2 Hwf) _ _ _ _ Hi) as (i0 & Hi0 & Hinv).
          destruct (find_op _ _ _ Hinv) as (o & Ho & Hk & Hop & _).
          destruct (find_op _ _ _ Hj) as (o' & Ho' & Hk' & Hop' & Hjo).
          pose proof (op_res o _ _ _ _ Ho Hk Hi) as Hio.
          rewrite <- Hk, <- Hk'. apply Hpos_rhb; [exact Ho | exact Ho'|].
          left. exists i, j. rewrite Hk, Hk'. auto.
      Qed.
    End FromRelLin.

    Theorem rel_lin_view_rt (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'})
        (nu_prefix : forall l1 l2, nu (l1 ++ l2) -> nu l1) L :
      wf L -> complete L -> rel_lin sel L indep nu -> exists H, view_rt H L.
    Proof.
      intros Hwf Hc (W & HW). eexists. exact (W_view_rt key_dec nu_prefix L Hwf W HW).
    Qed.

    (** Prop. I.10 without compatibility, with the witness family made
        explicit: the witnesses form a chain of prefixes. *)
    Theorem rel_lin_view_rt_chain (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'})
        (nu_prefix : forall l1 l2, nu (l1 ++ l2) -> nu l1) L :
      wf L -> complete L -> rel_lin sel L indep nu ->
      exists H (ts : nat -> list (Op E)),
        view_rt H L /\
        (forall n, n <= length L -> lin_h H (firstn n L) (ts n)) /\
        (forall n m, n <= m -> exists t', ts m = ts n ++ t').
    Proof.
      intros Hwf Hc (W & HW).
      exists (Hpos key_dec W), (fun n => firstn (bound key_dec W (resp_keys (firstn n L))) W).
      split; [exact (W_view_rt key_dec nu_prefix L Hwf W HW)|]. split.
      - intros n Hn. exact (prefix_witness key_dec nu_prefix L Hwf W HW n Hn).
      - intros n m Hnm. exact (prefix_witness_chain key_dec L W n m Hnm).
    Qed.

    Corollary rel_lin_iff_view_rt (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'})
        (nu_prefix : forall l1 l2, nu (l1 ++ l2) -> nu l1) L :
      wf L -> complete L -> (rel_lin sel L indep nu <-> exists H, view_rt H L).
    Proof.
      intros Hwf Hc. split.
      - exact (rel_lin_view_rt key_dec nu_prefix L Hwf Hc).
      - intros (H & Hv). exact (view_rt_rel_lin H L Hc Hv).
    Qed.

    (** Prop. I.10 in the paper's own form (Def. I.4, no real time): no
        view-based compatibility is needed.  The input is relaxed
        linearizable, so its witness already respects real time. *)
    Corollary rel_lin_view (key_dec : forall k k' : CallKey E, {k = k'} + {k <> k'})
        (nu_prefix : forall l1 l2, nu (l1 ++ l2) -> nu l1) L :
      wf L -> complete L -> rel_lin sel L indep nu -> exists H, view H L.
    Proof.
      intros Hwf Hc Hr. destruct (rel_lin_view_rt key_dec nu_prefix L Hwf Hc Hr) as (H & Hv & _).
      exists H. exact Hv.
    Qed.
  End Def.


  (** ** Thm. I.11 with real time *)

  Section Composition.
    Context {E F : RelaxedSig.t} {X : Type}.
    Context (IE : relation (Sig.op (RelaxedSig.effect E))) (nuE : list (Op E) -> Prop).
    Context (IF : relation (Sig.op (RelaxedSig.effect F))) (nuF : list (Op F) -> Prop).
    Context (keyE : forall k k' : CallKey E, {k = k'} + {k <> k'}).
    Context (nuE_prefix : forall l1 l2, nuE (l1 ++ l2) -> nuE l1).
    (** Interaction traces and their underlay and overlay projections. *)
    Context (pE : list X -> list (ThreadEvent E)) (pF : list X -> list (ThreadEvent F)).

    (** If every interaction whose underlay has a real-time-respecting
        prefix view has an overlay with one, then the implementation maps
        relaxed linearizable underlays to relaxed linearizable overlays
        (complete executions).  View-based compatibility is not used:
        it belongs to the proof that a VLHL simulation establishes the
        premise (Thm. I.9). *)
    Theorem thm_I11_rt (Beh : list X -> Prop) :
      (forall s, Beh s -> (exists H, view_rt IE nuE H (pE s)) -> exists H', view_rt IF nuF H' (pF s)) ->
      forall s, Beh s -> wf (pE s) -> complete (pE s) -> complete (pF s) ->
        rel_lin sel (pE s) IE nuE -> rel_lin sel (pF s) IF nuF.
    Proof.
      intros Hprem s Hs Hwf Hc Hc' Hrl.
      destruct (Hprem s Hs (rel_lin_view_rt IE nuE keyE nuE_prefix _ Hwf Hc Hrl)) as (H' & Hv).
      exact (view_rt_rel_lin IF nuF H' _ Hc' Hv).
    Qed.
  End Composition.

  (** ** Part 2: without real time, Thm. I.11 fails *)

  Section Counterexample.

    Inductive RegOp : Type := Wr (v : nat) | Rd.

    Definition RegAr (m : RegOp) : Type := match m with Wr _ => unit | Rd => nat end.

    Canonical Structure RegSig : Sig.t := {| Sig.op := RegOp; Sig.ar := RegAr |}.

    (** A register whose reads may be ordered before earlier writes of the
        same thread.  Only state-preserving operations overtake, which is
        the paper's criterion for view-based compatibility. *)
    Definition rd_bypass (a b : RegOp) : Prop :=
      match a, b with Wr _, Rd => True | _, _ => False end.

    Definition Reg : RelaxedSig.t := {|
      RelaxedSig.effect := RegSig;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := rd_bypass;
      RelaxedSig.mode := fun _ => RelaxedSig.Local;
    |}.

    Fixpoint reg_ok (cur : nat) (l : list (Op Reg)) : Prop :=
      match l with
      | [] => True
      | o :: l' =>
          match op_op o as m return @Sig.ar RegSig m -> Prop with
          | Wr v => fun _ => reg_ok v l'
          | Rd => fun r => r = cur /\ reg_ok cur l'
          end (op_ret o)
      end.

    Abbreviation nuR := (reg_ok 0).

    Lemma reg_ok_prefix c l1 l2 : reg_ok c (l1 ++ l2) -> reg_ok c l1.
    Proof.
      revert c. induction l1 as [|[k [v|] r] l1 IH]; intros c H; simpl in *; [exact I | |].
      - exact (IH v H).
      - destruct H as [Hr H]. split; [exact Hr | exact (IH c H)].
    Qed.

    Lemma nuR_prefix l1 l2 : nuR (l1 ++ l2) -> nuR l1.
    Proof. apply reg_ok_prefix. Qed.

    Definition key_dec (k k' : CallKey Reg) : {k = k'} + {k <> k'}.
    Proof. destruct k as [a b], k' as [a' b']. decide equality; [apply Nat.eq_dec | apply Pos.eq_dec]. Qed.

    Abbreviation selR := (@sel Reg).

    (** Every read of the overlay returns 0. *)
    Definition zero_reads (L : list (ThreadEvent Reg)) : Prop :=
      forall j k (r : @Sig.ar RegSig Rd), res_at selR L j k Rd r -> r = 0.

    (** *** Every trace whose reads return 0 has a prefix view *)

    Fixpoint inv_lookup (i : nat) (l : list (ThreadEvent Reg)) (k : CallKey Reg) : option (nat * RegOp) :=
      match l with
      | [] => None
      | e :: l' =>
          match te_ev Reg e with
          | InvEv h m => if key_dec (te_tid Reg e, h) k then Some (i, m) else inv_lookup (S i) l' k
          | ResEv _ _ _ => inv_lookup (S i) l' k
          end
      end.

    Lemma inv_lookup_spec l : forall i0 i k m,
      (forall i' m', inv_at selR l i' k m' -> i' = i) ->
      inv_at selR l i k m -> inv_lookup i0 l k = Some (i0 + i, m).
    Proof.
      induction l as [|e l IH]; intros i0 i k m Hu Hi.
      - destruct Hi as (x & Hx & _). destruct i; discriminate.
      - simpl. destruct Hi as (x & Hx & Hs). unfold sel in Hs.
        destruct i as [|i].
        + simpl in Hx. injection Hx as <-. injection Hs as ->. simpl.
          match goal with |- context [key_dec ?a ?b] => destruct (key_dec a b) as [_ | Hn] end;
            [rewrite Nat.add_0_r; reflexivity|].
          exfalso. apply Hn. destruct k; reflexivity.
        + simpl in Hx.
          assert (Hrest : inv_lookup (S i0) l k = Some (S i0 + i, m)).
          { apply IH.
            - intros i' m' (y & Hy & Hsy). assert (Heq : S i' = S i).
              { apply (Hu (S i') m'). exists y. split; [exact Hy | exact Hsy]. }
              lia.
            - exists x. split; [exact Hx | exact Hs]. }
          replace (i0 + S i) with (S i0 + i) by lia.
          destruct e as [t [h m0 | h m0 r0]]; simpl; [|exact Hrest].
          match goal with |- context [key_dec ?a ?b] => destruct (key_dec a b) as [Hk | _] end; [|exact Hrest].
          exfalso. assert (Heq : 0 = S i).
          { apply (Hu 0 m0). exists (Build_ThreadEvent t (InvEv h m0)).
            split; [reflexivity|]. unfold sel. rewrite <- Hk. reflexivity. }
          discriminate.
    Qed.

    Definition stamp (L : list (ThreadEvent Reg)) (k : CallKey Reg) : nat :=
      match inv_lookup 0 L k with
      | Some (i, Rd) => i
      | Some (i, Wr _) => length L + i
      | None => 0
      end.

    Lemma stamp_inv L i k m :
      wf L -> inv_at selR L i k m ->
      stamp L k = match m with Rd => i | Wr _ => length L + i end /\ i < length L.
    Proof.
      intros Hwf Hi. unfold stamp.
      rewrite (inv_lookup_spec L 0 i k m (fun i' m' Hi' => proj1 Hwf _ _ _ _ _ Hi' Hi) Hi).
      split; [destruct m; reflexivity|].
      destruct Hi as (x & Hx & _). apply nth_error_Some. congruence.
    Qed.

    (** The completed operations of a list of events. *)
    Definition res_ops (p : list (ThreadEvent Reg)) : list (Op Reg) :=
      flat_map (fun e => match te_ev Reg e with
                         | ResEv h m r => [Build_Op (te_tid Reg e, h) m r]
                         | InvEv _ _ => []
                         end) p.

    Lemma res_ops_in p j k m r : res_at selR p j k m r -> In (Build_Op k m r) (res_ops p).
    Proof.
      intros (x & Hx & Hs). unfold sel in Hs. injection Hs as ->.
      apply in_flat_map. exists (Build_ThreadEvent (fst k) (ResEv (snd k) m r)).
      split; [exact (nth_error_In _ _ Hx)|]. simpl. left. destruct k. reflexivity.
    Qed.

    Lemma res_ops_res p o : In o (res_ops p) -> exists j, res_at selR p j (op_key o) (op_op o) (op_ret o).
    Proof.
      intros Hin. apply in_flat_map in Hin as (e & He & Ho).
      destruct e as [t [h m | h m r]]; simpl in Ho; [destruct Ho|].
      destruct Ho as [<- | []]. apply In_nth_error in He as (j & Hj).
      exists j, (Build_ThreadEvent t (ResEv h m r)). split; [exact Hj | reflexivity].
    Qed.

    Lemma res_ops_nodup p :
      (forall i j k m m' (r : Sig.ar m) (r' : Sig.ar m'), res_at selR p i k m r -> res_at selR p j k m' r' -> i = j) ->
      NoDup (map op_key (res_ops p)).
    Proof.
      induction p as [|e p IH]; intros Hu; [constructor|].
      assert (Hu' : forall i j k m m' (r : Sig.ar m) (r' : Sig.ar m'),
                 res_at selR p i k m r -> res_at selR p j k m' r' -> i = j).
      { intros i j k m m' r r' (x & Hx & Hs) (y & Hy & Hs').
        assert (S i = S j) by (apply (Hu _ _ k m m' r r'); [exists x | exists y]; auto). lia. }
      destruct e as [t [h m | h m r]]; simpl; [exact (IH Hu')|].
      constructor; [|exact (IH Hu')].
      intros Hin. apply in_map_iff in Hin as (o & Hk & Ho).
      destruct (res_ops_res p o Ho) as (j & x & Hx & Hs).
      assert (Heq : 0 = S j).
      { apply (Hu 0 (S j) (t, h) m (op_op o) r (op_ret o)).
        - exists (Build_ThreadEvent t (ResEv h m r)). split; reflexivity.
        - exists x. split; [exact Hx|]. rewrite Hs, Hk. reflexivity. }
      discriminate.
    Qed.

    (** Insertion sort by a natural-number key. *)
    Fixpoint insert {A : Type} (f : A -> nat) (x : A) (l : list A) : list A :=
      match l with
      | [] => [x]
      | y :: l' => if Nat.leb (f x) (f y) then x :: l else y :: insert f x l'
      end.

    Fixpoint isort {A : Type} (f : A -> nat) (l : list A) : list A :=
      match l with
      | [] => []
      | x :: l' => insert f x (isort f l')
      end.

    Lemma insert_perm {A : Type} (f : A -> nat) x l : Permutation (insert f x l) (x :: l).
    Proof.
      induction l as [|y l IH]; simpl; [reflexivity|].
      destruct (Nat.leb (f x) (f y)); [reflexivity|].
      eapply perm_trans; [apply perm_skip; exact IH | apply perm_swap].
    Qed.

    Lemma isort_perm {A : Type} (f : A -> nat) l : Permutation (isort f l) l.
    Proof.
      induction l as [|x l IH]; simpl; [reflexivity|].
      eapply perm_trans; [apply insert_perm | apply perm_skip; exact IH].
    Qed.

    Lemma insert_sorted {A : Type} (f : A -> nat) x l :
      StronglySorted (fun a b => f a <= f b) l -> StronglySorted (fun a b => f a <= f b) (insert f x l).
    Proof.
      induction l as [|y l IH]; intros HS; simpl; [repeat constructor|].
      apply StronglySorted_inv in HS as [HS HF].
      destruct (Nat.leb (f x) (f y)) eqn:Hle.
      - apply Nat.leb_le in Hle. constructor; [constructor; assumption|].
        constructor; [exact Hle|]. eapply Forall_impl; [|exact HF]. simpl. intros a Ha. lia.
      - apply Nat.leb_gt in Hle. constructor; [exact (IH HS)|].
        apply Forall_forall. intros a Ha.
        apply (Permutation_in _ (insert_perm f x l)) in Ha as [<- | Ha]; [lia|].
        rewrite Forall_forall in HF. exact (HF a Ha).
    Qed.

    Lemma isort_sorted {A : Type} (f : A -> nat) l : StronglySorted (fun a b => f a <= f b) (isort f l).
    Proof. induction l as [|x l IH]; simpl; [constructor | apply insert_sorted; exact IH]. Qed.

    Lemma sorted_le_before {A : Type} (f : A -> nat) l a b :
      StronglySorted (fun x y => f x <= f y) l -> In a l -> In b l -> f a < f b -> before l a b.
    Proof.
      induction l as [|c l IH]; intros HS Ha Hb Hlt; [destruct Ha|].
      apply StronglySorted_inv in HS as [HS HF]. rewrite Forall_forall in HF.
      destruct Ha as [<- | Ha].
      - destruct Hb as [<- | Hb]; [lia|]. exists [], l. split; [reflexivity | exact Hb].
      - destruct Hb as [<- | Hb].
        + specialize (HF a Ha). lia.
        + destruct (IH HS Ha Hb Hlt) as (l1 & l2 & -> & Hin). exists (c :: l1), l2. split; [reflexivity | exact Hin].
    Qed.

    Definition is_wr (o : Op Reg) : Prop := match op_op o with Wr _ => True | Rd => False end.

    (** A list of operations is legal if reads return 0 and no read follows
        a write. *)
    Lemma reg_ok_reads_then_writes (l : list (Op Reg)) :
      (forall o : Op Reg, In o l -> match op_op o as m return @Sig.ar RegSig m -> Prop with
                          | Rd => fun r => r = 0 | Wr _ => fun _ => True end (op_ret o)) ->
      (forall l1 (w : Op Reg) l2 o, l = l1 ++ w :: l2 -> is_wr w -> In o l2 -> is_wr o) ->
      nuR l.
    Proof.
      assert (Hw : forall c (l : list (Op Reg)), (forall o, In o l -> is_wr o) -> reg_ok c l).
      { intros c l0. revert c. induction l0 as [|[k [v|] r] l0 IH]; intros c H; simpl; [exact I | |].
        - apply IH. intros o Ho. apply H. right. exact Ho.
        - exfalso. exact (H _ (or_introl eq_refl)). }
      induction l as [|[k [v|] r] l IH]; intros Hz Hord; simpl; [exact I | |].
      - apply Hw. intros o Ho. apply (Hord [] {| op_key := k; op_op := Wr v; op_ret := r |} l o eq_refl I Ho).
      - split.
        + exact (Hz _ (or_introl eq_refl)).
        + apply IH.
          * intros o Ho. apply Hz. right. exact Ho.
          * intros l1 w l2 o -> Hw' Ho.
            apply (Hord ({| op_key := k; op_op := Rd; op_ret := r |} :: l1) w l2 o eq_refl Hw' Ho).
    Qed.

    Lemma sorted_mid {A : Type} (R : A -> A -> Prop) l1 w l2 o :
      StronglySorted R (l1 ++ w :: l2) -> In o l2 -> R w o.
    Proof.
      induction l1 as [|a l1 IH]; intros HS Ho; simpl in HS.
      - apply StronglySorted_inv in HS as [_ HF]. rewrite Forall_forall in HF. exact (HF o Ho).
      - apply StronglySorted_inv in HS as [HS _]. exact (IH HS Ho).
    Qed.

    Abbreviation viewR := (@view Reg rd_bypass nuR).

    Theorem zero_reads_view L : wf L -> zero_reads L -> viewR (stamp L) L.
    Proof.
      intros Hwf Hz. split; [exact Hwf|]. split.
      - intros i j k k' m m' Hi Hj Hij _ Hn.
        destruct (stamp_inv L i k m Hwf Hi) as [Hs His].
        destruct (stamp_inv L j k' m' Hwf Hj) as [Hs' Hjs].
        rewrite Hs, Hs'. destruct m as [v|], m' as [v'|]; simpl in Hn; try lia;
          exfalso; exact (Hn I).
      - intros n Hn. set (p := firstn n L).
        set (f := fun o : Op Reg => stamp L (op_key o)).
        exists (isort f (res_ops p)).
        pose proof (isort_perm f (res_ops p)) as Hperm.
        assert (Hin : forall o, In o (isort f (res_ops p)) <-> In o (res_ops p)).
        { intros o. split; apply Permutation_in; [exact Hperm | exact (Permutation_sym Hperm)]. }
        assert (Hfact : forall o, In o (res_ops p) ->
                  exists i j, i < j /\ j < n /\ inv_at selR L i (op_key o) (op_op o) /\
                              res_at selR L j (op_key o) (op_op o) (op_ret o)).
        { intros o Ho. destruct (res_ops_res p o Ho) as (j & Hj). apply res_firstn in Hj as [Hjn Hj].
          destruct (proj2 (proj2 Hwf) _ _ _ _ Hj) as (i & Hij & Hi). exists i, j. auto. }
        assert (Hf : forall o, In o (res_ops p) -> (is_wr o -> length L <= f o) /\ (~ is_wr o -> f o < length L)).
        { intros o Ho. destruct (Hfact o Ho) as (i & j & Hij & Hjn & Hi & Hj).
          destruct (stamp_inv L i _ _ Hwf Hi) as [Hs Hil]. unfold f. rewrite Hs. unfold is_wr.
          clear -Hil. destruct o as [k m r]; simpl. destruct m; split; intros H; try lia; try contradiction;
            exfalso; apply H; exact I. }
        split; [|split; [|split; [|split]]].
        + apply reg_ok_reads_then_writes.
          * intros o Ho. apply Hin in Ho. destruct (Hfact o Ho) as (i & j & _ & _ & _ & Hj).
            destruct o as [k [v|] r]; simpl in *; [exact I|]. exact (Hz j k r Hj).
          * intros l1 w l2 o Heq Hw Ho.
            pose proof (isort_sorted f (res_ops p)) as HS. rewrite Heq in HS.
            pose proof (sorted_mid _ _ _ _ _ HS Ho) as Hle. simpl in Hle.
            assert (Hwin : In w (res_ops p)) by (apply Hin; rewrite Heq; apply in_or_app; right; left; reflexivity).
            assert (Hoin : In o (res_ops p)) by (apply Hin; rewrite Heq; apply in_or_app; right; right; exact Ho).
            pose proof (proj1 (Hf w Hwin) Hw) as Hfw.
            unfold is_wr. destruct (op_op o) eqn:Hop; [exact I|].
            exfalso. assert (Hno : ~ is_wr o) by (unfold is_wr; rewrite Hop; intros []).
            pose proof (proj2 (Hf o Hoin) Hno). lia.
        + apply (Permutation_NoDup (Permutation_map op_key (Permutation_sym Hperm))).
          apply res_ops_nodup. intros i j k m m' r r' Hi Hj.
          apply res_firstn in Hi as [_ Hi]. apply res_firstn in Hj as [_ Hj].
          exact (proj1 (proj2 Hwf) _ _ _ _ _ _ _ Hi Hj).
        + intros o Ho. apply Hin in Ho. destruct (Hfact o Ho) as (i & j & Hij & Hjn & Hi & Hj). split.
          * exists i. apply inv_firstn. split; [lia | exact Hi].
          * intros j' r' Hj'. apply res_firstn in Hj' as [_ Hj'].
            pose proof (proj1 (proj2 Hwf) _ _ _ _ _ _ _ Hj' Hj) as ->. exact (res_ret _ _ _ _ _ _ Hj' Hj).
        + intros j k m r Hj. apply Hin. exact (res_ops_in _ _ _ _ _ Hj).
        + intros o o' Ho Ho' Hlt. exact (sorted_le_before f _ o o' (isort_sorted f _) Ho Ho' Hlt).
    Qed.

    (** *** The execution *)

    Definition t1 : LinCCALBase.tid := 1%positive.
    Definition t2 : LinCCALBase.tid := 2%positive.

    (** Thread 1 calls [write(1)], which calls [E.wrt(1)] and returns;
        afterwards thread 2 calls [read()], which returns 0.  [s0] is the
        overlay trace, [u0] the underlay trace (same call keys). *)
    Definition s0 : list (ThreadEvent Reg) := [
      Build_ThreadEvent t1 (InvEv (E := Reg) 0%nat (Wr 1));
      Build_ThreadEvent t1 (ResEv (E := Reg) 0%nat (Wr 1) tt);
      Build_ThreadEvent t2 (InvEv (E := Reg) 0%nat Rd);
      Build_ThreadEvent t2 (ResEv (E := Reg) 0%nat Rd (0%nat : @Sig.ar RegSig Rd))].

    Definition u0 : list (ThreadEvent Reg) := firstn 2 s0.

    Definition o1 : Op Reg := Build_Op (E := Reg) (t1, 0%nat) (Wr 1) tt.
    Definition o2 : Op Reg := Build_Op (E := Reg) (t2, 0%nat) Rd (0%nat : @Sig.ar RegSig Rd).

    Lemma inv_s0 i k m :
      inv_at selR s0 i k m -> (i = 0 /\ k = (t1, 0%nat) /\ m = Wr 1) \/ (i = 2 /\ k = (t2, 0%nat) /\ m = Rd).
    Proof.
      intros (x & Hx & Hs). unfold sel in Hs.
      destruct i as [|[|[|[|i]]]]; unfold s0 in Hx; simpl in Hx; [| | | | destruct i; discriminate]; injection Hx as <-.
      - left. split; [reflexivity|].
        assert (Hev : Build_ThreadEvent t1 (InvEv (E := Reg) 0%nat (Wr 1)) =
                      Build_ThreadEvent (fst k) (InvEv (snd k) m)) by congruence.
        pose proof (f_equal (te_tid Reg) Hev) as Ht. pose proof (f_equal (te_ev Reg) Hev) as Hv.
        pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Hm.
        simpl in Ht, Hh, Hm. split; [destruct k; simpl in *; subst; reflexivity | auto].
      - discriminate.
      - right. split; [reflexivity|].
        assert (Hev : Build_ThreadEvent t2 (InvEv (E := Reg) 0%nat Rd) =
                      Build_ThreadEvent (fst k) (InvEv (snd k) m)) by congruence.
        pose proof (f_equal (te_tid Reg) Hev) as Ht. pose proof (f_equal (te_ev Reg) Hev) as Hv.
        pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Hm.
        simpl in Ht, Hh, Hm. split; [destruct k; simpl in *; subst; reflexivity | auto].
      - discriminate.
    Qed.

    Lemma res_s0 j k m (r : Sig.ar m) :
      res_at selR s0 j k m r ->
      (j = 1 /\ k = (t1, 0%nat) /\ m = Wr 1) \/ (j = 3 /\ k = (t2, 0%nat) /\ m = Rd).
    Proof.
      intros (x & Hx & Hs). unfold sel in Hs.
      destruct j as [|[|[|[|j]]]]; unfold s0 in Hx; simpl in Hx; [| | | | destruct j; discriminate]; injection Hx as <-.
      - discriminate.
      - left. split; [reflexivity|].
        assert (Hev : Build_ThreadEvent t1 (ResEv (E := Reg) 0%nat (Wr 1) tt) =
                      Build_ThreadEvent (fst k) (ResEv (snd k) m r)) by congruence.
        pose proof (f_equal (te_tid Reg) Hev) as Ht. pose proof (f_equal (te_ev Reg) Hev) as Hv.
        pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Hm.
        simpl in Ht, Hh, Hm. split; [destruct k; simpl in *; subst; reflexivity | auto].
      - discriminate.
      - right. split; [reflexivity|].
        assert (Hev : Build_ThreadEvent t2 (ResEv (E := Reg) 0%nat Rd (0%nat : @Sig.ar RegSig Rd)) =
                      Build_ThreadEvent (fst k) (ResEv (snd k) m r)) by congruence.
        pose proof (f_equal (te_tid Reg) Hev) as Ht. pose proof (f_equal (te_ev Reg) Hev) as Hv.
        pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Hm.
        simpl in Ht, Hh, Hm. split; [destruct k; simpl in *; subst; reflexivity | auto].
    Qed.

    Lemma inv_s0_0 : inv_at selR s0 0 (t1, 0%nat) (Wr 1).
    Proof. exists (nth 0 s0 (Build_ThreadEvent t1 (InvEv (E := Reg) 0%nat Rd))). split; reflexivity. Qed.
    Lemma res_s0_1 : res_at selR s0 1 (t1, 0%nat) (Wr 1) (tt : @Sig.ar RegSig (Wr 1)).
    Proof. eexists. split; reflexivity. Qed.
    Lemma inv_s0_2 : inv_at selR s0 2 (t2, 0%nat) Rd.
    Proof. eexists. split; reflexivity. Qed.
    Lemma res_s0_3 : res_at selR s0 3 (t2, 0%nat) Rd (0%nat : @Sig.ar RegSig Rd).
    Proof. eexists. split; reflexivity. Qed.

    Lemma wf_s0 : wf s0.
    Proof.
      split; [|split].
      - intros i j k m m' Hi Hj.
        destruct (inv_s0 _ _ _ Hi) as [(-> & -> & _) | (-> & -> & _)];
          destruct (inv_s0 _ _ _ Hj) as [(-> & Hk & _) | (-> & Hk & _)]; try reflexivity; discriminate Hk.
      - intros i j k m m' r r' Hi Hj.
        destruct (res_s0 _ _ _ _ Hi) as [(-> & -> & _) | (-> & -> & _)];
          destruct (res_s0 _ _ _ _ Hj) as [(-> & Hk & _) | (-> & Hk & _)]; try reflexivity; discriminate Hk.
      - intros j k m r Hj. destruct (res_s0 _ _ _ _ Hj) as [(-> & -> & ->) | (-> & -> & ->)].
        + exists 0. split; [lia | exact inv_s0_0].
        + exists 2. split; [lia | exact inv_s0_2].
    Qed.

    Lemma complete_s0 : complete s0.
    Proof.
      intros i k m Hi. destruct (inv_s0 _ _ _ Hi) as [(-> & -> & ->) | (-> & -> & ->)].
      - exists 1, tt. exact res_s0_1.
      - exists 3, 0%nat. exact res_s0_3.
    Qed.

    Lemma zero_reads_s0 : zero_reads s0.
    Proof.
      intros j k r Hj. destruct (res_s0 _ _ _ _ Hj) as [(-> & -> & Hm) | (-> & -> & _)]; [discriminate|].
      exact (res_ret _ _ _ _ _ _ Hj res_s0_3).
    Qed.

    Lemma occ_s0 o : occurs selR s0 o -> o = o1 \/ o = o2.
    Proof.
      destruct o as [k m r]. intros [(i & Hi) (j & Hj)]. simpl in *.
      destruct (inv_s0 _ _ _ Hi) as [(_ & -> & ->) | (_ & -> & ->)].
      - left. destruct r. reflexivity.
      - right. destruct (res_s0 _ _ _ _ Hj) as [(_ & Hk & _) | (-> & _ & _)]; [discriminate|].
        pose proof (res_ret _ _ _ _ _ _ Hj res_s0_3) as ->. reflexivity.
    Qed.

    Lemma reg_ok_app_inv c (l1 l2 : list (Op Reg)) : reg_ok c (l1 ++ l2) -> exists c', reg_ok c' l2.
    Proof.
      revert c. induction l1 as [|[k [v|] r] l1 IH]; intros c H; simpl in H; [eauto | |].
      - exact (IH v H).
      - exact (IH c (proj2 H)).
    Qed.

    Lemma no_stale_read (l : list (Op Reg)) : reg_ok 1 l -> (forall o, In o l -> o = o1 \/ o = o2) -> ~ In o2 l.
    Proof.
      induction l as [|o l IH]; intros Hr Hall Hin; [destruct Hin|].
      destruct (Hall o (or_introl eq_refl)) as [-> | ->]; simpl in Hr.
      - destruct Hin as [Heq | Hin]; [discriminate|].
        apply (IH Hr); [intros o' Ho'; apply Hall; right; exact Ho' | exact Hin].
      - destruct Hr as [Hr _]. discriminate.
    Qed.

    Theorem s0_not_rel_lin : ~ rel_lin selR s0 rd_bypass nuR.
    Proof.
      intros (W & Hnu & Hnd & Hocc & Hcov & Hord).
      assert (Hall : forall o, In o W -> o = o1 \/ o = o2) by (intros o Ho; exact (occ_s0 o (Hocc o Ho))).
      assert (H1 : In o1 W).
      { destruct (Hcov _ _ _ inv_s0_0) as (o & Ho & Hk).
        destruct (Hall o Ho) as [-> | ->]; [exact Ho | discriminate Hk]. }
      assert (H2 : In o2 W).
      { destruct (Hcov _ _ _ inv_s0_2) as (o & Ho & Hk).
        destruct (Hall o Ho) as [-> | ->]; [discriminate Hk | exact Ho]. }
      assert (Hb : before W o1 o2).
      { apply Hord; [exact H1 | exact H2|]. left. exists 1, 2.
        split; [exact res_s0_1|]. split; [exact inv_s0_2 | lia]. }
      destruct Hb as (l1 & l2 & HW & Hin).
      rewrite HW in Hnu. destruct (reg_ok_app_inv _ _ _ Hnu) as (c & Hc). simpl in Hc.
      apply (no_stale_read l2 Hc); [|exact Hin].
      intros o Ho. apply Hall. rewrite HW. apply in_or_app. right. right. exact Ho.
    Qed.

    Theorem u0_rel_lin : rel_lin selR u0 rd_bypass nuR.
    Proof.
      exists [o1]. split; [exact I|]. split; [repeat constructor; intros []|]. split; [|split].
      - intros o [<- | []]. split; [exists 0 | exists 1]; eexists; split; reflexivity.
      - intros i k m Hi. apply inv_firstn in Hi as [Hi2 Hi].
        destruct (inv_s0 _ _ _ Hi) as [(_ & -> & _) | (-> & _ & _)]; [|lia].
        exists o1. split; [left; reflexivity | reflexivity].
      - intros o o' [<- | []] [<- | []] Hr. exfalso.
        destruct Hr as [(i & j & Hi & Hj & Hij) | (_ & i & j & Hi & Hj & Hij & _)].
        + apply res_firstn in Hi as [Hi2 Hi]. apply inv_firstn in Hj as [Hj2 Hj].
          destruct (res_s0 _ _ _ _ Hi) as [(-> & _ & _) | (-> & _ & _)]; [|lia].
          destruct (inv_s0 _ _ _ Hj) as [(-> & _ & _) | (-> & _ & _)]; lia.
        + apply inv_firstn in Hi as [Hi2 Hi]. apply inv_firstn in Hj as [Hj2 Hj].
          destruct (inv_s0 _ _ _ Hi) as [(-> & _ & _) | (-> & _ & _)];
            destruct (inv_s0 _ _ _ Hj) as [(-> & _ & _) | (-> & _ & _)]; lia.
    Qed.

    (** Thm. I.11 fails for [M = {write(v) = E.wrt(v); read() = return 0}]
        over [E = F = Reg]:

        - its premise holds: every overlay trace of [M] is well formed and
          its reads return 0, so it has a prefix view ([zero_reads_view]);
          the VLHL possibility rules derive this view, stamping each read
          below every write;
        - [s0] / [u0] is a complete execution of [M] whose underlay is
          relaxed linearizable and whose overlay is not. *)
    Theorem counterexample_I11 :
      (forall L, wf L -> zero_reads L -> exists H, viewR H L) /\
      wf s0 /\ complete s0 /\ zero_reads s0 /\
      rel_lin selR u0 rd_bypass nuR /\
      ~ rel_lin selR s0 rd_bypass nuR.
    Proof.
      split; [intros L Hwf Hz; exists (stamp L); exact (zero_reads_view L Hwf Hz)|].
      split; [exact wf_s0|]. split; [exact complete_s0|]. split; [exact zero_reads_s0|].
      split; [exact u0_rel_lin | exact s0_not_rel_lin].
    Qed.

    (** With real time, [s0] has no view: Def. I.2 plus [rt_ok] rules it out. *)
    Corollary s0_no_view_rt : ~ exists H, @view_rt Reg rd_bypass nuR H s0.
    Proof.
      intros (H & Hv). apply s0_not_rel_lin. exact (@view_rt_rel_lin Reg rd_bypass nuR H s0 complete_s0 Hv).
    Qed.
  End Counterexample.

  (** ** Part 3: Def. I.1 *)

  Section Compat.
    Context {E : RelaxedSig.t}.
    Context (indep : relation (Sig.op (RelaxedSig.effect E))) (nu : list (Op E) -> Prop).

    Definition thread (o : Op E) : LinCCALBase.tid := fst (op_key o).

    (** Def. I.1 as printed, for a specification of sequential traces.
        There [s1 · α:f · s2 · α:r ∈ ν] forces [s2 = ε], so the definition
        says: inserting the operation [o = (α, f, r)] after [s1] keeps the
        suffix [s3] legal whenever every operation of [α] in [s3] is
        semi-independent of [f].  The hypothesis is vacuous when [α] has no
        operation in [s3]. *)
    Definition compat_printed : Prop :=
      forall s1 s3 (o : Op E), nu (s1 ++ s3) ->
        (forall o', In o' s3 -> thread o' = thread o -> indep (op_op o') (op_op o)) ->
        nu (s1 ++ [o]) -> nu (s1 ++ o :: s3).

    (** The intended reading: only an operation that overtakes a later
        operation of its own thread must be insertable. *)
    Definition compat_fixed : Prop :=
      forall s1 s3 (o : Op E), nu (s1 ++ s3) ->
        (exists o', In o' s3 /\ thread o' = thread o) ->
        (forall o', In o' s3 -> thread o' = thread o -> indep (op_op o') (op_op o)) ->
        nu (s1 ++ [o]) -> nu (s1 ++ o :: s3).
  End Compat.

  Section CompatReg.

    (** As printed, the register is not compatible: a write of thread 1
        inserted before a read of thread 2 changes the value read. *)
    Theorem reg_not_compat_printed : ~ @compat_printed Reg rd_bypass (reg_ok 0).
    Proof.
      intros Hc. specialize (Hc [] [o2] o1).
      assert (Hbad : reg_ok 0 (o1 :: [o2])).
      { apply Hc.
        - simpl. split; [reflexivity | exact I].
        - intros o' [<- | []] Ht. discriminate Ht.
        - simpl. exact I. }
      simpl in Hbad. destruct Hbad as [Hbad _]. discriminate Hbad.
    Qed.

    (** The same holds for the plain SC register, with no reordering at
        all: the failure comes from inserting a write before a read of
        another thread, not from any semi-independence. *)
    Theorem sc_reg_not_compat_printed : ~ @compat_printed Reg (fun _ _ => False) (reg_ok 0).
    Proof.
      intros Hc. specialize (Hc [] [o2] o1).
      assert (Hbad : reg_ok 0 (o1 :: [o2])).
      { apply Hc.
        - simpl. split; [reflexivity | exact I].
        - intros o' [<- | []] Ht. discriminate Ht.
        - simpl. exact I. }
      simpl in Hbad. destruct Hbad as [Hbad _]. discriminate Hbad.
    Qed.

    Lemma reg_ok_insert_read c (s1 s3 : list (Op Reg)) k (r : @Sig.ar RegSig Rd) :
      reg_ok c (s1 ++ s3) -> reg_ok c (s1 ++ [Build_Op (E := Reg) k Rd r]) ->
      reg_ok c (s1 ++ Build_Op (E := Reg) k Rd r :: s3).
    Proof.
      revert c. induction s1 as [|[k' [v|] r'] s1 IH]; intros c H1 H2; simpl in *.
      - destruct H2 as [Hr _]. split; [exact Hr | exact H1].
      - exact (IH v H1 H2).
      - destruct H1 as [Hr1 H1]. destruct H2 as [_ H2]. split; [exact Hr1 | exact (IH c H1 H2)].
    Qed.

    (** Read correctly, it is: only reads overtake, and reads do not
        change the state. *)
    Theorem reg_compat_fixed : @compat_fixed Reg rd_bypass (reg_ok 0).
    Proof.
      intros s1 s3 [k [v|] r] Hnu (o' & Ho' & Ht) Hind Hno.
      - exfalso. specialize (Hind o' Ho' Ht). simpl in Hind. destruct (op_op o'); exact Hind.
      - exact (reg_ok_insert_read 0 s1 s3 k r Hnu Hno).
    Qed.
  End CompatReg.

  (** ** Part 4: what compatibility does and does not cover *)

  Section Examples.

    (** The fixed Def. I.1 says nothing about inserting an operation of one
        thread before operations of other threads only, and such an
        insertion can break the suffix: thread 1's write placed before
        thread 2's read of 0. *)
    Theorem fixed_compat_silent :
      @compat_fixed Reg rd_bypass (reg_ok 0) /\
      reg_ok 0 ([] ++ [o2]) /\ reg_ok 0 ([] ++ [o1]) /\
      (forall o', In o' [o2] -> thread o' <> thread o1) /\
      ~ reg_ok 0 ([] ++ o1 :: [o2]).
    Proof.
      split; [exact reg_compat_fixed|]. split; [simpl; split; [reflexivity | exact I]|].
      split; [simpl; exact I|]. split.
      - intros o' [<- | []]. unfold thread. simpl. discriminate.
      - simpl. intros [H _]. discriminate H.
    Qed.

    (** Compatibility does not rescue Thm. I.11: the register of the
        counterexample is compatible in the fixed sense. *)
    Corollary compat_does_not_save_I11 :
      @compat_fixed Reg rd_bypass (reg_ok 0) /\
      (forall L, wf L -> zero_reads L -> exists H, @view Reg rd_bypass (reg_ok 0) H L) /\
      rel_lin (@sel Reg) u0 rd_bypass (reg_ok 0) /\ ~ rel_lin (@sel Reg) s0 rd_bypass (reg_ok 0).
    Proof.
      destruct counterexample_I11 as (Hv & _ & _ & _ & Hu & Hs).
      split; [exact reg_compat_fixed|]. auto.
    Qed.

    (** Why the paper's proof of Prop. I.10 inserts, and why it need not.
        In the prefix [p1], thread 2's read of 1 has returned while thread
        1's write of 1 is still pending.  Restricting the witness to the
        completed operation gives [rd = 1] alone, which is illegal.  The
        completion of Def. I.3 may also answer the pending write, and the
        prefix [wrt 1; rd = 1] of the global witness is legal. *)
    Definition p1 : list (ThreadEvent Reg) := [
      Build_ThreadEvent t1 (InvEv (E := Reg) 0%nat (Wr 1));
      Build_ThreadEvent t2 (InvEv (E := Reg) 0%nat Rd);
      Build_ThreadEvent t2 (ResEv (E := Reg) 0%nat Rd (1%nat : @Sig.ar RegSig Rd))].

    Definition o_rd1 : Op Reg := Build_Op (E := Reg) (t2, 0%nat) Rd (1%nat : @Sig.ar RegSig Rd).

    Definition H1 (k : CallKey Reg) : nat := if Pos.eqb (fst k) t1 then 0 else 1.

    Lemma res_p1 j k m (r : Sig.ar m) :
      res_at (@sel Reg) p1 j k m r -> j = 2 /\ k = (t2, 0%nat) /\ m = Rd.
    Proof.
      intros (x & Hx & Hs). unfold sel in Hs.
      destruct j as [|[|[|j]]]; unfold p1 in Hx; simpl in Hx; [| | | destruct j; discriminate];
        injection Hx as <-; try discriminate.
      split; [reflexivity|].
      assert (Hev : Build_ThreadEvent t2 (ResEv (E := Reg) 0%nat Rd (1%nat : @Sig.ar RegSig Rd)) =
                    Build_ThreadEvent (fst k) (ResEv (snd k) m r)) by congruence.
      pose proof (f_equal (te_tid Reg) Hev) as Ht. pose proof (f_equal (te_ev Reg) Hev) as Hv.
      pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Hm.
      simpl in Ht, Hh, Hm. split; [destruct k; simpl in *; subst; reflexivity | auto].
    Qed.

    Lemma res_p1_2 : res_at (@sel Reg) p1 2 (t2, 0%nat) Rd (1%nat : @Sig.ar RegSig Rd).
    Proof. eexists. split; reflexivity. Qed.

    Theorem naive_restriction_fails : ~ reg_ok 0 [o_rd1].
    Proof. simpl. intros [H _]. discriminate H. Qed.

    Theorem completion_witness : @lin_h Reg (reg_ok 0) H1 p1 [o1; o_rd1].
    Proof.
      split; [simpl; split; [reflexivity | exact I]|]. split.
      { repeat constructor; simpl; [intros [H | []]; discriminate H | intros []]. }
      split; [|split].
      - intros o [<- | [<- | []]]; split.
        + exists 0. eexists. split; reflexivity.
        + intros j r Hj. destruct (res_p1 _ _ _ _ Hj) as (_ & Hk & _). discriminate Hk.
        + exists 1. eexists. split; reflexivity.
        + intros j r Hj. destruct (res_p1 _ _ _ _ Hj) as (-> & _ & _).
          exact (res_ret _ _ _ _ _ _ Hj res_p1_2).
      - intros j k m r Hj. destruct (res_p1 _ _ _ _ Hj) as (-> & -> & ->).
        pose proof (res_ret _ _ _ _ _ _ Hj res_p1_2) as ->. right. left. reflexivity.
      - intros o o' [<- | [<- | []]] [<- | [<- | []]] Hlt; unfold H1 in Hlt; simpl in Hlt; try lia.
        exists [], [o_rd1]. split; [reflexivity | left; reflexivity].
    Qed.
  End Examples.
End PrefixView.
