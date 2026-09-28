(** * Bookkeeping along a trace: issue, pending and publication indices

    Both directions of the declarative characterization reason about a
    fixed trace of the buffered memory by positions: the index at which a
    write is issued, the indices at which it is pending, and the index of
    the flush block that publishes it.  This file collects those facts for
    an arbitrary trace [s] in which every non-flush block occurs at most
    once ([NoDup (hide s)]); the facts that need every block to be enabled
    are stated under [enabled_along].

    The central statement is [pending_iff]: a write is pending after the
    first [k] blocks iff it was issued before [k] and no flush block in
    between has published it. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.PArith.PArith.
Require Import Coq.Bool.Bool.
Require Import Coq.Logic.Classical.

Require Import memory.Prelude.
Require Import memory.Cell.

Import ListNotations.

Module Pending.

  Import Cell.

  Section General.
    Context (C : Cfg).

    Notation block := (block C).
    Notation trace := (trace C).

    (** ** [remove_first_at] *)

    Lemma In_remove_first_at (x : Loc C) (b : block) (l : list block) :
      In b (remove_first_at x l) -> In b l.
    Proof.
      induction l as [| c l IH]; cbn; auto.
      destruct (at_loc x c); cbn; auto. intros [-> | H]; auto.
    Qed.

    Lemma before_remove_first_at (x : Loc C) (a b : block) (l : list block) :
      before (remove_first_at x l) a b -> before l a b.
    Proof.
      induction l as [| c l IH]; intros H.
      - destruct H as (i & j & _ & Hi & _). destruct i; discriminate.
      - rewrite remove_first_at_cons in H. destruct (at_loc x c).
        + apply before_cons. auto.
        + destruct H as (i & j & Hij & Hi & Hj).
          destruct i as [| i]; destruct j as [| j]; cbn in *; try lia.
          * inversion Hi; subst. apply before_cons_head.
            eapply In_remove_first_at. eapply nth_error_In. eauto.
          * apply before_cons. apply IH. exists i, j. auto with arith.
    Qed.

    Lemma NoDup_remove_first_at (x : Loc C) (l : list block) : NoDup l -> NoDup (remove_first_at x l).
    Proof.
      induction l as [| c l IH]; intros Hnd; cbn; auto.
      apply NoDup_cons_iff in Hnd. destruct Hnd as [Hc Hnd].
      destruct (at_loc x c); auto.
      constructor; auto. intros H. apply Hc. eapply In_remove_first_at. eauto.
    Qed.

    Lemma In_proj (x : Loc C) (b : block) (l : list block) : In b (proj x l) <-> In b l /\ b_loc b = x.
    Proof.
      unfold proj. rewrite filter_In. rewrite at_loc_true. reflexivity.
    Qed.

    Lemma In_remove_first_at_iff (x : Loc C) (b : block) (l : list block) :
      NoDup l ->
      (In b (remove_first_at x l) <-> In b l /\ hd_error (proj x l) <> Some b).
    Proof.
      induction l as [| c l IH]; intros Hnd.
      - cbn. tauto.
      - apply NoDup_cons_iff in Hnd. destruct Hnd as [Hc Hnd].
        rewrite remove_first_at_cons, proj_cons.
        destruct (at_loc x c) eqn:Hxc.
        + cbn. split.
          * intros H. split; [right; auto |]. intros Heq. inversion Heq; subst. contradiction.
          * intros [[-> | H] Hne]; [congruence | auto].
        + cbn. rewrite IH by auto. split.
          * intros [Heq | [H Hne]].
            -- subst b. split; [left; auto |]. intros Heq.
               assert (Hin : In c (proj x l)).
               { destruct (proj x l); [discriminate |]. cbn in Heq. inversion Heq. left. auto. }
               apply In_proj in Hin. destruct Hin. contradiction.
            -- split; [right; auto | auto].
          * intros [[Heq | H] Hne]; [left; auto | right; auto].
    Qed.

    (** ** [pend] is an order-preserving subsequence of the trace *)

    Lemma before_pend (t : tid) (s : trace) (a b : block) : before (pend t s) a b -> before s a b.
    Proof.
      induction s as [| c s IH] using rev_ind; intros H.
      - unfold pend in H. cbn in H. destruct H as (i & j & _ & Hi & _). destruct i; discriminate.
      - rewrite pend_snoc in H. unfold pend_step in H.
        destruct c as [u h x v m | u h x m v | u h x].
        + destruct (Pos.eq_dec u t).
          * apply before_app_inv in H. destruct H as [H | [H | [Ha Hb]]].
            -- apply before_app_l. auto.
            -- destruct H as (i & j & Hij & Hi & Hj).
               destruct j as [| j]; [lia | destruct j; discriminate].
            -- apply before_app_lr; [| exact Hb]. apply pend_In in Ha. tauto.
          * apply before_app_l. auto.
        + apply before_app_l. auto.
        + destruct (Pos.eq_dec u t).
          * apply before_app_l. apply IH. apply before_remove_first_at in H. auto.
          * apply before_app_l. auto.
    Qed.

    Lemma pend_NoDup (t : tid) (s : trace) : NoDup (hide s) -> NoDup (pend t s).
    Proof.
      induction s as [| c s IH] using rev_ind; intros Hnd.
      - constructor.
      - rewrite hide_app in Hnd.
        assert (Hnd' : NoDup (hide s)) by (eapply NoDup_app_remove_r; eauto).
        rewrite pend_snoc. unfold pend_step.
        destruct c as [u h x v m | u h x m v | u h x]; auto.
        + destruct (Pos.eq_dec u t); auto.
          apply NoDup_snoc; auto. intros Hin.
          apply pend_In in Hin. destruct Hin as (Hin & _ & _).
          eapply (@NoDup_app_disjoint _ _ _ (BW u h x v m)); [exact Hnd | |].
          * apply In_hide. split; [auto | cbn; tauto].
          * cbn. left. auto.
        + destruct (Pos.eq_dec u t); auto. apply NoDup_remove_first_at. auto.
    Qed.

    (** Membership in [pend] and in a projection, by index. *)
    Lemma In_pend_pfx (t : tid) (s : trace) (k : nat) (b : block) :
      In b (pend t (firstn k s)) -> exists i, i < k /\ nth_error s i = Some b.
    Proof.
      intros H. apply pend_In in H. destruct H as (H & _ & _).
      apply In_nth_error in H. destruct H as [i Hi].
      apply nth_error_firstn_iff in Hi. exists i. tauto.
    Qed.

  End General.

  (** ** Indexed bookkeeping on a fixed trace *)

  Section Indexed.
    Context (C : Cfg).
    Notation block := (block C).
    Notation trace := (trace C).

    Variable s : trace.
    Hypothesis Hnd : NoDup (hide s).

    Definition at_idx (i : nat) (b : block) : Prop := nth_error s i = Some b.
    Definition pfx (k : nat) : trace := firstn k s.

    (** [w] is pending (issued and not yet published) after the first [k]
        blocks. *)
    Definition pending (k : nat) (w : block) : Prop :=
      In w (pend (b_tid w) (pfx k)).

    (** [w] is the oldest pending write of its thread at its location. *)
    Definition head_at (k : nat) (w : block) : Prop :=
      hd_error (proj (b_loc w) (pend (b_tid w) (pfx k))) = Some w.

    (** [w] is the youngest pending write of its thread at its location. *)
    Definition last_at (k : nat) (w : block) : Prop :=
      hd_error (rev (proj (b_loc w) (pend (b_tid w) (pfx k)))) = Some w.

    Definition flush_at (j : nat) (t : tid) (x : Loc C) : Prop :=
      exists h, at_idx j (BF t h x).

    (** The flush block at [j] publishes [w]. *)
    Definition removes (j : nat) (w : block) : Prop :=
      flush_at j (b_tid w) (b_loc w) /\ head_at j w.

    Lemma at_idx_lt i b : at_idx i b -> i < length s.
    Proof. intros H. apply nth_error_Some. unfold at_idx in H. congruence. Qed.

    Lemma at_idx_unique i j b :
      ~ is_flush b -> at_idx i b -> at_idx j b -> i = j.
    Proof.
      intros Hb Hi Hj.
      assert (Hu : unique_occ s b).
      { intros i' j' Hi' Hj'.
        destruct (lt_eq_lt_dec i' j') as [[Hlt | Heq] | Hgt]; auto; exfalso.
        - assert (before s b b) by (exists i', j'; auto).
          apply (@before_irrefl _ (hide s) b Hnd).
          apply before_filter; auto; destruct b; cbn in *; first [reflexivity | exfalso; apply Hb; exact I].
        - assert (before s b b) by (exists j', i'; auto).
          apply (@before_irrefl _ (hide s) b Hnd).
          apply before_filter; auto; destruct b; cbn in *; first [reflexivity | exfalso; apply Hb; exact I]. }
      apply Hu; auto.
    Qed.

    Lemma unique_occ_nonflush b : ~ is_flush b -> unique_occ s b.
    Proof. intros Hb i j Hi Hj. eapply at_idx_unique; eauto. Qed.

    Lemma pfx_S k b : at_idx k b -> pfx (S k) = pfx k ++ [b].
    Proof. intros H. unfold pfx. apply firstn_S_nth. exact H. Qed.

    Lemma pfx_S_none k : length s <= k -> pfx (S k) = pfx k.
    Proof. intros H. unfold pfx. rewrite !firstn_all2; auto; lia. Qed.

    Lemma pfx_all : pfx (length s) = s.
    Proof. unfold pfx. apply firstn_all. Qed.

    Lemma pfx_0 : pfx 0 = [].
    Proof. reflexivity. Qed.

    Lemma pend_pfx_S t k b :
      at_idx k b -> pend t (pfx (S k)) = pend_step t (pend t (pfx k)) b.
    Proof. intros H. rewrite (pfx_S k b H). apply pend_snoc. Qed.

    Lemma In_pfx k b : In b (pfx k) <-> exists i, i < k /\ at_idx i b.
    Proof.
      unfold pfx, at_idx. split.
      - intros H. apply In_nth_error in H. destruct H as [i Hi].
        apply nth_error_firstn_iff in Hi. exists i. tauto.
      - intros (i & Hi & H). apply nth_error_In with i. apply nth_error_firstn_iff. auto.
    Qed.

    Lemma before_pfx k a b : before (pfx k) a b -> before s a b.
    Proof.
      intros H. rewrite <- (firstn_skipn k s). apply before_app_l. exact H.
    Qed.

    Lemma pend_pfx_NoDup t k : NoDup (pend t (pfx k)).
    Proof.
      apply pend_NoDup. unfold pfx. rewrite <- (firstn_skipn k s) in Hnd.
      rewrite hide_app in Hnd. eapply NoDup_app_remove_r. eauto.
    Qed.

    Lemma pending_write k w : pending k w -> is_write w.
    Proof. intros H. apply pend_In in H. tauto. Qed.

    Lemma pending_idx k w : pending k w -> exists i, i < k /\ at_idx i w.
    Proof. intros H. eapply In_pend_pfx. exact H. Qed.

    Lemma head_at_pending k w : head_at k w -> pending k w.
    Proof.
      unfold head_at, pending. intros H.
      destruct (proj (b_loc w) (pend (b_tid w) (pfx k))) as [| c l] eqn:Hp; [discriminate |].
      cbn in H. inversion H; subst c.
      assert (In w (proj (b_loc w) (pend (b_tid w) (pfx k)))) by (rewrite Hp; left; auto).
      apply In_proj in H0. tauto.
    Qed.

    Lemma last_at_pending k w : last_at k w -> pending k w.
    Proof.
      unfold last_at, pending. intros H.
      apply hd_error_rev_iff in H. destruct H as [l' Hl'].
      assert (In w (proj (b_loc w) (pend (b_tid w) (pfx k)))).
      { rewrite Hl'. apply in_or_app. right. left. auto. }
      apply In_proj in H. tauto.
    Qed.

    Lemma removes_pending j w : removes j w -> pending j w.
    Proof. intros [_ H]. apply head_at_pending. exact H. Qed.

    Lemma removes_write j w : removes j w -> is_write w.
    Proof. intros H. eapply pending_write. apply removes_pending. exact H. Qed.

    Lemma flush_at_idx j t x b : flush_at j t x -> at_idx j b -> b = BF t (b_handle b) x.
    Proof.
      intros [h Hj] Hb. unfold at_idx in *. rewrite Hj in Hb. inversion Hb; subst. reflexivity.
    Qed.

    (** *** The characterization of pending writes *)

    Lemma pending_iff k w :
      is_write w ->
      (pending k w <->
       exists i, at_idx i w /\ i < k /\ forall j, i < j < k -> ~ removes j w).
    Proof.
      intros Hw. induction k as [| k IH].
      - split.
        + intros H. unfold pending in H. rewrite pfx_0 in H. inversion H.
        + intros (i & _ & Hi & _). lia.
      - destruct (le_lt_dec (length s) k) as [Hlen | Hlen].
        + (* no block at k *)
          assert (Hpf : pfx (S k) = pfx k) by (apply pfx_S_none; auto).
          unfold pending. rewrite Hpf. fold (pending k w). rewrite IH. split.
          * intros (i & Hi & Hik & Hno). exists i. split; auto. split; [lia |].
            intros j Hj Hr. destruct (lt_dec j k) as [Hjk | Hjk]; [eapply Hno; eauto; lia |].
            assert (j = k) by lia. subst j. destruct Hr as [[h Hf] _].
            apply at_idx_lt in Hf. lia.
          * intros (i & Hi & Hik & Hno). exists i. split; auto.
            apply at_idx_lt in Hi. split; [lia |]. intros j Hj. apply Hno. lia.
        + destruct (nth_error s k) as [b |] eqn:Hb; [| apply nth_error_None in Hb; lia].
          assert (Hbk : at_idx k b) by exact Hb.
          assert (Hstep : pending (S k) w <-> In w (pend_step (b_tid w) (pend (b_tid w) (pfx k)) b)).
          { unfold pending. rewrite (pend_pfx_S _ _ _ Hbk). reflexivity. }
          (* the right-hand side at [S k] versus at [k] *)
          assert (Hrhs : (exists i, at_idx i w /\ i < S k /\ forall j, i < j < S k -> ~ removes j w) <->
                         ((exists i, at_idx i w /\ i < k /\ forall j, i < j < k -> ~ removes j w) /\ ~ removes k w)
                         \/ at_idx k w).
          { split.
            - intros (i & Hi & Hik & Hno).
              destruct (lt_dec i k) as [Hlt | Hge].
              + left. split.
                * exists i. split; auto. split; auto. intros j Hj. apply Hno. lia.
                * apply Hno. lia.
              + right. replace k with i by lia. auto.
            - intros [[(i & Hi & Hik & Hno) Hk] | Hk].
              + exists i. split; auto. split; [lia |]. intros j Hj.
                destruct (lt_dec j k) as [Hjk | Hjk]; [apply Hno; lia |].
                replace j with k by lia. auto.
              + exists k. split; auto. split; [lia |]. intros j Hj. lia. }
          rewrite Hstep, Hrhs. rewrite <- IH. clear Hstep Hrhs IH.
          destruct b as [u h x v m | u h x m v | u h x].
          * (* a write block at [k] *)
            assert (Hnr : ~ removes k w).
            { intros [[h' Hf] _]. unfold at_idx in *. rewrite Hb in Hf. discriminate. }
            unfold pend_step. destruct (Pos.eq_dec u (b_tid w)) as [Hu | Hu].
            -- rewrite in_app_iff. cbn. split.
               ++ intros [H | [H | []]].
                  ** left. split; [exact H | exact Hnr].
                  ** right. subst w. exact Hb.
               ++ intros [[H _] | H]; [left; exact H |].
                  right. left. unfold at_idx in *. rewrite Hb in H. inversion H. reflexivity.
            -- split.
               ++ intros H. left. split; [exact H | exact Hnr].
               ++ intros [[H _] | H]; [exact H |].
                  unfold at_idx in *. rewrite Hb in H. inversion H; subst. cbn in Hu. congruence.
          * (* a read block at [k] *)
            assert (Hnr : ~ removes k w).
            { intros [[h' Hf] _]. unfold at_idx in *. rewrite Hb in Hf. discriminate. }
            cbn. split.
            -- intros H. left. split; [exact H | exact Hnr].
            -- intros [[H _] | H]; [exact H |].
               unfold at_idx in *. rewrite Hb in H. inversion H; subst. destruct Hw.
          * (* a flush block at [k] *)
            assert (Hnw : ~ at_idx k w).
            { intros H. unfold at_idx in *. rewrite Hb in H. inversion H; subst. destruct Hw. }
            unfold pend_step. destruct (Pos.eq_dec u (b_tid w)) as [Hu | Hu].
            -- subst u. rewrite In_remove_first_at_iff by apply pend_pfx_NoDup.
               split.
               ++ intros [Hin Hhd]. left. split; auto.
                  intros [[h' Hf] Hhead]. unfold head_at in Hhead.
                  unfold at_idx in Hf. rewrite Hb in Hf. inversion Hf; subst x.
                  congruence.
               ++ intros [[Hin Hnr] | H]; [| contradiction].
                  split; auto. intros Hhd.
                  destruct (Loc_eq_dec C x (b_loc w)) as [-> | Hx].
                  ** apply Hnr. split; [exists h; exact Hb | exact Hhd].
                  ** assert (In w (proj x (pend (b_tid w) (pfx k)))).
                     { destruct (proj x (pend (b_tid w) (pfx k))); [discriminate |].
                       cbn in Hhd. inversion Hhd; left; auto. }
                     apply In_proj in H. destruct H. congruence.
            -- split.
               ++ intros H. left. split; auto.
                  intros [[h' Hf] _]. unfold at_idx in Hf. rewrite Hb in Hf. inversion Hf. congruence.
               ++ intros [[H _] | H]; auto. contradiction.
    Qed.

    (** *** Consequences *)

    Lemma removes_after_idx j w i : removes j w -> at_idx i w -> i < j.
    Proof.
      intros Hr Hi.
      assert (Hw : is_write w) by (eapply removes_write; eauto).
      apply removes_pending in Hr. apply pending_iff in Hr; auto.
      destruct Hr as (i' & Hi' & Hlt & _).
      assert (i = i') by (eapply at_idx_unique; eauto; destruct w; cbn in *; tauto).
      lia.
    Qed.

    Lemma removes_not_pending_S j w : removes j w -> ~ pending (S j) w.
    Proof.
      intros Hr Hp.
      assert (Hw : is_write w) by (eapply removes_write; eauto).
      apply pending_iff in Hp; auto. destruct Hp as (i & Hi & Hik & Hno).
      assert (i < j) by (eapply removes_after_idx; eauto).
      apply (Hno j); [lia | exact Hr].
    Qed.

    Lemma removes_unique j j' w : removes j w -> removes j' w -> j = j'.
    Proof.
      intros Hj Hj'.
      assert (Hw : is_write w) by (eapply removes_write; eauto).
      destruct (lt_eq_lt_dec j j') as [[Hlt | Heq] | Hgt]; auto; exfalso.
      - apply removes_pending in Hj'. apply pending_iff in Hj'; auto.
        destruct Hj' as (i & Hi & _ & Hno). apply (Hno j); [| exact Hj].
        split; auto. eapply removes_after_idx; eauto.
      - apply removes_pending in Hj. apply pending_iff in Hj; auto.
        destruct Hj as (i & Hi & _ & Hno). apply (Hno j'); [| exact Hj'].
        split; auto. eapply removes_after_idx; eauto.
    Qed.

    (** With a known publication index, pending is an interval. *)
    Lemma pending_interval i j w k :
      at_idx i w -> removes j w -> (pending k w <-> i < k <= j).
    Proof.
      intros Hi Hj.
      assert (Hw : is_write w) by (eapply removes_write; eauto).
      assert (Hij : i < j) by (eapply removes_after_idx; eauto).
      rewrite pending_iff by auto. split.
      - intros (i' & Hi' & Hik & Hno).
        assert (i = i') by (eapply at_idx_unique; eauto; destruct w; cbn in *; tauto). subst i'.
        split; auto.
        destruct (le_lt_dec k j) as [Hkj | Hkj]; auto.
        exfalso. apply (Hno j); auto.
      - intros [Hik Hkj]. exists i. split; auto. split; auto.
        intros j' Hj' Hr. assert (j' = j) by (eapply removes_unique; eauto). lia.
    Qed.

    (** Pending writes that are never published stay pending. *)
    Lemma pending_persists_no_removal i w k k' :
      at_idx i w -> is_write w -> i < k -> k <= k' ->
      (forall j, i < j < k' -> ~ removes j w) -> pending k' w.
    Proof.
      intros Hi Hw Hik Hkk Hno. apply pending_iff; auto. exists i. split; auto. split; [lia | auto].
    Qed.

    (** A write that is not pending at the end of a trace it appears in has
        been published. *)
    Lemma issued_not_pending_removed i w k :
      at_idx i w -> is_write w -> i < k -> ~ pending k w ->
      exists j, i < j < k /\ removes j w.
    Proof.
      intros Hi Hw Hik Hnp. apply NNPP. intros Hno. apply Hnp.
      apply pending_iff; auto. exists i. split; auto. split; auto.
      intros j Hj Hr. apply Hno. eauto.
    Qed.

    (** *** Head and last of the pending writes at a location *)

    Lemma head_at_iff k w :
      head_at k w <->
      (pending k w /\
       forall w', pending k w' -> b_loc w' = b_loc w -> b_tid w' = b_tid w -> w' <> w ->
         before s w w').
    Proof.
      unfold head_at, pending. split.
      - intros H. split.
        + apply head_at_pending. exact H.
        + intros w' Hw' Hloc Htid Hne.
          destruct (proj (b_loc w) (pend (b_tid w) (pfx k))) as [| c l] eqn:Hp; [discriminate |].
          cbn in H. inversion H; subst c.
          assert (Hin : In w' (proj (b_loc w) (pend (b_tid w) (pfx k)))).
          { apply In_proj. rewrite <- Htid. auto. }
          rewrite Hp in Hin. destruct Hin as [-> | Hin]; [congruence |].
          apply before_pfx with k. apply before_pend with (b_tid w).
          apply before_filter_inv with (at_loc (b_loc w)). fold (proj (b_loc w) (pend (b_tid w) (pfx k))).
          rewrite Hp. apply before_cons_head. auto.
      - intros [Hin Hmin].
        assert (Hin' : In w (proj (b_loc w) (pend (b_tid w) (pfx k)))) by (apply In_proj; auto).
        destruct (proj (b_loc w) (pend (b_tid w) (pfx k))) as [| c l] eqn:Hp; [inversion Hin' |].
        cbn. destruct Hin' as [-> | Hin']; [reflexivity |].
        exfalso.
        assert (Hc : In c (proj (b_loc w) (pend (b_tid w) (pfx k)))) by (rewrite Hp; left; auto).
        apply In_proj in Hc. destruct Hc as [Hc Hcloc].
        assert (Hctid : b_tid c = b_tid w) by (apply pend_In in Hc; tauto).
        assert (Hcw : c <> w).
        { intros ->. pose proof (pend_pfx_NoDup (b_tid w) k) as Hnd'.
          assert (NoDup (proj (b_loc w) (pend (b_tid w) (pfx k)))) by (apply NoDup_filter; auto).
          rewrite Hp in H. apply NoDup_cons_iff in H. tauto. }
        assert (Hbefore : before s c w).
        { apply before_pfx with k. apply before_pend with (b_tid w).
          apply before_filter_inv with (at_loc (b_loc w)). fold (proj (b_loc w) (pend (b_tid w) (pfx k))).
          rewrite Hp. apply before_cons_head. auto. }
        assert (Hbefore' : before s w c).
        { apply Hmin; auto. unfold pending. rewrite Hctid. auto. }
        assert (Hwc : is_write c) by (apply pend_In in Hc; tauto).
        assert (Hww : is_write w) by (apply pend_In in Hin; tauto).
        eapply before_asym_u; [| | exact Hbefore' | exact Hbefore];
          apply unique_occ_nonflush; [destruct w | destruct c]; cbn in *; tauto.
    Qed.

    Lemma last_at_iff k w :
      last_at k w <->
      (pending k w /\
       forall w', pending k w' -> b_loc w' = b_loc w -> b_tid w' = b_tid w -> w' <> w ->
         before s w' w).
    Proof.
      unfold last_at, pending. split.
      - intros H. split.
        + apply last_at_pending. exact H.
        + intros w' Hw' Hloc Htid Hne.
          apply hd_error_rev_iff in H. destruct H as [l' Hl'].
          assert (Hin : In w' (proj (b_loc w) (pend (b_tid w) (pfx k)))).
          { apply In_proj. rewrite <- Htid. auto. }
          rewrite Hl' in Hin. apply in_app_or in Hin. destruct Hin as [Hin | [-> | []]]; [| congruence].
          apply before_pfx with k. apply before_pend with (b_tid w).
          apply before_filter_inv with (at_loc (b_loc w)). fold (proj (b_loc w) (pend (b_tid w) (pfx k))).
          rewrite Hl'. apply before_app_lr; auto. left. auto.
      - intros [Hin Hmax].
        assert (Hin' : In w (proj (b_loc w) (pend (b_tid w) (pfx k)))) by (apply In_proj; auto).
        apply hd_error_rev_iff.
        apply in_split in Hin'. destruct Hin' as (l1 & l2 & Hp).
        destruct l2 as [| c l2].
        + exists l1. exact Hp.
        + exfalso.
          assert (Hc : In c (proj (b_loc w) (pend (b_tid w) (pfx k)))).
          { rewrite Hp. apply in_or_app. right. right. left. auto. }
          apply In_proj in Hc. destruct Hc as [Hc Hcloc].
          assert (Hctid : b_tid c = b_tid w) by (apply pend_In in Hc; tauto).
          assert (Hcw : c <> w).
          { intros ->. pose proof (pend_pfx_NoDup (b_tid w) k) as Hnd'.
            assert (NoDup (proj (b_loc w) (pend (b_tid w) (pfx k)))) by (apply NoDup_filter; auto).
            rewrite Hp in H. apply NoDup_remove_2 in H. apply H. apply in_or_app. right. left. auto. }
          assert (Hbefore : before s w c).
          { apply before_pfx with k. apply before_pend with (b_tid w).
            apply before_filter_inv with (at_loc (b_loc w)). fold (proj (b_loc w) (pend (b_tid w) (pfx k))).
            rewrite Hp. replace (l1 ++ w :: c :: l2) with ((l1 ++ [w]) ++ c :: l2)
              by (rewrite <- app_assoc; reflexivity).
            apply before_app_lr; [apply in_or_app; right; left; auto | left; auto]. }
          assert (Hbefore' : before s c w).
          { apply Hmax; auto. unfold pending. rewrite Hctid. auto. }
          assert (Hwc : is_write c) by (apply pend_In in Hc; tauto).
          assert (Hww : is_write w) by (apply pend_In in Hin; tauto).
          eapply before_asym_u; [| | exact Hbefore | exact Hbefore'];
            apply unique_occ_nonflush; [destruct w | destruct c]; cbn in *; tauto.
    Qed.

    (** Two pending writes of one thread at one location are ordered in the
        trace as their issue order (FIFO). *)
    Lemma head_at_unique k w w' : head_at k w -> head_at k w' -> b_loc w = b_loc w' -> b_tid w = b_tid w' -> w = w'.
    Proof.
      intros H H' Hloc Htid. unfold head_at in *. rewrite Hloc, Htid in H. congruence.
    Qed.

    Lemma removes_head_unique j w w' : removes j w -> removes j w' -> w = w'.
    Proof.
      intros [[h Hf] Hh] [[h' Hf'] Hh']. unfold at_idx in *.
      rewrite Hf in Hf'. inversion Hf'; subst.
      eapply head_at_unique; eauto.
    Qed.

    (** *** The global value *)

    Definition no_flush_before (k : nat) (x : Loc C) : Prop :=
      forall j t, j < k -> ~ flush_at j t x.

    Definition last_flush_before (k : nat) (x : Loc C) (j : nat) : Prop :=
      (exists t, flush_at j t x) /\ j < k /\
      forall j' t', j < j' < k -> ~ flush_at j' t' x.

    Lemma cg_step_nonflush x k b :
      at_idx k b -> (forall t, b <> BF t (b_handle b) x) ->
      cg (state_after x (pfx (S k))) = cg (state_after x (pfx k)).
    Proof.
      intros Hk Hnf. rewrite (pfx_S k b Hk). rewrite state_after_snoc.
      unfold step_at. destruct (at_loc x b) eqn:Hx; auto.
      apply at_loc_true in Hx.
      destruct b as [t h y v a | t h y a v | t h y]; cbn in *; auto.
      subst y. exfalso. apply (Hnf t). reflexivity.
    Qed.

    Lemma cg_no_flush k x : no_flush_before k x -> cg (state_after x (pfx k)) = 0.
    Proof.
      induction k as [| k IH]; intros H.
      - reflexivity.
      - destruct (le_lt_dec (length s) k) as [Hlen | Hlen].
        + rewrite pfx_S_none by auto. apply IH. intros j t Hj. apply H. lia.
        + destruct (nth_error s k) as [b |] eqn:Hb; [| apply nth_error_None in Hb; lia].
          assert (Hnf : forall t, b <> BF t (b_handle b) x).
          { intros t Heq. rewrite Heq in Hb. apply (H k t); [lia |]. exists (b_handle b). exact Hb. }
          rewrite (cg_step_nonflush x k b Hb Hnf).
          apply IH. intros j t Hj. apply H. lia.
    Qed.

    Lemma cg_after_removal j w :
      removes j w -> cg (state_after (b_loc w) (pfx (S j))) = b_val w.
    Proof.
      intros [[h Hf] Hh]. rewrite (pfx_S j _ Hf). rewrite state_after_snoc.
      unfold step_at.
      replace (at_loc (b_loc w) (BF (b_tid w) h (b_loc w))) with true
        by (symmetry; apply at_loc_true; reflexivity).
      unfold next. rewrite bookkeeping. unfold head_at in Hh.
      destruct (proj (b_loc w) (pend (b_tid w) (pfx j))) as [| c l]; [discriminate |].
      cbn in Hh. inversion Hh; subst c. reflexivity.
    Qed.

    Lemma cg_last_flush k x j u :
      last_flush_before k x j -> removes j u -> cg (state_after x (pfx k)) = b_val u.
    Proof.
      intros (Hf & Hjk & Hno) Hr.
      assert (Hx : b_loc u = x).
      { destruct Hf as [t [h Hf]]. destruct Hr as [[h' Hr] _]. unfold at_idx in *.
        rewrite Hf in Hr. inversion Hr. reflexivity. }
      subst x.
      induction k as [| k IH]; [lia |].
      destruct (le_lt_dec (length s) k) as [Hlen | Hlen].
      - rewrite pfx_S_none by auto.
        destruct Hf as [t [h Hf]]. apply at_idx_lt in Hf.
        apply IH; [lia |]. intros j' t' Hj'. apply Hno. lia.
      - destruct (lt_eq_lt_dec j k) as [[Hlt | Heq] | Hgt]; [| subst j; apply cg_after_removal; auto | lia].
        destruct (nth_error s k) as [b |] eqn:Hb; [| apply nth_error_None in Hb; lia].
        assert (Hnf : forall t, b <> BF t (b_handle b) (b_loc u)).
        { intros t Heq. rewrite Heq in Hb. apply (Hno k t); [lia |]. exists (b_handle b). exact Hb. }
        rewrite (cg_step_nonflush (b_loc u) k b Hb Hnf).
        apply IH; [lia |]. intros j' t' Hj'. apply Hno. lia.
    Qed.

    (** *** Facts that need every block to be enabled *)

    Section Enabled.
      Hypothesis Hen : forall x, enabled_along x s.

      (** Every flush block publishes some pending write. *)
      Lemma flush_effective j t x :
        flush_at j t x -> exists u, removes j u /\ b_tid u = t /\ b_loc u = x.
      Proof.
        intros [h Hj].
        specialize (Hen x j (BF t h x) Hj eq_refl). fold (pfx j) in Hen.
        apply flush_enabled_iff in Hen.
        destruct (proj x (pend t (pfx j))) as [| u l] eqn:Hp; [congruence |].
        assert (Hu : In u (proj x (pend t (pfx j)))) by (rewrite Hp; left; auto).
        apply In_proj in Hu. destruct Hu as [Hu Hux].
        assert (Hut : b_tid u = t) by (apply pend_In in Hu; tauto).
        exists u. split; [| auto]. split.
        - exists h. rewrite Hut, Hux. exact Hj.
        - unfold head_at. rewrite Hut, Hux, Hp. reflexivity.
      Qed.

      (** A read block returns the forwarded value or the global value
          ([RdF] / [RdM]). *)
      Lemma read_value i r :
        at_idx i r -> is_read r ->
        (exists u, last_at i u /\ b_tid u = b_tid r /\ b_loc u = b_loc r /\ b_val u = b_val r) \/
        (proj (b_loc r) (pend (b_tid r) (pfx i)) = [] /\
         b_val r = cg (state_after (b_loc r) (pfx i))).
      Proof.
        intros Hi Hr. destruct r as [| t h x a v |]; cbn in Hr; try contradiction.
        specialize (Hen x i _ Hi eq_refl). fold (pfx i) in Hen. cbn in Hen.
        rewrite bookkeeping in Hen.
        destruct Hen as [[Hne Hv] | [Hnil Hv]].
        - left. cbn.
          destruct (proj x (pend t (pfx i))) as [| c l] eqn:Hp; [exfalso; apply Hne; reflexivity |].
          set (u := last (c :: l) c).
          assert (Hlast : c :: l = removelast (c :: l) ++ [u]) by (apply app_removelast_last; discriminate).
          assert (Hu : In u (c :: l)) by (rewrite Hlast; apply in_or_app; right; left; auto).
          assert (Hu' : In u (proj x (pend t (pfx i)))) by (rewrite Hp; auto).
          apply In_proj in Hu'. destruct Hu' as [Hu' Hux].
          assert (Hut : b_tid u = t) by (apply pend_In in Hu'; tauto).
          exists u. split; [| split; [auto | split; auto]].
          + unfold last_at. rewrite Hut, Hux, Hp. apply hd_error_rev_iff.
            exists (removelast (c :: l)). exact Hlast.
          + rewrite Hv. rewrite Hlast. rewrite map_app. cbn. rewrite last_app_single. reflexivity.
        - right. cbn. destruct (proj x (pend t (pfx i))); [| cbn in Hnil; discriminate].
          auto.
      Qed.

    End Enabled.

  End Indexed.

End Pending.
