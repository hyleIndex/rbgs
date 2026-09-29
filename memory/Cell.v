(** * The buffered memory cell (Appendix L, Sections L.1-L.4)

    This file defines, for a location set [Loc] and a mode assignment [M]:

    - the cell signature [Cell_M[Loc]] (Def. mem:def:cellsig) as an
      effect signature, and its relaxed effect signature whose
      semi-independence relation is induced by the fence modes
      (Def. mem:def:instances);
    - traces as lists of atomic blocks (write, read, flush), each block
      carrying its thread and its future handle;
    - the buffered cell [Buf_ℓ] (Def. mem:def:cell) as a labelled
      transition system on blocks, and its linearized behaviour [VBuf];
    - pending writes [pend] (Def. mem:def:pend) and the bookkeeping
      lemma (Lemma mem:lem:book);
    - the flush contract [contract I] (Def. mem:def:contract);
    - the memory [V I] and the hidden specification [nu I]
      (Def. mem:def:model).

    Traces are lists of blocks rather than lists of events: the
    transition labels of Def. mem:def:cell are blocks, every block is
    atomic in [V], and the [\todo] after Def. mem:def:pend asks
    precisely for flushes to appear atomically.  An erasure to event
    lists over [RelaxedLTSSpec.ThreadEvent] is a separate concern
    (not in this file). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.Arith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Bool.Bool.
Require Import Stdlib.Logic.Classical.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import memory.Prelude.

Import ListNotations.

Set Implicit Arguments.

Module Cell.

  Import RelaxedSig.

  (** Threads are named as in the rest of the development
      ([LinCCALBase.tid = positive]). *)
  Definition tid : Type := positive.

  (** ** Mode assignments (Def. mem:def:cellsig)

      A mode assignment is a pair of (non-empty) sets of write modes and
      read modes, here equipped directly with the fence-mode functions of
      Def. mem:def:instances. *)
  Record ModeAssign : Type := {
    MW : Type;
    MR : Type;
    accW : MW -> FenceMode;
    accR : MR -> FenceMode;
  }.

  (** The parameters of the development: a set of locations with
      decidable equality and a mode assignment. *)
  Record Cfg : Type := {
    Loc : Type;
    Loc_eq_dec : forall x y : Loc, {x = y} + {x <> y};
    M : ModeAssign;
  }.

  Section Cell.
    Context (C : Cfg).

    Abbreviation Loc := (Loc C).
    Abbreviation MW := (MW (M C)).
    Abbreviation MR := (MR (M C)).
    Abbreviation accW := (accW (M C)).
    Abbreviation accR := (accR (M C)).

    Definition loc_eqb (x y : Loc) : bool :=
      if Loc_eq_dec C x y then true else false.

    Lemma loc_eqb_true x y : loc_eqb x y = true <-> x = y.
    Proof.
      unfold loc_eqb. destruct (Loc_eq_dec C x y); split; congruence.
    Qed.

    Lemma loc_eqb_false x y : loc_eqb x y = false <-> x <> y.
    Proof.
      unfold loc_eqb. destruct (Loc_eq_dec C x y); split; congruence.
    Qed.

    Lemma loc_eqb_refl x : loc_eqb x x = true.
    Proof. apply loc_eqb_true. reflexivity. Qed.

    (** ** The cell signature [Cell_M[Loc]] *)

    Inductive cell_op : Type :=
    | wrt (x : Loc) (v : nat) (a : MW)
    | rd (x : Loc) (a : MR)
    | flush (x : Loc).

    Definition cell_ar (m : cell_op) : Type :=
      match m with
      | wrt _ _ _ => unit
      | rd _ _ => nat
      | flush _ => unit
      end.

    Definition CellSig : Sig.t :=
      {| Sig.op := cell_op; Sig.ar := cell_ar |}.

    Definition op_loc (m : cell_op) : Loc :=
      match m with
      | wrt x _ _ => x
      | rd x _ => x
      | flush x => x
      end.

    Definition op_is_write (m : cell_op) : Prop :=
      match m with wrt _ _ _ => True | _ => False end.
    Definition op_is_read (m : cell_op) : Prop :=
      match m with rd _ _ => True | _ => False end.
    Definition op_is_flush (m : cell_op) : Prop :=
      match m with flush _ => True | _ => False end.

    (** The fence-mode function [E.access] of Def. mem:def:instances.
        [flush] is a logical operation related to nothing; giving it the
        full fence mode makes it semi-independent of nothing. *)
    Definition access (m : cell_op) : FenceMode :=
      match m with
      | wrt _ _ a => accW a
      | rd _ a => accR a
      | flush _ => Fence
      end.

    (** The semi-independence relation induced by the tensored signature
        with empty intra-cell relations (Def. mem:def:instances):
        a cross-location pair is semi-independent iff the mode of the
        first is at most [LFence] and the mode of the second at most
        [RFence]. *)
    Definition mode_indep (m m' : cell_op) : Prop :=
      op_loc m <> op_loc m' /\ access m ≤f LFence /\ access m' ≤f RFence.

    Definition CellRSig : RelaxedSig.t :=
      {|
        RelaxedSig.effect := CellSig;
        RelaxedSig.handle := nat;
        RelaxedSig.semi_independent := mode_indep;
        RelaxedSig.mode := access;
      |}.

    Lemma CellRSig_well_formed : RelaxedSig.well_formed CellRSig.
    Proof.
      constructor; cbn.
      - intros m (Hloc & _ & _). apply Hloc. reflexivity.
      - intros m m' (_ & Hl & _). exact Hl.
      - intros m m' (_ & _ & Hr). exact Hr.
    Qed.

    Lemma mode_indep_cross m m' : mode_indep m m' -> op_loc m <> op_loc m'.
    Proof. intros (H & _ & _). exact H. Qed.

    Lemma mode_indep_flush_l x m : ~ mode_indep (flush x) m.
    Proof. intros (_ & H & _). exact H. Qed.

    Lemma mode_indep_flush_r m x : ~ mode_indep m (flush x).
    Proof. intros (_ & _ & H). exact H. Qed.

    (** ** Blocks and traces

        A block is an atomic invocation/response pair of [Cell_M[Loc]],
        tagged with the issuing thread and the future handle of the
        invocation.  Flush blocks carry a handle as well (every move
        does), but nothing below depends on it. *)
    Inductive block : Type :=
    | BW (t : tid) (h : nat) (x : Loc) (v : nat) (a : MW)
    | BR (t : tid) (h : nat) (x : Loc) (a : MR) (v : nat)
    | BF (t : tid) (h : nat) (x : Loc).

    Definition trace : Type := list block.

    Definition b_tid (b : block) : tid :=
      match b with BW t _ _ _ _ | BR t _ _ _ _ | BF t _ _ => t end.
    Definition b_handle (b : block) : nat :=
      match b with BW _ h _ _ _ | BR _ h _ _ _ | BF _ h _ => h end.
    Definition b_loc (b : block) : Loc :=
      match b with BW _ _ x _ _ | BR _ _ x _ _ | BF _ _ x => x end.
    Definition b_val (b : block) : nat :=
      match b with BW _ _ _ v _ => v | BR _ _ _ _ v => v | BF _ _ _ => 0 end.
    Definition b_inv (b : block) : cell_op :=
      match b with
      | BW _ _ x v a => wrt x v a
      | BR _ _ x a _ => rd x a
      | BF _ _ x => flush x
      end.

    Definition is_write (b : block) : Prop :=
      match b with BW _ _ _ _ _ => True | _ => False end.
    Definition is_read (b : block) : Prop :=
      match b with BR _ _ _ _ _ => True | _ => False end.
    Definition is_flush (b : block) : Prop :=
      match b with BF _ _ _ => True | _ => False end.

    Definition is_writeb (b : block) : bool :=
      match b with BW _ _ _ _ _ => true | _ => false end.
    Definition is_readb (b : block) : bool :=
      match b with BR _ _ _ _ _ => true | _ => false end.
    Definition is_flushb (b : block) : bool :=
      match b with BF _ _ _ => true | _ => false end.

    Lemma is_writeb_true b : is_writeb b = true <-> is_write b.
    Proof. destruct b; cbn; intuition congruence. Qed.
    Lemma is_readb_true b : is_readb b = true <-> is_read b.
    Proof. destruct b; cbn; intuition congruence. Qed.
    Lemma is_flushb_true b : is_flushb b = true <-> is_flush b.
    Proof. destruct b; cbn; intuition congruence. Qed.

    Lemma b_loc_inv b : op_loc (b_inv b) = b_loc b.
    Proof. destruct b; reflexivity. Qed.

    Definition at_loc (x : Loc) (b : block) : bool := loc_eqb (b_loc b) x.
    Definition of_thread (t : tid) (b : block) : bool :=
      if Pos.eq_dec (b_tid b) t then true else false.

    Lemma at_loc_true x b : at_loc x b = true <-> b_loc b = x.
    Proof. unfold at_loc. apply loc_eqb_true. Qed.
    Lemma at_loc_false x b : at_loc x b = false <-> b_loc b <> x.
    Proof. unfold at_loc. apply loc_eqb_false. Qed.
    Lemma of_thread_true t b : of_thread t b = true <-> b_tid b = t.
    Proof. unfold of_thread. destruct (Pos.eq_dec (b_tid b) t); split; congruence. Qed.

    (** [proj x s] is the projection [s↾x] onto the blocks at [x]. *)
    Definition proj (x : Loc) (s : trace) : trace := filter (at_loc x) s.

    (** [hide] deletes every flush block (Def. mem:def:model). *)
    Definition hide (s : trace) : trace := filter (fun b => negb (is_flushb b)) s.

    Definition flush_free (s : trace) : Prop := forall b, In b s -> ~ is_flush b.

    Lemma proj_app x s1 s2 : proj x (s1 ++ s2) = proj x s1 ++ proj x s2.
    Proof. apply filter_app. Qed.

    Lemma proj_cons x b s :
      proj x (b :: s) = if at_loc x b then b :: proj x s else proj x s.
    Proof. reflexivity. Qed.

    Lemma proj_nil x : proj x [] = [].
    Proof. reflexivity. Qed.

    Lemma hide_app s1 s2 : hide (s1 ++ s2) = hide s1 ++ hide s2.
    Proof. apply filter_app. Qed.

    Lemma hide_flush_free s : flush_free s -> hide s = s.
    Proof.
      induction s as [| b s IH]; intros H; cbn; auto.
      assert (Hb : ~ is_flush b) by (apply H; left; auto).
      destruct b; cbn in *; try contradiction; f_equal; apply IH; intros b' Hb'; apply H; right; auto.
    Qed.

    Lemma hide_flush_free_result s : flush_free (hide s).
    Proof.
      intros b Hb. unfold hide in Hb. apply filter_In in Hb. destruct Hb as [_ Hb].
      destruct b; cbn in *; congruence.
    Qed.

    Lemma In_hide b s : In b (hide s) <-> In b s /\ ~ is_flush b.
    Proof.
      unfold hide. rewrite filter_In. rewrite negb_true_iff.
      destruct b; cbn; intuition congruence.
    Qed.

    (** ** The buffered cell [Buf_ℓ] (Def. mem:def:cell) *)

    (** A state is a global value and per-thread pending values. *)
    Record cstate : Type := {
      cg : nat;
      cP : tid -> list nat;
    }.

    Definition upd (P : tid -> list nat) (t : tid) (w : list nat) : tid -> list nat :=
      fun u => if Pos.eq_dec u t then w else P u.

    Lemma upd_same P t w : upd P t w t = w.
    Proof. unfold upd. destruct (Pos.eq_dec t t); congruence. Qed.

    Lemma upd_other P t u w : u <> t -> upd P t w u = P u.
    Proof. unfold upd. intros H. destruct (Pos.eq_dec u t); congruence. Qed.

    Definition init_state : cstate := {| cg := 0; cP := fun _ => [] |}.

    (** The four rules [Wr], [RdF], [RdM], [Flh].  The mode argument is
        inert.  The location index [x] is the cell's own location: a
        block at another location has no transition in [Buf_x]. *)
    Inductive cell_step (x : Loc) : block -> cstate -> cstate -> Prop :=
    | cs_wr t h v a st :
        cell_step x (BW t h x v a) st
          {| cg := cg st; cP := upd (cP st) t (cP st t ++ [v]) |}
    | cs_rdf t h a st v :
        cP st t <> [] ->
        v = last (cP st t) 0 ->
        cell_step x (BR t h x a v) st st
    | cs_rdm t h a st :
        cP st t = [] ->
        cell_step x (BR t h x a (cg st)) st st
    | cs_fl t h st v w :
        cP st t = v :: w ->
        cell_step x (BF t h x) st {| cg := v; cP := upd (cP st) t w |}.

    Inductive cell_path (x : Loc) : cstate -> trace -> cstate -> Prop :=
    | cp_nil st : cell_path x st [] st
    | cp_cons st b st' s st'' :
        cell_step x b st st' ->
        cell_path x st' s st'' ->
        cell_path x st (b :: s) st''.

    (** The linearized behaviour [V^Buf_x]: traces labelling a path from
        the initial state. *)
    Definition VBuf (x : Loc) (s : trace) : Prop :=
      exists st, cell_path x init_state s st.

    (** *** Functional presentation

        [Buf_x] is deterministic.  [enabled] and [next] present it as a
        guard and a successor function; [cell_step_iff] relates the two. *)
    Definition next (b : block) (st : cstate) : cstate :=
      match b with
      | BW t _ _ v _ => {| cg := cg st; cP := upd (cP st) t (cP st t ++ [v]) |}
      | BR _ _ _ _ _ => st
      | BF t _ _ =>
          match cP st t with
          | v :: w => {| cg := v; cP := upd (cP st) t w |}
          | [] => st
          end
      end.

    Definition enabled (b : block) (st : cstate) : Prop :=
      match b with
      | BW _ _ _ _ _ => True
      | BR t _ _ _ v =>
          (cP st t <> [] /\ v = last (cP st t) 0) \/ (cP st t = [] /\ v = cg st)
      | BF t _ _ => cP st t <> []
      end.

    Lemma cell_step_iff x b st st' :
      cell_step x b st st' <-> (b_loc b = x /\ enabled b st /\ st' = next b st).
    Proof.
      split.
      - intros H. inversion H; subst; cbn.
        + repeat split.
        + split; [reflexivity |]. split; [left; auto | reflexivity].
        + split; [reflexivity |]. split; [right; auto | reflexivity].
        + split; [reflexivity |]. split; [congruence |]. rewrite H0. reflexivity.
      - intros (Hloc & Hen & ->). destruct b as [t h y v a | t h y a v | t h y]; cbn in *; subst y.
        + constructor.
        + destruct Hen as [[Hne Hv] | [Hnil Hv]].
          * apply cs_rdf; auto.
          * subst v. apply cs_rdm; auto.
        + destruct (cP st t) as [| v w] eqn:HP; [congruence |].
          econstructor. eauto.
    Qed.

    (** The state of [Buf_x] after a trace (only the blocks at [x] act). *)
    Definition step_at (x : Loc) (st : cstate) (b : block) : cstate :=
      if at_loc x b then next b st else st.

    Definition state_after (x : Loc) (s : trace) : cstate :=
      fold_left (step_at x) s init_state.

    Lemma state_after_app x s1 s2 :
      state_after x (s1 ++ s2) = fold_left (step_at x) s2 (state_after x s1).
    Proof. unfold state_after. apply fold_left_app. Qed.

    Lemma state_after_snoc x s b :
      state_after x (s ++ [b]) = step_at x (state_after x s) b.
    Proof. rewrite state_after_app. reflexivity. Qed.

    Lemma cell_path_app x st s1 s2 st'' :
      cell_path x st (s1 ++ s2) st'' <->
      exists st', cell_path x st s1 st' /\ cell_path x st' s2 st''.
    Proof.
      revert st. induction s1 as [| b s1 IH]; intros st; cbn.
      - split.
        + intros H. exists st. split; [constructor | auto].
        + intros (st' & H1 & H2). inversion H1; subst. auto.
      - split.
        + intros H. inversion H; subst.
          apply IH in H5. destruct H5 as (st1 & H1 & H2).
          exists st1. split; [econstructor; eauto | auto].
        + intros (st' & H1 & H2). inversion H1; subst.
          econstructor; eauto. apply IH. eauto.
    Qed.

    Lemma cell_path_det x st s st1 st2 :
      cell_path x st s st1 -> cell_path x st s st2 -> st1 = st2.
    Proof.
      intros H1. revert st2. induction H1 as [| st b st' s st'' Hs Hp IH]; intros st2 H2.
      - inversion H2; auto.
      - inversion H2 as [| ? ? st2' ? ? Hs2 Hp2]; subst.
        apply cell_step_iff in Hs. apply cell_step_iff in Hs2.
        destruct Hs as (_ & _ & ->). destruct Hs2 as (_ & _ & ->). auto.
    Qed.

    (** [VBuf x (proj x s)] holds iff every block of [s] at [x] is enabled
        in the state reached by the preceding blocks at [x]; and the state
        reached is [state_after x s]. *)
    Lemma cell_path_proj_state x s st :
      cell_path x init_state (proj x s) st -> st = state_after x s.
    Proof.
      revert st. induction s as [| b s IH] using rev_ind; intros st H.
      - inversion H; subst. reflexivity.
      - rewrite proj_app in H. apply cell_path_app in H.
        destruct H as (st' & H1 & H2). apply IH in H1. subst st'.
        rewrite state_after_snoc. unfold step_at.
        cbn in H2. destruct (at_loc x b) eqn:Hx; cbn in H2.
        + inversion H2 as [| ? ? st1 ? ? Hs Hp]; subst. inversion Hp; subst.
          apply cell_step_iff in Hs. destruct Hs as (_ & _ & ->). reflexivity.
        + inversion H2; subst. reflexivity.
    Qed.

    Definition enabled_along (x : Loc) (s : trace) : Prop :=
      forall i b, nth_error s i = Some b -> b_loc b = x ->
        enabled b (state_after x (firstn i s)).

    Lemma VBuf_proj_iff x s : VBuf x (proj x s) <-> enabled_along x s.
    Proof.
      split.
      - intros (st & Hpath) i b Hi Hloc.
        assert (Hsplit : s = firstn i s ++ b :: skipn (S i) s) by (apply nth_error_split; auto).
        rewrite Hsplit in Hpath. rewrite proj_app in Hpath.
        apply cell_path_app in Hpath. destruct Hpath as (st1 & H1 & H2).
        apply cell_path_proj_state in H1. subst st1.
        cbn in H2. rewrite (proj2 (at_loc_true x b) Hloc) in H2.
        inversion H2 as [| ? ? st2 ? ? Hs Hp]; subst. apply cell_step_iff in Hs. tauto.
      - intros Hen. exists (state_after x s).
        induction s as [| b s IH] using rev_ind.
        + constructor.
        + rewrite proj_app. apply cell_path_app.
          exists (state_after x s). split.
          * apply IH. intros i b' Hi Hloc.
            assert (Hlt : i < length s) by (apply nth_error_Some; congruence).
            specialize (Hen i b'). rewrite nth_error_app1 in Hen by auto.
            specialize (Hen Hi Hloc). rewrite firstn_app in Hen.
            replace (i - length s) with 0 in Hen by lia. rewrite firstn_O, app_nil_r in Hen. auto.
          * rewrite state_after_snoc. unfold step_at. cbn.
            destruct (at_loc x b) eqn:Hx.
            -- econstructor; [| constructor].
               apply cell_step_iff. split; [apply at_loc_true; auto |]. split; auto.
               specialize (Hen (length s) b). rewrite nth_error_app2 in Hen by lia.
               rewrite Nat.sub_diag in Hen. cbn in Hen.
               rewrite firstn_app, firstn_all, Nat.sub_diag in Hen. cbn in Hen.
               rewrite app_nil_r in Hen. apply Hen; auto. apply at_loc_true; auto.
            -- constructor.
    Qed.

    (** ** Pending writes (Def. mem:def:pend) *)

    Fixpoint remove_first_at (x : Loc) (l : list block) : list block :=
      match l with
      | [] => []
      | b :: l' => if at_loc x b then l' else b :: remove_first_at x l'
      end.

    Definition pend_step (t : tid) (acc : list block) (b : block) : list block :=
      match b with
      | BW u _ _ _ _ => if Pos.eq_dec u t then acc ++ [b] else acc
      | BF u _ x => if Pos.eq_dec u t then remove_first_at x acc else acc
      | BR _ _ _ _ _ => acc
      end.

    (** [pend t s] lists the pending writes of thread [t] after [s], in
        issue order. *)
    Definition pend (t : tid) (s : trace) : list block :=
      fold_left (pend_step t) s [].

    Lemma pend_app t s1 s2 : pend t (s1 ++ s2) = fold_left (pend_step t) s2 (pend t s1).
    Proof. unfold pend. apply fold_left_app. Qed.

    Lemma pend_snoc t s b : pend t (s ++ [b]) = pend_step t (pend t s) b.
    Proof. rewrite pend_app. reflexivity. Qed.

    Lemma remove_first_at_cons x b l :
      remove_first_at x (b :: l) = if at_loc x b then l else b :: remove_first_at x l.
    Proof. reflexivity. Qed.

    Lemma proj_remove_first_same x l :
      proj x (remove_first_at x l) = tl (proj x l).
    Proof.
      induction l as [| b l IH]; auto.
      rewrite remove_first_at_cons, proj_cons.
      destruct (at_loc x b) eqn:Hb.
      - reflexivity.
      - rewrite proj_cons, Hb. auto.
    Qed.

    Lemma proj_remove_first_other x y l :
      x <> y -> proj x (remove_first_at y l) = proj x l.
    Proof.
      intros Hxy. induction l as [| b l IH]; auto.
      rewrite remove_first_at_cons.
      destruct (at_loc y b) eqn:Hby.
      - apply at_loc_true in Hby. rewrite proj_cons.
        assert (Hx : at_loc x b = false) by (apply at_loc_false; congruence).
        rewrite Hx. reflexivity.
      - rewrite !proj_cons. rewrite IH. reflexivity.
    Qed.

    Lemma remove_first_at_no x l :
      proj x l = [] -> remove_first_at x l = l.
    Proof.
      induction l as [| b l IH]; intros H; auto.
      rewrite remove_first_at_cons. rewrite proj_cons in H.
      destruct (at_loc x b) eqn:Hb.
      - discriminate.
      - f_equal. auto.
    Qed.

    (** Every pending write is a write of the thread, and was issued in
        the trace. *)
    Lemma pend_In t s b :
      In b (pend t s) -> In b s /\ is_write b /\ b_tid b = t.
    Proof.
      revert b. induction s as [| a s IH] using rev_ind; intros b H.
      - inversion H.
      - rewrite pend_snoc in H. unfold pend_step in H.
        destruct a as [u h x v m | u h x m v | u h x].
        + destruct (Pos.eq_dec u t).
          * apply in_app_or in H. destruct H as [H | [H | []]].
            -- apply IH in H. destruct H as (H1 & H2 & H3). repeat split; auto.
               apply in_or_app. auto.
            -- subst. repeat split; auto. apply in_or_app. right. left. auto.
          * apply IH in H. destruct H as (H1 & H2 & H3). repeat split; auto.
            apply in_or_app. auto.
        + apply IH in H. destruct H as (H1 & H2 & H3). repeat split; auto.
          apply in_or_app. auto.
        + assert (Hsub : forall l, In b (remove_first_at x l) -> In b l).
          { clear. intros l. induction l as [| c l IH]; cbn; auto.
            destruct (at_loc x c); cbn; auto.
            intros [-> | H]; auto. }
          destruct (Pos.eq_dec u t).
          * apply Hsub in H. apply IH in H. destruct H as (H1 & H2 & H3). repeat split; auto.
            apply in_or_app. auto.
          * apply IH in H. destruct H as (H1 & H2 & H3). repeat split; auto.
            apply in_or_app. auto.
    Qed.

    (** *** Bookkeeping (Lemma mem:lem:book)

        The per-thread pending values of [Buf_x] after [s] are the values of
        the pending writes of the thread at [x], in order.  No hypothesis on
        [s] is needed for this functional form: the state is computed by
        [state_after] whether or not every block was enabled. *)
    Lemma bookkeeping x s t :
      cP (state_after x s) t = map b_val (proj x (pend t s)).
    Proof.
      induction s as [| b s IH] using rev_ind.
      - reflexivity.
      - rewrite state_after_snoc, pend_snoc.
        unfold step_at, pend_step.
        destruct b as [u h y v a | u h y a v | u h y].
        + (* write block *)
          destruct (at_loc x (BW u h y v a)) eqn:Hx; cbn in Hx.
          * apply at_loc_true in Hx. cbn in Hx. subst y.
            destruct (Pos.eq_dec u t) as [-> | Hut].
            -- cbn. rewrite upd_same. rewrite IH.
               rewrite proj_app, proj_cons, proj_nil.
               replace (at_loc x (BW t h x v a)) with true
                 by (symmetry; apply at_loc_true; reflexivity).
               rewrite map_app. reflexivity.
            -- cbn. rewrite upd_other by auto. auto.
          * destruct (Pos.eq_dec u t) as [-> | Hut]; auto.
            rewrite proj_app, proj_cons, proj_nil, Hx. rewrite app_nil_r. auto.
        + (* read block *)
          destruct (at_loc x (BR u h y a v)); cbn; auto.
        + (* flush block *)
          destruct (at_loc x (BF u h y)) eqn:Hx; cbn in Hx.
          * apply at_loc_true in Hx. cbn in Hx. subst y.
            destruct (Pos.eq_dec u t) as [-> | Hut].
            -- cbn. rewrite proj_remove_first_same. rewrite IH.
               destruct (proj x (pend t s)) as [| b l]; cbn.
               ++ exact IH.
               ++ rewrite upd_same. reflexivity.
            -- cbn. destruct (cP (state_after x s) u) as [| v w]; cbn; auto.
               rewrite upd_other by auto. auto.
          * apply at_loc_false in Hx. cbn in Hx.
            destruct (Pos.eq_dec u t) as [-> | Hut]; auto.
            rewrite proj_remove_first_other by auto. auto.
    Qed.

    (** Consequently a flush block of [t] at [x] is enabled after [s] iff
        [t] has a pending write at [x]. *)
    Lemma flush_enabled_iff x s t h :
      enabled (BF t h x) (state_after x s) <-> proj x (pend t s) <> [].
    Proof.
      cbn. rewrite bookkeeping. destruct (proj x (pend t s)); cbn; split; congruence.
    Qed.

    (** ** The flush contract (Def. mem:def:contract) *)

    (** [I] is a semi-independence relation on invocations.  A trace
        satisfies the contract if, at every flush block that publishes a
        pending write [m], every pending write [m'] of the same thread with a
        smaller handle is semi-independent of [m].  Only the write--write
        part of [I] is used. *)
    Definition contract (I : cell_op -> cell_op -> Prop) (s : trace) : Prop :=
      forall s1 t h x s2 m,
        s = s1 ++ BF t h x :: s2 ->
        hd_error (proj x (pend t s1)) = Some m ->
        forall m', In m' (pend t s1) -> b_handle m' < b_handle m ->
          I (b_inv m') (b_inv m).

    (** Prop. mem:prop:contract: the contract is prefix-closed. *)
    Lemma contract_prefix I s1 s2 : contract I (s1 ++ s2) -> contract I s1.
    Proof.
      intros H p t h x q m Hs Hm m' Hm' Hlt.
      eapply H; eauto. rewrite Hs. rewrite <- app_assoc. reflexivity.
    Qed.

    Lemma contract_nil I : contract I [].
    Proof.
      intros p t h x q m Hs. destruct p; discriminate.
    Qed.

    (** ** The memory and its hidden specification (Def. mem:def:model) *)

    Definition V (I : cell_op -> cell_op -> Prop) (s : trace) : Prop :=
      contract I s /\ forall x, VBuf x (proj x s).

    Definition nu (I : cell_op -> cell_op -> Prop) (s : trace) : Prop :=
      exists s', V I s' /\ hide s' = s.

    Lemma V_prefix I s1 s2 : V I (s1 ++ s2) -> V I s1.
    Proof.
      intros [Hc Hb]. split.
      - eapply contract_prefix; eauto.
      - intros x. specialize (Hb x). rewrite proj_app in Hb.
        destruct Hb as (st & Hp). apply cell_path_app in Hp.
        destruct Hp as (st' & H1 & _). exists st'. auto.
    Qed.

    Lemma nu_flush_free I s : nu I s -> flush_free s.
    Proof.
      intros (s' & _ & <-). apply hide_flush_free_result.
    Qed.

  End Cell.

  Arguments wrt {C} _ _ _.
  Arguments rd {C} _ _.
  Arguments flush {C} _.
  Arguments BW {C} _ _ _ _ _.
  Arguments BR {C} _ _ _ _ _.
  Arguments BF {C} _ _ _.

  Arguments loc_eqb {C} _ _.
  Arguments op_loc {C} _.
  Arguments op_is_write {C} _.
  Arguments op_is_read {C} _.
  Arguments op_is_flush {C} _.
  Arguments access {C} _.
  Arguments mode_indep {C} _ _.
  Arguments b_tid {C} _.
  Arguments b_handle {C} _.
  Arguments b_loc {C} _.
  Arguments b_val {C} _.
  Arguments b_inv {C} _.
  Arguments is_write {C} _.
  Arguments is_read {C} _.
  Arguments is_flush {C} _.
  Arguments is_writeb {C} _.
  Arguments is_readb {C} _.
  Arguments is_flushb {C} _.
  Arguments at_loc {C} _ _.
  Arguments of_thread {C} _ _.
  Arguments proj {C} _ _.
  Arguments hide {C} _.
  Arguments flush_free {C} _.
  Arguments cell_step {C} _ _ _ _.
  Arguments cell_path {C} _ _ _ _.
  Arguments VBuf {C} _ _.
  Arguments next {C} _ _.
  Arguments enabled {C} _ _.
  Arguments step_at {C} _ _ _.
  Arguments state_after {C} _ _.
  Arguments enabled_along {C} _ _.
  Arguments remove_first_at {C} _ _.
  Arguments pend_step {C} _ _ _.
  Arguments pend {C} _ _.
  Arguments contract {C} _ _.
  Arguments V {C} _ _.
  Arguments nu {C} _ _.

  (** ** Instances (Def. mem:def:instances) *)

  Module Instances.

    (** TSO and PSO: uniform modes. *)
    Definition TSO_modes : ModeAssign :=
      {| MW := unit; MR := unit; accW := fun _ => LFence; accR := fun _ => RFence |}.

    Definition PSO_modes : ModeAssign :=
      {| MW := unit; MR := unit; accW := fun _ => Local; accR := fun _ => RFence |}.

    (** Release/acquire memory: [Access_W = {rlx, rel}], [Access_R = {rlx, acq}]. *)
    Inductive WMode : Type := wrlx | rel.
    Inductive RMode : Type := rrlx | acq.

    Definition RC_accW (a : WMode) : FenceMode :=
      match a with wrlx => Local | rel => LFence end.
    Definition RC_accR (a : RMode) : FenceMode :=
      match a with rrlx => Local | acq => RFence end.

    Definition RC_modes : ModeAssign :=
      {| MW := WMode; MR := RMode; accW := RC_accW; accR := RC_accR |}.

    Definition TSO_cfg (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}) : Cfg :=
      {| Loc := Loc; Loc_eq_dec := dec; M := TSO_modes |}.
    Definition PSO_cfg (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}) : Cfg :=
      {| Loc := Loc; Loc_eq_dec := dec; M := PSO_modes |}.
    Definition RC_cfg (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}) : Cfg :=
      {| Loc := Loc; Loc_eq_dec := dec; M := RC_modes |}.

    Section Shape.
      Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).
      Abbreviation RC := (RC_cfg dec).

      (** Lemma mem:lem:shape, clause by clause, for the induced relation. *)
      Lemma RC_shape_WR x v a y b :
        x <> y -> mode_indep (C := RC) (wrt x v a) (rd y b).
      Proof.
        intros Hxy. repeat split; auto; cbn.
        - destruct a; exact I.
        - destruct b; exact I.
      Qed.

      Lemma RC_shape_RR x a y b :
        x <> y -> (mode_indep (C := RC) (rd x a) (rd y b) <-> a = rrlx).
      Proof.
        intros Hxy. unfold mode_indep. cbn. destruct a, b; cbn; intuition congruence.
      Qed.

      Lemma RC_shape_RW x a y v b :
        x <> y -> (mode_indep (C := RC) (rd x a) (wrt y v b) <-> (a = rrlx /\ b = wrlx)).
      Proof.
        intros Hxy. unfold mode_indep. cbn. destruct a, b; cbn; intuition congruence.
      Qed.

      Lemma RC_shape_WW x v a y v' b :
        x <> y -> (mode_indep (C := RC) (wrt x v a) (wrt y v' b) <-> b = wrlx).
      Proof.
        intros Hxy. unfold mode_indep. cbn. destruct a, b; cbn; intuition congruence.
      Qed.

      Lemma RC_shape_same_loc m m' :
        op_loc m = op_loc m' -> ~ mode_indep (C := RC) m m'.
      Proof.
        intros H (Hne & _ & _). congruence.
      Qed.
    End Shape.

    Section TSO_PSO.
      Context (Loc : Type) (dec : forall x y : Loc, {x = y} + {x <> y}).

      (** Under TSO only a write followed by a read of another location is
          semi-independent (Def. mem:def:instances). *)
      Lemma TSO_indep_iff m m' :
        mode_indep (C := TSO_cfg dec) m m' <->
        (op_loc m <> op_loc m' /\ op_is_write m /\ op_is_read m').
      Proof.
        unfold mode_indep. destruct m, m'; cbn; intuition.
      Qed.

      (** Under PSO, additionally two writes to different locations. *)
      Lemma PSO_indep_iff m m' :
        mode_indep (C := PSO_cfg dec) m m' <->
        (op_loc m <> op_loc m' /\ op_is_write m /\ (op_is_read m' \/ op_is_write m')).
      Proof.
        unfold mode_indep. destruct m, m'; cbn; intuition.
      Qed.
    End TSO_PSO.

  End Instances.

End Cell.
