(** * Extraction (Lemma mem:lem:extract, with Lemmas mem:lem:handleorder and
      mem:lem:complete)

    From a trace [s ∈ ν_E[Locs]] that presents a candidate [X] and respects
    an admissible [pre], build an OMCA-consistent witness [(mo, rf)] for [X].

    Throughout, [I] is a semi-independence relation on invocations that
    relates no two invocations at the same location (Lemma mem:lem:shape
    for [RC.I]; also true of [TSO.I] and [PSO.I]), which is all the
    proofs of Section L.6 use about [RC.I]. *)

Require Import Coq.Lists.List.
Require Import Coq.Arith.Arith.
Require Import Coq.micromega.Lia.
Require Import Coq.PArith.PArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Logic.Classical.
Require Import Coq.Relations.Relation_Definitions.
Require Import Coq.Relations.Relation_Operators.

Require Import memory.Prelude.
Require Import memory.Cell.
Require Import memory.Declarative.
Require Import memory.Pending.

Import ListNotations.

Module Extraction.

  Import Cell Decl Pending.

  Section Extraction.
    Context (C : Cfg).

    Notation block := (block C).
    Notation trace := (trace C).

    Variable I : cell_op C -> cell_op C -> Prop.
    Hypothesis HI : forall m m', I m m' -> op_loc m <> op_loc m'.

    Variable X : cand C.
    Hypothesis HX : wf_cand X.

    Variable pre : relation block.
    Hypothesis Hadm : admissible X I pre.

    (** The flush-free trace presenting [X]. *)
    Variable s : trace.
    Hypothesis Hpres : presents s X.
    Hypothesis Hresp : respects s pre.

    Lemma NoDup_s : NoDup s.
    Proof.
      eapply Permutation_NoDup; [symmetry; exact Hpres |]. apply (ops_nodup HX).
    Qed.

    Lemma In_s b : In b s <-> In b (ops X).
    Proof.
      split; intros H.
      - eapply Permutation_in; [exact Hpres | exact H].
      - eapply Permutation_in; [symmetry; exact Hpres | exact H].
    Qed.

    Lemma s_flush_free : flush_free s.
    Proof.
      intros b Hb. apply In_s in Hb. apply (ops_noflush HX). exact Hb.
    Qed.

    (** ** Properties of any trace hiding to [s] *)

    Section Hiding.
      Variable sh : trace.
      Hypothesis Hhide : hide sh = s.

      Lemma NoDup_hide_sh : NoDup (hide sh).
      Proof. rewrite Hhide. apply NoDup_s. Qed.

      Lemma In_sh_ops b : In b sh -> ~ is_flush b -> In b (ops X).
      Proof.
        intros Hb Hnf. apply In_s. rewrite <- Hhide. apply In_hide. auto.
      Qed.

      Lemma respects_sh : respects sh pre.
      Proof.
        intros a b Hab. apply Hresp in Hab. rewrite <- Hhide in Hab.
        eapply before_filter_inv. exact Hab.
      Qed.

      Lemma before_sh_of_s a b : before s a b -> before sh a b.
      Proof.
        intros H. rewrite <- Hhide in H. eapply before_filter_inv. exact H.
      Qed.

      Lemma before_s_of_sh a b :
        before sh a b -> ~ is_flush a -> ~ is_flush b -> before s a b.
      Proof.
        intros H Ha Hb. rewrite <- Hhide. apply before_filter; auto.
        - destruct a; cbn in *; tauto.
        - destruct b; cbn in *; tauto.
      Qed.

      Lemma unique_sh b : ~ is_flush b -> unique_occ sh b.
      Proof. apply unique_occ_nonflush. apply NoDup_hide_sh. Qed.

      Lemma po_loc_before a b : po_loc X a b -> before sh a b.
      Proof.
        intros H. apply respects_sh. destruct Hadm as (Hpre0 & _ & _). apply Hpre0.
        apply pre0_same_loc_po; auto.
      Qed.

      Lemma tc_pre_before a b : (pre⁺) a b -> before sh a b.
      Proof.
        intros H. induction H as [a b Hab | a b c Hab IH1 Hbc IH2].
        - apply respects_sh. exact Hab.
        - eapply before_trans_u; [| exact IH1 | exact IH2].
          apply unique_sh. destruct Hadm as (_ & _ & Hdom).
          assert (In b (ops X)).
          { clear IH1 IH2. induction Hab as [a' b' Hab' | a' b' c' Hab' IH1' Hbc' IH2']; auto.
            apply Hdom in Hab'. tauto. }
          apply (ops_noflush HX). auto.
      Qed.

      (** Lemma mem:lem:handleorder: write blocks of one thread at one
          location occur in increasing handle order. *)
      Lemma handle_ordered a b :
        before sh a b -> is_write a -> is_write b ->
        b_tid a = b_tid b -> b_loc a = b_loc b -> b_handle a < b_handle b.
      Proof.
        intros Hab Ha Hb Htid Hloc.
        assert (Hna : ~ is_flush a) by (destruct a; cbn in *; tauto).
        assert (Hnb : ~ is_flush b) by (destruct b; cbn in *; tauto).
        assert (Hne : a <> b).
        { intros Heq. subst b. exact (before_irrefl_u (unique_sh a Hna) Hab). }
        assert (Hina : In a (ops X)) by (apply In_sh_ops; auto; eapply before_In_l; eauto).
        assert (Hinb : In b (ops X)) by (apply In_sh_ops; auto; eapply before_In_r; eauto).
        destruct (po_total HX Hina Hinb Htid Hne) as [Hpo | Hpo].
        - apply (po_handles HX); auto.
        - exfalso. assert (Hba : before sh b a) by (apply po_loc_before; split; auto).
          exact (before_asym_u (unique_sh a Hna) (unique_sh b Hnb) Hab Hba).
      Qed.

    End Hiding.

    (** ** Completion (Lemma mem:lem:complete) *)

    (** Handle order for the write blocks of a trace, as a standalone
        property preserved by appending flush blocks. *)
    Definition handle_ordered_tr (sh : trace) : Prop :=
      forall a b, before sh a b -> is_write a -> is_write b ->
        b_tid a = b_tid b -> b_loc a = b_loc b -> b_handle a < b_handle b.

    Lemma handle_ordered_snoc_flush sh t h x :
      handle_ordered_tr sh -> handle_ordered_tr (sh ++ [BF t h x]).
    Proof.
      intros H a b Hab Ha Hb Htid Hloc.
      apply before_app_inv in Hab. destruct Hab as [Hab | [Hab | [Hina Hinb]]].
      - apply H; auto.
      - destruct Hab as (i & j & Hij & Hi & Hj). destruct j as [| j]; [lia | destruct j; discriminate].
      - destruct Hinb as [<- | []]. destruct Hb.
    Qed.

    Lemma remove_first_at_length x (l : list block) :
      proj x l <> [] -> S (length (remove_first_at x l)) = length l.
    Proof.
      induction l as [| b l IH]; intros H.
      - exfalso. apply H. reflexivity.
      - rewrite remove_first_at_cons. rewrite proj_cons in H.
        destruct (at_loc x b); cbn; auto.
    Qed.

    Lemma min_handle (l : list block) :
      l <> [] -> exists w, In w l /\ forall w', In w' l -> b_handle w <= b_handle w'.
    Proof.
      induction l as [| a l IH]; intros H; [congruence |].
      destruct l as [| b l].
      - exists a. split; [left; auto |]. intros w' [<- | []]. auto.
      - destruct IH as (w & Hw & Hmin); [discriminate |].
        destruct (le_lt_dec (b_handle a) (b_handle w)) as [Hle | Hlt].
        + exists a. split; [left; auto |]. intros w' [<- | Hw']; [auto |].
          specialize (Hmin w' Hw'). lia.
        + exists w. split; [right; auto |]. intros w' [<- | Hw']; [lia | auto].
    Qed.

    (** One completion step: publish the pending write of [t] with the least
        handle.  The contract holds vacuously at the new flush. *)
    Lemma flush_step (sh : trace) (t : tid) :
      V I sh -> hide sh = s -> handle_ordered_tr sh -> pend t sh <> [] ->
      exists sh',
        V I sh' /\ hide sh' = s /\ handle_ordered_tr sh' /\
        S (length (pend t sh')) = length (pend t sh) /\
        (forall u, u <> t -> pend u sh' = pend u sh).
    Proof.
      intros HV Hhide Hho Hne.
      destruct (min_handle _ Hne) as (w & Hw & Hmin).
      pose proof (pend_In _ _ _ Hw) as (Hwsh & Hww & Hwt).
      set (x := b_loc w).
      assert (Hnd : NoDup (hide sh)) by (rewrite Hhide; apply NoDup_s).
      (* [w] is the oldest pending write of [t] at [x] *)
      assert (Hhead : hd_error (proj x (pend t sh)) = Some w).
      { assert (Hh : head_at C sh (length sh) w).
        { apply head_at_iff; auto. unfold pending. rewrite (pfx_all C sh). split; [rewrite Hwt; auto |].
          intros w' Hw' Hloc Htid Hne'. rewrite Htid, Hwt in Hw'.
          pose proof (pend_In _ _ _ Hw') as (Hw'sh & Hww' & _).
          destruct (before_total_u (l := sh) (x := w) (y := w')) as [Hb | Hb]; auto.
          - apply unique_occ_nonflush; auto. destruct w; cbn in *; tauto.
          - apply unique_occ_nonflush; auto. destruct w'; cbn in *; tauto.
          - exfalso. specialize (Hho _ _ Hb Hww' Hww Htid Hloc).
            specialize (Hmin _ Hw'). lia. }
        unfold head_at in Hh. rewrite (pfx_all C sh), Hwt in Hh. exact Hh. }
      exists (sh ++ [BF t 0 x]).
      assert (Hproj : proj x (pend t sh) <> []) by (intros Hp; rewrite Hp in Hhead; discriminate).
      split; [| split; [| split; [| split]]].
      - (* V *)
        destruct HV as [Hc Hb]. split.
        + intros s1 t' h x' s2 m Hs Hm m' Hm' Hlt.
          apply snoc_split in Hs. destruct Hs as [(-> & -> & Heq) | (s2' & -> & Hs)].
          * inversion Heq; subst t' x'. rewrite Hhead in Hm. inversion Hm; subst m.
            specialize (Hmin _ Hm'). lia.
          * eapply Hc; eauto.
        + intros y. rewrite proj_app. rewrite proj_cons, proj_nil.
          destruct (at_loc y (BF t 0 x)) eqn:Hy.
          * apply at_loc_true in Hy. cbn in Hy. subst y.
            destruct (Hb x) as [st Hpath]. exists (next (BF t 0 x) st).
            apply cell_path_app. exists st. split; auto.
            econstructor; [| constructor].
            apply cell_step_iff. split; [reflexivity |]. split; [| reflexivity].
            apply cell_path_proj_state in Hpath. subst st.
            apply flush_enabled_iff. exact Hproj.
          * rewrite app_nil_r. apply Hb.
      - (* hide *)
        rewrite hide_app. cbn. rewrite app_nil_r. exact Hhide.
      - apply handle_ordered_snoc_flush. exact Hho.
      - rewrite pend_snoc. unfold pend_step. destruct (Pos.eq_dec t t); [| congruence].
        apply remove_first_at_length. exact Hproj.
      - intros u Hu. rewrite pend_snoc. unfold pend_step.
        destruct (Pos.eq_dec t u); [congruence | reflexivity].
    Qed.

    Lemma complete_thread (t : tid) (n : nat) :
      forall sh, V I sh -> hide sh = s -> handle_ordered_tr sh -> length (pend t sh) = n ->
      exists sh',
        V I sh' /\ hide sh' = s /\ handle_ordered_tr sh' /\ pend t sh' = [] /\
        (forall u, u <> t -> pend u sh' = pend u sh).
    Proof.
      induction n as [| n IH]; intros sh HV Hhide Hho Hlen.
      - exists sh. split; [| split; [| split; [| split]]]; auto.
        destruct (pend t sh); [reflexivity | discriminate].
      - assert (Hne : pend t sh <> []) by (destruct (pend t sh); [discriminate | congruence]).
        destruct (flush_step sh t HV Hhide Hho Hne) as (sh' & HV' & Hhide' & Hho' & Hlen' & Hother).
        destruct (IH sh' HV' Hhide' Hho') as (sh'' & HV'' & Hhide'' & Hho'' & Hemp & Hother'); [lia |].
        exists sh''. split; [| split; [| split; [| split]]]; auto.
        intros u Hu. rewrite Hother'; auto.
    Qed.

    Lemma complete_threads (ts : list tid) :
      forall sh, V I sh -> hide sh = s -> handle_ordered_tr sh ->
      exists sh',
        V I sh' /\ hide sh' = s /\ handle_ordered_tr sh' /\
        (forall t, In t ts -> pend t sh' = []) /\
        (forall t, pend t sh = [] -> pend t sh' = []).
    Proof.
      induction ts as [| t ts IH]; intros sh HV Hhide Hho.
      - exists sh. split; [| split; [| split; [| split]]]; auto. intros t [].
      - destruct (complete_thread t (length (pend t sh)) sh HV Hhide Hho eq_refl)
          as (sh1 & HV1 & Hhide1 & Hho1 & Hemp1 & Hother1).
        destruct (IH sh1 HV1 Hhide1 Hho1) as (sh2 & HV2 & Hhide2 & Hho2 & Hts & Hkeep).
        exists sh2. split; [| split; [| split; [| split]]]; auto.
        + intros u [<- | Hu]; auto.
        + intros u Hu. apply Hkeep. destruct (Pos.eq_dec u t) as [-> | Hut]; auto.
          rewrite Hother1; auto.
    Qed.

    (** Lemma mem:lem:complete: every witness extends to one in which every
        write has been published. *)
    Lemma completion (sh : trace) :
      V I sh -> hide sh = s ->
      exists sb,
        V I sb /\ hide sb = s /\ handle_ordered_tr sb /\ respects sb pre /\
        forall t, pend t sb = [].
    Proof.
      intros HV Hhide.
      assert (Hho : handle_ordered_tr sh) by (intros a b; apply (handle_ordered sh Hhide)).
      destruct (complete_threads (map b_tid sh) sh HV Hhide Hho) as (sb & HV' & Hhide' & Hho' & Hts & Hkeep).
      exists sb. split; [| split; [| split; [| split]]]; auto.
      - apply respects_sh. exact Hhide'.
      - intros t. destruct (in_dec Pos.eq_dec t (map b_tid sh)) as [Hin | Hnin]; auto.
        apply Hkeep. destruct (pend t sh) as [| w l] eqn:Hp; auto.
        exfalso. apply Hnin.
        assert (In w (pend t sh)) by (rewrite Hp; left; auto).
        apply pend_In in H. destruct H as (H & _ & <-). apply in_map. exact H.
    Qed.

    (** ** The witness extracted from a completed trace *)

    Section Witness.
      Variable sb : trace.
      Hypothesis HVb : V I sb.
      Hypothesis Hhideb : hide sb = s.
      Hypothesis Hhob : handle_ordered_tr sb.
      Hypothesis Hrespb : respects sb pre.
      Hypothesis Hcomplete : forall t, pend t sb = [].

      Lemma Hndb : NoDup (hide sb).
      Proof. apply NoDup_hide_sh. exact Hhideb. Qed.

      Lemma Henb : forall x, enabled_along x sb.
      Proof. intros x. apply VBuf_proj_iff. apply HVb. Qed.

      Notation at_idx := (Pending.at_idx C sb).
      Notation pfx := (Pending.pfx C sb).
      Notation pending := (Pending.pending C sb).
      Notation head_at := (Pending.head_at C sb).
      Notation last_at := (Pending.last_at C sb).
      Notation flush_at := (Pending.flush_at C sb).
      Notation removes := (Pending.removes C sb).
      Notation last_flush_before := (Pending.last_flush_before C sb).
      Notation no_flush_before := (Pending.no_flush_before C sb).

      (** *** Indices *)

      Definition idx (b : block) (i : nat) : Prop := at_idx i b.
      Definition fidx (w : block) (j : nat) : Prop := removes j w.

      Lemma ops_idx b : In b (ops X) -> exists i, idx b i.
      Proof.
        intros Hb. apply In_s in Hb. rewrite <- Hhideb in Hb. apply In_hide in Hb.
        destruct Hb as [Hb _]. apply In_nth_error in Hb. destruct Hb as [i Hi]. exists i. exact Hi.
      Qed.

      Lemma idx_ops b i : idx b i -> ~ is_flush b -> In b (ops X).
      Proof.
        intros Hi Hb. eapply In_sh_ops; eauto. eapply nth_error_In. exact Hi.
      Qed.

      Lemma idx_unique b i j : idx b i -> idx b j -> ~ is_flush b -> i = j.
      Proof. intros Hi Hj Hb. eapply at_idx_unique; eauto. exact Hndb. Qed.

      Lemma idx_before a b i j : idx a i -> idx b j -> i < j -> before sb a b.
      Proof. intros Hi Hj Hij. exists i, j. auto. Qed.

      Lemma before_idx a b : before sb a b -> ~ is_flush a -> ~ is_flush b ->
        forall i j, idx a i -> idx b j -> i < j.
      Proof.
        intros (i' & j' & Hij & Hi' & Hj') Ha Hb i j Hi Hj.
        assert (i = i') by (eapply idx_unique; eauto). assert (j = j') by (eapply idx_unique; eauto).
        lia.
      Qed.

      Lemma write_not_flush (w : block) : is_write w -> ~ is_flush w.
      Proof. destruct w; cbn; tauto. Qed.

      Lemma read_not_flush (r : block) : is_read r -> ~ is_flush r.
      Proof. destruct r; cbn; tauto. Qed.

      Lemma fidx_exists w : In w (ops X) -> is_write w -> exists j, fidx w j.
      Proof.
        intros Hw Hww. destruct (ops_idx w Hw) as [i Hi].
        assert (Hlt : i < length sb) by (eapply at_idx_lt; eauto).
        assert (Hnp : ~ pending (length sb) w).
        { unfold Pending.pending. rewrite pfx_all. rewrite Hcomplete. intros []. }
        destruct (issued_not_pending_removed C sb Hndb i w (length sb) Hi Hww Hlt Hnp) as (j & _ & Hj).
        exists j. exact Hj.
      Qed.

      Lemma fidx_unique w j j' : fidx w j -> fidx w j' -> j = j'.
      Proof. intros. eapply removes_unique; eauto. exact Hndb. Qed.

      Lemma fidx_inj w w' j : fidx w j -> fidx w' j -> w = w'.
      Proof. intros. eapply removes_head_unique; eauto. Qed.

      Lemma fidx_write w j : fidx w j -> is_write w.
      Proof. intros H. eapply removes_write; eauto. Qed.

      Lemma fidx_gt_idx w j i : fidx w j -> idx w i -> i < j.
      Proof. intros. eapply removes_after_idx; eauto. exact Hndb. Qed.

      Lemma fidx_flush w j : fidx w j -> flush_at j (b_tid w) (b_loc w).
      Proof. intros [H _]. exact H. Qed.

      Lemma pending_ops k w : pending k w -> In w (ops X).
      Proof.
        intros H. pose proof (pending_write C sb k w H) as Hw.
        apply In_pend_pfx in H. destruct H as (i & _ & Hi).
        eapply idx_ops; eauto. apply write_not_flush. auto.
      Qed.

      Lemma fidx_ops w j : fidx w j -> In w (ops X).
      Proof. intros H. eapply pending_ops. eapply removes_pending. exact H. Qed.

      Lemma pending_iff_fidx w i j k : idx w i -> fidx w j -> (pending k w <-> i < k <= j).
      Proof. intros. eapply pending_interval; eauto. exact Hndb. Qed.

      (** Same-thread, same-location writes are published in issue order (P2). *)
      Lemma issue_flush_order a b ja jb :
        before sb a b -> is_write a -> is_write b -> b_tid a = b_tid b -> b_loc a = b_loc b ->
        fidx a ja -> fidx b jb -> ja < jb.
      Proof.
        intros Hab Ha Hb Htid Hloc Hja Hjb.
        destruct (ops_idx a) as [ia Hia]; [eapply fidx_ops; eauto |].
        destruct (ops_idx b) as [ib Hib]; [eapply fidx_ops; eauto |].
        assert (Hiab : ia < ib) by (eapply before_idx; eauto using write_not_flush).
        assert (Hbjb : ib < jb) by (eapply fidx_gt_idx; eauto).
        destruct (classic (pending jb a)) as [Hp | Hnp].
        - exfalso.
          assert (Hne : a <> b).
          { intros ->. eapply before_irrefl_u; [| exact Hab]. eapply unique_sh; eauto. apply write_not_flush; auto. }
          destruct Hjb as [_ Hhead]. apply head_at_iff in Hhead; [| exact Hndb].
          destruct Hhead as [_ Hmin].
          assert (Hba : before sb b a) by (apply Hmin; auto).
          eapply before_asym_u; [| | exact Hab | exact Hba]; eapply unique_sh; eauto; apply write_not_flush; auto.
        - rewrite (pending_iff_fidx a ia ja jb Hia Hja) in Hnp. lia.
      Qed.

      (** *** The witness *)

      Definition mo_ex : relation block :=
        fun a b =>
          In a (ops X) /\ In b (ops X) /\ is_write a /\ is_write b /\ b_loc a = b_loc b /\
          exists ja jb, fidx a ja /\ fidx b jb /\ ja < jb.

      (** [RdF]: [r] reads the youngest pending write of its thread. *)
      Definition rf_fwd (u r : block) : Prop :=
        exists i, idx r i /\ last_at i u /\ b_tid u = b_tid r.

      (** [RdM]: [r] reads the write published by the last flush at its
          location before it. *)
      Definition rf_mem (u r : block) : Prop :=
        exists i j, idx r i /\ proj (b_loc r) (pend (b_tid r) (pfx i)) = [] /\
                    last_flush_before i (b_loc r) j /\ removes j u.

      Definition rf_ex : relation block :=
        fun u r =>
          In u (ops X) /\ In r (ops X) /\ is_write u /\ is_read r /\ b_loc u = b_loc r /\
          (rf_fwd u r \/ rf_mem u r).

      Definition wx : witness C := {| mo := mo_ex; rf := rf_ex |}.

      (** *** Facts about sources *)

      Lemma last_at_unique i u u' :
        last_at i u -> last_at i u' -> b_tid u = b_tid u' -> b_loc u = b_loc u' -> u = u'.
      Proof.
        unfold Pending.last_at. intros H H' Ht Hl. rewrite Ht, Hl in H. congruence.
      Qed.

      Lemma last_at_tid_loc i u r :
        last_at i u -> b_tid u = b_tid r /\ b_loc u = b_loc r ->
        forall u', last_at i u' -> b_tid u' = b_tid r -> b_loc u' = b_loc r -> u = u'.
      Proof.
        intros H [Ht Hl] u' H' Ht' Hl'. eapply last_at_unique; eauto; congruence.
      Qed.

      Lemma last_flush_before_unique i x j j' :
        last_flush_before i x j -> last_flush_before i x j' -> j = j'.
      Proof.
        intros ([t Hf] & Hj & Hno) ([t' Hf'] & Hj' & Hno').
        destruct (lt_eq_lt_dec j j') as [[Hlt | Heq] | Hgt]; auto; exfalso.
        - apply (Hno j' t'); auto.
        - apply (Hno' j t); auto.
      Qed.

      Lemma last_flush_exists i x :
        (exists j t, j < i /\ flush_at j t x) -> exists j, last_flush_before i x j.
      Proof.
        induction i as [| i IH]; intros (j & t & Hj & Hf); [lia |].
        destruct (classic (exists t', flush_at i t' x)) as [[t' Hf'] | Hnf].
        - exists i. split; [eauto |]. split; [lia |]. intros j' t'' Hj'. lia.
        - assert (Hji : j < i).
          { destruct (lt_eq_lt_dec j i) as [[H | H] | H]; auto; [| lia].
            subst j. exfalso. apply Hnf. exists t. exact Hf. }
          destruct IH as [j' (Hf'' & Hj' & Hno)]; [exists j, t; auto |].
          exists j'. split; auto. split; [lia |]. intros j'' t'' Hj'' Hf3.
          destruct (lt_dec j'' i) as [Hlt | Hge]; [eapply Hno; eauto; lia |].
          assert (j'' = i) by lia. subst j''. apply Hnf. exists t''. exact Hf3.
      Qed.

      Lemma flush_le_last j x i j' :
        last_flush_before i x j -> (exists t, flush_at j' t x) -> j' < i -> j' <= j.
      Proof.
        intros (_ & _ & Hno) [t Hf] Hj'. destruct (le_lt_dec j' j); auto.
        exfalso. eapply Hno; eauto.
      Qed.

      Lemma rf_mem_facts u r :
        rf_mem u r ->
        exists i j, idx r i /\ fidx u j /\ j < i /\ last_flush_before i (b_loc r) j /\
                    proj (b_loc r) (pend (b_tid r) (pfx i)) = [].
      Proof.
        intros (i & j & Hi & Hp & Hlf & Hr). exists i, j.
        assert (Hj : j < i) by (destruct Hlf as (_ & Hj & _); exact Hj).
        split; [exact Hi | split; [exact Hr | split; [exact Hj | split; [exact Hlf | exact Hp]]]].
      Qed.

      Lemma rf_fwd_pending u r i : is_read r -> idx r i -> rf_fwd u r -> pending i u.
      Proof.
        intros Hr Hi (i' & Hi' & Hl & _).
        assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto).
        subst i'. eapply last_at_pending. exact Hl.
      Qed.

      Lemma rf_fwd_last u r i : is_read r -> idx r i -> rf_fwd u r -> last_at i u.
      Proof.
        intros Hr Hi (i' & Hi' & Hl & _).
        assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto).
        subst i'. exact Hl.
      Qed.

      Lemma pending_proj_nonempty i u r :
        pending i u -> b_tid u = b_tid r -> b_loc u = b_loc r ->
        proj (b_loc r) (pend (b_tid r) (pfx i)) <> [].
      Proof.
        intros Hp Ht Hl Heq.
        assert (In u (proj (b_loc r) (pend (b_tid r) (pfx i)))).
        { apply In_proj. rewrite <- Ht. split; auto. }
        rewrite Heq in H. inversion H.
      Qed.

      (** What the cell says about a read block, in terms of sources. *)
      Lemma read_cases r i :
        In r (ops X) -> is_read r -> idx r i ->
        (exists u, rf_fwd u r /\ In u (ops X) /\ is_write u /\ b_loc u = b_loc r /\ b_val u = b_val r) \/
        (proj (b_loc r) (pend (b_tid r) (pfx i)) = [] /\
         b_val r = cg (state_after (b_loc r) (pfx i))).
      Proof.
        intros Hr Hrd Hi.
        destruct (read_value C sb Henb i r Hi Hrd) as [(u & Hl & Ht & Hx & Hv) | H].
        - left. exists u.
          assert (Hp : pending i u) by (eapply last_at_pending; eauto).
          split; [exists i; auto |]. split; [eapply pending_ops; eauto |].
          split; [eapply pending_write; eauto |]. auto.
        - right. exact H.
      Qed.

      Lemma no_source_no_flush r i :
        In r (ops X) -> is_read r -> idx r i -> (forall u, ~ rf_ex u r) ->
        no_flush_before i (b_loc r).
      Proof.
        intros Hr Hrd Hi Hno j t Hj Hf.
        destruct (read_cases r i Hr Hrd Hi) as [(u & Hfwd & Hu & Hw & Hx & Hv) | [Hp _]].
        - apply (Hno u). repeat split; auto.
        - destruct (last_flush_exists i (b_loc r)) as [j' Hlf]; [exists j, t; auto |].
          assert (Hf' : exists t', flush_at j' t' (b_loc r)) by (destruct Hlf as (Hf' & _ & _); exact Hf').
          destruct Hf' as [t' Hf'].
          destruct (flush_effective C sb Henb j' t' (b_loc r) Hf') as (u & Hru & Hut & Hux).
          apply (Hno u). repeat split.
          + eapply fidx_ops; eauto.
          + auto.
          + eapply fidx_write; eauto.
          + auto.
          + auto.
          + right. exists i, j'. auto.
      Qed.

      (** *** [wx] is a well-formed witness *)

      Lemma wx_wf : wf_witness X wx.
      Proof.
        constructor; cbn.
        - intros a b (Ha & Hb & Hwa & Hwb & Hl & _). auto.
        - intros a (_ & _ & _ & _ & _ & ja & ja' & Hja & Hja' & Hlt).
          assert (ja = ja') by (eapply fidx_unique; eauto). lia.
        - intros a b c (Ha & Hb & Hwa & Hwb & Hl & ja & jb & Hja & Hjb & Hlt)
                       (_ & Hc & _ & Hwc & Hl' & jb' & jc & Hjb' & Hjc & Hlt').
          assert (jb = jb') by (eapply fidx_unique; eauto). subst jb'.
          split; [auto | split; [auto | split; [auto | split; [auto | split; [congruence |]]]]].
          exists ja, jc. split; [auto | split; [auto | lia]].
        - intros a b Ha Hb Hwa Hwb Hl Hne.
          destruct (fidx_exists a Ha Hwa) as [ja Hja].
          destruct (fidx_exists b Hb Hwb) as [jb Hjb].
          destruct (lt_eq_lt_dec ja jb) as [[Hlt | Heq] | Hgt].
          + left. split; [auto | split; [auto | split; [auto | split; [auto | split; [auto |]]]]].
            exists ja, jb. auto.
          + subst jb. exfalso. apply Hne. eapply fidx_inj; eauto.
          + right. split; [auto | split; [auto | split; [auto | split; [auto | split; [auto |]]]]].
            exists jb, ja. auto.
        - intros u r (Hu & Hr & Hwu & Hrd & Hl & Hsrc).
          repeat split; auto.
          destruct (ops_idx r Hr) as [i Hi].
          destruct (read_cases r i Hr Hrd Hi) as [(u' & Hfwd' & _ & _ & Hx' & Hv') | [Hp Hv]].
          + destruct Hsrc as [Hfwd | Hmem].
            * assert (Hl1 : last_at i u) by (eapply rf_fwd_last; eauto).
              assert (Hl2 : last_at i u') by (eapply rf_fwd_last; eauto).
              destruct Hfwd as (_ & _ & _ & Ht). destruct Hfwd' as (_ & _ & _ & Ht').
              assert (u = u') by (eapply last_at_unique; eauto; congruence). subst u'. auto.
            * exfalso. apply rf_mem_facts in Hmem. destruct Hmem as (i' & j & Hi' & _ & _ & _ & Hp).
              assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto). subst i'.
              assert (Ht' : b_tid u' = b_tid r) by (destruct Hfwd' as (_ & _ & _ & Ht'); exact Ht').
              eapply pending_proj_nonempty; [eapply rf_fwd_pending; eauto | exact Ht' | exact Hx' | exact Hp].
          + destruct Hsrc as [Hfwd | Hmem].
            * exfalso. destruct Hfwd as (i' & Hi' & Hl' & Ht).
              assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto). subst i'.
              eapply pending_proj_nonempty; [eapply last_at_pending; eauto | exact Ht | exact Hl | exact Hp].
            * apply rf_mem_facts in Hmem. destruct Hmem as (i' & j & Hi' & Hj & Hji & Hlf & _).
              assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto). subst i'.
              rewrite Hv. symmetry. eapply cg_last_flush; eauto.
        - intros u u' r (Hu & Hr & Hwu & Hrd & Hl & Hsrc) (Hu' & _ & Hwu' & _ & Hl' & Hsrc').
          destruct (ops_idx r Hr) as [i Hi].
          destruct Hsrc as [Hfwd | Hmem]; destruct Hsrc' as [Hfwd' | Hmem'].
          + assert (Hl1 : last_at i u) by (eapply rf_fwd_last; eauto).
            assert (Hl2 : last_at i u') by (eapply rf_fwd_last; eauto).
            destruct Hfwd as (_ & _ & _ & Ht). destruct Hfwd' as (_ & _ & _ & Ht').
            eapply last_at_unique; eauto; congruence.
          + exfalso. apply rf_mem_facts in Hmem'. destruct Hmem' as (i' & j & Hi' & _ & _ & _ & Hp).
            assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto). subst i'.
            assert (Ht : b_tid u = b_tid r) by (destruct Hfwd as (_ & _ & _ & Ht); exact Ht).
            eapply pending_proj_nonempty; [eapply rf_fwd_pending; eauto | exact Ht | exact Hl | exact Hp].
          + exfalso. apply rf_mem_facts in Hmem. destruct Hmem as (i' & j & Hi' & _ & _ & _ & Hp).
            assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto). subst i'.
            assert (Ht' : b_tid u' = b_tid r) by (destruct Hfwd' as (_ & _ & _ & Ht'); exact Ht').
            eapply pending_proj_nonempty; [eapply rf_fwd_pending; eauto | exact Ht' | exact Hl' | exact Hp].
          + apply rf_mem_facts in Hmem. destruct Hmem as (i1 & j1 & Hi1 & Hj1 & _ & Hlf1 & _).
            apply rf_mem_facts in Hmem'. destruct Hmem' as (i2 & j2 & Hi2 & Hj2 & _ & Hlf2 & _).
            assert (i1 = i2) by (eapply idx_unique; eauto; apply read_not_flush; auto). subst i2.
            assert (j1 = j2) by (eapply last_flush_before_unique; eauto). subst j2.
            eapply fidx_inj; eauto.
        - intros r Hr Hrd Hno.
          destruct (ops_idx r Hr) as [i Hi].
          destruct (read_cases r i Hr Hrd Hi) as [(u & Hfwd & Hu & Hw & Hx & Hv) | [Hp Hv]].
          + exfalso. apply (Hno u). repeat split; auto.
          + rewrite Hv. apply cg_no_flush. eapply no_source_no_flush; eauto.
      Qed.


      (** *** Sources of a read: forwarded, from memory, or initial *)

      Lemma source_trichotomy r i :
        In r (ops X) -> is_read r -> idx r i ->
        (exists u, rf_ex u r /\ last_at i u /\ b_tid u = b_tid r /\ b_loc u = b_loc r) \/
        (exists u j, rf_ex u r /\ fidx u j /\ last_flush_before i (b_loc r) j /\
                     proj (b_loc r) (pend (b_tid r) (pfx i)) = []) \/
        ((forall u, ~ rf_ex u r) /\ no_flush_before i (b_loc r) /\
         proj (b_loc r) (pend (b_tid r) (pfx i)) = []).
      Proof.
        intros Hr Hrd Hi.
        destruct (read_cases r i Hr Hrd Hi) as [(u & Hfwd & Hu & Hw & Hx & Hv) | [Hp Hv]].
        - left. exists u.
          assert (Ht : b_tid u = b_tid r) by (destruct Hfwd as (_ & _ & _ & Ht); exact Ht).
          split; [repeat split; auto |]. split; auto. eapply rf_fwd_last; eauto.
        - destruct (classic (exists j t, j < i /\ flush_at j t (b_loc r))) as [Hex | Hnex].
          + right. left.
            destruct (last_flush_exists i (b_loc r) Hex) as [j Hlf].
            assert (Hf : exists t, flush_at j t (b_loc r)) by (destruct Hlf as (Hf & _ & _); exact Hf).
            destruct Hf as [t Hf].
            destruct (flush_effective C sb Henb j t (b_loc r) Hf) as (u & Hru & Hut & Hux).
            exists u, j. split; [| auto].
            repeat split; auto.
            * eapply fidx_ops; eauto.
            * eapply fidx_write; eauto.
            * right. exists i, j. auto.
          + right. right.
            assert (Hno : no_flush_before i (b_loc r)).
            { intros j t Hj Hf. apply Hnex. exists j, t. auto. }
            split; [| auto].
            intros u (Hu & _ & Hwu & _ & Hl & [Hfwd | Hmem]).
            * assert (Ht : b_tid u = b_tid r) by (destruct Hfwd as (_ & _ & _ & Ht); exact Ht).
              eapply pending_proj_nonempty; [eapply rf_fwd_pending; eauto | exact Ht | exact Hl | exact Hp].
            * apply rf_mem_facts in Hmem. destruct Hmem as (i' & j & Hi' & Hj & Hji & Hlf & _).
              assert (i = i') by (eapply idx_unique; eauto; apply read_not_flush; auto). subst i'.
              apply Hnex. exists j, (b_tid u).
              split; auto. destruct Hj as [Hf _]. rewrite Hl in Hf. exact Hf.
      Qed.

      Lemma rf_ex_unique u u' r : rf_ex u r -> rf_ex u' r -> u = u'.
      Proof. apply (rf_func wx_wf). Qed.

      (** *** (D1): per-location coherence *)

      (** The rank of an operation at its location: a write is ranked by
          its publication, a read by the rank of the version it observes
          ([0] for the initial value). *)
      Definition rk (b : block) (n : nat) : Prop :=
        (is_write b /\ exists j, fidx b j /\ n = S j) \/
        (is_read b /\
         ((exists u j, rf_ex u b /\ fidx u j /\ n = S j) \/
          ((forall u, ~ rf_ex u b) /\ n = 0))).

      Definition tag (b : block) : nat := if is_writeb b then 0 else 1.

      Definition key1 (b : block) (p : nat * nat * nat) : Prop :=
        (In b (ops X) /\ exists n i, rk b n /\ idx b i /\ p = (n, tag b, i)) \/
        (~ In b (ops X) /\ p = (0, 0, 0)).

      Lemma write_read_excl (b : block) : is_write b -> is_read b -> False.
      Proof. destruct b; cbn; tauto. Qed.

      Lemma ops_write_or_read b : In b (ops X) -> is_write b \/ is_read b.
      Proof.
        intros Hb. pose proof (ops_noflush HX b Hb). destruct b; cbn in *; tauto.
      Qed.

      Lemma rk_write w n : is_write w -> rk w n -> exists j, fidx w j /\ n = S j.
      Proof.
        intros Hw [[_ H] | [Hr _]]; [exact H | exfalso; eapply write_read_excl; eauto].
      Qed.

      Lemma rk_read r n :
        is_read r -> rk r n ->
        (exists u j, rf_ex u r /\ fidx u j /\ n = S j) \/ ((forall u, ~ rf_ex u r) /\ n = 0).
      Proof.
        intros Hr [[Hw _] | [_ H]]; [exfalso; eapply write_read_excl; eauto | exact H].
      Qed.

      Lemma rk_total b : In b (ops X) -> exists n, rk b n.
      Proof.
        intros Hb. destruct (ops_write_or_read b Hb) as [Hw | Hr].
        - destruct (fidx_exists b Hb Hw) as [j Hj]. exists (S j). left. split; auto. exists j. auto.
        - destruct (classic (exists u, rf_ex u b)) as [[u Hu] | Hno].
          + assert (Hu' := Hu). destruct Hu' as (Huo & _ & Hwu & _ & _ & _).
            destruct (fidx_exists u Huo Hwu) as [j Hj].
            exists (S j). right. split; auto. left. exists u, j. auto.
          + exists 0. right. split; auto. right. split; auto. intros u Hu. apply Hno. eauto.
      Qed.

      Lemma key1_total b : exists p, key1 b p.
      Proof.
        destruct (classic (In b (ops X))) as [Hb | Hb].
        - destruct (rk_total b Hb) as [n Hn]. destruct (ops_idx b Hb) as [i Hi].
          exists (n, tag b, i). left. split; auto. exists n, i. auto.
        - exists (0, 0, 0). right. auto.
      Qed.

      Lemma tag_write w : is_write w -> tag w = 0.
      Proof. destruct w; cbn; tauto. Qed.
      Lemma tag_read r : is_read r -> tag r = 1.
      Proof. destruct r; cbn; tauto. Qed.

      (** Ranks of the source of a read, from its rank. *)
      Lemma rk_read_src r n u j :
        is_read r -> rk r n -> rf_ex u r -> fidx u j -> n = S j.
      Proof.
        intros Hr Hn Hu Hj. apply rk_read in Hn; auto.
        destruct Hn as [(u' & j' & Hu' & Hj' & ->) | [Hno _]].
        - assert (u = u') by (eapply rf_ex_unique; eauto). subst u'.
          f_equal. eapply fidx_unique; eauto.
        - exfalso. eapply Hno. eauto.
      Qed.

      Lemma rk_read_nosrc r n : is_read r -> rk r n -> (forall u, ~ rf_ex u r) -> n = 0.
      Proof.
        intros Hr Hn Hno. apply rk_read in Hn; auto.
        destruct Hn as [(u' & j' & Hu' & _ & _) | [_ ->]]; auto. exfalso. eapply Hno. eauto.
      Qed.

      (** The four shapes of a same-location program-order edge. *)

      Lemma po_loc_WW a b na nb :
        before sb a b -> is_write a -> is_write b -> b_tid a = b_tid b -> b_loc a = b_loc b ->
        rk a na -> rk b nb -> na < nb.
      Proof.
        intros Hab Ha Hb Ht Hl Hna Hnb.
        apply rk_write in Hna; auto. apply rk_write in Hnb; auto.
        destruct Hna as (ja & Hja & ->). destruct Hnb as (jb & Hjb & ->).
        assert (ja < jb) by (eapply issue_flush_order; eauto). lia.
      Qed.

      Lemma po_loc_WR a b na nb ib :
        In a (ops X) -> In b (ops X) ->
        before sb a b -> is_write a -> is_read b -> b_tid a = b_tid b -> b_loc a = b_loc b ->
        rk a na -> rk b nb -> idx b ib -> na <= nb.
      Proof.
        intros Ha Hb Hab Hwa Hrb Ht Hl Hna Hnb Hib.
        apply rk_write in Hna; auto. destruct Hna as (ja & Hja & ->).
        destruct (ops_idx a Ha) as [ia Hia].
        assert (Hiab : ia < ib) by (eapply before_idx; eauto using write_not_flush, read_not_flush).
        destruct (source_trichotomy b ib Hb Hrb Hib)
          as [(u & Hu & Hlu & Htu & Hlu2) | [(u & j & Hu & Hju & Hlf & Hp) | (Hno & Hnf & Hp)]].
        - (* forwarded *)
          assert (Hu2 := Hu). destruct Hu2 as (Huo & _ & Hwu & _ & _ & _).
          destruct (fidx_exists u Huo Hwu) as [ju Hju].
          assert (nb = S ju) by (eapply (rk_read_src b nb u ju); eauto). subst nb.
          destruct (classic (pending ib a)) as [Hp | Hnp].
          + destruct (classic (a = u)) as [-> | Hne].
            * assert (ja = ju) by (eapply fidx_unique; eauto). lia.
            * apply last_at_iff in Hlu; [| exact Hndb]. destruct Hlu as [_ Hmax].
              assert (Hau : before sb a u) by (apply Hmax; auto; congruence).
              assert (ja < ju) by (eapply issue_flush_order; eauto; congruence). lia.
          + rewrite (pending_iff_fidx a ia ja ib Hia Hja) in Hnp.
            assert (Hpu : pending ib u) by (eapply last_at_pending; eauto).
            destruct (ops_idx u Huo) as [iu Hiu].
            rewrite (pending_iff_fidx u iu ju ib Hiu Hju) in Hpu. lia.
        - (* from memory *)
          assert (nb = S j) by (eapply (rk_read_src b nb u j); eauto). subst nb.
          assert (Hnp : ~ pending ib a).
          { intros Hp2. eapply pending_proj_nonempty; [exact Hp2 | exact Ht | exact Hl | exact Hp]. }
          rewrite (pending_iff_fidx a ia ja ib Hia Hja) in Hnp.
          assert (Hja_lt : ja < ib) by lia.
          assert (Hle : ja <= j).
          { eapply flush_le_last; eauto. exists (b_tid a). rewrite <- Hl. eapply fidx_flush; eauto. }
          lia.
        - (* initial: impossible, [a] has been published before [b] *)
          exfalso.
          assert (Hnp : ~ pending ib a).
          { intros Hp2. eapply pending_proj_nonempty; [exact Hp2 | exact Ht | exact Hl | exact Hp]. }
          rewrite (pending_iff_fidx a ia ja ib Hia Hja) in Hnp.
          apply (Hnf ja (b_tid a)); [lia |]. rewrite <- Hl. eapply fidx_flush; eauto.
      Qed.

      Lemma po_loc_WR_eq a b na nb :
        is_write a -> is_read b -> rk a na -> rk b nb -> na = nb -> rf_ex a b.
      Proof.
        intros Hwa Hrb Hna Hnb Heq.
        apply rk_write in Hna; auto. destruct Hna as (ja & Hja & ->).
        apply rk_read in Hnb; auto.
        destruct Hnb as [(u & j & Hu & Hj & ->) | [_ Heq0]]; [| lia].
        assert (ja = j) by lia. subst j.
        assert (a = u) by (eapply fidx_inj; eauto). subst u. exact Hu.
      Qed.

      Lemma po_loc_RW a b na nb ia ib :
        In a (ops X) -> In b (ops X) ->
        is_read a -> is_write b -> b_tid a = b_tid b -> b_loc a = b_loc b ->
        rk a na -> rk b nb -> idx a ia -> idx b ib -> ia < ib -> na < nb.
      Proof.
        intros Ha Hb Hra Hwb Ht Hl Hna Hnb Hia Hib Hiab.
        apply rk_write in Hnb; auto. destruct Hnb as (jb & Hjb & ->).
        assert (Hbjb : ib < jb) by (eapply fidx_gt_idx; eauto).
        destruct (source_trichotomy a ia Ha Hra Hia)
          as [(u & Hu & Hlu & Htu & Hlu2) | [(u & j & Hu & Hju & Hlf & Hp) | (Hno & Hnf & Hp)]].
        - assert (Hu2 := Hu). destruct Hu2 as (Huo & _ & Hwu & _ & _ & _).
          destruct (fidx_exists u Huo Hwu) as [ju Hju].
          assert (na = S ju) by (eapply (rk_read_src a na u ju); eauto). subst na.
          assert (Hpu : pending ia u) by (eapply last_at_pending; eauto).
          destruct (ops_idx u Huo) as [iu Hiu].
          rewrite (pending_iff_fidx u iu ju ia Hiu Hju) in Hpu.
          assert (Hub : before sb u b) by (eapply idx_before; eauto; lia).
          assert (ju < jb) by (eapply issue_flush_order; eauto; congruence). lia.
        - assert (na = S j) by (eapply (rk_read_src a na u j); eauto). subst na.
          destruct Hlf as (_ & Hj & _). lia.
        - assert (na = 0) by (eapply (rk_read_nosrc a na); eauto). subst na. lia.
      Qed.

      Lemma po_loc_RR a b na nb ia ib :
        In a (ops X) -> In b (ops X) ->
        is_read a -> is_read b -> b_tid a = b_tid b -> b_loc a = b_loc b ->
        rk a na -> rk b nb -> idx a ia -> idx b ib -> ia < ib -> na <= nb.
      Proof.
        intros Ha Hb Hra Hrb Ht Hl Hna Hnb Hia Hib Hiab.
        destruct (source_trichotomy a ia Ha Hra Hia)
          as [(u & Hu & Hlu & Htu & Hlu2) | [(u & j & Hu & Hju & Hlf & Hp) | (Hno & Hnf & Hp)]].
        - (* [a] forwarded from [u] *)
          assert (Hu2 := Hu). destruct Hu2 as (Huo & _ & Hwu & _ & _ & _).
          destruct (fidx_exists u Huo Hwu) as [ju Hju].
          assert (na = S ju) by (eapply (rk_read_src a na u ju); eauto). subst na.
          assert (Hpu : pending ia u) by (eapply last_at_pending; eauto).
          destruct (ops_idx u Huo) as [iu Hiu].
          assert (Hiu2 := Hpu). rewrite (pending_iff_fidx u iu ju ia Hiu Hju) in Hiu2.
          destruct (source_trichotomy b ib Hb Hrb Hib)
            as [(v & Hv & Hlv & Htv & Hlv2) | [(v & jv & Hv & Hjv & Hlf' & Hp') | (Hno' & Hnf' & Hp')]].
          + assert (Hv2 := Hv). destruct Hv2 as (Hvo & _ & Hwv & _ & _ & _).
            destruct (fidx_exists v Hvo Hwv) as [jv Hjv].
            assert (nb = S jv) by (eapply (rk_read_src b nb v jv); eauto). subst nb.
            destruct (classic (pending ib u)) as [Hpb | Hnpb].
            * destruct (classic (u = v)) as [-> | Hne].
              -- assert (ju = jv) by (eapply fidx_unique; eauto). lia.
              -- apply last_at_iff in Hlv; [| exact Hndb]. destruct Hlv as [_ Hmax].
                 assert (Huv : before sb u v) by (apply Hmax; auto; congruence).
                 assert (ju < jv) by (eapply issue_flush_order; eauto; congruence). lia.
            * rewrite (pending_iff_fidx u iu ju ib Hiu Hju) in Hnpb.
              assert (Hpv : pending ib v) by (eapply last_at_pending; eauto).
              destruct (ops_idx v Hvo) as [iv Hiv].
              rewrite (pending_iff_fidx v iv jv ib Hiv Hjv) in Hpv. lia.
          + assert (nb = S jv) by (eapply (rk_read_src b nb v jv); eauto). subst nb.
            assert (Hnpb : ~ pending ib u).
            { intros Hpb. eapply (pending_proj_nonempty ib u b); [exact Hpb | congruence | congruence | exact Hp']. }
            rewrite (pending_iff_fidx u iu ju ib Hiu Hju) in Hnpb.
            assert (Hle : ju <= jv).
            { eapply flush_le_last; eauto; [| lia]. exists (b_tid u). rewrite <- Hl, <- Hlu2. eapply fidx_flush; eauto. }
            lia.
          + exfalso.
            assert (Hnpb : ~ pending ib u).
            { intros Hpb. eapply (pending_proj_nonempty ib u b); [exact Hpb | congruence | congruence | exact Hp']. }
            rewrite (pending_iff_fidx u iu ju ib Hiu Hju) in Hnpb.
            apply (Hnf' ju (b_tid u)); [lia |]. rewrite <- Hl, <- Hlu2. eapply fidx_flush; eauto.
        - (* [a] from memory, source [u] published at [j] *)
          assert (na = S j) by (eapply (rk_read_src a na u j); eauto). subst na.
          assert (Hj : j < ia) by (destruct Hlf as (_ & Hj & _); exact Hj).
          assert (Hfj : exists t, flush_at j t (b_loc b)) by (destruct Hlf as (Hf & _ & _); rewrite <- Hl; exact Hf).
          destruct (source_trichotomy b ib Hb Hrb Hib)
            as [(v & Hv & Hlv & Htv & Hlv2) | [(v & jv & Hv & Hjv & Hlf' & Hp') | (Hno' & Hnf' & Hp')]].
          + assert (Hv2 := Hv). destruct Hv2 as (Hvo & _ & Hwv & _ & _ & _).
            destruct (fidx_exists v Hvo Hwv) as [jv Hjv].
            assert (nb = S jv) by (eapply (rk_read_src b nb v jv); eauto). subst nb.
            assert (Hpv : pending ib v) by (eapply last_at_pending; eauto).
            destruct (ops_idx v Hvo) as [iv Hiv].
            rewrite (pending_iff_fidx v iv jv ib Hiv Hjv) in Hpv. lia.
          + assert (nb = S jv) by (eapply (rk_read_src b nb v jv); eauto). subst nb.
            assert (Hle : j <= jv) by (eapply flush_le_last; eauto; lia). lia.
          + exfalso. destruct Hfj as [t Hfj]. apply (Hnf' j t); [lia | exact Hfj].
        - (* [a] reads the initial value *)
          assert (na = 0) by (eapply (rk_read_nosrc a na); eauto). subst na. lia.
      Qed.

      (** Every coherence edge increases [key1]. *)
      Lemma coh_edge_key a b pa pb :
        coh X wx a b -> key1 a pa -> key1 b pb -> lex3 pa pb.
      Proof.
        intros Hab Hpa Hpb.
        assert (Hin : In a (ops X) /\ In b (ops X)).
        { destruct Hab as [[[H | H] | H] | H].
          - destruct H as [H _]. apply (po_dom HX) in H. tauto.
          - cbn in H. destruct H as (Hu & Hr & _). auto.
          - cbn in H. destruct H as (Hu & Hr & _). auto.
          - destruct H as (Hr & Hu & _). auto. }
        destruct Hin as [Ha Hb].
        destruct Hpa as [(_ & na & ia & Hna & Hia & ->) | [Hna _]]; [| contradiction].
        destruct Hpb as [(_ & nb & ib & Hnb & Hib & ->) | [Hnb _]]; [| contradiction].
        destruct Hab as [[[H | H] | H] | H].
        - (* po_loc *)
          destruct H as [Hpo Hl].
          assert (Ht : b_tid a = b_tid b) by (apply (po_dom HX) in Hpo; tauto).
          assert (Hab : before sb a b) by (apply po_loc_before; auto; split; auto).
          destruct (ops_write_or_read a Ha) as [Hwa | Hra];
            destruct (ops_write_or_read b Hb) as [Hwb | Hrb].
          + assert (na < nb) by (eapply (po_loc_WW a b na nb); eauto). unfold lex3. lia.
          + assert (Hle : na <= nb) by (eapply (po_loc_WR a b na nb ib); eauto).
            destruct (le_lt_eq_dec na nb Hle) as [Hlt | Heq]; [unfold lex3; lia |].
            rewrite (tag_write a Hwa), (tag_read b Hrb). unfold lex3. lia.
          + assert (Hiab : ia < ib) by (eapply before_idx; eauto using write_not_flush, read_not_flush).
            assert (na < nb) by (eapply (po_loc_RW a b na nb ia ib); eauto). unfold lex3. lia.
          + assert (Hiab : ia < ib) by (eapply before_idx; eauto using read_not_flush).
            assert (Hle : na <= nb) by (eapply (po_loc_RR a b na nb ia ib); eauto).
            destruct (le_lt_eq_dec na nb Hle) as [Hlt | Heq]; [unfold lex3; lia |].
            subst nb. rewrite (tag_read a Hra), (tag_read b Hrb). unfold lex3. lia.
        - (* rf *)
          cbn in H. assert (H' := H). destruct H' as (Hu & Hr & Hwu & Hrd & Hl & _).
          apply rk_write in Hna; auto. destruct Hna as (ja & Hja & ->).
          assert (nb = S ja) by (eapply (rk_read_src b nb a ja); eauto). subst nb.
          rewrite (tag_write a Hwu), (tag_read b Hrd). unfold lex3. lia.
        - (* mo *)
          cbn in H. destruct H as (_ & _ & Hwa & Hwb & _ & ja & jb & Hja & Hjb & Hlt).
          apply rk_write in Hna; auto. destruct Hna as (ja' & Hja' & ->).
          apply rk_write in Hnb; auto. destruct Hnb as (jb' & Hjb' & ->).
          assert (ja = ja') by (eapply fidx_unique; eauto).
          assert (jb = jb') by (eapply fidx_unique; eauto).
          unfold lex3. lia.
        - (* rb *)
          destruct H as (_ & _ & Hra & Hwb & Hl & Hrb).
          apply rk_write in Hnb; auto. destruct Hnb as (jb & Hjb & ->).
          apply rk_read in Hna; auto.
          destruct Hna as [(u & j & Hu & Hj & ->) | [_ ->]].
          + specialize (Hrb u Hu). cbn in Hrb.
            destruct Hrb as (_ & _ & _ & _ & _ & ju & jb' & Hju & Hjb' & Hlt).
            assert (j = ju) by (eapply fidx_unique; eauto).
            assert (jb = jb') by (eapply fidx_unique; eauto).
            unfold lex3. lia.
          + unfold lex3. lia.
      Qed.

      Lemma wx_D1 : D1 X wx.
      Proof.
        unfold D1. eapply acyclic_by_rel_lex3 with (val := key1).
        - apply key1_total.
        - apply coh_edge_key.
      Qed.

      (** *** (D2): the global axiom *)

      (** Position of an operation on the completed trace: a write at its
          publication, a read at its block. *)
      Definition pos2 (b : block) (n : nat) : Prop :=
        (In b (ops X) /\ ((is_write b /\ fidx b n) \/ (is_read b /\ idx b n))) \/
        (~ In b (ops X) /\ n = 0).

      Lemma pos2_total b : exists n, pos2 b n.
      Proof.
        destruct (classic (In b (ops X))) as [Hb | Hb].
        - destruct (ops_write_or_read b Hb) as [Hw | Hr].
          + destruct (fidx_exists b Hb Hw) as [j Hj]. exists j. left. auto.
          + destruct (ops_idx b Hb) as [i Hi]. exists i. left. auto.
        - exists 0. right. auto.
      Qed.

      Lemma pos2_write w n : In w (ops X) -> is_write w -> pos2 w n -> fidx w n.
      Proof.
        intros Hin Hw [[_ [[_ H] | [Hr _]]] | [Hnin _]];
          [auto | exfalso; eapply write_read_excl; eauto | contradiction].
      Qed.

      Lemma pos2_read r n : In r (ops X) -> is_read r -> pos2 r n -> idx r n.
      Proof.
        intros Hin Hr [[_ [[Hw _] | [_ H]]] | [Hnin _]];
          [exfalso; eapply write_read_excl; eauto | auto | contradiction].
      Qed.

      (** A block's position is at least its index. *)
      Lemma pos2_ge_idx b n i : In b (ops X) -> pos2 b n -> idx b i -> i <= n.
      Proof.
        intros Hb Hp Hi. destruct (ops_write_or_read b Hb) as [Hw | Hr].
        - apply pos2_write in Hp; auto. assert (i < n) by (eapply fidx_gt_idx; eauto). lia.
        - apply pos2_read in Hp; auto. assert (i = n) by (eapply idx_unique; eauto; apply read_not_flush; auto). lia.
      Qed.

      Lemma pre_dom a b : pre a b -> In a (ops X) /\ In b (ops X).
      Proof. destruct Hadm as (_ & _ & H). apply H. Qed.

      Lemma tc_pre_dom a b : (pre⁺) a b -> In a (ops X) /\ In b (ops X).
      Proof.
        intros H. induction H as [a b H | a b c H1 IH1 H2 IH2].
        - apply pre_dom. exact H.
        - tauto.
      Qed.

      Lemma pre0_pre a b : pre0 X I a b -> pre a b.
      Proof. destruct Hadm as (H & _ & _). apply H. Qed.

      (** The contract, applied at the publication of [b]. *)
      Lemma contract_at_flush a b jb :
        fidx b jb -> pending jb a -> b_tid a = b_tid b -> b_handle a < b_handle b ->
        I (b_inv a) (b_inv b).
      Proof.
        intros Hjb Hpa Ht Hh.
        destruct HVb as [Hc _].
        destruct Hjb as [[h Hf] Hhead].
        apply (Hc (pfx jb) (b_tid b) h (b_loc b) (skipn (S jb) sb) b).
        - apply nth_error_split. exact Hf.
        - exact Hhead.
        - unfold Pending.pending in Hpa. rewrite Ht in Hpa. exact Hpa.
        - exact Hh.
      Qed.

      Lemma Dc_edge_pos a b na nb :
        Dc X I wx pre a b -> pos2 a na -> pos2 b nb -> na < nb.
      Proof.
        intros Hab Hpa Hpb.
        destruct Hab as [[[H | H] | H] | H].
        - (* ppo *)
          destruct H as [[Hra Hpre] | [Hpre0 [Hwa Hwb]]].
          + (* [rd];pre⁺ *)
            assert (Hin : In a (ops X) /\ In b (ops X)) by (apply tc_pre_dom; auto).
            destruct Hin as [Ha Hb].
            assert (Hab : before sb a b) by (apply tc_pre_before; auto).
            apply pos2_read in Hpa; auto.
            destruct (ops_idx b Hb) as [ib Hib].
            assert (na < ib).
            { eapply before_idx; eauto; [apply read_not_flush; auto |]. apply (ops_noflush HX b Hb). }
            assert (ib <= nb) by (eapply pos2_ge_idx; eauto). lia.
          + (* (po \ I) ∩ (W × W) *)
            assert (Hpo : po X a b) by (destruct Hpre0; auto).
            assert (HnI : ~ I_blk I a b) by (destruct Hpre0; auto).
            assert (Hin := po_dom HX _ _ Hpo). destruct Hin as (Ha & Hb & Ht).
            assert (Hab : before sb a b) by (apply respects_sh; auto; apply pre0_pre; auto).
            assert (Hh : b_handle a < b_handle b) by (apply (po_handles HX); auto).
            apply pos2_write in Hpa; auto. apply pos2_write in Hpb; auto.
            destruct (ops_idx a Ha) as [ia Hia]. destruct (ops_idx b Hb) as [ib Hib].
            assert (Hiab : ia < ib) by (eapply before_idx; eauto using write_not_flush).
            assert (Hibjb : ib < nb) by (eapply fidx_gt_idx; eauto).
            destruct (classic (pending nb a)) as [Hp | Hnp].
            * exfalso. apply HnI. unfold I_blk. eapply contract_at_flush; eauto.
            * rewrite (pending_iff_fidx a ia na nb Hia Hpa) in Hnp. lia.
        - (* rfe *)
          destruct H as [Hrf Htid]. cbn in Hrf.
          assert (Hrf' := Hrf). destruct Hrf' as (Hu & Hr & Hwu & Hrd & Hl & [Hfwd | Hmem]).
          + exfalso. destruct Hfwd as (_ & _ & _ & Ht). congruence.
          + apply pos2_write in Hpa; auto. apply pos2_read in Hpb; auto.
            apply rf_mem_facts in Hmem. destruct Hmem as (i & j & Hi & Hj & Hji & _ & _).
            assert (i = nb) by (eapply idx_unique; eauto; apply read_not_flush; auto).
            assert (j = na) by (eapply fidx_unique; eauto). lia.
        - (* mo *)
          cbn in H. destruct H as (Ha & Hb & Hwa & Hwb & _ & ja & jb & Hja & Hjb & Hlt).
          apply pos2_write in Hpa; auto. apply pos2_write in Hpb; auto.
          assert (ja = na) by (eapply fidx_unique; eauto).
          assert (jb = nb) by (eapply fidx_unique; eauto). lia.
        - (* rb *)
          destruct H as (Hr & Hu & Hrd & Hwu & Hl & Hrb).
          apply pos2_read in Hpa; auto. apply pos2_write in Hpb; auto.
          assert (Hne : na <> nb).
          { intros Heq. subst nb. destruct Hpb as [[h Hf] _]. unfold idx, Pending.at_idx in *.
            rewrite Hf in Hpa. inversion Hpa; subst. destruct Hrd. }
          destruct (source_trichotomy a na Hr Hrd Hpa)
            as [(u0 & Hu0 & Hlu & Htu & Hlu2) | [(u0 & j & Hu0 & Hju & Hlf & Hp) | (Hno & Hnf & Hp)]].
          + specialize (Hrb u0 Hu0). cbn in Hrb.
            destruct Hrb as (_ & _ & _ & _ & _ & j0 & jb & Hj0 & Hjb & Hlt).
            assert (jb = nb) by (eapply fidx_unique; eauto). subst jb.
            assert (Hu0o : In u0 (ops X)) by (destruct Hu0; auto).
            destruct (ops_idx u0 Hu0o) as [i0 Hi0].
            assert (Hp0 : pending na u0) by (eapply last_at_pending; eauto).
            rewrite (pending_iff_fidx u0 i0 j0 na Hi0 Hj0) in Hp0. lia.
          + specialize (Hrb u0 Hu0). cbn in Hrb.
            destruct Hrb as (_ & _ & _ & _ & _ & j0 & jb & Hj0 & Hjb & Hlt).
            assert (jb = nb) by (eapply fidx_unique; eauto). subst jb.
            assert (j0 = j) by (eapply fidx_unique; eauto). subst j0.
            destruct (le_lt_dec nb na) as [Hle | Hgt]; [| exact Hgt].
            exfalso. assert (nb < na) by lia.
            assert (Hle' : nb <= j).
            { eapply flush_le_last; eauto. exists (b_tid b). rewrite Hl. eapply fidx_flush; eauto. }
            lia.
          + destruct (le_lt_dec nb na) as [Hle | Hgt]; [| exact Hgt].
            exfalso. assert (nb < na) by lia.
            apply (Hnf nb (b_tid b)); [lia |]. rewrite Hl. eapply fidx_flush; eauto.
      Qed.

      Lemma wx_D2 : D2 X I wx pre.
      Proof.
        unfold D2. eapply acyclic_by_rel_nat with (val := pos2).
        - apply pos2_total.
        - apply Dc_edge_pos.
      Qed.

      Lemma wx_consistent : consistent X I wx pre.
      Proof. split; [apply wx_D1 | apply wx_D2]. Qed.

    End Witness.


    (** Lemma mem:lem:extract. *)
    Theorem extraction :
      nu I s -> exists w, wf_witness X w /\ consistent X I w pre.
    Proof.
      intros (sh & HV & Hhide).
      destruct (completion sh HV Hhide) as (sb & HVb & Hhideb & Hhob & Hrespb & Hcomplete).
      exists (wx sb). split.
      - apply wx_wf; auto.
      - apply wx_consistent; auto.
    Qed.

  End Extraction.

End Extraction.
