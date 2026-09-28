(** * Realization (Lemma mem:lem:realize)

    From an OMCA-consistent witness for a candidate [X] with respect to an
    admissible [pre], build a trace [ŝ ∈ V_E[Locs]] whose hiding presents
    [X] and respects [pre].

    The construction follows the paper: a clock (a linear extension of
    [Dc_pre]) decides how same-thread reads are served; the scheduling
    graph [𝔄] on reads, issue nodes and flush nodes carries the six kinds
    of requirements (E1)--(E6); Claim 1 shows it acyclic with an explicit
    potential (Section "Claim 1"); a topological order of [𝔄] is the trace,
    and Claim 2 checks it block by block against the buffered cell. *)

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

Module Realization.

  Import Cell Decl Pending.

  Section Realization.
    Context (C : Cfg).

    Notation block := (block C).
    Notation trace := (trace C).

    Variable I : cell_op C -> cell_op C -> Prop.
    Hypothesis HI : forall m m', I m m' -> op_loc m <> op_loc m'.

    Variable X : cand C.
    Hypothesis HX : wf_cand X.

    Variable pre : relation block.
    Hypothesis Hadm : admissible X I pre.

    Variable w : witness C.
    Hypothesis Hw : wf_witness X w.
    Hypothesis HD1 : D1 X w.
    Hypothesis HD2 : D2 X I w pre.

    Notation ops := (ops X).

    (** ** Generalities *)

    Lemma write_read_excl (b : block) : is_write b -> is_read b -> False.
    Proof. destruct b; cbn; tauto. Qed.

    Lemma write_not_flush (b : block) : is_write b -> ~ is_flush b.
    Proof. destruct b; cbn; tauto. Qed.

    Lemma read_not_flush (b : block) : is_read b -> ~ is_flush b.
    Proof. destruct b; cbn; tauto. Qed.

    Lemma ops_write_or_read b : In b ops -> is_write b \/ is_read b.
    Proof.
      intros Hb. pose proof (ops_noflush HX b Hb). destruct b; cbn in *; tauto.
    Qed.

    Lemma pre_dom a b : pre a b -> In a ops /\ In b ops.
    Proof. destruct Hadm as (_ & _ & H). apply H. Qed.

    Lemma pre_acyclic : acyclic pre.
    Proof. destruct Hadm as (_ & H & _). exact H. Qed.

    Lemma pre0_pre a b : pre0 X I a b -> pre a b.
    Proof. destruct Hadm as (H & _ & _). apply H. Qed.

    Lemma po_loc_pre a b : po_loc X a b -> pre a b.
    Proof. intros H. apply pre0_pre. apply pre0_same_loc_po; auto. Qed.

    Lemma tc_pre_dom a b : (pre⁺) a b -> In a ops /\ In b ops.
    Proof.
      intros H. induction H as [a b H | a b c H1 IH1 H2 IH2]; [apply pre_dom; auto | tauto].
    Qed.

    Lemma Dc_dom a b : Dc X I w pre a b -> In a ops /\ In b ops.
    Proof.
      intros [[[H | H] | H] | H].
      - destruct H as [[_ H] | [[H _] _]]; [apply tc_pre_dom; auto |].
        apply (po_dom HX) in H. tauto.
      - destruct H as [H _]. apply (rf_dom Hw) in H. tauto.
      - apply (mo_dom Hw) in H. tauto.
      - destruct H as (H1 & H2 & _). auto.
    Qed.

    (** Consequences (C1)--(C3) of (D1). *)

    Lemma C1_po_loc_mo a b :
      po_loc X a b -> is_write a -> is_write b -> mo w a b.
    Proof.
      intros Hpo Ha Hb.
      assert (Hin := po_dom HX _ _ (proj1 Hpo)). destruct Hin as (Hina & Hinb & _).
      assert (Hne : a <> b) by (intros ->; eapply (po_irrefl HX); apply Hpo).
      destruct (mo_total Hw Hina Hinb Ha Hb (proj2 Hpo) Hne) as [H | H]; auto.
      exfalso. apply (HD1 a). eapply t_trans; apply t_step.
      - left. left. left. exact Hpo.
      - left. right. exact H.
    Qed.

    (** A read never sees a version older than an earlier write of its own
        thread: if [w0] is [po_loc]-before [r] then [w0] is the source of
        [r] or [mo]-before it. *)
    Lemma C2_po_loc_read w0 r :
      po_loc X w0 r -> is_write w0 -> is_read r ->
      (rf w w0 r \/ forall u, rf w u r -> mo w w0 u).
    Proof.
      intros Hpo Hw0 Hr.
      destruct (classic (rf w w0 r)) as [H | H]; [left; auto | right].
      intros u Hu.
      assert (Hin := po_dom HX _ _ (proj1 Hpo)). destruct Hin as (Hin0 & Hinr & _).
      assert (Hu' := rf_dom Hw _ _ Hu). destruct Hu' as (Hinu & _ & Hwu & _ & Hlu & _).
      assert (Hne : w0 <> u) by (intros ->; contradiction).
      destruct (mo_total Hw Hin0 Hinu Hw0 Hwu ltac:(rewrite Hlu; apply Hpo) Hne) as [Hm | Hm]; auto.
      exfalso. apply (HD1 w0). eapply t_trans; [apply t_step; left; left; left; exact Hpo |].
      apply t_step. right. repeat split; auto; [symmetry; apply Hpo |].
      intros u0 Hu0. assert (u0 = u) by (eapply (rf_func Hw); eauto). subst u0. exact Hm.
    Qed.

    (** A read with no source is [rb]-before every earlier own write. *)
    Lemma C2_po_loc_read_init w0 r :
      po_loc X w0 r -> is_write w0 -> is_read r -> (forall u, ~ rf w u r) -> False.
    Proof.
      intros Hpo Hw0 Hr Hno.
      assert (Hin := po_dom HX _ _ (proj1 Hpo)). destruct Hin as (Hin0 & Hinr & _).
      apply (HD1 w0). eapply t_trans; [apply t_step; left; left; left; exact Hpo |].
      apply t_step. right. repeat split; auto; [symmetry; apply Hpo |].
      intros u Hu. exfalso. eapply Hno. eauto.
    Qed.

    (** The source of a read, if in the same thread, precedes it in
        program order. *)
    Lemma C3_rfi_po_loc u r :
      rf w u r -> b_tid u = b_tid r -> po_loc X u r.
    Proof.
      intros Hrf Ht.
      assert (H := rf_dom Hw _ _ Hrf). destruct H as (Hinu & Hinr & Hwu & Hrd & Hl & _).
      assert (Hne : u <> r) by (intros ->; eapply write_read_excl; eauto).
      destruct (po_total HX Hinu Hinr Ht Hne) as [Hpo | Hpo]; [split; auto |].
      exfalso. apply (HD1 r). eapply t_trans with (y := u); apply t_step.
      - left. left. left. exact (conj Hpo (eq_sym Hl)).
      - left. left. right. exact Hrf.
    Qed.

    (** ** The clock *)

    Lemma Dc_restr_acyclic : acyclic (restr (Dc X I w pre) ops).
    Proof.
      eapply acyclic_incl; [| exact HD2]. intros a b (_ & _ & H). exact H.
    Qed.

    Definition clock_spec (clk : list block) : Prop :=
      Permutation ops clk /\ forall a b, Dc X I w pre a b -> before clk a b.

    Lemma clock_exists : exists clk, clock_spec clk.
    Proof.
      destruct (@linear_extension _ (Dc X I w pre) ops (ops_nodup HX) Dc_restr_acyclic)
        as (clk & Hperm & Hbefore).
      exists clk. split; auto. intros a b Hab. apply Hbefore.
      destruct (Dc_dom a b Hab). repeat split; auto.
    Qed.

    Section WithClock.
      Variable clk : list block.
      Hypothesis Hclk : clock_spec clk.

      Lemma clk_NoDup : NoDup clk.
      Proof. eapply Permutation_NoDup; [apply Hclk | apply (ops_nodup HX)]. Qed.

      Lemma In_clk b : In b clk <-> In b ops.
      Proof.
        split; intros H.
        - eapply Permutation_in; [symmetry; apply Hclk | exact H].
        - eapply Permutation_in; [apply Hclk | exact H].
      Qed.

      Definition time (b : block) (i : nat) : Prop := nth_error clk i = Some b.

      Lemma time_total b : In b ops -> exists i, time b i.
      Proof. intros H. apply In_clk in H. apply In_nth_error in H. exact H. Qed.

      Lemma time_unique b i j : time b i -> time b j -> i = j.
      Proof. intros. eapply NoDup_unique_occ; eauto. apply clk_NoDup. Qed.

      Lemma time_inj a b i : time a i -> time b i -> a = b.
      Proof. unfold time. intros H1 H2. rewrite H1 in H2. inversion H2. reflexivity. Qed.

      Lemma Dc_time a b i j : Dc X I w pre a b -> time a i -> time b j -> i < j.
      Proof.
        intros Hab Hi Hj. destruct Hclk as [_ Hb]. specialize (Hb a b Hab).
        destruct Hb as (i' & j' & Hij & Hi' & Hj').
        assert (i = i') by (eapply time_unique; eauto).
        assert (j = j') by (eapply time_unique; eauto). lia.
      Qed.

      Lemma before_clk_total a b :
        In a ops -> In b ops -> a <> b -> before clk a b \/ before clk b a.
      Proof.
        intros Ha Hb Hne. apply before_total; auto; [apply clk_NoDup | |]; apply In_clk; auto.
      Qed.

      (** A same-thread read is forwarded iff the clock places it before
          its source. *)
      Definition forwarded (r : block) : Prop :=
        exists u, rf w u r /\ b_tid u = b_tid r /\ before clk r u.

      (** ** The scheduling graph 𝔄 *)

      Inductive node : Type :=
      | NR (r : block)
      | NI (w0 : block)
      | NF (w0 : block).

      (** [a•]: the read node of a read, the issue node of a write. *)
      Definition nd (b : block) : node :=
        match b with
        | BW _ _ _ _ _ => NI b
        | _ => NR b
        end.

      Definition blk (n : node) : block :=
        match n with
        | NR r => r
        | NI w0 => w0
        | NF w0 => BF (b_tid w0) 0 (b_loc w0)
        end.

      Lemma blk_nd b : blk (nd b) = b.
      Proof. destruct b; reflexivity. Qed.

      Lemma nd_write b : is_write b -> nd b = NI b.
      Proof. destruct b; cbn; tauto. Qed.

      Lemma nd_read b : is_read b -> nd b = NR b.
      Proof. destruct b; cbn; tauto. Qed.

      Inductive E : node -> node -> Prop :=
      | E1 a b : pre a b -> E (nd a) (nd b)
      | E2 w0 : In w0 ops -> is_write w0 -> E (NI w0) (NF w0)
      | E3 w0 w1 : mo w w0 w1 -> E (NF w0) (NF w1)
      | E4 w0 w1 : pre0 X I w0 w1 -> is_write w0 -> is_write w1 -> E (NF w0) (NF w1)
      | E5m u r : rf w u r -> ~ (b_tid u = b_tid r /\ before clk r u) -> E (NF u) (NR r)
      | E5f u r : rf w u r -> b_tid u = b_tid r -> before clk r u -> E (NR r) (NF u)
      | E6 r u : rb X w r u -> E (NR r) (NF u).

      Definition reads : list block := filter is_readb ops.
      Definition writes : list block := filter is_writeb ops.

      Definition nodes : list node :=
        map NR reads ++ map NI writes ++ map NF writes.

      Lemma In_reads b : In b reads <-> In b ops /\ is_read b.
      Proof. unfold reads. rewrite filter_In, is_readb_true. reflexivity. Qed.

      Lemma In_writes b : In b writes <-> In b ops /\ is_write b.
      Proof. unfold writes. rewrite filter_In, is_writeb_true. reflexivity. Qed.

      Lemma NoDup_nodes : NoDup nodes.
      Proof.
        unfold nodes.
        assert (Hr : NoDup reads) by (apply NoDup_filter, (ops_nodup HX)).
        assert (Hw' : NoDup writes) by (apply NoDup_filter, (ops_nodup HX)).
        assert (H1 : NoDup (map NR reads)) by (apply NoDup_map_on; auto; congruence).
        assert (H2 : NoDup (map NI writes)) by (apply NoDup_map_on; auto; congruence).
        assert (H3 : NoDup (map NF writes)) by (apply NoDup_map_on; auto; congruence).
        apply NoDup_app; auto.
        - apply NoDup_app; auto.
          intros n Hn Hn'. apply in_map_iff in Hn. apply in_map_iff in Hn'.
          destruct Hn as (x & <- & _). destruct Hn' as (y & Hy & _). discriminate.
        - intros n Hn Hn'. apply in_map_iff in Hn. destruct Hn as (x & <- & _).
          apply in_app_or in Hn'. destruct Hn' as [Hn' | Hn'];
            apply in_map_iff in Hn'; destruct Hn' as (y & Hy & _); discriminate.
      Qed.

      Lemma In_nodes_NR r : In (NR r) nodes <-> In r ops /\ is_read r.
      Proof.
        unfold nodes. rewrite !in_app_iff, !in_map_iff. split.
        - intros [(x & Hx & Hin) | [(x & Hx & _) | (x & Hx & _)]]; try discriminate.
          inversion Hx; subst. apply In_reads. auto.
        - intros H. left. exists r. split; auto. apply In_reads. auto.
      Qed.

      Lemma In_nodes_NI w0 : In (NI w0) nodes <-> In w0 ops /\ is_write w0.
      Proof.
        unfold nodes. rewrite !in_app_iff, !in_map_iff. split.
        - intros [(x & Hx & _) | [(x & Hx & Hin) | (x & Hx & _)]]; try discriminate.
          inversion Hx; subst. apply In_writes. auto.
        - intros H. right. left. exists w0. split; auto. apply In_writes. auto.
      Qed.

      Lemma In_nodes_NF w0 : In (NF w0) nodes <-> In w0 ops /\ is_write w0.
      Proof.
        unfold nodes. rewrite !in_app_iff, !in_map_iff. split.
        - intros [(x & Hx & _) | [(x & Hx & _) | (x & Hx & Hin)]]; try discriminate.
          inversion Hx; subst. apply In_writes. auto.
        - intros H. right. right. exists w0. split; auto. apply In_writes. auto.
      Qed.

      Lemma In_nodes_nd b : In b ops -> In (nd b) nodes.
      Proof.
        intros Hb. destruct (ops_write_or_read b Hb) as [Hw0 | Hr].
        - rewrite nd_write; auto. apply In_nodes_NI. auto.
        - rewrite nd_read; auto. apply In_nodes_NR. auto.
      Qed.

      Lemma E_dom n m : E n m -> In n nodes /\ In m nodes.
      Proof.
        intros HE. destruct HE as [a b Hp | w0 Hin Hw0 | w0 w1 Hm | w0 w1 Hp Hw0 Hw1 | u r Hr Hn | u r Hr Ht Hb | r u Hrb].
        - destruct (pre_dom _ _ Hp). split; apply In_nodes_nd; auto.
        - split; [apply In_nodes_NI | apply In_nodes_NF]; auto.
        - apply (mo_dom Hw) in Hm. destruct Hm as (Hd1 & Hd2 & Hd3 & Hd4 & _).
          split; apply In_nodes_NF; auto.
        - destruct Hp as [Hp _]. apply (po_dom HX) in Hp. destruct Hp as (Hd1 & Hd2 & _).
          split; apply In_nodes_NF; auto.
        - apply (rf_dom Hw) in Hr. destruct Hr as (Hd1 & Hd2 & Hd3 & Hd4 & _).
          split; [apply In_nodes_NF | apply In_nodes_NR]; auto.
        - apply (rf_dom Hw) in Hr. destruct Hr as (Hd1 & Hd2 & Hd3 & Hd4 & _).
          split; [apply In_nodes_NR | apply In_nodes_NF]; auto.
        - destruct Hrb as (Hd1 & Hd2 & Hd3 & Hd4 & _).
          split; [apply In_nodes_NR | apply In_nodes_NF]; auto.
      Qed.

      (** ** Claim 1: 𝔄 is acyclic *)

      (** A linear extension of [pre] on the operations, used to order issue
          nodes among themselves. *)
      Lemma pre_restr_acyclic : acyclic (restr pre ops).
      Proof.
        eapply acyclic_incl; [| exact pre_acyclic]. intros a b (_ & _ & H). exact H.
      Qed.

      Definition plist_spec (pl : list block) : Prop :=
        Permutation ops pl /\ forall a b, pre a b -> before pl a b.

      Lemma plist_exists : exists pl, plist_spec pl.
      Proof.
        destruct (@linear_extension _ pre ops (ops_nodup HX) pre_restr_acyclic)
          as (pl & Hperm & Hbefore).
        exists pl. split; auto. intros a b Hab. apply Hbefore.
        destruct (pre_dom a b Hab). repeat split; auto.
      Qed.

      Section Potential.
        Variable pl : list block.
        Hypothesis Hpl : plist_spec pl.

        Definition pidx (b : block) (p : nat) : Prop := nth_error pl p = Some b.

        Lemma pl_NoDup : NoDup pl.
        Proof. eapply Permutation_NoDup; [apply Hpl | apply (ops_nodup HX)]. Qed.

        Lemma pidx_total b : In b ops -> exists p, pidx b p.
        Proof.
          intros H. apply In_nth_error. eapply Permutation_in; [apply Hpl | exact H].
        Qed.

        Lemma pidx_unique b p q : pidx b p -> pidx b q -> p = q.
        Proof. intros. eapply NoDup_unique_occ; eauto. apply pl_NoDup. Qed.

        Lemma pre_pidx a b p q : pre a b -> pidx a p -> pidx b q -> p < q.
        Proof.
          intros Hab Hp Hq. destruct Hpl as [_ Hb]. specialize (Hb a b Hab).
          destruct Hb as (p' & q' & Hpq & Hp' & Hq').
          assert (p = p') by (eapply pidx_unique; eauto).
          assert (q = q') by (eapply pidx_unique; eauto). lia.
        Qed.

        (** [T w0]: the latest clock time (shifted by one) of a read that
            reaches [w0] by a [pre] chain; [0] if there is none. *)
        Definition T_spec (w0 : block) (T : nat) : Prop :=
          (forall r i, In r ops -> is_read r -> (pre⁺) r w0 -> time r i -> S i <= T) /\
          (T = 0 \/ exists r i, In r ops /\ is_read r /\ (pre⁺) r w0 /\ time r i /\ T = S i).

        Lemma T_exists w0 : exists T, T_spec w0 T.
        Proof.
          destruct (finite_max_rel ops (fun r => is_read r /\ (pre⁺) r w0)
                      (fun r n => exists i, time r i /\ n = S i)) as (m & Hub & Hatt).
          { intros x n n' (i & Hi & ->) (i' & Hi' & ->). f_equal. eapply time_unique; eauto. }
          exists m. split.
          - intros r i Hr Hrd Hpre Hi. apply (Hub r (S i) Hr); [auto | exists i; auto].
          - destruct Hatt as [-> | (r & n & Hr & [Hrd Hpre] & (i & Hi & ->) & ->)]; [left; auto |].
            right. exists r, i. auto.
        Qed.

        Definition val (n : node) (p : nat * nat * nat) : Prop :=
          match n with
          | NR r => exists i, time r i /\ p = (S i, 0, 0)
          | NF w0 => exists i, time w0 i /\ p = (S i, 0, 0)
          | NI w0 => exists T q, T_spec w0 T /\ pidx w0 q /\ p = (T, 1, q)
          end.

        Definition valn (n : node) (p : nat * nat * nat) : Prop :=
          (In n nodes /\ val n p) \/ (~ In n nodes /\ p = (0, 0, 0)).

        Lemma val_total n : In n nodes -> exists p, val n p.
        Proof.
          intros Hn. destruct n as [r | w0 | w0]; cbn.
          - apply In_nodes_NR in Hn. destruct Hn as [Hr _].
            destruct (time_total r Hr) as [i Hi]. exists (S i, 0, 0), i. auto.
          - apply In_nodes_NI in Hn. destruct Hn as [Hw0 _].
            destruct (T_exists w0) as [T HT]. destruct (pidx_total w0 Hw0) as [q Hq].
            exists (T, 1, q), T, q. auto.
          - apply In_nodes_NF in Hn. destruct Hn as [Hw0 _].
            destruct (time_total w0 Hw0) as [i Hi]. exists (S i, 0, 0), i. auto.
        Qed.

        Lemma valn_total n : exists p, valn n p.
        Proof.
          destruct (classic (In n nodes)) as [Hn | Hn].
          - destruct (val_total n Hn) as [p Hp]. exists p. left. auto.
          - exists (0, 0, 0). right. auto.
        Qed.

        (** Reads reaching a write by [pre] are clock-before everything the
            write is [pre]-before, and before the write's own flush. *)
        Lemma read_chain_time r w0 i j :
          In r ops -> is_read r -> (pre⁺) r w0 -> time r i -> time w0 j -> i < j.
        Proof.
          intros Hr Hrd Hpre Hi Hj. eapply Dc_time; eauto.
          left. left. left. left. split; auto.
        Qed.

        Lemma T_lt_time w0 T j :
          T_spec w0 T -> time w0 j -> T < S j.
        Proof.
          intros [_ Hatt] Hj.
          destruct Hatt as [-> | (r & i & Hr & Hrd & Hpre & Hi & ->)]; [lia |].
          assert (i < j) by (eapply read_chain_time; eauto). lia.
        Qed.

        Lemma T_lt_time_succ w0 T b j :
          T_spec w0 T -> pre w0 b -> time b j -> T < S j.
        Proof.
          intros [_ Hatt] Hpre Hj.
          destruct Hatt as [-> | (r & i & Hr & Hrd & Hpre' & Hi & ->)]; [lia |].
          assert (i < j).
          { eapply read_chain_time with (w0 := b); eauto. eapply t_trans; eauto. apply t_step. auto. }
          lia.
        Qed.

        Lemma T_mono w0 w1 T0 T1 :
          T_spec w0 T0 -> T_spec w1 T1 -> pre w0 w1 -> T0 <= T1.
        Proof.
          intros [_ Hatt] [Hub _] Hpre.
          destruct Hatt as [-> | (r & i & Hr & Hrd & Hpre' & Hi & ->)]; [lia |].
          apply (Hub r i); auto. eapply t_trans; eauto. apply t_step. auto.
        Qed.

        Lemma T_ge_read r w0 T i :
          T_spec w0 T -> In r ops -> is_read r -> pre r w0 -> time r i -> S i <= T.
        Proof.
          intros [Hub _] Hr Hrd Hpre Hi. apply (Hub r i); auto. apply t_step. auto.
        Qed.

        Lemma E_val n m p q : E n m -> val n p -> val m q -> lex3 p q.
        Proof.
          intros HE Hp Hq. destruct HE.
          - (* E1 *)
            destruct (pre_dom _ _ H) as [Ha Hb].
            destruct (ops_write_or_read a Ha) as [Hwa | Hra];
              destruct (ops_write_or_read b Hb) as [Hwb | Hrb].
            + rewrite nd_write in Hp, Hq; auto. cbn in Hp, Hq.
              destruct Hp as (Ta & qa & HTa & Hqa & ->). destruct Hq as (Tb & qb & HTb & Hqb & ->).
              assert (Ta <= Tb) by (eapply (T_mono a b Ta Tb); eauto).
              assert (qa < qb) by (eapply pre_pidx; eauto).
              unfold lex3. lia.
            + rewrite nd_write in Hp; auto. rewrite nd_read in Hq; auto. cbn in Hp, Hq.
              destruct Hp as (Ta & qa & HTa & Hqa & ->). destruct Hq as (j & Hj & ->).
              assert (Ta < S j) by (eapply (T_lt_time_succ a Ta b j); eauto). unfold lex3. lia.
            + rewrite nd_read in Hp; auto. rewrite nd_write in Hq; auto. cbn in Hp, Hq.
              destruct Hp as (i & Hi & ->). destruct Hq as (Tb & qb & HTb & Hqb & ->).
              assert (S i <= Tb) by (eapply (T_ge_read a b Tb i); eauto). unfold lex3. lia.
            + rewrite nd_read in Hp, Hq; auto. cbn in Hp, Hq.
              destruct Hp as (i & Hi & ->). destruct Hq as (j & Hj & ->).
              assert (i < j).
              { eapply Dc_time; eauto. left. left. left. left. split; auto. apply t_step. auto. }
              unfold lex3. lia.
          - (* E2 *)
            cbn in Hp, Hq. destruct Hp as (T & q' & HT & Hq' & ->). destruct Hq as (j & Hj & ->).
            assert (T < S j) by (eapply (T_lt_time w0 T j); eauto). unfold lex3. lia.
          - (* E3 *)
            cbn in Hp, Hq. destruct Hp as (i & Hi & ->). destruct Hq as (j & Hj & ->).
            assert (i < j) by (eapply Dc_time; eauto; left; right; auto). unfold lex3. lia.
          - (* E4 *)
            cbn in Hp, Hq. destruct Hp as (i & Hi & ->). destruct Hq as (j & Hj & ->).
            assert (i < j).
            { eapply Dc_time; eauto. left. left. left. right. split; auto. split; auto. }
            unfold lex3. lia.
          - (* E5m *)
            cbn in Hp, Hq. destruct Hp as (i & Hi & ->). destruct Hq as (j & Hj & ->).
            assert (i < j).
            { destruct (classic (b_tid u = b_tid r)) as [Ht | Ht].
              - assert (Hin := rf_dom Hw _ _ H). destruct Hin as (Hu & Hr & Hwu & Hrd & _).
                assert (Hne : u <> r) by (intros ->; eapply write_read_excl; eauto).
                destruct (before_clk_total u r Hu Hr Hne) as [Hb | Hb].
                + destruct Hb as (i' & j' & Hij & Hi' & Hj').
                  assert (i = i') by (eapply time_unique; eauto).
                  assert (j = j') by (eapply time_unique; eauto). lia.
                + exfalso. apply H0. auto.
              - eapply Dc_time; eauto. left. left. right. split; auto. }
            unfold lex3. lia.
          - (* E5f *)
            cbn in Hp, Hq. destruct Hp as (i & Hi & ->). destruct Hq as (j & Hj & ->).
            destruct H1 as (i' & j' & Hij & Hi' & Hj').
            assert (i = i') by (eapply time_unique; eauto).
            assert (j = j') by (eapply time_unique; eauto). unfold lex3. lia.
          - (* E6 *)
            cbn in Hp, Hq. destruct Hp as (i & Hi & ->). destruct Hq as (j & Hj & ->).
            assert (i < j) by (eapply Dc_time; eauto; right; auto). unfold lex3. lia.
        Qed.

        Lemma E_valn n m p q : E n m -> valn n p -> valn m q -> lex3 p q.
        Proof.
          intros HE Hp Hq. destruct (E_dom n m HE) as [Hn Hm].
          destruct Hp as [[_ Hp] | [Hp _]]; [| contradiction].
          destruct Hq as [[_ Hq] | [Hq _]]; [| contradiction].
          eapply E_val; eauto.
        Qed.

        Lemma E_acyclic : acyclic E.
        Proof.
          eapply acyclic_by_rel_lex3 with (val := valn).
          - apply valn_total.
          - apply E_valn.
        Qed.

      End Potential.

      Lemma E_acyclic' : acyclic E.
      Proof. destruct plist_exists as [pl Hpl]. eapply E_acyclic; eauto. Qed.

      Lemma E_restr_acyclic : acyclic (restr E nodes).
      Proof.
        eapply acyclic_incl; [| exact E_acyclic']. intros a b (_ & _ & H). exact H.
      Qed.

      (** ** The trace *)

      Definition order_spec (nl : list node) : Prop :=
        Permutation nodes nl /\ forall n m, E n m -> before nl n m.

      Lemma order_exists : exists nl, order_spec nl.
      Proof.
        destruct (@linear_extension _ E nodes NoDup_nodes E_restr_acyclic) as (nl & Hperm & Hbefore).
        exists nl. split; auto. intros n m Hnm. apply Hbefore.
        destruct (E_dom n m Hnm). repeat split; auto.
      Qed.

      (** ** Claim 2: the trace is in [V_E[Locs]] *)

      Section WithOrder.
        Variable nl : list node.
        Hypothesis Hnl : order_spec nl.

        Definition sh : trace := map blk nl.

        Definition npos (n : node) (k : nat) : Prop := nth_error nl k = Some n.

        Lemma nl_NoDup : NoDup nl.
        Proof. eapply Permutation_NoDup; [apply Hnl | apply NoDup_nodes]. Qed.

        Lemma In_nl n : In n nl <-> In n nodes.
        Proof.
          split; intros H.
          - eapply Permutation_in; [symmetry; apply Hnl | exact H].
          - eapply Permutation_in; [apply Hnl | exact H].
        Qed.

        Lemma npos_total n : In n nodes -> exists k, npos n k.
        Proof. intros H. apply In_nth_error. apply In_nl. exact H. Qed.

        Lemma npos_unique n k k' : npos n k -> npos n k' -> k = k'.
        Proof. intros. eapply NoDup_unique_occ; eauto. apply nl_NoDup. Qed.

        Lemma npos_inj n m k : npos n k -> npos m k -> n = m.
        Proof. unfold npos. intros H1 H2. rewrite H1 in H2. inversion H2. reflexivity. Qed.

        Lemma npos_In n k : npos n k -> In n nodes.
        Proof. intros H. apply In_nl. eapply nth_error_In. exact H. Qed.

        Lemma E_npos n m k k' : E n m -> npos n k -> npos m k' -> k < k'.
        Proof.
          intros HE Hk Hk'. destruct Hnl as [_ Hb]. specialize (Hb n m HE).
          destruct Hb as (i & j & Hij & Hi & Hj).
          assert (k = i) by (eapply npos_unique; eauto).
          assert (k' = j) by (eapply npos_unique; eauto). lia.
        Qed.

        (** Blocks of [sh] and nodes of [nl]. *)
        Lemma at_idx_sh k b : at_idx C sh k b <-> exists n, npos n k /\ blk n = b.
        Proof.
          unfold at_idx, sh, npos. rewrite nth_error_map.
          destruct (nth_error nl k) as [n |]; cbn.
          - split; [intros H; inversion H; eauto | intros (n' & H & <-); inversion H; auto].
          - split; [discriminate | intros (n' & H & _); discriminate].
        Qed.

        Lemma at_idx_write k w0 : is_write w0 -> (at_idx C sh k w0 <-> npos (NI w0) k).
        Proof.
          intros Hw0. rewrite at_idx_sh. split.
          - intros (n & Hn & Hb). destruct n as [r | w1 | w1]; cbn in Hb.
            + subst r. apply npos_In in Hn. apply In_nodes_NR in Hn. destruct Hn as [_ Hr].
              exfalso. eapply write_read_excl; eauto.
            + subst w1. exact Hn.
            + subst w0. destruct Hw0.
          - intros Hn. exists (NI w0). auto.
        Qed.

        Lemma at_idx_read k r : is_read r -> (at_idx C sh k r <-> npos (NR r) k).
        Proof.
          intros Hr. rewrite at_idx_sh. split.
          - intros (n & Hn & Hb). destruct n as [r' | w1 | w1]; cbn in Hb.
            + subst r'. exact Hn.
            + subst w1. apply npos_In in Hn. apply In_nodes_NI in Hn. destruct Hn as [_ Hw1].
              exfalso. eapply write_read_excl; eauto.
            + subst r. destruct Hr.
          - intros Hn. exists (NR r). auto.
        Qed.

        Lemma flush_at_sh j t x :
          flush_at C sh j t x <-> exists w0, npos (NF w0) j /\ b_tid w0 = t /\ b_loc w0 = x.
        Proof.
          unfold flush_at. split.
          - intros [h Hj]. apply at_idx_sh in Hj. destruct Hj as (n & Hn & Hb).
            destruct n as [r | w1 | w1]; cbn in Hb; try discriminate.
            + apply npos_In in Hn. apply In_nodes_NR in Hn. destruct Hn as [_ Hr].
              subst r. destruct Hr.
            + apply npos_In in Hn. apply In_nodes_NI in Hn. destruct Hn as [_ Hw1].
              subst w1. destruct Hw1.
            + inversion Hb; subst. exists w1. auto.
          - intros (w0 & Hn & <- & <-). exists 0. apply at_idx_sh. exists (NF w0). auto.
        Qed.

        (** *** [hide sh] presents [X] *)

        Lemma filter_map_comm (A B : Type) (f : B -> bool) (g : A -> B) (l : list A) :
          filter f (map g l) = map g (filter (fun a => f (g a)) l).
        Proof.
          induction l as [| a l IH]; cbn; auto. destruct (f (g a)); cbn; congruence.
        Qed.

        Definition is_NF (n : node) : bool := match n with NF _ => true | _ => false end.

        Lemma hide_sh : hide sh = map blk (filter (fun n => negb (is_NF n)) nl).
        Proof.
          unfold hide, sh. rewrite filter_map_comm.
          f_equal. apply filter_ext_in. intros n Hn.
          apply In_nl in Hn. destruct n as [r | w0 | w0]; cbn; auto.
          - apply In_nodes_NR in Hn. destruct Hn as [_ Hr]. destruct r; cbn in *; tauto.
          - apply In_nodes_NI in Hn. destruct Hn as [_ Hw0]. destruct w0; cbn in *; tauto.
        Qed.

        Lemma writes_negb_readb : writes = filter (fun b => negb (is_readb b)) ops.
        Proof.
          unfold writes. apply filter_ext_in. intros b Hb.
          pose proof (ops_noflush HX b Hb). destruct b; cbn in *; tauto.
        Qed.

        Lemma sh_presents : presents (hide sh) X.
        Proof.
          unfold presents. rewrite hide_sh.
          assert (Hp : Permutation (filter (fun n => negb (is_NF n)) nl)
                                   (map NR reads ++ map NI writes)).
          { eapply Permutation_trans.
            - apply Permutation_filter. symmetry. apply Hnl.
            - unfold nodes. rewrite !filter_app, !filter_map_comm. cbn.
              assert (H1 : filter (fun _ : block => true) reads = reads) by (apply filter_const_true).
              assert (H2 : filter (fun _ : block => true) writes = writes) by (apply filter_const_true).
              assert (H3 : filter (fun _ : block => false) writes = []) by (apply filter_const_false).
              rewrite H1, H2, H3. rewrite app_nil_r. reflexivity. }
          eapply Permutation_trans; [apply Permutation_map; exact Hp |].
          rewrite map_app, !map_map. cbn.
          rewrite !map_id.
          symmetry. rewrite writes_negb_readb. apply Permutation_filter_partition.
        Qed.

        Lemma sh_NoDup_hide : NoDup (hide sh).
        Proof. eapply Permutation_NoDup; [symmetry; apply sh_presents | apply (ops_nodup HX)]. Qed.

        Lemma sh_respects : respects sh pre.
        Proof.
          intros a b Hab. destruct Hnl as [_ Hb]. specialize (Hb _ _ (E1 a b Hab)).
          apply before_map with (f := blk) in Hb. rewrite !blk_nd in Hb. exact Hb.
        Qed.

        (** *** Publication indices *)

        Notation at_idx := (Pending.at_idx C sh).
        Notation pfx := (Pending.pfx C sh).
        Notation pending := (Pending.pending C sh).
        Notation head_at := (Pending.head_at C sh).
        Notation last_at := (Pending.last_at C sh).
        Notation flush_at := (Pending.flush_at C sh).
        Notation removes := (Pending.removes C sh).
        Notation last_flush_before := (Pending.last_flush_before C sh).
        Notation no_flush_before := (Pending.no_flush_before C sh).

        Let Hnd : NoDup (hide sh) := sh_NoDup_hide.

        Lemma issue_before_flush w0 ki kf :
          In w0 ops -> is_write w0 -> npos (NI w0) ki -> npos (NF w0) kf -> ki < kf.
        Proof. intros Hin Hw0 Hki Hkf. eapply E_npos; eauto. apply E2; auto. Qed.

        Lemma pre_npos a b ka kb : pre a b -> npos (nd a) ka -> npos (nd b) kb -> ka < kb.
        Proof. intros H. eapply E_npos. apply E1. exact H. Qed.

        (** Issue order of two same-thread, same-location writes is program
            order (consequence (ii) of (E1)). *)
        Lemma issue_order_po_loc w0 w1 ki ki' :
          In w0 ops -> In w1 ops -> is_write w0 -> is_write w1 ->
          b_tid w0 = b_tid w1 -> b_loc w0 = b_loc w1 -> w0 <> w1 ->
          npos (NI w0) ki -> npos (NI w1) ki' -> ki < ki' -> po_loc X w0 w1.
        Proof.
          intros H0 H1 Hw0 Hw1 Ht Hl Hne Hk0 Hk1 Hlt.
          destruct (po_total HX H0 H1 Ht Hne) as [Hpo | Hpo]; [split; auto |].
          exfalso. assert (ki' < ki).
          { eapply (pre_npos w1 w0); [apply po_loc_pre; split; [auto | symmetry; auto] | |];
              rewrite nd_write; auto. }
          lia.
        Qed.

        (** A write issued before a same-location read of its thread is
            program-order before it (consequence (i) of (E1)). *)
        Lemma issue_before_read_po_loc w0 r ki kr :
          In w0 ops -> In r ops -> is_write w0 -> is_read r ->
          b_tid w0 = b_tid r -> b_loc w0 = b_loc r ->
          npos (NI w0) ki -> npos (NR r) kr -> ki < kr -> po_loc X w0 r.
        Proof.
          intros H0 H1 Hw0 Hr Ht Hl Hk0 Hk1 Hlt.
          assert (Hne : w0 <> r) by (intros ->; eapply write_read_excl; eauto).
          destruct (po_total HX H0 H1 Ht Hne) as [Hpo | Hpo]; [split; auto |].
          exfalso. assert (kr < ki).
          { eapply (pre_npos r w0); [apply po_loc_pre; split; [auto | symmetry; auto] | |];
              [rewrite nd_read | rewrite nd_write]; auto. }
          lia.
        Qed.

        Lemma mo_npos w0 w1 k0 k1 : mo w w0 w1 -> npos (NF w0) k0 -> npos (NF w1) k1 -> k0 < k1.
        Proof. intros H. eapply E_npos. apply E3. exact H. Qed.

        Lemma rb_npos r u kr ku : rb X w r u -> npos (NR r) kr -> npos (NF u) ku -> kr < ku.
        Proof. intros H. eapply E_npos. apply E6. exact H. Qed.

        (** The invariant: the flush node of [w0] is exactly the flush that
            publishes [w0]. *)
        Lemma removes_iff_NF :
          forall j w0, In w0 ops -> is_write w0 -> (removes j w0 <-> npos (NF w0) j).
        Proof.
          intros j. induction j as [j IH] using lt_wf_ind.
          (* the backward direction, for any write, from the hypothesis on smaller indices *)
          assert (Hback : forall w0, In w0 ops -> is_write w0 -> npos (NF w0) j -> removes j w0).
          { intros w0 Hin Hw0 Hkf.
            destruct (npos_total (NI w0)) as [ki Hki]; [apply In_nodes_NI; auto |].
            assert (Hlt : ki < j) by (eapply issue_before_flush; eauto).
            (* [w0] is pending at [j] *)
            assert (Hpend : pending j w0).
            { apply pending_iff; auto. exists ki. split; [apply at_idx_write; auto |].
              split; auto. intros j' Hj' Hr. apply IH in Hr; auto; [| lia].
              assert (j' = j) by (eapply npos_unique; eauto). lia. }
            split.
            - apply flush_at_sh. exists w0. auto.
            - apply head_at_iff; auto. split; auto.
              intros w1 Hp1 Hl Ht Hne.
              assert (Hw1 : is_write w1) by (eapply pending_write; eauto).
              assert (Hin1 : In w1 ops).
              { apply pending_idx in Hp1. destruct Hp1 as (i1 & _ & Hi1).
                apply at_idx_write in Hi1; auto. apply npos_In in Hi1. apply In_nodes_NI in Hi1. tauto. }
              destruct (npos_total (NI w1)) as [ki1 Hki1]; [apply In_nodes_NI; auto |].
              destruct (npos_total (NF w1)) as [kf1 Hkf1]; [apply In_nodes_NF; auto |].
              (* [w1] is issued before [j] and not published before [j] *)
              apply pending_iff in Hp1; auto. destruct Hp1 as (i1 & Hi1 & Hi1j & Hno1).
              apply at_idx_write in Hi1; auto.
              assert (i1 = ki1) by (eapply npos_unique; eauto). subst i1.
              assert (Hkf1j : j < kf1).
              { destruct (lt_eq_lt_dec kf1 j) as [[Hlt1 | Heq] | Hgt]; auto.
                - exfalso. apply (Hno1 kf1); [| apply IH; auto].
                  split; auto. eapply issue_before_flush; eauto.
                - exfalso. subst kf1. apply Hne. symmetry. eapply npos_inj in Hkf; [| exact Hkf1]. congruence. }
              (* hence [w0] was issued before [w1] *)
              assert (Hkk : ki < ki1).
              { destruct (lt_eq_lt_dec ki ki1) as [[Hlt1 | Heq] | Hgt]; auto.
                - exfalso. subst ki1. apply Hne. eapply npos_inj in Hki; [| exact Hki1]. congruence.
                - exfalso.
                  assert (Hpo : po_loc X w1 w0).
                  { eapply issue_order_po_loc; eauto; congruence. }
                  assert (Hmo : mo w w1 w0) by (apply C1_po_loc_mo; auto).
                  assert (kf1 < j) by (eapply mo_npos; eauto). lia. }
              exists ki, ki1. split; auto. split; apply at_idx_write; auto. }
          split; [| apply Hback; auto].
          intros Hr. destruct Hr as [Hf Hh].
          apply flush_at_sh in Hf. destruct Hf as (w1 & Hkf1 & Ht & Hl).
          assert (Hin1 : In w1 ops /\ is_write w1) by (apply In_nodes_NF; eapply npos_In; eauto).
          destruct Hin1 as [Hin1 Hw1].
          assert (Hr1 : removes j w1) by (apply Hback; auto).
          assert (Hr0 : removes j w0).
          { split; auto. apply flush_at_sh. exists w1. auto. }
          assert (w0 = w1) by (eapply removes_head_unique; eauto).
          subst w1. exact Hkf1.
        Qed.


        Lemma pending_char k w0 ki kf :
          In w0 ops -> is_write w0 -> npos (NI w0) ki -> npos (NF w0) kf ->
          (pending k w0 <-> ki < k <= kf).
        Proof.
          intros Hin Hw0 Hki Hkf. eapply pending_interval; eauto.
          - apply at_idx_write; auto.
          - apply removes_iff_NF; auto.
        Qed.

        Lemma pending_ops k w0 : pending k w0 -> In w0 ops /\ is_write w0.
        Proof.
          intros Hp. assert (Hw0 : is_write w0) by (eapply pending_write; eauto).
          split; auto. apply pending_idx in Hp. destruct Hp as (i & _ & Hi).
          apply at_idx_write in Hi; auto. apply npos_In in Hi. apply In_nodes_NI in Hi. tauto.
        Qed.

        Lemma pending_pos k w0 :
          pending k w0 -> exists ki kf, npos (NI w0) ki /\ npos (NF w0) kf /\ ki < k <= kf.
        Proof.
          intros Hp. destruct (pending_ops k w0 Hp) as [Hin Hw0].
          destruct (npos_total (NI w0)) as [ki Hki]; [apply In_nodes_NI; auto |].
          destruct (npos_total (NF w0)) as [kf Hkf]; [apply In_nodes_NF; auto |].
          exists ki, kf. split; auto. split; auto. eapply pending_char; eauto.
        Qed.

        (** *** Enabledness of every block *)

        (** A read block is enabled if it is served by forwarding or from
            memory with the right value. *)
        Lemma read_enabled_fwd i r u :
          is_read r -> last_at i u -> b_tid u = b_tid r -> b_loc u = b_loc r -> b_val u = b_val r ->
          enabled r (state_after (b_loc r) (pfx i)).
        Proof.
          intros Hr Hl Ht Hx Hv. destruct r as [| t h x a v |]; cbn in Hr; try contradiction.
          cbn. left. rewrite bookkeeping. cbn in Ht, Hx, Hv.
          unfold Pending.last_at in Hl. rewrite Ht, Hx in Hl.
          apply hd_error_rev_iff in Hl. destruct Hl as [l' Hl]. rewrite Hl.
          rewrite map_app. cbn. rewrite last_app_single. split; [| auto].
          destruct (map b_val l'); discriminate.
        Qed.

        Lemma read_enabled_mem i r :
          is_read r -> proj (b_loc r) (pend (b_tid r) (pfx i)) = [] ->
          b_val r = cg (state_after (b_loc r) (pfx i)) ->
          enabled r (state_after (b_loc r) (pfx i)).
        Proof.
          intros Hr Hp Hv. destruct r as [| t h x a v |]; cbn in Hr; try contradiction.
          cbn in *. right. rewrite bookkeeping. rewrite Hp. auto.
        Qed.

        (** A same-location write of the reader's thread issued before the
            read is [po_loc]-before it. *)
        Lemma pending_at_read_po_loc kr r w0 :
          In r ops -> is_read r -> npos (NR r) kr -> pending kr w0 ->
          b_tid w0 = b_tid r -> b_loc w0 = b_loc r -> po_loc X w0 r.
        Proof.
          intros Hr Hrd Hkr Hp Ht Hl.
          destruct (pending_ops kr w0 Hp) as [Hin Hw0].
          destruct (pending_pos kr w0 Hp) as (ki & kf & Hki & Hkf & Hlt).
          eapply issue_before_read_po_loc; eauto. lia.
        Qed.

        (** Flushes at a location are flush nodes of writes there. *)
        Lemma flush_at_loc_node j t x :
          flush_at j t x -> exists w0, In w0 ops /\ is_write w0 /\ npos (NF w0) j /\ b_tid w0 = t /\ b_loc w0 = x.
        Proof.
          intros Hf. apply flush_at_sh in Hf. destruct Hf as (w0 & Hn & Ht & Hl).
          assert (H := npos_In _ _ Hn). apply In_nodes_NF in H. destruct H.
          exists w0. auto.
        Qed.

        Lemma read_enabled kr r :
          In r ops -> is_read r -> npos (NR r) kr ->
          enabled r (state_after (b_loc r) (pfx kr)).
        Proof.
          intros Hr Hrd Hkr.
          destruct (classic (exists u, rf w u r)) as [[u Hu] | Hno].
          - assert (Hud := rf_dom Hw _ _ Hu). destruct Hud as (Hinu & _ & Hwu & _ & Hlu & Hvu).
            destruct (npos_total (NI u)) as [kiu Hkiu]; [apply In_nodes_NI; auto |].
            destruct (npos_total (NF u)) as [kfu Hkfu]; [apply In_nodes_NF; auto |].
            destruct (classic (b_tid u = b_tid r /\ before clk r u)) as [[Ht Hb] | Hnf].
            + (* forwarded: [u] is the youngest pending write of the thread at the location *)
              apply read_enabled_fwd with (u := u); auto.
              assert (Hpo : po_loc X u r) by (apply C3_rfi_po_loc; auto).
              assert (Hki : kiu < kr).
              { eapply (pre_npos u r); [apply po_loc_pre; auto | rewrite nd_write; auto | rewrite nd_read; auto]. }
              assert (Hkf : kr < kfu) by (eapply E_npos; eauto; apply E5f; auto).
              apply last_at_iff; auto. split; [eapply pending_char; eauto; lia |].
              intros w1 Hp1 Hl1 Ht1 Hne.
              destruct (pending_ops kr w1 Hp1) as [Hin1 Hw1].
              destruct (pending_pos kr w1 Hp1) as (ki1 & kf1 & Hki1 & Hkf1 & Hlt1).
              assert (Hki_ne : ki1 <> kiu) by (intros ->; apply Hne; eapply npos_inj in Hki1; [| exact Hkiu]; congruence).
              destruct (lt_dec ki1 kiu) as [Hlt | Hge].
              * exists ki1, kiu. split; auto. split; apply at_idx_write; auto.
              * exfalso. assert (Hpo1 : po_loc X u w1).
                { eapply issue_order_po_loc; eauto; try congruence. lia. }
                assert (Hmo1 : mo w u w1) by (apply C1_po_loc_mo; auto).
                assert (Hpo2 : po_loc X w1 r).
                { eapply pending_at_read_po_loc; eauto; congruence. }
                destruct (C2_po_loc_read w1 r Hpo2 Hw1 Hrd) as [Hrf1 | Hmo2].
                -- apply Hne. eapply (rf_func Hw); eauto.
                -- specialize (Hmo2 u Hu). apply (mo_irrefl Hw u). eapply (mo_trans Hw); eauto.
            + (* from memory *)
              assert (Hkf : kfu < kr) by (eapply E_npos; eauto; apply E5m; auto).
              apply read_enabled_mem; auto.
              * (* nothing of the thread is pending at the location *)
                destruct (proj (b_loc r) (pend (b_tid r) (pfx kr))) as [| w1 l] eqn:Hp; auto.
                exfalso.
                assert (Hin1 : In w1 (proj (b_loc r) (pend (b_tid r) (pfx kr)))) by (rewrite Hp; left; auto).
                apply In_proj in Hin1. destruct Hin1 as [Hin1 Hl1].
                assert (Ht1 : b_tid w1 = b_tid r) by (apply pend_In in Hin1; tauto).
                assert (Hp1 : pending kr w1) by (unfold Pending.pending; rewrite Ht1; auto).
                destruct (pending_ops kr w1 Hp1) as [Hin1' Hw1].
                destruct (pending_pos kr w1 Hp1) as (ki1 & kf1 & Hki1 & Hkf1 & Hlt1).
                assert (Hpo2 : po_loc X w1 r) by (eapply pending_at_read_po_loc; eauto).
                destruct (C2_po_loc_read w1 r Hpo2 Hw1 Hrd) as [Hrf1 | Hmo2].
                -- assert (w1 = u) by (eapply (rf_func Hw); eauto). subst w1.
                   assert (kf1 = kfu) by (eapply npos_unique; eauto). lia.
                -- specialize (Hmo2 u Hu). assert (kf1 < kfu) by (eapply mo_npos; eauto). lia.
              * (* the global value is that of [u] *)
                symmetry. rewrite <- Hvu. rewrite <- Hlu.
                eapply cg_last_flush with (j := kfu).
                -- split; [exists (b_tid u); apply flush_at_sh; exists u; auto |].
                   split; auto. intros j' t' Hj' Hf'.
                   destruct (flush_at_loc_node j' t' (b_loc u) Hf') as (w1 & Hin1 & Hw1 & Hkf1 & Ht1 & Hl1).
                   assert (Hne : w1 <> u) by (intros ->; assert (j' = kfu) by (eapply npos_unique; eauto); lia).
                   destruct (mo_total Hw Hin1 Hinu Hw1 Hwu Hl1 Hne) as [Hmo | Hmo].
                   ++ assert (j' < kfu) by (eapply mo_npos; eauto). lia.
                   ++ assert (Hrb : rb X w r w1).
                      { split; [auto | split; [auto | split; [auto | split; [auto | split; [congruence |]]]]].
                        intros u0 Hu0.
                        assert (u0 = u) by (eapply (rf_func Hw); eauto). subst u0. exact Hmo. }
                      assert (kr < j') by (eapply rb_npos; eauto). lia.
                -- apply removes_iff_NF; auto.
          - (* initial value *)
            apply read_enabled_mem; auto.
            + destruct (proj (b_loc r) (pend (b_tid r) (pfx kr))) as [| w1 l] eqn:Hp; auto.
              exfalso.
              assert (Hin1 : In w1 (proj (b_loc r) (pend (b_tid r) (pfx kr)))) by (rewrite Hp; left; auto).
              apply In_proj in Hin1. destruct Hin1 as [Hin1 Hl1].
              assert (Ht1 : b_tid w1 = b_tid r) by (apply pend_In in Hin1; tauto).
              assert (Hp1 : pending kr w1) by (unfold Pending.pending; rewrite Ht1; auto).
              destruct (pending_ops kr w1 Hp1) as [Hin1' Hw1].
              assert (Hpo2 : po_loc X w1 r) by (eapply pending_at_read_po_loc; eauto).
              eapply (C2_po_loc_read_init w1 r); eauto.
            + rewrite (rf_init Hw r Hr Hrd); [| intros u Hu; apply Hno; eauto].
              symmetry. apply cg_no_flush. intros j t Hj Hf.
              destruct (flush_at_loc_node j t (b_loc r) Hf) as (w1 & Hin1 & Hw1 & Hkf1 & Ht1 & Hl1).
              assert (Hrb : rb X w r w1).
              { split; [auto | split; [auto | split; [auto | split; [auto | split; [congruence |]]]]].
                intros u0 Hu0. exfalso. apply Hno. eauto. }
              assert (kr < j) by (eapply rb_npos; eauto). lia.
        Qed.

        Lemma sh_enabled x : enabled_along x sh.
        Proof.
          intros i b Hi Hx. fold (pfx i).
          assert (Hi' : at_idx i b) by exact Hi.
          apply at_idx_sh in Hi'. destruct Hi' as (n & Hn & Hb).
          assert (Hnn := npos_In _ _ Hn).
          destruct n as [r | w0 | w0]; cbn in Hb; subst b.
          - apply In_nodes_NR in Hnn. destruct Hnn as [Hr Hrd]. subst x.
            apply read_enabled; auto.
          - apply In_nodes_NI in Hnn. destruct Hnn as [Hin Hw0]. destruct w0; cbn in Hw0; try contradiction.
            cbn. exact Logic.I.
          - apply In_nodes_NF in Hnn. destruct Hnn as [Hin Hw0]. cbn in Hx. subst x.
            apply flush_enabled_iff.
            destruct (npos_total (NI w0)) as [ki Hki]; [apply In_nodes_NI; auto |].
            assert (Hp : pending i w0).
            { eapply pending_char; eauto. split; [eapply issue_before_flush; eauto | lia]. }
            intros Hp'. assert (In w0 (proj (b_loc w0) (pend (b_tid w0) (pfx i)))) by (apply In_proj; auto).
            rewrite Hp' in H. inversion H.
        Qed.

        (** *** The contract *)

        Lemma sh_contract : contract I sh.
        Proof.
          intros s1 t h x s2 m Hs Hm m' Hm' Hlt.
          set (j := length s1).
          assert (Hs1 : s1 = pfx j).
          { unfold j, Pending.pfx. rewrite Hs. rewrite firstn_app. rewrite firstn_all, Nat.sub_diag. cbn.
            symmetry. apply app_nil_r. }
          assert (Hj : at_idx j (BF t h x)).
          { unfold Pending.at_idx. rewrite Hs. unfold j. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. }
          assert (Hf : flush_at j t x) by (exists h; exact Hj).
          destruct (flush_at_loc_node j t x Hf) as (w0 & Hin0 & Hw0 & Hkf & Ht & Hl).
          assert (Hr : removes j w0) by (apply removes_iff_NF; auto).
          destruct Hr as [_ Hh]. unfold Pending.head_at in Hh. rewrite Ht, Hl, <- Hs1 in Hh.
          rewrite Hh in Hm. inversion Hm; subst m. clear Hm.
          (* [m'] is a pending write of [t] with a smaller handle *)
          rewrite Hs1 in Hm'.
          assert (Ht' : b_tid m' = t) by (apply pend_In in Hm'; tauto).
          assert (Hp' : pending j m') by (unfold Pending.pending; rewrite Ht'; auto).
          destruct (pending_ops j m' Hp') as [Hin' Hw'].
          destruct (pending_pos j m' Hp') as (ki' & kf' & Hki' & Hkf' & Hlt').
          assert (Hne : m' <> w0).
          { intros ->. assert (kf' = j) by (eapply npos_unique; eauto). lia. }
          assert (Hpo : po X m' w0).
          { destruct (po_total HX Hin' Hin0 ltac:(congruence) Hne) as [Hpo | Hpo]; auto.
            exfalso. assert (b_handle w0 < b_handle m') by (apply (po_handles HX); auto). lia. }
          apply NNPP. intros HnI.
          assert (Hpre0 : pre0 X I m' w0) by (split; auto).
          assert (kf' < j) by (eapply E_npos; eauto; apply E4; auto).
          lia.
        Qed.

        Lemma sh_V : V I sh.
        Proof.
          split; [apply sh_contract |]. intros x. apply VBuf_proj_iff. apply sh_enabled.
        Qed.

        Lemma sh_nu : nu I (hide sh).
        Proof. exists sh. split; [apply sh_V | reflexivity]. Qed.

        Lemma hide_sh_respects : respects (hide sh) pre.
        Proof.
          intros a b Hab. destruct (pre_dom a b Hab) as [Ha Hb].
          apply before_filter; [apply sh_respects; auto | |].
          - pose proof (ops_noflush HX a Ha). destruct a; cbn in *; tauto.
          - pose proof (ops_noflush HX b Hb). destruct b; cbn in *; tauto.
        Qed.

      End WithOrder.

    End WithClock.


    (** Lemma mem:lem:realize. *)
    Theorem realization :
      exists s, nu I s /\ presents s X /\ respects s pre.
    Proof.
      destruct clock_exists as [clk Hclk].
      destruct (order_exists clk Hclk) as [nl Hnl].
      exists (hide (sh nl)). split; [| split].
      - eapply sh_nu; eauto.
      - eapply sh_presents; eauto.
      - eapply hide_sh_respects; eauto.
    Qed.

  End Realization.

End Realization.
