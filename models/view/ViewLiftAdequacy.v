(** * T2: runs of a ViewLift specification are relaxed linearizable

    A run of [ViewLift.VL P] is a sequence of atomic operations, each
    with the timestamp chosen at its response ([Run], [RStep]).  View
    traces are not relaxed linearizable as they stand: a retroactive
    operation may be invoked after another operation has responded and
    still be placed before it.  Relaxed linearizability instead records
    such reorderings as overlap: the response of the overtaken operation
    arrives later.

    - [run_rel_lin]: let [L] be any complete relaxed trace of the run's
      operations ([Del]) in which same-thread invocations keep the run
      order, and every response that precedes an invocation belongs to an
      operation that is smaller in (timestamp, run index) order.  Then [L]
      is relaxed linearizable ([RelaxedTraceLin.rel_lin]) for the
      sequential specification [nu_P] of [P] and the semi-independence
      relation [dep = false].  The witness lists the operations in
      (timestamp, run index) order.
    - [canon], [canon_rel_lin]: every run has such a trace.  Operations are
      invoked in run order.  A response immediately follows its
      invocation, unless a later operation is timestamped strictly before
      it; then it is delayed to the end of the trace ([canon_prompt]).
    - [canon_sync_prompt]: synchronizing operations are never delayed.
    - [vl_exec_rel_lin]: every execution of [VL P] from [vinit s0]
      determines such a run, with the execution's responses in run order.

    The proof maintains a witness incrementally ([Wit], [Wit_step]): an
    appended operation goes to the end, and a retroactive operation at
    timestamp [h] is inserted after every entry with timestamp [<= h]. *)

Require Import Stdlib.PArith.PArith.
Require Import Stdlib.Lists.List.
Require Import Stdlib.Sorting.Sorted.
Require Import Stdlib.Sorting.Permutation.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Bool.Bool.
Require Import models.EffectSignatures.
Require Import LinCCAL.
Require Import LTS.
Require Import models.simlin.AtomicLTS.
Require Import models.RelaxedSignature.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.view.ViewLift.
Import ListNotations.

Module ViewLiftAdequacy.
  Import Reg LinCCALBase ViewLift.

  Section Adequacy.
    Context {E : Op.t} (P : @Params E) (s0 : vl_state P).

    (** ** Runs with explicit timestamps *)

    Record Ent : Type := mkEnt {
      e_t : tid;
      e_m : Sig.op E;
      e_r : Sig.ar e_m;
      e_h : Time;
    }.

    Definition RStep (s : VState P) (e : Ent) (s' : VState P) : Prop :=
      Pos.lt (vs_floor P s) (e_h e) /\
      dep_ok P s (e_t e) (e_m e) (e_h e) /\
      ((vl_retro P (e_m e) = true /\
        vl_spec P (vs_tl P s (e_h e)) (e_t e) (e_m e) (e_r e) (vs_tl P s (e_h e)) /\
        s' = upd_retro P s (e_t e) (e_m e) (e_h e)) \/
       (vl_retro P (e_m e) = false /\ Pos.lt (vs_hor P s) (e_h e) /\
        exists st, vl_spec P (vs_tl P s (e_h e)) (e_t e) (e_m e) (e_r e) st /\
                   s' = upd_app P s (e_t e) (e_m e) (e_h e) st)).

    Inductive Run : list Ent -> VState P -> Prop :=
    | run_nil : Run [] (vinit P s0)
    | run_snoc R s e s' : Run R s -> RStep s e s' -> Run (R ++ [e]) s'.

    (** [RStep] is exactly a response step of [VStep] with its timestamp. *)
    Lemma rstep_vstep s e s' :
      RStep s e s' -> VStep P (LTSSpec.Build_ThreadEvent (e_t e) (LTSSpec.ResEv (e_m e) (e_r e))) s s'.
    Proof.
      intros (Hfl & Hdep & [(Hr & Hspec & ->) | (Hr & Hh & st & Hspec & ->)]).
      - eapply vstep_retro; eauto.
      - eapply vstep_app; eauto.
    Qed.

    Lemma vstep_rstep s t m r s' :
      Inv P s ->
      VStep P (LTSSpec.Build_ThreadEvent t (LTSSpec.ResEv m r)) s s' ->
      exists h, RStep s (mkEnt t m r h) s'.
    Proof.
      intros HI Hs. remember (LTSSpec.Build_ThreadEvent t (LTSSpec.ResEv m r)) as ev eqn:Hev.
      destruct Hs as [t1 m1 s1 e1 He | t1 m1 r1 h s1 s2 e1 He Hretro Hfloor Hdep Hspec Hupd
                     | t1 m1 r1 h st s1 s2 e1 He Hretro Hhor Hdep Hspec Hupd]; rewrite He in Hev.
      - discriminate.
      - pose proof (f_equal LTSSpec.te_tid Hev) as Ht. pose proof (f_equal LTSSpec.te_ev Hev) as Hr.
        simpl in Ht, Hr. subst t1.
        assert (Hm : m1 = m) by (injection Hr; auto). subst m1.
        apply LTSSpec.ResEvInversion in Hr. subst r1.
        exists h. split; [exact Hfloor|]. split; [exact Hdep|]. left. auto.
      - pose proof (f_equal LTSSpec.te_tid Hev) as Ht. pose proof (f_equal LTSSpec.te_ev Hev) as Hr.
        simpl in Ht, Hr. subst t1.
        assert (Hm : m1 = m) by (injection Hr; auto). subst m1.
        apply LTSSpec.ResEvInversion in Hr. subst r1.
        exists h. split.
        + eapply Pos.le_lt_trans; [exact (inv_floor _ _ HI) | exact Hhor].
        + split; [exact Hdep|]. right. split; [exact Hretro|]. split; [exact Hhor|]. eauto.
    Qed.

    Lemma rstep_Inv s e s' : RStep s e s' -> Inv P s -> Inv P s'.
    Proof. intros Hs HI. exact (VStep_Inv P _ _ _ (rstep_vstep _ _ _ Hs) HI). Qed.

    (** ** Relaxed signature, specification and operations *)

    Definition RS : RelaxedSig.t := {|
      RelaxedSig.effect := E;
      RelaxedSig.handle := nat;
      RelaxedSig.semi_independent := fun a b => vl_dep P a b = false;
      RelaxedSig.mode := fun _ => RelaxedSig.Fence;
    |}.

    Definition to_op (i : nat) (e : Ent) : RelaxedTraceLin.Op RS :=
      RelaxedTraceLin.Build_Op (E := RS) (e_t e, i) (e_m e) (e_r e).

    Inductive Chain : vl_state P -> list (RelaxedTraceLin.Op RS * vl_state P) -> Prop :=
    | chain_nil s : Chain s []
    | chain_cons s (o : RelaxedTraceLin.Op RS) s' W :
        vl_spec P s (fst (RelaxedTraceLin.op_key o)) (RelaxedTraceLin.op_op o) (RelaxedTraceLin.op_ret o) s' ->
        Chain s' W -> Chain s ((o, s') :: W).

    (** The sequential specification: replaying the operations from [s0]
        succeeds. *)
    Definition nu_P (W : list (RelaxedTraceLin.Op RS)) : Prop :=
      exists Ws, Chain s0 Ws /\ map fst Ws = W.

    Definition endst (s : vl_state P) (l : list (RelaxedTraceLin.Op RS * vl_state P)) : vl_state P :=
      fold_left (fun _ p => snd p) l s.

    Lemma endst_app s l1 l2 : endst s (l1 ++ l2) = endst (endst s l1) l2.
    Proof. unfold endst. apply fold_left_app. Qed.

    Lemma endst_snoc s l x : endst s (l ++ [x]) = snd x.
    Proof. rewrite endst_app. reflexivity. Qed.

    Lemma chain_app s l1 l2 : Chain s (l1 ++ l2) <-> Chain s l1 /\ Chain (endst s l1) l2.
    Proof.
      revert s. induction l1 as [|[o s1] l1 IH]; intros s; simpl.
      - split; [intros H; split; [constructor | exact H] | intros [_ H]; exact H].
      - split.
        + intros Hc. inversion Hc as [|s2 o2 s3 W2 Hsp Hc2]; subst. apply IH in Hc2 as [Hc1 Hc3].
          split; [constructor; assumption | exact Hc3].
        + intros [Hc Hc3]. inversion Hc as [|s2 o2 s4 W2 Hsp Hc2]; subst.
          constructor; [assumption|]. apply IH. split; assumption.
    Qed.


    (** ** List lemmas *)

    Lemma nth_snoc {A : Type} (l : list A) a i x :
      nth_error (l ++ [a]) i = Some x -> nth_error l i = Some x \/ (i = length l /\ x = a).
    Proof.
      intros H. destruct (Nat.lt_ge_cases i (length l)) as [Hlt | Hge].
      - left. rewrite nth_error_app1 in H by exact Hlt. exact H.
      - right. rewrite nth_error_app2 in H by exact Hge.
        destruct (i - length l) as [|k] eqn:Hk; simpl in H.
        + injection H as <-. split; [lia | reflexivity].
        + destruct k; discriminate.
    Qed.

    Lemma nth_snoc_old {A : Type} (l : list A) a i x :
      nth_error l i = Some x -> nth_error (l ++ [a]) i = Some x.
    Proof.
      intros H. rewrite nth_error_app1; [exact H|]. apply nth_error_Some. congruence.
    Qed.

    Lemma nth_snoc_new {A : Type} (l : list A) a : nth_error (l ++ [a]) (length l) = Some a.
    Proof. rewrite nth_error_app2 by lia. rewrite Nat.sub_diag. reflexivity. Qed.

    Lemma nth_lt {A : Type} (l : list A) i x : nth_error l i = Some x -> i < length l.
    Proof. intros H. apply nth_error_Some. congruence. Qed.

    Lemma StronglySorted_app {A : Type} (Rl : A -> A -> Prop) l1 l2 :
      StronglySorted Rl l1 -> StronglySorted Rl l2 ->
      (forall a b, In a l1 -> In b l2 -> Rl a b) -> StronglySorted Rl (l1 ++ l2).
    Proof.
      induction l1 as [|a l1 IH]; intros H1 H2 Hx; simpl; [exact H2|].
      apply StronglySorted_inv in H1 as [H1 HF]. constructor.
      - apply IH; auto. intros x y Hx' Hy. apply Hx; [right|]; assumption.
      - apply Forall_app. split; [exact HF|]. apply Forall_forall. intros b Hb. apply Hx; [left; reflexivity | exact Hb].
    Qed.

    Lemma StronglySorted_app_cross {A : Type} (Rl : A -> A -> Prop) l1 l2 a b :
      StronglySorted Rl (l1 ++ l2) -> In a l1 -> In b l2 -> Rl a b.
    Proof.
      induction l1 as [|c l1 IH]; intros HS Ha Hb; [destruct Ha|].
      simpl in HS. apply StronglySorted_inv in HS as [HS HF].
      destruct Ha as [<- | Ha].
      - rewrite Forall_forall in HF. apply HF. apply in_or_app. right. exact Hb.
      - exact (IH HS Ha Hb).
    Qed.

    Lemma StronglySorted_filter {A : Type} (Rl : A -> A -> Prop) f l :
      StronglySorted Rl l -> StronglySorted Rl (filter f l).
    Proof.
      induction l as [|a l IH]; intros H; simpl; [constructor|].
      apply StronglySorted_inv in H as [H HF]. destruct (f a).
      - constructor; [exact (IH H)|]. rewrite Forall_forall in *. intros x Hx.
        apply filter_In in Hx as [Hx _]. exact (HF x Hx).
      - exact (IH H).
    Qed.

    Lemma StronglySorted_nth {A : Type} (Rl : A -> A -> Prop) l a b x y :
      StronglySorted Rl l -> a < b -> nth_error l a = Some x -> nth_error l b = Some y -> Rl x y.
    Proof.
      revert a b. induction l as [|c l IH]; intros a b HS Hab Ha Hb; [destruct a; discriminate|].
      apply StronglySorted_inv in HS as [HS HF]. destruct a as [|a]; destruct b as [|b]; try lia.
      - simpl in Ha, Hb. injection Ha as <-. rewrite Forall_forall in HF. apply HF.
        eapply nth_error_In. exact Hb.
      - simpl in Ha, Hb. apply (IH a b); auto. lia.
    Qed.

    Lemma before_map {A B : Type} (f : A -> B) W a b :
      RelaxedTraceLin.before W a b -> RelaxedTraceLin.before (map f W) (f a) (f b).
    Proof.
      intros (l1 & l2 & -> & Hb). exists (map f l1), (map f l2).
      split; [rewrite map_app; reflexivity | apply in_map; exact Hb].
    Qed.

    (** ** The incremental witness

        The witness is a list of the run's operations, each with its index
        in the run and the state after it, sorted lexicographically by
        timestamp and then by run index. *)

    Record WE : Type := mkWE { w_i : nat; w_e : Ent; w_st : vl_state P }.

    Definition wh (w : WE) : Time := e_h (w_e w).
    Definition wapp (w : WE) : bool := negb (vl_retro P (e_m (w_e w))).
    Definition wproj (w : WE) : RelaxedTraceLin.Op RS * vl_state P := (to_op (w_i w) (w_e w), w_st w).

    (** Lexicographic order on (timestamp, run index). *)
    Definition ltx (hi : Time) (i : nat) (hj : Time) (j : nat) : Prop :=
      Pos.lt hi hj \/ (hi = hj /\ i < j).

    Definition ltw (a b : WE) : Prop := ltx (wh a) (w_i a) (wh b) (w_i b).

    Lemma ltw_le a b : ltw a b -> Pos.le (wh a) (wh b).
    Proof. unfold ltw, ltx. lia. Qed.

    Lemma ltw_asym a b : ltw a b -> ltw b a -> False.
    Proof. unfold ltw, ltx. lia. Qed.

    Lemma sorted_before W a b :
      StronglySorted ltw W -> In a W -> In b W -> ltw a b -> RelaxedTraceLin.before W a b.
    Proof.
      induction W as [|c W IH]; intros HS Ha Hb Hab; [destruct Ha|].
      apply StronglySorted_inv in HS as [HS HF]. rewrite Forall_forall in HF.
      destruct Ha as [<- | Ha].
      - destruct Hb as [<- | Hb]; [exfalso; exact (ltw_asym _ _ Hab Hab)|].
        exists [], W. split; [reflexivity | exact Hb].
      - destruct Hb as [<- | Hb].
        + exfalso. exact (ltw_asym _ _ Hab (HF a Ha)).
        + destruct (IH HS Ha Hb Hab) as (l1 & l2 & HW & Hin). rewrite HW.
          exists (c :: l1), l2. split; [reflexivity | exact Hin].
    Qed.

    Record Wit (R : list Ent) (s : VState P) (W : list WE) : Prop := {
      wi_inv : Inv P s;
      wi_nd : NoDup (map w_i W);
      wi_all : forall i e, nth_error R i = Some e -> exists w, In w W /\ w_i w = i;
      wi_ent : forall w, In w W -> nth_error R (w_i w) = Some (w_e w);
      wi_sort : StronglySorted ltw W;
      wi_chain : Chain s0 (map wproj W);
      wi_post : forall w, In w W -> w_st w = vs_tl P s (wh w);
      wi_const : forall x y, Pos.le x y ->
        (forall w, In w W -> wapp w = true -> ~ (Pos.lt x (wh w) /\ Pos.le (wh w) y)) ->
        vs_tl P s x = vs_tl P s y;
      wi_one : vs_tl P s xH = s0;
      wi_hor : forall w, In w W -> Pos.le (wh w) (vs_hor P s);
      wi_past : forall i e, nth_error R i = Some e -> In (e_m e, e_h e) (vs_past P s (e_t e));
      wi_sync : forall i e, nth_error R i = Some e -> vl_sync P (e_m e) = true ->
        Pos.le (e_h e) (vs_floor P s);
      wi_dep : forall i j ei ej, i < j -> nth_error R i = Some ei -> nth_error R j = Some ej ->
        e_t ei = e_t ej -> vl_dep P (e_m ei) (e_m ej) = true -> Pos.lt (e_h ei) (e_h ej);
      wi_syncord : forall i j ei ej, i < j -> nth_error R i = Some ei -> nth_error R j = Some ej ->
        vl_sync P (e_m ei) = true -> Pos.lt (e_h ei) (e_h ej);
    }.

    Lemma Wit_init : Wit [] (vinit P s0) [].
    Proof.
      constructor; simpl; try (intros; contradiction); try reflexivity.
      - apply Inv_init.
      - constructor.
      - intros i e H. destruct i; discriminate.
      - constructor.
      - constructor.
      - intros i e H. destruct i; discriminate.
      - intros i e H. destruct i; discriminate.
      - intros i j ei ej _ H. destruct i; discriminate.
      - intros i j ei ej _ H. destruct i; discriminate.
    Qed.

    (** Splitting a sorted list at a timestamp. *)
    Definition le_h (x : Time) (w : WE) : bool := Pos.leb (wh w) x.

    Lemma filter_all_false {A : Type} (f : A -> bool) l :
      (forall a, In a l -> f a = false) -> filter f l = [].
    Proof.
      induction l as [|a l IH]; intros H; [reflexivity|]. simpl.
      rewrite (H a (or_introl eq_refl)). apply IH. intros b Hb. apply H. right. exact Hb.
    Qed.

    Lemma filter_all_true {A : Type} (f : A -> bool) l :
      (forall a, In a l -> f a = true) -> filter f l = l.
    Proof.
      induction l as [|a l IH]; intros H; [reflexivity|]. simpl.
      rewrite (H a (or_introl eq_refl)). f_equal. apply IH. intros b Hb. apply H. right. exact Hb.
    Qed.

    Lemma sorted_split x W :
      StronglySorted ltw W ->
      W = filter (le_h x) W ++ filter (fun w => negb (le_h x w)) W.
    Proof.
      induction W as [|a W IH]; intros HS; [reflexivity|].
      apply StronglySorted_inv in HS as [HS HF]. simpl.
      destruct (le_h x a) eqn:Ha; simpl.
      - f_equal. exact (IH HS).
      - assert (Hall : forall w, In w W -> le_h x w = false).
        { intros w Hw. rewrite Forall_forall in HF. specialize (HF w Hw). apply ltw_le in HF.
          unfold le_h in *. apply Pos.leb_gt in Ha. apply Pos.leb_gt. lia. }
        rewrite (filter_all_false _ _ Hall).
        rewrite filter_all_true; [reflexivity|]. intros w Hw. rewrite (Hall w Hw). reflexivity.
    Qed.

    (** The state at the end of a sorted prefix of the witness is the
        timeline at any bound of its timestamps. *)
    Lemma endst_sorted s W x :
      StronglySorted ltw W ->
      (forall w, In w W -> w_st w = vs_tl P s (wh w)) ->
      (forall w, In w W -> Pos.le (wh w) x) ->
      (forall x' y, Pos.le x' y -> Pos.le y x ->
        (forall w, In w W -> wapp w = true -> ~ (Pos.lt x' (wh w) /\ Pos.le (wh w) y)) ->
        vs_tl P s x' = vs_tl P s y) ->
      vs_tl P s xH = s0 ->
      endst s0 (map wproj W) = vs_tl P s x.
    Proof.
      intros HS Hpost Hle Hconst Hone.
      destruct W as [|w0 W0] using rev_ind.
      - simpl. rewrite <- Hone. apply Hconst; [lia | lia | intros w []].
      - clear IHW0. rewrite map_app. change (map wproj [w0]) with [wproj w0].
        rewrite endst_snoc. simpl.
        assert (Hwl : In w0 (W0 ++ [w0])) by (apply in_or_app; right; left; reflexivity).
        rewrite (Hpost w0 Hwl).
        apply Hconst; [apply Hle; exact Hwl | lia |].
        intros w Hw _ [Hlt Hle'].
        apply in_app_or in Hw as [Hw | [<- | []]].
        + pose proof (StronglySorted_app_cross _ _ _ _ _ HS Hw (or_introl eq_refl)) as Hs.
          apply ltw_le in Hs. lia.
        + lia.
    Qed.

    (** ** Preservation of the witness *)

    Lemma push_past_old (past : tid -> list (Sig.op E * Time)) t m h t' p :
      In p (past t') -> In p (push_past past t m h t').
    Proof. unfold push_past. destruct (Pos.eqb t t'); [right|]; auto. Qed.

    Lemma push_past_new (past : tid -> list (Sig.op E * Time)) t m h : In (m, h) (push_past past t m h t).
    Proof. unfold push_past. rewrite Pos.eqb_refl. left. reflexivity. Qed.

    (** The parts of the step that do not depend on its kind. *)
    Lemma rstep_common s e s' :
      Inv P s -> RStep s e s' ->
      vs_past P s' = push_past (vs_past P s) (e_t e) (e_m e) (e_h e) /\
      Pos.le (vs_floor P s) (vs_floor P s') /\
      (vl_sync P (e_m e) = true -> Pos.le (e_h e) (vs_floor P s')).
    Proof.
      intros HI (Hfl & Hdep & [(Hr & Hspec & ->) | (Hr & Hh & st & Hspec & ->)]); simpl.
      - split; [reflexivity|]. destruct (vl_sync P (e_m e)); split; try lia; discriminate.
      - pose proof (inv_floor P s HI).
        split; [reflexivity|]. destruct (vl_sync P (e_m e)); split; try lia; discriminate.
    Qed.

    Lemma Wit_step R s W e s' :
      Wit R s W -> RStep s e s' -> exists W', Wit (R ++ [e]) s' W'.
    Proof.
      intros HW Hst.
      pose proof (rstep_common _ _ _ (wi_inv _ _ _ HW) Hst) as (Hpast & Hfloor & Hsync).
      pose proof Hst as (Hfl & Hdep & _).
      set (n := length R).
      assert (Hidx : forall w, In w W -> w_i w < n).
      { intros w Hw. exact (nth_lt _ _ _ (wi_ent _ _ _ HW w Hw)). }
      (* Facts about past, dependencies and synchronization. *)
      assert (Hp' : forall i ei, nth_error (R ++ [e]) i = Some ei ->
                    In (e_m ei, e_h ei) (vs_past P s' (e_t ei))).
      { intros i ei Hi. rewrite Hpast. apply nth_snoc in Hi as [Hi | (_ & ->)].
        - apply push_past_old. exact (wi_past _ _ _ HW i ei Hi).
        - apply push_past_new. }
      assert (Hs' : forall i ei, nth_error (R ++ [e]) i = Some ei -> vl_sync P (e_m ei) = true ->
                    Pos.le (e_h ei) (vs_floor P s')).
      { intros i ei Hi Hy. apply nth_snoc in Hi as [Hi | (_ & ->)].
        - pose proof (wi_sync _ _ _ HW i ei Hi Hy). lia.
        - exact (Hsync Hy). }
      assert (Hd' : forall i j ei ej, i < j -> nth_error (R ++ [e]) i = Some ei ->
                    nth_error (R ++ [e]) j = Some ej ->
                    e_t ei = e_t ej -> vl_dep P (e_m ei) (e_m ej) = true -> Pos.lt (e_h ei) (e_h ej)).
      { intros i j ei ej Hij Hi Hj Ht Hd.
        apply nth_snoc in Hj as [Hj | (Hjn & ->)].
        - assert (Hi' : nth_error R i = Some ei).
          { rewrite nth_error_app1 in Hi; [exact Hi|]. pose proof (nth_lt _ _ _ Hj). lia. }
          exact (wi_dep _ _ _ HW i j ei ej Hij Hi' Hj Ht Hd).
        - assert (Hi' : nth_error R i = Some ei) by (rewrite nth_error_app1 in Hi; [exact Hi | lia]).
          rewrite <- Ht in Hdep. exact (Hdep _ _ (wi_past _ _ _ HW i ei Hi') Hd). }
      assert (Hy' : forall i j ei ej, i < j -> nth_error (R ++ [e]) i = Some ei ->
                    nth_error (R ++ [e]) j = Some ej ->
                    vl_sync P (e_m ei) = true -> Pos.lt (e_h ei) (e_h ej)).
      { intros i j ei ej Hij Hi Hj Hy.
        apply nth_snoc in Hj as [Hj | (Hjn & ->)].
        - assert (Hi' : nth_error R i = Some ei).
          { rewrite nth_error_app1 in Hi; [exact Hi|]. pose proof (nth_lt _ _ _ Hj). lia. }
          exact (wi_syncord _ _ _ HW i j ei ej Hij Hi' Hj Hy).
        - assert (Hi' : nth_error R i = Some ei) by (rewrite nth_error_app1 in Hi; [exact Hi | lia]).
          pose proof (wi_sync _ _ _ HW i ei Hi' Hy). lia. }
      assert (HI' : Inv P s') by exact (rstep_Inv _ _ _ Hst (wi_inv _ _ _ HW)).
      assert (Hent_old : forall w, In w W -> nth_error (R ++ [e]) (w_i w) = Some (w_e w)).
      { intros w Hw. apply nth_snoc_old. exact (wi_ent _ _ _ HW w Hw). }
      destruct Hst as (_ & _ & [(Hr & Hspec & Hs) | (Hr & Hh & st & Hspec & Hs)]).
      - (* Retroactive: insert after every entry with timestamp <= h. *)
        set (h := e_h e) in *.
        set (x := mkWE n e (vs_tl P s h)).
        set (W1 := filter (le_h h) W). set (W2 := filter (fun w => negb (le_h h w)) W).
        assert (HW12 : W = W1 ++ W2) by exact (sorted_split h W (wi_sort _ _ _ HW)).
        assert (Hin12 : forall w, In w W <-> In w W1 \/ In w W2).
        { intros w. rewrite HW12 at 1. split; [apply in_app_or | apply in_or_app]. }
        assert (HW1 : forall w, In w W1 -> In w W /\ Pos.le (wh w) h).
        { intros w Hw. apply filter_In in Hw as [Hw Hl]. unfold le_h in Hl. apply Pos.leb_le in Hl. auto. }
        assert (HW2 : forall w, In w W2 -> In w W /\ Pos.lt h (wh w)).
        { intros w Hw. apply filter_In in Hw as [Hw Hl]. unfold le_h in Hl.
          destruct (Pos.leb (wh w) h) eqn:Hb; [discriminate|]. apply Pos.leb_gt in Hb. auto. }
        assert (Htl : vs_tl P s' = vs_tl P s) by (rewrite Hs; reflexivity).
        assert (Hhor : vs_hor P s' = Pos.max (vs_hor P s) h) by (rewrite Hs; reflexivity).
        assert (Hin' : forall w, In w (W1 ++ x :: W2) -> In w W \/ w = x).
        { intros w Hw. apply in_app_or in Hw as [Hw | [<- | Hw]]; auto.
          - left. apply HW1. exact Hw.
          - left. apply HW2. exact Hw. }
        assert (Hold' : forall w, In w W -> In w (W1 ++ x :: W2)).
        { intros w Hw. apply Hin12 in Hw as [Hw | Hw]; apply in_or_app; [left | right; right]; exact Hw. }
        (* The prefix W1 ends in the state at h. *)
        assert (Hend : endst s0 (map wproj W1) = vs_tl P s h).
        { apply endst_sorted.
          - apply StronglySorted_filter. exact (wi_sort _ _ _ HW).
          - intros w Hw. apply (wi_post _ _ _ HW). apply HW1. exact Hw.
          - intros w Hw. apply HW1. exact Hw.
          - intros x' y Hxy Hyh Hn. apply (wi_const _ _ _ HW); [exact Hxy|].
            intros w Hw Ha [H1 H2]. apply Hin12 in Hw as [Hw | Hw].
            + exact (Hn w Hw Ha (conj H1 H2)).
            + apply HW2 in Hw as [_ Hw]. lia.
          - exact (wi_one _ _ _ HW). }
        exists (W1 ++ x :: W2). constructor.
        + exact HI'.
        + rewrite map_app. simpl.
          apply (Permutation_NoDup (l := n :: map w_i W)).
          * rewrite HW12, map_app. apply Permutation_middle.
          * constructor; [|exact (wi_nd _ _ _ HW)].
            intros Hn. apply in_map_iff in Hn as (w & Hwn & Hw). specialize (Hidx w Hw). lia.
        + intros i ei Hi. apply nth_snoc in Hi as [Hi | (-> & ->)].
          * destruct (wi_all _ _ _ HW i ei Hi) as (w & Hw & Hwi). exists w. split; [apply Hold'; exact Hw | exact Hwi].
          * exists x. split; [apply in_or_app; right; left; reflexivity | reflexivity].
        + intros w Hw. apply Hin' in Hw as [Hw | ->]; [exact (Hent_old w Hw)|]. apply nth_snoc_new.
        + apply StronglySorted_app.
          * apply StronglySorted_filter. exact (wi_sort _ _ _ HW).
          * constructor; [apply StronglySorted_filter; exact (wi_sort _ _ _ HW)|].
            apply Forall_forall. intros w Hw. apply HW2 in Hw as [_ Hw]. left. exact Hw.
          * intros a b Ha Hb. apply HW1 in Ha as [Ha Hah]. pose proof (Hidx a Ha).
            destruct Hb as [<- | Hb].
            -- unfold ltw, ltx, x, wh in *. simpl. lia.
            -- apply HW2 in Hb as [_ Hb]. left. lia.
        + pose proof (wi_chain _ _ _ HW) as Hc. rewrite HW12, map_app in Hc.
          apply chain_app in Hc as [Hc1 Hc2]. rewrite Hend in Hc2.
          rewrite map_app. apply chain_app. split; [exact Hc1|].
          rewrite Hend. constructor; [exact Hspec | exact Hc2].
        + intros w Hw. rewrite Htl. apply Hin' in Hw as [Hw | ->]; [exact (wi_post _ _ _ HW w Hw) | reflexivity].
        + intros x' y Hxy Hn. rewrite Htl. apply (wi_const _ _ _ HW); [exact Hxy|].
          intros w Hw. apply Hn. apply Hold'. exact Hw.
        + rewrite Htl. exact (wi_one _ _ _ HW).
        + intros w Hw. rewrite Hhor. apply Hin' in Hw as [Hw | ->].
          * pose proof (wi_hor _ _ _ HW w Hw). lia.
          * unfold wh. simpl. fold h. lia.
        + exact Hp'.
        + exact Hs'.
        + exact Hd'.
        + exact Hy'.
      - (* Appended: add at the end. *)
        set (h := e_h e) in *.
        set (x := mkWE n e st).
        assert (Htl : vs_tl P s' = tl_write P (vs_tl P s) h st) by (rewrite Hs; reflexivity).
        assert (Hhor : vs_hor P s' = h) by (rewrite Hs; reflexivity).
        assert (Hbelow : forall w, In w W -> Pos.lt (wh w) h).
        { intros w Hw. pose proof (wi_hor _ _ _ HW w Hw). lia. }
        assert (Hin' : forall w, In w (W ++ [x]) -> In w W \/ w = x).
        { intros w Hw. apply in_app_or in Hw as [Hw | [<- | []]]; auto. }
        assert (Hold' : forall w, In w W -> In w (W ++ [x])).
        { intros w Hw. apply in_or_app. left. exact Hw. }
        assert (Hend : endst s0 (map wproj W) = vs_tl P s h).
        { apply endst_sorted.
          - exact (wi_sort _ _ _ HW).
          - exact (wi_post _ _ _ HW).
          - intros w Hw. pose proof (Hbelow w Hw). lia.
          - intros x' y Hxy _ Hn. exact (wi_const _ _ _ HW x' y Hxy Hn).
          - exact (wi_one _ _ _ HW). }
        assert (Htl_old : forall y, Pos.lt y h -> vs_tl P s' y = vs_tl P s y).
        { intros y Hy. rewrite Htl. unfold tl_write. destruct (Pos.leb h y) eqn:Hb; [|reflexivity].
          apply Pos.leb_le in Hb. lia. }
        assert (Htl_new : forall y, Pos.le h y -> vs_tl P s' y = st).
        { intros y Hy. rewrite Htl. unfold tl_write. apply Pos.leb_le in Hy. rewrite Hy. reflexivity. }
        exists (W ++ [x]). constructor.
        + exact HI'.
        + rewrite map_app. simpl.
          apply (Permutation_NoDup (l := n :: map w_i W)); [apply Permutation_cons_append|].
          constructor; [|exact (wi_nd _ _ _ HW)].
          intros Hn. apply in_map_iff in Hn as (w & Hwn & Hw). specialize (Hidx w Hw). lia.
        + intros i ei Hi. apply nth_snoc in Hi as [Hi | (-> & ->)].
          * destruct (wi_all _ _ _ HW i ei Hi) as (w & Hw & Hwi). exists w. split; [apply Hold'; exact Hw | exact Hwi].
          * exists x. split; [apply in_or_app; right; left; reflexivity | reflexivity].
        + intros w Hw. apply Hin' in Hw as [Hw | ->]; [exact (Hent_old w Hw)|]. apply nth_snoc_new.
        + apply StronglySorted_app; [exact (wi_sort _ _ _ HW) | repeat constructor |].
          intros a b Ha [<- | []]. left. exact (Hbelow a Ha).
        + rewrite map_app. apply chain_app. split; [exact (wi_chain _ _ _ HW)|].
          rewrite Hend. simpl. constructor; [exact Hspec | constructor].
        + intros w Hw. apply Hin' in Hw as [Hw | ->].
          * rewrite Htl_old by exact (Hbelow w Hw). exact (wi_post _ _ _ HW w Hw).
          * simpl. symmetry. apply Htl_new. unfold wh. simpl. lia.
        + intros x' y Hxy Hn.
          destruct (Pos.leb h x') eqn:Hx; [apply Pos.leb_le in Hx | apply Pos.leb_gt in Hx].
          * rewrite !Htl_new by lia. reflexivity.
          * destruct (Pos.leb h y) eqn:Hy; [apply Pos.leb_le in Hy | apply Pos.leb_gt in Hy].
            -- exfalso. apply (Hn x); [apply in_or_app; right; left; reflexivity | | ].
               ++ unfold wapp. simpl. rewrite Hr. reflexivity.
               ++ unfold wh. simpl. fold h. lia.
            -- rewrite !Htl_old by lia. apply (wi_const _ _ _ HW); [exact Hxy|].
               intros w Hw. apply Hn. apply Hold'. exact Hw.
        + rewrite Htl_old; [exact (wi_one _ _ _ HW)|]. pose proof (inv_floor P s (wi_inv _ _ _ HW)). lia.
        + intros w Hw. rewrite Hhor. apply Hin' in Hw as [Hw | ->].
          * pose proof (Hbelow w Hw). lia.
          * unfold wh. simpl. fold h. lia.
        + exact Hp'.
        + exact Hs'.
        + exact Hd'.
        + exact Hy'.
    Qed.

    Lemma run_witness R s : Run R s -> exists W, Wit R s W.
    Proof.
      induction 1 as [|R s e s' HR IH Hst].
      - exists []. exact Wit_init.
      - destruct IH as (W & HW). exact (Wit_step R s W e s' HW Hst).
    Qed.

    Lemma run_Inv R s : Run R s -> Inv P s.
    Proof. intros HR. destruct (run_witness R s HR) as (W & HW). exact (wi_inv _ _ _ HW). Qed.

    (** ** Adequacy for any trace with suitably delayed responses *)

    Section Trace.
      Import RelaxedLTSSpec RelaxedTraceLin.
      Context {X : Type} (sel : X -> option (RelaxedLTSSpec.ThreadEvent RS)) (L : list X).

      (** [Del R L]: [L] is a complete relaxed trace of the operations of
          [R], with operation [i] of [R] called under the key
          [(e_t e, i)], such that:
          - same-thread invocations keep the run order ([del_po]);
          - a response that precedes an invocation belongs to an
            operation that is smaller in (timestamp, run index) order
            ([del_rt]). *)
      Record Del (R : list Ent) : Prop := {
        del_occ : forall i e, nth_error R i = Some e -> occurs sel L (to_op i e);
        del_key : forall a k m, inv_at sel L a k m ->
          exists e, nth_error R (snd k) = Some e /\ fst k = e_t e;
        del_po : forall a b i j ei ej,
          nth_error R i = Some ei -> nth_error R j = Some ej -> e_t ei = e_t ej ->
          inv_at sel L a (e_t ei, i) (e_m ei) -> inv_at sel L b (e_t ej, j) (e_m ej) ->
          a < b -> i < j;
        del_rt : forall a b i j ei ej,
          nth_error R i = Some ei -> nth_error R j = Some ej ->
          res_at sel L a (e_t ei, i) (e_m ei) (e_r ei) -> inv_at sel L b (e_t ej, j) (e_m ej) ->
          a < b -> ltx (e_h ei) i (e_h ej) j;
      }.

      Lemma NoDup_map_compose {A B C : Type} (f : B -> C) (g : A -> B) l :
        NoDup (map (fun a => f (g a)) l) -> NoDup (map g l).
      Proof. intros H. rewrite <- map_map in H. exact (NoDup_map_inv _ _ H). Qed.

      Theorem run_rel_lin R s :
        Run R s -> Del R -> rel_lin sel L (RelaxedSig.semi_independent RS) nu_P.
      Proof.
        intros HR HD. destruct (run_witness R s HR) as (W & HW).
        set (f := fun w => to_op (w_i w) (w_e w)).
        assert (Hf : forall o, In o (map f W) -> exists w, In w W /\ o = f w).
        { intros o Ho. apply in_map_iff in Ho as (w & <- & Hw). eauto. }
        exists (map f W). split; [|split; [|split; [|split]]].
        - exists (map wproj W). split; [exact (wi_chain _ _ _ HW)|].
          rewrite map_map. reflexivity.
        - rewrite map_map. apply (NoDup_map_compose snd). simpl. exact (wi_nd _ _ _ HW).
        - intros o Ho. destruct (Hf o Ho) as (w & Hw & ->).
          exact (del_occ _ HD _ _ (wi_ent _ _ _ HW w Hw)).
        - intros a k m Ha. destruct (del_key _ HD a k m Ha) as (e & He & Ht).
          destruct (wi_all _ _ _ HW _ _ He) as (w & Hw & Hwi).
          pose proof (wi_ent _ _ _ HW w Hw) as Hwe. rewrite Hwi, He in Hwe. injection Hwe as Hwe.
          exists (f w). split; [apply in_map; exact Hw|].
          destruct k as [t i]. simpl in *. unfold f, to_op. simpl. rewrite Hwi, <- Hwe, Ht. reflexivity.
        - intros o o' Ho Ho' Hr.
          destruct (Hf o Ho) as (w & Hw & ->). destruct (Hf o' Ho') as (w' & Hw' & ->).
          apply before_map. apply sorted_before; [exact (wi_sort _ _ _ HW) | exact Hw | exact Hw' |].
          pose proof (wi_ent _ _ _ HW w Hw) as He. pose proof (wi_ent _ _ _ HW w' Hw') as He'.
          destruct Hr as [(a & b & Ha & Hb & Hab) | (Ht & a & b & Ha & Hb & Hab & Hn)].
          + exact (del_rt _ HD a b _ _ _ _ He He' Ha Hb Hab).
          + simpl in Ht, Hn.
            assert (Hd : vl_dep P (e_m (w_e w)) (e_m (w_e w')) = true)
              by (destruct (vl_dep P (e_m (w_e w)) (e_m (w_e w'))); [reflexivity | exfalso; apply Hn; reflexivity]).
            pose proof (del_po _ HD a b _ _ _ _ He He' Ht Ha Hb Hab) as Hij.
            left. exact (wi_dep _ _ _ HW _ _ _ _ Hij He He' Ht Hd).
      Qed.
    End Trace.

    (** ** The canonical trace of a run

        Operation [i] is invoked in run order.  Its response follows the
        invocation immediately, unless a later operation of the run has a
        strictly smaller timestamp ([ovt]); then the response is delayed
        to the end of the trace. *)

    Definition ovt (e : Ent) (l : list Ent) : bool :=
      existsb (fun e' => Pos.ltb (e_h e') (e_h e)) l.

    Fixpoint blocks (i : nat) (l : list Ent) : list (nat * bool) :=
      match l with
      | [] => []
      | e :: l' => (i, false) :: (if ovt e l' then [] else [(i, true)]) ++ blocks (S i) l'
      end.

    Fixpoint late (i : nat) (l : list Ent) : list (nat * bool) :=
      match l with
      | [] => []
      | e :: l' => (if ovt e l' then [(i, true)] else []) ++ late (S i) l'
      end.

    Definition canon (R : list Ent) : list (nat * bool) := blocks 0 R ++ late 0 R.

    (** [(i, false)] is the invocation and [(i, true)] the response of
        operation [i]. *)
    Definition csel (R : list Ent) (x : nat * bool) : option (RelaxedLTSSpec.ThreadEvent RS) :=
      match nth_error R (fst x) with
      | Some e => Some (RelaxedLTSSpec.Build_ThreadEvent (e_t e)
                   (if snd x then RelaxedLTSSpec.ResEv (E := RS) (fst x) (e_m e) (e_r e)
                    else RelaxedLTSSpec.InvEv (E := RS) (fst x) (e_m e)))
      | None => None
      end.

    Definition rank (x : nat * bool) : nat := 2 * fst x + (if snd x then 1 else 0).

    Lemma blocks_range i l j b : In (j, b) (blocks i l) -> i <= j.
    Proof.
      revert i. induction l as [|e l IH]; intros i H; [destruct H|]. simpl in H.
      destruct H as [H | H]; [injection H; lia|].
      apply in_app_or in H as [H | H].
      - destruct (ovt e l); [destruct H | destruct H as [H | []]; injection H; lia].
      - specialize (IH _ H). lia.
    Qed.

    Lemma blocks_sorted i l : StronglySorted (fun x y => rank x < rank y) (blocks i l).
    Proof.
      revert i. induction l as [|e l IH]; intros i; simpl; [constructor|].
      constructor.
      - apply StronglySorted_app.
        + destruct (ovt e l); repeat constructor.
        + apply IH.
        + intros a b Ha Hb. destruct b as [j c]. apply blocks_range in Hb.
          destruct (ovt e l); [destruct Ha | destruct Ha as [<- | []]]. unfold rank. simpl.
          destruct c; lia.
      - apply Forall_forall. intros [j c] H. apply in_app_or in H as [H | H].
        + destruct (ovt e l); [destruct H | destruct H as [H | []]]. injection H as <- <-.
          unfold rank. simpl. lia.
        + apply blocks_range in H. unfold rank. simpl. destruct c; lia.
    Qed.

    Lemma late_true i l j b : In (j, b) (late i l) -> b = true.
    Proof.
      revert i. induction l as [|e l IH]; intros i H; [destruct H|]. simpl in H.
      apply in_app_or in H as [H | H].
      - destruct (ovt e l); [destruct H as [H | []]; injection H; auto | destruct H].
      - exact (IH _ H).
    Qed.

    Lemma blocks_res i l j :
      In (j, true) (blocks i l) ->
      exists e, nth_error l (j - i) = Some e /\ ovt e (skipn (S (j - i)) l) = false /\ i <= j.
    Proof.
      revert i. induction l as [|e l IH]; intros i H; [destruct H|]. simpl in H.
      destruct H as [H | H]; [discriminate|].
      apply in_app_or in H as [H | H].
      - destruct (ovt e l) eqn:Ho; [destruct H|]. destruct H as [H | []]. injection H as <-.
        exists e. rewrite Nat.sub_diag. simpl. auto.
      - destruct (IH _ H) as (e' & He & Ho & Hle).
        exists e'. replace (j - i) with (S (j - S i)) by lia. simpl. split; [exact He|]. split; [exact Ho | lia].
    Qed.

    Lemma blocks_in i l k e :
      nth_error l k = Some e ->
      In ((i + k)%nat, false) (blocks i l) /\
      (ovt e (skipn (S k) l) = false -> In ((i + k)%nat, true) (blocks i l)) /\
      (ovt e (skipn (S k) l) = true -> In ((i + k)%nat, true) (late i l)).
    Proof.
      revert i k. induction l as [|e0 l IH]; intros i k H; [destruct k; discriminate|].
      destruct k as [|k]; simpl in H.
      - injection H as <-. rewrite Nat.add_0_r. simpl. split; [left; reflexivity|]. split.
        + intros Ho. rewrite Ho. right. left. reflexivity.
        + intros Ho. rewrite Ho. left. reflexivity.
      - destruct (IH (S i) k H) as (H1 & H2 & H3). replace (i + S k)%nat with (S i + k)%nat by lia.
        simpl. split; [|split].
        + right. apply in_or_app. right. exact H1.
        + intros Ho. right. apply in_or_app. right. exact (H2 Ho).
        + intros Ho. apply in_or_app. right. exact (H3 Ho).
    Qed.

    Lemma blocks_adj i l k e :
      nth_error l k = Some e -> ovt e (skipn (S k) l) = false ->
      exists l1 l2, blocks i l = l1 ++ ((i + k)%nat, false) :: ((i + k)%nat, true) :: l2.
    Proof.
      revert i k. induction l as [|e0 l IH]; intros i k H Ho; [destruct k; discriminate|].
      destruct k as [|k]; simpl in H.
      - injection H as <-. simpl in Ho. rewrite Nat.add_0_r. simpl. rewrite Ho.
        exists [], (blocks (S i) l). reflexivity.
      - simpl in Ho. destruct (IH (S i) k H Ho) as (l1 & l2 & Hb).
        exists ((i, false) :: (if ovt e0 l then [] else [(i, true)]) ++ l1), l2.
        simpl. rewrite Hb, <- app_assoc. replace (i + S k)%nat with (S i + k)%nat by lia. reflexivity.
    Qed.

    Lemma ovt_false e l : ovt e l = false -> forall e', In e' l -> Pos.le (e_h e) (e_h e').
    Proof.
      intros H e' Hin. unfold ovt in H.
      destruct (Pos.ltb (e_h e') (e_h e)) eqn:Hlt.
      - exfalso. assert (Hex : existsb (fun e'' => Pos.ltb (e_h e'') (e_h e)) l = true)
          by (apply existsb_exists; eauto). congruence.
      - apply Pos.ltb_ge in Hlt. exact Hlt.
    Qed.

    Lemma ovt_false_intro e l : (forall e', In e' l -> Pos.le (e_h e) (e_h e')) -> ovt e l = false.
    Proof.
      intros H. unfold ovt. destruct (existsb _ l) eqn:Hex; [|reflexivity].
      apply existsb_exists in Hex as (e' & Hin & Hlt). apply Pos.ltb_lt in Hlt.
      specialize (H e' Hin). lia.
    Qed.

    Lemma in_skipn_nth {A : Type} (l : list A) i x :
      In x (skipn (S i) l) -> exists j, i < j /\ nth_error l j = Some x.
    Proof.
      intros H. apply In_nth_error in H as (k & Hk). rewrite nth_error_skipn in Hk.
      exists (S i + k)%nat. split; [lia | exact Hk].
    Qed.

    Section Canon.
      Import RelaxedLTSSpec RelaxedTraceLin.
      Context (R : list Ent).

      Lemma canon_nth_in a x : nth_error (canon R) a = Some x -> In x (canon R).
      Proof. apply nth_error_In. Qed.

      Lemma csel_inv a k m :
        inv_at (csel R) (canon R) a k m ->
        nth_error (canon R) a = Some (snd k, false) /\
        exists e, nth_error R (snd k) = Some e /\ fst k = e_t e.
      Proof.
        intros ([j b] & Ha & Hs). unfold csel in Hs. simpl in Hs.
        destruct (nth_error R j) as [e|] eqn:He; [|discriminate].
        injection Hs as Ht Hev. destruct b; [discriminate|]. injection Hev as Hj _.
        subst j. split; [exact Ha|]. eauto.
      Qed.

      Lemma csel_res a k m r :
        res_at (csel R) (canon R) a k m r -> nth_error (canon R) a = Some (snd k, true).
      Proof.
        intros ([j b] & Ha & Hs). unfold csel in Hs. simpl in Hs.
        destruct (nth_error R j) as [e|] eqn:He; [|discriminate].
        injection Hs as Ht Hev. destruct b; [|discriminate]. injection Hev as Hj _.
        subst j. exact Ha.
      Qed.

      (** An invocation lies in the [blocks] part. *)
      Lemma canon_inv_pos b j :
        nth_error (canon R) b = Some (j, false) ->
        b < length (blocks 0 R) /\ nth_error (blocks 0 R) b = Some (j, false).
      Proof.
        intros H. unfold canon in H. destruct (Nat.lt_ge_cases b (length (blocks 0 R))) as [Hb | Hb].
        - rewrite nth_error_app1 in H by exact Hb. auto.
        - rewrite nth_error_app2 in H by exact Hb. apply nth_error_In in H.
          apply late_true in H. discriminate.
      Qed.

      Lemma canon_before a b x j :
        nth_error (canon R) a = Some x -> nth_error (canon R) b = Some (j, false) -> a < b ->
        rank x < rank (j, false) /\ In x (blocks 0 R).
      Proof.
        intros Ha Hb Hab. apply canon_inv_pos in Hb as [Hb Hb'].
        unfold canon in Ha. rewrite nth_error_app1 in Ha by lia.
        split; [|eapply nth_error_In; exact Ha].
        exact (StronglySorted_nth _ _ _ _ _ _ (blocks_sorted 0 R) Hab Ha Hb').
      Qed.

      Lemma occurs_canon i e : nth_error R i = Some e -> occurs (csel R) (canon R) (to_op i e).
      Proof.
        intros He. destruct (blocks_in 0 R i e He) as (H1 & H2 & H3). rewrite Nat.add_0_l in H1, H2, H3.
        assert (Hres : In (i, true) (canon R)).
        { unfold canon. apply in_or_app. destruct (ovt e (skipn (S i) R)).
          - right. exact (H3 eq_refl).
          - left. exact (H2 eq_refl). }
        assert (Hinv : In (i, false) (canon R)) by (unfold canon; apply in_or_app; left; exact H1).
        split.
        - apply In_nth_error in Hinv as (a & Ha). exists a, (i, false). split; [exact Ha|].
          unfold csel. simpl. rewrite He. reflexivity.
        - apply In_nth_error in Hres as (a & Ha). exists a, (i, true). split; [exact Ha|].
          unfold csel. simpl. rewrite He. reflexivity.
      Qed.

      Lemma canon_del : Del (csel R) (canon R) R.
      Proof.
        constructor.
        - exact occurs_canon.
        - intros a k m Ha. exact (proj2 (csel_inv a k m Ha)).
        - intros a b i j ei ej Hi Hj _ Ha Hb Hab.
          apply csel_inv in Ha as [Ha _]. apply csel_inv in Hb as [Hb _]. simpl in Ha, Hb.
          destruct (canon_before a b _ _ Ha Hb Hab) as [Hr _]. unfold rank in Hr. simpl in Hr. lia.
        - intros a b i j ei ej Hi Hj Ha Hb Hab.
          apply csel_res in Ha. apply csel_inv in Hb as [Hb _]. simpl in Ha, Hb.
          destruct (canon_before a b _ _ Ha Hb Hab) as [Hr Hin]. unfold rank in Hr. simpl in Hr.
          apply blocks_res in Hin as (e & He & Ho & _). rewrite Nat.sub_0_r in He, Ho.
          rewrite Hi in He. injection He as <-.
          assert (Hle : Pos.le (e_h ei) (e_h ej)).
          { apply (ovt_false ei (skipn (S i) R) Ho). rewrite <- (firstn_skipn (S i) R) in Hj.
            rewrite nth_error_app2 in Hj.
            - apply nth_error_In in Hj. exact Hj.
            - rewrite length_firstn. lia. }
          unfold ltx. lia.
      Qed.

      Theorem canon_rel_lin s :
        Run R s -> rel_lin (csel R) (canon R) (RelaxedSig.semi_independent RS) nu_P.
      Proof. intros HR. exact (run_rel_lin (csel R) (canon R) R s HR canon_del). Qed.

      (** A response is delayed only if a later operation is timestamped
          strictly before it.  Otherwise it immediately follows its
          invocation. *)
      Lemma canon_prompt i e :
        nth_error R i = Some e ->
        (forall j ej, i < j -> nth_error R j = Some ej -> Pos.le (e_h e) (e_h ej)) ->
        exists l1 l2, canon R = l1 ++ (i, false) :: (i, true) :: l2.
      Proof.
        intros He Hle.
        assert (Ho : ovt e (skipn (S i) R) = false).
        { apply ovt_false_intro. intros e' Hin. apply in_skipn_nth in Hin as (j & Hij & Hj).
          exact (Hle j e' Hij Hj). }
        destruct (blocks_adj 0 R i e He Ho) as (l1 & l2 & Hb). rewrite Nat.add_0_l in Hb.
        exists l1, (l2 ++ late 0 R). unfold canon. rewrite Hb, <- app_assoc. reflexivity.
      Qed.

      (** Synchronizing operations are never delayed. *)
      Theorem canon_sync_prompt s i e :
        Run R s -> nth_error R i = Some e -> vl_sync P (e_m e) = true ->
        exists l1 l2, canon R = l1 ++ (i, false) :: (i, true) :: l2.
      Proof.
        intros HR He Hy. destruct (run_witness R s HR) as (W & HW).
        apply (canon_prompt i e He). intros j ej Hij Hj.
        pose proof (wi_syncord _ _ _ HW i j e ej Hij He Hj Hy). lia.
      Qed.
    End Canon.

    (** ** Executions of the lifted LTS *)

    Definition ent_ev (e : Ent) : @LTSSpec.ThreadEvent E :=
      LTSSpec.Build_ThreadEvent (e_t e) (LTSSpec.ResEv (e_m e) (e_r e)).

    (** The responses of an event sequence. *)
    Definition resps (evs : list (@LTSSpec.ThreadEvent E)) : list (@LTSSpec.ThreadEvent E) :=
      filter (fun ev => match LTSSpec.te_ev ev with LTSSpec.ResEv _ _ => true | _ => false end) evs.

    Inductive Exec : list (@LTSSpec.ThreadEvent E) -> @AtomicLTS.AState E (VState P) -> Prop :=
    | exec_nil : Exec [] (AtomicLTS.Idle (vinit P s0))
    | exec_snoc evs st ev st' :
        Exec evs st -> LTS.LTSSpec.Step (VL P) ev st st' -> Exec (evs ++ [ev]) st'.

    Lemma exec_run evs st :
      Exec evs st -> exists R, Run R (AtomicLTS.state st) /\ resps evs = map ent_ev R.
    Proof.
      induction 1 as [|evs st ev st' HE IH Hst].
      - exists []. split; [constructor | reflexivity].
      - destruct IH as (R & HR & Hres). simpl in Hst.
        destruct Hst as [t m s1 s2 Hv | t m r s1 s2 Hv]; simpl in HR |- *.
        + exists R. unfold resps. rewrite filter_app. simpl. rewrite app_nil_r. split; [|exact Hres].
          remember (LTSSpec.Build_ThreadEvent t (LTSSpec.InvEv m)) as ev0 eqn:Hev0.
          destruct Hv as [t1 m1 s e He | t1 m1 r1 h s s' e He | t1 m1 r1 h st0 s s' e He];
            [exact HR | |]; rewrite He in Hev0; discriminate (f_equal LTSSpec.te_ev Hev0).
        + destruct (vstep_rstep s1 t m r s2 (run_Inv R s1 HR) Hv) as (h & Hr).
          exists (R ++ [mkEnt t m r h]). split; [exact (run_snoc R s1 _ s2 HR Hr)|].
          unfold resps in *. rewrite filter_app, Hres, map_app. reflexivity.
    Qed.

    (** End-to-end adequacy: every execution of [VL P] from [vinit s0]
        determines a run whose canonical trace is relaxed linearizable,
        with the responses of the execution in run order. *)
    Theorem vl_exec_rel_lin evs st :
      Exec evs st ->
      exists R, resps evs = map ent_ev R /\
        RelaxedTraceLin.rel_lin (csel R) (canon R) (RelaxedSig.semi_independent RS) nu_P.
    Proof.
      intros HE. destruct (exec_run evs st HE) as (R & HR & Hres).
      exists R. split; [exact Hres | exact (canon_rel_lin R _ HR)].
    Qed.
  End Adequacy.
End ViewLiftAdequacy.
