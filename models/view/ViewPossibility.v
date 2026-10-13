(** * View-based possibilities without view-based compatibility

    The paper's Thm. I.9 (soundness of the view-based possibility
    simulation, Def. I.7–I.8) assumes that the objects are view-based
    compatible (Def. I.1).  Its proof uses compatibility to keep a
    timestamp-ordered witness after an operation is stamped below an
    operation already justified.  This file checks two claims about that
    assumption, for complete traces and with real time ([view_rt],
    [models/view/PrefixView.v]).

    Part 1 ([Poss]): the possibility rules VT-Invoke / VT-Return already
    require [t · e ∈ view(ν)] of the abstract trace [t].  If this side
    condition is checked as stated, compatibility is not needed.

    - A possibility run interleaves concrete events ([CEv]) with abstract
      VT-Invoke ([AInv]) and VT-Return ([ARet]) steps.  The stamp of an
      abstract invocation of key [k] is [H k].
    - Each step satisfies local conditions ([ok]).  An abstract invocation
      follows the concrete one.  Its stamp is above the stamps of the
      operations that responded before the concrete invocation (real time,
      the condition missing from the paper; see [PrefixView]) and of the
      earlier dependent invocations of the same thread.  An abstract
      response follows the abstract invocation and is the first for its
      key.  A concrete response follows the abstract one, with the same
      value.
    - The side condition ([side]) asks only that the extended abstract
      trace have a timestamp-ordered witness ([PrefixView.lin_h]).  This is
      weaker than [t · e ∈ view(ν)], which also asks it of every prefix
      and asks Def. I.2(3) of [t].
    - Concrete traces may have several pending operations per thread
      (futures); Def. I.7 allows one.
    - [poss_view_rt]: the concrete trace has a real-time-respecting prefix
      view, so it is relaxed linearizable ([poss_rel_lin]).  The only
      hypothesis on [ν] is [ν []].

    Part 2 ([Timeline]): when [ν] is the sequential specification of a
    [ViewLift] parameter set, the [ViewLift] timeline rule discharges the
    side condition.  The rule is: an operation is appended above every
    existing timestamp, unless it leaves the state unchanged.

    - [TValid]: the local conditions hold, and the abstract responses of
      the run, in order and with the possibility's stamps, form a
      [ViewLiftAdequacy.Run].
    - [timeline_wit], [timeline_valid]: then every step satisfies [side].
      The witness is the incremental witness of [ViewLiftAdequacy] ([Wit])
      with the run's keys put back.
    - [timeline_view_rt], [timeline_rel_lin]: hence the conclusions of
      Part 1 hold for every [ViewLift] object, with no compatibility
      hypothesis.

    [examples/View/ViewLiftMultiWriter.v] gives a run satisfying [TValid]
    whose concrete trace is a non-SC TSO behaviour ([poss_run_rel_lin]). *)

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
Require Import models.view.ViewLift.
Require Import models.view.ViewLiftAdequacy.
Require Import models.view.PrefixView.
Import ListNotations.

Module ViewPossibility.
  Import RelaxedSig RelaxedLTSSpec RelaxedTraceLin.

  (** ** Events at an index of a concatenation *)

  Section Idx.
    Context {E : RelaxedSig.t}.

    Abbreviation inv L := (inv_at (@PrefixView.sel E) L).
    Abbreviation res L := (res_at (@PrefixView.sel E) L).

    Lemma nth_some_lt {A : Type} (l : list A) i x : nth_error l i = Some x -> i < length l.
    Proof. intros H. apply nth_error_Some. congruence. Qed.

    Lemma inv_lt L i k m : inv L i k m -> i < length L.
    Proof. intros (x & Hx & _). exact (nth_some_lt _ _ _ Hx). Qed.

    Lemma res_lt L i k m r : res L i k m r -> i < length L.
    Proof. intros (x & Hx & _). exact (nth_some_lt _ _ _ Hx). Qed.

    Lemma inv_app_l L1 L2 i k m : inv L1 i k m -> inv (L1 ++ L2) i k m.
    Proof.
      intros (x & Hx & Hs). exists x. split; [|exact Hs].
      rewrite nth_error_app1; [exact Hx | exact (nth_some_lt _ _ _ Hx)].
    Qed.

    Lemma res_app_l L1 L2 i k m r : res L1 i k m r -> res (L1 ++ L2) i k m r.
    Proof.
      intros (x & Hx & Hs). exists x. split; [|exact Hs].
      rewrite nth_error_app1; [exact Hx | exact (nth_some_lt _ _ _ Hx)].
    Qed.

    Lemma inv_app_lt L1 L2 i k m : i < length L1 -> inv (L1 ++ L2) i k m -> inv L1 i k m.
    Proof. intros Hi (x & Hx & Hs). exists x. rewrite nth_error_app1 in Hx by exact Hi. auto. Qed.

    Lemma res_app_lt L1 L2 i k m r : i < length L1 -> res (L1 ++ L2) i k m r -> res L1 i k m r.
    Proof. intros Hi (x & Hx & Hs). exists x. rewrite nth_error_app1 in Hx by exact Hi. auto. Qed.

    Lemma inv_In L i k m : inv L i k m -> In (Build_ThreadEvent (fst k) (InvEv (snd k) m)) L.
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      exact (nth_error_In _ _ Hx).
    Qed.

    Lemma res_In L i k m r : res L i k m r -> In (Build_ThreadEvent (fst k) (ResEv (snd k) m r)) L.
    Proof.
      intros (x & Hx & Hs). unfold PrefixView.sel in Hs. injection Hs as ->.
      exact (nth_error_In _ _ Hx).
    Qed.

    Lemma In_res L k m r : In (Build_ThreadEvent (fst k) (ResEv (snd k) m r)) L -> exists j, res L j k m r.
    Proof.
      intros Hin. apply In_nth_error in Hin as (j & Hj). exists j. exists (Build_ThreadEvent (fst k) (ResEv (snd k) m r)).
      split; [exact Hj | reflexivity].
    Qed.

    Lemma In_inv L k m : In (Build_ThreadEvent (fst k) (InvEv (snd k) m)) L -> exists i, inv L i k m.
    Proof.
      intros Hin. apply In_nth_error in Hin as (i & Hi). exists i. exists (Build_ThreadEvent (fst k) (InvEv (snd k) m)).
      split; [exact Hi | reflexivity].
    Qed.

    Lemma inv_ev_inj (k k' : CallKey E) m m' :
      Build_ThreadEvent (fst k) (InvEv (snd k) m) = Build_ThreadEvent (fst k') (InvEv (snd k') m') ->
      k = k' /\ m = m'.
    Proof.
      intros Hev. pose proof (f_equal (te_tid E) Hev) as Ht. pose proof (f_equal (te_ev E) Hev) as Hv.
      pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Ho.
      simpl in Ht, Hh, Ho. split; [|exact Ho]. destruct k, k'; simpl in *; congruence.
    Qed.

    Lemma res_ev_inj (k k' : CallKey E) m m' (r : Sig.ar m) (r' : Sig.ar m') :
      Build_ThreadEvent (fst k) (ResEv (snd k) m r) = Build_ThreadEvent (fst k') (ResEv (snd k') m' r') ->
      k = k' /\ m = m'.
    Proof.
      intros Hev. pose proof (f_equal (te_tid E) Hev) as Ht. pose proof (f_equal (te_ev E) Hev) as Hv.
      pose proof (f_equal event_handle Hv) as Hh. pose proof (f_equal event_op Hv) as Ho.
      simpl in Ht, Hh, Ho. split; [|exact Ho]. destruct k, k'; simpl in *; congruence.
    Qed.

    Lemma res_ev_ret (k : CallKey E) m (r r' : Sig.ar m) :
      Build_ThreadEvent (fst k) (ResEv (snd k) m r) = Build_ThreadEvent (fst k) (ResEv (snd k) m r') -> r = r'.
    Proof.
      intros Hev. pose proof (f_equal (te_ev E) Hev) as Hv. simpl in Hv. exact (ResEvInversion _ _ _ _ Hv).
    Qed.
    Lemma op_ret_eq (o : Op E) r : Build_Op (op_key o) (op_op o) r = o -> r = op_ret o.
    Proof.
      destruct o as [k m r0]. simpl. intros Heq.
      apply (f_equal (fun o : Op E => Build_ThreadEvent (fst (op_key o)) (ResEv (snd (op_key o)) (op_op o) (op_ret o)))) in Heq.
      exact (res_ev_ret _ _ _ _ Heq).
    Qed.
  End Idx.

  Lemma NoDup_key_eq {A B : Type} (f : A -> B) l x y :
    NoDup (map f l) -> In x l -> In y l -> f x = f y -> x = y.
  Proof.
    induction l as [|a l IH]; intros Hnd Hx Hy Hf; [destruct Hx|].
    simpl in Hnd. apply NoDup_cons_iff in Hnd as [Hna Hnd].
    destruct Hx as [<- | Hx], Hy as [<- | Hy]; [reflexivity | | | exact (IH Hnd Hx Hy Hf)].
    - exfalso. apply Hna. rewrite Hf. apply in_map. exact Hy.
    - exfalso. apply Hna. rewrite <- Hf. apply in_map. exact Hx.
  Qed.

  Lemma NoDup_map_from {A B C : Type} (f : A -> B) (g : A -> C) l :
    NoDup (map f l) -> (forall x y, In x l -> In y l -> g x = g y -> f x = f y) -> NoDup (map g l).
  Proof.
    induction l as [|a l IH]; intros Hnd Hfg; simpl; [constructor|].
    simpl in Hnd. apply NoDup_cons_iff in Hnd as [Hna Hnd]. constructor.
    - intros Hin. apply in_map_iff in Hin as (y & Hy & Hyl). apply Hna.
      rewrite <- (Hfg y a (or_intror Hyl) (or_introl eq_refl) Hy). apply in_map. exact Hyl.
    - apply IH; [exact Hnd|]. intros x y Hx Hy. apply Hfg; right; assumption.
  Qed.

  (** ** Part 1: possibility runs *)

  Section Poss.
    Context {E : RelaxedSig.t}.
    Context (indep : relation (Sig.op (RelaxedSig.effect E))).
    Context (nu : list (Op E) -> Prop) (nu_nil : nu []).

    Abbreviation inv L := (inv_at (@PrefixView.sel E) L).
    Abbreviation res L := (res_at (@PrefixView.sel E) L).

    (** A step of a possibility run: a concrete event of the overlay trace,
        or an abstract VT-Invoke / VT-Return step.  The stamp of an
        abstract invocation of key [k] is [H k]. *)
    Inductive PStep : Type :=
    | CEv (e : ThreadEvent E)
    | AInv (k : CallKey E) (m : Sig.op (RelaxedSig.effect E))
    | ARet (k : CallKey E) (m : Sig.op (RelaxedSig.effect E)) (r : Sig.ar m).

    Definition cev (st : PStep) : list (ThreadEvent E) :=
      match st with CEv e => [e] | _ => [] end.

    Definition aev (st : PStep) : list (ThreadEvent E) :=
      match st with
      | CEv _ => []
      | AInv k m => [Build_ThreadEvent (fst k) (InvEv (snd k) m)]
      | ARet k m r => [Build_ThreadEvent (fst k) (ResEv (snd k) m r)]
      end.

    (** The concrete trace and the abstract trace [t] of a run. *)
    Definition conc (run : list PStep) : list (ThreadEvent E) := flat_map cev run.
    Definition abs (run : list PStep) : list (ThreadEvent E) := flat_map aev run.

    Lemma conc_app r1 r2 : conc (r1 ++ r2) = conc r1 ++ conc r2.
    Proof. apply flat_map_app. Qed.

    Lemma abs_app r1 r2 : abs (r1 ++ r2) = abs r1 ++ abs r2.
    Proof. apply flat_map_app. Qed.

    Section Local.
      Context (H : CallKey E -> nat).

      (** Local conditions of a step after the run [r1]. *)
      Definition ok (r1 : list PStep) (st : PStep) : Prop :=
        match st with
        | CEv e =>
            (* VS-Return: a concrete response follows the abstract one. *)
            forall k m (r : Sig.ar m), e = Build_ThreadEvent (fst k) (ResEv (snd k) m r) ->
              exists b, res (abs r1) b k m r
        | AInv k m =>
            (* The concrete invocation has happened. *)
            (exists i, inv (conc r1) i k m) /\
            (* Real time: above every operation that responded before the
               concrete invocation. *)
            (forall i j k' m' (r' : Sig.ar m'), inv (conc r1) i k m -> res (conc r1) j k' m' r' ->
               j < i -> H k' < H k) /\
            (* Def. I.2(3): above every earlier dependent invocation of the
               same thread, which is already abstractly invoked. *)
            (forall i j k' m', inv (conc r1) i k m -> inv (conc r1) j k' m' -> j < i ->
               fst k' = fst k -> ~ indep m' m -> (exists a, inv (abs r1) a k' m') /\ H k' < H k)
        | ARet k m r =>
            (exists a, inv (abs r1) a k m) /\ (forall b m' (r' : Sig.ar m'), ~ res (abs r1) b k m' r')
        end.

      (** The side condition of VT-Invoke / VT-Return: the extended abstract
          trace has a timestamp-ordered witness. *)
      Definition side (r1 : list PStep) (st : PStep) : Prop :=
        match st with
        | CEv _ => True
        | _ => exists w, PrefixView.lin_h nu H (abs (r1 ++ [st])) w
        end.

      Definition LValid (run : list PStep) : Prop :=
        forall r1 st r2, run = r1 ++ st :: r2 -> ok r1 st.

      Definition Valid (run : list PStep) : Prop :=
        forall r1 st r2, run = r1 ++ st :: r2 -> ok r1 st /\ side r1 st.

      Lemma LValid_prefix r1 r2 : LValid (r1 ++ r2) -> LValid r1.
      Proof.
        intros HV a st b ->. apply (HV a st (b ++ r2)). rewrite <- app_assoc. reflexivity.
      Qed.

      Lemma Valid_prefix r1 r2 : Valid (r1 ++ r2) -> Valid r1.
      Proof.
        intros HV a st b ->. apply (HV a st (b ++ r2)). rewrite <- app_assoc. reflexivity.
      Qed.

      Lemma Valid_LValid run : Valid run -> LValid run.
      Proof. intros HV r1 st r2 Hr. exact (proj1 (HV r1 st r2 Hr)). Qed.

      (** Checking the local conditions step by step. *)
      Lemma LValid_nil : LValid [].
      Proof. intros r1 st r2 Heq. destruct r1; discriminate. Qed.

      Lemma LValid_snoc run st : LValid run -> ok run st -> LValid (run ++ [st]).
      Proof.
        intros HV Hok r1 st' r2 Heq. destruct r2 as [|x r2 _] using rev_ind.
        - apply app_inj_tail in Heq as [-> ->]. exact Hok.
        - apply (HV r1 st' r2). rewrite app_comm_cons, app_assoc in Heq.
          apply app_inj_tail in Heq as [-> _]. reflexivity.
      Qed.

      Fixpoint okall (pre rest : list PStep) : Prop :=
        match rest with
        | [] => True
        | st :: rest' => ok pre st /\ okall (pre ++ [st]) rest'
        end.

      Lemma okall_LValid pre rest : LValid pre -> okall pre rest -> LValid (pre ++ rest).
      Proof.
        revert pre. induction rest as [|st rest IH]; intros pre HV Hall; [rewrite app_nil_r; exact HV|].
        destruct Hall as [Hok Hall].
        replace (pre ++ st :: rest) with ((pre ++ [st]) ++ rest) by (rewrite <- app_assoc; reflexivity).
        exact (IH _ (LValid_snoc _ _ HV Hok) Hall).
      Qed.

      (** *** Locating steps *)

      Lemma abs_inv_step run a k m : inv (abs run) a k m -> exists r1 r2, run = r1 ++ AInv k m :: r2.
      Proof.
        intros Hi. apply inv_In in Hi. apply in_flat_map in Hi as (st & Hst & Hin).
        destruct st as [e | k' m' | k' m' r']; simpl in Hin.
        - destruct Hin.
        - destruct Hin as [Heq | []]. apply inv_ev_inj in Heq as [-> ->].
          exact (in_split _ _ Hst).
        - destruct Hin as [Heq | []]. apply (f_equal (te_ev E)) in Heq. discriminate.
      Qed.

      Lemma abs_res_step run b k m (r : Sig.ar m) : res (abs run) b k m r -> exists r1 r2, run = r1 ++ ARet k m r :: r2.
      Proof.
        intros Hj. apply res_In in Hj. apply in_flat_map in Hj as (st & Hst & Hin).
        destruct st as [e | k' m' | k' m' r']; simpl in Hin.
        - destruct Hin.
        - destruct Hin as [Heq | []]. apply (f_equal (te_ev E)) in Heq. discriminate.
        - destruct Hin as [Heq | []]. pose proof (res_ev_inj _ _ _ _ _ _ Heq) as [-> ->].
          apply res_ev_ret in Heq as ->. exact (in_split _ _ Hst).
      Qed.

      Lemma conc_res_step run j k m (r : Sig.ar m) :
        res (conc run) j k m r -> exists r1 r2, run = r1 ++ CEv (Build_ThreadEvent (fst k) (ResEv (snd k) m r)) :: r2.
      Proof.
        intros Hj. apply res_In in Hj. apply in_flat_map in Hj as (st & Hst & Hin).
        destruct st as [e | k' m' | k' m' r']; simpl in Hin; [|destruct Hin|destruct Hin].
        destruct Hin as [-> | []]. exact (in_split _ _ Hst).
      Qed.

      (** An abstract invocation follows the concrete one. *)
      Lemma abs_inv_conc run a k m : LValid run -> inv (abs run) a k m -> exists i, inv (conc run) i k m.
      Proof.
        intros HV Ha. destruct (abs_inv_step _ _ _ _ Ha) as (r1 & r2 & ->).
        destruct (HV r1 _ r2 eq_refl) as ((i & Hi) & _). exists i.
        rewrite conc_app. exact (inv_app_l _ _ _ _ _ Hi).
      Qed.

      (** A concrete response follows the abstract one. *)
      Lemma conc_res_abs run j k m (r : Sig.ar m) : LValid run -> res (conc run) j k m r -> exists b, res (abs run) b k m r.
      Proof.
        intros HV Hj. destruct (conc_res_step _ _ _ _ _ Hj) as (r1 & r2 & ->).
        destruct (HV r1 _ r2 eq_refl _ _ _ eq_refl) as (b & Hb). exists b.
        rewrite abs_app. exact (res_app_l _ _ _ _ _ _ Hb).
      Qed.

      (** A concretely completed operation has an abstract invocation. *)
      Lemma ainv_of_cres run j k m (r : Sig.ar m) :
        LValid run -> res (conc run) j k m r -> exists r1 r2, run = r1 ++ AInv k m :: r2.
      Proof.
        intros HV Hj. destruct (conc_res_abs _ _ _ _ _ HV Hj) as (b & Hb).
        destruct (abs_res_step _ _ _ _ _ Hb) as (r1 & r2 & Hrun).
        destruct (HV r1 _ r2 Hrun) as ((a & Ha) & _).
        destruct (abs_inv_step _ _ _ _ Ha) as (q1 & q2 & ->).
        exists q1, (q2 ++ ARet k m r :: r2). rewrite Hrun, <- app_assoc. reflexivity.
      Qed.

      (** *** Witnesses *)

      Lemma valid_wit run : Valid run -> exists w, PrefixView.lin_h nu H (abs run) w.
      Proof.
        induction run as [|st run IH] using rev_ind; intros HV.
        - exists []. split; [exact nu_nil|]. split; [constructor|]. split; [intros o []|].
          split; [|intros o o' []]. intros j k m r (x & Hx & _). destruct j; discriminate.
        - destruct (HV run st [] eq_refl) as [_ Hside].
          destruct st as [e | k m | k m r]; [|exact Hside | exact Hside].
          rewrite abs_app. simpl. rewrite app_nil_r. exact (IH (Valid_prefix _ _ HV)).
      Qed.

      (** The witness of the abstract trace is a witness of the concrete
          trace. *)
      Lemma wit_transfer run w : LValid run -> PrefixView.lin_h nu H (abs run) w -> PrefixView.lin_h nu H (conc run) w.
      Proof.
        intros HV (Hnu & Hnd & Hin & Hres & Hord).
        split; [exact Hnu|]. split; [exact Hnd|]. split; [|split; [|exact Hord]].
        - intros o Ho. destruct (Hin o Ho) as [(a & Ha) Hr]. split; [exact (abs_inv_conc _ _ _ _ HV Ha)|].
          intros j r Hj. destruct (conc_res_abs _ _ _ _ _ HV Hj) as (b & Hb). exact (Hr b r Hb).
        - intros j k m r Hj. destruct (conc_res_abs _ _ _ _ _ HV Hj) as (b & Hb). exact (Hres b k m r Hb).
      Qed.

      Lemma conc_prefix run n : n <= length (conc run) -> exists r1 r2, run = r1 ++ r2 /\ conc r1 = firstn n (conc run).
      Proof.
        revert n. induction run as [|st run IH]; intros n Hn.
        - exists [], []. simpl in *. split; [reflexivity|]. rewrite firstn_nil. reflexivity.
        - destruct n as [|n]; [exists [], (st :: run); split; [reflexivity | rewrite firstn_O; reflexivity]|].
          destruct st as [e | k m | k m r]; simpl in Hn |- *.
          + destruct (IH n ltac:(lia)) as (r1 & r2 & -> & Hc).
            exists (CEv e :: r1), r2. split; [reflexivity|]. simpl. rewrite Hc. reflexivity.
          + destruct (IH (S n) Hn) as (r1 & r2 & -> & Hc).
            exists (AInv k m :: r1), r2. split; [reflexivity|]. exact Hc.
          + destruct (IH (S n) Hn) as (r1 & r2 & -> & Hc).
            exists (ARet k m r :: r1), r2. split; [reflexivity|]. exact Hc.
      Qed.

      (** *** The theorem *)

      Theorem poss_view_rt run :
        Valid run -> PrefixView.wf (conc run) -> PrefixView.complete (conc run) ->
        PrefixView.view_rt indep nu H (conc run).
      Proof.
        intros HV Hwf Hc. pose proof (Valid_LValid _ HV) as HL.
        (* The abstract invocation of a key invoked at index [j]. *)
        assert (Hstep : forall j k m, inv (conc run) j k m ->
                  exists r1 r2, run = r1 ++ AInv k m :: r2 /\ inv (conc r1) j k m /\ ok r1 (AInv k m)).
        { intros j k m Hj. destruct (Hc _ _ _ Hj) as (j2 & r & Hj2).
          destruct (ainv_of_cres _ _ _ _ _ HL Hj2) as (r1 & r2 & Hrun).
          pose proof (HL r1 _ r2 Hrun) as Hok. pose proof Hok as ((i0 & Hi0) & _).
          assert (Hi0' : inv (conc run) i0 k m) by (rewrite Hrun, conc_app; exact (inv_app_l _ _ _ _ _ Hi0)).
          pose proof (proj1 Hwf _ _ _ _ _ Hi0' Hj) as ->. eauto. }
        split; [split; [exact Hwf|split]|].
        - intros i j k k' op op' Hi Hj Hij Hth Hn.
          destruct (Hstep _ _ _ Hj) as (r1 & r2 & Hrun & Hj1 & _ & _ & Hpo).
          assert (Hi1 : inv (conc r1) i k op).
          { apply (inv_app_lt _ (conc (AInv k' op' :: r2))); [pose proof (inv_lt _ _ _ _ Hj1); lia|].
            rewrite <- conc_app, <- Hrun. exact Hi. }
          exact (proj2 (Hpo _ _ _ _ Hj1 Hi1 Hij Hth Hn)).
        - intros n Hn. destruct (conc_prefix run n Hn) as (r1 & r2 & Hrun & Hc1).
          rewrite Hrun in HV. pose proof (Valid_prefix _ _ HV) as HV1.
          destruct (valid_wit _ HV1) as (w & Hw). exists w. rewrite <- Hc1.
          exact (wit_transfer _ _ (Valid_LValid _ HV1) Hw).
        - intros i j k k' op op' r Hi Hj Hij.
          destruct (Hstep _ _ _ Hj) as (r1 & r2 & Hrun & Hj1 & _ & Hrt & _).
          assert (Hi1 : res (conc r1) i k op r).
          { apply (res_app_lt _ (conc (AInv k' op' :: r2))); [pose proof (inv_lt _ _ _ _ Hj1); lia|].
            rewrite <- conc_app, <- Hrun. exact Hi. }
          exact (Hrt _ _ _ _ _ Hj1 Hi1 Hij).
      Qed.

      Corollary poss_rel_lin run :
        Valid run -> PrefixView.wf (conc run) -> PrefixView.complete (conc run) ->
        rel_lin (@PrefixView.sel E) (conc run) indep nu.
      Proof.
        intros HV Hwf Hc. exact (PrefixView.view_rt_rel_lin indep nu H _ Hc (poss_view_rt _ HV Hwf Hc)).
      Qed.
    End Local.
  End Poss.

  Arguments PStep : clear implicits.

  (** ** Part 2: the [ViewLift] timeline discharges the side condition *)

  Section Timeline.
    Import ViewLift ViewLiftAdequacy.
    Context {E0 : Reg.Op.t} (P : @Params E0) (s0 : vl_state P).

    Abbreviation RS := (ViewLiftAdequacy.RS P).
    Abbreviation indepT := (RelaxedSig.semi_independent RS).
    Abbreviation nuT := (nu_P P s0).
    Abbreviation inv L := (inv_at (@PrefixView.sel RS) L).
    Abbreviation res L := (res_at (@PrefixView.sel RS) L).

    (** The stamps chosen by the possibility. *)
    Context (hk : CallKey RS -> positive).

    Definition HT (k : CallKey RS) : nat := Pos.to_nat (hk k).

    (** The abstractly completed operations of a run, in order, and their
        timeline entries. *)
    Definition rets (run : list (PStep RS)) : list (Op RS) :=
      flat_map (fun st => match st with ARet k m r => [Build_Op k m r] | _ => [] end) run.

    Definition ent_of (o : Op RS) : Ent :=
      @mkEnt E0 (fst (op_key o)) (op_op o) (op_ret o) (hk (op_key o)).

    Definition ents (run : list (PStep RS)) : list Ent := map ent_of (rets run).

    (** A timeline run: the local conditions, and the abstract responses
        with their stamps form a run of [VL P]. *)
    Definition TValid (run : list (PStep RS)) : Prop :=
      LValid indepT HT run /\ exists s, Run P s0 (ents run) s.

    Lemma rets_app r1 r2 : rets (r1 ++ r2) = rets r1 ++ rets r2.
    Proof. apply flat_map_app. Qed.

    Lemma ents_app r1 r2 : ents (r1 ++ r2) = ents r1 ++ ents r2.
    Proof. unfold ents. rewrite rets_app. apply map_app. Qed.

    Lemma rets_res run o : In o (rets run) -> exists b, res (abs run) b (op_key o) (op_op o) (op_ret o).
    Proof.
      intros Hin. apply in_flat_map in Hin as (st & Hst & Hin).
      destruct st as [e | k m | k m r]; simpl in Hin; [destruct Hin | destruct Hin|].
      destruct Hin as [<- | []]. simpl. apply In_res. apply in_flat_map.
      exists (ARet k m r). split; [exact Hst | left; reflexivity].
    Qed.

    Lemma res_rets run b k m (r : Sig.ar m) : res (abs run) b k m r -> In (Build_Op k m r) (rets run).
    Proof.
      intros Hb. destruct (abs_res_step _ _ _ _ _ Hb) as (r1 & r2 & ->).
      rewrite rets_app. apply in_or_app. right. left. reflexivity.
    Qed.

    Lemma rets_nodup run : LValid indepT HT run -> NoDup (map op_key (rets run)).
    Proof.
      induction run as [|st run IH] using rev_ind; intros HV; [constructor|].
      pose proof (IH (LValid_prefix _ _ _ _ HV)) as Hnd.
      pose proof (HV run st [] eq_refl) as Hok.
      rewrite rets_app. destruct st as [e | k m | k m r]; simpl; try (rewrite app_nil_r; exact Hnd).
      rewrite map_app. simpl. apply (Permutation_NoDup (Permutation_cons_append _ _)).
      constructor; [|exact Hnd]. intros Hin. apply in_map_iff in Hin as (o & Hk & Ho).
      destruct (rets_res _ _ Ho) as (b & Hb). rewrite Hk in Hb.
      exact (proj2 Hok b _ _ Hb).
    Qed.

    Lemma run_prefix R1 R2 s : Run P s0 (R1 ++ R2) s -> exists s', Run P s0 R1 s'.
    Proof.
      revert s. induction R2 as [|e R2 IH] using rev_ind; intros s HR.
      - rewrite app_nil_r in HR. eauto.
      - rewrite app_assoc in HR. remember ((R1 ++ R2) ++ [e]) as l eqn:Hl.
        destruct HR as [|R s1 e1 s2 HR Hst].
        + destruct (R1 ++ R2); discriminate.
        + apply app_inj_tail in Hl as [-> _]. exact (IH _ HR).
    Qed.

    (** A timeline entry stands for the operation that the possibility
        completed at the same position. *)
    Definition relab (run : list (PStep RS)) (w : WE P) : Op RS :=
      match nth_error (rets run) (w_i P w) with Some o => o | None => to_op P (w_i P w) (w_e P w) end.

    Lemma relab_eq run w o : nth_error (rets run) (w_i P w) = Some o -> relab run w = o.
    Proof. intros Hn. unfold relab. rewrite Hn. reflexivity. Qed.

    Lemma chain_relab run W s :
      (forall w, In w W -> exists o, nth_error (rets run) (w_i P w) = Some o /\ w_e P w = ent_of o) ->
      Chain P s (map (wproj P) W) -> Chain P s (map (fun w => (relab run w, w_st P w)) W).
    Proof.
      revert s. induction W as [|a W IH]; intros s He Hc; simpl; [constructor|].
      unfold wproj in Hc. simpl in Hc.
      inversion Hc as [|s1 o1 s2 W2 Hsp Hc2]; subst.
      destruct (He a (or_introl eq_refl)) as (o & Hn & Hea).
      rewrite (relab_eq _ _ _ Hn). constructor.
      - rewrite Hea in Hsp. exact Hsp.
      - apply IH; [intros w Hw; apply He; right; exact Hw | exact Hc2].
    Qed.

    Lemma nuT_nil : nuT [].
    Proof. exists []. split; [constructor | reflexivity]. Qed.

    Theorem timeline_wit run : TValid run -> exists w, PrefixView.lin_h nuT HT (abs run) w.
    Proof.
      intros (HL & s & HR). destruct (run_witness P s0 _ _ HR) as (W & HW).
      pose proof (rets_nodup _ HL) as Hnd.
      assert (He : forall w, In w W -> exists o, nth_error (rets run) (w_i P w) = Some o /\ w_e P w = ent_of o).
      { intros w Hw. pose proof (wi_ent _ _ _ _ _ HW w Hw) as Hn. unfold ents in Hn.
        rewrite nth_error_map in Hn. destruct (nth_error (rets run) (w_i P w)) as [o|]; simpl in Hn; [|discriminate].
        injection Hn as Hn. exists o. auto. }
      exists (map (relab run) W). split; [|split; [|split; [|split]]].
      - exists (map (fun w => (relab run w, w_st P w)) W). split.
        + exact (chain_relab _ _ _ He (wi_chain _ _ _ _ _ HW)).
        + rewrite map_map. reflexivity.
      - rewrite map_map. apply (NoDup_map_from (w_i P) _ W (wi_nd _ _ _ _ _ HW)).
        intros x y Hx Hy Hk.
        destruct (He x Hx) as (ox & Hnx & _). destruct (He y Hy) as (oy & Hny & _).
        rewrite (relab_eq _ _ _ Hnx), (relab_eq _ _ _ Hny) in Hk.
        apply (proj1 (NoDup_nth_error _) Hnd).
        + rewrite length_map. exact (nth_some_lt _ _ _ Hnx).
        + rewrite !nth_error_map, Hnx, Hny. simpl. f_equal. exact Hk.
      - intros o' Ho'. apply in_map_iff in Ho' as (w & <- & Hw).
        destruct (He w Hw) as (o & Hn & _). rewrite (relab_eq _ _ _ Hn).
        pose proof (nth_error_In _ _ Hn) as Hin. split.
        + destruct (rets_res _ _ Hin) as (b & Hb). destruct (abs_res_step _ _ _ _ _ Hb) as (r1 & r2 & Hrun).
          destruct (HL r1 _ r2 Hrun) as ((a & Ha) & _). exists a.
          rewrite Hrun, abs_app. exact (inv_app_l _ _ _ _ _ Ha).
        + intros j r Hj. apply op_ret_eq.
          exact (NoDup_key_eq op_key _ _ _ Hnd (res_rets _ _ _ _ _ Hj) Hin eq_refl).
      - intros j k m r Hj. destruct (In_nth_error _ _ (res_rets _ _ _ _ _ Hj)) as (i & Hi).
        assert (Hi' : nth_error (ents run) i = Some (ent_of (Build_Op k m r))).
        { unfold ents. rewrite nth_error_map, Hi. reflexivity. }
        destruct (wi_all _ _ _ _ _ HW i _ Hi') as (w & Hw & Hwi).
        apply in_map_iff. exists w. split; [|exact Hw]. apply relab_eq. rewrite Hwi. exact Hi.
      - intros o1 o2 Ho1 Ho2 Hlt.
        apply in_map_iff in Ho1 as (w1 & <- & Hw1). apply in_map_iff in Ho2 as (w2 & <- & Hw2).
        apply before_map. apply (sorted_before P W w1 w2 (wi_sort _ _ _ _ _ HW) Hw1 Hw2).
        destruct (He w1 Hw1) as (o1 & Hn1 & He1). destruct (He w2 Hw2) as (o2 & Hn2 & He2).
        rewrite (relab_eq _ _ _ Hn1), (relab_eq _ _ _ Hn2) in Hlt.
        unfold ltw, ltx, wh. left. rewrite He1, He2. simpl. apply Pos2Nat.inj_lt. exact Hlt.
    Qed.

    (** Every step of a timeline run satisfies the side condition. *)
    Theorem timeline_valid run : TValid run -> Valid indepT nuT HT run.
    Proof.
      intros (HL & s & HR) r1 st r2 Hrun. split; [exact (HL _ _ _ Hrun)|].
      assert (HT1 : TValid (r1 ++ [st])).
      { assert (Hr : run = (r1 ++ [st]) ++ r2) by (rewrite Hrun, <- app_assoc; reflexivity).
        rewrite Hr in HL, HR. split; [exact (LValid_prefix _ _ _ _ HL)|].
        rewrite ents_app in HR. exact (run_prefix _ _ _ HR). }
      destruct st as [e | k m | k m r]; [exact I | exact (timeline_wit _ HT1) | exact (timeline_wit _ HT1)].
    Qed.

    Theorem timeline_view_rt run :
      TValid run -> PrefixView.wf (conc run) -> PrefixView.complete (conc run) ->
      PrefixView.view_rt indepT nuT HT (conc run).
    Proof.
      intros HV Hwf Hc. exact (poss_view_rt indepT nuT nuT_nil HT run (timeline_valid run HV) Hwf Hc).
    Qed.

    Corollary timeline_rel_lin run :
      TValid run -> PrefixView.wf (conc run) -> PrefixView.complete (conc run) ->
      rel_lin (@PrefixView.sel RS) (conc run) indepT nuT.
    Proof.
      intros HV Hwf Hc. exact (poss_rel_lin indepT nuT nuT_nil HT run (timeline_valid run HV) Hwf Hc).
    Qed.
  End Timeline.
End ViewPossibility.
