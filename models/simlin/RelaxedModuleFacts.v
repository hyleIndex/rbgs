(** Instrumented executions of the tagged module semantics, and the
    scheduling facts they provide.

    [module_step_tagged] forgets which overlay call issued an emitted
    underlay event and in which order events were enqueued.  The
    instrumented semantics below records both: every enqueued event gets
    a fresh identifier (its position in the global enqueue log), and every
    overlay invocation leaves a record ([InvRec]) of the local trace that
    its method body produced.  [instrument] shows that every tagged
    execution has an instrumented counterpart with the same observable
    trace, and [iinv_reach] that every reachable instrumented state
    satisfies the invariant [IInv].  The fields of [IInv] and the lemmas
    of Section [Facts] are the facts a composition proof needs:

    - [ii_order]: of two events enqueued in this order and related by
      (F1)--(F3) (same thread, [~ tagged_can_cross]), the first is emitted
      first;
    - [ii_ret_after]: every event of a call is emitted before the call
      returns;
    - [ii_emitted_after]: and after the call was invoked;
    - [complete_all_emitted]: at an empty queue every enqueued event has
      been emitted;
    - [complete_all_returned]: when no call is active, every recorded call
      has returned, with its recorded result;
    - [record_ids_ordered], [record_key_unique], [record_invkey_unique]:
      the log is laid out call by call, and overlay and underlay keys
      identify their call.

    Section [LocalTraces] adds two facts about a single method trace:
    invocation keys identify positions ([local_inv_unique]) and every
    response answers an invocation of the same trace
    ([produced_response_invoked]). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Sorting.Sorted.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.

Import ListNotations.


Module RelaxedModuleFacts.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.

  (** ** Generic list facts *)

  Section ListFacts.
    Context {A : Type}.

    Fixpoint number (n : nat) (l : list A) : list (nat * A) :=
      match l with
      | [] => []
      | x :: l' => (n, x) :: number (S n) l'
      end.

    Lemma number_length n l : length (number n l) = length l.
    Proof. revert n; induction l as [|a l IH]; cbn; intros n; [reflexivity | f_equal; apply IH]. Qed.

    Lemma number_snd n l : map snd (number n l) = l.
    Proof. revert n; induction l as [|a l IH]; cbn; intros n; [reflexivity | f_equal; apply IH]. Qed.

    Lemma in_number n l i x :
      In (i, x) (number n l) -> n <= i < n + length l /\ nth_error l (i - n) = Some x.
    Proof.
      revert n; induction l as [|a l IH]; cbn; intros n H; [contradiction |].
      destruct H as [H | H].
      - inversion H; subst. split; [lia |]. rewrite Nat.sub_diag. reflexivity.
      - destruct (IH (S n) H) as [Hr Hn]. split; [lia |].
        replace (i - n) with (S (i - S n)) by lia. exact Hn.
    Qed.

    Lemma in_number_fst n l x : In x (number n l) -> n <= fst x < n + length l.
    Proof. destruct x as [i y]. intros H. apply in_number in H. cbn. lia. Qed.

    Lemma nth_error_number n l j :
      nth_error (number n l) j = option_map (fun x => (n + j, x)) (nth_error l j).
    Proof.
      revert n j; induction l as [|a l IH]; intros n j; destruct j; cbn; auto.
      - rewrite Nat.add_0_r. reflexivity.
      - rewrite IH. destruct (nth_error l j); cbn; auto. do 2 f_equal. lia.
    Qed.

    Lemma number_sorted n l : StronglySorted (fun x y => fst x < fst y) (number n l).
    Proof.
      revert n; induction l as [|a l IH]; cbn; intros n; constructor; [apply IH |].
      apply Forall_forall. intros [i y] Hy. apply in_number in Hy. cbn. lia.
    Qed.

    Lemma ss_app (R : A -> A -> Prop) l1 l2 :
      StronglySorted R l1 -> StronglySorted R l2 ->
      (forall x y, In x l1 -> In y l2 -> R x y) ->
      StronglySorted R (l1 ++ l2).
    Proof.
      induction 1 as [|a l1 Hs IH Hf]; intros H2 Hxy; cbn; [exact H2 |].
      constructor.
      - apply IH; [exact H2 |]. intros x y Hx Hy. apply Hxy; [right |]; assumption.
      - apply Forall_app. split; [exact Hf |].
        apply Forall_forall. intros y Hy. apply Hxy; [left; reflexivity | exact Hy].
    Qed.

    Lemma ss_tail (R : A -> A -> Prop) l1 l2 :
      StronglySorted R (l1 ++ l2) -> StronglySorted R l2.
    Proof.
      induction l1 as [|a l1 IH]; cbn; intros H; [exact H |].
      apply IH. inversion H; assumption.
    Qed.

    Lemma ss_after (R : A -> A -> Prop) pre y post x :
      StronglySorted R (pre ++ y :: post) -> In x post -> R y x.
    Proof.
      intros H Hx. apply ss_tail in H. inversion H as [|? ? _ Hf]; subst.
      rewrite Forall_forall in Hf. apply Hf, Hx.
    Qed.

    Lemma ss_sub (R : A -> A -> Prop) pre y post :
      StronglySorted R (pre ++ y :: post) -> StronglySorted R (pre ++ post).
    Proof.
      induction pre as [|a pre IH]; cbn; intros H.
      - inversion H; assumption.
      - inversion H as [|? ? Hs Hf]; subst. constructor; [apply IH, Hs |].
        rewrite Forall_forall in *. intros z Hz. apply Hf.
        apply in_app_or in Hz as [Hz|Hz]; apply in_or_app; [left | right; right]; exact Hz.
    Qed.

    Lemma app_snoc_cases (pre : list A) (r : A) (post invs : list A) (r' : A) :
      pre ++ r :: post = invs ++ [r'] ->
      (post = [] /\ pre = invs /\ r = r') \/
      (exists post', post = post' ++ [r'] /\ invs = pre ++ r :: post').
    Proof.
      intros H. destruct post as [| p post] using rev_ind.
      - left. apply app_inj_tail in H as [H1 H2]. auto.
      - right. exists post. split.
        + rewrite app_comm_cons, app_assoc in H. apply app_inj_tail in H as [_ H2]. subst. reflexivity.
        + rewrite app_comm_cons, app_assoc in H. apply app_inj_tail in H as [H1 _]. auto.
    Qed.

    Lemma in_split_two (l : list A) x y :
      In x l -> In y l -> x <> y ->
      (exists l1 l2 l3, l = l1 ++ x :: l2 ++ y :: l3) \/
      (exists l1 l2 l3, l = l1 ++ y :: l2 ++ x :: l3).
    Proof.
      intros Hx Hy Hne. destruct (in_split _ _ Hy) as (l1 & l3 & ->).
      apply in_app_or in Hx as [Hx | [Hx | Hx]].
      - left. destruct (in_split _ _ Hx) as (a & b & ->). exists a, b, l3. rewrite <- app_assoc. reflexivity.
      - exfalso. apply Hne. symmetry. exact Hx.
      - right. destruct (in_split _ _ Hx) as (a & b & ->). exists l1, a, b. reflexivity.
    Qed.

  End ListFacts.

  Section NoDupFacts.
    Context {A : Type}.

    Lemma nodup_snoc (l : list A) a : NoDup l -> ~ In a l -> NoDup (l ++ [a]).
    Proof.
      intros Hnd Ha. apply NoDup_app; [exact Hnd | constructor; [intros [] | constructor] |].
      intros b Hb [<- | []]. exact (Ha Hb).
    Qed.

    Lemma nodup_map_inj {B : Type} (f : A -> B) l a b :
      NoDup (map f l) -> In a l -> In b l -> f a = f b -> a = b.
    Proof.
      induction l as [|c l IH]; cbn; intros Hnd Ha Hb Hf; [contradiction |].
      inversion Hnd as [|? ? Hnin Hnd']; subst.
      destruct Ha as [<- | Ha], Hb as [<- | Hb]; auto.
      - exfalso. apply Hnin. rewrite Hf. apply in_map. exact Hb.
      - exfalso. apply Hnin. rewrite <- Hf. apply in_map. exact Ha.
    Qed.

    Lemma nodup_app_disj {C : Type} (l1 l2 : list C) x : NoDup (l1 ++ l2) -> In x l1 -> In x l2 -> False.
    Proof.
      induction l1 as [|a l1 IH]; cbn; intros Hnd H1 H2; [contradiction |].
      inversion Hnd as [|? ? Hnin Hnd']; subst.
      destruct H1 as [<- | H1].
      - apply Hnin. apply in_or_app. right. exact H2.
      - exact (IH Hnd' H1 H2).
    Qed.

    Lemma nodup_flat_map_in {B : Type} (f : A -> list B) l a b k :
      NoDup (flat_map f l) -> In a l -> In b l -> In k (f a) -> In k (f b) -> a = b.
    Proof.
      induction l as [|c l IH]; cbn; intros Hnd Ha Hb Hka Hkb; [contradiction |].
      destruct Ha as [<- | Ha], Hb as [<- | Hb]; [reflexivity | | |].
      - exfalso. apply (nodup_app_disj _ _ k Hnd Hka). apply in_flat_map. exists b. auto.
      - exfalso. apply (nodup_app_disj _ _ k Hnd Hkb). apply in_flat_map. exists a. auto.
      - apply IH; auto. eapply NoDup_app_remove_l; exact Hnd.
    Qed.
  End NoDupFacts.

  (** ** Facts about local (single-method) traces *)

  Section LocalTraces.
    Context {E : RelaxedSig.t} {R : Type}.

    Lemma resolve_store_back (h : RelaxedSig.handle E) op ret (H H' : FutureStore E) :
      resolve_store h op ret H H' ->
      forall e, In e H' -> In e H \/ e = Build_FutureEntry h (Resolved op ret).
    Proof.
      induction 1 as [tail | h' cell H H' Hneq Hres IH]; intros e He; cbn in *.
      - destruct He as [<- | He]; [right; reflexivity | left; right; exact He].
      - destruct He as [<- | He]; [left; left; reflexivity |].
        destruct (IH e He) as [H1 | H1]; [left; right; exact H1 | right; exact H1].
    Qed.

    Lemma invocation_keys_inv (a : ThreadEvent E) l h op :
      te_ev E a = InvEv h op -> invocation_keys (a :: l) = (te_tid E a, h) :: invocation_keys l.
    Proof. intros He. cbn. rewrite He. reflexivity. Qed.

    Lemma invocation_keys_tail (a : ThreadEvent E) l :
      NoDup (invocation_keys (a :: l)) -> NoDup (invocation_keys l).
    Proof. cbn. destruct (te_ev E a); intros H; [inversion H; assumption | exact H]. Qed.

    Lemma invocation_keys_cons_in (a : ThreadEvent E) l k :
      In k (invocation_keys l) -> In k (invocation_keys (a :: l)).
    Proof. intros H. cbn. destruct (te_ev E a); [right |]; exact H. Qed.

    Lemma inv_key_in (l : list (ThreadEvent E)) j ev h op :
      nth_error l j = Some ev -> te_ev E ev = InvEv h op -> In (te_tid E ev, h) (invocation_keys l).
    Proof.
      revert j; induction l as [| a l IH]; intros j Hj Hev; [destruct j; discriminate |].
      destruct j as [| j]; cbn in Hj.
      - injection Hj as <-. rewrite (invocation_keys_inv _ _ _ _ Hev). left. reflexivity.
      - apply invocation_keys_cons_in. eapply IH; eauto.
    Qed.

    (** Invocation keys of a local trace identify their position. *)
    Lemma local_inv_unique (l : list (ThreadEvent E)) j j' ev ev' h op op' :
      NoDup (invocation_keys l) ->
      nth_error l j = Some ev -> nth_error l j' = Some ev' ->
      te_ev E ev = InvEv h op -> te_ev E ev' = InvEv h op' -> te_tid E ev = te_tid E ev' ->
      j = j'.
    Proof.
      revert j j'; induction l as [| a l IH]; intros j j' Hnd Hj Hj' He He' Ht;
        [destruct j; discriminate |].
      destruct j as [| j], j' as [| j']; cbn in Hj, Hj'.
      - reflexivity.
      - injection Hj as <-. rewrite (invocation_keys_inv _ _ _ _ He) in Hnd.
        inversion Hnd as [| ? ? Hnin _]. exfalso. apply Hnin. rewrite Ht. eapply inv_key_in; eauto.
      - injection Hj' as <-. rewrite (invocation_keys_inv _ _ _ _ He') in Hnd.
        inversion Hnd as [| ? ? Hnin _]. exfalso. apply Hnin. rewrite <- Ht. eapply inv_key_in; eauto.
      - f_equal. apply (IH j j'); auto. eapply invocation_keys_tail; exact Hnd.
    Qed.

    (** A response of a local trace answers an invocation of the same
        trace. *)
    Lemma tagged_execution_response_source t (c : ProgramConfig E R) trace c' :
      program_execution_tagged t c trace c' ->
      forall j m h op ret, nth_error trace j = Some m -> te_ev E (untag m) = ResEv h op ret ->
        (exists op', pending_at h op' (pc_futures c)) \/
        In (t, h) (invocation_keys (map untag trace)).
    Proof.
      induction 1 as [c | c1 c2 c3 trace Hstep Hexec IH | c1 c2 c3 m0 trace Hstep Hexec IH];
        intros j m h op ret Hj Hm.
      - destruct j; discriminate.
      - destruct (IH j m h op ret Hj Hm) as [(op' & Hp) | Hk]; [left | right; exact Hk].
        exists op'. inversion Hstep; subst; cbn in *; exact Hp.
      - destruct j as [| j]; cbn in Hj.
        + injection Hj as <-. left. inversion Hstep; subst; cbn in *; try discriminate.
          * apply (f_equal event_handle) in Hm. cbn in Hm. subst.
            exists op0. eapply resolve_store_pending; eauto.
          * apply (f_equal event_handle) in Hm. cbn in Hm. subst.
            exists op0. eapply resolve_store_pending; eauto.
        + destruct (IH j m h op ret Hj Hm) as [(op' & Hp) | Hk].
          * inversion Hstep; subst; cbn in *.
            -- destruct Hp as [He | Hp]; [right | left; exists op'; exact Hp].
               apply (f_equal (fe_handle E)) in He. cbn in He. subst. left. reflexivity.
            -- destruct Hp as [He | Hp]; [right | left; exists op'; exact Hp].
               apply (f_equal (fe_handle E)) in He. cbn in He. subst. left. reflexivity.
            -- left. exists op'. destruct (resolve_store_back _ _ _ _ _ Hresolve _ Hp) as [H1 | H1];
                 [exact H1 | discriminate].
            -- left. exists op'. destruct (resolve_store_back _ _ _ _ _ Hresolve _ Hp) as [H1 | H1];
                 [exact H1 | discriminate].
          * right. cbn [map]. apply invocation_keys_cons_in. exact Hk.
    Qed.

    Lemma produced_response_invoked t p trace (r : R) j m h op ret :
      program_produces_tagged t p trace r ->
      nth_error trace j = Some m -> te_ev E (untag m) = ResEv h op ret ->
      In (t, h) (invocation_keys (map untag trace)).
    Proof.
      intros (c' & Hexec & _) Hj Hm.
      destruct (tagged_execution_response_source _ _ _ _ Hexec j m h op ret Hj Hm)
        as [(op' & Hp) | Hk]; [| exact Hk].
      destruct Hp.
    Qed.
  End LocalTraces.


  (** ** The instrumented semantics *)

  Section Instrumented.
    Context {E F : RelaxedSig.t}.
    Context (VE : RelaxedLTSSpec.LTS E).
    Context (M : RelaxedModuleImpl E F).

    Local Abbreviation IEvent := (nat * TaggedScheduledEvent E F)%type.

    (** The record left by an overlay invocation: the call, the result the
        method body committed to, the identifier of its first enqueued
        event, the position of the invocation in the trace, and the local
        trace of the body. *)
    Record InvRec : Type := {
      ir_key : CallKey F;
      ir_op : Sig.op (RelaxedSig.effect F);
      ir_ret : Sig.ar ir_op;
      ir_start : nat;
      ir_pos : nat;
      ir_trace : list (TaggedEvent E);
    }.

    Definition ir_block (r : InvRec) : list IEvent :=
      number (ir_start r) (schedule_trace_tagged (ir_key r) (ir_trace r)).

    Record IConfig : Type := {
      ic_state : RelaxedLTSSpec.State VE;
      ic_calls : CallPool F;
      ic_queue : list IEvent;
      ic_used : list (CallKey E);
      ic_log : list IEvent;
      ic_invs : list InvRec;
    }.

    Inductive ITraceEvent : Type :=
    | IUnder (x : IEvent)
    | IOver (ev : ThreadEvent F).

    Definition ierase (e : ITraceEvent) : ModuleEvent E F :=
      match e with
      | IUnder x => UnderlayEvent (untag (ts_event (snd x)))
      | IOver ev => OverlayEvent ev
      end.

    Inductive iselect (cand : IEvent) : list IEvent -> list IEvent -> Prop :=
    | iselect_here suffix : iselect cand (cand :: suffix) suffix
    | iselect_next earlier q q'
        (Hcross : tagged_can_cross (ts_event (snd earlier)) (ts_event (snd cand)))
        (Hsel : iselect cand q q') :
        iselect cand (earlier :: q) (earlier :: q').

    Inductive istep (n : nat) : ITraceEvent -> IConfig -> IConfig -> Prop :=
    | istep_invoke t h op q pool queue used log invs trace ret
        (Hfresh_call : call_fresh (t, h) pool)
        (Hmethod : program_produces_tagged t (M op t) trace ret)
        (Hfresh_trace : trace_fresh used (map untag trace)) :
        istep n (IOver (Build_ThreadEvent t (@InvEv F h op)))
          (Build_IConfig q pool queue used log invs)
          (Build_IConfig q (Build_CallEntry t h (ActiveCall op ret) :: pool)
             (queue ++ ir_block (Build_InvRec (t, h) op ret (length log) n trace))
             (used ++ invocation_keys (map untag trace))
             (log ++ ir_block (Build_InvRec (t, h) op ret (length log) n trace))
             (invs ++ [Build_InvRec (t, h) op ret (length log) n trace]))
    | istep_underlay cand q q' pool queue queue' used log invs
        (Hsel : iselect cand queue queue')
        (Hlts : RelaxedLTSSpec.Step VE (untag (ts_event (snd cand))) q q') :
        istep n (IUnder cand)
          (Build_IConfig q pool queue used log invs)
          (Build_IConfig q' pool queue' used log invs)
    | istep_return t h op ret q pool pool' queue used log invs
        (Hfinish : finish_call t h op ret pool pool')
        (Hdone : owner_done_tagged (t, h) (map snd queue)) :
        istep n (IOver (Build_ThreadEvent t (@ResEv F h op ret)))
          (Build_IConfig q pool queue used log invs)
          (Build_IConfig q pool' queue used log invs).

    Inductive iexec (c0 : IConfig) : list ITraceEvent -> IConfig -> Prop :=
    | iexec_refl : iexec c0 [] c0
    | iexec_snoc tr c ev c'
        (Hexec : iexec c0 tr c)
        (Hstep : istep (length tr) ev c c') :
        iexec c0 (tr ++ [ev]) c'.

    Definition iinitial (q : RelaxedLTSSpec.State VE) : IConfig :=
      Build_IConfig q [] [] [] [] [].

    (** *** Every tagged execution can be instrumented *)

    Definition irel (ic : IConfig) (c : TaggedModuleConfig VE) : Prop :=
      tm_lts_state c = ic_state ic /\ tm_calls c = ic_calls ic /\
      tm_queue c = map snd (ic_queue ic) /\ tm_used_underlay c = ic_used ic.

    Lemma iselect_lift candidate queue queue' :
      select_frontier_tagged candidate queue queue' ->
      forall iq, map snd iq = queue ->
      exists cand iq', snd cand = candidate /\ iselect cand iq iq' /\ map snd iq' = queue'.
    Proof.
      induction 1 as [suffix | earlier queue queue' Hcross Hsel IH]; intros iq Hiq.
      - destruct iq as [| x iq]; [discriminate |]. cbn in Hiq. injection Hiq as Hx Htl.
        exists x, iq. split; [exact Hx |]. split; [apply iselect_here | exact Htl].
      - destruct iq as [| x iq]; [discriminate |]. cbn in Hiq. injection Hiq as Hx Htl.
        destruct (IH iq Htl) as (cand & iq' & Hc & Hs & He).
        exists cand, (x :: iq'). split; [exact Hc |]. split.
        + apply iselect_next; [rewrite Hx, Hc; exact Hcross | exact Hs].
        + cbn. rewrite Hx, He. reflexivity.
    Qed.

    Lemma istep_lift n ev c c' ic :
      module_step_tagged VE M ev c c' -> irel ic c ->
      exists iev ic', istep n iev ic ic' /\ ierase iev = ev /\ irel ic' c'.
    Proof.
      intros Hstep Hrel.
      destruct c as [q0 pool0 queue0 used0].
      destruct ic as [qs pool iq used log invs].
      destruct Hrel as (Hs & Hc & Hq & Hu). cbn in Hs, Hc, Hq, Hu. subst.
      inversion Hstep; subst.
      - eexists (IOver _), _. split.
        + eapply istep_invoke; eauto.
        + split; [reflexivity |]. unfold irel; cbn. split; [reflexivity |].
          split; [reflexivity |]. split; [| reflexivity].
          rewrite map_app. f_equal. unfold ir_block. symmetry. apply number_snd.
      - destruct (iselect_lift _ _ _ Hselect iq eq_refl) as (cand & iq' & Hc' & Hs' & He).
        exists (IUnder cand), (Build_IConfig q' pool iq' used log invs). split.
        + apply istep_underlay; [exact Hs' | rewrite Hc'; exact Hlts].
        + split; [cbn; rewrite Hc'; reflexivity |].
          unfold irel; cbn. split; [reflexivity |]. split; [reflexivity |].
          split; [symmetry; exact He | reflexivity].
      - eexists (IOver _), _. split.
        + eapply istep_return; eauto.
        + split; [reflexivity |]. unfold irel; cbn. repeat split; reflexivity.
    Qed.

    Lemma iexec_lift c1 T c3 :
      module_execution_tagged VE M c1 T c3 ->
      forall ic0 IT0 ic1, iexec ic0 IT0 ic1 -> irel ic1 c1 ->
      exists IT ic3, iexec ic0 (IT0 ++ IT) ic3 /\ map ierase IT = T /\ irel ic3 c3.
    Proof.
      induction 1 as [c | c1 c2 c3 ev trace Hstep Hexec IH]; intros ic0 IT0 ic1 Hx Hr.
      - exists [], ic1. rewrite app_nil_r. auto.
      - destruct (istep_lift (length IT0) _ _ _ _ Hstep Hr) as (iev & ic2 & Hs & He & Hr2).
        destruct (IH ic0 (IT0 ++ [iev]) ic2 (iexec_snoc _ _ _ _ _ Hx Hs) Hr2)
          as (IT & ic3 & Hx3 & HT & Hr3).
        exists (iev :: IT), ic3. split; [rewrite <- app_assoc in Hx3; exact Hx3 |].
        split; [cbn; rewrite He, HT; reflexivity | exact Hr3].
    Qed.

    Theorem instrument q0 T c :
      module_execution_tagged VE M (initial_tagged_module VE q0) T c ->
      exists IT ic, iexec (iinitial q0) IT ic /\ map ierase IT = T /\ irel ic c.
    Proof.
      intros Hx.
      assert (Hr0 : irel (iinitial q0) (initial_tagged_module VE q0))
        by (unfold irel; cbn; repeat split; reflexivity).
      destruct (iexec_lift _ _ _ Hx (iinitial q0) [] (iinitial q0) (iexec_refl _) Hr0)
        as (IT & ic & H1 & H2 & H3).
      exists IT, ic. auto.
    Qed.

    (** *** Invariants of instrumented executions

        [IInv IT ic] relates the instrumented trace [IT] to the
        configuration [ic] it leads to.  Positions in [IT] are the
        positions of the module trace.  The fields fall into four groups:
        the layout of the enqueue log ([ii_blocks] .. [ii_pos]); the
        queue/log/trace partition ([ii_queue_log] .. [ii_emitted_after]);
        the overlay call pool ([ii_invs_nodup] .. [ii_returned_done]); and
        the scheduling order ([ii_ret_after] .. [ii_order]). *)

    Record IInv (IT : list ITraceEvent) (ic : IConfig) : Prop := {
      ii_blocks : ic_log ic = flat_map ir_block (ic_invs ic);
      ii_starts : forall pre r post, ic_invs ic = pre ++ r :: post ->
                    ir_start r = length (flat_map ir_block pre);
      ii_pos : forall pre r post, ic_invs ic = pre ++ r :: post ->
                 nth_error IT (ir_pos r) =
                   Some (IOver (Build_ThreadEvent (fst (ir_key r))
                                  (@InvEv F (snd (ir_key r)) (ir_op r)))) /\
                 (forall r', In r' post -> ir_pos r < ir_pos r');
      ii_queue_log : forall x, In x (ic_queue ic) -> In x (ic_log ic);
      ii_queue_sorted : StronglySorted (fun x y => fst x < fst y) (ic_queue ic);
      ii_partition : forall x, In x (ic_log ic) -> In x (ic_queue ic) \/ In (IUnder x) IT;
      ii_emitted_log : forall x, In (IUnder x) IT -> In x (ic_log ic);
      ii_emitted_after : forall r x p, In r (ic_invs ic) -> In x (ir_block r) ->
                           nth_error IT p = Some (IUnder x) -> ir_pos r < p;
      ii_invs_nodup : NoDup (map ir_key (ic_invs ic));
      ii_invs_pool : forall r, In r (ic_invs ic) -> In (ir_key r) (map call_key (ic_calls ic));
      ii_pool_nodup : call_pool_well_formed (ic_calls ic);
      ii_pool_active : forall t h op ret,
          In (Build_CallEntry t h (@ActiveCall F op ret)) (ic_calls ic) ->
          exists r, In r (ic_invs ic) /\ ir_key r = (t, h) /\
                    @ActiveCall F op ret = ActiveCall (ir_op r) (ir_ret r);
      ii_status : forall r, In r (ic_invs ic) ->
          In (Build_CallEntry (fst (ir_key r)) (snd (ir_key r))
                (ActiveCall (ir_op r) (ir_ret r))) (ic_calls ic) \/
          exists q, nth_error IT q =
            Some (IOver (Build_ThreadEvent (fst (ir_key r))
                           (@ResEv F (snd (ir_key r)) (ir_op r) (ir_ret r))));
      ii_over_inv : forall p t h op,
          nth_error IT p = Some (IOver (Build_ThreadEvent t (@InvEv F h op))) ->
          exists r, In r (ic_invs ic) /\ ir_key r = (t, h) /\ ir_op r = op /\ ir_pos r = p;
      ii_over_res : forall p t h op ret,
          nth_error IT p = Some (IOver (Build_ThreadEvent t (@ResEv F h op ret))) ->
          exists r, In r (ic_invs ic) /\ ir_key r = (t, h);
      ii_returned_done : forall p t h op ret,
          nth_error IT p = Some (IOver (Build_ThreadEvent t (@ResEv F h op ret))) ->
          ~ In (t, h) (map ts_owner (map snd (ic_queue ic)));
      ii_ret_after : forall r x p q op ret,
          In r (ic_invs ic) -> In x (ir_block r) ->
          nth_error IT p = Some (IUnder x) ->
          nth_error IT q = Some (IOver (Build_ThreadEvent (fst (ir_key r))
                                          (@ResEv F (snd (ir_key r)) op ret))) ->
          p < q;
      ii_no_overtake : forall x y, In x (ic_queue ic) -> In (IUnder y) IT -> fst x < fst y ->
          tagged_can_cross (ts_event (snd x)) (ts_event (snd y));
      ii_order : forall x y p q,
          nth_error IT p = Some (IUnder x) -> nth_error IT q = Some (IUnder y) ->
          fst x < fst y -> ~ tagged_can_cross (ts_event (snd x)) (ts_event (snd y)) ->
          p < q;
      ii_used : ic_used ic = flat_map (fun r => invocation_keys (map untag (ir_trace r))) (ic_invs ic);
      ii_used_nodup : NoDup (ic_used ic);
      ii_produced : forall r, In r (ic_invs ic) ->
          program_produces_tagged (fst (ir_key r)) (M (ir_op r) (fst (ir_key r)))
            (ir_trace r) (ir_ret r);
    }.

    (** **** Helpers *)

    Lemma block_ids_aux (invs : list InvRec) : forall acc,
      (forall pre r post, invs = pre ++ r :: post ->
         ir_start r = acc + length (flat_map ir_block pre)) ->
      forall i x, nth_error (flat_map ir_block invs) i = Some x -> fst x = acc + i.
    Proof.
      induction invs as [| r invs IH]; intros acc Hst i x Hi; [destruct i; discriminate |].
      change (flat_map ir_block (r :: invs)) with (ir_block r ++ flat_map ir_block invs) in Hi.
      assert (Hr : ir_start r = acc) by (rewrite (Hst [] r invs eq_refl); cbn; lia).
      destruct (Nat.lt_ge_cases i (length (ir_block r))) as [Hlt | Hge].
      - rewrite nth_error_app1 in Hi by exact Hlt. unfold ir_block in Hi.
        rewrite nth_error_number in Hi.
        destruct (nth_error _ i); cbn in Hi; [| discriminate].
        inversion Hi; subst. cbn. lia.
      - rewrite nth_error_app2 in Hi by exact Hge.
        rewrite (IH (acc + length (ir_block r))) with (i := i - length (ir_block r)) (x := x); [lia | | exact Hi].
        intros pre r' post Heq. rewrite (Hst (r :: pre) r' post); [| rewrite Heq; reflexivity].
        cbn. rewrite length_app. lia.
    Qed.

    Lemma log_ids IT ic : IInv IT ic ->
      forall i x, nth_error (ic_log ic) i = Some x -> fst x = i.
    Proof.
      intros Hinv i x Hi. rewrite (ii_blocks _ _ Hinv) in Hi.
      apply (block_ids_aux (ic_invs ic) 0); [| exact Hi].
      intros pre r post Heq. rewrite (ii_starts _ _ Hinv pre r post Heq). lia.
    Qed.

    Lemma log_id_bound IT ic x : IInv IT ic -> In x (ic_log ic) -> fst x < length (ic_log ic).
    Proof.
      intros Hinv Hx. destruct (In_nth_error _ _ Hx) as [i Hi].
      rewrite (log_ids IT ic Hinv i x Hi). apply nth_error_Some. congruence.
    Qed.

    Lemma ss_fst_nodup (l : list IEvent) : StronglySorted (fun x y => fst x < fst y) l -> NoDup l.
    Proof.
      induction 1 as [|a l Hs IH Hf]; constructor; [| exact IH].
      intro Ha. rewrite Forall_forall in Hf. specialize (Hf a Ha). lia.
    Qed.

    Lemma iselect_split cand q q' :
      iselect cand q q' ->
      exists pre post, q = pre ++ cand :: post /\ q' = pre ++ post /\
        Forall (fun e => tagged_can_cross (ts_event (snd e)) (ts_event (snd cand))) pre.
    Proof.
      induction 1 as [suffix | earlier q q' Hcross Hsel IH].
      - exists [], suffix. auto.
      - destruct IH as (pre & post & -> & -> & Hall). exists (earlier :: pre), post. cbn. auto.
    Qed.

    Lemma block_owner r x :
      In x (ir_block r) ->
      ts_owner (snd x) = ir_key r /\
      exists j, nth_error (ir_trace r) j = Some (ts_event (snd x)) /\ fst x = ir_start r + j.
    Proof.
      destruct x as [i e]. unfold ir_block. intros H. apply in_number in H as [Hr Hn].
      unfold schedule_trace_tagged in Hn. rewrite nth_error_map in Hn.
      destruct (nth_error (ir_trace r) (i - ir_start r)) as [m |] eqn:Hm; cbn in Hn; [| discriminate].
      inversion Hn; subst. cbn. split; [reflexivity |]. exists (i - ir_start r). split; [exact Hm | lia].
    Qed.

    Lemma block_of_trace r j m :
      nth_error (ir_trace r) j = Some m ->
      In (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m) (ir_block r).
    Proof.
      intros Hj. unfold ir_block. apply nth_error_In with (n := j).
      rewrite nth_error_number. unfold schedule_trace_tagged. rewrite nth_error_map, Hj. reflexivity.
    Qed.

    Lemma block_ids r x : In x (ir_block r) -> ir_start r <= fst x < ir_start r + length (ir_block r).
    Proof.
      intros H. pose proof (in_number_fst _ _ _ H) as H'. unfold ir_block in *.
      rewrite number_length in *. exact H'.
    Qed.

    Lemma finish_call_source t h op ret (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' -> In (Build_CallEntry t h (ActiveCall op ret)) pool.
    Proof. induction 1; cbn; auto. Qed.

    Lemma finish_call_active_preserved t h op ret (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' ->
      forall t' h' op' ret',
        In (Build_CallEntry t' h' (@ActiveCall F op' ret')) pool' ->
        In (Build_CallEntry t' h' (ActiveCall op' ret')) pool.
    Proof.
      induction 1 as [tail | t0 h0 cell pool pool' Hneq Hfin IH]; intros t' h' op' ret' Hin; cbn in *.
      - destruct Hin as [Hin | Hin]; [discriminate | right; exact Hin].
      - destruct Hin as [Hin | Hin]; [left; exact Hin | right; eapply IH; exact Hin].
    Qed.

    Lemma finish_call_other t h op ret (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' ->
      forall e, In e pool -> call_key e <> (t, h) -> In e pool'.
    Proof.
      induction 1 as [tail | t0 h0 cell pool pool' Hneq Hfin IH]; intros e Hin Hk; cbn in *.
      - destruct Hin as [<- | Hin]; [exfalso; apply Hk; reflexivity | right; exact Hin].
      - destruct Hin as [<- | Hin]; [left; reflexivity | right; apply IH; assumption].
    Qed.

    Lemma finish_call_cases t h op ret (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' ->
      forall e, In e pool -> In e pool' \/ e = Build_CallEntry t h (ActiveCall op ret).
    Proof.
      induction 1 as [tail | t0 h0 cell pool pool' Hneq Hfin IH]; intros e Hin; cbn in *.
      - destruct Hin as [<- | Hin]; [right; reflexivity | left; right; exact Hin].
      - destruct Hin as [<- | Hin]; [left; left; reflexivity |].
        destruct (IH e Hin) as [H | H]; [left; right; exact H | right; exact H].
    Qed.

    Lemma pool_entry_unique (pool : CallPool F) e1 e2 :
      call_pool_well_formed pool -> In e1 pool -> In e2 pool -> call_key e1 = call_key e2 -> e1 = e2.
    Proof. intros Hwf. apply nodup_map_inj. exact Hwf. Qed.

    Definition cell_res (h : RelaxedSig.handle F) (cell : CallCell F) : option (Event F) :=
      match cell with
      | ActiveCall op ret => Some (ResEv h op ret)
      | DeadCall => None
      end.

    Lemma owners_sub (l l' : list IEvent) k :
      (forall x, In x l -> In x l') ->
      In k (map ts_owner (map snd l)) -> In k (map ts_owner (map snd l')).
    Proof.
      intros Hs Hk. rewrite map_map in *. apply in_map_iff in Hk as (x & <- & Hx).
      apply in_map_iff. exists x. auto.
    Qed.

    Lemma nth_error_snoc_lt {A : Type} (l : list A) (a : A) p x :
      nth_error l p = Some x -> nth_error (l ++ [a]) p = Some x.
    Proof. intros H. rewrite nth_error_app1; [exact H | apply nth_error_Some; congruence]. Qed.

    Lemma nth_error_snoc_new {A : Type} (l : list A) (a : A) :
      nth_error (l ++ [a]) (length l) = Some a.
    Proof. rewrite nth_error_app2, Nat.sub_diag by lia. reflexivity. Qed.

    Lemma nth_error_snoc_cases {A : Type} (l : list A) (a : A) p x :
      nth_error (l ++ [a]) p = Some x -> (p < length l /\ nth_error l p = Some x) \/ (p = length l /\ x = a).
    Proof.
      intros H. destruct (Nat.lt_ge_cases p (length l)) as [Hlt | Hge].
      - left. rewrite nth_error_app1 in H by exact Hlt. auto.
      - right. rewrite nth_error_app2 in H by exact Hge.
        destruct (p - length l) eqn:Hd; cbn in H.
        + inversion H. split; [lia | reflexivity].
        + destruct n; discriminate.
    Qed.

    Lemma nth_error_lt {A : Type} (l : list A) p x : nth_error l p = Some x -> p < length l.
    Proof. intros H. apply nth_error_Some. congruence. Qed.

    Lemma in_snoc_under (IT : list ITraceEvent) (e : ITraceEvent) x :
      In (IUnder x) (IT ++ [e]) -> In (IUnder x) IT \/ e = IUnder x.
    Proof. intros H. apply in_app_or in H as [H | [H | []]]; auto. Qed.

    Lemma in_snoc_over (IT : list ITraceEvent) ev x :
      In (IUnder x) (IT ++ [IOver ev]) -> In (IUnder x) IT.
    Proof. intros H. apply in_snoc_under in H as [H | H]; [exact H | discriminate]. Qed.

    Lemma nth_snoc_over_under (IT : list ITraceEvent) ev p x :
      nth_error (IT ++ [IOver ev]) p = Some (IUnder x) -> nth_error IT p = Some (IUnder x).
    Proof. intros H. apply nth_error_snoc_cases in H as [[_ H] | [_ H]]; [exact H | discriminate]. Qed.

    Lemma iinv_initial q : IInv [] (iinitial q).
    Proof.
      constructor; cbn;
        first [ reflexivity
              | (intros; contradiction)
              | (intros p; destruct p; intros; discriminate)
              | (intros x y p; destruct p; intros; discriminate)
              | (unfold call_pool_well_formed; constructor)
              | constructor ].
    Qed.

    (** **** The underlay step *)

    Lemma iinv_underlay IT cand q q' pool queue queue' used log invs :
      IInv IT (Build_IConfig q pool queue used log invs) ->
      iselect cand queue queue' ->
      IInv (IT ++ [IUnder cand]) (Build_IConfig q' pool queue' used log invs).
    Proof.
      intros Hinv Hsel.
      destruct (iselect_split _ _ _ Hsel) as (pre & post & Hq & Hq' & Hcross).
      destruct Hinv as [Hblocks Hstarts Hpos Hqlog Hsorted Hpart Helog Heafter Hind Hipool
                        Hpnd Hpact Hstat Hoinv Hores Hrdone Hrafter Hnoov Hord Hused Hund Hprod];
        cbn in *.
      subst queue queue'.
      assert (Hcand_q : In cand (pre ++ cand :: post)) by (apply in_or_app; right; left; reflexivity).
      assert (Hsub : forall x, In x (pre ++ post) -> In x (pre ++ cand :: post)).
      { intros x Hx. apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left | right; right]; exact Hx. }
      constructor; cbn.
      - exact Hblocks.
      - exact Hstarts.
      - intros pr r po Heq. destruct (Hpos pr r po Heq) as [H1 H2].
        split; [apply nth_error_snoc_lt; exact H1 | exact H2].
      - intros x Hx. apply Hqlog, Hsub, Hx.
      - eapply ss_sub; exact Hsorted.
      - intros x Hx. destruct (Hpart x Hx) as [Hxq | Hxe].
        + apply in_app_or in Hxq as [Hxq | [Hxq | Hxq]].
          * left. apply in_or_app. left. exact Hxq.
          * right. subst x. apply in_or_app. right. left. reflexivity.
          * left. apply in_or_app. right. exact Hxq.
        + right. apply in_or_app. left. exact Hxe.
      - intros x Hx. apply in_snoc_under in Hx as [Hx | Hx]; [apply Helog, Hx |].
        injection Hx as <-. apply Hqlog, Hcand_q.
      - intros r x p Hr Hx Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [-> He]].
        + eapply Heafter; eauto.
        + destruct (in_split _ _ Hr) as (l1 & l2 & Hsplit).
          destruct (Hpos _ _ _ Hsplit) as [H1 _]. eapply nth_error_lt; exact H1.
      - exact Hind.
      - exact Hipool.
      - exact Hpnd.
      - exact Hpact.
      - intros r Hr. destruct (Hstat r Hr) as [H | (q0 & Hq0)];
          [left; exact H | right; exists q0; apply nth_error_snoc_lt; exact Hq0].
      - intros p t h op Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]];
          [eapply Hoinv; exact Hp | discriminate].
      - intros p t h op ret Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]];
          [eapply Hores; exact Hp | discriminate].
      - intros p t h op ret Hp Hin. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]]; [| discriminate].
        apply (Hrdone p t h op ret Hp). eapply owners_sub; [exact Hsub | exact Hin].
      - intros r x p q0 op ret Hr Hx Hp Hq0.
        apply nth_error_snoc_cases in Hq0 as [[Hlt Hq0] | [_ He]]; [| discriminate].
        apply nth_error_snoc_cases in Hp as [[_ Hp] | [-> He']].
        + eapply Hrafter; eauto.
        + exfalso. injection He' as <-.
          apply (Hrdone q0 _ _ op ret Hq0). rewrite map_map. apply in_map_iff.
          exists x. split; [| exact Hcand_q].
          rewrite (proj1 (block_owner r x Hx)). apply surjective_pairing.
      - intros x y Hx Hy Hlt. apply in_snoc_under in Hy as [Hy | Hy].
        + apply Hnoov; [apply Hsub; exact Hx | exact Hy | exact Hlt].
        + injection Hy as <-. apply in_app_or in Hx as [Hx | Hx].
          * rewrite Forall_forall in Hcross. apply Hcross, Hx.
          * exfalso. pose proof (ss_after _ pre cand post x Hsorted Hx). cbn in *. lia.
      - intros x y p q0 Hp Hq0 Hlt Hnc.
        apply nth_error_snoc_cases in Hp as [[Hpl Hp] | [-> Hx]];
          apply nth_error_snoc_cases in Hq0 as [[Hql Hq0] | [-> Hy]].
        + eapply Hord; eauto.
        + exact Hpl.
        + exfalso. injection Hx as <-. apply Hnc. apply Hnoov;
            [exact Hcand_q | apply nth_error_In with (n := q0); exact Hq0 | exact Hlt].
        + injection Hx as <-. injection Hy as <-. lia.
      - exact Hused.
      - exact Hund.
      - exact Hprod.
    Qed.

    (** **** The invocation step *)

    Lemma iinv_invoke IT t h op q pool queue used log invs trace ret :
      IInv IT (Build_IConfig q pool queue used log invs) ->
      call_fresh (t, h) pool ->
      program_produces_tagged t (M op t) trace ret ->
      trace_fresh used (map untag trace) ->
      IInv (IT ++ [IOver (Build_ThreadEvent t (@InvEv F h op))])
        (Build_IConfig q (Build_CallEntry t h (ActiveCall op ret) :: pool)
           (queue ++ ir_block (Build_InvRec (t, h) op ret (length log) (length IT) trace))
           (used ++ invocation_keys (map untag trace))
           (log ++ ir_block (Build_InvRec (t, h) op ret (length log) (length IT) trace))
           (invs ++ [Build_InvRec (t, h) op ret (length log) (length IT) trace])).
    Proof.
      intros Hinv Hfresh Hmethod Htrace.
      set (r := Build_InvRec (t, h) op ret (length log) (length IT) trace).
      assert (Hlogb : forall x, In x log -> fst x < length log)
        by (intros x Hx; exact (log_id_bound _ _ x Hinv Hx)).
      assert (Hnew : forall y, In y (ir_block r) -> length log <= fst y)
        by (intros y Hy; apply block_ids in Hy; cbn in Hy; lia).
      destruct Hinv as [Hblocks Hstarts Hpos Hqlog Hsorted Hpart Helog Heafter Hind Hipool
                        Hpnd Hpact Hstat Hoinv Hores Hrdone Hrafter Hnoov Hord Hused Hund Hprod];
        cbn in *.
      assert (Hkey_new : forall r', In r' invs -> ir_key r' <> (t, h)).
      { intros r' Hr' Heq. apply Hfresh. rewrite <- Heq. apply Hipool, Hr'. }
      assert (Hin_invs : forall r', In r' (invs ++ [r]) -> In r' invs \/ r' = r).
      { intros r' Hr'. apply in_app_or in Hr' as [Hr' | [Hr' | []]]; auto. }
      constructor; cbn.
      - rewrite flat_map_app. cbn. rewrite app_nil_r, <- Hblocks. reflexivity.
      - intros pr r0 po Heq. destruct (app_snoc_cases _ _ _ _ _ (eq_sym Heq)) as [(-> & -> & ->) | (po' & -> & Heq')].
        + subst r. cbn. rewrite Hblocks. reflexivity.
        + exact (Hstarts pr r0 po' Heq').
      - intros pr r0 po Heq. destruct (app_snoc_cases _ _ _ _ _ (eq_sym Heq)) as [(-> & -> & ->) | (po' & -> & Heq')].
        + cbn. split; [apply nth_error_snoc_new | intros _ []].
        + destruct (Hpos pr r0 po' Heq') as [H1 H2]. split; [apply nth_error_snoc_lt; exact H1 |].
          intros r' Hr'. apply in_app_or in Hr' as [Hr' | [<- | []]]; [apply H2, Hr' |].
          cbn. eapply nth_error_lt; exact H1.
      - intros x Hx. apply in_app_or in Hx as [Hx | Hx]; apply in_or_app; [left; apply Hqlog, Hx | right; exact Hx].
      - apply ss_app; [exact Hsorted | apply number_sorted |].
        intros x y Hx Hy. pose proof (Hlogb x (Hqlog x Hx)). pose proof (Hnew y Hy). lia.
      - intros x Hx. apply in_app_or in Hx as [Hx | Hx].
        + destruct (Hpart x Hx) as [Hxq | Hxe].
          * left. apply in_or_app. left. exact Hxq.
          * right. apply in_or_app. left. exact Hxe.
        + left. apply in_or_app. right. exact Hx.
      - intros x Hx. apply in_snoc_over in Hx. apply in_or_app. left. apply Helog, Hx.
      - intros r0 x p Hr0 Hx Hp. apply nth_snoc_over_under in Hp.
        destruct (Hin_invs r0 Hr0) as [Hr0' | ->]; [eapply Heafter; eauto |].
        exfalso. pose proof (Hlogb x (Helog x (nth_error_In _ _ Hp))). pose proof (Hnew x Hx). lia.
      - rewrite map_app. apply nodup_snoc; [exact Hind |].
        intros Hin. apply in_map_iff in Hin as (r' & Hk & Hr'). exact (Hkey_new r' Hr' Hk).
      - intros r0 Hr0. destruct (Hin_invs r0 Hr0) as [Hr0' | ->]; [right; apply Hipool, Hr0' | left; reflexivity].
      - unfold call_pool_well_formed. cbn. constructor; [exact Hfresh | exact Hpnd].
      - intros t0 h0 op0 ret0 [He | He].
        + exists r. split; [apply in_or_app; right; left; reflexivity |].
          cbn. split; [congruence |].
          apply (f_equal (fun e => ce_cell F e)) in He. cbn in He. symmetry. exact He.
        + destruct (Hpact t0 h0 op0 ret0 He) as (r' & Hr' & Hk & Hc).
          exists r'. split; [apply in_or_app; left; exact Hr' | split; assumption].
      - intros r0 Hr0. destruct (Hin_invs r0 Hr0) as [Hr0' | ->].
        + destruct (Hstat r0 Hr0') as [H | (q0 & Hq0)];
            [left; right; exact H | right; exists q0; apply nth_error_snoc_lt; exact Hq0].
        + left. left. reflexivity.
      - intros p t0 h0 op0 Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [-> He]].
        + destruct (Hoinv p t0 h0 op0 Hp) as (r' & Hr' & H1 & H2 & H3).
          exists r'. split; [apply in_or_app; left; exact Hr' | auto].
        + injection He as <- <- <-. exists r. split; [apply in_or_app; right; left; reflexivity |].
          cbn. auto.
      - intros p t0 h0 op0 ret0 Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]]; [| discriminate].
        destruct (Hores p t0 h0 op0 ret0 Hp) as (r' & Hr' & Hk).
        exists r'. split; [apply in_or_app; left; exact Hr' | exact Hk].
      - intros p t0 h0 op0 ret0 Hp Hin. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]]; [| discriminate].
        destruct (Hores p t0 h0 op0 ret0 Hp) as (r' & Hr' & Hk).
        rewrite map_app, map_app in Hin. apply in_app_or in Hin as [Hin | Hin].
        + exact (Hrdone p t0 h0 op0 ret0 Hp Hin).
        + rewrite map_map in Hin. apply in_map_iff in Hin as (y & Hy & Hyb).
          rewrite (proj1 (block_owner r y Hyb)) in Hy. cbn in Hy.
          apply (Hkey_new r' Hr'). congruence.
      - intros r0 x p q0 op0 ret0 Hr0 Hx Hp Hq0.
        apply nth_snoc_over_under in Hp.
        apply nth_error_snoc_cases in Hq0 as [[_ Hq0] | [_ He]]; [| discriminate].
        destruct (Hin_invs r0 Hr0) as [Hr0' | ->]; [eapply Hrafter; eauto |].
        exfalso. pose proof (Hlogb x (Helog x (nth_error_In _ _ Hp))). pose proof (Hnew x Hx). lia.
      - intros x y Hx Hy Hlt. apply in_snoc_over in Hy.
        apply in_app_or in Hx as [Hx | Hx]; [apply Hnoov; assumption |].
        exfalso. pose proof (Hlogb y (Helog y Hy)). pose proof (Hnew x Hx). lia.
      - intros x y p q0 Hp Hq0. apply nth_snoc_over_under in Hp. apply nth_snoc_over_under in Hq0.
        eapply Hord; eauto.
      - rewrite flat_map_app, Hused. cbn. rewrite app_nil_r. reflexivity.
      - destruct Htrace as [Htnd Htfr]. apply NoDup_app; [exact Hund | exact Htnd |].
        intros a Ha Ha'. exact (Htfr a Ha' Ha).
      - intros r0 Hr0. destruct (Hin_invs r0 Hr0) as [Hr0' | ->]; [apply Hprod, Hr0' | exact Hmethod].
    Qed.

    (** **** The return step *)

    Lemma iinv_return IT t h op ret q pool pool' queue used log invs :
      IInv IT (Build_IConfig q pool queue used log invs) ->
      finish_call t h op ret pool pool' ->
      owner_done_tagged (t, h) (map snd queue) ->
      IInv (IT ++ [IOver (Build_ThreadEvent t (@ResEv F h op ret))])
        (Build_IConfig q pool' queue used log invs).
    Proof.
      intros Hinv Hfin Hdone.
      destruct Hinv as [Hblocks Hstarts Hpos Hqlog Hsorted Hpart Helog Heafter Hind Hipool
                        Hpnd Hpact Hstat Hoinv Hores Hrdone Hrafter Hnoov Hord Hused Hund Hprod];
        cbn in *.
      pose proof (finish_call_source _ _ _ _ _ _ Hfin) as Hsrc.
      constructor; cbn.
      - exact Hblocks.
      - exact Hstarts.
      - intros pr r po Heq. destruct (Hpos pr r po Heq) as [H1 H2].
        split; [apply nth_error_snoc_lt; exact H1 | exact H2].
      - exact Hqlog.
      - exact Hsorted.
      - intros x Hx. destruct (Hpart x Hx) as [H | H]; [left; exact H | right; apply in_or_app; left; exact H].
      - intros x Hx. apply in_snoc_over in Hx. apply Helog, Hx.
      - intros r x p Hr Hx Hp. apply nth_snoc_over_under in Hp. eapply Heafter; eauto.
      - exact Hind.
      - intros r Hr. rewrite <- (finish_call_keys _ _ _ _ _ _ Hfin). apply Hipool, Hr.
      - eapply finish_call_well_formed; eauto.
      - intros t0 h0 op0 ret0 He. apply Hpact. eapply finish_call_active_preserved; eauto.
      - intros r Hr. destruct (Hstat r Hr) as [H | (q0 & Hq0)].
        + destruct (finish_call_cases _ _ _ _ _ _ Hfin _ H) as [H' | Heq]; [left; exact H' |].
          right. exists (length IT). rewrite nth_error_snoc_new.
          pose proof (f_equal (fun e => ce_tid F e) Heq) as Ht. cbn in Ht.
          apply (f_equal (fun e => cell_res (ce_handle F e) (ce_cell F e))) in Heq. cbn in Heq.
          apply (f_equal (option_map (fun ev => IOver (Build_ThreadEvent t ev)))) in Heq.
          cbn in Heq. rewrite Ht. symmetry. exact Heq.
        + right. exists q0. apply nth_error_snoc_lt. exact Hq0.
      - intros p t0 h0 op0 Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]];
          [eapply Hoinv; exact Hp | discriminate].
      - intros p t0 h0 op0 ret0 Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]].
        + eapply Hores; exact Hp.
        + injection He as <- <-. destruct (Hpact _ _ _ _ Hsrc) as (r & Hr & Hk & _).
          exists r. split; [exact Hr | exact Hk].
      - intros p t0 h0 op0 ret0 Hp. apply nth_error_snoc_cases in Hp as [[_ Hp] | [_ He]].
        + eapply Hrdone; exact Hp.
        + injection He as <- <-. exact Hdone.
      - intros r x p q0 op0 ret0 Hr Hx Hp Hq0. apply nth_snoc_over_under in Hp.
        apply nth_error_snoc_cases in Hq0 as [[_ Hq0] | [-> _]].
        + eapply Hrafter; eauto.
        + eapply nth_error_lt; exact Hp.
      - intros x y Hx Hy Hlt. apply in_snoc_over in Hy. apply Hnoov; assumption.
      - intros x y p q0 Hp Hq0. apply nth_snoc_over_under in Hp. apply nth_snoc_over_under in Hq0.
        eapply Hord; eauto.
      - exact Hused.
      - exact Hund.
      - exact Hprod.
    Qed.

    Lemma iinv_reach q0 IT ic : iexec (iinitial q0) IT ic -> IInv IT ic.
    Proof.
      induction 1 as [| tr c ev c' Hexec IH Hstep].
      - apply iinv_initial.
      - inversion Hstep; subst.
        + apply iinv_invoke; assumption.
        + eapply iinv_underlay; eassumption.
        + eapply iinv_return; eassumption.
    Qed.

    (** *** Consequences *)

    Section Facts.
      Context (IT : list ITraceEvent) (ic : IConfig) (Hinv : IInv IT ic).

      (** Every emitted underlay event comes from the local trace of a
          recorded overlay call. *)
      Lemma emitted_source p x :
        nth_error IT p = Some (IUnder x) ->
        exists r j, In r (ic_invs ic) /\ In x (ir_block r) /\
          nth_error (ir_trace r) j = Some (ts_event (snd x)) /\
          fst x = ir_start r + j /\ ts_owner (snd x) = ir_key r.
      Proof.
        intros Hp. pose proof (ii_emitted_log _ _ Hinv x (nth_error_In _ _ Hp)) as Hx.
        rewrite (ii_blocks _ _ Hinv) in Hx. apply in_flat_map in Hx as (r & Hr & Hx).
        destruct (block_owner r x Hx) as (Ho & j & Hj & Hid).
        exists r, j. auto.
      Qed.

      (** At an empty queue every event of every recorded call has been
          emitted. *)
      Lemma complete_all_emitted r j m :
        ic_queue ic = [] -> In r (ic_invs ic) -> nth_error (ir_trace r) j = Some m ->
        exists p, nth_error IT p =
          Some (IUnder (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m)).
      Proof.
        intros Hq Hr Hj. pose proof (block_of_trace r j m Hj) as Hb.
        assert (Hl : In (ir_start r + j, Build_TaggedScheduledEvent (ir_key r) m) (ic_log ic)).
        { rewrite (ii_blocks _ _ Hinv). apply in_flat_map. exists r. auto. }
        destruct (ii_partition _ _ Hinv _ Hl) as [Hx | Hx]; [rewrite Hq in Hx; contradiction |].
        apply In_nth_error. exact Hx.
      Qed.

      Lemma record_pos_bound r : In r (ic_invs ic) -> ir_pos r < length IT.
      Proof.
        intros Hr. destruct (in_split _ _ Hr) as (l1 & l2 & Hs).
        eapply nth_error_lt. exact (proj1 (ii_pos _ _ Hinv _ _ _ Hs)).
      Qed.

      Lemma record_key_unique r r' :
        In r (ic_invs ic) -> In r' (ic_invs ic) -> ir_key r = ir_key r' -> r = r'.
      Proof. apply nodup_map_inj. exact (ii_invs_nodup _ _ Hinv). Qed.

      Lemma record_invkey_unique r r' k :
        In r (ic_invs ic) -> In r' (ic_invs ic) ->
        In k (invocation_keys (map untag (ir_trace r))) ->
        In k (invocation_keys (map untag (ir_trace r'))) -> r = r'.
      Proof.
        intros Hr Hr' Hk Hk'. pose proof (ii_used_nodup _ _ Hinv) as Hnd.
        rewrite (ii_used _ _ Hinv) in Hnd.
        exact (nodup_flat_map_in _ _ _ _ _ Hnd Hr Hr' Hk Hk').
      Qed.

      (** Blocks of calls invoked earlier have smaller identifiers. *)
      Lemma record_ids_ordered r r' x y :
        In r (ic_invs ic) -> In r' (ic_invs ic) -> ir_pos r < ir_pos r' ->
        In x (ir_block r) -> In y (ir_block r') -> fst x < fst y.
      Proof.
        intros Hr Hr' Hlt Hx Hy.
        assert (Hne : r <> r') by (intros ->; lia).
        destruct (in_split_two _ _ _ Hr Hr' Hne) as [(l1 & l2 & l3 & Hs) | (l1 & l2 & l3 & Hs)].
        - pose proof (ii_starts _ _ Hinv l1 r (l2 ++ r' :: l3) Hs) as Hs1.
          pose proof (ii_starts _ _ Hinv (l1 ++ r :: l2) r' l3) as Hs2.
          rewrite <- app_assoc in Hs2. cbn in Hs2. specialize (Hs2 Hs).
          rewrite flat_map_app in Hs2. cbn in Hs2. rewrite !length_app in Hs2.
          apply block_ids in Hx. apply block_ids in Hy. lia.
        - exfalso. pose proof (proj2 (ii_pos _ _ Hinv l1 r' (l2 ++ r :: l3) Hs) r) as H.
          assert (In r (l2 ++ r :: l3)) by (apply in_or_app; right; left; reflexivity).
          specialize (H ltac:(assumption)). lia.
      Qed.

      (** A complete run leaves no active call: every recorded call
          returned, with the recorded result. *)
      Lemma complete_all_returned r :
        (forall e, In e (ic_calls ic) -> ce_cell F e = DeadCall) ->
        In r (ic_invs ic) ->
        exists q, nth_error IT q =
          Some (IOver (Build_ThreadEvent (fst (ir_key r))
                         (@ResEv F (snd (ir_key r)) (ir_op r) (ir_ret r)))).
      Proof.
        intros Hdead Hr. destruct (ii_status _ _ Hinv r Hr) as [H | H]; [| exact H].
        specialize (Hdead _ H). discriminate.
      Qed.
    End Facts.

  End Instrumented.

End RelaxedModuleFacts.
