(** * POQueueRD: [POQueueR] with abandoned dequeues

    Task WHWQ (.rocq-review/tasks/WHWQ.md), phase P5b (design decision C7).
    [POQueueRD A] is [POQueueR A] with one more step, [poqrd_dead]: in
    [POQReady s] an invocation of [deq] may leave the state unchanged.  The
    dequeue then never enters [POQAtomic], which is the only state that
    enables a dequeue response.

    ** Why the step is needed

    [RelaxedModuleSemantics.tagged_invoke] commits a call's method trace,
    including the responses of its underlay calls, at the overlay
    invocation, and [RelaxedHoareSpec.EI] fixes the response of an
    underlay call at its invocation.  A dequeue whose last exchange was
    committed with a non-null result, but whose exchange reads null, can
    therefore never respond.  It has no pending invocation left, so by
    (F1)--(F3) the later calls of its thread are not ordered after it, and
    they can complete.  Their abstract invocations need the dequeue to have
    left [ls_inv] ([RelaxedPossibility.invocation_ready]; neither
    [(deq, enq)] nor [(deq, deq)] is in [I(enq, deq)]).  In [POQueueR] the
    dequeue can take its abstract invocation only together with its
    response: [POQAtomic] admits only that response, which removes a
    complete minimal vertex, and removing a vertex whose value is still in
    memory breaks the later dequeue that reads it.  [poqrd_dead] is the
    abstract invocation of such a dequeue.  The obstacle is described in
    the task file (C7); it is not stated as a Rocq theorem here.

    ** Main results

    - [poqrd_count]: along every path, the number of dequeue responses
      plus "ends in [POQAtomic]" is at most the number of dequeue
      invocations plus "starts in [POQAtomic]"; a [poqrd_dead] step makes
      the inequality strict, and equality makes the path a path of
      [POQueueR].
    - [deq_inv_res_count]: a complete, well-formed trace has as many
      dequeue invocations as dequeue responses.
    - [poqrd_complete_path]: hence a complete, well-formed path of
      [POQueueRD] from [poqr_init] has no [poqrd_dead] step: it is a path
      of [POQueueR].
    - [poqrd_sound]: [ViewLHL.sound_pres (νQ A) (POQueueRD A) poqr_init],
      from [POQueueRSound.poqr_sound].
    - [poqr_path_poqrd]: every path of [POQueueR] is a path of
      [POQueueRD].

    [POQueueRD] is handle-oblivious like [POQueueR].  On a trace that is
    not complete, a later dequeue's response may carry the handle of a
    dequeue that took [poqrd_dead]; [poqrd_sound] says nothing about such
    traces, and neither does [RelaxedGSim.gsim_rel_lin], whose hypothesis
    [HVF] concerns complete traces only.

    No axiom is used: every result is closed under the global context
    ([Print Assumptions]; task log). *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.micromega.Lia.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.PrefixView.
Require Import models.view.ViewLHL.
Require Import examples.Relaxed.WHWQ.WHWQSpec.
Require Import examples.Relaxed.WHWQ.POQueueR.
Require Import examples.Relaxed.WHWQ.POQueueRSound.

Import ListNotations.

Module POQueueRD.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedTraceLin.
  Import RelaxedGSim.
  Import WHWQSpec.
  Import POQueueR.

  Section Dead.
    Context {A : Type}.

    Local Abbreviation F := (FQ A).

    (** ** The presentation *)

    Definition poqrd_dead (ev : ThreadEvent F) (c c' : POQueueControl A) : Prop :=
      match te_ev _ ev with
      | InvEv _ o =>
          match o with
          | deq => exists s, c = POQReady s /\ c' = POQReady s
          | enq _ => False
          end
      | ResEv _ _ _ => False
      end.

    Definition poqrd_step (ev : ThreadEvent F) (c c' : POQueueControl A) : Prop :=
      poqr_step ev c c' \/ poqrd_dead ev c c'.

    Definition POQueueRD : LTS F :=
      {| State := POQueueControl A; Step := poqrd_step; Error := fun _ _ => False |}.

    Lemma poqr_path_poqrd v T v' :
      vf_path (POQueueR A) v T v' -> vf_path POQueueRD v T v'.
    Proof.
      induction 1 as [v | v ev v1 evs v'' Hs Hp IH].
      - constructor.
      - econstructor; [left; exact Hs | exact IH].
    Qed.

    (** ** Counting *)

    Definition is_deq_inv (e : ThreadEvent F) : bool :=
      match te_ev _ e with
      | InvEv _ o => match o with deq => true | enq _ => false end
      | ResEv _ _ _ => false
      end.

    Definition is_deq_res (e : ThreadEvent F) : bool :=
      match te_ev _ e with
      | InvEv _ _ => false
      | ResEv _ o _ => match o with deq => true | enq _ => false end
      end.

    Definition ndi (T : list (ThreadEvent F)) : nat := length (filter is_deq_inv T).
    Definition ndr (T : list (ThreadEvent F)) : nat := length (filter is_deq_res T).

    Definition atom (c : POQueueControl A) : nat :=
      match c with
      | POQAtomic _ _ => 1
      | POQReady _ => 0
      end.

    Definition b2n (b : bool) : nat := if b then 1 else 0.

    Lemma ndi_cons ev T : ndi (ev :: T) = b2n (is_deq_inv ev) + ndi T.
    Proof. unfold ndi. cbn. destruct (is_deq_inv ev); reflexivity. Qed.

    Lemma ndr_cons ev T : ndr (ev :: T) = b2n (is_deq_res ev) + ndr T.
    Proof. unfold ndr. cbn. destruct (is_deq_res ev); reflexivity. Qed.

    (** Every [POQueueR] step balances the count. *)
    Lemma poqr_step_count ev c c' :
      poqr_step ev c c' -> b2n (is_deq_res ev) + atom c' = b2n (is_deq_inv ev) + atom c.
    Proof.
      destruct ev as [t [h o | h o r]]; destruct o as [v |];
        unfold poqr_step, is_deq_inv, is_deq_res; cbn [te_ev te_tid].
      - intros (s & -> & _ & ->). reflexivity.
      - intros (s & -> & ->). reflexivity.
      - intros (s & n & -> & _ & ->). reflexivity.
      - intros (s & n & -> & _ & _ & _ & ->). reflexivity.
    Qed.

    (** A [poqrd_dead] step loses one. *)
    Lemma poqrd_dead_count ev c c' :
      poqrd_dead ev c c' -> S (b2n (is_deq_res ev) + atom c') = b2n (is_deq_inv ev) + atom c.
    Proof.
      destruct ev as [t [h o | h o r]]; destruct o as [v |];
        unfold poqrd_dead, is_deq_inv, is_deq_res; cbn [te_ev te_tid]; try contradiction.
      intros (s & -> & ->). reflexivity.
    Qed.

    Lemma poqrd_count v T v' :
      vf_path POQueueRD v T v' ->
      ndr T + atom v' <= ndi T + atom v /\
      (ndr T + atom v' = ndi T + atom v -> vf_path (POQueueR A) v T v').
    Proof.
      induction 1 as [v | v ev v1 evs v'' Hs Hp IH].
      - unfold ndr, ndi. cbn. split; [lia | intros _; constructor].
      - destruct IH as [Hle Heq]. rewrite ndi_cons, ndr_cons.
        destruct Hs as [Hs | Hs].
        + pose proof (poqr_step_count _ _ _ Hs) as Hc. split; [lia |].
          intros He. econstructor; [exact Hs | apply Heq; lia].
        + pose proof (poqrd_dead_count _ _ _ Hs) as Hc. split; [lia | intros He; lia].
    Qed.

    (** ** Complete traces balance *)

    Definition ev_key (e : ThreadEvent F) : CallKey F :=
      (te_tid _ e, match te_ev _ e with InvEv h _ => h | ResEv h _ _ => h end).

    (** A list whose selected elements have pairwise distinct keys at
        distinct positions has a duplicate-free list of selected keys. *)
    Lemma nodup_filter_keys {X K : Type} (P : X -> bool) (f : X -> K) (l : list X) :
      (forall i j x y, nth_error l i = Some x -> nth_error l j = Some y ->
         P x = true -> P y = true -> f x = f y -> i = j) ->
      NoDup (map f (filter P l)).
    Proof.
      induction l as [| a l IH]; intros Hu; [constructor |].
      cbn. assert (Hu' : forall i j x y, nth_error l i = Some x -> nth_error l j = Some y ->
                           P x = true -> P y = true -> f x = f y -> i = j).
      { intros i j x y Hi Hj Hx Hy Hf. assert (S i = S j) by exact (Hu (S i) (S j) x y Hi Hj Hx Hy Hf). lia. }
      destruct (P a) eqn:Ha; [| exact (IH Hu')].
      cbn. constructor; [| exact (IH Hu')].
      intros Hin. apply in_map_iff in Hin as (y & Hfy & Hy). apply filter_In in Hy as (Hy & HPy).
      apply In_nth_error in Hy as (j & Hj).
      assert (0 = S j) by exact (Hu 0 (S j) a y eq_refl Hj Ha HPy (eq_sym Hfy)). discriminate.
    Qed.

    Lemma inv_at_nth T i k op :
      inv_at (@PrefixView.sel F) T i k op <->
      nth_error T i = Some (Build_ThreadEvent (fst k) (@InvEv F (snd k) op)).
    Proof.
      unfold inv_at, PrefixView.sel. split.
      - intros (x & Hx & Hs). inversion Hs; subst. exact Hx.
      - intros Hx. eexists; split; [exact Hx | reflexivity].
    Qed.

    Lemma res_at_nth T i k op (r : Sig.ar op) :
      res_at (@PrefixView.sel F) T i k op r <->
      nth_error T i = Some (Build_ThreadEvent (fst k) (@ResEv F (snd k) op r)).
    Proof.
      unfold res_at, PrefixView.sel. split.
      - intros (x & Hx & Hs). inversion Hs; subst. exact Hx.
      - intros Hx. eexists; split; [exact Hx | reflexivity].
    Qed.

    Lemma is_deq_inv_true e : is_deq_inv e = true -> exists h, te_ev _ e = @InvEv F h deq.
    Proof.
      destruct e as [t [h o | h o r]]; destruct o as [v |]; cbn; try discriminate.
      intros _. exists h. reflexivity.
    Qed.

    Lemma is_deq_res_true e : is_deq_res e = true -> exists h (r : A), te_ev _ e = @ResEv F h deq r.
    Proof.
      destruct e as [t [h o | h o r]]; destruct o as [v |]; cbn; try discriminate.
      intros _. exists h, r. reflexivity.
    Qed.

    Lemma deq_inv_res_count T :
      PrefixView.wf T -> PrefixView.complete T -> ndi T = ndr T.
    Proof.
      intros (Hu1 & Hu2 & Hpre) Hc.
      assert (Hnd1 : NoDup (map ev_key (filter is_deq_inv T))).
      { apply nodup_filter_keys. intros i j x y Hi Hj Hx Hy Hf.
        destruct (is_deq_inv_true x Hx) as (hx & Ex). destruct (is_deq_inv_true y Hy) as (hy & Ey).
        destruct x as [tx ex], y as [ty ey]. cbn in Ex, Ey, Hf. subst ex ey.
        inversion Hf; subst.
        apply (Hu1 i j (ty, hy) deq deq); apply inv_at_nth; assumption. }
      assert (Hnd2 : NoDup (map ev_key (filter is_deq_res T))).
      { apply nodup_filter_keys. intros i j x y Hi Hj Hx Hy Hf.
        destruct (is_deq_res_true x Hx) as (hx & rx & Ex). destruct (is_deq_res_true y Hy) as (hy & ry & Ey).
        destruct x as [tx ex], y as [ty ey]. cbn in Ex, Ey, Hf. subst ex ey.
        inversion Hf; subst.
        apply (Hu2 i j (ty, hy) deq deq rx ry); apply res_at_nth; assumption. }
      assert (Hi12 : incl (map ev_key (filter is_deq_inv T)) (map ev_key (filter is_deq_res T))).
      { intros k Hk. apply in_map_iff in Hk as (x & <- & Hx). apply filter_In in Hx as (Hx & Hd).
        destruct (is_deq_inv_true x Hd) as (h & Ex). destruct x as [t ex]. cbn in Ex. subst ex.
        apply In_nth_error in Hx as (i & Hi).
        destruct (Hc i (t, h) deq (proj2 (inv_at_nth T i (t, h) deq) Hi)) as (j & r & Hj).
        apply res_at_nth in Hj. apply nth_error_In in Hj.
        apply in_map_iff. eexists; split; [| apply filter_In; split; [exact Hj | reflexivity]].
        reflexivity. }
      assert (Hi21 : incl (map ev_key (filter is_deq_res T)) (map ev_key (filter is_deq_inv T))).
      { intros k Hk. apply in_map_iff in Hk as (x & <- & Hx). apply filter_In in Hx as (Hx & Hd).
        destruct (is_deq_res_true x Hd) as (h & r & Ex). destruct x as [t ex]. cbn in Ex. subst ex.
        apply In_nth_error in Hx as (j & Hj).
        destruct (Hpre j (t, h) deq r (proj2 (res_at_nth T j (t, h) deq r) Hj)) as (i & _ & Hi).
        apply inv_at_nth in Hi. apply nth_error_In in Hi.
        apply in_map_iff. eexists; split; [| apply filter_In; split; [exact Hi | reflexivity]].
        reflexivity. }
      pose proof (NoDup_incl_length Hnd1 Hi12) as L1. pose proof (NoDup_incl_length Hnd2 Hi21) as L2.
      rewrite !length_map in L1, L2. unfold ndi, ndr. lia.
    Qed.

    (** ** Soundness *)

    Theorem poqrd_complete_path T c :
      vf_path POQueueRD poqr_init T c -> PrefixView.wf T -> PrefixView.complete T ->
      vf_path (POQueueR A) poqr_init T c.
    Proof.
      intros Hp Hwf Hc. destruct (poqrd_count _ _ _ Hp) as [Hle Heq].
      pose proof (deq_inv_res_count T Hwf Hc) as Hn.
      apply Heq. unfold poqr_init in *. cbn [atom] in *. lia.
    Qed.

    Theorem poqrd_sound : ViewLHL.sound_pres (νQ A) POQueueRD poqr_init.
    Proof.
      intros T c Hp Hwf Hc.
      exact (POQueueRSound.poqr_sound T c (poqrd_complete_path T c Hp Hwf Hc) Hwf Hc).
    Qed.

  End Dead.

  Arguments POQueueRD A : clear implicits.
End POQueueRD.
