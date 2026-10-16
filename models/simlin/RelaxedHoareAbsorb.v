(** * RLHL, part 11: copy-cat absorption (RLHL-3c.3, 3c.4; [absorb] pending)

    Purpose.  Latest-review M-22 item (2): the E-side copy-cat
    absorption that layering needs.  The paper's saturation proposition
    (Appendix/relaxedlin.tex:53-56) reads ⟦M⟧_E = cc_E;⟦M⟧_E;cc_F.  Its
    E-side half, after composing with an underlay presentation [VF] of
    the layer below, is

        MTraces VF M v0  =  MTraces (ModLTS VF idF) M (initial_tagged_module VF v0)

    (⟦M⟧ over [VF] versus ⟦M⟧ over the copy-cat run over [VF];
    [RelaxedHoareLayer.ModLTS]).  This file proves the inclusion [⊆]
    ([unabsorb]) for every [VF], shows that the inclusion [⊇]
    ([absorb]) is false for some [VF] ([absorb_needs_closure]), and
    proves the closure hypothesis proposed for [absorb] ([CCClosed]) for
    the specification LTSs [EI] and [EIhl] ([ei_ccclosed],
    [eihl_ccclosed]).  The theorem [absorb] itself
    ([CCClosed VF v0 -> MTraces (ModLTS VF idF) M (...) s -> MTraces VF
    M v0 s]) is PENDING (plan .rocq-review/tasks/RLHL-3c.md, sub-task
    3c.5); nothing here states or uses it.

    ** Results

    - Single method traces ([LocalTraces]):
      [produced_inv_answered] (every invocation of a produced trace is
      answered later in the same trace, same handle and operation; this
      is where [program_terminal]'s [all_resolved] is used),
      [produced_res_invoked] (every response answers an earlier
      invocation of the same handle and operation),
      [produced_rkeys_nodup] (a handle is answered at most once).
    - [CCWF u] and [rtraces_of_ccwf]: a path [u] of [V] with distinct
      invocation keys, distinct response keys, every response after its
      invocation, and a committed result for every invocation, is a
      copy-cat trace over [V] ([RTraces V v0 u]).  The copy-cat replays
      [u] event by event.
    - [underlay_ccwf], [underlay_rtraces]: the underlay trace of every
      execution of every module [M] over every [VE] is [CCWF], hence a
      copy-cat trace over [VE].  Invariant [UInv], stated over the
      emitted trace followed by the queued events.
    - [unabsorb]: [MTraces VF M v0 s -> MTraces (ModLTS VF idF) M
      (initial_tagged_module VF v0) s], for every [VF], [M], [s]; no
      hypothesis on [VF] and no inhabited-arity hypothesis (the
      copy-cat's committed result for a pending call is read off [M]'s
      own method trace, [produced_inv_answered]).  Corollaries
      [rtraces_unabsorb] (cc ⊆ cc;cc) and [complin_unabsorb] ([RCompLin]
      over the composite implies it over [VE]).
    - [rehandle], [ccimg Rk u u'] (rename the handle of every event of
      [u] along a key relation [Rk], and delete some responses),
      [ccimg_snoc_keep], [ccimg_snoc_drop], [ccimg_app], [ccimg_app_inv];
      [CCClosed V v0]: the paths of [V] from [v0] are closed under
      [ccimg Rk] for every [Rk] that is functional and injective within
      a thread.
    - [ei_ccclosed]: [CCClosed (RelaxedHoareSpec.EI δ) (s0, [])], for
      every [δ] and [s0] (only functionality of [Rk] is used).
      [eihl_ccclosed]: [CCClosed (RelaxedHoareCompLinSpec.EIhl δ) ((s0,
      []), [])] (injectivity is used for the handle-linearity check).
      The pending list must start empty: a pre-existing record could be
      answered under its old key only.
    - [absorb_needs_closure] (the plan's counterexample (R)): there are
      [VF], [M] and [s] with [s] in [MTraces (ModLTS VF idF) M ...] but
      not in [MTraces VF M ...].  [NeedsClosure.VF0] accepts invocations
      on handle [0] only; [NeedsClosure.M0] returns the raw handle of its
      one future ([RelaxedLang.future_handle]); the composite returns [5]
      ([composite_s0]), the direct run can only return [0]
      ([direct_not_s0]).  [NeedsClosure.vf0_not_ccclosed]: [VF0] is not
      [CCClosed], so the counterexample is outside the hypothesis.

    ** K / S / P / R

    - K: every result of this file is closed under the global context
      ([Print Assumptions]; no [classic], no [eq_rect_eq]).  Results are
      compared through events and projections ([some_inj],
      [pending_entry_eq], [cell_resev], [cell_val], [res_val]), never
      by inverting a dependent [ResEv] / [ActiveCall] equality.
    - S: [unabsorb] is generic: every [VF], every module, every
      execution (complete or not).  [ei_ccclosed] / [eihl_ccclosed] are
      for an empty initial pending list.  [CCClosed] is a provisional
      definition; that it is what [absorb] needs is argued in the plan
      (Design A: the target execution's underlay trace is a [ccimg] of
      the composite's inner path), not checked.
    - P: Appendix/relaxedlin.tex:53-56 (saturation) states the
      equation for strategies, without an underlay; here it is stated
      after composition with an underlay presentation [VF], one
      inclusion at a time.  [unabsorb] is ν;⟦M⟧ ⊆ ν;cc;⟦M⟧ for every
      presentation ν = [VF].  The converse is false without a closure
      hypothesis ([absorb_needs_closure]), so the proposition as printed
      ("for any ... sequential implementation") does not hold for
      handle-sensitive underlays in this model (D2).  The F-side
      (⟦M⟧;cc_F ⊆ ⟦M⟧) is not addressed.  Appendix/relaxedlin.tex:58-72
      (certified implementation, the equivalence it derives from
      saturation) needs [absorb] and is not here.
    - R: latest-review M-22, "Absorption, linking and mtraces_mono are
      missing".  This file supplies one half of absorption and the
      closure lemmas for the other; absorption ([absorb]) and linking
      ([RelaxedHoareLink], 3c.6) remain open.

    ** Provisional research-level choices (research-intent.md §7, not yet
       decided by the author)

    - D1 (semantic layering): the composite cc;⟦M⟧ is [M] run over the
      LTS [ModLTS VF idF], not a syntactic inlining.
    - D2 (saturation only on the E-side, over specification
      presentations): [absorb] is to be proved only under [CCClosed]
      (instances: [EI], [EIhl] from an empty pending list), because it
      is false in general ([absorb_needs_closure]).  [unabsorb] needs no
      such restriction.  The F-side is not attempted (the plan expects
      it to be false without SI inheritance, sub-task 3c.9).
    - D3 (verimpl in copy-cat form) concerns [RelaxedHoareLink]; nothing
      here depends on it.

    ** Known limitations

    - [absorb] is pending; so are [absorb_ei], [saturate_ei],
      [cc_idem_ei], [rcomplin_paper], [rlhl_sound_paper] (plan 3c.5).
    - The counterexample relies on programs reading raw handles
      ([future_handle]); a language without that would need the plan's
      second counterexample (D), response blocking, which is not
      mechanized.
    - No error transitions (latest-review m-8): [ModLTS] and [EI] have
      [Error := False]. *)

Require Import Stdlib.Lists.List.
Require Import Stdlib.Arith.PeanoNat.
Require Import Stdlib.PArith.PArith.
Require Import Stdlib.micromega.Lia.
Require Import Stdlib.Sorting.Permutation.

Require Import models.EffectSignatures.
Require Import models.RelaxedSignature.
Require Import models.LinCCAL.
Require Import models.simlin.RelaxedLTS.
Require Import models.simlin.RelaxedLang.
Require Import models.simlin.RelaxedSemantics.
Require Import models.simlin.RelaxedModuleSemantics.
Require Import models.simlin.RelaxedModuleFacts.
Require Import models.simlin.RelaxedTraceLin.
Require Import models.simlin.RelaxedGSim.
Require Import models.view.ViewLHL.
Require Import models.simlin.RelaxedHoareSpec.
Require Import models.simlin.RelaxedHoareCompLin.
Require Import models.simlin.RelaxedHoareCompLinSpec.
Require Import models.simlin.RelaxedHoareLayer.

Import ListNotations.


Module RelaxedHoareAbsorb.
  Import LinCCALBase.
  Import RelaxedSig.
  Import RelaxedLTSSpec.
  Import RelaxedLang.
  Import RelaxedSemantics.
  Import RelaxedModuleSemantics.
  Import RelaxedGSim.
  Import RelaxedHoareCompLin.
  Import RelaxedHoareLayer.

  (** ** Event helpers *)

  Definition is_res {F : RelaxedSig.t} (e : ThreadEvent F) : Prop :=
    match te_ev F e with ResEv _ _ _ => True | InvEv _ _ => False end.

  Definition ikey {F : RelaxedSig.t} (e : ThreadEvent F) : list (CallKey F) :=
    match te_ev F e with InvEv h _ => [(te_tid F e, h)] | ResEv _ _ _ => [] end.

  Definition rkey {F : RelaxedSig.t} (e : ThreadEvent F) : list (CallKey F) :=
    match te_ev F e with ResEv h _ _ => [(te_tid F e, h)] | InvEv _ _ => [] end.

  (** The keys of the responses of a trace, in order. *)
  Definition response_keys {F : RelaxedSig.t} (l : list (ThreadEvent F)) : list (CallKey F) :=
    flat_map rkey l.

  Lemma invocation_keys_flat {F : RelaxedSig.t} (l : list (ThreadEvent F)) :
    invocation_keys l = flat_map ikey l.
  Proof.
    induction l as [| e l IH]; [reflexivity |]. cbn. unfold ikey.
    destruct (te_ev F e); cbn; rewrite IH; reflexivity.
  Qed.

  Lemma response_keys_app {F : RelaxedSig.t} (l l' : list (ThreadEvent F)) :
    response_keys (l ++ l') = response_keys l ++ response_keys l'.
  Proof. apply flat_map_app. Qed.

  Lemma rkey_in {F : RelaxedSig.t} (e : ThreadEvent F) k :
    In k (rkey e) <-> is_res e /\ te_key e = k.
  Proof.
    destruct e as [t [h o | h o r]]; cbn; split.
    - intros [].
    - intros [[] _].
    - intros [<- | []]. split; [exact Logic.I | reflexivity].
    - intros [_ <-]. left. reflexivity.
  Qed.

  Lemma in_ikeys {F : RelaxedSig.t} (l : list (ThreadEvent F)) t h o :
    In (Build_ThreadEvent t (@InvEv F h o)) l -> In (t, h) (invocation_keys l).
  Proof.
    intros Hin. rewrite invocation_keys_flat. apply in_flat_map.
    exists (Build_ThreadEvent t (InvEv h o)). split; [exact Hin | left; reflexivity].
  Qed.

  Lemma in_rkeys {F : RelaxedSig.t} (l : list (ThreadEvent F)) e :
    In e l -> is_res e -> In (te_key e) (response_keys l).
  Proof.
    intros Hin Hr. apply in_flat_map. exists e. split; [exact Hin | apply rkey_in; auto].
  Qed.

  Lemma perm_ikeys {F : RelaxedSig.t} (l l' : list (ThreadEvent F)) :
    Permutation l l' -> Permutation (invocation_keys l) (invocation_keys l').
  Proof. intros Hp. rewrite !invocation_keys_flat. apply Permutation_flat_map. exact Hp. Qed.

  Lemma perm_rkeys {F : RelaxedSig.t} (l l' : list (ThreadEvent F)) :
    Permutation l l' -> Permutation (response_keys l) (response_keys l').
  Proof. intros Hp. apply Permutation_flat_map. exact Hp. Qed.

  (** In a list whose [f]-images are disjoint, a key identifies a
      position. *)
  Lemma nodup_flat_map_pos {A B : Type} (f : A -> list B) (l : list A) j1 j2 a1 a2 k :
    NoDup (flat_map f l) -> nth_error l j1 = Some a1 -> nth_error l j2 = Some a2 ->
    In k (f a1) -> In k (f a2) -> j1 = j2.
  Proof.
    revert j1 j2. induction l as [| x l IH]; intros j1 j2 Hnd H1 H2 Hk1 Hk2; [destruct j1; discriminate |].
    cbn in Hnd. destruct j1 as [| j1], j2 as [| j2]; cbn in H1, H2.
    - reflexivity.
    - apply some_inj in H1. subst x. exfalso.
      apply (RelaxedModuleFacts.nodup_app_disj _ _ k Hnd Hk1).
      apply in_flat_map. exists a2. split; [exact (nth_error_In _ _ H2) | exact Hk2].
    - apply some_inj in H2. subst x. exfalso.
      apply (RelaxedModuleFacts.nodup_app_disj _ _ k Hnd Hk2).
      apply in_flat_map. exists a1. split; [exact (nth_error_In _ _ H1) | exact Hk1].
    - f_equal. apply (IH j1 j2); auto. eapply NoDup_app_remove_l. exact Hnd.
  Qed.

  (** Two responses of a trace with distinct response keys and the same
      key are the same event. *)
  Lemma res_unique {F : RelaxedSig.t} (l : list (ThreadEvent F)) e1 e2 :
    NoDup (response_keys l) -> In e1 l -> In e2 l -> is_res e1 -> is_res e2 -> te_key e1 = te_key e2 -> e1 = e2.
  Proof.
    intros Hnd H1 H2 Hr1 Hr2 Hk.
    apply In_nth_error in H1 as (j1 & H1). apply In_nth_error in H2 as (j2 & H2).
    assert (j1 = j2) as <-.
    { apply (nodup_flat_map_pos rkey l j1 j2 e1 e2 (te_key e1) Hnd H1 H2);
        apply rkey_in; auto. }
    rewrite H1 in H2. exact (some_inj _ _ H2).
  Qed.

  (** Same-thread crossing is decided by [must_precede] alone (thread
      identifiers are [positive], so equality is decidable). *)
  Lemma cross_of_not_mp {E : RelaxedSig.t} (a b : TaggedEvent E) :
    ~ must_precede a b -> tagged_can_cross a b.
  Proof.
    intros H. destruct (Pos.eq_dec (te_tid E (untag a)) (te_tid E (untag b))) as [Heq | Hne].
    - right. split; assumption.
    - left. exact Hne.
  Qed.

  (** ** Facts about a single method trace

      [produced_inv_answered]: every invocation of a trace produced by a
      method body is answered later in the same trace, with the same
      handle and operation ([program_terminal] requires every future to
      be resolved).  [produced_res_invoked]: every response answers an
      earlier invocation of the same handle and operation.
      [produced_rkeys_nodup]: a handle is answered at most once.  All
      three compare results through events only (no [eq_rect_eq]). *)

  Section LocalTraces.
    Context {E : RelaxedSig.t} {R : Type}.

    Lemma resolve_store_keep (h0 : RelaxedSig.handle E) op0 (r0 : Sig.ar op0) (H H' : FutureStore E) e :
      resolve_store h0 op0 r0 H H' -> In e H -> In e H' \/ e = Build_FutureEntry h0 (Pending op0).
    Proof.
      induction 1 as [tail | h' cell H H' Hneq Hres IH]; intros He; cbn in *.
      - destruct He as [<- | He]; [right; reflexivity | left; right; exact He].
      - destruct He as [<- | He]; [left; left; reflexivity |].
        destruct (IH He) as [H1 | H1]; [left; right; exact H1 | right; exact H1].
    Qed.

    Lemma pending_entry_eq (h h' : RelaxedSig.handle E) op op' :
      Build_FutureEntry h (Pending op) = Build_FutureEntry h' (Pending op') -> h = h' /\ op = op'.
    Proof.
      intros Heq. split; [exact (f_equal (fe_handle E) Heq) |].
      exact (f_equal (fun e => match fe_cell E e with Pending o => o | Resolved o _ => o end) Heq).
    Qed.

    Lemma pending_not_resolved' (h h' : RelaxedSig.handle E) op op' (x : Sig.ar op') :
      Build_FutureEntry h (Pending op) <> Build_FutureEntry h' (Resolved op' x).
    Proof. intros Heq. apply (f_equal (fe_cell E)) in Heq. discriminate Heq. Qed.

    Lemma exec_pending_answered t (c : ProgramConfig E R) tr c' :
      program_execution_tagged t c tr c' ->
      forall h op, pending_at h op (pc_futures c) ->
      (exists j (ret : Sig.ar op), nth_error (map untag tr) j = Some (Build_ThreadEvent t (@ResEv E h op ret))) \/
      pending_at h op (pc_futures c').
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hstep Hex IH | c1 c2 c3 m tr Hstep Hex IH]; intros h op Hp.
      - right. exact Hp.
      - apply IH. inversion Hstep; subst; exact Hp.
      - assert (Hcase : pending_at h op (pc_futures c2) \/
                        exists ret : Sig.ar op, untag m = Build_ThreadEvent t (@ResEv E h op ret)).
        { inversion Hstep; subst; cbn in *.
          - left. right. exact Hp.
          - left. right. exact Hp.
          - destruct (resolve_store_keep _ _ _ _ _ _ Hresolve Hp) as [Hk | Heq]; [left; exact Hk |].
            right. destruct (pending_entry_eq _ _ _ _ Heq) as [-> ->]. exists ret. reflexivity.
          - destruct (resolve_store_keep _ _ _ _ _ _ Hresolve Hp) as [Hk | Heq]; [left; exact Hk |].
            right. destruct (pending_entry_eq _ _ _ _ Heq) as [-> ->]. exists ret. reflexivity. }
        destruct Hcase as [Hp2 | (ret & Hm)].
        + destruct (IH h op Hp2) as [(j & ret & Hj) | Hend]; [left | right; exact Hend].
          exists (S j), ret. exact Hj.
        + left. exists 0, ret. cbn. rewrite <- Hm. reflexivity.
    Qed.

    Lemma exec_inv_answered t (c : ProgramConfig E R) tr c' :
      program_execution_tagged t c tr c' ->
      forall j h op, nth_error (map untag tr) j = Some (Build_ThreadEvent t (@InvEv E h op)) ->
      (exists j' (ret : Sig.ar op), j < j' /\
         nth_error (map untag tr) j' = Some (Build_ThreadEvent t (@ResEv E h op ret))) \/
      pending_at h op (pc_futures c').
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hstep Hex IH | c1 c2 c3 m tr Hstep Hex IH]; intros j h op Hj.
      - destruct j; discriminate.
      - exact (IH j h op Hj).
      - destruct j as [| j]; cbn in Hj.
        + apply some_inj in Hj.
          assert (Hp2 : pending_at h op (pc_futures c2)).
          { inversion Hstep; subst; cbn in *; try discriminate Hj.
            - injection Hj as -> ->. left. reflexivity.
            - injection Hj as -> ->. left. reflexivity. }
          destruct (exec_pending_answered _ _ _ _ Hex h op Hp2) as [(j' & ret & Hj') | Hend].
          * left. exists (S j'), ret. split; [lia | exact Hj'].
          * right. exact Hend.
        + destruct (IH j h op Hj) as [(j' & ret & Hlt & Hj') | Hend].
          * left. exists (S j'), ret. split; [lia | exact Hj'].
          * right. exact Hend.
    Qed.

    Theorem produced_inv_answered t (p : Prog E R) tr (r : R) j h op :
      program_produces_tagged t p tr r ->
      nth_error (map untag tr) j = Some (Build_ThreadEvent t (@InvEv E h op)) ->
      exists j' (ret : Sig.ar op), j < j' /\
        nth_error (map untag tr) j' = Some (Build_ThreadEvent t (@ResEv E h op ret)).
    Proof.
      intros (c' & Hex & Hterm) Hj.
      destruct (exec_inv_answered _ _ _ _ Hex j h op Hj) as [H | Hp]; [exact H |].
      exfalso. inversion Hterm as [H0 r0 Hres]; subst. cbn in Hp.
      unfold all_resolved in Hres. rewrite Forall_forall in Hres. exact (Hres _ Hp).
    Qed.

    Lemma exec_res_invoked t (c : ProgramConfig E R) tr c' :
      program_execution_tagged t c tr c' ->
      forall j h op (ret : Sig.ar op),
        nth_error (map untag tr) j = Some (Build_ThreadEvent t (@ResEv E h op ret)) ->
        (exists i, i < j /\ nth_error (map untag tr) i = Some (Build_ThreadEvent t (@InvEv E h op))) \/
        pending_at h op (pc_futures c).
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hstep Hex IH | c1 c2 c3 m tr Hstep Hex IH]; intros j h op ret Hj.
      - destruct j; discriminate.
      - destruct (IH j h op ret Hj) as [Hi | Hp]; [left; exact Hi | right].
        inversion Hstep; subst; exact Hp.
      - destruct j as [| j]; cbn in Hj.
        + apply some_inj in Hj. right.
          inversion Hstep; subst; cbn in *; try discriminate Hj.
          * pose proof (f_equal (fun e => event_handle (te_ev E e)) Hj) as Hh.
            pose proof (f_equal (fun e => event_op (te_ev E e)) Hj) as Ho. cbn in Hh, Ho. subst.
            exact (resolve_store_pending _ _ _ _ _ Hresolve).
          * pose proof (f_equal (fun e => event_handle (te_ev E e)) Hj) as Hh.
            pose proof (f_equal (fun e => event_op (te_ev E e)) Hj) as Ho. cbn in Hh, Ho. subst.
            exact (resolve_store_pending _ _ _ _ _ Hresolve).
        + destruct (IH j h op ret Hj) as [(i & Hi & Hij) | Hp].
          * left. exists (S i). split; [lia | exact Hij].
          * inversion Hstep; subst; cbn in *.
            -- destruct Hp as [Heq | Hp]; [| right; exact Hp].
               destruct (pending_entry_eq _ _ _ _ Heq) as [<- <-].
               left. exists 0. split; [lia | reflexivity].
            -- destruct Hp as [Heq | Hp]; [| right; exact Hp].
               destruct (pending_entry_eq _ _ _ _ Heq) as [<- <-].
               left. exists 0. split; [lia | reflexivity].
            -- destruct (RelaxedModuleFacts.resolve_store_back _ _ _ _ _ Hresolve _ Hp) as [H1 | H1];
                 [right; exact H1 | exfalso; exact (pending_not_resolved' _ _ _ _ _ H1)].
            -- destruct (RelaxedModuleFacts.resolve_store_back _ _ _ _ _ Hresolve _ Hp) as [H1 | H1];
                 [right; exact H1 | exfalso; exact (pending_not_resolved' _ _ _ _ _ H1)].
    Qed.

    Theorem produced_res_invoked t (p : Prog E R) tr (r : R) j h op (ret : Sig.ar op) :
      program_produces_tagged t p tr r ->
      nth_error (map untag tr) j = Some (Build_ThreadEvent t (@ResEv E h op ret)) ->
      exists i, i < j /\ nth_error (map untag tr) i = Some (Build_ThreadEvent t (@InvEv E h op)).
    Proof.
      intros (c' & Hex & _) Hj.
      destruct (exec_res_invoked _ _ _ _ Hex j h op ret Hj) as [H | Hp]; [exact H |].
      destruct Hp.
    Qed.

    (** A handle that is present and no longer pending is never answered
        again. *)
    Lemma exec_done_no_res t (c : ProgramConfig E R) tr c' :
      program_execution_tagged t c tr c' ->
      forall h, In h (map (fe_handle E) (pc_futures c)) -> (forall op, ~ pending_at h op (pc_futures c)) ->
      ~ In (t, h) (response_keys (map untag tr)).
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hstep Hex IH | c1 c2 c3 m tr Hstep Hex IH]; intros h Hin Hnp.
      - intros [].
      - apply IH; inversion Hstep; subst; assumption.
      - inversion Hstep; subst; cbn [map untag tev_ev] in *; unfold response_keys in *; cbn [flat_map rkey te_ev te_tid app] in *.
        + apply IH.
          * right. exact Hin.
          * intros op' [Heq | Hp].
            -- destruct (pending_entry_eq _ _ _ _ Heq) as [Hh _]. subst. exact (Hfresh Hin).
            -- exact (Hnp op' Hp).
        + apply IH.
          * right. exact Hin.
          * intros op' [Heq | Hp].
            -- destruct (pending_entry_eq _ _ _ _ Heq) as [Hh _]. subst. exact (Hfresh Hin).
            -- exact (Hnp op' Hp).
        + intros [Heq | Hk].
          * injection Heq as Hh. subst. exact (Hnp _ (resolve_store_pending _ _ _ _ _ Hresolve)).
          * apply (IH h); [| | exact Hk].
            -- exact (eq_ind _ (fun l => In h l) Hin _ (resolve_store_handles _ _ _ _ _ Hresolve)).
            -- intros op' Hp. destruct (RelaxedModuleFacts.resolve_store_back _ _ _ _ _ Hresolve _ Hp) as [H1 | H1];
                 [exact (Hnp op' H1) | exact (pending_not_resolved' _ _ _ _ _ H1)].
        + intros [Heq | Hk].
          * injection Heq as Hh. subst. exact (Hnp _ (resolve_store_pending _ _ _ _ _ Hresolve)).
          * apply (IH h); [| | exact Hk].
            -- exact (eq_ind _ (fun l => In h l) Hin _ (resolve_store_handles _ _ _ _ _ Hresolve)).
            -- intros op' Hp. destruct (RelaxedModuleFacts.resolve_store_back _ _ _ _ _ Hresolve _ Hp) as [H1 | H1];
                 [exact (Hnp op' H1) | exact (pending_not_resolved' _ _ _ _ _ H1)].
    Qed.

    Lemma exec_rkeys_nodup t (c : ProgramConfig E R) tr c' :
      program_execution_tagged t c tr c' -> store_well_formed (pc_futures c) ->
      NoDup (response_keys (map untag tr)).
    Proof.
      induction 1 as [c | c1 c2 c3 tr Hstep Hex IH | c1 c2 c3 m tr Hstep Hex IH]; intros Hwf.
      - constructor.
      - apply IH. exact (program_step_store_well_formed _ _ _ _ (program_step_tagged_untag _ _ _ _ Hstep) Hwf).
      - pose proof (program_step_store_well_formed _ _ _ _ (program_step_tagged_untag _ _ _ _ Hstep) Hwf) as Hwf2.
        specialize (IH Hwf2).
        inversion Hstep; subst; cbn [map untag tev_ev] in *; unfold response_keys in *;
          cbn [flat_map rkey te_ev te_tid app] in *; try exact IH.
        + constructor; [| exact IH].
          apply (exec_done_no_res _ _ _ _ Hex h).
          * apply in_map_iff. exists (Build_FutureEntry h (Resolved op ret)).
            split; [reflexivity | exact (resolve_store_resolved _ _ _ _ _ Hresolve)].
          * intros op' Hp.
            pose proof (RelaxedModuleFacts.nodup_map_inj (fe_handle E) _ _ _ Hwf2 Hp
                          (resolve_store_resolved _ _ _ _ _ Hresolve) eq_refl) as Heq.
            exact (pending_not_resolved' _ _ _ _ _ Heq).
        + constructor; [| exact IH].
          apply (exec_done_no_res _ _ _ _ Hex h).
          * apply in_map_iff. exists (Build_FutureEntry h (Resolved op ret)).
            split; [reflexivity | exact (resolve_store_resolved _ _ _ _ _ Hresolve)].
          * intros op' Hp.
            pose proof (RelaxedModuleFacts.nodup_map_inj (fe_handle E) _ _ _ Hwf2 Hp
                          (resolve_store_resolved _ _ _ _ _ Hresolve) eq_refl) as Heq.
            exact (pending_not_resolved' _ _ _ _ _ Heq).
    Qed.

    Theorem produced_rkeys_nodup t (p : Prog E R) tr (r : R) :
      program_produces_tagged t p tr r -> NoDup (response_keys (map untag tr)).
    Proof.
      intros (c' & Hex & _). exact (exec_rkeys_nodup _ _ _ _ Hex empty_store_well_formed).
    Qed.
  End LocalTraces.

  (** ** Well-formed underlay traces are copy-cat traces

      [CCWF u]: invocation keys are distinct, response keys are distinct,
      every response answers an earlier invocation of the same key and
      operation, and every invocation has a result to commit to that
      agrees with every response of its key in [u] (for an answered
      invocation this is its response; for a pending one it is the only
      place where a value of the arity is needed).
      [rtraces_of_ccwf]: a [CCWF] path of [V] is a copy-cat trace over
      [V].  The copy-cat replays [u]: an invocation of [k] is the
      copy-cat's overlay invocation of [k] with underlay handle [snd k]
      and the committed result, immediately followed by the emission of
      its underlay invocation (the [V] step of [u]); a response of [k] is
      the emission of the underlay response followed by the overlay
      return.  The copy-cat's queue then holds only pending responses, so
      every emission is on the frontier (a response never blocks an
      untagged invocation or another response). *)

  Record CCWF {F : RelaxedSig.t} (u : list (ThreadEvent F)) : Prop := {
    ccwf_inv_nodup : NoDup (invocation_keys u);
    ccwf_res_nodup : NoDup (response_keys u);
    ccwf_res_inv : forall j t h op (r : Sig.ar op),
        nth_error u j = Some (Build_ThreadEvent t (@ResEv F h op r)) ->
        exists i, i < j /\ nth_error u i = Some (Build_ThreadEvent t (@InvEv F h op));
    ccwf_commit : forall t h op, In (Build_ThreadEvent t (@InvEv F h op)) u ->
        exists r : Sig.ar op, forall e, In e u -> is_res e -> te_key e = (t, h) ->
          e = Build_ThreadEvent t (@ResEv F h op r);
  }.

  Section CopyCatOfWF.
    Context {F : RelaxedSig.t} (V : LTS F) (v0 : State V) (u : list (ThreadEvent F)) (Hwf : CCWF u).

    Abbreviation Cfg := (@TaggedModuleConfig F F V).

    (** The response event an active copy-cat call has committed to. *)
    Definition cell_resev (en : CallEntry F) : option (ThreadEvent F) :=
      match ce_cell F en with
      | ActiveCall o x => Some (Build_ThreadEvent (ce_tid F en) (@ResEv F (ce_handle F en) o x))
      | DeadCall => None
      end.

    (** The copy-cat configuration [c] reached after replaying the prefix
        [p] of [u]. *)
    Record CCU (p : list (ThreadEvent F)) (c : Cfg) : Prop := {
      ccu_keys : forall k, In k (map call_key (tm_calls c)) <-> In k (invocation_keys p);
      ccu_used : forall k, In k (tm_used_underlay c) -> In k (invocation_keys p);
      ccu_nodup : NoDup (map call_key (tm_calls c));
      ccu_active : forall en ev, In en (tm_calls c) -> cell_resev en = Some ev ->
          In (Build_TaggedScheduledEvent (call_key en) (Build_TaggedEvent ev no_deps)) (tm_queue c) /\
          forall e, In e u -> is_res e -> te_key e = call_key en -> e = ev;
      ccu_dead : forall t h, In (Build_CallEntry t h DeadCall) (tm_calls c) ->
          exists j e, j < length p /\ nth_error u j = Some e /\ is_res e /\ te_key e = (t, h);
      ccu_queue : forall x, In x (tm_queue c) ->
          is_res (untag (ts_event x)) /\ In (ts_owner x) (map call_key (tm_calls c));
      ccu_owners : NoDup (map ts_owner (tm_queue c));
    }.

    Lemma ccu_init : CCU [] (initial_tagged_module V v0).
    Proof.
      constructor; cbn.
      - intros k. split; intros [].
      - intros k [].
      - constructor.
      - intros en ev [].
      - intros t h [].
      - intros x [].
      - constructor.
    Qed.

    Lemma res_cross (y x : TaggedEvent F) :
      is_res (untag y) -> (is_res (untag x) \/ forall h, ~ tev_deps x h) -> tagged_can_cross y x.
    Proof.
      intros Hy Hx. apply cross_of_not_mp. unfold must_precede, is_res in *.
      destruct (te_ev F (untag y)) as [h1 o1 | h1 o1 r1]; [destruct Hy |].
      destruct (te_ev F (untag x)) as [h2 o2 | h2 o2 r2].
      - destruct Hx as [[] | Hx]. exact (Hx h1).
      - intros [].
    Qed.

    Lemma finish_call_dead_in t h op (ret : Sig.ar op) (pool pool' : CallPool F) :
      finish_call t h op ret pool pool' -> In (Build_CallEntry t h DeadCall) pool'.
    Proof. induction 1; [left; reflexivity | right; assumption]. Qed.

    Lemma finish_call_back t h op (ret : Sig.ar op) (pool pool' : CallPool F) en :
      finish_call t h op ret pool pool' -> In en pool' -> In en pool \/ en = Build_CallEntry t h DeadCall.
    Proof.
      induction 1 as [tail | t' h' cell pool pool' Hneq Hf IH]; intros [<- | Hin].
      - right. reflexivity.
      - left. right. exact Hin.
      - left. left. reflexivity.
      - destruct (IH Hin) as [H1 | H1]; [left; right; exact H1 | right; exact H1].
    Qed.

    Lemma cc_loop vEnd : forall rest p (c : Cfg) evs,
      u = p ++ rest -> vf_path V (tm_lts_state c) rest vEnd ->
      module_execution_tagged V idF (initial_tagged_module V v0) evs c -> overlay_events evs = p ->
      CCU p c -> RTraces V v0 u.
    Proof.
      induction rest as [| e rest IH]; intros p c evs Hu Hp Hex Hov Hc.
      - exists evs, c. split; [exact Hex |]. rewrite Hov, Hu, app_nil_r. reflexivity.
      - destruct (ViewLHL.vf_path_cons_inv V _ _ _ _ Hp) as (v1 & Hs & Hp').
        assert (Hpos : nth_error u (length p) = Some e)
          by (rewrite Hu, nth_error_app2, Nat.sub_diag by lia; reflexivity).
        assert (Hin_u : In e u) by (rewrite Hu; apply in_elt).
        destruct c as [q pool Q used]. cbn [tm_lts_state tm_calls tm_queue tm_used_underlay] in *.
        destruct e as [t [h op | h op r]].
        + (* an invocation of [(t, h)] *)
          destruct (ccwf_commit _ Hwf t h op Hin_u) as (r & Hr).
          assert (Hnin : ~ In (t, h) (invocation_keys p)).
          { pose proof (ccwf_inv_nodup _ Hwf) as Hnd. rewrite Hu, RelaxedHoareCompLinSpec.invocation_keys_app in Hnd. cbn in Hnd.
            intros Hk. apply (NoDup_remove_2 _ _ _ Hnd). apply in_or_app. left. exact Hk. }
          assert (Hfresh : call_fresh (t, h) pool) by (intros Hk; exact (Hnin (proj1 (ccu_keys _ _ Hc _) Hk))).
          assert (Hft : trace_fresh used (map untag [cc_inv_ev t h op; cc_res_ev t h op r])).
          { split; cbn.
            - constructor; [intros [] | constructor].
            - intros k [<- | []] Hk. exact (Hnin (ccu_used _ _ Hc _ Hk)). }
          pose proof (tagged_invoke V idF t h op q pool Q used _ r Hfresh (idF_produces t h op r) Hft) as Hst1.
          assert (Hsel : select_frontier_tagged (ient (t, h) op) (Q ++ ient (t, h) op :: [rent (t, h) op r])
                           (Q ++ [rent (t, h) op r])).
          { apply select_of_cross. intros y Hy. apply res_cross; [exact (proj1 (ccu_queue _ _ Hc y Hy)) |].
            right. intros h' Hh'. exact (resolved_in_empty h' Hh'). }
          pose proof (tagged_underlay V idF (ient (t, h) op) q v1 (Build_CallEntry t h (ActiveCall op r) :: pool)
                        _ _ (used ++ [(t, h)]) Hsel Hs) as Hst2.
          apply (IH (p ++ [Build_ThreadEvent t (InvEv h op)])
                    (Build_TaggedModuleConfig v1 (Build_CallEntry t h (ActiveCall op r) :: pool)
                       (Q ++ [rent (t, h) op r]) (used ++ [(t, h)]))
                    (evs ++ [OverlayEvent (Build_ThreadEvent t (InvEv h op));
                             UnderlayEvent (Build_ThreadEvent t (InvEv h op))])).
          * rewrite Hu, <- app_assoc. reflexivity.
          * exact Hp'.
          * change (evs ++ [OverlayEvent (Build_ThreadEvent t (InvEv h op));
                            UnderlayEvent (Build_ThreadEvent t (InvEv h op))])
              with (evs ++ [OverlayEvent (Build_ThreadEvent t (InvEv h op))] ++
                           [UnderlayEvent (untag (ts_event (ient (t, h) op)))]).
            rewrite app_assoc. apply (exec_snoc _ _ _ _ _ _ _ (exec_snoc _ _ _ _ _ _ _ Hex Hst1)). exact Hst2.
          * rewrite overlay_events_app, Hov. reflexivity.
          * constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay map call_key ce_tid ce_handle].
            -- intros k. rewrite RelaxedHoareCompLinSpec.invocation_keys_app. cbn. rewrite (ccu_keys _ _ Hc k).
               split; [intros [<- | Hk]; apply in_or_app; [right; left; reflexivity | left; exact Hk] |].
               intros Hk. apply in_app_or in Hk as [Hk | [<- | []]]; [right; exact Hk | left; reflexivity].
            -- intros k Hk. rewrite RelaxedHoareCompLinSpec.invocation_keys_app. cbn. apply in_app_or in Hk as [Hk | [<- | []]].
               ++ apply in_or_app. left. exact (ccu_used _ _ Hc _ Hk).
               ++ apply in_or_app. right. left. reflexivity.
            -- constructor; [exact Hfresh | exact (ccu_nodup _ _ Hc)].
            -- intros en ev [<- | Hen] Hev.
               ++ cbn in Hev. apply some_inj in Hev. subst ev. split.
                  ** apply in_or_app. right. left. reflexivity.
                  ** intros e He Hre Hke. exact (Hr e He Hre Hke).
               ++ destruct (ccu_active _ _ Hc en ev Hen Hev) as (Hq & Hue).
                  split; [apply in_or_app; left; exact Hq | exact Hue].
            -- intros t' h' [Heq | Hin].
               ++ apply (f_equal (ce_cell F)) in Heq. discriminate Heq.
               ++ destruct (ccu_dead _ _ Hc t' h' Hin) as (j & e & Hj & Hje & Hre & Hke).
                  exists j, e. rewrite length_app. cbn. split; [lia | auto].
            -- intros x Hx. apply in_app_or in Hx as [Hx | [<- | []]].
               ++ destruct (ccu_queue _ _ Hc x Hx) as (Hrx & Hox). split; [exact Hrx | right; exact Hox].
               ++ split; [exact Logic.I | left; reflexivity].
            -- rewrite map_app. apply RelaxedModuleFacts.nodup_snoc; [exact (ccu_owners _ _ Hc) |].
               intros Ho. apply in_map_iff in Ho as (x & Hxo & Hx).
               apply Hfresh. cbn in Hxo. rewrite <- Hxo. exact (proj2 (ccu_queue _ _ Hc x Hx)).
        + (* a response of [(t, h)] *)
          destruct (ccwf_res_inv _ Hwf (length p) t h op r Hpos) as (i & Hi & Hpi).
          assert (Hkp : In (t, h) (invocation_keys p)).
          { rewrite Hu, nth_error_app1 in Hpi by exact Hi. apply (in_ikeys p t h op). exact (nth_error_In _ _ Hpi). }
          apply (ccu_keys _ _ Hc) in Hkp. apply in_map_iff in Hkp as ([t0 h0 cell] & Hk0 & Hen).
          cbn in Hk0. injection Hk0 as -> ->.
          destruct cell as [op0 r0 |].
          * destruct (ccu_active _ _ Hc _ (Build_ThreadEvent t (ResEv h op0 r0)) Hen eq_refl) as (Hq & Hue).
            pose proof (Hue _ Hin_u Logic.I eq_refl) as Heq. clear Hue.
            rewrite Heq in Hs, Hpos, Hin_u, Hu. clear Heq.
            cbn [tm_queue] in Hq. apply in_split in Hq as (pre & post & ->).
            assert (Hsel : select_frontier_tagged (rent (t, h) op0 r0) (pre ++ rent (t, h) op0 r0 :: post) (pre ++ post)).
            { apply select_of_cross. intros y Hy. apply res_cross.
              - apply (proj1 (ccu_queue _ _ Hc y ltac:(apply in_or_app; left; exact Hy))).
              - left. exact Logic.I. }
            pose proof (tagged_underlay V idF (rent (t, h) op0 r0) q v1 pool _ _ used Hsel Hs) as Hst1.
            destruct (finish_of_in t h op0 r0 pool (ccu_nodup _ _ Hc) Hen) as (pool' & Hfin).
            pose proof (ccu_owners _ _ Hc) as Hown. cbn [tm_queue] in Hown. rewrite map_app in Hown. cbn in Hown.
            assert (Hdone : owner_done_tagged (t, h) (pre ++ post)).
            { unfold owner_done_tagged. rewrite map_app. exact (NoDup_remove_2 _ _ _ Hown). }
            pose proof (tagged_return V idF t h op0 r0 v1 pool pool' (pre ++ post) used Hfin Hdone) as Hst2.
            apply (IH (p ++ [Build_ThreadEvent t (ResEv h op0 r0)])
                      (Build_TaggedModuleConfig v1 pool' (pre ++ post) used)
                      (evs ++ [UnderlayEvent (Build_ThreadEvent t (ResEv h op0 r0));
                               OverlayEvent (Build_ThreadEvent t (ResEv h op0 r0))])).
            -- rewrite Hu, <- app_assoc. reflexivity.
            -- exact Hp'.
            -- change (evs ++ [UnderlayEvent (Build_ThreadEvent t (ResEv h op0 r0));
                              OverlayEvent (Build_ThreadEvent t (ResEv h op0 r0))])
                 with (evs ++ [UnderlayEvent (untag (ts_event (rent (t, h) op0 r0)))] ++
                              [OverlayEvent (Build_ThreadEvent t (ResEv h op0 r0))]).
               rewrite app_assoc. apply (exec_snoc _ _ _ _ _ _ _ (exec_snoc _ _ _ _ _ _ _ Hex Hst1)). exact Hst2.
            -- rewrite overlay_events_app, Hov. reflexivity.
            -- pose proof (finish_call_keys _ _ _ _ _ _ Hfin) as Hkeys.
               constructor; cbn [tm_lts_state tm_calls tm_queue tm_used_underlay].
               ++ intros k. rewrite <- Hkeys, RelaxedHoareCompLinSpec.invocation_keys_app, app_nil_r. exact (ccu_keys _ _ Hc k).
               ++ intros k Hk. rewrite RelaxedHoareCompLinSpec.invocation_keys_app, app_nil_r. exact (ccu_used _ _ Hc k Hk).
               ++ rewrite <- Hkeys. exact (ccu_nodup _ _ Hc).
               ++ intros [t' h' cell'] ev Hen' Hev. destruct cell' as [o' x' |]; [| discriminate Hev].
                  cbn in Hev. apply some_inj in Hev. subst ev.
                  pose proof (RelaxedModuleFacts.finish_call_active_preserved _ _ _ _ _ _ Hfin _ _ _ _ Hen') as Hen0.
                  assert (Hne : (t', h') <> (t, h)).
                  { intros Hk. pose proof (RelaxedModuleFacts.nodup_map_inj call_key pool' _ _
                      ltac:(rewrite <- Hkeys; exact (ccu_nodup _ _ Hc)) Hen' (finish_call_dead_in _ _ _ _ _ _ Hfin) Hk) as Heq.
                    apply (f_equal (ce_cell F)) in Heq. discriminate Heq. }
                  destruct (ccu_active _ _ Hc _ _ Hen0 eq_refl) as (Hq & Hue). split; [| exact Hue].
                  apply (in_remove_ne _ _ _ _ Hq). intros Heq. apply (f_equal ts_owner) in Heq. exact (Hne Heq).
               ++ intros t' h' Hd. destruct (finish_call_back _ _ _ _ _ _ _ Hfin Hd) as [Hd0 | Heq].
                  ** destruct (ccu_dead _ _ Hc t' h' Hd0) as (j & e & Hj & Hje & Hre & Hke).
                     exists j, e. rewrite length_app. cbn. split; [lia | auto].
                  ** apply (f_equal (fun en => (ce_tid F en, ce_handle F en))) in Heq. cbn in Heq.
                     injection Heq as -> ->.
                     exists (length p), (Build_ThreadEvent t (ResEv h op0 r0)).
                     rewrite length_app. cbn. split; [lia |]. split; [exact Hpos |]. split; [exact Logic.I | reflexivity].
               ++ intros x Hx. destruct (ccu_queue _ _ Hc x (in_remove_in _ _ _ _ Hx)) as (Hrx & Hox).
                  split; [exact Hrx | rewrite <- Hkeys; exact Hox].
               ++ rewrite map_app. exact (NoDup_remove_1 _ _ _ Hown).
          * exfalso. destruct (ccu_dead _ _ Hc t h Hen) as (j & e & Hj & Hje & Hre & Hke).
            assert (j = length p) as Hjp.
            { apply (nodup_flat_map_pos rkey _ j (length p) e (Build_ThreadEvent t (ResEv h op r)) (t, h)
                       (ccwf_res_nodup _ Hwf) Hje Hpos).
              - apply rkey_in. auto.
              - apply rkey_in. split; [exact Logic.I | reflexivity]. }
            lia.
    Qed.

    Theorem rtraces_of_ccwf : LPaths V v0 u -> RTraces V v0 u.
    Proof.
      intros (vEnd & Hp).
      apply (cc_loop vEnd u [] (initial_tagged_module V v0) []); [reflexivity | exact Hp | constructor | reflexivity |].
      exact ccu_init.
    Qed.
  End CopyCatOfWF.

  (** ** The underlay trace of every module execution is [CCWF]

      [UInv u c]: [u] is the underlay trace emitted so far and [c] the
      configuration reached.  The fields are stated over [u ++ qevs Q]
      (emitted events followed by the queued ones), which an underlay
      step only permutes.  Invocation keys are distinct and used
      ([trace_fresh]); response keys are distinct and invoked
      ([produced_rkeys_nodup], [produced_res_invoked]); every invocation
      has a committed result, read off the method trace of its call
      ([produced_inv_answered]); a queued response is preceded in the
      queue by its invocation, or the invocation was emitted; an emitted
      response was preceded by its emitted invocation ((F1)). *)

  Section UnderlayWF.
    Context {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F).

    Definition qevs (Q : TaggedQueue E F) : list (ThreadEvent E) := map (fun x => untag (ts_event x)) Q.

    Record UInv (u : list (ThreadEvent E)) (c : @TaggedModuleConfig E F VE) : Prop := {
      ui_ikeys : NoDup (invocation_keys (u ++ qevs (tm_queue c)));
      ui_used : forall k, In k (invocation_keys (u ++ qevs (tm_queue c))) -> In k (tm_used_underlay c);
      ui_rkeys : NoDup (response_keys (u ++ qevs (tm_queue c)));
      ui_rinv : forall k, In k (response_keys (u ++ qevs (tm_queue c))) ->
                          In k (invocation_keys (u ++ qevs (tm_queue c)));
      ui_commit : forall t h op, In (Build_ThreadEvent t (@InvEv E h op)) (u ++ qevs (tm_queue c)) ->
          exists r : Sig.ar op, forall e, In e (u ++ qevs (tm_queue c)) -> is_res e -> te_key e = (t, h) ->
            e = Build_ThreadEvent t (@ResEv E h op r);
      ui_qres : forall j y t h op (r : Sig.ar op), nth_error (tm_queue c) j = Some y ->
          untag (ts_event y) = Build_ThreadEvent t (@ResEv E h op r) ->
          (exists i x, i < j /\ nth_error (tm_queue c) i = Some x /\
                       untag (ts_event x) = Build_ThreadEvent t (@InvEv E h op)) \/
          In (Build_ThreadEvent t (@InvEv E h op)) u;
      ui_ures : forall j t h op (r : Sig.ar op), nth_error u j = Some (Build_ThreadEvent t (@ResEv E h op r)) ->
          exists i, i < j /\ nth_error u i = Some (Build_ThreadEvent t (@InvEv E h op));
    }.

    Lemma uinv_init (σ0 : State VE) : UInv [] (initial_tagged_module VE σ0).
    Proof.
      constructor; cbn.
      - constructor.
      - intros k [].
      - constructor.
      - intros k [].
      - intros t h op [].
      - intros j y t h op r Hj. destruct j; discriminate.
      - intros j t h op r Hj. destruct j; discriminate.
    Qed.

    Lemma qevs_app Q Q' : qevs (Q ++ Q') = qevs Q ++ qevs Q'.
    Proof. apply map_app. Qed.

    Lemma qevs_schedule (k : CallKey F) (tr : list (TaggedEvent E)) :
      qevs (schedule_trace_tagged k tr) = map untag tr.
    Proof. unfold qevs, schedule_trace_tagged. rewrite map_map. reflexivity. Qed.

    (** An overlay invocation enqueues a method trace. *)
    Lemma uinv_invoke u t h op q pool Q used tr (ret : Sig.ar op) :
      program_produces_tagged t (M op t) tr ret -> trace_fresh used (map untag tr) ->
      UInv u (Build_TaggedModuleConfig q pool Q used) ->
      UInv u (Build_TaggedModuleConfig q (Build_CallEntry t h (ActiveCall op ret) :: pool)
                (Q ++ schedule_trace_tagged (t, h) tr) (used ++ invocation_keys (map untag tr))).
    Proof.
      intros Hprod [Hftnd Hftu] Hu.
      set (L := map untag tr).
      assert (HW : u ++ qevs (Q ++ schedule_trace_tagged (t, h) tr) = (u ++ qevs Q) ++ L)
        by (rewrite qevs_app, qevs_schedule, app_assoc; reflexivity).
      pose proof (program_produces_tagged_trace_tid _ _ _ _ Hprod) as Htid.
      assert (HtidL : forall e, In e L -> te_tid E e = t).
      { intros e He. apply in_map_iff in He as (m & <- & Hm). rewrite Forall_forall in Htid. exact (Htid m Hm). }
      pose proof (produced_rkeys_nodup _ _ _ _ Hprod) as HrkL. fold L in HrkL.
      assert (HrinvL : forall k, In k (response_keys L) -> In k (invocation_keys L)).
      { intros k Hk. apply in_flat_map in Hk as (e & He & Hke). apply rkey_in in Hke as (Hre & Hke).
        destruct e as [t0 [h0 o0 | h0 o0 r0]]; [destruct Hre |]. cbn in Hke. subst k.
        pose proof (HtidL _ He) as Ht0. cbn in Ht0. subst t0.
        apply In_nth_error in He as (j & Hj).
        destruct (produced_res_invoked t _ _ _ j h0 o0 r0 Hprod Hj) as (i & _ & Hi).
        exact (in_ikeys L t h0 o0 (nth_error_In _ _ Hi)). }
      destruct Hu as [Hik Hus Hrk Hri Hcm Hqr Hur]. cbn [tm_queue tm_used_underlay] in *.
      assert (Hdisj : forall k, In k (invocation_keys (u ++ qevs Q)) -> ~ In k (invocation_keys L)).
      { intros k Hk HkL. exact (Hftu k HkL (Hus k Hk)). }
      constructor; cbn [tm_queue tm_used_underlay]; rewrite ?HW.
      - rewrite RelaxedHoareCompLinSpec.invocation_keys_app. apply NoDup_app; [exact Hik | exact Hftnd | exact Hdisj].
      - intros k Hk. rewrite RelaxedHoareCompLinSpec.invocation_keys_app in Hk. apply in_app_or in Hk as [Hk | Hk]; apply in_or_app;
          [left; exact (Hus k Hk) | right; exact Hk].
      - rewrite response_keys_app. apply NoDup_app; [exact Hrk | exact HrkL |].
        intros k Hk HkL. exact (Hdisj k (Hri k Hk) (HrinvL k HkL)).
      - intros k Hk. rewrite response_keys_app in Hk. rewrite RelaxedHoareCompLinSpec.invocation_keys_app.
        apply in_app_or in Hk as [Hk | Hk]; apply in_or_app; [left; exact (Hri k Hk) | right; exact (HrinvL k Hk)].
      - intros t' h' op' Hin. apply in_app_or in Hin as [Hin | Hin].
        + destruct (Hcm t' h' op' Hin) as (r & Hr). exists r. intros e He Hre Hke.
          apply in_app_or in He as [He | He]; [exact (Hr e He Hre Hke) |].
          exfalso. apply (Hdisj (t', h')); [exact (in_ikeys _ t' h' op' Hin) |].
          apply HrinvL. rewrite <- Hke. exact (in_rkeys L e He Hre).
        + pose proof (HtidL _ Hin) as Ht'. cbn in Ht'. subst t'.
          apply In_nth_error in Hin as (j & Hj).
          destruct (produced_inv_answered t _ _ _ j h' op' Hprod Hj) as (j' & r & _ & Hj').
          exists r. intros e He Hre Hke. apply in_app_or in He as [He | He].
          * exfalso. apply (Hdisj (t, h')); [| exact (in_ikeys L t h' op' (nth_error_In _ _ Hj))].
            apply Hri. rewrite <- Hke. exact (in_rkeys _ e He Hre).
          * apply (res_unique L e _ HrkL He (nth_error_In _ _ Hj') Hre Logic.I). rewrite Hke. reflexivity.
      - intros j y t' h' op' r' Hj Hy. destruct (nth_app_cases _ _ _ _ Hj) as [(Hlt & HjQ) | (Hge & HjS)].
        + destruct (Hqr j y t' h' op' r' HjQ Hy) as [(i & x & Hij & Hi & Hx) | Hinu]; [left | right; exact Hinu].
          exists i, x. split; [exact Hij |]. split; [rewrite nth_error_app1 by lia; exact Hi | exact Hx].
        + unfold schedule_trace_tagged in HjS. rewrite nth_error_map in HjS.
          destruct (nth_error tr (j - length Q)) as [m |] eqn:Hm; [| discriminate HjS].
          cbn in HjS. apply some_inj in HjS. subst y. cbn in Hy.
          assert (HmL : nth_error L (j - length Q) = Some (untag m)) by (unfold L; rewrite nth_error_map, Hm; reflexivity).
          pose proof (HtidL _ (nth_error_In _ _ HmL)) as Ht'. rewrite Hy in Ht'. cbn in Ht'. subst t'.
          rewrite Hy in HmL.
          destruct (produced_res_invoked t _ _ _ _ h' op' r' Hprod HmL) as (i & Hi & HiL).
          unfold L in HiL. rewrite nth_error_map in HiL.
          destruct (nth_error tr i) as [mi |] eqn:Hmi; [| discriminate HiL]. cbn in HiL. apply some_inj in HiL.
          left. exists (length Q + i), (Build_TaggedScheduledEvent (t, h) mi). split; [lia |]. split; [| exact HiL].
          rewrite nth_error_app2 by lia. replace (length Q + i - length Q) with i by lia.
          unfold schedule_trace_tagged. rewrite nth_error_map, Hmi. reflexivity.
      - exact Hur.
    Qed.

    (** An underlay step moves one queued event to the emitted trace. *)
    Lemma uinv_underlay u cand q q' pool Q Q' used :
      select_frontier_tagged cand Q Q' ->
      UInv u (Build_TaggedModuleConfig q pool Q used) ->
      UInv (u ++ [untag (ts_event cand)]) (Build_TaggedModuleConfig q' pool Q' used).
    Proof.
      intros Hsel Hu.
      destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & -> & -> & Hcr).
      set (ec := untag (ts_event cand)).
      assert (Hperm : Permutation (u ++ qevs (pre ++ cand :: post)) ((u ++ [ec]) ++ qevs (pre ++ post))).
      { rewrite !qevs_app. cbn [qevs map]. rewrite <- app_assoc. cbn [app].
        apply Permutation_app_head. apply Permutation_sym. apply Permutation_middle. }
      assert (Hin : forall e, In e ((u ++ [ec]) ++ qevs (pre ++ post)) <-> In e (u ++ qevs (pre ++ cand :: post))).
      { intros e. split; apply Permutation_in; [apply Permutation_sym |]; exact Hperm. }
      assert (Hcand : nth_error (pre ++ cand :: post) (length pre) = Some cand)
        by (rewrite nth_error_app2, Nat.sub_diag by lia; reflexivity).
      destruct Hu as [Hik Hus Hrk Hri Hcm Hqr Hur]. cbn [tm_queue tm_used_underlay] in *.
      constructor; cbn [tm_queue tm_used_underlay].
      - exact (Permutation_NoDup (perm_ikeys _ _ Hperm) Hik).
      - intros k Hk. apply Hus. exact (Permutation_in _ (Permutation_sym (perm_ikeys _ _ Hperm)) Hk).
      - exact (Permutation_NoDup (perm_rkeys _ _ Hperm) Hrk).
      - intros k Hk. apply (Permutation_in _ (perm_ikeys _ _ Hperm)). apply Hri.
        exact (Permutation_in _ (Permutation_sym (perm_rkeys _ _ Hperm)) Hk).
      - intros t h op Hi. destruct (Hcm t h op (proj1 (Hin _) Hi)) as (r & Hr).
        exists r. intros e He. apply Hr. exact (proj1 (Hin e) He).
      - intros j y t h op r Hj Hy.
        destruct (nth_error_remove_middle pre post cand j y Hj) as [(Hlt & Hj0) | (Hge & Hj0)].
        + destruct (Hqr j y t h op r Hj0 Hy) as [(i & x & Hij & Hi & Hx) | Hinu].
          * left. exists i, x. split; [exact Hij |]. split; [| exact Hx].
            rewrite nth_error_app1 in Hi |- * by lia. exact Hi.
          * right. apply in_or_app. left. exact Hinu.
        + destruct (Hqr (S j) y t h op r Hj0 Hy) as [(i & x & Hij & Hi & Hx) | Hinu].
          * destruct (nth_error_middle_cases pre post cand i x Hi) as [(Hlt & Hi') | [(Heq & ->) | (Hgt & Hi')]].
            -- left. exists i, x. split; [lia | auto].
            -- right. apply in_or_app. right. left. unfold ec. exact Hx.
            -- left. exists (i - 1), x. split; [lia | auto].
          * right. apply in_or_app. left. exact Hinu.
      - intros j t h op r Hj. destruct (nth_app_cases _ _ _ _ Hj) as [(Hlt & Hju) | (Hge & Hjn)].
        + destruct (Hur j t h op r Hju) as (i & Hi & Hiu). exists i. split; [exact Hi |].
          rewrite nth_error_app1 by (apply nth_error_Some; congruence). exact Hiu.
        + assert (Hj' : j - length u = 0) by (destruct (j - length u) as [| n] eqn:?; [reflexivity | destruct n; discriminate Hjn]).
          rewrite Hj' in Hjn. cbn in Hjn. apply some_inj in Hjn. unfold ec in Hjn.
          destruct (Hqr (length pre) cand t h op r Hcand Hjn) as [(i & x & Hi & Hix & Hx) | Hinu].
          * exfalso. rewrite nth_error_app1 in Hix by exact Hi.
            rewrite Forall_forall in Hcr. specialize (Hcr x (nth_error_In _ _ Hix)).
            unfold tagged_can_cross, must_precede in Hcr. rewrite Hx, Hjn in Hcr. cbn in Hcr.
            destruct Hcr as [Hne | (_ & Hno)]; [exact (Hne eq_refl) | exact (Hno eq_refl)].
          * apply In_nth_error in Hinu as (i & Hiu). exists i.
            assert (Hi : i < length u) by (apply nth_error_Some; congruence).
            split; [lia |]. rewrite nth_error_app1 by exact Hi. exact Hiu.
    Qed.

    Lemma uinv_step u ev c c' :
      module_step_tagged VE M ev c c' -> UInv u c -> UInv (u ++ ViewLHL.underlay_events [ev]) c'.
    Proof.
      intros Hst Hu. destruct Hst as [t h op q pool Q used tr ret Hcf Hprod Hft
                                     | cand q q' pool Q Q' used Hsel Hlts
                                     | t h op ret q pool pool' Q used Hfin Hdone].
      - rewrite app_nil_r. exact (uinv_invoke u t h op q pool Q used tr ret Hprod Hft Hu).
      - exact (uinv_underlay u cand q q' pool Q Q' used Hsel Hu).
      - rewrite app_nil_r. destruct Hu as [Hik Hus Hrk Hri Hcm Hqr Hur]. constructor; assumption.
    Qed.

    Lemma uinv_exec c evs c' :
      module_execution_tagged VE M c evs c' -> forall u, UInv u c -> UInv (u ++ ViewLHL.underlay_events evs) c'.
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros u Hu.
      - rewrite app_nil_r. exact Hu.
      - specialize (IH _ (uinv_step u ev c1 c2 Hst Hu)).
        replace (u ++ ViewLHL.underlay_events (ev :: evs))
          with ((u ++ ViewLHL.underlay_events [ev]) ++ ViewLHL.underlay_events evs); [exact IH |].
        rewrite <- app_assoc. f_equal. destruct ev; reflexivity.
    Qed.

    (** The underlay trace of every execution from the initial
        configuration is well formed for the copy-cat. *)
    Theorem underlay_ccwf (σ0 : State VE) evs c :
      module_execution_tagged VE M (initial_tagged_module VE σ0) evs c -> CCWF (ViewLHL.underlay_events evs).
    Proof.
      intros Hex. pose proof (uinv_exec _ _ _ Hex [] (uinv_init σ0)) as Hu. cbn [app] in Hu.
      set (u := ViewLHL.underlay_events evs) in *.
      destruct Hu as [Hik Hus Hrk Hri Hcm Hqr Hur].
      constructor.
      - rewrite RelaxedHoareCompLinSpec.invocation_keys_app in Hik. exact (NoDup_app_remove_r _ _ Hik).
      - rewrite response_keys_app in Hrk. exact (NoDup_app_remove_r _ _ Hrk).
      - exact Hur.
      - intros t h op Hi. destruct (Hcm t h op (in_or_app _ _ _ (or_introl Hi))) as (r & Hr).
        exists r. intros e He. apply Hr. apply in_or_app. left. exact He.
    Qed.
  End UnderlayWF.

  (** The underlay trace of every execution of every module over [VE]
      is a copy-cat trace over [VE]. *)
  Corollary underlay_rtraces {E F : RelaxedSig.t} (VE : LTS E) (M : RelaxedModuleImpl E F) (σ0 : State VE) evs c :
    module_execution_tagged VE M (initial_tagged_module VE σ0) evs c ->
    RTraces VE σ0 (ViewLHL.underlay_events evs).
  Proof.
    intros Hex. apply (rtraces_of_ccwf VE σ0 _ (underlay_ccwf VE M σ0 evs c Hex)).
    exists (tm_lts_state c). exact (ViewLHL.exec_underlay_path M VE _ _ _ Hex).
  Qed.

  (** ** [unabsorb]: ⟦M⟧ over [VF] ⊆ ⟦M⟧ over cc_F;VF

      Every overlay trace of [M] over [VF] is an overlay trace of [M]
      over the composite [ModLTS VF idF] (the copy-cat run over [VF]),
      for every [VF].  Proof: the underlay trace [u] of the execution is
      a copy-cat trace over [VF] ([underlay_rtraces]), hence a path of
      the composite ([modlts_paths]), and the execution moves to the
      composite along it ([ViewLHL.exec_transport]).  Each inner
      invocation of the copy-cat is the first underlay step of the
      composite step after it; a trailing one is dropped.  No hypothesis
      on [VF], no inhabited-arity hypothesis: the copy-cat's committed
      result of a pending call is read off [M]'s own method trace. *)
  Theorem unabsorb {F G : RelaxedSig.t} (VF : LTS F) (v0 : State VF) (M : RelaxedModuleImpl F G) s :
    MTraces VF M v0 s -> MTraces (ModLTS VF idF) M (initial_tagged_module VF v0) s.
  Proof.
    intros (evs & c & Hex & Hov).
    pose proof (underlay_rtraces VF M v0 evs c Hex) as Hrt.
    destruct (proj2 (modlts_paths VF idF v0 _) Hrt) as (q' & Hp).
    destruct (ViewLHL.exec_transport M VF (ModLTS VF idF) _ _ _ Hex _ _ Hp) as (d & Hd & _).
    exists evs, d. split; [exact Hd | exact Hov].
  Qed.

  (** The copy-cat instance: cc ⊆ cc;cc. *)
  Corollary rtraces_unabsorb {F : RelaxedSig.t} (VF : LTS F) (v0 : State VF) s :
    RTraces VF v0 s -> RTraces (ModLTS VF idF) (initial_tagged_module VF v0) s.
  Proof. exact (unabsorb VF v0 idF s). Qed.

  (** Copy-cat inclusion over the composite implies it over the plain
      underlay. *)
  Corollary complin_unabsorb {E F : RelaxedSig.t} (M : RelaxedModuleImpl E F) (VE : LTS E) (σ0 : State VE)
      (VF : LTS F) (v0 : State VF) :
    RCompLin M (ModLTS VE idF) (initial_tagged_module VE σ0) VF v0 -> RCompLin M VE σ0 VF v0.
  Proof. intros HC s Hs. apply HC. exact (unabsorb VE σ0 M s Hs). Qed.

  (** ** Closure of an underlay under copy-cat images (RLHL-3c.4)

      Absorption ([MTraces (ModLTS VF idF) M ⊆ MTraces VF M], pending)
      cannot hold for every [VF] ([absorb_needs_closure] below): the
      inner copy-cat picks its own underlay handles and commits results
      that a response of [VF] may later contradict.  The hypothesis the
      plan proposes for it is [CCClosed VF v0]: the paths of [VF] from
      [v0] are closed under [ccimg Rk], which renames the handle of every
      event along a key relation [Rk] (functional, and injective within
      a thread) and may delete responses.  [ei_ccclosed] and
      [eihl_ccclosed]: the sequential-specification LTSs [EI δ] and
      [EIhl δ] from an empty pending list are [CCClosed]. *)

  Definition rehandle {F : RelaxedSig.t} (h : RelaxedSig.handle F) (e : ThreadEvent F) : ThreadEvent F :=
    Build_ThreadEvent (te_tid F e)
      (match te_ev F e with InvEv _ o => InvEv h o | ResEv _ o r => ResEv h o r end).

  Inductive ccimg {F : RelaxedSig.t} (Rk : CallKey F -> RelaxedSig.handle F -> Prop) :
      list (ThreadEvent F) -> list (ThreadEvent F) -> Prop :=
  | ccimg_nil : ccimg Rk [] []
  | ccimg_keep e h u u' : Rk (te_key e) h -> ccimg Rk u u' -> ccimg Rk (e :: u) (rehandle h e :: u')
  | ccimg_drop e u u' : is_res e -> ccimg Rk u u' -> ccimg Rk (e :: u) u'.

  Definition CCClosed {F : RelaxedSig.t} (V : LTS F) (v0 : State V) : Prop :=
    forall Rk u u', (forall k h1 h2, Rk k h1 -> Rk k h2 -> h1 = h2) ->
      (forall k1 k2 h, Rk k1 h -> Rk k2 h -> fst k1 = fst k2 -> k1 = k2) ->
      LPaths V v0 u -> ccimg Rk u u' -> LPaths V v0 u'.

  Section CCImg.
    Context {F : RelaxedSig.t} (Rk : CallKey F -> RelaxedSig.handle F -> Prop).

    Lemma ccimg_app u1 u1' u2 u2' : ccimg Rk u1 u1' -> ccimg Rk u2 u2' -> ccimg Rk (u1 ++ u2) (u1' ++ u2').
    Proof.
      induction 1 as [| e h u u' Hk Hc IH | e u u' Hr Hc IH]; intros H2; cbn.
      - exact H2.
      - apply ccimg_keep; [exact Hk | exact (IH H2)].
      - apply ccimg_drop; [exact Hr | exact (IH H2)].
    Qed.

    (** Paths are built by [snoc] in the absorption proof; [ccimg] is
        built by [cons]. *)
    Lemma ccimg_snoc_keep u u' e h :
      ccimg Rk u u' -> Rk (te_key e) h -> ccimg Rk (u ++ [e]) (u' ++ [rehandle h e]).
    Proof. intros Hc Hk. apply ccimg_app; [exact Hc | apply ccimg_keep; [exact Hk | constructor]]. Qed.

    Lemma ccimg_snoc_drop u u' e : ccimg Rk u u' -> is_res e -> ccimg Rk (u ++ [e]) u'.
    Proof.
      intros Hc Hr. rewrite <- (app_nil_r u'). apply ccimg_app; [exact Hc | apply ccimg_drop; [exact Hr | constructor]].
    Qed.

    Lemma ccimg_app_inv u1 u2 u' :
      ccimg Rk (u1 ++ u2) u' -> exists u1' u2', u' = u1' ++ u2' /\ ccimg Rk u1 u1' /\ ccimg Rk u2 u2'.
    Proof.
      revert u'. induction u1 as [| e u1 IH]; intros u' Hc.
      - exists [], u'. split; [reflexivity |]. split; [constructor | exact Hc].
      - cbn in Hc. inversion Hc as [| e0 h u0 u0' Hk Hc' | e0 u0 u0' Hr Hc']; subst.
        + destruct (IH _ Hc') as (u1' & u2' & -> & H1 & H2).
          exists (rehandle h e :: u1'), u2'. split; [reflexivity |]. split; [apply ccimg_keep; assumption | exact H2].
        + destruct (IH _ Hc') as (u1' & u2' & -> & H1 & H2).
          exists u1', u2'. split; [reflexivity |]. split; [apply ccimg_drop; assumption | exact H2].
    Qed.
  End CCImg.

  (** *** [EI δ] and [EIhl δ] from an empty pending list are [CCClosed]

      The image state of [(s, P)] is [(s, P')] where [P'] is a
      permutation of the renamed records of [P] followed by the records
      of dropped responses (which stay pending forever).  Invocations
      take the same [δ] step; a kept response finds its renamed record
      because [Rk] is functional.  [EIhl] adds the used-key list, which
      is renamed key by key; its freshness check survives renaming
      because [Rk] is injective within a thread. *)

  Section EIClosed.
    Context {F : RelaxedSig.t} {St : Type}.
    Context (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop).
    Context (Rk : CallKey F -> RelaxedSig.handle F -> Prop).
    Context (Hfun : forall k h1 h2, Rk k h1 -> Rk k h2 -> h1 = h2).

    Import RelaxedTraceLin.

    Definition RR (x x' : Op F) : Prop :=
      exists h', Rk (op_key x) h' /\ x' = RelaxedHoareCompLinSpec.rekey (fst (op_key x), h') x.

    Definition SR (σ σ' : St * list (Op F)) : Prop :=
      fst σ' = fst σ /\ exists Pa ex, Forall2 RR (snd σ) Pa /\ Permutation (snd σ') (Pa ++ ex).

    Lemma forall2_split {A B : Type} (R : A -> B -> Prop) l1 x l2 l' :
      Forall2 R (l1 ++ x :: l2) l' -> exists l1' x' l2', l' = l1' ++ x' :: l2' /\ Forall2 R l1 l1' /\ R x x' /\ Forall2 R l2 l2'.
    Proof.
      intros H. apply Forall2_app_inv_l in H as (l1' & l2'' & H1 & H2 & ->).
      inversion H2 as [| ? x' ? l2' Hx H2']; subst. exists l1', x', l2'. auto.
    Qed.

    Lemma ei_keep_step e h σ σ1 σ' :
      Step (RelaxedHoareSpec.EI δ) e σ σ1 -> Rk (te_key e) h -> SR σ σ' ->
      exists σ1', Step (RelaxedHoareSpec.EI δ) (rehandle h e) σ' σ1' /\ SR σ1 σ1'.
    Proof.
      destruct σ as [s P], σ' as [s' P']. intros Hs Hk (Hfst & Pa & ex & HF & Hperm). cbn in Hfst, HF, Hperm. subst s'.
      destruct e as [t [h0 o | h0 o r]]; cbn in Hs, Hk |- *.
      - destruct Hs as (r & st' & Hd & ->).
        exists (st', Build_Op (t, h) o r :: P'). split.
        + exists r, st'. split; [exact Hd | reflexivity].
        + split; [reflexivity |]. exists (Build_Op (t, h) o r :: Pa), ex. split.
          * constructor; [| exact HF]. exists h. split; [exact Hk | reflexivity].
          * cbn. apply perm_skip. exact Hperm.
      - destruct Hs as (P1 & P2 & HP & ->). cbn in HP. subst P.
        destruct (forall2_split _ _ _ _ _ HF) as (Pa1 & x' & Pa2 & -> & H1 & (h' & Hk' & ->) & H2).
        cbn in Hk'. pose proof (Hfun _ _ _ Hk' Hk) as ->. cbn in Hperm.
        assert (Hin : In (Build_Op (t, h) o r) P').
        { apply (Permutation_in _ (Permutation_sym Hperm)). apply in_or_app. left. apply in_elt. }
        apply in_split in Hin as (Q1 & Q2 & ->).
        exists (s, Q1 ++ Q2). split.
        + exists Q1, Q2. split; reflexivity.
        + split; [reflexivity |]. exists (Pa1 ++ Pa2), ex. split; [apply Forall2_app; assumption |].
          cbn. rewrite <- app_assoc in Hperm |- *. cbn in Hperm. exact (Permutation_app_inv _ _ _ _ _ Hperm).
    Qed.

    Lemma ei_drop_step e σ σ1 σ' :
      is_res e -> Step (RelaxedHoareSpec.EI δ) e σ σ1 -> SR σ σ' -> SR σ1 σ'.
    Proof.
      destruct σ as [s P], σ' as [s' P']. intros Hr Hs (Hfst & Pa & ex & HF & Hperm). cbn in Hfst, HF, Hperm.
      destruct e as [t [h0 o | h0 o r]]; [destruct Hr |]. cbn in Hs.
      destruct Hs as (P1 & P2 & HP & ->). cbn in HP. subst P.
      destruct (forall2_split _ _ _ _ _ HF) as (Pa1 & x' & Pa2 & -> & H1 & Hx & H2).
      split; [exact Hfst |]. exists (Pa1 ++ Pa2), (x' :: ex). split; [apply Forall2_app; assumption |].
      cbn. eapply Permutation_trans; [exact Hperm |]. rewrite <- !app_assoc. apply Permutation_app_head.
      cbn. apply Permutation_middle.
    Qed.

    Lemma ei_cc_path u u' : ccimg Rk u u' ->
      forall σ σend σ', vf_path (RelaxedHoareSpec.EI δ) σ u σend -> SR σ σ' -> LPaths (RelaxedHoareSpec.EI δ) σ' u'.
    Proof.
      induction 1 as [| e h u u' Hk Hc IH | e u u' Hr Hc IH]; intros σ σend σ' Hp Hsr.
      - exists σ'. constructor.
      - destruct (ViewLHL.vf_path_cons_inv _ _ _ _ _ Hp) as (σ1 & Hs & Hp').
        destruct (ei_keep_step _ _ _ _ _ Hs Hk Hsr) as (σ1' & Hs' & Hsr1).
        destruct (IH _ _ _ Hp' Hsr1) as (σe & Hpe). exists σe. econstructor; [exact Hs' | exact Hpe].
      - destruct (ViewLHL.vf_path_cons_inv _ _ _ _ _ Hp) as (σ1 & Hs & Hp').
        exact (IH _ _ _ Hp' (ei_drop_step _ _ _ _ Hr Hs Hsr)).
    Qed.

    Lemma sr_init (s0 : St) : SR (s0, []) (s0, []).
    Proof. split; [reflexivity |]. exists [], []. split; constructor. Qed.

    (** [EIhl]: the used-key lists are related key by key. *)
    Definition KR (k k' : CallKey F) : Prop := fst k' = fst k /\ Rk k (snd k').

    Lemma forall2_in_r {A B : Type} (R : A -> B -> Prop) l l' y :
      Forall2 R l l' -> In y l' -> exists x, In x l /\ R x y.
    Proof.
      induction 1 as [| x y' l l' Hxy Hl IH]; intros Hy; [destruct Hy |].
      destruct Hy as [<- | Hy]; [exists x; split; [left; reflexivity | exact Hxy] |].
      destruct (IH Hy) as (x' & Hx' & Hr). exists x'. split; [right; exact Hx' | exact Hr].
    Qed.

    Lemma eihl_cc_path (Hinj : forall k1 k2 h, Rk k1 h -> Rk k2 h -> fst k1 = fst k2 -> k1 = k2) u u' :
      ccimg Rk u u' ->
      forall σ σend σ', vf_path (RelaxedHoareCompLinSpec.EIhl δ) σ u σend -> SR (fst σ) (fst σ') ->
        Forall2 KR (snd σ) (snd σ') -> LPaths (RelaxedHoareCompLinSpec.EIhl δ) σ' u'.
    Proof.
      induction 1 as [| e h u u' Hk Hc IH | e u u' Hr Hc IH]; intros σ σend σ' Hp Hsr Hkr.
      - exists σ'. constructor.
      - destruct (ViewLHL.vf_path_cons_inv _ _ _ _ _ Hp) as (σ1 & Hs & Hp').
        pose proof (RelaxedHoareCompLinSpec.hl_step_base _ _ _ _ Hs) as Hsb.
        destruct (ei_keep_step _ _ _ _ _ Hsb Hk Hsr) as (σ1' & Hs' & Hsr1).
        destruct σ as [σa us], σ1 as [σ1a us1], σ' as [σa' us']. cbn in Hsb, Hs', Hsr, Hsr1, Hkr.
        destruct e as [t [h0 o | h0 o r]]; cbn in Hs, Hk, Hs'.
        + destruct Hs as (Hnu & _ & Hus1). cbn in Hus1. subst us1.
          assert (Hnu' : ~ In (t, h) us').
          { intros Hin. destruct (forall2_in_r _ _ _ _ Hkr Hin) as (k & Hk0 & (Hfk & Hrk)). cbn in Hfk, Hrk.
            pose proof (Hinj _ _ _ Hrk Hk ltac:(cbn; symmetry; exact Hfk)) as ->. exact (Hnu Hk0). }
          destruct (IH (σ1a, (t, h0) :: us) σend (σ1', (t, h) :: us') Hp' Hsr1) as (σe & Hpe).
          { constructor; [split; [reflexivity | exact Hk] | exact Hkr]. }
          exists σe. econstructor; [| exact Hpe]. cbn. split; [exact Hnu' |]. split; [exact Hs' | reflexivity].
        + destruct Hs as (_ & Hus1). cbn in Hus1. subst us1.
          destruct (IH (σ1a, us) σend (σ1', us') Hp' Hsr1 Hkr) as (σe & Hpe).
          exists σe. econstructor; [| exact Hpe]. cbn. split; [exact Hs' | reflexivity].
      - destruct (ViewLHL.vf_path_cons_inv _ _ _ _ _ Hp) as (σ1 & Hs & Hp').
        pose proof (RelaxedHoareCompLinSpec.hl_step_base _ _ _ _ Hs) as Hsb.
        pose proof (ei_drop_step _ _ _ _ Hr Hsb Hsr) as Hsr1.
        destruct e as [t [h0 o | h0 o r]]; [destruct Hr |]. cbn in Hs.
        destruct Hs as (_ & Hus1).
        apply (IH σ1 σend σ' Hp' Hsr1). exact (eq_ind_r (fun l => Forall2 KR l (snd σ')) Hkr Hus1).
    Qed.
  End EIClosed.

  Theorem ei_ccclosed {F : RelaxedSig.t} {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) (s0 : St) :
    CCClosed (RelaxedHoareSpec.EI δ) (s0, []).
  Proof.
    intros Rk u u' Hfun _ (σend & Hp) Hc. exact (ei_cc_path δ Rk Hfun u u' Hc _ _ _ Hp (sr_init Rk s0)).
  Qed.

  Theorem eihl_ccclosed {F : RelaxedSig.t} {St : Type}
      (δ : St -> forall o : Sig.op (RelaxedSig.effect F), Sig.ar o -> St -> Prop) (s0 : St) :
    CCClosed (RelaxedHoareCompLinSpec.EIhl δ) ((s0, []), []).
  Proof.
    intros Rk u u' Hfun Hinj (σend & Hp) Hc.
    exact (eihl_cc_path δ Rk Hfun Hinj u u' Hc _ _ ((s0, []), []) Hp (sr_init Rk s0) (Forall2_nil _)).
  Qed.

  (** ** Absorption needs a closure hypothesis (the plan's counterexample (R))

      [VF0] accepts invocations on handle [0] only.  [M0]'s single
      method issues one future and returns its raw handle (programs may
      read raw handles: [RelaxedLang.future_handle]).  Over the
      composite [ModLTS VF0 idF], [M0] may choose handle [5] for its
      call to the copy-cat, which forwards it to [VF0] on handle [0], so
      the composite returns [5].  Directly over [VF0], [M0]'s invocation
      must use handle [0] before the call can return, so it returns [0].
      Hence the overlay trace [inv; res 5] separates the two, and
      absorption fails without a hypothesis on [VF].  [vf0_not_ccclosed]:
      [VF0] is indeed not [CCClosed] (renaming handle [0] to [5] leaves
      its path language). *)

  Module NeedsClosure.
    Definition FE : Sig.t := {| Sig.op := unit; Sig.ar := fun _ => unit |}.
    Definition GE : Sig.t := {| Sig.op := unit; Sig.ar := fun _ => nat |}.
    Definition F0 : RelaxedSig.t := RelaxedSig.sc FE nat.
    Definition G0 : RelaxedSig.t := RelaxedSig.sc GE nat.

    Definition vf0_step (e : ThreadEvent F0) (_ _ : unit) : Prop :=
      match te_ev F0 e with InvEv h _ => h = 0 | ResEv _ _ _ => True end.

    Definition VF0 : LTS F0 := {| State := unit; Step := vf0_step; Error := fun _ _ => False |}.

    Definition body : Prog F0 nat :=
      Future (tt : Sig.op (RelaxedSig.effect F0)) (fun f => Wait f (fun _ => Ret (future_handle f))).

    Definition M0 : RelaxedModuleImpl F0 G0 := fun _ _ => body.

    Abbreviation t1 := 1%positive.

    Definition s0 : list (ThreadEvent G0) :=
      [Build_ThreadEvent t1 (@InvEv G0 0 tt); Build_ThreadEvent t1 (@ResEv G0 0 tt 5)].

    (** *** The composite returns [5] *)

    Definition trM : list (TaggedEvent F0) :=
      [Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv F0 5 tt)) (resolved_in (@empty_store F0));
       Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv F0 5 tt tt)) no_deps].

    Lemma body_produces5 : program_produces_tagged t1 (M0 tt t1) trM 5.
    Proof.
      exists (@Build_ProgramConfig F0 nat (Ret 5) [@Build_FutureEntry F0 5 (@Resolved F0 tt tt)]). split.
      - eapply tagged_execution_emit.
        { apply (@tagged_future F0 nat t1 tt (fun f => Wait f (fun _ => Ret (future_handle f))) 5 (@empty_store F0)).
          intros []. }
        eapply tagged_execution_emit.
        { apply (@tagged_wait_pending F0 nat t1 tt 5 tt (fun _ => Ret 5)). apply resolve_here. }
        apply tagged_execution_refl.
      - constructor. constructor; [exact Logic.I | constructor].
    Qed.

    Abbreviation CI := (@TaggedModuleConfig F0 F0 VF0).

    Definition ci0 : CI := initial_tagged_module VF0 tt.
    Definition ci1 : CI :=
      @Build_TaggedModuleConfig F0 F0 VF0 tt [@Build_CallEntry F0 t1 5 (@ActiveCall F0 tt tt)]
        [@Build_TaggedScheduledEvent F0 F0 (t1, 5) (@cc_inv_ev F0 t1 0 tt); @Build_TaggedScheduledEvent F0 F0 (t1, 5) (@cc_res_ev F0 t1 0 tt tt)]
        [(t1, 0)].
    Definition ci2 : CI :=
      @Build_TaggedModuleConfig F0 F0 VF0 tt [@Build_CallEntry F0 t1 5 (@DeadCall F0)] [] [(t1, 0)].

    Lemma mod_inv5 : mod_step VF0 idF (Build_ThreadEvent t1 (@InvEv F0 5 tt)) ci0 ci1.
    Proof.
      exists [], ci0. split; [constructor |].
      apply (tagged_invoke VF0 idF t1 5 tt tt [] [] [] [@cc_inv_ev F0 t1 0 tt; @cc_res_ev F0 t1 0 tt tt] tt).
      - intros [].
      - exact (@idF_produces F0 t1 0 tt tt).
      - split; cbn; [constructor; [intros [] | constructor] | intros k _ []].
    Qed.

    Lemma mod_res5 : mod_step VF0 idF (Build_ThreadEvent t1 (@ResEv F0 5 tt tt)) ci1 ci2.
    Proof.
      exists [Build_ThreadEvent t1 (@InvEv F0 0 tt); Build_ThreadEvent t1 (@ResEv F0 0 tt tt)],
             (@Build_TaggedModuleConfig F0 F0 VF0 tt [@Build_CallEntry F0 t1 5 (@ActiveCall F0 tt tt)] [] [(t1, 0)]).
      split.
      - eapply tagged_module_execution_cons.
        { apply (tagged_underlay VF0 idF (@Build_TaggedScheduledEvent F0 F0 (t1, 5) (@cc_inv_ev F0 t1 0 tt)) tt tt).
          - apply tagged_select_here.
          - reflexivity. }
        eapply tagged_module_execution_cons.
        { apply (tagged_underlay VF0 idF (@Build_TaggedScheduledEvent F0 F0 (t1, 5) (@cc_res_ev F0 t1 0 tt tt)) tt tt).
          - apply tagged_select_here.
          - exact Logic.I. }
        apply tagged_module_execution_refl.
      - apply (tagged_return VF0 idF t1 5 tt tt tt). { apply finish_here. } intros [].
    Qed.

    Lemma composite_s0 : MTraces (ModLTS VF0 idF) M0 (initial_tagged_module VF0 tt) s0.
    Proof.
      set (q0 := initial_tagged_module VF0 tt).
      exists [OverlayEvent (Build_ThreadEvent t1 (@InvEv G0 0 tt));
              UnderlayEvent (Build_ThreadEvent t1 (@InvEv F0 5 tt));
              UnderlayEvent (Build_ThreadEvent t1 (@ResEv F0 5 tt tt));
              OverlayEvent (Build_ThreadEvent t1 (@ResEv G0 0 tt 5))].
      eexists. split; [| reflexivity].
      eapply tagged_module_execution_cons.
      { apply (tagged_invoke (ModLTS VF0 idF) M0 t1 0 tt q0 [] [] [] trM 5).
        - intros [].
        - exact body_produces5.
        - split; cbn; [constructor; [intros [] | constructor] | intros k _ []]. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (ModLTS VF0 idF) M0
                 (@Build_TaggedScheduledEvent F0 G0 (t1, 0)
                    (Build_TaggedEvent (Build_ThreadEvent t1 (@InvEv F0 5 tt)) (resolved_in (@empty_store F0))))
                 q0 ci1).
        - apply tagged_select_here.
        - exact mod_inv5. }
      eapply tagged_module_execution_cons.
      { apply (tagged_underlay (ModLTS VF0 idF) M0
                 (@Build_TaggedScheduledEvent F0 G0 (t1, 0) (Build_TaggedEvent (Build_ThreadEvent t1 (@ResEv F0 5 tt tt)) no_deps))
                 ci1 ci2).
        - apply tagged_select_here.
        - exact mod_res5. }
      eapply tagged_module_execution_cons.
      { apply (tagged_return (ModLTS VF0 idF) M0 t1 0 tt 5 ci2). { apply finish_here. } intros []. }
      apply tagged_module_execution_refl.
    Qed.

    (** *** Directly over [VF0], every return of [M0] is [0] *)

    (** The body returns the handle of one of its invocations.  Read
        through views computed by [match], as in
        [RelaxedHoareCompLin.cc_trace]; no dependent inversion. *)
    Definition rview (h : nat) (p : Prog F0 nat) : Prop :=
      match p with Wait _ k => forall x, k x = Ret h | Ret y => y = h | _ => False end.

    Definition fview (p : Prog F0 nat) : Prop :=
      match p with Future o k => forall h, rview h (k (MkFutureRef o h)) | _ => False end.

    Definition PInv (t : tid) (c : ProgramConfig F0 nat) (done : list (ThreadEvent F0)) : Prop :=
      (fview (pc_prog c) /\ pc_futures c = []) \/
      (exists h, In (Build_ThreadEvent t (@InvEv F0 h tt)) done /\ rview h (pc_prog c)).

    Definition act_events (a : TAction F0) : list (ThreadEvent F0) :=
      match a with TSilent => [] | TEmit m => [untag m] end.

    Lemma pinv_step t a c1 c2 done :
      program_step_tagged t a c1 c2 -> PInv t c1 done -> PInv t c2 (done ++ act_events a).
    Proof.
      intros Hst Hi. destruct Hst as [o k h H Hf | o d k h H Hf | o h ret k H Hr | o h ret k H H' Hr | o h ret p H H' Hr | p H];
        destruct Hi as [(Hfv & Hst) | (h0 & Hin & Hrv)]; cbn in *; try contradiction.
      - right. exists h. destruct o. split; [apply in_or_app; right; left; reflexivity | exact (Hfv h)].
      - right. exists h0. rewrite app_nil_r. split; [exact Hin |]. rewrite (Hrv ret). reflexivity.
      - right. exists h0. split; [apply in_or_app; left; exact Hin |]. rewrite (Hrv ret). reflexivity.
      - subst H. inversion Hr.
      - right. exists h0. split; [apply in_or_app; left; exact Hin | exact Hrv].
    Qed.

    Lemma pinv_exec t c tr c' done :
      program_execution_tagged t c tr c' -> PInv t c done -> PInv t c' (done ++ map untag tr).
    Proof.
      intros Hex. revert done. induction Hex as [c | c1 c2 c3 tr Hstep Hex IH | c1 c2 c3 m tr Hstep Hex IH]; intros done Hi.
      - rewrite app_nil_r. exact Hi.
      - pose proof (pinv_step _ _ _ _ done Hstep Hi) as H2. cbn in H2. rewrite app_nil_r in H2. exact (IH _ H2).
      - pose proof (pinv_step _ _ _ _ done Hstep Hi) as H2. cbn in H2.
        specialize (IH _ H2). rewrite <- app_assoc in IH. exact IH.
    Qed.

    Lemma body_returns_handle t o tr (r : nat) :
      program_produces_tagged t (M0 o t) tr r -> In (Build_ThreadEvent t (@InvEv F0 r tt)) (map untag tr).
    Proof.
      intros (c' & Hex & Hterm).
      assert (H0 : PInv t (initial_program (M0 o t)) []).
      { left. split; [| reflexivity]. cbn. intros h x. reflexivity. }
      pose proof (pinv_exec _ _ _ _ _ Hex H0) as Hi. cbn in Hi.
      destruct Hterm as [H r0 Hres]. destruct Hi as [(Hfv & _) | (h & Hin & Hrv)]; cbn in *; [destruct Hfv |].
      subst h. exact Hin.
    Qed.

    Definition cell_val (en : CallEntry G0) : nat :=
      match ce_cell G0 en with ActiveCall _ x => x | DeadCall => 0 end.

    Definition res_val (e : ThreadEvent G0) : nat :=
      match te_ev G0 e with ResEv _ _ x => x | InvEv _ _ => 0 end.

    (** An active call returns [0], or its invocation of the handle it
        will return is still queued. *)
    Definition J (c : @TaggedModuleConfig F0 G0 VF0) : Prop :=
      forall en, In en (tm_calls c) -> (exists o x, ce_cell G0 en = @ActiveCall G0 o x) ->
        cell_val en = 0 \/
        exists y, In y (tm_queue c) /\ ts_owner y = call_key en /\
                  untag (ts_event y) = Build_ThreadEvent (ce_tid G0 en) (@InvEv F0 (cell_val en) tt).

    Lemma j_step ev c c' :
      module_step_tagged VF0 M0 ev c c' -> J c -> J c' /\ forall e, overlay_events [ev] = [e] -> is_res e -> res_val e = 0.
    Proof.
      intros Hst Hj. destruct Hst as [t h op q pool Q used tr ret Hcf Hprod Hft
                                     | cand q q' pool Q Q' used Hsel Hlts
                                     | t h op ret q pool pool' Q used Hfin Hdone].
      - split; [| intros e He; cbn in He; injection He as <-; intros []].
        intros en [<- | Hen] Hact; cbn [tm_calls tm_queue] in *.
        + right. cbn [cell_val ce_cell ce_tid call_key ce_handle].
          pose proof (body_returns_handle _ _ _ _ Hprod) as Hin. apply in_map_iff in Hin as (m & Hm & Hmin).
          exists (Build_TaggedScheduledEvent (t, h) m). split; [| split; [reflexivity | exact Hm]].
          apply in_or_app. right. unfold schedule_trace_tagged. apply in_map. exact Hmin.
        + destruct (Hj en Hen Hact) as [H0 | (y & Hy & Hyo & Hye)]; [left; exact H0 | right].
          exists y. split; [apply in_or_app; left; exact Hy | split; assumption].
      - split; [| intros e He; discriminate He].
        destruct (select_frontier_tagged_split _ _ _ Hsel) as (pre & post & -> & -> & _).
        intros en Hen Hact. cbn [tm_calls tm_queue] in *.
        destruct (Hj en Hen Hact) as [H0 | (y & Hy & Hyo & Hye)]; [left; exact H0 |].
        apply in_app_or in Hy as [Hy | [<- | Hy]].
        + right. exists y. split; [apply in_or_app; left; exact Hy | split; assumption].
        + left. cbn in Hlts. unfold vf0_step in Hlts. rewrite Hye in Hlts. exact Hlts.
        + right. exists y. split; [apply in_or_app; right; exact Hy | split; assumption].
      - split.
        + intros en Hen Hact. cbn [tm_calls tm_queue] in *.
          destruct en as [t' h' [o' x' |]]; [| destruct Hact as (? & ? & Hc); discriminate Hc].
          exact (Hj _ (RelaxedModuleFacts.finish_call_active_preserved _ _ _ _ _ _ Hfin _ _ _ _ Hen) Hact).
        + intros e He _. cbn in He. injection He as <-. cbn.
          pose proof (RelaxedModuleFacts.finish_call_source _ _ _ _ _ _ Hfin) as Hen.
          destruct (Hj _ Hen ltac:(eexists; eexists; reflexivity)) as [H0 | (y & Hy & Hyo & _)]; [exact H0 |].
          exfalso. apply Hdone. exact (eq_ind _ (fun k => In k (map ts_owner Q)) (in_map ts_owner Q y Hy) _ Hyo).
    Qed.

    Lemma j_exec c evs c' :
      module_execution_tagged VF0 M0 c evs c' -> J c ->
      forall e, In e (overlay_events evs) -> is_res e -> res_val e = 0.
    Proof.
      induction 1 as [c | c1 c2 c3 ev evs Hst Hex IH]; intros Hj e He Hr; [destruct He |].
      destruct (j_step _ _ _ Hst Hj) as (Hj2 & Hev).
      rewrite overlay_events_cons in He. apply in_app_or in He as [He | He]; [| exact (IH Hj2 e He Hr)].
      destruct ev as [eu | eo]; cbn in He; [destruct He |].
      destruct He as [<- | []]. exact (Hev eo eq_refl Hr).
    Qed.

    Lemma direct_not_s0 : ~ MTraces VF0 M0 tt s0.
    Proof.
      intros (evs & c & Hex & Hov).
      assert (Hj0 : J (initial_tagged_module VF0 tt)) by (intros en []).
      pose proof (j_exec _ _ _ Hex Hj0 (Build_ThreadEvent t1 (@ResEv G0 0 tt 5))) as H.
      rewrite Hov in H. specialize (H ltac:(right; left; reflexivity) Logic.I). discriminate H.
    Qed.

    Lemma vf0_not_ccclosed : ~ CCClosed VF0 tt.
    Proof.
      intros Hcc.
      set (Rk := fun (k : CallKey F0) (h : nat) => k = (t1, 0) /\ h = 5).
      destruct (Hcc Rk [Build_ThreadEvent t1 (@InvEv F0 0 tt)] [Build_ThreadEvent t1 (@InvEv F0 5 tt)])
        as (v & Hp).
      - intros k h1 h2 [_ ->] [_ ->]. reflexivity.
      - intros k1 k2 h [-> _] [-> _] _. reflexivity.
      - exists tt. econstructor; [reflexivity | constructor].
      - change (Build_ThreadEvent t1 (@InvEv F0 5 tt)) with (@rehandle F0 5 (Build_ThreadEvent t1 (@InvEv F0 0 tt))).
        apply ccimg_keep; [split; reflexivity | constructor].
      - inversion Hp as [| ? ? ? ? ? Hs _]; subst. cbn in Hs. unfold vf0_step in Hs. cbn in Hs. discriminate Hs.
    Qed.
  End NeedsClosure.

  Theorem absorb_needs_closure :
    exists (F G : RelaxedSig.t) (VF : LTS F) (v0 : State VF) (M : RelaxedModuleImpl F G) s,
      MTraces (ModLTS VF idF) M (initial_tagged_module VF v0) s /\ ~ MTraces VF M v0 s.
  Proof.
    exists NeedsClosure.F0, NeedsClosure.G0, NeedsClosure.VF0, tt, NeedsClosure.M0, NeedsClosure.s0.
    split; [exact NeedsClosure.composite_s0 | exact NeedsClosure.direct_not_s0].
  Qed.

End RelaxedHoareAbsorb.
